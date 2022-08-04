---
layout: post
title: "An approach to discovering profitable arbitrage opportunities in subquartic time."
math: true
---
The task of discovering [arbitrage](https://en.wikipedia.org/wiki/Arbitrage) opportunities in trading various financial instruments in several markets appears to have entered into common folklore of not only arbitrageurs, but of the algorithmists also. Nowadays, whenever you search for a solution to it, you inevitably land either on blog posts discussing the quartic solutions based on the idea of a modified version of [Floyd-Warshall algorithm](https://en.wikipedia.org/wiki/Floyd%E2%80%93Warshall_algorithm) or on a solution of [Sedgewick and Wayne’s arbitrage detection problem](https://algs4.cs.princeton.edu/code/edu/princeton/cs/algs4/Arbitrage.java.html) finding any one profitable chain using the logarithmic transformation followed by negative cycle detection. And the worst is, the latter is way too often believed to find the most profitable opportunity. Ouch!

I lived all that through too, after I had come across [another reincarnation of the puzzle](https://web.archive.org/web/20210128142317/https://priceonomics.com/jobs/puzzle/), and tried to understand, whether there were any recent advances in the field. All I got was a dump of the same looking public repositories (with the majority mistakenly using the negative cycle detection trick to find the best solution) and the aforementioned blog posts. I nearly put in my twopence and presented the world yet another unwelcome implementation of a well-known all-pairs shortest path algorithm (though written in Scala), however, the ancient wisdom of using linear algebra to solve graph problems awoke in my subconsciousness and fruited several hours later.

To break new ground, let’s recall the max-plus tropical semiring over real numbers (you never changed your advanced algebra 101 for the turquoise waters of the Caribbean, did you?), which is the set of real numbers plus negative infinity $\Bbb R\cup\lbrace−\infty\rbrace$ with two operations: $a\oplus b=\max\lbrace a,b\rbrace$ called "plus" and $a\otimes b=a+b$ (called "times"). The identity element for $\oplus$ is $-\infty$ , and the identity element for $\otimes$ is 0. If you hunger for homework, check that such an algebraic structure is indeed a semiring.

The "additive" and "multiplicative" monoids can be expressed with `cats.Monoid[T]` and `scala.math.Ordering[T]` respectively. I'll use `java.math.BigDecimal` as the easiest and nearest alternative to exact real numbers. However, to allow for your custom implementation of real values which are at least closed under addition and taking the logarithm, and which guarantee correct results during computation of maxima, I'll represent the domain with the following parametric type:

```scala
sealed trait MaxPlusDomain[+T] extends Any with java.io.Serializable

case object NegativeInfinity extends MaxPlusDomain[Nothing]

case class FiniteValue[T](value: T) extends AnyVal with MaxPlusDomain[T]

object MaxPlusDomain {
  def argMax[T](values: IndexedSeq[MaxPlusDomain[T]])(implicit ord: Ordering[T]): (Option[Int], MaxPlusDomain[T]) =
    if (values.isEmpty) (None, NegativeInfinity)
    else {
      var m: Int = 1
      var maxIdx: Int = 0
      var max: MaxPlusDomain[T] = values(maxIdx)
      while (m < values.size) {
        (max, values(m)) match {
          case (FiniteValue(x), acc@FiniteValue(a)) =>
            if (ord.lt(x, a)) {
              maxIdx = m
              max = acc
            }
          case (NegativeInfinity, acc) =>
            maxIdx = m
            max = acc
          case (_, NegativeInfinity) => ()
        }
        m += 1
      }
      (Some(maxIdx), max)
    }
}
```

We can compose matrices from the elements of that semiring, try to multiply them and discover that the algorithm for their multiplication will resemble the classic textbook matrix multiplication one with a caveat that the regular addition is substituted with the operations of taking a maximum, and the regular multiplication is substituted with the regular addition, i.e., if $A$ and $B$ are matrices with $p$ columns and $p$ rows correspondingly, and $[M]\_{ij}$ is the $ij^{th}$ element of matrix $M$, then $[A\otimes B]\_{ij}=\max\([A]\_{i1}+[B]\_{1j},\dots,[A]\_{ip}+[B]\_{pj}\)$ .

If we now take the distance matrix $D$ of a graph and compute its $p^{th}$ max-plus tropical power, then $[D^p]_{ij}$ will equal the length of the longest walk from vertex $i$ to vertex $j$ using at most $p$ steps, i.e. the largest value on the diagonal of the power points to the largest closed walk with at most $p$ steps and forms a promising foundation for finding the most profitable arbitrage opportunity.

All that’s left is to

- find the way to reconstruct those walks, e.g., by keeping tabs on all the edges in the walks while computing the maxima:

```scala
class MaxPlusTropicalSquareMatrix[T](private val matrix: Array[Array[MaxPlusDomain[T]]],
                                     private val walks: Map[(Int, Int), IndexedSeq[Int]])
                                    (implicit additive: Monoid[T], ord: Ordering[T]) {
  val dimension: Int = matrix.length

  def apply(i: Int, j: Int): MaxPlusDomain[T] = matrix(i)(j)

  def walk(from: Int, to: Int): Option[IndexedSeq[Int]] = walks.get(from -> to)

  private def update(i: Int, j: Int, value: MaxPlusDomain[T]): Unit = {
    matrix(i)(j) = value
  }

  def *(multiplier: MaxPlusTropicalSquareMatrix[T]): MaxPlusTropicalSquareMatrix[T] = {
    require(multiplier.dimension == dimension)
    val product = Array.fill[MaxPlusDomain[T]](dimension, dimension)(NegativeInfinity)
    var walks = scala.collection.mutable.ListBuffer.empty[((Int, Int), IndexedSeq[Int])]
    if (dimension > 0) {
      val accumulator = Array.ofDim[MaxPlusDomain[T]](dimension)
      var i = 0
      while (i < dimension) {
        var j = 0
        while (j < dimension) {
          var k = 0
          while (k < dimension) {
            accumulator(k) = (this (i, k), multiplier(k, j)) match {
              case (NegativeInfinity, _) => NegativeInfinity
              case (_, NegativeInfinity) => NegativeInfinity
              case (FiniteValue(lv), FiniteValue(rv)) => FiniteValue(additive.combine(lv, rv))
            }
            k += 1
          }
          MaxPlusDomain.argMax(accumulator) match {
            case (_, NegativeInfinity) => ()
            case (Some(maxIndex), max: FiniteValue[T]) =>
              product(i)(j) = max
              walk(i, maxIndex).foreach(walk => walks=walks :+ (i -> j) -> (walk :+ j))
          }
          j += 1
        }
        i += 1
      }
    }
    new MaxPlusTropicalSquareMatrix[T](product, Map.from(walks))
  }
}

object MaxPlusTropicalSquareMatrix {
  def apply[T](dimension: Int, values: Map[(Int, Int), FiniteValue[T]])
              (implicit additive: Monoid[T], ord: Ordering[T]) = {
    val matrix = Array.fill[MaxPlusDomain[T]](dimension, dimension)(NegativeInfinity)
    var walks = scala.collection.mutable.ListBuffer.empty[((Int, Int), IndexedSeq[Int])]
    values.foreachEntry { case ((from, to), value) =>
      matrix(from)(to) = value
      walks = walks :+ (from -> to) -> IndexedSeq(from, to)
    }

    new MaxPlusTropicalSquareMatrix[T](matrix, Map.from(walks))
  }
}
```
- to single out only those closed walks that form simple cycles, e.g., by using the tortoise and the hare algorithm:

```scala
def isSimpleCycle(cycle: IndexedSeq[Int]): Boolean = {
  val next = scala.collection.mutable.Map.empty[Int, Int]
  for (i <- 0 until cycle.size - 1) next(cycle(i)) = cycle(i + 1)
  val start = cycle(0)
  var (slow, fast) = (next(start), next(next(start)))
  while (slow != fast) {
    slow = next(slow)
    fast = next(next(fast))
  }

  var mu = 0
  slow = start
  while (slow != fast) {
    slow = next(slow)
    fast = next(fast)
    mu += 1
  }

  var lambda = 1
  fast = next(slow)
  while (slow != fast) {
    fast = next(fast)
    lambda += 1
  }
  mu == 0 && lambda == cycle.size - 1
}
```
- compute $D$’s tropical powers until the number of the graph’s vertices, and choose the maximal diagonal value among them, which corresponds to a simple cycle:

```scala
val (index2Currency, distanceMatrix) = buildDistanceMatrix(fxRates)

var (highestPositiveExponent, bestStrategy) = (ZERO, none[Seq[CurrencyCode]])

var powerOfDistanceMatrix = distanceMatrix
val values = Array.ofDim[MaxPlusDomain[BigDecimal]](powerOfDistanceMatrix.dimension)
for (_ <- 1 until powerOfDistanceMatrix.dimension) {
        powerOfDistanceMatrix *= distanceMatrix
        for (i <- 0 until powerOfDistanceMatrix.dimension) {
          values(i) = powerOfDistanceMatrix.walk(i, i).filter(isSimpleCycle).map(_ => powerOfDistanceMatrix(i, i)).getOrElse(NegativeInfinity)
        }
        MaxPlusDomain.argMax(values) match {
          case (_, NegativeInfinity) => ()
          case (Some(maxIndex), max: FiniteValue[BigDecimal]) =>
            if (max.value.bigDecimal.compareTo(highestPositiveExponent) > 0) {
              highestPositiveExponent = max.value.bigDecimal
              bestStrategy = powerOfDistanceMatrix.walk(maxIndex, maxIndex).map(_.map(index2Currency))
            }
        }
      }
```      
- and, finally, to somehow transform the weights of the graph’s edges to make sense within the new framework; fortunately, that bullet can be struck through by taking the logarithms of the weights, as per Sedgewick and Wayne:

```scala
def buildDistanceMatrix(fxRates: Map[CurrencyPair, PosBigDecimal]):
(Map[Int, CurrencyCode], MaxPlusTropicalSquareMatrix[BigDecimal]) = {
  val currency2index = scala.collection.mutable.Map.empty[CurrencyCode, Int]

  var nextIndex = 0

  def nextAvailableIdx: Int = {
    val idx = nextIndex
    nextIndex += 1
    idx
  }

  val matrixValues = fxRates.filter(_._2.value != ZERO).map { case (currencyPair, rate) =>
    val (base, quote) = currencyPair
    val from = currency2index.getOrElseUpdate(base, nextAvailableIdx)
    val to = currency2index.getOrElseUpdate(quote, nextAvailableIdx)

    ((from, to), FiniteValue(BigDecimal(DefaultBigDecimalMath.log(rate.value.bigDecimal))))
  }

  val index2currency = Map.from(currency2index.map{case (currency, index) => index -> currency})

  (index2currency, MaxPlusTropicalSquareMatrix[BigDecimal](nextIndex, matrixValues))
}
```

All those combined lead to an algorithm for discovering the best arbitrage opportunities that runs in $O(n^4)$, where $n$ is the number of traded instruments.
Check out [the GitHub repository](https://github.com/mplevako/arbitrageur) for the code and addenda.

The well-known trick of exponentiation by squaring can be used to improve the complexity to $O(n^3\log n)$.

However, there exists [a method](https://arxiv.org/abs/1312.6680v2), tailored exactly for computing the tropical product of two $n$ by $n$ matrices, that, after being substituted instead of my naive multiplication procedure, will yield a subquartic arbitrage opportunity detection algorithm running in $n^4\over 2^{\log^d n}$ time for some positive $d$ on the real RAM, where additions and comparisons of reals are unit cost.