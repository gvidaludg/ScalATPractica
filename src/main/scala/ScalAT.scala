import java.io._

import org.sat4j.minisat.SolverFactory
import org.sat4j.reader.DimacsReader
import org.sat4j.specs.{IProblem, ISolver}

import scala.Array._
import scala.collection.JavaConverters._
import scala.io.Source
import scala.math._

// Case class to deal with SAT solver results. ToString overrided to properly show result and stats.
case class SolverResult(model: Array[Boolean], time: Double, satisfiable: Boolean, stats: Map[String, Number]) {
  override def toString = {
    (List(if (this.satisfiable) "Safisfiable\n" else "Unsatisfiable\n", "Time: " + time.toString + "\n", "Stats:\n")
      ++ (for ((k, v) <- stats) yield (k + ": " + v))).mkString("\n")
  }
}


class ScalAT(problemName: String = "", workingpath: String = "working/") {
  //Working directory path. Files named "tmp.dimacs" and "tmp.res" will be stored there,
  // overwriting any existing file with that name. These are the input and the output of the solver respectively.
  // Read and write privileges to the directory are required

  // private function to deal with time
  private def timeMeasurement[A](block: => A, message: String = ""): (A, Double) = {
    val t0 = System.nanoTime()
    val result = block
    val t1 = System.nanoTime()
    val elapsed_time = (t1 - t0) / 1000000000.0
    (result, elapsed_time)
  }

  // private vars to
  private val tmp_pre_dimacs: String = workingpath + problemName + "_tmp_pre.dimacs"
  private val preDimacs: PrintWriter = new PrintWriter(new File(tmp_pre_dimacs))
  private val tmp_dimacs = workingpath + problemName + "_tmp.dimacs"

  // currently not used
  // private val tmp_res = workingpath + problemName + "_tmp.res"

  // Number of Boolean variables (starting with 2 because of true and false)
  var vars: Int = 1

  // List of clauses in  DIMACS format (lists of Int (literals), negative for the negated literals)
  var nclauses: Int = 1

  //Result of the call to the SAT solver
  var satisfiable = false

  //SAT solver solving statistics
  var conflicts = 0
  var propagations = 0
  var decisions = 0
  var time: Double = 0.0

  //Model of the formula (if it is satisfiable)
  private var model: Array[Boolean] = new Array[Boolean](1)

  val getTrue = 1 //Trivially true variable. Used as the "true" constant
  val getFalse: Int = -1 //Trivially false variable. Used as the "false" constant

  // Introduces a fresh var and returns its corresponding id
  def newVar(): Int = {
    vars += 1;
    vars
  }

  // Introduces l fresh variables and returns them in an array
  def newVarArray(l: Int): Array[Int] = {
    var z: Array[Int] = new Array[Int](l)
    z = (vars + 1 to vars + l).toList.toArray
    vars += l
    z
  }

  // Introduces l*m fresh variables and returns them in a 2D array
  def newVar2DArray(l: Int, m: Int): Array[Array[Int]] = {
    val z: Array[Array[Int]] = Array.ofDim[Int](l, m)
    for (i <- 0 until l) {
      z(i) = (vars + 1 to vars + m).toList.toArray
      vars += m
    }
    z
  }

  // Introduces l*m*n fresh variables and returns them in a 3D array
  def newVar3DArray(l: Int, m: Int, n: Int): Array[Array[Array[Int]]] = {
    val z = ofDim[Int](l, m, n)
    for (i <- 0 until l) {
      for (j <- 0 until m) {
        z(i)(j) = (vars + 1 to vars + n).toList.toArray
        vars += n
      }
    }
    z
  }

  // Introduces l*m*n*o fresh variables and returns them in a 4D array
  def newVar4DArray(l: Int, m: Int, n: Int, o: Int): Array[Array[Array[Array[Int]]]] = {
    val z = ofDim[Int](l, m, n, o)
    for (i <- 0 until l) {
      for (j <- 0 until m) {
        for (k <- 0 until n) {
          z(i)(j)(k) = (vars + 1 to vars + o).toList.toArray
          vars += o
        }
      }
    }
    z
  }


  //Get the value of var 'v' in the found model.
  //It is required that we have previously called teh solve() method and that it has retured true
  def getValue(v: Int): Boolean = model(v)

  //Get number of clauses (ignoring true and false constant setting)
  def getNClauses: Int = nclauses - 1

  //Get number of variables (ignoring true and false constant)
  def getNVars: Int = vars - 1

  //Get solver statistics
  def getConflicts: Int = conflicts

  def getPropagations: Int = propagations

  def getDecisions: Int = decisions

  def getTime: Double = time


  //Adds the clause l(0) \/ l(1) \/ ... \/ l(l.length-1). The empty list (clause) is also supported
  def addClause(c: List[Int]): Unit = {
    for (l <- c) preDimacs.write(l.toString + " ")
    preDimacs.write("0\n")
    nclauses += 1
  }

  //Adds the quadratic encoding of the at-most-one
  def addAMOQuad(l: List[Int]): Unit = {
    for (i <- 0 to l.length - 2)
      for (j <- i + 1 until l.length)
        addClause(-l(i) :: -l(j) :: List())
  }

  //Adds the logaritic encoding of the at-most-one
  def addAMOLog(x: List[Int]): Unit = ???

  //Adds the encoding of the at-least-one.
  def addALO(l: List[Int]): Unit = addClause(l)

  //Adds the encoding of the exactly-one using the quadratic at-most-one
  def addEOQuad(l: List[Int]): Unit = {
    addAMOQuad(l)
    addALO(l)
  }

  //Adds the encoding of the exactly-one using the logaritmic at-most-one
  def addEOLog(l: List[Int]): Unit = {
    addAMOLog(l)
    addALO(l)
  }

  //Adds the encoding of a 2 comparator
  //The arguments are literals
  //All variables must have been created with one of the newVar methods.
  def addCMP2(x1: Int, x2: Int, y1: Int, y2: Int) {
    //y1 <-> x1 \/ x2
    addClause(-y1 :: x1 :: x2 :: List())
    addClause(-x1 :: y1 :: List())
    addClause(-x2 :: y1 :: List())

    //y2 <-> x1 /\ x2
    addClause(-y2 :: x1 :: List())
    addClause(-y2 :: x2 :: List())
    addClause(-x1 :: -x2 :: y2 :: List())
  }

  //Ads the encodig of "sort x decreasingly into y". Both lists must have equal length, and empty lists are not allowed
  //The lists contain literals
  //All variables must have been created with one of the newVar methods.
  def addSorter(x: List[Int], y: List[Int]) {
    assert(x.length == y.length)
    assert(x.nonEmpty)
    if (x.length == 1) {
      addClause(-x(0) :: y(0) :: List())
      addClause(x(0) :: -y(0) :: List())
    }
    else if (x.length == 2)
      addCMP2(x(0), x(1), y(0), y(1))
    else {
      var xp: List[Int] = List()
      var yp: List[Int] = List()
      while (!isPowerOfTwo(x.length + xp.length)) {
        xp ::= getFalse
        yp ::= getFalse
      }
      xp = x ::: xp
      yp = y ::: yp

      val x1 = xp.take(xp.length / 2)
      val x2 = xp.drop(xp.length / 2)

      val z1 = newVarArray(xp.length / 2).toList
      val z2 = newVarArray(xp.length / 2).toList

      addSorter(x1, z1)
      addSorter(x2, z2)
      addMerge(z1, z2, yp)
    }
  }

  //Adds the encoding of "merge the decreasingly sorted lists x and xp into y"
  //x and xp must be of equal lenght and nonempty. y must have twice the lenght of x
  //The lists contain literals
  //All variables must have been created with one of the newVar methods.
  def addMerge(x: List[Int], xp: List[Int], y: List[Int]) {
    assert(x.length == xp.length)
    assert(x.nonEmpty)
    assert(2 * x.length == y.length)

    if (x.length == 1)
      addCMP2(x(0), xp(0), y(0), y(1))
    else {

      val xeven = (for (i <- 0 to x.length - 2 by 2) yield x(i)).toList
      val xodd = (for (i <- 1 until x.length by 2) yield x(i)).toList

      val xpeven = (for (i <- 0 to xp.length - 2 by 2) yield xp(i)).toList
      val xpodd = (for (i <- 1 until xp.length by 2) yield xp(i)).toList

      val zevenp = newVarArray(x.length - 1).toList
      val zoddp = newVarArray(x.length - 1).toList
      val zeven = y(0) :: zevenp
      val zodd = zoddp ::: List(y.last)

      addMerge(xeven, xpeven, zeven)
      addMerge(xodd, xpodd, zodd)

      for (((i, j), k) <- zevenp.zip(zoddp).zip(1 to zevenp.length)) addCMP2(i, j, y(2 * k - 1), y(2 * k))
    }

  }

  //Adds the encoding of an exactly-K constraint.
  // x can be empty, and K take any value from -infinity to infinity
  def addEK(x: List[Int], K: Int): Unit = ???



  //Adds the encoding of an at-least-K constraint.
  // x can be empty, and K take any value from -infinity to infinity
  def addALK(x: List[Int], K: Int): Unit = ???

  //Adds the encoding of an at-most-K constraint.
  // x can be empty, and K take any value from -infinity to infinity
  def addAMK(x: List[Int], K: Int): Unit = ???


  //Adds a PB constraint of the form q[0]x[0] + q[1]x[1] + ... + q[n]x[n] <= K
  //q must be a list of non-negative coefficients, and x a list of literals.
  def addPB(q: List[Int], x: List[Int], K: Int) {
    //We can get rid of literals with coefficient = 0
    val x2 = x
    x2.zip(q).collect { case (lit, 0) => lit }

    if (K < 0)
      addClause(List()); //Empty clause

    else if (K == 0) { //All literals must be false
      for (l <- x2)
        addClause(-l :: List())
    }

    else if (0 < K && K < x.sum) { //Otherwise, constraint trivially satisfied
      val n = x2.length
      var Sout: Array[Int] = new Array[Int](K)
      for (i <- 0 until K)
        Sout(i) = getFalse

      for (i <- 0 until n) {
        val Sin = Sout

        if (i < n - 1)
          Sout = newVarArray(K)

        if (i < n - 1 && i > 0)
          for (j <- 0 until K)
            addClause(-Sin(j) :: Sout(j) :: List())

        if (i < n - 1) {
          for (j <- 0 until q(i)) {
            addClause(-x(i) :: Sout(j) :: List())
          }
        }

        if (i > 0 && i < n - 1) {
          for (j <- 0 until K - q(i)) {
            addClause(-Sin(j) :: -x(i) :: Sout(j + q(i)) :: List())
          }
        }

        if (i > 0) {
          addClause(-Sin(K - q(i)) :: -x(i) :: List())
        }
      }
    }
  }


  //Returns true iff x is power of 2. Non-negative integer required
  def isPowerOfTwo(x: Int): Boolean = {
    var n = x
    if (n == 0) return false
    while (n != 1) {
      if (n % 2 != 0) return false
      n = n / 2
    }
    true
  }

  private def createDIMACSFile = {
    preDimacs.close()
    println("Creating DIMACS file: " + tmp_dimacs)
    val dimacs = new PrintWriter(new File(tmp_dimacs))
    dimacs.write("p cnf " + vars.toString + " " + nclauses.toString + "\n")
    dimacs.write("1 0\n") //True constant

    val sourcePredimacs = Source.fromFile(tmp_pre_dimacs)
    for (line <- sourcePredimacs.getLines()) dimacs.write(line + "\n")

    sourcePredimacs.close()
    dimacs.close()
  }

  //Calls the sat4j solver and retrieves the result of the call
  //Returns whether the formula CNF in 'clauses' is satisfiable, and if so, stores a model into 'model'

  private def mapModelResults(modelInt: Array[Int]) = {
    model = new Array[Boolean](vars + 1)
    for (i <- modelInt if i > 0) model(i) = true
  }

  private def runSAT4Jembedded = {
    val solver: ISolver = SolverFactory.newDefault
    solver.setTimeout(3600) // 1 hour timeout
    val reader = new DimacsReader(solver)
    // CNF filename is given on the command line
    val problem: IProblem = reader.parseInstance(tmp_dimacs)
    val (satisfiable, elapsedtime) = timeMeasurement(problem.isSatisfiable())
    val s: ISolver = problem.asInstanceOf[ISolver]
    if (satisfiable) {
      mapModelResults(problem.model)
      SolverResult(this.model, elapsedtime, true, s.getStat.asScala.toMap)
    }
    else
      SolverResult(this.model, elapsedtime, false, s.getStat.asScala.toMap)
  }

  def solve() = {
    createDIMACSFile
    runSAT4Jembedded
  }


}
