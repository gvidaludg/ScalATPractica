object NQueens extends App {

  val e = new ScalAT("NQueens")

  //Nombre de reines
  val n = 8

  //tauler(i)(j) es cert sii a la casella (i,j) hi ha una reina
  val tauler: Array[Array[Int]] = e.newVar2DArray(n, n)

  //A cada fila hi ha una reina
  for (i <- tauler) e.addEOQuad(i.toList)

  //A cada columna hi ha una reina
  for (i <- tauler.transpose) e.addEOQuad(i.toList)

  //A cada contradiagonal hi ha com a molt una reina
  for (v <- 0 to 2 * n - 2) {
    e.addAMOQuad((for (i <- 0 until n; j <- 0 until n; if i + j == v) yield tauler(i)(j)).toList)
  }

  //A cada diagonal hi ha com a molt una reina
  for (v <- -n + 1 until n) {
    e.addAMOQuad((for (i <- 0 until n; j <- 0 until n; if i - j == v) yield tauler(i)(j)).toList)
  }

  def getQueensPositions = tauler
    .map(_.map((i: Int) => if (e.getValue(i)) "X " else ". "))
    .map(_.mkString(""))
    .mkString("\n")

  val result=e.solve()
  println(result)
  if (result.satisfiable) println(getQueensPositions)


}
