

object TestSorter extends App {

  val e = new ScalAT("TestSorter")


  //Comprovem el funcionament d'un sorter


  val n = 30
  val x = e.newVarArray(n)
  val y = e.newVarArray(n)

  //Creem una llista desordenada 'x'
  for (i <- 0 until n) {
    if (i % 3 == 0)
      e.addClause(x(i) :: List())
    else
      e.addClause(-x(i) :: List())
  }

  //Ordenem x
  e.addSorter(x.toList, y.toList)

  //Solucionem
  val result = e.solve()
  println(result)
  if (result.satisfiable) {
    print("x: ")
    for (v <- x) {
      print(if (e.getValue(v)) "1 " else "0 ")
    }
    println()
    print("y: ")
    for (v <- y) {
      print(if (e.getValue(v)) "1 " else "0 ")
    }
  }


}

