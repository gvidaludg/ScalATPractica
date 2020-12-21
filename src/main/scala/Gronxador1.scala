object Gronxador1 extends App {
  val e = new ScalAT("Gronxador1")


  //Numeracio dels seients:
  // 0 1 2 3 4 /\ 5 6 7 8 9

  val seuA = e.newVarArray(5) //El nen A anira a l'esquerra
  val seuB = e.newVarArray(10)
  val seuC = e.newVarArray(10)

  val pesA = 9; // 36/4
  val pesB = 8; // 32/4
  val pesC = 4; // 16/4

  //Cada nen seu a un sol seient
  e.addEOQuad(seuA.toList)
  e.addEOQuad(seuB.toList)
  e.addEOQuad(seuC.toList)

  //A cada seient nomes hi seu un nen
  for (seient <- 0 to 4) {
    e.addAMOQuad(seuA(seient) :: seuB(seient) :: seuC(seient) :: List())
  }
  for (seient <- 5 to 9) {
    e.addAMOQuad(seuB(seient) :: seuC(seient) :: List())
  }


  //El gronxador està balancejat (PB constraint)
  var literals: List[Int] = List()
  var K: Int = 0

  //Seients de la esquerra
  for (seient <- 0 to 4) {

    for (_ <- 1 to pesA * (5 - seient))
      literals ::= seuA(seient)

    for (_ <- 1 to pesB * (5 - seient))
      literals ::= seuB(seient)

    for (_ <- 1 to pesC * (5 - seient))
      literals ::= seuC(seient)

  }

  //Seients de la dreta
  for (seient <- 5 to 9) {

    for (_ <- 1 to pesB * (seient - 4))
      literals ::= -seuB(seient)

    for (_ <- 1 to pesC * (seient - 4))
      literals ::= -seuC(seient)

    K += pesB * (seient - 4) + pesC * (seient - 4)

  }


  //Afegim el cardinality constraint (desplegat): PesEsquerra - PesDreta = 0
  e.addEK(literals, K)

  //Solucionem
  val result = e.solve()
  println(result)
  if (result.satisfiable) {

    for (i <- 0 to 4)
      if (e.getValue(seuA(i)))
        println("El nen A seu al seient " + i)

    for (i <- 0 to 9)
      if (e.getValue(seuB(i)))
        println("El nen B seu al seient " + i)

    for (i <- 0 to 9)
      if (e.getValue(seuC(i)))
        println("El nen C seu al seient " + i)
  }
}


