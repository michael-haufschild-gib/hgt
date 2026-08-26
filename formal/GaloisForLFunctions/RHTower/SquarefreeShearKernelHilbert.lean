import GaloisForLFunctions.RHTower.SquarefreeShearKernelFourier

/-!
# Hilbert packet form of the squarefree shear kernel

This module specializes the existing common-profile Boolean anchor-curvature theorem to the
canonical CRT coordinates of a certified distinct-prime family.  It identifies coordinate
nonvanishing with literal coprimality to each selected prime subproduct and proves the two Hilbert
equalities in `(SG6)` without replacing the arithmetic packet by an abstract surrogate.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Boolean nonzero indicator of one canonical CRT coordinate. -/
def squarefreePrimeNonzeroCoordinate
    {k : ℕ} (P : SquarefreePrimeFamily k) (i : Fin k) (x : ZMod P.product) : ℝ :=
  if (GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P x) i = 0 then 0 else 1

/-- The common-anchor weight on all CRT coordinates is the literal zero-product incidence
indicator. -/
theorem squarefreePrimeCommonAnchorWeight_eq
    {k : ℕ} (P : SquarefreePrimeFamily k) (x y : ZMod P.product) :
    commonAnchorWeight Finset.univ (squarefreePrimeNonzeroCoordinate P) x y =
      if x * y = 0 then 1 else 0 := by
  classical
  let E := GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P
  letI (i : Fin k) : Fact (P.primeValue i).Prime := ⟨P.prime i⟩
  unfold commonAnchorWeight
  by_cases hxy : x * y = 0
  · rw [if_pos hxy]
    apply Finset.prod_eq_one
    intro i _
    have hi := congrFun (congrArg E hxy) i
    simp only [map_mul, map_zero, Pi.mul_apply, Pi.zero_apply] at hi
    rcases mul_eq_zero.mp hi with hxi | hyi
    · simp [squarefreePrimeNonzeroCoordinate, E, hxi]
    · simp [squarefreePrimeNonzeroCoordinate, E, hyi]
  · rw [if_neg hxy]
    have hnotall : ¬ ∀ i, E x i * E y i = 0 := by
      intro hall
      apply hxy
      apply E.injective
      ext i
      simpa [map_mul] using hall i
    push Not at hnotall
    obtain ⟨i, hi⟩ := hnotall
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    have hxi : E x i ≠ 0 := fun hx => hi (by simp [hx])
    have hyi : E y i ≠ 0 := fun hy => hi (by simp [hy])
    simp [squarefreePrimeNonzeroCoordinate, E, hxi, hyi]

/-- Coordinate-weight presentation of one coprime packet, used to invoke the generic Boolean
anchor-curvature theorem. -/
def squarefreePrimeCoprimeCoordinatePacket
    {k : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : SquarefreePrimeFamily k) (ξ : ZMod P.product → H) (S : Finset (Fin k)) : H :=
  commonProfileSiftedVector Finset.univ S (squarefreePrimeNonzeroCoordinate P) ξ

/-- Product of the selected labelled primes. -/
def squarefreePrimeSubproduct
    {k : ℕ} (P : SquarefreePrimeFamily k) (S : Finset (Fin k)) : ℕ :=
  ∏ i ∈ S, P.primeValue i

/-- Coprimality to a selected prime subproduct is exactly nonvanishing of every selected canonical
CRT coordinate. -/
theorem squarefreePrime_coprime_subproduct_iff
    {k : ℕ} (P : SquarefreePrimeFamily k) (S : Finset (Fin k)) (x : ZMod P.product) :
    Nat.Coprime x.val (squarefreePrimeSubproduct P S) ↔
      ∀ i ∈ S,
        (GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P x) i ≠ 0 := by
  classical
  let E := GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P
  rw [squarefreePrimeSubproduct, Nat.coprime_prod_right_iff]
  apply forall_congr'
  intro i
  apply imp_congr_right
  intro hi
  rw [Nat.coprime_comm, (P.prime i).coprime_iff_not_dvd]
  have hcast : (x.val : ZMod (P.primeValue i)) = E x i := by
    simpa [E] using squarefreePrime_crtEquiv_symm_val_cast P (E x) i
  have hmod : ((x.val : ZMod (P.primeValue i)) = 0) ↔ P.primeValue i ∣ x.val := by
    exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd (x.val : ℤ) (P.primeValue i))
  simpa [hcast] using (not_congr hmod).symm

/-- Selected-coordinate weight equals the literal coprimality indicator. -/
theorem squarefreePrime_coordinatePacketWeight_eq_coprimeIndicator
    {k : ℕ} (P : SquarefreePrimeFamily k) (S : Finset (Fin k)) (x : ZMod P.product) :
    coordinatePacketWeight S (squarefreePrimeNonzeroCoordinate P) x =
      if Nat.Coprime x.val (squarefreePrimeSubproduct P S) then 1 else 0 := by
  classical
  have hiff := squarefreePrime_coprime_subproduct_iff P S x
  by_cases hcop : Nat.Coprime x.val (squarefreePrimeSubproduct P S)
  · rw [if_pos hcop]
    have h := hiff.mp hcop
    apply Finset.prod_eq_one
    intro i hi
    simp [squarefreePrimeNonzeroCoordinate, h i hi]
  · rw [if_neg hcop]
    have h : ¬ ∀ i ∈ S,
        (GaloisForLFunctions.IrregularStokes.DistinctPrimeFamily.crtEquiv P x) i ≠ 0 :=
      fun hall => hcop (hiff.mpr hall)
    push Not at h
    obtain ⟨i, hi, hix⟩ := h
    unfold coordinatePacketWeight
    apply Finset.prod_eq_zero hi
    simp [squarefreePrimeNonzeroCoordinate, hix]

/-- Literal packet `sum_(gcd(x, product_(i in S) p_i)=1) ξ_x`. -/
def squarefreePrimeCoprimePacket
    {k : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : SquarefreePrimeFamily k) (ξ : ZMod P.product → H) (S : Finset (Fin k)) : H :=
  ∑ x, if Nat.Coprime x.val (squarefreePrimeSubproduct P S) then ξ x else 0

/-- Literal coprime packet equals its reusable common-profile coordinate presentation. -/
theorem squarefreePrimeCoprimePacket_eq_coordinatePacket
    {k : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : SquarefreePrimeFamily k) (ξ : ZMod P.product → H) (S : Finset (Fin k)) :
    squarefreePrimeCoprimePacket P ξ S = squarefreePrimeCoprimeCoordinatePacket P ξ S := by
  classical
  letI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
  rw [squarefreePrimeCoprimePacket, squarefreePrimeCoprimeCoordinatePacket,
    commonProfileSiftedVector]
  apply Finset.sum_congr rfl
  intro x _
  rw [squarefreePrime_coordinatePacketWeight_eq_coprimeIndicator]
  by_cases hx : Nat.Coprime x.val (squarefreePrimeSubproduct P S) <;> simp [hx]

/-- Real part of the zero-product Gram form is the signed Boolean packet energy.  The proof is the
existing common-Gram Boolean anchor-curvature theorem specialized to CRT nonzero indicators. -/
theorem squarefreePrimeZeroProductGram_re_eq_signedPacketNormSq
    {k : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : SquarefreePrimeFamily k) (ξ : ZMod P.product → H) :
    (squarefreePrimeZeroProductGram P ξ).re =
      ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        (-1 : ℝ) ^ S.card * ‖squarefreePrimeCoprimeCoordinatePacket P ξ S‖ ^ 2 := by
  classical
  letI : NormedSpace ℝ H := NormedSpace.restrictScalars ℝ ℂ H
  letI : InnerProductSpace ℝ H := InnerProductSpace.rclikeToReal ℂ H
  have h := commonGramBooleanAnchorCurvature
    (indices := (Finset.univ : Finset (ZMod P.product)))
    (base := (∅ : Finset (Fin k)))
    (anchor := Finset.univ)
    (hdisj := Finset.disjoint_empty_left Finset.univ)
    (coordinate := squarefreePrimeNonzeroCoordinate P)
    (g := ξ)
  rw [squarefreePrimeZeroProductGram]
  change Complex.reCLM (∑ x, ∑ y, if x * y = 0 then inner ℂ (ξ x) (ξ y) else 0) = _
  rw [map_sum Complex.reCLM]
  simp_rw [map_sum Complex.reCLM]
  simp_rw [squarefreePrimeCommonAnchorWeight_eq P] at h
  simpa [squarefreePrimeCoprimeCoordinatePacket, commonProfileSiftedEnergy,
    coordinatePacketWeight, real_inner_eq_re_inner, apply_ite] using h

/-- The zero-product Gram form is real, by symmetry of zero-product incidence and Hermitian
symmetry of the inner product. -/
theorem star_squarefreePrimeZeroProductGram
    {k : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : SquarefreePrimeFamily k) (ξ : ZMod P.product → H) :
    star (squarefreePrimeZeroProductGram P ξ) =
      squarefreePrimeZeroProductGram P ξ := by
  classical
  rw [squarefreePrimeZeroProductGram, star_sum]
  simp_rw [star_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : x * y = 0
  · have hyx : y * x = 0 := by simpa [mul_comm] using hxy
    simp [hxy, hyx]
  · have hyx : y * x ≠ 0 := by simpa [mul_comm] using hxy
    simp [hxy, hyx]

/-- Complex zero-product Gram form equals the cast of the signed coordinate-packet norm square. -/
theorem squarefreePrimeZeroProductGram_eq_signedPacketNormSq
    {k : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : SquarefreePrimeFamily k) (ξ : ZMod P.product → H) :
    squarefreePrimeZeroProductGram P ξ =
      ((∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        (-1 : ℝ) ^ S.card * ‖squarefreePrimeCoprimeCoordinatePacket P ξ S‖ ^ 2 : ℝ) : ℂ) := by
  have hreal := Complex.conj_eq_iff_re.mp (star_squarefreePrimeZeroProductGram P ξ)
  rw [← hreal]
  exact congrArg (fun r : ℝ => (r : ℂ))
    (squarefreePrimeZeroProductGram_re_eq_signedPacketNormSq P ξ)

/-- Second equality of `(SG6)`: the zero-product Gram form is the literal alternating sum of
squared norms of packets coprime to every selected prime subproduct. -/
theorem squarefreePrimeZeroProductGram_eq_signedCoprimePacketNormSq
    {k : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : SquarefreePrimeFamily k) (ξ : ZMod P.product → H) :
    squarefreePrimeZeroProductGram P ξ =
      ((∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        (-1 : ℝ) ^ S.card * ‖squarefreePrimeCoprimePacket P ξ S‖ ^ 2 : ℝ) : ℂ) := by
  rw [squarefreePrimeZeroProductGram_eq_signedPacketNormSq]
  congr 1
  apply Finset.sum_congr rfl
  intro S _
  rw [squarefreePrimeCoprimePacket_eq_coordinatePacket]

/-- Full `(SG6)`: the Fourier shear packet form equals `l²` times the alternating literal coprime
packet norm square. -/
theorem squarefreePrimeShearPacketForm_eq_signedCoprimePacketNormSq
    {k : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (P : SquarefreePrimeFamily k) (ξ : ZMod P.product → H) :
    squarefreePrimeShearPacketForm P ξ =
      (P.product : ℂ) ^ 2 *
        ((∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
          (-1 : ℝ) ^ S.card * ‖squarefreePrimeCoprimePacket P ξ S‖ ^ 2 : ℝ) : ℂ) := by
  rw [squarefreePrimeShearPacketForm_eq_zeroProductGram,
    squarefreePrimeZeroProductGram_eq_signedCoprimePacketNormSq]

end

end RHTower
