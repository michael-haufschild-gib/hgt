import GaloisForLFunctions.HTGeometry.RittSubleadingSlice

/-!
# The denominator of a shifted coprime fraction is an exact eigenvector

Slicing a relation `σ W = c·W + (α·t + β)` in a coordinate the shift moves affinely,
`σ t = a·t + b`, writes `W = P/Q` as a coprime fraction with `Q` monic and produces the cross
relation between the twisted numerator and denominator.  Coprimality then splits that single
relation into two exact polynomial identities:

`Q^Φ(aX + b) = a^{deg Q}·Q`,   `P^Φ(aX + b) = a^{deg Q}·(c·P + (αX + β)·Q)`.

The first is entirely free of the eigenvalue and of the inhomogeneity: the denominator alone is a
twisted eigenvector of the affine substitution with scalar `a^{deg Q}`.  Reading it one degree below
the top — where the monic leading coefficient contributes `deg Q · a^{deg Q − 1} · b` — leaves the
affine relation

`Φ(Q_{deg Q − 1}) + deg Q · b = a · Q_{deg Q − 1}`

for a single coefficient field element, with eigenvalue exactly `a` and with the constant term `b` of
the shift as its inhomogeneity.  So a denominator of positive degree always hands back an affine
relation one level down whose eigenvalue is the coordinate's own multiplier.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {K : Type*} [Field K]

/-- **The denominator identity.**  Coprimality forces the twisted denominator to be the denominator
itself, scaled by a power of the multiplier. -/
theorem twistComp_denominator_eq (Φ : K →+* K) {a b c α β : K}
    (ha : a ≠ 0) (hc : c ≠ 0) {P Q : K[X]} (hQ : Q.Monic) (hcop : IsCoprime P Q)
    (hcross : twistComp Φ (C a * X + C b) P * Q
      = twistComp Φ (C a * X + C b) Q * (C c * P + (C α * X + C β) * Q)) :
    twistComp Φ (C a * X + C b) Q = C (a ^ Q.natDegree) * Q := by
  classical
  set T : K[X] := C a * X + C b with hT
  have hTdeg : T.natDegree = 1 := natDegree_linear ha
  have hTlead : T.leadingCoeff = a := leadingCoeff_linear ha
  have hQ0 : Q ≠ 0 := hQ.ne_zero
  have hcopQ : IsCoprime Q (C c * P + (C α * X + C β) * Q) := by
    have hcu : IsUnit (C c : K[X]) := isUnit_C.mpr (Ne.isUnit hc)
    have h1 : IsCoprime Q (C c * P) :=
      (isCoprime_mul_unit_left_right hcu _ _).mpr hcop.symm
    have h2 := h1.add_mul_left_right (C α * X + C β)
    have heq : C c * P + Q * (C α * X + C β) = C c * P + (C α * X + C β) * Q := by ring
    rwa [heq] at h2
  have hdvd : Q ∣ twistComp Φ T Q := by
    refine hcopQ.dvd_of_dvd_mul_right ?_
    exact ⟨twistComp Φ T P, by rw [← hcross]; ring⟩
  obtain ⟨d, hd0, hd⟩ :=
    eq_C_mul_of_dvd_of_natDegree_eq (twistComp_ne_zero Φ hTdeg hQ0) hdvd
      (natDegree_twistComp Φ hTdeg Q)
  have hde : d = a ^ Q.natDegree := by
    have hlead := leadingCoeff_twistComp Φ hTdeg Q
    rw [hd, hQ.leadingCoeff, map_one, hTlead, one_mul] at hlead
    rw [leadingCoeff_mul, leadingCoeff_C, hQ.leadingCoeff, mul_one] at hlead
    exact hlead
  rw [hd, hde]

/-- **The numerator identity.**  After the denominator is cancelled the numerator satisfies the
relation exactly, with the same scalar. -/
theorem twistComp_numerator_eq (Φ : K →+* K) {a b c α β : K}
    (ha : a ≠ 0) (hc : c ≠ 0) {P Q : K[X]} (hQ : Q.Monic) (hcop : IsCoprime P Q)
    (hcross : twistComp Φ (C a * X + C b) P * Q
      = twistComp Φ (C a * X + C b) Q * (C c * P + (C α * X + C β) * Q)) :
    twistComp Φ (C a * X + C b) P
      = C (a ^ Q.natDegree) * (C c * P + (C α * X + C β) * Q) := by
  refine mul_right_cancel₀ hQ.ne_zero ?_
  rw [hcross, twistComp_denominator_eq Φ ha hc hQ hcop hcross]
  ring

/-- **The subleading coefficient of the denominator.**  A denominator of positive degree carries an
affine relation whose eigenvalue is the multiplier of the coordinate and whose inhomogeneity is a
multiple of the constant term of the shift. -/
theorem denominator_subleading_relation (Φ : K →+* K) {a b c α β : K}
    (ha : a ≠ 0) (hc : c ≠ 0) {P Q : K[X]} (hQ : Q.Monic) (hcop : IsCoprime P Q)
    (hQdeg : 1 ≤ Q.natDegree)
    (hcross : twistComp Φ (C a * X + C b) P * Q
      = twistComp Φ (C a * X + C b) Q * (C c * P + (C α * X + C β) * Q)) :
    Φ (Q.coeff (Q.natDegree - 1)) + (Q.natDegree : K) * b
      = a * Q.coeff (Q.natDegree - 1) := by
  classical
  have hden := twistComp_denominator_eq Φ ha hc hQ hcop hcross
  have hmapdeg : (Q.map Φ).natDegree ≤ (Q.natDegree - 1) + 1 := by
    have := natDegree_map_le (f := Φ) (p := Q)
    omega
  have hidx : (Q.natDegree - 1) + 1 = Q.natDegree := by omega
  have hcast : ((Q.natDegree - 1 : ℕ) : K) + 1 = (Q.natDegree : K) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → K) hidx
  have hlead : Q.coeff Q.natDegree = 1 := hQ.coeff_natDegree
  have hcoeff := congrArg (fun R : K[X] => R.coeff (Q.natDegree - 1)) hden
  simp only [twistComp] at hcoeff
  rw [coeff_comp_linear_sub_one ha hmapdeg, coeff_C_mul, coeff_map, coeff_map, hidx,
    hlead, map_one] at hcoeff
  have hapow : a ^ Q.natDegree = a ^ (Q.natDegree - 1) * a := by
    conv_lhs => rw [← hidx]
    rw [pow_succ]
  rw [hapow] at hcoeff
  have hane : a ^ (Q.natDegree - 1) ≠ 0 := pow_ne_zero _ ha
  refine mul_left_cancel₀ hane ?_
  rw [← hcast]
  ring_nf
  ring_nf at hcoeff
  linear_combination hcoeff

section Ambient

variable {E L : Type*} [Field E] [Field L] [Algebra E L]

/-- **The denominator slice for an element of a simple transcendental adjunction.**  A coprime
representation whose denominator has positive degree yields an affine relation in the coefficient
field with eigenvalue the coordinate's multiplier and inhomogeneity a multiple of the shift's
constant term. -/
theorem exists_denominator_relation_of_affine_mem_adjoin (σ : L →+* L) (φ : E →+* E)
    (hcomp : ∀ x : E, σ (algebraMap E L x) = algebraMap E L (φ x))
    {t : L} (ht : Transcendental E t) {a b c α β : E} (ha : a ≠ 0) (hc : c ≠ 0)
    (hσt : σ t = algebraMap E L a * t + algebraMap E L b)
    {W : L} (hW0 : W ≠ 0) (hW : W ∈ IntermediateField.adjoin E ({t} : Set L))
    (hrel : σ W = algebraMap E L c * W + (algebraMap E L α * t + algebraMap E L β)) :
    ∃ A B : E[X], B.Monic ∧ IsCoprime A B ∧ A ≠ 0 ∧
      W = aeval t A / aeval t B ∧
      twistComp φ (C a * X + C b) A * B
        = twistComp φ (C a * X + C b) B * (C c * A + (C α * X + C β) * B) ∧
      (1 ≤ B.natDegree →
        φ (B.coeff (B.natDegree - 1)) + (B.natDegree : E) * b
          = a * B.coeff (B.natDegree - 1)) := by
  classical
  obtain ⟨A, B, hB, hcop, hAB⟩ := exists_coprime_monic_repr ht hW
  have hinj : Function.Injective (aeval t : E[X] →ₐ[E] L) :=
    transcendental_iff_injective.mp ht
  have hB0 : B ≠ 0 := hB.ne_zero
  have hBt : aeval t B ≠ 0 := fun h => hB0 (hinj (by simpa using h))
  have hA0 : A ≠ 0 := by
    intro h
    rw [h, map_zero] at hAB
    exact hW0 ((mul_eq_zero.mp hAB).resolve_right hBt)
  have hWeq : W = aeval t A / aeval t B := by
    field_simp
    exact hAB
  set T : E[X] := C a * X + C b with hT
  have hTval : aeval t T = σ t := by rw [hT, hσt]; simp
  have htwB : aeval t (twistComp φ T B) ≠ 0 := fun h =>
    (twistComp_ne_zero φ (natDegree_linear ha) hB0) (hinj (by simpa using h))
  have hcross : twistComp φ T A * B = twistComp φ T B * (C c * A + (C α * X + C β) * B) := by
    refine hinj ?_
    have hσA := aeval_twistComp_of_aeval_eq σ φ hcomp hTval A
    have hσB := aeval_twistComp_of_aeval_eq σ φ hcomp hTval B
    rw [hWeq, map_div₀, ← hσA, ← hσB] at hrel
    rw [map_mul, map_mul, map_add, map_mul, map_mul, map_add, map_mul, aeval_C, aeval_C,
      aeval_C, aeval_X]
    rw [div_eq_iff htwB] at hrel
    field_simp at hrel
    linear_combination hrel
  refine ⟨A, B, hB, hcop, hA0, hWeq, hcross, ?_⟩
  intro hBdeg
  exact denominator_subleading_relation φ ha hc hB hcop hBdeg hcross

end Ambient

end GaloisForLFunctions.HTGeometry
