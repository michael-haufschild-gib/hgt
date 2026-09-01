import GaloisForLFunctions.HTGeometry.RittGeneralInhomogeneity
import GaloisForLFunctions.HTGeometry.RittSubleadingSlice

/-!
# The denominator slice for an arbitrary polynomial inhomogeneity

The denominator identity `Q^φ(aX + b) = a^{deg Q}·Q` is insensitive to the inhomogeneity, so its
subleading coefficient carries the same affine relation whatever the inhomogeneity is:

`φ(Q_{D−1}) + D·b = a·Q_{D−1}`,   `D = deg Q ≥ 1`.

That is the relation which forces the denominator of a solution to be trivial, and it is available
for a solution whose inhomogeneity is an arbitrary polynomial in the coordinate — the shape the jets
of an affine tower produce.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {K : Type*} [Field K]

/-- **The subleading coefficient of the denominator, for an arbitrary polynomial
inhomogeneity.** -/
theorem denominator_subleading_relation_gen (Φ : K →+* K) {a b c : K}
    (ha : a ≠ 0) (hc : c ≠ 0) {P Q G : K[X]} (hQ : Q.Monic) (hcop : IsCoprime P Q)
    (hQdeg : 1 ≤ Q.natDegree)
    (hcross : twistComp Φ (C a * X + C b) P * Q
      = twistComp Φ (C a * X + C b) Q * (C c * P + G * Q)) :
    Φ (Q.coeff (Q.natDegree - 1)) + (Q.natDegree : K) * b
      = a * Q.coeff (Q.natDegree - 1) := by
  classical
  have hden := twistComp_denominator_eq_gen Φ ha hc hQ hcop hcross
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

/-- **The denominator slice inside an adjunction, for an arbitrary polynomial inhomogeneity.** -/
theorem exists_denominator_relation_gen (σ : L →+* L) (φ : E →+* E)
    (hcomp : ∀ x : E, σ (algebraMap E L x) = algebraMap E L (φ x))
    {t : L} (ht : Transcendental E t) {a b c : E} (ha : a ≠ 0) (hc : c ≠ 0)
    (hσt : σ t = algebraMap E L a * t + algebraMap E L b)
    {W : L} (hW0 : W ≠ 0) (hW : W ∈ IntermediateField.adjoin E ({t} : Set L))
    {G : E[X]} (hrel : σ W = algebraMap E L c * W + aeval t G) :
    ∃ A B : E[X], B.Monic ∧ IsCoprime A B ∧ A ≠ 0 ∧ W = aeval t A / aeval t B ∧
      twistComp φ (C a * X + C b) A * B
        = twistComp φ (C a * X + C b) B * (C c * A + G * B) ∧
      (1 ≤ B.natDegree →
        φ (B.coeff (B.natDegree - 1)) + (B.natDegree : E) * b
          = a * B.coeff (B.natDegree - 1)) := by
  obtain ⟨A, B, hB, hcop, hA0, hWeq, hcross⟩ :=
    exists_coprime_cross_gen σ φ hcomp ht ha hc hσt hW0 hW hrel
  exact ⟨A, B, hB, hcop, hA0, hWeq, hcross,
    fun hBdeg => denominator_subleading_relation_gen φ ha hc hB hcop hBdeg hcross⟩

end Ambient

end GaloisForLFunctions.HTGeometry
