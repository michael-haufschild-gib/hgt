import GaloisForLFunctions.MetaplecticMobiusDescent.Eisenstein.AngularCuspPhase

/-!
# The ideal character of the angular cusp phase

The extra denominator phase of the order `6k+1` source is exactly `ψ₆^(2k)`.
Consequently it descends to principal ideals, is trivial on units, and separates
under ideal products with modulus at most one.
-/

open Complex
open scoped ComplexConjugate Classical MatrixGroups Matrix BigOperators
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein GaloisForLFunctions.FamilyContinuationTheory
open CubicJacobi CubicKubota CubicRamified RationalSource
noncomputable section

private lemma complexUnitConj_sq (z : ℂ) : complexUnitConj z ^ 2 = conj z / z := by
  by_cases hz : z = 0
  · simp only [hz, map_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), div_zero]
  have hn : z * conj z = (‖z‖ : ℂ) ^ 2 := by
    rw [RCLike.mul_conj]
    norm_cast
  have hc : conj z ≠ 0 := by simpa using hz
  rw [complexUnitConj_apply, div_pow, ← hn]
  field_simp [hz, hc]

/-- The denominator phase is the even power of the sextic ideal character. -/
theorem angularCuspDenominatorPhase_eq_psiSix (k : ℕ) (c : O) :
    angularCuspDenominatorPhase k c = elemPsiSix c ^ (2 * k) := by
  change (-conj (ringComplex c) / ringComplex c) ^ (6 * k) = _
  calc
    _ = ((conj (ringComplex c) / ringComplex c) ^ 6) ^ k := by
      rw [pow_mul]
      congr 1
      ring
    _ = ((complexUnitConj (ringComplex c) ^ 2) ^ 6) ^ k := by rw [complexUnitConj_sq]
    _ = elemPsiSix c ^ (2 * k) := by
      rw [elemPsiSix_apply]
      simp only [← pow_mul]
      congr 1
      omega

theorem angularCuspDenominatorPhase_eq_idealPsiSix (k : ℕ) (c : O) :
    angularCuspDenominatorPhase k c = idealPsiSix (Ideal.span {c}) ^ (2 * k) := by
  rw [idealPsiSix_span_singleton, angularCuspDenominatorPhase_eq_psiSix]

lemma angularCuspDenominatorPhase_unit (k : ℕ) (u : Oˣ) :
    angularCuspDenominatorPhase k (u : O) = 1 := by
  rw [angularCuspDenominatorPhase_eq_psiSix, elemPsiSix_unit, one_pow]

lemma angularCuspDenominatorPhase_norm_le_one (k : ℕ) (c : O) :
    ‖angularCuspDenominatorPhase k c‖ ≤ 1 := by
  rw [angularCuspDenominatorPhase_eq_psiSix, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (norm_elemPsiSix_le_one c)

lemma FixedCuspShape.datum_jetMultiplier_six_mul {H : SL(2, O)}
    (s : FixedCuspShape H) (g : rationalExtension)
    (h : ((g : SL(2, O)) * H) 1 0 ≠ 0) (k : ℕ) :
    (s.datum g h).jetMultiplier (6 * k) = (s.datum g h).multiplier *
      elemPsiSix (((g : SL(2, O)) * H) 1 0) ^ (2 * k) := by
  rw [SourceCuspDatum.jetMultiplier_six_mul, s.datum_angular_phase,
    angularCuspDenominatorPhase_eq_psiSix]

/-- All Fourier residues of a controlled cusp share the same extra ideal character. -/
lemma ControlledStratumArithmetic.datum_jetMultiplier_six_mul
    {ι : Type*} [Fintype ι] {p : ι → O} {N a0 c0 : O} {mode : Bool}
    (D : ControlledStratumArithmetic p N a0 c0 mode)
    (hN : (9 : O) * c0 ∣ N) (hr : lambda ^ 2 ∣ (∏ i, p i) - 1)
    (hbase : if mode then lambda ^ 2 ∣ a0 - 1 else lambda ^ 2 ∣ c0 - 1)
    (s : FixedCuspShape (fixedCusp a0 c0 mode)) (hp : ∀ i, p i ≠ 0)
    (hc0 : c0 ≠ 0) (v : ∀ i, (O ⧸ Ideal.span {p i})ˣ) (k : ℕ) :
    (D.datum hN hr hbase s hp hc0 v).jetMultiplier (6 * k) =
      (D.datum hN hr hbase s hp hc0 v).multiplier *
        idealPsiSix (Ideal.span {c0 * ∏ i, p i}) ^ (2 * k) := by
  rw [ControlledStratumArithmetic.datum, s.datum_jetMultiplier_six_mul,
    D.sourceGamma_mul, D.denominator, idealPsiSix_span_singleton]

end
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
