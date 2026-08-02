import GaloisForLFunctions.HTGeometry.SourceGaugeCovariantCofaceLaw
import GaloisForLFunctions.RHTower.BVCoPoissonHellingerBetaResonanceTransmutation

/-!
# The source-forced Hellinger--Beta covariant coface

The Hellinger--Beta shift ratio determines a unique rank-one covariant coface.  Applied to the
actual critical co-Poisson product, this coface removes the horizontal Beta gauge and exposes the
adjacent critical-eta current exactly.  This constructs the algebraic off-diagonal coface; no
claim is made here about its closed graph or Xi-fibre landing.
-/

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Pointwise Hellinger--Beta covariant coface. -/
def hellingerBetaCovariantCoface (G : ℂ → ℂ) (s : ℂ) : ℂ :=
  G (s + 1) - (s + 1 / 2) / (s + 2) * G s

/-- The Hellinger--Beta column is horizontal for the source-forced coface. -/
theorem hellingerBetaCovariantCoface_horizontal
    {s : ℂ} (hshalf : s + 1 / 2 ≠ 0) (hstwo : s + 2 ≠ 0) :
    hellingerBetaCovariantCoface hellingerHodgeBetaColumnComplex s = 0 := by
  rw [hellingerBetaCovariantCoface,
    hellingerHodgeBetaColumnComplex_add_one hshalf hstwo, sub_self]

/-- Universal product transgression for the Hellinger--Beta source gauge. -/
theorem hellingerBetaCovariantCoface_mul
    (F : ℂ → ℂ) {s : ℂ} (hshalf : s + 1 / 2 ≠ 0) (hstwo : s + 2 ≠ 0) :
    hellingerBetaCovariantCoface
        (fun z => F z * hellingerHodgeBetaColumnComplex z) s =
      hellingerHodgeBetaColumnComplex (s + 1) * (F (s + 1) - F s) := by
  rw [hellingerBetaCovariantCoface,
    hellingerHodgeBetaColumnComplex_add_one hshalf hstwo]
  ring

/-- **Critical-eta off-diagonal coface.**  On the actual co-Poisson/Hellinger product, the unique
covariant coface is the shifted Beta gauge times the adjacent arithmetic current. -/
theorem hellingerBetaCovariantCoface_criticalEta
    {s : ℂ} (hshalf : s + 1 / 2 ≠ 0) (hstwo : s + 2 ≠ 0) :
    hellingerBetaCovariantCoface hellingerBetaCoPoissonMellin s =
      hellingerHodgeBetaColumnComplex (s + 1) *
        (criticalEtaMellin (s + 1) - criticalEtaMellin s) := by
  change hellingerBetaCovariantCoface
      (fun z => criticalEtaMellin z * hellingerHodgeBetaColumnComplex z) s = _
  exact hellingerBetaCovariantCoface_mul criticalEtaMellin hshalf hstwo

/-- On the physical real source domain the Hellinger--Beta gauge never vanishes. -/
theorem hellingerHodgeBetaColumnComplex_real_ne_zero
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) :
    hellingerHodgeBetaColumnComplex (a : ℂ) ≠ 0 := by
  unfold hellingerHodgeBetaColumnComplex
  apply neg_ne_zero.mpr
  apply div_ne_zero
  · apply mul_ne_zero
    · apply Complex.Gamma_ne_zero_of_re_pos
      norm_num
      linarith
    · apply Complex.Gamma_ne_zero_of_re_pos
      norm_num
  · apply Complex.Gamma_ne_zero_of_re_pos
    norm_num
    linarith

/-- Fisher/Gamma normalization of the forced coface is exactly the unweighted adjacent
critical-eta current. -/
theorem hellingerBetaCovariantCoface_criticalEta_normalized
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) :
    hellingerBetaCovariantCoface hellingerBetaCoPoissonMellin (a : ℂ) /
        hellingerHodgeBetaColumnComplex ((a + 1 : ℝ) : ℂ) =
      criticalEtaMellin ((a + 1 : ℝ) : ℂ) - criticalEtaMellin (a : ℂ) := by
  have hshalf : (a : ℂ) + 1 / 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  have hstwo : (a : ℂ) + 2 ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    norm_num at hre
    linarith
  push_cast
  change hellingerBetaCovariantCoface hellingerBetaCoPoissonMellin (a : ℂ) /
      hellingerHodgeBetaColumnComplex ((a : ℂ) + 1) =
    criticalEtaMellin ((a : ℂ) + 1) - criticalEtaMellin (a : ℂ)
  rw [hellingerBetaCovariantCoface_criticalEta hshalf hstwo]
  have hshift : hellingerHodgeBetaColumnComplex ((a + 1 : ℝ) : ℂ) ≠ 0 :=
    hellingerHodgeBetaColumnComplex_real_ne_zero (by linarith)
  have hshift' : hellingerHodgeBetaColumnComplex ((a : ℂ) + 1) ≠ 0 := by
    have hcast : (((a + 1 : ℝ) : ℂ)) = (a : ℂ) + 1 := by
      push_cast
      rfl
    rw [← hcast]
    exact hshift
  exact mul_div_cancel_left₀
    (criticalEtaMellin ((a : ℂ) + 1) - criticalEtaMellin (a : ℂ)) hshift'

/-- The rational Beta ratio is the unique first-order coefficient which keeps the physical real
Hellinger source horizontal. -/
theorem hellingerBetaCovariantCoface_coefficient_unique
    {a : ℝ} (ha : -(1 / 2 : ℝ) < a) (q : ℂ)
    (hq : hellingerHodgeBetaColumnComplex ((a + 1 : ℝ) : ℂ) -
      q * hellingerHodgeBetaColumnComplex (a : ℂ) = 0) :
    q = (((a + 1 / 2) / (a + 2) : ℝ) : ℂ) := by
  have hrec := hellingerHodgeBetaColumnComplex_real_add_one ha
  have hnonzero := hellingerHodgeBetaColumnComplex_real_ne_zero ha
  have hmul : q * hellingerHodgeBetaColumnComplex (a : ℂ) =
      (((a + 1 / 2) / (a + 2) : ℝ) : ℂ) *
        hellingerHodgeBetaColumnComplex (a : ℂ) := by
    rw [← hrec]
    exact (sub_eq_zero.mp hq).symm
  exact mul_right_cancel₀ hnonzero hmul

end

end RHTower
