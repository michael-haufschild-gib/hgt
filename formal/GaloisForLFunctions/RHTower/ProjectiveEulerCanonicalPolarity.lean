import GaloisForLFunctions.RHTower.ProjectiveEulerAnalyticGauge
import GaloisForLFunctions.RHTower.PrimeShiftResidueClosability
import GaloisForLFunctions.RHTower.ZetaRealStrip

/-!
# Canonical opposite Euler sheet and zeta-divisor polarity

The positive Boolean sheet is Riemann zeta and its global complement is `ζ(2s) / ζ(s)`.  At every
zeta zero in the closed right critical half-strip, the doubled zeta factor is a local analytic unit.
Consequently the negative sheet has the opposite meromorphic order and therefore a pole of exactly
the positive sheet's zero multiplicity.
-/

noncomputable section

open Complex ArithmeticFunction LSeries Filter Topology
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

/-- Canonical negative Helson sheet, globally represented as a meromorphic quotient. -/
def canonicalNegativeEulerSheet (s : ℂ) : ℂ :=
  riemannZeta (2 * s) / riemannZeta s

/-- The canonical negative sheet agrees with the all-negative Helson Dirichlet series on its Euler
half-plane. -/
theorem canonicalNegativeEulerSheet_eq_LSeries_phaseChar_neg_one :
    ∀ s : ℂ, 1 < s.re →
      canonicalNegativeEulerSheet s =
        LSeries (fun n => phaseChar (fun _ => (-1 : ℂ)) n) s := by
  intro s hs
  exact (LSeries_phaseChar_neg_one_eq_riemannZeta_two_mul_div hs).symm

/-- **Canonical divisor-polarity law.**  At every zeta zero with `Re ρ ≥ 1/2`, the negative
Euler sheet has exactly the negative of zeta's local order, including full multiplicity. -/
theorem canonicalNegativeEulerSheet_divisor_polarity :
    ∀ ρ : ℂ, 1 / 2 ≤ ρ.re → riemannZeta ρ = 0 →
      (meromorphicOrderAt canonicalNegativeEulerSheet ρ).untop₀ =
        -(meromorphicOrderAt riemannZeta ρ).untop₀ := by
  intro ρ hhalf hzero
  have hρ1 : ρ ≠ 1 := by
    intro h
    subst ρ
    exact riemannZeta_ne_zero_of_one_le_re (by simp) hzero
  have h2ρ1 : 2 * ρ ≠ 1 := by
    intro h
    have hρ : ρ = (1 / 2 : ℂ) := by
      calc
        ρ = (2 : ℂ)⁻¹ * (2 * ρ) := by ring
        _ = (2 : ℂ)⁻¹ * 1 := by rw [h]
        _ = 1 / 2 := by norm_num
    rw [hρ] at hzero
    exact _root_.RHTower.riemannZeta_real_strip_ne_zero (σ := 1 / 2)
      (by norm_num) (by norm_num) (by simpa using hzero)
  have hnum : AnalyticAt ℂ (fun z : ℂ => riemannZeta (2 * z)) ρ :=
    (_root_.RHTower.analyticAt_riemannZeta h2ρ1).comp (by fun_prop)
  have hden : AnalyticAt ℂ riemannZeta ρ :=
    _root_.RHTower.analyticAt_riemannZeta hρ1
  have hz2 : riemannZeta (2 * ρ) ≠ 0 := by
    apply riemannZeta_ne_zero_of_one_le_re
    rw [Complex.mul_re]
    norm_num
    linarith
  change (meromorphicOrderAt
    (fun z : ℂ => riemannZeta (2 * z) / riemannZeta z) ρ).untop₀ = _
  rw [fun_meromorphicOrderAt_div hnum.meromorphicAt hden.meromorphicAt,
    hnum.meromorphicOrderAt_eq,
    hnum.analyticOrderAt_eq_zero.mpr hz2]
  simp

/-- Every zeta zero in the closed right critical half-strip is a genuine pole of the canonical
negative sheet.  Together with `canonicalNegativeEulerSheet_divisor_polarity`, this records exact
multiplicity rather than merely nonremovability. -/
theorem canonicalNegativeEulerSheet_has_pole_at_right_half_zeta_zero :
    ∀ ρ : ℂ, 1 / 2 ≤ ρ.re → riemannZeta ρ = 0 →
      (meromorphicOrderAt canonicalNegativeEulerSheet ρ).untop₀ < 0 := by
  intro ρ hhalf hzero
  rw [canonicalNegativeEulerSheet_divisor_polarity ρ hhalf hzero]
  have hρ1 : ρ ≠ 1 := by
    intro h
    subst ρ
    exact riemannZeta_ne_zero_of_one_le_re (by simp) hzero
  have hana : AnalyticAt ℂ riemannZeta ρ :=
    _root_.RHTower.analyticAt_riemannZeta hρ1
  have htend : Tendsto riemannZeta (nhdsWithin ρ {ρ}ᶜ) (nhds 0) := by
    have hc : ContinuousWithinAt riemannZeta {ρ}ᶜ ρ :=
      hana.continuousAt.continuousWithinAt
    rw [ContinuousWithinAt, hzero] at hc
    exact hc
  have hpos : 0 < meromorphicOrderAt riemannZeta ρ :=
    (tendsto_zero_iff_meromorphicOrderAt_pos hana.meromorphicAt).mp htend
  have han_ne_top : analyticOrderAt riemannZeta ρ ≠ ⊤ :=
    _root_.RHTower.analyticOrderAt_riemannZeta_ne_top hρ1
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp han_ne_top
  have hmero_ne_top : meromorphicOrderAt riemannZeta ρ ≠ ⊤ := by
    apply WithTop.ne_top_iff_exists.mpr
    refine ⟨(n : ℤ), ?_⟩
    rw [hana.meromorphicOrderAt_eq, ← hn, ENat.map_coe]
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hmero_ne_top
  have hmpos : 0 < m := by
    rw [← hm] at hpos
    exact_mod_cast hpos
  rw [← hm, WithTop.untop₀_coe]
  omega

end GaloisForLFunctions.RHTower
