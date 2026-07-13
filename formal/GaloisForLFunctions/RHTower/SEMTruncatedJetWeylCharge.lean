import GaloisForLFunctions.RHTower.TruncatedJetWeylBoundary
import GaloisForLFunctions.RHTower.CompletedSEMContourBoundary

/-!
# Completed SEM contour charge equals the truncated-Weyl boundary anomaly

The completed symmetric Euler--Maclaurin contour carries a source-defined integral Fitting charge.
At modulus `2^k`, that charge is the hole count modulo `2^k`.  Independently, the truncated local
clock--shift model has one boundary anomaly, `h * (1 - zeta_k^d)`, where `d` is the same hole count.

This module proves that the two obstructions are identical:

`contour charge = 0  <->  zeta_k^d = 1  <->  top-jet Weyl anomaly = 0`

for every nonzero boundary holonomy `h`.  Thus the Fitting/contour and crossed-product/Weyl routes
do not have separate open cores.  Both ask for source annihilation of one dyadic boundary class.

The equivalence is a bridge assembled from already formalized source-count and primitive-root
theorems; no claim of new scientific knowledge is made.
-/

open Complex Matrix

noncomputable section

namespace RHTower

/-- Vanishing of the depth-`k` completed-SEM contour charge is exactly closure of the dyadic phase
around the actual finite hole count. -/
theorem completedSEMContourCharge_zero_iff_dyadicPhase_pow_holeCount
    {ρ : ℂ} {r₀ R : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (h : SEMSplitData ρ r₀ R N zs u) (k : ℕ) :
    integralJetCharge 1 (2 ^ k) (by omega)
        (completedSEMContourBoundaryZ ρ r₀ R N 1) = 0 ↔
      Bottcher.dyadicRoot k ^ zs.length = 1 := by
  rw [integralJetCharge_completedSEMContourBoundaryZ h,
    ZMod.natCast_eq_zero_iff]
  exact ((dyadicWeylPhase_isPrimitiveRoot k).pow_eq_one_iff_dvd zs.length).symm

/-- For every nonzero proposed wrap, the completed-SEM contour charge vanishes exactly when the
scalar top-jet Weyl anomaly vanishes. -/
theorem completedSEMContourCharge_zero_iff_dyadicTopJetAnomaly_zero
    {ρ : ℂ} {r₀ R : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (h : SEMSplitData ρ r₀ R N zs u) (k : ℕ) (holonomy : ℂ)
    (hholonomy : holonomy ≠ 0) :
    integralJetCharge 1 (2 ^ k) (by omega)
        (completedSEMContourBoundaryZ ρ r₀ R N 1) = 0 ↔
      holonomy * (1 - Bottcher.dyadicRoot k ^ zs.length) = 0 := by
  rw [completedSEMContourCharge_zero_iff_dyadicPhase_pow_holeCount h k]
  constructor
  · intro hphase
    rw [hphase]
    ring
  · intro hanomaly
    have hfactor : 1 - Bottcher.dyadicRoot k ^ zs.length = 0 :=
      (mul_eq_zero.mp hanomaly).resolve_left hholonomy
    exact (sub_eq_zero.mp hfactor).symm

/-- Matrix form: once the actual hole count is written as `n+1`, vanishing of the source contour
charge is exactly vanishing of the unique wrap entry of the boundary-completed Weyl defect. -/
theorem completedSEMContourCharge_zero_iff_boundaryCompletedJetWeylDefect_zero
    {ρ : ℂ} {r₀ R : ℝ} {N n : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (h : SEMSplitData ρ r₀ R N zs u) (hlen : zs.length = n + 1)
    (k : ℕ) (holonomy : ℂ) (hholonomy : holonomy ≠ 0) :
    integralJetCharge 1 (2 ^ k) (by omega)
        (completedSEMContourBoundaryZ ρ r₀ R N 1) = 0 ↔
      (truncatedJetClock n (Bottcher.dyadicRoot k) *
          boundaryCompletedJetShift n holonomy -
        Bottcher.dyadicRoot k •
          (boundaryCompletedJetShift n holonomy *
            truncatedJetClock n (Bottcher.dyadicRoot k))) 0 (Fin.last n) = 0 := by
  rw [boundaryCompletedJetWeylDefect_zero_last]
  rw [← hlen]
  exact completedSEMContourCharge_zero_iff_dyadicTopJetAnomaly_zero
    h k holonomy hholonomy

/-- **Exact RH capstone in semilinear holonomy coordinates.** RH is equivalent to closure of every
dyadic phase around every actual completed-SEM finite hole space.  This closes the target end of the
crossed-product detour without claiming that the source has yet forced the closure. -/
theorem riemannHypothesis_iff_all_dyadicSEMPhaseHolonomies_close :
    RiemannHypothesis ↔
      ∀ k : ℕ, ∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∀ (r₀ R : ℝ) (N : ℕ) (zs : List ℂ) (u : ℂ → ℂ),
          SEMSplitData ρ r₀ R N zs u →
          Bottcher.dyadicRoot k ^ zs.length = 1 := by
  constructor
  · intro hRH k ρ hρ hzero r₀ R N zs u hsplit
    have hcharge :=
      (riemannHypothesis_iff_all_completedSEMContourCharges_zero.mp hRH)
        k ρ hρ hzero r₀ R N ⟨zs, u, hsplit⟩
    exact (completedSEMContourCharge_zero_iff_dyadicPhase_pow_holeCount hsplit k).mp hcharge
  · intro hphase
    apply riemannHypothesis_iff_all_completedSEMContourCharges_zero.mpr
    intro k ρ hρ hzero r₀ R N hex
    obtain ⟨zs, u, hsplit⟩ := hex
    exact (completedSEMContourCharge_zero_iff_dyadicPhase_pow_holeCount hsplit k).mpr
      (hphase k ρ hρ hzero r₀ R N zs u hsplit)

end RHTower
