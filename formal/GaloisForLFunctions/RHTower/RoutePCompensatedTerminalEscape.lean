import GaloisForLFunctions.RHTower.RoutePCompensatedMassRiccati
import GaloisForLFunctions.RHTower.RoutePOneSidedChebyshevOscillation

/-!
# Unbounded ratio-one terminal excursions in Route P

For every real cap B and integer threshold M, a later head K satisfies
`sqrt(K+2)+ccmActualHeadMatchedQuantileParabolicCenteredShift K > B`.
The theorem is unconditional and retains the complete compensation square and centroid excess.

An assumed tail cap yields a quadratic upper barrier for the actual Abel primitive.
The continuous comparison pays the bounded gap between consecutive integer heads;
the Riccati and one-sided Landau results force RH internally. Under that consequence,
the exact mass-discrepancy bound and unconditional negative Chebyshev excursions
contradict the cap. Thus no fixed additive terminal correction can provide tail passivity.

This closes the ratio-one compensation obstruction; the signed normalized-variance
history floor still requires a law for the complete ordered history.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators
open GaloisForLFunctions.RHTower

namespace RHTower
noncomputable section

theorem routeP_parabolicMass_eq_primeMassHalf (K : ℕ) :
    ccmActualHeadParabolicMass K = primeMassHalf ((K + 2 : ℕ) : ℝ) := by
  rw [ccmActualHeadParabolicMass, ← centroid_sum_range_shift_two criticalMellinAtomWeight
    (by simp [criticalMellinAtomWeight]) (by simp [criticalMellinAtomWeight]),
    primeMassHalf, Nat.floor_natCast]
  apply Finset.sum_congr
  · ext n
    simp only [Finset.mem_range, Finset.mem_Icc]
    omega
  · intro n _
    by_cases hn : n = 0
    · simp [hn, criticalMellinAtomWeight]
    · have hnpos : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      rw [criticalMellinAtomWeight, show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
        Real.rpow_neg hnpos.le, ← Real.sqrt_eq_rpow, div_eq_mul_inv]
      ring

/-- The finite-head quadratic bound controls the actual continuous Abel primitive.
The gap between consecutive integer heads costs a fixed constant, not an assumed estimate. -/
theorem riemannHypothesis_of_routeP_terminal_eventually_upper {B : ℝ} {N : ℕ}
    (hB : ∀ K : ℕ, N ≤ K →
      Real.sqrt ((K + 2 : ℕ) : ℝ) + ccmActualHeadMatchedQuantileParabolicCenteredShift K ≤ B) :
    RiemannHypothesis := by
  let E : ℝ := ∑' n : ℕ, centroidAtomExcess n
  let b : ℝ := 1 + |B|
  have hb : 0 < b := by dsimp [b]; positivity
  refine riemannHypothesis_of_primeMass_quadraticAbelBound
    (C := E / 2 + 21) (X := (N : ℝ) + 3) hb ?_
  intro x hx
  let n : ℕ := ⌊x⌋₊
  let K : ℕ := n - 2
  have hx0 : 0 ≤ x := by linarith [show (0 : ℝ) ≤ (N : ℝ) from Nat.cast_nonneg N]
  have hn : N + 3 ≤ n := by
    apply (Nat.le_floor_iff hx0).mpr
    exact_mod_cast hx
  have hK : N ≤ K := by dsimp [K]; omega
  have hKn : K + 2 = n := by dsimp [K]; omega
  have hn1 : 1 ≤ (n : ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hxn : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have hm : primeMassHalf x = ccmActualHeadParabolicMass K := by
    rw [routeP_parabolicMass_eq_primeMassHalf, hKn]
    simp only [primeMassHalf, Nat.floor_natCast]
    rfl
  have hmn : primeMassHalf (n : ℝ) = primeMassHalf x := by
    simp only [primeMassHalf, Nat.floor_natCast]
    rfl
  have hp : Chebyshev.psi x = Chebyshev.psi (n : ℝ) := by
    simp only [Chebyshev.psi_eq_sum_Icc, Nat.floor_natCast]
    rfl
  let m : ℝ := primeMassHalf x
  let r : ℝ := Real.sqrt x
  let s : ℝ := Real.sqrt (n : ℝ)
  have hs : 0 ≤ s := Real.sqrt_nonneg _
  have hrs : s ≤ r := Real.sqrt_le_sqrt hnx
  have hr2 : r ^ 2 = x := Real.sq_sqrt hx0
  have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt (zero_le_one.trans hn1)
  have hm21 : m ≤ 21 * s := by
    dsimp only [m, s]
    rw [← hmn]
    exact primeMassHalf_le_sqrt hn1
  have hgap : m * (r - s) ≤ 21 := by
    have hprod := mul_le_mul_of_nonneg_right hm21 (sub_nonneg.mpr hrs)
    have hsGap : s * (r - s) ≤ 1 := by nlinarith [sq_nonneg (r - s)]
    nlinarith
  have hFgap : routePAbelMassPrimitive x ≤ routePAbelMassPrimitive (n : ℝ) + 21 := by
    rw [routePAbelMassPrimitive_eq (by linarith), routePAbelMassPrimitive_eq hn1, hp, hmn]
    change r * m - Chebyshev.psi (n : ℝ) ≤ s * m - Chebyshev.psi (n : ℝ) + 21
    nlinarith
  have hcoef := hB K hK
  have hident := ccmActualHeadMatchedQuantileParabolicUnitScaleCompensatedChebyshevIdentity K
  dsimp only at hident
  rw [hKn] at hident hcoef
  rw [← hm] at hident
  have hmass0 : 0 ≤ m := routeP_primeMass_nonneg x
  have hsource : 4 * m * (-B) ≤
      (m - 2 * s) ^ 2 + 2 * ccmActualHeadMatchedCentroidChebyshevExcess K +
      4 * chebyshevError (n : ℝ) + 4 * m := by
    change 4 * m * (-ccmActualHeadMatchedQuantileParabolicCenteredShift K - s) = _ at hident
    change s + ccmActualHeadMatchedQuantileParabolicCenteredShift K ≤ B at hcoef
    nlinarith
  have he : ccmActualHeadMatchedCentroidChebyshevExcess K ≤ E :=
    ccmActualHeadMatchedCentroidChebyshevExcess_le_tsum K
  have hFn := routePAbelMassPrimitive_eq hn1
  rw [hmn] at hFn
  change routePAbelMassPrimitive (n : ℝ) = s * m - Chebyshev.psi (n : ℝ) at hFn
  unfold chebyshevError at hsource
  have hBabs : B ≤ |B| := le_abs_self B
  have hBmass := mul_le_mul_of_nonneg_right hBabs hmass0
  change routePAbelMassPrimitive x - (E / 2 + 21) ≤ (m + 2 * b) ^ 2 / 4
  dsimp [b]
  nlinarith [sq_nonneg (1 + |B|)]

/-- Under the internally obtainable RH, the compensation cannot cap the terminal
coefficient at any fixed height: negative Chebyshev excursions defeat every such cap. -/
theorem routeP_terminal_positive_escape_of_RH (hRH : RiemannHypothesis) (B : ℝ) (M : ℕ) :
    ∃ K : ℕ, M ≤ K ∧ B <
      Real.sqrt ((K + 2 : ℕ) : ℝ) + ccmActualHeadMatchedQuantileParabolicCenteredShift K := by
  obtain ⟨D, hD, hmass⟩ := routeP_mass_discrepancy_eighth_power_of_RH hRH
  let F : ℝ := ∑' n : ℕ, centroidAtomExcess n
  have hF : 0 ≤ F := (ccmActualHeadMatchedCentroidChebyshevExcess_nonneg 0).trans
    (ccmActualHeadMatchedCentroidChebyshevExcess_le_tsum 0)
  let Q : ℝ := D ^ 2 + 2 * F + 4 * (1 + |B|) * (2 + D)
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  obtain ⟨n, hn, hn3, hneg⟩ := ccmFuPsiRemainder_negative_escape (Q + 1) (M + 2)
  let K : ℕ := n - 2
  have hK : M ≤ K := by dsimp [K]; omega
  have hKn : K + 2 = n := by dsimp [K]; omega
  let x : ℝ := (n : ℝ)
  let r : ℝ := Real.sqrt x
  let t : ℝ := x ^ (1 / 8 : ℝ)
  let m : ℝ := ccmActualHeadParabolicMass K
  let e : ℝ := ccmActualHeadMatchedCentroidChebyshevExcess K
  let u : ℝ := m - 2 * r
  have hx1 : 1 ≤ x := by dsimp [x]; exact_mod_cast (show 1 ≤ n by omega)
  have hx0 : 0 ≤ x := zero_le_one.trans hx1
  have hr1 : 1 ≤ r := Real.one_le_sqrt.mpr hx1
  have ht1 : 1 ≤ t := by
    dsimp [t]
    simpa using Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num : (0 : ℝ) ≤ 1 / 8)
  have ht4 : t ^ (4 : ℕ) = r := by
    dsimp [t, r]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx0]
    congr 1
    ring
  have ht2r : t ^ 2 ≤ r := by
    rw [← ht4]
    have ht2 : 1 ≤ t ^ 2 := one_le_pow₀ ht1
    nlinarith
  have htr : t ≤ r := by nlinarith
  have hu : |u| ≤ D * t := by
    have h := hmass K
    rw [hKn] at h
    exact h
  have hu2 : u ^ 2 ≤ D ^ 2 * r := by
    have hs := (sq_le_sq₀ (abs_nonneg u) (mul_nonneg hD (by linarith))).mpr hu
    rw [sq_abs, mul_pow] at hs
    exact hs.trans (mul_le_mul_of_nonneg_left ht2r (sq_nonneg D))
  have hm : m ≤ (2 + D) * r := by
    have hmul := mul_le_mul_of_nonneg_left htr hD
    have hup := (abs_le.mp hu).2
    dsimp [u] at hup
    nlinarith
  have hm0 : 0 < m := ccmActualHeadParabolicMass_pos K
  have he : e ≤ F * r := by
    have heF : e ≤ F := ccmActualHeadMatchedCentroidChebyshevExcess_le_tsum K
    exact heF.trans (by nlinarith)
  have hlin : 4 * m + 4 * m * B ≤ 4 * (1 + |B|) * (2 + D) * r := by
    have hBm := mul_le_mul_of_nonneg_right (le_abs_self B) hm0.le
    have hMm := mul_le_mul_of_nonneg_left hm (show 0 ≤ 4 * (1 + |B|) by positivity)
    nlinarith
  have hcomp : u ^ 2 + 2 * e + 4 * m + 4 * m * B ≤ Q * r := by
    dsimp [Q]
    nlinarith only [hu2, he, hlin]
  have hE : chebyshevError x < -(Q + 1) * r := by
    simpa only [psiRemainder, chebyshevPsi_eq_psi, chebyshevError, x, r] using hneg
  have hid := ccmActualHeadMatchedQuantileParabolicUnitScaleCompensatedChebyshevIdentity K
  dsimp only at hid
  rw [hKn] at hid
  change 4 * m * (-ccmActualHeadMatchedQuantileParabolicCenteredShift K - r) =
    u ^ 2 + 2 * e + 4 * chebyshevError x + 4 * m at hid
  refine ⟨K, hK, ?_⟩
  rw [hKn]
  change B < r + ccmActualHeadMatchedQuantileParabolicCenteredShift K
  have hQr : 0 ≤ Q * r := mul_nonneg hQ (by linarith)
  nlinarith only [hcomp, hE, hid, hm0, hr1, hQr]

/-- **Unconditional unbounded positive excursions of the ratio-one terminal coefficient.**
The full matched centroid, quantile shift and quadratic compensation are retained. -/
theorem routeP_terminal_positive_escape (B : ℝ) (M : ℕ) :
    ∃ K : ℕ, M ≤ K ∧ B <
      Real.sqrt ((K + 2 : ℕ) : ℝ) + ccmActualHeadMatchedQuantileParabolicCenteredShift K := by
  by_contra! h
  have hRH := riemannHypothesis_of_routeP_terminal_eventually_upper h
  obtain ⟨K, hK, hlt⟩ := routeP_terminal_positive_escape_of_RH hRH B M
  exact (not_lt_of_ge (h K hK)) hlt

end
end RHTower
