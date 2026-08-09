import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGammaScaling

/-!
# Finite sections at moving coordinates

The centred primary factor vanishes to order `g+1` at the origin, and on any disc of radius at least
one it is bounded; combining the two gives `‖E_g(z) - 1‖ ≤ C_R ‖z‖^{g+1}` on that disc, with no
restriction to the unit disc.

That bound dominates the centred factors of every finite nome section uniformly, so dominated
convergence for infinite products lets the coordinate move: the finite sections evaluated at a
convergent sequence of coordinates converge to the infinite-order product at the limit coordinate.
This completes the two-coordinate scaling table.
-/

namespace HTGeometry

open Filter Topology Metric
open scoped BigOperators

/-- **Radius-general estimate for a centred primary factor.**  On the unit disc the vanishing order
gives the bound; outside it the factor is bounded by compactness while `‖z‖^{g+1}` is at least
one. -/
theorem exists_primaryFactor_sub_one_bound (g : ℕ) (R : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℂ, ‖z‖ ≤ R → ‖primaryFactor g z - 1‖ ≤ C * ‖z‖ ^ (g + 1) := by
  have hcont : Continuous (fun z : ℂ => primaryFactor g z - 1) := by
    simp only [primaryFactor, primaryExponent]
    fun_prop
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ℂ) R).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max (Real.exp g) (max M 0), le_trans (Real.exp_nonneg _) (le_max_left _ _), ?_⟩
  intro z hz
  have hCnn : (0 : ℝ) ≤ max (Real.exp g) (max M 0) :=
    le_trans (Real.exp_nonneg _) (le_max_left _ _)
  by_cases h1 : ‖z‖ ≤ 1
  · calc ‖primaryFactor g z - 1‖ ≤ Real.exp g * ‖z‖ ^ (g + 1) :=
        primaryFactor_sub_one_norm_le g h1
      _ ≤ max (Real.exp g) (max M 0) * ‖z‖ ^ (g + 1) := by
          have hle : Real.exp g ≤ max (Real.exp g) (max M 0) := le_max_left _ _
          have hpow : (0 : ℝ) ≤ ‖z‖ ^ (g + 1) := by positivity
          exact mul_le_mul_of_nonneg_right hle hpow
  · have hgt : (1 : ℝ) < ‖z‖ := not_le.mp h1
    have hmem : z ∈ closedBall (0 : ℂ) R := by
      rw [mem_closedBall_zero_iff]
      exact hz
    have hMz : ‖primaryFactor g z - 1‖ ≤ M := hM z hmem
    have hpow : (1 : ℝ) ≤ ‖z‖ ^ (g + 1) := one_le_pow₀ (le_of_lt hgt)
    calc ‖primaryFactor g z - 1‖ ≤ M := hMz
      _ ≤ max (Real.exp g) (max M 0) := le_trans (le_max_left M 0) (le_max_right _ _)
      _ ≤ max (Real.exp g) (max M 0) * ‖z‖ ^ (g + 1) :=
          le_mul_of_one_le_right hCnn hpow

/-- **Finite sections at moving coordinates.**  The section evaluated along any convergent family of
coordinates converges to the infinite-order product at the limit coordinate. -/
theorem tendsto_finiteNomeSection_moving {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1)))
    {xS : Finset ι → ℂ} {x : ℂ} (hx : Tendsto xS atTop (𝓝 x)) :
    Tendsto (fun S : Finset ι => finiteNomeSection g p S (xS S)) atTop
      (𝓝 (infiniteMultipleEllipticGamma g p x)) := by
  classical
  set R : ℝ := ‖x‖ + 1 with hRdef
  have hR1 : (1 : ℝ) ≤ R := by
    rw [hRdef]
    linarith [norm_nonneg x]
  obtain ⟨C, hC0, hCbound⟩ := exists_primaryFactor_sub_one_bound g R
  have hq_le : ∀ ν : ι →₀ ℕ, ‖nomeMonomial p ν‖ ≤ 1 := norm_nomeMonomial_le_one p hp_lt
  have hq_sum : Summable (fun ν : ι →₀ ℕ => ‖nomeMonomial p ν‖ ^ (g + 1)) :=
    (summable_nomeMonomial_pow_iff g p hp_lt).2 hsum
  set bound : (ι →₀ ℕ) → ℝ :=
    fun ν => C * R ^ (g + 1) * ‖nomeMonomial p ν‖ ^ (g + 1) with hbdef
  have hbsum : Summable bound := hq_sum.mul_left _
  set f : Finset ι → (ι →₀ ℕ) → ℂ := fun S ν =>
    (if ν.support ⊆ S then primaryFactor g (xS S * nomeMonomial p ν) else 1) - 1 with hfdef
  set d : (ι →₀ ℕ) → ℂ := fun ν => primaryFactor g (x * nomeMonomial p ν) - 1 with hddef
  have hab : ∀ ν, Tendsto (fun S => f S ν) atTop (𝓝 (d ν)) := by
    intro ν
    have hcont : Continuous (fun z : ℂ => primaryFactor g (z * nomeMonomial p ν) - 1) := by
      simp only [primaryFactor, primaryExponent]
      fun_prop
    have h1 : Tendsto
        (fun S : Finset ι => primaryFactor g (xS S * nomeMonomial p ν) - 1) atTop (𝓝 (d ν)) :=
      (hcont.tendsto x).comp hx
    refine h1.congr' ?_
    filter_upwards [eventually_ge_atTop ν.support] with S hS
    simp only [hfdef, hS, if_true]
  have hbound : ∀ᶠ S in atTop, ∀ ν, ‖f S ν‖ ≤ bound ν := by
    have hxR : ∀ᶠ S : Finset ι in atTop, ‖xS S‖ ≤ R := by
      have hnorm := hx.norm
      exact hnorm.eventually (eventually_le_nhds (by rw [hRdef]; linarith : ‖x‖ < R))
    filter_upwards [hxR] with S hS ν
    by_cases hν : ν.support ⊆ S
    · have hqn : (0 : ℝ) ≤ ‖nomeMonomial p ν‖ := norm_nonneg _
      have hz : ‖xS S * nomeMonomial p ν‖ ≤ R := by
        rw [norm_mul]
        nlinarith [norm_nonneg (xS S), hq_le ν, hS, hR1]
      have hzle : ‖xS S * nomeMonomial p ν‖ ≤ R * ‖nomeMonomial p ν‖ := by
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_right hS hqn
      simp only [hfdef, hν, if_true]
      calc ‖primaryFactor g (xS S * nomeMonomial p ν) - 1‖
          ≤ C * ‖xS S * nomeMonomial p ν‖ ^ (g + 1) := hCbound _ hz
        _ ≤ C * (R * ‖nomeMonomial p ν‖) ^ (g + 1) := by
            refine mul_le_mul_of_nonneg_left ?_ hC0
            exact pow_le_pow_left₀ (norm_nonneg _) hzle _
        _ = bound ν := by
            rw [hbdef, mul_pow]
            ring
    · simp only [hfdef, hν, if_false, sub_self, norm_zero, hbdef]
      positivity
  have hlim := tendsto_tprod_one_add_of_dominated_convergence hbsum hab hbound
  have hleft : ∀ S : Finset ι, (∏' ν : ι →₀ ℕ, (1 + f S ν))
      = finiteNomeSection g p S (xS S) := by
    intro S
    rw [finiteNomeSection]
    refine tprod_congr fun ν => ?_
    rw [hfdef]
    ring
  have hright : (∏' ν : ι →₀ ℕ, (1 + d ν)) = infiniteMultipleEllipticGamma g p x := by
    rw [infiniteMultipleEllipticGamma, canonicalWeightProduct]
    refine tprod_congr fun ν => ?_
    rw [hddef]
    ring
  rw [hright] at hlim
  exact hlim.congr hleft

/-- **The scaling table.**  Whatever finite two-coordinate scaling is chosen, both halves converge:
the backward half to the product at the limit coordinate, the forward half to the product at the
forward limit — and by the boundary law one of the two arguments is zero. -/
theorem tendsto_scalingTable {ι : Type*} [Infinite ι] (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (hsum : Summable (fun a => ‖p a‖ ^ (g + 1)))
    {xS : Finset ι → ℂ} (hxS : ∀ S, xS S ≠ 0) {x y : ℂ}
    (hx : Tendsto xS atTop (𝓝 x))
    (hy : Tendsto (fun S => (∏ a ∈ S, p a) / xS S) atTop (𝓝 y)) :
    x * y = 0 ∧
      Tendsto (fun S : Finset ι => finiteNomeSection g p S (xS S)) atTop
        (𝓝 (infiniteMultipleEllipticGamma g p x)) ∧
      Tendsto (fun S : Finset ι => finiteNomeSection g p S ((∏ a ∈ S, p a) / xS S)) atTop
        (𝓝 (infiniteMultipleEllipticGamma g p y)) :=
  ⟨scalingBoundary_mul_eq_zero g p hp_lt hsum hxS hx hy,
    tendsto_finiteNomeSection_moving g p hp_lt hsum hx,
    tendsto_finiteNomeSection_moving g p hp_lt hsum hy⟩

end HTGeometry
