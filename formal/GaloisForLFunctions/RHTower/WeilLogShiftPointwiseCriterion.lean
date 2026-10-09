import GaloisForLFunctions.RHTower.WeilLogShiftNonnegativePotential

/-!
# From fixed probes to uniform expanding panels

With finite excess and convergent sampled potentials, approximate positivity
of each fixed integer-log probe forces a cutoff uniform over the expanding
panel. Nonnegative coefficients discharge all convergence premises. Failure
on that domain is witnessed by one fixed probe with a persistent negative margin.
-/

open Filter Topology Zeta23

noncomputable section

namespace RHTower

open WeilExcess

private theorem nonneg_limit_iff_eventually_approx {f : ℕ → ℝ} {d : ℝ}
    (ht : Tendsto f atTop (𝓝 d)) :
    0 ≤ d ↔ ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ k → -ε ≤ f k := by
  constructor
  · intro hd ε hε
    have hev := (tendsto_order.mp ht).1 (-ε) (by linarith only [hd, hε])
    obtain ⟨N, hN⟩ := eventually_atTop.mp hev
    exact ⟨N, fun k hk => (hN k hk).le⟩
  · intro h
    have hd : -d ≤ 0 := by
      apply le_of_forall_pos_le_add
      intro ε hε
      obtain ⟨N, hN⟩ := h ε hε
      have hev : ∀ᶠ k : ℕ in atTop, -f k ≤ ε := by
        refine eventually_atTop.mpr ⟨N, fun k hk => ?_⟩
        linarith only [hN k hk]
      simpa only [zero_add] using le_of_tendsto ht.neg hev
    linarith only [hd]

/-- Local convergence and finite excess permit the probe/cutoff quantifier
exchange: each fixed probe's approximate positivity controls the entire panel. -/
theorem weilLogShiftAsymptoticPositive_iff_pointwise_of_summable_potential
    {lam : ℕ → ℝ} (hexc : Summable (deviationExcess lam))
    (hp0 : Summable fun n => weilDeviation lam n *
      (riemannAutocorr (0 + Real.log n) + riemannAutocorr (0 - Real.log n)))
    (hpm : ∀ m : ℕ, 2 ≤ m → Summable fun n => weilDeviation lam n *
      (riemannAutocorr (Real.log m + Real.log n) +
        riemannAutocorr (Real.log m - Real.log n))) :
    WeilLogShiftAsymptoticPositive lam ↔
      ∀ m : ℕ, 2 ≤ m → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        -ε ≤ (weilFullFunctional lam (EF.weilTest
          (logShiftRiemannDifference k (Real.log m))
          (logShiftRiemannDifference k (Real.log m)))).re := by
  constructor
  · intro hpos m hm
    have ht := (tendsto_logShift_probe_of_summable_potential m hp0 (hpm m hm)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    apply (nonneg_limit_iff_eventually_approx ht).mp
    have hgap := logShiftAsymptotic_potential_le_of_summable_excess hpos hexc m hm
    linarith only [hgap]
  · intro hpoint
    apply (weilLogShiftAsymptoticPositive_iff_sampled_potential hexc).mpr
    intro m hm
    refine ⟨hpm m hm, ?_⟩
    have ht := (tendsto_logShift_probe_of_summable_potential m hp0 (hpm m hm)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    have hgap := (nonneg_limit_iff_eventually_approx ht).mpr (hpoint m hm)
    linarith only [hgap]

/-- For nonnegative coefficients with finite excess, separate cutoffs for the
fixed probes are equivalent to a single cutoff for every expanding panel. -/
theorem weilLogShiftAsymptoticPositive_iff_pointwise_of_nonneg_coefficients
    {lam : ℕ → ℝ} (hlam : ∀ n : ℕ, 2 ≤ n → 0 ≤ lam n)
    (hexc : Summable (deviationExcess lam)) :
    WeilLogShiftAsymptoticPositive lam ↔
      ∀ m : ℕ, 2 ≤ m → ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
        -ε ≤ (weilFullFunctional lam (EF.weilTest
          (logShiftRiemannDifference k (Real.log m))
          (logShiftRiemannDifference k (Real.log m)))).re :=
  weilLogShiftAsymptoticPositive_iff_pointwise_of_summable_potential hexc
    (summable_potential_of_nonneg_coefficients hlam hexc 0)
    (fun m _ => summable_potential_of_nonneg_coefficients hlam hexc (Real.log m))

/-- Failure of uniform positivity on the nonnegative finite-excess domain has
one fixed witness, with a fixed negative margin in every sufficiently late panel. -/
theorem exists_persistent_fixed_logShift_negative_of_not_asymptoticPositive
    {lam : ℕ → ℝ} (hlam : ∀ n : ℕ, 2 ≤ n → 0 ≤ lam n)
    (hexc : Summable (deviationExcess lam)) (hnot : ¬ WeilLogShiftAsymptoticPositive lam) :
    ∃ m : ℕ, 2 ≤ m ∧ ∃ η : ℝ, 0 < η ∧ ∃ N : ℕ, ∀ k : ℕ, N ≤ k →
      (m : ℝ) ≤ Real.exp (2 * (k : ℝ)) ∧
        (weilFullFunctional lam (EF.weilTest
          (logShiftRiemannDifference k (Real.log m))
          (logShiftRiemannDifference k (Real.log m)))).re ≤ -η := by
  have hpotential : ¬ ∀ m : ℕ, 2 ≤ m →
      deviationPotential lam 0 ≤ deviationPotential lam (Real.log m) := fun h =>
    hnot ((weilLogShiftAsymptoticPositive_iff_potential_of_nonneg_coefficients hlam hexc).mpr h)
  push Not at hpotential
  obtain ⟨m, hm, hgap⟩ := hpotential
  let d := 2 * (deviationPotential lam (Real.log m) - deviationPotential lam 0)
  have hd : d < 0 := by dsimp only [d]; linarith only [hgap]
  have ht := (tendsto_logShift_probe_of_summable_potential m
    (summable_potential_of_nonneg_coefficients hlam hexc 0)
    (summable_potential_of_nonneg_coefficients hlam hexc (Real.log m))).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hev := (tendsto_order.mp ht).2 (d / 2) (by change d < d / 2; linarith only [hd])
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  refine ⟨m, hm, -d / 2, by linarith only [hd], max N ⌈Real.log m / 2⌉₊, ?_⟩
  intro k hk
  constructor
  · have hlog : Real.log m / 2 ≤ (k : ℝ) := (Nat.le_ceil _).trans
      (by exact_mod_cast (show ⌈Real.log m / 2⌉₊ ≤ k from (le_max_right _ _).trans hk))
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    exact (Real.log_le_iff_le_exp hmpos).mp (by linarith only [hlog])
  · have h := hN k ((le_max_left _ _).trans hk)
    change (weilFullFunctional lam (EF.weilTest
      (logShiftRiemannDifference k (Real.log m))
      (logShiftRiemannDifference k (Real.log m)))).re < d / 2 at h
    linarith only [h]

end RHTower
