import GaloisForLFunctions.RHTower.CCM.CCMUnitRieszSuzukiGreenPositiveInverse

/-!
# Exact real-aperture Suzuki Green identity

The finite Chebyshev layer integral is evaluated at every positive real aperture, with
the literal cutoff `floor X`. Each atom agrees with the Suzuki reporter. This yields
`F(t)/2 = G(t) + polarCorrection(t) - archCorrection(t)` for every `t >= 1/2`,
retaining the same bounded corrections as the integer-log identity.

The positive Green inverse therefore proves an unconditional equivalence between RH and
a one-sided upper bound on the critical Chebyshev resolvent. No upper bound is assumed
in that equivalence or claimed as an unconditional fact.
-/

open Set MeasureTheory Topology
noncomputable section

namespace RHTower.UnitRieszRealAperture

open GaloisForLFunctions.RHTower

theorem psi_scaled_eq_indicator {X v : ℝ} (hX : 0 < X) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    Chebyshev.psi (X * v) = ∑ k ∈ Finset.Icc 0 ⌊X⌋₊,
      if (k : ℝ) / X ≤ v then ArithmeticFunction.vonMangoldt k else 0 := by
  have hXv0 : 0 ≤ X * v := mul_nonneg hX.le hv0
  have hfilter : (Finset.Icc 0 ⌊X⌋₊).filter (fun k : ℕ => (k : ℝ) / X ≤ v) =
      Finset.Icc 0 ⌊X * v⌋₊ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hk0, _⟩, hkv⟩
      have hkle : (k : ℝ) ≤ X * v := by
        rw [div_le_iff₀ hX] at hkv
        nlinarith
      exact ⟨hk0, Nat.le_floor hkle⟩
    · rintro ⟨hk0, hkfloor⟩
      have hkcast : (k : ℝ) ≤ (⌊X * v⌋₊ : ℝ) := by exact_mod_cast hkfloor
      have hkXv := hkcast.trans (Nat.floor_le hXv0)
      have hfloor : ⌊X * v⌋₊ ≤ ⌊X⌋₊ := Nat.floor_le_floor (by nlinarith)
      exact ⟨⟨hk0, hkfloor.trans hfloor⟩, (div_le_iff₀ hX).2 (by nlinarith)⟩
  rw [Chebyshev.psi_eq_sum_Icc, ← hfilter, Finset.sum_filter]

theorem psi_layer_eq_sum {X v : ℝ} (hX : 0 < X) (hv : v ∈ Icc (0 : ℝ) 1) :
    Chebyshev.psi (X * v) * layerWeight v = ∑ k ∈ Finset.Icc 0 ⌊X⌋₊,
      ArithmeticFunction.vonMangoldt k * (if (k : ℝ) / X ≤ v then layerWeight v else 0) := by
  rw [psi_scaled_eq_indicator hX hv.1 hv.2, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  split_ifs <;> ring

theorem integral_scaledPsi_layer {X : ℝ} (hX : 0 < X) :
    (∫ v in (0 : ℝ)..1, Chebyshev.psi (X * v) * layerWeight v) =
      ∑ k ∈ Finset.Icc 0 ⌊X⌋₊,
        ArithmeticFunction.vonMangoldt k * (1 - Real.sqrt ((k : ℝ) / X)) := by
  have hcongr : (∫ v in (0 : ℝ)..1, Chebyshev.psi (X * v) * layerWeight v) =
      ∫ v in (0 : ℝ)..1, ∑ k ∈ Finset.Icc 0 ⌊X⌋₊,
        ArithmeticFunction.vonMangoldt k * (if (k : ℝ) / X ≤ v then layerWeight v else 0) := by
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
    exact psi_layer_eq_sum hX hv
  rw [hcongr, intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [intervalIntegral.integral_const_mul]
    by_cases hk0 : k = 0
    · subst k
      simp
    · have hkpos : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk0
      have hkX : (k : ℝ) ≤ X :=
        (by exact_mod_cast (Finset.mem_Icc.mp hk).2 : (k : ℝ) ≤ (⌊X⌋₊ : ℝ)).trans
          (Nat.floor_le hX.le)
      rw [integral_indicatorLayer (div_pos hkpos hX) ((div_le_one hX).2 hkX)]
  · intro k _
    exact (intervalIntegrable_indicatorLayer ((k : ℝ) / X)).const_mul _

theorem intervalIntegrable_scaledPsi_layer {X : ℝ} (hX : 0 < X) :
    IntervalIntegrable (fun v : ℝ => Chebyshev.psi (X * v) * layerWeight v) volume 0 1 := by
  have hsum : IntervalIntegrable
      (fun v : ℝ => ∑ k ∈ Finset.Icc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt k *
        (if (k : ℝ) / X ≤ v then layerWeight v else 0)) volume 0 1 := by
    have h := IntervalIntegrable.sum (Finset.Icc 0 ⌊X⌋₊)
      (f := fun k : ℕ => fun v : ℝ => ArithmeticFunction.vonMangoldt k *
        (if (k : ℝ) / X ≤ v then layerWeight v else 0))
      (fun k _ => (intervalIntegrable_indicatorLayer ((k : ℝ) / X)).const_mul _)
    have hfun : (∑ k ∈ Finset.Icc 0 ⌊X⌋₊, fun v : ℝ => ArithmeticFunction.vonMangoldt k *
        (if (k : ℝ) / X ≤ v then layerWeight v else 0)) =
        fun v : ℝ => ∑ k ∈ Finset.Icc 0 ⌊X⌋₊, ArithmeticFunction.vonMangoldt k *
          (if (k : ℝ) / X ≤ v then layerWeight v else 0) := by
      funext v
      rw [Finset.sum_apply]
    rw [hfun] at h
    exact h
  refine hsum.congr fun v hv => ?_
  have hv0 : 0 ≤ v := le_of_lt (by simpa using hv.1)
  have hv1 : v ≤ 1 := by simpa using hv.2
  exact (psi_layer_eq_sum hX ⟨hv0, hv1⟩).symm

theorem resolvent_log_eq_prime_sum {X : ℝ} (hX : 0 < X) :
    criticalMellinChebyshevResolventSource (Real.log X) =
      (2 / Real.sqrt X) * (∑ k ∈ Finset.Icc 0 ⌊X⌋₊,
        ArithmeticFunction.vonMangoldt k * (1 - Real.sqrt ((k : ℝ) / X))) -
      (2 / 3) * Real.sqrt X := by
  have hsqrt : Real.sqrt X ≠ 0 := (Real.sqrt_pos.2 hX).ne'
  let f : ℝ → ℝ := fun v => X * v
  let f' : ℝ → ℝ := fun _ => X
  let G : ℝ → ℝ := fun y => (Chebyshev.psi y - y) * y ^ (-(1 / 2 : ℝ))
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (a := (0 : ℝ)) (b := (1 : ℝ)) (f := f) (f' := f') (g := G)
    (by fun_prop)
    (fun v _ => by
      dsimp only [f, f']
      simpa using (hasDerivAt_id v).const_mul X)
    (fun _ _ => hX.le)
  have hleft : (∫ v in (0 : ℝ)..1, (G ∘ f) v * f' v) =
      2 * Real.sqrt X * ∫ v in (0 : ℝ)..1,
        (Chebyshev.psi (X * v) - X * v) * layerWeight v := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro v hv
    rw [Set.uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hv
    change (Chebyshev.psi (X * v) - X * v) * (X * v) ^ (-(1 / 2 : ℝ)) * X =
      2 * Real.sqrt X * ((Chebyshev.psi (X * v) - X * v) * layerWeight v)
    rw [Real.mul_rpow hX.le hv.1, layerWeight_eq_rpow hv.1]
    have hscale : X ^ (-(1 / 2 : ℝ)) * X = Real.sqrt X := by
      nth_rewrite 2 [← Real.rpow_one X]
      rw [← Real.rpow_add hX, Real.sqrt_eq_rpow]
      congr 1
      ring
    calc
      (Chebyshev.psi (X * v) - X * v) *
          (X ^ (-(1 / 2 : ℝ)) * v ^ (-(1 / 2 : ℝ))) * X =
        (Chebyshev.psi (X * v) - X * v) * v ^ (-(1 / 2 : ℝ)) *
          (X ^ (-(1 / 2 : ℝ)) * X) := by ring
      _ = _ := by rw [hscale]; ring
  rw [hleft] at hsub
  have hsub' : (∫ y in (0 : ℝ)..X, (Chebyshev.psi y - y) * y ^ (-(1 / 2 : ℝ))) =
      2 * Real.sqrt X * ∫ v in (0 : ℝ)..1,
        (Chebyshev.psi (X * v) - X * v) * layerWeight v := by
    convert hsub.symm using 1
    all_goals norm_num [f, G]
  have hsplit : (∫ v in (0 : ℝ)..1, (Chebyshev.psi (X * v) - X * v) * layerWeight v) =
      (∫ v in (0 : ℝ)..1, Chebyshev.psi (X * v) * layerWeight v) -
        ∫ v in (0 : ℝ)..1, X * v * layerWeight v := by
    rw [← intervalIntegral.integral_sub (intervalIntegrable_scaledPsi_layer hX)
      (intervalIntegrable_polar X)]
    apply intervalIntegral.integral_congr
    intro v _
    ring
  have hsource := criticalMellinChebyshevResolventSource_log_eq hX
  rw [hsub', hsplit, integral_polar_layerWeight, integral_scaledPsi_layer hX] at hsource
  rw [hsource]
  field_simp [hsqrt, hX.ne']
  rw [Real.sq_sqrt hX.le]

theorem reporter_atom_eq_layer (H : ℝ) {k : ℕ} (hk : 0 < k) :
    criticalMellinAtomWeight k * unitRieszSuzukiReporter H (Real.log k) =
      (ArithmeticFunction.vonMangoldt k / Real.sqrt (Real.exp H)) *
        (1 - Real.sqrt ((k : ℝ) / Real.exp H)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hsk := sqrt_eq_exp_log_div_two hkR
  have hsX : Real.sqrt (Real.exp H) = Real.exp (H / 2) := by
    simpa only [Real.log_exp] using sqrt_eq_exp_log_div_two (Real.exp_pos H)
  have hE1 : Real.exp ((Real.log k - H) / 2) =
      Real.sqrt (k : ℝ) / Real.sqrt (Real.exp H) := by
    rw [hsk, hsX, ← Real.exp_sub]
    congr 1
    ring
  have hE2 : Real.exp (Real.log k - H) =
      (Real.sqrt (k : ℝ) / Real.sqrt (Real.exp H)) ^ 2 := by
    rw [← hE1, pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [criticalMellinAtomWeight_eq_screwPrimeWeight hk, screwPrimeWeight,
    unitRieszSuzukiReporter, hE1, hE2, Real.sqrt_div hkR.le]
  field_simp [(Real.sqrt_pos.mpr hkR).ne', (Real.sqrt_pos.mpr (Real.exp_pos H)).ne']

theorem reporter_sum_eq_layer (H : ℝ) :
    (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
      criticalMellinAtomWeight k * unitRieszSuzukiReporter H (Real.log k)) =
      (1 / Real.sqrt (Real.exp H)) * ∑ k ∈ Finset.Icc 0 ⌊Real.exp H⌋₊,
        ArithmeticFunction.vonMangoldt k * (1 - Real.sqrt ((k : ℝ) / Real.exp H)) := by
  have hsum : (∑ k ∈ Finset.Icc 0 ⌊Real.exp H⌋₊,
      ArithmeticFunction.vonMangoldt k * (1 - Real.sqrt ((k : ℝ) / Real.exp H))) =
      ∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        ArithmeticFunction.vonMangoldt k * (1 - Real.sqrt ((k : ℝ) / Real.exp H)) := by
    symm
    apply Finset.sum_subset
    · intro k hk
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, (Finset.mem_Icc.mp hk).2⟩
    · intro k hk hnot
      have hkN := (Finset.mem_Icc.mp hk).2
      have hk01 : k = 0 ∨ k = 1 := by
        simp only [Finset.mem_Icc] at hnot
        omega
      rcases hk01 with rfl | rfl <;> simp
  rw [hsum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [reporter_atom_eq_layer H (by have := (Finset.mem_Icc.mp hk).1; omega)]
  ring

theorem reporter_sum_eq_resolvent_half (H : ℝ) :
    (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
      criticalMellinAtomWeight k * unitRieszSuzukiReporter H (Real.log k)) =
      criticalMellinChebyshevResolventSource H / 2 + Real.exp (H / 2) / 3 := by
  have hsource := resolvent_log_eq_prime_sum (Real.exp_pos H)
  rw [Real.log_exp] at hsource
  have hsX : Real.sqrt (Real.exp H) = Real.exp (H / 2) := by
    simpa only [Real.log_exp] using sqrt_eq_exp_log_div_two (Real.exp_pos H)
  rw [reporter_sum_eq_layer, hsX]
  rw [hsX] at hsource
  rw [hsource]
  ring

end RHTower.UnitRieszRealAperture

namespace RHTower

open UnitRieszRealAperture GaloisForLFunctions.RHTower

theorem criticalMellinChebyshevResolventSource_half_eq_suzukiGreen
    {H : ℝ} (hH : unitRieszSuzukiBase ≤ H) :
    criticalMellinChebyshevResolventSource H / 2 =
      unitRieszSuzukiGreen H + unitRieszSuzukiPolarCorrection H -
        unitRieszSuzukiArchCorrection H := by
  have hreporter : Continuous (unitRieszSuzukiReporter H) := by
    unfold unitRieszSuzukiReporter
    fun_prop
  have harch : ContinuousOn ccmPublishedArchimedeanDensity (Icc unitRieszSuzukiBase H) := by
    intro h hh
    have hhpos : 0 < h := unitRieszSuzukiBase_pos.trans_le hh.1
    unfold ccmPublishedArchimedeanDensity
    have hden : Real.exp h - Real.exp (-h) ≠ 0 := by
      have he : Real.exp (-h) < Real.exp h := Real.exp_lt_exp.mpr (by linarith)
      linarith
    exact ((Real.continuous_exp.comp (continuous_id.div_const 2)).continuousAt.div
      ((Real.continuous_exp.sub
        (Real.continuous_exp.comp continuous_id.neg)).continuousAt) hden).continuousWithinAt
  have harchInt : IntervalIntegrable
      (fun h => unitRieszSuzukiReporter H h * ccmPublishedArchimedeanDensity h)
      volume unitRieszSuzukiBase H := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hH]
    exact hreporter.continuousOn.mul harch
  have hpolarInt : IntervalIntegrable
      (fun h => unitRieszSuzukiReporter H h * (2 * Real.cosh (h / 2)))
      volume unitRieszSuzukiBase H := by
    exact (hreporter.mul (continuous_const.mul
      (Real.continuous_cosh.comp (continuous_id.div_const 2)))).intervalIntegrable _ _
  have hsplit : (∫ h in unitRieszSuzukiBase..H, unitRieszSuzukiReporter H h *
      (ccmPublishedArchimedeanDensity h - 2 * Real.cosh (h / 2))) =
      unitRieszSuzukiArchCorrection H -
        ∫ h in unitRieszSuzukiBase..H, unitRieszSuzukiReporter H h * (2 * Real.cosh (h / 2)) := by
    rw [unitRieszSuzukiArchCorrection, ← intervalIntegral.integral_sub harchInt hpolarInt]
    apply intervalIntegral.integral_congr
    intro h _
    ring
  have hwindow : ccmGuinandWeilCompletedSourceWindow unitRieszSuzukiBase H
      (unitRieszSuzukiReporter H) =
      (∑ k ∈ Finset.Icc 2 ⌊Real.exp H⌋₊,
        criticalMellinAtomWeight k * unitRieszSuzukiReporter H (Real.log k)) +
      ∫ h in unitRieszSuzukiBase..H, unitRieszSuzukiReporter H h *
        (ccmPublishedArchimedeanDensity h - 2 * Real.cosh (h / 2)) := by
    rw [ccmGuinandWeilCompletedSourceWindow]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [if_pos (unitRieszSuzukiBase_lt_log_of_two_le (Finset.mem_Icc.mp hk).1)]
  have hgreen := unitRieszSuzuki_completedSource_eq_green hH
  rw [hwindow, hsplit, reporter_sum_eq_resolvent_half] at hgreen
  rw [unitRieszSuzukiPolarCorrection]
  linarith

theorem riemannHypothesis_of_criticalResolvent_boundedAbove
    {B : ℝ} (hB : ∀ t : ℝ, 0 ≤ t → criticalMellinChebyshevResolventSource t ≤ B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_unitRieszSuzukiGreen_boundedAbove
    (B := B / 2 + unitRieszSuzukiPolarUniformBound + unitRieszSuzukiArchUniformBound)
  intro t ht
  have heq := criticalMellinChebyshevResolventSource_half_eq_suzukiGreen ht
  have hpolar := (abs_le.mp (abs_unitRieszSuzukiPolarCorrection_le ht)).1
  have harch := (abs_le.mp (abs_unitRieszSuzukiArchCorrection_le ht)).2
  linarith [hB t (unitRieszSuzukiBase_pos.le.trans ht)]

theorem riemannHypothesis_iff_criticalResolvent_boundedAbove :
    RiemannHypothesis ↔ ∃ B : ℝ, ∀ t : ℝ, 0 ≤ t →
      criticalMellinChebyshevResolventSource t ≤ B := by
  constructor
  · intro hRH
    obtain ⟨B, _, hB⟩ := riemannHypothesis_iff_unitRieszCriticalResolventBounded.mp hRH
    exact ⟨B, fun t ht => (le_abs_self _).trans (hB t ht)⟩
  · rintro ⟨B, hB⟩
    exact riemannHypothesis_of_criticalResolvent_boundedAbove hB

end RHTower
