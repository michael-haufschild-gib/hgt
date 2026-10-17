import GaloisForLFunctions.BiScaleUncertainty.CoherentFiberPlasticInfimum

/-!
# Quantitative confinement gap in actual coherent classes

Finite source support bounds the complete coherent price by original energy.
The explicit positive plastic tail bounds that energy from below. Together
they give a positive gap above the sharp fiber infimum and force every
sufficiently accurate near-minimizer to leave each prescribed source window.
-/

open MeasureTheory Set Filter
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.ConfinedCoherentPlasticGap
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
open _root_.RHTower.WeilLevyCoshCrossover _root_.RHTower.WeilLevyPoleGauss
open GaloisForLFunctions.RHTower
open CenteredHyperbolicGram ProjectedHyperbolicGram ArithmeticMultiplierCollisions
open DyadicHyperbolicMoment HyperbolicRay SourceLattice SignedCoherentMoment
open CoherentSourceProjection LocalCoherentFilter FiniteFilterSchurResidual
open FoldedHyperbolicCellDefect CoherentFiberPlasticInfimum OutwardCoherentEscape
noncomputable section

private abbrev d := Real.log 2
private theorem d_pos : 0 < d := Real.log_pos (by norm_num : (1 : ℝ) < 2)

/-- Open source window whose first omitted lattice lag equals its diameter. -/
def confinementRadius (N : ℕ) : ℝ := ((N : ℝ) + 1) * Real.log 2 / 2

theorem confinementRadius_pos (N : ℕ) : 0 < confinementRadius N :=
  div_pos (mul_pos (by positivity) d_pos) (by norm_num)

/-- Exact elementary plastic tail beyond the source diameter and crossover threshold. -/
def confinementTail (N : ℕ) : ℝ :=
  archLevyAntideriv (2 * confinementRadius N + screwSignThreshold)

theorem confinementTail_pos (N : ℕ) : 0 < confinementTail N :=
  archLevyAntideriv_pos (by linarith [confinementRadius_pos N, screwSignThreshold_pos])

theorem confinementTail_eq_integral (N : ℕ) :
    confinementTail N = ∫ x in Ioi (2 * confinementRadius N + screwSignThreshold),
      levyCoshKernel screwSignThreshold x := by
  have ht : 0 < 2 * confinementRadius N + screwSignThreshold := by
    linarith [confinementRadius_pos N, screwSignThreshold_pos]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => show
    levyCoshKernel screwSignThreshold x = _root_.RHTower.archLevyDensity x from by
      unfold levyCoshKernel
      exact if_neg (by have hp := confinementRadius_pos N; change _ < x at hx; linarith))]
  exact (integral_archLevyDensity_Ioi ht).symm

/-- Explicit cost of recovering the full coherent price from confined source energy. -/
def confinementCost (N : ℕ) : ℝ :=
  (2 * (N : ℝ) + 1) * Real.sinh (confinementRadius N / 2) ^ 2

theorem confinementCost_pos (N : ℕ) : 0 < confinementCost N :=
  mul_pos (by positivity) (sq_pos_of_pos (Real.sinh_pos_iff.mpr (by
    linarith [confinementRadius_pos N])))

/-- The full signed coherent price of the canonical odd source. -/
def coherentPrice (f : C_c(ℝ, ℝ)) : ℝ :=
  localBudget (oddCompactSource f) - schurResidualGain (oddCompactSource f)

theorem coherentPrice_nonneg (f : C_c(ℝ, ℝ)) : 0 ≤ coherentPrice f := by
  have hi : 0 ≤ ∫ x in (0 : ℝ)..1, cellFold (oddCompactSource f) x ^ 2 :=
    intervalIntegral.integral_nonneg (by norm_num) (fun _ _ => sq_nonneg _)
  rw [integral_cellFold_sq] at hi
  have hh := mul_nonneg hi d_pos.le
  rw [div_mul_cancel₀ _ d_pos.ne'] at hh
  exact hh

/-- The coherent price vanishes exactly on the full zero-fold class. -/
theorem coherentPrice_eq_zero_iff (f : C_c(ℝ, ℝ)) :
    coherentPrice f = 0 ↔ cellFold (oddCompactSource f) = 0 := by
  constructor
  · intro hz
    have hi : (∫ x in (0 : ℝ)..1, cellFold (oddCompactSource f) x ^ 2) = 0 := by
      rw [integral_cellFold_sq]
      change coherentPrice f / d = 0
      rw [hz, zero_div]
    have hc := (cellFold (oddCompactSource f)).continuous.pow 2
    have hae := (intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae
      (by norm_num : (0 : ℝ) ≤ 1) (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (hc.intervalIntegrable (μ := volume) 0 1)).mp hi
    rw [MeasureTheory.restrict_Ioc_eq_restrict_Icc] at hae
    have he := Measure.eqOn_of_ae_eq hae hc.continuousOn continuous_const.continuousOn
      (show Icc (0 : ℝ) 1 ⊆ closure (interior (Icc (0 : ℝ) 1)) by
        rw [closure_interior_Icc (by norm_num : (0 : ℝ) ≠ 1)])
    have hcell (x : ℝ) (hx : x ∈ Icc (0 : ℝ) 1) : cellFold (oddCompactSource f) x = 0 := by
      apply sq_eq_zero_iff.mp
      exact he hx
    ext x
    obtain ⟨y, hy, hxy⟩ := (cellFold_periodic (oddCompactSource f)).exists_mem_Ico₀
      (by norm_num : (0 : ℝ) < 1) x
    change cellFold (oddCompactSource f) x = 0
    rw [hxy]
    exact hcell y ⟨hy.1, hy.2.le⟩
  · intro hz
    have hi := integral_cellFold_sq f
    simp only [hz, ContinuousMap.zero_apply, zero_pow (by decide : 2 ≠ 0),
      intervalIntegral.integral_zero] at hi
    have he := congrArg (fun x : ℝ => x * d) hi
    rw [zero_mul, div_mul_cancel₀ _ d_pos.ne'] at he
    exact he.symm

theorem coherentPrice_pos_iff (f : C_c(ℝ, ℝ)) :
    0 < coherentPrice f ↔ cellFold (oddCompactSource f) ≠ 0 := by
  constructor
  · intro hp hz
    have hc := (coherentPrice_eq_zero_iff f).mpr hz
    linarith only [hp, hc]
  · intro hn
    have hc : coherentPrice f ≠ 0 := fun hz => hn ((coherentPrice_eq_zero_iff f).mp hz)
    exact lt_of_le_of_ne (coherentPrice_nonneg f) hc.symm

private theorem odd_idem (f : C_c(ℝ, ℝ)) :
    oddCompactSource (oddCompactSource f) = oddCompactSource f := by
  ext u
  change (oddCompactSource f u - oddCompactSource f (-u)) / 2 = _
  rw [oddCompactSource_odd]
  ring

private theorem intrinsic_window (g : C_c(ℝ, ℝ)) (u : ℝ) (hu : g u ≠ 0) :
    |u| < confinementRadius (sourceCutoff g) := by
  have hb := abs_le_multiplierSourceRadius g u hu
  have hg := sourceCutoff_gap g
  unfold confinementRadius
  nlinarith only [hb, hg, d_pos]

private theorem window_lag_zero (g : C_c(ℝ, ℝ)) (N : ℕ)
    (hw : ∀ u, g u ≠ 0 → |u| < confinementRadius N) (x : ℝ)
    (hx : 2 * confinementRadius N ≤ x) : autocorr g x = 0 := by
  unfold autocorr
  have hp (u : ℝ) : g u * g (u + x) = 0 := by
    by_cases hu : g u = 0
    · rw [hu, zero_mul]
    by_cases hv : g (u + x) = 0
    · rw [hv, mul_zero]
    have hbu := (abs_lt.mp (hw u hu)).1
    have hbv := (abs_lt.mp (hw (u + x) hv)).2
    linarith only [hbu, hbv, hx]
  simp_rw [hp]
  simp

private theorem sinh_lattice_zero (g : C_c(ℝ, ℝ)) (N : ℕ)
    (hw : ∀ u, g u ≠ 0 → |u| < confinementRadius N) (k : ℕ) (hk : N ≤ k) :
    autocorr (sinhCompact (1 / 2) g) (((k : ℝ) + 1) * d) = 0 := by
  apply window_lag_zero (sinhCompact (1 / 2) g) N
  · intro u hu
    apply hw u
    intro hz
    exact hu (by change Real.sinh _ * g u = 0; rw [hz, mul_zero])
  · have hk' : (N : ℝ) ≤ k := by exact_mod_cast hk
    unfold confinementRadius
    nlinarith only [hk', d_pos]

private theorem price_formula (f : C_c(ℝ, ℝ)) :
    coherentPrice f = autocorr (sinhCompact (1 / 2) (oddCompactSource f)) 0 +
      2 * ∑ k ∈ Finset.range (sourceCutoff (oddCompactSource f)),
        autocorr (sinhCompact (1 / 2) (oddCompactSource f)) (((k : ℝ) + 1) * d) := by
  have he := odd_filter_pairing_identity f
  change signedCorrectionMass (oddCompactSource f) + centeredFilterPairing (oddCompactSource f) = _ at he
  rw [coherentPrice, localBudget_sub_residualGain]
  linarith only [he]

private theorem price_window_formula (f : C_c(ℝ, ℝ)) (N : ℕ)
    (hw : ∀ u, oddCompactSource f u ≠ 0 → |u| < confinementRadius N) :
    coherentPrice f = autocorr (sinhCompact (1 / 2) (oddCompactSource f)) 0 +
      2 * ∑ k ∈ Finset.range N,
        autocorr (sinhCompact (1 / 2) (oddCompactSource f)) (((k : ℝ) + 1) * d) := by
  have hM : (∑' k : ℕ, autocorr (sinhCompact (1 / 2) (oddCompactSource f)) (((k : ℝ) + 1) * d)) =
      ∑ k ∈ Finset.range (sourceCutoff (oddCompactSource f)),
        autocorr (sinhCompact (1 / 2) (oddCompactSource f)) (((k : ℝ) + 1) * d) :=
    tsum_eq_sum (fun k hk => sinh_lattice_zero _ _ (intrinsic_window _) k
      (by simpa only [Finset.mem_range, not_lt] using hk))
  have hN : (∑' k : ℕ, autocorr (sinhCompact (1 / 2) (oddCompactSource f)) (((k : ℝ) + 1) * d)) =
      ∑ k ∈ Finset.range N,
        autocorr (sinhCompact (1 / 2) (oddCompactSource f)) (((k : ℝ) + 1) * d) :=
    tsum_eq_sum (fun k hk => sinh_lattice_zero _ N hw k
      (by simpa only [Finset.mem_range, not_lt] using hk))
  rw [price_formula, hM.symm.trans hN]

private theorem sinh_energy_bound (g : C_c(ℝ, ℝ)) (N : ℕ)
    (hw : ∀ u, g u ≠ 0 → |u| < confinementRadius N) :
    autocorr (sinhCompact (1 / 2) g) 0 ≤
      Real.sinh (confinementRadius N / 2) ^ 2 * autocorr g 0 := by
  have hp (u : ℝ) : sinhCompact (1 / 2) g u ^ 2 ≤
      Real.sinh (confinementRadius N / 2) ^ 2 * g u ^ 2 := by
    change (Real.sinh ((1 / 2 : ℝ) * u) * g u) ^ 2 ≤ _
    rw [show (1 / 2 : ℝ) * u = u / 2 by ring, mul_pow]
    by_cases hu : g u = 0
    · simp only [hu, zero_pow (by decide : 2 ≠ 0), mul_zero, le_refl]
    have hs : |Real.sinh (u / 2)| ≤ Real.sinh (confinementRadius N / 2) := by
      rw [Real.abs_sinh, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact Real.sinh_le_sinh.mpr (by linarith only [hw u hu])
    have hh := abs_le.mp hs
    have hsq : Real.sinh (u / 2) ^ 2 ≤ Real.sinh (confinementRadius N / 2) ^ 2 := by
      nlinarith only [mul_nonneg (sub_nonneg.mpr hh.2) (sub_nonneg.mpr hh.1)]
    exact mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
  have hi : Integrable (fun u : ℝ => sinhCompact (1 / 2) g u ^ 2) :=
    integrable_sq (sinhCompact (1 / 2) g).continuous (sinhCompact (1 / 2) g).hasCompactSupport
  have hj : Integrable (fun u : ℝ => Real.sinh (confinementRadius N / 2) ^ 2 * g u ^ 2) :=
    (integrable_sq g.continuous g.hasCompactSupport).const_mul _
  have he := integral_mono hi hj hp
  rw [integral_const_mul, integral_sq_eq_autocorr_zero, integral_sq_eq_autocorr_zero] at he
  exact he

/-- Finite signed multiplier correlations control the full coherent price under actual confinement. -/
theorem coherentPrice_le_confinedEnergy (f : C_c(ℝ, ℝ)) (N : ℕ)
    (hw : ∀ u, oddCompactSource f u ≠ 0 → |u| < confinementRadius N) :
    coherentPrice f ≤ confinementCost N * autocorr (oddCompactSource f) 0 := by
  let S := sinhCompact (1 / 2) (oddCompactSource f)
  have hs : (∑ k ∈ Finset.range N, autocorr S (((k : ℝ) + 1) * d)) ≤
      (N : ℝ) * autocorr S 0 := by
    have h := Finset.sum_le_sum (s := Finset.range N) (fun k _ =>
      (le_abs_self (autocorr S (((k : ℝ) + 1) * d))).trans
        (abs_autocorr_le_zero S.hasCompactSupport S.continuous _))
    simpa only [Finset.sum_const, Finset.card_range, nsmul_eq_mul] using h
  have hb := sinh_energy_bound (oddCompactSource f) N hw
  calc
    coherentPrice f = autocorr S 0 + 2 * ∑ k ∈ Finset.range N, autocorr S (((k : ℝ) + 1) * d) :=
      price_window_formula f N hw
    _ ≤ (2 * (N : ℝ) + 1) * autocorr S 0 := by nlinarith only [hs]
    _ ≤ (2 * (N : ℝ) + 1) *
        (Real.sinh (confinementRadius N / 2) ^ 2 * autocorr (oddCompactSource f) 0) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = confinementCost N * autocorr (oddCompactSource f) 0 := by unfold confinementCost; ring

/-- The explicitly evaluated plastic tail is a coercive energy cost for every confined compact source. -/
theorem confinementTail_mul_energy_le_jump (g : C_c(ℝ, ℝ)) (N : ℕ)
    (hw : ∀ u, g u ≠ 0 → |u| < confinementRadius N) :
    confinementTail N * autocorr g 0 ≤ plasticJumpEnergy g := by
  let T := 2 * confinementRadius N + screwSignThreshold
  have hT : 0 < T := by dsimp [T]; linarith [confinementRadius_pos N, screwSignThreshold_pos]
  have hn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (fun x => (autocorr g 0 - autocorr g x) * levyCoshKernel screwSignThreshold x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact mul_nonneg (autocorr_sub_nonneg g.hasCompactSupport g.continuous x)
      (levyCoshKernel_pos hx).le
  have hst : Ioi T ≤ᵐ[volume] Ioi (0 : ℝ) :=
    Filter.Eventually.of_forall fun _ hx => hT.trans hx
  have hm := setIntegral_mono_set (integrableOn_plasticJumpIntegrand g) hn hst
  have he : (∫ x in Ioi T, (autocorr g 0 - autocorr g x) * levyCoshKernel screwSignThreshold x) =
      autocorr g 0 * confinementTail N := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun x hx => show
      (autocorr g 0 - autocorr g x) * levyCoshKernel screwSignThreshold x =
        autocorr g 0 * levyCoshKernel screwSignThreshold x from by
          rw [window_lag_zero g N hw x (by change T < x at hx; dsimp [T] at hx
              linarith [screwSignThreshold_pos]), sub_zero]),
      integral_const_mul, ← confinementTail_eq_integral]
  calc
    confinementTail N * autocorr g 0 = autocorr g 0 * confinementTail N := mul_comm _ _
    _ = ∫ x in Ioi T, (autocorr g 0 - autocorr g x) * levyCoshKernel screwSignThreshold x := he.symm
    _ ≤ plasticJumpEnergy g := hm

private theorem price_eq_of_mem (f g : C_c(ℝ, ℝ)) (hg : g ∈ coherentFiber f) :
    coherentPrice g = coherentPrice f := by
  have hh := integral_cellFold_sq g
  rw [hg.1, hg.2] at hh
  have he := congrArg (fun x : ℝ => x * d) (hh.symm.trans (integral_cellFold_sq f))
  rw [div_mul_cancel₀ _ d_pos.ne', div_mul_cancel₀ _ d_pos.ne'] at he
  unfold coherentPrice
  rw [hg.1]
  exact he

/-- Actual odd coherent fiber intersected with a prescribed open support window. -/
def confinedFiber (f : C_c(ℝ, ℝ)) (N : ℕ) : Set C_c(ℝ, ℝ) :=
  {g | g ∈ coherentFiber f ∧ ∀ u, g u ≠ 0 → |u| < confinementRadius N}

/-- Explicit positive separation from the global plastic infimum under confinement. -/
def confinementGap (f : C_c(ℝ, ℝ)) (N : ℕ) : ℝ :=
  2 * confinementTail N * coherentPrice f / confinementCost N

theorem confinementGap_nonneg (f : C_c(ℝ, ℝ)) (N : ℕ) : 0 ≤ confinementGap f N :=
  div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (confinementTail_pos N).le)
    (coherentPrice_nonneg f)) (confinementCost_pos N).le

theorem confinementGap_pos_iff (f : C_c(ℝ, ℝ)) (N : ℕ) :
    0 < confinementGap f N ↔ cellFold (oddCompactSource f) ≠ 0 := by
  constructor
  · intro hp hz
    have hc := (coherentPrice_eq_zero_iff f).mpr hz
    simp only [confinementGap, hc, mul_zero, zero_div, lt_self_iff_false] at hp
  · intro hn
    exact div_pos (mul_pos (mul_pos (by norm_num) (confinementTail_pos N))
      ((coherentPrice_pos_iff f).mpr hn)) (confinementCost_pos N)

/-- Uniform quantitative gap for every actual source in a confined full coherent class. -/
theorem confined_plastic_gap (f g : C_c(ℝ, ℝ)) (N : ℕ) (hg : g ∈ confinedFiber f N) :
    confinementGap f N ≤ plasticCrossover g + 2 * fiberMoment f ^ 2 := by
  have hb := coherentPrice_le_confinedEnergy g N (by simpa only [hg.1.1] using hg.2)
  rw [hg.1.1, price_eq_of_mem f g hg.1] at hb
  have ht := confinementTail_mul_energy_le_jump g N hg.2
  have he := plastic_eq_of_mem f g hg.1
  apply (div_le_iff₀ (confinementCost_pos N)).mpr
  calc
    2 * confinementTail N * coherentPrice f ≤
        2 * confinementTail N * (confinementCost N * autocorr g 0) :=
      mul_le_mul_of_nonneg_left hb (mul_nonneg (by norm_num) (confinementTail_pos N).le)
    _ = confinementCost N * (2 * (confinementTail N * autocorr g 0)) := by ring
    _ ≤ confinementCost N * (2 * plasticJumpEnergy g) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ht (by norm_num)) (confinementCost_pos N).le
    _ = (plasticCrossover g + 2 * fiberMoment f ^ 2) * confinementCost N := by rw [he]; ring

/-- Unconditional confinement bound with a window supplied by the actual input's compact support. -/
theorem intrinsic_plastic_gap (f : C_c(ℝ, ℝ)) :
    confinementGap f (sourceCutoff (oddCompactSource f)) ≤
      plasticCrossover (oddCompactSource f) + 2 * fiberMoment f ^ 2 :=
  confined_plastic_gap f (oddCompactSource f) _ ⟨⟨odd_idem f, rfl⟩, intrinsic_window _⟩

/-- Any coherent near-minimizer below the explicit threshold must leave the prescribed window. -/
theorem near_minimizer_outside (f g : C_c(ℝ, ℝ)) (N : ℕ) (hg : g ∈ coherentFiber f)
    (hq : plasticCrossover g + 2 * fiberMoment f ^ 2 < confinementGap f N) :
    ∃ u : ℝ, confinementRadius N ≤ |u| ∧ g u ≠ 0 := by
  by_contra hn
  have hw : ∀ u, g u ≠ 0 → |u| < confinementRadius N := by
    intro u hu
    by_contra hb
    exact hn ⟨u, le_of_not_gt hb, hu⟩
  have he := confined_plastic_gap f g N ⟨hg, hw⟩
  linarith only [he, hq]

/-- The explicit outward producer crosses every positive confinement threshold in its coherent class. -/
theorem exists_producer_below_confinement (f : C_c(ℝ, ℝ)) (N : ℕ)
    (hf : cellFold (oddCompactSource f) ≠ 0) :
    ∃ n : ℕ, plasticCrossover (escapingSource f n) + 2 * fiberMoment f ^ 2 < confinementGap f N ∧
      ∃ u : ℝ, confinementRadius N ≤ |u| ∧ escapingSource f n u ≠ 0 := by
  obtain ⟨n, hn⟩ := exists_escapingSource_lt f (confinementGap f N)
    ((confinementGap_pos_iff f N).mpr hf)
  have hq : plasticCrossover (escapingSource f n) + 2 * fiberMoment f ^ 2 < confinementGap f N :=
    by linarith only [hn]
  exact ⟨n, hq, near_minimizer_outside f _ N (escapingSource_mem f n) hq⟩

end
end GaloisForLFunctions.BiScaleUncertainty.ConfinedCoherentPlasticGap
