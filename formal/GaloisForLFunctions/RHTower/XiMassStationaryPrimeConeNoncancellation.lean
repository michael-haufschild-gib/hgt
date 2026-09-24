import GaloisForLFunctions.RHTower.PrimeMassSharpUpper
import GaloisForLFunctions.RHTower.XiMassRapidityPhaseGeometry

/-!
# Cohesive prime mass at fixed timelike stationary frequencies

The complete uncentered half-weighted von Mangoldt sum has a nonzero complex
value at every fixed-prime stationary rapidity, cofinally along the literal
moving T1 cutoff. The proof retains all prime powers and uses positive mass
at the top of the cone. The RH-equivalent vacuum-centered source has weights
`Λ(n)-1`, so its signed cancellation and the two-rapidity integral remain open.
-/

open Finset

namespace RHTower

private theorem cos_ge_one_sub_abs (x : ℝ) : 1 - |x| ≤ Real.cos x := by
  have h := Real.abs_cos_sub_cos_le x 0
  simp only [Real.cos_zero, sub_zero] at h
  linarith [(abs_le.mp h).1]

private theorem centered_phase_sum_re_lower
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (w : ι → ℝ)
    (phase : ι → ℝ) (good : ι → Prop) [DecidablePred good] (η : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (hgood : ∀ i ∈ s, good i → |phase i| ≤ η) :
    (∑ i ∈ s, (w i : ℂ) * Complex.exp (((phase i : ℝ) : ℂ) * Complex.I)).re ≥
      (1 - η) * (∑ i ∈ s, w i) -
        (2 - η) * (∑ i ∈ s.filter (fun i => ¬ good i), w i) := by
  have hpoint (i : ι) (hi : i ∈ s) :
      w i * Real.cos (phase i) ≥
        (1 - η) * w i - (if good i then 0 else (2 - η) * w i) := by
    by_cases hg : good i
    · simp only [hg, ↓reduceIte, sub_zero]
      have hc : 1 - η ≤ Real.cos (phase i) :=
        (sub_le_sub_left (hgood i hi hg) 1).trans (cos_ge_one_sub_abs _)
      exact mul_le_mul_of_nonneg_right hc (hw i hi) |>.trans_eq (by ring)
    · simp only [hg, ↓reduceIte]
      have hc := Real.neg_one_le_cos (phase i)
      nlinarith [mul_nonneg (hw i hi) (show 0 ≤ Real.cos (phase i) + 1 by linarith)]
  have hsum := Finset.sum_le_sum (fun i hi => hpoint i hi)
  have hrewrite :
      (∑ i ∈ s, ((1 - η) * w i - (if good i then 0 else (2 - η) * w i))) =
        (1 - η) * (∑ i ∈ s, w i) -
          (2 - η) * (∑ i ∈ s.filter (fun i => ¬ good i), w i) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    congr 1
    rw [Finset.mul_sum, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hg : good i <;> simp [hg]
  calc
    (∑ i ∈ s, (w i : ℂ) * Complex.exp (((phase i : ℝ) : ℂ) * Complex.I)).re =
        ∑ i ∈ s, w i * Real.cos (phase i) := by
          simp [Complex.re_sum, Complex.mul_re, Complex.exp_ofReal_mul_I_re]
    _ ≥ ∑ i ∈ s, ((1 - η) * w i -
          (if good i then 0 else (2 - η) * w i)) := hsum
    _ = _ := hrewrite

/-- Uncentered von Mangoldt mass with phase aligned at the moving cutoff. -/
noncomputable def apexAlignedPrimeMass (X delta : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 0 ⌊X⌋₊,
    (((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      Complex.exp (((delta * (Real.log X - Real.log n) : ℝ) : ℂ) * Complex.I))

/-- The complete uncentered cone retains at least one quarter of its
square-root prime mass after apex alignment. -/
theorem apexAlignedPrimeMass_re_ge_quarter_sqrt_of_small_phase
    {X delta : ℝ} (hX : (1000000 : ℝ) ≤ X)
    (hMass : (Real.log 2 / 2) * Real.sqrt X ≤ primeMassHalf X)
    (hdelta : |delta| * Real.log (1000000 : ℝ) ≤ 1 / 1000) :
    (1 / 4 : ℝ) * Real.sqrt X ≤ (apexAlignedPrimeMass X delta).re := by
  let s : Finset ℕ := Finset.Icc 0 ⌊X⌋₊
  let w : ℕ → ℝ := fun n => ArithmeticFunction.vonMangoldt n / Real.sqrt n
  let good : ℕ → Prop := fun n => X / 1000000 ≤ (n : ℝ)
  let phase : ℕ → ℝ := fun n => delta * (Real.log X - Real.log n)
  have hX0 : 0 < X := by linarith
  have hXK : 1 ≤ X / 1000000 := by
    apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 1000000)).2
    simpa using hX
  have hw (n : ℕ) (hn : n ∈ s) : 0 ≤ w n := by
    exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hgood (n : ℕ) (hn : n ∈ s) (hng : good n) : |phase n| ≤ (1 : ℝ) / 1000 := by
    have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (by positivity) hng
    have hnX : (n : ℝ) ≤ X :=
      (Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2).trans (Nat.floor_le hX0.le)
    have hloglo : Real.log (X / 1000000) ≤ Real.log n :=
      Real.log_le_log (by positivity) hng
    have hloghi : Real.log n ≤ Real.log X := Real.log_le_log hn0 hnX
    have hdiff0 : 0 ≤ Real.log X - Real.log n := by linarith
    have hdiffK : Real.log X - Real.log n ≤ Real.log (1000000 : ℝ) := by
      rw [Real.log_div hX0.ne' (by norm_num : (1000000 : ℝ) ≠ 0)] at hloglo
      linarith
    calc
      |phase n| = |delta| * (Real.log X - Real.log n) := by
        simp [phase, abs_mul, abs_of_nonneg hdiff0]
      _ ≤ |delta| * Real.log (1000000 : ℝ) :=
        mul_le_mul_of_nonneg_left hdiffK (abs_nonneg _)
      _ ≤ 1 / 1000 := hdelta
  have hlow :
      (∑ n ∈ s.filter (fun n => ¬ good n), w n) ≤ primeMassHalf (X / 1000000) := by
    unfold primeMassHalf
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      rcases Finset.mem_filter.mp hn with ⟨_, hbad⟩
      have hnsmall : (n : ℝ) < X / 1000000 := lt_of_not_ge hbad
      exact Finset.mem_Icc.mpr ⟨Nat.zero_le _, Nat.le_floor hnsmall.le⟩
    · intro n hn hnot
      exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
  have hlowBound :
      (∑ n ∈ s.filter (fun n => ¬ good n), w n) ≤
        (21 / 1000 : ℝ) * Real.sqrt X := by
    have hupper := primeMassHalf_le_sqrt hXK
    have hsqrt : Real.sqrt (X / 1000000) = Real.sqrt X / 1000 := by
      rw [Real.sqrt_div (by positivity : 0 ≤ X)]
      norm_num
    rw [hsqrt] at hupper
    nlinarith [hlow]
  have htotal : (∑ n ∈ s, w n) = primeMassHalf X := rfl
  have hlog2 : (2 / 3 : ℝ) < Real.log 2 := by
    have h := Real.log_two_gt_d9
    norm_num at h ⊢
    linarith
  have hsqrt0 : 0 < Real.sqrt X := Real.sqrt_pos.mpr hX0
  have hreal := centered_phase_sum_re_lower s w phase good (1 / 1000 : ℝ) hw hgood
  change (apexAlignedPrimeMass X delta).re ≥
      (1 - 1 / 1000 : ℝ) * (∑ n ∈ s, w n) -
        (2 - 1 / 1000 : ℝ) * (∑ n ∈ s.filter (fun n => ¬ good n), w n) at hreal
  have hthird : (1 / 3 : ℝ) * Real.sqrt X ≤ primeMassHalf X := by
    have hfactor : (1 / 3 : ℝ) ≤ Real.log 2 / 2 := by linarith
    exact (mul_le_mul_of_nonneg_right hfactor hsqrt0.le).trans hMass
  have hquarter : (1 / 4 : ℝ) * Real.sqrt X ≤ (apexAlignedPrimeMass X delta).re := by
    rw [htotal] at hreal
    nlinarith [hthird, hlowBound]
  exact hquarter

/-- Pointwise noncancellation is the strict consequence of the quantitative
source bound. -/
theorem apexAlignedPrimeMass_nonzero_of_small_phase
    {X delta : ℝ} (hX : (1000000 : ℝ) ≤ X)
    (hMass : (Real.log 2 / 2) * Real.sqrt X ≤ primeMassHalf X)
    (hdelta : |delta| * Real.log (1000000 : ℝ) ≤ 1 / 1000) :
    apexAlignedPrimeMass X delta ≠ 0 := by
  have hbound := apexAlignedPrimeMass_re_ge_quarter_sqrt_of_small_phase hX hMass hdelta
  have hsqrt : 0 < Real.sqrt X := Real.sqrt_pos.mpr (by linarith)
  intro hz
  rw [hz] at hbound
  simp only [Complex.zero_re] at hbound
  linarith

/-- The square-root lower bound persists for every moving cutoff whose
stationary frequency tends to zero. -/
theorem eventually_apexAlignedPrimeMass_re_ge_quarter_sqrt_of_tendsto
    {X delta : ℝ → ℝ} (hX : Filter.Tendsto X Filter.atTop Filter.atTop)
    (hdelta : Filter.Tendsto delta Filter.atTop (nhds 0)) :
    ∀ᶠ u : ℝ in Filter.atTop,
      (1 / 4 : ℝ) * Real.sqrt (X u) ≤ (apexAlignedPrimeMass (X u) (delta u)).re := by
  have hlogK : 0 < Real.log (1000000 : ℝ) := Real.log_pos (by norm_num)
  have heps : 0 < (1 : ℝ) / (1000 * Real.log 1000000) := by positivity
  have hsmall : ∀ᶠ u : ℝ in Filter.atTop,
      |delta u| * Real.log (1000000 : ℝ) ≤ 1 / 1000 := by
    filter_upwards [hdelta.eventually (Metric.ball_mem_nhds 0 heps)] with u hu
    rw [Real.dist_eq, sub_zero] at hu
    have hmul := mul_lt_mul_of_pos_right hu hlogK
    have hcancel : ((1 : ℝ) / (1000 * Real.log 1000000)) *
        Real.log 1000000 = 1 / 1000 := by field_simp
    linarith
  filter_upwards [hX.eventually (Filter.eventually_ge_atTop (1000000 : ℝ)),
    hX.eventually eventually_sqrt_le_primeMassHalf, hsmall] with u hu hmass hδ
  exact apexAlignedPrimeMass_re_ge_quarter_sqrt_of_small_phase hu hmass hδ

/-- A moving prime cone cannot cancel when its frequency vanishes, regardless
of cutoff growth. -/
theorem eventually_apexAlignedPrimeMass_nonzero_of_tendsto
    {X delta : ℝ → ℝ} (hX : Filter.Tendsto X Filter.atTop Filter.atTop)
    (hdelta : Filter.Tendsto delta Filter.atTop (nhds 0)) :
    ∀ᶠ u : ℝ in Filter.atTop, apexAlignedPrimeMass (X u) (delta u) ≠ 0 := by
  filter_upwards [eventually_apexAlignedPrimeMass_re_ge_quarter_sqrt_of_tendsto hX hdelta,
    hX.eventually (Filter.eventually_gt_atTop (0 : ℝ))] with u hquarter hu
  have hsqrt : 0 < Real.sqrt (X u) := Real.sqrt_pos.mpr hu
  intro hz
  rw [hz] at hquarter
  simp only [Complex.zero_re] at hquarter
  linarith

/-- The literal frequency at a fixed timelike stationary rapidity vanishes cofinally. -/
theorem tendsto_stationary_prime_frequency_zero (a h : ℝ) :
    Filter.Tendsto (fun u : ℝ => a * Real.sinh (-timelikeRapidity u h))
      Filter.atTop (nhds 0) := by
  have hpow : Filter.Tendsto (fun u : ℝ => u ^ (2 : ℕ))
      Filter.atTop Filter.atTop :=
    Filter.tendsto_pow_atTop (by norm_num)
  have hden : Filter.Tendsto (fun u : ℝ => u ^ (2 : ℕ) - h ^ (2 : ℕ))
      Filter.atTop Filter.atTop := by
    simpa only [sub_eq_add_neg] using
      (Filter.tendsto_atTop_add_const_right Filter.atTop (-(h ^ (2 : ℕ))) hpow)
  have hinv : Filter.Tendsto
      (fun u : ℝ => (Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ)))⁻¹)
      Filter.atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_sqrt_atTop.comp hden)
  have hlim := hinv.const_mul (-(a * h))
  have hlim0 : Filter.Tendsto
      (fun u : ℝ => -(a * h) * (Real.sqrt (u ^ (2 : ℕ) - h ^ (2 : ℕ)))⁻¹)
      Filter.atTop (nhds 0) := by simpa using hlim
  refine hlim0.congr' ?_
  filter_upwards with u
  rw [Real.sinh_neg, sinh_timelikeRapidity, div_eq_mul_inv]
  ring

/-- At the exact moving T1 cone scale, every fixed timelike stationary prime
frequency leaves a square-root-sized full von Mangoldt sum. -/
theorem eventually_apexAlignedPrimeMass_stationary_re_ge_quarter_sqrt
    {d : ℝ} (hd : (1 : ℝ) / 2 < d) (a h : ℝ) :
    ∀ᶠ u : ℝ in Filter.atTop,
      (1 / 4 : ℝ) * Real.sqrt (Real.exp (d * u / (d - 1 / 2))) ≤
        (apexAlignedPrimeMass (Real.exp (d * u / (d - 1 / 2)))
          (a * Real.sinh (-timelikeRapidity u h))).re := by
  have hcoef : 0 < d / (d - 1 / 2) := by
    apply div_pos <;> linarith
  have harg : Filter.Tendsto (fun u : ℝ => d * u / (d - 1 / 2))
      Filter.atTop Filter.atTop := by
    simpa only [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm, id_eq] using
      Filter.tendsto_id.const_mul_atTop hcoef
  have hX : Filter.Tendsto (fun u : ℝ => Real.exp (d * u / (d - 1 / 2)))
      Filter.atTop Filter.atTop := Real.tendsto_exp_atTop.comp harg
  exact eventually_apexAlignedPrimeMass_re_ge_quarter_sqrt_of_tendsto hX
    (tendsto_stationary_prime_frequency_zero a h)

/-- The previous quantitative bound excludes exact cancellation. -/
theorem eventually_apexAlignedPrimeMass_stationary_nonzero
    {d : ℝ} (hd : (1 : ℝ) / 2 < d) (a h : ℝ) :
    ∀ᶠ u : ℝ in Filter.atTop,
      apexAlignedPrimeMass (Real.exp (d * u / (d - 1 / 2)))
        (a * Real.sinh (-timelikeRapidity u h)) ≠ 0 := by
  filter_upwards [eventually_apexAlignedPrimeMass_stationary_re_ge_quarter_sqrt hd a h] with u hq
  intro hz
  rw [hz] at hq
  have hsqrt : 0 < Real.sqrt (Real.exp (d * u / (d - 1 / 2))) :=
    Real.sqrt_pos.mpr (Real.exp_pos _)
  simp only [Complex.zero_re] at hq
  linarith

/-- The range indexed by `k+2` is exactly the complete prime cone above its
vanishing `0` and `1` coefficients. -/
private theorem sum_shift_two {M : ℕ} (hM : 2 ≤ M) (f : ℕ → ℂ) :
    (∑ n ∈ Finset.Icc 2 M, f n) =
      ∑ k ∈ Finset.range (M - 1), f (k + 2) := by
  have hs : Finset.Icc 2 M =
      (Finset.range (M - 1)).image (fun k : ℕ => k + 2) := by
    ext n
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · intro hn
      refine ⟨n - 2, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩
      constructor <;> omega
  rw [hs, Finset.sum_image]
  intro k hk l hl h
  change k + 2 = l + 2 at h
  omega

/-- Exact `k+2` indexing of the full uncentered prime cone. -/
theorem apexAlignedPrimeMass_eq_shifted
    {X : ℝ} (hX : 2 ≤ X) (delta : ℝ) :
    apexAlignedPrimeMass X delta =
      ∑ k ∈ Finset.range (⌊X⌋₊ - 1),
        (((ArithmeticFunction.vonMangoldt (k + 2) /
          Real.sqrt ((k + 2 : ℕ) : ℝ) : ℝ) : ℂ) *
          Complex.exp (((delta * (Real.log X - Real.log ((k + 2 : ℕ) : ℝ)) : ℝ) : ℂ) * Complex.I)) := by
  let f : ℕ → ℂ := fun n =>
    (((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
      Complex.exp (((delta * (Real.log X - Real.log n) : ℝ) : ℂ) * Complex.I))
  have hM : 2 ≤ ⌊X⌋₊ := Nat.le_floor hX
  change (∑ n ∈ Finset.Icc 0 ⌊X⌋₊, f n) =
    ∑ k ∈ Finset.range (⌊X⌋₊ - 1), f (k + 2)
  rw [← sum_shift_two hM]
  symm
  apply Finset.sum_subset (by intro n hn; simp at hn ⊢; omega)
  intro n hn hnot
  have hnlt : n < 2 := by
    have hle := (Finset.mem_Icc.mp hn).2
    by_contra h
    apply hnot
    exact Finset.mem_Icc.mpr ⟨by omega, hle⟩
  interval_cases n
  · simp [f]
  · simp [f]

end RHTower
