import GaloisForLFunctions.RHTower.CCM.CCMPrimeDeficitEulerCriticalMass
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Positive rigidity for the actual Euler renewal kernel

For every fixed positive Euler modulus, the nonnegative causal super-renewal
cone has no nonzero continuous element with finite critical Laplace mass.
The proof retains the actual rough squared kernel. A finite portion already
has mass greater than one; translation of the Laplace weight then forces the
integral of every proposed positive comparison error to vanish. One explicit
arithmetic progression also gives superunit mass beyond exponent one. In
particular, the positive super-renewal cone with an `O(exp T)` budget is zero.

This is a restriction on positive comparison errors. It gives no estimate
for the signed Chebyshev deficit or its Euler forcing.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace RHTower

private theorem finite_delay_sum_le_dilation
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (f : ℝ → ℝ) (hf : ∀ t, 0 ≤ f t)
    (hcausal : ∀ t, t < 0 → f t = 0) (U : ℕ) (T : ℝ) :
    (∑ n ∈ Finset.Icc 1 U, a n * f (T - Real.log n)) ≤
      logarithmicWeightedDilation a f T := by
  unfold logarithmicWeightedDilation
  by_cases hU : U ≤ ⌊Real.exp T⌋₊
  · exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc le_rfl hU)
      (fun n _ _ => mul_nonneg (ha n) (hf _))
  · apply le_of_eq
    symm
    apply Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (le_of_not_ge hU))
    intro n hn hnT
    have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
    have hnot : ¬n ≤ ⌊Real.exp T⌋₊ := by
      intro h
      exact hnT (Finset.mem_Icc.mpr ⟨hn1, h⟩)
    have hexp : Real.exp T < (n : ℝ) := by
      exact lt_of_not_ge (fun h => hnot ((Nat.le_floor_iff (Real.exp_pos T).le).mpr h))
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hlog : T < Real.log n := (Real.lt_log_iff_exp_lt hnpos).mpr hexp
    rw [hcausal _ (sub_neg.mpr hlog), mul_zero]

private theorem laplace_delay_identity (σ u t : ℝ) (f : ℝ → ℝ) :
    Real.exp (-σ * t) * f (t - u) =
      Real.exp (-σ * u) * (Real.exp (-σ * (t - u)) * f (t - u)) := by
  rw [← mul_assoc, ← Real.exp_add]
  congr 2
  ring

private theorem laplace_zero_of_superunit_finite_delays
    (a : ℕ → ℝ) (ha : ∀ n, 0 ≤ a n)
    (f : ℝ → ℝ) (hf : ∀ t, 0 ≤ f t)
    (hcausal : ∀ t, t < 0 → f t = 0)
    (hrenew : ∀ t, logarithmicWeightedDilation a f t ≤ f t)
    (σ : ℝ) (hint : Integrable (fun t => Real.exp (-σ * t) * f t))
    (U : ℕ) (hmass : 1 < ∑ n ∈ Finset.Icc 1 U,
      a n * Real.exp (-σ * Real.log n)) :
    f =ᵐ[volume] 0 := by
  let F : ℝ → ℝ := fun t => Real.exp (-σ * t) * f t
  let w : ℕ → ℝ := fun n => a n * Real.exp (-σ * Real.log n)
  have hF : Integrable F := hint
  have hF0 : ∀ t, 0 ≤ F t := fun t => mul_nonneg (Real.exp_pos _).le (hf t)
  have hterm (n : ℕ) : Integrable (fun t => w n * F (t - Real.log n)) :=
    (hF.comp_sub_right (Real.log n)).const_mul (w n)
  have hdom (t : ℝ) :
      (∑ n ∈ Finset.Icc 1 U, w n * F (t - Real.log n)) ≤ F t := by
    have h := mul_le_mul_of_nonneg_left
      ((finite_delay_sum_le_dilation a ha f hf hcausal U t).trans (hrenew t))
      (Real.exp_pos (-σ * t)).le
    rw [Finset.mul_sum] at h
    calc
      _ = ∑ n ∈ Finset.Icc 1 U,
          Real.exp (-σ * t) * (a n * f (t - Real.log n)) := by
        apply Finset.sum_congr rfl
        intro n _
        dsimp [w, F]
        rw [mul_assoc, ← laplace_delay_identity σ (Real.log n) t f]
        ring
      _ ≤ F t := h
  have hbound := integral_mono
    (integrable_finsetSum _ (fun n _ => hterm n)) hF hdom
  have heval :
      (∫ t : ℝ, ∑ n ∈ Finset.Icc 1 U, w n * F (t - Real.log n)) =
        (∑ n ∈ Finset.Icc 1 U, w n) * ∫ t : ℝ, F t := by
    rw [integral_finsetSum _ (fun n _ => hterm n), Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    rw [integral_const_mul, integral_sub_right_eq_self]
  rw [heval] at hbound
  have hI0 : 0 ≤ ∫ t : ℝ, F t := integral_nonneg hF0
  have hI : (∫ t : ℝ, F t) = 0 := by
    change 1 < ∑ n ∈ Finset.Icc 1 U, w n at hmass
    nlinarith
  have hzero := (integral_eq_zero_iff_of_nonneg hF0 hF).mp hI
  filter_upwards [hzero] with t ht
  exact (mul_eq_zero.mp ht).resolve_left (Real.exp_ne_zero _)

/-- Nonnegative causal profiles dominating the actual Euler renewal, in a
specified Laplace domain. The only regularity requirement is continuity. -/
def ccmEulerPositiveRenewalCone (P : ℕ) (σ : ℝ) : Set (ℝ → ℝ) :=
  {f | Continuous f ∧ (∀ t, t < 0 → f t = 0) ∧ (∀ t, 0 ≤ f t) ∧
    Integrable (fun t => Real.exp (-σ * t) * f t) ∧
    ∀ t, logarithmicWeightedDilation (ccmEulerRenewalKernel P) f t ≤ f t}

private theorem positiveRenewalCone_eq_zero_of_mass
    (P U : ℕ) (σ : ℝ)
    (hmass : 1 < ∑ n ∈ Finset.Icc 1 U,
      ccmEulerRenewalKernel P n * Real.exp (-σ * Real.log n)) :
    ccmEulerPositiveRenewalCone P σ = {0} := by
  ext f
  constructor
  · rintro ⟨hcont, hcausal, hf, hint, hrenew⟩
    have hae := laplace_zero_of_superunit_finite_delays
      (ccmEulerRenewalKernel P) (ccmEulerRenewalKernel_nonneg P)
      f hf hcausal hrenew σ hint U hmass
    exact Set.mem_singleton_iff.mpr (MeasureTheory.Measure.eq_of_ae_eq hae hcont continuous_zero)
  · intro hf
    have hf0 : f = 0 := Set.mem_singleton_iff.mp hf
    subst f
    refine ⟨continuous_zero, ?_, ?_, ?_, ?_⟩
    · simp
    · simp
    · simp
    · simp [logarithmicWeightedDilation]

private theorem renewal_laplace_mass_half (P U : ℕ) :
    (∑ n ∈ Finset.Icc 1 U,
      ccmEulerRenewalKernel P n * Real.exp (-(1 / 2 : ℝ) * Real.log n)) =
        ccmEulerRenewalCriticalMass P U := by
  unfold ccmEulerRenewalCriticalMass
  apply Finset.sum_congr rfl
  intro n hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
  have hexp : Real.exp (Real.log (n : ℝ) / 2) = Real.sqrt n := by
    rw [← Real.log_sqrt hnpos.le, Real.exp_log (Real.sqrt_pos.mpr hnpos)]
  rw [show -(1 / 2 : ℝ) * Real.log n = -(Real.log n / 2) by ring,
    Real.exp_neg, hexp, div_eq_mul_inv]

/-- For every positive Euler modulus, positive super-renewal has a trivial
critical Laplace domain. No sign or bound for the actual deficit is assumed. -/
theorem ccmEulerPositiveRenewalCone_half_eq_zero (P : ℕ) :
    ccmEulerPositiveRenewalCone (P + 1) (1 / 2) = {0} := by
  obtain ⟨U, hU⟩ := ccmEulerRenewalCriticalMass_unbounded P 1
  apply positiveRenewalCone_eq_zero_of_mass (P + 1) U (1 / 2)
  rwa [renewal_laplace_mass_half]

private theorem renewal_harmonic_mass_superunit (P : ℕ) :
    ∃ U : ℕ, 1 < ∑ n ∈ Finset.Icc 1 U, ccmEulerRenewalKernel (P + 1) n / n := by
  let r : ℕ := P + 2
  let φ : ℕ → ℕ := fun j => r * ((P + 1) * (j + 1) + 1)
  have hr : 0 < r := by dsimp [r]; omega
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  obtain ⟨N, hN⟩ := (Real.tendsto_sum_range_one_div_nat_succ_atTop.eventually
    (eventually_gt_atTop ((r : ℝ) ^ 2))).exists
  let U := r ^ 2 * (N + 1)
  let S := (Finset.range N).image φ
  have hφpos (j : ℕ) : 0 < φ j := by dsimp [φ]; positivity
  have hφle (j : ℕ) : φ j ≤ r ^ 2 * (j + 1) := by
    have h : (P + 1) * (j + 1) + 1 ≤ (P + 2) * (j + 1) := by nlinarith
    calc
      φ j ≤ r * (r * (j + 1)) := Nat.mul_le_mul_left r h
      _ = r ^ 2 * (j + 1) := by ring
  have hinj : Function.Injective φ := by
    intro i j hij
    have h := Nat.eq_of_mul_eq_mul_left hr hij
    have h' := Nat.eq_of_mul_eq_mul_left (Nat.succ_pos P) (Nat.add_right_cancel h)
    exact Nat.add_right_cancel h'
  have hsub : S ⊆ Finset.Icc 1 U := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
    refine Finset.mem_Icc.mpr ⟨hφpos j, (hφle j).trans ?_⟩
    exact Nat.mul_le_mul_left _ (by have := Finset.mem_range.mp hj; omega)
  have hcoeff (j : ℕ) : 1 ≤ ccmEulerRenewalKernel (P + 1) (φ j) := by
    have hrrough : ccmEulerRough (P + 1) r = 1 := by
      change (if 1 < r ∧ r.Coprime (P + 1) then (1 : ℝ) else 0) = 1
      apply if_pos
      constructor
      · dsimp [r]; omega
      · have h : ((P + 1) * 1 + 1).Coprime (P + 1) := by
          simpa only [Nat.coprime_mul_left_add_left] using Nat.coprime_one_left (P + 1)
        rw [show r = (P + 1) * 1 + 1 by dsimp [r]; omega]
        exact h
    have hmrough : ccmEulerRough (P + 1) ((P + 1) * (j + 1) + 1) = 1 := by
      apply if_pos
      constructor
      · nlinarith [Nat.mul_pos (Nat.succ_pos P) (Nat.succ_pos j)]
      · simpa only [Nat.coprime_mul_left_add_left] using Nat.coprime_one_left (P + 1)
    rw [ccmEulerRenewalKernel, pow_two, ArithmeticFunction.mul_apply]
    have hmem : (r, (P + 1) * (j + 1) + 1) ∈ (φ j).divisorsAntidiagonal :=
      Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, (hφpos j).ne'⟩
    have h := Finset.single_le_sum (s := (φ j).divisorsAntidiagonal)
      (f := fun ab => ccmEulerRough (P + 1) ab.1 * ccmEulerRough (P + 1) ab.2)
      (fun ab _ => mul_nonneg (ccmEulerRough_nonneg _ ab.1)
        (ccmEulerRough_nonneg _ ab.2)) hmem
    simpa only [hrrough, hmrough, one_mul] using h
  have hterm (j : ℕ) :
      1 / (r : ℝ) ^ 2 * (1 / ((j : ℝ) + 1)) ≤
        ccmEulerRenewalKernel (P + 1) (φ j) / (φ j : ℝ) := by
    have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
    have hφR : (0 : ℝ) < φ j := by exact_mod_cast hφpos j
    calc
      _ = 1 / ((r : ℝ) ^ 2 * ((j : ℝ) + 1)) := by field_simp
      _ ≤ 1 / (φ j : ℝ) := one_div_le_one_div_of_le hφR (by exact_mod_cast hφle j)
      _ ≤ _ := div_le_div_of_nonneg_right (hcoeff j) hφR.le
  refine ⟨U, ?_⟩
  calc
    1 < 1 / (r : ℝ) ^ 2 * (∑ j ∈ Finset.range N, (1 / ((j : ℝ) + 1))) := by
      have hmul := mul_lt_mul_of_pos_left hN (by positivity : 0 < 1 / (r : ℝ) ^ 2)
      have hc : 1 / (r : ℝ) ^ 2 * (r : ℝ) ^ 2 = 1 := by field_simp [hrR.ne']
      rwa [hc] at hmul
    _ = ∑ j ∈ Finset.range N, 1 / (r : ℝ) ^ 2 * (1 / ((j : ℝ) + 1)) := by
      rw [Finset.mul_sum]
    _ ≤ ∑ j ∈ Finset.range N, ccmEulerRenewalKernel (P + 1) (φ j) / (φ j : ℝ) :=
      Finset.sum_le_sum fun j _ => hterm j
    _ = ∑ n ∈ S, ccmEulerRenewalKernel (P + 1) n / (n : ℝ) :=
      (Finset.sum_image (f := fun n => ccmEulerRenewalKernel (P + 1) n / (n : ℝ))
        (fun _ _ _ _ h => hinj h)).symm
    _ ≤ ∑ n ∈ Finset.Icc 1 U, ccmEulerRenewalKernel (P + 1) n / (n : ℝ) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub
        (fun n _ _ => div_nonneg (ccmEulerRenewalKernel_nonneg _ _) (Nat.cast_nonneg _))

/-- A finite part of the actual positive kernel already has Laplace mass
greater than one at an exponent strictly greater than one. -/
theorem exists_ccmEulerRenewal_superunit_block_above_one (P : ℕ) :
    ∃ σ : ℝ, 1 < σ ∧ ∃ U : ℕ, 1 < ∑ n ∈ Finset.Icc 1 U,
      ccmEulerRenewalKernel (P + 1) n * Real.exp (-σ * Real.log n) := by
  obtain ⟨U, hU⟩ := renewal_harmonic_mass_superunit P
  let M : ℝ → ℝ := fun σ => ∑ n ∈ Finset.Icc 1 U,
    ccmEulerRenewalKernel (P + 1) n * Real.exp (-σ * Real.log n)
  have hM : Continuous M := by
    apply continuous_finsetSum
    intro n _
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_neg.mul continuous_const))
  have hM1 : 1 < M 1 := by
    have heq : M 1 = ∑ n ∈ Finset.Icc 1 U, ccmEulerRenewalKernel (P + 1) n / n := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnpos : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      simp only [neg_mul, one_mul, Real.exp_neg, Real.exp_log hnpos, div_eq_mul_inv]
    rwa [heq]
  have hnhds : {σ | 1 < M σ} ∈ 𝓝 (1 : ℝ) :=
    (isOpen_lt continuous_const hM).mem_nhds hM1
  obtain ⟨l, u, hlu, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hnhds
  let σ : ℝ := (1 + u) / 2
  have hσ : 1 < σ := by dsimp [σ]; linarith [hlu.2]
  have hmass : 1 < M σ := hsub ⟨lt_trans hlu.1 hσ, by dsimp [σ]; linarith [hlu.2]⟩
  exact ⟨σ, hσ, U, hmass⟩

/-- Even without continuity, every positive causal super-renewal profile
in this source-derived Laplace domain vanishes almost everywhere. -/
theorem exists_ccmEulerPositiveRenewal_ae_rigidity (P : ℕ) :
    ∃ σ : ℝ, 1 < σ ∧ ∀ f : ℝ → ℝ,
      (∀ t, 0 ≤ f t) → (∀ t, t < 0 → f t = 0) →
      (∀ t, logarithmicWeightedDilation (ccmEulerRenewalKernel (P + 1)) f t ≤ f t) →
      Integrable (fun t => Real.exp (-σ * t) * f t) → f =ᵐ[volume] 0 := by
  obtain ⟨σ, hσ, U, hmass⟩ := exists_ccmEulerRenewal_superunit_block_above_one P
  refine ⟨σ, hσ, fun f hf hcausal hrenew hint => ?_⟩
  exact laplace_zero_of_superunit_finite_delays
    _ (ccmEulerRenewalKernel_nonneg (P + 1)) f hf hcausal hrenew σ hint U hmass

/-- Positive super-renewal is rigid in a Laplace domain strictly beyond
exponent one. Its exponent is fixed by the actual arithmetic kernel. -/
theorem exists_ccmEulerPositiveRenewalCone_above_one_eq_zero (P : ℕ) :
    ∃ σ : ℝ, 1 < σ ∧ ccmEulerPositiveRenewalCone (P + 1) σ = {0} := by
  obtain ⟨σ, hσ, U, hmass⟩ := exists_ccmEulerRenewal_superunit_block_above_one P
  exact ⟨σ, hσ, positiveRenewalCone_eq_zero_of_mass (P + 1) U σ hmass⟩

private theorem integrable_laplace_of_causal_exp_bound
    (f : ℝ → ℝ) (hcont : Continuous f)
    (hcausal : ∀ t, t < 0 → f t = 0) (hf : ∀ t, 0 ≤ f t)
    (C σ : ℝ) (hσ : 1 < σ) (hbound : ∀ t, 0 ≤ t → f t ≤ C * Real.exp t) :
    Integrable (fun t => Real.exp (-σ * t) * f t) := by
  have hgOn : IntegrableOn (fun t : ℝ => C * Real.exp ((1 - σ) * t)) (Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr
      ((integrableOn_exp_mul_Ioi (by linarith : 1 - σ < 0) 0).const_mul C)
  have hg : Integrable ((Ici (0 : ℝ)).indicator
      (fun t : ℝ => C * Real.exp ((1 - σ) * t))) :=
    (integrable_indicator_iff measurableSet_Ici).mpr hgOn
  apply hg.mono'
    ((Real.continuous_exp.comp (continuous_const.mul continuous_id)).mul hcont).aestronglyMeasurable
  apply Eventually.of_forall
  intro t
  change ‖Real.exp (-σ * t) * f t‖ ≤
    (Ici (0 : ℝ)).indicator (fun t => C * Real.exp ((1 - σ) * t)) t
  by_cases ht : t ∈ Ici (0 : ℝ)
  · rw [Set.indicator_of_mem ht, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.exp_pos _).le (hf t))]
    calc
      Real.exp (-σ * t) * f t ≤ Real.exp (-σ * t) * (C * Real.exp t) :=
        mul_le_mul_of_nonneg_left (hbound t ht) (Real.exp_pos _).le
      _ = C * (Real.exp (-σ * t) * Real.exp t) := by ring
      _ = C * Real.exp ((1 - σ) * t) := by
        rw [← Real.exp_add]
        congr 2
        ring
  · rw [Set.indicator_of_notMem ht, hcausal t (lt_of_not_ge ht), mul_zero, norm_zero]

/-- Positive, causal Euler super-renewal profiles with an ordinary exponential
budget. The growth constant is existential and independent of time. -/
def ccmEulerPositiveExponentialRenewalCone (P : ℕ) : Set (ℝ → ℝ) :=
  {f | Continuous f ∧ (∀ t, t < 0 → f t = 0) ∧ (∀ t, 0 ≤ f t) ∧
    (∃ C : ℝ, ∀ t, 0 ≤ t → f t ≤ C * Real.exp t) ∧
    ∀ t, logarithmicWeightedDilation (ccmEulerRenewalKernel P) f t ≤ f t}

/-- Complete rigidity of the positive comparison-error cone at the ordinary
exponential scale, for each finite positive Euler modulus. -/
theorem ccmEulerPositiveExponentialRenewalCone_eq_zero (P : ℕ) :
    ccmEulerPositiveExponentialRenewalCone (P + 1) = {0} := by
  obtain ⟨σ, hσ, hcone⟩ := exists_ccmEulerPositiveRenewalCone_above_one_eq_zero P
  ext f
  constructor
  · rintro ⟨hcont, hcausal, hf, ⟨C, hbound⟩, hrenew⟩
    have hm : f ∈ ccmEulerPositiveRenewalCone (P + 1) σ :=
      ⟨hcont, hcausal, hf,
        integrable_laplace_of_causal_exp_bound f hcont hcausal hf C σ hσ hbound, hrenew⟩
    rwa [hcone] at hm
  · intro hf
    have hf0 : f = 0 := Set.mem_singleton_iff.mp hf
    subst f
    refine ⟨continuous_zero, ?_, ?_, ⟨0, ?_⟩, ?_⟩ <;>
      simp [logarithmicWeightedDilation]

end RHTower
