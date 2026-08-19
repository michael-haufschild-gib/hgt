import GaloisForLFunctions.RHTower.Sieve.Section4Block

/-!
# The frequency scaling on a measurable set

`Sieve/LogPolyRestrict` converts a mean square over a symmetric *interval* in the Gallagher variable
into one in the Dirichlet variable.  The exceptional case of exposé §4 integrates over a measurable
subset of that interval, so the change of variables is needed there too — together with the
corresponding scaling of Lebesgue measure, which is what Lemma 2.5 controls.

The exceptional set in the Gallagher variable is exactly the preimage of the exceptional set in the
Dirichlet variable, so no set-theoretic work is needed downstream.
-/

namespace RHTower.Sieve

open Finset MeasureTheory

noncomputable section

/-- The Gallagher polynomial over a subset, in the `finCoeff` normal form. -/
theorem logPoly_subset_eq_dirPoly_finCoeff (a : ℕ → ℂ) {S : Finset ℕ} {N : ℕ}
    (hS : S ⊆ Finset.Icc 1 N) (w : ℝ) :
    logPoly a S w = dirPoly N (finCoeff S a N) (2 * Real.pi * w) :=
  logPoly_subset_eq_dirPoly a hS w

/-- **The change of variables on a measurable set.** -/
theorem setIntegral_comp_mul_left (g : ℝ → ℝ) (hg : Continuous g) {S : Set ℝ}
    (hS : MeasurableSet S) {c : ℝ} (hc : 0 < c) :
    (∫ w in (fun v : ℝ => c * v) ⁻¹' S, g (c * w)) = c⁻¹ * ∫ t in S, g t := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have hφ : Measurable (fun v : ℝ => c * v) := measurable_const_mul c
  have hmap : Measure.map (fun v : ℝ => c * v) (volume.restrict ((fun v : ℝ => c * v) ⁻¹' S))
      = (Measure.map (fun v : ℝ => c * v) volume).restrict S := (Measure.restrict_map hφ hS).symm
  have hvol : Measure.map (fun v : ℝ => c * v) volume = ENNReal.ofReal |c⁻¹| • volume :=
    Real.map_volume_mul_left hcne
  have hint : (∫ t : ℝ, g t ∂(Measure.map (fun v : ℝ => c * v)
      (volume.restrict ((fun v : ℝ => c * v) ⁻¹' S))))
      = ∫ w in (fun v : ℝ => c * v) ⁻¹' S, g (c * w) :=
    integral_map hφ.aemeasurable hg.aestronglyMeasurable
  rw [← hint, hmap, hvol, Measure.restrict_smul, integral_smul_measure,
    abs_of_pos (by positivity : (0 : ℝ) < c⁻¹), ENNReal.toReal_ofReal (by positivity),
    smul_eq_mul]

/-- **The measure of a scaled preimage.** -/
theorem volume_real_preimage_mul_left {S : Set ℝ} {c : ℝ} (hc : 0 < c) :
    volume.real ((fun v : ℝ => c * v) ⁻¹' S) = c⁻¹ * volume.real S := by
  have hcne : c ≠ 0 := ne_of_gt hc
  have h := Real.volume_preimage_mul_left hcne S
  rw [Measure.real, Measure.real, h, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (by positivity : (0:ℝ) ≤ |c⁻¹|), abs_of_pos (by positivity : (0:ℝ) < c⁻¹)]

/-- **The mean square of a Gallagher polynomial over a measurable set, in the Dirichlet
variable.** -/
theorem setIntegral_normSq_logPoly_eq (a : ℕ → ℂ) {D : Finset ℕ} {N : ℕ}
    (hD : D ⊆ Finset.Icc 1 N) {S : Set ℝ} (hS : MeasurableSet S) :
    (∫ w in (fun v : ℝ => 2 * Real.pi * v) ⁻¹' S, ‖logPoly a D w‖ ^ 2)
      = (2 * Real.pi)⁻¹ * ∫ t in S, ‖dirPoly N (finCoeff D a N) t‖ ^ 2 := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  have hcont : Continuous fun t : ℝ => ‖dirPoly N (finCoeff D a N) t‖ ^ 2 :=
    (((continuous_dirPoly N (finCoeff D a N)).norm).pow 2)
  have hpt : ∀ w : ℝ, ‖logPoly a D w‖ ^ 2
      = ‖dirPoly N (finCoeff D a N) (2 * Real.pi * w)‖ ^ 2 := by
    intro w
    rw [logPoly_subset_eq_dirPoly_finCoeff a hD w]
  have hmeas : MeasurableSet ((fun v : ℝ => 2 * Real.pi * v) ⁻¹' S) :=
    (measurable_const_mul (2 * Real.pi)) hS
  rw [MeasureTheory.setIntegral_congr_fun hmeas fun w _ => hpt w]
  exact setIntegral_comp_mul_left _ hcont hS hpi

/-- **The exceptional set in the Gallagher variable is the preimage of the Dirichlet one.** -/
theorem exceptional_preimage (a : ℕ → ℂ) {B : Finset ℕ} {NA : ℕ} (hB : B ⊆ Finset.Icc 1 NA)
    (W V : ℝ) :
    {w : ℝ | w ∈ Set.Icc (-W) W ∧ V ≤ ‖logPoly a B w‖}
      = (fun v : ℝ => 2 * Real.pi * v) ⁻¹' (blockExceptional B a NA (2 * Real.pi * W) V) := by
  have hpi : (0 : ℝ) < 2 * Real.pi := by positivity
  ext w
  simp only [Set.mem_setOf_eq, Set.mem_preimage, blockExceptional, Set.mem_setOf_eq,
    Set.mem_Icc]
  constructor
  · rintro ⟨hw, hV⟩
    refine ⟨⟨by nlinarith [hw.1], by nlinarith [hw.2]⟩, ?_⟩
    rw [← logPoly_subset_eq_dirPoly_finCoeff a hB w]
    exact hV
  · rintro ⟨⟨h1, h2⟩, hV⟩
    refine ⟨⟨by nlinarith, by nlinarith⟩, ?_⟩
    rw [logPoly_subset_eq_dirPoly_finCoeff a hB w]
    exact hV

/-! ## Halász–Montgomery for a Gallagher polynomial over a measurable set -/

/-- The energy of a restricted coefficient family. -/
theorem sum_normSq_finCoeff_le {D : Finset ℕ} {N : ℕ} {a : ℕ → ℂ} {Ω : ℝ} (hΩ : 0 ≤ Ω)
    (ha : ∀ n, ‖a n‖ ≤ Ω) :
    (∑ n : Fin N, ‖finCoeff D a N n‖ ^ 2) ≤ Ω ^ 2 * (D.card : ℝ) := by
  classical
  have hterm : ∀ n : Fin N, ‖finCoeff D a N n‖ ^ 2
      ≤ Ω ^ 2 * (if ((n : ℕ) + 1) ∈ D then (1 : ℝ) else 0) := by
    intro n
    rw [finCoeff, restrictCoeff]
    by_cases h : ((n : ℕ) + 1) ∈ D
    · rw [if_pos h, if_pos h, mul_one]
      have := ha ((n : ℕ) + 1)
      nlinarith [norm_nonneg (a ((n : ℕ) + 1)), hΩ]
    · rw [if_neg h, if_neg h]
      simp
  refine (Finset.sum_le_sum fun n _ => hterm n).trans ?_
  rw [← Finset.mul_sum, Finset.sum_boole]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  have hcard : ((Finset.univ.filter (fun n : Fin N => ((n : ℕ) + 1) ∈ D)).card : ℕ) ≤ D.card := by
    refine Finset.card_le_card_of_injOn (fun n : Fin N => (n : ℕ) + 1) ?_ ?_
    · intro n hn
      exact (Finset.mem_filter.1 hn).2
    · intro x _ y _ hxy
      have h : (x : ℕ) + 1 = (y : ℕ) + 1 := hxy
      exact Fin.ext (by omega)
  exact_mod_cast hcard

/-- **Lemma 2.6 for a Gallagher polynomial over a measurable set.** -/
theorem setIntegral_normSq_logPoly_le_HM (a : ℕ → ℂ) {D : Finset ℕ} {N : ℕ} (hN : 1 ≤ N)
    (hD : D ⊆ Finset.Icc 1 N) {S : Set ℝ} (hS : MeasurableSet S) {T : ℝ}
    (hSs : S ⊆ Set.Icc (-T) T) {Ω : ℝ} (hΩ : 0 ≤ Ω) (ha : ∀ n, ‖a n‖ ≤ Ω) :
    (∫ w in (fun v : ℝ => 2 * Real.pi * v) ⁻¹' S, ‖logPoly a D w‖ ^ 2)
      ≤ (2 * Real.pi)⁻¹
        * ((2 * (N : ℝ)
            + (((Nat.log 2 N : ℝ) + 1) * (214 * Real.sqrt (2 * T)) + 3072 * (N : ℝ))
              * volume.real S) * (Ω ^ 2 * (D.card : ℝ))) := by
  classical
  rw [setIntegral_normSq_logPoly_eq a hD hS]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  refine (setIntegral_normSq_dirPoly_le_explicit hN (finCoeff D a N) hS hSs).trans ?_
  have hvol : (0 : ℝ) ≤ volume.real S := ENNReal.toReal_nonneg
  have hNR : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg _
  have hlog0 : (0 : ℝ) ≤ (Nat.log 2 N : ℝ) + 1 := by
    have : (0 : ℝ) ≤ (Nat.log 2 N : ℝ) := Nat.cast_nonneg _
    linarith
  have hsqT : (0 : ℝ) ≤ Real.sqrt (2 * T) := Real.sqrt_nonneg _
  have hC0 : (0 : ℝ) ≤ ((Nat.log 2 N : ℝ) + 1) * (214 * Real.sqrt (2 * T)) + 3072 * (N : ℝ) := by
    nlinarith [hlog0, hsqT, hNR]
  have hfac : (0 : ℝ) ≤ 2 * (N : ℝ)
      + (((Nat.log 2 N : ℝ) + 1) * (214 * Real.sqrt (2 * T)) + 3072 * (N : ℝ))
        * volume.real S := by nlinarith [hC0, hvol, hNR]
  exact mul_le_mul_of_nonneg_left (sum_normSq_finCoeff_le hΩ ha) hfac

end

end RHTower.Sieve
