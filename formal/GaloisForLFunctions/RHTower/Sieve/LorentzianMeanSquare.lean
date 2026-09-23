import GaloisForLFunctions.RHTower.Sieve.GallagherAlmostDiagonal
import GaloisForLFunctions.RHTower.Sieve.GallagherDyadicTail

/-!
# The Lorentzian-weighted mean square of a Dirichlet polynomial

The weight attached to a vertical line by the sharp Perron kernel is `1/|s|`, so the quantity that
governs a mean value is the Lorentzian-weighted mean square

`∫_ℝ ‖∑_n a_n n^{2πiw}‖² dw/(1+w²)`.

Cutting the frequency line into the unit block and dyadic annuli, and paying each piece with the
almost-diagonal mean value theorem at the matching window length `δ = 1/(2πT)`, gives a bound with no
parameters at all:

`∫_ℝ ‖∑_n a_n n^{2πiw}‖² dw/(1+w²) ≤ (25π/2) ∑_n ‖a_n‖² · #{m : |log n - log m| < 1/(2π)}`.

Each annulus contributes `4^{-k}` from the weight against `2^k` from the mean value theorem, so the
dyadic sum is geometric: the frequency line is paid in full, and the only arithmetic left is the
unit-scale neighbour count of the support.
-/

noncomputable section

namespace RHTower.Sieve

open MeasureTheory Set Finset

/-- The neighbour count is monotone in the window length. -/
theorem logNeighbourCount_mono (s : Finset ℕ) {δ₁ δ₂ : ℝ} (h : δ₁ ≤ δ₂) (n : ℕ) :
    logNeighbourCount s δ₁ n ≤ logNeighbourCount s δ₂ n := by
  classical
  rw [logNeighbourCount, logNeighbourCount]
  refine Finset.card_le_card fun m hm => ?_
  rw [Finset.mem_filter] at hm ⊢
  exact ⟨hm.1, lt_of_lt_of_le hm.2 h⟩

/-- The squared modulus of the polynomial is continuous. -/
theorem continuous_normSq_logPoly (a : ℕ → ℂ) (s : Finset ℕ) :
    Continuous fun w : ℝ => ‖logPoly a s w‖ ^ (2 : ℕ) :=
  ((continuous_logPoly a s).norm).pow 2

/-- **The mean square over a symmetric block, against the unit-scale count.**  The mean value theorem
at the matching window length `δ = 1/(2πT)`, with the count relaxed to window length `1/(2π)`. -/
theorem integral_Icc_normSq_logPoly_le_unit_count (a : ℕ → ℂ) (s : Finset ℕ) {T : ℝ} (hT : 1 ≤ T) :
    (∫ w in Set.Icc (-T) T, ‖logPoly a s w‖ ^ (2 : ℕ))
      ≤ (5 * Real.pi / 2) * T
          * ∑ n ∈ s, (logNeighbourCount s (1 / (2 * Real.pi)) n : ℝ) * ‖a n‖ ^ (2 : ℕ) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hT0 : (0 : ℝ) < T := lt_of_lt_of_le zero_lt_one hT
  have hδ : 0 < 1 / (2 * Real.pi * T) := by positivity
  have hWδ : 2 * Real.pi * (1 / (2 * Real.pi * T)) * T ≤ 1 := by
    have hne : (2 : ℝ) * Real.pi * T ≠ 0 := by positivity
    rw [show 2 * Real.pi * (1 / (2 * Real.pi * T)) * T = (2 * Real.pi * T) / (2 * Real.pi * T) by
      ring, div_self hne]
  have h := integral_Icc_normSq_logPoly_le_count a s hδ hWδ
  have hcoef : (5 : ℝ) / (4 * (1 / (2 * Real.pi * T))) = (5 * Real.pi / 2) * T := by
    field_simp
    ring
  rw [hcoef] at h
  refine h.trans (mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun n _ => ?_) (by positivity))
  have hle : (1 : ℝ) / (2 * Real.pi * T) ≤ 1 / (2 * Real.pi) := by
    refine one_div_le_one_div_of_le (by positivity) ?_
    calc (2 : ℝ) * Real.pi = 2 * Real.pi * 1 := by ring
      _ ≤ 2 * Real.pi * T := by
          exact mul_le_mul_of_nonneg_left hT (by positivity)
  have hcount : (logNeighbourCount s (1 / (2 * Real.pi * T)) n : ℝ)
      ≤ (logNeighbourCount s (1 / (2 * Real.pi)) n : ℝ) := by
    exact_mod_cast logNeighbourCount_mono s hle n
  exact mul_le_mul_of_nonneg_right hcount (by positivity)

/-- The Lorentzian-weighted mean square is integrable: the polynomial is bounded. -/
theorem integrable_lorentz_normSq_logPoly (a : ℕ → ℂ) (s : Finset ℕ) :
    Integrable fun w : ℝ => ‖logPoly a s w‖ ^ (2 : ℕ) / (1 + w ^ (2 : ℕ)) := by
  have hM : ∀ w : ℝ, ‖logPoly a s w‖ ^ (2 : ℕ) ≤ (∑ n ∈ s, ‖a n‖) ^ (2 : ℕ) := fun w =>
    pow_le_pow_left₀ (norm_nonneg _) (norm_logPoly_le a s w) 2
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul ((∑ n ∈ s, ‖a n‖) ^ (2 : ℕ))) ?_ ?_
  · refine Continuous.aestronglyMeasurable ?_
    exact (continuous_normSq_logPoly a s).div (by fun_prop) fun w => by positivity
  · filter_upwards with w
    have hden : (0 : ℝ) < 1 + w ^ (2 : ℕ) := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ hden]
    have hcalc : (∑ n ∈ s, ‖a n‖) ^ (2 : ℕ) * (1 + w ^ (2 : ℕ))⁻¹ * (1 + w ^ (2 : ℕ))
        = (∑ n ∈ s, ‖a n‖) ^ (2 : ℕ) := by
      field_simp
    rw [hcalc]
    exact hM w

/-- Each dyadic annulus of frequencies is paid geometrically. -/
theorem integral_dyadicAnnulus_lorentz_le (a : ℕ → ℂ) (s : Finset ℕ) (k : ℕ) :
    (∫ w in dyadicAnnulus 1 k, ‖logPoly a s w‖ ^ (2 : ℕ) / (1 + w ^ (2 : ℕ)))
      ≤ 5 * Real.pi
          * (∑ n ∈ s, (logNeighbourCount s (1 / (2 * Real.pi)) n : ℝ) * ‖a n‖ ^ (2 : ℕ))
          * (1 / 2) ^ k := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hint := integrable_lorentz_normSq_logPoly a s
  have hcontI : IntegrableOn (fun w : ℝ => ‖logPoly a s w‖ ^ (2 : ℕ))
      (Set.Icc (-(2 ^ (k + 1) : ℝ)) (2 ^ (k + 1) : ℝ)) :=
    (continuous_normSq_logPoly a s).continuousOn.integrableOn_compact isCompact_Icc
  have hsub : dyadicAnnulus 1 k ⊆ Set.Icc (-(2 ^ (k + 1) : ℝ)) (2 ^ (k + 1) : ℝ) := by
    intro w hw
    have h2 : |w| < 2 ^ (k + 1) * 1 := hw.2
    rw [mul_one] at h2
    rw [Set.mem_Icc]
    have habs := abs_lt.mp h2
    exact ⟨habs.1.le, habs.2.le⟩
  have h4pos : (0 : ℝ) < (4 : ℝ) ^ k := by positivity
  -- the weight is at most `4^{-k}` on the annulus
  have hweight : ∀ w ∈ dyadicAnnulus 1 k,
      ‖logPoly a s w‖ ^ (2 : ℕ) / (1 + w ^ (2 : ℕ))
        ≤ ((1 : ℝ) / 4 ^ k) * ‖logPoly a s w‖ ^ (2 : ℕ) := by
    intro w hw
    have hlow : (2 : ℝ) ^ k * 1 ≤ |w| := hw.1
    rw [mul_one] at hlow
    have h0 : (0 : ℝ) ≤ (2 : ℝ) ^ k := by positivity
    have hsq : ((2 : ℝ) ^ k) ^ (2 : ℕ) ≤ w ^ (2 : ℕ) := by
      calc ((2 : ℝ) ^ k) ^ (2 : ℕ) ≤ |w| ^ (2 : ℕ) := by nlinarith [hlow, h0, abs_nonneg w]
        _ = w ^ (2 : ℕ) := sq_abs w
    have hpow : ((2 : ℝ) ^ k) ^ (2 : ℕ) = (4 : ℝ) ^ k := by
      rw [← pow_mul, show k * 2 = 2 * k by ring, pow_mul]
      norm_num
    have h4 : ((4 : ℝ) ^ k) ≤ 1 + w ^ (2 : ℕ) := by nlinarith [hsq, hpow]
    have hnum : (0 : ℝ) ≤ ‖logPoly a s w‖ ^ (2 : ℕ) := by positivity
    have hden : (0 : ℝ) < 1 + w ^ (2 : ℕ) := by positivity
    rw [div_le_iff₀ hden]
    have hstep : ‖logPoly a s w‖ ^ (2 : ℕ)
        = (1 / 4 ^ k) * ‖logPoly a s w‖ ^ (2 : ℕ) * (4 ^ k) := by
      field_simp
    calc ‖logPoly a s w‖ ^ (2 : ℕ)
        = (1 / 4 ^ k) * ‖logPoly a s w‖ ^ (2 : ℕ) * (4 ^ k) := hstep
      _ ≤ (1 / 4 ^ k) * ‖logPoly a s w‖ ^ (2 : ℕ) * (1 + w ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left h4 (by positivity)
  have hstep1 : (∫ w in dyadicAnnulus 1 k, ‖logPoly a s w‖ ^ (2 : ℕ) / (1 + w ^ (2 : ℕ)))
      ≤ ∫ w in dyadicAnnulus 1 k, ((1 : ℝ) / 4 ^ k) * ‖logPoly a s w‖ ^ (2 : ℕ) := by
    refine setIntegral_mono_on hint.integrableOn ?_ (measurableSet_dyadicAnnulus 1 k) hweight
    exact ((hcontI.mono_set hsub).const_mul _)
  have hstep2 : (∫ w in dyadicAnnulus 1 k, ((1 : ℝ) / 4 ^ k) * ‖logPoly a s w‖ ^ (2 : ℕ))
      ≤ ((1 : ℝ) / 4 ^ k) * ∫ w in Set.Icc (-(2 ^ (k + 1) : ℝ)) (2 ^ (k + 1) : ℝ),
          ‖logPoly a s w‖ ^ (2 : ℕ) := by
    rw [MeasureTheory.integral_const_mul]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    refine setIntegral_mono_set hcontI ?_ ?_
    · filter_upwards with w
      positivity
    · exact LE.le.eventuallyLE hsub
  have hTge : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 1) := one_le_pow₀ one_le_two
  have hblock := integral_Icc_normSq_logPoly_le_unit_count a s hTge
  have hCnn : (0 : ℝ) ≤ ∑ n ∈ s, (logNeighbourCount s (1 / (2 * Real.pi)) n : ℝ) * ‖a n‖ ^ (2 : ℕ) :=
    Finset.sum_nonneg fun n _ => by positivity
  have hchain : (∫ w in dyadicAnnulus 1 k, ‖logPoly a s w‖ ^ (2 : ℕ) / (1 + w ^ (2 : ℕ)))
      ≤ ((1 : ℝ) / 4 ^ k) * ((5 * Real.pi / 2) * (2 : ℝ) ^ (k + 1)
          * ∑ n ∈ s, (logNeighbourCount s (1 / (2 * Real.pi)) n : ℝ) * ‖a n‖ ^ (2 : ℕ)) := by
    refine le_trans (le_trans hstep1 hstep2) ?_
    exact mul_le_mul_of_nonneg_left hblock (by positivity)
  refine hchain.trans (le_of_eq ?_)
  have hval : ((1 : ℝ) / 4 ^ k) * ((5 * Real.pi / 2) * (2 : ℝ) ^ (k + 1))
      = 5 * Real.pi * (1 / 2) ^ k := by
    rw [show (4 : ℝ) ^ k = (2 : ℝ) ^ k * (2 : ℝ) ^ k by
      rw [← pow_add, show k + k = 2 * k by ring, pow_mul]; norm_num,
      pow_succ, one_div, one_div, inv_pow]
    have h2 : ((2 : ℝ) ^ k) ≠ 0 := by positivity
    field_simp
  calc ((1 : ℝ) / 4 ^ k) * ((5 * Real.pi / 2) * (2 : ℝ) ^ (k + 1)
        * ∑ n ∈ s, (logNeighbourCount s (1 / (2 * Real.pi)) n : ℝ) * ‖a n‖ ^ (2 : ℕ))
      = (((1 : ℝ) / 4 ^ k) * ((5 * Real.pi / 2) * (2 : ℝ) ^ (k + 1)))
          * ∑ n ∈ s, (logNeighbourCount s (1 / (2 * Real.pi)) n : ℝ) * ‖a n‖ ^ (2 : ℕ) := by ring
    _ = 5 * Real.pi
          * (∑ n ∈ s, (logNeighbourCount s (1 / (2 * Real.pi)) n : ℝ) * ‖a n‖ ^ (2 : ℕ))
          * (1 / 2) ^ k := by rw [hval]; ring

/-- **The Lorentzian-weighted mean value theorem.**  No parameters: the whole frequency line is paid by
the unit-scale neighbour count of the support. -/
theorem integral_lorentz_normSq_logPoly_le_count (a : ℕ → ℂ) (s : Finset ℕ) :
    (∫ w : ℝ, ‖logPoly a s w‖ ^ (2 : ℕ) / (1 + w ^ (2 : ℕ)))
      ≤ (25 * Real.pi / 2)
          * ∑ n ∈ s, (logNeighbourCount s (1 / (2 * Real.pi)) n : ℝ) * ‖a n‖ ^ (2 : ℕ) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  set C : ℝ := ∑ n ∈ s, (logNeighbourCount s (1 / (2 * Real.pi)) n : ℝ) * ‖a n‖ ^ (2 : ℕ) with hCdef
  have hC0 : 0 ≤ C := by
    rw [hCdef]
    exact Finset.sum_nonneg fun n _ => by positivity
  have hint := integrable_lorentz_normSq_logPoly a s
  have hfnn : ∀ w : ℝ, 0 ≤ ‖logPoly a s w‖ ^ (2 : ℕ) / (1 + w ^ (2 : ℕ)) := fun w => by positivity
  -- split at the unit block
  have hmeas : MeasurableSet {w : ℝ | (1 : ℝ) ≤ |w|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  have hsplit := integral_add_compl hmeas hint
  -- the far region, dyadically
  have hfar : (∫ w in {w : ℝ | (1 : ℝ) ≤ |w|}, ‖logPoly a s w‖ ^ (2 : ℕ) / (1 + w ^ (2 : ℕ)))
      ≤ 10 * Real.pi * C := by
    have hunion : {w : ℝ | (1 : ℝ) ≤ |w|} = ⋃ k : ℕ, dyadicAnnulus 1 k :=
      (iUnion_dyadicAnnulus one_pos).symm
    have hsum := hasSum_integral_iUnion (f := fun w : ℝ => ‖logPoly a s w‖ ^ (2 : ℕ) / (1 + w ^ (2 : ℕ)))
      (measurableSet_dyadicAnnulus 1) (pairwise_disjoint_dyadicAnnulus one_pos)
      (by rw [← hunion]; exact hint.integrableOn)
    have hgeo : HasSum (fun k : ℕ => 5 * Real.pi * C * (1 / 2 : ℝ) ^ k) (10 * Real.pi * C) := by
      have h := hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
      have h2 := h.mul_left (5 * Real.pi * C)
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num] at h2
      have hval : 5 * Real.pi * C * (1 / 2 : ℝ)⁻¹ = 10 * Real.pi * C := by
        rw [show (1 / 2 : ℝ)⁻¹ = 2 by norm_num]
        ring
      rw [hval] at h2
      exact h2
    rw [hunion, ← hsum.tsum_eq]
    refine le_trans (Summable.tsum_mono hsum.summable hgeo.summable
      (fun k => integral_dyadicAnnulus_lorentz_le a s k)) ?_
    exact le_of_eq hgeo.tsum_eq
  -- the central block
  have hcentral : (∫ w in {w : ℝ | (1 : ℝ) ≤ |w|}ᶜ, ‖logPoly a s w‖ ^ (2 : ℕ) / (1 + w ^ (2 : ℕ)))
      ≤ (5 * Real.pi / 2) * C := by
    have hsub : {w : ℝ | (1 : ℝ) ≤ |w|}ᶜ ⊆ Set.Icc (-1 : ℝ) 1 := by
      intro w hw
      rw [Set.mem_compl_iff, Set.mem_setOf_eq, not_le] at hw
      rw [Set.mem_Icc]
      have habs := abs_lt.mp hw
      exact ⟨habs.1.le, habs.2.le⟩
    have hIcc : IntegrableOn (fun w : ℝ => ‖logPoly a s w‖ ^ (2 : ℕ) / (1 + w ^ (2 : ℕ)))
        (Set.Icc (-1 : ℝ) 1) := hint.integrableOn
    have hmono : (∫ w in {w : ℝ | (1 : ℝ) ≤ |w|}ᶜ, ‖logPoly a s w‖ ^ (2 : ℕ) / (1 + w ^ (2 : ℕ)))
        ≤ ∫ w in Set.Icc (-1 : ℝ) 1, ‖logPoly a s w‖ ^ (2 : ℕ) / (1 + w ^ (2 : ℕ)) := by
      refine setIntegral_mono_set hIcc ?_ (LE.le.eventuallyLE hsub)
      filter_upwards with w
      exact hfnn w
    have hdrop : (∫ w in Set.Icc (-1 : ℝ) 1, ‖logPoly a s w‖ ^ (2 : ℕ) / (1 + w ^ (2 : ℕ)))
        ≤ ∫ w in Set.Icc (-1 : ℝ) 1, ‖logPoly a s w‖ ^ (2 : ℕ) := by
      refine setIntegral_mono_on hIcc
        ((continuous_normSq_logPoly a s).continuousOn.integrableOn_compact isCompact_Icc)
        measurableSet_Icc fun w _ => ?_
      have hden : (1 : ℝ) ≤ 1 + w ^ (2 : ℕ) := by nlinarith [sq_nonneg w]
      have hnum : (0 : ℝ) ≤ ‖logPoly a s w‖ ^ (2 : ℕ) := by positivity
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 1 + w ^ (2 : ℕ))]
      nlinarith [hnum, hden]
    have hb := integral_Icc_normSq_logPoly_le_unit_count a s (le_refl (1 : ℝ))
    rw [mul_one] at hb
    linarith [hmono, hdrop, hb]
  linarith [hsplit.symm.le, hsplit.le, hfar, hcentral]

end RHTower.Sieve

end
