import GaloisForLFunctions.RHTower.ChiDualSpatialMeanSquare
import GaloisForLFunctions.RHTower.ZetaChiDualNormalizedResonatorMean

/-!
# Full dual-block profiles under physical resonators

The actual finite Dirichlet resonator has a cardinality-energy envelope.
Combining it with the complete spatial mean-square profile bounds the weighted
error while retaining all coefficients and transition heights. On the existing
growing narrow-frequency schedule, the proved physical mass lower bound gives
normalized weighted error O(k^-3), uniformly in every nonzero coefficient family.
-/

open Complex Set Filter Topology MeasureTheory
open scoped BigOperators
noncomputable section
namespace RHTower

/-- The actual physical resonator obeys the full cardinality-energy envelope. -/
theorem norm_zetaChiDualResonator_sq_le (S : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) :
    ‖zetaChiDualResonator S c t‖ ^ 2 ≤ (S.card : ℝ) * ∑ a ∈ S, ‖c a‖ ^ 2 := by
  have hn : ‖zetaChiDualResonator S c t‖ ≤ ∑ a ∈ S, ‖c a‖ := by
    unfold zetaChiDualResonator
    apply (norm_sum_le _ _).trans
    apply Finset.sum_le_sum
    intro a ha
    rw [norm_mul, norm_bourgainOscillation, mul_one]
  have hcs : (∑ a ∈ S, ‖c a‖) ^ 2 ≤ (S.card : ℝ) * ∑ a ∈ S, ‖c a‖ ^ 2 := by
    simpa only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] using
      Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun a => ‖c a‖)
  exact (pow_le_pow_left₀ (norm_nonneg _) hn 2).trans hcs

private theorem continuous_zetaChiDualResonator_sq (S : Finset ℕ) (c : ℕ → ℂ) :
    Continuous (fun t => ‖zetaChiDualResonator S c t‖ ^ 2) := by
  have hD : Continuous (zetaChiDualResonator S c) := by
    unfold zetaChiDualResonator
    apply continuous_finsetSum
    intro a _
    unfold bourgainOscillation
    fun_prop
  exact hD.norm.pow 2

/-- Full spatial profile error under every finite physical Dirichlet resonator.
All coefficients and physical transition heights are retained. -/
theorem exists_chiDual_integer_block_resonator_profile
    (z : ℂ) {r : ℝ} (hr : 0 ≤ r) (hz0 : 1 / 2 ≤ z.re - r) (hz1 : z.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ m : ℕ in atTop, ∀ s ∈ Metric.closedBall z r,
      ∀ A B : ℕ, (m : ℝ) ^ 10 / 5 ≤ A → (B : ℝ) ≤ 6 * (m : ℝ) ^ 10 / 25 → A ≤ B →
      ∀ (S : Finset ℕ) (c : ℕ → ℂ),
      IntegrableOn (fun t => ‖chiDualIntegerBlock s ((m : ℝ) ^ 10) A B t -
        chiDualSpatialStepProfile ((m : ℝ) ^ 10) A B t‖ ^ 2 * ‖zetaChiDualResonator S c t‖ ^ 2)
          (Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10)) volume ∧
      ((∫ t in Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10),
        ‖chiDualIntegerBlock s ((m : ℝ) ^ 10) A B t -
          chiDualSpatialStepProfile ((m : ℝ) ^ 10) A B t‖ ^ 2 * ‖zetaChiDualResonator S c t‖ ^ 2) /
          (m : ℝ) ^ 10) ≤ C * S.card / (m : ℝ) ^ 2 * ∑ a ∈ S, ‖c a‖ ^ 2 := by
  obtain ⟨C, hC, hprofile⟩ := exists_chiDual_integer_block_mean_square_profile z hr hz0 hz1
  refine ⟨C, hC, ?_⟩
  filter_upwards [hprofile, eventually_ge_atTop (1 : ℕ)] with m hm hm1
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
  intro s hs A B hA hB hAB S c
  obtain ⟨hF, hmean⟩ := hm s hs A B hA hB hAB
  let F : ℝ → ℝ := fun t => ‖chiDualIntegerBlock s ((m : ℝ) ^ 10) A B t -
    chiDualSpatialStepProfile ((m : ℝ) ^ 10) A B t‖ ^ 2
  let D : ℝ → ℝ := fun t => ‖zetaChiDualResonator S c t‖ ^ 2
  let K : ℝ := (S.card : ℝ) * ∑ a ∈ S, ‖c a‖ ^ 2
  let W := Icc ((m : ℝ) ^ 10) (2 * (m : ℝ) ^ 10)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hD : AEStronglyMeasurable D (volume.restrict W) :=
    (continuous_zetaChiDualResonator_sq S c).aestronglyMeasurable
  have hbound : ∀ᵐ t ∂volume.restrict W, ‖D t‖ ≤ K := Filter.Eventually.of_forall (fun t => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact norm_zetaChiDualResonator_sq_le S c t)
  have hFD : IntegrableOn (fun t => F t * D t) W volume := hF.mul_bdd hD hbound
  refine ⟨hFD, ?_⟩
  have hb : (∫ t in W, F t * D t) ≤ ∫ t in W, F t * K := by
    apply setIntegral_mono hFD (hF.mul_const K)
    intro t
    exact mul_le_mul_of_nonneg_left (norm_zetaChiDualResonator_sq_le S c t) (sq_nonneg _)
  rw [integral_mul_const] at hb
  have hd := div_le_div_of_nonneg_right hb (by positivity : (0 : ℝ) ≤ (m : ℝ) ^ 10)
  change (∫ t in W, F t * D t) / (m : ℝ) ^ 10 ≤ _
  apply hd.trans
  calc
    _ = ((∫ t in W, F t) / (m : ℝ) ^ 10) * K := by ring
    _ ≤ (C / (m : ℝ) ^ 2) * K := mul_le_mul_of_nonneg_right hmean hK
    _ = _ := by dsimp only [K]; ring

/-- The complete scalar profile persists under every nonzero physical narrow
resonator on the corpus growing schedule. The normalized weighted mean-square
error tends to zero at rate O(k^-3), uniformly in every coefficient family. -/
theorem exists_chiDual_integer_block_normalized_resonator_profile
    (z : ℂ) {r : ℝ} (hr : 0 ≤ r) (hz0 : 1 / 2 ≤ z.re - r) (hz1 : z.re + r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ k : ℕ in atTop, ∀ s ∈ Metric.closedBall z r,
      ∀ A B : ℕ, (5 * (k : ℝ) ^ 2) ^ 10 / 5 ≤ A →
      (B : ℝ) ≤ 6 * (5 * (k : ℝ) ^ 2) ^ 10 / 25 → A ≤ B →
      ∀ (S : Finset ℕ), (∀ a ∈ S, 100 * k ≤ a ∧ a ≤ 101 * k) → ∀ c : ℕ → ℂ,
      0 < (∑ a ∈ S, ‖c a‖ ^ 2) →
      0 < zetaChiDualGrowingResonatorMass S c k ∧
      (∫ t in (5 * (k : ℝ) ^ 2) ^ 10..(2 * (5 * (k : ℝ) ^ 2) ^ 10),
        ‖chiDualIntegerBlock s ((5 * (k : ℝ) ^ 2) ^ 10) A B t -
          chiDualSpatialStepProfile ((5 * (k : ℝ) ^ 2) ^ 10) A B t‖ ^ 2 *
            ‖zetaChiDualResonator S c t‖ ^ 2) /
        zetaChiDualGrowingResonatorMass S c k ≤ C / (k : ℝ) ^ 3 := by
  obtain ⟨C, hC, hprofile⟩ := exists_chiDual_integer_block_resonator_profile z hr hz0 hz1
  obtain ⟨K, hK⟩ := eventually_atTop.mp hprofile
  refine ⟨4 * C, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop K, eventually_ge_atTop (1 : ℕ)] with k hkK hk1
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have hsch : K ≤ 5 * k ^ 2 := by nlinarith only [hkK, hk1]
  have hm := hK (5 * k ^ 2) hsch
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow] at hm
  intro s hs A B hA hB hAB S hS c henergy
  obtain ⟨hfi, hb⟩ := hm s hs A B hA hB hAB S c
  let N : ℝ := (5 * (k : ℝ) ^ 2) ^ 10
  let H : ℝ := zetaChiDualGrowingResonatorMass S c k
  let E : ℝ := ∑ a ∈ S, ‖c a‖ ^ 2
  let F : ℝ → ℝ := fun t =>
    ‖chiDualIntegerBlock s N A B t - chiDualSpatialStepProfile N A B t‖ ^ 2 *
      ‖zetaChiDualResonator S c t‖ ^ 2
  have hN : 0 < N := by dsimp only [N]; positivity
  have hE : 0 < E := henergy
  obtain ⟨hlo, _⟩ := zetaChiDualGrowingResonatorMass_bounds hk1 S c hS
  have hH : 0 < H := lt_of_lt_of_le (by change 0 < N / 2 * E; positivity) hlo
  refine ⟨hH, ?_⟩
  have hmass : N * E ≤ 2 * H := by
    change N / 2 * E ≤ H at hlo
    linarith only [hlo]
  have hsub : S ⊆ Finset.Icc (100 * k) (101 * k) := fun a ha => Finset.mem_Icc.mpr (hS a ha)
  have hcardN := Finset.card_le_card hsub
  rw [Nat.card_Icc] at hcardN
  have hcard : (S.card : ℝ) ≤ 2 * (k : ℝ) := by exact_mod_cast (by omega : S.card ≤ 2 * k)
  have hscalar : C * S.card / (5 * (k : ℝ) ^ 2) ^ 2 ≤ 2 * C / (k : ℝ) ^ 3 := by
    calc
      _ ≤ C * (2 * (k : ℝ)) / (5 * (k : ℝ) ^ 2) ^ 2 := by
        gcongr
      _ = (2 * C / 25) / (k : ℝ) ^ 3 := by field_simp; ring
      _ ≤ (2 * C) / (k : ℝ) ^ 3 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        linarith only [hC]
  have hraw : (∫ t in Icc N (2 * N), F t) ≤ (2 * C / (k : ℝ) ^ 3) * (N * E) := by
    have h0 : (∫ t in Icc N (2 * N), F t) / N ≤ (2 * C / (k : ℝ) ^ 3) * E :=
      hb.trans (mul_le_mul_of_nonneg_right hscalar hE.le)
    have h1 := (div_le_iff₀ hN).mp h0
    calc
      _ ≤ (2 * C / (k : ℝ) ^ 3 * E) * N := h1
      _ = _ := by ring
  change (∫ t in N..(2 * N), F t) / H ≤ _
  apply (div_le_iff₀ hH).mpr
  rw [intervalIntegral.integral_of_le (by linarith only [hN]), ← integral_Icc_eq_integral_Ioc]
  calc
    _ ≤ (2 * C / (k : ℝ) ^ 3) * (N * E) := hraw
    _ ≤ (2 * C / (k : ℝ) ^ 3) * (2 * H) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by ring

end RHTower
