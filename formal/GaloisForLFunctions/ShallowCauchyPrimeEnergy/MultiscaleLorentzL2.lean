import GaloisForLFunctions.ShallowCauchyPrimeEnergy.PoissonKernelDomination
import GaloisForLFunctions.RHTower.ZetaTypicalLocalZeroCountMultiScale
import GaloisForLFunctions.RHTower.ZetaCriticalAsymptotics

/-!
# Multiscale prime-cascade `L²` bound for critical-spacing Lorentzian sums

Combining the prime-cascade multiscale local zero-count regularity
(`exists_volume_multiscale_localZeroCount_gt_le`) with a dyadic superlevel-set decomposition of the
continuous profile `windowNarrowSum Z im (R₀ / 2)` on `[T/2, T] ∪ [T, 2T] ∪ [2T, 4T]` and direct
inverse-square decay on `ℝ \ [T/2, 4T]` establishes the unconditional bound

`Σ_{q₁, q₂ ∈ dyadicZeroWindow T} R₀² / (R₀² + (γ_{q₁} − γ_{q₂})²) ≤ C_pair (R₀ log T) T log T`

uniformly for all `0 < R₀ ≤ 1/32` with `κ₂ ≤ R₀ log T`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology GaloisForLFunctions.HTGeometry
open scoped BigOperators

namespace RHTower

/-! ## Pointwise multiscale bounds on `[S, 2S]` -/

/-- Height `t ∈ [S, 2S]` violates multiscale regularity above `u` if some scale `v ∈ [u, 1/16]`
carries more than `20 v log S` zero copies within ordinate distance `v` of `t`. -/
def MultiScaleBad (S u t : ℝ) : Prop :=
  t ∈ Icc S (2 * S) ∧ ∃ v : ℝ, u ≤ v ∧ v ≤ 1 / 16 ∧ ∃ F : Finset XiZeroCopy,
    (∀ q ∈ F, |((q.1 : ℂ)).im - t| ≤ v) ∧ 20 * (v * Real.log S) < F.card

theorem sum_half_pow_succ_le_one (K : ℕ) :
    ∑ j ∈ Finset.range K, ((1 / 2 : ℝ) ^ (j + 1)) ≤ 1 := by
  have hfactor : ∑ j ∈ Finset.range K, ((1 / 2 : ℝ) ^ (j + 1)) =
      (1 / 2 : ℝ) * ∑ j ∈ Finset.range K, (1 / 2 : ℝ) ^ j := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => by ring
  rw [hfactor, geom_sum_eq (by norm_num)]
  have hp : 0 ≤ (1 / 2 : ℝ) ^ K := by positivity
  linarith [show (1 / 2 : ℝ) * (((1 / 2 : ℝ) ^ K - 1) / (1 / 2 - 1)) =
    1 - (1 / 2 : ℝ) ^ K by ring]

theorem narrowMassTerm_le_far {r t : ℝ} {q : XiZeroCopy}
    (hf : ¬ |((q.1 : ℂ)).im - t| ≤ 1 / 16) :
    narrowMassTerm r t q ≤ 257 * r ^ (2 : ℕ) * lorentzMassTerm t q := by
  have hlt : (1 / 16 : ℝ) < |((q.1 : ℂ)).im - t| := lt_of_not_ge hf
  have hsq : (1 / 256 : ℝ) ≤ (t - (q.1 : ℂ).im) ^ (2 : ℕ) := by
    have habs : (t - (q.1 : ℂ).im) ^ (2 : ℕ) = |((q.1 : ℂ)).im - t| ^ (2 : ℕ) := by
      rw [sq_abs]; ring
    rw [habs]
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1 / 16) hlt.le 2
    linarith
  unfold narrowMassTerm lorentzMassTerm
  rw [← mul_div_assoc, mul_one, div_le_div_iff₀ (by positivity) (by positivity)]
  have hden : 1 + (t - (q.1 : ℂ).im) ^ (2 : ℕ) ≤
      257 * (r ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ)) := by
    have hr2 := sq_nonneg r
    linarith
  have hmul := mul_le_mul_of_nonneg_left hden (sq_nonneg r)
  linarith [show r ^ (2 : ℕ) * (257 * (r ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ))) =
    257 * r ^ (2 : ℕ) * (r ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ)) by ring]

/-- Deterministic ceiling for `windowNarrowSum` on `[S, 2S]` once `0 ≤ r ≤ 1`. -/
theorem windowNarrowSum_le_sixteen_log (Z : Finset XiZeroCopy)
    {S r t : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1)
    (hlog : xiLineTwoLogDerivConstant + Real.log (2 * S + 4) ≤ 2 * Real.log S)
    (ht : t ∈ Icc S (2 * S)) (hS0 : 0 ≤ S) :
    windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t ≤ 16 * Real.log S := by
  have ht0 : 0 ≤ t := hS0.trans ht.1
  have hsum : windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t ≤ lorentzMass t := by
    calc windowNarrowSum Z (fun q => (q.1 : ℂ).im) r t
        = ∑ q ∈ Z, narrowMassTerm r t q := rfl
      _ ≤ ∑ q ∈ Z, lorentzMassTerm t q :=
          Finset.sum_le_sum fun q _ => narrowMassTerm_le_lorentzMassTerm hr0 hr1 t q
      _ ≤ lorentzMass t :=
          (summable_lorentzMassTerm t).sum_le_tsum Z fun q _ => by
            unfold lorentzMassTerm; positivity
  have hlor := lorentzMass_le_log t
  have habs : |t| + 4 ≤ 2 * S + 4 := by rw [abs_of_nonneg ht0]; linarith [ht.2]
  have hlogt : Real.log (|t| + 4) ≤ Real.log (2 * S + 4) :=
    Real.log_le_log (by positivity) habs
  linarith

theorem sum_far_narrowMassTerm_le (Z : Finset XiZeroCopy)
    {S R₀ u t : ℝ} (hS0 : 0 ≤ S) (hR₀ : 0 < R₀) (hRu : R₀ ≤ u) (hu16 : u ≤ 1 / 16)
    (hlog : xiLineTwoLogDerivConstant + Real.log (2 * S + 4) ≤ 2 * Real.log S)
    (ht : t ∈ Icc S (2 * S)) :
    (∑ q ∈ Z.filter (fun q : XiZeroCopy => ¬ |((q.1 : ℂ)).im - t| ≤ 1 / 16),
        narrowMassTerm (R₀ / 2) t q) ≤ 65 * (u * Real.log S) := by
  have hu0 : 0 < u := hR₀.trans_le hRu
  have ht0 : 0 ≤ t := hS0.trans ht.1
  have h1 : (∑ q ∈ Z.filter (fun q : XiZeroCopy => ¬ |((q.1 : ℂ)).im - t| ≤ 1 / 16),
      narrowMassTerm (R₀ / 2) t q) ≤
        257 * (R₀ / 2) ^ (2 : ℕ) * lorentzMass t := by
    calc ∑ q ∈ Z.filter (fun q : XiZeroCopy => ¬ |((q.1 : ℂ)).im - t| ≤ 1 / 16),
          narrowMassTerm (R₀ / 2) t q
        ≤ ∑ q ∈ Z.filter (fun q : XiZeroCopy => ¬ |((q.1 : ℂ)).im - t| ≤ 1 / 16),
            257 * (R₀ / 2) ^ (2 : ℕ) * lorentzMassTerm t q :=
          Finset.sum_le_sum fun q hq => narrowMassTerm_le_far (Finset.mem_filter.mp hq).2
      _ = 257 * (R₀ / 2) ^ (2 : ℕ) *
            ∑ q ∈ Z.filter (fun q : XiZeroCopy => ¬ |((q.1 : ℂ)).im - t| ≤ 1 / 16),
              lorentzMassTerm t q := by rw [Finset.mul_sum]
      _ ≤ 257 * (R₀ / 2) ^ (2 : ℕ) * lorentzMass t :=
          mul_le_mul_of_nonneg_left
            ((summable_lorentzMassTerm t).sum_le_tsum _ fun _ _ => by
              unfold lorentzMassTerm; positivity) (by positivity)
  have habs : |t| + 4 ≤ 2 * S + 4 := by rw [abs_of_nonneg ht0]; linarith [ht.2]
  have hlogt : Real.log (|t| + 4) ≤ Real.log (2 * S + 4) :=
    Real.log_le_log (by positivity) habs
  have hlor : lorentzMass t ≤ 16 * Real.log S := by
    have := lorentzMass_le_log t; linarith
  have hr2 : (R₀ / 2) ^ (2 : ℕ) ≤ u / 64 := by
    have hRu16 : R₀ * R₀ ≤ u * (1 / 16) :=
      mul_le_mul hRu (hRu.trans hu16) hR₀.le hu0.le
    linarith [show (R₀ / 2) ^ (2 : ℕ) = R₀ * R₀ / 4 by ring]
  have hprod : 257 * (R₀ / 2) ^ (2 : ℕ) * lorentzMass t ≤ 257 * (u / 64) * (16 * Real.log S) :=
    mul_le_mul (mul_le_mul_of_nonneg_left hr2 (by norm_num)) hlor
      (tsum_nonneg fun _ => by unfold lorentzMassTerm; positivity) (by positivity)
  have hL0 : 0 ≤ u * Real.log S := by
    have hlor0 : 0 ≤ lorentzMass t := tsum_nonneg fun _ => by unfold lorentzMassTerm; positivity
    have : 0 ≤ Real.log S := by linarith
    exact mul_nonneg hu0.le this
  linarith [h1.trans hprod,
    show 257 * (u / 64) * (16 * Real.log S) = (257 / 4) * (u * Real.log S) by ring]

theorem finset_sum_union_le_of_nonneg {α : Type*} [DecidableEq α] (s₁ s₂ : Finset α)
    {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ s₁ ∪ s₂, f x ≤ (∑ x ∈ s₁, f x) + ∑ x ∈ s₂, f x := by
  have h := Finset.sum_union_inter (s₁ := s₁) (s₂ := s₂) (f := f)
  have hinter : 0 ≤ ∑ x ∈ s₁ ∩ s₂, f x := Finset.sum_nonneg fun x _ => hf x
  linarith

theorem finset_sum_range_biUnion_le_of_nonneg {α : Type*} [DecidableEq α] (K : ℕ)
    (t : ℕ → Finset α) {f : α → ℝ} (hf : ∀ x, 0 ≤ f x) :
    ∑ x ∈ (Finset.range K).biUnion t, f x ≤ ∑ j ∈ Finset.range K, ∑ x ∈ t j, f x := by
  induction K with
  | zero => simp
  | succ k ih =>
    rw [Finset.range_add_one, Finset.biUnion_insert,
      Finset.sum_insert Finset.notMem_range_self]
    exact (finset_sum_union_le_of_nonneg _ _ hf).trans (add_le_add le_rfl ih)

theorem sum_near_narrowMassTerm_le (Z : Finset XiZeroCopy)
    {S R₀ u t : ℝ} (hS : 2 ≤ S) (hR₀ : 0 < R₀) (hRu : R₀ ≤ u) (hu16 : u ≤ 1 / 16)
    (ht : t ∈ Icc S (2 * S)) (hgood : ¬ MultiScaleBad S u t) :
    (∑ q ∈ Z.filter (fun q : XiZeroCopy => |((q.1 : ℂ)).im - t| ≤ 1 / 16),
        narrowMassTerm (R₀ / 2) t q) ≤ 40 * (u * Real.log S) := by
  classical
  have hu0 : 0 < u := hR₀.trans_le hRu
  have hr0 : 0 < R₀ / 2 := half_pos hR₀
  have hL0 : 0 < Real.log S := Real.log_pos (by linarith)
  have hreg : ∀ v : ℝ, u ≤ v → v ≤ 1 / 16 → ∀ F : Finset XiZeroCopy,
      (∀ q ∈ F, |((q.1 : ℂ)).im - t| ≤ v) → (F.card : ℝ) ≤ 20 * (v * Real.log S) := by
    intro v hvu hv16 F hF
    by_contra hgt
    exact hgood ⟨ht, v, hvu, hv16, F, hF, lt_of_not_ge hgt⟩
  have hex : ∃ k : ℕ, 1 / 16 < (2 : ℝ) ^ k * u := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 16 / u) (by norm_num : (1 : ℝ) < 2)
    exact ⟨k, by rwa [div_lt_iff₀ hu0] at hk⟩
  let K := Nat.find hex
  have hKspec : 1 / 16 < (2 : ℝ) ^ K * u := Nat.find_spec hex
  let Znear := Z.filter (fun q : XiZeroCopy => |((q.1 : ℂ)).im - t| ≤ 1 / 16)
  let F₀ := Znear.filter (fun q : XiZeroCopy => |((q.1 : ℂ)).im - t| ≤ u)
  let shell : ℕ → Finset XiZeroCopy := fun j =>
    Znear.filter (fun q : XiZeroCopy =>
      (2 : ℝ) ^ j * u < |((q.1 : ℂ)).im - t| ∧
        |((q.1 : ℂ)).im - t| ≤ min ((2 : ℝ) ^ (j + 1) * u) (1 / 16))
  have hsub : Znear ⊆ F₀ ∪ (Finset.range K).biUnion shell := by
    intro q hq
    have hq16 : |((q.1 : ℂ)).im - t| ≤ 1 / 16 := (Finset.mem_filter.mp hq).2
    by_cases hqu : |((q.1 : ℂ)).im - t| ≤ u
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hq, hqu⟩)
    · apply Finset.mem_union_right
      have hexd : ∃ m : ℕ, |((q.1 : ℂ)).im - t| ≤ (2 : ℝ) ^ m * u :=
        ⟨K, hq16.trans hKspec.le⟩
      have hm_le : Nat.find hexd ≤ K := Nat.find_min' hexd (hq16.trans hKspec.le)
      have hm_pos : 1 ≤ Nat.find hexd := by
        rcases Nat.eq_zero_or_pos (Nat.find hexd) with hm0 | hmp
        · exfalso
          have := Nat.find_spec hexd
          rw [hm0, pow_zero, one_mul] at this
          exact hqu this
        · exact hmp
      refine Finset.mem_biUnion.mpr ⟨Nat.find hexd - 1, Finset.mem_range.mpr (by omega), ?_⟩
      refine Finset.mem_filter.mpr ⟨hq, lt_of_not_ge (Nat.find_min hexd (by omega)), le_min ?_ hq16⟩
      have hms : Nat.find hexd - 1 + 1 = Nat.find hexd := by omega
      rw [hms]
      exact Nat.find_spec hexd
  have hF₀ : ∑ q ∈ F₀, narrowMassTerm (R₀ / 2) t q ≤ 20 * (u * Real.log S) := by
    have hle1 : ∀ q ∈ F₀, narrowMassTerm (R₀ / 2) t q ≤ 1 := fun q _ =>
      (narrowMassTerm_le_lorentzMassTerm hr0.le (by linarith) t q).trans
        (by
          unfold lorentzMassTerm
          exact div_le_one_of_le₀ (by linarith [sq_nonneg (t - (q.1 : ℂ).im)]) (by positivity))
    calc ∑ q ∈ F₀, narrowMassTerm (R₀ / 2) t q ≤ ∑ _q ∈ F₀, (1 : ℝ) := Finset.sum_le_sum hle1
      _ = F₀.card := by simp
      _ ≤ 20 * (u * Real.log S) :=
          hreg u le_rfl hu16 F₀ fun q hq => (Finset.mem_filter.mp hq).2
  have hshell : ∀ j ∈ Finset.range K,
      ∑ q ∈ shell j, narrowMassTerm (R₀ / 2) t q ≤
        20 * (u * Real.log S) * ((1 / 2 : ℝ) ^ (j + 1)) := by
    intro j _
    have hvj_lo : u ≤ min ((2 : ℝ) ^ (j + 1) * u) (1 / 16) := le_min
      (by
        have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (j + 1) := one_le_pow₀ (by norm_num)
        exact (one_mul u).symm.trans_le (mul_le_mul_of_nonneg_right h1 hu0.le))
      hu16
    have hcard : ((shell j).card : ℝ) ≤ 20 * ((2 : ℝ) ^ (j + 1) * u * Real.log S) := by
      have hc := hreg (min ((2 : ℝ) ^ (j + 1) * u) (1 / 16)) hvj_lo (min_le_right _ _)
        (shell j) fun q hq => (Finset.mem_filter.mp hq).2.2
      exact hc.trans (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (min_le_left _ _) hL0.le) (by norm_num))
    have hterm : ∀ q ∈ shell j, narrowMassTerm (R₀ / 2) t q ≤ (1 / 4 : ℝ) ^ (j + 1) := by
      intro q hq
      have hlo : (2 : ℝ) ^ j * u < |((q.1 : ℂ)).im - t| := (Finset.mem_filter.mp hq).2.1
      have hlo_r : (2 : ℝ) ^ (j + 1) * (R₀ / 2) ≤ |((q.1 : ℂ)).im - t| := by
        have hpow : (2 : ℝ) ^ (j + 1) * (R₀ / 2) = (2 : ℝ) ^ j * R₀ := by
          rw [pow_succ]; ring
        rw [hpow]
        exact (mul_le_mul_of_nonneg_left hRu (by positivity)).trans hlo.le
      have hsq : ((2 : ℝ) ^ (j + 1) * (R₀ / 2)) ^ (2 : ℕ) ≤ (t - (q.1 : ℂ).im) ^ (2 : ℕ) := by
        have habs : (t - (q.1 : ℂ).im) ^ (2 : ℕ) = |((q.1 : ℂ)).im - t| ^ (2 : ℕ) := by
          rw [sq_abs]; ring
        rw [habs]
        exact pow_le_pow_left₀ (by positivity) hlo_r 2
      unfold narrowMassTerm
      rw [div_le_iff₀ (by positivity)]
      have hinv : ((2 : ℝ) ^ (j + 1)) ^ (2 : ℕ) * (1 / 4 : ℝ) ^ (j + 1) = 1 := by
        calc ((2 : ℝ) ^ (j + 1)) ^ (2 : ℕ) * (1 / 4 : ℝ) ^ (j + 1)
            = ((2 : ℝ) ^ (2 : ℕ)) ^ (j + 1) * (1 / 4 : ℝ) ^ (j + 1) := by
                rw [← pow_mul, mul_comm (j + 1) 2, pow_mul]
          _ = ((2 : ℝ) ^ (2 : ℕ) * (1 / 4 : ℝ)) ^ (j + 1) := (mul_pow _ _ _).symm
          _ = 1 := by norm_num
      have hmul : (R₀ / 2) ^ (2 : ℕ) =
          ((2 : ℝ) ^ (j + 1) * (R₀ / 2)) ^ (2 : ℕ) * (1 / 4 : ℝ) ^ (j + 1) := by
        calc (R₀ / 2) ^ (2 : ℕ) = (R₀ / 2) ^ (2 : ℕ) * 1 := (mul_one _).symm
          _ = (R₀ / 2) ^ (2 : ℕ) * (((2 : ℝ) ^ (j + 1)) ^ (2 : ℕ) * (1 / 4 : ℝ) ^ (j + 1)) := by
              rw [hinv]
          _ = ((2 : ℝ) ^ (j + 1) * (R₀ / 2)) ^ (2 : ℕ) * (1 / 4 : ℝ) ^ (j + 1) := by ring
      have hc0 : 0 ≤ (1 / 4 : ℝ) ^ (j + 1) := by positivity
      have hstep := mul_le_mul_of_nonneg_right hsq hc0
      have hrnn := mul_nonneg (sq_nonneg (R₀ / 2)) hc0
      linarith [show (1 / 4 : ℝ) ^ (j + 1) * ((R₀ / 2) ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ)) =
        (R₀ / 2) ^ (2 : ℕ) * (1 / 4 : ℝ) ^ (j + 1) +
          (t - (q.1 : ℂ).im) ^ (2 : ℕ) * (1 / 4 : ℝ) ^ (j + 1) by ring]
    calc ∑ q ∈ shell j, narrowMassTerm (R₀ / 2) t q
        ≤ ∑ _q ∈ shell j, (1 / 4 : ℝ) ^ (j + 1) := Finset.sum_le_sum hterm
      _ = ((shell j).card : ℝ) * (1 / 4 : ℝ) ^ (j + 1) := by simp
      _ ≤ (20 * ((2 : ℝ) ^ (j + 1) * u * Real.log S)) * (1 / 4 : ℝ) ^ (j + 1) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = 20 * (u * Real.log S) * ((1 / 2 : ℝ) ^ (j + 1)) := by
          have hp : (2 : ℝ) ^ (j + 1) * (1 / 4 : ℝ) ^ (j + 1) = (1 / 2 : ℝ) ^ (j + 1) := by
            rw [← mul_pow]; norm_num
          calc (20 * ((2 : ℝ) ^ (j + 1) * u * Real.log S)) * (1 / 4 : ℝ) ^ (j + 1)
              = 20 * (u * Real.log S) * ((2 : ℝ) ^ (j + 1) * (1 / 4 : ℝ) ^ (j + 1)) := by ring
            _ = 20 * (u * Real.log S) * ((1 / 2 : ℝ) ^ (j + 1)) := by rw [hp]
  have hnn : ∀ q : XiZeroCopy, 0 ≤ narrowMassTerm (R₀ / 2) t q :=
    narrowMassTerm_nonneg (R₀ / 2) t
  calc ∑ q ∈ Znear, narrowMassTerm (R₀ / 2) t q
      ≤ ∑ q ∈ F₀ ∪ (Finset.range K).biUnion shell, narrowMassTerm (R₀ / 2) t q :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub fun q _ _ => hnn q
    _ ≤ (∑ q ∈ F₀, narrowMassTerm (R₀ / 2) t q) +
          ∑ q ∈ (Finset.range K).biUnion shell, narrowMassTerm (R₀ / 2) t q :=
        finset_sum_union_le_of_nonneg _ _ hnn
    _ ≤ 20 * (u * Real.log S) + ∑ j ∈ Finset.range K, ∑ q ∈ shell j, narrowMassTerm (R₀ / 2) t q :=
        add_le_add hF₀ (finset_sum_range_biUnion_le_of_nonneg K shell hnn)
    _ ≤ 20 * (u * Real.log S) +
          ∑ j ∈ Finset.range K, 20 * (u * Real.log S) * ((1 / 2 : ℝ) ^ (j + 1)) :=
        add_le_add le_rfl (Finset.sum_le_sum hshell)
    _ = 20 * (u * Real.log S) +
          20 * (u * Real.log S) * ∑ j ∈ Finset.range K, ((1 / 2 : ℝ) ^ (j + 1)) := by
        rw [← Finset.mul_sum]
    _ ≤ 20 * (u * Real.log S) + 20 * (u * Real.log S) * 1 :=
        add_le_add le_rfl
          (mul_le_mul_of_nonneg_left (sum_half_pow_succ_le_one K) (by positivity))
    _ = 40 * (u * Real.log S) := by ring

/-- Outside `MultiScaleBad S u`, `windowNarrowSum Z im (R₀ / 2) t ≤ 105 u log S`. -/
theorem windowNarrowSum_le_of_not_multiScaleBad (Z : Finset XiZeroCopy)
    {S R₀ u t : ℝ} (hS : 2 ≤ S) (hR₀ : 0 < R₀) (hRu : R₀ ≤ u) (hu16 : u ≤ 1 / 16)
    (hlog : xiLineTwoLogDerivConstant + Real.log (2 * S + 4) ≤ 2 * Real.log S)
    (ht : t ∈ Icc S (2 * S)) (hgood : ¬ MultiScaleBad S u t) :
    windowNarrowSum Z (fun q => (q.1 : ℂ).im) (R₀ / 2) t ≤ 105 * (u * Real.log S) := by
  classical
  have hsplit : windowNarrowSum Z (fun q => (q.1 : ℂ).im) (R₀ / 2) t =
      (∑ q ∈ Z.filter (fun q : XiZeroCopy => |((q.1 : ℂ)).im - t| ≤ 1 / 16),
          narrowMassTerm (R₀ / 2) t q) +
        ∑ q ∈ Z.filter (fun q : XiZeroCopy => ¬ |((q.1 : ℂ)).im - t| ≤ 1 / 16),
          narrowMassTerm (R₀ / 2) t q :=
    (Finset.sum_filter_add_sum_filter_not Z
      (fun q : XiZeroCopy => |((q.1 : ℂ)).im - t| ≤ 1 / 16) (narrowMassTerm (R₀ / 2) t)).symm
  have hnear := sum_near_narrowMassTerm_le Z hS hR₀ hRu hu16 ht hgood
  have hfar := sum_far_narrowMassTerm_le Z (by linarith) hR₀ hRu hu16 hlog ht
  linarith

/-! ## Dyadic superlevel sets and `[S, 2S]` integral bound -/

/-- Dyadic superlevel set of `windowNarrowSum Z im (R₀ / 2)` on `[S, 2S]`. -/
def narrowSuperlevel (Z : Finset XiZeroCopy) (S R₀ : ℝ) (j : ℕ) : Set ℝ :=
  Icc S (2 * S) ∩
    {t : ℝ | 105 * ((2 : ℝ) ^ j * R₀ * Real.log S) <
      windowNarrowSum Z (fun q => (q.1 : ℂ).im) (R₀ / 2) t}

theorem measurableSet_narrowSuperlevel (Z : Finset XiZeroCopy) (S : ℝ) {R₀ : ℝ}
    (hR₀ : 0 < R₀) (j : ℕ) :
    MeasurableSet (narrowSuperlevel Z S R₀ j) :=
  measurableSet_Icc.inter
    (isOpen_lt continuous_const (continuous_windowNarrowSum Z _ (half_pos hR₀))).measurableSet

theorem narrowSuperlevel_subset_bad (Z : Finset XiZeroCopy) {S R₀ : ℝ} {j : ℕ}
    (hS : 2 ≤ S) (hR₀ : 0 < R₀) (hj16 : (2 : ℝ) ^ j * R₀ ≤ 1 / 16)
    (hlog : xiLineTwoLogDerivConstant + Real.log (2 * S + 4) ≤ 2 * Real.log S) :
    narrowSuperlevel Z S R₀ j ⊆ {t : ℝ | MultiScaleBad S ((2 : ℝ) ^ j * R₀) t} := by
  rintro t ⟨htIcc, htgt⟩
  by_contra hngood
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
  have hRu : R₀ ≤ (2 : ℝ) ^ j * R₀ := (one_mul R₀).symm.trans_le
    (mul_le_mul_of_nonneg_right h1 hR₀.le)
  have hle := windowNarrowSum_le_of_not_multiScaleBad Z hS hR₀ hRu hj16 hlog htIcc hngood
  rw [Set.mem_setOf_eq] at htgt
  linarith

/-- Majorant of `(windowNarrowSum Z im (R₀ / 2) t)²` on `[S, 2S]` built from measurable dyadic
superlevel indicators. -/
def narrowSuperlevelMajorant (Z : Finset XiZeroCopy) (S R₀ : ℝ) (M : ℕ) (t : ℝ) : ℝ :=
  (Icc S (2 * S)).indicator (fun _ => (105 * (R₀ * Real.log S)) ^ (2 : ℕ)) t +
    (∑ j ∈ Finset.range M,
      (narrowSuperlevel Z S R₀ j).indicator
        (fun _ => (105 * ((2 : ℝ) ^ (j + 1) * R₀ * Real.log S)) ^ (2 : ℕ)) t) +
    (narrowSuperlevel Z S R₀ M).indicator (fun _ => (16 * Real.log S) ^ (2 : ℕ)) t

theorem narrowSuperlevelMajorant_nonneg (Z : Finset XiZeroCopy) (S R₀ : ℝ) (M : ℕ) (t : ℝ) :
    0 ≤ narrowSuperlevelMajorant Z S R₀ M t := by
  unfold narrowSuperlevelMajorant
  exact add_nonneg
    (add_nonneg (Set.indicator_nonneg (fun _ _ => by positivity) t)
      (Finset.sum_nonneg fun _ _ => Set.indicator_nonneg (fun _ _ => by positivity) t))
    (Set.indicator_nonneg (fun _ _ => by positivity) t)

theorem windowNarrowSum_sq_le_superlevelMajorant (Z : Finset XiZeroCopy)
    {S R₀ t : ℝ} (M : ℕ) (hS0 : 0 ≤ S) (hR₀0 : 0 ≤ R₀) (hR₀2 : R₀ ≤ 2)
    (hlog : xiLineTwoLogDerivConstant + Real.log (2 * S + 4) ≤ 2 * Real.log S)
    (ht : t ∈ Icc S (2 * S)) :
    (windowNarrowSum Z (fun q => (q.1 : ℂ).im) (R₀ / 2) t) ^ (2 : ℕ) ≤
      narrowSuperlevelMajorant Z S R₀ M t := by
  classical
  have hG0 : 0 ≤ windowNarrowSum Z (fun q => (q.1 : ℂ).im) (R₀ / 2) t :=
    windowNarrowSum_nonneg Z _ (R₀ / 2) t
  have hbase : 0 ≤ (Icc S (2 * S)).indicator (fun _ => (105 * (R₀ * Real.log S)) ^ (2 : ℕ)) t :=
    Set.indicator_nonneg (fun _ _ => by positivity) t
  have hsum0 : 0 ≤ ∑ j ∈ Finset.range M,
      (narrowSuperlevel Z S R₀ j).indicator
        (fun _ => (105 * ((2 : ℝ) ^ (j + 1) * R₀ * Real.log S)) ^ (2 : ℕ)) t :=
    Finset.sum_nonneg fun _ _ => Set.indicator_nonneg (fun _ _ => by positivity) t
  have htop0 : 0 ≤ (narrowSuperlevel Z S R₀ M).indicator
      (fun _ => (16 * Real.log S) ^ (2 : ℕ)) t :=
    Set.indicator_nonneg (fun _ _ => by positivity) t
  by_cases htM : t ∈ narrowSuperlevel Z S R₀ M
  · have hceil : windowNarrowSum Z (fun q => (q.1 : ℂ).im) (R₀ / 2) t ≤ 16 * Real.log S :=
      windowNarrowSum_le_sixteen_log Z (by linarith) (by linarith) hlog ht hS0
    have hsq := pow_le_pow_left₀ hG0 hceil 2
    unfold narrowSuperlevelMajorant
    rw [Set.indicator_of_mem htM]
    linarith
  · by_cases ht0 : t ∈ narrowSuperlevel Z S R₀ 0
    · have hexk : ∃ k : ℕ, t ∉ narrowSuperlevel Z S R₀ k := ⟨M, htM⟩
      have hk_le : Nat.find hexk ≤ M := Nat.find_min' hexk htM
      have hk_pos : 1 ≤ Nat.find hexk := by
        rcases Nat.eq_zero_or_pos (Nat.find hexk) with hk0 | hkp
        · exfalso; exact (Nat.find_spec hexk) (hk0 ▸ ht0)
        · exact hkp
      have hjM : Nat.find hexk - 1 ∈ Finset.range M := Finset.mem_range.mpr (by omega)
      have htj : t ∈ narrowSuperlevel Z S R₀ (Nat.find hexk - 1) := by
        by_contra hnotj
        exact Nat.find_min hexk (by omega) hnotj
      have hnot_succ : t ∉ narrowSuperlevel Z S R₀ (Nat.find hexk - 1 + 1) := by
        have hjk : Nat.find hexk - 1 + 1 = Nat.find hexk := by omega
        rw [hjk]; exact Nat.find_spec hexk
      have hGj : windowNarrowSum Z (fun q => (q.1 : ℂ).im) (R₀ / 2) t ≤
          105 * ((2 : ℝ) ^ (Nat.find hexk - 1 + 1) * R₀ * Real.log S) := by
        by_contra hgt
        exact hnot_succ ⟨ht, lt_of_not_ge hgt⟩
      have hsq := pow_le_pow_left₀ hG0 hGj 2
      have hsingle :
          (105 * ((2 : ℝ) ^ (Nat.find hexk - 1 + 1) * R₀ * Real.log S)) ^ (2 : ℕ) ≤
            ∑ i ∈ Finset.range M,
              (narrowSuperlevel Z S R₀ i).indicator
                (fun _ => (105 * ((2 : ℝ) ^ (i + 1) * R₀ * Real.log S)) ^ (2 : ℕ)) t := by
        calc (105 * ((2 : ℝ) ^ (Nat.find hexk - 1 + 1) * R₀ * Real.log S)) ^ (2 : ℕ)
            = (narrowSuperlevel Z S R₀ (Nat.find hexk - 1)).indicator
                (fun _ => (105 * ((2 : ℝ) ^ (Nat.find hexk - 1 + 1) * R₀ * Real.log S)) ^ (2 : ℕ))
                t :=
              (Set.indicator_of_mem htj
                (fun _ : ℝ =>
                  (105 * ((2 : ℝ) ^ (Nat.find hexk - 1 + 1) * R₀ * Real.log S)) ^ (2 : ℕ))).symm
          _ ≤ _ := Finset.single_le_sum
              (f := fun i => (narrowSuperlevel Z S R₀ i).indicator
                (fun _ => (105 * ((2 : ℝ) ^ (i + 1) * R₀ * Real.log S)) ^ (2 : ℕ)) t)
              (fun _ _ => Set.indicator_nonneg (fun _ _ => by positivity) t) hjM
      unfold narrowSuperlevelMajorant
      linarith
    · have hG_base : windowNarrowSum Z (fun q => (q.1 : ℂ).im) (R₀ / 2) t ≤
          105 * (R₀ * Real.log S) := by
        by_contra hgt
        apply ht0
        refine ⟨ht, ?_⟩
        simpa using lt_of_not_ge hgt
      have hsq := pow_le_pow_left₀ hG0 hG_base 2
      unfold narrowSuperlevelMajorant
      rw [Set.indicator_of_mem ht]
      linarith

theorem sum_four_pow_mul_exp_neg_two_pow_le {x : ℝ} (hx : 1 ≤ x) (M : ℕ) :
    ∑ j ∈ Finset.range M, (4 : ℝ) ^ j * Real.exp (-((2 : ℝ) ^ j * x)) ≤ 17 := by
  rcases M with _ | m
  · simp
  · rw [Finset.sum_range_succ']
    have h0 : (4 : ℝ) ^ (0 : ℕ) * Real.exp (-((2 : ℝ) ^ (0 : ℕ) * x)) ≤ 1 := by
      simp only [pow_zero, one_mul]
      exact Real.exp_le_one_iff.mpr (by linarith)
    have hterm : ∀ k : ℕ,
        (4 : ℝ) ^ (k + 1) * Real.exp (-((2 : ℝ) ^ (k + 1) * x)) ≤
          8 * Real.exp (-((2 : ℝ) ^ k * 1)) := by
      intro k
      have hk_sq : ((2 : ℝ) ^ k) ^ (2 : ℕ) ≤ 2 * Real.exp ((2 : ℝ) ^ k) := by
        have h2 := Real.pow_div_factorial_le_exp ((2 : ℝ) ^ k) (by positivity) 2
        have hf : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num [Nat.factorial]
        rw [hf] at h2
        linarith
      have h4 : (4 : ℝ) ^ (k + 1) ≤ 8 * Real.exp ((2 : ℝ) ^ k) := by
        have heq : (4 : ℝ) ^ (k + 1) = 4 * ((2 : ℝ) ^ k) ^ (2 : ℕ) := by
          rw [pow_succ, show (4 : ℝ) ^ k = ((2 : ℝ) ^ k) ^ (2 : ℕ) by
            rw [← pow_mul, mul_comm, pow_mul]; norm_num]
          ring
        rw [heq]; linarith
      have hexp : Real.exp (-((2 : ℝ) ^ (k + 1) * x)) ≤ Real.exp (-(2 * (2 : ℝ) ^ k)) := by
        apply Real.exp_le_exp.mpr
        rw [pow_succ]
        have hk0 : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
        have hkx : (2 : ℝ) ^ k * 1 ≤ (2 : ℝ) ^ k * x :=
          mul_le_mul_of_nonneg_left hx hk0.le
        linarith
      calc (4 : ℝ) ^ (k + 1) * Real.exp (-((2 : ℝ) ^ (k + 1) * x))
          ≤ (8 * Real.exp ((2 : ℝ) ^ k)) * Real.exp (-(2 * (2 : ℝ) ^ k)) :=
            mul_le_mul h4 hexp (Real.exp_pos _).le (by positivity)
        _ = 8 * (Real.exp ((2 : ℝ) ^ k) * Real.exp (-(2 * (2 : ℝ) ^ k))) := by ring
        _ = 8 * Real.exp (-((2 : ℝ) ^ k * 1)) := by
            rw [← Real.exp_add]; congr 2; ring
    have hsum : ∑ k ∈ Finset.range m,
        (4 : ℝ) ^ (k + 1) * Real.exp (-((2 : ℝ) ^ (k + 1) * x)) ≤ 16 := by
      calc ∑ k ∈ Finset.range m, (4 : ℝ) ^ (k + 1) * Real.exp (-((2 : ℝ) ^ (k + 1) * x))
          ≤ ∑ k ∈ Finset.range m, 8 * Real.exp (-((2 : ℝ) ^ k * 1)) :=
            Finset.sum_le_sum fun k _ => hterm k
        _ = 8 * ∑ k ∈ Finset.range m, Real.exp (-((2 : ℝ) ^ k * 1)) := by
            rw [← Finset.mul_sum]
        _ ≤ 8 * (2 * Real.exp (-1)) :=
            mul_le_mul_of_nonneg_left (sum_exp_neg_two_pow_mul_le le_rfl m) (by norm_num)
        _ ≤ 16 := by
            have : Real.exp (-1) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
            linarith
    linarith

theorem integral_indicator_const_le_of_volume_le {B : Set ℝ} {c V : ℝ}
    (hBm : MeasurableSet B) (hc : 0 ≤ c) (hV : 0 ≤ V)
    (hvol : volume B ≤ ENNReal.ofReal V) :
    Integrable (B.indicator fun _ : ℝ => c) volume ∧
      (∫ t : ℝ, B.indicator (fun _ : ℝ => c) t) ≤ c * V := by
  have hfin : volume B < ⊤ := lt_of_le_of_lt hvol ENNReal.ofReal_lt_top
  have hint : Integrable (B.indicator fun _ : ℝ => c) volume :=
    ((integrableOn_const hfin.ne : IntegrableOn (fun _ : ℝ => c) B)).integrable_indicator hBm
  refine ⟨hint, ?_⟩
  rw [MeasureTheory.integral_indicator_const c hBm, smul_eq_mul, MeasureTheory.measureReal_def]
  have hle : (volume B).toReal ≤ (ENNReal.ofReal V).toReal :=
    ENNReal.toReal_mono ENNReal.ofReal_ne_top hvol
  rw [ENNReal.toReal_ofReal hV, mul_comm] at *
  exact mul_le_mul_of_nonneg_left hle hc

theorem eventually_log_cube_mul_rpow_three_quarters_le (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ S : ℝ in atTop, K * Real.log S ^ (3 : ℕ) * S ^ ((3 : ℝ) / 4) ≤ S := by
  have h1 := (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 12) (by norm_num)).bound
    (show (0 : ℝ) < 1 / (K + 1) by positivity)
  filter_upwards [h1, eventually_ge_atTop (1 : ℝ)] with S hS hS1
  have hS0 : 0 < S := by linarith
  have hL0 : 0 ≤ Real.log S := Real.log_nonneg hS1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL0,
    abs_of_nonneg (Real.rpow_nonneg hS0.le _)] at hS
  have hcube : Real.log S ^ (3 : ℕ) ≤ (1 / (K + 1)) ^ (3 : ℕ) * S ^ ((1 : ℝ) / 4) := by
    calc Real.log S ^ (3 : ℕ)
        ≤ (1 / (K + 1) * S ^ ((1 : ℝ) / 12)) ^ (3 : ℕ) := pow_le_pow_left₀ hL0 hS 3
      _ = (1 / (K + 1)) ^ (3 : ℕ) * (S ^ ((1 : ℝ) / 12)) ^ (3 : ℕ) := by ring
      _ = (1 / (K + 1)) ^ (3 : ℕ) * S ^ ((1 : ℝ) / 4) := by
          rw [← Real.rpow_natCast (S ^ ((1 : ℝ) / 12)), ← Real.rpow_mul hS0.le]
          norm_num
  have hinv_le : K * (1 / (K + 1)) ^ (3 : ℕ) ≤ 1 := by
    have hle1 : 1 / (K + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
    have hp : (1 / (K + 1)) ^ (3 : ℕ) ≤ 1 / (K + 1) := by
      calc (1 / (K + 1)) ^ (3 : ℕ)
          = (1 / (K + 1)) ^ (2 : ℕ) * (1 / (K + 1)) := by ring
        _ ≤ 1 * (1 / (K + 1)) :=
            mul_le_mul_of_nonneg_right (pow_le_one₀ (by positivity) hle1) (by positivity)
        _ = 1 / (K + 1) := one_mul _
    calc K * (1 / (K + 1)) ^ (3 : ℕ)
        ≤ K * (1 / (K + 1)) := mul_le_mul_of_nonneg_left hp hK
      _ ≤ (K + 1) * (1 / (K + 1)) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 1 := by field_simp
  calc K * Real.log S ^ (3 : ℕ) * S ^ ((3 : ℝ) / 4)
      ≤ K * ((1 / (K + 1)) ^ (3 : ℕ) * S ^ ((1 : ℝ) / 4)) * S ^ ((3 : ℝ) / 4) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcube hK)
          (Real.rpow_nonneg hS0.le _)
    _ = (K * (1 / (K + 1)) ^ (3 : ℕ)) * (S ^ ((1 : ℝ) / 4) * S ^ ((3 : ℝ) / 4)) := by ring
    _ = (K * (1 / (K + 1)) ^ (3 : ℕ)) * S := by
        rw [← Real.rpow_add hS0, show (1 : ℝ) / 4 + 3 / 4 = 1 by norm_num, Real.rpow_one]
    _ ≤ 1 * S := mul_le_mul_of_nonneg_right hinv_le hS0.le
    _ = S := one_mul S

theorem eventually_sq_log_mul_exp_neg_div_le (K : ℝ) (hK : 0 ≤ K) :
    ∀ᶠ S : ℝ in atTop,
      K * Real.log S ^ (2 : ℕ) * Real.exp (-(Real.log S / 3840000)) ≤ 1 := by
  have h1 := (isLittleO_log_rpow_atTop (r := (1 : ℝ) / 7680000) (by norm_num)).bound
    (show (0 : ℝ) < 1 / (K + 1) by positivity)
  filter_upwards [h1, eventually_ge_atTop (1 : ℝ)] with S hS hS1
  have hS0 : 0 < S := by linarith
  have hL0 : 0 ≤ Real.log S := Real.log_nonneg hS1
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hL0,
    abs_of_nonneg (Real.rpow_nonneg hS0.le _)] at hS
  have hsq : Real.log S ^ (2 : ℕ) ≤ (1 / (K + 1)) ^ (2 : ℕ) * S ^ ((1 : ℝ) / 3840000) := by
    calc Real.log S ^ (2 : ℕ)
        ≤ (1 / (K + 1) * S ^ ((1 : ℝ) / 7680000)) ^ (2 : ℕ) := pow_le_pow_left₀ hL0 hS 2
      _ = (1 / (K + 1)) ^ (2 : ℕ) * (S ^ ((1 : ℝ) / 7680000)) ^ (2 : ℕ) := by ring
      _ = (1 / (K + 1)) ^ (2 : ℕ) * S ^ ((1 : ℝ) / 3840000) := by
          rw [← Real.rpow_natCast (S ^ ((1 : ℝ) / 7680000)), ← Real.rpow_mul hS0.le]
          norm_num
  have hexp : Real.exp (-(Real.log S / 3840000)) = S ^ (-(1 : ℝ) / 3840000) := by
    rw [Real.rpow_def_of_pos hS0]; congr 1; ring
  have hinv_le : K * (1 / (K + 1)) ^ (2 : ℕ) ≤ 1 := by
    have hle1 : 1 / (K + 1) ≤ 1 := div_le_one_of_le₀ (by linarith) (by positivity)
    calc K * (1 / (K + 1)) ^ (2 : ℕ)
        = K * (1 / (K + 1)) * (1 / (K + 1)) := by ring
      _ ≤ K * (1 / (K + 1)) * 1 := mul_le_mul_of_nonneg_left hle1 (by positivity)
      _ ≤ (K + 1) * (1 / (K + 1)) := by
          rw [mul_one]
          exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = 1 := by field_simp
  calc K * Real.log S ^ (2 : ℕ) * Real.exp (-(Real.log S / 3840000))
      ≤ K * ((1 / (K + 1)) ^ (2 : ℕ) * S ^ ((1 : ℝ) / 3840000)) * S ^ (-(1 : ℝ) / 3840000) := by
        rw [hexp]
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hK)
          (Real.rpow_nonneg hS0.le _)
    _ = K * (1 / (K + 1)) ^ (2 : ℕ) *
          (S ^ ((1 : ℝ) / 3840000) * S ^ (-(1 : ℝ) / 3840000)) := by ring
    _ = K * (1 / (K + 1)) ^ (2 : ℕ) := by
        rw [← Real.rpow_add hS0, show (1 : ℝ) / 3840000 + -(1 : ℝ) / 3840000 = 0 by ring,
          Real.rpow_zero, mul_one]
    _ ≤ 1 := hinv_le

/-- **Multiscale `L²` bound on `[S, 2S]`.** There exist `C₁ > 0` and `κ₂ ≥ 120000` such that
eventually for large `S`, for every `0 < R₀ ≤ 1/16` with `κ₂ ≤ R₀ log S` and every finite set `Z`
of `ξ`-zero copies,

`∫_{t ∈ [S, 2S]} (windowNarrowSum Z im (R₀ / 2) t)² dt ≤ C₁ (R₀ log S)² S`. -/
theorem exists_integral_Icc_windowNarrowSum_sq_le :
    ∃ C₁ κ₂ : ℝ, 0 < C₁ ∧ 120000 ≤ κ₂ ∧ ∀ᶠ S : ℝ in atTop,
      ∀ R₀ : ℝ, 0 < R₀ → R₀ ≤ 1 / 16 → κ₂ ≤ R₀ * Real.log S →
      ∀ Z : Finset XiZeroCopy,
        (∫ t in Icc S (2 * S),
            (windowNarrowSum Z (fun q => (q.1 : ℂ).im) (R₀ / 2) t) ^ (2 : ℕ)) ≤
          C₁ * (R₀ * Real.log S) ^ (2 : ℕ) * S := by
  classical
  obtain ⟨C, κ₂, hC, hκ₂, hev⟩ := exists_volume_multiscale_localZeroCount_gt_le
  refine ⟨105 ^ (2 : ℕ) + 4 * 105 ^ (2 : ℕ) * 12 * C * 17 + 3, κ₂, by positivity, hκ₂, ?_⟩
  filter_upwards [hev,
    Real.tendsto_log_atTop.eventually_ge_atTop (|xiLineTwoLogDerivConstant| + 2),
    eventually_ge_atTop (4 : ℝ),
    eventually_log_cube_mul_rpow_three_quarters_le (105 ^ (2 : ℕ) * C) (by positivity),
    eventually_log_cube_mul_rpow_three_quarters_le (256 * C) (by positivity),
    eventually_sq_log_mul_exp_neg_div_le (256 * 12 * C) (by positivity)]
    with S hvol hLbig hS4 hsub1 hsub2 hexp_top R₀ hR₀ hR₀16 hκ Z
  have hS0 : 0 < S := by linarith
  have hL1 : 1 ≤ Real.log S := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
  have hlog_lor : xiLineTwoLogDerivConstant + Real.log (2 * S + 4) ≤ 2 * Real.log S := by
    have h2S4 : Real.log (2 * S + 4) ≤ Real.log (3 * S) :=
      Real.log_le_log (by linarith) (by linarith)
    have h3S : Real.log (3 * S) = Real.log 3 + Real.log S :=
      Real.log_mul (by norm_num) hS0.ne'
    have hlog3 : Real.log 3 ≤ 2 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
      linarith
    have hCabs : xiLineTwoLogDerivConstant ≤ |xiLineTwoLogDerivConstant| := le_abs_self _
    linarith
  have hex : ∃ k : ℕ, 1 / 16 < (2 : ℝ) ^ k * R₀ := by
    obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (1 / 16 / R₀) (by norm_num : (1 : ℝ) < 2)
    exact ⟨k, by rwa [div_lt_iff₀ hR₀] at hk⟩
  have hK₀spec : 1 / 16 < (2 : ℝ) ^ Nat.find hex * R₀ := Nat.find_spec hex
  have hK₀pos : 1 ≤ Nat.find hex := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hp
    · exfalso; rw [h0, pow_zero, one_mul] at hK₀spec; linarith
    · exact hp
  let M := Nat.find hex - 1
  have hM_le16 : ∀ j ≤ M, (2 : ℝ) ^ j * R₀ ≤ 1 / 16 :=
    fun j hj => not_lt.mp (Nat.find_min hex (by omega))
  have hM_gt32 : 1 / 32 < (2 : ℝ) ^ M * R₀ := by
    have hKM : Nat.find hex = M + 1 := by omega
    rw [hKM, pow_succ] at hK₀spec
    linarith
  have hBvol : ∀ j ≤ M,
      volume (narrowSuperlevel Z S R₀ j) ≤ ENNReal.ofReal
        (12 * C * S * Real.exp (-((2 : ℝ) ^ j * R₀ * Real.log S / 120000)) +
          C * S ^ ((3 : ℝ) / 4)) := by
    intro j hj
    have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hRu : R₀ ≤ (2 : ℝ) ^ j * R₀ :=
      (one_mul R₀).symm.trans_le (mul_le_mul_of_nonneg_right h1 hR₀.le)
    exact (measure_mono (narrowSuperlevel_subset_bad Z (by linarith) hR₀ (hM_le16 j hj)
      hlog_lor)).trans (hvol ((2 : ℝ) ^ j * R₀) (by positivity) (hM_le16 j hj)
        (hκ.trans (mul_le_mul_of_nonneg_right hRu (by linarith))))
  have hIcc_vol : volume (Icc S (2 * S)) ≤ ENNReal.ofReal S := by
    rw [Real.volume_Icc, show 2 * S - S = S by ring]
  obtain ⟨hint_base, hval_base⟩ := integral_indicator_const_le_of_volume_le
    measurableSet_Icc (c := (105 * (R₀ * Real.log S)) ^ (2 : ℕ)) (by positivity) hS0.le hIcc_vol
  have hB_est : ∀ j ≤ M,
      Integrable ((narrowSuperlevel Z S R₀ j).indicator
          fun _ : ℝ => (105 * ((2 : ℝ) ^ (j + 1) * R₀ * Real.log S)) ^ (2 : ℕ)) volume ∧
        (∫ t : ℝ, (narrowSuperlevel Z S R₀ j).indicator
          (fun _ : ℝ => (105 * ((2 : ℝ) ^ (j + 1) * R₀ * Real.log S)) ^ (2 : ℕ)) t) ≤
          (105 * ((2 : ℝ) ^ (j + 1) * R₀ * Real.log S)) ^ (2 : ℕ) *
            (12 * C * S * Real.exp (-((2 : ℝ) ^ j * R₀ * Real.log S / 120000)) +
              C * S ^ ((3 : ℝ) / 4)) :=
    fun j hj => integral_indicator_const_le_of_volume_le
      (measurableSet_narrowSuperlevel Z S hR₀ j) (by positivity) (by positivity) (hBvol j hj)
  obtain ⟨hint_top, hval_top⟩ := integral_indicator_const_le_of_volume_le
    (measurableSet_narrowSuperlevel Z S hR₀ M) (c := (16 * Real.log S) ^ (2 : ℕ))
    (by positivity) (by positivity) (hBvol M le_rfl)
  have hint_sum : Integrable (fun t : ℝ => ∑ j ∈ Finset.range M,
      (narrowSuperlevel Z S R₀ j).indicator
        (fun _ => (105 * ((2 : ℝ) ^ (j + 1) * R₀ * Real.log S)) ^ (2 : ℕ)) t) volume :=
    integrable_finsetSum (Finset.range M) fun j hj =>
      (hB_est j (Nat.le_of_lt (Finset.mem_range.mp hj))).1
  have hint_base_sum : Integrable (fun t : ℝ =>
      (Icc S (2 * S)).indicator (fun _ => (105 * (R₀ * Real.log S)) ^ (2 : ℕ)) t +
        ∑ j ∈ Finset.range M,
          (narrowSuperlevel Z S R₀ j).indicator
            (fun _ => (105 * ((2 : ℝ) ^ (j + 1) * R₀ * Real.log S)) ^ (2 : ℕ)) t) volume :=
    hint_base.add hint_sum
  have hint_maj : Integrable (narrowSuperlevelMajorant Z S R₀ M) volume :=
    hint_base_sum.add hint_top
  have hint_Icc_le :
      (∫ t in Icc S (2 * S),
          (windowNarrowSum Z (fun q => (q.1 : ℂ).im) (R₀ / 2) t) ^ (2 : ℕ)) ≤
        ∫ t : ℝ, narrowSuperlevelMajorant Z S R₀ M t := by
    calc ∫ t in Icc S (2 * S),
          (windowNarrowSum Z (fun q => (q.1 : ℂ).im) (R₀ / 2) t) ^ (2 : ℕ)
        ≤ ∫ t in Icc S (2 * S), narrowSuperlevelMajorant Z S R₀ M t :=
          MeasureTheory.setIntegral_mono_on
            (integrable_windowNarrowSum_sq Z _ (half_pos hR₀)).integrableOn
            hint_maj.integrableOn measurableSet_Icc
            (fun t ht => windowNarrowSum_sq_le_superlevelMajorant Z M hS0.le hR₀.le
              (by linarith) hlog_lor ht)
      _ ≤ ∫ t : ℝ, narrowSuperlevelMajorant Z S R₀ M t :=
          MeasureTheory.setIntegral_le_integral hint_maj
            (Filter.Eventually.of_forall (narrowSuperlevelMajorant_nonneg Z S R₀ M))
  have hmaj_eval :
      (∫ t : ℝ, narrowSuperlevelMajorant Z S R₀ M t) ≤
        (105 * (R₀ * Real.log S)) ^ (2 : ℕ) * S +
          (∑ j ∈ Finset.range M,
            (105 * ((2 : ℝ) ^ (j + 1) * R₀ * Real.log S)) ^ (2 : ℕ) *
              (12 * C * S * Real.exp (-((2 : ℝ) ^ j * R₀ * Real.log S / 120000)) +
                C * S ^ ((3 : ℝ) / 4))) +
          (16 * Real.log S) ^ (2 : ℕ) *
            (12 * C * S * Real.exp (-((2 : ℝ) ^ M * R₀ * Real.log S / 120000)) +
              C * S ^ ((3 : ℝ) / 4)) := by
    unfold narrowSuperlevelMajorant
    rw [MeasureTheory.integral_add hint_base_sum hint_top,
      MeasureTheory.integral_add hint_base hint_sum,
      MeasureTheory.integral_finsetSum (Finset.range M) fun j hj =>
        (hB_est j (Nat.le_of_lt (Finset.mem_range.mp hj))).1]
    exact add_le_add
      (add_le_add hval_base
        (Finset.sum_le_sum fun j hj => (hB_est j (Nat.le_of_lt (Finset.mem_range.mp hj))).2))
      hval_top
  have hx₀ : 1 ≤ R₀ * Real.log S / 120000 := by
    rw [le_div_iff₀ (by norm_num)]; linarith
  have hRL1 : 1 ≤ (R₀ * Real.log S) ^ (2 : ℕ) :=
    one_le_pow₀ (by linarith)
  have hS_le_RL : S ≤ (R₀ * Real.log S) ^ (2 : ℕ) * S :=
    (one_mul S).symm.trans_le (mul_le_mul_of_nonneg_right hRL1 hS0.le)
  have hM_le_L : (M : ℝ) ≤ Real.log S := by
    have hpowM : (2 : ℝ) ^ M * R₀ ≤ 1 / 16 := hM_le16 M le_rfl
    have h1 : (2 : ℝ) ^ M * 1 ≤ (2 : ℝ) ^ M * (R₀ * Real.log S) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h2 : (2 : ℝ) ^ M * (R₀ * Real.log S) ≤ (1 / 16) * Real.log S := by
      calc (2 : ℝ) ^ M * (R₀ * Real.log S) = ((2 : ℝ) ^ M * R₀) * Real.log S := by ring
        _ ≤ (1 / 16) * Real.log S := mul_le_mul_of_nonneg_right hpowM (by linarith)
    have hM2 : (M : ℝ) ≤ (2 : ℝ) ^ M := by
      have hlt : (M : ℝ) < (2 : ℝ) ^ M := by exact_mod_cast Nat.lt_two_pow_self (n := M)
      exact hlt.le
    linarith
  have hmid_exp :
      (∑ j ∈ Finset.range M,
          (105 * ((2 : ℝ) ^ (j + 1) * R₀ * Real.log S)) ^ (2 : ℕ) *
            (12 * C * S * Real.exp (-((2 : ℝ) ^ j * R₀ * Real.log S / 120000)))) ≤
        (4 * 105 ^ (2 : ℕ) * 12 * C * 17) * (R₀ * Real.log S) ^ (2 : ℕ) * S := by
    have hrew :
        (∑ j ∈ Finset.range M,
            (105 * ((2 : ℝ) ^ (j + 1) * R₀ * Real.log S)) ^ (2 : ℕ) *
              (12 * C * S * Real.exp (-((2 : ℝ) ^ j * R₀ * Real.log S / 120000)))) =
          (4 * 105 ^ (2 : ℕ) * 12 * C * (R₀ * Real.log S) ^ (2 : ℕ) * S) *
            ∑ j ∈ Finset.range M,
              (4 : ℝ) ^ j * Real.exp (-((2 : ℝ) ^ j * (R₀ * Real.log S / 120000))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have h4 : ((2 : ℝ) ^ (j + 1)) ^ (2 : ℕ) = 4 * (4 : ℝ) ^ j := by
        calc ((2 : ℝ) ^ (j + 1)) ^ (2 : ℕ)
            = ((2 : ℝ) ^ (2 : ℕ)) ^ (j + 1) := by rw [← pow_mul, mul_comm, pow_mul]
          _ = (4 : ℝ) ^ (j + 1) := by norm_num
          _ = 4 * (4 : ℝ) ^ j := by rw [pow_succ]; ring
      have hexp_eq : -((2 : ℝ) ^ j * R₀ * Real.log S / 120000) =
          -((2 : ℝ) ^ j * (R₀ * Real.log S / 120000)) := by ring
      rw [hexp_eq]
      calc (105 * ((2 : ℝ) ^ (j + 1) * R₀ * Real.log S)) ^ (2 : ℕ) *
            (12 * C * S * Real.exp (-((2 : ℝ) ^ j * (R₀ * Real.log S / 120000))))
          = 105 ^ (2 : ℕ) * ((2 : ℝ) ^ (j + 1)) ^ (2 : ℕ) * (R₀ * Real.log S) ^ (2 : ℕ) *
              (12 * C * S * Real.exp (-((2 : ℝ) ^ j * (R₀ * Real.log S / 120000)))) := by ring
        _ = 4 * 105 ^ (2 : ℕ) * 12 * C * (R₀ * Real.log S) ^ (2 : ℕ) * S *
              ((4 : ℝ) ^ j * Real.exp (-((2 : ℝ) ^ j * (R₀ * Real.log S / 120000)))) := by
              rw [h4]; ring
    rw [hrew]
    calc (4 * 105 ^ (2 : ℕ) * 12 * C * (R₀ * Real.log S) ^ (2 : ℕ) * S) *
          ∑ j ∈ Finset.range M,
            (4 : ℝ) ^ j * Real.exp (-((2 : ℝ) ^ j * (R₀ * Real.log S / 120000)))
        ≤ (4 * 105 ^ (2 : ℕ) * 12 * C * (R₀ * Real.log S) ^ (2 : ℕ) * S) * 17 :=
          mul_le_mul_of_nonneg_left (sum_four_pow_mul_exp_neg_two_pow_le hx₀ M) (by positivity)
      _ = (4 * 105 ^ (2 : ℕ) * 12 * C * 17) * (R₀ * Real.log S) ^ (2 : ℕ) * S := by ring
  have hmid_pow :
      (∑ j ∈ Finset.range M,
          (105 * ((2 : ℝ) ^ (j + 1) * R₀ * Real.log S)) ^ (2 : ℕ) *
            (C * S ^ ((3 : ℝ) / 4))) ≤ S := by
    have hcj_le : ∀ j ∈ Finset.range M,
        (105 * ((2 : ℝ) ^ (j + 1) * R₀ * Real.log S)) ^ (2 : ℕ) ≤
          (105 * Real.log S) ^ (2 : ℕ) := by
      intro j hj
      have hjM : j < M := Finset.mem_range.mp hj
      have h2j : (2 : ℝ) ^ (j + 1) * R₀ ≤ 1 := by
        have := hM_le16 j (by omega)
        rw [pow_succ]; linarith
      refine pow_le_pow_left₀ (by positivity) ?_ 2
      calc 105 * ((2 : ℝ) ^ (j + 1) * R₀ * Real.log S)
          = 105 * (((2 : ℝ) ^ (j + 1) * R₀) * Real.log S) := by ring
        _ ≤ 105 * (1 * Real.log S) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right h2j (by linarith)) (by norm_num)
        _ = 105 * Real.log S := by ring
    calc ∑ j ∈ Finset.range M,
          (105 * ((2 : ℝ) ^ (j + 1) * R₀ * Real.log S)) ^ (2 : ℕ) * (C * S ^ ((3 : ℝ) / 4))
        ≤ ∑ _j ∈ Finset.range M, (105 * Real.log S) ^ (2 : ℕ) * (C * S ^ ((3 : ℝ) / 4)) :=
          Finset.sum_le_sum fun j hj =>
            mul_le_mul_of_nonneg_right (hcj_le j hj) (by positivity)
      _ = (M : ℝ) * ((105 * Real.log S) ^ (2 : ℕ) * (C * S ^ ((3 : ℝ) / 4))) := by simp
      _ ≤ Real.log S * ((105 * Real.log S) ^ (2 : ℕ) * (C * S ^ ((3 : ℝ) / 4))) :=
          mul_le_mul_of_nonneg_right hM_le_L (by positivity)
      _ = 105 ^ (2 : ℕ) * C * Real.log S ^ (3 : ℕ) * S ^ ((3 : ℝ) / 4) := by ring
      _ ≤ S := hsub1
  have hmid_split :
      (∑ j ∈ Finset.range M,
          (105 * ((2 : ℝ) ^ (j + 1) * R₀ * Real.log S)) ^ (2 : ℕ) *
            (12 * C * S * Real.exp (-((2 : ℝ) ^ j * R₀ * Real.log S / 120000)) +
              C * S ^ ((3 : ℝ) / 4))) =
        (∑ j ∈ Finset.range M,
            (105 * ((2 : ℝ) ^ (j + 1) * R₀ * Real.log S)) ^ (2 : ℕ) *
              (12 * C * S * Real.exp (-((2 : ℝ) ^ j * R₀ * Real.log S / 120000)))) +
          ∑ j ∈ Finset.range M,
            (105 * ((2 : ℝ) ^ (j + 1) * R₀ * Real.log S)) ^ (2 : ℕ) *
              (C * S ^ ((3 : ℝ) / 4)) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun _ _ => by ring
  have htop_bound :
      (16 * Real.log S) ^ (2 : ℕ) *
          (12 * C * S * Real.exp (-((2 : ℝ) ^ M * R₀ * Real.log S / 120000)) +
            C * S ^ ((3 : ℝ) / 4)) ≤
        2 * (R₀ * Real.log S) ^ (2 : ℕ) * S := by
    have hexp_M : Real.exp (-((2 : ℝ) ^ M * R₀ * Real.log S / 120000)) ≤
        Real.exp (-(Real.log S / 3840000)) := by
      apply Real.exp_le_exp.mpr
      have := mul_lt_mul_of_pos_right hM_gt32 (show 0 < Real.log S by linarith)
      linarith
    have hp1 : (16 * Real.log S) ^ (2 : ℕ) *
        (12 * C * S * Real.exp (-((2 : ℝ) ^ M * R₀ * Real.log S / 120000))) ≤ S := by
      calc (16 * Real.log S) ^ (2 : ℕ) *
            (12 * C * S * Real.exp (-((2 : ℝ) ^ M * R₀ * Real.log S / 120000)))
          ≤ (16 * Real.log S) ^ (2 : ℕ) *
              (12 * C * S * Real.exp (-(Real.log S / 3840000))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left hexp_M (by positivity)) (by positivity)
        _ = (256 * 12 * C * Real.log S ^ (2 : ℕ) *
              Real.exp (-(Real.log S / 3840000))) * S := by ring
        _ ≤ 1 * S := mul_le_mul_of_nonneg_right hexp_top hS0.le
        _ = S := one_mul S
    have hp2 : (16 * Real.log S) ^ (2 : ℕ) * (C * S ^ ((3 : ℝ) / 4)) ≤ S := by
      have hL23 : Real.log S ^ (2 : ℕ) ≤ Real.log S ^ (3 : ℕ) := by
        calc Real.log S ^ (2 : ℕ) = Real.log S ^ (2 : ℕ) * 1 := (mul_one _).symm
          _ ≤ Real.log S ^ (2 : ℕ) * Real.log S :=
              mul_le_mul_of_nonneg_left hL1 (sq_nonneg _)
          _ = Real.log S ^ (3 : ℕ) := by ring
      calc (16 * Real.log S) ^ (2 : ℕ) * (C * S ^ ((3 : ℝ) / 4))
          = 256 * C * Real.log S ^ (2 : ℕ) * S ^ ((3 : ℝ) / 4) := by ring
        _ ≤ 256 * C * Real.log S ^ (3 : ℕ) * S ^ ((3 : ℝ) / 4) :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hL23 (by positivity)) (by positivity)
        _ ≤ S := hsub2
    linarith [show (16 * Real.log S) ^ (2 : ℕ) *
        (12 * C * S * Real.exp (-((2 : ℝ) ^ M * R₀ * Real.log S / 120000)) +
          C * S ^ ((3 : ℝ) / 4)) =
      (16 * Real.log S) ^ (2 : ℕ) *
        (12 * C * S * Real.exp (-((2 : ℝ) ^ M * R₀ * Real.log S / 120000))) +
      (16 * Real.log S) ^ (2 : ℕ) * (C * S ^ ((3 : ℝ) / 4)) by ring]
  have hbase_eq :
      (105 * (R₀ * Real.log S)) ^ (2 : ℕ) * S =
        105 ^ (2 : ℕ) * (R₀ * Real.log S) ^ (2 : ℕ) * S := by ring
  have hC₁_eq :
      (105 ^ (2 : ℕ) + 4 * 105 ^ (2 : ℕ) * 12 * C * 17 + 3) *
          (R₀ * Real.log S) ^ (2 : ℕ) * S =
        105 ^ (2 : ℕ) * (R₀ * Real.log S) ^ (2 : ℕ) * S +
          (4 * 105 ^ (2 : ℕ) * 12 * C * 17) * (R₀ * Real.log S) ^ (2 : ℕ) * S +
          (R₀ * Real.log S) ^ (2 : ℕ) * S +
          2 * (R₀ * Real.log S) ^ (2 : ℕ) * S := by ring
  linarith [hint_Icc_le, hmaj_eval, hmid_split, hmid_exp, hmid_pow, htop_bound, hS_le_RL,
    hbase_eq, hC₁_eq]

/-! ## Global `L²` bound and Lorentzian pair sum on `dyadicZeroWindow T` -/

/-- All multiplicity copies of `ξ`-zeros with ordinate in `[T, 2T]`. -/
def dyadicZeroWindow (T : ℝ) : Finset XiZeroCopy :=
  (zeroWindow (2 * T)).filter (fun q => T ≤ (q.1 : ℂ).im)

theorem mem_dyadicZeroWindow {T : ℝ} (hT : 0 < T) {q : XiZeroCopy} :
    q ∈ dyadicZeroWindow T ↔ T ≤ (q.1 : ℂ).im ∧ (q.1 : ℂ).im ≤ 2 * T := by
  rw [dyadicZeroWindow, Finset.mem_filter, mem_zeroWindow]
  constructor
  · rintro ⟨⟨_, hhi⟩, hlo⟩; exact ⟨hlo, hhi⟩
  · rintro ⟨hlo, hhi⟩; exact ⟨⟨by linarith, hhi⟩, hlo⟩

theorem card_dyadicZeroWindow_le (T : ℝ) :
    (dyadicZeroWindow T).card ≤ (zeroWindow (2 * T)).card :=
  Finset.card_filter_le _ _

theorem setIntegral_Iic_windowNarrowSum_sq_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r) :
    (∫ t in Iic (T / 2),
        (windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t) ^ (2 : ℕ)) ≤
      8 * Real.pi * r ^ (4 : ℕ) * ((dyadicZeroWindow T).card : ℝ) ^ (2 : ℕ) / T ^ (3 : ℕ) := by
  have hc : 0 < T / 2 := half_pos hT
  have hpt : ∀ t ∈ Iic (T / 2),
      (windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t) ^ (2 : ℕ) ≤
        (((dyadicZeroWindow T).card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / (T / 2) ^ (2 : ℕ)) *
          (((T / 2) ^ (2 : ℕ) + (t - T / 2) ^ (2 : ℕ))⁻¹) := by
    intro t ht
    have htle : t ≤ T / 2 := ht
    have hterm1 : ∀ q ∈ dyadicZeroWindow T,
        r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ)) ≤
          r ^ (2 : ℕ) / (T / 2) ^ (2 : ℕ) := by
      intro q hq
      have hqlo : T ≤ (q.1 : ℂ).im := ((mem_dyadicZeroWindow hT).mp hq).1
      have hdist : T / 2 ≤ (q.1 : ℂ).im - t := by linarith
      have hsq : (T / 2) ^ (2 : ℕ) ≤ r ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ) := by
        have h1 : (T / 2) ^ (2 : ℕ) ≤ ((q.1 : ℂ).im - t) ^ (2 : ℕ) :=
          pow_le_pow_left₀ hc.le hdist 2
        have h2 : ((q.1 : ℂ).im - t) ^ (2 : ℕ) = (t - (q.1 : ℂ).im) ^ (2 : ℕ) := by ring
        linarith [sq_nonneg r]
      exact div_le_div_of_nonneg_left (sq_nonneg r) (by positivity) hsq
    have hterm2 : ∀ q ∈ dyadicZeroWindow T,
        r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ)) ≤
          r ^ (2 : ℕ) * (((T / 2) ^ (2 : ℕ) + (t - T / 2) ^ (2 : ℕ))⁻¹) := by
      intro q hq
      have hqlo : T ≤ (q.1 : ℂ).im := ((mem_dyadicZeroWindow hT).mp hq).1
      have ha : T / 2 ≤ (q.1 : ℂ).im - T / 2 := by linarith
      have hb : 0 ≤ T / 2 - t := by linarith
      have hsq : (T / 2) ^ (2 : ℕ) + (t - T / 2) ^ (2 : ℕ) ≤
          r ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ) := by
        have ha2 : (T / 2) ^ (2 : ℕ) ≤ ((q.1 : ℂ).im - T / 2) ^ (2 : ℕ) :=
          pow_le_pow_left₀ hc.le ha 2
        have hcross : 0 ≤ 2 * ((q.1 : ℂ).im - T / 2) * (T / 2 - t) :=
          mul_nonneg (mul_nonneg (by norm_num) (hc.le.trans ha)) hb
        have hexpand : (t - (q.1 : ℂ).im) ^ (2 : ℕ) =
            ((q.1 : ℂ).im - T / 2) ^ (2 : ℕ) + 2 * ((q.1 : ℂ).im - T / 2) * (T / 2 - t) +
              (t - T / 2) ^ (2 : ℕ) := by ring
        linarith [sq_nonneg r]
      rw [← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left (sq_nonneg r) (by positivity) hsq
    have hG0 := windowNarrowSum_nonneg (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t
    have hG1 : windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t ≤
        ((dyadicZeroWindow T).card : ℝ) * (r ^ (2 : ℕ) / (T / 2) ^ (2 : ℕ)) := by
      calc windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t
          ≤ ∑ _q ∈ dyadicZeroWindow T, r ^ (2 : ℕ) / (T / 2) ^ (2 : ℕ) := Finset.sum_le_sum hterm1
        _ = ((dyadicZeroWindow T).card : ℝ) * (r ^ (2 : ℕ) / (T / 2) ^ (2 : ℕ)) := by simp
    have hG2 : windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t ≤
        ((dyadicZeroWindow T).card : ℝ) *
          (r ^ (2 : ℕ) * (((T / 2) ^ (2 : ℕ) + (t - T / 2) ^ (2 : ℕ))⁻¹)) := by
      calc windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t
          ≤ ∑ _q ∈ dyadicZeroWindow T,
              r ^ (2 : ℕ) * (((T / 2) ^ (2 : ℕ) + (t - T / 2) ^ (2 : ℕ))⁻¹) :=
            Finset.sum_le_sum hterm2
        _ = ((dyadicZeroWindow T).card : ℝ) *
              (r ^ (2 : ℕ) * (((T / 2) ^ (2 : ℕ) + (t - T / 2) ^ (2 : ℕ))⁻¹)) := by simp
    calc (windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t) ^ (2 : ℕ)
        = windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t *
            windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t := sq _
      _ ≤ (((dyadicZeroWindow T).card : ℝ) * (r ^ (2 : ℕ) / (T / 2) ^ (2 : ℕ))) *
            (((dyadicZeroWindow T).card : ℝ) *
              (r ^ (2 : ℕ) * (((T / 2) ^ (2 : ℕ) + (t - T / 2) ^ (2 : ℕ))⁻¹))) :=
          mul_le_mul hG1 hG2 hG0 (by positivity)
      _ = (((dyadicZeroWindow T).card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / (T / 2) ^ (2 : ℕ)) *
            (((T / 2) ^ (2 : ℕ) + (t - T / 2) ^ (2 : ℕ))⁻¹) := by ring
  have hint_rhs : Integrable (fun t : ℝ =>
      (((dyadicZeroWindow T).card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / (T / 2) ^ (2 : ℕ)) *
        (((T / 2) ^ (2 : ℕ) + (t - T / 2) ^ (2 : ℕ))⁻¹)) :=
    (integrable_inv_shifted_sq_add_sq hc (T / 2)).const_mul _
  calc ∫ t in Iic (T / 2),
        (windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t) ^ (2 : ℕ)
      ≤ ∫ t in Iic (T / 2),
          (((dyadicZeroWindow T).card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / (T / 2) ^ (2 : ℕ)) *
            (((T / 2) ^ (2 : ℕ) + (t - T / 2) ^ (2 : ℕ))⁻¹) :=
        MeasureTheory.setIntegral_mono_on
          (integrable_windowNarrowSum_sq (dyadicZeroWindow T) _ hr).integrableOn
          hint_rhs.integrableOn measurableSet_Iic hpt
    _ ≤ ∫ t : ℝ,
          (((dyadicZeroWindow T).card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / (T / 2) ^ (2 : ℕ)) *
            (((T / 2) ^ (2 : ℕ) + (t - T / 2) ^ (2 : ℕ))⁻¹) :=
        MeasureTheory.setIntegral_le_integral hint_rhs
          (Filter.Eventually.of_forall fun _ => by positivity)
    _ = (((dyadicZeroWindow T).card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / (T / 2) ^ (2 : ℕ)) *
          (Real.pi / (T / 2)) := by
        rw [MeasureTheory.integral_const_mul, integral_inv_shifted_sq_add_sq hc (T / 2)]
    _ = 8 * Real.pi * r ^ (4 : ℕ) * ((dyadicZeroWindow T).card : ℝ) ^ (2 : ℕ) / T ^ (3 : ℕ) := by
        field_simp; ring

theorem setIntegral_Ici_windowNarrowSum_sq_le {T r : ℝ} (hT : 0 < T) (hr : 0 < r) :
    (∫ t in Ici (4 * T),
        (windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t) ^ (2 : ℕ)) ≤
      8 * Real.pi * r ^ (4 : ℕ) * ((dyadicZeroWindow T).card : ℝ) ^ (2 : ℕ) / T ^ (3 : ℕ) := by
  have hc : 0 < T / 2 := half_pos hT
  have hpt : ∀ t ∈ Ici (4 * T),
      (windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t) ^ (2 : ℕ) ≤
        (((dyadicZeroWindow T).card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / (T / 2) ^ (2 : ℕ)) *
          (((T / 2) ^ (2 : ℕ) + (t - 4 * T) ^ (2 : ℕ))⁻¹) := by
    intro t ht
    have htge : 4 * T ≤ t := ht
    have hterm1 : ∀ q ∈ dyadicZeroWindow T,
        r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ)) ≤
          r ^ (2 : ℕ) / (T / 2) ^ (2 : ℕ) := by
      intro q hq
      have hqhi : (q.1 : ℂ).im ≤ 2 * T := ((mem_dyadicZeroWindow hT).mp hq).2
      have hdist : T / 2 ≤ t - (q.1 : ℂ).im := by linarith
      have hsq : (T / 2) ^ (2 : ℕ) ≤ r ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ) := by
        have h1 : (T / 2) ^ (2 : ℕ) ≤ (t - (q.1 : ℂ).im) ^ (2 : ℕ) :=
          pow_le_pow_left₀ hc.le hdist 2
        linarith [sq_nonneg r]
      exact div_le_div_of_nonneg_left (sq_nonneg r) (by positivity) hsq
    have hterm2 : ∀ q ∈ dyadicZeroWindow T,
        r ^ (2 : ℕ) / (r ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ)) ≤
          r ^ (2 : ℕ) * (((T / 2) ^ (2 : ℕ) + (t - 4 * T) ^ (2 : ℕ))⁻¹) := by
      intro q hq
      have hqhi : (q.1 : ℂ).im ≤ 2 * T := ((mem_dyadicZeroWindow hT).mp hq).2
      have ha : T / 2 ≤ 4 * T - (q.1 : ℂ).im := by linarith
      have hb : 0 ≤ t - 4 * T := by linarith
      have hsq : (T / 2) ^ (2 : ℕ) + (t - 4 * T) ^ (2 : ℕ) ≤
          r ^ (2 : ℕ) + (t - (q.1 : ℂ).im) ^ (2 : ℕ) := by
        have ha2 : (T / 2) ^ (2 : ℕ) ≤ (4 * T - (q.1 : ℂ).im) ^ (2 : ℕ) :=
          pow_le_pow_left₀ hc.le ha 2
        have hcross : 0 ≤ 2 * (4 * T - (q.1 : ℂ).im) * (t - 4 * T) :=
          mul_nonneg (mul_nonneg (by norm_num) (hc.le.trans ha)) hb
        have hexpand : (t - (q.1 : ℂ).im) ^ (2 : ℕ) =
            (4 * T - (q.1 : ℂ).im) ^ (2 : ℕ) + 2 * (4 * T - (q.1 : ℂ).im) * (t - 4 * T) +
              (t - 4 * T) ^ (2 : ℕ) := by ring
        linarith [sq_nonneg r]
      rw [← div_eq_mul_inv]
      exact div_le_div_of_nonneg_left (sq_nonneg r) (by positivity) hsq
    have hG0 := windowNarrowSum_nonneg (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t
    have hG1 : windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t ≤
        ((dyadicZeroWindow T).card : ℝ) * (r ^ (2 : ℕ) / (T / 2) ^ (2 : ℕ)) := by
      calc windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t
          ≤ ∑ _q ∈ dyadicZeroWindow T, r ^ (2 : ℕ) / (T / 2) ^ (2 : ℕ) := Finset.sum_le_sum hterm1
        _ = ((dyadicZeroWindow T).card : ℝ) * (r ^ (2 : ℕ) / (T / 2) ^ (2 : ℕ)) := by simp
    have hG2 : windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t ≤
        ((dyadicZeroWindow T).card : ℝ) *
          (r ^ (2 : ℕ) * (((T / 2) ^ (2 : ℕ) + (t - 4 * T) ^ (2 : ℕ))⁻¹)) := by
      calc windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t
          ≤ ∑ _q ∈ dyadicZeroWindow T,
              r ^ (2 : ℕ) * (((T / 2) ^ (2 : ℕ) + (t - 4 * T) ^ (2 : ℕ))⁻¹) :=
            Finset.sum_le_sum hterm2
        _ = ((dyadicZeroWindow T).card : ℝ) *
              (r ^ (2 : ℕ) * (((T / 2) ^ (2 : ℕ) + (t - 4 * T) ^ (2 : ℕ))⁻¹)) := by simp
    calc (windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t) ^ (2 : ℕ)
        = windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t *
            windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t := sq _
      _ ≤ (((dyadicZeroWindow T).card : ℝ) * (r ^ (2 : ℕ) / (T / 2) ^ (2 : ℕ))) *
            (((dyadicZeroWindow T).card : ℝ) *
              (r ^ (2 : ℕ) * (((T / 2) ^ (2 : ℕ) + (t - 4 * T) ^ (2 : ℕ))⁻¹))) :=
          mul_le_mul hG1 hG2 hG0 (by positivity)
      _ = (((dyadicZeroWindow T).card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / (T / 2) ^ (2 : ℕ)) *
            (((T / 2) ^ (2 : ℕ) + (t - 4 * T) ^ (2 : ℕ))⁻¹) := by ring
  have hint_rhs : Integrable (fun t : ℝ =>
      (((dyadicZeroWindow T).card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / (T / 2) ^ (2 : ℕ)) *
        (((T / 2) ^ (2 : ℕ) + (t - 4 * T) ^ (2 : ℕ))⁻¹)) :=
    (integrable_inv_shifted_sq_add_sq hc (4 * T)).const_mul _
  calc ∫ t in Ici (4 * T),
        (windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) r t) ^ (2 : ℕ)
      ≤ ∫ t in Ici (4 * T),
          (((dyadicZeroWindow T).card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / (T / 2) ^ (2 : ℕ)) *
            (((T / 2) ^ (2 : ℕ) + (t - 4 * T) ^ (2 : ℕ))⁻¹) :=
        MeasureTheory.setIntegral_mono_on
          (integrable_windowNarrowSum_sq (dyadicZeroWindow T) _ hr).integrableOn
          hint_rhs.integrableOn measurableSet_Ici hpt
    _ ≤ ∫ t : ℝ,
          (((dyadicZeroWindow T).card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / (T / 2) ^ (2 : ℕ)) *
            (((T / 2) ^ (2 : ℕ) + (t - 4 * T) ^ (2 : ℕ))⁻¹) :=
        MeasureTheory.setIntegral_le_integral hint_rhs
          (Filter.Eventually.of_forall fun _ => by positivity)
    _ = (((dyadicZeroWindow T).card : ℝ) ^ (2 : ℕ) * r ^ (4 : ℕ) / (T / 2) ^ (2 : ℕ)) *
          (Real.pi / (T / 2)) := by
        rw [MeasureTheory.integral_const_mul, integral_inv_shifted_sq_add_sq hc (4 * T)]
    _ = 8 * Real.pi * r ^ (4 : ℕ) * ((dyadicZeroWindow T).card : ℝ) ^ (2 : ℕ) / T ^ (3 : ℕ) := by
        field_simp; ring

/-- **Unconditional Lorentzian pair-sum bound on `dyadicZeroWindow T`.** There exist `C_pair > 0`
and `κ₂ ≥ 120000` such that eventually for large `T`, for every `0 < R₀ ≤ 1/32` with
`κ₂ ≤ R₀ log T`,

`Σ_{q₁, q₂ ∈ dyadicZeroWindow T} R₀² / (R₀² + (γ_{q₁} − γ_{q₂})²) ≤ C_pair (R₀ log T) T log T`. -/
theorem exists_dyadicZeroWindow_lorentzPairSum_le :
    ∃ C_pair κ₂ : ℝ, 0 < C_pair ∧ 120000 ≤ κ₂ ∧ ∀ᶠ T : ℝ in atTop,
      ∀ R₀ : ℝ, 0 < R₀ → R₀ ≤ 1 / 32 → κ₂ ≤ R₀ * Real.log T →
        (∑ q₁ ∈ dyadicZeroWindow T, ∑ q₂ ∈ dyadicZeroWindow T,
            R₀ ^ (2 : ℕ) /
              (R₀ ^ (2 : ℕ) + ((q₁.1 : ℂ).im - (q₂.1 : ℂ).im) ^ (2 : ℕ))) ≤
          C_pair * (R₀ * Real.log T) * (T * Real.log T) := by
  obtain ⟨C₁, κ₂, hC₁, hκ₂, hev_Icc⟩ := exists_integral_Icc_windowNarrowSum_sq_le
  refine ⟨4 * (11 * C₁ + 2) / Real.pi, κ₂, by positivity, hκ₂, ?_⟩
  obtain ⟨S₀, hS₀⟩ := eventually_atTop.mp hev_Icc
  obtain ⟨T₀_w, hT₀_w⟩ := eventually_atTop.mp eventually_card_zeroWindow_le
  have htail_small : ∀ᶠ T : ℝ in atTop,
      8 * Real.pi * Real.log T ^ (2 : ℕ) ≤ T ^ (2 : ℕ) := by
    have h1 := (isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num)).bound
      (show (0 : ℝ) < 1 / (8 * Real.pi + 1) by positivity)
    filter_upwards [h1, eventually_ge_atTop (1 : ℝ)] with T hT hT1
    have hT0 : 0 < T := by linarith
    have hL0 : 0 ≤ Real.log T := Real.log_nonneg hT1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, Real.rpow_one, abs_of_nonneg hL0,
      abs_of_nonneg hT0.le] at hT
    have hsq : Real.log T ^ (2 : ℕ) ≤ (1 / (8 * Real.pi + 1)) ^ (2 : ℕ) * T ^ (2 : ℕ) := by
      calc Real.log T ^ (2 : ℕ)
          ≤ (1 / (8 * Real.pi + 1) * T) ^ (2 : ℕ) := pow_le_pow_left₀ hL0 hT 2
        _ = (1 / (8 * Real.pi + 1)) ^ (2 : ℕ) * T ^ (2 : ℕ) := by ring
    have hc_le : 8 * Real.pi * (1 / (8 * Real.pi + 1)) ^ (2 : ℕ) ≤ 1 := by
      have hle1 : 1 / (8 * Real.pi + 1) ≤ 1 :=
        div_le_one_of_le₀ (by linarith [Real.pi_pos]) (by positivity)
      calc 8 * Real.pi * (1 / (8 * Real.pi + 1)) ^ (2 : ℕ)
          = 8 * Real.pi * (1 / (8 * Real.pi + 1)) * (1 / (8 * Real.pi + 1)) := by ring
        _ ≤ 8 * Real.pi * (1 / (8 * Real.pi + 1)) * 1 :=
            mul_le_mul_of_nonneg_left hle1 (by positivity)
        _ ≤ (8 * Real.pi + 1) * (1 / (8 * Real.pi + 1)) := by
            rw [mul_one]
            exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
        _ = 1 := by field_simp
    calc 8 * Real.pi * Real.log T ^ (2 : ℕ)
        ≤ 8 * Real.pi * ((1 / (8 * Real.pi + 1)) ^ (2 : ℕ) * T ^ (2 : ℕ)) :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = (8 * Real.pi * (1 / (8 * Real.pi + 1)) ^ (2 : ℕ)) * T ^ (2 : ℕ) := by ring
      _ ≤ 1 * T ^ (2 : ℕ) := mul_le_mul_of_nonneg_right hc_le (sq_nonneg T)
      _ = T ^ (2 : ℕ) := one_mul _
  filter_upwards [eventually_ge_atTop (max (max (2 * S₀) (T₀_w / 2)) 4), htail_small]
    with T hTbig htail R₀ hR₀ hR₀32 hκ
  have hT4 : 4 ≤ T := (le_max_right _ _).trans hTbig
  have hT0 : 0 < T := by linarith
  have hS_half : S₀ ≤ T / 2 := by
    have := (le_trans (le_max_left _ _) (le_max_left _ _)).trans hTbig; linarith
  have hcard : ((zeroWindow (2 * T)).card : ℝ) ≤ (2 * T) * Real.log (2 * T) / 5 := by
    have := (le_trans (le_max_right _ _) (le_max_left _ _)).trans hTbig
    exact hT₀_w (2 * T) (by linarith)
  have hr0 : 0 < R₀ / 2 := half_pos hR₀
  have hr1 : R₀ / 2 ≤ 1 := by linarith
  have hRL1 : 1 ≤ (R₀ * Real.log T) ^ (2 : ℕ) := one_le_pow₀ (by linarith)
  have hlog_half_ge : Real.log T ≤ 2 * Real.log (T / 2) := by
    have hsq_ge : T ≤ (T / 2) ^ (2 : ℕ) := by
      have : 0 ≤ T * (T - 4) := mul_nonneg hT0.le (by linarith)
      linarith [show (T / 2) ^ (2 : ℕ) - T = T * (T - 4) / 4 by ring]
    have h1 := Real.log_le_log hT0 hsq_ge
    rw [Real.log_pow] at h1
    simpa using h1
  have hlog_half_le : Real.log (T / 2) ≤ Real.log T :=
    Real.log_le_log (half_pos hT0) (by linarith)
  have hκ_half : κ₂ ≤ (2 * R₀) * Real.log (T / 2) := by
    have := mul_le_mul_of_nonneg_left hlog_half_ge hR₀.le
    linarith [show R₀ * (2 * Real.log (T / 2)) = (2 * R₀) * Real.log (T / 2) by ring]
  have hIcc1 :
      (∫ t in Icc (T / 2) T,
          (windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) (R₀ / 2) t) ^ (2 : ℕ)) ≤
        2 * C₁ * (R₀ * Real.log T) ^ (2 : ℕ) * T := by
    have hmono :
        (∫ t in Icc (T / 2) T,
            (windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) (R₀ / 2) t) ^ (2 : ℕ)) ≤
          ∫ t in Icc (T / 2) (2 * (T / 2)),
            (windowNarrowSum (dyadicZeroWindow T)
              (fun q => (q.1 : ℂ).im) ((2 * R₀) / 2) t) ^ (2 : ℕ) := by
      rw [show 2 * (T / 2) = T by ring]
      refine MeasureTheory.setIntegral_mono_on
        (integrable_windowNarrowSum_sq (dyadicZeroWindow T) _ hr0).integrableOn
        (integrable_windowNarrowSum_sq (dyadicZeroWindow T) _ (by positivity)).integrableOn
        measurableSet_Icc fun t _ => ?_
      exact pow_le_pow_left₀ (windowNarrowSum_nonneg (dyadicZeroWindow T) _ (R₀ / 2) t)
        (windowNarrowSum_mono_radius (dyadicZeroWindow T) _ hr0 (by linarith) t) 2
    have hbd := hS₀ (T / 2) hS_half (2 * R₀) (by positivity) (by linarith) hκ_half
      (dyadicZeroWindow T)
    have hsq_le : ((2 * R₀) * Real.log (T / 2)) ^ (2 : ℕ) ≤ 4 * (R₀ * Real.log T) ^ (2 : ℕ) := by
      have h1 : (2 * R₀) * Real.log (T / 2) ≤ 2 * (R₀ * Real.log T) := by
        have := mul_le_mul_of_nonneg_left hlog_half_le (show 0 ≤ 2 * R₀ by positivity)
        linarith [show (2 * R₀) * Real.log T = 2 * (R₀ * Real.log T) by ring]
      calc ((2 * R₀) * Real.log (T / 2)) ^ (2 : ℕ)
          ≤ (2 * (R₀ * Real.log T)) ^ (2 : ℕ) :=
            pow_le_pow_left₀ (by linarith [hκ_half, hκ₂]) h1 2
        _ = 4 * (R₀ * Real.log T) ^ (2 : ℕ) := by ring
    calc ∫ t in Icc (T / 2) T,
          (windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) (R₀ / 2) t) ^ (2 : ℕ)
        ≤ C₁ * ((2 * R₀) * Real.log (T / 2)) ^ (2 : ℕ) * (T / 2) := hmono.trans hbd
      _ ≤ C₁ * (4 * (R₀ * Real.log T) ^ (2 : ℕ)) * (T / 2) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq_le hC₁.le) (by positivity)
      _ = 2 * C₁ * (R₀ * Real.log T) ^ (2 : ℕ) * T := by ring
  have hIcc2 :
      (∫ t in Icc T (2 * T),
          (windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) (R₀ / 2) t) ^ (2 : ℕ)) ≤
        C₁ * (R₀ * Real.log T) ^ (2 : ℕ) * T :=
    hS₀ T (by linarith) R₀ hR₀ (by linarith) hκ (dyadicZeroWindow T)
  have hlog_2T_ge : Real.log T ≤ Real.log (2 * T) :=
    Real.log_le_log hT0 (by linarith)
  have hlog_2T_le : Real.log (2 * T) ≤ 2 * Real.log T := by
    rw [Real.log_mul (by norm_num) hT0.ne']
    have hlog2 : Real.log 2 ≤ Real.log T := Real.log_le_log (by norm_num) (by linarith)
    linarith
  have hIcc3 :
      (∫ t in Icc (2 * T) (4 * T),
          (windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) (R₀ / 2) t) ^ (2 : ℕ)) ≤
        8 * C₁ * (R₀ * Real.log T) ^ (2 : ℕ) * T := by
    have hbd := hS₀ (2 * T) (by linarith) R₀ hR₀ (by linarith)
      (hκ.trans (mul_le_mul_of_nonneg_left hlog_2T_ge hR₀.le)) (dyadicZeroWindow T)
    rw [show 2 * (2 * T) = 4 * T by ring] at hbd
    have hsq_le : (R₀ * Real.log (2 * T)) ^ (2 : ℕ) ≤ 4 * (R₀ * Real.log T) ^ (2 : ℕ) := by
      have h1 : R₀ * Real.log (2 * T) ≤ 2 * (R₀ * Real.log T) := by
        have := mul_le_mul_of_nonneg_left hlog_2T_le hR₀.le
        linarith [show R₀ * (2 * Real.log T) = 2 * (R₀ * Real.log T) by ring]
      calc (R₀ * Real.log (2 * T)) ^ (2 : ℕ)
          ≤ (2 * (R₀ * Real.log T)) ^ (2 : ℕ) :=
            pow_le_pow_left₀ (mul_nonneg hR₀.le (Real.log_nonneg (by linarith))) h1 2
        _ = 4 * (R₀ * Real.log T) ^ (2 : ℕ) := by ring
    calc ∫ t in Icc (2 * T) (4 * T),
          (windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) (R₀ / 2) t) ^ (2 : ℕ)
        ≤ C₁ * (R₀ * Real.log (2 * T)) ^ (2 : ℕ) * (2 * T) := hbd
      _ ≤ C₁ * (4 * (R₀ * Real.log T) ^ (2 : ℕ)) * (2 * T) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq_le hC₁.le) (by positivity)
      _ = 8 * C₁ * (R₀ * Real.log T) ^ (2 : ℕ) * T := by ring
  have hZcard : ((dyadicZeroWindow T).card : ℝ) ≤ T * Real.log T := by
    have hc1 : ((dyadicZeroWindow T).card : ℝ) ≤ (zeroWindow (2 * T)).card := by
      exact_mod_cast card_dyadicZeroWindow_le T
    have hc2 : (2 * T) * Real.log (2 * T) / 5 ≤ T * Real.log T := by
      have := mul_le_mul_of_nonneg_left hlog_2T_le (show 0 ≤ 2 * T by positivity)
      have hTL0 : 0 ≤ T * Real.log T := mul_nonneg hT0.le (by linarith)
      linarith [show (2 * T) * (2 * Real.log T) = 4 * (T * Real.log T) by ring]
    exact hc1.trans (hcard.trans hc2)
  have htail_val :
      8 * Real.pi * (R₀ / 2) ^ (4 : ℕ) * ((dyadicZeroWindow T).card : ℝ) ^ (2 : ℕ) / T ^ (3 : ℕ) ≤
        (R₀ * Real.log T) ^ (2 : ℕ) * T := by
    have hr4 : (R₀ / 2) ^ (4 : ℕ) ≤ 1 := pow_le_one₀ hr0.le hr1
    have hZsq : ((dyadicZeroWindow T).card : ℝ) ^ (2 : ℕ) ≤ (T * Real.log T) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) hZcard 2
    have hnum : 8 * Real.pi * (R₀ / 2) ^ (4 : ℕ) *
        ((dyadicZeroWindow T).card : ℝ) ^ (2 : ℕ) ≤ T ^ (4 : ℕ) := by
      calc 8 * Real.pi * (R₀ / 2) ^ (4 : ℕ) * ((dyadicZeroWindow T).card : ℝ) ^ (2 : ℕ)
          ≤ 8 * Real.pi * 1 * (T * Real.log T) ^ (2 : ℕ) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hr4 (by positivity)) hZsq
              (by positivity) (by positivity)
        _ = (8 * Real.pi * Real.log T ^ (2 : ℕ)) * T ^ (2 : ℕ) := by ring
        _ ≤ T ^ (2 : ℕ) * T ^ (2 : ℕ) :=
            mul_le_mul_of_nonneg_right htail (sq_nonneg T)
        _ = T ^ (4 : ℕ) := by ring
    have hdiv : 8 * Real.pi * (R₀ / 2) ^ (4 : ℕ) *
        ((dyadicZeroWindow T).card : ℝ) ^ (2 : ℕ) / T ^ (3 : ℕ) ≤ T := by
      rw [div_le_iff₀ (by positivity)]
      linarith [show T * T ^ (3 : ℕ) = T ^ (4 : ℕ) by ring]
    exact hdiv.trans ((one_mul T).symm.trans_le (mul_le_mul_of_nonneg_right hRL1 hT0.le))
  have hIic := (setIntegral_Iic_windowNarrowSum_sq_le hT0 hr0).trans htail_val
  have hIci := (setIntegral_Ici_windowNarrowSum_sq_le hT0 hr0).trans htail_val
  have htot_L2 :
      (∫ t : ℝ,
          (windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) (R₀ / 2) t) ^ (2 : ℕ)) ≤
        (11 * C₁ + 2) * (R₀ * Real.log T) ^ (2 : ℕ) * T := by
    have h5 := integral_le_five_pieces
      (integrable_windowNarrowSum_sq (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) hr0)
      (fun t => sq_nonneg (windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) (R₀ / 2) t))
      hT0
    linarith [h5, hIic, hIcc1, hIcc2, hIcc3, hIci]
  rw [lorentz_pairSum_eq_integral_windowNarrowSum_sq (dyadicZeroWindow T)
    (fun q => (q.1 : ℂ).im) hR₀]
  calc 4 / (Real.pi * R₀) *
        ∫ t : ℝ,
          (windowNarrowSum (dyadicZeroWindow T) (fun q => (q.1 : ℂ).im) (R₀ / 2) t) ^ (2 : ℕ)
      ≤ 4 / (Real.pi * R₀) * ((11 * C₁ + 2) * (R₀ * Real.log T) ^ (2 : ℕ) * T) :=
        mul_le_mul_of_nonneg_left htot_L2 (by positivity)
    _ = (4 * (11 * C₁ + 2) / Real.pi) * (R₀ * Real.log T) * (T * Real.log T) := by
        have hpi : Real.pi ≠ 0 := Real.pi_pos.ne'
        have hRne : R₀ ≠ 0 := hR₀.ne'
        field_simp

end RHTower

end
