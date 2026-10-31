import GaloisForLFunctions.SuccessorShellArithmetic.TheShellsAndThePoleCancelOnTheTopBand
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.PeriodicPairSumsOfADecreasingKernelAreLinear

/-!
# Periodic cancellation in smooth shell windows

Mean-zero periodic coefficients have bounded partial sums on every interval.
Abel summation controls the shell kernel and its first derivative, retaining
the actual window length. On visible products, the width absorbs the lattice
endpoint cost. The resulting bound is uniform up to width one quarter.
-/

open MeasureTheory Finset Filter Topology
namespace GaloisForLFunctions.SuccessorShellArithmetic
open RenormalizedArithmeticPotentialTheory RenormalizedArithmeticPotentialTheory.CompletedShell
  SpacingScaleHarmonicAnalysis ArithmeticElectrostatics
noncomputable section

/-- Bounded partial sums pay for a smooth lattice window through its first derivative. -/
theorem abs_weighted_lattice_sum_le_of_deriv
    (ψ : ℕ → ℝ) {F F' : ℝ → ℝ} {a P M K : ℝ} {L : ℕ}
    (hP : ∀ k ≤ L, |∑ i ∈ range k, ψ i| ≤ P)
    (hF : ∀ t ∈ Set.Icc a (a + L), |F t| ≤ M)
    (hd : ∀ t ∈ Set.Icc a (a + L), HasDerivAt F (F' t) t)
    (hK : ∀ t ∈ Set.Icc a (a + L), |F' t| ≤ K) :
    |∑ i ∈ range L, F (a + i) * ψ i| ≤ P * (M + L * K) := by
  have hP0 : 0 ≤ P := by simpa only [range_zero, sum_empty, abs_zero] using hP 0 (Nat.zero_le _)
  have ha : a ∈ Set.Icc a (a + L) := ⟨le_rfl, le_add_of_nonneg_right (Nat.cast_nonneg _)⟩
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK a ha)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hF a ha)
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp only [range_zero, sum_empty, abs_zero, Nat.cast_zero, zero_mul, add_zero]
    exact mul_nonneg hP0 hM0
  have he : |F (a + (L - 1 : ℕ))| ≤ M := hF _ ⟨le_add_of_nonneg_right (Nat.cast_nonneg _), by
    have h := Nat.cast_le (α := ℝ).mpr (Nat.sub_le L 1)
    linarith only [h]⟩
  have hdiff (i : ℕ) (hi : i ∈ range (L - 1)) :
      |F (a + (i + 1 : ℕ)) - F (a + i)| ≤ K := by
    have hiL : i + 1 ≤ L := by have := mem_range.mp hi; omega
    have hx : a + i ∈ Set.Icc a (a + L) :=
      ⟨le_add_of_nonneg_right (Nat.cast_nonneg _),
        (by have h : (i : ℝ) ≤ L := by exact_mod_cast Nat.le_of_succ_le hiL
            linarith only [h])⟩
    have hy : a + (i + 1 : ℕ) ∈ Set.Icc a (a + L) :=
      ⟨le_add_of_nonneg_right (Nat.cast_nonneg _),
        (by have h : ((i + 1 : ℕ) : ℝ) ≤ L := by exact_mod_cast hiL
            linarith only [h])⟩
    have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun t ht => (hd t ht).hasDerivWithinAt)
      (fun t ht => hK t ht) (convex_Icc _ _) hx hy
    have hlen : ‖(a + (i + 1 : ℕ)) - (a + i)‖ = 1 := by
      rw [show (a + (i + 1 : ℕ)) - (a + i) = (1 : ℝ) by push_cast; ring,
        norm_one]
    rw [hlen, mul_one, Real.norm_eq_abs] at h
    exact h
  have hs : (∑ i ∈ range (L - 1), |F (a + (i + 1 : ℕ)) - F (a + i)|) ≤ L * K := by
    calc
      _ ≤ ∑ _i ∈ range (L - 1), K := sum_le_sum hdiff
      _ = ((L - 1 : ℕ) : ℝ) * K := by simp only [sum_const, card_range, nsmul_eq_mul]
      _ ≤ L * K := mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.sub_le L 1) hK0
  exact (abs_sum_range_mul_le ψ (fun i => F (a + i)) L hP).trans
    (mul_le_mul_of_nonneg_left (add_le_add he hs) hP0)


theorem abs_periodic_lattice_sum_le_of_deriv
    {q : ℕ} (hq : 1 ≤ q) (ψ : ℕ → ℝ) {B : ℝ}
    (hper : ∀ n, ψ (n + q) = ψ n) (hmean : ∑ r ∈ range q, ψ r = 0)
    (hB : ∀ n, |ψ n| ≤ B) {F F' : ℝ → ℝ} {M K : ℝ} (A L : ℕ)
    (hF : ∀ t ∈ Set.Icc (A : ℝ) (A + L), |F t| ≤ M)
    (hd : ∀ t ∈ Set.Icc (A : ℝ) (A + L), HasDerivAt F (F' t) t)
    (hK : ∀ t ∈ Set.Icc (A : ℝ) (A + L), |F' t| ≤ K) :
    |∑ i ∈ range L, F ((A : ℝ) + i) * ψ (A + i)| ≤
      (2 * q * B) * (M + L * K) := by
  apply abs_weighted_lattice_sum_le_of_deriv (fun i => ψ (A + i)) _ hF hd hK
  intro k _
  have hm : (∑ i ∈ range q, ψ (A + i)) = 0 :=
    (sum_range_shift_of_periodic ψ hper A).trans hmean
  have hp : ∀ i, ψ (A + (i + q)) = ψ (A + i) := fun i => by
    simpa only [Nat.add_assoc] using hper (A + i)
  simpa only [hm, zero_div, mul_zero, sub_zero] using
    abs_sum_range_sub_mul_mean_le hq (fun i => ψ (A + i)) hp (fun i => hB (A + i)) k

/-- The smooth factor multiplying a periodic top-band partner. -/
def shellPartnerKernel (g : ℝ → ℝ) (ℓ : ℕ) (t : ℝ) : ℝ :=
  (Real.sqrt t)⁻¹ * bumpCorr g (Real.log t - Real.log ℓ)

theorem hasDerivAt_shellPartnerKernel {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    {w : ℝ} (hw : 0 < w) (ℓ : ℕ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (shellPartnerKernel (SpacingScaleHarmonicAnalysis.atomDilate φ w) ℓ)
      ((t * Real.sqrt t)⁻¹ *
        (deriv (shellAutocorr φ) ((Real.log t - Real.log ℓ) / w) -
          bumpCorr (SpacingScaleHarmonicAnalysis.atomDilate φ w) (Real.log t - Real.log ℓ) / 2)) t := by
  have hs : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hlog := Real.hasDerivAt_log ht.ne'
  have hinv := (Real.hasDerivAt_sqrt ht.ne').inv hs.ne'
  have hβ := (hasDerivAt_bumpCorr_atomDilate hφ hsupp hw (Real.log t - Real.log ℓ)).comp t
    (hlog.sub_const (Real.log ℓ))
  have h := hinv.mul hβ
  have hf : shellPartnerKernel (SpacingScaleHarmonicAnalysis.atomDilate φ w) ℓ =
      (fun x => (Real.sqrt x)⁻¹) *
        (bumpCorr (SpacingScaleHarmonicAnalysis.atomDilate φ w) ∘
          fun x => Real.log x - Real.log ℓ) := rfl
  rw [hf]
  refine h.congr_deriv ?_
  have hsq : Real.sqrt t ^ 2 = t := Real.sq_sqrt ht.le
  simp only [Pi.inv_apply, Function.comp]
  field_simp
  rw [hsq]
  ring


theorem abs_deriv_shellPartnerKernel_le {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    {w A₁ : ℝ} (hw : 0 < w) (hA₁ : ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁)
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) {t : ℝ} (ht : t ∈ Set.Icc ((ℓ : ℝ) / 2) (2 * ℓ)) :
    |(t * Real.sqrt t)⁻¹ *
      (deriv (shellAutocorr φ) ((Real.log t - Real.log ℓ) / w) -
        bumpCorr (atomDilate φ w) (Real.log t - Real.log ℓ) / 2)| ≤
      ((ℓ : ℝ) / 2 * Real.sqrt ((ℓ : ℝ) / 2))⁻¹ *
        ((∫ u, atomDilate φ w u ^ 2) + A₁) := by
  have hℓR : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓ0 : (0 : ℝ) < ℓ / 2 := by linarith only [hℓR]
  have ht0 : 0 < t := hℓ0.trans_le ht.1
  have hβ : |bumpCorr (atomDilate φ w) (Real.log t - Real.log ℓ)| ≤
      ∫ u, atomDilate φ w u ^ 2 := by
    rw [bumpCorr_atomDilate_eq hw, abs_mul, abs_of_pos hw, integral_atomDilate_sq hw]
    exact mul_le_mul_of_nonneg_left
      (abs_bumpCorr_le hφ.continuous
          (HasCompactSupport.intro isCompact_Icc (fun u hu => hsupp u hu))
          ((Real.log t - Real.log ℓ) / w)) hw.le
  have hG : 0 ≤ ∫ u, atomDilate φ w u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hden : ((ℓ : ℝ) / 2 * Real.sqrt ((ℓ : ℝ) / 2)) ≤ t * Real.sqrt t :=
    mul_le_mul ht.1 (Real.sqrt_le_sqrt ht.1) (Real.sqrt_nonneg _) ht0.le
  have hinv : (t * Real.sqrt t)⁻¹ ≤ ((ℓ : ℝ) / 2 * Real.sqrt ((ℓ : ℝ) / 2))⁻¹ :=
    inv_anti₀ (mul_pos hℓ0 (Real.sqrt_pos.mpr hℓ0)) hden
  have hb : |deriv (shellAutocorr φ) ((Real.log t - Real.log ℓ) / w) -
      bumpCorr (atomDilate φ w) (Real.log t - Real.log ℓ) / 2| ≤
      (∫ u, atomDilate φ w u ^ 2) + A₁ := by
    calc
      _ ≤ |deriv (shellAutocorr φ) ((Real.log t - Real.log ℓ) / w)| +
          |bumpCorr (atomDilate φ w) (Real.log t - Real.log ℓ) / 2| := abs_sub _ _
      _ ≤ A₁ + (∫ u, atomDilate φ w u ^ 2) / 2 := by
        rw [abs_div, abs_two]
        exact add_le_add (hA₁ _) (div_le_div_of_nonneg_right hβ (by norm_num))
      _ ≤ _ := by linarith only [hG]
  rw [abs_mul, abs_of_pos (inv_pos.mpr (mul_pos ht0 (Real.sqrt_pos.mpr ht0)))]
  exact mul_le_mul hinv hb (abs_nonneg _)
    (inv_nonneg.mpr (mul_nonneg hℓ0.le (Real.sqrt_nonneg _)))


/-- Periodic cancellation on a truncated shell window retains its actual length. -/
theorem abs_periodic_shellPartnerKernel_sum_le
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    {q : ℕ} (hq : 1 ≤ q) (ψ : ℕ → ℝ) {U : ℝ}
    (hper : ∀ n, ψ (n + q) = ψ n) (hmean : ∑ r ∈ range q, ψ r = 0)
    (hU : ∀ n, |ψ n| ≤ U) {w A₁ : ℝ} (hw : 0 < w)
    (hA₁ : ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁)
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (A L : ℕ)
    (hleft : (ℓ : ℝ) / 2 ≤ A) (hright : (A : ℝ) + L ≤ 2 * ℓ) :
    |∑ i ∈ range L, shellPartnerKernel (atomDilate φ w) ℓ ((A : ℝ) + i) * ψ (A + i)| ≤
      (2 * q * U) * ((∫ u, atomDilate φ w u ^ 2) / Real.sqrt ((ℓ : ℝ) / 2) +
        L * (((ℓ : ℝ) / 2 * Real.sqrt ((ℓ : ℝ) / 2))⁻¹ *
          ((∫ u, atomDilate φ w u ^ 2) + A₁))) := by
  have hℓR : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓ0 : (0 : ℝ) < ℓ / 2 := by linarith only [hℓR]
  have hsub : Set.Icc (A : ℝ) (A + L) ⊆ Set.Icc ((ℓ : ℝ) / 2) (2 * ℓ) :=
    fun _ ht => ⟨hleft.trans ht.1, ht.2.trans hright⟩
  apply abs_periodic_lattice_sum_le_of_deriv hq ψ hper hmean hU A L
  · intro t ht
    have ht0 : 0 < t := hℓ0.trans_le (hsub ht).1
    have hβ : |bumpCorr (atomDilate φ w) (Real.log t - Real.log ℓ)| ≤
        ∫ u, atomDilate φ w u ^ 2 := by
      rw [bumpCorr_atomDilate_eq hw, abs_mul, abs_of_pos hw, integral_atomDilate_sq hw]
      exact mul_le_mul_of_nonneg_left
        (abs_bumpCorr_le hφ.continuous
          (HasCompactSupport.intro isCompact_Icc (fun u hu => hsupp u hu))
          ((Real.log t - Real.log ℓ) / w)) hw.le
    rw [shellPartnerKernel, abs_mul, abs_inv, abs_of_nonneg (Real.sqrt_nonneg t)]
    have hden : (Real.sqrt t)⁻¹ ≤ (Real.sqrt ((ℓ : ℝ) / 2))⁻¹ :=
      inv_anti₀ (Real.sqrt_pos.mpr hℓ0) (Real.sqrt_le_sqrt (hsub ht).1)
    simpa only [div_eq_mul_inv, mul_comm] using
      mul_le_mul hden hβ (abs_nonneg _)
        (inv_nonneg.mpr (Real.sqrt_nonneg _))
  · intro t ht
    exact hasDerivAt_shellPartnerKernel hφ hsupp hw ℓ (hℓ0.trans_le (hsub ht).1)
  · intro t ht
    exact abs_deriv_shellPartnerKernel_le hφ hsupp hw hA₁ hℓ (hsub ht)


/-- The shell width absorbs the lattice endpoint cost on visible products. -/
theorem abs_weighted_periodic_shellPartnerKernel_sum_le
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2)
    {q : ℕ} (hq : 1 ≤ q) (ψ : ℕ → ℝ) {U : ℝ}
    (hper : ∀ n, ψ (n + q) = ψ n) (hmean : ∑ r ∈ range q, ψ r = 0)
    (hU : ∀ n, |ψ n| ≤ U) {w A₁ : ℝ} (hw : 0 < w) (hw4 : w ≤ 1 / 4)
    (hA₁0 : 0 ≤ A₁) (hA₁ : ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁)
    {ℓ : ℕ} (hℓ : 2 ≤ ℓ) (hwℓ : 1 / 2 ≤ w * ℓ) (A L : ℕ)
    (hleft : (ℓ : ℝ) / 2 ≤ A) (hright : (A : ℝ) + L ≤ 2 * ℓ)
    (hlen : (L : ℝ) ≤ 3 * w * ℓ + 2) :
    |poleVector ℓ * ∑ i ∈ range L,
        shellPartnerKernel (atomDilate φ w) ℓ ((A : ℝ) + i) * ψ (A + i)| ≤
      (4 + 56 * ((1 / 4 : ℝ) + A₁ / (∫ u, φ u ^ 2))) * q * U *
        (∫ u, atomDilate φ w u ^ 2) / ℓ := by
  set G := ∫ u, atomDilate φ w u ^ 2
  set M := ∫ u, φ u ^ 2
  set r := (1 / 4 : ℝ) + A₁ / M
  have hG : G = w * M := integral_atomDilate_sq hw
  have hG0 : 0 ≤ G := integral_nonneg fun u => sq_nonneg _
  have hr0 : 0 ≤ r := add_nonneg (by norm_num) (div_nonneg hA₁0 hM.le)
  have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU 0)
  have hℓR : (2 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓ0 : (0 : ℝ) < ℓ := by linarith only [hℓR]
  have hs : 0 < Real.sqrt ((ℓ : ℝ) / 2) := Real.sqrt_pos.mpr (by positivity)
  have hL : (L : ℝ) ≤ 7 * w * ℓ := by linarith only [hlen, hwℓ]
  have hratio : w * (G + A₁) ≤ r * G := by
    have he : w * (G + A₁) = (w + A₁ / M) * G := by
      rw [hG]
      field_simp [hM.ne']
    rw [he]
    exact mul_le_mul_of_nonneg_right (show w + A₁ / M ≤ r by
      dsimp only [r]
      linarith only [hw4]) hG0
  have hbracket : G / Real.sqrt ((ℓ : ℝ) / 2) +
      L * (((ℓ : ℝ) / 2 * Real.sqrt ((ℓ : ℝ) / 2))⁻¹ * (G + A₁)) ≤
      (1 + 14 * r) * G / Real.sqrt ((ℓ : ℝ) / 2) := by
    have h1 := mul_le_mul_of_nonneg_right hL
      (show 0 ≤ ((ℓ : ℝ) / 2 * Real.sqrt ((ℓ : ℝ) / 2))⁻¹ * (G + A₁) by positivity)
    have he : (7 * w * ℓ) *
        (((ℓ : ℝ) / 2 * Real.sqrt ((ℓ : ℝ) / 2))⁻¹ * (G + A₁)) =
        14 * (w * (G + A₁)) / Real.sqrt ((ℓ : ℝ) / 2) := by
      field_simp [hℓ0.ne', hs.ne']
      ring
    rw [he] at h1
    have h2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 14)) hs.le
    calc
      _ ≤ G / Real.sqrt ((ℓ : ℝ) / 2) + 14 * (r * G) / Real.sqrt ((ℓ : ℝ) / 2) :=
        add_le_add le_rfl (h1.trans h2)
      _ = _ := by ring
  have hweight : poleVector ℓ / Real.sqrt ((ℓ : ℝ) / 2) ≤ 2 / ℓ := by
    have hden : (ℓ : ℝ) / 2 ≤ Real.sqrt ℓ * Real.sqrt ((ℓ : ℝ) / 2) := by
      calc
        (ℓ : ℝ) / 2 = Real.sqrt ((ℓ : ℝ) / 2) * Real.sqrt ((ℓ : ℝ) / 2) :=
          (Real.mul_self_sqrt (by positivity)).symm
        _ ≤ _ := mul_le_mul_of_nonneg_right
          (Real.sqrt_le_sqrt (by linarith only [hℓ0])) hs.le
    have hi := inv_anti₀ (show (0 : ℝ) < ℓ / 2 by positivity) hden
    simpa only [poleVector, one_div, div_eq_mul_inv, mul_inv_rev,
      inv_div, inv_inv, one_mul, mul_comm] using hi
  have hb := abs_periodic_shellPartnerKernel_sum_le hφ hsupp hq ψ hper hmean hU
    hw hA₁ hℓ A L hleft hright
  have hb' := hb.trans (mul_le_mul_of_nonneg_left hbracket (by positivity))
  rw [abs_mul, abs_of_nonneg (show 0 ≤ poleVector ℓ by unfold poleVector; positivity)]
  calc
    _ ≤ poleVector ℓ * ((2 * q * U) * ((1 + 14 * r) * G / Real.sqrt ((ℓ : ℝ) / 2))) :=
      mul_le_mul_of_nonneg_left hb' (by unfold poleVector; positivity)
    _ = (poleVector ℓ / Real.sqrt ((ℓ : ℝ) / 2)) * ((2 * q * U) * (1 + 14 * r) * G) := by ring
    _ ≤ (2 / ℓ) * ((2 * q * U) * (1 + 14 * r) * G) :=
      mul_le_mul_of_nonneg_right hweight (by positivity)
    _ = _ := by dsimp only [r, M, G]; ring


theorem topBand_eq_Icc (N : ℕ) (w : ℝ) :
    topBand N w = Icc (Nat.floor ((N : ℝ) * Real.exp w / 2) + 1) N := by
  ext n
  rw [mem_topBand, mem_Icc, mem_Icc]
  have hx0 : 0 ≤ (N : ℝ) * Real.exp w / 2 := by positivity
  have hlo := Nat.floor_le hx0
  have hhi := Nat.lt_floor_add_one ((N : ℝ) * Real.exp w / 2)
  constructor
  · rintro ⟨⟨_, hnN⟩, hn⟩
    refine ⟨?_, hnN⟩
    by_contra h
    have hn' : n ≤ Nat.floor ((N : ℝ) * Real.exp w / 2) := by omega
    have hnR : (n : ℝ) ≤ Nat.floor ((N : ℝ) * Real.exp w / 2) := by exact_mod_cast hn'
    linarith only [hnR, hlo, hn]
  · rintro ⟨hn, hnN⟩
    have hnR : (Nat.floor ((N : ℝ) * Real.exp w / 2) : ℝ) + 1 ≤ n := by exact_mod_cast hn
    exact ⟨⟨by omega, hnN⟩, by linarith only [hhi, hnR]⟩

/-- Periodic cancellation survives both the horizon cutoff and the shell cutoff. -/
theorem abs_topBand_shellPartnerKernel_sum_le
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hsupp : ∀ u, u ∉ Set.Icc (0 : ℝ) 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2)
    {q : ℕ} (hq : 1 ≤ q) (ψ : ℕ → ℝ) {U : ℝ}
    (hper : ∀ n, ψ (n + q) = ψ n) (hmean : ∑ r ∈ range q, ψ r = 0)
    (hU : ∀ n, |ψ n| ≤ U) {w A₁ : ℝ} (hw : 0 < w) (hw4 : w ≤ 1 / 4)
    (hA₁0 : 0 ≤ A₁) (hA₁ : ∀ x, |deriv (shellAutocorr φ) x| ≤ A₁)
    {ℓ : ℕ} (hℓ : 4 ≤ ℓ) (hwℓ : 1 / 2 ≤ w * ℓ) (N : ℕ) :
    |poleVector ℓ * ∑ n ∈ topBand N w, shellPartnerKernel (atomDilate φ w) ℓ n * ψ n| ≤
      (4 + 56 * ((1 / 4 : ℝ) + A₁ / (∫ u, φ u ^ 2))) * q * U *
        (∫ u, atomDilate φ w u ^ 2) / ℓ := by
  set A₀ := Nat.floor ((ℓ : ℝ) * Real.exp (-w))
  set B₀ := Nat.floor ((ℓ : ℝ) * Real.exp w)
  set C := Nat.floor ((N : ℝ) * Real.exp w / 2) + 1
  set A := max A₀ C
  set B := min B₀ N
  have hℓR : (4 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓ0 : (0 : ℝ) < ℓ := by linarith only [hℓR]
  have hem : 3 / 4 ≤ Real.exp (-w) := by
    have := Real.add_one_le_exp (-w)
    linarith only [this, hw4]
  have hep : Real.exp w ≤ 4 / 3 := by
    have h := Real.exp_add w (-w)
    rw [add_neg_cancel, Real.exp_zero] at h
    nlinarith only [h, hem, Real.exp_pos w]
  have hexp : Real.exp w - Real.exp (-w) ≤ 3 * w := by
    have h1 := Real.add_one_le_exp (-w)
    have h2 : Real.exp w * Real.exp (-w) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    nlinarith only [h1, h2, hw, hw4, Real.exp_pos w, Real.exp_pos (-w)]
  have hAlo : (A₀ : ℝ) ≤ ℓ * Real.exp (-w) := Nat.floor_le (by positivity)
  have hAhi : (ℓ : ℝ) * Real.exp (-w) < A₀ + 1 := Nat.lt_floor_add_one _
  have hBlo : (B₀ : ℝ) ≤ ℓ * Real.exp w := Nat.floor_le (by positivity)
  have hBhi : (ℓ : ℝ) * Real.exp w < B₀ + 1 := Nat.lt_floor_add_one _
  have hA₀A : A₀ ≤ A := le_max_left _ _
  have hCA : C ≤ A := le_max_right _ _
  have hBB₀ : B ≤ B₀ := min_le_left _ _
  have hBN : B ≤ N := min_le_right _ _
  have hsub : Icc A B ⊆ topBand N w := by
    rw [topBand_eq_Icc]
    exact fun n hn => mem_Icc.mpr ⟨hCA.trans (mem_Icc.mp hn).1, (mem_Icc.mp hn).2.trans hBN⟩
  have hsum : (∑ n ∈ topBand N w, shellPartnerKernel (atomDilate φ w) ℓ n * ψ n) =
      ∑ n ∈ Icc A B, shellPartnerKernel (atomDilate φ w) ℓ n * ψ n := by
    symm
    apply sum_subset hsub
    intro n hn hnAB
    have hn0 : (0 : ℝ) < n := by
      exact_mod_cast (mem_Icc.mp (mem_topBand.mp hn).1).1
    have hnCN : C ≤ n ∧ n ≤ N := by
      rw [topBand_eq_Icc] at hn
      exact mem_Icc.mp hn
    have hnside : n < A₀ ∨ B₀ < n := by
      simp only [mem_Icc] at hnAB
      dsimp only [A, B] at hnAB
      omega
    rw [shellPartnerKernel, bumpCorr_atomDilate_eq_zero_of_le hφ hsupp hw, mul_zero, zero_mul]
    rcases hnside with hn | hn
    · have hnR : (n : ℝ) < A₀ := by exact_mod_cast hn
      have h := Real.log_lt_log hn0 (hnR.trans_le hAlo)
      rw [Real.log_mul hℓ0.ne' (Real.exp_pos _).ne', Real.log_exp] at h
      have hneg : Real.log n - Real.log ℓ < 0 := by linarith only [h, hw]
      rw [abs_of_neg hneg]
      linarith only [h]
    · have hnR : (B₀ : ℝ) + 1 ≤ n := by exact_mod_cast hn
      have h := Real.log_lt_log (mul_pos hℓ0 (Real.exp_pos w)) (hBhi.trans_le hnR)
      rw [Real.log_mul hℓ0.ne' (Real.exp_pos _).ne', Real.log_exp] at h
      have hpos : 0 < Real.log n - Real.log ℓ := by linarith only [h, hw]
      rw [abs_of_pos hpos]
      linarith only [h]
  rw [hsum]
  by_cases hAB : A ≤ B + 1
  · set L := B + 1 - A
    have hL : (L : ℝ) = B + 1 - A := by
      change ((B + 1 - A : ℕ) : ℝ) = B + 1 - A
      rw [Nat.cast_sub hAB]
      push_cast
      rfl
    have hAL : (A : ℝ) + L = B + 1 := by rw [hL]; ring
    have hAR : (A₀ : ℝ) ≤ A := by exact_mod_cast hA₀A
    have hBR : (B : ℝ) ≤ B₀ := by exact_mod_cast hBB₀
    have hleft : (ℓ : ℝ) / 2 ≤ A := by
      nlinarith only [hAhi, hem, hℓR, hAR]
    have hright : (A : ℝ) + L ≤ 2 * ℓ := by
      rw [hAL]
      nlinarith only [hBR, hBlo, hep, hℓR]
    have hlen : (L : ℝ) ≤ 3 * w * ℓ + 2 := by
      rw [hL]
      nlinarith only [hAhi, hAR, hBR, hBlo, hexp, hℓ0]
    have h := abs_weighted_periodic_shellPartnerKernel_sum_le hφ hsupp hM hq ψ
      hper hmean hU hw hw4 hA₁0 hA₁ (by omega : 2 ≤ ℓ) hwℓ A L hleft hright hlen
    rw [← Finset.Ico_add_one_right_eq_Icc, sum_Ico_eq_sum_range]
    simpa only [L, Nat.cast_add] using h
  · have he : Icc A B = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro n hn
      have := mem_Icc.mp hn
      omega
    rw [he, sum_empty, mul_zero, abs_zero]
    have hU0 : 0 ≤ U := (abs_nonneg _).trans (hU 0)
    have hG0 : 0 ≤ ∫ u, atomDilate φ w u ^ 2 := integral_nonneg fun u => sq_nonneg _
    positivity

#print axioms abs_topBand_shellPartnerKernel_sum_le

end
end GaloisForLFunctions.SuccessorShellArithmetic
