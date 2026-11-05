import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.WhatTheFailureOfTheHodgeIndexMeasures
import GaloisForLFunctions.HeckeKreinToeplitz.BoundedIndexIsClosedUnderPointwiseLimits
import GaloisForLFunctions.RHTower.WeilPositivityTwistObstruction
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection

/-!
# Inward dilation preserves the window index

Every finite negative subspace of a tempered Weil form survives a sufficiently small
inward dilation. Fourier scaling gives uniform quadratic decay on the critical strip;
dominated convergence then preserves the negative eigenvalues of its finite Gram matrix.
Consequently the aperture index is the supremum of its values at strictly smaller apertures.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

open SquareRootThreshold HTGeometry

/-- Contraction factors increasing to one, bounded below by one half. -/
def indexInwardScale (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 2)

theorem indexInwardScale_bounds (n : ℕ) :
    1 / 2 ≤ indexInwardScale n ∧ indexInwardScale n < 1 := by
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 2) := by positivity
  have hle : (1 : ℝ) / ((n : ℝ) + 2) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by linarith [Nat.cast_nonneg (α := ℝ) n])
  constructor <;> dsimp [indexInwardScale] <;> linarith

theorem tendsto_indexInwardScale : Tendsto indexInwardScale atTop (𝓝 1) := by
  have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
  have hshift : Tendsto (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 2)) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two] using
      h.comp (tendsto_add_atTop_nat 1)
  change Tendsto (fun n : ℕ => 1 - 1 / ((n : ℝ) + 2)) atTop (𝓝 1)
  simpa only [sub_zero] using tendsto_const_nhds.sub hshift

/-- A support window contracts by the same factor as its test. -/
theorem tsupport_comp_div_subset {f : ℝ → ℂ} {a t : ℝ} (ht : 0 < t)
    (hf : tsupport f ⊆ Icc (-a) a) :
    tsupport (fun u => f (u / t)) ⊆ Icc (-(a * t)) (a * t) := by
  refine closure_minimal (fun u hu => ?_) isClosed_Icc
  have hm := hf (subset_tsupport f (Function.mem_support.mp hu))
  constructor
  · have := (le_div_iff₀ ht).mp hm.1
    linarith
  · exact (div_le_iff₀ ht).mp hm.2

/-- Uniform strip decay under contractions between one half and one. -/
private theorem exists_dilation_decay {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) {a : ℝ}
    (ha : 0 ≤ a) (hfs : tsupport f ⊆ Icc (-a) a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t : ℝ, 1 / 2 ≤ t → t ≤ 1 → ∀ z : ℂ,
      |z.im| ≤ 1 / 2 →
      ‖paperFT (fun u => f (u / t)) z‖ ≤ C / (1 + |z.re|) ^ 2 := by
  let B := Real.exp a * (4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖))
  have hI : 0 ≤ (∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖ :=
    add_nonneg (integral_nonneg fun _ => norm_nonneg _)
      (integral_nonneg fun _ => norm_nonneg _)
  have hB : 0 ≤ B := by
    dsimp [B]
    exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (by norm_num) hI)
  refine ⟨4 * B, by positivity, fun t ht ht1 z hz => ?_⟩
  have ht0 : 0 < t := by linarith
  have hdec := RHTower.norm_paperFT_le_decay hf
    (fun u hu => abs_le.mpr (hfs (subset_tsupport f hu))) ((t : ℂ) * z)
  simp only [Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, add_zero, abs_mul, abs_of_pos ht0] at hdec
  have him : t * |z.im| ≤ 1 :=
    ((mul_le_of_le_one_left (abs_nonneg z.im) ht1).trans hz).trans (by norm_num)
  have hexp : Real.exp (t * |z.im| * a) ≤ Real.exp a :=
    Real.exp_le_exp.mpr (mul_le_of_le_one_left ha him)
  have hdec' : ‖paperFT f ((t : ℂ) * z)‖ ≤ B / (1 + t * |z.re|) ^ 2 :=
    hdec.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hexp (mul_nonneg (by norm_num) hI)) (sq_nonneg _))
  have hden : (1 + |z.re|) ^ 2 ≤ 4 * (1 + t * |z.re|) ^ 2 := by
    have hlin : 1 + |z.re| ≤ 2 * (1 + t * |z.re|) := by
      nlinarith only [mul_le_mul_of_nonneg_right ht (abs_nonneg z.re)]
    have hs := pow_le_pow_left₀ (by positivity : 0 ≤ 1 + |z.re|) hlin 2
    nlinarith only [hs]
  rw [RHTower.paperFT_comp_div ht0, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ht0]
  calc t * ‖paperFT f ((t : ℂ) * z)‖ ≤ ‖paperFT f ((t : ℂ) * z)‖ :=
        mul_le_of_le_one_left (norm_nonneg _) ht1
    _ ≤ B / (1 + t * |z.re|) ^ 2 := hdec'
    _ ≤ 4 * B / (1 + |z.re|) ^ 2 := by
        rw [div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith only [mul_le_mul_of_nonneg_left hden hB]

/-- The full sesquilinear Weil pairing converges under inward dilation. -/
theorem tendsto_W_indexInwardScale {Z : ZeroConfig} (hZ : TemperedConfig Z)
    {a : ℝ} (ha : 0 ≤ a) {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hg : ContDiff ℝ 2 g) (hfs : tsupport f ⊆ Icc (-a) a)
    (hgs : tsupport g ⊆ Icc (-a) a) :
    Tendsto (fun n => Z.W (fun u => f (u / indexInwardScale n))
      (fun u => g (u / indexInwardScale n))) atTop (𝓝 (Z.W f g)) := by
  obtain ⟨C, hC, hCf⟩ := exists_dilation_decay hf ha hfs
  obtain ⟨D, hD, hDg⟩ := exists_dilation_decay hg ha hgs
  have ht0 : ∀ n, 0 < indexInwardScale n := fun n =>
    lt_of_lt_of_le (by norm_num) (indexInwardScale_bounds n).1
  have hconv : ∀ (k : ℝ → ℂ), Continuous k → tsupport k ⊆ Icc (-a) a →
      ∀ z : ℂ, Tendsto (fun n => paperFT (fun u => k (u / indexInwardScale n)) z)
        atTop (𝓝 (paperFT k z)) := by
    intro k hk hks z
    have hkc : HasCompactSupport k :=
      isCompact_Icc.of_isClosed_subset (isClosed_tsupport k) hks
    have ht : Tendsto (fun n => (indexInwardScale n : ℂ)) atTop (𝓝 (1 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.comp tendsto_indexInwardScale
    have harg : Tendsto (fun n => (indexInwardScale n : ℂ) * z) atTop (𝓝 z) := by
      simpa only [one_mul] using ht.mul_const z
    have hlim := ht.mul (((WeilEF.differentiable_paperFT hk hkc).continuous.tendsto z).comp harg)
    simp only [one_mul] at hlim
    exact hlim.congr fun n => (RHTower.paperFT_comp_div (ht0 n) z).symm
  let bound : Z.carrier → ℝ := fun τ =>
    (4 / 3 * C * D) * ((Z.mult τ : ℝ) / (1 + normSq (gammaOf τ)))
  have hsum : Summable bound := hZ.mul_left (4 / 3 * C * D)
  have hbound : ∀ n (τ : Z.carrier),
      ‖Z.Wsummand (fun u => f (u / indexInwardScale n))
        (fun u => g (u / indexInwardScale n)) τ‖ ≤ bound τ := by
    intro n τ
    have him := abs_im_gammaOf_le Z τ
    have himc : |(conj (gammaOf τ)).im| ≤ 1 / 2 := by
      simpa only [Complex.conj_im, abs_neg] using him
    have hfn := hCf _ (indexInwardScale_bounds n).1 (indexInwardScale_bounds n).2.le _ him
    have hgn := hDg _ (indexInwardScale_bounds n).1 (indexInwardScale_bounds n).2.le _ himc
    have hgn' : ‖paperFT (fun u => g (u / indexInwardScale n)) (conj (gammaOf τ))‖ ≤ D :=
      hgn.trans (div_le_self hD (one_le_pow₀ (by linarith [abs_nonneg (conj (gammaOf τ)).re])))
    have hden : 1 / (1 + |(gammaOf τ).re|) ^ 2 ≤ (4 / 3) / (1 + normSq (gammaOf τ)) := by
      rw [Complex.normSq_apply, div_le_div_iff₀ (by positivity)
        (by nlinarith [mul_self_nonneg (gammaOf τ).re, mul_self_nonneg (gammaOf τ).im])]
      have hi : (gammaOf τ).im * (gammaOf τ).im ≤ 1 / 4 := by nlinarith [abs_le.mp him]
      nlinarith [abs_nonneg (gammaOf τ).re, sq_abs (gammaOf τ).re]
    have hfn' : ‖paperFT (fun u => f (u / indexInwardScale n)) (gammaOf τ)‖ ≤
        C * ((4 / 3) / (1 + normSq (gammaOf τ))) := by
      refine hfn.trans ?_
      rw [div_eq_mul_one_div C]
      exact mul_le_mul_of_nonneg_left hden hC
    rw [ZeroConfig.Wsummand, norm_mul, norm_mul, Complex.norm_natCast, Complex.norm_conj]
    calc (Z.mult τ : ℝ) * _ * _ ≤
          (Z.mult τ : ℝ) * (C * ((4 / 3) / (1 + normSq (gammaOf τ)))) * D :=
          mul_le_mul (mul_le_mul_of_nonneg_left hfn' (Nat.cast_nonneg _)) hgn'
            (norm_nonneg _) (mul_nonneg (Nat.cast_nonneg _)
              (mul_nonneg hC (div_nonneg (by norm_num)
                (add_nonneg (by norm_num) (Complex.normSq_nonneg _)))))
      _ = bound τ := by dsimp [bound]; ring
  apply tendsto_tsum_of_dominated_convergence hsum _ (Eventually.of_forall hbound)
  intro τ
  exact ((hconv f hf.continuous hfs (gammaOf τ)).const_mul (Z.mult τ : ℂ)).mul
    (Complex.continuous_conj.continuousAt.tendsto.comp
      (hconv g hg.continuous hgs (conj (gammaOf τ))))

/-- A finite family retains all its negative squares in a strictly smaller window. -/
theorem exists_smaller_aperture_index_ge {Z : ZeroConfig} (hZ : TemperedConfig Z)
    {a : ℝ} (ha : 0 < a) {n : ℕ} (f : Fin n → ℝ → ℂ)
    (hf : ∀ i, ContDiff ℝ 2 (f i) ∧ tsupport (f i) ⊆ Icc (-a) a) :
    ∃ b : ℝ, 0 < b ∧ b < a ∧
      (hermNegIndex (zeroGram Z f) : ℕ∞) ≤ hodgeDefectAt Z b := by
  have hev := HeckeKreinToeplitz.eventually_le_hermNegIndex
    (zeroGram_isHermitian Z f) (fun i j =>
      tendsto_W_indexInwardScale hZ ha.le (hf i).1 (hf j).1 (hf i).2 (hf j).2)
  obtain ⟨k, hk⟩ := hev.exists
  have ht : 0 < indexInwardScale k := lt_of_lt_of_le (by norm_num) (indexInwardScale_bounds k).1
  refine ⟨a * indexInwardScale k, mul_pos ha ht,
    mul_lt_of_lt_one_right ha (indexInwardScale_bounds k).2, ?_⟩
  exact (ENat.coe_le_coe.mpr hk).trans (le_hodgeDefectAt Z
    (fun i u => f i (u / indexInwardScale k)) fun i =>
      ⟨(hf i).1.comp (contDiff_id.div_const _), tsupport_comp_div_subset ht (hf i).2⟩)

/-- No new negative square appears at a left endpoint of the aperture filtration. -/
theorem hodgeDefectAt_eq_iSup_lt {Z : ZeroConfig} (hZ : TemperedConfig Z)
    {a : ℝ} (ha : 0 < a) :
    hodgeDefectAt Z a = ⨆ (b : ℝ) (_ : 0 < b ∧ b < a), hodgeDefectAt Z b := by
  refine le_antisymm (iSup₂_le fun n f => iSup_le fun hf => ?_)
    (iSup_le fun b => iSup_le fun hb => hodgeDefectAt_mono Z hb.2.le)
  obtain ⟨b, hb0, hba, hb⟩ := exists_smaller_aperture_index_ge hZ ha f hf
  exact hb.trans (le_iSup₂_of_le b ⟨hb0, hba⟩ le_rfl)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
