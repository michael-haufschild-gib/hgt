import GaloisForLFunctions.RHTower.WeilFullConeHerglotzRightHalfPlane
import GaloisForLFunctions.RHTower.IsolatedDeepZeroWeilDetection
import GaloisForLFunctions.HTGeometry.BochnerPositiveDefiniteReal

/-!
# The Bochner measures of a full-cone Weil-positive system

Let `lam` be full-cone Weil-positive and let `f` be a `C²` compactly supported test.  The function

`F_f(y) = W_lam(τ_y(f ⋆ f̃))`,  `τ_y k(x) = k(x − y)`,

is continuous and positive definite (`positiveDefinite_spectralKernel`,
`continuous_spectralKernel`), so it is the characteristic function of a finite positive measure
`ν_f` (`exists_spectralMeasure`).  Formally `ν_f = |f̂|² μ_lam`, where `μ_lam` is the boundary
measure of the Herglotz function of `lam`.

The proof uses three properties of the Weil functional on the class of admissible tests
(continuous, compactly supported, with `paperFT k · γ` integrable):
* it is linear (`weilFullFunctional_sum`);
* it is Hermitian, `W(k̃) = conj W(k)` (`weilFullFunctional_tilde`), so its values on
  autocorrelations are real;
* the Gram matrix of translates of `f` is the autocorrelation of a combination of translates
  (`weilTest_sum_transl`).
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

noncomputable section

namespace RHTower.WeilSpectral

/-! ## Translations -/

/-- Translation `τ_y k(x) = k(x − y)`. -/
def transl (y : ℝ) (k : ℝ → ℂ) : ℝ → ℂ := fun x => k (x - y)

theorem paperFT_transl (y : ℝ) (k : ℝ → ℂ) (z : ℂ) :
    paperFT (transl y k) z = cexp (I * z * y) * paperFT k z := by
  unfold paperFT transl
  rw [← integral_const_mul,
    ← integral_add_right_eq_self (μ := volume) (fun x : ℝ => k (x - y) * cexp (I * z * x)) y]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [add_sub_cancel_right]
  rw [show ((x + y : ℝ) : ℂ) = (x : ℂ) + y by push_cast; ring, mul_add, Complex.exp_add]
  ring

/-! ## Admissible tests -/

/-- Tests on which the Weil functional is a well-behaved linear functional. -/
structure Admissible (k : ℝ → ℂ) : Prop where
  cont : Continuous k
  supp : HasCompactSupport k
  arch : Integrable fun r : ℝ => paperFT k r * (EF.gammaBracket r : ℂ)

theorem Admissible.integrable {k : ℝ → ℂ} (hk : Admissible k) : Integrable k :=
  hk.cont.integrable_of_hasCompactSupport hk.supp

theorem norm_cexp_I_mul_ofReal (r y : ℝ) : ‖cexp (I * (r : ℂ) * y)‖ = 1 := by
  rw [show I * (r : ℂ) * (y : ℂ) = ((r * y : ℝ) : ℂ) * I by push_cast; ring,
    Complex.norm_exp_ofReal_mul_I]

theorem Admissible.transl {k : ℝ → ℂ} (hk : Admissible k) (y : ℝ) : Admissible (transl y k) where
  cont := hk.cont.comp (continuous_id.sub continuous_const)
  supp := hk.supp.comp_homeomorph (Homeomorph.subRight y)
  arch := by
    have h : Integrable fun r : ℝ =>
        cexp (I * (r : ℂ) * y) * (paperFT k r * (EF.gammaBracket r : ℂ)) :=
      hk.arch.bdd_mul (c := 1) (by fun_prop)
        (Eventually.of_forall fun r => (norm_cexp_I_mul_ofReal r y).le)
    refine h.congr (Eventually.of_forall fun r => ?_)
    simp only
    rw [paperFT_transl]
    ring

theorem paperFT_add {k₁ k₂ : ℝ → ℂ} (h₁ : Admissible k₁) (h₂ : Admissible k₂) (z : ℂ) :
    paperFT (k₁ + k₂) z = paperFT k₁ z + paperFT k₂ z := by
  unfold paperFT
  rw [← integral_add (WeilHerglotz.integrable_mul_cexp h₁.integrable h₁.supp z)
    (WeilHerglotz.integrable_mul_cexp h₂.integrable h₂.supp z)]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Pi.add_apply]
  ring

theorem paperFT_smul (a : ℂ) (k : ℝ → ℂ) (z : ℂ) : paperFT (a • k) z = a * paperFT k z := by
  unfold paperFT
  rw [← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

theorem Admissible.add {k₁ k₂ : ℝ → ℂ} (h₁ : Admissible k₁) (h₂ : Admissible k₂) :
    Admissible (k₁ + k₂) where
  cont := h₁.cont.add h₂.cont
  supp := h₁.supp.add h₂.supp
  arch := (h₁.arch.add h₂.arch).congr (Eventually.of_forall fun r => by
    simp only [Pi.add_apply, paperFT_add h₁ h₂]
    ring)

theorem Admissible.smul {k : ℝ → ℂ} (h : Admissible k) (a : ℂ) : Admissible (a • k) where
  cont := continuous_const.smul h.cont
  supp := h.supp.smul_left
  arch := (h.arch.const_mul a).congr (Eventually.of_forall fun r => by
    simp only [paperFT_smul]
    ring)

theorem admissible_zero : Admissible (0 : ℝ → ℂ) where
  cont := continuous_const
  supp := HasCompactSupport.zero
  arch := by
    refine integrable_zero ℝ ℂ volume |>.congr (Eventually.of_forall fun r => ?_)
    simp [paperFT]

theorem Admissible.sum {ι : Type*} (s : Finset ι) {k : ι → ℝ → ℂ}
    (h : ∀ i ∈ s, Admissible (k i)) : Admissible (∑ i ∈ s, k i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using admissible_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/-! ## Linearity and Hermitian symmetry of the Weil functional -/

theorem weilFullFunctional_add (lam : ℕ → ℝ) {k₁ k₂ : ℝ → ℂ} (h₁ : Admissible k₁)
    (h₂ : Admissible k₂) :
    weilFullFunctional lam (k₁ + k₂) = weilFullFunctional lam k₁ + weilFullFunctional lam k₂ := by
  unfold weilFullFunctional
  rw [paperFT_add h₁ h₂, paperFT_add h₁ h₂]
  have hs₁ := summable_primeAtoms (fun n => if 2 ≤ n then lam n / Real.sqrt n else 0) h₁.supp
  have hs₂ := summable_primeAtoms (fun n => if 2 ≤ n then lam n / Real.sqrt n else 0) h₂.supp
  have htsum : (∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
      ((k₁ + k₂) (Real.log n) + (k₁ + k₂) (-Real.log n))) =
      (∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
        (k₁ (Real.log n) + k₁ (-Real.log n))) +
      ∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
        (k₂ (Real.log n) + k₂ (-Real.log n)) := by
    rw [← hs₁.tsum_add hs₂]
    refine tsum_congr fun n => ?_
    simp only [Pi.add_apply]
    ring
  have hint : (∫ r : ℝ, paperFT (k₁ + k₂) r * (EF.gammaBracket r : ℂ)) =
      (∫ r : ℝ, paperFT k₁ r * (EF.gammaBracket r : ℂ)) +
        ∫ r : ℝ, paperFT k₂ r * (EF.gammaBracket r : ℂ) := by
    rw [← integral_add h₁.arch h₂.arch]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [paperFT_add h₁ h₂]
    ring
  rw [htsum, hint]
  ring

theorem weilFullFunctional_smul (lam : ℕ → ℝ) (a : ℂ) (k : ℝ → ℂ) :
    weilFullFunctional lam (a • k) = a * weilFullFunctional lam k := by
  unfold weilFullFunctional
  rw [paperFT_smul, paperFT_smul]
  have htsum : (∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
      ((a • k) (Real.log n) + (a • k) (-Real.log n))) =
      a * ∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n)) := by
    rw [← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hint : (∫ r : ℝ, paperFT (a • k) r * (EF.gammaBracket r : ℂ)) =
      a * ∫ r : ℝ, paperFT k r * (EF.gammaBracket r : ℂ) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [paperFT_smul]
    ring
  rw [htsum, hint]
  ring

theorem weilFullFunctional_zero (lam : ℕ → ℝ) : weilFullFunctional lam 0 = 0 := by
  have := weilFullFunctional_smul lam 0 0
  simpa using this

theorem weilFullFunctional_sum (lam : ℕ → ℝ) {ι : Type*} (s : Finset ι) {k : ι → ℝ → ℂ}
    (h : ∀ i ∈ s, Admissible (k i)) :
    weilFullFunctional lam (∑ i ∈ s, k i) = ∑ i ∈ s, weilFullFunctional lam (k i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using weilFullFunctional_zero lam
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      weilFullFunctional_add lam (h a (Finset.mem_insert_self a s))
        (Admissible.sum s fun i hi => h i (Finset.mem_insert_of_mem hi)),
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)]

/-- **Hermitian symmetry.** `W(k̃) = conj W(k)`. -/
theorem weilFullFunctional_tilde (lam : ℕ → ℝ) (k : ℝ → ℂ) :
    weilFullFunctional lam (EF.tilde k) = conj (weilFullFunctional lam k) := by
  unfold weilFullFunctional
  have hc1 : conj (I / 2) = -I / 2 := by rw [map_div₀, Complex.conj_I, map_ofNat]
  have hc2 : conj (-I / 2) = I / 2 := by
    rw [map_div₀, map_neg, Complex.conj_I, neg_neg, map_ofNat]
  rw [EF.paperFT_tilde, EF.paperFT_tilde, hc1, hc2]
  have htsum : (∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
      (EF.tilde k (Real.log n) + EF.tilde k (-Real.log n))) =
      conj (∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
        (k (Real.log n) + k (-Real.log n))) := by
    rw [Complex.conj_tsum]
    refine tsum_congr fun n => ?_
    simp only [EF.tilde, neg_neg, map_mul, map_add, Complex.conj_ofReal]
    ring
  have hint : (∫ r : ℝ, paperFT (EF.tilde k) r * (EF.gammaBracket r : ℂ)) =
      conj (∫ r : ℝ, paperFT k r * (EF.gammaBracket r : ℂ)) := by
    rw [← integral_conj]
    refine integral_congr_ae (Eventually.of_forall fun r => ?_)
    simp only [EF.paperFT_tilde, Complex.conj_ofReal, map_mul]
  rw [htsum, hint]
  simp only [map_add, map_sub, map_mul, map_div₀, map_one, map_ofNat, Complex.conj_ofReal]
  ring

/-! ## Autocorrelations -/

theorem weilTest_apply (f g : ℝ → ℂ) (x : ℝ) :
    EF.weilTest f g x = ∫ u, f u * conj (g (u - x)) := by
  rw [EF.weilTest, convolution_def]
  simp only [ContinuousLinearMap.mul_apply', EF.tilde, neg_sub]

theorem tilde_weilTest_self (g : ℝ → ℂ) : EF.tilde (EF.weilTest g g) = EF.weilTest g g := by
  funext x
  rw [EF.tilde, weilTest_apply, weilTest_apply, ← integral_conj,
    ← integral_sub_right_eq_self (μ := volume) (fun u => conj (g u * conj (g (u - -x)))) x]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [map_mul, Complex.conj_conj, sub_neg_eq_add, sub_add_cancel]
  ring

theorem im_weilFullFunctional_weilTest_self (lam : ℕ → ℝ) (g : ℝ → ℂ) :
    (weilFullFunctional lam (EF.weilTest g g)).im = 0 := by
  have h := weilFullFunctional_tilde lam (EF.weilTest g g)
  rw [tilde_weilTest_self] at h
  have := congrArg Complex.im h
  rw [Complex.conj_im] at this
  linarith

/-- The Gram matrix of translates of `f` is the autocorrelation of a combination of translates. -/
theorem weilTest_sum_transl {f : ℝ → ℂ} (hf : Continuous f) (hfc : HasCompactSupport f) {N : ℕ}
    (t : Fin N → ℝ) (c : Fin N → ℂ) :
    EF.weilTest (∑ j, c j • transl (t j) f) (∑ j, c j • transl (t j) f)
      = ∑ i, ∑ j, (star (c i) * c j) • transl (t j - t i) (EF.weilTest f f) := by
  funext x
  rw [weilTest_apply]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, transl]
  have hint : ∀ i j : Fin N, Integrable fun u : ℝ =>
      c j * f (u - t j) * (star (c i) * conj (f (u - x - t i))) := by
    intro i j
    have hc : Continuous fun u : ℝ => c j * f (u - t j) * (star (c i) * conj (f (u - x - t i))) := by
      fun_prop
    refine hc.integrable_of_hasCompactSupport ?_
    have hs : HasCompactSupport fun u : ℝ => f (u - t j) :=
      hfc.comp_homeomorph (Homeomorph.subRight (t j))
    exact (hs.mul_left (f := fun _ => c j)).mul_right
  have hprod : ∀ u : ℝ, (∑ j, c j * f (u - t j)) * conj (∑ i, c i * f (u - x - t i)) =
      ∑ i, ∑ j, c j * f (u - t j) * (star (c i) * conj (f (u - x - t i))) := by
    intro u
    rw [map_sum, Finset.sum_mul, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    rfl
  rw [integral_congr_ae (Eventually.of_forall hprod),
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hint i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [weilTest_apply,
    ← integral_add_right_eq_self (μ := volume)
      (fun u => c j * f (u - t j) * (star (c i) * conj (f (u - x - t i)))) (t j),
    ← integral_const_mul]
  refine integral_congr_ae (Eventually.of_forall fun u => ?_)
  simp only [add_sub_cancel_right]
  rw [show u + t j - x - t i = u - (x - (t j - t i)) by ring]
  ring

/-! ## The spectral kernel -/

/-- The spectral kernel `F_f(y) = W_lam(τ_y(f ⋆ f̃))`. -/
def spectralKernel (lam : ℕ → ℝ) (f : ℝ → ℂ) (y : ℝ) : ℂ :=
  weilFullFunctional lam (transl y (EF.weilTest f f))

theorem exists_abs_bound_of_hasCompactSupport {f : ℝ → ℂ} (hfc : HasCompactSupport f) :
    ∃ a : ℝ, ∀ u, f u ≠ 0 → |u| ≤ a := by
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  refine ⟨R, fun u hu => ?_⟩
  have := hR (subset_tsupport f hu)
  rwa [Metric.mem_closedBall, dist_zero_right, Real.norm_eq_abs] at this

theorem abs_gammaBracket_le (r : ℝ) :
    |EF.gammaBracket r| ≤ digammaVerticalGrowthConst (1 / 4) + Real.log Real.pi + 1 + |r| := by
  rw [WeilHerglotz.gammaBracket_eq]
  have h1 := abs_re_digamma_vertical_le (c := 1 / 4) (by norm_num) (r / 2)
  have hlog : Real.log (2 + |r / 2|) ≤ 1 + |r| := by
    have hpos : 0 < 2 + |r / 2| := by positivity
    have := Real.log_le_sub_one_of_pos hpos
    have hh : |r / 2| ≤ |r| := by
      rw [abs_div, show |(2 : ℝ)| = 2 by norm_num]
      linarith [abs_nonneg r]
    linarith
  have hpi : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
  calc |(Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * I)).re - Real.log Real.pi|
      ≤ |(Complex.digamma (((1 / 4 : ℝ) : ℂ) + ((r / 2 : ℝ) : ℂ) * I)).re| + Real.log Real.pi := by
        refine (abs_sub _ _).trans ?_
        rw [abs_of_nonneg hpi]
    _ ≤ _ := by linarith

/-- Autocorrelations of `C²` compactly supported tests are admissible. -/
theorem admissible_weilTest {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    Admissible (EF.weilTest f f) where
  cont := (EF.weilTest_contDiff hf hf.continuous hfc).continuous
  supp := EF.weilTest_hasCompactSupport hfc hfc
  arch := by
    obtain ⟨a, ha⟩ := exists_abs_bound_of_hasCompactSupport hfc
    set D := 4 * ((∫ u, ‖f u‖) + ∫ u, ‖deriv (deriv f) u‖) with hD
    set K := digammaVerticalGrowthConst (1 / 4) + Real.log Real.pi + 1 with hK
    have hK0 : 0 ≤ K := by
      have := digammaVerticalGrowthConst_nonneg (c := 1 / 4) (by norm_num)
      have : 0 ≤ Real.log Real.pi := Real.log_nonneg (by linarith [Real.pi_gt_three])
      linarith
    have hD0 : 0 ≤ D := by
      have h1 : 0 ≤ ∫ u, ‖f u‖ := integral_nonneg fun _ => norm_nonneg _
      have h2 : 0 ≤ ∫ u, ‖deriv (deriv f) u‖ := integral_nonneg fun _ => norm_nonneg _
      rw [hD]
      positivity
    have hdecay : ∀ r : ℝ, ‖paperFT f r‖ ≤ D / (1 + |r|) ^ 2 := by
      intro r
      have := norm_paperFT_le_decay hf ha (r : ℂ)
      simpa [hD] using this
    have hmaj : Integrable fun r : ℝ => D ^ 2 * (K + 1) * (1 + ‖r‖) ^ (-(3 : ℝ)) :=
      (integrable_one_add_norm (μ := volume) (E := ℝ) (r := 3) (by norm_num)).const_mul _
    refine hmaj.mono' ?_ (Eventually.of_forall fun r => ?_)
    · have hc := WeilHerglotz.continuous_paperFT_real
        ((EF.weilTest_contDiff hf hf.continuous hfc).continuous.integrable_of_hasCompactSupport
          (EF.weilTest_hasCompactSupport hfc hfc))
      exact (hc.mul (Complex.continuous_ofReal.comp
        WeilHerglotz.continuous_gammaBracket)).aestronglyMeasurable
    · rw [EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc, Complex.conj_ofReal, norm_mul,
        norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
      have h1 := hdecay r
      have hγ := abs_gammaBracket_le r
      rw [← hK] at hγ
      have hr0 : 0 ≤ |r| := abs_nonneg r
      have hpos : 0 < 1 + |r| := by linarith
      have hrpow : (1 + |r|) ^ (-(3 : ℝ)) = 1 / (1 + |r|) ^ 3 := by
        rw [Real.rpow_neg hpos.le, one_div]
        norm_cast
      rw [hrpow]
      have hsq : ‖paperFT f r‖ * ‖paperFT f r‖ ≤ D ^ 2 / (1 + |r|) ^ 4 := by
        calc ‖paperFT f r‖ * ‖paperFT f r‖ ≤ (D / (1 + |r|) ^ 2) * (D / (1 + |r|) ^ 2) :=
              mul_le_mul h1 h1 (norm_nonneg _) (by positivity)
          _ = D ^ 2 / (1 + |r|) ^ 4 := by field_simp
      have hγ' : |EF.gammaBracket r| ≤ (K + 1) * (1 + |r|) := by nlinarith
      calc ‖paperFT f r‖ * ‖paperFT f r‖ * |EF.gammaBracket r|
          ≤ D ^ 2 / (1 + |r|) ^ 4 * ((K + 1) * (1 + |r|)) :=
            mul_le_mul hsq hγ' (abs_nonneg _) (by positivity)
        _ = D ^ 2 * (K + 1) * (1 / (1 + |r|) ^ 3) := by field_simp

/-! ## Positive definiteness and continuity -/

theorem positiveDefinite_spectralKernel {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    GaloisForLFunctions.HTGeometry.PositiveDefiniteOnReal (spectralKernel lam f) := by
  intro N t c
  set g : ℝ → ℂ := ∑ j, c j • transl (t j) f with hg
  have hgc : ContDiff ℝ 2 g := by
    have : g = fun x => ∑ j, c j * f (x - t j) := by
      funext x
      simp [hg, Finset.sum_apply, transl]
    rw [this]
    exact ContDiff.sum fun j _ => contDiff_const.mul (hf.comp (contDiff_id.sub contDiff_const))
  have hgs : HasCompactSupport g :=
    HasCompactSupport.finset_sum fun j _ =>
      (hfc.comp_homeomorph (Homeomorph.subRight (t j))).smul_left
  have hadm := admissible_weilTest hf hfc
  have hkey : ∑ i, ∑ j, star (c i) * spectralKernel lam f (t j - t i) * c j =
      weilFullFunctional lam (EF.weilTest g g) := by
    rw [hg, weilTest_sum_transl hf.continuous hfc,
      weilFullFunctional_sum lam _ fun i _ => Admissible.sum _ fun j _ => (hadm.transl _).smul _]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [weilFullFunctional_sum lam _ fun j _ => (hadm.transl _).smul _]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [weilFullFunctional_smul, spectralKernel]
    ring
  refine ⟨(weilFullFunctional lam (EF.weilTest g g)).re, hW g hgc hgs, ?_⟩
  rw [hkey]
  exact Complex.ext rfl (by simpa using im_weilFullFunctional_weilTest_self lam g)

theorem continuous_primeSum_transl (lam : ℕ → ℝ) {k : ℝ → ℂ} (hk : Continuous k)
    (hkc : HasCompactSupport k) :
    Continuous fun y : ℝ => ∑' n : ℕ, ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
      (transl y k (Real.log n) + transl y k (-Real.log n)) := by
  obtain ⟨a, ha⟩ := exists_abs_bound_of_hasCompactSupport hkc
  rw [continuous_iff_continuousAt]
  intro y₀
  obtain ⟨N, hN⟩ := exists_nat_gt (Real.exp (|a| + |y₀| + 1))
  have hfin : Continuous fun y : ℝ => ∑ n ∈ Finset.range N,
      ((if 2 ≤ n then lam n / Real.sqrt n else 0 : ℝ) : ℂ) *
        (transl y k (Real.log n) + transl y k (-Real.log n)) := by
    unfold transl
    fun_prop
  refine hfin.continuousAt.congr_of_eventuallyEq ?_
  have hball : ∀ᶠ y in 𝓝 y₀, |y - y₀| < 1 := by
    have := Metric.ball_mem_nhds y₀ (one_pos : (0 : ℝ) < 1)
    filter_upwards [this] with y hy
    rwa [Metric.mem_ball, Real.dist_eq] at hy
  filter_upwards [hball] with y hy
  refine tsum_eq_sum fun n hn => ?_
  rw [Finset.mem_range, not_lt] at hn
  have hnpos : (0 : ℝ) < n := by
    have : Real.exp (|a| + |y₀| + 1) < n :=
      lt_of_lt_of_le hN (by exact_mod_cast hn)
    exact lt_trans (Real.exp_pos _) this
  have hlog : |a| + |y₀| + 1 < Real.log n := by
    rw [Real.lt_log_iff_exp_lt hnpos]
    exact lt_of_lt_of_le hN (by exact_mod_cast hn)
  have hy' : |y| ≤ |y₀| + 1 := by
    have := abs_sub_abs_le_abs_sub y y₀
    linarith
  have hzero : ∀ x : ℝ, |a| < |x| → k x = 0 := by
    intro x hx
    by_contra hne
    have := ha x hne
    linarith [le_abs_self a]
  have h1 : transl y k (Real.log n) = 0 := by
    refine hzero _ ?_
    have : |Real.log n| - |y| ≤ |Real.log n - y| := abs_sub_abs_le_abs_sub _ _
    rw [abs_of_pos (by linarith [abs_nonneg a, abs_nonneg y₀])] at this
    linarith
  have h2 : transl y k (-Real.log n) = 0 := by
    refine hzero _ ?_
    have : |-Real.log n| - |y| ≤ |-Real.log n - y| := abs_sub_abs_le_abs_sub _ _
    rw [abs_neg, abs_of_pos (by linarith [abs_nonneg a, abs_nonneg y₀])] at this
    linarith
  rw [h1, h2, add_zero, mul_zero]

theorem continuous_spectralKernel (lam : ℕ → ℝ) {k : ℝ → ℂ} (hk : Admissible k) :
    Continuous fun y => weilFullFunctional lam (transl y k) := by
  have hpole : Continuous fun y : ℝ =>
      paperFT (transl y k) (I / 2) + paperFT (transl y k) (-I / 2) := by
    simp_rw [paperFT_transl]
    fun_prop
  have harch : Continuous fun y : ℝ =>
      ∫ r : ℝ, paperFT (transl y k) r * (EF.gammaBracket r : ℂ) := by
    simp_rw [paperFT_transl]
    refine continuous_of_dominated (bound := fun r => ‖paperFT k r * (EF.gammaBracket r : ℂ)‖)
      (fun y => ?_) (fun y => Eventually.of_forall fun r => ?_) hk.arch.norm
      (Eventually.of_forall fun r => by fun_prop)
    · have hc := WeilHerglotz.continuous_paperFT_real hk.integrable
      have hcont : Continuous fun r : ℝ =>
          cexp (I * (r : ℂ) * y) * paperFT k r * (EF.gammaBracket r : ℂ) :=
        ((by fun_prop : Continuous fun r : ℝ => cexp (I * (r : ℂ) * y)).mul hc).mul
          (Complex.continuous_ofReal.comp WeilHerglotz.continuous_gammaBracket)
      exact hcont.aestronglyMeasurable
    · rw [mul_assoc, norm_mul, norm_cexp_I_mul_ofReal, one_mul]
  have hprime := continuous_primeSum_transl lam hk.cont hk.supp
  unfold weilFullFunctional
  exact ((hpole.sub hprime).add (continuous_const.mul harch))

/-- **Bochner measures.** For a full-cone Weil-positive `lam` and a `C²` compactly supported `f`,
`y ↦ W_lam(τ_y(f ⋆ f̃))` is the characteristic function of a finite positive measure. -/
theorem exists_spectralMeasure {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ∃ ν : Measure ℝ, IsFiniteMeasure ν ∧ ∀ y, charFun ν y = spectralKernel lam f y :=
  GaloisForLFunctions.HTGeometry.exists_charFun_eq_of_positiveDefinite
    (positiveDefinite_spectralKernel hW hf hfc)
    (continuous_spectralKernel lam (admissible_weilTest hf hfc))

end RHTower.WeilSpectral

end
