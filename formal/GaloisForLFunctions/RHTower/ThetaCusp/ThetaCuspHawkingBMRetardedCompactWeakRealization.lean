import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMCompleteOriginalWeakSource
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMOriginalSpacetimeRegularity

/-! # Compact weak realization of the literal retarded field

In event coordinates `(t, x)` the literal retarded potential is
`U(t, x, X, k) = originalPotential q br a (t + x) (t - x) X k`.  On the physical wedge
`W = {0 < t + x, x < 0}` it is smooth and solves the original forced wave equation pointwise.
Transposing the wave operator and the hyperbolic angular operator onto a smooth test supported
compactly in `W` gives the weak identity `∫ U · weakWaveTest F = ∫ e^{-k} · forcing · F`.  The
corrected future field satisfies the same identity, so their difference is weakly homogeneous on
`W`.

The proof multiplies `U` by a smooth cutoff equal to one near the support of the test, which
makes the field globally smooth, and then integrates by parts along every coordinate direction
of the target `(ℝ × ℝ) × ℂ`. -/

open MeasureTheory Set Filter Topology
open scoped ContDiff

namespace RHTower.D4BMRetardedCompactWeakRealization
open D4BMFullSourceWeakWave D4BMGeneralTemporalTransposition D4BMAdvancedKernelTransposition
open D4BMCompleteOriginalWeakSource D4BMOriginalCausalPotential D4BMOriginalSpacetimeRegularity
open D4BMJointSource D4BMModularCore

set_option autoImplicit false

/-! ### Smooth cutoffs -/

/-- A compact subset of an open set in a finite-dimensional space has a smooth compactly
supported cutoff, supported in the open set and equal to one on a neighbourhood of the compact
set. -/
theorem exists_contDiff_cutoff {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {K W : Set E} (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W) :
    ∃ χ : E → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ W ∧
      ∃ V, IsOpen V ∧ K ⊆ V ∧ ∀ x ∈ V, χ x = 1 := by
  obtain ⟨V₁, hV₁, hKV₁, hcl₁, hc₁⟩ := exists_open_between_and_isCompact_closure hK hW hKW
  obtain ⟨V₂, hV₂, hKV₂, hcl₂, -⟩ := exists_open_between_and_isCompact_closure hK hV₁ hKV₁
  obtain ⟨f, hfs, hf, hfr⟩ := hV₁.exists_contDiff_support_eq (n := ⊤)
  obtain ⟨g, hgs, hg, hgr⟩ := (isClosed_closure (s := V₂)).isOpen_compl.exists_contDiff_support_eq
    (n := ⊤)
  have hf0 : ∀ x, 0 ≤ f x := fun x => (hfr (mem_range_self x)).1
  have hg0 : ∀ x, 0 ≤ g x := fun x => (hgr (mem_range_self x)).1
  have hfpos : ∀ x ∈ V₁, 0 < f x := fun x hx =>
    lt_of_le_of_ne (hf0 x) (Ne.symm (show f x ≠ 0 by rw [← Function.mem_support, hfs]; exact hx))
  have hpos : ∀ x, 0 < f x + g x := by
    intro x
    by_cases hx : x ∈ V₁
    · linarith [hfpos x hx, hg0 x]
    · have hx' : x ∈ (closure V₂)ᶜ := fun h => hx (hcl₂ h)
      have hgx : 0 < g x := lt_of_le_of_ne (hg0 x)
        (Ne.symm (show g x ≠ 0 by rw [← Function.mem_support, hgs]; exact hx'))
      linarith [hf0 x]
  have hsupp : Function.support (fun x => f x / (f x + g x)) = V₁ := by
    ext x
    simp only [Function.mem_support, ne_eq, div_eq_zero_iff, not_or]
    rw [← hfs]
    exact ⟨fun h => h.1, fun h => ⟨h, (hpos x).ne'⟩⟩
  have htsupp : tsupport (fun x => f x / (f x + g x)) = closure V₁ := by
    rw [tsupport, hsupp]
  refine ⟨fun x => f x / (f x + g x), hf.div (hf.add hg) (fun x => (hpos x).ne'), ?_, ?_,
    V₂, hV₂, hKV₂, fun x hx => ?_⟩
  · rw [HasCompactSupport, htsupp]
    exact hc₁
  · rw [htsupp]
    exact hcl₁
  · have hgx : g x = 0 := by
      by_contra h
      have : x ∈ (closure V₂)ᶜ := by rw [← hgs]; exact h
      exact this (subset_closure hx)
    have hfx := hfpos x (hcl₂ (subset_closure hx))
    simp only [hgx, add_zero]
    exact div_self hfx.ne'

/-! ### Integration by parts against a compact test -/

section IntegrationByParts

private theorem dir_smooth {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {f : E → ℂ}
    (hf : ContDiff ℝ ∞ f) (v : E) : ContDiff ℝ ∞ (fun x => fderiv ℝ f x v) :=
  (hf.fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure]

/-- One directional derivative moves onto a compact test with a minus sign. -/
theorem integral_mul_dir {f g : E → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (v : E) :
    (∫ x, f x * fderiv ℝ g x v ∂μ) = -∫ x, fderiv ℝ f x v * g x ∂μ :=
  integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (((dir_smooth hf v).continuous.mul hg.continuous).integrable_of_hasCompactSupport
      (hc.fderiv_apply ℝ v).mul_right)
    ((hf.continuous.mul (dir_smooth hg v).continuous).integrable_of_hasCompactSupport hc.mul_right)
    ((hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport hc.mul_right)
    (fun x _ => hf.differentiable (by simp) x) (fun x _ => hg.differentiable (by simp) x)

/-- Two equal directional derivatives are self-transpose against a compact test. -/
theorem integral_mul_dir_dir {f g : E → ℂ} (hf : ContDiff ℝ ∞ f) (hc : HasCompactSupport f)
    (hg : ContDiff ℝ ∞ g) (v : E) :
    (∫ x, f x * fderiv ℝ (fun y => fderiv ℝ g y v) x v ∂μ) =
      ∫ x, fderiv ℝ (fun y => fderiv ℝ f y v) x v * g x ∂μ := by
  rw [integral_mul_dir hf hc (dir_smooth hg v) v,
    integral_mul_dir (dir_smooth hf v) (hc.fderiv_apply ℝ v) hg v, neg_neg]

end IntegrationByParts

/-! ### The operator dual to `weakWaveTest` -/

/-- The angular operator `e^{2k} ∂_X² + ∂_k² - ∂_k` in the chart `z = X + i k`. -/
noncomputable def angularOperator (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  (Real.exp z.im : ℂ) ^ 2 * fderiv ℝ (fun w => fderiv ℝ g w 1) z 1 +
    fderiv ℝ (fun w => fderiv ℝ g w Complex.I) z Complex.I - fderiv ℝ g z Complex.I

private theorem exp_im_smooth : ContDiff ℝ ∞ (fun w : ℂ => (Real.exp w.im : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp Complex.imCLM.contDiff)

private theorem exp_neg_im_smooth : ContDiff ℝ ∞ (fun w : ℂ => (Real.exp (-w.im) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp (Real.contDiff_exp.comp Complex.imCLM.contDiff.neg)

/-- **Angular transposition**: against a compact test the hyperbolic test operator is dual to
`e^{-k} ·` the angular operator, for every smooth field. -/
theorem integral_angularTestAction_mul {φ g : ℂ → ℂ} (hφ : ContDiff ℝ ∞ φ)
    (hc : HasCompactSupport φ) (hg : ContDiff ℝ ∞ g) :
    (∫ z, angularTestAction φ z * g z) =
      ∫ z, (Real.exp (-z.im) : ℂ) * φ z * angularOperator g z := by
  set A : ℂ → ℂ := fun w => (Real.exp w.im : ℂ) * φ w with hAdef
  set B : ℂ → ℂ := fun w => (Real.exp (-w.im) : ℂ) * φ w with hBdef
  have hA : ContDiff ℝ ∞ A := exp_im_smooth.mul hφ
  have hB : ContDiff ℝ ∞ B := exp_neg_im_smooth.mul hφ
  have cA : HasCompactSupport A := hc.mul_left
  have cB : HasCompactSupport B := hc.mul_left
  have hD {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (v : ℂ) : ContDiff ℝ ∞ (fun w => fderiv ℝ f w v) :=
    dir_smooth hf v
  have hDD {f : ℂ → ℂ} (hf : ContDiff ℝ ∞ f) (v : ℂ) :
      ContDiff ℝ ∞ (fun w => fderiv ℝ (fun y => fderiv ℝ f y v) w v) := dir_smooth (hD hf v) v
  have iAA : Integrable (fun z => fderiv ℝ (fun y => fderiv ℝ A y 1) z 1 * g z) :=
    ((hDD hA 1).continuous.mul hg.continuous).integrable_of_hasCompactSupport
      ((cA.fderiv_apply ℝ 1).fderiv_apply ℝ 1).mul_right
  have iBB : Integrable (fun z => fderiv ℝ (fun y => fderiv ℝ B y Complex.I) z Complex.I * g z) :=
    ((hDD hB Complex.I).continuous.mul hg.continuous).integrable_of_hasCompactSupport
      ((cB.fderiv_apply ℝ Complex.I).fderiv_apply ℝ Complex.I).mul_right
  have iB : Integrable (fun z => fderiv ℝ B z Complex.I * g z) :=
    ((hD hB Complex.I).continuous.mul hg.continuous).integrable_of_hasCompactSupport
      (cB.fderiv_apply ℝ Complex.I).mul_right
  have jAA : Integrable (fun z => A z * fderiv ℝ (fun y => fderiv ℝ g y 1) z 1) :=
    (hA.continuous.mul (hDD hg 1).continuous).integrable_of_hasCompactSupport cA.mul_right
  have jBB : Integrable (fun z => B z * fderiv ℝ (fun y => fderiv ℝ g y Complex.I) z Complex.I) :=
    (hB.continuous.mul (hDD hg Complex.I).continuous).integrable_of_hasCompactSupport cB.mul_right
  have jB : Integrable (fun z => B z * fderiv ℝ g z Complex.I) :=
    (hB.continuous.mul (hD hg Complex.I).continuous).integrable_of_hasCompactSupport cB.mul_right
  have hsplit : (fun z => angularTestAction φ z * g z) = fun z =>
      fderiv ℝ (fun y => fderiv ℝ A y 1) z 1 * g z +
        fderiv ℝ (fun y => fderiv ℝ B y Complex.I) z Complex.I * g z +
        fderiv ℝ B z Complex.I * g z := by
    funext z
    change (fderiv ℝ (fun y => fderiv ℝ A y 1) z 1 +
      fderiv ℝ (fun y => fderiv ℝ B y Complex.I) z Complex.I + fderiv ℝ B z Complex.I) * g z = _
    ring
  have hIAA := integral_mul_dir_dir (μ := volume) hA cA hg 1
  have hIBB := integral_mul_dir_dir (μ := volume) hB cB hg Complex.I
  have hIB := integral_mul_dir (μ := volume) hB cB hg Complex.I
  have iAB : Integrable (fun z => fderiv ℝ (fun y => fderiv ℝ A y 1) z 1 * g z +
      fderiv ℝ (fun y => fderiv ℝ B y Complex.I) z Complex.I * g z) := iAA.add iBB
  have jAB : Integrable (fun z => A z * fderiv ℝ (fun y => fderiv ℝ g y 1) z 1 +
      B z * fderiv ℝ (fun y => fderiv ℝ g y Complex.I) z Complex.I) := jAA.add jBB
  rw [hsplit, integral_add iAB iB, integral_add iAA iBB, ← hIAA, ← hIBB]
  have hIB' : (∫ z, fderiv ℝ B z Complex.I * g z) = -∫ z, B z * fderiv ℝ g z Complex.I := by
    rw [hIB, neg_neg]
  rw [hIB', ← integral_add jAA jBB, ← sub_eq_add_neg, ← integral_sub jAB jB]
  congr 1
  funext z
  have he : (Real.exp z.im : ℂ) = (Real.exp (-z.im) : ℂ) * (Real.exp z.im : ℂ) ^ 2 := by
    rw [Real.exp_neg, Complex.ofReal_inv]
    have hne : (Real.exp z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
    field_simp
  simp only [hAdef, hBdef, angularOperator]
  linear_combination (φ z * fderiv ℝ (fun y => fderiv ℝ g y 1) z 1) * he

/-- Directional derivative on the target `(ℝ × ℝ) × ℂ`. -/
noncomputable def targetDir (v : Target) (G : Target → ℂ) (r : Target) : ℂ := fderiv ℝ G r v

/-- The event wave operator `∂_t² - ∂_x²` on the target. -/
noncomputable def targetEventWave (G : Target → ℂ) (r : Target) : ℂ :=
  targetDir ((1, 0), 0) (targetDir ((1, 0), 0) G) r -
    targetDir ((0, 1), 0) (targetDir ((0, 1), 0) G) r

/-- The angular operator `e^{2k} ∂_X² + ∂_k² - ∂_k` on the target. -/
noncomputable def targetAngular (G : Target → ℂ) (r : Target) : ℂ :=
  (Real.exp r.2.im : ℂ) ^ 2 * targetDir (0, 1) (targetDir (0, 1) G) r +
    targetDir (0, Complex.I) (targetDir (0, Complex.I) G) r - targetDir (0, Complex.I) G r

/-- The field operator dual to `weakWaveTest`: `∂_t² - ∂_x² - (e^{2k}∂_X² + ∂_k² - ∂_k)/cosh² x`. -/
noncomputable def weakFieldOperator (G : Target → ℂ) (r : Target) : ℂ :=
  targetEventWave G r - targetAngular G r / (Real.cosh r.1.2 : ℂ) ^ 2

private theorem targetDir_smooth {G : Target → ℂ} (hG : ContDiff ℝ ∞ G) (v : Target) :
    ContDiff ℝ ∞ (targetDir v G) := dir_smooth hG v

private theorem event_slice {G : Target → ℂ} {e : ℝ × ℝ} {z : ℂ}
    (hG : DifferentiableAt ℝ G (e, z)) (v : ℝ × ℝ) :
    fderiv ℝ (fun e' => G (e', z)) e v = targetDir (v, 0) G (e, z) := by
  have he : HasFDerivAt (fun e' : ℝ × ℝ => (e', z))
      ((ContinuousLinearMap.id ℝ (ℝ × ℝ)).prod (0 : (ℝ × ℝ) →L[ℝ] ℂ)) e :=
    (hasFDerivAt_id e).prodMk (hasFDerivAt_const z e)
  have h := (hG.hasFDerivAt.comp e he).fderiv
  dsimp only [Function.comp_def] at h
  rw [targetDir, h]
  rfl

private theorem angular_slice {G : Target → ℂ} {e : ℝ × ℝ} {z : ℂ}
    (hG : DifferentiableAt ℝ G (e, z)) (v : ℂ) :
    fderiv ℝ (fun w => G (e, w)) z v = targetDir (0, v) G (e, z) := by
  have he : HasFDerivAt (fun w : ℂ => (e, w))
      ((0 : ℂ →L[ℝ] (ℝ × ℝ)).prod (ContinuousLinearMap.id ℝ ℂ)) z :=
    (hasFDerivAt_const e z).prodMk (hasFDerivAt_id z)
  have h := (hG.hasFDerivAt.comp z he).fderiv
  dsimp only [Function.comp_def] at h
  rw [targetDir, h]
  rfl

private theorem eventWave_slice {G : Target → ℂ} (hG : ContDiff ℝ ∞ G) (e : ℝ × ℝ) (z : ℂ) :
    eventWave (fun e' => G (e', z)) e = targetEventWave G (e, z) := by
  have h1 (v : ℝ × ℝ) : (fun e' => fderiv ℝ (fun e'' => G (e'', z)) e' v) =
      fun e' => targetDir (v, 0) G (e', z) :=
    funext fun e' => event_slice (hG.differentiable (by simp) _) v
  have h2 (v : ℝ × ℝ) := event_slice (G := targetDir (v, 0) G) (e := e) (z := z)
    ((targetDir_smooth hG (v, 0)).differentiable (by simp) _) v
  change fderiv ℝ (fun e' => fderiv ℝ (fun e'' => G (e'', z)) e' (1, 0)) e (1, 0) -
    fderiv ℝ (fun e' => fderiv ℝ (fun e'' => G (e'', z)) e' (0, 1)) e (0, 1) = _
  rw [h1, h1, h2, h2]
  rfl

private theorem angularOperator_slice {G : Target → ℂ} (hG : ContDiff ℝ ∞ G) (e : ℝ × ℝ)
    (z : ℂ) : angularOperator (fun w => G (e, w)) z = targetAngular G (e, z) := by
  have h1 (v : ℂ) : (fun w => fderiv ℝ (fun w' => G (e, w')) w v) =
      fun w => targetDir (0, v) G (e, w) :=
    funext fun w => angular_slice (hG.differentiable (by simp) _) v
  have h2 (v : ℂ) := angular_slice (G := targetDir (0, v) G) (e := e) (z := z)
    ((targetDir_smooth hG (0, v)).differentiable (by simp) _) v
  rw [angularOperator, h1, h1, h2, h2, angular_slice (hG.differentiable (by simp) _)]
  rfl

private theorem targetEventWave_smooth {G : Target → ℂ} (hG : ContDiff ℝ ∞ G) :
    ContDiff ℝ ∞ (targetEventWave G) :=
  (targetDir_smooth (targetDir_smooth hG _) _).sub (targetDir_smooth (targetDir_smooth hG _) _)

private theorem targetAngular_continuous {G : Target → ℂ} (hG : ContDiff ℝ ∞ G) :
    Continuous (targetAngular G) := by
  have hw : Continuous (fun r : Target => (Real.exp r.2.im : ℂ) ^ 2) := by fun_prop
  exact ((hw.mul (targetDir_smooth (targetDir_smooth hG _) _).continuous).add
    (targetDir_smooth (targetDir_smooth hG _) _).continuous).sub (targetDir_smooth hG _).continuous

private theorem target_fubini (F : Target → ℂ) (hi : Integrable F) :
    (∫ r : Target, F r) = ∫ e : ℝ × ℝ, ∫ z : ℂ, F (e, z) := by
  rw [Measure.volume_eq_prod] at hi ⊢
  exact integral_prod F hi

private theorem target_fubini_swap (F : Target → ℂ) (hi : Integrable F) :
    (∫ r : Target, F r) = ∫ z : ℂ, ∫ e : ℝ × ℝ, F (e, z) := by
  rw [Measure.volume_eq_prod] at hi ⊢
  exact integral_prod_symm F hi

private theorem slice_event_compact {F : Target → ℂ} (hc : HasCompactSupport F) (z : ℂ) :
    HasCompactSupport (fun e : ℝ × ℝ => F (e, z)) := by
  apply hc.comp_isClosedEmbedding
  refine ⟨isEmbedding_prodMkLeft z, ?_⟩
  have he : Set.range (fun e : ℝ × ℝ => (e, z)) = Set.univ ×ˢ ({z} : Set ℂ) := by
    ext ⟨e, w⟩
    simp [eq_comm]
  rw [he]
  exact isClosed_univ.prod isClosed_singleton

private theorem slice_angular_compact {F : Target → ℂ} (hc : HasCompactSupport F) (e : ℝ × ℝ) :
    HasCompactSupport (fun z : ℂ => F (e, z)) := by
  apply hc.comp_isClosedEmbedding
  refine ⟨isEmbedding_prodMkRight e, ?_⟩
  have he : Set.range (fun z : ℂ => (e, z)) = ({e} : Set (ℝ × ℝ)) ×ˢ Set.univ := by
    ext ⟨r, z⟩
    simp [eq_comm]
  rw [he]
  exact isClosed_singleton.prod isClosed_univ

/-- The event wave operator is self-transpose against a compact test. -/
private theorem integral_mul_eventWave {g φ : ℝ × ℝ → ℂ} (hg : ContDiff ℝ ∞ g)
    (hφ : ContDiff ℝ ∞ φ) (hc : HasCompactSupport φ) :
    (∫ e, g e * eventWave φ e) = ∫ e, eventWave g e * φ e := by
  have hD (v : ℝ × ℝ) {f : ℝ × ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
      ContDiff ℝ ∞ (fun y => fderiv ℝ (fun y' => fderiv ℝ f y' v) y v) :=
    dir_smooth (dir_smooth hf v) v
  have iφ (v : ℝ × ℝ) : Integrable (fun e => g e *
      fderiv ℝ (fun y => fderiv ℝ φ y v) e v) :=
    (hg.continuous.mul (hD v hφ).continuous).integrable_of_hasCompactSupport
      ((hc.fderiv_apply ℝ v).fderiv_apply ℝ v).mul_left
  have ig (v : ℝ × ℝ) : Integrable (fun e => fderiv ℝ (fun y => fderiv ℝ g y v) e v * φ e) :=
    ((hD v hg).continuous.mul hφ.continuous).integrable_of_hasCompactSupport hc.mul_left
  have hpair (v : ℝ × ℝ) : (∫ e, g e * fderiv ℝ (fun y => fderiv ℝ φ y v) e v) =
      ∫ e, fderiv ℝ (fun y => fderiv ℝ g y v) e v * φ e := by
    have h := integral_mul_dir_dir (μ := volume) hφ hc hg v
    simp only [mul_comm (φ _)] at h
    rw [h]
    congr 1
    funext e
    ring
  change (∫ e, g e * (fderiv ℝ (fun y => fderiv ℝ φ y (1, 0)) e (1, 0) -
      fderiv ℝ (fun y => fderiv ℝ φ y (0, 1)) e (0, 1))) =
    ∫ e, (fderiv ℝ (fun y => fderiv ℝ g y (1, 0)) e (1, 0) -
      fderiv ℝ (fun y => fderiv ℝ g y (0, 1)) e (0, 1)) * φ e
  simp only [mul_sub, sub_mul]
  rw [integral_sub (iφ _) (iφ _), integral_sub (ig _) (ig _), hpair, hpair]

/-- **Compact weak transposition.**  For every smooth field `G` and smooth compact test `F`,
`∫ G · weakWaveTest F = ∫ e^{-k} · weakFieldOperator G · F`. -/
theorem integral_mul_weakWaveTest {G F : Target → ℂ} (hG : ContDiff ℝ ∞ G)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    (∫ r, G r * weakWaveTest F r) =
      ∫ r, (Real.exp (-r.2.im) : ℂ) * weakFieldOperator G r * F r := by
  set Wt : Target → ℂ := fun r =>
    (Real.exp (-r.2.im) : ℂ) * eventWave (fun e => F (e, r.2)) r.1 with hWtdef
  set At : Target → ℂ := fun r =>
    angularTestAction (fun w => F (r.1, w)) r.2 / (Real.cosh r.1.2 : ℂ) ^ 2 with hAtdef
  have hweight : Continuous (fun r : Target => (Real.exp (-r.2.im) : ℂ)) := by fun_prop
  have hWt : Wt = fun r => (Real.exp (-r.2.im) : ℂ) * targetEventWave F r := by
    funext r
    simp only [hWtdef, eventWave_slice hF]
  have hWc : Continuous Wt := hWt ▸ hweight.mul (targetEventWave_smooth hF).continuous
  have hWcs : HasCompactSupport Wt := by
    rw [hWt]
    exact (((hc.fderiv_apply ℝ _).fderiv_apply ℝ _).sub
      ((hc.fderiv_apply ℝ _).fderiv_apply ℝ _)).mul_left
  obtain ⟨hTc, hTcs⟩ := weakWaveTest_regular F hF hc
  have hsplit : ∀ r, weakWaveTest F r = Wt r - At r := fun r => rfl
  have hAt : At = fun r => Wt r - weakWaveTest F r := by
    funext r
    rw [hsplit]
    ring
  have hAc : Continuous At := hAt ▸ hWc.sub hTc
  have hAcs : HasCompactSupport At := hAt ▸ hWcs.sub hTcs
  have iGW : Integrable (fun r => G r * Wt r) :=
    (hG.continuous.mul hWc).integrable_of_hasCompactSupport hWcs.mul_left
  have iGA : Integrable (fun r => G r * At r) :=
    (hG.continuous.mul hAc).integrable_of_hasCompactSupport hAcs.mul_left
  have hcosh : Continuous (fun r : Target => ((Real.cosh r.1.2 : ℂ) ^ 2)⁻¹) :=
    (by fun_prop : Continuous (fun r : Target => (Real.cosh r.1.2 : ℂ) ^ 2)).inv₀
      fun r => pow_ne_zero _ (Complex.ofReal_ne_zero.mpr (Real.cosh_pos _).ne')
  have iTW : Integrable (fun r : Target =>
      (Real.exp (-r.2.im) : ℂ) * targetEventWave G r * F r) :=
    ((hweight.mul (targetEventWave_smooth hG).continuous).mul hF.continuous
      ).integrable_of_hasCompactSupport hc.mul_left
  have iTA : Integrable (fun r : Target =>
      (Real.exp (-r.2.im) : ℂ) * (targetAngular G r / (Real.cosh r.1.2 : ℂ) ^ 2) * F r) := by
    simp only [div_eq_mul_inv]
    exact ((hweight.mul ((targetAngular_continuous hG).mul hcosh)).mul hF.continuous
      ).integrable_of_hasCompactSupport hc.mul_left
  have htemp : (∫ r, G r * Wt r) =
      ∫ r, (Real.exp (-r.2.im) : ℂ) * targetEventWave G r * F r := by
    rw [target_fubini_swap _ iGW, target_fubini_swap _ iTW]
    congr 1
    funext z
    have hφ : ContDiff ℝ ∞ (fun e : ℝ × ℝ => F (e, z)) :=
      hF.comp (contDiff_id.prodMk contDiff_const)
    have hg : ContDiff ℝ ∞ (fun e : ℝ × ℝ => G (e, z)) :=
      hG.comp (contDiff_id.prodMk contDiff_const)
    have h1 : (fun e : ℝ × ℝ => G (e, z) * Wt (e, z)) = fun e =>
        (Real.exp (-z.im) : ℂ) * (G (e, z) * eventWave (fun e' => F (e', z)) e) := by
      funext e
      simp only [hWtdef]
      ring
    have h2 : (fun e : ℝ × ℝ => (Real.exp (-(e, z).2.im) : ℂ) * targetEventWave G (e, z) *
        F (e, z)) = fun e => (Real.exp (-z.im) : ℂ) *
          (eventWave (fun e' => G (e', z)) e * F (e, z)) := by
      funext e
      rw [eventWave_slice hG]
      ring
    rw [h1, h2, integral_const_mul, integral_const_mul,
      integral_mul_eventWave hg hφ (slice_event_compact hc z)]
  have hang : (∫ r, G r * At r) =
      ∫ r, (Real.exp (-r.2.im) : ℂ) * (targetAngular G r / (Real.cosh r.1.2 : ℂ) ^ 2) * F r := by
    rw [target_fubini _ iGA, target_fubini _ iTA]
    congr 1
    funext e
    have hφ : ContDiff ℝ ∞ (fun z : ℂ => F (e, z)) := hF.comp (contDiff_const.prodMk contDiff_id)
    have hg : ContDiff ℝ ∞ (fun z : ℂ => G (e, z)) := hG.comp (contDiff_const.prodMk contDiff_id)
    have h1 : (fun z : ℂ => G (e, z) * At (e, z)) = fun z =>
        ((Real.cosh e.2 : ℂ) ^ 2)⁻¹ *
          (angularTestAction (fun w => F (e, w)) z * G (e, z)) := by
      funext z
      simp only [hAtdef, div_eq_mul_inv]
      ring
    have h2 : (fun z : ℂ => (Real.exp (-(e, z).2.im) : ℂ) *
        (targetAngular G (e, z) / (Real.cosh (e, z).1.2 : ℂ) ^ 2) * F (e, z)) = fun z =>
          ((Real.cosh e.2 : ℂ) ^ 2)⁻¹ * ((Real.exp (-z.im) : ℂ) * F (e, z) *
            angularOperator (fun w => G (e, w)) z) := by
      funext z
      rw [angularOperator_slice hG]
      simp only [div_eq_mul_inv]
      ring
    rw [h1, h2, integral_const_mul, integral_const_mul,
      integral_angularTestAction_mul hφ (slice_angular_compact hc e) hg]
  have hL : (fun r => G r * weakWaveTest F r) = fun r => G r * Wt r - G r * At r := by
    funext r
    rw [hsplit]
    ring
  rw [hL, integral_sub iGW iGA, htemp, hang, ← integral_sub iTW iTA]
  congr 1
  funext r
  simp only [weakFieldOperator]
  ring

/-! ### Germ locality -/

private theorem dir_eventually_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℂ} {x : E} (h : φ =ᶠ[𝓝 x] 0) (v : E) : (fun y => fderiv ℝ φ y v) =ᶠ[𝓝 x] 0 := by
  filter_upwards [h.eventually_nhds] with y hy
  have hy' : φ =ᶠ[𝓝 y] 0 := hy
  rw [hy'.fderiv_eq]
  simp

private theorem dir_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {φ : E → ℂ} {x : E} (h : φ =ᶠ[𝓝 x] 0) (v : E) : fderiv ℝ φ x v = 0 :=
  (dir_eventually_zero h v).eq_of_nhds

/-- The weak test operator vanishes off the topological support of the test. -/
theorem weakWaveTest_eq_zero_of_notMem {F : Target → ℂ} {r : Target} (hr : r ∉ tsupport F) :
    weakWaveTest F r = 0 := by
  rw [notMem_tsupport_iff_eventuallyEq] at hr
  obtain ⟨e, z⟩ := r
  have he : (fun e' => F (e', z)) =ᶠ[𝓝 e] 0 :=
    ((continuous_id.prodMk continuous_const).tendsto e).eventually hr
  have hz : (fun w => F (e, w)) =ᶠ[𝓝 z] 0 :=
    ((continuous_const.prodMk continuous_id).tendsto z).eventually hr
  have hA : (fun w : ℂ => (Real.exp w.im : ℂ) * F (e, w)) =ᶠ[𝓝 z] 0 := by
    filter_upwards [hz] with w hw
    simp only [Pi.zero_apply] at hw ⊢
    rw [hw, mul_zero]
  have hB : (fun w : ℂ => (Real.exp (-w.im) : ℂ) * F (e, w)) =ᶠ[𝓝 z] 0 := by
    filter_upwards [hz] with w hw
    simp only [Pi.zero_apply] at hw ⊢
    rw [hw, mul_zero]
  have hwave : eventWave (fun e' => F (e', z)) e = 0 := by
    change fderiv ℝ (fun y => fderiv ℝ (fun e' => F (e', z)) y (1, 0)) e (1, 0) -
      fderiv ℝ (fun y => fderiv ℝ (fun e' => F (e', z)) y (0, 1)) e (0, 1) = 0
    rw [dir_zero (dir_eventually_zero he _), dir_zero (dir_eventually_zero he _), sub_zero]
  have hang : angularTestAction (fun w => F (e, w)) z = 0 := by
    change fderiv ℝ (fun y => fderiv ℝ (fun w : ℂ => (Real.exp w.im : ℂ) * F (e, w)) y 1) z 1 +
      fderiv ℝ (fun y => fderiv ℝ (fun w : ℂ => (Real.exp (-w.im) : ℂ) * F (e, w)) y Complex.I) z
        Complex.I + fderiv ℝ (fun w : ℂ => (Real.exp (-w.im) : ℂ) * F (e, w)) z Complex.I = 0
    rw [dir_zero (dir_eventually_zero hA _), dir_zero (dir_eventually_zero hB _), dir_zero hB,
      add_zero, add_zero]
  change (Real.exp (-z.im) : ℂ) * eventWave (fun e' => F (e', z)) e -
    angularTestAction (fun w => F (e, w)) z / (Real.cosh e.2 : ℂ) ^ 2 = 0
  rw [hwave, hang]
  simp

/-- The field operator depends only on the germ of the field. -/
theorem weakFieldOperator_congr {G U : Target → ℂ} {r : Target} (h : G =ᶠ[𝓝 r] U) :
    weakFieldOperator G r = weakFieldOperator U r := by
  have h1 (v : Target) : targetDir v G =ᶠ[𝓝 r] targetDir v U := by
    filter_upwards [h.fderiv (𝕜 := ℝ)] with y hy
    simp only [targetDir, hy]
  have h2 (u v : Target) : targetDir u (targetDir v G) r = targetDir u (targetDir v U) r := by
    change fderiv ℝ (targetDir v G) r u = fderiv ℝ (targetDir v U) r u
    rw [(h1 v).fderiv_eq]
  simp only [weakFieldOperator, targetEventWave, targetAngular, h2, (h1 (0, Complex.I)).eq_of_nhds]

/-! ### The literal retarded potential in event coordinates -/

/-- The literal retarded potential `U(t, x, X, k) = originalPotential (t + x) (t - x) X k`. -/
noncomputable def eventPotential (q : XiZeroCopy) (br : Bool) (a : ℂ) (r : Target) : ℂ :=
  originalPotential q br a (r.1.1 + r.1.2) (r.1.1 - r.1.2) r.2.re r.2.im

/-- The physical wedge `0 < t + x`, `x < 0`. -/
def physicalWedge : Set Target := {r | 0 < r.1.1 + r.1.2 ∧ r.1.2 < 0}

theorem isOpen_physicalWedge : IsOpen physicalWedge :=
  (isOpen_lt continuous_const (show Continuous (fun r : Target => r.1.1 + r.1.2) by fun_prop)).inter
    (isOpen_lt (show Continuous (fun r : Target => r.1.2) by fun_prop) continuous_const)

/-- The null chart `((t, x), X + i k) ↦ (t + x, t - x, X, k)`. -/
private noncomputable def nullChart : Target →L[ℝ] (Fin 4 → ℝ) :=
  ContinuousLinearMap.pi ![
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℂ) +
      (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℂ),
    (ContinuousLinearMap.fst ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℂ) -
      (ContinuousLinearMap.snd ℝ ℝ ℝ).comp (ContinuousLinearMap.fst ℝ (ℝ × ℝ) ℂ),
    Complex.reCLM.comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℂ),
    Complex.imCLM.comp (ContinuousLinearMap.snd ℝ (ℝ × ℝ) ℂ)]

private theorem nullChart_apply (r : Target) :
    nullChart r = ![r.1.1 + r.1.2, r.1.1 - r.1.2, r.2.re, r.2.im] := by
  funext i
  fin_cases i <;> rfl

/-- The retarded potential as a function of the four null coordinates. -/
private noncomputable def nullPotential (q : XiZeroCopy) (br : Bool) (a : ℂ)
    (w : Fin 4 → ℝ) : ℂ :=
  originalPotential q br a (w 0) (w 1) (w 2) (w 3)

private theorem eventPotential_eq (q : XiZeroCopy) (br : Bool) (a : ℂ) :
    eventPotential q br a = fun r => nullPotential q br a (nullChart r) := by
  funext r
  rw [nullChart_apply]
  rfl

private theorem nullPotential_smooth (q : XiZeroCopy) (br : Bool) (a : ℂ) {w : Fin 4 → ℝ}
    (hw : 0 < w 0 ∧ w 0 < w 1) : ContDiffAt ℝ 2 (nullPotential q br a) w :=
  (originalPotential_smooth q br a w hw.1 hw.2).of_le (WithTop.coe_le_coe.mpr le_top)

private theorem nullChart_mem {r : Target} (hr : r ∈ physicalWedge) :
    0 < nullChart r 0 ∧ nullChart r 0 < nullChart r 1 := by
  rw [nullChart_apply]
  exact ⟨hr.1, by simp; linarith [hr.2]⟩

private theorem second_dir {f : (Fin 4 → ℝ) → ℂ} {w : Fin 4 → ℝ} (hf : ContDiffAt ℝ 2 f w)
    (c d : Fin 4 → ℝ) : fderiv ℝ (fun y => fderiv ℝ f y c) w d = fderiv ℝ (fderiv ℝ f) w d c := by
  have hD : DifferentiableAt ℝ (fderiv ℝ f) w :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [(hD.hasFDerivAt.clm_apply (hasFDerivAt_const c w)).fderiv]
  simp

private theorem targetDir_eventPotential_first (q : XiZeroCopy) (br : Bool) (a : ℂ) {r : Target}
    (hr : r ∈ physicalWedge) (v : Target) :
    targetDir v (eventPotential q br a) r =
      fderiv ℝ (nullPotential q br a) (nullChart r) (nullChart v) := by
  have hd := ((nullPotential_smooth q br a (nullChart_mem hr)).differentiableAt
    (by norm_num)).hasFDerivAt.comp r nullChart.hasFDerivAt
  rw [targetDir, eventPotential_eq, show (fun r => nullPotential q br a (nullChart r)) =
    nullPotential q br a ∘ nullChart from rfl, hd.fderiv]
  rfl

private theorem targetDir_eventPotential_second (q : XiZeroCopy) (br : Bool) (a : ℂ)
    {r : Target} (hr : r ∈ physicalWedge) (u v : Target) :
    targetDir u (targetDir v (eventPotential q br a)) r =
      fderiv ℝ (fderiv ℝ (nullPotential q br a)) (nullChart r) (nullChart u) (nullChart v) := by
  have he : targetDir v (eventPotential q br a) =ᶠ[𝓝 r]
      fun y => fderiv ℝ (nullPotential q br a) (nullChart y) (nullChart v) := by
    filter_upwards [isOpen_physicalWedge.mem_nhds hr] with y hy
    exact targetDir_eventPotential_first q br a hy v
  have hV := nullPotential_smooth q br a (nullChart_mem hr)
  have hD : DifferentiableAt ℝ (fun w => fderiv ℝ (nullPotential q br a) w (nullChart v))
      (nullChart r) :=
    ((hV.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const _)
  have hc := hD.hasFDerivAt.comp r nullChart.hasFDerivAt
  change fderiv ℝ (targetDir v (eventPotential q br a)) r u = _
  rw [he.fderiv_eq, show (fun y => fderiv ℝ (nullPotential q br a) (nullChart y) (nullChart v)) =
    (fun w => fderiv ℝ (nullPotential q br a) w (nullChart v)) ∘ nullChart from rfl, hc.fderiv]
  exact second_dir hV (nullChart v) (nullChart u)

/-! ### The pointwise field equation on the wedge -/

private theorem nullChart_t : nullChart ((1, 0), 0) = Pi.single 0 1 + Pi.single 1 1 := by
  rw [nullChart_apply]
  funext i
  fin_cases i <;> simp

private theorem nullChart_x : nullChart ((0, 1), 0) = Pi.single 0 1 - Pi.single 1 1 := by
  rw [nullChart_apply]
  funext i
  fin_cases i <;> simp

private theorem nullChart_X : nullChart (0, 1) = Pi.single 2 1 := by
  rw [nullChart_apply]
  funext i
  fin_cases i <;> simp

private theorem nullChart_k : nullChart (0, Complex.I) = Pi.single 3 1 := by
  rw [nullChart_apply]
  funext i
  fin_cases i <;> simp

private theorem curve_hasDerivAt (w : Fin 4 → ℝ) (i : Fin 4) (s : ℝ) :
    HasDerivAt (fun u => Function.update w i u) (Pi.single i 1) s :=
  hasDerivAt_update w i s

private theorem nullPotential_update_deriv (q : XiZeroCopy) (br : Bool) (a : ℂ)
    {w : Fin 4 → ℝ} (i : Fin 4) (hw : 0 < w 0 ∧ w 0 < w 1) :
    HasDerivAt (fun u => nullPotential q br a (Function.update w i u))
      (fderiv ℝ (nullPotential q br a) w (Pi.single i 1)) (w i) := by
  have hV := ((nullPotential_smooth q br a hw).differentiableAt (by norm_num)).hasFDerivAt
  have h := (show HasFDerivAt (nullPotential q br a) _ (Function.update w i (w i)) by
    rw [Function.update_eq_self]; exact hV).comp_hasDerivAt (w i) (curve_hasDerivAt w i (w i))
  exact h

private theorem dir_update_deriv (q : XiZeroCopy) (br : Bool) (a : ℂ)
    {w : Fin 4 → ℝ} (i j : Fin 4) (hw : 0 < w 0 ∧ w 0 < w 1) :
    HasDerivAt (fun u => fderiv ℝ (nullPotential q br a) (Function.update w i u) (Pi.single j 1))
      (fderiv ℝ (fderiv ℝ (nullPotential q br a)) w (Pi.single i 1) (Pi.single j 1)) (w i) := by
  have hV := nullPotential_smooth q br a hw
  have hD : DifferentiableAt ℝ (fun y => fderiv ℝ (nullPotential q br a) y (Pi.single j 1)) w :=
    ((hV.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const _)
  have h := (show HasFDerivAt (fun y => fderiv ℝ (nullPotential q br a) y (Pi.single j 1)) _
    (Function.update w i (w i)) by rw [Function.update_eq_self]; exact hD.hasFDerivAt
    ).comp_hasDerivAt (w i) (curve_hasDerivAt w i (w i))
  rw [second_dir hV] at h
  exact h

/-- The null mixed derivative `∂_r ∂_p V` is a second Fréchet derivative of the null potential. -/
private theorem null_mixed (q : XiZeroCopy) (br : Bool) (a : ℂ) {p ρ X k : ℝ} (hp : 0 < p)
    (hpρ : p < ρ) :
    deriv (fun b => deriv (fun u => originalPotential q br a u b X k) p) ρ =
      fderiv ℝ (fderiv ℝ (nullPotential q br a)) ![p, ρ, X, k] (Pi.single 1 1)
        (Pi.single 0 1) := by
  have hin : ∀ b, p < b → deriv (fun u => originalPotential q br a u b X k) p =
      fderiv ℝ (nullPotential q br a) ![p, b, X, k] (Pi.single 0 1) := by
    intro b hb
    have h := nullPotential_update_deriv q br a (w := ![p, b, X, k]) 0 ⟨hp, hb⟩
    have he : (fun u => nullPotential q br a (Function.update ![p, b, X, k] 0 u)) =
        fun u => originalPotential q br a u b X k := by
      funext u
      simp [nullPotential, Function.update]
    rw [he] at h
    exact h.deriv
  have hev : (fun b => deriv (fun u => originalPotential q br a u b X k) p) =ᶠ[𝓝 ρ]
      fun b => fderiv ℝ (nullPotential q br a) ![p, b, X, k] (Pi.single 0 1) := by
    filter_upwards [lt_mem_nhds hpρ] with b hb
    exact hin b hb
  rw [hev.deriv_eq]
  have h := dir_update_deriv q br a (w := ![p, ρ, X, k]) 1 0 ⟨hp, hpρ⟩
  have he : (fun u => fderiv ℝ (nullPotential q br a) (Function.update ![p, ρ, X, k] 1 u)
      (Pi.single 0 1)) =
      fun b => fderiv ℝ (nullPotential q br a) ![p, b, X, k] (Pi.single 0 1) := by
    funext u
    congr 2
    funext i
    fin_cases i <;> simp [Function.update]
  rw [he] at h
  exact h.deriv

/-- The angular Laplacian of the null potential in second Fréchet derivatives. -/
private theorem null_angular (q : XiZeroCopy) (br : Bool) (a : ℂ) {p ρ X k : ℝ} (hp : 0 < p)
    (hpρ : p < ρ) :
    angularLaplacian (originalPotential q br a p ρ) X k =
      (Real.exp k : ℂ) ^ 2 * fderiv ℝ (fderiv ℝ (nullPotential q br a)) ![p, ρ, X, k]
          (Pi.single 2 1) (Pi.single 2 1) +
        fderiv ℝ (fderiv ℝ (nullPotential q br a)) ![p, ρ, X, k] (Pi.single 3 1)
          (Pi.single 3 1) -
        fderiv ℝ (nullPotential q br a) ![p, ρ, X, k] (Pi.single 3 1) := by
  have hX : deriv (fun x => originalPotential q br a p ρ x k) =
      fun x => fderiv ℝ (nullPotential q br a) ![p, ρ, x, k] (Pi.single 2 1) := by
    funext x
    have h := nullPotential_update_deriv q br a (w := ![p, ρ, x, k]) 2 ⟨hp, hpρ⟩
    have he : (fun u => nullPotential q br a (Function.update ![p, ρ, x, k] 2 u)) =
        fun u => originalPotential q br a p ρ u k := by
      funext u
      simp [nullPotential, Function.update]
    rw [he] at h
    exact h.deriv
  have hK : deriv (fun y => originalPotential q br a p ρ X y) =
      fun y => fderiv ℝ (nullPotential q br a) ![p, ρ, X, y] (Pi.single 3 1) := by
    funext y
    have h := nullPotential_update_deriv q br a (w := ![p, ρ, X, y]) 3 ⟨hp, hpρ⟩
    have he : (fun u => nullPotential q br a (Function.update ![p, ρ, X, y] 3 u)) =
        fun u => originalPotential q br a p ρ X u := by
      funext u
      simp [nullPotential, Function.update]
    rw [he] at h
    exact h.deriv
  have hXX : deriv (fun x => fderiv ℝ (nullPotential q br a) ![p, ρ, x, k] (Pi.single 2 1)) X =
      fderiv ℝ (fderiv ℝ (nullPotential q br a)) ![p, ρ, X, k] (Pi.single 2 1)
        (Pi.single 2 1) := by
    have h := dir_update_deriv q br a (w := ![p, ρ, X, k]) 2 2 ⟨hp, hpρ⟩
    have he : (fun u => fderiv ℝ (nullPotential q br a) (Function.update ![p, ρ, X, k] 2 u)
        (Pi.single 2 1)) =
        fun x => fderiv ℝ (nullPotential q br a) ![p, ρ, x, k] (Pi.single 2 1) := by
      funext u
      congr 2
      funext i
      fin_cases i <;> simp [Function.update]
    rw [he] at h
    exact h.deriv
  have hKK : deriv (fun y => fderiv ℝ (nullPotential q br a) ![p, ρ, X, y] (Pi.single 3 1)) k =
      fderiv ℝ (fderiv ℝ (nullPotential q br a)) ![p, ρ, X, k] (Pi.single 3 1)
        (Pi.single 3 1) := by
    have h := dir_update_deriv q br a (w := ![p, ρ, X, k]) 3 3 ⟨hp, hpρ⟩
    have he : (fun u => fderiv ℝ (nullPotential q br a) (Function.update ![p, ρ, X, k] 3 u)
        (Pi.single 3 1)) =
        fun y => fderiv ℝ (nullPotential q br a) ![p, ρ, X, y] (Pi.single 3 1) := by
      funext u
      congr 2
      funext i
      fin_cases i <;> simp [Function.update]
    rw [he] at h
    exact h.deriv
  rw [angularLaplacian, hX, hK, hXX, hKK]

/-- **Pointwise field equation.**  On the physical wedge the literal retarded potential satisfies
`weakFieldOperator U = timeOriginalForcing`. -/
theorem weakFieldOperator_eventPotential (q : XiZeroCopy) (br : Bool) (a : ℂ) {r : Target}
    (hr : r ∈ physicalWedge) :
    weakFieldOperator (eventPotential q br a) r =
      timeOriginalForcing q br a r.1.1 r.1.2 ![r.2.re, Real.exp r.2.im] := by
  obtain ⟨⟨t, x⟩, z⟩ := r
  have hp : 0 < t + x := hr.1
  have hpρ : t + x < t - x := by linarith [hr.2]
  have hwave := originalPotential_wave q br a hp hpρ.le z.re z.im
  rw [null_mixed q br a hp hpρ, null_angular q br a hp hpρ,
    show (t + x + (t - x)) / 2 = t by ring, show (t + x - (t - x)) / 2 = x by ring] at hwave
  have hw₀ : nullChart ((t, x), z) = ![t + x, t - x, z.re, z.im] := nullChart_apply _
  have hsymm := (nullPotential_smooth q br a (w := ![t + x, t - x, z.re, z.im])
    ⟨hp, hpρ⟩).isSymmSndFDerivAt (by simp)
  simp only [weakFieldOperator, targetEventWave, targetAngular,
    targetDir_eventPotential_second q br a hr, targetDir_eventPotential_first q br a hr, hw₀,
    nullChart_t, nullChart_x, nullChart_X, nullChart_k, map_add, map_sub,
    add_apply, sub_apply]
  rw [← hwave, hsymm (Pi.single 0 1) (Pi.single 1 1)]
  ring

/-! ### The compact weak identity -/

private theorem eventPotential_contDiffAt (q : XiZeroCopy) (br : Bool) (a : ℂ) {r : Target}
    (hr : r ∈ physicalWedge) : ContDiffAt ℝ ∞ (eventPotential q br a) r := by
  rw [eventPotential_eq]
  have h := nullChart_mem hr
  exact (originalPotential_smooth q br a (nullChart r) h.1 h.2).comp r
    nullChart.contDiff.contDiffAt

/-- The retarded potential has an absolutely convergent pairing with every compact test
supported in the physical wedge. -/
theorem eventPotential_mul_weakWaveTest_integrable (q : XiZeroCopy) (br : Bool) (a : ℂ)
    {F : Target → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hW : tsupport F ⊆ physicalWedge) :
    Integrable (fun r => eventPotential q br a r * weakWaveTest F r) := by
  obtain ⟨hTc, hTcs⟩ := weakWaveTest_regular F hF hc
  have hcont : Continuous (fun r => eventPotential q br a r * weakWaveTest F r) := by
    rw [continuous_iff_continuousAt]
    intro r
    by_cases hr : r ∈ physicalWedge
    · exact (eventPotential_contDiffAt q br a hr).continuousAt.mul hTc.continuousAt
    · have hnot : r ∉ tsupport F := fun h => hr (hW h)
      have hev : (fun _ : Target => (0 : ℂ)) =ᶠ[𝓝 r]
          fun y => eventPotential q br a y * weakWaveTest F y := by
        filter_upwards [(isClosed_tsupport F).isOpen_compl.mem_nhds hnot] with y hy
        rw [weakWaveTest_eq_zero_of_notMem hy, mul_zero]
      exact continuousAt_const.congr hev
  exact hcont.integrable_of_hasCompactSupport hTcs.mul_left

/-- **Retarded compact weak realization.**  For every smooth test `F` with compact support in the
physical wedge `0 < t + x`, `x < 0`, the literal retarded potential satisfies
`∫ U · weakWaveTest F = ∫ e^{-k} · timeOriginalForcing(t, x, (X, e^k)) · F`. -/
theorem eventPotential_weak_wave (q : XiZeroCopy) (br : Bool) (a : ℂ) {F : Target → ℂ}
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) (hW : tsupport F ⊆ physicalWedge) :
    (∫ r, eventPotential q br a r * weakWaveTest F r) =
      ∫ r, (Real.exp (-r.2.im) : ℂ) *
        timeOriginalForcing q br a r.1.1 r.1.2 ![r.2.re, Real.exp r.2.im] * F r := by
  obtain ⟨χ, hχ, -, hχW, V, hV, hKV, hχ1⟩ := exists_contDiff_cutoff hc isOpen_physicalWedge hW
  set G : Target → ℂ := fun r => (χ r : ℂ) * eventPotential q br a r with hGdef
  have hG : ContDiff ℝ ∞ G := by
    rw [contDiff_iff_contDiffAt]
    intro r
    by_cases hr : r ∈ physicalWedge
    · exact (Complex.ofRealCLM.contDiff.comp hχ).contDiffAt.mul
        (eventPotential_contDiffAt q br a hr)
    · have hnot : r ∉ tsupport χ := fun h => hr (hχW h)
      rw [notMem_tsupport_iff_eventuallyEq] at hnot
      apply (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq
      filter_upwards [hnot] with y hy
      simp only [hGdef, hy, Pi.zero_apply, Complex.ofReal_zero, zero_mul]
  have h1 : (fun r => eventPotential q br a r * weakWaveTest F r) =
      fun r => G r * weakWaveTest F r := by
    funext r
    by_cases hr : r ∈ tsupport F
    · simp only [hGdef, hχ1 r (hKV hr), Complex.ofReal_one, one_mul]
    · simp only [weakWaveTest_eq_zero_of_notMem hr, mul_zero]
  have h3 : (fun r : Target => (Real.exp (-r.2.im) : ℂ) * weakFieldOperator G r * F r) = fun r =>
      (Real.exp (-r.2.im) : ℂ) * timeOriginalForcing q br a r.1.1 r.1.2
        ![r.2.re, Real.exp r.2.im] * F r := by
    funext r
    by_cases hr : r ∈ tsupport F
    · have hGU : G =ᶠ[𝓝 r] eventPotential q br a := by
        filter_upwards [hV.mem_nhds (hKV hr)] with y hy
        simp only [hGdef, hχ1 y hy, Complex.ofReal_one, one_mul]
      rw [weakFieldOperator_congr hGU, weakFieldOperator_eventPotential q br a (hW hr)]
    · rw [image_eq_zero_of_notMem_tsupport hr, mul_zero, mul_zero]
  rw [h1, integral_mul_weakWaveTest hG hF hc, h3]

/-- **Weak homogeneity of the retarded–future difference.**  The literal retarded potential and
the corrected future field have the same weak source on every compact test supported in the
physical wedge. -/
theorem eventPotential_sub_correctedFutureField_weak (q : XiZeroCopy) (br : Bool) (a : ℂ)
    {F : Target → ℂ} (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F)
    (hW : tsupport F ⊆ physicalWedge) :
    (∫ r, (eventPotential q br a r - correctedFutureField q br a r) * weakWaveTest F r) = 0 := by
  obtain ⟨hTc, hTcs⟩ := weakWaveTest_regular F hF hc
  have hphys : tsupport F ⊆ {r : Target | r.1.2 < 0} := fun r hr => (hW hr).2
  have iU := eventPotential_mul_weakWaveTest_integrable q br a hF hc hW
  have iC := corrected_future_test_integrable q br a (weakWaveTest F) hTc hTcs
  simp only [sub_mul]
  rw [integral_sub iU iC, eventPotential_weak_wave q br a hF hc hW,
    complete_original_weak_wave q br a F hF hc hphys, sub_self]

end RHTower.D4BMRetardedCompactWeakRealization
