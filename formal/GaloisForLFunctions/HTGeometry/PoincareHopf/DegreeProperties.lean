import GaloisForLFunctions.HTGeometry.PoincareHopf.HomotopyInvariance
import GaloisForLFunctions.HTGeometry.PoincareHopf.Degree

/-!
# Structural properties of the Brouwer degree

* homotopy invariance along an affine path that never meets `y` on `∂Ω`;
* excision: the degree only sees a neighbourhood of the solution set `f⁻¹ y`;
* normalization: the identity map has degree one at every interior point.
-/

open Matrix Finset Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ} {f g : (Fin n → ℝ) → (Fin n → ℝ)} {Ω Ω' : Set (Fin n → ℝ)} {y : Fin n → ℝ}
  {ρ : ℝ}

theorem linPath_sub_const (y : Fin n → ℝ) (t : ℝ) (x : Fin n → ℝ) :
    linPath (fun x => f x - y) (fun x => g x - y) t x = linPath f g t x - y := by
  simp only [linPath]
  abel_nf

/-- **Homotopy invariance of the degree** along an affine path. -/
theorem degree_eq_of_linPath (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g)
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hρ : 0 < ρ)
    (hfront : ∀ t ∈ Icc (0 : ℝ) 1, ∀ x ∈ frontier Ω, ρ + ρ < ‖linPath f g t x - y‖) :
    degree f Ω y = degree g Ω y := by
  have hadmf : AdmissibleRadius f Ω y ρ := by
    refine ⟨hρ, fun x hx => ?_⟩
    have := hfront 0 ⟨le_refl 0, zero_le_one⟩ x hx
    rwa [linPath_zero] at this
  have hadmg : AdmissibleRadius g Ω y ρ := by
    refine ⟨hρ, fun x hx => ?_⟩
    have := hfront 1 ⟨zero_le_one, le_refl 1⟩ x hx
    rwa [linPath_one] at this
  have hbc : ContDiff ℝ 1 (bumpWeight (n := n) ρ) := bumpWeight_contDiff hρ
  have hbs : ∀ w : Fin n → ℝ, ρ ≤ ‖w‖ → bumpWeight ρ w = 0 := bumpWeight_eq_zero hρ
  have hbm : ∫ w, bumpWeight (n := n) ρ w = 1 := bumpWeight_integral hρ
  rw [degree_eq_degIntegral hf hΩ hΩb hadmf hbc hbs hbm,
    degree_eq_degIntegral hg hΩ hΩb hadmg hbc hbs hbm]
  refine (degIntegral_linPath_eq (f := fun x => f x - y) (g := fun x => g x - y)
    (hf.sub contDiff_const) (hg.sub contDiff_const) hbc hbs hΩ hΩb ?_).symm
  intro t ht x hx
  rw [linPath_sub_const]
  have := hfront t ht x hx
  linarith

/-- **Excision.**  The degree does not change when `Ω` is shrunk to an open subset containing all
solutions of `f x = y`. -/
theorem degree_eq_of_subset (hf : ContDiff ℝ 2 f)
    (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hΩ' : IsOpen Ω') (hsub : Ω' ⊆ Ω)
    (hout : ∀ x ∈ closure Ω \ Ω', f x ≠ y) :
    degree f Ω y = degree f Ω' y := by
  classical
  have hΩ'b : Bornology.IsBounded Ω' := hΩb.subset hsub
  have hK : IsCompact (closure Ω \ Ω') := by
    refine Metric.isCompact_of_isClosed_isBounded ?_ (hΩb.closure.subset diff_subset)
    exact isClosed_closure.sdiff hΩ'
  rcases eq_empty_or_nonempty (closure Ω \ Ω') with hemp | hne
  · have hΩΩ' : Ω = Ω' := by
      refine subset_antisymm (fun x hx => ?_) hsub
      by_contra hcon
      exact absurd (Set.eq_empty_iff_forall_notMem.mp hemp x ⟨subset_closure hx, hcon⟩) (by simp)
    rw [hΩΩ']
  · obtain ⟨x₀, hx₀, hmin⟩ := hK.exists_isMinOn hne
      (((hf.continuous.sub continuous_const).norm).continuousOn)
    have hpos : 0 < ‖f x₀ - y‖ := by
      rw [norm_pos_iff, sub_ne_zero]
      exact hout x₀ hx₀
    set ρ₀ := ‖f x₀ - y‖ / 3 with hρ₀
    have hρ₀pos : 0 < ρ₀ := by rw [hρ₀]; linarith
    have hKbound : ∀ x ∈ closure Ω \ Ω', ρ₀ + ρ₀ < ‖f x - y‖ := by
      intro x hx
      have hle : ‖f x₀ - y‖ ≤ ‖f x - y‖ := hmin hx
      rw [hρ₀]
      linarith
    have hfrontΩ : frontier Ω ⊆ closure Ω \ Ω' := by
      intro x hx
      rw [hΩ.frontier_eq] at hx
      exact ⟨hx.1, fun h => hx.2 (hsub h)⟩
    have hfrontΩ' : frontier Ω' ⊆ closure Ω \ Ω' := by
      intro x hx
      rw [hΩ'.frontier_eq] at hx
      exact ⟨closure_mono hsub hx.1, hx.2⟩
    have hadm : AdmissibleRadius f Ω y ρ₀ := ⟨hρ₀pos, fun x hx => hKbound x (hfrontΩ hx)⟩
    have hadm' : AdmissibleRadius f Ω' y ρ₀ := ⟨hρ₀pos, fun x hx => hKbound x (hfrontΩ' hx)⟩
    have hbc : ContDiff ℝ 1 (bumpWeight (n := n) ρ₀) := bumpWeight_contDiff hρ₀pos
    have hbs : ∀ w : Fin n → ℝ, ρ₀ ≤ ‖w‖ → bumpWeight ρ₀ w = 0 := bumpWeight_eq_zero hρ₀pos
    have hbm : ∫ w, bumpWeight (n := n) ρ₀ w = 1 := bumpWeight_integral hρ₀pos
    rw [degree_eq_degIntegral hf hΩ hΩb hadm hbc hbs hbm,
      degree_eq_degIntegral hf hΩ' hΩ'b hadm' hbc hbs hbm]
    set h : (Fin n → ℝ) → ℝ := fun x => bumpWeight ρ₀ (f x - y) * (jac (fun x => f x - y) x).det
      with hh
    have hind : Ω.indicator h = Ω'.indicator h := by
      funext x
      by_cases hxΩ' : x ∈ Ω'
      · rw [Set.indicator_of_mem (hsub hxΩ') , Set.indicator_of_mem hxΩ']
      · rw [Set.indicator_of_notMem hxΩ']
        by_cases hxΩ : x ∈ Ω
        · rw [Set.indicator_of_mem hxΩ, hh]
          have hmem : x ∈ closure Ω \ Ω' := ⟨subset_closure hxΩ, hxΩ'⟩
          have hb := hKbound x hmem
          show bumpWeight ρ₀ (f x - y) * (jac (fun x => f x - y) x).det = 0
          rw [hbs (f x - y) (by linarith), zero_mul]
        · rw [Set.indicator_of_notMem hxΩ]
    calc degIntegral (fun x => f x - y) Ω (bumpWeight ρ₀)
        = ∫ x, Ω.indicator h x := by
          rw [degIntegral, ← MeasureTheory.integral_indicator hΩ.measurableSet]
      _ = ∫ x, Ω'.indicator h x := by rw [hind]
      _ = degIntegral (fun x => f x - y) Ω' (bumpWeight ρ₀) := by
          rw [degIntegral, ← MeasureTheory.integral_indicator hΩ'.measurableSet]

theorem jac_id (x : Fin n → ℝ) : jac (fun z : Fin n → ℝ => z) x = 1 := by
  have h : HasFDerivAt (fun z : Fin n → ℝ => z) (ContinuousLinearMap.id ℝ (Fin n → ℝ)) x :=
    hasFDerivAt_id x
  funext a b
  rw [jac, Matrix.of_apply, h.fderiv]
  simp [Matrix.one_apply, Pi.single_apply]

/-- **Normalization.**  The identity map has degree one at every point of `Ω`. -/
theorem degree_id (hΩ : IsOpen Ω) (hΩb : Bornology.IsBounded Ω) (hy : y ∈ Ω) :
    degree (fun z : Fin n → ℝ => z) Ω y = 1 := by
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hΩ y hy
  set ρ₀ := r / 3 with hρ₀
  have hρ₀pos : 0 < ρ₀ := by rw [hρ₀]; linarith
  have hadm : AdmissibleRadius (fun z : Fin n → ℝ => z) Ω y ρ₀ := by
    refine ⟨hρ₀pos, fun x hx => ?_⟩
    have hxΩ : x ∉ Ω := by
      rw [hΩ.frontier_eq] at hx
      exact hx.2
    have hrle : r ≤ ‖x - y‖ := by
      by_contra hcon
      exact hxΩ (hball (by rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_not_ge hcon))
    rw [hρ₀]
    linarith
  have hbc : ContDiff ℝ 1 (bumpWeight (n := n) ρ₀) := bumpWeight_contDiff hρ₀pos
  have hbs : ∀ w : Fin n → ℝ, ρ₀ ≤ ‖w‖ → bumpWeight ρ₀ w = 0 := bumpWeight_eq_zero hρ₀pos
  have hbm : ∫ w, bumpWeight (n := n) ρ₀ w = 1 := bumpWeight_integral hρ₀pos
  rw [degree_eq_degIntegral (f := fun z : Fin n → ℝ => z) contDiff_id hΩ hΩb hadm hbc hbs hbm]
  have hjac : ∀ x : Fin n → ℝ, (jac (fun z : Fin n → ℝ => z - y) x).det = 1 := by
    intro x
    have h : HasFDerivAt (fun z : Fin n → ℝ => z - y) (ContinuousLinearMap.id ℝ (Fin n → ℝ)) x :=
      (hasFDerivAt_id x).sub_const y
    have : jac (fun z : Fin n → ℝ => z - y) x = 1 := by
      funext a b
      rw [jac, Matrix.of_apply, h.fderiv]
      simp [Matrix.one_apply, Pi.single_apply]
    rw [this, Matrix.det_one]
  have hzero : ∀ x ∉ Ω, bumpWeight ρ₀ (x - y) * (jac (fun z : Fin n → ℝ => z - y) x).det = 0 := by
    intro x hx
    have hrle : r ≤ ‖x - y‖ := by
      by_contra hcon
      exact hx (hball (by rw [Metric.mem_ball, dist_eq_norm]; exact lt_of_not_ge hcon))
    rw [hbs (x - y) (by rw [hρ₀]; linarith), zero_mul]
  rw [degIntegral, MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  have : ∀ x : Fin n → ℝ,
      bumpWeight ρ₀ (x - y) * (jac (fun z : Fin n → ℝ => z - y) x).det = bumpWeight ρ₀ (x - y) := by
    intro x; rw [hjac x, mul_one]
  simp only [this]
  rw [MeasureTheory.integral_sub_right_eq_self (fun w => bumpWeight ρ₀ w) y]
  exact hbm

end GaloisForLFunctions.HTGeometry.PoincareHopf
