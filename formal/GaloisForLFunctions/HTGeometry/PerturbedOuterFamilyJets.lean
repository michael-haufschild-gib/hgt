import GaloisForLFunctions.HTGeometry.FamilyOuterObservationJets

/-!
# The jets of the perturbed outer family

The object of interest is the outer background of a mass parameter corrected by a fixed multiple of a
fixed function, observed along a family of real translates.  Its jets split: the observation of the
mass parameter carries the moving part, and the jets of the fixed correction form a constant vector.

That splitting is what makes a fixed additive perturbation invisible to a transversality argument in
the mass parameter, while the conclusion is still about the perturbed function.
-/

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Smoothness -/

theorem contDiffAt_natCast_of_top {f : ℂ → ℂ} {z : ℂ} (h : ContDiffAt ℂ (⊤ : ℕ∞) f z) (k : ℕ) :
    ContDiffAt ℂ (k : ℕ) f z :=
  h.of_le (by exact_mod_cast le_top)

/-- Smoothness is preserved by translation of the argument. -/
theorem contDiffAt_comp_add_const {f : ℂ → ℂ} {z c : ℂ} {N : WithTop ℕ∞}
    (h : ContDiffAt ℂ N f (z + c)) : ContDiffAt ℂ N (fun w => f (w + c)) z := by
  have hshift : ContDiffAt ℂ N (fun w : ℂ => w + c) z := contDiffAt_id.add contDiffAt_const
  exact h.comp z hshift

/-- **The outer background is smooth above the real axis.**  Its Cauchy transform is, and the Cayley
exponential is smooth wherever the transform avoids `-i`, which it does there. -/
theorem contDiffAt_outerBackground (ν : Measure ℝ) [IsFiniteMeasure ν] {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℂ (⊤ : ℕ∞) (outerBackground ν) z := by
  have hf : ContDiffAt ℂ (⊤ : ℕ∞) (cauchyTransform ν) z :=
    contDiffAt_cauchyTransform ν (ne_of_gt hz)
  have hden : ContDiffAt ℂ (⊤ : ℕ∞) (fun w => cauchyTransform ν w + Complex.I) z :=
    hf.add contDiffAt_const
  have hne : (fun w => cauchyTransform ν w + Complex.I) z ≠ 0 :=
    add_I_ne_zero_of_im_nonneg (im_cauchyTransform_nonneg ν hz)
  have hquot : ContDiffAt ℂ (⊤ : ℕ∞)
      (fun w => (cauchyTransform ν w - Complex.I) / (cauchyTransform ν w + Complex.I)) z :=
    (hf.sub contDiffAt_const).div hden hne
  have hcomp := (Complex.contDiff_exp (𝕜 := ℂ) (n := ((⊤ : ℕ∞) : WithTop ℕ∞))).contDiffAt.comp z
    hquot
  have hval : outerBackground ν = fun w => Complex.exp
      ((cauchyTransform ν w - Complex.I) / (cauchyTransform ν w + Complex.I)) := rfl
  rw [hval]
  exact hcomp

theorem contDiffAt_massOuterBackground {x ε : ℕ → ℝ} (hεpos : ∀ n, 0 < ε n) (hε : Summable ε)
    (u : MassParameter) {z : ℂ} (hz : 0 < z.im) :
    ContDiffAt ℂ (⊤ : ℕ∞) (massOuterBackground x ε u) z := by
  haveI := isFiniteMeasure_massMeasure (x := x) hεpos hε u
  exact contDiffAt_outerBackground _ hz

/-! ## The perturbed family and its carrier jets -/

/-- The perturbed outer family: the real translates of the outer background of a mass parameter,
each corrected by a fixed multiple of a fixed function. -/
def perturbedOuterFamily (x ε : ℕ → ℝ) (u : MassParameter) (c : ℂ) (A : ℂ → ℂ) {r : ℕ}
    (t : Fin r → ℝ) (i : Fin r) : ℂ → ℂ :=
  fun w => massOuterBackground x ε u (w + (t i : ℂ)) + c * A (w + (t i : ℂ))

/-- The jets of the fixed correction at the combined nodes, in the coordinates of the evaluation
matrix. -/
def outerCarrierJets {row : Type*} (r d D : ℕ) (h : r * (d + 1) = D) (z : row → ℂ) (t : Fin r → ℝ)
    (c : ℂ) (A : ℂ → ℂ) : row × Fin D → ℂ :=
  fun p => c * iteratedDeriv ((finProdFinEquiv.symm ((finCongr h).symm p.2)).2 : ℕ) A
    (combinedNodes z t (p.1, (finProdFinEquiv.symm ((finCongr h).symm p.2)).1))

/-- **The observation plus the carrier jets are the jets of the perturbed family.**  This is the
statement that the transversality argument, which moves only the mass parameter, is nevertheless an
argument about the perturbed function. -/
theorem familyOuterObservation_add_carrier_apply {row : Type*} (r d D : ℕ) (h : r * (d + 1) = D)
    (z : row → ℂ) (t : Fin r → ℝ) (hupper : ∀ b, 0 < (z b).im) (x : ℕ → ℝ) {ε : ℕ → ℝ}
    (hεpos : ∀ n, 0 < ε n) (hε : Summable ε) (u : MassParameter) (c : ℂ) {A : ℂ → ℂ}
    (hA : ∀ ζ : ℂ, 0 < ζ.im → ContDiffAt ℂ (⊤ : ℕ∞) A ζ) (b : row) (j : Fin D) :
    (familyOuterObservation r d D h z t x ε u + outerCarrierJets r d D h z t c A) (b, j)
      = iteratedDeriv ((finProdFinEquiv.symm ((finCongr h).symm j)).2 : ℕ)
        (perturbedOuterFamily x ε u c A t (finProdFinEquiv.symm ((finCongr h).symm j)).1) (z b) := by
  set i := (finProdFinEquiv.symm ((finCongr h).symm j)).1 with hi
  set k := (finProdFinEquiv.symm ((finCongr h).symm j)).2 with hk
  have hznode : 0 < (z b + (t i : ℂ)).im := by
    simpa using hupper b
  have hS : ContDiffAt ℂ ((k : ℕ) : ℕ) (fun w => massOuterBackground x ε u (w + (t i : ℂ))) (z b) :=
    contDiffAt_comp_add_const
      (contDiffAt_natCast_of_top (contDiffAt_massOuterBackground hεpos hε u hznode) (k : ℕ))
  have hAt : ContDiffAt ℂ ((k : ℕ) : ℕ) (fun w => c * A (w + (t i : ℂ))) (z b) :=
    contDiffAt_const.mul (contDiffAt_comp_add_const
      (contDiffAt_natCast_of_top (hA _ hznode) (k : ℕ)))
  have hsplit : perturbedOuterFamily x ε u c A t i
      = (fun w => massOuterBackground x ε u (w + (t i : ℂ))) + fun w => c * A (w + (t i : ℂ)) :=
    rfl
  rw [Pi.add_apply, familyOuterObservation_apply r d D h z t hupper x hεpos hε u b j, hsplit,
    iteratedDeriv_add hS hAt, iteratedDeriv_const_mul c
      (contDiffAt_comp_add_const (contDiffAt_natCast_of_top (hA _ hznode) (k : ℕ))),
    iteratedDeriv_translate]
  simp only [iteratedDeriv_translate]
  rfl

end

end GaloisForLFunctions.HTGeometry
