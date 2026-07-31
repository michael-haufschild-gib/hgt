import GaloisForLFunctions.HTGeometry.PencilDirectionalDerivation
import GaloisForLFunctions.HTGeometry.PencilExponentialSeed

/-!
# The directional derivation against the shift operators

The derivation `D_w` of the periodic pencil commutes with every translation, hence with the whole
difference-operator algebra, is `ℂ`-linear, and kills constants.  Together with the smoothness of
the dilate combinations these are the facts the `ℂ[δ]`-coefficient kernel argument consumes.

* `dirDeriv_add`, `dirDeriv_const_mul`, `dirDeriv_const` — linearity and constants;
* `dirDeriv_shiftAlgHom` — commutation with the shift algebra;
* `contDiff_dilateSumHom` — the dilate combinations are smooth.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : ℕ}

/-- The line through a point in a fixed direction is differentiable. -/
theorem differentiable_line (z w : Fin d → ℂ) :
    Differentiable ℂ fun t : ℂ => z + t • w :=
  (differentiable_id.smul_const w).const_add z

theorem differentiableAt_comp_line {f : (Fin d → ℂ) → ℂ} (hf : Differentiable ℂ f)
    (z w : Fin d → ℂ) (t : ℂ) : DifferentiableAt ℂ (fun s : ℂ => f (z + s • w)) t :=
  (hf _).comp t (differentiable_line z w t)

/-! ### Linearity and constants -/

theorem dirDeriv_const (w : Fin d → ℂ) (c : ℂ) :
    dirDeriv w (fun _ : Fin d → ℂ => c) = fun _ => 0 := by
  funext z
  show deriv (fun _ : ℂ => c) 0 = 0
  simp

theorem dirDeriv_add {f g : (Fin d → ℂ) → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    (w : Fin d → ℂ) :
    dirDeriv w (fun z => f z + g z) = fun z => dirDeriv w f z + dirDeriv w g z := by
  funext z
  show deriv (fun t : ℂ => f (z + t • w) + g (z + t • w)) 0 = _
  exact deriv_fun_add (differentiableAt_comp_line hf z w 0) (differentiableAt_comp_line hg z w 0)

theorem dirDeriv_const_mul {f : (Fin d → ℂ) → ℂ} (hf : Differentiable ℂ f) (c : ℂ)
    (w : Fin d → ℂ) :
    dirDeriv w (fun z => c * f z) = fun z => c * dirDeriv w f z := by
  funext z
  show deriv (fun t : ℂ => c * f (z + t • w)) 0 = _
  exact deriv_const_mul _ (differentiableAt_comp_line hf z w 0)

theorem dirDeriv_sum {ι : Type*} (s : Finset ι) {f : ι → (Fin d → ℂ) → ℂ}
    (hf : ∀ i ∈ s, Differentiable ℂ (f i)) (w : Fin d → ℂ) :
    dirDeriv w (fun z => ∑ i ∈ s, f i z) = fun z => ∑ i ∈ s, dirDeriv w (f i) z := by
  funext z
  show deriv (fun t : ℂ => ∑ i ∈ s, f i (z + t • w)) 0 = _
  have hterm : ∀ i ∈ s, HasDerivAt (fun t : ℂ => f i (z + t • w)) (dirDeriv w (f i) z) 0 :=
    fun i hi => (differentiableAt_comp_line (hf i hi) z w 0).hasDerivAt
  exact (HasDerivAt.fun_sum hterm).deriv

/-! ### Commutation with the shift algebra -/

/-- **The derivation commutes with every shift operator.** -/
theorem dirDeriv_shiftAlgHom (a : AddMonoidAlgebra ℂ (Fin d → ℂ)) {f : (Fin d → ℂ) → ℂ}
    (hf : Differentiable ℂ f) (w : Fin d → ℂ) :
    dirDeriv w (shiftAlgHom a f) = shiftAlgHom a (dirDeriv w f) := by
  funext z
  show deriv (fun t : ℂ => shiftAlgHom a f (z + t • w)) 0 = _
  have hfun : (fun t : ℂ => shiftAlgHom a f (z + t • w))
      = fun t : ℂ => ∑ γ ∈ a.coeff.support, a.coeff γ * f ((z + γ) + t • w) := by
    funext t
    rw [shiftAlgHom_apply]
    refine Finset.sum_congr rfl fun γ _ => ?_
    congr 2
    abel
  rw [hfun]
  have hterm : ∀ γ ∈ a.coeff.support,
      HasDerivAt (fun t : ℂ => a.coeff γ * f ((z + γ) + t • w))
        (a.coeff γ * dirDeriv w f (z + γ)) 0 := by
    intro γ _
    exact ((differentiableAt_comp_line hf (z + γ) w 0).hasDerivAt).const_mul _
  rw [(HasDerivAt.fun_sum hterm).deriv, shiftAlgHom_apply]

/-! ### Smoothness of the dilate combinations -/

theorem contDiff_dilateSumHom {E : Type*} [AddCommMonoid E] (a : AddMonoidAlgebra ℂ E)
    (L : E →+ ℂ) : ContDiff ℂ (⊤ : ℕ∞) (dilateSumHom a L) := by
  have hfun : dilateSumHom a L
      = fun u => ∑ γ ∈ a.coeff.support,
          a.coeff γ * Complex.exp (Complex.exp (L γ) * u) := rfl
  rw [hfun]
  exact ContDiff.sum fun γ _ =>
    contDiff_const.mul (Complex.contDiff_exp.comp (contDiff_const.mul contDiff_id))

theorem differentiable_dilateSumHom' {E : Type*} [AddCommMonoid E] (a : AddMonoidAlgebra ℂ E)
    (L : E →+ ℂ) : Differentiable ℂ (dilateSumHom a L) :=
  (contDiff_dilateSumHom a L).differentiable (by simp)

end

end GaloisForLFunctions.HTGeometry
