import GaloisForLFunctions.HTGeometry.CircleIntegralParamOpen

/-!
# Joint holomorphy of slice derivatives

For a jointly holomorphic function of two complex variables, every derivative in the second variable
is again jointly holomorphic.  The proof is the Cauchy integral formula for the first derivative on
a unit circle recentred at the base point, followed by holomorphy of a circle integral in its
parameters and an induction on the order.

The consequence used downstream is that all fibre jets of a jointly entire family depend
holomorphically on the family parameter.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Metric

noncomputable section

/-- Recentering a circle integral. -/
theorem circleIntegral_comp_add_left (f : ℂ → ℂ) (c : ℂ) (R : ℝ) :
    (∮ ζ in C(0, R), f (c + ζ)) = ∮ w in C(c, R), f w := by
  simp only [circleIntegral, deriv_circleMap]
  refine intervalIntegral.integral_congr fun θ _ => ?_
  simp [circleMap]

/-- The derivative of a two-variable function in its second variable. -/
def sliceDeriv (Φ : ℂ × ℂ → ℂ) : ℂ × ℂ → ℂ :=
  fun p => deriv (fun w => Φ (p.1, w)) p.2

theorem sliceDeriv_eq_circleIntegral {Φ : ℂ × ℂ → ℂ} (hΦ : Differentiable ℂ Φ) (p : ℂ × ℂ) :
    sliceDeriv Φ p
      = (2 * (Real.pi : ℂ) * Complex.I)⁻¹ • ∮ ζ in C(0, 1), (1 / ζ ^ 2) • Φ (p.1, p.2 + ζ) := by
  have hf : DifferentiableOn ℂ (fun w => Φ (p.1, w)) (closedBall p.2 1) :=
    (hΦ.comp (by fun_prop : Differentiable ℂ fun w : ℂ => (p.1, w))).differentiableOn
  have hcauchy := hf.deriv_eq_smul_circleIntegral (R := 1) (c := p.2) one_pos
  have htrans : (∮ ζ in C(0, 1), (1 / ζ ^ 2) • Φ (p.1, p.2 + ζ))
      = ∮ w in C(p.2, 1), (1 / (w - p.2) ^ 2) • Φ (p.1, w) := by
    have := circleIntegral_comp_add_left (fun w => (1 / (w - p.2) ^ 2) • Φ (p.1, w)) p.2 1
    simpa using this
  rw [htrans, hcauchy]
  have h2pi : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [smul_smul, inv_mul_cancel₀ h2pi, one_smul]
  rfl

theorem continuous_one_div_circleMap_sq :
    Continuous fun θ : ℝ => 1 / (circleMap 0 1 θ) ^ 2 := by
  refine continuous_const.div (((continuous_circleMap 0 1).pow 2)) fun θ => ?_
  have : circleMap 0 1 θ ≠ 0 := circleMap_ne_center one_ne_zero
  exact pow_ne_zero 2 this

theorem differentiableAt_circleIntegral_slice_prod {Φ : ℂ × ℂ → ℂ} (hΦ : Differentiable ℂ Φ)
    (p : ℂ × ℂ) :
    DifferentiableAt ℂ (fun q : ℂ × ℂ => ∮ ζ in C(0, 1), (1 / ζ ^ 2) • Φ (q.1, q.2 + ζ)) p := by
  classical
  set f : (Fin 3 → ℂ) → ℂ := fun q => Φ (q 1, q 2 + q 0) with hfdef
  have hproj : ∀ i : Fin 3, Differentiable ℂ fun q : Fin 3 → ℂ => q i := fun i =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin 3 => ℂ) i).differentiable
  have hfdiff : Differentiable ℂ f :=
    hΦ.comp (((hproj 1).prodMk ((hproj 2).add (hproj 0))))
  have hint := HTGeometry.differentiableAt_circleIntegral_slice_open (n := 2)
      (f := f) (U := Set.univ) (V := Set.univ) isOpen_univ isOpen_univ hfdiff.differentiableOn
      one_pos (fun ζ => 1 / ζ ^ 2) continuous_one_div_circleMap_sq
      (fun _ _ _ => Set.mem_univ _) (y₀ := ![p.1, p.2]) (Set.mem_univ _)
  have he : Differentiable ℂ fun q : ℂ × ℂ => (![q.1, q.2] : Fin 2 → ℂ) := by
    refine differentiable_pi.2 fun i => ?_
    fin_cases i <;> simp
  have hcomp := hint.comp p (he p)
  refine hcomp.congr_of_eventuallyEq ?_
  filter_upwards with q
  show (∮ ζ in C(0, 1), (1 / ζ ^ 2) • Φ (q.1, q.2 + ζ))
      = ∮ ζ in C(0, 1), (1 / ζ ^ 2) • f (Fin.cons ζ ![q.1, q.2])
  congr 1

theorem differentiable_sliceDeriv {Φ : ℂ × ℂ → ℂ} (hΦ : Differentiable ℂ Φ) :
    Differentiable ℂ (sliceDeriv Φ) := by
  intro p
  have h := (differentiableAt_circleIntegral_slice_prod hΦ p).const_smul
    ((2 * (Real.pi : ℂ) * Complex.I)⁻¹)
  refine h.congr_of_eventuallyEq ?_
  filter_upwards with q
  rw [Pi.smul_apply]
  exact sliceDeriv_eq_circleIntegral hΦ q

/-- The `j`-th derivative of a two-variable function in its second variable. -/
def sliceIteratedDeriv (j : ℕ) (Φ : ℂ × ℂ → ℂ) : ℂ × ℂ → ℂ := sliceDeriv^[j] Φ

theorem sliceIteratedDeriv_zero (Φ : ℂ × ℂ → ℂ) : sliceIteratedDeriv 0 Φ = Φ := rfl

theorem sliceIteratedDeriv_succ (j : ℕ) (Φ : ℂ × ℂ → ℂ) :
    sliceIteratedDeriv (j + 1) Φ = sliceIteratedDeriv j (sliceDeriv Φ) :=
  Function.iterate_succ_apply _ _ _

theorem differentiable_sliceIteratedDeriv {Φ : ℂ × ℂ → ℂ} (hΦ : Differentiable ℂ Φ) (j : ℕ) :
    Differentiable ℂ (sliceIteratedDeriv j Φ) := by
  induction j generalizing Φ with
  | zero => exact hΦ
  | succ j ih =>
      rw [sliceIteratedDeriv_succ]
      exact ih (differentiable_sliceDeriv hΦ)

/-- The slice iterate computes the iterated derivative of the fibre. -/
theorem sliceIteratedDeriv_apply (j : ℕ) (Φ : ℂ × ℂ → ℂ) (t z : ℂ) :
    sliceIteratedDeriv j Φ (t, z) = iteratedDeriv j (fun w => Φ (t, w)) z := by
  induction j generalizing Φ with
  | zero => rw [sliceIteratedDeriv_zero, iteratedDeriv_zero]
  | succ j ih =>
      rw [sliceIteratedDeriv_succ, ih, iteratedDeriv_succ']
      congr 1

/-- **The fibre jets of a jointly entire function are entire in the parameter.** -/
theorem differentiable_param_iteratedDeriv {Φ : ℂ × ℂ → ℂ} (hΦ : Differentiable ℂ Φ) (j : ℕ)
    (z : ℂ) :
    Differentiable ℂ fun t : ℂ => iteratedDeriv j (fun w => Φ (t, w)) z := by
  have h : Differentiable ℂ fun t : ℂ => sliceIteratedDeriv j Φ (t, z) :=
    (differentiable_sliceIteratedDeriv hΦ j).comp (by fun_prop)
  simpa [sliceIteratedDeriv_apply] using h

end

end GaloisForLFunctions.HTGeometry
