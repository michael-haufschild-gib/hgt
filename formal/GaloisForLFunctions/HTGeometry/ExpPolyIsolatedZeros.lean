import GaloisForLFunctions.HTGeometry.AccumulationZeros

/-!
# An identity theorem for exponential polynomials

A real-valued exponential polynomial whose zeros accumulate anywhere is identically zero.

Two ingredients meet.  Rolle propagation (`iteratedDeriv_eq_zero_of_accumZero`) turns accumulation
into the vanishing of every derivative at the accumulation point.  Differentiating an exponential
polynomial multiplies each coefficient by its exponent, so the vanishing derivatives are exactly the
power moments of the weights `C y e^{y t₀}` over the distinct nodes `y`, and Lagrange interpolation
(`coeff_eq_zero_of_forall_pow`) forces those weights — hence the coefficients — to vanish.

No real-analyticity API is used: only Rolle, continuity, and interpolation.  The consequence is that
the zeros of a nonzero exponential polynomial are isolated, which is the structural hypothesis the
Sturm descent of `SturmWindowCount` requires.
-/

open Set Filter

namespace GaloisForLFunctions.HTGeometry

variable {S : Finset ℂ} {C : ℂ → ℂ}

private theorem contDiff_expCombo (S : Finset ℂ) (C : ℂ → ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => ∑ y ∈ S, C y * Complex.exp (y * t)) := by
  refine ContDiff.sum (fun y _ => ?_)
  have hofReal : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun t : ℝ => y * (t : ℂ)) := by
    simpa [smul_eq_mul] using hofReal.const_smul y
  simpa [smul_eq_mul] using (h1.cexp).const_smul (C y)

/-- **The identity theorem.**  If the real part of an exponential polynomial has accumulating zeros,
every coefficient vanishes. -/
theorem coeff_eq_zero_of_accumZero {t₀ : ℝ}
    (hreal : ∀ t : ℝ, (∑ y ∈ S, C y * Complex.exp (y * t)).im = 0)
    (hacc : AccumZero (fun t => (∑ y ∈ S, C y * Complex.exp (y * t)).re) t₀) :
    ∀ y ∈ S, C y = 0 := by
  set F : ℝ → ℂ := fun t => ∑ y ∈ S, C y * Complex.exp (y * t) with hF
  set f : ℝ → ℝ := fun t => (F t).re with hf
  have hFf : ∀ t, F t = ((f t : ℝ) : ℂ) := by
    intro t
    refine Complex.ext ?_ ?_
    · simp [hf]
    · rw [Complex.ofReal_im]
      exact hreal t
  have hFsmooth : ContDiff ℝ (⊤ : ℕ∞) F := contDiff_expCombo S C
  have hfsmooth : ContDiff ℝ (⊤ : ℕ∞) f := by
    rw [hf]
    exact Complex.reCLM.contDiff.comp hFsmooth
  have hall := iteratedDeriv_eq_zero_of_accumZero hfsmooth hacc
  -- the derivatives of the complex form are the real ones, cast
  have htrans : ∀ n : ℕ, iteratedDeriv n F = fun t => ((iteratedDeriv n f t : ℝ) : ℂ) := by
    intro n
    induction n with
    | zero => funext t; rw [iteratedDeriv_zero, iteratedDeriv_zero]; exact hFf t
    | succ n ih =>
      funext t
      rw [iteratedDeriv_succ, ih]
      have hcd : ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv n f) := by
        rw [iteratedDeriv_eq_iterate]
        exact hfsmooth.iterate_deriv n
      have hd : HasDerivAt (iteratedDeriv n f) (iteratedDeriv (n + 1) f t) t := by
        rw [iteratedDeriv_succ]
        exact (hcd.differentiable (by simp) t).hasDerivAt
      exact (hd.ofReal_comp).deriv
  -- hence every power moment of the shifted weights vanishes
  have hmom : ∀ k : ℕ, ∑ y ∈ S, (C y * Complex.exp (y * t₀)) * y ^ k = 0 := by
    intro k
    have e1 : iteratedDeriv k F t₀ = ∑ y ∈ S, C y * y ^ k * Complex.exp (y * t₀) :=
      congrFun (iteratedDeriv_expCombo (S := S) C k) t₀
    have e2 : iteratedDeriv k F t₀ = ((iteratedDeriv k f t₀ : ℝ) : ℂ) := congrFun (htrans k) t₀
    have e3 : (∑ y ∈ S, C y * y ^ k * Complex.exp (y * t₀)) = 0 := by
      rw [← e1, e2, hall k]
      simp
    rw [← e3]
    exact Finset.sum_congr rfl (fun y _ => by ring)
  intro y hy
  have hDy := coeff_eq_zero_of_forall_pow hmom y hy
  exact (mul_eq_zero.mp hDy).resolve_right (Complex.exp_ne_zero _)


/-- **Isolated zeros.**  A nonzero exponential polynomial has no accumulation point of zeros. -/
theorem not_accumZero_of_coeff_ne {t₀ : ℝ} {y₀ : ℂ} (hy₀ : y₀ ∈ S) (hC : C y₀ ≠ 0)
    (hreal : ∀ t : ℝ, (∑ y ∈ S, C y * Complex.exp (y * t)).im = 0) :
    ¬ AccumZero (fun t => (∑ y ∈ S, C y * Complex.exp (y * t)).re) t₀ :=
  fun hacc => hC (coeff_eq_zero_of_accumZero hreal hacc y₀ hy₀)

/-- The punctured-neighbourhood form: around every point some punctured interval is zero-free. -/
theorem exists_punctured_zero_free {t₀ : ℝ} {y₀ : ℂ} (hy₀ : y₀ ∈ S) (hC : C y₀ ≠ 0)
    (hreal : ∀ t : ℝ, (∑ y ∈ S, C y * Complex.exp (y * t)).im = 0) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ s : ℝ, s ≠ t₀ → |s - t₀| < ε →
      (∑ y ∈ S, C y * Complex.exp (y * s)).re ≠ 0 := by
  have h := not_accumZero_of_coeff_ne (t₀ := t₀) hy₀ hC hreal
  rw [AccumZero] at h
  push Not at h
  obtain ⟨ε, hε, hfree⟩ := h
  exact ⟨ε, hε, fun s hs1 hs2 => hfree s hs1 hs2⟩

end GaloisForLFunctions.HTGeometry
