import GaloisForLFunctions.RHTower.DeningerFourierKothe

/-!
# The smooth periodic functions of a given period

Translating by a period does not change a function, so it does not change its derivative either:
the derivative of a periodic function is periodic.  Consequently every iterated derivative of a
smooth periodic function is again continuous and periodic, and successive derivatives are related
by the derivative relation.

That is exactly the data the Fourier decay estimates require, so the coefficients of a smooth
periodic function decay faster than any power.

* `deningerPeriodic_deriv` : the derivative of a periodic function is periodic.
* `DeningerSmoothPeriodic` : the smooth functions of period `T`.
* `deningerSmoothPeriodic_iteratedDeriv_periodic`, `_continuous`, `_hasDerivAt` : the derivative
  tower.
-/

namespace RHTower

section SmoothPeriodic

/-- **The derivative of a periodic function is periodic.** -/
theorem deningerPeriodic_deriv {f : ℝ → ℂ} {T : ℝ} (hf : Function.Periodic f T) :
    Function.Periodic (deriv f) T := by
  intro x
  have hfun : (fun y => f (y + T)) = f := funext hf
  have h1 : deriv (fun y => f (y + T)) x = deriv f (x + T) := deriv_comp_add_const f T x
  rw [hfun] at h1
  exact h1.symm

/-- **The smooth functions of period `T`.** -/
def DeningerSmoothPeriodic (T : ℝ) : Submodule ℂ (ℝ → ℂ) where
  carrier := {f | ContDiff ℝ (⊤ : ℕ∞) f ∧ Function.Periodic f T}
  add_mem' := by
    rintro f g ⟨hfd, hfp⟩ ⟨hgd, hgp⟩
    exact ⟨hfd.add hgd, hfp.add hgp⟩
  zero_mem' := ⟨contDiff_const, fun _ => rfl⟩
  smul_mem' := by
    rintro c f ⟨hfd, hfp⟩
    refine ⟨hfd.const_smul c, fun x => ?_⟩
    show c * f (x + T) = c * f x
    rw [hfp x]

theorem deningerSmoothPeriodic_contDiff {T : ℝ} (f : DeningerSmoothPeriodic T) :
    ContDiff ℝ (⊤ : ℕ∞) (f : ℝ → ℂ) := f.2.1

theorem deningerSmoothPeriodic_periodic {T : ℝ} (f : DeningerSmoothPeriodic T) :
    Function.Periodic (f : ℝ → ℂ) T := f.2.2

/-- **Every iterated derivative of a smooth periodic function is periodic.** -/
theorem deningerSmoothPeriodic_iteratedDeriv_periodic {T : ℝ} (f : DeningerSmoothPeriodic T)
    (k : ℕ) : Function.Periodic (iteratedDeriv k (f : ℝ → ℂ)) T := by
  induction k with
  | zero =>
      simpa [iteratedDeriv_zero] using deningerSmoothPeriodic_periodic f
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact deningerPeriodic_deriv ih

/-- **Every iterated derivative of a smooth periodic function is continuous.** -/
theorem deningerSmoothPeriodic_iteratedDeriv_continuous {T : ℝ} (f : DeningerSmoothPeriodic T)
    (k : ℕ) : Continuous (iteratedDeriv k (f : ℝ → ℂ)) :=
  (deningerSmoothPeriodic_contDiff f).continuous_iteratedDeriv k (by exact_mod_cast le_top)

/-- **Successive iterated derivatives are related by the derivative relation.** -/
theorem deningerSmoothPeriodic_hasDerivAt {T : ℝ} (f : DeningerSmoothPeriodic T) (k : ℕ)
    (x : ℝ) :
    HasDerivAt (iteratedDeriv k (f : ℝ → ℂ)) (iteratedDeriv (k + 1) (f : ℝ → ℂ) x) x := by
  have hdiff : Differentiable ℝ (iteratedDeriv k (f : ℝ → ℂ)) :=
    (deningerSmoothPeriodic_contDiff f).differentiable_iteratedDeriv k (by
      exact_mod_cast ENat.coe_lt_top k)
  have h := (hdiff x).hasDerivAt
  rw [iteratedDeriv_succ]
  exact h

/-- The values of an iterated derivative at the ends of a period agree. -/
theorem deningerSmoothPeriodic_iteratedDeriv_end {T : ℝ} (f : DeningerSmoothPeriodic T)
    (k : ℕ) : iteratedDeriv k (f : ℝ → ℂ) T = iteratedDeriv k (f : ℝ → ℂ) 0 := by
  have h := deningerSmoothPeriodic_iteratedDeriv_periodic f k 0
  simpa using h

/-- **An iterated derivative is bounded over a period**, being continuous on a compact
interval. -/
theorem deningerSmoothPeriodic_exists_bound {T : ℝ} (f : DeningerSmoothPeriodic T) (k : ℕ) :
    ∃ M : ℝ, ∀ x ∈ Set.uIoc (0 : ℝ) T, ‖iteratedDeriv k (f : ℝ → ℂ) x‖ ≤ M := by
  obtain ⟨M, hM⟩ := (isCompact_uIcc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
    (deningerSmoothPeriodic_iteratedDeriv_continuous f k).continuousOn
  exact ⟨M, fun x hx => hM x (Set.uIoc_subset_uIcc hx)⟩

/-- **The Fourier coefficients of a smooth periodic function decay faster than any power.** -/
theorem deningerSmoothPeriodic_coeff_decay {T : ℝ} (hT : 0 < T) (f : DeningerSmoothPeriodic T)
    (k : ℕ) : ∃ M : ℝ, ∀ n : ℤ, n ≠ 0 →
      ‖deningerFourierCoeff T (f : ℝ → ℂ) n‖ ≤ (T / (2 * Real.pi * |(n : ℝ)|)) ^ k * M := by
  obtain ⟨M, hM⟩ := deningerSmoothPeriodic_exists_bound f k
  refine ⟨M, fun n hn => ?_⟩
  have hzero : iteratedDeriv 0 (f : ℝ → ℂ) = (f : ℝ → ℂ) := iteratedDeriv_zero
  have hdecay := deningerFourierCoeff_rapid_decay hT (fun j => iteratedDeriv j (f : ℝ → ℂ))
    (fun j x => deningerSmoothPeriodic_hasDerivAt f j x)
    (fun j => deningerSmoothPeriodic_iteratedDeriv_continuous f j)
    (fun j => deningerSmoothPeriodic_iteratedDeriv_end f j) hn k hM
  rwa [hzero] at hdecay

end SmoothPeriodic

end RHTower
