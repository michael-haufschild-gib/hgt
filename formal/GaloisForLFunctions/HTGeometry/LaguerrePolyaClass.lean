import GaloisForLFunctions.HTGeometry.JensenPolynomialLimit

/-!
# The Laguerre–Pólya class

An entire function belongs to the Laguerre–Pólya class when it is a locally uniform limit of real
polynomials that split over `ℝ`.  Two consequences are recorded: all its zeros are real, and all
its Jensen polynomials split over `ℝ`.  The second follows because locally uniform convergence
forces convergence of every Taylor coefficient, and real-rootedness of Jensen polynomials is
preserved by coefficientwise limits.
-/

open Polynomial Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- A real polynomial read as an entire function. -/
def polyEvalC (p : ℝ[X]) : ℂ → ℂ := fun z => (aeval z p : ℂ)

theorem polyEvalC_eq_eval_map (p : ℝ[X]) (z : ℂ) :
    polyEvalC p z = (p.map (algebraMap ℝ ℂ)).eval z := by
  rw [polyEvalC, Polynomial.aeval_def, Polynomial.eval_map]

theorem polyEvalC_eq (p : ℝ[X]) : polyEvalC p = fun z => (p.map (algebraMap ℝ ℂ)).eval z :=
  funext (polyEvalC_eq_eval_map p)

theorem differentiable_polyEvalC (p : ℝ[X]) : Differentiable ℂ (polyEvalC p) := by
  rw [polyEvalC_eq]
  exact Polynomial.differentiable _

theorem deriv_polyEvalC (p : ℝ[X]) : deriv (polyEvalC p) = polyEvalC (derivative p) := by
  funext z
  rw [polyEvalC_eq p, Polynomial.deriv, polyEvalC_eq_eval_map, Polynomial.derivative_map]

theorem iterate_deriv_polyEvalC (p : ℝ[X]) (j : ℕ) :
    deriv^[j] (polyEvalC p) = polyEvalC ((⇑derivative)^[j] p) := by
  induction j generalizing p with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply, deriv_polyEvalC, ih, Function.iterate_succ_apply]

theorem polyEvalC_zero (p : ℝ[X]) : polyEvalC p 0 = ((p.coeff 0 : ℝ) : ℂ) := by
  rw [polyEvalC_eq_eval_map, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map]
  rfl

theorem iterate_deriv_polyEvalC_zero (p : ℝ[X]) (j : ℕ) :
    deriv^[j] (polyEvalC p) 0 = (j.factorial : ℂ) * ((p.coeff j : ℝ) : ℂ) := by
  rw [iterate_deriv_polyEvalC, polyEvalC_zero, Polynomial.coeff_iterate_derivative]
  simp [Nat.descFactorial_self, nsmul_eq_mul]

theorem differentiable_iterate_deriv {f : ℂ → ℂ} (hf : Differentiable ℂ f) (j : ℕ) :
    Differentiable ℂ (deriv^[j] f) := by
  induction j with
  | zero => simpa using hf
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ih.deriv

theorem tendstoLocallyUniformly_iterate_deriv {Fn : ℕ → ℂ → ℂ} {F : ℂ → ℂ}
    (hconv : TendstoLocallyUniformly Fn F atTop) (hdiff : ∀ m, Differentiable ℂ (Fn m)) :
    ∀ j, TendstoLocallyUniformly (fun m => deriv^[j] (Fn m)) (deriv^[j] F) atTop := by
  intro j
  induction j with
  | zero => simpa using hconv
  | succ j ih =>
      have hstep := (tendstoLocallyUniformlyOn_univ.2 ih).deriv
        (Filter.Eventually.of_forall fun m =>
          (differentiable_iterate_deriv (hdiff m) j).differentiableOn) isOpen_univ
      rw [tendstoLocallyUniformlyOn_univ] at hstep
      simpa [Function.comp_def, Function.iterate_succ_apply'] using hstep

/-- **The Laguerre–Pólya class.** -/
def LaguerrePolya (F : ℂ → ℂ) : Prop :=
  ∃ p : ℕ → ℝ[X], (∀ m, (p m).Splits) ∧
    TendstoLocallyUniformly (fun m => polyEvalC (p m)) F atTop

theorem LaguerrePolya.differentiable {F : ℂ → ℂ} (hF : LaguerrePolya F) :
    Differentiable ℂ F := by
  obtain ⟨p, _, hconv⟩ := hF
  rw [← differentiableOn_univ]
  exact (tendstoLocallyUniformlyOn_univ.2 hconv).differentiableOn
    (Filter.Eventually.of_forall fun m => (differentiable_polyEvalC (p m)).differentiableOn)
    isOpen_univ

theorem tendsto_coeff_of_tendstoLocallyUniformly {F : ℂ → ℂ} {p : ℕ → ℝ[X]}
    (hconv : TendstoLocallyUniformly (fun m => polyEvalC (p m)) F atTop) (j : ℕ) :
    Tendsto (fun m => ((p m).coeff j : ℂ)) atTop (𝓝 (deriv^[j] F 0 / (j.factorial : ℂ))) := by
  have hd := tendstoLocallyUniformly_iterate_deriv hconv
    (fun m => differentiable_polyEvalC (p m)) j
  have hpt : Tendsto (fun m => deriv^[j] (polyEvalC (p m)) 0) atTop (𝓝 (deriv^[j] F 0)) :=
    TendstoLocallyUniformlyOn.tendsto_at (tendstoLocallyUniformlyOn_univ.2 hd) (Set.mem_univ 0)
  have hfac : ((j.factorial : ℂ)) ≠ 0 := by
    exact_mod_cast Nat.cast_ne_zero.2 (Nat.factorial_ne_zero j)
  have h2 : Tendsto (fun m => (j.factorial : ℂ) * ((p m).coeff j : ℂ)) atTop
      (𝓝 (deriv^[j] F 0)) := by
    simpa [iterate_deriv_polyEvalC_zero] using hpt
  have h3 := h2.div_const ((j.factorial : ℂ))
  simpa [mul_div_cancel_left₀ _ hfac] using h3

theorem tendsto_coeff_real_of_tendstoLocallyUniformly {F : ℂ → ℂ} {p : ℕ → ℝ[X]} {c : ℕ → ℝ}
    (hconv : TendstoLocallyUniformly (fun m => polyEvalC (p m)) F atTop)
    (hc : ∀ j, ((c j : ℝ) : ℂ) = deriv^[j] F 0 / (j.factorial : ℂ)) (j : ℕ) :
    Tendsto (fun m => (p m).coeff j) atTop (𝓝 (c j)) := by
  have h := tendsto_coeff_of_tendstoLocallyUniformly hconv j
  rw [← hc j] at h
  have h2 := (Complex.continuous_re.tendsto (((c j : ℝ) : ℂ))).comp h
  simpa [Function.comp_def] using h2

/-- **Jensen's theorem, forward direction.**  Every Jensen polynomial of a Laguerre–Pólya function
splits over `ℝ`. -/
theorem splits_jensenPoly_of_laguerrePolya {F : ℂ → ℂ} {c : ℕ → ℝ}
    (hF : LaguerrePolya F)
    (hc : ∀ j, ((c j : ℝ) : ℂ) = deriv^[j] F 0 / (j.factorial : ℂ)) (d : ℕ) :
    (jensenPoly c d).Splits := by
  obtain ⟨p, hsplit, hconv⟩ := hF
  exact splits_jensenPoly_of_tendsto_coeff hsplit
    (fun j => tendsto_coeff_real_of_tendstoLocallyUniformly hconv hc j) d

/-- **A nonzero Laguerre–Pólya function has only real zeros.** -/
theorem im_eq_zero_of_laguerrePolya {F : ℂ → ℂ} (hF : LaguerrePolya F) {a z : ℂ}
    (ha : F a ≠ 0) (hz : F z = 0) : z.im = 0 := by
  obtain ⟨p, hsplit, hconv⟩ := hF
  have hne : ∀ᶠ m in atTop, p m ≠ 0 := by
    have hpt := (TendstoLocallyUniformlyOn.tendsto_at
      (tendstoLocallyUniformlyOn_univ.2 hconv) (Set.mem_univ a)).eventually_ne ha
    filter_upwards [hpt] with m hm h0
    exact hm (by simp [h0, polyEvalC])
  have hzeroS : ∀ᶠ m in atTop, ∀ w : ℂ, polyEvalC (p m) w = 0 → w ∈ {w : ℂ | w.im = 0} := by
    filter_upwards [hne] with m hm w hw
    exact im_eq_zero_of_splits (hsplit m) hm hw
  refine zero_mem_closed_of_tendstoLocallyUniformly (S := {w : ℂ | w.im = 0}) hconv
    ?_ (Filter.Eventually.of_forall fun m => differentiable_polyEvalC (p m))
    (isClosed_eq Complex.continuous_im continuous_const) hzeroS ha hz
  have hdiff : Differentiable ℂ F := by
    rw [← differentiableOn_univ]
    exact (tendstoLocallyUniformlyOn_univ.2 hconv).differentiableOn
      (Filter.Eventually.of_forall fun m => (differentiable_polyEvalC (p m)).differentiableOn)
      isOpen_univ
  exact hdiff.differentiableOn.analyticOnNhd isOpen_univ

end

end GaloisForLFunctions.HTGeometry
