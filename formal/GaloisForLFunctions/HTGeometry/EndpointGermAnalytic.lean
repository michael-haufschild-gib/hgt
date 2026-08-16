import Mathlib

/-!
# `(20)`: the endpoint germ of an entire datum is analytic in the boundary variable

The physical boundary variable is `r = e^{-L}`.  A datum that is entire in the characteristic
variable — in particular any finite exponential polynomial `Σ_j P_j(x)e^{λ_j x}` — composed with the
endpoint map `r ↦ a − r` is again entire, so its Taylor series at the endpoint converges everywhere;
substituting `r = e^{-L}` turns that series into a Dirichlet series in `e^{-L}` which converges
normally on every terminal ray.  That is exactly the source class the scale-gap theorem assumes,
so the square-Evans reconstruction forcing lies inside it.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- The `n`-th coefficient of the endpoint germ of `f` at `a`. -/
def endpointGermCoeff (f : ℂ → ℂ) (a : ℂ) (n : ℕ) : ℂ :=
  ((n.factorial : ℂ))⁻¹ * iteratedDeriv n (fun r : ℂ => f (a - r)) 0

theorem differentiable_endpointShift {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a : ℂ) :
    Differentiable ℂ fun r : ℂ => f (a - r) :=
  fun r => (hf (a - r)).comp r ((differentiable_id.const_sub a) r)

/-- **`(20)`: the endpoint germ is a Dirichlet series in `e^{-L}`.** -/
theorem hasSum_endpointGerm {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a : ℂ) (L : ℝ) :
    HasSum (fun n : ℕ => endpointGermCoeff f a n * ((Real.exp (-((n : ℝ) * L)) : ℝ) : ℂ))
      (f (a - ((Real.exp (-L) : ℝ) : ℂ))) := by
  have hg := differentiable_endpointShift hf a
  have h := hasSum_taylorSeries_of_entire hg 0 (((Real.exp (-L) : ℝ) : ℂ))
  refine h.congr_fun fun n => ?_
  have hpow : ((((Real.exp (-L) : ℝ) : ℂ)) - 0) ^ n = ((Real.exp (-((n : ℝ) * L)) : ℝ) : ℂ) := by
    rw [sub_zero, ← Complex.ofReal_pow, ← Real.exp_nat_mul]
    push_cast
    ring_nf
  rw [smul_eq_mul, smul_eq_mul, hpow, endpointGermCoeff]
  ring

/-- **The germ converges normally on every terminal ray.** -/
theorem summable_norm_endpointGerm {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a : ℂ) (L₀ : ℝ) :
    Summable fun n : ℕ => ‖endpointGermCoeff f a n‖ * Real.exp (-((n : ℝ) * L₀)) := by
  have h := (hasSum_endpointGerm hf a (L₀ - Real.log 2)).summable
  have h0 := h.tendsto_atTop_zero
  have hnorm : Filter.Tendsto
      (fun n : ℕ => ‖endpointGermCoeff f a n
        * ((Real.exp (-((n : ℝ) * (L₀ - Real.log 2))) : ℝ) : ℂ)‖) Filter.atTop (nhds 0) := by
    simpa using h0.norm
  obtain ⟨M, hM⟩ := hnorm.bddAbove_range
  have hMbd : ∀ n : ℕ, ‖endpointGermCoeff f a n‖
      * Real.exp (-((n : ℝ) * (L₀ - Real.log 2))) ≤ M := by
    intro n
    have := hM (Set.mem_range_self n)
    rwa [norm_mul, Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le] at this
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (Summable.mul_left M (summable_geometric_of_lt_one (by norm_num) (by norm_num : (1:ℝ)/2 < 1)))
  have hsplit : Real.exp (-((n : ℝ) * L₀))
      = Real.exp (-((n : ℝ) * (L₀ - Real.log 2))) * ((1 : ℝ) / 2) ^ n := by
    rw [show ((1 : ℝ) / 2) ^ n = Real.exp (-((n : ℝ) * Real.log 2)) by
      rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log (by norm_num : (0:ℝ) < 2)]
      rw [div_pow, one_pow]
      norm_num, ← Real.exp_add]
    congr 1
    ring
  rw [hsplit, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right (hMbd n) (by positivity)

/-- A finite exponential polynomial is entire. -/
theorem differentiable_expPolynomial {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℂ)
    (lam : ι → ℂ) :
    Differentiable ℂ fun x : ℂ => ∑ j ∈ s, (P j).eval x * Complex.exp (lam j * x) := by
  have hterm : ∀ j ∈ s, Differentiable ℂ fun x : ℂ => (P j).eval x * Complex.exp (lam j * x) := by
    intro j _
    have h1 : Differentiable ℂ fun x : ℂ => (P j).eval x := (P j).differentiable
    have h2 : Differentiable ℂ fun x : ℂ => Complex.exp (lam j * x) :=
      Complex.differentiable_exp.comp ((differentiable_id (𝕜 := ℂ)).const_mul (lam j))
    exact h1.mul h2
  have h := Differentiable.sum hterm
  have hfun : (∑ i ∈ s, fun x : ℂ => (P i).eval x * Complex.exp (lam i * x))
      = fun x : ℂ => ∑ j ∈ s, (P j).eval x * Complex.exp (lam j * x) := by
    funext x
    rw [Finset.sum_apply]
  rwa [hfun] at h

/-- **`(20)`: every finite exponential-polynomial datum has an analytic endpoint germ.** -/
theorem hasSum_endpointGerm_expPolynomial {ι : Type*} (s : Finset ι) (P : ι → Polynomial ℂ)
    (lam : ι → ℂ) (a : ℂ) (L : ℝ) :
    HasSum (fun n : ℕ =>
        endpointGermCoeff (fun x : ℂ => ∑ j ∈ s, (P j).eval x * Complex.exp (lam j * x)) a n
          * ((Real.exp (-((n : ℝ) * L)) : ℝ) : ℂ))
      (∑ j ∈ s, (P j).eval (a - ((Real.exp (-L) : ℝ) : ℂ))
        * Complex.exp (lam j * (a - ((Real.exp (-L) : ℝ) : ℂ)))) :=
  hasSum_endpointGerm (differentiable_expPolynomial s P lam) a L

end GaloisForLFunctions.HTGeometry
