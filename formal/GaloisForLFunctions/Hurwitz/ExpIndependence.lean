/-
# Distinct-exponent independence (the Hurwitz analytic core, exp form)

The single deep analytic input of the Hurwitz quadratic descent is that distinct complex exponents are
independent: a finite combination `∑ c_k x^{α_k}` of distinct power germs cannot vanish unless all
`c_k = 0`. Substituting `x^α = exp(α · z)` (`z = log x`) turns this into linear independence of the
entire functions `z ↦ exp(α_k z)` for distinct `α_k`, proved here by the clean
**differentiate-then-Vandermonde** argument:

* the `j`-th derivative of `∑ c_k exp(α_k z)` is `∑ c_k α_k^j exp(α_k z)` (`exp(α·)` is an eigenfunction
  of `d/dz` with eigenvalue `α`);
* if the combination is the zero function, evaluating all derivatives at `z = 0` gives
  `∑ c_k α_k^j = 0` for every `j`;
* the `n × n` system (`j < n`) is the **Vandermonde** system in the distinct `α_k`, invertible, so
  `c = 0`.

This is the Hurwitz analogue of the u₀ natural-boundary transcendence: the irreducible analytic fact
the algebraic engine (`OrbitObstruction`, `MonodromyScalar`) is fed by.
-/
import Mathlib

open Complex Polynomial Matrix

namespace HurwitzExp

/-- `exp(β·)` is an eigenfunction of `d/dz`: `HasDerivAt`. -/
theorem hasDerivAt_expLin (β z : ℂ) :
    HasDerivAt (fun w : ℂ => Complex.exp (β * w)) (β * Complex.exp (β * z)) z := by
  have h : HasDerivAt (fun w : ℂ => β * w) β z := by simpa using (hasDerivAt_id z).const_mul β
  simpa [mul_comm] using h.cexp

/-- `exp(β·)` is `C^∞`. -/
theorem contDiff_expLin (β : ℂ) {n : ℕ} : ContDiff ℂ n (fun z : ℂ => Complex.exp (β * z)) :=
  Complex.contDiff_exp.comp (contDiff_const.mul contDiff_id)

/-- **Eigenfunction iterated derivative:** `(d/dz)^n exp(β z) = β^n exp(β z)`. -/
theorem iteratedDeriv_expLin (β : ℂ) (n : ℕ) :
    iteratedDeriv n (fun z : ℂ => Complex.exp (β * z)) = fun z => β ^ n * Complex.exp (β * z) := by
  induction n with
  | zero => simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext z
    rw [deriv_const_mul _ (hasDerivAt_expLin β z).differentiableAt, (hasDerivAt_expLin β z).deriv]
    ring

/-- Iterated derivative splits over a finite sum of `C^n` functions. -/
theorem iteratedDeriv_finset_sum {ι : Type*} (u : Finset ι) (n : ℕ) {f : ι → ℂ → ℂ}
    (hf : ∀ i ∈ u, ContDiff ℂ n (f i)) (x : ℂ) :
    iteratedDeriv n (fun z => ∑ i ∈ u, f i z) x = ∑ i ∈ u, iteratedDeriv n (f i) x := by
  simp only [iteratedDeriv_eq_iteratedFDeriv]
  rw [iteratedFDeriv_sum hf, Finset.sum_apply, ContinuousMultilinearMap.sum_apply]

/-- **Distinct-exponent independence (exp form).** The entire functions `z ↦ exp(β_k z)`, for pairwise
distinct `β_k`, are `ℂ`-linearly independent: differentiate `j` times and evaluate at `0` to get the
Vandermonde system `∑_k c_k β_k^j = 0`, invertible by distinctness. The analytic core of the Hurwitz
quadratic descent. -/
theorem expLin_linearIndependent {n : ℕ} {β : Fin n → ℂ} (hβ : Function.Injective β) :
    LinearIndependent ℂ (fun k : Fin n => (fun z : ℂ => Complex.exp (β k * z))) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hzero : (fun z : ℂ => ∑ k, c k * Complex.exp (β k * z)) = 0 := by
    funext z
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using congrFun hc z
  have hpow : ∀ j : ℕ, ∑ k, c k * β k ^ j = 0 := by
    intro j
    have key : iteratedDeriv j (fun z : ℂ => ∑ k, c k * Complex.exp (β k * z)) 0 = 0 := by
      rw [hzero]; simp [iteratedDeriv]
    rw [iteratedDeriv_finset_sum _ j (fun k _ => contDiff_const.mul (contDiff_expLin (β k))) 0] at key
    simp only [iteratedDeriv_const_mul_field, iteratedDeriv_expLin, mul_zero, Complex.exp_zero,
      mul_one] at key
    exact key
  have hdet : (Matrix.vandermonde β).det ≠ 0 := by
    rw [Matrix.det_vandermonde]
    refine Finset.prod_ne_zero_iff.mpr (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j hj => ?_))
    rw [Finset.mem_Ioi] at hj
    exact sub_ne_zero.mpr (fun h => (ne_of_lt hj) (hβ h).symm)
  have hmv : (Matrix.vandermonde β)ᵀ *ᵥ c = 0 := by
    funext j
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Matrix.vandermonde_apply,
      Pi.zero_apply]
    rw [← hpow (j : ℕ)]
    exact Finset.sum_congr rfl (fun k _ => mul_comm _ _)
  have hc0 : c = 0 := Matrix.eq_zero_of_mulVec_eq_zero (by rwa [Matrix.det_transpose]) hmv
  exact fun k => congrFun hc0 k

/-- **Application-ready local form.** If `∑ c_k exp(β_k z) = 0` merely on a *nonempty open* `U ⊆ ℂ`
(with distinct `β_k`), then `c = 0`: the combination is entire, so vanishing on `U` forces vanishing
everywhere (identity theorem), then `expLin_linearIndependent` applies. This is the form the Hurwitz
exponent filtration consumes — the singular relation holds only on a punctured neighborhood of the
collision point. -/
theorem expLin_eq_zero_on_open {n : ℕ} {β : Fin n → ℂ} (hβ : Function.Injective β) {c : Fin n → ℂ}
    {U : Set ℂ} (hUo : IsOpen U) (hUne : U.Nonempty)
    (h : ∀ z ∈ U, ∑ k, c k * Complex.exp (β k * z) = 0) : c = 0 := by
  set g : ℂ → ℂ := fun z => ∑ k, c k * Complex.exp (β k * z) with hg
  have hdiff : Differentiable ℂ g := by
    apply Differentiable.fun_sum
    intro k _
    exact (differentiable_const _).mul
      (Complex.differentiable_exp.comp ((differentiable_const _).mul differentiable_id))
  have hg_an : AnalyticOnNhd ℂ g Set.univ := hdiff.differentiableOn.analyticOnNhd isOpen_univ
  obtain ⟨z0, hz0⟩ := hUne
  have hfreq : ∃ᶠ z in nhdsWithin z0 {z0}ᶜ, g z = 0 :=
    ((Filter.eventually_iff.mpr (Filter.mem_of_superset (hUo.mem_nhds hz0)
      (fun z hz => h z hz))).filter_mono nhdsWithin_le_nhds).frequently
  have hg0 : ∀ z, g z = 0 := fun z =>
    hg_an.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ (Set.mem_univ z0)
      hfreq (Set.mem_univ z)
  have hLI := expLin_linearIndependent hβ
  rw [Fintype.linearIndependent_iff] at hLI
  have hsum : (∑ i, c i • fun z => Complex.exp (β i * z)) = 0 := by
    funext z
    simpa [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using hg0 z
  funext k
  exact hLI c hsum k

end HurwitzExp
