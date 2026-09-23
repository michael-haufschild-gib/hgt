/-
# The trace is the only coordinate the Hilbert–Carleman determinant forgets

On finite rank the determinant and its second-order regularization differ by the exponential of the
first power trace,

  `det(1 − zA) = det₂(1 − zA)·exp(−z·tr A)`,

and the trace is exactly the coordinate that does not extend continuously to the Hilbert–Schmidt
completion.  Completing the determinant graph at Schatten order two therefore means adjoining one
scalar, the linear jet `−cz`, and this file shows that scalar is recovered by a single derivative:

  `det₂(1 − zK)·e^{−cz}` has derivative `−c` at the origin,

because the regularized determinant itself has vanishing linear Taylor coefficient.  Consequently
the completion coordinate is faithful, and along Hilbert–Schmidt-convergent kernels every locally
uniform limit of completed determinants is again a completed determinant, with the coordinates
converging.

Main results:
* `taylorCoeff_finiteDet2_one` — the trace counterterm cancels the linear term of `det(1 + zM)`.
* `detCoeff_one_eq_zero`, `deriv_entireDet2_zero` — the same for a Hilbert–Schmidt kernel.
* `completedDet2`, `deriv_completedDet2_zero` — the completion and its coordinate functional.
* `completedDet2_inj` — the coordinate is faithful.
* `tendsto_completionCoefficient` — necessity in the determinant-completion law at order two.
-/
import GaloisForLFunctions.HTGeometry.EntireDet2HilbertSchmidtContinuity

open HilbertSchmidt Metric Filter

namespace GaloisForLFunctions.HTGeometry

/-! ## The finite regularized determinant is flat to first order -/

variable {m : Type*} [Fintype m] [DecidableEq m]

/-- **The trace counterterm cancels the linear term.**  The finite regularized determinant
`det(1 + zM)·exp(−z·tr M)` has vanishing first Taylor coefficient at the origin. -/
theorem taylorCoeff_finiteDet2_one (M : Matrix m m ℂ) :
    taylorCoeff (fun z => finiteDet2 M z) 1 = 0 := by
  obtain ⟨P, hP⟩ : ∃ P : Polynomial ℂ, ∀ z : ℂ,
      ((1 : Matrix m m ℂ) + z • M).det = 1 + M.trace * z + Polynomial.eval z P * z ^ (2 : ℕ) :=
    ⟨(1 + Polynomial.X • M.map (Polynomial.C : ℂ →+* Polynomial ℂ)).det.divX.divX,
      fun z => Matrix.det_one_add_smul z M⟩
  have hfun : (fun z : ℂ => finiteDet2 M z)
      = fun z : ℂ => (1 + M.trace * z + Polynomial.eval z P * z ^ (2 : ℕ))
          * Complex.exp (-(z * M.trace)) := by
    funext z
    rw [finiteDet2, hP z]
  have hA : HasDerivAt (fun z : ℂ => 1 + M.trace * z) M.trace 0 :=
    (((hasDerivAt_id (0 : ℂ)).const_mul M.trace).const_add (1 : ℂ)).congr_deriv (by ring)
  have hB : HasDerivAt (fun z : ℂ => Polynomial.eval z P * z ^ (2 : ℕ)) 0 0 :=
    ((P.hasDerivAt (0 : ℂ)).mul (hasDerivAt_pow 2 (0 : ℂ))).congr_deriv (by norm_num)
  have hg : HasDerivAt
      (fun z : ℂ => 1 + M.trace * z + Polynomial.eval z P * z ^ (2 : ℕ)) M.trace 0 :=
    (hA.add hB).congr_deriv (by ring)
  have hi : HasDerivAt (fun z : ℂ => -(z * M.trace)) (-M.trace) 0 :=
    (((hasDerivAt_id (0 : ℂ)).mul_const M.trace).neg).congr_deriv (by ring)
  have hh : HasDerivAt (fun z : ℂ => Complex.exp (-(z * M.trace))) (-M.trace) 0 :=
    hi.cexp.congr_deriv (by simp)
  have hprod : HasDerivAt (fun z : ℂ => finiteDet2 M z) 0 0 := by
    rw [hfun]
    exact (hg.mul hh).congr_deriv (by simp)
  rw [taylorCoeff, iteratedDeriv_one, hprod.deriv]
  simp

/-! ## The entire regularized determinant is flat to first order -/

variable {ι : Type*} [DecidableEq ι]

/-- The first Taylor coefficient of the Hilbert--Carleman determinant of a Hilbert--Schmidt kernel
vanishes: it is the limit of the coefficients of the finite blocks, each of which is zero. -/
theorem detCoeff_one_eq_zero {K : ι × ι → ℂ} (hK : IsHS K) : detCoeff K 1 = 0 := by
  have h := tendsto_detCoeff_truncKernel hK 1
  have hzero : ∀ s : Finset ι, detCoeff (truncKernel K s) 1 = 0 := by
    intro s
    rw [detCoeff_truncKernel hK s 1]
    exact taylorCoeff_finiteDet2_one (-(blockMatrix K s))
  simp only [hzero] at h
  exact tendsto_nhds_unique h tendsto_const_nhds

/-- **The Hilbert--Carleman determinant is flat at the origin.** -/
theorem deriv_entireDet2_zero {K : ι × ι → ℂ} (hK : IsHS K) : deriv (entireDet2 K) 0 = 0 := by
  obtain ⟨-, r, hr, -, he⟩ := isRegularizedDet_entireDet2 hK
  have hev : entireDet2 K =ᶠ[nhds (0 : ℂ)] fun z => fredholmDet K z := by
    filter_upwards [isOpen_ball.mem_nhds (show (0 : ℂ) ∈ ball (0 : ℂ) r by simpa using hr)]
      with z hz
    exact he z hz
  rw [hev.deriv_eq]
  have h := detCoeff_one_eq_zero hK
  rw [detCoeff, taylorCoeff, iteratedDeriv_one] at h
  simpa using h

/-! ## The completion and its coordinate -/

/-- **The order-two determinant completion.**  The Hilbert--Carleman determinant of `K` twisted by
the exponential of the linear jet `−cz`; the scalar `c` is the adjoined trace coordinate. -/
noncomputable def completedDet2 (K : ι × ι → ℂ) (c : ℂ) : ℂ → ℂ :=
  fun z => entireDet2 K z * Complex.exp (-(z * c))

theorem differentiable_completedDet2 {K : ι × ι → ℂ} (hK : IsHS K) (c : ℂ) :
    Differentiable ℂ (completedDet2 K c) :=
  (differentiable_entireDet2 hK).mul (Complex.differentiable_exp.comp (by fun_prop))

theorem completedDet2_zero {K : ι × ι → ℂ} (hK : IsHS K) (c : ℂ) : completedDet2 K c 0 = 1 := by
  rw [completedDet2, (isRegularizedDet_entireDet2 hK).eq_one_at_zero]
  simp

/-- **Trace recovery.**  The adjoined coordinate is minus the derivative of the completed
determinant at the origin -- the determinant itself contributes nothing there. -/
theorem deriv_completedDet2_zero {K : ι × ι → ℂ} (hK : IsHS K) (c : ℂ) :
    deriv (completedDet2 K c) 0 = -c := by
  have hD : HasDerivAt (entireDet2 K) 0 0 := by
    have h := ((differentiable_entireDet2 hK).differentiableAt (x := (0 : ℂ))).hasDerivAt
    rwa [deriv_entireDet2_zero hK] at h
  have hi : HasDerivAt (fun z : ℂ => -(z * c)) (-c) 0 :=
    (((hasDerivAt_id (0 : ℂ)).mul_const c).neg).congr_deriv (by ring)
  have hE : HasDerivAt (fun z : ℂ => Complex.exp (-(z * c))) (-c) 0 :=
    hi.cexp.congr_deriv (by simp)
  have h0 : entireDet2 K 0 = 1 := (isRegularizedDet_entireDet2 hK).eq_one_at_zero
  have hprod : HasDerivAt (completedDet2 K c) (-c) 0 :=
    (hD.mul hE).congr_deriv (by rw [h0]; ring)
  exact hprod.deriv

/-- **The completion coordinate is faithful.**  Two completions of Hilbert--Schmidt kernels that
agree as functions have the same adjoined trace coordinate. -/
theorem completedDet2_inj {K₁ K₂ : ι × ι → ℂ} (hK₁ : IsHS K₁) (hK₂ : IsHS K₂) {c₁ c₂ : ℂ}
    (h : completedDet2 K₁ c₁ = completedDet2 K₂ c₂) : c₁ = c₂ := by
  have h1 := deriv_completedDet2_zero hK₁ c₁
  have h2 := deriv_completedDet2_zero hK₂ c₂
  rw [h, h2] at h1
  exact (neg_injective h1.symm)

/-! ## Necessity in the determinant-completion law at Schatten order two -/

/-- **Necessity of the completion law at order two.**  Let the kernels converge in
Hilbert--Schmidt norm and let their completed determinants converge locally uniformly.  Then the
adjoined coordinates converge, to minus the derivative of the limit at the origin, and the limit is
the completed determinant of the limit kernel with that coordinate.

Thus the closure of the graph of the completed determinant is again a graph of completed
determinants: the fibre of the completion is exactly the one adjoined scalar, no more and no
less. -/
theorem tendsto_completionCoefficient
    (K : ℕ → ι × ι → ℂ) (K₀ : ι × ι → ℂ) (hK : ∀ n, IsHS (K n)) (hK₀ : IsHS K₀)
    (hlim : Tendsto (fun n => hsNorm (K n - K₀)) atTop (nhds 0))
    (c : ℕ → ℂ) (F : ℂ → ℂ)
    (hF : TendstoLocallyUniformlyOn (fun n => completedDet2 (K n) (c n)) F atTop Set.univ) :
    Tendsto c atTop (nhds (-deriv F 0)) ∧ F = completedDet2 K₀ (-deriv F 0) := by
  have hdiff : ∀ᶠ n : ℕ in atTop,
      DifferentiableOn ℂ (completedDet2 (K n) (c n)) Set.univ :=
    Eventually.of_forall fun n => (differentiable_completedDet2 (hK n) (c n)).differentiableOn
  have hderiv := hF.deriv hdiff isOpen_univ
  have hat := hderiv.tendsto_at (Set.mem_univ (0 : ℂ))
  have hneg : Tendsto (fun n : ℕ => -(c n)) atTop (nhds (deriv F 0)) := by
    refine hat.congr fun n => ?_
    exact deriv_completedDet2_zero (hK n) (c n)
  have hc : Tendsto c atTop (nhds (-deriv F 0)) := by
    simpa using hneg.neg
  refine ⟨hc, ?_⟩
  funext z
  have h1 := hF.tendsto_at (Set.mem_univ z)
  have h2 := tendsto_entireDet2_of_hsNorm_sub_tendsto_zero K K₀ hK hK₀ hlim z
  have h3 : Tendsto (fun n : ℕ => Complex.exp (-(z * c n))) atTop
      (nhds (Complex.exp (-(z * -deriv F 0)))) :=
    (Complex.continuous_exp.tendsto _).comp (((hc.const_mul z)).neg)
  have h4 : Tendsto (fun n : ℕ => completedDet2 (K n) (c n) z) atTop
      (nhds (completedDet2 K₀ (-deriv F 0) z)) := h2.mul h3
  exact tendsto_nhds_unique h1 h4
