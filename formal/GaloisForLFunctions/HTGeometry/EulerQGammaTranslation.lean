import GaloisForLFunctions.HTGeometry.EulerQGammaLocalFactor

/-!
# The source-normal translation law of the Euler q-Gamma response

Jackson's q-Pochhammer shift `(a;q)_∞ = (1−a)(aq;q)_∞`, read at `a = p^{-w}` and `q = p^{-σ}`,
factors the local Euler factor of the arithmetic Dirichlet series as
`(p^{-w};q_p)_∞⁻¹ = (1−p^{-w})⁻¹ · (p^{-(w+σ)};q_p)_∞⁻¹`.  Multiplying over the primes turns the
first factor into `ζ(w)`, so the Dirichlet series satisfies `D(w) = ζ(w)·D(w+σ)`.  This is the
whole translation law: the response satisfies `F_σ(s+1) = ζ(σ)/ζ(σ(1+s)) · F_σ(s)`, and it is
already normalised, `F_σ(0) = F_σ(1) = 1`.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

set_option maxHeartbeats 1000000

noncomputable section

/-! ## The Dirichlet series and its shift -/

/-- The arithmetic Dirichlet series `D_σ(w) = ∑_m m^{-w}/∏_p (q_p;q_p)_{v_p(m)}`. -/
def eqgDirichlet (σ : EulerSigma) (w : ℂ) : ℂ := ∑' m : ℕ, eqgTerm σ w m

theorem eqgLocalFactor_shift (σ : EulerSigma) (w : ℂ) (p : Nat.Primes) :
    (qPochhammerInf (((p : ℕ) : ℂ) ^ (-w)) (eqgNome σ p).toEulerNome)⁻¹
      = (1 - ((p : ℕ) : ℂ) ^ (-w))⁻¹
        * (qPochhammerInf (((p : ℕ) : ℂ) ^ (-(w + (σ.val : ℂ)))) (eqgNome σ p).toEulerNome)⁻¹ := by
  have hpC : ((p : ℕ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact p.2.pos.ne'
  have hstep : ((p : ℕ) : ℂ) ^ (-w) * (((eqgNome σ p).toEulerNome : EulerNome) : ℂ)
      = ((p : ℕ) : ℂ) ^ (-(w + (σ.val : ℂ))) := by
    rw [RealEulerNome.toEulerNome_coe, eqgNome_val, ← eqgQ_cpow_neg,
      ← Complex.cpow_add _ _ hpC]
    congr 1
    ring
  rw [qPochhammerInf_shift, hstep, mul_inv]

/-- **The Dirichlet shift law** `D_σ(w) = ζ(w)·D_σ(w+σ)`. -/
theorem eqgDirichlet_shift (σ : EulerSigma) {w : ℂ} (hw : 1 < w.re) :
    eqgDirichlet σ w = riemannZeta w * eqgDirichlet σ (w + (σ.val : ℂ)) := by
  have hwσ : 1 < (w + (σ.val : ℂ)).re := by
    have : (w + (σ.val : ℂ)).re = w.re + σ.val := by simp
    rw [this]
    linarith [σ.pos]
  have h1 : Filter.Tendsto (fun t : Finset Nat.Primes =>
      ∏ p ∈ t, (qPochhammerInf (((p : ℕ) : ℂ) ^ (-w)) (eqgNome σ p).toEulerNome)⁻¹) atTop
      (nhds (eqgDirichlet σ w)) := eqgDirichlet_eulerProduct σ hw
  have h2 := (riemannZeta_eulerProduct_hasProd hw).mul (eqgDirichlet_eulerProduct σ hwσ)
  have h2' : Filter.Tendsto (fun t : Finset Nat.Primes =>
      ∏ p ∈ t, (qPochhammerInf (((p : ℕ) : ℂ) ^ (-w)) (eqgNome σ p).toEulerNome)⁻¹) atTop
      (nhds (riemannZeta w * eqgDirichlet σ (w + (σ.val : ℂ)))) := by
    refine Filter.Tendsto.congr (fun t => ?_) h2
    refine Finset.prod_congr rfl fun p _ => ?_
    exact (eqgLocalFactor_shift σ w p).symm
  exact tendsto_nhds_unique h1 h2'

/-! ## The response and its translation law -/

/-- **Equation (EQG.9).**  The Euler q-Gamma response. -/
def eqgResponse (σ : EulerSigma) (s : ℂ) : ℂ :=
  riemannZeta (σ.val : ℂ) ^ s * (((eqgConst σ : ℝ) : ℂ) * eqgDirichlet σ (eqgExponent σ s))

theorem eqgResponse_hasProd' (σ : EulerSigma) {s : ℂ} (hs : 1 < (eqgExponent σ s).re) :
    HasProd (fun p : Nat.Primes => qGammaOn (eqgNome σ p) (1 + s)) (eqgResponse σ s) :=
  eqgResponse_hasProd σ hs

theorem eqgExponent_succ (σ : EulerSigma) (s : ℂ) :
    eqgExponent σ (s + 1) = eqgExponent σ s + (σ.val : ℂ) := by
  rw [eqgExponent, eqgExponent]
  ring

theorem zeta_sigma_ne_zero (σ : EulerSigma) : riemannZeta (σ.val : ℂ) ≠ 0 := by
  refine riemannZeta_ne_zero_of_one_lt_re ?_
  simpa using σ.one_lt

/-- **Theorem 5.1, equation (EQG.13).**  The source-normal translation law. -/
theorem eqgResponse_translation (σ : EulerSigma) {s : ℂ} (hs : 1 < (eqgExponent σ s).re) :
    eqgResponse σ (s + 1)
      = riemannZeta (σ.val : ℂ) / riemannZeta (eqgExponent σ s) * eqgResponse σ s := by
  have hzw : riemannZeta (eqgExponent σ s) ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  have hshift := eqgDirichlet_shift σ hs
  rw [eqgResponse, eqgResponse, eqgExponent_succ,
    Complex.cpow_add _ _ (zeta_sigma_ne_zero σ), Complex.cpow_one, hshift]
  field_simp

/-! ## Normalisation -/

theorem eqgTerm_sigma (σ : EulerSigma) (m : ℕ) :
    eqgTerm σ (σ.val : ℂ) m = ((eqgWeight σ m : ℝ) : ℂ) := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [eqgTerm_zero, eqgWeight_zero, Complex.ofReal_zero]
  have hnum : (((m : ℝ) ^ (-σ.val) : ℝ) : ℂ) = ((m : ℕ) : ℂ) ^ (-(σ.val : ℂ)) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg m)]
    push_cast
    ring_nf
  rw [eqgTerm, if_neg hm, eqgWeight, if_neg hm, Complex.ofReal_div, hnum]

theorem eqgDirichlet_sigma (σ : EulerSigma) :
    eqgDirichlet σ (σ.val : ℂ) = ((eqgTotal σ : ℝ) : ℂ) := by
  rw [eqgDirichlet]
  have hmap := (summable_eqgWeight σ).hasSum.map (Complex.ofRealHom : ℝ →+* ℂ)
    Complex.continuous_ofReal
  have hfun : (fun m : ℕ => eqgTerm σ (σ.val : ℂ) m)
      = fun m : ℕ => ((eqgWeight σ m : ℝ) : ℂ) := by
    funext m
    exact eqgTerm_sigma σ m
  rw [hfun]
  refine HasSum.tsum_eq ?_
  refine hmap.congr_fun fun m => ?_
  rfl

/-- **Equation (EQG.14), first half.**  The response is already normalised at the source. -/
theorem eqgResponse_zero (σ : EulerSigma) : eqgResponse σ 0 = 1 := by
  have he : eqgExponent σ 0 = (σ.val : ℂ) := by
    rw [eqgExponent]
    ring
  rw [eqgResponse, he, eqgDirichlet_sigma, Complex.cpow_zero, one_mul, ← Complex.ofReal_mul]
  have hval : eqgConst σ * eqgTotal σ = 1 := inv_mul_cancel₀ (eqgTotal_pos σ).ne'
  rw [hval, Complex.ofReal_one]

/-- **Equation (EQG.14), second half.**  The unit translate is normalised too. -/
theorem eqgResponse_one (σ : EulerSigma) : eqgResponse σ 1 = 1 := by
  have he : eqgExponent σ 0 = (σ.val : ℂ) := by
    rw [eqgExponent]
    ring
  have hs : 1 < (eqgExponent σ 0).re := by
    rw [he]
    simpa using σ.one_lt
  have htr := eqgResponse_translation σ hs
  rw [zero_add] at htr
  rw [htr, he, eqgResponse_zero, mul_one, div_self (zeta_sigma_ne_zero σ)]

/-! ## The exponential intervention is already normalised -/

theorem summable_eqgTerm (σ : EulerSigma) {w : ℂ} (hw : 1 < w.re) : Summable (eqgTerm σ w) :=
  Summable.of_norm (summable_norm_eqgTerm σ hw)

theorem eqgExponent_one (σ : EulerSigma) : eqgExponent σ 1 = 2 * (σ.val : ℂ) := by
  rw [eqgExponent]
  ring

theorem eqgTiltTerm (σ : EulerSigma) (m : ℕ) :
    ((eqgMass σ m : ℝ) : ℂ) * (riemannZeta (σ.val : ℂ) * ((m : ℂ) ^ (-(σ.val : ℂ))))
      = riemannZeta (σ.val : ℂ) * (((eqgConst σ : ℝ) : ℂ) * eqgTerm σ (eqgExponent σ 1) m) := by
  have hmul : -((σ.val : ℂ) * 1) = -(σ.val : ℂ) := by ring
  rw [eqgMass, eqgTerm_eqgExponent, hmul, Complex.ofReal_mul]
  ring

/-- **Equation (EQG.15).**  The exponential intervention `e^{X_σ} = ζ(σ)·M^{-σ}` is already a
probability density: no fitted scalar correction is needed. -/
theorem eqgTilt_hasSum_one (σ : EulerSigma) :
    HasSum (fun m : ℕ => ((eqgMass σ m : ℝ) : ℂ)
      * (riemannZeta (σ.val : ℂ) * ((m : ℂ) ^ (-(σ.val : ℂ))))) 1 := by
  have he : eqgExponent σ 1 = 2 * (σ.val : ℂ) := eqgExponent_one σ
  have hre : 1 < (eqgExponent σ 1).re := by
    rw [he]
    have hval : ((2 : ℂ) * (σ.val : ℂ)).re = 2 * σ.val := by simp
    rw [hval]
    linarith [σ.one_lt]
  have hsum : HasSum (eqgTerm σ (eqgExponent σ 1)) (eqgDirichlet σ (eqgExponent σ 1)) :=
    (summable_eqgTerm σ hre).hasSum
  have h2 := (hsum.mul_left (((eqgConst σ : ℝ) : ℂ))).mul_left (riemannZeta (σ.val : ℂ))
  have hval : riemannZeta (σ.val : ℂ)
      * (((eqgConst σ : ℝ) : ℂ) * eqgDirichlet σ (eqgExponent σ 1)) = 1 := by
    have h := eqgResponse_one σ
    rw [eqgResponse, Complex.cpow_one] at h
    exact h
  rw [hval] at h2
  refine h2.congr_fun fun m => ?_
  exact eqgTiltTerm σ m

end

end GaloisForLFunctions.HTGeometry
