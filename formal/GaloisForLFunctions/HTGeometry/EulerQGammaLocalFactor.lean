import GaloisForLFunctions.HTGeometry.EulerQGammaDirichlet
import GaloisForLFunctions.HTGeometry.QGammaAnalytic

/-!
# The Euler q-Gamma response as a prime product

Jackson's local response splits into three factors,
`Γ_q(1+s) = (1−q)^{-s} · (q;q)_∞ · (q^{1+s};q)_∞⁻¹`, and at `q = p^{-σ}` each of the three has a
convergent prime product: the first is `ζ(σ)^s`, the second is the normalising constant `C_σ`, and
the third is the arithmetic Dirichlet series at the shifted exponent `σ(1+s)`.  Multiplying them
gives the Euler q-Gamma response (EQG.11).
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

set_option maxHeartbeats 1000000

noncomputable section

/-! ## Real powers under the complex power -/

theorem ofReal_rpow_cpow {x : ℝ} (hx : 0 < x) (a : ℝ) (w : ℂ) :
    ((x ^ a : ℝ) : ℂ) ^ w = (x : ℂ) ^ ((a : ℂ) * w) := by
  have hxa : (0 : ℝ) < x ^ a := Real.rpow_pos_of_pos hx a
  have h1 : ((x ^ a : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hxa.ne'
  have h2 : ((x : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hx.ne'
  rw [Complex.cpow_def_of_ne_zero h1, Complex.cpow_def_of_ne_zero h2,
    ← Complex.ofReal_log hxa.le, ← Complex.ofReal_log hx.le, Real.log_rpow hx]
  congr 1
  push_cast
  ring

theorem eqgNome_cpow (σ : EulerSigma) (p : Nat.Primes) (w : ℂ) :
    ((eqgNome σ p).val : ℂ) ^ w = ((p : ℕ) : ℂ) ^ (-((σ.val : ℂ) * w)) := by
  rw [eqgNome_val, eqgQ, ofReal_rpow_cpow (by exact_mod_cast p.2.pos) (-σ.val) w]
  congr 1
  push_cast
  ring

/-! ## The three factors of the local response -/

/-- The shifted Dirichlet exponent `w = σ(1+s)`. -/
def eqgExponent (σ : EulerSigma) (s : ℂ) : ℂ := (σ.val : ℂ) * (1 + s)

/-- **The local response splits into three factors.** -/
theorem qGammaOn_eqgNome_factor (σ : EulerSigma) (p : Nat.Primes) (s : ℂ) :
    qGammaOn (eqgNome σ p) (1 + s)
      = ((1 - eqgQ σ (p : ℕ) : ℝ) : ℂ) ^ (-s)
        * (((realQFactorialInf (eqgNome σ p) : ℝ) : ℂ)
          * (qPochhammerInf (((p : ℕ) : ℂ) ^ (-(eqgExponent σ s)))
              (eqgNome σ p).toEulerNome)⁻¹) := by
  have he1 : (1 : ℂ) - (1 + s) = -s := by ring
  rw [qGammaOn, qDenomProduct_eq, eqgNome_cpow, he1, div_eq_mul_inv, eqgExponent, eqgNome_val]

/-! ## The unit product and the zeta factor -/

theorem summable_eqgQ_primes (σ : EulerSigma) :
    Summable fun p : Nat.Primes => eqgQ σ (p : ℕ) :=
  (summable_eqgQ σ).comp_injective Nat.Primes.coe_nat_injective

theorem abs_log_one_sub_le (σ : EulerSigma) {n : ℕ} (hn : 2 ≤ n) :
    |Real.log (1 - eqgQ σ n)| ≤ 2 * eqgQ σ n := by
  have hq0 : 0 < eqgQ σ n := eqgQ_pos σ (by omega)
  have hqh : eqgQ σ n ≤ 1 / 2 := eqgQ_le_half σ hn
  have hpos : (0 : ℝ) < 1 - eqgQ σ n := by linarith
  have hupper : Real.log (1 - eqgQ σ n) ≤ 0 := Real.log_nonpos hpos.le (by linarith)
  have hlower : -(2 * eqgQ σ n) ≤ Real.log (1 - eqgQ σ n) := by
    rw [Real.le_log_iff_exp_le hpos]
    exact exp_neg_two_mul_le_one_sub hq0.le hqh
  rw [abs_of_nonpos hupper]
  linarith

theorem summable_log_one_sub (σ : EulerSigma) :
    Summable fun p : Nat.Primes => Real.log (1 - eqgQ σ (p : ℕ)) := by
  refine Summable.of_abs ?_
  refine Summable.of_nonneg_of_le (fun p => abs_nonneg _)
    (fun p => abs_log_one_sub_le σ p.2.two_le) ?_
  exact (summable_eqgQ_primes σ).mul_left 2

/-- The prime sum `∑_p log(1 − q_p)`. -/
def eqgLogUnit (σ : EulerSigma) : ℝ := ∑' p : Nat.Primes, Real.log (1 - eqgQ σ (p : ℕ))

theorem hasProd_one_sub (σ : EulerSigma) :
    HasProd (fun p : Nat.Primes => (1 - eqgQ σ (p : ℕ))) (Real.exp (eqgLogUnit σ)) := by
  have h := (summable_log_one_sub σ).hasSum.rexp
  refine h.congr_fun fun p => ?_
  have hpos : (0 : ℝ) < 1 - eqgQ σ (p : ℕ) := by
    have hq0 : 0 < eqgQ σ (p : ℕ) := eqgQ_pos σ p.2.pos
    have hqh : eqgQ σ (p : ℕ) ≤ 1 / 2 := eqgQ_le_half σ p.2.two_le
    linarith
  simp only [Function.comp_apply]
  rw [Real.exp_log hpos]

theorem hasProd_one_sub_complex (σ : EulerSigma) :
    HasProd (fun p : Nat.Primes => ((1 - eqgQ σ (p : ℕ) : ℝ) : ℂ))
      ((Real.exp (eqgLogUnit σ) : ℝ) : ℂ) :=
  (hasProd_one_sub σ).map (Complex.ofRealHom : ℝ →+* ℂ).toMonoidHom Complex.continuous_ofReal

theorem eqgQ_cpow_neg (σ : EulerSigma) (p : Nat.Primes) :
    ((p : ℕ) : ℂ) ^ (-(σ.val : ℂ)) = ((eqgQ σ (p : ℕ) : ℝ) : ℂ) := by
  rw [eqgQ, Complex.ofReal_cpow (Nat.cast_nonneg ((p : ℕ)))]
  push_cast
  ring_nf

/-- The unit prime product is the reciprocal of the zeta value. -/
theorem exp_eqgLogUnit_eq_zeta_inv (σ : EulerSigma) :
    ((Real.exp (eqgLogUnit σ) : ℝ) : ℂ) = (riemannZeta (σ.val : ℂ))⁻¹ := by
  have hre : 1 < ((σ.val : ℂ)).re := by simpa using σ.one_lt
  have hz := riemannZeta_eulerProduct_hasProd hre
  have hzfun : (fun p : Nat.Primes => (1 - ((p : ℕ) : ℂ) ^ (-(σ.val : ℂ)))⁻¹)
      = fun p : Nat.Primes => (((1 - eqgQ σ (p : ℕ) : ℝ) : ℂ))⁻¹ := by
    funext p
    rw [eqgQ_cpow_neg]
    push_cast
    ring_nf
  rw [hzfun] at hz
  have hne : ((Real.exp (eqgLogUnit σ) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact (Real.exp_pos _).ne'
  have hA : Filter.Tendsto (fun t : Finset Nat.Primes =>
      ∏ p ∈ t, ((1 - eqgQ σ (p : ℕ) : ℝ) : ℂ)) atTop
      (nhds ((Real.exp (eqgLogUnit σ) : ℝ) : ℂ)) := hasProd_one_sub_complex σ
  have hAinv := hA.inv₀ hne
  have hAinv' : Filter.Tendsto (fun t : Finset Nat.Primes =>
      ∏ p ∈ t, (((1 - eqgQ σ (p : ℕ) : ℝ) : ℂ))⁻¹) atTop
      (nhds (((Real.exp (eqgLogUnit σ) : ℝ) : ℂ))⁻¹) := by
    refine Filter.Tendsto.congr (fun t => ?_) hAinv
    rw [← Finset.prod_inv_distrib]
  have huniq := tendsto_nhds_unique hAinv' hz
  rw [← huniq, inv_inv]

theorem zeta_eq_exp (σ : EulerSigma) :
    riemannZeta (σ.val : ℂ) = ((Real.exp (-eqgLogUnit σ) : ℝ) : ℂ) := by
  have h := exp_eqgLogUnit_eq_zeta_inv σ
  have hz : riemannZeta (σ.val : ℂ) = (((Real.exp (eqgLogUnit σ) : ℝ) : ℂ))⁻¹ := by
    rw [h, inv_inv]
  rw [hz, Real.exp_neg]
  push_cast
  ring

theorem zeta_cpow (σ : EulerSigma) (s : ℂ) :
    riemannZeta (σ.val : ℂ) ^ s = Complex.exp ((eqgLogUnit σ : ℂ) * (-s)) := by
  have hne : ((Real.exp (-eqgLogUnit σ) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact (Real.exp_pos _).ne'
  rw [zeta_eq_exp, Complex.cpow_def_of_ne_zero hne,
    ← Complex.ofReal_log (Real.exp_pos _).le, Real.log_exp]
  congr 1
  push_cast
  ring

/-- **The first prime product**: the unit factors multiply to `ζ(σ)^s`. -/
theorem hasProd_one_sub_cpow (σ : EulerSigma) (s : ℂ) :
    HasProd (fun p : Nat.Primes => ((1 - eqgQ σ (p : ℕ) : ℝ) : ℂ) ^ (-s))
      (riemannZeta (σ.val : ℂ) ^ s) := by
  have hsum : HasSum
      (fun p : Nat.Primes => ((Real.log (1 - eqgQ σ (p : ℕ)) : ℝ) : ℂ) * (-s))
      ((eqgLogUnit σ : ℂ) * (-s)) := by
    have hreal := (summable_log_one_sub σ).hasSum
    have hmap := hreal.map (Complex.ofRealHom : ℝ →+* ℂ) Complex.continuous_ofReal
    have := hmap.mul_right (-s)
    refine this.congr_fun fun p => ?_
    rfl
  have hexp := hsum.cexp
  rw [zeta_cpow]
  refine hexp.congr_fun fun p => ?_
  have hpos : (0 : ℝ) < 1 - eqgQ σ (p : ℕ) := by
    have hq0 : 0 < eqgQ σ (p : ℕ) := eqgQ_pos σ p.2.pos
    have hqh : eqgQ σ (p : ℕ) ≤ 1 / 2 := eqgQ_le_half σ p.2.two_le
    linarith
  have hne : ((1 - eqgQ σ (p : ℕ) : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact hpos.ne'
  simp only [Function.comp_apply]
  rw [Complex.cpow_def_of_ne_zero hne, ← Complex.ofReal_log hpos.le]

/-! ## The Euler q-Gamma response -/

/-- **Theorem 4.1, equation (EQG.11).**  The prime product of the local q-Gamma responses converges
to `ζ(σ)^s · C_σ · D_σ(s)`, where `D_σ(s)` is the arithmetic Dirichlet series at the shifted
exponent `σ(1+s)`. -/
theorem eqgResponse_hasProd (σ : EulerSigma) {s : ℂ} (hs : 1 < (eqgExponent σ s).re) :
    HasProd (fun p : Nat.Primes => qGammaOn (eqgNome σ p) (1 + s))
      (riemannZeta (σ.val : ℂ) ^ s
        * (((eqgConst σ : ℝ) : ℂ) * ∑' m : ℕ, eqgTerm σ (eqgExponent σ s) m)) := by
  have h1 := hasProd_one_sub_cpow σ s
  have h2 : HasProd (fun p : Nat.Primes => ((realQFactorialInf (eqgNome σ p) : ℝ) : ℂ))
      ((eqgConst σ : ℝ) : ℂ) :=
    (eqgConst_hasProd σ).map (Complex.ofRealHom : ℝ →+* ℂ).toMonoidHom Complex.continuous_ofReal
  have h3 := eqgDirichlet_eulerProduct σ hs
  have h := h1.mul (h2.mul h3)
  refine h.congr_fun fun p => ?_
  exact qGammaOn_eqgNome_factor σ p s

/-! ## The probabilistic reading -/

/-- **Equations (EQG.8) and (EQG.9).**  The shifted arithmetic term is the unnormalised law times
the observable factor `m^{-σs}`: the exponential response of `X_σ = log ζ(σ) − σ log M`. -/
theorem eqgTerm_eqgExponent (σ : EulerSigma) (s : ℂ) (m : ℕ) :
    eqgTerm σ (eqgExponent σ s) m
      = ((eqgWeight σ m : ℝ) : ℂ) * ((m : ℂ) ^ (-((σ.val : ℂ) * s))) := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [eqgTerm_zero, eqgWeight_zero]
    simp
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
  have hmC : ((m : ℕ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Nat.cast_eq_zero]
    exact hm
  have hnum : (((m : ℝ) ^ (-σ.val) : ℝ) : ℂ) = ((m : ℕ) : ℂ) ^ (-(σ.val : ℂ)) := by
    rw [Complex.ofReal_cpow (Nat.cast_nonneg m)]
    push_cast
    ring_nf
  have hsplit : -(eqgExponent σ s) = -(σ.val : ℂ) + -((σ.val : ℂ) * s) := by
    rw [eqgExponent]
    ring
  have hden : ((eqgDenom σ m : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact (eqgDenom_pos σ m).ne'
  rw [eqgTerm, if_neg hm, eqgWeight, if_neg hm, hsplit,
    Complex.cpow_add _ _ hmC, Complex.ofReal_div, hnum]
  field_simp

/-- **Equation (EQG.12).**  The Dirichlet series of the shifted weight is the response transform of
the random-integer law. -/
theorem eqgDirichlet_eq_lawTransform (σ : EulerSigma) (s : ℂ) :
    ∑' m : ℕ, eqgTerm σ (eqgExponent σ s) m
      = ∑' m : ℕ, ((eqgWeight σ m : ℝ) : ℂ) * ((m : ℂ) ^ (-((σ.val : ℂ) * s))) :=
  tsum_congr fun m => eqgTerm_eqgExponent σ s m

end

end GaloisForLFunctions.HTGeometry
