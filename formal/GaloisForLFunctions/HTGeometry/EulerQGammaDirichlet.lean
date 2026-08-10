import GaloisForLFunctions.HTGeometry.EulerQGammaGlobalLaw
import GaloisForLFunctions.HTGeometry.QBinomialTheorem

/-!
# The Dirichlet form of the Euler q-Gamma response

Shifting the exponent of the arithmetic weight from `σ` to a complex `w` keeps it multiplicative,
and its local Euler factor becomes the q-binomial series at `a = p^{-w}` with nome `q_p = p^{-σ}`.
By the complex q-binomial theorem that series is `(p^{-w}; q_p)_∞⁻¹`, so the global Dirichlet
series of the arithmetic weight is the prime product of the reciprocal q-Pochhammer symbols — the
core of the Euler q-Gamma response (EQG.11)/(EQG.12).
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

set_option maxHeartbeats 1000000

noncomputable section

/-! ## The arithmetic weight at a real exponent -/

/-- The arithmetic weight with numerator exponent `x` and nomes taken from `σ`. -/
def eqgWeightRe (σ : EulerSigma) (x : ℝ) (m : ℕ) : ℝ :=
  if m = 0 then 0 else (m : ℝ) ^ (-x) / eqgDenom σ m

@[simp] theorem eqgWeightRe_zero (σ : EulerSigma) (x : ℝ) : eqgWeightRe σ x 0 = 0 := if_pos rfl

theorem eqgWeightRe_nonneg (σ : EulerSigma) (x : ℝ) (m : ℕ) : 0 ≤ eqgWeightRe σ x m := by
  rw [eqgWeightRe]
  split
  · exact le_rfl
  · exact div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg m) _) (eqgDenom_pos σ m).le

theorem eqgWeightRe_le (σ : EulerSigma) (x : ℝ) (m : ℕ) :
    eqgWeightRe σ x m ≤ Real.exp (4 * eqgTail σ) * (m : ℝ) ^ (-x) := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [eqgWeightRe_zero]
    exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (by norm_num) _)
  rw [eqgWeightRe, if_neg hm]
  have hlow := eqgDenom_lower σ m
  have hpos := eqgDenom_pos σ m
  rw [div_le_iff₀ hpos]
  have hq : (0 : ℝ) ≤ (m : ℝ) ^ (-x) := Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hexp : Real.exp (4 * eqgTail σ) * Real.exp (-(4 * eqgTail σ)) = 1 := by
    rw [← Real.exp_add]
    simp
  calc (m : ℝ) ^ (-x)
      = (m : ℝ) ^ (-x) * (Real.exp (4 * eqgTail σ) * Real.exp (-(4 * eqgTail σ))) := by
        rw [hexp, mul_one]
    _ ≤ (m : ℝ) ^ (-x) * (Real.exp (4 * eqgTail σ) * eqgDenom σ m) := by
        refine mul_le_mul_of_nonneg_left ?_ hq
        exact mul_le_mul_of_nonneg_left hlow (Real.exp_pos _).le
    _ = Real.exp (4 * eqgTail σ) * (m : ℝ) ^ (-x) * eqgDenom σ m := by ring

theorem summable_eqgWeightRe (σ : EulerSigma) {x : ℝ} (hx : 1 < x) :
    Summable (eqgWeightRe σ x) := by
  refine Summable.of_nonneg_of_le (eqgWeightRe_nonneg σ x) (eqgWeightRe_le σ x) ?_
  refine Summable.mul_left _ ?_
  have h : Summable fun n : ℕ => (((n : ℝ)) ^ x)⁻¹ := Real.summable_nat_rpow_inv.mpr hx
  refine h.congr fun n => ?_
  rw [Real.rpow_neg (Nat.cast_nonneg n)]

/-! ## The complex arithmetic weight -/

/-- The arithmetic weight at a complex exponent `w`, with nomes taken from `σ`. -/
def eqgTerm (σ : EulerSigma) (w : ℂ) (m : ℕ) : ℂ :=
  if m = 0 then 0 else (m : ℂ) ^ (-w) / ((eqgDenom σ m : ℝ) : ℂ)

@[simp] theorem eqgTerm_zero (σ : EulerSigma) (w : ℂ) : eqgTerm σ w 0 = 0 := if_pos rfl

@[simp] theorem eqgTerm_one (σ : EulerSigma) (w : ℂ) : eqgTerm σ w 1 = 1 := by
  rw [eqgTerm, if_neg one_ne_zero, eqgDenom_one, Nat.cast_one, Complex.one_cpow]
  norm_num

theorem norm_eqgTerm (σ : EulerSigma) (w : ℂ) (m : ℕ) :
    ‖eqgTerm σ w m‖ = eqgWeightRe σ w.re m := by
  rcases eq_or_ne m 0 with rfl | hm
  · rw [eqgTerm_zero, eqgWeightRe_zero, norm_zero]
  rw [eqgTerm, if_neg hm, eqgWeightRe, if_neg hm, norm_div,
    Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hm), Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (eqgDenom_pos σ m), Complex.neg_re]

theorem summable_norm_eqgTerm (σ : EulerSigma) {w : ℂ} (hw : 1 < w.re) :
    Summable fun m : ℕ => ‖eqgTerm σ w m‖ := by
  refine (summable_eqgWeightRe σ hw).congr fun m => ?_
  rw [norm_eqgTerm]

theorem eqgTerm_mul (σ : EulerSigma) (w : ℂ) {a b : ℕ} (hab : Nat.Coprime a b) :
    eqgTerm σ w (a * b) = eqgTerm σ w a * eqgTerm σ w b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  have hab0 : a * b ≠ 0 := mul_ne_zero ha hb
  have hcast : ((a * b : ℕ) : ℂ) ^ (-w) = (a : ℂ) ^ (-w) * (b : ℂ) ^ (-w) := by
    have h := Complex.mul_cpow_ofReal_nonneg (a := (a : ℝ)) (b := (b : ℝ))
      (Nat.cast_nonneg a) (Nat.cast_nonneg b) (-w)
    simpa using h
  rw [eqgTerm, eqgTerm, eqgTerm, if_neg hab0, if_neg ha, if_neg hb,
    eqgDenom_mul σ ha hb hab, hcast, Complex.ofReal_mul]
  have hda : ((eqgDenom σ a : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact (eqgDenom_pos σ a).ne'
  have hdb : ((eqgDenom σ b : ℝ) : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]
    exact (eqgDenom_pos σ b).ne'
  field_simp

theorem eqgTerm_prime_pow (σ : EulerSigma) (w : ℂ) (p : Nat.Primes) (e : ℕ) :
    eqgTerm σ w ((p : ℕ) ^ e) = qBinomialTerm (eqgNome σ p) ((p : ℂ) ^ (-w)) e := by
  rcases Nat.eq_zero_or_pos e with rfl | he
  · rw [pow_zero, eqgTerm_one, qBinomialTerm_zero]
  have hne : ((p : ℕ)) ^ e ≠ 0 := pow_ne_zero _ p.2.pos.ne'
  rw [eqgTerm, if_neg hne, qBinomialTerm, eqgDenom,
    Nat.primeFactors_prime_pow he.ne' p.2, Finset.prod_singleton, p.2.factorization_pow]
  simp only [Finsupp.single_eq_same]
  rw [eqgLocalFactorial_eq]
  congr 1
  rw [Nat.cast_pow, ← Complex.natCast_cpow_natCast_mul, Complex.cpow_nat_mul]

/-! ## The Euler product -/

theorem norm_natCast_cpow_lt_one {w : ℂ} (hw : 0 < w.re) (p : Nat.Primes) :
    ‖((p : ℕ) : ℂ) ^ (-w)‖ < 1 := by
  rw [Complex.norm_natCast_cpow_of_pos p.2.pos, Complex.neg_re]
  refine Real.rpow_lt_one_of_one_lt_of_neg ?_ (by linarith)
  exact_mod_cast p.2.one_lt

/-- The local Euler factor of the arithmetic weight is the reciprocal q-Pochhammer symbol. -/
theorem eqgTerm_local_hasSum (σ : EulerSigma) {w : ℂ} (hw : 0 < w.re) (p : Nat.Primes) :
    HasSum (fun e : ℕ => eqgTerm σ w ((p : ℕ) ^ e))
      (qPochhammerInf (((p : ℕ) : ℂ) ^ (-w)) (eqgNome σ p).toEulerNome)⁻¹ := by
  have hf : (fun e : ℕ => eqgTerm σ w ((p : ℕ) ^ e))
      = qBinomialTerm (eqgNome σ p) (((p : ℕ) : ℂ) ^ (-w)) := by
    funext e
    exact eqgTerm_prime_pow σ w p e
  rw [hf]
  exact qBinomial_hasSum (eqgNome σ p) (norm_natCast_cpow_lt_one hw p)

/-- **The Euler product of the arithmetic Dirichlet series.**  For `Re w > 1`,
`∑_m m^{-w}/∏_p (q_p;q_p)_{v_p(m)} = ∏_p (p^{-w}; q_p)_∞⁻¹`. -/
theorem eqgDirichlet_eulerProduct (σ : EulerSigma) {w : ℂ} (hw : 1 < w.re) :
    HasProd (fun p : Nat.Primes =>
        (qPochhammerInf (((p : ℕ) : ℂ) ^ (-w)) (eqgNome σ p).toEulerNome)⁻¹)
      (∑' m : ℕ, eqgTerm σ w m) := by
  have hw0 : 0 < w.re := lt_trans zero_lt_one hw
  have hbase := EulerProduct.eulerProduct_hasProd (f := eqgTerm σ w) (eqgTerm_one σ w)
    (fun {m n} h => eqgTerm_mul σ w h) (summable_norm_eqgTerm σ hw) (eqgTerm_zero σ w)
  have hfun : (fun p : Nat.Primes => ∑' e : ℕ, eqgTerm σ w ((p : ℕ) ^ e))
      = fun p : Nat.Primes =>
        (qPochhammerInf (((p : ℕ) : ℂ) ^ (-w)) (eqgNome σ p).toEulerNome)⁻¹ := by
    funext p
    exact (eqgTerm_local_hasSum σ hw0 p).tsum_eq
  rw [hfun] at hbase
  exact hbase

end

end GaloisForLFunctions.HTGeometry
