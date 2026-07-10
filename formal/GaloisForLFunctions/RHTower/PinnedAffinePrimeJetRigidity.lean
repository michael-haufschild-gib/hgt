import GaloisForLFunctions.RHTower.PinnedAffineConstantSourceBlindness

/-!
# Prime first jets retain labels in the pinned-affine quotient

Constant sources collapse in the one-slot quotient to a single scalar sum.  The first possible
label-sensitive refinement is the first germ jet.  At a point `rho`, the truncated prime germ is

`J_p(rho;X) = p^(-rho) * (1 - log(p) X) mod X^2`.

This file proves that for two distinct positive bases, `J_p` and `J_q` are linearly independent in
the order-two pinned-affine defect quotient at every complex point.  The descended Fitting boundary
recovers both polynomial coefficients.  Their two equations form a Vandermonde system in
`log p, log q`; nonvanishing of the prime amplitudes and injectivity of the real logarithm force both
source coefficients to vanish.

Unlike raw prime evaluation, this statement retains the prime labels.  Unlike susceptibility or
pointwise-tuned cancellation, it holds uniformly for every `rho` and does not encode a target zero
location.  It is the first nonconstant source rigidity surviving the pinned-affine quotient.  The
general finite-prime/order-`k` Vandermonde jet and the completed infinite-support attachment remain
the next mathematical steps.
-/

noncomputable section
namespace RHTower

open Matrix Polynomial Complex
open scoped BigOperators

/-- A general polynomial source in the canonical one-slot torsion presentation. -/
def oneSlotPolynomialDefect (R : Type*) [CommRing R] (P : Polynomial R) :
    Matrix (Fin 1) (Fin 1) (Polynomial R) :=
  Matrix.of ![![P]]

/-- The Fitting boundary of a one-slot polynomial source is exactly its local divisor jet. -/
theorem fittingBoundaryClass_oneSlotPolynomial_eq
    (R : Type*) [CommRing R] (m : ℕ) (P : Polynomial R) :
    fittingBoundaryClass m (oneSlotTorsionPresentation R m) (oneSlotPolynomialDefect R P) =
      jetClass R m P := by
  simp [fittingBoundaryClass, fittingBoundaryTrace, oneSlotTorsionPresentation,
    oneSlotPolynomialDefect, Matrix.adjugate_fin_one, Matrix.trace_fin_one]

/-- The constant and first-order Taylor terms of the prime exponential germ at `rho`. -/
def primeFirstJet (p : ℕ) (rho : ℂ) : Polynomial ℂ :=
  Polynomial.C ((p : ℂ) ^ (-rho)) +
    Polynomial.C (-((Real.log p : ℂ) * (p : ℂ) ^ (-rho))) * X

@[simp]
theorem primeFirstJet_coeff_zero (p : ℕ) (rho : ℂ) :
    (primeFirstJet p rho).coeff 0 = (p : ℂ) ^ (-rho) := by
  simp [primeFirstJet]

@[simp]
theorem primeFirstJet_coeff_one (p : ℕ) (rho : ℂ) :
    (primeFirstJet p rho).coeff 1 = -((Real.log p : ℂ) * (p : ℂ) ^ (-rho)) := by
  simp [primeFirstJet]

/-- A linear combination of two prime first jets, read in the order-two quotient. -/
def twoPrimeFirstJetPinnedAffineClass (p q : ℕ) (a b rho : ℂ) :
    PinnedAffineDefectQuotient 2 (oneSlotTorsionPresentation ℂ 2) :=
  QuotientAddGroup.mk
    (oneSlotPolynomialDefect ℂ (a • primeFirstJet p rho + b • primeFirstJet q rho))

/-- **Two-prime first-jet rigidity.**  Distinct positive prime labels give linearly independent
classes in the order-two pinned-affine quotient at every point. -/
theorem twoPrimeFirstJetPinnedAffineClass_eq_zero_iff
    {p q : ℕ} (hp : 0 < p) (hq : 0 < q) (hpq : p ≠ q) (a b rho : ℂ) :
    twoPrimeFirstJetPinnedAffineClass p q a b rho = 0 ↔ a = 0 ∧ b = 0 := by
  constructor
  · intro hzero
    have hboundary := congrArg
      (fun z => pinnedAffineBoundaryHom 2 (oneSlotTorsionPresentation ℂ 2)
        (oneSlotTorsionPresentation_det ℂ 2) z) hzero
    have hjet : jetClass ℂ 2 (a • primeFirstJet p rho + b • primeFirstJet q rho) = 0 := by
      simpa [twoPrimeFirstJetPinnedAffineClass,
        fittingBoundaryClass_oneSlotPolynomial_eq] using hboundary
    have hall := (jetClass_eq_zero_iff_coeff_lt_eq_zero ℂ 2).mp hjet
    have h0 := hall 0 (by omega)
    have h1 := hall 1 (by omega)
    simp only [Polynomial.coeff_add, Polynomial.coeff_smul, primeFirstJet_coeff_zero] at h0
    simp only [Polynomial.coeff_add, Polynomial.coeff_smul, primeFirstJet_coeff_one] at h1
    change a * (p : ℂ) ^ (-rho) + b * (q : ℂ) ^ (-rho) = 0 at h0
    change a * -((Real.log p : ℂ) * (p : ℂ) ^ (-rho)) +
      b * -((Real.log q : ℂ) * (q : ℂ) ^ (-rho)) = 0 at h1
    have hpv : (p : ℂ) ^ (-rho) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hp.ne'))
    have hqv : (q : ℂ) ^ (-rho) ≠ 0 :=
      Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hq.ne'))
    have hlogR : Real.log p ≠ Real.log q := by
      intro hlog
      have hpR : (0 : ℝ) < p := by exact_mod_cast hp
      have hqR : (0 : ℝ) < q := by exact_mod_cast hq
      have hpqR := Real.log_injOn_pos hpR hqR hlog
      exact hpq (by exact_mod_cast hpqR)
    have hlogC : (Real.log p : ℂ) ≠ (Real.log q : ℂ) := by
      exact_mod_cast hlogR
    have haProduct : a * (((Real.log q : ℂ) - Real.log p) * (p : ℂ) ^ (-rho)) = 0 := by
      linear_combination h1 + (Real.log q : ℂ) * h0
    have hfactor : ((Real.log q : ℂ) - Real.log p) * (p : ℂ) ^ (-rho) ≠ 0 :=
      mul_ne_zero (sub_ne_zero.mpr hlogC.symm) hpv
    have ha : a = 0 := (mul_eq_zero.mp haProduct).resolve_right hfactor
    rw [ha, zero_mul, zero_add] at h0
    have hb : b = 0 := (mul_eq_zero.mp h0).resolve_right hqv
    exact ⟨ha, hb⟩
  · rintro ⟨rfl, rfl⟩
    rw [twoPrimeFirstJetPinnedAffineClass, QuotientAddGroup.eq_zero_iff]
    refine ⟨0, 0, 0, 0, 0, ?_⟩
    ext i j
    fin_cases i
    fin_cases j
    simp [oneSlotPolynomialDefect, pinnedAffineWeldDefect, commutatorDefect]

/-- Prime specialization: two distinct prime labels remain independent at every point. -/
theorem twoPrimeFirstJetPinnedAffineClass_prime_eq_zero_iff
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (a b rho : ℂ) :
    twoPrimeFirstJetPinnedAffineClass p q a b rho = 0 ↔ a = 0 ∧ b = 0 :=
  twoPrimeFirstJetPinnedAffineClass_eq_zero_iff hp.pos hq.pos hpq a b rho

/-! ## Arbitrary finite prime support -/

/-- The first `k` derivative coefficients of the prime exponential germ.  Factorials are omitted:
the resulting diagonal rescaling does not affect Vandermonde independence. -/
def primeDerivativeJet (k p : ℕ) (rho : ℂ) : Polynomial ℂ :=
  ∑ j : Fin k,
    Polynomial.monomial (j : ℕ)
      ((p : ℂ) ^ (-rho) * (-(Real.log p : ℂ)) ^ (j : ℕ))

@[simp]
theorem primeDerivativeJet_coeff (k p : ℕ) (rho : ℂ) (j : Fin k) :
    (primeDerivativeJet k p rho).coeff (j : ℕ) =
      (p : ℂ) ^ (-rho) * (-(Real.log p : ℂ)) ^ (j : ℕ) := by
  classical
  simp [primeDerivativeJet, Polynomial.coeff_monomial, ← Fin.ext_iff]

/-- A finite linear combination of `k` prime derivative jets. -/
def finitePrimeDerivativeJetPolynomial {k : ℕ}
    (p : Fin k → ℕ) (a : Fin k → ℂ) (rho : ℂ) : Polynomial ℂ :=
  ∑ r : Fin k, a r • primeDerivativeJet k (p r) rho

@[simp]
theorem finitePrimeDerivativeJetPolynomial_coeff {k : ℕ}
    (p : Fin k → ℕ) (a : Fin k → ℂ) (rho : ℂ) (j : Fin k) :
    (finitePrimeDerivativeJetPolynomial p a rho).coeff (j : ℕ) =
      ∑ r : Fin k,
        a r * ((p r : ℕ) : ℂ) ^ (-rho) * (-(Real.log (p r) : ℂ)) ^ (j : ℕ) := by
  classical
  simp [finitePrimeDerivativeJetPolynomial, mul_assoc]

/-- The finite derivative-jet source class in the order-`k` pinned-affine quotient. -/
def finitePrimeDerivativeJetPinnedAffineClass {k : ℕ}
    (p : Fin k → ℕ) (a : Fin k → ℂ) (rho : ℂ) :
    PinnedAffineDefectQuotient k (oneSlotTorsionPresentation ℂ k) :=
  QuotientAddGroup.mk
    (oneSlotPolynomialDefect ℂ (finitePrimeDerivativeJetPolynomial p a rho))

/-- **Finite-prime jet Vandermonde rigidity.**  For any injective family of positive bases, the
first `k` derivative jets are independent in the order-`k` pinned-affine quotient at every complex
point. -/
theorem finitePrimeDerivativeJetPinnedAffineClass_eq_zero_iff {k : ℕ}
    (p : Fin k → ℕ) (hp : ∀ i, 0 < p i) (hpinj : Function.Injective p)
    (a : Fin k → ℂ) (rho : ℂ) :
    finitePrimeDerivativeJetPinnedAffineClass p a rho = 0 ↔ a = 0 := by
  classical
  constructor
  · intro hzero
    have hboundary := congrArg
      (fun z => pinnedAffineBoundaryHom k (oneSlotTorsionPresentation ℂ k)
        (oneSlotTorsionPresentation_det ℂ k) z) hzero
    have hjet : jetClass ℂ k (finitePrimeDerivativeJetPolynomial p a rho) = 0 := by
      simpa [finitePrimeDerivativeJetPinnedAffineClass,
        fittingBoundaryClass_oneSlotPolynomial_eq] using hboundary
    have hall := (jetClass_eq_zero_iff_coeff_lt_eq_zero ℂ k).mp hjet
    let f : Fin k → ℂ := fun r => -(Real.log (p r) : ℂ)
    let v : Fin k → ℂ := fun r => a r * ((p r : ℕ) : ℂ) ^ (-rho)
    have hf : Function.Injective f := by
      intro i j hij
      have hlogC : (Real.log (p i) : ℂ) = (Real.log (p j) : ℂ) := by
        dsimp [f] at hij
        exact neg_injective hij
      have hlogR : Real.log (p i) = Real.log (p j) := by
        exact_mod_cast hlogC
      have hpiR : (0 : ℝ) < p i := by exact_mod_cast hp i
      have hpjR : (0 : ℝ) < p j := by exact_mod_cast hp j
      apply hpinj
      exact_mod_cast Real.log_injOn_pos hpiR hpjR hlogR
    have hmom : ∀ j : Fin k, ∑ r : Fin k, v r * f r ^ (j : ℕ) = 0 := by
      intro j
      have hj := hall j j.isLt
      simpa [v, f, finitePrimeDerivativeJetPolynomial_coeff, mul_assoc] using hj
    have hv : v = 0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf hmom
    funext r
    have hvr := congrFun hv r
    change a r * ((p r : ℕ) : ℂ) ^ (-rho) = 0 at hvr
    exact (mul_eq_zero.mp hvr).resolve_right
      (Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (hp r).ne')))
  · rintro rfl
    rw [finitePrimeDerivativeJetPinnedAffineClass, QuotientAddGroup.eq_zero_iff]
    refine ⟨0, 0, 0, 0, 0, ?_⟩
    ext i j
    fin_cases i
    fin_cases j
    simp [oneSlotPolynomialDefect, finitePrimeDerivativeJetPolynomial,
      pinnedAffineWeldDefect, commutatorDefect]

/-- Prime-labelled specialization of the arbitrary finite-support theorem. -/
theorem finitePrimeDerivativeJetPinnedAffineClass_prime_eq_zero_iff {k : ℕ}
    (p : Fin k → ℕ) (hp : ∀ i, (p i).Prime) (hpinj : Function.Injective p)
    (a : Fin k → ℂ) (rho : ℂ) :
    finitePrimeDerivativeJetPinnedAffineClass p a rho = 0 ↔ a = 0 :=
  finitePrimeDerivativeJetPinnedAffineClass_eq_zero_iff p (fun i => (hp i).pos) hpinj a rho

end RHTower
