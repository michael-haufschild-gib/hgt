import GaloisForLFunctions.RHTower.PinnedAffineConstantSourceBlindness
import Mathlib.Algebra.Polynomial.Degree.IsMonicOfDegree

/-!
# Prime first jets retain labels in the pinned-affine quotient

Constant sources collapse in the one-slot quotient to a single scalar sum.  The first possible
label-sensitive refinement is the first germ jet.  At a point `rho`, the truncated prime germ is

`J_p(rho;X) = p^(-rho) * (1 - log(p) X) mod X^(2 : ℕ)`.

This file proves that for two distinct positive bases, `J_p` and `J_q` are linearly independent in
the order-two pinned-affine defect quotient at every complex point.  The descended Fitting boundary
recovers both polynomial coefficients.  Their two equations form a Vandermonde system in
`log p, log q`; nonvanishing of the prime amplitudes and injectivity of the real logarithm force both
source coefficients to vanish.

Unlike raw prime evaluation, this statement retains the prime labels.  Unlike susceptibility or
pointwise-tuned cancellation, it holds uniformly for every `rho` and does not encode a target zero
location.  The arbitrary finite-order theorem below exposes the exact limitation: every square
prime packet realizes every local divisor jet uniquely, so no fixed finite-order quotient can
distinguish prime evaluation from an archimedean differential functional.  The distinction appears
only in the fixed compatibility across all orders, where the two sectors intersect only at zero.
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

/-! ## Finite-order blindness versus all-orders separation -/

/-- A square packet of distinct nonzero characters realizes every finite moment vector uniquely. -/
theorem existsUnique_weightedFiniteMoments {k : ℕ} (f w : Fin k → ℂ)
    (hf : Function.Injective f) (hw : ∀ i, w i ≠ 0) (c : Fin k → ℂ) :
    ∃! a : Fin k → ℂ,
      ∀ j : Fin k, ∑ i : Fin k, a i * w i * f i ^ (j : ℕ) = c j := by
  have hvecInj : Function.Injective (Matrix.vandermonde f).vecMulLinear := by
    intro v u hvu
    apply sub_eq_zero.mp
    apply Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf
    intro j
    have hj := congrFun hvu j
    change (∑ i : Fin k, v i * f i ^ (j : ℕ)) =
      ∑ i : Fin k, u i * f i ^ (j : ℕ) at hj
    simpa [sub_mul, Finset.sum_sub_distrib] using sub_eq_zero.mpr hj
  obtain ⟨v, hv⟩ := LinearMap.surjective_of_injective hvecInj c
  refine ⟨fun i => v i / w i, ?_, ?_⟩
  · intro j
    have hj := congrFun hv j
    change (∑ i : Fin k, v i * f i ^ (j : ℕ)) = c j at hj
    simpa [div_mul_cancel₀ _ (hw _)] using hj
  · intro a ha
    funext i
    let d : Fin k → ℂ := fun r => ((v r / w r) - a r) * w r
    have hmom : ∀ j : Fin k, ∑ r : Fin k, d r * f r ^ (j : ℕ) = 0 := by
      intro j
      have hj := ha j
      have hvj := congrFun hv j
      change (∑ r : Fin k, v r * f r ^ (j : ℕ)) = c j at hvj
      simpa [d, sub_mul, Finset.sum_sub_distrib, div_mul_cancel₀ _ (hw _),
        mul_assoc] using sub_eq_zero.mpr (hvj.trans hj.symm)
    have hd : d = 0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf hmom
    have hdi := congrFun hd i
    change ((v i / w i) - a i) * w i = 0 at hdi
    exact (sub_eq_zero.mp ((mul_eq_zero.mp hdi).resolve_right (hw i))).symm

/-- Distinct positive natural labels give distinct negative logarithmic characters. -/
theorem neg_log_nat_injective {k : ℕ} (p : Fin k → ℕ)
    (hp : ∀ i, 0 < p i) (hpinj : Function.Injective p) :
    Function.Injective (fun i => -(Real.log (p i) : ℂ)) := by
  intro i j hij
  have hlogC : (Real.log (p i) : ℂ) = (Real.log (p j) : ℂ) :=
    neg_injective hij
  have hlogR : Real.log (p i) = Real.log (p j) := by exact_mod_cast hlogC
  apply hpinj
  exact_mod_cast Real.log_injOn_pos
    (by exact_mod_cast hp i : (0 : ℝ) < p i)
    (by exact_mod_cast hp j : (0 : ℝ) < p j) hlogR

/-- **Finite-order blindness.** Every order-`k` coefficient vector is realized by a unique packet
of `k` distinct positive prime-exponential jets, at every base point. -/
theorem existsUnique_finitePrimeDerivativeJet_coeff {k : ℕ}
    (p : Fin k → ℕ) (hp : ∀ i, 0 < p i) (hpinj : Function.Injective p)
    (rho : ℂ) (c : Fin k → ℂ) :
    ∃! a : Fin k → ℂ,
      ∀ j : Fin k,
        (finitePrimeDerivativeJetPolynomial p a rho).coeff (j : ℕ) = c j := by
  simpa [finitePrimeDerivativeJetPolynomial_coeff, mul_assoc] using
    existsUnique_weightedFiniteMoments
      (fun i => -(Real.log (p i) : ℂ))
      (fun i => ((p i : ℕ) : ℂ) ^ (-rho))
      (neg_log_nat_injective p hp hpinj)
      (fun i => Complex.cpow_ne_zero_iff.mpr
        (Or.inl (Nat.cast_ne_zero.mpr (hp i).ne'))) c

/-- Equivalently, the local divisor-jet algebra is realized bijectively by any fixed square packet
of distinct positive prime jets.  This discharges the target-jet existence and uniqueness Props. -/
theorem existsUnique_finitePrimeDerivativeJet_jetClass {k : ℕ}
    (p : Fin k → ℕ) (hp : ∀ i, 0 < p i) (hpinj : Function.Injective p)
    (rho : ℂ) (z : LocalDivisorJet ℂ k) :
    ∃! a : Fin k → ℂ,
      jetClass ℂ k (finitePrimeDerivativeJetPolynomial p a rho) = z := by
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective z
  obtain ⟨a, ha, hua⟩ :=
    existsUnique_finitePrimeDerivativeJet_coeff p hp hpinj rho
      (fun j => P.coeff (j : ℕ))
  refine ⟨a, ?_, ?_⟩
  · apply sub_eq_zero.mp
    rw [jetClass, ← map_sub]
    change jetClass ℂ k (finitePrimeDerivativeJetPolynomial p a rho - P) = 0
    apply (jetClass_eq_zero_iff_coeff_lt_eq_zero ℂ k).mpr
    intro j hj
    let jj : Fin k := ⟨j, hj⟩
    rw [Polynomial.coeff_sub]
    exact sub_eq_zero.mpr (ha jj)
  · intro b hb
    apply hua
    intro j
    have hzero : jetClass ℂ k
        (finitePrimeDerivativeJetPolynomial p b rho - P) = 0 := by
      rw [jetClass, map_sub, sub_eq_zero]
      exact hb
    have hj := (jetClass_eq_zero_iff_coeff_lt_eq_zero ℂ k).mp hzero j j.isLt
    rw [Polynomial.coeff_sub] at hj
    exact sub_eq_zero.mp hj

/-- For the one-slot presentation, the descended Fitting boundary loses no information: its kernel
is exactly the pinned-affine subgroup. -/
theorem pinnedAffineBoundaryHom_oneSlot_injective
    (R : Type*) [CommRing R] (m : ℕ) :
    Function.Injective
      (pinnedAffineBoundaryHom m (oneSlotTorsionPresentation R m)
        (oneSlotTorsionPresentation_det R m)) := by
  intro q r hqr
  apply sub_eq_zero.mp
  let x := q - r
  have hx : pinnedAffineBoundaryHom m (oneSlotTorsionPresentation R m)
      (oneSlotTorsionPresentation_det R m) x = 0 := by
    dsimp [x]
    rw [map_sub, hqr, sub_self]
  change x = 0
  revert hx
  refine QuotientAddGroup.induction_on x ?_
  intro Delta hDelta
  rw [QuotientAddGroup.eq_zero_iff]
  have hclass : fittingBoundaryClass m (oneSlotTorsionPresentation R m) Delta = 0 := by
    simpa using hDelta
  have hjet : jetClass R m (Delta 0 0) = 0 := by
    simpa [fittingBoundaryClass, fittingBoundaryTrace, oneSlotTorsionPresentation,
      Matrix.adjugate_fin_one, Matrix.trace_fin_one] using hclass
  have hdiv : (X : Polynomial R) ^ m ∣ Delta 0 0 :=
    Polynomial.X_pow_dvd_iff.mpr ((jetClass_eq_zero_iff_coeff_lt_eq_zero R m).mp hjet)
  obtain ⟨Q, hQ⟩ := hdiv
  refine ⟨0, 0, oneSlotPolynomialDefect R Q, 0, 0, ?_⟩
  apply Matrix.ext
  intro i j
  fin_cases i
  fin_cases j
  simpa [pinnedAffineWeldDefect, commutatorDefect, oneSlotTorsionPresentation,
    oneSlotPolynomialDefect] using hQ

/-- Every one-slot local divisor jet is the boundary of a pinned-affine quotient class. -/
theorem pinnedAffineBoundaryHom_oneSlot_surjective
    (R : Type*) [CommRing R] (m : ℕ) :
    Function.Surjective
      (pinnedAffineBoundaryHom m (oneSlotTorsionPresentation R m)
        (oneSlotTorsionPresentation_det R m)) := by
  intro z
  obtain ⟨P, rfl⟩ := Ideal.Quotient.mk_surjective z
  refine ⟨QuotientAddGroup.mk (oneSlotPolynomialDefect R P), ?_⟩
  exact fittingBoundaryClass_oneSlotPolynomial_eq R m P

/-- **One-slot quotient classification.** The universal pinned-affine defect quotient is detected
exactly by the local divisor-jet algebra; the descended boundary is a bijection. -/
theorem pinnedAffineBoundaryHom_oneSlot_bijective
    (R : Type*) [CommRing R] (m : ℕ) :
    Function.Bijective
      (pinnedAffineBoundaryHom m (oneSlotTorsionPresentation R m)
        (oneSlotTorsionPresentation_det R m)) :=
  ⟨pinnedAffineBoundaryHom_oneSlot_injective R m,
    pinnedAffineBoundaryHom_oneSlot_surjective R m⟩

/-- **Complete finite one-slot classification.** At every order and base point, any fixed square
packet of distinct positive prime germs represents every pinned-affine quotient class uniquely. -/
theorem existsUnique_finitePrimeDerivativeJet_pinnedAffineClass {k : ℕ}
    (p : Fin k → ℕ) (hp : ∀ i, 0 < p i) (hpinj : Function.Injective p)
    (rho : ℂ) (q : PinnedAffineDefectQuotient k (oneSlotTorsionPresentation ℂ k)) :
    ∃! a : Fin k → ℂ, finitePrimeDerivativeJetPinnedAffineClass p a rho = q := by
  let boundary := pinnedAffineBoundaryHom k (oneSlotTorsionPresentation ℂ k)
    (oneSlotTorsionPresentation_det ℂ k)
  have hboundary := pinnedAffineBoundaryHom_oneSlot_bijective ℂ k
  obtain ⟨a, ha, hua⟩ :=
    existsUnique_finitePrimeDerivativeJet_jetClass p hp hpinj rho (boundary q)
  refine ⟨a, hboundary.1 ?_, ?_⟩
  · simpa [boundary, finitePrimeDerivativeJetPinnedAffineClass,
      fittingBoundaryClass_oneSlotPolynomial_eq] using ha
  · intro b hb
    apply hua
    have hmap := congrArg boundary hb
    simpa [boundary, finitePrimeDerivativeJetPinnedAffineClass,
      fittingBoundaryClass_oneSlotPolynomial_eq] using hmap

/-- **All-orders intersection theorem.** A finite packet of distinct positive prime characters and
an eventually-zero differential moment sequence can agree at every order only when both vanish.
This is the exact fixed-constraint complement to finite-order blindness. -/
theorem finitePrimeMoments_eq_eventuallyZero_iff {k d : ℕ}
    (p : Fin k → ℕ) (hp : ∀ i, 1 < p i) (hpinj : Function.Injective p)
    (a : Fin k → ℂ) (mu : ℕ → ℂ) (hmu : ∀ n, d ≤ n → mu n = 0) :
    (∀ n : ℕ, (∑ i : Fin k, a i * (-(Real.log (p i) : ℂ)) ^ n) = mu n) ↔
      a = 0 ∧ mu = 0 := by
  classical
  constructor
  · intro hrep
    let f : Fin k → ℂ := fun i => -(Real.log (p i) : ℂ)
    let v : Fin k → ℂ := fun i => a i * f i ^ d
    have hf : Function.Injective f :=
      neg_log_nat_injective p (fun i => Nat.zero_lt_one.trans (hp i)) hpinj
    have hf0 : ∀ i, f i ≠ 0 := by
      intro i
      have hlog : 0 < Real.log (p i) := Real.log_pos (by exact_mod_cast hp i)
      dsimp [f]
      exact neg_ne_zero.mpr (by exact_mod_cast hlog.ne')
    have hmom : ∀ r : Fin k, ∑ i : Fin k, v i * f i ^ (r : ℕ) = 0 := by
      intro r
      have hr := hrep (d + (r : ℕ))
      rw [hmu _ (Nat.le_add_right d (r : ℕ))] at hr
      simpa [v, f, pow_add, mul_assoc, add_comm] using hr
    have hv : v = 0 := Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hf hmom
    have ha : a = 0 := by
      funext i
      have hvi := congrFun hv i
      change a i * f i ^ d = 0 at hvi
      exact (mul_eq_zero.mp hvi).resolve_right (pow_ne_zero d (hf0 i))
    refine ⟨ha, ?_⟩
    funext n
    have hn := hrep n
    simpa [ha] using hn.symm
  · rintro ⟨rfl, rfl⟩ n
    simp

/-! ## The archimedean derivation is outside every finite prime span -/

/-- Moments of coefficient extraction at derivative order one: the derivation sends `X` to `1` and
all other monomials to zero at the origin. -/
def archimedeanDerivationMoment (n : ℕ) : ℂ := if n = 1 then 1 else 0

/-! ## Exact first failure of finite prime interpolation -/

/-- The monic polynomial whose nodes are a finite family of real frequencies. -/
def negativeNodePolynomial {k : ℕ} (f : Fin k → ℝ) : Polynomial ℝ :=
  ∏ i : Fin k, (X - C (f i))

@[simp]
theorem negativeNodePolynomial_eval_node {k : ℕ} (f : Fin k → ℝ) (i : Fin k) :
    (negativeNodePolynomial f).eval (f i) = 0 := by
  classical
  rw [negativeNodePolynomial]
  change (Polynomial.evalRingHom (f i)) (∏ j : Fin k, (X - C (f j))) = 0
  rw [map_prod]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)

/-- If every node is negative, the node polynomial has strictly positive derivative at zero. -/
theorem negativeNodePolynomial_derivative_eval_zero_pos {k : ℕ} (hk : 0 < k)
    (f : Fin k → ℝ) (hf : ∀ i, f i < 0) :
    0 < (negativeNodePolynomial f).derivative.eval 0 := by
  classical
  rw [negativeNodePolynomial, Polynomial.derivative_prod_finset,
    Polynomial.eval_finsetSum]
  apply Finset.sum_pos
  · intro i _
    simp only [Polynomial.derivative_sub, Polynomial.derivative_X,
      Polynomial.derivative_C, sub_zero, mul_one]
    change 0 < (Polynomial.evalRingHom 0) (∏ j ∈ Finset.univ.erase i, (X - C (f j)))
    rw [map_prod]
    apply Finset.prod_pos
    intro j _
    simpa using neg_pos.mpr (hf j)
  · haveI : Nonempty (Fin k) := Fintype.card_pos_iff.mp (by simpa using hk)
    exact Finset.univ_nonempty

/-- Moment agreement through the degree of a polynomial makes weighted evaluation equal coefficient
extraction at degree one. -/
theorem weighted_eval_eq_coeff_one_of_moments {k : ℕ} (hk : 0 < k)
    (f a : Fin k → ℂ) (P : Polynomial ℂ) (hdeg : P.natDegree ≤ k)
    (hmom : ∀ n, n ≤ k → (∑ i : Fin k, a i * f i ^ n) = if n = 1 then 1 else 0) :
    (∑ i : Fin k, a i * P.eval (f i)) = P.coeff 1 := by
  have hdeg' : P.natDegree < k + 1 := Nat.lt_succ_of_le hdeg
  simp_rw [Polynomial.eval_eq_sum_range' hdeg']
  calc
    (∑ i : Fin k, a i * ∑ n ∈ Finset.range (k + 1), P.coeff n * f i ^ n) =
        ∑ n ∈ Finset.range (k + 1), P.coeff n * ∑ i : Fin k, a i * f i ^ n := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro n _
      ring
    _ = ∑ n ∈ Finset.range (k + 1), P.coeff n * (if n = 1 then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [hmom n (Nat.le_of_lt_succ (Finset.mem_range.mp hn))]
    _ = P.coeff 1 := by
      rw [Finset.sum_eq_single 1]
      · simp
      · intro n _ hne
        simp [hne]
      · intro hnot
        exact (hnot (Finset.mem_range.mpr (by omega))).elim

/-- The node polynomial has degree equal to the number of nodes, with no distinctness hypothesis. -/
theorem negativeNodePolynomial_natDegree {k : ℕ} (f : Fin k → ℝ) :
    (negativeNodePolynomial f).natDegree = k := by
  classical
  rw [negativeNodePolynomial, Polynomial.natDegree_prod_of_monic]
  · simp
  · intro i _
    exact Polynomial.monic_X_sub_C _

/-- Moment agreement below order `k` makes weighted evaluation of every degree-`< k` polynomial
equal coefficient extraction at degree one. -/
theorem weighted_eval_eq_coeff_one_of_finMoments {k : ℕ} (hk : 0 < k)
    (f a : Fin k → ℂ) (P : Polynomial ℂ) (hdeg : P.natDegree < k)
    (hmom : ∀ j : Fin k,
      (∑ i : Fin k, a i * f i ^ (j : ℕ)) = archimedeanDerivationMoment (j : ℕ)) :
    (∑ i : Fin k, a i * P.eval (f i)) = P.coeff 1 := by
  simp_rw [Polynomial.eval_eq_sum_range' hdeg]
  calc
    (∑ i : Fin k, a i * ∑ n ∈ Finset.range k, P.coeff n * f i ^ n) =
        ∑ n ∈ Finset.range k, P.coeff n * ∑ i : Fin k, a i * f i ^ n := by
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro n _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = ∑ n ∈ Finset.range k, P.coeff n * archimedeanDerivationMoment n := by
      apply Finset.sum_congr rfl
      intro n hn
      exact congrArg (P.coeff n * ·) (hmom ⟨n, Finset.mem_range.mp hn⟩)
    _ = P.coeff 1 := by
      by_cases h1 : 1 < k
      · rw [Finset.sum_eq_single 1]
        · simp [archimedeanDerivationMoment]
        · intro n _ hne
          simp [archimedeanDerivationMoment, hne]
        · intro hnot
          exact (hnot (Finset.mem_range.mpr h1)).elim
      · have hk1 : k = 1 := by omega
        subst k
        have hcoeff : P.coeff 1 = 0 :=
          Polynomial.coeff_eq_zero_of_natDegree_lt hdeg
        simp [archimedeanDerivationMoment, hcoeff]

/-- **Exact next-order defect.** If `k` real evaluation nodes match coefficient extraction in every
degree below `k`, their first omitted moment differs from the derivation moment by exactly the
negative derivative at zero of the node polynomial. -/
theorem finiteNegativeDerivationInterpolation_nextOrderDefect_eq {k : ℕ}
    (hk : 0 < k) (f : Fin k → ℝ) (a : Fin k → ℂ)
    (hmatch : ∀ j : Fin k,
      (∑ i : Fin k, a i * (f i : ℂ) ^ (j : ℕ)) =
        archimedeanDerivationMoment (j : ℕ)) :
    (∑ i : Fin k, a i * (f i : ℂ) ^ k) - archimedeanDerivationMoment k =
      -(((negativeNodePolynomial f).derivative.eval (0 : ℝ) : ℝ) : ℂ) := by
  classical
  let Qr : Polynomial ℝ := negativeNodePolynomial f
  let Q : Polynomial ℂ := Qr.map Complex.ofRealHom
  have hQrMonic : Qr.Monic := by
    dsimp [Qr, negativeNodePolynomial]
    exact Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hQMonic : Q.Monic := by
    dsimp [Q]
    exact hQrMonic.map Complex.ofRealHom
  have hQdeg : Q.natDegree = k := by
    dsimp [Q]
    rw [Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective]
    exact negativeNodePolynomial_natDegree f
  have hQiso : Q.IsMonicOfDegree k := ⟨hQdeg, hQMonic⟩
  let P : Polynomial ℂ := Q - X ^ k
  have hPdeg : P.natDegree < k := by
    dsimp [P]
    exact hQiso.natDegree_sub_X_pow hk.ne'
  have hweighted := weighted_eval_eq_coeff_one_of_finMoments hk
    (fun i => (f i : ℂ)) a P hPdeg hmatch
  have hQprod : Q = ∏ i : Fin k, (X - C (f i : ℂ)) := by
    dsimp [Q, Qr, negativeNodePolynomial]
    rw [Polynomial.map_prod]
    apply Finset.prod_congr rfl
    intro i _
    simp
  have hPeval : ∀ i : Fin k, P.eval (f i : ℂ) = -(f i : ℂ) ^ k := by
    intro i
    have hroot : Q.eval (f i : ℂ) = 0 := by
      rw [hQprod]
      change (Polynomial.evalRingHom (f i : ℂ))
        (∏ j : Fin k, (X - C (f j : ℂ))) = 0
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    simp [P, hroot]
  have hleft : (∑ i : Fin k, a i * P.eval (f i : ℂ)) =
      -(∑ i : Fin k, a i * (f i : ℂ) ^ k) := by
    simp_rw [hPeval]
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hPcoeff : P.coeff 1 =
      (((negativeNodePolynomial f).derivative.eval (0 : ℝ) : ℝ) : ℂ) -
        archimedeanDerivationMoment k := by
    dsimp [P]
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
    have hQcoeff : Q.coeff 1 =
        (((negativeNodePolynomial f).derivative.eval (0 : ℝ) : ℝ) : ℂ) := by
      dsimp [Q, Qr]
      rw [Polynomial.coeff_map]
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
      norm_num
    rw [hQcoeff]
    by_cases hk1 : k = 1
    · simp only [archimedeanDerivationMoment]
      rw [if_pos hk1.symm, if_pos hk1]
    · have h1k : 1 ≠ k := Ne.symm hk1
      simp only [archimedeanDerivationMoment]
      rw [if_neg h1k, if_neg hk1]
  rw [hleft, hPcoeff] at hweighted
  linear_combination -hweighted

/-- With all nodes negative, the exact next-order defect has strictly negative real part. -/
theorem finiteNegativeDerivationInterpolation_nextOrderDefect_re_neg {k : ℕ}
    (hk : 0 < k) (f : Fin k → ℝ) (hf : ∀ i, f i < 0) (a : Fin k → ℂ)
    (hmatch : ∀ j : Fin k,
      (∑ i : Fin k, a i * (f i : ℂ) ^ (j : ℕ)) =
        archimedeanDerivationMoment (j : ℕ)) :
    ((∑ i : Fin k, a i * (f i : ℂ) ^ k) - archimedeanDerivationMoment k).re < 0 := by
  rw [finiteNegativeDerivationInterpolation_nextOrderDefect_eq hk f a hmatch]
  simpa using neg_lt_zero.mpr (negativeNodePolynomial_derivative_eval_zero_pos hk f hf)

/-- No `k` negative evaluation nodes represent coefficient extraction at degree one through order
`k`.  The node polynomial vanishes at every evaluation node, but its degree-one coefficient is
strictly positive. -/
theorem no_negativeFiniteMoments_eq_derivation_through_card {k : ℕ} (hk : 0 < k)
    (f : Fin k → ℝ) (hf : ∀ i, f i < 0) (a : Fin k → ℂ) :
    ¬ ∀ n : ℕ, n ≤ k →
      (∑ i : Fin k, a i * (f i : ℂ) ^ n) = if n = 1 then 1 else 0 := by
  classical
  intro hmom
  let Qr : Polynomial ℝ := negativeNodePolynomial f
  let Q : Polynomial ℂ := ∏ i : Fin k, (X - C (f i : ℂ))
  have hQmap : Q = Qr.map Complex.ofRealHom := by
    dsimp [Q, Qr, negativeNodePolynomial]
    rw [Polynomial.map_prod]
    apply Finset.prod_congr rfl
    intro i _
    simp
  have hQdeg : Q.natDegree ≤ k := by
    rw [hQmap, Polynomial.natDegree_map_eq_of_injective Complex.ofReal_injective]
    change (negativeNodePolynomial f).natDegree ≤ k
    rw [negativeNodePolynomial_natDegree]
  have hweighted := weighted_eval_eq_coeff_one_of_moments hk
    (fun i => (f i : ℂ)) a Q hQdeg hmom
  have hleft : (∑ i : Fin k, a i * Q.eval (f i : ℂ)) = 0 := by
    apply Finset.sum_eq_zero
    intro i _
    have hroot : Q.eval (f i : ℂ) = 0 := by
      dsimp [Q]
      change (Polynomial.evalRingHom (f i : ℂ))
        (∏ j : Fin k, (X - C (f j : ℂ))) = 0
      rw [map_prod]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp)
    rw [hroot, mul_zero]
  have hcoeffZero : Q.coeff 1 = 0 := by
    rw [hleft] at hweighted
    exact hweighted.symm
  have hderivPos := negativeNodePolynomial_derivative_eval_zero_pos hk f hf
  have hcoeffRPos : 0 < Qr.coeff 1 := by
    have heq : Qr.derivative.eval 0 = Qr.coeff 1 := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative]
      norm_num
    rw [← heq]
    exact hderivPos
  have hcoeffNe : Q.coeff 1 ≠ 0 := by
    rw [hQmap, Polynomial.coeff_map]
    exact Complex.ofReal_ne_zero.mpr hcoeffRPos.ne'
  exact hcoeffNe hcoeffZero

/-- The exact first omitted-order defect for prime-log nodes. -/
theorem finitePrimeDerivationInterpolation_nextOrderDefect_eq {k : ℕ}
    (hk : 0 < k) (p : Fin k → ℕ) (a : Fin k → ℂ)
    (hmatch : ∀ j : Fin k,
      (∑ i : Fin k, a i * (-(Real.log (p i) : ℂ)) ^ (j : ℕ)) =
        archimedeanDerivationMoment (j : ℕ)) :
    (∑ i : Fin k, a i * (-(Real.log (p i) : ℂ)) ^ k) -
        archimedeanDerivationMoment k =
      -(((negativeNodePolynomial (fun i => -Real.log (p i))).derivative.eval
        (0 : ℝ) : ℝ) : ℂ) := by
  have hmatch' : ∀ j : Fin k,
      (∑ i : Fin k, a i * ((-Real.log (p i) : ℝ) : ℂ) ^ (j : ℕ)) =
        archimedeanDerivationMoment (j : ℕ) := by
    intro j
    simpa using hmatch j
  simpa using finiteNegativeDerivationInterpolation_nextOrderDefect_eq hk
    (fun i => -Real.log (p i)) a hmatch'

/-- For positive prime labels, every finite derivation interpolation has a strictly negative
first omitted-order defect. -/
theorem finitePrimeDerivationInterpolation_nextOrderDefect_re_neg {k : ℕ}
    (hk : 0 < k) (p : Fin k → ℕ) (hp : ∀ i, 1 < p i) (a : Fin k → ℂ)
    (hmatch : ∀ j : Fin k,
      (∑ i : Fin k, a i * (-(Real.log (p i) : ℂ)) ^ (j : ℕ)) =
        archimedeanDerivationMoment (j : ℕ)) :
    ((∑ i : Fin k, a i * (-(Real.log (p i) : ℂ)) ^ k) -
      archimedeanDerivationMoment k).re < 0 := by
  have hmatch' : ∀ j : Fin k,
      (∑ i : Fin k, a i * ((-Real.log (p i) : ℝ) : ℂ) ^ (j : ℕ)) =
        archimedeanDerivationMoment (j : ℕ) := by
    intro j
    simpa using hmatch j
  simpa using finiteNegativeDerivationInterpolation_nextOrderDefect_re_neg hk
    (fun i => -Real.log (p i))
    (fun i => neg_lt_zero.mpr (Real.log_pos (by exact_mod_cast hp i))) a hmatch'

/-- No `k` positive prime-log characters realize the archimedean derivation through order `k`.
Distinctness is unnecessary for this obstruction. -/
theorem no_finitePrimeMoments_eq_archimedeanDerivation_through_card {k : ℕ}
    (hk : 0 < k) (p : Fin k → ℕ) (hp : ∀ i, 1 < p i) (a : Fin k → ℂ) :
    ¬ ∀ n : ℕ, n ≤ k →
      (∑ i : Fin k, a i * (-(Real.log (p i) : ℂ)) ^ n) =
        archimedeanDerivationMoment n := by
  simpa [archimedeanDerivationMoment] using
    no_negativeFiniteMoments_eq_derivation_through_card hk
      (fun i => -Real.log (p i))
      (fun i => neg_lt_zero.mpr (Real.log_pos (by exact_mod_cast hp i))) a

/-- Any packet matching the derivation through orders `< k` necessarily fails at the first omitted
order `k`. -/
theorem finitePrimeDerivationInterpolation_nextOrder_ne {k : ℕ}
    (hk : 0 < k) (p : Fin k → ℕ) (hp : ∀ i, 1 < p i) (a : Fin k → ℂ)
    (hmatch : ∀ j : Fin k,
      (∑ i : Fin k, a i * (-(Real.log (p i) : ℂ)) ^ (j : ℕ)) =
        archimedeanDerivationMoment (j : ℕ)) :
    (∑ i : Fin k, a i * (-(Real.log (p i) : ℂ)) ^ k) ≠
      archimedeanDerivationMoment k := by
  intro hnext
  have hneg := finitePrimeDerivationInterpolation_nextOrderDefect_re_neg hk p hp a hmatch
  rw [hnext, sub_self] at hneg
  exact (lt_irrefl 0) hneg

/-- **No coefficient-preserving support extension.** A packet matching the first `k` derivation
moments cannot be extended to `k+1` matching moments by appending one new prime coefficient while
leaving every existing coefficient fixed.  Any successive finite repair must change old data. -/
theorem no_finitePrimeDerivationInterpolation_coefficientPreserving_extension {k : ℕ}
    (hk : 0 < k) (p : Fin (k + 1) → ℕ) (hp : ∀ i, 1 < p i)
    (a : Fin k → ℂ) (b : Fin (k + 1) → ℂ)
    (ha : ∀ j : Fin k,
      (∑ i : Fin k, a i * (-(Real.log (p i.castSucc) : ℂ)) ^ (j : ℕ)) =
        archimedeanDerivationMoment (j : ℕ))
    (hb : ∀ j : Fin (k + 1),
      (∑ i : Fin (k + 1), b i * (-(Real.log (p i) : ℂ)) ^ (j : ℕ)) =
        archimedeanDerivationMoment (j : ℕ))
    (hrestrict : ∀ i : Fin k, b i.castSucc = a i) : False := by
  have ha0 := ha ⟨0, hk⟩
  have hb0 := hb ⟨0, Nat.zero_lt_succ k⟩
  have hblast : b (Fin.last k) = 0 := by
    have h01 : (0 : ℕ) ≠ 1 := by norm_num
    simp only [pow_zero, mul_one, archimedeanDerivationMoment, if_neg h01] at ha0 hb0
    rw [Fin.sum_univ_castSucc] at hb0
    have hold : (∑ i : Fin k, b i.castSucc) = ∑ i : Fin k, a i := by
      apply Finset.sum_congr rfl
      intro i _
      exact hrestrict i
    rw [hold, ha0, zero_add] at hb0
    exact hb0
  have hbk := hb (Fin.last k)
  have hkEq : (∑ i : Fin k, a i * (-(Real.log (p i.castSucc) : ℂ)) ^ k) =
      archimedeanDerivationMoment k := by
    rw [Fin.sum_univ_castSucc] at hbk
    simp only [Fin.val_last] at hbk
    have holdk :
        (∑ i : Fin k, b i.castSucc * (-(Real.log (p i.castSucc) : ℂ)) ^ k) =
          ∑ i : Fin k, a i * (-(Real.log (p i.castSucc) : ℂ)) ^ k := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hrestrict]
    rw [holdk, hblast, zero_mul, add_zero] at hbk
    simpa using hbk
  exact finitePrimeDerivationInterpolation_nextOrder_ne hk (fun i => p i.castSucc)
    (fun i => hp i.castSucc) a ha hkEq

/-- Distinct positive prime-log nodes have a unique interpolation of the first `k` derivation
moments. -/
theorem existsUnique_finitePrimeDerivationInterpolation {k : ℕ}
    (p : Fin k → ℕ) (hp : ∀ i, 1 < p i) (hpinj : Function.Injective p) :
    ∃! a : Fin k → ℂ, ∀ j : Fin k,
      (∑ i : Fin k, a i * (-(Real.log (p i) : ℂ)) ^ (j : ℕ)) =
        archimedeanDerivationMoment (j : ℕ) := by
  simpa using existsUnique_weightedFiniteMoments
    (fun i => -(Real.log (p i) : ℂ)) (fun _ => (1 : ℂ))
    (neg_log_nat_injective p (fun i => Nat.zero_lt_one.trans (hp i)) hpinj)
    (fun _ => one_ne_zero) (fun j => archimedeanDerivationMoment (j : ℕ))

/-- **Exact finite/all-orders boundary.** There is a unique prime packet matching the derivation at
all orders `< k`; its order-`k` defect is the negative node-polynomial derivative and has strictly
negative real part. -/
theorem existsUnique_finitePrimeDerivationInterpolation_with_nextOrderDefect {k : ℕ}
    (hk : 0 < k) (p : Fin k → ℕ) (hp : ∀ i, 1 < p i) (hpinj : Function.Injective p) :
    ∃! a : Fin k → ℂ,
      (∀ j : Fin k,
        (∑ i : Fin k, a i * (-(Real.log (p i) : ℂ)) ^ (j : ℕ)) =
          archimedeanDerivationMoment (j : ℕ)) ∧
      (∑ i : Fin k, a i * (-(Real.log (p i) : ℂ)) ^ k) -
          archimedeanDerivationMoment k =
        -(((negativeNodePolynomial (fun i => -Real.log (p i))).derivative.eval
          (0 : ℝ) : ℝ) : ℂ) ∧
      ((∑ i : Fin k, a i * (-(Real.log (p i) : ℂ)) ^ k) -
        archimedeanDerivationMoment k).re < 0 := by
  obtain ⟨a, ha, hua⟩ := existsUnique_finitePrimeDerivationInterpolation p hp hpinj
  refine ⟨a, ⟨ha, finitePrimeDerivationInterpolation_nextOrderDefect_eq hk p a ha,
    finitePrimeDerivationInterpolation_nextOrderDefect_re_neg hk p hp a ha⟩, ?_⟩
  intro b hb
  exact hua b hb.1

/-- **Finite-prime/archimedean separation.**  No finite packet of distinct positive prime
evaluation characters can equal the archimedean derivation moment sequence.  The proof uses only
the fixed moment constraints: degrees `2,...,k+1` kill the packet by Vandermonde, contradicting its
required degree-one value. -/
theorem no_finitePrimeMoments_eq_archimedeanDerivationMoment {k : ℕ}
    (p : Fin k → ℕ) (hp : ∀ i, 1 < p i) (hpinj : Function.Injective p)
    (a : Fin k → ℂ) :
    ¬ ∀ n : ℕ,
      (∑ i : Fin k, a i * (-(Real.log (p i) : ℂ)) ^ n) =
        archimedeanDerivationMoment n := by
  intro hrep
  have htail : ∀ n, 2 ≤ n → archimedeanDerivationMoment n = 0 := by
    intro n hn
    have hne : n ≠ 1 := by omega
    simp [archimedeanDerivationMoment, hne]
  have hzero :=
    (finitePrimeMoments_eq_eventuallyZero_iff p hp hpinj a
      archimedeanDerivationMoment htail).mp hrep
  have hdegreeOne := congrFun hzero.2 1
  simp [archimedeanDerivationMoment] at hdegreeOne

/-- Prime-labelled specialization of finite-prime/archimedean separation. -/
theorem no_finitePrimeMoments_eq_archimedeanDerivationMoment_prime {k : ℕ}
    (p : Fin k → ℕ) (hp : ∀ i, (p i).Prime) (hpinj : Function.Injective p)
    (a : Fin k → ℂ) :
    ¬ ∀ n : ℕ,
      (∑ i : Fin k, a i * (-(Real.log (p i) : ℂ)) ^ n) =
        archimedeanDerivationMoment n :=
  no_finitePrimeMoments_eq_archimedeanDerivationMoment p (fun i => (hp i).one_lt) hpinj a

end RHTower
