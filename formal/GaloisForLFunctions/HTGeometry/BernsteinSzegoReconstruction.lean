import GaloisForLFunctions.HTGeometry.BernsteinSzegoMomentForm
import Mathlib.Analysis.Normed.Algebra.GelfandFormula
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Stable terminal reconstruction and the exact Bernstein--Szegő prefix law

A normalized terminal coefficient vector defines a finite feedback operator.  Its eigenvalues are
exactly roots of the terminal polynomial, so strict open-disk root location makes a power of the
feedback operator contractive.  The difference of any two compatible Toeplitz sesquilinear forms
is invariant under simultaneous feedback.  Contractivity therefore forces that difference to
vanish, proving that stable terminal data determines the complete finite Toeplitz section.

Applying this reconstruction law to the reciprocal-square Bernstein--Szegő density gives exact
finite-prefix reproduction directly, without importing an asymptotic approximation theorem.
-/

namespace GaloisForLFunctions.HTGeometry

open Complex Matrix Polynomial
open scoped ComplexConjugate ComplexOrder
open Filter
open scoped ENNReal NNReal Topology

noncomputable section

def opucResidualLinear {N : ℕ} (p : Fin (N + 2) → ℂ) :
    (Fin (N + 1) → ℂ) →ₗ[ℂ] (Fin (N + 1) → ℂ) where
  toFun q i :=
    opucTail q i.castSucc -
      (q (Fin.last N) / p (Fin.last (N + 1))) * p i.castSucc
  map_add' q r := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [opucTail]
      ring
    · simp [opucTail]
      ring
  map_smul' a q := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [opucTail]
      ring
    · simp [opucTail]
      ring

theorem opucTail_eq_feedback_add_head_residual
    {N : ℕ} (p : Fin (N + 2) → ℂ) (hp : p (Fin.last (N + 1)) ≠ 0)
    (q : Fin (N + 1) → ℂ) :
    opucTail q =
      (q (Fin.last N) / p (Fin.last (N + 1))) • p +
        opucHead (opucResidualLinear p q) := by
  funext i
  refine Fin.lastCases ?_ (fun k => ?_) i
  · simp [opucResidualLinear, opucTail, opucHead, hp]
  · simp [opucResidualLinear, opucTail, opucHead]

def opucResidualCLM {N : ℕ} (p : Fin (N + 2) → ℂ) :
    (Fin (N + 1) → ℂ) →L[ℂ] (Fin (N + 1) → ℂ) :=
  (opucResidualLinear p).toContinuousLinearMap

@[simp]
theorem opucResidualCLM_apply {N : ℕ} (p : Fin (N + 2) → ℂ)
    (q : Fin (N + 1) → ℂ) :
    opucResidualCLM p q = opucResidualLinear p q := rfl

theorem finiteCoefficientPolynomialEval_opucTail
    {N : ℕ} (q : Fin (N + 1) → ℂ) (z : ℂ) :
    finiteCoefficientPolynomialEval (opucTail q) z =
      z * finiteCoefficientPolynomialEval q z := by
  simp only [finiteCoefficientPolynomialEval]
  rw [Fin.sum_univ_succ]
  simp [opucTail, pow_succ]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem finiteCoefficientPolynomialEval_opucHead_same
    {N : ℕ} (q : Fin (N + 1) → ℂ) (z : ℂ) :
    finiteCoefficientPolynomialEval (opucHead q) z =
      finiteCoefficientPolynomialEval q z := by
  exact finiteCoefficientPolynomialEval_opucHead q z

theorem finiteCoefficientPolynomialEval_eq_eval_ofFn
    {N : ℕ} (u : Fin (N + 1) → ℂ) (z : ℂ) :
    finiteCoefficientPolynomialEval u z = (Polynomial.ofFn (N + 1) u).eval z := by
  rw [Polynomial.ofFn_eq_sum_monomial]
  symm
  change Polynomial.eval z
      (Finset.sum (Finset.univ : Finset (Fin (N + 1)))
        (fun i => Polynomial.monomial (i : ℕ) (u i))) =
    Finset.sum (Finset.univ : Finset (Fin (N + 1)))
      (fun i => u i * z ^ (i : ℕ))
  simpa using Polynomial.eval_finsetSum (Finset.univ : Finset (Fin (N + 1)))
    (fun i : Fin (N + 1) => Polynomial.monomial (i : ℕ) (u i)) z

theorem finiteCoefficientPolynomialEval_add
    {N : ℕ} (u v : Fin (N + 1) → ℂ) (z : ℂ) :
    finiteCoefficientPolynomialEval (u + v) z =
      finiteCoefficientPolynomialEval u z + finiteCoefficientPolynomialEval v z := by
  simp only [finiteCoefficientPolynomialEval, Pi.add_apply, add_mul,
    Finset.sum_add_distrib]

theorem finiteCoefficientPolynomialEval_smul
    {N : ℕ} (a : ℂ) (u : Fin (N + 1) → ℂ) (z : ℂ) :
    finiteCoefficientPolynomialEval (a • u) z =
      a * finiteCoefficientPolynomialEval u z := by
  simp only [finiteCoefficientPolynomialEval, Pi.smul_apply, smul_eq_mul, mul_assoc,
    Finset.mul_sum]

theorem opucResidual_eigenvalue_isRoot
    {N : ℕ} (p : Fin (N + 2) → ℂ) (hp : p (Fin.last (N + 1)) ≠ 0)
    {lam : ℂ} (hlam : Module.End.HasEigenvalue (opucResidualLinear p) lam) :
    (Polynomial.ofFn (N + 2) p).IsRoot lam := by
  obtain ⟨q, hq⟩ := hlam.exists_hasEigenvector
  have heig : opucResidualLinear p q = lam • q := hq.apply_eq_smul
  let a : ℂ := q (Fin.last N) / p (Fin.last (N + 1))
  have hfeedback := opucTail_eq_feedback_add_head_residual p hp q
  have heq : lam * finiteCoefficientPolynomialEval q lam =
      a * finiteCoefficientPolynomialEval p lam +
        lam * finiteCoefficientPolynomialEval q lam := by
    calc
      lam * finiteCoefficientPolynomialEval q lam =
          finiteCoefficientPolynomialEval (opucTail q) lam :=
        (finiteCoefficientPolynomialEval_opucTail q lam).symm
      _ = finiteCoefficientPolynomialEval
          (a • p + opucHead (opucResidualLinear p q)) lam := by
        rw [hfeedback]
      _ = a * finiteCoefficientPolynomialEval p lam +
          finiteCoefficientPolynomialEval (opucResidualLinear p q) lam := by
        rw [finiteCoefficientPolynomialEval_add,
          finiteCoefficientPolynomialEval_smul,
          finiteCoefficientPolynomialEval_opucHead_same]
      _ = a * finiteCoefficientPolynomialEval p lam +
          lam * finiteCoefficientPolynomialEval q lam := by
        rw [heig, finiteCoefficientPolynomialEval_smul]
  have ha : a ≠ 0 := by
    intro ha0
    have htail : opucTail q = opucHead (lam • q) := by
      rw [hfeedback, heig]
      simp [a, ha0]
    let Q : Polynomial ℂ := Polynomial.ofFn (N + 1) q
    have hpoly : Polynomial.X * Q = Polynomial.C lam * Q := by
      apply Polynomial.funext
      intro z
      have hz := congrArg (fun u : Fin (N + 2) → ℂ =>
        finiteCoefficientPolynomialEval u z) htail
      rw [Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_mul,
        Polynomial.eval_C]
      rw [show Q.eval z = finiteCoefficientPolynomialEval q z by
        simpa [Q] using
          (finiteCoefficientPolynomialEval_eq_eval_ofFn q z).symm]
      change finiteCoefficientPolynomialEval (opucTail q) z =
        finiteCoefficientPolynomialEval (opucHead (lam • q)) z at hz
      rw [finiteCoefficientPolynomialEval_opucTail,
        finiteCoefficientPolynomialEval_opucHead_same,
        finiteCoefficientPolynomialEval_smul] at hz
      exact hz
    have hzero : Q = 0 := by
      have hmul : (Polynomial.X - Polynomial.C lam) * Q = 0 := by
        rw [sub_mul, hpoly, sub_self]
      exact (mul_eq_zero.mp hmul).resolve_left
        (Polynomial.X_sub_C_ne_zero lam)
    have hqzero : q = 0 := by
      have htoFn := congrArg (Polynomial.toFn (N + 1)) hzero
      simpa only [Q, Polynomial.toFn_comp_ofFn_eq_id,
        Polynomial.toFn_zero] using htoFn
    exact hq.2 hqzero
  rw [Polynomial.IsRoot, ← finiteCoefficientPolynomialEval_eq_eval_ofFn]
  have hap : a * finiteCoefficientPolynomialEval p lam = 0 := by
    linear_combination -heq
  exact (mul_eq_zero.mp hap).resolve_left ha

/-- A strict spectral-radius bound supplies an actual power that is a contraction in the ambient
norm.  This is the exact fragment of Gelfand's formula needed for the reconstruction argument. -/
theorem exists_pos_pow_norm_lt_one_of_spectralRadius_lt_one
    {A : Type*} [NormedRing A] [NormedAlgebra ℂ A] [CompleteSpace A] [Nontrivial A]
    (a : A) (ha : spectralRadius ℂ a < 1) :
    ∃ m : ℕ, 0 < m ∧ ‖a ^ m‖ < 1 := by
  have hlim := spectrum.pow_norm_pow_one_div_tendsto_nhds_spectralRadius a
  have hev : ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (‖a ^ n‖ ^ (1 / (n : ℝ))) < 1 :=
    (tendsto_order.mp hlim).2 1 ha
  obtain ⟨M, hM⟩ := (eventually_atTop.mp hev)
  let m := max M 1
  have hmpos : 0 < m := by simp [m]
  refine ⟨m, hmpos, ?_⟩
  have hrootENN := hM m (by simp [m])
  have hroot : ‖a ^ m‖ ^ (1 / (m : ℝ)) < 1 :=
    ENNReal.ofReal_lt_one.mp hrootENN
  by_contra hnot
  have hbase : 1 ≤ ‖a ^ m‖ := le_of_not_gt hnot
  have hexp : 0 ≤ (1 / (m : ℝ)) := by positivity
  exact (not_lt_of_ge (Real.one_le_rpow hbase hexp)) hroot

/-- If all roots of the feedback polynomial lie in the open disk, some power of the residual
feedback operator is a strict operator-norm contraction. -/
theorem opucResidual_exists_contracting_power
    {N : ℕ} (p : Fin (N + 2) → ℂ) (hp : p (Fin.last (N + 1)) ≠ 0)
    (hroots : ∀ z : ℂ, (Polynomial.ofFn (N + 2) p).IsRoot z → ‖z‖ < 1) :
    ∃ m : ℕ, 0 < m ∧ ‖(opucResidualCLM p) ^ m‖ < 1 := by
  have hrho : spectralRadius ℂ (opucResidualCLM p) < 1 := by
    apply spectrum.spectralRadius_lt_of_forall_lt (opucResidualCLM p)
    intro z hz
    have hzlin : z ∈ spectrum ℂ (opucResidualLinear p) := by
      rw [ContinuousLinearMap.spectrum_eq] at hz
      simpa [opucResidualCLM] using hz
    have heig : Module.End.HasEigenvalue (opucResidualLinear p) z :=
      Module.End.HasEigenvalue.of_mem_spectrum hzlin
    have hzroot := opucResidual_eigenvalue_isRoot p hp heig
    exact_mod_cast hroots z hzroot
  exact exists_pos_pow_norm_lt_one_of_spectralRadius_lt_one (opucResidualCLM p) hrho

theorem finiteToeplitzInner_add_left
    {N : ℕ} (c : ℤ → ℂ) (u v w : Fin (N + 1) → ℂ) :
    finiteToeplitzInner c (u + v) w =
      finiteToeplitzInner c u w + finiteToeplitzInner c v w := by
  simp [finiteToeplitzInner, dotProduct_add]

theorem finiteToeplitzInner_add_right
    {N : ℕ} (c : ℤ → ℂ) (u v w : Fin (N + 1) → ℂ) :
    finiteToeplitzInner c u (v + w) =
      finiteToeplitzInner c u v + finiteToeplitzInner c u w := by
  simp [finiteToeplitzInner, Matrix.mulVec_add, add_dotProduct]

theorem finiteToeplitzInner_smul_left
    {N : ℕ} (c : ℤ → ℂ) (a : ℂ) (u v : Fin (N + 1) → ℂ) :
    finiteToeplitzInner c (a • u) v =
      star a * finiteToeplitzInner c u v := by
  simp [finiteToeplitzInner, dotProduct_smul]

theorem finiteToeplitzInner_smul_right
    {N : ℕ} (c : ℤ → ℂ) (a : ℂ) (u v : Fin (N + 1) → ℂ) :
    finiteToeplitzInner c u (a • v) =
      a * finiteToeplitzInner c u v := by
  simp [finiteToeplitzInner, Matrix.mulVec_smul, smul_dotProduct]

/-- Open-disk root location contracts a cofinal arithmetic subsequence of feedback iterates on
every coefficient vector.  The arithmetic subsequence is all the reconstruction proof needs. -/
theorem opucResidual_contracting_subsequence
    {N : ℕ} (p : Fin (N + 2) → ℂ) (hp : p (Fin.last (N + 1)) ≠ 0)
    (hroots : ∀ z : ℂ, (Polynomial.ofFn (N + 2) p).IsRoot z → ‖z‖ < 1)
    (q : Fin (N + 1) → ℂ) :
    ∃ m : ℕ, 0 < m ∧
      Tendsto (fun n : ℕ => (((opucResidualCLM p) ^ m) ^ n) q)
        atTop (𝓝 0) := by
  obtain ⟨m, hm, hcontract⟩ :=
    opucResidual_exists_contracting_power p hp hroots
  refine ⟨m, hm, ?_⟩
  have hpow : Tendsto (fun n : ℕ => ((opucResidualCLM p) ^ m) ^ n)
      atTop (𝓝 0) := tendsto_pow_atTop_nhds_zero_of_norm_lt_one hcontract
  have happ := (((ContinuousLinearMap.apply ℂ (Fin (N + 1) → ℂ)) q).continuous.tendsto 0).comp hpow
  simpa only [Function.comp_apply, ContinuousLinearMap.apply_apply] using happ

/-- A normalized vector that is orthogonal to the head space in both arguments decomposes every
Toeplitz quadratic value into a scalar feedback energy and the residual quadratic value. -/
theorem finiteToeplitzInner_head_feedback_recurrence
    {N : ℕ} (c : ℤ → ℂ) (p : Fin (N + 2) → ℂ)
    (hp : p (Fin.last (N + 1)) ≠ 0)
    (hself : finiteToeplitzInner c p p = 1)
    (hleft : ∀ r : Fin (N + 1) → ℂ,
      finiteToeplitzInner c p (opucHead r) = 0)
    (hright : ∀ r : Fin (N + 1) → ℂ,
      finiteToeplitzInner c (opucHead r) p = 0)
    (q : Fin (N + 1) → ℂ) :
    finiteToeplitzInner c (opucHead q) (opucHead q) =
      (Complex.normSq (q (Fin.last N) / p (Fin.last (N + 1))) : ℂ) +
        finiteToeplitzInner c (opucHead (opucResidualLinear p q))
          (opucHead (opucResidualLinear p q)) := by
  let a : ℂ := q (Fin.last N) / p (Fin.last (N + 1))
  let r : Fin (N + 1) → ℂ := opucResidualLinear p q
  have hshift : finiteToeplitzInner c (opucTail q) (opucTail q) =
      finiteToeplitzInner c (opucHead q) (opucHead q) := by
    exact opucTail_gram_eq_opucHead_gram c q
  have hfeedback := opucTail_eq_feedback_add_head_residual p hp q
  rw [← hshift, hfeedback]
  change finiteToeplitzInner c (a • p + opucHead r) (a • p + opucHead r) = _
  rw [finiteToeplitzInner_add_left, finiteToeplitzInner_add_right,
    finiteToeplitzInner_add_right, finiteToeplitzInner_smul_left,
    finiteToeplitzInner_smul_right, finiteToeplitzInner_smul_left,
    finiteToeplitzInner_smul_right]
  rw [hself, hleft r, hright r]
  simp only [mul_one, mul_zero, add_zero, zero_add]
  change star a * a + finiteToeplitzInner c (opucHead r) (opucHead r) =
    (Complex.normSq a : ℂ) + finiteToeplitzInner c (opucHead r) (opucHead r)
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [starRingEnd_apply]

/-- Toeplitz shift invariance is sesquilinear, not merely quadratic. -/
theorem finiteToeplitzInner_tail_eq_head
    {N : ℕ} (c : ℤ → ℂ) (u v : Fin N → ℂ) :
    finiteToeplitzInner c (opucTail u) (opucTail v) =
      finiteToeplitzInner c (opucHead u) (opucHead v) := by
  let common : ℂ :=
    ∑ i : Fin N, (∑ j : Fin N, c ((i : ℤ) - (j : ℤ)) * v j) * star (u i)
  have htail : finiteToeplitzInner c (opucTail u) (opucTail v) = common := by
    simp only [finiteToeplitzInner, dotProduct, Matrix.mulVec, Pi.star_apply]
    simp_rw [Fin.sum_univ_succ]
    simp [circleToeplitzGram, opucTail, common]
  have hhead : finiteToeplitzInner c (opucHead u) (opucHead v) = common := by
    simp only [finiteToeplitzInner, dotProduct, Matrix.mulVec, Pi.star_apply]
    simp_rw [Fin.sum_univ_castSucc]
    simp [circleToeplitzGram, opucHead, common]
  exact htail.trans hhead.symm

/-- Full mixed-form feedback recurrence.  The scalar term depends only on the shared normalized
terminal vector, while all remaining information is pushed through the stable residual operator. -/
theorem finiteToeplitzInner_head_feedback_recurrence_mixed
    {N : ℕ} (c : ℤ → ℂ) (p : Fin (N + 2) → ℂ)
    (hp : p (Fin.last (N + 1)) ≠ 0)
    (hself : finiteToeplitzInner c p p = 1)
    (hleft : ∀ r : Fin (N + 1) → ℂ,
      finiteToeplitzInner c p (opucHead r) = 0)
    (hright : ∀ r : Fin (N + 1) → ℂ,
      finiteToeplitzInner c (opucHead r) p = 0)
    (u v : Fin (N + 1) → ℂ) :
    finiteToeplitzInner c (opucHead u) (opucHead v) =
      star (u (Fin.last N) / p (Fin.last (N + 1))) *
          (v (Fin.last N) / p (Fin.last (N + 1))) +
        finiteToeplitzInner c (opucHead (opucResidualLinear p u))
          (opucHead (opucResidualLinear p v)) := by
  let a : ℂ := u (Fin.last N) / p (Fin.last (N + 1))
  let b : ℂ := v (Fin.last N) / p (Fin.last (N + 1))
  let ru : Fin (N + 1) → ℂ := opucResidualLinear p u
  let rv : Fin (N + 1) → ℂ := opucResidualLinear p v
  have hshift := finiteToeplitzInner_tail_eq_head c u v
  have hu := opucTail_eq_feedback_add_head_residual p hp u
  have hv := opucTail_eq_feedback_add_head_residual p hp v
  rw [← hshift, hu, hv]
  change finiteToeplitzInner c (a • p + opucHead ru) (b • p + opucHead rv) = _
  rw [finiteToeplitzInner_add_left, finiteToeplitzInner_add_right,
    finiteToeplitzInner_add_right, finiteToeplitzInner_smul_left,
    finiteToeplitzInner_smul_right, finiteToeplitzInner_smul_left,
    finiteToeplitzInner_smul_right]
  rw [hself, hleft rv, hright ru]
  simp only [mul_one, mul_zero, add_zero, zero_add]
  rfl

/-- Difference of two Toeplitz forms restricted to the common head space. -/
def finiteToeplitzHeadDiff {N : ℕ} (c d : ℤ → ℂ)
    (u v : Fin (N + 1) → ℂ) : ℂ :=
  finiteToeplitzInner c (opucHead u) (opucHead v) -
    finiteToeplitzInner d (opucHead u) (opucHead v)

def opucHeadLinear {N : ℕ} :
    (Fin N → ℂ) →ₗ[ℂ] (Fin (N + 1) → ℂ) where
  toFun := opucHead
  map_add' u v := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [opucHead]
  map_smul' a u := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [opucHead]

@[fun_prop]
theorem continuous_opucHead {N : ℕ} :
    Continuous (opucHead : (Fin N → ℂ) → (Fin (N + 1) → ℂ)) := by
  exact (opucHeadLinear (N := N)).continuous_of_finiteDimensional

theorem continuous_finiteToeplitzHeadDiff
    {N : ℕ} (c d : ℤ → ℂ) :
    Continuous (fun x : (Fin (N + 1) → ℂ) × (Fin (N + 1) → ℂ) =>
      finiteToeplitzHeadDiff c d x.1 x.2) := by
  unfold finiteToeplitzHeadDiff finiteToeplitzInner Matrix.mulVec dotProduct
  fun_prop

/-- Two Toeplitz forms with the same normalized terminal vector have a feedback-invariant head
difference.  This is the algebraic conservation law that stability will force to vanish. -/
theorem finiteToeplitzHeadDiff_residual_invariant
    {N : ℕ} (c d : ℤ → ℂ) (p : Fin (N + 2) → ℂ)
    (hp : p (Fin.last (N + 1)) ≠ 0)
    (hselfc : finiteToeplitzInner c p p = 1)
    (hleftc : ∀ r : Fin (N + 1) → ℂ,
      finiteToeplitzInner c p (opucHead r) = 0)
    (hrightc : ∀ r : Fin (N + 1) → ℂ,
      finiteToeplitzInner c (opucHead r) p = 0)
    (hselfd : finiteToeplitzInner d p p = 1)
    (hleftd : ∀ r : Fin (N + 1) → ℂ,
      finiteToeplitzInner d p (opucHead r) = 0)
    (hrightd : ∀ r : Fin (N + 1) → ℂ,
      finiteToeplitzInner d (opucHead r) p = 0)
    (u v : Fin (N + 1) → ℂ) :
    finiteToeplitzHeadDiff c d u v =
      finiteToeplitzHeadDiff c d (opucResidualLinear p u)
        (opucResidualLinear p v) := by
  unfold finiteToeplitzHeadDiff
  rw [finiteToeplitzInner_head_feedback_recurrence_mixed c p hp hselfc hleftc hrightc,
    finiteToeplitzInner_head_feedback_recurrence_mixed d p hp hselfd hleftd hrightd]
  ring

theorem finiteToeplitzHeadDiff_residual_pow_invariant
    {N : ℕ} (c d : ℤ → ℂ) (p : Fin (N + 2) → ℂ)
    (hinv : ∀ u v : Fin (N + 1) → ℂ,
      finiteToeplitzHeadDiff c d u v =
        finiteToeplitzHeadDiff c d (opucResidualLinear p u)
          (opucResidualLinear p v))
    (n : ℕ) (u v : Fin (N + 1) → ℂ) :
    finiteToeplitzHeadDiff c d u v =
      finiteToeplitzHeadDiff c d (((opucResidualCLM p) ^ n) u)
        (((opucResidualCLM p) ^ n) v) := by
  induction n generalizing u v with
  | zero => simp
  | succ n ih =>
      calc
        finiteToeplitzHeadDiff c d u v =
            finiteToeplitzHeadDiff c d (opucResidualLinear p u)
              (opucResidualLinear p v) := hinv u v
        _ = finiteToeplitzHeadDiff c d
              (((opucResidualCLM p) ^ n) (opucResidualLinear p u))
              (((opucResidualCLM p) ^ n) (opucResidualLinear p v)) :=
          ih (opucResidualLinear p u) (opucResidualLinear p v)
        _ = finiteToeplitzHeadDiff c d (((opucResidualCLM p) ^ (n + 1)) u)
              (((opucResidualCLM p) ^ (n + 1)) v) := by
          simp only [pow_succ, ContinuousLinearMap.mul_apply,
            opucResidualCLM_apply]

/-- **Stable terminal uniqueness on the head space.**  A common normalized terminal vector with
all roots in the open disk determines the entire preceding sesquilinear Toeplitz form. -/
theorem finiteToeplitzHeadDiff_eq_zero_of_stable_terminal
    {N : ℕ} (c d : ℤ → ℂ) (p : Fin (N + 2) → ℂ)
    (hp : p (Fin.last (N + 1)) ≠ 0)
    (hroots : ∀ z : ℂ, (Polynomial.ofFn (N + 2) p).IsRoot z → ‖z‖ < 1)
    (hselfc : finiteToeplitzInner c p p = 1)
    (hleftc : ∀ r : Fin (N + 1) → ℂ,
      finiteToeplitzInner c p (opucHead r) = 0)
    (hrightc : ∀ r : Fin (N + 1) → ℂ,
      finiteToeplitzInner c (opucHead r) p = 0)
    (hselfd : finiteToeplitzInner d p p = 1)
    (hleftd : ∀ r : Fin (N + 1) → ℂ,
      finiteToeplitzInner d p (opucHead r) = 0)
    (hrightd : ∀ r : Fin (N + 1) → ℂ,
      finiteToeplitzInner d (opucHead r) p = 0)
    (u v : Fin (N + 1) → ℂ) :
    finiteToeplitzHeadDiff c d u v = 0 := by
  let T := opucResidualCLM p
  obtain ⟨m, hm, hcontract⟩ :=
    opucResidual_exists_contracting_power p hp hroots
  have hOp : Tendsto (fun n : ℕ => (T ^ m) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_norm_lt_one hcontract
  have hTu : Tendsto (fun n : ℕ => ((T ^ m) ^ n) u) atTop (𝓝 0) := by
    have happ := (((ContinuousLinearMap.apply ℂ (Fin (N + 1) → ℂ)) u).continuous.tendsto 0).comp hOp
    simpa only [Function.comp_apply, ContinuousLinearMap.apply_apply] using happ
  have hTv : Tendsto (fun n : ℕ => ((T ^ m) ^ n) v) atTop (𝓝 0) := by
    have happ := (((ContinuousLinearMap.apply ℂ (Fin (N + 1) → ℂ)) v).continuous.tendsto 0).comp hOp
    simpa only [Function.comp_apply, ContinuousLinearMap.apply_apply] using happ
  have hinv : ∀ x y : Fin (N + 1) → ℂ,
      finiteToeplitzHeadDiff c d x y =
        finiteToeplitzHeadDiff c d (opucResidualLinear p x)
          (opucResidualLinear p y) :=
    finiteToeplitzHeadDiff_residual_invariant c d p hp hselfc hleftc hrightc
      hselfd hleftd hrightd
  have hconst (n : ℕ) :
      finiteToeplitzHeadDiff c d (((T ^ m) ^ n) u) (((T ^ m) ^ n) v) =
        finiteToeplitzHeadDiff c d u v := by
    have hi := finiteToeplitzHeadDiff_residual_pow_invariant c d p hinv (m * n) u v
    simpa only [T, pow_mul] using hi.symm
  have hpair : Tendsto
      (fun n : ℕ => (((T ^ m) ^ n) u, ((T ^ m) ^ n) v)) atTop (𝓝 (0, 0)) :=
    by simpa only [nhds_prod_eq] using hTu.prodMk hTv
  have hlim := ((continuous_finiteToeplitzHeadDiff c d).tendsto (0, 0)).comp hpair
  have hzero : finiteToeplitzHeadDiff c d (0 : Fin (N + 1) → ℂ) 0 = 0 := by
    have hhead0 : opucHead (0 : Fin (N + 1) → ℂ) = 0 := by
      exact (opucHeadLinear (N := N + 1)).map_zero
    simp [finiteToeplitzHeadDiff, hhead0, finiteToeplitzInner]
  have hlim0 : Tendsto
      (fun n : ℕ => finiteToeplitzHeadDiff c d (((T ^ m) ^ n) u) (((T ^ m) ^ n) v))
      atTop (𝓝 0) := by
    simpa only [Prod.fst, Prod.snd, hzero] using hlim
  have hconstlim : Tendsto (fun _ : ℕ => finiteToeplitzHeadDiff c d u v)
      atTop (𝓝 0) :=
    hlim0.congr' (Filter.Eventually.of_forall hconst)
  exact tendsto_nhds_unique tendsto_const_nhds hconstlim

/-- The low-coordinate residual after removing the unique multiple of a terminal vector that
matches the last coordinate. -/
def terminalHeadResidual {N : ℕ} (p x : Fin (N + 2) → ℂ) :
    Fin (N + 1) → ℂ := fun i =>
  x i.castSucc - (x (Fin.last (N + 1)) / p (Fin.last (N + 1))) * p i.castSucc

theorem terminal_eq_smul_add_head_residual
    {N : ℕ} (p x : Fin (N + 2) → ℂ)
    (hp : p (Fin.last (N + 1)) ≠ 0) :
    x = (x (Fin.last (N + 1)) / p (Fin.last (N + 1))) • p +
      opucHead (terminalHeadResidual p x) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp [opucHead, hp]
  · simp [opucHead, terminalHeadResidual]

theorem finiteToeplitzInner_terminal_decomposition
    {N : ℕ} (c : ℤ → ℂ) (p : Fin (N + 2) → ℂ)
    (hp : p (Fin.last (N + 1)) ≠ 0)
    (hself : finiteToeplitzInner c p p = 1)
    (hleft : ∀ r : Fin (N + 1) → ℂ,
      finiteToeplitzInner c p (opucHead r) = 0)
    (hright : ∀ r : Fin (N + 1) → ℂ,
      finiteToeplitzInner c (opucHead r) p = 0)
    (x y : Fin (N + 2) → ℂ) :
    finiteToeplitzInner c x y =
      star (x (Fin.last (N + 1)) / p (Fin.last (N + 1))) *
          (y (Fin.last (N + 1)) / p (Fin.last (N + 1))) +
        finiteToeplitzInner c (opucHead (terminalHeadResidual p x))
          (opucHead (terminalHeadResidual p y)) := by
  let a : ℂ := x (Fin.last (N + 1)) / p (Fin.last (N + 1))
  let b : ℂ := y (Fin.last (N + 1)) / p (Fin.last (N + 1))
  let rx := terminalHeadResidual p x
  let ry := terminalHeadResidual p y
  conv_lhs =>
    rw [terminal_eq_smul_add_head_residual p x hp,
      terminal_eq_smul_add_head_residual p y hp]
  change finiteToeplitzInner c (a • p + opucHead rx) (b • p + opucHead ry) = _
  rw [finiteToeplitzInner_add_left, finiteToeplitzInner_add_right,
    finiteToeplitzInner_add_right, finiteToeplitzInner_smul_left,
    finiteToeplitzInner_smul_right, finiteToeplitzInner_smul_left,
    finiteToeplitzInner_smul_right]
  rw [hself, hleft ry, hright rx]
  simp only [mul_one, mul_zero, add_zero, zero_add]
  rfl

/-- **Stable terminal Toeplitz reconstruction.**  A stable normalized terminal polynomial and its
two-sided orthogonality data determine the complete finite Toeplitz sesquilinear form. -/
theorem finiteToeplitzInner_eq_of_stable_terminal
    {N : ℕ} (c d : ℤ → ℂ) (p : Fin (N + 2) → ℂ)
    (hp : p (Fin.last (N + 1)) ≠ 0)
    (hroots : ∀ z : ℂ, (Polynomial.ofFn (N + 2) p).IsRoot z → ‖z‖ < 1)
    (hselfc : finiteToeplitzInner c p p = 1)
    (hleftc : ∀ r : Fin (N + 1) → ℂ,
      finiteToeplitzInner c p (opucHead r) = 0)
    (hrightc : ∀ r : Fin (N + 1) → ℂ,
      finiteToeplitzInner c (opucHead r) p = 0)
    (hselfd : finiteToeplitzInner d p p = 1)
    (hleftd : ∀ r : Fin (N + 1) → ℂ,
      finiteToeplitzInner d p (opucHead r) = 0)
    (hrightd : ∀ r : Fin (N + 1) → ℂ,
      finiteToeplitzInner d (opucHead r) p = 0)
    (x y : Fin (N + 2) → ℂ) :
    finiteToeplitzInner c x y = finiteToeplitzInner d x y := by
  rw [finiteToeplitzInner_terminal_decomposition c p hp hselfc hleftc hrightc,
    finiteToeplitzInner_terminal_decomposition d p hp hselfd hleftd hrightd]
  have hhead := finiteToeplitzHeadDiff_eq_zero_of_stable_terminal c d p hp hroots
    hselfc hleftc hrightc hselfd hleftd hrightd
    (terminalHeadResidual p x) (terminalHeadResidual p y)
  unfold finiteToeplitzHeadDiff at hhead
  rw [sub_eq_zero.mp hhead]

theorem circleToeplitzGram_eq_of_stable_terminal
    {N : ℕ} (c d : ℤ → ℂ) (p : Fin (N + 2) → ℂ)
    (hp : p (Fin.last (N + 1)) ≠ 0)
    (hroots : ∀ z : ℂ, (Polynomial.ofFn (N + 2) p).IsRoot z → ‖z‖ < 1)
    (hselfc : finiteToeplitzInner c p p = 1)
    (hleftc : ∀ r : Fin (N + 1) → ℂ,
      finiteToeplitzInner c p (opucHead r) = 0)
    (hrightc : ∀ r : Fin (N + 1) → ℂ,
      finiteToeplitzInner c (opucHead r) p = 0)
    (hselfd : finiteToeplitzInner d p p = 1)
    (hleftd : ∀ r : Fin (N + 1) → ℂ,
      finiteToeplitzInner d p (opucHead r) = 0)
    (hrightd : ∀ r : Fin (N + 1) → ℂ,
      finiteToeplitzInner d (opucHead r) p = 0) :
    circleToeplitzGram (N + 1) c = circleToeplitzGram (N + 1) d := by
  ext i j
  have hform := finiteToeplitzInner_eq_of_stable_terminal c d p hp hroots
    hselfc hleftc hrightc hselfd hleftd hrightd
    (Pi.single i 1) (Pi.single j 1)
  simpa [finiteToeplitzInner, Matrix.mulVec, dotProduct, Pi.single_apply] using hform

/-- Hermitian symmetry supplies the reverse orthogonality of the original finite OPUC vector. -/
theorem finiteOPUCVector_head_inner
    {N : ℕ} (c : ℤ → ℂ) (hG : (circleToeplitzGram N c).PosDef)
    (q : Fin N → ℂ) :
    finiteToeplitzInner c (opucHead q) (finiteOPUCVector c hG) = 0 := by
  let normInst := Matrix.toNormedAddCommGroup (circleToeplitzGram N c) hG
  letI : NormedAddCommGroup (Fin (N + 1) → ℂ) := normInst
  letI : SeminormedAddCommGroup (Fin (N + 1) → ℂ) :=
    normInst.toSeminormedAddCommGroup
  letI := Matrix.toInnerProductSpace (circleToeplitzGram N c) hG.posSemidef
  change inner ℂ (opucHead q) (finiteOPUCVector c hG) = 0
  calc
    inner ℂ (opucHead q) (finiteOPUCVector c hG) =
        star (inner ℂ (finiteOPUCVector c hG) (opucHead q)) := by
      simpa only [starRingEnd_apply] using
        (inner_conj_symm (opucHead q) (finiteOPUCVector c hG)).symm
    _ = 0 := by
      change star (finiteToeplitzInner c (finiteOPUCVector c hG) (opucHead q)) = 0
      rw [finiteOPUCVector_inner_head]
      simp

theorem continuous_finiteCoefficientPolynomialEval
    {N : ℕ} (u : Fin (N + 1) → ℂ) :
    Continuous (finiteCoefficientPolynomialEval u) := by
  unfold finiteCoefficientPolynomialEval
  fun_prop

theorem bernsteinSzego_form_circleIntegrable
    {N : ℕ} (c : ℤ → ℂ) (hG : (circleToeplitzGram N c).PosDef)
    (u v : Fin (N + 1) → ℂ) :
    CircleIntegrable
      (fun z : ℂ => finiteCoefficientPolynomialEval v z *
        star (finiteCoefficientPolynomialEval u z) *
        bernsteinSzegoComplexWeight c hG z) 0 1 := by
  apply ContinuousOn.circleIntegrable zero_le_one
  exact (((continuous_finiteCoefficientPolynomialEval v).continuousOn.mul
    (continuous_star.comp
      (continuous_finiteCoefficientPolynomialEval u)).continuousOn).mul
        (bernsteinSzegoComplexWeight_continuousOn_sphere c hG))

/-- The Bernstein--Szegő moment form is Hermitian, proved directly from its positive real boundary
weight rather than from a positivity theorem. -/
theorem finiteToeplitzInner_bernsteinSzegoMoment_conj_symm
    {N : ℕ} (c : ℤ → ℂ) (hG : (circleToeplitzGram N c).PosDef)
    (u v : Fin (N + 1) → ℂ) :
    star (finiteToeplitzInner (bernsteinSzegoMoment c hG) u v) =
      finiteToeplitzInner (bernsteinSzegoMoment c hG) v u := by
  let f : ℂ → ℂ := fun z => finiteCoefficientPolynomialEval v z *
    star (finiteCoefficientPolynomialEval u z) * bernsteinSzegoComplexWeight c hG z
  have hf : CircleIntegrable f 0 1 :=
    bernsteinSzego_form_circleIntegrable c hG u v
  have hcomm := (Complex.conjCLE : ℂ →L[ℝ] ℂ).circleAverage_comp_comm hf
  calc
    star (finiteToeplitzInner (bernsteinSzegoMoment c hG) u v) =
        star (Real.circleAverage f 0 1) := by
      exact congrArg star (finiteToeplitzInner_bernsteinSzegoMoment c hG u v)
    _ =
        (Complex.conjCLE : ℂ →L[ℝ] ℂ) (Real.circleAverage f 0 1) := by
      change star (Real.circleAverage f 0 1) = star (Real.circleAverage f 0 1)
      rfl
    _ = Real.circleAverage ((Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ f) 0 1 :=
      hcomm.symm
    _ = Real.circleAverage
        (fun z : ℂ => finiteCoefficientPolynomialEval u z *
          star (finiteCoefficientPolynomialEval v z) *
          bernsteinSzegoComplexWeight c hG z) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro z hz
      change star (finiteCoefficientPolynomialEval v z *
        star (finiteCoefficientPolynomialEval u z) *
        bernsteinSzegoComplexWeight c hG z) = _
      have hw : star (bernsteinSzegoComplexWeight c hG z) =
          bernsteinSzegoComplexWeight c hG z := by
        simp [bernsteinSzegoComplexWeight]
      rw [star_mul, star_mul, star_star, hw]
      ring
    _ = finiteToeplitzInner (bernsteinSzegoMoment c hG) v u := by
      exact (finiteToeplitzInner_bernsteinSzegoMoment c hG v u).symm

/-- Reverse orthogonality for the Bernstein--Szegő model. -/
theorem finiteToeplitzInner_bernsteinSzegoMoment_vector_head_zero
    {N : ℕ} (c : ℤ → ℂ) (hG : (circleToeplitzGram N c).PosDef)
    (q : Fin N → ℂ) :
    finiteToeplitzInner (bernsteinSzegoMoment c hG)
      (finiteOPUCVector c hG) (opucHead q) = 0 := by
  calc
    finiteToeplitzInner (bernsteinSzegoMoment c hG)
        (finiteOPUCVector c hG) (opucHead q) =
      star (finiteToeplitzInner (bernsteinSzegoMoment c hG)
        (opucHead q) (finiteOPUCVector c hG)) :=
      (finiteToeplitzInner_bernsteinSzegoMoment_conj_symm c hG
        (opucHead q) (finiteOPUCVector c hG)).symm
    _ = 0 := by
      rw [finiteToeplitzInner_bernsteinSzegoMoment_head_zero]
      simp

/-- **Exact Bernstein--Szegő prefix reconstruction.**  The reciprocal-square stable density built
from the terminal OPUC vector reproduces the complete Toeplitz section from which that vector was
constructed.  No limiting approximation theorem is used. -/
theorem circleToeplitzGram_bernsteinSzegoMoment_eq
    {N : ℕ} (c : ℤ → ℂ) (hG : (circleToeplitzGram (N + 1) c).PosDef) :
    circleToeplitzGram (N + 1) (bernsteinSzegoMoment c hG) =
      circleToeplitzGram (N + 1) c := by
  let p : Fin (N + 2) → ℂ := finiteOPUCVector c hG
  symm
  apply circleToeplitzGram_eq_of_stable_terminal c
    (bernsteinSzegoMoment c hG) p
  · exact finiteOPUCVector_last_ne_zero c hG
  · intro z hz
    apply finiteOPUCPolynomial_isRoot_norm_lt_one c hG
    simpa [p, finiteOPUCPolynomial] using hz
  · exact finiteOPUCVector_inner_self c hG
  · exact finiteOPUCVector_inner_head c hG
  · exact finiteOPUCVector_head_inner c hG
  · exact finiteToeplitzInner_bernsteinSzegoMoment_self c hG
  · exact finiteToeplitzInner_bernsteinSzegoMoment_vector_head_zero c hG
  · exact finiteToeplitzInner_bernsteinSzegoMoment_head_zero c hG

/-- Positive and negative Fourier coefficients in the full finite prefix are reproduced exactly. -/
theorem bernsteinSzegoMoment_prefix
    {N : ℕ} (c : ℤ → ℂ) (hG : (circleToeplitzGram (N + 1) c).PosDef)
    (k : Fin (N + 2)) :
    bernsteinSzegoMoment c hG (k : ℤ) = c (k : ℤ) ∧
      bernsteinSzegoMoment c hG (-(k : ℤ)) = c (-(k : ℤ)) := by
  have hmatrix := circleToeplitzGram_bernsteinSzegoMoment_eq c hG
  constructor
  · have hentry := congrFun (congrFun hmatrix k) (0 : Fin (N + 2))
    simpa [circleToeplitzGram] using hentry
  · have hentry := congrFun (congrFun hmatrix (0 : Fin (N + 2))) k
    simpa [circleToeplitzGram] using hentry

end
end GaloisForLFunctions.HTGeometry

