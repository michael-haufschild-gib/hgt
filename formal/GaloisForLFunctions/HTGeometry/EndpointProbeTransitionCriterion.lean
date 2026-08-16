import Mathlib.Data.Matrix.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

/-!
# When every one-site probe is blind to a transition

A probe supported on one tensor factor pairs two vectors only through their *reduced* transition
operator: for every operator `X` on the endpoint factor,

`⟨ψ, (X ⊗ 1) φ⟩ = Tr (X · R)`,   `R j i = ∑_k φ(j,k) conj(ψ(i,k))`.

Hence all endpoint probes annihilate the pair exactly when `R = 0`, and if `R ≠ 0` an explicitly
Hermitian probe already sees the pair.  This is the criterion behind endpoint completeness: the
failure of every endpoint probe on a pair of eigenvectors is the vanishing of one reduced
operator, and Hermitian probes are no weaker than arbitrary ones.
-/

open Matrix
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b]

/-- The reduced transition operator of a pair of vectors on a bipartite index. -/
def reducedTransition (ψ φ : a × b → ℂ) : Matrix a a ℂ :=
  Matrix.of fun j i => ∑ k, φ (j, k) * (starRingEnd ℂ) (ψ (i, k))

/-- A probe supported on the first tensor factor. -/
def endpointProbeAction (X : Matrix a a ℂ) (φ : a × b → ℂ) : a × b → ℂ :=
  fun p => ∑ j, X p.1 j * φ (j, p.2)

/-- The Hermitian pairing of two vectors. -/
def endpointPairing (ψ φ : a × b → ℂ) : ℂ := ∑ p, (starRingEnd ℂ) (ψ p) * φ p

omit [DecidableEq a] in
/-- **Endpoint probes pair only through the reduced operator.** -/
theorem endpointPairing_probe_eq_trace (X : Matrix a a ℂ) (ψ φ : a × b → ℂ) :
    endpointPairing ψ (endpointProbeAction X φ) = (X * reducedTransition ψ φ).trace := by
  classical
  rw [endpointPairing, Matrix.trace, Fintype.sum_prod_type]
  simp only [Matrix.diag_apply, Matrix.mul_apply, reducedTransition, Matrix.of_apply,
    endpointProbeAction]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hL : (∑ k, (starRingEnd ℂ) (ψ (i, k)) * ∑ j, X i j * φ (j, k))
      = ∑ k, ∑ j, (starRingEnd ℂ) (ψ (i, k)) * (X i j * φ (j, k)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
  have hR : (∑ j, X i j * ∑ k, φ (j, k) * (starRingEnd ℂ) (ψ (i, k)))
      = ∑ j, ∑ k, (starRingEnd ℂ) (ψ (i, k)) * (X i j * φ (j, k)) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [hL, hR, Finset.sum_comm]

/-! ## Explicit probes -/

/-- The elementary matrix unit. -/
def unitProbe (i₀ j₀ : a) : Matrix a a ℂ :=
  Matrix.of fun x y => if x = i₀ ∧ y = j₀ then 1 else 0

theorem trace_unitProbe_mul (i₀ j₀ : a) (R : Matrix a a ℂ) :
    (unitProbe i₀ j₀ * R).trace = R j₀ i₀ := by
  classical
  rw [Matrix.trace]
  simp only [Matrix.diag_apply, Matrix.mul_apply, unitProbe, Matrix.of_apply]
  rw [Finset.sum_eq_single i₀]
  · rw [Finset.sum_eq_single j₀]
    · simp
    · intro j _ hj
      simp [hj]
    · intro h
      exact absurd (Finset.mem_univ j₀) h
  · intro i _ hi
    refine Finset.sum_eq_zero fun j _ => ?_
    simp [hi]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

omit [Fintype a] in
theorem conjTranspose_unitProbe (i₀ j₀ : a) :
    (unitProbe i₀ j₀ : Matrix a a ℂ)ᴴ = unitProbe j₀ i₀ := by
  ext x y
  simp only [Matrix.conjTranspose_apply, unitProbe, Matrix.of_apply]
  by_cases h : y = i₀ ∧ x = j₀
  · simp [h]
  · have h' : ¬ (x = j₀ ∧ y = i₀) := fun hc => h ⟨hc.2, hc.1⟩
    simp [h, h']

/-- The symmetric Hermitian probe on one pair of endpoint levels. -/
def symmetricProbe (i₀ j₀ : a) : Matrix a a ℂ := unitProbe i₀ j₀ + unitProbe j₀ i₀

/-- The skew-built Hermitian probe on one pair of endpoint levels. -/
def skewProbe (i₀ j₀ : a) : Matrix a a ℂ :=
  Complex.I • unitProbe i₀ j₀ - Complex.I • unitProbe j₀ i₀

omit [Fintype a] in
theorem symmetricProbe_isHermitian (i₀ j₀ : a) : (symmetricProbe i₀ j₀).IsHermitian := by
  unfold Matrix.IsHermitian symmetricProbe
  rw [Matrix.conjTranspose_add, conjTranspose_unitProbe, conjTranspose_unitProbe, add_comm]

omit [Fintype a] in
theorem skewProbe_isHermitian (i₀ j₀ : a) : (skewProbe i₀ j₀).IsHermitian := by
  unfold Matrix.IsHermitian skewProbe
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul,
    conjTranspose_unitProbe, conjTranspose_unitProbe]
  have hstar : (star Complex.I : ℂ) = -Complex.I := by simp
  rw [hstar]
  module

theorem trace_symmetricProbe_mul (i₀ j₀ : a) (R : Matrix a a ℂ) :
    (symmetricProbe i₀ j₀ * R).trace = R j₀ i₀ + R i₀ j₀ := by
  rw [symmetricProbe, Matrix.add_mul, Matrix.trace_add, trace_unitProbe_mul, trace_unitProbe_mul]

theorem trace_skewProbe_mul (i₀ j₀ : a) (R : Matrix a a ℂ) :
    (skewProbe i₀ j₀ * R).trace = Complex.I * (R j₀ i₀ - R i₀ j₀) := by
  rw [skewProbe, Matrix.sub_mul, Matrix.trace_sub, Matrix.smul_mul, Matrix.smul_mul,
    Matrix.trace_smul, Matrix.trace_smul, trace_unitProbe_mul, trace_unitProbe_mul]
  simp only [smul_eq_mul]
  ring

/-! ## The criterion -/

/-- **A nonzero reduced operator is already seen by an explicit Hermitian endpoint probe.** -/
theorem exists_hermitian_endpointProbe_ne_zero (ψ φ : a × b → ℂ)
    (h : reducedTransition ψ φ ≠ 0) :
    ∃ X : Matrix a a ℂ, X.IsHermitian ∧ endpointPairing ψ (endpointProbeAction X φ) ≠ 0 := by
  classical
  obtain ⟨j₀, i₀, hji⟩ : ∃ j i, reducedTransition ψ φ j i ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact h (by ext j i; simpa using hcon j i)
  by_cases hsym : endpointPairing ψ (endpointProbeAction (symmetricProbe i₀ j₀) φ) = 0
  · refine ⟨skewProbe i₀ j₀, skewProbe_isHermitian i₀ j₀, ?_⟩
    intro hskew
    rw [endpointPairing_probe_eq_trace, trace_symmetricProbe_mul] at hsym
    rw [endpointPairing_probe_eq_trace, trace_skewProbe_mul] at hskew
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have hdiff : reducedTransition ψ φ j₀ i₀ - reducedTransition ψ φ i₀ j₀ = 0 :=
      (mul_eq_zero.mp hskew).resolve_left hI
    have : (2 : ℂ) * reducedTransition ψ φ j₀ i₀ = 0 := by linear_combination hsym + hdiff
    have h2 : (2 : ℂ) ≠ 0 := by norm_num
    exact hji ((mul_eq_zero.mp this).resolve_left h2)
  · exact ⟨symmetricProbe i₀ j₀, symmetricProbe_isHermitian i₀ j₀, hsym⟩

/-- **The endpoint blindness criterion.**  Every Hermitian endpoint probe annihilates a pair of
vectors exactly when their reduced transition operator vanishes. -/
theorem reducedTransition_eq_zero_iff (ψ φ : a × b → ℂ) :
    reducedTransition ψ φ = 0 ↔
      ∀ X : Matrix a a ℂ, X.IsHermitian → endpointPairing ψ (endpointProbeAction X φ) = 0 := by
  constructor
  · intro hzero X _
    rw [endpointPairing_probe_eq_trace, hzero, Matrix.mul_zero, Matrix.trace_zero]
  · intro hall
    by_contra hne
    obtain ⟨X, hX, hXne⟩ := exists_hermitian_endpointProbe_ne_zero ψ φ hne
    exact hXne (hall X hX)

end

end GaloisForLFunctions.HTGeometry
