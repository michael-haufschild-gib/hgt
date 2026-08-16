import GaloisForLFunctions.HTGeometry.EndpointProbeTransitionCriterion
import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Data.Finset.Sym

/-!
# One probe that sees every transition

Endpoint completeness delivers, for each ordered pair of levels, *some* probe of a finite family
with a nonzero matrix element.  A single edge coupling, however, is one operator.  A generic
complex combination of the family works: each matrix element is a nonzero linear form in the
combination coefficients, the product of those forms over all ordered pairs is a nonzero
polynomial, and a nonzero polynomial over `ℂ` has a point where it does not vanish.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A]

/-- The linear form recording one matrix element of a combination of probes. -/
def probeCombinationForm (M : S → Matrix A A ℂ) (α β : A) : MvPolynomial S ℂ :=
  ∑ s, MvPolynomial.C (M s α β) * MvPolynomial.X s

omit [Fintype A] [DecidableEq A] in
theorem eval_probeCombinationForm (M : S → Matrix A A ℂ) (α β : A) (t : S → ℂ) :
    MvPolynomial.eval t (probeCombinationForm M α β) = ∑ s, t s * M s α β := by
  simp only [probeCombinationForm, map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X]
  exact Finset.sum_congr rfl fun s _ => by ring

omit [Fintype A] [DecidableEq A] in
theorem probeCombinationForm_ne_zero {M : S → Matrix A A ℂ} {α β : A}
    (h : ∃ s, M s α β ≠ 0) : probeCombinationForm M α β ≠ 0 := by
  classical
  obtain ⟨s₀, hs₀⟩ := h
  intro hzero
  have heval := congrArg (MvPolynomial.eval (fun s => if s = s₀ then (1 : ℂ) else 0)) hzero
  rw [eval_probeCombinationForm] at heval
  have hval : (∑ s, (if s = s₀ then (1 : ℂ) else 0) * M s α β) = M s₀ α β := by simp
  rw [hval] at heval
  simpa using hs₀ (by simpa using heval)

omit [DecidableEq A] in
/-- **A single probe that sees every ordered pair.**  A generic complex combination of a covering
probe family has every off-diagonal matrix element nonzero. -/
theorem exists_probeCombination_ne_zero (M : S → Matrix A A ℂ)
    (hcover : ∀ α β : A, α ≠ β → ∃ s, M s α β ≠ 0) :
    ∃ t : S → ℂ, ∀ α β : A, α ≠ β → (∑ s, t s • M s) α β ≠ 0 := by
  classical
  set Q : MvPolynomial S ℂ :=
    ∏ p ∈ (Finset.univ : Finset A).offDiag, probeCombinationForm M p.1 p.2 with hQ
  have hQne : Q ≠ 0 := by
    rw [hQ]
    refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
    have hne : p.1 ≠ p.2 := (Finset.mem_offDiag.mp hp).2.2
    exact probeCombinationForm_ne_zero (hcover p.1 p.2 hne)
  obtain ⟨t, ht⟩ : ∃ t : S → ℂ, MvPolynomial.eval t Q ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hQne (MvPolynomial.funext fun x => by simpa using hcon x)
  refine ⟨t, fun α β hαβ => ?_⟩
  have hmem : (α, β) ∈ (Finset.univ : Finset A).offDiag :=
    Finset.mem_offDiag.mpr ⟨Finset.mem_univ α, Finset.mem_univ β, hαβ⟩
  have hfac : MvPolynomial.eval t (probeCombinationForm M α β) ≠ 0 := by
    intro hz
    apply ht
    rw [hQ, map_prod]
    exact Finset.prod_eq_zero hmem hz
  rw [eval_probeCombinationForm] at hfac
  have hentry : (∑ s, t s • M s) α β = ∑ s, t s * M s α β := by
    rw [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun s _ => by simp
  rw [hentry]
  exact hfac

/-! ## From endpoint completeness to one covering endpoint operator -/

variable {c d : Type*} [Fintype c] [DecidableEq c] [Fintype d]

omit [DecidableEq c] in
theorem endpointPairing_sum_probe {ι : Type*} [Fintype ι] (X : ι → Matrix c c ℂ) (t : ι → ℂ)
    (ψ φ : c × d → ℂ) :
    endpointPairing ψ (endpointProbeAction (∑ q, t q • X q) φ)
      = ∑ q, t q * endpointPairing ψ (endpointProbeAction (X q) φ) := by
  rw [endpointPairing_probe_eq_trace, Finset.sum_mul, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Matrix.smul_mul, Matrix.trace_smul, smul_eq_mul, endpointPairing_probe_eq_trace]

/-- **From endpoint completeness to one covering endpoint operator.**  If every ordered pair of a
finite vector family has nonzero reduced transition, one endpoint operator pairs every ordered
pair nontrivially. -/
theorem exists_covering_endpoint_probe {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : ι → c × d → ℂ)
    (hne : ∀ i j : ι, i ≠ j → reducedTransition (ψ i) (ψ j) ≠ 0) :
    ∃ X : Matrix c c ℂ, ∀ i j : ι, i ≠ j →
      endpointPairing (ψ i) (endpointProbeAction X (ψ j)) ≠ 0 := by
  classical
  -- one Hermitian probe per ordered pair
  have hchoice : ∀ q : ι × ι, ∃ X : Matrix c c ℂ, q.1 ≠ q.2 →
      endpointPairing (ψ q.1) (endpointProbeAction X (ψ q.2)) ≠ 0 := by
    intro q
    by_cases hq : q.1 = q.2
    · exact ⟨0, fun hcon => absurd hq hcon⟩
    · obtain ⟨X, -, hX⟩ := exists_hermitian_endpointProbe_ne_zero (ψ q.1) (ψ q.2) (hne q.1 q.2 hq)
      exact ⟨X, fun _ => hX⟩
  choose Xfam hXfam using hchoice
  -- the pairing matrix of each probe
  set N : (ι × ι) → Matrix ι ι ℂ :=
    fun q => Matrix.of fun i j => endpointPairing (ψ i) (endpointProbeAction (Xfam q) (ψ j))
    with hN
  have hcover : ∀ i j : ι, i ≠ j → ∃ q, N q i j ≠ 0 := by
    intro i j hij
    exact ⟨(i, j), hXfam (i, j) hij⟩
  obtain ⟨t, ht⟩ := exists_probeCombination_ne_zero N hcover
  refine ⟨∑ q, t q • Xfam q, fun i j hij => ?_⟩
  have hval : endpointPairing (ψ i) (endpointProbeAction (∑ q, t q • Xfam q) (ψ j))
      = (∑ q, t q • N q) i j := by
    rw [endpointPairing_sum_probe, Matrix.sum_apply]
    exact Finset.sum_congr rfl fun q _ => by simp [hN]
  rw [hval]
  exact ht i j hij

end

end GaloisForLFunctions.HTGeometry
