/-
# One Hermitian endpoint probe that sees every ordered pair

Endpoint completeness supplies, for each ordered pair of an eigenvector family, *some* Hermitian
probe with nonzero pairing.  A single probe seeing every pair at once is a generic combination of
those -- but the combination must have **real** coefficients, or Hermiticity is lost, and
Hermiticity is what makes the induced transition channel Hermitian and its residual energy
positive.

The real genericity is the same polynomial argument run over the reals: the squared modulus of a
real combination of complex numbers is a real polynomial in the coefficients, nonzero as soon as one
of the numbers is, and a finite product of nonzero real polynomials is nonzero, hence nonzero at
some real point.

Main results:
* `exists_realProbeCombination_ne_zero` — a real generic combination of a covering family.
* `exists_hermitian_covering_endpoint_probe` — one Hermitian probe for all ordered pairs.
* `endpointChannel`, `isHermitian_endpointChannel`, `endpointChannel_ne_zero` — the transition
  channel of an endpoint-complete family, Hermitian with every off-diagonal entry nonzero.
-/
import GaloisForLFunctions.HTGeometry.CompleteProbeCombination

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

section RealCombination

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq A]

/-- The squared modulus of one matrix element of a real combination of probes. -/
def realProbeModulusForm (M : S → Matrix A A ℂ) (α β : A) : MvPolynomial S ℝ :=
  (∑ s, MvPolynomial.C (M s α β).re * MvPolynomial.X s) ^ (2 : ℕ)
    + (∑ s, MvPolynomial.C (M s α β).im * MvPolynomial.X s) ^ (2 : ℕ)

omit [Fintype A] [DecidableEq A] in
theorem eval_realProbeModulusForm (M : S → Matrix A A ℂ) (α β : A) (t : S → ℝ) :
    MvPolynomial.eval t (realProbeModulusForm M α β)
      = Complex.normSq (∑ s, (t s : ℂ) * M s α β) := by
  have hre : (∑ s, (t s : ℂ) * M s α β).re = ∑ s, t s * (M s α β).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun s _ => by simp
  have him : (∑ s, (t s : ℂ) * M s α β).im = ∑ s, t s * (M s α β).im := by
    rw [Complex.im_sum]
    exact Finset.sum_congr rfl fun s _ => by simp
  rw [realProbeModulusForm, Complex.normSq_apply, hre, him]
  simp only [map_add, map_pow, map_sum, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X]
  have h1 : (∑ s, (M s α β).re * t s) = ∑ s, t s * (M s α β).re :=
    Finset.sum_congr rfl fun s _ => by ring
  have h2 : (∑ s, (M s α β).im * t s) = ∑ s, t s * (M s α β).im :=
    Finset.sum_congr rfl fun s _ => by ring
  rw [h1, h2]
  ring

omit [Fintype A] [DecidableEq A] in
theorem realProbeModulusForm_ne_zero {M : S → Matrix A A ℂ} {α β : A}
    (h : ∃ s, M s α β ≠ 0) : realProbeModulusForm M α β ≠ 0 := by
  classical
  obtain ⟨s₀, hs₀⟩ := h
  intro hzero
  have heval := congrArg (MvPolynomial.eval (fun s => if s = s₀ then (1 : ℝ) else 0)) hzero
  rw [eval_realProbeModulusForm] at heval
  have hval : (∑ s, ((if s = s₀ then (1 : ℝ) else 0 : ℝ) : ℂ) * M s α β) = M s₀ α β := by
    rw [Finset.sum_eq_single s₀]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ s₀) h
  rw [hval] at heval
  simp only [map_zero] at heval
  exact hs₀ (Complex.normSq_eq_zero.mp heval)

omit [DecidableEq A] in
/-- **A single real combination that sees every ordered pair.** -/
theorem exists_realProbeCombination_ne_zero (M : S → Matrix A A ℂ)
    (hcover : ∀ α β : A, α ≠ β → ∃ s, M s α β ≠ 0) :
    ∃ t : S → ℝ, ∀ α β : A, α ≠ β → (∑ s, (t s : ℂ) • M s) α β ≠ 0 := by
  classical
  set Q : MvPolynomial S ℝ :=
    ∏ p ∈ (Finset.univ : Finset A).offDiag, realProbeModulusForm M p.1 p.2 with hQ
  have hQne : Q ≠ 0 := by
    rw [hQ]
    refine Finset.prod_ne_zero_iff.mpr fun p hp => ?_
    exact realProbeModulusForm_ne_zero (hcover p.1 p.2 (Finset.mem_offDiag.mp hp).2.2)
  obtain ⟨t, ht⟩ : ∃ t : S → ℝ, MvPolynomial.eval t Q ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    exact hQne (MvPolynomial.funext fun x => by simpa using hcon x)
  refine ⟨t, fun α β hαβ => ?_⟩
  have hmem : (α, β) ∈ (Finset.univ : Finset A).offDiag :=
    Finset.mem_offDiag.mpr ⟨Finset.mem_univ α, Finset.mem_univ β, hαβ⟩
  have hfac : MvPolynomial.eval t (realProbeModulusForm M α β) ≠ 0 := by
    intro hz
    exact ht (by rw [hQ, map_prod]; exact Finset.prod_eq_zero hmem hz)
  rw [eval_realProbeModulusForm] at hfac
  have hentry : (∑ s, (t s : ℂ) • M s) α β = ∑ s, (t s : ℂ) * M s α β := by
    rw [Matrix.sum_apply]
    exact Finset.sum_congr rfl fun s _ => by simp
  rw [hentry]
  intro hz
  exact hfac (by rw [hz]; simp)

end RealCombination

section Probe

variable {c d : Type*} [Fintype c] [DecidableEq c] [Fintype d]

omit [Fintype c] [DecidableEq c] in
theorem reducedTransition_conjTranspose (ψ φ : c × d → ℂ) :
    (reducedTransition ψ φ)ᴴ = reducedTransition φ ψ := by
  ext i j
  simp only [Matrix.conjTranspose_apply, reducedTransition, Matrix.of_apply]
  rw [star_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [star_mul']
  simp [mul_comm]

/-- **One Hermitian probe that sees every ordered pair.** -/
theorem exists_hermitian_covering_endpoint_probe {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ψ : ι → c × d → ℂ)
    (hne : ∀ i j : ι, i ≠ j → reducedTransition (ψ i) (ψ j) ≠ 0) :
    ∃ X : Matrix c c ℂ, X.IsHermitian ∧ ∀ i j : ι, i ≠ j →
      endpointPairing (ψ i) (endpointProbeAction X (ψ j)) ≠ 0 := by
  classical
  have hchoice : ∀ q : ι × ι, ∃ X : Matrix c c ℂ, X.IsHermitian ∧ (q.1 ≠ q.2 →
      endpointPairing (ψ q.1) (endpointProbeAction X (ψ q.2)) ≠ 0) := by
    intro q
    by_cases hq : q.1 = q.2
    · exact ⟨0, Matrix.isHermitian_zero, fun hcon => absurd hq hcon⟩
    · obtain ⟨X, hXh, hX⟩ := exists_hermitian_endpointProbe_ne_zero (ψ q.1) (ψ q.2) (hne q.1 q.2 hq)
      exact ⟨X, hXh, fun _ => hX⟩
  choose Xfam hXherm hXfam using hchoice
  set N : (ι × ι) → Matrix ι ι ℂ :=
    fun q => Matrix.of fun i j => endpointPairing (ψ i) (endpointProbeAction (Xfam q) (ψ j))
    with hN
  have hcover : ∀ i j : ι, i ≠ j → ∃ q, N q i j ≠ 0 := fun i j hij => ⟨(i, j), hXfam (i, j) hij⟩
  obtain ⟨t, ht⟩ := exists_realProbeCombination_ne_zero N hcover
  refine ⟨∑ q, (t q : ℂ) • Xfam q, ?_, fun i j hij => ?_⟩
  · show (∑ q, (t q : ℂ) • Xfam q)ᴴ = ∑ q, (t q : ℂ) • Xfam q
    rw [Matrix.conjTranspose_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [Matrix.conjTranspose_smul, hXherm q]
    congr 1
    simp
  · have hval : endpointPairing (ψ i) (endpointProbeAction (∑ q, (t q : ℂ) • Xfam q) (ψ j))
        = (∑ q, (t q : ℂ) • N q) i j := by
      rw [endpointPairing_sum_probe, Matrix.sum_apply]
      exact Finset.sum_congr rfl fun q _ => by simp [hN]
    rw [hval]
    exact ht i j hij

/-- The transition channel of an eigenvector family in its own labelling. -/
def endpointChannel {ι : Type*} (ψ : ι → c × d → ℂ) (X : Matrix c c ℂ) : Matrix ι ι ℂ :=
  Matrix.of fun i j => endpointPairing (ψ i) (endpointProbeAction X (ψ j))

omit [DecidableEq c] in
/-- **The channel of a Hermitian probe is Hermitian.** -/
theorem isHermitian_endpointChannel {ι : Type*} [Fintype ι] (ψ : ι → c × d → ℂ)
    {X : Matrix c c ℂ} (hX : X.IsHermitian) : (endpointChannel ψ X).IsHermitian := by
  ext i j
  show (starRingEnd ℂ) (endpointChannel ψ X j i) = endpointChannel ψ X i j
  simp only [endpointChannel, Matrix.of_apply]
  rw [endpointPairing_probe_eq_trace, endpointPairing_probe_eq_trace]
  show star ((X * reducedTransition (ψ j) (ψ i)).trace) = _
  rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, reducedTransition_conjTranspose, hX,
    Matrix.trace_mul_comm]

omit [DecidableEq c] in
theorem endpointChannel_ne_zero {ι : Type*} (ψ : ι → c × d → ℂ) {X : Matrix c c ℂ}
    (hX : ∀ i j : ι, i ≠ j → endpointPairing (ψ i) (endpointProbeAction X (ψ j)) ≠ 0)
    (i j : ι) (hij : i ≠ j) : endpointChannel ψ X i j ≠ 0 := hX i j hij

end Probe

end

end GaloisForLFunctions.HTGeometry
