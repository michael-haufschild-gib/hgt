import GaloisForLFunctions.RHTower.TraceHankelConverse

/-!
# The shell-isolating real polynomial

Summing the corpus's phase-corrected orbit separators over a set of representatives of the nonreal
conjugate orbits of a finite packet produces a single **real** polynomial that is one on every
point of the selected shell and its conjugates and zero on every other point of the packet.  This
is the finite Schwarz-real interpolation used to isolate a bottom off-line shell.
-/

namespace RHTower

noncomputable section

theorem evalRealPolynomial_finsetSum {ι : Type*} (s : Finset ι) (p : ι → Polynomial ℝ) (z : ℂ) :
    evalRealPolynomial (∑ i ∈ s, p i) z = ∑ i ∈ s, evalRealPolynomial (p i) z := by
  simp [evalRealPolynomial, Polynomial.map_sum, Polynomial.eval_finsetSum]

/-- The shell-isolating real polynomial attached to a packet `F` and a set `S` of representatives
of nonreal conjugate orbits. -/
def shellIsolatingPolynomial (F S : Finset ℂ) (n : ℕ) : Polynomial ℝ :=
  ∑ α ∈ S, phaseCorrectedSeparatorPolynomial F α 1 n

/-- **The shell-isolating polynomial is one on the selected shell.** -/
theorem eval_shellIsolatingPolynomial_target {F S : Finset ℂ} (hSF : S ⊆ F)
    (h0 : ∀ α ∈ S, α ≠ 0) (him : ∀ α ∈ S, α.im ≠ 0)
    (hsep : ∀ α ∈ S, ∀ γ ∈ S, γ = (starRingEnd ℂ) α → γ = α)
    (n : ℕ) {β : ℂ} (hβ : β ∈ S) :
    evalRealPolynomial (shellIsolatingPolynomial F S n) β = 1 := by
  rw [shellIsolatingPolynomial, evalRealPolynomial_finsetSum, Finset.sum_eq_single β]
  · exact eval_phaseCorrectedSeparatorPolynomial_target (h0 β hβ) (him β hβ) n
  · intro α hα hαβ
    refine eval_phaseCorrectedSeparatorPolynomial_outer_zero (hSF hβ) (Ne.symm hαβ) ?_ n
    intro h
    exact hαβ (hsep α hα β hβ h).symm
  · intro h
    exact absurd hβ h

/-- **It is also one on the conjugate shell.** -/
theorem eval_shellIsolatingPolynomial_conj_target {F S : Finset ℂ} (hSF : S ⊆ F)
    (h0 : ∀ α ∈ S, α ≠ 0) (him : ∀ α ∈ S, α.im ≠ 0)
    (hsep : ∀ α ∈ S, ∀ γ ∈ S, γ = (starRingEnd ℂ) α → γ = α)
    (n : ℕ) {β : ℂ} (hβ : β ∈ S) :
    evalRealPolynomial (shellIsolatingPolynomial F S n) ((starRingEnd ℂ) β) = 1 := by
  rw [evalRealPolynomial_conj,
    eval_shellIsolatingPolynomial_target hSF h0 him hsep n hβ, map_one]

/-- **It vanishes on every other point of the packet.** -/
theorem eval_shellIsolatingPolynomial_outer_zero {F S : Finset ℂ} {z : ℂ} (hz : z ∈ F)
    (hzS : ∀ α ∈ S, z ≠ α ∧ z ≠ (starRingEnd ℂ) α) (n : ℕ) :
    evalRealPolynomial (shellIsolatingPolynomial F S n) z = 0 := by
  rw [shellIsolatingPolynomial, evalRealPolynomial_finsetSum]
  refine Finset.sum_eq_zero fun α hα => ?_
  exact eval_phaseCorrectedSeparatorPolynomial_outer_zero hz (hzS α hα).1 (hzS α hα).2 n

/-- **In particular it vanishes at every real point of the packet.** -/
theorem eval_shellIsolatingPolynomial_real_zero {F S : Finset ℂ} {x : ℝ} (hx : (x : ℂ) ∈ F)
    (him : ∀ α ∈ S, α.im ≠ 0) (n : ℕ) :
    evalRealPolynomial (shellIsolatingPolynomial F S n) (x : ℂ) = 0 := by
  refine eval_shellIsolatingPolynomial_outer_zero hx (fun α hα => ⟨?_, ?_⟩) n
  · intro h
    exact him α hα (by rw [← h]; simp)
  · intro h
    have : ((starRingEnd ℂ) α).im = 0 := by rw [← h]; simp
    rw [Complex.conj_im] at this
    exact him α hα (by linarith)

end

end RHTower
