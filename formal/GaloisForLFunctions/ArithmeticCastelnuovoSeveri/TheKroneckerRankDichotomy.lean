import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectCountsTheRightZeros

/-!
# The Kronecker-rank dichotomy: the Hodge defect is `0` or `∞` under recurrence

A configuration is **vertically recurrent** (`VerticallyRecurrent`) when every zero recurs, up to
any `ε` in its real part, at arbitrarily large heights. Lattice systems (Kronecker rank one) are
periodic in height (`verticallyRecurrent_of_periodic`); the zero sets of almost periodic
Dirichlet series of finite Kronecker rank recur in the same way by Bohr's almost periodicity.

**Theorem** (`recurrent_pontryagin_dichotomy`). A tempered, vertically recurrent configuration has
either no negative square on any finite family of tests, or arbitrarily many: one zero right of the
line recurs right of the line at unbounded heights (`rightZeros_infinite_of_recurrent`), and the
Pontryagin law (`pontryagin_law`) turns infinitely many right zeros into unboundedly many negative
squares.

So a finite, nonzero Hodge defect — `n` off-line zeros, `0 < n < ∞` — is impossible for recurrent
configurations; among Euler products it can occur only at infinite Kronecker rank, which is where
`ζ` sits.
-/

open Complex Set
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- Every zero recurs, up to `ε` in its real part, at arbitrarily large heights. -/
def VerticallyRecurrent (Z : ZeroConfig) : Prop :=
  ∀ ρ ∈ Z.carrier, ∀ ε > 0, ∀ T : ℝ, ∃ ρ' ∈ Z.carrier, T < ρ'.im ∧ |ρ'.re - ρ.re| < ε

/-- **Rank one is recurrent**: a configuration invariant under `ρ ↦ ρ + iP` recurs exactly. -/
theorem verticallyRecurrent_of_periodic (Z : ZeroConfig) {P : ℝ} (hP : 0 < P)
    (hper : ∀ ρ ∈ Z.carrier, ρ + I * P ∈ Z.carrier) : VerticallyRecurrent Z := by
  intro ρ hρ ε hε T
  have hmem : ∀ k : ℕ, ρ + I * ((k : ℝ) * P) ∈ Z.carrier := by
    intro k
    induction k with
    | zero => simpa using hρ
    | succ k ih =>
      have h := hper _ ih
      convert h using 1
      push_cast
      ring
  obtain ⟨k, hk⟩ := exists_nat_gt ((T - ρ.im) / P)
  refine ⟨_, hmem k, ?_, ?_⟩
  · have him : (ρ + I * ((k : ℝ) * P)).im = ρ.im + k * P := by
      simp [Complex.add_im, Complex.mul_im]
    rw [him]
    have := (div_lt_iff₀ hP).mp hk
    linarith
  · have hre : (ρ + I * ((k : ℝ) * P)).re = ρ.re := by
      simp [Complex.add_re, Complex.mul_re]
    rw [hre, sub_self, abs_zero]
    exact hε

/-- **One zero right of the line recurs to infinitely many.** -/
theorem rightZeros_infinite_of_recurrent (Z : ZeroConfig) (hrec : VerticallyRecurrent Z)
    (hne : (rightZeros Z).Nonempty) : (rightZeros Z).Infinite := by
  obtain ⟨ρ, hρ, hre⟩ := hne
  intro hfin
  -- a finite set of zeros has bounded heights
  obtain ⟨T, hT⟩ := (hfin.image Complex.im).bddAbove
  obtain ⟨ρ', hρ', hT', hclose⟩ := hrec ρ hρ (ρ.re - 1 / 2) (by linarith) T
  have hre' : 1 / 2 < ρ'.re := by
    have := (abs_lt.mp hclose).1
    linarith
  have := hT ⟨ρ', ⟨hρ', hre'⟩, rfl⟩
  linarith

/-- **The Kronecker-rank dichotomy.** A tempered, vertically recurrent configuration has Hodge
defect `0` or `∞`. -/
theorem recurrent_pontryagin_dichotomy (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hrec : VerticallyRecurrent Z) :
    (∀ (n : ℕ) (f : Fin n → ℝ → ℂ), (∀ i, ContDiff ℝ 2 (f i)) → (∀ i, HasCompactSupport (f i)) →
      hermNegIndex (zeroGram Z f) = 0) ∨
    ∀ n : ℕ, ∃ f : Fin n → ℝ → ℂ, (∀ i, ContDiff ℝ 2 (f i)) ∧ (∀ i, HasCompactSupport (f i)) ∧
      n ≤ hermNegIndex (zeroGram Z f) := by
  rcases (rightZeros Z).eq_empty_or_nonempty with hR | hR
  · refine Or.inl fun n f hf hfc => ?_
    have h := negIndex_zeroGram_le_of_tempered Z hZ f hf hfc
    rw [hR, Set.encard_empty] at h
    have h0 : hermNegIndex (zeroGram Z f) ≤ 0 := by exact_mod_cast h
    omega
  · refine Or.inr fun n => (pontryagin_law Z hZ n).mpr ?_
    rw [Set.encard_eq_top_iff.mpr (rightZeros_infinite_of_recurrent Z hrec hR)]
    exact le_top

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
