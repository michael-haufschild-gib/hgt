import GaloisForLFunctions.RHTower.LocalDivisorJetAdamsDilation
import GaloisForLFunctions.RHTower.SymplecticMultiplicity

/-!
# Quasi-unipotent and power-bounded Adams rigidity on local divisor jets

The actual Euler/Adams operation on an order-`m` local divisor jet has weights
`1, n, ..., n^(m-1)`.  Two source structures that are much weaker than a pure-weight metric
already force this jet to be reduced:

* quasi-unipotent monodromy makes every weight a root of unity;
* a power-bounded realization uniformly bounds every iterate of every weight.

For `n ≥ 2`, either condition excludes the first cotangent weight `n`, so a positive-length jet
has length one.  The final capstones pair this simplicity mechanism with a source-derived
symplectic realization of right-half Xi fibers.  Symplecticity makes their orders even, while
Adams rigidity makes them one, hence no such fiber exists.

The local algebra and the conditional RH capstones are unconditional.  This file does not
construct the missing completed prime--Gamma regular-singular or power-bounded realization.
-/

namespace RHTower

noncomputable section

/-- Every actual Adams-dilation weight is quasi-unipotent.  This is the exact local consequence
that a regular-singular arithmetic monodromy realization would have to supply. -/
def AdamsDilationQuasiUnipotent (m n : ℕ) : Prop :=
  ∀ j : Fin m, ∃ r : ℕ, 0 < r ∧ (((n : ℂ) ^ (j : ℕ)) ^ r = 1)

/-- **Quasi-unipotent Adams rigidity.**  A genuine Adams dilation cannot be quasi-unipotent on a
nonreduced positive-length local jet: the surviving cotangent weight would be the integer
`n ≥ 2`, which has no positive power equal to one. -/
theorem adamsDilation_quasiUnipotent_forces_simple
    {m n : ℕ} (hm : 0 < m) (hn : 2 ≤ n)
    (hqu : AdamsDilationQuasiUnipotent m n) :
    m = 1 := by
  by_contra hne
  have hm2 : 2 ≤ m := by omega
  let j1 : Fin m := ⟨1, hm2⟩
  obtain ⟨r, hrpos, hr⟩ := hqu j1
  have hnrC : (n : ℂ) ^ r = 1 := by simpa [j1] using hr
  have hnrNorm := congrArg norm hnrC
  have hnr : (n : ℝ) ^ r = 1 := by simpa using hnrNorm
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  have hgt : (1 : ℝ) < (n : ℝ) ^ r :=
    one_lt_pow₀ hnreal (Nat.ne_of_gt hrpos)
  linarith

/-- The entire Adams-dilation semigroup is uniformly power-bounded on the local weight packet. -/
def AdamsDilationPowerBounded (m n : ℕ) : Prop :=
  ∃ C : ℝ, ∀ k : ℕ, ∀ j : Fin m,
    ‖(((n : ℂ) ^ (j : ℕ)) ^ k)‖ ≤ C

/-- **Power-bounded Adams rigidity.**  A nonreduced jet contains the weight `n`, whose iterates
escape every fixed bound for `n ≥ 2`.  Thus any Banach, Markov, KMS, or operator realization that
makes the genuine local Adams semigroup power-bounded forces the jet to be reduced. -/
theorem adamsDilation_powerBounded_forces_simple
    {m n : ℕ} (hm : 0 < m) (hn : 2 ≤ n)
    (hbounded : AdamsDilationPowerBounded m n) :
    m = 1 := by
  by_contra hne
  have hm2 : 2 ≤ m := by omega
  let j1 : Fin m := ⟨1, hm2⟩
  obtain ⟨C, hC⟩ := hbounded
  have hnreal : (1 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨k, hk⟩ :=
    ((tendsto_pow_atTop_atTop_of_one_lt hnreal).eventually_gt_atTop C).exists
  have hbound : (n : ℝ) ^ k ≤ C := by
    simpa [j1] using hC k j1
  exact (not_lt_of_ge hbound) hk

/-- **Polarized regular-singular Adams route to RH.**  A source symplectic realization makes
every hypothetical right-half order even.  Quasi-unipotent compatibility with the actual local
Adams dilation makes the same positive order equal to one. -/
theorem
    riemannHypothesis_of_rightSymplecticRealization_of_rightAdamsDilationQuasiUnipotent
    (hsymplectic : ∀ rho ∈ rightHalf, xi rho = 0 → SymplecticRealization rho)
    (hquasi : ∀ rho ∈ rightHalf, xi rho = 0 →
      ∃ n : ℕ, 2 ≤ n ∧
        AdamsDilationQuasiUnipotent (analyticOrderAt xi rho).toNat n) :
    RiemannHypothesis := by
  have hladder : RHLadder 1 := rhLadder_one_of_symplecticRealization hsymplectic
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  obtain ⟨n, hn, hqu⟩ := hquasi rho hrho hzero
  have hmpos : 0 < (analyticOrderAt xi rho).toNat :=
    Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hzero)
  have hmone : (analyticOrderAt xi rho).toNat = 1 :=
    adamsDilation_quasiUnipotent_forces_simple hmpos hn hqu
  have heven : Even (analyticOrderAt xi rho).toNat :=
    rhLadder_one_iff_even_order.mp hladder rho hrho hzero
  rw [hmone] at heven
  exact Nat.not_even_one heven

/-- **Polarized power-bounded Adams route to RH.**  This is the analytic/operator counterpart of
the quasi-unipotent capstone: the same source object supplies even multiplicity and forbids the
expanding cotangent weight. -/
theorem
    riemannHypothesis_of_rightSymplecticRealization_of_rightAdamsDilationPowerBounded
    (hsymplectic : ∀ rho ∈ rightHalf, xi rho = 0 → SymplecticRealization rho)
    (hbounded : ∀ rho ∈ rightHalf, xi rho = 0 →
      ∃ n : ℕ, 2 ≤ n ∧
        AdamsDilationPowerBounded (analyticOrderAt xi rho).toNat n) :
    RiemannHypothesis := by
  have hladder : RHLadder 1 := rhLadder_one_of_symplecticRealization hsymplectic
  rw [rh_iff_xi_ne_zero_right]
  intro rho hrho hzero
  obtain ⟨n, hn, hb⟩ := hbounded rho hrho hzero
  have hmpos : 0 < (analyticOrderAt xi rho).toNat :=
    Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hzero)
  have hmone : (analyticOrderAt xi rho).toNat = 1 :=
    adamsDilation_powerBounded_forces_simple hmpos hn hb
  have heven : Even (analyticOrderAt xi rho).toNat :=
    rhLadder_one_iff_even_order.mp hladder rho hrho hzero
  rw [hmone] at heven
  exact Nat.not_even_one heven

end

end RHTower
