import Mathlib

/-!
# Airy-tower zero-loop Stokes rigidity

This file formalizes the arithmetic core of the Airy-tower classification for one ramified
irregular class.  A characteristic is the exact decreasing gcd chain

`R = e₀ > e₁ > ... > eₘ = 1`,  `eᵢ = gcd(eᵢ₋₁, βᵢ)`,  `β₁ > ... > βₘ > 0`.

Its weighted irregularity is `Σ βᵢ (eᵢ₋₁ - eᵢ)`.  The diagonal Stokes-loop functional is this
weighted irregularity minus `R² - 1`.  The main theorem proves that it vanishes exactly for the
Airy-tower law `βᵢ = eᵢ₋₁ + eᵢ` at every level.  The two strict inequalities at the first
deviation are also proved, giving the full sign law rather than only its zero case.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

/-- Exact ramified characteristic data, indexed by ramification and first characteristic exponent.

`terminal` is the final gcd drop `R > 1` to `1`.  `step` records a proper intermediate gcd `E > 1`
and a tail whose first exponent is strictly smaller. -/
inductive Characteristic : (ramification firstExponent : ℕ) → Type
  | terminal {R beta : ℕ}
      (ramified : 1 < R)
      (exponent_pos : 0 < beta)
      (gcd_eq_one : Nat.gcd R beta = 1) : Characteristic R beta
  | step {R E beta gamma : ℕ}
      (drop : E < R)
      (intermediate : 1 < E)
      (exponent_pos : 0 < beta)
      (gcd_eq : Nat.gcd R beta = E)
      (exponents_strict : gamma < beta)
      (tail : Characteristic E gamma) : Characteristic R beta

namespace Characteristic

/-- Ramification immediately after the first gcd drop. -/
def nextRamification {R beta : ℕ} : Characteristic R beta → ℕ
  | .terminal .. => 1
  | .step (E := E) .. => E

/-- Weighted irregularity `Σ βᵢ(eᵢ₋₁-eᵢ)`. -/
def weightedIrregularity {R beta : ℕ} : Characteristic R beta → ℕ
  | .terminal .. => beta * (R - 1)
  | .step (E := E) _ _ _ _ _ tail =>
      beta * (R - E) + tail.weightedIrregularity

/-- Signed diagonal Stokes-loop functional
`Σ βᵢ(eᵢ₋₁-eᵢ) - R² + 1`. -/
def diagonalLoop {R beta : ℕ} (c : Characteristic R beta) : ℤ :=
  (c.weightedIrregularity : ℤ) - (R : ℤ) ^ 2 + 1

/-- The Airy-tower law at every gcd drop. -/
def IsAiryTower {R beta : ℕ} : Characteristic R beta → Prop
  | .terminal .. => beta = R + 1
  | .step (E := E) _ _ _ _ _ tail => beta = R + E ∧ tail.IsAiryTower

/-- Hiroe's negative Fourier congruence at every characteristic step. -/
def SatisfiesNegativeFourier {R beta : ℕ} : Characteristic R beta → Prop
  | .terminal .. => beta ∣ R + 1
  | .step (E := E) _ _ _ _ _ tail => beta ∣ R + E ∧ tail.SatisfiesNegativeFourier

/-- Size branch selecting the all-negative Fourier reduction. -/
def HasLargeFourierSteps {R beta : ℕ} : Characteristic R beta → Prop
  | .terminal .. => R < beta
  | .step _ _ _ _ _ tail => R < beta ∧ tail.HasLargeFourierSteps

@[simp] theorem nextRamification_terminal {R beta : ℕ} (hR : 1 < R) (hbeta : 0 < beta)
    (hgcd : Nat.gcd R beta = 1) :
    (Characteristic.terminal hR hbeta hgcd).nextRamification = 1 := rfl

@[simp] theorem nextRamification_step {R E beta gamma : ℕ} (hER : E < R) (hE : 1 < E)
    (hbeta : 0 < beta) (hgcd : Nat.gcd R beta = E) (hgamma : gamma < beta)
    (tail : Characteristic E gamma) :
    (Characteristic.step hER hE hbeta hgcd hgamma tail).nextRamification = E := rfl

theorem nextRamification_pos {R beta : ℕ} (c : Characteristic R beta) :
    0 < c.nextRamification := by
  cases c with
  | terminal => simp [nextRamification]
  | step _ hE => simp [nextRamification]; omega

theorem nextRamification_lt {R beta : ℕ} (c : Characteristic R beta) :
    c.nextRamification < R := by
  cases c with
  | terminal hR => simp [nextRamification]; omega
  | step hER => simpa [nextRamification] using hER

theorem gcd_eq_nextRamification {R beta : ℕ} (c : Characteristic R beta) :
    Nat.gcd R beta = c.nextRamification := by
  cases c with
  | terminal _ _ hgcd => simpa [nextRamification] using hgcd
  | step _ _ _ hgcd => simpa [nextRamification] using hgcd

/-- A proper positive divisor is at most half its multiple. -/
private theorem twice_le_of_dvd_of_lt {E R : ℕ} (hE : 0 < E) (hdvd : E ∣ R) (hlt : E < R) :
    2 * E ≤ R := by
  obtain ⟨q, rfl⟩ := hdvd
  have hq : 1 < q := by nlinarith
  nlinarith

/-- There is no nontrivial gcd multiple strictly between `R-E` and `R+E` except `R`, whose gcd
with `R` is too large.  This is the discrete gap driving the negative half of the sign law. -/
theorem le_sub_of_lt_add_gcd {R beta E : ℕ} (hE : 0 < E) (hER : E < R)
    (hgcd : Nat.gcd R beta = E) (hlt : beta < R + E) :
    beta ≤ R - E := by
  have hEdvdR : E ∣ R := by
    rw [← hgcd]
    exact Nat.gcd_dvd_left R beta
  have hEdvdBeta : E ∣ beta := by
    rw [← hgcd]
    exact Nat.gcd_dvd_right R beta
  obtain ⟨r, rfl⟩ := hEdvdR
  obtain ⟨b, rfl⟩ := hEdvdBeta
  have hr : 1 < r := by nlinarith
  have hb_le : b ≤ r := by nlinarith
  have hb_ne : b ≠ r := by
    intro h
    subst b
    rw [Nat.gcd_self] at hgcd
    nlinarith
  have hb : b < r := lt_of_le_of_ne hb_le hb_ne
  have hmul : E * b ≤ E * (r - 1) :=
    Nat.mul_le_mul_left E (Nat.le_sub_one_of_lt hb)
  simpa [Nat.mul_sub_left_distrib] using hmul

/-- After `R+E`, the next possible common `E`-multiple is at least `R+2E`. -/
theorem add_twice_le_of_add_lt_of_dvd {R beta E : ℕ} (hE : 0 < E)
    (hEdvdR : E ∣ R) (hEdvdBeta : E ∣ beta) (hlt : R + E < beta) :
    R + 2 * E ≤ beta := by
  obtain ⟨r, rfl⟩ := hEdvdR
  obtain ⟨b, rfl⟩ := hEdvdBeta
  have hrb : r + 1 < b := by
    apply (Nat.mul_lt_mul_left hE).mp
    simpa [Nat.mul_add] using hlt
  have hrb' : r + 2 ≤ b := by omega
  have hmul := Nat.mul_le_mul_left E hrb'
  simpa [Nat.mul_add, Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul

/-- Every tail is bounded by its first exponent times the total remaining ramification drop. -/
theorem weightedIrregularity_le_first {R beta : ℕ} (c : Characteristic R beta) :
    c.weightedIrregularity ≤ beta * (R - 1) := by
  induction c with
  | terminal => rfl
  | @step R E beta gamma hER hE hbeta hgcd hgamma tail ih =>
      simp only [weightedIrregularity]
      have hgamma_le : gamma * (E - 1) ≤ beta * (E - 1) :=
        Nat.mul_le_mul_right (E - 1) (Nat.le_of_lt hgamma)
      have hsplit : R - E + (E - 1) = R - 1 := by omega
      calc
        beta * (R - E) + tail.weightedIrregularity
            ≤ beta * (R - E) + gamma * (E - 1) := Nat.add_le_add_left ih _
        _ ≤ beta * (R - E) + beta * (E - 1) := Nat.add_le_add_left hgamma_le _
        _ = beta * (R - 1) := by rw [← Nat.mul_add, hsplit]

/-- The tail bound is strict as soon as there is an intermediate gcd level. -/
theorem weightedIrregularity_lt_first_of_step {R E beta gamma : ℕ}
    (hER : E < R) (hE : 1 < E) (hbeta : 0 < beta) (hgcd : Nat.gcd R beta = E)
    (hgamma : gamma < beta) (tail : Characteristic E gamma) :
    (Characteristic.step hER hE hbeta hgcd hgamma tail).weightedIrregularity <
      beta * (R - 1) := by
  simp only [weightedIrregularity]
  have htail := tail.weightedIrregularity_le_first
  have hgamma_mul : gamma * (E - 1) < beta * (E - 1) :=
    (Nat.mul_lt_mul_right (by omega)).2 hgamma
  have hsplit : R - E + (E - 1) = R - 1 := by omega
  calc
    beta * (R - E) + tail.weightedIrregularity
        ≤ beta * (R - E) + gamma * (E - 1) := Nat.add_le_add_left htail _
    _ < beta * (R - E) + beta * (E - 1) := Nat.add_lt_add_left hgamma_mul _
    _ = beta * (R - 1) := by rw [← Nat.mul_add, hsplit]

/-- The first characteristic contribution is part of the full weighted irregularity. -/
theorem firstContribution_le_weightedIrregularity {R beta : ℕ} (c : Characteristic R beta) :
    beta * (R - c.nextRamification) ≤ c.weightedIrregularity := by
  cases c <;> simp [nextRamification, weightedIrregularity]

/-- Every characteristic has genuinely ramified initial degree. -/
theorem ramification_gt_one {R beta : ℕ} (c : Characteristic R beta) : 1 < R := by
  cases c with
  | terminal hR => exact hR
  | step hER hE => omega

/-- A first exponent below the Airy value forces negative signed diagonal loop. -/
theorem diagonalLoop_neg_of_first_lt {R beta : ℕ}
    (c : Characteristic R beta) (hfirst : beta < R + c.nextRamification) :
    c.diagonalLoop < 0 := by
  let E := c.nextRamification
  have hE : 0 < E := c.nextRamification_pos
  have hER : E < R := c.nextRamification_lt
  have hgcd : Nat.gcd R beta = E := c.gcd_eq_nextRamification
  have hbeta : beta ≤ R - E := le_sub_of_lt_add_gcd hE hER hgcd hfirst
  have hR : 1 < R := c.ramification_gt_one
  have hbetaR : beta ≤ R - 1 := by omega
  have hweighted := c.weightedIrregularity_le_first
  have hmul : beta * (R - 1) ≤ (R - 1) * (R - 1) :=
    Nat.mul_le_mul_right (R - 1) hbetaR
  have hbound : c.weightedIrregularity ≤ (R - 1) * (R - 1) :=
    le_trans hweighted hmul
  have hboundZ : (c.weightedIrregularity : ℤ) ≤ ((R - 1) * (R - 1) : ℕ) := by
    exact_mod_cast hbound
  have hRone : 1 ≤ R := by omega
  simp only [diagonalLoop]
  push_cast [Nat.cast_sub hRone] at hboundZ
  nlinarith

/-- A first exponent above the Airy value forces positive signed diagonal loop. -/
theorem diagonalLoop_pos_of_first_gt {R beta : ℕ}
    (c : Characteristic R beta) (hfirst : R + c.nextRamification < beta) :
    0 < c.diagonalLoop := by
  let E := c.nextRamification
  have hE : 0 < E := c.nextRamification_pos
  have hER : E < R := c.nextRamification_lt
  have hgcd : Nat.gcd R beta = E := c.gcd_eq_nextRamification
  have hEdvdR : E ∣ R := by
    rw [← hgcd]
    exact Nat.gcd_dvd_left R beta
  have hEdvdBeta : E ∣ beta := by
    rw [← hgcd]
    exact Nat.gcd_dvd_right R beta
  have hbeta : R + 2 * E ≤ beta :=
    add_twice_le_of_add_lt_of_dvd hE hEdvdR hEdvdBeta hfirst
  have htwice : 2 * E ≤ R := twice_le_of_dvd_of_lt hE hEdvdR hER
  have hERsub : R - E + E = R := Nat.sub_add_cancel (Nat.le_of_lt hER)
  have hEsub : E ≤ R - E := by omega
  have hproduct : R ^ 2 ≤ (R + 2 * E) * (R - E) := by
    nlinarith
  have hmono : (R + 2 * E) * (R - E) ≤ beta * (R - E) :=
    Nat.mul_le_mul_right (R - E) hbeta
  have hfirstContribution := c.firstContribution_le_weightedIrregularity
  have htotal : R ^ 2 ≤ c.weightedIrregularity :=
    le_trans hproduct (le_trans hmono hfirstContribution)
  have htotalZ : ((R : ℤ) ^ 2) ≤ (c.weightedIrregularity : ℤ) := by
    exact_mod_cast htotal
  simp only [diagonalLoop]
  omega

/-- At the Airy value, the signed diagonal loop is exactly the tail loop. -/
theorem diagonalLoop_step_of_first_eq
    {R E beta gamma : ℕ} (hER : E < R) (hE : 1 < E) (hbeta : 0 < beta)
    (hgcd : Nat.gcd R beta = E) (hgamma : gamma < beta) (tail : Characteristic E gamma)
    (hAiry : beta = R + E) :
    (Characteristic.step hER hE hbeta hgcd hgamma tail).diagonalLoop =
      tail.diagonalLoop := by
  subst beta
  simp only [diagonalLoop, weightedIrregularity]
  push_cast [Nat.cast_sub (Nat.le_of_lt hER)]
  ring

/-- The terminal Airy value gives zero signed diagonal loop. -/
theorem diagonalLoop_terminal_of_first_eq {R beta : ℕ} (hR : 1 < R)
    (hbeta : 0 < beta) (hgcd : Nat.gcd R beta = 1) (hAiry : beta = R + 1) :
    (Characteristic.terminal hR hbeta hgcd).diagonalLoop = 0 := by
  subst beta
  simp only [diagonalLoop, weightedIrregularity]
  push_cast [Nat.cast_sub (by omega : 1 ≤ R)]
  ring

/-- **Airy-tower zero-loop rigidity.**  Signed diagonal loop vanishes exactly when every
characteristic exponent is the sum of the adjacent gcd-chain ramifications. -/
theorem diagonalLoop_eq_zero_iff_isAiryTower {R beta : ℕ}
    (c : Characteristic R beta) :
    c.diagonalLoop = 0 ↔ c.IsAiryTower := by
  induction c with
  | @terminal R beta hR hbeta hgcd =>
      simp only [IsAiryTower]
      constructor
      · intro hzero
        by_contra hne
        have hlt_or_gt : beta < R + 1 ∨ R + 1 < beta := by omega
        cases hlt_or_gt with
        | inl hlt =>
            have hneg := diagonalLoop_neg_of_first_lt
              (Characteristic.terminal hR hbeta hgcd) (by simpa [nextRamification] using hlt)
            omega
        | inr hgt =>
            have hpos := diagonalLoop_pos_of_first_gt
              (Characteristic.terminal hR hbeta hgcd) (by simpa [nextRamification] using hgt)
            omega
      · intro hAiry
        exact diagonalLoop_terminal_of_first_eq hR hbeta hgcd hAiry
  | @step R E beta gamma hER hE hbeta hgcd hgamma tail ih =>
      simp only [IsAiryTower]
      constructor
      · intro hzero
        have hfirst : beta = R + E := by
          by_contra hne
          have hlt_or_gt : beta < R + E ∨ R + E < beta := by omega
          cases hlt_or_gt with
          | inl hlt =>
              have hneg := diagonalLoop_neg_of_first_lt
                (Characteristic.step hER hE hbeta hgcd hgamma tail)
                (by simpa [nextRamification] using hlt)
              omega
          | inr hgt =>
              have hpos := diagonalLoop_pos_of_first_gt
                (Characteristic.step hER hE hbeta hgcd hgamma tail)
                (by simpa [nextRamification] using hgt)
              omega
        refine ⟨hfirst, ?_⟩
        apply ih.mp
        rw [← diagonalLoop_step_of_first_eq hER hE hbeta hgcd hgamma tail hfirst]
        exact hzero
      · rintro ⟨hfirst, htail⟩
        rw [diagonalLoop_step_of_first_eq hER hE hbeta hgcd hgamma tail hfirst]
        exact ih.mpr htail

/-- Natural-number form of zero-loop rigidity: the weighted irregularity is exactly `R²-1`. -/
theorem weightedIrregularity_eq_diagonal_iff_isAiryTower {R beta : ℕ}
    (c : Characteristic R beta) :
    c.weightedIrregularity = R ^ 2 - 1 ↔ c.IsAiryTower := by
  rw [← c.diagonalLoop_eq_zero_iff_isAiryTower]
  have hR : 1 ≤ R := Nat.le_of_lt c.ramification_gt_one
  have hR2 : 1 ≤ R ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul hR hR
  constructor
  · intro h
    simp only [diagonalLoop]
    rw [h]
    push_cast [Nat.cast_sub hR2]
    ring
  · intro h
    have hcast : (c.weightedIrregularity : ℤ) = ((R ^ 2 - 1 : ℕ) : ℤ) := by
      simp only [diagonalLoop] at h
      push_cast [Nat.cast_sub hR2]
      nlinarith
    exact_mod_cast hcast

/-- Every Airy tower lies on Hiroe's negative Fourier branch. -/
theorem satisfiesNegativeFourier_of_isAiryTower {R beta : ℕ} (c : Characteristic R beta)
    (hAiry : c.IsAiryTower) : c.SatisfiesNegativeFourier := by
  induction c with
  | terminal => simp only [IsAiryTower, SatisfiesNegativeFourier] at hAiry ⊢; simp [hAiry]
  | step hER hE hbeta hgcd hgamma tail ih =>
      exact ⟨by simp [hAiry.1], ih hAiry.2⟩

/-- Every Airy tower has first exponent strictly above the current ramification at every step. -/
theorem hasLargeFourierSteps_of_isAiryTower {R beta : ℕ} (c : Characteristic R beta)
    (hAiry : c.IsAiryTower) : c.HasLargeFourierSteps := by
  induction c with
  | terminal => simp only [IsAiryTower, HasLargeFourierSteps] at hAiry ⊢; omega
  | step hER hE hbeta hgcd hgamma tail ih =>
      exact ⟨by rw [hAiry.1]; omega, ih hAiry.2⟩

/-- A positive multiple of `beta` strictly between `beta` and `2 beta` equals `beta`. -/
private theorem eq_of_dvd_of_lt_twice {beta n : ℕ} (hbeta : 0 < beta)
    (hdvd : beta ∣ n) (hle : beta ≤ n) (hlt : n < 2 * beta) : n = beta := by
  obtain ⟨k, rfl⟩ := hdvd
  have hkpos : 0 < k := by nlinarith
  have hkle : k < 2 := by nlinarith
  have hk : k = 1 := by omega
  simp [hk]

/-- Converse Fourier criterion.  Negative congruence plus the large-step branch forces the exact
Airy equality at every level. -/
theorem isAiryTower_of_negativeFourier_of_largeSteps {R beta : ℕ}
    (c : Characteristic R beta) (hFourier : c.SatisfiesNegativeFourier)
    (hLarge : c.HasLargeFourierSteps) : c.IsAiryTower := by
  induction c with
  | @terminal R beta hR hbeta hgcd =>
      simp only [SatisfiesNegativeFourier] at hFourier
      simp only [HasLargeFourierSteps] at hLarge
      simp only [IsAiryTower]
      have hle : beta ≤ R + 1 := Nat.le_of_dvd (by omega) hFourier
      symm
      apply eq_of_dvd_of_lt_twice hbeta hFourier hle (by omega)
  | @step R E beta gamma hER hE hbeta hgcd hgamma tail ih =>
      rcases hFourier with ⟨hdiv, htailFourier⟩
      rcases hLarge with ⟨hlarge, htailLarge⟩
      refine ⟨?_, ih htailFourier htailLarge⟩
      have hle : beta ≤ R + E := Nat.le_of_dvd (by omega) hdiv
      symm
      apply eq_of_dvd_of_lt_twice hbeta hdiv hle (by omega)

/-- Exact Fourier characterization of Airy towers. -/
theorem isAiryTower_iff_negativeFourier_and_largeSteps {R beta : ℕ}
    (c : Characteristic R beta) :
    c.IsAiryTower ↔ c.SatisfiesNegativeFourier ∧ c.HasLargeFourierSteps := by
  constructor
  · intro h
    exact ⟨c.satisfiesNegativeFourier_of_isAiryTower h,
      c.hasLargeFourierSteps_of_isAiryTower h⟩
  · rintro ⟨hFourier, hLarge⟩
    exact c.isAiryTower_of_negativeFourier_of_largeSteps hFourier hLarge

end Characteristic

/-- A strict divisor chain `R = e₀ > e₁ > ... > eₘ = 1`, with terminal `1` implicit.

The terminal constructor records the last drop `R > 1`; a step records a proper intermediate
divisor `E > 1`. -/
inductive StrictDivisorChain : ℕ → Type
  | terminal {R : ℕ} (ramified : 1 < R) : StrictDivisorChain R
  | step {R E : ℕ} (drop : E < R) (intermediate : 1 < E) (divides : E ∣ R)
      (tail : StrictDivisorChain E) : StrictDivisorChain R

namespace StrictDivisorChain

/-- First Airy exponent attached to a strict divisor chain. -/
def firstExponent {R : ℕ} : StrictDivisorChain R → ℕ
  | .terminal .. => R + 1
  | .step (E := E) .. => R + E

theorem ramification_gt_one {R : ℕ} (d : StrictDivisorChain R) : 1 < R := by
  cases d with
  | terminal hR => exact hR
  | step hER hE => omega

/-- The generated first exponent is always below twice the ramification. -/
theorem firstExponent_lt_twice {R : ℕ} (d : StrictDivisorChain R) :
    d.firstExponent < 2 * R := by
  cases d with
  | terminal hR => simp only [firstExponent]; omega
  | step hER => simp only [firstExponent]; omega

/-- Every strict divisor chain generates its canonical Airy characteristic. -/
def toCharacteristic {R : ℕ} (d : StrictDivisorChain R) :
    Characteristic R d.firstExponent :=
  match d with
  | .terminal hR =>
      Characteristic.terminal hR (by simp [firstExponent]) (by simp [firstExponent])
  | .step (E := E) hER hE hdvd tail =>
      have hgcd : Nat.gcd R (R + E) = E := by
        rw [Nat.gcd_self_add_right]
        exact Nat.gcd_eq_right_iff_dvd.mpr hdvd
      have hgamma : tail.firstExponent < R + E := by
        have htail := tail.firstExponent_lt_twice
        omega
      Characteristic.step (E := E) (beta := R + E) (gamma := tail.firstExponent)
        hER hE (by omega) hgcd hgamma tail.toCharacteristic

@[simp] theorem toCharacteristic_isAiryTower {R : ℕ} (d : StrictDivisorChain R) :
    d.toCharacteristic.IsAiryTower := by
  induction d with
  | terminal => rfl
  | step hER hE hdvd tail ih => exact ⟨rfl, ih⟩

end StrictDivisorChain

namespace Characteristic

/-- Forget exponents and retain the exact gcd divisor chain. -/
def toStrictDivisorChain {R beta : ℕ} (c : Characteristic R beta) : StrictDivisorChain R :=
  match c with
  | .terminal hR _ _ => StrictDivisorChain.terminal hR
  | .step (E := E) hER hE _ hgcd _ tail =>
      have hdvd : E ∣ R := by
        rw [← hgcd]
        exact Nat.gcd_dvd_left R beta
      StrictDivisorChain.step hER hE hdvd tail.toStrictDivisorChain

/-- Airy law uniquely fixes the exponent at every node of the extracted divisor chain. -/
theorem eq_firstExponent_toStrictDivisorChain_of_isAiryTower {R beta : ℕ}
    (c : Characteristic R beta) (hAiry : c.IsAiryTower) :
    beta = c.toStrictDivisorChain.firstExponent := by
  cases c with
  | terminal => simpa [IsAiryTower, toStrictDivisorChain, StrictDivisorChain.firstExponent]
      using hAiry
  | step => exact hAiry.1

end Characteristic

/-- Extracting the divisor chain from its canonical Airy characteristic is the identity. -/
@[simp] theorem StrictDivisorChain.toStrictDivisorChain_toCharacteristic {R : ℕ}
    (d : StrictDivisorChain R) :
    d.toCharacteristic.toStrictDivisorChain = d := by
  induction d with
  | terminal => rfl
  | step hER hE hdvd tail ih =>
      change StrictDivisorChain.step _ _ _
          tail.toCharacteristic.toStrictDivisorChain = StrictDivisorChain.step _ _ _ tail
      rw [ih]

end IrregularStokes
end GaloisForLFunctions
