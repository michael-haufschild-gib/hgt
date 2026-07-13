import GaloisForLFunctions.Bottcher.DyadicMonodromy
import GaloisForLFunctions.RHTower.IrrationalCircleOrderCharge

/-!
# Böttcher--Prüfer characters detect Xi multiplicity

The disconnected quadratic Böttcher tower supplies canonical complex multipliers of exact order
`2^n`.  Raising every depth multiplier to an integer multiplicity gives the trivial character at
all depths exactly when the multiplicity is zero.  Applied to the local Xi order, simultaneous
triviality at every right-half Xi zero is equivalent to RH.

This is a consumer-side bridge between two already formalized towers.  It does not construct a
source-natural coupling between the completed SEM boundary and Böttcher monodromy, nor prove such a
coupled character trivial.
-/

namespace RHTower

noncomputable section

/-- Evaluation of integer multiplicity on the depth-`n` Böttcher Prüfer multiplier. -/
def bottcherPrueferMultiplicityCharacter (m n : ℕ) : ℂ :=
  Bottcher.dyadicRoot n ^ m

/-- The complete Böttcher Prüfer tower separates every nonzero natural multiplicity. -/
theorem bottcherPrueferMultiplicityCharacter_all_one_iff (m : ℕ) :
    (∀ n, bottcherPrueferMultiplicityCharacter m n = 1) ↔ m = 0 := by
  constructor
  · intro h
    by_contra hm
    have hdvd : 2 ^ m ∣ m := by
      rw [← Bottcher.orderOf_dyadicRoot_named m]
      exact orderOf_dvd_of_pow_eq_one (h m)
    have hle : 2 ^ m ≤ m := Nat.le_of_dvd (Nat.pos_of_ne_zero hm) hdvd
    have hlt : m < 2 ^ m := Nat.lt_pow_self (by norm_num)
    omega
  · rintro rfl
    intro n
    simp [bottcherPrueferMultiplicityCharacter]

/-- The Böttcher Prüfer character of the local Xi order. -/
def xiBottcherPrueferCharge (ρ : ℂ) (n : ℕ) : ℂ :=
  bottcherPrueferMultiplicityCharacter (analyticOrderAt xi ρ).toNat n

theorem xiBottcherPrueferCharge_all_one_iff (ρ : ℂ) :
    (∀ n, xiBottcherPrueferCharge ρ n = 1) ↔
      (analyticOrderAt xi ρ).toNat = 0 := by
  exact bottcherPrueferMultiplicityCharacter_all_one_iff _

/-- RH is equivalent to simultaneous triviality of every Böttcher Prüfer character attached to
every hypothetical right-half Xi zero. -/
theorem riemannHypothesis_iff_all_xiBottcherPrueferCharges_trivial :
    RiemannHypothesis ↔
      ∀ ρ ∈ rightHalf, xi ρ = 0 → ∀ n, xiBottcherPrueferCharge ρ n = 1 := by
  constructor
  · intro hRH ρ hρ hzero
    exact (rh_iff_xi_ne_zero_right.mp hRH ρ hρ hzero).elim
  · intro hclose
    apply rh_iff_xi_ne_zero_right.mpr
    intro ρ hρ hzero
    have hzeroOrder := (xiBottcherPrueferCharge_all_one_iff ρ).mp
      (hclose ρ hρ hzero)
    exact (xi_order_toNat_ne_zero hzero hzeroOrder).elim

end


end RHTower
