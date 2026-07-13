import GaloisForLFunctions.RHTower.RHLadderTheory
import GaloisForLFunctions.RHTower.SigmaDivisorJet

/-!
# Prime-power rigidity of a local divisor jet

At a zero of order `m`, the local divisor algebra is `R[X]/(X^m)`.  A prime-power coordinate
operation sends the cotangent generator `X` to `X^n`.  Once `n >= m`, that image is zero.  Hence
such an operation cannot be invertible unless `m = 1`.

This gives a precise positive successor to the module-linear Weyl no-go: an invertible source
action which genuinely descends as a high prime-power coordinate map would force the local divisor
to be simple.  This file proves the local algebraic implication, not the source descent.
-/

namespace RHTower

open Polynomial

noncomputable section

/-- The cotangent-coordinate class in the order-`m` local divisor algebra. -/
def localDivisorJetVariable (R : Type*) [CommRing R] (m : ℕ) :
    LocalDivisorJet R m :=
  jetClass R m Polynomial.X

/-- At length at least two, the local cotangent coordinate survives. -/
theorem localDivisorJetVariable_ne_zero
    (R : Type*) [CommRing R] [Nontrivial R] {m : ℕ} (hm : 1 < m) :
    localDivisorJetVariable R m ≠ 0 := by
  rw [localDivisorJetVariable, jetClass_ne_zero_iff_exists_coeff_lt_ne_zero]
  exact ⟨1, hm, by simp⟩

/-- Every power at or above the truncation depth vanishes. -/
theorem localDivisorJetVariable_pow_eq_zero
    (R : Type*) [CommRing R] {m n : ℕ} (hmn : m ≤ n) :
    (localDivisorJetVariable R m) ^ n = 0 := by
  change jetClass R m ((Polynomial.X : Polynomial R) ^ n) = 0
  exact jetClass_eq_zero_of_X_pow_dvd R m (pow_dvd_pow Polynomial.X hmn)

/-- **Prime-power rigidity.**  If an automorphism of a positive-length divisor jet sends the
cotangent coordinate to a power at least the jet depth, then the jet has length one. -/
theorem localDivisorJet_primePower_equiv_forces_simple
    (R : Type*) [CommRing R] [Nontrivial R] {m n : ℕ}
    (hm : 0 < m) (hmn : m ≤ n)
    (F : LocalDivisorJet R m ≃+* LocalDivisorJet R m)
    (hF : F (localDivisorJetVariable R m) =
      (localDivisorJetVariable R m) ^ n) :
    m = 1 := by
  have hpow : (localDivisorJetVariable R m) ^ n = 0 :=
    localDivisorJetVariable_pow_eq_zero R hmn
  have hFx : F (localDivisorJetVariable R m) = 0 := hF.trans hpow
  have hx : localDivisorJetVariable R m = 0 := by
    apply F.injective
    simpa using hFx
  by_contra hne
  exact localDivisorJetVariable_ne_zero R (by omega) hx

/-- **Prime-power local-jet route to RH.**  The first ladder rung makes every hypothetical
right-half order even.  If a reversible source operation acts on that local divisor jet as one
coordinate power at least as large as the order, prime-power rigidity makes the same order one,
which is impossible. -/
theorem riemannHypothesis_of_rhLadder_one_of_rightLocalPrimePowerEquiv
    (hladder : RHLadder 1)
    (hprime : ∀ ρ ∈ rightHalf, xi ρ = 0 →
      ∃ n : ℕ, (analyticOrderAt xi ρ).toNat ≤ n ∧
        ∃ F : LocalDivisorJet ℂ (analyticOrderAt xi ρ).toNat ≃+*
            LocalDivisorJet ℂ (analyticOrderAt xi ρ).toNat,
          F (localDivisorJetVariable ℂ (analyticOrderAt xi ρ).toNat) =
            (localDivisorJetVariable ℂ (analyticOrderAt xi ρ).toNat) ^ n) :
    RiemannHypothesis := by
  rw [rh_iff_xi_ne_zero_right]
  intro ρ hρ hzero
  obtain ⟨n, hmn, F, hF⟩ := hprime ρ hρ hzero
  have hmpos : 0 < (analyticOrderAt xi ρ).toNat :=
    Nat.pos_of_ne_zero (xi_order_toNat_ne_zero hzero)
  have hmone : (analyticOrderAt xi ρ).toNat = 1 :=
    localDivisorJet_primePower_equiv_forces_simple ℂ hmpos hmn F hF
  have heven : Even (analyticOrderAt xi ρ).toNat :=
    rhLadder_one_iff_even_order.mp hladder ρ hρ hzero
  rw [hmone] at heven
  exact Nat.not_even_one heven

end

end RHTower
