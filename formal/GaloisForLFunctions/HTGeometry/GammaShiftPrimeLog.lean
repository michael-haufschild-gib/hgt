import GaloisForLFunctions.HTGeometry.GammaShiftMultiLaw
import GaloisForLFunctions.HTGeometry.WeldCircleFaithfulness

/-!
# The translation-saturated prime-log consequence

The shifts of the card's saturated field are the prime-log lattice `Λ = ⊕_p ℤ·log p`.  Two distinct
elements of `Λ` differ by an irrational amount — `primeLog_indep_mod_one`, the transcendence of `e`
together with unique factorization — so any finite family drawn from `Λ` satisfies the incongruence
hypothesis `(1)`.

Every relation over the saturated field uses finitely many translates, so it is a relation over some
finite `K_E`, and the zeta exclusion applies to it.
-/

open Filter Set Topology Function
open scoped BoundedContinuousFunction

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **Distinct prime-log lattice elements are incongruent modulo one.**  This is hypothesis `(1)` of
the card for shifts drawn from the prime-log lattice. -/
theorem primeLogShift_incongruent {c₁ c₂ : Nat.Primes →₀ ℤ} (hne : c₁ ≠ c₂) (k : ℤ) :
    RHTower.primeLogHom c₁ - RHTower.primeLogHom c₂ ≠ (k : ℝ) := by
  intro h
  have hsub : RHTower.primeLogHom (c₁ - c₂) = (k : ℝ) := by
    rw [map_sub]
    exact h
  have hval : ((c₁ - c₂).sum fun p z => z • Real.log (p : ℕ)) = (k : ℝ) := by
    rw [← RHTower.primeLogHom_apply]
    exact hsub
  obtain ⟨-, hzero⟩ := RHTower.primeLog_indep_mod_one (c₁ - c₂) k hval
  exact hne (by
    have := sub_eq_zero.mp hzero
    exact this)

/-- **Equation (25).**  Zeta satisfies no differential relation whose coefficients are built from
translates drawn from the prime-log lattice: any such relation uses finitely many of them, and the
finite-family exclusion applies. -/
theorem zeta_no_primeLogShift_relation {n N M r : ℕ} {σ R rr ρ : ℝ} (hσ : 1 < σ)
    (hN : 0 < N) (hM : 0 < M) (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R)
    (hRσ : R ≤ σ - 1)
    (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e) (F : Fin N → ℂ → ℂ)
    (cvec : Fin r → (Nat.Primes →₀ ℤ))
    (hlam : ∀ k, 0 < σ + RHTower.primeLogHom (cvec k))
    (cc : Fin N → Fin M → ℂ) (hcc : ∀ α i, cc α i ≠ 0) (ee : Fin N → Fin M → Fin r → ℕ)
    (q p : Fin N → Fin M → Polynomial ℂ) (hq : ∀ α i, q α i ≠ 0) (hp : ∀ α i, p α i ≠ 0)
    (bb : Fin N → Fin M → ℤ)
    (hdist : ∀ (α : Fin N) (i j : Fin M), i ≠ j →
      ¬(multiDegree (ee α i) = multiDegree (ee α j)
        ∧ multiExponent (fun k => RHTower.primeLogHom (cvec k)) (ee α i) (q α i) (p α i)
          = multiExponent (fun k => RHTower.primeLogHom (cvec k)) (ee α j) (q α j) (p α j)
        ∧ bb α i = bb α j))
    (hF : ∀ (α : Fin N) (t : ℝ), F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      = multiMonomialSum σ (fun k => RHTower.primeLogHom (cvec k)) (cc α) (ee α) (q α) (p α)
        (bb α) t)
    (hrel : ∀ s : ℂ,
      ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) riemannZeta s) ^ (e α i) = 0) :
    False :=
  zeta_no_gammaShiftMulti_relation hσ hN hM hr hρ hrρ hR hRσ e he F
    (fun k => RHTower.primeLogHom (cvec k)) hlam cc hcc ee q p hq hp bb hdist hF hrel

end

end GaloisForLFunctions.HTGeometry
