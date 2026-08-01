import GaloisForLFunctions.HTGeometry.DirichletBohrSpectrum
import GaloisForLFunctions.HTGeometry.StripAlmostPeriodicUniformLimit

/-!
# Independent frequencies force large rank

A family of frequencies of the hull that is independent over `ℤ` gives a linearly independent family
in the frequency group, so its cardinality bounds the rational rank from below.  For a Dirichlet
series every exponent with nonzero coefficient is such a frequency, so an independent family of `K+1`
exponents rules out the bound `K`.

Together with the contrapositive of the finite-phase law this is the mechanism of eq. (31): an
exponent group of infinite rational rank forces hypertranscendence over `ℂ(s)⟨Γ⟩`.
-/

open Filter Topology Complex

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- **Independent frequencies bound the rank from below.** -/
theorem cardinal_le_rank_of_independent_frequencies {f : ℝ →ᵇ ℂ} {ι : Type} (v : ι → ℝ)
    (hv : ∀ i, IsBohrHullFrequency f (v i)) (hind : LinearIndependent ℤ v) :
    Cardinal.mk ι ≤ Module.rank ℤ (bohrHullFrequencies f) := by
  classical
  set w : ι → bohrHullFrequencies f := fun i => ⟨v i, hv i⟩ with hw
  have hcomp : ((bohrHullFrequencies f).subtype.toIntLinearMap ∘ w) = v := by
    funext i
    rfl
  have hindw : LinearIndependent ℤ w := by
    refine LinearIndependent.of_comp (bohrHullFrequencies f).subtype.toIntLinearMap ?_
    rw [hcomp]
    exact hind
  exact hindw.cardinal_le_rank

/-- A family of `K+1` independent frequencies rules out the rank bound `K`. -/
theorem not_rank_le_of_independent_frequencies {f : ℝ →ᵇ ℂ} (K : ℕ) (v : Fin (K + 1) → ℝ)
    (hv : ∀ i, IsBohrHullFrequency f (v i)) (hind : LinearIndependent ℤ v) :
    ¬ (Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal)) := by
  intro hle
  have hcard := cardinal_le_rank_of_independent_frequencies v hv hind
  have hK : (Cardinal.mk (Fin (K + 1))) = ((K + 1 : ℕ) : Cardinal) := by simp
  rw [hK] at hcard
  have : ((K + 1 : ℕ) : Cardinal) ≤ (K : Cardinal) := le_trans hcard hle
  have hlt : (K : Cardinal) < ((K + 1 : ℕ) : Cardinal) := by
    exact_mod_cast Nat.lt_succ_self K
  exact absurd this (not_le.mpr hlt)

/-- **Independent exponents force large Bohr rank for a Dirichlet series.**  If `K+1` of the
exponents with nonzero coefficients are independent, the rational Bohr frequency rank of the series
exceeds `K`. -/
theorem not_rank_le_of_dirichlet_independent {σ : ℝ} (a : ℕ → ℂ) (lam : ℕ → ℝ) (D : ℂ → ℂ)
    (hinj : Function.Injective lam) {f : ℝ →ᵇ ℂ}
    (hf : ∀ x : ℝ, f x = D ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hDa : IsBohrAlmostPeriodic fun t : ℝ => D ((σ : ℂ) + (t : ℂ) * Complex.I))
    (K : ℕ) (idx : Fin (K + 1) → ℕ) (ha : ∀ i, a (idx i) ≠ 0)
    (hm : ∀ i : Fin (K + 1), ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, idx i < n₀ ∧ ∀ t : ℝ,
      ‖D ((σ : ℂ) + (t : ℂ) * Complex.I)
        - ∑ k ∈ Finset.range n₀,
          a k * Complex.exp (-(lam k : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ ε)
    (hind : LinearIndependent ℤ (fun i : Fin (K + 1) => -(lam (idx i)))) :
    ¬ (Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal)) := by
  refine not_rank_le_of_independent_frequencies K (fun i => -(lam (idx i))) (fun i => ?_) hind
  exact isBohrHullFrequency_dirichlet a lam D hinj hf hDa (idx i) (ha i) (hm i)

end GaloisForLFunctions
