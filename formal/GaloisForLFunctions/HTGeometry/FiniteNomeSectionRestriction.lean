import GaloisForLFunctions.HTGeometry.OccupationEulerProduct
import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGammaExhaustion
import GaloisForLFunctions.HTGeometry.InfiniteMultipleEllipticGammaMomentForm

/-!
# A finite section is the product of the restricted nome family

Occupations supported on a finite nome set are exactly the occupations of the restricted family, so
the finite section of the infinite-order product is literally the infinite-order product of that
restriction.  Everything already proved for arbitrary nome families therefore applies verbatim to
every finite section, with all summability hypotheses automatic.

In particular the finite section has the same regularized free energy, whose coefficients are the
finite Euler products over the nome set.
-/

namespace HTGeometry

open scoped BigOperators

/-- **The finite section is a restricted infinite product.** -/
theorem finiteNomeSection_eq_restricted {ι : Type*} (g : ℕ) (p : ι → ℂ) (S : Finset ι) (t : ℂ) :
    finiteNomeSection g p S t
      = infiniteMultipleEllipticGamma g (fun a : S => p a) t := by
  classical
  set e : (S →₀ ℕ) ≃ {ν : ι →₀ ℕ // ν.support ⊆ S} :=
    (Finsupp.equivFunOnFinite (α := S) (M := ℕ)).trans (supportedOccupationEquiv S) with hedef
  have hval : ∀ c : S →₀ ℕ,
      nomeMonomial p (e c).1 = nomeMonomial (fun a : S => p a) c := by
    intro c
    rw [hedef, Equiv.trans_apply, nomeMonomial_supportedOccupationEquiv, nomeMonomial,
      Finsupp.prod_fintype]
    · rfl
    · intro a
      simp
  calc finiteNomeSection g p S t
      = ∏' ν : ι →₀ ℕ, Set.mulIndicator {ν : ι →₀ ℕ | ν.support ⊆ S}
          (fun ν => primaryFactor g (t * nomeMonomial p ν)) ν := by
        rw [finiteNomeSection]
        refine tprod_congr fun ν => ?_
        by_cases hν : ν.support ⊆ S
        · rw [if_pos hν, Set.mulIndicator_of_mem hν]
        · rw [if_neg hν, Set.mulIndicator_of_notMem hν]
    _ = ∏' ν : {ν : ι →₀ ℕ // ν.support ⊆ S}, primaryFactor g (t * nomeMonomial p ν.1) :=
        (tprod_subtype {ν : ι →₀ ℕ | ν.support ⊆ S}
          (fun ν => primaryFactor g (t * nomeMonomial p ν))).symm
    _ = ∏' c : S →₀ ℕ, primaryFactor g (t * nomeMonomial p (e c).1) :=
        (Equiv.tprod_eq e (fun ν : {ν : ι →₀ ℕ // ν.support ⊆ S} =>
          primaryFactor g (t * nomeMonomial p ν.1))).symm
    _ = ∏' c : S →₀ ℕ, primaryFactor g (t * nomeMonomial (fun a : S => p a) c) := by
        refine tprod_congr fun c => ?_
        rw [hval c]
    _ = infiniteMultipleEllipticGamma g (fun a : S => p a) t := rfl

/-- **The free energy of a finite section.**  Its moment coefficients are the finite Euler products
over the nome set. -/
theorem finiteNomeSection_eq_exp_neg_moments {ι : Type*} (g : ℕ) (p : ι → ℂ)
    (hp_lt : ∀ a, ‖p a‖ < 1) (S : Finset ι) {t : ℂ} (ht : ‖t‖ < 1) :
    finiteNomeSection g p S t
      = Complex.exp (-∑' m : ℕ, t ^ (m + (g + 1)) / ((m + (g + 1) : ℕ) : ℂ) *
          ∏ a ∈ S, (1 - p a ^ (m + (g + 1)))⁻¹) := by
  classical
  rw [finiteNomeSection_eq_restricted,
    infiniteMultipleEllipticGamma_eq_exp_neg_moments g (fun a : S => p a)
      (fun a => hp_lt a) Summable.of_finite ht]
  congr 2
  refine tsum_congr fun m => ?_
  congr 1
  rw [tprod_fintype]
  exact (Finset.prod_subtype S (fun _ => Iff.rfl)
    (fun a => (1 - p a ^ (m + (g + 1)))⁻¹)).symm

end HTGeometry
