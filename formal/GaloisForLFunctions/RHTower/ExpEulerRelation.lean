import GaloisForLFunctions.RHTower.IntegralizedConjugateSet
import GaloisForLFunctions.RHTower.ReducedSubsetSumPoly
import GaloisForLFunctions.RHTower.OrbitSumDegree
import GaloisForLFunctions.RHTower.ScaledHermiteContradiction

/-!
# The non-monic Lindemann–Weierstrass contradiction

The analytic finish of Lindemann–Weierstrass for a Euler-type exponential relation over a *non-monic*
conjugate set.  If `μ ∈ ℤ[X]` is nonzero with leading coefficient `ℓ` and complete factorization
`μ.map = C ℓ · ∏_j (X − θ_j)`, and the subset-sum exponential relation
`∑_S exp(∑_{j∈S} θ_j) = 0` holds (the expansion of `∏_j (1 + e^{θ_j}) = 0`), a contradiction follows.

The mechanism is Hermite's, adapted to non-integer exponents.  The empty subset contributes `σ_∅ = 0`,
so the count `a₀ = #\{S : σ_S = 0\} ≥ 1` is the nondegeneracy — with the all-ones coefficient family
there is no sign cancellation.  Feed the reduced integer polynomial `g` (roots the nonzero `σ_S`) to
`exp_polynomial_approx`; the symmetric orbit sum `Φ = ∑_S aeval(∑_{j∈S} X_j) gp` is cleared to an
integer by `ℓ^{Φ.totalDegree}` (non-monic symmetric integrality), and `Φ.totalDegree ≤ gp.natDegree`
keeps the `ℓ`-power below `|ℓ|^{p·deg g}`.  The resulting integer
`J = a₀·n_p·ℓ^{Φ.totalDegree} + p·(T₀ − a₀·g_p(0)·ℓ^{Φ.totalDegree})` satisfies
`|J| ≤ (\#S)·(|ℓ|^{deg g}·B)^p/(p−1)! → 0`, so `J = 0`; but then `p ∣ a₀·n_p·ℓ^{Φ.totalDegree}`,
contradicting `p ∤ a₀`, `p ∤ n_p`, `p ∤ ℓ` for a large prime `p`.
-/

open Polynomial Finset
open scoped Nat

namespace GaloisForLFunctions.RHTower

theorem exp_euler_relation_ne {d : ℕ} (μ : ℤ[X]) (hμ0 : μ ≠ 0) (θ : Fin d → ℂ)
    (hθ : μ.map (Int.castRingHom ℂ)
        = C ((μ.leadingCoeff : ℤ) : ℂ) * (Multiset.map (fun j => X - C (θ j)) Finset.univ.val).prod)
    (hrel : ∑ S ∈ (Finset.univ : Finset (Fin d)).powerset, Complex.exp (∑ j ∈ S, θ j) = 0) :
    False := by
  classical
  set ℓ : ℤ := μ.leadingCoeff with hℓ
  have hℓ0 : ℓ ≠ 0 := by
    rw [hℓ]
    exact Polynomial.leadingCoeff_ne_zero.mpr hμ0
  set PS := (Finset.univ : Finset (Fin d)).powerset with hPS
  have hPSuniv : PS = (Finset.univ : Finset (Finset (Fin d))) := by
    ext S
    simp [hPS]
  set E : Finset (Fin d) → ℂ := fun S => ∑ j ∈ S, θ j with hE
  set a0 : ℤ := ((PS.filter (fun S => E S = 0)).card : ℤ) with ha0def
  have hemp : (∅ : Finset (Fin d)) ∈ PS.filter (fun S => E S = 0) := by
    rw [Finset.mem_filter, hPS, Finset.mem_powerset]
    exact ⟨Finset.empty_subset _, by simp [hE]⟩
  have ha0pos : 0 < a0 := by
    rw [ha0def]
    exact_mod_cast Finset.card_pos.mpr ⟨_, hemp⟩
  have ha0ne : a0 ≠ 0 := ne_of_gt ha0pos
  obtain ⟨g, hg0, hsubsetRoot⟩ := exists_reduced_subsetSum_poly μ hμ0 θ hθ
  refine exp_scaled_aggregate_zero_relation_ne E (fun _ => 1) g hg0 ?_
    ℓ a0 hℓ0 1 0 ?_ ?_ ha0ne ?_
  · intro S hS0
    exact hsubsetRoot S (by simp) (by simpa [hE] using hS0)
  · simpa [hE, hPSuniv] using hrel
  · rw [ha0def, hPSuniv]
    simp
  · intro q
    set Φ : MvPolynomial (Fin d) ℤ :=
      ∑ S ∈ PS, Polynomial.aeval (∑ j ∈ S, MvPolynomial.X (R := ℤ) j) q with hΦ
    have hΦsym : Φ.IsSymmetric := by
      intro σ
      rw [hΦ, map_sum]
      refine Finset.sum_nbij' (fun T => T.image σ) (fun T => T.image σ.symm) ?_ ?_ ?_ ?_ ?_
      · intro T _; simp [hPS]
      · intro T _; simp [hPS]
      · intro T _; simp [Finset.image_image]
      · intro T _; simp [Finset.image_image]
      · intro T _
        have hargeq : (MvPolynomial.rename σ) (∑ j ∈ T, MvPolynomial.X (R := ℤ) j)
            = ∑ j ∈ T.image σ, MvPolynomial.X (R := ℤ) j := by
          rw [map_sum, Finset.sum_image (fun a _ b _ h => σ.injective h)]
          exact Finset.sum_congr rfl (fun j _ => by simp [MvPolynomial.rename_X])
        rw [← Polynomial.aeval_algHom_apply, hargeq]
    obtain ⟨T, hT⟩ :=
      nonmonic_symmetric_aeval_isInt_of_factorization μ hμ0 θ hθ Φ hΦsym
    have hΦeval : MvPolynomial.aeval θ Φ =
        ∑ S ∈ PS, Polynomial.aeval (E S) q := by
      rw [hΦ, map_sum]
      refine Finset.sum_congr rfl (fun S _ => ?_)
      have harg : (MvPolynomial.aeval θ) (∑ j ∈ S, MvPolynomial.X (R := ℤ) j) = E S := by
        rw [hE, map_sum]
        refine Finset.sum_congr rfl (fun j _ => ?_)
        rw [MvPolynomial.aeval_X]
      rw [← Polynomial.aeval_algHom_apply, harg]
    refine ⟨Φ.totalDegree, T, ?_, ?_⟩
    · rw [hΦ, hPS]
      simpa using orbitSum_totalDegree_le q
    · rw [show ℓ = μ.leadingCoeff from hℓ]
      simp only [one_mul]
      rw [← hT, hΦeval]
      simp [hPS]

end GaloisForLFunctions.RHTower
