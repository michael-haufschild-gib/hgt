/-
# Globalising a quadratic-rate escape over a linear Hamiltonian family

A fixed shell is a *linear* family `H(θ) = ∑ θ_a P_a`, so its matrix entries are linear polynomials
in the coefficients and the labeling-orbit obstruction of a quadratic-rate relation is an honest
polynomial in `θ`.  One coefficient vector carrying a simple spectrum on which no relabeling holds
therefore forces the same failure somewhere inside every nonempty open set of *real* coefficients:
a nonzero polynomial cannot vanish on a nonempty open set of reals.

This is the globalisation step of a fixed-shell nonflatness theorem, stated for an arbitrary linear
family so that any architecture -- a Pauli shell, a leaf-extended tensor tree, a one-qubit
extension chart -- can be fed to it.

Main results:
* `genericShellMatrix`, `map_genericShellMatrix` — the family as a polynomial matrix family.
* `exists_eval_shellPullback_ne_zero` — the witness makes the pullback a nonzero polynomial.
* `exists_mem_real_shell_quadraticRate_ne_zero` — **the globalisation**.
-/
import GaloisForLFunctions.HTGeometry.PhysicalChartCoordinates

open Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {S : Type*} [Fintype S] [DecidableEq S] {m : ℕ}

/-- A linear Hamiltonian family as a matrix of polynomials in its coefficients. -/
def genericShellMatrix (P : Fin m → Matrix S S ℂ) :
    Matrix S S (MvPolynomial (Fin m) ℂ) :=
  fun x y => ∑ a, MvPolynomial.C (P a x y) * MvPolynomial.X a

omit [Fintype S] [DecidableEq S] in
/-- **The family evaluates to the shell Hamiltonian.** -/
theorem map_genericShellMatrix (P : Fin m → Matrix S S ℂ) (θ : Fin m → ℂ) :
    (genericShellMatrix P).map (MvPolynomial.eval₂Hom (RingHom.id ℂ) θ)
      = ∑ a, θ a • P a := by
  refine Matrix.ext fun x y => ?_
  rw [Matrix.map_apply, genericShellMatrix, Matrix.sum_apply]
  show MvPolynomial.eval₂ (RingHom.id ℂ) θ (∑ a, MvPolynomial.C (P a x y) * MvPolynomial.X a) = _
  rw [MvPolynomial.eval₂_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [MvPolynomial.eval₂_mul, MvPolynomial.eval₂_C, MvPolynomial.eval₂_X, Matrix.smul_apply,
    smul_eq_mul, RingHom.id_apply]
  ring

/-- **One coefficient vector makes the pullback a nonzero polynomial.** -/
theorem exists_eval_shellPullback_ne_zero (P : Fin m → Matrix S S ℂ) (c : S → ℂ) (κ : ℂ)
    {θ₀ : Fin m → ℂ} {energy₀ : S → ℂ} (hinj₀ : Function.Injective energy₀)
    (hroot₀ : ∀ i, matrixCharpolyRelation (∑ a, θ₀ a • P a, energy₀ i) = 0)
    (hfail : ∀ σ : Equiv.Perm S,
      (∑ j, c (σ.symm j) * energy₀ j) ^ (2 : ℕ) - κ * ∑ j, energy₀ j ^ (2 : ℕ) ≠ 0) :
    ∃ θ : Fin m → ℂ, MvPolynomial.eval₂ (RingHom.id ℂ) θ
      (quadraticRateObstructionPullback (genericShellMatrix P) c κ) ≠ 0 := by
  refine ⟨θ₀, ?_⟩
  have hroot : ∀ i, matrixCharpolyRelation
      ((genericShellMatrix P).map (MvPolynomial.eval₂Hom (RingHom.id ℂ) θ₀), energy₀ i) = 0 := by
    intro i
    rw [map_genericShellMatrix]
    exact hroot₀ i
  rw [eval_quadraticRateObstructionPullback _ c κ θ₀ energy₀ hinj₀ hroot]
  intro hzero
  obtain ⟨σ, hσ⟩ := (fieldQuadraticRateOrbitValue_eq_zero_iff c κ energy₀).mp hzero
  exact hfail σ hσ

/-- **The globalisation.**  One good coefficient vector forces, inside every nonempty open set of
real coefficients, a Hamiltonian on whose simple root packets no relabeling of the quadratic-rate
relation holds. -/
theorem exists_mem_real_shell_quadraticRate_ne_zero (P : Fin m → Matrix S S ℂ) (c : S → ℂ) (κ : ℂ)
    {θ₀ : Fin m → ℂ} {energy₀ : S → ℂ} (hinj₀ : Function.Injective energy₀)
    (hroot₀ : ∀ i, matrixCharpolyRelation (∑ a, θ₀ a • P a, energy₀ i) = 0)
    (hfail : ∀ σ : Equiv.Perm S,
      (∑ j, c (σ.symm j) * energy₀ j) ^ (2 : ℕ) - κ * ∑ j, energy₀ j ^ (2 : ℕ) ≠ 0)
    {V : Set (Fin m → ℝ)} (hVopen : IsOpen V) (hVne : V.Nonempty) :
    ∃ q ∈ V, ∀ energy : S → ℂ, Function.Injective energy →
      (∀ i, matrixCharpolyRelation (∑ a, ((q a : ℝ) : ℂ) • P a, energy i) = 0) →
      ∀ σ : Equiv.Perm S,
        (∑ j, c (σ.symm j) * energy j) ^ (2 : ℕ) - κ * ∑ j, energy j ^ (2 : ℕ) ≠ 0 := by
  obtain ⟨q, hq, hqne⟩ := exists_mem_eval₂_ne_zero_of_exists _
    (exists_eval_shellPullback_ne_zero P c κ hinj₀ hroot₀ hfail) hVopen hVne
  refine ⟨q, hq, fun energy hinj hroot σ hσ => hqne ?_⟩
  have hroot' : ∀ i, matrixCharpolyRelation
      ((genericShellMatrix P).map
        (MvPolynomial.eval₂Hom (RingHom.id ℂ) (fun a => ((q a : ℝ) : ℂ))), energy i) = 0 := by
    intro i
    rw [map_genericShellMatrix]
    exact hroot i
  rw [eval_quadraticRateObstructionPullback _ c κ (fun a => ((q a : ℝ) : ℂ)) energy hinj hroot']
  exact (fieldQuadraticRateOrbitValue_eq_zero_iff c κ energy).mpr ⟨σ, hσ⟩

end

end GaloisForLFunctions.HTGeometry
