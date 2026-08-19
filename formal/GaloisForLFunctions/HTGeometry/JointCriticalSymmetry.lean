/-
# The symmetrised criticality product is invariant under relabelling the spectrum

Relabelling the spectral variables translates the labelling of the spectral action and fixes the
coordinate variables, so it permutes the factors of the criticality product.  The product over all
labellings is therefore invariant, which is the symmetry that lets the construction descend to the
shell coordinates.

Main results:
* `rename_sumMap_jointAction`, `rename_sumMap_rename_inr` — the two elementary translations.
* `rename_sumMap_jointCriticality` — the criticality expression translates.
* `rename_sumMap_jointCriticalProduct` — **the product is invariant**.
-/
import GaloisForLFunctions.HTGeometry.JointCriticalProduct

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {N D : ℕ}

theorem rename_sumMap_rename_inr (τ : Equiv.Perm (Fin D)) (p : MvPolynomial (Fin N) ℝ) :
    MvPolynomial.rename (Sum.map (τ : Fin D → Fin D) (id : Fin N → Fin N))
        (MvPolynomial.rename (Sum.inr : Fin N → Fin D ⊕ Fin N) p)
      = MvPolynomial.rename (Sum.inr : Fin N → Fin D ⊕ Fin N) p := by
  rw [MvPolynomial.rename_rename]
  rfl

theorem rename_sumMap_jointAction (k : Fin D → ℝ) (π τ : Equiv.Perm (Fin D)) :
    MvPolynomial.rename (Sum.map (τ : Fin D → Fin D) (id : Fin N → Fin N))
        (jointAction (N := N) k π)
      = jointAction k (τ * π) := by
  rw [jointAction, jointAction, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, MvPolynomial.rename_C, MvPolynomial.rename_X]
  rfl

theorem rename_sumMap_jointCriticality (M : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ) (k : Fin D → ℝ)
    (π τ : Equiv.Perm (Fin D)) (i : Fin N) :
    MvPolynomial.rename (Sum.map (τ : Fin D → Fin D) (id : Fin N → Fin N))
        (jointCriticality M c k π i)
      = jointCriticality M c k (τ * π) i := by
  have hA : ∀ n : ℕ,
      MvPolynomial.rename (Sum.map (τ : Fin D → Fin D) (id : Fin N → Fin N))
        (MvPolynomial.rename Sum.inr (MvPolynomial.pderiv i (c n))
          * MvPolynomial.rename Sum.inr (normSqPoly N) * (jointAction k π) ^ n)
      = MvPolynomial.rename Sum.inr (MvPolynomial.pderiv i (c n))
          * MvPolynomial.rename Sum.inr (normSqPoly N) * (jointAction k (τ * π)) ^ n := by
    intro n
    rw [map_mul, map_mul, map_pow, rename_sumMap_rename_inr, rename_sumMap_rename_inr,
      rename_sumMap_jointAction]
  have hB : ∀ n : ℕ,
      MvPolynomial.rename (Sum.map (τ : Fin D → Fin D) (id : Fin N → Fin N))
        (MvPolynomial.C ((n : ℕ) : ℝ) * MvPolynomial.rename Sum.inr (c n)
          * (jointAction k π) ^ (n - 1))
      = MvPolynomial.C ((n : ℕ) : ℝ) * MvPolynomial.rename Sum.inr (c n)
          * (jointAction k (τ * π)) ^ (n - 1) := by
    intro n
    rw [map_mul, map_mul, map_pow, MvPolynomial.rename_C, rename_sumMap_rename_inr,
      rename_sumMap_jointAction]
  have hX : MvPolynomial.rename (Sum.map (τ : Fin D → Fin D) (id : Fin N → Fin N))
      ((MvPolynomial.X (Sum.inr i : Fin D ⊕ Fin N)) : MvPolynomial (Fin D ⊕ Fin N) ℝ)
      = ((MvPolynomial.X (Sum.inr i : Fin D ⊕ Fin N)) : MvPolynomial (Fin D ⊕ Fin N) ℝ) := by
    rw [MvPolynomial.rename_X]
    rfl
  have hsum1 : MvPolynomial.rename (Sum.map (τ : Fin D → Fin D) (id : Fin N → Fin N))
      (∑ n ∈ Finset.range (M + 1),
        MvPolynomial.rename Sum.inr (MvPolynomial.pderiv i (c n))
          * MvPolynomial.rename Sum.inr (normSqPoly N) * (jointAction k π) ^ n)
      = ∑ n ∈ Finset.range (M + 1),
        MvPolynomial.rename Sum.inr (MvPolynomial.pderiv i (c n))
          * MvPolynomial.rename Sum.inr (normSqPoly N) * (jointAction k (τ * π)) ^ n := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun n _ => hA n
  have hsum2 : MvPolynomial.rename (Sum.map (τ : Fin D → Fin D) (id : Fin N → Fin N))
      (∑ n ∈ Finset.range (M + 1),
        MvPolynomial.C ((n : ℕ) : ℝ) * MvPolynomial.rename Sum.inr (c n)
          * (jointAction k π) ^ (n - 1))
      = ∑ n ∈ Finset.range (M + 1),
        MvPolynomial.C ((n : ℕ) : ℝ) * MvPolynomial.rename Sum.inr (c n)
          * (jointAction k (τ * π)) ^ (n - 1) := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun n _ => hB n
  simp only [jointCriticality]
  rw [map_add, hsum1, map_mul, hsum2, map_mul, rename_sumMap_jointAction, hX]

theorem rename_sumMap_jointCriticalitySquareSum (M : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ)
    (k : Fin D → ℝ) (π τ : Equiv.Perm (Fin D)) :
    MvPolynomial.rename (Sum.map (τ : Fin D → Fin D) (id : Fin N → Fin N))
        (jointCriticalitySquareSum M c k π)
      = jointCriticalitySquareSum M c k (τ * π) := by
  have hterm : ∀ i : Fin N,
      MvPolynomial.rename (Sum.map (τ : Fin D → Fin D) (id : Fin N → Fin N))
        ((jointCriticality M c k π i) ^ 2)
      = (jointCriticality M c k (τ * π) i) ^ 2 := by
    intro i
    rw [map_pow, rename_sumMap_jointCriticality]
  simp only [jointCriticalitySquareSum]
  rw [map_sum, Finset.sum_congr rfl (fun i _ => hterm i)]

/-- **The symmetrised criticality product is invariant under relabelling the spectrum.** -/
theorem rename_sumMap_jointCriticalProduct (M : ℕ) (c : ℕ → MvPolynomial (Fin N) ℝ)
    (k : Fin D → ℝ) (τ : Equiv.Perm (Fin D)) :
    MvPolynomial.rename (Sum.map (τ : Fin D → Fin D) (id : Fin N → Fin N))
        (jointCriticalProduct M c k)
      = jointCriticalProduct M c k := by
  classical
  simp only [jointCriticalProduct]
  rw [map_prod,
    Finset.prod_congr rfl fun π _ => rename_sumMap_jointCriticalitySquareSum M c k π τ]
  exact Fintype.prod_equiv (Equiv.mulLeft τ) _ _ fun π => rfl

end

end GaloisForLFunctions.HTGeometry
