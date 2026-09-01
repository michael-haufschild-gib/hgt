import GaloisForLFunctions.HTGeometry.RittLogTowerCollapse
import GaloisForLFunctions.HTGeometry.RittLogTowerFirstOrder

/-!
# The rational affine connection from a collapse of the affine tower

Once the top weight of the collapsing polynomial is pinned to `n + 1`, the next weight layer of the
relation has multiplier

`ρ^{J + W - 1} = ρ^{-(n+1) + n} = ρ^{-1}`,

which is never trivial.  So every weight `n` monomial occurring in the collapsing polynomial
produces an obstruction: an affine transport equation with multiplier `ρ^{-1}` when the layer's
inhomogeneity is nonzero, and Ritt's order-one form when it vanishes.
-/

namespace GaloisForLFunctions.HTGeometry

namespace RittFrame

open MvPolynomial

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}

/-- **The weight `n` layer of a collapse is a rational affine connection.** -/
theorem affine_connection_of_collapse (Fr : RittFrame K L) {u : L} {b : K}
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b)
    (hind : AlgebraicIndependent K (Fr.jetFamily u n))
    {F : MvPolynomial (Fin n) K} (hF : WLe n F (n + 1))
    (hcol : Fr.σ (aeval (Fr.jetFamily u n) F)
      = algebraMap K L ((Fr.ρ ^ (n + 1))⁻¹) * aeval (Fr.jetFamily u n) F
        + Fr.towerDefect u b n)
    {d : Fin n →₀ ℕ} (hd : Finsupp.weight (jetWeight n) d + 1 = n + 1) :
    Fr.ψ (coeff d F) = Fr.ρ ^ (-1 : ℤ) * coeff d F
      + Fr.ρ ^ n * (coeff d (Fr.defectPoly b n)
        - coeff d (Fr.towerShift2 b n
            (weightedHomogeneousComponent (jetWeight n) (n + 1) F))) := by
  have hρ : (Fr.ρ : K) ≠ 0 := Fr.ρ_ne
  have hJ : (Fr.ρ : K) ^ (-((n : ℤ) + 1)) = (Fr.ρ ^ (n + 1))⁻¹ := by
    rw [zpow_neg, show ((n : ℤ) + 1) = ((n + 1 : ℕ) : ℤ) by push_cast; ring, zpow_natCast]
  have hcol' : Fr.σ (aeval (Fr.jetFamily u n) F)
      = algebraMap K L ((Fr.ρ : K) ^ (-((n : ℤ) + 1))) * aeval (Fr.jetFamily u n) F
        + aeval (Fr.jetFamily u n) (Fr.defectPoly b n) := by
    rw [hJ, Fr.aeval_defectPoly u b n]
    exact hcol
  have hpoly : Fr.towerShift b n F
      = C ((Fr.ρ : K) ^ (-((n : ℤ) + 1))) * F + Fr.defectPoly b n :=
    Fr.towerShift_eq_of_collapse hu hind hcol'
  have h := Fr.second_base_relation_of_towerShift b hF hpoly hd
  have hsucc : (n + 1) - 1 = n := by omega
  rw [hsucc] at h
  rw [h]
  congr 2
  rw [← zpow_natCast (Fr.ρ) n, ← zpow_add₀ hρ]
  congr 1
  ring

/-- **A weight `n` monomial of the collapsing polynomial produces an obstruction.** -/
theorem exists_obstruction_of_collapse_second (Fr : RittFrame K L) {u : L} {b : K}
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b)
    (hind : AlgebraicIndependent K (Fr.jetFamily u n))
    {F : MvPolynomial (Fin n) K} (hF : WLe n F (n + 1))
    (hcol : Fr.σ (aeval (Fr.jetFamily u n) F)
      = algebraMap K L ((Fr.ρ ^ (n + 1))⁻¹) * aeval (Fr.jetFamily u n) F
        + Fr.towerDefect u b n)
    {d : Fin n →₀ ℕ} (hd : Finsupp.weight (jetWeight n) d + 1 = n + 1)
    (hdne : coeff d F ≠ 0) :
    (∃ (w : K) (J : ℤ), w ≠ 0 ∧ J ≠ 0 ∧ Fr.ψ w = Fr.ρ ^ J * w) ∨
    (∃ (w h : K) (J : ℤ), w ≠ 0 ∧ h ≠ 0 ∧ Fr.ψ w = Fr.ρ ^ J * w + h) := by
  have h := Fr.affine_connection_of_collapse hu hind hF hcol hd
  set hh : K := Fr.ρ ^ n * (coeff d (Fr.defectPoly b n)
    - coeff d (Fr.towerShift2 b n
        (weightedHomogeneousComponent (jetWeight n) (n + 1) F))) with hhdef
  by_cases hz : hh = 0
  · refine Or.inl ⟨coeff d F, -1, hdne, by omega, ?_⟩
    rw [h, hz, add_zero]
  · exact Or.inr ⟨coeff d F, hh, -1, hdne, hz, h⟩

end RittFrame

end GaloisForLFunctions.HTGeometry
