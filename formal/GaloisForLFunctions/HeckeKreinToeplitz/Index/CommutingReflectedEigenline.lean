import GaloisForLFunctions.HeckeKreinToeplitz.Index.ReflectedNullEigenvector
import GaloisForLFunctions.HeckeKreinToeplitz.HyperbolicPairsAndTheIndexFormula

/-!
# A common reflected eigenline

For a commuting family of index-one isometries, a nonunitary common
eigencharacter has a common reflected eigencharacter. A single off-circle
operator supplies the companion vector; its one-dimensional eigenspace
forces every commuting operator to preserve that vector's line.
-/

noncomputable section
set_option autoImplicit false
open Complex
open scoped ComplexConjugate

namespace GaloisForLFunctions.HeckeKreinToeplitz.IndexOne

variable {G H : Type*} [Group G] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A common nonunitary eigencharacter has a reflected common null line with pairing one. -/
theorem exists_common_reflected_null_eigenvector
    (T : G → (H × ℂ) ≃L[ℂ] (H × ℂ))
    (hT : ∀ g u v, pairing (T g u) (T g v) = pairing u v)
    (hcomm : ∀ g h u, T g (T h u) = T h (T g u))
    (χ : G →* ℂ) (hχ : ¬ IsUnitaryChar χ) {z : H}
    (hw : ∀ g, T g (nullVector z) = χ g • nullVector z) :
    pairing (nullVector z) (nullVector z) = 0 ∧
      ∃ v : H × ℂ, pairing (nullVector z) v = 1 ∧ pairing v v = 0 ∧
        ∀ g, T g v = reflectChar χ g • v := by
  have hnot : ¬ ∀ g, ‖χ g‖ = 1 := hχ
  obtain ⟨g, hg⟩ := not_forall.mp hnot
  have hwq := pairing_self_eq_zero_of_nonunit_eigenvalue
    (T g).toContinuousLinearMap.toLinearMap (hT g) hg (hw g)
  obtain ⟨v, hpair, heig, hvq⟩ := exists_reflected_null_eigenvector
    (T g).toLinearEquiv (hT g) hg (hw g)
  change T g v = (conj (χ g))⁻¹ • v at heig
  have hv0 : v ≠ 0 := by
    intro he
    rw [he] at hpair
    simp only [pairing, Prod.fst_zero, Prod.snd_zero, inner_zero_right, mul_zero, sub_self] at hpair
    exact zero_ne_one hpair
  refine ⟨hwq, v, hpair, hvq, fun h => ?_⟩
  have hμ : ‖(conj (χ g))⁻¹‖ ≠ 1 := by
    have hn : ‖χ g‖⁻¹ ≠ 1 := fun h => hg (_root_.inv_eq_one.mp h)
    simpa only [norm_inv, norm_conj] using hn
  have hTh : T g (T h v) = (conj (χ g))⁻¹ • T h v := by
    rw [hcomm, heig, map_smul]
  have hscalar := eigenvector_eq_scalar_mul_of_nonunit
    (T g).toContinuousLinearMap.toLinearMap (hT g) hμ heig hTh hv0
  let c : ℂ := (T h v).2 / v.2
  have hcv : T h v = c • v := hscalar
  have he := hT h (nullVector z) v
  rw [hw h, hcv, pairing_smul_left, pairing_smul_right, hpair, mul_one] at he
  have hχ0 : conj (χ h) ≠ 0 := star_ne_zero.mpr (map_ne_zero χ h)
  have hc : c = (conj (χ h))⁻¹ := by
    calc
      c = (conj (χ h))⁻¹ * (conj (χ h) * c) := by
        rw [← mul_assoc, inv_mul_cancel₀ hχ0, one_mul]
      _ = _ := by rw [he, mul_one]
  rw [hcv, hc, reflectChar_apply, map_inv_eq_inv, map_inv₀]

end GaloisForLFunctions.HeckeKreinToeplitz.IndexOne
