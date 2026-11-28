import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothRepresentationScalarTwist
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.BlockUnipotentRadicals
import Mathlib.Topology.Algebra.Group.Matrix

/-! The determinant is trivial on every unipotent radical, so a
determinant character twist preserves all Jacquet relations.
On scalar matrices the central character is multiplied by the
rank-th power of the twisting character. -/

noncomputable section

open Matrix Representation

namespace GlobalTheory.GLp

variable {k : Type} [Field k] {n : ℕ}

theorem det_eq_one_of_mem_blockUnipotentRadical (b : Fin n → ℕ)
    (x : GL (Fin n) k) (hx : x ∈ blockUnipotentRadical k b) :
    GeneralLinearGroup.det x = 1 := by
  apply Units.ext
  change x.val.det = 1
  have htri : x.val.BlockTriangular b := blockTriangular_of_sub_one (show IsStrictBlockUpper b (x.val - 1) from hx)
  rw [htri.det]
  refine Finset.prod_eq_one fun c _ => ?_
  have h : x.val.toSquareBlock b c = 1 := by
    apply Matrix.ext
    intro i j
    have hij : b j.val ≤ b i.val := j.2.trans_le i.2.symm.le
    have he := mem_blockUnipotentRadical.mp hx i.val j.val hij
    rw [Matrix.sub_apply, sub_eq_zero] at he
    change x.val i.val j.val = (1 : Matrix {a : Fin n // b a = c} {a : Fin n // b a = c} k) i j
    rw [he]
    simp [Matrix.one_apply, Subtype.val_injective.eq_iff]
  rw [h, Matrix.det_one]

variable [TopologicalSpace k] [IsTopologicalRing k]
  {V : Type} [AddCommGroup V] [Module ℂ V]

theorem isSmoothCuspidal_of_determinantTwist
    (ρ : Representation ℂ (GL (Fin n) k) V) (hρ : IsSmoothCuspidal ρ)
    (χ : kˣ →* ℂˣ) (hχ : IsOpen (χ.ker : Set kˣ)) :
    IsSmoothCuspidal (ρ.scalarTwist (χ.comp GeneralLinearGroup.det)) := by
  refine ⟨scalarTwist_smooth ρ hρ.1 _ (hχ.preimage GeneralLinearGroup.continuous_det), fun b hb => ?_⟩
  have he : (ρ.scalarTwist (χ.comp GeneralLinearGroup.det)).comp
      (blockUnipotentRadical k b).subtype = ρ.comp (blockUnipotentRadical k b).subtype := by
    apply MonoidHom.ext
    intro g
    apply LinearMap.ext
    intro v
    change (χ (GeneralLinearGroup.det g.val) : ℂ) • ρ g.val v = ρ g.val v
    rw [det_eq_one_of_mem_blockUnipotentRadical b g.val g.2, map_one, Units.val_one, one_smul]
  rw [he]
  exact hρ.2 b hb

theorem determinantTwist_centralCharacter
    (ρ : Representation ℂ (GL (Fin n) k) V) (ω χ : kˣ →* ℂˣ)
    (hω : ∀ z v, ρ (GeneralLinearGroup.scalar (Fin n) z) v = (ω z : ℂ) • v)
    (z : kˣ) (v : V) :
    ρ.scalarTwist (χ.comp GeneralLinearGroup.det) (GeneralLinearGroup.scalar (Fin n) z) v =
      ((ω * χ ^ n) z : ℂ) • v := by
  rw [scalarTwist_apply, MonoidHom.comp_apply, GeneralLinearGroup.det_scalar, Fintype.card_fin,
    map_pow, hω, smul_smul, MonoidHom.mul_apply, MonoidHom.pow_apply, Units.val_mul, mul_comm]

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.isSmoothCuspidal_of_determinantTwist
#print axioms GlobalTheory.GLp.determinantTwist_centralCharacter
