import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothRepresentationScalarTwist
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.HarishChandraCuspidalRestriction
import Mathlib.RepresentationTheory.FinGroupCharZero

/-! A determinant twist preserves the cuspidality of a finite
character. The determinant is one on each two-block radical. -/

noncomputable section

open Matrix Representation CategoryTheory
open GaloisForLFunctions WindowedLandauTheory.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.GLq

variable {p n : ℕ} [Fact p.Prime]

private theorem det_eq_one_of_twoBlockLevi_eq_one {a b : ℕ}
    (x : twoBlockParabolic p a b)
    (hx : twoBlockLevi x = ((1 : Gn p a), (1 : Gn p b))) :
    GeneralLinearGroup.det x.val = 1 := by
  let M : Mt p (a + b) := x.val.val
  let e := finSumFinEquiv (m := a) (n := b)
  have htl : tl a M = 1 := by
    have he := congrArg (fun y : Gn p a × Gn p b => y.1.val) hx
    exact he
  have hbr : br a b M = 1 := by
    have he := congrArg (fun y : Gn p a × Gn p b => y.2.val) hx
    exact he
  have hM : M.submatrix e e =
      Matrix.fromBlocks (tl a M) (fun i j => M (Fin.castAdd b i) (Fin.natAdd a j)) 0 (br a b M) := by
    apply Matrix.ext
    rintro (i | i) (j | j)
    · exact (tl_apply_add M i j).symm
    · rfl
    · exact x.2 _ _ j.isLt (by change a ≤ a + i.val; omega)
    · exact (br_apply_add M i j).symm
  apply Units.ext
  change M.det = 1
  rw [← Matrix.det_submatrix_equiv_self e M, hM, det_fromBlocks_zero₂₁, htl, hbr, det_one, det_one, mul_one]

/-- The finite representation obtained by twisting through determinant. -/
def finiteDeterminantTwist (τ : FDRep ℂ (Gn p n)) (δ : (ZMod p)ˣ →* ℂˣ) :
    FDRep ℂ (Gn p n) :=
  FDRep.of (Representation.scalarTwist τ.ρ (δ.comp GeneralLinearGroup.det))

theorem finiteDeterminantTwist_character (τ : FDRep ℂ (Gn p n)) (δ : (ZMod p)ˣ →* ℂˣ)
    (x : Gn p n) : (finiteDeterminantTwist τ δ).character x = τ.character x * (δ x.det : ℂ) := by
  change LinearMap.trace ℂ τ.V ((δ x.det : ℂ) • τ.ρ x) = _
  rw [map_smul, smul_eq_mul, mul_comm]
  rfl

private theorem simple_finiteDeterminantTwist (τ : FDRep ℂ (Gn p n)) [Simple τ]
    (δ : (ZMod p)ˣ →* ℂˣ) : Simple (finiteDeterminantTwist τ δ) := by
  classical
  letI : Fintype (Gn p n) := Fintype.ofFinite _
  have hnorm := (FDRep.simple_iff_char_is_norm_one τ).mp (inferInstance : Simple τ)
  rw [FDRep.simple_iff_char_is_norm_one, ← hnorm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [finiteDeterminantTwist_character, finiteDeterminantTwist_character, map_inv, map_inv,
    Units.val_inv_eq_inv_val]
  calc
    _ = (τ.character x * τ.character x⁻¹) * ((δ x.det : ℂ) * (δ x.det : ℂ)⁻¹) := by ac_rfl
    _ = _ := by rw [mul_inv_cancel₀ (Units.ne_zero _), mul_one]

theorem isCusp_finiteDeterminantTwist (τ : FDRep ℂ (Gn p n)) (hτ : IsCusp τ.character)
    (δ : (ZMod p)ˣ →* ℂˣ) : IsCusp (finiteDeterminantTwist τ δ).character := by
  classical
  haveI : Simple τ := by
    obtain ⟨S, hS, hchar⟩ := hτ.2.1
    letI : Fintype (Gn p n) := Fintype.ofFinite _
    rw [FDRep.simple_iff_char_is_norm_one] at hS ⊢
    simpa only [hchar] using hS
  refine ⟨hτ.1, ⟨finiteDeterminantTwist τ δ, simple_finiteDeterminantTwist τ δ, fun _ => rfl⟩,
    fun a ha ha' => ?_⟩
  have h0 := hτ.2.2 a ha ha'
  generalize he : n - a = b at h0 ⊢
  have hsum : a + b = n := he ▸ Nat.add_sub_of_le ha'.le
  subst n
  rw [res_eq_sum_diagonal_fibre] at h0 ⊢
  let P := twoBlockParabolic p a b
  have hsum : (∑ x : P, if twoBlockLevi x = (1, 1) then (finiteDeterminantTwist τ δ).character x.val else 0) =
      ∑ x : P, if twoBlockLevi x = (1, 1) then τ.character x.val else 0 := by
    refine Finset.sum_congr rfl fun x _ => ?_
    split_ifs with hx
    · rw [finiteDeterminantTwist_character, det_eq_one_of_twoBlockLevi_eq_one x hx, map_one, Units.val_one, mul_one]
    · rfl
  exact (congrArg (((p : ℂ) ^ (a * b))⁻¹ * ·) hsum).trans h0

end GlobalTheory.GLq

#print axioms GlobalTheory.GLq.isCusp_finiteDeterminantTwist
