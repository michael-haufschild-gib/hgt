import GaloisForLFunctions.RepresentationLifting.Differential.NilpotentLogarithmicResidue
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Polynomial.AlgebraMap
import Mathlib.Tactic.Ring

/-!
# Logarithmic p-curvature and nilpotent residue filtrations

For the coefficientwise connection D = Euler − N over the prime field,
Dᵖ − D is the constant operator N − Nᵖ. For nilpotent N, the factor
1 − N^(p−1) is an invertible operator commuting with N. Consequently
p-curvature preserves every kernel and image in the residue's power
filtration, including its exact nilpotency order.

This refines the exponent splitting in Fersi, arXiv:2611.20395, §4.4,
by retaining the nilpotent residue on each logarithmic coefficient block.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.DividedPower
open Polynomial
variable (p : ℕ) [Fact p.Prime] {W : Type*} [AddCommGroup W] [Module (ZMod p) W]

/-- The residue contribution to logarithmic p-curvature. -/
def residueCurvature (N : Module.End (ZMod p) W) : Module.End (ZMod p) W := N - N ^ p

private theorem scalar_block_curvature (N : Module.End (ZMod p) W) (c : ZMod p) :
    (c • (1 : Module.End (ZMod p) W) - N) ^ p - (c • 1 - N) = residueCurvature p N := by
  have hp : (C c - (X : (ZMod p)[X])) ^ p - (C c - X) = X - X ^ p := by
    rw [sub_pow_char, ← map_pow, ZMod.pow_card]
    ring
  have he := congrArg (aeval N) hp
  simpa only [map_sub, map_pow, aeval_C, aeval_X, Algebra.algebraMap_eq_smul_one,
    residueCurvature] using he

/-- Powers of a logarithmic connection act independently on each exponent block. -/
theorem logarithmicConnection_pow_apply (N : Module.End (ZMod p) W)
    (k : ℕ) (f : ℕ →₀ W) (n : ℕ) :
    (logarithmicConnection p N ^ k) f n =
      (((n : ZMod p) • (1 : Module.End (ZMod p) W) - N) ^ k) (f n) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, logarithmicConnection_apply, ih,
      pow_succ', Module.End.mul_apply]
    rfl

/-- The full p-curvature is constant coefficient: every exponent contributes N−Nᵖ. -/
theorem logarithmic_pcurvature (N : Module.End (ZMod p) W) :
    logarithmicConnection p N ^ p - logarithmicConnection p N = lift (residueCurvature p N) := by
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro n
  change (logarithmicConnection p N ^ p) f n - logarithmicConnection p N f n = _
  rw [logarithmicConnection_pow_apply]
  have he := LinearMap.congr_fun (scalar_block_curvature p N (n : ZMod p)) (f n)
  exact he

private theorem residueCurvature_factor (N : Module.End (ZMod p) W) :
    residueCurvature p N = N * (1 - N ^ (p - 1)) := by
  have hp : 1 ≤ p := (Fact.out : p.Prime).one_le
  rw [residueCurvature, mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel hp]

private theorem residue_factor_commute (N : Module.End (ZMod p) W) :
    Commute N (1 - N ^ (p - 1)) := by
  show N * (1 - N ^ (p - 1)) = (1 - N ^ (p - 1)) * N
  rw [mul_sub, sub_mul, mul_one, one_mul, ← pow_succ', ← pow_succ]

private theorem residue_factor_isUnit (N : Module.End (ZMod p) W) (hN : IsNilpotent N) :
    IsUnit (1 - N ^ (p - 1)) := by
  have hp : 2 ≤ p := (Fact.out : p.Prime).two_le
  have he : p - 1 = (p - 2) + 1 := by omega
  rw [he]
  exact (IsNilpotent.pow_succ (p - 2) hN).isUnit_one_sub

/-- All curvature power kernels equal the corresponding residue kernels. -/
theorem residueCurvature_pow_kernel (N : Module.End (ZMod p) W) (hN : IsNilpotent N) (k : ℕ) :
    LinearMap.ker (residueCurvature p N ^ k) = LinearMap.ker (N ^ k) := by
  have hc := residue_factor_commute p N
  have hp : residueCurvature p N ^ k = (1 - N ^ (p - 1)) ^ k * N ^ k := by
    rw [residueCurvature_factor, hc.mul_pow, (hc.pow_pow k k).eq]
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv ((residue_factor_isUnit p N hN).pow k).unit
  have he (v : W) : e v = ((1 - N ^ (p - 1)) ^ k) v := by
    change (((residue_factor_isUnit p N hN).pow k).unit : Module.End (ZMod p) W) v = _
    rw [IsUnit.unit_spec]
  ext v
  change (residueCurvature p N ^ k) v = 0 ↔ (N ^ k) v = 0
  rw [hp, Module.End.mul_apply, ← he]
  constructor
  · intro h
    apply e.injective
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

/-- All curvature power images equal the corresponding residue images. -/
theorem residueCurvature_pow_range (N : Module.End (ZMod p) W) (hN : IsNilpotent N) (k : ℕ) :
    LinearMap.range (residueCurvature p N ^ k) = LinearMap.range (N ^ k) := by
  have hp : residueCurvature p N ^ k = N ^ k * (1 - N ^ (p - 1)) ^ k := by
    rw [residueCurvature_factor, (residue_factor_commute p N).mul_pow]
  let e := LinearMap.GeneralLinearGroup.toLinearEquiv ((residue_factor_isUnit p N hN).pow k).unit
  have he (v : W) : e v = ((1 - N ^ (p - 1)) ^ k) v := by
    change (((residue_factor_isUnit p N hN).pow k).unit : Module.End (ZMod p) W) v = _
    rw [IsUnit.unit_spec]
  ext v
  constructor
  · rintro ⟨w, rfl⟩
    exact ⟨e w, by rw [hp, Module.End.mul_apply, he]⟩
  · rintro ⟨w, rfl⟩
    refine ⟨e.symm w, ?_⟩
    rw [hp, Module.End.mul_apply, ← he, LinearEquiv.apply_symm_apply]

/-- Nilpotent residues have exactly the same vanishing powers as their p-curvature. -/
theorem residueCurvature_pow_eq_zero_iff (N : Module.End (ZMod p) W) (hN : IsNilpotent N) (k : ℕ) :
    residueCurvature p N ^ k = 0 ↔ N ^ k = 0 := by
  rw [← LinearMap.ker_eq_top, residueCurvature_pow_kernel p N hN, LinearMap.ker_eq_top]

/-- Vanishing logarithmic p-curvature forces a nilpotent residue to vanish. -/
theorem logarithmic_pcurvature_zero_iff (N : Module.End (ZMod p) W) (hN : IsNilpotent N) :
    logarithmicConnection p N ^ p - logarithmicConnection p N = 0 ↔ N = 0 := by
  rw [logarithmic_pcurvature]
  have he : lift (residueCurvature p N) = 0 ↔ residueCurvature p N = 0 := by
    constructor
    · intro h
      apply LinearMap.ext
      intro v
      have hv := congrArg (fun T : Module.End (ZMod p) (ℕ →₀ W) => T (constant (ZMod p) W v) 0) h
      simpa only [lift_apply, constant_zero, LinearMap.zero_apply, Finsupp.zero_apply] using hv
    · intro h
      apply LinearMap.ext
      intro f
      ext n
      rw [lift_apply, h]
      rfl
  rw [he]
  simpa only [pow_one] using residueCurvature_pow_eq_zero_iff p N hN 1

#print axioms logarithmic_pcurvature
#print axioms residueCurvature_pow_kernel
#print axioms residueCurvature_pow_range
#print axioms logarithmic_pcurvature_zero_iff
end GaloisForLFunctions.RepresentationLifting.DividedPower
