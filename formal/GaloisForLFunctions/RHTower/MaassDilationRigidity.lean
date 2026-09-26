import GaloisForLFunctions.RHTower.MaassCuspAutomorphicCorrespondence
import GaloisForLFunctions.RHTower.HeckeOperatorBasic
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Cusp dilation rigidity and nonvanishing of the Hecke residue branch

Inversion conjugates a positive dilation to its inverse. A scalar dilation
law for an inversion-invariant function therefore forces invariance under
the square dilation. Cusp decay makes that function zero.

For an actual nonzero level-one Maass form, the residue branch of the existing
normalized Hecke operator cannot vanish identically when the form satisfies
its eigen-equation. This is an exact nonvanishing result, not a quantitative
cancellation estimate or a Ramanujan-Petersson eigenvalue bound.
-/

open Complex UpperHalfPlane Filter Topology

namespace GaloisForLFunctions.RHTower.MaassDilationRigidity

/-- Dilation on both sides of modular inversion cancels exactly. -/
theorem dilation_inversion_dilation (a : {x : ℝ // 0 < x}) (z : ℍ) :
    a • (ModularGroup.S • (a • z)) = ModularGroup.S • z := by
  apply UpperHalfPlane.ext
  have ha : (a.val : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr a.2.ne'
  simp only [modular_S_smul, coe_pos_real_smul, Complex.real_smul]
  rw [inv_neg, mul_inv_rev, mul_neg, mul_left_comm, mul_inv_cancel₀ ha, mul_one,
    inv_neg]

/-- Inversion symmetry and cusp decay exclude every expanding scalar dilation law. -/
theorem zero_of_cusp_inversion_dilation {F : ℍ → ℂ}
    (hcusp : IsZeroAtImInfty F)
    (hS : ∀ z : ℍ, F (ModularGroup.S • z) = F z)
    (a : {x : ℝ // 0 < x}) (ha : 1 < a.val) (c : ℂ)
    (hscale : ∀ z : ℍ, F (a • z) = c * F z) : F = 0 := by
  have htwice (z : ℍ) : F ((a * a) • z) = F z := by
    calc
      F ((a * a) • z) = c * F (a • z) := by rw [mul_smul, hscale]
      _ = c * F (ModularGroup.S • (a • z)) := by rw [hS]
      _ = F (a • (ModularGroup.S • (a • z))) := (hscale _).symm
      _ = F z := by rw [dilation_inversion_dilation, hS]
  have hp (n : ℕ) (z : ℍ) : F ((a * a) ^ n • z) = F z := by
    induction n with
    | zero => rw [pow_zero, one_smul]
    | succ n ih => rw [pow_succ', mul_smul, htwice, ih]
  funext z
  have haa : 1 < a.val * a.val := ha.trans (by
    simpa only [mul_one] using mul_lt_mul_of_pos_left ha a.2)
  have him : Tendsto (fun n : ℕ => ((a * a) ^ n • z).im) atTop atTop := by
    simpa only [pos_real_im, Positive.val_pow, Positive.val_mul] using
      (tendsto_pow_atTop_atTop_of_one_lt haa).atTop_mul_const z.im_pos
  have hz : Tendsto (fun n : ℕ => (a * a) ^ n • z) atTop atImInfty :=
    tendsto_comap_iff.mpr him
  have hlim : Tendsto (fun n : ℕ => F ((a * a) ^ n • z)) atTop (𝓝 0) := hcusp.comp hz
  simp only [hp] at hlim
  exact tendsto_nhds_unique tendsto_const_nhds hlim

/-- No actual nonzero level-one Maass cusp form is an expanding dilation eigenfunction. -/
theorem not_maass_dilation_eigenfunction {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma 1)) lam)
    (a : {x : ℝ // 0 < x}) (ha : 1 < a.val) (c : ℂ) :
    ¬ ∀ z : ℍ, f.1.1 (a • z) = c * f.1.1 z := by
  intro hscale
  apply f.2.1
  apply Subtype.ext
  refine zero_of_cusp_inversion_dilation ?_ ?_ a ha c hscale
  · simpa only [map_one, one_smul] using f.2.2.2 (1 : SL2Z)
  · intro z
    exact f.1.2
      ⟨integralSL2ToReal ModularGroup.S,
        ⟨ModularGroup.S, CongruenceSubgroup.mem_Gamma_one _, rfl⟩⟩ z

/-- Real-coordinate presentation used by the existing normalized Hecke operator. -/
noncomputable def coordinateField (F : ℍ → ℂ) (x y : ℝ) : ℂ :=
  F (ofComplex ((x : ℂ) + (y : ℂ) * Complex.I))

/-- The expanding coordinate branch is the literal upper-half-plane dilation. -/
theorem coordinateField_dilation (F : ℍ → ℂ) (a : {x : ℝ // 0 < x}) (z : ℍ) :
    coordinateField F (a.val * z.re) (a.val * z.im) = F (a • z) := by
  have h : ((a.val * z.re : ℝ) : ℂ) + ((a.val * z.im : ℝ) : ℂ) * Complex.I =
      (a • z : ℍ) := by
    simp only [Complex.ofReal_mul, coe_pos_real_smul, Complex.real_smul]
    rw [mul_assoc, ← mul_add]
    congr 1
    exact Complex.re_add_im (z : ℂ)
  simp only [coordinateField, h, ofComplex_apply]

/-- An actual Hecke eigen-equation cannot have an identically zero residue branch. -/
theorem hecke_residue_sum_ne_zero {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma 1)) lam)
    {p : ℕ} (hp : 1 < p) (mu : ℂ)
    (heigen : ∀ z : ℍ, _root_.RHTower.heckeOp p (coordinateField f.1.1) z.re z.im =
      mu * f.1.1 z) :
    ∃ z : ℍ, (∑ b ∈ Finset.range p,
      coordinateField f.1.1 ((z.re + b) / p) (z.im / p)) ≠ 0 := by
  classical
  by_contra h
  have hzero (z : ℍ) : (∑ b ∈ Finset.range p,
      coordinateField f.1.1 ((z.re + b) / p) (z.im / p)) = 0 := by
    simpa using not_exists.mp h z
  have hpR : (1 : ℝ) < p := by exact_mod_cast hp
  let a : {x : ℝ // 0 < x} := ⟨p, lt_trans zero_lt_one hpR⟩
  apply not_maass_dilation_eigenfunction f a hpR ((Real.sqrt p : ℂ) * mu)
  intro z
  have he := heigen z
  rw [_root_.RHTower.heckeOp, hzero, add_zero] at he
  have hs : (Real.sqrt p : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr a.2).ne'
  rw [Complex.ofReal_inv, inv_mul_eq_iff_eq_mul₀ hs] at he
  change coordinateField f.1.1 (a.val * z.re) (a.val * z.im) = _ at he
  rw [coordinateField_dilation] at he
  simpa only [← mul_assoc] using he

end GaloisForLFunctions.RHTower.MaassDilationRigidity
