import GaloisForLFunctions.RHTower.Sieve.KloostermanHybridModulusAdjoint
import GaloisForLFunctions.RHTower.Sieve.KloostermanHybridResidueParseval

/-!
# Exact collapse of the two-sided shared hybrid carrier

When both residue vectors in a complete Kloosterman bilinear form are additive Fourier transforms,
finite character orthogonality removes the Kloosterman kernel exactly.  The result is an
inverse-residue correlation.  This classification prevents the resulting two-sided carrier from
being mistaken for the still-missing Kuznetsov spectral average.
-/

open scoped BigOperators
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- Pointwise Kloosterman hybrid transform written as the unit-frequency Fourier transform of
physical residue-class polynomials. -/
theorem kloostermanHybridTransform_eq_unitResidueFourier
    (q N : ℕ) (a : ℕ → ℂ) (n : ZMod (q + 1)) (t : ℝ) :
    kloostermanHybridTransform q N a n t =
      ((q + 1 : ℕ) : ℂ) *
        ∑ x : (ZMod (q + 1))ˣ,
          physicalResidueDirichletPoly q N a (-(x : ZMod (q + 1))) t *
            ZMod.stdAddChar (n * ((x⁻¹ : (ZMod (q + 1))ˣ) : ZMod (q + 1))) := by
  unfold kloostermanHybridTransform
  rw [kloostermanTransform_eq_unitFourier]
  simp_rw [kloostermanUnitFourierCoeff_additiveHybrid_eq]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _hx
  ring

/-- Additive hybrid polynomial as the Fourier transform of its physical residue fibres. -/
theorem additiveHybridDirichletPoly_eq_residueFourier
    (q N : ℕ) (a : ℕ → ℂ) (d : ZMod (q + 1)) (t : ℝ) :
    additiveHybridDirichletPoly q N a d t =
      ∑ r : ZMod (q + 1), physicalResidueDirichletPoly q N a r t *
        ZMod.stdAddChar (d * r) := by
  unfold additiveHybridDirichletPoly physicalResidueDirichletPoly
  exact additiveHybridLogPoly_eq_sum_residues q N a d (t / (2 * Real.pi))

/-- Inverse-residue correlation left after two additive Fourier legs meet the complete
Kloosterman kernel. -/
def inverseResidueHybridCorrelation
    (q N M : ℕ) (a b : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ x : (ZMod (q + 1))ˣ,
    physicalResidueDirichletPoly q N a (-(x : ZMod (q + 1))) t *
      physicalResidueDirichletPoly q M b
        (-((x⁻¹ : (ZMod (q + 1))ˣ) : ZMod (q + 1))) t

/-- Unnormalized additive-Fourier pairing evaluates at the reflected frequency. -/
theorem sum_additiveFourier_mul_stdAddChar
    (q : ℕ) [NeZero q] (F : ZMod q → ℂ) (u : ZMod q) :
    (∑ n : ZMod q, (∑ r : ZMod q, F r * ZMod.stdAddChar (n * r)) *
        ZMod.stdAddChar (n * u)) =
      (q : ℂ) * F (-u) := by
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  have hdiag : (∑ n : ZMod q,
      ZMod.stdAddChar (n * (-u)) * ZMod.stdAddChar (n * u)) = (q : ℂ) := by
    calc
      _ = ∑ n : ZMod q, ZMod.stdAddChar (n * ((-u) + u)) := by
        apply Finset.sum_congr rfl
        intro n _hn
        rw [mul_add, AddChar.map_add_eq_mul]
      _ = _ := by simp
  calc
    (∑ r : ZMod q, F r * ∑ n : ZMod q,
        ZMod.stdAddChar (n * r) * ZMod.stdAddChar (n * u)) =
        F (-u) * ∑ n : ZMod q,
          ZMod.stdAddChar (n * (-u)) * ZMod.stdAddChar (n * u) := by
      apply Fintype.sum_eq_single (-u)
      intro r hr
      have hne : r + u ≠ 0 := by
        intro h
        apply hr
        exact eq_neg_of_add_eq_zero_left h
      rw [show (∑ n : ZMod q,
            ZMod.stdAddChar (n * r) * ZMod.stdAddChar (n * u)) = 0 by
        calc
          _ = ∑ n : ZMod q, ZMod.stdAddChar (n * (r + u)) := by
            apply Finset.sum_congr rfl
            intro n _hn
            rw [mul_add, AddChar.map_add_eq_mul]
          _ = 0 := by simpa [hne] using sum_stdAddChar_mul q (r + u)]
      simp
    _ = _ := by rw [hdiag]; ring

/-- A complete Kloosterman bilinear form with two additive-hybrid inputs is exactly a scaled
inverse-residue correlation. -/
theorem kloostermanHybridBilinear_eq_inverseResidueCorrelation
    (q N M : ℕ) (a b : ℕ → ℂ) (t : ℝ) :
    (∑ n : ZMod (q + 1), additiveHybridDirichletPoly q M b n t *
        kloostermanHybridTransform q N a n t) =
      (((q + 1 : ℕ) : ℂ) ^ 2) * inverseResidueHybridCorrelation q N M a b t := by
  simp_rw [kloostermanHybridTransform_eq_unitResidueFourier,
    additiveHybridDirichletPoly_eq_residueFourier]
  unfold inverseResidueHybridCorrelation
  change (∑ n : ZMod (q + 1),
      (∑ r : ZMod (q + 1),
        physicalResidueDirichletPoly q M b r t * ZMod.stdAddChar (n * r)) *
      (((q + 1 : ℕ) : ℂ) * ∑ x : (ZMod (q + 1))ˣ,
        physicalResidueDirichletPoly q N a (-(x : ZMod (q + 1))) t *
          ZMod.stdAddChar
            (n * ((x⁻¹ : (ZMod (q + 1))ˣ) : ZMod (q + 1))))) = _
  calc
    _ = ((q + 1 : ℕ) : ℂ) * ∑ n : ZMod (q + 1),
        (∑ r : ZMod (q + 1),
          physicalResidueDirichletPoly q M b r t * ZMod.stdAddChar (n * r)) *
        ∑ x : (ZMod (q + 1))ˣ,
          physicalResidueDirichletPoly q N a (-(x : ZMod (q + 1))) t *
            ZMod.stdAddChar
              (n * ((x⁻¹ : (ZMod (q + 1))ˣ) : ZMod (q + 1))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n _hn
      ring
    _ = ((q + 1 : ℕ) : ℂ) * ∑ x : (ZMod (q + 1))ˣ,
        physicalResidueDirichletPoly q N a (-(x : ZMod (q + 1))) t *
          ∑ n : ZMod (q + 1),
            (∑ r : ZMod (q + 1),
              physicalResidueDirichletPoly q M b r t * ZMod.stdAddChar (n * r)) *
            ZMod.stdAddChar
              (n * ((x⁻¹ : (ZMod (q + 1))ˣ) : ZMod (q + 1))) := by
      congr 1
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _hx
      apply Finset.sum_congr rfl
      intro n _hn
      ring
    _ = ((q + 1 : ℕ) : ℂ) * ∑ x : (ZMod (q + 1))ˣ,
        physicalResidueDirichletPoly q N a (-(x : ZMod (q + 1))) t *
          (((q + 1 : ℕ) : ℂ) * physicalResidueDirichletPoly q M b
            (-((x⁻¹ : (ZMod (q + 1))ˣ) : ZMod (q + 1))) t) := by
      apply congrArg (((q + 1 : ℕ) : ℂ) * ·)
      apply Finset.sum_congr rfl
      intro x _hx
      rw [sum_additiveFourier_mul_stdAddChar]
    _ = _ := by
      calc
        _ = ∑ x : (ZMod (q + 1))ˣ,
            (((q + 1 : ℕ) : ℂ) ^ 2) *
              (physicalResidueDirichletPoly q N a (-(x : ZMod (q + 1))) t *
                physicalResidueDirichletPoly q M b
                  (-((x⁻¹ : (ZMod (q + 1))ˣ) : ZMod (q + 1))) t) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro x _hx
          ring
        _ = _ := (Finset.mul_sum _ _ _).symm

/-- Consequently the entire two-sided shared signed modulus carrier is an inverse-congruence
correlation, not a remaining Kloosterman spectral sum. -/
theorem kloostermanSharedHybridModulusBilinear_eq_inverseResidueCorrelation
    (Q : Finset ℕ) (w : ℕ → ℂ) (N M : ℕ)
    (a b : ℕ → ℂ) (t : ℝ) :
    kloostermanSharedHybridModulusBilinear Q w N M a b t =
      ∑ q ∈ Q, w q * (((q + 1 : ℕ) : ℂ) ^ 2) *
        inverseResidueHybridCorrelation q N M a b t := by
  unfold kloostermanSharedHybridModulusBilinear
    kloostermanHybridModulusBilinear
  apply Finset.sum_congr rfl
  intro q _hq
  rw [kloostermanHybridBilinear_eq_inverseResidueCorrelation]
  ring

end

end RHTower.Sieve
