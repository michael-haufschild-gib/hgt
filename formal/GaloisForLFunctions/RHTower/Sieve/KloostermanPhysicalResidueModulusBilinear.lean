import GaloisForLFunctions.RHTower.Sieve.KloostermanSharedHybridCollapse

/-!
# Shared physical-residue Kloosterman modulus carrier

Ordinary Dirichlet coefficients are grouped by their physical residue classes, without taking an
additive Fourier transform in either Kloosterman leg.  The complete Kloosterman kernel therefore
survives exactly.  Expanding the residue fibres recovers the classical signed sum over ordinary
coefficient indices and moduli.
-/

open scoped BigOperators
open Complex Finset

namespace RHTower.Sieve

noncomputable section

/-- One ordinary Dirichlet coefficient at physical height, written in the normalization used by
`physicalResidueDirichletPoly`. -/
def physicalDirichletTerm (a : ℕ → ℂ) (n : ℕ) (t : ℝ) : ℂ :=
  a n * Complex.exp
    (((2 * Real.pi * ((t / (2 * Real.pi)) * Real.log n) : ℝ) : ℂ) * Complex.I)

/-- Summing physical residue fibres against an arbitrary residue weight recovers the literal
ordinary-index sum. -/
theorem sum_physicalResidueDirichletPoly_mul
    (q N : ℕ) (a : ℕ → ℂ) (t : ℝ) (F : ZMod (q + 1) → ℂ) :
    (∑ r : ZMod (q + 1), physicalResidueDirichletPoly q N a r t * F r) =
      ∑ n ∈ Finset.Icc 1 N, physicalDirichletTerm a n t * F (Nat.cast n) := by
  unfold physicalResidueDirichletPoly logPoly additiveResidueInterval physicalDirichletTerm
  simp_rw [Finset.sum_mul]
  rw [← Finset.sum_fiberwise (Finset.Icc 1 N)
    (fun n : ℕ => (Nat.cast n : ZMod (q + 1)))
    (fun n =>
      a n * Complex.exp
        (((2 * Real.pi * ((t / (2 * Real.pi)) * Real.log n) : ℝ) : ℂ) * Complex.I) *
        F (Nat.cast n))]
  apply Finset.sum_congr rfl
  intro r _hr
  apply Finset.sum_congr rfl
  intro n hn
  have hnr : (Nat.cast n : ZMod (q + 1)) = r := (Finset.mem_filter.1 hn).2
  rw [hnr]

/-- Complete Kloosterman bilinear form on two shared physical-residue Dirichlet vectors. -/
def kloostermanPhysicalResidueBilinear
    (q N M : ℕ) (a b : ℕ → ℂ) (t : ℝ) : ℂ :=
  kloostermanBilinear (q + 1)
    (fun r => physicalResidueDirichletPoly q N a r t)
    (fun s => physicalResidueDirichletPoly q M b s t)

/-- Exact ordinary-index expansion: unlike the two-sided additive-hybrid specialization, the
Kloosterman kernel remains present. -/
theorem kloostermanPhysicalResidueBilinear_eq
    (q N M : ℕ) (a b : ℕ → ℂ) (t : ℝ) :
    kloostermanPhysicalResidueBilinear q N M a b t =
      ∑ m ∈ Finset.Icc 1 N, physicalDirichletTerm a m t *
        ∑ n ∈ Finset.Icc 1 M, physicalDirichletTerm b n t *
          kloostermanSum (q + 1) (Nat.cast m) (Nat.cast n) := by
  unfold kloostermanPhysicalResidueBilinear
  rw [kloostermanBilinear_eq]
  rw [sum_physicalResidueDirichletPoly_mul]
  apply Finset.sum_congr rfl
  intro m _hm
  rw [sum_physicalResidueDirichletPoly_mul]

/-- Signed modulus average of the shared physical-residue Kloosterman bilinear forms. -/
def kloostermanPhysicalResidueModulusBilinear
    (Q : Finset ℕ) (w : ℕ → ℂ) (N M : ℕ)
    (a b : ℕ → ℂ) (t : ℝ) : ℂ :=
  kloostermanModulusBilinear Q w
    (fun q r => physicalResidueDirichletPoly q N a r t)
    (fun q s => physicalResidueDirichletPoly q M b s t)

/-- Literal signed sum over moduli and ordinary Dirichlet indices.  This is the
cancellation-bearing finite carrier for a later Kuznetsov--Deshouillers--Iwaniec estimate. -/
theorem kloostermanPhysicalResidueModulusBilinear_eq
    (Q : Finset ℕ) (w : ℕ → ℂ) (N M : ℕ)
    (a b : ℕ → ℂ) (t : ℝ) :
    kloostermanPhysicalResidueModulusBilinear Q w N M a b t =
      ∑ q ∈ Q, w q *
        ∑ m ∈ Finset.Icc 1 N, physicalDirichletTerm a m t *
          ∑ n ∈ Finset.Icc 1 M, physicalDirichletTerm b n t *
            kloostermanSum (q + 1) (Nat.cast m) (Nat.cast n) := by
  unfold kloostermanPhysicalResidueModulusBilinear kloostermanModulusBilinear
  apply Finset.sum_congr rfl
  intro q _hq
  change w q * kloostermanPhysicalResidueBilinear q N M a b t = _
  rw [kloostermanPhysicalResidueBilinear_eq]

/-- The shared physical-residue modulus carrier is continuous in physical height. -/
theorem continuous_kloostermanPhysicalResidueModulusBilinear
    (Q : Finset ℕ) (w : ℕ → ℂ) (N M : ℕ) (a b : ℕ → ℂ) :
    Continuous (kloostermanPhysicalResidueModulusBilinear Q w N M a b) := by
  unfold kloostermanPhysicalResidueModulusBilinear kloostermanModulusBilinear
  apply continuous_finsetSum
  intro q _hq
  apply Continuous.const_mul
  unfold kloostermanBilinear
  apply continuous_finsetSum
  intro n _hn
  exact (continuous_physicalResidueDirichletPoly q M b n).mul
    (by
      unfold kloostermanTransform
      apply continuous_finsetSum
      intro m _hm
      exact (continuous_physicalResidueDirichletPoly q N a m).mul_const _)

/-- Exact fixed-modulus operator baseline for the physical-residue carrier. -/
theorem norm_kloostermanPhysicalResidueBilinear_sq_le
    (q N M : ℕ) (a b : ℕ → ℂ) (t : ℝ) :
    ‖kloostermanPhysicalResidueBilinear q N M a b t‖ ^ 2 ≤
      (((q + 1 : ℕ) : ℝ) ^ 2) *
        (∑ r : ZMod (q + 1), ‖physicalResidueDirichletPoly q N a r t‖ ^ 2) *
          ∑ s : ZMod (q + 1), ‖physicalResidueDirichletPoly q M b s t‖ ^ 2 := by
  exact norm_kloostermanBilinear_sq_le (q + 1)
    (fun r => physicalResidueDirichletPoly q N a r t)
    (fun s => physicalResidueDirichletPoly q M b s t)

end

end RHTower.Sieve
