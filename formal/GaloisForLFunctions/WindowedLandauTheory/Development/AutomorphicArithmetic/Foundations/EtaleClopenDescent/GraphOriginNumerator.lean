import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.OriginDiagonalTensor
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphIdentityCoefficient
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphChartSystem
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.FixedOriginFibreValues
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ProjectiveDiagonalAppendScaling

/-! The selected graph coefficient of the homogeneous diagonal class
has the exterior-power character of the cotangent action as its value. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.SchemeCohomology GlobalTheory.WH
open GlobalTheory.WH.WeightedChartSystem
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology TensorProduct

namespace GlobalTheory.PD

variable {k F E L κ : Type} [Field k] [CharZero k] [IsAlgClosed k]
  [Field F] [Field E] [Field L] [LinearOrder κ]
  [Algebra k F] [Algebra k E] [Algebra k L] [Algebra F E] [Algebra F L] [Algebra E L]
  [IsScalarTower k F E] [IsScalarTower k F L] [IsScalarTower k E L] [IsScalarTower F E L]
  {d q p : ℕ} {x : Fin (d + 1) → F}

local instance {r : ℕ} : IsScalarTower k F (ExteriorDifferentials k E r) :=
  IsScalarTower.to₁₂₄ k F E (ExteriorDifferentials k E r)

local notation "π" => (Algebra.TensorProduct.lmul' k : F ⊗[k] F →ₐ[k] F)
local notation "V" => ExteriorDifferentials k E q
local notation "W" => ExteriorDifferentials k E p
local notation "B" => rB k E x {0}
local notation "C" => rB k L x {0}
local notation "j₁" => IsScalarTower.toAlgHom k E L

/-- At a fixed origin point, the selected graph value is the signed
coefficient of the characteristic determinant of the right pullback. -/
theorem IsFinCover.graphOriginValue_of_diagonalColumn
    (hE : IsFinCover k E x) (hL : IsFinCover k L x)
    [IsReduced (B ⧸ originIdeal k E x)] [IsReduced (C ⧸ originIdeal k L x)]
    (j₂ : E →ₐ[k] L) (f : OriginFibrePoint k L x) (hf : IsFix C f.1 j₂ B)
    (A : Matrix (Fin d) (Fin d) k)
    (hrow : ∀ m, ∃ (c : C) (g : Fin d → C), f.1 c ≠ 0 ∧
      (c : L) * j₂ (algebraMap F E (x m.succ / x 0)) =
        ∑ l, (g l : L) * algebraMap F L (x l.succ / x 0) ∧
      ∀ l, f.1 (g l) = f.1 c * A m l)
    (τ : DR k E →ₗ[E] E) (hτ : IsTop (x := x) τ) (hqp : q + p = d)
    (ρ : F →ₗ[k] k) (hρ : IsRes x ρ)
    (n : κ → ℕ × ℕ) (c : Finset (κ ⊕ₗ DiagonalIndex d) → V ⊗[k] W) :
    let T := diagonalChartSystem (E := E) hE.pd q p
    let U := graphChartSystem hE.pd j₂ q p
    let n₀ := fun _ : DiagonalIndex d => ((1, 1) : ℕ × ℕ)
    let I := selectedIndices (diagonalIndexEmbedding (0 : Fin (d + 1)))
    (fun J => c (uni ∅ J)) ∈ (T.columnComplex n₀ T.homogeneousMinor {0} {0}).C (d : ℤ) →
    (∀ b : W, tensorContraction ((traceWedgeLeftDual (F := F) τ).flip b) (c (uni ∅ I)) =
      (-1 : ℤ) ^ d • (π (orderedMinor T.minorRows (uni {(0 : Fin (d + 1))} I)) • b)) →
    ∃ s : L,
      (U.scaleColumn (appendedDiagonalDegrees n) 0 0).symm
          (fun J => graphFormPullback (j₁) j₂ (c J)) (uni ∅ I) =
        (-1 : k) ^ d • (s • originAffineVolume k L x) ∧
      Val C f.1 s ((1 + (Polynomial.X : Polynomial k) • A.map Polynomial.C).det.coeff p) := by
  intro T U n₀ I hterm hact
  let b : Finset (DiagonalIndex d) → V ⊗[k] W := fun J => c (uni ∅ J)
  let eps : k := (-1 : k) ^ d
  let t : V ⊗[k] W := eps • (T.scaleColumn n₀ 0 0).symm b I
  obtain ⟨ht, hcontraction⟩ := hE.affineIdentityTensor_of_originColumn τ b hterm hact
  change t ∈ tensorChartLattice (regularExteriorLattice B q) (regularExteriorLattice B p) at ht
  obtain ⟨m, u, v, he⟩ := exists_tensorChartLattice_family ht
  change ∀ a : W, tensorContraction ((traceWedgeLeftDual (F := F) τ).flip a) t =
    (∏ l : Fin d, x l.succ / x 0) • a at hcontraction
  have hfamily (a : W) :
      (∑ j : Fin m, traceWedgeLeftDual (F := F) τ (u j : V) a • (v j : W)) =
        (∏ l : Fin d, x l.succ / x 0) • a := by
    simpa only [he, map_sum, tensorContraction_tmul, LinearMap.flip_apply] using hcontraction a
  obtain ⟨e, hfix⟩ := exists_originFibrePoint_of_isFix j₂ f hf
  obtain ⟨s, hs, hval⟩ := hE.exists_graphIdentityCoefficient hL j₂ e f hfix A hrow τ hτ hqp ρ hρ
    (fun j => (u j : V)) (fun j => (v j : W)) (fun j => (u j).property) (fun j => (v j).property)
    hfamily
  let a := (U.scaleColumn (appendedDiagonalDegrees n) 0 0).symm
    (fun J => graphFormPullback (j₁) j₂ (c J)) (uni ∅ I)
  have ha : graphFormPullback (j₁) j₂ t = eps • a := by
    change graphFormPullback (j₁) j₂ (eps • (T.scaleColumn n₀ 0 0).symm b I) = _
    rw [map_smul]
    have hu := appendedDiagonal_unscale_restrict hE.pd q p n 0 0 c I
    change ((normalizedDiagonalSystem (E := E) hE.pd q p).scaleColumn
      (appendedDiagonalDegrees n) 0 0).symm c (uni ∅ I) =
      (T.scaleColumn n₀ 0 0).symm b I at hu
    rw [← hu, graphFormPullback_unscale hE.pd j₂ q p]
  rw [← he, ha] at hs
  refine ⟨s, ?_, hval⟩
  change a = eps • (s • originAffineVolume k L x)
  rw [← hs, smul_smul, show eps * eps = 1 by
    change (-1 : k) ^ d * (-1 : k) ^ d = 1
    rw [← mul_pow, neg_mul_neg, one_mul, one_pow], one_smul]

end GlobalTheory.PD
