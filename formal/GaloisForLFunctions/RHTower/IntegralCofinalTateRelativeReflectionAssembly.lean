import GaloisForLFunctions.RHTower.IntegralRelativeReflectionComplexFusion

/-!
# Integral cofinal Tate relative-reflection assembly

This module constructs the reciprocal-clock completion object over the unspecialized integral
Laurent source. Finite Tate interval shifts, inclusions, and top boundaries are rebuilt over the
source ring rather than a field. Flat-versus-`T` and flat-versus-`T⁻¹` naturality defects recover
the two arrows of the universal relative-reflection matrix exactly.

The same matrix acts stagewise on the full cofinal direct sum and satisfies the source Clifford law
globally. No Xi divisor or physical character is used. The still-open theorem is strict integral
landing of this assembled source object through actual Xi completion.
-/

open Complex Matrix

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- Integral Laurent coefficient ring used by the cofinal Tate assembly. -/
abbrev DeningerIntegralTateRing := DeningerIntegralCartierSourceRing

/-- Standard basis vector in an integral finite Tate interval. -/
def deningerIntegralTateIntervalBasis
    {m : ℕ} (k : Fin m) : Fin m → DeningerIntegralTateRing :=
  fun i => if i = k then 1 else 0

/-- Nilpotent forward arrow on an integral `(m+1)`-vertex Tate interval. -/
def deningerIntegralTateIntervalForward (m : ℕ) :
    (Fin (m + 1) → DeningerIntegralTateRing) →ₗ[DeningerIntegralTateRing]
      (Fin (m + 1) → DeningerIntegralTateRing) where
  toFun f := Fin.cases 0 (fun i => f i.castSucc)
  map_add' f g := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp
  map_smul' c f := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i <;> simp

theorem deningerIntegralTateIntervalForward_last
    (m : ℕ) (f : Fin (m + 2) → DeningerIntegralTateRing) :
    deningerIntegralTateIntervalForward (m + 1) f (Fin.last (m + 1)) =
      f (Fin.last m).castSucc := by
  rw [← Fin.succ_last]
  rfl

/-- Integral cofinal inclusion, appending a zero top coordinate. -/
def deningerIntegralTateIntervalInclusion (m : ℕ) :
    (Fin m → DeningerIntegralTateRing) →ₗ[DeningerIntegralTateRing]
      (Fin (m + 1) → DeningerIntegralTateRing) where
  toFun f i := if hi : i.1 < m then f ⟨i.1, hi⟩ else 0
  map_add' f g := by
    funext i
    by_cases hi : i.1 < m <;> simp [hi]
  map_smul' c f := by
    funext i
    by_cases hi : i.1 < m <;> simp [hi]

/-- Rank-one integral top boundary born when the forward arrow leaves one finite interval. -/
def deningerIntegralTateIntervalTopBoundary (m : ℕ) :
    (Fin (m + 1) → DeningerIntegralTateRing) →ₗ[DeningerIntegralTateRing]
      (Fin (m + 2) → DeningerIntegralTateRing) where
  toFun f i := if i = Fin.last (m + 1) then f (Fin.last m) else 0
  map_add' f g := by
    funext i
    by_cases hi : i = Fin.last (m + 1) <;> simp [hi]
  map_smul' c f := by
    funext i
    by_cases hi : i = Fin.last (m + 1) <;> simp [hi]

theorem deningerIntegralTateIntervalTopBoundary_basis_last (m : ℕ) :
    deningerIntegralTateIntervalTopBoundary m
        (deningerIntegralTateIntervalBasis (Fin.last m)) =
      deningerIntegralTateIntervalBasis (Fin.last (m + 1)) := by
  funext i
  simp [deningerIntegralTateIntervalTopBoundary,
    deningerIntegralTateIntervalBasis, Fin.ext_iff]

/-- Integral Bockstein law: failure of finite forward shift to commute with zero-extension is
exactly the new top boundary. -/
theorem deningerIntegralTateIntervalForward_inclusion_defect
    (m : ℕ) (f : Fin (m + 1) → DeningerIntegralTateRing) :
    deningerIntegralTateIntervalForward (m + 1)
        (deningerIntegralTateIntervalInclusion (m + 1) f) =
      deningerIntegralTateIntervalInclusion (m + 1)
          (deningerIntegralTateIntervalForward m f) +
        deningerIntegralTateIntervalTopBoundary m f := by
  funext i
  rcases i with ⟨i, hi⟩
  cases i with
  | zero =>
      simp [deningerIntegralTateIntervalForward,
        deningerIntegralTateIntervalInclusion,
        deningerIntegralTateIntervalTopBoundary]
  | succ i =>
      by_cases him : i < m
      · have himle : i ≤ m := by omega
        have hine : i ≠ m := by omega
        simp [deningerIntegralTateIntervalForward,
          deningerIntegralTateIntervalInclusion,
          deningerIntegralTateIntervalTopBoundary, him, himle, hine,
          Fin.ext_iff]
      · have hieq : i = m := by omega
        subst i
        have htop :
            (⟨m + 1, hi⟩ : Fin (m + 2)) = Fin.last (m + 1) := by
          apply Fin.ext
          rfl
        rw [htop, deningerIntegralTateIntervalForward_last]
        simp [deningerIntegralTateIntervalForward,
          deningerIntegralTateIntervalInclusion,
          deningerIntegralTateIntervalTopBoundary, Fin.ext_iff]
        congr 1

/-- Naturality defect of an integral finite Tate arrow scaled by a Laurent clock gain. -/
def deningerIntegralTateScaledForwardNaturalityDefect
    (gain : DeningerIntegralTateRing) (m : ℕ)
    (f : Fin (m + 1) → DeningerIntegralTateRing) :
    Fin (m + 2) → DeningerIntegralTateRing :=
  (gain • deningerIntegralTateIntervalForward (m + 1))
      (deningerIntegralTateIntervalInclusion (m + 1) f) -
    deningerIntegralTateIntervalInclusion (m + 1)
      ((gain • deningerIntegralTateIntervalForward m) f)

theorem deningerIntegralTateScaledForwardNaturalityDefect_eq_topBoundary
    (gain : DeningerIntegralTateRing) (m : ℕ)
    (f : Fin (m + 1) → DeningerIntegralTateRing) :
    deningerIntegralTateScaledForwardNaturalityDefect gain m f =
      gain • deningerIntegralTateIntervalTopBoundary m f := by
  simp only [deningerIntegralTateScaledForwardNaturalityDefect,
    LinearMap.smul_apply, map_smul]
  rw [deningerIntegralTateIntervalForward_inclusion_defect]
  module

/-- Flat-minus-scaled integral cofinal defect. -/
def deningerIntegralTateFlatMinusRawCofinalDefect
    (gain : DeningerIntegralTateRing) (m : ℕ)
    (f : Fin (m + 1) → DeningerIntegralTateRing) :
    Fin (m + 2) → DeningerIntegralTateRing :=
  deningerIntegralTateScaledForwardNaturalityDefect 1 m f -
    deningerIntegralTateScaledForwardNaturalityDefect gain m f

theorem deningerIntegralTateFlatMinusRawCofinalDefect_eq_topBoundary
    (gain : DeningerIntegralTateRing) (m : ℕ)
    (f : Fin (m + 1) → DeningerIntegralTateRing) :
    deningerIntegralTateFlatMinusRawCofinalDefect gain m f =
      (1 - gain) • deningerIntegralTateIntervalTopBoundary m f := by
  rw [deningerIntegralTateFlatMinusRawCofinalDefect,
    deningerIntegralTateScaledForwardNaturalityDefect_eq_topBoundary,
    deningerIntegralTateScaledForwardNaturalityDefect_eq_topBoundary]
  module

/-- Canonical integral reader of the newly born top coordinate. -/
def deningerIntegralTateTopCoefficient
    (m : ℕ) (v : Fin (m + 2) → DeningerIntegralTateRing) :
    DeningerIntegralTateRing := v (Fin.last (m + 1))

/-- Paired flat-versus-`T` and flat-versus-`T⁻¹` Tate anomalies. -/
def deningerIntegralTateRelativeReflectionCoefficientMatrix
    (m : ℕ) : Matrix (Fin 2) (Fin 2) DeningerIntegralTateRing :=
  !![0,
      -deningerIntegralTateTopCoefficient m
        (deningerIntegralTateFlatMinusRawCofinalDefect
          (1 + deningerIntegralCartierSourceGenerator) m
          (deningerIntegralTateIntervalBasis (Fin.last m)));
    -deningerIntegralTateTopCoefficient m
        (deningerIntegralTateFlatMinusRawCofinalDefect
          (1 + inversion ℤ deningerIntegralCartierSourceGenerator) m
          (deningerIntegralTateIntervalBasis (Fin.last m))),
      0]

theorem deningerIntegralTateTopCoefficient_flatMinusRaw
    (gain : DeningerIntegralTateRing) (m : ℕ) :
    -deningerIntegralTateTopCoefficient m
        (deningerIntegralTateFlatMinusRawCofinalDefect gain m
          (deningerIntegralTateIntervalBasis (Fin.last m))) = gain - 1 := by
  rw [deningerIntegralTateFlatMinusRawCofinalDefect_eq_topBoundary,
    deningerIntegralTateIntervalTopBoundary_basis_last]
  simp [deningerIntegralTateTopCoefficient,
    deningerIntegralTateIntervalBasis]

/-- Source-level completion reconstruction: canonical top readout of reciprocal integral clock
defects is exactly the universal integral relative-reflection matrix. -/
theorem deningerIntegralTateRelativeReflectionCoefficientMatrix_eq
    (m : ℕ) :
    deningerIntegralTateRelativeReflectionCoefficientMatrix m =
      deningerIntegralRelativeReflectionDifferential := by
  apply Matrix.ext
  intro i j
  fin_cases i <;> fin_cases j
  · simp [deningerIntegralTateRelativeReflectionCoefficientMatrix,
      deningerIntegralRelativeReflectionDifferential]
  · simpa [deningerIntegralTateRelativeReflectionCoefficientMatrix,
      deningerIntegralRelativeReflectionDifferential,
      deningerIntegralCartierSourceGenerator] using
        (deningerIntegralTateTopCoefficient_flatMinusRaw
          (1 + deningerIntegralCartierSourceGenerator) m)
  · simpa [deningerIntegralTateRelativeReflectionCoefficientMatrix,
      deningerIntegralRelativeReflectionDifferential] using
        (deningerIntegralTateTopCoefficient_flatMinusRaw
          (1 + inversion ℤ deningerIntegralCartierSourceGenerator) m)
  · simp [deningerIntegralTateRelativeReflectionCoefficientMatrix,
      deningerIntegralRelativeReflectionDifferential]

/-- Algebraic direct sum of reciprocal orientation packets over all Tate stages. -/
abbrev DeningerIntegralCofinalTateOrientationPacket :=
  ℕ →₀ (Fin 2 → DeningerIntegralTateRing)

/-- Global integral relative-reflection operator, acting stagewise on the cofinal direct sum. -/
def deningerIntegralCofinalRelativeReflectionOperator :
    DeningerIntegralCofinalTateOrientationPacket →ₗ[DeningerIntegralTateRing]
      DeningerIntegralCofinalTateOrientationPacket :=
  Finsupp.mapRange.linearMap
    (Matrix.mulVecLin deningerIntegralRelativeReflectionDifferential)

@[simp] theorem deningerIntegralCofinalRelativeReflectionOperator_apply
    (x : DeningerIntegralCofinalTateOrientationPacket) (m : ℕ) :
    deningerIntegralCofinalRelativeReflectionOperator x m =
      deningerIntegralRelativeReflectionDifferential.mulVec (x m) := by
  simp [deningerIntegralCofinalRelativeReflectionOperator]

/-- Global source Clifford law on the full integral cofinal Tate direct sum. -/
theorem deningerIntegralCofinalRelativeReflectionOperator_sq :
    deningerIntegralCofinalRelativeReflectionOperator.comp
        deningerIntegralCofinalRelativeReflectionOperator =
      sourceHorizontalGammaSixIntegralHermitianSquare • LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Finsupp.ext
  intro m
  funext i
  rw [LinearMap.comp_apply,
    deningerIntegralCofinalRelativeReflectionOperator_apply,
    deningerIntegralCofinalRelativeReflectionOperator_apply,
    Matrix.mulVec_mulVec,
    deningerIntegralRelativeReflectionDifferential_sq]
  fin_cases i <;> simp [Matrix.mulVec]

end


end RHTower
