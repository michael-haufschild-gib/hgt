import GaloisForLFunctions.RHTower.FieldOneLocalHaarModule

/-!
# Haar scaling on finite-stage rational adeles

For `A_S = ℝ × ∏_{v ∈ S} ℚ_v`, this file proves:

* the coordinatewise idele action is distributive;
* its additive Haar character factors into the real character and all local
  characters;
* every standard rational `S`-unit generator has total character one;
* the full diagonal rational `S`-unit subgroup therefore lies in the Haar
  character kernel; and
* every additive Haar measure on `A_S` is invariant under that subgroup.

This is the exact measure-preservation input for a future quotient-measure
construction.  It does not manufacture that quotient measure or identify it
with a trace Hilbert space.
-/

open MeasureTheory
open MeasureTheory.Measure
open scoped ENNReal NNReal Pointwise Topology

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain

/-! ## Coordinate actions -/

/-- Coordinatewise idele scaling distributes over addition on `A_S`. -/
instance fieldOneFiniteStageIdeleAdeleDistribMulAction
    (S : Finset (HeightOneSpectrum ℤ)) :
    DistribMulAction (FieldOneFiniteStageIdele S)
      (FieldOneFiniteStageAdele S) where
  __ := fieldOneFiniteStageIdeleMulAction S
  smul_zero u := by
    apply Prod.ext
    · exact smul_zero u.1
    · funext v
      exact smul_zero (u.2 v)
  smul_add u x y := by
    apply Prod.ext
    · exact smul_add u.1 x.1 y.1
    · funext v
      exact smul_add (u.2 v) (x.2 v) (y.2 v)

/-- The real-coordinate action of finite-stage ideles. -/
instance fieldOneFiniteStageIdeleRealDistribMulAction
    (S : Finset (HeightOneSpectrum ℤ)) :
    DistribMulAction (FieldOneFiniteStageIdele S) ℝ where
  smul u x := u.1 • x
  one_smul x := one_smul ℝˣ x
  mul_smul u w x := mul_smul u.1 w.1 x
  smul_zero u := smul_zero u.1
  smul_add u x y := smul_add u.1 x y

/-- Every fixed finite-stage idele acts continuously on the real
coordinate. -/
instance fieldOneFiniteStageIdeleRealContinuousConstSMul
    (S : Finset (HeightOneSpectrum ℤ)) :
    ContinuousConstSMul (FieldOneFiniteStageIdele S) ℝ where
  continuous_const_smul u := by
    change Continuous fun x : ℝ => (u.1 : ℝ) * x
    exact continuous_const.mul continuous_id

/-- The action of finite-stage ideles on one selected finite coordinate. -/
instance fieldOneFiniteStageIdeleLocalDistribMulAction
    (S : Finset (HeightOneSpectrum ℤ))
    (v : ↥S) :
    DistribMulAction (FieldOneFiniteStageIdele S)
      (v.1.adicCompletion ℚ) where
  smul u x := u.2 v • x
  one_smul x := one_smul (v.1.adicCompletion ℚ)ˣ x
  mul_smul u w x := mul_smul (u.2 v) (w.2 v) x
  smul_zero u := smul_zero (u.2 v)
  smul_add u x y := smul_add (u.2 v) x y

/-- Every fixed finite-stage idele acts continuously on each selected finite
coordinate. -/
instance fieldOneFiniteStageIdeleLocalContinuousConstSMul
    (S : Finset (HeightOneSpectrum ℤ))
    (v : ↥S) :
    ContinuousConstSMul (FieldOneFiniteStageIdele S)
      (v.1.adicCompletion ℚ) where
  continuous_const_smul u := by
    change Continuous fun x : v.1.adicCompletion ℚ =>
      (u.2 v : v.1.adicCompletion ℚ) * x
    exact continuous_const.mul continuous_id

/-- Projection of a finite-stage idele to its real unit. -/
def fieldOneFiniteStageRealProjection
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageIdele S →* ℝˣ where
  toFun := Prod.fst
  map_one' := rfl
  map_mul' _ _ := rfl

/-- Projection of a finite-stage idele to one finite-place unit. -/
def fieldOneFiniteStageLocalProjection
    (S : Finset (HeightOneSpectrum ℤ))
    (v : ↥S) :
    FieldOneFiniteStageIdele S →*
      (v.1.adicCompletion ℚ)ˣ where
  toFun u := u.2 v
  map_one' := rfl
  map_mul' _ _ := rfl

/-! ## Haar-character functoriality and factorization -/

/-- If two group elements induce the same additive self-map, their
distributive Haar characters agree. -/
theorem fieldOne_distribHaarChar_change_group
    {G H A : Type*}
    [Group G] [Group H] [AddCommGroup A]
    [DistribMulAction G A] [DistribMulAction H A]
    [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [IsTopologicalAddGroup A] [LocallyCompactSpace A]
    [SecondCountableTopology A]
    [ContinuousConstSMul G A] [ContinuousConstSMul H A]
    (φ : G →* H) (g : G)
    (hφ : ∀ x : A, g • x = φ g • x) :
    distribHaarChar A g = distribHaarChar A (φ g) := by
  let μ : Measure A := addHaar
  obtain ⟨s, hs_compact, hs_nhds⟩ :=
    exists_compact_mem_nhds (0 : A)
  have hs_ne_zero : μ s ≠ 0 := by
    intro hs
    exact
      (IsOpenPosMeasure.open_pos (interior s) isOpen_interior
        ⟨0, mem_interior_iff_mem_nhds.mpr hs_nhds⟩)
      (measure_mono_null interior_subset hs)
  have hs_ne_top : μ s ≠ ∞ :=
    ne_of_lt hs_compact.measure_lt_top
  apply ENNReal.coe_injective
  rw [distribHaarChar_eq_div hs_ne_zero hs_ne_top]
  rw [distribHaarChar_eq_div hs_ne_zero hs_ne_top]
  congr 1
  apply congrArg μ
  ext x
  rw [Set.mem_smul_set, Set.mem_smul_set]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, (hφ y).symm⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, hφ y⟩

/-- The finite-stage additive Haar character is the product of its real and
selected finite-place characters. -/
theorem fieldOneFiniteStage_distribHaarChar_factorization
    (S : Finset (HeightOneSpectrum ℤ))
    (u : FieldOneFiniteStageIdele S) :
    distribHaarChar (FieldOneFiniteStageAdele S) u =
      distribHaarChar ℝ u.1 *
        ∏ v : ↥S,
          distribHaarChar
            (v.1.adicCompletion ℚ) (u.2 v) := by
  rw [fieldOne_distribHaarChar_prod
    (A := ℝ)
    (B := (v : ↥S) → v.1.adicCompletion ℚ) u]
  have hreal :
      distribHaarChar ℝ u =
        distribHaarChar ℝ u.1 := by
    apply fieldOne_distribHaarChar_change_group
      (fieldOneFiniteStageRealProjection S) u
    intro x
    rfl
  rw [hreal]
  rw [fieldOne_distribHaarChar_pi
    (A := fun v : ↥S => v.1.adicCompletion ℚ) u]
  apply congrArg (fun z => distribHaarChar ℝ u.1 * z)
  apply Finset.prod_congr rfl
  intro v _
  apply fieldOne_distribHaarChar_change_group
    (fieldOneFiniteStageLocalProjection S v) u
  intro x
  rfl

/-- For every finite-stage idele, additive Haar character is exactly the
previously constructed finite-stage norm module. -/
theorem fieldOneFiniteStage_distribHaarChar_eq_module
    (S : Finset (HeightOneSpectrum ℤ))
    (u : FieldOneFiniteStageIdele S) :
    distribHaarChar (FieldOneFiniteStageAdele S) u =
      fieldOneFiniteStageModule S u := by
  rw [fieldOneFiniteStage_distribHaarChar_factorization]
  rw [fieldOne_realUnits_distribHaarChar]
  simp_rw [fieldOneAdicUnits_distribHaarChar_eq_nnnorm]
  rfl

/-! ## Product formula on rational S-unit generators -/

/-- The diagonal sign has total finite-stage Haar character one. -/
theorem fieldOneFiniteStage_distribHaarChar_negOne
    (S : Finset (HeightOneSpectrum ℤ)) :
    distribHaarChar (FieldOneFiniteStageAdele S)
      (fieldOneFiniteStageDiagonalUnit S (-1)) = 1 := by
  rw [fieldOneFiniteStage_distribHaarChar_factorization]
  have hreal :
      distribHaarChar ℝ
          (fieldOneFiniteStageDiagonalUnit S (-1)).1 = 1 := by
    change
      distribHaarChar ℝ
        (fieldOneRationalRealUnit (-1)) = 1
    rw [fieldOne_realUnits_distribHaarChar]
    simp [fieldOneRationalRealUnit]
  rw [hreal, one_mul]
  have hlocal (v : ↥S) :
      distribHaarChar (v.1.adicCompletion ℚ)
          ((fieldOneFiniteStageDiagonalUnit S (-1)).2 v) =
        1 := by
    change
      distribHaarChar (v.1.adicCompletion ℚ)
        (fieldOneRationalLocalUnit v.1 (-1)) = 1
    exact
      fieldOneRationalLocalUnit_distribHaarChar_negOne v.1
  simp_rw [hlocal]
  simp

/-- Each selected diagonal rational prime has total finite-stage Haar
character one: the real factor `p` cancels the same-place finite factor
`p⁻¹`, while all other local factors equal one. -/
theorem fieldOneFiniteStage_distribHaarChar_prime
    (S : Finset (HeightOneSpectrum ℤ))
    (v : ↥S) :
    distribHaarChar (FieldOneFiniteStageAdele S)
      (fieldOneFiniteStageDiagonalUnit S
        (fieldOneRationalPrimeUnit v.1)) = 1 := by
  classical
  rw [fieldOneFiniteStage_distribHaarChar_factorization]
  have hreal :
      distribHaarChar ℝ
          (fieldOneFiniteStageDiagonalUnit S
            (fieldOneRationalPrimeUnit v.1)).1 =
        ((Rat.HeightOneSpectrum.primesEquiv v.1 : ℕ) :
          ℝ≥0) := by
    change
      distribHaarChar ℝ
          (fieldOneRationalRealUnit
            (fieldOneRationalPrimeUnit v.1)) =
        ((Rat.HeightOneSpectrum.primesEquiv v.1 : ℕ) :
          ℝ≥0)
    rw [fieldOne_realUnits_distribHaarChar]
    apply NNReal.eq
    simp [fieldOneRationalRealUnit,
      fieldOneRationalPrimeUnit]
  rw [hreal]
  rw [Finset.prod_eq_single v]
  · change
      ((Rat.HeightOneSpectrum.primesEquiv v.1 : ℕ) :
          ℝ≥0) *
        distribHaarChar (v.1.adicCompletion ℚ)
          (fieldOneRationalLocalUnit v.1
            (fieldOneRationalPrimeUnit v.1)) =
        1
    rw [fieldOneRationalPrimeUnit_localDistribHaarChar_self]
    have hp0 :
        ((Rat.HeightOneSpectrum.primesEquiv v.1 : ℕ) :
          ℝ≥0) ≠ 0 := by
      exact_mod_cast
        (Rat.HeightOneSpectrum.primesEquiv v.1).property.ne_zero
    exact mul_inv_cancel₀ hp0
  · intro w _ hwv
    change
      distribHaarChar (w.1.adicCompletion ℚ)
        (fieldOneRationalLocalUnit w.1
          (fieldOneRationalPrimeUnit v.1)) = 1
    exact
      fieldOneRationalPrimeUnit_localDistribHaarChar_of_ne
        v.1 w.1 (fun h => hwv (Subtype.ext h))
  · simp

/-! ## Kernel and measure preservation -/

/-- Every rational `S`-unit lies in the kernel of the diagonal finite-stage
Haar character. -/
theorem fieldOneSUnitSubgroup_le_distribHaarCharKernel
    (S : Finset (HeightOneSpectrum ℤ)) :
    fieldOneSUnitSubgroup S ≤
      ((distribHaarChar (FieldOneFiniteStageAdele S)).comp
        (fieldOneFiniteStageDiagonalUnit S)).ker := by
  rw [fieldOneSUnitSubgroup]
  rw [Subgroup.closure_le]
  intro u hu
  rcases Set.eq_or_mem_of_mem_insert hu with rfl | hu
  · change
      distribHaarChar (FieldOneFiniteStageAdele S)
          (fieldOneFiniteStageDiagonalUnit S (-1)) = 1
    exact fieldOneFiniteStage_distribHaarChar_negOne S
  · obtain ⟨v, rfl⟩ := hu
    change
      distribHaarChar (FieldOneFiniteStageAdele S)
          (fieldOneFiniteStageDiagonalUnit S
            (fieldOneRationalPrimeUnit v.1)) = 1
    exact
      fieldOneFiniteStage_distribHaarChar_prime S v

/-- The full diagonal `S`-unit image lies in the finite-stage additive Haar
character kernel. -/
theorem fieldOneFiniteStageSUnitImage_le_distribHaarCharKernel
    (S : Finset (HeightOneSpectrum ℤ)) :
    fieldOneFiniteStageSUnitImage S ≤
      (distribHaarChar
        (FieldOneFiniteStageAdele S)).ker := by
  intro u hu
  obtain ⟨q, hq, rfl⟩ := hu
  exact
    fieldOneSUnitSubgroup_le_distribHaarCharKernel S hq

/-- Haar character descended to the finite-stage idele class group. -/
def fieldOneFiniteStageIdeleClassHaarCharacter
    (S : Finset (HeightOneSpectrum ℤ)) :
    FieldOneFiniteStageIdeleClassGroup S →* ℝ≥0 :=
  QuotientGroup.lift
    (fieldOneFiniteStageSUnitImage S)
    (distribHaarChar (FieldOneFiniteStageAdele S))
    (fieldOneFiniteStageSUnitImage_le_distribHaarCharKernel S)

/-- The descended Haar character is exactly the previously constructed
idele-class module. -/
theorem fieldOneFiniteStageIdeleClassHaarCharacter_eq_module
    (S : Finset (HeightOneSpectrum ℤ)) :
    fieldOneFiniteStageIdeleClassHaarCharacter S =
      fieldOneFiniteStageIdeleClassModule S := by
  apply MonoidHom.ext
  intro c
  refine Quotient.inductionOn c ?_
  intro u
  change
    distribHaarChar (FieldOneFiniteStageAdele S) u =
      fieldOneFiniteStageModule S u
  exact fieldOneFiniteStage_distribHaarChar_eq_module S u

/-- Exact scaling law for every additive Haar measure on `A_S` and every
finite-stage idele. -/
theorem fieldOneFiniteStage_measure_smul
    (S : Finset (HeightOneSpectrum ℤ))
    (u : FieldOneFiniteStageIdele S)
    (μ : Measure (FieldOneFiniteStageAdele S))
    [IsAddHaarMeasure μ] [Regular μ]
    (s : Set (FieldOneFiniteStageAdele S)) :
    μ (u • s) =
      (fieldOneFiniteStageModule S u : ℝ≥0∞) * μ s := by
  rw [← distribHaarChar_mul μ u s]
  rw [fieldOneFiniteStage_distribHaarChar_eq_module]

/-- Every additive Haar measure on `A_S` is invariant under the diagonal
rational `S`-unit image. -/
theorem fieldOneFiniteStageSUnitImage_measure_smul
    (S : Finset (HeightOneSpectrum ℤ))
    (h : fieldOneFiniteStageSUnitImage S)
    (μ : Measure (FieldOneFiniteStageAdele S))
    [IsAddHaarMeasure μ] [Regular μ]
    (s : Set (FieldOneFiniteStageAdele S)) :
    μ ((h : FieldOneFiniteStageIdele S) • s) = μ s := by
  have hh :=
    fieldOneFiniteStageSUnitImage_le_distribHaarCharKernel
      S h.property
  change
    distribHaarChar (FieldOneFiniteStageAdele S)
      (h : FieldOneFiniteStageIdele S) = 1 at hh
  rw [← distribHaarChar_mul μ
    (h : FieldOneFiniteStageIdele S) s]
  rw [hh]
  simp

end

end GaloisForLFunctions.RHTower
