import GaloisForLFunctions.RHTower.FieldOnePadicSoninL2
import GaloisForLFunctions.RHTower.FieldOnePadicRamifiedTateEquation258Full
import GaloisForLFunctions.RHTower.FieldOnePadicMultiplicativeHaarTatePairing
import Mathlib.MeasureTheory.Function.LpSpace.DomAct.Continuous

/-!
# Unit invariants in local p-adic Haar L²

The literal `ℤ_pˣ` representation on `L²(ℚ_p)`, its Haar projector,
Bruhat compatibility, and Fourier covariance.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Set Topology TopologicalSpace
open scoped BigOperators ENNReal NNReal ComplexConjugate

variable (p : ℕ) [Fact p.Prime]

@[simp] theorem fieldOnePadicUnit_smul (u : ℤ_[p]ˣ) (x : ℚ_[p]) :
    u • x = ((fieldOnePadicUnitEmbedding p u : ℚ_[p]ˣ) : ℚ_[p]) * x := by
  change (((u : ℤ_[p]) : ℚ_[p])) * x = _
  rw [fieldOnePadicUnitEmbedding_val]

theorem fieldOnePadicUnitMeasurePreserving (u : ℤ_[p]ˣ) :
    MeasurePreserving (fun x : ℚ_[p] => u • x)
      (fieldOnePadicUnitBallNormalizedHaar p)
      (fieldOnePadicUnitBallNormalizedHaar p) := by
  apply MeasurePreserving.mk (measurable_const_smul u)
  rw [show (fun x : ℚ_[p] => u • x) =
      fun x : ℚ_[p] => ((fieldOnePadicUnitEmbedding p u : ℚ_[p]ˣ) : ℚ_[p]) * x by
    funext x
    exact fieldOnePadicUnit_smul p u x]
  change DomMulAct.mk (fieldOnePadicUnitEmbedding p u)⁻¹ •
      fieldOnePadicUnitBallNormalizedHaar p =
    fieldOnePadicUnitBallNormalizedHaar p
  rw [fieldOnePadicUnitBallNormalizedHaar_domSMul, map_inv,
    fieldOnePadicUnitEmbedding_distribHaarChar, inv_one, one_smul]

instance fieldOnePadicUnitContinuousSMul : ContinuousSMul ℤ_[p]ˣ ℚ_[p] where
  continuous_smul := by
    have hcoe : Continuous (fun u : ℤ_[p]ˣ =>
        (((u : ℤ_[p]) : ℚ_[p]))) := by
      have huq : Continuous (fun u : ℤ_[p]ˣ =>
          ((fieldOnePadicUnitEmbedding p u : ℚ_[p]ˣ) : ℚ_[p])) :=
        Units.continuous_val.comp
          ((fieldOnePadicValuationUnitContinuousMulEquiv p).continuous.comp
            (continuous_const.prodMk continuous_id))
      simpa only [fieldOnePadicUnitEmbedding_val] using huq
    change Continuous (fun z : ℤ_[p]ˣ × ℚ_[p] =>
      (((z.1 : ℤ_[p]) : ℚ_[p])) * z.2)
    exact (hcoe.comp continuous_fst).mul
      (continuous_snd : Continuous (fun z : ℤ_[p]ˣ × ℚ_[p] => z.2))

instance fieldOnePadicUnitSMulInvariantMeasure :
    SMulInvariantMeasure ℤ_[p]ˣ ℚ_[p]
      (fieldOnePadicUnitBallNormalizedHaar p) where
  measure_preimage_smul u _s hs :=
    (fieldOnePadicUnitMeasurePreserving p u).measure_preimage hs.nullMeasurableSet

def fieldOnePadicUnitActionL2 (u : ℤ_[p]ˣ) :
    FieldOnePadicL2 p →ₗᵢ[ℂ] FieldOnePadicL2 p :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun x : ℚ_[p] => u • x)
    (fieldOnePadicUnitMeasurePreserving p u)

@[simp] theorem fieldOnePadicUnitActionL2_apply
    (u : ℤ_[p]ˣ) (f : FieldOnePadicL2 p) :
    fieldOnePadicUnitActionL2 p u f =
      Lp.compMeasurePreserving (fun x : ℚ_[p] => u • x)
        (fieldOnePadicUnitMeasurePreserving p u) f := rfl

theorem fieldOnePadicUnitActionL2_ae
    (u : ℤ_[p]ˣ) (f : FieldOnePadicL2 p) :
    (fieldOnePadicUnitActionL2 p u f : ℚ_[p] → ℂ) =ᵐ[
      fieldOnePadicUnitBallNormalizedHaar p]
      fun x => f (u • x) := by
  exact Lp.coeFn_compMeasurePreserving f
    (fieldOnePadicUnitMeasurePreserving p u)

def FieldOnePadicUnitInvariantL2 : Submodule ℂ (FieldOnePadicL2 p) :=
  ⨅ u : ℤ_[p]ˣ,
    LinearMap.ker ((fieldOnePadicUnitActionL2 p u).toLinearMap - LinearMap.id)

theorem mem_fieldOnePadicUnitInvariantL2_iff
    (f : FieldOnePadicL2 p) :
    f ∈ FieldOnePadicUnitInvariantL2 p ↔
      ∀ u : ℤ_[p]ˣ, fieldOnePadicUnitActionL2 p u f = f := by
  simp only [FieldOnePadicUnitInvariantL2, Submodule.mem_iInf,
    LinearMap.mem_ker, LinearMap.sub_apply, LinearIsometry.coe_toLinearMap,
    LinearMap.id_apply, sub_eq_zero]

theorem fieldOnePadicUnitActionL2_bruhat
    (u : ℤ_[p]ˣ) (f : compactlySupportedLocallyConstant ℚ_[p]) :
    fieldOnePadicUnitActionL2 p u (fieldOnePadicBruhatToL2Linear p f) =
      fieldOnePadicBruhatToL2Linear p
        (fieldOnePadicBruhatDilation p (fieldOnePadicUnitEmbedding p u) f) := by
  change Lp.compMeasurePreserving (fun x : ℚ_[p] => u • x)
      (fieldOnePadicUnitMeasurePreserving p u)
      ((fieldOnePadicBruhat_memLp p f).toLp f.1) =
    (fieldOnePadicBruhat_memLp p
      (fieldOnePadicBruhatDilation p (fieldOnePadicUnitEmbedding p u) f)).toLp
      (fieldOnePadicBruhatDilation p (fieldOnePadicUnitEmbedding p u) f).1
  rw [Lp.toLp_compMeasurePreserving]
  exact MemLp.toLp_congr
    ((fieldOnePadicBruhat_memLp p f).comp_measurePreserving
      (fieldOnePadicUnitMeasurePreserving p u))
    (fieldOnePadicBruhat_memLp p
      (fieldOnePadicBruhatDilation p (fieldOnePadicUnitEmbedding p u) f))
    (Filter.Eventually.of_forall fun x => by
      change f.1 (u • x) =
        f.1 (((fieldOnePadicUnitEmbedding p u : ℚ_[p]ˣ) : ℚ_[p]) * x)
      rw [fieldOnePadicUnit_smul])

theorem fieldOnePadicL2Fourier_unitAction
    (u : ℤ_[p]ˣ) (f : FieldOnePadicL2 p) :
    fieldOnePadicL2Fourier p (fieldOnePadicUnitActionL2 p u f) =
      fieldOnePadicUnitActionL2 p u⁻¹ (fieldOnePadicL2Fourier p f) := by
  let A : FieldOnePadicL2 p →L[ℂ] FieldOnePadicL2 p :=
    (fieldOnePadicL2Fourier p).toLinearIsometry.toContinuousLinearMap.comp
      (fieldOnePadicUnitActionL2 p u).toContinuousLinearMap
  let B : FieldOnePadicL2 p →L[ℂ] FieldOnePadicL2 p :=
    (fieldOnePadicUnitActionL2 p u⁻¹).toContinuousLinearMap.comp
      (fieldOnePadicL2Fourier p).toLinearIsometry.toContinuousLinearMap
  have heq : A = B := by
    have hcomp : (A : FieldOnePadicL2 p → FieldOnePadicL2 p) ∘
          fieldOnePadicBruhatToL2Linear p =
        (B : FieldOnePadicL2 p → FieldOnePadicL2 p) ∘
      fieldOnePadicBruhatToL2Linear p := by
      funext h
      change fieldOnePadicL2Fourier p
          (fieldOnePadicUnitActionL2 p u
            (fieldOnePadicBruhatToL2Linear p h)) =
        fieldOnePadicUnitActionL2 p u⁻¹
          (fieldOnePadicL2Fourier p
            (fieldOnePadicBruhatToL2Linear p h))
      rw [fieldOnePadicUnitActionL2_bruhat,
        fieldOnePadicL2Fourier_bruhat,
        fieldOnePadicL2Fourier_bruhat,
        fieldOnePadicUnitActionL2_bruhat]
      apply congrArg (fieldOnePadicBruhatToL2Linear p)
      exact fieldOnePadicBruhatFourierLinear_dilation_unit p u h
    have hfun : (A : FieldOnePadicL2 p → FieldOnePadicL2 p) = B :=
      (fieldOnePadicBruhatToL2Linear_denseRange p).equalizer
        A.continuous B.continuous hcomp
    exact DFunLike.ext A B fun x => congrFun hfun x
  exact congrArg (fun T : FieldOnePadicL2 p →L[ℂ] FieldOnePadicL2 p => T f) heq

theorem fieldOnePadicL2Fourier_mem_unitInvariant
    {f : FieldOnePadicL2 p} (hf : f ∈ FieldOnePadicUnitInvariantL2 p) :
    fieldOnePadicL2Fourier p f ∈ FieldOnePadicUnitInvariantL2 p := by
  rw [mem_fieldOnePadicUnitInvariantL2_iff] at hf ⊢
  intro u
  calc
    fieldOnePadicUnitActionL2 p u (fieldOnePadicL2Fourier p f) =
        fieldOnePadicUnitActionL2 p (u⁻¹)⁻¹
          (fieldOnePadicL2Fourier p f) := by rw [inv_inv]
    _ = fieldOnePadicL2Fourier p
          (fieldOnePadicUnitActionL2 p u⁻¹ f) :=
      (fieldOnePadicL2Fourier_unitAction p u⁻¹ f).symm
    _ = fieldOnePadicL2Fourier p f := by rw [hf u⁻¹]

def fieldOnePadicUnitAverageL2 (f : FieldOnePadicL2 p) :
    FieldOnePadicL2 p :=
  ∫ u : ℤ_[p]ˣ, fieldOnePadicUnitActionL2 p u f
    ∂fieldOnePadicUnitNormalizedHaar p

theorem continuous_fieldOnePadicUnitActionL2_orbit
    (f : FieldOnePadicL2 p) :
    Continuous (fun u : ℤ_[p]ˣ => fieldOnePadicUnitActionL2 p u f) := by
  let g : ℤ_[p]ˣ → C(ℚ_[p], ℚ_[p]) := fun u =>
    ⟨fun x => u • x, continuous_const_smul u⟩
  have hg : Continuous g := by
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact continuous_smul
  have h := (continuous_const : Continuous
      (fun _u : ℤ_[p]ˣ => f)).compMeasurePreservingLp hg
        (fun u => fieldOnePadicUnitMeasurePreserving p u) (by norm_num)
  exact h

theorem integrable_fieldOnePadicUnitActionL2_orbit
    (f : FieldOnePadicL2 p) :
    Integrable (fun u : ℤ_[p]ˣ => fieldOnePadicUnitActionL2 p u f)
      (fieldOnePadicUnitNormalizedHaar p) :=
  (continuous_fieldOnePadicUnitActionL2_orbit p f).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem norm_fieldOnePadicUnitAverageL2_le (f : FieldOnePadicL2 p) :
    ‖fieldOnePadicUnitAverageL2 p f‖ ≤ ‖f‖ := by
  unfold fieldOnePadicUnitAverageL2
  have h := norm_integral_le_of_norm_le_const
    (μ := fieldOnePadicUnitNormalizedHaar p)
    (f := fun u : ℤ_[p]ˣ => fieldOnePadicUnitActionL2 p u f)
    (C := ‖f‖) (Filter.Eventually.of_forall fun u => by simp)
  simpa only [Measure.real, fieldOnePadicUnitNormalizedHaar_univ,
    ENNReal.toReal_one, mul_one] using h

theorem fieldOnePadicUnitAverageL2_eq_self_of_invariant
    {f : FieldOnePadicL2 p} (hf : f ∈ FieldOnePadicUnitInvariantL2 p) :
    fieldOnePadicUnitAverageL2 p f = f := by
  rw [mem_fieldOnePadicUnitInvariantL2_iff] at hf
  unfold fieldOnePadicUnitAverageL2
  simp_rw [hf]
  rw [integral_const, Measure.real,
    fieldOnePadicUnitNormalizedHaar_univ]
  simp

theorem fieldOnePadicUnitAverageL2_sub
    (g f : FieldOnePadicL2 p) :
    fieldOnePadicUnitAverageL2 p (g - f) =
      fieldOnePadicUnitAverageL2 p g -
        fieldOnePadicUnitAverageL2 p f := by
  unfold fieldOnePadicUnitAverageL2
  rw [← integral_sub
    (integrable_fieldOnePadicUnitActionL2_orbit p g)
    (integrable_fieldOnePadicUnitActionL2_orbit p f)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    exact map_sub (fieldOnePadicUnitActionL2 p u) g f

theorem fieldOnePadicUnitAverageL2_sub_invariant
    (g : FieldOnePadicL2 p) {f : FieldOnePadicL2 p}
    (hf : f ∈ FieldOnePadicUnitInvariantL2 p) :
    fieldOnePadicUnitAverageL2 p g - f =
      fieldOnePadicUnitAverageL2 p (g - f) := by
  calc
    fieldOnePadicUnitAverageL2 p g - f =
        fieldOnePadicUnitAverageL2 p g -
          fieldOnePadicUnitAverageL2 p f := by
      rw [fieldOnePadicUnitAverageL2_eq_self_of_invariant p hf]
    _ = fieldOnePadicUnitAverageL2 p (g - f) :=
      (fieldOnePadicUnitAverageL2_sub p g f).symm

theorem dist_fieldOnePadicUnitAverageL2_le_of_invariant
    (g : FieldOnePadicL2 p) {f : FieldOnePadicL2 p}
    (hf : f ∈ FieldOnePadicUnitInvariantL2 p) :
    dist (fieldOnePadicUnitAverageL2 p g) f ≤ dist g f := by
  simp only [dist_eq_norm]
  rw [fieldOnePadicUnitAverageL2_sub_invariant p g hf]
  exact norm_fieldOnePadicUnitAverageL2_le p (g - f)

theorem fieldOnePadicUnitActionL2_mul
    (u v : ℤ_[p]ˣ) (f : FieldOnePadicL2 p) :
    fieldOnePadicUnitActionL2 p u (fieldOnePadicUnitActionL2 p v f) =
      fieldOnePadicUnitActionL2 p (u * v) f := by
  change Lp.compMeasurePreserving (fun x : ℚ_[p] => u • x)
      (fieldOnePadicUnitMeasurePreserving p u)
      (Lp.compMeasurePreserving (fun x : ℚ_[p] => v • x)
        (fieldOnePadicUnitMeasurePreserving p v) f) =
    Lp.compMeasurePreserving (fun x : ℚ_[p] => (u * v) • x)
      (fieldOnePadicUnitMeasurePreserving p (u * v)) f
  rw [← Lp.compMeasurePreserving_comp_apply]
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f
      ((fieldOnePadicUnitMeasurePreserving p v).comp
        (fieldOnePadicUnitMeasurePreserving p u)),
    Lp.coeFn_compMeasurePreserving f
      (fieldOnePadicUnitMeasurePreserving p (u * v))]
    with x hleft hright
  rw [hleft, hright]
  exact congrArg (fun y : ℚ_[p] => f y) (by
    simp only [Function.comp_apply, smul_smul, mul_comm])

theorem fieldOnePadicUnitAverageL2_mem_invariant
    (f : FieldOnePadicL2 p) :
    fieldOnePadicUnitAverageL2 p f ∈ FieldOnePadicUnitInvariantL2 p := by
  rw [mem_fieldOnePadicUnitInvariantL2_iff]
  intro v
  unfold fieldOnePadicUnitAverageL2
  change (fieldOnePadicUnitActionL2 p v).toContinuousLinearMap
      (∫ u : ℤ_[p]ˣ, fieldOnePadicUnitActionL2 p u f
        ∂fieldOnePadicUnitNormalizedHaar p) = _
  rw [← (fieldOnePadicUnitActionL2 p v).toContinuousLinearMap.integral_comp_comm
    (integrable_fieldOnePadicUnitActionL2_orbit p f)]
  calc
    (∫ u : ℤ_[p]ˣ,
        fieldOnePadicUnitActionL2 p v
          (fieldOnePadicUnitActionL2 p u f)
        ∂fieldOnePadicUnitNormalizedHaar p) =
        ∫ u : ℤ_[p]ˣ,
          fieldOnePadicUnitActionL2 p (u * v) f
          ∂fieldOnePadicUnitNormalizedHaar p := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u => by
        simpa only [mul_comm] using
          fieldOnePadicUnitActionL2_mul p v u f
    _ = ∫ u : ℤ_[p]ˣ, fieldOnePadicUnitActionL2 p u f
          ∂fieldOnePadicUnitNormalizedHaar p :=
      integral_mul_right_eq_self
        (fun u : ℤ_[p]ˣ => fieldOnePadicUnitActionL2 p u f) v

/-- Banach-valued exact Haar quadrature through a finite multiplicative
quotient. This is the vector-valued form needed for Hilbert-space averaging. -/
theorem fieldOneFiniteMulQuotient_sampleSum_eq_nsmul_integral_normed
    {G Q E : Type*} [CommGroup G] [CommGroup Q] [Fintype Q]
    [TopologicalSpace G] [MeasurableSpace G] [BorelSpace G]
    [IsTopologicalGroup G] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E]
    (μ : Measure G) [μ.IsMulLeftInvariant]
    (hμ : μ Set.univ = 1)
    (q : G →* Q) (hq : Function.Surjective q)
    (rep : Q → G) (hrep : ∀ r, q (rep r) = r)
    (f : G → E) (hf : Integrable f μ)
    (hclass : ∀ {x y : G}, q x = q y → f x = f y) :
    ∑ r : Q, f (rep r) =
      Fintype.card Q • (∫ x, f x ∂μ) := by
  have havg (x : G) :
      ∑ r : Q, f (rep r * x) = ∑ r : Q, f (rep r) := by
    obtain ⟨s, hs⟩ := hq (q x)
    apply Finset.sum_equiv (Equiv.mulRight (q x))
    · simp
    · intro r _
      apply hclass
      rw [map_mul, hrep, hrep]
      rfl
  calc
    ∑ r : Q, f (rep r) =
        ∫ _ : G, (∑ r : Q, f (rep r)) ∂μ := by
      rw [integral_const, Measure.real, hμ]
      simp
    _ = ∫ x : G, (∑ r : Q, f (rep r * x)) ∂μ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => (havg x).symm
    _ = ∑ r : Q, ∫ x : G, f (rep r * x) ∂μ := by
      apply integral_finsetSum
      intro r _
      exact hf.comp_mul_left _
    _ = ∑ _r : Q, ∫ x : G, f x ∂μ := by
      apply Finset.sum_congr rfl
      intro r _
      exact integral_mul_left_eq_self f _
    _ = Fintype.card Q • (∫ x, f x ∂μ) := by
      rw [Finset.sum_const, Finset.card_univ]

theorem fieldOnePadicUnit_sampleSum_eq_nsmul_integral_L2
    (n : ℕ) (f : ℤ_[p]ˣ → FieldOnePadicL2 p)
    (hf : Integrable f (fieldOnePadicUnitNormalizedHaar p))
    (hclass : ∀ {x y : ℤ_[p]ˣ},
      fieldOnePadicUnitReduction p n x =
        fieldOnePadicUnitReduction p n y → f x = f y) :
    ∑ r : (ZMod (p ^ n))ˣ,
        f (fieldOnePadicUnitResidueRep p n r) =
      Fintype.card (ZMod (p ^ n))ˣ •
        (∫ u, f u ∂fieldOnePadicUnitNormalizedHaar p) := by
  exact fieldOneFiniteMulQuotient_sampleSum_eq_nsmul_integral_normed
    (fieldOnePadicUnitNormalizedHaar p)
    (fieldOnePadicUnitNormalizedHaar_univ p)
    (fieldOnePadicUnitReduction p n)
    (fieldOnePadicUnitReduction_surjective p n)
    (fieldOnePadicUnitResidueRep p n)
    (fieldOnePadicUnitResidueRep_spec p n)
    f hf hclass

def fieldOnePadicRadializeBruhat
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    compactlySupportedLocallyConstant ℚ_[p] :=
  fieldOnePadicPrimitiveAngularProjection p 0
    (fieldOnePadicConductorZeroCharacter p) f

@[simp] theorem fieldOnePadicRadializeBruhat_apply
    (f : compactlySupportedLocallyConstant ℚ_[p]) (x : ℚ_[p]) :
    (fieldOnePadicRadializeBruhat p f).1 x =
      ∫ u : ℤ_[p]ˣ, f.1 ((((u : ℤ_[p]) : ℚ_[p])) * x)
        ∂fieldOnePadicUnitNormalizedHaar p := by
  unfold fieldOnePadicRadializeBruhat
  rw [fieldOnePadicPrimitiveAngularProjection_apply]
  unfold fieldOnePadicPrimitiveAngularProjectionValue
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    simp only [fieldOnePadicPrimitiveUnitCharacter,
      fieldOnePadicConductorZeroCharacter_apply, one_mul]

theorem fieldOnePadicRadializeBruhat_unitInvariant
    (f : compactlySupportedLocallyConstant ℚ_[p])
    (v : ℤ_[p]ˣ) (x : ℚ_[p]) :
    (fieldOnePadicRadializeBruhat p f).1
        ((((v : ℤ_[p]) : ℚ_[p])) * x) =
      (fieldOnePadicRadializeBruhat p f).1 x := by
  have h := fieldOnePadicPrimitiveAngularProjectionValue_unit_covariance
    p 0 (fieldOnePadicConductorZeroCharacter p) f v x
  rw [fieldOnePadicPrimitiveUnitCharacter,
    fieldOnePadicConductorZeroCharacter_apply, inv_one, one_mul] at h
  exact h

theorem fieldOnePadicUnitActionL2_bruhat_eq_of_reduction_eq
    (N L : ℕ) (f : compactlySupportedLocallyConstant ℚ_[p])
    (hsupport : tsupport (f.1 : ℚ_[p] → ℂ) ⊆
      fieldOnePadicDenominatorStage p N)
    (hperiod : ∀ x : ℚ_[p], ∀ z : ℤ_[p],
      f.1 (x + (p : ℚ_[p]) ^ L * (z : ℚ_[p])) = f.1 x)
    {u v : ℤ_[p]ˣ}
    (hred : fieldOnePadicUnitReduction p (0 + N + L) u =
      fieldOnePadicUnitReduction p (0 + N + L) v) :
    fieldOnePadicUnitActionL2 p u (fieldOnePadicBruhatToL2Linear p f) =
      fieldOnePadicUnitActionL2 p v (fieldOnePadicBruhatToL2Linear p f) := by
  rw [fieldOnePadicUnitActionL2_bruhat,
    fieldOnePadicUnitActionL2_bruhat]
  congr 1
  apply Subtype.ext
  apply LocallyConstant.ext
  intro x
  simpa only [fieldOnePadicBruhatDilation_apply,
    fieldOnePadicUnitEmbedding_val] using
      fieldOnePadicBruhat_unit_action_eq_of_deeperReduction_eq
        p 0 N L f hsupport hperiod (u := u) (v := v) hred x

theorem fieldOnePadicUnitAverageL2_bruhat
    (f : compactlySupportedLocallyConstant ℚ_[p]) :
    fieldOnePadicUnitAverageL2 p (fieldOnePadicBruhatToL2Linear p f) =
      fieldOnePadicBruhatToL2Linear p (fieldOnePadicRadializeBruhat p f) := by
  classical
  obtain ⟨N, L, hsupport, hperiod⟩ :=
    fieldOnePadicBruhat_exists_finiteLevel p f
  let g : FieldOnePadicL2 p := fieldOnePadicBruhatToL2Linear p f
  have hclass : ∀ {u v : ℤ_[p]ˣ},
      fieldOnePadicUnitReduction p (0 + N + L) u =
        fieldOnePadicUnitReduction p (0 + N + L) v →
      fieldOnePadicUnitActionL2 p u g =
        fieldOnePadicUnitActionL2 p v g := by
    intro u v huv
    exact fieldOnePadicUnitActionL2_bruhat_eq_of_reduction_eq
      p N L f hsupport hperiod huv
  have hquad := fieldOnePadicUnit_sampleSum_eq_nsmul_integral_L2
    p (0 + N + L) (fun u : ℤ_[p]ˣ => fieldOnePadicUnitActionL2 p u g)
    (integrable_fieldOnePadicUnitActionL2_orbit p g) hclass
  have hfinite :=
    fieldOnePadicPrimitiveAngularProjection_eq_finiteAverage_of_finiteLevel
      p 0 N L (fieldOnePadicConductorZeroCharacter p) f hsupport hperiod
  rw [fieldOnePadicRadializeBruhat, hfinite,
    fieldOnePadicPrimitiveAngularFiniteAverage, map_sum]
  simp only [map_smul, fieldOnePadicPrimitiveUnitCharacter,
    fieldOnePadicConductorZeroCharacter_apply, mul_one]
  simp_rw [← fieldOnePadicUnitActionL2_bruhat p]
  change fieldOnePadicUnitAverageL2 p g =
    ∑ r : (ZMod (p ^ (0 + N + L)))ˣ,
      (((Fintype.card (ZMod (p ^ (0 + N + L)))ˣ : ℕ) : ℂ)⁻¹) •
        fieldOnePadicUnitActionL2 p
          (fieldOnePadicUnitResidueRep p (0 + N + L) r) g
  rw [← Finset.smul_sum, hquad]
  rw [← Nat.cast_smul_eq_nsmul ℂ]
  have hK : ((Fintype.card (ZMod (p ^ (0 + N + L)))ˣ : ℕ) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [← mul_smul, inv_mul_cancel₀ hK, one_smul]
  rfl

end

end GaloisForLFunctions.RHTower
