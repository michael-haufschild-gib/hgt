import GaloisForLFunctions.HTGeometry.CompletedObserverTimeTorus
import GaloisForLFunctions.HTGeometry.TorusFourierWeakConvergenceLaw
import GaloisForLFunctions.HTGeometry.TorusReturnExponentLaw

/-!
# Return volume of an integer character embedding

The completed time of a finite frequency packet is the image of a presenting torus under the
integer character matrix of the packet.  This file computes the order of the Haar volume of the
pulled-back return target.

A nonsingular integer square matrix pushes torus Haar measure to itself — its Fourier coefficients
are those of Haar because a nonsingular matrix has trivial left kernel — so preimages along it have
unchanged measure.  The pulled-back return target contains a ball of radius proportional to the
tolerance, because every character is Lipschitz with the constant given by its row sum, and it is
contained in the preimage of a ball of radius twice the tolerance along any nonsingular square
selection of characters.  Both bounds are of order `ε` to the presenting dimension, so the
logarithmic return exponent is exactly that dimension.
-/

open Filter MeasureTheory Metric Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {k : Type*} [Fintype k] [DecidableEq k]

/-- A nonsingular integer matrix has trivial left kernel. -/
theorem integerVecMul_eq_zero_iff {N : Matrix k k ℤ} (hdet : N.det ≠ 0) (n : k → ℤ) :
    (fun j => ∑ i, n i * N i j) = 0 ↔ n = 0 := by
  constructor
  · intro hn
    exact Matrix.eq_zero_of_vecMul_eq_zero hdet hn
  · rintro rfl
    funext j
    simp

/-- **A nonsingular integer matrix preserves torus Haar measure.**  Its pushforward has the Fourier
coefficients of Haar measure. -/
theorem orbitClosureHaar_eq_haar {N : Matrix k k ℤ} (hdet : N.det ≠ 0) :
    orbitClosureHaar (N : k → k → ℤ) = finiteTorusHaarProbabilityMeasure k := by
  refine probabilityMeasure_ext_of_mFourier_integral_eq _ _ fun n => ?_
  rw [orbitClosureHaar_mFourier_integral, finiteTorusHaarProbabilityMeasure_mFourier_integral,
    if_congr (integerVecMul_eq_zero_iff hdet n) rfl rfl]

/-- Preimages along a nonsingular integer torus endomorphism have unchanged Haar measure. -/
theorem measure_preimage_torusIntegerHom {N : Matrix k k ℤ} (hdet : N.det ≠ 0)
    {A : Set (UnitAddTorus k)} (hA : MeasurableSet A) :
    (finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k))
        (torusIntegerHom (N : k → k → ℤ) ⁻¹' A)
      = (finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)) A := by
  have hmap := congrArg (fun μ : ProbabilityMeasure (UnitAddTorus k) =>
    (μ : Measure (UnitAddTorus k))) (orbitClosureHaar_eq_haar hdet)
  simp only [orbitClosureHaar, ProbabilityMeasure.toMeasure_map] at hmap
  rw [← Measure.map_apply (continuous_torusIntegerHom (N : k → k → ℤ)).measurable hA, hmap]

variable {d : Type*} [Fintype d]

/-- A crude uniform bound for the row sums of an integer character matrix. -/
def torusRowBound (M : d → k → ℤ) : ℝ := 1 + ∑ i, ∑ j, ‖M i j‖

omit [DecidableEq k] in
theorem one_le_torusRowBound (M : d → k → ℤ) : 1 ≤ torusRowBound M := by
  have : (0 : ℝ) ≤ ∑ i, ∑ j, ‖M i j‖ :=
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _
  simp only [torusRowBound]
  linarith

omit [DecidableEq k] in
theorem torusRowBound_pos (M : d → k → ℤ) : 0 < torusRowBound M :=
  lt_of_lt_of_le one_pos (one_le_torusRowBound M)

omit [DecidableEq k] in
theorem rowSum_le_torusRowBound (M : d → k → ℤ) (i : d) :
    ∑ j, ‖M i j‖ ≤ torusRowBound M := by
  have hmem : (∑ j, ‖M i j‖) ≤ ∑ i', ∑ j, ‖M i' j‖ :=
    Finset.single_le_sum (f := fun i' => ∑ j, ‖M i' j‖)
      (fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _) (Finset.mem_univ i)
  simp only [torusRowBound]
  linarith

/-- The pulled-back anchored return target of an integer character family. -/
def integerReturnPreimage (M : d → k → ℤ) (ε : ℝ) : Set (UnitAddTorus k) :=
  {u | ∀ i, dist (torusIntegerHom M u i) 0 ≤ ε}

/-- The square character matrix selected by an index injection. -/
def selectedSquare (M : d → k → ℤ) (σ : k → d) : Matrix k k ℤ :=
  Matrix.of fun a b => M (σ a) b

omit [DecidableEq k] in
/-- Every character is Lipschitz with its row-sum constant, so a small ball lies in the pulled-back
return target. -/
theorem ball_subset_integerReturnPreimage (M : d → k → ℤ) {ε : ℝ} (hε : 0 < ε) :
    Metric.ball (0 : UnitAddTorus k) (ε / torusRowBound M) ⊆ integerReturnPreimage M ε := by
  intro u hu
  have hL : 0 < torusRowBound M := torusRowBound_pos M
  have hr : 0 < ε / torusRowBound M := div_pos hε hL
  have hcoord : ∀ j, ‖u j‖ < ε / torusRowBound M := by
    have hall := (dist_pi_lt_iff hr).mp (mem_ball.mp hu)
    intro j
    simpa [dist_zero_right] using hall j
  intro i
  have hnorm : ‖torusIntegerHom M u i‖ ≤ ∑ j, ‖M i j‖ * ‖u j‖ := by
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun j _ => ?_)
    exact norm_zsmul_le (M i j) (u j)
  have hbound : ∑ j, ‖M i j‖ * ‖u j‖ ≤ (∑ j, ‖M i j‖) * (ε / torusRowBound M) := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    exact mul_le_mul_of_nonneg_left (hcoord j).le (norm_nonneg _)
  have hfinal : (∑ j, ‖M i j‖) * (ε / torusRowBound M) ≤ ε := by
    calc (∑ j, ‖M i j‖) * (ε / torusRowBound M)
        ≤ torusRowBound M * (ε / torusRowBound M) :=
          mul_le_mul_of_nonneg_right (rowSum_le_torusRowBound M i) hr.le
      _ = ε := by field_simp
  rw [dist_zero_right]
  linarith [hnorm, hbound, hfinal]

omit [DecidableEq k] [Fintype d] in
/-- A nonsingular square selection of characters confines the pulled-back return target to the
preimage of a ball of twice the radius. -/
theorem integerReturnPreimage_subset_preimage_ball (M : d → k → ℤ) (σ : k → d) {ε : ℝ}
    (hε : 0 < ε) :
    integerReturnPreimage M ε ⊆
      torusIntegerHom ((selectedSquare M σ : Matrix k k ℤ) : k → k → ℤ) ⁻¹'
        Metric.ball (0 : UnitAddTorus k) (2 * ε) := by
  intro u hu
  rw [Set.mem_preimage, mem_ball, dist_pi_lt_iff (by linarith)]
  intro a
  have hval : torusIntegerHom ((selectedSquare M σ : Matrix k k ℤ) : k → k → ℤ) u a
      = torusIntegerHom M u (σ a) := rfl
  rw [hval]
  have hbound := hu (σ a)
  simp only [Pi.zero_apply] at hbound ⊢
  linarith

/-- **A spanning integer character family contains a nonsingular square selection.**  If the rows
of the character matrix span the rational presenting space, some `k` of them are a basis. -/
theorem exists_selectedSquare_det_ne_zero (M : d → k → ℤ)
    (hspan : Submodule.span ℚ
        (Set.range fun i : d => ((fun j => (M i j : ℚ)) : k → ℚ)) = ⊤) :
    ∃ σ : k → d, (selectedSquare M σ).det ≠ 0 := by
  classical
  by_cases hk : IsEmpty k
  · haveI := hk
    exact ⟨fun x => isEmptyElim x, by rw [Matrix.det_isEmpty]; exact one_ne_zero⟩
  haveI : Nonempty k := not_isEmpty_iff.mp hk
  obtain ⟨κ, a, hainj, hsp, hli⟩ :=
    exists_linearIndependent' ℚ fun i : d => ((fun j => (M i j : ℚ)) : k → ℚ)
  haveI : Finite κ := Finite.of_injective a hainj
  haveI : Fintype κ := Fintype.ofFinite κ
  rw [hspan] at hsp
  let B : Module.Basis κ ℚ (k → ℚ) := Module.Basis.mk hli (le_of_eq hsp.symm)
  have hcard : Fintype.card k = Fintype.card κ := by
    have h1 := Module.finrank_eq_card_basis B
    have h2 := Module.finrank_fintype_fun_eq_card ℚ (η := k)
    omega
  let e : k ≃ κ := Fintype.equivOfCardEq hcard
  refine ⟨a ∘ e, fun hdet => ?_⟩
  have hindep : LinearIndependent ℚ
      ((selectedSquare M (a ∘ e)).map (Int.cast : ℤ → ℚ)).row := hli.comp e e.injective
  have hne : ((selectedSquare M (a ∘ e)).map (Int.cast : ℤ → ℚ)).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).mp
      (Matrix.linearIndependent_rows_iff_isUnit.mp hindep)).ne_zero
  apply hne
  have hmap := RingHom.map_det (Int.castRingHom ℚ) (selectedSquare M (a ∘ e))
  simp only [RingHom.mapMatrix_apply, Int.coe_castRingHom] at hmap
  rw [← hmap, hdet]
  simp

/-- **Return-volume law for an integer character embedding.**  If some square selection of the
characters is nonsingular, the pulled-back return target has Haar volume of exact order `ε` to the
presenting dimension. -/
theorem integerReturnPreimage_measure_sandwich (M : d → k → ℤ) (σ : k → d)
    (hdet : (selectedSquare M σ).det ≠ 0) :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (2 / torusRowBound M) ^ Fintype.card k * ε ^ Fintype.card k ≤
          ((finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k))
            (integerReturnPreimage M ε)).toReal ∧
        ((finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k))
            (integerReturnPreimage M ε)).toReal ≤
          (4 : ℝ) ^ Fintype.card k * ε ^ Fintype.card k := by
  have hL : 0 < torusRowBound M := torusRowBound_pos M
  have hL1 : 1 ≤ torusRowBound M := one_le_torusRowBound M
  have hIoo : Set.Ioo (0 : ℝ) (1 / 4) ∈ 𝓝[>] (0 : ℝ) := Ioo_mem_nhdsGT (by norm_num)
  filter_upwards [eventually_of_mem hIoo fun _ h => h] with ε hε
  have hεpos : 0 < ε := hε.1
  have hεsmall : ε < 1 / 4 := hε.2
  have hsmall1 : ε / torusRowBound M ≤ 1 / 2 := by
    have : ε / torusRowBound M ≤ ε := by
      rw [div_le_iff₀ hL]
      nlinarith
    linarith
  have hsmall2 : 2 * ε ≤ 1 / 2 := by linarith
  constructor
  · have hmono := measure_mono
      (μ := (finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)))
      (ball_subset_integerReturnPreimage M hεpos)
    have hle := (ENNReal.toReal_le_toReal
      (measure_ne_top (finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)) _)
      (measure_ne_top (finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)) _)).mpr
      hmono
    rw [toReal_finiteTorusHaar_ball (0 : UnitAddTorus k) (by positivity) hsmall1] at hle
    calc (2 / torusRowBound M) ^ Fintype.card k * ε ^ Fintype.card k
        = (2 * (ε / torusRowBound M)) ^ Fintype.card k := by
          rw [← mul_pow]
          ring_nf
      _ ≤ _ := hle
  · have hmono := measure_mono
      (μ := (finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)))
      (integerReturnPreimage_subset_preimage_ball M σ hεpos)
    rw [measure_preimage_torusIntegerHom hdet measurableSet_ball] at hmono
    have hle := (ENNReal.toReal_le_toReal
      (measure_ne_top (finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)) _)
      (measure_ne_top (finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k)) _)).mpr
      hmono
    rw [toReal_finiteTorusHaar_ball (0 : UnitAddTorus k) (by positivity) hsmall2] at hle
    calc ((finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k))
          (integerReturnPreimage M ε)).toReal
        ≤ (2 * (2 * ε)) ^ Fintype.card k := hle
      _ = (4 : ℝ) ^ Fintype.card k * ε ^ Fintype.card k := by
          rw [← mul_pow]
          ring_nf

/-- **Local return exponent of an integer character embedding.**  The logarithmic Haar return
exponent of the pulled-back target is exactly the presenting dimension. -/
theorem tendsto_log_integerReturnPreimage_div_log (M : d → k → ℤ) (σ : k → d)
    (hdet : (selectedSquare M σ).det ≠ 0) :
    Tendsto (fun ε => Real.log
        ((finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k))
          (integerReturnPreimage M ε)).toReal / Real.log ε)
      (𝓝[>] 0) (𝓝 (Fintype.card k : ℝ)) := by
  have hL : 0 < torusRowBound M := torusRowBound_pos M
  have hsand := integerReturnPreimage_measure_sandwich M σ hdet
  refine tendsto_log_div_log_of_power_sandwich
    (c₁ := (2 / torusRowBound M) ^ Fintype.card k) (c₂ := (4 : ℝ) ^ Fintype.card k)
    (by positivity) (by positivity) ?_ ?_
  · filter_upwards [hsand] with ε hε
    exact hε.1
  · filter_upwards [hsand] with ε hε
    exact hε.2

/-- **Local return exponent from a spanning integer character family.**  If the integer characters
span the rational presenting space — that is, if the presentation of the frequency packet is
minimal — the logarithmic Haar return exponent of the pulled-back target is exactly the presenting
dimension, with no further hypothesis. -/
theorem tendsto_log_integerReturnPreimage_div_log_of_span (M : d → k → ℤ)
    (hspan : Submodule.span ℚ
        (Set.range fun i : d => ((fun j => (M i j : ℚ)) : k → ℚ)) = ⊤) :
    Tendsto (fun ε => Real.log
        ((finiteTorusHaarProbabilityMeasure k : Measure (UnitAddTorus k))
          (integerReturnPreimage M ε)).toReal / Real.log ε)
      (𝓝[>] 0) (𝓝 (Fintype.card k : ℝ)) := by
  obtain ⟨σ, hσ⟩ := exists_selectedSquare_det_ne_zero M hspan
  exact tendsto_log_integerReturnPreimage_div_log M σ hσ

end

end GaloisForLFunctions.HTGeometry
