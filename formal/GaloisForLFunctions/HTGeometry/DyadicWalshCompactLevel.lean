import GaloisForLFunctions.HTGeometry.DyadicSiblingPartition
import GaloisForLFunctions.HTGeometry.WalshLpBlocks
import GaloisForLFunctions.HTGeometry.LpInjectionCompression
import GaloisForLFunctions.HTGeometry.LaplaceFormationCompletionTopology

/-! # Compact dyadic levels with geometrically small Walsh norm

Each level factors through a compact reciprocal diagonal, an input coordinate
restriction, the proven block Walsh isometry, and a zero extension.
-/

namespace GaloisForLFunctions.HTGeometry
noncomputable section
open Filter RHTower
open scoped Topology

def dyadicColumnWeight (k j : ℕ) : ℂ :=
  ((2 * max ((2 ^ k : ℕ) : ℝ) ((j : ℝ) + 1))⁻¹ : ℝ)

theorem dyadicColumnWeight_norm (k j : ℕ) :
    ‖dyadicColumnWeight k j‖ = (2 * max ((2 ^ k : ℕ) : ℝ) ((j : ℝ) + 1))⁻¹ := by
  rw [dyadicColumnWeight, Complex.norm_real, Real.norm_of_nonneg (by positivity)]

theorem dyadicColumnWeight_bound (k j : ℕ) :
    ‖dyadicColumnWeight k j‖ ≤ (2 * ((2 ^ k : ℕ) : ℝ))⁻¹ := by
  rw [dyadicColumnWeight_norm]
  exact inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num))

theorem dyadicColumnWeight_tendsto (k : ℕ) :
    Tendsto (fun j => ‖dyadicColumnWeight k j‖) atTop (𝓝 0) := by
  have hb (j : ℕ) : ‖dyadicColumnWeight k j‖ ≤ (1 / 2 : ℝ) * (1 / ((j : ℝ) + 1)) := by
    rw [dyadicColumnWeight_norm]
    calc
      _ ≤ (2 * ((j : ℝ) + 1))⁻¹ :=
        inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_left (le_max_right _ _) (by norm_num))
      _ = _ := by rw [mul_inv_rev]; ring
  exact squeeze_zero (fun _ => norm_nonneg _) hb
    (by simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul (1 / 2 : ℝ))

theorem dyadicColumnWeight_right (k : ℕ) (p : ℕ × Fin (2 ^ k)) :
    dyadicColumnWeight k (dyadicChild k 1 p) =
      ((2 * ((dyadicChild k 1 p : ℕ) : ℝ) + 2)⁻¹ : ℝ) := by
  have h : ((2 ^ k : ℕ) : ℝ) ≤ (dyadicChild k 1 p : ℝ) + 1 := by
    exact_mod_cast (Nat.le_succ_of_le (dyadicChild_right_lower k p))
  rw [dyadicColumnWeight, max_eq_right h]
  congr 2
  ring

def dyadicColumnOperator (k : ℕ) : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  lpDiagonalCLM (dyadicColumnWeight k) (by positivity) (dyadicColumnWeight_bound k)

theorem dyadicColumnOperator_compact (k : ℕ) : IsCompactOperator (dyadicColumnOperator k) :=
  isCompactOperator_lpDiagonalCLM _ _ _ (dyadicColumnWeight_tendsto k)

/-- One complete dyadic level, including every sibling block. -/
def dyadicWalshLevel (k : ℕ) : lp (fun _ : ℕ => ℂ) 2 →L[ℂ] lp (fun _ : ℕ => ℂ) 2 :=
  (Real.sqrt ((2 ^ k : ℕ) : ℝ) : ℂ) •
    (lpScalarInjection (dyadicChild k 0) (dyadicChild_injective k 0)).toContinuousLinearMap.comp
      ((walshBlockIsometry ℕ k).toLinearIsometry.toContinuousLinearMap.comp
        ((lpCoordinatePullback (E := ℂ) (dyadicChild k 1) (dyadicChild_injective k 1)).comp
          (dyadicColumnOperator k)))

theorem dyadicWalshLevel_compact (k : ℕ) : IsCompactOperator (dyadicWalshLevel k) :=
  (((dyadicColumnOperator_compact k).clm_comp
    (lpCoordinatePullback (E := ℂ) (dyadicChild k 1) (dyadicChild_injective k 1))).clm_comp
      (walshBlockIsometry ℕ k).toLinearIsometry.toContinuousLinearMap).clm_comp
        (lpScalarInjection (dyadicChild k 0) (dyadicChild_injective k 0)).toContinuousLinearMap
    |>.smul (Real.sqrt ((2 ^ k : ℕ) : ℝ) : ℂ)

def dyadicWalshMajorant (k : ℕ) : ℝ :=
  Real.sqrt ((2 ^ k : ℕ) : ℝ) * (2 * ((2 ^ k : ℕ) : ℝ))⁻¹

theorem dyadicWalshLevel_norm_le (k : ℕ) : ‖dyadicWalshLevel k‖ ≤ dyadicWalshMajorant k := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by unfold dyadicWalshMajorant; positivity)
  intro x
  change ‖(Real.sqrt ((2 ^ k : ℕ) : ℝ) : ℂ) •
    lpScalarInjection (dyadicChild k 0) (dyadicChild_injective k 0)
      (walshBlockIsometry ℕ k
        (lpCoordinatePullback (E := ℂ) (dyadicChild k 1) (dyadicChild_injective k 1)
          (dyadicColumnOperator k x)))‖ ≤ _
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (Real.sqrt_nonneg _),
    LinearIsometry.norm_map, LinearIsometryEquiv.norm_map]
  have hp := lpCoordinatePullbackLinear_norm_le (dyadicChild k 1) (dyadicChild_injective k 1)
    (dyadicColumnOperator k x)
  have hd := norm_lpDiagonalLM_le (dyadicColumnWeight k) (by positivity)
    (dyadicColumnWeight_bound k) x
  have h : ‖lpCoordinatePullback (E := ℂ) (dyadicChild k 1) (dyadicChild_injective k 1)
      (dyadicColumnOperator k x)‖ ≤ (2 * ((2 ^ k : ℕ) : ℝ))⁻¹ * ‖x‖ := hp.trans hd
  exact (mul_le_mul_of_nonneg_left h (Real.sqrt_nonneg _)).trans_eq (mul_assoc _ _ _).symm

theorem dyadicWalshMajorant_geometric (k : ℕ) :
    dyadicWalshMajorant k = (1 / 2 : ℝ) * ((Real.sqrt 2)⁻¹) ^ k := by
  have hp : Real.sqrt ((2 ^ k : ℕ) : ℝ) = (Real.sqrt 2) ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, Nat.cast_mul, Real.sqrt_mul (by positivity), ih, Nat.cast_ofNat,
          pow_succ]
  have hd : (0 : ℝ) < ((2 ^ k : ℕ) : ℝ) := by positivity
  have hs : Real.sqrt ((2 ^ k : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hd).ne'
  calc
    dyadicWalshMajorant k = (1 / 2 : ℝ) * (Real.sqrt ((2 ^ k : ℕ) : ℝ))⁻¹ := by
      unfold dyadicWalshMajorant
      field_simp
      nlinarith [Real.sq_sqrt hd.le]
    _ = _ := by rw [hp, inv_pow]

theorem dyadicWalshMajorant_summable : Summable dyadicWalshMajorant := by
  have hg : Summable (fun k : ℕ => ((Real.sqrt 2)⁻¹) ^ k) := by
    apply summable_geometric_of_norm_lt_one
    rw [norm_inv, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
    exact (inv_lt_one₀ (by positivity)).2 Real.one_lt_sqrt_two
  simpa only [← dyadicWalshMajorant_geometric] using hg.mul_left (1 / 2 : ℝ)

theorem dyadicWalshLevel_summable : Summable dyadicWalshLevel :=
  Summable.of_norm_bounded dyadicWalshMajorant_summable dyadicWalshLevel_norm_le

end
end GaloisForLFunctions.HTGeometry
