import GaloisForLFunctions.ExceptionalLayerTheory.NonstationaryGaussianTypeII
import GaloisForLFunctions.RHTower.Sieve.TypeIICoefficientEnergy
import GaloisForLFunctions.RHTower.Sieve.GapSums

/-!
# An explicit arithmetic saving for Gaussian Vaughan rectangles

Chebyshev's bound and the second divisor moment control both actual
Vaughan coefficient energies. Together with nonstationary correlations,
this gives an explicit inverse-height saving in the squared block norm,
up to logarithmic factors, while retaining Gaussian damping.
-/

open Complex Finset RHTower RHTower.Sieve

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

/-- The arithmetic envelope after both Vaughan coefficient energies have been bounded. -/
def gaussianVaughanDyadicEnvelope (σ α ξ : ℝ) (D M : ℕ) : ℝ :=
  ((D : ℝ) * M * (D : ℝ) ^ (-σ) * (M : ℝ) ^ (-σ)) ^ 2 *
    Real.log (2 * (D : ℝ)) * (1 + invSum (2 * M) ^ 3) *
      Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) *
        (1 / (M : ℝ) + 2 * Real.pi * (1 + Real.log (2 * (M : ℝ))) /
          (ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2))

private theorem dyadic_weighted_energy_le {σ : ℝ} (hσ : 0 ≤ σ) (f : ℕ → ℂ)
    {D : ℕ} (hD : 1 ≤ D) :
    (∑ d ∈ Ico D (2 * D), ‖f d * (((d : ℝ) ^ (-σ) : ℝ) : ℂ)‖ ^ 2) ≤
      ((D : ℝ) ^ (-σ)) ^ 2 * ∑ d ∈ Icc 1 (2 * D), ‖f d‖ ^ 2 := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  calc
    _ ≤ ∑ d ∈ Ico D (2 * D), ((D : ℝ) ^ (-σ)) ^ 2 * ‖f d‖ ^ 2 := by
      apply sum_le_sum
      intro d hd
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _), mul_pow, mul_comm]
      have hw : (d : ℝ) ^ (-σ) ≤ (D : ℝ) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos hD0 (by exact_mod_cast (mem_Ico.mp hd).1) (neg_nonpos.mpr hσ)
      gcongr
    _ ≤ ∑ d ∈ Icc 1 (2 * D), ((D : ℝ) ^ (-σ)) ^ 2 * ‖f d‖ ^ 2 := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact mem_Icc.mpr ⟨hD.trans (mem_Ico.mp hd).1, (mem_Ico.mp hd).2.le⟩
      · intro d _ _
        positivity
    _ = _ := (mul_sum _ _ _).symm

/-- A uniform arithmetic bound for each Gaussian Vaughan rectangle.
The constant is independent of height, cutoffs, abscissa and damping. -/
theorem exists_gaussianVaughan_dyadic_envelope_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ α ξ t : ℝ) (A B D M U V : ℕ),
      0 ≤ σ → 0 ≤ α → 0 < ξ → 1 ≤ A → 1 ≤ B → 1 ≤ D → 1 ≤ M →
      16 * ξ * D * (M : ℝ) ^ 2 ≤ Real.pi →
      ‖gaussianVaughanDyadicSum σ α ξ t A B D M U V‖ ^ 2 ≤
        C * gaussianVaughanDyadicEnvelope σ α ξ D M := by
  obtain ⟨C, hC, hlong⟩ := exists_sum_typeIILong_sq_le
  refine ⟨8 * C, by positivity, ?_⟩
  intro σ α ξ t A B D M U V hσ hα hξ hA hB hD hM hband
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlogD : 0 ≤ Real.log (2 * (D : ℝ)) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ 2 * D by omega))
  have hlogM : 0 ≤ Real.log (2 * (M : ℝ)) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ 2 * M by omega))
  have hL := hlong U (2 * D) (by omega)
  rw [Ico_add_one_right_eq_Icc] at hL
  have hS := sum_typeIIShort_sq_le V (2 * M)
  have hEa : (∑ d ∈ Ico D (2 * D),
      ‖((typeIILong U d : ℝ) : ℂ) * (((d : ℝ) ^ (-σ) : ℝ) : ℂ)‖ ^ 2) ≤
      ((D : ℝ) ^ (-σ)) ^ 2 * (C * (2 * (D : ℝ)) * Real.log (2 * (D : ℝ))) := by
    refine (dyadic_weighted_energy_le hσ (fun d => ((typeIILong U d : ℝ) : ℂ)) hD).trans ?_
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hL
  have hEb : (∑ m ∈ Ico M (2 * M),
      ‖((typeIIShort V m : ℝ) : ℂ) * (((m : ℝ) ^ (-σ) : ℝ) : ℂ)‖ ^ 2) ≤
      ((M : ℝ) ^ (-σ)) ^ 2 * (4 * (M : ℝ) * (1 + invSum (2 * M) ^ 3)) := by
    refine (dyadic_weighted_energy_le hσ (fun m => ((typeIIShort V m : ℝ) : ℂ)) hM).trans ?_
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    have he : 2 * ((2 * M : ℕ) : ℝ) + 2 * (((2 * M : ℕ) : ℝ) * invSum (2 * M) ^ 3) =
        4 * (M : ℝ) * (1 + invSum (2 * M) ^ 3) := by push_cast; ring
    exact hS.trans_eq he
  have hEa0 : 0 ≤ ((D : ℝ) ^ (-σ)) ^ 2 * (C * (2 * (D : ℝ)) * Real.log (2 * (D : ℝ))) := by
    positivity
  have hE := mul_le_mul hEa hEb (sum_nonneg fun _ _ => sq_nonneg _) hEa0
  have hrow0 : 0 ≤ gaussianDyadicRowBound ξ D M := by
    unfold gaussianDyadicRowBound
    positivity
  have hrow : gaussianDyadicRowBound ξ D M = ((D : ℝ) * M) *
      (1 / (M : ℝ) + 2 * Real.pi * (1 + Real.log (2 * (M : ℝ))) /
        (ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2)) := by
    have hh := congrArg (fun x : ℝ => x * ((D : ℝ) * M))
      (gaussianDyadicRowBound_normalized hξ hD hM)
    rw [div_mul_cancel₀ _ (mul_ne_zero hD0.ne' hM0.ne')] at hh
    exact hh.trans (mul_comm _ _)
  refine (norm_gaussianVaughan_dyadic_nonstationary_sq_le hα hξ σ t hA hB hD hM hband U V).trans ?_
  have hh := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hE (Real.exp_pos (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2)).le) hrow0
  refine hh.trans_eq ?_
  rw [hrow]
  unfold gaussianVaughanDyadicEnvelope
  ring

/-- At quadratic scale `ξD²M²=t`, the squared arithmetic saving is
`1/M+2π(1+log(2M))/t`, provided the long factor lies beyond the height. -/
theorem exists_gaussianVaughan_dyadic_height_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ α t : ℝ) (A B D M U V : ℕ),
      0 ≤ σ → 0 ≤ α → 0 < t → 1 ≤ A → 1 ≤ B → 1 ≤ D → 1 ≤ M →
      16 * t ≤ Real.pi * D →
      ‖gaussianVaughanDyadicSum σ α (t / ((D : ℝ) ^ 2 * (M : ℝ) ^ 2)) t A B D M U V‖ ^ 2 ≤
        C * (((D : ℝ) * M * (D : ℝ) ^ (-σ) * (M : ℝ) ^ (-σ)) ^ 2 *
          Real.log (2 * (D : ℝ)) * (1 + invSum (2 * M) ^ 3) *
            Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) *
              (1 / (M : ℝ) + 2 * Real.pi * (1 + Real.log (2 * (M : ℝ))) / t)) := by
  obtain ⟨C, hC, hbound⟩ := exists_gaussianVaughan_dyadic_envelope_bound
  refine ⟨C, hC, ?_⟩
  intro σ α t A B D M U V hσ hα ht hA hB hD hM hband
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hξ : 0 < t / ((D : ℝ) ^ 2 * (M : ℝ) ^ 2) := by positivity
  have hscale : t / ((D : ℝ) ^ 2 * (M : ℝ) ^ 2) * (D : ℝ) ^ 2 * (M : ℝ) ^ 2 = t := by
    field_simp [hD0.ne', hM0.ne']
  have hsmall : 16 * (t / ((D : ℝ) ^ 2 * (M : ℝ) ^ 2)) * D * (M : ℝ) ^ 2 ≤ Real.pi := by
    have he : 16 * (t / ((D : ℝ) ^ 2 * (M : ℝ) ^ 2)) * D * (M : ℝ) ^ 2 = 16 * t / D := by
      field_simp [hD0.ne', hM0.ne']
    rw [he]
    exact (div_le_iff₀ hD0).mpr hband
  have hh := hbound σ α (t / ((D : ℝ) ^ 2 * (M : ℝ) ^ 2)) t A B D M U V
    hσ hα hξ hA hB hD hM hsmall
  simpa only [gaussianVaughanDyadicEnvelope, hscale] using hh

/-- On rectangles at or above the stationary quadratic scale, the actual
type-II norm has a square-root-of-height saving with logarithmic arithmetic losses. -/
theorem exists_gaussianVaughan_dyadic_log_height_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ α ξ t : ℝ) (A B D M U V : ℕ),
      0 ≤ σ → 0 ≤ α → 0 < ξ → 0 < t → 1 ≤ A → 1 ≤ B → 1 ≤ D → 1 ≤ M →
      16 * ξ * D * (M : ℝ) ^ 2 ≤ Real.pi →
      t ≤ 32 * ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2 → t ≤ M →
      ‖gaussianVaughanDyadicSum σ α ξ t A B D M U V‖ ^ 2 ≤
        C * (((D : ℝ) * M * (D : ℝ) ^ (-σ) * (M : ℝ) ^ (-σ)) ^ 2 *
          (1 + Real.log (2 * (D : ℝ))) * (1 + Real.log (2 * (M : ℝ))) ^ 4 *
            Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) / t) := by
  obtain ⟨C, hC, hbound⟩ := exists_gaussianVaughan_dyadic_envelope_bound
  refine ⟨2 * (1 + 64 * Real.pi) * C, by positivity, ?_⟩
  intro σ α ξ t A B D M U V hσ hα hξ ht hA hB hD hM hband hscale htM
  have hlogD : 0 ≤ Real.log (2 * (D : ℝ)) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ 2 * D by omega))
  have hlogM : 0 ≤ Real.log (2 * (M : ℝ)) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ 2 * M by omega))
  have hLM : 1 ≤ 1 + Real.log (2 * (M : ℝ)) := by linarith only [hlogM]
  have hH0 := invSum_nonneg (2 * M)
  have hHle : invSum (2 * M) ≤ 1 + Real.log (2 * (M : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using invSum_le_one_add_log (N := 2 * M) (by omega)
  have hHpow := pow_le_pow_left₀ hH0 hHle 3
  have hLpow : 1 ≤ (1 + Real.log (2 * (M : ℝ))) ^ 3 := by
    simpa using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hLM 3
  have hH : 1 + invSum (2 * M) ^ 3 ≤ 2 * (1 + Real.log (2 * (M : ℝ))) ^ 3 := by
    linarith only [hHpow, hLpow]
  have hrec : 1 / (ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) ≤ 32 / t := by
    apply (div_le_div_iff₀ (by positivity) ht).mpr
    nlinarith only [hscale]
  have hb : 1 / (M : ℝ) + 2 * Real.pi * (1 + Real.log (2 * (M : ℝ))) /
      (ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) ≤
      (1 + 64 * Real.pi) * (1 + Real.log (2 * (M : ℝ))) / t := by
    have hnum : 1 + 64 * Real.pi * (1 + Real.log (2 * (M : ℝ))) ≤
        (1 + 64 * Real.pi) * (1 + Real.log (2 * (M : ℝ))) := by
      nlinarith only [hLM]
    calc
      _ ≤ 1 / t + (2 * Real.pi * (1 + Real.log (2 * (M : ℝ)))) * (32 / t) := by
        apply _root_.add_le_add (div_le_div_of_nonneg_left (by norm_num) ht htM)
        simpa only [div_eq_mul_inv, one_mul] using
          mul_le_mul_of_nonneg_left hrec (by positivity : 0 ≤ 2 * Real.pi * (1 + Real.log (2 * (M : ℝ))))
      _ = (1 + 64 * Real.pi * (1 + Real.log (2 * (M : ℝ)))) / t := by ring
      _ ≤ _ := by
        simpa only [div_eq_mul_inv] using
          mul_le_mul_of_nonneg_right hnum (by positivity : 0 ≤ t⁻¹)
  have hp : Real.log (2 * (D : ℝ)) * (1 + invSum (2 * M) ^ 3) ≤
      (1 + Real.log (2 * (D : ℝ))) * (2 * (1 + Real.log (2 * (M : ℝ))) ^ 3) := by
    apply mul_le_mul (by linarith only) hH <;> positivity
  have hw := mul_le_mul hp hb (by positivity) (by positivity)
  have hweighted := mul_le_mul_of_nonneg_left hw
    (by positivity : 0 ≤ C * ((D : ℝ) * M * (D : ℝ) ^ (-σ) * (M : ℝ) ^ (-σ)) ^ 2 *
      Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2))
  refine (hbound σ α ξ t A B D M U V hσ hα hξ hA hB hD hM hband).trans ?_
  unfold gaussianVaughanDyadicEnvelope
  calc
    _ = (C * ((D : ℝ) * M * (D : ℝ) ^ (-σ) * (M : ℝ) ^ (-σ)) ^ 2 *
        Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2)) *
      (Real.log (2 * (D : ℝ)) * (1 + invSum (2 * M) ^ 3) *
        (1 / (M : ℝ) + 2 * Real.pi * (1 + Real.log (2 * (M : ℝ))) /
          (ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2))) := by ring
    _ ≤ (C * ((D : ℝ) * M * (D : ℝ) ^ (-σ) * (M : ℝ) ^ (-σ)) ^ 2 *
        Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2)) *
      ((1 + Real.log (2 * (D : ℝ))) * (2 * (1 + Real.log (2 * (M : ℝ))) ^ 3) *
        ((1 + 64 * Real.pi) * (1 + Real.log (2 * (M : ℝ))) / t)) := hweighted
    _ = _ := by ring

/-- Every dyadic rectangle containing a quadratic stationary point lies in
the quadratic-scale range of the logarithmic height bound. -/
theorem gaussian_stationary_height_le_dyadic_scale {ξ : ℝ} (hξ : 0 ≤ ξ)
    {D M d m : ℕ} (hd : d ∈ Ico D (2 * D)) (hm : m ∈ Ico M (2 * M)) :
    2 * ξ * ((d * m : ℕ) : ℝ) ^ 2 ≤ 32 * ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2 := by
  have hp : d * m ≤ 4 * D * M := by
    calc
      d * m ≤ (2 * D) * (2 * M) :=
        Nat.mul_le_mul (mem_Ico.mp hd).2.le (mem_Ico.mp hm).2.le
      _ = 4 * D * M := by ring
  have hs : (((d * m : ℕ) : ℝ)) ^ 2 ≤ (4 * (D : ℝ) * M) ^ 2 := by
    exact_mod_cast Nat.pow_le_pow_left hp 2
  have hh := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 2 * ξ)
  nlinarith only [hh]

#print axioms gaussian_stationary_height_le_dyadic_scale
#print axioms exists_gaussianVaughan_dyadic_log_height_saving
#print axioms exists_gaussianVaughan_dyadic_envelope_bound
#print axioms exists_gaussianVaughan_dyadic_height_saving

end GaloisForLFunctions.ExceptionalLayerTheory
