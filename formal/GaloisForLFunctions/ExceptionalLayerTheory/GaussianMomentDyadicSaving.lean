import GaloisForLFunctions.ExceptionalLayerTheory.NonstationaryGaussianTypeII
import GaloisForLFunctions.RHTower.Sieve.TypeIICoefficientEnergy
import GaloisForLFunctions.RHTower.Sieve.GapSums
import GaloisForLFunctions.RHTower.Sieve.TypeIILongSupport

/-!
# First Gaussian moments suppress small-product rectangles

The first damping moment multiplies each term by `ε(dm)²/t`.
Its separated coefficient energies gain the square of the quadratic scale
relative to height. This removes the inverse-scale singularity of the
nonstationary correlation bound while retaining the product cutoff.
-/

open Complex Finset RHTower RHTower.Sieve

noncomputable section
namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem rpow_shift_two {x : ℝ} (hx : 0 < x) (σ : ℝ) :
    x ^ (-(σ - 2)) = x ^ (2 : ℕ) * x ^ (-σ) := by
  rw [show -(σ - 2) = ((2 : ℕ) : ℝ) + (-σ) by push_cast; ring,
    Real.rpow_add hx, Real.rpow_natCast]

/-- The literal first Gaussian moment on a masked Vaughan rectangle. -/
def gaussianVaughanMomentDyadicSum (σ α ξ t : ℝ) (A B D M U V : ℕ) : ℂ :=
  (((α : ℂ) - ξ * I) / t) * gaussianVaughanDyadicSum (σ - 2) α ξ t A B D M U V

/-- The abscissa shift is precisely multiplication of each original term by `εn²/t`. -/
theorem gaussianVaughanMomentDyadicSum_eq (σ α ξ t : ℝ) (A B : ℕ) {D M : ℕ}
    (hD : 1 ≤ D) (hM : 1 ≤ M) (U V : ℕ) :
    gaussianVaughanMomentDyadicSum σ α ξ t A B D M U V =
      ∑ d ∈ Ico D (2 * D), ∑ m ∈ Ico M (2 * M),
        if d * m ∈ Ico A B then
          ((typeIILong U d : ℝ) : ℂ) * ((typeIIShort V m : ℝ) : ℂ) *
            ((((α : ℂ) - ξ * I) / t) * ((d * m : ℕ) : ℂ) ^ 2) *
              gaussianPrimeWeight σ α ξ t (d * m)
        else 0 := by
  unfold gaussianVaughanMomentDyadicSum gaussianVaughanDyadicSum
  simp_rw [mul_sum]
  apply sum_congr rfl
  intro d hd
  apply sum_congr rfl
  intro m hm
  by_cases hcut : d * m ∈ Ico A B
  · rw [if_pos hcut, if_pos hcut]
    have hn : 0 < ((d * m : ℕ) : ℝ) := by
      exact_mod_cast Nat.mul_pos
        (by have := (mem_Ico.mp hd).1; omega : 0 < d)
        (by have := (mem_Ico.mp hm).1; omega : 0 < m)
    rw [gaussianPrimeWeight, gaussianPrimeWeight, rpow_shift_two hn]
    push_cast
    ring
  · rw [if_neg hcut, if_neg hcut, mul_zero]

private theorem dyadic_shifted_energy_le {σ : ℝ} (hσ : 0 ≤ σ) (f : ℕ → ℂ)
    {D : ℕ} (hD : 1 ≤ D) :
    (∑ d ∈ Ico D (2 * D), ‖f d * (((d : ℝ) ^ (-(σ - 2)) : ℝ) : ℂ)‖ ^ 2) ≤
      (16 * (D : ℝ) ^ 4 * ((D : ℝ) ^ (-σ)) ^ 2) *
        ∑ d ∈ Icc 1 (2 * D), ‖f d‖ ^ 2 := by
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  calc
    _ ≤ ∑ d ∈ Ico D (2 * D),
        (16 * (D : ℝ) ^ 4 * ((D : ℝ) ^ (-σ)) ^ 2) * ‖f d‖ ^ 2 := by
      apply sum_le_sum
      intro d hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by have := mem_Ico.mp hd; omega)
      have hr : (d : ℝ) ^ (-σ) ≤ (D : ℝ) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos hD0 (by exact_mod_cast (mem_Ico.mp hd).1) (neg_nonpos.mpr hσ)
      have hsq : (d : ℝ) ^ 2 ≤ 4 * (D : ℝ) ^ 2 := by
        have hh : (d : ℝ) ^ 2 ≤ (2 * (D : ℝ)) ^ 2 := by
          exact_mod_cast Nat.pow_le_pow_left (mem_Ico.mp hd).2.le 2
        nlinarith only [hh]
      have hw : (d : ℝ) ^ (-(σ - 2)) ≤ 4 * (D : ℝ) ^ 2 * (D : ℝ) ^ (-σ) := by
        rw [rpow_shift_two hd0]
        exact mul_le_mul hsq hr (Real.rpow_nonneg (Nat.cast_nonneg d) _) (by positivity)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _), mul_pow]
      calc
        _ ≤ ‖f d‖ ^ 2 * (4 * (D : ℝ) ^ 2 * (D : ℝ) ^ (-σ)) ^ 2 := by gcongr
        _ = _ := by ring
    _ ≤ ∑ d ∈ Icc 1 (2 * D),
        (16 * (D : ℝ) ^ 4 * ((D : ℝ) ^ (-σ)) ^ 2) * ‖f d‖ ^ 2 := by
      apply sum_le_sum_of_subset_of_nonneg
      · intro d hd
        exact mem_Icc.mpr ⟨hD.trans (mem_Ico.mp hd).1, (mem_Ico.mp hd).2.le⟩
      · intro d _ _
        positivity
    _ = _ := (mul_sum _ _ _).symm

/-- Both shifted Vaughan coefficient energies have a uniform arithmetic bound. -/
theorem exists_gaussianVaughan_shifted_dyadic_coefficient_energy :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ : ℝ) (D M U V : ℕ), 0 ≤ σ → 1 ≤ D → 1 ≤ M →
      (∑ d ∈ Ico D (2 * D),
        ‖((typeIILong U d : ℝ) : ℂ) * (((d : ℝ) ^ (-(σ - 2)) : ℝ) : ℂ)‖ ^ 2) *
      (∑ m ∈ Ico M (2 * M),
        ‖((typeIIShort V m : ℝ) : ℂ) * (((m : ℝ) ^ (-(σ - 2)) : ℝ) : ℂ)‖ ^ 2) ≤
        C * (((D : ℝ) * M * (D : ℝ) ^ (-σ) * (M : ℝ) ^ (-σ)) ^ 2 *
          ((D : ℝ) * M) ^ 3 * Real.log (2 * (D : ℝ)) * (1 + invSum (2 * M) ^ 3)) := by
  obtain ⟨C, hC, hlong⟩ := exists_sum_typeIILong_sq_le
  refine ⟨2048 * C, by positivity, ?_⟩
  intro σ D M U V hσ hD hM
  have hlogD : 0 ≤ Real.log (2 * (D : ℝ)) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ 2 * D by omega))
  have hL := hlong U (2 * D) (by omega)
  rw [Ico_add_one_right_eq_Icc] at hL
  have hS := sum_typeIIShort_sq_le V (2 * M)
  have hEa : (∑ d ∈ Ico D (2 * D),
      ‖((typeIILong U d : ℝ) : ℂ) * (((d : ℝ) ^ (-(σ - 2)) : ℝ) : ℂ)‖ ^ 2) ≤
      (16 * (D : ℝ) ^ 4 * ((D : ℝ) ^ (-σ)) ^ 2) *
        (C * (2 * (D : ℝ)) * Real.log (2 * (D : ℝ))) := by
    refine (dyadic_shifted_energy_le hσ (fun d => ((typeIILong U d : ℝ) : ℂ)) hD).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using hL
  have hEb : (∑ m ∈ Ico M (2 * M),
      ‖((typeIIShort V m : ℝ) : ℂ) * (((m : ℝ) ^ (-(σ - 2)) : ℝ) : ℂ)‖ ^ 2) ≤
      (16 * (M : ℝ) ^ 4 * ((M : ℝ) ^ (-σ)) ^ 2) *
        (4 * (M : ℝ) * (1 + invSum (2 * M) ^ 3)) := by
    refine (dyadic_shifted_energy_le hσ (fun m => ((typeIIShort V m : ℝ) : ℂ)) hM).trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have he : 2 * ((2 * M : ℕ) : ℝ) + 2 * (((2 * M : ℕ) : ℝ) * invSum (2 * M) ^ 3) =
        4 * (M : ℝ) * (1 + invSum (2 * M) ^ 3) := by push_cast; ring
    exact hS.trans_eq he
  have hE := mul_le_mul hEa hEb (sum_nonneg fun _ _ => sq_nonneg _) (by positivity)
  exact hE.trans_eq (by ring)

/-- The normalized first moment gains `(θ/t)²` in squared arithmetic energy,
where `θ=ξD²M²`. Both actual Vaughan coefficients are bounded uniformly. -/
theorem exists_gaussianVaughan_moment_dyadic_envelope_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ α ξ t : ℝ) (A B D M U V : ℕ),
      0 ≤ σ → 0 ≤ α → α ≤ ξ → 0 < ξ → 0 < t →
      1 ≤ A → 1 ≤ B → 1 ≤ D → 1 ≤ M →
      16 * ξ * D * (M : ℝ) ^ 2 ≤ Real.pi →
      ‖gaussianVaughanMomentDyadicSum σ α ξ t A B D M U V‖ ^ 2 ≤
        C * (((D : ℝ) * M * (D : ℝ) ^ (-σ) * (M : ℝ) ^ (-σ)) ^ 2 *
          Real.log (2 * (D : ℝ)) * (1 + invSum (2 * M) ^ 3) *
            Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) *
              ((ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2 / t) ^ 2 *
                (1 / (M : ℝ) + 2 * Real.pi * (1 + Real.log (2 * (M : ℝ))) /
                  (ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2)))) := by
  obtain ⟨C, hC, henergy⟩ := exists_gaussianVaughan_shifted_dyadic_coefficient_energy
  refine ⟨4 * C, by positivity, ?_⟩
  intro σ α ξ t A B D M U V hσ hα hαξ hξ ht hA hB hD hM hband
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hlogM : 0 ≤ Real.log (2 * (M : ℝ)) := Real.log_nonneg (by
    exact_mod_cast (show 1 ≤ 2 * M by omega))
  have hE := henergy σ D M U V hσ hD hM
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
  have hε : ‖(α : ℂ) - ξ * I‖ ≤ 2 * ξ := by
    calc
      _ ≤ ‖(α : ℂ)‖ + ‖(ξ : ℂ) * I‖ := norm_sub_le _ _
      _ = α + ξ := by
        rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs,
          Real.norm_eq_abs, abs_of_nonneg hα, abs_of_pos hξ, Complex.norm_I, mul_one]
      _ ≤ _ := by linarith only [hαξ]
  have hεt : ‖((α : ℂ) - ξ * I) / t‖ ^ 2 ≤ (2 * ξ / t) ^ 2 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht]
    gcongr
  have hbase := (norm_gaussianVaughan_dyadic_nonstationary_sq_le hα hξ (σ - 2) t
    hA hB hD hM hband U V).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hE (Real.exp_pos _).le) hrow0)
  unfold gaussianVaughanMomentDyadicSum
  rw [norm_mul, mul_pow]
  refine (mul_le_mul hεt hbase (sq_nonneg _) (by positivity)).trans_eq ?_
  rw [hrow]
  ring

private theorem moment_row_cost_le {θ t M K : ℝ} (hθ : 0 < θ)
    (ht : 0 < t) (hM : 0 < M) (hθM : θ ≤ M) :
    (θ / t) ^ 2 * (1 / M + K / θ) ≤ θ / t ^ 2 * (1 + K) := by
  have hratio : θ / M ≤ 1 := (div_le_one hM).mpr hθM
  calc
    _ = θ / t ^ 2 * (θ / M + K) := by field_simp [hθ.ne', ht.ne', hM.ne']
    _ ≤ _ := mul_le_mul_of_nonneg_left (_root_.add_le_add hratio le_rfl) (by positivity)

/-- Below the stationary scale, the first moment has an extra `θ/t` saving
in squared norm. This covers the small-product range of the first band. -/
theorem exists_gaussianVaughan_moment_small_scale_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ α ξ t : ℝ) (A B D M U V : ℕ),
      0 ≤ σ → 0 ≤ α → α ≤ ξ → 0 < ξ → 0 < t →
      1 ≤ A → 1 ≤ B → 1 ≤ D → 1 ≤ M →
      16 * ξ * D * (M : ℝ) ^ 2 ≤ Real.pi →
      ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2 ≤ t → t ≤ M →
      ‖gaussianVaughanMomentDyadicSum σ α ξ t A B D M U V‖ ^ 2 ≤
        C * (((D : ℝ) * M * (D : ℝ) ^ (-σ) * (M : ℝ) ^ (-σ)) ^ 2 *
          (1 + Real.log (2 * (D : ℝ))) * (1 + Real.log (2 * (M : ℝ))) ^ 4 *
            Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) *
              (ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2 / t ^ 2)) := by
  obtain ⟨C, hC, hb⟩ := exists_gaussianVaughan_moment_dyadic_envelope_bound
  refine ⟨2 * (1 + 2 * Real.pi) * C, by positivity, ?_⟩
  intro σ α ξ t A B D M U V hσ hα hαξ hξ ht hA hB hD hM hband hsmall htM
  have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
  have hM0 : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
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
  have hp : Real.log (2 * (D : ℝ)) * (1 + invSum (2 * M) ^ 3) ≤
      (1 + Real.log (2 * (D : ℝ))) * (2 * (1 + Real.log (2 * (M : ℝ))) ^ 3) := by
    apply mul_le_mul (by linarith only) hH <;> positivity
  have hr := moment_row_cost_le (by positivity : 0 < ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2)
    (K := 2 * Real.pi * (1 + Real.log (2 * (M : ℝ)))) ht hM0 (hsmall.trans htM)
  have hK : 1 + 2 * Real.pi * (1 + Real.log (2 * (M : ℝ))) ≤
      (1 + 2 * Real.pi) * (1 + Real.log (2 * (M : ℝ))) := by
    nlinarith only [hLM]
  have hr' := hr.trans (mul_le_mul_of_nonneg_left hK
    (by positivity : 0 ≤ ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2 / t ^ 2))
  have hw := mul_le_mul hp hr' (by positivity) (by positivity)
  have hw' := mul_le_mul_of_nonneg_left hw
    (by positivity : 0 ≤ C * ((D : ℝ) * M * (D : ℝ) ^ (-σ) * (M : ℝ) ^ (-σ)) ^ 2 *
      Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2))
  refine (hb σ α ξ t A B D M U V hσ hα hαξ hξ ht hA hB hD hM hband).trans ?_
  convert hw' using 1 <;> ring

theorem gaussianVaughanMomentDyadicSum_eq_zero_of_cutoff
    (σ α ξ t : ℝ) (A B D M U V : ℕ) (hM : 1 ≤ M)
    (hcut : 2 * D ≤ U ∨ 2 * M ≤ V) :
    gaussianVaughanMomentDyadicSum σ α ξ t A B D M U V = 0 := by
  unfold gaussianVaughanMomentDyadicSum
  suffices hz : gaussianVaughanDyadicSum (σ - 2) α ξ t A B D M U V = 0 by
    rw [hz, mul_zero]
  unfold gaussianVaughanDyadicSum
  apply sum_eq_zero
  intro d hd
  apply sum_eq_zero
  intro m hm
  by_cases hdm : d * m ∈ Ico A B
  · rw [if_pos hdm]
    rcases hcut with hcut | hcut
    · rw [typeIILong_eq_zero_of_le ((mem_Ico.mp hd).2.le.trans hcut)]
      simp only [Complex.ofReal_zero, zero_mul]
    · have hz : typeIIShort V m = 0 := one_sub_zeta_mul_truncAF_moebius_apply_eq_zero
        (hM.trans (mem_Ico.mp hm).1) ((mem_Ico.mp hm).2.le.trans hcut)
      rw [hz]
      simp only [Complex.ofReal_zero, mul_zero, zero_mul]
  · exact if_neg hdm

/-- Height-sized Vaughan cutoffs make the first-band and short-factor
conditions automatic on every active small-product rectangle. -/
theorem exists_gaussianVaughan_moment_all_small_rectangles_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (σ α ξ t : ℝ) (A B D M U V : ℕ),
      0 ≤ σ → 0 ≤ α → α ≤ ξ → 0 < ξ → 0 < t →
      1 ≤ A → 1 ≤ B → 1 ≤ D → 1 ≤ M →
      32 * t ≤ Real.pi * U → 2 * t ≤ V →
      ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2 ≤ t →
      ‖gaussianVaughanMomentDyadicSum σ α ξ t A B D M U V‖ ^ 2 ≤
        C * (((D : ℝ) * M * (D : ℝ) ^ (-σ) * (M : ℝ) ^ (-σ)) ^ 2 *
          (1 + Real.log (2 * (D : ℝ))) * (1 + Real.log (2 * (M : ℝ))) ^ 4 *
            Real.exp (-2 * α * (D : ℝ) ^ 2 * (M : ℝ) ^ 2) *
              (ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2 / t ^ 2)) := by
  obtain ⟨C, hC, hb⟩ := exists_gaussianVaughan_moment_small_scale_saving
  refine ⟨C, hC, ?_⟩
  intro σ α ξ t A B D M U V hσ hα hαξ hξ ht hA hB hD hM hU hV hsmall
  by_cases hcut : 2 * D ≤ U ∨ 2 * M ≤ V
  · rw [gaussianVaughanMomentDyadicSum_eq_zero_of_cutoff σ α ξ t A B D M U V hM hcut,
      norm_zero, zero_pow (by norm_num : 2 ≠ 0)]
    have hlogD : 0 ≤ Real.log (2 * (D : ℝ)) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ 2 * D by omega))
    positivity
  · have hUD : (U : ℝ) < 2 * D := by
      exact_mod_cast (show U < 2 * D by omega)
    have hVM : (V : ℝ) < 2 * M := by
      exact_mod_cast (show V < 2 * M by omega)
    have hD0 : (0 : ℝ) < D := by exact_mod_cast (show 0 < D by omega)
    have htM : t ≤ M := by linarith only [hV, hVM]
    have htD : 16 * t ≤ Real.pi * D := by
      have hh := mul_lt_mul_of_pos_left hUD Real.pi_pos
      nlinarith only [hU, hh]
    have hband : 16 * ξ * D * (M : ℝ) ^ 2 ≤ Real.pi := by
      have hh := (mul_le_mul_of_nonneg_left hsmall (by norm_num : (0 : ℝ) ≤ 16)).trans htD
      have he : 16 * ξ * D * (M : ℝ) ^ 2 =
          (16 * (ξ * (D : ℝ) ^ 2 * (M : ℝ) ^ 2)) / D := by
        field_simp [hD0.ne']
      rw [he]
      exact (div_le_iff₀ hD0).mpr hh
    exact hb σ α ξ t A B D M U V hσ hα hαξ hξ ht hA hB hD hM hband hsmall htM

#print axioms exists_gaussianVaughan_shifted_dyadic_coefficient_energy
#print axioms exists_gaussianVaughan_moment_all_small_rectangles_bound

#print axioms exists_gaussianVaughan_moment_small_scale_saving

#print axioms gaussianVaughanMomentDyadicSum_eq
#print axioms exists_gaussianVaughan_moment_dyadic_envelope_bound

end GaloisForLFunctions.ExceptionalLayerTheory
