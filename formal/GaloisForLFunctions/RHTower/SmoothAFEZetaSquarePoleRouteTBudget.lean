import GaloisForLFunctions.RHTower.SmoothAFEZetaPoleDecay
import GaloisForLFunctions.RHTower.Sieve.SmoothAFEZetaSquareExactAFE

/-!
# Mean-square budget for the pole term of the zeta-square AFE

In the smoothed approximate functional equation for `ζ(s)^2` at `s = 1/2 + it` with length `N`, the
double pole at `w = 1 - s` contributes
`P_N(t) = (N^(1-s) e^((1-s)^2)/(1-s)) · (log N + 2(1 - s) + 2 Z'(1) - 1/(1 - s))`, where `Z` is the
regularized zeta function. For `t ∈ [N, 2N]` the Gaussian factor `e^(-t^2)` makes the prefactor
`O(√N/N^2)` while the bracket is `O(N)`, so `P_N` is uniformly bounded there and its mean square
over `[N, 2N]` is `O(N) ⊆ O(N^(101/100))`.

## Main results

- `smoothAFEZetaSquarePoleAFESummand`: the pole term `P_N(t)`.
- `smoothAFEZetaSquarePoleAFESummand_eq_exact_confluent_term`: its explicit form.
- `exists_norm_smoothAFEZetaSquarePoleAFESummandBracket_le`: the bracket is at most `D N` for
  `N ≥ 4` and `t ∈ [N, 2N]`.
- `exists_norm_smoothAFEZetaSquarePoleAFESummand_le`: `|P_N(t)| ≤ C` uniformly for `N ≥ 4`,
  `t ∈ [N, 2N]`.
- `exists_integral_normSq_smoothAFEZetaSquarePoleAFESummand_le_routeTBudget`:
  `∫_{[N, 2N]} |P_N(t)|^2 dt ≤ K N^(101/100)` for all `N ≥ 4`.

## Hypotheses

Unconditional; the bounds hold for `N ≥ 4` with absolute constants.
-/

noncomputable section
open Complex Set MeasureTheory
namespace RHTower

/-- Pole term of the zeta-square AFE at `s = 1/2 + it`: the shifted pole residue
`N^(1-s) e^((1-s)^2)/(1-s)` times `log N + 2(1 - s) + 2 Z'(1) - 1/(1 - s)`. -/
def smoothAFEZetaSquarePoleAFESummand (N : ℕ) (t : ℝ) : ℂ :=
  smoothAFEZetaShiftedPoleResidue (linePt t) (N : ℝ) *
    ((Real.log (N : ℝ) : ℂ) + 2 * (1 - linePt t) +
      2 * deriv regularizedRiemannZeta 1 - (1 - linePt t)⁻¹)

/-- Explicit form of the pole term: `(N^(1-s) e^((1-s)^2)/(1-s)) (log N + 2(1-s) + 2 Z'(1) - 1/(1-s))`. -/
theorem smoothAFEZetaSquarePoleAFESummand_eq_exact_confluent_term
    (N : ℕ) (t : ℝ) :
    smoothAFEZetaSquarePoleAFESummand N t =
      (((N : ℂ) ^ (1 - linePt t) *
          Complex.exp ((1 - linePt t) ^ 2) / (1 - linePt t)) *
        ((Real.log (N : ℝ) : ℂ) + 2 * (1 - linePt t) +
          2 * deriv regularizedRiemannZeta 1 - (1 - linePt t)⁻¹)) := by
  rfl

/-- For `t ≥ 1`, `e^(-t^2) ≤ 1/t^2`. -/
theorem exp_neg_sq_le_inv_sq {t : ℝ} (ht : 1 ≤ t) :
    Real.exp (-(t ^ 2)) ≤ 1 / (t ^ 2) := by
  rw [Real.exp_neg]
  have hsq : 0 < t ^ 2 := sq_pos_of_pos (by linarith)
  have he : t ^ 2 ≤ Real.exp (t ^ 2) :=
    (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans
      (Real.add_one_le_exp (t ^ 2))
  simpa [one_div] using (inv_le_inv₀ (Real.exp_pos _) hsq).2 he

theorem norm_one_sub_linePt_le_one_add {t : ℝ} (ht : 0 ≤ t) :
    ‖(1 : ℂ) - linePt t‖ ≤ 1 + t := by
  have hcoord : (1 : ℂ) - linePt t =
      ((1 / 2 : ℝ) : ℂ) - (t : ℂ) * I := by
    unfold linePt
    push_cast
    ring
  rw [hcoord]
  calc
    ‖((1 / 2 : ℝ) : ℂ) - (t : ℂ) * I‖ ≤
        ‖((1 / 2 : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_sub_le _ _
    _ = 1 / 2 + t := by simp [abs_of_nonneg ht]
    _ ≤ 1 + t := by linarith

theorem norm_inv_one_sub_linePt_le_one {t : ℝ} (ht : 1 ≤ t) :
    ‖((1 : ℂ) - linePt t)⁻¹‖ ≤ 1 := by
  rw [norm_inv]
  have htden : t ≤ ‖(1 : ℂ) - linePt t‖ := by
    simpa [abs_of_nonneg (by linarith : 0 ≤ t)] using
      norm_one_sub_linePt_ge_abs t
  have hden : 1 ≤ ‖(1 : ℂ) - linePt t‖ := ht.trans htden
  exact (inv_le_one₀ (zero_lt_one.trans_le hden)).2 hden

/-- There is `D ≥ 0` such that for `N ≥ 4` and `t ∈ [N, 2N]` the bracket
`log N + 2(1 - s) + 2 Z'(1) - 1/(1 - s)` has norm at most `D N`. -/
theorem exists_norm_smoothAFEZetaSquarePoleAFESummandBracket_le :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {N : ℕ} {t : ℝ}, 4 ≤ N →
      (N : ℝ) ≤ t → t ≤ 2 * (N : ℝ) →
      ‖(Real.log (N : ℝ) : ℂ) + 2 * (1 - linePt t) +
        2 * deriv regularizedRiemannZeta 1 - (1 - linePt t)⁻¹‖ ≤
          D * (N : ℝ) := by
  let E : ℝ := ‖deriv regularizedRiemannZeta 1‖
  let D : ℝ := 6 + 2 * E
  have hE : 0 ≤ E := norm_nonneg _
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro N t hN htN ht2N
  have hNR : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have ht1 : 1 ≤ t := by linarith
  have hlog0 : 0 ≤ Real.log (N : ℝ) :=
    Real.log_nonneg (by linarith)
  have hlog : |Real.log (N : ℝ)| ≤ (N : ℝ) := by
    rw [abs_of_nonneg hlog0]
    exact Real.log_le_self (by linarith)
  have hone := norm_one_sub_linePt_le_one_add (show 0 ≤ t by linarith)
  have hinv := norm_inv_one_sub_linePt_le_one ht1
  calc
    ‖(Real.log (N : ℝ) : ℂ) + 2 * (1 - linePt t) +
        2 * deriv regularizedRiemannZeta 1 - (1 - linePt t)⁻¹‖ ≤
      ‖(Real.log (N : ℝ) : ℂ)‖ + ‖2 * (1 - linePt t)‖ +
        ‖2 * deriv regularizedRiemannZeta 1‖ + ‖(1 - linePt t)⁻¹‖ := by
      calc
        _ ≤ ‖(Real.log (N : ℝ) : ℂ) + 2 * (1 - linePt t) +
            2 * deriv regularizedRiemannZeta 1‖ + ‖(1 - linePt t)⁻¹‖ :=
          norm_sub_le _ _
        _ ≤ (‖(Real.log (N : ℝ) : ℂ) + 2 * (1 - linePt t)‖ +
            ‖2 * deriv regularizedRiemannZeta 1‖) + ‖(1 - linePt t)⁻¹‖ := by
          gcongr
          exact norm_add_le _ _
        _ ≤ (‖(Real.log (N : ℝ) : ℂ)‖ + ‖2 * (1 - linePt t)‖ +
            ‖2 * deriv regularizedRiemannZeta 1‖) + ‖(1 - linePt t)⁻¹‖ := by
          gcongr
          exact norm_add_le _ _
    _ = |Real.log (N : ℝ)| + 2 * ‖1 - linePt t‖ + 2 * E +
        ‖(1 - linePt t)⁻¹‖ := by
      dsimp only [E]
      rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_mul]
      norm_num
    _ ≤ (N : ℝ) + 2 * (1 + t) + 2 * E + 1 := by gcongr
    _ ≤ (N : ℝ) + 2 * (1 + 2 * (N : ℝ)) + 2 * E + 1 := by gcongr
    _ ≤ D * (N : ℝ) := by
      dsimp only [D]
      nlinarith [mul_le_mul_of_nonneg_left hNR hE]

/-- There is `C ≥ 0` with `|P_N(t)| ≤ C` for all `N ≥ 4` and `t ∈ [N, 2N]`. -/
theorem exists_norm_smoothAFEZetaSquarePoleAFESummand_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ} {t : ℝ}, 4 ≤ N →
      (N : ℝ) ≤ t → t ≤ 2 * (N : ℝ) → ‖smoothAFEZetaSquarePoleAFESummand N t‖ ≤ C := by
  obtain ⟨D, hD, hbracket⟩ := exists_norm_smoothAFEZetaSquarePoleAFESummandBracket_le
  let C : ℝ := Real.exp (1 / 4) * D
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N t hN htN ht2N
  have hNR : (4 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have ht1 : 1 ≤ t := by linarith
  have htpos : 0 < t := by linarith
  have htsq : (N : ℝ) ^ 2 ≤ t ^ 2 := by nlinarith
  have hinv : 1 / (t ^ 2) ≤ 1 / ((N : ℝ) ^ 2) :=
    one_div_le_one_div_of_le (sq_pos_of_pos hNpos) htsq
  have hexp : Real.exp (-(t ^ 2)) ≤ 1 / ((N : ℝ) ^ 2) :=
    (exp_neg_sq_le_inv_sq ht1).trans hinv
  have hres0 := norm_smoothAFEZetaShiftedPoleResidue_line_le
    (x := (N : ℝ)) (τ := t) hNpos
    (by simpa [abs_of_nonneg htpos.le] using ht1)
  have hres :
      ‖smoothAFEZetaShiftedPoleResidue (linePt t) (N : ℝ)‖ ≤
        Real.sqrt (N : ℝ) * Real.exp (1 / 4) /
          ((N : ℝ) ^ 2) := by
    calc
      ‖smoothAFEZetaShiftedPoleResidue (linePt t) (N : ℝ)‖ ≤
          Real.sqrt (N : ℝ) * Real.exp (1 / 4) *
            Real.exp (-(t ^ 2)) := hres0
      _ ≤ Real.sqrt (N : ℝ) * Real.exp (1 / 4) *
            (1 / ((N : ℝ) ^ 2)) := by gcongr
      _ = Real.sqrt (N : ℝ) * Real.exp (1 / 4) /
            ((N : ℝ) ^ 2) := by ring
  have hsqrt : Real.sqrt (N : ℝ) ≤ (N : ℝ) := by
    rw [Real.sqrt_le_iff]
    constructor
    · exact hNpos.le
    · nlinarith
  rw [smoothAFEZetaSquarePoleAFESummand, norm_mul]
  calc
    ‖smoothAFEZetaShiftedPoleResidue (linePt t) (N : ℝ)‖ *
        ‖(Real.log (N : ℝ) : ℂ) + 2 * (1 - linePt t) +
          2 * deriv regularizedRiemannZeta 1 - (1 - linePt t)⁻¹‖ ≤
      (Real.sqrt (N : ℝ) * Real.exp (1 / 4) / ((N : ℝ) ^ 2)) *
        (D * (N : ℝ)) := by
      exact mul_le_mul hres (hbracket hN htN ht2N) (norm_nonneg _) (by positivity)
    _ = (Real.exp (1 / 4) * D) *
        (Real.sqrt (N : ℝ) / (N : ℝ)) := by
      field_simp [hNpos.ne']
    _ ≤ (Real.exp (1 / 4) * D) * 1 := by
      gcongr
      exact (div_le_one hNpos).2 hsqrt
    _ = C := by simp [C]

/-- For `N > 0`, the pole term `t ↦ P_N(t)` is continuous. -/
theorem continuous_smoothAFEZetaSquarePoleAFESummand {N : ℕ} (hN : 0 < N) :
    Continuous (smoothAFEZetaSquarePoleAFESummand N) := by
  unfold smoothAFEZetaSquarePoleAFESummand smoothAFEZetaShiftedPoleResidue
  have hline : Continuous fun t : ℝ => linePt t := by
    unfold linePt
    fun_prop
  have hshift : Continuous fun t : ℝ => (1 : ℂ) - linePt t :=
    continuous_const.sub hline
  have hden : ∀ t : ℝ, (1 : ℂ) - linePt t ≠ 0 := by
    intro t hzero
    have hre := congrArg Complex.re hzero
    simp [linePt] at hre
    norm_num at hre
  have hbase : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
  have hpow : Continuous fun t : ℝ => (N : ℂ) ^ (1 - linePt t) :=
    hshift.const_cpow (Or.inl hbase)
  have hexp : Continuous fun t : ℝ => Complex.exp ((1 - linePt t) ^ 2) :=
    (hshift.pow 2).cexp
  have hres : Continuous fun t : ℝ =>
      (N : ℂ) ^ (1 - linePt t) * Complex.exp ((1 - linePt t) ^ 2) /
        (1 - linePt t) :=
    (hpow.mul hexp).div hshift hden
  have hinv : Continuous fun t : ℝ => ((1 : ℂ) - linePt t)⁻¹ :=
    hshift.inv₀ hden
  have hbracket : Continuous fun t : ℝ =>
      (Real.log (N : ℝ) : ℂ) + 2 * (1 - linePt t) +
        2 * deriv regularizedRiemannZeta 1 - (1 - linePt t)⁻¹ := by
    fun_prop
  exact hres.mul hbracket

/-- There is `K ≥ 0` such that `∫_{[N, 2N]} |P_N(t)|^2 dt ≤ K N^(101/100)` for every `N ≥ 4`. -/
theorem exists_integral_normSq_smoothAFEZetaSquarePoleAFESummand_le_routeTBudget :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {N : ℕ}, 4 ≤ N →
      (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ), ‖smoothAFEZetaSquarePoleAFESummand N t‖ ^ 2) ≤
        K * (N : ℝ) ^ (101 / 100 : ℝ) := by
  obtain ⟨C, hC, hpoint⟩ := exists_norm_smoothAFEZetaSquarePoleAFESummand_le
  let K : ℝ := C ^ 2
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro N hN
  have hNpos : 0 < N := by omega
  have hNRpos : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hNR1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hfun : IntegrableOn (fun t : ℝ => ‖smoothAFEZetaSquarePoleAFESummand N t‖ ^ 2)
      (Set.Icc (N : ℝ) (2 * N : ℝ)) :=
    ((continuous_smoothAFEZetaSquarePoleAFESummand hNpos).norm.pow 2).integrableOn_Icc
  have hconst : IntegrableOn (fun _ : ℝ => C ^ 2)
      (Set.Icc (N : ℝ) (2 * N : ℝ)) :=
    integrableOn_const isCompact_Icc.measure_ne_top
  have hmono := setIntegral_mono_on hfun hconst measurableSet_Icc
    (fun t ht => by
      have hp := hpoint hN ht.1 (by simpa using ht.2)
      exact pow_le_pow_left₀ (norm_nonneg _) hp 2)
  have hrpow : (N : ℝ) ≤ (N : ℝ) ^ (101 / 100 : ℝ) := by
    calc
      (N : ℝ) = (N : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ (N : ℝ) ^ (101 / 100 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hNR1 (by norm_num)
  calc
    (∫ t in Set.Icc (N : ℝ) (2 * N : ℝ), ‖smoothAFEZetaSquarePoleAFESummand N t‖ ^ 2) ≤
        ∫ _t in Set.Icc (N : ℝ) (2 * N : ℝ), C ^ 2 := hmono
    _ = C ^ 2 * (N : ℝ) := by
      rw [MeasureTheory.setIntegral_const,
        Real.volume_real_Icc_of_le (by linarith : (N : ℝ) ≤ 2 * N)]
      simp only [smul_eq_mul]
      ring
    _ ≤ C ^ 2 * (N : ℝ) ^ (101 / 100 : ℝ) := by gcongr
    _ = K * (N : ℝ) ^ (101 / 100 : ℝ) := by rfl

end RHTower
