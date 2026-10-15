import GaloisForLFunctions.RHTower.WeilConeUniquenessUnconditional
import GaloisForLFunctions.RHTower.EvenTestLaplacePositivity

/-!
# The twisted-arc null function is positive on an imaginary segment

For a finite measure `ν` on the modular bottom arc `u ∈ [−½, ½]` let
`m_j = ∫ √(y(u)/2) u^{2j} dν` and `w_j = 4√2 · 4^j m_j / (2j)!` (`arcGammaWeight`).  The
shifted-Gamma tests `F_j` have `F̂_j = Ξ Q_j` with `Q_j(τ) = ∏_{k<j}(k + ¼ + iτ/2)`, so the weighted
autocorrelation `G = Σ_j w_j F_j ⋆ F̃_j` has, at the imaginary point `iy`,

`Ĝ(iy) = Ξ(iy)² · Σ_j w_j p_j(y)`,   `p_j(y) = ∏_{k<j} (k + ¼ − y/2)(k + ¼ + y/2)`.

For `j ≥ 1` the factor `k = 0` makes `p_j(y) < 0` on `½ < y < 5/2`, so each such `F_j` has negative
Laplace pairing there (`laplacePairing_xiShiftedGammaTest_neg` for `½ < y < ¾`).  The weighted sum
is nevertheless positive on the whole segment `|y| ≤ 3/2`.

**Theorem** (`sqrt_two_mul_le_tsum_arcGammaWeight_mul_prod`).  For `|y| ≤ 3/2`,
`Σ_j w_j p_j(y) ≥ √2 m_0`.

Proof.  For `|y| ≤ 3/2` every factor satisfies `|k + ¼ ± y/2| ≤ k + 1`, so `|p_j(y)| ≤ (j!)²`.  On
the arc `u² ≤ ¼`, so `m_j ≤ 4^{−j} m_0`.  Hence `|w_j p_j(y)| ≤ 4√2 m_0 (j!)²/(2j)!`.  Also
`(j!)²/(2j)! ≤ (3/2)(1/3)^j`, since consecutive ratios `(j+1)/(2(2j+1))` are `≤ 1/3` for `j ≥ 1`.
The term `j = 0` is `4√2 m_0`, and the remaining terms total at most `4√2 m_0 · ¾`.

**Corollary** (`tsum_arcGammaWeight_mul_laplacePairing_pos`).  With `Ξ(iy) > 0` for real `y`
(`thetaSourceLaplace_pos`), the weighted Laplace pairing of the shifted-Gamma family at `iy`,
`|y| < 3/4`, is positive for every probability measure on the arc.  In particular this holds for the
blind twisted-arc measure behind `eq_vonMangoldt_of_weilPositiveFull`.

Reading.  On the real line this null function is positive definite.  On the imaginary axis it is
positive for `|y| ≤ 3/2`, a range that contains the pole `y = ½`.  Its negative Legendre moments
(`y = 2m + ½`, `m ≥ 1`) lie beyond `3/2`.
-/

open Complex MeasureTheory Set Finset Zeta23
open scoped Nat ComplexConjugate

noncomputable section

namespace RHTower.WeilSpectral

/-- `(j!)²/(2j)! ≤ (3/2)(1/3)^j`. -/
theorem factorial_sq_div_factorial_two_mul_le (j : ℕ) :
    (j ! : ℝ) ^ 2 / ((2 * j)! : ℝ) ≤ 3 / 2 * (1 / 3 : ℝ) ^ j := by
  induction j with
  | zero => norm_num
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · norm_num [Nat.factorial]
    have hpos : (0 : ℝ) < ((2 * n)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have e : ((n + 1)! : ℝ) ^ 2 / ((2 * (n + 1))! : ℝ) =
        ((n : ℝ) + 1) ^ 2 / ((2 * n + 2) * (2 * n + 1)) * ((n ! : ℝ) ^ 2 / ((2 * n)! : ℝ)) := by
      rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Nat.factorial_succ (2 * n + 1),
        Nat.factorial_succ (2 * n), Nat.factorial_succ n]
      push_cast
      field_simp
      ring
    have hr : ((n : ℝ) + 1) ^ 2 / ((2 * n + 2) * (2 * n + 1)) ≤ 1 / 3 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    rw [e, pow_succ]
    calc ((n : ℝ) + 1) ^ 2 / ((2 * n + 2) * (2 * n + 1)) * ((n ! : ℝ) ^ 2 / ((2 * n)! : ℝ))
        ≤ 1 / 3 * (3 / 2 * (1 / 3 : ℝ) ^ n) :=
          mul_le_mul hr ih (by positivity) (by norm_num)
      _ = 3 / 2 * ((1 / 3 : ℝ) ^ n * (1 / 3)) := by ring

/-- The shifted-Gamma Laplace factor `p_j(y) = ∏_{k<j} (k + ¼ − y/2)(k + ¼ + y/2)`. -/
def shiftedGammaLaplaceFactor (j : ℕ) (y : ℝ) : ℝ :=
  ∏ k ∈ range j, (((k : ℝ) + 1 / 4 - y / 2) * ((k : ℝ) + 1 / 4 + y / 2))

theorem abs_shiftedGammaLaplaceFactor_le {y : ℝ} (hy : |y| ≤ 3 / 2) (j : ℕ) :
    |shiftedGammaLaplaceFactor j y| ≤ (j ! : ℝ) ^ 2 := by
  unfold shiftedGammaLaplaceFactor
  rw [abs_prod, ← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod, ← Finset.prod_pow]
  refine Finset.prod_le_prod (fun _ _ => abs_nonneg _) fun k _ => ?_
  obtain ⟨h1, h2⟩ := abs_le.mp hy
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  rw [abs_mul, sq]
  push_cast
  exact mul_le_mul (abs_le.mpr ⟨by linarith, by linarith⟩) (abs_le.mpr ⟨by linarith, by linarith⟩)
    (abs_nonneg _) (by linarith)

theorem shiftedGammaLaplaceFactor_zero (y : ℝ) : shiftedGammaLaplaceFactor 0 y = 1 := by
  simp [shiftedGammaLaplaceFactor]

theorem integrable_sqrt_arcHeight_mul_pow (ν : Measure ArcParam) [IsFiniteMeasure ν] (j : ℕ) :
    Integrable (fun u : ArcParam => (fun _ : ArcParam => (1 : ℝ)) u *
      (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j))) ν := by
  have hc : Continuous fun u : ArcParam =>
      (1 : ℝ) * (Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)) :=
    continuous_const.mul (((continuous_modularArcHeight_param.div_const 2).sqrt).mul
      (continuous_subtype_val.pow _))
  refine (integrable_const (1 : ℝ)).mono' hc.aestronglyMeasurable
    (Filter.Eventually.of_forall fun u => ?_)
  have hu : (u : ℝ) ^ 2 ≤ 1 / 4 := by nlinarith [u.2.1, u.2.2]
  have hu0 : (0 : ℝ) ≤ (u : ℝ) ^ 2 := sq_nonneg _
  rw [Real.norm_eq_abs, one_mul, abs_of_nonneg (mul_nonneg (Real.sqrt_nonneg _)
    (by rw [pow_mul]; exact pow_nonneg hu0 _))]
  calc Real.sqrt (modularArcHeight u / 2) * (u : ℝ) ^ (2 * j)
      ≤ 1 * 1 := by
        refine mul_le_mul (sqrt_modularArcHeight_half_le_one u) ?_
          (by rw [pow_mul]; exact pow_nonneg hu0 _) zero_le_one
        rw [pow_mul]
        exact pow_le_one₀ hu0 (by linarith)
    _ = 1 := one_mul 1

theorem twArcEvenMoment_one_nonneg' (ν : Measure ArcParam) (j : ℕ) :
    0 ≤ twArcEvenMoment ν (fun _ => 1) j := by
  unfold twArcEvenMoment
  refine integral_nonneg fun u => mul_nonneg zero_le_one (mul_nonneg (Real.sqrt_nonneg _) ?_)
  rw [pow_mul]
  exact pow_nonneg (sq_nonneg _) _

/-- On the arc `u² ≤ ¼`, so the even moments decay geometrically. -/
theorem twArcEvenMoment_one_le_mul_zero (ν : Measure ArcParam) [IsFiniteMeasure ν] (j : ℕ) :
    twArcEvenMoment ν (fun _ => 1) j ≤ (1 / 4 : ℝ) ^ j * twArcEvenMoment ν (fun _ => 1) 0 := by
  unfold twArcEvenMoment
  rw [← integral_const_mul]
  refine integral_mono (integrable_sqrt_arcHeight_mul_pow ν j)
    ((integrable_sqrt_arcHeight_mul_pow ν 0).const_mul _) fun u => ?_
  have hu : (u : ℝ) ^ 2 ≤ 1 / 4 := by nlinarith [u.2.1, u.2.2]
  simp only [one_mul, mul_zero, pow_zero, mul_one]
  rw [mul_comm ((1 / 4 : ℝ) ^ j)]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  rw [pow_mul]
  exact pow_le_pow_left₀ (sq_nonneg _) hu j

theorem abs_arcGammaWeight_mul_le (ν : Measure ArcParam) [IsFiniteMeasure ν] {y : ℝ}
    (hy : |y| ≤ 3 / 2) (j : ℕ) :
    |arcGammaWeight (twArcEvenMoment ν (fun _ => 1) j) j * shiftedGammaLaplaceFactor j y| ≤
      4 * Real.sqrt 2 * twArcEvenMoment ν (fun _ => 1) 0 * (3 / 2 * (1 / 3 : ℝ) ^ j) := by
  set m := twArcEvenMoment ν (fun _ => 1)
  have hm0 : 0 ≤ m 0 := twArcEvenMoment_one_nonneg' ν 0
  have hmj : 0 ≤ m j := twArcEvenMoment_one_nonneg' ν j
  have hle : m j ≤ (1 / 4 : ℝ) ^ j * m 0 := twArcEvenMoment_one_le_mul_zero ν j
  have hf : (0 : ℝ) < ((2 * j)! : ℝ) := by exact_mod_cast Nat.factorial_pos _
  have hw0 : 0 ≤ arcGammaWeight (m j) j := by unfold arcGammaWeight; positivity
  rw [abs_mul, abs_of_nonneg hw0]
  calc arcGammaWeight (m j) j * |shiftedGammaLaplaceFactor j y|
      ≤ arcGammaWeight ((1 / 4 : ℝ) ^ j * m 0) j * (j ! : ℝ) ^ 2 := by
        refine mul_le_mul ?_ (abs_shiftedGammaLaplaceFactor_le hy j) (abs_nonneg _)
          (by unfold arcGammaWeight; positivity)
        unfold arcGammaWeight
        gcongr
    _ = 4 * Real.sqrt 2 * m 0 * ((j ! : ℝ) ^ 2 / ((2 * j)! : ℝ)) := by
        have h4 : (4 : ℝ) ^ j * (1 / 4) ^ j = 1 := by rw [← mul_pow]; norm_num
        unfold arcGammaWeight
        calc _ = 4 * Real.sqrt 2 * m 0 * ((4 : ℝ) ^ j * (1 / 4) ^ j) *
              ((j ! : ℝ) ^ 2 / ((2 * j)! : ℝ)) := by ring
          _ = _ := by rw [h4, mul_one]
    _ ≤ 4 * Real.sqrt 2 * m 0 * (3 / 2 * (1 / 3 : ℝ) ^ j) :=
        mul_le_mul_of_nonneg_left (factorial_sq_div_factorial_two_mul_le j) (by positivity)

theorem summable_arcGammaWeight_mul_shiftedGammaLaplaceFactor (ν : Measure ArcParam)
    [IsFiniteMeasure ν] {y : ℝ} (hy : |y| ≤ 3 / 2) :
    Summable fun j =>
      arcGammaWeight (twArcEvenMoment ν (fun _ => 1) j) j * shiftedGammaLaplaceFactor j y := by
  refine Summable.of_norm_bounded
    (((summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 3 : ℝ) < 1)).mul_left
      (3 / 2)).mul_left (4 * Real.sqrt 2 * twArcEvenMoment ν (fun _ => 1) 0)) fun j => ?_
  rw [Real.norm_eq_abs]
  exact abs_arcGammaWeight_mul_le ν hy j

/-- **The weighted shifted-Gamma Laplace factors are positive on `|y| ≤ 3/2`.** -/
theorem sqrt_two_mul_le_tsum_arcGammaWeight_mul_prod (ν : Measure ArcParam) [IsFiniteMeasure ν]
    {y : ℝ} (hy : |y| ≤ 3 / 2) :
    Real.sqrt 2 * twArcEvenMoment ν (fun _ => 1) 0 ≤
      ∑' j, arcGammaWeight (twArcEvenMoment ν (fun _ => 1) j) j *
        shiftedGammaLaplaceFactor j y := by
  set m := twArcEvenMoment ν (fun _ => 1)
  set f : ℕ → ℝ := fun j => arcGammaWeight (m j) j * shiftedGammaLaplaceFactor j y with hf_def
  have hs : Summable f := summable_arcGammaWeight_mul_shiftedGammaLaplaceFactor ν hy
  have hm0 : 0 ≤ m 0 := twArcEvenMoment_one_nonneg' ν 0
  have hgeo : Summable fun j : ℕ => 4 * Real.sqrt 2 * m 0 * (3 / 2 * (1 / 3 : ℝ) ^ (j + 1)) :=
    (((summable_geometric_of_lt_one (by norm_num) (by norm_num : (1 / 3 : ℝ) < 1)).comp_injective
      (add_left_injective 1)).mul_left (3 / 2)).mul_left _
  have htail : -(∑' j : ℕ, 4 * Real.sqrt 2 * m 0 * (3 / 2 * (1 / 3 : ℝ) ^ (j + 1))) ≤
      ∑' j : ℕ, f (j + 1) := by
    rw [← tsum_neg]
    refine Summable.tsum_le_tsum (fun j => ?_) hgeo.neg
      (hs.comp_injective (add_left_injective 1))
    exact neg_le_of_abs_le (abs_arcGammaWeight_mul_le ν hy (j + 1))
  have hval : ∑' j : ℕ, 4 * Real.sqrt 2 * m 0 * (3 / 2 * (1 / 3 : ℝ) ^ (j + 1)) =
      3 * Real.sqrt 2 * m 0 := by
    have e : ∀ j : ℕ, 4 * Real.sqrt 2 * m 0 * (3 / 2 * (1 / 3 : ℝ) ^ (j + 1)) =
        2 * Real.sqrt 2 * m 0 * (1 / 3 : ℝ) ^ j := fun j => by ring
    simp_rw [e]
    rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
    ring
  have h0 : f 0 = 4 * Real.sqrt 2 * m 0 := by
    simp only [hf_def, shiftedGammaLaplaceFactor_zero, mul_one, arcGammaWeight]
    norm_num
  rw [hs.tsum_eq_zero_add, h0]
  linarith

/-- **Positivity for probability measures on the arc.** -/
theorem tsum_arcGammaWeight_mul_prod_pos (μ : ProbabilityMeasure ArcParam) {y : ℝ}
    (hy : |y| ≤ 3 / 2) :
    0 < ∑' j, arcGammaWeight (twArcEvenMoment (μ : Measure ArcParam) (fun _ => 1) j) j *
      shiftedGammaLaplaceFactor j y :=
  lt_of_lt_of_le (mul_pos (by positivity) (twArcEvenMoment_one_zero_pos μ))
    (sqrt_two_mul_le_tsum_arcGammaWeight_mul_prod (μ : Measure ArcParam) hy)

/-- The Laplace pairing of a shifted-Gamma test at `iy` is `Ξ(iy)² p_j(y)`. -/
theorem laplacePairing_xiShiftedGammaTest_eq (j : ℕ) {y : ℝ} (hy : |y| < 3 / 4) :
    paperFT (fun u => (xiShiftedGammaTest j u : ℂ)) (I * y) *
      conj (paperFT (fun u => (xiShiftedGammaTest j u : ℂ)) (conj (I * y))) =
      ((RHTower.thetaSourceLaplace y * RHTower.thetaSourceLaplace (-y) *
        shiftedGammaLaplaceFactor j y : ℝ) : ℂ) := by
  have hc : conj (I * (y : ℂ)) = I * ((-y : ℝ) : ℂ) := by
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]; push_cast; ring
  have him1 : |(I * (y : ℂ)).im| < 3 / 4 := by simpa using hy
  have him2 : |(I * ((-y : ℝ) : ℂ)).im| < 3 / 4 := by simpa [abs_neg] using hy
  rw [hc, paperFT_xiShiftedGammaTest j him1, paperFT_xiShiftedGammaTest j him2]
  unfold xiShiftedGamma
  rw [RHTower.XiC_I_mul, RHTower.XiC_I_mul, RHTower.EvenSector.shiftedGammaPoly_I_mul,
    RHTower.EvenSector.shiftedGammaPoly_I_mul]
  simp only [← Complex.ofReal_mul, Complex.conj_ofReal]
  congr 1
  unfold shiftedGammaLaplaceFactor
  rw [Finset.prod_mul_distrib]
  have e : ∀ k : ℕ, (k : ℝ) + 1 / 4 - -y / 2 = (k : ℝ) + 1 / 4 + y / 2 := fun k => by ring
  simp_rw [e]
  ring

/-- **The blind twisted-arc family has positive Laplace pairing on `|y| < 3/4`.** -/
theorem tsum_arcGammaWeight_mul_laplacePairing_pos (μ : ProbabilityMeasure ArcParam) {y : ℝ}
    (hy : |y| < 3 / 4) :
    0 < ∑' j, arcGammaWeight (twArcEvenMoment (μ : Measure ArcParam) (fun _ => 1) j) j *
      (paperFT (fun u => (xiShiftedGammaTest j u : ℂ)) (I * y) *
        conj (paperFT (fun u => (xiShiftedGammaTest j u : ℂ)) (conj (I * y)))).re := by
  have e : ∀ j, arcGammaWeight (twArcEvenMoment (μ : Measure ArcParam) (fun _ => 1) j) j *
      (paperFT (fun u => (xiShiftedGammaTest j u : ℂ)) (I * y) *
        conj (paperFT (fun u => (xiShiftedGammaTest j u : ℂ)) (conj (I * y)))).re =
      RHTower.thetaSourceLaplace y * RHTower.thetaSourceLaplace (-y) *
        (arcGammaWeight (twArcEvenMoment (μ : Measure ArcParam) (fun _ => 1) j) j *
          shiftedGammaLaplaceFactor j y) := fun j => by
    rw [laplacePairing_xiShiftedGammaTest_eq j hy, Complex.ofReal_re]
    ring
  simp_rw [e]
  rw [tsum_mul_left]
  exact mul_pos (mul_pos (RHTower.thetaSourceLaplace_pos y) (RHTower.thetaSourceLaplace_pos (-y)))
    (tsum_arcGammaWeight_mul_prod_pos μ (by linarith [hy.le]))

end RHTower.WeilSpectral

end
