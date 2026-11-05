import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheWindowIndexCountsTheJumpMultiples
import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.TheTwistedHorizonLayerIsPositive
import GaloisForLFunctions.HTGeometry.PositiveDefiniteMatrixLimit

/-!
# Mass of joint periodic windows

Different periodic twists share a common period. Their spatially varying
linear combinations retain the full residue-averaged mass Gram matrix.
-/

noncomputable section
open Finset Filter Topology MeasureTheory Zeta23 Matrix
open scoped ComplexConjugate ComplexOrder

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri HTGeometry

/-- A mean-zero twist remains mean-zero over every positive multiple of its period. -/
theorem MeanZeroTwist.of_dvd {χ : ℕ → ℝ} {m M : ℕ} (hχ : MeanZeroTwist χ m)
    (hM : 0 < M) (hm : m ∣ M) : MeanZeroTwist χ M := by
  obtain ⟨q, rfl⟩ := hm
  refine ⟨hM, fun n => ?_, ?_⟩
  · simpa only [Nat.mul_comm] using hχ.apply_add_mul n q
  · simpa only [Nat.mul_comm, Nat.add_zero, sum_range_zero] using sum_range_mul_add hχ q 0

/-- Subtracting the period mean gives a mean-zero periodic twist. -/
theorem meanZeroTwist_sub_periodMean {ψ : ℕ → ℝ} {M : ℕ} (hM : 0 < M)
    (hper : ∀ n, ψ (n + M) = ψ n) :
    MeanZeroTwist (fun n => ψ n - (∑ r ∈ range M, ψ r) / M) M := by
  refine ⟨hM, fun n => by rw [hper], ?_⟩
  rw [sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
  have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast hM.ne'
  field_simp
  ring

private theorem tendsto_sum_horizonWeights_mul {g h : ℝ → ℝ} {A : ℝ}
    (hg : Continuous g) (hh : Continuous h) (hA : 0 ≤ A)
    (hgs : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0)
    (hhs : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N, horizonWeights g N n * horizonWeights h N n)
      atTop (𝓝 (∫ y, g y * h y)) := by
  have hp := tendsto_sum_horizonWeights_sq (hg.add hh)
    (fun y hy => by simp only [Pi.add_apply, hgs y hy, hhs y hy, add_zero]) hA
  have hm := tendsto_sum_horizonWeights_sq (hg.sub hh)
    (fun y hy => by simp only [Pi.sub_apply, hgs y hy, hhs y hy, sub_zero]) hA
  have hlim := (hp.sub hm).div_const 4
  have hpol := integral_polarize_of_window (A := A) (w := fun _ => (1 : ℝ))
    continuous_const hg hh hgs hhs
  simp only [one_mul] at hpol
  simp only [Pi.add_apply, Pi.sub_apply] at hlim
  rw [hpol] at hlim
  refine hlim.congr fun N => ?_
  rw [← sum_sub_distrib, sum_div]
  refine sum_congr rfl fun n _ => ?_
  dsimp only [horizonWeights, Pi.add_apply, Pi.sub_apply]
  ring

private theorem tendsto_sum_horizonWeights_mul_zeroMean {g h : ℝ → ℝ} {A : ℝ}
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hgs : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0)
    {ψ : ℕ → ℝ} {M : ℕ} (hψ : MeanZeroTwist ψ M) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N,
      horizonWeights g N n * horizonWeights h N n * ψ n) atTop (𝓝 0) := by
  have hz := tendsto_twistedRiemannSum (hg.mul hh) hA
    (fun y hy => by rw [hgs y hy, zero_mul]) hψ (s := 0) le_rfl (by norm_num)
  have hlim := (Complex.continuous_re.tendsto 0).comp hz
  rw [Complex.zero_re] at hlim
  refine hlim.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  simp only [Function.comp_apply]
  rw [twistedRiemannSum_eq _ _ 0 hN]
  have hterm : ∀ r ∈ Icc 1 N,
      horizonProfile (fun y => g y * h y) 0 (r / N) * (ψ r : ℂ) =
        (((N : ℝ) * (horizonWeights g N r * horizonWeights h N r * ψ r) : ℝ) : ℂ) := by
    intro r hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast (mem_Icc.mp hr).1
    rw [horizonProfile_zero _ (div_pos hr0 hN0), ← Complex.ofReal_mul]
    congr 1
    dsimp only [horizonWeights]
    rw [Real.log_div hr0.ne' hN0.ne', div_mul_div_comm, ← pow_two,
      Real.sq_sqrt hr0.le]
    field_simp
  rw [sum_congr rfl hterm, ← Complex.ofReal_sum, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
    Complex.ofReal_re, ← mul_sum, inv_mul_cancel_left₀ hN0.ne']

/-- A periodic modulation of a spatial cross mass converges to its period average. -/
theorem tendsto_periodic_horizon_cross_mass {g h : ℝ → ℝ} {A : ℝ}
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hgs : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0)
    (hhs : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {ψ : ℕ → ℝ} {M : ℕ} (hM : 0 < M) (hper : ∀ n, ψ (n + M) = ψ n) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N,
      horizonWeights g N n * horizonWeights h N n * ψ n) atTop
        (𝓝 ((∑ r ∈ range M, ψ r) / M * ∫ y, g y * h y)) := by
  have hz := tendsto_sum_horizonWeights_mul_zeroMean hg hh hA hgs
    (meanZeroTwist_sub_periodMean hM hper)
  have hm := (tendsto_sum_horizonWeights_mul hg.continuous hh.continuous hA hgs hhs).const_mul
    ((∑ r ∈ range M, ψ r) / M)
  have hlim := hm.add hz
  rw [add_zero] at hlim
  refine hlim.congr fun N => ?_
  rw [mul_sum, ← sum_add_distrib]
  exact sum_congr rfl fun n _ => by ring

/-- The mixed mass of two periodic windows keeps both twists and both spatial profiles. -/
theorem tendsto_sum_jointTwistedWeights_mul {g h : ℝ → ℝ} {A : ℝ}
    (hg : ContDiff ℝ 2 g) (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hgs : ∀ y, y ∉ Set.Icc (-A) 0 → g y = 0)
    (hhs : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0)
    {χ ψ : ℕ → ℝ} {M : ℕ} (hχ : MeanZeroTwist χ M) (hψ : MeanZeroTwist ψ M) :
    Tendsto (fun N : ℕ => ∑ n ∈ Icc 1 N,
      twistedWeights g χ N n * twistedWeights h ψ N n) atTop
        (𝓝 ((∑ r ∈ range M, χ r * ψ r) / M * ∫ y, g y * h y)) := by
  refine (tendsto_periodic_horizon_cross_mass hg hh hA hgs hhs hχ.pos
    (fun n => by rw [hχ.periodic, hψ.periodic])).congr fun N => ?_
  exact sum_congr rfl fun n _ => by dsimp only [twistedWeights]; ring

variable {d : ℕ}

/-- The residue-averaged mass matrix of a joint family. -/
def jointPeriodicMassGram (g : Fin d → ℝ → ℝ) (χ : Fin d → ℕ → ℝ) (M : ℕ) :
    Matrix (Fin d) (Fin d) ℝ :=
  fun i j => (∑ r ∈ range M, ∫ y, (g i y * χ i r) * (g j y * χ j r)) / M

/-- Joint independence is measured on the spatial window and the common residue set together. -/
def jointPeriodicFeature (g : Fin d → ℝ → ℝ) (χ : Fin d → ℕ → ℝ) (M : ℕ)
    (i : Fin d) (p : ℝ × Fin M) : ℝ := g i p.1 * χ i p.2

private theorem jointPeriodicMassGram_apply (g : Fin d → ℝ → ℝ)
    (χ : Fin d → ℕ → ℝ) (M : ℕ) (i j : Fin d) :
    jointPeriodicMassGram g χ M i j =
      (∑ r ∈ range M, χ i r * χ j r) / M * ∫ y, g i y * g j y := by
  change (∑ r ∈ range M, ∫ y, (g i y * χ i r) * (g j y * χ j r)) / M = _
  have hentry (r : ℕ) : (∫ y, (g i y * χ i r) * (g j y * χ j r)) =
      (χ i r * χ j r) * ∫ y, g i y * g j y := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun y => by ring)
  simp only [hentry, ← sum_mul]
  ring

private theorem real_window_gram_quadratic {A : ℝ} {H : Fin d → ℝ → ℝ}
    (hH : ∀ i, Continuous (H i))
    (hHs : ∀ i y, y ∉ Set.Icc (-A) 0 → H i y = 0) (x : Fin d → ℝ) :
    x ⬝ᵥ (fun i j => ∫ y, H i y * H j y) *ᵥ x =
      ∫ y, (∑ i, x i * H i y) ^ 2 := by
  have h := hermQuad_weightGram_eq (A := A) (w := fun _ => (1 : ℝ))
    continuous_const hH hHs (fun i => (x i : ℂ))
  simp only [one_mul] at h
  have hleft : hermQuad (fun i j => ((∫ y, H i y * H j y : ℝ) : ℂ))
      (fun i => (x i : ℂ)) = x ⬝ᵥ (fun i j => ∫ y, H i y * H j y) *ᵥ x := by
    simp only [hermQuad, dotProduct, mulVec, Pi.star_apply, Complex.star_def,
      Complex.conj_ofReal, ← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.ofReal_re]
  rw [hleft] at h
  refine h.trans (integral_congr_ae (Eventually.of_forall fun y => ?_))
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_sum, Complex.normSq_ofReal, sq]

/-- The mass form is the mean of the squared joint combinations. -/
theorem jointPeriodicMassGram_quadratic {A : ℝ} {g : Fin d → ℝ → ℝ}
    (hg : ∀ i, Continuous (g i))
    (hgs : ∀ i y, y ∉ Set.Icc (-A) 0 → g i y = 0)
    (χ : Fin d → ℕ → ℝ) (M : ℕ) (x : Fin d → ℝ) :
    x ⬝ᵥ jointPeriodicMassGram g χ M *ᵥ x =
      (∑ r ∈ range M, ∫ y, (∑ i, x i * (g i y * χ i r)) ^ 2) / M := by
  have hsum : x ⬝ᵥ jointPeriodicMassGram g χ M *ᵥ x =
      (∑ r ∈ range M, x ⬝ᵥ (fun i j => ∫ y,
        (g i y * χ i r) * (g j y * χ j r)) *ᵥ x) / M := by
    simp only [jointPeriodicMassGram, dotProduct, mulVec, mul_sum, sum_mul,
      sum_div, ← mul_div_assoc, div_mul_eq_mul_div]
    conv_lhs =>
      arg 2
      ext i
      rw [sum_comm]
    rw [sum_comm]
  rw [hsum]
  congr 1
  exact sum_congr rfl fun r _ => real_window_gram_quadratic
    (fun i => (hg i).mul_const _) (fun i y hy => by rw [hgs i y hy, zero_mul]) x

/-- Joint independence gives a strictly positive mass matrix, even for coupled twists. -/
theorem jointPeriodicMassGram_posDef {A : ℝ} {g : Fin d → ℝ → ℝ}
    (hg : ∀ i, Continuous (g i))
    (hgs : ∀ i y, y ∉ Set.Icc (-A) 0 → g i y = 0)
    (χ : Fin d → ℕ → ℝ) {M : ℕ} (hM : 0 < M)
    (hlin : LinearIndependent ℝ (jointPeriodicFeature g χ M)) :
    (jointPeriodicMassGram g χ M).PosDef := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨?_, fun x hx => ?_⟩
  · ext i j
    simp only [conjTranspose_apply, star_trivial, jointPeriodicMassGram_apply]
    rw [show (∑ r ∈ range M, χ j r * χ i r) = ∑ r ∈ range M, χ i r * χ j r from
      sum_congr rfl fun r _ => mul_comm _ _]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun y => mul_comm _ _)
  · rw [star_trivial, jointPeriodicMassGram_quadratic hg hgs]
    have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
    apply div_pos _ hM0
    obtain ⟨y, r, hr⟩ : ∃ y : ℝ, ∃ r : Fin M,
        ∑ i, x i * (g i y * χ i r) ≠ 0 := by
      by_contra hn
      push Not at hn
      apply hx
      have hzero : ∑ i, x i • jointPeriodicFeature g χ M i = 0 := by
        funext p
        simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
          jointPeriodicFeature] using hn p.1 p.2
      exact funext ((Fintype.linearIndependent_iff.mp hlin) x hzero)
    have hcont : Continuous (fun y => (∑ i, x i * (g i y * χ i r)) ^ 2) :=
      (continuous_finsetSum _ fun i _ => continuous_const.mul ((hg i).mul_const _)).pow 2
    have hsupp : HasCompactSupport (fun y => (∑ i, x i * (g i y * χ i r)) ^ 2) :=
      hasCompactSupport_of_window (A := A) fun y hy => by
        simp only [hgs _ y hy, zero_mul, mul_zero, sum_const_zero, zero_pow two_ne_zero]
    have hpos := hcont.integral_pos_of_hasCompactSupport_nonneg_nonzero (μ := volume) hsupp
      (fun _ => sq_nonneg _) (x := y) (pow_ne_zero 2 hr)
    exact hpos.trans_le (single_le_sum
      (f := fun r : ℕ => ∫ y : ℝ, (∑ i, x i * (g i y * χ i r)) ^ 2)
      (fun r _ => integral_nonneg fun y => sq_nonneg _) (mem_range.mpr r.isLt))

private def jointDiscreteMassGram (g : Fin d → ℝ → ℝ) (χ : Fin d → ℕ → ℝ)
    (N : ℕ) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => ∑ n ∈ Icc 1 N, twistedWeights (g i) (χ i) N n * twistedWeights (g j) (χ j) N n

private theorem jointDiscreteMassGram_quadratic (g : Fin d → ℝ → ℝ)
    (χ : Fin d → ℕ → ℝ) (N : ℕ) (x : Fin d → ℝ) :
    x ⬝ᵥ jointDiscreteMassGram g χ N *ᵥ x =
      ∑ n ∈ Icc 1 N, (∑ i, x i * twistedWeights (g i) (χ i) N n) ^ 2 := by
  simp only [jointDiscreteMassGram, dotProduct, mulVec, mul_sum, sum_mul, sq]
  conv_lhs =>
    arg 2
    ext i
    rw [sum_comm]
  rw [sum_comm]
  apply sum_congr rfl
  intro n _
  exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by ring

/-- Joint periodic mass is uniformly coercive on every finite independent family. -/
theorem eventually_jointPeriodic_mass_coercive {A : ℝ} {g : Fin d → ℝ → ℝ}
    (hg : ∀ i, ContDiff ℝ 2 (g i)) (hA : 0 ≤ A)
    (hgs : ∀ i y, y ∉ Set.Icc (-A) 0 → g i y = 0)
    {χ : Fin d → ℕ → ℝ} {M : ℕ} (hM : 0 < M)
    (hχ : ∀ i, MeanZeroTwist (χ i) M)
    (hlin : LinearIndependent ℝ (jointPeriodicFeature g χ M)) :
    ∃ μ : ℝ, 0 < μ ∧ ∀ᶠ N : ℕ in atTop, ∀ x : Fin d → ℝ,
      μ * ∑ i, x i ^ 2 ≤
        ∑ n ∈ Icc 1 N, (∑ i, x i * twistedWeights (g i) (χ i) N n) ^ 2 := by
  obtain ⟨μ, hμ, hcoer⟩ := posDef_coercive
    (jointPeriodicMassGram_posDef (fun i => (hg i).continuous) hgs χ hM hlin)
  let ε : ℝ := μ / (2 * (d + 1))
  have hε : 0 < ε := div_pos hμ (by positivity)
  have hlim (i j : Fin d) : Tendsto (fun N =>
      jointDiscreteMassGram g χ N i j - jointPeriodicMassGram g χ M i j)
      atTop (𝓝 0) := by
    have h := (tendsto_sum_jointTwistedWeights_mul (hg i) (hg j) hA (hgs i) (hgs j)
      (hχ i) (hχ j)).sub_const (jointPeriodicMassGram g χ M i j)
    simpa only [jointDiscreteMassGram, jointPeriodicMassGram_apply, sub_self] using h
  have hev : ∀ᶠ N : ℕ in atTop, ∀ i j,
      |jointDiscreteMassGram g χ N i j - jointPeriodicMassGram g χ M i j| ≤ ε := by
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro j
    have h := (hlim i j).abs
    simp only [abs_zero] at h
    exact h.eventually (ge_mem_nhds hε)
  refine ⟨μ / 2, half_pos hμ, hev.mono fun N hN x => ?_⟩
  have hb := abs_dotProduct_mulVec_le
    (jointDiscreteMassGram g χ N - jointPeriodicMassGram g χ M) hε.le hN x
  have hsplit : x ⬝ᵥ (jointDiscreteMassGram g χ N - jointPeriodicMassGram g χ M) *ᵥ x =
      x ⬝ᵥ jointDiscreteMassGram g χ N *ᵥ x - x ⬝ᵥ jointPeriodicMassGram g χ M *ᵥ x := by
    rw [Matrix.sub_mulVec, dotProduct_sub]
  have hδε : (d : ℝ) * ε ≤ μ / 2 := by
    dsimp only [ε]
    rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith only [hμ]
  have hxx : 0 ≤ x ⬝ᵥ x := by
    rw [dotProduct]
    exact sum_nonneg fun i _ => mul_self_nonneg _
  have hc := hcoer x
  have he := mul_le_mul_of_nonneg_right hδε hxx
  have hh := (abs_le.mp hb).1
  rw [hsplit] at hh
  rw [← jointDiscreteMassGram_quadratic]
  have hnorm : ∑ i, x i ^ 2 = x ⬝ᵥ x := by simp only [dotProduct, sq]
  rw [hnorm]
  linarith only [hc, he, hh]

#print axioms MeanZeroTwist.of_dvd
#print axioms tendsto_sum_jointTwistedWeights_mul
#print axioms jointPeriodicMassGram_posDef
#print axioms eventually_jointPeriodic_mass_coercive

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
