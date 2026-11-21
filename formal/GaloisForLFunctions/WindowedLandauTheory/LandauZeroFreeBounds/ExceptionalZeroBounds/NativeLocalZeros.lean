import GaloisForLFunctions.RHTower.ConductorUniform.DirichletLConductorUniformLogDerivative
import GaloisForLFunctions.WindowedLandauTheory.LandauZeroFreeBounds.NoZeroComplexOf

/-! Restrict the uniform partial fraction to the zeros nearest the evaluation line. -/

open Complex Finset Metric

namespace WindowedLandauTheory.ZeroFreeDirichlet

private theorem zero_multiplicity {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {ρ : ℂ} (hz : χ.LFunction ρ = 0) :
    1 ≤ analyticOrderNatAt χ.LFunction ρ ∧
      (deriv χ.LFunction ρ = 0 → 2 ≤ analyticOrderNatAt χ.LFunction ρ) := by
  have han (s : ℂ) : AnalyticAt ℂ χ.LFunction s :=
    (DirichletCharacter.differentiable_LFunction hχ).analyticAt s
  have htop : analyticOrderAt χ.LFunction ρ ≠ ⊤ := by
    intro h
    have he := (AnalyticOnNhd.analyticOrderAt_eq_top_iff_eq_zero ρ han).1 h
    have htwo : χ.LFunction 2 ≠ 0 := χ.LFunction_ne_zero_of_one_le_re (.inl hχ) (by norm_num)
    exact htwo (congrFun he 2)
  have hcast := Nat.cast_analyticOrderNatAt htop
  constructor
  · rw [Nat.one_le_iff_ne_zero]
    intro hz'
    rw [hz', Nat.cast_zero] at hcast
    exact ((han ρ).analyticOrderAt_ne_zero.mpr hz) hcast.symm
  · intro hder
    have h : ((2 : ℕ) : ℕ∞) ≤ analyticOrderAt χ.LFunction ρ := by
      apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (han ρ)).mpr
      intro i hi
      interval_cases i
      · simpa using hz
      · simpa using hder
    rw [← hcast] at h
    exact_mod_cast h

theorem log_height_shift (q : ℕ) [NeZero q] (t : ℝ) :
    Real.log (q * (|t| + 3)) ≤ 2 * Real.log (q * (|t| + 2)) := by
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast (NeZero.pos q)
  have h : |t| + 3 ≤ (|t| + 2) ^ 2 := by nlinarith only [abs_nonneg t, sq_nonneg |t|]
  have hsq : (q : ℝ) * (|t| + 3) ≤ ((q : ℝ) * (|t| + 2)) ^ 2 := by
    calc (q : ℝ) * (|t| + 3) ≤ q * (|t| + 2) ^ 2 := mul_le_mul_of_nonneg_left h (by positivity)
      _ ≤ q * (q * (|t| + 2) ^ 2) := mul_le_mul_of_nonneg_left
        (le_mul_of_one_le_left (sq_nonneg _) hq) (by positivity)
      _ = _ := by ring
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < q * (|t| + 3)) hsq
  rw [Real.log_pow] at hlog
  simpa using hlog

theorem localZeros : LocalZeros := by
  refine ⟨2 * RHTower.pfConst, ?_⟩
  intro q _ χ hχ t
  obtain ⟨B, hB, _, bound⟩ := RHTower.L_partial_fraction_with_multiplicity_bound hχ t
  let c : ℂ := (11 / 10 : ℂ) + t * I
  let c' : ℂ := 2 + t * I
  classical
  let Z := B.filter (fun ρ => ρ ∈ closedBall c (1 / 5))
  have hB' (ρ : ℂ) : ρ ∈ B ↔ ρ ∈ closedBall c' (22 / 25 * (91 / 50)) ∧ χ.LFunction ρ = 0 := by
    change ρ ∈ (B : Set ℂ) ↔ _
    rw [hB] <;> rfl
  have hc : dist c c' = 9 / 10 := by
    rw [Complex.dist_eq, show c - c' = ((-(9 / 10) : ℝ) : ℂ) by
      simp only [c, c']
      push_cast
      ring, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  have hZ (ρ : ℂ) : ρ ∈ Z ↔ ρ ∈ closedBall c (1 / 5) ∧ χ.LFunction ρ = 0 := by
    simp only [Z, Finset.mem_filter, hB']
    constructor
    · rintro ⟨⟨_, hz⟩, hρ⟩
      exact ⟨hρ, hz⟩
    · rintro ⟨hρ, hz⟩
      refine ⟨⟨?_, hz⟩, hρ⟩
      have hd := dist_triangle ρ c c'
      rw [hc] at hd
      rw [Metric.mem_closedBall] at hρ ⊢
      linarith only [hd, hρ]
  let m := analyticOrderNatAt χ.LFunction
  refine ⟨Z, m, hZ, fun ρ hρ => (zero_multiplicity hχ ((hZ ρ).1 hρ).2).1,
    fun ρ hρ => (zero_multiplicity hχ ((hZ ρ).1 hρ).2).2, ?_⟩
  intro σ hσ hupper
  let s : ℂ := (σ : ℂ) + t * I
  have hdiff : s - c' = ((σ - 2 : ℝ) : ℂ) := by
    simp only [s, c']
    push_cast
    ring
  have hball : s ∈ closedBall c' (3 / 2) := by
    rw [Metric.mem_closedBall, Complex.dist_eq, hdiff, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith only [hσ, hupper]
  have hsre : s.re = σ := by simp [s]
  have hnz := χ.LFunction_ne_zero_of_one_le_re (.inl hχ) (by rw [hsre]; exact hσ.le)
  have hnorm := bound s hball hnz
  have hRe := Complex.re_le_norm (-(logDeriv χ.LFunction s - ∑ ρ ∈ B, (m ρ : ℂ) / (s - ρ)))
  rw [Complex.neg_re, Complex.sub_re, norm_neg] at hRe
  have hsum : (∑ ρ ∈ B, (m ρ : ℂ) / (s - ρ)).re =
      ∑ ρ ∈ B, (m ρ : ℝ) * (1 / (s - ρ)).re := by
    rw [Complex.re_sum]
    refine sum_congr rfl fun ρ _ => ?_
    rw [div_eq_mul_inv, show (m ρ : ℂ) = ((m ρ : ℝ) : ℂ) by norm_cast,
      Complex.re_ofReal_mul, one_div]
  rw [hsum, logDeriv_apply] at hRe
  have hbound := hRe.trans hnorm
  have hcst := mul_le_mul_of_nonneg_left (log_height_shift q t) RHTower.pfConst_pos.le
  have hsub : ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / (s - ρ)).re ≤
      ∑ ρ ∈ B, (m ρ : ℝ) * (1 / (s - ρ)).re :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun ρ hρ _ => by
      have hre := RHTower.re_lt_one_of_LFunction_eq_zero hχ ((hB' ρ).1 hρ).2
      apply mul_nonneg (Nat.cast_nonneg _)
      rw [one_div, Complex.inv_re, Complex.sub_re, hsre]
      exact div_nonneg (sub_nonneg.mpr (hre.le.trans hσ.le)) (Complex.normSq_nonneg _)
  unfold negLD
  rw [Complex.neg_re]
  linarith only [hbound, hcst, hsub]

end WindowedLandauTheory.ZeroFreeDirichlet
