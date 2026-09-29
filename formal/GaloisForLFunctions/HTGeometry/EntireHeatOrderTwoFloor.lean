import GaloisForLFunctions.HTGeometry.StrelitzCircleBootstrap
import GaloisForLFunctions.HTGeometry.SuperGaussianPlateauEulerJets
import GaloisForLFunctions.HTGeometry.EntireHeatDifferentialOrderFloor

/-!
# Entire-heat anchors satisfy no algebraic differential equation of order at most two

Let `u(t, z) = Σ a_n e^{-4π² n² t} e^{2πinz}` converge at every complex time `t` and every `z`, and
let `h(w) = Σ a_n w^n` be its multiplicative anchor.  Then either `h` is a polynomial, or `h`
satisfies no algebraic differential equation of differential order at most two over `ℂ(w)`.
Consequently a differentially algebraic infinite-spectrum anchor has minimal order at least three.

Entire backward heat evolution makes the coefficients super-Gaussian, so the central index is
sublogarithmic, `log M_h(r) = o((log r)²)`, and the central index has arbitrarily wide plateaus.
At the midpoint of a wide plateau every Taylor term is geometrically separated from the dominant
one.  On that circle `h` is at least half its dominant term, `z h'/h` is within `32q` of the
dominant index, and the second Euler jet is at most `64q`.  For an assumed order-two equation this
circle is clean for the circle bootstrap of the logarithmic-jet relation, which forces `h` to be a
polynomial.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Complex Metric Set Filter Topology Real GaloisForLFunctions

variable {a : ℕ → ℂ}

/-- Entire complex-time heat evolution gives super-Gaussian Taylor coefficients. -/
theorem superGaussianCoeffs_of_entireHeat
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ (2 : ℕ)) * (n : ℂ) ^ (2 : ℕ) * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z))) :
    SuperGaussianCoeffs a := by
  intro A hA
  obtain ⟨M, hM⟩ := EntireHeatHolonomic.exists_superGaussian_bound hheat A hA
  refine ⟨max M 1, lt_of_lt_of_le one_pos (le_max_right _ _), fun n => ?_⟩
  calc ‖a n‖ ≤ M * Real.exp (-A * (n : ℝ) ^ (2 : ℕ)) := hM n
    _ ≤ max M 1 * Real.exp (-(A * (n : ℝ) ^ (2 : ℕ))) := by
        rw [neg_mul]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

/-- **Zero logarithmic type at the quadratic scale.**  An entire-heat anchor satisfies
`log M_h(r) = o((log r)²)`: for every `ε > 0` eventually `|h(z)| ≤ exp(ε (log |z|)²)`. -/
theorem entireHeat_norm_le_exp_mul_log_sq
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ (2 : ℕ)) * (n : ℂ) ^ (2 : ℕ) * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℝ, ∀ z : ℂ, R ≤ ‖z‖ → ‖coeffFun a z‖ ≤ Real.exp (ε * Real.log ‖z‖ ^ 2) := by
  have hSG := superGaussianCoeffs_of_entireHeat hheat
  have ha : EntireCoeffs a := entireCoeffs_of_superGaussian hSG
  obtain ⟨C, hC, hbound⟩ := hSG (1 / ε) (by positivity)
  set K : ℝ := Real.log (2 * C) + ε / 2 * Real.log 2 ^ 2 with hK
  refine ⟨max 1 (Real.exp (Real.sqrt (2 * max K 0 / ε))), fun z hz => ?_⟩
  have hz1 : 1 ≤ ‖z‖ := (le_max_left _ _).trans hz
  have hz0 : 0 < ‖z‖ := by linarith
  set L := Real.log ‖z‖ with hL
  have hL0 : 0 ≤ L := Real.log_nonneg hz1
  have hLbig : 2 * max K 0 / ε ≤ L ^ 2 := by
    have h1 : Real.exp (Real.sqrt (2 * max K 0 / ε)) ≤ ‖z‖ := (le_max_right _ _).trans hz
    have h2 : Real.sqrt (2 * max K 0 / ε) ≤ L := by
      rw [hL, Real.le_log_iff_exp_le hz0]
      exact h1
    have h3 := Real.sq_sqrt (show 0 ≤ 2 * max K 0 / ε by positivity)
    nlinarith [Real.sqrt_nonneg (2 * max K 0 / ε)]
  have hmaj : ‖coeffFun a z‖ ≤ 2 * (C * Real.exp (Real.log (2 * ‖z‖) ^ 2 / (4 * (1 / ε)))) :=
    (norm_coeffFun_le ha hz0).trans ((coeffSum_le_two_mul_maxTerm ha hz0).trans
      (mul_le_mul_of_nonneg_left (maxTerm_le_of_superGaussian (by positivity) hC hbound
        (by positivity)) (by norm_num)))
  have hlog2 : Real.log (2 * ‖z‖) = Real.log 2 + L := by
    rw [Real.log_mul (by norm_num) hz0.ne']
  have hexp : Real.log (2 * ‖z‖) ^ 2 / (4 * (1 / ε)) ≤ ε / 2 * Real.log 2 ^ 2 + ε / 2 * L ^ 2 := by
    rw [hlog2, div_le_iff₀ (by positivity)]
    have : (Real.log 2 - L) ^ 2 ≥ 0 := sq_nonneg _
    field_simp
    nlinarith
  have hpos : 0 < 2 * C := by positivity
  calc ‖coeffFun a z‖ ≤ 2 * (C * Real.exp (Real.log (2 * ‖z‖) ^ 2 / (4 * (1 / ε)))) := hmaj
    _ = Real.exp (Real.log (2 * C) + Real.log (2 * ‖z‖) ^ 2 / (4 * (1 / ε))) := by
        rw [Real.exp_add, Real.exp_log hpos]
        ring
    _ ≤ Real.exp (ε * L ^ 2) := by
        refine Real.exp_le_exp.mpr ?_
        have hKle : K ≤ ε / 2 * L ^ 2 := by
          have := le_max_left K 0
          have h2 : max K 0 ≤ ε / 2 * L ^ 2 := by
            rw [div_le_iff₀ hε] at hLbig
            nlinarith
          linarith
        linarith

/-- **Order two is excluded.**  An infinite-spectrum entire-heat anchor satisfies no algebraic
differential equation of order at most two. -/
theorem not_differentiallyAlgebraicOfOrder_two_entireHeat
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ (2 : ℕ)) * (n : ℂ) ^ (2 : ℕ) * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0) :
    ¬ DifferentiallyAlgebraicOfOrder (coeffFun a) 2 := by
  intro hDA
  have hSG := superGaussianCoeffs_of_entireHeat hheat
  have ha : EntireCoeffs a := entireCoeffs_of_superGaussian hSG
  have hf : Differentiable ℂ (coeffFun a) := differentiable_coeffFun ha
  obtain ⟨Q, hQ, hrel⟩ := exists_strelitzLogJetRelation_of_differentiallyAlgebraicOfOrder_two
    (hf.differentiableOn.analyticOnNhd isOpen_univ) hDA
  obtain ⟨E, ρ₀, hρ₀, hgapρ⟩ := exists_strelitzSecondJetGap hQ
  set ρ := min ρ₀ (1 / (12 * π)) with hρdef
  have hρ : 0 < ρ := lt_min hρ₀ (by positivity)
  have hρπ : 3 * π * ρ ≤ 1 / 4 := by
    have hle : ρ ≤ 1 / (12 * π) := min_le_right _ _
    calc 3 * π * ρ ≤ 3 * π * (1 / (12 * π)) := by gcongr
      _ = 1 / 4 := by field_simp; ring
  obtain ⟨κ, hκ, hκ1, hgap⟩ := hgapρ ρ hρ (min_le_left _ _)
  -- the plateau ratio `q` and width `B`, with `exp (-(B / 2)) = q`
  set q := min (1 / 128) (ρ / 64) with hqdef
  have hq0 : 0 < q := lt_min (by norm_num) (by positivity)
  have hq128 : q ≤ 1 / 128 := min_le_left _ _
  have hqρ : q ≤ ρ / 64 := min_le_right _ _
  set B := -2 * Real.log q with hBdef
  have hB : 0 < B := by
    have : Real.log q < 0 := Real.log_neg hq0 (by linarith)
    linarith
  have hexpB : Real.exp (-(B / 2)) = q := by
    rw [hBdef, show -(-2 * Real.log q / 2) = Real.log q by ring, Real.exp_log hq0]
  -- a far nonzero coefficient controls the size of the maximum term
  obtain ⟨n₀, -, hn₀⟩ := htrans 0
  obtain ⟨j, hj, haj⟩ := htrans (E + 2)
  have hajpos : 0 < ‖a j‖ := norm_pos_iff.mpr haj
  -- eventual conditions on the logarithmic radius
  have hev1 : ∀ᶠ x : ℝ in atTop, (x + 2) ^ E * (3 / κ) ≤ Real.exp x := by
    have hlim : Tendsto (fun x : ℝ => (x + 2) ^ E * Real.exp (-(x + 2))) atTop (𝓝 0) :=
      (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero E).comp
        (tendsto_atTop_add_const_right _ 2 tendsto_id)
    have hev := hlim.eventually (gt_mem_nhds (by positivity : (0 : ℝ) < κ / (3 * Real.exp 2)))
    filter_upwards [hev] with x hx
    have hsplit : (x + 2) ^ E = (x + 2) ^ E * Real.exp (-(x + 2)) * Real.exp (x + 2) := by
      rw [mul_assoc, ← Real.exp_add]
      simp
    have hexp2 : Real.exp (x + 2) = Real.exp x * Real.exp 2 := Real.exp_add x 2
    rw [hsplit, hexp2]
    have h2 : 0 < Real.exp 2 := Real.exp_pos 2
    have hx' : (x + 2) ^ E * Real.exp (-(x + 2)) * (3 * Real.exp 2) ≤ κ := by
      rw [lt_div_iff₀ (by positivity)] at hx
      exact hx.le
    have hκ3 : 0 < 3 / κ := by positivity
    calc (x + 2) ^ E * Real.exp (-(x + 2)) * (Real.exp x * Real.exp 2) * (3 / κ)
        = ((x + 2) ^ E * Real.exp (-(x + 2)) * (3 * Real.exp 2)) * Real.exp x / κ := by
          field_simp
      _ ≤ κ * Real.exp x / κ := by gcongr
      _ = Real.exp x := by field_simp
  have hev2 : ∀ᶠ x : ℝ in atTop, 2 ^ (E + 1) / ‖a j‖ ≤ Real.exp x :=
    Real.tendsto_exp_atTop.eventually_ge_atTop _
  have hev3 : ∀ᶠ x : ℝ in atTop, (centralIndex a (Real.exp x) : ℝ) ≤ x := by
    have hνlog := tendsto_entireHeat_centralIndex_div_log_zero ha hheat hn₀
    have hlt := (hνlog.comp Real.tendsto_exp_atTop).eventually (gt_mem_nhds one_pos)
    filter_upwards [hlt, eventually_gt_atTop 0] with x hx hx0
    simp only [Function.comp_def, Real.log_exp] at hx
    rw [div_lt_one hx0] at hx
    exact hx.le
  obtain ⟨X, hX⟩ := eventually_atTop.mp (hev1.and (hev2.and hev3))
  -- a wide plateau beyond every threshold
  obtain ⟨n, T, hnN, hTX, hTpos, hcu, hcv⟩ :=
    exists_wide_plateau hSG htrans hB (max (E + 2) (⌈3 / κ⌉₊ + 2)) (max X 0)
  set x := T + B / 2 with hxdef
  set t := Real.exp x with htdef
  have hx0 : 0 ≤ x := by linarith
  have hxX : X ≤ x := by linarith [le_max_left X 0]
  obtain ⟨hx1, hx2, hx3⟩ := hX x hxX
  have ht1 : 1 ≤ t := Real.one_le_exp hx0
  have ht0 : 0 < t := Real.exp_pos x
  have hνt : centralIndex a t = n := by
    have h1 : centralIndex a (Real.exp T) ≤ centralIndex a t := centralIndex_mono ha
      (Real.exp_pos T) (Real.exp_le_exp.mpr (by linarith : T ≤ x)) hn₀
    have h2 : centralIndex a t ≤ centralIndex a (Real.exp (T + B)) := centralIndex_mono ha ht0
      (Real.exp_le_exp.mpr (by linarith : x ≤ T + B)) hn₀
    rw [hcu] at h1
    rw [hcv] at h2
    omega
  have han : a n ≠ 0 := by
    have := coeff_centralIndex_ne_zero ha ht0 hn₀
    rwa [hνt] at this
  have hsep : ∀ m : ℕ, ‖a m‖ * t ^ m ≤ ‖a n‖ * t ^ n * q ^ idxDist m n := by
    intro m
    have h := term_le_midplateau ha hn₀ hcu hcv m
    rwa [mul_comm (-(B / 2)), Real.exp_nat_mul, hexpB] at h
  have hjets := fun z (hz : ‖z‖ = t) =>
    eulerJets_of_geometric_separation ha han ht0 hq0.le (by linarith) hsep hz
  -- the thresholds of the circle bootstrap at `r₀ = t`, `N = n`
  have hnx : (n : ℝ) ≤ x := by rw [← hνt]; exact hx3
  have hnE : E + 2 ≤ n := (le_max_left _ _).trans hnN
  have hnκ : ⌈3 / κ⌉₊ + 2 ≤ n := (le_max_right _ _).trans hnN
  have hNE : (E : ℝ) + 1 ≤ n := by
    have : ((E + 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hnE
    push_cast at this
    linarith
  have hN : 3 / κ + 1 ≤ n := by
    have h1 : 3 / κ ≤ (⌈3 / κ⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈3 / κ⌉₊ + 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast hnκ
    push_cast at h2
    linarith
  have hn2 : ((n : ℝ) + 2) ^ E * (3 / κ) ≤ t := by
    calc ((n : ℝ) + 2) ^ E * (3 / κ) ≤ (x + 2) ^ E * (3 / κ) := by
          gcongr
      _ ≤ t := hx1
  have hr₀N : 3 * ((n : ℝ) + 2) ^ E / κ ≤ t := by
    calc 3 * ((n : ℝ) + 2) ^ E / κ = ((n : ℝ) + 2) ^ E * (3 / κ) := by ring
      _ ≤ t := hn2
  have hinit : ∀ z ∈ sphere (0 : ℂ) t, strelitzCircleThreshold E n κ t ≤ ‖coeffFun a z‖ ∧
      ‖eulerLogDeriv (coeffFun a) z - n‖ ≤ 1 / 4 ∧
      ‖eulerLogDerivSecond (coeffFun a) z‖ ≤ ρ := by
    intro z hz
    have hzt : ‖z‖ = t := by simpa using hz
    obtain ⟨hfz, huz, hvz⟩ := hjets z hzt
    refine ⟨?_, by linarith, by linarith⟩
    have hμj : ‖a j‖ * t ^ j ≤ ‖a n‖ * t ^ n := by
      have h := hsep j
      have hq1 : q ^ idxDist j n ≤ 1 := pow_le_one₀ hq0.le (by linarith)
      calc ‖a j‖ * t ^ j ≤ ‖a n‖ * t ^ n * q ^ idxDist j n := h
        _ ≤ ‖a n‖ * t ^ n * 1 := by gcongr
        _ = ‖a n‖ * t ^ n := mul_one _
    have htj : t ^ (E + 2) ≤ t ^ j := pow_le_pow_right₀ ht1 hj
    have h1t : (1 + t) ^ E ≤ 2 ^ E * t ^ E := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) (by linarith) E
    have hbig : 2 ^ (E + 1) ≤ ‖a j‖ * t := by
      rw [div_le_iff₀ hajpos] at hx2
      linarith
    calc strelitzCircleThreshold E n κ t
        = (1 + t) ^ E * (((n : ℝ) + 2) ^ E * (3 / κ)) := by
          unfold strelitzCircleThreshold
          ring
      _ ≤ (2 ^ E * t ^ E) * t := by gcongr
      _ = 2 ^ (E + 1) * t ^ (E + 1) / 2 := by ring
      _ ≤ (‖a j‖ * t) * t ^ (E + 1) / 2 := by gcongr
      _ = ‖a j‖ * t ^ (E + 2) / 2 := by ring
      _ ≤ ‖a j‖ * t ^ j / 2 := by gcongr
      _ ≤ ‖a n‖ * t ^ n / 2 := by gcongr
      _ ≤ ‖coeffFun a z‖ := hfz
  have hpoly := iteratedDeriv_eq_zero_of_strelitzCleanCircle hf hrel hρ hρπ hκ hκ1 hgap ht1 hNE
    hN hr₀N hinit
  obtain ⟨m, hm, ham⟩ := htrans (n + 1)
  have hmn : (n : ℝ) + 1 / 2 < m := by
    have : ((n + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm
    push_cast at this
    linarith
  have hzero := hpoly m hmn
  have hcoeff := taylorCoeff_coeffFun ha m
  rw [taylorCoeff, hzero, mul_zero] at hcoeff
  exact ham hcoeff.symm

/-- **The differential-order floor.**  An infinite-spectrum entire-heat anchor satisfies no
algebraic differential equation of order at most two. -/
theorem not_differentiallyAlgebraicOfOrder_le_two_entireHeat
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ (2 : ℕ)) * (n : ℂ) ^ (2 : ℕ) * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0) {k : ℕ} (hk : k ≤ 2) :
    ¬ DifferentiallyAlgebraicOfOrder (coeffFun a) k := by
  intro hDA
  have h2 : DifferentiallyAlgebraicOfOrder (coeffFun a) 2 := by
    interval_cases k
    · exact hDA.succ.succ
    · exact hDA.succ
    · exact hDA
  exact not_differentiallyAlgebraicOfOrder_two_entireHeat hheat htrans h2

/-- **The card theorem.**  An entire-heat anchor is either a polynomial, or satisfies no algebraic
differential equation of order at most two. -/
theorem entireHeat_eventually_zero_or_not_differentiallyAlgebraicOfOrder_le_two
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ (2 : ℕ)) * (n : ℂ) ^ (2 : ℕ) * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z))) :
    (∃ M : ℕ, ∀ n, M ≤ n → a n = 0) ∨
      ∀ k ≤ 2, ¬ DifferentiallyAlgebraicOfOrder (coeffFun a) k := by
  by_cases htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0
  · exact Or.inr fun k hk => not_differentiallyAlgebraicOfOrder_le_two_entireHeat hheat htrans hk
  · push Not at htrans
    exact Or.inl htrans

/-- **Minimal order at least three.**  A differentially algebraic infinite-spectrum entire-heat
anchor has every algebraic differential equation of order at least three. -/
theorem three_le_of_differentiallyAlgebraicOfOrder_entireHeat
    (hheat : ∀ t z : ℂ, Summable (fun n : ℕ =>
      a n * Complex.exp (-(4 * (Real.pi : ℂ) ^ (2 : ℕ)) * (n : ℂ) ^ (2 : ℕ) * t)
        * Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (n : ℂ) * z)))
    (htrans : ∀ M : ℕ, ∃ n, M ≤ n ∧ a n ≠ 0) {k : ℕ}
    (hDA : DifferentiallyAlgebraicOfOrder (coeffFun a) k) : 3 ≤ k := by
  by_contra hk
  exact not_differentiallyAlgebraicOfOrder_le_two_entireHeat hheat htrans (by omega) hDA

end

end GaloisForLFunctions.HTGeometry
