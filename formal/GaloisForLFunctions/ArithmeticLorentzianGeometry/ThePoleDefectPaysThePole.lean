import GaloisForLFunctions.ArithmeticLorentzianGeometry.ThePoleDefectControlsTheVRow
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheHodgeIndexHoldsAtAFixedFractionOfTheSpacing
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartOfTheMarkovFormAtTheSpacing

/-!
# The pole defect pays the pole

Weil's form on an atomic test `f = Σ_{n ≤ N} x_n g(· − log n)` is the Markov form plus the pole
term, `W(f) = M(f) + 2AB` with `A = ∫ f e^{−u/2}`, `B = ∫ f e^{u/2}`. The pole term costs up to
`K√(log N)` against a uniform margin (`TheUniformMarginPaysThePoleOnlyUpToARootLogarithm`); the
proof at a fixed fraction `c★` of the spacing pays it with tilted per-atom margins and a constant
`c★ ≈ 10⁻¹¹`. Here the Dirichlet energy of the pole relations pays it, eventually in `N`, up to a
fraction of the spacing set by the finite part of the Markov form.

* **The Markov form keeps its defect** (`eventually_markovEnergy_ge_defect`): eventually in `N`,
  `M(f) ≥ ‖g‖²(φ₀|x|² + c₀ D_N(x))` with the finite part
  `φ₀ = 2θ′(0) + log(1/(wN)) + κ_L(φ) + γ − ε − (e^{1/2}/2)w − A wN` and `c₀ = 1 − ε − 32e² wN`;
  this is the lower bound of RenormalizedArithmeticPotentialTheory with the pole defect retained.
* **The defect pays the pole** (`two_mul_abs_poleMoments_le_defect`): by Cauchy–Schwarz on the
  `H`-row and the multiplicative Hardy inequality on the `V`-row (`sq_vRow_le`, applied to `|x|`,
  whose defect is smaller), `2|AB| ≤ c_P e^{w/2} wN ‖g‖²(2|x|² + D_N(x))`, `c_P = √(2C_H)`.
* **Weil positivity** (`eventually_weilQuad_atomicTest_nonneg_of_finitePart`): when
  `φ₀ ≥ 2c_P e^{w/2} wN` and `c₀ ≥ c_P e^{w/2} wN`, Weil's form is nonnegative on every atomic
  test. Hence (`eventually_weilQuad_nonneg_at_fraction`) there is an explicit fraction
  `K★(φ) > 0` of the spacing — the minimum of `1/(A + 2c_P e^{1/2})`, `exp(2θ′(0) + κ_L(φ) + γ − ε − 2)`
  and two overlap bounds — at which Weil's form is nonnegative on every atomic test, eventually in
  `N`. The Hodge index, `(TD_π)` and hyperbolic links of the atomic intersection Gram follow
  (`TheAtomicFormIsMetzlerBelowTheSpacing`).

The pole is paid by the defect of the prime form below its sharp counterterm, not by a tilt: the
vectors on which the pole term is large are far from the pole line, and the defect is large on
them. The fraction `K★` is limited by the Chebyshev constants of the cross penalty, not by the
mechanism; the finite part itself vanishes at the Robin–Euler threshold
(`TheStabilityRegimeEndsAtTheRobinEulerThreshold`).
-/

noncomputable section

open MeasureTheory Finset RHTower

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

local notation "γ" => Real.eulerMascheroniConstant

/-- The Hardy constant `C_H = 48B² + 51`, `B = log 4 + 4`. -/
def hardyConstant : ℝ := 48 * (Real.log 4 + 4) ^ 2 + 51

/-- The pole constant `c_P = √(2C_H)`. -/
def poleConstant : ℝ := Real.sqrt (2 * hardyConstant)

theorem hardyConstant_pos : 0 < hardyConstant := by unfold hardyConstant; positivity

theorem poleConstant_sq : poleConstant ^ 2 = 2 * hardyConstant :=
  Real.sq_sqrt (by have := hardyConstant_pos; linarith)

theorem poleConstant_pos : 0 < poleConstant :=
  Real.sqrt_pos.mpr (by have := hardyConstant_pos; linarith)

/-! ### The Markov form keeps its defect -/

/-- **The Markov form with its defect.** Eventually in `N`, every atomic test of the atom `φ(·/w)`,
`w ≤ δ_N/2`, `wN ≤ 1/(64e²)`, has `M(f) ≥ φ₀ ‖f‖² + ‖g‖² c₀ D_N(x)`. -/
theorem eventually_markovEnergy_ge_defect {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {K : ℝ}
    (hK : ∀ u v, |φ u - φ v| ≤ K * |u - v|) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : ℝ, 0 < w → w ≤ atomSpacing N / 2 →
      w * N ≤ markovOverlapBound → ∀ x : ℕ → ℝ,
        (2 * gammaHardyPhaseRate 0 + Real.log (1 / (w * N)) + profileRobin φ + γ - ε -
            Real.exp (1 / 2) / 2 * w - markovCrossConstant * (w * N)) *
            (∫ u, atomicTest N x (atomDilate φ w) u ^ 2) +
          (∫ u, atomDilate φ w u ^ 2) * (1 - ε - 32 * Real.exp 2 * (w * N)) * poleDefect N x ≤
          markovEnergy (fun u => (atomicTest N x (atomDilate φ w) u : ℂ)) := by
  obtain ⟨N₁, hN₁⟩ := eventually_atomicWeilForm_add_poleDefect_le hε
  refine ⟨max N₁ 1, fun N hN w hw0 hw hwN x => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hNN₁ : N₁ ≤ N := le_trans (le_max_left _ _) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hδ := atomSpacing_pos hN1
  have hδ1 := atomSpacing_le_one hN1
  have hw' : w < atomSpacing N := by linarith
  have hw1 : w ≤ 1 := by linarith
  obtain ⟨hgc2, hgsupp, hgc⟩ := atomDilate_facts hφ hφsupp hw0
  have hself := abs_levyEnergy_atomDilate_sub_le hφ hφsupp hφ0 hw0 hw1 hK
  have hf := contDiff_atomicTest hgc2 N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  rw [markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc, archForm_eq_levyEnergy hf hfc,
    primeSum_atomicTest hgc2 hgc hgsupp hw' x, integral_atomicTest_sq hgc2 hgc hgsupp hw' x]
  have hlevy := levyEnergy_atomicTest_ge_diag hgc2 hgc hgsupp hN1 hw0 hw x
  have hpen := cross_penalty_le hN1 hw0 x
  have hP := hN₁ N hNN₁ x
  have hM : 0 ≤ ∫ u, atomDilate φ w u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have hX : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun n _ => sq_nonneg (x n)
  have hg_low : (Real.log (1 / w) + profileRobin φ - Real.exp (1 / 2) / 2 * w) *
      ∫ u, atomDilate φ w u ^ 2 ≤ levyEnergy (atomDilate φ w) := by
    have := (abs_le.mp hself).1; linarith
  have hlog : Real.log (1 / (w * N)) = Real.log (1 / w) - Real.log N := by
    rw [one_div, Real.log_inv, Real.log_mul hw0.ne' hN0.ne', one_div, Real.log_inv]; ring
  have h1 := mul_le_mul_of_nonneg_left hg_low hX
  have h2 := mul_le_mul_of_nonneg_left hpen
    (by positivity : (0 : ℝ) ≤ 2 * ∫ u, atomDilate φ w u ^ 2)
  have h3 := mul_le_mul_of_nonneg_left hP hM
  rw [hlog]
  unfold markovCrossConstant
  linarith

/-! ### The defect pays the pole -/

theorem poleDefect_abs_le (N : ℕ) (x : ℕ → ℝ) :
    poleDefect N (fun n => |x n|) ≤ poleDefect N x := by
  refine sum_le_sum fun m _ => sum_le_sum fun t _ => ?_
  refine mul_le_mul_of_nonneg_left ?_ ArithmeticFunction.vonMangoldt_nonneg
  have ht : 0 ≤ Real.sqrt t := Real.sqrt_nonneg _
  have e : |x m| / Real.sqrt t = |x m / Real.sqrt t| := by rw [abs_div, abs_of_nonneg ht]
  rw [e, ← sq_abs (x (m * t) - x m / Real.sqrt t)]
  exact pow_le_pow_left₀ (abs_nonneg _) (abs_abs_sub_abs_le_abs_sub _ _) 2 |>.trans_eq'
    (by rw [sq_abs])

/-- **The defect pays the pole**: for `N ≥ 3`,
`2|AB| ≤ c_P e^{w/2} wN ‖g‖² (2|x|² + D_N(x))`. -/
theorem two_mul_abs_poleMoments_le_defect {g : ℝ → ℝ} {w : ℝ} (hg : Continuous g)
    (hgc : HasCompactSupport g) (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 < w)
    {N : ℕ} (hN : 3 ≤ N) (x : ℕ → ℝ) :
    2 * |(∫ u, atomicTest N x g u * Real.exp (-(u / 2))) *
        ∫ u, atomicTest N x g u * Real.exp (u / 2)| ≤
      poleConstant * Real.exp (w / 2) * (w * N) * (∫ u, g u ^ 2) *
        (2 * ∑ n ∈ Icc 1 N, x n ^ 2 + poleDefect N x) := by
  set A₁ := ∫ u, |g u|
  set G := ∫ u, g u ^ 2
  set X := ∑ n ∈ Icc 1 N, x n ^ 2
  set D := poleDefect N x
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hL1 : 1 ≤ Real.log N := by
    have h3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
    have he : Real.exp 1 ≤ 3 := le_of_lt (Real.exp_one_lt_d9.trans (by norm_num))
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (he.trans h3)
  have hA₁ : 0 ≤ A₁ := integral_nonneg fun _ => abs_nonneg _
  have hG : 0 ≤ G := integral_nonneg fun _ => sq_nonneg _
  have hX : 0 ≤ X := sum_nonneg fun _ _ => sq_nonneg _
  have hD : 0 ≤ D := poleDefect_nonneg N x
  -- the atom moments
  have hA : |∫ u, atomicTest N x g u * Real.exp (-(u / 2))| ≤
      A₁ * ∑ n ∈ Icc 1 N, |x n| * Real.exp (-(Real.log n / 2)) := by
    rw [integral_atomicTest_mul (by fun_prop) hg hgsupp, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n _ => ?_)
    rw [abs_mul]
    have := abs_integral_shift_mul_le hg hgc hgsupp
      (φ := fun u => Real.exp (-(u / 2))) (by fun_prop) (c := Real.log n)
      (M := Real.exp (-(Real.log n / 2))) fun u hu => by
        rw [abs_of_pos (Real.exp_pos _)]
        exact Real.exp_le_exp.mpr (by linarith [hu.1])
    nlinarith [abs_nonneg (x n), Real.exp_pos (-(Real.log n / 2))]
  have hB : |∫ u, atomicTest N x g u * Real.exp (u / 2)| ≤
      Real.exp (w / 2) * A₁ * ∑ n ∈ Icc 1 N, |x n| * Real.sqrt n := by
    rw [integral_atomicTest_mul (by fun_prop) hg hgsupp, mul_sum]
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun n hn => ?_)
    have hn1 := (Finset.mem_Icc.mp hn).1
    have hsq : Real.exp (Real.log n / 2) = Real.sqrt n := by
      rw [← Real.sqrt_sq (Real.exp_pos _).le, exp_half_log_sq hn1]
    rw [abs_mul]
    have := abs_integral_shift_mul_le hg hgc hgsupp
      (φ := fun u => Real.exp (u / 2)) (by fun_prop) (c := Real.log n)
      (M := Real.exp (Real.log n / 2) * Real.exp (w / 2)) fun u hu => by
        rw [abs_of_pos (Real.exp_pos _), ← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith [hu.2])
    rw [hsq] at this
    nlinarith [abs_nonneg (x n), Real.exp_pos (w / 2), Real.sqrt_nonneg (n : ℝ)]
  -- the `H`-row by Cauchy–Schwarz
  have hS₁ : (∑ n ∈ Icc 1 N, |x n| * Real.exp (-(Real.log n / 2))) ^ 2 ≤ X * (2 * Real.log N) := by
    have h := sum_mul_sq_le_sq_mul_sq (Icc 1 N) (fun n => |x n|)
      (fun n => Real.exp (-(Real.log n / 2)))
    have hharm : ∑ n ∈ Icc 1 N, (1 : ℝ) / n ≤ 1 + Real.log N := by
      have h := harmonic_le_one_add_log N
      simp only [_root_.harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
      simpa only [one_div] using h
    have e1 : ∑ n ∈ Icc 1 N, |x n| ^ 2 = X := sum_congr rfl fun n _ => sq_abs _
    have e2 : ∑ n ∈ Icc 1 N, Real.exp (-(Real.log n / 2)) ^ 2 = ∑ n ∈ Icc 1 N, (1 : ℝ) / n :=
      sum_congr rfl fun n hn => exp_neg_half_log_sq (Finset.mem_Icc.mp hn).1
    rw [e1, e2] at h
    exact h.trans (mul_le_mul_of_nonneg_left (by linarith) hX)
  -- the `V`-row by the multiplicative Hardy inequality
  have hS₂ : (∑ n ∈ Icc 1 N, |x n| * Real.sqrt n) ^ 2 ≤
      hardyConstant * ((N : ℝ) ^ 2 / Real.log N) * (D + X) := by
    have h := sq_vRow_le hN (fun n => |x n|)
    have e1 : ∑ n ∈ Icc 1 N, Real.sqrt n * |x n| = ∑ n ∈ Icc 1 N, |x n| * Real.sqrt n :=
      sum_congr rfl fun n _ => mul_comm _ _
    have e2 : ∑ n ∈ Icc 1 N, |x n| ^ 2 = X := sum_congr rfl fun n _ => sq_abs _
    rw [e1, e2] at h
    refine h.trans (mul_le_mul_of_nonneg_left (by linarith [poleDefect_abs_le N x]) ?_)
    have := hardyConstant_pos
    positivity
  have hA1 : A₁ ^ 2 ≤ w * G := sq_integral_abs_le hg hgsupp hw0
  -- assemble the squares
  set P := (∫ u, atomicTest N x g u * Real.exp (-(u / 2))) * ∫ u, atomicTest N x g u * Real.exp (u / 2)
  set S₁ := ∑ n ∈ Icc 1 N, |x n| * Real.exp (-(Real.log n / 2))
  set S₂ := ∑ n ∈ Icc 1 N, |x n| * Real.sqrt n
  have hS₁0 : 0 ≤ S₁ := sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have hS₂0 : 0 ≤ S₂ := sum_nonneg fun n _ => mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hP : |P| ≤ A₁ * S₁ * (Real.exp (w / 2) * A₁ * S₂) := by
    rw [abs_mul]; exact mul_le_mul hA hB (abs_nonneg _) (by positivity)
  have hP2 : P ^ 2 ≤ 2 * hardyConstant * Real.exp w * (w * N) ^ 2 * G ^ 2 * X * (D + X) := by
    have hexp : Real.exp (w / 2) ^ 2 = Real.exp w := by rw [← Real.exp_nat_mul]; ring_nf
    have hP' : P ^ 2 ≤ (A₁ * S₁ * (Real.exp (w / 2) * A₁ * S₂)) ^ 2 := by
      rw [← sq_abs P]; exact pow_le_pow_left₀ (abs_nonneg _) hP 2
    have e : (A₁ * S₁ * (Real.exp (w / 2) * A₁ * S₂)) ^ 2 =
        Real.exp w * (A₁ ^ 2) ^ 2 * S₁ ^ 2 * S₂ ^ 2 := by rw [← hexp]; ring
    rw [e] at hP'
    have hA4 : (A₁ ^ 2) ^ 2 ≤ (w * G) ^ 2 := pow_le_pow_left₀ (sq_nonneg _) hA1 2
    have hSS : S₁ ^ 2 * S₂ ^ 2 ≤
        X * (2 * Real.log N) * (hardyConstant * ((N : ℝ) ^ 2 / Real.log N) * (D + X)) :=
      mul_le_mul hS₁ hS₂ (sq_nonneg _) (by positivity)
    have e2 : X * (2 * Real.log N) * (hardyConstant * ((N : ℝ) ^ 2 / Real.log N) * (D + X)) =
        2 * hardyConstant * N ^ 2 * X * (D + X) := by field_simp
    rw [e2] at hSS
    calc P ^ 2 ≤ Real.exp w * (A₁ ^ 2) ^ 2 * S₁ ^ 2 * S₂ ^ 2 := hP'
      _ = Real.exp w * (A₁ ^ 2) ^ 2 * (S₁ ^ 2 * S₂ ^ 2) := by ring
      _ ≤ Real.exp w * (w * G) ^ 2 * (2 * hardyConstant * N ^ 2 * X * (D + X)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hA4 (Real.exp_pos w).le) hSS
            (mul_nonneg (sq_nonneg _) (sq_nonneg _)) (by positivity)
      _ = 2 * hardyConstant * Real.exp w * (w * N) ^ 2 * G ^ 2 * X * (D + X) := by ring
  -- `(2X + D)² ≥ 4X(X + D)`
  set c := poleConstant * Real.exp (w / 2) * (w * N)
  have hc0 : 0 ≤ c := by have := poleConstant_pos; positivity
  have hc2 : c ^ 2 = 2 * hardyConstant * Real.exp w * (w * N) ^ 2 := by
    simp only [c]
    rw [mul_pow, mul_pow, poleConstant_sq, ← Real.exp_nat_mul]; ring_nf
  have h2 : (2 * |P|) ^ 2 ≤ (c * G * (2 * X + D)) ^ 2 := by
    have hl : (2 * |P|) ^ 2 = 4 * P ^ 2 := by rw [mul_pow, sq_abs]; norm_num
    have hr : (c * G * (2 * X + D)) ^ 2 = c ^ 2 * G ^ 2 * (2 * X + D) ^ 2 := by ring
    rw [hl, hr, hc2]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hardyConstant_pos.le (Real.exp_pos w).le)
      (sq_nonneg (w * N))) (sq_nonneg G), sq_nonneg D]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h2

/-! ### Weil positivity -/

/-- **Weil positivity from the finite part.** Eventually in `N`, at every width `w ≤ δ_N/2` with
`wN ≤ 1/(64e²)`, `c_P e^{w/2} wN ≤ c₀` and `2c_P e^{w/2} wN ≤ φ₀`, Weil's form is nonnegative on
every atomic test of the atom `φ(·/w)`. -/
theorem eventually_weilQuad_atomicTest_nonneg_of_finitePart {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {K : ℝ}
    (hK : ∀ u v, |φ u - φ v| ≤ K * |u - v|) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 2) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : ℝ, 0 < w → w ≤ atomSpacing N / 2 →
      w * N ≤ markovOverlapBound →
      poleConstant * Real.exp (w / 2) * (w * N) ≤ 1 - ε - 32 * Real.exp 2 * (w * N) →
      2 * (poleConstant * Real.exp (w / 2) * (w * N)) ≤
        2 * gammaHardyPhaseRate 0 + Real.log (1 / (w * N)) + profileRobin φ + γ - ε -
          Real.exp (1 / 2) / 2 * w - markovCrossConstant * (w * N) →
      ∀ x : ℕ → ℝ, 0 ≤ weilQuad (atomicTest N x (atomDilate φ w)) := by
  obtain ⟨N₀, hN₀⟩ := eventually_markovEnergy_ge_defect hφ hφsupp hφ0 hK hε hε1
  refine ⟨max N₀ 3, fun N hN w hw0 hw hwN hc₀ hφ₀ x => ?_⟩
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hM := hN₀ N (le_trans (le_max_left _ _) hN) w hw0 hw hwN x
  obtain ⟨hgc2, hgsupp, hgc⟩ := atomDilate_facts hφ hφsupp hw0
  have hw' : w < atomSpacing N := by linarith [atomSpacing_pos (show 1 ≤ N by omega)]
  have hf := contDiff_atomicTest hgc2 N x
  have hfc := hasCompactSupport_atomicTest hgsupp N x
  have hpole := two_mul_abs_poleMoments_le_defect hgc2.continuous hgc hgsupp hw0 hN3 x
  rw [integral_atomicTest_sq hgc2 hgc hgsupp hw' x] at hM
  -- Weil's form is the Markov form plus the pole term
  have hW : weilQuad (atomicTest N x (atomDilate φ w)) =
      markovEnergy (fun u => (atomicTest N x (atomDilate φ w) u : ℂ)) +
        2 * (∫ u, atomicTest N x (atomDilate φ w) u * Real.exp (-(u / 2))) *
          ∫ u, atomicTest N x (atomDilate φ w) u * Real.exp (u / 2) := by
    rw [weilQuad_eq hf hfc, add_sub_assoc, two_mul_cosh_sq_sub_sinh_sq_eq hf.continuous hfc,
      markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc, archForm_eq_levyEnergy hf hfc]
    ring
  rw [hW]
  set G := ∫ u, atomDilate φ w u ^ 2
  set X := ∑ n ∈ Icc 1 N, x n ^ 2
  set D := poleDefect N x
  set c := poleConstant * Real.exp (w / 2) * (w * N)
  set φ₀ := 2 * gammaHardyPhaseRate 0 + Real.log (1 / (w * N)) + profileRobin φ + γ - ε -
    Real.exp (1 / 2) / 2 * w - markovCrossConstant * (w * N)
  set c₀ := 1 - ε - 32 * Real.exp 2 * (w * N)
  set P := (∫ u, atomicTest N x (atomDilate φ w) u * Real.exp (-(u / 2))) *
    ∫ u, atomicTest N x (atomDilate φ w) u * Real.exp (u / 2)
  have hG : 0 ≤ G := integral_nonneg fun _ => sq_nonneg _
  have hX : 0 ≤ X := sum_nonneg fun _ _ => sq_nonneg _
  have hD : 0 ≤ D := poleDefect_nonneg N x
  have hP := neg_abs_le P
  have h1 : 0 ≤ G * ((φ₀ - 2 * c) * X) := mul_nonneg hG (mul_nonneg (by linarith) hX)
  have h2 : 0 ≤ G * ((c₀ - c) * D) := mul_nonneg hG (mul_nonneg (by linarith) hD)
  have e : 2 * (∫ u, atomicTest N x (atomDilate φ w) u * Real.exp (-(u / 2))) *
      ∫ u, atomicTest N x (atomDilate φ w) u * Real.exp (u / 2) = 2 * P := by ring
  rw [e]
  nlinarith

/-- The fraction `K★(φ, ε)` of the spacing at which the pole defect pays the pole. -/
def defectFraction (φ : ℝ → ℝ) (ε : ℝ) : ℝ :=
  min (min markovOverlapBound (1 / (4 * (poleConstant * Real.exp (1 / 2) + 32 * Real.exp 2))))
    (min (1 / (markovCrossConstant + 2 * (poleConstant * Real.exp (1 / 2))))
      (Real.exp (2 * gammaHardyPhaseRate 0 + profileRobin φ + γ - ε - 2)))

theorem markovCrossConstant_pos : 0 < markovCrossConstant := by
  unfold markovCrossConstant
  have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
  positivity

theorem defectFraction_pos (φ : ℝ → ℝ) (ε : ℝ) : 0 < defectFraction φ ε := by
  have := poleConstant_pos
  have := markovCrossConstant_pos
  unfold defectFraction markovOverlapBound
  refine lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (Real.exp_pos _))

/-- **Weil positivity at the fraction `K★(φ, ε)` of the spacing, eventually in `N`**: for every
`C²` Lipschitz profile `φ` on `[0, 1]` and `0 < ε ≤ 1/4`, eventually in `N`, Weil's form is
nonnegative on every atomic test of the atom `φ(·/w)` with `0 < w ≤ K★ δ_N`. -/
theorem eventually_weilQuad_nonneg_at_fraction {φ : ℝ → ℝ} (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {K : ℝ}
    (hK : ∀ u v, |φ u - φ v| ≤ K * |u - v|) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : ℝ, 0 < w → w ≤ defectFraction φ ε * atomSpacing N →
      ∀ x : ℕ → ℝ, 0 ≤ weilQuad (atomicTest N x (atomDilate φ w)) := by
  obtain ⟨N₀, hN₀⟩ := eventually_weilQuad_atomicTest_nonneg_of_finitePart hφ hφsupp hφ0 hK hε
    (by linarith)
  refine ⟨max N₀ 1, fun N hN w hw0 hw x => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hδ := atomSpacing_pos hN1
  have hδN : atomSpacing N * N ≤ 1 := by
    have h := atomSpacing_le_inv hN1
    calc atomSpacing N * N ≤ 1 / N * N := mul_le_mul_of_nonneg_right h hN0.le
      _ = 1 := by field_simp
  have hδ1 : atomSpacing N ≤ 1 := atomSpacing_le_one hN1
  set Ks := defectFraction φ ε
  have hKs := defectFraction_pos φ ε
  have hc := poleConstant_pos
  have hA := markovCrossConstant_pos
  -- the pieces of `K★`
  have hK1 : Ks ≤ markovOverlapBound := (min_le_left _ _).trans (min_le_left _ _)
  have hK2 : Ks ≤ 1 / (4 * (poleConstant * Real.exp (1 / 2) + 32 * Real.exp 2)) :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hK3 : Ks ≤ 1 / (markovCrossConstant + 2 * (poleConstant * Real.exp (1 / 2))) :=
    (min_le_right _ _).trans (min_le_left _ _)
  have hK4 : Ks ≤ Real.exp (2 * gammaHardyPhaseRate 0 + profileRobin φ + γ - ε - 2) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hMOB : markovOverlapBound ≤ 1 / 2 := by
    unfold markovOverlapBound
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [Real.add_one_le_exp 2]
  -- the overlap ratio `K = wN ≤ K★`
  have hwN : w * N ≤ Ks := by
    calc w * N ≤ Ks * atomSpacing N * N := mul_le_mul_of_nonneg_right hw hN0.le
      _ = Ks * (atomSpacing N * N) := by ring
      _ ≤ Ks * 1 := mul_le_mul_of_nonneg_left hδN hKs.le
      _ = Ks := mul_one Ks
  have hwN0 : 0 < w * N := by positivity
  have hw2 : w ≤ atomSpacing N / 2 := by
    calc w ≤ Ks * atomSpacing N := hw
      _ ≤ 1 / 2 * atomSpacing N := mul_le_mul_of_nonneg_right (hK1.trans hMOB) hδ.le
      _ = atomSpacing N / 2 := by ring
  have hw1 : w ≤ 1 / 2 := by linarith
  have hexp : Real.exp (w / 2) ≤ Real.exp (1 / 2) := Real.exp_le_exp.mpr (by linarith)
  have hcK : poleConstant * Real.exp (w / 2) * (w * N) ≤ poleConstant * Real.exp (1 / 2) * Ks :=
    mul_le_mul (mul_le_mul_of_nonneg_left hexp hc.le) hwN hwN0.le (by positivity)
  refine hN₀ N (le_trans (le_max_left _ _) hN) w hw0 hw2 (hwN.trans hK1) ?_ ?_ x
  · -- the defect keeps a positive weight
    have h4 : (poleConstant * Real.exp (1 / 2) + 32 * Real.exp 2) * Ks ≤ 1 / 4 := by
      have hpos : 0 < 4 * (poleConstant * Real.exp (1 / 2) + 32 * Real.exp 2) := by positivity
      rw [le_div_iff₀ hpos] at hK2
      linarith
    have : 32 * Real.exp 2 * (w * N) ≤ 32 * Real.exp 2 * Ks :=
      mul_le_mul_of_nonneg_left hwN (by positivity)
    nlinarith
  · -- the finite part exceeds the pole cost
    have h5 : (markovCrossConstant + 2 * (poleConstant * Real.exp (1 / 2))) * Ks ≤ 1 := by
      have hpos : 0 < markovCrossConstant + 2 * (poleConstant * Real.exp (1 / 2)) := by positivity
      rw [le_div_iff₀ hpos] at hK3
      linarith
    have hlog : -(2 * gammaHardyPhaseRate 0 + profileRobin φ + γ - ε - 2) ≤
        Real.log (1 / (w * N)) := by
      have h6 : Real.log (w * N) ≤ 2 * gammaHardyPhaseRate 0 + profileRobin φ + γ - ε - 2 := by
        have := Real.log_le_log hwN0 (hwN.trans hK4)
        rwa [Real.log_exp] at this
      rw [one_div, Real.log_inv]
      linarith
    have hAK : markovCrossConstant * (w * N) ≤ markovCrossConstant * Ks :=
      mul_le_mul_of_nonneg_left hwN hA.le
    have hew : Real.exp (1 / 2) / 2 * w ≤ 1 := by
      have := exp_half_lt_two
      nlinarith [Real.exp_pos (1 / 2 : ℝ)]
    linarith

/-- **The Hodge index of the atomic intersection Gram at `K★`, eventually in `N`.** -/
theorem eventually_atomicIntersectionGram_isHyperbolic_at_fraction {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2)
    {K : ℝ} (hK : ∀ u v, |φ u - φ v| ≤ K * |u - v|) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : ℝ, 0 < w → w ≤ defectFraction φ ε * atomSpacing N →
      IsHyperbolic (atomicIntersectionGram (atomDilate φ w) N) := by
  obtain ⟨N₀, h⟩ := eventually_weilQuad_nonneg_at_fraction hφ hφsupp hφ0 hK hε hε1
  refine ⟨N₀, fun N hN w hw0 hw => ?_⟩
  obtain ⟨hgc2, hgsupp, -⟩ := atomDilate_facts hφ hφsupp hw0
  rw [atomicIntersectionGram_isHyperbolic_iff hgc2 hgsupp hw0.le N]
  intro d
  rw [finAtomicTest_eq_atomicTest]
  exact h N hN w hw0 hw _

end GaloisForLFunctions.ArithmeticLorentzianGeometry
