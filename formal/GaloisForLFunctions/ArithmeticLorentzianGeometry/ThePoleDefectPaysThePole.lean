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
            ∫ u, atomicTest N x (atomDilate φ w) u ^ 2 +
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
  have hsq := integral_atomicTest_sq hgc2 hgc hgsupp hw' x
  rw [hlog]
  simp only [hsq]
  unfold markovCrossConstant
  linarith

/-! ### The defect pays the pole -/

omit [Fintype ℕ] in
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
    unfold hardyConstant at *
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
    rw [mul_pow, sq_abs, mul_pow, mul_pow, hc2]
    nlinarith [mul_nonneg (mul_nonneg (mul_nonneg hardyConstant_pos.le (Real.exp_pos w).le)
      (sq_nonneg (w * N))) (sq_nonneg G), sq_nonneg D]
  exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp h2

end GaloisForLFunctions.ArithmeticLorentzianGeometry
