import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheCrossEnergyOfTwoWindowsIsBoundedByTheirMasses
import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheStabilityRegimeReachesAFixedFractionOfTheRobinEulerThreshold
import GaloisForLFunctions.RHTower.ChebyshevPsiErrorInputs

/-!
# The stability regime reaches a quarter of the Robin–Euler threshold

Three refinements of `TheStabilityRegimeReachesAFixedFractionOfTheRobinEulerThreshold`:

* **The prime number theorem for the up-rows** (`exists_psi_le_of_ge`, `sum_mul_upRow_sq_le_pnt`,
  `eventually_upWeightPNT_le`): with `ψ(x) ≤ (1 + η)x` beyond some `X₀`, the low atoms `N/m ≥ X₀`
  have `m R_m ≤ (1 + η)N/(b log N) + N^b`. The high atoms `m > N/Y` keep Chebyshev's bound but form
  a harmonic tail of size at most `Y`. Hence
  `Σ_m m R_m² ≤ ((1 + η)²/b² + o(1)) N²/log N`, with Chebyshev's `B_ψ² ≈ 8.2` replaced by `1`.
* **The halved cross penalty** (`TheCrossEnergyOfTwoWindowsIsBoundedByTheirMasses`).
* **The parameters** `λ = 1/4`, `κ = 3/20`, `b = 19/20`, `θ = 2`, `ζ = 1/20`, `ρ = 3/2`.

Together (`eventually_weilQuad_windowTest_nonneg_quarter`): eventually in `N`, Weil's form is
nonnegative on every window test of shape `β(G_n) ≥ β‖G_n‖²` at every width
`w ≤ K★_q(β, ε, a) δ_N`, `K★_q = min(3/20, (3/4)/C_D, a/C_X, exp(2θ′(0) + 2c_∞ + β + γ − ε − a − 1/25))`,
`C_X ≈ 10.5`, `C_D ≈ 7.0`. This is `≈ 0.108` of the spacing for plateau profiles, a quarter of the
Robin–Euler threshold `≈ 0.43`, and `≈ 0.072` for every profile, against `≈ 0.16`. With absolute
values on the pole term, the linear costs (Lévy loss and pole) keep this method below about half
of the threshold even with optimal constants.
-/

noncomputable section

open MeasureTheory Finset Filter Asymptotics RHTower
open scoped ArithmeticFunction.vonMangoldt Topology

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

local notation "γ" => Real.eulerMascheroniConstant

variable {G : ℕ → ℝ → ℝ} {w : ℝ}

/-! ### The prime number theorem for the up-rows -/

/-- **PNT**: for every `η > 0`, `ψ(x) ≤ (1 + η) x` for all `x ≥ X₀`, some `X₀ ≥ 1`. -/
theorem exists_psi_le_of_ge {η : ℝ} (hη : 0 < η) :
    ∃ X₀ : ℝ, 1 ≤ X₀ ∧ ∀ x : ℝ, X₀ ≤ x → Chebyshev.psi x ≤ (1 + η) * x := by
  obtain ⟨X₁, hX₁⟩ := eventually_atTop.mp
    (tendsto_psi_div_self.eventually (Iio_mem_nhds (by linarith : (1 : ℝ) < 1 + η)))
  refine ⟨max X₁ 1, le_max_right _ _, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith [le_max_right X₁ 1]
  have h := hX₁ x (le_trans (le_max_left _ _) hx)
  rw [div_lt_iff₀ hx0] at h
  exact h.le

/-- The up-row weight with the prime number theorem,
`((1 + η)N/(b log N) + N^b)²(1 + log N) + (B_ψ N/(b log N) + N^b)² Y`. -/
def upWeightPNT (N : ℕ) (b η Y : ℝ) : ℝ :=
  ((1 + η) * N / (b * Real.log N) + (N : ℝ) ^ b) ^ 2 * (1 + Real.log N) +
    (psiConstant * N / (b * Real.log N) + (N : ℝ) ^ b) ^ 2 * Y

/-- **The up-row weight under the prime number theorem**: for `η > 0` there is `Y ≥ 1` with
`Σ_m m R_m² ≤ upWeightPNT N b η Y` for all `N ≥ 2`, `b > 0`. -/
theorem sum_mul_upRow_sq_le_pnt {η : ℝ} (hη : 0 < η) :
    ∃ Y : ℝ, 1 ≤ Y ∧ ∀ N : ℕ, 2 ≤ N → ∀ b : ℝ, 0 < b →
      ∑ m ∈ Icc 1 N, (m : ℝ) * upRow N m ^ 2 ≤ upWeightPNT N b η Y := by
  obtain ⟨X₀, hX₀1, hX₀⟩ := exists_psi_le_of_ge hη
  refine ⟨X₀ + 1, by linarith, fun N hN b hb0 => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  set R₁ := (1 + η) * N / (b * Real.log N) + (N : ℝ) ^ b
  set R₂ := psiConstant * N / (b * Real.log N) + (N : ℝ) ^ b
  have hharm : ∑ m ∈ Icc 1 N, (1 : ℝ) / m ≤ 1 + Real.log N := by
    have h := harmonic_le_one_add_log N
    simp only [_root_.harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
    simpa only [one_div] using h
  have hterm : ∀ m ∈ Icc 1 N, (m : ℝ) * upRow N m ^ 2 ≤
      R₁ ^ 2 * (1 / m) + R₂ ^ 2 * ((X₀ + 1) / N) := by
    intro m hm
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
    have h0 : 0 ≤ (m : ℝ) * upRow N m := mul_nonneg hm0.le (upRow_nonneg hm1)
    have hsum := mul_upRow_le_sum hN hm hb0
    rw [sum_vonMangoldt_Icc_eq_psi] at hsum
    have hq1 : (1 : ℝ) ≤ ((N / m : ℕ) : ℝ) := by exact_mod_cast Nat.div_pos hmN hm1
    have hdiv : (m : ℝ) * ((N / m : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.mul_div_le N m
    have hsplit : (m : ℝ) * upRow N m ^ 2 = ((m : ℝ) * upRow N m) ^ 2 * (1 / m) := by
      field_simp
    have hR₂0 : 0 ≤ R₂ ^ 2 * ((X₀ + 1) / N) := by positivity
    have hR₁0 : 0 ≤ R₁ ^ 2 * (1 / m) := by positivity
    by_cases hT : X₀ ≤ ((N / m : ℕ) : ℝ)
    · -- a low atom: the prime number theorem
      have hψ := hX₀ _ hT
      have h1 : (m : ℝ) * Chebyshev.psi ((N / m : ℕ) : ℝ) ≤ (1 + η) * N := by
        calc (m : ℝ) * Chebyshev.psi ((N / m : ℕ) : ℝ) ≤ m * ((1 + η) * ((N / m : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left hψ hm0.le
          _ = (1 + η) * (m * ((N / m : ℕ) : ℝ)) := by ring
          _ ≤ (1 + η) * N := mul_le_mul_of_nonneg_left hdiv (by linarith)
      have h2 : (m : ℝ) * upRow N m ≤ R₁ := by
        have : (m : ℝ) * Chebyshev.psi ((N / m : ℕ) : ℝ) / (b * Real.log N) ≤
            (1 + η) * N / (b * Real.log N) := div_le_div_of_nonneg_right h1 (by positivity)
        simp only [R₁]; linarith
      rw [hsplit]
      have := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ h0 h2 2)
        (by positivity : (0 : ℝ) ≤ 1 / m)
      linarith
    · -- a high atom: Chebyshev and `1/m < Y/N`
      push Not at hT
      have hψ := psi_le_psiConstant hq1
      have h1 : (m : ℝ) * Chebyshev.psi ((N / m : ℕ) : ℝ) ≤ psiConstant * N := by
        calc (m : ℝ) * Chebyshev.psi ((N / m : ℕ) : ℝ) ≤ m * (psiConstant * ((N / m : ℕ) : ℝ)) :=
              mul_le_mul_of_nonneg_left hψ hm0.le
          _ = psiConstant * (m * ((N / m : ℕ) : ℝ)) := by ring
          _ ≤ psiConstant * N := mul_le_mul_of_nonneg_left hdiv psiConstant_pos.le
      have h2 : (m : ℝ) * upRow N m ≤ R₂ := by
        have : (m : ℝ) * Chebyshev.psi ((N / m : ℕ) : ℝ) / (b * Real.log N) ≤
            psiConstant * N / (b * Real.log N) := div_le_div_of_nonneg_right h1 (by positivity)
        simp only [R₂]; linarith
      -- `N < (⌊N/m⌋ + 1) m < (X₀ + 1) m`
      have hlt : (N : ℝ) < (((N / m : ℕ) : ℝ) + 1) * m := by
        have := Nat.lt_div_mul_add (a := N) (show 0 < m by omega)
        exact_mod_cast (by linarith [this] : N < (N / m + 1) * m)
      have hinv : 1 / (m : ℝ) ≤ (X₀ + 1) / N := by
        rw [div_le_div_iff₀ hm0 hN0]
        nlinarith
      rw [hsplit]
      have := mul_le_mul (pow_le_pow_left₀ h0 h2 2) hinv (by positivity) (by positivity)
      linarith
  calc ∑ m ∈ Icc 1 N, (m : ℝ) * upRow N m ^ 2
      ≤ ∑ m ∈ Icc 1 N, (R₁ ^ 2 * (1 / m) + R₂ ^ 2 * ((X₀ + 1) / N)) := sum_le_sum hterm
    _ = R₁ ^ 2 * ∑ m ∈ Icc 1 N, (1 : ℝ) / m + R₂ ^ 2 * (X₀ + 1) := by
        rw [sum_add_distrib, ← mul_sum, sum_const, Nat.card_Icc, nsmul_eq_mul]
        push_cast; field_simp
    _ ≤ upWeightPNT N b η (X₀ + 1) := by
        simp only [upWeightPNT, R₁, R₂]
        gcongr


/-- **The PNT up-row weight is asymptotically sharp**:
`(1 + ζ) U_N + 1 + 1/ζ ≤ ((1 + ζ)((1 + η)/b)² + η') N²/log N` eventually. -/
theorem eventually_upWeightPNT_le {b η Y ζ η' : ℝ} (hb0 : 0 < b) (hb : b < 1) (hη : 0 < η)
    (hY : 1 ≤ Y) (hζ : 0 < ζ) (hη' : 0 < η') :
    ∀ᶠ N : ℕ in atTop, (1 + ζ) * upWeightPNT N b η Y + (1 + 1 / ζ) ≤
      ((1 + ζ) * ((1 + η) / b) ^ 2 + η') * ((N : ℝ) ^ 2 / Real.log N) := by
  set c₁ := (1 + η) / b
  set c₂ := psiConstant / b
  have hc₁ : 0 ≤ c₁ := by positivity
  have hc₂ : 0 ≤ c₂ := div_nonneg psiConstant_pos.le hb0.le
  set K := (1 + ζ) * (c₁ ^ 2 + 4 * c₁ + 2) + (1 + ζ) * (c₂ + 1) ^ 2 + 1
  have hK : 0 < K := by positivity
  set δ := min 1 (η' / K)
  have hδ0 : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδK : δ * K ≤ η' := by
    have := min_le_right 1 (η' / K)
    rw [le_div_iff₀ hK] at this; exact this
  filter_upwards [eventually_rpow_mul_log_le hb hδ0,
    eventually_ge_atTop (⌈Real.exp (Y / δ)⌉₊ + ⌈(1 + 1 / ζ) / δ⌉₊ + 2)] with N h1 h2
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  -- `Y/log N ≤ δ`, hence `1/log N ≤ δ`
  have hYδ : Y / Real.log N ≤ δ := by
    have hexp : Real.exp (Y / δ) ≤ N := by
      have := Nat.le_ceil (Real.exp (Y / δ))
      have : (⌈Real.exp (Y / δ)⌉₊ : ℝ) ≤ N := by exact_mod_cast (show _ ≤ N by omega)
      linarith
    have : Y / δ ≤ Real.log N := by
      rw [← Real.log_exp (Y / δ)]; exact Real.log_le_log (Real.exp_pos _) hexp
    rw [div_le_iff₀ hL]; rw [div_le_iff₀ hδ0] at this; linarith
  have hLδ : 1 / Real.log N ≤ δ :=
    (div_le_div_of_nonneg_right hY hL.le).trans hYδ
  have hcst : (1 + 1 / ζ) * Real.log N / N ^ 2 ≤ δ := by
    have hN : (1 + 1 / ζ) / δ ≤ N := by
      have := Nat.le_ceil ((1 + 1 / ζ) / δ)
      have : (⌈(1 + 1 / ζ) / δ⌉₊ : ℝ) ≤ N := by exact_mod_cast (show _ ≤ N by omega)
      linarith
    have hlogN : Real.log N ≤ N := (Real.log_le_sub_one_of_pos hN0).trans (by linarith)
    rw [div_le_iff₀ (by positivity)]
    rw [div_le_iff₀ hδ0] at hN
    have hζ' : 0 ≤ 1 + 1 / ζ := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hlogN hζ']
  set q := (N : ℝ) ^ b * Real.log N / N
  have hq0 : 0 ≤ q := by positivity
  have hqδ : q ≤ δ := by simp only [q]; rw [div_le_iff₀ hN0]; exact h1
  set Q := (N : ℝ) ^ 2 / Real.log N
  have hQ : 0 < Q := by positivity
  have hU : upWeightPNT N b η Y =
      Q * ((c₁ + q) ^ 2 * (1 + 1 / Real.log N) + (c₂ + q) ^ 2 * (Y / Real.log N)) := by
    simp only [upWeightPNT, Q, c₁, c₂, q]
    field_simp
    ring
  have hmain := sq_add_mul_le hc₁ hq0 hqδ hδ1
  have hmono : (c₁ + q) ^ 2 * (1 + 1 / Real.log N) ≤ (c₁ + q) ^ 2 * (1 + δ) :=
    mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
  have htail : (c₂ + q) ^ 2 * (Y / Real.log N) ≤ (c₂ + 1) ^ 2 * δ := by
    have h1' : (c₂ + q) ^ 2 ≤ (c₂ + 1) ^ 2 := pow_le_pow_left₀ (by positivity) (by linarith) 2
    exact mul_le_mul h1' hYδ (by positivity) (sq_nonneg _)
  have hcQ : 1 + 1 / ζ ≤ δ * Q := by
    simp only [Q]
    rw [mul_div_assoc', le_div_iff₀ hL]
    rw [div_le_iff₀ (by positivity)] at hcst
    linarith
  rw [hU]
  have h3 : (1 + ζ) * (Q * ((c₁ + q) ^ 2 * (1 + 1 / Real.log N) + (c₂ + q) ^ 2 * (Y / Real.log N))) ≤
      (1 + ζ) * (Q * ((c₁ ^ 2 + δ * (c₁ ^ 2 + 4 * c₁ + 2)) + (c₂ + 1) ^ 2 * δ)) := by
    gcongr; linarith
  have h4 : (1 + ζ) * (Q * ((c₁ ^ 2 + δ * (c₁ ^ 2 + 4 * c₁ + 2)) + (c₂ + 1) ^ 2 * δ)) + δ * Q =
      Q * ((1 + ζ) * c₁ ^ 2 + δ * K) := by simp only [K]; ring
  nlinarith [mul_le_mul_of_nonneg_left hδK hQ.le]

/-! ### Weil positivity at a quarter of the Robin–Euler threshold -/

/-- The edge constant `1/(2b) + η` at `b = 19/20`, `η = 1/100`. -/
def quarterCE : ℝ := 1 / (2 * (19 / 20)) + 1 / 100

/-- The up-row constant `(1 + ζ)((1 + η)/b)² + η'` at `b = 19/20`, `ζ = 1/20`, `η = η' = 1/100`. -/
def quarterCU : ℝ := (1 + 1 / 20) * ((1 + 1 / 100) / (19 / 20)) ^ 2 + 1 / 100

/-- The pole cost on `|y|²` at `θ = 2`, `ρ = 3/2`. -/
def quarterPoleX : ℝ :=
  Real.exp (1 / 100) * (3 / 2 * (1 + 1 / 100) + (1 + 1 / 2) * quarterCU / (3 / 2))

/-- The pole cost on the defect at `θ = 2`, `ρ = 3/2`. -/
def quarterPoleD : ℝ := Real.exp (1 / 100) * ((1 + 2) * quarterCE / (3 / 2))

/-- The linear cost on `|y|²`: the halved cross penalty at `λ = 1/4`, `κ = 3/20`, plus the pole. -/
def quarterCostX : ℝ := crossConstant (1 / 4) (3 / 20) / 2 + quarterPoleX

/-- The linear cost on the defect. -/
def quarterCostD : ℝ := (1 + 1 / (1 / 4)) / (1 - 3 / 20) + quarterPoleD

/-- The fraction `K★_q(β, ε, a)` of the spacing. -/
def quarterFraction (β ε a : ℝ) : ℝ :=
  min (min (3 / 20) (3 / 4 / quarterCostD))
    (min (a / quarterCostX)
      (Real.exp (2 * gammaHardyPhaseRate 0 + archRobinConstant + β + γ - ε - a - 1 / 25)))

theorem quarterCE_pos : 0 < quarterCE := by unfold quarterCE; norm_num

theorem quarterCU_pos : 0 < quarterCU := by unfold quarterCU; positivity

theorem quarterCostX_pos : 0 < quarterCostX := by
  unfold quarterCostX quarterPoleX crossConstant
  have := psiConstant_pos
  have := quarterCU_pos
  have := Real.log_nonneg (show (1 : ℝ) ≤ 2 by norm_num)
  positivity

theorem quarterCostD_pos : 0 < quarterCostD := by
  unfold quarterCostD quarterPoleD; have := quarterCE_pos; positivity

theorem quarterFraction_pos (β ε a : ℝ) (ha : 0 < a) : 0 < quarterFraction β ε a := by
  have := quarterCostX_pos
  have := quarterCostD_pos
  unfold quarterFraction
  exact lt_min (lt_min (by norm_num) (by positivity)) (lt_min (by positivity) (Real.exp_pos _))

/-- **The pole bound under the prime number theorem**: if `log N ≥ 100`, the weights obey their
asymptotic bounds and `w ≤ 1/50`, then `2|AB| ≤ wN (quarterPoleX |y|² + quarterPoleD D_N(y))`. -/
theorem two_mul_abs_poleMoments_windowTest_le_quarter (hG : ∀ n, ContDiff ℝ 2 (G n))
    (hGsupp : ∀ n u, u ∉ Set.Icc 0 w → G n u = 0) (hw0 : 0 < w) (hw : w ≤ 1 / 50) {N : ℕ}
    (hN : 2 ≤ N) (hLN : 100 ≤ Real.log N) {U : ℝ}
    (hUb : ∑ m ∈ Icc 1 N, (m : ℝ) * upRow N m ^ 2 ≤ U)
    (hEN : edgeWeight N (19 / 20) ≤ quarterCE * ((N : ℝ) ^ 2 / Real.log N))
    (hUN : (1 + 1 / 20) * U + (1 + 1 / (1 / 20)) ≤ quarterCU * ((N : ℝ) ^ 2 / Real.log N)) :
    2 * |(∫ u, windowTest N G u * Real.exp (-(u / 2))) * ∫ u, windowTest N G u * Real.exp (u / 2)| ≤
      w * N * (quarterPoleX * ∑ n ∈ Icc 1 N, windowNorm G n ^ 2 +
        quarterPoleD * poleDefect N (windowNorm G)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlogN : 0 < Real.log N := by linarith
  set y := windowNorm G
  set X := ∑ n ∈ Icc 1 N, y n ^ 2
  set D := poleDefect N y
  set S₁ := ∑ n ∈ Icc 1 N, y n * Real.exp (-(Real.log n / 2))
  set S₂ := ∑ n ∈ Icc 1 N, y n * Real.sqrt n
  obtain ⟨hA, hB⟩ := abs_poleRows_windowTest_le hG hGsupp hw0 N
  have hX : 0 ≤ X := sum_nonneg fun _ _ => sq_nonneg _
  have hD : 0 ≤ D := poleDefect_nonneg N y
  have hy0 : ∀ n, 0 ≤ y n := windowNorm_nonneg G
  have hS₁0 : 0 ≤ S₁ := sum_nonneg fun n _ => mul_nonneg (hy0 n) (Real.exp_pos _).le
  have hS₂0 : 0 ≤ S₂ := sum_nonneg fun n _ => mul_nonneg (hy0 n) (Real.sqrt_nonneg _)
  have hsw : Real.sqrt w * Real.sqrt w = w := Real.mul_self_sqrt hw0.le
  set Q := (N : ℝ) ^ 2 / Real.log N
  have hQ : 0 < Q := by positivity
  -- the `H`-row
  have hS₁ : S₁ ^ 2 ≤ (1 + Real.log N) * X := by
    have h := sum_mul_sq_le_sq_mul_sq (Icc 1 N) y (fun n => Real.exp (-(Real.log n / 2)))
    have hharm : ∑ n ∈ Icc 1 N, (1 : ℝ) / n ≤ 1 + Real.log N := by
      have h := harmonic_le_one_add_log N
      simp only [_root_.harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at h
      simpa only [one_div] using h
    have e2 : ∑ n ∈ Icc 1 N, Real.exp (-(Real.log n / 2)) ^ 2 = ∑ n ∈ Icc 1 N, (1 : ℝ) / n :=
      sum_congr rfl fun n hn => exp_neg_half_log_sq (Finset.mem_Icc.mp hn).1
    rw [e2] at h
    nlinarith [mul_le_mul_of_nonneg_left hharm hX]
  -- the `V`-row
  have hS₂ : S₂ ^ 2 ≤ (quarterCE * Q * (1 + 2) * D + (1 + 1 / 2) * quarterCU * Q * X) := by
    have h := sq_vRow_le_of_upRow_le hN (b := 19 / 20) (by norm_num) (θ := 2) (ζ := 1 / 20)
      (by norm_num) (by norm_num) hUb y
    have e1 : ∑ n ∈ Icc 1 N, Real.sqrt n * y n = S₂ := sum_congr rfl fun n _ => mul_comm _ _
    rw [e1] at h
    have h1 : (1 + 2) * edgeWeight N (19 / 20) * D ≤ (1 + 2) * (quarterCE * Q) * D :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hEN (by norm_num)) hD
    have h2 : (1 + 1 / 2) * ((1 + 1 / 20) * U + (1 + 1 / (1 / 20))) * X ≤
        (1 + 1 / 2) * (quarterCU * Q) * X :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hUN (by norm_num)) hX
    nlinarith
  -- `2|AB| ≤ 2 w e^{w/2} S₁ S₂ ≤ w e^{w/2}(ρ' S₁² + S₂²/ρ')`, `ρ' = (3/2) N/log N`
  have hAB : 2 * |(∫ u, windowTest N G u * Real.exp (-(u / 2))) *
      ∫ u, windowTest N G u * Real.exp (u / 2)| ≤ 2 * (w * Real.exp (w / 2)) * (S₁ * S₂) := by
    rw [abs_mul]
    have := mul_le_mul hA hB (abs_nonneg _) (by positivity)
    have e : Real.sqrt w * S₁ * (Real.exp (w / 2) * Real.sqrt w * S₂) =
        w * Real.exp (w / 2) * (S₁ * S₂) := by
      calc Real.sqrt w * S₁ * (Real.exp (w / 2) * Real.sqrt w * S₂) =
          (Real.sqrt w * Real.sqrt w) * (Real.exp (w / 2) * (S₁ * S₂)) := by ring
        _ = w * Real.exp (w / 2) * (S₁ * S₂) := by rw [hsw]; ring
    linarith
  set ρ := 3 / 2 * N / Real.log N
  have hρ : 0 < ρ := by positivity
  have hamgm : 2 * (S₁ * S₂) ≤ ρ * S₁ ^ 2 + S₂ ^ 2 / ρ := by
    have h : ρ * S₁ ^ 2 + S₂ ^ 2 / ρ - 2 * (S₁ * S₂) = (ρ * S₁ - S₂) ^ 2 / ρ := by
      field_simp; ring
    have : 0 ≤ (ρ * S₁ - S₂) ^ 2 / ρ := div_nonneg (sq_nonneg _) hρ.le
    linarith
  have hfirst : ρ * S₁ ^ 2 ≤ 3 / 2 * (1 + 1 / 100) * N * X := by
    calc ρ * S₁ ^ 2 ≤ ρ * ((1 + Real.log N) * X) := mul_le_mul_of_nonneg_left hS₁ hρ.le
      _ ≤ 3 / 2 * (1 + 1 / 100) * N * X := by
          simp only [ρ]
          rw [div_mul_eq_mul_div, div_le_iff₀ hlogN]
          nlinarith [mul_nonneg hX hN0.le]
  have hsecond : S₂ ^ 2 / ρ ≤ (quarterCE * (1 + 2) * D + (1 + 1 / 2) * quarterCU * X) * N /
      (3 / 2) := by
    rw [div_le_iff₀ hρ]
    have e : (quarterCE * (1 + 2) * D + (1 + 1 / 2) * quarterCU * X) * N / (3 / 2) * ρ =
        quarterCE * Q * (1 + 2) * D + (1 + 1 / 2) * quarterCU * Q * X := by
      simp only [ρ, Q]; field_simp
    rw [e]; exact hS₂
  have hexp : Real.exp (w / 2) ≤ Real.exp (1 / 100) := Real.exp_le_exp.mpr (by linarith)
  have hd0 : 0 ≤ 3 / 2 * (1 + 1 / 100) * N * X +
      (quarterCE * (1 + 2) * D + (1 + 1 / 2) * quarterCU * X) * N / (3 / 2) := by
    have := quarterCE_pos; have := quarterCU_pos; positivity
  calc 2 * |(∫ u, windowTest N G u * Real.exp (-(u / 2))) *
        ∫ u, windowTest N G u * Real.exp (u / 2)|
      ≤ w * Real.exp (w / 2) * (2 * (S₁ * S₂)) := by linarith
    _ ≤ w * Real.exp (w / 2) * (3 / 2 * (1 + 1 / 100) * N * X +
          (quarterCE * (1 + 2) * D + (1 + 1 / 2) * quarterCU * X) * N / (3 / 2)) :=
        mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ ≤ w * Real.exp (1 / 100) * (3 / 2 * (1 + 1 / 100) * N * X +
          (quarterCE * (1 + 2) * D + (1 + 1 / 2) * quarterCU * X) * N / (3 / 2)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp hw0.le) hd0
    _ = w * N * (quarterPoleX * X + quarterPoleD * D) := by
        simp only [quarterPoleX, quarterPoleD]; ring

/-- **Weil positivity at a quarter of the Robin–Euler threshold.** For `0 < ε ≤ 1/4` and `a > 0`,
eventually in `N`: for every `β`, every width `0 < w ≤ K★_q(β, ε, a) δ_N` and every window test
whose profiles have shape term `β(G_n) ≥ β‖G_n‖²`, Weil's form is nonnegative. -/
theorem eventually_weilQuad_windowTest_nonneg_quarter {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1 / 4)
    {a : ℝ} (ha : 0 < a) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ β w : ℝ, 0 < w → w ≤ quarterFraction β ε a * atomSpacing N →
      ∀ G : ℕ → ℝ → ℝ, (∀ n, ContDiff ℝ 2 (G n)) → (∀ n u, u ∉ Set.Icc 0 w → G n u = 0) →
      (∀ n, β * ∫ u, G n u ^ 2 ≤ bumpRobin (G n) w) → 0 ≤ weilQuad (windowTest N G) := by
  obtain ⟨N₁, hN₁⟩ := eventually_markovEnergy_windowTest_ge_fubini hε (κ := 3 / 20) (by norm_num)
    (by norm_num) (lam := 1 / 4) (by norm_num)
  obtain ⟨Y, hY1, hUb⟩ := sum_mul_upRow_sq_le_pnt (η := 1 / 100) (by norm_num)
  have hE := eventually_edgeWeight_le (b := 19 / 20) (η := 1 / 100) (by norm_num) (by norm_num)
    (by norm_num)
  have hU := eventually_upWeightPNT_le (b := 19 / 20) (η := 1 / 100) (Y := Y) (ζ := 1 / 20)
    (η' := 1 / 100) (by norm_num) (by norm_num) (by norm_num) hY1 (by norm_num) (by norm_num)
  have hL : ∀ᶠ N : ℕ in atTop, (100 : ℝ) ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 100
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp (hE.and (hU.and (hL.and (eventually_ge_atTop 50))))
  refine ⟨max N₁ N₂, fun N hN β w hw0 hw G hG hGsupp hβ => ?_⟩
  obtain ⟨hEN, hUN, hLN, hN50⟩ := hN₂ N (le_trans (le_max_right _ _) hN)
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hδ := atomSpacing_pos hN1
  have hδN : atomSpacing N * N ≤ 1 := by
    have h := atomSpacing_le_inv hN1
    calc atomSpacing N * N ≤ 1 / N * N := mul_le_mul_of_nonneg_right h hN0.le
      _ = 1 := by field_simp
  have hKs := quarterFraction_pos β ε a ha
  have hK1 : quarterFraction β ε a ≤ 3 / 20 := (min_le_left _ _).trans (min_le_left _ _)
  have hK2 : quarterFraction β ε a ≤ 3 / 4 / quarterCostD :=
    (min_le_left _ _).trans (min_le_right _ _)
  have hK3 : quarterFraction β ε a ≤ a / quarterCostX := (min_le_right _ _).trans (min_le_left _ _)
  have hK4 : quarterFraction β ε a ≤
      Real.exp (2 * gammaHardyPhaseRate 0 + archRobinConstant + β + γ - ε - a - 1 / 25) :=
    (min_le_right _ _).trans (min_le_right _ _)
  have hKK : w * N ≤ quarterFraction β ε a := by
    calc w * N ≤ quarterFraction β ε a * atomSpacing N * N :=
          mul_le_mul_of_nonneg_right hw hN0.le
      _ = quarterFraction β ε a * (atomSpacing N * N) := by ring
      _ ≤ quarterFraction β ε a * 1 := mul_le_mul_of_nonneg_left hδN hKs.le
      _ = quarterFraction β ε a := mul_one _
  have hK0 : 0 < w * N := by positivity
  have hwκ : w ≤ 3 / 20 * atomSpacing N := hw.trans (mul_le_mul_of_nonneg_right hK1 hδ.le)
  have hwsmall : w ≤ 1 / 300 := by
    have h1 : w * N ≤ 3 / 20 := hKK.trans hK1
    have h2 : (50 : ℝ) ≤ N := by exact_mod_cast hN50
    nlinarith
  have hM := hN₁ N (le_trans (le_max_left _ _) hN) w hw0 hwκ G hG hGsupp β hβ
  have hP := two_mul_abs_poleMoments_windowTest_le_quarter hG hGsupp hw0 (by linarith) (by omega)
    hLN (hUb N (by omega) (19 / 20) (by norm_num)) hEN hUN
  have hf := contDiff_windowTest hG N
  have hfc := hasCompactSupport_windowTest hGsupp N
  have hW : weilQuad (windowTest N G) = markovEnergy (fun u => (windowTest N G u : ℂ)) +
      2 * ((∫ u, windowTest N G u * Real.exp (-(u / 2))) *
        ∫ u, windowTest N G u * Real.exp (u / 2)) := by
    rw [weilQuad_eq hf hfc, add_sub_assoc, two_mul_cosh_sq_sub_sinh_sq_eq hf.continuous hfc,
      markovEnergy_ofReal_eq_archForm_sub_primeSum hf hfc, archForm_eq_levyEnergy hf hfc]
    ring
  rw [hW]
  have hc₀ : quarterPoleD * (w * N) ≤ 1 - ε - (1 + 1 / (1 / 4)) / (1 - 3 / 20) * (w * N) := by
    have h := mul_le_mul_of_nonneg_left (hKK.trans hK2) quarterCostD_pos.le
    have e : quarterCostD * (3 / 4 / quarterCostD) = 3 / 4 := by
      have := quarterCostD_pos; field_simp
    rw [e] at h
    unfold quarterCostD at h
    linarith
  have hφ₀ : quarterPoleX * (w * N) ≤ 2 * gammaHardyPhaseRate 0 + Real.log (1 / (w * N)) +
      archRobinConstant + β + γ - ε - Real.exp (1 / 2) / 2 * w -
      crossConstant (1 / 4) (3 / 20) / 2 * (w * N) := by
    have hlog : -(2 * gammaHardyPhaseRate 0 + archRobinConstant + β + γ - ε - a - 1 / 25) ≤
        Real.log (1 / (w * N)) := by
      have h6 : Real.log (w * N) ≤
          2 * gammaHardyPhaseRate 0 + archRobinConstant + β + γ - ε - a - 1 / 25 := by
        have := Real.log_le_log hK0 (hKK.trans hK4)
        rwa [Real.log_exp] at this
      have e : Real.log (1 / (w * N)) = -Real.log (w * N) := by
        rw [one_div (w * (N : ℝ)), Real.log_inv]
      rw [e]
      linarith
    have hcost : quarterCostX * (w * N) ≤ a := by
      have h := mul_le_mul_of_nonneg_left (hKK.trans hK3) quarterCostX_pos.le
      have e : quarterCostX * (a / quarterCostX) = a := by
        have := quarterCostX_pos; field_simp
      rwa [e] at h
    have hew : Real.exp (1 / 2) / 2 * w ≤ 1 / 25 := by
      have := exp_half_lt_two
      nlinarith
    unfold quarterCostX at hcost
    linarith
  set X := ∑ n ∈ Icc 1 N, windowNorm G n ^ 2
  set D := poleDefect N (windowNorm G)
  have hX : 0 ≤ X := sum_nonneg fun _ _ => sq_nonneg _
  have hD : 0 ≤ D := poleDefect_nonneg N _
  set P := (∫ u, windowTest N G u * Real.exp (-(u / 2))) * ∫ u, windowTest N G u * Real.exp (u / 2)
  have hPabs := neg_abs_le P
  have h1 := mul_nonneg hX (sub_nonneg.mpr hφ₀)
  have h2 := mul_nonneg hD (sub_nonneg.mpr hc₀)
  linarith

end GaloisForLFunctions.ArithmeticLorentzianGeometry
