import GaloisForLFunctions.RHTower.WeilOneSidedConvergenceRigidity
import GaloisForLFunctions.RHTower.PrimeSmallDeviationArithmetic

/-!
# Convergence of the harmonic deviation series on the Weil cone

**Theorem** (`exists_tendsto_sum_coneDeviation_div`). Let `lam` be full-cone Weil-positive and
suppose `d = lam − Λ` is `o(Λ)`: for every `η > 0`, `|d(n)| ≤ η Λ(n)` for all large `n`. Then the
partial sums `Σ_{n<N} d(n)/n` converge as `N → ∞`.

**Proof.** Let `φ ≥ 0` be the continuous harmonic profile, supported in `[−½, ½]`, let
`Φ(y) = ∫_{−1}^y φ` and `I = Φ(1) > 0`. The harmonic windows `W(L) = Σ_n d(n) φ(log n − L)/n`
satisfy `|W(L)| ≤ C/L²` for `L ≥ L₁`, by window pinning and the smoothed prime number theorem.
For `N ≤ N'` with `X = log N` and `X' = log N'`,
`I Σ_{N≤n<N'} d(n)/n = ∫_X^{X'} W + Σ_n (d(n)/n) (e(log n − X) − e(log n − X'))`,
where `e(y) = I 1_{y≥0} − Φ(y)` is bounded by `I` and vanishes for `|y| > ½`.
* The integral is at most `C/X`.
* Each boundary sum is at most `I Σ_{|log n − Z| ≤ ½} |d(n)|/n`. For large `Z` this is at most
  `I η (2 log 4 + 16) e^{1/2}`, by the square-root Chebyshev bound.

Hence the partial sums are Cauchy.
-/

noncomputable section

open MeasureTheory Set Filter Topology Finset ArithmeticFunction
open scoped Real

namespace RHTower.WeilOneSided

open RHTower.PrimeSmallDeviation

/-! ## The primitive of a profile -/

section Primitive

variable {φ : ℝ → ℝ}

/-- The primitive `Φ(y) = ∫_{−1}^y φ`. -/
def profilePrimitive (φ : ℝ → ℝ) (y : ℝ) : ℝ := ∫ x in (-1 : ℝ)..y, φ x

theorem integral_eq_zero_of_far (hφs : ∀ x, 1 / 2 < |x| → φ x = 0) {a b : ℝ}
    (h : ∀ x ∈ uIcc a b, 1 / 2 < |x|) : ∫ x in a..b, φ x = 0 := by
  rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) fun x hx => hφs x (h x hx)]
  simp

theorem profilePrimitive_eq_zero (hφs : ∀ x, 1 / 2 < |x| → φ x = 0) {y : ℝ} (hy : y < -1 / 2) :
    profilePrimitive φ y = 0 := by
  refine integral_eq_zero_of_far hφs fun x hx => ?_
  have : x < -1 / 2 := by
    rcases Set.mem_uIcc.mp hx with h | h
    · linarith [h.2]
    · linarith [h.2]
  rw [abs_of_neg (by linarith)]; linarith

theorem profilePrimitive_eq_one (hφc : Continuous φ) (hφs : ∀ x, 1 / 2 < |x| → φ x = 0) {y : ℝ}
    (hy : 1 / 2 < y) : profilePrimitive φ y = profilePrimitive φ 1 := by
  have h0 : ∫ x in (1 : ℝ)..y, φ x = 0 := integral_eq_zero_of_far hφs fun x hx => by
    have : 1 / 2 < x := by
      rcases Set.mem_uIcc.mp hx with h | h
      · linarith [h.1]
      · linarith [h.1]
    rw [abs_of_pos (by linarith)]; exact this
  unfold profilePrimitive
  rw [← intervalIntegral.integral_add_adjacent_intervals (hφc.intervalIntegrable (μ := volume) (-1) 1)
    (hφc.intervalIntegrable 1 y), h0, add_zero]

theorem profilePrimitive_nonneg (hφ0 : ∀ x, 0 ≤ φ x) (hφs : ∀ x, 1 / 2 < |x| → φ x = 0) (y : ℝ) :
    0 ≤ profilePrimitive φ y := by
  rcases lt_or_ge y (-1 / 2) with hy | hy
  · rw [profilePrimitive_eq_zero hφs hy]
  · exact intervalIntegral.integral_nonneg (by linarith) fun x _ => hφ0 x

theorem profilePrimitive_le (hφc : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hφs : ∀ x, 1 / 2 < |x| → φ x = 0) (y : ℝ) : profilePrimitive φ y ≤ profilePrimitive φ 1 := by
  rcases lt_or_ge (1 / 2) y with hy | hy
  · rw [profilePrimitive_eq_one hφc hφs hy]
  · have h := intervalIntegral.integral_interval_sub_left
      (hφc.intervalIntegrable (μ := volume) (-1) 1) (hφc.intervalIntegrable (-1) y)
    have h0 : 0 ≤ ∫ x in y..1, φ x := intervalIntegral.integral_nonneg (by linarith) fun x _ => hφ0 x
    unfold profilePrimitive
    linarith

/-- The edge function `e(y) = I 1_{y≥0} − Φ(y)`. -/
def profileEdge (φ : ℝ → ℝ) (y : ℝ) : ℝ :=
  profilePrimitive φ 1 * (if 0 ≤ y then 1 else 0) - profilePrimitive φ y

theorem abs_profileEdge_le (hφc : Continuous φ) (hφ0 : ∀ x, 0 ≤ φ x)
    (hφs : ∀ x, 1 / 2 < |x| → φ x = 0) (y : ℝ) :
    |profileEdge φ y| ≤ profilePrimitive φ 1 * (if |y| ≤ 1 / 2 then 1 else 0) := by
  have h0 := profilePrimitive_nonneg hφ0 hφs y
  have h1 := profilePrimitive_le hφc hφ0 hφs y
  unfold profileEdge
  split_ifs with hy hy' hy'
  · rw [mul_one, abs_of_nonneg (by linarith)]; linarith
  · have hy2 : 1 / 2 < y := by
      rw [abs_of_nonneg hy] at hy'; exact not_le.mp hy'
    rw [profilePrimitive_eq_one (y := y) hφc hφs hy2]
    simp
  · rw [mul_zero, zero_sub, abs_neg, abs_of_nonneg h0, mul_one]; exact h1
  · have hy2 : y < -1 / 2 := by
      rw [abs_of_neg (not_le.mp hy)] at hy'; linarith [not_le.mp hy']
    rw [profilePrimitive_eq_zero (y := y) hφs hy2]
    simp

/-- **Interval integral of a window sum.** -/
theorem integral_windowSum_eq (hφc : Continuous φ) (d : ℕ → ℝ) (N₁ : ℕ) (X X' : ℝ) :
    ∫ L in X..X', ∑ n ∈ range N₁, d n * φ (Real.log n - L) / n =
      ∑ n ∈ range N₁, d n / n *
        (profilePrimitive φ (Real.log n - X) - profilePrimitive φ (Real.log n - X')) := by
  rw [intervalIntegral.integral_finsetSum fun n _ =>
    (Continuous.intervalIntegrable (by fun_prop) _ _)]
  refine Finset.sum_congr rfl fun n _ => ?_
  have e : (fun L => d n * φ (Real.log n - L) / n) = fun L => d n / n * φ (Real.log n - L) := by
    funext L; ring
  rw [e, intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_sub_left
    (fun x => φ x) (Real.log n)]
  unfold profilePrimitive
  rw [intervalIntegral.integral_interval_sub_left (hφc.intervalIntegrable _ _)
    (hφc.intervalIntegrable _ _)]

/-- **Decomposition of a sharp block.** For `1 ≤ N ≤ N'` and `n ≥ 1`,
`I 1_{N≤n<N'} = (Φ(log n − X) − Φ(log n − X')) + e(log n − X) − e(log n − X')`. -/
theorem indicator_block_eq {N N' n : ℕ} (hN : 1 ≤ N) (hNN : N ≤ N') (hn : 1 ≤ n) :
    profilePrimitive φ 1 * (if N ≤ n ∧ n < N' then 1 else 0) =
      (profilePrimitive φ (Real.log n - Real.log N) -
          profilePrimitive φ (Real.log n - Real.log N')) +
        profileEdge φ (Real.log n - Real.log N) - profileEdge φ (Real.log n - Real.log N') := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN'0 : (0 : ℝ) < N' := by exact_mod_cast (show 1 ≤ N' by omega)
  have i1 : (0 ≤ Real.log n - Real.log N) ↔ N ≤ n := by
    rw [sub_nonneg, Real.log_le_log_iff hN0 hn0]; exact_mod_cast Iff.rfl
  have i2 : (0 ≤ Real.log n - Real.log N') ↔ N' ≤ n := by
    rw [sub_nonneg, Real.log_le_log_iff hN'0 hn0]; exact_mod_cast Iff.rfl
  unfold profileEdge
  by_cases h1 : N ≤ n <;> by_cases h2 : N' ≤ n
  · rw [if_pos (i1.mpr h1), if_pos (i2.mpr h2), if_neg (by omega)]; ring
  · rw [if_pos (i1.mpr h1), if_neg (fun h => h2 (i2.mp h)), if_pos ⟨h1, by omega⟩]; ring
  · omega
  · rw [if_neg (fun h => h1 (i1.mp h)), if_neg (fun h => h2 (i2.mp h)), if_neg (by omega)]; ring

end Primitive

/-! ## The local mass of an `o(Λ)` deviation -/

/-- The constant `(2 log 4 + 16) e^{1/2}` of the local mass. -/
def localMassConst : ℝ := (2 * Real.log 4 + 16) * Real.exp (1 / 2)

theorem localMassConst_nonneg : 0 ≤ localMassConst := by
  unfold localMassConst
  have := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
  positivity

/-- **Local mass.** For an `o(Λ)` deviation, `Σ_{|log n − Z| ≤ ½} |d(n)|/n ≤ η (2 log 4 + 16) e^{1/2}`
for all large `Z`. -/
theorem exists_localMass_le {d : ℕ → ℝ} (hd : IsLittleOVonMangoldt d) {η : ℝ} (hη : 0 < η) :
    ∃ Z₀ : ℝ, ∀ Z, Z₀ ≤ Z → ∀ N₁ : ℕ,
      ∑ n ∈ range N₁, |d n| / n * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0) ≤
        η * localMassConst := by
  obtain ⟨P₀, hP₀⟩ := hd η hη
  refine ⟨Real.log (P₀ + 1) + 1, fun Z hZ N₁ => ?_⟩
  have hlogP : 0 ≤ Real.log (P₀ + 1) :=
    Real.log_nonneg (by linarith [(Nat.cast_nonneg P₀ : (0 : ℝ) ≤ P₀)])
  set K : ℕ := ⌊Real.exp (Z + 1 / 2)⌋₊ with hK
  set c : ℝ := Real.exp (-((Z - 1 / 2) / 2)) with hc
  have hpt : ∀ n ∈ range N₁, |d n| / n * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0) ≤
      η * c * ((Λ n : ℝ) / Real.sqrt n * (if n ≤ K then 1 else 0)) := by
    intro n _
    split_ifs with h1 h2 h2
    · rw [mul_one, mul_one]
      have hlow : Z - 1 / 2 ≤ Real.log n := by linarith [(abs_le.mp h1).1]
      have hn1 : 1 ≤ n := by
        by_contra hn
        have : n = 0 := by omega
        rw [this, Nat.cast_zero, Real.log_zero] at hlow
        linarith
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      have hbig : (P₀ : ℝ) + 1 ≤ n := by
        rw [← Real.exp_log hn0, ← Real.exp_log (by positivity : (0 : ℝ) < P₀ + 1)]
        exact Real.exp_le_exp.mpr (by linarith)
      have hdn := hP₀ n (by exact_mod_cast (show (P₀ : ℝ) ≤ n by linarith))
      have hsq : Real.exp ((Z - 1 / 2) / 2) ≤ Real.sqrt n := by
        rw [Real.le_sqrt (by positivity) hn0.le, ← Real.exp_log hn0, ← Real.exp_nat_mul]
        exact Real.exp_le_exp.mpr (by push_cast; linarith)
      have hs0 : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
      have hinv : (n : ℝ)⁻¹ ≤ c * (Real.sqrt n)⁻¹ := by
        have hnn : (n : ℝ) = Real.sqrt n * Real.sqrt n := (Real.mul_self_sqrt hn0.le).symm
        rw [hc, Real.exp_neg, ← mul_inv]
        calc (n : ℝ)⁻¹ = (Real.sqrt n * Real.sqrt n)⁻¹ := by rw [← hnn]
          _ ≤ (Real.exp ((Z - 1 / 2) / 2) * Real.sqrt n)⁻¹ :=
              inv_anti₀ (by positivity) (mul_le_mul_of_nonneg_right hsq hs0.le)
      rw [div_eq_mul_inv, div_eq_mul_inv]
      calc |d n| * (n : ℝ)⁻¹ ≤ (η * Λ n) * (c * (Real.sqrt n)⁻¹) :=
            mul_le_mul hdn hinv (by positivity) (by positivity)
        _ = η * c * (Λ n * (Real.sqrt n)⁻¹) := by ring
    · exfalso
      have hup : Real.log n ≤ Z + 1 / 2 := by linarith [(abs_le.mp h1).2]
      have hn1 : 1 ≤ n := by
        by_contra hn
        have : n = 0 := by omega
        have hlow : Z - 1 / 2 ≤ Real.log n := by linarith [(abs_le.mp h1).1]
        rw [this, Nat.cast_zero, Real.log_zero] at hlow
        linarith
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      exact h2 (Nat.le_floor (by rw [← Real.exp_log hn0]; exact Real.exp_le_exp.mpr hup))
    · rw [mul_zero]
      have : 0 ≤ (Λ n : ℝ) / Real.sqrt n * 1 := by
        have := vonMangoldt_nonneg (n := n); positivity
      positivity
    · rw [mul_zero, mul_zero, mul_zero]
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  have hsub : ∑ n ∈ range N₁, (Λ n : ℝ) / Real.sqrt n * (if n ≤ K then 1 else 0) ≤
      ∑ n ∈ range (K + 1), (Λ n : ℝ) / Real.sqrt n := by
    rw [← Finset.sum_filter_add_sum_filter_not (range N₁) (fun n => n ≤ K)]
    have h2 : ∑ n ∈ (range N₁).filter (fun n => ¬ n ≤ K),
        (Λ n : ℝ) / Real.sqrt n * (if n ≤ K then 1 else 0) = 0 :=
      Finset.sum_eq_zero fun n hn => by rw [if_neg (Finset.mem_filter.mp hn).2, mul_zero]
    rw [h2, add_zero]
    calc ∑ n ∈ (range N₁).filter (fun n => n ≤ K),
          (Λ n : ℝ) / Real.sqrt n * (if n ≤ K then 1 else 0)
        = ∑ n ∈ (range N₁).filter (fun n => n ≤ K), (Λ n : ℝ) / Real.sqrt n :=
          Finset.sum_congr rfl fun n hn => by rw [if_pos (Finset.mem_filter.mp hn).2, mul_one]
      _ ≤ ∑ n ∈ range (K + 1), (Λ n : ℝ) / Real.sqrt n :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun n hn => Finset.mem_range.mpr (by have := (Finset.mem_filter.mp hn).2; omega))
            fun n _ _ => by have := vonMangoldt_nonneg (n := n); positivity
  have hK1 : 1 ≤ K := Nat.le_floor (by
    push_cast
    have : (1 : ℝ) ≤ Real.exp (Z + 1 / 2) := Real.one_le_exp (by linarith)
    exact this)
  have hcheb := sum_range_vonMangoldt_div_sqrt_le hK1
  have hsqK : Real.sqrt K ≤ Real.exp ((Z + 1 / 2) / 2) := by
    rw [Real.sqrt_le_left (by positivity), ← Real.exp_nat_mul]
    push_cast
    rw [show (2 : ℝ) * ((Z + 1 / 2) / 2) = Z + 1 / 2 by ring]
    exact Nat.floor_le (by positivity)
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  have hlog4 := Real.log_nonneg (show (1 : ℝ) ≤ 4 by norm_num)
  have hce : c * Real.exp ((Z + 1 / 2) / 2) = Real.exp (1 / 2) := by
    rw [hc, ← Real.exp_add]; congr 1; ring
  calc η * c * ∑ n ∈ range N₁, (Λ n : ℝ) / Real.sqrt n * (if n ≤ K then 1 else 0)
      ≤ η * c * ((2 * Real.log 4 + 16) * Real.sqrt K) :=
        mul_le_mul_of_nonneg_left (hsub.trans hcheb) (by positivity)
    _ ≤ η * c * ((2 * Real.log 4 + 16) * Real.exp ((Z + 1 / 2) / 2)) := by gcongr
    _ = η * localMassConst := by
        rw [localMassConst, ← hce]; ring

/-! ## The harmonic windows of a Weil-positive sequence, at every scale -/

theorem exp_neg_half_le_inv_sq (L : ℝ) (hL : 0 < L) : Real.exp (-(L / 2)) ≤ 8 * (L ^ 2)⁻¹ := by
  have h := Real.pow_div_factorial_le_exp (L / 2) (by positivity) 2
  norm_num [Nat.factorial] at h
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have h1 : 0 < Real.exp (L / 2) := Real.exp_pos _
  rw [inv_mul_le_iff₀ h1]
  nlinarith

theorem exp_neg_sqrt_div_le_inv_sq {c : ℝ} (hc : 0 < c) {L : ℝ} (hL : 0 < L) :
    Real.exp (-(Real.sqrt L / c)) ≤ 24 * c ^ 4 * (L ^ 2)⁻¹ := by
  have h := Real.pow_div_factorial_le_exp (Real.sqrt L / c) (by positivity) 4
  have e : (Real.sqrt L / c) ^ 4 = L ^ 2 / c ^ 4 := by
    rw [div_pow, show (4 : ℕ) = 2 * 2 by norm_num, pow_mul, Real.sq_sqrt hL.le]
  rw [e] at h
  norm_num [Nat.factorial] at h
  rw [Real.exp_neg, ← div_eq_mul_inv, le_div_iff₀ (by positivity)]
  have h1 : 0 < Real.exp (Real.sqrt L / c) := Real.exp_pos _
  rw [inv_mul_le_iff₀ h1]
  have hc4 : 0 < c ^ 4 := by positivity
  rw [div_div, div_le_iff₀ (by positivity)] at h
  nlinarith

/-- **A continuous profile with `O(L^{−2})` harmonic windows.** There is one continuous profile
`φ ≥ 0`, supported in `[−½, ½]`, with `∫_{−1}^1 φ > 0`, such that every full-cone Weil-positive
`lam` has `|Σ_{n<N} d(n) φ(log n − L)/n| ≤ C/L²` for all real `L ≥ L₁` and `N ≥ e^{L+1}`. -/
theorem exists_profile_window_le_inv_sq :
    ∃ (φ : ℝ → ℝ) (C L₁ : ℝ), Continuous φ ∧ (∀ x, 0 ≤ φ x) ∧ (∀ x, 1 / 2 < |x| → φ x = 0) ∧
      0 < profilePrimitive φ 1 ∧ 1 ≤ L₁ ∧ 0 ≤ C ∧
      ∀ lam : ℕ → ℝ, WeilPositiveFull lam → ∀ L, L₁ ≤ L → ∀ N : ℕ, Real.exp (L + 1) ≤ N →
        |∑ n ∈ range N, coneDeviation lam n * φ (Real.log n - L) / n| ≤ C * (L ^ 2)⁻¹ := by
  set g := narrowG 0 with hgdef
  have hg := contDiff_narrowG 0
  have hgc := hasCompactSupport_narrowG 0
  have hsupp := narrowG_supp 0
  have hg0 : ∀ u, 0 ≤ g u := fun u => (narrowBump 0).nonneg
  obtain ⟨Kρ, Hρ, hK0, hH0, hK, hH, hcont⟩ := exists_autoCorr_constants hg hgc
  set φ := harmonicProfile g with hφdef
  have hφ0 : ∀ x, 0 ≤ φ x := fun x => mul_nonneg (autoCorr_nonneg_of_nonneg hg0 x) (Real.exp_pos _).le
  have hφs : ∀ x, 1 / 2 < |x| → φ x = 0 := fun x hx => by
    rw [hφdef, harmonicProfile, autoCorr_eq_zero hsupp hx, zero_mul]
  have hφc : Continuous φ := by
    rw [hφdef]; unfold harmonicProfile; fun_prop
  have hφ00 : 0 < φ 0 := by
    rw [hφdef, harmonicProfile, zero_div, Real.exp_zero, mul_one]
    exact autoCorr_narrowG_zero_pos 0
  obtain ⟨η, hη, hηφ⟩ := Metric.continuousAt_iff.mp hφc.continuousAt (φ 0 / 2) (by positivity)
  set η' : ℝ := min (η / 2) (1 / 2) with hη'
  have hη'0 : 0 < η' := lt_min (by linarith) (by norm_num)
  have hη'1 : η' ≤ 1 / 2 := min_le_right _ _
  have hpos : ∀ x ∈ Ioo (-η') η', 0 < φ x := by
    intro x hx
    have hd : dist x 0 < η := by
      rw [Real.dist_eq, sub_zero, abs_lt]
      constructor <;> linarith [hx.1, hx.2, min_le_left (η / 2) (1 / 2)]
    have := hηφ hd
    rw [Real.dist_eq] at this
    linarith [neg_abs_le (φ x - φ 0)]
  have hI : 0 < profilePrimitive φ 1 := by
    unfold profilePrimitive
    rw [← intervalIntegral.integral_add_adjacent_intervals (hφc.intervalIntegrable (-1) (-η'))
      (hφc.intervalIntegrable (-η') 1), ← intervalIntegral.integral_add_adjacent_intervals
      (hφc.intervalIntegrable (-η') η') (hφc.intervalIntegrable η' 1)]
    have h1 : 0 ≤ ∫ x in (-1 : ℝ)..(-η'), φ x :=
      intervalIntegral.integral_nonneg (by linarith) fun x _ => hφ0 x
    have h2 : 0 < ∫ x in (-η')..η', φ x :=
      intervalIntegral.intervalIntegral_pos_of_pos_on (hφc.intervalIntegrable _ _) hpos
        (by linarith)
    have h3 : 0 ≤ ∫ x in η'..1, φ x :=
      intervalIntegral.integral_nonneg (by linarith) fun x _ => hφ0 x
    linarith
  obtain ⟨C, L₀, hC0, hC⟩ := exists_abs_windowSum_sub_vonMangoldt_le hg hgc hsupp
  set c : ℝ := 1920000 with hc
  refine ⟨φ, C * (8 + 24 * c ^ 4), max L₀ 1, hφc, hφ0, hφs, hI, le_max_right _ _,
    by positivity, fun lam hW L hL N hN => ?_⟩
  have hL1 : 1 ≤ L := (le_max_right _ _).trans hL
  have hL0 : 0 < L := by linarith
  have hid := sum_harmonicProfile_eq_windowSum hg hgc hsupp
    (fun n => lam n - ArithmeticFunction.vonMangoldt n) hL1 hN
  have hcd : ∀ n, coneDeviation lam n * φ (Real.log n - L) / n =
      (if 2 ≤ n then lam n - ArithmeticFunction.vonMangoldt n else 0) *
        harmonicProfile g (Real.log n - L) / n := fun n => rfl
  simp_rw [hcd]
  rw [hid, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hw := hC lam hW L ((le_max_left _ _).trans hL)
  have e1 : Real.exp (-(L / 2)) * Real.exp (L / 2) = 1 := by
    rw [← Real.exp_add]; simp
  have hA := exp_neg_half_le_inv_sq L hL0
  have hB := exp_neg_sqrt_div_le_inv_sq (c := c) (by positivity) hL0
  calc Real.exp (-(L / 2)) *
        |windowSum hg hgc hsupp (fun n => lam n - ArithmeticFunction.vonMangoldt n) L|
      ≤ Real.exp (-(L / 2)) * (C * (1 + Real.exp (L / 2) * Real.exp (-(Real.sqrt L / c)))) :=
        mul_le_mul_of_nonneg_left hw (Real.exp_pos _).le
    _ = C * (Real.exp (-(L / 2)) + (Real.exp (-(L / 2)) * Real.exp (L / 2)) *
          Real.exp (-(Real.sqrt L / c))) := by ring
    _ ≤ C * (8 * (L ^ 2)⁻¹ + 1 * (24 * c ^ 4 * (L ^ 2)⁻¹)) := by
        rw [e1]; gcongr
    _ = C * (8 + 24 * c ^ 4) * (L ^ 2)⁻¹ := by ring

/-! ## Convergence -/

theorem integral_const_div_sq_le {C X X' : ℝ} (hC : 0 ≤ C) (hX : 0 < X) (hXX : X ≤ X') :
    ∫ L in X..X', C * (L ^ 2)⁻¹ ≤ C / X := by
  have h0 : (0 : ℝ) ∉ uIcc X X' := by
    rw [Set.uIcc_of_le hXX]; intro h; linarith [h.1]
  have e : (fun L : ℝ => C * (L ^ 2)⁻¹) = fun L => C * L ^ (-2 : ℤ) := by
    funext L; rw [zpow_neg, zpow_two, sq]
  rw [e, intervalIntegral.integral_const_mul, integral_zpow (Or.inr ⟨by norm_num, h0⟩)]
  have hX' : 0 < X' := by linarith
  have e2 : (X' ^ ((-2 : ℤ) + 1) - X ^ ((-2 : ℤ) + 1)) / (((-2 : ℤ) : ℝ) + 1) = X⁻¹ - X'⁻¹ := by
    rw [show ((-2 : ℤ) + 1) = -1 by norm_num, zpow_neg_one, zpow_neg_one]; push_cast; ring
  rw [e2, div_eq_mul_inv]
  have := inv_pos.mpr hX'
  nlinarith

/-- **Convergence of the harmonic deviation series, local-mass form.** If `lam` is full-cone
Weil-positive and the local harmonic mass of `d = lam − Λ` tends to `0`, then `Σ_{n<N} d(n)/n`
converges. -/
theorem exists_tendsto_sum_coneDeviation_div_of_localMass {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hloc : ∀ η : ℝ, 0 < η → ∃ Z₀ : ℝ, ∀ Z, Z₀ ≤ Z → ∀ N₁ : ℕ,
      ∑ n ∈ range N₁, |coneDeviation lam n| / n * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0) ≤
        η * localMassConst) :
    ∃ Y : ℝ, Tendsto (fun N : ℕ => ∑ n ∈ range N, coneDeviation lam n / n) atTop (𝓝 Y) := by
  obtain ⟨φ, C, L₁, hφc, hφ0, hφs, hI, hL₁, hC0, hwin⟩ := exists_profile_window_le_inv_sq
  set I := profilePrimitive φ 1 with hIdef
  set d := coneDeviation lam with hddef
  have hd0 : d 0 = 0 := by simp [hddef, coneDeviation]
  set s : ℕ → ℝ := fun N => ∑ n ∈ range N, d n / n with hs
  refine cauchySeq_tendsto_of_complete (Metric.cauchySeq_iff'.mpr fun ε hε => ?_)
  have hCl := localMassConst_nonneg
  set η : ℝ := ε / (4 * (localMassConst + 1)) with hη
  have hη0 : 0 < η := by positivity
  have hηC : 2 * (η * localMassConst) < ε / 2 := by
    rw [hη]
    have h1 : 0 < localMassConst + 1 := by linarith
    rw [div_mul_eq_mul_div, mul_div_assoc', div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  obtain ⟨Z₀, hZ₀⟩ := hloc η hη0
  set X₀ : ℝ := max (max L₁ Z₀) (2 * C / (I * ε) + 1) with hX₀
  refine ⟨⌈Real.exp X₀⌉₊, fun N' hN' => ?_⟩
  set N := ⌈Real.exp X₀⌉₊ with hNdef
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (by
    rw [hNdef]; exact (Nat.ceil_pos.mpr (Real.exp_pos _)).ne')
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN1
  have hN'0 : (0 : ℝ) < N' := by exact_mod_cast (show 1 ≤ N' by omega)
  set X := Real.log N with hX
  set X' := Real.log N' with hX'
  have hXX₀ : X₀ ≤ X := by
    rw [hX, Real.le_log_iff_exp_le hN0]; exact Nat.le_ceil _
  have hXX' : X ≤ X' := Real.log_le_log hN0 (by exact_mod_cast hN')
  have hL₁X : L₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXX₀
  have hZX : Z₀ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXX₀
  have hZX' : Z₀ ≤ X' := hZX.trans hXX'
  have hX0 : 0 < X := by linarith
  set N₁ := ⌈Real.exp (X' + 1)⌉₊ with hN₁
  have hN'N₁ : N' ≤ N₁ := by
    have : (N' : ℝ) ≤ Real.exp (X' + 1) := by
      rw [Real.exp_add, hX', Real.exp_log hN'0]
      nlinarith [Real.add_one_le_exp (1 : ℝ)]
    exact_mod_cast this.trans (Nat.le_ceil _)
  -- the block identity
  have hblock : I * (s N' - s N) =
      (∑ n ∈ range N₁, d n / n * (profilePrimitive φ (Real.log n - X) -
          profilePrimitive φ (Real.log n - X'))) +
        ∑ n ∈ range N₁, d n / n * profileEdge φ (Real.log n - X) -
          ∑ n ∈ range N₁, d n / n * profileEdge φ (Real.log n - X') := by
    have hsN : s N' - s N = ∑ n ∈ range N₁, d n / n * (if N ≤ n ∧ n < N' then 1 else 0) := by
      rw [hs]
      simp only
      rw [← Finset.sum_Ico_eq_sub _ hN']
      simp only [mul_ite, mul_one, mul_zero]
      rw [← Finset.sum_filter]
      congr 1
      ext n
      simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range]
      constructor
      · rintro ⟨h1, h2⟩; exact ⟨by omega, h1, h2⟩
      · rintro ⟨-, h1, h2⟩; exact ⟨h1, h2⟩
    rw [hsN, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hd0]; simp
    rw [mul_left_comm, indicator_block_eq hN1 hN' hn]
    ring
  -- the window integral
  have hint : |∑ n ∈ range N₁, d n / n * (profilePrimitive φ (Real.log n - X) -
      profilePrimitive φ (Real.log n - X'))| ≤ C / X := by
    rw [← integral_windowSum_eq hφc d N₁ X X']
    have hb := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) hXX'
      (g := fun L => C * (L ^ 2)⁻¹) (Eventually.of_forall fun L hL => by
        rw [Real.norm_eq_abs]
        refine hwin lam hW L (hL₁X.trans hL.1.le) N₁ ?_
        refine le_trans (Real.exp_le_exp.mpr (by linarith [hL.2])) (Nat.le_ceil _))
      (ContinuousOn.intervalIntegrable (continuousOn_const.mul (ContinuousOn.inv₀
        (continuousOn_pow 2) fun L hL => by
          rw [Set.uIcc_of_le hXX'] at hL
          exact pow_ne_zero 2 (by linarith [hL.1]))))
    rw [Real.norm_eq_abs] at hb
    exact hb.trans (integral_const_div_sq_le hC0 hX0 hXX')
  -- the edges
  have hedge : ∀ Z, Z₀ ≤ Z →
      |∑ n ∈ range N₁, d n / n * profileEdge φ (Real.log n - Z)| ≤ I * (η * localMassConst) := by
    intro Z hZ
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ n ∈ range N₁, |d n / n * profileEdge φ (Real.log n - Z)|
        ≤ ∑ n ∈ range N₁, I * (|d n| / n * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0)) := by
          refine Finset.sum_le_sum fun n _ => ?_
          rw [abs_mul, abs_div, Nat.abs_cast]
          have h := abs_profileEdge_le hφc hφ0 hφs (Real.log n - Z)
          calc |d n| / n * |profileEdge φ (Real.log n - Z)|
              ≤ |d n| / n * (I * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0)) :=
                mul_le_mul_of_nonneg_left h (by positivity)
            _ = _ := by ring
      _ = I * ∑ n ∈ range N₁, |d n| / n * (if |Real.log n - Z| ≤ 1 / 2 then 1 else 0) := by
          rw [Finset.mul_sum]
      _ ≤ I * (η * localMassConst) := mul_le_mul_of_nonneg_left (hZ₀ Z hZ N₁) hI.le
  have he1 := hedge X hZX
  have he2 := hedge X' hZX'
  have hCX : C / X < I * (ε / 2) := by
    have hXb : 2 * C / (I * ε) + 1 ≤ X := (le_max_right _ _).trans hXX₀
    rw [div_lt_iff₀ hX0]
    have h1 : 2 * C / (I * ε) < X := by linarith
    rw [div_lt_iff₀ (mul_pos hI hε)] at h1
    nlinarith
  have htot : I * |s N' - s N| < I * ε := by
    rw [← abs_of_pos hI, ← abs_mul, abs_of_pos hI, hblock]
    have := abs_add_three (∑ n ∈ range N₁, d n / n * (profilePrimitive φ (Real.log n - X) -
      profilePrimitive φ (Real.log n - X')))
      (∑ n ∈ range N₁, d n / n * profileEdge φ (Real.log n - X))
      (-∑ n ∈ range N₁, d n / n * profileEdge φ (Real.log n - X'))
    rw [abs_neg, ← sub_eq_add_neg] at this
    have hIη : I * (η * localMassConst) + I * (η * localMassConst) < I * (ε / 2) := by
      rw [← mul_add]
      exact mul_lt_mul_of_pos_left (by linarith) hI
    linarith
  rw [Real.dist_eq]
  exact lt_of_mul_lt_mul_left htot hI.le

/-- **Convergence of the harmonic deviation series.** If `lam` is full-cone Weil-positive and
`d = lam − Λ` is `o(Λ)`, then `Σ_{n<N} d(n)/n` converges. -/
theorem exists_tendsto_sum_coneDeviation_div {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hd : IsLittleOVonMangoldt (coneDeviation lam)) :
    ∃ Y : ℝ, Tendsto (fun N : ℕ => ∑ n ∈ range N, coneDeviation lam n / n) atTop (𝓝 Y) :=
  exists_tendsto_sum_coneDeviation_div_of_localMass hW fun _ hη => exists_localMass_le hd hη

end RHTower.WeilOneSided
