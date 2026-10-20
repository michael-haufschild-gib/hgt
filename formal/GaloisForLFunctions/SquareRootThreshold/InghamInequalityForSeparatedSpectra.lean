import GaloisForLFunctions.SquareRootThreshold.WeilFormDeterminesTheConfiguration

/-!
# Ingham's inequality for separated real spectra

For real frequencies `γ_j` with pairwise gaps at least `g`, and `T` with `Tg > π`,

`C(T, g) Σ_j |c_j|² ≤ ∫_{−T}^{T} |Σ_j c_j e^{iγ_j t}|² dt`,  `C(T, g) > 0`

(`ingham_inequality`, `inghamConst_pos`). At `Tg = π` the off-diagonal mass of the cosine
kernel exactly balances its diagonal.

* **Kernel** (`inghamKernel_eq`). With `a = π/(2T)`, the weight `cos(at)` on `[−T, T]` has transform
  `K(x) = ∫_{−T}^{T} cos(at) e^{ixt} dt = cos(xT) (1/(x + a) − 1/(x − a))`. So `K(0) = 2/a` and
  `|K(x)| ≤ 2a/(x² − a²)` for `|x| > a`.
* **Quadratic form** (`integral_cos_mul_normSq_expSum`). `∫ cos(at)|f|² = Re Σ_{j,l} c_j c̄_l K(γ_j − γ_l)`,
  and `cos(at) ≤ 1` bounds it by `∫ |f|²`.
* **Off-diagonal sum** (`sum_offDiag_le_two_tsum`). On each side of `γ_j` the `n`-th neighbour lies
  at distance at least `ng`, so `Σ_{l ≠ j} |K(γ_j − γ_l)| ≤ (2/a) · 2 Σ_{n ≥ 1} 1/(b²n² − 1)` with
  `b = g/a = 2Tg/π`.
* **Telescoping** (`hasSum_two_div_four_sq_sub_one`). `Σ_{n ≥ 1} 2/(4n² − 1) = 1`, by
  `2/(4n² − 1) = 1/(2n − 1) − 1/(2n + 1)`. For `b > 2`, that is `Tg > π`, the off-diagonal sum is
  strictly smaller than the diagonal `K(0) = 2/a`.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

/-- `∫_{−T}^{T} e^{iμt} dt = 2 sin(μT)/μ`. -/
theorem integral_exp_I_mul_symm {μ : ℝ} (hμ : μ ≠ 0) (T : ℝ) :
    ∫ t in -T..T, cexp (I * μ * t) = ((2 * Real.sin (μ * T) / μ : ℝ) : ℂ) := by
  have hc : (I * μ : ℂ) ≠ 0 := mul_ne_zero I_ne_zero (by exact_mod_cast hμ)
  rw [integral_exp_mul_complex hc]
  have h1 : cexp (I * μ * T) = Complex.cos (μ * T) + Complex.sin (μ * T) * I := by
    rw [← Complex.exp_mul_I]
    ring_nf
  have h2 : cexp (I * μ * ((-T : ℝ) : ℂ)) = Complex.cos (μ * T) - Complex.sin (μ * T) * I := by
    rw [show I * (μ : ℂ) * ((-T : ℝ) : ℂ) = (-((μ : ℂ) * T)) * I by push_cast; ring,
      Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
    ring
  rw [h1, h2]
  push_cast
  field_simp
  ring

/-- The Ingham kernel `K_T(x) = ∫_{−T}^{T} cos(πt/(2T)) e^{ixt} dt`. -/
def inghamKernel (T x : ℝ) : ℂ :=
  ∫ t in -T..T, ((Real.cos (π / (2 * T) * t) : ℝ) : ℂ) * cexp (I * x * t)

/-- **The kernel in closed form.** With `a = π/(2T)`,
`K_T(x) = cos(xT) (1/(x + a) − 1/(x − a))` for `x ≠ ±a`. -/
theorem inghamKernel_eq {T x : ℝ} (hT : 0 < T) (hx1 : x + π / (2 * T) ≠ 0)
    (hx2 : x - π / (2 * T) ≠ 0) :
    inghamKernel T x =
      ((Real.cos (x * T) * (1 / (x + π / (2 * T)) - 1 / (x - π / (2 * T))) : ℝ) : ℂ) := by
  set a := π / (2 * T) with ha
  have hsplit : ∀ t : ℝ, ((Real.cos (a * t) : ℝ) : ℂ) * cexp (I * x * t) =
      (cexp (I * ((x + a : ℝ) : ℂ) * t) + cexp (I * ((x - a : ℝ) : ℂ) * t)) / 2 := by
    intro t
    rw [Complex.ofReal_cos, Complex.cos,
      show cexp (I * ((x + a : ℝ) : ℂ) * t) = cexp (((a * t : ℝ) : ℂ) * I) * cexp (I * x * t) by
        rw [← Complex.exp_add]; congr 1; push_cast; ring,
      show cexp (I * ((x - a : ℝ) : ℂ) * t) = cexp (-((a * t : ℝ) : ℂ) * I) * cexp (I * x * t) by
        rw [← Complex.exp_add]; congr 1; push_cast; ring]
    ring
  have hint : ∀ μ : ℝ, IntervalIntegrable (fun t : ℝ => cexp (I * (μ : ℂ) * t)) volume (-T) T :=
    fun μ => (by fun_prop : Continuous fun t : ℝ => cexp (I * (μ : ℂ) * t)).intervalIntegrable _ _
  rw [inghamKernel, ← ha]
  simp_rw [hsplit]
  rw [intervalIntegral.integral_div, intervalIntegral.integral_add (hint _) (hint _),
    integral_exp_I_mul_symm hx1 T, integral_exp_I_mul_symm hx2 T]
  have haT : a * T = π / 2 := by rw [ha]; field_simp
  have hs1 : Real.sin ((x + a) * T) = Real.cos (x * T) := by
    rw [add_mul, haT, Real.sin_add_pi_div_two]
  have hs2 : Real.sin ((x - a) * T) = -Real.cos (x * T) := by
    rw [sub_mul, haT, Real.sin_sub_pi_div_two]
  rw [hs1, hs2]
  push_cast
  ring

theorem inghamKernel_zero {T : ℝ} (hT : 0 < T) : inghamKernel T 0 = ((4 * T / π : ℝ) : ℂ) := by
  have ha : 0 < π / (2 * T) := by positivity
  rw [inghamKernel_eq hT (by rw [zero_add]; exact ha.ne') (by rw [zero_sub]; exact neg_ne_zero.mpr ha.ne')]
  congr 1
  rw [zero_mul, Real.cos_zero, one_mul]
  field_simp
  ring

/-- `|K_T(x)| ≤ 2a/(x² − a²)` for `|x| > a = π/(2T)`. -/
theorem norm_inghamKernel_le {T x : ℝ} (hT : 0 < T) (hx : π / (2 * T) < |x|) :
    ‖inghamKernel T x‖ ≤ 2 * (π / (2 * T)) / (x ^ 2 - (π / (2 * T)) ^ 2) := by
  set a := π / (2 * T) with ha
  have ha0 : 0 < a := by positivity
  have hxa : a ^ 2 < x ^ 2 := by
    have := sq_lt_sq' (by linarith [abs_nonneg x, neg_abs_le x]) hx
    rwa [sq_abs] at this
  have h1 : x + a ≠ 0 := fun h => by
    have : x = -a := by linarith
    rw [this, abs_neg, abs_of_pos ha0] at hx; linarith
  have h2 : x - a ≠ 0 := fun h => by
    have : x = a := by linarith
    rw [this, abs_of_pos ha0] at hx; linarith
  rw [inghamKernel_eq hT h1 h2, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have hd : x ^ 2 - a ^ 2 ≠ 0 := by linarith
  have hid : 1 / (x + a) - 1 / (x - a) = -(2 * a / (x ^ 2 - a ^ 2)) := by
    rw [show x ^ 2 - a ^ 2 = (x + a) * (x - a) by ring]
    field_simp
    ring
  rw [hid, abs_neg, abs_of_pos (div_pos (by positivity : (0 : ℝ) < 2 * a)
    (by linarith : (0 : ℝ) < x ^ 2 - a ^ 2))]
  exact mul_le_of_le_one_left (by positivity) (Real.abs_cos_le_one _)

/-- **The weighted mean square as a quadratic form.**
`∫_{−T}^{T} cos(πt/(2T)) |Σ_j c_j e^{iγ_j t}|² dt = Re Σ_{j,l} c_j c̄_l K_T(γ_j − γ_l)`. -/
theorem integral_cos_mul_normSq_expSum {ι : Type*} [Fintype ι] (γ : ι → ℝ) (c : ι → ℂ) (T : ℝ) :
    ∫ t in -T..T, Real.cos (π / (2 * T) * t) * ‖∑ j, c j * cexp (I * γ j * t)‖ ^ 2 =
      (∑ j, ∑ l, c j * conj (c l) * inghamKernel T (γ j - γ l)).re := by
  set G : ℝ → ℂ := fun t => ∑ j, ∑ l, c j * conj (c l) *
    (((Real.cos (π / (2 * T) * t) : ℝ) : ℂ) * cexp (I * ((γ j - γ l : ℝ) : ℂ) * t)) with hG
  have hpt : ∀ t : ℝ, Real.cos (π / (2 * T) * t) * ‖∑ j, c j * cexp (I * γ j * t)‖ ^ 2 =
      (G t).re := by
    intro t
    have hn : ‖∑ j, c j * cexp (I * γ j * t)‖ ^ 2 =
        ((∑ j, c j * cexp (I * γ j * t)) * conj (∑ j, c j * cexp (I * γ j * t))).re := by
      rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    rw [hn, ← Complex.re_ofReal_mul, hG, map_sum, Finset.sum_mul, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, ← Complex.exp_conj, map_mul, map_mul, Complex.conj_I, Complex.conj_ofReal,
      Complex.conj_ofReal]
    rw [show cexp (I * ((γ j - γ l : ℝ) : ℂ) * t) =
      cexp (I * γ j * t) * cexp (-I * γ l * t) by rw [← Complex.exp_add]; congr 1; push_cast; ring]
    ring
  have hcont : Continuous G := by rw [hG]; fun_prop
  rw [intervalIntegral.integral_congr (fun t _ => hpt t),
    show (∫ t in -T..T, (G t).re) = (∫ t in -T..T, G t).re from
      intervalIntegral.intervalIntegral_re (hcont.intervalIntegrable _ _), hG]
  congr 1
  rw [intervalIntegral.integral_finsetSum fun j _ =>
    (by fun_prop : Continuous fun t : ℝ => ∑ l, c j * conj (c l) *
      (((Real.cos (π / (2 * T) * t) : ℝ) : ℂ) *
        cexp (I * ((γ j - γ l : ℝ) : ℂ) * t))).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [intervalIntegral.integral_finsetSum fun l _ =>
    (by fun_prop : Continuous fun t : ℝ => c j * conj (c l) *
      (((Real.cos (π / (2 * T) * t) : ℝ) : ℂ) *
        cexp (I * ((γ j - γ l : ℝ) : ℂ) * t))).intervalIntegrable _ _]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [intervalIntegral.integral_const_mul, inghamKernel]

/-- **Telescoping.** `Σ_{n ≥ 1} 2/(4n² − 1) = 1`. -/
theorem hasSum_two_div_four_sq_sub_one :
    HasSum (fun n : ℕ => (2 : ℝ) / (4 * ((n : ℝ) + 1) ^ 2 - 1)) 1 := by
  have hterm : ∀ n : ℕ, (2 : ℝ) / (4 * ((n : ℝ) + 1) ^ 2 - 1) =
      1 / (2 * (n : ℝ) + 1) - 1 / (2 * ((n + 1 : ℕ) : ℝ) + 1) := by
    intro n
    push_cast
    have h1 : (0 : ℝ) < 2 * n + 1 := by positivity
    have h2 : (0 : ℝ) < 2 * (n + 1) + 1 := by positivity
    rw [show 4 * ((n : ℝ) + 1) ^ 2 - 1 = (2 * n + 1) * (2 * (n + 1) + 1) by ring]
    field_simp
    ring
  have hpart : ∀ N : ℕ, ∑ n ∈ Finset.range N, (2 : ℝ) / (4 * ((n : ℝ) + 1) ^ 2 - 1) =
      1 - 1 / (2 * (N : ℝ) + 1) := by
    intro N
    simp_rw [hterm]
    rw [Finset.sum_range_sub' (fun n : ℕ => 1 / (2 * (n : ℝ) + 1)) N]
    simp
  refine (hasSum_iff_tendsto_nat_of_nonneg (fun n => ?_) 1).mpr ?_
  · have : (0 : ℝ) < 4 * ((n : ℝ) + 1) ^ 2 - 1 := by nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    positivity
  · simp_rw [hpart]
    have h : Tendsto (fun N : ℕ => 1 / (2 * (N : ℝ) + 1)) atTop (𝓝 0) := by
      refine tendsto_const_nhds.div_atTop ?_
      exact tendsto_atTop_add_const_right _ 1
        (tendsto_natCast_atTop_atTop.const_mul_atTop two_pos)
    simpa using tendsto_const_nhds.sub h

/-- For `b > 2`: `Σ_{n ≥ 1} 2/(b²n² − 1) < 1`. -/
theorem tsum_two_div_sq_sub_one_lt_one {b : ℝ} (hb : 2 < b) :
    Summable (fun n : ℕ => (2 : ℝ) / (b ^ 2 * ((n : ℝ) + 1) ^ 2 - 1)) ∧
      ∑' n : ℕ, (2 : ℝ) / (b ^ 2 * ((n : ℝ) + 1) ^ 2 - 1) < 1 := by
  have hpos : ∀ n : ℕ, (0 : ℝ) < 4 * ((n : ℝ) + 1) ^ 2 - 1 := fun n => by
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hle : ∀ n : ℕ, (2 : ℝ) / (b ^ 2 * ((n : ℝ) + 1) ^ 2 - 1) ≤
      2 / (4 * ((n : ℝ) + 1) ^ 2 - 1) := fun n => by
    have h4 : 4 * ((n : ℝ) + 1) ^ 2 ≤ b ^ 2 * ((n : ℝ) + 1) ^ 2 := by
      have : (4 : ℝ) ≤ b ^ 2 := by nlinarith
      nlinarith [sq_nonneg ((n : ℝ) + 1)]
    exact div_le_div_of_nonneg_left (by norm_num) (hpos n) (by linarith)
  have hnn : ∀ n : ℕ, (0 : ℝ) ≤ 2 / (b ^ 2 * ((n : ℝ) + 1) ^ 2 - 1) := fun n => by
    have h4 : 4 * ((n : ℝ) + 1) ^ 2 ≤ b ^ 2 * ((n : ℝ) + 1) ^ 2 := by
      have : (4 : ℝ) ≤ b ^ 2 := by nlinarith
      nlinarith [sq_nonneg ((n : ℝ) + 1)]
    have := hpos n
    exact div_nonneg (by norm_num) (by linarith)
  have hs := hasSum_two_div_four_sq_sub_one
  have hsum : Summable (fun n : ℕ => (2 : ℝ) / (b ^ 2 * ((n : ℝ) + 1) ^ 2 - 1)) :=
    Summable.of_nonneg_of_le hnn hle hs.summable
  refine ⟨hsum, ?_⟩
  have hlt : (2 : ℝ) / (b ^ 2 * (((0 : ℕ) : ℝ) + 1) ^ 2 - 1) <
      2 / (4 * (((0 : ℕ) : ℝ) + 1) ^ 2 - 1) := by
    simp only [Nat.cast_zero, zero_add, one_pow, mul_one]
    have : (4 : ℝ) < b ^ 2 := by nlinarith
    exact div_lt_div_of_pos_left (by norm_num) (by norm_num) (by linarith)
  calc ∑' n : ℕ, (2 : ℝ) / (b ^ 2 * ((n : ℝ) + 1) ^ 2 - 1)
      < ∑' n : ℕ, (2 : ℝ) / (4 * ((n : ℝ) + 1) ^ 2 - 1) :=
        hsum.tsum_lt_tsum hle hlt hs.summable
    _ = 1 := hs.tsum_eq

/-- **One side of the off-diagonal sum.** For `g`-separated reals and `ψ` nonnegative and
nonincreasing on `[g, ∞)`, the points `γ_l` with `σ(γ_l − γ_j) > 0` contribute at most
`Σ_{n ≥ 1} ψ(ng)`: the `n`-th of them lies at distance at least `ng`. -/
theorem sum_side_le_tsum {ι : Type*} [Fintype ι] [DecidableEq ι] (γ : ι → ℝ) {g : ℝ} (hg : 0 < g)
    (hsep : ∀ j l, j ≠ l → g ≤ |γ j - γ l|) {ψ : ℝ → ℝ} (hψ0 : ∀ x, g ≤ x → 0 ≤ ψ x)
    (hψmono : ∀ x y, g ≤ x → x ≤ y → ψ y ≤ ψ x) (hψs : Summable fun n : ℕ => ψ ((n + 1) * g))
    (j : ι) {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) :
    ∑ l ∈ Finset.univ.filter (fun l => 0 < σ * (γ l - γ j)), ψ |γ j - γ l| ≤
      ∑' n : ℕ, ψ ((n + 1) * g) := by
  classical
  set S := Finset.univ.filter fun l => 0 < σ * (γ l - γ j) with hS
  have hd : ∀ l ∈ S, |γ j - γ l| = σ * (γ l - γ j) := fun l hl => by
    have h := (Finset.mem_filter.mp hl).2
    rcases hσ with rfl | rfl
    · rw [abs_sub_comm, abs_of_pos (by linarith)]; ring
    · rw [abs_of_pos (by linarith)]; ring
  have hlj : ∀ l ∈ S, l ≠ j := fun l hl h => by
    have := (Finset.mem_filter.mp hl).2
    rw [h, sub_self, mul_zero] at this
    exact lt_irrefl _ this
  set m : ι → ℕ := fun l => ⌊|γ j - γ l| / g⌋₊ - 1 with hm
  have hge : ∀ l ∈ S, 1 ≤ ⌊|γ j - γ l| / g⌋₊ := fun l hl =>
    Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hg, one_mul]; exact hsep j l (hlj l hl).symm)
  have hmg : ∀ l ∈ S, ((m l : ℝ) + 1) * g ≤ |γ j - γ l| := fun l hl => by
    have h1 := hge l hl
    have h2 : ((m l : ℕ) : ℝ) + 1 = (⌊|γ j - γ l| / g⌋₊ : ℝ) := by
      rw [hm]; simp only; rw [Nat.cast_sub h1]; push_cast; ring
    rw [h2, ← le_div_iff₀ hg]
    exact Nat.floor_le (div_nonneg (abs_nonneg _) hg.le)
  have hinj : Set.InjOn m S := by
    intro l hl l' hl' hll'
    by_contra hne
    have hsep' := hsep l l' hne
    have hfl : ⌊|γ j - γ l| / g⌋₊ = ⌊|γ j - γ l'| / g⌋₊ := by
      have h1 := hge l hl
      have h2 := hge l' hl'
      simp only [hm] at hll'
      omega
    have hx := Nat.floor_le (div_nonneg (abs_nonneg (γ j - γ l)) hg.le)
    have hx' := Nat.lt_floor_add_one (|γ j - γ l| / g)
    have hy := Nat.floor_le (div_nonneg (abs_nonneg (γ j - γ l')) hg.le)
    have hy' := Nat.lt_floor_add_one (|γ j - γ l'| / g)
    rw [hfl] at hx hx'
    have hdiff : |(|γ j - γ l| / g - |γ j - γ l'| / g)| < 1 := by
      rw [abs_lt]; constructor <;> linarith
    rw [← sub_div, abs_div, abs_of_pos hg, div_lt_one hg, hd l hl, hd l' hl'] at hdiff
    have : |γ l - γ l'| < g := by
      rcases hσ with rfl | rfl
      · rw [show 1 * (γ l - γ j) - 1 * (γ l' - γ j) = γ l - γ l' by ring] at hdiff; exact hdiff
      · rw [show -1 * (γ l - γ j) - -1 * (γ l' - γ j) = -(γ l - γ l') by ring, abs_neg] at hdiff
        exact hdiff
    linarith
  calc ∑ l ∈ S, ψ |γ j - γ l| ≤ ∑ l ∈ S, ψ (((m l : ℝ) + 1) * g) :=
        Finset.sum_le_sum fun l hl => hψmono _ _ (by
          have : (1 : ℝ) ≤ (m l : ℝ) + 1 := by linarith [(Nat.cast_nonneg (m l) : (0 : ℝ) ≤ m l)]
          nlinarith) (hmg l hl)
    _ = ∑ n ∈ S.image m, ψ ((((n : ℕ) : ℝ) + 1) * g) := (Finset.sum_image (f := fun n : ℕ => ψ (((n : ℝ) + 1) * g)) hinj).symm
    _ ≤ ∑' n : ℕ, ψ ((n + 1) * g) := hψs.sum_le_tsum _ fun n _ => hψ0 _ (by
          have : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
          nlinarith)

/-- **Off-diagonal sum.** For `g`-separated reals and `ψ` nonnegative and nonincreasing on
`[g, ∞)`, `Σ_{l ≠ j} ψ(|γ_j − γ_l|) ≤ 2 Σ_{n ≥ 1} ψ(ng)`. -/
theorem sum_offDiag_le_two_tsum {ι : Type*} [Fintype ι] [DecidableEq ι] (γ : ι → ℝ) {g : ℝ}
    (hg : 0 < g) (hsep : ∀ j l, j ≠ l → g ≤ |γ j - γ l|) {ψ : ℝ → ℝ}
    (hψ0 : ∀ x, g ≤ x → 0 ≤ ψ x) (hψmono : ∀ x y, g ≤ x → x ≤ y → ψ y ≤ ψ x)
    (hψs : Summable fun n : ℕ => ψ ((n + 1) * g)) (j : ι) :
    ∑ l ∈ Finset.univ.filter (· ≠ j), ψ |γ j - γ l| ≤ 2 * ∑' n : ℕ, ψ ((n + 1) * g) := by
  classical
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ.filter (· ≠ j))
    (fun l => 0 < 1 * (γ l - γ j)) (fun l => ψ |γ j - γ l|)
  have h1 : (Finset.univ.filter (· ≠ j)).filter (fun l => 0 < 1 * (γ l - γ j)) =
      Finset.univ.filter (fun l => 0 < 1 * (γ l - γ j)) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨fun hl => ?_, h⟩
      rw [hl, sub_self, mul_zero] at h
      exact lt_irrefl _ h
  have h2 : (Finset.univ.filter (· ≠ j)).filter (fun l => ¬ 0 < 1 * (γ l - γ j)) =
      Finset.univ.filter (fun l => 0 < -1 * (γ l - γ j)) := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hl, h⟩
      have hne : γ l ≠ γ j := fun he => by
        have := hsep j l (Ne.symm hl)
        rw [he, sub_self, abs_zero] at this
        linarith
      push Not at h
      have : γ l - γ j < 0 := lt_of_le_of_ne (by linarith) (sub_ne_zero.mpr hne)
      linarith
    · intro h
      refine ⟨fun hl => ?_, by push Not; linarith⟩
      rw [hl, sub_self, mul_zero] at h
      exact lt_irrefl _ h
  rw [← hsplit, h1, h2, two_mul]
  exact add_le_add (sum_side_le_tsum γ hg hsep hψ0 hψmono hψs j (Or.inl rfl))
    (sum_side_le_tsum γ hg hsep hψ0 hψmono hψs j (Or.inr rfl))

/-- The Ingham constant `C(T, g) = (4T/π)(1 − Σ_{n ≥ 1} 2/(b²n² − 1))`, `b = 2Tg/π`. -/
def inghamConst (T g : ℝ) : ℝ :=
  4 * T / π * (1 - ∑' n : ℕ, 2 / ((2 * T * g / π) ^ 2 * ((n : ℝ) + 1) ^ 2 - 1))

theorem inghamConst_pos {T g : ℝ} (hT : 0 < T) (hTg : π < T * g) : 0 < inghamConst T g := by
  have hb : 2 < 2 * T * g / π := by rw [lt_div_iff₀ Real.pi_pos]; linarith
  have h := (tsum_two_div_sq_sub_one_lt_one hb).2
  exact mul_pos (by positivity) (by linarith)

/-- **Ingham's inequality.** For reals `γ_j` with pairwise gaps at least `g` and `Tg > π`,
`C(T, g) Σ_j |c_j|² ≤ ∫_{−T}^{T} |Σ_j c_j e^{iγ_j t}|² dt` with `C(T, g) > 0`. -/
theorem ingham_inequality {ι : Type*} [Fintype ι] (γ : ι → ℝ) (c : ι → ℂ) {g T : ℝ}
    (hg : 0 < g) (hT : 0 < T) (hTg : π < T * g) (hsep : ∀ j l, j ≠ l → g ≤ |γ j - γ l|) :
    inghamConst T g * ∑ j, ‖c j‖ ^ 2 ≤ ∫ t in -T..T, ‖∑ j, c j * cexp (I * γ j * t)‖ ^ 2 := by
  classical
  set a := π / (2 * T) with ha
  have ha0 : 0 < a := by positivity
  have hga : 2 * a < g := by
    rw [ha, show 2 * (π / (2 * T)) = π / T by field_simp, div_lt_iff₀ hT]
    linarith
  set b := 2 * T * g / π with hb
  have hb2 : 2 < b := by rw [hb, lt_div_iff₀ Real.pi_pos]; linarith
  have hgab : g = b * a := by rw [hb, ha]; field_simp
  obtain ⟨hbs, -⟩ := tsum_two_div_sq_sub_one_lt_one hb2
  set B := ∑' n : ℕ, (2 : ℝ) / (b ^ 2 * ((n : ℝ) + 1) ^ 2 - 1) with hB
  have hconst : inghamConst T g = 2 / a * (1 - B) := by
    rw [inghamConst, hB, hb, ha]
    congr 1
    field_simp
    ring
  -- the comparison function
  set ψ : ℝ → ℝ := fun x => 2 * a / (x ^ 2 - a ^ 2) with hψ
  have hψ0 : ∀ x, g ≤ x → 0 ≤ ψ x := fun x hx => div_nonneg (by positivity) (by nlinarith)
  have hψmono : ∀ x y, g ≤ x → x ≤ y → ψ y ≤ ψ x := fun x y hx hxy =>
    div_le_div_of_nonneg_left (by positivity) (by nlinarith) (by nlinarith)
  have hψn : ∀ n : ℕ, ψ (((n : ℝ) + 1) * g) = 1 / a * (2 / (b ^ 2 * ((n : ℝ) + 1) ^ 2 - 1)) := by
    intro n
    have hpos : 0 < b ^ 2 * ((n : ℝ) + 1) ^ 2 - 1 := by
      have : (4 : ℝ) ≤ b ^ 2 := by nlinarith
      nlinarith [sq_nonneg ((n : ℝ) + 1), (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
    rw [hψ, hgab]
    simp only
    rw [show (((n : ℝ) + 1) * (b * a)) ^ 2 - a ^ 2 = a ^ 2 * (b ^ 2 * ((n : ℝ) + 1) ^ 2 - 1) by ring]
    field_simp
  have hψs : Summable fun n : ℕ => ψ (((n : ℝ) + 1) * g) :=
    (hbs.mul_left (1 / a)).congr fun n => (hψn n).symm
  have hψt : 2 * ∑' n : ℕ, ψ (((n : ℝ) + 1) * g) = 2 / a * B := by
    rw [tsum_congr hψn, tsum_mul_left, hB]
    ring
  have hrow : ∀ j, ∑ l ∈ Finset.univ.filter (· ≠ j), ψ |γ j - γ l| ≤ 2 / a * B := fun j =>
    (sum_offDiag_le_two_tsum γ hg hsep hψ0 hψmono hψs j).trans_eq hψt
  have hk : ∀ j l, j ≠ l → ‖inghamKernel T (γ j - γ l)‖ ≤ ψ |γ j - γ l| := fun j l hjl => by
    have hd := hsep j l hjl
    have h := norm_inghamKernel_le (x := γ j - γ l) hT (by rw [← ha]; linarith)
    rw [← ha] at h
    rw [hψ]
    simp only
    rwa [sq_abs]
  -- the weight `cos(at) ≤ 1`
  set f : ℝ → ℂ := fun t => ∑ j, c j * cexp (I * γ j * t) with hf
  have hfc : Continuous fun t => ‖f t‖ ^ 2 := by rw [hf]; fun_prop
  have h1 : ∫ t in -T..T, Real.cos (a * t) * ‖f t‖ ^ 2 ≤ ∫ t in -T..T, ‖f t‖ ^ 2 :=
    intervalIntegral.integral_mono_on (by linarith)
      ((show Continuous fun t : ℝ => Real.cos (a * t) * ‖f t‖ ^ 2 from
        (Real.continuous_cos.comp (continuous_const.mul continuous_id)).mul hfc).intervalIntegrable _ _)
      (hfc.intervalIntegrable _ _) fun t _ =>
        mul_le_of_le_one_left (by positivity) (Real.cos_le_one _)
  have hQ := integral_cos_mul_normSq_expSum γ c T
  rw [← ha] at hQ
  refine le_trans ?_ (hQ ▸ h1)
  -- the quadratic form is bounded below
  rw [hconst, Complex.re_sum]
  have hX : ∀ j, (∑ l, c j * conj (c l) * inghamKernel T (γ j - γ l)).re ≥
      2 / a * ‖c j‖ ^ 2 - ∑ l ∈ Finset.univ.filter (· ≠ j), ‖c j‖ * ‖c l‖ * ψ |γ j - γ l| := by
    intro j
    rw [Finset.filter_ne', ← Finset.add_sum_erase _ _ (Finset.mem_univ j), Complex.add_re,
      Complex.re_sum, sub_self, inghamKernel_zero hT, Complex.mul_conj, ← Complex.ofReal_mul,
      Complex.ofReal_re, Complex.normSq_eq_norm_sq]
    have hdiag : ‖c j‖ ^ 2 * (4 * T / π) = 2 / a * ‖c j‖ ^ 2 := by rw [ha]; field_simp; ring
    rw [hdiag]
    have hoff : ∀ l ∈ Finset.univ.erase j, -(‖c j‖ * ‖c l‖ * ψ |γ j - γ l|) ≤
        (c j * conj (c l) * inghamKernel T (γ j - γ l)).re := fun l hl => by
      have hne : j ≠ l := (Finset.ne_of_mem_erase hl).symm
      have h := (abs_le.mp (Complex.abs_re_le_norm
        (c j * conj (c l) * inghamKernel T (γ j - γ l)))).1
      rw [norm_mul, norm_mul, Complex.norm_conj] at h
      have := hk j l hne
      nlinarith [norm_nonneg (c j), norm_nonneg (c l), mul_nonneg (norm_nonneg (c j)) (norm_nonneg (c l)),
        norm_nonneg (inghamKernel T (γ j - γ l))]
    have := Finset.sum_le_sum hoff
    rw [Finset.sum_neg_distrib] at this
    linarith
  have hswap : ∀ F : ι → ι → ℝ, ∑ j, ∑ l ∈ Finset.univ.filter (· ≠ j), F j l =
      ∑ l, ∑ j ∈ Finset.univ.filter (· ≠ l), F j l := by
    intro F
    simp only [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
    by_cases h : j = l
    · subst h; simp
    · simp [h, Ne.symm h]
  have hschur : ∑ j, ∑ l ∈ Finset.univ.filter (· ≠ j), ‖c j‖ * ‖c l‖ * ψ |γ j - γ l| ≤
      2 / a * B * ∑ j, ‖c j‖ ^ 2 := by
    have hamgm : ∀ j, ∀ l ∈ Finset.univ.filter (· ≠ j), ‖c j‖ * ‖c l‖ * ψ |γ j - γ l| ≤
        ‖c j‖ ^ 2 * ψ |γ j - γ l| / 2 + ‖c l‖ ^ 2 * ψ |γ j - γ l| / 2 := fun j l hl => by
      have hψ' : 0 ≤ ψ |γ j - γ l| :=
        hψ0 _ (hsep j l (Ne.symm (Finset.mem_filter.mp hl).2))
      nlinarith [sq_nonneg (‖c j‖ - ‖c l‖), mul_nonneg hψ' (sq_nonneg (‖c j‖ - ‖c l‖))]
    have hfirst : ∑ j, ∑ l ∈ Finset.univ.filter (· ≠ j), ‖c j‖ ^ 2 * ψ |γ j - γ l| / 2 ≤
        2 / a * B * ∑ j, ‖c j‖ ^ 2 / 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun j _ => ?_
      rw [← Finset.sum_div, ← Finset.mul_sum]
      have := mul_le_mul_of_nonneg_left (hrow j) (sq_nonneg ‖c j‖)
      linarith
    have hsecond : ∑ j, ∑ l ∈ Finset.univ.filter (· ≠ j), ‖c l‖ ^ 2 * ψ |γ j - γ l| / 2 ≤
        2 / a * B * ∑ j, ‖c j‖ ^ 2 / 2 := by
      rw [hswap (fun j l => ‖c l‖ ^ 2 * ψ |γ j - γ l| / 2), Finset.mul_sum]
      refine Finset.sum_le_sum fun l _ => ?_
      rw [← Finset.sum_div, ← Finset.mul_sum]
      have hr := hrow l
      have hrow' : ∑ j ∈ Finset.univ.filter (· ≠ l), ψ |γ j - γ l| ≤ 2 / a * B := by
        simpa only [abs_sub_comm] using hr
      have := mul_le_mul_of_nonneg_left hrow' (sq_nonneg ‖c l‖)
      linarith
    calc ∑ j, ∑ l ∈ Finset.univ.filter (· ≠ j), ‖c j‖ * ‖c l‖ * ψ |γ j - γ l|
        ≤ ∑ j, ∑ l ∈ Finset.univ.filter (· ≠ j),
            (‖c j‖ ^ 2 * ψ |γ j - γ l| / 2 + ‖c l‖ ^ 2 * ψ |γ j - γ l| / 2) :=
          Finset.sum_le_sum fun j _ => Finset.sum_le_sum (hamgm j)
      _ = ∑ j, ∑ l ∈ Finset.univ.filter (· ≠ j), ‖c j‖ ^ 2 * ψ |γ j - γ l| / 2 +
          ∑ j, ∑ l ∈ Finset.univ.filter (· ≠ j), ‖c l‖ ^ 2 * ψ |γ j - γ l| / 2 := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun j _ => Finset.sum_add_distrib
      _ ≤ 2 / a * B * ∑ j, ‖c j‖ ^ 2 / 2 + 2 / a * B * ∑ j, ‖c j‖ ^ 2 / 2 :=
          add_le_add hfirst hsecond
      _ = 2 / a * B * ∑ j, ‖c j‖ ^ 2 := by rw [← Finset.sum_div]; ring
  have hsum := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => hX j
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  linarith

end GaloisForLFunctions.SquareRootThreshold
