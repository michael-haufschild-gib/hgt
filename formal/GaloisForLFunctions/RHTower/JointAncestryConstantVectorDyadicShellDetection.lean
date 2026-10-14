import GaloisForLFunctions.RHTower.JointAncestryConstantVectorDyadicShells

/-!
# Dyadic-shell detection of a maximal off-line zero by constant-vector JAS tests

**Theorem** (`eventually_not_jasConstProductPositiveOn_shell_of_maximal_offLine`).  If an off-line
zero has the largest distance `δ` from the critical line and `δ < σ < 1 + δ`, then for every
sufficiently large `N` the constant-vector JAS test on the primes of the dyadic shell `(N, 2N]` is
negative for some `z ∈ ℂ`.

**Capstones.**  RH holds iff the zeros approach the line and constant-vector positivity holds on
infinitely many dyadic shells; the same holds with "no off-line chain" in place of the first
condition.

**Mechanism.**
* *Shell main term.*  For `z = α − it`, `0 < α < 1`, the shell sum `Σ_{N<p≤2N} p^{−z}` is
  `M_z(2N) − M_z(N) + o(E_α(N))`, with `M_z(N) = N^{1−z}/((1−z) log N)` and
  `E_α(N) = N^{1−α}/log N`.  Since `M_z(2N) = λ_N 2^{1−α} e^{it log 2} M_z(N)` with
  `λ_N = log N/log 2N → 1`, the shell sum has size `f(t) E_α(N) + o(E_α(N))`, where
  `f(t) = |2^{1−α} e^{it log 2} − 1|/|1 − α + it|`.
* *Tie group.*  `f > 0` and `f(t) ≤ 3/|t|`, so among the zeros at distance `δ` only finitely many
  have `f ≥ f(γ₀)/2`.  The largest value `f_max` is attained on a finite group `G`, and all other
  zeros at distance `δ` have `f ≤ f₂ < f_max`.  Zeros closer to the line have shell sums
  `o(E_α(N))`.
* *Anti-alignment.*  The group `G` may contain several zeros of exactly equal size; the multi-point
  anti-alignment lemma handles all of them at once.  The other zeros of a finite set `F ⊇ G` are
  far at every rung, and the zeros outside `F` form a light tail.
* *Uniform angle.*  For a zero at distance at most `δ < ½` from the line,
  `Re(1/(ρ(1−ρ))) ≥ (¼ − δ²) |1/(ρ(1−ρ))|`.
-/

open Complex Filter
open scoped ComplexConjugate Topology BigOperators

namespace RHTower

noncomputable section

/-! ## A uniform angle for the zero weights -/

/-- `Re(1/(s(1−s))) ≥ (¼ − δ²) ‖1/(s(1−s))‖` when `|Re s − ½| ≤ δ < ½`. -/
theorem quarter_sub_sq_mul_norm_le_re_one_div {δ : ℝ} (hδ : δ < 1 / 2) {s : ℂ}
    (hs : |s.re - 1 / 2| ≤ δ) :
    (1 / 4 - δ ^ 2) * ‖1 / (s * (1 - s))‖ ≤ (1 / (s * (1 - s))).re := by
  obtain ⟨v, hv⟩ : ∃ v : ℂ, v = s * (1 - s) := ⟨_, rfl⟩
  rw [← hv]
  have hvre : v.re = 1 / 4 - (s.re - 1 / 2) ^ 2 + s.im ^ 2 := by rw [hv]; simp; ring
  have hvim : v.im = -2 * (s.re - 1 / 2) * s.im := by rw [hv]; simp; ring
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hs
  have hd := abs_le.mp hs
  have hd2 : (s.re - 1 / 2) ^ 2 ≤ δ ^ 2 := by nlinarith
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℝ, κ = 1 / 4 - δ ^ 2 := ⟨_, rfl⟩
  rw [← hκdef]
  have hκ : 0 < κ := by rw [hκdef]; nlinarith
  have hκ4 : κ ≤ 1 / 4 := by rw [hκdef]; nlinarith
  have hA : κ + s.im ^ 2 ≤ v.re := by rw [hvre]; linarith
  have hApos : 0 < v.re := by nlinarith [sq_nonneg s.im]
  have hnorm2 : ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have him2 : v.im ^ 2 ≤ s.im ^ 2 := by
    have h4 : 4 * (s.re - 1 / 2) ^ 2 ≤ 1 := by nlinarith
    have e : v.im ^ 2 = 4 * (s.re - 1 / 2) ^ 2 * s.im ^ 2 := by rw [hvim]; ring
    rw [e]; nlinarith [sq_nonneg s.im]
  have hy : 4 * κ * s.im ^ 2 ≤ v.re ^ 2 := by
    have h1 : (κ + s.im ^ 2) ^ 2 ≤ v.re ^ 2 := pow_le_pow_left₀ (by positivity) hA 2
    nlinarith [sq_nonneg (κ - s.im ^ 2)]
  have hkey : (κ * ‖v‖) ^ 2 ≤ v.re ^ 2 := by
    rw [mul_pow, hnorm2]
    have h1 : κ ^ 2 * v.im ^ 2 ≤ κ ^ 2 * s.im ^ 2 := mul_le_mul_of_nonneg_left him2 (sq_nonneg κ)
    have h2 : κ * (4 * κ * s.im ^ 2) ≤ κ * v.re ^ 2 := mul_le_mul_of_nonneg_left hy hκ.le
    have h3 : κ * v.re ^ 2 ≤ 1 / 4 * v.re ^ 2 := mul_le_mul_of_nonneg_right hκ4 (sq_nonneg _)
    have h4 : κ ^ 2 ≤ 1 / 16 := by nlinarith
    have h5 : κ ^ 2 * v.re ^ 2 ≤ 1 / 16 * v.re ^ 2 := mul_le_mul_of_nonneg_right h4 (sq_nonneg _)
    nlinarith
  have hkey' : κ * ‖v‖ ≤ v.re := by
    have h0 : 0 ≤ κ * ‖v‖ := mul_nonneg hκ.le (norm_nonneg _)
    nlinarith
  have hv0 : v ≠ 0 := fun h => by rw [h, Complex.zero_re] at hApos; exact lt_irrefl _ hApos
  have hvn : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  rw [one_div, Complex.inv_re, norm_inv, Complex.normSq_eq_norm_sq]
  rw [show κ * ‖v‖⁻¹ = κ * ‖v‖ / ‖v‖ ^ 2 by field_simp]
  exact div_le_div_of_nonneg_right hkey' (by positivity)

/-! ## The large prime sum through a fixed exponent -/

/-- `‖W_big(s)‖ = ‖W((σ − |Re s − ½|) − i|Im s|)‖`. -/
theorem norm_jasBigSum_eq (P : Finset Nat.Primes) (σ : ℝ) (s : ℂ) :
    ‖jasBigSum P σ s‖ =
      ‖jasCpowSum P (((σ - |s.re - 1 / 2| : ℝ) : ℂ) - ((|s.im| : ℝ) : ℂ) * I)‖ := by
  obtain ⟨t, ht⟩ : ∃ t : ℂ, t = ((σ - |s.re - 1 / 2| : ℝ) : ℂ) - ((|s.im| : ℝ) : ℂ) * I :=
    ⟨_, rfl⟩
  rw [← ht, jasBigSum]
  split_ifs with h
  · have hre : |s.re - 1 / 2| = s.re - 1 / 2 := abs_of_nonneg (by linarith)
    rcases le_or_gt 0 s.im with hi | hi
    · have : (σ : ℂ) - (s - 1 / 2) = t :=
        Complex.ext (by rw [ht, hre]; simp) (by rw [ht]; simp [abs_of_nonneg hi])
      rw [this]
    · have : (σ : ℂ) - (s - 1 / 2) = conj t :=
        Complex.ext (by rw [ht, hre]; simp) (by rw [ht]; simp [abs_of_neg hi])
      rw [this, norm_jasCpowSum_conj]
  · push Not at h
    have hre : |s.re - 1 / 2| = -(s.re - 1 / 2) := abs_of_neg (by linarith)
    rcases le_or_gt 0 s.im with hi | hi
    · have : (σ : ℂ) + (s - 1 / 2) = conj t :=
        Complex.ext (by rw [ht, hre]; simp; ring) (by rw [ht]; simp [abs_of_nonneg hi])
      rw [this, norm_jasCpowSum_conj]
    · have : (σ : ℂ) + (s - 1 / 2) = t :=
        Complex.ext (by rw [ht, hre]; simp; ring) (by rw [ht]; simp [abs_of_neg hi])
      rw [this]

/-! ## The main term of a dyadic shell -/

/-- `E_α(2N) = 2^{1−α} (log N/log 2N) E_α(N)`. -/
theorem jasMainScale_two_mul (α : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    jasMainScale α (2 * N) =
      (2 : ℝ) ^ (1 - α) * (Real.log N / Real.log (2 * N)) * jasMainScale α N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog := Real.log_pos hN1
  have hlog2 : 0 < Real.log (2 * N) := Real.log_pos (by linarith)
  rw [jasMainScale, jasMainScale]
  push_cast
  rw [Real.mul_rpow (by norm_num) hN0.le]
  field_simp

/-- `M_z(2N) = λ_N 2^{1−α} e^{it log 2} M_z(N)` for `z = α − it`, `λ_N = log N/log 2N`. -/
theorem jasMainTerm_two_mul (α t : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    jasMainTerm ((α : ℂ) - (t : ℂ) * I) (2 * N) =
      (((2 : ℝ) ^ (1 - α) * (Real.log N / Real.log (2 * N)) : ℝ) : ℂ) *
        cexp (((t * Real.log 2 : ℝ) : ℂ) * I) * jasMainTerm ((α : ℂ) - (t : ℂ) * I) N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  rw [jasMainTerm_eq α t (by omega : 0 < 2 * N), jasMainTerm_eq α t (by omega : 0 < N),
    jasMainScale_two_mul α hN]
  have hlog : Real.log ((2 * N : ℕ) : ℝ) = Real.log 2 + Real.log N := by
    push_cast; exact Real.log_mul two_ne_zero hN0.ne'
  rw [hlog]
  have e : (((t * (Real.log 2 + Real.log N) : ℝ) : ℂ) * I) =
      ((t * Real.log 2 : ℝ) : ℂ) * I + ((t * Real.log N : ℝ) : ℂ) * I := by push_cast; ring
  rw [e, Complex.exp_add]
  push_cast
  ring

/-- The shell factor `f(t) = |2^{1−α} e^{it log 2} − 1|/|1 − α + it|`. -/
def jasShellFactor (α t : ℝ) : ℝ :=
  ‖(((2 : ℝ) ^ (1 - α) : ℝ) : ℂ) * cexp (((t * Real.log 2 : ℝ) : ℂ) * I) - 1‖ /
    Real.sqrt ((1 - α) ^ 2 + t ^ 2)

theorem norm_two_rpow_mul_cexp (α t : ℝ) :
    ‖(((2 : ℝ) ^ (1 - α) : ℝ) : ℂ) * cexp (((t * Real.log 2 : ℝ) : ℂ) * I)‖ =
      (2 : ℝ) ^ (1 - α) := by
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (by positivity)]

theorem jasShellFactor_pos {α : ℝ} (hα1 : α < 1) (t : ℝ) : 0 < jasShellFactor α t := by
  have h1 : 1 < (2 : ℝ) ^ (1 - α) := Real.one_lt_rpow (by norm_num) (by linarith)
  have h2 := norm_sub_norm_le ((((2 : ℝ) ^ (1 - α) : ℝ) : ℂ) *
    cexp (((t * Real.log 2 : ℝ) : ℂ) * I)) 1
  rw [norm_two_rpow_mul_cexp, norm_one] at h2
  have h1α : 0 < 1 - α := by linarith
  exact div_pos (by linarith)
    (Real.sqrt_pos.mpr (add_pos_of_pos_of_nonneg (pow_pos h1α 2) (sq_nonneg t)))

/-- `f(t) |t| ≤ 3`. -/
theorem jasShellFactor_mul_abs_le {α : ℝ} (hα0 : 0 < α) (t : ℝ) :
    jasShellFactor α t * |t| ≤ 3 := by
  have h1 : (2 : ℝ) ^ (1 - α) ≤ 2 := by
    calc (2 : ℝ) ^ (1 - α) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have h2 : ‖(((2 : ℝ) ^ (1 - α) : ℝ) : ℂ) * cexp (((t * Real.log 2 : ℝ) : ℂ) * I) - 1‖ ≤ 3 := by
    refine (norm_sub_le _ _).trans ?_
    rw [norm_two_rpow_mul_cexp, norm_one]; linarith
  have h3 : |t| ≤ Real.sqrt ((1 - α) ^ 2 + t ^ 2) := by
    rw [← Real.sqrt_sq_eq_abs]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg (1 - α)])
  rcases eq_or_lt_of_le (abs_nonneg t) with h0 | h0
  · rw [← h0, mul_zero]; norm_num
  · have hs : 0 < Real.sqrt ((1 - α) ^ 2 + t ^ 2) := h0.trans_le h3
    rw [jasShellFactor, div_mul_eq_mul_div, div_le_iff₀ hs]
    nlinarith [norm_nonneg ((((2 : ℝ) ^ (1 - α) : ℝ) : ℂ) *
      cexp (((t * Real.log 2 : ℝ) : ℂ) * I) - 1)]

/-- **The shell main term.**  `|‖M_z(2N) − M_z(N)‖ − f(t) E_α(N)| ≤ 2(1 − λ_N) E_α(N)/(1 − α)`. -/
theorem abs_norm_shellMain_sub_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (t : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    |‖jasMainTerm ((α : ℂ) - (t : ℂ) * I) (2 * N) - jasMainTerm ((α : ℂ) - (t : ℂ) * I) N‖ -
        jasShellFactor α t * jasMainScale α N| ≤
      2 * (1 - Real.log N / Real.log (2 * N)) * jasMainScale α N / (1 - α) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog := Real.log_pos hN1
  have hlog2 : Real.log N ≤ Real.log (2 * N) :=
    Real.log_le_log (by linarith) (by linarith)
  have hlog2' : 0 < Real.log (2 * N) := hlog.trans_le hlog2
  obtain ⟨l, hl⟩ : ∃ l : ℝ, l = Real.log N / Real.log (2 * N) := ⟨_, rfl⟩
  have hl0 : 0 ≤ l := by rw [hl]; positivity
  have hl1 : l ≤ 1 := by rw [hl, div_le_one hlog2']; exact hlog2
  obtain ⟨g, hg⟩ : ∃ g : ℂ, g = (((2 : ℝ) ^ (1 - α) : ℝ) : ℂ) *
      cexp (((t * Real.log 2 : ℝ) : ℂ) * I) := ⟨_, rfl⟩
  have hgn : ‖g‖ = (2 : ℝ) ^ (1 - α) := by rw [hg, norm_two_rpow_mul_cexp]
  have hg2 : (2 : ℝ) ^ (1 - α) ≤ 2 := by
    calc (2 : ℝ) ^ (1 - α) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  obtain ⟨M, hM⟩ : ∃ M : ℂ, M = jasMainTerm ((α : ℂ) - (t : ℂ) * I) N := ⟨_, rfl⟩
  have h2N : jasMainTerm ((α : ℂ) - (t : ℂ) * I) (2 * N) = (l : ℂ) * g * M := by
    rw [jasMainTerm_two_mul α t hN, ← hl, ← hM, hg]; push_cast; ring
  have hMn : ‖M‖ = jasMainScale α N / Real.sqrt ((1 - α) ^ 2 + t ^ 2) := by
    rw [hM, norm_jasMainTerm_eq α t hN]
  have hsq : 1 - α ≤ Real.sqrt ((1 - α) ^ 2 + t ^ 2) :=
    calc 1 - α = Real.sqrt ((1 - α) ^ 2) := (Real.sqrt_sq (by linarith)).symm
      _ ≤ Real.sqrt ((1 - α) ^ 2 + t ^ 2) := Real.sqrt_le_sqrt (by nlinarith [sq_nonneg t])
  have hsq0 : 0 < Real.sqrt ((1 - α) ^ 2 + t ^ 2) := lt_of_lt_of_le (by linarith) hsq
  have hE := jasMainScale_pos (α := α) hN
  rw [h2N, ← hM, show (l : ℂ) * g * M - M = ((l : ℂ) * g - 1) * M by ring, norm_mul, hMn]
  have hfE : jasShellFactor α t * jasMainScale α N =
      ‖g - 1‖ * (jasMainScale α N / Real.sqrt ((1 - α) ^ 2 + t ^ 2)) := by
    rw [jasShellFactor, ← hg]; ring
  rw [hfE, ← sub_mul, abs_mul, abs_of_nonneg (show 0 ≤ jasMainScale α N /
    Real.sqrt ((1 - α) ^ 2 + t ^ 2) by positivity), ← hl]
  have hdiff : |‖(l : ℂ) * g - 1‖ - ‖g - 1‖| ≤ 2 * (1 - l) := by
    refine (abs_norm_sub_norm_le _ _).trans ?_
    rw [show (l : ℂ) * g - 1 - (g - 1) = -((((1 - l : ℝ)) : ℂ) * g) by push_cast; ring, norm_neg,
      norm_mul, Complex.norm_real, Real.norm_of_nonneg (by linarith), hgn]
    exact mul_le_mul_of_nonneg_left hg2 (by linarith) |>.trans_eq (by ring)
  calc |‖(l : ℂ) * g - 1‖ - ‖g - 1‖| * (jasMainScale α N / Real.sqrt ((1 - α) ^ 2 + t ^ 2))
      ≤ 2 * (1 - l) * (jasMainScale α N / (1 - α)) :=
        mul_le_mul hdiff (div_le_div_of_nonneg_left hE.le (by linarith) hsq) (by positivity)
          (by linarith)
    _ = 2 * (1 - l) * jasMainScale α N / (1 - α) := by ring

/-- `E_α(2N) ≤ 2 E_α(N)` for `0 ≤ α`. -/
theorem jasMainScale_two_mul_le {α : ℝ} (hα0 : 0 ≤ α) {N : ℕ} (hN : 2 ≤ N) :
    jasMainScale α (2 * N) ≤ 2 * jasMainScale α N := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog := Real.log_pos hN1
  have hlog2 : Real.log (2 * N) = Real.log 2 + Real.log N :=
    Real.log_mul two_ne_zero (by linarith)
  have hlog2' : 0 < Real.log (2 * N) := by rw [hlog2]; linarith [Real.log_pos one_lt_two]
  have hE := jasMainScale_pos (α := α) hN
  rw [jasMainScale_two_mul α hN]
  have h1 : (2 : ℝ) ^ (1 - α) ≤ 2 := by
    calc (2 : ℝ) ^ (1 - α) ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 2 := Real.rpow_one 2
  have h2 : Real.log N / Real.log (2 * N) ≤ 1 := by
    rw [div_le_one hlog2', hlog2]; linarith [Real.log_pos one_lt_two]
  have h3 : (2 : ℝ) ^ (1 - α) * (Real.log N / Real.log (2 * N)) ≤ 2 :=
    (mul_le_mul h1 h2 (by positivity) (by norm_num)).trans_eq (by ring)
  exact mul_le_mul_of_nonneg_right h3 hE.le

/-- The shell `(N, 2N]` is the difference of two initial windows. -/
theorem jasWindowSum_shell_eq (N : ℕ) (z : ℂ) :
    jasWindowSum N (2 * N) z = jasWindowSum 0 (2 * N) z - jasWindowSum 0 N z := by
  rw [jasWindowSum_eq_sub (by omega : N ≤ 2 * N), jasWindowSum_eq_sub (Nat.zero_le _),
    jasWindowSum_eq_sub (Nat.zero_le _)]
  ring

theorem tendsto_two_mul_atTop : Tendsto (fun N : ℕ => 2 * N) atTop atTop :=
  tendsto_atTop_mono (fun n => show id n ≤ 2 * n by rw [id]; omega) tendsto_id

/-- **Shell sums follow the shell factor.**  For `0 < α < 1`, eventually
`|‖Σ_{N<p≤2N} p^{−(α−it)}‖ − f(t) E_α(N)| ≤ η E_α(N)`. -/
theorem eventually_abs_norm_shell_sub_le {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (t : ℝ) {η : ℝ}
    (hη : 0 < η) :
    ∀ᶠ N : ℕ in atTop, |‖jasWindowSum N (2 * N) ((α : ℂ) - (t : ℂ) * I)‖ -
      jasShellFactor α t * jasMainScale α N| ≤ η * jasMainScale α N := by
  have hre : ((α : ℂ) - (t : ℂ) * I).re = α := by simp
  have h1 := eventually_norm_jasWindowSum_sub_main_le 0 (s := (α : ℂ) - (t : ℂ) * I)
    (by rw [hre]; exact hα0) (by rw [hre]; exact hα1) (show 0 < η / 6 by positivity)
  rw [hre] at h1
  have h2 := tendsto_two_mul_atTop.eventually h1
  have h1α : 0 < 1 - α := by linarith
  have h3 : ∀ᶠ N : ℕ in atTop, 4 * Real.log 2 / ((1 - α) * η) ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually (eventually_ge_atTop _)
  filter_upwards [h1, h2, h3, eventually_ge_atTop 2] with N hN1 hN2 hN3 hN
  have hN1' : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog := Real.log_pos hN1'
  have hE := jasMainScale_pos (α := α) hN
  have hlog2 : Real.log (2 * N) = Real.log 2 + Real.log N :=
    Real.log_mul two_ne_zero (by linarith)
  have hlog2' : 0 < Real.log (2 * N) := by rw [hlog2]; linarith [Real.log_pos one_lt_two]
  have hE2 := jasMainScale_two_mul_le hα0.le hN
  -- the window part
  have hwin : ‖jasWindowSum N (2 * N) ((α : ℂ) - (t : ℂ) * I) -
      (jasMainTerm ((α : ℂ) - (t : ℂ) * I) (2 * N) - jasMainTerm ((α : ℂ) - (t : ℂ) * I) N)‖ ≤
      η / 2 * jasMainScale α N := by
    rw [jasWindowSum_shell_eq]
    have e : jasWindowSum 0 (2 * N) ((α : ℂ) - (t : ℂ) * I) -
        jasWindowSum 0 N ((α : ℂ) - (t : ℂ) * I) -
        (jasMainTerm ((α : ℂ) - (t : ℂ) * I) (2 * N) - jasMainTerm ((α : ℂ) - (t : ℂ) * I) N) =
        (jasWindowSum 0 (2 * N) ((α : ℂ) - (t : ℂ) * I) -
          jasMainTerm ((α : ℂ) - (t : ℂ) * I) (2 * N)) -
        (jasWindowSum 0 N ((α : ℂ) - (t : ℂ) * I) - jasMainTerm ((α : ℂ) - (t : ℂ) * I) N) := by
      ring
    rw [e]
    refine (norm_sub_le _ _).trans ?_
    have := mul_le_mul_of_nonneg_left hE2 (show 0 ≤ η / 6 by positivity)
    linarith
  -- the main part
  have hmain := abs_norm_shellMain_sub_le hα0 hα1 t hN
  have hl : 2 * (1 - Real.log N / Real.log (2 * N)) * jasMainScale α N / (1 - α) ≤
      η / 2 * jasMainScale α N := by
    have e : 1 - Real.log N / Real.log (2 * N) = Real.log 2 / Real.log (2 * N) := by
      field_simp; rw [hlog2]; ring
    rw [e]
    have h4 : Real.log 2 / Real.log (2 * N) ≤ Real.log 2 / Real.log N :=
      div_le_div_of_nonneg_left (Real.log_pos one_lt_two).le hlog
        (by rw [hlog2]; linarith [Real.log_pos one_lt_two])
    have h5 : Real.log 2 / Real.log N ≤ (1 - α) * η / 4 := by
      rw [div_le_iff₀ hlog]
      rw [div_le_iff₀ (by positivity)] at hN3
      linarith
    rw [div_le_iff₀ h1α]
    have h6 : 2 * (Real.log 2 / Real.log (2 * N)) ≤ 2 * ((1 - α) * η / 4) := by linarith
    have := mul_le_mul_of_nonneg_right h6 hE.le
    nlinarith
  have htri := abs_norm_sub_norm_le (jasWindowSum N (2 * N) ((α : ℂ) - (t : ℂ) * I))
    (jasMainTerm ((α : ℂ) - (t : ℂ) * I) (2 * N) - jasMainTerm ((α : ℂ) - (t : ℂ) * I) N)
  have := abs_sub_le (‖jasWindowSum N (2 * N) ((α : ℂ) - (t : ℂ) * I)‖)
    ‖jasMainTerm ((α : ℂ) - (t : ℂ) * I) (2 * N) - jasMainTerm ((α : ℂ) - (t : ℂ) * I) N‖
    (jasShellFactor α t * jasMainScale α N)
  linarith

/-! ## The tie group -/

/-- **The tie group.**  Let `φ > 0` at `q₀ ∈ D` and `φ ≤ φ(q₀)/2` on the zeros of `D` above height
`H`.  Then the largest value `M` of `φ` on `D` is attained on a finite nonempty group `G`, and
`φ ≤ f₂` on the rest of `D` for some `f₂ ∈ [M/2, M)`. -/
theorem exists_top_group (D : Set XiZeroCopy) (φ : XiZeroCopy → ℝ) {q₀ : XiZeroCopy}
    (hq₀ : q₀ ∈ D) (hφ0 : 0 < φ q₀) {H : ℝ} (hH : 0 ≤ H)
    (hdecay : ∀ q ∈ D, H < |(q.1 : ℂ).im| → φ q ≤ φ q₀ / 2) :
    ∃ (G : Finset XiZeroCopy) (M f₂ : ℝ), (∀ q ∈ G, q ∈ D) ∧ G.Nonempty ∧ 0 < M ∧
      M / 2 ≤ f₂ ∧ f₂ < M ∧ (∀ q ∈ G, φ q = M) ∧ (∀ q ∈ D, q ∉ G → φ q ≤ f₂) := by
  classical
  have hfin := finite_xiZeroCopy_band 0 hH
  obtain ⟨B, hB⟩ : ∃ B : Finset XiZeroCopy, B = hfin.toFinset.filter (· ∈ D) := ⟨_, rfl⟩
  have hmemB : ∀ q, q ∈ B ↔ |(q.1 : ℂ).im| ≤ H ∧ q ∈ D := by
    intro q
    rw [hB, Finset.mem_filter, Set.Finite.mem_toFinset, Set.mem_setOf_eq, sub_zero]
  have hq₀B : q₀ ∈ B := by
    refine (hmemB q₀).mpr ⟨?_, hq₀⟩
    by_contra h
    push Not at h
    have := hdecay q₀ hq₀ h
    linarith
  obtain ⟨qs, hqsB, hqsmax⟩ := B.exists_max_image φ ⟨q₀, hq₀B⟩
  obtain ⟨M, hM⟩ : ∃ M : ℝ, M = φ qs := ⟨_, rfl⟩
  have hM0 : φ q₀ ≤ M := hM ▸ hqsmax q₀ hq₀B
  obtain ⟨V, hV⟩ : ∃ V : Finset ℝ,
      V = insert (M / 2) ((B.filter (fun q => φ q < M)).image φ) := ⟨_, rfl⟩
  have hVne : V.Nonempty := hV ▸ Finset.insert_nonempty _ _
  have hhalf : M / 2 ≤ V.max' hVne := V.le_max' _ (by rw [hV]; exact Finset.mem_insert_self _ _)
  have hVlt : ∀ x ∈ V, x < M := by
    intro x hx
    rw [hV, Finset.mem_insert, Finset.mem_image] at hx
    rcases hx with rfl | ⟨q, hq, rfl⟩
    · linarith
    · exact (Finset.mem_filter.mp hq).2
  refine ⟨B.filter (fun q => φ q = M), M, V.max' hVne, fun q hq =>
    ((hmemB q).mp (Finset.mem_filter.mp hq).1).2, ⟨qs, Finset.mem_filter.mpr ⟨hqsB, hM.symm⟩⟩,
    by linarith, hhalf, hVlt _ (V.max'_mem hVne), fun q hq => (Finset.mem_filter.mp hq).2, ?_⟩
  intro q hqD hqG
  by_cases hqH : |(q.1 : ℂ).im| ≤ H
  · have hqB : q ∈ B := (hmemB q).mpr ⟨hqH, hqD⟩
    have hle : φ q ≤ M := hM ▸ hqsmax q hqB
    have hne : φ q ≠ M := fun h => hqG (Finset.mem_filter.mpr ⟨hqB, h⟩)
    have hlt : φ q < M := lt_of_le_of_ne hle hne
    exact V.le_max' _ (by
      rw [hV]
      exact Finset.mem_insert_of_mem (Finset.mem_image_of_mem φ (Finset.mem_filter.mpr ⟨hqB, hlt⟩)))
  · push Not at hqH
    have h1 := hdecay q hqD hqH
    linarith

/-- A budget exponent: `A e^{4 − L} ≤ b` for some `L ≥ 0`, when `A ≥ 0` and `b > 0`. -/
theorem exists_exp_budget {A b : ℝ} (hA : 0 ≤ A) (hb : 0 < b) :
    ∃ L : ℝ, 0 ≤ L ∧ A * Real.exp (4 - L) ≤ b := by
  have hx : 1 ≤ A / b + 1 := by have := div_nonneg hA hb.le; linarith
  refine ⟨4 + Real.log (A / b + 1), by linarith [Real.log_nonneg hx], ?_⟩
  have e : Real.exp (4 - (4 + Real.log (A / b + 1))) = (A / b + 1)⁻¹ := by
    rw [show 4 - (4 + Real.log (A / b + 1)) = -Real.log (A / b + 1) by ring, Real.exp_neg,
      Real.exp_log (by linarith)]
  rw [e, ← div_eq_mul_inv, div_le_iff₀ (by linarith)]
  have : b * (A / b + 1) = A + b := by field_simp
  linarith

/-! ## One dyadic shell -/

/-- **One shell.**  All constants fixed and all asymptotic conditions met at `N`, some constant
vector `z` with `|z| ≤ BY/(c₁ E_α(N))` makes the test on the shell `(N, 2N]` negative. -/
theorem jasConst_shell_exists_neg_at {N : ℕ}
    {σ δ α f₁ f₂ ε c₁ ρ₂ W wmin L R₀ BY C₂ Λ₀ ε₂ ε₃ : ℝ} {G F : Finset XiZeroCopy}
    {qs : XiZeroCopy} (hα : α = σ - δ) (hα0 : 0 < α) (hδ : δ < 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ δ)
    (hGF : G ⊆ F) (hqs : qs ∈ G) (hGD : ∀ q ∈ G, |(q.1 : ℂ).re - 1 / 2| = δ)
    (hGval : ∀ q ∈ G, jasShellFactor α |(q.1 : ℂ).im| = f₁)
    (hrest : ∀ q ∈ F, |(q.1 : ℂ).re - 1 / 2| = δ → q ∉ G →
      jasShellFactor α |(q.1 : ℂ).im| ≤ f₂)
    (hf₂ : f₂ < f₁) (hhalf : f₁ / 2 ≤ f₂) (hε : ε = (f₁ - f₂) / 4)
    (hc₁ : c₁ = f₁ - ε) (hρ₂ : ρ₂ = (f₂ + ε) / c₁)
    (hwmin : ∀ q ∈ G, wmin ≤ ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) (hwmin0 : 0 < wmin)
    (hW : W = ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖)
    (hL : 0 ≤ L) (hLbig : 2 * W * Real.exp (4 - L) ≤ (1 / 4 - δ ^ 2) * wmin / 4)
    (hR₀ : R₀ = 1 + 2 * L / (1 - ρ₂) ^ 2)
    (hBY : BY = antiAlignLadder (1 / 4 - δ ^ 2) L R₀ (2 * G.card) + 4)
    (hΛ₀ : Λ₀ = 2 * BY * C₂ / c₁)
    (hFtail : (∑' q : {x // x ∉ F}, ‖1 / ((q.1.1 : ℂ) * (1 - (q.1.1 : ℂ)))‖) *
      (2 * Real.exp Λ₀) ≤ (1 / 4 - δ ^ 2) * wmin * Real.exp R₀ / 8)
    (hε₂ : ε₂ * C₂ ≤ f₂ + ε) (hε₂0 : 0 ≤ ε₂)
    (hε₃ : ε₃ * C₂ * BY ≤ (1 / 4 - δ ^ 2) * c₁ / 24) (hε₃0 : 0 ≤ ε₃)
    (hN : 2 ≤ N)
    (hA1 : BY / (c₁ * jasMainScale α N) ≤ 1 / 4)
    (hAΛ : 2 * (BY / (c₁ * jasMainScale α N)) * Λ₀ ≤ (1 / 4 - δ ^ 2) / 24)
    (hAY : BY * (BY / (c₁ * jasMainScale α N)) ≤ (1 / 4 - δ ^ 2) / 24)
    (hsh : ∀ q ∈ F, |(q.1 : ℂ).re - 1 / 2| = δ →
      |‖jasWindowSum N (2 * N) ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I)‖ -
        jasShellFactor α |(q.1 : ℂ).im| * jasMainScale α N| ≤ ε * jasMainScale α N)
    (hrp : jasPrimeRpowSum α (2 * N) ≤ C₂ * jasMainScale α N)
    (hσ : jasPrimeRpowSum σ (2 * N) ≤ ε₃ * jasPrimeRpowSum α (2 * N))
    (hsha : ∀ q ∈ F, |(q.1 : ℂ).re - 1 / 2| < δ →
      jasPrimeRpowSum (σ - |(q.1 : ℂ).re - 1 / 2|) (2 * N) ≤ ε₂ * jasPrimeRpowSum α (2 * N)) :
    ∃ z : ℂ, ‖z‖ ≤ BY / (c₁ * jasMainScale α N) ∧ (∑' q : XiZeroCopy, jasConstPairTerm
      (jasPrimeWindow N (2 * N)) σ (z / ((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) (q.1 : ℂ)).re < 0 := by
  classical
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = jasMainScale α N := ⟨_, rfl⟩
  rw [← hE] at hA1 hAΛ hAY hsh hrp ⊢
  have hE0 : 0 < E := hE ▸ jasMainScale_pos hN
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / 4 - δ ^ 2 := ⟨_, rfl⟩
  rw [← hc] at hLbig hBY hFtail hε₃ hAΛ hAY
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans (hmax qs)
  have hc0 : 0 < c := by rw [hc]; nlinarith
  have hc1 : c ≤ 1 := by rw [hc]; nlinarith
  have hf₁0 : 0 < f₁ := by linarith
  have hε0 : 0 < ε := by rw [hε]; linarith
  have hc₁0 : 0 < c₁ := by rw [hc₁, hε]; linarith
  have hρ₂0 : 0 ≤ ρ₂ := by rw [hρ₂]; exact div_nonneg (by linarith) hc₁0.le
  have hρ₂1 : ρ₂ < 1 := by rw [hρ₂, div_lt_one hc₁0, hc₁, hε]; linarith
  have hρc : ρ₂ * c₁ = f₂ + ε := by rw [hρ₂]; field_simp
  obtain ⟨P, hP⟩ : ∃ P : Finset Nat.Primes, P = jasPrimeWindow N (2 * N) := ⟨_, rfl⟩
  rw [← hP]
  -- the large sums at distance `δ`
  have hbigD : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| = δ →
      ‖jasBigSum P σ (q.1 : ℂ)‖ =
        ‖jasWindowSum N (2 * N) ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I)‖ := by
    intro q hq
    rw [norm_jasBigSum_eq, hq, ← hα, jasWindowSum_eq_jasCpowSum, hP]
  -- the maximizer on `G`
  obtain ⟨qm, hqm, hqmmax⟩ := G.exists_max_image (fun q => ‖jasBigSum P σ (q.1 : ℂ)‖) ⟨qs, hqs⟩
  have hSlow : c₁ * E ≤ ‖jasBigSum P σ (qm.1 : ℂ)‖ := by
    have h1 := hqmmax qs hqs
    have h2 := hsh qs (hGF hqs) (hGD qs hqs)
    rw [hGval qs hqs, ← hbigD qs (hGD qs hqs)] at h2
    have h3 := (abs_le.mp h2).1
    have e : c₁ * E = f₁ * E - ε * E := by rw [hc₁]; ring
    linarith
  have hSpos : 0 < ‖jasBigSum P σ (qm.1 : ℂ)‖ := lt_of_lt_of_le (mul_pos hc₁0 hE0) hSlow
  have hS0 : jasBigSum P σ (qm.1 : ℂ) ≠ 0 := norm_pos_iff.mp hSpos
  -- competitors
  have hcomp : ∀ q ∈ F, q ∉ G →
      ‖jasBigSum P σ (q.1 : ℂ)‖ ≤ ρ₂ * ‖jasBigSum P σ (qm.1 : ℂ)‖ := by
    intro q hqF hqG
    have hgoal : ‖jasBigSum P σ (q.1 : ℂ)‖ ≤ (f₂ + ε) * E := by
      rcases lt_or_eq_of_le (hmax q) with hlt | hd
      · have h1 := norm_jasBigSum_le P σ (q.1 : ℂ)
        have h2 := sum_jasPrimeWindow_le_jasPrimeRpowSum N (2 * N) (σ - |(q.1 : ℂ).re - 1 / 2|)
        rw [← hP] at h2
        have h3 := hsha q hqF hlt
        have h4 : ε₂ * jasPrimeRpowSum α (2 * N) ≤ ε₂ * (C₂ * E) :=
          mul_le_mul_of_nonneg_left hrp hε₂0
        have h5 : ε₂ * (C₂ * E) ≤ (f₂ + ε) * E := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hε₂ hE0.le
        linarith
      · have h1 := hsh q hqF hd
        rw [← hbigD q hd] at h1
        have h3 := (abs_le.mp h1).2
        have h4 : jasShellFactor α |(q.1 : ℂ).im| * E ≤ f₂ * E :=
          mul_le_mul_of_nonneg_right (hrest q hqF hd hqG) hE0.le
        have e : (f₂ + ε) * E = f₂ * E + ε * E := by ring
        linarith
    calc ‖jasBigSum P σ (q.1 : ℂ)‖ ≤ (f₂ + ε) * E := hgoal
      _ = ρ₂ * (c₁ * E) := by rw [← hρc]; ring
      _ ≤ ρ₂ * ‖jasBigSum P σ (qm.1 : ℂ)‖ := mul_le_mul_of_nonneg_left hSlow hρ₂0
  -- the ladder
  have h1ρ : 0 < (1 - ρ₂) ^ 2 := by
    have : 0 < 1 - ρ₂ := by linarith
    positivity
  have hR₀pos : 0 < R₀ := by rw [hR₀]; positivity
  have hfarR : 2 * L / R₀ ≤ (1 - ρ₂) ^ 2 := by
    rw [div_le_iff₀ hR₀pos]
    have hne : (1 - ρ₂) ≠ 0 := (sub_pos.mpr hρ₂1).ne'
    have e : (1 - ρ₂) ^ 2 * (2 * L / (1 - ρ₂) ^ 2) = 2 * L := by field_simp
    rw [hR₀, mul_add, mul_one, e]
    linarith
  have hcw : ∀ q ∈ G, c * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤
      (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := fun q _ =>
    hc ▸ quarter_sub_sq_mul_norm_le_re_one_div hδ (hmax q)
  have hWF : ∑ q ∈ F, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤ W :=
    hW ▸ summable_inv_mul_one_sub.norm.sum_le_tsum F fun _ _ => norm_nonneg _
  -- the amplitude scale
  have hBY0 : 0 < BY := by
    rw [hBY]; linarith [hR₀pos.trans_le (antiAlignLadder_ge (c := c) hL (2 * G.card))]
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = BY / ‖jasBigSum P σ (qm.1 : ℂ)‖ := ⟨_, rfl⟩
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have haA : a ≤ BY / (c₁ * E) := by
    rw [ha]; exact div_le_div_of_nonneg_left hBY0.le (mul_pos hc₁0 hE0) hSlow
  have hPα : ∑ p ∈ P, Real.exp (-(σ - δ) * Real.log p) ≤ C₂ * E := by
    rw [← hα, hP]; exact (sum_jasPrimeWindow_le_jasPrimeRpowSum N (2 * N) α).trans hrp
  have hPα0 : 0 ≤ ∑ p ∈ P, Real.exp (-(σ - δ) * Real.log p) :=
    Finset.sum_nonneg fun p _ => (Real.exp_pos _).le
  have hAE : BY / (c₁ * E) * (C₂ * E) = BY * C₂ / c₁ := by field_simp
  have hΛ : 2 * a * ∑ p ∈ P, Real.exp (-(σ - δ) * Real.log p) ≤ Λ₀ := by
    have h1 := mul_le_mul haA hPα hPα0 (by positivity)
    rw [hAE] at h1
    rw [hΛ₀]
    have e : 2 * BY * C₂ / c₁ = 2 * (BY * C₂ / c₁) := by ring
    rw [e]; linarith
  have hsq : 2 * a * (2 * a * ∑ p ∈ P, Real.exp (-(σ - δ) * Real.log p)) ≤ c / 24 := by
    have hΛ₀0 : 0 ≤ Λ₀ := by
      have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) ha0) hPα0
      linarith
    have h1 := mul_le_mul_of_nonneg_left hΛ (show 0 ≤ 2 * a by linarith)
    have h2 : 2 * a * Λ₀ ≤ 2 * (BY / (c₁ * E)) * Λ₀ :=
      mul_le_mul_of_nonneg_right (by linarith) hΛ₀0
    linarith
  have hsmall : a * ∑ p ∈ P, Real.exp (-σ * Real.log p) ≤ c / 24 := by
    have h1 := sum_jasPrimeWindow_le_jasPrimeRpowSum N (2 * N) σ
    rw [← hP] at h1
    have h0 : 0 ≤ ∑ p ∈ P, Real.exp (-σ * Real.log p) :=
      Finset.sum_nonneg fun p _ => (Real.exp_pos _).le
    have h2 : ∑ p ∈ P, Real.exp (-σ * Real.log p) ≤ ε₃ * (C₂ * E) :=
      h1.trans (hσ.trans (mul_le_mul_of_nonneg_left hrp hε₃0))
    have h3 := mul_le_mul haA h2 h0 (by positivity)
    have e : BY / (c₁ * E) * (ε₃ * (C₂ * E)) = ε₃ * C₂ * BY / c₁ := by field_simp
    rw [e] at h3
    have h4 : ε₃ * C₂ * BY / c₁ ≤ c / 24 := by
      rw [div_le_iff₀ hc₁0]; linarith
    linarith
  have hYa : (antiAlignLadder c L R₀ (2 * G.card) + 4) * a ^ 2 ≤ c / 24 := by
    rw [← hBY]
    have h1 : a ≤ 1 := by linarith
    have h2 : BY * a ≤ c / 24 := (mul_le_mul_of_nonneg_left haA hBY0.le).trans hAY
    have h3 : BY * a ^ 2 ≤ BY * a := by
      have := mul_le_mul_of_nonneg_left (mul_le_of_le_one_left ha0 h1) hBY0.le
      rw [sq]; linarith
    linarith
  have ha' : a = (antiAlignLadder c L R₀ (2 * G.card) + 4) / ‖jasBigSum P σ (qm.1 : ℂ)‖ := by
    rw [ha, hBY]
  obtain ⟨z, hzn, hz⟩ := exists_jasConstPairTerm_tsum_neg hGF hqm hqmmax hcomp hρ₂1 hfarR hS0
    hmax (by rw [← hα]; exact hα0) hc0 hc1 hcw hwmin hwmin0 hR₀pos hL hWF hLbig ha' (by linarith)
    hsq hsmall hYa hΛ hFtail
  exact ⟨z, hzn.trans haA, hz⟩

/-! ## Every large dyadic shell -/

/-- **A small complex constant vector detects a maximal off-line zero on every large dyadic
shell.**  If a zero off the critical line has the largest distance `δ` from it among all zeros,
`δ < σ < 1 + δ` and `β < 1 + δ − σ`, then for every sufficiently large `N` some `z ∈ ℂ` with
`|z| ≤ N^{−β}` makes the constant-vector JAS test on the primes in `(N, 2N]` negative. -/
theorem eventually_exists_small_neg_shell_of_maximal_offLine (q₀ : XiZeroCopy)
    (hoff : (q₀.1 : ℂ).re ≠ 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) {σ β : ℝ}
    (hσ0 : |(q₀.1 : ℂ).re - 1 / 2| < σ) (hσ1 : σ < 1 + |(q₀.1 : ℂ).re - 1 / 2|)
    (hβ : β < 1 + |(q₀.1 : ℂ).re - 1 / 2| - σ) :
    ∀ᶠ N : ℕ in atTop, ∃ z : ℂ, ‖z‖ ≤ (N : ℝ) ^ (-β) ∧ (∑' q : XiZeroCopy, jasConstPairTerm
      (jasPrimeWindow N (2 * N)) σ (z / ((1 + ‖z‖ ^ 2 : ℝ) : ℂ)) (q.1 : ℂ)).re < 0 := by
  classical
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = |(q₀.1 : ℂ).re - 1 / 2| := ⟨_, rfl⟩
  rw [← hδ] at hmax hσ0 hσ1 hβ
  have hδ0 : 0 < δ := by rw [hδ]; exact abs_pos.mpr (sub_ne_zero.mpr hoff)
  have hδ1 : δ < 1 / 2 := by
    have h0 := xiZeroCopy_re_pos q₀
    have h1 := xiZeroCopy_re_lt_one q₀
    rw [hδ, abs_lt]; constructor <;> linarith
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = σ - δ := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; linarith
  have hα1 : α < 1 := by rw [hα]; linarith
  have h1α : 0 < 1 - α := by linarith
  -- the tie group
  obtain ⟨φ₀, hφ₀⟩ : ∃ φ₀ : ℝ, φ₀ = jasShellFactor α |(q₀.1 : ℂ).im| := ⟨_, rfl⟩
  have hφ0 : 0 < φ₀ := hφ₀ ▸ jasShellFactor_pos hα1 _
  have hdecay : ∀ q ∈ {q : XiZeroCopy | |(q.1 : ℂ).re - 1 / 2| = δ}, 6 / φ₀ < |(q.1 : ℂ).im| →
      jasShellFactor α |(q.1 : ℂ).im| ≤ φ₀ / 2 := by
    intro q _ hq
    have hpos : 0 < |(q.1 : ℂ).im| := (by positivity : (0 : ℝ) < 6 / φ₀).trans hq
    have h1 := jasShellFactor_mul_abs_le hα0 |(q.1 : ℂ).im|
    rw [abs_abs] at h1
    have h2 : jasShellFactor α |(q.1 : ℂ).im| ≤ 3 / |(q.1 : ℂ).im| := by
      rw [le_div_iff₀ hpos]; exact h1
    have h3 : 3 / |(q.1 : ℂ).im| ≤ 3 / (6 / φ₀) :=
      div_le_div_of_nonneg_left (by norm_num) (by positivity) hq.le
    have h4 : 3 / (6 / φ₀) = φ₀ / 2 := by field_simp; ring
    linarith
  obtain ⟨G, f₁, f₂, hGD, hGne, -, hhalf, hf₂, hGval, hrestD⟩ :=
    exists_top_group {q : XiZeroCopy | |(q.1 : ℂ).re - 1 / 2| = δ}
      (fun q => jasShellFactor α |(q.1 : ℂ).im|) (q₀ := q₀) hδ.symm (hφ₀ ▸ hφ0)
      (H := 6 / φ₀) (by positivity) (by rw [← hφ₀]; exact hdecay)
  obtain ⟨qs, hqs⟩ := hGne
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (f₁ - f₂) / 4 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hε]; linarith
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = f₁ - ε := ⟨_, rfl⟩
  have hc₁0 : 0 < c₁ := by rw [hc₁, hε]; linarith
  obtain ⟨ρ₂, hρ₂⟩ : ∃ ρ₂ : ℝ, ρ₂ = (f₂ + ε) / c₁ := ⟨_, rfl⟩
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = 1 / 4 - δ ^ 2 := ⟨_, rfl⟩
  have hc0 : 0 < c := by rw [hc]; nlinarith
  -- weights
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
    ⟨_, rfl⟩
  have hW0 : 0 ≤ W := by rw [hW]; exact tsum_nonneg fun _ => norm_nonneg _
  obtain ⟨qw, -, hqwmin⟩ :=
    G.exists_min_image (fun q => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) ⟨qs, hqs⟩
  obtain ⟨wmin, hwmin⟩ : ∃ wmin : ℝ, wmin = ‖1 / ((qw.1 : ℂ) * (1 - (qw.1 : ℂ)))‖ := ⟨_, rfl⟩
  have hwmin0 : 0 < wmin := by
    rw [hwmin]
    refine norm_pos_iff.mpr (one_div_ne_zero (mul_ne_zero ?_ ?_))
    · intro h
      have := xiZeroCopy_re_pos qw
      rw [h, Complex.zero_re] at this
      exact lt_irrefl _ this
    · intro h
      have := xiZeroCopy_re_lt_one qw
      have h' : (qw.1 : ℂ) = 1 := by linear_combination -h
      rw [h', Complex.one_re] at this
      exact lt_irrefl _ this
  have hwminG : ∀ q ∈ G, wmin ≤ ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := fun q hq =>
    hwmin ▸ hqwmin q hq
  obtain ⟨L, hL0, hLbig⟩ := exists_exp_budget (A := 2 * W) (b := c * wmin / 4) (by positivity)
    (by positivity)
  obtain ⟨R₀, hR₀⟩ : ∃ R₀ : ℝ, R₀ = 1 + 2 * L / (1 - ρ₂) ^ 2 := ⟨_, rfl⟩
  have hR₀1 : 1 ≤ R₀ := by
    rw [hR₀]; have : 0 ≤ 2 * L / (1 - ρ₂) ^ 2 := by positivity
    linarith
  obtain ⟨BY, hBY⟩ : ∃ BY : ℝ, BY = antiAlignLadder c L R₀ (2 * G.card) + 4 := ⟨_, rfl⟩
  have hBY0 : 0 < BY := by
    rw [hBY]; linarith [antiAlignLadder_ge (c := c) (R₀ := R₀) hL0 (2 * G.card)]
  obtain ⟨C₂, hC₂⟩ : ∃ C₂ : ℝ, C₂ = 2 * (1 / (1 - α) + 1) := ⟨_, rfl⟩
  have hC₂0 : 0 < C₂ := by rw [hC₂]; positivity
  obtain ⟨Λ₀, hΛ₀⟩ : ∃ Λ₀ : ℝ, Λ₀ = 2 * BY * C₂ / c₁ := ⟨_, rfl⟩
  have hΛ₀0 : 0 ≤ Λ₀ := by rw [hΛ₀]; positivity
  -- the finite set
  obtain ⟨F, hFtail, hGF⟩ : ∃ F : Finset XiZeroCopy,
      (∑' q : {x // x ∉ F}, ‖1 / ((q.1.1 : ℂ) * (1 - (q.1.1 : ℂ)))‖) * (2 * Real.exp Λ₀) ≤
        c * wmin * Real.exp R₀ / 8 ∧ G ⊆ F := by
    have hpos : 0 < c * wmin * Real.exp R₀ / 8 / (2 * Real.exp Λ₀) := by positivity
    have h1 := (tendsto_tsum_compl_atTop_zero
      (fun q : XiZeroCopy => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖)).eventually (gt_mem_nhds hpos)
    have h2 : ∀ᶠ F : Finset XiZeroCopy in atTop, G ⊆ F := eventually_ge_atTop G
    obtain ⟨F, hF1, hF2⟩ := (h1.and h2).exists
    refine ⟨F, ?_, hF2⟩
    rw [lt_div_iff₀ (by positivity)] at hF1
    exact hF1.le
  -- tolerances
  obtain ⟨ε₂, hε₂⟩ : ∃ ε₂ : ℝ, ε₂ = (f₂ + ε) / C₂ := ⟨_, rfl⟩
  have hε₂0 : 0 < ε₂ := by rw [hε₂]; exact div_pos (by linarith) hC₂0
  have hε₂C : ε₂ * C₂ ≤ f₂ + ε := le_of_eq (by rw [hε₂]; field_simp)
  obtain ⟨ε₃, hε₃⟩ : ∃ ε₃ : ℝ, ε₃ = c * c₁ / (24 * C₂ * BY) := ⟨_, rfl⟩
  have hε₃0 : 0 < ε₃ := by rw [hε₃]; positivity
  have hε₃C : ε₃ * C₂ * BY ≤ c * c₁ / 24 := le_of_eq (by rw [hε₃]; field_simp)
  obtain ⟨κ, hκ⟩ : ∃ κ : ℝ,
      κ = min (1 / 4) (min (c / (48 * (Λ₀ + 1))) (c / (24 * (BY + 1)))) := ⟨_, rfl⟩
  have hκ0 : 0 < κ := by
    rw [hκ]; exact lt_min (by norm_num) (lt_min (by positivity) (by positivity))
  -- eventual conditions
  have ev1 : ∀ᶠ N : ℕ in atTop, ∀ q ∈ F, |(q.1 : ℂ).re - 1 / 2| = δ →
      |‖jasWindowSum N (2 * N) ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I)‖ -
        jasShellFactor α |(q.1 : ℂ).im| * jasMainScale α N| ≤ ε * jasMainScale α N := by
    refine (Filter.eventually_all_finset F).mpr fun q _ => ?_
    filter_upwards [eventually_abs_norm_shell_sub_le hα0 hα1 |(q.1 : ℂ).im| hε0] with N hN _
      using hN
  have ev2 : ∀ᶠ N : ℕ in atTop, jasPrimeRpowSum α (2 * N) ≤ C₂ * jasMainScale α N := by
    filter_upwards [tendsto_two_mul_atTop.eventually
      (eventually_jasPrimeRpowSum_le_main hα0 hα1 one_pos), eventually_ge_atTop 2] with N hN hN2
    have h0 : 0 ≤ 1 / (1 - α) + 1 := by positivity
    have h1 := mul_le_mul_of_nonneg_left (jasMainScale_two_mul_le hα0.le hN2) h0
    have e : C₂ * jasMainScale α N = (1 / (1 - α) + 1) * (2 * jasMainScale α N) := by
      rw [hC₂]; ring
    rw [e]
    linarith
  have ev3 : ∀ᶠ N : ℕ in atTop, jasPrimeRpowSum σ (2 * N) ≤ ε₃ * jasPrimeRpowSum α (2 * N) :=
    tendsto_two_mul_atTop.eventually
      (eventually_jasPrimeRpowSum_le hα1.le (by rw [hα]; linarith) hε₃0)
  have ev4 : ∀ᶠ N : ℕ in atTop, ∀ q ∈ F, |(q.1 : ℂ).re - 1 / 2| < δ →
      jasPrimeRpowSum (σ - |(q.1 : ℂ).re - 1 / 2|) (2 * N) ≤ ε₂ * jasPrimeRpowSum α (2 * N) := by
    refine (Filter.eventually_all_finset F).mpr fun q _ => ?_
    by_cases hq : |(q.1 : ℂ).re - 1 / 2| < δ
    · filter_upwards [tendsto_two_mul_atTop.eventually (eventually_jasPrimeRpowSum_le hα1.le
        (show α < σ - |(q.1 : ℂ).re - 1 / 2| by rw [hα]; linarith) hε₂0)] with N hN _ using hN
    · exact Eventually.of_forall fun N h => absurd h hq
  have hamp : Tendsto (fun N : ℕ => BY / (c₁ * jasMainScale α N)) atTop (𝓝 0) := by
    have := (tendsto_natLog_div_rpow_atTop h1α).const_mul (BY / c₁)
    rw [mul_zero] at this
    refine this.congr' ((eventually_ge_atTop 2).mono fun N hN => ?_)
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hlog := Real.log_pos hN1
    have hpow : 0 < (N : ℝ) ^ (1 - α) := Real.rpow_pos_of_pos (by linarith) _
    simp only [jasMainScale]
    field_simp
  have ev5 := hamp.eventually (ge_mem_nhds hκ0)
  -- the amplitude bound `BY/(c₁ E_α(N)) ≤ N^{−β}`
  have ev6 : ∀ᶠ N : ℕ in atTop, BY / (c₁ * jasMainScale α N) ≤ (N : ℝ) ^ (-β) := by
    have hγ : 0 < 1 - α - β := by rw [hα]; linarith
    have hlim := (tendsto_natLog_div_rpow_atTop hγ).const_mul (BY / c₁)
    rw [mul_zero] at hlim
    filter_upwards [hlim.eventually (ge_mem_nhds one_pos), eventually_ge_atTop 2] with N hN hN2
    have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
    have hNpos : (0 : ℝ) < N := by linarith
    have hlog := Real.log_pos hN1
    have e : BY / (c₁ * jasMainScale α N) =
        BY / c₁ * (Real.log N / (N : ℝ) ^ (1 - α - β)) * (N : ℝ) ^ (-β) := by
      simp only [jasMainScale]
      have h1 : (N : ℝ) ^ (1 - α - β) * (N : ℝ) ^ β = (N : ℝ) ^ (1 - α) := by
        rw [← Real.rpow_add hNpos]; ring_nf
      have h3 : 0 < (N : ℝ) ^ (1 - α - β) := Real.rpow_pos_of_pos hNpos _
      have h4 : 0 < (N : ℝ) ^ β := Real.rpow_pos_of_pos hNpos _
      rw [Real.rpow_neg hNpos.le, ← h1]
      field_simp
    rw [e]
    exact mul_le_of_le_one_left (Real.rpow_nonneg hNpos.le _) hN
  filter_upwards [ev1, ev2, ev3, ev4, ev5, ev6, eventually_ge_atTop 2] with N h1 h2 h3 h4 h5 h6 hN2
  have hA1 : BY / (c₁ * jasMainScale α N) ≤ 1 / 4 :=
    h5.trans (by rw [hκ]; exact min_le_left _ _)
  have hAΛ : 2 * (BY / (c₁ * jasMainScale α N)) * Λ₀ ≤ c / 24 := by
    have hk : κ ≤ c / (48 * (Λ₀ + 1)) := by
      rw [hκ]; exact (min_le_right _ _).trans (min_le_left _ _)
    have h6 := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (h5.trans hk) (show (0 : ℝ) ≤ 2 by norm_num)) hΛ₀0
    have h7 : 2 * (c / (48 * (Λ₀ + 1))) * Λ₀ ≤ 2 * (c / (48 * (Λ₀ + 1))) * (Λ₀ + 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have h8 : 2 * (c / (48 * (Λ₀ + 1))) * (Λ₀ + 1) = c / 24 := by field_simp; ring
    linarith
  have hAY : BY * (BY / (c₁ * jasMainScale α N)) ≤ c / 24 := by
    have hk : κ ≤ c / (24 * (BY + 1)) := by
      rw [hκ]; exact (min_le_right _ _).trans (min_le_right _ _)
    have h6 := mul_le_mul_of_nonneg_left (h5.trans hk) hBY0.le
    have h7 : BY * (c / (24 * (BY + 1))) ≤ (BY + 1) * (c / (24 * (BY + 1))) :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h8 : (BY + 1) * (c / (24 * (BY + 1))) = c / 24 := by field_simp
    linarith
  subst hc
  obtain ⟨z, hzn, hz⟩ := jasConst_shell_exists_neg_at hα hα0 hδ1 hmax hGF hqs hGD hGval
    (fun q _ hd hqG => hrestD q hd hqG) hf₂ hhalf hε hc₁ hρ₂ hwminG hwmin0 hW hL0 hLbig hR₀ hBY
    hΛ₀ hFtail hε₂C hε₂0.le hε₃C hε₃0.le hN2 hA1 hAΛ hAY h1 h2 h3 h4
  exact ⟨z, hzn.trans h6, hz⟩


/-- **A complex constant vector detects a maximal off-line zero on every large dyadic shell.**  If a
zero off the critical line has the largest distance `δ` from it among all zeros, and
`δ < σ < 1 + δ`, then for every sufficiently large `N` the constant-vector JAS test on the primes in
`(N, 2N]` is negative for some `z ∈ ℂ`. -/
theorem eventually_not_jasConstProductPositiveOn_shell_of_maximal_offLine (q₀ : XiZeroCopy)
    (hoff : (q₀.1 : ℂ).re ≠ 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) {σ : ℝ}
    (hσ0 : |(q₀.1 : ℂ).re - 1 / 2| < σ) (hσ1 : σ < 1 + |(q₀.1 : ℂ).re - 1 / 2|) :
    ∀ᶠ N : ℕ in atTop, ¬ JasConstProductPositiveOn (jasPrimeWindow N (2 * N)) σ := by
  filter_upwards [eventually_exists_small_neg_shell_of_maximal_offLine q₀ hoff hmax hσ0 hσ1
    (β := 0) (by linarith)] with N hN hpos
  obtain ⟨z, -, hz⟩ := hN
  exact absurd (re_tsum_jasConstPairTerm_nonneg hpos z) (not_le.mpr hz)

/-! ## Capstones -/

/-- Under RH the constant-vector tests are positive on every dyadic shell above some height. -/
theorem frequently_jasConstProductPositiveOn_shell_of_riemannHypothesis
    (hRH : RiemannHypothesis) :
    ∃ᶠ N : ℕ in atTop, JasConstProductPositiveOn (jasPrimeWindow N (2 * N)) 1 := by
  obtain ⟨X, hX⟩ := riemannHypothesis_iff_exists_jasProductPositiveAbove_one.mp hRH
  refine (eventually_ge_atTop X).frequently.mono fun N hN => ?_
  exact hX.constOn fun p hp => lt_of_le_of_lt hN (mem_jasPrimeWindow.mp hp).1

/-- A maximal off-line zero excludes level-one constant-vector positivity on infinitely many
dyadic shells. -/
theorem not_frequently_jasConstProductPositiveOn_shell_of_maximal_offLine (q₀ : XiZeroCopy)
    (hoff : (q₀.1 : ℂ).re ≠ 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) :
    ¬ ∃ᶠ N : ℕ in atTop, JasConstProductPositiveOn (jasPrimeWindow N (2 * N)) 1 := by
  intro hfr
  have hδ0 : 0 < |(q₀.1 : ℂ).re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hoff)
  have hδ1 : |(q₀.1 : ℂ).re - 1 / 2| < 1 := by
    have h0 := xiZeroCopy_re_pos q₀
    have h1 := xiZeroCopy_re_lt_one q₀
    rw [abs_lt]; constructor <;> linarith
  have hev := eventually_not_jasConstProductPositiveOn_shell_of_maximal_offLine q₀ hoff hmax
    (σ := 1) hδ1 (by linarith)
  obtain ⟨N, hN, hN'⟩ := (hfr.and_eventually hev).exists
  exact hN' hN

/-- **RH ⟺ the zeros approach the line ∧ level-one constant-vector positivity on infinitely many
dyadic shells `(N, 2N]`.** -/
theorem riemannHypothesis_iff_zerosApproachLine_and_frequently_jasConstProductPositiveOn_shell :
    RiemannHypothesis ↔ BacklundConverse.ZerosApproachLine ∧
      ∃ᶠ N : ℕ in atTop, JasConstProductPositiveOn (jasPrimeWindow N (2 * N)) 1 := by
  constructor
  · intro hRH
    exact ⟨zerosApproachLine_of_riemannHypothesis hRH,
      frequently_jasConstProductPositiveOn_shell_of_riemannHypothesis hRH⟩
  · rintro ⟨hZ, hfr⟩
    by_contra hRH
    obtain ⟨Θ, hΘ, q₀, hq₀, hmaxq⟩ := attainedTopExcess_of_zerosApproachLine hZ hRH
    have habs : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| = |(q.1 : ℂ).re - 1 / 2| := fun q => by
      rw [LindelofSparse.spectral_im_eq, abs_sub_comm]
    have hq₀' : |(q₀.1 : ℂ).re - 1 / 2| = Θ := by rw [← habs]; exact hq₀
    have hoff : (q₀.1 : ℂ).re ≠ 1 / 2 := fun h => by
      rw [h, sub_self, abs_zero] at hq₀'; linarith
    have hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2| := fun q => by
      rw [hq₀', ← habs]; exact hmaxq q
    exact not_frequently_jasConstProductPositiveOn_shell_of_maximal_offLine q₀ hoff hmax hfr

/-- **RH ⟺ no off-line chain ∧ level-one constant-vector positivity on infinitely many dyadic
shells `(N, 2N]`.** -/
theorem riemannHypothesis_iff_not_jasOffLineChain_and_frequently_jasConstProductPositiveOn_shell :
    RiemannHypothesis ↔ ¬ JasOffLineChain ∧
      ∃ᶠ N : ℕ in atTop, JasConstProductPositiveOn (jasPrimeWindow N (2 * N)) 1 := by
  constructor
  · intro hRH
    refine ⟨fun ⟨⟨q, hq⟩, _⟩ => hq (xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q),
      frequently_jasConstProductPositiveOn_shell_of_riemannHypothesis hRH⟩
  · rintro ⟨hno, hfr⟩
    by_contra hRH
    obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_re_gt_half_of_not_riemannHypothesis hRH
    have hnot : ¬ ∀ q₀ : XiZeroCopy, (q₀.1 : ℂ).re ≠ 1 / 2 →
        ∃ q : XiZeroCopy, |(q₀.1 : ℂ).re - 1 / 2| < |(q.1 : ℂ).re - 1 / 2| :=
      fun h => hno ⟨⟨q₁, ne_of_gt hq₁⟩, h⟩
    push Not at hnot
    obtain ⟨q₀, hoff, hmax⟩ := hnot
    exact not_frequently_jasConstProductPositiveOn_shell_of_maximal_offLine q₀ hoff hmax hfr

end

end RHTower
