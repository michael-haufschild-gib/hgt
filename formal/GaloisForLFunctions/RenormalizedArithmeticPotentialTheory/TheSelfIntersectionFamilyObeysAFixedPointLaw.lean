import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheTorsionCountertermIsTheGoldenRatio

/-!
# The self-intersection family obeys a fixed-point law

Weight the self-intersection by `α ∈ ℝ`: `T_α = α diag(log n) + P_N` on `[1, N]`. Its spectrum fills
`[κ₋ log N, κ₊ log N]` up to `O(1)`, where `κ₊ > 0 > κ₋ = −1/κ₊` are the roots of `κ² = ακ + 1`,
i.e. the fixed points `κ = α + 1/κ`. At `α = 0` this is `[−log N, log N]`; at `α = 1` (torsion) it is
`[−log N/φ, φ log N]`.

* **The `κ`-twisted ground-state identity** (`fixedPoint_identity`): for `κ ≠ 0` and `α = κ − 1/κ`,
  `α Σ log n · x_n² + P_N(x) + D_κ(x)/κ = κ Σ (A(⌊N/n⌋) + log n) x_n²`, with the twisted pole
  defect `D_κ(x) = Σ_{mt ≤ N} Λ(t)(x_{mt} − κ x_m/√t)² ≥ 0`. At `κ = 1` it is the ground-state
  identity of the prime form.
* **The ends** (`fixedPoint_top`, `fixedPoint_bottom`): for `κ > 0`, `T_α ≤ κ(log N + log 4 + 4)`;
  for `κ < 0`, `T_α ≥ κ(log N + log 4 + 4)`. The vector `x_n = κ^{ω(n)}/√n` satisfies every coprime
  twisted pole relation exactly, and its non-coprime edges carry `(1 − κ)²` times the tame different,
  `O(1)` on average; so `T_α(x) = κ log N |x|² + O(|x|²)` and both ends are attained.

* **The semicircle law** (`abs_atomicWeilForm_le_semicircle`): with `H = Σ log n · x_n²`,
  `S = |x|²`, `L′ = log N + log 4 + 4`: `|P_N(x)| ≤ 2√(H(L′S − H))`. In the limit the joint numerical
  range of `(log n/log N, P_N/log N)` is the disk `v² ≤ 4u(1 − u)`, whose support function in the
  direction `(α, 1)` is `κ₊(α)`: height and prime form are the two components of a large spin.

The extremal charges are multiplicative: each new prime factor multiplies the charge by `κ±`, the
fixed point of `z ↦ α + 1/z`. The top end at `α = 1` is the torsion counterterm `φ log N`
(`TheTorsionCountertermIsTheGoldenRatio`); the bottom end, `−log N/φ` with alternating charges
`(−1/φ)^{ω(n)}`, is the largest positive square of the renormalized torsion form.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory
  GaloisForLFunctions.ArithmeticElectrostatics GaloisForLFunctions.ArithmeticIntersectionTheory

/-! ### 1. The twisted ground-state identity -/

/-- The **`κ`-twisted pole defect** `D_κ(x) = Σ_{mt ≤ N} Λ(t)(x_{mt} − κ x_m/√t)²`. -/
def twistedPoleDefect (κ : ℝ) (N : ℕ) (x : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Icc 1 N, ∑ t ∈ Icc 1 (N / m), Λ t * (x (m * t) - κ * x m / Real.sqrt t) ^ 2

theorem twistedPoleDefect_nonneg (κ : ℝ) (N : ℕ) (x : ℕ → ℝ) : 0 ≤ twistedPoleDefect κ N x :=
  sum_nonneg fun _ _ => sum_nonneg fun _ _ => mul_nonneg vonMangoldt_nonneg (sq_nonneg _)

/-- `D_κ = Σ log n · x_n² − κ P_N(x) + κ² Σ A(⌊N/m⌋) x_m²`. -/
theorem twistedPoleDefect_eq (κ : ℝ) (N : ℕ) (x : ℕ → ℝ) :
    twistedPoleDefect κ N x = ∑ n ∈ Icc 1 N, Real.log n * x n ^ 2 - κ * atomicWeilForm N x +
      κ ^ 2 * ∑ m ∈ Icc 1 N, mertensSum (N / m) * x m ^ 2 := by
  have hm : ∀ m ∈ Icc 1 N,
      ∑ t ∈ Icc 1 (N / m), Λ t * (x (m * t) - κ * x m / Real.sqrt t) ^ 2 =
        ∑ t ∈ Icc 1 (N / m), Λ t * x (m * t) ^ 2 -
          κ * (2 * ∑ t ∈ Icc 1 (N / m), Λ t / Real.sqrt t * (x m * x (m * t))) +
          κ ^ 2 * (mertensSum (N / m) * x m ^ 2) := by
    intro m _
    rw [mertensSum, sum_mul, mul_sum, mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun t ht => ?_
    have ht0 : (0 : ℝ) < t := by exact_mod_cast (mem_Icc.mp ht).1
    have hs0 : Real.sqrt t ≠ 0 := (Real.sqrt_pos.mpr ht0).ne'
    have hsq : (x (m * t) - κ * x m / Real.sqrt t) ^ 2 =
        x (m * t) ^ 2 - 2 * κ * (x m * x (m * t)) / Real.sqrt t + κ ^ 2 * (x m ^ 2 / t) := by
      rw [sub_sq, div_pow, mul_pow, Real.sq_sqrt ht0.le]; ring
    rw [hsq]
    field_simp
  rw [twistedPoleDefect, sum_congr rfl hm, sum_add_distrib, sum_sub_distrib, ← mul_sum,
    ← mul_sum, ← mul_sum, ← sum_log_mul_sq_eq_edges, ← atomicWeilForm_eq_edges]

/-- **The fixed-point identity.** For `κ ≠ 0` and `α = κ − 1/κ`,
`α Σ log n · x_n² + P_N(x) + D_κ(x)/κ = κ Σ (A(⌊N/n⌋) + log n) x_n²`. -/
theorem fixedPoint_identity {κ : ℝ} (hκ : κ ≠ 0) (N : ℕ) (x : ℕ → ℝ) :
    (κ - 1 / κ) * ∑ n ∈ Icc 1 N, Real.log n * x n ^ 2 + atomicWeilForm N x +
        twistedPoleDefect κ N x / κ =
      κ * ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * x n ^ 2 := by
  rw [twistedPoleDefect_eq]
  have hsplit : ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * x n ^ 2 =
      ∑ n ∈ Icc 1 N, mertensSum (N / n) * x n ^ 2 + ∑ n ∈ Icc 1 N, Real.log n * x n ^ 2 := by
    rw [← sum_add_distrib]; exact sum_congr rfl fun n _ => by ring
  rw [hsplit]
  field_simp
  ring

/-- `Σ (A(⌊N/n⌋) + log n) x_n² ≤ (log N + log 4 + 4) |x|²`. -/
theorem sum_row_mul_sq_le (N : ℕ) (x : ℕ → ℝ) :
    ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * x n ^ 2 ≤
      (Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  rw [mul_sum]
  exact sum_le_sum fun n hn => mul_le_mul_of_nonneg_right
    (row_le (mem_Icc.mp hn).1 (mem_Icc.mp hn).2) (sq_nonneg _)

/-- `Σ (A(⌊N/n⌋) + log n) x_n² ≥ (log N − log 2 − log 4 − 4) |x|²`. -/
theorem sum_row_mul_sq_ge (N : ℕ) (x : ℕ → ℝ) :
    (Real.log N - (Real.log 2 + (Real.log 4 + 4))) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤
      ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * x n ^ 2 := by
  rw [mul_sum]
  refine sum_le_sum fun m hm => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  obtain ⟨hm1, hmN⟩ := mem_Icc.mp hm
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm1
  have hq : 1 ≤ N / m := (Nat.le_div_iff_mul_le hm1).mpr (by linarith)
  have hq0 : (0 : ℝ) < ((N / m : ℕ) : ℝ) := by exact_mod_cast hq
  have hmert := (abs_le.mp (RHTower.Mertens.mertens_first (N / m) hq)).1
  have hN2 : (N : ℝ) ≤ 2 * m * ((N / m : ℕ) : ℝ) := by
    have h1 := Nat.lt_div_mul_add (a := N) hm1
    have h2 : N ≤ 2 * m * (N / m) := by nlinarith
    exact_mod_cast h2
  have hlog : Real.log N ≤ Real.log 2 + Real.log m + Real.log ((N / m : ℕ) : ℝ) := by
    rw [← Real.log_mul (by norm_num) hm0.ne', ← Real.log_mul (by positivity) hq0.ne']
    exact Real.log_le_log (by exact_mod_cast (show 0 < N by omega)) hN2
  simp only [mertensSum]
  linarith

/-! ### 2. The two ends -/

/-- **The top end** (`κ > 0`): `(κ − 1/κ) Σ log n · x_n² + P_N(x) ≤ κ (log N + log 4 + 4)|x|²`. -/
theorem fixedPoint_top_le {κ : ℝ} (hκ : 0 < κ) (N : ℕ) (x : ℕ → ℝ) :
    (κ - 1 / κ) * ∑ n ∈ Icc 1 N, Real.log n * x n ^ 2 + atomicWeilForm N x ≤
      κ * (Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2 := by
  have hid := fixedPoint_identity hκ.ne' N x
  have hD : 0 ≤ twistedPoleDefect κ N x / κ := div_nonneg (twistedPoleDefect_nonneg κ N x) hκ.le
  have hrow := mul_le_mul_of_nonneg_left (sum_row_mul_sq_le N x) hκ.le
  linarith

/-- **The bottom end** (`κ < 0`): `(κ − 1/κ) Σ log n · x_n² + P_N(x) ≥ κ (log N + log 4 + 4)|x|²`. -/
theorem fixedPoint_bottom_ge {κ : ℝ} (hκ : κ < 0) (N : ℕ) (x : ℕ → ℝ) :
    κ * (Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤
      (κ - 1 / κ) * ∑ n ∈ Icc 1 N, Real.log n * x n ^ 2 + atomicWeilForm N x := by
  have hid := fixedPoint_identity hκ.ne N x
  have hD : twistedPoleDefect κ N x / κ ≤ 0 :=
    div_nonpos_of_nonneg_of_nonpos (twistedPoleDefect_nonneg κ N x) hκ.le
  have hrow := mul_le_mul_of_nonpos_left (sum_row_mul_sq_le N x) hκ.le
  linarith

/-! ### 3. The extremal charges `κ^{ω(n)}` -/

/-- The weight `w^{ω(n)}`. -/
def omegaWeight (w : ℝ) (n : ℕ) : ℝ := w ^ n.primeFactors.card

/-- The **fixed-point vector** `x_n = κ^{ω(n)}/√n`. -/
def fixedPointTest (κ : ℝ) (n : ℕ) : ℝ := κ ^ n.primeFactors.card / Real.sqrt n

theorem fixedPointTest_sq (κ : ℝ) (n : ℕ) :
    fixedPointTest κ n ^ 2 = omegaWeight (κ ^ 2) n / n := by
  rw [fixedPointTest, div_pow, Real.sq_sqrt (Nat.cast_nonneg _), omegaWeight, ← pow_mul,
    ← pow_mul, mul_comm]

theorem omegaWeight_nonneg {w : ℝ} (hw : 0 ≤ w) (n : ℕ) : 0 ≤ omegaWeight w n :=
  pow_nonneg hw _

/-- The multiples of `p` carry at most `w/(p − 1)` of the `w^{ω}`-mass. -/
theorem sum_omegaWeight_dvd_le {w : ℝ} (hw : 0 ≤ w) {p : ℕ} (hp : p.Prime) (N : ℕ) :
    ∑ m ∈ (Icc 1 N).filter (fun m => p ∣ m), omegaWeight w m / m ≤
      w / ((p : ℝ) - 1) * ∑ m ∈ Icc 1 N, omegaWeight w m / m := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hr0 : (0 : ℝ) ≤ 1 / p := by positivity
  have hr1 : (1 : ℝ) / p < 1 := by rw [div_lt_one (by linarith)]; exact hp1
  rw [sum_filter, sum_Icc_eq_sum_ladders hp N]
  have hladder : ∀ u ∈ (Icc 1 N).filter (fun u => ¬ p ∣ u),
      ∑ j ∈ range (N + 1), (if u * p ^ j ≤ N then
        (if p ∣ u * p ^ j then omegaWeight w (u * p ^ j) / ((u * p ^ j : ℕ) : ℝ) else 0) else 0) ≤
      w / ((p : ℝ) - 1) * (omegaWeight w u / u) := by
    intro u hu
    obtain ⟨hu1, hpu⟩ := mem_filter.mp hu
    have hu0 : 0 < u := (mem_Icc.mp hu1).1
    have hu0' : (0 : ℝ) < u := by exact_mod_cast hu0
    have hc0 : 0 ≤ w * (omegaWeight w u / u) :=
      mul_nonneg hw (div_nonneg (omegaWeight_nonneg hw u) hu0'.le)
    have hterm : ∀ j ∈ range (N + 1), (if u * p ^ j ≤ N then
        (if p ∣ u * p ^ j then omegaWeight w (u * p ^ j) / ((u * p ^ j : ℕ) : ℝ) else 0) else 0) ≤
        if j = 0 then 0 else w * (omegaWeight w u / u) * (1 / (p : ℝ)) ^ j := by
      intro j _
      rcases Nat.eq_zero_or_pos j with rfl | hj
      · rw [pow_zero, mul_one, if_neg hpu, ite_self, if_pos rfl]
      rw [if_neg hj.ne']
      have hG : omegaWeight w (u * p ^ j) = w * omegaWeight w u := by
        rw [omegaWeight, omegaWeight, card_primeFactors_mul_prime_pow hu0.ne' hp hj.ne',
          if_neg hpu, pow_succ]
        ring
      have hval : omegaWeight w (u * p ^ j) / ((u * p ^ j : ℕ) : ℝ) =
          w * (omegaWeight w u / u) * (1 / (p : ℝ)) ^ j := by
        rw [hG]; push_cast; field_simp
        rw [mul_assoc, ← mul_pow, mul_one_div_cancel (ne_of_gt (by linarith)), one_pow, mul_one]
      have hnn : 0 ≤ w * (omegaWeight w u / u) * (1 / (p : ℝ)) ^ j :=
        mul_nonneg hc0 (pow_nonneg hr0 _)
      split_ifs <;> first | rw [hval] | exact hnn
    have hgeom : ∑ j ∈ range N, (1 / (p : ℝ)) ^ j ≤ 1 / (1 - 1 / (p : ℝ)) := by
      have := geom_sum_Ico_le_of_lt_one (m := 0) (n := N) hr0 hr1
      rwa [← range_eq_Ico, pow_zero] at this
    calc _ ≤ ∑ j ∈ range (N + 1), (if j = 0 then 0 else
          w * (omegaWeight w u / u) * (1 / (p : ℝ)) ^ j) := sum_le_sum hterm
      _ = w * (omegaWeight w u / u) * (1 / (p : ℝ)) * ∑ j ∈ range N, (1 / (p : ℝ)) ^ j := by
          rw [sum_range_succ', if_pos rfl, add_zero, mul_sum]
          exact sum_congr rfl fun j _ => by rw [if_neg (Nat.succ_ne_zero j), pow_succ]; ring
      _ ≤ w * (omegaWeight w u / u) * (1 / (p : ℝ)) * (1 / (1 - 1 / (p : ℝ))) :=
          mul_le_mul_of_nonneg_left hgeom (mul_nonneg hc0 hr0)
      _ = w / ((p : ℝ) - 1) * (omegaWeight w u / u) := by
          have hp0 : (p : ℝ) ≠ 0 := by linarith
          have hp10 : (p : ℝ) - 1 ≠ 0 := by linarith
          field_simp
  refine (sum_le_sum hladder).trans ?_
  rw [← mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (div_nonneg hw (by linarith))
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun u _ _ =>
    div_nonneg (omegaWeight_nonneg hw u) (Nat.cast_nonneg u)

/-- **The tame different on average** under `w^{ω}`: `Σ_m (w^{ω(m)}/m) d(m) ≤ 2wK Σ_m w^{ω(m)}/m`. -/
theorem sum_omegaWeight_tame_le {w : ℝ} (hw : 0 ≤ w) (N : ℕ) :
    ∑ m ∈ Icc 1 N, omegaWeight w m / m * tameDifferent m ≤
      w * (2 * tameConstant) * ∑ m ∈ Icc 1 N, omegaWeight w m / m := by
  set S := ∑ m ∈ Icc 1 N, omegaWeight w m / m
  have hS : 0 ≤ S := sum_nonneg fun m _ => div_nonneg (omegaWeight_nonneg hw m) (Nat.cast_nonneg m)
  have hswap : ∑ m ∈ Icc 1 N, omegaWeight w m / m * tameDifferent m =
      ∑ p ∈ (Icc 1 N).filter Nat.Prime, Real.log p / ((p : ℝ) - 1) *
        ∑ m ∈ (Icc 1 N).filter (p ∣ ·), omegaWeight w m / m := by
    have h1 : ∑ m ∈ Icc 1 N, omegaWeight w m / m * tameDifferent m =
        ∑ m ∈ Icc 1 N, ∑ p ∈ m.primeFactors,
          Real.log p / ((p : ℝ) - 1) * (omegaWeight w m / m) := by
      refine sum_congr rfl fun m _ => ?_
      rw [tameDifferent, mul_sum]
      exact sum_congr rfl fun p _ => by ring
    simp only [h1, mul_sum]
    refine sum_comm' fun m p => ?_
    simp only [mem_Icc, mem_filter, Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨h1, h2⟩, hp, hpm, -⟩
      exact ⟨⟨⟨h1, h2⟩, hpm⟩, ⟨hp.one_lt.le, (Nat.le_of_dvd h1 hpm).trans h2⟩, hp⟩
    · rintro ⟨⟨⟨h1, h2⟩, hpm⟩, -, hp⟩
      exact ⟨⟨h1, h2⟩, hp, hpm, by omega⟩
  rw [hswap]
  have hterm : ∀ p ∈ (Icc 1 N).filter Nat.Prime,
      Real.log p / ((p : ℝ) - 1) * ∑ m ∈ (Icc 1 N).filter (p ∣ ·), omegaWeight w m / m ≤
        w * (2 * (4 * ((p : ℝ) ^ ((3 : ℝ) / 2))⁻¹)) * S := by
    intro p hp
    have hpr := (mem_filter.mp hp).2
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpr.one_lt
    have hlog : 0 ≤ Real.log p / ((p : ℝ) - 1) :=
      div_nonneg (Real.log_nonneg hp1.le) (by linarith)
    have hinner := sum_omegaWeight_dvd_le hw hpr N
    have htame := log_div_mul_le hpr.two_le
    have hratio : Real.log p / ((p : ℝ) - 1) * (1 / ((p : ℝ) - 1)) ≤
        2 * (Real.log p / ((p : ℝ) - 1) / p) := by
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpr.two_le
      have hq0 : (p : ℝ) - 1 ≠ 0 := by linarith
      have hp0 : (p : ℝ) ≠ 0 := by linarith
      have e1 : Real.log p / ((p : ℝ) - 1) * (1 / ((p : ℝ) - 1)) =
          Real.log p * (1 / (((p : ℝ) - 1) * ((p : ℝ) - 1))) := by field_simp
      have e2 : 2 * (Real.log p / ((p : ℝ) - 1) / p) =
          Real.log p * (2 / (((p : ℝ) - 1) * p)) := by field_simp
      rw [e1, e2]
      refine mul_le_mul_of_nonneg_left ?_ (Real.log_nonneg hp1.le)
      rw [div_le_div_iff₀ (by nlinarith) (by nlinarith)]
      nlinarith
    calc Real.log p / ((p : ℝ) - 1) * ∑ m ∈ (Icc 1 N).filter (p ∣ ·), omegaWeight w m / m
        ≤ Real.log p / ((p : ℝ) - 1) * (w / ((p : ℝ) - 1) * S) :=
          mul_le_mul_of_nonneg_left hinner hlog
      _ = w * (Real.log p / ((p : ℝ) - 1) * (1 / ((p : ℝ) - 1))) * S := by ring
      _ ≤ w * (2 * (4 * ((p : ℝ) ^ ((3 : ℝ) / 2))⁻¹)) * S := by
          refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hw) hS
          linarith
  refine (sum_le_sum hterm).trans ?_
  rw [← sum_mul, ← mul_sum, ← mul_sum]
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left ?_ (by norm_num)) hw) hS
  exact summable_tame.sum_le_tsum _ fun n _ => by positivity

/-- **The twisted defect of the fixed-point vector**: only the non-coprime edges contribute,
`D_κ(κ^{ω}/√n) ≤ (1 − κ)² κ² (2K) |x|²`. -/
theorem twistedPoleDefect_fixedPointTest_le (κ : ℝ) (N : ℕ) :
    twistedPoleDefect κ N (fixedPointTest κ) ≤
      (1 - κ) ^ 2 * (κ ^ 2 * (2 * tameConstant)) * ∑ n ∈ Icc 1 N, fixedPointTest κ n ^ 2 := by
  set x := fixedPointTest κ
  have hw : 0 ≤ κ ^ 2 := sq_nonneg κ
  -- edge by edge
  have hedge : ∀ m ∈ Icc 1 N, ∀ t ∈ Icc 1 (N / m),
      Λ t * (x (m * t) - κ * x m / Real.sqrt t) ^ 2 =
        (1 - κ) ^ 2 * (omegaWeight (κ ^ 2) m / m) * (if m.Coprime t then 0 else Λ t / t) := by
    intro m hm t ht
    have hm0 := (mem_Icc.mp hm).1
    have ht0 := (mem_Icc.mp ht).1
    by_cases hΛ : Λ t = 0
    · simp [hΛ]
    obtain ⟨p, k, hp, hk0, rfl⟩ := (isPrimePow_nat_iff _).mp (vonMangoldt_ne_zero_iff.mp hΛ)
    have hk : k ≠ 0 := hk0.ne'
    have hm0' : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
    have ht0' : (0 : ℝ) < ((p ^ k : ℕ) : ℝ) := by exact_mod_cast (show 0 < p ^ k by omega)
    have hsmt : Real.sqrt ((m * p ^ k : ℕ) : ℝ) = Real.sqrt m * Real.sqrt ((p ^ k : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Real.sqrt_mul hm0'.le]
    have hcard := card_primeFactors_mul_prime_pow (show m ≠ 0 by omega) hp hk
    have hsm : Real.sqrt m ^ 2 = m := Real.sq_sqrt hm0'.le
    have hst : Real.sqrt ((p ^ k : ℕ) : ℝ) ^ 2 = ((p ^ k : ℕ) : ℝ) := Real.sq_sqrt ht0'.le
    have hsm0 : 0 < Real.sqrt m := Real.sqrt_pos.mpr hm0'
    have hst0 : 0 < Real.sqrt ((p ^ k : ℕ) : ℝ) := Real.sqrt_pos.mpr ht0'
    simp only [x, fixedPointTest]
    rw [hcard, hsmt]
    by_cases hpm : p ∣ m
    · have hnc : ¬ m.Coprime (p ^ k) := fun h => (coprime_prime_pow_iff hp hk).mp h hpm
      rw [if_pos hpm, add_zero, if_neg hnc, omegaWeight, ← pow_mul, pow_mul']
      field_simp
      rw [hsm, hst]
      ring
    · have hc : m.Coprime (p ^ k) := (coprime_prime_pow_iff hp hk).mpr hpm
      rw [if_neg hpm, if_pos hc, mul_zero]
      have : κ ^ (m.primeFactors.card + 1) / (Real.sqrt m * Real.sqrt ((p ^ k : ℕ) : ℝ)) -
          κ * (κ ^ m.primeFactors.card / Real.sqrt m) / Real.sqrt ((p ^ k : ℕ) : ℝ) = 0 := by
        rw [pow_succ]; field_simp; ring
      rw [this]; ring
  have hD : twistedPoleDefect κ N x = (1 - κ) ^ 2 * ∑ m ∈ Icc 1 N, omegaWeight (κ ^ 2) m / m *
      ∑ t ∈ Icc 1 (N / m), (if m.Coprime t then 0 else Λ t / t) := by
    rw [twistedPoleDefect, mul_sum]
    refine sum_congr rfl fun m hm => ?_
    rw [sum_congr rfl (hedge m hm), mul_sum, mul_sum]
    exact sum_congr rfl fun t _ => by ring
  have hbound : ∑ m ∈ Icc 1 N, omegaWeight (κ ^ 2) m / m *
      ∑ t ∈ Icc 1 (N / m), (if m.Coprime t then 0 else Λ t / t) ≤
      ∑ m ∈ Icc 1 N, omegaWeight (κ ^ 2) m / m * tameDifferent m :=
    sum_le_sum fun m hm => mul_le_mul_of_nonneg_left
      (sum_noncoprime_vonMangoldt_le (mem_Icc.mp hm).1 _)
      (div_nonneg (omegaWeight_nonneg hw m) (Nat.cast_nonneg m))
  have htame := sum_omegaWeight_tame_le hw N
  have hS : ∑ n ∈ Icc 1 N, x n ^ 2 = ∑ m ∈ Icc 1 N, omegaWeight (κ ^ 2) m / m :=
    sum_congr rfl fun n _ => fixedPointTest_sq κ n
  rw [hD, hS]
  have := mul_le_mul_of_nonneg_left (hbound.trans htame) (sq_nonneg (1 - κ))
  linarith

/-! ### 4. The fixed-point law -/

/-- **The top of `α diag(log n) + P_N`**, `α = κ − 1/κ`, `κ > 0`: for every `N ≥ 1` it lies in
`[κ(log N − log 2 − log 4 − 4) − 2Kκ(1 − κ)², κ(log N + log 4 + 4)]`, the lower end attained at
`κ^{ω(n)}/√n`. -/
theorem fixedPoint_top {κ : ℝ} (hκ : 0 < κ) (N : ℕ) :
    (∀ x : ℕ → ℝ, (κ - 1 / κ) * ∑ n ∈ Icc 1 N, Real.log n * x n ^ 2 + atomicWeilForm N x ≤
        κ * (Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2) ∧
      (κ * (Real.log N - (Real.log 2 + (Real.log 4 + 4))) - κ * (1 - κ) ^ 2 * (2 * tameConstant)) *
          ∑ n ∈ Icc 1 N, fixedPointTest κ n ^ 2 ≤
        (κ - 1 / κ) * ∑ n ∈ Icc 1 N, Real.log n * fixedPointTest κ n ^ 2 +
          atomicWeilForm N (fixedPointTest κ) := by
  refine ⟨fixedPoint_top_le hκ N, ?_⟩
  have hid := fixedPoint_identity hκ.ne' N (fixedPointTest κ)
  have hrow := mul_le_mul_of_nonneg_left (sum_row_mul_sq_ge N (fixedPointTest κ)) hκ.le
  have hD := twistedPoleDefect_fixedPointTest_le κ N
  have hDk : twistedPoleDefect κ N (fixedPointTest κ) / κ ≤
      κ * (1 - κ) ^ 2 * (2 * tameConstant) * ∑ n ∈ Icc 1 N, fixedPointTest κ n ^ 2 := by
    rw [div_le_iff₀ hκ]
    nlinarith [sq_nonneg κ]
  nlinarith

/-- **The bottom of `α diag(log n) + P_N`**, `α = κ − 1/κ`, `κ < 0`: for every `N ≥ 1` it lies in
`[κ(log N + log 4 + 4), κ(log N − log 2 − log 4 − 4) + 2K|κ|(1 − κ)²]`, the upper end attained at
the alternating charges `κ^{ω(n)}/√n`. -/
theorem fixedPoint_bottom {κ : ℝ} (hκ : κ < 0) (N : ℕ) :
    (∀ x : ℕ → ℝ, κ * (Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2 ≤
        (κ - 1 / κ) * ∑ n ∈ Icc 1 N, Real.log n * x n ^ 2 + atomicWeilForm N x) ∧
      (κ - 1 / κ) * ∑ n ∈ Icc 1 N, Real.log n * fixedPointTest κ n ^ 2 +
          atomicWeilForm N (fixedPointTest κ) ≤
        (κ * (Real.log N - (Real.log 2 + (Real.log 4 + 4))) -
            κ * (1 - κ) ^ 2 * (2 * tameConstant)) * ∑ n ∈ Icc 1 N, fixedPointTest κ n ^ 2 := by
  refine ⟨fixedPoint_bottom_ge hκ N, ?_⟩
  have hid := fixedPoint_identity hκ.ne N (fixedPointTest κ)
  have hrow := mul_le_mul_of_nonpos_left (sum_row_mul_sq_ge N (fixedPointTest κ)) hκ.le
  have hD := twistedPoleDefect_fixedPointTest_le κ N
  have hDk : -(κ * (1 - κ) ^ 2 * (2 * tameConstant) * ∑ n ∈ Icc 1 N, fixedPointTest κ n ^ 2) ≥
      -(twistedPoleDefect κ N (fixedPointTest κ) / κ) := by
    have hk' : 0 < -κ := by linarith
    rw [show -(twistedPoleDefect κ N (fixedPointTest κ) / κ) =
      twistedPoleDefect κ N (fixedPointTest κ) / (-κ) by ring]
    rw [ge_iff_le, div_le_iff₀ hk']
    nlinarith [sq_nonneg κ]
  nlinarith

/-! ### 5. The semicircle law -/

/-- For every `κ ≠ 0`: `κ P_N(x) ≤ κ²((log N + log 4 + 4)|x|² − H) + H`, with `H = Σ log n · x_n²`. -/
theorem atomicWeilForm_mul_le_of_kappa {κ : ℝ} (hκ : κ ≠ 0) (N : ℕ) (x : ℕ → ℝ) :
    κ * atomicWeilForm N x ≤
      κ ^ 2 * ((Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2 -
        ∑ n ∈ Icc 1 N, Real.log n * x n ^ 2) + ∑ n ∈ Icc 1 N, Real.log n * x n ^ 2 := by
  have hid := fixedPoint_identity hκ N x
  have hD := twistedPoleDefect_nonneg κ N x
  have hrow := sum_row_mul_sq_le N x
  set H := ∑ n ∈ Icc 1 N, Real.log n * x n ^ 2
  set R := ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * x n ^ 2
  -- multiply the identity by `κ`
  have h1 : κ * ((κ - 1 / κ) * H + atomicWeilForm N x + twistedPoleDefect κ N x / κ) =
      κ * (κ * R) := by rw [hid]
  have h2 : κ * ((κ - 1 / κ) * H + atomicWeilForm N x + twistedPoleDefect κ N x / κ) =
      (κ ^ 2 - 1) * H + κ * atomicWeilForm N x + twistedPoleDefect κ N x := by
    field_simp
  have h3 : κ ^ 2 * R ≤ κ ^ 2 * ((Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2) :=
    mul_le_mul_of_nonneg_left hrow (sq_nonneg κ)
  nlinarith

/-- **The semicircle law of the prime form**: with `H = Σ log n · x_n²`, `S = |x|²` and
`L′ = log N + log 4 + 4`, `|P_N(x)| ≤ 2√(H (L′S − H))`. The prime form is the off-diagonal part of a
large spin whose diagonal is the height `log n`: vectors concentrated low or at the top carry little
prime form, and the bound is the support function of the disk traced by the fixed-point law. -/
theorem abs_atomicWeilForm_le_semicircle (N : ℕ) (x : ℕ → ℝ) :
    |atomicWeilForm N x| ≤
      2 * Real.sqrt ((∑ n ∈ Icc 1 N, Real.log n * x n ^ 2) *
        ((Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2 -
          ∑ n ∈ Icc 1 N, Real.log n * x n ^ 2)) := by
  set H := ∑ n ∈ Icc 1 N, Real.log n * x n ^ 2
  set a := (Real.log N + (Real.log 4 + 4)) * ∑ n ∈ Icc 1 N, x n ^ 2 - H
  set P := atomicWeilForm N x
  have hH : 0 ≤ H := sum_nonneg fun n hn =>
    mul_nonneg (Real.log_nonneg (by exact_mod_cast (mem_Icc.mp hn).1)) (sq_nonneg _)
  have hrow := sum_row_mul_sq_le N x
  -- `a ≥ 0`: the rows dominate the height
  have ha : 0 ≤ a := by
    have : H ≤ ∑ n ∈ Icc 1 N, (mertensSum (N / n) + Real.log n) * x n ^ 2 :=
      sum_le_sum fun n _ => by
        have : 0 ≤ mertensSum (N / n) :=
          sum_nonneg fun t _ => div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg t)
        nlinarith [sq_nonneg (x n)]
    simp only [a]; linarith
  -- for every `κ ≠ 0`: `κ P ≤ κ² a + H`
  have hk : ∀ κ : ℝ, κ ≠ 0 → κ * P ≤ κ ^ 2 * a + H := fun κ hκ =>
    atomicWeilForm_mul_le_of_kappa hκ N x
  -- the square of `P` is at most `4 a H`
  have hHa : 0 ≤ H * a := mul_nonneg hH ha
  have hsq : P ^ 2 ≤ 4 * (H * a) := by
    rcases eq_or_ne P 0 with hP | hP
    · rw [hP]; nlinarith
    rcases eq_or_lt_of_le ha with ha0 | hapos
    · -- `a = 0`: `κ P ≤ H` for every `κ ≠ 0` is impossible with `P ≠ 0`
      exfalso
      have h := hk ((H + 1) / P) (div_ne_zero (by linarith) hP)
      rw [← ha0, mul_zero, zero_add, div_mul_cancel₀ _ hP] at h
      linarith
    · -- `κ = P/(2a)`
      have h := hk (P / (2 * a)) (div_ne_zero hP (by linarith))
      have e1 : P / (2 * a) * P = 2 * (P ^ 2 / (4 * a)) := by field_simp; ring
      have e2 : (P / (2 * a)) ^ 2 * a = P ^ 2 / (4 * a) := by field_simp; ring
      rw [e1, e2] at h
      have h4 : P ^ 2 / (4 * a) ≤ H := by linarith
      rw [div_le_iff₀ (by linarith)] at h4
      nlinarith
  have hS : 0 ≤ 4 * (H * a) := by linarith
  calc |P| = Real.sqrt (P ^ 2) := (Real.sqrt_sq_eq_abs P).symm
    _ ≤ Real.sqrt (4 * (H * a)) := Real.sqrt_le_sqrt hsq
    _ = 2 * Real.sqrt (H * a) := by
        rw [Real.sqrt_mul (by norm_num), show Real.sqrt 4 = 2 by
          rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
