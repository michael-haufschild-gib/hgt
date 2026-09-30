import GaloisForLFunctions.RHTower.WeilFullConeExposedPoint

/-!
# No Weil-positive completion minorizes `Λ`

**Theorem** (`eq_vonMangoldt_of_weilPositiveFull_of_le`, unconditional). If the prime weights `lam`
are Weil-positive with the pole term (`WeilPositiveFull`) and `lam(n) ≤ Λ(n)` for all `n ≥ 2`, then
`lam(n) = Λ(n)` for all `n ≥ 2`. No sign, growth or summability condition on `lam` is assumed, and
the Herglotz representation of the cone is not used.

Together with `eq_vonMangoldt_of_weilPositiveFull_of_ge` this makes `Λ` order-isolated in the full
Weil cone: no Weil-positive system is comparable with `Λ` without being equal to it.

**The test.** `u = Φχ_L` is the truncated Riemann kernel and `K_L(y) = ∫ u(t) u(t − y) dt` its
autocorrelation. The test is the log-shift difference `f = u − u(· − log m)`
(`logShiftRiemannDifference`). Its transform is `(1 − e^{iz log m}) û(z)`. On the zeros the
multiplier is at most `1 + √m`, so the zero side is at most `(1 + √m)²` times the near-radical
energy of `Φχ_L`, which beats `e^{2L}` (`exists_exp_mul_nearRadicalEnergy_le`). The autocorrelation
of `f` is `2K_L(y) − K_L(y + c) − K_L(y − c)` (`weilTest_logShiftRiemannDifference`).

**The argument.** Put `v(n) = (Λ(n) − lam(n))/√n ≥ 0`. Let `m` maximize `v` on the window
`2 ≤ n ≤ e^{2L}`, which carries every atom `K_L` sees. Positivity then gives
`2 v(m) K_L(0) ≤ ‖W(f, f)‖ + 4 v(m) Σ_{2 ≤ n ≤ e^{2L}} K(log n)`.

**The kernel inequality** (`sum_riemannAutocorr_log_le`). `Σ_{n ≥ 2} K(log n) ≤ (23/50) K(0)`,
with `K` the autocorrelation of `Φ`. It is pointwise: `Φ(s + h) Φ(s − h) ≤ (101/100)² R(e^{2h}) Φ(s)²`
(`riemannKernelReal_shift_mul_le`), where `R(x) = e^{−π(x−1)} ((4π²x − 6π)/(4π² − 6π))²`
and `R(n) ≤ (19/50) 8^{2−n}`. The proof has two parts:
- `Φ` lies between its lead cusp term `φ₁(u) = e^{5u/2}(4π²e^{2u} − 6π)e^{−πe^{2u}}` and
  `(101/100) φ₁` (`riemannKernelReal_sandwich`).
- `φ₁` satisfies the shift inequality exactly, by AM–GM in `Y = e^{2u}` and the convexity of
  `e^{2u}` (`riemannLeadTerm_shift_mul_le`).

Since `4 · 23/50 < 2`, the contradiction is `(2/25) v(m) K(0) ≤ ‖W‖ → 0`.

**Corollary** (`riemannHypothesis_iff_exists_weilPositiveFull_le`). RH holds iff some full-cone
Weil-positive `lam ≤ Λ` exists; such a `lam` equals `Λ`. The earlier minorant criterion
`riemannHypothesis_of_weilPositiveFull_of_le` needed `0 ≤ lam`.
-/

open Complex MeasureTheory Filter Topology Set
open scoped Real ComplexConjugate
open Zeta23

namespace RHTower

noncomputable section

/-- The leading cusp term `e^{5t/2}(4π²e^{2t} − 6π)e^{−πe^{2t}}` of Riemann's kernel. -/
def riemannLeadTerm (t : ℝ) : ℝ :=
  Real.exp (5 * t / 2) * (4 * π ^ 2 * Real.exp (2 * t) - 6 * π) * Real.exp (-π * Real.exp (2 * t))

theorem cuspTerm_one_eq_riemannLeadTerm (t : ℝ) :
    cuspTerm riemannCuspPoly 1 t = riemannLeadTerm t := by
  unfold cuspTerm riemannLeadTerm
  rw [riemannCuspPoly_eval]
  have h : Real.exp (5 * t / 2) = Real.exp (t / 2) * Real.exp (2 * t) := by
    rw [← Real.exp_add]; ring_nf
  rw [h]
  push_cast
  ring_nf

theorem riemannLeadTerm_pos {t : ℝ} (ht : 0 ≤ t) : 0 < riemannLeadTerm t := by
  rw [← cuspTerm_one_eq_riemannLeadTerm]
  exact cuspTerm_riemannCuspPoly_pos le_rfl ht

/-- For `u ≥ 0` the lead term dominates `2π² Y² e^{u/2} e^{−πY}`, `Y = e^{2u}`. -/
theorem riemannLeadTerm_ge {u : ℝ} (hu : 0 ≤ u) :
    2 * π ^ 2 * Real.exp (2 * u) ^ 2 * Real.exp (u / 2) * Real.exp (-π * Real.exp (2 * u)) ≤
      riemannLeadTerm u := by
  rw [← cuspTerm_one_eq_riemannLeadTerm]
  unfold cuspTerm
  rw [riemannCuspPoly_eval]
  set Y := Real.exp (2 * u) with hY
  have hY1 : 1 ≤ Y := Real.one_le_exp (by linarith)
  have hπ := Real.pi_gt_three
  have hpoly : 2 * π ^ 2 * Y ^ 2 ≤ 4 * π ^ 2 * ((1 : ℕ) ^ 2 * Y) ^ 2 - 6 * π * ((1 : ℕ) ^ 2 * Y) := by
    push_cast
    have : 0 ≤ π * Y * (π * Y - 3) := by
      apply mul_nonneg (by positivity); nlinarith
    nlinarith
  have he1 := Real.exp_pos (u / 2)
  have he2 := Real.exp_pos (-π * ((1 : ℕ) ^ 2 * Y))
  have hcast : ((1 : ℕ) : ℝ) ^ 2 * Y = Y := by push_cast; ring
  calc 2 * π ^ 2 * Y ^ 2 * Real.exp (u / 2) * Real.exp (-π * Y)
      = Real.exp (u / 2) * (2 * π ^ 2 * Y ^ 2) * Real.exp (-π * ((1 : ℕ) ^ 2 * Y)) := by
        rw [hcast]; ring
    _ ≤ _ := by gcongr

/-- A higher cusp term is a tiny multiple of the lead term. -/
theorem cuspTerm_add_two_le {u : ℝ} (hu : 0 ≤ u) (n : ℕ) :
    cuspTerm riemannCuspPoly (n + 2) u ≤
      32 * Real.exp (-9) * (1 / 2 : ℝ) ^ n * riemannLeadTerm u := by
  have hlow := riemannLeadTerm_ge hu
  unfold cuspTerm
  rw [riemannCuspPoly_eval]
  set Y := Real.exp (2 * u) with hY
  have hY1 : 1 ≤ Y := Real.one_le_exp (by linarith)
  have hπ := Real.pi_gt_three
  set m : ℝ := ((n + 2 : ℕ) : ℝ) with hm
  have hm2 : 2 ≤ m := by rw [hm]; push_cast; linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hmn : m = n + 2 := by rw [hm]; push_cast; ring
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  -- the polynomial factor
  have hpoly : 4 * π ^ 2 * (m ^ 2 * Y) ^ 2 - 6 * π * (m ^ 2 * Y) ≤ 4 * π ^ 2 * m ^ 4 * Y ^ 2 := by
    have : 0 ≤ 6 * π * (m ^ 2 * Y) := by positivity
    nlinarith
  -- the Gaussian factor
  have hgauss : Real.exp (-π * (m ^ 2 * Y)) ≤
      Real.exp (-π * Y) * Real.exp (-(12 * n + 9)) := by
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have h1 : (4 * n + 3 : ℝ) ≤ m ^ 2 - 1 := by rw [hmn]; nlinarith
    have h2 : (4 * n + 3) * 1 ≤ (m ^ 2 - 1) * Y := by
      apply mul_le_mul h1 hY1 (by norm_num) (by nlinarith)
    have h3 : (12 * n + 9 : ℝ) ≤ π * (4 * n + 3) := by nlinarith
    nlinarith
  -- the moment factor
  have hmom : m ^ 4 ≤ 16 * Real.exp (2 * n) := by
    have h1 : 1 + (n : ℝ) / 2 ≤ Real.exp (n / 2) := by
      have := Real.add_one_le_exp ((n : ℝ) / 2); linarith
    have h2 : (1 + (n : ℝ) / 2) ^ 4 ≤ Real.exp (n / 2) ^ 4 :=
      pow_le_pow_left₀ (by positivity) h1 4
    have h3 : Real.exp (n / 2) ^ 4 = Real.exp (2 * n) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have h4 : m ^ 4 = 16 * (1 + (n : ℝ) / 2) ^ 4 := by rw [hmn]; ring
    rw [h4, ← h3]; linarith
  have hgeo : Real.exp (-(10 * n)) ≤ (1 / 2 : ℝ) ^ n := by
    have h2 : (2 : ℝ) ≤ Real.exp 10 := by
      have := Real.add_one_le_exp (10 : ℝ); linarith
    have : Real.exp (-(10 * n)) = (Real.exp 10)⁻¹ ^ n := by
      rw [← Real.exp_neg, ← Real.exp_nat_mul]; ring_nf
    rw [this]
    apply pow_le_pow_left₀ (by positivity)
    rw [inv_le_comm₀ (Real.exp_pos _) (by norm_num)]; linarith
  have he := Real.exp_pos (u / 2)
  have hE := Real.exp_pos (-π * Y)
  set L := riemannLeadTerm u
  have hstep : Real.exp (u / 2) * (4 * π ^ 2 * (m ^ 2 * Y) ^ 2 - 6 * π * (m ^ 2 * Y)) *
      Real.exp (-π * (m ^ 2 * Y)) ≤
      2 * m ^ 4 * Real.exp (-(12 * n + 9)) *
        (2 * π ^ 2 * Y ^ 2 * Real.exp (u / 2) * Real.exp (-π * Y)) := by
    have hpos : 0 ≤ 4 * π ^ 2 * (m ^ 2 * Y) ^ 2 - 6 * π * (m ^ 2 * Y) := by
      have hy : 1 ≤ m ^ 2 * Y := by nlinarith
      have h1 : 0 ≤ 4 * π * (m ^ 2 * Y) - 6 := by nlinarith
      have h2 : 0 ≤ π * (m ^ 2 * Y) := by positivity
      have := mul_nonneg h2 h1
      nlinarith
    calc Real.exp (u / 2) * (4 * π ^ 2 * (m ^ 2 * Y) ^ 2 - 6 * π * (m ^ 2 * Y)) *
          Real.exp (-π * (m ^ 2 * Y))
        ≤ Real.exp (u / 2) * (4 * π ^ 2 * m ^ 4 * Y ^ 2) *
            (Real.exp (-π * Y) * Real.exp (-(12 * n + 9))) := by gcongr
      _ = _ := by ring
  have hfin : 2 * m ^ 4 * Real.exp (-(12 * n + 9)) ≤ 32 * Real.exp (-9) * (1 / 2 : ℝ) ^ n := by
    have hsplit : Real.exp (-(12 * n + 9)) = Real.exp (-(10 * n)) * Real.exp (-9) *
        Real.exp (-(2 * n)) := by
      rw [← Real.exp_add, ← Real.exp_add]; ring_nf
    have hinv : Real.exp (2 * n) * Real.exp (-(2 * n)) = 1 := by
      rw [← Real.exp_add]; simp
    rw [hsplit]
    have h9 := Real.exp_pos (-9)
    have hm2' := Real.exp_pos (-(2 * (n : ℝ)))
    calc 2 * m ^ 4 * (Real.exp (-(10 * n)) * Real.exp (-9) * Real.exp (-(2 * n)))
        ≤ 2 * (16 * Real.exp (2 * n)) * ((1 / 2 : ℝ) ^ n * Real.exp (-9) * Real.exp (-(2 * n))) := by
          gcongr
      _ = 32 * Real.exp (-9) * (1 / 2 : ℝ) ^ n * (Real.exp (2 * n) * Real.exp (-(2 * n))) := by ring
      _ = _ := by rw [hinv, mul_one]
  have hL0 : 0 ≤ 2 * π ^ 2 * Y ^ 2 * Real.exp (u / 2) * Real.exp (-π * Y) := by positivity
  calc _ ≤ 2 * m ^ 4 * Real.exp (-(12 * n + 9)) *
        (2 * π ^ 2 * Y ^ 2 * Real.exp (u / 2) * Real.exp (-π * Y)) := hstep
    _ ≤ 32 * Real.exp (-9) * (1 / 2 : ℝ) ^ n * L := by
        apply mul_le_mul hfin hlow hL0 (by positivity)

/-- `64 e^{−9} ≤ 1/100`. -/
theorem sixtyfour_exp_neg_nine_le : 64 * Real.exp (-9) ≤ 1 / 100 := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h9 : Real.exp 9 = Real.exp 1 ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
  have hpow : (2.7182818283 : ℝ) ^ 9 ≤ Real.exp 1 ^ 9 := pow_le_pow_left₀ (by norm_num) he.le 9
  have hbig : (6400 : ℝ) ≤ Real.exp 9 := by rw [h9]; nlinarith [hpow]
  rw [Real.exp_neg]
  rw [show (64 : ℝ) * (Real.exp 9)⁻¹ = 64 / Real.exp 9 by ring, div_le_iff₀ (Real.exp_pos _)]
  linarith

/-- **Sandwich.** For `u ≥ 0`, `φ₁(u) ≤ Φ(u) ≤ (101/100) φ₁(u)`. -/
theorem riemannLeadTerm_le_riemannKernelReal {u : ℝ} (hu : 0 ≤ u) :
    riemannLeadTerm u ≤ riemannKernelReal u ∧
      riemannKernelReal u ≤ (101 / 100) * riemannLeadTerm u := by
  have hs := summable_cuspTerm riemannCuspPoly u
  have hsplit : riemannKernelReal u = riemannLeadTerm u +
      ∑' n : ℕ, cuspTerm riemannCuspPoly (n + 2) u := by
    unfold riemannKernelReal
    rw [abs_of_nonneg hu, cuspSeries, hs.tsum_eq_zero_add, ← cuspTerm_one_eq_riemannLeadTerm]
  have hpos : ∀ n : ℕ, 0 ≤ cuspTerm riemannCuspPoly (n + 2) u := fun n =>
    (cuspTerm_riemannCuspPoly_pos (by omega) hu).le
  have hgeo : Summable fun n : ℕ => (1 / 2 : ℝ) ^ n :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hmaj : Summable fun n : ℕ => 32 * Real.exp (-9) * (1 / 2 : ℝ) ^ n * riemannLeadTerm u := by
    have := (hgeo.mul_left (32 * Real.exp (-9))).mul_right (riemannLeadTerm u)
    exact this
  have hs2 : Summable fun n : ℕ => cuspTerm riemannCuspPoly (n + 2) u :=
    Summable.of_nonneg_of_le hpos (cuspTerm_add_two_le hu) hmaj
  have htail : ∑' n : ℕ, cuspTerm riemannCuspPoly (n + 2) u ≤ 64 * Real.exp (-9) * riemannLeadTerm u := by
    calc ∑' n : ℕ, cuspTerm riemannCuspPoly (n + 2) u
        ≤ ∑' n : ℕ, 32 * Real.exp (-9) * (1 / 2 : ℝ) ^ n * riemannLeadTerm u :=
          hs2.tsum_le_tsum (cuspTerm_add_two_le hu) hmaj
      _ = 32 * Real.exp (-9) * (∑' n : ℕ, (1 / 2 : ℝ) ^ n) * riemannLeadTerm u := by
          rw [tsum_mul_right, tsum_mul_left]
      _ = 64 * Real.exp (-9) * riemannLeadTerm u := by
          rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
          have : (1 - (1 / 2 : ℝ))⁻¹ = 2 := by norm_num
          rw [this]; ring
  have ht0 : 0 ≤ ∑' n : ℕ, cuspTerm riemannCuspPoly (n + 2) u := tsum_nonneg hpos
  have hL := riemannLeadTerm_pos hu
  have h64 := sixtyfour_exp_neg_nine_le
  constructor
  · linarith
  · have : 64 * Real.exp (-9) * riemannLeadTerm u ≤ 1 / 100 * riemannLeadTerm u :=
      mul_le_mul_of_nonneg_right h64 hL.le
    linarith

/-- The shift ratio `e^{−π(x−1)} ((4π²x − 6π)/(4π² − 6π))²`. -/
def riemannShiftRatio (x : ℝ) : ℝ :=
  Real.exp (-(π * (x - 1))) * ((4 * π ^ 2 * x - 6 * π) / (4 * π ^ 2 - 6 * π)) ^ 2

theorem riemannLeadTerm_shift_mul_le_of_nonneg {s h : ℝ} (hs : 0 ≤ s) (hh : 0 ≤ h)
    (hx : 2 ≤ Real.exp (2 * h)) :
    riemannLeadTerm |s + h| * riemannLeadTerm |s - h| ≤
      riemannShiftRatio (Real.exp (2 * h)) * riemannLeadTerm |s| ^ 2 := by
  have hπ := Real.pi_gt_three
  obtain ⟨p, hp⟩ : ∃ p : ℝ, p = 4 * π ^ 2 := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ q : ℝ, q = 6 * π := ⟨_, rfl⟩
  have hpq : 0 < p - q := by rw [hp, hq]; nlinarith
  have hq0 : 0 < q := by rw [hq]; positivity
  have hp0 : 0 < p := by linarith
  have hRdef : ∀ y : ℝ, riemannShiftRatio y =
      Real.exp (-(π * (y - 1))) * ((p * y - q) / (p - q)) ^ 2 := by
    intro y; rw [hp, hq]; rfl
  have hlead : ∀ t : ℝ, riemannLeadTerm t =
      Real.exp (5 * t / 2) * (p * Real.exp (2 * t) - q) * Real.exp (-π * Real.exp (2 * t)) := by
    intro t; rw [hp, hq]; rfl
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = Real.exp (2 * h) := ⟨_, rfl⟩
  obtain ⟨Z, hZdef⟩ : ∃ Z : ℝ, Z = Real.exp (2 * s) := ⟨_, rfl⟩
  rw [← hxdef] at hx ⊢
  have hZ1 : 1 ≤ Z := by rw [hZdef]; exact Real.one_le_exp (by linarith)
  have hx0 : 0 < x := by linarith
  have habs_s : |s| = s := abs_of_nonneg hs
  have habs_p : |s + h| = s + h := abs_of_nonneg (by linarith)
  set E := Real.exp (5 * s) * Real.exp (-(2 * π * Z)) with hEdef
  have hE0 : 0 < E := by positivity
  have hRHS : riemannShiftRatio x * riemannLeadTerm |s| ^ 2 =
      Real.exp (-(π * (x - 1))) * ((p * x - q) / (p - q)) ^ 2 * (p * Z - q) ^ 2 * E := by
    rw [hRdef, habs_s, hlead s, ← hZdef]
    have e1 : Real.exp (5 * s / 2) ^ 2 = Real.exp (5 * s) := by
      rw [← Real.exp_nat_mul]; ring_nf
    have e2 : Real.exp (-π * Z) ^ 2 = Real.exp (-(2 * π * Z)) := by
      rw [← Real.exp_nat_mul]; ring_nf
    calc Real.exp (-(π * (x - 1))) * ((p * x - q) / (p - q)) ^ 2 *
          (Real.exp (5 * s / 2) * (p * Z - q) * Real.exp (-π * Z)) ^ 2
        = Real.exp (-(π * (x - 1))) * ((p * x - q) / (p - q)) ^ 2 * (p * Z - q) ^ 2 *
          (Real.exp (5 * s / 2) ^ 2 * Real.exp (-π * Z) ^ 2) := by ring
      _ = _ := by rw [e1, e2]
  have hZq : 0 < p * Z - q := by
    have : p * 1 ≤ p * Z := mul_le_mul_of_nonneg_left hZ1 hp0.le
    linarith
  have hratio1 : 1 ≤ ((p * x - q) / (p - q)) ^ 2 := by
    have h1 : 1 ≤ (p * x - q) / (p - q) := by
      rw [le_div_iff₀ hpq]
      have : p * 1 ≤ p * x := mul_le_mul_of_nonneg_left (by linarith) hp0.le
      linarith
    nlinarith
  have hX0 : 0 < Real.exp (-(π * (x - 1))) := Real.exp_pos _
  rw [hRHS]
  rcases le_or_gt h s with hhs | hsh
  · -- both points on the right half-line
    have habs_m : |s - h| = s - h := abs_of_nonneg (by linarith)
    have hxZ : x ≤ Z := by rw [hxdef, hZdef]; exact Real.exp_le_exp.mpr (by linarith)
    obtain ⟨b, hbdef⟩ : ∃ b : ℝ, b = Real.exp (-(2 * h)) := ⟨_, rfl⟩
    have hxb : x * b = 1 := by rw [hxdef, hbdef, ← Real.exp_add]; simp
    have hb0 : 0 < b := by rw [hbdef]; exact Real.exp_pos _
    have e1 : Real.exp (2 * (s + h)) = Z * x := by rw [hZdef, hxdef, ← Real.exp_add]; ring_nf
    have e2 : Real.exp (2 * (s - h)) = Z * b := by rw [hZdef, hbdef, ← Real.exp_add]; ring_nf
    have e3 : Real.exp (5 * (s + h) / 2) * Real.exp (5 * (s - h) / 2) = Real.exp (5 * s) := by
      rw [← Real.exp_add]; ring_nf
    rw [habs_p, habs_m, hlead, hlead, e1, e2]
    have hZb : 1 ≤ Z * b := by
      rw [← e2]; exact Real.one_le_exp (by linarith)
    have hZx : 1 ≤ Z * x := one_le_mul_of_one_le_of_one_le hZ1 (by linarith)
    have hQ0 : 0 ≤ (p * (Z * x) - q) * (p * (Z * b) - q) := by
      have h1 : p * 1 ≤ p * (Z * x) := mul_le_mul_of_nonneg_left hZx hp0.le
      have h2 : p * 1 ≤ p * (Z * b) := mul_le_mul_of_nonneg_left hZb hp0.le
      exact mul_nonneg (by linarith) (by linarith)
    have hsum : 2 ≤ x + b := by nlinarith [sq_nonneg (x - b)]
    have hQ : (p * (Z * x) - q) * (p * (Z * b) - q) ≤ (p * Z - q) ^ 2 := by
      have hexp : (p * (Z * x) - q) * (p * (Z * b) - q) =
          p ^ 2 * Z ^ 2 * (x * b) - p * q * Z * (x + b) + q ^ 2 := by ring
      rw [hexp, hxb]
      have : 0 ≤ p * q * Z * (x + b - 2) :=
        mul_nonneg (mul_nonneg (mul_nonneg hp0.le hq0.le) (by linarith)) (by linarith)
      have e : (p * Z - q) ^ 2 - (p ^ 2 * Z ^ 2 * 1 - p * q * Z * (x + b) + q ^ 2) =
          p * q * Z * (x + b - 2) := by ring
      linarith
    have hgap : x - 1 ≤ Z * x + Z * b - 2 * Z := by
      have h1 : Z * x + Z * b - 2 * Z = Z * (x + b - 2) := by ring
      have h2 : x * (x + b - 2) ≤ Z * (x + b - 2) :=
        mul_le_mul_of_nonneg_right hxZ (by linarith)
      have h3 : x * (x + b - 2) = x ^ 2 + 1 - 2 * x := by
        have : x * (x + b - 2) = x ^ 2 + x * b - 2 * x := by ring
        rw [this, hxb]
      have h4 : 0 ≤ (x - 1) * (x - 2) := mul_nonneg (by linarith) (by linarith)
      have h5 : (x - 1) * (x - 2) = x ^ 2 - 3 * x + 2 := by ring
      linarith
    have hE : Real.exp (-π * (Z * x)) * Real.exp (-π * (Z * b)) ≤
        Real.exp (-(π * (x - 1))) * Real.exp (-(2 * π * Z)) := by
      rw [← Real.exp_add (-π * (Z * x)) (-π * (Z * b)),
        ← Real.exp_add (-(π * (x - 1))) (-(2 * π * Z))]
      apply Real.exp_le_exp.mpr
      have key := mul_le_mul_of_nonneg_left hgap Real.pi_pos.le
      linear_combination key
    have hEE0 : 0 ≤ Real.exp (-π * (Z * x)) * Real.exp (-π * (Z * b)) := by positivity
    calc Real.exp (5 * (s + h) / 2) * (p * (Z * x) - q) * Real.exp (-π * (Z * x)) *
          (Real.exp (5 * (s - h) / 2) * (p * (Z * b) - q) * Real.exp (-π * (Z * b)))
        = (Real.exp (5 * (s + h) / 2) * Real.exp (5 * (s - h) / 2)) *
            ((p * (Z * x) - q) * (p * (Z * b) - q)) *
            (Real.exp (-π * (Z * x)) * Real.exp (-π * (Z * b))) := by ring
      _ = Real.exp (5 * s) * ((p * (Z * x) - q) * (p * (Z * b) - q)) *
            (Real.exp (-π * (Z * x)) * Real.exp (-π * (Z * b))) := by rw [e3]
      _ ≤ Real.exp (5 * s) * (p * Z - q) ^ 2 *
            (Real.exp (-(π * (x - 1))) * Real.exp (-(2 * π * Z))) := by
          gcongr
      _ = Real.exp (-(π * (x - 1))) * (p * Z - q) ^ 2 * E * 1 := by rw [hEdef]; ring
      _ ≤ Real.exp (-(π * (x - 1))) * (p * Z - q) ^ 2 * E * ((p * x - q) / (p - q)) ^ 2 :=
          mul_le_mul_of_nonneg_left hratio1 (by positivity)
      _ = _ := by ring
  · -- the left point reflects
    have habs_m : |s - h| = h - s := by rw [abs_sub_comm]; exact abs_of_nonneg (by linarith)
    obtain ⟨V, hVdef⟩ : ∃ V : ℝ, V = Real.exp (2 * (h - s)) := ⟨_, rfl⟩
    obtain ⟨Zi, hZidef⟩ : ∃ Zi : ℝ, Zi = Real.exp (-(2 * s)) := ⟨_, rfl⟩
    have hZZi : Z * Zi = 1 := by rw [hZdef, hZidef, ← Real.exp_add]; simp
    have hZi0 : 0 < Zi := by rw [hZidef]; exact Real.exp_pos _
    have hV : V = x * Zi := by rw [hVdef, hxdef, hZidef, ← Real.exp_add]; ring_nf
    have hV1 : 1 ≤ V := by rw [hVdef]; exact Real.one_le_exp (by linarith)
    have e1 : Real.exp (2 * (s + h)) = Z * x := by rw [hZdef, hxdef, ← Real.exp_add]; ring_nf
    have e3 : Real.exp (5 * (s + h) / 2) * Real.exp (5 * (h - s) / 2) = Real.exp (5 * h) := by
      rw [← Real.exp_add]; ring_nf
    rw [habs_p, habs_m, hlead, hlead, e1, ← hVdef]
    have hZx : 1 ≤ Z * x := one_le_mul_of_one_le_of_one_le hZ1 (by linarith)
    have hQ0 : 0 ≤ (p * (Z * x) - q) * (p * V - q) := by
      have h1 : p * 1 ≤ p * (Z * x) := mul_le_mul_of_nonneg_left hZx hp0.le
      have h2 : p * 1 ≤ p * V := mul_le_mul_of_nonneg_left hV1 hp0.le
      exact mul_nonneg (by linarith) (by linarith)
    have hsum : 2 ≤ Z + Zi := by nlinarith [sq_nonneg (Z - Zi)]
    have hQ : (p * (Z * x) - q) * (p * V - q) ≤ (p * x - q) ^ 2 := by
      have hexp : (p * (Z * x) - q) * (p * V - q) =
          p ^ 2 * x ^ 2 * (Z * Zi) - p * q * x * (Z + Zi) + q ^ 2 := by rw [hV]; ring
      rw [hexp, hZZi]
      have : 0 ≤ p * q * x * (Z + Zi - 2) :=
        mul_nonneg (mul_nonneg (mul_nonneg hp0.le hq0.le) hx0.le) (by linarith)
      have e : (p * x - q) ^ 2 - (p ^ 2 * x ^ 2 * 1 - p * q * x * (Z + Zi) + q ^ 2) =
          p * q * x * (Z + Zi - 2) := by ring
      linarith
    have hD : (p - q) ^ 2 ≤ (p * Z - q) ^ 2 := by
      have : p * 1 ≤ p * Z := mul_le_mul_of_nonneg_left hZ1 hp0.le
      exact pow_le_pow_left₀ hpq.le (by linarith) 2
    have hVlin : 1 + 2 * (h - s) ≤ V := by
      have := Real.add_one_le_exp (2 * (h - s)); rw [hVdef]; linarith
    have hE : Real.exp (5 * h) * (Real.exp (-π * (Z * x)) * Real.exp (-π * V)) ≤
        Real.exp (-(π * (x - 1))) * E := by
      rw [hEdef, ← Real.exp_add (-π * (Z * x)) (-π * V), ← Real.exp_add (5 * h),
        ← Real.exp_add (5 * s) (-(2 * π * Z)), ← Real.exp_add (-(π * (x - 1)))]
      apply Real.exp_le_exp.mpr
      have h1 : (x - 2) * 1 ≤ (x - 2) * Z := mul_le_mul_of_nonneg_left hZ1 (by linarith)
      have h2 : 5 * (h - s) ≤ 2 * π * (h - s) :=
        mul_le_mul_of_nonneg_right (by linarith) (by linarith)
      have h3 := mul_le_mul_of_nonneg_left hVlin Real.pi_pos.le
      have h4 := mul_le_mul_of_nonneg_left h1 Real.pi_pos.le
      linear_combination h2 + h3 + h4
    have hEE0 : 0 ≤ Real.exp (5 * h) * (Real.exp (-π * (Z * x)) * Real.exp (-π * V)) := by
      positivity
    have hdiv : ((p * x - q) / (p - q)) ^ 2 * (p - q) ^ 2 = (p * x - q) ^ 2 := by
      rw [div_pow, div_mul_cancel₀]; exact pow_ne_zero 2 hpq.ne'
    calc Real.exp (5 * (s + h) / 2) * (p * (Z * x) - q) * Real.exp (-π * (Z * x)) *
          (Real.exp (5 * (h - s) / 2) * (p * V - q) * Real.exp (-π * V))
        = ((p * (Z * x) - q) * (p * V - q)) * ((Real.exp (5 * (s + h) / 2) *
            Real.exp (5 * (h - s) / 2)) * (Real.exp (-π * (Z * x)) * Real.exp (-π * V))) := by ring
      _ = ((p * (Z * x) - q) * (p * V - q)) *
            (Real.exp (5 * h) * (Real.exp (-π * (Z * x)) * Real.exp (-π * V))) := by rw [e3]
      _ ≤ (p * x - q) ^ 2 * (Real.exp (-(π * (x - 1))) * E) :=
          mul_le_mul hQ hE hEE0 (sq_nonneg _)
      _ = Real.exp (-(π * (x - 1))) * (((p * x - q) / (p - q)) ^ 2 * (p - q) ^ 2) * E := by
          rw [hdiv]; ring
      _ ≤ Real.exp (-(π * (x - 1))) * (((p * x - q) / (p - q)) ^ 2 * (p * Z - q) ^ 2) * E := by
          gcongr
      _ = _ := by ring

/-- **The shift inequality for the lead term.** For `e^{2h} ≥ 2`,
`φ₁(|s+h|) φ₁(|s−h|) ≤ R(e^{2h}) φ₁(|s|)²`. -/
theorem riemannLeadTerm_shift_mul_le (s : ℝ) {h : ℝ} (hh : 0 ≤ h) (hx : 2 ≤ Real.exp (2 * h)) :
    riemannLeadTerm |s + h| * riemannLeadTerm |s - h| ≤
      riemannShiftRatio (Real.exp (2 * h)) * riemannLeadTerm |s| ^ 2 := by
  rcases le_or_gt 0 s with hs | hs
  · exact riemannLeadTerm_shift_mul_le_of_nonneg hs hh hx
  · have hk := riemannLeadTerm_shift_mul_le_of_nonneg (s := -s) (by linarith) hh hx
    have e1 : |-s + h| = |s - h| := by rw [show -s + h = -(s - h) by ring, abs_neg]
    have e2 : |-s - h| = |s + h| := by rw [show -s - h = -(s + h) by ring, abs_neg]
    rw [e1, e2, abs_neg, mul_comm] at hk
    exact hk

/-- **Sandwich on the whole line.** `φ₁(|v|) ≤ Φ(v) ≤ (101/100) φ₁(|v|)`. -/
theorem riemannKernelReal_sandwich (v : ℝ) :
    riemannLeadTerm |v| ≤ riemannKernelReal v ∧
      riemannKernelReal v ≤ (101 / 100) * riemannLeadTerm |v| := by
  have h := riemannLeadTerm_le_riemannKernelReal (abs_nonneg v)
  have e : riemannKernelReal |v| = riemannKernelReal v := by
    unfold riemannKernelReal; rw [abs_abs]
  rwa [e] at h

/-- **The shift inequality for Riemann's kernel.** For `e^{2h} ≥ 2`,
`Φ(s + h) Φ(s − h) ≤ (101/100)² R(e^{2h}) Φ(s)²`. -/
theorem riemannKernelReal_shift_mul_le (s : ℝ) {h : ℝ} (hh : 0 ≤ h) (hx : 2 ≤ Real.exp (2 * h)) :
    riemannKernelReal (s + h) * riemannKernelReal (s - h) ≤
      (101 / 100) ^ 2 * riemannShiftRatio (Real.exp (2 * h)) * riemannKernelReal s ^ 2 := by
  obtain ⟨-, h1⟩ := riemannKernelReal_sandwich (s + h)
  obtain ⟨-, h2⟩ := riemannKernelReal_sandwich (s - h)
  obtain ⟨h3, -⟩ := riemannKernelReal_sandwich s
  have hk := riemannLeadTerm_shift_mul_le s hh hx
  have p1 := riemannLeadTerm_pos (abs_nonneg (s + h))
  have p2 := riemannLeadTerm_pos (abs_nonneg (s - h))
  have p3 := riemannLeadTerm_pos (abs_nonneg s)
  have hR : 0 ≤ riemannShiftRatio (Real.exp (2 * h)) := by
    unfold riemannShiftRatio; positivity
  have hΦ1 := riemannKernelReal_pos (s + h)
  have hΦ2 := riemannKernelReal_pos (s - h)
  calc riemannKernelReal (s + h) * riemannKernelReal (s - h)
      ≤ ((101 / 100) * riemannLeadTerm |s + h|) * ((101 / 100) * riemannLeadTerm |s - h|) :=
        mul_le_mul h1 h2 hΦ2.le (by positivity)
    _ = (101 / 100) ^ 2 * (riemannLeadTerm |s + h| * riemannLeadTerm |s - h|) := by ring
    _ ≤ (101 / 100) ^ 2 * (riemannShiftRatio (Real.exp (2 * h)) * riemannLeadTerm |s| ^ 2) :=
        mul_le_mul_of_nonneg_left hk (by norm_num)
    _ ≤ (101 / 100) ^ 2 * (riemannShiftRatio (Real.exp (2 * h)) * riemannKernelReal s ^ 2) := by
        gcongr
    _ = _ := by ring

/-! ## The autocorrelation of Riemann's kernel -/

/-- The autocorrelation `K(y) = ∫ Φ(t) Φ(t − y) dt` of Riemann's kernel. -/
def riemannAutocorr (y : ℝ) : ℝ := ∫ t, riemannKernelReal t * riemannKernelReal (t - y)

theorem integrable_riemannKernelReal_mul (y : ℝ) :
    Integrable fun t => riemannKernelReal t * riemannKernelReal (t - y) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannPhiKernel_le_exp (B := 1) zero_le_one
  have hΦ : ∀ x, riemannKernelReal x ≤ C * Real.exp (-|x|) := by
    intro x
    have h := hC x
    rw [riemannPhiKernel_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (riemannKernelReal_pos x), one_mul] at h
    exact h
  refine Integrable.mono' (integrable_exp_neg_abs.const_mul (C ^ 2))
    ((continuous_riemannKernelReal.mul (continuous_riemannKernelReal.comp
      (continuous_id.sub continuous_const))).aestronglyMeasurable)
    (Eventually.of_forall fun t => ?_)
  have h1 := hΦ t
  have h2 := hΦ (t - y)
  have p1 := riemannKernelReal_pos t
  have p2 := riemannKernelReal_pos (t - y)
  have he : Real.exp (-|t - y|) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith [abs_nonneg (t - y)])
  rw [Real.norm_eq_abs, abs_of_pos (mul_pos p1 p2)]
  calc riemannKernelReal t * riemannKernelReal (t - y)
      ≤ (C * Real.exp (-|t|)) * (C * Real.exp (-|t - y|)) := mul_le_mul h1 h2 p2.le (by positivity)
    _ ≤ (C * Real.exp (-|t|)) * (C * 1) := by gcongr
    _ = C ^ 2 * Real.exp (-|t|) := by ring

theorem riemannAutocorr_zero : riemannAutocorr 0 = ∫ t, riemannKernelReal t ^ 2 := by
  unfold riemannAutocorr
  congr 1; funext t; rw [sub_zero, sq]

theorem riemannAutocorr_zero_pos : 0 < riemannAutocorr 0 := by
  have hint := integrable_riemannKernelReal_mul 0
  unfold riemannAutocorr
  rw [integral_pos_iff_support_of_nonneg (fun t => (mul_pos (riemannKernelReal_pos t)
    (riemannKernelReal_pos _)).le) hint]
  have hsupp : Function.support (fun t => riemannKernelReal t * riemannKernelReal (t - 0)) =
      Set.univ := by
    ext t
    simp only [Function.mem_support, Set.mem_univ, iff_true]
    exact (mul_pos (riemannKernelReal_pos t) (riemannKernelReal_pos _)).ne'
  rw [hsupp, Real.volume_univ]
  exact ENNReal.zero_lt_top

/-- **Autocorrelation at a shift.** For `e^{2h} ≥ 2`, `K(2h) ≤ (101/100)² R(e^{2h}) K(0)`. -/
theorem riemannAutocorr_two_mul_le {h : ℝ} (hh : 0 ≤ h) (hx : 2 ≤ Real.exp (2 * h)) :
    riemannAutocorr (2 * h) ≤
      (101 / 100) ^ 2 * riemannShiftRatio (Real.exp (2 * h)) * riemannAutocorr 0 := by
  have hshift : riemannAutocorr (2 * h) =
      ∫ s, riemannKernelReal (s + h) * riemannKernelReal (s - h) := by
    unfold riemannAutocorr
    rw [← integral_add_right_eq_self (fun t => riemannKernelReal t *
      riemannKernelReal (t - 2 * h)) h]
    congr 1; funext s
    rw [show s + h - 2 * h = s - h by ring]
  rw [hshift, riemannAutocorr_zero, ← integral_const_mul]
  have hi1 : Integrable fun s => riemannKernelReal (s + h) * riemannKernelReal (s - h) := by
    have := (integrable_riemannKernelReal_mul (2 * h)).comp_add_right h
    refine this.congr (Eventually.of_forall fun s => ?_)
    simp only
    rw [show s + h - 2 * h = s - h by ring]
  have hi2 : Integrable fun s => (101 / 100) ^ 2 * riemannShiftRatio (Real.exp (2 * h)) *
      riemannKernelReal s ^ 2 := by
    have := (integrable_riemannKernelReal_mul 0).const_mul
      ((101 / 100) ^ 2 * riemannShiftRatio (Real.exp (2 * h)))
    refine this.congr (Eventually.of_forall fun s => ?_)
    simp only
    rw [sub_zero]; ring
  exact integral_mono hi1 hi2 fun s => riemannKernelReal_shift_mul_le s hh hx

/-! ## The explicit sum -/

theorem exp_pi_ge : (45 / 2 : ℝ) ≤ Real.exp π := by
  have he : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
  have h3 : (2.7182818283 : ℝ) ^ 3 ≤ Real.exp 1 ^ 3 := pow_le_pow_left₀ (by norm_num) he.le 3
  have h14 : (1.14 : ℝ) ≤ Real.exp 0.14 := by
    have := Real.add_one_le_exp (0.14 : ℝ); linarith
  have hsplit : Real.exp 3.14 = Real.exp 1 ^ 3 * Real.exp 0.14 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have hmono : Real.exp 3.14 ≤ Real.exp π := Real.exp_le_exp.mpr Real.pi_gt_d2.le
  have hprod : (2.7182818283 : ℝ) ^ 3 * 1.14 ≤ Real.exp 1 ^ 3 * Real.exp 0.14 :=
    mul_le_mul h3 h14 (by norm_num) (by positivity)
  nlinarith

/-- **The ratio decays geometrically.** `R(k + 2) ≤ (19/50) 8^{−k}`. -/
theorem riemannShiftRatio_le (k : ℕ) :
    riemannShiftRatio ((k + 2 : ℕ) : ℝ) ≤ 19 / 50 * (1 / 8 : ℝ) ^ k := by
  have hπ1 := Real.pi_gt_d2
  have hπ3 := Real.pi_gt_three
  unfold riemannShiftRatio
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hcast : ((k + 2 : ℕ) : ℝ) = k + 2 := by push_cast; ring
  rw [hcast]
  set D := 4 * π ^ 2 - 6 * π with hD
  have hD0 : 0 < D := by rw [hD]; nlinarith
  -- the polynomial factor
  have hbern : 1 + (k : ℝ) * (33 / 50) ≤ (83 / 50 : ℝ) ^ k := by
    have := one_add_mul_le_pow (a := (33 / 50 : ℝ)) (by norm_num) k
    norm_num at this ⊢; linarith
  have hB0 : (0 : ℝ) ≤ (83 / 50 : ℝ) ^ k := by positivity
  have hpoly : (4 * π ^ 2 * (k + 2) - 6 * π) / D ≤ 583 / 200 * (83 / 50 : ℝ) ^ k := by
    rw [div_le_iff₀ hD0]
    have h1 : 583 / 200 * (1 + (k : ℝ) * (33 / 50)) * D ≤ 583 / 200 * (83 / 50 : ℝ) ^ k * D := by
      gcongr
    have h2 : 0 ≤ π * (π - 3.14) := mul_nonneg Real.pi_pos.le (by linarith)
    have h3 : 0 ≤ (k : ℝ) * (π * (π - 3.14)) := mul_nonneg hk0 h2
    rw [hD] at h1 ⊢
    nlinarith
  have hpoly0 : 0 ≤ (4 * π ^ 2 * (k + 2) - 6 * π) / D := by
    apply div_nonneg _ hD0.le; nlinarith
  have hsq : ((4 * π ^ 2 * (k + 2) - 6 * π) / D) ^ 2 ≤ (583 / 200) ^ 2 * ((83 / 50 : ℝ) ^ 2) ^ k := by
    calc ((4 * π ^ 2 * (k + 2) - 6 * π) / D) ^ 2 ≤ (583 / 200 * (83 / 50 : ℝ) ^ k) ^ 2 :=
          pow_le_pow_left₀ hpoly0 hpoly 2
      _ = _ := by rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm k 2]
  -- the exponential factor
  have hexp : Real.exp (-(π * ((k : ℝ) + 2 - 1))) ≤ 2 / 45 * (2 / 45 : ℝ) ^ k := by
    have hinv : Real.exp (-π) ≤ 2 / 45 := by
      rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num)]
      have := exp_pi_ge; norm_num at this ⊢; linarith
    have heq : Real.exp (-(π * ((k : ℝ) + 2 - 1))) = Real.exp (-π) ^ (k + 1) := by
      rw [← Real.exp_nat_mul]; push_cast; ring_nf
    rw [heq, pow_succ, mul_comm]
    apply mul_le_mul hinv (pow_le_pow_left₀ (Real.exp_pos _).le hinv k) (by positivity)
      (by norm_num)
  have hE0 : 0 ≤ Real.exp (-(π * ((k : ℝ) + 2 - 1))) := (Real.exp_pos _).le
  calc Real.exp (-(π * ((k : ℝ) + 2 - 1))) * ((4 * π ^ 2 * (k + 2) - 6 * π) / D) ^ 2
      ≤ (2 / 45 * (2 / 45 : ℝ) ^ k) * ((583 / 200) ^ 2 * ((83 / 50 : ℝ) ^ 2) ^ k) :=
        mul_le_mul hexp hsq (sq_nonneg _) (by positivity)
    _ = 2 / 45 * (583 / 200) ^ 2 * ((2 / 45 : ℝ) * (83 / 50) ^ 2) ^ k := by
        rw [mul_pow]; ring
    _ ≤ 19 / 50 * (1 / 8 : ℝ) ^ k := by
        apply mul_le_mul (by norm_num) (pow_le_pow_left₀ (by norm_num) (by norm_num) k)
          (by positivity) (by norm_num)

/-- **The log-shift sum.** `Σ_{2 ≤ n ≤ N} K(log n) ≤ (23/50) K(0)`. -/
theorem sum_riemannAutocorr_log_le (N : ℕ) :
    ∑ n ∈ Finset.Icc 2 N, riemannAutocorr (Real.log n) ≤ 23 / 50 * riemannAutocorr 0 := by
  have hK0 := riemannAutocorr_zero_pos
  have hterm : ∀ k : ℕ, riemannAutocorr (Real.log ((k + 2 : ℕ) : ℝ)) ≤
      (101 / 100) ^ 2 * (19 / 50 * (1 / 8 : ℝ) ^ k) * riemannAutocorr 0 := by
    intro k
    have hpos : (0 : ℝ) < ((k + 2 : ℕ) : ℝ) := by positivity
    set h := Real.log ((k + 2 : ℕ) : ℝ) / 2 with hh
    have hx : Real.exp (2 * h) = ((k + 2 : ℕ) : ℝ) := by
      rw [hh, show 2 * (Real.log ((k + 2 : ℕ) : ℝ) / 2) = Real.log ((k + 2 : ℕ) : ℝ) by ring,
        Real.exp_log hpos]
    have hh0 : 0 ≤ h := by
      rw [hh]; apply div_nonneg (Real.log_nonneg _) (by norm_num)
      push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have hx2 : 2 ≤ Real.exp (2 * h) := by
      rw [hx]; push_cast; linarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    have h1 := riemannAutocorr_two_mul_le hh0 hx2
    rw [hx] at h1
    rw [show Real.log ((k + 2 : ℕ) : ℝ) = 2 * h by rw [hh]; ring]
    calc riemannAutocorr (2 * h) ≤ (101 / 100) ^ 2 * riemannShiftRatio ((k + 2 : ℕ) : ℝ) *
          riemannAutocorr 0 := h1
      _ ≤ _ := by gcongr; exact riemannShiftRatio_le k
  rcases Nat.lt_or_ge N 2 with hN | hN
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]; positivity
  have hIcc : Finset.Icc 2 N = Finset.Ico 2 (N + 1) := (Finset.Ico_add_one_right_eq_Icc 2 N).symm
  rw [hIcc, Finset.sum_Ico_eq_sum_range]
  have hgeo : Summable fun k : ℕ => (1 / 8 : ℝ) ^ k :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  have hsum : ∑ k ∈ Finset.range (N + 1 - 2), (1 / 8 : ℝ) ^ k ≤ 8 / 7 := by
    calc ∑ k ∈ Finset.range (N + 1 - 2), (1 / 8 : ℝ) ^ k ≤ ∑' k : ℕ, (1 / 8 : ℝ) ^ k :=
          hgeo.sum_le_tsum _ fun k _ => by positivity
      _ = 8 / 7 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num
  calc ∑ k ∈ Finset.range (N + 1 - 2), riemannAutocorr (Real.log ((2 + k : ℕ) : ℝ))
      ≤ ∑ k ∈ Finset.range (N + 1 - 2),
          (101 / 100) ^ 2 * (19 / 50 * (1 / 8 : ℝ) ^ k) * riemannAutocorr 0 := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [show 2 + k = k + 2 by ring]; exact hterm k
    _ = (101 / 100) ^ 2 * (19 / 50) * riemannAutocorr 0 *
          ∑ k ∈ Finset.range (N + 1 - 2), (1 / 8 : ℝ) ^ k := by
        rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun k _ => ?_; ring
    _ ≤ (101 / 100) ^ 2 * (19 / 50) * riemannAutocorr 0 * (8 / 7) := by gcongr
    _ ≤ 23 / 50 * riemannAutocorr 0 := by nlinarith

/-! ## The truncated autocorrelation -/

theorem truncatedRiemannKernelReal_le (L u : ℝ) : truncatedRiemannKernelReal L u ≤ riemannKernelReal u := by
  unfold truncatedRiemannKernelReal
  calc riemannKernelReal u * bulkCutoff L u ≤ riemannKernelReal u * 1 :=
        mul_le_mul_of_nonneg_left (bulkCutoff_le_one L u) (riemannKernelReal_pos u).le
    _ = _ := mul_one _

theorem truncatedRiemannAutocorr_le_riemannAutocorr (L y : ℝ) :
    truncatedRiemannAutocorr L y ≤ riemannAutocorr y := by
  unfold truncatedRiemannAutocorr riemannAutocorr
  refine integral_mono (integrable_truncatedRiemannKernel_prod L y)
    (integrable_riemannKernelReal_mul y) fun t => ?_
  exact mul_le_mul (truncatedRiemannKernelReal_le L t) (truncatedRiemannKernelReal_le L _)
    (truncatedRiemannKernelReal_nonneg L _) (riemannKernelReal_pos t).le

theorem truncatedRiemannKernelReal_eq_zero_of_le {L u : ℝ} (hu : L ≤ |u|) :
    truncatedRiemannKernelReal L u = 0 := by
  unfold truncatedRiemannKernelReal; rw [bulkCutoff_eq_zero hu, mul_zero]

theorem truncatedRiemannAutocorr_eq_zero {L y : ℝ} (hy : 2 * L ≤ |y|) :
    truncatedRiemannAutocorr L y = 0 := by
  unfold truncatedRiemannAutocorr
  have hz : (fun t => truncatedRiemannKernelReal L t * truncatedRiemannKernelReal L (t - y)) =
      fun _ => (0 : ℝ) := by
    funext t
    by_cases ht : L ≤ |t|
    · rw [truncatedRiemannKernelReal_eq_zero_of_le ht, zero_mul]
    · have ht' : L ≤ |t - y| := by
        by_contra h'
        push Not at ht h'
        have : |y| ≤ |t| + |t - y| := by
          calc |y| = |t - (t - y)| := by ring_nf
            _ ≤ |t| + |t - y| := abs_sub _ _
        linarith
      rw [truncatedRiemannKernelReal_eq_zero_of_le ht', mul_zero]
  rw [hz, integral_zero]

theorem truncatedRiemannAutocorr_neg (L y : ℝ) :
    truncatedRiemannAutocorr L (-y) = truncatedRiemannAutocorr L y := by
  unfold truncatedRiemannAutocorr
  rw [← integral_sub_right_eq_self (fun t => truncatedRiemannKernelReal L t *
    truncatedRiemannKernelReal L (t - -y)) y]
  congr 1; funext t
  rw [show t - y - -y = t by ring, mul_comm]

/-- The bulk of the kernel carries all but `η` of `K(0)`. -/
theorem exists_truncatedRiemannAutocorr_zero_ge {η : ℝ} (hη : 0 < η) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L → riemannAutocorr 0 - η ≤ truncatedRiemannAutocorr L 0 := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannPhiKernel_le_exp (B := 4) (by norm_num)
  have hΦ : ∀ x, riemannKernelReal x ≤ C * Real.exp (-(4 * |x|)) := by
    intro x
    have h := hC x
    rwa [riemannPhiKernel_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (riemannKernelReal_pos x)] at h
  set G := ∫ t : ℝ, Real.exp (-|t|) with hG
  have hG0 : 0 ≤ G := integral_nonneg fun _ => (Real.exp_pos _).le
  refine ⟨1 + C ^ 2 * G / (7 * η), fun L hL => ?_⟩
  have hL1 : 1 ≤ L := by
    have : 0 ≤ C ^ 2 * G / (7 * η) := by positivity
    linarith
  set a := Real.exp (-(7 * (L - 1))) with ha
  have hpt : ∀ t, riemannKernelReal t * riemannKernelReal (t - 0) -
      truncatedRiemannKernelReal L t * truncatedRiemannKernelReal L (t - 0) ≤
      C ^ 2 * a * Real.exp (-|t|) := by
    intro t
    rw [sub_zero]
    by_cases ht : |t| ≤ L - 1
    · have e : truncatedRiemannKernelReal L t = riemannKernelReal t := by
        unfold truncatedRiemannKernelReal; rw [bulkCutoff_eq_one ht, mul_one]
      rw [e, sub_self]; positivity
    · push Not at ht
      have h0 := truncatedRiemannKernelReal_nonneg L t
      have hp := riemannKernelReal_pos t
      have h1 := hΦ t
      have hsq : riemannKernelReal t * riemannKernelReal t ≤
          (C * Real.exp (-(4 * |t|))) * (C * Real.exp (-(4 * |t|))) :=
        mul_le_mul h1 h1 hp.le (by positivity)
      have hexp : Real.exp (-(4 * |t|)) * Real.exp (-(4 * |t|)) ≤ a * Real.exp (-|t|) := by
        rw [ha, ← Real.exp_add, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        linarith
      have hC2 : (C * Real.exp (-(4 * |t|))) * (C * Real.exp (-(4 * |t|))) ≤
          C ^ 2 * (a * Real.exp (-|t|)) := by
        rw [show (C * Real.exp (-(4 * |t|))) * (C * Real.exp (-(4 * |t|))) =
          C ^ 2 * (Real.exp (-(4 * |t|)) * Real.exp (-(4 * |t|))) by ring]
        exact mul_le_mul_of_nonneg_left hexp (sq_nonneg C)
      nlinarith [mul_nonneg h0 h0]
  have hdiff : riemannAutocorr 0 - truncatedRiemannAutocorr L 0 ≤ C ^ 2 * a * G := by
    unfold riemannAutocorr truncatedRiemannAutocorr
    rw [← integral_sub (integrable_riemannKernelReal_mul 0)
      (integrable_truncatedRiemannKernel_prod L 0), hG, ← integral_const_mul]
    exact integral_mono ((integrable_riemannKernelReal_mul 0).sub
      (integrable_truncatedRiemannKernel_prod L 0)) (integrable_exp_neg_abs.const_mul _) hpt
  have hsmall : C ^ 2 * a * G ≤ η := by
    have hlin : 1 + 7 * (L - 1) ≤ Real.exp (7 * (L - 1)) := by
      have := Real.add_one_le_exp (7 * (L - 1)); linarith
    have hae : a * Real.exp (7 * (L - 1)) = 1 := by
      rw [ha, ← Real.exp_add]; simp
    have ha0 : 0 < a := Real.exp_pos _
    have hL' : C ^ 2 * G ≤ 7 * η * (L - 1) := by
      have : C ^ 2 * G / (7 * η) ≤ L - 1 := by linarith
      rw [div_le_iff₀ (by positivity)] at this
      linarith
    have h1 : C ^ 2 * G ≤ η * Real.exp (7 * (L - 1)) := by
      have := mul_le_mul_of_nonneg_left hlin hη.le
      linarith
    calc C ^ 2 * a * G = a * (C ^ 2 * G) := by ring
      _ ≤ a * (η * Real.exp (7 * (L - 1))) := mul_le_mul_of_nonneg_left h1 ha0.le
      _ = η * (a * Real.exp (7 * (L - 1))) := by ring
      _ = η := by rw [hae, mul_one]
  linarith

/-! ## The log-shift test -/

/-- The log-shift difference `Φχ_L − Φχ_L(· − c)`. -/
def logShiftRiemannDifference (L c : ℝ) (u : ℝ) : ℂ :=
  truncatedRiemannKernel L u - truncatedRiemannKernel L (u - c)

theorem logShiftRiemannDifference_eq (L c : ℝ) :
    logShiftRiemannDifference L c =
      fun u => ((truncatedRiemannKernelReal L u - truncatedRiemannKernelReal L (u - c) : ℝ) : ℂ) := by
  funext u
  simp only [logShiftRiemannDifference, truncatedRiemannKernel_eq]
  push_cast; ring

theorem contDiff_logShiftRiemannDifference (L c : ℝ) :
    ContDiff ℝ 2 (logShiftRiemannDifference L c) := by
  have h := contDiff_nearRadicalTest L (fun _ : Fin 1 => (1 : ℂ))
  have h1 : ContDiff ℝ 2 fun u : ℝ => truncatedRiemannKernel L (u - c) :=
    h.comp (contDiff_id.sub contDiff_const)
  exact h.sub h1

theorem hasCompactSupport_logShiftRiemannDifference (L c : ℝ) :
    HasCompactSupport (logShiftRiemannDifference L c) :=
  (hasCompactSupport_truncatedRiemannKernel L).sub
    (hasCompactSupport_comp_sub (hasCompactSupport_truncatedRiemannKernel L) c)

/-- The transform of the log-shift difference: `(1 − e^{izc}) û(z)`. -/
theorem paperFT_logShiftRiemannDifference (L c : ℝ) (z : ℂ) :
    paperFT (logShiftRiemannDifference L c) z =
      (1 - Complex.exp (I * z * c)) * paperFT (truncatedRiemannKernel L) z := by
  have h0 : Integrable fun u : ℝ => truncatedRiemannKernel L u * Complex.exp (I * z * u) := by
    simpa using integrable_translate_mul_cexp L 0 z
  have h1 := integrable_translate_mul_cexp L c z
  have e1 := paperFT_comp_sub (truncatedRiemannKernel L) c z
  unfold paperFT at e1 ⊢
  have hsplit : (fun u : ℝ => logShiftRiemannDifference L c u * Complex.exp (I * z * u)) =
      fun u : ℝ => truncatedRiemannKernel L u * Complex.exp (I * z * u) -
        truncatedRiemannKernel L (u - c) * Complex.exp (I * z * u) := by
    funext u; simp only [logShiftRiemannDifference]; ring
  beta_reduce at e1
  rw [hsplit, integral_sub h0 h1, e1]
  ring

theorem norm_logShiftMultiplier_le {c : ℝ} (hc : 0 ≤ c) {z : ℂ} (hz : |z.im| ≤ 1 / 2) :
    ‖1 - Complex.exp (I * z * c)‖ ≤ 1 + Real.exp (c / 2) := by
  have hre : (I * z * (c : ℂ)).re = -(z.im * c) := by simp [Complex.mul_re]
  have h1 : -(z.im * c) ≤ c / 2 := by
    have h2 : |z.im * c| ≤ 1 / 2 * c := by
      rw [abs_mul, abs_of_nonneg hc]; exact mul_le_mul_of_nonneg_right hz hc
    have := neg_abs_le (z.im * c)
    linarith
  calc ‖1 - Complex.exp (I * z * c)‖ ≤ ‖(1 : ℂ)‖ + ‖Complex.exp (I * z * c)‖ := norm_sub_le _ _
    _ = 1 + Real.exp (-(z.im * c)) := by rw [norm_one, Complex.norm_exp, hre]
    _ ≤ 1 + Real.exp (c / 2) := by gcongr

/-- The zero side of the log-shift difference. -/
theorem norm_W_logShiftRiemannDifference_le (L : ℝ) {c : ℝ} (hc : 0 ≤ c) {Λ : ℝ}
    (hΛ : ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ Λ) :
    ‖zetaZeroConfig.W (logShiftRiemannDifference L c) (logShiftRiemannDifference L c)‖ ≤
      (1 + Real.exp (c / 2)) ^ 2 * ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) := by
  have hE0 := truncatedRiemannTailEnergy_nonneg L
  have hm0 : 0 ≤ 1 + Real.exp (c / 2) := by positivity
  have h := norm_W_le_of_zero_bound (f := logShiftRiemannDifference L c)
    (E := (1 + Real.exp (c / 2)) * truncatedRiemannTailEnergy L) (by positivity) (fun ρ => ?_)
  · calc _ ≤ (5 / 4) * zetaInvSqSum * ((1 + Real.exp (c / 2)) * truncatedRiemannTailEnergy L) ^ 2 := h
      _ = _ := by ring
  have hmem := ρ.2
  have hstrip' : 0 < (ρ : ℂ).re ∧ (ρ : ℂ).re < 1 := by
    have h : IsNontrivialZero (ρ : ℂ) := hmem
    exact ⟨h.2.1, h.2.2⟩
  have hIm : |(gammaOf (ρ : ℂ)).im| ≤ 1 / 2 := (WeilEF.abs_gammaOf_im_lt hstrip').le
  have hIm' : |((starRingEnd ℂ) (gammaOf (ρ : ℂ))).im| ≤ 1 / 2 := by
    rw [Complex.conj_im, abs_neg]; exact hIm
  obtain ⟨hv1, hv2⟩ := truncatedRiemannKernel_zero_bound L hΛ ρ
  constructor
  · rw [paperFT_logShiftRiemannDifference, norm_mul]
    have hm := norm_logShiftMultiplier_le hc hIm
    calc (1 + |(ρ : ℂ).im|) * (‖1 - Complex.exp (I * gammaOf ρ * c)‖ *
          ‖paperFT (truncatedRiemannKernel L) (gammaOf ρ)‖)
        = ‖1 - Complex.exp (I * gammaOf ρ * c)‖ *
          ((1 + |(ρ : ℂ).im|) * ‖paperFT (truncatedRiemannKernel L) (gammaOf ρ)‖) := by ring
      _ ≤ (1 + Real.exp (c / 2)) * truncatedRiemannTailEnergy L :=
          mul_le_mul hm hv1 (by positivity) hm0
  · rw [paperFT_logShiftRiemannDifference, norm_mul]
    have hm := norm_logShiftMultiplier_le hc hIm'
    calc (1 + |(ρ : ℂ).im|) * (‖1 - Complex.exp (I * (starRingEnd ℂ) (gammaOf ρ) * c)‖ *
          ‖paperFT (truncatedRiemannKernel L) ((starRingEnd ℂ) (gammaOf ρ))‖)
        = ‖1 - Complex.exp (I * (starRingEnd ℂ) (gammaOf ρ) * c)‖ *
          ((1 + |(ρ : ℂ).im|) *
            ‖paperFT (truncatedRiemannKernel L) ((starRingEnd ℂ) (gammaOf ρ))‖) := by ring
      _ ≤ (1 + Real.exp (c / 2)) * truncatedRiemannTailEnergy L :=
          mul_le_mul hm hv2 (by positivity) hm0

/-- The autocorrelation of the log-shift difference: `2K_L(y) − K_L(y + c) − K_L(y − c)`. -/
theorem weilTest_logShiftRiemannDifference (L c y : ℝ) :
    EF.weilTest (logShiftRiemannDifference L c) (logShiftRiemannDifference L c) y =
      ((2 * truncatedRiemannAutocorr L y - truncatedRiemannAutocorr L (y + c) -
        truncatedRiemannAutocorr L (y - c) : ℝ) : ℂ) := by
  rw [logShiftRiemannDifference_eq, weilTest_ofReal_eq]
  congr 1
  have hF : ∀ t, truncatedRiemannKernelReal L t - truncatedRiemannKernelReal L (t - c) =
      ∑ i : Fin 2, ![1, -1] i * truncatedRiemannKernelReal L (t - ![0, c] i) := by
    intro t
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one, sub_zero]
    ring
  have e := integral_translateComb_autocorr Finset.univ ![1, -1] ![0, c]
    (continuous_truncatedRiemannKernelReal L) (hasCompactSupport_truncatedRiemannKernelReal L) y
  have hk : ∀ v, (∫ t, truncatedRiemannKernelReal L t * truncatedRiemannKernelReal L (t - v)) =
      truncatedRiemannAutocorr L v := fun v => rfl
  simp only [hk] at e
  have hint : (∫ t, (truncatedRiemannKernelReal L t - truncatedRiemannKernelReal L (t - c)) *
      (truncatedRiemannKernelReal L (t - y) - truncatedRiemannKernelReal L (t - y - c))) =
      ∫ t, (∑ i : Fin 2, ![1, -1] i * truncatedRiemannKernelReal L (t - ![0, c] i)) *
        (∑ j : Fin 2, ![1, -1] j * truncatedRiemannKernelReal L (t - y - ![0, c] j)) := by
    congr 1; funext t; rw [hF, hF (t - y)]
  rw [hint, e]
  simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [show y + 0 - 0 = y by ring, show y + c - 0 = y + c by ring, show y + 0 - c = y - c by ring,
    show y + c - c = y by ring]
  ring

/-! ## The zero side against the window -/

/-- The near-radical energy of `Φχ_L` beats `e^{2L}`. -/
theorem exists_exp_mul_nearRadicalEnergy_le {ε : ℝ} (hε : 0 < ε) :
    ∃ L₀ : ℝ, ∀ L : ℝ, L₀ ≤ L →
      Real.exp (2 * L) * ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) ≤ ε := by
  obtain ⟨Λ, hΛ0, hΛ⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
  obtain ⟨M, hM0, hM⟩ := exists_integral_norm_sq_truncatedRiemannKernel_le
  set S := zetaInvSqSum with hS
  have hS0 : 0 ≤ S := zetaInvSqSum_nonneg
  have hc : 0 < ε / (Real.exp 2 * (M + 1)) := by positivity
  obtain ⟨Y₁, hY₁⟩ := Filter.eventually_atTop.1
    ((tendsto_order.1 (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1)).2 _ hc)
  set Ystar := max (max 100 (Real.log (720 * nearRadicalConst S Λ + 1))) (max Y₁ 1) with hYstar
  refine ⟨1 + |Real.log Ystar| / 2 + 1, fun L hL => ?_⟩
  set Y₀ := Real.exp (2 * (L - 1)) with hY₀def
  have hYstar_pos : 0 < Ystar :=
    lt_of_lt_of_le (by norm_num) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hY₀ge : Ystar ≤ Y₀ := by
    have : Real.log Ystar ≤ 2 * (L - 1) := by
      have := le_abs_self (Real.log Ystar); linarith
    calc Ystar = Real.exp (Real.log Ystar) := (Real.exp_log hYstar_pos).symm
      _ ≤ Y₀ := Real.exp_le_exp.mpr this
  have hY100 : 100 ≤ Y₀ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY₀ge
  have hYlog : Real.log (720 * nearRadicalConst S Λ + 1) ≤ Y₀ :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY₀ge
  have hY₁le : Y₁ ≤ Y₀ := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hY₀ge
  have hY40 : 40 ≤ Y₀ := by linarith
  have hkY : ((0 + 2 : ℕ) : ℝ) + 1 ≤ Y₀ / 10 := by push_cast; linarith
  have hW := nearRadicalEnergy_le_ratio L hΛ hY40 hkY
  rw [← hY₀def, ← hS] at hW
  have hratio := nearRadical_ratio_le (k := 0 + 2) hS0 hΛ0 hkY hY100 hYlog
  have hI : 0 ≤ ∫ u : ℝ, ‖truncatedRiemannKernel L u‖ ^ 2 := integral_nonneg fun _ => by positivity
  have hIM : ∫ u : ℝ, ‖truncatedRiemannKernel L u‖ ^ 2 ≤ M := hM L
  have hE : (5 / 4) * S * truncatedRiemannTailEnergy L ^ 2 ≤ Real.exp (-Y₀) * (M + 1) := by
    calc (5 / 4) * S * truncatedRiemannTailEnergy L ^ 2
        ≤ Real.exp (-Y₀) * ∫ u : ℝ, ‖truncatedRiemannKernel L u‖ ^ 2 :=
          hW.trans (mul_le_mul_of_nonneg_right hratio hI)
      _ ≤ Real.exp (-Y₀) * (M + 1) := mul_le_mul_of_nonneg_left (by linarith) (Real.exp_pos _).le
  have hexp2 : Real.exp (2 * L) = Real.exp 2 * Y₀ := by
    rw [hY₀def, ← Real.exp_add]; ring_nf
  have hsmall : Y₀ ^ 1 * Real.exp (-Y₀) < ε / (Real.exp 2 * (M + 1)) := hY₁ Y₀ hY₁le
  rw [pow_one, lt_div_iff₀ (by positivity)] at hsmall
  calc Real.exp (2 * L) * ((5 / 4) * S * truncatedRiemannTailEnergy L ^ 2)
      ≤ Real.exp (2 * L) * (Real.exp (-Y₀) * (M + 1)) :=
        mul_le_mul_of_nonneg_left hE (Real.exp_pos _).le
    _ = Y₀ * Real.exp (-Y₀) * (Real.exp 2 * (M + 1)) := by rw [hexp2]; ring
    _ ≤ ε := hsmall.le

/-! ## Order rigidity from below -/

/-- **No Weil-positive completion minorizes `Λ`.** If `lam` is Weil-positive with the pole term
(`WeilPositiveFull`) and `lam(n) ≤ Λ(n)` for all `n ≥ 2`, then `lam(n) = Λ(n)` for all `n ≥ 2`.
Unconditional; no sign or growth condition on `lam` is assumed. -/
theorem eq_vonMangoldt_of_weilPositiveFull_of_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    (hle : ∀ n, 2 ≤ n → lam n ≤ (ArithmeticFunction.vonMangoldt n : ℝ)) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  by_contra hne
  push Not at hne
  obtain ⟨n₀, hn₀, hne₀⟩ := hne
  -- the deficit `v(n) = (Λ(n) − lam(n))/√n ≥ 0`
  set v : ℕ → ℝ := fun n => if 2 ≤ n then
    ((ArithmeticFunction.vonMangoldt n : ℝ) - lam n) / Real.sqrt n else 0 with hvdef
  have hv0 : ∀ n, 0 ≤ v n := by
    intro n; simp only [hvdef]
    split_ifs with h2
    · exact div_nonneg (sub_nonneg.mpr (hle n h2)) (Real.sqrt_nonneg _)
    · exact le_rfl
  have hn₀R : (1 : ℝ) < n₀ := by exact_mod_cast (show 1 < n₀ by omega)
  have hvn₀ : 0 < v n₀ := by
    simp only [hvdef, if_pos hn₀]
    exact div_pos (sub_pos.mpr (lt_of_le_of_ne (hle n₀ hn₀) hne₀))
      (Real.sqrt_pos.mpr (by linarith))
  set K₀ := riemannAutocorr 0 with hK₀
  have hK₀pos : 0 < K₀ := riemannAutocorr_zero_pos
  -- the truncation
  obtain ⟨L₁, hL₁⟩ := exists_truncatedRiemannAutocorr_zero_ge (η := K₀ / 25) (by positivity)
  obtain ⟨L₂, hL₂⟩ := exists_exp_mul_nearRadicalEnergy_le (ε := v n₀ * K₀ / 100) (by positivity)
  set L := max (max L₁ L₂) (Real.log n₀ / 2 + 1) with hL
  have hLL₁ : L₁ ≤ L := le_trans (le_max_left _ _) (le_max_left _ _)
  have hLL₂ : L₂ ≤ L := le_trans (le_max_right _ _) (le_max_left _ _)
  have hLn₀ : Real.log n₀ / 2 + 1 ≤ L := le_max_right _ _
  have hlog₀ : 0 < Real.log n₀ := Real.log_pos hn₀R
  have hL0 : 0 < L := by linarith
  have hKL0 := hL₁ L hLL₁
  have hEL := hL₂ L hLL₂
  -- the window and its argmax
  set N := ⌊Real.exp (2 * L)⌋₊ with hN
  have hn₀N : n₀ ≤ N := by
    apply Nat.le_floor
    calc (n₀ : ℝ) = Real.exp (Real.log n₀) := (Real.exp_log (by linarith)).symm
      _ ≤ Real.exp (2 * L) := Real.exp_le_exp.mpr (by linarith)
  have hne : (Finset.Icc 2 N).Nonempty := ⟨n₀, Finset.mem_Icc.mpr ⟨hn₀, hn₀N⟩⟩
  obtain ⟨m, hmW, hmax⟩ := Finset.exists_max_image (Finset.Icc 2 N) v hne
  have hm2 : 2 ≤ m := (Finset.mem_Icc.mp hmW).1
  have hmN : m ≤ N := (Finset.mem_Icc.mp hmW).2
  have hMge : v n₀ ≤ v m := hmax n₀ (Finset.mem_Icc.mpr ⟨hn₀, hn₀N⟩)
  have hmR : (1 : ℝ) < m := by exact_mod_cast (show 1 < m by omega)
  set c := Real.log m with hc
  have hc0 : 0 ≤ c := (Real.log_pos hmR).le
  have hcL : c ≤ 2 * L := by
    rw [hc, Real.log_le_iff_le_exp (by linarith)]
    calc (m : ℝ) ≤ N := by exact_mod_cast hmN
      _ ≤ Real.exp (2 * L) := Nat.floor_le (Real.exp_pos _).le
  -- window facts: outside `[2, N]` the atoms see nothing
  have hout : ∀ n : ℕ, N < n → truncatedRiemannAutocorr L (Real.log n) = 0 := by
    intro n hn
    apply truncatedRiemannAutocorr_eq_zero
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have hlt : Real.exp (2 * L) < n := by
      have := Nat.lt_floor_add_one (Real.exp (2 * L))
      have h2 : ((N : ℝ) + 1) ≤ n := by exact_mod_cast hn
      rw [← hN] at this; linarith
    have hlog : 2 * L < Real.log n := by rw [Real.lt_log_iff_exp_lt hnpos]; exact hlt
    rw [abs_of_pos (by linarith)]; exact hlog.le
  -- the test
  set f := logShiftRiemannDifference L c with hf
  have hfd : ContDiff ℝ 2 f := contDiff_logShiftRiemannDifference L c
  have hfc : HasCompactSupport f := hasCompactSupport_logShiftRiemannDifference L c
  set k := EF.weilTest f f with hk
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  have hpos := hW f hfd hfc
  rw [weilFullFunctional_eq_sub lam hkc, ← weilFullFunctional_vonMangoldt,
    ← zeta_W_eq_weilFullFunctional hfd hfc] at hpos
  set a : ℕ → ℝ := fun n => if 2 ≤ n then (lam n - ArithmeticFunction.vonMangoldt n) / Real.sqrt n
    else 0 with ha
  have hav : ∀ n, a n = -v n := by
    intro n; simp only [ha, hvdef]
    split_ifs
    · ring
    · ring
  set kr : ℝ → ℝ := fun y => 2 * truncatedRiemannAutocorr L y - truncatedRiemannAutocorr L (y + c) -
    truncatedRiemannAutocorr L (y - c) with hkr
  have hkeq : ∀ y, k y = ((kr y : ℝ) : ℂ) := fun y => weilTest_logShiftRiemannDifference L c y
  have hsum := summable_primeAtoms a hkc
  have hterm_re : ∀ n : ℕ, (((a n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))).re =
      -(v n * (kr (Real.log n) + kr (-Real.log n))) := by
    intro n
    rw [hkeq, hkeq, ← Complex.ofReal_add, ← Complex.ofReal_mul, Complex.ofReal_re, hav]; ring
  have hsumre : Summable fun n : ℕ => (((a n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))).re :=
    Complex.reCLM.summable hsum
  set F : ℕ → ℝ := fun n => v n * (kr (Real.log n) + kr (-Real.log n)) with hF
  have hFs : Summable F := by
    have := hsumre.neg
    refine this.congr fun n => ?_
    rw [hterm_re, neg_neg]
  have hmain : 0 ≤ (zetaZeroConfig.W f f).re + ∑' n, F n := by
    rw [Complex.sub_re, Complex.re_tsum hsum] at hpos
    have e : (∑' n : ℕ, (((a n : ℝ) : ℂ) * (k (Real.log n) + k (-Real.log n))).re) =
        -∑' n, F n := by
      rw [← tsum_neg]; exact tsum_congr hterm_re
    rw [e] at hpos
    linarith
  -- the comparison function
  set G : ℕ → ℝ := fun n => 4 * (v n * truncatedRiemannAutocorr L (Real.log n)) -
    2 * (if n = m then v m * truncatedRiemannAutocorr L 0 else 0) with hG
  have hFG : ∀ n, F n ≤ G n := by
    intro n
    have hsym : kr (Real.log n) + kr (-Real.log n) = 4 * truncatedRiemannAutocorr L (Real.log n) -
        2 * truncatedRiemannAutocorr L (Real.log n + c) -
        2 * truncatedRiemannAutocorr L (Real.log n - c) := by
      simp only [hkr]
      rw [truncatedRiemannAutocorr_neg L (Real.log n),
        show -Real.log n + c = -(Real.log n - c) by ring,
        show -Real.log n - c = -(Real.log n + c) by ring,
        truncatedRiemannAutocorr_neg L (Real.log n - c),
        truncatedRiemannAutocorr_neg L (Real.log n + c)]
      ring
    have h1 := truncatedRiemannAutocorr_nonneg L (Real.log n + c)
    have h2 := truncatedRiemannAutocorr_nonneg L (Real.log n - c)
    have hvn := hv0 n
    simp only [hF, hG]
    rw [hsym]
    split_ifs with hnm
    · subst hnm
      rw [show Real.log n - c = 0 by rw [hc]; ring]
      nlinarith [mul_nonneg hvn h1]
    · nlinarith [mul_nonneg hvn h1, mul_nonneg hvn h2]
  have hGs : Summable G := by
    refine summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun n hn => ?_
    rw [Finset.mem_range, not_lt] at hn
    have hnN : N < n := by omega
    have hnm : n ≠ m := by omega
    simp only [hG, hout n hnN, if_neg hnm]; ring
  have hsum1 : Summable fun n : ℕ => v n * truncatedRiemannAutocorr L (Real.log n) := by
    refine summable_of_ne_finset_zero (s := Finset.range (N + 1)) fun n hn => ?_
    rw [Finset.mem_range, not_lt] at hn
    rw [hout n (by omega), mul_zero]
  have htsumG : ∑' n, G n = 4 * ∑' n, v n * truncatedRiemannAutocorr L (Real.log n) -
      2 * (v m * truncatedRiemannAutocorr L 0) := by
    have h2 : Summable fun n : ℕ => 2 * (if n = m then v m * truncatedRiemannAutocorr L 0 else 0) :=
      summable_of_ne_finset_zero (s := {m}) fun n hn => by
        rw [Finset.mem_singleton] at hn; simp [hn]
    simp only [hG]
    rw [Summable.tsum_sub (hsum1.mul_left 4) h2, tsum_mul_left, tsum_mul_left, tsum_ite_eq]
  -- the atom sum on the window
  have hwin : ∑' n, v n * truncatedRiemannAutocorr L (Real.log n) ≤ v m * (23 / 50 * K₀) := by
    rw [tsum_eq_sum (s := Finset.Icc 2 N) fun n hn => ?_]
    · calc ∑ n ∈ Finset.Icc 2 N, v n * truncatedRiemannAutocorr L (Real.log n)
          ≤ ∑ n ∈ Finset.Icc 2 N, v m * riemannAutocorr (Real.log n) :=
            Finset.sum_le_sum fun n hn => mul_le_mul (hmax n hn)
              (truncatedRiemannAutocorr_le_riemannAutocorr L _)
              (truncatedRiemannAutocorr_nonneg L _) (hv0 m)
        _ = v m * ∑ n ∈ Finset.Icc 2 N, riemannAutocorr (Real.log n) := by rw [Finset.mul_sum]
        _ ≤ v m * (23 / 50 * K₀) :=
            mul_le_mul_of_nonneg_left (sum_riemannAutocorr_log_le N) (hv0 m)
    · rw [Finset.mem_Icc, not_and_or] at hn
      rcases hn with hn | hn
      · push Not at hn
        simp only [hvdef, if_neg (show ¬ 2 ≤ n by omega), zero_mul]
      · push Not at hn
        rw [hout n hn, mul_zero]
  -- the zero side
  have hWnorm : ‖zetaZeroConfig.W f f‖ ≤ v n₀ * K₀ / 25 := by
    obtain ⟨Λ', -, hΛ'⟩ := GaloisForLFunctions.HTGeometry.exists_bound_deriv_smoothTransition
    have h := norm_W_logShiftRiemannDifference_le L hc0 hΛ'
    have hmul : (1 + Real.exp (c / 2)) ^ 2 ≤ 4 * Real.exp (2 * L) := by
      have h1 : Real.exp (c / 2) ≤ Real.exp L := Real.exp_le_exp.mpr (by linarith)
      have h2 : 1 ≤ Real.exp L := Real.one_le_exp hL0.le
      have h3 : Real.exp L ^ 2 = Real.exp (2 * L) := by rw [← Real.exp_nat_mul]; ring_nf
      have h4 : 0 ≤ 1 + Real.exp (c / 2) := by positivity
      have h5 : 1 + Real.exp (c / 2) ≤ 2 * Real.exp L := by linarith
      calc (1 + Real.exp (c / 2)) ^ 2 ≤ (2 * Real.exp L) ^ 2 := pow_le_pow_left₀ h4 h5 2
        _ = 4 * Real.exp L ^ 2 := by ring
        _ = 4 * Real.exp (2 * L) := by rw [h3]
    have hE0 : 0 ≤ (5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2 := by
      have := zetaInvSqSum_nonneg; positivity
    calc ‖zetaZeroConfig.W f f‖ ≤ (1 + Real.exp (c / 2)) ^ 2 *
          ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) := h
      _ ≤ 4 * Real.exp (2 * L) * ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2) :=
          mul_le_mul_of_nonneg_right hmul hE0
      _ = 4 * (Real.exp (2 * L) * ((5 / 4) * zetaInvSqSum * truncatedRiemannTailEnergy L ^ 2)) := by
          ring
      _ ≤ 4 * (v n₀ * K₀ / 100) := by gcongr
      _ = v n₀ * K₀ / 25 := by ring
  -- assembling
  have hFG' : ∑' n, F n ≤ ∑' n, G n := hFs.tsum_le_tsum hFG hGs
  rw [htsumG] at hFG'
  have hWre := Complex.re_le_norm (zetaZeroConfig.W f f)
  have hvm := hv0 m
  have hKL : K₀ - K₀ / 25 ≤ truncatedRiemannAutocorr L 0 := hKL0
  have h1 : v m * (K₀ - K₀ / 25) ≤ v m * truncatedRiemannAutocorr L 0 :=
    mul_le_mul_of_nonneg_left hKL hvm
  have h2 : v n₀ * K₀ ≤ v m * K₀ := mul_le_mul_of_nonneg_right hMge hK₀pos.le
  have h3 : 0 < v n₀ * K₀ := mul_pos hvn₀ hK₀pos
  linarith

/-- **RH is the existence of a Weil-positive minorant of `Λ`.** A full-cone Weil-positive
`lam ≤ Λ` exists iff RH holds, and then `lam = Λ` on `n ≥ 2`. -/
theorem riemannHypothesis_iff_exists_weilPositiveFull_le :
    RiemannHypothesis ↔ ∃ lam : ℕ → ℝ, WeilPositiveFull lam ∧
      ∀ n, 2 ≤ n → lam n ≤ (ArithmeticFunction.vonMangoldt n : ℝ) := by
  constructor
  · intro hRH
    exact ⟨_, riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH, fun _ _ => le_rfl⟩
  · rintro ⟨lam, hW, hle⟩
    have h := eq_vonMangoldt_of_weilPositiveFull_of_le hW hle
    refine riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mpr fun f hf hfc => ?_
    rw [weilFullFunctional_congr (lam' := lam) (fun n hn => (h n hn).symm)]
    exact hW f hf hfc

end

end RHTower
