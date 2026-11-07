import GaloisForLFunctions.RigidArithmeticOfCuts.TheSelbergLedgerSeparatesTheTwin
import Mathlib.NumberTheory.LSeries.Dirichlet

/-!
# The quadratic gap is the harmonic mass

The Selberg ledger separates the Liouville twin at scale `N`. This module computes what the separation reads.

A filtered twin is `Λ − 2b` with `0 ≤ b ≤ Λ 1_{Ω even}`: only a chosen set of even prime powers changes sign, so it may agree
with `Λ` on every prime power below a level. For a producer of slope `L`, with `O` uniform in `b`,

`ledger(Selberg Λ, N) − ledger(Selberg (Λ − 2b), N) = 4 L N Σ_{e ≤ N} b(e)/e + O(N^{3/4})`.

So the separation reads one number, the harmonic mass of the changed even prime powers.

* The Liouville twin has mass `Σ_m Λ(m)/m² = −ζ′/ζ(2)`, so its gap is `4 L (−ζ′/ζ(2)) N`, asymptotically exactly.
* A twin agreeing with `Λ` up to level `y` is still separated at scale `N`, by the positive constant `4 L (κ − H(y))`.
* That constant tends to `0` with `y`. A level growing with `N` makes the gap `o(N)`.

The ledger passes the twin and every filter of it, and what it reads is a value at `s = 2`. It does not break parity.
-/

open Finset Filter Topology
open ArithmeticFunction (vonMangoldt cardFactors)
open GaloisForLFunctions.ArithmeticKreinLangerTheory
open GaloisForLFunctions.ArithmeticAuxiliaryDynamics
open GaloisForLFunctions.ArithmeticOfSquareRootPrecision

noncomputable section

namespace GaloisForLFunctions.RigidArithmeticOfCuts

/-- A filtered twin: `Λ` with the even prime powers carried by `b` reversed. -/
def filteredTwin (b : ℕ → ℝ) (n : ℕ) : ℝ := vonMangoldtWeight n - 2 * b n

/-- The harmonic mass of a filter up to `N`. -/
def harmonicMass (b : ℕ → ℝ) (N : ℕ) : ℝ := ∑ e ∈ Ioc 0 N, b e / e

/-- An admissible filter: nonnegative and below the even part of `Λ`. -/
structure IsEvenFilter (b : ℕ → ℝ) : Prop where
  nonneg : ∀ n, 0 ≤ b n
  le_even : ∀ n, b n ≤ evenVonMangoldt n

variable {c : ℕ →₀ ℤ} {m B : ℕ} {b : ℕ → ℝ}

theorem IsEvenFilter.sum_le (hb : IsEvenFilter b) (N : ℕ) :
    ∑ e ∈ Ioc 0 N, b e ≤ (Real.log 4 + 4) * (Nat.sqrt N : ℝ) := by
  refine (sum_le_sum fun e _ => hb.le_even e).trans ?_
  rw [sum_evenVonMangoldt]
  exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg _)

theorem ledger_mono (hP : IsProducer c m B) {a a' : ℕ → ℝ} (h : ∀ d, a d ≤ a' d) (N : ℕ) :
    ledger c a N ≤ ledger c a' N :=
  sum_le_sum fun d _ => mul_le_mul_of_nonneg_right (h d) (by exact_mod_cast hP.nonneg _)

theorem conv_filter_le (hb : IsEvenFilter b) (n : ℕ) :
    conv b b n ≤ conv evenVonMangoldt evenVonMangoldt n :=
  sum_le_sum fun d _ => mul_le_mul (hb.le_even d) (hb.le_even _) (hb.nonneg _)
    (evenVonMangoldt_nonneg d)

/-- The ledger of `Λ` at `⌊N/e⌋` against the main term `L N/e`. -/
private lemma abs_ledger_div_sub_le (hP : IsProducer c m B) {N e : ℕ} (he : e ∈ Ioc 0 N) :
    |ledger c vonMangoldtWeight (N / e) - stencilSlope c * ((N : ℝ) / e)| ≤
      stencilSlope c + stencilErrorConst c * (1 + Real.log N) := by
  obtain ⟨he0, heN⟩ := mem_Ioc.mp he
  have hM : 1 ≤ N / e := (Nat.one_le_div_iff he0).mpr heN
  have hlog : ledger c vonMangoldtWeight (N / e) = Real.log (stencilInt c (N / e) : ℝ) := by
    rw [log_stencilInt_eq_vonMangoldt hP.zero hP.nonneg]
    rfl
  have h1 := abs_log_stencilInt_sub_slope_le hP.zero hP.balanced hP.nonneg hM
  rw [← hlog] at h1
  have hslope := stencilSlope_pos hP
  have hE := stencilErrorConst_nonneg c
  have he0R : (0 : ℝ) < e := by exact_mod_cast he0
  have hhi : ((N / e : ℕ) : ℝ) ≤ (N : ℝ) / e := Nat.cast_div_le
  have hlo : (N : ℝ) / e - 1 ≤ ((N / e : ℕ) : ℝ) := by
    have h2 : N < e * (N / e + 1) := Nat.lt_mul_div_succ N he0
    have h3 : (N : ℝ) < e * (((N / e : ℕ) : ℝ) + 1) := by exact_mod_cast h2
    have h4 : (N : ℝ) / e < ((N / e : ℕ) : ℝ) + 1 := by
      rw [div_lt_iff₀ he0R]
      linarith
    linarith
  have hlogN : Real.log ((N / e : ℕ) : ℝ) ≤ Real.log N :=
    Real.log_le_log (by exact_mod_cast hM) (by exact_mod_cast Nat.div_le_self N e)
  have hEl : stencilErrorConst c * (1 + Real.log ((N / e : ℕ) : ℝ)) ≤
      stencilErrorConst c * (1 + Real.log N) := mul_le_mul_of_nonneg_left (by linarith) hE
  have hs1 : stencilSlope c * ((N / e : ℕ) : ℝ) ≤ stencilSlope c * ((N : ℝ) / e) :=
    mul_le_mul_of_nonneg_left hhi hslope.le
  have hs2 : stencilSlope c * ((N : ℝ) / e - 1) ≤ stencilSlope c * ((N / e : ℕ) : ℝ) :=
    mul_le_mul_of_nonneg_left hlo hslope.le
  obtain ⟨h5, h6⟩ := abs_le.mp h1
  rw [abs_le]
  constructor <;> linarith

/-- **The cross term is the harmonic mass.** -/
theorem abs_ledger_conv_sub_le (hP : IsProducer c m B) (hb : IsEvenFilter b) (N : ℕ) :
    |ledger c (conv vonMangoldtWeight b) N - stencilSlope c * N * harmonicMass b N| ≤
      (stencilSlope c + stencilErrorConst c * (1 + Real.log N)) *
        ((Real.log 4 + 4) * (Nat.sqrt N : ℝ)) := by
  have hslope := stencilSlope_pos hP
  have hE := stencilErrorConst_nonneg c
  have hlogN : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hK : 0 ≤ stencilSlope c + stencilErrorConst c * (1 + Real.log N) := by positivity
  have hmain : stencilSlope c * N * harmonicMass b N =
      ∑ e ∈ Ioc 0 N, b e * (stencilSlope c * ((N : ℝ) / e)) := by
    rw [harmonicMass, mul_sum]
    exact sum_congr rfl fun e _ => by ring
  rw [ledger_conv, hmain, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ e ∈ Ioc 0 N, |b e * ledger c vonMangoldtWeight (N / e) -
      b e * (stencilSlope c * ((N : ℝ) / e))| ≤
      b e * (stencilSlope c + stencilErrorConst c * (1 + Real.log N)) := by
    intro e he
    rw [← mul_sub, abs_mul, abs_of_nonneg (hb.nonneg e)]
    exact mul_le_mul_of_nonneg_left (abs_ledger_div_sub_le hP he) (hb.nonneg e)
  refine (sum_le_sum hterm).trans ?_
  rw [← sum_mul, mul_comm]
  exact mul_le_mul_of_nonneg_left (hb.sum_le N) hK

/-- Selberg's weight of a filtered twin, expanded. -/
theorem selbergWeight_filteredTwin (b : ℕ → ℝ) (n : ℕ) :
    selbergWeight (filteredTwin b) n = selbergWeight vonMangoldtWeight n +
      ((-2) * (b n * Real.log n) + ((-4) * conv vonMangoldtWeight b n + 4 * conv b b n)) := by
  have htw : filteredTwin b = fun d => vonMangoldtWeight d + (-2) * b d := by
    funext d
    rw [filteredTwin]
    ring
  have hright : ∀ a : ℕ → ℝ, conv a (filteredTwin b) n = conv a vonMangoldtWeight n +
      (-2) * conv a b n := by
    intro a
    rw [conv_comm, htw, conv_add_left, conv_smul_left, conv_comm vonMangoldtWeight, conv_comm b]
  have hconv : conv (filteredTwin b) (filteredTwin b) n =
      conv vonMangoldtWeight vonMangoldtWeight n +
        ((-4) * conv vonMangoldtWeight b n + 4 * conv b b n) := by
    rw [hright, htw, conv_add_left, conv_smul_left, conv_add_left, conv_smul_left,
      conv_comm b vonMangoldtWeight]
    ring
  rw [selbergWeight, selbergWeight, hconv, filteredTwin]
  ring

/-- The scales `⌊√N⌋`, `⌊√⌊√N⌋⌋`, `log N` against `x = √√N`. -/
private lemma sqrt_scales {N : ℕ} (hN : 1 ≤ N) :
    1 ≤ Real.sqrt (Real.sqrt N) ∧ (Nat.sqrt N : ℝ) ≤ Real.sqrt (Real.sqrt N) ^ 2 ∧
      (Nat.sqrt (Nat.sqrt N) : ℝ) ≤ Real.sqrt (Real.sqrt N) ∧
        Real.log N ≤ 4 * Real.sqrt (Real.sqrt N) := by
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hx0 : 0 ≤ Real.sqrt (Real.sqrt N) := Real.sqrt_nonneg _
  have hxsq : Real.sqrt (Real.sqrt N) ^ 2 = Real.sqrt N := Real.sq_sqrt (Real.sqrt_nonneg _)
  have hxN : Real.sqrt (Real.sqrt N) ^ 4 = (N : ℝ) := by
    have h1 : Real.sqrt (Real.sqrt N) ^ 4 = (Real.sqrt (Real.sqrt N) ^ 2) ^ 2 := by ring
    rw [h1, hxsq, Real.sq_sqrt hN0]
  refine ⟨Real.one_le_sqrt.mpr (Real.one_le_sqrt.mpr hN1), ?_, ?_, ?_⟩
  · rw [hxsq]
    exact Real.nat_sqrt_le_real_sqrt
  · exact Real.nat_sqrt_le_real_sqrt.trans (Real.sqrt_le_sqrt Real.nat_sqrt_le_real_sqrt)
  · have hlog := Real.log_le_self hx0
    have hval : Real.log N = 4 * Real.log (Real.sqrt (Real.sqrt N)) := by
      conv_lhs => rw [← hxN, Real.log_pow]
      norm_num
    linarith

/-- The arithmetic of the three pieces of the gap, in the variable `x = √√N`. -/
private lemma gap_arith {L E W C x lg s t Lb Bb Y : ℝ} (hL : 0 ≤ L) (hE : 0 ≤ E) (hW : 0 ≤ W) (hC : 0 ≤ C)
    (hx1 : 1 ≤ x) (hs0 : 0 ≤ s) (hs : s ≤ x ^ 2) (ht : t ≤ x) (hlg : lg ≤ 4 * x) (hY : |Y| ≤ (L + E * (1 + lg)) * (C * s)) (hLb0 : 0 ≤ Lb)
    (hLb1 : Lb ≤ W * (lg * (C * s))) (hBb0 : 0 ≤ Bb) (hBb1 : Bb ≤ 2 * W * C ^ 2 * t * s) :
    |2 * Lb + 4 * Y - 4 * Bb| ≤ (4 * (L + 5 * E) * C + 8 * W * C + 8 * W * C ^ 2) * x ^ 3 := by
  have hx0 : 0 ≤ x := by linarith
  have hCs : C * s ≤ C * x ^ 2 := mul_le_mul_of_nonneg_left hs hC
  have hlinear : L + E * (1 + lg) ≤ (L + 5 * E) * x := by
    have h1 : L ≤ L * x := le_mul_of_one_le_right hL hx1
    have h2 : E * (1 + lg) ≤ E * (5 * x) := mul_le_mul_of_nonneg_left (by linarith) hE
    have h3 : (L + 5 * E) * x = L * x + E * (5 * x) := by ring
    linarith
  have hA : (L + E * (1 + lg)) * (C * s) ≤ (L + 5 * E) * C * x ^ 3 := by
    calc _ ≤ ((L + 5 * E) * x) * (C * x ^ 2) :=
          mul_le_mul hlinear hCs (mul_nonneg hC hs0) (by positivity)
      _ = _ := by ring
  have hB : W * (lg * (C * s)) ≤ 4 * W * C * x ^ 3 := by
    have h2 : lg * (C * s) ≤ (4 * x) * (C * x ^ 2) :=
      mul_le_mul hlg hCs (mul_nonneg hC hs0) (by positivity)
    calc _ ≤ W * ((4 * x) * (C * x ^ 2)) := mul_le_mul_of_nonneg_left h2 hW
      _ = _ := by ring
  have hD : 2 * W * C ^ 2 * t * s ≤ 2 * W * C ^ 2 * x ^ 3 := by
    have h1 : t * s ≤ x * x ^ 2 := mul_le_mul ht hs hs0 hx0
    calc _ = 2 * W * C ^ 2 * (t * s) := by ring
      _ ≤ 2 * W * C ^ 2 * (x * x ^ 2) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = _ := by ring
  have hval : (4 * (L + 5 * E) * C + 8 * W * C + 8 * W * C ^ 2) * x ^ 3 =
      4 * ((L + 5 * E) * C * x ^ 3) + 2 * (4 * W * C * x ^ 3) + 4 * (2 * W * C ^ 2 * x ^ 3) := by ring
  have hp1 : 0 ≤ 4 * W * C * x ^ 3 := by positivity
  have hp2 : 0 ≤ 2 * W * C ^ 2 * x ^ 3 := by positivity
  obtain ⟨hc1, hc2⟩ := abs_le.mp hY
  rw [hval, abs_le]
  constructor <;> linarith

/-- **The quadratic gap is the harmonic mass.** Uniformly in the filter, the Selberg reading of a filtered twin leaves that
of `Λ` by `4 L N Σ_{e ≤ N} b(e)/e`, up to `O(N^{3/4})`. -/
theorem exists_abs_selberg_gap_sub_le (hP : IsProducer c m B) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ b : ℕ → ℝ, IsEvenFilter b → ∀ N : ℕ, 1 ≤ N →
      |ledger c (selbergWeight vonMangoldtWeight) N - ledger c (selbergWeight (filteredTwin b)) N -
          4 * stencilSlope c * N * harmonicMass b N| ≤ M * Real.sqrt (Real.sqrt N) ^ 3 := by
  have hL : 0 ≤ stencilSlope c := (stencilSlope_pos hP).le
  have hE : 0 ≤ stencilErrorConst c := stencilErrorConst_nonneg c
  have hW : (0 : ℝ) ≤ ((peak c : ℤ) : ℝ) := by
    have h1 := hP.nonneg 0
    have h2 := hP.stepWeight_le_peak 0
    exact_mod_cast h1.trans h2
  have hC : (0 : ℝ) ≤ Real.log 4 + 4 := by
    have := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)
    linarith
  refine ⟨4 * (stencilSlope c + 5 * stencilErrorConst c) * (Real.log 4 + 4) +
    8 * ((peak c : ℤ) : ℝ) * (Real.log 4 + 4) + 8 * ((peak c : ℤ) : ℝ) * (Real.log 4 + 4) ^ 2,
    by positivity, fun b hb N hN => ?_⟩
  obtain ⟨hx1, hs, ht, hlogN⟩ := sqrt_scales hN
  have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hLbnn : ∀ n : ℕ, 0 ≤ b n * Real.log n := fun n =>
    mul_nonneg (hb.nonneg n) (Real.log_natCast_nonneg n)
  have hexpand : ledger c (selbergWeight (filteredTwin b)) N =
      ledger c (selbergWeight vonMangoldtWeight) N +
        ((-2) * ledger c (fun n => b n * Real.log n) N +
          ((-4) * ledger c (conv vonMangoldtWeight b) N + 4 * ledger c (conv b b) N)) := by
    have hfun : ledger c (selbergWeight (filteredTwin b)) N = ledger c (fun n =>
        selbergWeight vonMangoldtWeight n + ((-2) * (b n * Real.log n) +
          ((-4) * conv vonMangoldtWeight b n + 4 * conv b b n))) N := by
      simp only [ledger, selbergWeight_filteredTwin]
    rw [hfun, ledger_add, ledger_add, ledger_smul, ledger_add, ledger_smul, ledger_smul]
  have hLb1 : ledger c (fun n => b n * Real.log n) N ≤
      ((peak c : ℤ) : ℝ) * (Real.log N * ((Real.log 4 + 4) * (Nat.sqrt N : ℝ))) := by
    refine (ledger_le hP hLbnn N).trans (mul_le_mul_of_nonneg_left ?_ hW)
    have h1 : ∑ d ∈ Ioc 0 N, b d * Real.log d ≤ ∑ d ∈ Ioc 0 N, b d * Real.log N := by
      refine sum_le_sum fun d hd => mul_le_mul_of_nonneg_left ?_ (hb.nonneg d)
      obtain ⟨hd0, hdN⟩ := mem_Ioc.mp hd
      exact Real.log_le_log (by exact_mod_cast hd0) (by exact_mod_cast hdN)
    refine h1.trans ?_
    rw [← sum_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hb.sum_le N) hlog0
  have hconvnn : ∀ n, 0 ≤ conv b b n := fun n =>
    sum_nonneg fun d _ => mul_nonneg (hb.nonneg d) (hb.nonneg _)
  have hgap : ledger c (selbergWeight vonMangoldtWeight) N - ledger c (selbergWeight (filteredTwin b)) N -
      4 * stencilSlope c * N * harmonicMass b N =
      2 * ledger c (fun n => b n * Real.log n) N +
        4 * (ledger c (conv vonMangoldtWeight b) N - stencilSlope c * N * harmonicMass b N) -
          4 * ledger c (conv b b) N := by
    rw [hexpand]
    ring
  rw [hgap]
  exact gap_arith hL hE hW hC hx1 (Nat.cast_nonneg _) hs ht hlogN
    (abs_ledger_conv_sub_le hP hb N) (ledger_nonneg hP hLbnn N) hLb1 (ledger_nonneg hP hconvnn N)
    ((ledger_mono hP (conv_filter_le hb) N).trans (ledger_conv_even_le hP N))

/-- **The asymptotic of the gap.** If the harmonic mass of a filter converges, the gap per unit of `N` converges to `4 L`
times the limit. -/
theorem tendsto_selberg_gap_of_tendsto_mass (hP : IsProducer c m B) (hb : IsEvenFilter b) {κ : ℝ}
    (hκ : Tendsto (harmonicMass b) atTop (𝓝 κ)) :
    Tendsto (fun N : ℕ => (ledger c (selbergWeight vonMangoldtWeight) N -
        ledger c (selbergWeight (filteredTwin b)) N) / N) atTop
      (𝓝 (4 * stencilSlope c * κ)) := by
  obtain ⟨M, hM0, hM⟩ := exists_abs_selberg_gap_sub_le hP
  have hx : Tendsto (fun N : ℕ => Real.sqrt (Real.sqrt (N : ℝ))) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  have hdecay : Tendsto (fun N : ℕ => M / Real.sqrt (Real.sqrt (N : ℝ))) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hx
  have herr : Tendsto (fun N : ℕ => (ledger c (selbergWeight vonMangoldtWeight) N -
      ledger c (selbergWeight (filteredTwin b)) N - 4 * stencilSlope c * N * harmonicMass b N) / N)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm' ?_ hdecay
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    set x : ℝ := Real.sqrt (Real.sqrt N) with hxdef
    have hxpos : 0 < x := Real.sqrt_pos.mpr (Real.sqrt_pos.mpr hN0)
    have hxsq : x ^ 2 = Real.sqrt N := Real.sq_sqrt (Real.sqrt_nonneg _)
    have hxN : x ^ 4 = (N : ℝ) := by
      have h1 : x ^ 4 = (x ^ 2) ^ 2 := by ring
      rw [h1, hxsq, Real.sq_sqrt hN0.le]
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hN0, div_le_iff₀ hN0]
    have hbound := hM b hb N hN
    rw [← hxdef] at hbound
    refine hbound.trans (le_of_eq ?_)
    rw [← hxN, div_mul_eq_mul_div, eq_div_iff hxpos.ne']
    ring
  have hmain := (herr.add (hκ.const_mul (4 * stencilSlope c)))
  rw [zero_add] at hmain
  refine hmain.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
  field_simp
  ring

/-! ### The Liouville twin -/

/-- The even part of `Λ` is an admissible filter. -/
theorem isEvenFilter_even : IsEvenFilter evenVonMangoldt := ⟨evenVonMangoldt_nonneg, fun _ => le_rfl⟩

theorem filteredTwin_even : filteredTwin evenVonMangoldt = twinWeight := by
  funext n
  rw [filteredTwin, twinWeight_eq]

/-- `Σ_{e ≤ N} Λ(e) 1_{Ω(e) even} / e = Σ_{j ≤ √N} Λ(j)/j²`. -/
theorem harmonicMass_even (N : ℕ) :
    harmonicMass evenVonMangoldt N = ∑ j ∈ Ioc 0 (Nat.sqrt N), vonMangoldt j / (j : ℝ) ^ 2 := by
  rw [harmonicMass]
  symm
  refine sum_bij_ne_zero (fun j _ _ => j ^ 2) ?_ ?_ ?_ ?_
  · intro j hj _
    obtain ⟨h1, h2⟩ := mem_Ioc.mp hj
    exact mem_Ioc.mpr ⟨by positivity, Nat.le_sqrt'.mp h2⟩
  · intro a _ _ b _ _ h
    exact Nat.pow_left_injective (by norm_num) h
  · intro n hn hne
    have heq : evenVonMangoldt n ≠ 0 := fun h => hne (by rw [h, zero_div])
    have hΛ : vonMangoldt n ≠ 0 := by
      intro h0
      apply heq
      simp [evenVonMangoldt, h0]
    have heven : Even (cardFactors n) := by
      by_contra h
      apply heq
      simp [evenVonMangoldt, h]
    obtain ⟨p, k, hp, hk, rfl⟩ := isPrimePow_nat_iff _ |>.mp
      (not_not.mp (mt ArithmeticFunction.vonMangoldt_eq_zero_iff.mpr hΛ))
    rw [ArithmeticFunction.cardFactors_apply_prime_pow hp] at heven
    obtain ⟨i, rfl⟩ := heven
    have hi : 0 < i := by omega
    have hp0 : p ^ i ≠ 0 := pow_ne_zero _ hp.ne_zero
    have hsq : (p ^ i) ^ 2 = p ^ (i + i) := by rw [← pow_mul, mul_two]
    have hval : vonMangoldt (p ^ i) ≠ 0 := by
      rw [ArithmeticFunction.vonMangoldt_apply_pow hi.ne', ArithmeticFunction.vonMangoldt_apply_prime hp]
      exact (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
    refine ⟨p ^ i, mem_Ioc.mpr ⟨Nat.pos_of_ne_zero hp0, Nat.le_sqrt'.mpr ?_⟩, ?_, hsq⟩
    · rw [hsq]
      exact (mem_Ioc.mp hn).2
    · exact div_ne_zero hval (by exact_mod_cast pow_ne_zero 2 hp0)
  · intro j hj _
    have hj0 : j ≠ 0 := by
      have := (mem_Ioc.mp hj).1
      omega
    have heven : Even (cardFactors (j ^ 2)) := by
      rw [sq, ArithmeticFunction.cardFactors_mul hj0 hj0]
      exact ⟨_, rfl⟩
    rw [evenVonMangoldt, if_pos heven, ArithmeticFunction.vonMangoldt_apply_pow two_ne_zero]
    push_cast
    rfl

/-- The prime-square constant `κ = Σ_j Λ(j)/j²`. -/
def primeSquareMass : ℝ := ∑' j : ℕ, vonMangoldt j / (j : ℝ) ^ 2

theorem term_vonMangoldt_two (j : ℕ) :
    LSeries.term (fun n => ((vonMangoldt n : ℝ) : ℂ)) 2 j = ((vonMangoldt j / (j : ℝ) ^ 2 : ℝ) : ℂ) := by
  rcases eq_or_ne j 0 with rfl | hj
  · simp
  · rw [LSeries.term_of_ne_zero hj]
    push_cast
    norm_cast

theorem summable_vonMangoldt_div_sq : Summable fun j : ℕ => vonMangoldt j / (j : ℝ) ^ 2 := by
  have h := ArithmeticFunction.LSeriesSummable_vonMangoldt (s := 2) (by norm_num)
  have h2 : Summable fun j : ℕ => ((vonMangoldt j / (j : ℝ) ^ 2 : ℝ) : ℂ) := by
    exact h.congr fun j => term_vonMangoldt_two j
  exact Complex.summable_ofReal.mp h2

/-- **The constant is a value of the logarithmic derivative:** `κ = −ζ′(2)/ζ(2)`. -/
theorem ofReal_primeSquareMass : (primeSquareMass : ℂ) = -deriv riemannZeta 2 / riemannZeta 2 := by
  rw [← ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div (s := 2) (by norm_num),
    primeSquareMass, Complex.ofReal_tsum, LSeries]
  exact tsum_congr fun j => (term_vonMangoldt_two j).symm

private lemma sum_Ioc_eq_sum_range {f : ℕ → ℝ} (hf : f 0 = 0) (s : ℕ) :
    ∑ j ∈ Ioc 0 s, f j = ∑ j ∈ range (s + 1), f j := by
  refine sum_subset (fun j hj => ?_) fun j hj hj' => ?_
  · have := (mem_Ioc.mp hj).2
    exact mem_range.mpr (by omega)
  · have h0 : j = 0 := by
      by_contra h0
      have := mem_range.mp hj
      exact hj' (mem_Ioc.mpr ⟨Nat.pos_of_ne_zero h0, by omega⟩)
    rw [h0, hf]

private lemma tendsto_sqrt_nat : Tendsto Nat.sqrt atTop atTop :=
  tendsto_atTop_atTop.mpr fun b => ⟨b ^ 2, fun _ ha => Nat.le_sqrt'.mpr ha⟩

/-- The harmonic mass of the even part converges to `κ`. -/
theorem tendsto_harmonicMass_even : Tendsto (harmonicMass evenVonMangoldt) atTop (𝓝 primeSquareMass) := by
  have h := summable_vonMangoldt_div_sq.hasSum.tendsto_sum_nat
  have h2 := h.comp ((tendsto_add_atTop_nat 1).comp tendsto_sqrt_nat)
  refine h2.congr fun N => ?_
  rw [harmonicMass_even, sum_Ioc_eq_sum_range (by simp)]
  rfl

/-- **The exact constant of the twin gap.** The Selberg reading of the Liouville twin leaves the exact value at rate
`4 L κ`, with `κ = −ζ′(2)/ζ(2)`. -/
theorem tendsto_selberg_twin_gap (hP : IsProducer c m B) :
    Tendsto (fun N : ℕ => (ledger c (selbergWeight vonMangoldtWeight) N -
        ledger c (selbergWeight twinWeight) N) / N) atTop
      (𝓝 (4 * stencilSlope c * primeSquareMass)) := by
  have h := tendsto_selberg_gap_of_tendsto_mass hP isEvenFilter_even tendsto_harmonicMass_even
  rwa [filteredTwin_even] at h

/-! ### Twins that agree up to a level -/

/-- The even part of `Λ` above the level `y`: the twin that agrees with `Λ` up to `y`. -/
def levelFilter (y n : ℕ) : ℝ := if y < n then evenVonMangoldt n else 0

theorem isEvenFilter_level (y : ℕ) : IsEvenFilter (levelFilter y) := by
  refine ⟨fun n => ?_, fun n => ?_⟩
  · unfold levelFilter
    split_ifs
    · exact evenVonMangoldt_nonneg n
    · exact le_rfl
  · unfold levelFilter
    split_ifs
    · exact le_rfl
    · exact evenVonMangoldt_nonneg n

/-- The filtered twin agrees with `Λ` up to the level. -/
theorem filteredTwin_level_of_le {y n : ℕ} (hn : n ≤ y) :
    filteredTwin (levelFilter y) n = vonMangoldtWeight n := by
  rw [filteredTwin, levelFilter, if_neg (not_lt.mpr hn), mul_zero, sub_zero]

/-- The mass above the level. -/
theorem harmonicMass_level {y N : ℕ} (h : y ≤ N) :
    harmonicMass (levelFilter y) N = harmonicMass evenVonMangoldt N - harmonicMass evenVonMangoldt y := by
  rw [harmonicMass, harmonicMass, harmonicMass, ← sum_Ioc_consecutive _ (Nat.zero_le y) h,
    ← sum_Ioc_consecutive _ (Nat.zero_le y) h]
  have h1 : ∑ e ∈ Ioc 0 y, levelFilter y e / e = 0 := by
    refine sum_eq_zero fun e he => ?_
    rw [levelFilter, if_neg (not_lt.mpr (mem_Ioc.mp he).2), zero_div]
  have h2 : ∑ e ∈ Ioc y N, levelFilter y e / e = ∑ e ∈ Ioc y N, evenVonMangoldt e / e :=
    sum_congr rfl fun e he => by rw [levelFilter, if_pos (mem_Ioc.mp he).1]
  rw [h1, h2]
  ring

/-- The separation constant of the twin agreeing with `Λ` up to `y`. -/
def levelConstant (y : ℕ) : ℝ := primeSquareMass - harmonicMass evenVonMangoldt y

theorem tendsto_harmonicMass_level (y : ℕ) :
    Tendsto (harmonicMass (levelFilter y)) atTop (𝓝 (levelConstant y)) := by
  refine (tendsto_harmonicMass_even.sub_const _).congr' ?_
  filter_upwards [eventually_ge_atTop y] with N hN
  rw [harmonicMass_level hN]

/-- **Every level is seen at scale `N`.** -/
theorem tendsto_selberg_level_gap (hP : IsProducer c m B) (y : ℕ) :
    Tendsto (fun N : ℕ => (ledger c (selbergWeight vonMangoldtWeight) N -
        ledger c (selbergWeight (filteredTwin (levelFilter y))) N) / N) atTop
      (𝓝 (4 * stencilSlope c * levelConstant y)) :=
  tendsto_selberg_gap_of_tendsto_mass hP (isEvenFilter_level y) (tendsto_harmonicMass_level y)

theorem monotone_harmonicMass_even : Monotone (harmonicMass evenVonMangoldt) := by
  refine monotone_nat_of_le_succ fun N => ?_
  rw [harmonicMass, harmonicMass, ← Finset.insert_Ioc_right_eq_Ioc_add_one (Nat.zero_le N),
    sum_insert (by simp)]
  have : 0 ≤ evenVonMangoldt (N + 1) / ((N + 1 : ℕ) : ℝ) :=
    div_nonneg (evenVonMangoldt_nonneg _) (Nat.cast_nonneg _)
  linarith

/-- **The separation constant is positive at every level.** -/
theorem levelConstant_pos (y : ℕ) : 0 < levelConstant y := by
  obtain ⟨p, hpy, hp⟩ := Nat.exists_infinite_primes (y + 2)
  have hp2 : y < p ^ 2 := by nlinarith
  have hsplit := harmonicMass_level hp2.le
  have hle : harmonicMass evenVonMangoldt (p ^ 2) ≤ primeSquareMass :=
    monotone_harmonicMass_even.ge_of_tendsto tendsto_harmonicMass_even _
  have hheven : Even (cardFactors (p ^ 2)) := by
    rw [ArithmeticFunction.cardFactors_apply_prime_pow hp]
    decide
  have hval : evenVonMangoldt (p ^ 2) = Real.log p := by
    rw [evenVonMangoldt, if_pos hheven, ArithmeticFunction.vonMangoldt_apply_pow two_ne_zero,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have hlogp : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hpos : 0 < harmonicMass (levelFilter y) (p ^ 2) := by
    rw [harmonicMass]
    have hmem : p ^ 2 ∈ Ioc 0 (p ^ 2) := mem_Ioc.mpr ⟨by have := hp.pos; positivity, le_rfl⟩
    have hnn : ∀ e ∈ Ioc 0 (p ^ 2), 0 ≤ levelFilter y e / e := fun e _ =>
      div_nonneg ((isEvenFilter_level y).nonneg e) (Nat.cast_nonneg e)
    refine lt_of_lt_of_le ?_ (single_le_sum hnn hmem)
    rw [levelFilter, if_pos hp2, hval]
    have hp0 : (0 : ℝ) < ((p ^ 2 : ℕ) : ℝ) := by
      have := hp.pos
      positivity
    exact div_pos hlogp hp0
  rw [levelConstant]
  rw [hsplit] at hpos
  linarith

/-- **The separation constant dies with the level.** -/
theorem tendsto_levelConstant : Tendsto levelConstant atTop (𝓝 0) := by
  have h := tendsto_harmonicMass_even.const_sub primeSquareMass
  rwa [sub_self] at h

end GaloisForLFunctions.RigidArithmeticOfCuts
