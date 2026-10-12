import GaloisForLFunctions.RHTower.JointAncestryPrimeCosineKernel
import GaloisForLFunctions.RHTower.PrimeLagLandauPrimesOnly

/-!
# Single-prime JAS tests: quasi-RH below dressing `½`, RH at dressing `0`

A single-prime test is a Bernoulli product test on one prime `p`.  Its value is
`Re Σ_ρ (1 + z p^{−(ρ+c)} + z̄ p^{−(1−ρ+c)} + |z|²)/(ρ(1−ρ)) = (1 + |z|²) Φ(0) + 2 Re z · p^{−σ} Φ(log p)`
with `c = σ − ½` and `Φ` the lag function (`re_jasSinglePrimeAggregate`).  So positivity of all
single-prime tests on primes `p > X` at level `σ` says exactly `|Φ(log p)| ≤ Φ(0) p^σ` for every prime
`p > X` (`jasSinglePrimePositiveAbove_iff`).

* **Dressing below `½` is quasi-RH** (`exists_xiZeroHalfPlaneBound_iff_exists_jasSinglePrimePositiveAbove`).
  Some half-plane bound `Re ρ ≤ ½ + α`, `α < ½`, holds iff the single-prime tests on the primes
  `p > X` are positive at some level `σ < ½`, for some `X`.  One direction: between consecutive large
  primes the gap is at most `p^{71/100}`, and the lag function moves by `O(p^{23/100})` over such a
  gap.  So `Φ(log p) ≤ M p^σ` on large primes gives `Φ(L) ≤ M' e^{max(σ, ¼) L}` on `L ≥ 0`, and the
  growth criterion bounds every zero by `½ + max(σ, ¼)`.  The other direction: a half-plane bound
  `α` gives `|Φ(L)| ≤ e^{αL} Σ_ρ |w_ρ|`.
* **Dressing `½` is unconditional** (`exists_jasSinglePrimePositiveAbove_half`).  Every zero has
  `Re ρ < 1`, so `p^{−½} Φ(log p) → 0` by dominated convergence.  The single-prime abscissa therefore
  lies in `[0, ½]`.  It is below `½` exactly under quasi-RH, and it is `0` exactly under RH.
* **Dressing `0` is RH** (`riemannHypothesis_iff_exists_jasSinglePrimePositiveAbove_zero`).  At
  `σ = 0` the single-prime tests on large primes bound the prime lags, and the prime-lag criterion
  gives RH.
* **A JAS-internal capstone** (`riemannHypothesis_iff_exists_jasSinglePrime_and_jasProductPositiveAbove`,
  `riemannHypothesis_iff_exists_jasSinglePrime_and_jasCosinePositiveAbove`).  RH holds iff, for some
  `X`, the single-prime tests on primes `> X` are positive at some level `σ < ½` and the product
  tests (equivalently, the cosine tests) on primes `> X` are positive at `σ = 1`.  The half-plane
  hypothesis of the large-prime capstone is itself a JAS positivity statement.
* **Cosine form at every level** (`riemannHypothesis_iff_exists_jasCosinePositiveAbove_lt_half`,
  `riemannHypothesis_iff_exists_jasCosinePositiveAbove_zero`).  RH holds iff the cosine tests on
  large primes are positive at some level `σ < ½`.  At `σ = 0` the kernel is
  `K_P(s) = ∏_p 2 cosh²((s − ½) log p / 2)` (`jasCosineKernel_zero`).
* **One condition below `½`** (`JasProductPositiveAbove.mono_level`,
  `riemannHypothesis_iff_exists_jasProductPositiveAbove_lt_half`).  Product-test positivity is
  monotone in the dressing level: a factor at level `σ'` is a factor at level `σ` evaluated at
  `p^{−(σ'−σ)} z`, plus the constant `|z|²(1 − p^{−2(σ'−σ)}) ≥ 0`.  Hence RH holds iff the product
  tests on the primes `p > X` are positive at some level `σ < ½`, for some `X`.
-/

open Complex Filter Topology
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-! ## The single-prime aggregate -/

theorem jasHoloA_dressed_eq_exp (q : ℂ) (σ : ℝ) (p : Nat.Primes) :
    jasHoloA (q + ((σ - 1 / 2 : ℝ) : ℂ)) p =
      (Real.exp (-σ * Real.log p) : ℂ) * cexp (((-Real.log p : ℝ) : ℂ) * (q - 1 / 2)) := by
  rw [jasHoloA, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem jasHoloB_dressed_eq_exp (q : ℂ) (σ : ℝ) (p : Nat.Primes) :
    jasHoloB (q - ((σ - 1 / 2 : ℝ) : ℂ)) p =
      (Real.exp (-σ * Real.log p) : ℂ) * cexp (((Real.log p : ℝ) : ℂ) * (q - 1 / 2)) := by
  rw [jasHoloB, Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- **The single-prime aggregate.**
`Σ_ρ (1 + zA + z̄B + |z|²)/(ρ(1−ρ)) = (1 + |z|²) Φ(0) + (z + z̄) p^{−σ} Φ(log p)`. -/
theorem jasSinglePrimeAggregate_eq (σ : ℝ) (p : Nat.Primes) (z : ℂ) :
    ∑' q : XiZeroCopy, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) z / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) =
      (1 + z * conj z) * weilLagFunction 0 +
        (z + conj z) * ((Real.exp (-σ * Real.log p) : ℂ) * weilLagFunction (Real.log p)) := by
  set E : ℂ := (Real.exp (-σ * Real.log p) : ℂ) with hE
  set T : ℝ → XiZeroCopy → ℂ := fun L q =>
    cexp ((L : ℂ) * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) with hT
  have hterm : ∀ q : XiZeroCopy,
      jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) z / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) =
      ((1 + z * conj z) * T 0 q + z * E * T (-Real.log p) q) + conj z * E * T (Real.log p) q := by
    intro q
    rw [jasBernoulliFactor, jasHoloA_dressed_eq_exp, jasHoloB_dressed_eq_exp, hT]
    simp only [Complex.ofReal_zero, zero_mul, Complex.exp_zero]
    ring
  have hs0 : Summable fun q => (1 + z * conj z) * T 0 q := (summable_weilLagTerm 0).mul_left _
  have hs1 : Summable fun q => z * E * T (-Real.log p) q :=
    (summable_weilLagTerm (-Real.log p)).mul_left _
  have hs2 : Summable fun q => conj z * E * T (Real.log p) q :=
    (summable_weilLagTerm (Real.log p)).mul_left _
  rw [tsum_congr hterm, Summable.tsum_add (hs0.add hs1) hs2, Summable.tsum_add hs0 hs1, tsum_mul_left,
    tsum_mul_left, tsum_mul_left]
  have hW : ∀ L : ℝ, ∑' q, T L q = weilLagFunction L := fun L => rfl
  rw [hW, hW, hW, weilLagFunction_neg]
  ring

/-- The real part of the single-prime aggregate. -/
theorem re_jasSinglePrimeAggregate (σ : ℝ) (p : Nat.Primes) (z : ℂ) :
    (∑' q : XiZeroCopy, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) z / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re =
      (1 + ‖z‖ ^ 2) * poleSharpConstant +
        2 * z.re * (Real.exp (-σ * Real.log p) * weilLagFunctionReal (Real.log p)) := by
  rw [jasSinglePrimeAggregate_eq, weilLagFunction_zero, weilLagFunction_eq_ofReal,
    Complex.mul_conj, Complex.add_conj, Complex.normSq_eq_norm_sq]
  have e : ((1 : ℂ) + ((‖z‖ ^ 2 : ℝ) : ℂ)) * (poleSharpConstant : ℂ) + ((2 * z.re : ℝ) : ℂ) *
      ((Real.exp (-σ * Real.log p) : ℂ) * (weilLagFunctionReal (Real.log p) : ℂ)) =
      (((1 + ‖z‖ ^ 2) * poleSharpConstant + 2 * z.re *
        (Real.exp (-σ * Real.log p) * weilLagFunctionReal (Real.log p)) : ℝ) : ℂ) := by
    push_cast; ring
  rw [e, Complex.ofReal_re]

/-! ## Single-prime positivity -/

/-- Positivity of the single-prime Bernoulli tests on the primes `p > X` at level `σ`. -/
def JasSinglePrimePositiveAbove (X : ℕ) (σ : ℝ) : Prop :=
  ∀ p : Nat.Primes, X < (p : ℕ) → ∀ z : ℂ,
    0 ≤ (∑' q : XiZeroCopy, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
      (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) z / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re

/-- **Single-prime positivity is a bound on the prime lags**: `|Φ(log p)| ≤ Φ(0) p^σ`. -/
theorem jasSinglePrimePositiveAbove_iff {X : ℕ} {σ : ℝ} :
    JasSinglePrimePositiveAbove X σ ↔ ∀ p : Nat.Primes, X < (p : ℕ) →
      |weilLagFunctionReal (Real.log p)| ≤ poleSharpConstant * Real.exp (σ * Real.log p) := by
  have hA := poleSharpConstant_pos
  have hEE : ∀ p : Nat.Primes, Real.exp (-σ * Real.log p) * Real.exp (σ * Real.log p) = 1 :=
    fun p => by rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  constructor
  · intro h p hp
    have hm := h p hp (-1)
    have h1 := h p hp 1
    rw [re_jasSinglePrimeAggregate] at hm h1
    simp only [norm_neg, norm_one, Complex.neg_re, Complex.one_re] at hm h1
    have hE := Real.exp_pos (σ * Real.log p)
    set F := weilLagFunctionReal (Real.log p)
    have key : |Real.exp (-σ * Real.log p) * F| ≤ poleSharpConstant := by
      rw [abs_le]; constructor <;> nlinarith
    calc |F| = Real.exp (σ * Real.log p) * |Real.exp (-σ * Real.log p) * F| := by
          rw [abs_mul, abs_of_pos (Real.exp_pos _), ← mul_assoc, mul_comm (Real.exp _), hEE, one_mul]
      _ ≤ Real.exp (σ * Real.log p) * poleSharpConstant := by gcongr
      _ = poleSharpConstant * Real.exp (σ * Real.log p) := mul_comm _ _
  · intro h p hp z
    rw [re_jasSinglePrimeAggregate]
    set F := weilLagFunctionReal (Real.log p)
    have hF : |Real.exp (-σ * Real.log p) * F| ≤ poleSharpConstant := by
      have := h p hp
      rw [abs_mul, abs_of_pos (Real.exp_pos _)]
      calc Real.exp (-σ * Real.log p) * |F|
          ≤ Real.exp (-σ * Real.log p) * (poleSharpConstant * Real.exp (σ * Real.log p)) := by
            gcongr
        _ = poleSharpConstant := by rw [mul_comm poleSharpConstant, ← mul_assoc, hEE, one_mul]
    have hre : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm z) 2
    have hzF : -(|z.re| * poleSharpConstant) ≤ z.re * (Real.exp (-σ * Real.log p) * F) := by
      have := abs_mul z.re (Real.exp (-σ * Real.log p) * F)
      have h2 := neg_abs_le (z.re * (Real.exp (-σ * Real.log p) * F))
      nlinarith [abs_nonneg z.re]
    have hsq : 0 ≤ (1 - |z.re|) ^ 2 := sq_nonneg _
    have habs : |z.re| ^ 2 = z.re ^ 2 := sq_abs _
    nlinarith

theorem JasProductPositiveAbove.singlePrime {X : ℕ} {σ : ℝ} (h : JasProductPositiveAbove X σ) :
    JasSinglePrimePositiveAbove X σ := by
  intro p hp z
  have := h {p} (fun r hr => by rw [Finset.mem_singleton.mp hr]; exact hp) fun _ => z
  simpa only [Finset.prod_singleton] using this

theorem JasSinglePrimePositiveAbove.mono {X Y : ℕ} {σ : ℝ} (h : JasSinglePrimePositiveAbove X σ)
    (hXY : X ≤ Y) : JasSinglePrimePositiveAbove Y σ :=
  fun p hp => h p (lt_of_le_of_lt hXY hp)

/-! ## Dressing below `½`: growth from the prime lags -/

/-- If `Φ(log p) ≤ M p^a` for all primes `p > X` (`a ≥ 0`), then `Φ(L) ≤ M₃ e^{max(a, ¼) L}` for
`L ≥ 0`. -/
theorem exists_growth_bound_of_primeLag_le_rpow {X : ℕ} {M a : ℝ} (ha : 0 ≤ a)
    (hM : ∀ p : ℕ, p.Prime → X < p → integerLag p ≤ M * Real.exp (a * Real.log p)) :
    ∃ M₃ : ℝ, ∀ L : ℝ, 0 ≤ L →
      weilLagFunctionReal L ≤ M₃ * Real.exp (max a (1 / 4) * L) := by
  obtain ⟨X₀, hX₀4, hX₀⟩ := exists_prime_short_gap
  obtain ⟨X₁, hX₁⟩ : ∃ X₁ : ℝ, X₁ = max X₀ (2 * X + 4) := ⟨_, rfl⟩
  have hX₁0 : X₀ ≤ X₁ := hX₁ ▸ le_max_left _ _
  have hX₁X : 2 * (X : ℝ) + 4 ≤ X₁ := hX₁ ▸ le_max_right _ _
  obtain ⟨L₀, hL₀⟩ : ∃ L₀ : ℝ, L₀ = Real.log X₁ := ⟨_, rfl⟩
  have hL₀0 : 0 ≤ L₀ := by rw [hL₀]; exact Real.log_nonneg (by linarith)
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0:ℝ)) (b := L₀)).bddAbove_image
    continuous_weilLagFunctionReal.continuousOn
  set b := max a (1 / 4) with hb
  refine ⟨|M| + 457776 + max B 0, fun L hL => ?_⟩
  have hE : 1 ≤ Real.exp (b * L) := Real.one_le_exp (mul_nonneg (le_max_of_le_left ha) hL)
  rcases le_or_gt L L₀ with hLL₀ | hLL₀
  · have h1 : weilLagFunctionReal L ≤ B := hB ⟨L, ⟨hL, hLL₀⟩, rfl⟩
    have h3 : max B 0 ≤ max B 0 * Real.exp (b * L) := le_mul_of_one_le_right (le_max_right _ _) hE
    have h4 : 0 ≤ (|M| + 457776) * Real.exp (b * L) := by positivity
    nlinarith [le_max_left B 0]
  · obtain ⟨Y, hY⟩ : ∃ Y : ℝ, Y = Real.exp L := ⟨_, rfl⟩
    have hYX₁ : X₁ ≤ Y := by
      rw [hY, ← Real.exp_log (by linarith : (0:ℝ) < X₁), ← hL₀]
      exact Real.exp_le_exp.mpr hLL₀.le
    obtain ⟨p, hp, hpY, hgap⟩ := hX₀ Y (hX₁0.trans hYX₁)
    have hp2 : 2 ≤ p := hp.two_le
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (by omega : 1 ≤ p)
    have hp2' : (2 : ℝ) ≤ p := by exact_mod_cast hp2
    have hlogp : Real.log p ≤ L := by
      rw [← Real.log_exp L, ← hY]; exact Real.log_le_log hp0 hpY
    have hpow_le : (p : ℝ) ^ (71 / 100 : ℝ) ≤ p := Real.rpow_le_self_of_one_le hp1 (by norm_num)
    have hfl : Y - 1 < (⌊Y⌋₊ : ℝ) := Nat.sub_one_lt_floor Y
    have hpX : X < p := by
      have : (X : ℝ) < p := by linarith
      exact_mod_cast this
    have hm2p : ⌊Y⌋₊ ≤ 2 * p := by
      have h1 : (⌊Y⌋₊ : ℝ) < 2 * p := by linarith
      exact_mod_cast h1.le
    have hgapℕ : ((⌊Y⌋₊ - p : ℕ) : ℝ) ≤ (p : ℝ) ^ (71 / 100 : ℝ) := by
      have hpm : p ≤ ⌊Y⌋₊ := Nat.le_floor hpY
      rw [Nat.cast_sub hpm]
      linarith
    have hbound := abs_weilLagFunctionReal_sub_integerLag_le_of_gap hp2 hlogp (hY ▸ hm2p)
    have hfactor : 11 * ((⌊Real.exp L⌋₊ - p : ℕ) + 1) * (Real.log (2 * p) + 2) ^ 2 / Real.sqrt p
        ≤ 11 * ((p : ℝ) ^ (71 / 100 : ℝ) + 1) * (Real.log (2 * p) + 2) ^ 2 / Real.sqrt p := by
      rw [← hY]; gcongr
    have hgf := gap_factor_le hp2'
    have hpL : (p : ℝ) ^ (23 / 100 : ℝ) ≤ Real.exp (b * L) := by
      rw [Real.rpow_def_of_pos hp0, mul_comm]
      exact Real.exp_le_exp.mpr (by nlinarith [le_max_right a (1 / 4), Real.log_nonneg hp1])
    have hlag : integerLag p ≤ |M| * Real.exp (b * L) := by
      have h1 := hM p hp hpX
      have h2 : Real.exp (a * Real.log p) ≤ Real.exp (b * L) :=
        Real.exp_le_exp.mpr (by nlinarith [le_max_left a (1 / 4), Real.log_nonneg hp1])
      calc integerLag p ≤ M * Real.exp (a * Real.log p) := h1
        _ ≤ |M| * Real.exp (a * Real.log p) := by gcongr; exact le_abs_self M
        _ ≤ |M| * Real.exp (b * L) := by gcongr
    have h1 := (abs_le.mp hbound).2
    have hmax0 : 0 ≤ max B 0 * Real.exp (b * L) := by positivity
    calc weilLagFunctionReal L ≤ integerLag p + 11 * ((⌊Real.exp L⌋₊ - p : ℕ) + 1)
          * (Real.log (2 * p) + 2) ^ 2 / Real.sqrt p := by linarith
      _ ≤ |M| * Real.exp (b * L) + 457776 * Real.exp (b * L) := by linarith
      _ ≤ (|M| + 457776 + max B 0) * Real.exp (b * L) := by nlinarith

/-- **Single-prime positivity below `½` is a half-plane bound.**  If the single-prime tests on the
primes `p > X` are positive at a level `0 ≤ σ < ½`, every zero satisfies `Re ρ ≤ ½ + max(σ, ¼)`. -/
theorem xiZeroHalfPlaneBound_of_jasSinglePrimePositiveAbove {X : ℕ} {σ : ℝ} (hσ0 : 0 ≤ σ)
    (hσ : σ < 1 / 2) (h : JasSinglePrimePositiveAbove X σ) :
    XiZeroHalfPlaneBound (max σ (1 / 4)) := by
  have hb := jasSinglePrimePositiveAbove_iff.mp h
  obtain ⟨M₃, hM₃⟩ := exists_growth_bound_of_primeLag_le_rpow (X := X) (M := poleSharpConstant)
    hσ0 fun p hp hpX => (le_abs_self _).trans (hb ⟨p, hp⟩ hpX)
  intro ρ hρ
  obtain ⟨q, rfl⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ
  exact re_le_half_add_of_weilLagFunctionReal_le_exp (le_max_of_le_left hσ0)
    (max_lt hσ (by norm_num)) hM₃ q

/-- Under a half-plane bound `α ≥ 0`, `|Φ(L)| ≤ e^{αL} Σ_ρ |w_ρ|` for `L ≥ 0`. -/
theorem abs_weilLagFunctionReal_le_of_xiZeroHalfPlaneBound {alpha : ℝ}
    (hXi : XiZeroHalfPlaneBound alpha) {L : ℝ} (hL : 0 ≤ L) :
    |weilLagFunctionReal L| ≤ Real.exp (alpha * L) * jasLagAbsMass := by
  have hterm : ∀ q : XiZeroCopy, ‖cexp ((L : ℂ) * ((q.1 : ℂ) - 1 / 2)) /
      ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ ≤ Real.exp (alpha * L) * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ := by
    intro q
    rw [div_eq_mul_one_div, norm_mul, Complex.norm_exp]
    gcongr
    have hq := (abs_le.mp (abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi q)).2
    have hre : ((L : ℂ) * ((q.1 : ℂ) - 1 / 2)).re = L * (((q.1 : ℂ)).re - 1 / 2) := by
      simp [Complex.mul_re]
    rw [hre]
    nlinarith
  have hs : Summable fun q : XiZeroCopy => Real.exp (alpha * L) * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
    summable_inv_mul_one_sub.norm.mul_left _
  calc |weilLagFunctionReal L| ≤ ‖weilLagFunction L‖ := Complex.abs_re_le_norm _
    _ ≤ ∑' q : XiZeroCopy, ‖cexp ((L : ℂ) * ((q.1 : ℂ) - 1 / 2)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
        norm_tsum_le_tsum_norm ((summable_weilLagTerm L).norm)
    _ ≤ ∑' q : XiZeroCopy, Real.exp (alpha * L) * ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
        Summable.tsum_le_tsum hterm (summable_weilLagTerm L).norm hs
    _ = Real.exp (alpha * L) * jasLagAbsMass := by rw [tsum_mul_left]; rfl

/-- **A half-plane bound gives single-prime positivity at every larger level.**  If every zero
satisfies `Re ρ ≤ ½ + α` with `α < σ`, the single-prime tests on all sufficiently large primes
are positive at level `σ`. -/
theorem exists_jasSinglePrimePositiveAbove_of_xiZeroHalfPlaneBound_of_lt {alpha σ : ℝ}
    (hσa : alpha < σ) (hXi : XiZeroHalfPlaneBound alpha) :
    ∃ X : ℕ, JasSinglePrimePositiveAbove X σ := by
  have hσa' : 0 < σ - alpha := by linarith
  have hA := poleSharpConstant_pos
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp
    ((Real.tendsto_exp_atTop.comp (tendsto_id.const_mul_atTop hσa')).eventually_ge_atTop
      (jasLagAbsMass / poleSharpConstant))
  refine ⟨⌈Real.exp L₀⌉₊, jasSinglePrimePositiveAbove_iff.mpr fun p hp => ?_⟩
  have hpL : L₀ ≤ Real.log p := by
    have h1 : Real.exp L₀ ≤ (p : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast hp.le)
    rw [← Real.log_exp L₀]; exact Real.log_le_log (Real.exp_pos _) h1
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast p.2.one_lt.le)
  have h1 := abs_weilLagFunctionReal_le_of_xiZeroHalfPlaneBound hXi hlog0
  have h2 : jasLagAbsMass / poleSharpConstant ≤ Real.exp ((σ - alpha) * Real.log p) := by
    have := hL₀ (Real.log p) hpL
    simpa [Function.comp] using this
  have h3 : jasLagAbsMass ≤ poleSharpConstant * Real.exp ((σ - alpha) * Real.log p) := by
    rwa [div_le_iff₀ hA, mul_comm] at h2
  calc |weilLagFunctionReal (Real.log p)| ≤ Real.exp (alpha * Real.log p) * jasLagAbsMass := h1
    _ ≤ Real.exp (alpha * Real.log p) * (poleSharpConstant * Real.exp ((σ - alpha) * Real.log p)) := by
        gcongr
    _ = poleSharpConstant * Real.exp (σ * Real.log p) := by
        rw [mul_left_comm, ← Real.exp_add]; ring_nf

/-- **A half-plane bound below `½` gives single-prime positivity below `½`.** -/
theorem exists_jasSinglePrimePositiveAbove_of_xiZeroHalfPlaneBound {alpha : ℝ} (halpha : alpha < 1 / 2)
    (hXi : XiZeroHalfPlaneBound alpha) :
    ∃ X : ℕ, ∃ σ : ℝ, 0 ≤ σ ∧ σ < 1 / 2 ∧ JasSinglePrimePositiveAbove X σ := by
  set a := max alpha 0 with ha
  have hXa : XiZeroHalfPlaneBound a := fun ρ hρ => (hXi ρ hρ).trans (by linarith [le_max_left alpha 0])
  have ha0 : 0 ≤ a := le_max_right _ _
  have ha1 : a < 1 / 2 := max_lt halpha (by norm_num)
  obtain ⟨X, hX⟩ := exists_jasSinglePrimePositiveAbove_of_xiZeroHalfPlaneBound_of_lt
    (show a < (a + 1 / 2) / 2 by linarith) hXa
  exact ⟨X, (a + 1 / 2) / 2, by linarith, by linarith, hX⟩

/-- **The single-prime level is the half-plane level on `[¼, ½)`.**  For `¼ ≤ σ < ½`: single-prime
positivity at level `σ` on large primes gives the half-plane bound `σ`, and any half-plane bound
`α < σ` gives single-prime positivity at level `σ` on large primes. -/
theorem jasSinglePrime_level_eq_halfPlane_level {σ : ℝ} (hσ4 : 1 / 4 ≤ σ) (hσ : σ < 1 / 2) :
    ((∃ X : ℕ, JasSinglePrimePositiveAbove X σ) → XiZeroHalfPlaneBound σ) ∧
      (∀ alpha : ℝ, alpha < σ → XiZeroHalfPlaneBound alpha →
        ∃ X : ℕ, JasSinglePrimePositiveAbove X σ) := by
  refine ⟨fun ⟨X, hX⟩ => ?_, fun alpha h1 hXi =>
    exists_jasSinglePrimePositiveAbove_of_xiZeroHalfPlaneBound_of_lt h1 hXi⟩
  have := xiZeroHalfPlaneBound_of_jasSinglePrimePositiveAbove (by linarith) hσ hX
  rwa [max_eq_left hσ4] at this

/-- **Quasi-RH is single-prime JAS positivity below dressing `½`.** -/
theorem exists_xiZeroHalfPlaneBound_iff_exists_jasSinglePrimePositiveAbove :
    (∃ alpha : ℝ, alpha < 1 / 2 ∧ XiZeroHalfPlaneBound alpha) ↔
      ∃ X : ℕ, ∃ σ : ℝ, 0 ≤ σ ∧ σ < 1 / 2 ∧ JasSinglePrimePositiveAbove X σ := by
  constructor
  · rintro ⟨alpha, halpha, hXi⟩
    exact exists_jasSinglePrimePositiveAbove_of_xiZeroHalfPlaneBound halpha hXi
  · rintro ⟨X, σ, hσ0, hσ, h⟩
    exact ⟨max σ (1 / 4), max_lt hσ (by norm_num),
      xiZeroHalfPlaneBound_of_jasSinglePrimePositiveAbove hσ0 hσ h⟩

/-! ## The unconditional end of the single-prime scale -/

/-- `e^{−L/2} |Φ(L)| → 0`: every zero has `Re ρ < 1`, and the weights are summable. -/
theorem tendsto_abs_weilLagFunctionReal_mul_exp_neg_half :
    Tendsto (fun L : ℝ => |weilLagFunctionReal L| * Real.exp (-(L / 2))) atTop (𝓝 0) := by
  set f : ℝ → XiZeroCopy → ℝ := fun L q =>
    ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ * Real.exp (((q.1 : ℂ).re - 1) * L) with hf
  have hdom : Summable fun q : XiZeroCopy => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
    summable_inv_mul_one_sub.norm
  have hlim : Tendsto (fun L => ∑' q, f L q) atTop (𝓝 (∑' _q : XiZeroCopy, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence (𝓕 := atTop) hdom (fun q => ?_)
      (Filter.eventually_ge_atTop 0 |>.mono fun L hL q => ?_)
    · have h1 : ((q.1 : ℂ).re - 1) < 0 := by linarith [xiZeroCopy_re_lt_one q]
      have := Real.tendsto_exp_atBot.comp (tendsto_id.const_mul_atTop_of_neg h1)
      simpa [hf, Function.comp] using this.const_mul ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖
    · rw [hf, Real.norm_of_nonneg (by positivity)]
      refine mul_le_of_le_one_right (norm_nonneg _) (Real.exp_le_one_iff.mpr ?_)
      nlinarith [xiZeroCopy_re_lt_one q]
  rw [tsum_zero] at hlim
  refine squeeze_zero (fun L => by positivity) (fun L => ?_) hlim
  have hterm : ∀ q : XiZeroCopy, ‖cexp ((L : ℂ) * ((q.1 : ℂ) - 1 / 2)) /
      ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ * Real.exp (-(L / 2)) = f L q := by
    intro q
    rw [hf, div_eq_mul_one_div, norm_mul, Complex.norm_exp, mul_comm (Real.exp _), mul_assoc,
      ← Real.exp_add]
    congr 2
    simp [Complex.mul_re]
    ring
  have hs := (summable_weilLagTerm L).norm
  calc |weilLagFunctionReal L| * Real.exp (-(L / 2))
      ≤ (∑' q : XiZeroCopy, ‖cexp ((L : ℂ) * ((q.1 : ℂ) - 1 / 2)) /
          ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) * Real.exp (-(L / 2)) := by
        gcongr
        exact (Complex.abs_re_le_norm _).trans (norm_tsum_le_tsum_norm hs)
    _ = ∑' q, f L q := by rw [← tsum_mul_right]; exact tsum_congr hterm

/-- **The single-prime tests are positive at level `½` on all large primes, unconditionally.** -/
theorem exists_jasSinglePrimePositiveAbove_half : ∃ X : ℕ, JasSinglePrimePositiveAbove X (1 / 2) := by
  have hA := poleSharpConstant_pos
  obtain ⟨L₀, hL₀⟩ := Filter.eventually_atTop.mp
    (tendsto_abs_weilLagFunctionReal_mul_exp_neg_half.eventually (ge_mem_nhds hA))
  refine ⟨⌈Real.exp L₀⌉₊, jasSinglePrimePositiveAbove_iff.mpr fun p hp => ?_⟩
  have hpL : L₀ ≤ Real.log p := by
    have h1 : Real.exp L₀ ≤ (p : ℝ) := (Nat.le_ceil _).trans (by exact_mod_cast hp.le)
    rw [← Real.log_exp L₀]; exact Real.log_le_log (Real.exp_pos _) h1
  have h := hL₀ _ hpL
  have hE : Real.exp (-(Real.log p / 2)) * Real.exp (1 / 2 * Real.log p) = 1 := by
    rw [← Real.exp_add]; ring_nf; exact Real.exp_zero
  calc |weilLagFunctionReal (Real.log p)|
      = |weilLagFunctionReal (Real.log p)| * Real.exp (-(Real.log p / 2)) *
          Real.exp (1 / 2 * Real.log p) := by rw [mul_assoc, hE, mul_one]
    _ ≤ poleSharpConstant * Real.exp (1 / 2 * Real.log p) := by gcongr

/-! ## Dressing `0` -/

/-- **At dressing `0`, single-prime positivity on large primes is RH.** -/
theorem riemannHypothesis_iff_exists_jasSinglePrimePositiveAbove_zero :
    RiemannHypothesis ↔ ∃ X : ℕ, JasSinglePrimePositiveAbove X 0 := by
  constructor
  · intro hRH
    refine ⟨0, jasSinglePrimePositiveAbove_iff.mpr fun p _ => ?_⟩
    rw [zero_mul, Real.exp_zero, mul_one]
    exact abs_integerLag_le_of_riemannHypothesis hRH p
  · rintro ⟨X, h⟩
    have hb := jasSinglePrimePositiveAbove_iff.mp h
    refine riemannHypothesis_of_primeLag_le
      (M := poleSharpConstant + ∑ n ∈ Finset.range (X + 1), |integerLag n|) fun p hp => ?_
    have hsum0 : 0 ≤ ∑ n ∈ Finset.range (X + 1), |integerLag n| :=
      Finset.sum_nonneg fun _ _ => abs_nonneg _
    rcases lt_or_ge X p with hpX | hpX
    · have := hb ⟨p, hp⟩ hpX
      rw [zero_mul, Real.exp_zero, mul_one] at this
      have := le_abs_self (integerLag p)
      unfold integerLag at *
      linarith
    · have hmem : p ∈ Finset.range (X + 1) := Finset.mem_range.mpr (by omega)
      have h1 := Finset.single_le_sum (f := fun n => |integerLag n|) (fun _ _ => abs_nonneg _) hmem
      have h2 := le_abs_self (integerLag p)
      have hA := poleSharpConstant_pos
      linarith

/-! ## The JAS-internal capstone -/

/-- **JAS-internal capstone.**  RH holds iff, for some `X`, the single-prime tests on the primes
`p > X` are positive at some level `σ < ½` and the product tests on the primes `p > X` are positive
at `σ = 1`. -/
theorem riemannHypothesis_iff_exists_jasSinglePrime_and_jasProductPositiveAbove :
    RiemannHypothesis ↔ ∃ X : ℕ, (∃ σ : ℝ, 0 ≤ σ ∧ σ < 1 / 2 ∧ JasSinglePrimePositiveAbove X σ) ∧
      JasProductPositiveAbove X 1 := by
  constructor
  · intro hRH
    obtain ⟨⟨X, hX⟩, -⟩ := riemannHypothesis_iff_exists_jasProductPositiveAbove_one_and_quasi.mp hRH
    obtain ⟨Y, hY⟩ := riemannHypothesis_iff_exists_jasSinglePrimePositiveAbove_zero.mp hRH
    have hY0 : JasSinglePrimePositiveAbove 0 0 := by
      refine jasSinglePrimePositiveAbove_iff.mpr fun p _ => ?_
      rw [zero_mul, Real.exp_zero, mul_one]
      exact abs_integerLag_le_of_riemannHypothesis hRH p
    exact ⟨X, ⟨0, le_rfl, by norm_num, hY0.mono (Nat.zero_le X)⟩, hX⟩
  · rintro ⟨X, ⟨σ, hσ0, hσ, hS⟩, hP⟩
    exact riemannHypothesis_iff_exists_jasProductPositiveAbove_one_and_quasi.mpr
      ⟨⟨X, hP⟩, max σ (1 / 4), max_lt hσ (by norm_num),
        xiZeroHalfPlaneBound_of_jasSinglePrimePositiveAbove hσ0 hσ hS⟩

/-- **JAS-internal capstone, cosine form.**  RH holds iff, for some `X`, the single-prime tests on
primes `> X` are positive at some level `σ < ½`, and the zero measure is nonnegative against every
vertical translate of every prime cosine kernel `K_P`, `P` a finite set of primes `> X`, at `σ = 1`. -/
theorem riemannHypothesis_iff_exists_jasSinglePrime_and_jasCosinePositiveAbove :
    RiemannHypothesis ↔ ∃ X : ℕ, (∃ σ : ℝ, 0 ≤ σ ∧ σ < 1 / 2 ∧ JasSinglePrimePositiveAbove X σ) ∧
      JasCosinePositiveAbove X 1 := by
  rw [riemannHypothesis_iff_exists_jasSinglePrime_and_jasProductPositiveAbove]
  refine exists_congr fun X => and_congr_right fun _ => ?_
  exact jasProductPositiveAbove_iff_jasCosinePositiveAbove

/-! ## Monotonicity in the dressing level and the single-condition capstone -/

theorem norm_jasBernoulliFactor_dressed_le (q : XiZeroCopy) (c : ℝ) (p : Nat.Primes) (w : ℂ) :
    ‖jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + c) p) (jasHoloB ((q.1 : ℂ) - c) p) w‖ ≤
      1 + 2 * ‖w‖ * Real.exp (|c| * Real.log p) + ‖w‖ ^ 2 := by
  have hL := log_prime_pos p
  have h0 := xiZeroCopy_re_pos q
  have h1 := xiZeroCopy_re_lt_one q
  have hc := neg_abs_le c
  have hA : ‖jasHoloA ((q.1 : ℂ) + c) p‖ ≤ Real.exp (|c| * Real.log p) := by
    rw [norm_jasHoloA, Real.exp_le_exp, Complex.add_re, Complex.ofReal_re]
    nlinarith
  have hB : ‖jasHoloB ((q.1 : ℂ) - c) p‖ ≤ Real.exp (|c| * Real.log p) := by
    rw [norm_jasHoloB, Real.exp_le_exp, Complex.sub_re, Complex.ofReal_re]
    nlinarith
  have hw := norm_nonneg w
  calc ‖jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + c) p) (jasHoloB ((q.1 : ℂ) - c) p) w‖
      ≤ ‖(1 : ℂ)‖ + ‖w * jasHoloA ((q.1 : ℂ) + c) p‖ + ‖conj w * jasHoloB ((q.1 : ℂ) - c) p‖ +
          ‖w * conj w‖ := by
        rw [jasBernoulliFactor]
        calc _ ≤ ‖1 + w * jasHoloA ((q.1 : ℂ) + c) p + conj w * jasHoloB ((q.1 : ℂ) - c) p‖ +
              ‖w * conj w‖ := norm_add_le _ _
          _ ≤ ‖1 + w * jasHoloA ((q.1 : ℂ) + c) p‖ + ‖conj w * jasHoloB ((q.1 : ℂ) - c) p‖ +
              ‖w * conj w‖ := by gcongr; exact norm_add_le _ _
          _ ≤ _ := by gcongr; exact norm_add_le _ _
    _ ≤ 1 + ‖w‖ * Real.exp (|c| * Real.log p) + ‖w‖ * Real.exp (|c| * Real.log p) + ‖w‖ ^ 2 := by
        rw [norm_one, norm_mul, norm_mul, norm_mul, Complex.norm_conj, ← sq]
        gcongr
    _ = 1 + 2 * ‖w‖ * Real.exp (|c| * Real.log p) + ‖w‖ ^ 2 := by ring

theorem summable_jasBernoulliAggregate (T : Finset Nat.Primes) (c : ℝ) (w : Nat.Primes → ℂ) :
    Summable fun q : XiZeroCopy =>
      (∏ p ∈ T, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + c) p) (jasHoloB ((q.1 : ℂ) - c) p) (w p)) /
        ((q.1 : ℂ) * (1 - (q.1 : ℂ))) := by
  refine (summable_inv_mul_one_sub.norm.mul_left
    (∏ p ∈ T, (1 + 2 * ‖w p‖ * Real.exp (|c| * Real.log p) + ‖w p‖ ^ 2))).of_norm_bounded
    fun q => ?_
  rw [div_eq_mul_one_div, norm_mul, norm_prod]
  gcongr with p
  exact norm_jasBernoulliFactor_dressed_le q c p (w p)

/-- **Product-test positivity is monotone in the dressing level.**  A factor at level `σ'` is a
factor at level `σ` evaluated at `p^{−(σ'−σ)} z`, plus the nonnegative constant
`|z|²(1 − p^{−2(σ'−σ)})`. -/
theorem JasProductPositiveAbove.mono_level {X : ℕ} {σ σ' : ℝ} (h : JasProductPositiveAbove X σ)
    (hσ : σ ≤ σ') : JasProductPositiveAbove X σ' := by
  classical
  intro P hP z
  obtain ⟨s, hs⟩ : ∃ s : Nat.Primes → ℝ, s = fun p : Nat.Primes => Real.exp (-(σ' - σ) * Real.log p) :=
    ⟨_, rfl⟩
  obtain ⟨z', hz'⟩ : ∃ z' : Nat.Primes → ℂ, z' = fun p => (s p : ℂ) * z p := ⟨_, rfl⟩
  obtain ⟨k, hk⟩ : ∃ k : Nat.Primes → ℝ, k = fun p => ‖z p‖ ^ 2 * (1 - s p ^ 2) := ⟨_, rfl⟩
  have hs1 : ∀ p, s p ≤ 1 := fun p => by
    rw [hs, Real.exp_le_one_iff]; nlinarith [log_prime_pos p]
  have hs0 : ∀ p, 0 ≤ s p := fun p => by rw [hs]; exact (Real.exp_pos _).le
  have hk0 : ∀ p, 0 ≤ k p := fun p => by
    rw [hk]; exact mul_nonneg (sq_nonneg _) (by nlinarith [hs1 p, hs0 p])
  have hA : ∀ (q : ℂ) (p : Nat.Primes), jasHoloA (q + ((σ' - 1 / 2 : ℝ) : ℂ)) p =
      (s p : ℂ) * jasHoloA (q + ((σ - 1 / 2 : ℝ) : ℂ)) p := fun q p => by
    rw [hs, jasHoloA, jasHoloA, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hB : ∀ (q : ℂ) (p : Nat.Primes), jasHoloB (q - ((σ' - 1 / 2 : ℝ) : ℂ)) p =
      (s p : ℂ) * jasHoloB (q - ((σ - 1 / 2 : ℝ) : ℂ)) p := fun q p => by
    rw [hs, jasHoloB, jasHoloB, Complex.ofReal_exp, ← Complex.exp_add]
    congr 1; push_cast; ring
  have hfac : ∀ (q : XiZeroCopy) (p : Nat.Primes),
      jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ' - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ' - 1 / 2 : ℝ)) p) (z p) =
      jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z' p) + (k p : ℂ) := by
    intro q p
    have hzz : z p * conj (z p) = ((‖z p‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [jasBernoulliFactor, jasBernoulliFactor, hA, hB, hz', hk]
    simp only [map_mul, Complex.conj_ofReal]
    rw [show (s p : ℂ) * z p * ((s p : ℂ) * conj (z p)) = (s p : ℂ) ^ 2 * (z p * conj (z p)) by ring,
      hzz]
    push_cast
    ring
  have hexp : ∀ q : XiZeroCopy, (∏ p ∈ P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ' - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ' - 1 / 2 : ℝ)) p) (z p)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) =
      ∑ T ∈ P.powerset, ((∏ p ∈ P \ T, k p : ℝ) : ℂ) *
        ((∏ p ∈ T, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
          (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z' p)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
    intro q
    simp_rw [hfac q]
    rw [Finset.prod_add, Finset.sum_div]
    refine Finset.sum_congr rfl fun T _ => ?_
    push_cast
    ring
  have hsum : ∀ T ∈ P.powerset, Summable fun q : XiZeroCopy => ((∏ p ∈ P \ T, k p : ℝ) : ℂ) *
      ((∏ p ∈ T, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
        (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) (z' p)) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) :=
    fun T _ => (summable_jasBernoulliAggregate T (σ - 1 / 2) z').mul_left _
  simp_rw [hexp]
  rw [Summable.tsum_finsetSum hsum, Complex.re_sum]
  refine Finset.sum_nonneg fun T hT => ?_
  rw [tsum_mul_left, Complex.re_ofReal_mul]
  refine mul_nonneg (Finset.prod_nonneg fun p _ => hk0 p) ?_
  exact h T (fun p hp => hP p (Finset.mem_powerset.mp hT hp)) z'

/-- **Single-condition capstone.**  RH holds iff, for some `X` and some level `0 ≤ σ < ½`, the
Bernoulli product tests on the primes `p > X` are positive at `σ`. -/
theorem riemannHypothesis_iff_exists_jasProductPositiveAbove_lt_half :
    RiemannHypothesis ↔ ∃ X : ℕ, ∃ σ : ℝ, 0 ≤ σ ∧ σ < 1 / 2 ∧ JasProductPositiveAbove X σ := by
  constructor
  · intro hRH
    exact ⟨0, 0, le_rfl, by norm_num, JasDressedPSDAbove.productPositive fun S _ =>
      (jasDressedPSD_zero_of_riemannHypothesis hRH).on S⟩
  · rintro ⟨X, σ, hσ0, hσ, h⟩
    exact riemannHypothesis_iff_exists_jasSinglePrime_and_jasProductPositiveAbove.mpr
      ⟨X, ⟨σ, hσ0, hσ, h.singlePrime⟩, h.mono_level (by linarith)⟩

/-- At dressing `0` the cosine kernel is a product of squares:
`K_P(s) = ∏_{p ∈ P} 2 cosh²((s − ½) log p / 2)`. -/
theorem jasCosineKernel_zero (P : Finset Nat.Primes) (s : ℂ) :
    jasCosineKernel P 0 s =
      ∏ p ∈ P, 2 * Complex.cosh ((s - 1 / 2) * (Real.log p : ℂ) / 2) ^ 2 := by
  rw [jasCosineKernel]
  refine Finset.prod_congr rfl fun p _ => ?_
  have h2 := Complex.cosh_two_mul ((s - 1 / 2) * (Real.log p : ℂ) / 2)
  have hs := Complex.cosh_sq ((s - 1 / 2) * (Real.log p : ℂ) / 2)
  rw [show 2 * ((s - 1 / 2) * (Real.log p : ℂ) / 2) = (s - 1 / 2) * (Real.log p : ℂ) by ring] at h2
  rw [neg_zero, zero_mul, Real.exp_zero, Complex.ofReal_one, one_mul, h2]
  linear_combination (-1 : ℂ) * hs

/-- **Single-condition cosine capstone.**  RH holds iff, for some `X` and some level `0 ≤ σ < ½`,
the zero measure is nonnegative against every vertical translate of every prime cosine kernel
`K_P`, `P` a finite set of primes `> X`. -/
theorem riemannHypothesis_iff_exists_jasCosinePositiveAbove_lt_half :
    RiemannHypothesis ↔ ∃ X : ℕ, ∃ σ : ℝ, 0 ≤ σ ∧ σ < 1 / 2 ∧ JasCosinePositiveAbove X σ := by
  rw [riemannHypothesis_iff_exists_jasProductPositiveAbove_lt_half]
  simp only [jasProductPositiveAbove_iff_jasCosinePositiveAbove]

/-- **The cosh-square criterion.**  RH holds iff for some `X`,
`Re Σ_ρ ∏_{p ∈ P} cosh²((ρ − ½ − it) log p / 2)/(ρ(1−ρ)) ≥ 0` for every finite set `P` of primes
`> X` and every real `t` (dressing `0`, where `K_P = ∏ 2 cosh²`). -/
theorem riemannHypothesis_iff_exists_jasCosinePositiveAbove_zero :
    RiemannHypothesis ↔ ∃ X : ℕ, JasCosinePositiveAbove X 0 := by
  constructor
  · intro hRH
    exact ⟨0, (JasDressedPSDAbove.productPositive fun S _ =>
      (jasDressedPSD_zero_of_riemannHypothesis hRH).on S).cosinePositive⟩
  · rintro ⟨X, h⟩
    exact riemannHypothesis_iff_exists_jasSinglePrimePositiveAbove_zero.mpr
      ⟨X, (jasProductPositiveAbove_of_cosinePositive h).singlePrime⟩

end

end RHTower
