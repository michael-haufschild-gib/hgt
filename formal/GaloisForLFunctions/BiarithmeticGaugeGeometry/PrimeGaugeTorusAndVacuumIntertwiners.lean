import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The Prime Gauge Torus, Multiplicative Vacuum Blindness, and Catalan–Bézout Successor Holonomy

Biarithmetic gauge geometry begins by separating what purely multiplicative operators on `ℕ` can
observe from what requires coupling multiplication to the additive successor `n ↦ n + 1`.

1. **The prime gauge torus (`PrimeGauge`, `gaugeChar`).**
   A unitary prime gauge assigns a unit complex phase `ω(p)` (`‖ω(p)‖ = 1`) to each prime `p` and
   extends by unique factorization to a completely multiplicative character `gaugeChar ω : ℕ → ℂ`
   on `ℕ \ {0}`. Distinguished points include the **Euler vacuum** `eulerGauge` (`ω(p) = 1`), the
   **Liouville vacuum** `liouvilleGauge` (`ω(p) = -1`, whose character is Liouville's `λ(n)`), and
   the **Kronecker archimedean line** `kroneckerGauge γ` (`ω(p) = p^{iγ}`).

2. **Unitary gauge equivalence and multiplicative blindness (`diagForm_gaugeTwist_eq`,
   `ratioShift_gaugeTwist_eq`, `realSign_latticeForm_eq`, `nonneg_realSign_latticeForm_iff`).**
   Pointwise multiplication `gaugeTwist ω ψ n = gaugeChar ω n * ψ n` is norm-preserving on `ℕ \ {0}`,
   leaves every diagonal archimedean potential invariant, and intertwines every multiplicative
   ratio shift `a ↦ a * m` with multiplication by `gaugeChar ω m`. For any real sign gauge
   (`ω(p) ∈ {±1}`, including `liouvilleGauge`), **both** ratio shifts and product crossings
   `(a, b) ↦ a * b` are unitarily equivalent to the untwisted Euler form on every finite horizon
   `[1, X]`. Consequently, no quadratic form built solely from diagonal archimedean weights, sharp
   horizon cutoffs, and multiplicative ratio/product incidences can distinguish `ζ` from its
   Liouville twin `λ`.

3. **Successor gauge connection and Catalan–Bézout reconstruction (`succConn`,
   `succConn_flat_iff_primes_eq_one`, `catalan_holonomy_two`, `catalan_holonomy_three`).**
   Conjugating the additive successor shift `n ↦ n + 1` introduces the discrete gauge connection
   `succConn ω n = conj(gaugeChar ω n) * gaugeChar ω (n + 1)`. Flatness (`succConn ω n = 1` for
   `1 ≤ n ≤ N`) holds iff `ω(p) = 1` for every prime `p ≤ N + 1`. Already on the minimal Catalan
   interval `2 → 3 → 4 = 2²`, the two successor links `A₂ = succConn ω 2` and `A₃ = succConn ω 3`
   algebraically reconstruct the prime phases via `A₂ * A₃ = ω(2)` and `A₂² * A₃ = ω(3)`,
   detecting the Liouville parity jump `succConn liouvilleGauge 3 = -1`.
-/

open Finset Complex

noncomputable section
set_option autoImplicit false

namespace GaloisForLFunctions.BiarithmeticGaugeGeometry

/-! ## §1. The unitary prime gauge torus and its completely multiplicative lift -/

/-- A unitary gauge field on the primes: a phase `ω(p) ∈ U(1)` at each prime `p`, normalized to `1`
at non-primes. -/
structure PrimeGauge where
  val : ℕ → ℂ
  norm_prime : ∀ {p : ℕ}, p.Prime → ‖val p‖ = 1
  nonprime_eq_one : ∀ {n : ℕ}, ¬ n.Prime → val n = 1

namespace PrimeGauge

@[ext]
theorem ext {ω₁ ω₂ : PrimeGauge} (h : ∀ n : ℕ, ω₁.val n = ω₂.val n) : ω₁ = ω₂ := by
  cases ω₁; cases ω₂; simp only [mk.injEq]; funext n; exact h n

/-- Every value `ω.val n` (`n : ℕ`) has unit complex norm. -/
theorem norm_val (ω : PrimeGauge) (n : ℕ) : ‖ω.val n‖ = 1 := by
  by_cases hn : n.Prime
  · exact ω.norm_prime hn
  · rw [ω.nonprime_eq_one hn, norm_one]

theorem val_ne_zero (ω : PrimeGauge) (n : ℕ) : ω.val n ≠ 0 := by
  intro h0
  have h1 := ω.norm_val n
  rw [h0, norm_zero] at h1
  norm_num at h1

theorem conj_mul_val (ω : PrimeGauge) (n : ℕ) :
    starRingEnd ℂ (ω.val n) * ω.val n = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ω.norm_val n]
  norm_num

theorem val_mul_conj (ω : PrimeGauge) (n : ℕ) :
    ω.val n * starRingEnd ℂ (ω.val n) = 1 := by
  rw [mul_comm, ω.conj_mul_val n]

/-- The **Euler vacuum** `ω ≡ 1`, corresponding to untwisted `ζ`. -/
def eulerGauge : PrimeGauge where
  val _ := 1
  norm_prime _ := norm_one
  nonprime_eq_one _ := rfl

/-- The **Liouville vacuum** `ω(p) = -1` on primes, whose multiplicative character is Liouville's
function `λ(n) = (-1)^{Ω(n)}`. -/
def liouvilleGauge : PrimeGauge where
  val n := if n.Prime then -1 else 1
  norm_prime hp := by simp [hp]
  nonprime_eq_one hn := by simp [hn]

/-- The **Kronecker archimedean gauge** `ω_γ(p) = p^{iγ}` (`γ ∈ ℝ`) induced by vertical shift
`s ↦ s - iγ`. -/
def kroneckerGauge (γ : ℝ) : PrimeGauge where
  val n := if n.Prime then (n : ℂ) ^ ((γ : ℂ) * I) else 1
  norm_prime {p} hp := by
    simp only [hp, ↓reduceIte]
    have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
    have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hlog : Complex.log (p : ℂ) = (Real.log (p : ℝ) : ℂ) := by
      have hp_cast : (p : ℂ) = ((p : ℝ) : ℂ) := by simp
      rw [hp_cast, ← Complex.ofReal_log hp_pos.le]
    rw [Complex.cpow_def_of_ne_zero hp_ne, hlog, Complex.norm_exp]
    have hre : ((Real.log (p : ℝ) : ℂ) * ((γ : ℂ) * I)).re = 0 := by
      rw [Complex.re_ofReal_mul]
      simp
    rw [hre, Real.exp_zero]
  nonprime_eq_one hn := by simp [hn]

/-- Complex-conjugate (inverse) gauge `ω̄(p) = conj(ω(p))`. -/
def conjGauge (ω : PrimeGauge) : PrimeGauge where
  val n := starRingEnd ℂ (ω.val n)
  norm_prime hp := by rw [RingHomIsometric.norm_map, ω.norm_prime hp]
  nonprime_eq_one hn := by rw [ω.nonprime_eq_one hn, map_one]

/-- Completely multiplicative lift `χ_ω : ℕ → ℂ` of a prime gauge (`χ_ω(0) = 0`). -/
def gaugeChar (ω : PrimeGauge) (n : ℕ) : ℂ :=
  if n = 0 then 0 else n.factorization.prod (fun p e => ω.val p ^ e)

@[simp]
theorem gaugeChar_zero (ω : PrimeGauge) : ω.gaugeChar 0 = 0 := rfl

@[simp]
theorem gaugeChar_one (ω : PrimeGauge) : ω.gaugeChar 1 = 1 := by
  simp [gaugeChar]

theorem gaugeChar_of_ne_zero (ω : PrimeGauge) {n : ℕ} (hn : n ≠ 0) :
    ω.gaugeChar n = n.factorization.prod (fun p e => ω.val p ^ e) := by
  simp [gaugeChar, hn]

@[simp]
theorem gaugeChar_prime (ω : PrimeGauge) {p : ℕ} (hp : p.Prime) :
    ω.gaugeChar p = ω.val p := by
  rw [ω.gaugeChar_of_ne_zero hp.ne_zero, hp.factorization, Finsupp.prod_single_index]
  · exact pow_one _
  · exact pow_zero _

/-- Complete multiplicativity of `gaugeChar ω` across all `m, n : ℕ`. -/
theorem gaugeChar_mul (ω : PrimeGauge) (m n : ℕ) :
    ω.gaugeChar (m * n) = ω.gaugeChar m * ω.gaugeChar n := by
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ω.gaugeChar_of_ne_zero (mul_ne_zero hm hn), ω.gaugeChar_of_ne_zero hm,
    ω.gaugeChar_of_ne_zero hn, Nat.factorization_mul hm hn]
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem gaugeChar_pow (ω : PrimeGauge) (n k : ℕ) :
    ω.gaugeChar (n ^ k) = ω.gaugeChar n ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ω.gaugeChar_mul, ih, pow_succ]

/-- Unit-modulus law: `‖χ_ω(n)‖ = 1` for every `n ≥ 1`. -/
theorem norm_gaugeChar (ω : PrimeGauge) {n : ℕ} (hn : n ≠ 0) :
    ‖ω.gaugeChar n‖ = 1 := by
  rw [ω.gaugeChar_of_ne_zero hn]
  unfold Finsupp.prod
  rw [norm_prod]
  refine Finset.prod_eq_one fun p _ => ?_
  rw [norm_pow, ω.norm_val p, one_pow]

theorem conj_gaugeChar_eq (ω : PrimeGauge) (n : ℕ) :
    starRingEnd ℂ (ω.gaugeChar n) = ω.conjGauge.gaugeChar n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [ω.gaugeChar_of_ne_zero hn, ω.conjGauge.gaugeChar_of_ne_zero hn]
  unfold Finsupp.prod
  rw [map_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [map_pow]
  rfl

theorem conj_mul_gaugeChar (ω : PrimeGauge) {n : ℕ} (hn : n ≠ 0) :
    starRingEnd ℂ (ω.gaugeChar n) * ω.gaugeChar n = 1 := by
  rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, ω.norm_gaugeChar hn]
  norm_num

theorem gaugeChar_euler {n : ℕ} (hn : n ≠ 0) : eulerGauge.gaugeChar n = 1 := by
  rw [gaugeChar_of_ne_zero _ hn]
  unfold Finsupp.prod
  refine Finset.prod_eq_one fun _ _ => ?_
  simp [eulerGauge]

theorem gaugeChar_kronecker_prime_pow (γ : ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (kroneckerGauge γ).gaugeChar (p ^ k) = ((p ^ k : ℕ) : ℂ) ^ ((γ : ℂ) * I) := by
  rw [gaugeChar_pow, gaugeChar_prime _ hp]
  simp only [kroneckerGauge, hp, ↓reduceIte]
  have hp_pos : (0 : ℝ) < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hrpow : (((p : ℝ) ^ k : ℝ) : ℂ) ^ ((γ : ℂ) * I) =
      (((p : ℝ) : ℂ) ^ ((γ : ℂ) * I)) ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
      have hk_pos : (0 : ℝ) ≤ (p : ℝ) ^ k := pow_nonneg hp_pos.le k
      rw [pow_succ, Complex.ofReal_mul,
        Complex.mul_cpow_ofReal_nonneg hk_pos hp_pos.le, ih, pow_succ]
  have hcast : ((p ^ k : ℕ) : ℂ) = ((p : ℝ) ^ k : ℝ) := by push_cast; rfl
  have hp_cast : ((p : ℝ) : ℂ) = (p : ℂ) := by simp
  rw [hcast, hrpow, hp_cast]

end PrimeGauge

/-! ## §2. Unitary gauge intertwining and blindness of multiplicative lattice forms -/

/-- Pointwise unitary gauge transformation `(U_ω ψ)(n) = χ_ω(n) ψ(n)`. -/
def gaugeTwist (ω : PrimeGauge) (ψ : ℕ → ℂ) (n : ℕ) : ℂ :=
  ω.gaugeChar n * ψ n

theorem norm_gaugeTwist (ω : PrimeGauge) (ψ : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    ‖gaugeTwist ω ψ n‖ = ‖ψ n‖ := by
  rw [gaugeTwist, norm_mul, ω.norm_gaugeChar hn, one_mul]

theorem gaugeTwist_conj_cancel (ω : PrimeGauge) (ψ : ℕ → ℂ) {n : ℕ} (hn : n ≠ 0) :
    gaugeTwist ω.conjGauge (gaugeTwist ω ψ) n = ψ n := by
  unfold gaugeTwist
  rw [← ω.conj_gaugeChar_eq n, ← mul_assoc, ω.conj_mul_gaugeChar hn, one_mul]

/-- Every real diagonal potential (including archimedean digamma and reflected-diagonal weights)
is strictly invariant under `gaugeTwist ω` on `[1, X]`. -/
theorem diagForm_gaugeTwist_eq (ω : PrimeGauge) (W : ℕ → ℝ) (ψ : ℕ → ℂ) (X : ℕ) :
    ∑ n ∈ Icc 1 X, W n * ‖gaugeTwist ω ψ n‖ ^ 2 =
      ∑ n ∈ Icc 1 X, W n * ‖ψ n‖ ^ 2 := by
  refine Finset.sum_congr rfl fun n hn => ?_
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
  rw [norm_gaugeTwist ω ψ hn0]

/-- Multiplicative ratio shifts intertwine with `gaugeTwist ω` via the scalar factor `χ_ω(m)`. -/
theorem ratioShift_gaugeTwist_eq (ω : PrimeGauge) (ψ : ℕ → ℂ) {a : ℕ} (ha : a ≠ 0) (m : ℕ) :
    starRingEnd ℂ (gaugeTwist ω ψ a) * gaugeTwist ω ψ (a * m) =
      ω.gaugeChar m * (starRingEnd ℂ (ψ a) * ψ (a * m)) := by
  unfold gaugeTwist
  rw [ω.gaugeChar_mul a m, map_mul]
  calc (starRingEnd ℂ (ω.gaugeChar a) * starRingEnd ℂ (ψ a)) *
        (ω.gaugeChar a * ω.gaugeChar m * ψ (a * m))
      = (starRingEnd ℂ (ω.gaugeChar a) * ω.gaugeChar a) *
          (ω.gaugeChar m * (starRingEnd ℂ (ψ a) * ψ (a * m))) := by ring
    _ = ω.gaugeChar m * (starRingEnd ℂ (ψ a) * ψ (a * m)) := by
        rw [ω.conj_mul_gaugeChar ha, one_mul]

/-- A prime gauge is a **real sign gauge** when `ω(p) ∈ {1, -1}` at every prime. -/
def IsRealSignGauge (ω : PrimeGauge) : Prop :=
  ∀ {p : ℕ}, p.Prime → ω.val p = 1 ∨ ω.val p = -1

theorem isRealSignGauge_euler : IsRealSignGauge PrimeGauge.eulerGauge :=
  fun _ => Or.inl rfl

theorem isRealSignGauge_liouville : IsRealSignGauge PrimeGauge.liouvilleGauge :=
  fun hp => Or.inr (by simp [PrimeGauge.liouvilleGauge, hp])

/-- Real-valued multiplicative sign character `σ_ω(n) = Re χ_ω(n)` of a real sign gauge. -/
def realSignChar (ω : PrimeGauge) (n : ℕ) : ℝ :=
  (ω.gaugeChar n).re

theorem gaugeChar_eq_realSignChar {ω : PrimeGauge} (hω : IsRealSignGauge ω) (n : ℕ) :
    ω.gaugeChar n = (realSignChar ω n : ℂ) := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [realSignChar]
  suffices hre : (ω.gaugeChar n).im = 0 by
    apply Complex.ext <;> simp [realSignChar, hre]
  rw [ω.gaugeChar_of_ne_zero hn]
  unfold Finsupp.prod
  have hreal : ∀ s : Finset ℕ, (∀ p ∈ s, (ω.val p).im = 0) →
      (∏ p ∈ s, ω.val p ^ n.factorization p).im = 0 := by
    intro s hs
    induction s using Finset.induction_on with
    | empty => simp
    | @insert p s hp ih =>
      rw [Finset.prod_insert hp]
      have hp0 : (ω.val p).im = 0 := hs p (Finset.mem_insert_self p s)
      have hp_pow : (ω.val p ^ n.factorization p).im = 0 := by
        have heq : ω.val p = ((ω.val p).re : ℂ) := by apply Complex.ext <;> simp [hp0]
        rw [heq, ← Complex.ofReal_pow, Complex.ofReal_im]
      have hs0 : (∏ q ∈ s, ω.val q ^ n.factorization q).im = 0 :=
        ih fun q hq => hs q (Finset.mem_insert_of_mem hq)
      simp [Complex.mul_im, hp_pow, hs0]
  refine hreal _ fun p _ => ?_
  by_cases hp : p.Prime
  · rcases hω hp with h1 | hm1
    · simp [h1]
    · simp [hm1]
  · simp [ω.nonprime_eq_one hp]

theorem realSignChar_mul {ω : PrimeGauge} (hω : IsRealSignGauge ω) (m n : ℕ) :
    realSignChar ω (m * n) = realSignChar ω m * realSignChar ω n := by
  have h := congrArg Complex.re (ω.gaugeChar_mul m n)
  rw [gaugeChar_eq_realSignChar hω m, gaugeChar_eq_realSignChar hω n,
    ← Complex.ofReal_mul, Complex.ofReal_re] at h
  exact h

theorem realSignChar_sq_eq_one {ω : PrimeGauge} (hω : IsRealSignGauge ω) {n : ℕ} (hn : n ≠ 0) :
    realSignChar ω n ^ 2 = 1 := by
  have hnorm := ω.norm_gaugeChar hn
  rw [gaugeChar_eq_realSignChar hω n, Complex.norm_real, Real.norm_eq_abs] at hnorm
  rw [← sq_abs, hnorm, one_pow]

/-- Real lattice quadratic form combining an arbitrary diagonal weight `W_diag`, ratio shift weight
`w_ratio`, and product crossing weight `w_prod`, twisted by `realSignChar ω`. -/
def twistedLatticeForm (ω : PrimeGauge) (W_diag w_ratio w_prod : ℕ → ℝ) (X : ℕ) (q : ℕ → ℝ) : ℝ :=
  (∑ n ∈ Icc 1 X, W_diag n * q n ^ 2) +
    (∑ m ∈ Icc 2 X, w_ratio m * realSignChar ω m * ∑ a ∈ Icc 1 X, q a * q (a * m)) +
    (∑ a ∈ Icc 1 X, ∑ b ∈ Icc 1 X, w_prod (a * b) * realSignChar ω (a * b) * q a * q b)

/-- **Unitary equivalence of real sign-gauge lattice forms (`realSign_latticeForm_eq`).**
For any real sign gauge `ω` (in particular `liouvilleGauge`), twisting the test profile on `[1, ∞)`
by `q'(n) = σ_ω(n) q(n)` identifies the `ω`-twisted combined diagonal + ratio + product quadratic
form identically with the untwisted Euler form! -/
theorem realSign_latticeForm_eq {ω : PrimeGauge} (hω : IsRealSignGauge ω)
    (W_diag w_ratio w_prod : ℕ → ℝ) (X : ℕ) (q : ℕ → ℝ) :
    twistedLatticeForm ω W_diag w_ratio w_prod X (fun n => realSignChar ω n * q n) =
      twistedLatticeForm PrimeGauge.eulerGauge W_diag w_ratio w_prod X q := by
  have heuler : ∀ {k : ℕ}, k ≠ 0 → realSignChar PrimeGauge.eulerGauge k = 1 := by
    intro k hk
    simp [realSignChar, PrimeGauge.gaugeChar_euler hk]
  unfold twistedLatticeForm
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl fun n hn => ?_
      have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
      have hsq : (realSignChar ω n * q n) ^ 2 = q n ^ 2 := by
        rw [mul_pow, realSignChar_sq_eq_one hω hn0, one_mul]
      rw [hsq]
    · refine Finset.sum_congr rfl fun m hm => ?_
      have hm0 : m ≠ 0 := by have := (mem_Icc.mp hm).1; omega
      rw [heuler hm0, mul_one, Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun a ha => ?_
      dsimp only
      have ha0 : a ≠ 0 := by have := (mem_Icc.mp ha).1; omega
      rw [realSignChar_mul hω a m]
      calc w_ratio m * realSignChar ω m *
            (realSignChar ω a * q a * (realSignChar ω a * realSignChar ω m * q (a * m)))
          = w_ratio m * (realSignChar ω m ^ 2) * (realSignChar ω a ^ 2) * (q a * q (a * m)) := by
              ring
        _ = w_ratio m * (q a * q (a * m)) := by
              rw [realSignChar_sq_eq_one hω hm0, realSignChar_sq_eq_one hω ha0]; ring
  · refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
    dsimp only
    have ha0 : a ≠ 0 := by have := (mem_Icc.mp ha).1; omega
    have hb0 : b ≠ 0 := by have := (mem_Icc.mp hb).1; omega
    have hab0 : a * b ≠ 0 := mul_ne_zero ha0 hb0
    rw [heuler hab0, realSignChar_mul hω a b]
    calc w_prod (a * b) * (realSignChar ω a * realSignChar ω b) *
          (realSignChar ω a * q a) * (realSignChar ω b * q b)
        = w_prod (a * b) * (realSignChar ω a ^ 2) * (realSignChar ω b ^ 2) * q a * q b := by ring
      _ = w_prod (a * b) * 1 * q a * q b := by
            rw [realSignChar_sq_eq_one hω ha0, realSignChar_sq_eq_one hω hb0]; ring

/-- **Complete blindness of multiplicative lattice positivity to real sign gauges:**
a combined diagonal + ratio + product lattice quadratic form is nonnegative for all profiles
vanishing above `X` at a real sign gauge `ω` (such as `liouvilleGauge`) if and only if it is
nonnegative at `eulerGauge`! -/
theorem nonneg_realSign_latticeForm_iff {ω : PrimeGauge} (hω : IsRealSignGauge ω)
    (W_diag w_ratio w_prod : ℕ → ℝ) (X : ℕ) :
    (∀ q : ℕ → ℝ, (∀ n, X < n → q n = 0) →
      0 ≤ twistedLatticeForm ω W_diag w_ratio w_prod X q) ↔
    (∀ q : ℕ → ℝ, (∀ n, X < n → q n = 0) →
      0 ≤ twistedLatticeForm PrimeGauge.eulerGauge W_diag w_ratio w_prod X q) := by
  constructor
  · intro h q hq
    rw [← realSign_latticeForm_eq hω W_diag w_ratio w_prod X q]
    exact h _ fun n hn => by simp [hq n hn]
  · intro h q hq
    have hq_inv : twistedLatticeForm ω W_diag w_ratio w_prod X q =
        twistedLatticeForm ω W_diag w_ratio w_prod X
          (fun n => realSignChar ω n * (realSignChar ω n * q n)) := by
      unfold twistedLatticeForm
      have hcancel : ∀ {k : ℕ}, k ≠ 0 →
          realSignChar ω k * (realSignChar ω k * q k) = q k := fun {k} hk => by
        rw [← mul_assoc, ← sq, realSignChar_sq_eq_one hω hk, one_mul]
      congr 1
      · congr 1
        · refine Finset.sum_congr rfl fun n hn => ?_
          dsimp only
          have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
          rw [hcancel hn0]
        · refine Finset.sum_congr rfl fun m hm => ?_
          have hm0 : m ≠ 0 := by have := (mem_Icc.mp hm).1; omega
          congr 1
          refine Finset.sum_congr rfl fun a ha => ?_
          dsimp only
          have ha0 : a ≠ 0 := by have := (mem_Icc.mp ha).1; omega
          rw [hcancel ha0, hcancel (mul_ne_zero ha0 hm0)]
      · refine Finset.sum_congr rfl fun a ha => Finset.sum_congr rfl fun b hb => ?_
        dsimp only
        have ha0 : a ≠ 0 := by have := (mem_Icc.mp ha).1; omega
        have hb0 : b ≠ 0 := by have := (mem_Icc.mp hb).1; omega
        rw [hcancel ha0, hcancel hb0]
    rw [hq_inv, realSign_latticeForm_eq hω]
    exact h _ fun n hn => by simp [hq n hn]

/-! ## §3. The biarithmetic successor connection and Catalan–Bézout `{1, 2, 3, 4}` reconstruction -/

/-- Discrete successor gauge connection `A_ω(n) = conj(χ_ω(n)) · χ_ω(n + 1)` coupling
additive shift `n ↦ n + 1` to the multiplicative prime gauge `ω`. -/
def succConn (ω : PrimeGauge) (n : ℕ) : ℂ :=
  starRingEnd ℂ (ω.gaugeChar n) * ω.gaugeChar (n + 1)

/-- Covariant transport of the additive successor pairing under `gaugeTwist ω`. -/
theorem succShift_gaugeTwist_eq (ω : PrimeGauge) (ψ : ℕ → ℂ) (n : ℕ) :
    starRingEnd ℂ (gaugeTwist ω ψ n) * gaugeTwist ω ψ (n + 1) =
      succConn ω n * (starRingEnd ℂ (ψ n) * ψ (n + 1)) := by
  unfold gaugeTwist succConn
  rw [map_mul]
  ring

theorem succConn_euler {n : ℕ} (hn : n ≠ 0) : succConn PrimeGauge.eulerGauge n = 1 := by
  unfold succConn
  rw [PrimeGauge.gaugeChar_euler hn, PrimeGauge.gaugeChar_euler (Nat.succ_ne_zero n), map_one,
    one_mul]

/-- **Successor flatness characterizes the Euler vacuum (`succConn_flat_iff_primes_eq_one`).**
The successor connection is trivial (`succConn ω n = 1`) across `1 ≤ n ≤ N` if and only if
`ω(p) = 1` for every prime `p ≤ N + 1`. -/
theorem succConn_flat_iff_primes_eq_one (ω : PrimeGauge) (N : ℕ) :
    (∀ n ∈ Icc 1 N, succConn ω n = 1) ↔
      ∀ p : ℕ, p ≤ N + 1 → p.Prime → ω.val p = 1 := by
  constructor
  · intro hflat
    have hall : ∀ m : ℕ, 1 ≤ m → m ≤ N + 1 → ω.gaugeChar m = 1 := by
      intro m hm1 hmN
      induction m with
      | zero => omega
      | succ k ih =>
        rcases eq_or_ne k 0 with rfl | hk0
        · exact ω.gaugeChar_one
        · have hk1 : 1 ≤ k := Nat.pos_of_ne_zero hk0
          have hkN : k ≤ N := by omega
          have hconn := hflat k (mem_Icc.mpr ⟨hk1, hkN⟩)
          have hprev := ih hk1 (by omega)
          unfold succConn at hconn
          rw [hprev, map_one, one_mul] at hconn
          exact hconn
    intro p hpN hp
    rw [← ω.gaugeChar_prime hp]
    exact hall p hp.pos hpN
  · intro hprimes n hn
    obtain ⟨hn1, hnN⟩ := mem_Icc.mp hn
    have hchar_one : ∀ m : ℕ, m ≠ 0 → m ≤ N + 1 → ω.gaugeChar m = 1 := by
      intro m hm0 hmN
      rw [ω.gaugeChar_of_ne_zero hm0]
      unfold Finsupp.prod
      refine Finset.prod_eq_one fun p hp_mem => ?_
      dsimp only
      have hp : p.Prime := Nat.prime_of_mem_primeFactors hp_mem
      have hdvd : p ∣ m := Nat.dvd_of_mem_primeFactors hp_mem
      have hp_le : p ≤ N + 1 := (Nat.le_of_dvd (Nat.pos_of_ne_zero hm0) hdvd).trans hmN
      rw [hprimes p hp_le hp, one_pow]
    unfold succConn
    rw [hchar_one n (by omega) (by omega), hchar_one (n + 1) (by omega) (by omega),
      map_one, one_mul]

/-- **Catalan–Bézout reconstruction at prime `2` (`2 → 3 → 4 = 2²`):**
the product of the two consecutive successor links `succConn ω 2` and `succConn ω 3` equals `ω(2)`
identically for every unitary prime gauge `ω`. -/
theorem catalan_holonomy_two (ω : PrimeGauge) :
    succConn ω 2 * succConn ω 3 = ω.val 2 := by
  have h2 : ω.gaugeChar 2 = ω.val 2 := ω.gaugeChar_prime Nat.prime_two
  have h3 : ω.gaugeChar 3 = ω.val 3 := ω.gaugeChar_prime Nat.prime_three
  have h4 : ω.gaugeChar 4 = ω.val 2 ^ 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ω.gaugeChar_pow 2 2, h2]
  unfold succConn
  rw [h2, h3, h4]
  calc (starRingEnd ℂ (ω.val 2) * ω.val 3) * (starRingEnd ℂ (ω.val 3) * ω.val 2 ^ 2)
      = (ω.val 3 * starRingEnd ℂ (ω.val 3)) * (starRingEnd ℂ (ω.val 2) * ω.val 2) * ω.val 2 := by
          ring
    _ = ω.val 2 := by rw [ω.val_mul_conj 3, ω.conj_mul_val 2]; ring

/-- **Catalan–Bézout reconstruction at prime `3` (`2 → 3 → 4 = 2²`):**
`(succConn ω 2)² * succConn ω 3 = ω(3)` identically for every unitary prime gauge `ω`. -/
theorem catalan_holonomy_three (ω : PrimeGauge) :
    succConn ω 2 ^ 2 * succConn ω 3 = ω.val 3 := by
  have h2 : ω.gaugeChar 2 = ω.val 2 := ω.gaugeChar_prime Nat.prime_two
  have h3 : ω.gaugeChar 3 = ω.val 3 := ω.gaugeChar_prime Nat.prime_three
  have h4 : ω.gaugeChar 4 = ω.val 2 ^ 2 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ω.gaugeChar_pow 2 2, h2]
  unfold succConn
  rw [h2, h3, h4]
  calc (starRingEnd ℂ (ω.val 2) * ω.val 3) ^ 2 * (starRingEnd ℂ (ω.val 3) * ω.val 2 ^ 2)
      = (starRingEnd ℂ (ω.val 2) * ω.val 2) ^ 2 * (starRingEnd ℂ (ω.val 3) * ω.val 3) *
          ω.val 3 := by ring
    _ = ω.val 3 := by rw [ω.conj_mul_val 2, ω.conj_mul_val 3]; ring

/-- On the Catalan–Bézout link `3 → 4 = 2²`, the Liouville vacuum flips sign (`succConn = -1`)
whereas the Euler vacuum remains `+1`. -/
theorem succConn_liouville_three :
    succConn PrimeGauge.liouvilleGauge 3 = -1 ∧ succConn PrimeGauge.eulerGauge 3 = 1 := by
  refine ⟨?_, succConn_euler (by omega)⟩
  have h3 : PrimeGauge.liouvilleGauge.gaugeChar 3 = -1 := by
    rw [PrimeGauge.gaugeChar_prime _ Nat.prime_three]
    simp [PrimeGauge.liouvilleGauge, Nat.prime_three]
  have h4 : PrimeGauge.liouvilleGauge.gaugeChar 4 = 1 := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, PrimeGauge.gaugeChar_pow,
      PrimeGauge.gaugeChar_prime _ Nat.prime_two]
    simp [PrimeGauge.liouvilleGauge, Nat.prime_two]
  unfold succConn
  rw [h3, h4]
  simp

end GaloisForLFunctions.BiarithmeticGaugeGeometry
