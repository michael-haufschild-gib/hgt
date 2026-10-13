import GaloisForLFunctions.RHTower.JointAncestryMaximalOffLineExclusion
import GaloisForLFunctions.RHTower.JointAncestryLogWeightExpansion
import GaloisForLFunctions.RHTower.RiemannVonMangoldt
import GaloisForLFunctions.RHTower.XiZeroBandFinite

/-!
# Real-amplitude JAS tests detect a maximal off-line zero

For a finite set `P` of primes, a level `σ` and a real amplitude `t ∈ [0, 1]` put
`K_{P,t}(s) = ∏_{p ∈ P} (1 + t p^{−σ} cosh((s − ½) log p))`.
These are the JAS product tests at real test vectors: the Bernoulli factor at a real `z` is
`(1 + z²)(1 + t p^{−σ} cosh((ρ − ½) log p))` with `t = 2z/(1 + z²)`.  On the critical line every
factor is `1 + t p^{−σ} cos(γ log p) > 0`, so every on-line zero contributes positively.

**Theorem** (`not_jasRealPositiveAbove_of_maximal_offLine`).  Suppose a zero `ρ₀` off the critical
line has the largest distance `δ = |Re ρ₀ − ½|` among all zeros, and `δ < σ < 1 + δ`.  Then for every
`X` there are `N > X` and `t ∈ (0, 1]` with
`Re Σ_ρ K_{(X,N],t}(ρ)/(ρ(1−ρ)) < 0`.

So a single real phase detects every attained off-line zero; complex phases are not needed.

Proof.  Among the zeros at distance `δ` choose `ρ* = ½ + δ + iγ` with `|γ|` minimal; `γ ≠ 0` because
`ξ` has no real zeros.  Its kernel is `exp(Σ_p u_p + R)` with
`Σ_p u_p = (t/2)(Σ_p p^{−(σ−δ−iγ)} + Σ_p p^{−(σ+δ+iγ)})`.
By the prime number theorem the first sum is
`T(N) ~ N^{1−s}/((1−s) log N)`, `s = σ − δ − iγ`, whose argument `γ log N − arg(1 − s)` turns with
`N`.  The edge `N` of the prime range thus supplies the zero's own frequency.  Choose `N` with
`T(N)/|T(N)|` close to the direction of `Z = R + i(π − arg w)`, `w = 1/(ρ*(1−ρ*))`, and put
`t = 2|Z|/|T(N)|`.  Then the kernel is close to `e^Z`, and `w e^Z = −|w| e^R`.
* The four zeros `ρ*, ρ̄*, 1 − ρ*, 1 − ρ̄*` contribute the same real part.
* Zeros at distance `δ` and larger height have main terms smaller by the fixed ratio
  `|1 − s|/|1 − s'| < 1`, so for large `R` their kernels are `e^{(1−η)R}`-small against `e^R`.
* Zeros closer to the line have sums `o(Σ_p p^{−(σ−δ)})`, so their kernels tend to `1`.
* Every zero has kernel at most `exp(t Σ_p p^{−(σ−δ)})`, which stays bounded; the weight of the
  zeros outside a large finite set is small.
-/

open Complex Filter
open scoped ComplexConjugate Topology BigOperators

namespace RHTower

noncomputable section

/-! ## The real-amplitude factor -/

/-- The real-amplitude prime factor `1 + t p^{−σ} cosh((s − ½) log p)`. -/
def jasRealFactor (σ t : ℝ) (p : Nat.Primes) (s : ℂ) : ℂ :=
  1 + ((t * Real.exp (-σ * Real.log p) : ℝ) : ℂ) * Complex.cosh ((s - 1 / 2) * (Real.log p : ℂ))

/-- The real-amplitude kernel `K_{P,t}(s) = ∏_{p ∈ P} (1 + t p^{−σ} cosh((s − ½) log p))`. -/
def jasRealKernel (P : Finset Nat.Primes) (σ t : ℝ) (s : ℂ) : ℂ := ∏ p ∈ P, jasRealFactor σ t p s

/-- Positivity of the zero measure against every real-amplitude kernel on primes `p > X`. -/
def JasRealPositiveAbove (X : ℕ) (σ : ℝ) : Prop :=
  ∀ P : Finset Nat.Primes, (∀ p ∈ P, X < (p : ℕ)) → ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    0 ≤ (∑' q : XiZeroCopy, jasRealKernel P σ t (q.1 : ℂ) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re

/-- `u_p = (t/2)(p^{−(σ − (s − ½))} + p^{−(σ + (s − ½))})`. -/
theorem jasRealFactor_sub_one (σ t : ℝ) (p : Nat.Primes) (s : ℂ) :
    jasRealFactor σ t p s - 1 = ((t / 2 : ℝ) : ℂ) *
      (cexp (-((σ : ℂ) - (s - 1 / 2)) * (Real.log p : ℂ)) +
        cexp (-((σ : ℂ) + (s - 1 / 2)) * (Real.log p : ℂ))) := by
  rw [jasRealFactor, add_sub_cancel_left, Complex.cosh, Complex.ofReal_mul, Complex.ofReal_exp,
    Complex.ofReal_mul, Complex.ofReal_neg]
  have e1 : cexp (-((σ : ℂ) - (s - 1 / 2)) * (Real.log p : ℂ)) =
      cexp (-(σ : ℂ) * (Real.log p : ℂ)) * cexp ((s - 1 / 2) * (Real.log p : ℂ)) := by
    rw [← Complex.exp_add]; congr 1; ring
  have e2 : cexp (-((σ : ℂ) + (s - 1 / 2)) * (Real.log p : ℂ)) =
      cexp (-(σ : ℂ) * (Real.log p : ℂ)) * cexp (-((s - 1 / 2) * (Real.log p : ℂ))) := by
    rw [← Complex.exp_add]; congr 1; ring
  rw [e1, e2, Complex.ofReal_div, Complex.ofReal_ofNat]
  ring

theorem norm_cexp_neg_mul_log (s : ℂ) (p : Nat.Primes) :
    ‖cexp (-s * (Real.log p : ℂ))‖ = Real.exp (-s.re * Real.log p) := by
  rw [Complex.norm_exp]
  congr 1
  rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re]
  ring

/-- `‖u_p‖ ≤ t p^{−(σ − |Re s − ½|)}`. -/
theorem norm_jasRealFactor_sub_one_le {σ t : ℝ} (ht : 0 ≤ t) (p : Nat.Primes) (s : ℂ) :
    ‖jasRealFactor σ t p s - 1‖ ≤ t * Real.exp (-(σ - |s.re - 1 / 2|) * Real.log p) := by
  rw [jasRealFactor_sub_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hL := (log_two_le_log_prime p).trans' (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
  have h1 : ‖cexp (-((σ : ℂ) - (s - 1 / 2)) * (Real.log p : ℂ))‖ ≤
      Real.exp (-(σ - |s.re - 1 / 2|) * Real.log p) := by
    rw [norm_cexp_neg_mul_log]
    refine Real.exp_le_exp.mpr ?_
    have : ((σ : ℂ) - (s - 1 / 2)).re = σ - (s.re - 1 / 2) := by simp
    rw [this]
    nlinarith [le_abs_self (s.re - 1 / 2)]
  have h2 : ‖cexp (-((σ : ℂ) + (s - 1 / 2)) * (Real.log p : ℂ))‖ ≤
      Real.exp (-(σ - |s.re - 1 / 2|) * Real.log p) := by
    rw [norm_cexp_neg_mul_log]
    refine Real.exp_le_exp.mpr ?_
    have : ((σ : ℂ) + (s - 1 / 2)).re = σ + (s.re - 1 / 2) := by simp
    rw [this]
    nlinarith [neg_abs_le (s.re - 1 / 2)]
  calc t / 2 * ‖_ + _‖ ≤ t / 2 * (Real.exp (-(σ - |s.re - 1 / 2|) * Real.log p) +
        Real.exp (-(σ - |s.re - 1 / 2|) * Real.log p)) := by
        gcongr; exact (norm_add_le _ _).trans (add_le_add h1 h2)
    _ = _ := by ring

theorem jasRealFactor_conj (σ t : ℝ) (p : Nat.Primes) (s : ℂ) :
    jasRealFactor σ t p (conj s) = conj (jasRealFactor σ t p s) := by
  rw [jasRealFactor, jasRealFactor, map_add, map_one, map_mul, Complex.conj_ofReal,
    ← Complex.cosh_conj, map_mul, map_sub, Complex.conj_ofReal, map_div₀, map_one, map_ofNat]

theorem jasRealFactor_one_sub (σ t : ℝ) (p : Nat.Primes) (s : ℂ) :
    jasRealFactor σ t p (1 - s) = jasRealFactor σ t p s := by
  rw [jasRealFactor, jasRealFactor, ← Complex.cosh_neg]
  congr 3
  ring

/-- The JAS term `K(s)/(s(1−s))` depends on `s − ½` evenly and commutes with conjugation. -/
def jasRealTerm (P : Finset Nat.Primes) (σ t : ℝ) (s : ℂ) : ℂ :=
  jasRealKernel P σ t s / (s * (1 - s))

theorem jasRealTerm_one_sub (P : Finset Nat.Primes) (σ t : ℝ) (s : ℂ) :
    jasRealTerm P σ t (1 - s) = jasRealTerm P σ t s := by
  rw [jasRealTerm, jasRealTerm, jasRealKernel, jasRealKernel,
    Finset.prod_congr rfl fun p _ => jasRealFactor_one_sub σ t p s]
  congr 1
  ring

theorem jasRealTerm_conj (P : Finset Nat.Primes) (σ t : ℝ) (s : ℂ) :
    jasRealTerm P σ t (conj s) = conj (jasRealTerm P σ t s) := by
  rw [jasRealTerm, jasRealTerm, jasRealKernel, jasRealKernel,
    Finset.prod_congr rfl fun p _ => jasRealFactor_conj σ t p s, ← map_prod, map_div₀]
  congr 1
  simp [map_mul, map_sub]

/-- The four zeros `½ ± z, ½ ± z̄` have JAS terms with equal real parts. -/
theorem re_jasRealTerm_eq_of_abs {P : Finset Nat.Primes} {σ t : ℝ} {s s₀ : ℂ}
    (hre : |s.re - 1 / 2| = |s₀.re - 1 / 2|) (him : |s.im| = |s₀.im|) :
    (jasRealTerm P σ t s).re = (jasRealTerm P σ t s₀).re := by
  have hcases : s = s₀ ∨ s = conj s₀ ∨ s = 1 - s₀ ∨ s = 1 - conj s₀ := by
    rcases abs_eq_abs.mp hre with h1 | h1 <;> rcases abs_eq_abs.mp him with h2 | h2
    · left; exact Complex.ext (by linarith) h2
    · right; left; exact Complex.ext (by simp; linarith) (by simp; linarith)
    · right; right; right; exact Complex.ext (by simp; linarith) (by simp; linarith)
    · right; right; left; exact Complex.ext (by simp; linarith) (by simp; linarith)
  rcases hcases with h | h | h | h <;> subst h
  · rfl
  · rw [jasRealTerm_conj, Complex.conj_re]
  · rw [jasRealTerm_one_sub]
  · rw [jasRealTerm_one_sub, jasRealTerm_conj, Complex.conj_re]

/-! ## Prime window sums -/

theorem jasPrimeWindow_eq_sdiff {X N : ℕ} :
    jasPrimeWindow X N = jasPrimesUpTo N \ jasPrimesUpTo X := by
  ext p
  rw [mem_jasPrimeWindow, Finset.mem_sdiff, mem_jasPrimesUpTo, mem_jasPrimesUpTo]
  omega

/-- The window sum `W_{X,N}(s) = Σ_{X < p ≤ N} p^{−s}`. -/
def jasWindowSum (X N : ℕ) (s : ℂ) : ℂ := ∑ p ∈ jasPrimeWindow X N, cexp (-s * (Real.log p : ℂ))

theorem jasWindowSum_eq_sub {X N : ℕ} (hXN : X ≤ N) (s : ℂ) :
    jasWindowSum X N s = (∑ n ∈ Nat.primesLE N, (n : ℂ) ^ (-s)) -
      ∑ n ∈ Nat.primesLE X, (n : ℂ) ^ (-s) := by
  rw [jasWindowSum, jasPrimeWindow_eq_sdiff, Finset.sum_sdiff_eq_sub (jasPrimesUpTo_mono hXN),
    sum_jasPrimesUpTo (fun n : ℕ => cexp (-s * (Real.log n : ℂ))) N,
    sum_jasPrimesUpTo (fun n : ℕ => cexp (-s * (Real.log n : ℂ))) X]
  congr 1 <;> refine Finset.sum_congr rfl fun n hn => ?_ <;>
    exact (natCast_cpow_neg_eq_cexp (Nat.prime_of_mem_primesBelow hn).pos s).symm

/-- The main term `M_s(N) = N^{1−s}/((1−s) log N)`. -/
def jasMainTerm (s : ℂ) (N : ℕ) : ℂ := ((N : ℝ) : ℂ) ^ (1 - s) / ((1 - s) * (Real.log N : ℂ))

/-- The scale `E_α(N) = N^{1−α}/log N`. -/
def jasMainScale (α : ℝ) (N : ℕ) : ℝ := (N : ℝ) ^ (1 - α) / Real.log N

theorem tendsto_natLog_div_rpow_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun N : ℕ => Real.log N / (N : ℝ) ^ c) atTop (𝓝 0) :=
  (tendsto_log_div_rpow_atTop hc).comp tendsto_natCast_atTop_atTop

/-- **Window sums follow their main terms.**  For `0 < Re s < 1`,
`‖W_{X,N}(s) − M_s(N)‖ = o(N^{1−Re s}/log N)`. -/
theorem tendsto_jasWindowSum_sub_main (X : ℕ) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) :
    Tendsto (fun N : ℕ => ‖jasWindowSum X N s - jasMainTerm s N‖ * Real.log N /
      (N : ℝ) ^ (1 - s.re)) atTop (𝓝 0) := by
  have hA := tendsto_sum_primesLE_cpow_sub_main h0 h1
  set H : ℂ := ∑ n ∈ Nat.primesLE X, (n : ℂ) ^ (-s) with hH
  have hB : Tendsto (fun N : ℕ => ‖H‖ * (Real.log N / (N : ℝ) ^ (1 - s.re))) atTop (𝓝 0) := by
    simpa using (tendsto_natLog_div_rpow_atTop (show 0 < 1 - s.re by linarith)).const_mul ‖H‖
  have hAB := hA.add hB
  rw [zero_add] at hAB
  refine squeeze_zero' (Eventually.of_forall fun N => by positivity) ?_ hAB
  filter_upwards [eventually_ge_atTop X, eventually_ge_atTop 2] with N hN hN2
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hpow : 0 < (N : ℝ) ^ (1 - s.re) := Real.rpow_pos_of_pos (by exact_mod_cast (show 0 < N by omega)) _
  rw [jasWindowSum_eq_sub hN, ← hH]
  have e : (∑ n ∈ Nat.primesLE N, (n : ℂ) ^ (-s)) - H - jasMainTerm s N =
      ((∑ n ∈ Nat.primesLE N, (n : ℂ) ^ (-s)) - ((N : ℝ) : ℂ) ^ (1 - s) /
        ((1 - s) * (Real.log N : ℂ))) - H := by rw [jasMainTerm]; ring
  rw [e]
  calc ‖_ - H‖ * Real.log N / (N : ℝ) ^ (1 - s.re)
      ≤ (‖(∑ n ∈ Nat.primesLE N, (n : ℂ) ^ (-s)) - ((N : ℝ) : ℂ) ^ (1 - s) /
          ((1 - s) * (Real.log N : ℂ))‖ + ‖H‖) * Real.log N / (N : ℝ) ^ (1 - s.re) := by
        gcongr; exact norm_sub_le _ _
    _ = _ := by rw [add_mul, add_div, mul_div_assoc ‖H‖]

/-! ## The edge phase -/

/-- **The edge of the prime range supplies every phase.**  For `γ ≠ 0` the unimodular numbers
`e^{iγ log N}` come arbitrarily close to any unimodular `v` for arbitrarily large `N`. -/
theorem frequently_cexp_log_near {γ : ℝ} (hγ : γ ≠ 0) {v : ℂ} (hv : ‖v‖ = 1) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ᶠ N : ℕ in atTop, ‖cexp (((γ * Real.log N : ℝ) : ℂ) * I) - v‖ < ε := by
  rw [Filter.frequently_atTop]
  intro N₀
  have hγ0 : 0 < |γ| := abs_pos.mpr hγ
  set m : ℝ := 2 * Real.pi / |γ| with hm
  have hm0 : 0 < m := by positivity
  set x₁ : ℝ := v.arg / γ with hx₁
  set x₀ : ℝ := max (Real.log (N₀ + 1)) (Real.log (|γ| / ε)) + 1 with hx₀
  obtain ⟨j, hj⟩ : ∃ j : ℕ, x₀ ≤ x₁ + m * j := by
    obtain ⟨j, hj⟩ := exists_nat_ge ((x₀ - x₁) / m)
    refine ⟨j, ?_⟩
    rw [div_le_iff₀ hm0] at hj
    linarith
  set x : ℝ := x₁ + m * j with hx
  have hγx : γ * x = v.arg + (if 0 < γ then 1 else -1) * (2 * Real.pi * j) := by
    rw [hx, hx₁, hm, mul_add, mul_div_cancel₀ _ hγ]
    split_ifs with hpos
    · rw [abs_of_pos hpos]; field_simp
    · rw [abs_of_neg (lt_of_le_of_ne (not_lt.mp hpos) hγ)]; field_simp
  have hexp : cexp (((γ * x : ℝ) : ℂ) * I) = v := by
    rw [hγx]
    have : cexp (((v.arg + (if 0 < γ then 1 else -1) * (2 * Real.pi * j) : ℝ) : ℂ) * I) =
        cexp ((v.arg : ℂ) * I) := by
      split_ifs
      · rw [show (((v.arg + 1 * (2 * Real.pi * j) : ℝ) : ℂ) * I) =
          (v.arg : ℂ) * I + ((j : ℤ) : ℂ) * (2 * Real.pi * I) by push_cast; ring,
          Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
      · rw [show (((v.arg + -1 * (2 * Real.pi * j) : ℝ) : ℂ) * I) =
          (v.arg : ℂ) * I + ((-(j : ℤ) : ℤ) : ℂ) * (2 * Real.pi * I) by push_cast; ring,
          Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [this]
    have h := Complex.norm_mul_exp_arg_mul_I v
    rw [hv, Complex.ofReal_one, one_mul] at h
    exact h
  have hxx0 : x₀ ≤ x := hj
  have hxpos : 0 < x := by
    have : 0 ≤ Real.log (N₀ + 1) := Real.log_nonneg (by linarith [(N₀.cast_nonneg : (0 : ℝ) ≤ N₀)])
    have := le_max_left (Real.log (N₀ + 1)) (Real.log (|γ| / ε))
    linarith
  set N : ℕ := ⌈Real.exp x⌉₊ with hN
  have hNx : Real.exp x ≤ N := Nat.le_ceil _
  have hNx1 : (N : ℝ) < Real.exp x + 1 := Nat.ceil_lt_add_one (Real.exp_pos x).le
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos x) hNx
  refine ⟨N, ?_, ?_⟩
  · have h1 : Real.log (N₀ + 1) + 1 ≤ x := by
      have := le_max_left (Real.log (N₀ + 1)) (Real.log (|γ| / ε)); linarith
    have h2 : (N₀ : ℝ) + 1 ≤ Real.exp x := by
      calc (N₀ : ℝ) + 1 = Real.exp (Real.log (N₀ + 1)) :=
            (Real.exp_log (by positivity)).symm
        _ ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
    exact_mod_cast (show (N₀ : ℝ) ≤ N by linarith)
  · have hlogN1 : x ≤ Real.log N := by
      rw [← Real.log_exp x]; exact Real.log_le_log (Real.exp_pos x) hNx
    have hlogN2 : Real.log N ≤ x + Real.exp (-x) := by
      have : Real.log N ≤ Real.log (Real.exp x + 1) := Real.log_le_log hN0 hNx1.le
      have e : Real.log (Real.exp x + 1) = x + Real.log (1 + Real.exp (-x)) := by
        rw [← Real.log_exp x, ← Real.log_mul (Real.exp_pos x).ne' (by positivity), Real.log_exp,
          mul_add, mul_one, ← Real.exp_add, add_neg_cancel, Real.exp_zero]
      have h3 : Real.log (1 + Real.exp (-x)) ≤ Real.exp (-x) := by
        have := Real.log_le_sub_one_of_pos (show 0 < 1 + Real.exp (-x) by positivity)
        linarith
      linarith
    have hdiff : |Real.log N - x| ≤ Real.exp (-x) := by
      rw [abs_le]; constructor <;> linarith [Real.exp_pos (-x)]
    have hsmall : |γ| * Real.exp (-x) < ε := by
      have h1 : Real.log (|γ| / ε) + 1 ≤ x := by
        have := le_max_right (Real.log (N₀ + 1)) (Real.log (|γ| / ε)); linarith
      have h2 : Real.exp (-x) < ε / |γ| := by
        calc Real.exp (-x) ≤ Real.exp (-(Real.log (|γ| / ε) + 1)) := Real.exp_le_exp.mpr (by linarith)
          _ < Real.exp (-Real.log (|γ| / ε)) := Real.exp_lt_exp.mpr (by linarith)
          _ = ε / |γ| := by rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
      calc |γ| * Real.exp (-x) < |γ| * (ε / |γ|) := mul_lt_mul_of_pos_left h2 hγ0
        _ = ε := by field_simp
    rw [← hexp]
    have e : cexp (((γ * Real.log N : ℝ) : ℂ) * I) - cexp (((γ * x : ℝ) : ℂ) * I) =
        cexp (((γ * x : ℝ) : ℂ) * I) * (cexp (I * ((γ * (Real.log N - x) : ℝ) : ℂ)) - 1) := by
      rw [mul_sub, mul_one, ← Complex.exp_add]
      congr 2
      push_cast; ring
    rw [e, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul]
    refine lt_of_le_of_lt Real.norm_exp_I_mul_ofReal_sub_one_le ?_
    rw [Real.norm_eq_abs, abs_mul]
    exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hdiff (abs_nonneg γ)) hsmall

/-! ## Kernel bounds -/

/-- The sum `W_P(z) = Σ_{p ∈ P} p^{−z}`. -/
def jasCpowSum (P : Finset Nat.Primes) (z : ℂ) : ℂ := ∑ p ∈ P, cexp (-z * (Real.log p : ℂ))

theorem jasWindowSum_eq_jasCpowSum (X N : ℕ) (z : ℂ) :
    jasWindowSum X N z = jasCpowSum (jasPrimeWindow X N) z := rfl

theorem norm_jasCpowSum_le (P : Finset Nat.Primes) (z : ℂ) :
    ‖jasCpowSum P z‖ ≤ ∑ p ∈ P, Real.exp (-z.re * Real.log p) := by
  refine (norm_sum_le _ _).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun p _ => norm_cexp_neg_mul_log z p

theorem jasCpowSum_conj (P : Finset Nat.Primes) (z : ℂ) :
    jasCpowSum P (conj z) = conj (jasCpowSum P z) := by
  rw [jasCpowSum, jasCpowSum, map_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [← Complex.exp_conj, map_mul, map_neg, Complex.conj_ofReal]

theorem norm_jasCpowSum_conj (P : Finset Nat.Primes) (z : ℂ) :
    ‖jasCpowSum P (conj z)‖ = ‖jasCpowSum P z‖ := by
  rw [jasCpowSum_conj, Complex.norm_conj]

/-- `Σ_p u_p = (t/2)(W(σ − (s − ½)) + W(σ + (s − ½)))`. -/
theorem sum_jasRealFactor_sub_one (P : Finset Nat.Primes) (σ t : ℝ) (s : ℂ) :
    ∑ p ∈ P, (jasRealFactor σ t p s - 1) = ((t / 2 : ℝ) : ℂ) *
      (jasCpowSum P ((σ : ℂ) - (s - 1 / 2)) + jasCpowSum P ((σ : ℂ) + (s - 1 / 2))) := by
  simp_rw [jasRealFactor_sub_one]
  rw [← Finset.mul_sum, Finset.sum_add_distrib, jasCpowSum, jasCpowSum]

theorem norm_jasRealKernel_le_exp (P : Finset Nat.Primes) (σ t : ℝ) (s : ℂ) :
    ‖jasRealKernel P σ t s‖ ≤ Real.exp (∑ p ∈ P, ‖jasRealFactor σ t p s - 1‖) := by
  rw [jasRealKernel, norm_prod, Real.exp_sum]
  refine Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p _ => ?_
  calc ‖jasRealFactor σ t p s‖ = ‖1 + (jasRealFactor σ t p s - 1)‖ := by ring_nf
    _ ≤ 1 + ‖jasRealFactor σ t p s - 1‖ := by
        refine (norm_add_le _ _).trans ?_; rw [norm_one]
    _ ≤ Real.exp ‖jasRealFactor σ t p s - 1‖ := by
        linarith [Real.add_one_le_exp ‖jasRealFactor σ t p s - 1‖]

/-- With every `‖u_p‖ ≤ ½`, the kernel is `exp(Σ u_p + R)` with `‖R‖ ≤ Σ ‖u_p‖²`. -/
theorem exists_jasRealKernel_eq_exp (P : Finset Nat.Primes) (σ t : ℝ) (s : ℂ)
    (h : ∀ p ∈ P, ‖jasRealFactor σ t p s - 1‖ ≤ 1 / 2) :
    ∃ R : ℂ, ‖R‖ ≤ ∑ p ∈ P, ‖jasRealFactor σ t p s - 1‖ ^ 2 ∧
      jasRealKernel P σ t s = cexp (∑ p ∈ P, (jasRealFactor σ t p s - 1) + R) := by
  obtain ⟨R, hR, he⟩ := exists_prod_one_add_eq_exp P (fun p => jasRealFactor σ t p s - 1) h
  refine ⟨R, hR, ?_⟩
  rw [← he, jasRealKernel]
  exact Finset.prod_congr rfl fun p _ => by ring

/-- `Σ_{X < p ≤ N} p^{−β} ≤ S_β(N)`. -/
theorem sum_jasPrimeWindow_le_jasPrimeRpowSum (X N : ℕ) (β : ℝ) :
    ∑ p ∈ jasPrimeWindow X N, Real.exp (-β * Real.log p) ≤ jasPrimeRpowSum β N := by
  refine Finset.sum_le_sum_of_subset_of_nonneg (fun p hp => ?_) fun _ _ _ => (Real.exp_pos _).le
  rw [mem_jasPrimeWindow] at hp
  exact mem_jasPrimesUpTo.mpr hp.2

theorem exp_neg_mul_log_prime_le_one {β : ℝ} (hβ : 0 ≤ β) (p : Nat.Primes) :
    Real.exp (-β * Real.log p) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  have := (Real.log_pos (by exact_mod_cast p.2.one_lt : (1 : ℝ) < (p : ℕ))).le
  nlinarith

theorem exp_neg_mul_log_prime_anti {β β' : ℝ} (h : β ≤ β') (p : Nat.Primes) :
    Real.exp (-β' * Real.log p) ≤ Real.exp (-β * Real.log p) := by
  refine Real.exp_le_exp.mpr ?_
  have := (Real.log_pos (by exact_mod_cast p.2.one_lt : (1 : ℝ) < (p : ℕ))).le
  nlinarith

/-! ## Main terms -/

theorem jasMainScale_pos {α : ℝ} {N : ℕ} (hN : 2 ≤ N) : 0 < jasMainScale α N := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  exact div_pos (Real.rpow_pos_of_pos (by linarith) _) (Real.log_pos hN1)

/-- `M_s(N) = E_α(N) e^{iγ log N}/(1 − s)` for `s = α − iγ`. -/
theorem jasMainTerm_eq (α γ : ℝ) {N : ℕ} (hN : 0 < N) :
    jasMainTerm ((α : ℂ) - (γ : ℂ) * I) N =
      ((jasMainScale α N : ℝ) : ℂ) * cexp (((γ * Real.log N : ℝ) : ℂ) * I) /
        (1 - ((α : ℂ) - (γ : ℂ) * I)) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hcpow : ((N : ℝ) : ℂ) ^ (1 - ((α : ℂ) - (γ : ℂ) * I)) =
      (((N : ℝ) ^ (1 - α) : ℝ) : ℂ) * cexp (((γ * Real.log N : ℝ) : ℂ) * I) := by
    rw [show (1 : ℂ) - ((α : ℂ) - (γ : ℂ) * I) = ((1 - α : ℝ) : ℂ) + ((γ : ℂ) * I) by
      push_cast; ring, Complex.cpow_add _ _ (by exact_mod_cast hNr.ne'),
      ← Complex.ofReal_cpow hNr.le, Complex.cpow_def_of_ne_zero (by exact_mod_cast hNr.ne'),
      ← Complex.ofReal_log hNr.le]
    congr 2
    push_cast; ring
  rw [jasMainTerm, hcpow, jasMainScale]
  push_cast
  field_simp

theorem norm_one_sub_alpha_sub (α γ : ℝ) :
    ‖1 - ((α : ℂ) - (γ : ℂ) * I)‖ = Real.sqrt ((1 - α) ^ 2 + γ ^ 2) := by
  rw [Complex.norm_eq_sqrt_sq_add_sq]
  congr 1
  simp only [Complex.sub_re, Complex.one_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
    Complex.ofReal_im, Complex.I_im, Complex.sub_im, Complex.one_im, Complex.mul_im]
  ring

/-- Window sums are eventually within `ε E_α(N)` of their main terms. -/
theorem eventually_norm_jasWindowSum_sub_main_le (X : ℕ) {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, ‖jasWindowSum X N s - jasMainTerm s N‖ ≤ ε * jasMainScale s.re N := by
  filter_upwards [(tendsto_jasWindowSum_sub_main X h0 h1).eventually (gt_mem_nhds hε),
    eventually_ge_atTop 2] with N hN hN2
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog := Real.log_pos hN1
  have hpow : 0 < (N : ℝ) ^ (1 - s.re) := Real.rpow_pos_of_pos (by linarith) _
  rw [jasMainScale]
  rw [mul_div_assoc', le_div_iff₀ hlog]
  rw [div_lt_iff₀ hpow] at hN
  linarith

/-- `S_α(N) ≤ (1/(1 − α) + ε) E_α(N)` eventually, for `0 < α < 1`. -/
theorem eventually_jasPrimeRpowSum_le_main {α : ℝ} (h0 : 0 < α) (h1 : α < 1) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop, jasPrimeRpowSum α N ≤ (1 / (1 - α) + ε) * jasMainScale α N := by
  have hA := tendsto_sum_primesLE_cpow_sub_main (s := (α : ℂ)) (by simpa using h0)
    (by simpa using h1)
  simp only [Complex.ofReal_re] at hA
  filter_upwards [hA.eventually (gt_mem_nhds hε), eventually_ge_atTop 2] with N hN hN2
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog := Real.log_pos hN1
  have hpow : 0 < (N : ℝ) ^ (1 - α) := Real.rpow_pos_of_pos (by linarith) _
  have h1α : 0 < 1 - α := by linarith
  have hS : ((jasPrimeRpowSum α N : ℝ) : ℂ) = ∑ n ∈ Nat.primesLE N, (n : ℂ) ^ (-(α : ℂ)) := by
    rw [jasPrimeRpowSum, Complex.ofReal_sum,
      sum_jasPrimesUpTo (fun n : ℕ => ((Real.exp (-α * Real.log n) : ℝ) : ℂ)) N]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [natCast_cpow_neg_eq_cexp (Nat.prime_of_mem_primesBelow hn).pos, Complex.ofReal_exp]
    push_cast; ring_nf
  have hM : ‖((N : ℝ) : ℂ) ^ (1 - (α : ℂ)) / ((1 - (α : ℂ)) * (Real.log N : ℂ))‖ =
      jasMainScale α N / (1 - α) := by
    rw [show (1 : ℂ) - (α : ℂ) = ((1 - α : ℝ) : ℂ) by push_cast; ring,
      ← Complex.ofReal_cpow (by positivity), ← Complex.ofReal_mul, ← Complex.ofReal_div,
      Complex.norm_real, Real.norm_of_nonneg (by positivity),
      jasMainScale]
    field_simp
  rw [div_lt_iff₀ hpow] at hN
  have herr : ‖((jasPrimeRpowSum α N : ℝ) : ℂ) - ((N : ℝ) : ℂ) ^ (1 - (α : ℂ)) /
      ((1 - (α : ℂ)) * (Real.log N : ℂ))‖ ≤ ε * jasMainScale α N := by
    rw [hS, jasMainScale, mul_div_assoc', le_div_iff₀ hlog]
    linarith
  have := norm_le_insert' ((jasPrimeRpowSum α N : ℝ) : ℂ)
    (((N : ℝ) : ℂ) ^ (1 - (α : ℂ)) / ((1 - (α : ℂ)) * (Real.log N : ℂ)))
  rw [Complex.norm_real, Real.norm_of_nonneg (jasPrimeRpowSum_nonneg _ _), hM] at this
  have e : (1 / (1 - α) + ε) * jasMainScale α N = jasMainScale α N / (1 - α) +
      ε * jasMainScale α N := by ring
  rw [e]
  linarith

/-! ## The dominant term -/

/-- `Re(w e^{R + i(π − arg w) + e}) ≤ −|w| e^R/2` when `‖e‖ ≤ 1/4`. -/
theorem re_mul_cexp_antiAligned_le {w : ℂ} (R : ℝ) {e : ℂ} (he : ‖e‖ ≤ 1 / 4) :
    (w * cexp ((R : ℂ) + ((Real.pi - w.arg : ℝ) : ℂ) * I + e)).re ≤ -(‖w‖ * Real.exp R) / 2 := by
  have halign : w * cexp ((R : ℂ) + ((Real.pi - w.arg : ℝ) : ℂ) * I) =
      -(((‖w‖ * Real.exp R : ℝ)) : ℂ) := by
    nth_rw 1 [← Complex.norm_mul_exp_arg_mul_I w]
    rw [show (R : ℂ) + ((Real.pi - w.arg : ℝ) : ℂ) * I = (R : ℂ) + ((Real.pi : ℂ) * I - (w.arg : ℂ) * I)
      by push_cast; ring, Complex.exp_add, Complex.exp_sub, Complex.exp_pi_mul_I, ← Complex.ofReal_exp]
    have hne : cexp ((w.arg : ℂ) * I) ≠ 0 := Complex.exp_ne_zero _
    push_cast
    field_simp
  rw [Complex.exp_add, ← mul_assoc, halign]
  have h1 : ‖cexp e - 1‖ ≤ 1 / 2 := by
    have := Complex.norm_exp_sub_one_le (show ‖e‖ ≤ 1 by linarith)
    linarith
  have h2 : 1 / 2 ≤ (cexp e).re := by
    have := Complex.abs_re_le_norm (cexp e - 1)
    rw [Complex.sub_re, Complex.one_re] at this
    linarith [abs_le.mp (this.trans h1)]
  have hpos : 0 ≤ ‖w‖ * Real.exp R := by positivity
  rw [neg_mul, Complex.neg_re, Complex.re_ofReal_mul]
  nlinarith

/-- The big/small split of a zero at distance `δ` from the critical line. -/
theorem norm_jasCpowSum_pair_le (P : Finset Nat.Primes) {σ δ : ℝ} {q : ℂ}
    (hd : |q.re - 1 / 2| = δ) :
    ‖jasCpowSum P ((σ : ℂ) - (q - 1 / 2))‖ + ‖jasCpowSum P ((σ : ℂ) + (q - 1 / 2))‖ ≤
      ‖jasCpowSum P (((σ - δ : ℝ) : ℂ) - ((|q.im| : ℝ) : ℂ) * I)‖ +
        ∑ p ∈ P, Real.exp (-(σ + δ) * Real.log p) := by
  set s : ℂ := ((σ - δ : ℝ) : ℂ) - ((|q.im| : ℝ) : ℂ) * I with hs
  have hbound : ∀ z : ℂ, z.re = σ + δ → ‖jasCpowSum P z‖ ≤ ∑ p ∈ P, Real.exp (-(σ + δ) * Real.log p) :=
    fun z hz => (norm_jasCpowSum_le P z).trans (le_of_eq (by rw [hz]))
  have hbig : ∀ z : ℂ, z.re = σ - δ → |z.im| = |q.im| → ‖jasCpowSum P z‖ = ‖jasCpowSum P s‖ := by
    intro z hzr hzi
    rcases abs_eq_abs.mp hzi with h | h
    · rcases le_or_gt 0 q.im with hq | hq
      · have : z = conj s := Complex.ext (by simp [hs, hzr]) (by simp [hs, h, abs_of_nonneg hq])
        rw [this, norm_jasCpowSum_conj]
      · have : z = s := Complex.ext (by simp [hs, hzr]) (by simp [hs, h, abs_of_neg hq])
        rw [this]
    · rcases le_or_gt 0 q.im with hq | hq
      · have : z = s := Complex.ext (by simp [hs, hzr]) (by simp [hs, h, abs_of_nonneg hq])
        rw [this]
      · have : z = conj s := Complex.ext (by simp [hs, hzr]) (by simp [hs, h, abs_of_neg hq])
        rw [this, norm_jasCpowSum_conj]
  have hδ0 : 0 ≤ δ := hd ▸ abs_nonneg _
  rcases (abs_eq hδ0).mp hd with h | h
  · -- `Re q − ½ = δ`
    have e1 := hbig ((σ : ℂ) - (q - 1 / 2)) (by simp; linarith) (by simp [abs_neg])
    have e2 := hbound ((σ : ℂ) + (q - 1 / 2)) (by simp; linarith)
    linarith
  · -- `Re q − ½ = −δ`
    have e1 := hbig ((σ : ℂ) + (q - 1 / 2)) (by simp; linarith) (by simp)
    have e2 := hbound ((σ : ℂ) - (q - 1 / 2)) (by simp; linarith)
    linarith

/-! ## A normalized maximal zero -/

theorem xiZeroCopyConjEquiv_val (q : XiZeroCopy) :
    ((xiZeroCopyConjEquiv q).1 : ℂ) = conj (q.1 : ℂ) := rfl

theorem xiZeroCopyReflectEquiv_val (q : XiZeroCopy) :
    ((xiZeroCopyReflectEquiv q).1 : ℂ) = 1 - (q.1 : ℂ) := rfl

/-- **Normalization.**  If `q₀` is off the critical line at distance `δ`, there is a zero
`½ + δ + iγ` with `γ > 0` minimal among the zeros at distance `δ`, and a gap `γ₁ > γ`: every zero at
distance `δ` has `|Im| = γ` or `|Im| ≥ γ₁`. -/
theorem exists_normalized_maximal_zero (q₀ : XiZeroCopy) (hoff : (q₀.1 : ℂ).re ≠ 1 / 2) :
    ∃ (q₁ : XiZeroCopy) (γ γ₁ : ℝ), 0 < γ ∧ γ < γ₁ ∧
      (q₁.1 : ℂ) = 1 / 2 + ((|(q₀.1 : ℂ).re - 1 / 2| : ℝ) : ℂ) + (γ : ℂ) * I ∧
      (∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| = |(q₀.1 : ℂ).re - 1 / 2| →
        |(q.1 : ℂ).im| = γ ∨ γ₁ ≤ |(q.1 : ℂ).im|) := by
  classical
  set δ := |(q₀.1 : ℂ).re - 1 / 2| with hδ
  have hδ0 : 0 < δ := abs_pos.mpr (sub_ne_zero.mpr hoff)
  set K := |(q₀.1 : ℂ).im| with hK
  have hfin : {q : XiZeroCopy | |(q.1 : ℂ).im - 0| ≤ K}.Finite :=
    finite_xiZeroCopy_band 0 (abs_nonneg _)
  set S := hfin.toFinset.filter (fun q => |(q.1 : ℂ).re - 1 / 2| = δ) with hS
  have hmemS : ∀ q : XiZeroCopy, q ∈ S ↔ |(q.1 : ℂ).im| ≤ K ∧ |(q.1 : ℂ).re - 1 / 2| = δ := by
    intro q; rw [hS, Finset.mem_filter, Set.Finite.mem_toFinset]; simp
  have hq₀S : q₀ ∈ S := (hmemS q₀).mpr ⟨le_rfl, rfl⟩
  obtain ⟨qm, hqmS, hqm⟩ := S.exists_min_image (fun q => |(q.1 : ℂ).im|) ⟨q₀, hq₀S⟩
  set γ := |(qm.1 : ℂ).im| with hγ
  have hqmd : |(qm.1 : ℂ).re - 1 / 2| = δ := ((hmemS qm).mp hqmS).2
  have hγ0 : 0 < γ := abs_pos.mpr (xiSupport_im_ne_zero qm.1)
  have hmin : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| = δ → γ ≤ |(q.1 : ℂ).im| := by
    intro q hq
    by_cases hqK : |(q.1 : ℂ).im| ≤ K
    · exact hqm q ((hmemS q).mpr ⟨hqK, hq⟩)
    · have := hqm q₀ hq₀S
      linarith [not_le.mp hqK]
  have hfin2 : {q : XiZeroCopy | |(q.1 : ℂ).im - 0| ≤ γ + 1}.Finite :=
    finite_xiZeroCopy_band 0 (by linarith)
  set T := hfin2.toFinset.filter
    (fun q => |(q.1 : ℂ).re - 1 / 2| = δ ∧ |(q.1 : ℂ).im| ≠ γ) with hT
  have hmemT : ∀ q : XiZeroCopy, q ∈ T ↔
      |(q.1 : ℂ).im| ≤ γ + 1 ∧ (|(q.1 : ℂ).re - 1 / 2| = δ ∧ |(q.1 : ℂ).im| ≠ γ) := by
    intro q; rw [hT, Finset.mem_filter, Set.Finite.mem_toFinset]; simp
  obtain ⟨γ₁, hγγ₁, hγ₁⟩ : ∃ γ₁ : ℝ, γ < γ₁ ∧ γ₁ ≤ γ + 1 ∧ ∀ q ∈ T, γ₁ ≤ |(q.1 : ℂ).im| := by
    by_cases hTn : T.Nonempty
    · obtain ⟨qt, hqtT, hqt⟩ := T.exists_min_image (fun q => |(q.1 : ℂ).im|) hTn
      obtain ⟨_, hqtd, hqtne⟩ := (hmemT qt).mp hqtT
      refine ⟨min (γ + 1) |(qt.1 : ℂ).im|, lt_min (by linarith)
        (lt_of_le_of_ne (hmin qt hqtd) (Ne.symm hqtne)), min_le_left _ _, fun q hq => ?_⟩
      exact (min_le_right _ _).trans (hqt q hq)
    · refine ⟨γ + 1, by linarith, le_rfl, fun q hq => absurd ⟨q, hq⟩ hTn⟩
  have hdich : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| = δ →
      |(q.1 : ℂ).im| = γ ∨ γ₁ ≤ |(q.1 : ℂ).im| := by
    intro q hq
    by_cases hqγ : |(q.1 : ℂ).im| = γ
    · exact Or.inl hqγ
    · right
      by_cases hq1 : |(q.1 : ℂ).im| ≤ γ + 1
      · exact hγ₁.2 q ((hmemT q).mpr ⟨hq1, hq, hqγ⟩)
      · linarith [not_le.mp hq1, hγ₁.1]
  -- move the minimal zero to `Re > ½`, `Im > 0`
  obtain ⟨q₂, hq₂re, hq₂im⟩ : ∃ q₂ : XiZeroCopy, (q₂.1 : ℂ).re - 1 / 2 = δ ∧
      |(q₂.1 : ℂ).im| = γ := by
    rcases (abs_eq hδ0.le).mp hqmd with h | h
    · exact ⟨qm, h, rfl⟩
    · refine ⟨xiZeroCopyReflectEquiv qm, ?_, ?_⟩
      · rw [xiZeroCopyReflectEquiv_val, Complex.sub_re, Complex.one_re]; linarith
      · rw [xiZeroCopyReflectEquiv_val, Complex.sub_im, Complex.one_im, zero_sub, abs_neg]
  obtain ⟨q₁, hq₁re, hq₁im⟩ : ∃ q₁ : XiZeroCopy, (q₁.1 : ℂ).re - 1 / 2 = δ ∧
      (q₁.1 : ℂ).im = γ := by
    rcases (abs_eq hγ0.le).mp hq₂im with h | h
    · exact ⟨q₂, hq₂re, h⟩
    · refine ⟨xiZeroCopyConjEquiv q₂, ?_, ?_⟩
      · rw [xiZeroCopyConjEquiv_val, Complex.conj_re]; exact hq₂re
      · rw [xiZeroCopyConjEquiv_val, Complex.conj_im, h, neg_neg]
  refine ⟨q₁, γ, γ₁, hγ0, hγγ₁, ?_, hdich⟩
  apply Complex.ext
  · simp; linarith
  · simp [hq₁im]

/-! ## The detection theorem -/

theorem norm_jasMainTerm_eq (α t : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    ‖jasMainTerm ((α : ℂ) - (t : ℂ) * I) N‖ =
      jasMainScale α N / Real.sqrt ((1 - α) ^ 2 + t ^ 2) := by
  rw [jasMainTerm_eq α t (by omega), norm_div, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one,
    Complex.norm_real, Real.norm_of_nonneg (jasMainScale_pos hN).le, norm_one_sub_alpha_sub]

/-- A large exponent beats a fixed linear budget: there is `R > 0` with
`16 W (2 + e^{(R + 2π)ρ + 1}) ≤ c e^R`, for `ρ < 1`, `c > 0`. -/
theorem exists_large_exponent {W c ρ : ℝ} (hc : 0 < c) (hρ : ρ < 1) :
    ∃ R : ℝ, 0 < R ∧ 16 * W * (2 + Real.exp ((R + 2 * Real.pi) * ρ + 1)) ≤ c * Real.exp R := by
  have hc' : 0 < 1 - ρ := by linarith
  have h1 := (Real.tendsto_exp_neg_atTop_nhds_zero).const_mul (32 * W)
  have h2 := ((Real.tendsto_exp_neg_atTop_nhds_zero).comp
    (tendsto_id.const_mul_atTop hc')).const_mul (16 * W * Real.exp (2 * Real.pi * ρ + 1))
  have ht := h1.add h2
  rw [mul_zero, mul_zero, add_zero] at ht
  obtain ⟨R, hR, hR1⟩ := ((ht.eventually (ge_mem_nhds hc)).and
    (eventually_ge_atTop (1 : ℝ))).exists
  refine ⟨R, by linarith, ?_⟩
  simp only [Function.comp, id] at hR
  have e1 : Real.exp ((R + 2 * Real.pi) * ρ + 1) =
      Real.exp R * (Real.exp (2 * Real.pi * ρ + 1) * Real.exp (-((1 - ρ) * R))) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  have e2 : Real.exp R * Real.exp (-R) = 1 := by
    rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  calc 16 * W * (2 + Real.exp ((R + 2 * Real.pi) * ρ + 1))
      = Real.exp R * (32 * W * Real.exp (-R) + 16 * W * Real.exp (2 * Real.pi * ρ + 1) *
          Real.exp (-((1 - ρ) * R))) := by rw [e1]; linear_combination (-32 * W) * e2
    _ ≤ Real.exp R * c := by gcongr
    _ = c * Real.exp R := mul_comm _ _

/-- **The main-term approximation.**  With `a = 2ν m₀/E`, `M = E e^{iγ log N}/(1 − s)`,
`m₀ = ‖1 − s‖` and `v = u(1 − s)/m₀`:
`‖(a/2) W − ν u‖ ≤ ν m₀ ‖W − M‖/E + ν ‖e^{iγ log N} − v‖`. -/
theorem norm_half_amp_mul_sub_le {W M s u v c : ℂ} {E ν m₀ : ℝ} (hE : 0 < E) (hν : 0 ≤ ν)
    (hm₀ : m₀ = ‖1 - s‖) (hm₀0 : 0 < m₀) (hM : M = (E : ℂ) * c / (1 - s))
    (hv : v = u * ((1 - s) / (m₀ : ℂ))) :
    ‖((2 * ν * m₀ / E / 2 : ℝ) : ℂ) * W - (ν : ℂ) * u‖ ≤
      ν * m₀ * ‖W - M‖ / E + ν * ‖c - v‖ := by
  have h1s : (1 : ℂ) - s ≠ 0 := by intro h; rw [h, norm_zero] at hm₀; linarith
  have hm₀c : (m₀ : ℂ) ≠ 0 := by exact_mod_cast hm₀0.ne'
  have hEc : (E : ℂ) ≠ 0 := by exact_mod_cast hE.ne'
  have hsplit : ((2 * ν * m₀ / E / 2 : ℝ) : ℂ) * W - (ν : ℂ) * u =
      ((ν * m₀ / E : ℝ) : ℂ) * (W - M) + (ν : ℂ) * ((m₀ : ℂ) / (1 - s) * (c - v)) := by
    rw [hM, hv]
    push_cast
    field_simp
    ring
  rw [hsplit]
  have t1 : ‖((ν * m₀ / E : ℝ) : ℂ) * (W - M)‖ = ν * m₀ * ‖W - M‖ / E := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]; ring
  have t2 : ‖(ν : ℂ) * ((m₀ : ℂ) / (1 - s) * (c - v))‖ = ν * ‖c - v‖ := by
    rw [norm_mul, norm_mul, norm_div, Complex.norm_real, Complex.norm_real,
      Real.norm_of_nonneg hm₀0.le, Real.norm_of_nonneg hν, ← hm₀, div_self hm₀0.ne', one_mul]
  exact (norm_add_le _ _).trans (le_of_eq (by rw [t1, t2]))

/-- **The dominant zero.**  If its kernel exponent is within `1/4` of `R + i(π − arg w)`, with
`w = 1/(q(1 − q))`, then its term has real part at most `−|w| e^R/2`. -/
theorem re_jasRealTerm_dominant_le {P : Finset Nat.Primes} {σ a δ R : ℝ} {s₀ q : ℂ}
    (hbig : (σ : ℂ) - (q - 1 / 2) = s₀) (hsmallre : ((σ : ℂ) + (q - 1 / 2)).re = σ + δ)
    (hu : ∀ p ∈ P, ‖jasRealFactor σ a p q - 1‖ ≤ 1 / 2)
    (hR : ∑ p ∈ P, ‖jasRealFactor σ a p q - 1‖ ^ 2 ≤ 1 / 12)
    (hsmall : a / 2 * ∑ p ∈ P, Real.exp (-(σ + δ) * Real.log p) ≤ 1 / 96) (ha : 0 ≤ a)
    (hmain : ‖((a / 2 : ℝ) : ℂ) * jasCpowSum P s₀ -
      ((R : ℂ) + ((Real.pi - (1 / (q * (1 - q))).arg : ℝ) : ℂ) * I)‖ ≤ 1 / 12) :
    (jasRealTerm P σ a q).re ≤ -(‖1 / (q * (1 - q))‖ * Real.exp R) / 2 := by
  obtain ⟨R₁, hR₁, hK₁⟩ := exists_jasRealKernel_eq_exp P σ a q hu
  rw [sum_jasRealFactor_sub_one, hbig] at hK₁
  set Z : ℂ := (R : ℂ) + ((Real.pi - (1 / (q * (1 - q))).arg : ℝ) : ℂ) * I with hZ
  set e : ℂ := ((a / 2 : ℝ) : ℂ) * (jasCpowSum P s₀ + jasCpowSum P ((σ : ℂ) + (q - 1 / 2))) +
    R₁ - Z with he
  have hK : jasRealKernel P σ a q = cexp (Z + e) := by rw [hK₁, he]; ring_nf
  have hsm : ‖((a / 2 : ℝ) : ℂ) * jasCpowSum P ((σ : ℂ) + (q - 1 / 2))‖ ≤ 1 / 96 := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
    refine (mul_le_mul_of_nonneg_left (norm_jasCpowSum_le P _) (by positivity)).trans ?_
    rw [hsmallre]; exact hsmall
  have he_le : ‖e‖ ≤ 1 / 4 := by
    have e2 : e = (((a / 2 : ℝ) : ℂ) * jasCpowSum P s₀ - Z) +
        ((a / 2 : ℝ) : ℂ) * jasCpowSum P ((σ : ℂ) + (q - 1 / 2)) + R₁ := by rw [he]; ring
    rw [e2]
    have h3 := hR₁.trans hR
    calc ‖_ + _ + R₁‖ ≤ ‖((a / 2 : ℝ) : ℂ) * jasCpowSum P s₀ - Z‖ +
          ‖((a / 2 : ℝ) : ℂ) * jasCpowSum P ((σ : ℂ) + (q - 1 / 2))‖ + ‖R₁‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
      _ ≤ 1 / 4 := by linarith
  have ht : jasRealTerm P σ a q = 1 / (q * (1 - q)) * jasRealKernel P σ a q := by
    rw [jasRealTerm]; ring
  rw [ht, hK, hZ]
  exact re_mul_cexp_antiAligned_le R he_le

/-- **A competitor at the same distance.**  If `(t/2)‖W(s_q)‖ ≤ B` for the big exponent and the
other bounds hold, the kernel is at most `e^{B + 1}`. -/
theorem norm_jasRealKernel_sameDepth_le {P : Finset Nat.Primes} {σ a δ B : ℝ} {q : ℂ}
    (hd : |q.re - 1 / 2| = δ) (ha : 0 ≤ a)
    (hu : ∀ p ∈ P, ‖jasRealFactor σ a p q - 1‖ ≤ 1 / 2)
    (hR : ∑ p ∈ P, ‖jasRealFactor σ a p q - 1‖ ^ 2 ≤ 1 / 12)
    (hsmall : a / 2 * ∑ p ∈ P, Real.exp (-(σ + δ) * Real.log p) ≤ 1 / 96)
    (hbigq : a / 2 * ‖jasCpowSum P (((σ - δ : ℝ) : ℂ) - ((|q.im| : ℝ) : ℂ) * I)‖ ≤ B) :
    ‖jasRealKernel P σ a q‖ ≤ Real.exp (B + 1) := by
  obtain ⟨Rq, hRq, hKq⟩ := exists_jasRealKernel_eq_exp P σ a q hu
  rw [hKq, Complex.norm_exp]
  refine Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans ((norm_add_le _ _).trans ?_))
  rw [sum_jasRealFactor_sub_one, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have hpair := norm_jasCpowSum_pair_le P (σ := σ) hd
  have h1 : a / 2 * ‖jasCpowSum P ((σ : ℂ) - (q - 1 / 2)) + jasCpowSum P ((σ : ℂ) + (q - 1 / 2))‖ ≤
      B + 1 / 96 := by
    calc _ ≤ a / 2 * (‖jasCpowSum P ((σ : ℂ) - (q - 1 / 2))‖ +
          ‖jasCpowSum P ((σ : ℂ) + (q - 1 / 2))‖) :=
          mul_le_mul_of_nonneg_left (norm_add_le _ _) (by positivity)
      _ ≤ a / 2 * (‖jasCpowSum P (((σ - δ : ℝ) : ℂ) - ((|q.im| : ℝ) : ℂ) * I)‖ +
          ∑ p ∈ P, Real.exp (-(σ + δ) * Real.log p)) :=
          mul_le_mul_of_nonneg_left hpair (by positivity)
      _ ≤ B + 1 / 96 := by rw [mul_add]; linarith
  linarith [hRq.trans hR]

/-- **A competitor closer to the line** has kernel at most `2`. -/
theorem norm_jasRealKernel_shallow_le {P : Finset Nat.Primes} {σ a : ℝ} {q : ℂ} (ha : 0 ≤ a)
    (h : a * ∑ p ∈ P, Real.exp (-(σ - |q.re - 1 / 2|) * Real.log p) ≤ 1 / 48) :
    ‖jasRealKernel P σ a q‖ ≤ 2 := by
  have hsum : ∑ p ∈ P, ‖jasRealFactor σ a p q - 1‖ ≤
      a * ∑ p ∈ P, Real.exp (-(σ - |q.re - 1 / 2|) * Real.log p) := by
    rw [Finset.mul_sum]; exact Finset.sum_le_sum fun p _ => norm_jasRealFactor_sub_one_le ha p q
  refine (norm_jasRealKernel_le_exp P σ a q).trans ?_
  have h3 : Real.exp (∑ p ∈ P, ‖jasRealFactor σ a p q - 1‖) ≤ Real.exp (1 / 48) :=
    Real.exp_le_exp.mpr (hsum.trans h)
  have h5 : Real.exp (1 / 48 : ℝ) ≤ 2 := by
    calc Real.exp (1 / 48 : ℝ) ≤ Real.exp (Real.log 2) :=
          Real.exp_le_exp.mpr (by linarith [Real.log_two_gt_d9])
      _ = 2 := Real.exp_log (by norm_num)
  linarith

/-- **Assembly.**  A dominant group of equal real parts beats bounded competitors and a light
tail. -/
theorem re_tsum_jasRealTerm_neg {P : Finset Nat.Primes} {σ a : ℝ} (F : Finset XiZeroCopy)
    (D : XiZeroCopy → Prop) [DecidablePred D] (q₁ : XiZeroCopy) (hq₁ : q₁ ∈ F.filter D)
    {A Bc Bt : ℝ} (hA : 0 < A)
    (hdom : (jasRealTerm P σ a (q₁.1 : ℂ)).re ≤ -A)
    (hDeq : ∀ q ∈ F.filter D, (jasRealTerm P σ a (q.1 : ℂ)).re = (jasRealTerm P σ a (q₁.1 : ℂ)).re)
    (hcomp : ∀ q ∈ F.filter (fun q => ¬ D q), ‖jasRealKernel P σ a (q.1 : ℂ)‖ ≤ Bc)
    (hall : ∀ q : XiZeroCopy, ‖jasRealKernel P σ a (q.1 : ℂ)‖ ≤ Bt) (hBc : 0 ≤ Bc)
    (hFc : (∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) * Bc ≤ A / 4)
    (htail : (∑' q : {x // x ∉ F}, ‖1 / ((q.1.1 : ℂ) * (1 - (q.1.1 : ℂ)))‖) * Bt ≤ A / 4) :
    (∑' q : XiZeroCopy, jasRealTerm P σ a (q.1 : ℂ)).re < 0 := by
  set wq : XiZeroCopy → ℝ := fun q => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ with hwq
  have hwsum : Summable wq := summable_inv_mul_one_sub.norm
  have hwq0 : ∀ q, 0 ≤ wq q := fun q => norm_nonneg _
  have hnorm : ∀ q : XiZeroCopy, ‖jasRealTerm P σ a (q.1 : ℂ)‖ ≤ Bt * wq q := fun q => by
    rw [jasRealTerm, div_eq_mul_one_div, norm_mul]
    exact mul_le_mul_of_nonneg_right (hall q) (norm_nonneg _)
  have hsumm : Summable fun q : XiZeroCopy => jasRealTerm P σ a (q.1 : ℂ) :=
    Summable.of_norm_bounded (hwsum.mul_left Bt) hnorm
  refine re_tsum_neg_of_dominant hsumm F D hA ?_ ?_ ?_
  · rw [Complex.re_sum, Finset.sum_congr rfl hDeq, Finset.sum_const, nsmul_eq_mul]
    have hcard : (1 : ℝ) ≤ ((F.filter D).card : ℝ) := by
      exact_mod_cast Finset.card_pos.mpr ⟨q₁, hq₁⟩
    nlinarith
  · refine (norm_sum_le _ _).trans ?_
    calc ∑ q ∈ F.filter (fun q => ¬ D q), ‖jasRealTerm P σ a (q.1 : ℂ)‖
        ≤ ∑ q ∈ F.filter (fun q => ¬ D q), wq q * Bc := by
          refine Finset.sum_le_sum fun q hq => ?_
          rw [jasRealTerm, div_eq_mul_one_div, norm_mul, mul_comm]
          exact mul_le_mul_of_nonneg_left (hcomp q hq) (norm_nonneg _)
      _ = (∑ q ∈ F.filter (fun q => ¬ D q), wq q) * Bc := by rw [Finset.sum_mul]
      _ ≤ (∑' q, wq q) * Bc := by
          gcongr
          exact hwsum.sum_le_tsum _ fun q _ => hwq0 q
      _ ≤ A / 4 := hFc
  · have hs1 : Summable (fun q : {x // x ∉ F} => ‖jasRealTerm P σ a (q.1.1 : ℂ)‖) :=
      hsumm.norm.subtype _
    have hs2 : Summable (fun q : {x // x ∉ F} => Bt * wq q) := (hwsum.mul_left Bt).subtype _
    calc ‖∑' q : {x // x ∉ F}, jasRealTerm P σ a (q.1.1 : ℂ)‖
        ≤ ∑' q : {x // x ∉ F}, ‖jasRealTerm P σ a (q.1.1 : ℂ)‖ := norm_tsum_le_tsum_norm hs1
      _ ≤ ∑' q : {x // x ∉ F}, Bt * wq q := Summable.tsum_le_tsum (fun q => hnorm q) hs1 hs2
      _ = (∑' q : {x // x ∉ F}, wq q) * Bt := by rw [tsum_mul_left, mul_comm]
      _ ≤ A / 4 := htail

/-- Uniform bounds for the factors of every zero at amplitude `a`. -/
theorem jasReal_uniform_bounds {X N : ℕ} {σ δ α a Λ₀ : ℝ} (hα : α = σ - δ) (hα0 : 0 < α)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ δ) (ha0 : 0 ≤ a) (ha_half : a ≤ 1 / 2)
    (haΛ : a * Λ₀ ≤ 1 / 12) (haS : a * jasPrimeRpowSum α N ≤ Λ₀) (q : XiZeroCopy) :
    (∀ p ∈ jasPrimeWindow X N, ‖jasRealFactor σ a p (q.1 : ℂ) - 1‖ ≤ 1 / 2) ∧
      ∑ p ∈ jasPrimeWindow X N, ‖jasRealFactor σ a p (q.1 : ℂ) - 1‖ ^ 2 ≤ 1 / 12 ∧
      ‖jasRealKernel (jasPrimeWindow X N) σ a (q.1 : ℂ)‖ ≤ Real.exp Λ₀ := by
  have hdq : α ≤ σ - |(q.1 : ℂ).re - 1 / 2| := by rw [hα]; linarith [hmax q]
  have hu_le : ∀ p : Nat.Primes,
      ‖jasRealFactor σ a p (q.1 : ℂ) - 1‖ ≤ a * Real.exp (-α * Real.log p) := fun p =>
    (norm_jasRealFactor_sub_one_le ha0 p _).trans
      (mul_le_mul_of_nonneg_left (exp_neg_mul_log_prime_anti hdq p) ha0)
  have hu_a : ∀ p : Nat.Primes, ‖jasRealFactor σ a p (q.1 : ℂ) - 1‖ ≤ a := fun p =>
    (hu_le p).trans (mul_le_of_le_one_right ha0 (exp_neg_mul_log_prime_le_one hα0.le p))
  have hsum_u : ∑ p ∈ jasPrimeWindow X N, ‖jasRealFactor σ a p (q.1 : ℂ) - 1‖ ≤ Λ₀ :=
    (Finset.sum_le_sum fun p _ => hu_le p).trans (by
      rw [← Finset.mul_sum]
      exact (mul_le_mul_of_nonneg_left (sum_jasPrimeWindow_le_jasPrimeRpowSum X N α) ha0).trans
        haS)
  refine ⟨fun p _ => (hu_a p).trans ha_half, ?_, ?_⟩
  · calc ∑ p ∈ jasPrimeWindow X N, ‖jasRealFactor σ a p (q.1 : ℂ) - 1‖ ^ 2
        ≤ ∑ p ∈ jasPrimeWindow X N, a * ‖jasRealFactor σ a p (q.1 : ℂ) - 1‖ := by
          refine Finset.sum_le_sum fun p _ => ?_
          rw [sq]
          exact mul_le_mul_of_nonneg_right (hu_a p) (norm_nonneg _)
      _ = a * ∑ p ∈ jasPrimeWindow X N, ‖jasRealFactor σ a p (q.1 : ℂ) - 1‖ := by
          rw [Finset.mul_sum]
      _ ≤ a * Λ₀ := mul_le_mul_of_nonneg_left hsum_u ha0
      _ ≤ 1 / 12 := haΛ
  · exact (norm_jasRealKernel_le_exp _ σ a _).trans (Real.exp_le_exp.mpr hsum_u)

/-- The dominant exponent is within `1/12` of `R + i(π − arg w)`. -/
theorem jasReal_main_le {X N : ℕ} {α γ R θ ν m₀ ε a E : ℝ} {s₀ u v w : ℂ}
    (hN2 : 2 ≤ N) (hE : E = jasMainScale α N) (ha : a = 2 * ν * m₀ / E)
    (hs₀ : s₀ = (α : ℂ) - (γ : ℂ) * I) (hm₀ : m₀ = ‖1 - s₀‖) (hm₀0 : 0 < m₀)
    (hθ : θ = Real.pi - w.arg) (hν0 : 0 < ν)
    (hu : (ν : ℂ) * u = (R : ℂ) + (θ : ℂ) * I) (hv : v = u * ((1 - s₀) / (m₀ : ℂ)))
    (hε2 : ν * m₀ * ε ≤ 1 / 24)
    (h1 : ‖jasWindowSum X N s₀ - jasMainTerm s₀ N‖ ≤ ε * E)
    (hph : ‖cexp (((γ * Real.log N : ℝ) : ℂ) * I) - v‖ < 1 / (24 * ν)) :
    ‖((a / 2 : ℝ) : ℂ) * jasCpowSum (jasPrimeWindow X N) s₀ -
      ((R : ℂ) + ((Real.pi - w.arg : ℝ) : ℂ) * I)‖ ≤ 1 / 12 := by
  have hE0 : 0 < E := hE ▸ jasMainScale_pos hN2
  have hM := jasMainTerm_eq α γ (show 0 < N by omega)
  rw [← hs₀, ← hE] at hM
  have key := norm_half_amp_mul_sub_le (W := jasCpowSum (jasPrimeWindow X N) s₀) (u := u)
    (v := v) (c := cexp (((γ * Real.log N : ℝ) : ℂ) * I)) hE0 hν0.le hm₀ hm₀0 hM hv
  rw [show 2 * ν * m₀ / E / 2 = a / 2 by rw [ha], hu, hθ] at key
  refine key.trans ?_
  have hb1 : ν * m₀ * ‖jasCpowSum (jasPrimeWindow X N) s₀ - jasMainTerm s₀ N‖ / E ≤ 1 / 24 := by
    rw [div_le_iff₀ hE0]
    calc ν * m₀ * ‖jasCpowSum (jasPrimeWindow X N) s₀ - jasMainTerm s₀ N‖
        ≤ ν * m₀ * (ε * E) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ = ν * m₀ * ε * E := by ring
      _ ≤ 1 / 24 * E := mul_le_mul_of_nonneg_right hε2 hE0.le
  have hb2 : ν * ‖cexp (((γ * Real.log N : ℝ) : ℂ) * I) - v‖ ≤ 1 / 24 := by
    have := mul_lt_mul_of_pos_left hph hν0
    rw [show ν * (1 / (24 * ν)) = 1 / 24 by field_simp] at this
    exact this.le
  linarith

/-- The big-exponent bound for a zero at distance `δ` and height `≥ γ₁`. -/
theorem jasReal_sameDepth_big_le {X N : ℕ} {α γ₁ ν m₀ μ₁ ρ₂ ε a E t : ℝ}
    (hN2 : 2 ≤ N) (hE : E = jasMainScale α N) (ha : a = 2 * ν * m₀ / E) (hν0 : 0 < ν)
    (hm₀0 : 0 ≤ m₀) (hμ₁ : μ₁ = Real.sqrt ((1 - α) ^ 2 + γ₁ ^ 2)) (hμ₁0 : 0 < μ₁) (hγ₁0 : 0 ≤ γ₁)
    (hρ₂ : m₀ / μ₁ + m₀ * ε ≤ ρ₂) (ht : γ₁ ≤ t)
    (h5 : ‖jasWindowSum X N ((α : ℂ) - (t : ℂ) * I) - jasMainTerm ((α : ℂ) - (t : ℂ) * I) N‖ ≤
      ε * E) :
    a / 2 * ‖jasCpowSum (jasPrimeWindow X N) ((α : ℂ) - (t : ℂ) * I)‖ ≤ ν * ρ₂ := by
  have hE0 : 0 < E := hE ▸ jasMainScale_pos hN2
  have hMn : ‖jasMainTerm ((α : ℂ) - (t : ℂ) * I) N‖ ≤ E / μ₁ := by
    rw [norm_jasMainTerm_eq α _ hN2, ← hE]
    refine div_le_div_of_nonneg_left hE0.le hμ₁0 ?_
    rw [hμ₁]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hWsq : ‖jasCpowSum (jasPrimeWindow X N) ((α : ℂ) - (t : ℂ) * I)‖ ≤ E / μ₁ + ε * E := by
    have := norm_le_insert' (jasWindowSum X N ((α : ℂ) - (t : ℂ) * I))
      (jasMainTerm ((α : ℂ) - (t : ℂ) * I) N)
    rw [jasWindowSum_eq_jasCpowSum] at this h5
    linarith
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  calc a / 2 * ‖jasCpowSum (jasPrimeWindow X N) ((α : ℂ) - (t : ℂ) * I)‖
      ≤ a / 2 * (E / μ₁ + ε * E) := mul_le_mul_of_nonneg_left hWsq (by positivity)
    _ = ν * (m₀ / μ₁ + m₀ * ε) := by rw [ha]; field_simp
    _ ≤ ν * ρ₂ := mul_le_mul_of_nonneg_left hρ₂ hν0.le
/-- The competitors in the finite set: kernels at most `2 + e^{(R + 2π)ρ₂ + 1}`. -/
theorem jasReal_competitor_le {X N : ℕ} {σ δ α γ γ₁ R ν m₀ μ₁ ρ₂ ε ε₂ Λ₀ a E : ℝ}
    {q : XiZeroCopy} (hN2 : 2 ≤ N) (hα : α = σ - δ) (hγ0 : 0 < γ) (hγ₁ : γ < γ₁)
    (hE : E = jasMainScale α N) (ha : a = 2 * ν * m₀ / E) (ha0 : 0 ≤ a) (hν0 : 0 < ν)
    (hm₀0 : 0 ≤ m₀) (hμ₁ : μ₁ = Real.sqrt ((1 - α) ^ 2 + γ₁ ^ 2)) (hμ₁0 : 0 < μ₁)
    (hρ₂ : m₀ / μ₁ + m₀ * ε ≤ ρ₂) (hρ₂0 : 0 ≤ ρ₂) (hνR : ν ≤ R + 2 * Real.pi)
    (haS : a * jasPrimeRpowSum α N ≤ Λ₀) (hε₂0 : 0 ≤ ε₂) (hε₂Λ : ε₂ * Λ₀ ≤ 1 / 48)
    (hmax : |(q.1 : ℂ).re - 1 / 2| ≤ δ)
    (hgap : |(q.1 : ℂ).re - 1 / 2| = δ → |(q.1 : ℂ).im| = γ ∨ γ₁ ≤ |(q.1 : ℂ).im|)
    (hnot : ¬ (|(q.1 : ℂ).re - 1 / 2| = δ ∧ |(q.1 : ℂ).im| = γ))
    (hU : (∀ p ∈ jasPrimeWindow X N, ‖jasRealFactor σ a p (q.1 : ℂ) - 1‖ ≤ 1 / 2) ∧
      ∑ p ∈ jasPrimeWindow X N, ‖jasRealFactor σ a p (q.1 : ℂ) - 1‖ ^ 2 ≤ 1 / 12)
    (hsmall : a / 2 * ∑ p ∈ jasPrimeWindow X N, Real.exp (-(σ + δ) * Real.log p) ≤ 1 / 96)
    (h5 : (|(q.1 : ℂ).re - 1 / 2| < δ →
        jasPrimeRpowSum (σ - |(q.1 : ℂ).re - 1 / 2|) N ≤ ε₂ * jasPrimeRpowSum α N) ∧
      (|(q.1 : ℂ).re - 1 / 2| = δ →
        ‖jasWindowSum X N ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I) -
          jasMainTerm ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I) N‖ ≤ ε * E)) :
    ‖jasRealKernel (jasPrimeWindow X N) σ a (q.1 : ℂ)‖ ≤
      2 + Real.exp ((R + 2 * Real.pi) * ρ₂ + 1) := by
  rcases lt_or_eq_of_le hmax with hlt | hqd
  · refine (norm_jasRealKernel_shallow_le ha0 ?_).trans
      (by linarith [Real.exp_pos ((R + 2 * Real.pi) * ρ₂ + 1)])
    calc a * ∑ p ∈ jasPrimeWindow X N, Real.exp (-(σ - |(q.1 : ℂ).re - 1 / 2|) * Real.log p)
        ≤ a * (ε₂ * jasPrimeRpowSum α N) := mul_le_mul_of_nonneg_left
          ((sum_jasPrimeWindow_le_jasPrimeRpowSum X N _).trans (h5.1 hlt)) ha0
      _ = ε₂ * (a * jasPrimeRpowSum α N) := by ring
      _ ≤ ε₂ * Λ₀ := mul_le_mul_of_nonneg_left haS hε₂0
      _ ≤ 1 / 48 := hε₂Λ
  · have hqi : γ₁ ≤ |(q.1 : ℂ).im| := by
      rcases hgap hqd with h | h
      · exact absurd ⟨hqd, h⟩ hnot
      · exact h
    have hbigq := jasReal_sameDepth_big_le hN2 hE ha hν0 hm₀0 hμ₁ hμ₁0
      (hγ0.le.trans hγ₁.le) hρ₂ hqi (h5.2 hqd)
    rw [hα] at hbigq
    refine (norm_jasRealKernel_sameDepth_le hqd ha0 hU.1 hU.2 hsmall hbigq).trans ?_
    have h1 : ν * ρ₂ + 1 ≤ (R + 2 * Real.pi) * ρ₂ + 1 := by
      linarith [mul_le_mul_of_nonneg_right hνR hρ₂0]
    linarith [Real.exp_le_exp.mpr h1]

/-- **The test at one scale.**  All quantitative choices made, the real-amplitude test with
amplitude `a = 2ν m₀/E_α(N)` on the primes in `(X, N]` has negative aggregate. -/
theorem jasReal_tsum_neg_core {X N : ℕ} {σ δ α γ γ₁ R θ ν m₀ μ₁ ρ₂ ε ε₂ Λ₀ W : ℝ}
    {s₀ u v : ℂ} {q₁ : XiZeroCopy} {F : Finset XiZeroCopy}
    (hN2 : 2 ≤ N) (hδ0 : 0 < δ) (hα : α = σ - δ) (hα0 : 0 < α) (hα1 : α < 1) (hγ0 : 0 < γ)
    (hq₁ : (q₁.1 : ℂ) = 1 / 2 + (δ : ℂ) + (γ : ℂ) * I)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ δ)
    (hgap : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| = δ →
      |(q.1 : ℂ).im| = γ ∨ γ₁ ≤ |(q.1 : ℂ).im|)
    (hγ₁ : γ < γ₁) (hs₀ : s₀ = (α : ℂ) - (γ : ℂ) * I) (hm₀ : m₀ = ‖1 - s₀‖) (hm₀0 : 0 < m₀)
    (hμ₁ : μ₁ = Real.sqrt ((1 - α) ^ 2 + γ₁ ^ 2)) (hμ₁0 : 0 < μ₁)
    (hρ₂ : m₀ / μ₁ + m₀ * ε ≤ ρ₂) (hρ₂0 : 0 ≤ ρ₂)
    (hθ : θ = Real.pi - (1 / ((q₁.1 : ℂ) * (1 - (q₁.1 : ℂ)))).arg)
    (hν0 : 0 < ν) (hνR : ν ≤ R + 2 * Real.pi)
    (hu : (ν : ℂ) * u = (R : ℂ) + (θ : ℂ) * I) (hv : v = u * ((1 - s₀) / (m₀ : ℂ)))
    (hW : W = ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖)
    (hRbig : 16 * W * (2 + Real.exp ((R + 2 * Real.pi) * ρ₂ + 1)) ≤
      ‖1 / ((q₁.1 : ℂ) * (1 - (q₁.1 : ℂ)))‖ * Real.exp R)
    (hΛ₀ : Λ₀ = 2 * ν * m₀ * (1 / (1 - α) + 1)) (hΛ₀0 : 0 < Λ₀)
    (hFtail : (∑' q : {x // x ∉ F}, ‖1 / ((q.1.1 : ℂ) * (1 - (q.1.1 : ℂ)))‖) * Real.exp Λ₀ ≤
      ‖1 / ((q₁.1 : ℂ) * (1 - (q₁.1 : ℂ)))‖ * Real.exp R / 8)
    (hq₁F : q₁ ∈ F) (hε2 : ν * m₀ * ε ≤ 1 / 24) (hε₂Λ : ε₂ * Λ₀ ≤ 1 / 48) (hε₂0 : 0 ≤ ε₂)
    (h1 : ‖jasWindowSum X N s₀ - jasMainTerm s₀ N‖ ≤ ε * jasMainScale α N)
    (h2 : jasPrimeRpowSum α N ≤ (1 / (1 - α) + 1) * jasMainScale α N)
    (h3 : jasPrimeRpowSum (σ + δ) N ≤ ε₂ * jasPrimeRpowSum α N)
    (h4 : 2 * ν * m₀ / jasMainScale α N ≤ min (1 / 2) (1 / (12 * (Λ₀ + 1))))
    (h5 : ∀ q ∈ F, (|(q.1 : ℂ).re - 1 / 2| < δ →
        jasPrimeRpowSum (σ - |(q.1 : ℂ).re - 1 / 2|) N ≤ ε₂ * jasPrimeRpowSum α N) ∧
      (|(q.1 : ℂ).re - 1 / 2| = δ →
        ‖jasWindowSum X N ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I) -
          jasMainTerm ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I) N‖ ≤ ε * jasMainScale α N))
    (hph : ‖cexp (((γ * Real.log N : ℝ) : ℂ) * I) - v‖ < 1 / (24 * ν)) :
    (∑' q : XiZeroCopy, jasRealTerm (jasPrimeWindow X N) σ (2 * ν * m₀ / jasMainScale α N)
      (q.1 : ℂ)).re < 0 := by
  classical
  obtain ⟨E, hE⟩ : ∃ E : ℝ, E = jasMainScale α N := ⟨_, rfl⟩
  have hE0 : 0 < E := hE ▸ jasMainScale_pos hN2
  rw [← hE] at h1 h2 h4 h5 ⊢
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 2 * ν * m₀ / E := ⟨_, rfl⟩
  rw [← ha] at h4 ⊢
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have ha_half : a ≤ 1 / 2 := h4.trans (min_le_left _ _)
  have haΛ : a * Λ₀ ≤ 1 / 12 := by
    have h4' : a ≤ 1 / (12 * (Λ₀ + 1)) := h4.trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at h4'
    calc a * Λ₀ ≤ a * (Λ₀ + 1) := mul_le_mul_of_nonneg_left (by linarith) ha0
      _ = a * (12 * (Λ₀ + 1)) / 12 := by ring
      _ ≤ 1 / 12 := by linarith
  have h1α : 0 < 1 - α := by linarith
  have haS : a * jasPrimeRpowSum α N ≤ Λ₀ := by
    rw [ha, hΛ₀]
    calc 2 * ν * m₀ / E * jasPrimeRpowSum α N ≤ 2 * ν * m₀ / E * ((1 / (1 - α) + 1) * E) := by
          gcongr
      _ = 2 * ν * m₀ * (1 / (1 - α) + 1) := by field_simp
  have hU := fun q => jasReal_uniform_bounds (X := X) (N := N) hα hα0 hmax ha0 ha_half haΛ haS q
  have hsmall_sum : a / 2 * ∑ p ∈ jasPrimeWindow X N, Real.exp (-(σ + δ) * Real.log p) ≤
      1 / 96 := by
    have h1' : ∑ p ∈ jasPrimeWindow X N, Real.exp (-(σ + δ) * Real.log p) ≤
        ε₂ * jasPrimeRpowSum α N := (sum_jasPrimeWindow_le_jasPrimeRpowSum X N (σ + δ)).trans h3
    calc a / 2 * ∑ p ∈ jasPrimeWindow X N, Real.exp (-(σ + δ) * Real.log p)
        ≤ a / 2 * (ε₂ * jasPrimeRpowSum α N) := mul_le_mul_of_nonneg_left h1' (by positivity)
      _ = ε₂ * (a * jasPrimeRpowSum α N) / 2 := by ring
      _ ≤ ε₂ * Λ₀ / 2 := by linarith [mul_le_mul_of_nonneg_left haS hε₂0]
      _ ≤ 1 / 96 := by linarith
  have hq₁re : (q₁.1 : ℂ).re - 1 / 2 = δ := by rw [hq₁]; simp
  have hq₁im : (q₁.1 : ℂ).im = γ := by rw [hq₁]; simp
  have hbig : (σ : ℂ) - ((q₁.1 : ℂ) - 1 / 2) = s₀ := by rw [hq₁, hs₀, hα]; push_cast; ring
  have hsmallre : ((σ : ℂ) + ((q₁.1 : ℂ) - 1 / 2)).re = σ + δ := by
    have : ((σ : ℂ) + ((q₁.1 : ℂ) - 1 / 2)).re = σ + ((q₁.1 : ℂ).re - 1 / 2) := by simp
    rw [this, hq₁re]
  have hmain := jasReal_main_le hN2 hE ha hs₀ hm₀ hm₀0 hθ hν0 hu hv hε2 h1 hph
  have hdom := re_jasRealTerm_dominant_le hbig hsmallre (hU q₁).1 (hU q₁).2.1 hsmall_sum ha0
    hmain
  let D : XiZeroCopy → Prop := fun q => |(q.1 : ℂ).re - 1 / 2| = δ ∧ |(q.1 : ℂ).im| = γ
  have hcomp : ∀ q ∈ F.filter (fun q => ¬ D q),
      ‖jasRealKernel (jasPrimeWindow X N) σ a (q.1 : ℂ)‖ ≤
        2 + Real.exp ((R + 2 * Real.pi) * ρ₂ + 1) := fun q hq =>
    jasReal_competitor_le hN2 hα hγ0 hγ₁ hE ha ha0 hν0 hm₀0.le hμ₁ hμ₁0 hρ₂ hρ₂0 hνR haS hε₂0
      hε₂Λ (hmax q) (hgap q) (Finset.mem_filter.mp hq).2 ⟨(hU q).1, (hU q).2.1⟩ hsmall_sum
      (h5 q (Finset.mem_filter.mp hq).1)
  have hq₁D : q₁ ∈ F.filter D := Finset.mem_filter.mpr ⟨hq₁F,
    ⟨by rw [hq₁re, abs_of_pos hδ0], by rw [hq₁im, abs_of_pos hγ0]⟩⟩
  have hDeq : ∀ q ∈ F.filter D, (jasRealTerm (jasPrimeWindow X N) σ a (q.1 : ℂ)).re =
      (jasRealTerm (jasPrimeWindow X N) σ a (q₁.1 : ℂ)).re := by
    intro q hq
    obtain ⟨hqd, hqi⟩ := (Finset.mem_filter.mp hq).2
    exact re_jasRealTerm_eq_of_abs (by rw [hqd, hq₁re, abs_of_pos hδ0])
      (by rw [hqi, hq₁im, abs_of_pos hγ0])
  have hW0 : 0 ≤ W := by rw [hW]; exact tsum_nonneg fun q => norm_nonneg _
  have hq0 : (q₁.1 : ℂ) ≠ 0 := fun h => by
    have := xiZeroCopy_re_pos q₁; rw [h, Complex.zero_re] at this; exact lt_irrefl 0 this
  have hq1 : 1 - (q₁.1 : ℂ) ≠ 0 := fun h => by
    have h1' := xiZeroCopy_re_lt_one q₁
    have := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
    linarith
  have hwn : 0 < ‖1 / ((q₁.1 : ℂ) * (1 - (q₁.1 : ℂ)))‖ :=
    norm_pos_iff.mpr (one_div_ne_zero (mul_ne_zero hq0 hq1))
  have hpos_w : 0 < ‖1 / ((q₁.1 : ℂ) * (1 - (q₁.1 : ℂ)))‖ * Real.exp R / 2 := by positivity
  have hBc0 : 0 ≤ 2 + Real.exp ((R + 2 * Real.pi) * ρ₂ + 1) := by positivity
  refine re_tsum_jasRealTerm_neg F D q₁ hq₁D hpos_w (by linarith) hDeq hcomp (fun q => (hU q).2.2)
    hBc0 ?_ ?_
  · rw [← hW]
    linarith [mul_nonneg hW0 hBc0]
  · linarith

/-- **The negative tests.**  If a zero `ρ₀` off the critical line has the largest distance
`δ = |Re ρ₀ − ½|` from it among all zeros and `δ < σ < 1 + δ`, there is `κ > 0` such that for
infinitely many `N` the real-amplitude kernel on the primes in `(X, N]` with amplitude
`κ/E_{σ−δ}(N) ≤ 1`, `E_α(N) = N^{1−α}/log N`, has negative aggregate. -/
theorem frequently_jasReal_neg_of_maximal_offLine (q₀ : XiZeroCopy)
    (hoff : (q₀.1 : ℂ).re ≠ 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) {σ : ℝ}
    (hσ0 : |(q₀.1 : ℂ).re - 1 / 2| < σ) (hσ1 : σ < 1 + |(q₀.1 : ℂ).re - 1 / 2|) (X : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∃ᶠ N : ℕ in atTop, 2 ≤ N ∧
      κ / jasMainScale (σ - |(q₀.1 : ℂ).re - 1 / 2|) N ≤ 1 ∧
      (∑' q : XiZeroCopy, jasRealTerm (jasPrimeWindow X N) σ
        (κ / jasMainScale (σ - |(q₀.1 : ℂ).re - 1 / 2|) N) (q.1 : ℂ)).re < 0 := by
  classical
  obtain ⟨q₁, γ, γ₁, hγ0, hγγ₁, hq₁, hgap⟩ := exists_normalized_maximal_zero q₀ hoff
  obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = |(q₀.1 : ℂ).re - 1 / 2| := ⟨_, rfl⟩
  rw [← hδ] at hmax hσ0 hσ1 hq₁ hgap ⊢
  have hδ0 : 0 < δ := by rw [hδ]; exact abs_pos.mpr (sub_ne_zero.mpr hoff)
  obtain ⟨α, hα⟩ : ∃ α : ℝ, α = σ - δ := ⟨_, rfl⟩
  have hα0 : 0 < α := by rw [hα]; linarith
  have hα1 : α < 1 := by rw [hα]; linarith
  have h1α : 0 < 1 - α := by linarith
  obtain ⟨s₀, hs₀⟩ : ∃ s₀ : ℂ, s₀ = (α : ℂ) - (γ : ℂ) * I := ⟨_, rfl⟩
  have hs₀re : s₀.re = α := by rw [hs₀]; simp
  have hq₀ : (q₁.1 : ℂ) ≠ 0 := fun h => by
    have := xiZeroCopy_re_pos q₁; rw [h, Complex.zero_re] at this; exact lt_irrefl 0 this
  have hq₁1 : 1 - (q₁.1 : ℂ) ≠ 0 := fun h => by
    have h1' := xiZeroCopy_re_lt_one q₁
    have := congrArg Complex.re h
    rw [Complex.sub_re, Complex.one_re, Complex.zero_re] at this
    linarith
  obtain ⟨w₀, hw₀⟩ : ∃ w : ℂ, w = 1 / ((q₁.1 : ℂ) * (1 - (q₁.1 : ℂ))) := ⟨_, rfl⟩
  have hw₀n : 0 < ‖w₀‖ :=
    norm_pos_iff.mpr (by rw [hw₀]; exact one_div_ne_zero (mul_ne_zero hq₀ hq₁1))
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
    ⟨_, rfl⟩
  obtain ⟨m₀, hm₀⟩ : ∃ m₀ : ℝ, m₀ = ‖1 - s₀‖ := ⟨_, rfl⟩
  have hm₀eq : m₀ = Real.sqrt ((1 - α) ^ 2 + γ ^ 2) := by rw [hm₀, hs₀, norm_one_sub_alpha_sub]
  have hm₀0 : 0 < m₀ := by rw [hm₀eq]; exact Real.sqrt_pos.mpr (by positivity)
  obtain ⟨μ₁, hμ₁⟩ : ∃ μ₁ : ℝ, μ₁ = Real.sqrt ((1 - α) ^ 2 + γ₁ ^ 2) := ⟨_, rfl⟩
  have hm₀μ₁ : m₀ < μ₁ := by
    rw [hm₀eq, hμ₁]; exact Real.sqrt_lt_sqrt (by positivity) (by nlinarith)
  have hμ₁0 : 0 < μ₁ := hm₀0.trans hm₀μ₁
  obtain ⟨ρ₁, hρ₁⟩ : ∃ ρ₁ : ℝ, ρ₁ = m₀ / μ₁ := ⟨_, rfl⟩
  have hρ₁1 : ρ₁ < 1 := by rw [hρ₁, div_lt_one hμ₁0]; exact hm₀μ₁
  have hρ₁0 : 0 < ρ₁ := by rw [hρ₁]; positivity
  obtain ⟨ρ₂, hρ₂⟩ : ∃ ρ₂ : ℝ, ρ₂ = (1 + ρ₁) / 2 := ⟨_, rfl⟩
  have hρ₂1 : ρ₂ < 1 := by rw [hρ₂]; linarith
  obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, θ = Real.pi - w₀.arg := ⟨_, rfl⟩
  have hθ0 : 0 ≤ θ := by rw [hθ]; linarith [Complex.arg_le_pi w₀]
  have hθ1 : θ ≤ 2 * Real.pi := by rw [hθ]; linarith [Complex.neg_pi_lt_arg w₀]
  obtain ⟨R, hR0, hRbig⟩ := exists_large_exponent (W := W) hw₀n hρ₂1
  obtain ⟨ν, hν⟩ : ∃ ν : ℝ, ν = ‖(R : ℂ) + (θ : ℂ) * I‖ := ⟨_, rfl⟩
  have hν0 : 0 < ν := by
    rw [hν]; refine norm_pos_iff.mpr fun h => ?_
    have := congrArg Complex.re h; simp at this; linarith
  have hνR : ν ≤ R + 2 * Real.pi := by
    rw [hν]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
      Real.norm_of_nonneg hR0.le, Real.norm_of_nonneg hθ0]
    linarith
  have hνc : (ν : ℂ) ≠ 0 := by exact_mod_cast hν0.ne'
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u = ((R : ℂ) + (θ : ℂ) * I) / (ν : ℂ) := ⟨_, rfl⟩
  have hνu : (ν : ℂ) * u = (R : ℂ) + (θ : ℂ) * I := by rw [hu, mul_div_cancel₀ _ hνc]
  obtain ⟨v, hv⟩ : ∃ v : ℂ, v = u * ((1 - s₀) / (m₀ : ℂ)) := ⟨_, rfl⟩
  have hvn : ‖v‖ = 1 := by
    rw [hv, norm_mul, norm_div, Complex.norm_real, Real.norm_of_nonneg hm₀0.le, ← hm₀,
      div_self hm₀0.ne', mul_one, hu, norm_div, Complex.norm_real, Real.norm_of_nonneg hν0.le,
      ← hν, div_self hν0.ne']
  obtain ⟨Λ₀, hΛ₀⟩ : ∃ Λ₀ : ℝ, Λ₀ = 2 * ν * m₀ * (1 / (1 - α) + 1) := ⟨_, rfl⟩
  have hΛ₀0 : 0 < Λ₀ := by rw [hΛ₀]; positivity
  obtain ⟨F, hFtail, hq₁F⟩ : ∃ F : Finset XiZeroCopy,
      (∑' q : {x // x ∉ F}, ‖1 / ((q.1.1 : ℂ) * (1 - (q.1.1 : ℂ)))‖) * Real.exp Λ₀ ≤
        ‖w₀‖ * Real.exp R / 8 ∧ q₁ ∈ F := by
    have hpos8 : 0 < ‖w₀‖ * Real.exp R / 8 / Real.exp Λ₀ := by positivity
    have h1 := (tendsto_tsum_compl_atTop_zero
      (fun q : XiZeroCopy => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖)).eventually (gt_mem_nhds hpos8)
    have h2 : ∀ᶠ F : Finset XiZeroCopy in atTop, {q₁} ⊆ F := eventually_ge_atTop {q₁}
    obtain ⟨F, hF1, hF2⟩ := (h1.and h2).exists
    refine ⟨F, ?_, hF2 (Finset.mem_singleton_self q₁)⟩
    rw [lt_div_iff₀ (Real.exp_pos _)] at hF1
    exact hF1.le
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = min 1 (min (1 / (24 * ν * m₀)) ((1 - ρ₁) / (2 * m₀))) :=
    ⟨_, rfl⟩
  have hε0 : 0 < ε := by
    rw [hε]; exact lt_min one_pos (lt_min (by positivity) (div_pos (by linarith) (by positivity)))
  have hε2 : ν * m₀ * ε ≤ 1 / 24 := by
    have : ε ≤ 1 / (24 * ν * m₀) := by rw [hε]; exact (min_le_right _ _).trans (min_le_left _ _)
    rw [le_div_iff₀ (by positivity)] at this
    linarith
  have hε3 : m₀ / μ₁ + m₀ * ε ≤ ρ₂ := by
    have : ε ≤ (1 - ρ₁) / (2 * m₀) := by
      rw [hε]; exact (min_le_right _ _).trans (min_le_right _ _)
    rw [le_div_iff₀ (by positivity)] at this
    rw [← hρ₁, hρ₂]; linarith
  obtain ⟨ε₂, hε₂⟩ : ∃ ε₂ : ℝ, ε₂ = 1 / (48 * (Λ₀ + 1)) := ⟨_, rfl⟩
  have hε₂0 : 0 < ε₂ := by rw [hε₂]; positivity
  have hε₂Λ : ε₂ * Λ₀ ≤ 1 / 48 := by
    rw [hε₂, div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) (by norm_num)]
    linarith
  -- eventual conditions
  have ev1 := eventually_norm_jasWindowSum_sub_main_le X (s := s₀) (by rw [hs₀re]; exact hα0)
    (by rw [hs₀re]; exact hα1) hε0
  have ev2 := eventually_jasPrimeRpowSum_le_main hα0 hα1 one_pos
  have ev3 := eventually_jasPrimeRpowSum_le hα1.le (show α < σ + δ by rw [hα]; linarith) hε₂0
  have hamp0 : Tendsto (fun N : ℕ => 2 * ν * m₀ / jasMainScale α N) atTop (𝓝 0) := by
    have := (tendsto_natLog_div_rpow_atTop h1α).const_mul (2 * ν * m₀)
    rw [mul_zero] at this
    refine this.congr fun N => ?_
    simp only [jasMainScale]
    rw [div_div_eq_mul_div, mul_div_assoc]
  have ev4 := hamp0.eventually (ge_mem_nhds (show (0 : ℝ) < min (1 / 2) (1 / (12 * (Λ₀ + 1))) from
    lt_min (by norm_num) (by positivity)))
  have ev5 : ∀ᶠ N : ℕ in atTop, ∀ q ∈ F,
      (|(q.1 : ℂ).re - 1 / 2| < δ →
        jasPrimeRpowSum (σ - |(q.1 : ℂ).re - 1 / 2|) N ≤ ε₂ * jasPrimeRpowSum α N) ∧
      (|(q.1 : ℂ).re - 1 / 2| = δ →
        ‖jasWindowSum X N ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I) -
          jasMainTerm ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I) N‖ ≤ ε * jasMainScale α N) := by
    refine (Filter.eventually_all_finset F).mpr fun q _ => ?_
    refine Eventually.and ?_ ?_
    · by_cases hq : |(q.1 : ℂ).re - 1 / 2| < δ
      · filter_upwards [eventually_jasPrimeRpowSum_le hα1.le
          (show α < σ - |(q.1 : ℂ).re - 1 / 2| by rw [hα]; linarith) hε₂0] with N hN _ using hN
      · exact Eventually.of_forall fun N h => absurd h hq
    · have hre : ((α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I).re = α := by simp
      have h := eventually_norm_jasWindowSum_sub_main_le X
        (s := (α : ℂ) - ((|(q.1 : ℂ).im| : ℝ) : ℂ) * I) (by rw [hre]; exact hα0)
        (by rw [hre]; exact hα1) hε0
      filter_upwards [h] with N hN _
      rwa [hre] at hN
  have fr := frequently_cexp_log_near (γ := γ) hγ0.ne' hvn (show 0 < 1 / (24 * ν) by positivity)
  rw [← hα]
  refine ⟨2 * ν * m₀, by positivity, (fr.and_eventually (ev1.and (ev2.and (ev3.and
    (ev4.and (ev5.and (eventually_ge_atTop 2))))))).mono ?_⟩
  rintro N ⟨hph, h1, h2, h3, h4, h5, hN2⟩
  rw [hs₀re] at h1
  have hneg := jasReal_tsum_neg_core (R := R) (θ := θ) (u := u) hN2 hδ0 hα hα0 hα1 hγ0 hq₁ hmax
    hgap hγγ₁ hs₀ hm₀ hm₀0 hμ₁ hμ₁0 hε3 (by rw [hρ₂, hρ₁]; positivity) (by rw [hθ, hw₀]) hν0 hνR
    hνu hv hW (by rw [← hw₀]; exact hRbig) hΛ₀ hΛ₀0 (by rw [← hw₀]; exact hFtail) hq₁F hε2 hε₂Λ
    hε₂0.le h1 h2 h3 h4 h5 hph
  exact ⟨hN2, h4.trans ((min_le_left _ _).trans (by norm_num)), hneg⟩

/-- **A single real phase detects every attained off-line zero.**  If a zero `ρ₀` off the critical
line has the largest distance `δ = |Re ρ₀ − ½|` from it among all zeros, then for every level
`δ < σ < 1 + δ` and every `X`, some real-amplitude kernel on the primes in `(X, N]` has negative
aggregate: `JasRealPositiveAbove X σ` fails. -/
theorem not_jasRealPositiveAbove_of_maximal_offLine (q₀ : XiZeroCopy)
    (hoff : (q₀.1 : ℂ).re ≠ 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) {σ : ℝ}
    (hσ0 : |(q₀.1 : ℂ).re - 1 / 2| < σ) (hσ1 : σ < 1 + |(q₀.1 : ℂ).re - 1 / 2|) (X : ℕ) :
    ¬ JasRealPositiveAbove X σ := by
  intro hpos
  obtain ⟨κ, hκ, hfr⟩ := frequently_jasReal_neg_of_maximal_offLine q₀ hoff hmax hσ0 hσ1 X
  obtain ⟨N, hN2, ha1, hneg⟩ := hfr.exists
  have ha0 : 0 ≤ κ / jasMainScale (σ - |(q₀.1 : ℂ).re - 1 / 2|) N :=
    div_nonneg hκ.le (jasMainScale_pos hN2).le
  exact absurd (hpos (jasPrimeWindow X N) (fun p hp => (mem_jasPrimeWindow.mp hp).1) _ ha0 ha1)
    (not_le.mpr hneg)

/-! ## The real budget law is sharp -/

/-- Real-amplitude positivity on the initial windows `(X, N]` within the prime budget
`t Σ_{p ≤ N} p^{−(σ−½)} ≤ N^λ`. -/
def JasRealBudgetPositiveAbove (X : ℕ) (σ lam : ℝ) : Prop :=
  ∀ N : ℕ, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → t * jasPrimeRpowSum (σ - 1 / 2) N ≤ (N : ℝ) ^ lam →
    0 ≤ (∑' q : XiZeroCopy, jasRealKernel (jasPrimeWindow X N) σ t (q.1 : ℂ) /
      ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re

/-- `E_α(N)/E_β(N) = N^{β−α}`. -/
theorem jasMainScale_div_jasMainScale (α β : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    jasMainScale β N / jasMainScale α N = (N : ℝ) ^ (α - β) := by
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog := Real.log_pos hN1
  have hNpos : (0 : ℝ) < N := by linarith
  rw [jasMainScale, jasMainScale, div_div_div_cancel_right₀ hlog.ne',
    ← Real.rpow_sub hNpos]
  congr 1
  ring

/-- **The real budget law is sharp at attained zeros.**  If an off-line zero at the largest
distance `δ` exists, `½ < σ < min (3/2) (1 + δ)` and `½ − δ < λ`, then real-amplitude positivity
fails already within the prime budget `N^λ`: the negative tests of
`frequently_jasReal_neg_of_maximal_offLine` satisfy `t Σ_{p≤N} p^{−(σ−½)} ≍ N^{½−δ}`. -/
theorem not_jasRealBudgetPositiveAbove_of_maximal_offLine (q₀ : XiZeroCopy)
    (hoff : (q₀.1 : ℂ).re ≠ 1 / 2)
    (hmax : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ |(q₀.1 : ℂ).re - 1 / 2|) {σ lam : ℝ}
    (hσ0 : |(q₀.1 : ℂ).re - 1 / 2| < σ) (hσ1 : σ < 1 + |(q₀.1 : ℂ).re - 1 / 2|)
    (hσ2 : 1 / 2 < σ) (hσ3 : σ < 3 / 2) (hlam : 1 / 2 - |(q₀.1 : ℂ).re - 1 / 2| < lam) (X : ℕ) :
    ¬ JasRealBudgetPositiveAbove X σ lam := by
  intro hpos
  obtain ⟨κ, hκ, hfr⟩ := frequently_jasReal_neg_of_maximal_offLine q₀ hoff hmax hσ0 hσ1 X
  set δ := |(q₀.1 : ℂ).re - 1 / 2| with hδ
  set C := 1 / (1 - (σ - 1 / 2)) + 1 with hC
  have hC0 : 0 < C := by rw [hC]; have : 0 < 1 - (σ - 1 / 2) := by linarith
                         positivity
  have hS := eventually_jasPrimeRpowSum_le_main (α := σ - 1 / 2) (by linarith) (by linarith)
    one_pos
  have hexp : 0 < lam - (1 / 2 - δ) := by linarith
  have hgrow : ∀ᶠ N : ℕ in atTop, κ * C ≤ (N : ℝ) ^ (lam - (1 / 2 - δ)) :=
    ((tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  have hbudget : ∀ᶠ N : ℕ in atTop,
      κ / jasMainScale (σ - δ) N * jasPrimeRpowSum (σ - 1 / 2) N ≤ (N : ℝ) ^ lam := by
    filter_upwards [hS, hgrow, eventually_ge_atTop 2] with N hSN hgN hN2
    have hE0 := jasMainScale_pos (α := σ - δ) hN2
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hratio := jasMainScale_div_jasMainScale (σ - δ) (σ - 1 / 2) hN2
    calc κ / jasMainScale (σ - δ) N * jasPrimeRpowSum (σ - 1 / 2) N
        ≤ κ / jasMainScale (σ - δ) N * (C * jasMainScale (σ - 1 / 2) N) :=
          mul_le_mul_of_nonneg_left (by rw [hC]; exact hSN) (div_nonneg hκ.le hE0.le)
      _ = κ * C * (jasMainScale (σ - 1 / 2) N / jasMainScale (σ - δ) N) := by
          field_simp
      _ = κ * C * (N : ℝ) ^ (1 / 2 - δ) := by rw [hratio]; congr 2; ring
      _ ≤ (N : ℝ) ^ (lam - (1 / 2 - δ)) * (N : ℝ) ^ (1 / 2 - δ) :=
          mul_le_mul_of_nonneg_right hgN (Real.rpow_nonneg hNpos.le _)
      _ = (N : ℝ) ^ lam := by rw [← Real.rpow_add hNpos]; congr 1; ring
  obtain ⟨N, ⟨hN2, ha1, hneg⟩, hb⟩ := (hfr.and_eventually hbudget).exists
  have ha0 : 0 ≤ κ / jasMainScale (σ - δ) N := div_nonneg hκ.le (jasMainScale_pos hN2).le
  exact absurd (hpos N _ ha0 ha1 hb) (not_le.mpr hneg)

end

end RHTower
