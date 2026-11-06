import GaloisForLFunctions.ArithmeticKreinLangerTheory.FinitePrimeHeckeAuxiliaryObstructions
import GaloisForLFunctions.RHTower.WindowBudget

/-!
# The forced jumps of a producer

A **producer** is a balanced integer stencil `c` whose multiplicity function
`g(r) = Σ c(k)⌊r/k⌋` is nonnegative and at least `m` on `[1, B)`. Its multiplicity increases by
`h(r) = Σ_{k ∣ r} c(k)`, the Dirichlet convolution `c * 1`. Three facts follow.

* **Forced jumps.** At every `r` divisible by no letter `k ≠ 1` of the alphabet, `h(r) = c(1) ≥ m`,
  so `g(r) ≥ m` above the window and `g(r) ≥ 2m` inside it. Every prime beyond the alphabet is such
  an `r`. Summed in the pronic series for the slope, this gives a polynomial floor
  `A(K) − 1 ≥ c₀ / (K (1 + log K))` for the normalized slope on alphabets `≤ K`.
* **Möbius rigidity.** `c = μ * h`, so the coefficients of a stencil are recovered from its
  multiplicities, and a constant window forces `c = m μ` on the window.
* **Coefficient bound.** Nonnegativity and the pronic series give `g(r) ≤ slope · r(r + 1)`, hence
  `|c(k)| ≤ 4 · slope · k²`. A producer of bounded slope has polynomially bounded coefficients, so the
  constant in its Chebyshev bound is polynomial in the alphabet:
  `ψ(x) ≤ A x + 8 K³ (5 + log K) (1 + log x) (1 + log x / log 2)` when `A ≤ 2`.
-/

open Finset
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- A balanced integer stencil with nonnegative multiplicity, at least `m ≥ 1` on `[1, B)`. -/
structure IsProducer (c : ℕ →₀ ℤ) (m B : ℕ) : Prop where
  zero : c 0 = 0
  balanced : IsBalanced c
  nonneg : ∀ r : ℕ, 0 ≤ stepWeight c r
  one_le_m : 1 ≤ m
  two_le_B : 2 ≤ B
  window : ∀ r ∈ Ico 1 B, (m : ℤ) ≤ stepWeight c r

/-- The normalized slope `slope / (m (1 − 1/B))`, the constant in the Chebyshev bound. -/
def normSlope (c : ℕ →₀ ℤ) (m B : ℕ) : ℝ := stencilSlope c / ((m : ℝ) * (1 - 1 / (B : ℝ)))

/-- The excess of the slope over the main term: the tail mass `Σ (g − m 1_{[1,B)}) / (r (r+1))`. -/
def excess (c : ℕ →₀ ℤ) (m B : ℕ) : ℝ := stencilSlope c - (m : ℝ) * (1 - 1 / (B : ℝ))

/-- The alphabet of the stencil lies in `[1, K]`. -/
def AlphabetLE (c : ℕ →₀ ℤ) (K : ℕ) : Prop := ∀ k ∈ c.support, k ≤ K

/-- The increment `h(r) = Σ_{k ∣ r} c(k)` of the multiplicity. -/
def increment (c : ℕ →₀ ℤ) (r : ℕ) : ℤ := ∑ k ∈ c.support, if k ∣ r then c k else 0

/-- `r` is divisible by no letter of the alphabet other than `1`. -/
def IsRough (c : ℕ →₀ ℤ) (r : ℕ) : Prop := ∀ k ∈ c.support, k ≠ 1 → ¬ k ∣ r

theorem stepWeight_succ (c : ℕ →₀ ℤ) (r : ℕ) :
    stepWeight c (r + 1) = stepWeight c r + increment c (r + 1) := by
  simp only [stepWeight, increment, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  rw [Nat.succ_div]
  split_ifs <;> push_cast <;> ring

/-- `h = c * 1` on the positive integers. -/
theorem increment_eq_sum_divisors {c : ℕ →₀ ℤ} {r : ℕ} (hr : 0 < r) :
    increment c r = ∑ d ∈ r.divisors, c d := by
  classical
  rw [increment, ← sum_filter]
  refine sum_subset (fun k hk => ?_) (fun k _ hk => ?_)
  · exact Nat.mem_divisors.mpr ⟨(mem_filter.mp hk).2, hr.ne'⟩
  · by_contra hne
    exact hk (mem_filter.mpr ⟨Finsupp.mem_support_iff.mpr hne,
      (Nat.mem_divisors.mp ‹k ∈ r.divisors›).1⟩)

/-- **Möbius rigidity.** The coefficients are the Möbius inversion of the increments. -/
theorem coeff_eq_moebius_increment (c : ℕ →₀ ℤ) {n : ℕ} (hn : 0 < n) :
    c n = ∑ x ∈ n.divisorsAntidiagonal, ArithmeticFunction.moebius x.1 * increment c x.2 := by
  have h := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq (R := ℤ) (f := fun d => c d)
    (g := increment c)).mp (fun m hm => (increment_eq_sum_divisors hm).symm) n hn
  simpa using h.symm

/-- **A constant window is Möbius.** If the multiplicity is the constant `m` on `[1, B)`, then
`c(n) = m μ(n)` for `n < B`. -/
theorem coeff_eq_of_constant_window {c : ℕ →₀ ℤ} {m : ℤ} {B : ℕ}
    (hconst : ∀ r ∈ Ico 1 B, stepWeight c r = m) {n : ℕ} (hn : 0 < n) (hnB : n < B) :
    c n = m * ArithmeticFunction.moebius n := by
  have hinc : ∀ d, 0 < d → d < B → increment c d = if d = 1 then m else 0 := by
    intro d hd hdB
    obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
    have h := stepWeight_succ c e
    rcases Nat.eq_zero_or_pos e with rfl | he
    · have h1 := hconst 1 (mem_Ico.mpr ⟨le_rfl, hdB⟩)
      have h0 : stepWeight c 0 = 0 := stepWeight_zero c
      simp only [zero_add] at h ⊢
      simp only [if_true]
      linarith
    · have h1 := hconst (e + 1) (mem_Ico.mpr ⟨by omega, hdB⟩)
      have h2 := hconst e (mem_Ico.mpr ⟨he, by omega⟩)
      rw [if_neg (by omega)]
      linarith
  rw [coeff_eq_moebius_increment c hn, sum_congr rfl (g := fun x : ℕ × ℕ =>
    ArithmeticFunction.moebius x.1 * if x.2 = 1 then m else 0)]
  · rw [sum_eq_single (n, 1)]
    · simp [mul_comm]
    · rintro ⟨a, b⟩ hab hne
      have hb : b ≠ 1 := by
        rintro rfl
        have : a = n := by simpa using (Nat.mem_divisorsAntidiagonal.mp hab).1
        exact hne (by rw [this])
      simp [hb]
    · intro h
      exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨mul_one n, hn.ne'⟩) h
  · rintro ⟨a, b⟩ hab
    obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hab
    have hb : 0 < b := Nat.pos_of_ne_zero fun h => hn0 (by rw [← hprod, h, mul_zero])
    have hbn : b ≤ n := Nat.le_of_dvd hn ⟨a, by rw [← hprod, mul_comm]⟩
    simp only
    rw [hinc b hb (by omega)]

/-- At a rough `r` the increment is `c(1)`. -/
theorem increment_of_isRough {c : ℕ →₀ ℤ} {r : ℕ} (hr : IsRough c r) : increment c r = c 1 := by
  classical
  rw [increment]
  by_cases h1 : 1 ∈ c.support
  · rw [sum_eq_single 1]
    · simp
    · intro k hk hk1
      rw [if_neg (hr k hk hk1)]
    · intro h; exact absurd h1 h
  · rw [Finsupp.notMem_support_iff.mp h1, sum_eq_zero]
    intro k hk
    have hk1 : k ≠ 1 := fun h => h1 (h ▸ hk)
    rw [if_neg (hr k hk hk1)]

/-- A prime beyond the alphabet is rough. -/
theorem isRough_of_prime_of_alphabet {c : ℕ →₀ ℤ} {K p : ℕ} (hK : AlphabetLE c K)
    (hp : p.Prime) (hpK : K < p) : IsRough c p := by
  intro k hk hk1 hdvd
  have := (Nat.dvd_prime hp).mp hdvd
  rcases this with h | h
  · exact hk1 h
  · have := hK k hk
    omega

namespace IsProducer

variable {c : ℕ →₀ ℤ} {m B : ℕ}

theorem m_pos (hP : IsProducer c m B) : (0 : ℝ) < m := by exact_mod_cast hP.one_le_m

theorem one_lt_B (hP : IsProducer c m B) : (1 : ℝ) < B := by exact_mod_cast hP.two_le_B

theorem one_sub_pos (hP : IsProducer c m B) : 0 < 1 - 1 / (B : ℝ) := by
  have h := hP.one_lt_B
  rw [sub_pos, div_lt_one (by linarith)]
  exact h

/-- The first coefficient is the multiplicity at `1`, so it is at least `m`. -/
theorem le_coeff_one (hP : IsProducer c m B) : (m : ℤ) ≤ c 1 := by
  have h := hP.window 1 (mem_Ico.mpr ⟨le_rfl, by have := hP.two_le_B; omega⟩)
  rwa [stepWeight_one hP.zero] at h

/-- The pronic series for the slope. -/
theorem hasSum_slope (hP : IsProducer c m B) :
    HasSum (fun j : ℕ => (stepWeight c (j + 1) : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2)))
      (stencilSlope c) :=
  hasSum_stepWeight_div_pronic hP.zero hP.balanced

/-- **The multiplicity is bounded by the slope.** `g(r) ≤ slope · r (r + 1)`. -/
theorem stepWeight_le_slope (hP : IsProducer c m B) (j : ℕ) :
    (stepWeight c (j + 1) : ℝ) ≤ stencilSlope c * (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
  have hpos : 0 < ((j : ℝ) + 1) * ((j : ℝ) + 2) := by positivity
  have hle := le_hasSum hP.hasSum_slope j fun i _ =>
    div_nonneg (by exact_mod_cast hP.nonneg (i + 1)) (by positivity)
  rwa [div_le_iff₀ hpos] at hle

theorem slope_nonneg (hP : IsProducer c m B) : 0 ≤ stencilSlope c :=
  stencilSlope_nonneg hP.zero hP.balanced hP.nonneg

/-- **The increment is bounded by the slope.** `|h(r)| ≤ slope · r (r + 1)` for `r ≥ 1`. -/
theorem abs_increment_le (hP : IsProducer c m B) {r : ℕ} (hr : 0 < r) :
    |(increment c r : ℝ)| ≤ stencilSlope c * ((r : ℝ) * ((r : ℝ) + 1)) := by
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
  have hS := hP.slope_nonneg
  have hsucc : (stepWeight c (j + 1) : ℝ) = stepWeight c j + increment c (j + 1) := by
    exact_mod_cast stepWeight_succ c j
  have hcast : (((j + 1 : ℕ) : ℝ)) = (j : ℝ) + 1 := by push_cast; rfl
  rw [hcast]
  have hupper : (stepWeight c (j + 1) : ℝ) ≤
      stencilSlope c * (((j : ℝ) + 1) * ((j : ℝ) + 1 + 1)) := by
    have := hP.stepWeight_le_slope j
    rwa [show (j : ℝ) + 2 = (j : ℝ) + 1 + 1 by ring] at this
  have hprev : (stepWeight c j : ℝ) ≤ stencilSlope c * (((j : ℝ) + 1) * ((j : ℝ) + 1 + 1)) := by
    rcases Nat.eq_zero_or_pos j with rfl | hj
    · rw [stepWeight_zero]
      push_cast
      positivity
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      refine (hP.stepWeight_le_slope i).trans (mul_le_mul_of_nonneg_left ?_ hS)
      push_cast
      nlinarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
  have h0 : (0 : ℝ) ≤ stepWeight c (j + 1) := by exact_mod_cast hP.nonneg (j + 1)
  have h1 : (0 : ℝ) ≤ stepWeight c j := by exact_mod_cast hP.nonneg j
  rw [abs_le]
  constructor <;> linarith

end IsProducer

/-- `Σ_{d ≤ n} 1/d² ≤ 2`. -/
private lemma sum_Icc_inv_sq_le (n : ℕ) : ∑ d ∈ Icc 1 n, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 2 := by
  have h : ∀ n : ℕ, ∑ d ∈ Icc 1 (n + 1), (1 : ℝ) / (d : ℝ) ^ 2 ≤ 2 - 1 / ((n : ℝ) + 1) := by
    intro n
    induction n with
    | zero => simp; norm_num
    | succ n ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hstep : (1 : ℝ) / (((n + 1 + 1 : ℕ) : ℝ)) ^ 2 ≤
          1 / ((n : ℝ) + 1) - 1 / (((n + 1 : ℕ) : ℝ) + 1) := by
        push_cast
        rw [div_sub_div _ _ hn.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      linarith
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · obtain ⟨j, rfl⟩ : ∃ j, n = j + 1 := ⟨n - 1, by omega⟩
    have hj : (0 : ℝ) ≤ 1 / ((j : ℝ) + 1) := by positivity
    linarith [h j]

/-- `Σ_{d ∣ n} d (d + 1) ≤ 4 n²`. -/
private lemma sum_divisors_pronic_le {n : ℕ} (hn : 0 < n) :
    ∑ d ∈ n.divisors, (d : ℝ) * ((d : ℝ) + 1) ≤ 4 * (n : ℝ) ^ 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hterm : ∀ d ∈ n.divisors, (d : ℝ) * ((d : ℝ) + 1) ≤ 2 * (d : ℝ) ^ 2 := by
    intro d hd
    have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast Nat.pos_of_mem_divisors hd
    nlinarith
  have hflip : ∑ d ∈ n.divisors, (d : ℝ) ^ 2 = ∑ d ∈ n.divisors, ((n / d : ℕ) : ℝ) ^ 2 :=
    (Nat.sum_div_divisors n fun d => (d : ℝ) ^ 2).symm
  have hdiv : ∀ d ∈ n.divisors, ((n / d : ℕ) : ℝ) ^ 2 = (n : ℝ) ^ 2 * (1 / (d : ℝ) ^ 2) := by
    intro d hd
    rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd)
      (Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne')]
    ring
  have hsub : n.divisors ⊆ Icc 1 n := fun d hd =>
    mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.divisor_le hd⟩
  have hsum : ∑ d ∈ n.divisors, (1 : ℝ) / (d : ℝ) ^ 2 ≤ 2 :=
    (sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans (sum_Icc_inv_sq_le n)
  calc ∑ d ∈ n.divisors, (d : ℝ) * ((d : ℝ) + 1)
      ≤ ∑ d ∈ n.divisors, 2 * (d : ℝ) ^ 2 := sum_le_sum hterm
    _ = 2 * ((n : ℝ) ^ 2 * ∑ d ∈ n.divisors, (1 : ℝ) / (d : ℝ) ^ 2) := by
        rw [← mul_sum, hflip, sum_congr rfl hdiv, ← mul_sum]
    _ ≤ 2 * ((n : ℝ) ^ 2 * 2) := by gcongr
    _ = 4 * (n : ℝ) ^ 2 := by ring

namespace IsProducer

variable {c : ℕ →₀ ℤ} {m B : ℕ}

/-- **The coefficient bound.** A producer has `|c(n)| ≤ 4 · slope · n²`. -/
theorem abs_coeff_le (hP : IsProducer c m B) {n : ℕ} (hn : 0 < n) :
    |(c n : ℝ)| ≤ 4 * stencilSlope c * (n : ℝ) ^ 2 := by
  have hS := hP.slope_nonneg
  rw [coeff_eq_moebius_increment c hn]
  push_cast
  calc |∑ x ∈ n.divisorsAntidiagonal,
        ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) * (increment c x.2 : ℝ)|
      ≤ ∑ x ∈ n.divisorsAntidiagonal,
        |((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) * (increment c x.2 : ℝ)| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ x ∈ n.divisorsAntidiagonal,
        stencilSlope c * ((x.2 : ℝ) * ((x.2 : ℝ) + 1)) := by
        refine sum_le_sum fun x hx => ?_
        obtain ⟨hprod, hn0⟩ := Nat.mem_divisorsAntidiagonal.mp hx
        have hb : 0 < x.2 := Nat.pos_of_ne_zero fun h => hn0 (by rw [← hprod, h, mul_zero])
        have hmu : |((ArithmeticFunction.moebius x.1 : ℤ) : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one
        rw [abs_mul]
        calc _ ≤ 1 * |(increment c x.2 : ℝ)| := by gcongr
          _ = |(increment c x.2 : ℝ)| := one_mul _
          _ ≤ _ := hP.abs_increment_le hb
    _ = stencilSlope c * ∑ d ∈ n.divisors, (d : ℝ) * ((d : ℝ) + 1) := by
        rw [← mul_sum]
        congr 1
        exact Nat.sum_divisorsAntidiagonal' (fun _ b => (b : ℝ) * ((b : ℝ) + 1))
    _ ≤ stencilSlope c * (4 * (n : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left (sum_divisors_pronic_le hn) hS
    _ = 4 * stencilSlope c * (n : ℝ) ^ 2 := by ring

theorem support_subset_Icc (hP : IsProducer c m B) {K : ℕ} (hK : AlphabetLE c K) :
    c.support ⊆ Icc 1 K := fun k hk => mem_Icc.mpr
  ⟨Nat.pos_of_ne_zero fun h => by subst h; exact Finsupp.mem_support_iff.mp hk hP.zero, hK k hk⟩

/-- **The polynomial error constant.** `E ≤ 4 · slope · K³ · (5 + log K)`. -/
theorem stencilErrorConst_le (hP : IsProducer c m B) {K : ℕ} (hK : AlphabetLE c K) :
    stencilErrorConst c ≤ 4 * stencilSlope c * (K : ℝ) ^ 3 * (5 + Real.log K) := by
  have hS := hP.slope_nonneg
  have hsub := hP.support_subset_Icc hK
  have hterm : ∀ k ∈ c.support, |(c k : ℝ)| * (3 + Real.log k + 2) ≤
      (4 * stencilSlope c * (K : ℝ) ^ 2) * (5 + Real.log K) := by
    intro k hk
    obtain ⟨hk1, hkK⟩ := mem_Icc.mp (hsub hk)
    have hk1R : (1 : ℝ) ≤ k := by exact_mod_cast hk1
    have hkKR : (k : ℝ) ≤ K := by exact_mod_cast hkK
    have hlog : Real.log k ≤ Real.log K := Real.log_le_log (by linarith) hkKR
    have hlog0 : 0 ≤ Real.log k := Real.log_nonneg hk1R
    have hc := hP.abs_coeff_le (n := k) hk1
    have hsq : (k : ℝ) ^ 2 ≤ (K : ℝ) ^ 2 := by gcongr
    exact mul_le_mul (hc.trans (mul_le_mul_of_nonneg_left hsq (by positivity)))
      (by linarith) (by linarith) (by positivity)
  have hcard : (c.support.card : ℝ) ≤ K := by
    have := card_le_card hsub
    rw [Nat.card_Icc] at this
    exact_mod_cast (by omega : c.support.card ≤ K)
  have hlogK : 0 ≤ 5 + Real.log K := by
    have : 0 ≤ Real.log K := Real.log_natCast_nonneg K
    linarith
  calc stencilErrorConst c
      ≤ ∑ _k ∈ c.support, (4 * stencilSlope c * (K : ℝ) ^ 2) * (5 + Real.log K) := sum_le_sum hterm
    _ = (c.support.card : ℝ) * ((4 * stencilSlope c * (K : ℝ) ^ 2) * (5 + Real.log K)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (K : ℝ) * ((4 * stencilSlope c * (K : ℝ) ^ 2) * (5 + Real.log K)) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = 4 * stencilSlope c * (K : ℝ) ^ 3 * (5 + Real.log K) := by ring

/-- The terms of the excess series. -/
def excessTerm (m B : ℕ) (c : ℕ →₀ ℤ) (j : ℕ) : ℝ :=
  ((stepWeight c (j + 1) : ℝ) - (if j + 1 < B then (m : ℝ) else 0)) /
    (((j : ℝ) + 1) * ((j : ℝ) + 2))

private lemma sum_window_pronic (hB : 1 ≤ B) :
    ∑ j ∈ range (B - 1), (1 : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) = 1 - 1 / (B : ℝ) := by
  obtain ⟨n, rfl⟩ : ∃ n, B = n + 1 := ⟨B - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih (by omega)]
    push_cast
    field_simp
    ring

/-- **The excess series.** `excess = Σ (g(r) − m 1_{r<B}) / (r (r+1))`. -/
theorem hasSum_excess (hP : IsProducer c m B) :
    HasSum (excessTerm m B c) (excess c m B) := by
  have hwin : HasSum (fun j : ℕ => (if j + 1 < B then (m : ℝ) else 0) /
      (((j : ℝ) + 1) * ((j : ℝ) + 2))) ((m : ℝ) * (1 - 1 / (B : ℝ))) := by
    have hfin : ∑ j ∈ range (B - 1), (if j + 1 < B then (m : ℝ) else 0) /
        (((j : ℝ) + 1) * ((j : ℝ) + 2)) = (m : ℝ) * (1 - 1 / (B : ℝ)) := by
      rw [← sum_window_pronic (by have := hP.two_le_B; omega), mul_sum]
      refine sum_congr rfl fun j hj => ?_
      rw [if_pos (by have := mem_range.mp hj; omega)]
      ring
    rw [← hfin]
    refine hasSum_sum_of_ne_finset_zero fun j hj => ?_
    rw [if_neg (by
      have := mem_range.not.mp hj
      omega), zero_div]
  have hfun : excessTerm m B c = fun j : ℕ =>
      (stepWeight c (j + 1) : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) -
        (if j + 1 < B then (m : ℝ) else 0) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
    funext j
    simp only [excessTerm, sub_div]
  rw [hfun]
  exact hP.hasSum_slope.sub hwin

theorem excessTerm_nonneg (hP : IsProducer c m B) (j : ℕ) : 0 ≤ excessTerm m B c j := by
  refine div_nonneg ?_ (by positivity)
  split_ifs with h
  · have := hP.window (j + 1) (mem_Ico.mpr ⟨by omega, h⟩)
    have hR : (m : ℝ) ≤ stepWeight c (j + 1) := by exact_mod_cast this
    linarith
  · have hR : (0 : ℝ) ≤ stepWeight c (j + 1) := by exact_mod_cast hP.nonneg (j + 1)
    linarith

theorem excess_nonneg (hP : IsProducer c m B) : 0 ≤ excess c m B :=
  hP.hasSum_excess.nonneg hP.excessTerm_nonneg

/-- **The jump at a rough point.** A rough `r ≥ 2` contributes at least `m / (r (r + 1))` to the
excess: above the window `g(r) ≥ m`, and inside it `g(r) ≥ 2m`. -/
theorem le_excessTerm_of_isRough (hP : IsProducer c m B) {j : ℕ} (hj : 1 ≤ j)
    (hr : IsRough c (j + 1)) :
    (m : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) ≤ excessTerm m B c j := by
  have hpos : 0 < ((j : ℝ) + 1) * ((j : ℝ) + 2) := by positivity
  refine div_le_div_of_nonneg_right ?_ hpos.le
  have hs := stepWeight_succ c j
  rw [increment_of_isRough hr] at hs
  have hc1 : (m : ℝ) ≤ c 1 := by exact_mod_cast hP.le_coeff_one
  have hsR : (stepWeight c (j + 1) : ℝ) = stepWeight c j + c 1 := by exact_mod_cast hs
  split_ifs with h
  · have := hP.window j (mem_Ico.mpr ⟨hj, by omega⟩)
    have hR : (m : ℝ) ≤ stepWeight c j := by exact_mod_cast this
    linarith
  · have hR : (0 : ℝ) ≤ stepWeight c j := by exact_mod_cast hP.nonneg j
    linarith

/-- **The rough floor.** Every finite set of rough `r ≥ 2` bounds the excess from below. -/
theorem sum_rough_le_excess (hP : IsProducer c m B) (R : Finset ℕ)
    (hR : ∀ r ∈ R, 2 ≤ r ∧ IsRough c r) :
    (m : ℝ) * ∑ r ∈ R, 1 / ((r : ℝ) * ((r : ℝ) + 1)) ≤ excess c m B := by
  classical
  have hinj : Set.InjOn (fun r : ℕ => r - 1) (R : Set ℕ) := by
    intro a ha b hb hab
    have h1 := (hR a ha).1
    have h2 := (hR b hb).1
    simp only at hab
    omega
  have hsum := sum_le_hasSum (R.image fun r => r - 1)
    (fun j _ => hP.excessTerm_nonneg j) hP.hasSum_excess
  rw [sum_image hinj] at hsum
  refine le_trans ?_ hsum
  rw [mul_sum]
  refine sum_le_sum fun r hr => ?_
  obtain ⟨h2, hrough⟩ := hR r hr
  obtain ⟨j, rfl⟩ : ∃ j, r = j + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have := hP.le_excessTerm_of_isRough (j := j) (by omega) hrough
  calc (m : ℝ) * (1 / (((j + 1 : ℕ) : ℝ) * (((j + 1 : ℕ) : ℝ) + 1)))
      = (m : ℝ) / (((j : ℝ) + 1) * ((j : ℝ) + 2)) := by
        push_cast
        rw [show (j : ℝ) + 1 + 1 = (j : ℝ) + 2 by ring, mul_one_div]
    _ ≤ _ := this

/-- The normalized slope is `1` plus at least the excess per unit of `m`. -/
theorem one_add_excess_div_le_normSlope (hP : IsProducer c m B) :
    1 + excess c m B / m ≤ normSlope c m B := by
  have hm := hP.m_pos
  have h1 := hP.one_sub_pos
  have hB : (0 : ℝ) < 1 / (B : ℝ) := by have := hP.one_lt_B; positivity
  have hE := hP.excess_nonneg
  have hle : 1 - 1 / (B : ℝ) ≤ 1 := by linarith
  have hdenom : 0 < (m : ℝ) * (1 - 1 / (B : ℝ)) := mul_pos hm h1
  rw [normSlope, le_div_iff₀ hdenom]
  have hS : stencilSlope c = excess c m B + (m : ℝ) * (1 - 1 / (B : ℝ)) := by
    rw [excess]; ring
  rw [hS]
  have hdiv : 0 ≤ excess c m B / m := div_nonneg hE hm.le
  have hX : excess c m B / m * (m * (1 - 1 / (B : ℝ))) ≤ excess c m B := by
    calc excess c m B / m * (m * (1 - 1 / (B : ℝ)))
        = excess c m B * (1 - 1 / (B : ℝ)) := by field_simp
      _ ≤ excess c m B * 1 := by gcongr
      _ = excess c m B := mul_one _
  nlinarith

/-- **The Chebyshev bound with its constant.** For `x ≥ 1`,
`ψ(x) ≤ A x + (E/m)(1 + log x)(1 + log x / log 2)`, `A` the normalized slope and `E` the Stirling
error constant. -/
theorem psi_le (hP : IsProducer c m B) {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.psi x ≤ normSlope c m B * x +
      (stencilErrorConst c / m) * (1 + Real.log x) * (1 + Real.log x / Real.log 2) := by
  have hm := hP.m_pos
  have h1B := hP.one_sub_pos
  have hS := hP.slope_nonneg
  have hE : 0 ≤ stencilErrorConst c / m := div_nonneg (stencilErrorConst_nonneg c) hm.le
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hB := hP.two_le_B
  have hA : 0 ≤ normSlope c m B := div_nonneg hS (mul_pos hm h1B).le
  have hstep : ∀ n : ℕ, 1 ≤ n → Chebyshev.psi n - Chebyshev.psi (n / B : ℕ) ≤
      (stencilSlope c / m) * n + (stencilErrorConst c / m) * (1 + Real.log n) := by
    intro n hn
    have hpsi := psi_sub_le_log_stencilInt hP.zero hP.nonneg hP.window (by omega) n
    have hst := (abs_le.mp (abs_log_stencilInt_sub_slope_le hP.zero hP.balanced hP.nonneg hn)).2
    rw [show (stencilSlope c / m) * (n : ℝ) + (stencilErrorConst c / m) * (1 + Real.log n) =
      (stencilSlope c * n + stencilErrorConst c * (1 + Real.log n)) / m by ring, le_div_iff₀ hm]
    linarith
  have hmain : ∀ n : ℕ, 1 ≤ n → Chebyshev.psi n ≤ normSlope c m B * n +
      (stencilErrorConst c / m) * (1 + Real.log n) * (1 + Real.log n / Real.log 2) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro hn
      have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hlogn : 0 ≤ Real.log n := Real.log_nonneg hnR
      have hdecomp : normSlope c m B * (1 - 1 / (B : ℝ)) = stencilSlope c / m := by
        rw [normSlope, div_mul_eq_mul_div, div_eq_div_iff (mul_pos hm h1B).ne' hm.ne']
        ring
      have hAB : stencilSlope c / m ≤ normSlope c m B := by
        rw [← hdecomp]
        have : 1 - 1 / (B : ℝ) ≤ 1 := by
          have : (0 : ℝ) ≤ 1 / (B : ℝ) := by positivity
          linarith
        nlinarith
      have hdiv2 : 0 ≤ Real.log n / Real.log 2 := div_nonneg hlogn hlog2.le
      have hs := hstep n hn
      rcases Nat.eq_zero_or_pos (n / B) with h0 | hpos
      · rw [h0, Nat.cast_zero, Chebyshev.psi_zero, sub_zero] at hs
        have hE1 : (stencilErrorConst c / m) * (1 + Real.log n) ≤
            (stencilErrorConst c / m) * (1 + Real.log n) * (1 + Real.log n / Real.log 2) := by
          have : 0 ≤ (stencilErrorConst c / m) * (1 + Real.log n) := by positivity
          nlinarith
        nlinarith
      · have hlt : n / B < n := Nat.div_lt_self (by omega) (by omega)
        have hih := ih (n / B) hlt hpos
        have hn'R : (1 : ℝ) ≤ ((n / B : ℕ) : ℝ) := by exact_mod_cast hpos
        have hBR : (0 : ℝ) < B := by exact_mod_cast (by omega : 0 < B)
        have hdivle : ((n / B : ℕ) : ℝ) ≤ (n : ℝ) / B := Nat.cast_div_le
        have hBdiv2 : ((n / B : ℕ) : ℝ) ≤ (n : ℝ) / 2 := by
          refine hdivle.trans (div_le_div_of_nonneg_left (by linarith) (by norm_num) ?_)
          exact_mod_cast hB
        have hlogle : Real.log ((n / B : ℕ) : ℝ) ≤ Real.log n - Real.log 2 := by
          calc Real.log ((n / B : ℕ) : ℝ) ≤ Real.log ((n : ℝ) / 2) :=
                Real.log_le_log (by linarith) hBdiv2
            _ = Real.log n - Real.log 2 := Real.log_div (by linarith) (by norm_num)
        have hlog' : 0 ≤ Real.log ((n / B : ℕ) : ℝ) := Real.log_nonneg hn'R
        have hq : 1 + Real.log ((n / B : ℕ) : ℝ) / Real.log 2 ≤ Real.log n / Real.log 2 := by
          have : Real.log ((n / B : ℕ) : ℝ) / Real.log 2 ≤ Real.log n / Real.log 2 - 1 := by
            rw [div_le_iff₀ hlog2]
            have : (Real.log n / Real.log 2 - 1) * Real.log 2 = Real.log n - Real.log 2 := by
              field_simp
            linarith
          linarith
        have hprod : (1 + Real.log ((n / B : ℕ) : ℝ)) * (1 + Real.log ((n / B : ℕ) : ℝ) / Real.log 2) ≤
            (1 + Real.log n) * (Real.log n / Real.log 2) :=
          mul_le_mul (by linarith) hq (by positivity) (by positivity)
        have hEprod := mul_le_mul_of_nonneg_left hprod hE
        have hAmain : normSlope c m B * ((n / B : ℕ) : ℝ) + (stencilSlope c / m) * n ≤
            normSlope c m B * n := by
          have hdiv : normSlope c m B * ((n / B : ℕ) : ℝ) ≤ normSlope c m B * ((n : ℝ) / B) :=
            mul_le_mul_of_nonneg_left hdivle hA
          rw [← hdecomp]
          have hid : normSlope c m B * ((n : ℝ) / B) + normSlope c m B * (1 - 1 / (B : ℝ)) * n =
              normSlope c m B * n := by
            field_simp
            ring
          linarith
        have hfinal : (stencilErrorConst c / m) * (1 + Real.log n) * (Real.log n / Real.log 2) +
            (stencilErrorConst c / m) * (1 + Real.log n) =
            (stencilErrorConst c / m) * (1 + Real.log n) * (1 + Real.log n / Real.log 2) := by ring
        have hE' : (stencilErrorConst c / m) * ((1 + Real.log ((n / B : ℕ) : ℝ)) *
            (1 + Real.log ((n / B : ℕ) : ℝ) / Real.log 2)) =
            (stencilErrorConst c / m) * (1 + Real.log ((n / B : ℕ) : ℝ)) *
            (1 + Real.log ((n / B : ℕ) : ℝ) / Real.log 2) := by ring
        have hE'' : (stencilErrorConst c / m) * ((1 + Real.log n) * (Real.log n / Real.log 2)) =
            (stencilErrorConst c / m) * (1 + Real.log n) * (Real.log n / Real.log 2) := by ring
        linarith
  set N := ⌊x⌋₊
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hx)
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hpsi_eq : Chebyshev.psi x = Chebyshev.psi (N : ℝ) := by
    rw [Chebyshev.psi, Chebyshev.psi, Nat.floor_natCast]
  rw [hpsi_eq]
  have hlog_le : Real.log N ≤ Real.log x := Real.log_le_log (by linarith) hNx
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg hNR
  refine (hmain N hN1).trans (add_le_add (mul_le_mul_of_nonneg_left hNx hA) ?_)
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  refine mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hE) ?_ (by positivity)
    (mul_nonneg hE (by linarith))
  have : Real.log N / Real.log 2 ≤ Real.log x / Real.log 2 :=
    div_le_div_of_nonneg_right hlog_le hlog2.le
  linarith

/-- **The explicit constant `C_ε`.** A producer on alphabet `≤ K` with `A ≤ 2` has
`ψ(x) ≤ A x + 8 K³ (5 + log K)(1 + log x)(1 + log x / log 2)`. No duality constant survives: the
constant is polynomial in the alphabet. -/
theorem psi_le_of_alphabet (hP : IsProducer c m B) {K : ℕ} (hK : AlphabetLE c K)
    (hA : normSlope c m B ≤ 2) {x : ℝ} (hx : 1 ≤ x) :
    Chebyshev.psi x ≤ normSlope c m B * x +
      8 * (K : ℝ) ^ 3 * (5 + Real.log K) * (1 + Real.log x) * (1 + Real.log x / Real.log 2) := by
  have hm := hP.m_pos
  have h1B := hP.one_sub_pos
  have hslope : stencilSlope c / m ≤ 2 := by
    have hle : 1 - 1 / (B : ℝ) ≤ 1 := by
      have : (0 : ℝ) ≤ 1 / (B : ℝ) := by positivity
      linarith
    have hid : normSlope c m B * (1 - 1 / (B : ℝ)) = stencilSlope c / m := by
      rw [normSlope, div_mul_eq_mul_div, div_eq_div_iff (mul_pos hm h1B).ne' hm.ne']
      ring
    have hA0 : 0 ≤ normSlope c m B := div_nonneg hP.slope_nonneg (mul_pos hm h1B).le
    rw [← hid]
    nlinarith
  have hlogK : 0 ≤ 5 + Real.log K := by
    have : 0 ≤ Real.log K := Real.log_natCast_nonneg K
    linarith
  have hEm : stencilErrorConst c / m ≤ 8 * (K : ℝ) ^ 3 * (5 + Real.log K) := by
    rw [div_le_iff₀ hm]
    have hE := hP.stencilErrorConst_le hK
    have hS : stencilSlope c ≤ 2 * m := by rwa [div_le_iff₀ hm] at hslope
    refine hE.trans ?_
    have hK3 : 0 ≤ (K : ℝ) ^ 3 * (5 + Real.log K) := by positivity
    nlinarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hfac : 0 ≤ (1 + Real.log x) * (1 + Real.log x / Real.log 2) := by positivity
  have h := hP.psi_le hx
  have hmul := mul_le_mul_of_nonneg_right hEm hfac
  nlinarith

end IsProducer

/-- The Chebyshev window of width `2²⁴ K` holds at least `K / log(2²⁴ K)` primes. -/
private lemma window_card_lower {K : ℝ} (hK : 1 ≤ K) :
    K ≤ ((RHTower.windowPrimes K (2 ^ 24 * K)).card : ℝ) * Real.log (2 ^ 24 * K) := by
  set y : ℝ := 2 ^ 24 * K with hy
  have hy0 : (2 : ℝ) ^ 24 ≤ y := by rw [hy]; nlinarith
  have hKy : K ≤ y := by rw [hy]; nlinarith
  refine le_trans ?_ (RHTower.windowPrimes_card_ge hK hKy)
  set u : ℝ := √(√y) with hu
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hy_pos : 0 < y := by linarith [show (0 : ℝ) < 2 ^ 24 by norm_num]
  have hs : √y = u ^ 2 := (Real.sq_sqrt (Real.sqrt_nonneg y)).symm
  have hyu : y = u ^ 4 := by
    have := Real.sq_sqrt hy_pos.le
    rw [hs] at this
    rw [← this]; ring
  have hu64 : 64 ≤ u := by
    by_contra hlt
    push Not at hlt
    have : u ^ 4 < 64 ^ 4 := pow_lt_pow_left₀ hlt hu0 (by norm_num)
    rw [← hyu] at this
    norm_num at this hy0
    linarith
  have hlog_u : Real.log y ≤ 4 * u := by
    have hupos : 0 < u := by linarith
    rw [hyu, Real.log_pow]
    have := Real.log_le_sub_one_of_pos hupos
    push_cast
    linarith
  have hu3 : 64 * u ^ 3 ≤ y := by
    rw [hyu]
    calc 64 * u ^ 3 ≤ u * u ^ 3 := by gcongr
      _ = u ^ 4 := by ring
  have hmain : 2 * √y * Real.log y ≤ y / 8 := by
    rw [hs]
    have h2 : 2 * u ^ 2 * Real.log y ≤ 2 * u ^ 2 * (4 * u) :=
      mul_le_mul_of_nonneg_left hlog_u (by positivity)
    nlinarith
  have hlogy2 : Real.log (y + 2) ≤ y / 16 := by
    have h2y : y + 2 ≤ 2 * y := by linarith [show (2 : ℝ) ≤ 2 ^ 24 by norm_num]
    have h1 : Real.log (y + 2) ≤ Real.log 2 + Real.log y := by
      rw [← Real.log_mul (by norm_num) hy_pos.ne']
      exact Real.log_le_log (by linarith) h2y
    have hl2 : Real.log 2 ≤ 1 := by
      have := Real.log_two_lt_d9
      linarith
    have huy : 64 ^ 3 * u ≤ y := by
      rw [hyu]
      calc 64 ^ 3 * u ≤ u ^ 3 * u := by gcongr
        _ = u ^ 4 := by ring
    nlinarith
  have hl2lo : (69 : ℝ) / 100 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  have hl2hi : Real.log 2 ≤ 7 / 10 := by
    have := Real.log_two_lt_d9
    linarith
  have hl4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  rw [hl4]
  have hKsmall : 2 ^ 24 * K = y := hy.symm
  nlinarith

/-- **The polynomial floor of the slope.** There is an absolute `c₀ > 0` such that every producer
on an alphabet in `[1, K]` has normalized slope at least `1 + c₀ / (K (1 + log K))`. Every prime
beyond the alphabet forces a jump. -/
theorem exists_floor_normSlope :
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ (K : ℕ) (c : ℕ →₀ ℤ) (m B : ℕ), 1 ≤ K → IsProducer c m B →
      AlphabetLE c K → 1 + c₀ / ((K : ℝ) * (1 + Real.log K)) ≤ normSlope c m B := by
  set C : ℝ := 2 ^ 24 with hC
  have hC1 : 1 ≤ C := by rw [hC]; norm_num
  have hC0 : 0 < C := by linarith
  have hlogC : 0 < Real.log C := Real.log_pos (by rw [hC]; norm_num)
  refine ⟨1 / (2 * C ^ 2 * (1 + Real.log C)), by positivity, ?_⟩
  intro K c m B hK1 hP hK
  have hKR : (1 : ℝ) ≤ K := by exact_mod_cast hK1
  have hK0 : (0 : ℝ) < K := by linarith
  set y : ℝ := C * K with hy
  have hy1 : 1 ≤ y := by rw [hy]; nlinarith
  have hy0 : 0 < y := by linarith
  have hlogy : 0 < Real.log y := Real.log_pos (by rw [hy]; nlinarith [show (2 : ℝ) ≤ C by rw [hC]; norm_num])
  have hcard : (K : ℝ) ≤ ((RHTower.windowPrimes K y).card : ℝ) * Real.log y :=
    window_card_lower hKR
  have hmem : ∀ p ∈ RHTower.windowPrimes K y, p.Prime ∧ (K : ℝ) < p ∧ (p : ℝ) ≤ y := fun p hp =>
    (RHTower.mem_windowPrimes hK0.le hy0.le).mp hp
  have hrough : ∀ r ∈ RHTower.windowPrimes K y, 2 ≤ r ∧ IsRough c r := by
    intro r hr
    obtain ⟨hpr, hlt, _⟩ := hmem r hr
    exact ⟨hpr.two_le, isRough_of_prime_of_alphabet hK hpr (by exact_mod_cast hlt)⟩
  have hsum : ((RHTower.windowPrimes K y).card : ℝ) * (1 / (2 * y ^ 2)) ≤
      ∑ r ∈ RHTower.windowPrimes K y, 1 / ((r : ℝ) * ((r : ℝ) + 1)) := by
    rw [← nsmul_eq_mul, ← sum_const]
    refine sum_le_sum fun r hr => ?_
    obtain ⟨hpr, _, hle⟩ := hmem r hr
    have hr0 : (0 : ℝ) < r := by exact_mod_cast hpr.pos
    refine one_div_le_one_div_of_le (by positivity) ?_
    nlinarith
  have hex := hP.sum_rough_le_excess _ hrough
  have hm := hP.m_pos
  have hdiv : ∑ r ∈ RHTower.windowPrimes K y, 1 / ((r : ℝ) * ((r : ℝ) + 1)) ≤ excess c m B / m := by
    rw [le_div_iff₀ hm]; linarith
  have hfloor := hP.one_add_excess_div_le_normSlope
  have hcardge : (K : ℝ) / Real.log y ≤ ((RHTower.windowPrimes K y).card : ℝ) := by
    rwa [div_le_iff₀ hlogy]
  have hlow : (K : ℝ) / Real.log y * (1 / (2 * y ^ 2)) ≤
      ∑ r ∈ RHTower.windowPrimes K y, 1 / ((r : ℝ) * ((r : ℝ) + 1)) :=
    (mul_le_mul_of_nonneg_right hcardge (by positivity)).trans hsum
  have hlogyle : Real.log y ≤ (1 + Real.log C) * (1 + Real.log K) := by
    rw [hy, Real.log_mul hC0.ne' hK0.ne']
    have : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hKR
    nlinarith
  have hLK : 0 < 1 + Real.log (K : ℝ) := by
    have : 0 ≤ Real.log (K : ℝ) := Real.log_nonneg hKR
    linarith
  have hgoal : 1 / (2 * C ^ 2 * (1 + Real.log C)) / ((K : ℝ) * (1 + Real.log K)) ≤
      (K : ℝ) / Real.log y * (1 / (2 * y ^ 2)) := by
    have hrw : (K : ℝ) / Real.log y * (1 / (2 * y ^ 2)) =
        1 / (2 * C ^ 2 * (K : ℝ) * Real.log y) := by
      rw [hy]; field_simp
    rw [hrw, div_div]
    refine one_div_le_one_div_of_le (by positivity) ?_
    have hmul : 2 * C ^ 2 * (K : ℝ) * Real.log y ≤
        2 * C ^ 2 * (K : ℝ) * ((1 + Real.log C) * (1 + Real.log K)) :=
      mul_le_mul_of_nonneg_left hlogyle (by positivity)
    calc 2 * C ^ 2 * (K : ℝ) * Real.log y
        ≤ 2 * C ^ 2 * (K : ℝ) * ((1 + Real.log C) * (1 + Real.log K)) := hmul
      _ = 2 * C ^ 2 * (1 + Real.log C) * ((K : ℝ) * (1 + Real.log K)) := by ring
  linarith

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
