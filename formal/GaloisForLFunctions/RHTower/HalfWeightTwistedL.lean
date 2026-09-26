import GaloisForLFunctions.RHTower.HalfWeightTwistedCoefficients
import GaloisForLFunctions.RHTower.HalfWeightEisensteinContinuation

/-!
# The twisted coefficients as `L`-function quotients

For a prime `q`, `ψ₀` mod `q` with `ψ₀ ≠ 1`, `ψ₀² ≠ 1`, and `n ≠ 0`:

* `prodChar`, `prodChar_natCast`: `ψχ` at level `ab`, `(ψχ)(c) = ψ(c)χ(c)`; `chiTw = ψ̄₀ χ_n`.
* `chiG_eq_mul`, `LSeries_sqfG`: for every Dirichlet character, `χ = (μ²χ) ⍟ (χ on squares)` and
  `Σ μ(c)²χ(c) c^{-s} = L(s,χ)/L(2s,χ²)`.
* `Btw_eq_mul`: `ψ̄₀ g_L = (μ² χ') ⍟ ψ̄₀ e_L` (`pmul` by a completely multiplicative function distributes
  over `⍟`).
* `lseriesSummable_Qf`, `norm_LSeries_Qf_le`: the `q`-part converges on `Re s > 0`,
  `‖L(Q,s)‖ ≤ 8q|n|/(1 - q^{-σ})`.
* `LSeries_Qf_Btw`: `L(Q * ψ̄₀ g_L, s) = L(Q,s) L(s,χ')/L(2s,χ'²) L(ψ̄₀ e_L, s)`; `chiTw_sq`:
  `χ'² = ψ̄₀²` lifted (`χ_n² = 1`), so `L(u,χ'²) = L(u,ψ̄₀²) ∏_{p ∣ q·4|n|M'}(1 - ψ̄₀²(p)p^{-u})`;
  `chiTw_ne_one`: `χ' ≠ 1` since `ψ₀² ≠ 1`.
* **`Dstw_eq`**, **`differentiableAt_Dstw`**: `D*_n = L(4w-1, ψ̄₀²) D_n` on `Re w > 3/4`, and `D*_n` is
  holomorphic on `Re w > 1/4`.
* **`Aq_zero`**, `Dser_tw_zero`: `A_α(0) = 0` (substitute `b ↦ t²b` with `ψ₀(t)² ≠ 1`), so `D_0 = 0`.
* **`exists_bound_Dstw`**: on a closed ball in `Re w > 1/4`, `‖D*_n(w)‖ ≤ C |n|^{5+γ+β}`.
-/

open Complex ArithmeticFunction
open scoped Real ArithmeticFunction.Moebius

namespace GaloisForLFunctions.RHTower.HalfWeight

noncomputable section

/-! ### The product of two Dirichlet characters -/

section Product

variable {a b : ℕ} [NeZero a] [NeZero b]

/-- `ψχ` at level `ab`. -/
def prodChar (ψ : DirichletCharacter ℂ a) (χ : DirichletCharacter ℂ b) : DirichletCharacter ℂ (a * b) :=
  ψ.changeLevel (dvd_mul_right a b) * χ.changeLevel (dvd_mul_left b a)

theorem changeLevel_natCast_of_unit {m N : ℕ} [NeZero N] (h : m ∣ N) (χ : DirichletCharacter ℂ m) {c : ℕ}
    (hc : IsUnit (c : ZMod N)) : χ.changeLevel h (c : ZMod N) = χ (c : ZMod m) := by
  obtain ⟨u, hu⟩ := hc
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd χ h u
  rw [hu, ZMod.cast_natCast h] at this
  exact this

theorem prodChar_natCast (ψ : DirichletCharacter ℂ a) (χ : DirichletCharacter ℂ b) (c : ℕ) :
    prodChar ψ χ (c : ZMod (a * b)) = ψ (c : ZMod a) * χ (c : ZMod b) := by
  unfold prodChar
  rw [MulChar.mul_apply]
  by_cases hu : IsUnit (c : ZMod (a * b))
  · rw [changeLevel_natCast_of_unit _ _ hu, changeLevel_natCast_of_unit _ _ hu]
  · rw [MulChar.map_nonunit _ hu, zero_mul]
    have hc : ¬ c.Coprime (a * b) := fun h => hu ((ZMod.isUnit_iff_coprime c (a * b)).2 h)
    rw [Nat.coprime_mul_iff_right, not_and_or] at hc
    rcases hc with h | h
    · rw [MulChar.map_nonunit ψ (fun h' => h ((ZMod.isUnit_iff_coprime c a).1 h')), zero_mul]
    · rw [MulChar.map_nonunit χ (fun h' => h ((ZMod.isUnit_iff_coprime c b).1 h')), mul_zero]

end Product

/-! ### Square-free and square parts of a Dirichlet character -/

section Generic

variable {N : ℕ} (χ : DirichletCharacter ℂ N)

/-- `χ` as an arithmetic function. -/
def chiG : ArithmeticFunction ℂ := ⟨fun c => if c = 0 then 0 else χ c, by simp⟩

theorem chiG_apply {c : ℕ} (hc : c ≠ 0) : chiG χ c = χ c := by simp [chiG, hc]

theorem isMultiplicative_chiG : (chiG χ).IsMultiplicative := by
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by rw [chiG_apply χ one_ne_zero]; simp, fun {x y} hx hy _ => ?_⟩
  rw [chiG_apply χ (mul_ne_zero hx hy), chiG_apply χ hx, chiG_apply χ hy, Nat.cast_mul, map_mul]

/-- `μ² χ`. -/
def sqfG : ArithmeticFunction ℂ := ((μ : ArithmeticFunction ℂ).pmul (μ : ArithmeticFunction ℂ)).pmul (chiG χ)

theorem isMultiplicative_sqfG : (sqfG χ).IsMultiplicative :=
  (isMultiplicative_moebius.intCast.pmul isMultiplicative_moebius.intCast).pmul (isMultiplicative_chiG χ)

theorem sqfG_apply (c : ℕ) : sqfG χ c = ((μ c : ℤ) : ℂ) ^ 2 * chiG χ c := by
  simp [sqfG, ArithmeticFunction.pmul_apply, sq]

open Classical in
/-- `χ` restricted to squares. -/
def sqPartG : ArithmeticFunction ℂ := ⟨fun c => if IsSquare c then chiG χ c else 0, by simp [chiG]⟩

open Classical in
theorem sqPartG_apply (c : ℕ) : sqPartG χ c = if IsSquare c then chiG χ c else 0 := rfl

theorem isMultiplicative_sqPartG : (sqPartG χ).IsMultiplicative := by
  classical
  rw [IsMultiplicative.iff_ne_zero]
  refine ⟨by rw [sqPartG_apply, if_pos ⟨1, rfl⟩, (isMultiplicative_chiG χ).map_one],
    fun {x y} hx hy hxy => ?_⟩
  rw [sqPartG_apply, sqPartG_apply, sqPartG_apply]
  by_cases hA : IsSquare x
  · by_cases hB : IsSquare y
    · have hAB : IsSquare (x * y) := (isSquare_mul_of_coprime hxy).2 ⟨hA, hB⟩
      simp only [hA, hB, hAB, if_true]
      exact (isMultiplicative_chiG χ).map_mul_of_coprime hxy
    · have hAB : ¬ IsSquare (x * y) := fun h => hB ((isSquare_mul_of_coprime hxy).1 h).2
      simp only [hAB, hB, if_false, mul_zero]
  · have hAB : ¬ IsSquare (x * y) := fun h => hA ((isSquare_mul_of_coprime hxy).1 h).1
    simp only [hAB, hA, if_false, zero_mul]

theorem chiG_prime_pow {p : ℕ} (hp : p.Prime) (j : ℕ) : chiG χ (p ^ j) = (chiG χ p) ^ j := by
  rw [chiG_apply χ (pow_ne_zero _ hp.ne_zero), chiG_apply χ hp.ne_zero, Nat.cast_pow, map_pow]

/-- **`χ = (μ² χ) ⍟ (χ on squares)`**. -/
theorem chiG_eq_mul : chiG χ = sqfG χ * sqPartG χ := by
  classical
  have hmul := (isMultiplicative_sqfG χ).mul (isMultiplicative_sqPartG χ)
  refine (IsMultiplicative.eq_iff_eq_on_prime_powers _ (isMultiplicative_chiG χ) _ hmul).2 ?_
  intro p i hp
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp only [pow_zero, (isMultiplicative_chiG χ).map_one, hmul.map_one]
  rw [mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => sqfG χ a * sqPartG χ b),
    Nat.sum_divisors_prime_pow hp]
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have hz : ∀ j ∈ Finset.range k, sqfG χ (p ^ (j + 1 + 1)) *
      sqPartG χ (p ^ (k + 1) / p ^ (j + 1 + 1)) = 0 := by
    intro j _
    rw [sqfG_apply, ArithmeticFunction.moebius_apply_prime_pow hp (by omega), if_neg (by omega)]
    simp
  rw [Finset.sum_eq_zero hz, zero_add]
  have hdiv : p ^ (k + 1) / p ^ (0 + 1) = p ^ k := by
    rw [zero_add, pow_one, pow_succ, Nat.mul_div_cancel _ hp.pos]
  rw [hdiv, pow_zero, Nat.div_one, (isMultiplicative_sqfG χ).map_one, one_mul, zero_add,
    pow_one, sqfG_apply, ArithmeticFunction.moebius_apply_prime hp, sqPartG_apply, sqPartG_apply,
    chiG_prime_pow χ hp, chiG_prime_pow χ hp]
  rcases Nat.even_or_odd k with he | ho
  · have h1 : IsSquare (p ^ k) := (isSquare_prime_pow_iff hp k).2 he
    have h2 : ¬ IsSquare (p ^ (k + 1)) := fun h =>
      Nat.not_even_iff_odd.2 he.add_one ((isSquare_prime_pow_iff hp _).1 h)
    simp only [h1, h2, if_true, if_false]
    push_cast; ring
  · have h1 : ¬ IsSquare (p ^ k) := fun h =>
      Nat.not_even_iff_odd.2 ho ((isSquare_prime_pow_iff hp _).1 h)
    have h2 : IsSquare (p ^ (k + 1)) := (isSquare_prime_pow_iff hp _).2 ho.add_one
    simp only [h1, h2, if_true, if_false]
    ring

theorem norm_chiG_le (c : ℕ) : ‖chiG χ c‖ ≤ 1 := by
  by_cases hc : c = 0
  · simp [chiG, hc]
  · rw [chiG_apply χ hc]; exact DirichletCharacter.norm_le_one _ _

theorem norm_sqfG_le (c : ℕ) : ‖sqfG χ c‖ ≤ 1 := by
  rw [sqfG_apply, norm_mul, norm_pow]
  have h1 : ‖((μ c : ℤ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_intCast]; exact_mod_cast ArithmeticFunction.abs_moebius_le_one
  have h2 := norm_chiG_le χ c
  have h3 : ‖((μ c : ℤ) : ℂ)‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) h1
  nlinarith [norm_nonneg (chiG χ c), sq_nonneg ‖((μ c : ℤ) : ℂ)‖]

theorem norm_sqPartG_le (c : ℕ) : ‖sqPartG χ c‖ ≤ 1 := by
  classical
  rw [sqPartG_apply]
  split_ifs
  · exact norm_chiG_le χ c
  · simp

theorem LSeries_chiG [NeZero N] {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun c => chiG χ c) s = DirichletCharacter.LFunction χ s := by
  rw [DirichletCharacter.LFunction_eq_LSeries _ hs]
  exact LSeries_congr (fun {c} hc => chiG_apply χ hc) s

theorem LSeries_sqPartG [NeZero N] {s : ℂ} (hs : 1 / 2 < s.re) :
    LSeries (fun c => sqPartG χ c) s = DirichletCharacter.LFunction (χ ^ 2) (2 * s) := by
  classical
  rw [DirichletCharacter.LFunction_eq_LSeries _ (by simp; linarith)]
  unfold LSeries
  have hinj : Function.Injective (fun k : ℕ => k ^ 2) := Nat.pow_left_injective two_ne_zero
  have hsupp : Function.support (LSeries.term (fun c => sqPartG χ c) s) ⊆
      Set.range (fun k : ℕ => k ^ 2) := by
    intro c hc
    rw [Function.mem_support, LSeries.term_def] at hc
    split_ifs at hc with hc0
    · exact absurd rfl hc
    · rw [sqPartG_apply] at hc
      split_ifs at hc with hsq
      · obtain ⟨k, rfl⟩ := hsq; exact ⟨k, by ring⟩
      · simp at hc
  rw [← hinj.tsum_eq hsupp]
  refine tsum_congr fun k => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [LSeries.term_def]
  have hk0 : k ≠ 0 := hk.ne'
  rw [LSeries.term_of_ne_zero (pow_ne_zero 2 hk0), LSeries.term_of_ne_zero hk0, sqPartG_apply,
    if_pos ⟨k, by ring⟩, chiG_apply χ (pow_ne_zero 2 hk0), MulChar.pow_apply' _ two_ne_zero,
    Nat.cast_pow, map_pow]
  congr 1
  rw [show (2 * s) = ((2 : ℕ) : ℂ) * s by norm_num, Complex.natCast_cpow_natCast_mul]
  push_cast; ring_nf

/-- **`Σ μ(c)² χ(c) c^{-s} = L(s, χ) / L(2s, χ²)`** for `Re s > 1`. -/
theorem LSeries_sqfG [NeZero N] {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun c => sqfG χ c) s = DirichletCharacter.LFunction χ s /
      DirichletCharacter.LFunction (χ ^ 2) (2 * s) := by
  have h1 := lseriesSummable_of_norm_le_one (norm_sqfG_le χ) hs
  have h2 := lseriesSummable_of_norm_le_one (norm_sqPartG_le χ) hs
  have hmul := LSeries_mul' h1 h2
  rw [← chiG_eq_mul, LSeries_chiG χ hs, LSeries_sqPartG χ (by linarith)] at hmul
  have hne : DirichletCharacter.LFunction (χ ^ 2) (2 * s) ≠ 0 := by
    apply DirichletCharacter.LFunction_ne_zero_of_one_le_re
    · right; intro h; have := congrArg Complex.re h; simp at this; linarith
    · simp; linarith
  rw [hmul, mul_div_assoc, div_self hne, mul_one]

end Generic

/-! ### The twisted `q`-free part -/

theorem pmul_mul_of_complete {f : ArithmeticFunction ℂ} (hf : ∀ a b, f (a * b) = f a * f b)
    (g h : ArithmeticFunction ℂ) : f.pmul (g * h) = (f.pmul g) * (f.pmul h) := by
  ext c
  rw [pmul_apply, mul_apply, mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Nat.mem_divisorsAntidiagonal] at hx
  rw [pmul_apply, pmul_apply, ← hx.1, hf]
  ring

section Twist

variable {q : ℕ} [hq : Fact q.Prime] (ψ₀ : DirichletCharacter ℂ q)

theorem conjA_mul (a b : ℕ) : conjA ψ₀ (a * b) = conjA ψ₀ a * conjA ψ₀ b := by
  by_cases ha : a = 0
  · simp [conjA, ha]
  by_cases hb : b = 0
  · simp [conjA, hb]
  rw [conjA_apply ψ₀ (mul_ne_zero ha hb), conjA_apply ψ₀ ha, conjA_apply ψ₀ hb, Nat.cast_mul,
    map_mul, map_mul]

theorem norm_conjA_le (c : ℕ) : ‖conjA ψ₀ c‖ ≤ 1 := by
  by_cases hc : c = 0
  · simp [conjA, hc]
  · rw [conjA_apply ψ₀ hc, Complex.norm_conj]; exact DirichletCharacter.norm_le_one _ _

variable {n : ℤ} {M' : ℕ} (hn : n ≠ 0) (hM : 0 < M')

/-- `χ' = ψ̄₀ χ_n` at level `q · 4|n|M'`. -/
def chiTw : DirichletCharacter ℂ (q * kmod n M') := prodChar ψ₀⁻¹ (kronChar hn hM)

/-- `ψ̄₀ e_L`. -/
def eLtw : ArithmeticFunction ℂ := (conjA ψ₀).pmul (eL (n := n) (M := M'))

theorem conjA_pmul_sqfChi : (conjA ψ₀).pmul (sqfChi hn hM) = sqfG (chiTw ψ₀ hn hM) := by
  haveI : NeZero (kmod n M') := ⟨(kmod_pos hn hM).ne'⟩
  ext c
  rw [pmul_apply, sqfChi_apply, sqfG_apply]
  by_cases hc : c = 0
  · simp [hc, conjA]
  rw [conjA_apply ψ₀ hc, chiA_apply hn hM hc, chiG_apply _ hc, chiTw, prodChar_natCast,
    show ψ₀⁻¹ (c : ZMod q) = star (ψ₀ (c : ZMod q)) from (MulChar.star_apply' ψ₀ _).symm,
    show star (ψ₀ (c : ZMod q)) = starRingEnd ℂ (ψ₀ (c : ZMod q)) from rfl]
  ring

/-- **`ψ̄₀ g_L = (μ² χ') ⍟ ψ̄₀ e_L`**. -/
theorem Btw_eq_mul : Btw ψ₀ n M' = sqfG (chiTw ψ₀ hn hM) * eLtw ψ₀ (n := n) (M' := M') := by
  rw [Btw, gL_eq_mul hn hM, pmul_mul_of_complete (conjA_mul ψ₀), conjA_pmul_sqfChi]
  rfl

include hn in
theorem lseriesSummable_eLtw {s : ℂ} (hs : 0 < s.re) :
    LSeriesSummable (fun c => eLtw ψ₀ (n := n) (M' := M') c) s := by
  refine (lseriesSummable_eL (n := n) (M := M') hn hs).norm.of_norm_bounded fun c => ?_
  rw [LSeries.term_def, LSeries.term_def]
  split_ifs
  · simp
  · rw [eLtw, pmul_apply, norm_div, norm_div, norm_mul]
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_left (norm_nonneg _) (norm_conjA_le ψ₀ c))
      (norm_nonneg _)

/-! ### The `q`-part converges on `Re s > 0` -/

theorem norm_Qf_pow_le {n : ℤ} (hn : n ≠ 0) (α : ℕ) :
    ‖Qf ψ₀ n (q ^ α)‖ ≤ 8 * q * n.natAbs := by
  rw [Qf_pow]
  split_ifs with h2
  · have hA := norm_Aq_le ψ₀ n (α := α) (by omega)
    haveI : NeZero (q ^ (α - 1)) := ⟨pow_ne_zero _ hq.out.ne_zero⟩
    rw [sqCount_eq_rootCard, Complex.norm_natCast] at hA
    have hr : (rootCard n (q ^ (α - 1)) : ℝ) ≤ 8 * n.natAbs := by exact_mod_cast rootCard_le hn _
    calc _ ≤ (q : ℝ) * (rootCard n (q ^ (α - 1)) : ℝ) := hA
      _ ≤ (q : ℝ) * (8 * n.natAbs) := mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := by ring
  · simp only [norm_zero]; positivity

theorem Qf_eq_zero_of_not_mem {n : ℤ} {c : ℕ} (hc : c ∉ Set.range (fun α : ℕ => q ^ α)) :
    Qf ψ₀ n c = 0 := by
  simp only [Qf, ArithmeticFunction.coe_mk]
  rw [if_neg]
  rintro ⟨-, h⟩
  exact hc ⟨_, h.symm⟩

theorem qpow_rpow_lt_one {σ : ℝ} (hσ : 0 < σ) : (q : ℝ) ^ (-σ) < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hq.out.one_lt) (by linarith)

theorem norm_term_Qf_le {n : ℤ} (hn : n ≠ 0) (s : ℂ) (α : ℕ) :
    ‖LSeries.term (fun c => Qf ψ₀ n c) s (q ^ α)‖ ≤ 8 * q * n.natAbs * ((q : ℝ) ^ (-s.re)) ^ α := by
  have hq0 : q ^ α ≠ 0 := pow_ne_zero _ hq.out.ne_zero
  rw [LSeries.term_of_ne_zero hq0, norm_div, Complex.norm_natCast_cpow_of_pos (by positivity)]
  have hpow : ((q ^ α : ℕ) : ℝ) ^ s.re = ((q : ℝ) ^ s.re) ^ α := by
    push_cast; rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), mul_comm,
      Real.rpow_mul (by positivity), Real.rpow_natCast]
  rw [hpow, div_eq_mul_inv, ← inv_pow, ← Real.rpow_neg (by positivity)]
  exact mul_le_mul_of_nonneg_right (norm_Qf_pow_le ψ₀ hn α) (by positivity)

theorem lseriesSummable_Qf {n : ℤ} (hn : n ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    LSeriesSummable (fun c => Qf ψ₀ n c) s := by
  have hinj : Function.Injective (fun α : ℕ => q ^ α) := Nat.pow_right_injective hq.out.two_le
  unfold LSeriesSummable
  rw [← hinj.summable_iff (fun c hc => by
    rw [LSeries.term_def]; split_ifs
    · rfl
    · rw [Qf_eq_zero_of_not_mem ψ₀ hc, zero_div])]
  refine Summable.of_norm_bounded ((summable_geometric_of_lt_one (by positivity)
    (qpow_rpow_lt_one (q := q) hs)).mul_left (8 * (q : ℝ) * (n.natAbs : ℝ))) fun α => ?_
  exact norm_term_Qf_le ψ₀ hn s α

theorem norm_LSeries_Qf_le {n : ℤ} (hn : n ≠ 0) {s : ℂ} (hs : 0 < s.re) :
    ‖LSeries (fun c => Qf ψ₀ n c) s‖ ≤ 8 * q * n.natAbs / (1 - (q : ℝ) ^ (-s.re)) := by
  have hinj : Function.Injective (fun α : ℕ => q ^ α) := Nat.pow_right_injective hq.out.two_le
  have hzero : ∀ c ∉ Set.range (fun α : ℕ => q ^ α), LSeries.term (fun c => Qf ψ₀ n c) s c = 0 := by
    intro c hc
    rw [LSeries.term_def]; split_ifs
    · rfl
    · rw [Qf_eq_zero_of_not_mem ψ₀ hc, zero_div]
  have hr := qpow_rpow_lt_one (q := q) hs
  have hg := (summable_geometric_of_lt_one (by positivity) hr).mul_left (8 * (q : ℝ) * (n.natAbs : ℝ))
  have hsum : Summable fun α : ℕ => ‖LSeries.term (fun c => Qf ψ₀ n c) s (q ^ α)‖ :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun α => norm_term_Qf_le ψ₀ hn s α) hg
  unfold LSeries
  rw [← hinj.tsum_eq (Function.support_subset_iff'.2 hzero)]
  calc ‖∑' α : ℕ, LSeries.term (fun c => Qf ψ₀ n c) s (q ^ α)‖
      ≤ ∑' α : ℕ, ‖LSeries.term (fun c => Qf ψ₀ n c) s (q ^ α)‖ := norm_tsum_le_tsum_norm hsum
    _ ≤ ∑' α : ℕ, 8 * q * n.natAbs * ((q : ℝ) ^ (-s.re)) ^ α :=
        hsum.tsum_le_tsum (fun α => norm_term_Qf_le ψ₀ hn s α) hg
    _ = _ := by rw [tsum_mul_left, tsum_geometric_of_lt_one (by positivity) hr, div_eq_mul_inv]

/-! ### The Euler product form and the regularised coefficients -/

/-- **`L(Q * ψ̄₀ g_L, s) = L(Q, s) · L(s, χ')/L(2s, χ'²) · L(ψ̄₀ e_L, s)`** for `Re s > 1`. -/
theorem LSeries_Qf_Btw {s : ℂ} (hs : 1 < s.re) :
    haveI : NeZero (kmod n M') := ⟨(kmod_pos hn hM).ne'⟩
    LSeries (fun c => (Qf ψ₀ n * Btw ψ₀ n M') c) s =
      LSeries (fun c => Qf ψ₀ n c) s * (DirichletCharacter.LFunction (chiTw ψ₀ hn hM) s /
        DirichletCharacter.LFunction (chiTw ψ₀ hn hM ^ 2) (2 * s)) *
        LSeries (fun c => eLtw ψ₀ (n := n) (M' := M') c) s := by
  haveI : NeZero (kmod n M') := ⟨(kmod_pos hn hM).ne'⟩
  have h0 : 0 < s.re := by linarith
  have hQ := lseriesSummable_Qf ψ₀ hn h0
  have hS := lseriesSummable_of_norm_le_one (norm_sqfG_le (chiTw ψ₀ hn hM)) hs
  have hE := lseriesSummable_eLtw ψ₀ hn (M' := M') h0
  rw [Btw_eq_mul ψ₀ hn hM, LSeries_mul' hQ (LSeriesSummable_mul hS hE), LSeries_mul' hS hE,
    LSeries_sqfG _ hs]
  ring

omit hq in
theorem chiTw_sq :
    haveI : NeZero (kmod n M') := ⟨(kmod_pos hn hM).ne'⟩
    chiTw ψ₀ hn hM ^ 2 = (DirichletCharacter.changeLevel (dvd_mul_right q (kmod n M'))) (ψ₀⁻¹ ^ 2) := by
  haveI : NeZero (kmod n M') := ⟨(kmod_pos hn hM).ne'⟩
  rw [chiTw, prodChar, mul_pow, ← map_pow, ← map_pow, kronChar_sq hn hM,
    DirichletCharacter.changeLevel_one, mul_one]

omit hq in
theorem inv_sq_ne_one (h2 : ψ₀ ^ 2 ≠ 1) : ψ₀⁻¹ ^ 2 ≠ 1 := by
  intro h; apply h2
  rw [inv_pow, inv_eq_one] at h; exact h

/-- `∏_{p ∣ N} (1 - ψ̄₀²(p) p^{-u})`. -/
def eulerTw (N : ℕ) (u : ℂ) : ℂ := ∏ p ∈ N.primeFactors, (1 - (ψ₀⁻¹ ^ 2) (p : ZMod q) * (p : ℂ) ^ (-u))

theorem eulerTw_ne_zero (N : ℕ) {u : ℂ} (hu : 0 < u.re) : eulerTw ψ₀ N u ≠ 0 := by
  unfold eulerTw
  rw [Finset.prod_ne_zero_iff]
  intro p hp
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hlt : ‖(ψ₀⁻¹ ^ 2) (p : ZMod q) * (p : ℂ) ^ (-u)‖ < 1 := by
    rw [norm_mul, Complex.norm_natCast_cpow_of_pos hpp.pos]
    have h1 := DirichletCharacter.norm_le_one (ψ₀⁻¹ ^ 2) (p : ZMod q)
    have h2 : (p : ℝ) ^ (-u).re < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast hpp.one_lt) (by simp; linarith)
    calc _ ≤ 1 * (p : ℝ) ^ (-u).re := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ < 1 := by linarith
  intro h0
  have : (ψ₀⁻¹ ^ 2) (p : ZMod q) * (p : ℂ) ^ (-u) = 1 := by linear_combination -h0
  rw [this, norm_one] at hlt
  exact lt_irrefl _ hlt

theorem differentiable_eulerTw (N : ℕ) : Differentiable ℂ (eulerTw ψ₀ N) := by
  unfold eulerTw
  refine Differentiable.fun_finsetProd fun p hp => ?_
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero
  exact (differentiable_const _).sub ((differentiable_const _).mul
    ((differentiable_id.neg).const_cpow (Or.inl hp0)))

/-- `L(u, χ'²) = L(u, ψ̄₀²) ∏_{p ∣ q 4|n|M'} (1 - ψ̄₀²(p) p^{-u})`. -/
theorem LFunction_chiTw_sq (h2 : ψ₀ ^ 2 ≠ 1) (u : ℂ) :
    haveI : NeZero (kmod n M') := ⟨(kmod_pos hn hM).ne'⟩
    DirichletCharacter.LFunction (chiTw ψ₀ hn hM ^ 2) u =
      DirichletCharacter.LFunction (ψ₀⁻¹ ^ 2) u * eulerTw ψ₀ (q * kmod n M') u := by
  haveI : NeZero (kmod n M') := ⟨(kmod_pos hn hM).ne'⟩
  haveI : NeZero (q * kmod n M') := ⟨mul_ne_zero hq.out.ne_zero (kmod_pos hn hM).ne'⟩
  rw [chiTw_sq ψ₀ hn hM, DirichletCharacter.LFunction_changeLevel _ _ (Or.inl (inv_sq_ne_one ψ₀ h2))]
  rfl

theorem chiTw_ne_one (h2 : ψ₀ ^ 2 ≠ 1) : chiTw ψ₀ hn hM ≠ 1 := by
  haveI : NeZero (kmod n M') := ⟨(kmod_pos hn hM).ne'⟩
  haveI : NeZero (q * kmod n M') := ⟨mul_ne_zero hq.out.ne_zero (kmod_pos hn hM).ne'⟩
  intro h
  have hs := chiTw_sq ψ₀ hn hM
  rw [h, one_pow] at hs
  apply inv_sq_ne_one ψ₀ h2
  apply DirichletCharacter.changeLevel_injective (dvd_mul_right q (kmod n M'))
  rw [← hs, DirichletCharacter.changeLevel_one]

/-- The regularised twisted coefficient
`D*_n(w) = i^{1/2}/(√2 τ) L(Q, s) L(s, χ') L(ψ̄₀ e_L, s) ∏_{p}(1 - ψ̄₀²(p)p^{1-4w})⁻¹`, `s = 2w - 1/2`. -/
def Dstw (w : ℂ) : ℂ :=
  haveI : NeZero (kmod n M') := ⟨(kmod_pos hn hM).ne'⟩
  I ^ (1 / 2 : ℂ) / Real.sqrt 2 * (tauG ψ₀)⁻¹ * LSeries (fun c => Qf ψ₀ n c) (2 * w - 1 / 2) *
    DirichletCharacter.LFunction (chiTw ψ₀ hn hM) (2 * w - 1 / 2) *
    LSeries (fun c => eLtw ψ₀ (n := n) (M' := M') c) (2 * w - 1 / 2) *
    (eulerTw ψ₀ (q * kmod n M') (4 * w - 1))⁻¹

/-- **`D*_n = L(4w-1, ψ̄₀²) D_n`** on `Re w > 3/4`. -/
theorem Dstw_eq (h1 : ψ₀ ≠ 1) (h2 : ψ₀ ^ 2 ≠ 1) [NeZero M'] (hcop : q.Coprime (4 * M'))
    (hqM : q ∣ 4 * (M' * q ^ 2)) {w : ℂ} (hw : 3 / 4 < w.re) :
    Dstw ψ₀ hn hM w = DirichletCharacter.LFunction (ψ₀⁻¹ ^ 2) (4 * w - 1) *
      Dser (M' * q ^ 2) (ψ₀.changeLevel hqM) n w := by
  haveI : NeZero (kmod n M') := ⟨(kmod_pos hn hM).ne'⟩
  have hs : 1 < (2 * w - 1 / 2).re := by simp; linarith
  rw [Dser_tw_eq_LSeries ψ₀ h1 n hcop hqM, LSeries_Qf_Btw ψ₀ hn hM hs,
    show 2 * (2 * w - 1 / 2) = 4 * w - 1 by ring, LFunction_chiTw_sq ψ₀ hn hM h2]
  have hL : DirichletCharacter.LFunction (ψ₀⁻¹ ^ 2) (4 * w - 1) ≠ 0 :=
    DirichletCharacter.LFunction_ne_zero_of_one_le_re _ (Or.inl (inv_sq_ne_one ψ₀ h2)) (by simp; linarith)
  have hE := eulerTw_ne_zero ψ₀ (q * kmod n M') (u := 4 * w - 1) (by simp; linarith)
  unfold Dstw
  set L := DirichletCharacter.LFunction (ψ₀⁻¹ ^ 2) (4 * w - 1)
  set E := eulerTw ψ₀ (q * kmod n M') (4 * w - 1)
  set A := LSeries (fun c => Qf ψ₀ n c) (2 * w - 1 / 2)
  set B := DirichletCharacter.LFunction (chiTw ψ₀ hn hM) (2 * w - 1 / 2)
  set C := LSeries (fun c => eLtw ψ₀ (n := n) (M' := M') c) (2 * w - 1 / 2)
  field_simp

theorem differentiableAt_Dstw (h2 : ψ₀ ^ 2 ≠ 1) {w₀ : ℂ} (hw : 1 / 4 < w₀.re) :
    DifferentiableAt ℂ (Dstw ψ₀ hn hM) w₀ := by
  haveI : NeZero (kmod n M') := ⟨(kmod_pos hn hM).ne'⟩
  haveI : NeZero (q * kmod n M') := ⟨mul_ne_zero hq.out.ne_zero (kmod_pos hn hM).ne'⟩
  have hs : 0 < (2 * w₀ - 1 / 2).re := by simp; linarith
  have hu : 0 < (4 * w₀ - 1).re := by simp; linarith
  have hlin : ∀ a b : ℂ, DifferentiableAt ℂ (fun w : ℂ => a * w - b) w₀ := fun a b =>
    (differentiableAt_id.const_mul a).sub_const b
  have hQ0 : DifferentiableAt ℂ (LSeries (fun c => Qf ψ₀ n c)) (2 * w₀ - 1 / 2) :=
    differentiableAt_LSeries_of_summable (fun s hs => lseriesSummable_Qf ψ₀ hn hs) hs
  have hQ := hQ0.comp w₀ (hlin 2 (1 / 2))
  have hL0 : DifferentiableAt ℂ (DirichletCharacter.LFunction (chiTw ψ₀ hn hM)) (2 * w₀ - 1 / 2) :=
    DirichletCharacter.differentiable_LFunction (chiTw_ne_one ψ₀ hn hM h2) _
  have hL := hL0.comp w₀ (hlin 2 (1 / 2))
  have hE0 : DifferentiableAt ℂ (LSeries (fun c => eLtw ψ₀ (n := n) (M' := M') c)) (2 * w₀ - 1 / 2) :=
    differentiableAt_LSeries_of_summable (fun s hs => lseriesSummable_eLtw ψ₀ hn hs) hs
  have hE := hE0.comp w₀ (hlin 2 (1 / 2))
  have hEu : DifferentiableAt ℂ (fun w => (eulerTw ψ₀ (q * kmod n M') (4 * w - 1))⁻¹) w₀ :=
    ((differentiable_eulerTw ψ₀ _ _).comp w₀ (hlin 4 1)).inv (eulerTw_ne_zero ψ₀ _ hu)
  unfold Dstw
  exact ((((differentiableAt_const _).mul hQ).mul hL).mul hE).mul hEu

/-! ### The constant coefficient vanishes -/

omit hq in
theorem rootCard_mul_unit_sq {f : ℕ} [NeZero f] (m k : ℤ) (hu : IsUnit ((m : ℤ) : ZMod f)) :
    rootCard (m ^ 2 * k) f = rootCard k f := by
  obtain ⟨u, hu⟩ := hu
  unfold rootCard
  symm
  refine Finset.card_equiv (Units.mulLeft u) fun x => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Units.mulLeft_apply]
  push_cast
  rw [← hu, mul_pow]
  constructor
  · intro h; rw [h]
  · intro h
    have h' := congrArg (fun y => ((u⁻¹ : (ZMod f)ˣ) : ZMod f) ^ 2 * y) h
    simp only [← mul_assoc, ← mul_pow, Units.inv_mul, one_pow, one_mul] at h'
    exact h'

omit hq in
theorem sqCount_mul_unit_sq {f : ℕ} [NeZero f] (m k : ℤ) (hu : IsUnit ((m : ℤ) : ZMod f)) :
    sqCount (m ^ 2 * k) f = sqCount k f := by
  rw [sqCount_eq_rootCard, sqCount_eq_rootCard, rootCard_mul_unit_sq m k hu]

/-- **`A_α(0) = 0`** when `ψ₀² ≠ 1`: the substitution `b ↦ t²b` multiplies `A_α(0)` by `ψ₀(t)²`. -/
theorem Aq_zero (h2 : ψ₀ ^ 2 ≠ 1) {α : ℕ} (hα : 1 ≤ α) : Aq ψ₀ 0 α = 0 := by
  obtain ⟨t, ht⟩ := MulChar.ne_one_iff.1 h2
  rw [MulChar.pow_apply' _ two_ne_zero] at ht
  have hunit : IsUnit ((((t : ZMod q).val : ℕ) : ℤ) : ZMod (q ^ α)) := by
    have hc : ((t : ZMod q).val).Coprime (q ^ α) :=
      Nat.Coprime.pow_right _ (ZMod.val_coe_unit_coprime t)
    have := (ZMod.isUnit_iff_coprime _ _).2 hc
    simpa using this
  have key : ψ₀ (t : ZMod q) ^ 2 * Aq ψ₀ 0 α = Aq ψ₀ 0 α := by
    unfold Aq
    rw [Finset.mul_sum]
    refine Fintype.sum_equiv (Units.mulLeft (t ^ 2)) _ _ fun b => ?_
    simp only [Units.mulLeft_apply, Units.val_pow_eq_pow_val, zero_add]
    rw [map_mul, map_pow]
    have hcg : sqCount ((((t : ZMod q) ^ 2 * b).val : ℕ) * ((q ^ (α - 1) : ℕ) : ℤ)) (q ^ α) =
        sqCount (((t : ZMod q).val : ℤ) ^ 2 * (((b.val : ℕ) : ℤ) * ((q ^ (α - 1) : ℕ) : ℤ))) (q ^ α) := by
      have := sqCount_congr (q := q) 0 (A := (((t : ZMod q) ^ 2 * b).val : ℤ))
        (B := ((t : ZMod q).val : ℤ) ^ 2 * ((b.val : ℕ) : ℤ)) hα (by
          rw [← ZMod.intCast_eq_intCast_iff_dvd_sub]; push_cast; simp)
      simp only [zero_add] at this
      rw [this]; ring_nf
    haveI : NeZero (q ^ α) := ⟨pow_ne_zero _ hq.out.ne_zero⟩
    rw [hcg, sqCount_mul_unit_sq _ _ hunit]
    ring
  have hne : (1 : ℂ) - ψ₀ (t : ZMod q) ^ 2 ≠ 0 := sub_ne_zero.2 (Ne.symm ht)
  have : (1 - ψ₀ (t : ZMod q) ^ 2) * Aq ψ₀ 0 α = 0 := by linear_combination (-1 : ℂ) * key
  exact (mul_eq_zero.1 this).resolve_left hne

theorem Qf_zero (h2 : ψ₀ ^ 2 ≠ 1) : Qf ψ₀ 0 = 0 := by
  ext c
  simp only [Qf, ArithmeticFunction.coe_mk, ArithmeticFunction.zero_apply]
  split_ifs with h
  · exact Aq_zero ψ₀ h2 (by omega)
  · rfl

/-- **The twisted Eisenstein series has no `y^{1-w}` term**: `D_0 = 0` when `ψ₀² ≠ 1`. -/
theorem Dser_tw_zero (h1 : ψ₀ ≠ 1) (h2 : ψ₀ ^ 2 ≠ 1) {M' : ℕ} [NeZero M'] (hcop : q.Coprime (4 * M'))
    (hqM : q ∣ 4 * (M' * q ^ 2)) (w : ℂ) :
    Dser (M' * q ^ 2) (ψ₀.changeLevel hqM) 0 w = 0 := by
  rw [Dser_tw_eq_LSeries ψ₀ h1 0 hcop hqM, Qf_zero ψ₀ h2, zero_mul]
  have : (fun c => (0 : ArithmeticFunction ℂ) c) = 0 := by ext c; simp
  rw [this, LSeries_zero]; simp

/-! ### Polynomial bounds for the regularised coefficients -/

include hn hM in
theorem norm_LSeries_eLtw_le {s : ℂ} (hs : 0 < s.re) :
    ‖LSeries (fun c => eLtw ψ₀ (n := n) (M' := M') c) s‖ ≤
      4 * n.natAbs * (kmod n M' : ℝ) ^ betaE s.re := by
  have hm := summable_eMaj (n := n) (M := M') hn hs
  have hb : ∀ c, ‖LSeries.term (fun c => eLtw ψ₀ (n := n) (M' := M') c) s c‖ ≤
      eMaj (n := n) (M := M') s.re c := by
    intro c
    rcases Nat.eq_zero_or_pos c with rfl | hc
    · simp [LSeries.term_def, eMaj]
    rw [LSeries.term_of_ne_zero hc.ne', norm_div, Complex.norm_natCast_cpow_of_pos hc, eMaj,
      Real.rpow_neg (Nat.cast_nonneg _), div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    rw [eLtw, pmul_apply, norm_mul, eL_apply]
    refine (mul_le_of_le_one_left (norm_nonneg _) (norm_conjA_le ψ₀ c)).trans ?_
    split_ifs
    · exact le_rfl
    · simp
  have hsn : Summable fun c => ‖LSeries.term (fun c => eLtw ψ₀ (n := n) (M' := M') c) s c‖ :=
    Summable.of_nonneg_of_le (fun c => norm_nonneg _) hb hm
  calc ‖LSeries (fun c => eLtw ψ₀ (n := n) (M' := M') c) s‖
      ≤ ∑' c, ‖LSeries.term (fun c => eLtw ψ₀ (n := n) (M' := M') c) s c‖ := norm_tsum_le_tsum_norm hsn
    _ ≤ ∑' c, eMaj (n := n) (M := M') s.re c := hsn.tsum_le_tsum hb hm
    _ ≤ _ := tsum_eMaj_le hn hM hs

theorem norm_eulerTw_inv_le {N : ℕ} (hN : N ≠ 0) {u : ℂ} (hu : 0 < u.re) :
    ‖(eulerTw ψ₀ N u)⁻¹‖ ≤ (N : ℝ) ^ gammaE u.re := by
  set σ := u.re
  have h0 := one_sub_two_rpow_pos hu
  have hloc : ∀ p ∈ N.primeFactors, 1 - (2 : ℝ) ^ (-σ) ≤
      ‖1 - (ψ₀⁻¹ ^ 2) (p : ZMod q) * (p : ℂ) ^ (-u)‖ := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have h1 : ‖(ψ₀⁻¹ ^ 2) (p : ZMod q) * (p : ℂ) ^ (-u)‖ ≤ (2 : ℝ) ^ (-σ) := by
      rw [norm_mul, Complex.norm_natCast_cpow_of_pos hpp.pos]
      have hc := DirichletCharacter.norm_le_one (ψ₀⁻¹ ^ 2) (p : ZMod q)
      have hr : (p : ℝ) ^ (-u).re ≤ (2 : ℝ) ^ (-σ) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hpp.two_le)
          (by simp only [Complex.neg_re]; linarith)
      calc _ ≤ 1 * (p : ℝ) ^ (-u).re := mul_le_mul_of_nonneg_right hc (by positivity)
        _ ≤ _ := by linarith
    have := norm_sub_norm_le (1 : ℂ) ((ψ₀⁻¹ ^ 2) (p : ZMod q) * (p : ℂ) ^ (-u))
    rw [norm_one] at this
    linarith
  have hprod : (1 - (2 : ℝ) ^ (-σ)) ^ N.primeFactors.card ≤ ‖eulerTw ψ₀ N u‖ := by
    rw [eulerTw, norm_prod]
    calc (1 - (2 : ℝ) ^ (-σ)) ^ N.primeFactors.card = ∏ p ∈ N.primeFactors, (1 - (2 : ℝ) ^ (-σ)) :=
          (Finset.prod_const _).symm
      _ ≤ _ := Finset.prod_le_prod (fun _ _ => h0.le) hloc
  have hpos : 0 < (1 - (2 : ℝ) ^ (-σ)) ^ N.primeFactors.card := pow_pos h0 _
  have hB : 1 ≤ 1 / (1 - (2 : ℝ) ^ (-σ)) := by
    rw [le_div_iff₀ h0]; have := Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) (-σ); linarith
  rw [norm_inv]
  calc ‖eulerTw ψ₀ N u‖⁻¹ ≤ ((1 - (2 : ℝ) ^ (-σ)) ^ N.primeFactors.card)⁻¹ :=
        inv_anti₀ hpos hprod
    _ = (1 / (1 - (2 : ℝ) ^ (-σ))) ^ N.primeFactors.card := by rw [one_div, inv_pow]
    _ ≤ _ := pow_card_primeFactors_le hN hB

theorem norm_LFunction_chiTw_le (h2 : ψ₀ ^ 2 ≠ 1) {s : ℂ} (h0 : 0 ≤ s.re) :
    haveI : NeZero (kmod n M') := ⟨(kmod_pos hn hM).ne'⟩
    ‖DirichletCharacter.LFunction (chiTw ψ₀ hn hM) s‖ ≤
      (stripC * (q : ℝ) ^ 3 * ‖s - 4‖ ^ 3 + 2) * (kmod n M' : ℝ) ^ 3 := by
  haveI : NeZero (kmod n M') := ⟨(kmod_pos hn hM).ne'⟩
  haveI : NeZero (q * kmod n M') := ⟨mul_ne_zero hq.out.ne_zero (kmod_pos hn hM).ne'⟩
  have hk := kmod_one_le hn hM
  have hk3 : (1 : ℝ) ≤ (kmod n M' : ℝ) ^ 3 := one_le_pow₀ hk
  have hC := stripC_pos
  have hA : 0 ≤ stripC * (q : ℝ) ^ 3 * ‖s - 4‖ ^ 3 := by positivity
  rcases le_or_gt s.re 2 with h | h
  · have hL := norm_LFunction_le_of_ne_one (chiTw_ne_one ψ₀ hn hM h2) h0 h
    have hkm : ((q * kmod n M' : ℕ) : ℝ) = (q : ℝ) * (kmod n M' : ℝ) := Nat.cast_mul _ _
    calc _ ≤ stripC * ((q * kmod n M' : ℕ) : ℝ) ^ 3 * ‖s - 4‖ ^ 3 := hL
      _ = stripC * (q : ℝ) ^ 3 * ‖s - 4‖ ^ 3 * (kmod n M' : ℝ) ^ 3 := by rw [hkm]; ring
      _ ≤ _ := by nlinarith
  · have hL := norm_LFunction_le_two (chiTw ψ₀ hn hM) h.le
    nlinarith

omit hq in
/-- The exponent `5 + γ(4τ-1) + β(2τ-1/2)`. -/
def expTw (τ : ℝ) : ℝ := 5 + gammaE (4 * τ - 1) + betaE (2 * τ - 1 / 2)

omit hq in
theorem expTw_nonneg {τ : ℝ} (h1 : 1 / 4 < τ) : 0 ≤ expTw τ := by
  unfold expTw
  have := gammaE_nonneg (σ := 4 * τ - 1) (by linarith)
  have := betaE_nonneg (σ := 2 * τ - 1 / 2) (by linarith)
  linarith

/-- **Uniform polynomial bound for the regularised twisted coefficients** on a closed ball in
`Re w > 1/4`: `‖D*_n(w)‖ ≤ C |n|^{e}`. -/
theorem exists_bound_Dstw (h2 : ψ₀ ^ 2 ≠ 1) {M' : ℕ} (hM : 0 < M') {w₀ : ℂ} {r : ℝ}
    (h1 : 1 / 4 < w₀.re - r) :
    ∃ C, 0 ≤ C ∧ ∀ w ∈ Metric.closedBall w₀ r, ∀ n : ℤ, ∀ hn : n ≠ 0,
      ‖Dstw ψ₀ hn hM w‖ ≤ C * |(n : ℝ)| ^ expTw (w₀.re - r) := by
  set τ₁ := w₀.re - r
  set σ₁ := 2 * τ₁ - 1 / 2
  set σ₁' := 4 * τ₁ - 1
  have hσ₁ : 0 < σ₁ := by simp only [σ₁]; linarith
  have hσ₁' : 0 < σ₁' := by simp only [σ₁']; linarith
  set E := expTw τ₁
  have hE0 : 0 ≤ E := expTw_nonneg h1
  set R : ℝ := 2 * (‖w₀‖ + |r|) + 9 / 2
  set T : ℝ := ‖(tauG ψ₀)⁻¹‖
  have hq1 : (1 : ℝ) < q := by exact_mod_cast hq.out.one_lt
  have hqr := qpow_rpow_lt_one (q := q) hσ₁
  have hden : 0 < 1 - (q : ℝ) ^ (-σ₁) := by linarith
  have hC := stripC_pos
  set C₀ : ℝ := T / Real.sqrt 2 * (8 * q / (1 - (q : ℝ) ^ (-σ₁))) * (stripC * (q : ℝ) ^ 3 * R ^ 3 + 2) *
    (q : ℝ) ^ gammaE σ₁'
  have hC₀ : 0 ≤ C₀ := by positivity
  refine ⟨C₀ * (4 * M' : ℝ) ^ E, by positivity, fun w hw n hn => ?_⟩
  haveI : NeZero (kmod n M') := ⟨(kmod_pos hn hM).ne'⟩
  obtain ⟨hre1, _⟩ := re_ge_of_mem_closedBall hw
  set k : ℝ := (kmod n M' : ℝ)
  have hk := kmod_one_le hn hM
  have hk0 : 0 < k := by linarith
  have hkn : (n.natAbs : ℝ) ≤ k := by
    simp only [k, kmod]; push_cast
    have : (1 : ℝ) ≤ 4 * M' := by have : (1 : ℝ) ≤ M' := by exact_mod_cast hM
                                  linarith
    nlinarith [(Nat.cast_nonneg n.natAbs : (0 : ℝ) ≤ n.natAbs)]
  have hk4 : (4 * n.natAbs : ℝ) ≤ k := by
    simp only [k, kmod]; push_cast
    have : (1 : ℝ) ≤ M' := by exact_mod_cast hM
    nlinarith [(Nat.cast_nonneg n.natAbs : (0 : ℝ) ≤ n.natAbs)]
  have hsre : (2 * w - 1 / 2).re = 2 * w.re - 1 / 2 := by simp
  have hure : (4 * w - 1).re = 4 * w.re - 1 := by simp
  have hs0 : 0 < (2 * w - 1 / 2).re := by rw [hsre]; linarith
  -- the four factors
  have hA := norm_LSeries_Qf_le ψ₀ hn hs0
  have hA' : ‖LSeries (fun c => Qf ψ₀ n c) (2 * w - 1 / 2)‖ ≤ 8 * q / (1 - (q : ℝ) ^ (-σ₁)) * k := by
    refine hA.trans ?_
    have hmono : (q : ℝ) ^ (-(2 * w - 1 / 2).re) ≤ (q : ℝ) ^ (-σ₁) :=
      Real.rpow_le_rpow_of_exponent_le hq1.le (by rw [hsre]; simp only [σ₁]; linarith)
    have hd2 : 0 < 1 - (q : ℝ) ^ (-(2 * w - 1 / 2).re) := by linarith
    rw [div_mul_eq_mul_div, div_le_div_iff₀ hd2 hden]
    have : 8 * (q : ℝ) * n.natAbs ≤ 8 * q * k := by nlinarith
    nlinarith [mul_le_mul this (by linarith : 1 - (q : ℝ) ^ (-σ₁) ≤ 1 - (q : ℝ) ^ (-(2 * w - 1 / 2).re))
      hden.le (by positivity)]
  have hB := norm_LFunction_chiTw_le ψ₀ hn hM h2 (s := 2 * w - 1 / 2) hs0.le
  have hsR : ‖2 * w - 1 / 2 - 4‖ ≤ R := by
    have := norm_le_of_mem_closedBall hw (-9 / 4)
    calc ‖2 * w - 1 / 2 - 4‖ = 2 * ‖w + (-9 / 4)‖ := by
          rw [show 2 * w - 1 / 2 - 4 = 2 * (w + (-9 / 4)) by ring, norm_mul]; norm_num
      _ ≤ 2 * (‖w₀‖ + |r| + ‖(-9 / 4 : ℂ)‖) := by linarith [le_abs_self r]
      _ = R := by simp only [R]; norm_num; ring
  have hB' : ‖DirichletCharacter.LFunction (chiTw ψ₀ hn hM) (2 * w - 1 / 2)‖ ≤
      (stripC * (q : ℝ) ^ 3 * R ^ 3 + 2) * k ^ 3 :=
    hB.trans (mul_le_mul_of_nonneg_right (by gcongr) (by positivity))
  have hEL := norm_LSeries_eLtw_le ψ₀ hn hM (s := 2 * w - 1 / 2) hs0
  rw [hsre] at hEL
  have hβ : betaE (2 * w.re - 1 / 2) ≤ betaE σ₁ := betaE_anti hσ₁ (by simp only [σ₁]; linarith)
  have hEL' : ‖LSeries (fun c => eLtw ψ₀ (n := n) (M' := M') c) (2 * w - 1 / 2)‖ ≤
      k * k ^ betaE σ₁ :=
    hEL.trans (mul_le_mul hk4 (Real.rpow_le_rpow_of_exponent_le hk hβ) (by positivity) (by positivity))
  haveI : NeZero (q * kmod n M') := ⟨mul_ne_zero hq.out.ne_zero (kmod_pos hn hM).ne'⟩
  have hD := norm_eulerTw_inv_le ψ₀ (N := q * kmod n M') (NeZero.ne _) (u := 4 * w - 1)
    (by rw [hure]; linarith)
  rw [hure] at hD
  have hγ : gammaE (4 * w.re - 1) ≤ gammaE σ₁' := gammaE_anti hσ₁' (by simp only [σ₁']; linarith)
  have hqk : (1 : ℝ) ≤ ((q * kmod n M' : ℕ) : ℝ) := by
    have : 1 ≤ q * kmod n M' := Nat.one_le_iff_ne_zero.2 (NeZero.ne _)
    exact_mod_cast this
  have hD' : ‖(eulerTw ψ₀ (q * kmod n M') (4 * w - 1))⁻¹‖ ≤ (q : ℝ) ^ gammaE σ₁' * k ^ gammaE σ₁' := by
    refine hD.trans ((Real.rpow_le_rpow_of_exponent_le hqk hγ).trans (le_of_eq ?_))
    rw [Nat.cast_mul, Real.mul_rpow (by positivity) (by positivity)]
  -- assembly
  have hnorm : ‖Dstw ψ₀ hn hM w‖ = T / Real.sqrt 2 *
      ‖LSeries (fun c => Qf ψ₀ n c) (2 * w - 1 / 2)‖ *
      ‖DirichletCharacter.LFunction (chiTw ψ₀ hn hM) (2 * w - 1 / 2)‖ *
      ‖LSeries (fun c => eLtw ψ₀ (n := n) (M' := M') c) (2 * w - 1 / 2)‖ *
      ‖(eulerTw ψ₀ (q * kmod n M') (4 * w - 1))⁻¹‖ := by
    unfold Dstw
    simp only [norm_mul, norm_div, norm_I_cpow_half, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 2))]
    simp only [T]; ring
  have hkE : k ^ (1 : ℝ) * k ^ (3 : ℝ) * (k * k ^ betaE σ₁) * k ^ gammaE σ₁' = k ^ E := by
    simp only [E, expTw]
    rw [show (5 : ℝ) + gammaE (4 * τ₁ - 1) + betaE (2 * τ₁ - 1 / 2) =
      1 + 3 + 1 + betaE σ₁ + gammaE σ₁' by simp only [σ₁, σ₁']; ring]
    rw [Real.rpow_add hk0, Real.rpow_add hk0, Real.rpow_add hk0, Real.rpow_add hk0, Real.rpow_one]
    ring
  have hkn' : k ^ E = (4 * M' : ℝ) ^ E * |(n : ℝ)| ^ E := by
    rw [← Real.mul_rpow (by positivity) (abs_nonneg _)]
    congr 1
    simp only [k, kmod]; push_cast; rw [Nat.cast_natAbs, Int.cast_abs]; ring
  rw [hnorm]
  have hT : 0 ≤ T / Real.sqrt 2 := by positivity
  calc T / Real.sqrt 2 * ‖LSeries (fun c => Qf ψ₀ n c) (2 * w - 1 / 2)‖ *
        ‖DirichletCharacter.LFunction (chiTw ψ₀ hn hM) (2 * w - 1 / 2)‖ *
        ‖LSeries (fun c => eLtw ψ₀ (n := n) (M' := M') c) (2 * w - 1 / 2)‖ *
        ‖(eulerTw ψ₀ (q * kmod n M') (4 * w - 1))⁻¹‖
      ≤ T / Real.sqrt 2 * (8 * q / (1 - (q : ℝ) ^ (-σ₁)) * k) *
          ((stripC * (q : ℝ) ^ 3 * R ^ 3 + 2) * k ^ 3) * (k * k ^ betaE σ₁) *
          ((q : ℝ) ^ gammaE σ₁' * k ^ gammaE σ₁') := by
        gcongr
    _ = C₀ * (k ^ (1 : ℝ) * k ^ (3 : ℝ) * (k * k ^ betaE σ₁) * k ^ gammaE σ₁') := by
        simp only [C₀]
        rw [Real.rpow_one, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        ring
    _ = C₀ * (4 * M' : ℝ) ^ E * |(n : ℝ)| ^ E := by rw [hkE, hkn']; ring

end Twist

end

end GaloisForLFunctions.RHTower.HalfWeight
