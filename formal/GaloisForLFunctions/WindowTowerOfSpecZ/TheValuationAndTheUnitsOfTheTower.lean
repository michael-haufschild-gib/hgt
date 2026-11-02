import GaloisForLFunctions.WindowTowerOfSpecZ.TheTowerOfSmallExtensions

/-!
# The valuation and the units of the tower

**Stage multiplicativity.** The stage at which an arithmetic function starts to act on the tower is
its first nonzero index. It is multiplicative (`mul_vanishesBelow`): if `f` vanishes below `a` and `g`
below `b`, then `f * g` vanishes below `ab` and `(f * g)(ab) = f(a)g(b)` — the only factorization of
`ab` with factors `≥ a` and `≥ b` is `a·b`. Hence on the tower:

* a product of folds acts exactly from the product of their stages on
  (`windowRep_mul_eq_zero_iff`): `ρ_A(f)ρ_A(g) = 0` iff `ab > ⌊e^A⌋`;
* a fold starting at `n₀ ≥ 2` is nilpotent of exact order: `ρ_A(x)^k = 0` iff `n₀^k > ⌊e^A⌋`
  (`windowRep_pow_eq_zero_iff`), i.e. its nilpotency index is `⌊log⌊e^A⌋/log n₀⌋ + 1`.

**Wiener's lemma for the window algebra** (`isUnit_windowRep_iff`): on a window of length `A ≥ 0`,
`ρ_A(f)` is invertible iff `f(1) ≠ 0`; the inverse is the truncated geometric series of the Hecke
part. Every window operator is `f(1)` plus a nilpotent, so its spectrum is the single point `f(1)`
(`isUnit_windowRep_sub_iff`). The window algebra is local with the folds as its radical: an operator
built from the Hecke shifts is invertible exactly when its identity coefficient is.
-/

noncomputable section

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ

/-! ### Stage multiplicativity -/

/-- `f` vanishes below `a`: `f(n) = 0` for `n < a`. -/
def VanishesBelow (a : ℕ) (f : ArithmeticFunction ℝ) : Prop := ∀ n, n < a → f n = 0

/-- **The stage of a product is the product of the stages.** -/
theorem mul_vanishesBelow {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) {f g : ArithmeticFunction ℝ}
    (hf : VanishesBelow a f) (hg : VanishesBelow b g) :
    VanishesBelow (a * b) (f * g) ∧ (f * g) (a * b) = f a * g b := by
  -- every factorization `x.1 x.2 = k` with `x.1 ≥ a`, `x.2 ≥ b` has `k ≥ ab`, with equality only at `(a,b)`
  have hterm : ∀ k, ∀ x ∈ k.divisorsAntidiagonal, x ≠ (a, b) → k ≤ a * b →
      f x.1 * g x.2 = 0 := fun k x hx hxab hk => by
    obtain ⟨hxk, _⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    by_cases h1 : x.1 < a
    · rw [hf _ h1, zero_mul]
    by_cases h2 : x.2 < b
    · rw [hg _ h2, mul_zero]
    exfalso
    push Not at h1 h2
    have hge : a * b ≤ x.1 * x.2 := Nat.mul_le_mul h1 h2
    rcases h1.lt_or_eq with h1' | h1'
    · have : (a + 1) * b ≤ x.1 * x.2 := Nat.mul_le_mul h1' h2
      nlinarith
    · rcases h2.lt_or_eq with h2' | h2'
      · have : a * (b + 1) ≤ x.1 * x.2 := Nat.mul_le_mul h1 h2'
        nlinarith
      · exact hxab (Prod.ext h1'.symm h2'.symm)
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [ArithmeticFunction.mul_apply]
    refine Finset.sum_eq_zero fun x hx => ?_
    refine hterm k x hx (fun h => ?_) hk.le
    rw [h] at hx
    obtain ⟨hxk, _⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    simp only at hxk
    omega
  · rw [ArithmeticFunction.mul_apply, Finset.sum_eq_single (a, b)]
    · exact fun x hx hxab => hterm _ x hx hxab le_rfl
    · intro h
      exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨rfl, by positivity⟩) h

/-- **Powers**: a function starting at `n₀` has `k`-th power starting at `n₀^k` with leading
coefficient `x(n₀)^k`. -/
theorem pow_vanishesBelow {n₀ : ℕ} (hn₀ : 1 ≤ n₀) {x : ArithmeticFunction ℝ}
    (hx : VanishesBelow n₀ x) (k : ℕ) :
    VanishesBelow (n₀ ^ k) (x ^ k) ∧ (x ^ k) (n₀ ^ k) = x n₀ ^ k := by
  induction k with
  | zero =>
    refine ⟨fun n hn => ?_, ?_⟩
    · rw [pow_zero] at hn ⊢
      rw [ArithmeticFunction.one_apply, if_neg (by omega)]
    · simp
  | succ k ih =>
    have h := mul_vanishesBelow (Nat.one_le_pow _ _ hn₀) hn₀ ih.1 hx
    rw [pow_succ, pow_succ, pow_succ, h.2, ih.2]
    exact ⟨h.1, rfl⟩

theorem mem_truncIdeal_of_vanishesBelow {N a : ℕ} {f : ArithmeticFunction ℝ}
    (hf : VanishesBelow a f) (hN : N < a) : f ∈ truncIdeal N :=
  fun n _ hn => hf n (by omega)

/-- `ρ_A(f) = 0` for a function starting at `a` with `f(a) ≠ 0` iff `a > ⌊e^A⌋`. -/
theorem windowRep_eq_zero_iff_lt {A : ℝ} {a : ℕ} (ha : 1 ≤ a) {f : ArithmeticFunction ℝ}
    (hf : VanishesBelow a f) (hfa : f a ≠ 0) : windowRep A f = 0 ↔ windowLevel A < a := by
  rw [← RingHom.mem_ker, ker_windowRep]
  constructor
  · intro h
    by_contra hle
    exact hfa (h a ha (not_lt.mp hle))
  · exact mem_truncIdeal_of_vanishesBelow hf

/-- **A product of folds acts from the product of their stages**: `ρ_A(f)ρ_A(g) = 0` iff
`ab > ⌊e^A⌋`. -/
theorem windowRep_mul_eq_zero_iff {A : ℝ} {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    {f g : ArithmeticFunction ℝ} (hf : VanishesBelow a f) (hg : VanishesBelow b g)
    (hfa : f a ≠ 0) (hgb : g b ≠ 0) :
    windowRep A f * windowRep A g = 0 ↔ windowLevel A < a * b := by
  obtain ⟨h1, h2⟩ := mul_vanishesBelow ha hb hf hg
  rw [← map_mul]
  exact windowRep_eq_zero_iff_lt (Nat.one_le_iff_ne_zero.mpr (by positivity)) h1
    (by rw [h2]; exact mul_ne_zero hfa hgb)

/-- **Exact nilpotency**: a fold starting at `n₀` has `ρ_A(x)^k = 0` iff `n₀^k > ⌊e^A⌋`. -/
theorem windowRep_pow_eq_zero_iff {A : ℝ} {n₀ : ℕ} (hn₀ : 1 ≤ n₀) {x : ArithmeticFunction ℝ}
    (hx : VanishesBelow n₀ x) (hx₀ : x n₀ ≠ 0) (k : ℕ) :
    windowRep A x ^ k = 0 ↔ windowLevel A < n₀ ^ k := by
  obtain ⟨h1, h2⟩ := pow_vanishesBelow hn₀ hx k
  rw [← map_pow]
  exact windowRep_eq_zero_iff_lt (Nat.one_le_pow _ _ hn₀) h1 (by rw [h2]; exact pow_ne_zero _ hx₀)

/-! ### Wiener's lemma -/

/-- `ρ_A(c·δ_1) = c`. -/
theorem windowRep_single_one (A c : ℝ) : windowRep A (single 1 c) = c • 1 := by
  have h : single 1 c = single 1 c * 1 := (mul_one _).symm
  refine LinearMap.ext fun H => Subtype.ext (funext fun u => ?_)
  rw [windowRep_apply, windowRepFun]
  by_cases hN : 1 ≤ windowLevel A
  · rw [Finset.sum_eq_single_of_mem 1 (Finset.mem_Icc.mpr ⟨le_rfl, hN⟩) fun n _ hn => by
      rw [single_apply, if_neg fun h => hn h.1, zero_div, zero_mul]]
    rw [single_apply_self one_ne_zero, Nat.cast_one, Real.sqrt_one, div_one, Real.log_one,
      windowShift_zero H.2]
    rfl
  · have hA0 : A < 0 := by
      by_contra h
      exact hN (Nat.one_le_floor_iff _ |>.mpr (Real.one_le_exp (not_lt.mp h)))
    have h0 : (H : ℝ → ℝ) u = 0 := H.2 u fun hm => by linarith [hm.1, hm.2]
    rw [Finset.sum_eq_zero fun n hn => absurd ((Finset.mem_Icc.mp hn).1.trans
      (Finset.mem_Icc.mp hn).2) hN]
    change 0 = c * (H : ℝ → ℝ) u
    rw [h0, mul_zero]

/-- The window module of a nonnegative length is nontrivial: its left end point is nonzero. -/
theorem windowRep_one_ne_zero {A : ℝ} (hA : 0 ≤ A) : (1 : Module.End ℝ (windowSupported A)) ≠ 0 := by
  intro h
  have := congrArg (fun φ : Module.End ℝ (windowSupported A) =>
    (φ ⟨leftEndPoint A, leftEndPoint_mem hA⟩ : ℝ → ℝ) (-A)) h
  simp only [Module.End.one_apply, LinearMap.zero_apply, Submodule.coe_zero, Pi.zero_apply] at this
  rw [leftEndPoint, Set.indicator_of_mem (Set.mem_singleton _)] at this
  exact one_ne_zero this

/-- **Wiener's lemma for the window algebra**: for `A ≥ 0`, `ρ_A(f)` is invertible iff `f(1) ≠ 0`. -/
theorem isUnit_windowRep_iff {A : ℝ} (hA : 0 ≤ A) (f : ArithmeticFunction ℝ) :
    IsUnit (windowRep A f) ↔ f 1 ≠ 0 := by
  set N := windowLevel A
  constructor
  · intro hu hf1
    -- `f ∈ m`, so `ρ_A(f)^{N+1} = 0`
    have hm : f ∈ truncIdeal 1 := mem_truncIdeal_one.mpr hf1
    have hpow : f ^ (N + 1) ∈ truncIdeal N :=
      truncIdeal_anti (by have := Nat.lt_two_pow_self (n := N + 1); omega)
        (pow_truncIdeal_one_le N (Ideal.pow_mem_pow hm (N + 1)))
    have h0 : windowRep A f ^ (N + 1) = 0 := by rw [← map_pow]; exact windowRep_eq_zero_of_mem hpow
    have hu' := hu.pow (N + 1)
    rw [h0, isUnit_zero_iff] at hu'
    exact windowRep_one_ne_zero hA hu'.symm
  · intro hf1
    set c := f 1
    -- `f = c(1 + y)` with `y ∈ m`; invert `1 + y` by the truncated geometric series
    set y := single 1 c⁻¹ * f - 1 with hydef
    have hc : single 1 c * single 1 c⁻¹ = (1 : ArithmeticFunction ℝ) := by
      rw [single_mul_single one_ne_zero one_ne_zero, mul_inv_cancel₀ hf1]
      ext n; rw [single_apply, ArithmeticFunction.one_apply]
      by_cases h : n = 1 <;> simp [h]
    have hy1 : y ∈ truncIdeal 1 := by
      rw [mem_truncIdeal_one, hydef, sub_apply', ArithmeticFunction.one_one,
        ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_one, Finset.sum_singleton,
        single_apply_self one_ne_zero, inv_mul_cancel₀ hf1, sub_self]
    have hfy : f = single 1 c * (1 + y) := by
      rw [hydef, add_sub_cancel, ← mul_assoc, hc, one_mul]
    set g := single 1 c⁻¹ * ∑ i ∈ Finset.range (N + 1), (-y) ^ i with hgdef
    have hpow : (-y) ^ (N + 1) ∈ truncIdeal N :=
      truncIdeal_anti (by have := Nat.lt_two_pow_self (n := N + 1); omega)
        (pow_truncIdeal_one_le N (Ideal.pow_mem_pow (Submodule.neg_mem _ hy1) (N + 1)))
    have hfg : f * g = 1 - (-y) ^ (N + 1) := by
      rw [hfy, hgdef, show single 1 c * (1 + y) * (single 1 c⁻¹ * ∑ i ∈ Finset.range (N + 1),
        (-y) ^ i) = (single 1 c * single 1 c⁻¹) * ((1 - -y) * ∑ i ∈ Finset.range (N + 1),
          (-y) ^ i) by ring, hc, one_mul, mul_neg_geom_sum]
    have hρ : windowRep A f * windowRep A g = 1 := by
      have h := windowRep_eq_zero_of_mem hpow
      rw [← map_mul, hfg, map_sub, map_one, h]
      exact sub_zero (1 : Module.End ℝ (windowSupported A))
    have hρ' : windowRep A g * windowRep A f = 1 := by
      rw [← map_mul, mul_comm, map_mul, hρ]
    exact ⟨⟨windowRep A f, windowRep A g, hρ, hρ'⟩, rfl⟩

/-- **One-point spectrum**: `ρ_A(f) − c` is invertible iff `c ≠ f(1)`. -/
theorem isUnit_windowRep_sub_iff {A : ℝ} (hA : 0 ≤ A) (f : ArithmeticFunction ℝ) (c : ℝ) :
    IsUnit (windowRep A (f - single 1 c)) ↔ c ≠ f 1 := by
  rw [isUnit_windowRep_iff hA, sub_apply', single_apply_self one_ne_zero, sub_ne_zero, ne_comm]

end GaloisForLFunctions.WindowTowerOfSpecZ
