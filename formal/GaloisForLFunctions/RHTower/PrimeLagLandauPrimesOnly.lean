import GaloisForLFunctions.RHTower.PowerLagLandauCriterion

/-!
# The prime-only lag criterion for the Riemann hypothesis

If the lag values `a_p = Φ(log p)` are bounded above at the primes alone, the Riemann hypothesis
holds.  The proper prime powers `p^k`, `k ≥ 2`, carry a Dirichlet series
`Σ_{p^k, k ≥ 2} (M − a_{p^k}) Λ(p^k) (p^k)^{−1−s}` that converges, hence is analytic, for
`Re s > Θ − 1`, far to the left of every point used in the prime-power argument; subtracting it
from the prime-power series leaves a nonnegative series to which Landau's theorem applies with the
same zero-side continuation.
-/

open Complex Filter Topology Set Metric
open ArithmeticFunction (vonMangoldt)

namespace RHTower

noncomputable section

/-! ## Proper prime powers -/

/-- Prime powers with exponent at least two. -/
def IsProperPrimePow (n : ℕ) : Prop := IsPrimePow n ∧ ¬ n.Prime

noncomputable instance : DecidablePred IsProperPrimePow := Classical.decPred _

theorem not_isProperPrimePow_zero : ¬ IsProperPrimePow 0 := fun h => not_isPrimePow_zero h.1

theorem isProperPrimePow_iff {n : ℕ} :
    IsProperPrimePow n ↔ ∃ p : ℕ, p.Prime ∧ ∃ j : ℕ, n = p ^ (j + 2) := by
  constructor
  · rintro ⟨hpp, hnp⟩
    obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff _).mp hpp
    rcases k with _ | k
    · omega
    rcases k with _ | k
    · exfalso; exact hnp (by simpa using hp)
    · exact ⟨p, hp, k, rfl⟩
  · rintro ⟨p, hp, j, rfl⟩
    refine ⟨(isPrimePow_nat_iff _).mpr ⟨p, j + 2, hp, by omega, rfl⟩, ?_⟩
    intro hprime
    have := ((Nat.Prime.pow_eq_iff hprime).mp rfl).2
    omega

/-- The parametrisation of the proper prime powers. -/
def properPowMap (y : Nat.Primes × ℕ) : ℕ := (y.1 : ℕ) ^ (y.2 + 2)

/-- The parametrisation `(p, j) ↦ p^{j+2}` of the proper prime powers is injective. -/
theorem properPow_injective : Function.Injective properPowMap := by
  rintro ⟨p, j⟩ ⟨q, k⟩ h
  simp only [properPowMap] at h
  have h' : (p : ℕ) ^ (j + 1 + 1) = (q : ℕ) ^ (k + 1 + 1) := h
  obtain ⟨hpq, hjk⟩ := Nat.Prime.pow_inj p.2 q.2 h'
  have hjk' : j = k := by omega
  subst hjk'
  congr 1
  exact Subtype.ext hpq

/-- `p^{−x} ≤ 3/4` for `p ≥ 2`, `x > 1/2`. -/
theorem rpow_neg_le_three_quarters {p : ℕ} (hp : 2 ≤ p) {x : ℝ} (hx : 1 / 2 < x) :
    (p : ℝ) ^ (-x) ≤ 3 / 4 := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hx0 : 0 ≤ x := by linarith
  have h1 : (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (p : ℝ) ^ x :=
    calc (2 : ℝ) ^ (1 / 2 : ℝ) ≤ (2 : ℝ) ^ x := Real.rpow_le_rpow_of_exponent_le (by norm_num) hx.le
      _ ≤ (p : ℝ) ^ x := Real.rpow_le_rpow (by norm_num) h2 hx0
  have hsq : (4 / 3 : ℝ) ≤ (2 : ℝ) ^ (1 / 2 : ℝ) := by
    rw [← Real.sqrt_eq_rpow]
    exact (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
  rw [Real.rpow_neg (by positivity)]
  have hpos : (0 : ℝ) < (p : ℝ) ^ x := by positivity
  rw [inv_le_comm₀ hpos (by norm_num)]
  linarith

/-- `Σ_{j ≥ 0} (j + 2)(3/4)^j` converges. -/
theorem summable_shifted_geometric :
    Summable fun j : ℕ => ((j : ℝ) + 2) * (3 / 4 : ℝ) ^ j := by
  have h1 : Summable fun j : ℕ => (j : ℝ) ^ 1 * (3 / 4 : ℝ) ^ j :=
    summable_pow_mul_geometric_of_norm_lt_one 1 (by rw [Real.norm_eq_abs]; norm_num)
  have h2 : Summable fun j : ℕ => (3 / 4 : ℝ) ^ j := summable_geometric_of_lt_one (by norm_num) (by norm_num)
  refine (h1.add (h2.mul_left 2)).congr fun j => ?_
  ring

/-- The proper-prime-power logarithmic term. -/
def properLogTerm (x : ℝ) (n : ℕ) : ℝ :=
  if IsProperPrimePow n then Real.log n * (n : ℝ) ^ (-x) else 0

theorem properLogTerm_eq_zero_of_notMem_range {x : ℝ} {n : ℕ} (hn : n ∉ Set.range properPowMap) :
    properLogTerm x n = 0 := by
  unfold properLogTerm
  rw [if_neg]
  intro hpp
  obtain ⟨p, hp, j, rfl⟩ := isProperPrimePow_iff.mp hpp
  exact hn ⟨(⟨p, hp⟩, j), rfl⟩

theorem properLogTerm_comp (x : ℝ) (y : Nat.Primes × ℕ) :
    properLogTerm x (properPowMap y)
      = ((y.2 : ℝ) + 2) * Real.log (y.1 : ℕ) * ((y.1 : ℕ) : ℝ) ^ (-((y.2 : ℝ) + 2) * x) := by
  obtain ⟨p, j⟩ := y
  have hpp : IsProperPrimePow ((p : ℕ) ^ (j + 2)) := isProperPrimePow_iff.mpr ⟨p, p.2, j, rfl⟩
  unfold properLogTerm properPowMap
  rw [if_pos hpp]
  have hp0 : (0 : ℝ) ≤ (p : ℕ) := Nat.cast_nonneg _
  rw [Nat.cast_pow, Real.log_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp0]
  push_cast
  ring_nf

/-- The termwise bound `(j+2) log p · p^{−(j+2)x} ≤ log p · p^{−2x} · (j+2)(3/4)^j`. -/
theorem properLogTerm_comp_le {x : ℝ} (hx : 1 / 2 < x) (y : Nat.Primes × ℕ) :
    properLogTerm x (properPowMap y)
      ≤ Real.log (y.1 : ℕ) * ((y.1 : ℕ) : ℝ) ^ (-(2 * x))
        * (((y.2 : ℝ) + 2) * (3 / 4 : ℝ) ^ y.2) := by
  obtain ⟨p, j⟩ := y
  rw [properLogTerm_comp]
  have hp2 : 2 ≤ (p : ℕ) := p.2.two_le
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast (by omega : 0 < (p : ℕ))
  have hlog : 0 ≤ Real.log (p : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ (p : ℕ)))
  have hsplit : ((p : ℕ) : ℝ) ^ (-((j : ℝ) + 2) * x)
      = ((p : ℕ) : ℝ) ^ (-(2 * x)) * (((p : ℕ) : ℝ) ^ (-x)) ^ j := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_add hp0]
    congr 1; ring
  have hle : (((p : ℕ) : ℝ) ^ (-x)) ^ j ≤ (3 / 4 : ℝ) ^ j :=
    pow_le_pow_left₀ (by positivity) (rpow_neg_le_three_quarters hp2 hx) j
  rw [hsplit]
  have h0 : 0 ≤ ((j : ℝ) + 2) * Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-(2 * x)) := by positivity
  calc ((j : ℝ) + 2) * Real.log (p : ℕ)
        * (((p : ℕ) : ℝ) ^ (-(2 * x)) * (((p : ℕ) : ℝ) ^ (-x)) ^ j)
      = (((j : ℝ) + 2) * Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-(2 * x)))
          * (((p : ℕ) : ℝ) ^ (-x)) ^ j := by ring
    _ ≤ (((j : ℝ) + 2) * Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-(2 * x))) * (3 / 4 : ℝ) ^ j := by
        gcongr
    _ = _ := by ring

theorem properLogTerm_comp_nonneg (x : ℝ) (y : Nat.Primes × ℕ) :
    0 ≤ properLogTerm x (properPowMap y) := by
  rw [properLogTerm_comp]
  have : 0 ≤ Real.log (y.1 : ℕ) :=
    Real.log_nonneg (by exact_mod_cast (by have := y.1.2.two_le; omega : 1 ≤ (y.1 : ℕ)))
  positivity

/-- The constant `Σ_{j ≥ 0} (j + 2)(3/4)^j`. -/
def shiftedGeomSum : ℝ := ∑' j : ℕ, ((j : ℝ) + 2) * (3 / 4 : ℝ) ^ j

theorem shiftedGeomSum_nonneg : 0 ≤ shiftedGeomSum :=
  tsum_nonneg fun j => by positivity

/-- The row `j ↦ log p · p^{−2x} · (j+2)(3/4)^j` is summable. -/
theorem summable_properMajorant_row (x : ℝ) (p : Nat.Primes) :
    Summable fun j : ℕ =>
      Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-(2 * x)) * (((j : ℝ) + 2) * (3 / 4 : ℝ) ^ j) :=
  summable_shifted_geometric.mul_left _

theorem tsum_properMajorant_row (x : ℝ) (p : Nat.Primes) :
    ∑' j : ℕ, Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-(2 * x)) * (((j : ℝ) + 2) * (3 / 4 : ℝ) ^ j)
      = Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-(2 * x)) * shiftedGeomSum := by
  unfold shiftedGeomSum
  rw [tsum_mul_left]

theorem log_nonneg_prime (p : Nat.Primes) : 0 ≤ Real.log (p : ℕ) :=
  Real.log_nonneg (by exact_mod_cast (by have := p.2.two_le; omega : 1 ≤ (p : ℕ)))

/-- `log p · p^{−2x} ≤ (1/ε) p^{−(1+ε)}` with `ε = (2x − 1)/2`. -/
theorem log_mul_rpow_le_prime {x : ℝ} (hx : 1 / 2 < x) (p : Nat.Primes) :
    Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-(2 * x))
      ≤ (1 / ((2 * x - 1) / 2)) * ((p : ℕ) : ℝ) ^ (-(1 + (2 * x - 1) / 2)) := by
  have hεpos : 0 < (2 * x - 1) / 2 := by linarith
  have hp0 : (0 : ℝ) < (p : ℕ) := by exact_mod_cast p.2.pos
  have hlog : Real.log (p : ℕ) ≤ ((p : ℕ) : ℝ) ^ ((2 * x - 1) / 2) / ((2 * x - 1) / 2) :=
    Real.log_le_rpow_div hp0.le hεpos
  have hr : 0 ≤ ((p : ℕ) : ℝ) ^ (-(2 * x)) := by positivity
  calc Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-(2 * x))
      ≤ ((p : ℕ) : ℝ) ^ ((2 * x - 1) / 2) / ((2 * x - 1) / 2) * ((p : ℕ) : ℝ) ^ (-(2 * x)) := by
        gcongr
    _ = (1 / ((2 * x - 1) / 2))
          * (((p : ℕ) : ℝ) ^ ((2 * x - 1) / 2) * ((p : ℕ) : ℝ) ^ (-(2 * x))) := by ring
    _ = (1 / ((2 * x - 1) / 2)) * ((p : ℕ) : ℝ) ^ (-(1 + (2 * x - 1) / 2)) := by
        rw [← Real.rpow_add hp0]; congr 2; ring

/-- The column sums are summable over the primes. -/
theorem summable_properMajorant_col {x : ℝ} (hx : 1 / 2 < x) :
    Summable fun p : Nat.Primes =>
      Real.log (p : ℕ) * ((p : ℕ) : ℝ) ^ (-(2 * x)) * shiftedGeomSum := by
  have hs : Summable fun p : Nat.Primes =>
      (1 / ((2 * x - 1) / 2)) * ((p : ℕ) : ℝ) ^ (-(1 + (2 * x - 1) / 2)) * shiftedGeomSum :=
    ((Nat.Primes.summable_rpow.mpr (by linarith)).mul_left _).mul_right _
  refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hs
  · have := log_nonneg_prime p
    have := shiftedGeomSum_nonneg
    positivity
  · exact mul_le_mul_of_nonneg_right (log_mul_rpow_le_prime hx p) shiftedGeomSum_nonneg

/-- The product majorant `log p · p^{−2x} · (j+2)(3/4)^j` is summable for `x > 1/2`. -/
theorem summable_properMajorant {x : ℝ} (hx : 1 / 2 < x) :
    Summable fun y : Nat.Primes × ℕ =>
      Real.log (y.1 : ℕ) * ((y.1 : ℕ) : ℝ) ^ (-(2 * x)) * (((y.2 : ℝ) + 2) * (3 / 4 : ℝ) ^ y.2) := by
  have hnn : ∀ y : Nat.Primes × ℕ, 0 ≤ Real.log (y.1 : ℕ) * ((y.1 : ℕ) : ℝ) ^ (-(2 * x))
      * (((y.2 : ℝ) + 2) * (3 / 4 : ℝ) ^ y.2) := by
    intro y
    have := log_nonneg_prime y.1
    positivity
  rw [summable_prod_of_nonneg hnn]
  refine ⟨fun p => summable_properMajorant_row x p, ?_⟩
  have hcol := summable_properMajorant_col hx
  refine hcol.congr fun p => ?_
  exact (tsum_properMajorant_row x p).symm

/-- The proper-prime-power sum `Σ log n · n^{−x}` converges for `x > 1/2`. -/
theorem summable_properPrimePow_log_rpow {x : ℝ} (hx : 1 / 2 < x) :
    Summable (properLogTerm x) := by
  rw [← properPow_injective.summable_iff (fun n hn => properLogTerm_eq_zero_of_notMem_range hn)]
  exact Summable.of_nonneg_of_le (fun y => properLogTerm_comp_nonneg x y)
    (fun y => properLogTerm_comp_le hx y) (summable_properMajorant hx)

/-! ## The prime-only and proper-power coefficients -/

/-- The coefficient restricted to the primes. -/
def primeOnlyCoeff (M : ℝ) (n : ℕ) : ℝ := if n.Prime then primeLagCoeff M n else 0

/-- The coefficient restricted to the proper prime powers. -/
def properCoeff (M : ℝ) (n : ℕ) : ℝ := if n.Prime then 0 else primeLagCoeff M n

theorem primeLagCoeff_eq_primeOnly_add_proper (M : ℝ) (n : ℕ) :
    primeLagCoeff M n = primeOnlyCoeff M n + properCoeff M n := by
  unfold primeOnlyCoeff properCoeff
  split_ifs <;> ring

theorem primeOnlyCoeff_nonneg {M : ℝ} (hM : ∀ p : ℕ, p.Prime → integerLag p ≤ M) (n : ℕ) :
    0 ≤ primeOnlyCoeff M n := by
  unfold primeOnlyCoeff
  split_ifs with hp
  · unfold primeLagCoeff
    have h1 : 0 ≤ M - integerLag n := by linarith [hM n hp]
    have h2 : 0 ≤ vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    positivity
  · exact le_rfl

theorem properCoeff_eq_zero {M : ℝ} {n : ℕ} (h : ¬ IsProperPrimePow n) : properCoeff M n = 0 := by
  unfold properCoeff
  split_ifs with hp
  · rfl
  · unfold primeLagCoeff
    have hΛ : vonMangoldt n = 0 := by
      by_contra hne
      exact h ⟨ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hne, hp⟩
    rw [hΛ]; ring

/-- The proper-power coefficient is dominated by `(|M| + W) · [proper n] · log n · n^{θ − 3/2}`. -/
theorem abs_properCoeff_le {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ) (hθ2 : 1 / 2 ≤ θ)
    {M : ℝ} {n : ℕ} (hn : 1 ≤ n) :
    |properCoeff M n| ≤ (|M| + lagWeightTotal)
      * (if IsProperPrimePow n then Real.log n * (n : ℝ) ^ (θ - 3 / 2) else 0) := by
  classical
  by_cases h : IsProperPrimePow n
  · rw [if_pos h]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have h1 : |properCoeff M n| ≤ |primeLagCoeff M n| := by
      unfold properCoeff
      split_ifs
      · simp
      · exact le_rfl
    refine h1.trans ?_
    refine (abs_lagCoeff_le hθ hθ2 hn).trans (le_of_eq ?_)
    have : (n : ℝ) ^ (θ - 1 / 2) / n = (n : ℝ) ^ (θ - 3 / 2) := by
      rw [show θ - 3 / 2 = θ - 1 / 2 - 1 by ring, Real.rpow_sub_one hn0.ne']
    rw [mul_div_assoc, this]
    ring
  · rw [if_neg h, properCoeff_eq_zero h, abs_zero, mul_zero]

/-- The proper-power series converges for `Re s > θ − 1`. -/
theorem properCoeff_LSeriesSummable {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hθ2 : 1 / 2 ≤ θ) {M : ℝ} {s : ℂ} (hs : θ - 1 < s.re) :
    LSeriesSummable (fun n => (properCoeff M n : ℂ)) s := by
  classical
  set x : ℝ := s.re + 3 / 2 - θ with hx
  have hx12 : 1 / 2 < x := by rw [hx]; linarith
  have hmaj := (summable_properPrimePow_log_rpow hx12).mul_left (|M| + lagWeightTotal)
  refine Summable.of_norm_bounded hmaj fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero, properLogTerm, not_isProperPrimePow_zero]
  · rw [LSeries.term_of_ne_zero hn.ne', norm_div, Complex.norm_natCast_cpow_of_pos hn,
      Complex.norm_real, Real.norm_eq_abs]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hW := lagWeightTotal_nonneg
    have hb := abs_properCoeff_le hθ hθ2 (M := M) hn
    rw [div_le_iff₀ (by positivity)]
    refine hb.trans (le_of_eq ?_)
    unfold properLogTerm
    by_cases h : IsProperPrimePow n
    · rw [if_pos h, if_pos h]
      have e : (n : ℝ) ^ (-x) * (n : ℝ) ^ s.re = (n : ℝ) ^ (θ - 3 / 2) := by
        rw [← Real.rpow_add hn0]; congr 1; rw [hx]; ring
      rw [← e]
      ring
    · rw [if_neg h, if_neg h]
      simp

/-- The proper-power series is differentiable on `Re s > θ − 1`. -/
theorem differentiableAt_LSeries_properCoeff {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hθ2 : 1 / 2 ≤ θ) {M : ℝ} {s : ℂ} (hs : θ - 1 < s.re) :
    DifferentiableAt ℂ (LSeries (fun n => (properCoeff M n : ℂ))) s := by
  have habs : LSeries.abscissaOfAbsConv (fun n => (properCoeff M n : ℂ)) ≤ ((θ - 1 : ℝ) : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      properCoeff_LSeriesSummable hθ hθ2 (by simpa using hy)
  exact (LSeries_analyticOnNhd _ s (lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr hs))).differentiableAt

/-! ## The prime-only series and its continuation -/

theorem primeOnlyCoeff_fun_eq (M : ℝ) :
    (fun n => (primeOnlyCoeff M n : ℂ))
      = (fun n => (primeLagCoeff M n : ℂ)) - (fun n => (properCoeff M n : ℂ)) := by
  funext n
  simp only [Pi.sub_apply]
  rw [primeLagCoeff_eq_primeOnly_add_proper]
  push_cast
  ring

/-- The prime-only series converges for `Re s > θ − 1/2`. -/
theorem primeOnlyCoeff_LSeriesSummable {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hθ2 : 1 / 2 ≤ θ) {M : ℝ} {s : ℂ} (hs : θ - 1 / 2 < s.re) :
    LSeriesSummable (fun n => (primeOnlyCoeff M n : ℂ)) s := by
  rw [primeOnlyCoeff_fun_eq]
  exact (lagCoeff_LSeriesSummable hθ hθ2 hs).sub (properCoeff_LSeriesSummable hθ hθ2 (by linarith))

/-- The prime-only continuation `G_M − T`. -/
def primeOnlyG (M : ℝ) (s : ℂ) : ℂ :=
  landauG M s - LSeries (fun n => (properCoeff M n : ℂ)) s

/-- The prime-only series equals `G_M − T` on `Re s > θ − 1/2`. -/
theorem LSeries_primeOnlyCoeff_eq {θ : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hθ2 : 1 / 2 ≤ θ) {M : ℝ} {s : ℂ} (hs : θ - 1 / 2 < s.re) :
    LSeries (fun n => (primeOnlyCoeff M n : ℂ)) s = primeOnlyG M s := by
  rw [primeOnlyCoeff_fun_eq,
    LSeries_sub (lagCoeff_LSeriesSummable hθ hθ2 hs) (properCoeff_LSeriesSummable hθ hθ2 (by linarith)),
    LSeries_lagCoeff_eq hθ hθ2 hs]
  rfl

theorem differentiableOn_primeOnlyG {θ η t₀ r M : ℝ} (hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ θ)
    (hθ2 : 1 / 2 ≤ θ) (hθ34 : θ ≤ 3 / 4) (hη : η ≤ 1 / 20) (hr1 : r ≤ 1) {U : Set ℂ}
    (hUbox : U ⊆ landauBox θ η t₀ r) (hpos : ∀ s ∈ U, 0 < s.re)
    (hnear : ∀ q ∈ nearSet t₀, ∀ s ∈ U, s + 3 / 2 - (q.1 : ℂ) ≠ 1) :
    DifferentiableOn ℂ (primeOnlyG M) U := by
  have h1 := differentiableOn_landauG (M := M) hθ hθ34 hη hr1 hUbox hpos hnear
  have h2 : DifferentiableOn ℂ (LSeries (fun n => (properCoeff M n : ℂ))) U := by
    intro s hs
    have := (hUbox hs).1
    exact (differentiableAt_LSeries_properCoeff hθ hθ2 (M := M) (by linarith)).differentiableWithinAt
  exact h1.sub h2

/-! ## The Landau transfer step for the primes -/

theorem primesOnly_transfer_step {M : ℝ} (hM : ∀ p : ℕ, p.Prime → integerLag p ≤ M)
    (hRH : ¬ RiemannHypothesis) :
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 / 20 ∧ η < zeroReSup - 1 / 2 ∧
      (∀ q : XiZeroCopy, |zeroOrdinate q| ≤ 6 → 3 * η ≤ |zeroOrdinate q| / 2) ∧
      LSeriesSummable (fun n => (primeOnlyCoeff M n : ℂ)) ((zeroReSup - 1 / 2 - η / 4 : ℝ) : ℂ) := by
  obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_re_gt_half_of_not_rh hRH
  haveI : Nonempty XiZeroCopy := ⟨q₁⟩
  set Θ := zeroReSup with hΘ
  have hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ Θ := re_le_zeroReSup
  have hΘ12 : 1 / 2 < Θ := lt_of_lt_of_le hq₁ (re_le_zeroReSup q₁)
  have hΘ34 : Θ ≤ 3 / 4 := zeroReSup_le (re_le_three_quarters_of_primeLag_le hM)
  obtain ⟨γmin, hγpos, hγmin⟩ := exists_pos_le_abs_ordinate
  set η : ℝ := min (1 / 20) (min ((Θ - 1 / 2) / 2) (γmin / 6)) with hη
  have hηpos : 0 < η := lt_min (by norm_num) (lt_min (by linarith) (by linarith))
  have hη20 : η ≤ 1 / 20 := min_le_left _ _
  have hηΘ : η ≤ (Θ - 1 / 2) / 2 := (min_le_right _ _).trans (min_le_left _ _)
  have hηγ : η ≤ γmin / 6 := (min_le_right _ _).trans (min_le_right _ _)
  have hηΘ' : η < Θ - 1 / 2 := by linarith
  refine ⟨η, hηpos, hη20, hηΘ', fun q hq => by linarith [hγmin q hq], ?_⟩
  have hsum : LSeriesSummable (fun n => (primeOnlyCoeff M n : ℂ)) ((Θ - 1 / 2 + η : ℝ) : ℂ) :=
    primeOnlyCoeff_LSeriesSummable hθ hΘ12.le (by simp; linarith)
  set R : NNReal := ⟨5 * η / 2, by positivity⟩ with hR
  have hRval : (R : ℝ) = 5 * η / 2 := rfl
  have hball : closedBall (((Θ - 1 / 2 + η) + η : ℝ) : ℂ) (R : ℝ) ⊆ landauBox Θ η 0 (3 * η) := by
    intro s hs
    rw [mem_closedBall, Complex.dist_eq] at hs
    have hre := Complex.abs_re_le_norm (s - (((Θ - 1 / 2 + η) + η : ℝ) : ℂ))
    have him := Complex.abs_im_le_norm (s - (((Θ - 1 / 2 + η) + η : ℝ) : ℂ))
    rw [Complex.sub_re, Complex.ofReal_re] at hre
    rw [Complex.sub_im, Complex.ofReal_im, sub_zero] at him
    rw [hRval] at hs
    have h1 := (abs_le.mp (hre.trans hs)).1
    have h2 := (abs_le.mp (hre.trans hs)).2
    refine ⟨by linarith, by linarith, ?_⟩
    rw [sub_zero]
    linarith [him.trans hs]
  have hGd : DifferentiableOn ℂ (primeOnlyG M)
      (closedBall (((Θ - 1 / 2 + η) + η : ℝ) : ℂ) (R : ℝ)) := by
    refine (differentiableOn_primeOnlyG (θ := Θ) (η := η) (t₀ := 0) (r := 3 * η) (M := M) hθ
      hΘ12.le hΘ34 hη20 (by linarith) (U := landauBox Θ η 0 (3 * η)) le_rfl ?_ ?_).mono hball
    · intro s hs
      have := hs.1
      linarith
    · intro q hq s hs h1
      have hqn : |zeroOrdinate q - 0| < 5 := hq
      rw [sub_zero] at hqn
      have hq6 : |zeroOrdinate q| ≤ 6 := by linarith
      have hγ := hγmin q hq6
      have him : (s + 3 / 2 - (q.1 : ℂ)).im = s.im - zeroOrdinate q := by simp [zeroOrdinate]
      rw [h1, Complex.one_im] at him
      have hs3 := hs.2.2
      rw [sub_zero] at hs3
      have habs : |zeroOrdinate q| = |s.im| := by
        rw [show zeroOrdinate q = s.im by linarith]
      linarith
  have hagree : ∀ s : ℂ, Θ - 1 / 2 + η < s.re →
      primeOnlyG M s = LSeries (fun n => (primeOnlyCoeff M n : ℂ)) s := by
    intro s hs
    exact (LSeries_primeOnlyCoeff_eq hθ hΘ12.le (by linarith)).symm
  exact landau_local_summability_transfer (a := primeOnlyCoeff M) (primeOnlyCoeff_nonneg hM)
    (σ₁ := Θ - 1 / 2 + η) (h := η) hηpos hsum (R := R) (G := primeOnlyG M) hGd hagree
    (σ := Θ - 1 / 2 - η / 4) (by rw [hRval]; linarith)

/-! ## The criterion -/

/-- **Bounded prime lags force the Riemann hypothesis.** -/
theorem riemannHypothesis_of_primeLag_le {M : ℝ}
    (hM : ∀ p : ℕ, p.Prime → integerLag p ≤ M) : RiemannHypothesis := by
  by_contra hRH
  obtain ⟨η, hηpos, hη20, hηΘ, -, hsumσ⟩ := primesOnly_transfer_step hM hRH
  obtain ⟨q₁', hq₁'⟩ := exists_xiZeroCopy_re_gt_half_of_not_rh hRH
  haveI : Nonempty XiZeroCopy := ⟨q₁'⟩
  set Θ := zeroReSup with hΘ
  have hθ : ∀ q : XiZeroCopy, (q.1 : ℂ).re ≤ Θ := re_le_zeroReSup
  have hΘ12 : 1 / 2 < Θ := lt_of_lt_of_le hq₁' (re_le_zeroReSup q₁')
  have hΘ34 : Θ ≤ 3 / 4 := zeroReSup_le (re_le_three_quarters_of_primeLag_le hM)
  set c : ℕ → ℂ := fun n => (primeOnlyCoeff M n : ℂ) with hc
  set σ : ℝ := Θ - 1 / 2 - η / 4 with hσ
  have habs : LSeries.abscissaOfAbsConv c ≤ (σ : EReal) :=
    LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
      hsumσ.of_re_le_re (by simp; linarith)
  have hFd : ∀ z : ℂ, σ < z.re → DifferentiableAt ℂ (LSeries c) z := fun z hz =>
    (LSeries_analyticOnNhd c z
      (lt_of_le_of_lt habs (EReal.coe_lt_coe_iff.mpr hz))).differentiableAt
  obtain ⟨q₁, hq₁⟩ := exists_re_gt_of_lt_zeroReSup (b := Θ - η / 8) (by linarith)
  set ρ₁ : ℂ := (q₁.1 : ℂ) with hρ₁
  set K : Set ℂ := Set.Icc ρ₁.re 1 ×ℂ Set.Icc ρ₁.im ρ₁.im with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hfin : (xiZeroSet_weilLagFunctionCriterion ∩ K).Finite := finite_xiZeroSet_inter hKc
  have hmem₁ : ρ₁ ∈ xiZeroSet_weilLagFunctionCriterion ∩ K := by
    refine ⟨xi_xiZeroCopy_eq_zero q₁, ?_⟩
    rw [hK, Complex.mem_reProdIm]
    exact ⟨⟨le_rfl, (xiZeroCopy_re_lt_one q₁).le⟩, ⟨le_rfl, le_rfl⟩⟩
  obtain ⟨ρ₀, hρ₀⟩ := hfin.exists_maximalFor Complex.re _ ⟨ρ₁, hmem₁⟩
  have hρ₀mem : ρ₀ ∈ xiZeroSet_weilLagFunctionCriterion ∩ K := hρ₀.1
  have hmax : ∀ z ∈ xiZeroSet_weilLagFunctionCriterion ∩ K, ρ₀.re ≤ z.re → z.re ≤ ρ₀.re := fun z hz h => hρ₀.2 hz h
  obtain ⟨q₀, hq₀⟩ := exists_xiZeroCopy_of_xi_eq_zero hρ₀mem.1
  have hρ₀K := hρ₀mem.2
  rw [hK, Complex.mem_reProdIm] at hρ₀K
  have hre₀ : Θ - η / 8 < ρ₀.re := lt_of_lt_of_le hq₁ hρ₀K.1.1
  have hre₀' : ρ₀.re < 1 := by have := xiZeroCopy_re_lt_one q₀; rwa [hq₀] at this
  have him₀ : ρ₀.im = ρ₁.im := le_antisymm hρ₀K.2.2 hρ₀K.2.1
  have hmaxq : ∀ q : XiZeroCopy, zeroOrdinate q = zeroOrdinate q₀ →
      (q.1 : ℂ).re ≤ (q₀.1 : ℂ).re := by
    intro q hq
    rw [hq₀]
    by_contra hlt
    push Not at hlt
    have hmemK : (q.1 : ℂ) ∈ xiZeroSet_weilLagFunctionCriterion ∩ K := by
      refine ⟨xi_xiZeroCopy_eq_zero q, ?_⟩
      rw [hK, Complex.mem_reProdIm]
      refine ⟨⟨by linarith [hρ₀K.1.1], (xiZeroCopy_re_lt_one q).le⟩, ?_⟩
      have : (q.1 : ℂ).im = ρ₁.im := by
        unfold zeroOrdinate at hq; rw [hq, hq₀, him₀]
      rw [this]; exact ⟨le_rfl, le_rfl⟩
    have := hmax _ hmemK hlt.le
    linarith
  have hβ₀ : Θ - η < (q₀.1 : ℂ).re := by rw [hq₀]; linarith
  have hβ₀' : 1 / 2 < (q₀.1 : ℂ).re := by rw [hq₀]; linarith
  obtain ⟨C, hC⟩ := landauG_ray_lower_bound (M := M) hθ hΘ34 hη20 hηpos q₀ hβ₀ hβ₀' hmaxq
  -- the proper-power series is bounded on the closed ray segment
  have hTc : ContinuousOn (fun t : ℝ => LSeries (fun n => (properCoeff M n : ℂ)) ((q₀.1 : ℂ) - 1 / 2 + t))
      (Icc (0 : ℝ) (1 / 4)) := by
    intro t ht
    have hd : DifferentiableAt ℂ (LSeries (fun n => (properCoeff M n : ℂ))) ((q₀.1 : ℂ) - 1 / 2 + t) := by
      apply differentiableAt_LSeries_properCoeff hθ hΘ12.le
      simp [hq₀]; linarith [ht.1]
    have hc : ContinuousAt (fun t : ℝ => (q₀.1 : ℂ) - 1 / 2 + (t : ℂ)) t :=
      (continuous_const.add Complex.continuous_ofReal).continuousAt
    exact (ContinuousAt.comp (g := LSeries (fun n => (properCoeff M n : ℂ)))
      (f := fun t : ℝ => (q₀.1 : ℂ) - 1 / 2 + (t : ℂ)) hd.continuousAt hc).continuousWithinAt
  obtain ⟨BT, hBT⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1 / 4)).exists_bound_of_continuousOn hTc
  have hC' : ∀ t : ℝ, 0 < t → t ≤ 1 / 4 →
      ‖aliasedWeight q₀‖ / t - (C + BT) ≤ ‖primeOnlyG M ((q₀.1 : ℂ) - 1 / 2 + t)‖ := by
    intro t ht ht4
    have h1 := hC t ht ht4
    have h2 := hBT t ⟨ht.le, ht4⟩
    unfold primeOnlyG
    have := norm_sub_norm_le (landauG M ((q₀.1 : ℂ) - 1 / 2 + t))
      (LSeries (fun n => (properCoeff M n : ℂ)) ((q₀.1 : ℂ) - 1 / 2 + t))
    linarith
  -- the ray box
  set γ₀ : ℝ := zeroOrdinate q₀ with hγ₀
  have hγ₀im : ρ₀.im = γ₀ := by rw [hγ₀]; unfold zeroOrdinate; rw [hq₀]
  obtain ⟨r, hrpos, hr1, hrgap⟩ := exists_pos_le_ordinate_gap γ₀
  set U₀ : Set ℂ := landauBox ρ₀.re 0 γ₀ r with hU₀
  have hU₀open : IsOpen U₀ := isOpen_landauBox _ _ _ _
  have hGd : DifferentiableOn ℂ (primeOnlyG M) U₀ := by
    refine differentiableOn_primeOnlyG (θ := Θ) (η := η) (t₀ := γ₀) (r := r) hθ hΘ12.le hΘ34 hη20
      hr1 (U := U₀) ?_ ?_ ?_
    · intro s hs
      exact ⟨by linarith [hs.1], hs.2.1, hs.2.2⟩
    · intro s hs
      linarith [hs.1]
    · intro q hq s hs h1
      have him : s.im = zeroOrdinate q := by
        have := congrArg Complex.im h1
        simp at this
        unfold zeroOrdinate
        linarith
      have hre : s.re = (q.1 : ℂ).re - 1 / 2 := by
        have := congrArg Complex.re h1
        simp at this
        linarith
      by_cases hord : zeroOrdinate q = γ₀
      · have := hmaxq q hord
        rw [hq₀] at this
        have hs1 := hs.1
        linarith
      · have hgap := hrgap q hq hord
        have hs3 := hs.2.2
        rw [him] at hs3
        linarith
  set p₀ : ℂ := ρ₀ - 1 / 2 with hp₀
  set ℓ : ℝ → ℂ := fun t => p₀ + t with hℓ
  have hℓan : ∀ t : ℝ, AnalyticAt ℝ ℓ t := fun t =>
    analyticAt_const.add (Complex.ofRealCLM.analyticAt t)
  have hℓeq : ∀ t : ℝ, ℓ t = (q₀.1 : ℂ) - 1 / 2 + t := fun t => by rw [hℓ, hp₀, hq₀]
  have hℓre : ∀ t : ℝ, (ℓ t).re = ρ₀.re - 1 / 2 + t := fun t => by rw [hℓ, hp₀]; simp
  have hℓim : ∀ t : ℝ, (ℓ t).im = γ₀ := fun t => by rw [hℓ, hp₀]; simp [hγ₀im]
  set U : Set ℝ := Ioo (0 : ℝ) (1 / 4) with hU
  have hℓU₀ : ∀ t ∈ U, ℓ t ∈ U₀ := by
    intro t ht
    refine ⟨?_, ?_, ?_⟩
    · rw [hℓre]; linarith [ht.1]
    · rw [hℓre]; linarith [ht.2]
    · rw [hℓim, sub_self, abs_zero]; exact hrpos
  set V : Set ℂ := {z : ℂ | σ < z.re} with hV
  have hVopen : IsOpen V := isOpen_lt continuous_const Complex.continuous_re
  have hFdiff : DifferentiableOn ℂ (LSeries c) V := fun z hz => (hFd z hz).differentiableWithinAt
  have hℓV : ∀ t ∈ U, ℓ t ∈ V := by
    intro t ht
    show σ < (ℓ t).re
    rw [hℓre]; linarith [ht.1]
  have hF : AnalyticOnNhd ℝ (fun t : ℝ => LSeries c (ℓ t)) U := fun t ht =>
    ((hFdiff.analyticAt (hVopen.mem_nhds (hℓV t ht))).restrictScalars).comp (hℓan t)
  have hG : AnalyticOnNhd ℝ (fun t : ℝ => primeOnlyG M (ℓ t)) U := fun t ht =>
    ((hGd.analyticAt (hU₀open.mem_nhds (hℓU₀ t ht))).restrictScalars).comp (hℓan t)
  have hUconn : IsPreconnected U := isPreconnected_Ioo
  have h18U : (1 / 8 : ℝ) ∈ U := ⟨by norm_num, by norm_num⟩
  have hagree : ∀ s : ℂ, Θ - 1 / 2 < s.re → LSeries c s = primeOnlyG M s := fun s hs =>
    LSeries_primeOnlyCoeff_eq hθ hΘ12.le hs
  have hfg : (fun t : ℝ => LSeries c (ℓ t)) =ᶠ[𝓝 (1 / 8 : ℝ)]
      (fun t : ℝ => primeOnlyG M (ℓ t)) := by
    refine Filter.eventuallyEq_of_mem
      (Ioo_mem_nhds (by linarith : η / 8 < 1 / 8) (by norm_num : (1 / 8 : ℝ) < 1 / 4))
      fun t ht => ?_
    apply hagree
    rw [hℓre]
    linarith [ht.1]
  have heq := hF.eqOn_of_preconnected_of_eventuallyEq hG hUconn h18U hfg
  have hp₀σ : σ < p₀.re := by rw [hp₀]; simp; linarith
  have hFcont : ContinuousAt (LSeries c) p₀ := (hFd p₀ hp₀σ).continuousAt
  have hℓ0 : Tendsto ℓ (𝓝 0) (𝓝 p₀) := by
    have : Tendsto (fun t : ℝ => p₀ + (t : ℂ)) (𝓝 0) (𝓝 (p₀ + ((0 : ℝ) : ℂ))) :=
      tendsto_const_nhds.add (Complex.continuous_ofReal.tendsto 0)
    rwa [Complex.ofReal_zero, add_zero] at this
  have hcomp : Tendsto (fun t : ℝ => LSeries c (ℓ t)) (𝓝 0) (𝓝 (LSeries c p₀)) :=
    hFcont.tendsto.comp hℓ0
  obtain ⟨δ, hδ, hδF⟩ := Metric.eventually_nhds_iff.mp
    (Metric.tendsto_nhds.mp hcomp 1 one_pos)
  obtain ⟨C', hC0, h3⟩ : ∃ C' : ℝ, 0 ≤ C' ∧ C + BT ≤ C' :=
    ⟨max (C + BT) 0, le_max_right _ _, le_max_left _ _⟩
  obtain ⟨Bd, hBd⟩ : ∃ Bd : ℝ, Bd = ‖LSeries c p₀‖ + 1 := ⟨_, rfl⟩
  have hw : 0 < ‖aliasedWeight q₀‖ := norm_aliasedWeight_pos q₀
  have hBpos : 0 < Bd + C' + 1 := by rw [hBd]; positivity
  obtain ⟨t₀, ht₀pos, ht₀δ, ht₀t₁, ht₀4, h2⟩ :=
    exists_small_ray_parameter hδ (one_pos : (0 : ℝ) < 1) hw hBpos
  have ht₀U : t₀ ∈ U := ⟨ht₀pos, ht₀4⟩
  have hFb : ‖LSeries c (ℓ t₀)‖ ≤ Bd := by
    have hd : dist t₀ 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos ht₀pos]; exact ht₀δ
    have := hδF hd
    rw [dist_eq_norm] at this
    calc ‖LSeries c (ℓ t₀)‖
        = ‖(LSeries c (ℓ t₀) - LSeries c p₀) + LSeries c p₀‖ := by congr 1; ring
      _ ≤ ‖LSeries c (ℓ t₀) - LSeries c p₀‖ + ‖LSeries c p₀‖ := norm_add_le _ _
      _ ≤ 1 + ‖LSeries c p₀‖ := by linarith
      _ = Bd := by rw [hBd]; ring
  have hGb : Bd < ‖primeOnlyG M (ℓ t₀)‖ := by
    have h1 := hC' t₀ ht₀pos ht₀4.le
    rw [← hℓeq] at h1
    -- `‖W₀‖/(2t₀) ≥ 2(Bd + C' + 1)` gives `‖W₀‖/t₀ ≥ 4(Bd + C' + 1)`
    have h4 : ‖aliasedWeight q₀‖ / t₀ = 2 * (‖aliasedWeight q₀‖ / (2 * t₀)) := by
      field_simp
    linarith
  have hEq : LSeries c (ℓ t₀) = primeOnlyG M (ℓ t₀) := heq ht₀U
  rw [hEq] at hFb
  linarith

/-- **RH ⟺ the lag sequence is bounded above on the primes.** -/
theorem riemannHypothesis_iff_primeLag_bddAbove :
    RiemannHypothesis ↔ ∃ M : ℝ, ∀ p : ℕ, p.Prime → integerLag p ≤ M := by
  constructor
  · intro h
    exact ⟨poleSharpConstant, fun p _ =>
      (abs_le.mp (abs_integerLag_le_of_riemannHypothesis h p)).2⟩
  · rintro ⟨M, hM⟩
    exact riemannHypothesis_of_primeLag_le hM

/-- **The sharp prime criterion.**  RH holds iff `Φ(log p) ≤ 2 + γ − log 4π` for every prime `p`. -/
theorem riemannHypothesis_iff_primeLag_le_sharp :
    RiemannHypothesis ↔ ∀ p : ℕ, p.Prime → integerLag p ≤ poleSharpConstant := by
  constructor
  · intro h p _
    exact (abs_le.mp (abs_integerLag_le_of_riemannHypothesis h p)).2
  · intro hM
    exact riemannHypothesis_of_primeLag_le hM

end

end RHTower
