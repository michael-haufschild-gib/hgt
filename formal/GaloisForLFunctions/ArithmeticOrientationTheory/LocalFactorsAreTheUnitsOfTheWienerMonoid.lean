import GaloisForLFunctions.ArithmeticOrientationTheory.TheCriticalWienerMonoid

/-!
# Local factors are the units of the Wiener monoid

A **local factor** at the prime `p` is the two-point kernel `δ₁ − a δ_p` (`localFactorKernel`).
Its Dirichlet inverse is the geometric tower `Σ_k a^k δ_{p^k}` (`localFactorInverse`,
`dirichletConv_localFactor_inverse`), and the tower is critical Wiener exactly when
`|a| < √p` (`criticalWiener_localFactorInverse_iff`).

* **Commutativity and uniqueness** (`dirichletConv_comm`, `inverse_unique`): Dirichlet
  convolution is commutative, so inverses in the monoid are unique away from `0`.
* **The unit law** (`isWienerUnit_localFactor_iff`): `δ₁ − a δ_p` is a unit of the critical Wiener
  monoid iff `|a| < √p`.

This is the orientation-theoretic form of the local factor law of Trans-Horizon Incidence
Mechanics (local factors with `|a| < √p` preserve the receiver class): they preserve it because
they are invertible in the stability monoid, and the threshold `√p` is where the inverse tower
leaves the critical Wiener class, i.e. where the Euler factor `1 − a p^{−s}` acquires a zero on
`Re s = ½`.
-/

open Finset

namespace GaloisForLFunctions.ArithmeticOrientationTheory

open TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Local factors and their inverse towers -/

/-- The local factor `δ₁ − a δ_p`. -/
def localFactorKernel (p : ℕ) (a : ℝ) : ℕ → ℝ := fun n => if n = 1 then 1 else if n = p then -a else 0

/-- The inverse tower `Σ_k a^k δ_{p^k}`, read through `Nat.log`. -/
def localFactorInverse (p : ℕ) (a : ℝ) : ℕ → ℝ :=
  fun n => if p ^ Nat.log p n = n then a ^ Nat.log p n else 0

theorem localFactorInverse_pow {p : ℕ} (hp : 1 < p) (a : ℝ) (k : ℕ) :
    localFactorInverse p a (p ^ k) = a ^ k := by
  simp [localFactorInverse, Nat.log_pow hp]

theorem localFactorInverse_eq_zero {p : ℕ} (a : ℝ) {n : ℕ} (h : ∀ k, n ≠ p ^ k) :
    localFactorInverse p a n = 0 := by
  unfold localFactorInverse
  rw [if_neg]
  intro h'
  exact h _ h'.symm

/-- Convolution with a two-point kernel. -/
theorem dirichletConv_localFactorKernel {p : ℕ} (hp : p.Prime) (a : ℝ) (g : ℕ → ℝ) {n : ℕ}
    (hn : n ≠ 0) :
    RHTower.dirichletConv (localFactorKernel p a) g n =
      g n - a * (if p ∣ n then g (n / p) else 0) := by
  unfold RHTower.dirichletConv
  have hterm : ∀ d ∈ n.divisors, localFactorKernel p a d * g (n / d) =
      (if d = 1 then g n else 0) + (if d = p then -a * g (n / p) else 0) := by
    intro d _
    unfold localFactorKernel
    by_cases h1 : d = 1
    · subst h1
      have : (1 : ℕ) ≠ p := hp.one_lt.ne
      simp [this]
    · by_cases h2 : d = p
      · subst h2; simp [h1]
      · simp [h1, h2]
  rw [sum_congr rfl hterm, sum_add_distrib, sum_ite_eq', sum_ite_eq']
  rw [if_pos (Nat.one_mem_divisors.2 hn)]
  by_cases hpn : p ∣ n
  · rw [if_pos (Nat.mem_divisors.2 ⟨hpn, hn⟩), if_pos hpn]; ring
  · rw [if_neg (fun h => hpn (Nat.mem_divisors.1 h).1), if_neg hpn]; ring

/-- **The inverse tower inverts the local factor** away from `0`. -/
theorem dirichletConv_localFactor_inverse {p : ℕ} (hp : p.Prime) (a : ℝ) {n : ℕ} (hn : n ≠ 0) :
    RHTower.dirichletConv (localFactorKernel p a) (localFactorInverse p a) n = unitKernel n := by
  rw [dirichletConv_localFactorKernel hp a _ hn]
  by_cases hpow : ∃ m, n = p ^ m
  · obtain ⟨m, rfl⟩ := hpow
    rcases m with _ | k
    · have h1 : localFactorInverse p a 1 = 1 := by
        simpa using localFactorInverse_pow hp.one_lt a 0
      rw [pow_zero, if_neg hp.not_dvd_one, h1, mul_zero, sub_zero]
      simp [unitKernel]
    · have hdvd : p ∣ p ^ (k + 1) := dvd_pow_self p (Nat.succ_ne_zero k)
      have hdiv : p ^ (k + 1) / p = p ^ k := by
        rw [pow_succ, Nat.mul_div_cancel _ hp.pos]
      have hne1 : p ^ (k + 1) ≠ 1 := (one_lt_pow' hp.one_lt (Nat.succ_ne_zero k)).ne'
      rw [if_pos hdvd, hdiv, localFactorInverse_pow hp.one_lt, localFactorInverse_pow hp.one_lt]
      have hu : unitKernel (p ^ (k + 1)) = 0 := by unfold unitKernel; rw [if_neg hne1]
      rw [hu, pow_succ]
      ring
  · have hnot : ∀ k, n ≠ p ^ k := fun k h => hpow ⟨k, h⟩
    have hne1 : n ≠ 1 := fun h => hnot 0 (by rw [h, pow_zero])
    rw [localFactorInverse_eq_zero a hnot]
    simp only [unitKernel, hne1, if_false, zero_sub, neg_eq_zero, mul_eq_zero]
    right
    split_ifs with hpn
    · obtain ⟨q, rfl⟩ := hpn
      rw [Nat.mul_div_cancel_left q hp.pos]
      refine localFactorInverse_eq_zero a fun k h => hnot (k + 1) ?_
      rw [h, pow_succ, mul_comm]
    · rfl

/-! ### The critical Wiener threshold `|a| < √p` -/

/-- The weighted tower term `|a|^k (p^k)^{−1/2}` is the geometric term `(|a| p^{−1/2})^k`. -/
theorem abs_localFactorInverse_mul_rpow {p : ℕ} (hp : p.Prime) (a : ℝ) (k : ℕ) :
    |localFactorInverse p a (p ^ k)| * ((p ^ k : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) =
      (|a| * (p : ℝ) ^ (-(1 / 2 : ℝ))) ^ k := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  rw [localFactorInverse_pow hp.one_lt, abs_pow, mul_pow, Nat.cast_pow]
  congr 1
  rw [← Real.rpow_natCast (p : ℝ) k, ← Real.rpow_mul hp0.le, mul_comm, Real.rpow_mul hp0.le,
    Real.rpow_natCast]

theorem eq_zero_of_not_mem_range_pow (p : ℕ) (a : ℝ) {n : ℕ}
    (hr : n ∉ Set.range (fun k : ℕ => p ^ k)) :
    |localFactorInverse p a n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) = 0 := by
  have hnot : ∀ k, n ≠ p ^ k := fun k h => hr ⟨k, h.symm⟩
  rw [localFactorInverse_eq_zero a hnot, abs_zero, zero_mul]

/-- **The inverse tower is critical Wiener iff `|a| < √p`.** -/
theorem criticalWiener_localFactorInverse_iff {p : ℕ} (hp : p.Prime) (a : ℝ) :
    CriticalWiener (localFactorInverse p a) ↔ |a| < Real.sqrt p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  unfold CriticalWiener
  rw [← (Nat.pow_right_injective hp.two_le).summable_iff
    (fun n hn => eq_zero_of_not_mem_range_pow p a hn)]
  have hcomp : ((fun n : ℕ => |localFactorInverse p a n| * (n : ℝ) ^ (-(1 / 2 : ℝ))) ∘
      fun k : ℕ => p ^ k) = fun k => (|a| * (p : ℝ) ^ (-(1 / 2 : ℝ))) ^ k := by
    funext k
    exact abs_localFactorInverse_mul_rpow hp a k
  rw [hcomp, summable_geometric_iff_norm_lt_one, Real.norm_eq_abs,
    abs_of_nonneg (by positivity), Real.rpow_neg hp0.le, ← Real.sqrt_eq_rpow,
    mul_inv_lt_iff₀ (Real.sqrt_pos.2 hp0), one_mul]

/-! ### Commutativity, uniqueness, and the unit law -/

/-- Dirichlet convolution is commutative. -/
theorem dirichletConv_comm (a b : ℕ → ℝ) :
    RHTower.dirichletConv a b = RHTower.dirichletConv b a := by
  rw [dirichletConv_eq_toArithmeticFunction, dirichletConv_eq_toArithmeticFunction, mul_comm]

/-- Convolution only reads values at positive arguments. -/
theorem dirichletConv_congr {a a' b b' : ℕ → ℝ} (ha : ∀ n, n ≠ 0 → a n = a' n)
    (hb : ∀ n, n ≠ 0 → b n = b' n) (n : ℕ) :
    RHTower.dirichletConv a b n = RHTower.dirichletConv a' b' n := by
  unfold RHTower.dirichletConv
  refine sum_congr rfl fun d hd => ?_
  have hd0 : d ≠ 0 := (Nat.pos_of_mem_divisors hd).ne'
  have hnd : n / d ≠ 0 := (Nat.div_pos (Nat.divisor_le hd) (Nat.pos_of_mem_divisors hd)).ne'
  rw [ha d hd0, hb (n / d) hnd]

/-- **Inverses are unique** away from `0`. -/
theorem inverse_unique {k g h : ℕ → ℝ}
    (hg : ∀ n, n ≠ 0 → RHTower.dirichletConv k g n = unitKernel n)
    (hh : ∀ n, n ≠ 0 → RHTower.dirichletConv k h n = unitKernel n) {n : ℕ} (hn : n ≠ 0) :
    g n = h n := by
  calc g n = RHTower.dirichletConv unitKernel g n := (dirichletConv_unitKernel g hn).symm
    _ = RHTower.dirichletConv (RHTower.dirichletConv k h) g n :=
        dirichletConv_congr (fun m hm => (hh m hm).symm) (fun _ _ => rfl) n
    _ = RHTower.dirichletConv h (RHTower.dirichletConv k g) n := by
        rw [dirichletConv_comm k h, dirichletConv_assoc]
    _ = RHTower.dirichletConv h unitKernel n :=
        dirichletConv_congr (fun _ _ => rfl) hg n
    _ = h n := by rw [dirichletConv_comm]; exact dirichletConv_unitKernel h hn

/-- The critical Wiener property only reads values at positive arguments. -/
theorem criticalWiener_congr {a b : ℕ → ℝ} (h : ∀ n, n ≠ 0 → a n = b n) :
    CriticalWiener a ↔ CriticalWiener b := by
  unfold CriticalWiener
  have : (fun n : ℕ => |a n| * (n : ℝ) ^ (-(1 / 2 : ℝ))) =
      fun n => |b n| * (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · rw [h n hn]
  rw [this]

theorem criticalWiener_localFactorKernel (p : ℕ) (a : ℝ) : CriticalWiener (localFactorKernel p a) := by
  unfold CriticalWiener
  refine summable_of_ne_finset_zero (s := {1, p}) fun n hn => ?_
  simp only [mem_insert, mem_singleton, not_or] at hn
  simp [localFactorKernel, hn.1, hn.2]

/-- A unit of the critical Wiener monoid: a critical Wiener kernel with a critical Wiener inverse
away from `0`. -/
def IsWienerUnit (k : ℕ → ℝ) : Prop :=
  CriticalWiener k ∧ ∃ g : ℕ → ℝ, CriticalWiener g ∧
    ∀ n, n ≠ 0 → RHTower.dirichletConv k g n = unitKernel n

/-- **The unit law for local factors**: `δ₁ − a δ_p` is a unit of the critical Wiener monoid iff
`|a| < √p`. -/
theorem isWienerUnit_localFactor_iff {p : ℕ} (hp : p.Prime) (a : ℝ) :
    IsWienerUnit (localFactorKernel p a) ↔ |a| < Real.sqrt p := by
  constructor
  · rintro ⟨-, g, hg, hinv⟩
    rw [← criticalWiener_localFactorInverse_iff hp]
    exact (criticalWiener_congr fun n hn =>
      inverse_unique (fun m hm => dirichletConv_localFactor_inverse hp a hm) hinv hn).2 hg
  · intro h
    exact ⟨criticalWiener_localFactorKernel p a, localFactorInverse p a,
      (criticalWiener_localFactorInverse_iff hp a).2 h,
      fun n hn => dirichletConv_localFactor_inverse hp a hn⟩

end

end GaloisForLFunctions.ArithmeticOrientationTheory
