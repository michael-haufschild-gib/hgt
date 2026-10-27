import GaloisForLFunctions.ArithmeticElectrostatics.TheSelfIntersectionOfATorsionOrbit
import GaloisForLFunctions.RHTower.MertensFirst

/-!
# The torsion counterterm is logarithmic

Put a charge `y_n` on each point of the torsion orbit `O_n`, for the orders `1 ≤ n ≤ N`. With the
self-energies of the points removed, the interaction of the configuration is the **torsion
pairing** `Σ_{m,n} y_m y_n I(m, n)` (`torsionPairing`), where `I` is the archimedean intersection of
orbits; its logarithmic energy is minus this. Discrete charges have no sign once the diagonal is
removed: positivity needs a **counterterm**, a self-energy `κ` per point, and the renormalized
energy `κ Σ φ(n) y_n² − Σ y_m y_n I(m, n)` must be nonnegative (`RenormalizesAt N κ`). A constant
`κ` per point is compatible with every power map.

* **Upper bound** (`renormalizesAt_log`): `κ = 4 log N + 2(log 4 + 4)` renormalizes every
  configuration on orders `≤ N`. The diagonal costs `I(n, n) ≤ φ(n) log n`; off the diagonal a
  Schur test with weights `1/n` reduces the row sums to the Hecke law: up the tower the row is
  `φ(m) Σ_{t ≤ N/m} Λ(t)/t ≤ φ(m)(log N + log 4 + 4)` (Mertens), down the tower it is at most
  `2φ(m) log m` (super-multiplicativity of `φ`, and `t ≤ 2φ(t)` at prime powers).
* **Lower bound** (`le_of_renormalizesAt_prime`, `half_log_le_of_renormalizesAt`): the orbit of a
  prime `p ≤ N` alone has pairing `(p − 2) log p` against self-mass `p − 1`, so every renormalizing
  `κ` is at least `((p − 2)/(p − 1)) log p`; with Bertrand's postulate, at least `½ log(N/2)` for
  `N ≥ 4`.

So the minimal counterterm on orders `≤ N` lies between `½ log(N/2)` and `4 log N + O(1)`: no finite
renormalization of the diagonal keeps the torsion pairing positive uniformly in the order, and the
divergence is exactly logarithmic — the rate of the archimedean self-energy `log(1/ε)` of an atom of
width `ε ≍ 1/N`, the spacing of the atoms `log n`, `n ≤ N`.
-/

noncomputable section

open Finset
open scoped ArithmeticFunction.Moebius

namespace GaloisForLFunctions.ArithmeticElectrostatics

open ArithmeticFunction GaloisForLFunctions.ArithmeticEffectivityTheory

/-- The **torsion pairing** of charges `y_n` per point of `O_n`, orders `1 ≤ n ≤ N`. -/
def torsionPairing (N : ℕ) (y : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, y m * y n * orbitIntersection m n

/-- The **self-mass** `Σ φ(n) y_n²`: the number of points weighted by the squared charge. -/
def selfMass (N : ℕ) (y : ℕ → ℝ) : ℝ := ∑ n ∈ Icc 1 N, (Nat.totient n : ℝ) * y n ^ 2

/-- A counterterm `κ` per point **renormalizes** the orders `≤ N` when the renormalized energy
`κ · selfMass − torsionPairing` is nonnegative for every configuration. -/
def RenormalizesAt (N : ℕ) (κ : ℝ) : Prop := ∀ y : ℕ → ℝ, torsionPairing N y ≤ κ * selfMass N y

/-! ### Elementary facts about the intersection of orbits -/

theorem orbitIntersection_comm (m n : ℕ) : orbitIntersection m n = orbitIntersection n m := by
  rw [orbitIntersection, orbitIntersection, sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by rw [norm_sub_rev]

theorem orbitIntersection_nonneg_of_ne {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    0 ≤ orbitIntersection m n := by
  rw [orbitIntersection_eq hm hn hmn]
  split_ifs <;> first
    | exact mul_nonneg (Nat.cast_nonneg _) vonMangoldt_nonneg
    | exact le_rfl

/-- At a prime power `t ≤ 2 φ(t)`. -/
theorem le_two_mul_totient_of_isPrimePow {t : ℕ} (ht : IsPrimePow t) :
    (t : ℝ) ≤ 2 * Nat.totient t := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff t).mp ht
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [Nat.totient_prime_pow_succ hp, pow_succ]
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  push_cast [Nat.cast_sub hp.one_le]
  have hpj : (0 : ℝ) ≤ (p : ℝ) ^ j := by positivity
  nlinarith

/-- Down the tower: `φ(n) · (m/n) · Λ(m/n) ≤ 2 φ(m) Λ(m/n)` for `n ∣ m`. -/
theorem totient_mul_quot_le {m n : ℕ} (hnm : n ∣ m) :
    (Nat.totient n : ℝ) * ((m / n : ℕ) : ℝ) * Λ (m / n) ≤ 2 * Nat.totient m * Λ (m / n) := by
  by_cases hΛ : Λ (m / n) = 0
  · rw [hΛ]; simp
  have hpp : IsPrimePow (m / n) := by
    by_contra h; exact hΛ (vonMangoldt_eq_zero_iff.mpr h)
  have h1 := le_two_mul_totient_of_isPrimePow hpp
  have h2 : (Nat.totient n : ℝ) * Nat.totient (m / n) ≤ Nat.totient m := by
    have := Nat.totient_super_multiplicative n (m / n)
    rw [Nat.mul_div_cancel' hnm] at this
    exact_mod_cast this
  have hΛ0 : 0 ≤ Λ (m / n) := vonMangoldt_nonneg
  have hφn : (0 : ℝ) ≤ Nat.totient n := Nat.cast_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left h1 hφn]

/-! ### The row sums -/

/-- Multiples of `m` in `[1, N]` are the images `m t`, `t ∈ [1, N/m]`. -/
theorem filter_dvd_Icc_eq_image {m N : ℕ} (hm : 0 < m) :
    (Icc 1 N).filter (fun n => m ∣ n) = (Icc 1 (N / m)).image (fun t => m * t) := by
  ext n
  simp only [mem_filter, mem_Icc, mem_image]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨t, rfl⟩⟩
    refine ⟨t, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos t with rfl | ht
      · omega
      · exact ht
    · rw [Nat.le_div_iff_mul_le hm]; linarith [mul_comm m t]
  · rintro ⟨t, ⟨h1, h2⟩, rfl⟩
    refine ⟨⟨by nlinarith, ?_⟩, dvd_mul_right m t⟩
    rw [Nat.le_div_iff_mul_le hm] at h2; linarith [mul_comm m t]

/-- Divisors of `m ≤ N` are the elements of `[1, N]` dividing `m`. -/
theorem filter_Icc_dvd_eq_divisors {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    (Icc 1 N).filter (fun n => n ∣ m) = m.divisors := by
  ext n
  simp only [mem_filter, mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨-, h⟩; exact ⟨h, hm.ne'⟩
  · rintro ⟨h, -⟩
    have hn := Nat.pos_of_dvd_of_pos h hm
    exact ⟨⟨hn, (Nat.le_of_dvd hm h).trans hmN⟩, h⟩

/-- The pointwise Schur bound off the diagonal. -/
theorem orbitIntersection_mul_ratio_le {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hmn : m ≠ n) :
    orbitIntersection m n * ((m : ℝ) / n) ≤
      (if m ∣ n then (Nat.totient m : ℝ) * Λ (n / m) * ((m : ℝ) / n) else 0) +
        (if n ∣ m then 2 * Nat.totient m * Λ (m / n) else 0) := by
  have hratio : (0 : ℝ) ≤ (m : ℝ) / n := by positivity
  rw [orbitIntersection_eq hm hn hmn]
  by_cases hnm : n ∣ m
  · have hmn' : ¬ m ∣ n := fun h => hmn (Nat.dvd_antisymm h hnm)
    rw [if_pos hnm, if_neg hmn', if_pos hnm, zero_add]
    have hcast : (m : ℝ) / n = ((m / n : ℕ) : ℝ) := by
      rw [Nat.cast_div hnm (by exact_mod_cast hn.ne')]
    rw [hcast]
    have := totient_mul_quot_le hnm
    linarith
  · rw [if_neg hnm, if_neg hnm, add_zero]
    split_ifs
    · exact le_rfl
    · simp

/-- **The row bound**: `Σ_{n ≤ N, n ≠ m} I(m, n) m/n ≤ φ(m)(3 log N + log 4 + 4)`. -/
theorem sum_offDiag_row_le {m N : ℕ} (hm : 0 < m) (hmN : m ≤ N) :
    ∑ n ∈ (Icc 1 N).erase m, orbitIntersection m n * ((m : ℝ) / n) ≤
      (Nat.totient m : ℝ) * (3 * Real.log N + (Real.log 4 + 4)) := by
  have hφ : (0 : ℝ) ≤ Nat.totient m := Nat.cast_nonneg _
  have hN : 0 < N := lt_of_lt_of_le hm hmN
  -- the two Hecke directions
  have hup : ∑ n ∈ Icc 1 N, (if m ∣ n then (Nat.totient m : ℝ) * Λ (n / m) * ((m : ℝ) / n)
      else 0) ≤ (Nat.totient m : ℝ) * (Real.log N + (Real.log 4 + 4)) := by
    rw [← sum_filter, filter_dvd_Icc_eq_image hm,
      sum_image fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hm h]
    have hterm : ∀ t ∈ Icc 1 (N / m), (Nat.totient m : ℝ) * Λ (m * t / m) * ((m : ℝ) / (m * t : ℕ)) =
        (Nat.totient m : ℝ) * (Λ t / t) := by
      intro t ht
      have ht0 : (t : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by have := (mem_Icc.mp ht).1; omega)
      have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
      rw [Nat.mul_div_cancel_left t hm, Nat.cast_mul]
      field_simp
    rw [sum_congr rfl hterm, ← mul_sum]
    refine mul_le_mul_of_nonneg_left ?_ hφ
    have hNm : 1 ≤ N / m := (Nat.le_div_iff_mul_le hm).mpr (by linarith)
    have hmert := RHTower.Mertens.mertens_first (N / m) hNm
    have hlog : Real.log ((N / m : ℕ) : ℝ) ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast hNm) (by exact_mod_cast Nat.div_le_self N m)
    have := (abs_le.mp hmert).2
    linarith
  have hdown : ∑ n ∈ Icc 1 N, (if n ∣ m then 2 * (Nat.totient m : ℝ) * Λ (m / n) else 0) ≤
      (Nat.totient m : ℝ) * (2 * Real.log N) := by
    rw [← sum_filter, filter_Icc_dvd_eq_divisors hm hmN, ← mul_sum,
      Nat.sum_div_divisors m (fun d => Λ d), vonMangoldt_sum]
    have hlog : Real.log m ≤ Real.log N :=
      Real.log_le_log (by exact_mod_cast hm) (by exact_mod_cast hmN)
    nlinarith
  calc ∑ n ∈ (Icc 1 N).erase m, orbitIntersection m n * ((m : ℝ) / n)
      ≤ ∑ n ∈ (Icc 1 N).erase m,
          ((if m ∣ n then (Nat.totient m : ℝ) * Λ (n / m) * ((m : ℝ) / n) else 0) +
            (if n ∣ m then 2 * Nat.totient m * Λ (m / n) else 0)) :=
        sum_le_sum fun n hn => orbitIntersection_mul_ratio_le hm
          (mem_Icc.mp (mem_of_mem_erase hn)).1 (ne_of_mem_erase hn).symm
    _ ≤ ∑ n ∈ Icc 1 N,
          ((if m ∣ n then (Nat.totient m : ℝ) * Λ (n / m) * ((m : ℝ) / n) else 0) +
            (if n ∣ m then 2 * Nat.totient m * Λ (m / n) else 0)) := by
        refine sum_le_sum_of_subset_of_nonneg (erase_subset _ _) fun n _ _ => ?_
        refine add_nonneg ?_ ?_ <;> split_ifs <;> positivity
    _ = _ + _ := sum_add_distrib
    _ ≤ (Nat.totient m : ℝ) * (Real.log N + (Real.log 4 + 4)) +
          (Nat.totient m : ℝ) * (2 * Real.log N) := add_le_add hup hdown
    _ = (Nat.totient m : ℝ) * (3 * Real.log N + (Real.log 4 + 4)) := by ring

/-! ### The upper bound -/

/-- Sums over ordered pairs of distinct elements of a finite set are invariant under swapping. -/
theorem sum_sum_erase_comm (S : Finset ℕ) (G : ℕ → ℕ → ℝ) :
    ∑ m ∈ S, ∑ n ∈ S.erase m, G n m = ∑ m ∈ S, ∑ n ∈ S.erase m, G m n := by
  have e : ∀ H : ℕ → ℕ → ℝ,
      ∑ m ∈ S, ∑ n ∈ S.erase m, H m n = ∑ m ∈ S, ∑ n ∈ S, H m n - ∑ m ∈ S, H m m := by
    intro H
    rw [← sum_sub_distrib]
    exact sum_congr rfl fun m hm => sum_erase_eq_sub hm
  rw [e (fun m n => G n m), e G, sum_comm]

/-- **Upper bound**: `κ = 4 log N + (log 4 + 4)` renormalizes the orders `≤ N`. -/
theorem renormalizesAt_log (N : ℕ) :
    RenormalizesAt N (4 * Real.log N + (Real.log 4 + 4)) := by
  intro y
  set S := Icc 1 N
  have hpos : ∀ n ∈ S, 0 < n := fun n hn => (mem_Icc.mp hn).1
  -- split off the diagonal
  have hsplit : torsionPairing N y =
      ∑ m ∈ S, y m ^ 2 * orbitIntersection m m +
        ∑ m ∈ S, ∑ n ∈ S.erase m, y m * y n * orbitIntersection m n := by
    rw [torsionPairing, ← sum_add_distrib]
    refine sum_congr rfl fun m hm => ?_
    rw [← add_sum_erase S _ hm, sq]
  -- the diagonal
  have hdiag : ∑ m ∈ S, y m ^ 2 * orbitIntersection m m ≤
      ∑ m ∈ S, y m ^ 2 * ((Nat.totient m : ℝ) * Real.log N) := by
    refine sum_le_sum fun m hm => mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
    refine (orbitIntersection_self_le (hpos m hm)).trans (mul_le_mul_of_nonneg_left ?_
      (Nat.cast_nonneg _))
    exact Real.log_le_log (by exact_mod_cast hpos m hm) (by exact_mod_cast (mem_Icc.mp hm).2)
  -- off the diagonal: Schur with weights `1/n`
  have hpair : ∀ m ∈ S, ∀ n ∈ S.erase m, y m * y n * orbitIntersection m n ≤
      (y m ^ 2 * (orbitIntersection m n * ((m : ℝ) / n)) +
        y n ^ 2 * (orbitIntersection n m * ((n : ℝ) / m))) / 2 := by
    intro m hm n hn
    have hm0 : (0 : ℝ) < m := by exact_mod_cast hpos m hm
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hpos n (mem_of_mem_erase hn)
    have hI : 0 ≤ orbitIntersection m n := orbitIntersection_nonneg_of_ne (hpos m hm)
      (hpos n (mem_of_mem_erase hn)) (ne_of_mem_erase hn).symm
    rw [orbitIntersection_comm n m]
    have hamgm : 2 * (y m * y n) ≤ y m ^ 2 * ((m : ℝ) / n) + y n ^ 2 * ((n : ℝ) / m) := by
      have key : y m ^ 2 * ((m : ℝ) / n) + y n ^ 2 * ((n : ℝ) / m) - 2 * (y m * y n) =
          (y m * m - y n * n) ^ 2 / (m * n) := by
        field_simp
        ring
      have : 0 ≤ (y m * m - y n * n) ^ 2 / (m * n) := by positivity
      linarith
    nlinarith
  have hoff : ∑ m ∈ S, ∑ n ∈ S.erase m, y m * y n * orbitIntersection m n ≤
      ∑ m ∈ S, y m ^ 2 * ∑ n ∈ S.erase m, orbitIntersection m n * ((m : ℝ) / n) := by
    have hsym : ∑ m ∈ S, ∑ n ∈ S.erase m, y n ^ 2 * (orbitIntersection n m * ((n : ℝ) / m)) =
        ∑ m ∈ S, ∑ n ∈ S.erase m, y m ^ 2 * (orbitIntersection m n * ((m : ℝ) / n)) :=
      sum_sum_erase_comm S fun a b => y a ^ 2 * (orbitIntersection a b * ((a : ℝ) / b))
    calc ∑ m ∈ S, ∑ n ∈ S.erase m, y m * y n * orbitIntersection m n
        ≤ ∑ m ∈ S, ∑ n ∈ S.erase m, (y m ^ 2 * (orbitIntersection m n * ((m : ℝ) / n)) +
            y n ^ 2 * (orbitIntersection n m * ((n : ℝ) / m))) / 2 :=
          sum_le_sum fun m hm => sum_le_sum fun n hn => hpair m hm n hn
      _ = ∑ m ∈ S, y m ^ 2 * ∑ n ∈ S.erase m, orbitIntersection m n * ((m : ℝ) / n) := by
          simp only [← sum_div, sum_add_distrib, hsym, mul_sum]
          ring
  have hrow : ∑ m ∈ S, y m ^ 2 * ∑ n ∈ S.erase m, orbitIntersection m n * ((m : ℝ) / n) ≤
      ∑ m ∈ S, y m ^ 2 * ((Nat.totient m : ℝ) * (3 * Real.log N + (Real.log 4 + 4))) :=
    sum_le_sum fun m hm => mul_le_mul_of_nonneg_left
      (sum_offDiag_row_le (hpos m hm) (mem_Icc.mp hm).2) (sq_nonneg _)
  rw [hsplit, selfMass, mul_sum]
  calc _ ≤ ∑ m ∈ S, y m ^ 2 * ((Nat.totient m : ℝ) * Real.log N) +
        ∑ m ∈ S, y m ^ 2 * ((Nat.totient m : ℝ) * (3 * Real.log N + (Real.log 4 + 4))) :=
        add_le_add hdiag (hoff.trans hrow)
    _ = _ := by rw [← sum_add_distrib]; exact sum_congr rfl fun m _ => by ring

/-! ### The lower bound -/

/-- The orbit of a prime `p` alone: pairing `(p − 2) log p`, self-mass `p − 1`. -/
theorem le_of_renormalizesAt_prime {N : ℕ} {κ : ℝ} (h : RenormalizesAt N κ) {p : ℕ}
    (hp : p.Prime) (hpN : p ≤ N) : ((p : ℝ) - 2) * Real.log p ≤ κ * ((p : ℝ) - 1) := by
  have hmem : p ∈ Icc 1 N := mem_Icc.mpr ⟨hp.one_le, hpN⟩
  set y : ℕ → ℝ := fun n => if n = p then 1 else 0
  have hpair : torsionPairing N y = orbitIntersection p p := by
    rw [torsionPairing, sum_eq_single_of_mem p hmem fun m _ hm => by simp [y, hm],
      sum_eq_single_of_mem p hmem fun n _ hn => by simp [y, hn]]
    simp [y]
  have hmass : selfMass N y = (p : ℝ) - 1 := by
    rw [selfMass, sum_eq_single_of_mem p hmem fun n _ hn => by simp [y, hn]]
    simp [y, Nat.totient_prime hp, Nat.cast_sub hp.one_le]
  have hI : orbitIntersection p p = ((p : ℝ) - 2) * Real.log p := by
    have := orbitIntersection_self_prime_pow hp 0
    simp only [zero_add, pow_one, pow_zero, one_mul, Nat.cast_zero] at this
    rw [this, Nat.totient_prime hp, Nat.cast_sub hp.one_le]
    push_cast; ring
  have := h y
  rwa [hpair, hmass, hI] at this

/-- **Lower bound**: for `N ≥ 4` every renormalizing counterterm is at least `½ log(N/2)`. -/
theorem half_log_le_of_renormalizesAt {N : ℕ} (hN : 4 ≤ N) {κ : ℝ} (h : RenormalizesAt N κ) :
    Real.log ((N : ℝ) / 2) / 2 ≤ κ := by
  obtain ⟨p, hp, hlt, hle⟩ := Nat.exists_prime_lt_and_le_two_mul (N / 2) (by omega)
  have hpN : p ≤ N := hle.trans (Nat.mul_div_le N 2)
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by omega)
  have hkey := le_of_renormalizesAt_prime h hp hpN
  -- `log p ≥ log(N/2)` since `p > N/2`
  have hp2 : (N : ℝ) / 2 < p := by
    have h1 : N < 2 * (N / 2 + 1) := by omega
    have h2 : N / 2 + 1 ≤ p := hlt
    have : (N : ℝ) < 2 * p := by exact_mod_cast (show N < 2 * p by omega)
    linarith
  have hN2 : (0 : ℝ) < (N : ℝ) / 2 := by
    have : (4 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  have hlog : Real.log ((N : ℝ) / 2) ≤ Real.log p := Real.log_le_log hN2 hp2.le
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hlogN : 0 ≤ Real.log ((N : ℝ) / 2) := Real.log_nonneg (by
    have : (4 : ℝ) ≤ N := by exact_mod_cast hN
    linarith)
  -- `((p − 2)/(p − 1)) log p ≥ ½ log p` for `p ≥ 3`
  by_contra hκ
  push Not at hκ
  have hκ' : κ * ((p : ℝ) - 1) < Real.log ((N : ℝ) / 2) / 2 * ((p : ℝ) - 1) :=
    mul_lt_mul_of_pos_right hκ (by linarith)
  nlinarith

/-- **The counterterm rate**: the minimal renormalizing counterterm on orders `≤ N` lies between
`½ log(N/2)` and `4 log N + log 4 + 4`. -/
theorem torsionCounterterm_rate :
    (∀ N : ℕ, RenormalizesAt N (4 * Real.log N + (Real.log 4 + 4))) ∧
      ∀ N : ℕ, 4 ≤ N → ∀ κ : ℝ, RenormalizesAt N κ → Real.log ((N : ℝ) / 2) / 2 ≤ κ :=
  ⟨renormalizesAt_log, fun _ hN _ h => half_log_le_of_renormalizesAt hN h⟩

end GaloisForLFunctions.ArithmeticElectrostatics
