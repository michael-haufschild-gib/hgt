import GaloisForLFunctions.TransHorizonIncidenceMechanics.EvenFlipPairsOverTheOddSquarefreeWeightAreClassifiedAtThePole

/-!
# Finite perturbations of the coprime weights are decided at the pole

For a modulus `q ≥ 1` let `u_q(d) = 1_{(d,q)=1} d^{-ε}`: the principal character mod `q`, damped. It
has density `φ(q)/q` and its pole at `s = 1 − ε`. For every kernel `k` on `[1, J]` and `0 < ε ≤ 1/2`,
**the receiver of `k ⋆ u_q` is bounded if and only if `K(1 − ε) = Σ_j k(j) j^{-(1−ε)} = 0`.**

* Counting: every window of `q` consecutive integers holds exactly `φ(q)` integers prime to `q`, so
  `N_q(y) = #{m ≤ y : (m, q) = 1}` satisfies `|N_q(y) − y φ(q)/q| ≤ q`.
* Sufficiency: the partial sums of `k̃ ⋆ 1_{(·,q)=1}` are the floor sums `Σ_j k̃(j) N_q(⌊n/j⌋)`, within
  `q Σ|k̃|` of `(φ(q)/q) Σ_j k̃(j)⌊n/j⌋`, which is bounded once the mean `K(1 − ε)` vanishes.
* Necessity: the pole law of finite kernels with the drift of `u_q`.

So for every modulus the paid finite perturbations of the coprime weight form the same hyperplane
`K(1 − ε) = 0`: the local factors at the primes dividing `q` never move the pole.
-/

open Finset Filter Topology
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-- The indicator of the integers prime to `q`. -/
def coprimeIndicator (q n : ℕ) : ℝ := if Nat.Coprime n q then 1 else 0

theorem coprimeIndicator_nonneg (q n : ℕ) : 0 ≤ coprimeIndicator q n := by
  unfold coprimeIndicator; split_ifs <;> norm_num

theorem coprimeIndicator_le_one (q n : ℕ) : coprimeIndicator q n ≤ 1 := by
  unfold coprimeIndicator; split_ifs <;> norm_num

/-- Every window of `q` consecutive integers holds exactly `φ(q)` integers prime to `q`. -/
theorem sum_Ioc_coprimeIndicator_window (q m : ℕ) :
    ∑ x ∈ Ioc m (m + q), coprimeIndicator q x = q.totient := by
  have h := Nat.filter_coprime_Ico_eq_totient q (m + 1)
  have hIoc : Ioc m (m + q) = Ico (m + 1) (m + 1 + q) := by
    ext x; simp only [mem_Ioc, mem_Ico]; omega
  rw [hIoc, ← h]
  unfold coprimeIndicator
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]
  congr 2
  ext x
  simp only [mem_filter, Nat.coprime_comm]

/-- `N_q(y) = #{m ≤ y : (m, q) = 1}`. -/
def coprimeCount (q y : ℕ) : ℝ := ∑ x ∈ Icc 1 y, coprimeIndicator q x

theorem coprimeCount_add (q y : ℕ) : coprimeCount q (y + q) = coprimeCount q y + q.totient := by
  unfold coprimeCount
  have h : Icc 1 (y + q) = Icc 1 y ∪ Ioc y (y + q) := by
    ext x; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  rw [h, sum_union (by
    rw [disjoint_left]; intro x h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega),
    sum_Ioc_coprimeIndicator_window]

theorem coprimeCount_sub (q n m : ℕ) (hnm : n ≤ m) :
    coprimeCount q m - coprimeCount q n = ∑ x ∈ Ioc n m, coprimeIndicator q x := by
  unfold coprimeCount
  have h : Icc 1 m = Icc 1 n ∪ Ioc n m := by
    ext x; simp only [mem_union, mem_Icc, mem_Ioc]; omega
  rw [h, sum_union (by
    rw [disjoint_left]; intro x h1 h2; simp only [mem_Icc, mem_Ioc] at h1 h2; omega)]
  ring

/-- **The coprime count** `|N_q(y) − y φ(q)/q| ≤ q`. -/
theorem abs_coprimeCount_sub_le {q : ℕ} (hq : 0 < q) (y : ℕ) :
    |coprimeCount q y - y * ((q.totient : ℝ) / q)| ≤ q := by
  obtain ⟨t, r, hr, rfl⟩ : ∃ t r, r < q ∧ y = r + t * q :=
    ⟨y / q, y % q, Nat.mod_lt _ hq, (Nat.mod_add_div' y q).symm⟩
  have hcount : coprimeCount q (r + t * q) = coprimeCount q r + t * q.totient := by
    induction t with
    | zero => simp
    | succ t ih =>
      rw [show r + (t + 1) * q = (r + t * q) + q by ring, coprimeCount_add, ih]
      push_cast; ring
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hr_le : coprimeCount q r ≤ r := by
    unfold coprimeCount
    calc ∑ x ∈ Icc 1 r, coprimeIndicator q x ≤ ∑ x ∈ Icc 1 r, (1 : ℝ) :=
          sum_le_sum fun x _ => coprimeIndicator_le_one q x
      _ = r := by simp
  have hr0 : 0 ≤ coprimeCount q r := sum_nonneg fun x _ => coprimeIndicator_nonneg q x
  have hφ : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  rw [hcount]
  push_cast
  have hsplit : ((r : ℝ) + t * q) * ((q.totient : ℝ) / q) = r * ((q.totient : ℝ) / q) + t * q.totient := by
    field_simp
  rw [hsplit]
  have hrq : (r : ℝ) * ((q.totient : ℝ) / q) ≤ r := by
    rw [mul_div_assoc', div_le_iff₀ hq0]
    exact mul_le_mul_of_nonneg_left hφ (Nat.cast_nonneg r)
  have hrq0 : 0 ≤ (r : ℝ) * ((q.totient : ℝ) / q) := by positivity
  have hrlt : (r : ℝ) < q := by exact_mod_cast hr
  rw [abs_le]; constructor <;> linarith

/-- **At a zero of the pole value, `k̃ ⋆ 1_{(·,q)=1}` has bounded partial sums.** -/
theorem abs_sum_range_dirichletConv_coprime_le {q : ℕ} (hq : 0 < q) {k : ℕ → ℝ} {J : ℕ}
    (hkJ : ∀ j, J < j → k j = 0) {ε : ℝ} (hK : poleValue k J ε = 0) (x : ℕ) :
    |∑ d ∈ range x, RHTower.dirichletConv (undampedKernel k ε) (coprimeIndicator q) d| ≤
      (q + 1) * ∑ j ∈ Icc 1 J, |undampedKernel k ε j| := by
  set k' := undampedKernel k ε
  set L := ∑ j ∈ Icc 1 J, |k' j|
  have hL : 0 ≤ L := sum_nonneg fun j _ => abs_nonneg _
  have hk'J : ∀ j, J < j → k' j = 0 := undampedKernel_support hkJ ε
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  set ρ := (q.totient : ℝ) / q
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 := by
    rw [div_le_one hq0]; exact_mod_cast Nat.totient_le q
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simpa using mul_nonneg (by positivity : (0 : ℝ) ≤ q + 1) hL
  obtain ⟨n, rfl⟩ : ∃ n, x = n + 1 := ⟨x - 1, by omega⟩
  rw [dampedSign_sum_range_succ_eq_add_Icc]
  have h0 : RHTower.dirichletConv k' (coprimeIndicator q) 0 = 0 := by simp [RHTower.dirichletConv]
  rw [h0, zero_add]
  have hft := RHTower.floorTransform_comp k' (coprimeIndicator q) (fun _ => (1 : ℝ)) n
  simp only [RHTower.floorTransform, mul_one] at hft
  rw [← hft]
  have hsplit : ∑ j ∈ Icc 1 n, k' j * ∑ m ∈ Icc 1 (n / j), coprimeIndicator q m =
      ∑ j ∈ Icc 1 n, k' j * (coprimeCount q (n / j) - ((n / j : ℕ) : ℝ) * ρ) +
        ρ * ∑ j ∈ Icc 1 n, k' j * ((n / j : ℕ) : ℝ) := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun j _ => by unfold coprimeCount; ring
  have hmean := abs_weightCenteredPrefix_finiteKernel_le hk'J n
  rw [sum_undampedKernel_div, hK, weightCenteredPrefix, sum_Icc_sum_divisors_eq_floor,
    zero_mul, sub_zero] at hmean
  have hsub : ∑ j ∈ Icc 1 n, |k' j| ≤ L := by
    calc ∑ j ∈ Icc 1 n, |k' j| ≤ ∑ j ∈ Icc 1 (n + J), |k' j| :=
          sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc le_rfl (by omega))
            fun _ _ _ => abs_nonneg _
      _ = L := by
          refine (sum_subset (Icc_subset_Icc le_rfl (by omega)) fun j hj hjJ => ?_).symm
          have : J < j := by simp only [mem_Icc] at hj hjJ; omega
          rw [hk'J j this, abs_zero]
  have hfirst : |∑ j ∈ Icc 1 n, k' j * (coprimeCount q (n / j) - ((n / j : ℕ) : ℝ) * ρ)| ≤
      q * L := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ Icc 1 n, |k' j * (coprimeCount q (n / j) - ((n / j : ℕ) : ℝ) * ρ)|
        ≤ ∑ j ∈ Icc 1 n, |k' j| * q := sum_le_sum fun j _ => by
          rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (abs_coprimeCount_sub_le hq _) (abs_nonneg _)
      _ ≤ q * L := by rw [← sum_mul, mul_comm]; exact mul_le_mul_of_nonneg_left hsub hq0.le
  rw [hsplit]
  calc |∑ j ∈ Icc 1 n, k' j * (coprimeCount q (n / j) - ((n / j : ℕ) : ℝ) * ρ) +
        ρ * ∑ j ∈ Icc 1 n, k' j * ((n / j : ℕ) : ℝ)|
      ≤ q * L + 1 * L := by
        refine (abs_add_le _ _).trans (add_le_add hfirst ?_)
        rw [abs_mul, abs_of_nonneg hρ0]
        exact mul_le_mul hρ1 hmean (abs_nonneg _) zero_le_one
    _ = (q + 1) * L := by ring

/-- The coprime weight drifts: eventually `n Σ_{(n,2n]} u_q(d)/d ≥ (2q)^{-1} 2^{-1-ε} n^{1−ε}`. -/
theorem eventually_coprime_drift {q : ℕ} (hq : 0 < q) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, (2 * (q : ℝ))⁻¹ * (2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (1 - ε) ≤
      (n : ℝ) * ∑ d ∈ Ioc n (2 * n), dampedSignWeight (coprimeIndicator q) ε d / d := by
  filter_upwards [eventually_ge_atTop (4 * q ^ 2), eventually_ge_atTop 1] with n hn hn1
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hcount : (n : ℝ) / (2 * q) ≤ ∑ d ∈ Ioc n (2 * n), coprimeIndicator q d := by
    rw [← coprimeCount_sub q n (2 * n) (by omega)]
    have h1 := abs_coprimeCount_sub_le hq (2 * n)
    have h2 := abs_coprimeCount_sub_le hq n
    rw [abs_le] at h1 h2
    have hφ : (1 : ℝ) ≤ q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
    have hnq : (4 : ℝ) * q ^ 2 ≤ n := by exact_mod_cast hn
    have hρ : (n : ℝ) / q ≤ n * ((q.totient : ℝ) / q) := by
      rw [mul_div_assoc']; exact div_le_div_of_nonneg_right (by nlinarith) hq0.le
    have hkey : (n : ℝ) / (2 * q) + 2 * q ≤ n / q := by
      rw [div_add' _ _ _ (by positivity), div_le_div_iff₀ (by positivity) hq0]
      nlinarith
    push_cast at h1
    nlinarith
  set P := (2 * (n : ℝ)) ^ (-(1 + ε))
  have hP : 0 ≤ P := Real.rpow_nonneg (by positivity) _
  have hcell : ∀ d ∈ Ioc n (2 * n), coprimeIndicator q d * P ≤
      dampedSignWeight (coprimeIndicator q) ε d / d := fun d hd => by
    have hd := mem_Ioc.mp hd
    have hd0 : (0 : ℝ) < d := by exact_mod_cast (show 0 < d by omega)
    have hd2 : (d : ℝ) ≤ 2 * n := by exact_mod_cast hd.2
    rw [dampedSignWeight_div hε, mul_comm ((d : ℝ) ^ _)]
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hd0 hd2 (by linarith))
      (coprimeIndicator_nonneg q d)
  have hsum : P * ((n : ℝ) / (2 * q)) ≤ ∑ d ∈ Ioc n (2 * n), dampedSignWeight (coprimeIndicator q) ε d / d :=
    (mul_le_mul_of_nonneg_left hcount hP).trans (by
      rw [mul_sum]; exact sum_le_sum fun d hd => by rw [mul_comm]; exact hcell d hd)
  have hPn : P = (2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (-(1 + ε)) := Real.mul_rpow (by norm_num) hn0.le
  have hpow : (n : ℝ) * ((n : ℝ) ^ (-(1 + ε)) * n) = (n : ℝ) ^ (1 - ε) := by
    rw [show (1 - ε) = 1 + (-(1 + ε) + 1) by ring, Real.rpow_add hn0, Real.rpow_add hn0,
      Real.rpow_one]
  calc (2 * (q : ℝ))⁻¹ * (2 : ℝ) ^ (-(1 + ε)) * (n : ℝ) ^ (1 - ε)
      = (n : ℝ) * (P * ((n : ℝ) / (2 * q))) := by rw [hPn, ← hpow]; field_simp
    _ ≤ (n : ℝ) * ∑ d ∈ Ioc n (2 * n), dampedSignWeight (coprimeIndicator q) ε d / d :=
        mul_le_mul_of_nonneg_left hsum hn0.le

/-- **Finite perturbations of the coprime weights are decided at the pole.** For `q ≥ 1`,
`0 < ε ≤ 1/2` and `k` supported on `[1, J]`, the receiver of `k ⋆ (1_{(·,q)=1} d^{-ε})` is bounded if
and only if `Σ_j k(j) j^{-(1−ε)} = 0`. -/
theorem receiverBounded_dirichletConv_coprime_iff {q : ℕ} (hq : 0 < q) {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) {k : ℕ → ℝ} {J : ℕ} (hkJ : ∀ j, J < j → k j = 0) :
    ReceiverBounded (RHTower.dirichletConv k (dampedSignWeight (coprimeIndicator q) ε)) ↔
      poleValue k J ε = 0 := by
  constructor
  · intro hB
    by_contra hK
    refine not_receiverBounded_dirichletConv_of_drift hε hε2
      (q := dampedSignWeight (coprimeIndicator q) ε)
      (fun d => mul_nonneg (coprimeIndicator_nonneg q d) (Real.rpow_nonneg (Nat.cast_nonneg d) _))
      (K := 1) (fun d => by
        rw [dampedSignWeight, abs_mul, abs_of_nonneg (coprimeIndicator_nonneg q d),
          abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _), one_mul]
        exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _)
          (coprimeIndicator_le_one q d))
      (κ := (2 * (q : ℝ))⁻¹ * (2 : ℝ) ^ (-(1 + ε))) (by positivity)
      (eventually_coprime_drift hq hε) hkJ hK hB
  · intro hK
    rw [show RHTower.dirichletConv k (dampedSignWeight (coprimeIndicator q) ε) =
        dampedSignWeight (RHTower.dirichletConv (undampedKernel k ε) (coprimeIndicator q)) ε from
      funext (dirichletConv_damped_eq k (coprimeIndicator q) ε)]
    exact exists_weightPronicEnergy_dampedSign_le
      (mul_nonneg (by positivity) (sum_nonneg fun j _ => abs_nonneg _)) hε
      (abs_sum_range_dirichletConv_coprime_le hq hkJ hK)

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
