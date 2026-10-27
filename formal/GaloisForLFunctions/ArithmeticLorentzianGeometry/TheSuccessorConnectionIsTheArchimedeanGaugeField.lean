import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheSignIsAGaugeFixing

/-!
# The successor connection is the archimedean gauge field

Two readings of the successor `n ↦ n + 1` meet on the atoms.

* **The successor is not a monotone direction of the prime form.** The successor defect of the
  atomic Weil prime form is the form of the shifted kernel `P(m + 1, n + 1) − P(m, n)`
  (`atomicWeilForm_succShift`), a shifted-divisor correlation. It has no sign on the nonnegative
  cone: `δ_1 + δ_3 ↦ δ_2 + δ_4` lowers the form (`log 2/√2 < log 3/√3`), `δ_2 + δ_5 ↦ δ_3 + δ_6`
  raises it (`atomicWeilForm_succShift_not_monotone`). A transfer-matrix positivity along the
  successor is not available at the level of the prime form.
* **The successor carries the gauge charge.** In the gauge `g = conj χ`, where the twisted prime
  kernel of a twin becomes the Euler kernel, the archimedean kernel on the successor edge
  `(n, n + 1)` carries exactly the phase `conj A_ω(n)` of the successor connection
  `A_ω(n) = conj χ(n) χ(n + 1)` of BiarithmeticGaugeGeometry (`gaugedArch_succ`). So it is
  nonnegative on every successor edge of `[1, N]` iff the connection is flat there, iff `ω(p) = 1`
  for every prime `p ≤ N + 1` (`gaugedArch_succ_nonneg_iff`).

The positive survivor of the successor-monotonicity route is therefore a reinterpretation: the
successor connection is the gauge field that the archimedean kernel sees once the prime kernel is
put in Euler form, and its flatness is the Lorentzian sign hypothesis.
-/

noncomputable section

open Finset Complex
open scoped ComplexConjugate ComplexOrder

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open ArithmeticEffectivityTheory BiarithmeticGaugeGeometry ArithmeticElectrostatics

/-! ### The successor defect of the prime form -/

/-- The successor shift of an atomic profile: `(Sx)_n = x_{n−1}` for `n ≥ 2`, `(Sx)_1 = 0`. -/
def succShiftProfile (x : ℕ → ℝ) (n : ℕ) : ℝ := if 2 ≤ n then x (n - 1) else 0

/-- **The successor defect is a shifted-kernel form**: `P_{N+1}(Sx) = Σ_{m,n ≤ N} x_m x_n P(m+1, n+1)`. -/
theorem atomicWeilForm_succShift (N : ℕ) (x : ℕ → ℝ) :
    atomicWeilForm (N + 1) (succShiftProfile x) =
      ∑ m ∈ Icc 1 N, ∑ n ∈ Icc 1 N, x m * x n * weilPrimeKernel (m + 1) (n + 1) := by
  have hsplit : ∀ f : ℕ → ℝ, ∑ n ∈ Icc 1 (N + 1), f n = f 1 + ∑ n ∈ Icc 1 N, f (n + 1) := by
    intro f
    rw [← Nat.Icc_insert_succ_left (by omega : 1 ≤ N + 1), sum_insert (by simp)]
    congr 1
    rw [show Icc (1 + 1) (N + 1) = (Icc 1 N).map (addRightEmbedding 1) by
      ext k; simp only [mem_Icc, mem_map, addRightEmbedding_apply]
      constructor
      · intro h; exact ⟨k - 1, by omega, by omega⟩
      · rintro ⟨a, ha, rfl⟩; omega, sum_map]
    rfl
  unfold atomicWeilForm
  rw [hsplit]
  simp only [succShiftProfile, show ¬ (2 ≤ 1) by omega, if_false, zero_mul, sum_const_zero,
    zero_add]
  refine sum_congr rfl fun m hm => ?_
  rw [hsplit]
  simp only [show ¬ (2 ≤ 1) by omega, if_false, mul_zero, zero_mul, zero_add]
  refine sum_congr rfl fun n hn => ?_
  have hm2 : 2 ≤ m + 1 := by have := (mem_Icc.mp hm).1; omega
  have hn2 : 2 ≤ n + 1 := by have := (mem_Icc.mp hn).1; omega
  simp only [hm2, hn2, if_true, Nat.add_sub_cancel]

/-- `log 2/√2 < log 3/√3`: from `2³ < 3²` and `√3 < (3/2)√2`. -/
theorem log_two_div_sqrt_lt : Real.log 2 / Real.sqrt 2 < Real.log 3 / Real.sqrt 3 := by
  have h32 : 3 * Real.log 2 < 2 * Real.log 3 := by
    rw [← Real.log_rpow (by norm_num), ← Real.log_rpow (by norm_num)]
    exact Real.log_lt_log (by norm_num) (by norm_num)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs2 : 0 < Real.sqrt 2 := by positivity
  have hs3 : 0 < Real.sqrt 3 := by positivity
  have hsq : Real.sqrt 3 ≤ 3 / 2 * Real.sqrt 2 := by
    rw [show (3 : ℝ) / 2 * Real.sqrt 2 = Real.sqrt (9 / 4 * 2) by
      rw [Real.sqrt_mul (by norm_num), show (9 : ℝ) / 4 = (3 / 2) ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  rw [div_lt_div_iff₀ hs2 hs3]
  nlinarith

theorem weilPrimeKernel_dvd_prime {m p : ℕ} (hm : 0 < m) (hp : p.Prime) :
    weilPrimeKernel m (m * p) = Real.log p / Real.sqrt p := by
  unfold weilPrimeKernel
  have hne : m ≠ m * p := fun h => by
    have := Nat.eq_of_mul_eq_mul_left hm (h.symm.trans (mul_one m).symm); exact hp.ne_one this
  rw [if_pos ⟨dvd_mul_right m p, hne⟩, Nat.mul_div_cancel_left p hm,
    ArithmeticFunction.vonMangoldt_apply_prime hp]

theorem weilPrimeKernel_eq_zero_of_coprime {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    (h : Nat.Coprime m n) : weilPrimeKernel m n = 0 := by
  unfold weilPrimeKernel
  have h1 : ¬ (m ∣ n ∧ m ≠ n) := fun h' =>
    absurd (Nat.Coprime.eq_one_of_dvd h h'.1) (by omega)
  have h2 : ¬ (n ∣ m ∧ n ≠ m) := fun h' =>
    absurd (Nat.Coprime.eq_one_of_dvd h.symm h'.1) (by omega)
  rw [if_neg h1, if_neg h2]

/-- **The successor is not a monotone direction** of the atomic Weil prime form on the
nonnegative cone: it lowers the form on `δ_1 + δ_3` and raises it on `δ_2 + δ_5`. -/
theorem atomicWeilForm_succShift_not_monotone :
    atomicWeilForm 4 (succShiftProfile fun n => if n = 1 ∨ n = 3 then 1 else 0) <
        atomicWeilForm 3 (fun n => if n = 1 ∨ n = 3 then 1 else 0) ∧
      atomicWeilForm 5 (fun n => if n = 2 ∨ n = 5 then 1 else 0) <
        atomicWeilForm 6 (succShiftProfile fun n => if n = 2 ∨ n = 5 then 1 else 0) := by
  have k13 : weilPrimeKernel 1 3 = Real.log 3 / Real.sqrt 3 := by
    simpa using weilPrimeKernel_dvd_prime one_pos Nat.prime_three
  have k24 : weilPrimeKernel 2 4 = Real.log 2 / Real.sqrt 2 := by
    simpa using weilPrimeKernel_dvd_prime (m := 2) (by norm_num) Nat.prime_two
  have k36 : weilPrimeKernel 3 6 = Real.log 2 / Real.sqrt 2 := by
    simpa using weilPrimeKernel_dvd_prime (m := 3) (by norm_num) Nat.prime_two
  have k25 : weilPrimeKernel 2 5 = 0 :=
    weilPrimeKernel_eq_zero_of_coprime (by norm_num) (by norm_num) (by norm_num)
  have hsym := weilPrimeKernel_comm
  have hl := log_two_div_sqrt_lt
  have hpos : 0 < Real.log 2 / Real.sqrt 2 :=
    div_pos (Real.log_pos (by norm_num)) (by positivity)
  constructor
  · rw [show (4 : ℕ) = 3 + 1 from rfl, atomicWeilForm_succShift]
    simp only [atomicWeilForm, show Icc 1 3 = {1, 2, 3} by decide, sum_insert, mem_insert,
      mem_singleton, sum_singleton]
    norm_num [weilPrimeKernel_self, k13, k24, hsym 3 1, hsym 4 2]
    linarith
  · rw [show (6 : ℕ) = 5 + 1 from rfl, atomicWeilForm_succShift]
    simp only [atomicWeilForm, show Icc 1 5 = {1, 2, 3, 4, 5} by decide, sum_insert, mem_insert,
      mem_singleton, sum_singleton]
    norm_num [weilPrimeKernel_self, k25, k36, hsym 5 2, hsym 6 3]
    linarith

/-! ### The successor connection as the archimedean gauge field -/

/-- **Gauge transport.** In the gauge `g = conj χ` (where the twin's prime kernel is Euler's), the
archimedean kernel on the successor edge `(n, n + 1)` carries the phase `conj A_ω(n)`. -/
theorem gaugedArch_succ (ω : PrimeGauge) (n : ℕ) :
    conj (conj (ω.gaugeChar n)) * conj (ω.gaugeChar (n + 1)) * (archAtomKernel n (n + 1) : ℂ) =
      conj (succConn ω n) * (archAtomKernel n (n + 1) : ℂ) := by
  simp only [succConn, map_mul, Complex.conj_conj]

theorem norm_succConn (ω : PrimeGauge) {n : ℕ} (hn : n ≠ 0) : ‖succConn ω n‖ = 1 := by
  rw [succConn, norm_mul, Complex.norm_conj, ω.norm_gaugeChar hn,
    ω.norm_gaugeChar (Nat.succ_ne_zero n), one_mul]

/-- **Flatness is the sign.** In the prime-Euler gauge the archimedean kernel is nonnegative on every
successor edge of `[1, N + 1]` iff the successor connection is flat on `[1, N]`, iff `ω(p) = 1` for
every prime `p ≤ N + 1`. -/
theorem gaugedArch_succ_nonneg_iff (ω : PrimeGauge) (N : ℕ) :
    (∀ n ∈ Icc 1 N, 0 ≤ conj (conj (ω.gaugeChar n)) * conj (ω.gaugeChar (n + 1)) *
        (archAtomKernel n (n + 1) : ℂ)) ↔
      ∀ p : ℕ, p ≤ N + 1 → p.Prime → ω.val p = 1 := by
  rw [← succConn_flat_iff_primes_eq_one]
  refine forall₂_congr fun n hn => ?_
  have hn0 : n ≠ 0 := by have := (mem_Icc.mp hn).1; omega
  have hA := archAtomKernel_pos (Nat.pos_of_ne_zero hn0) (Nat.succ_pos n) (Nat.succ_ne_self n).symm
  rw [gaugedArch_succ]
  constructor
  · intro h
    exact eq_of_conj_mul_nonneg (norm_succConn ω hn0) norm_one hA (by simpa using h)
  · intro h
    rw [h, map_one, one_mul]
    exact_mod_cast hA.le

end GaloisForLFunctions.ArithmeticLorentzianGeometry
