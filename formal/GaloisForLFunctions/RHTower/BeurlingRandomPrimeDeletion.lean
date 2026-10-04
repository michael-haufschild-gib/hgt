import GaloisForLFunctions.HTGeometry.GroupedSelectionConcentration

/-!
# A thinning of the primes with square-root discrepancy at every frequency

Fix `0 < α < 1` and give the prime `p` the weight `w(p) = p^{α−1}`.  In the dyadic block
`[2^k, 2^{k+1})` cut the primes into the groups `G_{k,i}` of those `p` with
`⌊(p − 2^k)/L_k⌋ = i`, `L_k = ⌊2^{k(1−α)}⌋`.  A group has at most `L_k` elements, each of weight
`≤ 2^{k(α−1)}`, so its weight is `≤ 1`; there are `n_k ≤ 3·2^{kα}` groups.  Select at most one
prime per group, `p` with probability `w(p)` (`HTGeometry.GroupedSelection`).

**Block bound** (`norm_blockDev_le`).  Some selection makes the block deviation
`D_k(x, t) = Σ_{p ∈ block, p ≤ x} (1[p selected] − w(p)) p^{−it}` satisfy, for all real `x`, `t`,

`|D_k(x, t)| ≤ 26 · 2^{kα/2} √(k+1) √log(|t|+2) + 2`.

Only the cutoff primes `x = q` of the block and the net points `t = ±m/(n_k(k+1))` are tested;
the threshold `4√n_k √log(2^{k+5}(m+1)²)` makes the failure probabilities sum to `π²/24 < 1`, and
`|p^{−it} − p^{−it'}| ≤ |t − t'| log p` covers the rest of the line.

**Discrepancy** (`exists_deletedPrimes`).  Gluing one good selection per block gives a set `S` of
primes and a constant `C` with

`|Σ_{p ≤ x} (1_S(p) − p^{α−1}) p^{−it}| ≤ C x^{α/2} (log x + 1) √log(|t|+2)`

for all `x ≥ 1` and all real `t`.
-/

open Complex Finset
open GaloisForLFunctions.HTGeometry.GroupedSelection
open scoped ENNReal

noncomputable section

namespace RHTower.BeurlingDeletion

variable {α : ℝ}

/-! ## Weights, blocks and groups -/

/-- The deletion weight `p^{α−1}`. -/
def delWeight (α : ℝ) (p : ℕ) : ℝ := (p : ℝ) ^ (α - 1)

theorem delWeight_nonneg (α : ℝ) (p : ℕ) : 0 ≤ delWeight α p :=
  Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- The group length `⌊2^{k(1−α)}⌋` in block `k`. -/
def blockLen (α : ℝ) (k : ℕ) : ℕ := ⌊(2 : ℝ) ^ ((k : ℝ) * (1 - α))⌋₊

theorem one_le_two_rpow (hα : α < 1) (k : ℕ) : 1 ≤ (2 : ℝ) ^ ((k : ℝ) * (1 - α)) :=
  Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg _) (by linarith))

theorem one_le_blockLen (hα : α < 1) (k : ℕ) : 1 ≤ blockLen α k :=
  Nat.le_floor (by exact_mod_cast one_le_two_rpow hα k)

theorem blockLen_pos (hα : α < 1) (k : ℕ) : 0 < blockLen α k := one_le_blockLen hα k

theorem blockLen_le (hα : α < 1) (k : ℕ) :
    (blockLen α k : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) * (1 - α)) :=
  Nat.floor_le (le_trans zero_le_one (one_le_two_rpow hα k))

theorem half_le_blockLen (hα : α < 1) (k : ℕ) :
    (2 : ℝ) ^ ((k : ℝ) * (1 - α)) / 2 ≤ blockLen α k := by
  have h1 := Nat.lt_floor_add_one ((2 : ℝ) ^ ((k : ℝ) * (1 - α)))
  have h2 : (1 : ℝ) ≤ blockLen α k := by exact_mod_cast one_le_blockLen hα k
  unfold blockLen at h2 ⊢
  linarith

/-- The number of groups of block `k`. -/
def blockCount (α : ℝ) (k : ℕ) : ℕ := 2 ^ k / blockLen α k + 1

theorem blockCount_pos (α : ℝ) (k : ℕ) : 0 < blockCount α k := Nat.succ_pos _

theorem two_pow_eq (α : ℝ) (k : ℕ) :
    (2 : ℝ) ^ k = (2 : ℝ) ^ ((k : ℝ) * (1 - α)) * (2 : ℝ) ^ ((k : ℝ) * α) := by
  rw [← Real.rpow_add (by norm_num), ← Real.rpow_natCast]
  congr 1
  ring

theorem blockCount_le (hα0 : 0 < α) (hα : α < 1) (k : ℕ) :
    (blockCount α k : ℝ) ≤ 3 * (2 : ℝ) ^ ((k : ℝ) * α) := by
  have hL := half_le_blockLen hα k
  have hpos : 0 < (2 : ℝ) ^ ((k : ℝ) * (1 - α)) := Real.rpow_pos_of_pos (by norm_num) _
  have hLpos : (0 : ℝ) < blockLen α k := by exact_mod_cast blockLen_pos hα k
  have hdiv : ((2 ^ k / blockLen α k : ℕ) : ℝ) ≤ (2 : ℝ) ^ k / blockLen α k := by
    rw [le_div_iff₀ hLpos]
    exact_mod_cast Nat.div_mul_le_self _ _
  have h2 : (2 : ℝ) ^ k / blockLen α k ≤ 2 * (2 : ℝ) ^ ((k : ℝ) * α) := by
    rw [div_le_iff₀ hLpos, two_pow_eq α k]
    nlinarith [Real.rpow_pos_of_pos (show (0 : ℝ) < 2 by norm_num) ((k : ℝ) * α)]
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ ((k : ℝ) * α) :=
    Real.one_le_rpow (by norm_num) (mul_nonneg (Nat.cast_nonneg _) hα0.le)
  unfold blockCount
  push_cast
  linarith

/-- The primes of block `k`. -/
def blockPrimes (k : ℕ) : Finset ℕ := (Finset.Ico (2 ^ k) (2 ^ (k + 1))).filter Nat.Prime

theorem card_blockPrimes_le (k : ℕ) : (blockPrimes k).card ≤ 2 ^ k := by
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Nat.card_Ico, pow_succ]
  omega

theorem mem_blockPrimes {k p : ℕ} : p ∈ blockPrimes k ↔ p.Prime ∧ 2 ^ k ≤ p ∧ p < 2 ^ (k + 1) := by
  simp [blockPrimes, and_comm]

/-- The group index `⌊(p − 2^k)/L_k⌋`. -/
def blockIdx (α : ℝ) (k p : ℕ) : ℕ := (p - 2 ^ k) / blockLen α k

theorem blockIdx_lt {k p : ℕ} (hp : p ∈ blockPrimes k) :
    blockIdx α k p < blockCount α k := by
  rw [mem_blockPrimes] at hp
  unfold blockIdx blockCount
  have : p - 2 ^ k ≤ 2 ^ k := by rw [pow_succ] at hp; omega
  exact Nat.lt_succ_of_le (Nat.div_le_div_right this)

/-- The group `G_{k,i}`. -/
def blockGroup (α : ℝ) (k : ℕ) (i : Fin (blockCount α k)) : Finset ℕ :=
  (blockPrimes k).filter fun p => blockIdx α k p = i

theorem zero_not_mem_blockGroup (α : ℝ) (k : ℕ) (i : Fin (blockCount α k)) :
    0 ∉ blockGroup α k i := by
  simp [blockGroup, mem_blockPrimes, Nat.not_prime_zero]

theorem card_blockGroup_le (hα : α < 1) (k : ℕ) (i : Fin (blockCount α k)) :
    (blockGroup α k i).card ≤ blockLen α k := by
  have hL := blockLen_pos hα k
  calc (blockGroup α k i).card ≤ (Finset.range (blockLen α k)).card := by
        refine Finset.card_le_card_of_injOn (fun p => p - 2 ^ k - (i : ℕ) * blockLen α k)
          (fun p hp => ?_) (fun p hp q hq hpq => ?_)
        · simp only [blockGroup, Finset.coe_filter, Set.mem_setOf_eq, mem_blockPrimes] at hp
          simp only [Finset.coe_range, Set.mem_Iio]
          obtain ⟨⟨-, hk, -⟩, hi⟩ := hp
          unfold blockIdx at hi
          have h1 := Nat.div_mul_le_self (p - 2 ^ k) (blockLen α k)
          have h2 := Nat.lt_div_mul_add (a := p - 2 ^ k) hL
          rw [hi] at h1 h2
          omega
        · simp only [blockGroup, Finset.coe_filter, Set.mem_setOf_eq, mem_blockPrimes] at hp hq
          have h1 := Nat.div_mul_le_self (p - 2 ^ k) (blockLen α k)
          have h2 := Nat.div_mul_le_self (q - 2 ^ k) (blockLen α k)
          unfold blockIdx at hp hq
          rw [hp.2] at h1
          rw [hq.2] at h2
          simp only at hpq
          omega
    _ = blockLen α k := Finset.card_range _

theorem delWeight_le (hα : α < 1) {k p : ℕ} (hp : 2 ^ k ≤ p) :
    delWeight α p ≤ (2 : ℝ) ^ ((k : ℝ) * (α - 1)) := by
  have h2k : (0 : ℝ) < 2 ^ k := by positivity
  have hpk : ((2 : ℝ) ^ k) ≤ p := by exact_mod_cast hp
  calc delWeight α p = (p : ℝ) ^ (α - 1) := rfl
    _ ≤ ((2 : ℝ) ^ k) ^ (α - 1) := Real.rpow_le_rpow_of_nonpos h2k hpk (by linarith)
    _ = (2 : ℝ) ^ ((k : ℝ) * (α - 1)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]

theorem sum_delWeight_blockGroup_le_one (hα : α < 1) (k : ℕ) (i : Fin (blockCount α k)) :
    ∑ p ∈ blockGroup α k i, delWeight α p ≤ 1 := by
  have hb : ∀ p ∈ blockGroup α k i, delWeight α p ≤ (2 : ℝ) ^ ((k : ℝ) * (α - 1)) := by
    intro p hp
    simp only [blockGroup, Finset.mem_filter, mem_blockPrimes] at hp
    exact delWeight_le hα hp.1.2.1
  calc ∑ p ∈ blockGroup α k i, delWeight α p
      ≤ ∑ _p ∈ blockGroup α k i, (2 : ℝ) ^ ((k : ℝ) * (α - 1)) := Finset.sum_le_sum hb
    _ = (blockGroup α k i).card * (2 : ℝ) ^ ((k : ℝ) * (α - 1)) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (2 : ℝ) ^ ((k : ℝ) * (1 - α)) * (2 : ℝ) ^ ((k : ℝ) * (α - 1)) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.rpow_nonneg (by norm_num) _)
        exact le_trans (by exact_mod_cast card_blockGroup_le hα k i) (blockLen_le hα k)
    _ = 1 := by
        rw [← Real.rpow_add (by norm_num)]
        simp [show (k : ℝ) * (1 - α) + (k : ℝ) * (α - 1) = 0 by ring]

/-! ## Tests and the block deviation -/

/-- The test `p ↦ 1[0 < p ≤ x] p^{−it}`. -/
def testFn (x t : ℝ) (p : ℕ) : ℂ :=
  if 0 < p ∧ (p : ℝ) ≤ x then (p : ℂ) ^ (-((t : ℂ) * I)) else 0

theorem norm_natCast_cpow_neg_mul_I {p : ℕ} (hp : 0 < p) (t : ℝ) :
    ‖(p : ℂ) ^ (-((t : ℂ) * I))‖ = 1 := by
  rw [Complex.norm_natCast_cpow_of_pos hp]
  simp

theorem norm_testFn_le (x t : ℝ) (p : ℕ) : ‖testFn x t p‖ ≤ 1 := by
  unfold testFn
  split_ifs with h
  · rw [norm_natCast_cpow_neg_mul_I h.1]
  · simp

/-- The deviation of block `k` under the choice `ω`. -/
def blockDev (α : ℝ) (k : ℕ) (ω : Fin (blockCount α k) → ℕ) (x t : ℝ) : ℂ :=
  ∑ i, groupDev (blockGroup α k) (delWeight α) (testFn x t) i (ω i)

/-- The net spacing `1/(n_k(k+1))`. -/
def netStep (α : ℝ) (k : ℕ) : ℝ := 1 / ((blockCount α k : ℝ) * ((k : ℝ) + 1))

theorem netStep_pos (α : ℝ) (k : ℕ) : 0 < netStep α k := by
  have := blockCount_pos α k
  unfold netStep
  positivity

/-- The net point `±m·step`. -/
def netPoint (α : ℝ) (k : ℕ) (b : Bool) (m : ℕ) : ℝ :=
  (if b then (1 : ℝ) else -1) * (m : ℝ) * netStep α k

/-- The threshold at net index `m`. -/
def threshold (α : ℝ) (k m : ℕ) : ℝ :=
  4 * Real.sqrt (blockCount α k) *
    Real.sqrt (Real.log ((2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2))

theorem one_le_arg (k m : ℕ) : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2 := by
  have h1 : (1 : ℝ) ≤ (2 : ℝ) ^ (k + 5) := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := one_le_pow₀ (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])
  nlinarith

theorem threshold_nonneg (α : ℝ) (k m : ℕ) : 0 ≤ threshold α k m := by
  unfold threshold; positivity

theorem exp_neg_threshold (α : ℝ) (k m : ℕ) :
    4 * Real.exp (-threshold α k m ^ 2 / (16 * (blockCount α k : ℝ))) =
      4 / ((2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2) := by
  have hn : (0 : ℝ) < blockCount α k := by exact_mod_cast blockCount_pos α k
  have harg := one_le_arg k m
  have hlog : 0 ≤ Real.log ((2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2) := Real.log_nonneg harg
  unfold threshold
  rw [mul_pow, mul_pow, Real.sq_sqrt hn.le, Real.sq_sqrt hlog]
  rw [show -((4 : ℝ) ^ 2 * (blockCount α k : ℝ) *
      Real.log ((2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2)) / (16 * (blockCount α k : ℝ)) =
      -Real.log ((2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2) by field_simp; ring,
    Real.exp_neg, Real.exp_log (by linarith)]
  ring

theorem hasSum_inv_succ_sq : HasSum (fun m : ℕ => 1 / ((m : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
  have h := (hasSum_nat_add_iff' (f := fun n : ℕ => 1 / (n : ℝ) ^ 2) 1).mpr hasSum_zeta_two
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, div_zero, sub_zero, Nat.cast_add, Nat.cast_one] at h
  exact h

theorem tsum_failure_lt (α : ℝ) (k : ℕ) :
    ∑' e : {q // q ∈ blockPrimes k} × Bool × ℕ,
      ENNReal.ofReal (4 * Real.exp (-threshold α k e.2.2 ^ 2 / (16 * (blockCount α k : ℝ)))) < 1 := by
  simp only [exp_neg_threshold]
  have hsum : HasSum (fun m : ℕ => 4 / ((2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2))
      (4 / (2 : ℝ) ^ (k + 5) * (Real.pi ^ 2 / 6)) := by
    have := hasSum_inv_succ_sq.mul_left (4 / (2 : ℝ) ^ (k + 5))
    refine this.congr_fun fun m => ?_
    field_simp
  have hm : ∑' m : ℕ, ENNReal.ofReal (4 / ((2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2)) =
      ENNReal.ofReal (4 / (2 : ℝ) ^ (k + 5) * (Real.pi ^ 2 / 6)) := by
    rw [← hsum.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun m => by positivity) hsum.summable]
  set F : ℕ → ℝ≥0∞ := fun m => ENNReal.ofReal (4 / ((2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2))
    with hF
  have hsplit : (∑' e : {q // q ∈ blockPrimes k} × Bool × ℕ, F e.2.2) =
      ∑' _q : {q // q ∈ blockPrimes k}, ∑' _b : Bool, ∑' m : ℕ, F m := by
    refine (ENNReal.tsum_prod (f := fun _q (bm : Bool × ℕ) => F bm.2)).trans ?_
    exact tsum_congr fun _ => ENNReal.tsum_prod (f := fun _b m => F m)
  change (∑' e : {q // q ∈ blockPrimes k} × Bool × ℕ, F e.2.2) < 1
  rw [hsplit]
  set c : ℝ≥0∞ := ENNReal.ofReal (4 / (2 : ℝ) ^ (k + 5) * (Real.pi ^ 2 / 6)) with hc
  have hm' : (∑' m : ℕ, F m) = c := hm
  simp only [hm', tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_bool,
    Fintype.card_coe, nsmul_eq_mul]
  have hcard : ((blockPrimes k).card : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ k := by
    exact_mod_cast card_blockPrimes_le k
  have hval : ((2 : ℕ) : ℝ≥0∞) * c = ENNReal.ofReal (Real.pi ^ 2 / 24) * ((2 : ℝ≥0∞) ^ k)⁻¹ := by
    rw [hc, show ((2 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 2 by simp,
      ← ENNReal.ofReal_mul (by norm_num),
      show ((2 : ℝ≥0∞) ^ k)⁻¹ = ENNReal.ofReal (((2 : ℝ) ^ k)⁻¹) by
        rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by norm_num)]
        simp,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1
    rw [pow_add]
    field_simp
    ring
  rw [hval]
  calc ((blockPrimes k).card : ℝ≥0∞) * (ENNReal.ofReal (Real.pi ^ 2 / 24) * ((2 : ℝ≥0∞) ^ k)⁻¹)
      ≤ (2 : ℝ≥0∞) ^ k * (ENNReal.ofReal (Real.pi ^ 2 / 24) * ((2 : ℝ≥0∞) ^ k)⁻¹) :=
        mul_le_mul_left hcard _
    _ = ENNReal.ofReal (Real.pi ^ 2 / 24) := by
        rw [mul_comm, mul_assoc, ENNReal.inv_mul_cancel (by positivity) (by simp), mul_one]
    _ < 1 := by
        rw [← ENNReal.ofReal_one]
        refine (ENNReal.ofReal_lt_ofReal_iff one_pos).mpr ?_
        have h1 := Real.pi_lt_d2
        have h0 := Real.pi_pos
        have hsq : Real.pi ^ 2 < 3.15 ^ 2 := by nlinarith
        norm_num at hsq ⊢
        linarith

/-- **One block admits a good selection.** -/
theorem exists_blockChoice (hα : α < 1) (k : ℕ) :
    ∃ ω : Fin (blockCount α k) → ℕ, (∀ i, ω i = 0 ∨ ω i ∈ blockGroup α k i) ∧
      ∀ (q : {q // q ∈ blockPrimes k}) (b : Bool) (m : ℕ),
        ‖blockDev α k ω q (netPoint α k b m)‖ < threshold α k m := by
  obtain ⟨ω, hω, hdev⟩ := exists_selection (G := blockGroup α k) (w := delWeight α)
    (fun p => delWeight_nonneg α p) (fun i => sum_delWeight_blockGroup_le_one hα k i)
    (fun i => zero_not_mem_blockGroup α k i)
    (E := {q // q ∈ blockPrimes k} × Bool × ℕ)
    (fun e => testFn e.1 (netPoint α k e.2.1 e.2.2)) (fun e p => norm_testFn_le _ _ p)
    (fun e => threshold α k e.2.2) (fun e => threshold_nonneg α k e.2.2) (tsum_failure_lt α k)
  exact ⟨ω, hω, fun q b m => hdev (q, b, m)⟩

/-! ## The block bound on the whole line -/

theorem norm_cpow_sub_cpow_le {p : ℕ} (hp : 0 < p) (t t' : ℝ) :
    ‖(p : ℂ) ^ (-((t : ℂ) * I)) - (p : ℂ) ^ (-((t' : ℂ) * I))‖ ≤ |t - t'| * Real.log p := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hlog : Complex.log (p : ℂ) = (Real.log p : ℂ) := (Complex.ofReal_natCast p ▸
    (Complex.ofReal_log (Nat.cast_nonneg p)).symm)
  rw [Complex.cpow_def_of_ne_zero hp0, Complex.cpow_def_of_ne_zero hp0, hlog]
  have e1 : (Real.log p : ℂ) * -((t : ℂ) * I) = I * ((-(t * Real.log p) : ℝ) : ℂ) := by
    push_cast; ring
  have e2 : (Real.log p : ℂ) * -((t' : ℂ) * I) = I * ((-(t' * Real.log p) : ℝ) : ℂ) := by
    push_cast; ring
  rw [e1, e2]
  set a : ℝ := -(t * Real.log p)
  set b : ℝ := -(t' * Real.log p)
  have hfac : Complex.exp (I * (a : ℂ)) - Complex.exp (I * (b : ℂ)) =
      Complex.exp (I * (b : ℂ)) * (Complex.exp (I * ((a - b : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    push_cast
    ring_nf
  rw [hfac, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
  have hl : 0 ≤ Real.log p := Real.log_natCast_nonneg p
  rw [Real.norm_eq_abs, show a - b = -((t - t') * Real.log p) by ring, abs_neg, abs_mul,
    abs_of_nonneg hl]

theorem log_le_of_mem_blockPrimes {k p : ℕ} (hp : p ∈ blockPrimes k) :
    Real.log p ≤ (k : ℝ) + 1 := by
  rw [mem_blockPrimes] at hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.1.pos
  have hlt : (p : ℝ) < (2 : ℝ) ^ (k + 1) := by exact_mod_cast hp.2.2
  have h1 : Real.log p < (k + 1 : ℕ) * Real.log 2 := by
    rw [← Real.log_pow]; exact Real.log_lt_log hp0 hlt
  have h2 := Real.log_two_lt_d9
  push_cast at h1
  nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]

/-- Changing `t` by `h` moves the block deviation by at most `2 n_k (k+1) |h|`. -/
theorem norm_blockDev_sub_le (hα : α < 1) (k : ℕ) (ω : Fin (blockCount α k) → ℕ) (x t t' : ℝ) :
    ‖blockDev α k ω x t - blockDev α k ω x t'‖ ≤
      2 * (blockCount α k : ℝ) * (((k : ℝ) + 1) * |t - t'|) := by
  unfold blockDev
  rw [← Finset.sum_sub_distrib]
  have hD : 0 ≤ ((k : ℝ) + 1) * |t - t'| := by positivity
  calc ‖∑ i, (groupDev (blockGroup α k) (delWeight α) (testFn x t) i (ω i) -
        groupDev (blockGroup α k) (delWeight α) (testFn x t') i (ω i))‖
      ≤ ∑ i : Fin (blockCount α k), 2 * (((k : ℝ) + 1) * |t - t'|) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
        rw [groupDev_sub]
        refine norm_groupDev_le_of_le _ (fun p hp => ?_) (fun p => delWeight_nonneg α p)
          (fun i => sum_delWeight_blockGroup_le_one hα k i) hD _
        have hpb : p ∈ blockPrimes k := (Finset.mem_filter.mp hp).1
        have hpos : 0 < p := (mem_blockPrimes.mp hpb).1.pos
        unfold testFn
        split_ifs with h
        · refine (norm_cpow_sub_cpow_le hpos t t').trans ?_
          rw [mul_comm]
          exact mul_le_mul_of_nonneg_right (log_le_of_mem_blockPrimes hpb) (abs_nonneg _)
        · simpa using hD
    _ = 2 * (blockCount α k : ℝ) * (((k : ℝ) + 1) * |t - t'|) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

/-- The block deviation only depends on the cutoff through the block primes below it. -/
theorem blockDev_eq_of_cutoff (k : ℕ) (ω : Fin (blockCount α k) → ℕ) {x y : ℝ}
    (h : ∀ p ∈ blockPrimes k, ((p : ℝ) ≤ x ↔ (p : ℝ) ≤ y)) (t : ℝ) :
    blockDev α k ω x t = blockDev α k ω y t := by
  unfold blockDev
  refine Finset.sum_congr rfl fun i _ => groupDev_congr (fun p hp => ?_) _
  have hpb : p ∈ blockPrimes k := (Finset.mem_filter.mp hp).1
  unfold testFn
  simp only [h p hpb]

theorem blockDev_zero_of_cutoff (k : ℕ) (ω : Fin (blockCount α k) → ℕ) {x : ℝ}
    (h : ∀ p ∈ blockPrimes k, x < p) (t : ℝ) : blockDev α k ω x t = 0 := by
  unfold blockDev
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [groupDev_congr (φ' := fun _ => 0) (fun p hp => ?_)]
  · simp [groupDev]
  · have hpb : p ∈ blockPrimes k := (Finset.mem_filter.mp hp).1
    unfold testFn
    rw [if_neg fun h' => absurd h'.2 (not_le.mpr (h p hpb))]

theorem sqrt_two_rpow (k : ℕ) (α : ℝ) :
    Real.sqrt ((2 : ℝ) ^ ((k : ℝ) * α)) = (2 : ℝ) ^ ((k : ℝ) * α / 2) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul (by norm_num)]
  congr 1
  ring

/-- **The threshold grows like `2^{kα/2}√(k+1)√log(|t|+2)`.** -/
theorem threshold_le (hα0 : 0 < α) (hα : α < 1) (k m : ℕ) {t : ℝ}
    (hm : (m : ℝ) ≤ |t| / netStep α k) :
    threshold α k m ≤ 26 * (2 : ℝ) ^ ((k : ℝ) * α / 2) * Real.sqrt ((k : ℝ) + 1) *
      Real.sqrt (Real.log (|t| + 2)) := by
  set n : ℝ := (blockCount α k : ℝ) with hn
  have hn0 : 0 < n := by rw [hn]; exact_mod_cast blockCount_pos α k
  have hnle := blockCount_le hα0 hα k
  rw [← hn] at hnle
  have h2a : (2 : ℝ) ^ ((k : ℝ) * α) ≤ (2 : ℝ) ^ k := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by nlinarith [(Nat.cast_nonneg k : (0:ℝ) ≤ k)])
  have hk2 : (k : ℝ) + 1 ≤ (2 : ℝ) ^ k := by
    have := Nat.lt_two_pow_self (n := k)
    have : k + 1 ≤ 2 ^ k := this
    exact_mod_cast this
  have hL : Real.log 2 ≤ Real.log (|t| + 2) :=
    Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hlog2 := Real.log_two_gt_d9
  set L := Real.log (|t| + 2) with hLdef
  have hL0 : 1 / 2 ≤ L := by linarith
  -- bound on `m + 1`
  have hstep : |t| / netStep α k = |t| * (n * ((k : ℝ) + 1)) := by
    unfold netStep; rw [← hn]; field_simp
  rw [hstep] at hm
  have hm1 : (m : ℝ) + 1 ≤ 3 * (4 : ℝ) ^ k * (|t| + 2) := by
    have h4 : n * ((k : ℝ) + 1) ≤ 3 * (4 : ℝ) ^ k := by
      have : (4 : ℝ) ^ k = (2 : ℝ) ^ k * (2 : ℝ) ^ k := by rw [← mul_pow]; norm_num
      rw [this]
      have h3 : n ≤ 3 * (2 : ℝ) ^ k := hnle.trans (by linarith)
      nlinarith [pow_pos (show (0:ℝ) < 2 by norm_num) k]
    have hpow : (1 : ℝ) ≤ 3 * (4 : ℝ) ^ k := by
      have := one_le_pow₀ (show (1 : ℝ) ≤ 4 by norm_num) (n := k); linarith
    nlinarith [abs_nonneg t]
  -- bound on the logarithm
  have harg : (2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2 ≤ 288 * (32 : ℝ) ^ k * (|t| + 2) ^ 2 := by
    have hm0 : 0 ≤ (m : ℝ) + 1 := by positivity
    have hsq : ((m : ℝ) + 1) ^ 2 ≤ (3 * (4 : ℝ) ^ k * (|t| + 2)) ^ 2 :=
      pow_le_pow_left₀ hm0 hm1 2
    have e : (2 : ℝ) ^ (k + 5) * (3 * (4 : ℝ) ^ k * (|t| + 2)) ^ 2 =
        288 * (32 : ℝ) ^ k * (|t| + 2) ^ 2 := by
      rw [pow_add, mul_pow, mul_pow, ← pow_mul,
        show (32 : ℝ) ^ k = (2 : ℝ) ^ k * ((4 : ℝ) ^ k) ^ 2 by
          rw [← pow_mul, show (32 : ℝ) = 2 * 4 ^ 2 by norm_num, mul_pow, ← pow_mul, mul_comm k 2]]
      ring
    calc _ ≤ (2 : ℝ) ^ (k + 5) * (3 * (4 : ℝ) ^ k * (|t| + 2)) ^ 2 :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
      _ = _ := e
  have hlogarg : Real.log ((2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2) ≤ 14 * ((k : ℝ) + 1) * L := by
    have h1 := Real.log_le_log (by have := one_le_arg k m; linarith) harg
    have h2 : Real.log (288 * (32 : ℝ) ^ k * (|t| + 2) ^ 2) =
        Real.log 288 + (k : ℝ) * Real.log 32 + 2 * L := by
      rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
        Real.log_pow, Real.log_pow, hLdef]
      push_cast; ring
    have h288 : Real.log 288 < 6 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := Real.exp_one_gt_d9
      calc (288 : ℝ) < 2.7182818283 ^ 6 := by norm_num
        _ < Real.exp 1 ^ 6 := by gcongr
        _ = Real.exp 6 := by rw [← Real.exp_nat_mul]; norm_num
    have h32 : Real.log 32 < 4 := by
      rw [Real.log_lt_iff_lt_exp (by norm_num)]
      have := Real.exp_one_gt_d9
      calc (32 : ℝ) < 2.7182818283 ^ 4 := by norm_num
        _ < Real.exp 1 ^ 4 := by gcongr
        _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hL0' : 0 ≤ L := by linarith
    have hkL : (k : ℝ) * Real.log 32 ≤ 4 * k := by nlinarith
    nlinarith [mul_nonneg hk0 hL0']
  have hsqrt : Real.sqrt (Real.log ((2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2)) ≤
      Real.sqrt 14 * Real.sqrt ((k : ℝ) + 1) * Real.sqrt L := by
    rw [← Real.sqrt_mul (by norm_num), ← Real.sqrt_mul (by positivity)]
    exact Real.sqrt_le_sqrt (by linarith)
  have hsn : Real.sqrt n ≤ Real.sqrt 3 * (2 : ℝ) ^ ((k : ℝ) * α / 2) := by
    rw [← sqrt_two_rpow, ← Real.sqrt_mul (by norm_num)]
    exact Real.sqrt_le_sqrt hnle
  have h42 : 4 * Real.sqrt 3 * Real.sqrt 14 ≤ 26 := by
    have hs : Real.sqrt 3 * Real.sqrt 14 = Real.sqrt 42 := by
      rw [← Real.sqrt_mul (by norm_num)]; norm_num
    have : Real.sqrt 42 ≤ 6.5 := by rw [Real.sqrt_le_left (by norm_num)]; norm_num
    nlinarith [hs]
  unfold threshold
  rw [← hn]
  have hA : 0 ≤ (2 : ℝ) ^ ((k : ℝ) * α / 2) := by positivity
  calc 4 * Real.sqrt n * Real.sqrt (Real.log ((2 : ℝ) ^ (k + 5) * ((m : ℝ) + 1) ^ 2))
      ≤ 4 * (Real.sqrt 3 * (2 : ℝ) ^ ((k : ℝ) * α / 2)) *
          (Real.sqrt 14 * Real.sqrt ((k : ℝ) + 1) * Real.sqrt L) := by gcongr
    _ = (4 * Real.sqrt 3 * Real.sqrt 14) * (2 : ℝ) ^ ((k : ℝ) * α / 2) *
          Real.sqrt ((k : ℝ) + 1) * Real.sqrt L := by ring
    _ ≤ 26 * (2 : ℝ) ^ ((k : ℝ) * α / 2) * Real.sqrt ((k : ℝ) + 1) * Real.sqrt L := by
        gcongr

/-- **The block bound.** -/
theorem norm_blockDev_le (hα0 : 0 < α) (hα : α < 1) (k : ℕ) {ω : Fin (blockCount α k) → ℕ}
    (hω : ∀ (q : {q // q ∈ blockPrimes k}) (b : Bool) (m : ℕ),
      ‖blockDev α k ω q (netPoint α k b m)‖ < threshold α k m) (x t : ℝ) :
    ‖blockDev α k ω x t‖ ≤ 26 * (2 : ℝ) ^ ((k : ℝ) * α / 2) * Real.sqrt ((k : ℝ) + 1) *
      Real.sqrt (Real.log (|t| + 2)) + 2 := by
  classical
  have hRHS : 0 ≤ 26 * (2 : ℝ) ^ ((k : ℝ) * α / 2) * Real.sqrt ((k : ℝ) + 1) *
      Real.sqrt (Real.log (|t| + 2)) := by positivity
  set P := (blockPrimes k).filter fun p : ℕ => ((p : ℝ) ≤ x) with hP
  by_cases hne : P.Nonempty
  swap
  · rw [blockDev_zero_of_cutoff k ω (fun p hp => ?_) t]
    · simp only [norm_zero]; linarith
    · by_contra hle
      exact hne ⟨p, Finset.mem_filter.mpr ⟨hp, not_lt.mp hle⟩⟩
  set q := P.max' hne with hq
  have hqP : q ∈ P := P.max'_mem hne
  have hqb : q ∈ blockPrimes k := (Finset.mem_filter.mp hqP).1
  have hcut : ∀ p ∈ blockPrimes k, ((p : ℝ) ≤ x ↔ (p : ℝ) ≤ (q : ℝ)) := by
    intro p hp
    constructor
    · intro hpx
      exact_mod_cast P.le_max' p (Finset.mem_filter.mpr ⟨hp, hpx⟩)
    · intro hpq
      exact hpq.trans (Finset.mem_filter.mp hqP).2
  rw [blockDev_eq_of_cutoff k ω hcut t]
  -- the net point
  set η := netStep α k with hη
  have hη0 : 0 < η := netStep_pos α k
  set m : ℕ := ⌊|t| / η⌋₊ with hm
  have hm1 : (m : ℝ) ≤ |t| / η := Nat.floor_le (div_nonneg (abs_nonneg t) hη0.le)
  have hm2 : |t| / η < (m : ℝ) + 1 := Nat.lt_floor_add_one _
  set b : Bool := decide (0 ≤ t) with hb
  have hclose : |t - netPoint α k b m| ≤ η := by
    have hmη : (m : ℝ) * η ≤ |t| := by rwa [le_div_iff₀ hη0] at hm1
    have hmη' : |t| < ((m : ℝ) + 1) * η := by rwa [div_lt_iff₀ hη0] at hm2
    unfold netPoint
    rw [← hη]
    by_cases ht : 0 ≤ t
    · have : b = true := by rw [hb]; exact decide_eq_true ht
      rw [this, if_pos rfl, abs_of_nonneg ht] at *
      rw [abs_le]; constructor <;> nlinarith
    · have : b = false := by rw [hb]; exact decide_eq_false ht
      rw [this, if_neg (by simp)]
      rw [abs_of_neg (not_le.mp ht)] at hmη hmη'
      rw [abs_le]; constructor <;> nlinarith
  have hlip := norm_blockDev_sub_le hα k ω q t (netPoint α k b m)
  have hlip' : 2 * (blockCount α k : ℝ) * (((k : ℝ) + 1) * |t - netPoint α k b m|) ≤ 2 := by
    have hn0 : (0 : ℝ) < blockCount α k := by exact_mod_cast blockCount_pos α k
    have hk : (0 : ℝ) < (k : ℝ) + 1 := by positivity
    calc _ ≤ 2 * (blockCount α k : ℝ) * (((k : ℝ) + 1) * η) := by gcongr
      _ = 2 := by rw [hη]; unfold netStep; field_simp
  have hnet := hω ⟨q, hqb⟩ b m
  have hthr := threshold_le hα0 hα k m hm1
  calc ‖blockDev α k ω q t‖
      ≤ ‖blockDev α k ω q (netPoint α k b m)‖ +
          ‖blockDev α k ω q t - blockDev α k ω q (netPoint α k b m)‖ := by
        have := norm_add_le (blockDev α k ω q (netPoint α k b m))
          (blockDev α k ω q t - blockDev α k ω q (netPoint α k b m))
        rwa [add_sub_cancel] at this
    _ ≤ threshold α k m + 2 := by
        have := hnet.le
        linarith [hlip.trans hlip']
    _ ≤ _ := by linarith

/-! ## Gluing the blocks -/

/-- A good selection in block `k`. -/
def goodChoice (hα : α < 1) (k : ℕ) : Fin (blockCount α k) → ℕ :=
  Classical.choose (exists_blockChoice hα k)

theorem goodChoice_mem (hα : α < 1) (k : ℕ) (i : Fin (blockCount α k)) :
    goodChoice hα k i = 0 ∨ goodChoice hα k i ∈ blockGroup α k i :=
  (Classical.choose_spec (exists_blockChoice hα k)).1 i

theorem goodChoice_net (hα : α < 1) (k : ℕ) (q : {q // q ∈ blockPrimes k}) (b : Bool) (m : ℕ) :
    ‖blockDev α k (goodChoice hα k) q (netPoint α k b m)‖ < threshold α k m :=
  (Classical.choose_spec (exists_blockChoice hα k)).2 q b m

/-- The deleted primes. -/
def deletedPrimes (hα : α < 1) : Set ℕ := {p | ∃ k i, goodChoice hα k i = p ∧ p ≠ 0}

theorem log_eq_of_mem_blockPrimes {k p : ℕ} (hp : p ∈ blockPrimes k) : Nat.log 2 p = k := by
  rw [mem_blockPrimes] at hp
  exact Nat.log_eq_of_pow_le_of_lt_pow hp.2.1 hp.2.2

theorem prime_of_mem_deletedPrimes (hα : α < 1) {p : ℕ} (hp : p ∈ deletedPrimes hα) : p.Prime := by
  obtain ⟨k, i, hki, hp0⟩ := hp
  rcases goodChoice_mem hα k i with h | h
  · exact absurd (hki ▸ h) hp0
  · rw [hki] at h
    exact (mem_blockPrimes.mp (Finset.mem_filter.mp h).1).1

theorem mem_deletedPrimes_iff (hα : α < 1) {k p : ℕ} (hp : p ∈ blockPrimes k) :
    p ∈ deletedPrimes hα ↔ goodChoice hα k ⟨blockIdx α k p, blockIdx_lt hp⟩ = p := by
  constructor
  · rintro ⟨k', i, hki, hp0⟩
    rcases goodChoice_mem hα k' i with h | h
    · exact absurd (hki ▸ h) hp0
    · rw [hki] at h
      obtain ⟨hpb', hidx⟩ := Finset.mem_filter.mp h
      have hk : k' = k := (log_eq_of_mem_blockPrimes hpb').symm.trans (log_eq_of_mem_blockPrimes hp)
      subst hk
      have hi : (⟨blockIdx α k' p, blockIdx_lt hp⟩ : Fin (blockCount α k')) = i := Fin.ext hidx
      rw [hi]; exact hki
  · intro h
    exact ⟨k, _, h, (mem_blockPrimes.mp hp).1.ne_zero⟩

/-- The block deviation of the good selection as a sum over the block primes. -/
theorem blockDev_goodChoice (hα : α < 1) (k : ℕ) (x t : ℝ) :
    blockDev α k (goodChoice hα k) x t = ∑ p ∈ blockPrimes k,
      ((deletedPrimes hα).indicator (fun _ => (1 : ℂ)) p - (delWeight α p : ℂ)) * testFn x t p := by
  classical
  set g : ℕ → Fin (blockCount α k) := fun p =>
    if h : p ∈ blockPrimes k then ⟨blockIdx α k p, blockIdx_lt h⟩ else ⟨0, blockCount_pos α k⟩
  have hgroup : ∀ i, blockGroup α k i = (blockPrimes k).filter fun p => g p = i := by
    intro i
    unfold blockGroup
    refine Finset.filter_congr fun p hp => ?_
    simp only [g, dif_pos hp, Fin.ext_iff]
  unfold blockDev groupDev
  simp_rw [hgroup]
  rw [← Finset.sum_fiberwise_of_maps_to (s := blockPrimes k) (t := Finset.univ) (g := g)
    (fun _ _ => Finset.mem_univ _)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hpb, hgi⟩ := Finset.mem_filter.mp hp
  have hgi' : (⟨blockIdx α k p, blockIdx_lt hpb⟩ : Fin (blockCount α k)) = i := by
    rw [← hgi]; simp only [g, dif_pos hpb]
  congr 1
  rw [Set.indicator_apply]
  by_cases hdel : p ∈ deletedPrimes hα
  · rw [if_pos hdel, if_pos (by rw [← hgi']; exact (mem_deletedPrimes_iff hα hpb).mp hdel)]
  · rw [if_neg hdel, if_neg fun h => hdel ((mem_deletedPrimes_iff hα hpb).mpr (by rw [hgi']; exact h))]

/-- **The deviation up to `x` is the sum of the block deviations.** -/
theorem sum_primes_eq_sum_blockDev (hα : α < 1) {x : ℝ} (hx : 1 ≤ x) (t : ℝ) :
    ∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
      ((deletedPrimes hα).indicator (fun _ => (1 : ℂ)) p - (delWeight α p : ℂ)) *
        (p : ℂ) ^ (-((t : ℂ) * I)) =
      ∑ k ∈ Finset.range (Nat.log 2 ⌊x⌋₊ + 1), blockDev α k (goodChoice hα k) x t := by
  classical
  set K := Nat.log 2 ⌊x⌋₊ with hK
  set f : ℕ → ℂ := fun p =>
    ((deletedPrimes hα).indicator (fun _ => (1 : ℂ)) p - (delWeight α p : ℂ)) * testFn x t p
  set T := (Finset.Iio (2 ^ (K + 1))).filter Nat.Prime with hT
  have hx0 : 0 ≤ x := by linarith
  simp_rw [blockDev_goodChoice hα]
  -- blocks partition the primes below `2^{K+1}`
  have hfib : ∑ k ∈ Finset.range (K + 1), ∑ p ∈ blockPrimes k, f p = ∑ p ∈ T, f p := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := T) (t := Finset.range (K + 1)) (g := Nat.log 2)
      (fun p hp => by
        rw [Finset.mem_range]
        have hp' := Finset.mem_filter.mp hp
        exact Nat.lt_succ_of_le (Nat.le_of_lt_succ
          (Nat.log_lt_of_lt_pow hp'.2.ne_zero (Finset.mem_Iio.mp hp'.1))))]
    refine Finset.sum_congr rfl fun k hk => Finset.sum_congr ?_ fun _ _ => rfl
    ext p
    simp only [Finset.mem_filter, Finset.mem_Iio, mem_blockPrimes, hT]
    have hk' : k < K + 1 := Finset.mem_range.mp hk
    constructor
    · rintro ⟨hp, h2k, hlt⟩
      refine ⟨⟨lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hk'), hp⟩, ?_⟩
      exact Nat.log_eq_of_pow_le_of_lt_pow h2k hlt
    · rintro ⟨⟨_, hp⟩, hlog⟩
      refine ⟨hp, ?_, ?_⟩
      · rw [← hlog]; exact Nat.pow_log_le_self 2 hp.ne_zero
      · rw [← hlog]; exact Nat.lt_pow_succ_log_self (by norm_num) p
  rw [hfib]
  have hsub : (Finset.Iic ⌊x⌋₊).filter Nat.Prime ⊆ T := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    refine Finset.mem_filter.mpr ⟨Finset.mem_Iio.mpr ?_, hp2⟩
    exact lt_of_le_of_lt (Finset.mem_Iic.mp hp1) (Nat.lt_pow_succ_log_self (by norm_num) _)
  rw [← Finset.sum_subset hsub fun p hpT hpnot => ?_]
  · refine Finset.sum_congr rfl fun p hp => ?_
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    simp only [f, testFn]
    rw [if_pos ⟨hp2.pos, (Nat.cast_le.mpr (Finset.mem_Iic.mp hp1)).trans (Nat.floor_le hx0)⟩]
  · have hpx : x < p := by
      have hnot : ¬ p ≤ ⌊x⌋₊ := fun h =>
        hpnot (Finset.mem_filter.mpr ⟨Finset.mem_Iic.mpr h, (Finset.mem_filter.mp hpT).2⟩)
      exact (Nat.lt_floor_add_one x).trans_le (by exact_mod_cast not_le.mp hnot)
    simp only [f, testFn]
    rw [if_neg fun h => absurd h.2 (not_le.mpr hpx), mul_zero]

/-- **Square-root discrepancy of the deleted primes at every frequency.** -/
theorem exists_deletedPrimes (hα0 : 0 < α) (hα : α < 1) :
    ∃ S : Set ℕ, (∀ p ∈ S, p.Prime) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x → ∀ t : ℝ,
      ‖∑ p ∈ (Finset.Iic ⌊x⌋₊).filter Nat.Prime,
        (S.indicator (fun _ => (1 : ℂ)) p - (delWeight α p : ℂ)) * (p : ℂ) ^ (-((t : ℂ) * I))‖ ≤
        C * x ^ (α / 2) * (Real.log x + 1) * Real.sqrt (Real.log (|t| + 2)) := by
  set r : ℝ := (2 : ℝ) ^ (α / 2) with hr
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) (by linarith)
  have hr0 : 0 < r - 1 := by linarith
  refine ⟨deletedPrimes hα, fun p hp => prime_of_mem_deletedPrimes hα hp,
    52 * (r / (r - 1)) + 6, by positivity, fun x hx t => ?_⟩
  set K := Nat.log 2 ⌊x⌋₊ with hK
  set L := Real.log (|t| + 2) with hL
  have hx0 : 0 < x := by linarith
  have hL2 : Real.log 2 ≤ L := Real.log_le_log (by norm_num) (by linarith [abs_nonneg t])
  have hlog2 := Real.log_two_gt_d9
  have hsL : 4 / 5 ≤ Real.sqrt L := by
    rw [Real.le_sqrt (by norm_num) (by linarith)]; nlinarith
  have hxα : 1 ≤ x ^ (α / 2) := Real.one_le_rpow hx (by linarith)
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  -- `2^K ≤ x`
  have h2K : (2 : ℝ) ^ K ≤ x := by
    have h1 : 2 ^ K ≤ ⌊x⌋₊ := Nat.pow_log_le_self 2 (Nat.floor_pos.mpr hx).ne'
    calc (2 : ℝ) ^ K ≤ (⌊x⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ x := Nat.floor_le hx0.le
  have hK1 : (K : ℝ) + 1 ≤ 2 * (Real.log x + 1) := by
    have h := Real.log_le_log (by positivity) h2K
    rw [Real.log_pow] at h
    nlinarith
  have hrK : r ^ K ≤ x ^ (α / 2) := by
    rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), mul_comm,
      Real.rpow_mul (by norm_num)]
    exact Real.rpow_le_rpow (by positivity) (by rwa [Real.rpow_natCast]) (by linarith)
  have hgeom : ∑ k ∈ Finset.range (K + 1), r ^ k ≤ r / (r - 1) * x ^ (α / 2) := by
    rw [geom_sum_eq hr1.ne', div_le_iff₀ (by linarith)]
    have hrK' : r ^ (K + 1) = r * r ^ K := by rw [pow_succ]; ring
    have : r / (r - 1) * x ^ (α / 2) * (r - 1) = r * x ^ (α / 2) := by
      field_simp
    rw [this, hrK']
    nlinarith [pow_pos (show (0:ℝ) < r by linarith) K]
  have hblock : ∀ k ∈ Finset.range (K + 1), ‖blockDev α k (goodChoice hα k) x t‖ ≤
      26 * r ^ k * Real.sqrt ((K : ℝ) + 1) * Real.sqrt L + 2 := by
    intro k hk
    have hkK : (k : ℝ) + 1 ≤ (K : ℝ) + 1 := by
      have h := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have : (k : ℝ) ≤ K := by exact_mod_cast h
      linarith
    have hb := norm_blockDev_le hα0 hα k (goodChoice_net hα k) x t
    have hrk : (2 : ℝ) ^ ((k : ℝ) * α / 2) = r ^ k := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]; congr 1; ring
    rw [hrk] at hb
    have hs : Real.sqrt ((k : ℝ) + 1) ≤ Real.sqrt ((K : ℝ) + 1) := Real.sqrt_le_sqrt hkK
    calc _ ≤ 26 * r ^ k * Real.sqrt ((k : ℝ) + 1) * Real.sqrt L + 2 := hb
      _ ≤ _ := by gcongr
  rw [sum_primes_eq_sum_blockDev hα hx t]
  have hsK : Real.sqrt ((K : ℝ) + 1) ≤ (K : ℝ) + 1 := by
    rw [Real.sqrt_le_left (by positivity)]; nlinarith [(Nat.cast_nonneg K : (0:ℝ) ≤ K)]
  calc ‖∑ k ∈ Finset.range (K + 1), blockDev α k (goodChoice hα k) x t‖
      ≤ ∑ k ∈ Finset.range (K + 1), (26 * r ^ k * Real.sqrt ((K : ℝ) + 1) * Real.sqrt L + 2) :=
        (norm_sum_le _ _).trans (Finset.sum_le_sum hblock)
    _ = 26 * Real.sqrt ((K : ℝ) + 1) * Real.sqrt L * ∑ k ∈ Finset.range (K + 1), r ^ k +
          2 * ((K : ℝ) + 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
          Finset.mul_sum]
        push_cast
        congr 1
        · exact Finset.sum_congr rfl fun k _ => by ring
        · ring
    _ ≤ 26 * (2 * (Real.log x + 1)) * Real.sqrt L * (r / (r - 1) * x ^ (α / 2)) +
          2 * (2 * (Real.log x + 1)) := by
        gcongr
        exact hsK.trans hK1
    _ ≤ (52 * (r / (r - 1)) + 6) * x ^ (α / 2) * (Real.log x + 1) * Real.sqrt L := by
        have hq : 0 ≤ r / (r - 1) := div_nonneg (by linarith) (by linarith)
        have h4 : 4 * (Real.log x + 1) ≤ 6 * x ^ (α / 2) * (Real.log x + 1) * Real.sqrt L := by
          have : (1 : ℝ) ≤ x ^ (α / 2) * Real.sqrt L * (5 / 4) := by nlinarith
          nlinarith
        nlinarith

end RHTower.BeurlingDeletion


