import GaloisForLFunctions.HTGeometry.QBinomialTheorem
import GaloisForLFunctions.HTGeometry.AbelianZetaGas.Core

/-!
# Two-sided bounds on the vacuum weight

The Euler weight of the empty configuration is `w_{q,0} = (q;q)_∞`.  It is at most `1 − q`, because
the depth-one factor already contributes that much, and it exceeds `1 − q/(1−q)` by the Weierstrass
product inequality.  Both bounds are what the symmetrization argument of the condensed phase needs:
the first says an occupied copy has probability at least `q`, the second that the empty copy has
probability more than `1/2` once `q < 1/3`.
-/

namespace GaloisForLFunctions.HTGeometry

/-- **The Weierstrass product inequality.** -/
theorem one_sub_sum_le_prod_one_sub {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (h0 : ∀ i ∈ s, 0 ≤ a i) (h1 : ∀ i ∈ s, a i ≤ 1) :
    1 - ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 - a i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    have h0' : ∀ j ∈ s, 0 ≤ a j := fun j hj => h0 j (Finset.mem_insert_of_mem hj)
    have h1' : ∀ j ∈ s, a j ≤ 1 := fun j hj => h1 j (Finset.mem_insert_of_mem hj)
    have hai0 : 0 ≤ a i := h0 i (Finset.mem_insert_self i s)
    have hai1 : a i ≤ 1 := h1 i (Finset.mem_insert_self i s)
    have hprodnn : 0 ≤ ∏ j ∈ s, (1 - a j) :=
      Finset.prod_nonneg fun j hj => by linarith [h1' j hj]
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    rcases le_or_gt (1 - ∑ j ∈ s, a j) 0 with hneg | hpos
    · have : 0 ≤ (1 - a i) * ∏ j ∈ s, (1 - a j) := by
        have : 0 ≤ 1 - a i := by linarith
        positivity
      linarith
    · have hSnn : 0 ≤ ∑ j ∈ s, a j := Finset.sum_nonneg h0'
      have hstep := ih h0' h1'
      have hmul : (1 - a i) * (1 - ∑ j ∈ s, a j) ≤ (1 - a i) * ∏ j ∈ s, (1 - a j) :=
        mul_le_mul_of_nonneg_left hstep (by linarith)
      nlinarith [hmul, mul_nonneg hai0 hSnn]

/-- **The vacuum weight exceeds `1 − q/(1−q)`.** -/
theorem realQFactorialInf_ge (q : RealEulerNome) :
    1 - q.val / (1 - q.val) ≤ realQFactorialInf q := by
  have hq1 : (0 : ℝ) < 1 - q.val := by
    have := q.lt_one
    linarith
  have hgeom : HasSum (fun j : ℕ => q.val ^ (j + 1)) (q.val / (1 - q.val)) := by
    have h := hasSum_geometric_of_lt_one q.pos.le q.lt_one
    have hshift := (hasSum_nat_add_iff' (f := fun j : ℕ => q.val ^ j) 1).mpr h
    simp only [Finset.range_one, Finset.sum_singleton, pow_zero] at hshift
    have hval : (1 - q.val)⁻¹ - 1 = q.val / (1 - q.val) := by
      field_simp
      ring
    rwa [hval] at hshift
  refine ge_of_tendsto (realQFactorial_tendsto q) ?_
  filter_upwards with n
  have hbound : 1 - ∑ j ∈ Finset.range n, q.val ^ (j + 1) ≤ realQFactorial q n := by
    rw [realQFactorial]
    refine one_sub_sum_le_prod_one_sub _ _ (fun j _ => pow_nonneg q.pos.le _) (fun j _ => ?_)
    exact (pow_lt_one₀ q.pos.le q.lt_one (by omega)).le
  have hpartial : ∑ j ∈ Finset.range n, q.val ^ (j + 1) ≤ q.val / (1 - q.val) :=
    sum_le_hasSum _ (fun j _ => pow_nonneg q.pos.le _) hgeom
  linarith

/-- **The vacuum weight is at most `1 − q`.** -/
theorem realQFactorialInf_le_one_sub (q : RealEulerNome) :
    realQFactorialInf q ≤ 1 - q.val := by
  have h := realQFactorialInf_le q 1
  rwa [realQFactorial, Finset.prod_range_one, pow_one] at h

/-- **Below `q = 1/3` the vacuum weight exceeds one half.** -/
theorem half_lt_realQFactorialInf {q : RealEulerNome} (hq : q.val < 1 / 3) :
    1 / 2 < realQFactorialInf q := by
  have hq1 : (0 : ℝ) < 1 - q.val := by
    have := q.lt_one
    linarith
  have hkey : q.val / (1 - q.val) < 1 / 2 := by
    rw [div_lt_div_iff₀ hq1 (by norm_num)]
    linarith
  have := realQFactorialInf_ge q
  linarith

/-- **The symmetrization bound.**  Below `q = 1/3` the probability that one copy is empty and the
other occupied is at least `q/2`. -/
theorem half_mul_le_vacuum_mul_occupied {q : RealEulerNome} (hq : q.val < 1 / 3) :
    q.val / 2 ≤ realQFactorialInf q * (1 - realQFactorialInf q) := by
  have hhalf := half_lt_realQFactorialInf hq
  have hocc : q.val ≤ 1 - realQFactorialInf q := by
    have := realQFactorialInf_le_one_sub q
    linarith
  have hqpos : 0 < q.val := q.pos
  nlinarith

/-! ## Divergence of the symmetrization probabilities -/

/-- The nome of a prime at temperature `σ`. -/
noncomputable def primeNome {σ : ℝ} (hσ : 0 < σ) (p : Nat.Primes) : RealEulerNome where
  val := (p : ℝ) ^ (-σ)
  pos := Real.rpow_pos_of_pos (by exact_mod_cast p.2.pos) _
  lt_one :=
    Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.2.one_lt) (neg_neg_of_pos hσ)

@[simp] theorem primeNome_val {σ : ℝ} (hσ : 0 < σ) (p : Nat.Primes) :
    (primeNome hσ p).val = (p : ℝ) ^ (-σ) := rfl

theorem primeNome_lt_third {σ : ℝ} (hσ : 0 < σ) (hhalf : 1 / 2 < σ) {p : Nat.Primes}
    (hp : 11 ≤ (p : ℕ)) : (primeNome hσ p).val < 1 / 3 := by
  have hpR : (11 : ℝ) ≤ (p : ℕ) := by exact_mod_cast hp
  have h11 : (3 : ℝ) < (11 : ℝ) ^ σ := by
    have hbase : (1 : ℝ) < 11 := by norm_num
    have hmono : (11 : ℝ) ^ ((1 : ℝ) / 2) < (11 : ℝ) ^ σ :=
      Real.rpow_lt_rpow_of_exponent_lt hbase hhalf
    have hhalfval : (3 : ℝ) < (11 : ℝ) ^ ((1 : ℝ) / 2) := by
      have h9 : (9 : ℝ) < 11 := by norm_num
      have := Real.rpow_lt_rpow (by norm_num : (0:ℝ) ≤ 9) h9 (by norm_num : (0:ℝ) < 1/2)
      rw [show (9 : ℝ) = 3 ^ (2 : ℕ) by norm_num, ← Real.rpow_natCast (3 : ℝ) 2,
        ← Real.rpow_mul (by norm_num : (0:ℝ) ≤ 3)] at this
      norm_num at this
      exact this
    linarith
  have hpow : (11 : ℝ) ^ σ ≤ ((p : ℕ) : ℝ) ^ σ :=
    Real.rpow_le_rpow (by norm_num) hpR hσ.le
  have hppos : (0 : ℝ) < ((p : ℕ) : ℝ) ^ σ := by
    refine Real.rpow_pos_of_pos ?_ _
    exact_mod_cast p.2.pos
  have hgt : (3 : ℝ) < ((p : ℕ) : ℝ) ^ σ := lt_of_lt_of_le h11 hpow
  rw [primeNome_val, Real.rpow_neg (by positivity)]
  rw [inv_lt_comm₀ hppos (by norm_num)]
  linarith

/-- **The symmetrization probabilities of the condensed phase are not summable.**  This is the
Borel–Cantelli input of Theorem 1.1: below the depth-one wall, infinitely many primes see one copy
empty and the other occupied. -/
theorem not_summable_symmetrization {σ : ℝ} (hσ : 0 < σ) (hhalf : 1 / 2 < σ) (hone : σ ≤ 1) :
    ¬ Summable (fun p : Nat.Primes =>
      realQFactorialInf (primeNome hσ p) * (1 - realQFactorialInf (primeNome hσ p))) := by
  classical
  intro hsum
  set f : Nat.Primes → ℝ := fun p =>
    realQFactorialInf (primeNome hσ p) * (1 - realQFactorialInf (primeNome hσ p)) with hf
  set g : Nat.Primes → ℝ := fun p =>
    if 11 ≤ (p : ℕ) then (1 / 2) * ((p : ℕ) : ℝ) ^ (-σ) else 0 with hg
  have hgnn : ∀ p, 0 ≤ g p := by
    intro p
    simp only [hg]
    split
    · positivity
    · exact le_rfl
  have hgle : ∀ p, g p ≤ f p := by
    intro p
    simp only [hg, hf]
    split
    · rename_i hp
      have hthird := primeNome_lt_third hσ hhalf hp
      have := half_mul_le_vacuum_mul_occupied hthird
      rw [primeNome_val] at this
      linarith
    · have hw := realQFactorialInf_pos (primeNome hσ p)
      have hw1 := realQFactorialInf_le_one_sub (primeNome hσ p)
      have hq := (primeNome hσ p).pos
      nlinarith
  have hgsum : Summable g := Summable.of_nonneg_of_le hgnn hgle hsum
  have hfinset : {p : Nat.Primes | (p : ℕ) < 11}.Finite := by
    refine Set.Finite.of_finite_image ?_ (Set.injOn_of_injective Nat.Primes.coe_nat_injective)
    refine (Set.finite_Iio 11).subset ?_
    rintro n ⟨p, hp, rfl⟩
    exact hp
  have hhsum : Summable (fun p : Nat.Primes => (1 / 2) * ((p : ℕ) : ℝ) ^ (-σ) - g p) := by
    refine summable_of_ne_finset_zero (s := hfinset.toFinset) ?_
    intro p hp
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_lt] at hp
    simp only [hg, if_pos hp]
    ring
  have hcomb := hgsum.add hhsum
  have hhalfsum : Summable (fun p : Nat.Primes => (1 / 2) * ((p : ℕ) : ℝ) ^ (-σ)) := by
    refine hcomb.congr fun p => ?_
    ring
  have hfinal : Summable (fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-σ)) := by
    have := hhalfsum.mul_left 2
    refine this.congr fun p => ?_
    ring
  exact not_summable_prime_rpow_of_exponent_le_one hσ hone hfinal

end GaloisForLFunctions.HTGeometry
