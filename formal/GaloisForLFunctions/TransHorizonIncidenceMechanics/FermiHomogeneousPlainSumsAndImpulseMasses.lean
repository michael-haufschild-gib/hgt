import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiDyadicAntichainCoordinates

/-!
# Plain-sum homogeneous energies and exact scalar impulse masses

Every positive integer is uniquely `2^k (2j+1)`. Reindexing an absolutely
convergent series over positive integers along this factorization identifies
the reciprocal-square energies

* `P_h = ∑_{n ≥ 1} A(n)^2 / n^2`,
* `Q_h = ∑_{n odd} J(n)^2 / n^2 + ∑_{4 ∣ n, n > 0} J(n)^2 / n^2`

with the odd-ray forms `sieveHomogeneousEnergy` and
`fermiSelectedHomogeneousEnergy`: the dyadic level `k` is normalized by `2^k`
and weighted by the reciprocal square of the odd part.

A single scalar dyadic impulse at level `j` has selected square mass `13/12`
for `j = 0`, `1/3` for `j = 1`, and `4/3` for `j ≥ 2`, against full mass `4/3`.
-/

open scoped BigOperators
open Finset GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false

private theorem two_adic_valuation (k j : ℕ) : (2 ^ k * (2 * j + 1)).factorization 2 = k := by
  rw [Nat.factorization_mul (by positivity) (by omega), Finsupp.add_apply, Nat.factorization_pow,
    Finsupp.smul_apply, Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by omega)]
  simp

private theorem two_pow_mul_odd_injective :
    Function.Injective (fun p : ℕ × ℕ => 2 ^ p.1 * (2 * p.2 + 1)) := by
  rintro ⟨a, b⟩ ⟨c, d⟩ h
  dsimp only at h
  have hac : a = c := by
    have := congrArg (fun n : ℕ => n.factorization 2) h
    simpa only [two_adic_valuation] using this
  subst hac
  have hbd := Nat.eq_of_mul_eq_mul_left (by positivity) h
  exact Prod.ext rfl (by omega)

private theorem two_pow_mul_odd_bijective :
    Function.Bijective (fun p : ℕ × ℕ => 2 ^ p.1 * (2 * p.2 + 1) - 1) := by
  constructor
  · intro p q h
    apply two_pow_mul_odd_injective
    have hp : 0 < 2 ^ p.1 * (2 * p.2 + 1) := by positivity
    have hq : 0 < 2 ^ q.1 * (2 * q.2 + 1) := by positivity
    dsimp only at h ⊢
    omega
  · intro m
    obtain ⟨k, u, hu, he⟩ := Nat.exists_eq_two_pow_mul_odd (n := m + 1) (by omega)
    obtain ⟨j, rfl⟩ := hu
    exact ⟨(k, j), by dsimp only; omega⟩

/-- Unique dyadic factorization reindexes a convergent series over positive integers. -/
theorem tsum_pos_eq_tsum_two_pow_mul_odd (g : ℕ → ℝ) (hg : Summable (fun n : ℕ => g (n + 1))) :
    Summable (fun p : ℕ × ℕ => g (2 ^ p.1 * (2 * p.2 + 1))) ∧
      (∑' n : ℕ, g (n + 1)) = ∑' k : ℕ, ∑' j : ℕ, g (2 ^ k * (2 * j + 1)) := by
  let e := Equiv.ofBijective _ two_pow_mul_odd_bijective
  have hidx (p : ℕ × ℕ) : e p + 1 = 2 ^ p.1 * (2 * p.2 + 1) := by
    have : 0 < 2 ^ p.1 * (2 * p.2 + 1) := by positivity
    change 2 ^ p.1 * (2 * p.2 + 1) - 1 + 1 = _
    omega
  have hs : Summable (fun p : ℕ × ℕ => g (2 ^ p.1 * (2 * p.2 + 1))) :=
    (hg.comp_injective e.injective).congr (fun p => by simp only [Function.comp_apply, hidx])
  refine ⟨hs, ?_⟩
  calc
    _ = ∑' p : ℕ × ℕ, g (e p + 1) := (e.tsum_eq (fun n => g (n + 1))).symm
    _ = ∑' p : ℕ × ℕ, g (2 ^ p.1 * (2 * p.2 + 1)) := by simp only [hidx]
    _ = _ := hs.tsum_prod

private theorem summable_shift_inv_sq : Summable (fun n : ℕ => 1 / (((n + 1 : ℕ) : ℝ))^2) :=
  hasSum_zeta_two.summable.comp_injective (fun a b h => by simpa using h)

private theorem summable_bounded_sq (x : ℕ → ℝ) (B : ℝ) (hx : ∀ n, |x n| ≤ B) :
    Summable (fun n : ℕ => (x (n + 1))^2 / (((n + 1 : ℕ) : ℝ))^2) := by
  apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_shift_inv_sq.mul_left (B^2))
  rw [mul_one_div]
  apply div_le_div_of_nonneg_right _ (by positivity)
  have := hx (n + 1)
  nlinarith [abs_nonneg (x (n + 1)), sq_abs (x (n + 1))]

private theorem normalized_sq (x : ℝ) (k b : ℕ) :
    x^2 / (((2 ^ k * b : ℕ) : ℝ))^2 = (x / (2 : ℝ)^k)^2 / ((b : ℕ) : ℝ)^2 := by
  push_cast
  rw [div_pow, mul_pow, div_div]

/-- The plain reciprocal-square full energy equals the odd-ray homogeneous energy. -/
theorem sieveHomogeneousEnergy_eq_tsum (N : ℕ) (c : ℕ → ℝ) :
    sieveHomogeneousEnergy N c =
      ∑' n : ℕ, (sieveSeq N c (n + 1))^2 / (((n + 1 : ℕ) : ℝ))^2 := by
  let g : ℕ → ℝ := fun n => (sieveSeq N c n)^2 / ((n : ℝ))^2
  have hg : Summable (fun n : ℕ => g (n + 1)) := by
    simpa only [g, Nat.cast_add, Nat.cast_one] using
      summable_bounded_sq (sieveSeq N c) _ (abs_sieveSeq_le_sum_abs N c)
  obtain ⟨hs, he⟩ := tsum_pos_eq_tsum_two_pow_mul_odd g hg
  have hrow := hs.prod
  change _ = ∑' n : ℕ, g (n + 1)
  rw [he, hrow.tsum_eq_zero_add, sieveHomogeneousEnergy,
    (sieve_fermi_homogeneous_summable N c).2.1.tsum_prod]
  congr 1
  · apply tsum_congr
    intro j
    simp only [g, pow_zero, one_mul]
  · apply tsum_congr
    intro k
    apply tsum_congr
    intro j
    dsimp only
    rw [fermiNormalizedDyadicSieve]
    exact (normalized_sq (sieveSeq N c (2 ^ (k + 1) * (2 * j + 1))) (k + 1) (2 * j + 1)).symm

/-- The plain reciprocal-square selected energy equals its odd-ray homogeneous form. -/
theorem fermiSelectedHomogeneousEnergy_eq_tsum (N : ℕ) (c : ℕ → ℝ) :
    fermiSelectedHomogeneousEnergy N c =
      (∑' m : ℕ, (fermiBoundaryJump N c (2 * m + 1))^2 / (((2 * m + 1 : ℕ) : ℝ))^2) +
        ∑' m : ℕ, (fermiBoundaryJump N c (4 * m + 4))^2 / (((4 * m + 4 : ℕ) : ℝ))^2 := by
  let h : ℕ → ℝ := fun n => (fermiBoundaryJump N c (4 * n))^2 / (((4 * n : ℕ) : ℝ))^2
  set M := ∑ d ∈ Finset.Icc 1 N, |c d|
  have hJ (m : ℕ) : |fermiBoundaryJump N c (4 * (m + 1))| ≤ 3 * M := by
    rw [show 4 * (m + 1) = 2 * (2 * m + 1) + 2 by ring, fermiBoundaryJump_even]
    have h1 := abs_sieveSeq_le_sum_abs N c (2 * m + 1 + 1)
    have h2 := abs_sieveSeq_le_sum_abs N c (2 * (2 * m + 1) + 2)
    calc
      _ ≤ |2 * sieveSeq N c (2 * m + 1 + 1)| + |sieveSeq N c (2 * (2 * m + 1) + 2)| :=
        abs_sub _ _
      _ ≤ 3 * M := by rw [abs_mul]; norm_num; linarith
  have hh : Summable (fun n : ℕ => h (n + 1)) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      (summable_shift_inv_sq.mul_left ((3 * M)^2))
    simp only [h]
    rw [mul_one_div]
    have hJn := hJ n
    have hsq : (fermiBoundaryJump N c (4 * (n + 1)))^2 ≤ (3 * M)^2 := by
      nlinarith [abs_nonneg (fermiBoundaryJump N c (4 * (n + 1))),
        sq_abs (fermiBoundaryJump N c (4 * (n + 1)))]
    have hden : (((n + 1 : ℕ) : ℝ))^2 ≤ (((4 * (n + 1) : ℕ) : ℝ))^2 := by
      push_cast
      nlinarith
    calc
      _ ≤ (3 * M)^2 / (((4 * (n + 1) : ℕ) : ℝ))^2 :=
        div_le_div_of_nonneg_right hsq (by positivity)
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity) hden
  obtain ⟨hs, he⟩ := tsum_pos_eq_tsum_two_pow_mul_odd h hh
  rw [fermiSelectedHomogeneousEnergy, (sieve_fermi_homogeneous_summable N c).2.2.tsum_prod]
  congr 1
  · apply tsum_congr
    intro m
    rw [fermiBoundaryJump_odd, neg_sq]
  · have hidx : (fun m : ℕ => (fermiBoundaryJump N c (4 * m + 4))^2 /
        (((4 * m + 4 : ℕ) : ℝ))^2) = fun m => h (m + 1) := by
      funext m
      simp only [h, show 4 * (m + 1) = 4 * m + 4 by ring]
    rw [hidx, he]
    apply tsum_congr
    intro k
    apply tsum_congr
    intro j
    dsimp only
    have h4 : 4 * (2 ^ k * (2 * j + 1)) = 2 ^ (k + 1 + 1) * (2 * j + 1) := by ring
    show _ = (fermiBoundaryJump N c (4 * (2 ^ k * (2 * j + 1))))^2 /
      (((4 * (2 ^ k * (2 * j + 1)) : ℕ) : ℝ))^2
    rw [h4, fermiNormalizedDyadicJump]
    exact (normalized_sq (fermiBoundaryJump N c (2 ^ (k + 1 + 1) * (2 * j + 1))) (k + 1 + 1)
      (2 * j + 1)).symm

/-- Plain-sum homogeneous comparison `P_h/2 ≤ P ≤ P_h`. -/
theorem sieveTotalPronicEnergy_plainSum_bounds (N : ℕ) (c : ℕ → ℝ) :
    (∑' n : ℕ, (sieveSeq N c (n + 1))^2 / (((n + 1 : ℕ) : ℝ))^2) / 2 ≤
        sieveTotalPronicEnergy N c ∧
      sieveTotalPronicEnergy N c ≤ ∑' n : ℕ, (sieveSeq N c (n + 1))^2 / (((n + 1 : ℕ) : ℝ))^2 := by
  rw [← sieveHomogeneousEnergy_eq_tsum]
  exact sieveHomogeneousEnergy_pronic_bounds N c

/-- Plain-sum homogeneous comparison `Q_h/2 ≤ Q ≤ Q_h`. -/
theorem fermiSelectedTotalPronicEnergy_plainSum_bounds (N : ℕ) (c : ℕ → ℝ) :
    ((∑' m : ℕ, (fermiBoundaryJump N c (2 * m + 1))^2 / (((2 * m + 1 : ℕ) : ℝ))^2) +
        ∑' m : ℕ, (fermiBoundaryJump N c (4 * m + 4))^2 / (((4 * m + 4 : ℕ) : ℝ))^2) / 2 ≤
        fermiSelectedTotalPronicEnergy N c ∧
      fermiSelectedTotalPronicEnergy N c ≤
        (∑' m : ℕ, (fermiBoundaryJump N c (2 * m + 1))^2 / (((2 * m + 1 : ℕ) : ℝ))^2) +
          ∑' m : ℕ, (fermiBoundaryJump N c (4 * m + 4))^2 / (((4 * m + 4 : ℕ) : ℝ))^2 := by
  rw [← fermiSelectedHomogeneousEnergy_eq_tsum]
  exact fermiSelectedHomogeneousEnergy_pronic_bounds N c

private theorem impulse_value (j r : ℕ) : fermiDyadicImpulse j (r + j) = (1 / 2 : ℝ)^r := by
  unfold fermiDyadicImpulse
  rw [if_pos (by omega), pow_add, one_div_pow]
  field_simp

private theorem impulse_step_hasSum (j : ℕ) :
    HasSum (fun r : ℕ => (fermiDyadicImpulse j (r + j) - fermiDyadicImpulse j (r + 1 + j))^2)
      (1 / 3 : ℝ) := by
  have hg := (hasSum_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)).mul_left
    (1 / 4 : ℝ)
  have hf : (fun r : ℕ => (fermiDyadicImpulse j (r + j) - fermiDyadicImpulse j (r + 1 + j))^2) =
      fun r : ℕ => (1 / 4 : ℝ) * (1 / 4 : ℝ)^r := by
    funext r
    rw [impulse_value, impulse_value, pow_succ, show (1 / 4 : ℝ) = (1 / 2)^2 by norm_num, ← pow_mul]
    ring
  rw [hf, show (1 / 3 : ℝ) = 1 / 4 * (1 - 1 / 4)⁻¹ by norm_num]
  exact hg

/-- Exact selected square mass of one scalar dyadic impulse at each depth. -/
theorem fermiDyadicImpulse_selected_mass (j : ℕ) :
    (fermiDyadicImpulse j 0)^2 +
        ∑' k : ℕ, (fermiDyadicImpulse j (k + 1) - fermiDyadicImpulse j (k + 2))^2 =
      if j = 0 then 13 / 12 else if j = 1 then 1 / 3 else 4 / 3 := by
  have hs := (fermiDyadicImpulse_selected_lower j).1
  rcases j with _ | _ | j
  · have h := impulse_step_hasSum 0
    have ht : HasSum (fun k : ℕ => (fermiDyadicImpulse 0 (k + 1) - fermiDyadicImpulse 0 (k + 2))^2)
        (1 / 12 : ℝ) := by
      have h2 := (hasSum_nat_add_iff' 1).mpr h
      simp only [Finset.sum_range_one, add_zero, zero_add, impulse_value 0 0, impulse_value 0 1]
        at h2
      norm_num at h2
      simpa [Nat.add_assoc] using h2
    rw [ht.tsum_eq]
    norm_num [fermiDyadicImpulse]
  · have ht : HasSum (fun k : ℕ => (fermiDyadicImpulse 1 (k + 1) - fermiDyadicImpulse 1 (k + 2))^2)
        (1 / 3 : ℝ) := by
      simpa [Nat.add_assoc] using impulse_step_hasSum 1
    rw [ht.tsum_eq]
    norm_num [fermiDyadicImpulse]
  · have hsplit := hs.sum_add_tsum_nat_add (j + 1)
    have htail : HasSum (fun r : ℕ => (fermiDyadicImpulse (j + 2) (r + (j + 1) + 1) -
        fermiDyadicImpulse (j + 2) (r + (j + 1) + 2))^2) (1 / 3 : ℝ) := by
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using impulse_step_hasSum (j + 2)
    have hfin : ∑ k ∈ Finset.range (j + 1),
        (fermiDyadicImpulse (j + 2) (k + 1) - fermiDyadicImpulse (j + 2) (k + 2))^2 = 1 := by
      rw [Finset.sum_eq_single j]
      · simp [fermiDyadicImpulse]
      · intro k hk hkj
        have := Finset.mem_range.mp hk
        simp [fermiDyadicImpulse, show ¬ j + 2 ≤ k + 1 by omega, show ¬ j + 2 ≤ k + 2 by omega]
      · intro h
        exact (h (Finset.mem_range.mpr (by omega))).elim
    rw [← hsplit, htail.tsum_eq, hfin]
    norm_num [fermiDyadicImpulse]

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
