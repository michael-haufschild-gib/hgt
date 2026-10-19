import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiOddDivisorGramAndFrameBounds
import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiHomogeneousEnergyAndPronicComparison

/-!
# Native dyadic-antichain coordinates

A finite set of odd indices with one assigned dyadic depth per index produces a
literal coefficient packet. Its native normalized sieve rays are exact packets
in the odd-divisor profiles, and its selected jumps are their consecutive
coordinate differences. Every scalar impulse has full homogeneous mass `4/3`
and selected mass at least `1/3`, independently of its assigned depth.

These are supporting identities for the antichain prime-capacity classification;
they do not by themselves assert its uniform native energy bound.
-/

open scoped BigOperators
open Finset GaloisForLFunctions.BezoutValuationIncidence


namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false

private theorem dyadic_odd_dvd_iff (j k : ℕ) {d b : ℕ} (hd : Odd d) (hb : Odd b) :
    2^j*d ∣ 2^k*b ↔ j ≤ k ∧ d ∣ b := by
  constructor
  · intro h
    have hpow : (2 : ℕ)^j ∣ 2^k*b := dvd_trans (dvd_mul_right _ _) h
    have hdvd : d ∣ 2^k*b := dvd_trans (dvd_mul_left _ _) h
    exact ⟨(Nat.pow_dvd_pow_iff_le_right (by decide : 1 < (2 : ℕ))).mp
      ((hb.coprime_two_left.pow_left j).dvd_mul_right.mp hpow),
      (hd.coprime_two_right.pow_right k).dvd_mul_left.mp hdvd⟩
  · rintro ⟨hjk, hdb⟩
    exact Nat.mul_dvd_mul (pow_dvd_pow 2 hjk) hdb

/-- Literal coefficients for one admitted dyadic impulse at each odd index. -/
def fermiDyadicAntichainCoefficient (S : Finset ℕ) (j : S → ℕ) (a : S → ℝ)
    (n : ℕ) : ℝ :=
  ∑ d : S, if n = 2^(j d)*(d : ℕ) then (2 : ℝ)^(j d)*(d : ℝ)*a d else 0

/-- State of one dyadic impulse in normalized coordinates. -/
def fermiDyadicImpulse (j k : ℕ) : ℝ :=
  if j ≤ k then (2 : ℝ)^j/(2 : ℝ)^k else 0

private theorem antichain_sieve (N : ℕ) (S : Finset ℕ) (j : S → ℕ) (a : S → ℝ)
    (hS : ∀ d ∈ S, Odd d) (hN : ∀ d : S, 2^(j d)*(d : ℕ) ≤ N) (n : ℕ) :
    sieveSeq N (fermiDyadicAntichainCoefficient S j a) n =
      ∑ d : S, if 2^(j d)*(d : ℕ) ∣ n then (2 : ℝ)^(j d)*(d : ℝ)*a d else 0 := by
  unfold sieveSeq fermiDyadicAntichainCoefficient
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  have hdpos : 0 < (d : ℕ) := (hS d d.property).pos
  have hpos : 1 ≤ (2 : ℕ)^(j d)*(d : ℕ) :=
    Nat.succ_le_of_lt (Nat.mul_pos (by positivity) hdpos)
  simp only [Finset.sum_ite_eq', Finset.mem_filter, Finset.mem_Icc, hpos, hN d,
    true_and]

/-- Exact odd-divisor coordinate formula for a native normalized sieve ray. -/
theorem fermiDyadicAntichain_sieve_coordinate (N : ℕ) (S : Finset ℕ)
    (j : S → ℕ) (a : S → ℝ) (hS : ∀ d ∈ S, Odd d)
    (hN : ∀ d : S, 2^(j d)*(d : ℕ) ≤ N) (k m : ℕ) :
    fermiNormalizedDyadicSieve N (fermiDyadicAntichainCoefficient S j a) (2*m+1) k /
      ((2*m+1 : ℕ) : ℝ) =
      fermiOddDivisorPacket S (fun d => fermiDyadicImpulse (j d) k*a d) m := by
  unfold fermiNormalizedDyadicSieve
  rw [antichain_sieve N S j a hS hN, Finset.sum_div, Finset.sum_div]
  unfold fermiOddDivisorPacket
  apply Finset.sum_congr rfl
  intro d _
  simp only [dyadic_odd_dvd_iff _ _ (hS d d.property) (⟨m, by omega⟩ : Odd (2*m+1))]
  unfold fermiDyadicImpulse fermiOddDivisorProfile
  by_cases hj : j d ≤ k <;> by_cases hd : (d : ℕ) ∣ 2*m+1 <;>
    simp [hj, hd, div_eq_mul_inv]
  ring

/-- Selected native jumps are the differences of adjacent odd-divisor coordinates. -/
theorem fermiDyadicAntichain_jump_coordinate (N : ℕ) (S : Finset ℕ)
    (j : S → ℕ) (a : S → ℝ) (hS : ∀ d ∈ S, Odd d)
    (hN : ∀ d : S, 2^(j d)*(d : ℕ) ≤ N) (k m : ℕ) :
    fermiNormalizedDyadicJump N (fermiDyadicAntichainCoefficient S j a) (2*m+1) (k+1) /
      ((2*m+1 : ℕ) : ℝ) =
      fermiOddDivisorPacket S
        (fun d => (fermiDyadicImpulse (j d) (k+1) - fermiDyadicImpulse (j d) (k+2))*a d) m := by
  rw [fermiNormalizedDyadicJump_eq_sub _ _ (by omega : 0 < 2*m+1), sub_div,
    fermiDyadicAntichain_sieve_coordinate N S j a hS hN,
    fermiDyadicAntichain_sieve_coordinate N S j a hS hN]
  unfold fermiOddDivisorPacket
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d _
  ring


private theorem impulse_tail (j k : ℕ) :
    fermiDyadicImpulse j (k+j) = 1/(2 : ℝ)^k := by
  unfold fermiDyadicImpulse
  rw [if_pos (by omega : j ≤ k+j), pow_add]
  field_simp

private theorem half_power_sq (x : ℝ) (k : ℕ) :
    (x/(2 : ℝ)^k)^2 = x^2*(1/4 : ℝ)^k := by
  rw [div_pow, ← pow_mul, Nat.mul_comm k 2, pow_mul, div_pow]
  norm_num
  ring

/-- Every single dyadic impulse has exactly the same full homogeneous mass. -/
theorem fermiDyadicImpulse_square_hasSum (j : ℕ) :
    HasSum (fun k : ℕ => (fermiDyadicImpulse j k)^2) (4/3 : ℝ) := by
  have hg := hasSum_geometric_of_lt_one (r := (1/4 : ℝ)) (by norm_num) (by norm_num)
  have ht : HasSum (fun k : ℕ => (fermiDyadicImpulse j (k+j))^2) (4/3 : ℝ) := by
    simpa only [impulse_tail, half_power_sq, one_pow, one_mul,
      show (1 - 1/4 : ℝ)⁻¹ = 4/3 by norm_num] using hg
  have hz : (∑ k ∈ Finset.range j, (fermiDyadicImpulse j k)^2) = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    simp [fermiDyadicImpulse, show ¬ j ≤ k by have := Finset.mem_range.mp hk; omega]
  simpa only [hz, zero_add] using
    (HasSum.sum_range_add (f := fun k => (fermiDyadicImpulse j k)^2) ht)

/-- A single impulse always pays at least one quarter of its full energy in selected data. -/
theorem fermiDyadicImpulse_selected_lower (j : ℕ) :
    Summable (fun k : ℕ => (fermiDyadicImpulse j (k+1) - fermiDyadicImpulse j (k+2))^2) ∧
      (1/3 : ℝ) ≤ (fermiDyadicImpulse j 0)^2 +
        ∑' k : ℕ, (fermiDyadicImpulse j (k+1) - fermiDyadicImpulse j (k+2))^2 := by
  have hfull := (fermiDyadicImpulse_square_hasSum j).summable
  have h1 : Summable (fun k : ℕ => (fermiDyadicImpulse j (k+1))^2) :=
    hfull.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have h2 : Summable (fun k : ℕ => (fermiDyadicImpulse j (k+2))^2) :=
    hfull.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  have hs : Summable (fun k : ℕ =>
      (fermiDyadicImpulse j (k+1) - fermiDyadicImpulse j (k+2))^2) :=
    Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => by
      nlinarith [sq_nonneg (fermiDyadicImpulse j (k+1) + fermiDyadicImpulse j (k+2))])
      ((h1.mul_left 2).add (h2.mul_left 2))
  refine ⟨hs, ?_⟩
  rcases j with _ | j
  · have h0 : fermiDyadicImpulse 0 0 = 1 := by norm_num [fermiDyadicImpulse]
    rw [h0]
    have ht : 0 ≤ ∑' k : ℕ, (fermiDyadicImpulse 0 (k+1) - fermiDyadicImpulse 0 (k+2))^2 :=
      tsum_nonneg (fun k => sq_nonneg _)
    nlinarith
  rcases j with _ | j
  · have heq (k : ℕ) : fermiDyadicImpulse 1 (k+1) - fermiDyadicImpulse 1 (k+2) =
        (1/2 : ℝ)/(2 : ℝ)^k := by
      rw [impulse_tail 1 k, show k+2 = (k+1)+1 by omega, impulse_tail 1 (k+1), pow_succ]
      field_simp
      ring
    have hg := (hasSum_geometric_of_lt_one (r := (1/4 : ℝ))
      (by norm_num) (by norm_num)).mul_left (1/4 : ℝ)
    have ht : HasSum (fun k : ℕ =>
        (fermiDyadicImpulse 1 (k+1) - fermiDyadicImpulse 1 (k+2))^2) (1/3 : ℝ) := by
      have hf : (fun k : ℕ =>
          (fermiDyadicImpulse 1 (k+1) - fermiDyadicImpulse 1 (k+2))^2) =
          fun k : ℕ => (1/4 : ℝ)*(1/4 : ℝ)^k := by
        funext k
        rw [heq, half_power_sq]
        norm_num
      rw [hf]
      simpa only [show (1/4 : ℝ)*(1-1/4)⁻¹ = 1/3 by norm_num] using hg
    rw [ht.tsum_eq]
    norm_num [fermiDyadicImpulse]
  · have ha : fermiDyadicImpulse (j+1+1) (j+1) = 0 := by
      simp [fermiDyadicImpulse]
    have hb : fermiDyadicImpulse (j+1+1) (j+2) = 1 := by
      simp [fermiDyadicImpulse, Nat.add_assoc]
    have ht := hs.le_tsum j (fun _ _ => sq_nonneg _)
    rw [ha, hb] at ht
    nlinarith [sq_nonneg (fermiDyadicImpulse (j+1+1) 0)]


/-- Assigning one depth to each distinct odd index produces distinct literal indices. -/
theorem fermiDyadicAntichain_index_injective (S : Finset ℕ)
    (hS : ∀ d ∈ S, Odd d) (j : S → ℕ) :
    Function.Injective (fun d : S => 2^(j d)*(d : ℕ)) := by
  intro d e h
  have hde := (dyadic_odd_dvd_iff (j d) (j e) (hS d d.property) (hS e e.property)).mp
    (dvd_of_eq h)
  have hed := (dyadic_odd_dvd_iff (j e) (j d) (hS e e.property) (hS d d.property)).mp
    (dvd_of_eq h.symm)
  exact Subtype.ext (Nat.dvd_antisymm hde.2 hed.2)

/-- The literal coefficient at an assigned index is exactly its normalized amplitude. -/
theorem fermiDyadicAntichainCoefficient_at (S : Finset ℕ)
    (hS : ∀ d ∈ S, Odd d) (j : S → ℕ) (a : S → ℝ) (d : S) :
    fermiDyadicAntichainCoefficient S j a (2^(j d)*(d : ℕ)) =
      (2 : ℝ)^(j d)*(d : ℝ)*a d := by
  have hi := fermiDyadicAntichain_index_injective S hS j
  unfold fermiDyadicAntichainCoefficient
  simp only [hi.eq_iff, Finset.sum_ite_eq, Finset.mem_univ, if_true]

/-- Nonnegative normalized amplitudes give nonnegative native coefficients. -/
theorem fermiDyadicAntichainCoefficient_nonneg (S : Finset ℕ)
    (j : S → ℕ) (a : S → ℝ) (ha : ∀ d, 0 ≤ a d) (n : ℕ) :
    0 ≤ fermiDyadicAntichainCoefficient S j a n := by
  unfold fermiDyadicAntichainCoefficient
  apply Finset.sum_nonneg
  intro d _
  exact ite_nonneg
    (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) (Nat.cast_nonneg _)) (ha d))
    le_rfl

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
