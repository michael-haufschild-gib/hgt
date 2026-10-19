import GaloisForLFunctions.TransHorizonIncidenceMechanics.FermiDyadicAntichainCoordinates

/-!
# Uniform physical Fermi bounds for finite-prime antichains

A finite odd support carries one dyadic depth and normalized amplitude per odd
integer. Exact native coordinates turn homogeneous energies into odd-divisor
packet energies. Prime-product frame bounds and scalar impulse laws give the
physical observability constant `8 * (product (p+1)/(p-1))^2`.

The bound permits arbitrary signed amplitudes and every horizon containing the
literal indices. Representation of every arbitrary antichain support remains a
separate task.
-/

open scoped BigOperators
open Finset GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics
noncomputable section
set_option autoImplicit false

private theorem antichain_sieve_square (N : ℕ) (S : Finset ℕ)
    (j : S → ℕ) (a : S → ℝ) (hS : ∀ d ∈ S, Odd d)
    (hN : ∀ d : S, 2^(j d)*(d : ℕ) ≤ N) (k m : ℕ) :
    (fermiNormalizedDyadicSieve N (fermiDyadicAntichainCoefficient S j a) (2*m+1) k)^2 /
      ((2*m+1 : ℕ) : ℝ)^2 =
      (fermiOddDivisorPacket S (fun d => fermiDyadicImpulse (j d) k*a d) m)^2 := by
  rw [← div_pow, fermiDyadicAntichain_sieve_coordinate N S j a hS hN]

private theorem antichain_odd_square (N : ℕ) (S : Finset ℕ)
    (j : S → ℕ) (a : S → ℝ) (hS : ∀ d ∈ S, Odd d)
    (hN : ∀ d : S, 2^(j d)*(d : ℕ) ≤ N) (m : ℕ) :
    (sieveSeq N (fermiDyadicAntichainCoefficient S j a) (2*m+1))^2 /
      ((2*m+1 : ℕ) : ℝ)^2 =
      (fermiOddDivisorPacket S (fun d => fermiDyadicImpulse (j d) 0*a d) m)^2 := by
  simpa only [fermiNormalizedDyadicSieve, pow_zero, one_mul, div_one] using
    antichain_sieve_square N S j a hS hN 0 m

private theorem antichain_jump_square (N : ℕ) (S : Finset ℕ)
    (j : S → ℕ) (a : S → ℝ) (hS : ∀ d ∈ S, Odd d)
    (hN : ∀ d : S, 2^(j d)*(d : ℕ) ≤ N) (k m : ℕ) :
    (fermiNormalizedDyadicJump N (fermiDyadicAntichainCoefficient S j a) (2*m+1) (k+1))^2 /
      ((2*m+1 : ℕ) : ℝ)^2 =
      (fermiOddDivisorPacket S
        (fun d => (fermiDyadicImpulse (j d) (k+1) - fermiDyadicImpulse (j d) (k+2))*a d) m)^2 := by
  rw [← div_pow, fermiDyadicAntichain_jump_coordinate N S j a hS hN]

/-- Exact convergent full homogeneous energy in antichain coordinates. -/
theorem fermiDyadicAntichain_homogeneousEnergy (N : ℕ) (S : Finset ℕ)
    (j : S → ℕ) (a : S → ℝ) (hS : ∀ d ∈ S, Odd d)
    (hN : ∀ d : S, 2^(j d)*(d : ℕ) ≤ N) :
    Summable (fun k : ℕ => ∑' m : ℕ,
      (fermiOddDivisorPacket S (fun d => fermiDyadicImpulse (j d) k*a d) m)^2) ∧
    sieveHomogeneousEnergy N (fermiDyadicAntichainCoefficient S j a) =
      ∑' k : ℕ, ∑' m : ℕ,
        (fermiOddDivisorPacket S (fun d => fermiDyadicImpulse (j d) k*a d) m)^2 := by
  let E : ℕ → ℝ := fun k => ∑' m : ℕ,
    (fermiOddDivisorPacket S (fun d => fermiDyadicImpulse (j d) k*a d) m)^2
  change Summable E ∧ sieveHomogeneousEnergy N (fermiDyadicAntichainCoefficient S j a) = ∑' k, E k
  have hp := (sieve_fermi_homogeneous_summable N (fermiDyadicAntichainCoefficient S j a)).2.1
  have ht : Summable (fun k : ℕ => E (k+1)) := hp.prod.congr (fun k =>
    tsum_congr (fun m => antichain_sieve_square N S j a hS hN (k+1) m))
  have hE : Summable E := ht.comp_nat_add
  refine ⟨hE, ?_⟩
  rw [sieveHomogeneousEnergy, hp.tsum_prod, hE.tsum_eq_zero_add]
  congr 1
  · exact tsum_congr (fun m => antichain_odd_square N S j a hS hN m)
  · exact tsum_congr (fun k => tsum_congr
      (fun m => antichain_sieve_square N S j a hS hN (k+1) m))

/-- Exact convergent selected homogeneous energy in antichain coordinates. -/
theorem fermiDyadicAntichain_selectedHomogeneousEnergy (N : ℕ) (S : Finset ℕ)
    (j : S → ℕ) (a : S → ℝ) (hS : ∀ d ∈ S, Odd d)
    (hN : ∀ d : S, 2^(j d)*(d : ℕ) ≤ N) :
    Summable (fun k : ℕ => ∑' m : ℕ,
      (fermiOddDivisorPacket S
        (fun d => (fermiDyadicImpulse (j d) (k+1) - fermiDyadicImpulse (j d) (k+2))*a d) m)^2) ∧
    fermiSelectedHomogeneousEnergy N (fermiDyadicAntichainCoefficient S j a) =
      (∑' m : ℕ, (fermiOddDivisorPacket S (fun d => fermiDyadicImpulse (j d) 0*a d) m)^2) +
      ∑' k : ℕ, ∑' m : ℕ,
        (fermiOddDivisorPacket S
          (fun d => (fermiDyadicImpulse (j d) (k+1) - fermiDyadicImpulse (j d) (k+2))*a d) m)^2 := by
  have hp := (sieve_fermi_homogeneous_summable N (fermiDyadicAntichainCoefficient S j a)).2.2
  refine ⟨hp.prod.congr (fun k => tsum_congr
    (fun m => antichain_jump_square N S j a hS hN k m)), ?_⟩
  rw [fermiSelectedHomogeneousEnergy, hp.tsum_prod]
  congr 1
  · exact tsum_congr (fun m => antichain_odd_square N S j a hS hN m)
  · exact tsum_congr (fun k => tsum_congr
      (fun m => antichain_jump_square N S j a hS hN k m))

private theorem impulse_coefficient_mass (S : Finset ℕ) (j : S → ℕ) (a : S → ℝ) :
    Summable (fun k : ℕ => ∑ d : S, (fermiDyadicImpulse (j d) k*a d)^2) ∧
      (∑' k : ℕ, ∑ d : S, (fermiDyadicImpulse (j d) k*a d)^2) =
        (4/3 : ℝ)*(∑ d : S, (a d)^2) := by
  have hd (d : S) : HasSum (fun k : ℕ => (fermiDyadicImpulse (j d) k*a d)^2)
      ((4/3 : ℝ)*(a d)^2) := by
    simpa only [mul_pow] using (fermiDyadicImpulse_square_hasSum (j d)).mul_right ((a d)^2)
  refine ⟨summable_sum (fun d _ => (hd d).summable), ?_⟩
  rw [Summable.tsum_finsetSum (fun d _ => (hd d).summable)]
  simp_rw [(hd _).tsum_eq]
  rw [Finset.mul_sum]

private theorem impulse_coefficient_selected (S : Finset ℕ) (j : S → ℕ) (a : S → ℝ) :
    Summable (fun k : ℕ => ∑ d : S,
      ((fermiDyadicImpulse (j d) (k+1) - fermiDyadicImpulse (j d) (k+2))*a d)^2) ∧
      (1/3 : ℝ)*(∑ d : S, (a d)^2) ≤
        (∑ d : S, (fermiDyadicImpulse (j d) 0*a d)^2) +
        ∑' k : ℕ, ∑ d : S,
          ((fermiDyadicImpulse (j d) (k+1) - fermiDyadicImpulse (j d) (k+2))*a d)^2 := by
  have hd (d : S) : Summable (fun k : ℕ =>
      ((fermiDyadicImpulse (j d) (k+1) - fermiDyadicImpulse (j d) (k+2))*a d)^2) := by
    simpa only [mul_pow] using (fermiDyadicImpulse_selected_lower (j d)).1.mul_right ((a d)^2)
  refine ⟨summable_sum (fun d _ => hd d), ?_⟩
  rw [Summable.tsum_finsetSum (fun d _ => hd d), ← Finset.sum_add_distrib, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro d _
  have h := mul_le_mul_of_nonneg_right (fermiDyadicImpulse_selected_lower (j d)).2 (sq_nonneg (a d))
  simpa only [mul_pow, tsum_mul_right, add_mul] using h

/-- Explicit homogeneous bounds for antichain packets supported on a finite prime set. -/
theorem fermiDyadicAntichain_prime_homogeneous_bounds (N : ℕ) (P S : Finset ℕ)
    (j : S → ℕ) (a : S → ℝ) (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ d ∈ S, Odd d) (hSP : ∀ d ∈ S, d.primeFactors ⊆ P)
    (hN : ∀ d : S, 2^(j d)*(d : ℕ) ≤ N) :
    fermiOddHomogeneousMass*(∏ p ∈ P, ((p : ℝ)-1)/((p : ℝ)+1))*(1/3)*(∑ d : S, (a d)^2) ≤
      fermiSelectedHomogeneousEnergy N (fermiDyadicAntichainCoefficient S j a) ∧
    sieveHomogeneousEnergy N (fermiDyadicAntichainCoefficient S j a) ≤
      fermiOddHomogeneousMass*(∏ p ∈ P, ((p : ℝ)+1)/((p : ℝ)-1))*(4/3)*(∑ d : S, (a d)^2) := by
  let v : ℕ → S → ℝ := fun k d => fermiDyadicImpulse (j d) k*a d
  let w : ℕ → S → ℝ := fun k d =>
    (fermiDyadicImpulse (j d) (k+1) - fermiDyadicImpulse (j d) (k+2))*a d
  let A : ℝ := ∏ p ∈ P, ((p : ℝ)-1)/((p : ℝ)+1)
  let B : ℝ := ∏ p ∈ P, ((p : ℝ)+1)/((p : ℝ)-1)
  have hA : 0 ≤ fermiOddHomogeneousMass*A := by
    apply mul_nonneg fermiOddHomogeneousMass_pos.le
    apply Finset.prod_nonneg
    intro p hp
    have hp1 : 1 < (p : ℝ) := by exact_mod_cast (hP p hp).one_lt
    exact div_nonneg (by linarith) (by positivity)
  have hf := fermiDyadicAntichain_homogeneousEnergy N S j a hS hN
  have hg := fermiDyadicAntichain_selectedHomogeneousEnergy N S j a hS hN
  have hmass := impulse_coefficient_mass S j a
  have hsel := impulse_coefficient_selected S j a
  constructor
  · have hlo (k : ℕ) : fermiOddHomogeneousMass*A*(∑ d : S, (w k d)^2) ≤
        ∑' m : ℕ, (fermiOddDivisorPacket S (w k) m)^2 :=
      (fermiOddDivisorPacket_frame_bounds P S hP hS hSP (w k)).1
    have hs := Summable.tsum_le_tsum hlo (hsel.1.mul_left (fermiOddHomogeneousMass*A)) hg.1
    rw [tsum_mul_left] at hs
    have hzero := (fermiOddDivisorPacket_frame_bounds P S hP hS hSP (v 0)).1
    change fermiOddHomogeneousMass*A*(1/3)*(∑ d : S, (a d)^2) ≤ _
    rw [hg.2]
    calc
      fermiOddHomogeneousMass*A*(1/3)*(∑ d : S, (a d)^2) =
          fermiOddHomogeneousMass*A*((1/3)*(∑ d : S, (a d)^2)) := by ring
      _ ≤ fermiOddHomogeneousMass*A*((∑ d : S, (v 0 d)^2) +
          ∑' k : ℕ, ∑ d : S, (w k d)^2) := mul_le_mul_of_nonneg_left hsel.2 hA
      _ = fermiOddHomogeneousMass*A*(∑ d : S, (v 0 d)^2) +
          fermiOddHomogeneousMass*A*(∑' k : ℕ, ∑ d : S, (w k d)^2) := by ring
      _ ≤ _ := add_le_add hzero hs
  · have hup (k : ℕ) : (∑' m : ℕ, (fermiOddDivisorPacket S (v k) m)^2) ≤
        fermiOddHomogeneousMass*B*(∑ d : S, (v k d)^2) :=
      (fermiOddDivisorPacket_frame_bounds P S hP hS hSP (v k)).2
    have hs := Summable.tsum_le_tsum hup hf.1 (hmass.1.mul_left (fermiOddHomogeneousMass*B))
    rw [tsum_mul_left, hmass.2, ← hf.2] at hs
    simpa only [mul_assoc] using hs

/-- Uniform native physical observability for a finite set of allowed odd prime factors. -/
theorem fermiDyadicAntichain_finitePrime_physical_bound (N : ℕ) (P S : Finset ℕ)
    (j : S → ℕ) (a : S → ℝ) (hP : ∀ p ∈ P, p.Prime)
    (hS : ∀ d ∈ S, Odd d) (hSP : ∀ d ∈ S, d.primeFactors ⊆ P)
    (hN : ∀ d : S, 2^(j d)*(d : ℕ) ≤ N) :
    sieveTotalPronicEnergy N (fermiDyadicAntichainCoefficient S j a) ≤
      8*(∏ p ∈ P, ((p : ℝ)+1)/((p : ℝ)-1))^2 *
        fermiSelectedTotalPronicEnergy N (fermiDyadicAntichainCoefficient S j a) := by
  let A : ℝ := ∏ p ∈ P, ((p : ℝ)-1)/((p : ℝ)+1)
  let B : ℝ := ∏ p ∈ P, ((p : ℝ)+1)/((p : ℝ)-1)
  have hBA : B*A = 1 := by
    dsimp only [A, B]
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro p hp
    have hp1 : 1 < (p : ℝ) := by exact_mod_cast (hP p hp).one_lt
    field_simp [(sub_pos.mpr hp1).ne', show (p : ℝ)+1 ≠ 0 by linarith]
  have h := fermiDyadicAntichain_prime_homogeneous_bounds N P S j a hP hS hSP hN
  have hhom : sieveHomogeneousEnergy N (fermiDyadicAntichainCoefficient S j a) ≤
      4*B^2*fermiSelectedHomogeneousEnergy N (fermiDyadicAntichainCoefficient S j a) := by
    calc
      _ ≤ fermiOddHomogeneousMass*B*(4/3)*(∑ d : S, (a d)^2) := h.2
      _ = 4*B^2*(fermiOddHomogeneousMass*A*(1/3)*(∑ d : S, (a d)^2)) := by
        calc
          _ = fermiOddHomogeneousMass*B*(4/3)*(∑ d : S, (a d)^2)*(B*A) := by rw [hBA, mul_one]
          _ = _ := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h.1 (by positivity)
  have hp := sieveHomogeneousEnergy_pronic_bounds N (fermiDyadicAntichainCoefficient S j a)
  have hq := fermiSelectedHomogeneousEnergy_pronic_bounds N (fermiDyadicAntichainCoefficient S j a)
  change _ ≤ 8*B^2*_
  calc
    _ ≤ sieveHomogeneousEnergy N (fermiDyadicAntichainCoefficient S j a) := hp.2
    _ ≤ 4*B^2*fermiSelectedHomogeneousEnergy N (fermiDyadicAntichainCoefficient S j a) := hhom
    _ ≤ 4*B^2*(2*fermiSelectedTotalPronicEnergy N (fermiDyadicAntichainCoefficient S j a)) :=
      mul_le_mul_of_nonneg_left (by linarith [hq.1]) (by positivity)
    _ = _ := by ring

end
end GaloisForLFunctions.TransHorizonIncidenceMechanics
