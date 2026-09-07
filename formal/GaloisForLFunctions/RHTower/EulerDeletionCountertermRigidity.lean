import GaloisForLFunctions.RHTower.EulerDeletionQuotientHarmonicBound
import GaloisForLFunctions.RHTower.Sieve.MoebiusHarmonicTailIdentity

/-!
# Exact increment-mass compensation and finite-energy rigidity

The actual harmonic scalar is minus an absolutely convergent Mertens-increment
mass. It is the unique scalar giving finite full weighted error energy.
-/
noncomputable section
set_option autoImplicit false
open Filter Topology
open scoped BigOperators
namespace RHTower.DeletionCounterterm

private theorem hasSum_reciprocal_mass {N : ℕ} (hN : 1 ≤ N) :
    HasSum (fun i : ℕ => 1 / (((i+N : ℕ) : ℝ)*(((i+N : ℕ) : ℝ)+1)))
      (1/(N : ℝ)) := by
  have hterm (i : ℕ) : 1 / (((i+N : ℕ) : ℝ)*(((i+N : ℕ) : ℝ)+1)) =
      1/((i+N : ℕ) : ℝ)-1/((i+1+N : ℕ) : ℝ) := by
    have hi : (0 : ℝ) < (i+N : ℕ) := by positivity
    have hi1 : (0 : ℝ) < ((i+N : ℕ) : ℝ)+1 := by positivity
    rw [show ((i+1+N : ℕ) : ℝ)=((i+N : ℕ) : ℝ)+1 by push_cast; ring]
    field_simp
    ring
  apply (hasSum_iff_tendsto_nat_of_nonneg (fun _ => by positivity) _).mpr
  have hsum (k : ℕ) : (∑ i ∈ Finset.range k,
      1 / (((i+N : ℕ) : ℝ)*(((i+N : ℕ) : ℝ)+1))) =
        1/(N : ℝ)-1/((k+N : ℕ) : ℝ) := by
    simp_rw [hterm]
    simpa using Finset.sum_range_sub' (fun i : ℕ => 1/((i+N : ℕ) : ℝ)) k
  have ht : Tendsto (fun k : ℕ => 1/((k+N : ℕ) : ℝ)) atTop (nhds 0) :=
    (tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat N)
  simpa only [hsum,sub_zero] using tendsto_const_nhds.sub ht

/-- The complete cutoff increment field has absolutely convergent weighted mass. -/
theorem hasSum_mertensIncrement_mass {N : ℕ} (hN : 1 ≤ N) :
    HasSum (fun i : ℕ => (Sieve.mertensM (i+N)-Sieve.mertensM N) /
      (((i+N : ℕ) : ℝ)*(((i+N : ℕ) : ℝ)+1))) (-deningerHarmonicPartial N) := by
  have hs := (summable_nat_add_iff N).mpr deningerMertensHarmonic_summable
  have hm := hs.hasSum.sub ((hasSum_reciprocal_mass hN).mul_left (Sieve.mertensM N))
  have hid := Sieve.deningerHarmonicPartial_eq_mertens_boundary_sub_tail N
  have hmass : (∑' i : ℕ, Sieve.mertensM (i+N) /
      (((i+N : ℕ) : ℝ)*(((i+N : ℕ) : ℝ)+1))) - Sieve.mertensM N*(1/(N : ℝ)) =
      -deningerHarmonicPartial N := by rw [mul_one_div]; linarith
  rw [hmass] at hm
  simpa only [mul_one_div,← sub_div] using hm

/-- The counterterm is fixed by the entire signed increment mass. -/
theorem harmonic_eq_neg_increment_mass {N : ℕ} (hN : 1 ≤ N) :
    deningerHarmonicPartial N = -(∑' i : ℕ,
      (Sieve.mertensM (i+N)-Sieve.mertensM N) /
        (((i+N : ℕ) : ℝ)*(((i+N : ℕ) : ℝ)+1))) := by
  rw [(hasSum_mertensIncrement_mass hN).tsum_eq,neg_neg]

/-- The source is exactly quotient sampling minus the full continuous-cell mass. -/
theorem error_eq_compensated_quotient_mass {N n : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n) :
    1-bdMobiusModularApproximant N n =
      (∑ j ∈ Finset.Icc 1 (n/(N+1)), (Sieve.mertensM (n/j)-Sieve.mertensM N)) -
        (n : ℝ)*(∑' i : ℕ, (Sieve.mertensM (i+N)-Sieve.mertensM N) /
          (((i+N : ℕ) : ℝ)*(((i+N : ℕ) : ℝ)+1))) := by
  rw [one_sub_bdMobiusModularApproximant_eq_harmonic_add_floorResidual,
    DeletionQuotientTail.floorResidual_eq_quotient_mertens N n hn,
    harmonic_eq_neg_increment_mass hN]
  ring

/-- A proposed linear compensation of the literal omitted-floor field. -/
def correctedError (N : ℕ) (c : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ)*c+bdMobiusFloorResidual N n

/-- The genuine full-tail weights, with all coordinates n>=1 present. -/
def correctedEnergyTerm (N : ℕ) (c : ℝ) (j : ℕ) : ℝ :=
  correctedError N c (j+1)^2/(((j : ℝ)+1)*((j : ℝ)+2))

/-- Changing the counterterm adds precisely a linear tail to the bounded actual error. -/
theorem correctedError_eq (N : ℕ) (c : ℝ) (n : ℕ) :
    correctedError N c n = (n : ℝ)*(c-deningerHarmonicPartial N)+
      (1-bdMobiusModularApproximant N n) := by
  rw [correctedError,one_sub_bdMobiusModularApproximant_eq_harmonic_add_floorResidual]
  ring

/-- The full signed tail fixes its asymptotic linear coefficient exactly. -/
theorem correctedError_div_tendsto (N : ℕ) (c : ℝ) :
    Tendsto (fun j : ℕ => correctedError N c (j+1)/((j : ℝ)+1)) atTop
      (nhds (c-deningerHarmonicPartial N)) := by
  have he : Tendsto (fun j : ℕ =>
      (1-bdMobiusModularApproximant N (j+1))/((j : ℝ)+1)) atTop (nhds 0) := by
    apply squeeze_zero_norm (a := fun j : ℕ => ((N : ℝ)+1)/((j : ℝ)+1))
    · intro j
      rw [Real.norm_eq_abs,abs_div,abs_of_pos (by positivity : (0 : ℝ) < (j : ℝ)+1)]
      exact div_le_div_of_nonneg_right (abs_one_sub_bdMobiusModularApproximant_le N _) (by positivity)
    · simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one] using
        (tendsto_const_div_atTop_nhds_zero_nat ((N : ℝ)+1)).comp (tendsto_add_atTop_nat 1)
  have hfun (j : ℕ) : correctedError N c (j+1)/((j : ℝ)+1) =
      (c-deningerHarmonicPartial N)+(1-bdMobiusModularApproximant N (j+1))/((j : ℝ)+1) := by
    rw [correctedError_eq]
    push_cast
    field_simp
  simpa only [hfun,add_zero] using tendsto_const_nhds.add he

/-- Every incorrect scalar leaves a nonzero limiting energy summand. -/
theorem correctedEnergyTerm_tendsto (N : ℕ) (c : ℝ) :
    Tendsto (correctedEnergyTerm N c) atTop (nhds ((c-deningerHarmonicPartial N)^2)) := by
  have hr : Tendsto (fun j : ℕ => ((j : ℝ)+1)/((j : ℝ)+2)) atTop (nhds 1) := by
    simpa only [Function.comp_def,Nat.cast_add,Nat.cast_one,show (1 : ℝ)+1=2 by ring,add_assoc] using
      (tendsto_natCast_div_add_atTop (1 : ℝ)).comp (tendsto_add_atTop_nat 1)
  have hfun (j : ℕ) : correctedEnergyTerm N c j =
      (correctedError N c (j+1)/((j : ℝ)+1))^2 * (((j : ℝ)+1)/((j : ℝ)+2)) := by
    rw [correctedEnergyTerm]
    field_simp
  change Tendsto (fun j => correctedEnergyTerm N c j) _ _
  simp_rw [hfun]
  simpa only [mul_one] using ((correctedError_div_tendsto N c).pow 2).mul hr

/-- The unique admissible scalar gives the actual full source error energy. -/
theorem hasSum_correctedEnergyTerm (N : ℕ) :
    HasSum (correctedEnergyTerm N (deningerHarmonicPartial N)) (bdMobiusFullErrorEnergy N) := by
  unfold correctedEnergyTerm
  simp_rw [correctedError_eq]
  simpa only [sub_self,mul_zero,zero_add,pow_two,bdMobiusFullErrorEnergy] using
      hasSum_stepGram (abs_one_sub_bdMobiusModularApproximant_le N)
        (abs_one_sub_bdMobiusModularApproximant_le N)

/-- Complete classification: finite full weighted energy forces exactly the source counterterm. -/
theorem summable_correctedEnergyTerm_iff (N : ℕ) (c : ℝ) :
    Summable (correctedEnergyTerm N c) ↔ c=deningerHarmonicPartial N := by
  constructor
  · intro hs
    have hzero := tendsto_nhds_unique (correctedEnergyTerm_tendsto N c) hs.tendsto_atTop_zero
    nlinarith [sq_nonneg (c-deningerHarmonicPartial N)]
  · rintro rfl
    exact (hasSum_correctedEnergyTerm N).summable

/-- The uncompensated quotient field has finite energy exactly at zero harmonic defect. -/
theorem summable_floorResidual_energy_iff (N : ℕ) :
    Summable (fun j : ℕ => bdMobiusFloorResidual N (j+1)^2/
      (((j : ℝ)+1)*((j : ℝ)+2))) ↔ deningerHarmonicPartial N=0 := by
  have h := summable_correctedEnergyTerm_iff N 0
  unfold correctedEnergyTerm correctedError at h
  simpa only [mul_zero,zero_add,eq_comm] using h

end RHTower.DeletionCounterterm
