import GaloisForLFunctions.RHTower.MobiusDivisorPrimeCorrelationBlockIntegral
import GaloisForLFunctions.RHTower.DivisorSourceResidueOrientation

/-!
# The discrete prime-release coefficient is the signed physical average

Countable integration joins every literal quotient block with no omitted
tail. Exact dilation then identifies the complete discrete release with
the physical head average. Its source residue determines the strict sign
at sufficiently distant unprocessed primes for each fixed nonempty core.
No threshold uniform in the changing core or cutoff is assumed.
-/

noncomputable section
open Finset Set Filter Topology MeasureTheory
namespace RHTower

private lemma kernel_integral_from_zero (P : Finset ℕ) (p : ℕ) :
    (∫u in Ioi (0:ℝ),mobiusDivisorPrimeCorrelationKernel P p u)=
      ∫u in Ioi (1:ℝ),mobiusDivisorPrimeCorrelationKernel P p u := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))
  intro u hu
  have hu1 : u≤1 := le_of_not_gt hu.2
  simp [mobiusDivisorPrimeCorrelationKernel,mobiusDivisorContinuousHead_eq_zero P hu1]

private lemma dilation_integral_from_zero (P : Finset ℕ) (Y : ℝ) :
    (∫x in Ioi (0:ℝ),mobiusDivisorContinuousHead P (Y*x)*mobiusDivisorContinuousHead P x/x^3)=
      mobiusDivisorDilationMean P Y := by
  apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
    (Ioi_subset_Ioi (by norm_num : (0:ℝ)≤1))
  intro x hx
  have hx1 : x≤1 := le_of_not_gt hx.2
  simp [mobiusDivisorContinuousHead_eq_zero P hx1]

/-- The complete physical prime kernel is exactly the dilation average,
with the Jacobian and both square-root factors retained. -/
theorem integral_mobiusDivisorPrimeCorrelationKernel_eq_dilationMean
    (P : Finset ℕ) {p : ℕ} (hp : 0<p) :
    (∫u in Ioi (1:ℝ),mobiusDivisorPrimeCorrelationKernel P p u)=
      2*(p:ℝ)^(-(3/2:ℝ))*mobiusDivisorDilationMean P p := by
  have hpR : (0:ℝ)<p := by exact_mod_cast hp
  let f : ℝ→ℝ := fun x => mobiusDivisorContinuousHead P ((p:ℝ)*x)*mobiusDivisorContinuousHead P x/x^3
  have he (u : ℝ) : mobiusDivisorPrimeCorrelationKernel P p u =
      (2*Real.sqrt p/(p:ℝ)^3)*f ((p:ℝ)⁻¹*u) := by
    dsimp [mobiusDivisorPrimeCorrelationKernel,f]
    rw [show (p:ℝ)*((p:ℝ)⁻¹*u)=u by field_simp]
    rw [div_eq_mul_inv u (p:ℝ),mul_comm (p:ℝ)⁻¹ u]
    by_cases hu : u=0
    · simp [hu]
    · field_simp
  rw [← kernel_integral_from_zero]
  simp_rw [he]
  rw [integral_const_mul,integral_comp_mul_left_Ioi f 0 (inv_pos.mpr hpR),
    mul_zero,inv_inv,smul_eq_mul]
  change (2*Real.sqrt p/(p:ℝ)^3)*((p:ℝ)*
    (∫x in Ioi (0:ℝ),mobiusDivisorContinuousHead P ((p:ℝ)*x)*mobiusDivisorContinuousHead P x/x^3))=_
  rw [dilation_integral_from_zero]
  have hr : (p:ℝ)^(-(3/2:ℝ))=Real.sqrt p/(p:ℝ)^2 := by
    rw [show -(3/2:ℝ)=1/2-2 by norm_num,Real.rpow_sub hpR,
      ← Real.sqrt_eq_rpow,Real.rpow_two]
  rw [hr]
  field_simp

private lemma unit_blocks_union :
    (⋃n : ℕ,Ioc ((n+1:ℕ):ℝ) (n+2:ℕ))=Ioi (1:ℝ) := by
  ext u
  constructor
  · intro hu
    obtain ⟨n,hn⟩ := mem_iUnion.mp hu
    have h1 : (1:ℝ)≤(n+1:ℕ) := by exact_mod_cast Nat.le_add_left 1 n
    exact lt_of_le_of_lt h1 hn.1
  · intro hu
    have hc : 2≤⌈u⌉₊ := by
      have h : (1:ℝ)<(⌈u⌉₊:ℝ) := lt_of_lt_of_le hu (Nat.le_ceil u)
      have hn : 1<⌈u⌉₊ := by exact_mod_cast h
      omega
    obtain ⟨n,hn⟩ : ∃n : ℕ,⌈u⌉₊=n+2 := ⟨⌈u⌉₊-2,by omega⟩
    have hlo := Nat.ceil_lt_add_one (show 0≤u by linarith [show 1<u from hu])
    have hhi := Nat.le_ceil u
    rw [hn] at hlo hhi
    refine mem_iUnion.mpr ⟨n,?_⟩
    constructor
    · norm_num only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at *
      linarith
    · exact hhi

private lemma unit_blocks_disjoint :
    Pairwise (Function.onFun Disjoint (fun n : ℕ => Ioc ((n+1:ℕ):ℝ) (n+2:ℕ))) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro u hi hj
  rcases hi with ⟨hil,hih⟩
  rcases hj with ⟨hjl,hjh⟩
  norm_num only [Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at *
  rcases lt_or_gt_of_ne hij with h | h
  · have hh : (i:ℝ)+1≤j := by exact_mod_cast Nat.succ_le_of_lt h
    linarith
  · have hh : (j:ℝ)+1 ≤ (i:ℝ) := by exact_mod_cast Nat.succ_le_of_lt h
    linarith

/-- The entire discrete mass series is the physical integral of the actual
two-head source, with absolute convergence across all quotient blocks. -/
theorem hasSum_mobiusDivisorPrimeCorrelationMass_integral (P : Finset ℕ)
    (hP : ∀p∈P,p.Prime) {p : ℕ} (hp : 0<p) :
    HasSum (mobiusDivisorPrimeCorrelationMass P p)
      ((Sieve.squarefreeDensity*∏q∈insert p P,(q:ℝ)/(q+1))*
        ∫u in Ioi (1:ℝ),mobiusDivisorPrimeCorrelationKernel P p u) := by
  have hi : IntegrableOn (mobiusDivisorPrimeCorrelationKernel P p)
      (⋃n : ℕ,Ioc ((n+1:ℕ):ℝ) (n+2:ℕ)) := by
    rw [unit_blocks_union]
    exact integrable_mobiusDivisorPrimeCorrelationKernel P hp
  have h := hasSum_integral_iUnion (fun _ => measurableSet_Ioc) unit_blocks_disjoint hi
  rw [unit_blocks_union] at h
  have hmul := h.mul_left (Sieve.squarefreeDensity*∏q∈insert p P,(q:ℝ)/(q+1))
  have hs : HasSum (fun n : ℕ => mobiusDivisorPrimeCorrelationMass P p (n+1))
      ((Sieve.squarefreeDensity*∏q∈insert p P,(q:ℝ)/(q+1))*
        ∫u in Ioi (1:ℝ),mobiusDivisorPrimeCorrelationKernel P p u) := by
    apply HasSum.congr_fun hmul
    intro n
    rw [show n+2=(n+1)+1 by omega,
      integral_mobiusDivisorPrimeCorrelationKernel_block P hP hp (by omega : 0<n+1)]
    simp [mobiusDivisorPrimeCorrelationMass]
  simpa [mobiusDivisorPrimeCorrelationMass] using (hasSum_nat_add_iff 1).mp hs

/-- The actual discrete prime-release coefficient equals the physical
signed dilation average with its exact positive density and dilation factor. -/
theorem mobiusDivisorPrimeReleaseCoefficient_eq_dilationMean (P : Finset ℕ)
    (hP : ∀q∈P,q.Prime) {p : ℕ} (hp : p.Prime) (hpP : p∉P) :
    ((∑'n,mobiusDivisorFixedCoreBlockMass P n)-
      ∑'n,mobiusDivisorFixedCoreBlockMass (insert p P) n)=
      2*(Sieve.squarefreeDensity*∏q∈insert p P,(q:ℝ)/(q+1))*
        (p:ℝ)^(-(3/2:ℝ))*mobiusDivisorDilationMean P p := by
  have h := (hasSum_mobiusDivisorPrimeCorrelationMass P hP hp hpP).unique
    (hasSum_mobiusDivisorPrimeCorrelationMass_integral P hP hp.pos)
  rw [integral_mobiusDivisorPrimeCorrelationKernel_eq_dilationMean P hp.pos] at h
  convert! h using 1; ring

/-- Every fixed nonempty prime core has the strict parity-determined
discrete release sign at all sufficiently distant unprocessed primes. -/
theorem eventually_mobiusDivisorPrimeReleaseCoefficient_oriented_pos (P : Finset ℕ)
    (hP : P.Nonempty) (hprime : ∀q∈P,q.Prime) :
    ∀ᶠp : ℕ in atTop,p.Prime → p∉P →
      0<(-1:ℝ)^(P.card+1)*((∑'n,mobiusDivisorFixedCoreBlockMass P n)-
        ∑'n,mobiusDivisorFixedCoreBlockMass (insert p P) n) := by
  have hw := (tendsto_natCast_atTop_atTop : Tendsto (fun p : ℕ => (p:ℝ)) atTop atTop).eventually
    (eventually_mobiusDivisorDilationMean_oriented_pos P hP hprime)
  filter_upwards [hw] with p hpw
  intro hp hpP
  rw [mobiusDivisorPrimeReleaseCoefficient_eq_dilationMean P hprime hp hpP]
  have hprod : 0<∏q∈insert p P,(q:ℝ)/(q+1) := by
    apply Finset.prod_pos
    intro q hq
    have hqprime : q.Prime := by
      rcases Finset.mem_insert.mp hq with rfl | hq
      · exact hp
      · exact hprime q hq
    exact div_pos (by exact_mod_cast hqprime.pos) (by positivity)
  have hfactor : 0<2*(Sieve.squarefreeDensity*∏q∈insert p P,(q:ℝ)/(q+1))*
      (p:ℝ)^(-(3/2:ℝ)) :=
    mul_pos (mul_pos (by norm_num) (mul_pos (by rw [Sieve.squarefreeDensity_eq]; positivity) hprod))
      (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _)
  convert! mul_pos hfactor hpw using 1; ring

end RHTower
