import GaloisForLFunctions.RestrictedFactorizationCalculus.ArbitrarilySlowSignedCrossingsOnOneDenseMatching
import GaloisForLFunctions.RestrictedFactorizationCalculus.CenteringThePrimePowerReadingsAtTheirQuotientFloors

/-!
# Fixed and crossing flux through growing sets of quotient cuts

Deleting the small primes lifts a single exchange table to every smooth
divisor fibre. The two product endpoints induce different sharp cuts in
each fibre. The signed multiplicities at repeated products are exactly
the coefficients of the deleted Möbius function.
-/

noncomputable section

open Finset Filter ArithmeticFunction RHTower.CoprimeMobius
open scoped Classical ArithmeticFunction.Moebius ArithmeticFunction.zeta
open GaloisForLFunctions.BezoutValuationIncidence GaloisForLFunctions.QuantitativeFactorizationMatching

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private abbrev smooth (y X : ℕ) := RHTower.Sieve.smoothUpTo (Nat.primesLE y) X

/-- Applying the same prefix to all smooth divisor fibres, with the quotient
taken separately in each fibre. -/
def smoothLiftedPrefix (P : ℕ → ℝ) (y X : ℕ) : ℝ :=
  ∑ d ∈ smooth y X,P (X/d)

/-- Smooth dilation recovers the rough Möbius prefix, also at zero. -/
theorem smooth_lift_of_the_full_prefix (y X : ℕ) :
    smoothLiftedPrefix (coprimeMoebiusSum 1) y X=coprimeMoebiusSum (primorial y) X := by
  let B := RoughReading.banned y
  have conv : mobiusAF B*(ζ : ArithmeticFunction ℤ)=smoothAF B := by
    ext n
    rw [coe_mul_zeta_apply,sum_divisors_mobiusAF]
  have inv : smoothAF B*μ=mobiusAF B := by rw [←conv,mul_assoc,coe_zeta_mul_moebius,mul_one]
  have row (n : ℕ) (hn : n ∈ Icc 1 X) : coprimeMoebiusIndicator (primorial y) n=
      ∑ t ∈ n.divisorsAntidiagonal,((smoothAF B t.1:ℤ):ℝ)*(μ t.2:ℝ) := by
    rw [primorial_indicator_eq_deleted_mobius y n (mem_Icc.mp hn).1]
    change (mobiusAF B n:ℝ)=_
    rw [←inv,mul_apply]
    push_cast
    rfl
  rw [coprimeMoebiusSum,sum_congr rfl row,RHTower.Sieve.sum_Icc_divisorsAntidiagonal_swap
    (fun d k => ((smoothAF B d:ℤ):ℝ)*(μ k:ℝ)) X]
  unfold smoothLiftedPrefix
  change (∑ d ∈ (Icc 1 X).filter (fun d => d.primeFactors ⊆ Nat.primesLE y),_)=_
  rw [sum_filter]
  apply sum_congr rfl
  intro d hd
  have ok : IsSmooth B d ↔ d.primeFactors ⊆ Nat.primesLE y :=
    ⟨fun h p hp => Nat.mem_primesLE.mpr ⟨h.2 p hp,Nat.prime_of_mem_primeFactors hp⟩,
     fun h => ⟨Nat.ne_of_gt (show 0<d from (mem_Icc.mp hd).1),fun p hp => (Nat.mem_primesLE.mp (h hp)).1⟩⟩
  rw [←mul_sum,smoothAF_apply]
  by_cases h : IsSmooth B d <;> simp [h,←ok,coprimeMoebiusSum,coprimeMoebiusIndicator]

/-- Signed response of finitely many quotient jumps between two product
endpoints. A change of orientation reverses the sign of the response. -/
def quotientBoundary (P : ℕ → ℝ) (S : Finset ℕ) (a : ℕ → ℝ) (L U : ℕ) : ℝ :=
  ∑ q ∈ S,a q*(P (U/q)-P (L/q))

/-- Concatenating two product intervals with a change of reading leaves
the signed jump in that reading. The formula allows repeated endpoints. -/
theorem compose_quotient_boundaries (P : ℕ → ℝ) (S : Finset ℕ) (a b : ℕ → ℝ)
    (L T U : ℕ) :
    quotientBoundary P S a L T+quotientBoundary P S b T U=
      quotientBoundary P S a L U+quotientBoundary P S (fun q => b q-a q) T U := by
  simp only [quotientBoundary,←sum_add_distrib]
  exact sum_congr rfl (fun q _ => by ring)

/-- Full signed response equals the fixed and crossing responses of the
same exchange table in every smooth fibre at both endpoints. -/
theorem two_cutoff_rough_quotient_flux (F : ℕ → ℕ)
    (law : ∀ n,Squarefree n → F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n)))
    (y : ℕ) (S : Finset ℕ) (a : ℕ → ℝ) (L U : ℕ) :
    quotientBoundary (coprimeMoebiusSum (primorial y)) S a L U=
      quotientBoundary (smoothLiftedPrefix (fixedSignedPrefix F) y) S a L U+
      quotientBoundary (smoothLiftedPrefix (crossingSignedPrefix F) y) S a L U := by
  have part (n : ℕ) : coprimeMoebiusSum (primorial y) n=
      smoothLiftedPrefix (fixedSignedPrefix F) y n+smoothLiftedPrefix (crossingSignedPrefix F) y n := by
    rw [←smooth_lift_of_the_full_prefix]
    simp only [smoothLiftedPrefix,←sum_add_distrib]
    exact sum_congr rfl (fun d _ => (fixed_add_crossing F law (n/d)).symm)
  simp only [quotientBoundary,←sum_add_distrib]
  apply sum_congr rfl
  intro q _
  rw [part (U/q),part (L/q)]
  ring

/-- Summing successive exchange tables and quotient readings counts each
visit at its own cutoff. A change of table alone cancels between fixed
and crossing flux. Changes of reading or prime wall remain explicit. -/
theorem signed_flux_along_a_quotient_history (F : ℕ → ℕ → ℕ)
    (law : ∀ i n,Squarefree n → F i (F i n)=n ∧ (F i n=n ∨ GlobalDyadicOneTwoRel n (F i n)))
    (y cut : ℕ → ℕ) (S : ℕ → Finset ℕ) (a : ℕ → ℕ → ℝ) (N : ℕ) :
    let value := fun i t => ∑ q ∈ S i,a i q*coprimeMoebiusSum (primorial (y i)) (t/q)
    (∑ i ∈ range N,
      (quotientBoundary (smoothLiftedPrefix (fixedSignedPrefix (F i)) (y i)) (S i) (a i) (cut i) (cut (i+1))+
       quotientBoundary (smoothLiftedPrefix (crossingSignedPrefix (F i)) (y i)) (S i) (a i) (cut i) (cut (i+1))))+
      (∑ i ∈ range N,(value (i+1) (cut (i+1))-value i (cut (i+1))))=
      value N (cut N)-value 0 (cut 0) := by
  let value := fun i t => ∑ q ∈ S i,a i q*coprimeMoebiusSum (primorial (y i)) (t/q)
  have leg (i : ℕ) := two_cutoff_rough_quotient_flux (F i) (law i) (y i) (S i) (a i) (cut i) (cut (i+1))
  have endpoints (i : ℕ) : quotientBoundary (coprimeMoebiusSum (primorial (y i))) (S i) (a i)
      (cut i) (cut (i+1))=value i (cut (i+1))-value i (cut i) := by
    simp only [value,quotientBoundary,mul_sub,sum_sub_distrib]
  simp only [←leg,endpoints]
  change (∑ i ∈ range N,(value i (cut (i+1))-value i (cut i)))+
    (∑ i ∈ range N,(value (i+1) (cut (i+1))-value i (cut (i+1))))=value N (cut N)-value 0 (cut 0)
  rw [←sum_add_distrib]
  calc _ = ∑ i ∈ range N,(value (i+1) (cut (i+1))-value i (cut i)) :=
             sum_congr rfl (fun _ _ => by ring)
       _ = _ := Finset.sum_range_sub (fun i => value i (cut i)) N

private def logBudget (X : ℕ) := Real.log ((X:ℝ)+1)
private theorem logBudget_nonneg (X : ℕ) : 0 ≤ logBudget X :=
  Real.log_nonneg (le_add_of_nonneg_left (Nat.cast_nonneg X))
private theorem logBudget_mono : Monotone logBudget := fun _ _ h =>
  Real.log_le_log (by positivity) (add_le_add_left (Nat.cast_le.mpr h) _)

private theorem lifted_crossing_at_one_cut {F : ℕ → ℕ}
    (bound : ∀ n,|crossingSignedPrefix F n| ≤ logBudget n) (y X q : ℕ) :
    |smoothLiftedPrefix (crossingSignedPrefix F) y (X/q)| ≤
      logBudget X*deletionPrice (1/2) y*Real.sqrt X/Real.sqrt q := by
  have price := smooth_population_le_deletion_price (by norm_num : 0<(1/2:ℝ)) y (X/q)
  rw [←Real.sqrt_eq_rpow] at price
  have cap : ((X/q:ℕ):ℝ) ≤ (X:ℝ)/q := by
    rcases Nat.eq_zero_or_pos q with rfl | pos
    · simp
    · exact (le_div_iff₀ (Nat.cast_pos.mpr pos)).mpr (by exact_mod_cast Nat.div_mul_le_self X q)
  have hi := Real.sqrt_le_sqrt cap
  rw [Real.sqrt_div (Nat.cast_nonneg _)] at hi
  have e0 := zero_le_one.trans (deletionPrice_one_le (by norm_num : 0<(1/2:ℝ)) y)
  have count := price.trans (mul_le_mul_of_nonneg_right hi e0)
  calc |smoothLiftedPrefix (crossingSignedPrefix F) y (X/q)| ≤
         ∑ d ∈ smooth y (X/q),|crossingSignedPrefix F (X/q/d)| := abs_sum_le_sum_abs ..
       _ ≤ ∑ _d ∈ smooth y (X/q),logBudget X := sum_le_sum (fun d _ => (bound _).trans
         (logBudget_mono ((Nat.div_le_self (X/q) d).trans (Nat.div_le_self X q))))
       _ = ((smooth y (X/q)).card:ℝ)*logBudget X := by simp
       _ ≤ _ := (mul_le_mul_of_nonneg_right count (logBudget_nonneg _)).trans_eq (by ring)

/-- One density-one matching prices the moving contribution for all prime
walls, quotient atoms, arithmetic readings and oriented pairs of cuts.
The only weight norm used is the reciprocal-root mass of its jumps. -/
theorem one_matching_for_all_rough_quotient_boundaries :
    ∃ F : ℕ → ℕ,(∀ n,F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n))) ∧
      (∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in atTop,((prefixUnpaid F X).card:ℝ) ≤ ε*X ∧ |(F X:ℝ)-X| ≤ ε*X) ∧
      ∀ (y : ℕ) (S : Finset ℕ) (a : ℕ → ℝ) (L U : ℕ),
        |quotientBoundary (coprimeMoebiusSum (primorial y)) S a L U-
          quotientBoundary (smoothLiftedPrefix (fixedSignedPrefix F) y) S a L U| ≤
        ((Real.log ((U:ℝ)+1)*Real.sqrt U+Real.log ((L:ℝ)+1)*Real.sqrt L)*deletionPrice (1/2) y)*
          (∑ q ∈ S,|a q|/Real.sqrt q) := by
  have top : Tendsto logBudget atTop atTop := Real.tendsto_log_atTop.comp
    (tendsto_atTop_mono (show ∀ n : ℕ,(n:ℝ) ≤ n+1 by intro n; linarith) tendsto_natCast_atTop_atTop)
  obtain ⟨F,legal,pop,cross⟩ := arbitrarily_slow_signed_crossings logBudget logBudget_nonneg top
  refine ⟨F,legal,pop,fun y S a L U => ?_⟩
  rw [two_cutoff_rough_quotient_flux F (fun n _ => legal n),add_sub_cancel_left]
  unfold quotientBoundary
  rw [mul_sum]
  apply (abs_sum_le_sum_abs ..).trans (sum_le_sum (fun q _ => ?_))
  rw [abs_mul]
  have atCut := lifted_crossing_at_one_cut (fun n => (cross n).1) y
  exact (mul_le_mul_of_nonneg_left ((abs_sub ..).trans (add_le_add (atCut U q) (atCut L q)))
    (abs_nonneg _)).trans_eq (by unfold logBudget; ring)

#print axioms smooth_lift_of_the_full_prefix
#print axioms signed_flux_along_a_quotient_history
#print axioms compose_quotient_boundaries
#print axioms two_cutoff_rough_quotient_flux
#print axioms one_matching_for_all_rough_quotient_boundaries

end GaloisForLFunctions.RestrictedFactorizationCalculus
