import GaloisForLFunctions.RestrictedFactorizationCalculus.IndependentPrimeWindowsOnRoughCofactors
import GaloisForLFunctions.RestrictedFactorizationCalculus.BothSignsInTheCenteredUnitWindow
import GaloisForLFunctions.RestrictedFactorizationCalculus.PrimeSupplyAtTheCubeRootBoundary

/-!
# A shared prime excursion across polynomially many quotient windows

Every prime cofactor above the sieve has negative sign. The very same
prime-error excursion can occur in all its allowed quotient subwindows.
Independent choices of signed proper powers cannot remove either sign.
-/
noncomputable section
open Finset Filter ArithmeticFunction RHTower.CoprimeMobius
open scoped Classical Topology
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

private theorem sign_of_a_prime_cofactor {y p : ℕ} (hp : p.Prime) (above : y<p) : RoughReading.row y p= -1 := by
  have good := (isFree_prime (RoughReading.banned y) hp).mpr (not_le.mpr above)
  rw [RoughReading.row_value,if_pos good,moebius_apply_prime hp]
  norm_num

/-- The common ordinary window (y,T] contributes its error once for
every chosen prime cofactor. The floor at the prime wall is exact. -/
theorem one_prime_interval_at_every_selected_prime_cofactor {y T : ℕ} (order : y ≤ T) (S : Finset ℕ)
    (prime : ∀ m ∈ S,m.Prime ∧ y< m) :
    (∑ m ∈ S,RoughReading.row y m*centeredPrimeInterval (roughOrdinaryPrimeWeight y) y y T)=
      -(S.card:ℝ)*(ordinaryThetaError T-ordinaryThetaError y+((T%y:ℕ):ℝ)) := by
  simp only [centered_ordinary_prime_interval le_rfl order,Nat.mod_self,Nat.cast_zero,sub_zero]
  rw [sum_congr rfl (fun m hm => congrArg (fun z : ℝ => z*_) (sign_of_a_prime_cofactor (prime m hm).1 (prime m hm).2))]
  rw [sum_const,nsmul_eq_mul]
  ring

/-- Uniformly up to the square root in the sieve, all edited prime
windows differ from the genuine top prime error by only O(√T). -/
private theorem cost_at_the_lower_sieve_endpoint :
    ∃ D : ℝ,0 ≤ D ∧ ∀ y T : ℕ,1 ≤ y → y ≤ T → (y:ℝ) ≤ Real.sqrt T →
      ∀ a : ArithmeticFunction ℝ,(∀ q ∈ Ioc y T,|a q| ≤ vonMangoldt q) →
      (∀ q ∈ Ioc y T,q.Prime → a q=roughOrdinaryPrimeWeight y q) →
      |centeredPrimeInterval a y y T-ordinaryThetaError T| ≤ D*Real.sqrt T := by
  obtain ⟨C,primePower⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have lc : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  refine ⟨max 0 C+Real.log 4+2,by positivity,fun y T yp yT small a dom fix => ?_⟩
  have extra := (proper_power_edits_in_a_prime_interval a dom fix).trans ((primePower T).trans
    (mul_le_mul_of_nonneg_right (le_max_right 0 C) (Real.sqrt_nonneg _)))
  have prime := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (α := ℝ) y)
  have per : |ordinaryThetaError y| ≤ (Real.log 4+1)*(y:ℝ) := by
    change |Chebyshev.theta y-y| ≤ _
    have tri := abs_sub (Chebyshev.theta y) (y:ℝ)
    rw [abs_of_nonneg (Chebyshev.theta_nonneg _),abs_of_nonneg (Nat.cast_nonneg _)] at tri
    linarith only [tri,prime]
  have residue : ((T%y:ℕ):ℝ) ≤ y := Nat.cast_le.mpr (Nat.mod_lt _ yp).le
  let b := roughOrdinaryPrimeWeight y
  have lower : |centeredPrimeInterval b y y T-ordinaryThetaError T| ≤ (Real.log 4+2)*y := by
    rw [centered_ordinary_prime_interval le_rfl yT,Nat.mod_self,Nat.cast_zero,sub_zero,
      show ordinaryThetaError T-ordinaryThetaError y+((T%y:ℕ):ℝ)-ordinaryThetaError T=((T%y:ℕ):ℝ)-ordinaryThetaError y by ring]
    apply (abs_sub ..).trans
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    linarith only [residue,per]
  have big := lower.trans (mul_le_mul_of_nonneg_left small (by linarith only [lc]))
  have tri := abs_sub_le (centeredPrimeInterval a y y T) (centeredPrimeInterval b y y T) (ordinaryThetaError T)
  change |centeredPrimeInterval a y y T-centeredPrimeInterval b y y T| ≤ _ at extra
  linarith only [tri,big,extra]

/-- For either sign, one sequence of observations works for all sieve
walls up to √T and for every family of signed proper-power selections.
All chosen prime cofactors can use the common physical interval (y,T]. -/
theorem simultaneous_excursions_repeated_at_prime_cofactors :
    ∃ δ : ℝ,0<δ ∧ ∀ σ : ℝ,σ=1 ∨ σ= -1 →
      ∃ᶠ T : ℕ in atTop,∀ y : ℕ,1 ≤ y → y ≤ T → (y:ℝ) ≤ Real.sqrt T →
        ∀ S : Finset ℕ,(∀ m ∈ S,m.Prime ∧ y< m) → ∀ a : ℕ → ArithmeticFunction ℝ,
        (∀ m ∈ S,∀ q ∈ Ioc y T,|a m q| ≤ vonMangoldt q) →
        (∀ m ∈ S,∀ q ∈ Ioc y T,q.Prime → a m q=roughOrdinaryPrimeWeight y q) →
        (S.card:ℝ)*(δ*Real.sqrt T*Real.log (Real.log (Real.log T))) ≤
          -σ*∑ m ∈ S,RoughReading.row y m*centeredPrimeInterval (a m) y y T := by
  obtain ⟨D,d0,cost⟩ := cost_at_the_lower_sieve_endpoint
  let c := RHTower.littlewoodConst/28
  have cp : 0<c := div_pos RHTower.littlewoodConst_pos (by norm_num)
  refine ⟨c/4,div_pos cp (by norm_num),fun σ dir => frequently_atTop.mpr (fun N => ?_)⟩
  obtain ⟨t,size,record,large,_⟩ := oriented_prime_error_records σ dir (2*D) (max N 1)
  have tp := (le_max_right N 1).trans size
  have root := Real.sqrt_pos.mpr (Nat.cast_pos.mpr tp)
  have pay := (lt_div_iff₀ root).mp record
  have gain := (lt_div_iff₀ root).mp large
  refine ⟨t,(le_max_left N 1).trans size,fun y yp yt small S prime a dom fix => ?_⟩
  have per (m : ℕ) (hm : m ∈ S) : c/4*Real.sqrt t*Real.log (Real.log (Real.log t)) ≤
      -σ*(RoughReading.row y m*centeredPrimeInterval (a m) y y t) := by
    rw [sign_of_a_prime_cofactor (prime m hm).1 (prime m hm).2,neg_one_mul,neg_mul_neg]
    have bound := cost y t yp yt small (a m) (dom m hm) (fix m hm)
    have oriented : |σ*(centeredPrimeInterval (a m) y y t-ordinaryThetaError t)| ≤ D*Real.sqrt t := by
      rcases dir with h | h <;> simpa only [h,one_mul,neg_one_mul,abs_neg] using bound
    change c/2*Real.log (Real.log (Real.log t))*Real.sqrt t < σ*ordinaryThetaError t at gain
    linarith only [(abs_le.mp oriented).1,pay,gain]
  simpa only [sum_const,nsmul_eq_mul,←mul_sum] using sum_le_sum per

#print axioms one_prime_interval_at_every_selected_prime_cofactor
#print axioms simultaneous_excursions_repeated_at_prime_cofactors
end GaloisForLFunctions.RestrictedFactorizationCalculus
