import GaloisForLFunctions.RestrictedFactorizationCalculus.ThePrimeErrorInTheCenteredUnitWindow
import GaloisForLFunctions.RHTower.QuasiRHQuotientHeadAndFiniteContactAbscissaLaw
import GaloisForLFunctions.HTGeometry.RpowPartialSumBound

/-!
# Independent prime windows on rough cofactors

Each cofactor can choose both endpoints of its own prime window and
change every proper prime-power weight. Summing the absolute errors
costs a power of the quotient scale and one floor residue per cofactor.
-/
noncomputable section
open Finset Filter ArithmeticFunction RHTower.CoprimeMobius
open GaloisForLFunctions.BezoutValuationIncidence
open scoped Classical Topology
namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- A sharp arithmetic interval after subtracting the original floor at both ends. -/
def centeredPrimeInterval (a : ArithmeticFunction ℝ) (y l u : ℕ) : ℝ :=
  ∑ q ∈ Ioc l u,(a-exactQuotientFloorWeight y) q

private theorem difference_at (a b : ArithmeticFunction ℝ) (q : ℕ) : (a-b) q=a q-b q := rfl

private theorem floor_residue (y t : ℕ) : quotientFloorCenter y t+((t%y:ℕ):ℝ)=t := by
  unfold quotientFloorCenter
  exact_mod_cast Nat.div_add_mod t y

/-- At every pair of endpoints above the sieve, the ordinary reading
exposes the two prime errors and precisely their two floor residues. -/
theorem centered_ordinary_prime_interval {y l u : ℕ} (first : y ≤ l) (order : l ≤ u) :
    centeredPrimeInterval (roughOrdinaryPrimeWeight y) y l u=
      (ordinaryThetaError u-ordinaryThetaError l)+((u%y:ℕ):ℝ)-((l%y:ℕ):ℝ) := by
  have primes := GaloisForLFunctions.WorldsOfTheZeroConfiguration.PrimeEdits.theta_sub_theta order
  have per (p : ℕ) (hp : p ∈ Ioc l u) : roughOrdinaryPrimeWeight y p=(if p.Prime then Real.log p else 0) := by
    change (if p.Prime ∧ y<p then Real.log p else 0)=_
    simp only [first.trans_lt (mem_Ioc.mp hp).1,and_true]
  simp only [centeredPrimeInterval,difference_at,sum_sub_distrib,exact_floor_weight_in_an_interval y order]
  rw [sum_congr rfl per,←primes]
  dsimp only [ordinaryThetaError]
  linarith only [floor_residue y u,floor_residue y l]

/-- Only the atoms inside the chosen interval need to agree on primes. -/
theorem proper_power_edits_in_a_prime_interval {y l u : ℕ} (a : ArithmeticFunction ℝ)
    (dom : ∀ q ∈ Ioc l u,|a q| ≤ vonMangoldt q)
    (fixed : ∀ q ∈ Ioc l u,q.Prime → a q=roughOrdinaryPrimeWeight y q) :
    |centeredPrimeInterval a y l u-centeredPrimeInterval (roughOrdinaryPrimeWeight y) y l u| ≤
      Chebyshev.psi u-Chebyshev.theta u := by
  simp only [centeredPrimeInterval,difference_at,sum_sub_distrib]
  rw [show ∀ v w t : ℝ,(v-t)-(w-t)=v-w from fun _ _ _ => by ring,←sum_sub_distrib]
  have per (q : ℕ) (hq : q ∈ Ioc l u) :
      |a q-roughOrdinaryPrimeWeight y q| ≤ (if ¬q.Prime then vonMangoldt q else 0) := by
    by_cases prime : q.Prime
    · simp [prime,fixed q hq prime]
    · simpa [prime,roughOrdinaryPrimeWeight] using dom q hq
  have sub : Ioc l u ⊆ Ioc 0 u := fun q h => mem_Ioc.mpr
    ⟨(Nat.zero_le l).trans_lt (mem_Ioc.mp h).1,(mem_Ioc.mp h).2⟩
  have grow := sum_le_sum_of_subset_of_nonneg (f := fun q => if ¬q.Prime then vonMangoldt q else 0)
    sub (fun _ _ _ => by split <;> first | exact vonMangoldt_nonneg | exact le_rfl)
  have eq := Chebyshev.psi_sub_theta_eq_sum_not_prime (u:ℝ)
  rw [Nat.floor_natCast,sum_filter] at eq
  exact (abs_sum_le_sum_abs ..).trans ((sum_le_sum per).trans (grow.trans eq.symm.le))

private theorem ordinary_theta_price {s : ℝ} (strip : RHTower.zetaZeroAbscissa<s) :
    ∃ C : ℝ,0<C ∧ ∀ n : ℕ,1 ≤ n → |ordinaryThetaError n| ≤ C*(n:ℝ)^s := by
  obtain ⟨C,cp,price⟩ := RHTower.exists_chebyshevTheta_error_power_bound_of_chebyshevErrorPowerSpectrum
    (sub_nonneg.mpr RHTower.half_le_zetaZeroAbscissa) (sub_pos.mpr strip)
    RHTower.chebyshevErrorPowerSpectrum_zetaZeroAbscissa_sub_half
  rw [show (1:ℝ)/2+(RHTower.zetaZeroAbscissa-1/2)+(s-RHTower.zetaZeroAbscissa)=s by ring] at price
  exact ⟨C,cp,fun n pn => price n (Nat.one_le_cast.mpr pn)⟩

/-- The price depends on the upper endpoint of each actual window.
The sieve contributes a single residue per row. -/
theorem price_of_an_independent_prime_interval {s : ℝ} (strip : RHTower.zetaZeroAbscissa<s) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ y l u : ℕ,0<y → y ≤ l → l ≤ u → ∀ a : ArithmeticFunction ℝ,
      (∀ q ∈ Ioc l u,|a q| ≤ vonMangoldt q) → (∀ q ∈ Ioc l u,q.Prime → a q=roughOrdinaryPrimeWeight y q) →
      |centeredPrimeInterval a y l u| ≤ C*(u:ℝ)^s+y := by
  obtain ⟨A,ap,price⟩ := ordinary_theta_price strip
  obtain ⟨D,powers⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  have hs := RHTower.half_le_zetaZeroAbscissa.trans_lt strip
  have sp := (by norm_num : (0:ℝ)<1/2).trans hs
  refine ⟨2*A+max 0 D,by positivity,fun y l u yp yl lu a dom fixed => ?_⟩
  let W := centeredPrimeInterval (roughOrdinaryPrimeWeight y) y l u
  have diff := (proper_power_edits_in_a_prime_interval a dom fixed).trans (powers u)
  have lp := yp.trans_le yl
  have up := lp.trans_le lu
  have root : Real.sqrt u ≤ (u:ℝ)^s := by
    rw [Real.sqrt_eq_rpow]; exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr up) hs.le
  have extra := diff.trans (mul_le_mul (le_max_right 0 D) root (Real.sqrt_nonneg _) (le_max_left ..))
  have low := (price l lp).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.cast_le.mpr lu) sp.le) ap.le)
  have endpoint := (abs_sub _ _).trans (add_le_add (price u up) low)
  have residues : |((u%y:ℕ):ℝ)-((l%y:ℕ):ℝ)| ≤ y := by
    have hu := Nat.cast_le.mpr (α := ℝ) (Nat.mod_lt u yp).le
    have hl := Nat.cast_le.mpr (α := ℝ) (Nat.mod_lt l yp).le
    exact abs_le.mpr ⟨by linarith only [hl,Nat.cast_nonneg (α := ℝ) (u%y)],
      by linarith only [hu,Nat.cast_nonneg (α := ℝ) (l%y)]⟩
  have plain : |W| ≤ A*(u:ℝ)^s+A*(u:ℝ)^s+y := by
    dsimp only [W]
    rw [centered_ordinary_prime_interval yl lu,show ∀ z v w : ℝ,z+v-w=z+(v-w) from fun _ _ _ => by ring]
    exact (abs_add_le ..).trans (add_le_add endpoint residues)
  have tri := abs_add_le (centeredPrimeInterval a y l u-W) W
  rw [sub_add_cancel] at tri
  change |centeredPrimeInterval a y l u-W| ≤ _ at extra
  linarith only [tri,plain,extra]

/-- All subwindows can be chosen independently at their own cofactor.
The estimate pays for their absolute values, including both endpoints
and all proper-power changes, before any Möbius signs are summed. -/
theorem absolute_price_of_independent_quotient_subwindows {s : ℝ} (strip : RHTower.zetaZeroAbscissa<s) (small : s<1) :
    ∃ C : ℝ,0 ≤ C ∧ ∀ y X Z : ℕ,0<y → ∀ S : Finset ℕ,S ⊆ Icc 1 Z →
      ∀ l u : ℕ → ℕ,(∀ m ∈ S,y ≤ l m ∧ l m ≤ u m ∧ u m ≤ X/m) →
      ∀ a : ℕ → ArithmeticFunction ℝ,
      (∀ m ∈ S,∀ q ∈ Ioc (l m) (u m),|a m q| ≤ vonMangoldt q) →
      (∀ m ∈ S,∀ q ∈ Ioc (l m) (u m),q.Prime → a m q=roughOrdinaryPrimeWeight y q) →
      (∑ m ∈ S,|centeredPrimeInterval (a m) y (l m) (u m)|) ≤
        C*(X:ℝ)^s*(Z:ℝ)^(1-s)+(y:ℝ)*S.card := by
  obtain ⟨A,ap,price⟩ := price_of_an_independent_prime_interval strip
  have sp := (by norm_num : (0:ℝ)<1/2).trans (RHTower.half_le_zetaZeroAbscissa.trans_lt strip)
  have dp := sub_pos.mpr small
  refine ⟨A/(1-s),div_nonneg ap dp.le,fun y X Z yp S sub l u supported a dom fixed => ?_⟩
  have per (m : ℕ) (hm : m ∈ S) :
      |centeredPrimeInterval (a m) y (l m) (u m)| ≤ A*(X:ℝ)^s*(m:ℝ)^(-s)+y := by
    obtain ⟨yl,lu,ux⟩ := supported m hm
    have mp := (mem_Icc.mp (sub hm)).1
    have hi : (u m:ℝ) ≤ (X:ℝ)/m := (Nat.cast_le.mpr ux).trans ((le_div_iff₀ (Nat.cast_pos.mpr mp)).mpr
      (by exact_mod_cast Nat.div_mul_le_self X m))
    have pow := Real.rpow_le_rpow (Nat.cast_nonneg _) hi sp.le
    rw [Real.div_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)] at pow
    apply (price y (l m) (u m) yp yl lu _ (dom m hm) (fixed m hm)).trans
    rw [Real.rpow_neg (Nat.cast_nonneg _)]
    exact add_le_add ((mul_le_mul_of_nonneg_left pow ap).trans_eq (by ring)) le_rfl
  have finite := sum_le_sum_of_subset_of_nonneg (f := fun m : ℕ => (m:ℝ)^(-s)) sub
    (fun m _ _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have allm : (∑ m ∈ Icc 1 Z,(m:ℝ)^(-s)) ≤ (Z:ℝ)^(1-s)/(1-s) := by
    have h := HTGeometry.sum_rpow_sub_one_le dp (by linarith only [sp] : (1:ℝ)-s<1) Z
    rw [show (1:ℝ)-s-1= -s by ring] at h
    rw [sum_Icc_eq_sum_range]
    simpa only [Nat.add_sub_cancel,Nat.cast_add,Nat.cast_one,add_comm (1:ℝ)] using h
  have summed := sum_le_sum per
  rw [sum_add_distrib,←mul_sum,sum_const,nsmul_eq_mul] at summed
  have mult := mul_le_mul_of_nonneg_left (finite.trans allm) (mul_nonneg ap (Real.rpow_nonneg (Nat.cast_nonneg X) s))
  exact summed.trans ((add_le_add mult le_rfl).trans_eq (by ring))

#print axioms absolute_price_of_independent_quotient_subwindows
#print axioms centered_ordinary_prime_interval
end GaloisForLFunctions.RestrictedFactorizationCalculus
