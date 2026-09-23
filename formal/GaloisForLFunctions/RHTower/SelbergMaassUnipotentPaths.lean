import GaloisForLFunctions.RHTower.SelbergMaassUnipotentBlocks
import GaloisForLFunctions.RHTower.SelbergMaassChordEnergy
import GaloisForLFunctions.RHTower.SelbergMaassCurrentCurvature
import GaloisForLFunctions.RHTower.SelbergMaassCurrentTransport
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# Complete unipotent block motion and original current periods

Augmented source chords are exactly normalized literal modular displacements,
including common zeros. Modular inversion identifies each lower unipotent
motion with a signed upper horizontal path. The complete block comparison is
therefore controlled by its original resistance/current path integrals.

Both integrands are periodic with period one. Their signed integer integrals
scale linearly, so the path product has exact quadratic scaling. The complete
block parameter moment is N(2N+1)/12. All paths reduce to two original heights,
with the invariant mean and the full pair, phase and regulator-gradient energy
retained. No uniform resistance or quotient-area comparison is assumed.
-/

open Complex Set UpperHalfPlane ModularGroup MeasureTheory
open scoped BigOperators
namespace GaloisForLFunctions.RHTower.SelbergMaassUnipotentPaths
open SelbergMaassCongruenceTrace SelbergMaassCongruenceAverage SelbergMaassMean
open SelbergMaassGeneratorComparison SelbergMaassUnipotentBlocks
open SelbergMaassAugmentedDirection SelbergMaassTraceRegularized
open SelbergMaassChordEnergy SelbergMaassPairPhaseEnergy SelbergMaassTraceRadial
open SelbergMaassSourceCurrents SelbergMaassCurrentTransport SelbergMaassTraceEnergy SelbergMaassTraceBoundary
open GaloisForLFunctions.HTGeometry.FiniteRingSl2
noncomputable section

/-- Literal upper elementary matrices are integer translation powers. -/
theorem upper_eq_T_zpow (j : ℤ) : upper j=T^j := by
  apply Subtype.ext
  exact (ModularGroup.coe_T_zpow j).symm

/-- Literal lower motion is conjugated upper motion with opposite parameter. -/
theorem lower_eq_conjugate_upper (j : ℤ) : lower j=S*upper (-j)*S⁻¹ := by
  have h : lower j*S=S*upper (-j) := by
    apply Matrix.SpecialLinearGroup.ext
    intro i k
    fin_cases i <;> fin_cases k <;>
      simp [lower,upper,ModularGroup.S,Matrix.SpecialLinearGroup.coe_mul]
  rw [← h,mul_assoc,mul_inv_cancel,mul_one]

/-- The actual horizontal endpoint chart of an integer upper motion. -/
theorem upper_smul_eq_point (j : ℤ) (z : ℍ) :
    upper j • z=ofComplex (point (z.re+j) z.im) := by
  rw [upper_eq_T_zpow,modular_T_zpow_smul]
  apply UpperHalfPlane.ext
  rw [ofComplex_apply_of_im_pos (by simpa [point] using z.im_pos)]
  rw [coe_vadd]
  apply Complex.ext <;> simp [point,add_comm]

theorem ofComplex_point_self (z : ℍ) : ofComplex (point z.re z.im)=z := by
  have h : point z.re z.im=(z:ℂ) := by apply Complex.ext <;> simp [point]
  rw [h,ofComplex_apply]

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N+1))) lam)
    (e : Ioi (0:ℝ))

/-- Both augmented endpoints transform by the same complete coordinate permutation. -/
theorem augmented_chord_modular (A : SL2Z) (z w : ℍ) :
    distanceSq N f e (A • z) (A • w)=distanceSq N f e z w := by
  unfold distanceSq
  simp only [unit_equivariant,Fintype.sum_option,Option.map_none,Option.map_some]
  congr 1
  exact Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk A : Deck N))
    (fun q : Deck N => normSq (unit N f e (some q) (w:ℂ)-unit N f e (some q) (z:ℂ)))

/-- Exact regulated reconstruction of an original modular displacement, including nodes. -/
theorem displacementEnergy_eq_radius_sq_mul_augmented_chord (A : SL2Z) (z : ℍ) :
    displacementEnergy N f A z=radius N f e (z:ℂ)^(2 : ℕ)*distanceSq N f e z (A • z) := by
  have h (q : Deck N) :
      (quotientForm N f q).1.1 (A • z)-(quotientForm N f q).1.1 z=
        (radius N f e (z:ℂ):ℂ)*(unit N f e (some q) (A • z : ℍ)-unit N f e (some q) (z:ℂ)) := by
    have hz := radius_mul_unit N f e (some q) (z:ℂ)
    have hw := radius_mul_unit N f e (some q) (A • z : ℍ)
    simp only [SelbergMaassAugmentedDirection.source,ofComplex_apply] at hz hw
    rw [radius_invariant] at hw
    rw [mul_sub,hw,hz]
  unfold displacementEnergy distanceSq
  rw [Fintype.sum_option]
  have heq : unit N f e none (A • z : ℍ)=unit N f e none (z:ℂ) := by
    simp only [SelbergMaassAugmentedDirection.unit,SelbergMaassAugmentedDirection.source,radius_invariant]
  simp only [heq,sub_self,normSq_zero,zero_add,h,normSq_mul,Complex.normSq_ofReal,← pow_two]
  rw [Finset.mul_sum]

/-- Every lower chord is the upper chord on the literal inverted source point. -/
theorem lower_augmented_chord_eq (j : ℤ) (z : ℍ) :
    distanceSq N f e z (lower j • z)=
      distanceSq N f e (S⁻¹ • z) (upper (-j) • (S⁻¹ • z)) := by
  rw [← augmented_chord_modular N f e S (S⁻¹ • z) (upper (-j) • (S⁻¹ • z)),
    smul_inv_smul,lower_eq_conjugate_upper,mul_smul,mul_smul]

/-- The full actual resistance/current cost of one signed horizontal displacement. -/
def horizontalCost (z : ℍ) (j : ℤ) : ℝ :=
  pathResistance N f e z.im z.re (z.re+j)*pathEnergy N f e z.im z.re (z.re+j)

/-- Actual horizontal displacement is controlled by its complete retained path cost. -/
theorem upper_augmented_chord_le (j : ℤ) (z : ℍ) :
    distanceSq N f e z (upper j • z) ≤ horizontalCost N f e z j := by
  have h := chord_le_oriented_resistance_energy N f e z.im_pos z.re (z.re+j)
  rw [ofComplex_point_self,← upper_smul_eq_point] at h
  exact h

/-- The inverted horizontal path controls every lower block motion. -/
theorem lower_augmented_chord_le (j : ℤ) (z : ℍ) :
    distanceSq N f e z (lower j • z) ≤ horizontalCost N f e (S⁻¹ • z) (-j) := by
  rw [lower_augmented_chord_eq]
  exact upper_augmented_chord_le N f e (-j) (S⁻¹ • z)

/-- Both signs of each literal path retain nonnegative resistance times current energy. -/
theorem horizontalCost_nonneg (z : ℍ) (j : ℤ) : 0 ≤ horizontalCost N f e z j := by
  exact (Finset.sum_nonneg (fun _ _ => normSq_nonneg _)).trans (upper_augmented_chord_le N f e j z)

/-- All original upper and inverted lower path costs with their exact block normalization. -/
def blockPathCost (z : ℍ) : ℝ :=
  (2*(N+1:ℕ):ℝ)⁻¹*((∑ j : Multiplicative (ZMod (N+1)), horizontalCost N f e z (j.toAdd.val:ℤ))+
    ∑ j : Multiplicative (ZMod (N+1)), horizontalCost N f e (S⁻¹ • z) (-(j.toAdd.val:ℤ)))

theorem blockPathCost_nonneg (z : ℍ) : 0 ≤ blockPathCost N f e z := by
  exact mul_nonneg (by positivity) (add_nonneg
    (Finset.sum_nonneg (fun _ _ => horizontalCost_nonneg N f e _ _))
    (Finset.sum_nonneg (fun _ _ => horizontalCost_nonneg N f e _ _)))

/-- Complete original block energy is controlled by the actual regularized current paths. -/
theorem blockEnergy_le_radius_sq_mul_pathCost (z : ℍ) :
    blockEnergy N f z ≤ radius N f e (z:ℂ)^(2 : ℕ)*blockPathCost N f e z := by
  have hu (j : Multiplicative (ZMod (N+1))) := mul_le_mul_of_nonneg_left
    (upper_augmented_chord_le N f e (j.toAdd.val:ℤ) z) (sq_nonneg (radius N f e (z:ℂ)))
  have hl (j : Multiplicative (ZMod (N+1))) := mul_le_mul_of_nonneg_left
    (lower_augmented_chord_le N f e (j.toAdd.val:ℤ) z) (sq_nonneg (radius N f e (z:ℂ)))
  simp only [← displacementEnergy_eq_radius_sq_mul_augmented_chord] at hu hl
  have h := mul_le_mul_of_nonneg_left (add_le_add
    (Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hu j))
    (Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hl j)))
    (by positivity : 0 ≤ (2*(N+1:ℕ):ℝ)⁻¹)
  simpa only [← Finset.mul_sum,← mul_add,mul_left_comm,blockEnergy,blockPathCost] using h

/-- The complete source comparison retains invariant mean, regularization, and every current path. -/
theorem density_le_mean_add_pathCost (z : ℍ) :
    density N f z ≤ (Fintype.card (Deck N):ℝ)*normSq (sourceMean N f z)+
      16*(density N f z+(e:ℝ)^(2 : ℕ))*blockPathCost N f e z := by
  have h := density_le_mean_add_blockEnergy N f z
  have hc := blockEnergy_le_radius_sq_mul_pathCost N f e z
  rw [radius_sq,ofComplex_apply] at hc
  nlinarith

/-- Mean-zero sources retain a quantitative original-density lower demand on every regulator. -/
theorem density_fraction_le_pathCost_of_mean_zero (z : ℍ) (hm : sourceMean N f z=0) :
    density N f z/(density N f z+(e:ℝ)^(2 : ℕ)) ≤ 16*blockPathCost N f e z := by
  have h := density_le_mean_add_pathCost N f e z
  simp only [hm,normSq_zero,mul_zero,zero_add] at h
  apply (div_le_iff₀ (by simpa only [ofComplex_apply] using denominator_pos N f e (z:ℂ))).2
  nlinarith

/-- The literal horizontal current density retains pair, phase and regulator-gradient terms. -/
def horizontalCurrentDensity (z : ℂ) : ℝ :=
  (pairEnergy N f 1 z+phaseCurrent N f 1 z^(2 : ℕ)+
    (e:ℝ)^(2 : ℕ)*directionalEnergy N f 1 (ofComplex z))/radius N f e z^(3 : ℕ)

/-- Exact source identification, with no common-zero deletion or limit interchange. -/
theorem horizontalCurrentDensity_eq (z : ℍ) :
    horizontalCurrentDensity N f e (z:ℂ)=
      directionalRemainder N f e 1 z/radius N f e (z:ℂ) := by
  have h := regularized_pair_phase_identity N f e 1 z
  have hr := radius_sq N f e (z:ℂ)
  simp only [ofComplex_apply] at hr
  rw [← hr] at h
  rw [horizontalCurrentDensity,ofComplex_apply,← h]
  field_simp [(radius_pos N f e (z:ℂ)).ne']

/-- The path energy is exactly the integral of its retained original current density. -/
theorem pathEnergy_eq_current_integral {y : ℝ} (hy : 0 < y) (a b : ℝ) :
    pathEnergy N f e y a b=∫ x in a..b, horizontalCurrentDensity N f e (point x y) := by
  unfold pathEnergy
  apply intervalIntegral.integral_congr
  intro x _
  have h := horizontalCurrentDensity_eq N f e (ofComplex (point x y))
  have hp : ((ofComplex (point x y):ℍ):ℂ)=point x y := by
    rw [ofComplex_apply_of_im_pos (by simpa [point] using hy : 0 < (point x y).im)]
  rw [hp] at h
  exact h.symm

/-- Integer translation has identity complex differential. -/
theorem denom_T (z : ℍ) : denom T z=1 := by simp [denom,ModularGroup.T]

/-- The original complete horizontal derivative energy has period one. -/
theorem directionalEnergy_T (z : ℍ) : directionalEnergy N f 1 (T • z)=directionalEnergy N f 1 z := by
  have hd (q : Deck N) := field_dir_modular N f q T z 1
  simp only [denom_T,one_pow,div_one,one_mul] at hd
  change (∑ q : Deck N, normSq (dir 1 (field N f q) (T • z : ℍ)))=
    ∑ q : Deck N, normSq (dir 1 (field N f q) (z:ℂ))
  simp_rw [hd]
  exact Equiv.sum_comp (Equiv.mulRight (QuotientGroup.mk T : Deck N))
    (fun q : Deck N => normSq (dir 1 (field N f q) (z:ℂ)))

/-- The original regulated horizontal current density has period one. -/
theorem horizontalCurrentDensity_T (z : ℍ) :
    horizontalCurrentDensity N f e (T • z : ℍ)=horizontalCurrentDensity N f e (z:ℂ) := by
  have hc := current_modular N f T z 1
  simp only [denom_T,one_pow,div_one,one_mul] at hc
  rw [horizontalCurrentDensity_eq,horizontalCurrentDensity_eq,directionalRemainder_eq,
    directionalRemainder_eq,directionalEnergy_T,← hc,density_invariant,radius_invariant]

theorem coe_ofComplex_point (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ((ofComplex (point x y):ℍ):ℂ)=point x y := by
  rw [ofComplex_apply_of_im_pos (by simpa [point] using hy : 0 < (point x y).im)]

theorem point_T (x : ℝ) {y : ℝ} (hy : 0 < y) :
    T • ofComplex (point x y)=ofComplex (point (x+1) y) := by
  have h := upper_smul_eq_point 1 (ofComplex (point x y))
  have hr : (ofComplex (point x y)).re=x := by
    change (((ofComplex (point x y):ℍ):ℂ)).re=x
    rw [coe_ofComplex_point x hy]; simp [point]
  have hi : (ofComplex (point x y)).im=y := by
    change (((ofComplex (point x y):ℍ):ℂ)).im=y
    rw [coe_ofComplex_point x hy]; simp [point]
  simpa only [upper_eq_T_zpow,zpow_one,Int.cast_one,hr,hi] using h

/-- The literal reciprocal-radius integrand is periodic with period one. -/
theorem reciprocal_radius_periodic {y : ℝ} (hy : 0 < y) :
    Function.Periodic (fun x => 1/radius N f e (point x y)) 1 := by
  intro x
  have h := radius_invariant N f e T (ofComplex (point x y))
  rw [point_T x hy,coe_ofComplex_point (x+1) hy,coe_ofComplex_point x hy] at h
  change 1/radius N f e (point (x+1) y)=1/radius N f e (point x y)
  rw [h]

/-- The literal regulated current integrand is periodic with period one. -/
theorem horizontalCurrentDensity_periodic {y : ℝ} (hy : 0 < y) :
    Function.Periodic (fun x => horizontalCurrentDensity N f e (point x y)) 1 := by
  intro x
  have h := horizontalCurrentDensity_T N f e (ofComplex (point x y))
  rw [point_T x hy,coe_ofComplex_point (x+1) hy,coe_ofComplex_point x hy] at h
  exact h

/-- Resistance over a signed integer number of periods is exactly that integer times one period. -/
theorem pathResistance_integer {y : ℝ} (hy : 0 < y) (a : ℝ) (j : ℤ) :
    pathResistance N f e y a (a+j)=(j:ℝ)*pathResistance N f e y a (a+1) := by
  have h := (reciprocal_radius_periodic N f e hy).intervalIntegral_add_zsmul_eq j a
    (fun b c => (continuous_const.div (radius_slice_continuous N f e hy)
      (fun x => (radius_pos N f e (point x y)).ne')).intervalIntegrable b c)
  simpa only [pathResistance,SelbergWeightedPathEnergy.resistance,zsmul_eq_mul,mul_one] using h

/-- Retained current energy over signed integer periods has the same exact linear scaling. -/
theorem pathEnergy_integer {y : ℝ} (hy : 0 < y) (a : ℝ) (j : ℤ) :
    pathEnergy N f e y a (a+j)=(j:ℝ)*pathEnergy N f e y a (a+1) := by
  have hi (b c : ℝ) : IntervalIntegrable (fun x => horizontalCurrentDensity N f e (point x y)) volume b c := by
    have he : (fun x => horizontalCurrentDensity N f e (point x y))=
        (fun x => directionalRemainder N f e 1 (ofComplex (point x y))/radius N f e (point x y)) := by
      funext x
      have h := horizontalCurrentDensity_eq N f e (ofComplex (point x y))
      rwa [coe_ofComplex_point x hy] at h
    rw [he]
    exact path_energy_intervalIntegrable N f e hy b c
  have h := (horizontalCurrentDensity_periodic N f e hy).intervalIntegral_add_zsmul_eq j a hi
  simpa only [pathEnergy_eq_current_integral N f e hy,zsmul_eq_mul,mul_one] using h

/-- The actual resistance/current path product grows exactly quadratically with integer length. -/
theorem horizontalCost_integer (z : ℍ) (j : ℤ) :
    horizontalCost N f e z j=(j:ℝ)^(2 : ℕ)*horizontalCost N f e z 1 := by
  unfold horizontalCost
  rw [pathResistance_integer N f e z.im_pos,pathEnergy_integer N f e z.im_pos]
  simp only [Int.cast_one]
  ring

/-- Complete normalized squared parameter moment of the actual unipotent block. -/
def parameterMoment (N : ℕ) : ℝ :=
  (2*(N+1:ℕ):ℝ)⁻¹*∑ j : Multiplicative (ZMod (N+1)), (j.toAdd.val:ℝ)^(2 : ℕ)

/-- Every actual complete block cost is exactly one parameter moment times two unit-path costs. -/
theorem blockPathCost_eq_parameterMoment (z : ℍ) :
    blockPathCost N f e z=parameterMoment N*
      (horizontalCost N f e z 1+horizontalCost N f e (S⁻¹ • z) 1) := by
  have hu : (∑ j : Multiplicative (ZMod (N+1)), horizontalCost N f e z (j.toAdd.val:ℤ))=
      (∑ j : Multiplicative (ZMod (N+1)), (j.toAdd.val:ℝ)^(2 : ℕ))*horizontalCost N f e z 1 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simpa only [Int.cast_natCast] using horizontalCost_integer N f e z (j.toAdd.val:ℤ)
  have hl : (∑ j : Multiplicative (ZMod (N+1)), horizontalCost N f e (S⁻¹ • z) (-(j.toAdd.val:ℤ)))=
      (∑ j : Multiplicative (ZMod (N+1)), (j.toAdd.val:ℝ)^(2 : ℕ))*horizontalCost N f e (S⁻¹ • z) 1 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    simpa only [Int.cast_natCast,Int.cast_neg,neg_sq] using
      horizontalCost_integer N f e (S⁻¹ • z) (-(j.toAdd.val:ℤ))
  rw [blockPathCost,hu,hl,parameterMoment]
  ring

/-- The finite sum of squared integer parameters is obtained by polynomial induction. -/
theorem sum_fin_sq (n : ℕ) : (∑ j : Fin n, (j.val:ℝ)^(2 : ℕ))=(n:ℝ)*((n:ℝ)-1)*(2*(n:ℝ)-1)/6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.val_castSucc,Fin.val_last,ih,Nat.cast_add,Nat.cast_one]
    ring

/-- Exact level dependence of this actual geometric path comparison. -/
theorem parameterMoment_eq (N : ℕ) : parameterMoment N=(N:ℝ)*(2*(N:ℝ)+1)/12 := by
  have h := Equiv.sum_comp (Multiplicative.ofAdd : ZMod (N+1) ≃ Multiplicative (ZMod (N+1)))
    (fun j : Multiplicative (ZMod (N+1)) => (j.toAdd.val:ℝ)^(2 : ℕ))
  simp only [toAdd_ofAdd] at h
  have hs : (∑ j : Multiplicative (ZMod (N+1)), (j.toAdd.val:ℝ)^(2 : ℕ))=
      (∑ j : Fin (N+1), (j.val:ℝ)^(2 : ℕ)) := h.symm
  rw [parameterMoment,hs,sum_fin_sq]
  push_cast
  field_simp
  ring

/-- The source comparison is reduced to two one-period current costs with its exact level factor. -/
theorem density_le_mean_add_two_unit_costs (z : ℍ) :
    density N f z ≤ (Fintype.card (Deck N):ℝ)*normSq (sourceMean N f z)+
      (4/3:ℝ)*(N:ℝ)*(2*(N:ℝ)+1)*(density N f z+(e:ℝ)^(2 : ℕ))*
        (horizontalCost N f e z 1+horizontalCost N f e (S⁻¹ • z) 1) := by
  have h := density_le_mean_add_pathCost N f e z
  rw [blockPathCost_eq_parameterMoment,parameterMoment_eq] at h
  nlinarith

/-- One complete horizontal period of literal inverse-amplitude resistance. -/
def periodResistance (y : ℝ) : ℝ := pathResistance N f e y 0 1

/-- One complete horizontal period of the retained pair, phase and regulator current energy. -/
def periodCurrentEnergy (y : ℝ) : ℝ := pathEnergy N f e y 0 1

/-- The complete one-period resistance/current cost at a specified original height. -/
def periodCost (y : ℝ) : ℝ := periodResistance N f e y*periodCurrentEnergy N f e y

theorem pathResistance_one_period {y : ℝ} (hy : 0 < y) (a : ℝ) :
    pathResistance N f e y a (a+1)=periodResistance N f e y := by
  simpa only [pathResistance,SelbergWeightedPathEnergy.resistance,periodResistance,zero_add] using
    (reciprocal_radius_periodic N f e hy).intervalIntegral_add_eq a 0

theorem pathEnergy_one_period {y : ℝ} (hy : 0 < y) (a : ℝ) :
    pathEnergy N f e y a (a+1)=periodCurrentEnergy N f e y := by
  simpa only [periodCurrentEnergy,pathEnergy_eq_current_integral N f e hy,zero_add] using
    (horizontalCurrentDensity_periodic N f e hy).intervalIntegral_add_eq a 0

/-- The original signed path cost depends only on its height and squared integer length. -/
theorem horizontalCost_eq_periodCost (z : ℍ) (j : ℤ) :
    horizontalCost N f e z j=(j:ℝ)^(2 : ℕ)*periodCost N f e z.im := by
  rw [horizontalCost_integer,horizontalCost]
  simp only [Int.cast_one,pathResistance_one_period N f e z.im_pos,
    pathEnergy_one_period N f e z.im_pos,periodCost]

/-- Exact reduction of every literal block path to two full horizontal periods. -/
theorem blockPathCost_eq_two_periods (z : ℍ) :
    blockPathCost N f e z=(N:ℝ)*(2*(N:ℝ)+1)/12*
      (periodCost N f e z.im+periodCost N f e (S⁻¹ • z).im) := by
  rw [blockPathCost_eq_parameterMoment,parameterMoment_eq,
    horizontalCost_eq_periodCost,horizontalCost_eq_periodCost]
  simp

/-- Complete density control by two source current periods, including its invariant mean and nodes. -/
theorem density_le_mean_add_two_periods (z : ℍ) :
    density N f z ≤ (Fintype.card (Deck N):ℝ)*normSq (sourceMean N f z)+
      (4/3:ℝ)*(N:ℝ)*(2*(N:ℝ)+1)*(density N f z+(e:ℝ)^(2 : ℕ))*
        (periodCost N f e z.im+periodCost N f e (S⁻¹ • z).im) := by
  have h := density_le_mean_add_pathCost N f e z
  rw [blockPathCost_eq_two_periods] at h
  nlinarith

/-- Positive mean-zero source points require two-period current cost at every regulator
whose square is no greater than the original density. -/
theorem two_period_cost_lower_of_mean_zero (z : ℍ) (hz : 0 < density N f z)
    (hm : sourceMean N f z=0) (he : (e:ℝ)^(2 : ℕ) ≤ density N f z) :
    1 ≤ (8/3:ℝ)*(N:ℝ)*(2*(N:ℝ)+1)*
      (periodCost N f e z.im+periodCost N f e (S⁻¹ • z).im) := by
  have hf := density_fraction_le_pathCost_of_mean_zero N f e z hm
  have hd : 0 < density N f z+(e:ℝ)^(2 : ℕ) := by positivity
  have hhalf : (1/2:ℝ) ≤ density N f z/(density N f z+(e:ℝ)^(2 : ℕ)) := by
    apply (le_div_iff₀ hd).2
    linarith
  have hh : 1 ≤ 32*blockPathCost N f e z := by linarith
  rw [blockPathCost_eq_two_periods] at hh
  nlinarith

end
end GaloisForLFunctions.RHTower.SelbergMaassUnipotentPaths
