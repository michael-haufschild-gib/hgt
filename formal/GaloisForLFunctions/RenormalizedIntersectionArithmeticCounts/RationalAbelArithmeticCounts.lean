import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.ThickenedArithmeticIntersections
import GaloisForLFunctions.HeightHomotopyArithmeticCounts.FiniteRadiusTorsionEnergy
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Arithmetic radial counts and residual self-intersection

Monic integral radial cyclotomic equations define finite residue rings.
Their logarithmic cardinalities recover the rational-radius Abel energy
with its exact homogeneous term. An integral divided difference removes
coincident root pairs through an explicit exact sequence of quotient
modules. The residual count specializes to the absolute discriminant;
its prime-local multiplicities and dilation degree are exact. The
normalized counts retain the nonnegative finite-radius error and converge
along consecutive integer radii to the actual diagonal residue height.
-/
noncomputable section
open Polynomial Finset Complex
open scoped ComplexConjugate
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
open ArithmeticEffectivityTheory HeightHomotopyArithmeticCounts

/-- The monic integral equation of the torsion orbit dilated by an integer radius. -/
def radialCyclotomic (n a : ℕ) : ℤ[X] := (cyclotomic n ℤ).scaleRoots (a:ℤ)

theorem radialCyclotomic_monic (n a : ℕ) : (radialCyclotomic n a).Monic :=
  (monic_scaleRoots_iff _).mpr (cyclotomic.monic n ℤ)

/-- The actual intersection ring of two integral radial torsion divisors. -/
abbrev RadialTorsionIntersection (m n a b : ℕ) :=
  ArithmeticIntersectionRing (radialCyclotomic m a) (radialCyclotomic n b)

/-- Cardinality of the independently defined radial intersection. -/
def radialTorsionCount (m n a b : ℕ) : ℕ :=
  Nat.card (RadialTorsionIntersection m n a b)

private theorem scaleRoots_linear_product (S : Finset ℂ) (a : ℂ) :
    (∏z∈S,(X-C z)).scaleRoots a = ∏z∈S,(X-C (a*z)) := by
  induction S using Finset.induction_on with
  | empty => simp only [prod_empty,one_scaleRoots]
  | @insert z S hz ih =>
      rw [prod_insert hz,mul_scaleRoots_of_noZeroDivisors,X_sub_C_scaleRoots,ih,prod_insert hz]
      rw [mul_comm z a]

/-- The integral radial equation splits over the dilated primitive-root orbit. -/
theorem radialCyclotomic_complex {n : ℕ} (hn : 0 < n) (a : ℕ) :
    (radialCyclotomic n a).map (Int.castRingHom ℂ) =
      ∏z∈primitiveRoots n ℂ,(X-C ((a:ℂ)*z)) := by
  rw [radialCyclotomic,map_scaleRoots _ _ _ (by
    simp only [(cyclotomic.monic n ℤ).leadingCoeff,map_one,ne_eq,one_ne_zero,not_false_eq_true]),
    map_cyclotomic_int]
  simp only [Int.coe_castRingHom,Int.cast_natCast]
  rw [cyclotomic_eq_prod_X_sub_primitiveRoots (Complex.isPrimitiveRoot_exp n hn.ne'),
    scaleRoots_linear_product]

/-- The actual radial resultant is a product of differences of points on two integer-radius circles. -/
theorem radial_resultant_complex_product {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (a b : ℕ) :
    (((radialCyclotomic m a).resultant (radialCyclotomic n b) : ℤ) : ℂ) =
      ∏z∈primitiveRoots m ℂ,∏w∈primitiveRoots n ℂ,((a:ℂ)*z-(b:ℂ)*w) := by
  have he := resultant_map_map (radialCyclotomic m a) (radialCyclotomic n b)
    (radialCyclotomic m a).natDegree (radialCyclotomic n b).natDegree (Int.castRingHom ℂ)
  have hc : (((radialCyclotomic m a).resultant (radialCyclotomic n b) : ℤ) : ℂ) =
      ((radialCyclotomic m a).map (Int.castRingHom ℂ)).resultant
        ((radialCyclotomic n b).map (Int.castRingHom ℂ)) := by
    simpa only [(radialCyclotomic_monic m a).natDegree_map,
      (radialCyclotomic_monic n b).natDegree_map,Int.coe_castRingHom] using he.symm
  rw [hc,radialCyclotomic_complex hm,radialCyclotomic_complex hn,
    resultant_prod_left _ _ _ _ (by simp only [leadingCoeff_X_sub_C,prod_const_one,ne_eq,
      one_ne_zero,not_false_eq_true]) le_rfl]
  apply prod_congr rfl
  intro z _
  rw [natDegree_X_sub_C,resultant_X_sub_C_left _ _ _ le_rfl,eval_prod]
  simp only [eval_sub,eval_X,eval_C]

/-- Distinct integer radii separate every pair of torsion points. -/
theorem radial_torsion_difference_ne_zero {m n a b : ℕ} (hab : a < b) {z w : ℂ}
    (hz : z∈primitiveRoots m ℂ) (hw : w∈primitiveRoots n ℂ) :
    (a:ℂ)*z-(b:ℂ)*w ≠ 0 := by
  intro hzero
  have he := congrArg norm (sub_eq_zero.mp hzero)
  simp only [norm_mul,Complex.norm_natCast,norm_of_mem_primitiveRoots hz,
    norm_of_mem_primitiveRoots hw,mul_one] at he
  exact (Nat.ne_of_lt hab) (by exact_mod_cast he)

/-- Radial properness is proved from the equations and the separation of the two circles. -/
theorem radial_resultant_ne_zero {m n a b : ℕ} (hm : 0 < m) (hn : 0 < n) (hab : a < b) :
    (radialCyclotomic m a).resultant (radialCyclotomic n b) ≠ 0 := by
  intro hzero
  have hp : (∏z∈primitiveRoots m ℂ,∏w∈primitiveRoots n ℂ,
      ((a:ℂ)*z-(b:ℂ)*w)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro z hz
    exact Finset.prod_ne_zero_iff.mpr (fun w hw => radial_torsion_difference_ne_zero hab hz hw)
  apply hp
  rw [←radial_resultant_complex_product hm hn,hzero,Int.cast_zero]

/-- The radial torsion intersection is an actual finite residue ring. -/
theorem radialTorsionIntersection_finite {m n a b : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hab : a < b) : Finite (RadialTorsionIntersection m n a b) :=
  arithmeticIntersectionRing_finite (radialCyclotomic_monic m a)
    (radial_resultant_ne_zero hm hn hab)

#print axioms radial_resultant_complex_product
#print axioms radial_resultant_ne_zero
#print axioms radialTorsionIntersection_finite

/-- Splitting a difference of radial points separates the homogeneous radius factor. -/
theorem radial_torsion_norm {m n a b : ℕ} (hab : a < b) {z w : ℂ}
    (_hz : z ∈ primitiveRoots m ℂ) (hw : w ∈ primitiveRoots n ℂ) :
    ‖(a:ℂ)*z-(b:ℂ)*w‖ = (b:ℝ)*‖1-((a:ℝ)/b:ℂ)*(z*conj w)‖ := by
  have hb : (b:ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le a) hab))
  have he : (a:ℂ)*z-(b:ℂ)*w = (b:ℂ)*(((a:ℝ)/b:ℂ)*z-w) := by
    push_cast
    field_simp [hb]
  rw [he,norm_mul,Complex.norm_natCast,←norm_one_sub_mul_conj (norm_of_mem_primitiveRoots hw)]
  rw [mul_assoc]

/-- Logarithmic cardinality is the sum of the local archimedean root-pair contributions. -/
theorem radialTorsionCount_log_roots {m n a b : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hab : a < b) :
    Real.log (radialTorsionCount m n a b) =
      ∑z∈primitiveRoots m ℂ,∑w∈primitiveRoots n ℂ,Real.log ‖(a:ℂ)*z-(b:ℂ)*w‖ := by
  change arithmeticIntersectionHeight (radialCyclotomic m a) (radialCyclotomic n b) = _
  rw [arithmeticIntersectionHeight_archimedean (radialCyclotomic_monic m a)
    (radial_resultant_ne_zero hm hn hab)]
  have hnorm : |((radialCyclotomic m a).resultant (radialCyclotomic n b) : ℝ)| =
      ‖(((radialCyclotomic m a).resultant (radialCyclotomic n b) : ℤ):ℂ)‖ := by
    rw [←Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
  rw [hnorm,radial_resultant_complex_product hm hn,norm_prod]
  simp_rw [norm_prod]
  have hne : ∀z∈primitiveRoots m ℂ,∀w∈primitiveRoots n ℂ,‖(a:ℂ)*z-(b:ℂ)*w‖ ≠ 0 := by
    intro z hz w hw
    exact norm_ne_zero_iff.mpr (radial_torsion_difference_ne_zero hab hz hw)
  rw [Real.log_prod (fun z hz => Finset.prod_ne_zero_iff.mpr (hne z hz))]
  exact sum_congr rfl (fun z hz => Real.log_prod (hne z hz))

/-- Actual integral quotient counts recover the rational-radius Abel energy. -/
theorem radialTorsionCount_log {m n a b : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hab : a < b) :
    Real.log (radialTorsionCount m n a b) =
      (Nat.totient m:ℝ)*Nat.totient n*Real.log b-torsionEnergy ((a:ℝ)/b) m n := by
  have hb : (b:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le a) hab))
  have hpair : ∀z∈primitiveRoots m ℂ,∀w∈primitiveRoots n ℂ,
      Real.log ‖(a:ℂ)*z-(b:ℂ)*w‖ + -Real.log ‖1-((a:ℝ)/b:ℂ)*(z*conj w)‖ = Real.log b := by
    intro z hz w hw
    have hne : ‖1-((a:ℝ)/b:ℂ)*(z*conj w)‖ ≠ 0 := by
      intro he
      have hh := norm_ne_zero_iff.mpr (radial_torsion_difference_ne_zero hab hz hw)
      rw [radial_torsion_norm hab hz hw,he,mul_zero] at hh
      exact hh rfl
    rw [radial_torsion_norm hab hz hw,Real.log_mul hb hne]
    ring
  apply eq_sub_iff_add_eq.mpr
  rw [radialTorsionCount_log_roots hm hn hab,torsionEnergy,←sum_add_distrib]
  simp_rw [←sum_add_distrib]
  have he : (∑z∈primitiveRoots m ℂ,∑w∈primitiveRoots n ℂ,
      (Real.log ‖(a:ℂ)*z-(b:ℂ)*w‖ + -Real.log ‖1-((a:ℝ)/b:ℂ)*(z*conj w)‖)) =
      ∑z∈primitiveRoots m ℂ,∑w∈primitiveRoots n ℂ,Real.log b := by
    exact sum_congr rfl (fun z hz => sum_congr rfl (fun w hw => hpair z hz w hw))
  simp only [Complex.ofReal_div,Complex.ofReal_natCast] at he ⊢
  rw [he]
  simp only [sum_const,nsmul_eq_mul,(Complex.isPrimitiveRoot_exp m hm.ne').card_primitiveRoots,
    (Complex.isPrimitiveRoot_exp n hn.ne').card_primitiveRoots]
  ring

#print axioms radialTorsionCount_log_roots
#print axioms radialTorsionCount_log

/-- Integral radial divided difference, including coincident radii without division. -/
def radialDividedDifference (P : ℤ[X]) (a b : ℤ) : ℤ[X] :=
  ∑i∈P.support,monomial i (P.coeff i * ∑j∈range (P.natDegree-i),b^j*a^(P.natDegree-i-1-j))

theorem coeff_radialDividedDifference (P : ℤ[X]) (a b : ℤ) (i : ℕ) :
    (radialDividedDifference P a b).coeff i =
      P.coeff i * ∑j∈range (P.natDegree-i),b^j*a^(P.natDegree-i-1-j) := by
  simp +contextual [radialDividedDifference,coeff_monomial]

/-- The entire coincident-radius divisor is removed inside the integral polynomial ring. -/
theorem radialDividedDifference_factor (P : ℤ[X]) (a b : ℤ) :
    P.scaleRoots b-P.scaleRoots a = C (b-a)*radialDividedDifference P a b := by
  ext i
  rw [coeff_sub,coeff_scaleRoots,coeff_scaleRoots,coeff_C_mul,coeff_radialDividedDifference]
  have he := geom_sum₂_mul b a (P.natDegree-i)
  calc P.coeff i*b^(P.natDegree-i)-P.coeff i*a^(P.natDegree-i) =
      P.coeff i*(b^(P.natDegree-i)-a^(P.natDegree-i)) := by ring
    _ = P.coeff i*((∑j∈range (P.natDegree-i),b^j*a^(P.natDegree-i-1-j))*(b-a)) := by rw [he]
    _ = _ := by ring

/-- The diagonal radial divided difference is the Euler derivative of the equation. -/
theorem radialDividedDifference_one (P : ℤ[X]) :
    radialDividedDifference P 1 1 = C (P.natDegree:ℤ)*P-X*P.derivative := by
  ext i
  rw [coeff_radialDividedDifference,coeff_sub,coeff_C_mul]
  simp only [one_pow,mul_one,sum_const,card_range,nsmul_eq_mul,mul_one]
  cases i with
  | zero => rw [coeff_X_mul_zero,sub_zero]; simp only [Nat.sub_zero]; ring
  | succ i =>
      rw [coeff_X_mul,coeff_derivative]
      by_cases hi : i+1 ≤ P.natDegree
      · rw [Nat.cast_sub hi]; push_cast; ring
      · rw [coeff_eq_zero_of_natDegree_lt (lt_of_not_ge hi)]; ring

/-- Radial division does not introduce higher powers of the coordinate. -/
theorem radialDividedDifference_natDegree_le (P : ℤ[X]) (a b : ℤ) :
    (radialDividedDifference P a b).natDegree ≤ P.natDegree := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [coeff_radialDividedDifference,coeff_eq_zero_of_natDegree_lt hi,zero_mul]

/-- Removing the common radial factor removes exactly its degree from the resultant. -/
theorem radialDividedDifference_resultant {P : ℤ[X]} (hP : P.Monic) (a b : ℤ) :
    (P.scaleRoots a).resultant (P.scaleRoots b) =
      (b-a)^P.natDegree*(P.scaleRoots a).resultant (radialDividedDifference P a b) := by
  have hd := radialDividedDifference_natDegree_le P a b
  have he : P.scaleRoots b = C (b-a)*radialDividedDifference P a b + P.scaleRoots a*1 := by
    linear_combination radialDividedDifference_factor P a b
  have hm : (P.scaleRoots a).Monic := (monic_scaleRoots_iff _).mpr hP
  rw [natDegree_scaleRoots,natDegree_scaleRoots,he,
    resultant_add_mul_right _ _ _ _ _ (by simp only [natDegree_one,zero_add]; exact le_rfl)
      (by rw [natDegree_scaleRoots]),resultant_C_mul_right]
  congr 1
  conv_lhs => arg 4; rw [←Nat.add_sub_of_le hd]
  rw [resultant_add_right_deg _ _ _ _ _ le_rfl]
  simp only [←natDegree_scaleRoots P a,coeff_natDegree,hm.leadingCoeff,one_pow,one_mul]

/-- The self-interaction count after radial division is a count of an actual integral ring. -/
abbrev RadialSelfIntersection (n a b : ℕ) :=
  ArithmeticIntersectionRing (radialCyclotomic n a)
    (radialDividedDifference (cyclotomic n ℤ) a b)

def radialSelfCount (n a b : ℕ) : ℕ := Nat.card (RadialSelfIntersection n a b)

/-- Properness of the divided self-intersection follows from separation of the original circles. -/
theorem radialSelf_resultant_ne_zero {n a b : ℕ} (hn : 0 < n) (hab : a < b) :
    (radialCyclotomic n a).resultant (radialDividedDifference (cyclotomic n ℤ) a b) ≠ 0 := by
  have hh := radial_resultant_ne_zero hn hn hab
  rw [radialCyclotomic,radialCyclotomic,radialDividedDifference_resultant (cyclotomic.monic n ℤ)] at hh
  exact right_ne_zero_of_mul hh

/-- Arithmetic removal of coincident root pairs leaves a finite integral residue ring. -/
theorem radialSelfIntersection_finite {n a b : ℕ} (hn : 0 < n) (hab : a < b) :
    Finite (RadialSelfIntersection n a b) :=
  arithmeticIntersectionRing_finite (radialCyclotomic_monic n a) (radialSelf_resultant_ne_zero hn hab)

/-- The coincident-root factor is separated from a genuine residual integer count. -/
theorem radialTorsionCount_self_factor {n a b : ℕ} (hn : 0 < n) (hab : a < b) :
    radialTorsionCount n n a b = (b-a)^(Nat.totient n)*radialSelfCount n a b := by
  change arithmeticIntersectionCount _ _ = _*arithmeticIntersectionCount _ _
  rw [arithmeticIntersectionCount_eq_resultant (radialCyclotomic_monic n a)
    (radial_resultant_ne_zero hn hn hab),
    arithmeticIntersectionCount_eq_resultant (radialCyclotomic_monic n a)
      (radialSelf_resultant_ne_zero hn hab)]
  rw [radialCyclotomic,radialCyclotomic,radialDividedDifference_resultant (cyclotomic.monic n ℤ),
    Int.natAbs_mul,Int.natAbs_pow,natDegree_cyclotomic,
    ←Nat.cast_sub (le_of_lt hab),Int.natAbs_natCast]

#print axioms radialDividedDifference_factor
#print axioms radialDividedDifference_one
#print axioms radialDividedDifference_resultant
#print axioms radialSelfIntersection_finite
#print axioms radialTorsionCount_self_factor

/-- Common integral dilation acts on the defining radial equations. -/
theorem radialCyclotomic_mul (n a k : ℕ) :
    radialCyclotomic n (a*k) = (radialCyclotomic n a).scaleRoots (k:ℤ) := by
  simp only [radialCyclotomic,Nat.cast_mul,scaleRoots_mul]

/-- Common dilation has the exact homogeneous cardinality degree. -/
theorem radialTorsionCount_dilation {m n a b k : ℕ} (hm : 0 < m) (hn : 0 < n)
    (hab : a < b) (hk : 0 < k) :
    radialTorsionCount m n (a*k) (b*k) =
      k^(Nat.totient m*Nat.totient n)*radialTorsionCount m n a b := by
  change arithmeticIntersectionCount _ _ = _*arithmeticIntersectionCount _ _
  rw [arithmeticIntersectionCount_eq_resultant (radialCyclotomic_monic m (a*k))
    (radial_resultant_ne_zero hm hn (Nat.mul_lt_mul_of_pos_right hab hk)),
    arithmeticIntersectionCount_eq_resultant (radialCyclotomic_monic m a)
    (radial_resultant_ne_zero hm hn hab),radialCyclotomic_mul,radialCyclotomic_mul,
    resultant_scaleRoots,Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_natCast]
  simp only [radialCyclotomic,natDegree_scaleRoots,natDegree_cyclotomic]

/-- Removing the coincident-radius factor removes its exact logarithmic self-energy. -/
theorem radialSelfCount_log {n a b : ℕ} (hn : 0 < n) (hab : a < b) :
    Real.log (radialTorsionCount n n a b) =
      (Nat.totient n:ℝ)*Real.log (b-a:ℕ)+Real.log (radialSelfCount n a b) := by
  have hd : ((b-a:ℕ):ℝ) ≠ 0 := by exact_mod_cast (Nat.sub_pos_of_lt hab).ne'
  have hc : (radialSelfCount n a b:ℝ) ≠ 0 := by
    have hh := (arithmeticIntersectionHeight_prime_sum (radialCyclotomic_monic n a)
      (radialSelf_resultant_ne_zero hn hab)).1
    exact_mod_cast (ne_of_gt hh)
  rw [radialTorsionCount_self_factor hn hab,Nat.cast_mul,Nat.cast_pow,
    Real.log_mul (pow_ne_zero _ hd) hc,Real.log_pow]

/-- The residual integer count retains the signed finite-radius error after homogeneous normalization. -/
theorem radialSelfCount_finite_radius {n a b : ℕ} (hn : 0 < n) (ha : 0 < a) (hab : a < b) :
    Real.log (radialSelfCount n a b) -
      ((Nat.totient n:ℝ)^2-Nat.totient n)*Real.log b -
      (torsionPairCount n n:ℝ)*Real.log ((a:ℝ)/b)/2 =
      orbitIntersection n n+torsionRadialError ((a:ℝ)/b) n n := by
  have hb : (0:ℝ) < b := by exact_mod_cast lt_trans ha hab
  have ha' : (0:ℝ) < a := by exact_mod_cast ha
  have hab' : (a:ℝ) < b := by exact_mod_cast hab
  have hgap : (0:ℝ) < ((b-a:ℕ):ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hab
  have hr := div_pos ha' hb
  have hlog : Real.log |1-(a:ℝ)/b| = Real.log (b-a:ℕ)-Real.log b := by
    rw [abs_of_pos (sub_pos.mpr ((div_lt_one hb).mpr hab'))]
    have he : 1-(a:ℝ)/b = ((b-a:ℕ):ℝ)/(b:ℝ) := by
      rw [Nat.cast_sub (le_of_lt hab)]
      field_simp [hb.ne']
    rw [he,Real.log_div hgap.ne' hb.ne']
  have ht := torsionEnergy_finite_radius ((a:ℝ)/b) hr n
  rw [hlog] at ht
  have hc := radialTorsionCount_log hn hn hab
  have hs := radialSelfCount_log hn hab
  linear_combination hc - hs - ht

/-- Arithmetic residual height approaches the discriminant height with a nonnegative quadratic error. -/
theorem radialSelfCount_error_bounds {n a b : ℕ} (hn : 0 < n) (ha : 0 < a) (hab : a < b) :
    let E := Real.log (radialSelfCount n a b) -
      ((Nat.totient n:ℝ)^2-Nat.totient n)*Real.log b -
      (torsionPairCount n n:ℝ)*Real.log ((a:ℝ)/b)/2 - orbitIntersection n n
    0 ≤ E ∧ E ≤ (1-(a:ℝ)/b)^2/(2*((a:ℝ)/b))*torsionInverseChordCost n n := by
  dsimp only
  rw [radialSelfCount_finite_radius hn ha hab,add_sub_cancel_left]
  exact torsionRadialError_bounds _ (div_pos (by exact_mod_cast ha)
    (by exact_mod_cast lt_trans ha hab)) n n

#print axioms radialTorsionCount_dilation
#print axioms radialSelfCount_log
#print axioms radialSelfCount_finite_radius
#print axioms radialSelfCount_error_bounds

private theorem monic_resultant_right_degree {P : ℤ[X]} (hP : P.Monic) (Q : ℤ[X])
    (d : ℕ) (hd : Q.natDegree ≤ d) :
    P.resultant Q P.natDegree d = P.resultant Q := by
  conv_lhs => arg 4; rw [←Nat.add_sub_of_le hd]
  rw [resultant_add_right_deg _ _ _ _ _ le_rfl]
  simp only [coeff_natDegree,hP.leadingCoeff,one_pow,one_mul]

/-- At coincidence, radial intersection becomes the different, with the constant coefficient factor. -/
theorem radialDividedDifference_diagonal_resultant {P : ℤ[X]} (hP : P.Monic) :
    P.resultant (radialDividedDifference P 1 1) = P.coeff 0*P.resultant P.derivative := by
  by_cases hd : P.natDegree = 0
  · have hp : P = 1 := hP.natDegree_eq_zero.mp hd
    subst P
    simp only [resultant_one_left,natDegree_one,zero_mul,pow_zero,mul_one,coeff_one_zero]
  have hdpos : 0 < P.natDegree := Nat.pos_of_ne_zero hd
  have hs : (X:ℤ[X]).natDegree+P.derivative.natDegree = P.natDegree := by
    rw [natDegree_X,natDegree_derivative]
    omega
  have he : radialDividedDifference P 1 1 = C (-1)*(X*P.derivative)+P*C (P.natDegree:ℤ) := by
    rw [radialDividedDifference_one,C_neg,C_1]
    ring
  have hc : P.resultant (radialDividedDifference P 1 1) =
      (-1)^P.natDegree*(P.resultant X*P.resultant P.derivative) := by
    rw [←monic_resultant_right_degree hP _ _ (radialDividedDifference_natDegree_le P 1 1),he,
      resultant_add_mul_right _ _ _ _ _ (by simp only [natDegree_C,zero_add]; exact le_rfl) le_rfl,
      resultant_C_mul_right]
    congr 1
    have hh := resultant_mul_right P X P.derivative P.natDegree le_rfl
    rw [hs] at hh
    exact hh
  have hx : P.resultant X = (-1)^P.natDegree*P.coeff 0 := by
    have hh := resultant_X_pow_right P P.natDegree 1 le_rfl
    rw [show (X:ℤ[X])^1 = X from pow_one _] at hh
    simpa only [pow_one,natDegree_X,mul_one] using hh
  rw [hc,hx]
  have hsign : (-1:ℤ)^P.natDegree*(-1)^P.natDegree = 1 := by rw [←mul_pow]; simp
  calc (-1:ℤ)^P.natDegree*((-1)^P.natDegree*P.coeff 0*P.resultant P.derivative) =
      ((-1)^P.natDegree*(-1)^P.natDegree)*(P.coeff 0*P.resultant P.derivative) := by ring
    _ = _ := by rw [hsign,one_mul]

/-- For monic integral equations, the derivative resultant has absolute value equal to the discriminant. -/
theorem monic_resultant_derivative_natAbs {P : ℤ[X]} (hP : P.Monic) :
    (P.resultant P.derivative).natAbs = P.discr.natAbs := by
  by_cases hd : P.natDegree = 0
  · have hp : P = 1 := hP.natDegree_eq_zero.mp hd
    subst P
    have hdis : (1:ℤ[X]).discr = 1 := by simpa only [C_1] using discr_C (1:ℤ)
    rw [hdis]
    simp
  have he := resultant_deriv (natDegree_pos_iff_degree_pos.mp (Nat.pos_of_ne_zero hd))
    (f := P)
  rw [←natDegree_derivative] at he
  have hh := congrArg Int.natAbs he
  simpa only [Int.natAbs_mul,Int.natAbs_pow,Int.natAbs_neg,Int.natAbs_one,
    hP.leadingCoeff,one_pow,one_mul] using hh

/-- The diagonal radial resultant is the discriminant times the constant coefficient, in absolute value. -/
theorem radialDividedDifference_diagonal_natAbs {P : ℤ[X]} (hP : P.Monic) :
    (P.resultant (radialDividedDifference P 1 1)).natAbs =
      (P.coeff 0).natAbs*P.discr.natAbs := by
  rw [radialDividedDifference_diagonal_resultant hP,Int.natAbs_mul,
    monic_resultant_derivative_natAbs hP]

#print axioms radialDividedDifference_diagonal_resultant
#print axioms monic_resultant_derivative_natAbs
#print axioms radialDividedDifference_diagonal_natAbs

/-- Cyclotomic constant coefficients are units, including the conductor-one sign. -/
theorem cyclotomic_constant_natAbs (n : ℕ) : ((cyclotomic n ℤ).coeff 0).natAbs = 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rcases eq_or_lt_of_le (Nat.succ_le_of_lt hn) with he | hn
  · subst n
    simp
  · rw [cyclotomic_coeff_zero ℤ hn]
    rfl

/-- Separability supplies the nonzero derivative resultant over the integers. -/
theorem cyclotomic_derivative_resultant_ne_zero {n : ℕ} (hn : 0 < n) :
    (cyclotomic n ℤ).resultant (cyclotomic n ℤ).derivative ≠ 0 := by
  letI : NeZero (n:ℚ) := ⟨by exact_mod_cast hn.ne'⟩
  have he := resultant_map_map (cyclotomic n ℤ) (cyclotomic n ℤ).derivative
    (cyclotomic n ℤ).natDegree (cyclotomic n ℤ).derivative.natDegree (Int.castRingHom ℚ)
  rw [←derivative_map,map_cyclotomic_int] at he
  have hne := resultant_ne_zero (cyclotomic n ℚ) (cyclotomic n ℚ).derivative
    (separable_cyclotomic n ℚ)
  intro hzero
  simp only [natDegree_derivative,natDegree_cyclotomic] at he hne hzero
  rw [hzero,map_zero] at he
  exact hne he

/-- The renormalized diagonal equation has a nonzero resultant. -/
theorem radialSelf_diagonal_resultant_ne_zero {n : ℕ} (hn : 0 < n) :
    (radialCyclotomic n 1).resultant (radialDividedDifference (cyclotomic n ℤ) 1 1) ≠ 0 := by
  have hc : (cyclotomic n ℤ).coeff 0 ≠ 0 := by
    intro he
    have hh := cyclotomic_constant_natAbs n
    rw [he,Int.natAbs_zero] at hh
    exact Nat.zero_ne_one hh
  have hscale : radialCyclotomic n 1 = cyclotomic n ℤ := by
    rw [radialCyclotomic,Nat.cast_one,scaleRoots_one]
  rw [hscale,radialDividedDifference_diagonal_resultant (cyclotomic.monic n ℤ)]
  exact mul_ne_zero hc (cyclotomic_derivative_resultant_ne_zero hn)

/-- The independently constructed diagonal residue ring is finite. -/
theorem radialSelfIntersection_diagonal_finite {n : ℕ} (hn : 0 < n) :
    Finite (RadialSelfIntersection n 1 1) :=
  arithmeticIntersectionRing_finite (radialCyclotomic_monic n 1)
    (radialSelf_diagonal_resultant_ne_zero hn)

/-- Arithmetic self-intersection at the unit radius counts the absolute cyclotomic discriminant. -/
theorem radialSelfCount_diagonal {n : ℕ} (hn : 0 < n) :
    radialSelfCount n 1 1 = (cyclotomic n ℤ).discr.natAbs := by
  change arithmeticIntersectionCount _ _ = _
  simp only [Nat.cast_one]
  rw [arithmeticIntersectionCount_eq_resultant (radialCyclotomic_monic n 1)
    (radialSelf_diagonal_resultant_ne_zero hn),radialCyclotomic,Nat.cast_one,scaleRoots_one,
    radialDividedDifference_diagonal_natAbs (cyclotomic.monic n ℤ),
    cyclotomic_constant_natAbs,one_mul]

#print axioms cyclotomic_derivative_resultant_ne_zero
#print axioms radialSelfIntersection_diagonal_finite
#print axioms radialSelfCount_diagonal

/-- Multiplication by the scalar divisor sends the residual intersection into the full intersection. -/
def intersectionScalarInclusion (P D : ℤ[X]) (c : ℤ) :
    ArithmeticIntersectionRing P D →ₗ[ℤ[X]] ArithmeticIntersectionRing P (C c*D) :=
  Submodule.mapQ (Ideal.span ({P,D}:Set ℤ[X])) (Ideal.span ({P,C c*D}:Set ℤ[X]))
    ((C c) • LinearMap.id) (by
      intro r hr
      change C c*r ∈ Ideal.span ({P,C c*D}:Set ℤ[X])
      obtain ⟨u,v,he⟩ := Ideal.mem_span_pair.mp hr
      apply Ideal.mem_span_pair.mpr
      refine ⟨C c*u,v,?_⟩
      rw [←he]
      ring)

@[simp] theorem intersectionScalarInclusion_mk (P D : ℤ[X]) (c : ℤ) (r : ℤ[X]) :
    intersectionScalarInclusion P D c (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ (C c*r) := rfl

/-- Reduction modulo the scalar divisor is defined on the full intersection. -/
def intersectionScalarProjection (P D : ℤ[X]) (c : ℤ) :
    ArithmeticIntersectionRing P (C c*D) →ₗ[ℤ[X]] ArithmeticIntersectionRing P (C c) :=
  Submodule.mapQ (Ideal.span ({P,C c*D}:Set ℤ[X])) (Ideal.span ({P,C c}:Set ℤ[X]))
    LinearMap.id (by
      intro r hr
      change r ∈ Ideal.span ({P,C c}:Set ℤ[X])
      obtain ⟨u,v,he⟩ := Ideal.mem_span_pair.mp hr
      apply Ideal.mem_span_pair.mpr
      refine ⟨u,v*D,?_⟩
      rw [←he]
      ring)

@[simp] theorem intersectionScalarProjection_mk (P D : ℤ[X]) (c : ℤ) (r : ℤ[X]) :
    intersectionScalarProjection P D c (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk _ r := rfl

/-- A nonzero integer acts injectively modulo a monic polynomial equation. -/
theorem monic_scalar_saturation {P : ℤ[X]} (hP : P.Monic) {c : ℤ} (hc : c ≠ 0)
    (r : ℤ[X]) (h : P ∣ C c*r) : P ∣ r := by
  have hz := (modByMonic_eq_zero_iff_dvd hP).mpr h
  rw [←smul_eq_C_mul,smul_modByMonic] at hz
  exact (modByMonic_eq_zero_iff_dvd hP).mp ((smul_eq_zero.mp hz).resolve_left hc)

/-- Monic flatness makes the residual inclusion injective. -/
theorem intersectionScalarInclusion_injective {P : ℤ[X]} (hP : P.Monic) (D : ℤ[X])
    {c : ℤ} (hc : c ≠ 0) : Function.Injective (intersectionScalarInclusion P D c) := by
  have hzero : ∀x,intersectionScalarInclusion P D c x = 0 → x = 0 := by
    intro x hx
    obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [intersectionScalarInclusion_mk,Ideal.Quotient.eq_zero_iff_mem] at hx
    obtain ⟨u,v,he⟩ := Ideal.mem_span_pair.mp hx
    have hd : P ∣ C c*(r-v*D) := by
      refine ⟨u,?_⟩
      linear_combination -he
    obtain ⟨w,hw⟩ := monic_scalar_saturation hP hc _ hd
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_pair.mpr
    refine ⟨w,v,?_⟩
    linear_combination -hw
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero
  rw [map_sub,hxy,sub_self]

/-- Every scalar residue class comes from the full intersection. -/
theorem intersectionScalarProjection_surjective (P D : ℤ[X]) (c : ℤ) :
    Function.Surjective (intersectionScalarProjection P D c) := by
  intro x
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact ⟨Ideal.Quotient.mk _ r,rfl⟩

/-- The actual quotient maps form the residual intersection exact sequence. -/
theorem intersectionScalarSequence_exact (P D : ℤ[X]) (c : ℤ) :
    LinearMap.range (intersectionScalarInclusion P D c) =
      LinearMap.ker (intersectionScalarProjection P D c) := by
  ext x
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective x
  constructor
  · rintro ⟨y,hy⟩
    obtain ⟨v,rfl⟩ := Ideal.Quotient.mk_surjective y
    rw [←hy]
    change Ideal.Quotient.mk (Ideal.span ({P,C c}:Set ℤ[X])) (C c*v) = 0
    apply Ideal.Quotient.eq_zero_iff_mem.mpr
    apply Ideal.mem_span_pair.mpr
    exact ⟨0,v,by ring⟩
  · intro hx
    change Ideal.Quotient.mk (Ideal.span ({P,C c}:Set ℤ[X])) r = 0 at hx
    obtain ⟨u,v,he⟩ := Ideal.mem_span_pair.mp (Ideal.Quotient.eq_zero_iff_mem.mp hx)
    refine ⟨Ideal.Quotient.mk _ v,?_⟩
    rw [intersectionScalarInclusion_mk]
    apply Ideal.Quotient.eq.mpr
    apply Ideal.mem_span_pair.mpr
    refine ⟨-u,0,?_⟩
    linear_combination -he

#print axioms intersectionScalarInclusion_injective
#print axioms intersectionScalarProjection_surjective
#print axioms intersectionScalarSequence_exact

/-- The original radial pair and the scalar-times-residual pair define the same integral ideal. -/
theorem radialSelf_full_ideal (n a b : ℕ) :
    Ideal.span ({radialCyclotomic n a,radialCyclotomic n b}:Set ℤ[X]) =
      Ideal.span ({radialCyclotomic n a,
        C ((b:ℤ)-a)*radialDividedDifference (cyclotomic n ℤ) a b}:Set ℤ[X]) := by
  have he := radialDividedDifference_factor (cyclotomic n ℤ) (a:ℤ) (b:ℤ)
  change radialCyclotomic n b-radialCyclotomic n a = _ at he
  apply le_antisymm
  · apply Ideal.span_le.mpr
    intro r hr
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact Ideal.subset_span (by simp)
    · apply Ideal.mem_span_pair.mpr
      refine ⟨1,1,?_⟩
      linear_combination -he
  · apply Ideal.span_le.mpr
    intro r hr
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hr
    rcases hr with rfl | rfl
    · exact Ideal.subset_span (by simp)
    · apply Ideal.mem_span_pair.mpr
      refine ⟨-1,1,?_⟩
      linear_combination he

/-- Scalar multiplication and reduction give an exact sequence on the original radial intersection rings. -/
theorem radialSelfIntersection_exact_sequence {n a b : ℕ} (hab : a < b) :
    ∃ (i : RadialSelfIntersection n a b →ₗ[ℤ[X]] RadialTorsionIntersection n n a b)
      (π : RadialTorsionIntersection n n a b →ₗ[ℤ[X]]
        ArithmeticIntersectionRing (radialCyclotomic n a) (C ((b:ℤ)-a))),
      Function.Injective i ∧ Function.Surjective π ∧ LinearMap.range i = LinearMap.ker π := by
  have hc : (b:ℤ)-a ≠ 0 := by
    have hh : (a:ℤ) < b := by exact_mod_cast hab
    exact (sub_pos.mpr hh).ne'
  change ∃ (i : ArithmeticIntersectionRing _ _ →ₗ[ℤ[X]]
      (ℤ[X] ⧸ Ideal.span ({radialCyclotomic n a,radialCyclotomic n b}:Set ℤ[X])))
    (π : (ℤ[X] ⧸ Ideal.span ({radialCyclotomic n a,radialCyclotomic n b}:Set ℤ[X])) →ₗ[ℤ[X]] _),
      Function.Injective i ∧ Function.Surjective π ∧ LinearMap.range i = LinearMap.ker π
  rw [radialSelf_full_ideal]
  exact ⟨intersectionScalarInclusion _ _ _,intersectionScalarProjection _ _ _,
    intersectionScalarInclusion_injective (radialCyclotomic_monic n a) _ hc,
    intersectionScalarProjection_surjective _ _ _,intersectionScalarSequence_exact _ _ _⟩

#print axioms radialSelf_full_ideal
#print axioms radialSelfIntersection_exact_sequence

/-- Differentiating the linear root factor leaves the product over the remaining torsion points. -/
theorem cyclotomic_derivative_at_root {n : ℕ} (hn : 0 < n) {z : ℂ}
    (hz : z ∈ primitiveRoots n ℂ) :
    eval z (cyclotomic n ℂ).derivative = ∏w∈(primitiveRoots n ℂ).erase z,(z-w) := by
  have he := cyclotomic_eq_prod_X_sub_primitiveRoots (Complex.isPrimitiveRoot_exp n hn.ne')
  rw [←Finset.insert_erase hz,prod_insert (notMem_erase z (primitiveRoots n ℂ))] at he
  rw [he,derivative_mul,derivative_sub,derivative_X,derivative_C,sub_zero,
    eval_add,eval_mul,eval_one,one_mul,eval_mul,eval_sub,eval_X,eval_C,sub_self,
    zero_mul,add_zero,eval_prod]
  simp only [eval_sub,eval_X,eval_C]

/-- The derivative resultant is the product of the noncoincident differences. -/
theorem cyclotomic_derivative_resultant_complex_product {n : ℕ} (hn : 0 < n) :
    (((cyclotomic n ℤ).resultant (cyclotomic n ℤ).derivative : ℤ):ℂ) =
      ∏z∈primitiveRoots n ℂ,∏w∈(primitiveRoots n ℂ).erase z,(z-w) := by
  letI : NeZero (n:ℂ) := ⟨by exact_mod_cast hn.ne'⟩
  have he := resultant_map_map (cyclotomic n ℤ) (cyclotomic n ℤ).derivative
    (cyclotomic n ℤ).natDegree (cyclotomic n ℤ).derivative.natDegree (Int.castRingHom ℂ)
  rw [←derivative_map,map_cyclotomic_int] at he
  have hc : (((cyclotomic n ℤ).resultant (cyclotomic n ℤ).derivative : ℤ):ℂ) =
      (cyclotomic n ℂ).resultant (cyclotomic n ℂ).derivative := by
    simpa only [natDegree_derivative,natDegree_cyclotomic,Int.coe_castRingHom] using he.symm
  rw [hc,resultant_eq_prod_eval _ _ _ le_rfl (IsAlgClosed.splits _),
    (cyclotomic.monic n ℂ).leadingCoeff,one_pow,one_mul,
    cyclotomic.roots_eq_primitiveRoots_val]
  change (∏z∈primitiveRoots n ℂ,eval z (cyclotomic n ℂ).derivative) = _
  exact prod_congr rfl (fun z hz => cyclotomic_derivative_at_root hn hz)

/-- The cyclotomic discriminant height is the full torsion self-intersection, for every conductor. -/
theorem cyclotomic_log_discriminant {n : ℕ} (hn : 0 < n) :
    Real.log ((cyclotomic n ℤ).discr.natAbs) = orbitIntersection n n := by
  rw [←monic_resultant_derivative_natAbs (cyclotomic.monic n ℤ),Nat.cast_natAbs,Int.cast_abs]
  have he : |((cyclotomic n ℤ).resultant (cyclotomic n ℤ).derivative : ℝ)| =
      ‖(((cyclotomic n ℤ).resultant (cyclotomic n ℤ).derivative : ℤ):ℂ)‖ := by
    rw [←Complex.ofReal_intCast,Complex.norm_real,Real.norm_eq_abs]
  rw [he,cyclotomic_derivative_resultant_complex_product hn,norm_prod]
  simp_rw [norm_prod]
  have hne : ∀z∈primitiveRoots n ℂ,∀w∈(primitiveRoots n ℂ).erase z,‖z-w‖≠0 := by
    intro z _ w hw
    exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr (ne_of_mem_erase hw).symm)
  rw [Real.log_prod (fun z hz => Finset.prod_ne_zero_iff.mpr (hne z hz)),orbitIntersection]
  apply sum_congr rfl
  intro z hz
  rw [Real.log_prod (hne z hz),←add_sum_erase _ _ hz,sub_self,norm_zero,Real.log_zero,zero_add]

/-- The actual diagonal residue count recovers the torsion self-intersection. -/
theorem radialSelfCount_diagonal_log {n : ℕ} (hn : 0 < n) :
    Real.log (radialSelfCount n 1 1) = orbitIntersection n n := by
  rw [radialSelfCount_diagonal hn,cyclotomic_log_discriminant hn]

#print axioms cyclotomic_derivative_resultant_complex_product
#print axioms cyclotomic_log_discriminant
#print axioms radialSelfCount_diagonal_log

/-- The residual height removes exactly the homogeneous term from the renormalized Abel energy. -/
theorem radialSelfCount_normalized_log {n a b : ℕ} (hn : 0 < n) (hab : a < b) :
    Real.log (radialSelfCount n a b) - ((Nat.totient n:ℝ)^2-Nat.totient n)*Real.log b =
      -(torsionEnergy ((a:ℝ)/b) n n+(Nat.totient n:ℝ)*Real.log |1-(a:ℝ)/b|) := by
  have hb : (0:ℝ) < b := by exact_mod_cast lt_of_le_of_lt (Nat.zero_le a) hab
  have hab' : (a:ℝ) < b := by exact_mod_cast hab
  have hgap : (0:ℝ) < ((b-a:ℕ):ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hab
  have hlog : Real.log |1-(a:ℝ)/b| = Real.log (b-a:ℕ)-Real.log b := by
    rw [abs_of_pos (sub_pos.mpr ((div_lt_one hb).mpr hab'))]
    have he : 1-(a:ℝ)/b = ((b-a:ℕ):ℝ)/(b:ℝ) := by
      rw [Nat.cast_sub (le_of_lt hab)]
      field_simp [hb.ne']
    rw [he,Real.log_div hgap.ne' hb.ne']
  rw [hlog]
  have hc := radialTorsionCount_log hn hn hab
  have hs := radialSelfCount_log hn hab
  linear_combination hc-hs

open Filter Topology in
/-- Counts on consecutive integer radii converge, after their homogeneous normalization, to the actual diagonal height. -/
theorem radialSelfCount_diagonal_limit {n : ℕ} (hn : 0 < n) :
    Tendsto (fun k : ℕ => Real.log (radialSelfCount n k (k+1)) -
      ((Nat.totient n:ℝ)^2-Nat.totient n)*Real.log (k+1:ℕ))
      atTop (𝓝 (Real.log (radialSelfCount n 1 1))) := by
  have hr : Tendsto (fun k : ℕ => (k:ℝ)/((k+1:ℕ):ℝ)) atTop (𝓝 1) := by
    simpa only [Nat.cast_add,Nat.cast_one] using tendsto_natCast_div_add_atTop (𝕜 := ℝ) (1:ℝ)
  have ht := ((tendsto_torsionEnergy_self_add_log n).comp hr).neg
  rw [radialSelfCount_diagonal_log hn]
  simpa only [neg_neg] using ht.congr' (Filter.Eventually.of_forall
    (fun k => (radialSelfCount_normalized_log hn (Nat.lt_succ_self k)).symm))

/-- The residual count has the discriminant's homogeneous dilation degree. -/
theorem radialSelfCount_dilation {n a b k : ℕ} (hn : 0 < n) (hab : a < b) (hk : 0 < k) :
    radialSelfCount n (a*k) (b*k) = k^(Nat.totient n*(Nat.totient n-1))*radialSelfCount n a b := by
  have hd : 0 < Nat.totient n := Nat.totient_pos.mpr hn
  have he : Nat.totient n*Nat.totient n =
      Nat.totient n+Nat.totient n*(Nat.totient n-1) := by
    rw [Nat.mul_sub_left_distrib,Nat.mul_one]
    exact (Nat.add_sub_of_le (Nat.le_mul_of_pos_right _ hd)).symm
  have hc := radialTorsionCount_dilation hn hn hab hk
  rw [radialTorsionCount_self_factor hn (Nat.mul_lt_mul_of_pos_right hab hk),
    radialTorsionCount_self_factor hn hab,←Nat.sub_mul,mul_pow,he,pow_add] at hc
  have hnonzero : (b-a)^(Nat.totient n)*k^(Nat.totient n) ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ (Nat.sub_pos_of_lt hab).ne') (pow_ne_zero _ hk.ne')
  apply mul_left_cancel₀ hnonzero
  calc (b-a)^(Nat.totient n)*k^(Nat.totient n)*radialSelfCount n (a*k) (b*k) =
      (k^(Nat.totient n)*k^(Nat.totient n*(Nat.totient n-1)))*
        ((b-a)^(Nat.totient n)*radialSelfCount n a b) := hc
    _ = _ := by ring

#print axioms radialSelfCount_normalized_log
#print axioms radialSelfCount_diagonal_limit
#print axioms radialSelfCount_dilation

/-- Each prime-local coincident contribution is removed inside the integers. -/
theorem radialSelfCount_local_factor {n a b : ℕ} (hn : 0 < n) (hab : a < b) (p : ℕ) :
    (radialTorsionCount n n a b).factorization p =
      Nat.totient n*(b-a).factorization p+(radialSelfCount n a b).factorization p := by
  have hc : radialSelfCount n a b ≠ 0 := ne_of_gt
    (arithmeticIntersectionHeight_prime_sum (radialCyclotomic_monic n a)
      (radialSelf_resultant_ne_zero hn hab)).1
  rw [radialTorsionCount_self_factor hn hab,
    Nat.factorization_mul (pow_ne_zero _ (Nat.sub_pos_of_lt hab).ne') hc,
    Finsupp.add_apply,Nat.factorization_pow,Finsupp.smul_apply,smul_eq_mul]

#print axioms radialSelfCount_local_factor

end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
