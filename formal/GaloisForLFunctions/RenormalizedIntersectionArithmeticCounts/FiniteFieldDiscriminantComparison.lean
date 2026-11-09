import GaloisForLFunctions.HTGeometry.MonicDiscriminantProducts
import GaloisForLFunctions.HTGeometry.PowerBasisPolynomialDiscriminant
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.ArithmeticDiscriminantCover
import GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts.FiniteFieldOrientationCounts

/-!
# The discriminant cover and residue-field orientations

Cross-resultants give an explicit square relating the polynomial discriminant
to the product of residue-field trace discriminants. Scaling each actual
orientation fibre identifies the two covers and transfers the independently
counted root orientations to polynomial factorization signs.
-/

noncomputable section
open Polynomial Finset UniqueFactorizationMonoid
namespace GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
attribute [local instance] Classical.propDecidable
variable {F : Type*} [Field F] [Fintype F]

/-- The actual product of cross-resultants of the monic irreducible factors. -/
def factorCrossResultant (f : F[X]) : F :=
  HTGeometry.listCrossResultant (normalizedFactors f).toList

/-- Each monic residue-field power basis retains the polynomial's exact discriminant. -/
theorem irreducibleTraceDiscriminant_eq_discr {f : F[X]} (hf : f.Monic)
    (hi : Irreducible f) : irreducibleTraceDiscriminant f = f.discr := by
  rw [irreducibleTraceDiscriminant, dif_pos hi]
  exact HTGeometry.adjoinRoot_powerBasis_discr_eq hf hi

/-- The ramified locus is precisely the nonsquarefree locus of the monic coefficient family. -/
theorem discr_eq_zero_iff_not_squarefree {f : F[X]} (hf : f.Monic) :
    f.discr = 0 ↔ ¬ Squarefree f := by
  rw [HTGeometry.monic_discr_eq_zero_iff_not_separable hf,
    PerfectField.separable_iff_squarefree]

/-- Cross-resultants provide the exact square missing from the normalization discriminant. -/
theorem discr_eq_factorTrace_mul_cross_square {f : F[X]} (hf : f.Monic) :
    f.discr = factorTraceDiscriminant f * factorCrossResultant f ^ 2 := by
  by_cases hs : Squarefree f
  · have hp : (normalizedFactors f).toList.prod = f := by
      have h := leadingCoeff_mul_prod_normalizedFactors f
      rw [← Multiset.prod_coe, Multiset.coe_toList]
      simpa only [hf.leadingCoeff, C_1, one_mul] using h
    have hm : ∀ P ∈ (normalizedFactors f).toList, P.Monic := by
      intro P hP
      exact ((Polynomial.mem_normalizedFactors_iff hf.ne_zero).mp
        (Multiset.mem_toList.mp hP)).2.1
    have he : ((normalizedFactors f).toList.map Polynomial.discr).prod =
        ((normalizedFactors f).map irreducibleTraceDiscriminant).prod := by
      rw [← Multiset.prod_coe, ← Multiset.map_coe, Multiset.coe_toList]
      apply congrArg Multiset.prod
      apply Multiset.map_congr rfl
      intro P hP
      have hmem := (Polynomial.mem_normalizedFactors_iff hf.ne_zero).mp
        hP
      exact (irreducibleTraceDiscriminant_eq_discr hmem.2.1 hmem.1).symm
    have h := HTGeometry.discr_list_prod_of_monic (normalizedFactors f).toList hm
    rw [hp, he] at h
    simpa only [factorTraceDiscriminant, if_pos hs, factorCrossResultant] using h
  · rw [(discr_eq_zero_iff_not_squarefree hf).mpr hs,
      factorTraceDiscriminant, if_neg hs, zero_mul]

/-- The cross-resultant scaling is invertible on every squarefree fibre. -/
theorem factorCrossResultant_ne_zero {f : F[X]} (hf : f.Monic) (hs : Squarefree f) :
    factorCrossResultant f ≠ 0 := by
  intro hz
  have hd : f.discr ≠ 0 := fun h => (discr_eq_zero_iff_not_squarefree hf).mp h hs
  apply hd
  rw [discr_eq_factorTrace_mul_cross_square hf, hz, zero_pow two_ne_zero, mul_zero]

/-- Use the actual cross-resultant off ramification, and the identity on its single zero point. -/
def discriminantFibreScale (f : F[X]) : F :=
  if Squarefree f then factorCrossResultant f else 1

/-- The fibre scaling is nonzero on the entire monic coefficient space. -/
theorem discriminantFibreScale_ne_zero {f : F[X]} (hf : f.Monic) :
    discriminantFibreScale f ≠ 0 := by
  by_cases hs : Squarefree f
  · simpa only [discriminantFibreScale, if_pos hs] using factorCrossResultant_ne_zero hf hs
  · simp only [discriminantFibreScale, if_neg hs, ne_eq, one_ne_zero, not_false_eq_true]

/-- The same scaling equation includes the ramified fibres. -/
theorem discr_eq_factorTrace_mul_scale_square {f : F[X]} (hf : f.Monic) :
    f.discr = factorTraceDiscriminant f * discriminantFibreScale f ^ 2 := by
  by_cases hs : Squarefree f
  · simpa only [discriminantFibreScale, if_pos hs] using
      discr_eq_factorTrace_mul_cross_square hf
  · rw [(discr_eq_zero_iff_not_squarefree hf).mpr hs,
      factorTraceDiscriminant, if_neg hs, zero_mul]

/-- Multiplication by the explicit nonzero cross-resultant identifies the actual orientation fibres. -/
def discriminantFibreEquiv {f : F[X]} (hf : f.Monic) :
    {y : F // y ^ 2 = factorTraceDiscriminant f} ≃ {y : F // y ^ 2 = f.discr} where
  toFun y := ⟨discriminantFibreScale f * y.val, by
    rw [mul_pow, y.property, discr_eq_factorTrace_mul_scale_square hf, mul_comm]⟩
  invFun y := ⟨y.val / discriminantFibreScale f, by
    rw [div_pow]
    apply (div_eq_iff (pow_ne_zero 2 (discriminantFibreScale_ne_zero hf))).mpr
    exact y.property.trans (discr_eq_factorTrace_mul_scale_square hf)⟩
  left_inv y := by
    apply Subtype.ext
    change discriminantFibreScale f * y.val / discriminantFibreScale f = y.val
    field_simp [discriminantFibreScale_ne_zero hf]
  right_inv y := by
    apply Subtype.ext
    change discriminantFibreScale f * (y.val / discriminantFibreScale f) = y.val
    field_simp [discriminantFibreScale_ne_zero hf]

private theorem mem_factorOrientationCover_iff (n : ℕ) (fy : F[X] × F) :
    fy ∈ factorOrientationCover (F := F) n ↔
      fy.1 ∈ ArithmeticGaugeTheory.monicOfDeg F n ∧
        fy.2 ^ 2 = factorTraceDiscriminant fy.1 := by
  change fy ∈ ((ArithmeticGaugeTheory.monicOfDeg F n) ×ˢ (univ : Finset F)).filter _ ↔ _
  simp only [mem_filter, mem_product, mem_univ, and_true]

/-- The coefficient-preserving fibre maps identify the two actual finite covers. -/
def factorOrientationCoverEquiv (n : ℕ) :
    ↥(factorOrientationCover (F := F) n) ≃ ↥(arithmeticDiscriminantCover F n) where
  toFun z := by
    have hz := (mem_factorOrientationCover_iff n z.val).mp z.property
    let f : ArithmeticGaugeTheory.monicOfDeg F n := ⟨z.val.1, hz.1⟩
    let y := discriminantFibreEquiv (ArithmeticGaugeTheory.mem_monicOfDeg.mp hz.1).1
      ⟨z.val.2, hz.2⟩
    exact ⟨(f, y.val), mem_filter.mpr ⟨mem_univ _, y.property⟩⟩
  invFun z := by
    let y := (discriminantFibreEquiv
      (ArithmeticGaugeTheory.mem_monicOfDeg.mp z.val.1.property).1).symm
      ⟨z.val.2, (mem_filter.mp z.property).2⟩
    exact ⟨(z.val.1.val, y.val), (mem_factorOrientationCover_iff n _).mpr
      ⟨z.val.1.property, y.property⟩⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change discriminantFibreScale z.val.1 * z.val.2 / discriminantFibreScale z.val.1 = z.val.2
      have hm := (ArithmeticGaugeTheory.mem_monicOfDeg.mp
        ((mem_factorOrientationCover_iff n z.val).mp z.property).1).1
      field_simp [discriminantFibreScale_ne_zero hm]
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · change discriminantFibreScale z.val.1.val *
          (z.val.2 / discriminantFibreScale z.val.1.val) = z.val.2
      have hm := (ArithmeticGaugeTheory.mem_monicOfDeg.mp z.val.1.property).1
      field_simp [discriminantFibreScale_ne_zero hm]

/-- Independent arithmetic orientation counts count the residue-field cover in degree at least two. -/
theorem factorOrientationCover_card_independent (n : ℕ) [Nontrivial (Fin n)]
    (hF : ringChar F ≠ 2) : (factorOrientationCover (F := F) n).card = Fintype.card F ^ n := by
  have h := Fintype.card_congr (factorOrientationCoverEquiv (F := F) n)
  rw [Fintype.card_coe, Fintype.card_coe] at h
  rw [h, arithmeticDiscriminantCover_card F n hF]

/-- The polynomial discriminant retains exactly the residue-field orientation character. -/
theorem discriminant_character_eq_factorTrace {f : F[X]} (hf : f.Monic) :
    quadraticChar F f.discr = quadraticChar F (factorTraceDiscriminant f) := by
  rw [discr_eq_factorTrace_mul_scale_square hf, map_mul,
    quadraticChar_sq_one' (discriminantFibreScale_ne_zero hf), mul_one]

/-- Pellet's sign identity follows from the actual residue-field discriminants and cross-resultants. -/
theorem discriminant_character_eq_moebius (hF : ringChar F ≠ 2)
    {f : F[X]} (hf : f.Monic) :
    quadraticChar F f.discr = (-1 : ℤ) ^ f.natDegree * ArithmeticGaugeTheory.polyMoebius f := by
  rw [discriminant_character_eq_factorTrace hf, factorTraceDiscriminant_character hF hf]

section FrobeniusWeight
open MulAction Equiv
variable (E : Type*) [Field E] [Algebra F E] [Fintype E] (n : ℕ)
local instance : MulAction (Perm (Fin n)) (Fin n → E) :=
  permutationTupleAction E (Perm (Fin n)) (Fin n)

/-- The actual root-orbit transporter weight is the signed polynomial Möbius coefficient. -/
theorem frobeniusOrientationWeight_eq_moebius
    (hd : n.factorial ∣ Module.finrank F E) (hF : ringChar F ≠ 2)
    (f : ArithmeticGaugeTheory.monicOfDeg F n) :
    orientationOrbitWeight (tupleFrobenius F E (Perm (Fin n)) (Fin n))
        Perm.sign ((monicFrobeniusOrbitEquiv F E n hd) f).val =
      (((-1 : ℤ) ^ n * ArithmeticGaugeTheory.polyMoebius f.val : ℤ) : ℚ) := by
  obtain ⟨hm, hn⟩ := ArithmeticGaugeTheory.mem_monicOfDeg.mp f.property
  rw [← discriminant_quadraticChar_eq_orientationWeight F E n hd hF f,
    discriminant_character_eq_moebius hF hm, hn]

end FrobeniusWeight

/-- Independent orientation counts cancel the polynomial Möbius degree sums. -/
theorem moebiusDegreeSum_eq_zero_of_orientation_count (n : ℕ) [Nontrivial (Fin n)]
    (hF : ringChar F ≠ 2) : ArithmeticGaugeTheory.moebiusDegreeSum F n = 0 := by
  have hc := sum_discriminant_quadraticChar_eq_zero F n hF
  have hs : (∑ f : ArithmeticGaugeTheory.monicOfDeg F n, quadraticChar F f.val.discr) =
      (-1 : ℤ) ^ n * ArithmeticGaugeTheory.moebiusDegreeSum F n := by
    calc
      _ = ∑ f : ArithmeticGaugeTheory.monicOfDeg F n,
          (-1 : ℤ) ^ n * ArithmeticGaugeTheory.polyMoebius f.val := by
        apply sum_congr rfl
        intro f _
        obtain ⟨hm, hn⟩ := ArithmeticGaugeTheory.mem_monicOfDeg.mp f.property
        rw [discriminant_character_eq_moebius hF hm, hn]
      _ = _ := by
        rw [← mul_sum, Finset.sum_coe_sort]
        rfl
  rw [hs] at hc
  exact (mul_eq_zero.mp hc).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))

#print axioms irreducibleTraceDiscriminant_eq_discr
#print axioms discr_eq_zero_iff_not_squarefree
#print axioms discr_eq_factorTrace_mul_cross_square
#print axioms factorCrossResultant_ne_zero
#print axioms discriminantFibreScale_ne_zero
#print axioms discr_eq_factorTrace_mul_scale_square
#print axioms discriminantFibreEquiv
#print axioms factorOrientationCoverEquiv
#print axioms factorOrientationCover_card_independent
#print axioms discriminant_character_eq_factorTrace
#print axioms discriminant_character_eq_moebius
#print axioms frobeniusOrientationWeight_eq_moebius
#print axioms moebiusDegreeSum_eq_zero_of_orientation_count
end GaloisForLFunctions.RenormalizedIntersectionArithmeticCounts
