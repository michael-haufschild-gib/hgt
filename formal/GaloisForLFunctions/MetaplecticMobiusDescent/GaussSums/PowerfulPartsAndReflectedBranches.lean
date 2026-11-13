/-
Powerful parts and reflected branches adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.RowCompletion.CoprimalityMasksAndSexticRows

/-!
# Powerful parts and reflected branches

Simple, powerful and mask parts of a row ideal and the completed local exponents. Reflected
branches and fiber data `ReflectedFiberData` with their energy bounds.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators Classical Topology InnerProductSpace ComplexConjugate MatrixGroups ENNReal
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open Eisenstein CubicJacobi CubicKubota CubicRamified
open scoped NNReal Pointwise
open RationalSource
open scoped Manifold ContDiff
open scoped Matrix
open UniqueFactorizationMonoid
open Asymptotics
open scoped ContDiff FourierTransform SchwartzMap
open scoped ContDiff FourierTransform SchwartzMap
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter Asymptotics MeasureTheory
open scoped BigOperators Topology
open Filter
open scoped BigOperators Classical SchwartzMap
open scoped BigOperators Classical SchwartzMap
open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion UniqueFactorizationMonoid
open scoped BigOperators Classical

/-- Every prime factor of a powerful ideal occurs at least twice. -/
def PowerfulIdeal (I : Ideal O) : Prop :=
  I≠0 ∧ ∀P∈normalizedFactors I, 2≤(normalizedFactors I).count P

lemma ideals_coprime_of_relprime (A B : Ideal O) (h : IsRelPrime A B) : IsCoprime A B := by
  apply Ideal.isCoprime_iff_gcd.mpr
  simpa only [Ideal.one_eq_top] using Ideal.isUnit_iff.mp
    (h (GCDMonoid.gcd_dvd_left A B) (GCDMonoid.gcd_dvd_right A B))

/-- Product of the prime powers with exponent at least two. -/
def rowPowerfulPart (I : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (fun P => 2≤(normalizedFactors I).count P)).prod

/-- Product of the primes occurring exactly once. -/
def rowSimplePart (I : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (fun P => ¬2≤(normalizedFactors I).count P)).prod

theorem rowPowerfulPart_ne_zero (I : Ideal O) : rowPowerfulPart I≠0 :=
  Multiset.prod_ne_zero (fun h => zero_notMem_normalizedFactors I (Multiset.mem_filter.mp h).1)

theorem rowSimplePart_ne_zero (I : Ideal O) : rowSimplePart I≠0 :=
  Multiset.prod_ne_zero (fun h => zero_notMem_normalizedFactors I (Multiset.mem_filter.mp h).1)

theorem normalizedFactors_rowPowerfulPart (I : Ideal O) :
    normalizedFactors (rowPowerfulPart I)=
      (normalizedFactors I).filter (fun P => 2≤(normalizedFactors I).count P) :=
  normalizedFactors_prod_of_prime (fun P hP => prime_of_normalized_factor P (Multiset.mem_filter.mp hP).1)

theorem normalizedFactors_rowSimplePart (I : Ideal O) :
    normalizedFactors (rowSimplePart I)=
      (normalizedFactors I).filter (fun P => ¬2≤(normalizedFactors I).count P) :=
  normalizedFactors_prod_of_prime (fun P hP => prime_of_normalized_factor P (Multiset.mem_filter.mp hP).1)

theorem rowPowerfulPart_powerful (I : Ideal O) : PowerfulIdeal (rowPowerfulPart I) := by
  refine ⟨rowPowerfulPart_ne_zero I,?_⟩
  intro P hP
  rw [normalizedFactors_rowPowerfulPart] at hP ⊢
  have hp := (Multiset.mem_filter.mp hP).2
  rw [Multiset.count_filter,if_pos hp]
  exact hp

theorem rowSimplePart_squarefree (I : Ideal O) : Squarefree (rowSimplePart I) := by
  apply (squarefree_iff_nodup_normalizedFactors (rowSimplePart_ne_zero I)).mpr
  rw [normalizedFactors_rowSimplePart]
  apply Multiset.nodup_iff_count_le_one.mpr
  intro P
  rw [Multiset.count_filter]
  split_ifs <;> omega

theorem row_powerful_simple_product (I : Ideal O) (hI : I≠0) :
    rowPowerfulPart I*rowSimplePart I=I := by
  rw [rowPowerfulPart,rowSimplePart,←Multiset.prod_add,Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self hI

theorem row_powerful_simple_coprime (I : Ideal O) :
    IsCoprime (rowPowerfulPart I) (rowSimplePart I) := by
  apply ideals_coprime_of_relprime
  apply (isRelPrime_iff_no_prime_factors (rowPowerfulPart_ne_zero I)).mpr
  intro P hp hs hP
  have hp' := (UniqueFactorizationMonoid.mem_normalizedFactors_iff (rowPowerfulPart_ne_zero I)).mpr ⟨hP,hp⟩
  have hs' := (UniqueFactorizationMonoid.mem_normalizedFactors_iff (rowSimplePart_ne_zero I)).mpr ⟨hP,hs⟩
  rw [normalizedFactors_rowPowerfulPart] at hp'
  rw [normalizedFactors_rowSimplePart] at hs'
  exact (Multiset.mem_filter.mp hs').2 (Multiset.mem_filter.mp hp').2

theorem rowSimplePart_norm (I : Ideal O) (hI : I≠0) :
    (Ideal.absNorm (rowSimplePart I):ℝ)=
      (Ideal.absNorm I:ℝ)/(Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  have hp : (Ideal.absNorm (rowPowerfulPart I):ℝ)≠0 := by
    exact_mod_cast (fun hz => rowPowerfulPart_ne_zero I (Ideal.absNorm_eq_zero_iff.mp hz))
  apply (eq_div_iff hp).mpr
  have he := congrArg (fun J : Ideal O => (Ideal.absNorm J:ℝ)) (row_powerful_simple_product I hI)
  simpa only [map_mul,Nat.cast_mul,mul_comm] using he


def squarefreeMaskPart (I R : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (fun P => P∣R)).prod

def squarefreeResidualPart (I R : Ideal O) : Ideal O :=
  ((normalizedFactors I).filter (fun P => ¬P∣R)).prod

theorem squarefreeMaskPart_ne_zero (I R : Ideal O) : squarefreeMaskPart I R≠0 :=
  Multiset.prod_ne_zero (fun h => zero_notMem_normalizedFactors I (Multiset.mem_filter.mp h).1)

theorem squarefreeResidualPart_ne_zero (I R : Ideal O) : squarefreeResidualPart I R≠0 :=
  Multiset.prod_ne_zero (fun h => zero_notMem_normalizedFactors I (Multiset.mem_filter.mp h).1)

theorem normalizedFactors_squarefreeMaskPart (I R : Ideal O) :
    normalizedFactors (squarefreeMaskPart I R)=(normalizedFactors I).filter (fun P => P∣R) :=
  normalizedFactors_prod_of_prime (fun P hP => prime_of_normalized_factor P (Multiset.mem_filter.mp hP).1)

theorem normalizedFactors_squarefreeResidualPart (I R : Ideal O) :
    normalizedFactors (squarefreeResidualPart I R)=(normalizedFactors I).filter (fun P => ¬P∣R) :=
  normalizedFactors_prod_of_prime (fun P hP => prime_of_normalized_factor P (Multiset.mem_filter.mp hP).1)

theorem squarefreeMaskPart_squarefree (I R : Ideal O) (hI : Squarefree I) : Squarefree (squarefreeMaskPart I R) := by
  apply (squarefree_iff_nodup_normalizedFactors (squarefreeMaskPart_ne_zero I R)).mpr
  rw [normalizedFactors_squarefreeMaskPart]
  exact ((squarefree_iff_nodup_normalizedFactors hI.ne_zero).mp hI).filter _

theorem squarefreeResidualPart_squarefree (I R : Ideal O) (hI : Squarefree I) : Squarefree (squarefreeResidualPart I R) := by
  apply (squarefree_iff_nodup_normalizedFactors (squarefreeResidualPart_ne_zero I R)).mpr
  rw [normalizedFactors_squarefreeResidualPart]
  exact ((squarefree_iff_nodup_normalizedFactors hI.ne_zero).mp hI).filter _

theorem squarefree_mask_residual_product (I R : Ideal O) (hI : I≠0) :
    squarefreeMaskPart I R*squarefreeResidualPart I R=I := by
  rw [squarefreeMaskPart,squarefreeResidualPart,←Multiset.prod_add,Multiset.filter_add_not]
  exact Ideal.prod_normalizedFactors_eq_self hI

theorem squarefreeResidualPart_coprime (I R : Ideal O) : IsCoprime (squarefreeResidualPart I R) R := by
  apply ideals_coprime_of_relprime
  apply (isRelPrime_iff_no_prime_factors (squarefreeResidualPart_ne_zero I R)).mpr
  intro P hp hr hP
  have hm := (UniqueFactorizationMonoid.mem_normalizedFactors_iff (squarefreeResidualPart_ne_zero I R)).mpr ⟨hP,hp⟩
  rw [normalizedFactors_squarefreeResidualPart] at hm
  exact (Multiset.mem_filter.mp hm).2 hr

theorem squarefreeMaskPart_dvd (I R : Ideal O) (hI : Squarefree I) : squarefreeMaskPart I R∣R := by
  by_cases hR : R=0
  · rw [hR]; exact dvd_zero _
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (squarefreeMaskPart_ne_zero I R) hR).mpr
  rw [normalizedFactors_squarefreeMaskPart]
  apply Multiset.le_iff_count.mpr
  intro P
  rw [Multiset.count_filter]
  split_ifs with hp
  · have hn := Multiset.nodup_iff_count_le_one.mp ((squarefree_iff_nodup_normalizedFactors hI.ne_zero).mp hI) P
    by_cases hz : (normalizedFactors I).count P=0
    · omega
    · have hm := Multiset.count_pos.mp (Nat.pos_of_ne_zero hz)
      have hr := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hR).mpr ⟨prime_of_normalized_factor P hm,hp⟩
      have hc := Multiset.count_pos.mpr hr
      omega
  · omega

/-- The squarefree part supported on the fixed modulus. -/
def rowMaskPart (I R : Ideal O) : Ideal O := squarefreeMaskPart (rowSimplePart I) R
/-- The squarefree part coprime to the fixed modulus. -/
def rowResidualPart (I R : Ideal O) : Ideal O := squarefreeResidualPart (rowSimplePart I) R

theorem row_powerful_mask_residual_product (I R : Ideal O) (hI : I≠0) :
    rowPowerfulPart I*rowMaskPart I R*rowResidualPart I R=I := by
  rw [mul_assoc,rowMaskPart,rowResidualPart,squarefree_mask_residual_product _ _ (rowSimplePart_ne_zero I),
    row_powerful_simple_product I hI]

theorem rowMaskPart_dvd (I R : Ideal O) : rowMaskPart I R∣R :=
  squarefreeMaskPart_dvd _ _ (rowSimplePart_squarefree I)

theorem rowResidualPart_squarefree (I R : Ideal O) : Squarefree (rowResidualPart I R) :=
  squarefreeResidualPart_squarefree _ _ (rowSimplePart_squarefree I)

theorem rowResidualPart_admissible (I R : Ideal O) (hbad : ∀P∈fixedBadPrimes,P∣R) :
    quadraticIdealAdmissible (rowResidualPart I R) :=
  admissible_of_squarefree_coprime_bad _ R (rowResidualPart_squarefree I R)
    (squarefreeResidualPart_coprime (rowSimplePart I) R) hbad

theorem rowResidualPart_prime_exponent (I R P : Ideal O)
    (hP : P∈normalizedFactors (rowResidualPart I R)) :
    P∈normalizedFactors I ∧ (normalizedFactors I).count P=1 ∧ ¬P∣R := by
  rw [rowResidualPart,normalizedFactors_squarefreeResidualPart] at hP
  obtain ⟨hs,hr⟩ := Multiset.mem_filter.mp hP
  rw [normalizedFactors_rowSimplePart] at hs
  obtain ⟨hi,hcount⟩ := Multiset.mem_filter.mp hs
  exact ⟨hi,by have hp := Multiset.count_pos.mpr hi; omega,hr⟩

theorem rowResidualPart_norm (I R : Ideal O) (hI : I≠0) :
    (Ideal.absNorm (rowResidualPart I R):ℝ)=(Ideal.absNorm I:ℝ)/
      ((Ideal.absNorm (rowPowerfulPart I):ℝ)*(Ideal.absNorm (rowMaskPart I R):ℝ)) := by
  have hp : (Ideal.absNorm (rowPowerfulPart I):ℝ)≠0 := by
    exact_mod_cast (fun hz => rowPowerfulPart_ne_zero I (Ideal.absNorm_eq_zero_iff.mp hz))
  have ht : (Ideal.absNorm (rowMaskPart I R):ℝ)≠0 := by
    exact_mod_cast (fun hz => squarefreeMaskPart_ne_zero (rowSimplePart I) R (Ideal.absNorm_eq_zero_iff.mp hz))
  apply (eq_div_iff (mul_ne_zero hp ht)).mpr
  have he := congrArg (fun J : Ideal O => (Ideal.absNorm J:ℝ)) (row_powerful_mask_residual_product I R hI)
  simpa only [map_mul,Nat.cast_mul,mul_comm] using he

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion UniqueFactorizationMonoid
open scoped BigOperators Classical

/-- Rows sharing the same powerful part and fixed-modulus squarefree part. -/
def completedRowFiber (S : Finset (Ideal O)) (Q A T : Ideal O) : Finset (Ideal O) :=
  S.filter (fun I => rowPowerfulPart I=A ∧ rowMaskPart I Q=T)

theorem rowResidualPart_injective_on_fiber (S : Finset (Ideal O)) (Q A T : Ideal O)
    (hS : ∀I∈S,I≠0) : Set.InjOn (fun I => rowResidualPart I Q) (completedRowFiber S Q A T) := by
  intro I hI J hJ he
  change rowResidualPart I Q=rowResidualPart J Q at he
  obtain ⟨hIS,hIA,hIT⟩ := Finset.mem_filter.mp hI
  obtain ⟨hJS,hJA,hJT⟩ := Finset.mem_filter.mp hJ
  calc
    I = rowPowerfulPart I*rowMaskPart I Q*rowResidualPart I Q := (row_powerful_mask_residual_product I Q (hS I hIS)).symm
    _ = rowPowerfulPart J*rowMaskPart J Q*rowResidualPart J Q := by rw [hIA,hJA,hIT,hJT,he]
    _ = J := row_powerful_mask_residual_product J Q (hS J hJS)

theorem completedRowFiber_residual_range (S : Finset (Ideal O)) (Q A T : Ideal O)
    (hbad : ∀P∈fixedBadPrimes,P∣Q) (K : ℝ)
    (hS : ∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) (I : Ideal O)
    (hI : I∈completedRowFiber S Q A T) :
    rowResidualPart I Q∈idealRange (K/((Ideal.absNorm A:ℝ)*(Ideal.absNorm T:ℝ))) := by
  obtain ⟨hIS,hIA,hIT⟩ := Finset.mem_filter.mp hI
  apply mem_idealRange.mpr
  refine ⟨rowResidualPart_admissible I Q hbad,?_⟩
  rw [rowResidualPart_norm I Q (hS I hIS).1,hIA,hIT]
  exact div_le_div_of_nonneg_right (hS I hIS).2 (by positivity)

theorem completedRowFiber_energy_le (S : Finset (Ideal O)) (Q A T : Ideal O)
    (hbad : ∀P∈fixedBadPrimes,P∣Q) (K : ℝ)
    (hS : ∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤K) (f : Ideal O→ℂ) :
    (∑I∈completedRowFiber S Q A T,‖f (rowResidualPart I Q)‖^2)≤
      ∑J : idealRange (K/((Ideal.absNorm A:ℝ)*(Ideal.absNorm T:ℝ))),‖f J.val‖^2 := by
  let U := (completedRowFiber S Q A T).image (fun I => rowResidualPart I Q)
  have he : (∑I∈completedRowFiber S Q A T,‖f (rowResidualPart I Q)‖^2)=∑J∈U,‖f J‖^2 := by
    rw [Finset.sum_image (rowResidualPart_injective_on_fiber S Q A T (fun I hI => (hS I hI).1))]
  rw [he,Finset.sum_coe_sort (s := idealRange (K/((Ideal.absNorm A:ℝ)*(Ideal.absNorm T:ℝ)))) (f := fun J : Ideal O => ‖f J‖^2)]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro J hJ
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hJ
    exact completedRowFiber_residual_range S Q A T hbad K hS I hI
  · intro _ _ _
    exact sq_nonneg _

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion UniqueFactorizationMonoid
open scoped BigOperators Classical

lemma powerful_quadratic_decomposition (I : Ideal O) (hI : I≠0) :
    quadraticSquarePart I ^ 2*quadraticSquarefreePart I=I := by
  simpa only [mul_comm] using quadraticParts_mul_square I hI

theorem powerful_squarefree_dvd_squarePart (I : Ideal O) (hI : PowerfulIdeal I) :
    quadraticSquarefreePart I ∣ quadraticSquarePart I := by
  have ha := quadraticSquarePart_ne_zero I
  have hb := (quadraticSquarefreePart_squarefree I).ne_zero
  apply (dvd_iff_normalizedFactors_le_normalizedFactors hb ha).mpr
  apply Multiset.le_iff_count.mpr
  intro P
  have he := congrArg normalizedFactors (powerful_quadratic_decomposition I hI.1)
  rw [normalizedFactors_mul (pow_ne_zero _ ha) hb,normalizedFactors_pow] at he
  have hc := congrArg (Multiset.count P) he
  simp only [Multiset.count_add,Multiset.count_nsmul] at hc
  have hsf := Multiset.nodup_iff_count_le_one.mp
    ((squarefree_iff_nodup_normalizedFactors hb).mp (quadraticSquarefreePart_squarefree I)) P
  by_cases hzero : (normalizedFactors (quadraticSquarefreePart I)).count P=0
  · omega
  · have hm : P∈normalizedFactors I := Multiset.count_pos.mp (by omega)
    have hp := hI.2 P hm
    omega

theorem powerful_exists_square_cube (I : Ideal O) (hI : PowerfulIdeal I) :
    ∃A : Ideal O, A≠0 ∧ A^2*quadraticSquarefreePart I ^ 3=I := by
  obtain ⟨A,hA⟩ := powerful_squarefree_dvd_squarePart I hI
  have ha : A≠0 := by
    intro hz
    have h := quadraticSquarePart_ne_zero I
    apply h
    rw [hA,hz,mul_zero]
  refine ⟨A,ha,?_⟩
  calc
    _ = (quadraticSquarefreePart I*A)^2*quadraticSquarefreePart I := by ring
    _ = quadraticSquarePart I ^ 2*quadraticSquarefreePart I := by rw [←hA]
    _ = I := powerful_quadratic_decomposition I hI.1

def powerfulBase (I : Ideal O) : Ideal O :=
  if hI : PowerfulIdeal I then (powerful_exists_square_cube I hI).choose else 0

theorem powerfulBase_spec (I : Ideal O) (hI : PowerfulIdeal I) :
    powerfulBase I≠0 ∧ powerfulBase I ^ 2*quadraticSquarefreePart I ^ 3=I := by
  rw [powerfulBase,dif_pos hI]
  exact (powerful_exists_square_cube I hI).choose_spec

theorem powerfulBase_injective_on_fiber (I J : Ideal O)
    (hI : PowerfulIdeal I) (hJ : PowerfulIdeal J)
    (hb : quadraticSquarefreePart I=quadraticSquarefreePart J) (ha : powerfulBase I=powerfulBase J) : I=J := by
  rw [←(powerfulBase_spec I hI).2,←(powerfulBase_spec J hJ).2,ha,hb]


end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion UniqueFactorizationMonoid
open scoped BigOperators Classical

/-- A uniform bound for the reciprocal norms of powerful ideals. -/
def powerfulReciprocalConstant : ℝ := finite_inverse_norm_square_bound.choose^2

lemma powerfulReciprocalConstant_pos : 0<powerfulReciprocalConstant :=
  pow_pos finite_inverse_norm_square_bound.choose_spec.1 2

theorem powerful_inverse_norm_sum (S : Finset (Ideal O))
    (hS : ∀I∈S,PowerfulIdeal I) :
    (∑I∈S,1/(Ideal.absNorm I:ℝ))≤powerfulReciprocalConstant := by
  let A := S.image powerfulBase
  let B := S.image quadraticSquarefreePart
  let pair : Ideal O→Ideal O×Ideal O := fun I => (powerfulBase I,quadraticSquarefreePart I)
  have ha (I : Ideal O) (hI : I∈A) : I≠0 := by
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    exact (powerfulBase_spec J (hS J hJ)).1
  have hb (I : Ideal O) (hI : I∈B) : I≠0 := by
    obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
    exact (quadraticSquarefreePart_squarefree J).ne_zero
  let C : ℝ := finite_inverse_norm_square_bound.choose
  have hC : 0<C := finite_inverse_norm_square_bound.choose_spec.1
  have hca := finite_inverse_norm_square_bound.choose_spec.2 A
  have hcb := finite_inverse_norm_square_bound.choose_spec.2 B
  have hinj : Set.InjOn pair S := by
    intro I hI J hJ he
    exact powerfulBase_injective_on_fiber I J (hS I hI) (hS J hJ)
      (congrArg Prod.snd he) (congrArg Prod.fst he)
  have hsub : S.image pair ⊆ A×ˢB := by
    intro p hp
    obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hp
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hI,Finset.mem_image_of_mem _ hI⟩
  calc
    _ ≤ ∑I∈S,1/(Ideal.absNorm (powerfulBase I):ℝ)^2 *
        (1/(Ideal.absNorm (quadraticSquarefreePart I):ℝ)^2) := by
      apply Finset.sum_le_sum
      intro I hI
      have hni := (powerfulBase_spec I (hS I hI)).2
      have hb1 : 1≤(Ideal.absNorm (quadraticSquarefreePart I):ℝ) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr
          (fun hz => (quadraticSquarefreePart_squarefree I).ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
      have ha0 : 0<(Ideal.absNorm (powerfulBase I):ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero
          (fun hz => (powerfulBase_spec I (hS I hI)).1 (Ideal.absNorm_eq_zero_iff.mp hz))
      have he : (Ideal.absNorm I:ℝ)=(Ideal.absNorm (powerfulBase I):ℝ)^2*
          (Ideal.absNorm (quadraticSquarefreePart I):ℝ)^3 := by
        have h := congrArg (fun J : Ideal O => (Ideal.absNorm J:ℝ)) hni
        simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using h.symm
      rw [he,one_div,one_div,one_div,←mul_inv]
      exact inv_anti₀ (by positivity)
        (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hb1 (by decide)) (sq_nonneg _))
    _ = ∑p∈S.image pair,1/(Ideal.absNorm p.1:ℝ)^2 * (1/(Ideal.absNorm p.2:ℝ)^2) := by
      rw [Finset.sum_image hinj]
    _ ≤ ∑p∈A×ˢB,1/(Ideal.absNorm p.1:ℝ)^2 * (1/(Ideal.absNorm p.2:ℝ)^2) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ = (∑I∈A,1/(Ideal.absNorm I:ℝ)^2)*(∑I∈B,1/(Ideal.absNorm I:ℝ)^2) := by
      rw [Finset.sum_product,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro I _
      rw [Finset.mul_sum]
    _ ≤ C*C := mul_le_mul hca hcb (by positivity) hC.le
    _ = _ := by simp only [powerfulReciprocalConstant,C,pow_two]

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion UniqueFactorizationMonoid
open scoped BigOperators Classical

open IdealDivisorBound

theorem sum_completedRowFibers (S : Finset (Ideal O)) (Q : Ideal O) (f : Ideal O→ℝ) :
    (∑A∈S.image rowPowerfulPart,∑T∈S.image (fun I => rowMaskPart I Q),
      ∑I∈completedRowFiber S Q A T,f I)=∑I∈S,f I := by
  let mapPair : Ideal O→Ideal O×Ideal O := fun I => (rowPowerfulPart I,rowMaskPart I Q)
  have hm : ∀I∈S,mapPair I∈(S.image rowPowerfulPart)×ˢ(S.image (fun J => rowMaskPart J Q)) := by
    intro I hI
    exact Finset.mem_product.mpr ⟨Finset.mem_image_of_mem _ hI,Finset.mem_image_of_mem _ hI⟩
  have hh := Finset.sum_fiberwise_of_maps_to hm f
  rw [Finset.sum_product] at hh
  simpa only [mapPair,Prod.mk.injEq,completedRowFiber] using hh

theorem rowMaskPart_image_card (S : Finset (Ideal O)) (Q : Ideal O) (hQ : Q≠0) :
    (S.image (fun I => rowMaskPart I Q)).card≤(idealDivisors Q).card := by
  apply Finset.card_le_card
  intro T hT
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hT
  exact (mem_idealDivisors hQ).mpr (rowMaskPart_dvd I Q)

theorem completed_outer_row_sum_bound (S : Finset (Ideal O)) (Q : Ideal O) (hQ : Q≠0)
    (f : Ideal O→ℝ) (C : ℝ) (hC : 0≤C)
    (hblocks : ∀A∈S.image rowPowerfulPart,∀T∈S.image (fun I => rowMaskPart I Q),
      (∑I∈completedRowFiber S Q A T,f I)≤C/(Ideal.absNorm A:ℝ)) :
    (∑I∈S,f I)≤powerfulReciprocalConstant*((idealDivisors Q).card:ℝ)*C := by
  rw [←sum_completedRowFibers S Q f]
  calc
    _ ≤ ∑A∈S.image rowPowerfulPart,∑T∈S.image (fun I => rowMaskPart I Q),C/(Ideal.absNorm A:ℝ) := by
      apply Finset.sum_le_sum
      intro A hA
      exact Finset.sum_le_sum (fun T hT => hblocks A hA T hT)
    _ = ((S.image (fun I => rowMaskPart I Q)).card:ℝ)*C*
        ∑A∈S.image rowPowerfulPart,1/(Ideal.absNorm A:ℝ) := by
      simp only [Finset.sum_const,nsmul_eq_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro A hA
      ring
    _ ≤ ((S.image (fun I => rowMaskPart I Q)).card:ℝ)*C*powerfulReciprocalConstant := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply powerful_inverse_norm_sum
      intro A hA
      obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hA
      exact rowPowerfulPart_powerful I
    _ ≤ ((idealDivisors Q).card:ℝ)*C*powerfulReciprocalConstant := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (rowMaskPart_image_card S Q hQ)) hC) powerfulReciprocalConstant_pos.le
    _ = _ := by ring

theorem completed_outer_row_small_power (ε : ℝ) (hε : 0<ε) :
    ∃D : ℝ,0<D ∧ ∀(S : Finset (Ideal O)) (Q : Ideal O),Q≠0 →
      ∀(f : Ideal O→ℝ) (C : ℝ),0≤C →
      (∀A∈S.image rowPowerfulPart,∀T∈S.image (fun I => rowMaskPart I Q),
        (∑I∈completedRowFiber S Q A T,f I)≤C/(Ideal.absNorm A:ℝ)) →
      (∑I∈S,f I)≤D*(Ideal.absNorm Q:ℝ)^ε*C := by
  obtain ⟨D,hD,hbound⟩ := IdealDivisorBound.ideal_divisor_small_power ε hε
  refine ⟨powerfulReciprocalConstant*D,mul_pos powerfulReciprocalConstant_pos hD,?_⟩
  intro S Q hQ f C hC hblocks
  apply (completed_outer_row_sum_bound S Q hQ f C hC hblocks).trans
  have hh := mul_le_mul_of_nonneg_right (hbound Q hQ) hC
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh powerfulReciprocalConstant_pos.le

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion UniqueFactorizationMonoid
open scoped BigOperators Classical

theorem prime_square_dvd_powerful (I P : Ideal O) (hI : PowerfulIdeal I)
    (hP : Prime P) (hd : P∣I) : P^2∣I := by
  have hm := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hI.1).mpr ⟨hP,hd⟩
  apply (dvd_iff_normalizedFactors_le_normalizedFactors (pow_ne_zero 2 hP.ne_zero) hI.1).mpr
  rw [normalizedFactors_pow,normalizedFactors_irreducible hP.irreducible,normalize_eq]
  apply Multiset.le_iff_count.mpr
  intro Q
  by_cases hQP : Q=P
  · subst Q
    simpa using hI.2 P hm
  · simp [hQP]

theorem nonresidual_prime_square_dvd (I Q P : Ideal O) (hI : I≠0) (hP : Prime P)
    (hd : P∣I) (hr : ¬P∣rowResidualPart I Q) :
    P^2∣rowPowerfulPart I*(rowMaskPart I Q)^2 := by
  have hh : P∣rowPowerfulPart I*rowMaskPart I Q := by
    rw [←row_powerful_mask_residual_product I Q hI] at hd
    exact (hP.dvd_mul.mp hd).resolve_right hr
  rcases hP.dvd_mul.mp hh with ha|ht
  · exact dvd_mul_of_dvd_left (prime_square_dvd_powerful _ _ (rowPowerfulPart_powerful I) hP ha) _
  · exact dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd ht 2) _

def nonresidualGain (I P : Ideal O) : Ideal O := if P∣I then P^2 else P

theorem nonresidual_gain_product_dvd {ι : Type*} [Fintype ι]
    (I Q : Ideal O) (hI : I≠0) (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀i,P i∣I*Q) (hres : ∀i,¬P i∣rowResidualPart I Q) :
    (∏i,nonresidualGain I (P i)) ∣ rowPowerfulPart I*(rowMaskPart I Q)^2*Q := by
  apply Fintype.prod_dvd_of_coprime
  · intro i j hij
    change IsCoprime (nonresidualGain I (P i)) (nonresidualGain I (P j))
    unfold nonresidualGain
    by_cases hi : P i∣I
    · rw [if_pos hi]
      by_cases hj : P j∣I
      · rw [if_pos hj]
        exact (hcop hij).pow
      · rw [if_neg hj]
        exact (hcop hij).pow_left
    · rw [if_neg hi]
      by_cases hj : P j∣I
      · rw [if_pos hj]
        exact (hcop hij).pow_right
      · rw [if_neg hj]
        exact hcop hij
  · intro i
    have hp : Prime (P i) := Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance
    by_cases hi : P i∣I
    · rw [nonresidualGain,if_pos hi]
      exact dvd_mul_of_dvd_left (nonresidual_prime_square_dvd I Q (P i) hI hp hi (hres i)) Q
    · rw [nonresidualGain,if_neg hi]
      exact dvd_mul_of_dvd_right ((hp.dvd_mul.mp (hpool i)).resolve_left hi) _

open Eisenstein UniqueFactorizationMonoid

/-- Sextic exponent after the fourth-power column twist. -/
def completedLocalExponent (I F P : Ideal O) : ℕ :=
  ((normalizedFactors I).count P+4*(if P∣F then 1 else 0))%6

def reflectionExtractedPrime (P : Ideal O) (j : ℕ) (e v : Fin 3) : Ideal O :=
  if (j=4 ∧ e=v) ∨ (j=0 ∧ v=0) then P else 1

/-- Divisor forced into each frequency variable by an exceptional local term. -/
def reflectionExtractedDivisor {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (j : ι→ℕ) (e : ι→Fin 3) (v : Fin 3) : Ideal O :=
  ∏i,reflectionExtractedPrime (P i) (j i) (e i) v

def reflectionConductorCost {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (j : ι→ℕ) (e : ι→Fin 3) : ℝ :=
  (Ideal.absNorm (∏i,P i):ℝ)^2/
    ((Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*
     (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
     (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)^4)

def reflectionLocalCost (q : ℝ) (j : ℕ) (e : Fin 3) : ℝ :=
  if j=4 then (if e=2 then 1/q^2 else q)
  else if j=0 then q else q^2

theorem reflectionConductorCost_eq_prod {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (hP : ∀i,P i≠0) (j : ι→ℕ) (e : ι→Fin 3) :
    reflectionConductorCost P j e=∏i,reflectionLocalCost (Ideal.absNorm (P i):ℝ) (j i) (e i) := by
  have hn i : (Ideal.absNorm (P i):ℝ)≠0 := by
    exact_mod_cast (fun hz => hP i (Ideal.absNorm_eq_zero_iff.mp hz))
  simp only [reflectionConductorCost,reflectionExtractedDivisor,map_prod,Nat.cast_prod,
    ←Finset.prod_pow,←Finset.prod_mul_distrib,←Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hj4 : j i=4
  · rw [hj4]
    generalize he : e i=v
    fin_cases v <;> simp [reflectionExtractedPrime,reflectionLocalCost] <;> field_simp
  · by_cases hj0 : j i=0
    · simp [reflectionExtractedPrime,reflectionLocalCost,hj0]
      field_simp
    · simp [reflectionExtractedPrime,reflectionLocalCost,hj4,hj0]

theorem reflectionLocalCost_nonneg (q : ℝ) (hq : 0≤q) (j : ℕ) (e : Fin 3) :
    0≤reflectionLocalCost q j e := by
  unfold reflectionLocalCost
  split_ifs <;> positivity

theorem reflectionLocalCost_le_square (q : ℝ) (hq : 1≤q) (j : ℕ) (e : Fin 3) :
    reflectionLocalCost q j e≤q^2 := by
  have hq0 : 0<q := by linarith
  have hq2 : 1≤q^2 := one_le_pow₀ hq
  unfold reflectionLocalCost
  split_ifs
  · exact (div_le_one (by positivity)).mpr hq2 |>.trans hq2
  · nlinarith
  · nlinarith
  · rfl

theorem reflectionLocalCost_le_single (q : ℝ) (hq : 1≤q) (j : ℕ) (e : Fin 3)
    (hj : j=0 ∨ j=4) : reflectionLocalCost q j e≤q := by
  have hq0 : 0<q := by linarith
  rcases hj with rfl|rfl
  · simp [reflectionLocalCost]
  · simp only [reflectionLocalCost,ite_true]
    split_ifs
    · exact ((div_le_one (by positivity)).mpr (one_le_pow₀ hq)).trans hq
    · rfl

theorem completedLocalExponent_of_not_dvd (I F P : Ideal O) (hI : I≠0) (_hP : Prime P)
    (hn : ¬P∣I) : completedLocalExponent I F P=0 ∨ completedLocalExponent I F P=4 := by
  have hm : P∉normalizedFactors I := by
    intro h
    exact hn ((UniqueFactorizationMonoid.mem_normalizedFactors_iff hI).mp h).2
  simp only [completedLocalExponent,Multiset.count_eq_zero.mpr hm,zero_add]
  split_ifs <;> norm_num

theorem reflectionLocalCost_le_gain (I F P : Ideal O) (hI : I≠0) (hP : Prime P) (e : Fin 3) :
    reflectionLocalCost (Ideal.absNorm P:ℝ) (completedLocalExponent I F P) e≤
      (Ideal.absNorm (nonresidualGain I P):ℝ) := by
  have hq : 1≤(Ideal.absNorm P:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hP.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
  by_cases hd : P∣I
  · rw [nonresidualGain,if_pos hd,map_pow,Nat.cast_pow]
    exact reflectionLocalCost_le_square _ hq _ _
  · rw [nonresidualGain,if_neg hd]
    exact reflectionLocalCost_le_single _ hq _ _ (completedLocalExponent_of_not_dvd I F P hI hP hd)

theorem reflectionConductorCost_bound {ι : Type*} [Fintype ι]
    (I F Q : Ideal O) (hI : I≠0) (hQ : Q≠0)
    (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀i,P i∣I*Q) (hres : ∀i,¬P i∣rowResidualPart I Q) (e : ι→Fin 3) :
    reflectionConductorCost P (fun i => completedLocalExponent I F (P i)) e≤
      (Ideal.absNorm (rowPowerfulPart I):ℝ)*(Ideal.absNorm (rowMaskPart I Q):ℝ)^2*(Ideal.absNorm Q:ℝ) := by
  rw [reflectionConductorCost_eq_prod P (fun i => NeZero.ne (P i))]
  have hfirst : (∏i,reflectionLocalCost (Ideal.absNorm (P i):ℝ) (completedLocalExponent I F (P i)) (e i))≤
      (Ideal.absNorm (∏i,nonresidualGain I (P i)):ℝ) := by
    rw [map_prod,Nat.cast_prod]
    exact Finset.prod_le_prod (fun i _ => reflectionLocalCost_nonneg _ (Nat.cast_nonneg _) _ _)
      (fun i _ => reflectionLocalCost_le_gain I F (P i) hI (Ideal.prime_of_isPrime (NeZero.ne (P i)) inferInstance) (e i))
  apply hfirst.trans
  have hd := nonresidual_gain_product_dvd I Q hI P hcop hpool hres
  have hN : 0<Ideal.absNorm (rowPowerfulPart I*(rowMaskPart I Q)^2*Q) := by
    apply Nat.pos_of_ne_zero
    intro hz
    have hne := mul_ne_zero (mul_ne_zero (rowPowerfulPart_ne_zero I)
      (pow_ne_zero 2 (squarefreeMaskPart_ne_zero (rowSimplePart I) Q))) hQ
    exact hne (Ideal.absNorm_eq_zero_iff.mp hz)
  have hb := Nat.le_of_dvd hN (map_dvd Ideal.absNorm hd)
  have hr : (Ideal.absNorm (∏i,nonresidualGain I (P i)):ℝ)≤
      (Ideal.absNorm (rowPowerfulPart I*(rowMaskPart I Q)^2*Q):ℝ) := by exact_mod_cast hb
  simpa only [map_mul,map_pow,Nat.cast_mul,Nat.cast_pow] using hr

end CompletedGauss

namespace CompletedGauss
open Eisenstein NormalizedReflection
open scoped BigOperators Classical

def exceptionalPiece (P : Ideal O) [P.IsMaximal] (e : Fin 3) (n b : O) : ℂ :=
  if e=0 then -(rootCard (O ⧸ P) : ℂ)⁻¹
  else if e=1 then (rootCard (O ⧸ P) : ℂ)*(if n∈P then 1 else 0)
  else (rootCard (O ⧸ P) : ℂ)*(if n∉P ∧ b∈P then 1 else 0)

theorem bracket_four_eq_sum_exceptionalPiece (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (n b : O) :
    bracket (complexSexticChar P hg) 4 (Ideal.Quotient.mk P (n*b^3)) =
      ∑e : Fin 3, exceptionalPiece P e n b := by
  rw [canonical_bracket_four_cube_split]
  simp [Fin.sum_univ_succ,exceptionalPiece]
  ring

theorem rootCard_eq_sqrt_absNorm (P : Ideal O) [P.IsMaximal] :
    rootCard (O ⧸ P)=Real.sqrt (Ideal.absNorm P:ℝ) := by
  rw [rootCard,←Nat.card_eq_fintype_card]
  rfl

theorem exceptionalPiece_norm_le (P : Ideal O) [P.IsMaximal]
    (e : Fin 3) (n b : O) :
    ‖exceptionalPiece P e n b‖≤(if e=0 then (rootCard (O ⧸ P))⁻¹ else rootCard (O ⧸ P)) := by
  have hr : 0≤rootCard (O ⧸ P) := rootCard_pos.le
  fin_cases e <;> simp only [exceptionalPiece,Fin.isValue,Fin.zero_eta,↓reduceIte]
  · simp [abs_of_nonneg hr]
  · by_cases hn : n∈P <;> simp [hn,abs_of_nonneg hr,hr]
  · by_cases hn : n∉P ∧ b∈P <;> simp [hn,abs_of_nonneg hr,hr]


end CompletedGauss

namespace CompletedGauss
open Eisenstein NormalizedReflection
open scoped BigOperators Classical

def reflectedLocalPiece (P : Ideal O) [P.IsMaximal] (hg : lambda∉P)
    (j : ℕ) (e : Fin 3) (n b : O) : ℂ :=
  if j=4 then exceptionalPiece P e n b
  else if e=0 then bracket (complexSexticChar P hg) j (Ideal.Quotient.mk P (n*b^3)) else 0

def reflectedLocalSize (P : Ideal O) [P.IsMaximal] (j : ℕ) (e : Fin 3) : ℝ :=
  if j=4 then (if e=0 then (rootCard (O ⧸ P))⁻¹ else rootCard (O ⧸ P))
  else if j=0 then (rootCard (O ⧸ P))⁻¹ else 1

def reflectedBranch {ι : Type*} [Fintype ι] (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hg : ∀i,lambda∉P i) (j : ι→ℕ) (e : ι→Fin 3) (n b : O) : ℂ :=
  ∏i,reflectedLocalPiece (P i) (hg i) (j i) (e i) n b

theorem bracket_eq_sum_reflectedLocalPiece (P : Ideal O) [P.IsMaximal]
    (hg : lambda∉P) (j : ℕ) (n b : O) :
    bracket (complexSexticChar P hg) j (Ideal.Quotient.mk P (n*b^3))=
      ∑e : Fin 3, reflectedLocalPiece P hg j e n b := by
  by_cases hj : j=4
  · subst j
    simpa only [reflectedLocalPiece,ite_true] using bracket_four_eq_sum_exceptionalPiece P hg n b
  · simp [reflectedLocalPiece,hj]

theorem prod_bracket_eq_full_branches {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (n b : O) :
    (∏i,bracket (complexSexticChar (P i) (hg i)) (j i) (Ideal.Quotient.mk (P i) (n*b^3)))=
      ∑e : ι→Fin 3,reflectedBranch P hg j e n b := by
  simp_rw [bracket_eq_sum_reflectedLocalPiece]
  simpa only [Fintype.piFinset_univ,reflectedBranch] using
    Finset.prod_univ_sum (fun _ : ι => (Finset.univ : Finset (Fin 3)))
      (fun i e => reflectedLocalPiece (P i) (hg i) (j i) e n b)

theorem reflectedLocalPiece_norm_le (P : Ideal O) [P.IsMaximal] (hg : lambda∉P)
    (j : ℕ) (e : Fin 3) (n b : O) :
    ‖reflectedLocalPiece P hg j e n b‖≤reflectedLocalSize P j e := by
  have hr : 0<rootCard (O ⧸ P) := rootCard_pos
  by_cases hj4 : j=4
  · subst j
    simpa only [reflectedLocalPiece,reflectedLocalSize,ite_true] using exceptionalPiece_norm_le P e n b
  · by_cases he : e=0
    · rw [reflectedLocalPiece,if_neg hj4,if_pos he,reflectedLocalSize,if_neg hj4]
      by_cases hj0 : j=0
      · subst j
        simpa only [ite_true] using norm_bracket_zero_le (complexSexticChar P hg) (Ideal.Quotient.mk P (n*b^3))
      · rw [if_neg hj0]
        exact norm_bracket_nonexceptional_le_one _ j hj4 hj0 _
    · simp only [reflectedLocalPiece,if_neg hj4,if_neg he,norm_zero,reflectedLocalSize]
      split_ifs <;> positivity

theorem sqrt_norm_reflectionExtractedDivisor {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (j : ι→ℕ) (e : ι→Fin 3) (v : Fin 3) :
    Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ)=
      ∏i,if (j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0) then rootCard (O ⧸ P i) else 1 := by
  rw [reflectionExtractedDivisor,map_prod,Nat.cast_prod,Real.sqrt_prod]
  · apply Finset.prod_congr rfl
    intro i _
    unfold reflectionExtractedPrime
    split_ifs
    · rw [rootCard_eq_sqrt_absNorm]
    · simp
  · intro i _
    exact Nat.cast_nonneg _

theorem reflectedBranch_norm_bound {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (n b : O) :
    ‖reflectedBranch P hg j e n b‖≤
      Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*
      Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)/
      Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ) := by
  have hb : ‖reflectedBranch P hg j e n b‖≤∏i,reflectedLocalSize (P i) (j i) (e i) := by
    rw [reflectedBranch,norm_prod]
    exact Finset.prod_le_prod (fun i _ => norm_nonneg _)
      (fun i _ => reflectedLocalPiece_norm_le (P i) (hg i) (j i) (e i) n b)
  apply hb.trans_eq
  rw [sqrt_norm_reflectionExtractedDivisor,sqrt_norm_reflectionExtractedDivisor,
    sqrt_norm_reflectionExtractedDivisor,←Finset.prod_mul_distrib,←Finset.prod_div_distrib]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hj4 : j i=4
  · rw [hj4]
    generalize e i=x
    fin_cases x <;> simp [reflectedLocalSize]
  · by_cases hj0 : j i=0
    · simp [reflectedLocalSize,hj0]
    · simp [reflectedLocalSize,hj4,hj0]

theorem reflectionExtractedDivisor_ne_zero {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) (hP : ∀i,P i≠0) (j : ι→ℕ) (e : ι→Fin 3) (v : Fin 3) :
    reflectionExtractedDivisor P j e v≠0 := by
  unfold reflectionExtractedDivisor
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  unfold reflectionExtractedPrime
  split_ifs
  · exact hP i
  · exact one_ne_zero

theorem reflectedBranch_normalized_bound {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (n b : O) (U B : ℝ) (hU : 0<U) (hB : 0<B) :
    ‖reflectedBranch P hg j e n b‖ /
      (Real.sqrt ((Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)*U)*
        ((Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)*B)) ≤
      1/(Real.sqrt U*B*Real.sqrt ((Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
        (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ))) := by
  have hn (v : Fin 3) : 0<(Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e v
      (Ideal.absNorm_eq_zero_iff.mp hz))
  have hs (v : Fin 3) : 0<Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ) := Real.sqrt_pos.mpr (hn v)
  have hsu : 0<Real.sqrt U := Real.sqrt_pos.mpr hU
  apply (div_le_div_of_nonneg_right (reflectedBranch_norm_bound P hg j e n b) (by positivity)).trans
  rw [Real.sqrt_mul (hn 1).le,Real.sqrt_mul (hn 0).le]
  have he := Real.sq_sqrt (hn 2).le
  apply le_of_eq
  field_simp [(hs 0).ne', (hs 1).ne', (hs 2).ne', (hn 2).ne', hsu.ne', hB.ne']
  nlinarith

theorem reflectedBranch_divisibility {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (hcop : Pairwise (fun i k => IsCoprime (P i) (P k)))
    (j : ι→ℕ) (e : ι→Fin 3) (n b : O) (hne : reflectedBranch P hg j e n b≠0) :
    reflectionExtractedDivisor P j e 1∣Ideal.span {n} ∧
    reflectionExtractedDivisor P j e 2∣Ideal.span {b} ∧
    (∀i,j i=4 → e i=2 → n∉P i) := by
  have hn i : reflectedLocalPiece (P i) (hg i) (j i) (e i) n b≠0 :=
    (Finset.prod_ne_zero_iff.mp hne) i (Finset.mem_univ i)
  have hmemn i (hj : j i=4) (he : e i=1) : n∈P i := by
    by_contra hz
    exact hn i (by simp [reflectedLocalPiece,exceptionalPiece,hj,he,hz])
  have hmemb i (hj : j i=4) (he : e i=2) : n∉P i ∧ b∈P i := by
    by_contra hz
    exact hn i (by simp [reflectedLocalPiece,exceptionalPiece,hj,he,hz])
  have hprod (v : Fin 3) (z : O)
      (hz : ∀i,(j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0) → z∈P i) :
      reflectionExtractedDivisor P j e v∣Ideal.span {z} := by
    unfold reflectionExtractedDivisor reflectionExtractedPrime
    apply Fintype.prod_dvd_of_coprime
    · intro i k hik
      change IsCoprime (if (j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0) then P i else 1)
        (if (j k=4 ∧ e k=v) ∨ (j k=0 ∧ v=0) then P k else 1)
      by_cases hi : (j i=4 ∧ e i=v) ∨ (j i=0 ∧ v=0)
      · rw [if_pos hi]
        by_cases hk : (j k=4 ∧ e k=v) ∨ (j k=0 ∧ v=0)
        · rw [if_pos hk]
          exact hcop hik
        · rw [if_neg hk]
          exact isCoprime_one_right
      · rw [if_neg hi]
        exact isCoprime_one_left
    · intro i
      split_ifs with hi
      · rw [Ideal.dvd_iff_le,Ideal.span_le,Set.singleton_subset_iff,SetLike.mem_coe]
        exact hz i hi
      · exact one_dvd _
  refine ⟨hprod 1 n ?_,hprod 2 b ?_,fun i hj he => (hmemb i hj he).1⟩
  · intro i hi
    rcases hi with ⟨hj,he⟩|⟨hj,he⟩
    · exact hmemn i hj he
    · exact False.elim ((by decide : (1:Fin 3)≠0) he)
  · intro i hi
    rcases hi with ⟨hj,he⟩|⟨hj,he⟩
    · exact (hmemb i hj he).2
    · exact False.elim ((by decide : (2:Fin 3)≠0) he)

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion NormalizedReflection UniqueFactorizationMonoid
open scoped BigOperators Classical

theorem completed_fiber_scalar_cost (deltaLoss K X a t Q c D S E : ℝ)
    (hδ : 0≤deltaLoss) (hK : 1≤K) (hX : 1≤X) (ha : 1≤a) (ht : 1≤t) (hQ : 1≤Q)
    (hc0 : 0<c) (hc : c≤K*Q) (hD : 1≤D) (hS : 1≤S) (hE : 1≤E)
    (hcost : c^2/(D*S*E^4)≤a*t^2*Q) :
    let k := K/(a*t)
    let y := k^2*c^2/(X*D*E^3)
    (k*y)^(2*deltaLoss)*(k+y)/(S*E)≤(K*Q)^(10*deltaLoss)*(K+K^2*Q/X)/a := by
  dsimp only
  let k : ℝ := K/(a*t)
  let y : ℝ := k^2*c^2/(X*D*E^3)
  change (k*y)^(2*deltaLoss)*(k+y)/(S*E)≤_
  have ha0 : 0<a := by linarith
  have ht0 : 0<t := by linarith
  have hX0 : 0<X := by linarith
  have hD0 : 0<D := by linarith
  have hS0 : 0<S := by linarith
  have hE0 : 0<E := by linarith
  have hK0 : 0<K := by linarith
  have hQ0 : 0<Q := by linarith
  have hk0 : 0<k := by dsimp [k]; positivity
  have hy0 : 0<y := by dsimp [y]; positivity
  have hat : 1≤a*t := one_le_mul_of_one_le_of_one_le ha ht
  have hk : k≤K := (div_le_self hK0.le hat)
  have hden : 1≤X*D*E^3 := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hX hD) (one_le_pow₀ hE)
  have hy : y≤K^2*(K*Q)^2 := by
    calc
      y ≤ k^2*c^2 := div_le_self (by positivity) hden
      _ ≤ K^2*(K*Q)^2 := mul_le_mul
        (pow_le_pow_left₀ hk0.le hk 2) (pow_le_pow_left₀ hc0.le hc 2) (by positivity) (by positivity)
  have hky : k*y≤(K*Q)^5 := by
    have hQ3 : 1≤Q^3 := one_le_pow₀ hQ
    calc
      k*y ≤ K*(K^2*(K*Q)^2) := mul_le_mul hk hy hy0.le hK0.le
      _ ≤ (K*(K^2*(K*Q)^2))*Q^3 := le_mul_of_one_le_right (by positivity) hQ3
      _ = (K*Q)^5 := by ring
  have hp : (k*y)^(2*deltaLoss)≤(K*Q)^(10*deltaLoss) := by
    have hh := Real.rpow_le_rpow (mul_pos hk0 hy0).le hky (by positivity : 0≤2*deltaLoss)
    convert hh using 1
    rw [←Real.rpow_natCast_mul (mul_pos hK0 hQ0).le]
    congr 1
    ring
  have hfirst : k/(S*E)≤K/a := by
    have hse : 1≤t*(S*E) := one_le_mul_of_one_le_of_one_le ht (one_le_mul_of_one_le_of_one_le hS hE)
    calc
      k/(S*E) = (K/a)/(t*(S*E)) := by dsimp [k]; field_simp
      _ ≤ K/a := div_le_self (by positivity) hse
  have hsecond : y/(S*E)≤K^2*Q/(a*X) := by
    calc
      y/(S*E) = (k^2/X)*(c^2/(D*S*E^4)) := by dsimp [y]; field_simp
      _ ≤ (k^2/X)*(a*t^2*Q) := mul_le_mul_of_nonneg_left hcost (by positivity)
      _ = K^2*Q/(a*X) := by dsimp [k]; field_simp
  have hshape : (k+y)/(S*E)≤(K+K^2*Q/X)/a := by
    calc
      _ = k/(S*E)+y/(S*E) := add_div _ _ _
      _ ≤ K/a+K^2*Q/(a*X) := add_le_add hfirst hsecond
      _ = _ := by ring
  calc
    _ = (k*y)^(2*deltaLoss)*((k+y)/(S*E)) := by ring
    _ ≤ (K*Q)^(10*deltaLoss)*((K+K^2*Q/X)/a) :=
      mul_le_mul hp hshape (by positivity) (by positivity)
    _ = _ := by ring

theorem completed_conductor_norm_bound {ι : Type*} [Fintype ι]
    (I Q : Ideal O) (hI : I≠0) (hQ : Q≠0)
    (P : ι→Ideal O) (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀i,P i∣I*Q) :
    (Ideal.absNorm (∏i,P i):ℝ)≤(Ideal.absNorm I:ℝ)*(Ideal.absNorm Q:ℝ) := by
  have hd : (∏i,P i)∣I*Q := Fintype.prod_dvd_of_coprime hcop hpool
  have hn : 0<Ideal.absNorm (I*Q) := Nat.pos_of_ne_zero (fun hz =>
    mul_ne_zero hI hQ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hh := Nat.le_of_dvd hn (map_dvd Ideal.absNorm hd)
  exact_mod_cast (by simpa only [map_mul] using hh)

theorem completed_actual_fiber_cost {ι : Type*} [Fintype ι]
    (deltaLoss K X : ℝ) (hδ : 0≤deltaLoss) (hK : 1≤K) (hX : 1≤X)
    (I F Q : Ideal O) (hI : I≠0) (hQ : Q≠0) (hIK : (Ideal.absNorm I:ℝ)≤K)
    (P : ι→Ideal O) [∀i,(P i).IsMaximal]
    (hcop : Pairwise (fun i j => IsCoprime (P i) (P j)))
    (hpool : ∀i,P i∣I*Q) (hres : ∀i,¬P i∣rowResidualPart I Q) (e : ι→Fin 3) :
    let j := fun i => completedLocalExponent I F (P i)
    let k := K/((Ideal.absNorm (rowPowerfulPart I):ℝ)*(Ideal.absNorm (rowMaskPart I Q):ℝ))
    let D := (Ideal.absNorm (reflectionExtractedDivisor P j e 1):ℝ)
    let S := (Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)
    let E := (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)
    let y := k^2*(Ideal.absNorm (∏i,P i):ℝ)^2/(X*D*E^3)
    (k*y)^(2*deltaLoss)*(k+y)/(S*E)≤
      (K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
        (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  have hn (J : Ideal O) (hJ : J≠0) : 1≤(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hprod : (∏i,P i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i))
  have hc := (completed_conductor_norm_bound I Q hI hQ P hcop hpool).trans
    (mul_le_mul_of_nonneg_right hIK (Nat.cast_nonneg _))
  have hh := completed_fiber_scalar_cost deltaLoss K X
    (Ideal.absNorm (rowPowerfulPart I):ℝ) (Ideal.absNorm (rowMaskPart I Q):ℝ)
    (Ideal.absNorm Q:ℝ) (Ideal.absNorm (∏i,P i):ℝ)
    (Ideal.absNorm (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 1):ℝ)
    (Ideal.absNorm (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 0):ℝ)
    (Ideal.absNorm (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 2):ℝ)
    hδ hK hX (hn _ (rowPowerfulPart_ne_zero I))
    (hn _ (squarefreeMaskPart_ne_zero (rowSimplePart I) Q)) (hn _ hQ)
    (lt_of_lt_of_le (by norm_num) (hn _ hprod)) hc
    (hn _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) _ e 1))
    (hn _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) _ e 0))
    (hn _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) _ e 2))
    (reflectionConductorCost_bound I F Q hI hQ P hcop hpool hres e)
  exact hh


end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion NormalizedReflection UniqueFactorizationMonoid
open scoped BigOperators Classical

def completedShellWindow (x : ℝ) : ℂ :=
  if -Real.log 2≤x ∧ x≤0 then 1 else 0

theorem completedShellWindow_support (x : ℝ) (h : completedShellWindow x≠0) :
    |x|≤Real.log 2 := by
  have hx : -Real.log 2≤x ∧ x≤0 := by
    by_contra hn
    exact h (by simp [completedShellWindow,hn])
  apply abs_le.mpr
  exact ⟨hx.1,hx.2.trans (Real.log_nonneg (by norm_num))⟩

theorem completedShellWindow_norm (x : ℝ) : ‖completedShellWindow x‖≤1 := by
  unfold completedShellWindow
  split_ifs <;> simp

theorem completedShellWindow_log (x U : ℝ) (hx : 0<x) (hU : 0<U)
    (hlo : U/2≤x) (hhi : x≤U) : completedShellWindow (Real.log (x/U))=1 := by
  apply if_pos
  constructor
  · have hhalf : (1/2:ℝ)≤x/U := (le_div_iff₀ hU).mpr (by linarith)
    have hh := Real.strictMonoOn_log.monotoneOn (by norm_num : (1/2:ℝ)∈Set.Ioi 0)
      (show x/U∈Set.Ioi 0 from div_pos hx hU) hhalf
    simpa only [one_div,Real.log_inv] using hh
  · exact Real.log_nonpos (div_nonneg hx.le hU.le) ((div_le_one hU).mpr hhi)

theorem dyadic_root_product_bound (u v U B : ℝ) (hu : 0<u) (_hv : 0<v)
    (hU : 0<U) (hB : 0<B) (huU : U/2≤u) (hvB : B/2≤v) :
    Real.sqrt U*B≤4*(Real.sqrt u*v) := by
  have hs : Real.sqrt U≤2*Real.sqrt u := by
    apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mp
    rw [mul_pow,Real.sq_sqrt hU.le,Real.sq_sqrt hu.le]
    nlinarith
  calc
    _ ≤ (2*Real.sqrt u)*(2*v) := mul_le_mul hs (by linarith) hB.le (by positivity)
    _ = _ := by ring

def reflectedDyadicCoefficient {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (η : Ideal O→Ideal O→ℂ) (r : ℝ)
    (n v : Ideal O) : ℂ :=
  η n v*reflectedBranch P hg j e
    (primaryIdealGenerator (reflectionExtractedDivisor P j e 1*n))
    (primaryIdealGenerator (reflectionExtractedDivisor P j e 2*v))/
    ((4*r*Real.sqrt (Ideal.absNorm (reflectionExtractedDivisor P j e 1*n):ℝ)*
      (Ideal.absNorm (reflectionExtractedDivisor P j e 2*v):ℝ):ℝ):ℂ)

theorem reflectedDyadicCoefficient_norm {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (η : Ideal O→Ideal O→ℂ) (r U B : ℝ)
    (hr : 0<r) (hU : 0<U) (hB : 0<B) (n v : Ideal O) (hn : n≠0) (hv : v≠0)
    (hη : ‖η n v‖≤1) (hlo : U/2≤(Ideal.absNorm n:ℝ)) (hlov : B/2≤(Ideal.absNorm v:ℝ)) :
    ‖reflectedDyadicCoefficient P hg j e η r n v‖≤
      1/(Real.sqrt U*B*r*Real.sqrt
        ((Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
          (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ))) := by
  let D := reflectionExtractedDivisor P j e 1
  let E := reflectionExtractedDivisor P j e 2
  let S := reflectionExtractedDivisor P j e 0
  have hnorm (J : Ideal O) (hJ : J≠0) : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hDn := hnorm D (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e 1)
  have hEn := hnorm E (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e 2)
  have hSn := hnorm S (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e 0)
  have hnn := hnorm n hn
  have hvn := hnorm v hv
  have hlocal := reflectedBranch_normalized_bound P hg j e
    (primaryIdealGenerator (D*n)) (primaryIdealGenerator (E*v))
    (Ideal.absNorm n:ℝ) (Ideal.absNorm v:ℝ) hnn hvn
  change ‖reflectedBranch P hg j e (primaryIdealGenerator (D*n)) (primaryIdealGenerator (E*v))‖ /
      (Real.sqrt ((Ideal.absNorm D:ℝ)*(Ideal.absNorm n:ℝ))*
        ((Ideal.absNorm E:ℝ)*(Ideal.absNorm v:ℝ)))≤
      1/(Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm v:ℝ)*
        Real.sqrt ((Ideal.absNorm S:ℝ)*(Ideal.absNorm E:ℝ))) at hlocal
  have hbase : 0<Real.sqrt ((Ideal.absNorm S:ℝ)*(Ideal.absNorm E:ℝ)) := by positivity
  have hroot := dyadic_root_product_bound _ _ U B hnn hvn hU hB hlo hlov
  unfold reflectedDyadicCoefficient
  change ‖η n v*reflectedBranch P hg j e (primaryIdealGenerator (D*n)) (primaryIdealGenerator (E*v))/
    ((4*r*Real.sqrt (Ideal.absNorm (D*n):ℝ)*(Ideal.absNorm (E*v):ℝ):ℝ):ℂ)‖≤_
  rw [norm_div,norm_mul,Complex.norm_real,Real.norm_of_nonneg (by positivity)]
  simp only [map_mul,Nat.cast_mul]
  calc
    _ ≤ ‖reflectedBranch P hg j e (primaryIdealGenerator (D*n)) (primaryIdealGenerator (E*v))‖/
      (4*r*Real.sqrt ((Ideal.absNorm D:ℝ)*(Ideal.absNorm n:ℝ))*
        ((Ideal.absNorm E:ℝ)*(Ideal.absNorm v:ℝ))) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_of_le_one_left (norm_nonneg _) hη
    _ = (1/(4*r))*(‖reflectedBranch P hg j e (primaryIdealGenerator (D*n)) (primaryIdealGenerator (E*v))‖/
      (Real.sqrt ((Ideal.absNorm D:ℝ)*(Ideal.absNorm n:ℝ))*
        ((Ideal.absNorm E:ℝ)*(Ideal.absNorm v:ℝ)))) := by ring
    _ ≤ (1/(4*r))*(1/(Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm v:ℝ)*
      Real.sqrt ((Ideal.absNorm S:ℝ)*(Ideal.absNorm E:ℝ)))) :=
        mul_le_mul_of_nonneg_left hlocal (by positivity)
    _ = 1/(4*(Real.sqrt (Ideal.absNorm n:ℝ)*(Ideal.absNorm v:ℝ))*r*
      Real.sqrt ((Ideal.absNorm S:ℝ)*(Ideal.absNorm E:ℝ))) := by ring
    _ ≤ _ := by
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hroot hr.le) hbase.le


end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

/-- The finite ideal range and the native quadratic sieve index the same conductors. -/
def idealRangeEquiv (K : ℝ) : idealRange K ≃ QuadraticIdealRange K where
  toFun I:=⟨⟨I.val,(mem_idealRange.mp I.property).1⟩,(mem_idealRange.mp I.property).2⟩
  invFun I:=⟨I.val.val,mem_idealRange.mpr ⟨I.val.property,I.property⟩⟩
  left_inv _:=rfl
  right_inv _:=rfl

lemma bounded_idealRange_quadratic_norm (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀K X L : ℝ,1≤K → 1≤X → 0≤L → ∀S : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤X) →
      ∀a : Ideal O→ℂ,(∀I∈S,‖a I‖≤L) →
      (∑k : idealRange K,‖∑I∈S,canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator I)*a I‖^2)≤
        C*(K*X)^ε*(K+X)*X*L^2 := by
  obtain ⟨C,hC,hb⟩:=CanonicalQuadraticSieve.bounded_nonzero_quadratic_norm ε hε
  refine ⟨C,hC,?_⟩
  intro K X L hK hX hL S hS a ha
  have he (k : idealRange K) (z : O) :
      canonicalQuadraticRowOfIdeal k.val z=canonicalQuadraticRow (idealRangeEquiv K k).val z := by
    simp only [canonicalQuadraticRowOfIdeal,dif_pos (mem_idealRange.mp k.property).1]
    rfl
  simp_rw [he]
  exact ((idealRangeEquiv K).sum_comp _).trans_le (hb K X L hK hX hL S hS a ha)

def productColumnCoefficient (S T : Finset (Ideal O)) (β : Ideal O → Ideal O → ℂ) (I : Ideal O) : ℂ :=
  ∑p∈(S×ˢT).filter (fun p => p.1*p.2=I),β p.1 p.2

theorem product_fiber_card (P : Finset (Ideal O×Ideal O)) (I : Ideal O) (hI : I≠0) :
    (P.filter (fun p => p.1*p.2=I)).card≤(idealDivisors I).card := by
  apply Finset.card_le_card_of_injOn Prod.fst
  · intro p hp
    apply (mem_idealDivisors hI).mpr
    rw [←(Finset.mem_filter.mp hp).2]
    exact dvd_mul_right _ _
  · intro p hp q hq he
    have hp' := (Finset.mem_filter.mp hp).2
    have hq' := (Finset.mem_filter.mp hq).2
    have hz : p.1≠0 := by intro hz; simp only [hz,zero_mul] at hp'; exact hI hp'.symm
    apply Prod.ext he
    apply mul_left_cancel₀ hz
    rw [hp',he,hq']

theorem productColumnCoefficient_norm (S T : Finset (Ideal O)) (β : Ideal O → Ideal O → ℂ)
    (hβ : ∀n∈S,∀b∈T,‖β n b‖≤1) (I : Ideal O) (hI : I≠0) :
    ‖productColumnCoefficient S T β I‖≤(idealDivisors I).card := by
  unfold productColumnCoefficient
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑p∈(S×ˢT).filter (fun p => p.1*p.2=I),(1:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hh := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      exact hβ p.1 hh.1 p.2 hh.2
    _ = ((S×ˢT).filter (fun p => p.1*p.2=I)).card := by simp
    _ ≤ _ := by exact_mod_cast product_fiber_card (S×ˢT) I hI

theorem productColumnCoefficient_row_sum (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (k : Ideal O) :
    (∑n∈S,∑b∈T,canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (n*b))*β n b)=
    ∑I∈(S×ˢT).image (fun p => p.1*p.2),canonicalQuadraticRowOfIdeal k (primaryIdealGenerator I)*productColumnCoefficient S T β I := by
  rw [←Finset.sum_product (f := fun p : Ideal O×Ideal O => canonicalQuadraticRowOfIdeal k (primaryIdealGenerator (p.1*p.2))*β p.1 p.2)]
  rw [←Finset.sum_fiberwise_of_maps_to
    (fun p (hp : p∈S×ˢT) => Finset.mem_image_of_mem (fun p : Ideal O×Ideal O => p.1*p.2) hp)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [productColumnCoefficient,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]

theorem product_quadratic_norm_all :
    ∀ε : ℝ, 0<ε → ∃C : ℝ, 0<C ∧ ∀K U B : ℝ,
      1≤K → 1≤U → 1≤B → ∀S T : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
      ∀β : Ideal O → Ideal O → ℂ, (∀n∈S,∀b∈T,‖β n b‖≤1) →
      (∑k : idealRange K,‖∑n∈S,∑b∈T,canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (n*b))*β n b‖^2)≤
        C*(K*(U*B))^ε*(K+U*B)*(U*B) := by
  intro ε hε
  have hh : 0<ε/2 := by positivity
  have hq : 0<ε/4 := by positivity
  obtain ⟨C,hC,hbound⟩ := bounded_idealRange_quadratic_norm (ε/2) hh
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/4) hq
  refine ⟨C*D^2,by positivity,?_⟩
  intro K U B hK hU hB S T hS hT β hβ
  let X := U*B
  let P := (S×ˢT).image (fun p => p.1*p.2)
  have hX : 1≤X := by dsimp [X]; nlinarith
  have hX0 : 0<X := by linarith
  have hK0 : 0<K := by linarith
  have hp (I : Ideal O) (hI : I∈P) : I≠0 ∧ (Ideal.absNorm I:ℝ)≤X := by
    obtain ⟨⟨n,b⟩,hnb,rfl⟩ := Finset.mem_image.mp hI
    have hm := Finset.mem_product.mp hnb
    refine ⟨mul_ne_zero (hS n hm.1).1 (hT b hm.2).1,?_⟩
    rw [map_mul,Nat.cast_mul]
    exact mul_le_mul (hS n hm.1).2 (hT b hm.2).2 (Nat.cast_nonneg _) (by linarith)
  have hcoeff (I : Ideal O) (hI : I∈P) : ‖productColumnCoefficient S T β I‖≤D*X^(ε/4) := by
    apply (productColumnCoefficient_norm S T β hβ I (hp I hI).1).trans
    apply (hdiv I (hp I hI).1).trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hp I hI).2 hq.le) hD.le
  have hb := hbound K X (D*X^(ε/4)) hK hX (by positivity) P hp (productColumnCoefficient S T β) hcoeff
  simp_rw [productColumnCoefficient_row_sum]
  apply hb.trans
  have hpow : (K*X)^(ε/2)*(X^(ε/4))^2≤(K*X)^ε := by
    have hXP : X≤K*X := by nlinarith
    calc
      _ ≤ (K*X)^(ε/2)*((K*X)^(ε/4))^2 := by gcongr
      _ = _ := by
        rw [pow_two,←mul_assoc,←Real.rpow_add (by positivity : 0<K*X),←Real.rpow_add (by positivity : 0<K*X)]
        congr 1
        ring
  calc
    _ = (C*D^2)*((K*X)^(ε/2)*(X^(ε/4))^2)*(K+X)*X := by ring
    _ ≤ _ := by change _≤(C*D^2)*(K*X)^ε*(K+X)*X; gcongr
theorem product_quadratic_norm_scaled (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀K U B lengthScale : ℝ,1≤K → 1≤U → 1≤B → 0≤lengthScale →
    ∀S T : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
    ∀β : Ideal O→Ideal O→ℂ,(∀n∈S,∀b∈T,‖β n b‖≤lengthScale) →
      (∑k : idealRange K,‖∑n∈S,∑b∈T,
        canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (n*b))*β n b‖^2)≤
      C*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2 := by
  obtain ⟨C,hC,hbound⟩ := product_quadratic_norm_all ε hε
  refine ⟨C,hC,?_⟩
  intro K U B lengthScale hK hU hB hL S T hS hT β hβ
  by_cases hL0 : lengthScale=0
  · have hz n hn b hb : β n b=0 := norm_eq_zero.mp (le_antisymm (by simpa [hL0] using hβ n hn b hb) (norm_nonneg _))
    simp only [hL0,pow_two,mul_zero]
    apply le_of_eq
    apply Finset.sum_eq_zero
    intro k _
    have hh : (∑n∈S,∑b∈T,canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (n*b))*β n b)=0 := by
      apply Finset.sum_eq_zero
      intro n hn
      apply Finset.sum_eq_zero
      intro b hb
      rw [hz n hn b hb,mul_zero]
    rw [hh,norm_zero,zero_mul]
  have hLp : 0<lengthScale := lt_of_le_of_ne hL (Ne.symm hL0)
  have hLc : (lengthScale:ℂ)≠0 := Complex.ofReal_ne_zero.mpr hL0
  let γ : Ideal O→Ideal O→ℂ := fun n b => β n b/(lengthScale:ℂ)
  have hγ (n : Ideal O) (hn : n∈S) (b : Ideal O) (hb : b∈T) : ‖γ n b‖≤1 := by
    dsimp [γ]
    rw [norm_div,Complex.norm_real,Real.norm_of_nonneg hL]
    exact (div_le_one hLp).mpr (hβ n hn b hb)
  have hb := hbound K U B hK hU hB S T hS hT γ hγ
  have he (k : idealRange K) :
      (∑n∈S,∑b∈T,canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (n*b))*β n b)=
      (lengthScale:ℂ)*(∑n∈S,∑b∈T,canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (n*b))*γ n b) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    dsimp [γ]
    field_simp
  simp_rw [he,norm_mul,Complex.norm_real,Real.norm_of_nonneg hL,mul_pow]
  rw [←Finset.mul_sum]
  calc
    _ ≤ lengthScale^2*(C*(K*(U*B))^ε*(K+U*B)*(U*B)) := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by ring

theorem completed_quadratic_dyad (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀K U B r S₀ E : ℝ,
      1≤K → 1≤U → 1≤B → 0<r → 0<S₀ → 0<E →
    ∀S T : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
    ∀β : Ideal O→Ideal O→ℂ,
      (∀n∈S,∀b∈T,‖β n b‖≤1/(Real.sqrt U*B*r*Real.sqrt (S₀*E))) →
      (∑k : idealRange K,‖∑n∈S,∑b∈T,
        canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (n*b))*β n b‖^2)≤
      C*(K*(U*B))^ε*(K+U*B)/(B*r^2*S₀*E) := by
  obtain ⟨C,hC,hbound⟩ := product_quadratic_norm_scaled ε hε
  refine ⟨C,hC,?_⟩
  intro K U B r S₀ E hK hU hB hr hS₀ hE S T hS hT β hβ
  apply (hbound K U B _ hK hU hB (by positivity) S T hS hT β hβ).trans
  apply le_of_eq
  have hU0 : U≠0 := by linarith
  have hB0 : B≠0 := by linarith
  have hr0 := ne_of_gt hr
  have hS0 := ne_of_gt hS₀
  have hE0 := ne_of_gt hE
  simp only [one_div,inv_pow,mul_pow,Real.sq_sqrt (show 0≤U by linarith),
    Real.sq_sqrt (show 0≤S₀*E by positivity)]
  field_simp

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

theorem finite_integral_energy_bound {κ : Type*} [Fintype κ]
    (b : ℝ→ℂ) (φ : κ→ℝ→ℂ) (E : ℝ) (hE : 0≤E)
    (hb : Integrable (fun t => ‖b t‖))
    (hφ : ∀k,Integrable (fun t => b t*φ k t))
    (hbound : ∀t,(∑k,‖φ k t‖^2)≤E) :
    (∑k,‖∫t : ℝ,b t*φ k t‖^2)≤E*(∫t : ℝ,‖b t‖)^2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : ℝ→EuclideanSpace ℂ κ := fun t => e.symm (fun k => b t*φ k t)
  have hF (t : ℝ) : ‖F t‖≤‖b t‖*Real.sqrt E := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE]
    change (∑k,‖b t*φ k t‖^2)≤‖b t‖^2*E
    simp only [norm_mul,mul_pow,←Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hbound t) (sq_nonneg _)
  have he : (∫t : ℝ,F t)=e.symm (fun k => ∫t : ℝ,b t*φ k t) := by
    rw [show F=(fun t => e.symm (fun k => b t*φ k t)) from rfl,e.symm.integral_comp_comm]
    congr 1
    funext k
    exact eval_integral hφ k
  have hn : ‖e.symm (fun k => ∫t : ℝ,b t*φ k t)‖≤(∫t : ℝ,‖b t‖)*Real.sqrt E := by
    rw [←he,←integral_mul_const]
    exact norm_integral_le_of_norm_le (hb.mul_const _) (Filter.Eventually.of_forall hF)
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE] at hs
  simpa [e,mul_comm] using hs

open Eisenstein

theorem integrated_product_quadratic (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀K U B lengthScale : ℝ,1≤K → 1≤U → 1≤B → 0≤lengthScale →
    ∀S T : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
    ∀β : ℝ→Ideal O→Ideal O→ℂ,
      (∀n b,Continuous (fun t => β t n b)) →
      (∀t,∀n∈S,∀b∈T,‖β t n b‖≤lengthScale) →
    ∀rowPhase : idealRange K→ℝ→ℂ,(∀k,Continuous (rowPhase k)) → (∀k t,‖rowPhase k t‖≤1) →
    ∀b : 𝓢(ℝ,ℂ),
      (∑k : idealRange K,‖∫t : ℝ,b t*(rowPhase k t*
        ∑n∈S,∑v∈T,canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (n*v))*β t n v)‖^2)≤
      C*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2*(∫t : ℝ,‖b t‖)^2 := by
  obtain ⟨C,hC,hbound⟩ := product_quadratic_norm_scaled ε hε
  refine ⟨C,hC,?_⟩
  intro K U B lengthScale hK hU hB hL S T hS hT β hβc hβ rowPhase hωc hω b
  let E := C*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2
  have hE : 0≤E := by dsimp [E]; positivity
  let φ : idealRange K→ℝ→ℂ := fun k t => rowPhase k t*
    ∑n∈S,∑v∈T,canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (n*v))*β t n v
  have hφc (k : idealRange K) : Continuous (φ k) := by
    apply (hωc k).mul
    apply continuous_finsetSum
    intro n hn
    apply continuous_finsetSum
    intro v hv
    exact continuous_const.mul (hβc n v)
  have hφbound (t : ℝ) : (∑k,‖φ k t‖^2)≤E := by
    apply le_trans _ (hbound K U B lengthScale hK hU hB hL S T hS hT (β t) (hβ t))
    apply Finset.sum_le_sum
    intro k hk
    exact pow_le_pow_left₀ (norm_nonneg _) (by
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hω k t)) 2
  have hpoint (k : idealRange K) (t : ℝ) : ‖φ k t‖≤Real.sqrt E := by
    apply (Real.le_sqrt (norm_nonneg _) hE).mpr
    exact (Finset.single_le_sum (fun j _ => sq_nonneg ‖φ j t‖) (Finset.mem_univ k)).trans (hφbound t)
  have hφint (k : idealRange K) : Integrable (fun t : ℝ => b t*φ k t) :=
    b.integrable.mul_bdd (hφc k).aestronglyMeasurable (Filter.Eventually.of_forall (hpoint k))
  exact finite_integral_energy_bound b φ E hE b.integrable.norm hφint hφbound

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

theorem completed_kernel_three_window
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W) (A : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀R : ℝ,0<R → ∃B : 𝓢(ℝ,ℂ),
      (∀r u v : ℝ,V₀ r*V₁ u*V₂ v*paperKernel (Vstar W)
        (R*Real.exp (-2*r+u+3*v))=
        ∫t : ℝ,(V₀ r*kernelLogPhase t (-2*r))*
          (V₁ u*kernelLogPhase t u)*(V₂ v*kernelLogPhase t (3*v))*B t) ∧
      (1+R)^A*(∫t : ℝ,‖B t‖)≤C := by
  let V : Fin 3→ℝ→ℂ := ![V₀,V₁,V₂]
  let slope : Fin 3→ℝ := ![-2,1,3]
  let M : Fin 3→ℝ := ![M₀,M₁,M₂]
  have hm : ∀i,0≤M i := by intro i; fin_cases i <;> assumption
  have hv : ∀i y,V i y≠0 → |y|≤M i := by intro i; fin_cases i <;> assumption
  obtain ⟨C,hC,h⟩ := completed_kernel_log_separation V slope M hm hv W a b ha hsupp hW A 0
  refine ⟨C,hC,?_⟩
  intro R hR
  obtain ⟨B,hB,hi,hbound,hpoint⟩ := h R hR
  refine ⟨B,?_,by simpa only [pow_zero,one_mul] using hbound⟩
  intro r u v
  simpa [V,slope,Fin.prod_univ_succ,Fin.sum_univ_succ,mul_assoc,add_assoc] using hB ![r,u,v]

theorem completed_smooth_quadratic
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (hV₀n : ∀y,‖V₀ y‖≤1) (hV₁n : ∀y,‖V₁ y‖≤1) (hV₂n : ∀y,‖V₂ y‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (A : ℕ) (ε : ℝ) (hε : 0<ε) :
    ∃C : ℝ,0<C ∧ ∀K U B lengthScale R : ℝ,1≤K → 1≤U → 1≤B → 0≤lengthScale → 0<R →
    ∀S T : Finset (Ideal O),
      (∀I∈S,I≠0 ∧ (Ideal.absNorm I:ℝ)≤U) →
      (∀I∈T,I≠0 ∧ (Ideal.absNorm I:ℝ)≤B) →
    ∀β : Ideal O→Ideal O→ℂ,(∀n∈S,∀v∈T,‖β n v‖≤lengthScale) →
    ∀yr : idealRange K→ℝ,∀yn yb : Ideal O→ℝ,
    (∑k : idealRange K,‖∑n∈S,∑v∈T,
      canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (n*v))*β n v*
      (V₀ (yr k)*V₁ (yn n)*V₂ (yb v)*paperKernel (Vstar W)
        (R*Real.exp (-2*yr k+yn n+3*yb v)))‖^2)≤
      C*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2/(1+R)^(2*A) := by
  obtain ⟨Cq,hCq,hq⟩ := integrated_product_quadratic ε hε
  obtain ⟨Ck,hCk,hkernel⟩ := completed_kernel_three_window V₀ V₁ V₂ M₀ M₁ M₂
    hM₀ hM₁ hM₂ hV₀ hV₁ hV₂ W a b ha hsupp hW A
  refine ⟨Cq*(Ck^2+1),by positivity,?_⟩
  intro K U B lengthScale R hK hU hB hL hR S T hS hT β hβ yr yn yb
  obtain ⟨g,hsep,hg⟩ := hkernel R hR
  let rowPhase : idealRange K→ℝ→ℂ := fun k t => V₀ (yr k)*kernelLogPhase t (-2*yr k)
  let βt : ℝ→Ideal O→Ideal O→ℂ := fun t n v =>
    β n v*(V₁ (yn n)*kernelLogPhase t (yn n))*(V₂ (yb v)*kernelLogPhase t (3*yb v))
  have hphase (t x : ℝ) : ‖kernelLogPhase t x‖=1 := kernelLogPhase_norm t x
  have hrowPhase (k : idealRange K) (t : ℝ) : ‖rowPhase k t‖≤1 := by
    simp only [rowPhase,norm_mul,hphase,mul_one]
    exact hV₀n _
  have hβt (t : ℝ) (n : Ideal O) (hn : n∈S) (v : Ideal O) (hv : v∈T) : ‖βt t n v‖≤lengthScale := by
    simp only [βt,norm_mul,hphase,mul_one]
    exact (mul_le_of_le_one_right (by positivity)
      (hV₂n _)).trans ((mul_le_of_le_one_right (norm_nonneg _) (hV₁n _)).trans (hβ n hn v hv))
  have hrowPhasec (k : idealRange K) : Continuous (rowPhase k) :=
    continuous_const.mul (kernelLogPhase_continuous_left _)
  have hβtc (n v : Ideal O) : Continuous (fun t => βt t n v) :=
    (continuous_const.mul (continuous_const.mul (kernelLogPhase_continuous_left _))).mul
      (continuous_const.mul (kernelLogPhase_continuous_left _))
  have hi := hq K U B lengthScale hK hU hB hL S T hS hT βt hβtc hβt rowPhase hrowPhasec hrowPhase g
  have he (k : idealRange K) :
      (∑n∈S,∑v∈T,canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (n*v))*β n v*
        (V₀ (yr k)*V₁ (yn n)*V₂ (yb v)*paperKernel (Vstar W)
          (R*Real.exp (-2*yr k+yn n+3*yb v)))) =
      ∫t : ℝ,g t*(rowPhase k t*∑n∈S,∑v∈T,canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (n*v))*βt t n v) := by
    have hint (n v : Ideal O) : Integrable (fun t : ℝ =>
        g t*(rowPhase k t*(canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (n*v))*βt t n v))) := by
      apply g.integrable.mul_bdd (c := ‖canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (n*v))*β n v‖)
      · exact ((hrowPhasec k).mul (continuous_const.mul (hβtc n v))).aestronglyMeasurable
      · filter_upwards [] with t
        simp only [rowPhase,βt,norm_mul,hphase,mul_one]
        have hv01 : ‖V₀ (yr k)‖*‖V₁ (yn n)‖≤1 := by
          simpa only [one_mul] using mul_le_mul (hV₀n (yr k)) (hV₁n (yn n)) (norm_nonneg _) zero_le_one
        have hv012 : (‖V₀ (yr k)‖*‖V₁ (yn n)‖)*‖V₂ (yb v)‖≤1 := by
          simpa only [one_mul] using mul_le_mul hv01 (hV₂n (yb v)) (norm_nonneg _) zero_le_one
        calc
          _ = (‖canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (n*v))‖*‖β n v‖)*
            ((‖V₀ (yr k)‖*‖V₁ (yn n)‖)*‖V₂ (yb v)‖) := by ring
          _ ≤ (‖canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (n*v))‖*‖β n v‖)*1 :=
            mul_le_mul_of_nonneg_left hv012 (by positivity)
          _ = _ := by ring
    simp only [Finset.mul_sum]
    rw [integral_finsetSum _ (fun n hn => integrable_finsetSum _ (fun v hv => hint n v))]
    apply Finset.sum_congr rfl
    intro n hn
    rw [integral_finsetSum _ (fun v hv => hint n v)]
    apply Finset.sum_congr rfl
    intro v hv
    rw [hsep (yr k) (yn n) (yb v),←integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp [rowPhase,βt]
    ring
  simp_rw [he]
  apply hi.trans
  have hpow : 0<(1+R)^A := by positivity
  have hmass : (∫t : ℝ,‖g t‖)≤Ck/(1+R)^A := (le_div_iff₀ hpow).mpr (by simpa only [mul_comm] using hg)
  have hmass2 := pow_le_pow_left₀ (integral_nonneg (fun t => norm_nonneg _)) hmass 2
  have hbase : 0≤Cq*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2 := by positivity
  calc
    _ ≤ (Cq*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2)*(Ck/(1+R)^A)^2 :=
      mul_le_mul_of_nonneg_left hmass2 hbase
    _ ≤ (Cq*(K*(U*B))^ε*(K+U*B)*(U*B)*lengthScale^2)*((Ck^2+1)/(1+R)^(2*A)) := by
      apply mul_le_mul_of_nonneg_left _ hbase
      rw [div_pow,←pow_mul]
      have hp : A*2=2*A := Nat.mul_comm _ _
      rw [hp]
      exact div_le_div_of_nonneg_right (by nlinarith : Ck^2≤Ck^2+1) (by positivity)
    _ = _ := by ring

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

open CompletedDyadic

def completedSmoothDyadicBlock (V₀ V₁ V₂ W : ℝ→ℂ) (K Y ρ q : ℝ)
    (S T : (ℕ×ℕ×ℕ)→Finset (Ideal O))
    (β : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ) (i : ℕ×ℕ×ℕ) (k : idealRange K) : ℂ :=
  ∑n∈S i,∑v∈T i,canonicalQuadraticRowOfIdeal k.val (primaryIdealGenerator (n*v))*β i n v*
    (V₀ (Real.log ((Ideal.absNorm k.val:ℝ)/K))*
      V₁ (Real.log ((Ideal.absNorm n:ℝ)/(2:ℝ)^i.2.2))*
      V₂ (Real.log ((Ideal.absNorm v:ℝ)/(2:ℝ)^i.2.1))*
      paperKernel (Vstar W)
        ((Y⁻¹*(ramifiedScale ρ q i.1)^3*((2:ℝ)^i.2.1)^3*(2:ℝ)^i.2.2)*
          Real.exp (-2*Real.log ((Ideal.absNorm k.val:ℝ)/K)+
            Real.log ((Ideal.absNorm n:ℝ)/(2:ℝ)^i.2.2)+
              3*Real.log ((Ideal.absNorm v:ℝ)/(2:ℝ)^i.2.1))))

theorem completed_smooth_series_rowPhase
    (V₀ V₁ V₂ : ℝ→ℂ) (M₀ M₁ M₂ : ℝ)
    (hM₀ : 0≤M₀) (hM₁ : 0≤M₁) (hM₂ : 0≤M₂)
    (hV₀ : ∀y,V₀ y≠0 → |y|≤M₀) (hV₁ : ∀y,V₁ y≠0 → |y|≤M₁)
    (hV₂ : ∀y,V₂ y≠0 → |y|≤M₂)
    (hV₀n : ∀y,‖V₀ y‖≤1) (hV₁n : ∀y,‖V₁ y‖≤1) (hV₂n : ∀y,‖V₂ y‖≤1)
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ρ q : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) :
    ∃C : ℝ,0<C ∧ ∀K Y H : ℝ,1≤K → 0<Y → 0<H →
    ∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal O),
      (∀i,∀I∈S i,I≠0 ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀I∈T i,I≠0 ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.1) →
    ∀β : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖β i n v‖≤
        1/(Real.sqrt ((2:ℝ)^i.2.2)*(2:ℝ)^i.2.1*ramifiedScale ρ q i.1*Real.sqrt H)) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange K→ℂ,(∀i k,‖σ i k‖≤1) →
      (∀k,Summable (fun i => ‖σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k‖)) ∧
      (∑k : idealRange K,‖∑'i : ℕ×ℕ×ℕ,
        σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k‖^2)
        ≤C*(K*Y)^(2*deltaLoss)*(K+Y)/H := by
  obtain ⟨A,hA⟩ := exists_nat_gt (deltaLoss+1/2)
  obtain ⟨Cq,hCq,hquad⟩ := completed_smooth_quadratic V₀ V₁ V₂ M₀ M₁ M₂
    hM₀ hM₁ hM₂ hV₀ hV₁ hV₂ hV₀n hV₁n hV₂n W a b ha hsupp hW A (2*deltaLoss) (by positivity)
  obtain ⟨Cs,hCs,hsum⟩ := normMajorant_sum_bound deltaLoss A ρ q hδ hA hρ hq
  refine ⟨2*Cq*Cs^2,by positivity,?_⟩
  intro K Y H hK hY hH S T hS hT β hβ σ hσ
  have hKp : 0<K := by linarith
  have hqp : 0<q := by linarith
  let g : (ℕ×ℕ×ℕ)→ℝ := fun i => Real.sqrt Cq *
    normMajorant deltaLoss A K Y⁻¹ (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)
  have hg0 (i : ℕ×ℕ×ℕ) : 0≤g i := by
    dsimp [g]
    exact mul_nonneg (Real.sqrt_nonneg _) (normMajorant_nonneg _ _ _ _ _ _ _ _
      hKp (by positivity) (ramifiedScale_pos ρ q hρ hqp _) hH (by positivity) (by positivity))
  have henergy (i : ℕ×ℕ×ℕ) :
      (∑k : idealRange K,‖σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k‖^2)
        ≤(g i)^2 := by
    let U : ℝ := (2:ℝ)^i.2.2
    let B : ℝ := (2:ℝ)^i.2.1
    let r : ℝ := ramifiedScale ρ q i.1
    let R : ℝ := Y⁻¹*r^3*B^3*U
    have hU : 1≤U := one_le_pow₀ (by norm_num)
    have hB : 1≤B := one_le_pow₀ (by norm_num)
    have hUp : 0<U := by positivity
    have hBp : 0<B := by positivity
    have hr : 0<r := ramifiedScale_pos ρ q hρ hqp _
    have hR : 0<R := by dsimp [R]; positivity
    have h := hquad K U B (1/(Real.sqrt U*B*r*Real.sqrt H)) R
      hK hU hB (by positivity) hR (S i) (T i) (hS i) (hT i) (β i) (hβ i)
      (fun k => Real.log ((Ideal.absNorm k.val:ℝ)/K))
      (fun n => Real.log ((Ideal.absNorm n:ℝ)/U))
      (fun v => Real.log ((Ideal.absNorm v:ℝ)/B))
    change (∑k,‖completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k‖^2)≤_ at h
    have hphase : (∑k : idealRange K,‖σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k‖^2)≤
        ∑k : idealRange K,‖completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k‖^2 := by
      apply Finset.sum_le_sum
      intro k _
      apply pow_le_pow_left₀ (norm_nonneg _)
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (hσ i k)
    apply (hphase.trans h).trans
    have he : Cq*(K*(U*B))^(2*deltaLoss)*(K+U*B)*(U*B)*
        (1/(Real.sqrt U*B*r*Real.sqrt H))^2/(1+R)^(2*A)=
        Cq*((K*(U*B))^(2*deltaLoss)*(K+U*B)/(B*r^2*H)/(1+R)^(2*(A:ℝ))) := by
      rw [show 2*(A:ℝ)=((2*A:ℕ):ℝ) by norm_num,Real.rpow_natCast]
      simp only [one_div,inv_pow,mul_pow,Real.sq_sqrt hUp.le,Real.sq_sqrt hH.le]
      field_simp

    rw [he]
    have hm := smooth_energy_le_normMajorant_sq deltaLoss A K Y⁻¹ r H U B
      hKp (by positivity) hr hH hUp hBp
    calc
      _ ≤ Cq*(normMajorant deltaLoss A K Y⁻¹ r H U B)^2 := mul_le_mul_of_nonneg_left hm hCq.le
      _ = (g i)^2 := by dsimp [g,U,B,r]; rw [mul_pow,Real.sq_sqrt hCq.le]
  obtain ⟨hs,hb⟩ := hsum K Y H hKp hY hH
  have hm := finite_tsum_energy_bound
    (fun i k => σ i k*completedSmoothDyadicBlock V₀ V₁ V₂ W K Y ρ q S T β i k) g hg0
    (hs.mul_left (Real.sqrt Cq)) henergy
  refine ⟨hm.1,hm.2.trans ?_⟩
  have hb' : (∑'i,g i)≤Real.sqrt Cq*(Cs*(K*Y)^deltaLoss*(Real.sqrt K+Real.sqrt Y)/Real.sqrt H) := by
    rw [show g=(fun i => Real.sqrt Cq*normMajorant deltaLoss A K Y⁻¹
      (ramifiedScale ρ q i.1) H ((2:ℝ)^i.2.2) ((2:ℝ)^i.2.1)) from rfl,tsum_mul_left]
    exact mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _)
  have hsq := pow_le_pow_left₀ (tsum_nonneg hg0) hb' 2
  apply hsq.trans
  have hroot : (Real.sqrt K+Real.sqrt Y)^2≤2*(K+Y) := by
    nlinarith [Real.sq_sqrt hKp.le,Real.sq_sqrt hY.le,
      sq_nonneg (Real.sqrt K-Real.sqrt Y)]
  simp only [mul_pow,div_pow,Real.sq_sqrt hCq.le,Real.sq_sqrt hH.le]
  have hp : ((K*Y)^deltaLoss)^2=(K*Y)^(2*deltaLoss) := by
    rw [←Real.rpow_mul_natCast (mul_pos hKp hY).le]
    congr 1
    ring
  rw [hp]
  calc
    _ ≤ Cq*(Cs^2*(K*Y)^(2*deltaLoss)*(2*(K+Y))/H) := by
      apply mul_le_mul_of_nonneg_left _ hCq.le
      exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hroot (by positivity)) hH.le
    _ = _ := by ring

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

open CompletedDyadic

def reflectedBranchBlock {ι : Type*} [Fintype ι]
    (P : ι→Ideal O) [∀i,(P i).IsMaximal] (hg : ∀i,lambda∉P i)
    (j : ι→ℕ) (e : ι→Fin 3) (W : ℝ→ℂ) (K Y ρ q : ℝ)
    (S T : (ℕ×ℕ×ℕ)→Finset (Ideal O))
    (η : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ)
    (σ : (ℕ×ℕ×ℕ)→idealRange K→ℂ) (i : ℕ×ℕ×ℕ) (k : idealRange K) : ℂ :=
  σ i k*completedSmoothDyadicBlock completedShellWindow completedShellWindow completedShellWindow
    W K Y ρ q S T (fun v => reflectedDyadicCoefficient P hg j e (η v) (ramifiedScale ρ q v.1)) i k

theorem completed_reflected_branch_series
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ρ q : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) :
    ∃C : ℝ,0<C ∧ ∀K Y : ℝ,1≤K → 0<Y →
    ∀{ι : Type*} [Fintype ι] (P : ι→Ideal O) [∀i,(P i).IsMaximal]
      (hg : ∀i,lambda∉P i) (j : ι→ℕ) (e : ι→Fin 3),
    ∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal O),
      (∀i,∀I∈S i,I≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀I∈T i,I≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm I:ℝ) ∧ (Ideal.absNorm I:ℝ)≤(2:ℝ)^i.2.1) →
    ∀η : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖η i n v‖≤1) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange K→ℂ,(∀i k,‖σ i k‖≤1) →
      (∀k,Summable (fun i => ‖reflectedBranchBlock P hg j e W K Y ρ q S T η σ i k‖)) ∧
      (∑k : idealRange K,‖∑'i : ℕ×ℕ×ℕ,reflectedBranchBlock P hg j e W K Y ρ q S T η σ i k‖^2)
        ≤C*(K*Y)^(2*deltaLoss)*(K+Y)/
          ((Ideal.absNorm (reflectionExtractedDivisor P j e 0):ℝ)*
            (Ideal.absNorm (reflectionExtractedDivisor P j e 2):ℝ)) := by
  have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
  obtain ⟨C,hC,h⟩ := completed_smooth_series_rowPhase
    completedShellWindow completedShellWindow completedShellWindow (Real.log 2) (Real.log 2) (Real.log 2)
    hl hl hl completedShellWindow_support completedShellWindow_support completedShellWindow_support
    completedShellWindow_norm completedShellWindow_norm completedShellWindow_norm
    W a b ha hsupp hW deltaLoss ρ q hδ hρ hq
  refine ⟨C,hC,?_⟩
  intro K Y hK hY ι _ P _ hg j e S T hS hT η hη σ hσ
  have hn (v : Fin 3) : 0<(Ideal.absNorm (reflectionExtractedDivisor P j e v):ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz =>
      reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i)) j e v
        (Ideal.absNorm_eq_zero_iff.mp hz))
  exact h K Y _ hK hY (mul_pos (hn 0) (hn 2)) S T
    (fun i I hI => ⟨(hS i I hI).1,(hS i I hI).2.2⟩)
    (fun i I hI => ⟨(hT i I hI).1,(hT i I hI).2.2⟩)
    (fun v => reflectedDyadicCoefficient P hg j e (η v) (ramifiedScale ρ q v.1))
    (fun i n hn v hv => reflectedDyadicCoefficient_norm P hg j e (η i)
      (ramifiedScale ρ q i.1) _ _ (ramifiedScale_pos ρ q hρ (by linarith) _) (by positivity) (by positivity)
      n v (hS i n hn).1 (hT i v hv).1 (hη i n hn v hv) (hS i n hn).2.1 (hT i v hv).2.1)
    σ hσ

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

def completedResidualScale (K : ℝ) (I Q : Ideal O) : ℝ :=
  K/((Ideal.absNorm (rowPowerfulPart I):ℝ)*(Ideal.absNorm (rowMaskPart I Q):ℝ))

def completedBranchScale {ι : Type*} [Fintype ι]
    (K X : ℝ) (I F Q : Ideal O) (P : ι→Ideal O) (e : ι→Fin 3) : ℝ :=
  (completedResidualScale K I Q)^2*(Ideal.absNorm (∏i,P i):ℝ)^2/
    (X*(Ideal.absNorm (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 1):ℝ)*
      (Ideal.absNorm (reflectionExtractedDivisor P (fun i => completedLocalExponent I F (P i)) e 2):ℝ)^3)

theorem completed_reflected_fiber
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ρ q : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) :
    ∃C : ℝ,0<C ∧ ∀K X : ℝ,1≤K → 1≤X →
    ∀I F Q : Ideal O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤completedResidualScale K I Q →
    ∀{ι : Type*} [Fintype ι] (P : ι→Ideal O) [∀i,(P i).IsMaximal]
      (hg : ∀i,lambda∉P i),
      Pairwise (fun i j => IsCoprime (P i) (P j)) →
      (∀i,P i∣I*Q) → (∀i,¬P i∣rowResidualPart I Q) →
    ∀e : ι→Fin 3,∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal O),
      (∀i,∀J∈S i,J≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀J∈T i,J≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.1) →
    ∀η : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖η i n v‖≤1) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange (completedResidualScale K I Q)→ℂ,(∀i k,‖σ i k‖≤1) →
      (∑k : idealRange (completedResidualScale K I Q),‖∑'i : ℕ×ℕ×ℕ,
        reflectedBranchBlock P hg (fun i => completedLocalExponent I F (P i)) e W
          (completedResidualScale K I Q) (completedBranchScale K X I F Q P e) ρ q S T η σ i k‖^2)
        ≤C*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨C,hC,h⟩ := completed_reflected_branch_series W a b ha hsupp hW deltaLoss ρ q hδ hρ hq
  refine ⟨C,hC,?_⟩
  intro K X hK hX I F Q hI hQ hIK hscale ι _ P _ hg hcop hpool hres e S T hS hT η hη σ hσ
  have hn (J : Ideal O) (hJ : J≠0) : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hj (v : Fin 3) := hn _
    (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i))
      (fun i => completedLocalExponent I F (P i)) e v)
  have hp := hn (∏i,P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i)))
  have hy : 0<completedBranchScale K X I F Q P e := by
    unfold completedBranchScale
    have hk : 0<completedResidualScale K I Q := by linarith
    have hx : 0<X := by linarith
    have hd := hj 1
    have he := hj 2
    positivity
  have hb := (h (completedResidualScale K I Q) (completedBranchScale K X I F Q P e)
    hscale hy P hg (fun i => completedLocalExponent I F (P i)) e S T hS hT η hη σ hσ).2
  have hc := completed_actual_fiber_cost deltaLoss K X hδ.le hK hX I F Q hI hQ hIK P hcop hpool hres e
  have hm := mul_le_mul_of_nonneg_left hc hC.le
  apply hb.trans
  convert hm using 1 <;> (try dsimp [completedResidualScale,completedBranchScale]) <;> ring

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

theorem completed_scaled_shape (ε k y H c B : ℝ) (hε : 0≤ε) (hk : 0<k)
    (hy : 0<y) (hH : 0<H) (hc : 0<c) (hcB : c≤B) (hB : 1≤B) :
    (k*(c*y))^ε*(k+c*y)/H≤B^(ε+1)*((k*y)^ε*(k+y)/H) := by
  have hB0 : 0<B := by linarith
  have hp : (k*(c*y))^ε≤B^ε*(k*y)^ε := by
    rw [show k*(c*y)=c*(k*y) by ring,Real.mul_rpow hc.le (mul_pos hk hy).le]
    exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hc.le hcB hε) (by positivity)
  have hs : k+c*y≤B*(k+y) := by nlinarith
  calc
    _ ≤ (B^ε*(k*y)^ε)*(B*(k+y))/H :=
      div_le_div_of_nonneg_right (mul_le_mul hp hs (by positivity) (by positivity)) hH.le
    _ = (B^ε*B)*((k*y)^ε*(k+y)/H) := by ring
    _ = _ := by rw [←Real.rpow_add_one hB0.ne']

theorem completedBranchScale_div {ι : Type*} [Fintype ι]
    (K X c : ℝ) (I F Q : Ideal O) (P : ι→Ideal O) (e : ι→Fin 3) :
    completedBranchScale K (X/c) I F Q P e=c*completedBranchScale K X I F Q P e := by
  unfold completedBranchScale
  simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
  ring

theorem completed_reflected_fiber_fixed_scale
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ρ q B : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) (hB : 1≤B) :
    ∃C : ℝ,0<C ∧ ∀K X c : ℝ,1≤K → 1≤X → 0<c → c≤B →
    ∀I F Q : Ideal O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤completedResidualScale K I Q →
    ∀{ι : Type*} [Fintype ι] (P : ι→Ideal O) [∀i,(P i).IsMaximal]
      (hg : ∀i,lambda∉P i),
      Pairwise (fun i j => IsCoprime (P i) (P j)) →
      (∀i,P i∣I*Q) → (∀i,¬P i∣rowResidualPart I Q) →
    ∀e : ι→Fin 3,∀S T : (ℕ×ℕ×ℕ)→Finset (Ideal O),
      (∀i,∀J∈S i,J≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.2) →
      (∀i,∀J∈T i,J≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.1) →
    ∀η : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ,
      (∀i,∀n∈S i,∀v∈T i,‖η i n v‖≤1) →
    ∀σ : (ℕ×ℕ×ℕ)→idealRange (completedResidualScale K I Q)→ℂ,(∀i k,‖σ i k‖≤1) →
      (∑k : idealRange (completedResidualScale K I Q),‖∑'i : ℕ×ℕ×ℕ,
        reflectedBranchBlock P hg (fun i => completedLocalExponent I F (P i)) e W
          (completedResidualScale K I Q) (completedBranchScale K (X/c) I F Q P e) ρ q S T η σ i k‖^2)
        ≤C*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨C,hC,h⟩ := completed_reflected_branch_series W a b ha hsupp hW deltaLoss ρ q hδ hρ hq
  refine ⟨C*B^(2*deltaLoss+1),by positivity,?_⟩
  intro K X c hK hX hc hcB I F Q hI hQ hIK hk ι _ P _ hg hcop hpool hres e S T hS hT η hη σ hσ
  have hn (J : Ideal O) (hJ : J≠0) : 0<(Ideal.absNorm J:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hJ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hj (v : Fin 3) := hn _ (reflectionExtractedDivisor_ne_zero P (fun i => NeZero.ne (P i))
    (fun i => completedLocalExponent I F (P i)) e v)
  have hp := hn (∏i,P i) (Finset.prod_ne_zero_iff.mpr (fun i _ => NeZero.ne (P i)))
  have hk0 : 0<completedResidualScale K I Q := by linarith
  have hy : 0<completedBranchScale K X I F Q P e := by
    unfold completedBranchScale
    have hX0 : 0<X := by linarith
    have hd := hj 1
    have he := hj 2
    positivity
  rw [completedBranchScale_div]
  have hb := (h (completedResidualScale K I Q) (c*completedBranchScale K X I F Q P e)
    hk (mul_pos hc hy) P hg (fun i => completedLocalExponent I F (P i)) e S T hS hT η hη σ hσ).2
  have hs := completed_scaled_shape (2*deltaLoss) (completedResidualScale K I Q)
    (completedBranchScale K X I F Q P e) _ c B (by positivity) hk0 hy
    (mul_pos (hj 0) (hj 2)) hc hcB hB
  have hcst := completed_actual_fiber_cost deltaLoss K X hδ.le hK hX I F Q hI hQ hIK P hcop hpool hres e
  have hh := hs.trans (mul_le_mul_of_nonneg_left hcst (by positivity : 0≤B^(2*deltaLoss+1)))
  apply hb.trans
  have hfinal := mul_le_mul_of_nonneg_left hh hC.le
  convert hfinal using 1 <;> (try dsimp [completedResidualScale,completedBranchScale]) <;> ring

end CompletedGauss

namespace CompletedGauss
open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion MeasureTheory UniqueFactorizationMonoid
open scoped BigOperators Classical SchwartzMap ContDiff

/-- A reflected branch with dyadic column sets and normalized coefficients. -/
structure ReflectedBranchData (levelBound K : ℝ) (I F Q : Ideal O) where
  levelScale : ℝ
  levelScale_pos : 0<levelScale
  levelScale_le : levelScale≤levelBound
  primes : Finset (Ideal O)
  maximal : ∀p : primes,p.val.IsMaximal
  good : ∀p : primes,lambda∉p.val
  coprime : Pairwise (fun p r : primes => IsCoprime p.val r.val)
  divides : ∀p : primes,p.val∣I*Q
  nonresidual : ∀p : primes,¬p.val∣rowResidualPart I Q
  label : primes→Fin 3
  nColumns : (ℕ×ℕ×ℕ)→Finset (Ideal O)
  bColumns : (ℕ×ℕ×ℕ)→Finset (Ideal O)
  nBounds : ∀i,∀J∈nColumns i,J≠0 ∧ (2:ℝ)^i.2.2/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.2
  bBounds : ∀i,∀J∈bColumns i,J≠0 ∧ (2:ℝ)^i.2.1/2≤(Ideal.absNorm J:ℝ) ∧ (Ideal.absNorm J:ℝ)≤(2:ℝ)^i.2.1
  amplitude : (ℕ×ℕ×ℕ)→Ideal O→Ideal O→ℂ
  amplitude_bound : ∀i,∀n∈nColumns i,∀b∈bColumns i,‖amplitude i n b‖≤1
  rowPhase : (ℕ×ℕ×ℕ)→idealRange (completedResidualScale K I Q)→ℂ
  rowPhase_bound : ∀i k,‖rowPhase i k‖≤1

namespace ReflectedBranchData

def value {levelBound K : ℝ} {I F Q : Ideal O} (d : ReflectedBranchData levelBound K I F Q)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) : ℂ := by
  letI : ∀p : d.primes,p.val.IsMaximal := d.maximal
  exact ∑'i : ℕ×ℕ×ℕ,reflectedBranchBlock (fun p : d.primes => p.val) d.good
    (fun p => completedLocalExponent I F p.val) d.label W
    (completedResidualScale K I Q) (completedBranchScale K (X/d.levelScale) I F Q (fun p : d.primes => p.val) d.label)
    ρ q d.nColumns d.bColumns d.amplitude d.rowPhase i k

theorem energy_bound
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃C : ℝ,0<C ∧ ∀K X : ℝ,1≤K → 1≤X →
    ∀I F Q : Ideal O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤completedResidualScale K I Q → ∀d : ReflectedBranchData levelBound K I F Q,
      (∑k,‖d.value W X ρ q k‖^2)≤
        C*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨C,hC,h⟩ := completed_reflected_fiber_fixed_scale W a b ha hsupp hW deltaLoss ρ q levelBound hδ hρ hq hlevel
  refine ⟨C,hC,?_⟩
  intro K X hK hX I F Q hI hQ hIK hk d
  let : ∀p : d.primes,p.val.IsMaximal := d.maximal
  exact h K X d.levelScale hK hX d.levelScale_pos d.levelScale_le I F Q hI hQ hIK hk _ d.good d.coprime d.divides d.nonresidual
    d.label d.nColumns d.bColumns d.nBounds d.bBounds d.amplitude d.amplitude_bound
    d.rowPhase d.rowPhase_bound

end ReflectedBranchData

/-- Finite local branches over a common residual squarefree conductor. -/
structure ReflectedFiberData (rays : ℕ) (levelBound K : ℝ) (I F Q : Ideal O) where
  pool : Finset (Ideal O)
  maximal : ∀p : pool,p.val.IsMaximal
  divides : ∀p : pool,p.val∣I*Q
  branch : (Fin rays×(pool→Fin 6))→ReflectedBranchData levelBound K I F Q
  weight : (Fin rays×(pool→Fin 6))→ℂ
  weight_bound : ∀b,‖weight b‖≤1

namespace ReflectedFiberData

def value {rays : ℕ} {levelBound K : ℝ} {I F Q : Ideal O} (d : ReflectedFiberData rays levelBound K I F Q)
    (W : ℝ→ℂ) (X ρ q : ℝ) (k : idealRange (completedResidualScale K I Q)) : ℂ :=
  ∑b,d.weight b*(d.branch b).value W X ρ q k

theorem finite_energy_bound {κ τ : Type*} [Fintype κ] [Fintype τ]
    (f : τ→κ→ℂ) (w : τ→ℂ) (hw : ∀t,‖w t‖≤1) (E : ℝ)
    (hf : ∀t,(∑k,‖f t k‖^2)≤E) :
    (∑k,‖∑t,w t*f t k‖^2)≤(Fintype.card τ:ℝ)^2*E := by
  have hpoint (k : κ) : ‖∑t,w t*f t k‖^2≤(Fintype.card τ:ℝ)*∑t,‖f t k‖^2 := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : τ => (1:ℝ)) (fun t => ‖w t*f t k‖)
    have hn : ‖∑t,w t*f t k‖^2≤(∑t,‖w t*f t k‖)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
    apply hn.trans
    apply (show (∑t,‖w t*f t k‖)^2≤(Fintype.card τ:ℝ)*∑t,‖w t*f t k‖^2 by simpa using h).trans
    apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
    apply Finset.sum_le_sum
    intro t _
    apply pow_le_pow_left₀ (norm_nonneg _)
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (hw t)
  calc
    _ ≤ ∑k,(Fintype.card τ:ℝ)*∑t,‖f t k‖^2 := Finset.sum_le_sum (fun k _ => hpoint k)
    _ = (Fintype.card τ:ℝ)*∑t,∑k,‖f t k‖^2 := by rw [←Finset.mul_sum,Finset.sum_comm]
    _ ≤ (Fintype.card τ:ℝ)*∑_t : τ,E :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun t _ => hf t)) (Nat.cast_nonneg _)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

theorem energy_bound
    (W : ℝ→ℂ) (a b : ℝ) (ha : 0<a)
    (hsupp : Function.support W⊆Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (deltaLoss ε ρ q levelBound : ℝ) (hδ : 0<deltaLoss) (hε : 0<ε) (hρ : 0<ρ) (hq : 1<q) (hlevel : 1≤levelBound) :
    ∃C : ℝ,0<C ∧ ∀(rays : ℕ) (K X : ℝ),1≤K → 1≤X →
    ∀I F Q : Ideal O,I≠0 → Q≠0 → (Ideal.absNorm I:ℝ)≤K →
      1≤completedResidualScale K I Q → ∀d : ReflectedFiberData rays levelBound K I F Q,
      (∑k,‖d.value W X ρ q k‖^2)≤
        C*(rays:ℝ)^2*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss+ε)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
          (Ideal.absNorm (rowPowerfulPart I):ℝ) := by
  obtain ⟨Cb,hCb,hb⟩ := ReflectedBranchData.energy_bound W a b ha hsupp hW deltaLoss ρ q levelBound hδ hρ hq hlevel
  obtain ⟨Cp,hCp,hp⟩ := completed_branch_count_small_power ε hε
  refine ⟨Cb*Cp,by positivity,?_⟩
  intro rays K X hK hX I F Q hI hQ hIK hk d
  let : ∀p : d.pool,p.val.IsMaximal := d.maximal
  have hcount := hp (I*Q) (mul_ne_zero hI hQ) (fun p : d.pool => p.val)
    Subtype.val_injective d.divides
  have hnorm : (Ideal.absNorm (I*Q):ℝ)≤K*(Ideal.absNorm Q:ℝ) := by
    simp only [map_mul,Nat.cast_mul]
    exact mul_le_mul_of_nonneg_right hIK (Nat.cast_nonneg _)
  have hcount' : (6:ℝ)^(2*d.pool.card)≤Cp*(K*(Ideal.absNorm Q:ℝ))^ε := by
    have hc : (6:ℝ)^(2*d.pool.card)≤Cp*(Ideal.absNorm (I*Q):ℝ)^ε := by
      simpa only [Fintype.card_coe] using hcount
    exact hc.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) hnorm hε.le) hCp.le)
  have he := finite_energy_bound
    (fun b => (d.branch b).value W X ρ q) d.weight d.weight_bound _
    (fun b => hb K X hK hX I F Q hI hQ hIK hk (d.branch b))
  change (∑k,‖d.value W X ρ q k‖^2)≤_ at he
  apply he.trans
  have hc : (Fintype.card (Fin rays×(d.pool→Fin 6)):ℝ)^2=(rays:ℝ)^2*(6:ℝ)^(2*d.pool.card) := by
    simp only [Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe,Nat.cast_mul,Nat.cast_pow]
    rw [mul_pow,←pow_mul,Nat.mul_comm d.pool.card 2]
    norm_num
  rw [hc]
  have hnQ : 0<(Ideal.absNorm Q:ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hQ (Ideal.absNorm_eq_zero_iff.mp hz))
  have hKQ : 0<K*(Ideal.absNorm Q:ℝ) := mul_pos (by linarith) hnQ
  calc
    _ ≤ ((rays:ℝ)^2*(Cp*(K*(Ideal.absNorm Q:ℝ))^ε))*
      (Cb*(K*(Ideal.absNorm Q:ℝ))^(10*deltaLoss)*(K+K^2*(Ideal.absNorm Q:ℝ)/X)/
        (Ideal.absNorm (rowPowerfulPart I):ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_left hcount' (sq_nonneg _)
    _ = _ := by rw [Real.rpow_add hKQ]; ring

end ReflectedFiberData

open Eisenstein SchwartzPlanePoisson CanonicalRowCompletion

theorem one_le_completedResidualScale (K : ℝ) (I Q : Ideal O)
    (hI : I≠0) (hIK : (Ideal.absNorm I:ℝ)≤K) : 1≤completedResidualScale K I Q := by
  have hn : 1≤(Ideal.absNorm (rowResidualPart I Q):ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz =>
      squarefreeResidualPart_ne_zero (rowSimplePart I) Q (Ideal.absNorm_eq_zero_iff.mp hz))
  apply hn.trans
  rw [rowResidualPart_norm I Q hI,completedResidualScale]
  exact div_le_div_of_nonneg_right hIK (by positivity)

namespace ReflectedFiberData

def idealValue {rays : ℕ} {levelBound K : ℝ} {I F Q : Ideal O} (d : ReflectedFiberData rays levelBound K I F Q)
    (W : ℝ→ℂ) (X ρ q : ℝ) (J : Ideal O) : ℂ :=
  if h : J∈idealRange (completedResidualScale K I Q) then d.value W X ρ q ⟨J,h⟩ else 0

theorem idealValue_at {rays : ℕ} {levelBound K : ℝ} {I F Q : Ideal O} (d : ReflectedFiberData rays levelBound K I F Q)
    (W : ℝ→ℂ) (X ρ q : ℝ) (J : idealRange (completedResidualScale K I Q)) :
    d.idealValue W X ρ q J.val=d.value W X ρ q J := by
  simp only [idealValue,dif_pos J.property]

end ReflectedFiberData


end CompletedGauss

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
