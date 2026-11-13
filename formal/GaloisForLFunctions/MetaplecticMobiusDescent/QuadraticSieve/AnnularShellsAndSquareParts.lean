/-
Annular shells and square parts adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.QuadraticSieve.PoissonComparisonMajorant

/-!
# Annular shells and square parts

The small squarefree norm ball is separated before the remaining rows move into annuli. The
weighted common-conductor block is a finite sum of high squarefree-part pairs; the low source
term is a finite sum of principal square-variable kernels.
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

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein FiniteSieveRestriction
open scoped Classical

def liftingDivisibleColumns (N : ℝ) : Finset (QuadraticIdealRange N) :=
  Finset.univ.filter (fun J => liftingPrime ∣ J.val.val)

def liftingQuotientColumn (N : ℝ) (J : liftingDivisibleColumns N) : QuadraticIdealRange N :=
  ⟨⟨quadraticIdealQuotient liftingPrime J.val.val.val,
      quadraticIdealQuotient_admissible J.val.val.property (Finset.mem_filter.mp J.property).2⟩,by
    rw [quadraticIdealQuotient_norm liftingPrime_prime.ne_zero (Finset.mem_filter.mp J.property).2,
      liftingPrime_norm]
    have hN : 0 ≤ N := (Nat.cast_nonneg _).trans J.val.property
    exact (div_le_div_of_nonneg_right J.val.property (by norm_num : (0:ℝ)≤(7:ℕ))).trans
      (div_le_self hN (by norm_num))⟩

lemma liftingQuotientColumn_injective (N : ℝ) : Function.Injective (liftingQuotientColumn N) := by
  intro I J h
  apply Subtype.ext
  apply Subtype.ext
  apply Subtype.ext
  exact quadraticIdealQuotient_injective liftingPrime
    (Finset.mem_filter.mp I.property).2 (Finset.mem_filter.mp J.property).2
    (congrArg (fun Q : QuadraticIdealRange N => Q.val.val) h)

def liftingFreeCoefficient (N : ℝ) (a : QuadraticIdealRange N → ℂ) : QuadraticIdealRange N → ℂ :=
  fun J => if liftingPrime∣J.val.val then 0 else a J

def liftingDividedCoefficient (N : ℝ) (a : QuadraticIdealRange N → ℂ) : QuadraticIdealRange N → ℂ :=
  extendByZero Finset.univ (liftingQuotientColumn N) (fun J : liftingDivisibleColumns N => a J.val)

theorem liftingFreeCoefficient_coprime (N : ℝ) (a : QuadraticIdealRange N → ℂ)
    (J : QuadraticIdealRange N) (hJ : liftingFreeCoefficient N a J≠0) : IsCoprime liftingPrime J.val.val := by
  apply ideal_coprime_of_isRelPrime _ _
  apply liftingPrime_prime.irreducible.isRelPrime_iff_not_dvd.mpr
  intro hd
  exact hJ (by simp only [liftingFreeCoefficient,hd,ite_true])

theorem liftingDividedCoefficient_coprime (N : ℝ) (a : QuadraticIdealRange N → ℂ)
    (J : QuadraticIdealRange N) (hJ : liftingDividedCoefficient N a J≠0) : IsCoprime liftingPrime J.val.val := by
  classical
  have hmem : J∈(Finset.univ : Finset (liftingDivisibleColumns N)).image (liftingQuotientColumn N) := by
    by_contra hn
    exact hJ (extendByZero_zero _ _ _ _ hn)
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hmem
  have hdiv := (Finset.mem_filter.mp I.property).2
  have hsf : Squarefree (liftingPrime*quadraticIdealQuotient liftingPrime I.val.val.val) := by
    rw [quadraticIdeal_mul_quotient hdiv]
    exact I.val.val.property.2.1
  exact ideal_coprime_of_isRelPrime _ _ (squarefree_mul_iff.mp hsf).1

theorem liftingDividedCoefficient_row_sum (N : ℝ) (a : QuadraticIdealRange N → ℂ) (z : O) :
    (∑J : QuadraticIdealRange N, canonicalQuadraticRow J.val z*liftingDividedCoefficient N a J) =
      ∑J : liftingDivisibleColumns N, canonicalQuadraticRow (liftingQuotientColumn N J).val z*a J.val := by
  simpa only [liftingDividedCoefficient,liftingQuotientColumn] using
    extendByZero_matrix Finset.univ (liftingQuotientColumn N)
      (fun J : liftingDivisibleColumns N => a J.val) (fun (_ : Unit) J => canonicalQuadraticRow J.val z) ()

theorem liftingCoefficient_row_split (N : ℝ) (a : QuadraticIdealRange N → ℂ) (z : O) :
    (∑J : QuadraticIdealRange N, canonicalQuadraticRow J.val z*a J) =
      (∑J : QuadraticIdealRange N, canonicalQuadraticRow J.val z*liftingFreeCoefficient N a J) +
      canonicalQuadraticRow ⟨liftingPrime,liftingPrime_admissible⟩ z*(∑J : QuadraticIdealRange N, canonicalQuadraticRow J.val z*liftingDividedCoefficient N a J) := by
  rw [liftingDividedCoefficient_row_sum,Finset.mul_sum]
  have hs : (∑ J : liftingDivisibleColumns N,
      canonicalQuadraticRow ⟨liftingPrime,liftingPrime_admissible⟩ z *
        (canonicalQuadraticRow (liftingQuotientColumn N J).val z*a J.val)) =
      ∑ J ∈ liftingDivisibleColumns N, canonicalQuadraticRow J.val z*a J := by
    rw [← Finset.sum_coe_sort (s := liftingDivisibleColumns N)
      (f := fun J : QuadraticIdealRange N => canonicalQuadraticRow J.val z*a J)]
    apply Finset.sum_congr rfl
    intro J _
    rw [canonicalQuadraticRow_divisor_factor J.val.val liftingPrime (Finset.mem_filter.mp J.property).2]
    simp only [liftingQuotientColumn,mul_assoc]
  rw [hs]
  simp only [liftingDivisibleColumns,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J _
  by_cases hd : liftingPrime∣J.val.val <;>
    simp only [hd,ite_true,ite_false,liftingFreeCoefficient,mul_zero,zero_add,add_zero]

theorem liftingCoefficient_energy (N : ℝ) (a : QuadraticIdealRange N → ℂ) :
    (∑J : QuadraticIdealRange N, ‖liftingFreeCoefficient N a J‖^2) +
      (∑J : QuadraticIdealRange N, ‖liftingDividedCoefficient N a J‖^2) = ∑J, ‖a J‖^2 := by
  have he := extendByZero_energy Finset.univ (liftingQuotientColumn N)
    (fun J : liftingDivisibleColumns N => a J.val) (liftingQuotientColumn_injective N).injOn
  change (∑J : QuadraticIdealRange N, ‖liftingDividedCoefficient N a J‖^2)=
    ∑J : liftingDivisibleColumns N, ‖a J.val‖^2 at he
  rw [he,Finset.sum_coe_sort (liftingDivisibleColumns N) (fun J => ‖a J‖^2)]
  simp only [liftingDivisibleColumns,Finset.sum_filter,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro J _
  by_cases hd : liftingPrime∣J.val.val <;>
    simp only [liftingFreeCoefficient,hd,ite_true,ite_false,norm_zero,zero_pow (by decide : 2≠0),zero_add,add_zero]

theorem liftingCoefficient_row_energy (N : ℝ) (a : QuadraticIdealRange N → ℂ) (z : O) :
    ‖∑J : QuadraticIdealRange N, canonicalQuadraticRow J.val z*a J‖^2 ≤
      2*(‖∑J : QuadraticIdealRange N, canonicalQuadraticRow J.val z*liftingFreeCoefficient N a J‖^2 +
        ‖∑J : QuadraticIdealRange N, canonicalQuadraticRow J.val z*liftingDividedCoefficient N a J‖^2) := by
  rw [liftingCoefficient_row_split]
  let u := ∑J : QuadraticIdealRange N, canonicalQuadraticRow J.val z*liftingFreeCoefficient N a J
  let v := ∑J : QuadraticIdealRange N, canonicalQuadraticRow J.val z*liftingDividedCoefficient N a J
  change ‖u+canonicalQuadraticRow ⟨liftingPrime,liftingPrime_admissible⟩ z*v‖^2≤2*(‖u‖^2+‖v‖^2)
  have hp : ‖canonicalQuadraticRow ⟨liftingPrime,liftingPrime_admissible⟩ z*v‖≤‖v‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_left (norm_nonneg _) (canonicalQuadraticRow_norm_le_one _ _)
  have hn : ‖u+canonicalQuadraticRow ⟨liftingPrime,liftingPrime_admissible⟩ z*v‖≤‖u‖+‖v‖ := by
    linarith [norm_add_le u (canonicalQuadraticRow ⟨liftingPrime,liftingPrime_admissible⟩ z*v)]
  have hs := pow_le_pow_left₀ (norm_nonneg _) hn 2
  nlinarith [sq_nonneg (‖u‖-‖v‖)]


end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein
open scoped Classical

def ballQuadraticEnergy (M N : ℝ) (a : QuadraticIdealRange N → ℂ) : ℝ :=
  ∑ I : QuadraticIdealRange M,
    ‖∑ J : QuadraticIdealRange N, canonicalQuadraticRow J.val (primaryIdealGenerator I.val.val)*a J‖^2

/-- Separate the small squarefree norm ball before moving the remaining rows into annuli. -/
theorem ballQuadraticEnergy_low_high (M N K : ℝ) (a : QuadraticIdealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ sieveNorm K N * (∑ J, ‖a J‖^2) +
      ∑ I : squarefreeHighRange M K,
        ‖∑ J : QuadraticIdealRange N, canonicalQuadraticRow J.val (primaryIdealGenerator I.val.val.val)*a J‖^2 := by
  let S : Finset (QuadraticIdealRange M) :=
    Finset.univ.filter (fun I => (Ideal.absNorm I.val.val : ℝ) ≤ K)
  let E : QuadraticIdealRange M → ℝ := fun I =>
    ‖∑ J : QuadraticIdealRange N, canonicalQuadraticRow J.val (primaryIdealGenerator I.val.val)*a J‖^2
  have hr : Function.Injective (fun I : S => I.val.val) := by
    intro I J h
    exact Subtype.ext (Subtype.ext h)
  have hn := family_squared_norm_le (fun I : S => I.val.val)
    (fun J : QuadraticIdealRange N => J.val) hr Subtype.val_injective K N
    (fun I => (Finset.mem_filter.mp I.property).2) (fun J => J.property)
  have he := FiniteSieveOperator.energy_bound
    (fun (I : S) (J : QuadraticIdealRange N) =>
      canonicalQuadraticRow J.val (primaryIdealGenerator I.val.val.val)) a
  have hlo : (∑ I ∈ S, E I) ≤ sieveNorm K N * ∑ J, ‖a J‖^2 := by
    rw [← Finset.sum_coe_sort (s := S) (f := E)]
    exact he.trans (mul_le_mul_of_nonneg_right hn (by positivity))
  change (∑ I, E I) ≤ _ + ∑ I : squarefreeHighRange M K, E I.val
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun I : QuadraticIdealRange M => (Ideal.absNorm I.val.val : ℝ) ≤ K) E]
  rw [Finset.sum_coe_sort (s := squarefreeHighRange M K) (f := E)]
  simp only [not_le,squarefreeHighRange]
  exact add_le_add hlo le_rfl

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein
open scoped Classical

theorem ballQuadraticEnergy_lifted_annuli (M N K : ℝ) (hM : 0<M) (a : QuadraticIdealRange N → ℂ) :
    ballQuadraticEnergy M N a ≤ sieveNorm K N*(∑J, ‖a J‖^2) +
      2*((∑j : Fin 7, annularHighEnergy ((2:ℝ)^j.val*M) N K (liftingFreeCoefficient N a)) +
        ∑j : Fin 7, annularHighEnergy ((2:ℝ)^j.val*M) N K (liftingDividedCoefficient N a)) := by
  have hlo := ballQuadraticEnergy_low_high M N K a
  have hs : (∑I : squarefreeHighRange M K,
      ‖∑J : QuadraticIdealRange N, canonicalQuadraticRow J.val (primaryIdealGenerator I.val.val.val)*a J‖^2) ≤
      2*((∑I : squarefreeHighRange M K,
          ‖∑J : QuadraticIdealRange N, canonicalQuadraticRow J.val (primaryIdealGenerator I.val.val.val)*liftingFreeCoefficient N a J‖^2) +
        ∑I : squarefreeHighRange M K,
          ‖∑J : QuadraticIdealRange N, canonicalQuadraticRow J.val (primaryIdealGenerator I.val.val.val)*liftingDividedCoefficient N a J‖^2) := by
    calc
      _ ≤ ∑I : squarefreeHighRange M K, 2*(
          ‖∑J : QuadraticIdealRange N, canonicalQuadraticRow J.val (primaryIdealGenerator I.val.val.val)*liftingFreeCoefficient N a J‖^2 +
          ‖∑J : QuadraticIdealRange N, canonicalQuadraticRow J.val (primaryIdealGenerator I.val.val.val)*liftingDividedCoefficient N a J‖^2) :=
        Finset.sum_le_sum (fun I _ => liftingCoefficient_row_energy N a (primaryIdealGenerator I.val.val.val))
      _ = _ := by rw [←Finset.mul_sum,Finset.sum_add_distrib]
  have hfree := squarefreeHigh_energy_le_annuli M N K hM (liftingFreeCoefficient N a)
    (liftingFreeCoefficient_coprime N a)
  have hdiv := squarefreeHigh_energy_le_annuli M N K hM (liftingDividedCoefficient N a)
    (liftingDividedCoefficient_coprime N a)
  linarith

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein FiniteSieveRestriction
open scoped Classical

def CoefficientOnShell (N X : ℝ) (a : QuadraticIdealRange N → ℂ) : Prop :=
  ∀ J, a J ≠ 0 → X / 2 < (Ideal.absNorm J.val.val : ℝ) ∧ (Ideal.absNorm J.val.val : ℝ) ≤ X

theorem column_dyadic_exists (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale) (J : QuadraticIdealRange N) :
    ∃ j ∈ Finset.range (lengthScale + 1), (2 : ℝ) ^ j / 2 < (Ideal.absNorm J.val.val : ℝ) ∧
      (Ideal.absNorm J.val.val : ℝ) ≤ (2 : ℝ) ^ j := by
  have hn : 1 ≤ Ideal.absNorm J.val.val := Nat.one_le_iff_ne_zero.mpr
    (fun hz => (primaryIdealGenerator_ne_zero_ideal _ J.val.property.1) (Ideal.absNorm_eq_zero_iff.mp hz))
  exact exists_dyadic_shell (Ideal.absNorm J.val.val) lengthScale hn (J.property.trans hNL)

def columnDyadicSector (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale) (J : QuadraticIdealRange N) : Fin (lengthScale + 1) :=
  ⟨(column_dyadic_exists N lengthScale hNL J).choose,
    Finset.mem_range.mp (column_dyadic_exists N lengthScale hNL J).choose_spec.1⟩

def dyadicColumnCoefficient (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (j : Fin (lengthScale + 1)) (a : QuadraticIdealRange N → ℂ) : QuadraticIdealRange N → ℂ :=
  sectorCoefficient (columnDyadicSector N lengthScale hNL) j a

theorem dyadicColumnCoefficient_shell (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (j : Fin (lengthScale + 1)) (a : QuadraticIdealRange N → ℂ) :
    CoefficientOnShell N ((2 : ℝ) ^ j.val) (dyadicColumnCoefficient N lengthScale hNL j a) := by
  intro J hJ
  have he : columnDyadicSector N lengthScale hNL J = j := by
    by_contra hn
    exact hJ (by simp only [dyadicColumnCoefficient, sectorCoefficient, if_neg hn])
  have hs := (column_dyadic_exists N lengthScale hNL J).choose_spec.2
  have hv : (columnDyadicSector N lengthScale hNL J).val = j.val := congrArg Fin.val he
  change (column_dyadic_exists N lengthScale hNL J).choose = j.val at hv
  simpa only [hv] using hs

theorem dyadicColumnCoefficient_energy (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (a : QuadraticIdealRange N → ℂ) :
    (∑ j : Fin (lengthScale + 1), ∑ J, ‖dyadicColumnCoefficient N lengthScale hNL j a J‖ ^ 2) = ∑ J, ‖a J‖ ^ 2 :=
  sectorCoefficient_energy (columnDyadicSector N lengthScale hNL) a

theorem weighted_energy_column_shells {m : Type*} [Fintype m]
    (N : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (A : Matrix m (QuadraticIdealRange N) ℂ) (v : m → ℝ) (hv : ∀ i, 0 ≤ v i)
    (a : QuadraticIdealRange N → ℂ) :
    (∑ i, v i * ‖∑ J, A i J * a J‖ ^ 2) ≤
      (lengthScale + 1 : ℝ) * ∑ j : Fin (lengthScale + 1), ∑ i,
        v i * ‖∑ J, A i J * dyadicColumnCoefficient N lengthScale hNL j a J‖ ^ 2 := by
  simpa only [Fintype.card_fin, Nat.cast_add, Nat.cast_one, dyadicColumnCoefficient] using
    weighted_energy_sector_bound (columnDyadicSector N lengthScale hNL) A a v hv

theorem annularHighEnergy_column_shells (M N K : ℝ) (lengthScale : ℕ) (hNL : N ≤ (2 : ℝ) ^ lengthScale)
    (a : QuadraticIdealRange N → ℂ) :
    annularHighEnergy M N K a ≤ (lengthScale + 1 : ℝ) *
      ∑ j : Fin (lengthScale + 1), annularHighEnergy M N K (dyadicColumnCoefficient N lengthScale hNL j a) := by
  exact weighted_energy_column_shells N lengthScale hNL
    (fun I : highKernelRange (2 * M) K => fun J => canonicalQuadraticRow J.val (primaryIdealGenerator I.val))
    (fun I => annularHighWeight M I.val) (fun _ => annularSieveBump.nonneg) a


end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory FiniteSieveRestriction
open scoped SchwartzMap Classical

def originalPairSource (I J : QuadraticIdeal) (W : ℝ → ℂ) (M : ℝ) (H : Ideal O) : ℂ :=
  if quadraticSupported H then
    star (canonicalQuadraticRow I (primaryIdealGenerator H)) *
      canonicalQuadraticRow J (primaryIdealGenerator H) * W ((Ideal.absNorm H : ℝ)/M)
  else 0

def originalPairLow (I J : QuadraticIdeal) (W : ℝ → ℂ) (M K : ℝ) (H : Ideal O) : ℂ :=
  if (Ideal.absNorm (quadraticSquarefreePart H) : ℝ) ≤ K then originalPairSource I J W M H else 0

def originalPairHigh (I J : QuadraticIdeal) (W : ℝ → ℂ) (M K : ℝ) (H : Ideal O) : ℂ :=
  if K < (Ideal.absNorm (quadraticSquarefreePart H) : ℝ) then originalPairSource I J W M H else 0

lemma originalPairSource_summable (I J : QuadraticIdeal) (W : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0 < M) :
    Summable (originalPairSource I J W M) := by
  apply Summable.of_norm
  apply Summable.of_nonneg_of_le (fun H => norm_nonneg _) _ (radial_ideal_summable_norm W M hM)
  intro H
  by_cases hH : quadraticSupported H
  · simp only [originalPairSource,if_pos hH,norm_mul,norm_star]
    calc
      _ ≤ (1*1)*‖W ((Ideal.absNorm H : ℝ)/M)‖ := by
        gcongr
        · exact canonicalQuadraticRow_norm_le_one I _
        · exact canonicalQuadraticRow_norm_le_one J _
      _ = _ := by rw [one_mul,one_mul]
  · simp only [originalPairSource,if_neg hH,norm_zero]
    positivity

lemma originalPairLow_summable (I J : QuadraticIdeal) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0 < M) :
    Summable (originalPairLow I J W M K) :=
  (originalPairSource_summable I J W M hM).indicator _

lemma originalPairHigh_summable (I J : QuadraticIdeal) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0 < M) :
    Summable (originalPairHigh I J W M K) :=
  (originalPairSource_summable I J W M hM).indicator _

lemma originalPairHigh_eq_source_sub_low (I J : QuadraticIdeal) (W : 𝓢(ℝ,ℂ))
    (M K : ℝ) (hM : 0 < M) :
    (∑' H : Ideal O, originalPairHigh I J W M K H) =
      (∑' H : Ideal O, originalPairSource I J W M H) - ∑' H : Ideal O, originalPairLow I J W M K H := by
  calc
    _ = ∑' H : Ideal O, (originalPairSource I J W M H - originalPairLow I J W M K H) := by
      apply tsum_congr
      intro H
      by_cases hK : (Ideal.absNorm (quadraticSquarefreePart H) : ℝ) ≤ K
      · simp only [originalPairHigh,originalPairLow,if_pos hK,if_neg (not_lt.mpr hK),sub_self]
      · simp only [originalPairHigh,originalPairLow,if_neg hK,if_pos (lt_of_not_ge hK),sub_zero]
    _ = _ := (originalPairSource_summable I J W M hM).tsum_sub (originalPairLow_summable I J W M K hM)

lemma annularHighWeight_eq_zero (M : ℝ) (hM : 0 < M) (I : Ideal O)
    (hI : 2*M ≤ (Ideal.absNorm I : ℝ)) : annularHighWeight M I = 0 := by
  have ht : 2 ≤ (Ideal.absNorm I : ℝ)/M := (le_div_iff₀ hM).mpr (by linarith)
  exact annularSieveBump_zero_of_ge (by linarith)

lemma originalPairHigh_annular_finite (I J : QuadraticIdeal) (M K : ℝ) (hM : 0 < M) :
    (∑' H : Ideal O, originalPairHigh I J annularSieveCutoff M K H) =
      ∑ H : highKernelRange (2*M) K,
        star (canonicalQuadraticRow I (primaryIdealGenerator H.val)) *
          canonicalQuadraticRow J (primaryIdealGenerator H.val) * (annularHighWeight M H.val : ℂ) := by
  rw [tsum_eq_sum (s := highKernelRange (2*M) K) (fun H hH => ?_)]
  · rw [← Finset.sum_coe_sort (s := highKernelRange (2*M) K)
      (f := fun H => originalPairHigh I J annularSieveCutoff M K H)]
    apply Finset.sum_congr rfl
    intro H _
    have hh := mem_highKernelRange.mp H.property
    simp only [originalPairHigh,originalPairSource,if_pos hh.1,if_pos hh.2.2,
      annularSieveCutoff_apply,annularHighWeight]
  · by_cases hs : quadraticSupported H
    · by_cases hk : K < (Ideal.absNorm (quadraticSquarefreePart H) : ℝ)
      · have hn : 2*M < (Ideal.absNorm H : ℝ) := by
          by_contra h
          exact hH (mem_highKernelRange.mpr ⟨hs,le_of_not_gt h,hk⟩)
        simp only [originalPairHigh,originalPairSource,if_pos hk,if_pos hs,annularSieveCutoff_apply]
        change _ * (annularHighWeight M H : ℂ) = 0
        rw [annularHighWeight_eq_zero M hM H hn.le,Complex.ofReal_zero,mul_zero]
      · simp only [originalPairHigh,if_neg hk]
    · simp only [originalPairHigh,originalPairSource,if_neg hs,ite_self]

/-- The weighted common-conductor block is a finite sum of high squarefree-part pairs. -/
theorem annularRayCommonFactorBlock_eq_pair_high (M N K : ℝ) (hM : 0 < M)
    (D : Ideal O) (c : QuadraticRayRing) (a : QuadraticIdealRange N → ℂ) :
    annularRayCommonFactorBlock M N K D c a =
      ∑ I : QuadraticIdealRange N, ∑ J : QuadraticIdealRange N,
        (if I.val.val ⊔ J.val.val = D ∧ quadraticColumnRay I.val = c ∧ quadraticColumnRay J.val = c
          then star (a I)*a J else 0) *
        ∑' H : Ideal O, originalPairHigh I.val J.val annularSieveCutoff M K H := by
  simp_rw [originalPairHigh_annular_finite _ _ M K hM]
  unfold annularRayCommonFactorBlock weightedRayCommonFactorBlock weightedCommonFactorBlock
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro I _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro J _
  apply Finset.sum_congr rfl
  intro H _
  by_cases hd : I.val.val ⊔ J.val.val = D <;>
    by_cases hi : quadraticColumnRay I.val = c <;>
    by_cases hj : quadraticColumnRay J.val = c <;>
      simp only [sectorCoefficient,hd,hi,hj,ite_true,ite_false,true_and,false_and,and_false,
        mul_zero,zero_mul,star_zero,star_mul] <;> ring

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory
open scoped SchwartzMap Classical

/-- Squarefree-square decomposition of the source term below its squarefree cutoff. -/
theorem originalPairLow_squarefree_tsum (I J : QuadraticIdeal)
    (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0 < M) :
    (∑' H : Ideal O, originalPairLow I J W M K H) =
      ∑' B : QuadraticIdeal, if (Ideal.absNorm B.val : ℝ) ≤ K then
        (canonicalQuadraticRow I (primaryIdealGenerator B.val) * canonicalQuadraticRow J (primaryIdealGenerator B.val)) *
          ∑' A : QuadraticSupportedIdeal,
            (quadraticIdealMask I (primaryIdealGenerator A.val) * quadraticIdealMask J (primaryIdealGenerator A.val)) *
              W (((Ideal.absNorm B.val : ℝ)*(Ideal.absNorm A.val : ℝ)^2)/M)
        else 0 := by
  let F : QuadraticIdeal × QuadraticSupportedIdeal → ℂ := fun p =>
    if (Ideal.absNorm p.1.val : ℝ) ≤ K then
      (canonicalQuadraticRow I (primaryIdealGenerator p.1.val) * canonicalQuadraticRow J (primaryIdealGenerator p.1.val)) *
        (quadraticIdealMask I (primaryIdealGenerator p.2.val) * quadraticIdealMask J (primaryIdealGenerator p.2.val)) *
          W (((Ideal.absNorm p.1.val : ℝ)*(Ideal.absNorm p.2.val : ℝ)^2)/M)
    else 0
  have hterm (p : QuadraticIdeal × QuadraticSupportedIdeal) :
      originalPairLow I J W M K (p.1.val*p.2.val^2) = F p := by
    have hs : quadraticSupported (p.1.val*p.2.val^2) :=
      (quadraticSupported_mul _ _).mpr ⟨⟨p.1.property.1,p.1.property.2.2⟩,
        (quadraticSupported_sq _).mpr p.2.property⟩
    unfold originalPairLow
    rw [(quadraticParts_of_squarefree p.1.val p.2.val p.1.property.2.1
      (primaryIdealGenerator_ne_zero_ideal _ p.2.property.1)).1]
    by_cases hk : (Ideal.absNorm p.1.val : ℝ) ≤ K
    · rw [if_pos hk,originalPairSource,if_pos hs,canonicalQuadraticRow_star]
      simp only [
        canonicalQuadraticRow_squarefree_argument,F,if_pos hk,map_mul,map_pow,Nat.cast_mul,Nat.cast_pow]
      ring
    · simp only [if_neg hk,F]
  have hsub := (originalPairLow_summable I J W M K hM).subtype quadraticSupported
  have hp0 : Summable (fun p : QuadraticIdeal × QuadraticSupportedIdeal =>
      originalPairLow I J W M K (p.1.val*p.2.val^2)) :=
    quadraticSupportedPartsEquiv.symm.summable_iff.mpr hsub
  have hp : Summable F := hp0.congr hterm
  have he : (∑' H : QuadraticSupportedIdeal, originalPairLow I J W M K H.val) =
      ∑' H : Ideal O, originalPairLow I J W M K H := by
    apply tsum_subtype_eq_of_support_subset
    intro H hH
    by_contra hs
    change ¬ quadraticSupported H at hs
    exact hH (by simp only [originalPairLow,originalPairSource,if_neg hs,ite_self])
  rw [← he,quadraticSupported_tsum_parts]
  calc
    _ = ∑' p, F p := tsum_congr hterm
    _ = ∑' B : QuadraticIdeal, ∑' A : QuadraticSupportedIdeal, F (B,A) := hp.tsum_prod
    _ = _ := by
      apply tsum_congr
      intro B
      by_cases hB : (Ideal.absNorm B.val : ℝ) ≤ K
      · simp only [F,if_pos hB,mul_assoc,tsum_mul_left]
      · simp only [F,if_neg hB,tsum_zero]

lemma tsum_quadraticIdeal_cutoff (K : ℝ) (f : QuadraticIdeal → ℂ) :
    (∑' B : QuadraticIdeal, if (Ideal.absNorm B.val : ℝ) ≤ K then f B else 0) =
      ∑ B : QuadraticIdealRange K, f B.val := by
  let F : QuadraticIdeal → ℂ := fun B => if (Ideal.absNorm B.val : ℝ) ≤ K then f B else 0
  have he : (∑' B : QuadraticIdealRange K, F B.val) = ∑' B : QuadraticIdeal, F B := by
    apply tsum_subtype_eq_of_support_subset
    intro B hB
    by_contra hn
    exact hB (if_neg hn)
  change (∑' B, F B) = _
  rw [← he,tsum_fintype]
  exact Finset.sum_congr rfl (fun B _ => if_pos B.property)

/-- The low source term is a finite sum of principal square-variable kernels. -/
theorem originalPairLow_principal_finite (I J : QuadraticIdeal)
    (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0 < M) :
    (∑' H : Ideal O, originalPairLow I J W M K H) =
      ∑ B : QuadraticIdealRange K,
        (canonicalQuadraticRow I (primaryIdealGenerator B.val.val) *
          canonicalQuadraticRow J (primaryIdealGenerator B.val.val)) *
          ((Nat.card Oˣ : ℂ)⁻¹ * quadraticLowPrincipalLattice I J W
            (Real.sqrt (M/(Ideal.absNorm B.val.val : ℝ)))) := by
  rw [originalPairLow_squarefree_tsum I J W M K hM,tsum_quadraticIdeal_cutoff]
  apply Finset.sum_congr rfl
  intro B _
  congr 1
  have hN : 0 < (Ideal.absNorm B.val.val : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr
      (fun hz => (primaryIdealGenerator_ne_zero_ideal _ B.val.property.1) (Ideal.absNorm_eq_zero_iff.mp hz))
  have hX : 0 < Real.sqrt (M/(Ideal.absNorm B.val.val : ℝ)) := Real.sqrt_pos.mpr (div_pos hM hN)
  rw [quadraticLowPrincipalLattice_eq I J W _ hX,←mul_assoc,
    inv_mul_cancel₀ eisenstein_unit_card_ne_zero,one_mul]
  unfold quadraticLowPrincipalIdeal
  apply tsum_congr
  intro A
  congr 2
  rw [div_pow,Real.sq_sqrt (div_pos hM hN).le]
  field_simp

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson
open scoped SchwartzMap Classical

def quotientColumn (D : Ideal O) (I : QuadraticIdeal) (h : D ∣ I.val) : QuadraticIdeal :=
  ⟨quadraticIdealQuotient D I.val,quadraticIdealQuotient_admissible I.property h⟩

lemma rowPrimeSupportMask_indicator (G : Ideal O) (hG : G ≠ 0) (z : O) :
    rowCoprimeMask (fun P : primeSupport G => P.val) Finset.univ z =
      if IsCoprime (Ideal.span {z}) G then 1 else 0 := by
  simp only [rowCoprimeMask,primeCoprimeMask_indicator,Finset.mem_univ,true_implies,
    Subtype.forall,ideal_generator_dvd_iff,← ideal_coprime_support_iff _ G hG]

/-- Removing a common conductor leaves exactly its coprimality mask. -/
lemma canonical_pair_divisor_mask (D : Ideal O) (I J : QuadraticIdeal)
    (hDI : D ∣ I.val) (hDJ : D ∣ J.val) (z : O) :
    star (canonicalQuadraticRow I z) * canonicalQuadraticRow J z =
      quadraticIdealMask ⟨D,quadraticIdealAdmissible_of_dvd I.property hDI⟩ z *
        (canonicalQuadraticRow (quotientColumn D I hDI) z * canonicalQuadraticRow (quotientColumn D J hDJ) z) := by
  let D' : QuadraticIdeal := ⟨D,quadraticIdealAdmissible_of_dvd I.property hDI⟩
  have hs : canonicalQuadraticRow D' z ^ 2 = quadraticIdealMask D' z := by
    rw [pow_two,← canonicalQuadraticRow_mul,← pow_two,canonicalQuadraticRow_square]
  rw [canonicalQuadraticRow_star,canonicalQuadraticRow_divisor_factor I D hDI,
    canonicalQuadraticRow_divisor_factor J D hDJ]
  change (canonicalQuadraticRow D' z * canonicalQuadraticRow (quotientColumn D I hDI) z) *
      (canonicalQuadraticRow D' z * canonicalQuadraticRow (quotientColumn D J hDJ) z) = _
  calc
    _ = canonicalQuadraticRow D' z ^ 2 *
        (canonicalQuadraticRow (quotientColumn D I hDI) z * canonicalQuadraticRow (quotientColumn D J hDJ) z) := by ring
    _ = _ := by rw [hs]

lemma quadraticIdealMask_primary_commonMask (D : QuadraticIdeal) (B : Ideal O)
    (hB : quadraticSupported B) :
    quadraticIdealMask D (primaryIdealGenerator B) =
      if IsCoprime B (quadraticMaskIdeal D.val) then 1 else 0 := by
  rw [quadraticIdealMask_indicator,(primaryIdealGenerator_spec B hB.1).1]
  simp only [quadraticMask_coprime_iff D.val B (primaryIdealGenerator_ne_zero_ideal _ D.property.1),hB,true_and]

lemma residual_joint_mask (D : Ideal O) (I J : QuadraticIdeal)
    (hDI : D ∣ I.val) (hDJ : D ∣ J.val) (z : O) :
    primeCoprimeMask cubicIdealGenerator (quadraticMaskPrimes (I.val*J.val)) z =
      rowCoprimeMask (fun P : primeSupport
        (quadraticMaskIdeal D*(quadraticIdealQuotient D I.val*quadraticIdealQuotient D J.val)) => P.val) Finset.univ z := by
  have hD : D ≠ 0 := ne_zero_of_dvd_ne_zero (primaryIdealGenerator_ne_zero_ideal _ I.property.1) hDI
  have hIq := quadraticIdealQuotient_admissible I.property hDI
  have hJq := quadraticIdealQuotient_admissible J.property hDJ
  have hQ : quadraticIdealQuotient D I.val*quadraticIdealQuotient D J.val ≠ 0 :=
    mul_ne_zero (primaryIdealGenerator_ne_zero_ideal _ hIq.1) (primaryIdealGenerator_ne_zero_ideal _ hJq.1)
  have hIJ : I.val*J.val ≠ 0 :=
    mul_ne_zero (primaryIdealGenerator_ne_zero_ideal _ I.property.1) (primaryIdealGenerator_ne_zero_ideal _ J.property.1)
  rw [primeIdealMask_indicator _ (quadraticMaskPrimes_prime _),
    rowPrimeSupportMask_indicator _ (mul_ne_zero (quadraticMaskIdeal_squarefree D).ne_zero hQ)]
  change (if IsCoprime (Ideal.span {z}) (quadraticMaskIdeal (I.val*J.val)) then (1:ℂ) else 0) = _
  congr 1
  apply propext
  rw [quadraticMask_coprime_iff _ _ hIJ]
  constructor
  · rintro ⟨hs,hc⟩
    have hd : IsCoprime (Ideal.span {z}) D :=
      hc.of_isCoprime_of_dvd_right (hDI.trans (dvd_mul_right I.val J.val))
    have hq : IsCoprime (Ideal.span {z}) (quadraticIdealQuotient D I.val*quadraticIdealQuotient D J.val) :=
      hc.of_isCoprime_of_dvd_right (mul_dvd_mul (quadraticIdealQuotient_dvd hDI) (quadraticIdealQuotient_dvd hDJ))
    exact ((quadraticMask_coprime_iff D _ hD).mpr ⟨hs,hd⟩).mul_right hq
  · intro hc
    have hmask := hc.of_isCoprime_of_dvd_right
      (dvd_mul_right (quadraticMaskIdeal D) (quadraticIdealQuotient D I.val*quadraticIdealQuotient D J.val))
    obtain ⟨hs,hd⟩ := (quadraticMask_coprime_iff D _ hD).mp hmask
    have hq := hc.of_isCoprime_of_dvd_right
      (dvd_mul_left (quadraticIdealQuotient D I.val*quadraticIdealQuotient D J.val) (quadraticMaskIdeal D))
    have hi := hq.of_isCoprime_of_dvd_right
      (dvd_mul_right (quadraticIdealQuotient D I.val) (quadraticIdealQuotient D J.val))
    have hj := hq.of_isCoprime_of_dvd_right
      (dvd_mul_left (quadraticIdealQuotient D J.val) (quadraticIdealQuotient D I.val))
    refine ⟨hs,?_⟩
    have hp := (hd.mul_right hi).mul_right (hd.mul_right hj)
    simpa only [quadraticIdeal_mul_quotient hDI,quadraticIdeal_mul_quotient hDJ] using hp

lemma quadraticLowPrincipalLattice_residual (D : Ideal O) (I J : QuadraticIdeal)
    (hDI : D ∣ I.val) (hDJ : D ∣ J.val) (W : 𝓢(ℝ,ℂ)) (X : ℝ) :
    quadraticLowPrincipalLattice I J W X =
      ∑' z : O, rowCoprimeMask (fun P : primeSupport
        (quadraticMaskIdeal D*(quadraticIdealQuotient D I.val*quadraticIdealQuotient D J.val)) => P.val) Finset.univ z *
        (if z=0 then 0 else quadraticSquareProfile W (‖ringComplex z‖^2/X)) := by
  unfold quadraticLowPrincipalLattice
  apply tsum_congr
  intro z
  by_cases hz : z=0
  · subst z
    rw [primeCoprimeMask_zero cubicIdealGenerator (quadraticMaskPrimes (I.val*J.val))
      ⟨ramifiedIdeal,Finset.mem_union_left _ (Finset.mem_insert_self _ _)⟩,zero_mul,if_pos rfl,mul_zero]
  · rw [if_neg hz,quadraticSquareProfile_apply,residual_joint_mask D I J hDI hDJ]

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein
open scoped Classical

lemma primaryIdealGenerator_unit_mod_four (I : QuadraticIdeal) :
    IsUnit (quadraticColumnRay I) := by
  have hn := ((quadraticSupported_iff_bad_not_dvd I.val).mp ⟨I.property.1,I.property.2.2⟩).2
  have hc := (ideal_coprime_prime_iff_not_dvd I.val cubicTwoIdeal quadratic_twoIdeal_prime).mpr hn
  rw [← (primaryIdealGenerator_spec I.val I.property.1).1,cubicTwoIdeal,
    Ideal.isCoprime_span_singleton_iff] at hc
  have h4 : IsCoprime (primaryIdealGenerator I.val) (4 : O) := by
    simpa only [show (-2 : O)^2=4 by norm_num] using hc.pow_right (n := 2)
  obtain ⟨a,b,hab⟩ := h4
  let f := Ideal.Quotient.mk (Ideal.span {(4 : O)})
  have hz : f (4 : O) = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (by simp))
  have he : f a*f (primaryIdealGenerator I.val) = 1 := by
    have h := congrArg f hab
    simpa only [map_add,map_mul,map_one,hz,mul_zero,add_zero] using h
  refine ⟨⟨f (primaryIdealGenerator I.val),f a,?_,he⟩,rfl⟩
  simpa only [mul_comm] using he

/-- Division by a common odd conductor preserves equality of residue classes modulo four. -/
lemma quadraticColumnRay_quotient_eq (D : Ideal O) (I J : QuadraticIdeal)
    (hDI : D ∣ I.val) (hDJ : D ∣ J.val)
    (hray : quadraticColumnRay I = quadraticColumnRay J) :
    quadraticColumnRay (quotientColumn D I hDI) = quadraticColumnRay (quotientColumn D J hDJ) := by
  let D' : QuadraticIdeal := ⟨D,quadraticIdealAdmissible_of_dvd I.property hDI⟩
  obtain ⟨u,hu⟩ := primaryIdealGenerator_unit_mod_four D'
  change Ideal.Quotient.mk (Ideal.span {(4 : O)}) (primaryIdealGenerator I.val) =
    Ideal.Quotient.mk (Ideal.span {(4 : O)}) (primaryIdealGenerator J.val) at hray
  rw [quadraticIdealGenerator_factor hDI,quadraticIdealGenerator_factor hDJ,map_mul,map_mul] at hray
  change (u : QuadraticRayRing) = Ideal.Quotient.mk (Ideal.span {(4 : O)}) (primaryIdealGenerator D) at hu
  rw [← hu] at hray
  exact (Units.mul_right_inj u).mp hray

lemma residual_quadraticMask_coprime (D : Ideal O) (I : QuadraticIdeal) (hDI : D ∣ I.val) :
    IsCoprime (quadraticMaskIdeal D) (quadraticIdealQuotient D I.val) := by
  have hQ := quadraticIdealQuotient_admissible I.property hDI
  have hD : D ≠ 0 := ne_zero_of_dvd_ne_zero (primaryIdealGenerator_ne_zero_ideal _ I.property.1) hDI
  have hs : Squarefree (D*quadraticIdealQuotient D I.val) := by
    rw [quadraticIdeal_mul_quotient hDI]
    exact I.property.2.1
  have hc := ideal_coprime_of_isRelPrime D (quadraticIdealQuotient D I.val) (squarefree_mul_iff.mp hs).1
  exact ((quadraticMask_coprime_iff D _ hD).mpr ⟨⟨hQ.1,hQ.2.2⟩,hc.symm⟩).symm

lemma quadraticIdealQuotient_shell (D I : Ideal O) (hD : D ≠ 0) (hDI : D ∣ I) (N : ℝ)
    (hI : N/2 ≤ (Ideal.absNorm I : ℝ) ∧ (Ideal.absNorm I : ℝ) ≤ N) :
    (N/(Ideal.absNorm D : ℝ))/2 ≤ (Ideal.absNorm (quadraticIdealQuotient D I) : ℝ) ∧
      (Ideal.absNorm (quadraticIdealQuotient D I) : ℝ) ≤ N/(Ideal.absNorm D : ℝ) := by
  rw [quadraticIdealQuotient_norm hD hDI]
  constructor
  · calc
      _ = (N/2)/(Ideal.absNorm D : ℝ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hI.1 (Nat.cast_nonneg _)
  · exact div_le_div_of_nonneg_right hI.2 (Nat.cast_nonneg _)

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson
open scoped SchwartzMap Classical

lemma sum_quadraticIdealRange_coprime (D : Ideal O) (K : ℝ) (f : Ideal O → ℂ) :
    (∑ B : QuadraticIdealRange K, if IsCoprime B.val.val (quadraticMaskIdeal D) then f B.val.val else 0) =
      ∑ B : coprimeSquarefreeIdealBall (quadraticMaskIdeal D) K, f B.val := by
  let S := Finset.univ.filter (fun B : QuadraticIdealRange K => IsCoprime B.val.val (quadraticMaskIdeal D))
  let e : S ≃ coprimeSquarefreeIdealBall (quadraticMaskIdeal D) K := {
    toFun := fun B => ⟨B.val.val.val,Finset.mem_filter.mpr
      ⟨mem_squarefreeIdealBall.mpr ⟨B.val.val.property.2.1,B.val.property⟩,
        (Finset.mem_filter.mp B.property).2⟩⟩
    invFun := fun B => ⟨⟨⟨B.val,coprimeSquarefreeIdealBall_admissible D K B⟩,
      (mem_squarefreeIdealBall.mp (Finset.mem_filter.mp B.property).1).2⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp B.property).2⟩⟩
    left_inv := fun B => by apply Subtype.ext; apply Subtype.ext; apply Subtype.ext; rfl
    right_inv := fun B => by apply Subtype.ext; rfl }
  calc
    _ = ∑ B ∈ S, f B.val.val := by rw [Finset.sum_filter]
    _ = ∑ B : S, f B.val.val.val := (Finset.sum_coe_sort S _).symm
    _ = _ := Fintype.sum_equiv e _ _ (fun _ => rfl)

def pairMaskedSquareSource (G : Ideal O) (I J : QuadraticIdeal)
    (W : 𝓢(ℝ,ℂ)) (M : ℝ) (B : Ideal O) : ℂ :=
  (canonicalQuadraticRow I (primaryIdealGenerator B)*canonicalQuadraticRow J (primaryIdealGenerator B))*
    ∑' z : O, rowCoprimeMask (fun P : primeSupport (G*(I.val*J.val)) => P.val) Finset.univ z *
      (if z=0 then 0 else quadraticSquareProfile W (‖ringComplex z‖^2/sourcePrincipalScale M B))

/-- Removing a common conductor turns the low squarefree sum into a coprime principal sum. -/
theorem originalPairLow_residual_finite (D : Ideal O) (I J : QuadraticIdeal)
    (hDI : D ∣ I.val) (hDJ : D ∣ J.val) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0 < M) :
    (∑' H : Ideal O, originalPairLow I J W M K H) =
      (Nat.card Oˣ : ℂ)⁻¹ * ∑ B : coprimeSquarefreeIdealBall (quadraticMaskIdeal D) K,
        pairMaskedSquareSource (quadraticMaskIdeal D) (quotientColumn D I hDI) (quotientColumn D J hDJ) W M B.val := by
  rw [originalPairLow_principal_finite I J W M K hM]
  have ht (B : QuadraticIdealRange K) :
      (canonicalQuadraticRow I (primaryIdealGenerator B.val.val)*canonicalQuadraticRow J (primaryIdealGenerator B.val.val))*
        ((Nat.card Oˣ : ℂ)⁻¹*quadraticLowPrincipalLattice I J W (Real.sqrt (M/(Ideal.absNorm B.val.val : ℝ)))) =
      (Nat.card Oˣ : ℂ)⁻¹ * (if IsCoprime B.val.val (quadraticMaskIdeal D) then
        pairMaskedSquareSource (quadraticMaskIdeal D) (quotientColumn D I hDI) (quotientColumn D J hDJ) W M B.val.val else 0) := by
    have hp := canonical_pair_divisor_mask D I J hDI hDJ (primaryIdealGenerator B.val.val)
    rw [canonicalQuadraticRow_star,quadraticIdealMask_primary_commonMask _ _
      ⟨B.val.property.1,B.val.property.2.2⟩] at hp
    rw [hp,quadraticLowPrincipalLattice_residual D I J hDI hDJ]
    by_cases hc : IsCoprime B.val.val (quadraticMaskIdeal D)
    · simp only [if_pos hc,one_mul,pairMaskedSquareSource,sourcePrincipalScale,quotientColumn]
      simp only [mul_assoc,mul_left_comm,mul_comm]
      rfl
    · simp only [if_neg hc,zero_mul,mul_zero]
  simp_rw [ht]
  rw [← Finset.mul_sum,sum_quadraticIdealRange_coprime]

theorem originalLow_commonFactor_aggregate {n : Type} [Fintype n]
    (D : Ideal O) (hD : D ≠ 0) (cols : n → QuadraticIdeal)
    (hdiv : ∀ j, D ∣ (cols j).val) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0 < M) :
    (∑ j, ∑ k, if (cols j).val ⊔ (cols k).val = D then
      star (a j)*a k*(∑' H : Ideal O, originalPairLow (cols j) (cols k) W M K H) else 0) =
      (Nat.card Oˣ : ℂ)⁻¹ * maskedPrincipalSourceSum (quadraticMaskIdeal D) (quadraticSquareProfile W)
        (fun B : coprimeSquarefreeIdealBall (quadraticMaskIdeal D) K =>
          ⟨B.val,coprimeSquarefreeIdealBall_admissible D K B⟩)
        (fun j => quotientColumn D (cols j) (hdiv j)) a M := by
  let S := coprimeSquarefreeIdealBall (quadraticMaskIdeal D) K
  let q := fun j => quotientColumn D (cols j) (hdiv j)
  let rows : S → QuadraticIdeal := fun B => ⟨B.val,coprimeSquarefreeIdealBall_admissible D K B⟩
  have ht (j k : n) :
      (if (cols j).val ⊔ (cols k).val = D then
        star (a j)*a k*(∑' H : Ideal O, originalPairLow (cols j) (cols k) W M K H) else 0) =
      (Nat.card Oˣ : ℂ)⁻¹ * ∑ B : S,
        originalTerm rows q q a a 1 1 B j k *
          ∑' z : O, rowCoprimeMask (fun P : primeSupport (quadraticMaskIdeal D*((q j).val*(q k).val)) => P.val) Finset.univ z *
            (if z=0 then 0 else quadraticSquareProfile W (‖ringComplex z‖^2/sourcePrincipalScale M B.val)) := by
    have heq := quadraticIdealQuotient_coprime_iff D (cols j).val (cols k).val hD (hdiv j) (hdiv k)
    by_cases hc : (q j).val ⊔ (q k).val = ⊤
    · rw [if_pos (heq.mp hc),originalPairLow_residual_finite D _ _ (hdiv j) (hdiv k) W M K hM]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro B _
      simp only [originalTerm,if_pos hc,one_dvd,ite_true,pairMaskedSquareSource,star_mul,
        canonicalQuadraticRow_star,rows,q]
      ring
    · have hg : ¬(cols j).val ⊔ (cols k).val = D := fun h => hc (heq.mpr h)
      simp only [if_neg hg,originalTerm,if_neg hc,zero_mul,Finset.sum_const_zero,mul_zero]
  simp_rw [ht,Finset.mul_sum]
  simp_rw [Finset.sum_comm (s := (Finset.univ : Finset n)) (t := (Finset.univ : Finset S))]
  simp only [maskedPrincipalSourceSum,Finset.mul_sum,rows,q]
  rfl

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson
open scoped SchwartzMap Classical

lemma primeSupportMask_generator_indicator (G H : Ideal O) (hG : G ≠ 0) :
    primeCoprimeMask cubicIdealGenerator (primeSupport G) (cubicIdealGenerator H) =
      if IsCoprime H G then 1 else 0 := by
  simp only [primeCoprimeMask_indicator,ideal_generator_dvd_iff,span_cubicIdealGenerator,
    ← ideal_coprime_support_iff H G hG]

/-- Extracting a common conductor gives the masked ideal kernel before Poisson summation. -/
theorem originalPairSource_residual (D : Ideal O) (I J : QuadraticIdeal)
    (hDI : D ∣ I.val) (hDJ : D ∣ J.val)
    (hray : quadraticColumnRay I = quadraticColumnRay J) (W : ℝ → ℂ) (M : ℝ) :
    (∑' H : Ideal O, originalPairSource I J W M H) =
      maskedPairIdealSourceKernel (quadraticMaskIdeal D)
        (quotientColumn D I hDI) (quotientColumn D J hDJ) W M := by
  have hD : D ≠ 0 := ne_zero_of_dvd_ne_zero (primaryIdealGenerator_ne_zero_ideal _ I.property.1) hDI
  have hqray := quadraticColumnRay_quotient_eq D I J hDI hDJ hray
  have ht (H : Ideal O) : originalPairSource I J W M H =
      primeCoprimeMask cubicIdealGenerator (primeSupport (quadraticMaskIdeal D)) (cubicIdealGenerator H) *
        canonicalQuadraticPairIdeal (quotientColumn D I hDI) (quotientColumn D J hDJ) H *
          W ((Ideal.absNorm H : ℝ)/M) := by
    rw [primeSupportMask_generator_indicator _ _ (quadraticMaskIdeal_squarefree D).ne_zero]
    by_cases hs : quadraticSupported H
    · rw [originalPairSource,if_pos hs,canonical_pair_divisor_mask D I J hDI hDJ,
        quadraticIdealMask_primary_commonMask _ _ hs,canonicalQuadraticPairIdeal_primary _ _ hqray H hs.1]
    · have hc : ¬ IsCoprime H (quadraticMaskIdeal D) :=
        fun hc => hs ((quadraticMask_coprime_iff D H hD).mp hc).1
      simp only [originalPairSource,if_neg hs,if_neg hc,zero_mul]
  have he : (∑' H : NonzeroIdeal, originalPairSource I J W M H.val) =
      ∑' H : Ideal O, originalPairSource I J W M H := by
    apply tsum_subtype_eq_of_support_subset
    intro H hH hz
    subst H
    have hs : ¬ quadraticSupported (0 : Ideal O) :=
      fun h => primaryIdealGenerator_ne_zero_ideal _ h.1 rfl
    exact hH (by simp only [originalPairSource,if_neg hs])
  rw [← he]
  exact tsum_congr (fun H => ht H.val)

theorem originalPairSource_poisson (D : Ideal O) (I J : QuadraticIdeal)
    (hDI : D ∣ I.val) (hDJ : D ∣ J.val) (hcommon : I.val ⊔ J.val = D)
    (hproper : I.val ≠ D) (hray : quadraticColumnRay I = quadraticColumnRay J)
    (W : 𝓢(ℝ,ℂ)) (M : ℝ) (hM : 0 < M) :
    (∑' H : Ideal O, originalPairSource I J W M H) =
      maskedPairIdealDualKernel (quadraticMaskIdeal D)
        (quotientColumn D I hDI) (quotientColumn D J hDJ) W M := by
  have hD : D ≠ 0 := ne_zero_of_dvd_ne_zero (primaryIdealGenerator_ne_zero_ideal _ I.property.1) hDI
  have hc : IsCoprime (quotientColumn D I hDI).val (quotientColumn D J hDJ).val := Ideal.isCoprime_iff_sup_eq.mpr
    ((quadraticIdealQuotient_coprime_iff D I.val J.val hD hDI hDJ).mpr hcommon)
  have hnt : (quotientColumn D I hDI).val ≠ 1 := by
    intro h
    have he := quadraticIdeal_mul_quotient hDI
    change D * (quotientColumn D I hDI).val = I.val at he
    rw [h,mul_one] at he
    exact hproper he.symm
  exact (originalPairSource_residual D I J hDI hDJ hray W M).trans
    (maskedPairIdealSourceKernel_poisson (quadraticMaskIdeal D) (quadraticMaskIdeal_squarefree D)
      (quotientColumn D I hDI) (quotientColumn D J hDJ) hc
      (quadraticColumnRay_quotient_eq D I J hDI hDJ hray) (Or.inl hnt) W M hM)

/-- The high squarefree-part block is precisely the dual-minus-principal Poisson difference. -/
theorem originalHigh_commonFactor_eq_maskedPoissonDifference {n : Type} [Fintype n]
    (D : Ideal O) (hD : D ≠ 0) (cols : n → QuadraticIdeal)
    (hdiv : ∀ j, D ∣ (cols j).val) (hproper : ∀ j, (cols j).val ≠ D)
    (hray : ∀ j k, quadraticColumnRay (cols j) = quadraticColumnRay (cols k))
    (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) (M K : ℝ) (hM : 0 < M) :
    (∑ j, ∑ k, if (cols j).val ⊔ (cols k).val = D then
      star (a j)*a k*(∑' H : Ideal O, originalPairHigh (cols j) (cols k) W M K H) else 0) =
      maskedPoissonDifference D W (fun j => quotientColumn D (cols j) (hdiv j)) a M K := by
  let q := fun j => quotientColumn D (cols j) (hdiv j)
  have ht (j k : n) :
      (if (cols j).val ⊔ (cols k).val = D then
        star (a j)*a k*(∑' H : Ideal O, originalPairHigh (cols j) (cols k) W M K H) else 0) =
      (if IsCoprime (q j).val (q k).val then
        star (a j)*a k*maskedPairIdealDualKernel (quadraticMaskIdeal D) (q j) (q k) W M else 0) -
      (if (cols j).val ⊔ (cols k).val = D then
        star (a j)*a k*(∑' H : Ideal O, originalPairLow (cols j) (cols k) W M K H) else 0) := by
    have heq : IsCoprime (q j).val (q k).val ↔ (cols j).val ⊔ (cols k).val = D :=
      Ideal.isCoprime_iff_sup_eq.trans
        (quadraticIdealQuotient_coprime_iff D (cols j).val (cols k).val hD (hdiv j) (hdiv k))
    by_cases hg : (cols j).val ⊔ (cols k).val = D
    · rw [if_pos hg,if_pos hg,if_pos (heq.mpr hg),
        originalPairHigh_eq_source_sub_low _ _ W M K hM,
        originalPairSource_poisson D _ _ (hdiv j) (hdiv k) hg (hproper j) (hray j k) W M hM]
      ring
    · simp only [if_neg hg,if_neg (fun hc => hg (heq.mp hc)),sub_self]
  simp_rw [ht,Finset.sum_sub_distrib]
  rw [originalLow_commonFactor_aggregate D hD cols hdiv a W M K hM]
  rfl

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory
open scoped SchwartzMap Classical

def commonFactorRaySupport {n : Type} [Fintype n] (cols : n → QuadraticIdeal) (a : n → ℂ)
    (D : Ideal O) (c : QuadraticRayRing) : Finset n :=
  Finset.univ.filter (fun j => D ∣ (cols j).val ∧ quadraticColumnRay (cols j) = c ∧ a j ≠ 0)

lemma mem_commonFactorRaySupport {n : Type} [Fintype n] (cols : n → QuadraticIdeal) (a : n → ℂ)
    (D : Ideal O) (c : QuadraticRayRing) (j : n) :
    j ∈ commonFactorRaySupport cols a D c ↔ D ∣ (cols j).val ∧ quadraticColumnRay (cols j) = c ∧ a j ≠ 0 := by
  simp only [commonFactorRaySupport,Finset.mem_filter,Finset.mem_univ,true_and]

lemma commonFactor_ray_pair_sum_restrict {n : Type} [Fintype n]
    (cols : n → QuadraticIdeal) (a : n → ℂ) (D : Ideal O) (c : QuadraticRayRing) (H : n → n → ℂ) :
    (∑ j, ∑ k, if (cols j).val ⊔ (cols k).val = D ∧ quadraticColumnRay (cols j) = c ∧ quadraticColumnRay (cols k) = c
      then star (a j)*a k*H j k else 0) =
    ∑ j : commonFactorRaySupport cols a D c, ∑ k : commonFactorRaySupport cols a D c,
      if (cols j.val).val ⊔ (cols k.val).val = D then star (a j.val)*a k.val*H j.val k.val else 0 := by
  let S := commonFactorRaySupport cols a D c
  let f := fun j k => if (cols j).val ⊔ (cols k).val = D ∧ quadraticColumnRay (cols j) = c ∧ quadraticColumnRay (cols k) = c
    then star (a j)*a k*H j k else 0
  have hjzero (j : n) (hj : j ∉ S) (k : n) : f j k = 0 := by
    dsimp only [f]
    split_ifs with h
    · have hz : a j = 0 := by
        by_contra hn
        apply hj
        exact (mem_commonFactorRaySupport cols a D c j).mpr
          ⟨h.1 ▸ Ideal.dvd_iff_le.mpr le_sup_left,h.2.1,hn⟩
      simp only [hz,star_zero,zero_mul]
    · rfl
  have hkzero (k : n) (hk : k ∉ S) (j : n) : f j k = 0 := by
    dsimp only [f]
    split_ifs with h
    · have hz : a k = 0 := by
        by_contra hn
        apply hk
        exact (mem_commonFactorRaySupport cols a D c k).mpr
          ⟨h.1 ▸ Ideal.dvd_iff_le.mpr le_sup_right,h.2.2,hn⟩
      simp only [hz,mul_zero,zero_mul]
    · rfl
  have hleft : (∑ j ∈ S, ∑ k, f j k) = ∑ j, ∑ k, f j k := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro j _ hj
    exact Finset.sum_eq_zero (fun k _ => hjzero j hj k)
  change (∑ j, ∑ k, f j k) = _
  rw [← hleft,← Finset.sum_coe_sort S (fun j => ∑ k, f j k)]
  apply Finset.sum_congr rfl
  intro j _
  have hright : (∑ k ∈ S, f j.val k) = ∑ k, f j.val k := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro k _ hk
    exact hkzero k hk j.val
  rw [← hright,← Finset.sum_coe_sort S (fun k => f j.val k)]
  apply Finset.sum_congr rfl
  intro k _
  have hj := (mem_commonFactorRaySupport cols a D c j.val).mp j.property
  have hk := (mem_commonFactorRaySupport cols a D c k.val).mp k.property
  simp only [f,hj.2.1,hk.2.1,and_true]

lemma commonFactorRaySupport_energy {n : Type} [Fintype n]
    (cols : n → QuadraticIdeal) (a : n → ℂ) (D : Ideal O) (c : QuadraticRayRing) :
    (∑ j : commonFactorRaySupport cols a D c, ‖a j.val‖ ^ 2) ≤ ∑ j, ‖a j‖ ^ 2 := by
  rw [Finset.sum_coe_sort (commonFactorRaySupport cols a D c) (fun j => ‖a j‖ ^ 2)]
  exact Finset.sum_le_univ_sum_of_nonneg (fun j => sq_nonneg ‖a j‖)

def activeCommonFactorColumns (N : ℝ) (a : QuadraticIdealRange N → ℂ) (D : Ideal O) (c : QuadraticRayRing) :
    commonFactorRaySupport (fun I : QuadraticIdealRange N => I.val) a D c → QuadraticIdeal :=
  fun j => quotientColumn D j.val.val ((mem_commonFactorRaySupport _ a D c j.val).mp j.property).1

def activeCommonFactorCoefficient (N : ℝ) (a : QuadraticIdealRange N → ℂ) (D : Ideal O) (c : QuadraticRayRing) :
    commonFactorRaySupport (fun I : QuadraticIdealRange N => I.val) a D c → ℂ := fun j => a j.val

theorem commonFactorRaySupport_quotient_properties (N X : ℝ) (a : QuadraticIdealRange N → ℂ)
    (ha : CoefficientOnShell N X a) (D : Ideal O) (hD : D ≠ 0) (c : QuadraticRayRing) :
    let cols := activeCommonFactorColumns N a D c
    Function.Injective cols ∧
    (∀ j, (X/(Ideal.absNorm D : ℝ))/2 ≤ (Ideal.absNorm (cols j).val : ℝ) ∧
      (Ideal.absNorm (cols j).val : ℝ) ≤ X/(Ideal.absNorm D : ℝ) ∧
      IsCoprime (quadraticMaskIdeal D) (cols j).val) ∧
    (∀ j k, quadraticColumnRay (cols j) = quadraticColumnRay (cols k)) := by
  dsimp only
  have hp (j : commonFactorRaySupport (fun I : QuadraticIdealRange N => I.val) a D c) :=
    (mem_commonFactorRaySupport (fun I : QuadraticIdealRange N => I.val) a D c j.val).mp j.property
  refine ⟨?_,?_,?_⟩
  · intro j k hjk
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    exact quadraticIdealQuotient_injective D (hp j).1 (hp k).1 (congrArg Subtype.val hjk)
  · intro j
    have hshell := quadraticIdealQuotient_shell D j.val.val.val hD (hp j).1 X
      ⟨(ha j.val (hp j).2.2).1.le,(ha j.val (hp j).2.2).2⟩
    exact ⟨hshell.1,hshell.2,residual_quadraticMask_coprime D j.val.val (hp j).1⟩
  · intro j k
    exact quadraticColumnRay_quotient_eq D j.val.val k.val.val (hp j).1 (hp k).1
      ((hp j).2.1.trans (hp k).2.1.symm)

lemma commonFactorRaySupport_proper (N X : ℝ) (a : QuadraticIdealRange N → ℂ)
    (ha : CoefficientOnShell N X a) (D : Ideal O) (c : QuadraticRayRing)
    (hsmall : (Ideal.absNorm D : ℝ) ≤ X/2)
    (j : commonFactorRaySupport (fun I : QuadraticIdealRange N => I.val) a D c) : j.val.val.val ≠ D := by
  intro h
  have hp := (mem_commonFactorRaySupport (fun I : QuadraticIdealRange N => I.val) a D c j.val).mp j.property
  have hs := (ha j.val hp.2.2).1
  rw [h] at hs
  exact (not_lt_of_ge hsmall) hs

theorem annularRayCommonFactorBlock_eq_active_difference (M N X K : ℝ) (hM : 0  <  M)
    (a : QuadraticIdealRange N → ℂ) (ha : CoefficientOnShell N X a)
    (D : Ideal O) (hD : D ≠ 0) (hsmall : (Ideal.absNorm D : ℝ) ≤ X/2) (c : QuadraticRayRing) :
    annularRayCommonFactorBlock M N K D c a =
      maskedPoissonDifference D annularSieveCutoff
        (activeCommonFactorColumns N a D c) (activeCommonFactorCoefficient N a D c) M K := by
  rw [annularRayCommonFactorBlock_eq_pair_high M N K hM D c a]
  simp only [ite_mul,zero_mul]
  rw [commonFactor_ray_pair_sum_restrict]
  let S := commonFactorRaySupport (fun I : QuadraticIdealRange N => I.val) a D c
  have hdiv (j : S) : D ∣ j.val.val.val :=
    ((mem_commonFactorRaySupport _ a D c j.val).mp j.property).1
  have hray (j k : S) : quadraticColumnRay j.val.val = quadraticColumnRay k.val.val := by
    have hj := ((mem_commonFactorRaySupport _ a D c j.val).mp j.property).2.1
    have hk := ((mem_commonFactorRaySupport _ a D c k.val).mp k.property).2.1
    exact hj.trans hk.symm
  exact originalHigh_commonFactor_eq_maskedPoissonDifference D hD
    (fun j : S => j.val.val) hdiv (commonFactorRaySupport_proper N X a ha D c hsmall)
    hray (fun j : S => a j.val) annularSieveCutoff M K hM

theorem HasSieveExponent.annular_small_commonFactor_complete {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0  <  deltaLoss) (l A : ℕ) :
    ∃ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ),
      0  <  CD ∧ 0  <  CS ∧ 0  <  CT ∧ 0  <  CP ∧
      ∀ (ε : ℝ) (hε : 0  <  ε) (M N X K T : ℝ), 1 ≤ M → 1 ≤ K → 4 ≤ T →
      ∀ (a : QuadraticIdealRange N → ℂ), CoefficientOnShell N X a →
      ∀ (D : Ideal O), D ≠ 0 → (Ideal.absNorm D : ℝ) ≤ X/2 →
      ∀ (c : QuadraticRayRing),
        ‖(Nat.card Oˣ : ℂ)*annularRayCommonFactorBlock M N K D c a‖ ≤ 
          poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε
            (quadraticMaskIdeal D) K (X/(Ideal.absNorm D : ℝ)) M T
            (activeCommonFactorCoefficient N a D c) annularSieveCutoff := by
  obtain ⟨sD,sS,sT,CD,CS,CT,CP,hCD,hCS,hCT,hCP,hbound⟩ :=
    hexp.masked_poisson_complete hα deltaLoss hδ l A
  refine ⟨sD,sS,sT,CD,CS,CT,CP,hCD,hCS,hCT,hCP,?_⟩
  intro ε hε M N X K T hM hK hT a ha D hD hsmall c
  have hDn : 0  <  (Ideal.absNorm D : ℝ) := by
    exact_mod_cast Nat.pos_iff_ne_zero.mpr (fun hz => hD (Ideal.absNorm_eq_zero_iff.mp hz))
  have hscale : 1 ≤ X/(Ideal.absNorm D : ℝ) := (le_div_iff₀ hDn).mpr (by linarith)
  have hp := commonFactorRaySupport_quotient_properties N X a ha D hD c
  rw [annularRayCommonFactorBlock_eq_active_difference M N X K (by linarith) a ha D hD hsmall c]
  exact hbound ε hε D K (X/(Ideal.absNorm D : ℝ)) M T hK hscale hM hT
    (activeCommonFactorColumns N a D c) hp.1 (fun j => ⟨(hp.2.1 j).1,(hp.2.1 j).2.1⟩)
    hp.2.2 (fun j => (hp.2.1 j).2.2) (activeCommonFactorCoefficient N a D c)
    annularSieveCutoff annularSieveCutoff_zero

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein
open scoped Classical

def selectedPoissonT (C M X η : ℝ) : ℝ := C*(M*X) ^ η
def selectedPoissonK (C M X η : ℝ) : ℝ := selectedPoissonT C M X η*X ^ 2/M

theorem selectedPoisson_bounds (C M X η : ℝ)
    (hC : 4 ≤ C) (hM : 1 ≤ M) (hX : 1 ≤ X) (hMX : M ≤ X ^ 2) (hη : 0 ≤ η) :
    4 ≤ selectedPoissonT C M X η ∧ 1 ≤ selectedPoissonK C M X η ∧
      selectedPoissonK C M X η ≤ C*(M*X) ^ (η+2) := by
  have hM0 : 0 < M := by linarith
  have hX0 : 0 < X := by linarith
  have hprod : 1 ≤ M*X := by nlinarith
  have hpow : 1 ≤ (M*X) ^ η := Real.one_le_rpow hprod hη
  have hT : 4 ≤ selectedPoissonT C M X η := by
    unfold selectedPoissonT
    nlinarith
  have hfrac : 1 ≤ X ^ 2/M := (le_div_iff₀ hM0).mpr (by simpa using hMX)
  have hK : 1 ≤ selectedPoissonK C M X η := by
    unfold selectedPoissonK
    rw [mul_div_assoc]
    nlinarith
  refine ⟨hT,hK,?_⟩
  have hXprod : X ≤ M*X := by nlinarith
  have hfracup : X ^ 2/M ≤ (M*X) ^ 2 :=
    (div_le_self (sq_nonneg X) hM).trans (pow_le_pow_left₀ hX0.le hXprod 2)
  unfold selectedPoissonK selectedPoissonT
  rw [mul_div_assoc,Real.rpow_add (by positivity : 0 < M*X),Real.rpow_two]
  calc
    _ ≤ (C*(M*X) ^ η)*(M*X) ^ 2 := mul_le_mul_of_nonneg_left hfracup (by positivity)
    _ = _ := by ring

theorem selectedPoisson_radial_identity (C B M X q η : ℝ)
    (hM : 0 < M) (hX : 0 < X) (hq : 0 < q) (hB : 0 < B) :
    (M/((B*q)*(X/q)*(X/q)))*selectedPoissonK C M X η =
      selectedPoissonT C M X η*q/B := by
  unfold selectedPoissonK
  field_simp

theorem cutoff_middle_identity (M X T α : ℝ) (hM : 0 < M) (hX : 0 < X) (hT : 0 < T) :
    T*Real.sqrt M*(T*X ^ 2/M) ^ (α-1/2) =
      T ^ (α+1/2)*X ^ (2*α-1)*M ^ (1-α) := by
  rw [Real.div_rpow (by positivity : 0 ≤ T*X ^ 2) hM.le,
    Real.mul_rpow hT.le (sq_nonneg X),←Real.rpow_two,←Real.rpow_mul hX.le]
  have hx : 2*(α-1/2)=2*α-1 := by ring
  have hm : 1-α=1/2-(α-1/2) := by ring
  have ht : α+1/2=1+(α-1/2) := by ring
  have hmPow : M ^ (1-α)=M ^ (1/2:ℝ)/M ^ (α-1/2) := by
    calc
      _ = M ^ ((1/2:ℝ)-(α-1/2)) := by rw [hm]
      _ = _ := Real.rpow_sub hM _ _
  have htPow : T ^ (α+1/2)=T*T ^ (α-1/2) := by
    calc
      _ = T ^ (1+(α-1/2)) := by rw [ht]
      _ = _ := by rw [Real.rpow_add hT,Real.rpow_one]
  rw [hx,hmPow,htPow,Real.sqrt_eq_rpow]
  ring

theorem selectedPoisson_middle_bound (C M X η α : ℝ)
    (hC : 4 ≤ C) (hM : 1 ≤ M) (hX : 1 ≤ X) (hη : 0 ≤ η) (hα : α ≤ 2) :
    selectedPoissonT C M X η*Real.sqrt M*(2*selectedPoissonK C M X η) ^ (α-1/2) ≤ 
      4*C ^ 3*(M*X) ^ (3*η)*(X ^ (2*α-1)*M ^ (1-α)) := by
  have hM0 : 0 < M := by linarith
  have hX0 : 0 < X := by linarith
  have hP : 0 < M*X := by positivity
  have hP1 : 1 ≤ M*X := by nlinarith
  have hpow : 1 ≤ (M*X) ^ η := Real.one_le_rpow hP1 hη
  have hT : 1 ≤ selectedPoissonT C M X η := by unfold selectedPoissonT; nlinarith
  have hT0 : 0 < selectedPoissonT C M X η := by linarith
  have hK0 : 0 < selectedPoissonK C M X η := by unfold selectedPoissonK; positivity
  have htwo : (2:ℝ) ^ (α-1/2) ≤ 4 := by
    calc
      _ ≤ (2:ℝ) ^ (2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := by norm_num
  have hp3 : ((M*X) ^ η) ^ 3 = (M*X) ^ (3*η) := by
    rw [←Real.rpow_natCast,←Real.rpow_mul hP.le]
    congr 1
    ring
  have hT3 : (selectedPoissonT C M X η) ^ (α+1/2) ≤ C ^ 3*(M*X) ^ (3*η) := by
    calc
      _ ≤ (selectedPoissonT C M X η) ^ (3:ℝ) := Real.rpow_le_rpow_of_exponent_le hT (by linarith)
      _ = C ^ 3*(M*X) ^ (3*η) := by norm_num only [selectedPoissonT,Real.rpow_ofNat,mul_pow,hp3]
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hK0.le]
  calc
    _ ≤ 4*(selectedPoissonT C M X η*Real.sqrt M*(selectedPoissonK C M X η) ^ (α-1/2)) := by
      have hh := mul_le_mul_of_nonneg_right htwo
        (show 0 ≤ selectedPoissonT C M X η*Real.sqrt M*(selectedPoissonK C M X η) ^ (α-1/2) by positivity)
      nlinarith [hh]
    _ = 4*((selectedPoissonT C M X η) ^ (α+1/2)*X ^ (2*α-1)*M ^ (1-α)) := by
      rw [selectedPoissonK,cutoff_middle_identity M X _ α hM0 hX0 hT0]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_right hT3
        (show 0 ≤ X ^ (2*α-1)*M ^ (1-α) by positivity)
      nlinarith [hh]


def cutoffRescaleCoefficient (C η r q : ℝ) : ℝ := C*r*q ^ 2/(r/q) ^ η

theorem cutoffRescaleCoefficient_eq (C η r q : ℝ) (hr : 0 < r) (hq : 0 < q) :
    cutoffRescaleCoefficient C η r q=C*r ^ (1-η)*q ^ (2+η) := by
  rw [cutoffRescaleCoefficient,Real.div_rpow hr.le hq.le,
    Real.rpow_sub hr,Real.rpow_one,Real.rpow_add hq,Real.rpow_two]
  have hrp : r ^ η≠0 := (Real.rpow_pos_of_pos hr η).ne'
  have hqp : q ^ η≠0 := (Real.rpow_pos_of_pos hq η).ne'
  field_simp

theorem cutoffRescaleCoefficient_bounds (C η r q : ℝ)
    (hC : 0 ≤ C) (hη : 0 ≤ η) (hη1 : η ≤ 1) (hr : 1 ≤ r) (hr64 : r ≤ 64) (hq : 1 ≤ q) (hq7 : q ≤ 7) :
    C ≤ cutoffRescaleCoefficient C η r q ∧ cutoffRescaleCoefficient C η r q ≤ 21952*C := by
  rw [cutoffRescaleCoefficient_eq C η r q (by linarith) (by linarith)]
  have hrlo : 1 ≤ r ^ (1-η) := Real.one_le_rpow hr (by linarith)
  have hqlo : 1 ≤ q ^ (2+η) := Real.one_le_rpow hq (by linarith)
  have hrup : r ^ (1-η) ≤ r := by
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hr (show 1-η ≤ 1 by linarith)
  have hqup : q ^ (2+η) ≤ q ^ 3 := by
    simpa only [Real.rpow_ofNat] using Real.rpow_le_rpow_of_exponent_le hq (show 2+η ≤ (3:ℝ) by linarith)
  constructor
  · calc
      C = C*1*1 := by ring
      _ ≤ _ := by gcongr
  · calc
      _ ≤ C*r*q ^ 3 := by gcongr
      _ ≤ C*64*7 ^ 3 := by gcongr
      _ = _ := by ring

theorem selectedPoissonK_rescale (C M X η r q : ℝ)
    (hM : 0 < M) (hX : 0 < X) (hr : 0 < r) (hq : 0 < q) :
    selectedPoissonK (cutoffRescaleCoefficient C η r q) (r*M) (X/q) η =
      selectedPoissonK C M X η := by
  unfold selectedPoissonK selectedPoissonT cutoffRescaleCoefficient
  have he : (r*M)*(X/q)=(r/q)*(M*X) := by ring
  rw [he,Real.mul_rpow (by positivity : 0 ≤ r/q) (by positivity : 0 ≤ M*X)]
  have hp : (r/q) ^ η≠0 := (Real.rpow_pos_of_pos (by positivity) η).ne'
  field_simp


def largeCommonFactorThreshold (α N : ℝ) : ℝ := N ^ (1-1/α)

theorem largeCommonFactorThreshold_quotient_power (α N : ℝ) (hα : α≠0) (hN : 0 < N) :
    (N/largeCommonFactorThreshold α N) ^ α=N := by
  have he : N/largeCommonFactorThreshold α N=N ^ (1/α) := by
    rw [show 1/α=1-(1-1/α) by ring,Real.rpow_sub hN,Real.rpow_one]
    rfl
  rw [he,←Real.rpow_mul hN.le]
  field_simp
  rw [Real.rpow_one]

theorem largeCommonFactorThreshold_bounds (α N : ℝ) (hα1 : 1 ≤ α) (hα2 : α ≤ 2) (hN : 4 ≤ N) :
    1 ≤ largeCommonFactorThreshold α N ∧ largeCommonFactorThreshold α N ≤ N/2 := by
  have hα : 0 < α := by linarith
  have hN0 : 0 < N := by linarith
  have ha : 0 ≤ 1-1/α := by
    have hi : 1/α ≤ 1 := (div_le_one hα).mpr hα1
    linarith
  have hb : 1-1/α ≤ (1/2:ℝ) := by
    have hi : (1/2:ℝ) ≤ 1/α := (le_div_iff₀ hα).mpr (by linarith)
    linarith
  refine ⟨Real.one_le_rpow (by linarith) ha,?_⟩
  calc
    largeCommonFactorThreshold α N ≤ N ^ (1/2:ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) hb
    _ = Real.sqrt N := (Real.sqrt_eq_rpow N).symm
    _ ≤ N/2 := (Real.sqrt_le_iff).mpr ⟨by positivity,by nlinarith⟩

theorem high_kernel_chosen_scale (M N K : ℝ) (hM : 0 < M) (_hN : 0 < N) (hK : 0 < K)
    (hcut : N ^ 2/M ≤ K) : Real.sqrt ((2*M)/K)*N ≤ 2*M := by
  have hNK : N ^ 2 ≤ M*K := by
    have h := (div_le_iff₀ hM).mp hcut
    nlinarith
  let s := Real.sqrt ((2*M)/K)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs : s ^ 2*K=2*M := by
    dsimp only [s]
    rw [Real.sq_sqrt (by positivity),div_mul_cancel₀ _ hK.ne']
  have hb : s ^ 2*N ^ 2 ≤ 2*M ^ 2 := by
    calc
      _ ≤ s ^ 2*(M*K) := mul_le_mul_of_nonneg_left hNK (sq_nonneg s)
      _ = (s ^ 2*K)*M := by ring
      _ = _ := by rw [hs]; ring
  change s*N ≤ 2*M
  nlinarith [sq_nonneg (s*N)]

theorem chosen_large_commonFactor_main (α M N K : ℝ) (hα : α≠0)
    (hM : 0 < M) (hN : 0 < N) (hK : 0 < K) (hcut : N ^ 2/M ≤ K) :
    2*M+Real.sqrt ((2*M)/K)*(N/largeCommonFactorThreshold α N) ^ α ≤ 4*M := by
  rw [largeCommonFactorThreshold_quotient_power α N hα hN]
  linarith [high_kernel_chosen_scale M N K hM hN hK hcut]

theorem chosen_large_commonFactor_full (α deltaLoss C M N K : ℝ) (hα1 : 1 ≤ α) (hα2 : α ≤ 2)
    (hδ : 0 ≤ deltaLoss) (hC : 0 ≤ C) (hM : 0 < M) (hN : 4 ≤ N) (hK : 0 < K)
    (hcut : N ^ 2/M ≤ K) :
    C*((2*M)*(N/largeCommonFactorThreshold α N)) ^ deltaLoss*
      (2*M+Real.sqrt ((2*M)/K)*(N/largeCommonFactorThreshold α N) ^ α) ≤ 
        (4*C*2 ^ deltaLoss)*(M*N) ^ deltaLoss*M := by
  have hh := largeCommonFactorThreshold_bounds α N hα1 hα2 hN
  have hH : 0 < largeCommonFactorThreshold α N := by linarith
  have hN0 : 0 < N := by linarith
  have hp : ((2*M)*(N/largeCommonFactorThreshold α N)) ^ deltaLoss ≤ (2*(M*N)) ^ deltaLoss := by
    apply Real.rpow_le_rpow (by positivity) _ hδ
    have hn := div_le_self hN0.le hh.1
    nlinarith
  have hm := chosen_large_commonFactor_main α M N K (by linarith) hM hN0 hK hcut
  calc
    _ ≤ C*(2*(M*N)) ^ deltaLoss*(4*M) := by gcongr
    _ = _ := by rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (by positivity)]; ring


end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson DivisorBlockCauchy
open scoped SchwartzMap Classical

theorem commonFactorRaySupport_energy_eq {n : Type} [Fintype n]
    (cols : n → QuadraticIdeal) (a : n → ℂ) (D : Ideal O) (c : QuadraticRayRing) :
    (∑j : commonFactorRaySupport cols a D c, ‖a j.val‖ ^ 2) =
      ∑j, if D ∣ (cols j).val ∧ quadraticColumnRay (cols j)=c then ‖a j‖ ^ 2 else 0 := by
  classical
  rw [Finset.sum_coe_sort (commonFactorRaySupport cols a D c) (fun j => ‖a j‖ ^ 2)]
  simp only [commonFactorRaySupport,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hz : a j=0
  · simp only [hz,norm_zero,ne_eq,not_true_eq_false,and_false,ite_self,zero_pow (by decide : 2≠0)]
  · simp only [hz,ne_eq,not_false_eq_true,and_true]

theorem commonFactorRaySupport_energy_ray_sum {n : Type} [Fintype n]
    (cols : n → QuadraticIdeal) (a : n → ℂ) (D : Ideal O) :
    (∑c : QuadraticRayRing, ∑j : commonFactorRaySupport cols a D c, ‖a j.val‖ ^ 2) =
      ∑j, ‖if D ∣ (cols j).val then a j else 0‖ ^ 2 := by
  classical
  simp_rw [commonFactorRaySupport_energy_eq]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hd : D ∣ (cols j).val
  · simp only [hd,true_and,ite_true]
    rw [Finset.sum_eq_single (quadraticColumnRay (cols j))]
    · simp only [ite_true]
    · intro c hc hne
      exact if_neg (Ne.symm hne)
    · simp
  · simp only [hd,false_and,ite_false,Finset.sum_const_zero,norm_zero,zero_pow (by decide : 2≠0)]

theorem commonFactorRaySupport_energy_divisor_sum {n : Type} [Fintype n]
    (ε : ℝ) (hε : 0 < ε) (S : Finset (Ideal O)) (cols : n → QuadraticIdeal)
    (hcols : ∀j, (cols j).val ≠ 0) (a : n → ℂ) (X : ℝ)
    (hX : ∀j, a j≠0 → (Ideal.absNorm (cols j).val:ℝ) ≤ X) :
    (∑c : QuadraticRayRing, ∑D∈S,
      ∑j : commonFactorRaySupport cols a D c, ‖a j.val‖ ^ 2) ≤ 
      (divisorConstant ε hε*X ^ ε)*∑j, ‖a j‖ ^ 2 := by
  classical
  rw [Finset.sum_comm]
  simp_rw [commonFactorRaySupport_energy_ray_sum]
  apply (divisor_mask_energy S (fun j => (cols j).val) hcols a).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  by_cases hz : a j=0
  · simp only [hz,norm_zero,zero_pow (by decide : 2≠0),mul_zero,le_refl]
  · apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    apply ((IdealDivisorBound.ideal_divisor_small_power ε hε).choose_spec.2 (cols j).val (hcols j)).trans
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (hX j hz) hε.le) (divisorConstant_pos ε hε).le

theorem commonFactorRaySupport_weighted_sum_bound {n : Type} [Fintype n]
    (ε : ℝ) (hε : 0 < ε) (S : Finset (Ideal O)) (cols : n → QuadraticIdeal)
    (hcols : ∀j, (cols j).val ≠ 0) (a : n → ℂ) (X C : ℝ) (hC : 0 ≤ C)
    (hX : ∀j, a j≠0 → (Ideal.absNorm (cols j).val:ℝ) ≤ X)
    (F : Ideal O → QuadraticRayRing → ℝ)
    (hF : ∀D∈S, ∀c, F D c ≤ C*∑j : commonFactorRaySupport cols a D c, ‖a j.val‖ ^ 2) :
    (∑c : QuadraticRayRing, ∑D∈S, F D c) ≤ 
      C*(divisorConstant ε hε*X ^ ε)*∑j, ‖a j‖ ^ 2 := by
  calc
    _ ≤ ∑c : QuadraticRayRing, ∑D∈S,
        C*∑j : commonFactorRaySupport cols a D c, ‖a j.val‖ ^ 2 :=
      Finset.sum_le_sum (fun c _ => Finset.sum_le_sum (fun D hD => hF D hD c))
    _ = C*(∑c : QuadraticRayRing, ∑D∈S,
        ∑j : commonFactorRaySupport cols a D c, ‖a j.val‖ ^ 2) := by simp only [Finset.mul_sum]
    _ ≤ C*((divisorConstant ε hε*X ^ ε)*∑j, ‖a j‖ ^ 2) :=
      mul_le_mul_of_nonneg_left (commonFactorRaySupport_energy_divisor_sum ε hε S cols hcols a X hX) hC
    _ = _ := by ring


theorem divisorEnergyFactor_diagonal {n : Type*} [Fintype n]
    (ε : ℝ) (hε : 0 < ε) (N : ℝ) (a : n → ℂ) :
    divisorEnergyFactor ε hε N a a =
      ((2*diagonalControl sieveCutoff)*(divisorConstant ε hε*N ^ ε) ^ 2)*∑j, ‖a j‖ ^ 2 := by
  unfold divisorEnergyFactor
  have hs : 0 ≤ ∑j, ‖a j‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  rw [mul_assoc _ (Real.sqrt _) (Real.sqrt _),Real.mul_self_sqrt hs]

theorem poissonComparisonMajorant_energy_factor {n : Type} [Fintype n]
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ) (l A : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (G : Ideal O) (K N M T : ℝ) (a : n → ℂ) (W : 𝓢(ℝ,ℂ)) :
    poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T a W =
      poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T
        (fun _ : Unit => (1:ℂ)) W * ∑j, ‖a j‖ ^ 2 := by
  unfold poissonComparisonMajorant retainedDualMajorant sourcePrincipalMajorant
    smallPrincipalMajorant dualMiddleMajorant
  simp only [divisorEnergyFactor_diagonal,Fintype.sum_unique,norm_one,one_pow,mul_one]
  ring


end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory DivisorBlockCauchy
open scoped SchwartzMap Classical

/-- Summing the small common-conductor bounds and the large-conductor sieve cost controls an annulus. -/
theorem HasSieveExponent.annular_energy_from_scalar_cost {α : ℝ} (hexp : HasSieveExponent α)
    (hα : 1/2 ≤ α) (deltaLoss : ℝ) (hδ : 0  <  deltaLoss) (l A : ℕ) :
    ∃ (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP CH : ℝ),
      0  <  CD ∧ 0  <  CS ∧ 0  <  CT ∧ 0  <  CP ∧ 0  <  CH ∧
      ∀ (ε : ℝ) (hε : 0  <  ε) (M N K T H C : ℝ),
      1 ≤ M → 1 ≤ N → 1 ≤ K → 4 ≤ T → 0  <  H → H ≤ N/2 → 0 ≤ C →
      (∀ D ∈ commonFactorPool (fun J : QuadraticIdealRange N => J.val), (Ideal.absNorm D : ℝ) ≤ H →
        poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε
          (quadraticMaskIdeal D) K (N/(Ideal.absNorm D : ℝ)) M T
          (fun _ : Unit => (1 : ℂ)) annularSieveCutoff ≤ C) →
      ∀ (a : QuadraticIdealRange N → ℂ), CoefficientOnShell N N a →
      annularHighEnergy M N K a ≤ 
        16*((C/(Nat.card Oˣ : ℝ))*(divisorConstant ε hε*N ^ ε) +
          (CH*((2*M)*(N/H)) ^ deltaLoss*(2*M+Real.sqrt ((2*M)/K)*(N/H) ^ α))*
            (divisorConstant ε hε*N ^ ε) ^ 2)*∑ J, ‖a J‖ ^ 2 := by
  obtain ⟨sD,sS,sT,CD,CS,CT,CP,hCD,hCS,hCT,hCP,hsmall⟩ :=
    hexp.annular_small_commonFactor_complete hα deltaLoss hδ l A
  obtain ⟨CH,hCH,hhigh⟩ := hexp.high_kernel deltaLoss hδ
  refine ⟨sD,sS,sT,CD,CS,CT,CP,CH,hCD,hCS,hCT,hCP,hCH,?_⟩
  intro ε hε M N K T H C hM hN hK hT hH hHN hC hcost a ha
  have huc : 0  <  (Nat.card Oˣ : ℝ) := by
    have hn : Nat.card Oˣ ≠ 0 := by
      intro h
      exact eisenstein_unit_card_ne_zero (by rw [h]; norm_num)
    exact_mod_cast Nat.pos_iff_ne_zero.mpr hn
  let S := (commonFactorPool (fun J : QuadraticIdealRange N => J.val)).filter (fun D => (Ideal.absNorm D : ℝ) ≤ H)
  have hb (D : Ideal O) (hD : D ∈ S) (c : QuadraticRayRing) :
      ‖annularRayCommonFactorBlock M N K D c a‖ ≤ 
        (C/(Nat.card Oˣ : ℝ))*∑ j : commonFactorRaySupport (fun I : QuadraticIdealRange N => I.val) a D c, ‖a j.val‖ ^ 2 := by
    have hd := Finset.mem_filter.mp hD
    have hadm := commonFactorPool_admissible (fun J : QuadraticIdealRange N => J.val) D hd.1
    have hh := hsmall ε hε M N N K T hM hK hT a ha D
      (primaryIdealGenerator_ne_zero_ideal D hadm.1) (hd.2.trans hHN) c
    rw [poissonComparisonMajorant_energy_factor,norm_mul,Complex.norm_natCast] at hh
    have hbound := mul_le_mul_of_nonneg_right (hcost D hd.1 hd.2)
      (show 0 ≤ ∑ j : commonFactorRaySupport (fun I : QuadraticIdealRange N => I.val) a D c, ‖a j.val‖ ^ 2 by positivity)
    change _ ≤ C*(∑ j : commonFactorRaySupport (fun I : QuadraticIdealRange N => I.val) a D c, ‖a j.val‖ ^ 2) at hbound
    have he := hh.trans hbound
    calc
      _ ≤ (C*(∑ j : commonFactorRaySupport (fun I : QuadraticIdealRange N => I.val) a D c, ‖a j.val‖ ^ 2))/(Nat.card Oˣ : ℝ) :=
        (le_div_iff₀ huc).mpr (by simpa only [mul_comm] using he)
      _ = _ := by ring
  have hs := commonFactorRaySupport_weighted_sum_bound ε hε S (fun J : QuadraticIdealRange N => J.val)
    (fun J => primaryIdealGenerator_ne_zero_ideal _ J.val.property.1) a N (C/(Nat.card Oˣ : ℝ)) (by positivity)
    (fun J _ => J.property) (fun D c => ‖annularRayCommonFactorBlock M N K D c a‖) hb
  have hNH : 1 ≤ N/H := (le_div_iff₀ hH).mpr (by linarith)
  have hh := hhigh (2*M) (N/H) K (by linarith) hNH hK
  have hred := annularHighEnergy_commonFactor_reduction M N K H hN hH ε hε a
  apply hred.trans
  have hdiv := (divisorConstant_pos ε hε).le
  calc
    _ ≤ 16*((C/(Nat.card Oˣ : ℝ))*(divisorConstant ε hε*N ^ ε)*∑ J, ‖a J‖ ^ 2 +
      (CH*((2*M)*(N/H)) ^ deltaLoss*(2*M+Real.sqrt ((2*M)/K)*(N/H) ^ α))*
        (divisorConstant ε hε*N ^ ε) ^ 2*∑ J, ‖a J‖ ^ 2) := by
      gcongr
    _ = _ := by ring

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory TruncatedPrincipalPoisson DivisorBlockCauchy
open scoped SchwartzMap Classical

theorem list_prod_le_power (xs : List ℝ) (U : ℝ) (hU : 0 ≤ U)
    (hxs : ∀x∈xs, 0 ≤ x ∧ x ≤ U) : xs.prod ≤ U ^ xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have hx := hxs x (by simp)
    have ht : ∀y∈xs, 0 ≤ y ∧ y ≤ U := fun y hy => hxs y (by simp [hy])
    simp only [List.prod_cons,List.length_cons,pow_succ]
    have hp : 0 ≤ xs.prod := List.prod_nonneg (fun y hy => (ht y hy).1)
    exact (mul_le_mul hx.2 (ih ht) hp hU).trans_eq (mul_comm _ _)

theorem list_prod_budget (xs budget : List ℝ) (U : ℝ) (hU : 1 ≤ U)
    (hbudget : ∀x∈budget, 0 ≤ x ∧ x ≤ U) (hxs : ∀x∈xs, x∈budget) (hlen : xs.length ≤ 8) :
    xs.prod ≤ U ^ 8 := by
  apply (list_prod_le_power xs U (by linarith) (fun x hx => hbudget x (hxs x hx))).trans
  exact pow_le_pow_right₀ hU hlen

theorem poisson_nine_terms_box
    (d lk ln f e vh vz dv uh du lat cd cs ct cp M N T a b eD eS tail U S : ℝ)
    (hU : 1 ≤ U) (hS : 0 ≤ S)
    (hbudget : ∀x∈([d,lk,ln,f,e,vh,vz,dv,uh,du,lat,cd,cs,ct,cp] : List ℝ), 0 ≤ x ∧ x ≤ U)
    (hM : 0 ≤ M) (hN : 0 ≤ N) (hT : 1 ≤ T) (ha : 0 ≤ a)
    (hMS : M ≤ S) (hNS : N ≤ S) (hTa : T*a ≤ S)
    (hb : 0 ≤ b ∧ b ≤ S) (hED : 0 ≤ eD ∧ eD ≤ S) (hES : 0 ≤ eS ∧ eS ≤ S)
    (htail : 0 ≤ tail ∧ tail ≤ S) :
    d*lk*(2*vh*ln ^ 2*f*e*(M+a) + 2*vz*ln ^ 2*f*e*(M+2*T*a) +
      2*ln ^ 2*lat*dv*f*e*(M+2*T*a) + 4*cd*eD) +
    d*ct*tail +
    lk*(2*uh*d*ln ^ 2*f*e*(4*N/T+a) + 2*d*ln ^ 2*lat*du*f*e*(N+2*T*a) +
      2*cs*eS) + uh*d ^ 2*cp*b ≤ 262144*U ^ 8*S := by
  let budget : List ℝ := [d,lk,ln,f,e,vh,vz,dv,uh,du,lat,cd,cs,ct,cp]
  have hp (xs : List ℝ) (hx : ∀x∈xs, x∈budget) (hn : xs.length ≤ 8) : xs.prod ≤ U ^ 8 :=
    list_prod_budget xs budget U hU hbudget hx hn
  have hc1 : d*lk*vh*ln ^ 2*f*e ≤ U ^ 8 := by
    have hh := hp [d,lk,vh,ln,ln,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc2 : d*lk*vz*ln ^ 2*f*e ≤ U ^ 8 := by
    have hh := hp [d,lk,vz,ln,ln,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc3 : d*lk*ln ^ 2*lat*dv*f*e ≤ U ^ 8 := by
    have hh := hp [d,lk,ln,ln,lat,dv,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc4 : d*lk*cd ≤ U ^ 8 := by
    have hh := hp [d,lk,cd] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,mul_assoc] using hh
  have hc5 : d*ct ≤ U ^ 8 := by
    have hh := hp [d,ct] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,mul_assoc] using hh
  have hc6 : lk*uh*d*ln ^ 2*f*e ≤ U ^ 8 := by
    have hh := hp [lk,uh,d,ln,ln,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc7 : lk*d*ln ^ 2*lat*du*f*e ≤ U ^ 8 := by
    have hh := hp [lk,d,ln,ln,lat,du,f,e] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have hc8 : lk*cs ≤ U ^ 8 := by
    have hh := hp [lk,cs] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,mul_assoc] using hh
  have hc9 : uh*d ^ 2*cp ≤ U ^ 8 := by
    have hh := hp [uh,d,d,cp] (by intro x hx; simp only [budget,List.mem_cons,List.not_mem_nil,or_false] at hx ⊢; tauto) (by simp)
    simpa only [List.prod_cons,List.prod_nil,mul_one,pow_two,mul_assoc] using hh
  have haS : a ≤ S := (by nlinarith only [ha, hT] : a ≤ T*a).trans hTa
  have hdiv : N/T ≤ N := div_le_self hN hT
  have h1 : M+a ≤ 2*S := by linarith only [hMS, haS]
  have h2 : M+2*T*a ≤ 3*S := by nlinarith only [hMS, hTa]
  have h3 : M+2*T*a ≤ 3*S := h2
  have h6 : 4*N/T+a ≤ 5*S := by rw [mul_div_assoc]; linarith only [hdiv, hNS, haS]
  have h7 : N+2*T*a ≤ 3*S := by nlinarith only [hNS, hTa]
  have hU8 : 0 ≤ U ^ 8 := by positivity
  have ht1 := mul_le_mul hc1 h1 (by positivity : 0 ≤ M+a) hU8
  have ht2 := mul_le_mul hc2 h2 (by positivity : 0 ≤ M+2*T*a) hU8
  have ht3 := mul_le_mul hc3 h3 (by positivity : 0 ≤ M+2*T*a) hU8
  have ht4 := mul_le_mul hc4 hED.2 hED.1 hU8
  have ht5 := mul_le_mul hc5 htail.2 htail.1 hU8
  have ht6 := mul_le_mul hc6 h6 (by positivity : 0 ≤ 4*N/T+a) hU8
  have ht7 := mul_le_mul hc7 h7 (by positivity : 0 ≤ N+2*T*a) hU8
  have ht8 := mul_le_mul hc8 hES.2 hES.1 hU8
  have ht9 := mul_le_mul hc9 hb.2 hb.1 hU8
  nlinarith only [ht1, ht2, ht3, ht4, ht5, ht6, ht7, ht8, ht9, mul_nonneg hU8 hS]



def poissonUnitBudget
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (G : Ideal O) (K N : ℝ) (W : 𝓢(ℝ,ℂ)) : List ℝ :=
  [(idealDivisors G).card,
   (columnDyadicLength K+1:ℕ), (columnDyadicLength N+1:ℕ),
   (2*diagonalControl sieveCutoff)*(divisorConstant ε hε*N ^ ε) ^ 2,
   divisorExponentConstant hexp deltaLoss hδ*((2*K)*N) ^ deltaLoss,
   ((idealDivisors (quadraticMaskIdeal 1)).card : ℝ)*‖paperRadialFourier (quadraticTransformedSquareProfile W) 0‖,
   ((idealDivisors (quadraticMaskIdeal 1)).card : ℝ)*‖quadraticTransformedSquareProfile W 0‖,
   ((idealDivisors (quadraticMaskIdeal 1)).card : ℝ)*dualMiddleDecayConstant (quadraticTransformedSquareProfile W),
   ‖paperRadialFourier (quadraticSquareProfile W) 0‖,
   originalMiddleDecayConstant (quadraticSquareProfile W),
   nonzeroLatticeEnvelopeConstant,
   (diagonalControl sieveCutoff) ^ 2*divisorConstant ε hε*(N*N) ^ ε*(CD*sD.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W)),
   (diagonalControl sieveCutoff) ^ 2*divisorConstant ε hε*((Ideal.absNorm G:ℝ)*(N*N)) ^ ε*(CS*sS.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)),
   ((Nat.card Oˣ : ℝ)*(2*diagonalControl sieveCutoff))*CT*sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W,
   divisorConstant ε hε*N ^ ε*CP*(K*N) ^ deltaLoss]

theorem poissonComparisonMajorant_unit_box
    (sD sS sT : Finset (ℕ×ℕ)) (CD CS CT CP : ℝ) (l A : ℕ)
    {α : ℝ} (hexp : HasSieveExponent α) (deltaLoss : ℝ) (hδ : 0 < deltaLoss) (ε : ℝ) (hε : 0 < ε)
    (G : Ideal O) (K N M T U S : ℝ) (W : 𝓢(ℝ,ℂ))
    (hK : 0 ≤ K) (hN : 0 < N) (hM : 0 ≤ M) (hT : 1 ≤ T) (hU : 1 ≤ U) (hS : 0 ≤ S)
    (hbudget : ∀x∈poissonUnitBudget sD sS sT CD CS CT CP hexp deltaLoss hδ ε hε G K N W, 0 ≤ x ∧ x ≤ U)
    (hMS : M ≤ S) (hNS : N ≤ S) (hmid : T*Real.sqrt M*(2*K) ^ (α-1/2) ≤ S)
    (hpr : Real.sqrt (M/K)*N+Real.sqrt M*K ^ (α-1/2) ≤ S)
    (hED : K*M/T ^ l ≤ S) (hES : K*N/T ^ l ≤ S)
    (htail : M/((min 1 (M/((Ideal.absNorm G:ℝ)*N*N))) ^ 2*
      (1+(M/((Ideal.absNorm G:ℝ)*N*N))*K) ^ A) ≤ S) :
    poissonComparisonMajorant sD sS sT CD CS CT CP l A hexp deltaLoss hδ ε hε G K N M T
      (fun _ : Unit => (1:ℂ)) W ≤ 262144*U ^ 8*S := by
  have hh := poisson_nine_terms_box
    ((idealDivisors G).card:ℝ)
    (columnDyadicLength K+1:ℕ) (columnDyadicLength N+1:ℕ)
    ((2*diagonalControl sieveCutoff)*(divisorConstant ε hε*N ^ ε) ^ 2)
    (divisorExponentConstant hexp deltaLoss hδ*((2*K)*N) ^ deltaLoss)
    (((idealDivisors (quadraticMaskIdeal 1)).card : ℝ)*‖paperRadialFourier (quadraticTransformedSquareProfile W) 0‖)
    (((idealDivisors (quadraticMaskIdeal 1)).card : ℝ)*‖quadraticTransformedSquareProfile W 0‖)
    (((idealDivisors (quadraticMaskIdeal 1)).card : ℝ)*dualMiddleDecayConstant (quadraticTransformedSquareProfile W))
    ‖paperRadialFourier (quadraticSquareProfile W) 0‖
    (originalMiddleDecayConstant (quadraticSquareProfile W)) nonzeroLatticeEnvelopeConstant
    ((diagonalControl sieveCutoff) ^ 2*divisorConstant ε hε*(N*N) ^ ε*(CD*sD.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticTransformedSquareProfile W)))
    ((diagonalControl sieveCutoff) ^ 2*divisorConstant ε hε*((Ideal.absNorm G:ℝ)*(N*N)) ^ ε*(CS*sS.sup (schwartzSeminormFamily ℝ ℝ ℂ) (quadraticSquareProfile W)))
    (((Nat.card Oˣ : ℝ)*(2*diagonalControl sieveCutoff))*CT*sT.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)
    (divisorConstant ε hε*N ^ ε*CP*(K*N) ^ deltaLoss)
    M N T (Real.sqrt M*(2*K) ^ (α-1/2))
    (Real.sqrt (M/K)*N+Real.sqrt M*K ^ (α-1/2))
    (K*M/T ^ l) (K*N/T ^ l)
    (M/((min 1 (M/((Ideal.absNorm G:ℝ)*N*N))) ^ 2*(1+(M/((Ideal.absNorm G:ℝ)*N*N))*K) ^ A))
    U S hU hS hbudget hM hN.le hT (by positivity) hMS hNS
    (by simpa only [mul_assoc] using hmid) ⟨by positivity,hpr⟩
    ⟨by positivity,hED⟩ ⟨by positivity,hES⟩ ⟨by positivity,htail⟩
  convert hh using 1
  unfold poissonComparisonMajorant retainedDualMajorant sourcePrincipalMajorant
    smallPrincipalMajorant dualMiddleMajorant
  simp only [divisorEnergyFactor_diagonal,Fintype.sum_unique,norm_one,one_pow,
    mul_one,one_mul,div_one]
  field_simp
  ; ring


end SchwartzPlanePoisson.CanonicalQuadraticSieve

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
