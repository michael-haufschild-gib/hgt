/-
Composition of quadratic sieves adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.QuadraticSieve.QuadraticLargeSieve

/-!
# Composition of quadratic sieves

Supported and admissible ideals of the canonical quadratic sieve. Pairs are grouped by their
product before sieving; excluded primes cost the divisor count of the fixed mask, and repeated
columns cost their largest fiber.
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
open Eisenstein
open scoped Classical

/-- Group pairs by their product before applying the quadratic sieve. -/
def productColumnCoefficient (S T : Finset (Ideal O)) (β : Ideal O → Ideal O → ℂ) (I : Ideal O) : ℂ :=
  ∑p∈(S×ˢT).filter (fun p => p.1*p.2=I),β p.1 p.2

theorem product_fiber_card (P : Finset (Ideal O×Ideal O)) (I : Ideal O) (hI : I≠0) :
    (P.filter (fun p => p.1*p.2=I)).card ≤ (idealDivisors I).card := by
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
    (hβ : ∀n∈S,∀b∈T,‖β n b‖ ≤ 1) (I : Ideal O) (hI : I≠0) :
    ‖productColumnCoefficient S T β I‖ ≤ (idealDivisors I).card := by
  unfold productColumnCoefficient
  apply (norm_sum_le _ _).trans
  calc
    _  ≤  ∑p∈(S×ˢT).filter (fun p => p.1*p.2=I),(1:ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hh := Finset.mem_product.mp (Finset.mem_filter.mp hp).1
      exact hβ p.1 hh.1 p.2 hh.2
    _ = ((S×ˢT).filter (fun p => p.1*p.2=I)).card := by simp
    _  ≤  _ := by exact_mod_cast product_fiber_card (S×ˢT) I hI

theorem productColumnCoefficient_row_sum (S T : Finset (Ideal O))
    (β : Ideal O → Ideal O → ℂ) (k : QuadraticIdeal) :
    (∑n∈S,∑b∈T,canonicalQuadraticRow k (primaryIdealGenerator (n*b))*β n b)=
    ∑I∈(S×ˢT).image (fun p => p.1*p.2),canonicalQuadraticRow k (primaryIdealGenerator I)*productColumnCoefficient S T β I := by
  rw [←Finset.sum_product (f := fun p : Ideal O×Ideal O => canonicalQuadraticRow k (primaryIdealGenerator (p.1*p.2))*β p.1 p.2)]
  rw [←Finset.sum_fiberwise_of_maps_to
    (fun p (hp : p∈S×ˢT) => Finset.mem_image_of_mem (fun p : Ideal O×Ideal O => p.1*p.2) hp)]
  apply Finset.sum_congr rfl
  intro I hI
  rw [productColumnCoefficient,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [(Finset.mem_filter.mp hp).2]

theorem product_quadratic_norm :
    ∀ε : ℝ, 0 < ε → ∃C : ℝ, 0 < C ∧ ∀K U B : ℝ,
      1 ≤ K → 1 ≤ U → 1 ≤ B → ∀S T : Finset (Ideal O),
      (∀I∈S,quadraticSupported I ∧ (Ideal.absNorm I:ℝ) ≤ U) →
      (∀I∈T,quadraticSupported I ∧ (Ideal.absNorm I:ℝ) ≤ B) →
      ∀β : Ideal O → Ideal O → ℂ, (∀n∈S,∀b∈T,‖β n b‖ ≤ 1) →
      (∑k : QuadraticIdealRange K,‖∑n∈S,∑b∈T,canonicalQuadraticRow k.val (primaryIdealGenerator (n*b))*β n b‖ ^ 2) ≤ 
        C*(K*(U*B)) ^ ε*(K+U*B)*(U*B) := by
  intro ε hε
  have hh : 0 < ε/2 := by positivity
  have hq : 0 < ε/4 := by positivity
  obtain ⟨C,hC,hbound⟩ := bounded_supported_quadratic_norm (ε/2) hh
  obtain ⟨D,hD,hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε/4) hq
  refine ⟨C*D ^ 2,by positivity,?_⟩
  intro K U B hK hU hB S T hS hT β hβ
  let X := U*B
  let P := (S×ˢT).image (fun p => p.1*p.2)
  have hX : 1 ≤ X := by dsimp [X]; nlinarith
  have hX0 : 0 < X := by linarith
  have hK0 : 0 < K := by linarith
  have hp (I : Ideal O) (hI : I∈P) : quadraticSupported I ∧ (Ideal.absNorm I:ℝ) ≤ X := by
    obtain ⟨⟨n,b⟩,hnb,rfl⟩ := Finset.mem_image.mp hI
    have hm := Finset.mem_product.mp hnb
    refine ⟨(quadraticSupported_mul n b).mpr ⟨(hS n hm.1).1,(hT b hm.2).1⟩,?_⟩
    rw [map_mul,Nat.cast_mul]
    exact mul_le_mul (hS n hm.1).2 (hT b hm.2).2 (Nat.cast_nonneg _) (by linarith)
  have hcoeff (I : Ideal O) (hI : I∈P) : ‖productColumnCoefficient S T β I‖ ≤ D*X ^ (ε/4) := by
    apply (productColumnCoefficient_norm S T β hβ I (primaryIdealGenerator_ne_zero_ideal I (hp I hI).1.1)).trans
    apply (hdiv I (primaryIdealGenerator_ne_zero_ideal I (hp I hI).1.1)).trans
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (Nat.cast_nonneg _) (hp I hI).2 hq.le) hD.le
  have hb := hbound K X (D*X ^ (ε/4)) hK hX (by positivity) P hp (productColumnCoefficient S T β) hcoeff
  simp_rw [productColumnCoefficient_row_sum]
  apply hb.trans
  have hpow : (K*X) ^ (ε/2)*(X ^ (ε/4)) ^ 2 ≤ (K*X) ^ ε := by
    have hXP : X ≤ K*X := by nlinarith
    calc
      _  ≤  (K*X) ^ (ε/2)*((K*X) ^ (ε/4)) ^ 2 := by gcongr
      _ = _ := by
        rw [pow_two,←mul_assoc,←Real.rpow_add (by positivity : 0 < K*X),←Real.rpow_add (by positivity : 0 < K*X)]
        congr 1
        ring
  calc
    _ = (C*D ^ 2)*((K*X) ^ (ε/2)*(X ^ (ε/4)) ^ 2)*(K+X)*X := by ring
    _  ≤  _ := by change _ ≤ (C*D ^ 2)*(K*X) ^ ε*(K+X)*X; gcongr


end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein
open scoped Classical

/-- Excluded prime factors cost only the number of divisors of the fixed mask. -/
theorem squarefree_all_column_energy {n : Type*} [Fintype n]
    (cols : n → {I : Ideal O // Squarefree I}) (hinj : Function.Injective cols) (X K : ℝ)
    (hcols : ∀ j, (Ideal.absNorm (cols j).val : ℝ) ≤ X) (a : n → ℂ) :
    (∑ k : QuadraticIdealRange K, ‖∑ j,
      canonicalQuadraticRow k.val (primaryIdealGenerator (cols j).val)*a j‖ ^ 2) ≤
      ((idealDivisors (quadraticMaskIdeal 1)).card : ℝ)*sieveNorm X K*∑ j, ‖a j‖ ^ 2 := by
  let sector (D : idealDivisors (quadraticMaskIdeal 1)) := {j : n // quadraticBadSector (cols j) = D}
  have hsector (D : idealDivisors (quadraticMaskIdeal 1)) :
      (∑ k : QuadraticIdealRange K, ‖∑ j : sector D,
        canonicalQuadraticRow k.val (primaryIdealGenerator (cols j.val).val)*a j.val‖ ^ 2) ≤
        sieveNorm X K*∑ j : sector D, ‖a j.val‖ ^ 2 := by
    let good : sector D → QuadraticIdeal := fun j => quadraticGoodRow (cols j.val)
    have hg : Function.Injective good := by
      intro i j hij
      apply Subtype.ext
      apply hinj
      exact quadraticGoodRow_injective_on_sector (cols i.val) (cols j.val)
        (i.property.trans j.property.symm) hij
    let B : Matrix (sector D) (QuadraticIdealRange K) ℂ := fun j k =>
      canonicalQuadraticRow k.val (primaryIdealGenerator (good j).val)
    have hB : ‖FiniteSieveOperator.operator B‖ ^ 2 ≤ sieveNorm X K :=
      family_squared_norm_le good (fun k : QuadraticIdealRange K => k.val) hg Subtype.val_injective X K
        (fun j => (quadraticGoodRow_norm_le (cols j.val)).trans (hcols j.val)) (fun k => k.property)
    have hBT : B.conjTranspose =
        (fun k j => canonicalQuadraticRow k.val (primaryIdealGenerator (good j).val)) := by
      ext k j
      exact canonicalQuadraticRow_star _ _
    have he := FiniteSieveOperator.energy_bound B.conjTranspose (fun j : sector D => a j.val)
    rw [FiniteSieveOperator.operator_conjTranspose_norm,hBT] at he
    have hrow (k : QuadraticIdealRange K) :
        (∑ j : sector D, canonicalQuadraticRow k.val (primaryIdealGenerator (cols j.val).val)*a j.val) =
          canonicalQuadraticRow k.val (primaryIdealGenerator D.val)*
          ∑ j : sector D, canonicalQuadraticRow k.val (primaryIdealGenerator (good j).val)*a j.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      have hj : (cols j.val).val = D.val*(good j).val := by
        rw [←quadraticBadSector_good_product (cols j.val),j.property]
      rw [hj,primaryIdealGenerator_mul,canonicalQuadraticRow_mul]
      ring
    have hpoint (k : QuadraticIdealRange K) :
        ‖∑ j : sector D, canonicalQuadraticRow k.val (primaryIdealGenerator (cols j.val).val)*a j.val‖ ^ 2 ≤
          ‖∑ j : sector D, canonicalQuadraticRow k.val (primaryIdealGenerator (good j).val)*a j.val‖ ^ 2 := by
      rw [hrow,norm_mul]
      apply pow_le_pow_left₀ (by positivity)
      exact mul_le_of_le_one_left (norm_nonneg _) (canonicalQuadraticRow_norm_le_one _ _)
    exact (Finset.sum_le_sum (fun k _ => hpoint k)).trans
      (he.trans (mul_le_mul_of_nonneg_right hB (by positivity)))
  have hpoint (k : QuadraticIdealRange K) :
      ‖∑ j, canonicalQuadraticRow k.val (primaryIdealGenerator (cols j).val)*a j‖ ^ 2 ≤
        ((idealDivisors (quadraticMaskIdeal 1)).card : ℝ)*
        ∑ D : idealDivisors (quadraticMaskIdeal 1), ‖∑ j : sector D,
          canonicalQuadraticRow k.val (primaryIdealGenerator (cols j.val).val)*a j.val‖ ^ 2 := by
    rw [←Fintype.sum_fiberwise (fun j => quadraticBadSector (cols j))]
    have hn := pow_le_pow_left₀ (norm_nonneg _)
      (norm_sum_le Finset.univ (fun D : idealDivisors (quadraticMaskIdeal 1) =>
        ∑ j : sector D, canonicalQuadraticRow k.val (primaryIdealGenerator (cols j.val).val)*a j.val)) 2
    have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : idealDivisors (quadraticMaskIdeal 1) => (1 : ℝ))
      (fun D : idealDivisors (quadraticMaskIdeal 1) =>
        ‖∑ j : sector D, canonicalQuadraticRow k.val (primaryIdealGenerator (cols j.val).val)*a j.val‖)
    apply hn.trans
    simpa only [one_mul,one_pow,Finset.sum_const,Finset.card_univ,Fintype.card_coe,
      nsmul_eq_mul,mul_one] using hc
  calc
    _ ≤ ∑ k : QuadraticIdealRange K, ((idealDivisors (quadraticMaskIdeal 1)).card : ℝ)*
        ∑ D : idealDivisors (quadraticMaskIdeal 1), ‖∑ j : sector D,
          canonicalQuadraticRow k.val (primaryIdealGenerator (cols j.val).val)*a j.val‖ ^ 2 :=
      Finset.sum_le_sum (fun k _ => hpoint k)
    _ = ((idealDivisors (quadraticMaskIdeal 1)).card : ℝ)*
        ∑ D : idealDivisors (quadraticMaskIdeal 1), ∑ k : QuadraticIdealRange K,
          ‖∑ j : sector D, canonicalQuadraticRow k.val (primaryIdealGenerator (cols j.val).val)*a j.val‖ ^ 2 := by
      rw [←Finset.mul_sum,Finset.sum_comm]
    _ ≤ ((idealDivisors (quadraticMaskIdeal 1)).card : ℝ)*
        ∑ D : idealDivisors (quadraticMaskIdeal 1), sieveNorm X K*∑ j : sector D, ‖a j.val‖ ^ 2 := by
      gcongr with D
      exact hsector D
    _ = _ := by
      have he : (∑ D : idealDivisors (quadraticMaskIdeal 1), ∑ j : sector D, ‖a j.val‖ ^ 2) =
          ∑ j, ‖a j‖ ^ 2 :=
        Fintype.sum_fiberwise (fun j => quadraticBadSector (cols j)) (fun j => ‖a j‖ ^ 2)
      rw [←Finset.mul_sum,he]
      ring

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein
open scoped Classical

lemma columnSquareFiber_nonzero_bounds (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀ I ∈ S, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ X) (A : Ideal O)
    (I : columnSquareFiber S A) :
    Squarefree (quadraticSquarefreePart I.val) ∧
      (Ideal.absNorm (quadraticSquarefreePart I.val) : ℝ) ≤ X/(Ideal.absNorm A : ℝ) ^ 2 := by
  have hi := hS I.val (Finset.mem_filter.mp I.property).1
  have hI0 := hi.1
  have ha := (Finset.mem_filter.mp I.property).2
  have hAz : A ≠ 0 := by rw [← ha]; exact quadraticSquarePart_ne_zero I.val
  have hAn : 0 < (Ideal.absNorm A : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (fun hz => hAz (Ideal.absNorm_eq_zero_iff.mp hz))
  refine ⟨quadraticSquarefreePart_squarefree I.val,(le_div_iff₀ (sq_pos_of_pos hAn)).mpr ?_⟩
  have hn := quadraticSquarePart_norm_decomposition I.val hI0
  rw [ha] at hn
  nlinarith only [hn,hi.2]

lemma columnSquareFiber_nonzero_card (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀ I ∈ S, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ X) (A : Ideal O)
    (hscale : 1 ≤ X/(Ideal.absNorm A : ℝ) ^ 2) :
    ((columnSquareFiber S A).card : ℝ) ≤ diagonalControl sieveCutoff*(X/(Ideal.absNorm A : ℝ) ^ 2) := by
  let T := (columnSquareFiber S A).image quadraticSquarefreePart
  have hcard : T.card = (columnSquareFiber S A).card := Finset.card_image_iff.mpr (by
    intro I hI J hJ he
    have hh : (⟨I,hI⟩ : columnSquareFiber S A) = (⟨J,hJ⟩ : columnSquareFiber S A) :=
      columnSquareFiber_injective S (fun I hI => (hS I hI).1) A he
    exact congrArg Subtype.val hh)
  rw [← hcard]
  apply finite_ideal_card_bound T _ hscale
  intro I hI
  obtain ⟨J,hJ,rfl⟩ := Finset.mem_image.mp hI
  exact (columnSquareFiber_nonzero_bounds S X hS A ⟨J,hJ⟩).2


theorem columnSquareFiber_all_energy (S : Finset (Ideal O)) (X K : ℝ)
    (hS : ∀ I ∈ S, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ X)
    (A : Ideal O) (a : Ideal O → ℂ) :
    (∑ k : QuadraticIdealRange K, ‖∑ I ∈ columnSquareFiber S A,
      canonicalQuadraticRow k.val (primaryIdealGenerator I)*a I‖ ^ 2) ≤
      ((idealDivisors (quadraticMaskIdeal 1)).card : ℝ)*sieveNorm (X/(Ideal.absNorm A : ℝ) ^ 2) K * ∑ I ∈ columnSquareFiber S A, ‖a I‖ ^ 2 := by
  let T := columnSquareFiber S A
  let cols : T → {I : Ideal O // Squarefree I} := fun I =>
    ⟨quadraticSquarefreePart I.val,quadraticSquarefreePart_squarefree I.val⟩
  have hinj : Function.Injective cols := by
    intro I J he
    exact columnSquareFiber_injective S (fun I hI => (hS I hI).1) A
      (congrArg Subtype.val he)
  have he := squarefree_all_column_energy cols hinj (X/(Ideal.absNorm A : ℝ) ^ 2) K
    (fun I => (columnSquareFiber_nonzero_bounds S X hS A I).2) (fun I : T => a I.val)
  have hm (k : QuadraticIdealRange K) :
      ‖∑ I : T, canonicalQuadraticRow k.val (primaryIdealGenerator I.val)*a I.val‖ ^ 2 ≤
        ‖∑ I : T, canonicalQuadraticRow k.val (primaryIdealGenerator (quadraticSquarefreePart I.val))*a I.val‖ ^ 2 := by
    have hrow : (∑ I : T, canonicalQuadraticRow k.val (primaryIdealGenerator I.val)*a I.val) =
        quadraticIdealMask k.val (primaryIdealGenerator A)*
        ∑ I : T, canonicalQuadraticRow k.val (primaryIdealGenerator (quadraticSquarefreePart I.val))*a I.val := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro I _
      have hi := Finset.mem_filter.mp I.property
      have hq := canonicalQuadraticRow_squarefree_argument k.val (quadraticSquarefreePart I.val) (quadraticSquarePart I.val)
      rw [quadraticParts_mul_square I.val (hS I.val hi.1).1,hi.2] at hq
      rw [hq]
      ring
    rw [hrow,norm_mul,mul_pow]
    have hmask : ‖quadraticIdealMask k.val (primaryIdealGenerator A)‖ ^ 2 ≤ 1 := by
      rw [quadraticIdealMask_indicator]
      split_ifs <;> norm_num
    exact mul_le_of_le_one_left (sq_nonneg _) hmask
  have hsum (k : QuadraticIdealRange K) :
      (∑ I ∈ columnSquareFiber S A, canonicalQuadraticRow k.val (primaryIdealGenerator I)*a I) =
      ∑ I : T, canonicalQuadraticRow k.val (primaryIdealGenerator I.val)*a I.val :=
    (Finset.sum_coe_sort T _).symm
  simp_rw [hsum]
  rw [← Finset.sum_coe_sort T (fun I => ‖a I‖ ^ 2)]
  exact (Finset.sum_le_sum (fun k _ => hm k)).trans
    he

lemma columnSquareParts_nonzero_bounds (S : Finset (Ideal O)) (X : ℝ)
    (hS : ∀ I ∈ S, I ≠ 0 ∧ (Ideal.absNorm I : ℝ) ≤ X) (A : Ideal O)
    (hA : A ∈ S.image quadraticSquarePart) :
    A ≠ 0 ∧ 1 ≤ (Ideal.absNorm A : ℝ) ∧ (Ideal.absNorm A : ℝ) ≤ X ∧ 1 ≤ X/(Ideal.absNorm A : ℝ) ^ 2 := by
  obtain ⟨I,hI,rfl⟩ := Finset.mem_image.mp hA
  have hi := hS I hI
  have hI0 := hi.1
  have hAz := quadraticSquarePart_ne_zero I
  have hDz := (quadraticSquarefreePart_squarefree I).ne_zero
  have ha : 1 ≤ (Ideal.absNorm (quadraticSquarePart I) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hAz (Ideal.absNorm_eq_zero_iff.mp hz))
  have hd : 1 ≤ (Ideal.absNorm (quadraticSquarefreePart I) : ℝ) := by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr (fun hz => hDz (Ideal.absNorm_eq_zero_iff.mp hz))
  have hn := quadraticSquarePart_norm_decomposition I hI0
  refine ⟨hAz,ha,by nlinarith only [ha,hd,hn,hi.2],?_⟩
  apply (le_div_iff₀ (by positivity : 0 < (Ideal.absNorm (quadraticSquarePart I) : ℝ) ^ 2)).mpr
  nlinarith only [ha,hd,hn,hi.2]

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein MeasureTheory
open scoped Classical

/-- Square-part fibers and fixed exceptional sectors control every nonzero column. -/
theorem bounded_nonzero_quadratic_norm :
    ∀ε : ℝ, 0 < ε → ∃C : ℝ, 0 < C ∧ ∀K X lengthScale : ℝ,
      1 ≤ K → 1 ≤ X → 0 ≤ lengthScale → ∀S : Finset (Ideal O),
      (∀I∈S,I ≠ 0 ∧ (Ideal.absNorm I:ℝ) ≤ X) →
      ∀a : Ideal O → ℂ, (∀I∈S,‖a I‖ ≤ lengthScale) →
      (∑k : QuadraticIdealRange K,‖∑I∈S,canonicalQuadraticRow k.val (primaryIdealGenerator I)*a I‖ ^ 2) ≤ 
        C*(K*X) ^ ε*(K+X)*X*lengthScale ^ 2 := by
  intro ε hε
  have hdiag := diagonalControl_nonneg sieveCutoff
  let B : ℝ := (idealDivisors (quadraticMaskIdeal 1)).card+1
  have hB : 0 < B := by dsimp [B]; positivity
  let deltaLoss := ε/3
  have hδ : 0 < deltaLoss := by dsimp [deltaLoss]; positivity
  obtain ⟨C,hC,hsharp⟩ := sieveNorm_sharp deltaLoss hδ
  let D : ℝ := (2*(diagonalControl sieveCutoff+1))*(2+1/(deltaLoss*Real.log 2))
  have hD : 0 < D := by have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num); dsimp [D]; positivity
  refine ⟨B*(diagonalControl sieveCutoff+1)*C*D ^ 2,by positivity,?_⟩
  intro K X lengthScale hK hX hL S hS a ha
  let T := S.image quadraticSquarePart
  let R : ℝ := ∑A∈T,1/(Ideal.absNorm A:ℝ)
  have hK0 : 0 < K := by linarith
  have hX0 : 0 < X := by linarith
  have hP0 : 0 < K*X := by positivity
  have hprop (A : Ideal O) (hA : A∈T) := columnSquareParts_nonzero_bounds S X hS A hA
  have hT0 : ∀A∈T,A≠0 := fun A hA => (hprop A hA).1
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hRL : R ≤ D*X ^ deltaLoss := by
    apply (finite_inverse_norm_sum T X hT0 (fun A hA => (hprop A hA).2.2.1)).trans
    have hh := columnDyadicLength_small_power deltaLoss hδ X hX
    dsimp [D]
    have hp := Real.rpow_nonneg hX0.le deltaLoss
    have hlog : 0  <  Real.log 2 := Real.log_pos (by norm_num)
    have hc : 0  ≤  2+1/(deltaLoss*Real.log 2) := by positivity
    nlinarith only [hh,hdiag,hp,mul_nonneg hc hp]
  let F : ℝ := B*(diagonalControl sieveCutoff+1)*C*(K*X) ^ deltaLoss*(K+X)*X*lengthScale ^ 2
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hf (A : Ideal O) (hA : A∈T) :
      (Ideal.absNorm A:ℝ)*(∑k : QuadraticIdealRange K,‖∑I∈columnSquareFiber S A,
        canonicalQuadraticRow k.val (primaryIdealGenerator I)*a I‖ ^ 2) ≤ F/(Ideal.absNorm A:ℝ) := by
    have hp := hprop A hA
    have hn : 0 < (Ideal.absNorm A:ℝ) := by linarith [hp.2.1]
    let Y := X/(Ideal.absNorm A:ℝ) ^ 2
    have hY : 1 ≤ Y := hp.2.2.2
    have hYX : Y ≤ X := div_le_self hX0.le (one_le_pow₀ hp.2.1)
    have hb : sieveNorm Y K ≤ C*(K*X) ^ deltaLoss*(K+X) := by
      apply (hsharp Y K hY hK).trans
      have hprod : Y*K ≤ K*X := by nlinarith
      have hpw := Real.rpow_le_rpow (by positivity : 0 ≤ Y*K) hprod hδ.le
      exact mul_le_mul (mul_le_mul_of_nonneg_left hpw hC.le) (by linarith)
        (by positivity) (by positivity)
    have hea : (∑I∈columnSquareFiber S A,‖a I‖ ^ 2) ≤ (diagonalControl sieveCutoff+1)*Y*lengthScale ^ 2 := by
      calc
        _  ≤  ∑_I∈columnSquareFiber S A,lengthScale ^ 2 := by
          apply Finset.sum_le_sum
          intro I hI
          exact pow_le_pow_left₀ (norm_nonneg _) (ha I (Finset.mem_filter.mp hI).1) 2
        _ = ((columnSquareFiber S A).card:ℝ)*lengthScale ^ 2 := by simp
        _  ≤  diagonalControl sieveCutoff*Y*lengthScale  ^  2 :=
          mul_le_mul_of_nonneg_right (columnSquareFiber_nonzero_card S X hS A hY) (sq_nonneg _)
        _  ≤  _ := by gcongr; linarith
    have he := columnSquareFiber_all_energy S X K hS A a
    calc
      _  ≤  (Ideal.absNorm A:ℝ)*(B*sieveNorm Y K*(∑I∈columnSquareFiber S A,‖a I‖ ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply he.trans
        apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
        apply mul_le_mul_of_nonneg_right _ (sieveNorm_nonneg Y K)
        dsimp only [B]
        exact le_add_of_nonneg_right zero_le_one
      _  ≤  (Ideal.absNorm A:ℝ)*((B*(C*(K*X) ^ deltaLoss*(K+X)))*((diagonalControl sieveCutoff+1)*Y*lengthScale ^ 2)) := by
        gcongr
      _ = F/(Ideal.absNorm A:ℝ) := by dsimp [F,Y]; field_simp [hn.ne']
  have hsplit (k : QuadraticIdealRange K) :
      (∑I∈S,canonicalQuadraticRow k.val (primaryIdealGenerator I)*a I)=
      ∑A∈T,∑I∈columnSquareFiber S A,canonicalQuadraticRow k.val (primaryIdealGenerator I)*a I := by
    exact (Finset.sum_fiberwise_of_maps_to (fun I hI => Finset.mem_image_of_mem quadraticSquarePart hI) _).symm
  have hcauchy (k : QuadraticIdealRange K) :
      ‖∑I∈S,canonicalQuadraticRow k.val (primaryIdealGenerator I)*a I‖ ^ 2 ≤ 
      R*∑A∈T,(Ideal.absNorm A:ℝ)*‖∑I∈columnSquareFiber S A,canonicalQuadraticRow k.val (primaryIdealGenerator I)*a I‖ ^ 2 := by
    rw [hsplit]
    exact ideal_reciprocal_cauchy T hT0 _
  have htotal : (∑k : QuadraticIdealRange K,‖∑I∈S,canonicalQuadraticRow k.val (primaryIdealGenerator I)*a I‖ ^ 2) ≤ F*R ^ 2 := by
    calc
      _  ≤  ∑k : QuadraticIdealRange K,R*∑A∈T,(Ideal.absNorm A:ℝ)*‖∑I∈columnSquareFiber S A,
          canonicalQuadraticRow k.val (primaryIdealGenerator I)*a I‖ ^ 2 := Finset.sum_le_sum (fun k _ => hcauchy k)
      _ = R*∑A∈T,(Ideal.absNorm A:ℝ)*∑k : QuadraticIdealRange K,‖∑I∈columnSquareFiber S A,
          canonicalQuadraticRow k.val (primaryIdealGenerator I)*a I‖ ^ 2 := by
        rw [←Finset.mul_sum,Finset.sum_comm]
        congr 1
        apply Finset.sum_congr rfl
        intro A hA
        rw [←Finset.mul_sum]
      _  ≤  R*∑A∈T,F/(Ideal.absNorm A:ℝ) := by gcongr with A hA; exact hf A hA
      _ = F*R ^ 2 := by
        simp_rw [div_eq_mul_inv]
        rw [←Finset.mul_sum]
        dsimp [R]
        simp only [one_div]
        ring
  have hpower : (K*X) ^ deltaLoss*(X ^ deltaLoss) ^ 2 ≤ (K*X) ^ ε := by
    have hXP : X ≤ K*X := by nlinarith
    calc
      _  ≤  (K*X) ^ deltaLoss*((K*X) ^ deltaLoss) ^ 2 := by gcongr
      _ = (K*X) ^ ε := by
        rw [pow_two,←mul_assoc,←Real.rpow_add hP0,←Real.rpow_add hP0]
        congr 1
        dsimp [deltaLoss]
        ring
  apply htotal.trans
  calc
    _  ≤  F*(D*X ^ deltaLoss) ^ 2 := by gcongr
    _ = (B*(diagonalControl sieveCutoff+1)*C*D ^ 2)*((K*X) ^ deltaLoss*(X ^ deltaLoss) ^ 2)*(K+X)*X*lengthScale ^ 2 := by dsimp [F]; ring
    _  ≤  _ := by gcongr


end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein
open scoped Classical

/-- Grouping repeated columns costs their largest fiber cardinality. -/
theorem column_fiber_sieve {K X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (rows : Finset K) (source : Finset X) (target : Finset Y)
    (φ : X → Y) (q : K → Y → ℂ) (a : X → ℂ) (Q D : ℝ) (hQ : 0 ≤ Q)
    (hφ : ∀ x ∈ source, φ x ∈ target)
    (hfiber : ∀ y ∈ target, ((source.filter (fun x => φ x = y)).card : ℝ) ≤ D)
    (hsieve : ∀ f : Y → ℂ,
      (∑ k ∈ rows, ‖∑ y ∈ target, q k y*f y‖ ^ 2) ≤ Q*∑ y ∈ target, ‖f y‖ ^ 2) :
    (∑ k ∈ rows, ‖∑ x ∈ source, q k (φ x)*a x‖ ^ 2) ≤ Q*D*∑ x ∈ source, ‖a x‖ ^ 2 := by
  let f : Y → ℂ := fun y => ∑ x ∈ source with φ x = y, a x
  have he (k : K) : (∑ x ∈ source, q k (φ x)*a x) = ∑ y ∈ target, q k y*f y := by
    rw [←Finset.sum_fiberwise_of_maps_to hφ]
    apply Finset.sum_congr rfl
    intro y _
    dsimp only [f]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x hx
    rw [(Finset.mem_filter.mp hx).2]
  have hb (y : Y) (hy : y ∈ target) : ‖f y‖ ^ 2 ≤ D*∑ x ∈ source with φ x = y, ‖a x‖ ^ 2 := by
    let S := source.filter (fun x => φ x = y)
    have hn := pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le S a) 2
    have hc := Finset.sum_mul_sq_le_sq_mul_sq S (fun _ => (1 : ℝ)) (fun x => ‖a x‖)
    simp only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one] at hc
    exact (hn.trans hc).trans (mul_le_mul_of_nonneg_right (hfiber y hy) (by positivity))
  have hf : (∑ y ∈ target, ‖f y‖ ^ 2) ≤ D*∑ x ∈ source, ‖a x‖ ^ 2 := by
    calc
      _ ≤ ∑ y ∈ target, D*∑ x ∈ source with φ x = y, ‖a x‖ ^ 2 := Finset.sum_le_sum hb
      _ = _ := by rw [←Finset.mul_sum,Finset.sum_fiberwise_of_maps_to hφ]
  simp_rw [he]
  exact (hsieve f).trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hf hQ)

/-- Restrict a nonnegative row energy from the complete norm ball. -/
lemma quadratic_range_energy_restrict (K : ℝ) (rows : Finset QuadraticIdeal)
    (hrows : ∀ k ∈ rows, (Ideal.absNorm k.val : ℝ) ≤ K)
    (E : QuadraticIdeal → ℝ) (hE : ∀ k, 0 ≤ E k) :
    (∑ k ∈ rows, E k) ≤ ∑ k : QuadraticIdealRange K, E k.val := by
  let f : rows → QuadraticIdealRange K := fun k => ⟨k.val,hrows k.val k.property⟩
  have hf : Function.Injective f := fun i j h => Subtype.ext (congrArg (fun k : QuadraticIdealRange K => k.val) h)
  rw [←Finset.sum_coe_sort rows E]
  change (∑ k : rows, E (f k).val) ≤ _
  rw [←Finset.sum_image (f := fun k : QuadraticIdealRange K => E k.val) (g := f)
    (fun _ _ _ _ h => hf h)]
  exact Finset.sum_le_univ_sum_of_nonneg (fun k => hE k.val)

/-- The sharp quadratic sieve allows squarefree columns containing excluded primes. -/
theorem finite_squarefree_quadratic_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset QuadraticIdeal) (cols : Finset (Ideal O)),
      (∀ k ∈ rows, (Ideal.absNorm k.val : ℝ) ≤ K) →
      (∀ J ∈ cols, Squarefree J ∧ (Ideal.absNorm J : ℝ) ≤ X) →
    ∀ a : Ideal O → ℂ,
      (∑ k ∈ rows, ‖∑ J ∈ cols, canonicalQuadraticRow k (primaryIdealGenerator J)*a J‖ ^ 2) ≤
        C*(K*X) ^ ε*(K+X)*∑ J ∈ cols, ‖a J‖ ^ 2 := by
  obtain ⟨C,hC,hsharp⟩ := sieveNorm_sharp ε hε
  let B : ℝ := (idealDivisors (quadraticMaskIdeal 1)).card+1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨B*C,mul_pos hB hC,?_⟩
  intro K X hK hX rows cols hrows hcols a
  let f : cols → {I : Ideal O // Squarefree I} := fun J => ⟨J.val,(hcols J.val J.property).1⟩
  have hf : Function.Injective f := fun I J h => Subtype.ext (congrArg (fun J : {I : Ideal O // Squarefree I} => J.val) h)
  have hb := squarefree_all_column_energy f hf X K
    (fun J => (hcols J.val J.property).2) (fun J => a J.val)
  have hi (k : QuadraticIdealRange K) :
      (∑ J : cols, canonicalQuadraticRow k.val (primaryIdealGenerator (f J).val)*a J.val) =
        ∑ J ∈ cols, canonicalQuadraticRow k.val (primaryIdealGenerator J)*a J :=
    Finset.sum_coe_sort cols (fun J => canonicalQuadraticRow k.val (primaryIdealGenerator J)*a J)
  simp_rw [hi] at hb
  rw [Finset.sum_coe_sort cols (fun J => ‖a J‖ ^ 2)] at hb
  apply (quadratic_range_energy_restrict K rows hrows
    (fun k => ‖∑ J ∈ cols, canonicalQuadraticRow k (primaryIdealGenerator J)*a J‖ ^ 2)
    (fun _ => sq_nonneg _)).trans
  apply hb.trans
  calc
    _ ≤ B*(C*(X*K) ^ ε*(X+K))*∑ J ∈ cols, ‖a J‖ ^ 2 := by
      apply mul_le_mul_of_nonneg_right _ (Finset.sum_nonneg (fun _ _ => sq_nonneg _))
      apply mul_le_mul _ (hsharp X K hX hK) (sieveNorm_nonneg X K) hB.le
      dsimp only [B]
      exact le_add_of_nonneg_right zero_le_one
    _ = _ := by rw [mul_comm X K,add_comm X K]; ring

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson.CanonicalQuadraticSieve
open Eisenstein
open scoped Classical

/-- Product collisions cost a divisor bound, absorbed into the arbitrary small power. -/
theorem quadratic_squarefree_product_column_energy (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset QuadraticIdeal) (pairs : Finset (Ideal O × Ideal O)),
      (∀ k ∈ rows, (Ideal.absNorm k.val : ℝ) ≤ K) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ a : Ideal O × Ideal O → ℂ,
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        canonicalQuadraticRow k (primaryIdealGenerator (p.1 * p.2)) * a p‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * ∑ p ∈ pairs, ‖a p‖ ^ 2 := by
  have hhalf : 0 < ε / 2 := by positivity
  obtain ⟨Cq, hCq, hquad⟩ := finite_squarefree_quadratic_energy (ε / 2) hhalf
  obtain ⟨Cd, hCd, hdiv⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 2) hhalf
  refine ⟨Cq * Cd, mul_pos hCq hCd, ?_⟩
  intro K X hK hX rows pairs hrows hpairs a
  let target := pairs.image (fun p => p.1 * p.2)
  have ht (J : Ideal O) (hJ : J ∈ target) :
      Squarefree J ∧ (Ideal.absNorm J : ℝ) ≤ X := by
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hJ
    exact hpairs p hp
  have hfiber (J : Ideal O) (hJ : J ∈ target) :
      ((pairs.filter (fun p => p.1 * p.2 = J)).card : ℝ) ≤ Cd * X ^ (ε / 2) := by
    apply (Nat.cast_le.mpr (product_fiber_card pairs J (ht J hJ).1.ne_zero)).trans
    exact (hdiv J (ht J hJ).1.ne_zero).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg _) (ht J hJ).2 hhalf.le) hCd.le)
  have he := column_fiber_sieve rows pairs target (fun p => p.1 * p.2)
    (fun k J => canonicalQuadraticRow k (primaryIdealGenerator J)) a
    (Cq * (K * X) ^ (ε / 2) * (K + X)) (Cd * X ^ (ε / 2)) (by positivity)
    (fun p hp => Finset.mem_image_of_mem _ hp) hfiber
    (hquad K X hK hX rows target hrows ht)
  apply he.trans
  have hKX : 0 < K * X := mul_pos (by linarith) (by linarith)
  have hpow : (K * X) ^ (ε / 2) * X ^ (ε / 2) ≤ (K * X) ^ ε := by
    calc
      _ ≤ (K * X) ^ (ε / 2) * (K * X) ^ (ε / 2) := by
        apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hKX.le _)
        exact Real.rpow_le_rpow (by linarith) (le_mul_of_one_le_left (by linarith) hK) hhalf.le
      _ = _ := by rw [← Real.rpow_add hKX]; congr 1 ; ring
  calc
    _ = (Cq * Cd) * ((K * X) ^ (ε / 2) * X ^ (ε / 2)) * (K + X) *
        ∑ p ∈ pairs, ‖a p‖ ^ 2 := by ring
    _ ≤ _ := by gcongr

theorem quadratic_fixed_factor_energy
    (rows : Finset QuadraticIdeal) (pairs : Finset (Ideal O × Ideal O))
    (B : Ideal O)
    (a : Ideal O × Ideal O → ℂ) :
    (∑ k ∈ rows, ‖∑ p ∈ pairs,
      canonicalQuadraticRow k (primaryIdealGenerator (B * (p.1 * p.2))) * a p‖ ^ 2) ≤
    ∑ k ∈ rows, ‖∑ p ∈ pairs,
      canonicalQuadraticRow k (primaryIdealGenerator (p.1 * p.2)) * a p‖ ^ 2 := by
  apply Finset.sum_le_sum
  intro k hk
  have he : (∑ p ∈ pairs,
      canonicalQuadraticRow k (primaryIdealGenerator (B * (p.1 * p.2))) * a p) =
      canonicalQuadraticRow k (primaryIdealGenerator B) * ∑ p ∈ pairs,
        canonicalQuadraticRow k (primaryIdealGenerator (p.1 * p.2)) * a p := by
    simp only [primaryIdealGenerator_mul,
      canonicalQuadraticRow_mul k, Finset.mul_sum, mul_assoc]
  rw [he]
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _) (canonicalQuadraticRow_norm_le_one k _)

theorem quadratic_squarefree_product_energy_fixed_factor (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ K X : ℝ, 1 ≤ K → 1 ≤ X →
    ∀ (rows : Finset QuadraticIdeal) (pairs : Finset (Ideal O × Ideal O)),
      (∀ k ∈ rows, (Ideal.absNorm k.val : ℝ) ≤ K) →
      (∀ p ∈ pairs, Squarefree (p.1 * p.2) ∧ (Ideal.absNorm (p.1 * p.2) : ℝ) ≤ X) →
    ∀ (B : Ideal O) (a : Ideal O × Ideal O → ℂ),
      (∑ k ∈ rows, ‖∑ p ∈ pairs,
        canonicalQuadraticRow k (primaryIdealGenerator (B * (p.1 * p.2))) * a p‖ ^ 2) ≤
      C * (K * X) ^ ε * (K + X) * ∑ p ∈ pairs, ‖a p‖ ^ 2 := by
  obtain ⟨C, hC, hb⟩ := quadratic_squarefree_product_column_energy ε hε
  refine ⟨C, hC, ?_⟩
  intro K X hK hX rows pairs hrows hpairs B a
  exact (quadratic_fixed_factor_energy rows pairs B a).trans
    (hb K X hK hX rows pairs hrows hpairs a)

end SchwartzPlanePoisson.CanonicalQuadraticSieve

namespace SchwartzPlanePoisson
open Eisenstein
open scoped Classical SchwartzMap

/-- The exact trace Gauss sum of a product of prime characters. -/
def primeRowTraceGauss {ι : Type*} [Fintype ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) : ℂ :=
  let c := ∏ i, p i
  let hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  ∑ x : O ⧸ Ideal.span {c},
    primeCuspRowCharacter p χ (GaussianShiftedPartition.representative c x)*residueTraceQuotientChar 1 c hc x

/-- Poisson reflection retains the actual Gauss factor, needed for signed cancellation. -/
theorem prime_row_trace_poisson {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (hχ : ∀ i, χ i ≠ 1) :
    ‖primeRowTraceGauss p hp χ‖ ^ 2 = ‖ringComplex (∏ i, p i)‖ ^ 2 ∧
    ∀ (W : 𝓢(ℝ, ℂ)) (Y : ℝ), 0 < Y →
      (∑' z : O, primeCuspRowCharacter p χ z*W (‖ringComplex z‖ ^ 2/Y)) =
        ((Y : ℂ)*primeRowTraceGauss p hp χ/(‖ringComplex (∏ i, p i)‖ ^ 2 : ℝ))*
          ∑' h : O, primeCuspRowCharacter p (fun i => (χ i)⁻¹) h*
            paperRadialFourier W (Y*‖ringComplex h‖ ^ 2/‖ringComplex (∏ i, p i)‖ ^ 2) := by
  let P : ι → Ideal O := fun i => Ideal.span {p i}
  let c := ∏ i, p i
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  have hspan : Ideal.span {c} = ∏ i, P i := span_finset_prime_product p Finset.univ
  let e : (O ⧸ Ideal.span {c}) ≃+* ∀ i, O ⧸ P i :=
    (Ideal.quotEquivOfEq hspan).trans (Eisenstein.primeCRT P hinj)
  have he (z : O) (i : ι) :
      e (Ideal.Quotient.mk (Ideal.span {c}) z) i = Ideal.Quotient.mk (P i) z := by
    simp only [e,RingEquiv.trans_apply,Ideal.quotEquivOfEq_mk,Eisenstein.primeCRT]
    rfl
  let ψ := residueTraceQuotientChar 1 c hc
  let A : O ⧸ Ideal.span {c} → ℂ := fun x => ∏ i, χ i (e x i)
  have ha (z : O) : A (Ideal.Quotient.mk (Ideal.span {c}) z) = primeCuspRowCharacter p χ z := by
    change (∏ i, χ i (e (Ideal.Quotient.mk (Ideal.span {c}) z) i)) =
      ∏ i, χ i (Ideal.Quotient.mk (P i) z)
    simp only [he]
  have hG : primeRowTraceGauss p hp χ = ∑ x, A x*ψ x := by
    unfold primeRowTraceGauss
    apply Finset.sum_congr rfl
    intro x _
    have hx := ha (GaussianShiftedPartition.representative c x)
    rw [GaussianShiftedPartition.representative_spec c x] at hx
    rw [←hx]
  constructor
  · rw [hG,finite_crt_gauss_norm_sq (fun i => O ⧸ P i) e χ hχ ψ
      (residueTraceQuotientChar_primitive c hc)]
    simpa only [Ideal.absNorm_apply,Submodule.cardQuot_apply,Nat.card_eq_fintype_card]
      using (ringComplex_norm_sq_eq_absNorm_span c).symm
  · intro W Y hY
    have hf := actual_radial_poisson_trace W Y hY c hc A
    simp_rw [ha] at hf
    rw [hf]
    change ((Y/‖ringComplex c‖ ^ 2 : ℝ) : ℂ)*
      (∑' h : O, (∑ x, A x*ψ (Ideal.Quotient.mk (Ideal.span {c}) h*x))*
        paperRadialFourier W (Y*‖ringComplex h‖ ^ 2/‖ringComplex c‖ ^ 2)) = _
    have ht (h : O) : (∑ x, A x*ψ (Ideal.Quotient.mk (Ideal.span {c}) h*x)) =
        primeCuspRowCharacter p (fun i => (χ i)⁻¹) h*primeRowTraceGauss p hp χ := by
      rw [hG]
      change (∑ x, A x*ψ (Ideal.Quotient.mk (Ideal.span {c}) h*x)) =
        (∏ i, (χ i)⁻¹ (Ideal.Quotient.mk (P i) h))*(∑ x, A x*ψ x)
      simpa only [A,he] using
        finite_crt_gauss_transform (fun i => O ⧸ P i) e χ hχ ψ (Ideal.Quotient.mk (Ideal.span {c}) h)
    simp_rw [ht]
    have hs : (∑' h : O, (primeCuspRowCharacter p (fun i => (χ i)⁻¹) h*primeRowTraceGauss p hp χ)*
        paperRadialFourier W (Y*‖ringComplex h‖ ^ 2/‖ringComplex c‖ ^ 2)) =
        primeRowTraceGauss p hp χ*∑' h : O, primeCuspRowCharacter p (fun i => (χ i)⁻¹) h*
          paperRadialFourier W (Y*‖ringComplex h‖ ^ 2/‖ringComplex c‖ ^ 2) := by
      rw [←tsum_mul_left]
      apply tsum_congr
      intro h
      ring
    rw [hs]
    push_cast
    ring

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein
open scoped Classical SchwartzMap

theorem prime_row_trace_masked_poisson {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (hχ : ∀ i, χ i ≠ 1) :
    ∀ {κ : Type*} (q : κ → O) (hq : ∀ i, q i ≠ 0)
      (hcop : Pairwise (Function.onFun IsCoprime q)) (S : Finset κ)
      (W : 𝓢(ℝ, ℂ)) (Y : ℝ), 0 < Y →
      (∑' z : O, primeCoprimeMask q S z * primeCuspRowCharacter p χ z *
        W (‖ringComplex z‖ ^ 2 / Y)) =
        ((Y : ℂ)*primeRowTraceGauss p hp χ/(‖ringComplex (∏ i, p i)‖ ^ 2 : ℝ)) *
          ∑ E ∈ S.powerset,
            ((-1 : ℂ) ^ E.card * primeCuspRowCharacter p χ (∏ i ∈ E, q i) /
              (‖ringComplex (∏ i ∈ E, q i)‖ ^ 2 : ℝ)) *
              ∑' h : O, primeCuspRowCharacter p (fun i => (χ i)⁻¹) h *
                paperRadialFourier W
                  (Y * ‖ringComplex h‖ ^ 2 /
                    (‖ringComplex (∏ i ∈ E, q i)‖ ^ 2 * ‖ringComplex (∏ i, p i)‖ ^ 2)) := by
  classical
  have hP := (prime_row_trace_poisson p hp hinj χ hχ).2
  intro κ q hq hcop S W Y hY
  rw [prime_row_masked_dilations p χ q hq hcop S W Y hY, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro E hE
  have hd : (∏ i ∈ E, q i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hq i)
  have hn : 0 < ‖ringComplex (∏ i ∈ E, q i)‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr (ringComplex_ne_zero hd))
  rw [hP W _ (div_pos hY hn)]
  have harg (h : O) :
      Y / ‖ringComplex (∏ i ∈ E, q i)‖ ^ 2 * ‖ringComplex h‖ ^ 2 /
          ‖ringComplex (∏ i, p i)‖ ^ 2 =
        Y * ‖ringComplex h‖ ^ 2 /
          (‖ringComplex (∏ i ∈ E, q i)‖ ^ 2 * ‖ringComplex (∏ i, p i)‖ ^ 2) := by ring
  simp_rw [harg]
  push_cast
  ring


end SchwartzPlanePoisson

namespace CoprimeMobiusExtension
open scoped Classical

theorem sum_subset_sign {ι : Type*} [DecidableEq ι] (S : Finset ι) :
    (∑ D ∈ S.powerset, (-1 : ℂ) ^ D.card) = if S = ∅ then 1 else 0 := by
  have hp := Finset.prod_sub (fun _ : ι => (1 : ℂ)) (fun _ => 1) S
  by_cases hS : S = ∅
  · simp [hS]
  · have hc : S.card ≠ 0 := Finset.card_ne_zero.mpr (Finset.nonempty_iff_ne_empty.mpr hS)
    simpa [hS, hc] using hp.symm

theorem disjoint_indicator_expansion {ι : Type*} [DecidableEq ι]
    (B S T : Finset ι) (hS : S ⊆ B) (_hT : T ⊆ B) :
    (if Disjoint S T then (1 : ℂ) else 0) =
      ∑ D ∈ B.powerset, if D ⊆ S ∧ D ⊆ T then (-1 : ℂ) ^ D.card else 0 := by
  have hsub : (S ∩ T).powerset ⊆ B.powerset :=
    Finset.powerset_mono.mpr (Finset.inter_subset_left.trans hS)
  have heq : (∑ D ∈ B.powerset, if D ⊆ S ∧ D ⊆ T then (-1 : ℂ) ^ D.card else 0) =
      ∑ D ∈ (S ∩ T).powerset, (-1 : ℂ) ^ D.card := by
    calc
      _ = ∑ D ∈ (S ∩ T).powerset,
            if D ⊆ S ∧ D ⊆ T then (-1 : ℂ) ^ D.card else 0 := by
        symm
        apply Finset.sum_subset hsub
        intro D hD hnot
        have hn : ¬(D ⊆ S ∧ D ⊆ T) := by
          simpa only [Finset.mem_powerset, Finset.subset_inter_iff] using hnot
        simp [hn]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro D hD
        have hh : D ⊆ S ∧ D ⊆ T := by
          simpa only [Finset.mem_powerset, Finset.subset_inter_iff] using hD
        simp [hh]
  rw [heq, sum_subset_sign]
  simp only [Finset.disjoint_iff_inter_eq_empty]

theorem double_sum_disjoint_expansion {ι : Type*} [DecidableEq ι]
    (B : Finset ι) (Z : Finset ι → Finset ι → ℂ) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset, if Disjoint S T then Z S T else 0) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        ∑ S ∈ B.powerset, ∑ T ∈ B.powerset,
          if D ⊆ S ∧ D ⊆ T then Z S T else 0 := by
  have hp (S T : Finset ι) (hS : S ∈ B.powerset) (hT : T ∈ B.powerset) :
      (if Disjoint S T then Z S T else 0) =
        ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
          if D ⊆ S ∧ D ⊆ T then Z S T else 0 := by
    calc
      _ = (if Disjoint S T then (1 : ℂ) else 0) * Z S T := by split_ifs <;> simp
      _ = (∑ D ∈ B.powerset,
          if D ⊆ S ∧ D ⊆ T then (-1 : ℂ) ^ D.card else 0) * Z S T := by
        rw [disjoint_indicator_expansion B S T (Finset.mem_powerset.mp hS)
          (Finset.mem_powerset.mp hT)]
      _ = _ := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro D hD
        split_ifs <;> simp
  calc
    _ = ∑ S ∈ B.powerset, ∑ T ∈ B.powerset, ∑ D ∈ B.powerset,
        (-1 : ℂ) ^ D.card * if D ⊆ S ∧ D ⊆ T then Z S T else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      exact Finset.sum_congr rfl (fun T hT => hp S T hS hT)
    _ = _ := by
      simp_rw [Finset.mul_sum]
      calc
        _ = ∑ S ∈ B.powerset, ∑ D ∈ B.powerset, ∑ T ∈ B.powerset,
            (-1 : ℂ) ^ D.card * if D ⊆ S ∧ D ⊆ T then Z S T else 0 := by
          apply Finset.sum_congr rfl
          intro S hS
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm

theorem sum_supersets {ι : Type*} [DecidableEq ι]
    (B D : Finset ι) (hD : D ⊆ B) (f : Finset ι → ℂ) :
    (∑ S ∈ B.powerset, if D ⊆ S then f S else 0) =
      ∑ U ∈ (B \ D).powerset, f (D ∪ U) := by
  rw [← Finset.sum_filter]
  refine Finset.sum_bij (fun S _ => S \ D) ?_ ?_ ?_ ?_
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS ⊢
    exact Finset.sdiff_subset_sdiff hS.1 (Finset.Subset.refl _)
  · intro S hS T hT heq
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS hT
    have he := congrArg (fun U => D ∪ U) heq
    simpa [Finset.union_sdiff_of_subset hS.2, Finset.union_sdiff_of_subset hT.2] using he
  · intro U hU
    have hUB : U ⊆ B \ D := Finset.mem_powerset.mp hU
    refine ⟨D ∪ U, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.union_subset hD (hUB.trans Finset.sdiff_subset), Finset.subset_union_left⟩
    · apply Finset.union_sdiff_cancel_left
      exact (Finset.disjoint_of_subset_right hUB disjoint_sdiff_self_right)
  · intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS
    rw [Finset.union_sdiff_of_subset hS.2]

theorem double_sum_disjoint_reindexed {ι : Type*} [DecidableEq ι]
    (B : Finset ι) (Z : Finset ι → Finset ι → ℂ) :
    (∑ S ∈ B.powerset, ∑ T ∈ B.powerset, if Disjoint S T then Z S T else 0) =
      ∑ D ∈ B.powerset, (-1 : ℂ) ^ D.card *
        ∑ U ∈ (B \ D).powerset, ∑ V ∈ (B \ D).powerset, Z (D ∪ U) (D ∪ V) := by
  rw [double_sum_disjoint_expansion]
  apply Finset.sum_congr rfl
  intro D hD
  congr 1
  have hDB := Finset.mem_powerset.mp hD
  calc
    _ = ∑ S ∈ B.powerset, if D ⊆ S then
          (∑ T ∈ B.powerset, if D ⊆ T then Z S T else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro S hS
      by_cases hh : D ⊆ S <;> simp [hh]
    _ = _ := by
      rw [sum_supersets B D hDB]
      apply Finset.sum_congr rfl
      intro U hU
      exact sum_supersets B D hDB (Z (D ∪ U))

end CoprimeMobiusExtension

namespace SchwartzPlanePoisson
open Eisenstein MulChar AddChar
open scoped Classical

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))

include hinj

lemma primeRowTraceGauss_eq_crt (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) :
    let hc := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
    letI : Finite (O ⧸ Ideal.span {∏ i, p i}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {∏ i, p i}) := Fintype.ofFinite _
    primeRowTraceGauss p hp χ = ∑ x : O ⧸ Ideal.span {∏ i, p i},
      (∏ i, χ i (primeProductCRT p hinj x i))*residueTraceQuotientChar 1 _ hc x := by
  dsimp only
  unfold primeRowTraceGauss
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  change (∏ i, χ i (Ideal.Quotient.mk (Ideal.span {p i})
    (GaussianShiftedPartition.representative (∏ i, p i) x))) = _
  conv_rhs => rw [←GaussianShiftedPartition.representative_spec (∏ i, p i) x]
  simp only [primeProductCRT_mk]

lemma primeRowTraceGauss_ne_zero
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (hχ : ∀ i, χ i ≠ 1) :
    primeRowTraceGauss p hp χ ≠ 0 := by
  have hc : ringComplex (∏ i, p i) ≠ 0 :=
    ringComplex_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))
  have hn := (prime_row_trace_poisson p hp hinj χ hχ).1
  intro hz
  rw [hz,norm_zero,zero_pow (by decide)] at hn
  exact (pow_pos (norm_pos_iff.mpr hc) 2).ne' hn.symm

/-- The quadratic trace Gauss factor is the explicit phase modulo four. -/
theorem primeRowTraceGauss_quadratic
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2) :
    primeRowTraceGauss p hp (fun i => complexQuadraticChar (Ideal.span {p i})) =
      (‖ringComplex (∏ i, p i)‖ : ℂ)*QuadraticPhase.Eisenstein.fixedDualAverage (∏ i, p i) := by
  let c := ∏ i, p i
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [primeRowTraceGauss_eq_crt p hp hinj]
  change (∑ x : O ⧸ Ideal.span {c},
    (∏ i, ((quadraticChar (O ⧸ Ideal.span {p i})).ringHomComp (Int.castRingHom ℂ))
      (primeProductCRT p hinj x i))*residueTraceQuotientChar 1 c hc x) = _
  rw [QuadraticPhase.ProductGauss.quadratic_factorization_equiv
    (fun i => O ⧸ Ideal.span {p i}) (primeProductCRT p hinj)
    (residueTraceQuotientChar 1 c hc) (residueTraceQuotientChar_primitive c hc) hodd]
  simp only [residueTraceQuotientChar_eq_principal]
  change QuadraticPhase.Eisenstein.quadraticTraceGauss c hc = _
  have hn : (‖ringComplex c‖ : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (ringComplex_ne_zero hc))
  exact ((div_eq_iff hn).mp
    (QuadraticPhase.Eisenstein.normalizedQuadraticTraceGauss_eq_fixedDualAverage c hc)).trans
      (mul_comm _ _)

/-- The primary local cubic identity multiplies to the signed sextic–cubic–quadratic identity. -/
theorem primeRowTraceGauss_sextic_product
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i-1) :
    (∏ i, complexSexticChar (Ideal.span {p i}) (hg i) (4 : O ⧸ Ideal.span {p i}))*
      primeRowTraceGauss p hp (fun i => complexSexticChar (Ideal.span {p i}) (hg i))*
      primeRowTraceGauss p hp (fun i => complexCubicChar (Ideal.span {p i}) (hg i)) =
    (-1 : ℂ) ^ Fintype.card ι*ringComplex (∏ i, p i)*
      primeRowTraceGauss p hp (fun i => complexQuadraticChar (Ideal.span {p i})) := by
  let c := ∏ i, p i
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let F := fun i => O ⧸ Ideal.span {p i}
  let ψ := residueTraceQuotientChar 1 c hc
  let η := ψ.compAddMonoidHom (primeProductCRT p hinj).symm.toAddMonoidHom
  have hη : η.IsPrimitive := ProductGauss.primitive_comp_ringEquiv _ ψ
    (residueTraceQuotientChar_primitive c hc)
  have hl (i : ι) : complexSexticChar (Ideal.span {p i}) (hg i) (4 : F i)*
      gaussSum (complexSexticChar (Ideal.span {p i}) (hg i)) (ProductGauss.localChar F η i)*
      gaussSum (complexCubicChar (Ideal.span {p i}) (hg i)) (ProductGauss.localChar F η i) =
      -ringComplex (p i)*gaussSum (complexQuadraticChar (Ideal.span {p i}))
        (ProductGauss.localChar F η i) := by
    have h := sextic_cubic_gauss_product (Ideal.span {p i}) (hg i) (hodd i) _
      (ProductGauss.localChar_primitive F η hη i)
    rw [←primaryGenerator_unique (Ideal.span {p i}) (hg i) (p i) rfl (hpr i)] at h
    exact h
  rw [primeRowTraceGauss_eq_crt p hp hinj,primeRowTraceGauss_eq_crt p hp hinj,
    primeRowTraceGauss_eq_crt p hp hinj]
  rw [ProductGauss.factorization_equiv F (primeProductCRT p hinj),
    ProductGauss.factorization_equiv F (primeProductCRT p hinj),
    ProductGauss.factorization_equiv F (primeProductCRT p hinj)]
  rw [←Finset.prod_mul_distrib,←Finset.prod_mul_distrib]
  trans ∏ i, -ringComplex (p i)*gaussSum (complexQuadraticChar (Ideal.span {p i}))
    (ProductGauss.localChar F η i)
  · exact Finset.prod_congr rfl (fun i _ => hl i)
  · rw [Finset.prod_mul_distrib,Finset.prod_neg,Finset.card_univ,map_prod]

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein
open scoped Classical

/-- Gauss sum of an integral multiplicative row, using the fixed trace character. -/
def residueRowGauss (c : O) (hc : c ≠ 0) (A : O → ℂ) : ℂ :=
  ∑' x : O ⧸ Ideal.span {c}, A (qrep x)*residueTraceQuotientChar 1 c hc x

lemma periodicRow_qrep_mk (c : O) (A : O → ℂ)
    (hA : ∀ x y, c ∣ x-y → A x = A y) (z : O) :
    A (qrep (Ideal.Quotient.mk (Ideal.span {c}) z)) = A z := by
  apply hA
  exact Ideal.mem_span_singleton.mp (Ideal.Quotient.eq.mp (mk_qrep _))

lemma primeCuspRowCharacter_congr {ι : Type*} [Fintype ι] (p : ι → O)
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (x y : O)
    (h : (∏ i, p i) ∣ x-y) : primeCuspRowCharacter p χ x = primeCuspRowCharacter p χ y := by
  change (∏ i, χ i (Ideal.Quotient.mk (Ideal.span {p i}) x)) =
    ∏ i, χ i (Ideal.Quotient.mk (Ideal.span {p i}) y)
  apply Finset.prod_congr rfl
  intro i _
  congr 1
  exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr
    ((Finset.dvd_prod_of_mem p (Finset.mem_univ i)).trans h))

lemma primeRowTraceGauss_eq_residueRowGauss {ι : Type*} [Fintype ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0)
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) :
    primeRowTraceGauss p hp χ = residueRowGauss (∏ i, p i)
      (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)) (primeCuspRowCharacter p χ) := by
  have hc : (∏ i, p i) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  letI : Finite (O ⧸ Ideal.span {∏ i, p i}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {∏ i, p i}) := Fintype.ofFinite _
  rw [primeRowTraceGauss,residueRowGauss,tsum_fintype]
  apply Finset.sum_congr rfl
  intro x _
  congr 1

/-- The linear CRT parametrization splits the trace phase without inverse coefficients. -/
lemma residueTraceChar_crt_linear (c d : O) (hc : c ≠ 0) (hd : d ≠ 0) (x y : O) :
    residueTraceQuotientChar 1 (c*d) (mul_ne_zero hc hd)
      (Ideal.Quotient.mk (Ideal.span {c*d}) (d*x+c*y)) =
    residueTraceQuotientChar 1 c hc (Ideal.Quotient.mk (Ideal.span {c}) x)*
      residueTraceQuotientChar 1 d hd (Ideal.Quotient.mk (Ideal.span {d}) y) := by
  rw [residueTraceQuotientChar_phase,residueTraceQuotientChar_phase,
    residueTraceQuotientChar_phase,←AddChar.map_add_eq_mul]
  congr 1
  simp only [one_mul,map_mul,map_add]
  field_simp [ringComplex_ne_zero hc,ringComplex_ne_zero hd,
    ringComplex_ne_zero traceLambda_ne_zero]

/-- Coprime periodic multiplicative rows split with their reciprocal cross values. -/
theorem residueRowGauss_mul (c d : O) (hc : c ≠ 0) (hd : d ≠ 0)
    (hcd : IsCoprime c d) (A B : O →* ℂ)
    (hA : ∀ x y, c ∣ x-y → A x = A y)
    (hB : ∀ x y, d ∣ x-y → B x = B y) :
    residueRowGauss (c*d) (mul_ne_zero hc hd) (A*B) =
      A d*B c*residueRowGauss c hc A*residueRowGauss d hd B := by
  letI : NeZero c := ⟨hc⟩
  letI : NeZero d := ⟨hd⟩
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Finite (O ⧸ Ideal.span {d}) := finite_quotient_span hd
  letI : Finite (O ⧸ Ideal.span {c*d}) := finite_quotient_span (mul_ne_zero hc hd)
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  letI : Fintype (O ⧸ Ideal.span {d}) := Fintype.ofFinite _
  letI : Fintype (O ⧸ Ideal.span {c*d}) := Fintype.ofFinite _
  have hAB (x y : O) (h : c*d ∣ x-y) : (A*B) x = (A*B) y := by
    rw [MonoidHom.mul_apply,MonoidHom.mul_apply,
      hA x y ((dvd_mul_right c d).trans h),hB x y ((dvd_mul_left d c).trans h)]
  have hleft (x y : O) : A (d*x+c*y) = A d*A x := by
    rw [hA (d*x+c*y) (d*x) (by convert dvd_mul_right c y using 1 <;> ring),map_mul]
  have hright (x y : O) : B (d*x+c*y) = B c*B y := by
    rw [hB (d*x+c*y) (c*y) (by convert dvd_mul_right d x using 1 <;> ring),map_mul]
  simp only [residueRowGauss,tsum_fintype]
  rw [←Fintype.sum_bijective _ (crtParam_bijective c d hcd)
    (fun z => (A*B) (qrep (crtParam c d z))*
      residueTraceQuotientChar 1 (c*d) (mul_ne_zero hc hd) (crtParam c d z)) _
    (fun _ => rfl),Fintype.sum_prod_type]
  simp only [Finset.mul_sum,Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  dsimp only [crtParam]
  rw [periodicRow_qrep_mk (c*d) ((A*B : O →* ℂ) : O → ℂ) hAB,MonoidHom.mul_apply,
    hleft,hright,residueTraceChar_crt_linear c d hc hd,mk_qrep,mk_qrep]
  ring

end SchwartzPlanePoisson

namespace SchwartzPlanePoisson
open Eisenstein
open scoped Classical

lemma finiteGauss_inverse_character {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    gaussSum χ⁻¹ ψ = χ (-1)*star (gaussSum χ ψ) := by
  have hψ : ψ⁻¹ = ψ.mulShift (-1) := by
    ext x
    simp only [AddChar.inv_apply,AddChar.mulShift_apply,neg_one_mul]
  have hstar : star (gaussSum χ ψ) = χ (-1)*gaussSum χ⁻¹ ψ := by
    rw [star_gaussSum_eq,hψ]
    simpa only [Units.val_neg,Units.val_one,inv_inv] using
      gaussSum_mulShift_eq χ⁻¹ ψ (-1 : Fˣ)
  have hs : χ (-1)*χ (-1) = 1 := by rw [←map_mul,neg_mul_neg,one_mul,map_one]
  rw [hstar,←mul_assoc,hs,one_mul]

/-- Inverting all prime characters conjugates the exact trace Gauss factor. -/
theorem primeRowTraceGauss_inverse {ι : Type*} [Fintype ι] [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) :
    primeRowTraceGauss p hp (fun i => (χ i)⁻¹) =
      primeCuspRowCharacter p χ (-1)*star (primeRowTraceGauss p hp χ) := by
  let c := ∏ i, p i
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  rw [primeRowTraceGauss_eq_crt p hp hinj,primeRowTraceGauss_eq_crt p hp hinj]
  rw [ProductGauss.factorization_equiv (fun i => O ⧸ Ideal.span {p i}) (primeProductCRT p hinj),
    ProductGauss.factorization_equiv (fun i => O ⧸ Ideal.span {p i}) (primeProductCRT p hinj)]
  simp_rw [finiteGauss_inverse_character]
  rw [Finset.prod_mul_distrib,←star_prod]
  congr 1

end SchwartzPlanePoisson

namespace SecondPassFiber
open Eisenstein
open scoped Classical

@[ext] structure OldTuple where
  core : Fin 8 → Ideal O
  v : Ideal O
  j2 : Ideal O
  b2 : Ideal O
  row : O

structure Valid (x : OldTuple) (F b0 : Ideal O) (y : O) : Prop where
  label : x.core 0 * x.core 1 * x.core 2 * x.v = F
  j_split : x.core 3 * x.j2 = x.core 0
  b_split : x.core 4 * x.b2 = b0 ^ 2 * x.j2 ^ 2 * x.core 3
  a1 : x.core 5 ∣ x.core 4 * x.b2
  a2 : x.core 6 ∣ x.core 4 * x.b2
  d : x.core 7 ∣ F * b0
  row_eq : cubicIdealGenerator (x.core 7) * cubicIdealGenerator (x.core 2) * x.row = y

def divisorTarget (F b0 : Ideal O) : Ideal O := (F * b0) ^ 2

theorem core_dvd_target (x : OldTuple) (F b0 : Ideal O) (y : O)
    (h : Valid x F b0 y) (i : Fin 8) : x.core i ∣ divisorTarget F b0 := by
  have hJ : x.core 0 ∣ F := by
    rw [← h.label]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_right _ _) _) _
  have hC : x.core 1 ∣ F := by
    rw [← h.label]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (dvd_mul_left _ _) _) _
  have he : x.core 2 ∣ F := by
    rw [← h.label]
    exact dvd_mul_of_dvd_left (dvd_mul_left _ _) _
  have hs : x.core 3 ∣ F := by
    apply dvd_trans _ hJ
    rw [← h.j_split]
    exact dvd_mul_right _ _
  have hFT : F ∣ divisorTarget F b0 := by
    dsimp [divisorTarget]
    exact (dvd_mul_right F b0).trans (dvd_pow_self _ (by decide))
  have hbprod : x.core 4 * x.b2 ∣ divisorTarget F b0 := by
    apply dvd_trans (b := b0 ^ 2 * x.core 0 ^ 2)
    · refine ⟨x.core 3, ?_⟩
      rw [h.b_split, ← h.j_split]
      ring
    · dsimp [divisorTarget]
      rw [mul_pow, mul_comm (F ^ 2)]
      exact mul_dvd_mul_left _ (pow_dvd_pow_of_dvd hJ 2)
  fin_cases i
  · exact hJ.trans hFT
  · exact hC.trans hFT
  · exact he.trans hFT
  · exact hs.trans hFT
  · exact (dvd_mul_right _ _).trans hbprod
  · exact h.a1.trans hbprod
  · exact h.a2.trans hbprod
  · exact h.d.trans (dvd_pow_self _ (by decide))

theorem target_ne_zero (F b0 : Ideal O) (hF : F ≠ ⊥) (hb0 : b0 ≠ ⊥) :
    divisorTarget F b0 ≠ 0 := pow_ne_zero _ (mul_ne_zero hF hb0)

theorem core_ne_zero (x : OldTuple) (F b0 : Ideal O) (y : O)
    (hF : F ≠ ⊥) (hb0 : b0 ≠ ⊥) (h : Valid x F b0 y) (i : Fin 8) :
    x.core i ≠ 0 := by
  intro he
  have hd := core_dvd_target x F b0 y h i
  rw [he, zero_dvd_iff] at hd
  exact target_ne_zero F b0 hF hb0 hd

theorem valid_core_injective (F b0 : Ideal O) (y : O)
    (hF : F ≠ ⊥) (hb0 : b0 ≠ ⊥) {x z : OldTuple}
    (hx : Valid x F b0 y) (hz : Valid z F b0 y) (hcore : x.core = z.core) : x = z := by
  have hc (i : Fin 8) : x.core i = z.core i := congrFun hcore i
  have hv : x.v = z.v := by
    apply mul_left_cancel₀
      (mul_ne_zero (mul_ne_zero (core_ne_zero x F b0 y hF hb0 hx 0)
        (core_ne_zero x F b0 y hF hb0 hx 1)) (core_ne_zero x F b0 y hF hb0 hx 2))
    calc
      _ = F := hx.label
      _ = _ := by simpa only [hc] using hz.label.symm
  have hj : x.j2 = z.j2 := by
    apply mul_left_cancel₀ (core_ne_zero x F b0 y hF hb0 hx 3)
    calc
      _ = x.core 0 := hx.j_split
      _ = _ := by simpa only [hc] using hz.j_split.symm
  have hb : x.b2 = z.b2 := by
    apply mul_left_cancel₀ (core_ne_zero x F b0 y hF hb0 hx 4)
    calc
      _ = b0 ^ 2 * x.j2 ^ 2 * x.core 3 := hx.b_split
      _ = _ := by simpa only [hc, hj] using hz.b_split.symm
  have hgen (i : Fin 8) : cubicIdealGenerator (x.core i) ≠ 0 := by
    intro he
    apply core_ne_zero x F b0 y hF hb0 hx i
    rw [← span_cubicIdealGenerator (x.core i), he]
    simp
  have hr : x.row = z.row := by
    apply mul_left_cancel₀ (mul_ne_zero (hgen 7) (hgen 2))
    calc
      _ = y := hx.row_eq
      _ = _ := by simpa only [hc] using hz.row_eq.symm
  exact OldTuple.ext hcore hv hj hb hr

theorem valid_tuple_card_le (s : Finset OldTuple) (F b0 : Ideal O) (y : O)
    (hF : F ≠ ⊥) (hb0 : b0 ≠ ⊥) (hs : ∀ x ∈ s, Valid x F b0 y) :
    s.card ≤ (idealDivisors (divisorTarget F b0)).card ^ 8 := by
  let D := idealDivisors (divisorTarget F b0)
  let encode (x : s) : Fin 8 → D := fun i => ⟨x.val.core i, by
    apply (mem_idealDivisors (target_ne_zero F b0 hF hb0)).mpr
    exact core_dvd_target x.val F b0 y (hs x.val x.property) i⟩
  have hinj : Function.Injective encode := by
    intro x z he
    apply Subtype.ext
    apply valid_core_injective F b0 y hF hb0 (hs x.val x.property) (hs z.val z.property)
    funext i
    exact congrArg Subtype.val (congrFun he i)
  have hc := Fintype.card_le_of_injective encode hinj
  simpa [D] using hc

theorem valid_tuple_small_power (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset OldTuple) (F b0 : Ideal O) (y : O),
      F ≠ ⊥ → b0 ≠ ⊥ → (∀ x ∈ s, Valid x F b0 y) →
      (s.card : ℝ) ≤ C * ((Ideal.absNorm F : ℝ) * Ideal.absNorm b0) ^ ε := by
  obtain ⟨C, hC, h⟩ := IdealDivisorBound.ideal_divisor_small_power (ε / 16) (by positivity)
  refine ⟨C ^ 8, by positivity, ?_⟩
  intro s F b0 y hF hb0 hs
  have hc : (s.card : ℝ) ≤ ((idealDivisors (divisorTarget F b0)).card : ℝ) ^ 8 := by
    exact_mod_cast valid_tuple_card_le s F b0 y hF hb0 hs
  have hd := pow_le_pow_left₀ (by positivity)
    (h (divisorTarget F b0) (target_ne_zero F b0 hF hb0)) 8
  apply hc.trans (hd.trans_eq ?_)
  rw [mul_pow]
  congr 1
  simp only [divisorTarget, map_pow, map_mul, Nat.cast_pow, Nat.cast_mul]
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  congr 1
  ring

def newLabel (x : OldTuple) : Ideal O := x.core 0 * x.core 1 * x.core 2 * x.v
def newRow (x : OldTuple) : O :=
  cubicIdealGenerator (x.core 7) * cubicIdealGenerator (x.core 2) * x.row

theorem second_energy_pushforward (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : Finset OldTuple) (t : Finset (Ideal O × O))
      (b0 : Ideal O) (w : OldTuple → ℂ) (P : Ideal O × O → ℂ) (B H : ℝ),
      b0 ≠ ⊥ → 0 ≤ B → 0 ≤ H →
      (∀ x ∈ s, Valid x (newLabel x) b0 (newRow x)) →
      (∀ x ∈ s, (newLabel x, newRow x) ∈ t) →
      (∀ z ∈ t, z.1 ≠ ⊥) →
      (∀ z ∈ t, (Ideal.absNorm z.1 : ℝ) ≤ H) →
      (∀ x ∈ s, ‖w x‖ ≤ B) →
      (∑ x ∈ s, ‖w x‖ * ‖P (newLabel x, newRow x)‖ ^ 2) ≤
        B * C * (H * Ideal.absNorm b0) ^ ε * ∑ z ∈ t, ‖P z‖ ^ 2 := by
  obtain ⟨C, hC, hc⟩ := valid_tuple_small_power ε hε
  refine ⟨C, hC, ?_⟩
  intro s t b0 w P B H hb0 hB hH hvalid hmap ht hnorm hw
  have hpush := DescentWeightedCauchy.bounded_energy_pushforward
    s t (fun x => (newLabel x, newRow x)) w P B hmap hw
  apply hpush.trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro z hz
  have hval : ∀ x ∈ s.filter (fun x => (newLabel x, newRow x) = z), Valid x z.1 b0 z.2 := by
    intro x hx
    have he := (Finset.mem_filter.mp hx).2
    have hv := hvalid x (Finset.mem_filter.mp hx).1
    have h1 : newLabel x = z.1 := congrArg Prod.fst he
    have h2 : newRow x = z.2 := congrArg Prod.snd he
    simpa only [h1, h2] using hv
  have hfiber := hc (s.filter (fun x => (newLabel x, newRow x) = z)) z.1 b0 z.2
    (ht z hz) hb0 hval
  have hgrowth : (Ideal.absNorm z.1 : ℝ) * Ideal.absNorm b0 ≤ H * Ideal.absNorm b0 :=
    mul_le_mul_of_nonneg_right (hnorm z hz) (by positivity)
  have hcard := hfiber.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow (by positivity) hgrowth hε.le) hC.le)
  have hterm := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hcard hB) (sq_nonneg ‖P z‖)
  simpa only [mul_assoc] using hterm


end SecondPassFiber

open scoped Classical SchwartzMap FourierTransform ContDiff
open scoped Classical
open scoped Classical
open scoped Classical
open scoped Classical SchwartzMap
open MeasureTheory
open scoped BigOperators Classical ContDiff SchwartzMap FourierTransform
open MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

namespace CanonicalQuadraticSieve
open Eisenstein
/-- Nonzero squarefree ideals with every prime factor outside two and three. -/
def Admissible (I : Ideal O) : Prop :=
  I ≠ 0 ∧ Squarefree I ∧ ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
    lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2
/-- Prime support outside two and three, allowing repeated factors. -/
def Supported (I : Ideal O) : Prop :=
  I ≠ 0 ∧ ∀ P ∈ UniqueFactorizationMonoid.normalizedFactors I,
    lambda ∉ P ∧ ringChar (O ⧸ P) ≠ 2
lemma admissible_supported {I : Ideal O} (hI : Admissible I) : Supported I := ⟨hI.1,hI.2.2⟩
end CanonicalQuadraticSieve

namespace CanonicalQuadraticSieve
open Eisenstein SchwartzPlanePoisson
open scoped Classical

/-- Prime-support admissibility is exactly the native quadratic sieve condition. -/
theorem admissible_iff_native (I:Ideal O) : Admissible I ↔ quadraticIdealAdmissible I := by
  constructor
  · intro h
    refine ⟨primaryIdealGenerator_ne_zero_of_good_factors I h.1 (fun P hP => (h.2.2 P hP).1),h.2.1,?_⟩
    intro P hP
    exact (h.2.2 P (Multiset.mem_toFinset.mp hP)).2
  · intro h
    refine ⟨primaryIdealGenerator_ne_zero_ideal I h.1,h.2.1,?_⟩
    intro P hP
    exact ⟨(primaryIdealPrime_spec P (primaryIdealPrime_factor_ne_zero I P h.1 hP)).2.1,
      h.2.2 P (Multiset.mem_toFinset.mpr hP)⟩

lemma supported_mul_iff (I J:Ideal O) : Supported (I*J) ↔ Supported I ∧ Supported J := by
  by_cases hI:I=0
  · subst I
    simp only [zero_mul,Supported,ne_eq,not_true_eq_false,false_and]
  by_cases hJ:J=0
  · subst J
    simp only [mul_zero,Supported,ne_eq,not_true_eq_false,false_and,and_false]
  simp only [Supported,UniqueFactorizationMonoid.normalizedFactors_mul hI hJ,Multiset.mem_add]
  constructor
  · intro h
    exact ⟨⟨hI,fun P hP=>h.2 P (Or.inl hP)⟩,⟨hJ,fun P hP=>h.2 P (Or.inr hP)⟩⟩
  · rintro ⟨hI',hJ'⟩
    refine ⟨mul_ne_zero hI hJ,?_⟩
    intro P hP
    exact hP.elim (hI'.2 P) (hJ'.2 P)

lemma supported_pow {I:Ideal O} (hI:Supported I) (k:ℕ) : Supported (I ^ k) := by
  induction k with
  | zero =>
    refine ⟨by simp,?_⟩
    intro P hP
    simp only [pow_zero,UniqueFactorizationMonoid.normalizedFactors_one,Multiset.notMem_zero] at hP
  | succ k ih =>
    rw [pow_succ,supported_mul_iff]
    exact ⟨ih,hI⟩
end CanonicalQuadraticSieve

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
