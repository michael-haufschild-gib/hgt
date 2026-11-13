/-
First-pass Gauss blocks adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.CubeCoordinatesAndGlobalData

/-!
# First-pass Gauss blocks

Disjoint conductors split the trace Gauss sum with both cross-row factors; local Gauss blocks
multiply to the normalized sum. The first reflection leaves the conjugate ray factor after
cubic cancellation; dilated core rows and the first cube energy.
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

namespace SecondPassArithmetic
open Eisenstein SchwartzPlanePoisson
open scoped Classical

/-- Disjoint conductors split the trace Gauss sum with both cross-row factors. -/
theorem subsetTraceGauss_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (S T : Finset ι) (hd : Disjoint S T) :
    subsetTraceGauss p hp χ (S ∪ T) =
      primeSubsetRow p χ S (∏ i ∈ T, p i) * primeSubsetRow p χ T (∏ i ∈ S, p i) *
        subsetTraceGauss p hp χ S * subsetTraceGauss p hp χ T := by
  let c := ∏ i ∈ S, p i
  let d := ∏ i ∈ T, p i
  have hc : c ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  have hd0 : d ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)
  let A := primeCuspRowCharacter (fun i : S => p i.val) (fun i => χ i.val)
  let B := primeCuspRowCharacter (fun i : T => p i.val) (fun i => χ i.val)
  have hA (z : O) : A z = primeSubsetRow p χ S z := primeCuspRowCharacter_restrict p χ S z
  have hB (z : O) : B z = primeSubsetRow p χ T z := primeCuspRowCharacter_restrict p χ T z
  have hAc (x y : O) (h : c ∣ x-y) : A x = A y := by
    rw [hA, hA]
    exact primeSubsetRow_congr p χ S x y h
  have hBd (x y : O) (h : d ∣ x-y) : B x = B y := by
    rw [hB, hB]
    exact primeSubsetRow_congr p χ T x y h
  have ha : residueRowGauss c hc A = subsetTraceGauss p hp χ S := by
    rw [show (A : O → ℂ) = primeSubsetRow p χ S from funext hA]
    exact (subsetTraceGauss_eq_residueRowGauss p hp χ S).symm
  have hb : residueRowGauss d hd0 B = subsetTraceGauss p hp χ T := by
    rw [show (B : O → ℂ) = primeSubsetRow p χ T from funext hB]
    exact (subsetTraceGauss_eq_residueRowGauss p hp χ T).symm
  have hAB : ((A : O → ℂ)*B) = primeSubsetRow p χ (S ∪ T) := by
    funext z
    change A z * B z = _
    simp only [hA, hB, primeSubsetRow, Finset.prod_union hd]
  have h := residueRowGauss_mul c d hc hd0 (prime_subsets_coprime p hinj S T hd) A B hAc hBd
  rw [hAB, ha, hb, hA, hB] at h
  rw [subsetTraceGauss_eq_residueRowGauss]
  simpa only [c, d, Finset.prod_union hd] using h

def normalizedSubsetTraceGauss {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (S : Finset ι) : ℂ :=
  subsetTraceGauss p hp χ S / (‖ringComplex (∏ i ∈ S, p i)‖ : ℂ)

theorem normalizedSubsetTraceGauss_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (S T : Finset ι) (hd : Disjoint S T) :
    normalizedSubsetTraceGauss p hp χ (S ∪ T) =
      primeSubsetRow p χ S (∏ i ∈ T, p i) * primeSubsetRow p χ T (∏ i ∈ S, p i) *
        normalizedSubsetTraceGauss p hp χ S * normalizedSubsetTraceGauss p hp χ T := by
  simp only [normalizedSubsetTraceGauss, subsetTraceGauss_union p hp hinj χ S T hd,
    Finset.prod_union hd, map_mul, norm_mul, Complex.ofReal_mul, div_eq_mul_inv, mul_inv_rev]
  ring

end SecondPassArithmetic

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem poweredRow_product (S T : Finset ι) (e : ι → ℕ) (he : ∀ i ∈ S, e i ≠ 0) :
    primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i) ^ e i) S
      (∏ k ∈ T, p k) = ∏ i ∈ S, ∏ k ∈ T, crossSymbol p hg i k ^ e i := by
  simp only [primeSubsetRow, map_prod]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro k _
  exact MulChar.pow_apply' _ (he i hi) _

theorem blockCross_eq_poweredRows (S T : Finset ι) (e : ι → ℕ)
    (heS : ∀ i ∈ S, e i ≠ 0) (heT : ∀ i ∈ T, e i ≠ 0) :
    blockCross p hg S T e =
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i) ^ e i) S
        (∏ k ∈ T, p k) *
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i) ^ e i) T
        (∏ k ∈ S, p k) := by
  rw [poweredRow_product p hg S T e heS, poweredRow_product p hg T S e heT]
  rw [Finset.prod_comm (s := T) (t := S)]
  simp only [blockCross, Finset.prod_mul_distrib]

theorem normalizedSubsetTraceGauss_singleton_power (i : ι) (e : ι → ℕ) :
    normalizedSubsetTraceGauss p hp (fun k => complexSexticChar (Ideal.span {p k}) (hg k) ^ e k) {i} =
      localTraceGauss (p i) (hp i) (hg i) (e i) := by
  rw [normalizedSubsetTraceGauss, subsetTraceGauss_eq_residueRowGauss]
  have hf : primeSubsetRow p
      (fun k => complexSexticChar (Ideal.span {p k}) (hg k) ^ e k) {i} =
      (fun z => (complexSexticChar (Ideal.span {p i}) (hg i) ^ e i)
        (Ideal.Quotient.mk (Ideal.span {p i}) z)) := by
    funext z
    simp only [primeSubsetRow, Finset.prod_singleton]
  simp only [Finset.prod_singleton, hf, localTraceGauss]

/-- Local Gauss blocks multiply to the normalized trace Gauss sum. -/
theorem normalizedSubsetTraceGauss_eq_gaussBlock
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (S : Finset ι) (e : ι → ℕ) (he : ∀ i ∈ S, e i ≠ 0) :
    normalizedSubsetTraceGauss p hp (fun i => complexSexticChar (Ideal.span {p i}) (hg i) ^ e i) S =
      gaussBlock p hp hg S e := by
  induction S using Finset.induction_on with
  | empty =>
    simp only [normalizedSubsetTraceGauss, subsetTraceGauss, primeRowTraceGauss_empty,
      gaussBlock, Finset.prod_empty, map_one, norm_one, Complex.ofReal_one, div_one]
  | @insert i S hi ih =>
    have hS : ∀ k ∈ S, e k ≠ 0 := fun k hk => he k (Finset.mem_insert_of_mem hk)
    have hi' : ∀ k ∈ ({i} : Finset ι), e k ≠ 0 := fun k hk =>
      he k (Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp hk)))
    have hd : Disjoint ({i} : Finset ι) S := Finset.disjoint_singleton_left.mpr hi
    have hs : insert i S = ({i} : Finset ι) ∪ S := by ext k; simp
    rw [hs, normalizedSubsetTraceGauss_union p hp hinj _ {i} S hd,
      gaussBlock_union p hp hg {i} S hd, ih hS,
      normalizedSubsetTraceGauss_singleton_power p hp hg i e,
      blockCross_eq_poweredRows p hg {i} S e hi' hS]
    simp only [gaussBlock, Finset.prod_singleton, Finset.erase_singleton,
      Finset.prod_empty, one_mul]
    ring

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hp hinj in
theorem quadraticCrossPhase_eq_ray
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (S T : Finset ι) (hd : Disjoint S T) :
    quadraticCrossPhase p hg S T =
      rayQuadraticPair (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S, p i))
        (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ T, p i)) := by
  have hrow (A B : Finset ι) :
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) A
        (∏ i ∈ B, p i) ^ 3 = ∏ i ∈ A, ∏ k ∈ B, crossSymbol p hg i k ^ 3 := by
    simp only [primeSubsetRow, map_prod, ← Finset.prod_pow, crossSymbol]
  have he : quadraticCrossPhase p hg S T =
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S
        (∏ i ∈ T, p i) ^ 3 *
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) T
        (∏ i ∈ S, p i) ^ 3 := by
    rw [hrow, hrow, Finset.prod_comm (s := T) (t := S)]
    simp only [quadraticCrossPhase, Finset.prod_mul_distrib]
  rw [he, sexticRow_cube p hg, sexticRow_cube p hg]
  change quadraticSubsetSymbol p S T * quadraticSubsetSymbol p T S = _
  have hcop := prime_subsets_coprime p hinj S T hd
  have hq : quadraticSubsetSymbol p T S ^ 2 = 1 := quadraticSubsetRow_sq p T _ hcop.symm
  rw [quadraticSubsetSymbol_reciprocity p hp hinj hodd S T, mul_assoc,
    ← pow_two, hq, mul_one, rayQuadraticPair_mk]

include hp hinj in
theorem mixedCubeCross_eq_ray
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (U B : Finset ι) (hd : Disjoint U B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) :
    mixedCubeCross p hg U B v ε₁ ε₂ side =
      (if side then star (primeSubsetRow p
          (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U (crtLabel p B v ε₁ ε₂ side))
        else primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U
          (crtLabel p B v ε₁ ε₂ side)) *
      rayQuadraticPair (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ U, p i))
        (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ cubeOddSupport B v ε₁ ε₂, p i)) := by
  rw [mixedCubeCross_eq_row_quadratic p hcop hg hpr U B hd,
    quadraticCrossPhase_eq_ray p hp hinj hg hodd U (cubeOddSupport B v ε₁ ε₂)
      (hd.mono_right (Finset.filter_subset _ _))]

theorem blockCubeExponent_ne_zero (U B : Finset ι) (v : ι → ℕ)
    (ε₁ ε₂ : ι → Bool) (side : Bool) :
    ∀ i ∈ U ∪ cubeActiveSupport B v ε₁ ε₂, blockCubeExponent U v ε₁ ε₂ side i ≠ 0 := by
  intro i hi
  by_cases hiU : i ∈ U
  · cases side <;> simp [blockCubeExponent, hiU]
  · have hiB := (Finset.mem_union.mp hi).resolve_left hiU
    simp only [blockCubeExponent, if_neg hiU]
    exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hiB).2

include hinj in
/-- The first conductor splits into squarefree and cube blocks, with an explicit residue phase. -/
theorem normalizedTraceGauss_cube_partition
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (U B : Finset ι) (hd : Disjoint U B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (side : Bool) :
    normalizedSubsetTraceGauss p hp
      (fun i => complexSexticChar (Ideal.span {p i}) (hg i) ^ blockCubeExponent U v ε₁ ε₂ side i)
      (U ∪ cubeActiveSupport B v ε₁ ε₂) =
    gaussBlock p hp hg U (fun _ => if side then 5 else 1) *
      gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
        (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
      ((if side then star (primeSubsetRow p
          (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U (crtLabel p B v ε₁ ε₂ side))
        else primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U
          (crtLabel p B v ε₁ ε₂ side)) *
      rayQuadraticPair (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ U, p i))
        (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ cubeOddSupport B v ε₁ ε₂, p i))) := by
  rw [normalizedSubsetTraceGauss_eq_gaussBlock p hp hg hinj _ _
    (blockCubeExponent_ne_zero U B v ε₁ ε₂ side), gaussBlock_cube_partition p hp hg U B hd,
    mixedCubeCross_eq_ray p hp hinj hg hcop hodd hpr U B hd]

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

include hinj in
theorem normalizedSubsetTraceGauss_norm_one
    (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ) (S : Finset ι)
    (hχ : ∀ i ∈ S, χ i ≠ 1) : ‖normalizedSubsetTraceGauss p hp χ S‖ = 1 := by
  have hs := (prime_row_trace_poisson (fun i : S => p i.val) (fun i => hp i.val)
    (hinj.comp Subtype.val_injective) (fun i => χ i.val) (fun i => hχ i.val i.property)).1
  have hn : ‖subsetTraceGauss p hp χ S‖ = ‖ringComplex (∏ i ∈ S, p i)‖ := by
    apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
    simpa only [subsetTraceGauss, Finset.prod_coe_sort] using hs
  have hne : ‖ringComplex (∏ i ∈ S, p i)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (ringComplex_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i)))
  rw [normalizedSubsetTraceGauss, norm_div, hn, Complex.norm_real,
    Real.norm_of_nonneg (norm_nonneg _), div_self hne]

include hinj in
theorem gaussBlock_norm_one
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (S : Finset ι) (e : ι → ℕ) (he : ∀ i ∈ S, e i ≠ 0) (he6 : ∀ i ∈ S, e i < 6) :
    ‖gaussBlock p hp hg S e‖ = 1 := by
  rw [← normalizedSubsetTraceGauss_eq_gaussBlock p hp hg hinj S e he]
  exact normalizedSubsetTraceGauss_norm_one p hp hinj _ S (fun i hi =>
    complexSexticChar_pow_ne_one (Ideal.span {p i}) (hg i) (hodd i) (e i) (he6 i hi) (he i hi))

include hinj in
theorem cubeGaussBlock_norm_one
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    ‖gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
      (fun i => (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val)‖ = 1 := by
  apply gaussBlock_norm_one p hp hinj hg hodd
  · intro i hi
    exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hi).2
  · intro i _
    exact ZMod.val_lt _

include hinj in
theorem secondColumnCoefficient_eq_gaussBlock (S : Finset ι) :
    secondColumnCoefficient p S =
      star (ringComplex (∏ i ∈ S, p i) / (‖ringComplex (∏ i ∈ S, p i)‖ : ℂ)) *
        gaussBlock p hp hg S (fun _ => 2) := by
  rw [← normalizedSubsetTraceGauss_eq_gaussBlock p hp hg hinj S (fun _ => 2)
    (fun _ _ => by decide)]
  have hχ : (fun i => complexSexticChar (Ideal.span {p i}) (hg i) ^ 2) =
      (fun i => complexCubicChar (Ideal.span {p i}) (hg i)) :=
    funext (fun i => (complexSexticChar_powers (Ideal.span {p i}) (hg i)).1)
  rw [normalizedSubsetTraceGauss, hχ]
  have h := primeRowTraceGauss_cubic (fun i : S => p i.val) (fun i => hp i.val)
    (hinj.comp Subtype.val_injective) (fun i => hg i.val)
  have hG : subsetTraceGauss p hp (fun i => complexCubicChar (Ideal.span {p i}) (hg i)) S =
      cubicUnitGaussSum 1 (∏ i ∈ S, p i) := by
    simpa only [subsetTraceGauss, Finset.prod_coe_sort] using h
  rw [hG]
  rfl

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical

theorem blockCross_union_left {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T C : Finset ι)
    (hd : Disjoint S T) (e : ι → ℕ) :
    blockCross p hg (S ∪ T) C e = blockCross p hg S C e * blockCross p hg T C e :=
  Finset.prod_union hd

def threeBlockExponent {ι : Type*} [DecidableEq ι] (N P : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (i : ι) : ℕ :=
  if i ∈ N then 5 else if i ∈ P then 1
  else (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val

theorem gaussBlock_three_cube_partition {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    gaussBlock p hp hg ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂)
      (threeBlockExponent N P v ε₁ ε₂) =
    gaussBlock p hp hg N (fun _ => 5) * gaussBlock p hp hg P (fun _ => 1) *
      gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
        (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
      quadraticCrossPhase p hg N P * mixedCubeCross p hg N B v ε₁ ε₂ true *
        mixedCubeCross p hg P B v ε₁ ε₂ false := by
  let C := cubeActiveSupport B v ε₁ ε₂
  let e := threeBlockExponent N P v ε₁ ε₂
  have hNC : Disjoint N C := hNB.mono_right (Finset.filter_subset _ _)
  have hPC : Disjoint P C := hPB.mono_right (Finset.filter_subset _ _)
  have hNPC : Disjoint (N ∪ P) C := Finset.disjoint_union_left.mpr ⟨hNC, hPC⟩
  have hN (i : ι) (hi : i ∈ N) : e i = 5 := by simp [e, threeBlockExponent, hi]
  have hP (i : ι) (hi : i ∈ P) : e i = 1 := by
    have hn : i ∉ N := fun h => Finset.disjoint_left.mp hNP h hi
    simp [e, threeBlockExponent, hn, hi]
  have hC (i : ι) (hi : i ∈ C) : e i =
      (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val := by
    have hn : i ∉ N := fun h => Finset.disjoint_left.mp hNC h hi
    have hp' : i ∉ P := fun h => Finset.disjoint_left.mp hPC h hi
    simp [e, threeBlockExponent, hn, hp']
  have hcrossNP : blockCross p hg N P e = quadraticCrossPhase p hg N P := by
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro k hk
    rw [hN i hi, hP k hk, pow_one]
    have hr := cross_square_primary p hg hpr i k
    calc
      _ = crossSymbol p hg i k ^ 3 * crossSymbol p hg i k ^ 2 * crossSymbol p hg k i := by ring
      _ = _ := by rw [hr]; ring
  have hcrossNC : blockCross p hg N C e = mixedCubeCross p hg N B v ε₁ ε₂ true := by
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro k hk
    rw [hN i hi, hC k hk]
    rfl
  have hcrossPC : blockCross p hg P C e = mixedCubeCross p hg P B v ε₁ ε₂ false := by
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro k hk
    rw [hP i hi, hC k hk]
    rfl
  change gaussBlock p hp hg ((N ∪ P) ∪ C) e = _
  rw [gaussBlock_union p hp hg (N ∪ P) C hNPC, gaussBlock_union p hp hg N P hNP,
    blockCross_union_left p hg N P C hNP,
    gaussBlock_congr p hp hg N e (fun _ => 5) hN,
    gaussBlock_congr p hp hg P e (fun _ => 1) hP,
    gaussBlock_congr p hp hg C e _ hC, hcrossNP, hcrossNC, hcrossPC]
  ring


def blockRow {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ) (u : O) : ℂ :=
  primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i) ^ e i) S u

theorem blockRow_eq_product {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e : ι → ℕ) (u : O) :
    blockRow p hg S e u = ∏ i ∈ S,
      (complexSexticChar (Ideal.span {p i}) (hg i) ^ e i) (Ideal.Quotient.mk (Ideal.span {p i}) u) := rfl

theorem blockRow_union {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S T : Finset ι) (hd : Disjoint S T)
    (e : ι → ℕ) (u : O) :
    blockRow p hg (S ∪ T) e u = blockRow p hg S e u * blockRow p hg T e u := by
  simp only [blockRow_eq_product, Finset.prod_union hd]

theorem blockRow_congr {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (e f : ι → ℕ)
    (hef : ∀ i ∈ S, e i = f i) (u : O) : blockRow p hg S e u = blockRow p hg S f u := by
  simp only [blockRow_eq_product]
  exact Finset.prod_congr rfl (fun i hi => by rw [hef i hi])

theorem blockRow_one {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (u : O) :
    blockRow p hg S (fun _ => 1) u = primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S u := by
  simp only [blockRow_eq_product, pow_one, primeSubsetRow]

theorem blockRow_five {ι : Type*} (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (S : Finset ι) (u : O) :
    blockRow p hg S (fun _ => 5) u = star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S u) := by
  rw [sexticRow_star p hg S u]
  simp only [blockRow_eq_product, primeSubsetRow, ← Finset.prod_pow]
  apply Finset.prod_congr rfl
  intro i _
  exact MulChar.pow_apply' _ (by decide : (5 : ℕ) ≠ 0) _


theorem threeBlockRow_factor {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (u : O) :
    blockRow p hg ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂)
      (threeBlockExponent N P v ε₁ ε₂) u =
    star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) N u) *
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) P u *
      blockRow p hg (cubeActiveSupport B v ε₁ ε₂)
        (fun i => (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val) u := by
  have hNC : Disjoint N (cubeActiveSupport B v ε₁ ε₂) := hNB.mono_right (Finset.filter_subset _ _)
  have hPC : Disjoint P (cubeActiveSupport B v ε₁ ε₂) := hPB.mono_right (Finset.filter_subset _ _)
  have hN : ∀ i ∈ N, threeBlockExponent N P v ε₁ ε₂ i = 5 := by
    intro i hi; simp [threeBlockExponent, hi]
  have hP : ∀ i ∈ P, threeBlockExponent N P v ε₁ ε₂ i = 1 := by
    intro i hi
    simp [threeBlockExponent, hi, show i ∉ N from fun hn => Finset.disjoint_left.mp hNP hn hi]
  have hC : ∀ i ∈ cubeActiveSupport B v ε₁ ε₂, threeBlockExponent N P v ε₁ ε₂ i =
      (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val := by
    intro i hi
    simp [threeBlockExponent,
      show i ∉ N from fun hn => Finset.disjoint_left.mp hNC hn hi,
      show i ∉ P from fun hp => Finset.disjoint_left.mp hPC hp hi]
  rw [blockRow_union p hg (N ∪ P) _ (Finset.disjoint_union_left.mpr ⟨hNC, hPC⟩),
    blockRow_union p hg N P hNP, blockRow_congr p hg N _ _ hN,
    blockRow_congr p hg P _ _ hP, blockRow_congr p hg _ _ _ hC,
    blockRow_five, blockRow_one]

def cubeBaseFactor {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (d h : O) : ℂ :=
  let C := cubeActiveSupport B v ε₁ ε₂
  let e := fun i => (conductorExponent (parity (v i)) (ε₁ i) (ε₂ i)).val
  gaussBlock p hp hg C e * blockRow p hg C e d * star (blockRow p hg C e h)


theorem blockRow_norm_le_one {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (S : Finset ι) (e : ι → ℕ) (a : O) : ‖blockRow p hg S e a‖ ≤ 1 :=
  primeSubsetRow_norm_le_one p _ S a

theorem cubeBaseFactor_norm_le_one {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (d h : O) :
    ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ ≤ 1 := by
  simp only [cubeBaseFactor, norm_mul, norm_star,
    cubeGaussBlock_norm_one p hp hinj hg hodd, one_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (blockRow_norm_le_one p hg _ _ _)).trans (blockRow_norm_le_one p hg _ _ _)


end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O) (hp : ∀ i, p i ≠ 0)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hinj : Function.Injective (fun i => Ideal.span {p i}))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})
  (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
  (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)

include hp hinj hg hodd in
theorem secondColumnCoefficient_mul_star (S : Finset ι) :
    secondColumnCoefficient p S * star (secondColumnCoefficient p S) = 1 := by
  have hn : ‖secondColumnCoefficient p S‖ = 1 := by
    rw [secondColumnCoefficient_eq_gaussBlock p hp hinj hg S, norm_mul, norm_star,
      gaussBlock_norm_one p hp hinj hg hodd S (fun _ => 2)
        (fun _ _ => by decide) (fun _ _ => by decide), mul_one, norm_div,
      Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr
      (ringComplex_ne_zero (Finset.prod_ne_zero_iff.mpr (fun i _ => hp i))))
  rw [← starRingEnd_apply, Complex.mul_conj', hn]
  norm_num

include hinj hodd hpr in
theorem gaussBlock_one_mobius (S : Finset ι) :
    supportMobius S * gaussBlock p hp hg S (fun _ => 1) =
      star (subsetTraceRayFactor p hg S * secondColumnCoefficient p S) := by
  rw [← normalizedSubsetTraceGauss_eq_gaussBlock p hp hg hinj S (fun _ => 1)
    (fun _ _ => by decide)]
  have h := congrArg (starRingEnd ℂ) (subsetTraceGauss_mobius_conversion p hp hinj hg hodd hpr S)
  rw [map_div₀, map_mul, Complex.conj_ofReal] at h
  simpa only [normalizedSubsetTraceGauss, starRingEnd_apply, star_supportMobius,
    star_star, pow_one, div_eq_mul_inv, mul_assoc] using h

include hinj in
theorem gaussBlock_five (S : Finset ι) :
    gaussBlock p hp hg S (fun _ => 5) =
      primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S (-1) *
        star (gaussBlock p hp hg S (fun _ => 1)) := by
  let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i)
  have hi : (fun i => χ i ^ 5) = (fun i => (χ i)⁻¹) := by
    funext i
    have h6 : χ i ^ 6 = 1 := (complexSexticChar_powers _ _).2.2
    calc
      _ = (χ i)⁻¹ * χ i ^ 6 := by group
      _ = _ := by rw [h6, mul_one]
  rw [← normalizedSubsetTraceGauss_eq_gaussBlock p hp hg hinj S (fun _ => 5)
      (fun _ _ => by decide),
    ← normalizedSubsetTraceGauss_eq_gaussBlock p hp hg hinj S (fun _ => 1)
      (fun _ _ => by decide)]
  change normalizedSubsetTraceGauss p hp (fun i => χ i ^ 5) S =
    primeSubsetRow p χ S (-1) * star (normalizedSubsetTraceGauss p hp (fun i => χ i ^ 1) S)
  rw [hi]
  simp only [pow_one, normalizedSubsetTraceGauss, subsetTraceGauss_inverse p hp hinj χ S]
  have hs : star (subsetTraceGauss p hp χ S / (‖ringComplex (∏ i ∈ S, p i)‖ : ℂ)) =
      star (subsetTraceGauss p hp χ S) / (‖ringComplex (∏ i ∈ S, p i)‖ : ℂ) := by
    change (starRingEnd ℂ) (_ / _) = _
    rw [map_div₀, Complex.conj_ofReal, starRingEnd_apply]
  rw [hs]
  ring

/-- The first reflection leaves the conjugate finite ray factor after cubic cancellation. -/
def firstColumnPhase (S : Finset ι) : ℂ := star (subsetTraceRayFactor p hg S)

include hinj hodd hpr in
theorem first_gauss_cancellation (S : Finset ι) :
    secondColumnCoefficient p S * gaussBlock p hp hg S (fun _ => 1) =
      supportMobius S * firstColumnPhase p hg S ∧
    star (secondColumnCoefficient p S) * gaussBlock p hp hg S (fun _ => 5) =
      supportMobius S *
        primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S (-1) *
        star (firstColumnPhase p hg S) := by
  have hc := secondColumnCoefficient_mul_star p hp hinj hg hodd S
  have h1 : secondColumnCoefficient p S * gaussBlock p hp hg S (fun _ => 1) =
      supportMobius S * firstColumnPhase p hg S := by
    calc
      _ = supportMobius S * secondColumnCoefficient p S *
          (supportMobius S * gaussBlock p hp hg S (fun _ => 1)) := by
        calc
          _ = (supportMobius S * supportMobius S) *
              (secondColumnCoefficient p S * gaussBlock p hp hg S (fun _ => 1)) := by
            rw [supportMobius_sq, one_mul]
          _ = _ := by ring
      _ = _ := by
        rw [gaussBlock_one_mobius p hp hinj hg hodd hpr S, star_mul]
        calc
          _ = supportMobius S * star (subsetTraceRayFactor p hg S) *
              (secondColumnCoefficient p S * star (secondColumnCoefficient p S)) := by ring
          _ = _ := by rw [hc, mul_one]; rfl
  refine ⟨h1, ?_⟩
  rw [gaussBlock_five p hp hinj hg S]
  calc
    _ = primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S (-1) *
        star (secondColumnCoefficient p S * gaussBlock p hp hg S (fun _ => 1)) := by
      rw [star_mul]
      ring
    _ = _ := by rw [h1, star_mul, star_supportMobius]; ring

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical

theorem normalizedTraceGauss_three_cube_partition {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) :
    normalizedSubsetTraceGauss p hp
      (fun i => complexSexticChar (Ideal.span {p i}) (hg i) ^ threeBlockExponent N P v ε₁ ε₂ i)
      ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂) =
    gaussBlock p hp hg N (fun _ => 5) * gaussBlock p hp hg P (fun _ => 1) *
      gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
        (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
      quadraticCrossPhase p hg N P *
      (star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) N (crtLabel p B v ε₁ ε₂ true)) *
        quadraticCrossPhase p hg N (cubeOddSupport B v ε₁ ε₂)) *
      (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) P (crtLabel p B v ε₁ ε₂ false) *
        quadraticCrossPhase p hg P (cubeOddSupport B v ε₁ ε₂)) := by
  have he : ∀ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂,
      threeBlockExponent N P v ε₁ ε₂ i ≠ 0 := by
    intro i hi
    by_cases hn : i ∈ N
    · simp [threeBlockExponent, hn]
    by_cases hp' : i ∈ P
    · simp [threeBlockExponent, hn, hp']
    · have hiC : i ∈ cubeActiveSupport B v ε₁ ε₂ := by simpa [hn, hp'] using hi
      simp only [threeBlockExponent, if_neg hn, if_neg hp']
      exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hiC).2
  rw [normalizedSubsetTraceGauss_eq_gaussBlock p hp hg hinj _ _ he,
    gaussBlock_three_cube_partition p hp hg hpr N P B hNP hNB hPB,
    mixedCubeCross_eq_row_quadratic p hcop hg hpr N B hNB,
    mixedCubeCross_eq_row_quadratic p hcop hg hpr P B hPB]
  rfl


def firstPassColumnMinus {ι : Type*} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (C : Finset ι → ℂ) (d : O) (S : Finset ι) : ℂ :=
  star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S (-1)) *
    firstColumnPhase p hg S *
    primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S d * C S

def firstPassColumnPlus {ι : Type*} [DecidableEq ι] (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (C : Finset ι → ℂ) (d : O) (S : Finset ι) : ℂ :=
  firstColumnPhase p hg S *
    primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S d * C S

theorem a_weighted_three_cube_gauss {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) :
    star (secondColumnCoefficient p N * C₁ N) *
      (secondColumnCoefficient p P * C₂ P) *
      normalizedSubsetTraceGauss p hp
        (fun i => complexSexticChar (Ideal.span {p i}) (hg i) ^ threeBlockExponent N P v ε₁ ε₂ i)
        ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂) =
    (gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
        (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
      quadraticCrossPhase p hg N P *
      quadraticCrossPhase p hg N (cubeOddSupport B v ε₁ ε₂) *
      quadraticCrossPhase p hg P (cubeOddSupport B v ε₁ ε₂)) *
      star (supportMobius N *
        firstPassColumnMinus p hg C₁ (crtLabel p B v ε₁ ε₂ true) N) *
      (supportMobius P *
        firstPassColumnPlus p hg C₂ (crtLabel p B v ε₁ ε₂ false) P) := by
  rw [normalizedTraceGauss_three_cube_partition p hp hinj hcop hg hpr N P B hNP hNB hPB]
  have hn := (first_gauss_cancellation p hp hinj hg hc hpr N).2
  have hp' := (first_gauss_cancellation p hp hinj hg hc hpr P).1
  simp only [firstPassColumnMinus, firstPassColumnPlus, star_mul, star_star, star_supportMobius]
  calc
    _ = (star (secondColumnCoefficient p N) * gaussBlock p hp hg N (fun _ => 5)) *
      (secondColumnCoefficient p P * gaussBlock p hp hg P (fun _ => 1)) *
      (star (C₁ N) * C₂ P *
        gaussBlock p hp hg (cubeActiveSupport B v ε₁ ε₂)
          (fun k => (conductorExponent (parity (v k)) (ε₁ k) (ε₂ k)).val) *
        quadraticCrossPhase p hg N P *
        quadraticCrossPhase p hg N (cubeOddSupport B v ε₁ ε₂) *
        quadraticCrossPhase p hg P (cubeOddSupport B v ε₁ ε₂) *
        star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) N
          (crtLabel p B v ε₁ ε₂ true)) *
        primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) P
          (crtLabel p B v ε₁ ε₂ false)) := by ring
    _ = _ := by rw [hn, hp']; ring

def threeGaussRowFactor {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (N P B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) : ℂ :=
  let S := (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂
  let e := threeBlockExponent N P v ε₁ ε₂
  star (secondColumnCoefficient p N * C₁ N) *
    (secondColumnCoefficient p P * C₂ P) *
    normalizedSubsetTraceGauss p hp
      (fun i => complexSexticChar (Ideal.span {p i}) (hg i) ^ e i) S *
    (blockRow p hg S e d * star (blockRow p hg S e h))

def cubeTransformedPair {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (N P B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) : ℂ :=
  cubeBaseFactor p hp hg B v ε₁ ε₂ d h * quadraticCrossPhase p hg N P *
    quadraticCrossPhase p hg N (cubeOddSupport B v ε₁ ε₂) *
    quadraticCrossPhase p hg P (cubeOddSupport B v ε₁ ε₂) *
    star (supportMobius N *
      firstPassColumnMinus p hg C₁ (d * crtLabel p B v ε₁ ε₂ true) N *
      star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) N h)) *
    (supportMobius P *
      firstPassColumnPlus p hg C₂ (d * crtLabel p B v ε₁ ε₂ false) P *
      star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) P h))

theorem threeGaussRowFactor_eq_transformedPair {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    threeGaussRowFactor p hp hg N P B v ε₁ ε₂ C₁ C₂ d h =
      cubeTransformedPair p hp hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  unfold threeGaussRowFactor
  dsimp only
  rw [a_weighted_three_cube_gauss p hp hinj hcop hg hc hpr N P B hNP hNB hPB,
    threeBlockRow_factor p hg N P B hNP hNB hPB,
    threeBlockRow_factor p hg N P B hNP hNB hPB]
  simp only [cubeTransformedPair, cubeBaseFactor,
    firstPassColumnMinus, firstPassColumnPlus,
    subsetRow_mul, star_mul, star_star]
  ring


end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical SchwartzMap

/-- Poisson summation for a masked sextic block, with its normalized Gauss factor retained. -/
theorem masked_block_radial_poisson_product {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (M S : Finset ι) (e : ι → ℕ) (he : ∀ i ∈ S, e i ≠ 0) (he6 : ∀ i ∈ S, e i < 6)
    (W : 𝓢(ℝ, ℂ)) (lengthScale : ℝ) (hL : 0 < lengthScale) :
    (∑' z : O, primeCoprimeMask p M z * blockRow p hg S e z *
      W (‖ringComplex z‖ ^ 2 / lengthScale)) =
    ((lengthScale : ℂ) * normalizedSubsetTraceGauss p hp
      (fun i => complexSexticChar (Ideal.span {p i}) (hg i) ^ e i) S /
        (‖ringComplex (∏ i ∈ S, p i)‖ : ℂ)) *
      ∑ E ∈ M.powerset,
        (supportMobius E * blockRow p hg S e (∏ i ∈ E, p i) /
          (‖ringComplex (∏ i ∈ E, p i)‖ ^ 2 : ℝ)) *
          ∑' h : O, star (blockRow p hg S e h) * paperRadialFourier W
            (lengthScale * ‖ringComplex h‖ ^ 2 /
              (‖ringComplex (∏ i ∈ E, p i)‖ ^ 2 * ‖ringComplex (∏ i ∈ S, p i)‖ ^ 2)) := by
  let χ := fun i => complexSexticChar (Ideal.span {p i}) (hg i) ^ e i
  have hcop : Pairwise (Function.onFun IsCoprime p) := by
    intro i j hij
    simpa only [Finset.prod_singleton] using prime_subsets_coprime p hinj {i} {j}
      (Finset.disjoint_singleton.mpr hij)
  have hχ (i : S) : χ i.val ≠ 1 :=
    complexSexticChar_pow_ne_one _ (hg i.val) (hodd i.val) _ (he6 i.val i.property) (he i.val i.property)
  have h := prime_row_trace_masked_poisson (fun i : S => p i.val) (fun i => hp i.val)
    (hinj.comp Subtype.val_injective) (fun i => χ i.val) hχ p hp hcop M W lengthScale hL
  simp only [primeCuspRowCharacter_restrict, Finset.prod_coe_sort] at h
  have hInv (z : O) :
      primeCuspRowCharacter (fun i : S => p i.val) (fun i => (χ i.val)⁻¹) z =
        star (blockRow p hg S e z) := by
    change (∏ i : S, (χ i.val)⁻¹ (Ideal.Quotient.mk (Ideal.span {p i.val}) z)) = _
    calc
      _ = ∏ i ∈ S, (χ i)⁻¹ (Ideal.Quotient.mk (Ideal.span {p i}) z) :=
        Finset.prod_coe_sort (s := S)
          (f := fun i : ι => (χ i)⁻¹ (Ideal.Quotient.mk (Ideal.span {p i}) z))
      _ = _ := by
        simp only [blockRow, primeSubsetRow, star_prod, MulChar.star_apply', χ]
  simp_rw [hInv] at h
  have hn : ((lengthScale : ℂ) * subsetTraceGauss p hp χ S /
      (‖ringComplex (∏ i ∈ S, p i)‖ ^ 2 : ℝ)) =
      (lengthScale : ℂ) * normalizedSubsetTraceGauss p hp χ S /
        (‖ringComplex (∏ i ∈ S, p i)‖ : ℂ) := by
    rw [normalizedSubsetTraceGauss, Complex.ofReal_pow]
    ring
  rw [show primeRowTraceGauss (fun i : S => p i.val) (fun i => hp i.val)
      (fun i => χ i.val) = subsetTraceGauss p hp χ S from rfl, hn] at h
  simpa only [blockRow, supportMobius, χ, primeSubsetRow, star_prod, MulChar.star_apply'] using h

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical SchwartzMap

theorem a_weighted_three_block_radial_poisson {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (M N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (lengthScale : ℝ) (hL : 0 < lengthScale) :
    let S := (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂
    let e := threeBlockExponent N P v ε₁ ε₂
    star (secondColumnCoefficient p N * C₁ N) *
      (secondColumnCoefficient p P * C₂ P) *
      (∑' z : O, primeCoprimeMask p M z * blockRow p hg S e z *
        W (‖ringComplex z‖ ^ 2 / lengthScale)) =
    ((lengthScale : ℂ) / (‖ringComplex (∏ i ∈ S, p i)‖ : ℂ)) *
      ∑ E ∈ M.powerset,
        let d := (∏ i ∈ E, p i)
        (supportMobius E /
          (‖ringComplex d‖ ^ 2 : ℝ)) *
          ∑' h : O, paperRadialFourier W
            (lengthScale * ‖ringComplex h‖ ^ 2 / (‖ringComplex d‖ ^ 2 * ‖ringComplex (∏ i ∈ S, p i)‖ ^ 2)) *
              cubeTransformedPair p hp hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  dsimp only
  have he : ∀ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂,
      threeBlockExponent N P v ε₁ ε₂ i ≠ 0 := by
    intro i hi
    by_cases hn : i ∈ N
    · simp [threeBlockExponent, hn]
    by_cases hp' : i ∈ P
    · simp [threeBlockExponent, hn, hp']
    · have hiC : i ∈ cubeActiveSupport B v ε₁ ε₂ := by simpa [hn, hp'] using hi
      simp only [threeBlockExponent, if_neg hn, if_neg hp']
      exact (ZMod.val_eq_zero _).not.mpr (Finset.mem_filter.mp hiC).2
  have he6 : ∀ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂,
      threeBlockExponent N P v ε₁ ε₂ i < 6 := by
    intro i hi
    unfold threeBlockExponent
    split_ifs <;> first | omega | exact ZMod.val_lt _
  rw [masked_block_radial_poisson_product p hp hinj hg hc M _ _ he he6 W lengthScale hL]
  simp_rw [← threeGaussRowFactor_eq_transformedPair p hp hinj hcop hg hc hpr N P B hNP hNB hPB]
  simp only [Finset.mul_sum, ← tsum_mul_left]
  apply Finset.sum_congr rfl
  intro E hE
  apply tsum_congr
  intro h
  unfold threeGaussRowFactor
  dsimp only
  ring

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ)

def supportPairTerm (C₁ C₂ : Finset ι → ℂ) (h : O) (S T : Finset ι) : ℂ :=
  star (supportMobius S * C₁ S * star (primeSubsetRow p χ S h)) *
    (supportMobius T * C₂ T * star (primeSubsetRow p χ T h))

/-- Common primes contribute their coprimality mask, while their two Möbius signs cancel. -/
theorem supportPairTerm_union (C₁ C₂ : Finset ι → ℂ) (h : O) (D S T : Finset ι)
    (hDS : Disjoint D S) (hDT : Disjoint D T) :
    supportPairTerm p χ C₁ C₂ h (D ∪ S) (D ∪ T) =
      primeCoprimeMask p D h *
        supportPairTerm p χ (fun U => C₁ (D ∪ U)) (fun U => C₂ (D ∪ U)) h S T := by
  simp only [supportPairTerm, supportMobius_union D S hDS, supportMobius_union D T hDT,
    primeSubsetRow_union p χ D S hDS, primeSubsetRow_union p χ D T hDT,
    star_mul, star_star, star_supportMobius]
  calc
    _ = (supportMobius D * supportMobius D) *
      (star (primeSubsetRow p χ D h) * primeSubsetRow p χ D h) *
      (supportMobius S * star (C₁ (D ∪ S)) * primeSubsetRow p χ S h *
        (supportMobius T * C₂ (D ∪ T) * star (primeSubsetRow p χ T h))) := by ring
    _ = _ := by rw [supportMobius_sq, primeSubsetRow_diagonal, one_mul]; ring

theorem supportPairTerm_sum (F : Finset ι) (C₁ C₂ : Finset ι → ℂ) (h : O) :
    (∑ S ∈ F.powerset, ∑ T ∈ F.powerset, supportPairTerm p χ C₁ C₂ h S T) =
      star (supportConjugateSum p χ F C₁ h) * supportConjugateSum p χ F C₂ h := by
  simp only [supportPairTerm, supportConjugateSum, star_sum, Finset.sum_mul, Finset.mul_sum]
  exact Finset.sum_comm

def firstResidueMask (r : QuadraticRayRing) (C : Finset ι → ℂ) (S : Finset ι) : ℂ :=
  if Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S, p i) = r then C S else 0

theorem supportPairTerm_residue (Ω : QuadraticRayRing → QuadraticRayRing → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (h : O) (S T : Finset ι) :
    Ω (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S, p i))
        (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ T, p i)) *
      supportPairTerm p χ C₁ C₂ h S T =
      ∑ r : QuadraticRayRing × QuadraticRayRing, Ω r.1 r.2 *
        supportPairTerm p χ (firstResidueMask p r.1 C₁) (firstResidueMask p r.2 C₂) h S T := by
  have hstar (P : Prop) [Decidable P] (a : ℂ) :
      star (if P then a else 0) = if P then star a else 0 := by
    split_ifs <;> simp only [star_zero]
  simp only [Fintype.sum_prod_type, supportPairTerm, firstResidueMask,
    mul_ite, ite_mul, mul_zero, zero_mul, hstar]
  simp

/-- Two residue classes separate a finite pair sum into conjugate row products. -/
theorem sum_supportPairTerm_residue (F : Finset ι)
    (Ω : QuadraticRayRing → QuadraticRayRing → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (h : O) :
    (∑ S ∈ F.powerset, ∑ T ∈ F.powerset,
      Ω (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S, p i))
          (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ T, p i)) *
        supportPairTerm p χ C₁ C₂ h S T) =
      ∑ r : QuadraticRayRing × QuadraticRayRing, Ω r.1 r.2 *
        star (supportConjugateSum p χ F (firstResidueMask p r.1 C₁) h) *
        supportConjugateSum p χ F (firstResidueMask p r.2 C₂) h := by
  simp_rw [supportPairTerm_residue p χ Ω C₁ C₂ h]
  calc
    _ = ∑ S ∈ F.powerset, ∑ r : QuadraticRayRing × QuadraticRayRing,
        ∑ T ∈ F.powerset, Ω r.1 r.2 *
          supportPairTerm p χ (firstResidueMask p r.1 C₁) (firstResidueMask p r.2 C₂) h S T := by
      apply Finset.sum_congr rfl
      intro S _
      exact Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      simp_rw [← Finset.mul_sum]
      rw [supportPairTerm_sum]
      ring

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ)

def firstResidueWeight (Ω : QuadraticRayRing → QuadraticRayRing → ℂ)
    (D : Finset ι) (h : O) (r : QuadraticRayRing × QuadraticRayRing) : ℂ :=
  supportMobius D * primeCoprimeMask p D h *
    Ω (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ D, p i) * r.1)
      (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ D, p i) * r.2)

def firstResidueReindex (F : Finset ι) (Ω : QuadraticRayRing → QuadraticRayRing → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (h : O) : ℂ :=
  ∑ D ∈ F.powerset, ∑ r : QuadraticRayRing × QuadraticRayRing,
    firstResidueWeight p Ω D h r *
      star (supportConjugateSum p χ (F \ D)
        (firstResidueMask p r.1 (fun U => C₁ (D ∪ U))) h) *
      supportConjugateSum p χ (F \ D)
        (firstResidueMask p r.2 (fun U => C₂ (D ∪ U))) h

/-- Möbius inversion removes the disjointness condition before separating the two residues. -/
theorem disjoint_supportPairTerm_reindex (F : Finset ι)
    (Ω : QuadraticRayRing → QuadraticRayRing → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (h : O) :
    (∑ S ∈ F.powerset, ∑ T ∈ F.powerset, if Disjoint S T then
      Ω (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S, p i))
          (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ T, p i)) *
        supportPairTerm p χ C₁ C₂ h S T else 0) =
      firstResidueReindex p χ F Ω C₁ C₂ h := by
  rw [CoprimeMobiusExtension.double_sum_disjoint_reindexed]
  unfold firstResidueReindex
  apply Finset.sum_congr rfl
  intro D hD
  let ΩD := fun r s : QuadraticRayRing =>
    Ω (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ D, p i) * r)
      (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ D, p i) * s)
  have hinner :
      (∑ S ∈ (F \ D).powerset, ∑ T ∈ (F \ D).powerset,
        Ω (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ D ∪ S, p i))
          (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ D ∪ T, p i)) *
          supportPairTerm p χ C₁ C₂ h (D ∪ S) (D ∪ T)) =
      primeCoprimeMask p D h *
        (∑ S ∈ (F \ D).powerset, ∑ T ∈ (F \ D).powerset,
          ΩD (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S, p i))
            (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ T, p i)) *
          supportPairTerm p χ (fun U => C₁ (D ∪ U)) (fun U => C₂ (D ∪ U)) h S T) := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro S hS
    apply Finset.sum_congr rfl
    intro T hT
    have hDS : Disjoint D S := Finset.disjoint_of_subset_right
      (Finset.mem_powerset.mp hS) disjoint_sdiff_self_right
    have hDT : Disjoint D T := Finset.disjoint_of_subset_right
      (Finset.mem_powerset.mp hT) disjoint_sdiff_self_right
    rw [Finset.prod_union hDS, Finset.prod_union hDT, map_mul, map_mul,
      supportPairTerm_union p χ C₁ C₂ h D S T hDS hDT]
    dsimp only [ΩD]
    ring
  rw [hinner, sum_supportPairTerm_residue p χ (F \ D) ΩD]
  simp only [Finset.mul_sum, firstResidueWeight, supportMobius, ΩD]
  apply Finset.sum_congr rfl
  intro r _
  ring

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical

def fixedRayExpansion {ι : Type*} (p : ι → O) (F S : Finset ι) : ℂ :=
  rayQuadraticPair (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ S, p i))
    (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ F, p i))

theorem fixedRayExpansion_eq_cross {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (F S : Finset ι) (hd : Disjoint S F) :
    fixedRayExpansion p F S = quadraticCrossPhase p hg S F :=
  (quadraticCrossPhase_eq_ray p hp hinj hg hodd S F hd).symm

def cubeMinusCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C : Finset ι → ℂ) (d : O) (S : Finset ι) : ℂ :=
  star (fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S) *
    firstPassColumnMinus p hg C (d * crtLabel p B v ε₁ ε₂ true) S

def cubePlusCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C : Finset ι → ℂ) (d : O) (S : Finset ι) : ℂ :=
  fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S *
    firstPassColumnPlus p hg C (d * crtLabel p B v ε₁ ε₂ false) S

theorem threeGaussRowFactor_eq_ray_columns {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (N P B : Finset ι) (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    threeGaussRowFactor p hp hg N P B v ε₁ ε₂ C₁ C₂ d h =
      cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
        rayQuadraticPair (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ N, p i))
          (Ideal.Quotient.mk (Ideal.span {(4 : O)}) (∏ i ∈ P, p i)) *
        supportPairTerm p (fun i => complexSexticChar (Ideal.span {p i}) (hg i))
          (cubeMinusCoefficient p hg B v ε₁ ε₂ C₁ d)
          (cubePlusCoefficient p hg B v ε₁ ε₂ C₂ d) h N P := by
  rw [threeGaussRowFactor_eq_transformedPair p hp hinj hcop hg hodd hpr N P B hNP hNB hPB]
  unfold cubeTransformedPair supportPairTerm cubeMinusCoefficient cubePlusCoefficient
  rw [fixedRayExpansion_eq_cross p hp hinj hg hodd (cubeOddSupport B v ε₁ ε₂) N
      (hNB.mono_right (Finset.filter_subset _ _)),
    fixedRayExpansion_eq_cross p hp hinj hg hodd (cubeOddSupport B v ε₁ ε₂) P
      (hPB.mono_right (Finset.filter_subset _ _)),
    quadraticCrossPhase_eq_ray p hp hinj hg hodd N P hNP]
  simp only [star_mul, star_star]
  ring

/-- The full three-block sum becomes a finite sum of conjugate rows in fixed residue classes. -/
theorem sum_threeGaussRowFactor_eq_rows {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hodd : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1)
    (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
      threeGaussRowFactor p hp hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
      cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
        firstResidueReindex p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F
          rayQuadraticPair (cubeMinusCoefficient p hg B v ε₁ ε₂ C₁ d)
          (cubePlusCoefficient p hg B v ε₁ ε₂ C₂ d) h := by
  rw [← disjoint_supportPairTerm_reindex]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hd : Disjoint N P
  · rw [if_pos hd, if_pos hd, threeGaussRowFactor_eq_ray_columns p hp hinj hcop hg hodd hpr
      N P B hd (hFB.mono_left (Finset.mem_powerset.mp hN))
      (hFB.mono_left (Finset.mem_powerset.mp hP))]
    ring
  · simp only [if_neg hd, mul_zero]

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap

def logTwistMinus {ι : Type*} (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι) : ℂ :=
  C S * star (V (y S) * kernelLogPhase t (-(y S)))

def logTwistPlus {ι : Type*} (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι) : ℂ :=
  C S * (V (y S) * kernelLogPhase t (-(y S)))

theorem threeGaussRowFactor_log_twist {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (N P B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O)
    (V₁ V₂ : ℝ → ℂ) (y₁ y₂ : Finset ι → ℝ) (t : ℝ) :
    threeGaussRowFactor p hp hg N P B v ε₁ ε₂
      (logTwistMinus C₁ V₁ y₁ t) (logTwistPlus C₂ V₂ y₂ t) d h =
    (V₁ (y₁ N) * kernelLogPhase t (-(y₁ N))) * (V₂ (y₂ P) * kernelLogPhase t (-(y₂ P))) *
      threeGaussRowFactor p hp hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  simp only [threeGaussRowFactor, logTwistMinus, logTwistPlus, star_mul, star_star]
  ring

theorem threeGaussRowFactor_normalized {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (N P B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O) :
    threeGaussRowFactor p hp hg N P B v ε₁ ε₂
      (normalizedColumn p C₁) (normalizedColumn p C₂) d h =
    ((‖ringComplex (∏ i ∈ N, p i)‖ : ℂ)⁻¹ * (‖ringComplex (∏ i ∈ P, p i)‖ : ℂ)⁻¹) *
      threeGaussRowFactor p hp hg N P B v ε₁ ε₂ C₁ C₂ d h := by
  have hs (x : ℝ) : star (x : ℂ) = (x : ℂ) := by simp
  have hsi (x : ℝ) : star ((x : ℂ)⁻¹) = (x : ℂ)⁻¹ := by simp
  simp only [threeGaussRowFactor, normalizedColumn, div_eq_mul_inv, star_mul, hsi]
  ring

theorem actual_pair_prefactor {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (N P B : Finset ι)
    (hNP : Disjoint N P) (hNB : Disjoint N B) (hPB : Disjoint P B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (lengthScale : ℝ) (d h : O) :
    ((lengthScale : ℂ) / (‖ringComplex (∏ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
      threeGaussRowFactor p hp hg N P B v ε₁ ε₂ C₁ C₂ d h =
    ((lengthScale : ℂ) / (‖ringComplex (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
      threeGaussRowFactor p hp hg N P B v ε₁ ε₂
        (normalizedColumn p C₁) (normalizedColumn p C₂) d h := by
  rw [threeGaussRowFactor_normalized]
  have hNC : Disjoint N (cubeActiveSupport B v ε₁ ε₂) := hNB.mono_right (Finset.filter_subset _ _)
  have hPC : Disjoint P (cubeActiveSupport B v ε₁ ε₂) := hPB.mono_right (Finset.filter_subset _ _)
  rw [Finset.prod_union (Finset.disjoint_union_left.mpr ⟨hNC, hPC⟩), Finset.prod_union hNP]
  simp only [map_mul, norm_mul, Complex.ofReal_mul, div_eq_mul_inv, mul_inv_rev]
  ring

theorem cube_integral_of_radial_separation {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hinj : Function.Injective (fun i => Ideal.span {p i}))
    (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
    (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ) (d h : O)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (y₁ y₂ : Finset ι → ℝ) (R : ℝ)
    (b : 𝓢(ℝ, ℂ))
    (hsep : ∀ x y : ℝ, V₁ x * V₂ y * paperRadialFourier W (R * Real.exp (-x-y)) =
      ∫ t : ℝ, (V₁ x * kernelLogPhase t (-x)) *
        (V₂ y * kernelLogPhase t (-y)) * b t) :
    Integrable (fun t : ℝ => b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      firstResidueReindex p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F rayQuadraticPair
        (cubeMinusCoefficient p hg B v ε₁ ε₂ (logTwistMinus C₁ V₁ y₁ t) d)
        (cubePlusCoefficient p hg B v ε₁ ε₂ (logTwistPlus C₂ V₂ y₂ t) d) h) volume ∧
    (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
      (V₁ (y₁ N) * V₂ (y₂ P) * paperRadialFourier W (R * Real.exp (-(y₁ N)-y₂ P))) *
        threeGaussRowFactor p hp hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
    ∫ t : ℝ, b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
      firstResidueReindex p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F rayQuadraticPair
        (cubeMinusCoefficient p hg B v ε₁ ε₂ (logTwistMinus C₁ V₁ y₁ t) d)
        (cubePlusCoefficient p hg B v ε₁ ε₂ (logTwistPlus C₂ V₂ y₂ t) d) h := by
  let G : ℝ → Finset ι → Finset ι → ℂ := fun t N P => if Disjoint N P then
    b t * threeGaussRowFactor p hp hg N P B v ε₁ ε₂
      (logTwistMinus C₁ V₁ y₁ t) (logTwistPlus C₂ V₂ y₂ t) d h else 0
  have hGint (N P : Finset ι) : Integrable (fun t => G t N P) volume := by
    by_cases hd : Disjoint N P
    · simp only [G, if_pos hd]
      convert integrable_log_pair b (-(y₁ N)) (-(y₂ P))
        (V₁ (y₁ N) * V₂ (y₂ P) * threeGaussRowFactor p hp hg N P B v ε₁ ε₂ C₁ C₂ d h) using 1
      funext t
      rw [threeGaussRowFactor_log_twist]
      ring
    · simp only [G, if_neg hd]
      exact integrable_zero _ _ _
  have hGsum (t : ℝ) :
      (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, G t N P) =
        b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
        firstResidueReindex p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F rayQuadraticPair
          (cubeMinusCoefficient p hg B v ε₁ ε₂ (logTwistMinus C₁ V₁ y₁ t) d)
          (cubePlusCoefficient p hg B v ε₁ ε₂ (logTwistPlus C₂ V₂ y₂ t) d) h := by
    calc
      _ = b t * (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
        threeGaussRowFactor p hp hg N P B v ε₁ ε₂
          (logTwistMinus C₁ V₁ y₁ t) (logTwistPlus C₂ V₂ y₂ t) d h else 0) := by
            simp only [G, Finset.mul_sum, mul_ite, mul_zero]
      _ = _ := by
        rw [sum_threeGaussRowFactor_eq_rows p hp hinj hcop hg hc hpr F B hFB]
        ring
  have hint : Integrable (fun t => ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, G t N P) volume :=
    integrable_finsetSum _ (fun N _ => integrable_finsetSum _ (fun P _ => hGint N P))
  constructor
  · simpa only [hGsum] using hint
  · have hterm (N P : Finset ι) :
        (if Disjoint N P then
          (V₁ (y₁ N) * V₂ (y₂ P) * paperRadialFourier W (R * Real.exp (-(y₁ N)-y₂ P))) *
            threeGaussRowFactor p hp hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
        ∫ t : ℝ, G t N P := by
      by_cases hd : Disjoint N P
      · simp only [G, if_pos hd]
        rw [hsep (y₁ N) (y₂ P), ← integral_mul_const]
        apply integral_congr_ae
        filter_upwards [] with t
        rw [threeGaussRowFactor_log_twist]
        ring
      · simp [G, hd]
    calc
      _ = ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, ∫ t : ℝ, G t N P := by
        apply Finset.sum_congr rfl
        intro N hN
        exact Finset.sum_congr rfl (fun P hP => hterm N P)
      _ = ∫ t : ℝ, ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, G t N P := by
        rw [integral_finsetSum _ (fun N _ => integrable_finsetSum _ (fun P _ => hGint N P))]
        apply Finset.sum_congr rfl
        intro N hN
        exact (integral_finsetSum _ (fun P _ => hGint N P)).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [] with t
        exact hGsum t


end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap

def actualFirstKernel {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (C₁ C₂ : Finset ι → ℂ)
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ) (X₁ X₂ lengthScale : ℝ) (d h : O) : ℂ :=
  ∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
    (V₁ (columnLog p X₁ N) * V₂ (columnLog p X₂ P)) *
    ((lengthScale : ℂ) / (‖ringComplex (∏ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
    paperRadialFourier W (lengthScale * ‖ringComplex h‖ ^ 2 /
      (‖ringComplex d‖ ^ 2 * primeProductNorm p ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂))) *
    threeGaussRowFactor p hp hg N P B v ε₁ ε₂ C₁ C₂ d h else 0

theorem actual_first_kernel_uniform_integral
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀
      {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
      (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
      (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂), ∀ lengthScale : ℝ, 0 < lengthScale → ∀ d h : O, d ≠ 0 → h ≠ 0 →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ t : ℝ, (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h) ^ A *
          ‖b t‖ ≤ K * firstLogDensity J t) ∧
        ∀ C₁ C₂ : Finset ι → ℂ,
        Integrable (fun t : ℝ => b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
          firstResidueReindex p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F rayQuadraticPair
            (cubeMinusCoefficient p hg B v ε₁ ε₂
              (logTwistMinus (normalizedColumn p C₁) V₁ (columnLog p X₁) t) d)
            (cubePlusCoefficient p hg B v ε₁ ε₂
              (logTwistPlus (normalizedColumn p C₂) V₂ (columnLog p X₂) t) d) h) volume ∧
        (∑ N ∈ F.powerset, ∑ P ∈ F.powerset, if Disjoint N P then
          (V₁ (columnLog p X₁ N) * V₂ (columnLog p X₂ P)) *
          ((lengthScale : ℂ) / (‖ringComplex (∏ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
          paperRadialFourier W (lengthScale * ‖ringComplex h‖ ^ 2 /
            (‖ringComplex d‖ ^ 2 * primeProductNorm p ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂))) *
          threeGaussRowFactor p hp hg N P B v ε₁ ε₂ C₁ C₂ d h else 0) =
        ((lengthScale : ℂ) / (‖ringComplex (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
        ∫ t : ℝ, b t * cubeBaseFactor p hp hg B v ε₁ ε₂ d h *
          firstResidueReindex p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F rayQuadraticPair
            (cubeMinusCoefficient p hg B v ε₁ ε₂
              (logTwistMinus (normalizedColumn p C₁) V₁ (columnLog p X₁) t) d)
            (cubePlusCoefficient p hg B v ε₁ ε₂
              (logTwistPlus (normalizedColumn p C₂) V₂ (columnLog p X₂) t) d) h := by
  obtain ⟨K, hK, hs⟩ := two_variable_radial_envelope W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F B hFB v ε₁ ε₂ X₁ X₂ hX₁ hX₂
  intro lengthScale hL d h hd hh
  let R := firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h
  have hR : 0 < R := by
    unfold R firstDualScale
    exact div_pos (mul_pos hL (pow_pos (norm_pos_iff.mpr (ringComplex_ne_zero hh)) 2))
      (mul_pos (mul_pos (mul_pos (pow_pos (norm_pos_iff.mpr (ringComplex_ne_zero hd)) 2)
        (primeProductNorm_pos p hp _)) hX₁) hX₂)
  obtain ⟨b, hb, hbound⟩ := hs R hR
  refine ⟨b, hbound, ?_⟩
  intro C₁ C₂
  have hpair := cube_integral_of_radial_separation p hp hinj hcop hg hc hpr F B hFB v ε₁ ε₂
    (normalizedColumn p C₁) (normalizedColumn p C₂) d h W V₁ V₂ (columnLog p X₁) (columnLog p X₂) R b hb
  refine ⟨hpair.1, ?_⟩
  rw [← hpair.2, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro N hN
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro P hP
  by_cases hNP : Disjoint N P
  · rw [if_pos hNP, if_pos hNP]
    have hNB : Disjoint N B := hFB.mono_left (Finset.mem_powerset.mp hN)
    have hPB : Disjoint P B := hFB.mono_left (Finset.mem_powerset.mp hP)
    have harg := actual_radial_argument p hp N P (cubeActiveSupport B v ε₁ ε₂) hNP
      (hNB.mono_right (Finset.filter_subset _ _)) (hPB.mono_right (Finset.filter_subset _ _))
      lengthScale X₁ X₂ hX₁ hX₂ d h
    change R * Real.exp (-(columnLog p X₁ N) - columnLog p X₂ P) = _ at harg
    rw [harg]
    have hpre := actual_pair_prefactor p hp hg N P B hNP hNB hPB v ε₁ ε₂ C₁ C₂ lengthScale d h
    calc
      _ = (V₁ (columnLog p X₁ N) * V₂ (columnLog p X₂ P) *
          paperRadialFourier W (lengthScale * ‖ringComplex h‖ ^ 2 /
            (‖ringComplex d‖ ^ 2 * primeProductNorm p ((N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂)))) *
          (((lengthScale : ℂ) / (‖ringComplex (∏ i ∈ (N ∪ P) ∪ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)) *
            threeGaussRowFactor p hp hg N P B v ε₁ ε₂ C₁ C₂ d h) := by ring
      _ = _ := by rw [hpre]; ring
  · simp [hNP]


end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ)

def firstResidueColumn (F D : Finset ι) (r : QuadraticRayRing)
    (C : Finset ι → ℂ) (h : O) : ℂ :=
  supportConjugateSum p χ (F \ D) (firstResidueMask p r (fun U => C (D ∪ U))) h

/-- The two residue coordinates retain the quadratic reciprocity weight. -/
def firstResidueEnergy (F : Finset ι) (Ω : QuadraticRayRing → QuadraticRayRing → ℂ)
    (C : Finset ι → ℂ) (negative : Bool) (h : O) : ℝ :=
  ∑ D ∈ F.powerset, ∑ r : QuadraticRayRing × QuadraticRayRing,
    ‖firstResidueWeight p Ω D h r‖ *
      ‖firstResidueColumn p χ F D (if negative then r.1 else r.2) C h‖ ^ 2

theorem firstResidueReindex_norm_le (F : Finset ι)
    (Ω : QuadraticRayRing → QuadraticRayRing → ℂ)
    (C₁ C₂ : Finset ι → ℂ) (h : O) :
    ‖firstResidueReindex p χ F Ω C₁ C₂ h‖ ≤
      Real.sqrt (firstResidueEnergy p χ F Ω C₁ true h) *
        Real.sqrt (firstResidueEnergy p χ F Ω C₂ false h) := by
  have hh := DescentWeightedCauchy.weighted_cauchy
    (F.powerset ×ˢ (Finset.univ : Finset (QuadraticRayRing × QuadraticRayRing)))
    (fun z => firstResidueWeight p Ω z.1 h z.2)
    (fun z => firstResidueColumn p χ F z.1 z.2.2 C₂ h)
    (fun z => firstResidueColumn p χ F z.1 z.2.1 C₁ h)
  simp only [Finset.sum_product, firstResidueEnergy, firstResidueColumn,
    firstResidueReindex, ite_true, Bool.false_eq_true, ite_false] at hh ⊢
  convert hh using 1
  · congr 2
    funext D
    congr 1
    funext r
    ring
  · ring

theorem firstResidueColumn_continuous (F D : Finset ι) (r : QuadraticRayRing)
    (C : ℝ → Finset ι → ℂ) (hc : ∀ S, Continuous (fun t => C t S)) (h : O) :
    Continuous (fun t => firstResidueColumn p χ F D r (C t) h) := by
  unfold firstResidueColumn supportConjugateSum
  apply continuous_finsetSum
  intro S _
  unfold firstResidueMask
  split_ifs
  · exact (continuous_const.mul (hc (D ∪ S))).mul continuous_const
  · exact continuous_const

theorem firstResidueColumn_uniform_bound (F D : Finset ι) (r : QuadraticRayRing)
    (C : ℝ → Finset ι → ℂ) (hn : ∀ t S, ‖C t S‖ = ‖C 0 S‖) (h : O) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, ‖firstResidueColumn p χ F D r (C t) h‖ ≤ M := by
  refine ⟨∑ S ∈ (F \ D).powerset,
    ‖supportMobius S * firstResidueMask p r (fun U => C 0 (D ∪ U)) S *
      star (primeSubsetRow p χ S h)‖, by positivity, ?_⟩
  intro t
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro S _
  unfold firstResidueMask
  split_ifs <;> simp only [norm_mul, hn] <;> exact le_rfl

theorem firstResidueEnergy_nonneg (F : Finset ι)
    (Ω : QuadraticRayRing → QuadraticRayRing → ℂ)
    (C : Finset ι → ℂ) (negative : Bool) (h : O) :
    0 ≤ firstResidueEnergy p χ F Ω C negative h := by
  unfold firstResidueEnergy
  positivity

theorem firstResidueEnergy_continuous (F : Finset ι)
    (Ω : QuadraticRayRing → QuadraticRayRing → ℂ)
    (C : ℝ → Finset ι → ℂ) (hc : ∀ S, Continuous (fun t => C t S))
    (negative : Bool) (h : O) :
    Continuous (fun t => firstResidueEnergy p χ F Ω (C t) negative h) := by
  unfold firstResidueEnergy
  apply continuous_finsetSum
  intro D _
  apply continuous_finsetSum
  intro r _
  exact continuous_const.mul
    ((firstResidueColumn_continuous p χ F D _ C hc h).norm.pow 2)

theorem firstResidueEnergy_uniform_bound (F : Finset ι)
    (Ω : QuadraticRayRing → QuadraticRayRing → ℂ)
    (C : ℝ → Finset ι → ℂ) (hn : ∀ t S, ‖C t S‖ = ‖C 0 S‖)
    (negative : Bool) (h : O) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, firstResidueEnergy p χ F Ω (C t) negative h ≤ M := by
  choose M hM hb using fun (D : Finset ι) (r : QuadraticRayRing × QuadraticRayRing) =>
    firstResidueColumn_uniform_bound p χ F D (if negative then r.1 else r.2) C hn h
  refine ⟨∑ D ∈ F.powerset, ∑ r : QuadraticRayRing × QuadraticRayRing,
    ‖firstResidueWeight p Ω D h r‖ * (M D r) ^ 2, by positivity, ?_⟩
  intro t
  apply Finset.sum_le_sum
  intro D _
  apply Finset.sum_le_sum
  intro r _
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hb D r t) 2)
    (norm_nonneg _)

theorem firstResidueEnergy_integrable (F : Finset ι)
    (Ω : QuadraticRayRing → QuadraticRayRing → ℂ)
    (C : ℝ → Finset ι → ℂ) (hc : ∀ S, Continuous (fun t => C t S))
    (hn : ∀ t S, ‖C t S‖ = ‖C 0 S‖) (negative : Bool) (h : O) (b : 𝓢(ℝ, ℂ)) :
    Integrable (fun t => ‖b t‖ * firstResidueEnergy p χ F Ω (C t) negative h) volume := by
  obtain ⟨M, hM, hb⟩ := firstResidueEnergy_uniform_bound p χ F Ω C hn negative h
  apply b.integrable.norm.mul_bdd (c := M)
  · exact (firstResidueEnergy_continuous p χ F Ω C hc negative h).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (firstResidueEnergy_nonneg p χ F Ω (C t) negative h)]
      exact hb t)

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
  (χ : ∀ i, MulChar (O ⧸ Ideal.span {p i}) ℂ)

theorem first_integral_norm_le_energy
    (F : Finset ι) (Ω : QuadraticRayRing → QuadraticRayRing → ℂ) (h : O)
    (H₁ H₂ : ℝ → Finset ι → ℂ)
    (hc₁ : ∀ S, Continuous (fun t => H₁ t S))
    (hc₂ : ∀ S, Continuous (fun t => H₂ t S))
    (hn₁ : ∀ t S, ‖H₁ t S‖ = ‖H₁ 0 S‖)
    (hn₂ : ∀ t S, ‖H₂ t S‖ = ‖H₂ 0 S‖) (b : 𝓢(ℝ, ℂ)) (a : ℂ) :
    ‖∫ t : ℝ, b t * a * firstResidueReindex p χ F Ω (H₁ t) (H₂ t) h‖ ≤
      Real.sqrt (∫ t : ℝ, ‖b t‖ * ‖a‖ * firstResidueEnergy p χ F Ω (H₁ t) true h) *
      Real.sqrt (∫ t : ℝ, ‖b t‖ * ‖a‖ * firstResidueEnergy p χ F Ω (H₂ t) false h) := by
  let E₁ := fun t => firstResidueEnergy p χ F Ω (H₁ t) true h
  let E₂ := fun t => firstResidueEnergy p χ F Ω (H₂ t) false h
  let w := fun t : ℝ => ‖b t‖ * ‖a‖
  have hE₁ : ∀ t, 0 ≤ E₁ t := fun t => firstResidueEnergy_nonneg p χ F Ω (H₁ t) true h
  have hE₂ : ∀ t, 0 ≤ E₂ t := fun t => firstResidueEnergy_nonneg p χ F Ω (H₂ t) false h
  have hw : ∀ t, 0 ≤ w t := fun t => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have i₁ : Integrable (fun t => w t * E₁ t) volume :=
    by simpa only [w, E₁, mul_assoc, mul_left_comm, mul_comm] using
      (firstResidueEnergy_integrable p χ F Ω H₁ hc₁ hn₁ true h b).mul_const ‖a‖
  have i₂ : Integrable (fun t => w t * E₂ t) volume :=
    by simpa only [w, E₂, mul_assoc, mul_left_comm, mul_comm] using
      (firstResidueEnergy_integrable p χ F Ω H₂ hc₂ hn₂ false h b).mul_const ‖a‖
  let f := fun t => Real.sqrt (w t * E₁ t)
  let g := fun t => Real.sqrt (w t * E₂ t)
  have hf : Continuous f := Real.continuous_sqrt.comp ((b.continuous.norm.mul continuous_const).mul
    (firstResidueEnergy_continuous p χ F Ω H₁ hc₁ true h))
  have hg' : Continuous g := Real.continuous_sqrt.comp ((b.continuous.norm.mul continuous_const).mul
    (firstResidueEnergy_continuous p χ F Ω H₂ hc₂ false h))
  have hfsq (t : ℝ) : f t ^ 2 = w t * E₁ t := Real.sq_sqrt (mul_nonneg (hw t) (hE₁ t))
  have hgsq (t : ℝ) : g t ^ 2 = w t * E₂ t := Real.sq_sqrt (mul_nonneg (hw t) (hE₂ t))
  have mf : MemLp f 2 volume := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mpr
    (by simpa only [hfsq] using i₁)
  have mg : MemLp g 2 volume := (memLp_two_iff_integrable_sq hg'.aestronglyMeasurable).mpr
    (by simpa only [hgsq] using i₂)
  have hfg (t : ℝ) : f t * g t = w t * (Real.sqrt (E₁ t) * Real.sqrt (E₂ t)) := by
    dsimp only [f, g]
    rw [Real.sqrt_mul (hw t), Real.sqrt_mul (hw t)]
    calc
      _ = (Real.sqrt (w t))^2 * (Real.sqrt (E₁ t) * Real.sqrt (E₂ t)) := by ring
      _ = _ := by rw [Real.sq_sqrt (hw t)]
  have hnorm : ‖∫ t : ℝ, b t * a * firstResidueReindex p χ F Ω (H₁ t) (H₂ t) h‖ ≤
      ∫ t : ℝ, f t * g t := by
    apply norm_integral_le_of_norm_le (mf.integrable_mul mg)
    exact Filter.Eventually.of_forall (fun t => by
      simp only [Pi.mul_apply]
      rw [hfg, norm_mul, norm_mul]
      exact mul_le_mul_of_nonneg_left
        (firstResidueReindex_norm_le p χ F Ω (H₁ t) (H₂ t) h) (hw t))
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (w t * E₁ t)))
    (Filter.Eventually.of_forall (fun t => Real.sqrt_nonneg (w t * E₂ t)))
    (show MemLp f (ENNReal.ofReal (2 : ℝ)) volume by simpa using mf)
    (show MemLp g (ENNReal.ofReal (2 : ℝ)) volume by simpa using mg)
  have hfinal : (∫ t : ℝ, f t * g t) ≤
      Real.sqrt (∫ t : ℝ, w t * E₁ t) * Real.sqrt (∫ t : ℝ, w t * E₂ t) := by
    simp only [Real.rpow_two, ← Real.sqrt_eq_rpow] at hh
    change (∫ t : ℝ, f t * g t) ≤
      Real.sqrt (∫ t : ℝ, f t ^ 2) * Real.sqrt (∫ t : ℝ, g t ^ 2) at hh
    simpa only [hfsq, hgsq] using hh
  exact hnorm.trans hfinal


end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def cubeLogCoefficient (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (d : O) : Finset ι → ℂ :=
  if negative then cubeMinusCoefficient p hg B v ε₁ ε₂ (logTwistMinus C V y t) d
  else cubePlusCoefficient p hg B v ε₁ ε₂ (logTwistPlus C V y t) d

theorem cubeLogCoefficient_continuous (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (d : O) (S : Finset ι) :
    Continuous (fun t => cubeLogCoefficient p hg B v ε₁ ε₂ negative C V y t d S) := by
  have ht := kernelLogPhase_continuous_left (-(y S))
  cases negative <;> simp only [cubeLogCoefficient, Bool.false_eq_true, ite_false, ite_true,
    cubeMinusCoefficient, cubePlusCoefficient, firstPassColumnMinus, firstPassColumnPlus,
    logTwistMinus, logTwistPlus] <;> fun_prop

theorem cubeLogCoefficient_norm_time (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (d : O) (S : Finset ι) :
    ‖cubeLogCoefficient p hg B v ε₁ ε₂ negative C V y t d S‖ =
      ‖cubeLogCoefficient p hg B v ε₁ ε₂ negative C V y 0 d S‖ := by
  cases negative <;> simp only [cubeLogCoefficient, Bool.false_eq_true, ite_false, ite_true,
    cubeMinusCoefficient, cubePlusCoefficient, firstPassColumnMinus, firstPassColumnPlus,
    logTwistMinus, logTwistPlus, norm_mul, norm_star, kernelLogPhase_norm]

/-- Integrated residue energy of a column after the first Poisson transformation. -/
def firstColumnEnergy (F B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (X : ℝ) (d h : O) (b : 𝓢(ℝ, ℂ)) : ℝ :=
  ∫ t : ℝ, ‖b t‖ * ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ *
    firstResidueEnergy p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F rayQuadraticPair
      (cubeLogCoefficient p hg B v ε₁ ε₂ negative (normalizedColumn p C) V (columnLog p X) t d)
      negative h

theorem firstColumnEnergy_nonneg (F B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (X : ℝ) (d h : O) (b : 𝓢(ℝ, ℂ)) :
    0 ≤ firstColumnEnergy p hp hg F B v ε₁ ε₂ negative C V X d h b := by
  apply integral_nonneg
  intro t
  exact mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    (firstResidueEnergy_nonneg p _ F rayQuadraticPair _ negative h)

/-- One Fourier density works for every pair of arithmetic columns. -/
theorem actual_first_kernel_uniform_energy_envelope
    (W : 𝓢(ℝ, ℂ)) (V₁ V₂ : ℝ → ℂ)
    (M₁ M₂ : ℝ) (hM₁ : 0 ≤ M₁) (hM₂ : 0 ≤ M₂)
    (hV₁ : ∀ x, V₁ x ≠ 0 → |x| ≤ M₁) (hV₂ : ∀ y, V₂ y ≠ 0 → |y| ≤ M₂)
    (A J : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀
      {ι : Type*} [DecidableEq ι]
      (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hinj : Function.Injective (fun i => Ideal.span {p i}))
      (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
      (hg : ∀ i, lambda ∉ Ideal.span {p i})
      (hc : ∀ i, ringChar (O ⧸ Ideal.span {p i}) ≠ 2)
      (hpr : ∀ i, lambda ^ 2 ∣ p i - 1) (F B : Finset ι) (hFB : Disjoint F B)
      (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
      (X₁ X₂ : ℝ) (hX₁ : 0 < X₁) (hX₂ : 0 < X₂), ∀ lengthScale : ℝ, 0 < lengthScale → ∀ d h : O, d ≠ 0 → h ≠ 0 →
      ∃ b : 𝓢(ℝ, ℂ),
        (∀ t : ℝ, (1 + firstDualScale p (cubeActiveSupport B v ε₁ ε₂) lengthScale X₁ X₂ d h) ^ A *
          ‖b t‖ ≤ K * firstLogDensity J t) ∧
        ∀ C₁ C₂ : Finset ι → ℂ,
          ‖actualFirstKernel p hp hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale d h‖ ≤
            (lengthScale / ‖ringComplex (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖) *
              Real.sqrt (firstColumnEnergy p hp hg F B v ε₁ ε₂ true C₁ V₁ X₁ d h b) *
              Real.sqrt (firstColumnEnergy p hp hg F B v ε₁ ε₂ false C₂ V₂ X₂ d h b) := by
  obtain ⟨K, hK, hs⟩ := actual_first_kernel_uniform_integral
    W V₁ V₂ M₁ M₂ hM₁ hM₂ hV₁ hV₂ A J
  refine ⟨K, hK, ?_⟩
  intro ι _ p hp _ hinj hcop hg hc hpr F B hFB v ε₁ ε₂ X₁ X₂ hX₁ hX₂
  have hs := hs p hp hinj hcop hg hc hpr F B hFB v ε₁ ε₂ X₁ X₂ hX₁ hX₂
  intro lengthScale hL d h hd hh
  obtain ⟨b, hb, he⟩ := hs lengthScale hL d h hd hh
  refine ⟨b, hb, ?_⟩
  intro C₁ C₂
  have heq := (he C₁ C₂).2
  let D₁ := fun t => cubeLogCoefficient p hg B v ε₁ ε₂ true
    (normalizedColumn p C₁) V₁ (columnLog p X₁) t d
  let D₂ := fun t => cubeLogCoefficient p hg B v ε₁ ε₂ false
    (normalizedColumn p C₂) V₂ (columnLog p X₂) t d
  have hiE := first_integral_norm_le_energy p
    (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F rayQuadraticPair h D₁ D₂
    (cubeLogCoefficient_continuous p hg B v ε₁ ε₂ true _ _ _ d)
    (cubeLogCoefficient_continuous p hg B v ε₁ ε₂ false _ _ _ d)
    (fun t S => cubeLogCoefficient_norm_time p hg B v ε₁ ε₂ true _ _ _ t d S)
    (fun t S => cubeLogCoefficient_norm_time p hg B v ε₁ ε₂ false _ _ _ t d S)
    b (cubeBaseFactor p hp hg B v ε₁ ε₂ d h)
  change actualFirstKernel p hp hg F B v ε₁ ε₂ C₁ C₂ W V₁ V₂ X₁ X₂ lengthScale d h = _ at heq
  rw [heq, norm_mul]
  have hn : ‖(lengthScale : ℂ) / (‖ringComplex (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ : ℂ)‖ =
      lengthScale / ‖ringComplex (∏ i ∈ cubeActiveSupport B v ε₁ ε₂, p i)‖ := by
    simp only [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hL.le,
      abs_of_nonneg (norm_nonneg _)]
  rw [hn, mul_assoc]
  exact mul_le_mul_of_nonneg_left hiE (div_nonneg hL.le (norm_nonneg _))

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical

variable {ι : Type*} [DecidableEq ι] (q : ι → O)
  [∀ i, (Ideal.span {q i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {q i})

include hg in
theorem mask_union (S T : Finset ι) (hd : Disjoint S T) (a : O) :
    primeCoprimeMask q (S ∪ T) a = primeCoprimeMask q S a * primeCoprimeMask q T a := by
  simp only [← row_sixth q hg, primeSubsetRow_union q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S T hd, mul_pow]

theorem row_four_star (S : Finset ι) (f h : O) :
    primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S f ^ 4 * star (primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S h) =
      star (primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (h * f ^ 2)) := by
  have hf : star (primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (f ^ 2)) =
      primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S f ^ 4 := by
    rw [row_pow, star_pow, sexticRow_star]
    calc
      _ = primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S f ^ 4 * primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S f ^ 6 := by ring
      _ = _ := by
        rw [row_sixth]
        simpa only [pow_one] using row_power_mul_mask_power q hg S f 4 1 (by decide)
  rw [subsetRow_mul, star_mul, hf]

def beforeDilationLabel {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (side : Bool) (c d f : O) (S : Finset ι) : ℂ :=
  primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S c ^ 4 * primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S d *
    (primeCoprimeMask q S (cubeRadical p B) *
      primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
      primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (crtLabel p B v ε₁ ε₂ side)) *
    primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S f ^ 4

def afterDilationLabel {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (c d : O) (S : Finset ι) : ℂ :=
  primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (c * jLabel p B v ε₁ ε₂) ^ 4 *
    primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S d * primeCoprimeMask q S (b0Label p B v ε₁ ε₂)

theorem beforeDilationLabel_union {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (side : Bool) (c d f : O)
    (S T : Finset ι) (hd : Disjoint S T) :
    beforeDilationLabel q hg p B v ε₁ ε₂ side c d f (S ∪ T) =
      beforeDilationLabel q hg p B v ε₁ ε₂ side c d f S *
      beforeDilationLabel q hg p B v ε₁ ε₂ side c d f T := by
  simp only [beforeDilationLabel, primeSubsetRow_union q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S T hd, mask_union q hg S T hd, mul_pow]
  ring

theorem beforeDilationLabel_norm_le_one {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (side : Bool) (c d f : O) (S : Finset ι) :
    ‖beforeDilationLabel q hg p B v ε₁ ε₂ side c d f S‖ ≤ 1 := by
  have hm : ‖primeCoprimeMask q S (cubeRadical p B)‖ ≤ 1 := by
    rw [primeCoprimeMask_indicator]
    split_ifs <;> simp
  simp only [beforeDilationLabel, norm_mul, norm_pow]
  calc
    _ ≤ (1:ℝ)^4 * 1 * (1 * 1^4 * 1) * 1^4 := by
      gcongr <;> first | exact hm | exact primeSubsetRow_norm_le_one q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S _
    _ = 1 := by norm_num

theorem beforeDilationLabel_star_row {κ : Type*} (p : κ → O) (B : Finset κ)
    (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (side : Bool) (c d f h : O) (S : Finset ι) :
    beforeDilationLabel q hg p B v ε₁ ε₂ side c d f S *
      star (primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S h) =
    afterDilationLabel q hg p B v ε₁ ε₂ c d S *
      star (primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (h * f^2 * dilationLabel p B v ε₁ ε₂)) := by
  unfold beforeDilationLabel afterDilationLabel
  calc
    _ = (primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S c ^ 4 * primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S d) *
      ((primeCoprimeMask q S (cubeRadical p B) *
        primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (aLabel p B (if side then ε₂ else ε₁)) ^ 4 *
        primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S (crtLabel p B v ε₁ ε₂ side)) *
        (primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S f ^ 4 * star (primeSubsetRow q (fun i => complexSexticChar (Ideal.span {q i}) (hg i)) S h))) := by ring
    _ = _ := by
      rw [row_four_star, first_pass_after_dual_dilation q hg S p B v ε₁ ε₂ hv side]
      simp only [subsetRow_mul, mul_pow]
      ring

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic
open scoped Classical

def originalLabelColumn {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (B : Finset ι) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (c f : O) (S : Finset ι) : ℂ :=
  C S * primeCoprimeMask p S (cubeRadical p B) *
    primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S
      (aLabel p B (if negative then ε₂ else ε₁) * c) ^ 4 *
    primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S f ^ 4

def cubeCoreCoefficient {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι) : ℂ :=
  if negative then
    star (fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S) *
      star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) S (-1)) *
      firstColumnPhase p hg S * C S *
      star (V (y S) * kernelLogPhase t (-(y S)))
  else
    fixedRayExpansion p (cubeOddSupport B v ε₁ ε₂) S *
      firstColumnPhase p hg S * C S *
      (V (y S) * kernelLogPhase t (-(y S)))

theorem cubeLogCoefficient_originalLabel {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i}) (B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) (c d f : O) (S : Finset ι) :
    cubeLogCoefficient p hg B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d S =
    cubeCoreCoefficient p hg B v ε₁ ε₂ negative C V y t S *
      beforeDilationLabel p hg p B v ε₁ ε₂ negative c d f S := by
  cases negative <;>
    simp only [cubeLogCoefficient, cubeCoreCoefficient, cubeMinusCoefficient,
      cubePlusCoefficient, firstPassColumnMinus,
      firstPassColumnPlus, logTwistMinus, logTwistPlus,
      originalLabelColumn, beforeDilationLabel, Bool.false_eq_true, ite_false, ite_true,
      subsetRow_mul, mul_pow] <;> ring

theorem normalized_originalLabelColumn {ι : Type*} (p : ι → O)
    [∀ i, (Ideal.span {p i}).IsMaximal] (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (B : Finset ι) (ε₁ ε₂ : ι → Bool) (negative : Bool)
    (C : Finset ι → ℂ) (c f : O) :
    normalizedColumn p (originalLabelColumn p hg B ε₁ ε₂ negative C c f) =
      originalLabelColumn p hg B ε₁ ε₂ negative (normalizedColumn p C) c f := by
  funext S
  simp only [normalizedColumn, originalLabelColumn, div_eq_mul_inv]
  ring


end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι] (p : ι → O)
  [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

def dilatedResidueColumn {κ : Type*} (F D : Finset ι) (r : QuadraticRayRing)
    (C : Finset ι → ℂ) (q : κ → O) (B : Finset κ) (v : κ → ℕ)
    (ε₁ ε₂ : κ → Bool) (c d y : O) : ℂ :=
  supportConjugateSum p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (F \ D)
    (firstResidueMask p r (fun U => C (D ∪ U) * afterDilationLabel p hg q B v ε₁ ε₂ c d U)) y

theorem firstResidueColumn_beforeDilation {κ : Type*}
    (F D : Finset ι) (r : QuadraticRayRing) (C : Finset ι → ℂ)
    (q : κ → O) (B : Finset κ) (v : κ → ℕ) (ε₁ ε₂ : κ → Bool)
    (hv : ∀ j ∈ B, 0 < v j) (side : Bool) (c d f h : O) :
    firstResidueColumn p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F D r
      (fun S => C S * beforeDilationLabel p hg q B v ε₁ ε₂ side c d f S) h =
      beforeDilationLabel p hg q B v ε₁ ε₂ side c d f D *
        dilatedResidueColumn p hg F D r C q B v ε₁ ε₂ c d
          (h * f ^ 2 * dilationLabel q B v ε₁ ε₂) := by
  unfold firstResidueColumn dilatedResidueColumn supportConjugateSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro U hU
  have hd : Disjoint D U := Finset.disjoint_of_subset_right
    (Finset.mem_powerset.mp hU) disjoint_sdiff_self_right
  unfold firstResidueMask
  split_ifs
  · dsimp only
    rw [beforeDilationLabel_union p hg q B v ε₁ ε₂ side c d f D U hd]
    calc
      _ = beforeDilationLabel p hg q B v ε₁ ε₂ side c d f D * supportMobius U * C (D ∪ U) *
        (beforeDilationLabel p hg q B v ε₁ ε₂ side c d f U *
          star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U h)) := by ring
      _ = _ := by rw [beforeDilationLabel_star_row p hg q B v ε₁ ε₂ hv side c d f h U]; ring
  · simp only [mul_zero, zero_mul]

theorem firstResidueColumn_cube_labels (F D B : Finset ι) (r : QuadraticRayRing)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (negative : Bool) (C : Finset ι → ℂ) (V : ℝ → ℂ)
    (y : Finset ι → ℝ) (t : ℝ) (c d f h : O) :
    firstResidueColumn p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F D r
      (cubeLogCoefficient p hg B v ε₁ ε₂ negative
        (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d) h =
      beforeDilationLabel p hg p B v ε₁ ε₂ negative c d f D *
        dilatedResidueColumn p hg F D r
          (cubeCoreCoefficient p hg B v ε₁ ε₂ negative C V y t)
          p B v ε₁ ε₂ c d (h * f ^ 2 * dilationLabel p B v ε₁ ε₂) := by
  have he : cubeLogCoefficient p hg B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V y t d =
      fun S => cubeCoreCoefficient p hg B v ε₁ ε₂ negative C V y t S *
        beforeDilationLabel p hg p B v ε₁ ε₂ negative c d f S := by
    funext S
    exact cubeLogCoefficient_originalLabel p hg B v ε₁ ε₂ negative C V y t c d f S
  rw [he]
  exact firstResidueColumn_beforeDilation p hg F D r _ p B v ε₁ ε₂ hv negative c d f h

/-- Dilation leaves exactly the mask and fourth-power label used by the second passage. -/
theorem dilatedResidueColumn_eq_inputRow {κ : Type*}
    (F D : Finset ι) (r : QuadraticRayRing) (C : Finset ι → ℂ)
    (q : κ → O) (B : Finset κ) (v : κ → ℕ) (ε₁ ε₂ : κ → Bool) (c d y : O) :
    dilatedResidueColumn p hg F D r C q B v ε₁ ε₂ c d y =
      inputConjugateRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) (F \ D)
        (1 : O →* ℂ) (b0Label q B v ε₁ ε₂) (c * jLabel q B v ε₁ ε₂) d
        (firstResidueMask p r (fun U => C (D ∪ U))) y := by
  unfold dilatedResidueColumn inputConjugateRow supportConjugateSum
  apply Finset.sum_congr rfl
  intro U _
  simp only [secondInputCoefficient, afterDilationLabel, MonoidHom.one_apply, one_mul]
  unfold firstResidueMask
  split_ifs <;> ring

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap

variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem firstColumnEnergy_original_labels (F B : Finset ι)
    (v : ι → ℕ) (ε₁ ε₂ : ι → Bool) (hv : ∀ j ∈ B, 0 < v j)
    (negative : Bool) (C : Finset ι → ℂ) (V : ℝ → ℂ) (X : ℝ)
    (c d f h : O) (b : 𝓢(ℝ, ℂ)) :
    firstColumnEnergy p hp hg F B v ε₁ ε₂ negative
      (originalLabelColumn p hg B ε₁ ε₂ negative C c f) V X d h b =
    ∫ t : ℝ, ‖b t‖ * ‖cubeBaseFactor p hp hg B v ε₁ ε₂ d h‖ *
      ∑ D ∈ F.powerset, ∑ r : QuadraticRayRing × QuadraticRayRing,
        ‖firstResidueWeight p rayQuadraticPair D h r‖ *
        (‖beforeDilationLabel p hg p B v ε₁ ε₂ negative c d f D‖ ^ 2 *
          ‖dilatedResidueColumn p hg F D (if negative then r.1 else r.2)
            (cubeCoreCoefficient p hg B v ε₁ ε₂ negative
              (normalizedColumn p C) V (columnLog p X) t)
            p B v ε₁ ε₂ c d (h * f ^ 2 * dilationLabel p B v ε₁ ε₂)‖ ^ 2) := by
  unfold firstColumnEnergy
  rw [normalized_originalLabelColumn]
  apply integral_congr_ae
  filter_upwards [] with t
  congr 1
  unfold firstResidueEnergy
  apply Finset.sum_congr rfl
  intro D _
  apply Finset.sum_congr rfl
  intro r _
  rw [firstResidueColumn_cube_labels p hg F D B _ v ε₁ ε₂ hv negative
    (normalizedColumn p C) V (columnLog p X) t c d f h, norm_mul, mul_pow]

def dilatedCoreRow (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (C : Finset ι → ℂ)
    (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d : O) (t : ℝ) (z : O) : ℂ :=
  dilatedResidueColumn p hg F D r
    (cubeCoreCoefficient p hg B v ε₁ ε₂ negative C V y t) p B v ε₁ ε₂ c d z

theorem cubeCoreCoefficient_continuous (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (S : Finset ι) :
    Continuous (fun t => cubeCoreCoefficient p hg B v ε₁ ε₂ negative C V y t S) := by
  have ht := kernelLogPhase_continuous_left (-(y S))
  cases negative <;> simp only [cubeCoreCoefficient, Bool.false_eq_true, ite_false, ite_true] <;> fun_prop

theorem cubeCoreCoefficient_norm_time (B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (C : Finset ι → ℂ) (V : ℝ → ℂ) (y : Finset ι → ℝ) (t : ℝ) (S : Finset ι) :
    ‖cubeCoreCoefficient p hg B v ε₁ ε₂ negative C V y t S‖ =
      ‖cubeCoreCoefficient p hg B v ε₁ ε₂ negative C V y 0 S‖ := by
  cases negative <;> simp only [cubeCoreCoefficient, Bool.false_eq_true, ite_false, ite_true,
    norm_mul, norm_star, kernelLogPhase_norm]

theorem dilatedCoreRow_continuous (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (C : Finset ι → ℂ)
    (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d z : O) :
    Continuous (fun t => dilatedCoreRow p hg F D B v ε₁ ε₂ negative r C V y c d t z) := by
  unfold dilatedCoreRow dilatedResidueColumn supportConjugateSum
  apply continuous_finsetSum
  intro U _
  unfold firstResidueMask
  split_ifs
  · exact (continuous_const.mul ((cubeCoreCoefficient_continuous p hg B v ε₁ ε₂ negative C V y
      (D ∪ U)).mul continuous_const)).mul continuous_const
  · exact continuous_const

theorem dilatedCoreRow_uniform_bound (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (C : Finset ι → ℂ)
    (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d z : O) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t, ‖dilatedCoreRow p hg F D B v ε₁ ε₂ negative r C V y c d t z‖ ≤ M := by
  let q := fun (t : ℝ) (U : Finset ι) => supportMobius U *
    firstResidueMask p r (fun U => cubeCoreCoefficient p hg B v ε₁ ε₂ negative C V y t (D ∪ U) *
      afterDilationLabel p hg p B v ε₁ ε₂ c d U) U *
        star (primeSubsetRow p (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) U z)
  refine ⟨∑ U ∈ (F \ D).powerset, ‖q 0 U‖, by positivity, ?_⟩
  intro t
  change ‖∑ U ∈ (F \ D).powerset, q t U‖ ≤ _
  apply (norm_sum_le _ _).trans_eq
  apply Finset.sum_congr rfl
  intro U _
  dsimp only [q]
  unfold firstResidueMask
  split_ifs <;> simp only [norm_mul, cubeCoreCoefficient_norm_time]

theorem dilatedCoreRow_integrable (F D B : Finset ι) (v : ι → ℕ) (ε₁ ε₂ : ι → Bool)
    (negative : Bool) (r : QuadraticRayRing) (C : Finset ι → ℂ)
    (V : ℝ → ℂ) (y : Finset ι → ℝ) (c d z : O) {k : ℝ → ℝ} (hk : Integrable k volume) :
    Integrable (fun t => k t * ‖dilatedCoreRow p hg F D B v ε₁ ε₂ negative r C V y c d t z‖ ^ 2) volume := by
  obtain ⟨M, hM, hb⟩ := dilatedCoreRow_uniform_bound p hg F D B v ε₁ ε₂ negative r C V y c d z
  apply hk.mul_bdd (c := M ^ 2)
  · exact ((dilatedCoreRow_continuous p hg F D B v ε₁ ε₂ negative r C V y c d z).norm.pow 2).aestronglyMeasurable
  · exact Filter.Eventually.of_forall (fun t => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) (hb t) 2)

end FirstPassCubeLabels

namespace FirstPassCubeLabels
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic MeasureTheory
open scoped Classical SchwartzMap

/-- Divisor fibers cost an arbitrarily small power of the dilated row norm. -/
theorem first_cube_energy_small_power (δ : ℝ) (hδ : 0 < δ) :
    ∃ K : ℝ, 0 < K ∧ ∀ {ι : Type*} [DecidableEq ι]
      (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
      (hg : ∀ i, lambda ∉ Ideal.span {p i}) (F D B : Finset ι)
      (v : ι → ℕ) (ε₁ ε₂ : ι → Bool), (∀ j ∈ B, 0 < v j) →
      ∀ (negative : Bool) (r : QuadraticRayRing) (C : Finset ι → ℂ) (V : ℝ → ℂ)
      (y : Finset ι → ℝ) (t : ℝ) (c d : O)
      (s : Finset (Ideal O × O)) (T : Finset O) (w : Ideal O × O → ℂ) (M Y : ℝ),
      0 ≤ M →
      (∀ x ∈ s, DescentWeightedCauchy.firstElementRowMap (dilationLabel p B v ε₁ ε₂) x ∈ T) →
      (∀ z ∈ T, z ≠ 0) → (∀ z ∈ T, (Ideal.absNorm (Ideal.span {z}) : ℝ) ≤ Y) →
      (∀ x ∈ s, ‖w x‖ ≤ M) →
      (∑ x ∈ s, ‖w x‖ * ‖firstResidueColumn p
        (fun i => complexSexticChar (Ideal.span {p i}) (hg i)) F D r
        (cubeLogCoefficient p hg B v ε₁ ε₂ negative
          (originalLabelColumn p hg B ε₁ ε₂ negative C c (cubicIdealGenerator x.1)) V y t d) x.2‖ ^ 2) ≤
      M * K * Y ^ δ * ∑ z ∈ T,
        ‖dilatedCoreRow p hg F D B v ε₁ ε₂ negative r C V y c d t z‖ ^ 2 := by
  obtain ⟨K, hK, hpush⟩ := DescentWeightedCauchy.first_element_energy_small_power δ hδ
  refine ⟨K, hK, ?_⟩
  intro ι _ p _ hg F D B v ε₁ ε₂ hv negative r C V y t c d s T w M Y hM hmap hT hnorm hw
  apply le_trans _ (hpush s T (dilationLabel p B v ε₁ ε₂) w
    (dilatedCoreRow p hg F D B v ε₁ ε₂ negative r C V y c d t) M Y hM hmap hT hnorm hw)
  apply Finset.sum_le_sum
  intro x hx
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply pow_le_pow_left₀ (norm_nonneg _)
  rw [firstResidueColumn_cube_labels p hg F D B r v ε₁ ε₂ hv negative C V y t c d,
    norm_mul]
  exact mul_le_of_le_one_left (norm_nonneg _)
    (beforeDilationLabel_norm_le_one p hg p B v ε₁ ε₂ negative c d (cubicIdealGenerator x.1) D)

end FirstPassCubeLabels

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
