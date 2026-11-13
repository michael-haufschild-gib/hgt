/-
Ideal row characters adapted from OpenAI's formalization, Apache-2.0.
See LICENSE and NOTICE in the parent directory for source attribution.
-/
import GaloisForLFunctions.MetaplecticMobiusDescent.CubicSieve.CanonicalCubeSeparation

/-!
# Ideal row characters

Multiplicative ideal rows `idealRowHom` from prescribed prime values, fixed bad primes, prime
pools and row twists. Bounded nonzero ideals avoiding a fixed prime set; binned energies of the
outside canonical rows.
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

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic MeasureTheory
open scoped Classical

/-- Polynomially weighted integration preserves finite row-energy bounds. -/
theorem finite_integral_energy_polynomial {κ : Type*} [Fintype κ]
    (b : ℝ → ℂ) (φ : κ → ℝ → ℂ) (d : ℕ) (E : ℝ) (hE : 0  ≤  E)
    (hb : Integrable (fun t => ‖b t‖*(1+|t|)^d))
    (hφ : ∀ k, Integrable (fun t => b t*φ k t))
    (hbound : ∀ t, (∑ k, ‖φ k t‖^2)  ≤  E*(1+|t|)^(2*d)) :
    (∑ k, ‖∫ t : ℝ, b t*φ k t‖^2)  ≤ 
      E*(∫ t : ℝ, ‖b t‖*(1+|t|)^d)^2 := by
  let e := PiLp.continuousLinearEquiv 2 ℂ (fun _ : κ => ℂ)
  let F : ℝ → EuclideanSpace ℂ κ := fun t => e.symm (fun k => b t*φ k t)
  have hF (t : ℝ) : ‖F t‖  ≤  (‖b t‖*(1+|t|)^d)*Real.sqrt E := by
    apply (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp
    rw [EuclideanSpace.norm_sq_eq]
    change (∑ k, ‖b t*φ k t‖^2)  ≤  _
    simp only [norm_mul,mul_pow,← Finset.mul_sum,Real.sq_sqrt hE]
    have hp : (1+|t|)^(2*d) = ((1+|t|)^d)^2 := by
      rw [← pow_mul,Nat.mul_comm d 2]
    calc
      _  ≤  ‖b t‖^2 * (E*(1+|t|)^(2*d)) :=
        mul_le_mul_of_nonneg_left (hbound t) (sq_nonneg _)
      _ = _ := by rw [hp]; ring
  have he : (∫ t : ℝ, F t) = e.symm (fun k => ∫ t : ℝ, b t*φ k t) := by
    rw [show F = (fun t => e.symm (fun k => b t*φ k t)) from rfl,
      e.symm.integral_comp_comm]
    congr 1
    funext k
    exact eval_integral hφ k
  have hn : ‖e.symm (fun k => ∫ t : ℝ, b t*φ k t)‖  ≤ 
      (∫ t : ℝ, ‖b t‖*(1+|t|)^d)*Real.sqrt E := by
    rw [← he,← integral_mul_const]
    exact norm_integral_le_of_norm_le (hb.mul_const _)
      (Filter.Eventually.of_forall hF)
  have hh := pow_le_pow_left₀ (norm_nonneg _) hn 2
  rw [EuclideanSpace.norm_sq_eq,mul_pow,Real.sq_sqrt hE] at hh
  change (∑ k, ‖∫ t : ℝ, b t*φ k t‖^2)  ≤ 
    (∫ t : ℝ, ‖b t‖*(1+|t|)^d)^2 * E at hh
  simpa only [mul_comm] using hh

theorem norm_add_sum_sq_le {κ : Type*} (s : Finset κ) (a : ℂ) (b : κ → ℂ) :
    ‖a + ∑ k ∈ s, b k‖^2  ≤  2*(‖a‖^2 + s.card*∑ k ∈ s, ‖b k‖^2) := by
  have hs : ‖∑ k ∈ s, b k‖^2  ≤  (s.card : ℝ)*∑ k ∈ s, ‖b k‖^2 := by
    calc
      _  ≤  (∑ k ∈ s, ‖b k‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _  ≤  _ := by
        simpa only [one_mul,one_pow,Finset.sum_const,nsmul_eq_mul,mul_one]
          using Finset.sum_mul_sq_le_sq_mul_sq s (fun _ => (1:ℝ)) (fun k => ‖b k‖)
  have ha := pow_le_pow_left₀ (norm_nonneg _) (norm_add_le a (∑ k ∈ s, b k)) 2
  nlinarith [sq_nonneg (‖a‖ - ‖∑ k ∈ s, b k‖)]

def rowFamilyEnergy (labels : Finset (Ideal O)) (P : Ideal O → O → ℂ) (K : ℝ) : ℝ :=
  (∑ I ∈ labels, nonzeroRowMajorantSum (P I) K).re

theorem rowFamilyEnergy_eq_sum (labels : Finset (Ideal O)) (P : Ideal O → O → ℂ)
    (K : ℝ) (hK : 0 < K) :
    rowFamilyEnergy labels P K =
      ∑ I ∈ labels, ∑ z ∈ (firstFrequencyDisk (2*K)).erase 0,
        (rowMajorant (‖ringComplex z‖^2/K)).re * ‖P I z‖^2 := by
  unfold rowFamilyEnergy
  simp only [nonzeroRowMajorantSum_exact_disk _ K hK, Complex.re_sum,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]

theorem rowFamilyEnergy_nonneg (labels : Finset (Ideal O)) (P : Ideal O → O → ℂ)
    (K : ℝ) (hK : 0 < K) : 0  ≤  rowFamilyEnergy labels P K := by
  rw [rowFamilyEnergy_eq_sum labels P K hK]
  exact Finset.sum_nonneg (fun I hI => Finset.sum_nonneg
    (fun z hz => mul_nonneg (rowMajorant_nonneg _) (sq_nonneg _)))

theorem rowFamilyEnergy_integral_polynomial
    (labels : Finset (Ideal O)) (K : ℝ) (hK : 0 < K)
    (b : ℝ → ℂ) (φ : Ideal O → O → ℝ → ℂ) (d : ℕ) (E : ℝ) (hE : 0  ≤  E)
    (hb : Integrable (fun t => ‖b t‖*(1+|t|)^d))
    (hφ : ∀ I z, Integrable (fun t => b t*φ I z t))
    (hbound : ∀ t, rowFamilyEnergy labels (fun I z => φ I z t) K  ≤  E*(1+|t|)^(2*d)) :
    rowFamilyEnergy labels (fun I z => ∫ t : ℝ, b t*φ I z t) K  ≤ 
      E*(∫ t : ℝ, ‖b t‖*(1+|t|)^d)^2 := by
  let R := (firstFrequencyDisk (2*K)).erase 0
  let w : O → ℝ := fun z => Real.sqrt ((rowMajorant (‖ringComplex z‖^2/K)).re)
  have hw (z : O) : 0  ≤  w z := Real.sqrt_nonneg _
  have hw2 (z : O) : (w z)^2 = (rowMajorant (‖ringComplex z‖^2/K)).re :=
    Real.sq_sqrt (rowMajorant_nonneg _)
  have hsum (P : Ideal O → O → ℂ) :
      (∑ x : labels × R, ‖(w x.2.val : ℂ)*P x.1.val x.2.val‖^2) = rowFamilyEnergy labels P K := by
    rw [rowFamilyEnergy_eq_sum labels P K hK]
    simp only [Fintype.sum_prod_type]
    rw [Finset.sum_coe_sort (s := labels)
      (f := fun I : Ideal O => ∑ z : R, ‖(w z.val : ℂ)*P I z.val‖^2)]
    apply Finset.sum_congr rfl
    intro I hI
    rw [Finset.sum_coe_sort (s := R) (f := fun z : O => ‖(w z : ℂ)*P I z‖^2)]
    apply Finset.sum_congr rfl
    intro z hz
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hw z),mul_pow,hw2]
  let ψ : labels × R → ℝ → ℂ := fun x t => (w x.2.val : ℂ)*φ x.1.val x.2.val t
  have hψ (x : labels × R) : Integrable (fun t => b t*ψ x t) := by
    have he : (fun t => b t*ψ x t) =
        (fun t => (w x.2.val : ℂ)*(b t*φ x.1.val x.2.val t)) := by
      funext t
      dsimp only [ψ]
      ring
    rw [he]
    exact (hφ x.1.val x.2.val).const_mul (w x.2.val : ℂ)
  have hψbound (t : ℝ) : (∑ x : labels × R, ‖ψ x t‖^2)  ≤  E*(1+|t|)^(2*d) := by
    change (∑ x : labels × R, ‖(w x.2.val : ℂ)*φ x.1.val x.2.val t‖^2)  ≤  _
    rw [hsum (fun I z => φ I z t)]
    exact hbound t
  have hi (x : labels × R) :
      (∫ t : ℝ, b t*ψ x t) = (w x.2.val : ℂ)*(∫ t : ℝ, b t*φ x.1.val x.2.val t) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [] with t
    dsimp only [ψ]
    ring
  have hm := finite_integral_energy_polynomial b ψ d E hE hb hψ hψbound
  simp_rw [hi] at hm
  rwa [hsum (fun I z => ∫ t : ℝ, b t*φ I z t)] at hm

theorem rowFamilyEnergy_const_mul (labels : Finset (Ideal O)) (P : Ideal O → O → ℂ)
    (K : ℝ) (hK : 0 < K) (c : ℂ) :
    rowFamilyEnergy labels (fun I z => c*P I z) K = ‖c‖^2*rowFamilyEnergy labels P K := by
  simp only [rowFamilyEnergy_eq_sum _ _ K hK, norm_mul, mul_pow, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro I hI
  apply Finset.sum_congr rfl
  intro z hz
  ring

theorem canonicalSmoothedEnergy_eq_rowFamilyEnergy {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (pool : Finset ι) (Ψ : O →* ℂ) (m : O) (labels : Finset (Ideal O))
    (H : Finset ι → ℂ) (K : ℝ) :
    canonicalSmoothedEnergy p hg pool Ψ m labels H K =
      rowFamilyEnergy labels (fun I z => fixedChildRow p hg pool Ψ m H (cubicIdealGenerator I) z) K := rfl

theorem rowFamilyEnergy_bound_sum {κ : Type*}
    (labels : Finset (Ideal O)) (bins : Finset κ) (K : ℝ) (hK : 0 < K)
    (P A : Ideal O → O → ℂ) (B : κ → Ideal O → O → ℂ) (c N : ℝ)
    (hbound : ∀ I ∈ labels, ∀ z ∈ (firstFrequencyDisk (2*K)).erase 0,
      ‖P I z‖^2  ≤  c*(‖A I z‖^2 + N*∑ j ∈ bins, ‖B j I z‖^2)) :
    rowFamilyEnergy labels P K  ≤ 
      c*(rowFamilyEnergy labels A K + N*∑ j ∈ bins, rowFamilyEnergy labels (B j) K) := by
  let R := (firstFrequencyDisk (2*K)).erase 0
  let w : O → ℝ := fun z => (rowMajorant (‖ringComplex z‖^2/K)).re
  have hswap : (∑ I ∈ labels, ∑ z ∈ R, w z*∑ j ∈ bins, ‖B j I z‖^2) =
      ∑ j ∈ bins, rowFamilyEnergy labels (B j) K := by
    simp_rw [Finset.mul_sum]
    calc
      _ = ∑ I ∈ labels, ∑ j ∈ bins, ∑ z ∈ R, w z*‖B j I z‖^2 :=
        Finset.sum_congr rfl (fun I hI => Finset.sum_comm)
      _ = ∑ j ∈ bins, ∑ I ∈ labels, ∑ z ∈ R, w z*‖B j I z‖^2 := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl (fun j hj => (rowFamilyEnergy_eq_sum labels (B j) K hK).symm)
  rw [rowFamilyEnergy_eq_sum labels P K hK]
  calc
    _  ≤  ∑ I ∈ labels, ∑ z ∈ R,
        (c*(w z*‖A I z‖^2) + c*N*(∑ j ∈ bins, w z*‖B j I z‖^2)) := by
      apply Finset.sum_le_sum
      intro I hI
      apply Finset.sum_le_sum
      intro z hz
      calc
        _  ≤  w z*(c*(‖A I z‖^2 + N*∑ j ∈ bins, ‖B j I z‖^2)) :=
          mul_le_mul_of_nonneg_left (hbound I hI z hz) (rowMajorant_nonneg _)
        _ = _ := by rw [← Finset.mul_sum]; ring
    _ = c*(rowFamilyEnergy labels A K + N*∑ j ∈ bins, rowFamilyEnergy labels (B j) K) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
      rw [hswap, ← rowFamilyEnergy_eq_sum labels A K hK]
      ring


end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson FirstPassCubeLabels SecondPassArithmetic UniqueFactorizationMonoid
open scoped Classical

/-- Multiplicative extension of prescribed prime values, vanishing at the zero ideal. -/
def primeValueHom (w : Ideal O → ℂ) : Ideal O →*₀ ℂ where
  toFun I := if I=0 then 0 else ((UniqueFactorizationMonoid.normalizedFactors I).map w).prod
  map_zero' := by simp
  map_one' := by
    rw [if_neg one_ne_zero,UniqueFactorizationMonoid.normalizedFactors_one]
    rfl
  map_mul' I J := by
    by_cases hI : I=0
    · simp [hI]
    by_cases hJ : J=0
    · simp [hJ]
    simp only [if_neg hI,if_neg hJ,if_neg (mul_ne_zero hI hJ),
      UniqueFactorizationMonoid.normalizedFactors_mul hI hJ,Multiset.map_add,Multiset.prod_add]

theorem primeValueHom_prime (w : Ideal O → ℂ) (P : Ideal O) (hP : Prime P) :
    primeValueHom w P = w P := by
  change (if P=0 then 0 else _) = w P
  rw [if_neg hP.ne_zero,
    UniqueFactorizationMonoid.normalizedFactors_irreducible hP.irreducible]
  simp only [normalize_eq,Multiset.map_singleton,Multiset.prod_singleton]

theorem primeValueHom_norm_le_one (w : Ideal O → ℂ) (hw : ∀ P,‖w P‖ ≤ 1)
    (I : Ideal O) : ‖primeValueHom w I‖ ≤ 1 := by
  by_cases hI : I=0
  · rw [hI,map_zero,norm_zero]
    exact zero_le_one
  change ‖if I=0 then 0 else _‖ ≤ 1
  rw [if_neg hI]
  have hprod (s : Multiset (Ideal O)) : ‖(s.map w).prod‖ ≤ 1 := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons P s ih =>
      simp only [Multiset.map_cons,Multiset.prod_cons,norm_mul]
      exact (mul_le_of_le_one_left (norm_nonneg _) (hw P)).trans ih
  exact hprod _

def principalIdealHom : O →*₀ Ideal O where
  toFun n := Ideal.span {n}
  map_zero' := by simp
  map_one' := by simp
  map_mul' a b := (Ideal.span_singleton_mul_span_singleton a b).symm

def localRowValue (x : O) (P : Ideal O) : ℂ :=
  if h : P.IsMaximal ∧ lambda∉P then
    letI : P.IsMaximal := h.1
    complexSexticChar P h.2 (Ideal.Quotient.mk P x)
  else 0

theorem localRowValue_good (x : O) (P : Ideal O) [P.IsMaximal] (hg : lambda∉P) :
    localRowValue x P = complexSexticChar P hg (Ideal.Quotient.mk P x) := by
  simp only [localRowValue,dif_pos (show P.IsMaximal ∧ lambda∉P from ⟨inferInstance,hg⟩)]

theorem localRowValue_norm (x : O) (P : Ideal O) : ‖localRowValue x P‖ ≤ 1 := by
  unfold localRowValue
  split_ifs with h
  · let : P.IsMaximal := h.1
    let : Fintype (O⧸P) := Fintype.ofFinite _
    exact FiniteRayExpansion.norm_char_le_one _ _
  · simp

def idealRowHom (x : O) : Ideal O →*₀ ℂ := primeValueHom (localRowValue x)

def rowTwist (Ψ : O →* ℂ) (m f z : O) : O →* ℂ :=
  Ψ * (idealRowHom (m^6*f^4*z)).toMonoidHom.comp principalIdealHom.toMonoidHom

theorem idealRowHom_prime (x : O) (P : Ideal O) [P.IsMaximal] (hg : lambda∉P) :
    idealRowHom x P = complexSexticChar P hg (Ideal.Quotient.mk P x) := by
  rw [idealRowHom,primeValueHom_prime _ P
    (Ideal.prime_of_isPrime (NeZero.ne P) inferInstance),localRowValue_good]

theorem idealRowHom_norm (x : O) (I : Ideal O) : ‖idealRowHom x I‖ ≤ 1 :=
  primeValueHom_norm_le_one _ (localRowValue_norm x) I

theorem rowTwist_norm (Ψ : O →* ℂ) (hΨ : ∀n,‖Ψ n‖ ≤ 1) (m f z n : O) :
    ‖rowTwist Ψ m f z n‖ ≤ 1 := by
  change ‖Ψ n * idealRowHom (m^6*f^4*z) (Ideal.span {n})‖ ≤ 1
  rw [norm_mul]
  exact (mul_le_of_le_one_left (norm_nonneg _) (hΨ n)).trans (idealRowHom_norm _ _)

theorem idealRowHom_product {ι : Type*} (p : ι → O)
    [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
    (S : Finset ι) (x : O) :
    idealRowHom x (Ideal.span {∏i∈S,p i}) =
      primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S x := by
  rw [span_finset_prime_product,map_prod]
  simp only [primeSubsetRow]
  apply Finset.prod_congr rfl
  intro i hi
  exact idealRowHom_prime x _ (hg i)

theorem rowTwist_product {ι : Type*} (p : ι → O)
    [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i})
    (S : Finset ι) (Ψ : O →* ℂ) (m f z : O) :
    rowTwist Ψ m f z (∏i∈S,p i) =
      Ψ (∏i∈S,p i)*primeCoprimeMask p S m*
        primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S f^4*
        primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S z := by
  change Ψ _ * idealRowHom _ (Ideal.span {∏i∈S,p i}) = _
  rw [idealRowHom_product p hg S,subsetRow_mul,subsetRow_mul,
    FirstPassCubeLabels.row_pow,FirstPassCubeLabels.row_pow,FirstPassCubeLabels.row_sixth]
  ring

theorem localRowValue_zero_of_mem (x : O) (P : Ideal O) (hx : x∈P) :
    localRowValue x P = 0 := by
  unfold localRowValue
  split_ifs with h
  · let : P.IsMaximal := h.1
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact MulChar.map_nonunit _ (not_isUnit_zero)
  · rfl

theorem idealRowHom_zero_of_dvd (x : O) {P I : Ideal O}
    (hP : Prime P) (hPI : P∣I) (hx : x∈P) : idealRowHom x I = 0 := by
  obtain ⟨J,rfl⟩ := hPI
  rw [map_mul]
  have hz : idealRowHom x P = 0 := by
    rw [idealRowHom,primeValueHom_prime _ P hP,localRowValue_zero_of_mem x P hx]
  rw [hz,zero_mul]


theorem localRowValue_mul (a b : O) (P : Ideal O) :
    localRowValue (a*b) P = localRowValue a P * localRowValue b P := by
  unfold localRowValue
  split_ifs with h
  · let : P.IsMaximal := h.1
    simp only [map_mul]
  · simp

theorem idealRowHom_argument_mul (a b : O) (I : Ideal O) :
    idealRowHom (a*b) I = idealRowHom a I * idealRowHom b I := by
  by_cases hI : I=0
  · rw [hI,map_zero,map_zero,map_zero,zero_mul]
  change (if I=0 then 0 else _) = (if I=0 then 0 else _) * (if I=0 then 0 else _)
  simp only [if_neg hI]
  have hprod (s : Multiset (Ideal O)) :
      (s.map (localRowValue (a*b))).prod =
        (s.map (localRowValue a)).prod * (s.map (localRowValue b)).prod := by
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons P s ih =>
      simp only [Multiset.map_cons,Multiset.prod_cons]
      rw [localRowValue_mul,ih]
      ring
  exact hprod _

theorem rowTwist_row_factor (Ψ : O →* ℂ) (m f z n : O) :
    rowTwist Ψ m f z n =
      rowTwist Ψ m f 1 n * idealRowHom z (Ideal.span {n}) := by
  change Ψ n * idealRowHom (m^6*f^4*z) (Ideal.span {n}) =
    (Ψ n * idealRowHom (m^6*f^4*1) (Ideal.span {n})) * idealRowHom z (Ideal.span {n})
  rw [mul_one,idealRowHom_argument_mul]
  ring


end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic UniqueFactorizationMonoid
open scoped Classical

/-- Prime support shared by a finite ideal family. -/
noncomputable def primePool (F : Finset (Ideal O)) : Finset (Ideal O) :=
  F.biUnion (fun I => (UniqueFactorizationMonoid.normalizedFactors I).toFinset)

theorem mem_primePool_iff {F : Finset (Ideal O)} {P : Ideal O} :
    P ∈ primePool F ↔
      ∃ I ∈ F, P ∈ UniqueFactorizationMonoid.normalizedFactors I := by
  classical
  simp only [primePool, Finset.mem_biUnion, Multiset.mem_toFinset]

noncomputable def idealSupport (F : Finset (Ideal O)) (I : Ideal O) :
    Finset (primePool F) :=
  Finset.univ.filter (fun i => i.1 ∈ UniqueFactorizationMonoid.normalizedFactors I)

theorem mem_idealSupport_iff (F : Finset (Ideal O)) (I : Ideal O)
    (i : primePool F) :
    i ∈ idealSupport F I ↔ i.1 ∈ UniqueFactorizationMonoid.normalizedFactors I := by
  classical
  simp [idealSupport]

theorem idealSupport_image_eq_factors
    (F : Finset (Ideal O)) {I : Ideal O} (hI : I ∈ F) :
    (idealSupport F I).image Subtype.val =
      (UniqueFactorizationMonoid.normalizedFactors I).toFinset := by
  ext P
  simp only [Finset.mem_image, Multiset.mem_toFinset]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact (mem_idealSupport_iff F I p).mp hp
  · intro hP
    let p : primePool F := ⟨P, mem_primePool_iff.mpr ⟨I, hI, hP⟩⟩
    exact ⟨p, (mem_idealSupport_iff F I p).mpr hP, rfl⟩

theorem idealSupport_product_eq
    (F : Finset (Ideal O)) {I : Ideal O} (hI : I ∈ F) (hsI : Squarefree I) :
    (∏ i ∈ idealSupport F I, i.val) = I := by
  have hnodup := (UniqueFactorizationMonoid.squarefree_iff_nodup_normalizedFactors
    hsI.ne_zero).mp hsI
  calc
    _ = ∏ P ∈ (idealSupport F I).image Subtype.val, P := by
      rw [Finset.prod_image]
      exact fun a ha b hb h => Subtype.val_injective h
    _ = ∏ P ∈ (UniqueFactorizationMonoid.normalizedFactors I).toFinset, P := by
      rw [idealSupport_image_eq_factors F hI]
    _ = (UniqueFactorizationMonoid.normalizedFactors I).prod := by
      change ((UniqueFactorizationMonoid.normalizedFactors I).toFinset.val.map id).prod = _
      rw [Multiset.map_id, Multiset.toFinset_val, Multiset.dedup_eq_self.mpr hnodup]
    _ = I := Ideal.prod_normalizedFactors_eq_self hsI.ne_zero
instance canonicalPoolMaximal (F : Finset (Ideal O)) (i : primePool F) : i.val.IsMaximal := by
  obtain ⟨I, hIF, hi⟩ := mem_primePool_iff.mp i.property
  have hp := UniqueFactorizationMonoid.prime_of_normalized_factor i.val hi
  exact (Ideal.isPrime_of_prime hp).isMaximal hp.ne_zero

theorem poolGood (F : Finset (Ideal O)) (hF : ∀ I∈F,quadraticIdealAdmissible I)
    (i : primePool F) : lambda∉i.val := by
  obtain ⟨I,hIF,hi⟩:=mem_primePool_iff.mp i.property
  exact (primaryIdealPrime_spec i.val (primaryIdealPrime_factor_ne_zero I i.val (hF I hIF).1 hi)).2.1

theorem poolOdd (F : Finset (Ideal O)) (hF : ∀ I∈F,quadraticIdealAdmissible I)
    (i : primePool F) : ringChar (O⧸i.val)≠2 := by
  obtain ⟨I,hIF,hi⟩:=mem_primePool_iff.mp i.property
  exact (hF I hIF).2.2 i.val (Multiset.mem_toFinset.mpr hi)

def poolPrimary (F : Finset (Ideal O)) (i : primePool F) : O := primaryIdealPrime i.val

theorem poolPrimary_ne_zero (F : Finset (Ideal O)) (hF : ∀ I ∈ F, quadraticIdealAdmissible I)
    (i : primePool F) : poolPrimary F i ≠ 0 := primaryIdealPrime_ne_zero i.val (poolGood F hF i)

theorem poolPrimary_span (F : Finset (Ideal O)) (hF : ∀ I ∈ F, quadraticIdealAdmissible I)
    (i : primePool F) : Ideal.span {poolPrimary F i} = i.val :=
  (primaryIdealPrime_spec i.val (poolPrimary_ne_zero F hF i)).2.2.1

theorem primaryIdealPrime_eq_primaryIdealGenerator (P : Ideal O) [P.IsMaximal] :
    primaryIdealPrime P = primaryIdealGenerator P := by
  have hp : Prime P := Ideal.prime_of_isPrime (NeZero.ne P) inferInstance
  rw [primaryIdealGenerator, if_neg hp.ne_zero, UniqueFactorizationMonoid.normalizedFactors_irreducible hp.irreducible,
    normalize_eq]
  simp only [Multiset.map_singleton, Multiset.prod_singleton]

theorem primaryIdealGenerator_eq_poolProduct (F : Finset (Ideal O)) (hF : ∀ I ∈ F, quadraticIdealAdmissible I)
    (I : Ideal O) (hIF : I ∈ F) :
    primaryIdealGenerator I = ∏ i ∈ idealSupport F I, poolPrimary F i := by
  calc
    _ = primaryIdealGenerator (∏ i ∈ idealSupport F I, i.val) :=
      congrArg primaryIdealGenerator (idealSupport_product_eq F hIF (hF I hIF).2.1).symm
    _ = ∏ i ∈ idealSupport F I, primaryIdealGenerator i.val := by
      change primaryIdealGeneratorHom (∏ i ∈ idealSupport F I, i.val) =
        ∏ i ∈ idealSupport F I, primaryIdealGeneratorHom i.val
      rw [map_prod]
    _ = _ := Finset.prod_congr rfl (fun i hi => (primaryIdealPrime_eq_primaryIdealGenerator i.val).symm)

theorem poolPrimary_coprime (F : Finset (Ideal O)) (hF : ∀ I ∈ F, quadraticIdealAdmissible I) :
    Pairwise (Function.onFun IsCoprime (fun i : primePool F => Ideal.span {poolPrimary F i})) := by
  intro i j hij
  change IsCoprime (Ideal.span {poolPrimary F i}) (Ideal.span {poolPrimary F j})
  rw [poolPrimary_span F hF i, poolPrimary_span F hF j]
  exact Ideal.isCoprime_of_isMaximal (fun he => hij (Subtype.ext he))

theorem poolPrimary_good (F : Finset (Ideal O)) (hF : ∀ I ∈ F, quadraticIdealAdmissible I) (i : primePool F) :
    lambda ∉ Ideal.span {poolPrimary F i} := by rw [poolPrimary_span F hF i]; exact poolGood F hF i

theorem poolPrimary_odd (F : Finset (Ideal O)) (hF : ∀ I ∈ F, quadraticIdealAdmissible I) (i : primePool F) :
    ringChar (O ⧸ Ideal.span {poolPrimary F i}) ≠ 2 := by rw [poolPrimary_span F hF i]; exact poolOdd F hF i
theorem poolPrimary_norm (F : Finset (Ideal O)) (hF : ∀ I ∈ F, quadraticIdealAdmissible I)
    (S : Finset (primePool F)) :
    primeProductNorm (poolPrimary F) S = (Ideal.absNorm (∏ i ∈ S,i.val) : ℝ) := by
  rw [primeProductNorm, ringComplex_norm_sq_eq_absNorm_span, span_finset_prime_product]
  congr 2
  apply Finset.prod_congr rfl
  intro i hi
  exact poolPrimary_span F hF i


end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic UniqueFactorizationMonoid
open scoped Classical

lemma pool_product_factors (F : Finset (Ideal O)) (S : Finset (primePool F)) :
    normalizedFactors (∏i∈S,i.val)=S.val.map Subtype.val := by
  change normalizedFactors ((S.val.map Subtype.val).prod)=_
  apply normalizedFactors_prod_of_prime
  intro P hP
  obtain ⟨i,hi,rfl⟩:=Multiset.mem_map.mp hP
  exact Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance

lemma pool_support_product (F : Finset (Ideal O)) (S : Finset (primePool F)) :
    idealSupport F (∏i∈S,i.val)=S := by
  ext i
  rw [mem_idealSupport_iff,pool_product_factors]
  constructor
  · intro hi
    obtain ⟨j,hj,he⟩:=Multiset.mem_map.mp hi
    exact Subtype.val_injective he ▸ hj
  · intro hi
    exact Multiset.mem_map.mpr ⟨i,hi,rfl⟩

lemma pool_product_injective (F : Finset (Ideal O)) :
    Function.Injective (fun S:Finset (primePool F)=>∏i∈S,i.val) := by
  intro S T h
  have he:=congrArg (idealSupport F) h
  simpa only [pool_support_product] using he

theorem poolProduct_admissible (F : Finset (Ideal O)) (hF : ∀I∈F,quadraticIdealAdmissible I)
    (S : Finset (primePool F)) : quadraticIdealAdmissible (∏i∈S,i.val) := by
  have hp (i:primePool F) : Prime i.val:=Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
  have hn : (∏i∈S,i.val)≠(0:Ideal O):=Finset.prod_ne_zero_iff.mpr (fun i _=>(hp i).ne_zero)
  have hg : ∀P∈normalizedFactors (∏i∈S,i.val),lambda∉P ∧ ringChar (O⧸P)≠2 := by
    intro P hP
    rw [pool_product_factors] at hP
    obtain ⟨i,hi,rfl⟩:=Multiset.mem_map.mp hP
    exact ⟨poolGood F hF i,poolOdd F hF i⟩
  refine ⟨primaryIdealGenerator_ne_zero_of_good_factors _ hn (fun P hP=>(hg P hP).1),?_,?_⟩
  · apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i hi j hj hij
      exact (Ideal.isCoprime_of_isMaximal (fun he=>hij (Subtype.ext he))).isRelPrime
    · intro i hi
      exact (hp i).squarefree
  · intro P hP
    exact (hg P (Multiset.mem_toFinset.mp hP)).2

theorem sum_selected_ideals (F : Finset (Ideal O)) (hF : ∀I∈F,Squarefree I)
    (a : Ideal O→ℂ) :
    (∑I∈F,a I)=∑S∈(Finset.univ:Finset (primePool F)).powerset,
      if (∏i∈S,i.val)∈F then a (∏i∈S,i.val) else 0 := by
  rw [←Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun S _=>∏i∈S,i.val)
  · intro S hS
    exact (Finset.mem_filter.mp hS).2
  · intro S hS T hT he
    exact pool_product_injective F he
  · intro I hI
    refine ⟨idealSupport F I,?_,idealSupport_product_eq F hI (hF I hI)⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr (Finset.subset_univ _),?_⟩
    rwa [idealSupport_product_eq F hI (hF I hI)]
  · intro S hS
    rfl

def selectedIdealTest (F : Finset (Ideal O)) (W : ℕ→ℂ) (S : Finset (primePool F)) : ℂ :=
  if (∏i∈S,i.val)∈F then W (Ideal.absNorm (∏i∈S,i.val)) else 0

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss
open scoped Classical

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι→O) (hp : ∀i,p i≠0) [∀i,(Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i=>Ideal.span {p i})))
  (hg : ∀i,lambda∉Ideal.span {p i})

include hp hcop in
lemma squarefreeGaussCoefficient_finset (hpr : ∀i,lambda^2∣p i-1) (S : Finset ι) :
    squarefreeGaussCoefficient (Ideal.span {∏i∈S,p i})=secondColumnCoefficient p S := by
  have hs : Squarefree (Ideal.span {∏i∈S,p i}) := by
    rw [span_finset_prime_product]
    apply Finset.squarefree_prod_of_pairwise_isCoprime
    · intro i hi j hj hij
      exact (hcop hij).isRelPrime
    · intro i hi
      exact (Ideal.prime_of_isPrime (NeZero.ne (Ideal.span {p i})) inferInstance).squarefree
  have hn : (∏i∈S,p i)≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hprimary:=primary_finset_product S p (fun i _=>hpr i)
  rw [squarefreeGaussCoefficient,if_pos hs,primaryIdealGenerator_span _ hn hprimary]
  rfl

include hp hcop in
theorem columnWeight_finset (hpr : ∀i,lambda^2∣p i-1)
    (S : Finset ι) (Ψ : O →* ℂ) (m f z : O) (H : Finset ι → ℂ) :
    columnWeight (rowTwist Ψ m f z) (Ideal.span {∏i∈S,p i}) * H S =
      canonicalSourceCoefficient p hg Ψ m f H S *
        primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S z := by
  have hn : (∏i∈S,p i)≠0 := Finset.prod_ne_zero_iff.mpr (fun i _=>hp i)
  have hprimary : lambda^2∣(∏i∈S,p i)-1 := by
    have h := primary_finset_product S p (fun i _=>hpr i)
    exact h
  rw [columnWeight,squarefreeGaussCoefficient_finset p hp hcop hpr S,
    primaryIdealGenerator_span _ hn hprimary,rowTwist_product p hg S]
  simp only [canonicalSourceCoefficient]
  ring

end

theorem selected_column_sum (F : Finset (Ideal O))
    (hF : ∀I∈F,quadraticIdealAdmissible I)
    (Ψ : O →* ℂ) (m f z : O) (W : ℕ → ℂ) :
    let p := poolPrimary F
    let hp := poolPrimary_ne_zero F hF
    letI : ∀i:primePool F,(Ideal.span {p i}).IsMaximal :=
      fun i=>by rw [poolPrimary_span F hF i]; infer_instance
    let hcop := poolPrimary_coprime F hF
    let hg := poolPrimary_good F hF
    (∑I∈F,columnWeight (rowTwist Ψ m f z) I * W (Ideal.absNorm I)) =
      ∑S∈(Finset.univ:Finset (primePool F)).powerset,
        canonicalSourceCoefficient p hg Ψ m f (selectedIdealTest F W) S *
          primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) S z := by
  dsimp only
  let : ∀i:primePool F,
      (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i]; infer_instance
  rw [sum_selected_ideals F (fun I hI=>(hF I hI).2.1)]
  apply Finset.sum_congr rfl
  intro S hS
  have hspan : (Ideal.span {∏i∈S,poolPrimary F i}) = ∏i∈S,i.val := by
    rw [span_finset_prime_product]
    exact Finset.prod_congr rfl (fun i _=>poolPrimary_span F hF i)
  have hpr (i:primePool F) :
      lambda^2∣poolPrimary F i-1 :=
    (primaryIdealPrime_spec i.val (poolPrimary_ne_zero F hF i)).2.2.2
  have h := columnWeight_finset (poolPrimary F)
    (poolPrimary_ne_zero F hF)
    (poolPrimary_coprime F hF)
    (poolPrimary_good F hF) hpr S Ψ m f z
    (selectedIdealTest F W)
  rw [hspan] at h
  rw [←h]
  unfold selectedIdealTest
  split_ifs <;> simp

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic UniqueFactorizationMonoid
open scoped Classical

/-- Bounded nonzero ideals avoiding a fixed finite prime set. -/
def outsideIdealsUpTo (S : Finset (Ideal O)) (D : ℕ) : Finset (Ideal O) :=
  (Ideal.finite_setOf_absNorm_le (S := O) D).toFinset.filter
    (fun I=>1≤Ideal.absNorm I ∧ ∀P∈S,¬P∣I)

lemma mem_outsideIdealsUpTo {S : Finset (Ideal O)} {D : ℕ} {I : Ideal O} :
    I∈outsideIdealsUpTo S D ↔
      1≤Ideal.absNorm I ∧ Ideal.absNorm I≤D ∧ ∀P∈S,¬P∣I := by
  simp only [outsideIdealsUpTo,Finset.mem_filter,Set.Finite.mem_toFinset,Set.mem_setOf_eq]
  tauto

lemma outsideIdealsUpTo_ne_bot (S : Finset (Ideal O)) (D : ℕ)
    (I : Ideal O) (hI : I∈outsideIdealsUpTo S D) : I≠⊥ := by
  intro hz
  have hn:=(mem_outsideIdealsUpTo.mp hI).1
  have hn0 : Ideal.absNorm I=0 := Ideal.absNorm_eq_zero_iff.mpr hz
  omega

lemma outsideIdealsUpTo_norm_le (S : Finset (Ideal O)) (D : ℕ)
    (I : Ideal O) (hI : I∈outsideIdealsUpTo S D) : Ideal.absNorm I≤D :=
  (mem_outsideIdealsUpTo.mp hI).2.1

def fixedBadPrimes : Finset (Ideal O) := {ramifiedIdeal,cubicTwoIdeal}

lemma fixedBadPrimes_prime (P : Ideal O) (hP : P∈fixedBadPrimes) : Prime P := by
  rcases Finset.mem_insert.mp hP with rfl|hP
  · exact ramifiedIdeal_prime
  · rw [Finset.mem_singleton.mp hP]
    exact quadratic_twoIdeal_prime

lemma outside_supported (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes⊆S)
    (I : Ideal O) (hI : I∈outsideIdealsUpTo S D) : quadraticSupported I := by
  apply (quadraticSupported_iff_bad_not_dvd I).mpr
  have hh:=(mem_outsideIdealsUpTo.mp hI).2.2
  exact ⟨hh _ (hbad (Finset.mem_insert_self _ _)),
    hh _ (hbad (Finset.mem_insert_of_mem (Finset.mem_singleton_self _)))⟩

def outsideSquarefreeIdeals (S : Finset (Ideal O)) (D : ℕ) : Finset (Ideal O) :=
  (outsideIdealsUpTo S D).filter Squarefree

theorem outsideSquarefree_admissible (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes⊆S) : ∀I∈outsideSquarefreeIdeals S D,quadraticIdealAdmissible I := by
  intro I hI
  obtain ⟨ho,hs⟩:=Finset.mem_filter.mp hI
  have h:=outside_supported S D hbad I ho
  exact ⟨h.1,hs,h.2⟩

theorem outside_factors_mem_pool (S : Finset (Ideal O)) (D : ℕ)
    {I : Ideal O} (hI : I∈outsideIdealsUpTo S D) :
    ∀P∈normalizedFactors I,P∈primePool (outsideSquarefreeIdeals S D) := by
  intro P hP
  have hp:=prime_of_normalized_factor P hP
  have hd:P∣I:=dvd_of_mem_normalizedFactors hP
  have hi:=mem_outsideIdealsUpTo.mp hI
  have hPI:Ideal.absNorm P≤Ideal.absNorm I:=Nat.le_of_dvd (by omega) (map_dvd Ideal.absNorm hd)
  have ho:P∈outsideIdealsUpTo S D:=mem_outsideIdealsUpTo.mpr
    ⟨Nat.one_le_iff_ne_zero.mpr (Ideal.absNorm_eq_zero_iff.not.mpr hp.ne_zero),hPI.trans hi.2.1,
      fun Q hQ hQP=>hi.2.2 Q hQ (hQP.trans hd)⟩
  apply mem_primePool_iff.mpr
  refine ⟨P,Finset.mem_filter.mpr ⟨ho,hp.squarefree⟩,?_⟩
  rw [normalizedFactors_irreducible hp.irreducible,normalize_eq]
  exact Multiset.mem_singleton_self _

theorem outside_pool_product_not_dvd (S : Finset (Ideal O)) (D : ℕ)
    (hSp : ∀ P ∈ S, Prime P) (T : Finset (primePool (outsideSquarefreeIdeals S D))) :
    ∀ P ∈ S, ¬ P ∣ ∏ i ∈ T,i.val := by
  intro P hPS hdiv
  obtain ⟨i,hi,hPi⟩ := ((hSp P hPS).dvd_finsetProd_iff
    (fun i : primePool (outsideSquarefreeIdeals S D) => i.val)).mp hdiv
  obtain ⟨I,hIF,hiI⟩ := mem_primePool_iff.mp i.property
  have ho : I ∈ outsideIdealsUpTo S D := (Finset.mem_filter.mp hIF).1
  have hn := outsideIdealsUpTo_ne_bot S D I ho
  have hd : i.val ∣ I := (UniqueFactorizationMonoid.mem_normalizedFactors_iff hn).mp hiI |>.2
  exact (mem_outsideIdealsUpTo.mp ho).2.2 P hPS (hPi.trans hd)

theorem selectedIdealTest_outside (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀ P ∈ S, Prime P)
    (W : ℝ → ℂ) (b Z : ℝ) (hZ : 0 < Z)
    (hs : ∀ t, W t ≠ 0 → t ≤ b) (hD : b*Z ≤ D)
    (T : Finset (primePool (outsideSquarefreeIdeals S D))) :
    selectedIdealTest (outsideSquarefreeIdeals S D) (fun n => W (n/Z)) T =
    W (primeProductNorm (poolPrimary (outsideSquarefreeIdeals S D)) T/Z) := by
  let F := outsideSquarefreeIdeals S D
  have hF := outsideSquarefree_admissible S D hbad
  rw [poolPrimary_norm F hF T]
  unfold selectedIdealTest
  by_cases hw : W ((Ideal.absNorm (∏ i ∈ T,i.val) : ℝ)/Z)=0
  · split_ifs
    · rfl
    · exact hw.symm
  · apply if_pos
    have ha := poolProduct_admissible F hF T
    apply Finset.mem_filter.mpr
    refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,?_,outside_pool_product_not_dvd S D hSp T⟩,ha.2.1⟩
    · exact Nat.one_le_iff_ne_zero.mpr (fun hz => ha.2.1.ne_zero (Ideal.absNorm_eq_zero_iff.mp hz))
    · exact_mod_cast ((div_le_iff₀ hZ).mp (hs _ hw)).trans hD


end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open scoped Classical
theorem columnWeight_zero_of_mask (Ψ : O →* ℂ) (m f z : O) {P I : Ideal O}
    (hP : Prime P) (hPI : P∣I) (hm : m∈P) :
    columnWeight (rowTwist Ψ m f z) I = 0 := by
  unfold columnWeight
  have hx : m^6*f^4*z∈P := by
    have hm6 : m^6∈P := by
      rw [show m^6=m^5*m by ring]
      exact P.mul_mem_left (m^5) hm
    exact P.mul_mem_right z (P.mul_mem_right (f^4) hm6)
  by_cases hg : primaryIdealGenerator I=0
  · rw [hg]
    change squarefreeGaussCoefficient I * (Ψ 0 * idealRowHom _ (Ideal.span {0})) = 0
    rw [Ideal.span_singleton_zero]
    change squarefreeGaussCoefficient I * (Ψ 0 * idealRowHom _ (0:Ideal O)) = 0
    rw [map_zero (idealRowHom _),mul_zero,mul_zero]
  · change squarefreeGaussCoefficient I *
      (Ψ (primaryIdealGenerator I) * idealRowHom _ (Ideal.span {primaryIdealGenerator I})) = 0
    rw [(primaryIdealGenerator_spec I hg).1,idealRowHom_zero_of_dvd _ hP hPI hx,mul_zero,mul_zero]

theorem columnWeight_zero_of_not_squarefree (Ψ : O →* ℂ) {I : Ideal O}
    (hI : ¬Squarefree I) : columnWeight Ψ I = 0 := by
  simp [columnWeight,squarefreeGaussCoefficient,hI]

theorem weighted_column_support (S : Finset (Ideal O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P) (Ψ : O →* ℂ) (m f z : O) (hm : ∀P∈S,m∈P)
    (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t ≤ b) (hD : b*X ≤ D)
    {I : Ideal O}
    (hn : columnWeight (rowTwist Ψ m f z) I * W ((Ideal.absNorm I:ℝ)/X) ≠ 0) :
    I∈outsideSquarefreeIdeals S D := by
  have hc : columnWeight (rowTwist Ψ m f z) I ≠ 0 :=
    fun h=>hn (by rw [h,zero_mul])
  have hwindow : W ((Ideal.absNorm I:ℝ)/X) ≠ 0 :=
    fun h=>hn (by rw [h,mul_zero])
  have hI : I≠0 := fun h=>hc (by rw [h,columnWeight_zero])
  have hsf : Squarefree I := by
    by_contra h
    exact hc (columnWeight_zero_of_not_squarefree _ h)
  apply Finset.mem_filter.mpr
  refine ⟨mem_outsideIdealsUpTo.mpr ⟨?_,?_,?_⟩,hsf⟩
  · exact Nat.one_le_iff_ne_zero.mpr (fun h=>hI (Ideal.absNorm_eq_zero_iff.mp h))
  · exact_mod_cast ((div_le_iff₀ hX).mp (hW _ hwindow)).trans hD
  · intro P hP hPI
    exact hc (columnWeight_zero_of_mask Ψ m f z (hSp P hP) hPI (hm P hP))

theorem weighted_column_tsum_eq (S : Finset (Ideal O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P) (Ψ : O →* ℂ) (m f z : O) (hm : ∀P∈S,m∈P)
    (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t ≤ b) (hD : b*X ≤ D) :
    (∑'I:Ideal O,columnWeight (rowTwist Ψ m f z) I * W ((Ideal.absNorm I:ℝ)/X)) =
      ∑I∈outsideSquarefreeIdeals S D,
        columnWeight (rowTwist Ψ m f z) I * W ((Ideal.absNorm I:ℝ)/X) := by
  apply tsum_eq_sum
  intro I hI
  by_contra hn
  exact hI (weighted_column_support S D hSp Ψ m f z hm W b X hX hW hD hn)

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open scoped Classical
theorem cubeWeight_row_factor (Ψ : O →* ℂ) (m f z : O) (B : Ideal O) :
    cubeWeight (rowTwist Ψ m f z) B =
      cubeWeight (rowTwist Ψ m f 1) B * idealRowHom z B^3 := by
  by_cases hB : primaryIdealGenerator B=0
  · have hzero (x:O) : rowTwist Ψ m f x (primaryIdealGenerator B) = 0 := by
      rw [hB]
      change Ψ 0 * idealRowHom _ (Ideal.span {(0:O)}) = 0
      rw [Ideal.span_singleton_zero]
      change Ψ 0 * idealRowHom _ (0:Ideal O) = 0
      rw [map_zero (idealRowHom _),mul_zero]
    change _ * rowTwist Ψ m f z (primaryIdealGenerator B)^3 / _ =
      (_ * rowTwist Ψ m f 1 (primaryIdealGenerator B)^3 / _) * _
    rw [hzero z,hzero 1]
    simp
  · change _ * rowTwist Ψ m f z (primaryIdealGenerator B)^3 / _ =
      (_ * rowTwist Ψ m f 1 (primaryIdealGenerator B)^3 / _) * _
    rw [rowTwist_row_factor,(primaryIdealGenerator_spec B hB).1,mul_pow]
    ring

theorem idealRowHom_prime_powers {ι : Type*} (p : ι → O)
    [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i}) (pool : Finset ι)
    (v : ι → ℕ) (z : O) :
    idealRowHom z (∏i∈pool,(Ideal.span {p i})^v i) = multiplicityRow p hg pool v z := by
  rw [map_prod]
  simp only [map_pow,multiplicityRow]
  apply Finset.prod_congr rfl
  intro i hi
  rw [idealRowHom_prime z (Ideal.span {p i}) (hg i)]

theorem cubeWeight_prime_powers {ι : Type*} (p : ι → O)
    [∀i,(Ideal.span {p i}).IsMaximal] (hg : ∀i,lambda∉Ideal.span {p i}) (pool : Finset ι)
    (v : ι → ℕ) (Ψ : O →* ℂ) (m f z : O) :
    cubeWeight (rowTwist Ψ m f z) (∏i∈pool,(Ideal.span {p i})^v i) =
      cubeWeight (rowTwist Ψ m f 1) (∏i∈pool,(Ideal.span {p i})^v i) *
        multiplicityRow p hg pool v z^3 := by
  rw [cubeWeight_row_factor,idealRowHom_prime_powers p hg pool v z]

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open scoped Classical
def excludedGenerator (S : Finset (Ideal O)) : O := cubicIdealGenerator (∏P∈S,P)

theorem excludedGenerator_mem (S : Finset (Ideal O)) {P : Ideal O} (hP : P∈S) :
    excludedGenerator S∈P := by
  have hdiv : P∣∏Q∈S,Q := Finset.dvd_prod_of_mem (fun Q:Ideal O=>Q) hP
  have hm : cubicIdealGenerator (∏Q∈S,Q)∈Ideal.span {cubicIdealGenerator (∏Q∈S,Q)} :=
    Ideal.subset_span (by simp)
  rw [span_cubicIdealGenerator] at hm
  exact (Ideal.dvd_iff_le.mp hdiv) hm

theorem excludedGenerator_not_mem_pool (S : Finset (Ideal O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P)
    (i : primePool (outsideSquarefreeIdeals S D)) :
    excludedGenerator S∉i.val := by
  intro hm
  have hprime : Prime i.val := Ideal.prime_of_isPrime (NeZero.ne i.val) inferInstance
  have hspan : Ideal.span {excludedGenerator S}  ≤  i.val :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hm)
  change Ideal.span {cubicIdealGenerator (∏Q∈S,Q)}  ≤  i.val at hspan
  rw [span_cubicIdealGenerator] at hspan
  have hdiv : i.val∣∏Q∈S,Q := Ideal.dvd_iff_le.mpr hspan
  obtain ⟨P,hPS,hPi⟩ := (hprime.dvd_finsetProd_iff (fun Q:Ideal O=>Q)).mp hdiv
  have heq : i.val=P := (prime_dvd_prime_iff_eq hprime (hSp P hPS)).mp hPi
  obtain ⟨I,hI,hfactor⟩ := mem_primePool_iff.mp i.property
  have ho : I∈outsideIdealsUpTo S D := (Finset.mem_filter.mp hI).1
  have hd : i.val∣I := UniqueFactorizationMonoid.dvd_of_mem_normalizedFactors hfactor
  exact (mem_outsideIdealsUpTo.mp ho).2.2 P hPS (heq ▸ hd)

theorem outside_pool_fixed_mask (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes⊆S) (hSp : ∀P∈S,Prime P)
    (T : Finset (primePool (outsideSquarefreeIdeals S D))) :
    primeCoprimeMask (poolPrimary (outsideSquarefreeIdeals S D)) T (excludedGenerator S)=1 := by
  unfold primeCoprimeMask
  apply Finset.prod_eq_one
  intro i hi
  have hn : ¬poolPrimary (outsideSquarefreeIdeals S D) i ∣ excludedGenerator S := by
    intro hd
    apply excludedGenerator_not_mem_pool S D hSp i
    rw [←poolPrimary_span _ (outsideSquarefree_admissible S D hbad) i]
    exact Ideal.mem_span_singleton.mpr hd
  rw [if_neg hn,sub_zero]


theorem canonicalSourceCoefficient_fixed_mask {ι : Type*} [DecidableEq ι]
    (p : ι → O) [∀i,(Ideal.span {p i}).IsMaximal]
    (hg : ∀i,lambda∉Ideal.span {p i}) (Ψ : O →* ℂ) (m c f : O)
    (H : Finset ι → ℂ) (T : Finset ι)
    (hc : primeCoprimeMask p T c=1) :
    canonicalSourceCoefficient p hg Ψ (m*c) f H T =
      canonicalSourceCoefficient p hg Ψ m f H T := by
  simp only [canonicalSourceCoefficient,FirstPassCubeLabels.mask_mul p hg,hc,mul_one]

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open scoped Classical
def outsideCanonicalRow (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ → ℂ) (X : ℝ) : ℂ :=
  let F := outsideSquarefreeIdeals S D
  let hF := outsideSquarefree_admissible S D hbad
  letI : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i]; infer_instance
  fixedChildRow (poolPrimary F)
    (poolPrimary_good F hF) Finset.univ Ψ m
    (fun T=>W (primeProductNorm (poolPrimary F) T/X)) f z

theorem outsideCanonicalRow_eq_global (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t ≤ b) (hD : b*X  ≤  D) :
    outsideCanonicalRow S D hbad Ψ m f z W X =
      ∑'I:Ideal O,columnWeight (rowTwist Ψ (m*excludedGenerator S) f z) I *
        W ((Ideal.absNorm I:ℝ)/X) := by
  let F := outsideSquarefreeIdeals S D
  have hF := outsideSquarefree_admissible S D hbad
  let : ∀i:primePool F,(Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i=>by rw [poolPrimary_span F hF i]; infer_instance
  symm
  rw [weighted_column_tsum_eq S D hSp Ψ (m*excludedGenerator S) f z
    (fun P hP=>P.mul_mem_left m (excludedGenerator_mem S hP)) W b X hX hW hD]
  have he := selected_column_sum F hF Ψ (m*excludedGenerator S) f z (fun n=>W (n/X))
  dsimp only at he
  rw [he]
  unfold outsideCanonicalRow fixedChildRow
  dsimp only
  apply Finset.sum_congr rfl
  intro T hT
  rw [canonicalSourceCoefficient_fixed_mask _ _ Ψ m (excludedGenerator S) f _ T
    (outside_pool_fixed_mask S D hbad hSp T)]
  have ht := selectedIdealTest_outside S D hbad hSp W b X hX hW hD T
  simp only [canonicalSourceCoefficient,secondChildColumn]
  rw [ht]
  ring

theorem outsideCanonicalRow_cube_inverse (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (b X : ℝ) (hX : 0<X) (hW : ∀t,W t≠0 → t ≤ b) (hD : b*X  ≤  D) :
    (Real.sqrt X:ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      ∑'H:Ideal O,(UniqueFactorizationMonoid.moebius H:ℂ)*
        cubeWeight (rowTwist Ψ (m*excludedGenerator S) f z) H *
        completedIdealT (rowTwist Ψ (m*excludedGenerator S) f z) W
          (X/(Ideal.absNorm H:ℝ)^3) := by
  rw [outsideCanonicalRow_eq_global S D hbad hSp Ψ m f z W b X hX hW hD]
  exact completed_cube_inverse _ W hWc X hX

theorem outsideCanonicalRow_cube_split (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hX : 0<X) (hW : ∀t,W t≠0 → t ≤ b) (hD : b*X  ≤  D) :
    (Real.sqrt X:ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀ +
      ∑'I:Ideal O,∑'B:Ideal O,largeCubeCoefficient H₀ B *
        CompletedGauss.summand (rowTwist Ψ (m*excludedGenerator S) f z) W X I B := by
  rw [outsideCanonicalRow_eq_global S D hbad hSp Ψ m f z W b X hX hW hD]
  exact completed_cube_inverse_split _ W hWc X H₀ hX

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open scoped Classical
def cubeIndex (F : Finset (Ideal O)) (B : Ideal O) : primePool F →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (fun i=>(UniqueFactorizationMonoid.normalizedFactors B).count i.val)

@[simp] theorem cubeIndex_apply (F : Finset (Ideal O)) (B : Ideal O) (i : primePool F) :
    cubeIndex F B i = (UniqueFactorizationMonoid.normalizedFactors B).count i.val := by
  simp [cubeIndex]

def cubeIdeal (F : Finset (Ideal O)) (v : primePool F →₀ ℕ) : Ideal O :=
  ∏i:primePool F,i.val^v i

theorem cubeIdeal_cubeIndex (F : Finset (Ideal O)) (B : Ideal O) (hB : B≠0)
    (hcover : ∀P∈UniqueFactorizationMonoid.normalizedFactors B,P∈primePool F) :
    cubeIdeal F (cubeIndex F B) = B := by
  have hsub : (UniqueFactorizationMonoid.normalizedFactors B).toFinset ⊆ primePool F := by
    intro P hP
    exact hcover P (Multiset.mem_toFinset.mp hP)
  calc
    _ = ∏P∈primePool F,P^(UniqueFactorizationMonoid.normalizedFactors B).count P := by
      simp only [cubeIdeal,cubeIndex_apply]
      exact Finset.prod_coe_sort (s := primePool F)
        (f := fun P:Ideal O=>P^(UniqueFactorizationMonoid.normalizedFactors B).count P)
    _ = (UniqueFactorizationMonoid.normalizedFactors B).prod :=
      (Finset.prod_multiset_count_of_subset _ _ hsub).symm
    _ = B := Ideal.prod_normalizedFactors_eq_self hB

theorem cubeIndex_inj (F : Finset (Ideal O)) (B C : Ideal O) (hB : B≠0) (hC : C≠0)
    (hb : ∀P∈UniqueFactorizationMonoid.normalizedFactors B,P∈primePool F)
    (hc : ∀P∈UniqueFactorizationMonoid.normalizedFactors C,P∈primePool F)
    (heq : cubeIndex F B = cubeIndex F C) : B=C := by
  have he := congrArg (cubeIdeal F) heq
  rwa [cubeIdeal_cubeIndex F B hB hb,cubeIdeal_cubeIndex F C hC hc] at he

theorem outside_cubeIdeal_cubeIndex (S : Finset (Ideal O)) (D : ℕ)
    {B : Ideal O} (hB : B∈outsideIdealsUpTo S D) :
    cubeIdeal (outsideSquarefreeIdeals S D)
      (cubeIndex (outsideSquarefreeIdeals S D) B) = B := by
  exact cubeIdeal_cubeIndex _ B (outsideIdealsUpTo_ne_bot S D B hB)
    (outside_factors_mem_pool S D hB)

theorem sum_outside_cubeIndex (S : Finset (Ideal O)) (D : ℕ) (a : Ideal O → ℂ) :
    (∑B∈outsideIdealsUpTo S D,a B) =
      ∑v∈(outsideIdealsUpTo S D).image (cubeIndex (outsideSquarefreeIdeals S D)),
        a (cubeIdeal (outsideSquarefreeIdeals S D) v) := by
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro B hB
    rw [outside_cubeIdeal_cubeIndex S D hB]
  · intro B hB C hC he
    exact cubeIndex_inj _ B C (outsideIdealsUpTo_ne_bot S D B hB)
      (outsideIdealsUpTo_ne_bot S D C hC)
      (outside_factors_mem_pool S D hB)
      (outside_factors_mem_pool S D hC) he

theorem cubeIdeal_ne_zero (F : Finset (Ideal O)) (v : primePool F →₀ ℕ) :
    cubeIdeal F v ≠ 0 := by
  unfold cubeIdeal
  exact Finset.prod_ne_zero_iff.mpr (fun i _=>pow_ne_zero _ (NeZero.ne i.val))

theorem cubeIdeal_primaryIdealGenerator (F : Finset (Ideal O))
    (v : primePool F →₀ ℕ) :
    primaryIdealGenerator (cubeIdeal F v) =
      FirstPassCubeLabels.primeProduct (poolPrimary F) Finset.univ v := by
  change primaryIdealGeneratorHom (∏i:primePool F,i.val^v i) = _
  rw [map_prod]
  simp only [map_pow]
  unfold FirstPassCubeLabels.primeProduct
  apply Finset.prod_congr rfl
  intro i hi
  change primaryIdealGenerator i.val^v i = poolPrimary F i^v i
  rw [←primaryIdealPrime_eq_primaryIdealGenerator i.val]
  rfl

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open scoped Classical
theorem rowTwist_primary_zero_of_mask (Ψ : O →* ℂ) (m f z : O) {P B : Ideal O}
    (hP : Prime P) (hPB : P∣B) (hm : m∈P) :
    rowTwist Ψ m f z (primaryIdealGenerator B) = 0 := by
  have hx : m^6*f^4*z∈P := by
    have hm6 : m^6∈P := by
      rw [show m^6=m^5*m by ring]
      exact P.mul_mem_left (m^5) hm
    exact P.mul_mem_right z (P.mul_mem_right (f^4) hm6)
  by_cases hg : primaryIdealGenerator B=0
  · rw [hg]
    change Ψ 0 * idealRowHom _ (Ideal.span {(0:O)}) = 0
    rw [Ideal.span_singleton_zero]
    change Ψ 0 * idealRowHom _ (0:Ideal O) = 0
    rw [map_zero (idealRowHom _),mul_zero]
  · change Ψ (primaryIdealGenerator B) * idealRowHom _ (Ideal.span {primaryIdealGenerator B}) = 0
    rw [(primaryIdealGenerator_spec B hg).1,idealRowHom_zero_of_dvd _ hP hPB hx,mul_zero]

theorem cubeWeight_zero_of_prime_mask (Ψ : O →* ℂ) (m f z : O) {P B : Ideal O}
    (hP : Prime P) (hPB : P∣B) (hm : m∈P) :
    cubeWeight (rowTwist Ψ m f z) B = 0 :=
by
  change star (angularFactor (primaryIdealGenerator B))^3 *
    rowTwist Ψ m f z (primaryIdealGenerator B)^3 / _ = 0
  rw [rowTwist_primary_zero_of_mask Ψ m f z hP hPB hm]
  simp only [zero_pow (by decide : (3:ℕ)≠0),mul_zero,zero_div]

theorem summand_cube_support (S : Finset (Ideal O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P) (Ψ : O →* ℂ) (m f z : O) (hm : ∀P∈S,m∈P)
    (W : ℝ → ℂ) (b X : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t ≤ b) (hD : b*X  ≤  D)
    (I B : Ideal O) (hn : CompletedGauss.summand (rowTwist Ψ m f z) W X I B≠0) :
    B∈outsideIdealsUpTo S D := by
  have hI : I≠0 := fun h=>hn (by rw [h,summand_zero_left])
  have hB : B≠0 := fun h=>hn (by rw [h,summand_zero_right])
  have hw : W ((Ideal.absNorm I:ℝ)*(Ideal.absNorm B:ℝ)^3/X)≠0 :=
    fun h=>hn (summand_zero_window _ W X I B h)
  have hsize := (div_le_iff₀ hX).mp (hW _ hw)
  have hb := (triple_scale_bounds (Ideal.absNorm I:ℝ) (Ideal.absNorm B:ℝ) 1
    (norm_at_least_one I hI) (norm_at_least_one B hB) (by norm_num)).2.1
  simp only [one_pow,mul_one] at hb
  apply mem_outsideIdealsUpTo.mpr
  refine ⟨?_,?_,?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (fun h=>hB (Ideal.absNorm_eq_zero_iff.mp h))
  · exact_mod_cast (hb.trans hsize).trans hD
  · intro P hP hPB
    have hz := cubeWeight_zero_of_prime_mask Ψ m f z (hSp P hP) hPB (hm P hP)
    exact hn (by simp only [CompletedGauss.summand,hz,mul_zero,zero_mul])

theorem large_cube_sum_comm (Ψ : O →* ℂ) (W : ℝ → ℂ)
    (hW : HasCompactSupport W) (X H₀ : ℝ) (hX : 0<X) :
    (∑'I:Ideal O,∑'B:Ideal O,largeCubeCoefficient H₀ B*CompletedGauss.summand Ψ W X I B) =
      ∑'B:Ideal O,∑'I:Ideal O,largeCubeCoefficient H₀ B*CompletedGauss.summand Ψ W X I B := by
  let a : Ideal O×Ideal O → ℂ := fun p=>largeCubeCoefficient H₀ p.2*CompletedGauss.summand Ψ W X p.1 p.2
  have hf : (Function.support a).Finite :=
    (completedIdealT_finite_support Ψ W hW X hX).subset (by
      intro p hp
      exact fun h=>hp (by simp only [a,h,mul_zero]))
  have hs : Summable a := summable_of_hasFiniteSupport hf
  let e := Equiv.prodComm (Ideal O) (Ideal O)
  have ht : Summable (fun p=>a (e p)) := e.summable_iff.mpr hs
  calc
    _ = ∑'p:Ideal O×Ideal O,a p := hs.tsum_prod.symm
    _ = ∑'p:Ideal O×Ideal O,a (e p) := (e.tsum_eq a).symm
    _ = _ := ht.tsum_prod

theorem large_cube_sum_finite (S : Finset (Ideal O)) (D : ℕ)
    (hSp : ∀P∈S,Prime P) (Ψ : O →* ℂ) (m f z : O) (hm : ∀P∈S,m∈P)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ : ℝ) (hX : 0<X)
    (hW : ∀t,W t≠0 → t ≤ b) (hD : b*X  ≤  D) :
    (∑'I:Ideal O,∑'B:Ideal O,largeCubeCoefficient H₀ B*CompletedGauss.summand (rowTwist Ψ m f z) W X I B) =
      ∑B∈outsideIdealsUpTo S D,largeCubeCoefficient H₀ B*
        ∑'I:Ideal O,CompletedGauss.summand (rowTwist Ψ m f z) W X I B := by
  rw [large_cube_sum_comm _ W hWc X H₀ hX]
  simp only [tsum_mul_left]
  apply tsum_eq_sum
  intro B hB
  have hz : ∀I:Ideal O,CompletedGauss.summand (rowTwist Ψ m f z) W X I B=0 := by
    intro I
    by_contra hn
    exact hB (summand_cube_support S D hSp Ψ m f z hm W b X hX hW hD I B hn)
  simp only [hz,tsum_zero,mul_zero]


theorem inner_completed_sum (Ψ : O →* ℂ) (W : ℝ → ℂ) (X : ℝ) (hX : 0<X)
    (B : Ideal O) (hB : B≠0) :
    (∑'I:Ideal O,CompletedGauss.summand Ψ W X I B) =
      (cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) *
        ∑'I:Ideal O,columnWeight Ψ I * W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3)) := by
  have hN : 0 < (Ideal.absNorm B:ℝ) := lt_of_lt_of_le zero_lt_one (norm_at_least_one B hB)
  have hY : 0 < X/(Ideal.absNorm B:ℝ)^3 := div_pos hX (pow_pos hN _)
  have ht (I:Ideal O) : CompletedGauss.summand Ψ W X I B =
      (cubeWeight Ψ B * (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) *
        (columnWeight Ψ I * W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))) := by
    have harg : (Ideal.absNorm I:ℝ)*(Ideal.absNorm B:ℝ)^3/X =
        (Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3) := by
      rw [div_div_eq_mul_div]
    have hn := vstar_source_normalization Ψ W (X/(Ideal.absNorm B:ℝ)^3) hY I
    calc
      _ = cubeWeight Ψ B * (columnWeight Ψ I/(Real.sqrt (Ideal.absNorm I:ℝ):ℂ) *
          Vstar W ((Ideal.absNorm I:ℝ)/(X/(Ideal.absNorm B:ℝ)^3))) := by
        rw [CompletedGauss.summand,harg]
        ring
      _ = _ := by rw [hn]; ring
  simp_rw [ht]
  exact tsum_mul_left

theorem outsideCanonicalRow_reopened (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hb : 0  ≤  b) (hX : 0<X)
    (hW : ∀t,W t≠0 → t ≤ b) (hD : b*X  ≤  D) :
    (Real.sqrt X:ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀ +
      ∑B∈outsideIdealsUpTo S D,
        (largeCubeCoefficient H₀ B * cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) B *
          (Real.sqrt (X/(Ideal.absNorm B:ℝ)^3):ℂ)⁻¹) * idealRowHom z B^3 *
          outsideCanonicalRow S D hbad Ψ m f z W (X/(Ideal.absNorm B:ℝ)^3) := by
  rw [outsideCanonicalRow_cube_split S D hbad hSp Ψ m f z W hWc b X H₀ hX hW hD]
  rw [large_cube_sum_finite S D hSp Ψ (m*excludedGenerator S) f z
    (fun P hP=>P.mul_mem_left m (excludedGenerator_mem S hP)) W hWc b X H₀ hX hW hD]
  congr 1
  apply Finset.sum_congr rfl
  intro B hB
  have hB0 : B≠0 := outsideIdealsUpTo_ne_bot S D B hB
  have hN := norm_at_least_one B hB0
  have hY : 0 < X/(Ideal.absNorm B:ℝ)^3 := by positivity
  have hYX : X/(Ideal.absNorm B:ℝ)^3  ≤  X :=
    div_le_self hX.le (one_le_pow₀ hN)
  have hDY : b*(X/(Ideal.absNorm B:ℝ)^3)  ≤  D :=
    (mul_le_mul_of_nonneg_left hYX hb).trans hD
  rw [inner_completed_sum _ W X hX B hB0]
  rw [←outsideCanonicalRow_eq_global S D hbad hSp Ψ m f z W b
    (X/(Ideal.absNorm B:ℝ)^3) hY hW hDY]
  rw [cubeWeight_row_factor]
  ring

theorem outsideCanonicalRow_reopened_exponents (S : Finset (Ideal O)) (D : ℕ)
    (hbad : fixedBadPrimes ⊆ S) (hSp : ∀P∈S,Prime P)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ → ℂ) (hWc : HasCompactSupport W)
    (b X H₀ : ℝ) (hb : 0  ≤  b) (hX : 0<X)
    (hW : ∀t,W t≠0 → t ≤ b) (hD : b*X  ≤  D) :
    let F := outsideSquarefreeIdeals S D
    (Real.sqrt X:ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀ +
      ∑v∈(outsideIdealsUpTo S D).image (cubeIndex F),
        (largeCubeCoefficient H₀ (cubeIdeal F v) *
          cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v) *
          (Real.sqrt (X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3):ℂ)⁻¹) *
          idealRowHom z (cubeIdeal F v)^3 *
          outsideCanonicalRow S D hbad Ψ m f z W (X/(Ideal.absNorm (cubeIdeal F v):ℝ)^3) := by
  dsimp only
  rw [outsideCanonicalRow_reopened S D hbad hSp Ψ m f z W hWc b X H₀ hb hX hW hD]
  rw [sum_outside_cubeIndex S D]
end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open CanonicalCubeSeparation JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff

section
variable {ι : Type*} [DecidableEq ι]
  (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
  (hcop : Pairwise (Function.onFun IsCoprime (fun i => Ideal.span {p i})))
  (hg : ∀ i, lambda ∉ Ideal.span {p i})

theorem fixedChildRow_coefficient_expansion
    (pool : Finset ι) (Ψ : O →* ℂ) (m f z : O) (H : Finset ι → ℂ) :
    fixedChildRow p hg pool Ψ m H f z =
      ∑ T ∈ pool.powerset,
        canonicalSourceCoefficient p hg Ψ m f (fun _ => 1) T *
          primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) T z * H T := by
  unfold fixedChildRow
  apply Finset.sum_congr rfl
  intro T hT
  simp only [secondChildColumn, canonicalSourceCoefficient]
  ring

theorem reopenedCanonicalRow_integrand
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (Ψ : O →* ℂ) (m f z : O) (H : Finset ι → ℂ) :
    reopenedCanonicalRow p hg pool Q β Ψ m f H z =
      ∑ v ∈ Q, ∑ T ∈ pool.powerset,
        β v * (multiplicityRow p hg pool v z ^ 3 *
          canonicalSourceCoefficient p hg Ψ m f (fun _ => 1) T *
          primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) T z) * H T := by
  unfold reopenedCanonicalRow
  apply Finset.sum_congr rfl
  intro v hv
  apply Finset.sum_congr rfl
  intro T hT
  simp only [canonicalSourceCoefficient]
  ring

include hp in
theorem canonical_bin_separation
    (W : ℝ → ℂ) (a b : ℝ) (ha : 0 < a)
    (hs : Function.support W ⊆ Set.Icc a b) (hW : ContDiff ℝ ∞ W)
    (V : 𝓢(ℝ,ℂ)) (hV : ∀ u, |u|  ≤  columnWindowRadius a b → V u = 1)
    (pool : Finset ι) (Q : Finset (ι →₀ ℕ)) (β : (ι →₀ ℕ) → ℂ)
    (n : (ι →₀ ℕ) → ℝ) (Ψ : O →* ℂ) (m f z : O) (B ell X : ℝ)
    (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : ∀ v ∈ Q, B  ≤  n v) (hn' : ∀ v ∈ Q, n v  ≤  Real.exp 1*B) :
    (∑ v ∈ Q, (β v * (n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹) *
      multiplicityRow p hg pool v z ^ 3 *
      fixedChildRow p hg pool Ψ m
        (fun T => W (primeProductNorm p T/(X/(n v)^3))) f z) =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          reopenedCanonicalRow p hg pool Q
            (separatedCubeCoefficient β n B ξ) Ψ m f
            (fun T => frequencyTwist V ξ (columnLog p ell T)) z := by
  let A : (ι →₀ ℕ) → Finset ι → ℂ := fun v T =>
    multiplicityRow p hg pool v z ^ 3 *
      canonicalSourceCoefficient p hg Ψ m f (fun _ => 1) T *
      primeSubsetRow p (fun i=>complexSexticChar (Ideal.span {p i}) (hg i)) T z
  have hsep := reopening_finite_sum W a b ha hs hW V hV Q pool.powerset β A n
    (primeProductNorm p) B ell X hB hell hX hn hn'
    (fun T _ => primeProductNorm_pos p hp T)
  calc
    _ = ∑ v ∈ Q, ∑ T ∈ pool.powerset, (β v * A v T) *
        ((n v : ℂ)⁻¹ * (Real.sqrt (X/(n v)^3) : ℂ)⁻¹ *
          W (primeProductNorm p T/(X/(n v)^3))) := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [fixedChildRow_coefficient_expansion p hg, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T hT
      dsimp only [A]
      ring
    _ = _ := by
      rw [hsep]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with ξ
      rw [reopenedCanonicalRow_integrand p hg]
      rfl

end
end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open CanonicalCubeSeparation JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
theorem cube_coefficient_restore (H₀ : ℝ) (Ψ : O →* ℂ) (I : Ideal O)
    (hI : I ≠ 0) :
    reopenedCubeCoefficient H₀ Ψ I * (Ideal.absNorm I : ℂ)⁻¹ =
      largeCubeCoefficient H₀ I * cubeWeight Ψ I := by
  have hN : (Ideal.absNorm I : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (lt_of_lt_of_le zero_lt_one (norm_at_least_one I hI)))
  unfold reopenedCubeCoefficient cubePhase
  field_simp

theorem cubeIdeal_row (F : Finset (Ideal O)) (hF : ∀ I ∈ F, quadraticIdealAdmissible I)
    (v : primePool F →₀ ℕ) (z : O) :
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    idealRowHom z (cubeIdeal F v) =
      multiplicityRow (poolPrimary F) (poolPrimary_good F hF)
        Finset.univ v z := by
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  have hprod : cubeIdeal F v = ∏ i : primePool F, (Ideal.span {poolPrimary F i}) ^ v i := by
    unfold cubeIdeal
    exact Finset.prod_congr rfl (fun i _ => by rw [poolPrimary_span F hF i])
  rw [hprod, idealRowHom_prime_powers]

def outsideCanonicalBin (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Q : Finset (primePool (outsideSquarefreeIdeals S D) →₀ ℕ))
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ → ℂ) (X H₀ : ℝ) : ℂ :=
  let F := outsideSquarefreeIdeals S D
  ∑ v ∈ Q,
    (largeCubeCoefficient H₀ (cubeIdeal F v) *
      cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v) *
      (Real.sqrt (X/(Ideal.absNorm (cubeIdeal F v) : ℝ)^3) : ℂ)⁻¹) *
      idealRowHom z (cubeIdeal F v)^3 *
      outsideCanonicalRow S D hbad Ψ m f z W (X/(Ideal.absNorm (cubeIdeal F v) : ℝ)^3)

theorem outsideCanonicalBin_separated
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Q : Finset (primePool (outsideSquarefreeIdeals S D) →₀ ℕ))
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ → ℂ)
    (a b : ℝ) (ha : 0 < a) (hs : Function.support W ⊆ Set.Icc a b)
    (hW : ContDiff ℝ ∞ W) (V : 𝓢(ℝ,ℂ))
    (hV : ∀ u, |u|  ≤  columnWindowRadius a b → V u = 1)
    (B ell X H₀ : ℝ) (hB : 0 < B) (hell : 0 < ell) (hX : X = B^3*ell)
    (hn : ∀ v ∈ Q, B  ≤  (Ideal.absNorm (cubeIdeal (outsideSquarefreeIdeals S D) v) : ℝ))
    (hn' : ∀ v ∈ Q, (Ideal.absNorm (cubeIdeal (outsideSquarefreeIdeals S D) v) : ℝ)  ≤  Real.exp 1*B) :
    let F := outsideSquarefreeIdeals S D
    let hF := outsideSquarefree_admissible S D hbad
    letI : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
      fun i => by rw [poolPrimary_span F hF i]; infer_instance
    let β := fun v => reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)
    let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
    outsideCanonicalBin S D hbad Q Ψ m f z W X H₀ =
      ((B*Real.sqrt ell : ℝ) : ℂ)⁻¹ *
        ∫ ξ : ℝ, reopeningCoefficient W a b ha hs hW ξ *
          reopenedCanonicalRow (poolPrimary F) (poolPrimary_good F hF) Finset.univ Q
            (separatedCubeCoefficient β n B ξ) Ψ m f
            (fun T => frequencyTwist V ξ (columnLog (poolPrimary F) ell T)) z := by
  dsimp only
  let F := outsideSquarefreeIdeals S D
  have hF := outsideSquarefree_admissible S D hbad
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  let β := fun v => reopenedCubeCoefficient H₀ (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v)
  let n := fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)
  rw [← canonical_bin_separation (poolPrimary F) (poolPrimary_ne_zero F hF)
    (poolPrimary_good F hF) W a b ha hs hW V hV
    Finset.univ Q β n Ψ m f z B ell X hB hell hX hn hn']
  unfold outsideCanonicalBin
  dsimp only
  apply Finset.sum_congr rfl
  intro v hv
  rw [cubeIdeal_row F hF v z]
  have hc := cube_coefficient_restore H₀ (rowTwist Ψ (m*excludedGenerator S) f 1)
    (cubeIdeal F v) (cubeIdeal_ne_zero F v)
  change _ = (β v * (n v : ℂ)⁻¹ * _) * _ * _
  have hc' : β v * (n v : ℂ)⁻¹ =
      largeCubeCoefficient H₀ (cubeIdeal F v) *
        cubeWeight (rowTwist Ψ (m*excludedGenerator S) f 1) (cubeIdeal F v) := by
    simpa only [β,n,Complex.ofReal_natCast] using hc
  rw [hc']
  rfl

end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open CanonicalCubeSeparation JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
theorem fixedChildRow_zero_of_subunit {ι : Type*} [DecidableEq ι]
    (p : ι → O) (hp : ∀ i, p i ≠ 0) [∀ i, (Ideal.span {p i}).IsMaximal]
    (hg : ∀ i, lambda ∉ Ideal.span {p i})
    (pool : Finset ι) (Ψ : O →* ℂ) (m f z : O) (W : ℝ → ℂ)
    (b X : ℝ) (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t  ≤  b) (hsub : b*X < 1) :
    fixedChildRow p hg pool Ψ m
      (fun T => W (primeProductNorm p T/X)) f z = 0 := by
  unfold fixedChildRow
  apply Finset.sum_eq_zero
  intro T hT
  have hw : W (primeProductNorm p T/X) = 0 := by
    by_contra hne
    have hh := (div_le_iff₀ hX).mp (hW _ hne)
    have hone := primeProductNorm_ge_one p hp T
    linarith
  simp only [secondChildColumn,hw,mul_zero]

theorem outsideCanonicalRow_zero_of_subunit
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ → ℂ)
    (b X : ℝ) (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t  ≤  b) (hsub : b*X < 1) :
    outsideCanonicalRow S D hbad Ψ m f z W X = 0 := by
  let F := outsideSquarefreeIdeals S D
  have hF := outsideSquarefree_admissible S D hbad
  let : ∀ i : primePool F, (Ideal.span {poolPrimary F i}).IsMaximal :=
    fun i => by rw [poolPrimary_span F hF i]; infer_instance
  unfold outsideCanonicalRow
  dsimp only
  exact fixedChildRow_zero_of_subunit (poolPrimary F) (poolPrimary_ne_zero F hF) _ _ Ψ m f z W b X hX hW hsub

def activeCubeExponents (S : Finset (Ideal O)) (D : ℕ) (b X : ℝ) :
    Finset (primePool (outsideSquarefreeIdeals S D) →₀ ℕ) :=
  let F := outsideSquarefreeIdeals S D
  ((outsideIdealsUpTo S D).image (cubeIndex F)).filter
    (fun v => (Ideal.absNorm (cubeIdeal F v) : ℝ)^3  ≤  b*X)

theorem outsideCanonicalBin_eq_active
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ → ℂ) (b X H₀ : ℝ)
    (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t  ≤  b) :
    outsideCanonicalBin S D hbad
      ((outsideIdealsUpTo S D).image (cubeIndex (outsideSquarefreeIdeals S D)))
      Ψ m f z W X H₀ =
    outsideCanonicalBin S D hbad (activeCubeExponents S D b X) Ψ m f z W X H₀ := by
  unfold outsideCanonicalBin activeCubeExponents
  dsimp only
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro v hv hn
  have hlarge : b*X < (Ideal.absNorm (cubeIdeal (outsideSquarefreeIdeals S D) v) : ℝ)^3 := by
    exact lt_of_not_ge (fun hh => hn (Finset.mem_filter.mpr ⟨hv,hh⟩))
  have hN : 0 < (Ideal.absNorm (cubeIdeal (outsideSquarefreeIdeals S D) v) : ℝ) :=
    lt_of_lt_of_le zero_lt_one (norm_at_least_one _ (cubeIdeal_ne_zero _ v))
  have hsub : b*(X/(Ideal.absNorm (cubeIdeal (outsideSquarefreeIdeals S D) v) : ℝ)^3) < 1 := by
    rw [← mul_div_assoc]
    exact (div_lt_one (pow_pos hN _)).mpr hlarge
  rw [outsideCanonicalRow_zero_of_subunit S D hbad Ψ m f z W b _
    (div_pos hX (pow_pos hN _)) hW hsub,mul_zero]

theorem outsideCanonicalRow_reopened_active
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (Ψ : O →* ℂ) (m f z : O)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ : ℝ)
    (hb : 0  ≤  b) (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t  ≤  b) (hD : b*X  ≤  D) :
    (Real.sqrt X : ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀ +
        outsideCanonicalBin S D hbad (activeCubeExponents S D b X) Ψ m f z W X H₀ := by
  have hh := outsideCanonicalRow_reopened_exponents S D hbad hSp Ψ m f z W hWc b X H₀ hb hX hW hD
  change _ = _ + outsideCanonicalBin S D hbad
    ((outsideIdealsUpTo S D).image (cubeIndex (outsideSquarefreeIdeals S D)))
    Ψ m f z W X H₀ at hh
  rwa [outsideCanonicalBin_eq_active S D hbad Ψ m f z W b X H₀ hX hW] at hh

theorem activeCubeExponents_norm_bound
    (S : Finset (Ideal O)) (D : ℕ) (b X : ℝ)
    (v : primePool (outsideSquarefreeIdeals S D) →₀ ℕ)
    (hv : v ∈ activeCubeExponents S D b X) :
    (Ideal.absNorm (cubeIdeal (outsideSquarefreeIdeals S D) v) : ℝ)  ≤  max 1 (b*X) := by
  have hcube := (Finset.mem_filter.mp hv).2
  have hN := norm_at_least_one _ (cubeIdeal_ne_zero (outsideSquarefreeIdeals S D) v)
  let n := (Ideal.absNorm (cubeIdeal (outsideSquarefreeIdeals S D) v) : ℝ)
  have hone : 1  ≤  n := hN
  have hnn : n  ≤  n^3 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hone) (show 0  ≤  n^2+n by positivity)]
  exact (hnn.trans hcube).trans (le_max_right _ _)



def cubeLogIndex (S : Finset (Ideal O)) (D : ℕ)
    (v : primePool (outsideSquarefreeIdeals S D) →₀ ℕ) : ℕ :=
  normLogBin (Ideal.absNorm (cubeIdeal (outsideSquarefreeIdeals S D) v) : ℝ)

def cubeLogRange (b X : ℝ) : Finset ℕ :=
  Finset.range (normLogBin (max 1 (b*X)) + 1)

def activeCubeLogBin (S : Finset (Ideal O)) (D : ℕ) (b X : ℝ) (j : ℕ) :
    Finset (primePool (outsideSquarefreeIdeals S D) →₀ ℕ) :=
  (activeCubeExponents S D b X).filter (fun v => cubeLogIndex S D v = j)

theorem activeCubeLogIndex_mem (S : Finset (Ideal O)) (D : ℕ) (b X : ℝ)
    (v : primePool (outsideSquarefreeIdeals S D) →₀ ℕ)
    (hv : v ∈ activeCubeExponents S D b X) : cubeLogIndex S D v ∈ cubeLogRange b X := by
  apply Finset.mem_range.mpr
  apply Nat.lt_succ_of_le
  exact normLogBin_mono
    (lt_of_lt_of_le zero_lt_one (norm_at_least_one _ (cubeIdeal_ne_zero _ v)))
    (activeCubeExponents_norm_bound S D b X v hv)

theorem activeCubeLogBin_norms (S : Finset (Ideal O)) (D : ℕ) (b X : ℝ) (j : ℕ)
    (v : primePool (outsideSquarefreeIdeals S D) →₀ ℕ)
    (hv : v ∈ activeCubeLogBin S D b X j) :
    normLogScale j  ≤  (Ideal.absNorm (cubeIdeal (outsideSquarefreeIdeals S D) v) : ℝ) ∧
    (Ideal.absNorm (cubeIdeal (outsideSquarefreeIdeals S D) v) : ℝ)  ≤  Real.exp 1*normLogScale j := by
  have hj := (Finset.mem_filter.mp hv).2
  rw [← hj]
  have hh := normLogBin_scale_bounds
    (Ideal.absNorm (cubeIdeal (outsideSquarefreeIdeals S D) v) : ℝ)
    (norm_at_least_one _ (cubeIdeal_ne_zero _ v))
  exact ⟨hh.1,by simpa only [mul_comm,cubeLogIndex] using hh.2⟩

theorem cubeLogRange_card (b X : ℝ) :
    (cubeLogRange b X).card = normLogBin (max 1 (b*X)) + 1 := by
  exact Finset.card_range _

theorem sum_activeCubeLogBins {M : Type*} [AddCommMonoid M]
    (S : Finset (Ideal O)) (D : ℕ) (b X : ℝ)
    (a : (primePool (outsideSquarefreeIdeals S D) →₀ ℕ) → M) :
    (∑ v ∈ activeCubeExponents S D b X, a v) =
      ∑ j ∈ cubeLogRange b X, ∑ v ∈ activeCubeLogBin S D b X j, a v := by
  symm
  exact Finset.sum_fiberwise_of_maps_to
    (fun v hv => activeCubeLogIndex_mem S D b X v hv) a

theorem outsideCanonicalBin_log_bins
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (Ψ : O →* ℂ) (m f z : O) (W : ℝ → ℂ) (b X H₀ : ℝ) :
    outsideCanonicalBin S D hbad (activeCubeExponents S D b X) Ψ m f z W X H₀ =
      ∑ j ∈ cubeLogRange b X,
        outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) Ψ m f z W X H₀ := by
  unfold outsideCanonicalBin
  dsimp only
  exact sum_activeCubeLogBins S D b X _

theorem outsideCanonicalRow_reopened_binned
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (Ψ : O →* ℂ) (m f z : O)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ : ℝ)
    (hb : 0  ≤  b) (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t  ≤  b) (hD : b*X  ≤  D) :
    (Real.sqrt X : ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X =
      shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀ +
        ∑ j ∈ cubeLogRange b X,
          outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) Ψ m f z W X H₀ := by
  rw [outsideCanonicalRow_reopened_active S D hbad hSp Ψ m f z W hWc b X H₀ hb hX hW hD,
    outsideCanonicalBin_log_bins]
end CanonicalRowCompletion

namespace CanonicalRowCompletion
open Eisenstein SchwartzPlanePoisson SecondPassArithmetic FirstPassCubeLabels CompletedGauss UniqueFactorizationMonoid
open CanonicalCubeSeparation JointLogSeparation MeasureTheory
open scoped BigOperators Classical SchwartzMap ContDiff
theorem outsideCanonicalRow_binned_energy
    (S : Finset (Ideal O)) (D : ℕ) (hbad : fixedBadPrimes ⊆ S)
    (hSp : ∀ P ∈ S, Prime P) (Ψ : O →* ℂ) (m f z : O)
    (W : ℝ → ℂ) (hWc : HasCompactSupport W) (b X H₀ : ℝ)
    (hb : 0  ≤  b) (hX : 0 < X) (hW : ∀ t, W t ≠ 0 → t  ≤  b) (hD : b*X  ≤  D) :
    ‖outsideCanonicalRow S D hbad Ψ m f z W X‖^2  ≤ 
      2*X*(‖shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀‖^2 +
        (cubeLogRange b X).card * ∑ j ∈ cubeLogRange b X,
          ‖outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) Ψ m f z W X H₀‖^2) := by
  have hs := norm_add_sum_sq_le (cubeLogRange b X)
    (shortCompletedSum (rowTwist Ψ (m*excludedGenerator S) f z) W X H₀)
    (fun j => outsideCanonicalBin S D hbad (activeCubeLogBin S D b X j) Ψ m f z W X H₀)
  rw [← outsideCanonicalRow_reopened_binned S D hbad hSp Ψ m f z W hWc b X H₀ hb hX hW hD] at hs
  have hn : ‖outsideCanonicalRow S D hbad Ψ m f z W X‖^2 =
      X*‖(Real.sqrt X : ℂ)⁻¹ * outsideCanonicalRow S D hbad Ψ m f z W X‖^2 := by
    rw [norm_mul,norm_inv,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (Real.sqrt_nonneg X),
      mul_pow,inv_pow,Real.sq_sqrt hX.le]
    field_simp
  rw [hn]
  simpa only [mul_assoc,mul_left_comm] using mul_le_mul_of_nonneg_left hs hX.le

end CanonicalRowCompletion

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
