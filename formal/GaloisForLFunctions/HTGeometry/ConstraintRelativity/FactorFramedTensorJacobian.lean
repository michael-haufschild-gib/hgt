import GaloisForLFunctions.HTGeometry.ConstraintRelativity.GorensteinMonogenic
import Mathlib.LinearAlgebra.Quotient.Pi
import Mathlib.Data.Finset.Max
import Mathlib.RingTheory.DiscreteValuationRing.Basic
import Mathlib.Tactic

/-!
# Factor-framed tensor Jacobian defect

Combinatorial Smith normal form of the factor-gradient cokernel.  Coordinates are indexed by
squarefree faces `T`; multiplication by the `i`th complementary monomial contributes the pure
coefficient `a^(2 * sum_{j ∉ T, j ≠ i} r_j)`.  This file identifies the generated coordinate ideal
with its least exponent and packages the resulting quotient as the exact product of cyclic bars.
-/

namespace HTGeometry.ConstraintRelativity

open scoped BigOperators
open IsLocalRing

abbrev TensorFace (d : ℕ) := Finset (Fin d)

def missingFace {d : ℕ} (T : TensorFace d) : Finset (Fin d) := Finset.univ \ T

/-- Valuation of the pure target coefficient contributed by factor `i` to face `T`. -/
def factorSourceExponent {d : ℕ} (r : Fin d → ℕ) (T : TensorFace d) (i : Fin d) : ℕ :=
  2 * ∑ j ∈ (missingFace T).erase i, r j

/-- Weighted excess-codimension depth from card `(19)`, with the empty missing face assigned zero. -/
noncomputable def weightedFaceDepth {d : ℕ} (r : Fin d → ℕ) (T : TensorFace d) : ℕ :=
  if hM : (missingFace T).Nonempty then
    2 * (∑ j ∈ missingFace T, r j - ((missingFace T).image r).max' (hM.image r))
  else 0

theorem exists_mem_factorSourceExponent_eq_weightedFaceDepth
    {d : ℕ} (r : Fin d → ℕ) (T : TensorFace d) (hM : (missingFace T).Nonempty) :
    ∃ i ∈ missingFace T, factorSourceExponent r T i = weightedFaceDepth r T := by
  classical
  have hmaxmem : ((missingFace T).image r).max' (hM.image r) ∈
      (missingFace T).image r := Finset.max'_mem _ _
  obtain ⟨i, hiM, hir⟩ := Finset.mem_image.mp hmaxmem
  refine ⟨i, hiM, ?_⟩
  simp only [factorSourceExponent, weightedFaceDepth, dif_pos hM]
  rw [← hir]
  have hsum : (∑ j ∈ (missingFace T).erase i, r j) + r i =
      ∑ j ∈ missingFace T, r j := Finset.sum_erase_add _ _ hiM
  omega

theorem exists_factorSourceExponent_eq_weightedFaceDepth
    {d : ℕ} [NeZero d] (r : Fin d → ℕ) (T : TensorFace d) :
    ∃ i : Fin d, factorSourceExponent r T i = weightedFaceDepth r T := by
  classical
  by_cases hM : (missingFace T).Nonempty
  · obtain ⟨i, _, hi⟩ := exists_mem_factorSourceExponent_eq_weightedFaceDepth r T hM
    exact ⟨i, hi⟩
  · have hEmpty : missingFace T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hM
    let i : Fin d := Classical.choice (inferInstance : Nonempty (Fin d))
    refine ⟨i, ?_⟩
    simp [factorSourceExponent, weightedFaceDepth, hM, hEmpty]

theorem weightedFaceDepth_le_factorSourceExponent
    {d : ℕ} [NeZero d] (r : Fin d → ℕ) (T : TensorFace d) (i : Fin d) :
    weightedFaceDepth r T ≤ factorSourceExponent r T i := by
  classical
  by_cases hM : (missingFace T).Nonempty
  · let m := ((missingFace T).image r).max' (hM.image r)
    have hm_mem : m ∈ (missingFace T).image r := Finset.max'_mem _ _
    obtain ⟨j, hjM, hjr⟩ := Finset.mem_image.mp hm_mem
    have hm_sum : m ≤ ∑ k ∈ missingFace T, r k := by
      rw [← hjr]
      exact Finset.single_le_sum (fun k _ => Nat.zero_le (r k)) hjM
    by_cases hiM : i ∈ missingFace T
    · have hri : r i ≤ m := by
        exact Finset.le_max' ((missingFace T).image r) (r i)
          (Finset.mem_image_of_mem r hiM)
      have hsumErase : (∑ k ∈ (missingFace T).erase i, r k) + r i =
          ∑ k ∈ missingFace T, r k := Finset.sum_erase_add _ _ hiM
      simp only [weightedFaceDepth, dif_pos hM, factorSourceExponent]
      change 2 * (∑ k ∈ missingFace T, r k - m) ≤
        2 * ∑ k ∈ (missingFace T).erase i, r k
      omega
    · have herase : (missingFace T).erase i = missingFace T := Finset.erase_eq_of_notMem hiM
      simp only [weightedFaceDepth, dif_pos hM, factorSourceExponent, herase]
      change 2 * (∑ k ∈ missingFace T, r k - m) ≤
        2 * ∑ k ∈ missingFace T, r k
      omega
  · simp [weightedFaceDepth, hM]

/-- Principal Smith bar attached to face `T`. -/
def faceBarIdeal {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (T : TensorFace d) : Submodule R R :=
  Ideal.span {a ^ weightedFaceDepth r T}

/-- Diagonal pure-basis image of the factor-gradient map. -/
def factorGradientImage {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) : Submodule R (TensorFace d → R) :=
  Submodule.pi Set.univ (faceBarIdeal a r)

/-- A source exponent generates an element of the Smith ideal of its target face. -/
theorem factorSourcePower_mem_faceBarIdeal
    {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    (a : R) (r : Fin d → ℕ) (T : TensorFace d) (i : Fin d) :
    a ^ factorSourceExponent r T i ∈ faceBarIdeal a r T := by
  rw [faceBarIdeal, Ideal.mem_span_singleton]
  exact pow_dvd_pow a (weightedFaceDepth_le_factorSourceExponent r T i)

/-- Pure target contribution of factor `i`.  The membership condition `i ∉ T` is the
squarefree-basis form of the source relation `f_i = 0` in `A/(f_i)`. -/
def factorGradientAtom {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) (T : TensorFace d) : TensorFace d → R :=
  if i ∈ missingFace T then Pi.single T (a ^ factorSourceExponent r T i) else 0

/-- The `F = 0` target relation.  Its only new pure generator is the full-face coordinate. -/
def factorFullFaceAtom {R : Type*} [CommRing R] {d : ℕ} : TensorFace d → R :=
  Pi.single Finset.univ 1

/-- Actual pure-basis image generated by factor gradients together with the target relation `F=0`. -/
def factorGradientPresentationImage {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) : Submodule R (TensorFace d → R) :=
  Submodule.span R
    ({factorFullFaceAtom} ∪ Set.range (fun p : Fin d × TensorFace d =>
      factorGradientAtom a r p.1 p.2))

/-- Pure-basis gradient calculation `(14)`--`(16)`/`(23)`--`(24)`: the image of the actual
factor generators and `F=0` relation is exactly the coordinatewise weighted Smith image. -/
theorem factorGradientPresentationImage_eq_factorGradientImage
    {R : Type*} [CommRing R] {d : ℕ} [NeZero d] (a : R) (r : Fin d → ℕ) :
    factorGradientPresentationImage a r = factorGradientImage a r := by
  classical
  apply le_antisymm
  · rw [factorGradientPresentationImage, Submodule.span_le]
    rintro x (hx | hx)
    · simp only [Set.mem_singleton_iff] at hx
      subst x
      change factorFullFaceAtom ∈ factorGradientImage a r
      rw [factorGradientImage, Submodule.mem_pi]
      intro T _
      by_cases hT : T = Finset.univ
      · subst T
        simp [factorFullFaceAtom, faceBarIdeal, weightedFaceDepth, missingFace]
      · simp [factorFullFaceAtom, Pi.single_apply, hT]
    · obtain ⟨⟨i, T⟩, rfl⟩ := hx
      change factorGradientAtom a r i T ∈ factorGradientImage a r
      rw [factorGradientImage, Submodule.mem_pi]
      intro U _
      by_cases hi : i ∈ missingFace T
      · by_cases hUT : U = T
        · subst U
          simpa [factorGradientAtom, hi] using factorSourcePower_mem_faceBarIdeal a r T i
        · simp [factorGradientAtom, hi, Pi.single_apply, hUT]
      · simp [factorGradientAtom, hi]
  · intro y hy
    rw [factorGradientImage, Submodule.mem_pi] at hy
    have hsingle : ∀ T : TensorFace d,
        Pi.single T (y T) ∈ factorGradientPresentationImage a r := by
      intro T
      have hyT : y T ∈ faceBarIdeal a r T := hy T (Set.mem_univ T)
      by_cases hM : (missingFace T).Nonempty
      · obtain ⟨i, hiM, hiDepth⟩ :=
          exists_mem_factorSourceExponent_eq_weightedFaceDepth r T hM
        rw [faceBarIdeal, Ideal.mem_span_singleton] at hyT
        obtain ⟨c, hc⟩ := hyT
        have hatom : factorGradientAtom a r i T ∈ factorGradientPresentationImage a r := by
          apply Submodule.subset_span
          exact Or.inr ⟨(i, T), rfl⟩
        have hsmul := (factorGradientPresentationImage a r).smul_mem c hatom
        rw [factorGradientAtom, if_pos hiM, hiDepth] at hsmul
        rw [hc]
        have heq : c • Pi.single T (a ^ weightedFaceDepth r T) =
            Pi.single T (a ^ weightedFaceDepth r T * c) := by
          ext U
          by_cases hUT : U = T <;> simp [Pi.single_apply, hUT, mul_comm]
        rw [← heq]
        exact hsmul
      · have hEmpty : missingFace T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hM
        have hsub : Finset.univ ⊆ T :=
          Finset.sdiff_eq_empty_iff_subset.mp (by simpa [missingFace] using hEmpty)
        have hT : T = Finset.univ :=
          Finset.Subset.antisymm (Finset.subset_univ T) hsub
        have hfull : factorFullFaceAtom ∈ factorGradientPresentationImage a r := by
          apply Submodule.subset_span
          exact Or.inl rfl
        have hsmul := (factorGradientPresentationImage a r).smul_mem (y T) hfull
        subst T
        have heq : y Finset.univ • (factorFullFaceAtom : TensorFace d → R) =
            (Pi.single Finset.univ (y Finset.univ) : TensorFace d → R) := by
          ext U
          by_cases hU : U = Finset.univ <;>
            simp [factorFullFaceAtom, Pi.single_apply, hU]
        rw [← heq]
        exact hsmul
    have hsum : ∑ T : TensorFace d, Pi.single T (y T) = y := by
      ext T
      simp
    rw [← hsum]
    exact Submodule.sum_mem _ fun T _ => hsingle T

/-- Exact factor-gradient cokernel in its pure squarefree-face basis. -/
abbrev FactorGradientCokernel {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :=
  (TensorFace d → R) ⧸ factorGradientImage a r

/-- **Card Theorem 2 `(20)`.** Exact heterogeneous Smith decomposition, including zero bars on
the full face and facets. -/
noncomputable def factorGradientCokernelEquivFaceBars
    {R : Type*} [CommRing R] {d : ℕ} (a : R) (r : Fin d → ℕ) :
    FactorGradientCokernel a r ≃ₗ[R]
      ∀ T : TensorFace d, R ⧸ faceBarIdeal a r T :=
  Submodule.quotientPi (faceBarIdeal a r)

/-! ## Exact finite-length source and target models -/

/-- Squarefree basis faces for the `i`th cotangent summand `A/(f_i)`. -/
abbrev FactorSourceFace (d : ℕ) (i : Fin d) := {T : TensorFace d // i ∉ T}

theorem factorSourceFace_card {d : ℕ} (i : Fin d) :
    Fintype.card (FactorSourceFace d i) = 2 ^ (d - 1) := by
  classical
  let e : FactorSourceFace d i ≃
      {T : TensorFace d // T ∈ (Finset.univ.erase i).powerset} :=
    Equiv.subtypeEquivRight fun T => by simp [Finset.subset_erase]
  rw [Fintype.card_congr e, Fintype.card_coe, Finset.card_powerset,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]

/-- Cyclic coefficient bar in the `i`th cotangent summand. -/
def factorSourceBarIdeal {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (i : Fin d) : Submodule R R :=
  Ideal.span {a ^ (2 * r i)}

/-- Pure-basis model of `⊕_i A/(f_i) df_i`, card `(5)` and heterogeneous `(22)`. -/
abbrev FactorCotangentModel {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :=
  ∀ i : Fin d, FactorSourceFace d i → R ⧸ factorSourceBarIdeal a r i

/-- Target bar exponent of `A/F A`: multiplication by `F` pairs a face with its complement. -/
def factorTraceTargetDepth {d : ℕ} (r : Fin d → ℕ) (T : TensorFace d) : ℕ :=
  2 * ∑ j ∈ missingFace T, r j

def factorTraceTargetIdeal {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) (T : TensorFace d) : Submodule R R :=
  Ideal.span {a ^ factorTraceTargetDepth r T}

/-- Pure-basis model of `A/F A ≅ A♯/A`, card `(4)`. -/
abbrev FactorTraceQuotientModel {R : Type*} [CommRing R] {d : ℕ}
    (a : R) (r : Fin d → ℕ) :=
  ∀ T : TensorFace d, R ⧸ factorTraceTargetIdeal a r T

/-- Double-counting identity: across all subsets, each vertex occurs exactly half the time. -/
theorem sum_powerset_sum_nat { α : Type* } [DecidableEq α]
    (s : Finset α) (f : α → ℕ) :
    (∑ T ∈ s.powerset, ∑ i ∈ T, f i) =
      2 ^ (s.card - 1) * ∑ i ∈ s, f i := by
  induction s using Finset.induction with
  | empty => simp
  | @insert a s ha ih =>
      rw [Finset.sum_powerset_insert ha, ih]
      have hsecond :
          (∑ T ∈ s.powerset, ∑ i ∈ insert a T, f i) =
            ∑ T ∈ s.powerset, (f a + ∑ i ∈ T, f i) := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [Finset.sum_insert (Finset.notMem_of_mem_powerset_of_notMem hT ha)]
      rw [hsecond, Finset.sum_add_distrib, ih, Finset.sum_const,
        Finset.card_powerset, Finset.card_insert_of_notMem ha, Finset.sum_insert ha]
      simp only [Nat.nsmul_eq_mul]
      by_cases hs : s = ∅
      · simp [hs]
      · have hpos : 0 < s.card := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hs)
        rw [show s.card + 1 - 1 = s.card by omega,
          show s.card = (s.card - 1) + 1 by omega, pow_succ]
        have hexp : s.card - 1 + 1 - 1 = s.card - 1 := by omega
        rw [hexp]
        ring

/-- Sum of target exponents in `A/F A`, the target half of heterogeneous card `(22)`. -/
theorem sum_factorTraceTargetDepth {d : ℕ} [NeZero d] (r : Fin d → ℕ) :
    (∑ T : TensorFace d, factorTraceTargetDepth r T) = 2 ^ d * ∑ j, r j := by
  have hd : 0 < d := Nat.pos_of_neZero d
  let e : TensorFace d ≃ TensorFace d :=
    { toFun := fun T => Finset.univ \ T
      invFun := fun T => Finset.univ \ T
      left_inv := by intro T; ext; simp
      right_inv := by intro T; ext; simp }
  calc
    (∑ T : TensorFace d, factorTraceTargetDepth r T) =
        2 * ∑ T : TensorFace d, ∑ j ∈ T, r j := by
      rw [Finset.mul_sum]
      have hperm := e.sum_comp (fun T : TensorFace d => ∑ j ∈ T, r j)
      simpa [factorTraceTargetDepth, missingFace, e, Finset.mul_sum] using
        congrArg (fun n : ℕ => 2 * n) hperm
    _ = 2 * (2 ^ (d - 1) * ∑ j, r j) := by
      rw [← Finset.powerset_univ, sum_powerset_sum_nat]
      simp
    _ = 2 ^ d * ∑ j, r j := by
      have hpow : 2 ^ d = 2 * 2 ^ (d - 1) := by
        calc
          2 ^ d = 2 ^ ((d - 1) + 1) := congrArg (2 ^ ·) (by omega)
          _ = 2 * 2 ^ (d - 1) := by rw [pow_succ]; ring
      rw [hpow]
      ring

/-- A Smith bar has length equal to its weighted depth when `a` is a DVR uniformizer. -/
theorem faceBar_length
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {d : ℕ} (a : R) (ha : Ideal.span ({a} : Set R) = maximalIdeal R)
    (r : Fin d → ℕ) (T : TensorFace d) :
    Module.length R (R ⧸ faceBarIdeal a r T) = weightedFaceDepth r T := by
  rw [faceBarIdeal, ← Ideal.span_singleton_pow, ha]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal R _

theorem factorSourceBar_length
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {d : ℕ} (a : R) (ha : Ideal.span ({a} : Set R) = maximalIdeal R)
    (r : Fin d → ℕ) (i : Fin d) :
    Module.length R (R ⧸ factorSourceBarIdeal a r i) = 2 * r i := by
  rw [factorSourceBarIdeal, ← Ideal.span_singleton_pow, ha]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal R _

theorem factorTraceTargetBar_length
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {d : ℕ} (a : R) (ha : Ideal.span ({a} : Set R) = maximalIdeal R)
    (r : Fin d → ℕ) (T : TensorFace d) :
    Module.length R (R ⧸ factorTraceTargetIdeal a r T) = factorTraceTargetDepth r T := by
  rw [factorTraceTargetIdeal, ← Ideal.span_singleton_pow, ha]
  exact IsDiscreteValuationRing.length_quotient_pow_maximalIdeal R _

/-- Source half of card `(22)`: `length K_r = 2^d ∑_i r_i`. -/
theorem factorCotangentModel_length
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {d : ℕ} [NeZero d] (a : R) (ha : Ideal.span ({a} : Set R) = maximalIdeal R)
    (r : Fin d → ℕ) :
    Module.length R (FactorCotangentModel a r) =
      ((2 ^ d * ∑ i, r i : ℕ) : ℕ∞) := by
  rw [Module.length_pi_of_fintype]
  simp only [Module.length_pi, ENat.card_eq_coe_natCard, Nat.card_eq_fintype_card,
    factorSourceFace_card, factorSourceBar_length a ha r]
  norm_cast
  simp_rw [← mul_assoc]
  rw [← Finset.mul_sum]
  have hd : 0 < d := Nat.pos_of_neZero d
  have hpow : 2 ^ d = 2 * 2 ^ (d - 1) := by
    calc
      2 ^ d = 2 ^ ((d - 1) + 1) := congrArg (2 ^ ·) (by omega)
      _ = 2 * 2 ^ (d - 1) := by rw [pow_succ]; ring
  rw [hpow]
  ring

/-- Target half of card `(22)`: `length L_r = 2^d ∑_i r_i`. -/
theorem factorTraceQuotientModel_length
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {d : ℕ} [NeZero d] (a : R) (ha : Ideal.span ({a} : Set R) = maximalIdeal R)
    (r : Fin d → ℕ) :
    Module.length R (FactorTraceQuotientModel a r) =
      ((2 ^ d * ∑ i, r i : ℕ) : ℕ∞) := by
  rw [Module.length_pi_of_fintype]
  simp_rw [factorTraceTargetBar_length a ha r]
  norm_cast
  exact sum_factorTraceTargetDepth r

/-- **Card `(21)`, module form.** Length of the heterogeneous factor-gradient cokernel is the sum
of its exact face depths. -/
theorem factorGradientCokernel_length_eq_sum_weightedFaceDepth
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {d : ℕ} (a : R) (ha : Ideal.span ({a} : Set R) = maximalIdeal R)
    (r : Fin d → ℕ) :
    Module.length R (FactorGradientCokernel a r) =
      ((∑ T : TensorFace d, weightedFaceDepth r T : ℕ) : ℕ∞) := by
  rw [(factorGradientCokernelEquivFaceBars a r).length_eq, Module.length_pi_of_fintype]
  simp_rw [faceBar_length a ha r]
  norm_cast

/-- Conversely, one actual factor contribution attains and generates the face bar ideal. -/
theorem exists_factorSourcePower_span_eq_faceBarIdeal
    {R : Type*} [CommRing R] {d : ℕ} [NeZero d]
    (a : R) (r : Fin d → ℕ) (T : TensorFace d) :
    ∃ i : Fin d, Ideal.span {a ^ factorSourceExponent r T i} = faceBarIdeal a r T := by
  obtain ⟨i, hi⟩ := exists_factorSourceExponent_eq_weightedFaceDepth r T
  exact ⟨i, by simp [faceBarIdeal, hi]⟩

/-- Homogeneous contact depths recover twice excess codimension, card `(10e)`. -/
theorem weightedFaceDepth_const_one
    {d : ℕ} [NeZero d] (T : TensorFace d) :
    weightedFaceDepth (fun _ : Fin d => 1) T = 2 * (d - 1 - T.card) := by
  classical
  by_cases hM : (missingFace T).Nonempty
  · have hmax : ((missingFace T).image fun _ : Fin d => 1).max' (hM.image _) = 1 := by
      apply le_antisymm
      · exact Finset.max'_le _ _ _ (by simp)
      · exact Finset.le_max' ((missingFace T).image (fun _ : Fin d => 1)) 1
          (Finset.mem_image_of_mem (fun _ : Fin d => 1) hM.choose_spec)
    have hcard : (missingFace T).card = d - T.card := by
      simpa [missingFace] using Finset.card_sdiff_of_subset (Finset.subset_univ T)
    have hpos : 0 < d - T.card := by
      rw [← hcard]
      exact Finset.card_pos.mpr hM
    simp [weightedFaceDepth, hM, hmax, hcard]
    omega
  · have hEmpty : missingFace T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hM
    have hcard : T.card = d := by
      have : T = Finset.univ := by
        have hsub : Finset.univ ⊆ T :=
          Finset.sdiff_eq_empty_iff_subset.mp (by simpa [missingFace] using hEmpty)
        exact Finset.Subset.antisymm (Finset.subset_univ T) hsub
      simp [this]
    simp [weightedFaceDepth, hM, hcard]

/-- Faces which survive the closed-horizon Jacobian quotient: the `(d - 3)`-skeleton. -/
abbrev ClosedHorizonFace (d : ℕ) := {T : TensorFace d // T.card ≤ d - 2}

/-- Exact face count in card `(10d)`. -/
theorem closedHorizonFace_card {d : ℕ} (hd : 2 ≤ d) :
    Fintype.card (ClosedHorizonFace d) = 2 ^ d - d - 1 := by
  classical
  let bad : TensorFace d → Prop := fun T => ¬ T.card ≤ d - 2
  have hbad (T : TensorFace d) : bad T ↔ T.card = d - 1 ∨ T.card = d := by
    have hle : T.card ≤ d := by
      simpa using Finset.card_le_univ T
    simp only [bad]
    omega
  have hbadCard : Fintype.card {T : TensorFace d // bad T} = d + 1 := by
    calc
      Fintype.card {T : TensorFace d // bad T} =
          Fintype.card {T : TensorFace d // T.card = d - 1 ∨ T.card = d} :=
        Fintype.card_congr (Equiv.subtypeEquivRight hbad)
      _ = Fintype.card {T : TensorFace d // T.card = d - 1} +
          Fintype.card {T : TensorFace d // T.card = d} := by
        apply Fintype.card_subtype_or_disjoint
        rw [Pi.disjoint_iff]
        intro T
        rw [Prop.disjoint_iff]
        omega
      _ = d.choose (d - 1) + d.choose d := by
        simp only [Fintype.card_finset_len, Fintype.card_fin]
      _ = d + 1 := by
        have hpred : d.choose (d - 1) = d := by
          have hd' : d - 1 + 1 = d := by omega
          simpa only [hd'] using Nat.choose_succ_self_right (d - 1)
        simp [hpred]
  have htotal : Fintype.card (TensorFace d) = 2 ^ d := by simp [TensorFace]
  calc
    Fintype.card (ClosedHorizonFace d) =
        Fintype.card {T : TensorFace d // ¬ bad T} :=
      Fintype.card_congr (Equiv.subtypeEquivRight (fun T => by simp [bad]))
    _ = Fintype.card (TensorFace d) - Fintype.card {T : TensorFace d // bad T} :=
      Fintype.card_subtype_compl bad
    _ = 2 ^ d - (d + 1) := by rw [htotal, hbadCard]
    _ = 2 ^ d - d - 1 := by omega

/-- Closed-horizon vector-space dimension from card `(10d)`. -/
theorem closedHorizonFaceSpace_finrank
    {k : Type*} [Field k] {d : ℕ} (hd : 2 ≤ d) :
    Module.finrank k (ClosedHorizonFace d → k) = 2 ^ d - d - 1 := by
  rw [Module.finrank_pi, closedHorizonFace_card hd]

/-- Binomial evaluation behind card `(9)`. -/
theorem homogeneous_face_depth_binomial_sum {d : ℕ} (hd : 2 ≤ d) :
    (∑ t ∈ Finset.range (d - 1), 2 * (d - 1 - t) * d.choose t) =
      2 ^ d * (d - 2) + 2 := by
  have hprefix0 : (∑ t ∈ Finset.range d, d.choose t) = 2 ^ d - 1 := by
    have h := Nat.sum_range_choose d
    rw [Finset.sum_range_succ] at h
    simp only [Nat.choose_self] at h
    omega
  have hprefix1 : (∑ t ∈ Finset.range d, t * d.choose t) =
      d * 2 ^ (d - 1) - d := by
    have h := Nat.sum_range_mul_choose d
    rw [Finset.sum_range_succ] at h
    simp only [Nat.choose_self, mul_one] at h
    omega
  have hpowOne : 1 ≤ 2 ^ (d - 1) := one_le_pow₀ (by omega)
  have hmul : d ≤ d * 2 ^ (d - 1) := by
    calc
      d = d * 1 := by simp
      _ ≤ d * 2 ^ (d - 1) := Nat.mul_le_mul_left d hpowOne
  have hprefix0Z : (∑ t ∈ Finset.range d, (d.choose t : ℤ)) = (2 : ℤ) ^ d - 1 := by
    rw [← Nat.cast_sum, hprefix0, Nat.cast_sub (one_le_pow₀ (by omega))]
    rfl
  have hprefix1Z : (∑ t ∈ Finset.range d, ((t * d.choose t : ℕ) : ℤ)) =
      (d : ℤ) * 2 ^ (d - 1) - d := by
    rw [← Nat.cast_sum, hprefix1, Nat.cast_sub hmul]
    rfl
  have hzero : 2 * (d - 1 - (d - 1)) * d.choose (d - 1) = 0 := by simp
  have hmain :
      (∑ t ∈ Finset.range d, (2 * (d - 1 - t) * d.choose t : ℕ) : ℤ) =
        2 * ((d - 1 : ℕ) : ℤ) * (∑ t ∈ Finset.range d, (d.choose t : ℤ)) -
          2 * ∑ t ∈ Finset.range d, ((t * d.choose t : ℕ) : ℤ) := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have ht' : t < d := Finset.mem_range.mp ht
    simp only [Nat.cast_mul]
    rw [Nat.cast_sub (by omega : t ≤ d - 1)]
    ring
  calc
    (∑ t ∈ Finset.range (d - 1), 2 * (d - 1 - t) * d.choose t) =
        (∑ t ∈ Finset.range (d - 1), 2 * (d - 1 - t) * d.choose t) +
          2 * (d - 1 - (d - 1)) * d.choose (d - 1) := by rw [hzero, add_zero]
    _ = ∑ t ∈ Finset.range ((d - 1) + 1), 2 * (d - 1 - t) * d.choose t := by
      rw [Finset.sum_range_succ]
    _ = ∑ t ∈ Finset.range d, 2 * (d - 1 - t) * d.choose t := by
      rw [show d - 1 + 1 = d by omega]
    _ = 2 ^ d * (d - 2) + 2 := by
      apply Int.ofNat_injective
      change ((↑(∑ t ∈ Finset.range d, 2 * (d - 1 - t) * d.choose t) : ℤ)) =
        (↑(2 ^ d * (d - 2) + 2) : ℤ)
      rw [Nat.cast_sum, hmain]
      rw [hprefix0Z, hprefix1Z, Nat.cast_add, Nat.cast_mul, Nat.cast_sub hd,
        Nat.cast_sub (by omega : 1 ≤ d)]
      push_cast
      have hpow : (2 : ℤ) ^ d = 2 * (2 : ℤ) ^ (d - 1) := by
        conv_lhs => rw [show d = (d - 1) + 1 by omega, pow_succ]
        ring
      rw [hpow]
      ring

/-- **Card `(9)`.** Total homogeneous Smith depth is `2^d(d-2)+2`. -/
theorem sum_weightedFaceDepth_const_one {d : ℕ} (hd : 2 ≤ d) :
    (∑ T : TensorFace d, weightedFaceDepth (fun _ : Fin d => 1) T) =
      2 ^ d * (d - 2) + 2 := by
  letI : NeZero d := ⟨by omega⟩
  calc
    (∑ T : TensorFace d, weightedFaceDepth (fun _ : Fin d => 1) T) =
        ∑ t ∈ Finset.range (d + 1), 2 * (d - 1 - t) * d.choose t := by
      rw [← Finset.powerset_univ, Finset.sum_powerset]
      simp only [Finset.card_univ, Fintype.card_fin]
      apply Finset.sum_congr rfl
      intro t ht
      simp_rw [weightedFaceDepth_const_one]
      have hsum :
          (∑ T ∈ (Finset.univ : Finset (Fin d)).powersetCard t,
              2 * (d - 1 - T.card)) =
            ∑ _T ∈ (Finset.univ : Finset (Fin d)).powersetCard t,
              2 * (d - 1 - t) := by
        apply Finset.sum_congr rfl
        intro T hT
        rw [(Finset.mem_powersetCard.mp hT).2]
      rw [hsum, Finset.sum_const, Finset.card_powersetCard]
      simp [Nat.nsmul_eq_mul, mul_comm, mul_left_comm]
    _ = ∑ t ∈ Finset.range (d - 1), 2 * (d - 1 - t) * d.choose t := by
      rw [show d + 1 = (d - 1) + 2 by omega, Finset.sum_range_succ,
        Finset.sum_range_succ]
      simp
    _ = 2 ^ d * (d - 2) + 2 := homogeneous_face_depth_binomial_sum hd

/-- **Card `(9)`, literal module length.** -/
theorem homogeneous_factorGradientCokernel_length
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    {d : ℕ} (hd : 2 ≤ d) (a : R)
    (ha : Ideal.span ({a} : Set R) = maximalIdeal R) :
    Module.length R (FactorGradientCokernel a (fun _ : Fin d => 1)) =
      ((2 ^ d * (d - 2) + 2 : ℕ) : ℕ∞) := by
  rw [factorGradientCokernel_length_eq_sum_weightedFaceDepth a ha,
    sum_weightedFaceDepth_const_one hd]

/-- Card `(11)`: the two-factor anomaly has exact length two. -/
theorem homogeneous_factorGradientCokernel_length_two
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (a : R) (ha : Ideal.span ({a} : Set R) = maximalIdeal R) :
    Module.length R (FactorGradientCokernel a (fun _ : Fin 2 => 1)) = 2 := by
  simpa using homogeneous_factorGradientCokernel_length (d := 2) (by omega) a ha

/-- Card `(12)`: the three-factor anomaly has exact length ten. -/
theorem homogeneous_factorGradientCokernel_length_three
    {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (a : R) (ha : Ideal.span ({a} : Set R) = maximalIdeal R) :
    Module.length R (FactorGradientCokernel a (fun _ : Fin 3 => 1)) = 10 := by
  simpa using homogeneous_factorGradientCokernel_length (d := 3) (by omega) a ha

end HTGeometry.ConstraintRelativity
