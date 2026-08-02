import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaAllFaceIndependence
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaTelescope
import GaloisForLFunctions.HTGeometry.MultipleEllipticGammaPacketCoface

/-!
# Structural translates of the order-two primitive decompose along the squarefree faces

Write `Ψ` for the logarithmic derivative of the genuine order-two multiple elliptic gamma function
attached to a three-element period family, and `σ_a` for translation by `a`.  Modulo differentially
algebraic functions, an arbitrary structural translate splits as

`σ_{n₀τ₀ + n₁τ₁ + n₂τ₂} Ψ = Ψ + Σᵢ (σ_{nᵢτᵢ} - 1) Ψ`,

and each single-direction difference telescopes into translates of the codimension-one face
coordinate obtained by deleting `i`.  The cross terms are differentially algebraic because
translating a codimension-one face packet in a *surviving* direction lands in a face with only one
period left.

This is the squarefree Stanley--Reisner relation `xᵢxⱼ ≡ 0` realized on the actual meromorphic
kernels: every structural translate is, up to differentially algebraic error, a
constant-coefficient combination of the top coordinate and the three single-direction face packets,
all of which are jointly differentially independent.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

/-! ## Two closure properties of differential algebraicity -/

/-- Zero is differentially algebraic. -/
theorem differentialAlgebraicOver_zero
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E] :
    DifferentialAlgebraicOver F (0 : E) := by
  simpa using differentialAlgebraicOver_algebraMap (F := F) (E := E) 0

/-- Differential algebraicity is closed under finite sums. -/
theorem differentialAlgebraicOver_finset_sum
    {F E : Type*} [Field F] [Field E] [Algebra F E]
    [Differential F] [Differential E] [DifferentialAlgebra F E] [CharZero E]
    {κ : Type*} (s : Finset κ) {f : κ → E}
    (hf : ∀ k ∈ s, DifferentialAlgebraicOver F (f k)) :
    DifferentialAlgebraicOver F (∑ k ∈ s, f k) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using differentialAlgebraicOver_zero (F := F) (E := E)
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact differentialAlgebraicOver_add (hf a (Finset.mem_insert_self a s))
        (ih fun k hk => hf k (Finset.mem_insert_of_mem hk))

/-! ## Differential algebraicity transports along translations -/

/-- Translation preserves differential algebraicity over the constants. -/
theorem differentialAlgebraicOver_addTranslationMeroEquiv (a : ℂ)
    {y : meroField (Set.univ : Set ℂ)} (hy : DifferentialAlgebraicOver ℂ y) :
    DifferentialAlgebraicOver ℂ (addTranslationMeroEquiv a y) := by
  have h := (addTranslationMeroDifferentialAlgEquiv a).differentialAlgebraicOver_map_iff y
  simpa only [addTranslationMeroDifferentialAlgEquiv, addTranslationMeroAlgEquiv] using! h.mpr hy

/-! ## Cross translations of a face packet are differentially algebraic -/

/-- One translation of a face packet in a surviving direction whose insertion leaves fewer than two
periods is differentially algebraic. -/
theorem differentialAlgebraicOver_facePacket_translate_sub
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    (J : Finset ι) {q : ι} (hq : q ∉ J) (hlt : (((insert q J))ᶜ).card < 2)
    {y : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ multipleEllipticGammaFacePacket τ hτ J) :
    DifferentialAlgebraicOver ℂ (addTranslationMeroEquiv (τ q) y - y) :=
  differentialAlgebraicOver_facePacket_of_compl_lt_two τ hτ hQ hι (insert q J) hlt
    (facePacket_translate_sub_mem τ hτ J hq hy)

/-- Repeated translation in a single surviving direction stays differentially algebraic. -/
theorem differentialAlgebraicOver_facePacket_translate_nsmul_sub
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    (J : Finset ι) {q : ι} (hq : q ∉ J) (hlt : (((insert q J))ᶜ).card < 2)
    {y : meroField (Set.univ : Set ℂ)}
    (hy : y ∈ multipleEllipticGammaFacePacket τ hτ J) (m : ℕ) :
    DifferentialAlgebraicOver ℂ (addTranslationMeroEquiv ((m : ℂ) * τ q) y - y) := by
  induction m with
  | zero => simpa [addTranslationMeroEquiv_zero_apply] using differentialAlgebraicOver_zero (F := ℂ)
  | succ m ih =>
      have hcast : (((m + 1 : ℕ)) : ℂ) * τ q = τ q + (m : ℂ) * τ q := by push_cast; ring
      have hsplit : addTranslationMeroEquiv ((((m + 1 : ℕ)) : ℂ) * τ q) y - y =
          addTranslationMeroEquiv (τ q) (addTranslationMeroEquiv ((m : ℂ) * τ q) y - y) +
            (addTranslationMeroEquiv (τ q) y - y) := by
        rw [hcast, ← addTranslationMeroEquiv_add, map_sub]
        abel
      rw [hsplit]
      exact differentialAlgebraicOver_add
        (differentialAlgebraicOver_addTranslationMeroEquiv (τ q) ih)
        (differentialAlgebraicOver_facePacket_translate_sub τ hτ hQ hι J hq hlt hy)

/-- Translating a face packet by any nonnegative integer combination of surviving directions whose
insertions leave fewer than two periods is differentially algebraic. -/
theorem differentialAlgebraicOver_facePacket_translate_finsetSum_sub
    (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (hι : 2 ≤ Fintype.card ι)
    (J : Finset ι) (m : ι → ℕ) :
    ∀ S : Finset ι, (∀ q ∈ S, q ∉ J) → (∀ q ∈ S, (((insert q J))ᶜ).card < 2) →
      ∀ {y : meroField (Set.univ : Set ℂ)}, y ∈ multipleEllipticGammaFacePacket τ hτ J →
        DifferentialAlgebraicOver ℂ
          (addTranslationMeroEquiv (∑ q ∈ S, (m q : ℂ) * τ q) y - y) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro _ _ y _
      simpa [addTranslationMeroEquiv_zero_apply] using differentialAlgebraicOver_zero (F := ℂ)
  | @insert p S hpS ih =>
      intro hmem hcard y hy
      have hpJ : p ∉ J := hmem p (Finset.mem_insert_self p S)
      have hpc : (((insert p J))ᶜ).card < 2 := hcard p (Finset.mem_insert_self p S)
      have hS : ∀ q ∈ S, q ∉ J := fun q hq => hmem q (Finset.mem_insert_of_mem hq)
      have hSc : ∀ q ∈ S, (((insert q J))ᶜ).card < 2 :=
        fun q hq => hcard q (Finset.mem_insert_of_mem hq)
      have hsum : ∑ q ∈ insert p S, (m q : ℂ) * τ q =
          (m p : ℂ) * τ p + ∑ q ∈ S, (m q : ℂ) * τ q := Finset.sum_insert hpS
      have hsplit : addTranslationMeroEquiv (∑ q ∈ insert p S, (m q : ℂ) * τ q) y - y =
          addTranslationMeroEquiv ((m p : ℂ) * τ p)
              (addTranslationMeroEquiv (∑ q ∈ S, (m q : ℂ) * τ q) y - y) +
            (addTranslationMeroEquiv ((m p : ℂ) * τ p) y - y) := by
        rw [hsum, ← addTranslationMeroEquiv_add, map_sub]
        abel
      rw [hsplit]
      exact differentialAlgebraicOver_add
        (differentialAlgebraicOver_addTranslationMeroEquiv _ (ih hS hSc hy))
        (differentialAlgebraicOver_facePacket_translate_nsmul_sub
          τ hτ hQ hι J hpJ hpc hy (m p))

/-! ## The order-two structural decomposition -/

/-- The single-direction face branch: the telescoped sum of translates of the codimension-one face
coordinate obtained by deleting `i`. -/
def orderTwoFaceBranch (τ : Fin 3 → ℂ) (hτ : ∀ i, 0 < (τ i).im) (i : Fin 3) (m : ℕ) :
    meroField (Set.univ : Set ℂ) :=
  ∑ j ∈ Finset.range m, addTranslationMeroEquiv ((j : ℂ) * τ i)
    (multipleEllipticGammaLogDerivFaceMero τ hτ {i})

theorem orderTwoFaceBranch_eq_translate_sub (τ : Fin 3 → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (i : Fin 3) (m : ℕ) :
    orderTwoFaceBranch τ hτ i m =
      addTranslationMeroEquiv ((m : ℂ) * τ i) (multipleEllipticGammaLogDerivMero τ hτ) -
        multipleEllipticGammaLogDerivMero τ hτ := by
  have h := multipleEllipticGammaLogDerivFaceMero_translate_sub_eq_sum τ hτ ∅
    (q := i) (by simp) m
  rw [multipleEllipticGammaLogDerivFaceMero_empty] at h
  simpa [orderTwoFaceBranch] using h.symm

/-- An integer multiple of the deleted period lies in the external lattice of a one-element
face. -/
theorem natCast_mul_mem_faceShiftLattice_singleton (τ : ι → ℂ) (i : ι) (j : ℕ) :
    (j : ℂ) * τ i ∈ faceShiftLattice τ ({i} : Finset ι) := by
  have hzero : (0 : ℂ) ∈ faceShiftLattice τ ({i} : Finset ι) := ⟨0, fun _ _ => rfl, by simp⟩
  simpa using
    faceShiftLattice_add_zsmul τ ({i} : Finset ι) (q := i) (by simp) hzero (j : ℤ)

theorem mem_facePacket_translate_faceMero (τ : ι → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (i : ι) (j : ℕ) :
    addTranslationMeroEquiv ((j : ℂ) * τ i)
        (multipleEllipticGammaLogDerivFaceMero τ hτ {i}) ∈
      multipleEllipticGammaFacePacket τ hτ {i} :=
  ⟨(j : ℂ) * τ i, natCast_mul_mem_faceShiftLattice_singleton τ i j, rfl⟩

/-- **Order-two structural decomposition.**  Every nonnegative structural translate of the
order-two primitive differs from the sum of the top coordinate and the three telescoped face
branches by a differentially algebraic function. -/
theorem orderTwoStructuralTranslate_sub_branches_differentialAlgebraic
    (τ : Fin 3 → ℂ) (hτ : ∀ i, 0 < (τ i).im)
    (hQ : PeriodsIntegrallyIndependent τ) (n : Fin 3 → ℕ) :
    DifferentialAlgebraicOver ℂ
      (addTranslationMeroEquiv (∑ i, (n i : ℂ) * τ i)
          (multipleEllipticGammaLogDerivMero τ hτ) -
        multipleEllipticGammaLogDerivMero τ hτ -
        ∑ i, orderTwoFaceBranch τ hτ i (n i)) := by
  have hι : 2 ≤ Fintype.card (Fin 3) := by simp
  set Ψ := multipleEllipticGammaLogDerivMero τ hτ with hΨ
  -- the cross terms produced by moving a branch out of its own direction
  have hcross : ∀ (i : Fin 3) (S : Finset (Fin 3)), (∀ q ∈ S, q ≠ i) →
      DifferentialAlgebraicOver ℂ
        (addTranslationMeroEquiv (∑ q ∈ S, (n q : ℂ) * τ q) (orderTwoFaceBranch τ hτ i (n i)) -
          orderTwoFaceBranch τ hτ i (n i)) := by
    intro i S hS
    have hmemS : ∀ q ∈ S, q ∉ ({i} : Finset (Fin 3)) := by
      intro q hq
      simpa using hS q hq
    have hcardS : ∀ q ∈ S, (((insert q ({i} : Finset (Fin 3))))ᶜ).card < 2 := by
      intro q hq
      have hqi : q ≠ i := hS q hq
      have hcard : (insert q ({i} : Finset (Fin 3))).card = 2 := by
        rw [Finset.card_insert_of_notMem (by simpa using hqi), Finset.card_singleton]
      have htotal := Finset.card_add_card_compl (insert q ({i} : Finset (Fin 3)))
      simp only [Fintype.card_fin] at htotal
      omega
    have hbranch : ∀ j ∈ Finset.range (n i),
        DifferentialAlgebraicOver ℂ
          (addTranslationMeroEquiv (∑ q ∈ S, (n q : ℂ) * τ q)
              (addTranslationMeroEquiv ((j : ℂ) * τ i)
                (multipleEllipticGammaLogDerivFaceMero τ hτ {i})) -
            addTranslationMeroEquiv ((j : ℂ) * τ i)
              (multipleEllipticGammaLogDerivFaceMero τ hτ {i})) := by
      intro j _
      exact differentialAlgebraicOver_facePacket_translate_finsetSum_sub τ hτ hQ hι
        ({i} : Finset (Fin 3)) n S hmemS hcardS
        (mem_facePacket_translate_faceMero τ hτ i j)
    have hsum : addTranslationMeroEquiv (∑ q ∈ S, (n q : ℂ) * τ q)
          (orderTwoFaceBranch τ hτ i (n i)) - orderTwoFaceBranch τ hτ i (n i) =
        ∑ j ∈ Finset.range (n i),
          (addTranslationMeroEquiv (∑ q ∈ S, (n q : ℂ) * τ q)
              (addTranslationMeroEquiv ((j : ℂ) * τ i)
                (multipleEllipticGammaLogDerivFaceMero τ hτ {i})) -
            addTranslationMeroEquiv ((j : ℂ) * τ i)
              (multipleEllipticGammaLogDerivFaceMero τ hτ {i})) := by
      rw [orderTwoFaceBranch, map_sum, ← Finset.sum_sub_distrib]
    rw [hsum]
    exact differentialAlgebraicOver_finset_sum _ hbranch
  -- telescope the three structural directions
  have hτsum : ∑ i, (n i : ℂ) * τ i =
      (n 0 : ℂ) * τ 0 + ((n 1 : ℂ) * τ 1 + (n 2 : ℂ) * τ 2) := by
    simp [Fin.sum_univ_three]
    ring
  have hb0 : orderTwoFaceBranch τ hτ 0 (n 0) =
      addTranslationMeroEquiv ((n 0 : ℂ) * τ 0) Ψ - Ψ :=
    orderTwoFaceBranch_eq_translate_sub τ hτ 0 (n 0)
  have hb1 : orderTwoFaceBranch τ hτ 1 (n 1) =
      addTranslationMeroEquiv ((n 1 : ℂ) * τ 1) Ψ - Ψ :=
    orderTwoFaceBranch_eq_translate_sub τ hτ 1 (n 1)
  have hb2 : orderTwoFaceBranch τ hτ 2 (n 2) =
      addTranslationMeroEquiv ((n 2 : ℂ) * τ 2) Ψ - Ψ :=
    orderTwoFaceBranch_eq_translate_sub τ hτ 2 (n 2)
  have hbranchSum : ∑ i, orderTwoFaceBranch τ hτ i (n i) =
      orderTwoFaceBranch τ hτ 0 (n 0) + orderTwoFaceBranch τ hτ 1 (n 1) +
        orderTwoFaceBranch τ hτ 2 (n 2) := by
    simp [Fin.sum_univ_three]
  have hcross2 := hcross 2 {0, 1} (by decide)
  have hcross1 := hcross 1 {0} (by decide)
  have hkey : addTranslationMeroEquiv (∑ i, (n i : ℂ) * τ i) Ψ - Ψ -
      ∑ i, orderTwoFaceBranch τ hτ i (n i) =
      (addTranslationMeroEquiv (∑ q ∈ ({0, 1} : Finset (Fin 3)), (n q : ℂ) * τ q)
          (orderTwoFaceBranch τ hτ 2 (n 2)) - orderTwoFaceBranch τ hτ 2 (n 2)) +
      (addTranslationMeroEquiv (∑ q ∈ ({0} : Finset (Fin 3)), (n q : ℂ) * τ q)
          (orderTwoFaceBranch τ hτ 1 (n 1)) - orderTwoFaceBranch τ hτ 1 (n 1)) := by
    have hs01 : ∑ q ∈ ({0, 1} : Finset (Fin 3)), (n q : ℂ) * τ q =
        (n 0 : ℂ) * τ 0 + (n 1 : ℂ) * τ 1 :=
      Finset.sum_pair (by decide)
    have hs0 : ∑ q ∈ ({0} : Finset (Fin 3)), (n q : ℂ) * τ q = (n 0 : ℂ) * τ 0 := by simp
    rw [hbranchSum, hb0, hb1, hb2, hs01, hs0, hτsum]
    simp only [map_sub, ← addTranslationMeroEquiv_add]
    abel
  rw [hkey]
  exact differentialAlgebraicOver_add hcross2 hcross1

end

end GaloisForLFunctions
