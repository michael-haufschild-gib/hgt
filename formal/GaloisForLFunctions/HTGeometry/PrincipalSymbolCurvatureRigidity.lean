import GaloisForLFunctions.HTGeometry.GradedPrincipalSymbolHorizon

/-!
# Principal-symbol curvature and horizon rigidity

The consecutive layer symbols of a rank-one filtered law carry an alternating curvature.  It is
the two-layer principal coefficient of a commutator.  If the laws close under commutator inside the
same first-order filtered law space, this curvature vanishes.  Consequently all nonzero layer
symbols have the same kernel, so the apparent countable characteristic arrangement collapses to a
single horizon.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open Module Set

variable {k K L g : Type*} [Field k] [Field K] [Field L]
  [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
  [AddCommMonoid g] [Module k g]

/-- The alternating consecutive-symbol coefficient detected by a two-step commutator. -/
def principalSymbolCurvature
    (symbol : ℕ → g →ₗ[k] K) (n : ℕ) (A B : g) : K :=
  symbol n B * symbol (n + 1) A -
    symbol n A * symbol (n + 1) B

/-- The curvature as a genuine `k`-bilinear form on law space. -/
def principalSymbolCurvatureForm
    (symbol : ℕ → g →ₗ[k] K) (n : ℕ) :
    g →ₗ[k] g →ₗ[k] K :=
  LinearMap.mk₂ k (principalSymbolCurvature symbol n)
    (by
      intro A B C
      simp [principalSymbolCurvature]
      ring)
    (by
      intro c A B
      simp [principalSymbolCurvature, Algebra.smul_def]
      ring)
    (by
      intro A B C
      simp [principalSymbolCurvature]
      ring)
    (by
      intro c A B
      simp [principalSymbolCurvature, Algebra.smul_def]
      ring)

@[simp]
theorem principalSymbolCurvatureForm_apply
    (symbol : ℕ → g →ₗ[k] K) (n : ℕ) (A B : g) :
    principalSymbolCurvatureForm symbol n A B =
      principalSymbolCurvature symbol n A B := rfl

@[simp]
theorem principalSymbolCurvature_self
    (symbol : ℕ → g →ₗ[k] K) (n : ℕ) (A : g) :
    principalSymbolCurvature symbol n A A = 0 := by
  simp [principalSymbolCurvature]

theorem principalSymbolCurvature_swap
    (symbol : ℕ → g →ₗ[k] K) (n : ℕ) (A B : g) :
    principalSymbolCurvature symbol n B A =
      -principalSymbolCurvature symbol n A B := by
  simp [principalSymbolCurvature]

@[simp]
theorem principalSymbolCurvature_zero_left
    (symbol : ℕ → g →ₗ[k] K) (n : ℕ) (B : g) :
    principalSymbolCurvature symbol n 0 B = 0 := by
  simp [principalSymbolCurvature]

theorem coefficient_eq_zero_of_smul_source_mem_principalFiltration
    (u : ℕ → L) (hu : AlgebraicIndependent K u) (n : ℕ) (c : K)
    (hc : c • u n ∈ principalFiltration (K := K) u n) :
    c = 0 := by
  have hsubset : Set.range (fun j : Fin n ↦ u j) ⊆
      u '' (Set.univ \ {n}) := by
    rintro y ⟨j, rfl⟩
    refine ⟨j, ?_, rfl⟩
    simp only [Set.mem_sdiff, Set.mem_univ, Set.mem_singleton_iff, true_and]
    exact Nat.ne_of_lt j.isLt
  exact hu.linearIndependent.eq_zero_of_smul_mem_span n c
    ((Submodule.span_mono hsubset) hc)

/-- The principal two-layer term of a composite filtered law is the product of its consecutive
layer symbols. -/
theorem law_comp_sub_consecutiveSymbol_smul_mem
    (law : g →ₗ[k] Derivation k L L)
    (coefficientLaw : g →ₗ[k] Derivation k K K)
    (symbol : ℕ → g →ₗ[k] K) (u : ℕ → L)
    (hcompat : ∀ A : g, ∀ a : K,
      law A (algebraMap K L a) = algebraMap K L (coefficientLaw A a))
    (hstep : ∀ A : g, ∀ n : ℕ,
      law A (u n) - symbol n A • u (n + 1) ∈
        principalFiltration (K := K) u (n + 1))
    (A B : g) (n : ℕ) :
    law A (law B (u n)) -
        (symbol n B * symbol (n + 1) A) • u (n + 2) ∈
      principalFiltration (K := K) u (n + 2) := by
  let r : L := law B (u n) - symbol n B • u (n + 1)
  have hr : r ∈ principalFiltration (K := K) u (n + 1) := hstep B n
  have hAr : law A r ∈ principalFiltration (K := K) u (n + 2) := by
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      derivation_principalFiltration_succ_graded
        (coefficientLaw A) (law A) u (fun j ↦ symbol j A)
        (hcompat A) (hstep A) (n + 1) hr
  have hcoeff : coefficientLaw A (symbol n B) • u (n + 1) ∈
      principalFiltration (K := K) u (n + 2) :=
    (principalFiltration (K := K) u (n + 2)).smul_mem _
      (principalFiltration_source_mem (K := K) u (by omega))
  have hscaled : symbol n B •
      (law A (u (n + 1)) - symbol (n + 1) A • u (n + 2)) ∈
      principalFiltration (K := K) u (n + 2) :=
    (principalFiltration (K := K) u (n + 2)).smul_mem _ (hstep A (n + 1))
  have hsum := (principalFiltration (K := K) u (n + 2)).add_mem
    ((principalFiltration (K := K) u (n + 2)).add_mem hAr hcoeff) hscaled
  have hrEq : law B (u n) = r + symbol n B • u (n + 1) := by
    exact (sub_add_cancel _ _).symm
  rw [hrEq, map_add, Algebra.smul_def, Derivation.leibniz, hcompat]
  convert hsum using 1 <;> simp [Algebra.smul_def] <;> ring

/-- The two-layer principal coefficient of the commutator is exactly the consecutive-symbol
curvature. -/
theorem law_commutator_sub_principalSymbolCurvature_smul_mem
    (law : g →ₗ[k] Derivation k L L)
    (coefficientLaw : g →ₗ[k] Derivation k K K)
    (symbol : ℕ → g →ₗ[k] K) (u : ℕ → L)
    (hcompat : ∀ A : g, ∀ a : K,
      law A (algebraMap K L a) = algebraMap K L (coefficientLaw A a))
    (hstep : ∀ A : g, ∀ n : ℕ,
      law A (u n) - symbol n A • u (n + 1) ∈
        principalFiltration (K := K) u (n + 1))
    (A B : g) (n : ℕ) :
    law A (law B (u n)) - law B (law A (u n)) -
        principalSymbolCurvature symbol n A B • u (n + 2) ∈
      principalFiltration (K := K) u (n + 2) := by
  have hAB := law_comp_sub_consecutiveSymbol_smul_mem
    law coefficientLaw symbol u hcompat hstep A B n
  have hBA := law_comp_sub_consecutiveSymbol_smul_mem
    law coefficientLaw symbol u hcompat hstep B A n
  have hsub := (principalFiltration (K := K) u (n + 2)).sub_mem hAB hBA
  convert hsub using 1 <;>
    simp [principalSymbolCurvature, Algebra.smul_def] <;> ring

/-- First-order commutator closure forces the consecutive-symbol curvature to vanish. -/
theorem principalSymbolCurvature_eq_zero_of_commutatorClosure
    (law : g →ₗ[k] Derivation k L L)
    (coefficientLaw : g →ₗ[k] Derivation k K K)
    (symbol : ℕ → g →ₗ[k] K) (u : ℕ → L)
    (hcompat : ∀ A : g, ∀ a : K,
      law A (algebraMap K L a) = algebraMap K L (coefficientLaw A a))
    (hstep : ∀ A : g, ∀ n : ℕ,
      law A (u n) - symbol n A • u (n + 1) ∈
        principalFiltration (K := K) u (n + 1))
    (hu : AlgebraicIndependent K u)
    (bracket : g → g → g)
    (hclosure : ∀ A B : g, ∀ x : L,
      law A (law B x) - law B (law A x) = law (bracket A B) x) :
    ∀ n A B, principalSymbolCurvature symbol n A B = 0 := by
  intro n A B
  have hcurv := law_commutator_sub_principalSymbolCurvature_smul_mem
    law coefficientLaw symbol u hcompat hstep A B n
  rw [hclosure A B (u n)] at hcurv
  have hlaw : law (bracket A B) (u n) ∈
      principalFiltration (K := K) u (n + 2) := by
    have hun : u n ∈ principalFiltration (K := K) u (n + 1) :=
      principalFiltration_source_mem (K := K) u (by omega)
    simpa only [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      derivation_principalFiltration_succ_graded
        (coefficientLaw (bracket A B)) (law (bracket A B)) u
        (fun j ↦ symbol j (bracket A B))
        (hcompat (bracket A B)) (hstep (bracket A B)) (n + 1) hun
  have hlead := (principalFiltration (K := K) u (n + 2)).sub_mem hlaw hcurv
  have hlead' : principalSymbolCurvature symbol n A B • u (n + 2) ∈
      principalFiltration (K := K) u (n + 2) := by
    convert hlead using 1 <;> abel
  exact coefficient_eq_zero_of_smul_source_mem_principalFiltration
    u hu (n + 2) (principalSymbolCurvature symbol n A B) hlead'

/-- A nonzero curvature value is an unconditional obstruction to closing the candidate laws under
commutator inside the same first-order filtered law space. -/
theorem no_commutatorClosure_of_principalSymbolCurvature_ne_zero
    (law : g →ₗ[k] Derivation k L L)
    (coefficientLaw : g →ₗ[k] Derivation k K K)
    (symbol : ℕ → g →ₗ[k] K) (u : ℕ → L)
    (hcompat : ∀ A : g, ∀ a : K,
      law A (algebraMap K L a) = algebraMap K L (coefficientLaw A a))
    (hstep : ∀ A : g, ∀ n : ℕ,
      law A (u n) - symbol n A • u (n + 1) ∈
        principalFiltration (K := K) u (n + 1))
    (hu : AlgebraicIndependent K u)
    (n : ℕ) (A B : g)
    (hcurv : principalSymbolCurvature symbol n A B ≠ 0) :
    ¬ ∃ bracket : g → g → g, ∀ C D : g, ∀ x : L,
      law C (law D x) - law D (law C x) = law (bracket C D) x := by
  rintro ⟨bracket, hclosure⟩
  exact hcurv (principalSymbolCurvature_eq_zero_of_commutatorClosure
    law coefficientLaw symbol u hcompat hstep hu bracket hclosure n A B)

theorem exists_apply_ne_zero_of_linearMap_ne_zero
    (f : g →ₗ[k] K) (hf : f ≠ 0) :
    ∃ A, f A ≠ 0 := by
  by_contra h
  push Not at h
  apply hf
  ext A
  simpa using h A

/-- Vanishing consecutive-symbol curvature makes two nonzero adjacent layer symbols have the same
kernel. -/
theorem consecutiveSymbol_ker_eq_of_curvature_zero
    (symbol : ℕ → g →ₗ[k] K) (n : ℕ)
    (hcurv : ∀ A B, principalSymbolCurvature symbol n A B = 0)
    (hn : symbol n ≠ 0) (hnext : symbol (n + 1) ≠ 0) :
    (symbol n).ker = (symbol (n + 1)).ker := by
  ext A
  simp only [LinearMap.mem_ker]
  constructor
  · intro hA
    obtain ⟨B, hB⟩ := exists_apply_ne_zero_of_linearMap_ne_zero (symbol n) hn
    have hprod : symbol n B * symbol (n + 1) A = 0 := by
      simpa [principalSymbolCurvature, hA] using hcurv A B
    exact (mul_eq_zero.mp hprod).resolve_left hB
  · intro hA
    obtain ⟨B, hB⟩ :=
      exists_apply_ne_zero_of_linearMap_ne_zero (symbol (n + 1)) hnext
    have hprod : symbol n A * symbol (n + 1) B = 0 := by
      simpa [principalSymbolCurvature, hA] using hcurv B A
    exact (mul_eq_zero.mp hprod).resolve_right hB

/-- In the flat nondegenerate case every layer symbol has the same characteristic kernel. -/
theorem all_layerSymbol_kernels_eq_first_of_curvature_zero
    (symbol : ℕ → g →ₗ[k] K)
    (hcurv : ∀ n A B, principalSymbolCurvature symbol n A B = 0)
    (hsymbol : ∀ n, symbol n ≠ 0) :
    ∀ n, (symbol n).ker = (symbol 0).ker := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
      exact (consecutiveSymbol_ker_eq_of_curvature_zero symbol n
        (hcurv n) (hsymbol n) (hsymbol (n + 1))).symm.trans ih

/-- The curvature is intrinsic whenever two proposed symbol sequences describe the same filtered
law action on an algebraically free source. -/
theorem principalSymbolCurvature_unique
    (law : g →ₗ[k] Derivation k L L)
    (symbol₁ symbol₂ : ℕ → g →ₗ[k] K) (u : ℕ → L)
    (hstep₁ : ∀ A : g, ∀ n : ℕ,
      law A (u n) - symbol₁ n A • u (n + 1) ∈
        principalFiltration (K := K) u (n + 1))
    (hstep₂ : ∀ A : g, ∀ n : ℕ,
      law A (u n) - symbol₂ n A • u (n + 1) ∈
        principalFiltration (K := K) u (n + 1))
    (hu : AlgebraicIndependent K u) :
    ∀ n A B,
      principalSymbolCurvature symbol₁ n A B =
        principalSymbolCurvature symbol₂ n A B := by
  have hsymbol : symbol₁ = symbol₂ := by
    funext n
    apply LinearMap.ext
    intro A
    exact congrFun (gradedPrincipalSymbol_unique (law A) u
      (fun j ↦ symbol₁ j A) (fun j ↦ symbol₂ j A)
      (hstep₁ A) (hstep₂ A) hu) n
  subst symbol₂
  simp

/-- If one layer symbol vanishes identically, every law direction is characteristic. -/
theorem characteristicSet_eq_univ_of_layerSymbol_eq_zero
    (law : g →ₗ[k] Derivation k L L)
    (coefficientLaw : g →ₗ[k] Derivation k K K)
    (symbol : ℕ → g →ₗ[k] K) (u : ℕ → L)
    (hcompat : ∀ A : g, ∀ a : K,
      law A (algebraMap K L a) = algebraMap K L (coefficientLaw A a))
    (hstep : ∀ A : g, ∀ n : ℕ,
      law A (u n) - symbol n A • u (n + 1) ∈
        principalFiltration (K := K) u (n + 1))
    (hu : AlgebraicIndependent K u)
    (m : ℕ) (hm : symbol m = 0) :
    {A : g | ¬ AlgebraicIndependent K
      (fun n : ℕ ↦ ((law A : L → L)^[n] (u 0)))} = Set.univ := by
  ext A
  simp only [Set.mem_setOf_eq, Set.mem_univ, iff_true]
  intro hAI
  have hnonzero := (gradedPrincipalJet_algebraicIndependent_iff
    (coefficientLaw A) (law A) u (fun n ↦ symbol n A)
    (hcompat A) (hstep A) hu).mp hAI m
  apply hnonzero
  simp [hm]

/-- **Flat rank-one horizon rigidity.** If every layer symbol is nonzero and the law space closes
under commutator, the entire differential-algebraic law spectrum is one kernel, not a countable
arrangement. -/
theorem characteristicSet_eq_first_ker_of_commutatorClosure
    (law : g →ₗ[k] Derivation k L L)
    (coefficientLaw : g →ₗ[k] Derivation k K K)
    (symbol : ℕ → g →ₗ[k] K) (u : ℕ → L)
    (hcompat : ∀ A : g, ∀ a : K,
      law A (algebraMap K L a) = algebraMap K L (coefficientLaw A a))
    (hstep : ∀ A : g, ∀ n : ℕ,
      law A (u n) - symbol n A • u (n + 1) ∈
        principalFiltration (K := K) u (n + 1))
    (hu : AlgebraicIndependent K u)
    (hsymbol : ∀ n, symbol n ≠ 0)
    (bracket : g → g → g)
    (hclosure : ∀ A B : g, ∀ x : L,
      law A (law B x) - law B (law A x) = law (bracket A B) x) :
    {A : g | ¬ AlgebraicIndependent K
      (fun n : ℕ ↦ ((law A : L → L)^[n] (u 0)))} =
      ((symbol 0).ker : Set g) := by
  have hcurv := principalSymbolCurvature_eq_zero_of_commutatorClosure
    law coefficientLaw symbol u hcompat hstep hu bracket hclosure
  have hk := all_layerSymbol_kernels_eq_first_of_curvature_zero symbol hcurv hsymbol
  ext A
  simp only [Set.mem_setOf_eq, LinearMap.mem_ker]
  have hiff := gradedPrincipalJet_algebraicIndependent_iff
    (coefficientLaw A) (law A) u (fun n ↦ symbol n A)
    (hcompat A) (hstep A) hu
  constructor
  · intro hnot
    by_contra hzero
    apply hnot
    apply hiff.mpr
    intro n hn
    have hmemn : A ∈ (symbol n).ker := hn
    have hmem0 : A ∈ (symbol 0).ker := by
      rw [← hk n]
      exact hmemn
    exact hzero hmem0
  · intro hzero hAI
    exact (hiff.mp hAI 0) hzero

/-- Complete integrable rank-one dichotomy: either one layer symbol vanishes and every direction is
characteristic, or all layer symbols are nonzero and the characteristic spectrum is the single
first-symbol kernel. -/
theorem characteristicSet_integrable_rankOne_dichotomy
    (law : g →ₗ[k] Derivation k L L)
    (coefficientLaw : g →ₗ[k] Derivation k K K)
    (symbol : ℕ → g →ₗ[k] K) (u : ℕ → L)
    (hcompat : ∀ A : g, ∀ a : K,
      law A (algebraMap K L a) = algebraMap K L (coefficientLaw A a))
    (hstep : ∀ A : g, ∀ n : ℕ,
      law A (u n) - symbol n A • u (n + 1) ∈
        principalFiltration (K := K) u (n + 1))
    (hu : AlgebraicIndependent K u)
    (bracket : g → g → g)
    (hclosure : ∀ A B : g, ∀ x : L,
      law A (law B x) - law B (law A x) = law (bracket A B) x) :
    (∃ m, symbol m = 0 ∧
      {A : g | ¬ AlgebraicIndependent K
        (fun n : ℕ ↦ ((law A : L → L)^[n] (u 0)))} = Set.univ) ∨
    ((∀ m, symbol m ≠ 0) ∧
      {A : g | ¬ AlgebraicIndependent K
        (fun n : ℕ ↦ ((law A : L → L)^[n] (u 0)))} =
          ((symbol 0).ker : Set g)) := by
  classical
  by_cases hzero : ∃ m, symbol m = 0
  · left
    obtain ⟨m, hm⟩ := hzero
    exact ⟨m, hm, characteristicSet_eq_univ_of_layerSymbol_eq_zero
      law coefficientLaw symbol u hcompat hstep hu m hm⟩
  · right
    have hsymbol : ∀ m, symbol m ≠ 0 := by
      intro m hm
      exact hzero ⟨m, hm⟩
    exact ⟨hsymbol, characteristicSet_eq_first_ker_of_commutatorClosure
      law coefficientLaw symbol u hcompat hstep hu hsymbol bracket hclosure⟩

end

end GaloisForLFunctions.HTGeometry
