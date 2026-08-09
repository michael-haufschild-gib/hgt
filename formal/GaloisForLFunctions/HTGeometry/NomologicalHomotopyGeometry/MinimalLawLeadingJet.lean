import GaloisForLFunctions.HilbertMetric.NomologicalCrossGram
import Mathlib.LinearAlgebra.Pi

set_option maxHeartbeats 200000

/-!
# Leading formal-law jets and observer irreversibility

The weight-`m` component of a coalgebra-morphism equation consists of the linearly conjugated
`m`-ary operations plus partition terms involving only lower operations.  This file retains that
exact triangular structure and proves invariance of first nonzero weight and its linear conjugacy.
It also proves homotopy-abelianity invariance, serial tangent loss, the parallel kernel-intersection
gate, the sharp injective/non-surjective countermodel, and re-exports the exact framed Gram polar
fibre theorem already proved in the Hilbert module.
-/

namespace HTGeometry.NomologicalHomotopyGeometry.MinimalLawLeadingJet

/-- Taylor operations of a minimal formal law on a graded carrier. -/
structure MinimalLaw (Arity : ℕ → Type*) (H : Type*)
    [∀ n, AddCommGroup (Arity n)] [∀ n, Module ℝ (Arity n)]
    [AddCommGroup H] [Module ℝ H] where
  operation : ∀ n, Arity n →ₗ[ℝ] H
  unary_zero : operation 1 = 0

namespace MinimalLaw

variable {Arity : ℕ → Type*} {H : Type*}
variable [∀ n, AddCommGroup (Arity n)] [∀ n, Module ℝ (Arity n)]
variable [AddCommGroup H] [Module ℝ H]

/-- `r` is the first nonzero primary operation order. -/
def FirstNonzero (Q : MinimalLaw Arity H) (r : ℕ) : Prop :=
  2 ≤ r ∧ Q.operation r ≠ 0 ∧
    ∀ n, 2 ≤ n → n < r → Q.operation n = 0

/-- A minimal formal law is abelian when every operation of arity at least two vanishes. -/
def IsAbelian (Q : MinimalLaw Arity H) : Prop :=
  ∀ n, 2 ≤ n → Q.operation n = 0

/-- Every nonabelian minimal law has a first nonzero operation. -/
theorem exists_firstNonzero_of_not_abelian (Q : MinimalLaw Arity H)
    (hQ : ¬Q.IsAbelian) : ∃ r, Q.FirstNonzero r := by
  classical
  simp only [IsAbelian, not_forall] at hQ
  obtain ⟨r, hr⟩ := hQ
  have hex : ∃ n, 2 ≤ n ∧ Q.operation n ≠ 0 := by
    obtain ⟨hr2, hrne⟩ := hr
    exact ⟨r, hr2, hrne⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro n hn hnm
  by_contra hne
  exact absurd (Nat.find_min' hex ⟨hn, hne⟩) (Nat.not_le.mpr hnm)

end MinimalLaw

/-- Triangular weight decomposition of an invertible formal coordinate change.

The two remainders are precisely the non-leading partition terms in `FQ = Q'F`; each vanishes
when all lower source or target operations vanish.
-/
structure MinimalLawEquiv
    (A B : ℕ → Type*) (H H' : Type*)
    [∀ n, AddCommGroup (A n)] [∀ n, Module ℝ (A n)]
    [∀ n, AddCommGroup (B n)] [∀ n, Module ℝ (B n)]
    [AddCommGroup H] [Module ℝ H] [AddCommGroup H'] [Module ℝ H']
    (Q : MinimalLaw A H) (Q' : MinimalLaw B H') where
  linear : H ≃ₗ[ℝ] H'
  arity : ∀ n, A n ≃ₗ[ℝ] B n
  sourceRemainder : ∀ n, A n →ₗ[ℝ] H'
  targetRemainder : ∀ n, A n →ₗ[ℝ] H'
  weightEquation : ∀ n,
    linear.toLinearMap.comp (Q.operation n) + sourceRemainder n =
      (Q'.operation n).comp (arity n).toLinearMap + targetRemainder n
  sourceRemainder_zero : ∀ n,
    (∀ m, 2 ≤ m → m < n → Q.operation m = 0) → sourceRemainder n = 0
  targetRemainder_zero : ∀ n,
    (∀ m, 2 ≤ m → m < n → Q'.operation m = 0) → targetRemainder n = 0

namespace MinimalLawEquiv

variable {A B : ℕ → Type*} {H H' : Type*}
variable [∀ n, AddCommGroup (A n)] [∀ n, Module ℝ (A n)]
variable [∀ n, AddCommGroup (B n)] [∀ n, Module ℝ (B n)]
variable [AddCommGroup H] [Module ℝ H] [AddCommGroup H'] [Module ℝ H']
variable {Q : MinimalLaw A H} {Q' : MinimalLaw B H'}
variable (F : MinimalLawEquiv A B H H' Q Q')

/-- At a common first surviving weight, the full morphism equation reduces to linear conjugacy. -/
theorem leading_weight_equation (r : ℕ)
    (hQ : ∀ m, 2 ≤ m → m < r → Q.operation m = 0)
    (hQ' : ∀ m, 2 ≤ m → m < r → Q'.operation m = 0) :
    F.linear.toLinearMap.comp (Q.operation r) =
      (Q'.operation r).comp (F.arity r).toLinearMap := by
  have h := F.weightEquation r
  rw [F.sourceRemainder_zero r hQ, F.targetRemainder_zero r hQ', add_zero, add_zero] at h
  exact h

/-- If the target leading operation vanishes under the reduced weight equation, so does source. -/
theorem source_zero_of_target_zero (r : ℕ)
    (hEq : F.linear.toLinearMap.comp (Q.operation r) =
      (Q'.operation r).comp (F.arity r).toLinearMap)
    (hzero : Q'.operation r = 0) : Q.operation r = 0 := by
  apply LinearMap.ext
  intro x
  apply F.linear.injective
  have hx := LinearMap.congr_fun hEq x
  simpa [hzero, LinearMap.comp_apply] using hx

/-- If source leading operation vanishes under the reduced equation, so does target. -/
theorem target_zero_of_source_zero (r : ℕ)
    (hEq : F.linear.toLinearMap.comp (Q.operation r) =
      (Q'.operation r).comp (F.arity r).toLinearMap)
    (hzero : Q.operation r = 0) : Q'.operation r = 0 := by
  apply LinearMap.ext
  intro y
  let x := (F.arity r).symm y
  have hx := LinearMap.congr_fun hEq x
  simpa [x, hzero, LinearMap.comp_apply] using hx.symm

include F in
/-- First nonzero formal-law order is invariant under invertible formal coordinate change. -/
theorem firstNonzero_order_eq {r s : ℕ}
    (hr : Q.FirstNonzero r) (hs : Q'.FirstNonzero s) : r = s := by
  apply le_antisymm
  · by_contra hnot
    have hsr : s < r := Nat.lt_of_not_ge hnot
    have hEq := F.leading_weight_equation s
      (fun m hm hms => hr.2.2 m hm (lt_trans hms hsr)) hs.2.2
    exact hs.2.1 (F.target_zero_of_source_zero s hEq (hr.2.2 s hs.1 hsr))
  · by_contra hnot
    have hrs : r < s := Nat.lt_of_not_ge hnot
    have hEq := F.leading_weight_equation r hr.2.2
      (fun m hm hmr => hs.2.2 m hm (lt_trans hmr hrs))
    exact hr.2.1 (F.source_zero_of_target_zero r hEq (hs.2.2 r hr.1 hrs))

/-- Primary operations at the common first order are linearly conjugate. -/
theorem firstNonzero_conjugacy {r : ℕ}
    (hr : Q.FirstNonzero r) (hr' : Q'.FirstNonzero r) :
    F.linear.toLinearMap.comp (Q.operation r) =
      (Q'.operation r).comp (F.arity r).toLinearMap :=
  F.leading_weight_equation r hr.2.2 hr'.2.2

include F in
/-- A nonabelian source cannot be isomorphic to an abelian target. -/
theorem not_target_abelian_of_source_firstNonzero {r : ℕ}
    (hr : Q.FirstNonzero r) : ¬Q'.IsAbelian := by
  intro hAb
  have hEq := F.leading_weight_equation r hr.2.2
    (fun m hm _ => hAb m hm)
  exact hr.2.1 (F.source_zero_of_target_zero r hEq (hAb r hr.1))

include F in
/-- An abelian source cannot be isomorphic to a nonabelian target. -/
theorem not_source_abelian_of_target_firstNonzero {r : ℕ}
    (hr : Q'.FirstNonzero r) : ¬Q.IsAbelian := by
  intro hAb
  have hEq := F.leading_weight_equation r (fun m hm _ => hAb m hm) hr.2.2
  exact hr.2.1 (F.target_zero_of_source_zero r hEq (hAb r hr.1))

include F in
/-- Homotopy-abelianity is invariant under minimal formal-law isomorphism. -/
theorem abelian_iff : Q.IsAbelian ↔ Q'.IsAbelian := by
  constructor
  · intro hQ
    by_contra hQ'
    obtain ⟨r, hr⟩ := Q'.exists_firstNonzero_of_not_abelian hQ'
    exact F.not_source_abelian_of_target_firstNonzero hr hQ
  · intro hQ'
    by_contra hQ
    obtain ⟨r, hr⟩ := Q.exists_firstNonzero_of_not_abelian hQ
    exact F.not_target_abelian_of_source_firstNonzero hr hQ'

end MinimalLawEquiv

section ObserverIrreversibility

variable {H M N : Type*}
variable [AddCommGroup H] [Module ℝ H]
variable [AddCommGroup M] [Module ℝ M]
variable [AddCommGroup N] [Module ℝ N]

/-- Every tangent direction killed by one observer remains killed after serial composition. -/
theorem ker_le_serial_comp (f : H →ₗ[ℝ] M) (g : M →ₗ[ℝ] N) :
    LinearMap.ker f ≤ LinearMap.ker (g.comp f) := by
  intro x hx
  rw [LinearMap.mem_ker, LinearMap.comp_apply, hx, map_zero]

/-- A later observer cannot repair failure of tangent injectivity. -/
theorem serial_comp_not_injective (f : H →ₗ[ℝ] M) (g : M →ₗ[ℝ] N)
    (hf : ¬Function.Injective f) : ¬Function.Injective (g.comp f) := by
  intro hcomp
  apply hf
  intro x y hxy
  apply hcomp
  simp [LinearMap.comp_apply, hxy]

/-- Product tangent reporter for a finite or infinite observer family. -/
def productReporter {ι : Type*} {Mι : ι → Type*}
    [∀ i, AddCommGroup (Mι i)] [∀ i, Module ℝ (Mι i)]
    (f : ∀ i, H →ₗ[ℝ] Mι i) : H →ₗ[ℝ] (∀ i, Mι i) :=
  LinearMap.pi f

/-- Parallel infinitesimal reconstruction is exactly trivial intersection of reporter kernels. -/
theorem productReporter_injective_iff {ι : Type*} {Mι : ι → Type*}
    [∀ i, AddCommGroup (Mι i)] [∀ i, Module ℝ (Mι i)]
    (f : ∀ i, H →ₗ[ℝ] Mι i) :
    Function.Injective (productReporter f) ↔ (⨅ i, LinearMap.ker (f i)) = ⊥ := by
  have hker : LinearMap.ker (productReporter f) = ⨅ i, LinearMap.ker (f i) := by
    ext x
    simp [productReporter, LinearMap.mem_ker, funext_iff]
  rw [← LinearMap.ker_eq_bot, hker]

/-- Sharp countermodel: tangent injectivity need not be tangent equivalence. -/
def lineInclusion : ℝ →ₗ[ℝ] ℝ × ℝ where
  toFun x := (x, 0)
  map_add' x y := by ext <;> simp
  map_smul' c x := by ext <;> simp

theorem lineInclusion_injective : Function.Injective lineInclusion := by
  intro x y h
  exact congrArg Prod.fst h

theorem lineInclusion_not_surjective : ¬Function.Surjective lineInclusion := by
  rintro h
  obtain ⟨x, hx⟩ := h (0, 1)
  have := congrArg Prod.snd hx
  norm_num [lineInclusion] at this

end ObserverIrreversibility

section PolarFibre

open scoped InnerProduct

/-- Exact framed polar-fibre theorem, inherited from the cross-Gram formalization. -/
theorem framed_gram_fibre
    {𝕜 D W : Type*} [RCLike 𝕜]
    [NormedAddCommGroup D] [InnerProductSpace 𝕜 D]
    [NormedAddCommGroup W] [InnerProductSpace 𝕜 W]
    [FiniteDimensional 𝕜 D] [FiniteDimensional 𝕜 W]
    (T S : D →L[𝕜] W) :
    HilbertMetric.NomologicalCrossGram.gram T =
        HilbertMetric.NomologicalCrossGram.gram S ↔
      ∃ U : W ≃ₗᵢ[𝕜] W, ∀ x, U (T x) = S x :=
  HilbertMetric.NomologicalCrossGram.gram_eq_iff_exists_codomainUnitary T S

end PolarFibre

end HTGeometry.NomologicalHomotopyGeometry.MinimalLawLeadingJet
