import GaloisForLFunctions.HTGeometry.RealFiniteAnalyticEscape
import GaloisForLFunctions.HTGeometry.ValuatedSpectralCharacterLaw
import Mathlib.Analysis.Analytic.Polynomial
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Countable separable-interaction saturation

Every projective spectral relation has finite support, even when the
ambient pure-point spectrum is countably infinite.  This file exploits
that local finiteness with a two-parameter geometric interaction.

For injections `codeA : A → ℕ` and `codeB : B → ℕ`, the interaction
coordinate `(i,j)` receives the distinct bivariate monomial

`s ^ (codeA i + 1) * t ^ (codeB j + 1)`.

Consequently each nonzero finitely supported relation is a nonzero real
polynomial in `(s,t)`.  Baire avoidance supplies one arbitrarily small
parameter pair escaping all countably many relations simultaneously.
The resulting factor sequences are summable.  Thus a single separable
interaction with summable diagonal factors makes every finite spectral
window maximally projective, for arbitrary countable input spectra and
without simplicity, boundedness, or arithmetic assumptions on their
energies.
-/

open Set Topology
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Exponent vector distinguishing one product-spectrum coordinate. -/
def geometricSeparableMonomialIndex
    {A B : Type*} (codeA : A → ℕ) (codeB : B → ℕ)
    (x : A × B) : Fin 2 →₀ ℕ :=
  Finsupp.single 0 (codeA x.1 + 1) +
    Finsupp.single 1 (codeB x.2 + 1)

theorem geometricSeparableMonomialIndex_injective
    {A B : Type*} {codeA : A → ℕ} {codeB : B → ℕ}
    (hA : Function.Injective codeA) (hB : Function.Injective codeB) :
    Function.Injective (geometricSeparableMonomialIndex codeA codeB) := by
  intro x y hxy
  have h0 := congrArg (fun q : Fin 2 →₀ ℕ => q 0) hxy
  have h1 := congrArg (fun q : Fin 2 →₀ ℕ => q 1) hxy
  simp [geometricSeparableMonomialIndex] at h0 h1
  have hx : x.1 = y.1 := by
    apply hA
    omega
  have hy : x.2 = y.2 := by
    apply hB
    omega
  exact Prod.ext hx hy

def geometricSeparableRelationPolynomial
    {A B : Type*}
    (left : A → ℝ) (right : B → ℝ)
    (codeA : A → ℕ) (codeB : B → ℕ)
    (k : ProjectiveCharacter (A × B)) :
    MvPolynomial (Fin 2) ℝ :=
  ∑ x ∈ k.1.support, (
    MvPolynomial.monomial 0
        ((k.1 x : ℝ) * (left x.1 + right x.2)) +
      MvPolynomial.monomial
        (geometricSeparableMonomialIndex codeA codeB x) (k.1 x : ℝ))

theorem coeff_geometricSeparableRelationPolynomial
    {A B : Type*}
    (left : A → ℝ) (right : B → ℝ)
    (codeA : A → ℕ) (codeB : B → ℕ)
    (hA : Function.Injective codeA) (hB : Function.Injective codeB)
    (k : ProjectiveCharacter (A × B)) (x : A × B) :
    MvPolynomial.coeff
        (geometricSeparableMonomialIndex codeA codeB x)
        (geometricSeparableRelationPolynomial left right codeA codeB k) =
      (k.1 x : ℝ) := by
  classical
  unfold geometricSeparableRelationPolynomial
  rw [MvPolynomial.coeff_sum]
  have hindexZero :
      geometricSeparableMonomialIndex codeA codeB x ≠ 0 := by
    intro h
    have h0 := congrArg (fun q : Fin 2 →₀ ℕ => q 0) h
    simp [geometricSeparableMonomialIndex] at h0
  by_cases hx : x ∈ k.1.support
  · rw [Finset.sum_eq_single x]
    · rw [MvPolynomial.coeff_add,
        MvPolynomial.coeff_monomial, if_neg hindexZero.symm,
        MvPolynomial.coeff_monomial, if_pos rfl,
        zero_add]
    · intro y hy hyx
      have hindex : geometricSeparableMonomialIndex codeA codeB y ≠
          geometricSeparableMonomialIndex codeA codeB x := by
        intro h
        exact hyx (geometricSeparableMonomialIndex_injective hA hB h)
      rw [MvPolynomial.coeff_add,
        MvPolynomial.coeff_monomial, if_neg hindexZero.symm,
        MvPolynomial.coeff_monomial, if_neg hindex,
        zero_add]
    · intro hnot
      exact (hnot hx).elim
  · have hkx : k.1 x = 0 := Finsupp.notMem_support_iff.mp hx
    rw [hkx]
    simp only [Int.cast_zero]
    rw [Finset.sum_eq_zero]
    intro y hy
    have hyx : y ≠ x := by
      intro h
      subst y
      exact hx hy
    have hindex : geometricSeparableMonomialIndex codeA codeB y ≠
        geometricSeparableMonomialIndex codeA codeB x := by
      intro h
      exact hyx (geometricSeparableMonomialIndex_injective hA hB h)
    rw [MvPolynomial.coeff_add,
      MvPolynomial.coeff_monomial, if_neg hindexZero.symm,
      MvPolynomial.coeff_monomial, if_neg hindex,
      zero_add]

theorem geometricSeparableRelationPolynomial_ne_zero
    {A B : Type*}
    (left : A → ℝ) (right : B → ℝ)
    (codeA : A → ℕ) (codeB : B → ℕ)
    (hA : Function.Injective codeA) (hB : Function.Injective codeB)
    (k : ProjectiveCharacter (A × B)) (hk : k ≠ 0) :
    geometricSeparableRelationPolynomial left right codeA codeB k ≠ 0 := by
  obtain ⟨x, hx⟩ : ∃ x, k.1 x ≠ 0 := by
    by_contra h
    push Not at h
    apply hk
    apply Subtype.ext
    exact Finsupp.ext h
  intro hzero
  have hcoeff := coeff_geometricSeparableRelationPolynomial
    left right codeA codeB hA hB k x
  rw [hzero, MvPolynomial.coeff_zero] at hcoeff
  exact hx (Int.cast_eq_zero.mp hcoeff.symm)

def geometricSeparableInteractionEnergy
    {A B : Type*}
    (left : A → ℝ) (right : B → ℝ)
    (codeA : A → ℕ) (codeB : B → ℕ)
    (p : Fin 2 → ℝ) (x : A × B) : ℝ :=
  left x.1 + right x.2 +
    p 0 ^ (codeA x.1 + 1) * p 1 ^ (codeB x.2 + 1)

def geometricSeparableRelationResponse
    {A B : Type*}
    (left : A → ℝ) (right : B → ℝ)
    (codeA : A → ℕ) (codeB : B → ℕ)
    (k : ProjectiveCharacter (A × B))
    (p : Fin 2 → ℝ) : ℝ :=
  ∑ x ∈ k.1.support,
    (k.1 x : ℝ) *
      geometricSeparableInteractionEnergy left right codeA codeB p x

theorem eval_geometricSeparableRelationPolynomial
    {A B : Type*}
    (left : A → ℝ) (right : B → ℝ)
    (codeA : A → ℕ) (codeB : B → ℕ)
    (k : ProjectiveCharacter (A × B))
    (p : Fin 2 → ℝ) :
    MvPolynomial.eval p
        (geometricSeparableRelationPolynomial left right codeA codeB k) =
      geometricSeparableRelationResponse left right codeA codeB k p := by
  classical
  simp [geometricSeparableRelationPolynomial,
    geometricSeparableRelationResponse,
    geometricSeparableInteractionEnergy,
    geometricSeparableMonomialIndex,
    MvPolynomial.eval_monomial]
  apply Finset.sum_congr rfl
  intro x hx
  ring

theorem analyticOnNhd_geometricSeparableRelationResponse
    {A B : Type*}
    (left : A → ℝ) (right : B → ℝ)
    (codeA : A → ℕ) (codeB : B → ℕ)
    (k : ProjectiveCharacter (A × B)) :
    AnalyticOnNhd ℝ
      (geometricSeparableRelationResponse left right codeA codeB k)
      Set.univ := by
  have hfun :
      geometricSeparableRelationResponse left right codeA codeB k =
        fun p => MvPolynomial.eval p
          (geometricSeparableRelationPolynomial left right codeA codeB k) := by
    funext p
    exact (eval_geometricSeparableRelationPolynomial
      left right codeA codeB k p).symm
  rw [hfun]
  exact AnalyticOnNhd.eval_mvPolynomial _

/-- Coded version of simultaneous relation erasure for countable spectra. -/
theorem exists_small_geometricSeparableInteraction_relationFree_coded
    {A B : Type*} [Countable A] [Countable B]
    (left : A → ℝ) (right : B → ℝ)
    (codeA : A → ℕ) (codeB : B → ℕ)
    (hA : Function.Injective codeA) (hB : Function.Injective codeB)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ p : Fin 2 → ℝ,
      (∀ k : ProjectiveCharacter (A × B), k ≠ 0 →
        geometricSeparableRelationResponse left right codeA codeB k p ≠ 0) ∧
      (∀ x : A × B,
        |p 0 ^ (codeA x.1 + 1) * p 1 ^ (codeB x.2 + 1)| < δ) ∧
      |p 0| < 1 ∧ |p 1| < 1 := by
  classical
  let ε : ℝ := min 1 δ
  have hε : 0 < ε := lt_min zero_lt_one hδ
  let I := {k : ProjectiveCharacter (A × B) // k ≠ 0}
  let U : Set (Fin 2 → ℝ) := Metric.ball 0 ε
  let f : I → (Fin 2 → ℝ) → ℝ := fun j p =>
    MvPolynomial.eval p
      (geometricSeparableRelationPolynomial left right codeA codeB j.1)
  have hUopen : IsOpen U := Metric.isOpen_ball
  have hUconnected : IsPreconnected U :=
    (convex_ball (0 : Fin 2 → ℝ) ε).isPreconnected
  have hUnonempty : U.Nonempty := by
    refine ⟨0, ?_⟩
    simpa [U] using hε
  have hf : ∀ j : I, AnalyticOnNhd ℝ (f j) U := by
    intro j
    exact (AnalyticOnNhd.eval_mvPolynomial _).mono (Set.subset_univ U)
  have hne : ∀ j : I, ∃ p ∈ U, f j p ≠ 0 := by
    intro j
    have hpoly :
        geometricSeparableRelationPolynomial left right codeA codeB j.1 ≠ 0 :=
      geometricSeparableRelationPolynomial_ne_zero
        left right codeA codeB hA hB j.1 j.2
    have hglobal : ∃ p : Fin 2 → ℝ, f j p ≠ 0 := by
      by_contra hall
      push Not at hall
      apply hpoly
      apply MvPolynomial.funext
      intro p
      simpa [f] using hall p
    obtain ⟨q, hqU, hqne⟩ :=
      exists_mem_neZero_of_analyticOnNhd_real
        (AnalyticOnNhd.eval_mvPolynomial
          (geometricSeparableRelationPolynomial left right codeA codeB j.1))
        isPreconnected_univ
        ⟨Classical.choose hglobal, Set.mem_univ _, Classical.choose_spec hglobal⟩
        hUopen hUnonempty (Set.subset_univ U)
    exact ⟨q, hqU, by simpa [f] using hqne⟩
  obtain ⟨p, hpU, hpAll⟩ :=
    exists_forall_neZero_of_countable_analyticOnNhd_real_local
      f U hUopen hUconnected hUnonempty hf hne
  have hpNorm : ‖p‖ < ε := by
    simpa [U, Metric.mem_ball, dist_zero_right] using hpU
  have hpCoordinate : ∀ i : Fin 2, |p i| < ε := by
    intro i
    have hi := (pi_norm_lt_iff hε).mp hpNorm i
    simpa [Real.norm_eq_abs] using hi
  refine ⟨p, ?_, ?_, ?_, ?_⟩
  · intro k hk
    have h := hpAll (⟨k, hk⟩ : I)
    change MvPolynomial.eval p
      (geometricSeparableRelationPolynomial left right codeA codeB k) ≠ 0 at h
    rw [eval_geometricSeparableRelationPolynomial] at h
    exact h
  · intro x
    have hp0 := hpCoordinate 0
    have hp1 := hpCoordinate 1
    have hεone : ε ≤ 1 := min_le_left _ _
    have hεδ : ε ≤ δ := min_le_right _ _
    have hp0one : |p 0| ≤ 1 := hp0.le.trans hεone
    have hp1one : |p 1| ≤ 1 := hp1.le.trans hεone
    have hpow0 : |p 0| ^ codeA x.1 ≤ 1 :=
      pow_le_one₀ (abs_nonneg _) hp0one
    have hpow1 : |p 1| ^ codeB x.2 ≤ 1 :=
      pow_le_one₀ (abs_nonneg _) hp1one
    have hleft : |p 0| ^ codeA x.1 * |p 0| ≤ |p 0| :=
      mul_le_of_le_one_left (abs_nonneg _) hpow0
    have hright : |p 1| ^ codeB x.2 * |p 1| ≤ |p 1| :=
      mul_le_of_le_one_left (abs_nonneg _) hpow1
    have hbase : |p 0| * |p 1| < δ := by
      nlinarith [abs_nonneg (p 0), abs_nonneg (p 1)]
    calc
      |p 0 ^ (codeA x.1 + 1) * p 1 ^ (codeB x.2 + 1)| =
          (|p 0| ^ codeA x.1 * |p 0|) *
            (|p 1| ^ codeB x.2 * |p 1|) := by
              rw [abs_mul, abs_pow, abs_pow, pow_succ, pow_succ]
      _ ≤ |p 0| * |p 1| := by
        exact mul_le_mul hleft hright
          (mul_nonneg (pow_nonneg (abs_nonneg _) _) (abs_nonneg _))
          (abs_nonneg _)
      _ < δ := hbase
  · exact (hpCoordinate 0).trans_le (min_le_left _ _)
  · exact (hpCoordinate 1).trans_le (min_le_left _ _)

/-- Every finitely supported balanced integer relation is trivial. -/
def FinitelySupportedMaximallyProjectiveEnergy
    {I : Type*} (energy : I → ℝ) : Prop :=
  ∀ k : ProjectiveCharacter I,
    (∑ i ∈ k.1.support, (k.1 i : ℝ) * energy i) = 0 → k = 0

/-- **Countable weak-interaction saturation.** Every pair of countable
spectra admits an arbitrarily small separable interaction that erases every
finitely supported nonzero projective spectral relation at once. -/
theorem exists_smallSeparableInteraction_finitelySupportedMaximallyProjective
    {A B : Type*} [Countable A] [Countable B]
    (left : A → ℝ) (right : B → ℝ)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ u : A → ℝ, ∃ v : B → ℝ,
      Summable (fun i => |u i|) ∧
      Summable (fun j => |v j|) ∧
      Summable (fun x : A × B => |u x.1 * v x.2|) ∧
      (∀ x : A × B, |u x.1 * v x.2| < δ) ∧
      FinitelySupportedMaximallyProjectiveEnergy
        (fun x : A × B =>
          left x.1 + right x.2 + u x.1 * v x.2) := by
  classical
  letI : Encodable A := Encodable.ofCountable A
  letI : Encodable B := Encodable.ofCountable B
  let codeA : A → ℕ := Encodable.encode
  let codeB : B → ℕ := Encodable.encode
  obtain ⟨p, hrelations, hsmall, hp0, hp1⟩ :=
    exists_small_geometricSeparableInteraction_relationFree_coded
      left right codeA codeB Encodable.encode_injective
        Encodable.encode_injective δ hδ
  let u : A → ℝ := fun i => p 0 ^ (codeA i + 1)
  let v : B → ℝ := fun j => p 1 ^ (codeB j + 1)
  refine ⟨u, v, ?_, ?_, ?_, ?_, ?_⟩
  · have hinj : Function.Injective (fun i : A => codeA i + 1) := by
      intro i j h
      exact Encodable.encode_injective (Nat.add_right_cancel h)
    have hsum :=
      (summable_geometric_of_lt_one (abs_nonneg (p 0)) hp0).comp_injective hinj
    apply hsum.congr
    intro i
    simp [u, abs_pow]
  · have hinj : Function.Injective (fun j : B => codeB j + 1) := by
      intro i j h
      exact Encodable.encode_injective (Nat.add_right_cancel h)
    have hsum :=
      (summable_geometric_of_lt_one (abs_nonneg (p 1)) hp1).comp_injective hinj
    apply hsum.congr
    intro j
    simp [v, abs_pow]
  · have hu : Summable (fun i : A => |u i|) := by
      have hinj : Function.Injective (fun i : A => codeA i + 1) := by
        intro i j h
        exact Encodable.encode_injective (Nat.add_right_cancel h)
      have hsum :=
        (summable_geometric_of_lt_one (abs_nonneg (p 0)) hp0).comp_injective hinj
      apply hsum.congr
      intro i
      simp [u, abs_pow]
    have hv : Summable (fun j : B => |v j|) := by
      have hinj : Function.Injective (fun j : B => codeB j + 1) := by
        intro i j h
        exact Encodable.encode_injective (Nat.add_right_cancel h)
      have hsum :=
        (summable_geometric_of_lt_one (abs_nonneg (p 1)) hp1).comp_injective hinj
      apply hsum.congr
      intro j
      simp [v, abs_pow]
    simpa [abs_mul] using
      hu.mul_of_nonneg hv (fun _ => abs_nonneg _) (fun _ => abs_nonneg _)
  · intro x
    exact hsmall x
  · intro k hzero
    by_contra hk
    apply hrelations k hk
    simpa [geometricSeparableRelationResponse,
      geometricSeparableInteractionEnergy, u, v] using hzero

/-- Maximal projective freedom survives restriction to every embedded
subsystem.  In particular, one countable saturation witness controls all
finite spectral windows simultaneously. -/
theorem FinitelySupportedMaximallyProjectiveEnergy.comp_embedding
    {I J : Type*} {energy : I → ℝ}
    (hmax : FinitelySupportedMaximallyProjectiveEnergy energy)
    (e : J ↪ I) :
    FinitelySupportedMaximallyProjectiveEnergy (energy ∘ e) := by
  intro k hzero
  let raw : I →₀ ℤ := k.1.embDomain e
  have hcharge : integerCharacterCharge I raw = 0 := by
    change raw.sum (fun _ m => m) = 0
    rw [Finsupp.sum_embDomain]
    exact k.2
  let K : ProjectiveCharacter I := ⟨raw, hcharge⟩
  have hKzero : K = 0 := by
    apply hmax K
    change (∑ i ∈ raw.support, (raw i : ℝ) * energy i) = 0
    rw [Finsupp.support_embDomain]
    rw [Finset.sum_map]
    simpa [raw, Function.comp_apply] using hzero
  apply Subtype.ext
  apply Finsupp.embDomain_injective e
  exact congrArg Subtype.val hKzero

end

end GaloisForLFunctions.HTGeometry
