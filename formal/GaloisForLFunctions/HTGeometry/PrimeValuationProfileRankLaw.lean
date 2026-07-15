import GaloisForLFunctions.HTGeometry.PrimeValuationLeadingEchelon
import GaloisForLFunctions.HTGeometry.DifferentialPivotRelationIdeal
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# The prime-valuation profile rank law

Consider arithmetic functions supported on positive prime powers whose coefficient at `p^(n+1)`
depends only on the valuation index `n`, not on the prime `p`.  Such a source is encoded by its
valuation profile `u : ℕ → ℂ`.

For every finite family, differential algebraic independence under the rotated logarithmic
derivation is equivalent to ordinary linear independence of the valuation profiles.  Thus the
entire finite differential matroid of this infinite-tail class collapses exactly to the linear
matroid of sequences.  The forward direction uses a finite nonsingular evaluation minor of the
profiles; the reverse direction uses coefficient uniqueness and order-zero linear dependence.
-/

namespace GaloisForLFunctions.HTGeometry

open ArithmeticFunction Matrix
open scoped Differential BigOperators

noncomputable section

set_option maxHeartbeats 500000
set_option synthInstance.maxHeartbeats 80000

/-- A finite linearly independent family of scalar sequences has a nonsingular evaluation minor
on pairwise distinct natural coordinates. -/
theorem exists_injective_evaluation_minor_of_linearIndependent_profiles
    {d : ℕ} (u : Fin d → ℕ → ℂ) (hu : LinearIndependent ℂ u) :
    ∃ (e : Fin d → ℕ) (P : Matrix (Fin d) (Fin d) ℂ),
      Function.Injective e ∧ IsUnit P.det ∧
      ∀ r s, P r s = u s (e r) := by
  have hspan : Submodule.span ℂ (Set.range (flip u)) = ⊤ :=
    (span_flip_eq_top_iff_linearIndependent).2 hu
  obtain ⟨v, hvrange, _hvspan, hvLI⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℂ (Set.range (flip u))
  have hfinrank : Module.finrank ℂ
      (Submodule.span ℂ (Set.range (flip u))) = d := by
    rw [hspan]
    simp [Module.finrank_fintype_fun_eq_card]
  let E : Fin d ≃ Fin (Module.finrank ℂ
      (Submodule.span ℂ (Set.range (flip u)))) :=
    finCongr hfinrank.symm
  let w : Fin d → (Fin d → ℂ) := v ∘ E
  have hwrange : ∀ i, w i ∈ Set.range (flip u) := fun i => hvrange (E i)
  have hwLI : LinearIndependent ℂ w := hvLI.comp E E.injective
  choose e heval using hwrange
  have he : Function.Injective e := by
    intro i j hij
    apply hwLI.injective
    rw [← heval i, ← heval j, hij]
  let P : Matrix (Fin d) (Fin d) ℂ := Matrix.of fun r s => w r s
  have hProws : LinearIndependent ℂ P.row := by
    simpa only [P, Matrix.row, Matrix.of_apply] using hwLI
  obtain ⟨Q, hPQ⟩ := exists_matrix_rightInverse_of_linearIndependent_rows P hProws
  have hPdet : P.det ≠ 0 := Matrix.det_ne_zero_of_right_inverse hPQ
  refine ⟨e, P, he, isUnit_iff_ne_zero.mpr hPdet, ?_⟩
  intro r s
  change w r s = u s (e r)
  exact (congrFun (heval r) s).symm

/-- A profile relation forces the same linear relation among the full prime-power-supported
arithmetic sources. -/
theorem primeValuationProfile_relation_lifts
    {d : ℕ} (u : Fin d → ℕ → ℂ)
    (g : Fin d → ArithmeticFunction ℂ)
    (hsupport : ∀ r, SupportedOnPositivePrimePowers (g r))
    (hprofile : ∀ r (p : Nat.Primes) n,
      g r ((p : ℕ) ^ (n + 1)) = u r n)
    (z : Fin d → ℂ)
    (hz : ∑ r, z r • u r = 0) :
    ∑ r, z r • g r = 0 := by
  ext n
  let ev : ArithmeticFunction ℂ →+ ℂ :=
    { toFun := fun f => f n
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev (∑ r, z r • g r) = 0
  rw [map_sum]
  change (∑ r, z r * g r n) = 0
  by_cases hpow : ∃ (p : Nat.Primes) (k : ℕ), n = (p : ℕ) ^ (k + 1)
  · obtain ⟨p, k, rfl⟩ := hpow
    simp only [hprofile]
    have hzat := congrFun hz k
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] using hzat
  · apply Finset.sum_eq_zero
    intro r hr
    have hzero : g r n = 0 := by
      by_contra hne
      exact hpow (hsupport r hne)
    rw [hzero, mul_zero]

/-- **Prime-valuation profile rank law.**  For every finite nonempty family of prime-radial
positive-prime-power sources, differential independence is exactly linear independence of the
valuation profiles.  Equivalently, on this class the finite differential matroid is the ordinary
linear matroid of the profile sequences. -/
theorem primeValuationProfile_differentialIndependent_iff
    {d : ℕ} [Nonempty (Fin d)]
    (u : Fin d → ℕ → ℂ)
    (g : Fin d → ArithmeticFunction ℂ)
    (hsupport : ∀ r, SupportedOnPositivePrimePowers (g r))
    (hprofile : ∀ r (p : Nat.Primes) n,
      g r ((p : ℕ) ^ (n + 1)) = u r n) :
    GaloisForLFunctions.DifferentialIndependent ℂ
        (fun r => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (g r)) ↔
      LinearIndependent ℂ u := by
  constructor
  · intro hDI
    have hlin : LinearIndependent ℂ
        (fun r => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (g r)) :=
      hDI.algebraicIndependent.linearIndependent
    rw [Fintype.linearIndependent_iff] at hlin ⊢
    intro z hz r
    apply hlin z
    have hsource := primeValuationProfile_relation_lifts
      u g hsupport hprofile z hz
    let F : ArithmeticFunction ℂ →ₐ[ℂ] arithmeticFunctionFractionField :=
      IsScalarTower.toAlgHom ℂ (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField
    have hmapped := congrArg F hsource
    change ∑ i, z i • F (g i) = 0
    simpa only [map_sum, map_smul, _root_.map_zero] using hmapped
  · intro hu
    obtain ⟨e, P, he, hP, hPeval⟩ :=
      exists_injective_evaluation_minor_of_linearIndependent_profiles u hu
    apply primeValuationProfileMinor_differentialIndependent g e he P hP hsupport
    intro r s p
    rw [hprofile]
    exact (hPeval r s).symm

/-- Equality of valuation profiles lifts to equality of the complete prime-radial arithmetic
sources, including all infinitely many prime rays. -/
theorem primeValuationProfile_source_eq_linearCombination
    {d : ℕ} {R : Type*} [Fintype (Fin d)]
    (u : Fin d → ℕ → ℂ) (v : R → ℕ → ℂ)
    (g : Fin d → ArithmeticFunction ℂ) (y : R → ArithmeticFunction ℂ)
    (A : R → Fin d → ℂ)
    (hgsupport : ∀ b, SupportedOnPositivePrimePowers (g b))
    (hysupport : ∀ r, SupportedOnPositivePrimePowers (y r))
    (hgprofile : ∀ b (p : Nat.Primes) n,
      g b ((p : ℕ) ^ (n + 1)) = u b n)
    (hyprofile : ∀ r (p : Nat.Primes) n,
      y r ((p : ℕ) ^ (n + 1)) = v r n)
    (hv : ∀ r n, v r n = ∑ b, A r b * u b n)
    (r : R) :
    y r = ∑ b, A r b • g b := by
  ext n
  let ev : ArithmeticFunction ℂ →+ ℂ :=
    { toFun := fun f => f n
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change y r n = ev (∑ b, A r b • g b)
  rw [map_sum]
  change y r n = ∑ b, A r b * g b n
  by_cases hpow : ∃ (p : Nat.Primes) (k : ℕ), n = (p : ℕ) ^ (k + 1)
  · obtain ⟨p, k, rfl⟩ := hpow
    rw [hyprofile, hv]
    simp only [hgprofile]
  · have hyzero : y r n = 0 := by
      by_contra hne
      exact hpow (hysupport r hne)
    rw [hyzero]
    symm
    apply Finset.sum_eq_zero
    intro b hb
    have hgzero : g b n = 0 := by
      by_contra hne
      exact hpow (hgsupport b hne)
    rw [hgzero, mul_zero]

/-- **Complete prime-valuation profile relation law.**  Choose linearly independent pivot
profiles and express every remaining profile by a constant coefficient matrix.  The complete
differential relation ideal of all corresponding prime-radial sources is generated by exactly the
prolonged linear profile relations.  No extra nonlinear relation exists. -/
theorem primeValuationProfile_complete_relationIdeal
    {d : ℕ} [Nonempty (Fin d)] {R : Type*}
    (u : Fin d → ℕ → ℂ) (v : R → ℕ → ℂ)
    (g : Fin d → ArithmeticFunction ℂ) (y : R → ArithmeticFunction ℂ)
    (A : R → Fin d → ℂ)
    (hu : LinearIndependent ℂ u)
    (hgsupport : ∀ b, SupportedOnPositivePrimePowers (g b))
    (hysupport : ∀ r, SupportedOnPositivePrimePowers (y r))
    (hgprofile : ∀ b (p : Nat.Primes) n,
      g b ((p : ℕ) ^ (n + 1)) = u b n)
    (hyprofile : ∀ r (p : Nat.Primes) n,
      y r ((p : ℕ) ^ (n + 1)) = v r n)
    (hv : ∀ r n, v r n = ∑ b, A r b * u b n) :
    GaloisForLFunctions.differentialRelationIdeal (C := ℂ)
        (Sum.elim
          (fun b => algebraMap (ArithmeticFunction ℂ)
            arithmeticFunctionFractionField (g b))
          (fun r => algebraMap (ArithmeticFunction ℂ)
            arithmeticFunctionFractionField (y r))) =
      differentialPivotRelationIdeal A (fun _ _ => 0) := by
  let x : Fin d → arithmeticFunctionFractionField := fun b =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (g b)
  let z : R → arithmeticFunctionFractionField := fun r =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (y r)
  have hx : GaloisForLFunctions.DifferentialIndependent ℂ x :=
    (primeValuationProfile_differentialIndependent_iff
      u g hgsupport hgprofile).2 hu
  have hz : z = matrixLinearForms A x := by
    funext r
    have hsource := primeValuationProfile_source_eq_linearCombination
      u v g y A hgsupport hysupport hgprofile hyprofile hv r
    let F : ArithmeticFunction ℂ →ₐ[ℂ] arithmeticFunctionFractionField :=
      IsScalarTower.toAlgHom ℂ (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField
    have hmapped := congrArg F hsource
    change F (y r) = matrixLinearForms A (fun b => F (g b)) r
    simp only [matrixLinearForms, ← Algebra.smul_def]
    simpa only [map_sum, map_smul] using hmapped
  apply differentialRelationIdeal_sumElim_eq_pivot x z A (fun _ _ => 0) hx
  intro r n
  rw [show z r = matrixLinearForms A x r from congrFun hz r]
  rw [differentialJet_matrixLinearForms
    arithmeticFunctionFractionField_deriv_algebraMap_complex A x r n]
  simp [matrixLinearForms]

/-- The same profile presentation gives an exact differential-transcendence basis: adjoining all
dependent sources creates the same differential field as adjoining only the profile pivots. -/
theorem primeValuationProfile_differentialAdjoin_eq_pivots
    {d : ℕ} [Nonempty (Fin d)] {R : Type*}
    (u : Fin d → ℕ → ℂ) (v : R → ℕ → ℂ)
    (g : Fin d → ArithmeticFunction ℂ) (y : R → ArithmeticFunction ℂ)
    (A : R → Fin d → ℂ)
    (hgsupport : ∀ b, SupportedOnPositivePrimePowers (g b))
    (hysupport : ∀ r, SupportedOnPositivePrimePowers (y r))
    (hgprofile : ∀ b (p : Nat.Primes) n,
      g b ((p : ℕ) ^ (n + 1)) = u b n)
    (hyprofile : ∀ r (p : Nat.Primes) n,
      y r ((p : ℕ) ^ (n + 1)) = v r n)
    (hv : ∀ r n, v r n = ∑ b, A r b * u b n) :
    GaloisForLFunctions.differentialAdjoin ℂ
        (Set.range (Sum.elim
          (fun b => algebraMap (ArithmeticFunction ℂ)
            arithmeticFunctionFractionField (g b))
          (fun r => algebraMap (ArithmeticFunction ℂ)
            arithmeticFunctionFractionField (y r)))) =
      GaloisForLFunctions.differentialAdjoin ℂ
        (Set.range (fun b => algebraMap (ArithmeticFunction ℂ)
          arithmeticFunctionFractionField (g b))) := by
  let x : Fin d → arithmeticFunctionFractionField := fun b =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (g b)
  let z : R → arithmeticFunctionFractionField := fun r =>
    algebraMap (ArithmeticFunction ℂ) arithmeticFunctionFractionField (y r)
  have hz : z = matrixLinearForms A x := by
    funext r
    have hsource := primeValuationProfile_source_eq_linearCombination
      u v g y A hgsupport hysupport hgprofile hyprofile hv r
    let F : ArithmeticFunction ℂ →ₐ[ℂ] arithmeticFunctionFractionField :=
      IsScalarTower.toAlgHom ℂ (ArithmeticFunction ℂ)
        arithmeticFunctionFractionField
    have hmapped := congrArg F hsource
    change F (y r) = matrixLinearForms A (fun b => F (g b)) r
    simp only [matrixLinearForms, ← Algebra.smul_def]
    simpa only [map_sum, map_smul] using hmapped
  apply differentialAdjoin_sumElim_eq_left_of_affineJets
    x z A (fun _ _ => 0)
  intro r n
  rw [show z r = matrixLinearForms A x r from congrFun hz r]
  rw [differentialJet_matrixLinearForms
    arithmeticFunctionFractionField_deriv_algebraMap_complex A x r n]
  simp [matrixLinearForms]

end

end GaloisForLFunctions.HTGeometry
