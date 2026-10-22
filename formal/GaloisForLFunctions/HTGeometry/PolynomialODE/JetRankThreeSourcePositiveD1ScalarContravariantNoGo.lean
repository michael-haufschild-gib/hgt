import GaloisForLFunctions.HTGeometry.PolynomialODE.JetRankThreeSourcePositiveD1CyclicContravariantNoGo
import GaloisForLFunctions.HTGeometry.GammaPoleReciprocalBellGrading

/-!
# No scalar contravariant D1 carrier for the source-positive theta sl₂ action

An `E,F`-stable polynomial carrier is automatically stable under `H=[E,F]`. Every individual
polynomial has a finite adapted-weight decomposition, and the Cartan eigenvalues `2W` of its
components are distinct. Finite spectral extraction therefore forces every adapted component of a
carrier vector back into the carrier. Applied to the actual rank-three D1 polynomial, this removes
the grading hypothesis from the cyclic vacuum-string obstruction: no source-`sl₂`-stable polynomial
carrier containing D1 supports a positive scalar-contravariant form.

The result is purely algebraic. It uses neither numerical certificates nor finite-dimensionality,
topological closure, or an explicit coefficient expansion of D1.
-/

open Complex Real

namespace HTGeometry

noncomputable section

/-- Finite spectral extraction in an invariant submodule. If a finite sum of eigenvectors with
distinct eigenvalues belongs to an operator-invariant submodule, then every summand belongs to it. -/
theorem mem_of_finset_sum_mem_of_distinct_eigenvalues
    {𝕜 V ι : Type*} [Field 𝕜] [AddCommGroup V] [Module 𝕜 V]
    [DecidableEq ι]
    (U : Submodule 𝕜 V) (C : V →ₗ[𝕜] V)
    (hUinv : ∀ u : V, u ∈ U → C u ∈ U)
    (x : ι → V) (lam : ι → 𝕜)
    (hlam : Function.Injective lam)
    (hx : ∀ i, C (x i) = lam i • x i)
    (s : Finset ι) (hsum : (∑ i ∈ s, x i) ∈ U)
    {i₀ : ι} (hi₀ : i₀ ∈ s) : x i₀ ∈ U := by
  classical
  have key : ∀ S : Finset ι, i₀ ∉ S → ∀ c : ι → 𝕜,
      (x i₀ + ∑ i ∈ S, c i • x i) ∈ U → x i₀ ∈ U := by
    intro S
    induction S using Finset.induction_on with
    | empty =>
        intro _ c h
        simpa using h
    | insert j S' hj ih =>
        intro hi₀S c h
        have hi₀j : i₀ ≠ j := fun hc => hi₀S (hc ▸ Finset.mem_insert_self j S')
        have hi₀S' : i₀ ∉ S' := fun hc => hi₀S (Finset.mem_insert_of_mem hc)
        have hgap : lam i₀ - lam j ≠ 0 := sub_ne_zero.mpr (hlam.ne hi₀j)
        let w : V := x i₀ + ∑ i ∈ insert j S', c i • x i
        have hCw : C w =
            lam i₀ • x i₀ + ∑ i ∈ insert j S', (c i * lam i) • x i := by
          simp only [w, map_add, map_sum, hx, map_smul, smul_smul]
        have hcomb : C w - lam j • w =
            (lam i₀ - lam j) • x i₀ +
              ∑ i ∈ insert j S', (c i * (lam i - lam j)) • x i := by
          calc
            C w - lam j • w =
                (lam i₀ • x i₀ - lam j • x i₀) +
                  ((∑ i ∈ insert j S', (c i * lam i) • x i) -
                    lam j • (∑ i ∈ insert j S', c i • x i)) := by
              rw [hCw]
              simp only [w, smul_add]
              abel
            _ = (lam i₀ - lam j) • x i₀ +
                  ∑ i ∈ insert j S', (c i * (lam i - lam j)) • x i := by
              rw [sub_smul, Finset.smul_sum]
              simp_rw [smul_smul]
              rw [← Finset.sum_sub_distrib]
              congr 1
              refine Finset.sum_congr rfl fun i _ => ?_
              rw [← sub_smul]
              congr 1
              ring
        have hw : w ∈ U := h
        have hmem : (lam i₀ - lam j)⁻¹ • (C w - lam j • w) ∈ U :=
          U.smul_mem _ (U.sub_mem (hUinv w hw) (U.smul_mem _ hw))
        rw [hcomb, smul_add, Finset.smul_sum, smul_smul,
          inv_mul_cancel₀ hgap, one_smul, Finset.sum_insert hj] at hmem
        refine ih hi₀S' (fun i =>
          (lam i₀ - lam j)⁻¹ * (c i * (lam i - lam j))) ?_
        simpa only [smul_smul, sub_self, mul_zero, zero_smul, smul_zero,
          zero_add] using hmem
  refine key (s.erase i₀) (Finset.notMem_erase _ _) (fun _ => 1) ?_
  have hsplit : (∑ i ∈ s, x i) =
      x i₀ + ∑ i ∈ s.erase i₀, (1 : 𝕜) • x i := by
    simp only [one_smul]
    exact (Finset.add_sum_erase _ _ hi₀).symm
  rwa [hsplit] at hsum

/-- Cartan Lie derivative as a complex-linear operator. -/
def modularThetaSourcePositiveSl2HLinear :
    ModularThetaSourcePositivePolynomial →ₗ[ℂ]
      ModularThetaSourcePositivePolynomial where
  toFun := modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2H
  map_add' := modularThetaSourcePositiveFieldLie_add _
  map_smul' := modularThetaSourcePositiveFieldLie_smul _

/-- **Automatic adapted grading.** Every source-`E,F`-stable complex polynomial submodule contains
each adapted homogeneous component of each of its vectors. -/
theorem modularThetaSourcePositiveAdaptedComponent_mem_of_sl2EFInvariant
    (U : Submodule ℂ ModularThetaSourcePositivePolynomial)
    (hE : ∀ P : ModularThetaSourcePositivePolynomial, P ∈ U →
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E P ∈ U)
    (hF : ∀ P : ModularThetaSourcePositivePolynomial, P ∈ U →
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F P ∈ U)
    {P : ModularThetaSourcePositivePolynomial} (hP : P ∈ U) (W : ℕ) :
    modularThetaSourcePositiveAdaptedComponent W P ∈ U := by
  let Hlin := modularThetaSourcePositiveSl2HLinear
  have hH : ∀ Q : ModularThetaSourcePositivePolynomial, Q ∈ U → Hlin Q ∈ U := by
    intro Q hQ
    rw [show Hlin Q =
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2H Q by rfl]
    rw [← modularThetaSourcePositiveFieldLie_sl2_ef Q]
    exact U.sub_mem (hE _ (hF _ hQ)) (hF _ (hE _ hQ))
  let N := (modularThetaSourcePositiveToAdapted P).weightedTotalDegree
    modularThetaSourcePositiveAdaptedWeight
  by_cases hW : W ∈ Finset.range (N + 1)
  · let x : ℕ → ModularThetaSourcePositivePolynomial := fun n =>
      modularThetaSourcePositiveAdaptedComponent n P
    let lam : ℕ → ℂ := fun n => ((2 * n : ℕ) : ℂ)
    have hlam : Function.Injective lam := by
      intro a b hab
      change ((2 * a : ℕ) : ℂ) = ((2 * b : ℕ) : ℂ) at hab
      have hn : 2 * a = 2 * b := by exact_mod_cast hab
      omega
    have hx : ∀ n, Hlin (x n) = lam n • x n := by
      intro n
      change modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2H
          (modularThetaSourcePositiveAdaptedComponent n P) =
        ((2 * n : ℕ) : ℂ) •
          modularThetaSourcePositiveAdaptedComponent n P
      exact modularThetaSourcePositiveFieldLie_sl2H_of_adaptedHomogeneous
        (MvPolynomial.weightedHomogeneousComponent_mem
          modularThetaSourcePositiveAdaptedWeight
          (modularThetaSourcePositiveToAdapted P) n)
    have hsum : (∑ n ∈ Finset.range (N + 1), x n) = P := by
      have hadapted := GaloisForLFunctions.sum_weightedHomogeneousComponent_natRange
        modularThetaSourcePositiveAdaptedWeight
        (modularThetaSourcePositiveToAdapted P)
      have horiginal := congrArg modularThetaSourcePositiveOfAdapted hadapted
      simpa [x, N, modularThetaSourcePositiveAdaptedComponent,
        ← RingHom.comp_apply,
        modularThetaSourcePositiveOfAdapted_comp_toAdapted] using horiginal
    apply mem_of_finset_sum_mem_of_distinct_eigenvalues U Hlin hH x lam
      hlam hx (Finset.range (N + 1))
    · rwa [hsum]
    · exact hW
  · have hNW : N < W := by
      simp only [Finset.mem_range, Nat.lt_add_one_iff] at hW
      omega
    unfold modularThetaSourcePositiveAdaptedComponent
    rw [MvPolynomial.weightedHomogeneousComponent_eq_zero W
      (modularThetaSourcePositiveToAdapted P) hNW]
    simp

/-- Positive scalar-contravariant data on an arbitrary source-`sl₂`-stable polynomial carrier
containing actual D1. No grading assumption is included. -/
structure ModularThetaSourcePositiveD1ScalarContravariantCarrier
    (c : ℝ) where
  carrier : Submodule ℂ ModularThetaSourcePositivePolynomial
  d1_mem : modularThetaSourcePositiveReflectedEighthPolynomial ∈ carrier
  sl2E_mem : ∀ P : ModularThetaSourcePositivePolynomial,
    P ∈ carrier →
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E P ∈ carrier
  sl2F_mem : ∀ P : ModularThetaSourcePositivePolynomial,
    P ∈ carrier →
      modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F P ∈ carrier
  pair : ModularThetaSourcePositivePolynomial →
    ModularThetaSourcePositivePolynomial → ℂ
  smul_left : ∀ (a : ℂ) (p q : ModularThetaSourcePositivePolynomial),
    pair (a • p) q = star a * pair p q
  smul_right : ∀ (a : ℂ) (p q : ModularThetaSourcePositivePolynomial),
    pair p (a • q) = a * pair p q
  positive : ∀ p : ModularThetaSourcePositivePolynomial,
    p ∈ carrier → p ≠ 0 → 0 < (pair p p).re
  contravariant : ∀ p q : ModularThetaSourcePositivePolynomial,
    p ∈ carrier → q ∈ carrier →
      pair (modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2E p) q =
        pair p ((c : ℂ) •
          modularThetaSourcePositiveFieldLie modularThetaSourcePositiveSl2F q)

/-- **Unrestricted D1 scalar-form no-go.** No positive scalar-contravariant form exists on any
source-`sl₂`-stable polynomial carrier containing the actual rank-three D1 polynomial. -/
theorem modularThetaSourcePositive_no_D1_scalarContravariantCarrier :
    ¬ ∃ (c : ℝ), Nonempty
      (ModularThetaSourcePositiveD1ScalarContravariantCarrier c) := by
  rintro ⟨c, ⟨B⟩⟩
  apply modularThetaSourcePositive_no_D1_gradedScalarContravariantCarrier
  refine ⟨c, ⟨{
    carrier := B.carrier
    d1_mem := B.d1_mem
    adaptedComponent_mem := ?_
    sl2E_mem := B.sl2E_mem
    sl2F_mem := B.sl2F_mem
    pair := B.pair
    smul_left := B.smul_left
    smul_right := B.smul_right
    positive := B.positive
    contravariant := B.contravariant }⟩⟩
  intro W P hP
  exact modularThetaSourcePositiveAdaptedComponent_mem_of_sl2EFInvariant
    B.carrier B.sl2E_mem B.sl2F_mem hP W

end

end HTGeometry
