import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerDilationFlow
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerPaugamSpectralPairing

/-!
# Flow-correct generalized Paugam jet pairing

A multiple zeta zero carries a triangular family of generalized Mellin jets.
Pairing only the top jet with its reflected top jet is alternating but is not
stable under dilation: translation mixes every lower jet into it.

This file derives the forced correction.  The order-`n` Paugam form is the
full binomial complementary-jet block

`Σ_{j=0}^n choose(n,j) (E_j(u) E_{n-j}(Jv) - E_j(v) E_{n-j}(Ju))`.

It is exactly the `n`-th derivative of the antisymmetrized product of two
faithful entire Mellin transforms.  Consequently it is alternating,
anti-invariant under simultaneous `J`, and transforms under simultaneous
dilation by the exact weight-one character `exp(c)`.  Boundary descent for
every constituent jet comes from the differentiated Poisson--zeta
factorization, so the form lives on actual all-weight Meyer cohomology.

No simplicity, semisimplicity, RH, trace, positivity, spectral decomposition,
or numerical premise occurs.
-/

open Complex Filter Function Set Topology
open scoped Classical

namespace RHTower

noncomputable section

def DeningerMeyerZetaZeroJetDatum.evaluationLE
    (d : DeningerMeyerZetaZeroJetDatum)
    (j : ℕ) (hj : j ≤ d.jetOrder) :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ :=
  deningerMeyerZetaZeroJetEvaluationLM
    d.point d.re_pos d.ne_one j
      (fun i hi => d.zeta_vanishing i (hi.trans hj))

@[simp]
theorem DeningerMeyerZetaZeroJetDatum.evaluationLE_mk
    (d : DeningerMeyerZetaZeroJetDatum)
    (j : ℕ) (hj : j ≤ d.jetOrder)
    (g : DeningerMeyerStrongLogTarget) :
    d.evaluationLE j hj (Submodule.Quotient.mk g) =
      deningerMeyerStrongLogMellinJetLM j d.point g :=
  rfl

private def deningerMeyerAlternatingProduct
    (a b : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ) :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ]
      DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ where
  toFun u :=
    { toFun := fun v => a u * b v - a v * b u
      map_add' := by
        intro v w
        simp only [LinearMap.map_add, mul_add, add_mul]
        ring
      map_smul' := by
        intro c v
        simp only [LinearMap.map_smul, RingHom.id_apply, smul_eq_mul]
        ring }
  map_add' := by
    intro u v
    apply LinearMap.ext
    intro w
    simp only [LinearMap.add_apply, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.map_add, add_mul, mul_add]
    ring
  map_smul' := by
    intro c u
    apply LinearMap.ext
    intro v
    simp only [LinearMap.smul_apply, LinearMap.coe_mk, AddHom.coe_mk,
      LinearMap.map_smul, RingHom.id_apply, smul_eq_mul]
    ring

private theorem deningerMeyerAlternatingProduct_apply
    (a b : DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ)
    (u v : DeningerMeyerStrongLogCohomology) :
    deningerMeyerAlternatingProduct a b u v =
      a u * b v - a v * b u :=
  rfl

/--
The full complementary-jet Paugam block.  Binomial coefficients are forced
by Leibniz differentiation of the antisymmetrized Mellin product.
-/
def deningerMeyerPaugamGeneralizedJetPairing
    (d : DeningerMeyerZetaZeroJetDatum) :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ]
      DeningerMeyerStrongLogCohomology →ₗ[ℂ] ℂ :=
  ∑ i : Fin (d.jetOrder + 1),
    (d.jetOrder.choose i : ℂ) •
      deningerMeyerAlternatingProduct
        (d.evaluationLE i
          (Nat.le_of_lt_succ i.isLt))
        ((d.evaluationLE (d.jetOrder - i)
          (Nat.sub_le _ _)).comp
            deningerMeyerStrongLogCohomologyJ)

theorem deningerMeyerPaugamGeneralizedJetPairing_apply
    (d : DeningerMeyerZetaZeroJetDatum)
    (u v : DeningerMeyerStrongLogCohomology) :
    deningerMeyerPaugamGeneralizedJetPairing d u v =
      ∑ i : Fin (d.jetOrder + 1),
        (d.jetOrder.choose i : ℂ) *
          (d.evaluationLE i
                (Nat.le_of_lt_succ i.isLt) u *
              d.evaluationLE (d.jetOrder - i)
                (Nat.sub_le _ _)
                (deningerMeyerStrongLogCohomologyJ v) -
            d.evaluationLE i
                (Nat.le_of_lt_succ i.isLt) v *
              d.evaluationLE (d.jetOrder - i)
                (Nat.sub_le _ _)
                (deningerMeyerStrongLogCohomologyJ u)) := by
  rw [deningerMeyerPaugamGeneralizedJetPairing]
  rw [LinearMap.sum_apply, LinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [LinearMap.smul_apply, LinearMap.smul_apply,
    smul_eq_mul, deningerMeyerAlternatingProduct_apply]
  rfl

@[simp]
theorem deningerMeyerPaugamGeneralizedJetPairing_self
    (d : DeningerMeyerZetaZeroJetDatum)
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerPaugamGeneralizedJetPairing d u u = 0 := by
  rw [deningerMeyerPaugamGeneralizedJetPairing_apply]
  apply Finset.sum_eq_zero
  intro i _
  ring

theorem deningerMeyerPaugamGeneralizedJetPairing_skew
    (d : DeningerMeyerZetaZeroJetDatum)
    (u v : DeningerMeyerStrongLogCohomology) :
    deningerMeyerPaugamGeneralizedJetPairing d u v =
      -deningerMeyerPaugamGeneralizedJetPairing d v u := by
  rw [deningerMeyerPaugamGeneralizedJetPairing_apply,
    deningerMeyerPaugamGeneralizedJetPairing_apply,
    ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Antisymmetrized Mellin product whose highest derivative is the full jet block. -/
def deningerMeyerPaugamMellinProduct
    (g h : DeningerMeyerStrongLogTarget) (s : ℂ) : ℂ :=
  deningerMeyerStrongLogMellin g s *
      deningerMeyerStrongLogMellin
        (deningerMeyerStrongLogJ h) s -
    deningerMeyerStrongLogMellin h s *
      deningerMeyerStrongLogMellin
        (deningerMeyerStrongLogJ g) s

@[simp]
theorem deningerMeyerPaugamMellinProduct_J
    (g h : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerPaugamMellinProduct
        (deningerMeyerStrongLogJ g)
        (deningerMeyerStrongLogJ h) s =
      -deningerMeyerPaugamMellinProduct g h s := by
  unfold deningerMeyerPaugamMellinProduct
  simp only [deningerMeyerStrongLogJ_sq]
  ring

theorem deningerMeyerPaugamGeneralizedJetPairing_mk
    (d : DeningerMeyerZetaZeroJetDatum)
    (g h : DeningerMeyerStrongLogTarget) :
    deningerMeyerPaugamGeneralizedJetPairing d
        (Submodule.Quotient.mk g)
        (Submodule.Quotient.mk h) =
      iteratedDeriv d.jetOrder
        (deningerMeyerPaugamMellinProduct g h) d.point := by
  rw [deningerMeyerPaugamGeneralizedJetPairing_apply]
  simp only [
    DeningerMeyerZetaZeroJetDatum.evaluationLE_mk,
    deningerMeyerStrongLogCohomologyJ_mk,
    deningerMeyerStrongLogMellinJetLM_eq_iteratedDeriv]
  rw [Fin.sum_univ_eq_sum_range
    (fun i : ℕ =>
      (d.jetOrder.choose i : ℂ) *
        (iteratedDeriv i
              (deningerMeyerStrongLogMellin g) d.point *
            iteratedDeriv (d.jetOrder - i)
              (deningerMeyerStrongLogMellin
                (deningerMeyerStrongLogJ h)) d.point -
          iteratedDeriv i
              (deningerMeyerStrongLogMellin h) d.point *
            iteratedDeriv (d.jetOrder - i)
              (deningerMeyerStrongLogMellin
                (deningerMeyerStrongLogJ g)) d.point))
    (d.jetOrder + 1)]
  have hg :
      ContDiffAt ℂ (d.jetOrder : WithTop ℕ∞)
        (deningerMeyerStrongLogMellin g) d.point :=
    (analyticOnNhd_deningerMeyerStrongLogMellin
      g.property d.point (Set.mem_univ _)).contDiffAt
  have hh :
      ContDiffAt ℂ (d.jetOrder : WithTop ℕ∞)
        (deningerMeyerStrongLogMellin h) d.point :=
    (analyticOnNhd_deningerMeyerStrongLogMellin
      h.property d.point (Set.mem_univ _)).contDiffAt
  have hJg :
      ContDiffAt ℂ (d.jetOrder : WithTop ℕ∞)
        (deningerMeyerStrongLogMellin
          (deningerMeyerStrongLogJ g)) d.point :=
    (analyticOnNhd_deningerMeyerStrongLogMellin
      (deningerMeyerStrongLogJ g).property
      d.point (Set.mem_univ _)).contDiffAt
  have hJh :
      ContDiffAt ℂ (d.jetOrder : WithTop ℕ∞)
        (deningerMeyerStrongLogMellin
          (deningerMeyerStrongLogJ h)) d.point :=
    (analyticOnNhd_deningerMeyerStrongLogMellin
      (deningerMeyerStrongLogJ h).property
      d.point (Set.mem_univ _)).contDiffAt
  unfold deningerMeyerPaugamMellinProduct
  change
    _ =
      iteratedDeriv d.jetOrder
        ((deningerMeyerStrongLogMellin g *
            deningerMeyerStrongLogMellin
              (deningerMeyerStrongLogJ h)) -
          (deningerMeyerStrongLogMellin h *
            deningerMeyerStrongLogMellin
              (deningerMeyerStrongLogJ g)))
        d.point
  symm
  calc
    iteratedDeriv d.jetOrder
          ((deningerMeyerStrongLogMellin g *
              deningerMeyerStrongLogMellin
                (deningerMeyerStrongLogJ h)) -
            (deningerMeyerStrongLogMellin h *
              deningerMeyerStrongLogMellin
                (deningerMeyerStrongLogJ g)))
          d.point =
        iteratedDeriv d.jetOrder
            (deningerMeyerStrongLogMellin g *
              deningerMeyerStrongLogMellin
                (deningerMeyerStrongLogJ h)) d.point -
          iteratedDeriv d.jetOrder
            (deningerMeyerStrongLogMellin h *
              deningerMeyerStrongLogMellin
                (deningerMeyerStrongLogJ g)) d.point :=
      iteratedDeriv_sub (hg.mul hJh) (hh.mul hJg)
    _ =
        (∑ i ∈ Finset.range (d.jetOrder + 1),
          (d.jetOrder.choose i : ℂ) *
            iteratedDeriv i
              (deningerMeyerStrongLogMellin g) d.point *
            iteratedDeriv (d.jetOrder - i)
              (deningerMeyerStrongLogMellin
                (deningerMeyerStrongLogJ h)) d.point) -
        ∑ i ∈ Finset.range (d.jetOrder + 1),
          (d.jetOrder.choose i : ℂ) *
            iteratedDeriv i
              (deningerMeyerStrongLogMellin h) d.point *
            iteratedDeriv (d.jetOrder - i)
              (deningerMeyerStrongLogMellin
                (deningerMeyerStrongLogJ g)) d.point := by
      rw [iteratedDeriv_mul hg hJh,
        iteratedDeriv_mul hh hJg]
    _ =
        ∑ i ∈ Finset.range (d.jetOrder + 1),
          (d.jetOrder.choose i : ℂ) *
            (iteratedDeriv i
                (deningerMeyerStrongLogMellin g) d.point *
              iteratedDeriv (d.jetOrder - i)
                (deningerMeyerStrongLogMellin
                  (deningerMeyerStrongLogJ h)) d.point -
            iteratedDeriv i
                (deningerMeyerStrongLogMellin h) d.point *
              iteratedDeriv (d.jetOrder - i)
                (deningerMeyerStrongLogMellin
                  (deningerMeyerStrongLogJ g)) d.point) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

theorem deningerMeyerPaugamGeneralizedJetPairing_J
    (d : DeningerMeyerZetaZeroJetDatum)
    (u v : DeningerMeyerStrongLogCohomology) :
    deningerMeyerPaugamGeneralizedJetPairing d
        (deningerMeyerStrongLogCohomologyJ u)
        (deningerMeyerStrongLogCohomologyJ v) =
      -deningerMeyerPaugamGeneralizedJetPairing d u v := by
  induction u using Submodule.Quotient.induction_on with
  | _ g =>
      induction v using Submodule.Quotient.induction_on with
      | _ h =>
          simp only [
            deningerMeyerStrongLogCohomologyJ_mk]
          rw [
            deningerMeyerPaugamGeneralizedJetPairing_mk,
            deningerMeyerPaugamGeneralizedJetPairing_mk]
          have hfun :
              deningerMeyerPaugamMellinProduct
                  (deningerMeyerStrongLogJ g)
                  (deningerMeyerStrongLogJ h) =
                -deningerMeyerPaugamMellinProduct g h := by
            funext s
            exact deningerMeyerPaugamMellinProduct_J g h s
          rw [hfun, iteratedDeriv_neg]

/--
The antisymmetrized entire Mellin product has exact Paugam weight one under
simultaneous dilation.
-/
theorem deningerMeyerPaugamMellinProduct_flow
    (c : ℝ) (g h : DeningerMeyerStrongLogTarget) (s : ℂ) :
    deningerMeyerPaugamMellinProduct
        (deningerMeyerStrongLogFlow c g)
        (deningerMeyerStrongLogFlow c h) s =
      (Real.exp c : ℂ) *
        deningerMeyerPaugamMellinProduct g h s := by
  unfold deningerMeyerPaugamMellinProduct
  rw [deningerMeyerStrongLogMellin_flow,
    deningerMeyerStrongLogMellin_flow,
    deningerMeyerStrongLogJ_flow,
    deningerMeyerStrongLogJ_flow]
  have hJg :
      deningerMeyerStrongLogMellin
          (((Real.exp c : ℂ) •
            deningerMeyerStrongLogFlow (-c)
              (deningerMeyerStrongLogJ g)) :
                DeningerMeyerStrongLogTarget) s =
        (Real.exp c : ℂ) *
          deningerMeyerStrongLogMellin
            (deningerMeyerStrongLogFlow (-c)
              (deningerMeyerStrongLogJ g)) s := by
    change
      deningerMeyerStrongLogMellinLM s
          ((Real.exp c : ℂ) •
            deningerMeyerStrongLogFlow (-c)
              (deningerMeyerStrongLogJ g)) =
        (Real.exp c : ℂ) *
          deningerMeyerStrongLogMellinLM s
            (deningerMeyerStrongLogFlow (-c)
              (deningerMeyerStrongLogJ g))
    simpa only [smul_eq_mul] using
      (deningerMeyerStrongLogMellinLM s).map_smul
        (Real.exp c : ℂ)
        (deningerMeyerStrongLogFlow (-c)
          (deningerMeyerStrongLogJ g))
  have hJh :
      deningerMeyerStrongLogMellin
          (((Real.exp c : ℂ) •
            deningerMeyerStrongLogFlow (-c)
              (deningerMeyerStrongLogJ h)) :
                DeningerMeyerStrongLogTarget) s =
        (Real.exp c : ℂ) *
          deningerMeyerStrongLogMellin
            (deningerMeyerStrongLogFlow (-c)
              (deningerMeyerStrongLogJ h)) s := by
    change
      deningerMeyerStrongLogMellinLM s
          ((Real.exp c : ℂ) •
            deningerMeyerStrongLogFlow (-c)
              (deningerMeyerStrongLogJ h)) =
        (Real.exp c : ℂ) *
          deningerMeyerStrongLogMellinLM s
            (deningerMeyerStrongLogFlow (-c)
              (deningerMeyerStrongLogJ h))
    simpa only [smul_eq_mul] using
      (deningerMeyerStrongLogMellinLM s).map_smul
        (Real.exp c : ℂ)
        (deningerMeyerStrongLogFlow (-c)
          (deningerMeyerStrongLogJ h))
  rw [hJg, hJh,
    deningerMeyerStrongLogMellin_flow,
    deningerMeyerStrongLogMellin_flow]
  have hcancel :
      Complex.exp (s * (c : ℂ)) *
          Complex.exp (s * ((-c : ℝ) : ℂ)) = 1 := by
    rw [← Complex.exp_add]
    convert Complex.exp_zero
    push_cast
    ring
  calc
    Complex.exp (s * (c : ℂ)) *
          deningerMeyerStrongLogMellin g s *
          ((Real.exp c : ℂ) *
            (Complex.exp (s * ((-c : ℝ) : ℂ)) *
              deningerMeyerStrongLogMellin
                (deningerMeyerStrongLogJ h) s)) -
        Complex.exp (s * (c : ℂ)) *
          deningerMeyerStrongLogMellin h s *
          ((Real.exp c : ℂ) *
            (Complex.exp (s * ((-c : ℝ) : ℂ)) *
              deningerMeyerStrongLogMellin
                (deningerMeyerStrongLogJ g) s)) =
      (Real.exp c : ℂ) *
        (Complex.exp (s * (c : ℂ)) *
          Complex.exp (s * ((-c : ℝ) : ℂ))) *
        (deningerMeyerStrongLogMellin g s *
            deningerMeyerStrongLogMellin
              (deningerMeyerStrongLogJ h) s -
          deningerMeyerStrongLogMellin h s *
            deningerMeyerStrongLogMellin
              (deningerMeyerStrongLogJ g) s) := by
      ring
    _ = _ := by rw [hcancel]; ring

theorem iteratedDeriv_deningerMeyerPaugamMellinProduct_flow
    (c : ℝ) (g h : DeningerMeyerStrongLogTarget)
    (n : ℕ) (s : ℂ) :
    iteratedDeriv n
        (deningerMeyerPaugamMellinProduct
          (deningerMeyerStrongLogFlow c g)
          (deningerMeyerStrongLogFlow c h)) s =
      (Real.exp c : ℂ) *
        iteratedDeriv n
          (deningerMeyerPaugamMellinProduct g h) s := by
  have hfun :
      deningerMeyerPaugamMellinProduct
          (deningerMeyerStrongLogFlow c g)
          (deningerMeyerStrongLogFlow c h) =
        fun z : ℂ =>
          (Real.exp c : ℂ) *
            deningerMeyerPaugamMellinProduct g h z := by
    funext z
    exact deningerMeyerPaugamMellinProduct_flow c g h z
  rw [hfun, iteratedDeriv_const_mul_field]

/--
**Exact generalized Paugam weight-one law.**  The full complementary-jet
block, unlike a top-jet-only determinant, is equivariant under simultaneous
dilation with weight `exp(c)`.
-/
theorem deningerMeyerPaugamGeneralizedJetPairing_flow
    (d : DeningerMeyerZetaZeroJetDatum)
    (c : ℝ)
    (u v : DeningerMeyerStrongLogCohomology) :
    deningerMeyerPaugamGeneralizedJetPairing d
        (deningerMeyerStrongLogCohomologyFlow c u)
        (deningerMeyerStrongLogCohomologyFlow c v) =
      (Real.exp c : ℂ) *
        deningerMeyerPaugamGeneralizedJetPairing d u v := by
  induction u using Submodule.Quotient.induction_on with
  | _ g =>
      induction v using Submodule.Quotient.induction_on with
      | _ h =>
          simp only [
            deningerMeyerStrongLogCohomologyFlow_mk,
            deningerMeyerPaugamGeneralizedJetPairing_mk]
          exact
            iteratedDeriv_deningerMeyerPaugamMellinProduct_flow
              c g h d.jetOrder d.point

end

end RHTower
