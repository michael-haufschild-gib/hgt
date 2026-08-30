import GaloisForLFunctions.HTGeometry.AnalyticGermRing

/-!
# Gohberg--Sigal covariant-family index rigidity

For a holomorphic operator family on an arbitrary complex normed space, local characteristic
multiplicity is modeled as complex length of its analytic-germ cokernel. Holomorphic invertible
left and right factors act by explicit equivalences of analytic-vector-germ modules, so they
preserve this length. Iterating deck covariance makes every window index equal and forces the
stack sum to be stack size times base index.
-/

noncomputable section

namespace GaloisForLFunctions.RHTower.GohbergSigalCovariantIndexRigidity

open Filter Topology
open GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

local instance gohbergSigalCovariantIndexRigidityLocalInst1 : IsScalarTower ℂ (H →L[ℂ] H) H where
  smul_assoc _ _ _ := rfl

local instance gohbergSigalCovariantIndexRigidityLocalInst2 : IsBoundedSMul (H →L[ℂ] H) H where
  dist_smul_pair' A x y := by
    change dist (A x) (A y) ≤ dist A 0 * dist x y
    simpa only [dist_eq_norm, sub_zero, map_sub] using A.le_opNorm (x - y)
  dist_pair_smul' A B x := by
    change dist (A x) (B x) ≤ dist A B * dist x 0
    simpa only [dist_eq_norm, sub_zero, sub_apply] using (A - B).le_opNorm x

def analyticVectorGermSubmodule (p : ℂ) :
    Submodule (AnalyticGerm p) (Germ (nhds p) H) where
  carrier := {g | ∃ f : ℂ → H, AnalyticAt ℂ f p ∧ (f : Germ (nhds p) H) = g}
  zero_mem' := ⟨0, analyticAt_const, rfl⟩
  add_mem' := by
    rintro a b ⟨f, hf, rfl⟩ ⟨g, hg, rfl⟩
    exact ⟨f + g, hf.add hg, rfl⟩
  smul_mem' := by
    intro c x hx
    rcases c with ⟨a, ⟨f, hf, hfa⟩⟩
    rcases hx with ⟨g, hg, hgx⟩
    subst a
    subst x
    exact ⟨f • g, hf.smul hg, rfl⟩

abbrev AnalyticVectorGerm (p : ℂ) (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H] :=
  {x // x ∈ analyticVectorGermSubmodule (H := H) p}

def complexToAnalyticGerm (p : ℂ) : ℂ →+* AnalyticGerm p where
  toFun c := analyticGermOf (p := p) (f := fun _ : ℂ => c) analyticAt_const
  map_one' := by apply Subtype.ext; rfl
  map_mul' _ _ := by apply Subtype.ext; rfl
  map_zero' := by apply Subtype.ext; rfl
  map_add' _ _ := by apply Subtype.ext; rfl

noncomputable instance analyticVectorGermModuleComplex (p : ℂ) :
    Module ℂ (AnalyticVectorGerm p H) :=
  Module.compHom (AnalyticVectorGerm p H) (complexToAnalyticGerm p)

theorem germOperator_smul_comm (p : ℂ) (c : Germ (nhds p) ℂ)
    (A : Germ (nhds p) (H →L[ℂ] H)) (v : Germ (nhds p) H) :
    A • (c • v) = c • (A • v) := by
  refine Filter.Germ.inductionOn₃ c A v fun cf Af vf => ?_
  apply Germ.coe_eq.mpr
  filter_upwards with z
  exact (Af z).map_smul (cf z) (vf z)

def germOperatorLinearMap (p : ℂ) (A : Germ (nhds p) (H →L[ℂ] H)) :
    Germ (nhds p) H →ₗ[Germ (nhds p) ℂ] Germ (nhds p) H where
  toFun v := A • v
  map_add' v w := by
    refine Filter.Germ.inductionOn₃ A v w fun Af vf wf => ?_
    apply Germ.coe_eq.mpr
    filter_upwards with z
    exact (Af z).map_add (vf z) (wf z)
  map_smul' c v := by
    refine Filter.Germ.inductionOn₃ c A v fun cf Af vf => ?_
    apply Germ.coe_eq.mpr
    filter_upwards with z
    exact (Af z).map_smul (cf z) (vf z)

def analyticOperatorGermMap (p : ℂ) {A : ℂ → H →L[ℂ] H}
    (hA : AnalyticAt ℂ A p) :
    AnalyticVectorGerm p H →ₗ[AnalyticGerm p] AnalyticVectorGerm p H where
  toFun v := ⟨(A : Germ (nhds p) (H →L[ℂ] H)) • v.1, by
    rcases v.2 with ⟨f, hf, hfv⟩
    refine ⟨A • f, hA.smul hf, ?_⟩
    rw [← hfv]
    rfl⟩
  map_add' v w := by
    apply Subtype.ext
    exact (germOperatorLinearMap p (A : Germ (nhds p) (H →L[ℂ] H))).map_add v.1 w.1
  map_smul' c v := by
    apply Subtype.ext
    exact germOperator_smul_comm p c.1 (A : Germ (nhds p) (H →L[ℂ] H)) v.1

theorem analyticOperatorGermMap_mul (p : ℂ)
    {A B : ℂ → H →L[ℂ] H} (hA : AnalyticAt ℂ A p) (hB : AnalyticAt ℂ B p) :
    analyticOperatorGermMap p (hA.mul hB) =
      (analyticOperatorGermMap p hA).comp (analyticOperatorGermMap p hB) := by
  ext v
  change ((A * B : ℂ → H →L[ℂ] H) : Germ (nhds p) (H →L[ℂ] H)) • v.1 =
    (A : Germ (nhds p) (H →L[ℂ] H)) •
      ((B : Germ (nhds p) (H →L[ℂ] H)) • v.1)
  refine Filter.Germ.inductionOn v.1 fun vf => ?_
  apply Germ.coe_eq.mpr
  filter_upwards with z
  rfl

theorem analyticOperatorGermMap_congr (p : ℂ)
    {A B : ℂ → H →L[ℂ] H} (hA : AnalyticAt ℂ A p) (hB : AnalyticAt ℂ B p)
    (hAB : A =ᶠ[nhds p] B) :
    analyticOperatorGermMap p hA = analyticOperatorGermMap p hB := by
  ext v
  change (A : Germ (nhds p) (H →L[ℂ] H)) • v.1 =
    (B : Germ (nhds p) (H →L[ℂ] H)) • v.1
  refine Filter.Germ.inductionOn v.1 fun vf => ?_
  apply Germ.coe_eq.mpr
  filter_upwards [hAB] with z hz
  rw [hz]

def analyticOperatorGermEquiv (p : ℂ)
    {E Ei : ℂ → H →L[ℂ] H} (hE : AnalyticAt ℂ E p) (hEi : AnalyticAt ℂ Ei p)
    (hleft : Ei * E =ᶠ[nhds p] 1) (hright : E * Ei =ᶠ[nhds p] 1) :
    AnalyticVectorGerm p H ≃ₗ[AnalyticGerm p] AnalyticVectorGerm p H where
  toFun := analyticOperatorGermMap p hE
  invFun := analyticOperatorGermMap p hEi
  map_add' := (analyticOperatorGermMap p hE).map_add
  map_smul' := (analyticOperatorGermMap p hE).map_smul
  left_inv v := by
    apply Subtype.ext
    change (Ei : Germ (nhds p) (H →L[ℂ] H)) •
      ((E : Germ (nhds p) (H →L[ℂ] H)) • v.1) = v.1
    refine Filter.Germ.inductionOn v.1 fun vf => ?_
    apply Germ.coe_eq.mpr
    filter_upwards [hleft] with z hz
    exact congrArg (fun T : H →L[ℂ] H => T (vf z)) hz
  right_inv v := by
    apply Subtype.ext
    change (E : Germ (nhds p) (H →L[ℂ] H)) •
      ((Ei : Germ (nhds p) (H →L[ℂ] H)) • v.1) = v.1
    refine Filter.Germ.inductionOn v.1 fun vf => ?_
    apply Germ.coe_eq.mpr
    filter_upwards [hright] with z hz
    exact congrArg (fun T : H →L[ℂ] H => T (vf z)) hz

def cokernelEquivOfCompEquiv
    {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]
    (A : M →ₗ[R] M) (e f : M ≃ₗ[R] M) :
    (M ⧸ A.range) ≃ₗ[R]
      (M ⧸ (e.toLinearMap.comp (A.comp f.toLinearMap)).range) :=
  Submodule.Quotient.equiv A.range
    (e.toLinearMap.comp (A.comp f.toLinearMap)).range e (by
      ext y
      constructor
      · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
        refine ⟨f.symm u, ?_⟩
        simp
      · rintro ⟨x, rfl⟩
        refine ⟨A (f x), ⟨f x, rfl⟩, rfl⟩)

def cokernelFinrankVia
    {S R M : Type*} [DivisionRing S] [Ring R] [AddCommGroup M] [Module R M]
    (phi : S →+* R) (A : M →ₗ[R] M) : ℕ := by
  let Q := M ⧸ A.range
  letI : Module S Q := Module.compHom Q phi
  exact Module.finrank S Q

theorem cokernelFinrankVia_comp_equiv
    {S R M : Type*} [DivisionRing S] [Ring R] [AddCommGroup M] [Module R M]
    (phi : S →+* R) (A : M →ₗ[R] M) (e f : M ≃ₗ[R] M) :
    cokernelFinrankVia phi (e.toLinearMap.comp (A.comp f.toLinearMap)) =
      cokernelFinrankVia phi A := by
  let Q := M ⧸ A.range
  let Q' := M ⧸ (e.toLinearMap.comp (A.comp f.toLinearMap)).range
  letI : Module S Q := Module.compHom Q phi
  letI : Module S Q' := Module.compHom Q' phi
  let qR : Q ≃ₗ[R] Q' := cokernelEquivOfCompEquiv A e f
  let qS : Q ≃ₗ[S] Q' :=
    { toEquiv := qR.toEquiv
      map_add' := qR.map_add
      map_smul' := fun c x => qR.map_smul (phi c) x }
  exact qS.finrank_eq.symm

/-- Gohberg--Sigal local multiplicity as the complex length of the analytic-germ cokernel. -/
noncomputable def gohbergSigalLocalMultiplicity (p : ℂ)
    {A : ℂ → H →L[ℂ] H} (hA : AnalyticAt ℂ A p) : ℕ :=
  cokernelFinrankVia (complexToAnalyticGerm p) (analyticOperatorGermMap p hA)

theorem gohbergSigalLocalMultiplicity_congr (p : ℂ)
    {A B : ℂ → H →L[ℂ] H} (hA : AnalyticAt ℂ A p) (hB : AnalyticAt ℂ B p)
    (hAB : A =ᶠ[nhds p] B) :
    gohbergSigalLocalMultiplicity p hA = gohbergSigalLocalMultiplicity p hB := by
  unfold gohbergSigalLocalMultiplicity
  rw [analyticOperatorGermMap_congr p hA hB hAB]

theorem gohbergSigalLocalMultiplicity_mul_equiv (p : ℂ)
    {A E Ei F Fi : ℂ → H →L[ℂ] H}
    (hA : AnalyticAt ℂ A p) (hE : AnalyticAt ℂ E p) (hEi : AnalyticAt ℂ Ei p)
    (hF : AnalyticAt ℂ F p) (hFi : AnalyticAt ℂ Fi p)
    (hEleft : Ei * E =ᶠ[nhds p] 1) (hEright : E * Ei =ᶠ[nhds p] 1)
    (hFleft : Fi * F =ᶠ[nhds p] 1) (hFright : F * Fi =ᶠ[nhds p] 1) :
    gohbergSigalLocalMultiplicity p ((hE.mul hA).mul hF) =
      gohbergSigalLocalMultiplicity p hA := by
  unfold gohbergSigalLocalMultiplicity
  rw [analyticOperatorGermMap_mul p (hE.mul hA) hF,
    analyticOperatorGermMap_mul p hE hA]
  exact cokernelFinrankVia_comp_equiv (complexToAnalyticGerm p)
    (analyticOperatorGermMap p hA)
    (analyticOperatorGermEquiv p hE hEi hEleft hEright)
    (analyticOperatorGermEquiv p hF hFi hFleft hFright)

/-- A local holomorphic left-right equivalence between two operator-family germs. -/
structure AnalyticFredholmEquivalenceStep (p : ℂ)
    (A B : ℂ → H →L[ℂ] H) where
  E : ℂ → H →L[ℂ] H
  Ei : ℂ → H →L[ℂ] H
  F : ℂ → H →L[ℂ] H
  Fi : ℂ → H →L[ℂ] H
  analytic_E : AnalyticAt ℂ E p
  analytic_Ei : AnalyticAt ℂ Ei p
  analytic_F : AnalyticAt ℂ F p
  analytic_Fi : AnalyticAt ℂ Fi p
  E_left : Ei * E =ᶠ[nhds p] 1
  E_right : E * Ei =ᶠ[nhds p] 1
  F_left : Fi * F =ᶠ[nhds p] 1
  F_right : F * Fi =ᶠ[nhds p] 1
  covariance : B =ᶠ[nhds p] (E * A) * F

theorem AnalyticFredholmEquivalenceStep.localMultiplicity_eq
    {p : ℂ} {A B : ℂ → H →L[ℂ] H}
    (step : AnalyticFredholmEquivalenceStep p A B)
    (hA : AnalyticAt ℂ A p) (hB : AnalyticAt ℂ B p) :
    gohbergSigalLocalMultiplicity p hB = gohbergSigalLocalMultiplicity p hA := by
  calc
    gohbergSigalLocalMultiplicity p hB =
        gohbergSigalLocalMultiplicity p
          ((step.analytic_E.mul hA).mul step.analytic_F) :=
      gohbergSigalLocalMultiplicity_congr p hB
        ((step.analytic_E.mul hA).mul step.analytic_F) step.covariance
    _ = gohbergSigalLocalMultiplicity p hA :=
      gohbergSigalLocalMultiplicity_mul_equiv p hA step.analytic_E step.analytic_Ei
        step.analytic_F step.analytic_Fi step.E_left step.E_right step.F_left step.F_right

theorem gohbergSigalLocalMultiplicity_eq_base_of_covariant_steps
    (p : ℂ) (A : ℕ → ℂ → H →L[ℂ] H) (n : ℕ)
    (hA : ∀ j, AnalyticAt ℂ (A j) p)
    (hstep : ∀ j < n, AnalyticFredholmEquivalenceStep p (A j) (A (j + 1))) :
    ∀ j ≤ n,
      gohbergSigalLocalMultiplicity p (hA j) =
        gohbergSigalLocalMultiplicity p (hA 0) := by
  intro j hj
  induction j with
  | zero => rfl
  | succ j ih =>
      calc
        gohbergSigalLocalMultiplicity p (hA (j + 1)) =
            gohbergSigalLocalMultiplicity p (hA j) :=
          (hstep j (Nat.lt_of_succ_le hj)).localMultiplicity_eq (hA j) (hA (j + 1))
        _ = gohbergSigalLocalMultiplicity p (hA 0) := ih (Nat.le_of_succ_le hj)

/-- Summing all `n+1` covariant windows gives exactly `(n+1)` times the base multiplicity. -/
theorem gohbergSigalStackMultiplicity_eq_mul
    (p : ℂ) (A : ℕ → ℂ → H →L[ℂ] H) (n : ℕ)
    (hA : ∀ j, AnalyticAt ℂ (A j) p)
    (hstep : ∀ j < n, AnalyticFredholmEquivalenceStep p (A j) (A (j + 1))) :
    (∑ j : Fin (n + 1), gohbergSigalLocalMultiplicity p (hA j)) =
      (n + 1) * gohbergSigalLocalMultiplicity p (hA 0) := by
  classical
  have hconst : ∀ j : Fin (n + 1),
      gohbergSigalLocalMultiplicity p (hA j) =
        gohbergSigalLocalMultiplicity p (hA 0) := by
    intro j
    exact gohbergSigalLocalMultiplicity_eq_base_of_covariant_steps
      p A n hA hstep j (Nat.le_of_lt_succ j.isLt)
  simp_rw [hconst]
  simp

def translatedOperatorFamily (A : ℂ → H →L[ℂ] H) (δ : ℂ) (j : ℕ) :
    ℂ → H →L[ℂ] H := fun z => A (z + (j : ℂ) * δ)

theorem analyticAt_translatedOperatorFamily
    {A : ℂ → H →L[ℂ] H} {p δ : ℂ} (j : ℕ)
    (hA : AnalyticAt ℂ A (p + (j : ℂ) * δ)) :
    AnalyticAt ℂ (translatedOperatorFamily A δ j) p := by
  have hshift : AnalyticAt ℂ (fun z : ℂ => z + (j : ℂ) * δ) p :=
    analyticAt_id.add analyticAt_const
  have hcomp := hA.comp (f := fun z : ℂ => z + (j : ℂ) * δ) hshift
  change AnalyticAt ℂ (A ∘ fun z : ℂ => z + (j : ℂ) * δ) p
  exact hcomp

/-- Exact shifted-window form of T3: covariance at every deck step forces equal local index on
every translate and total stack multiplicity equal to stack size times the base value. -/
theorem shiftedCovariantGohbergSigalStack_eq_mul
    (A : ℂ → H →L[ℂ] H) (p δ : ℂ) (n : ℕ)
    (hA : ∀ j : ℕ, AnalyticAt ℂ A (p + (j : ℂ) * δ))
    (hstep : ∀ j < n, AnalyticFredholmEquivalenceStep p
      (translatedOperatorFamily A δ j) (translatedOperatorFamily A δ (j + 1))) :
    (∑ j : Fin (n + 1), gohbergSigalLocalMultiplicity p
      (analyticAt_translatedOperatorFamily j (hA j))) =
      (n + 1) * gohbergSigalLocalMultiplicity p
        (analyticAt_translatedOperatorFamily (A := A) (p := p) (δ := δ) 0
          (by simpa using hA 0)) := by
  exact gohbergSigalStackMultiplicity_eq_mul p
    (fun j => translatedOperatorFamily A δ j) n
    (fun j => analyticAt_translatedOperatorFamily j (hA j)) hstep

/-- Full finite characteristic-value support: after summing local Smith lengths in every window,
the total over an `(n+1)`-window covariant stack is `(n+1)` times the base-window index. -/
theorem shiftedCovariantGohbergSigalFiniteWindowStack_eq_mul
    {ι : Type*} [Fintype ι] (rho : ι → ℂ)
    (A : ℂ → H →L[ℂ] H) (δ : ℂ) (n : ℕ)
    (hA : ∀ q, ∀ j : ℕ, AnalyticAt ℂ A (rho q + (j : ℂ) * δ))
    (hstep : ∀ q, ∀ j < n, AnalyticFredholmEquivalenceStep (rho q)
      (translatedOperatorFamily A δ j) (translatedOperatorFamily A δ (j + 1))) :
    (∑ j : Fin (n + 1), ∑ q : ι, gohbergSigalLocalMultiplicity (rho q)
      (analyticAt_translatedOperatorFamily j (hA q j))) =
      (n + 1) * (∑ q : ι, gohbergSigalLocalMultiplicity (rho q)
        (analyticAt_translatedOperatorFamily (A := A) (p := rho q) (δ := δ) 0
          (by simpa using hA q 0))) := by
  classical
  rw [Finset.sum_comm]
  calc
    ∑ q : ι, ∑ j : Fin (n + 1), gohbergSigalLocalMultiplicity (rho q)
        (analyticAt_translatedOperatorFamily j (hA q j)) =
        ∑ q : ι, (n + 1) * gohbergSigalLocalMultiplicity (rho q)
          (analyticAt_translatedOperatorFamily (A := A) (p := rho q) (δ := δ) 0
            (by simpa using hA q 0)) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact shiftedCovariantGohbergSigalStack_eq_mul A (rho q) δ n
        (hA q) (hstep q)
    _ = (n + 1) * (∑ q : ι, gohbergSigalLocalMultiplicity (rho q)
          (analyticAt_translatedOperatorFamily (A := A) (p := rho q) (δ := δ) 0
            (by simpa using hA q 0))) := by
      rw [Finset.mul_sum]

/-- Closed universal capstone for holomorphic-cocycle covariance rigidity. -/
theorem covariantFamilyIndexRigidity_unconditional :
    ∀ (H : Type) [NormedAddCommGroup H] [NormedSpace ℂ H]
      (A : ℂ → H →L[ℂ] H) (p δ : ℂ) (n : ℕ)
      (hA : ∀ j : ℕ, AnalyticAt ℂ A (p + (j : ℂ) * δ)),
      (∀ j < n, AnalyticFredholmEquivalenceStep p
        (translatedOperatorFamily A δ j) (translatedOperatorFamily A δ (j + 1))) →
      (∑ j : Fin (n + 1), gohbergSigalLocalMultiplicity p
        (analyticAt_translatedOperatorFamily j (hA j))) =
        (n + 1) * gohbergSigalLocalMultiplicity p
          (analyticAt_translatedOperatorFamily (A := A) (p := p) (δ := δ) 0
            (by simpa using hA 0)) := by
  intro H _ _ A p δ n hA hstep
  exact shiftedCovariantGohbergSigalStack_eq_mul A p δ n hA hstep

end GaloisForLFunctions.RHTower.GohbergSigalCovariantIndexRigidity
