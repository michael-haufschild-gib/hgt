import GaloisForLFunctions.HTGeometry.SiegelMeroFieldDependence
import GaloisForLFunctions.HTGeometry.SeveralVariableDirectionalDifferential

/-!
# The noncompact period-quotient law for several-variable meromorphic germs

A constant directional derivation commutes with every translation, so all the jets of an element of
the several-variable meromorphic field share its periods.  If the quotient by the period group were
compact, Siegel's bound would make `n + 2` of those jets algebraically dependent over `ℂ`, that is,
would make the element differentially algebraic.  Contrapositive: a hypertranscendental element has
a noncompact period quotient in every dimension.

Together with the closedness of the period group and the complex linearity of its identity
component this is the whole period-escape package: `isEscapeSubgroup_meroPeriodSubgroupGen` needed
exactly this missing clause.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher Filter Set
open scoped Differential

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- **Translation commutes with the directional derivative of a scalar function.** -/
theorem dirDerivFun_comp_add (w h : E) {f : E → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ) :
    dirDerivFun w (fun z => f (z + h)) = fun z => dirDerivFun w f (z + h) := by
  funext z
  show fderiv ℂ (fun v => f (v + h)) z w = fderiv ℂ f (z + h) w
  have hdiff : Differentiable ℂ f := fun v => (hf v (Set.mem_univ v)).differentiableAt
  have hshift : HasFDerivAt (fun v : E => v + h) (ContinuousLinearMap.id ℂ E) z :=
    (hasFDerivAt_id z).add_const h
  have hcomp : HasFDerivAt (fun v : E => f (v + h))
      ((fderiv ℂ f (z + h)).comp (ContinuousLinearMap.id ℂ E)) z :=
    (hdiff (z + h)).hasFDerivAt.comp z hshift
  rw [hcomp.fderiv]
  rfl

/-- **Translation commutes with the directional derivation of the analytic germ ring.** -/
theorem addTranslationAnalyticEquivGen_dirDeriv (h w : E)
    (a : analyticSubringGen (Set.univ : Set E)) :
    addTranslationAnalyticEquivGen h
        (analyticSubringGenDirDeriv w (isOpen_univ (X := E)) a)
      = analyticSubringGenDirDeriv w (isOpen_univ (X := E))
        (addTranslationAnalyticEquivGen h a) := by
  obtain ⟨A, hA, hAa⟩ := a.2
  refine Subtype.ext ?_
  have hcoe : ((analyticSubringGenDirDeriv w (isOpen_univ (X := E)) a :
      analyticSubringGen (Set.univ : Set E)) : Germ (𝓟 (Set.univ : Set E)) ℂ)
      = Germ.coeRingHom (𝓟 (Set.univ : Set E)) (dirDerivFun w A) := by
    rw [analyticSubringGenDirDeriv_coe, ← hAa]
    rfl
  have hleft : ((addTranslationAnalyticEquivGen h
      (analyticSubringGenDirDeriv w (isOpen_univ (X := E)) a) :
        analyticSubringGen (Set.univ : Set E)) : Germ (𝓟 (Set.univ : Set E)) ℂ)
      = Germ.coeRingHom (𝓟 (Set.univ : Set E)) (fun z => dirDerivFun w A (z + h)) :=
    (addTranslationAnalyticEquivGen_rep h hcoe.symm).symm
  have hright : ((analyticSubringGenDirDeriv w (isOpen_univ (X := E))
      (addTranslationAnalyticEquivGen h a) : analyticSubringGen (Set.univ : Set E)) :
        Germ (𝓟 (Set.univ : Set E)) ℂ)
      = Germ.coeRingHom (𝓟 (Set.univ : Set E)) (dirDerivFun w (fun z => A (z + h))) := by
    rw [analyticSubringGenDirDeriv_coe, ← addTranslationAnalyticEquivGen_rep h hAa]
    rfl
  rw [hleft, hright, dirDerivFun_comp_add w h hA]

/-- Translation commutes with the derivation on the image of the analytic germ ring. -/
theorem addTranslationMeroEquivGen_dirDeriv_algebraMap (h w : E)
    (a : analyticSubringGen (Set.univ : Set E)) :
    letI := Bottcher.isDomain_analyticSubringGen (Set.univ : Set E) isOpen_univ
      isPreconnected_univ_gen Set.univ_nonempty
    letI := meroFieldGenDirDifferential w (isOpen_univ (X := E)) isPreconnected_univ_gen
      Set.univ_nonempty
    addTranslationMeroEquivGen h
        ((algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen (Set.univ : Set E))
          a)′)
      = (addTranslationMeroEquivGen h
          (algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen (Set.univ : Set E))
            a))′ := by
  letI := Bottcher.isDomain_analyticSubringGen (Set.univ : Set E) isOpen_univ
    isPreconnected_univ_gen Set.univ_nonempty
  letI := meroFieldGenDirDifferential w (isOpen_univ (X := E)) isPreconnected_univ_gen
    Set.univ_nonempty
  rw [meroFieldGenDirDifferential_algebraMap w (isOpen_univ (X := E)) isPreconnected_univ_gen
      Set.univ_nonempty, addTranslationMeroEquivGen_algebraMap,
    addTranslationMeroEquivGen_algebraMap,
    meroFieldGenDirDifferential_algebraMap w (isOpen_univ (X := E)) isPreconnected_univ_gen
      Set.univ_nonempty, addTranslationAnalyticEquivGen_dirDeriv h w a]

/-- **Translation commutes with the directional derivation of the meromorphic field.** -/
theorem addTranslationMeroEquivGen_dirDeriv (h w : E)
    (x : meroFieldGen (Set.univ : Set E)) :
    letI := Bottcher.isDomain_analyticSubringGen (Set.univ : Set E) isOpen_univ
      isPreconnected_univ_gen Set.univ_nonempty
    letI := meroFieldGenDirDifferential w (isOpen_univ (X := E)) isPreconnected_univ_gen
      Set.univ_nonempty
    addTranslationMeroEquivGen h (x′) = (addTranslationMeroEquivGen h x)′ := by
  letI := Bottcher.isDomain_analyticSubringGen (Set.univ : Set E) isOpen_univ
    isPreconnected_univ_gen Set.univ_nonempty
  letI := meroFieldGenDirDifferential w (isOpen_univ (X := E)) isPreconnected_univ_gen
    Set.univ_nonempty
  obtain ⟨a, b, hb, hxab⟩ :=
    IsFractionRing.div_surjective (A := analyticSubringGen (Set.univ : Set E))
      (K := meroFieldGen (Set.univ : Set E)) x
  have hbne : algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen (Set.univ : Set E))
      b ≠ 0 := by
    intro hzero
    exact nonZeroDivisors.ne_zero hb
      (IsFractionRing.injective (analyticSubringGen (Set.univ : Set E))
        (meroFieldGen (Set.univ : Set E)) (by rw [hzero, map_zero]))
  set α := algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen (Set.univ : Set E)) a
    with hαdef
  set β := algebraMap (analyticSubringGen (Set.univ : Set E)) (meroFieldGen (Set.univ : Set E)) b
    with hβdef
  have hA := addTranslationMeroEquivGen_dirDeriv_algebraMap h w a
  have hB := addTranslationMeroEquivGen_dirDeriv_algebraMap h w b
  have hL : addTranslationMeroEquivGen h ((α / β)′)
      = (addTranslationMeroEquivGen h β)⁻¹ ^ 2
        * ((addTranslationMeroEquivGen h β) * (addTranslationMeroEquivGen h α)′
          - (addTranslationMeroEquivGen h α) * (addTranslationMeroEquivGen h β)′) := by
    rw [Derivation.leibniz_div]
    simp only [smul_eq_mul]
    rw [map_mul, map_sub, map_mul, map_mul, map_pow, map_inv₀, hA, hB]
  have hR : (addTranslationMeroEquivGen h (α / β))′
      = (addTranslationMeroEquivGen h β)⁻¹ ^ 2
        * ((addTranslationMeroEquivGen h β) * (addTranslationMeroEquivGen h α)′
          - (addTranslationMeroEquivGen h α) * (addTranslationMeroEquivGen h β)′) := by
    rw [map_div₀, Derivation.leibniz_div]
    simp only [smul_eq_mul]
  rw [← hxab, hL, hR]

theorem addTranslationMeroEquivGen_iterate_deriv (h w : E) (r : ℕ)
    (x : meroFieldGen (Set.univ : Set E)) :
    letI := Bottcher.isDomain_analyticSubringGen (Set.univ : Set E) isOpen_univ
      isPreconnected_univ_gen Set.univ_nonempty
    letI := meroFieldGenDirDifferential w (isOpen_univ (X := E)) isPreconnected_univ_gen
      Set.univ_nonempty
    addTranslationMeroEquivGen h (differentialJet r x)
      = differentialJet r (addTranslationMeroEquivGen h x) := by
  letI := Bottcher.isDomain_analyticSubringGen (Set.univ : Set E) isOpen_univ
    isPreconnected_univ_gen Set.univ_nonempty
  letI := meroFieldGenDirDifferential w (isOpen_univ (X := E)) isPreconnected_univ_gen
    Set.univ_nonempty
  induction r generalizing x with
  | zero => simp [differentialJet]
  | succ r ih =>
      rw [differentialJet, differentialJet, Function.iterate_succ_apply,
        Function.iterate_succ_apply]
      have h1 : addTranslationMeroEquivGen h ((Differential.deriv^[r]) (x′))
          = (Differential.deriv^[r]) (addTranslationMeroEquivGen h (x′)) := ih (x′)
      rw [h1, addTranslationMeroEquivGen_dirDeriv h w x]

variable {n : ℕ}

/-- **The noncompact period-quotient law in every dimension.**  A hypertranscendental element of
the several-variable meromorphic field of `ℂ^{n+1}` has a noncompact quotient by any group of its
periods. -/
theorem not_compactSpace_quotient_of_hypertranscendental_gen (w : Fin (n + 1) → ℂ)
    {P : AddSubgroup (Fin (n + 1) → ℂ)}
    {x : meroFieldGen (Set.univ : Set (Fin (n + 1) → ℂ))}
    (hfix : ∀ p ∈ P, p ∈ meroPeriodSubgroupGen (E := Fin (n + 1) → ℂ) x)
    (hx : letI := meroFieldGenDirDifferential w (isOpen_univ (X := Fin (n + 1) → ℂ))
            isPreconnected_univ_gen Set.univ_nonempty
          HypertranscendentalOver ℂ x) :
    ¬ CompactSpace ((Fin (n + 1) → ℂ) ⧸ P) := by
  letI := meroFieldGenDirDifferential w (isOpen_univ (X := Fin (n + 1) → ℂ))
    isPreconnected_univ_gen Set.univ_nonempty
  intro hP
  -- the jets share the periods
  have hjet : ∀ (k : Fin (n + 2)), ∀ p ∈ P,
      p ∈ meroPeriodSubgroupGen (E := Fin (n + 1) → ℂ) (differentialJet (k : ℕ) x) := by
    intro k p hp
    rw [mem_meroPeriodSubgroupGen,
      addTranslationMeroEquivGen_iterate_deriv p w (k : ℕ) x]
    congr 1
    exact hfix p hp
  obtain ⟨Q, hQ0, hQ⟩ :=
    exists_ne_zero_poly_aeval_of_compactSpace_quotient hP
      (fun k : Fin (n + 2) => differentialJet (k : ℕ) x) hjet
  have hindep : DifferentialIndependent ℂ (fun _ : Unit => x) := not_not.mp hx
  have hinj : Function.Injective (fun k : Fin (n + 2) => (((), (k : ℕ)) : Unit × ℕ)) := by
    intro a b hab
    exact Fin.val_injective (congrArg Prod.snd hab)
  have hfull : AlgebraicIndependent ℂ (fun p : Unit × ℕ => differentialJet p.2 x) := hindep
  have hsub := AlgebraicIndependent.comp hfull (fun k : Fin (n + 2) => ((), (k : ℕ))) hinj
  have hinj2 : Function.Injective (MvPolynomial.aeval (R := ℂ)
      ((fun p : Unit × ℕ => differentialJet p.2 x)
        ∘ fun k : Fin (n + 2) => ((), (k : ℕ)))) := hsub
  refine hQ0 (hinj2 ?_)
  rw [map_zero]
  exact hQ

/-- **The period group of a hypertranscendental several-variable meromorphic germ is an escape
subgroup**, in every dimension. -/
theorem isEscapeSubgroup_meroPeriodSubgroupGen_of_hypertranscendental (w : Fin (n + 1) → ℂ)
    {x : meroFieldGen (Set.univ : Set (Fin (n + 1) → ℂ))}
    (hx : letI := meroFieldGenDirDifferential w (isOpen_univ (X := Fin (n + 1) → ℂ))
            isPreconnected_univ_gen Set.univ_nonempty
          HypertranscendentalOver ℂ x) :
    IsEscapeSubgroup (meroPeriodSubgroupGen (E := Fin (n + 1) → ℂ) x) :=
  isEscapeSubgroup_meroPeriodSubgroupGen x
    (not_compactSpace_quotient_of_hypertranscendental_gen w (fun _ hp => hp) hx)

end GaloisForLFunctions.HTGeometry
