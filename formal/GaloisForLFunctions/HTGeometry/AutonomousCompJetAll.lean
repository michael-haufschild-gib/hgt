import GaloisForLFunctions.HTGeometry.AutonomousCompJet
import GaloisForLFunctions.HTGeometry.AlgebraicClosureDerivationClosed

/-!
# Every composed jet is algebraic over the composition

For the composed jets `f⁽ⁱ⁾ ∘ g` the natural derivation is not `d/dz` but its pullback
`x ↦ x′ / g′`, for which `f⁽ⁱ⁾∘g ↦ f⁽ⁱ⁺¹⁾∘g`.  With that derivation the field `ℂ(f∘g)` has the
property that the derivative of each of its elements is algebraic over it — the generator's
derivative is `f′∘g`, which the autonomy relation makes algebraic — so its relative algebraic closure
is derivation-closed, and every composed jet lands inside it.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher
open scoped Differential

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-- The derivative of a nonconstant entire function is a nonzero field element. -/
theorem jetElem_one_ne_zero {g : ℂ → ℂ} (hg : Differentiable ℂ g)
    (hnc : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c) : jetElem hg 1 ≠ 0 := by
  intro hcon
  rw [jetElem] at hcon
  have hzero := (analyticMeroElement_eq_zero_iff _).mp hcon
  refine hnc ⟨g 0, ?_⟩
  have hderiv : ∀ z : ℂ, deriv g z = 0 := by
    intro z
    have h := hzero z (Set.mem_univ z)
    simpa [iteratedDeriv_one] using h
  exact fun z => is_const_of_deriv_eq_zero hg hderiv z 0

set_option synthInstance.maxHeartbeats 1000000 in
/-- **Every composed jet is algebraic over the composition.**  With the pullback derivation the
relative algebraic closure of `ℂ(f∘g)` is derivation-closed, and it contains every `f⁽ⁱ⁾∘g`. -/
theorem isAlgebraic_compJetElem_of_autonomous {f g : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hg : Differentiable ℂ g) (haut : AutonomousFirstOrder f)
    (hcomp : Differentiable ℂ (fun w => f (g w)))
    (hncomp : ¬ ∃ c : ℂ, ∀ z : ℂ, f (g z) = c)
    (hncg : ¬ ∃ c : ℂ, ∀ z : ℂ, g z = c) (i : ℕ) :
    IsAlgebraic ↥(IntermediateField.adjoin ℂ
        ({jetElem hcomp 0} : Set (meroField (Set.univ : Set ℂ)))) (compJetElem hf hg i) := by
  classical
  set hElem : meroField (Set.univ : Set ℂ) := jetElem hcomp 0 with hhE
  set c : meroField (Set.univ : Set ℂ) := jetElem hg 1 with hcdef
  have hcne : c ≠ 0 := jetElem_one_ne_zero hg hncg
  set E : IntermediateField ℂ (meroField (Set.univ : Set ℂ)) :=
    IntermediateField.adjoin ℂ ({hElem} : Set (meroField (Set.univ : Set ℂ))) with hEdef
  let d0 := @Differential.deriv (meroField (Set.univ : Set ℂ)) _ relativeGaugeDifferential
  letI D : Differential (meroField (Set.univ : Set ℂ)) := ⟨c⁻¹ • d0⟩
  have hDapply : ∀ x : meroField (Set.univ : Set ℂ), x′ = c⁻¹ * d0 x := fun _ => rfl
  -- the pullback derivation shifts the composed jets
  have hshift : ∀ j : ℕ, (compJetElem hf hg j)′ = compJetElem hf hg (j + 1) := by
    intro j
    rw [hDapply, show d0 (compJetElem hf hg j) = compJetElem hf hg (j + 1) * c from
      deriv_compJetElem hf hg j]
    field_simp
  -- the closure contains the first composed jet
  have hmemE : ∀ y : meroField (Set.univ : Set ℂ), ∀ hy : y ∈ E,
      y ∈ algebraicClosure ↥E (meroField (Set.univ : Set ℂ)) := by
    intro y hy
    exact IntermediateField.algebraMap_mem (algebraicClosure ↥E (meroField (Set.univ : Set ℂ)))
      (⟨y, hy⟩ : ↥E)
  have hclos1 : compJetElem hf hg 1 ∈ algebraicClosure ↥E (meroField (Set.univ : Set ℂ)) := by
    refine mem_algebraicClosure_iff.mpr ?_
    refine isAlgebraic_intermediateField_of_isAlgebraic_algebraAdjoin
      ({hElem} : Set (meroField (Set.univ : Set ℂ))) ?_
    exact isAlgebraic_compJetElem_one hf hg haut hcomp hncomp
  -- the derivative of every element of the base is in the closure
  have hbase : ∀ y : meroField (Set.univ : Set ℂ),
      y ∈ (⊥ : IntermediateField ↥E (meroField (Set.univ : Set ℂ))) →
      y′ ∈ algebraicClosure ↥E (meroField (Set.univ : Set ℂ)) := by
    intro y hy
    have hyE : y ∈ E := by
      rw [IntermediateField.mem_bot] at hy
      obtain ⟨w, rfl⟩ := hy
      exact w.2
    clear hy
    rw [hEdef] at hyE
    induction hyE using IntermediateField.adjoin_induction with
    | mem x hx =>
        rcases hx with rfl
        have h0 : compJetElem hf hg 0 = hElem := compJetElem_zero hf hg hcomp
        have h1 := hshift 0
        rw [h0] at h1
        rw [h1]
        exact hclos1
    | algebraMap a =>
        have hconst : (algebraMap ℂ (meroField (Set.univ : Set ℂ))) a
            = analyticMeroElement (fun _ : ℂ => a) analyticOnNhd_const :=
          (analyticMeroElement_const (Set.univ : Set ℂ) a).trans rfl
        have hderivfun : deriv (fun _ : ℂ => a) = fun _ : ℂ => (0 : ℂ) := by
          funext z
          simp
        have hzero : d0 ((algebraMap ℂ (meroField (Set.univ : Set ℂ))) a) = 0 := by
          rw [hconst]
          show @Differential.deriv (meroField (Set.univ : Set ℂ)) _ relativeGaugeDifferential
            (analyticMeroElement (fun _ : ℂ => a) analyticOnNhd_const) = 0
          rw [deriv_analyticMeroElement,
            analyticMeroElement_congr _ analyticOnNhd_const hderivfun,
            analyticMeroElement_zero]
        rw [hDapply, hzero, mul_zero]
        exact Subalgebra.zero_mem _
    | add a b ha hb iha ihb =>
        rw [deriv_add']
        exact Subalgebra.add_mem _ iha ihb
    | inv a ha iha =>
        by_cases ha0 : a = 0
        · rw [ha0]
          have hz : (0 : meroField (Set.univ : Set ℂ))⁻¹ = 0 := by simp
          rw [hz, hDapply]
          have hd0 : d0 (0 : meroField (Set.univ : Set ℂ)) = 0 := map_zero _
          rw [hd0, mul_zero]
          exact Subalgebra.zero_mem _
        · have hprod : a * a⁻¹ = 1 := mul_inv_cancel₀ ha0
          have hone : ((1 : meroField (Set.univ : Set ℂ)))′ = 0 := by
            have h := deriv_mul' (1 : meroField (Set.univ : Set ℂ)) 1
            simp only [mul_one, one_mul] at h
            linear_combination -h
          have hleib := deriv_mul' a a⁻¹
          rw [hprod, hone] at hleib
          have h1 : a * (a⁻¹)′ = -(a⁻¹ * a′) := by linear_combination -hleib
          have hinv : (a⁻¹)′ = -(a⁻¹ * a⁻¹ * a′) := by
            calc (a⁻¹)′ = a⁻¹ * (a * (a⁻¹)′) := by
                  rw [← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
              _ = a⁻¹ * (-(a⁻¹ * a′)) := by rw [h1]
              _ = -(a⁻¹ * a⁻¹ * a′) := by ring
          rw [hinv]
          have hainv : a⁻¹ ∈ algebraicClosure ↥E (meroField (Set.univ : Set ℂ)) :=
            hmemE _ (E.inv_mem ha)
          exact Subalgebra.neg_mem _
            (Subalgebra.mul_mem _ (Subalgebra.mul_mem _ hainv hainv) iha)
    | mul a b ha hb iha ihb =>
        rw [deriv_mul']
        exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ (hmemE _ ha) ihb)
          (Subalgebra.mul_mem _ (hmemE _ hb) iha)
  -- every composed jet is in the closure
  have hmem : ∀ j : ℕ, compJetElem hf hg j ∈ algebraicClosure ↥E (meroField (Set.univ : Set ℂ)) := by
    intro j
    induction j with
    | zero =>
        rw [compJetElem_zero hf hg hcomp]
        refine hmemE _ ?_
        rw [hEdef]
        exact IntermediateField.subset_adjoin ℂ _ rfl
    | succ k ih =>
        rw [← hshift k]
        exact deriv_mem_algebraicClosure hbase ih
  exact mem_algebraicClosure_iff.mp (hmem i)

end

end GaloisForLFunctions.HTGeometry
