import GaloisForLFunctions.HTGeometry.FormWedgeLeibniz
import GaloisForLFunctions.HTGeometry.PeriodicCohomology

/-!
# The wedge product on the periodic de Rham complex

The wedge product of two periodic forms of class `C^(1 : ℕ)` is again periodic of class `C^(1 : ℕ)`, because in
coordinates it is a finite sum of products of the coefficients times constant forms.  By the Leibniz
rule the wedge of two closed forms is closed, and the wedge of an exact form with a closed one is
exact with a periodic primitive, so the product descends to cohomology.  On classes of invariant
forms it is the product of the exterior algebra, so the comparison of the cohomology of the torus
with the exterior power of the dual is multiplicative.

* `wedgeForm_differentiable`, `wedgeForm_fderiv_continuous` : the wedge is of class `C^(1 : ℕ)`.
* `wedgeForm_mem_closed` : the wedge of closed periodic forms is a closed periodic form.
* `wedgeForm_extDeriv_left`, `wedgeForm_extDeriv_right` : wedging with a closed form commutes with
  the exterior derivative, up to the sign `(-1)^p` on the left.
* `wedgeForm_class_eq` : the class of a wedge is the wedge of the invariant representatives, so the
  comparison with the exterior power is multiplicative.
-/

set_option maxSynthPendingDepth 3
set_option maxHeartbeats 1000000

namespace GaloisForLFunctions.HTGeometry

open exteriorPower Module

section Regularity

variable {𝕜 : Type*} [RCLike 𝕜] {r p q n : ℕ}

/-- The coefficients of a form of class `C^(1 : ℕ)` are of class `C^(1 : ℕ)`. -/
theorem form_coeff_fderiv_continuous {ω : PeriodicFormSpace 𝕜 r n} (hω : Differentiable 𝕜 ω)
    (hcont : Continuous (fderiv 𝕜 ω)) (S : Set.powersetCard (Fin r) n) :
    Continuous (fderiv 𝕜 fun x => ω x (coordTuple 𝕜 S)) := by
  have hfd : (fderiv 𝕜 fun x => ω x (coordTuple 𝕜 S)) =
      fun x => (evalFormL (coordTuple 𝕜 S)).comp (fderiv 𝕜 ω x) := by
    funext x
    exact (((evalFormL (coordTuple 𝕜 S)).hasFDerivAt).comp x (hω x).hasFDerivAt).fderiv
  rw [hfd]
  exact isBoundedBilinearMap_comp.continuous.comp (continuous_const.prodMk hcont)

/-- A scalar function times a constant form is of class `C^(1 : ℕ)`. -/
theorem fderiv_continuous_smul_const {c : (Fin r → 𝕜) → 𝕜} (hc : Differentiable 𝕜 c)
    (hc' : Continuous (fderiv 𝕜 c)) (K : (Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜) :
    Continuous (fderiv 𝕜 fun y => c y • K) := by
  have hfd : (fderiv 𝕜 fun y => c y • K) = fun y => (fderiv 𝕜 c y).smulRight K := by
    funext y
    exact ((hc y).hasFDerivAt.smul_const K).fderiv
  rw [hfd]
  exact (((ContinuousLinearMap.smulRightL 𝕜 (Fin r → 𝕜)
    ((Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜)).flip K).continuous).comp hc'

/-- A finite sum of forms of class `C^(1 : ℕ)` is of class `C^(1 : ℕ)`. -/
theorem fderiv_continuous_finset_sum {ι : Type*} (t : Finset ι) (F : ι → PeriodicFormSpace 𝕜 r n)
    (hF : ∀ i, Differentiable 𝕜 (F i)) (hF' : ∀ i, Continuous (fderiv 𝕜 (F i))) :
    Continuous (fderiv 𝕜 fun y => ∑ i ∈ t, F i y) := by
  haveI : ContinuousAdd ((Fin r → 𝕜) →L[𝕜] ((Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜)) := by
    have htag : IsTopologicalAddGroup
        ((Fin r → 𝕜) →L[𝕜] ((Fin r → 𝕜) [⋀^Fin n]→L[𝕜] 𝕜)) := inferInstance
    exact htag.toContinuousAdd
  have hfd : (fderiv 𝕜 fun y => ∑ i ∈ t, F i y) = fun y => ∑ i ∈ t, fderiv 𝕜 (F i) y := by
    funext y
    exact fderiv_fun_sum fun i _ => (hF i) y
  rw [hfd]
  exact continuous_finsetSum t fun i _ => hF' i

/-- **The wedge product of two differentiable forms is differentiable.** -/
theorem wedgeForm_differentiable (h : p + q = n) {ω : PeriodicFormSpace 𝕜 r p}
    {η : PeriodicFormSpace 𝕜 r q} (hω : Differentiable 𝕜 ω) (hη : Differentiable 𝕜 η) :
    Differentiable 𝕜 fun y => wedgeForm h (ω y) (η y) := by
  have hexp : (fun y => wedgeForm h (ω y) (η y)) =
      fun y => ∑ S : Set.powersetCard (Fin r) p, ∑ T : Set.powersetCard (Fin r) q,
        (ω y (coordTuple 𝕜 S) * η y (coordTuple 𝕜 T)) •
          constantFormOfExterior 𝕜 r n
            (exteriorMulOf h (coordExterior 𝕜 r p S) (coordExterior 𝕜 r q T)) := by
    funext y
    exact wedgeForm_expansion h (ω y) (η y)
  rw [hexp]
  intro y
  refine DifferentiableAt.fun_sum fun S _ => ?_
  refine DifferentiableAt.fun_sum fun T _ => ?_
  exact (((form_coeff_differentiable hω S) y).mul ((form_coeff_differentiable hη T) y)).smul_const _

/-- **The wedge product of two forms of class `C^(1 : ℕ)` is of class `C^(1 : ℕ)`.** -/
theorem wedgeForm_fderiv_continuous (h : p + q = n) {ω : PeriodicFormSpace 𝕜 r p}
    {η : PeriodicFormSpace 𝕜 r q} (hω : Differentiable 𝕜 ω) (hωc : Continuous (fderiv 𝕜 ω))
    (hη : Differentiable 𝕜 η) (hηc : Continuous (fderiv 𝕜 η)) :
    Continuous (fderiv 𝕜 fun y => wedgeForm h (ω y) (η y)) := by
  have hexp : (fun y => wedgeForm h (ω y) (η y)) =
      fun y => ∑ S : Set.powersetCard (Fin r) p, ∑ T : Set.powersetCard (Fin r) q,
        (ω y (coordTuple 𝕜 S) * η y (coordTuple 𝕜 T)) •
          constantFormOfExterior 𝕜 r n
            (exteriorMulOf h (coordExterior 𝕜 r p S) (coordExterior 𝕜 r q T)) := by
    funext y
    exact wedgeForm_expansion h (ω y) (η y)
  rw [hexp]
  have hcoeff : ∀ (S : Set.powersetCard (Fin r) p) (T : Set.powersetCard (Fin r) q),
      Continuous (fderiv 𝕜 fun y => ω y (coordTuple 𝕜 S) * η y (coordTuple 𝕜 T)) := by
    intro S T
    have hfd : (fderiv 𝕜 fun y => ω y (coordTuple 𝕜 S) * η y (coordTuple 𝕜 T)) =
        fun y => (ω y (coordTuple 𝕜 S)) • fderiv 𝕜 (fun z => η z (coordTuple 𝕜 T)) y +
          (η y (coordTuple 𝕜 T)) • fderiv 𝕜 (fun z => ω z (coordTuple 𝕜 S)) y := by
      funext y
      exact fderiv_fun_mul ((form_coeff_differentiable hω S) y)
        ((form_coeff_differentiable hη T) y)
    rw [hfd]
    haveI : ContinuousAdd ((Fin r → 𝕜) →L[𝕜] 𝕜) := by
      have htag : IsTopologicalAddGroup ((Fin r → 𝕜) →L[𝕜] 𝕜) := inferInstance
      exact htag.toContinuousAdd
    refine Continuous.add ?_ ?_
    · exact ((evalFormL (coordTuple 𝕜 S)).continuous.comp hω.continuous).smul
        (form_coeff_fderiv_continuous hη hηc T)
    · exact ((evalFormL (coordTuple 𝕜 T)).continuous.comp hη.continuous).smul
        (form_coeff_fderiv_continuous hω hωc S)
  refine fderiv_continuous_finset_sum Finset.univ _ ?_ ?_
  · intro S y
    refine DifferentiableAt.fun_sum fun T _ => ?_
    exact (((form_coeff_differentiable hω S) y).mul
      ((form_coeff_differentiable hη T) y)).smul_const _
  · intro S
    refine fderiv_continuous_finset_sum Finset.univ _ ?_ ?_
    · intro T y
      exact (((form_coeff_differentiable hω S) y).mul
        ((form_coeff_differentiable hη T) y)).smul_const _
    · intro T
      exact fderiv_continuous_smul_const
        (fun y => ((form_coeff_differentiable hω S) y).mul ((form_coeff_differentiable hη T) y))
        (hcoeff S T) _

end Regularity

section ClosedAndExact

variable {𝕜 : Type*} [RCLike 𝕜] {r p q n : ℕ}

/-- The wedge product of periodic forms is periodic. -/
theorem wedgeForm_periodic {c : 𝕜} (h : p + q = n) {ω : PeriodicFormSpace 𝕜 r p}
    {η : PeriodicFormSpace 𝕜 r q}
    (hω : ∀ (l : Fin r) (w : Fin r → 𝕜), ω (w + c • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = ω w)
    (hη : ∀ (l : Fin r) (w : Fin r → 𝕜), η (w + c • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = η w)
    (l : Fin r) (w : Fin r → 𝕜) :
    wedgeForm h (ω (w + c • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)))
        (η (w + c • (Pi.single l (1 : 𝕜) : Fin r → 𝕜))) =
      wedgeForm h (ω w) (η w) := by
  rw [hω l w, hη l w]

theorem wedgeForm_zero_left (h : p + q = n) (β : (Fin r → 𝕜) [⋀^Fin q]→L[𝕜] 𝕜) :
    wedgeForm h (0 : (Fin r → 𝕜) [⋀^Fin p]→L[𝕜] 𝕜) β = 0 := by
  have h0 : (0 : (Fin r → 𝕜) [⋀^Fin p]→L[𝕜] 𝕜) =
      (0 : 𝕜) • (0 : (Fin r → 𝕜) [⋀^Fin p]→L[𝕜] 𝕜) := by
    ext v
    show (0 : 𝕜) = (0 : 𝕜) * (0 : 𝕜)
    rw [mul_zero]
  rw [h0, wedgeForm_smul_left]
  ext v
  show (0 : 𝕜) * _ = (0 : 𝕜)
  rw [zero_mul]

theorem wedgeForm_zero_right (h : p + q = n) (α : (Fin r → 𝕜) [⋀^Fin p]→L[𝕜] 𝕜) :
    wedgeForm h α (0 : (Fin r → 𝕜) [⋀^Fin q]→L[𝕜] 𝕜) = 0 := by
  have h0 : (0 : (Fin r → 𝕜) [⋀^Fin q]→L[𝕜] 𝕜) =
      (0 : 𝕜) • (0 : (Fin r → 𝕜) [⋀^Fin q]→L[𝕜] 𝕜) := by
    ext v
    show (0 : 𝕜) = (0 : 𝕜) * (0 : 𝕜)
    rw [mul_zero]
  rw [h0, wedgeForm_smul_right]
  ext v
  show (0 : 𝕜) * _ = (0 : 𝕜)
  rw [zero_mul]

/-- **The wedge product of two closed periodic forms of class `C^(1 : ℕ)` is one.** -/
theorem wedgeForm_mem_closed {c : 𝕜} (h : p + q = n) {ω : PeriodicFormSpace 𝕜 r p}
    {η : PeriodicFormSpace 𝕜 r q} (hω : ω ∈ periodicClosedForms c r p)
    (hη : η ∈ periodicClosedForms c r q) :
    (fun y => wedgeForm h (ω y) (η y)) ∈ periodicClosedForms c r n := by
  obtain ⟨hωd, hωc, hωp, hωz⟩ := hω
  obtain ⟨hηd, hηc, hηp, hηz⟩ := hη
  refine ⟨wedgeForm_differentiable h hωd hηd,
    wedgeForm_fderiv_continuous h hωd hωc hηd hηc,
    fun l w => wedgeForm_periodic h hωp hηp l w, fun x => ?_⟩
  rw [extDeriv_wedgeForm h hωd hηd x, hωz x, hηz x, wedgeForm_zero_left, wedgeForm_zero_right]
  ext v
  show (0 : 𝕜) + ((-1 : 𝕜) ^ p) * (0 : 𝕜) = (0 : 𝕜)
  ring

/-- **Wedging with a closed form on the right commutes with the exterior derivative.** -/
theorem wedgeForm_extDeriv_left {pb qa m : ℕ} (hm : pb + qa = m)
    {θ : PeriodicFormSpace 𝕜 r pb} {η : PeriodicFormSpace 𝕜 r qa}
    (hθ : Differentiable 𝕜 θ) (hη : Differentiable 𝕜 η)
    (hηz : ∀ x, extDeriv η x = 0) (x : Fin r → 𝕜) :
    extDeriv (fun y => wedgeForm hm (θ y) (η y)) x =
      wedgeForm (by omega : pb + 1 + qa = m + 1) (extDeriv θ x) (η x) := by
  have hz : ((-1 : 𝕜) ^ pb) • (0 : (Fin r → 𝕜) [⋀^Fin (m + 1)]→L[𝕜] 𝕜) = 0 := by
    ext v
    show ((-1 : 𝕜) ^ pb) * ((0 : (Fin r → 𝕜) [⋀^Fin (m + 1)]→L[𝕜] 𝕜) v) =
      (0 : (Fin r → 𝕜) [⋀^Fin (m + 1)]→L[𝕜] 𝕜) v
    rw [show ((0 : (Fin r → 𝕜) [⋀^Fin (m + 1)]→L[𝕜] 𝕜) v) = (0 : 𝕜) from rfl, mul_zero]
  rw [extDeriv_wedgeForm hm hθ hη x, hηz x, wedgeForm_zero_right, hz, add_zero]

/-- **Wedging with a closed form on the left commutes with the exterior derivative** up to the sign
`(-1)^p`. -/
theorem wedgeForm_extDeriv_right {pa qb m : ℕ} (hm : pa + qb = m)
    {ω : PeriodicFormSpace 𝕜 r pa} {θ : PeriodicFormSpace 𝕜 r qb}
    (hω : Differentiable 𝕜 ω) (hωz : ∀ x, extDeriv ω x = 0) (hθ : Differentiable 𝕜 θ)
    (x : Fin r → 𝕜) :
    extDeriv (fun y => wedgeForm hm (ω y) (θ y)) x =
      ((-1 : 𝕜) ^ pa) • wedgeForm (by omega : pa + (qb + 1) = m + 1) (ω x) (extDeriv θ x) := by
  rw [extDeriv_wedgeForm hm hω hθ x, hωz x, wedgeForm_zero_left, zero_add]

/-- **The class of a wedge product is the wedge of the invariant representatives.**  Replacing a
closed form by its invariant representative plus an exact term changes the wedge by an exact term
with a periodic primitive, so the comparison of the cohomology of the torus with the exterior power
of the dual is multiplicative. -/
theorem wedgeForm_class_eq {c : 𝕜} {pb qb : ℕ}
    {ω : PeriodicFormSpace 𝕜 r (pb + 1)} {θ : PeriodicFormSpace 𝕜 r pb}
    {θ' : PeriodicFormSpace 𝕜 r qb}
    {α : (Fin r → 𝕜) [⋀^Fin (pb + 1)]→L[𝕜] 𝕜} {β : (Fin r → 𝕜) [⋀^Fin (qb + 1)]→L[𝕜] 𝕜}
    (hωd : Differentiable 𝕜 ω) (hωc : Continuous (fderiv 𝕜 ω))
    (hωp : ∀ (l : Fin r) (w : Fin r → 𝕜),
      ω (w + c • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = ω w)
    (hωz : ∀ x, extDeriv ω x = 0) (hωeq : ∀ y, ω y = α + extDeriv θ y)
    (hθd : Differentiable 𝕜 θ) (hθc : Continuous (fderiv 𝕜 θ))
    (hθp : ∀ (l : Fin r) (w : Fin r → 𝕜),
      θ (w + c • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = θ w)
    (hθ'd : Differentiable 𝕜 θ') (hθ'c : Continuous (fderiv 𝕜 θ'))
    (hθ'p : ∀ (l : Fin r) (w : Fin r → 𝕜),
      θ' (w + c • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = θ' w) :
    ∃ ζ : PeriodicFormSpace 𝕜 r (pb + qb + 1),
      Differentiable 𝕜 ζ ∧ Continuous (fderiv 𝕜 ζ) ∧
      (∀ (l : Fin r) (w : Fin r → 𝕜),
        ζ (w + c • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)) = ζ w) ∧
      ∀ y, wedgeForm (by omega : pb + 1 + (qb + 1) = pb + qb + 1 + 1) (ω y) (β + extDeriv θ' y) =
        wedgeForm (by omega : pb + 1 + (qb + 1) = pb + qb + 1 + 1) α β + extDeriv ζ y := by
  have hβconst : ∀ x : Fin r → 𝕜, extDeriv (fun _ : Fin r → 𝕜 => β) x = 0 :=
    fun x => extDeriv_const β x
  have hβdiff : Differentiable 𝕜 (fun _ : Fin r → 𝕜 => β) := differentiable_const β
  have hβcont : Continuous (fderiv 𝕜 (fun _ : Fin r → 𝕜 => β)) := by
    have hfd : fderiv 𝕜 (fun _ : Fin r → 𝕜 => β) = fun _ => 0 := by
      funext w
      exact fderiv_const_apply _
    rw [hfd]
    exact continuous_const
  set ζ : PeriodicFormSpace 𝕜 r (pb + qb + 1) := fun y =>
    wedgeForm (by omega : pb + (qb + 1) = pb + qb + 1) (θ y) β +
      ((-1 : 𝕜) ^ (pb + 1)) •
        wedgeForm (by omega : pb + 1 + qb = pb + qb + 1) (ω y) (θ' y) with hζ
  have hζ1diff : Differentiable 𝕜 fun y =>
      wedgeForm (by omega : pb + (qb + 1) = pb + qb + 1) (θ y) β :=
    wedgeForm_differentiable _ hθd hβdiff
  have hζ2diff : Differentiable 𝕜 fun y =>
      wedgeForm (by omega : pb + 1 + qb = pb + qb + 1) (ω y) (θ' y) :=
    wedgeForm_differentiable _ hωd hθ'd
  refine ⟨ζ, fun y => (hζ1diff y).add ((hζ2diff y).const_smul ((-1 : 𝕜) ^ (pb + 1))), ?_, ?_, ?_⟩
  · haveI : ContinuousAdd ((Fin r → 𝕜) →L[𝕜]
        ((Fin r → 𝕜) [⋀^Fin (pb + qb + 1)]→L[𝕜] 𝕜)) := by
      have htag : IsTopologicalAddGroup ((Fin r → 𝕜) →L[𝕜]
        ((Fin r → 𝕜) [⋀^Fin (pb + qb + 1)]→L[𝕜] 𝕜)) := inferInstance
      exact htag.toContinuousAdd
    have hfd : fderiv 𝕜 ζ = fun y =>
        fderiv 𝕜 (fun z => wedgeForm (by omega : pb + (qb + 1) = pb + qb + 1) (θ z) β) y +
          ((-1 : 𝕜) ^ (pb + 1)) •
            fderiv 𝕜 (fun z =>
              wedgeForm (by omega : pb + 1 + qb = pb + qb + 1) (ω z) (θ' z)) y := by
      funext y
      have h2 : DifferentiableAt 𝕜 (fun z => ((-1 : 𝕜) ^ (pb + 1)) •
          wedgeForm (by omega : pb + 1 + qb = pb + qb + 1) (ω z) (θ' z)) y :=
        (hζ2diff y).const_smul ((-1 : 𝕜) ^ (pb + 1))
      rw [hζ, fderiv_fun_add (hζ1diff y) h2, fderiv_fun_const_smul (hζ2diff y)]
    rw [hfd]
    exact (wedgeForm_fderiv_continuous _ hθd hθc hβdiff hβcont).add
      ((wedgeForm_fderiv_continuous _ hωd hωc hθ'd hθ'c).const_smul ((-1 : 𝕜) ^ (pb + 1)))
  · intro l w
    show wedgeForm _ (θ (w + c • (Pi.single l (1 : 𝕜) : Fin r → 𝕜))) β +
        ((-1 : 𝕜) ^ (pb + 1)) • wedgeForm _
          (ω (w + c • (Pi.single l (1 : 𝕜) : Fin r → 𝕜)))
          (θ' (w + c • (Pi.single l (1 : 𝕜) : Fin r → 𝕜))) = _
    rw [hθp l w, hωp l w, hθ'p l w]
  · intro y
    have hsign : ((-1 : 𝕜) ^ (pb + 1 + (pb + 1))) = 1 := by
      rw [← two_mul, pow_mul]
      norm_num
    have hcancel : ∀ X : (Fin r → 𝕜) [⋀^Fin (pb + qb + 1 + 1)]→L[𝕜] 𝕜,
        ((-1 : 𝕜) ^ (pb + 1)) • (((-1 : 𝕜) ^ (pb + 1)) • X) = X := by
      intro X
      ext v
      show ((-1 : 𝕜) ^ (pb + 1)) * (((-1 : 𝕜) ^ (pb + 1)) * (X v)) = X v
      rw [← mul_assoc, ← pow_add, hsign, one_mul]
    have e1 : wedgeForm (by omega : pb + 1 + (qb + 1) = pb + qb + 1 + 1) (ω y) β =
        wedgeForm (by omega : pb + 1 + (qb + 1) = pb + qb + 1 + 1) α β +
          extDeriv (fun z =>
            wedgeForm (by omega : pb + (qb + 1) = pb + qb + 1) (θ z) β) y := by
      rw [hωeq y, wedgeForm_add_left,
        wedgeForm_extDeriv_left (by omega : pb + (qb + 1) = pb + qb + 1) hθd hβdiff hβconst y]
    have e2 : wedgeForm (by omega : pb + 1 + (qb + 1) = pb + qb + 1 + 1) (ω y) (extDeriv θ' y) =
        ((-1 : 𝕜) ^ (pb + 1)) • extDeriv (fun z =>
          wedgeForm (by omega : pb + 1 + qb = pb + qb + 1) (ω z) (θ' z)) y := by
      rw [wedgeForm_extDeriv_right (by omega : pb + 1 + qb = pb + qb + 1) hωd hωz hθ'd y,
        hcancel]
    have hdζ : extDeriv ζ y =
        extDeriv (fun z =>
            wedgeForm (by omega : pb + (qb + 1) = pb + qb + 1) (θ z) β) y +
          ((-1 : 𝕜) ^ (pb + 1)) • extDeriv (fun z =>
            wedgeForm (by omega : pb + 1 + qb = pb + qb + 1) (ω z) (θ' z)) y := by
      have h2 : DifferentiableAt 𝕜 (fun z => ((-1 : 𝕜) ^ (pb + 1)) •
          wedgeForm (by omega : pb + 1 + qb = pb + qb + 1) (ω z) (θ' z)) y :=
        (hζ2diff y).const_smul ((-1 : 𝕜) ^ (pb + 1))
      have hsm : (fun z => ((-1 : 𝕜) ^ (pb + 1)) •
          wedgeForm (by omega : pb + 1 + qb = pb + qb + 1) (ω z) (θ' z)) =
          ((-1 : 𝕜) ^ (pb + 1)) • (fun z =>
            wedgeForm (by omega : pb + 1 + qb = pb + qb + 1) (ω z) (θ' z)) := rfl
      rw [hζ, extDeriv_fun_add (hζ1diff y) h2, hsm, extDeriv_smul]
    rw [wedgeForm_add_right, e1, e2, hdζ]
    abel

end ClosedAndExact

end GaloisForLFunctions.HTGeometry
