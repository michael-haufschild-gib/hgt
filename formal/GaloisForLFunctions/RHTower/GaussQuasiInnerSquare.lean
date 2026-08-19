import GaloisForLFunctions.RHTower.CircleReflectionOperator

/-!
# `C² = G`

Equation (1) of the source reduction of `gauss-component-quasi-inner-residue-hierarchy` asserts

`G = C² = p · B D B^{-2} D* B`,  where `C = B D I B`.

With the reflection `I` in hand this is an algebraic identity: `I² = 1` lets one insert `I I`
between the two copies of `C`, `I D I = D*` is already proved, and `I B² I = p · B^{-2}` is the
symbol computation `b_p(1-x)² = p^x = p · b_p(x)^{-2}`.
-/

namespace RHTower

open MeasureTheory

noncomputable section

/-- Composing two bounded multipliers multiplies the symbols. -/
theorem lpBoundedMulCLM_comp_circle
    {φ ψ : AddCircle (1 : ℝ) → ℂ} (hφ : Measurable φ) (hψ : Measurable ψ)
    {Cφ Cψ : ℝ} (hCφ0 : 0 ≤ Cφ) (hCφ : ∀ x, ‖φ x‖ ≤ Cφ)
    (hCψ0 : 0 ≤ Cψ) (hCψ : ∀ x, ‖ψ x‖ ≤ Cψ)
    (hprod : Measurable (fun x => φ x * ψ x))
    (hCprod : ∀ x, ‖φ x * ψ x‖ ≤ Cφ * Cψ) :
    (lpBoundedMulCLM (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) (p := 2) hφ hCφ0 hCφ) ∘L
        (lpBoundedMulCLM (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) (p := 2) hψ hCψ0 hCψ)
      = lpBoundedMulCLM (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) (p := 2) hprod
          (mul_nonneg hCφ0 hCψ0) hCprod := by
  ext f
  have h1 := lpBoundedMulCLM_coeFn hφ hCφ0 hCφ
    (lpBoundedMulCLM (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) (p := 2) hψ hCψ0 hCψ f)
  have h2 := lpBoundedMulCLM_coeFn hψ hCψ0 hCψ f
  have h3 := lpBoundedMulCLM_coeFn hprod (mul_nonneg hCφ0 hCψ0) hCprod f
  refine h1.trans ((?_ : _ =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))] _).trans h3.symm)
  filter_upwards [h2] with x hx
  rw [hx]
  ring

/-- The reflection conjugates a multiplier into the reflected multiplier. -/
theorem circleReflection_lpBoundedMul_conj
    {φ : AddCircle (1 : ℝ) → ℂ} (hφ : Measurable φ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, ‖φ x‖ ≤ C)
    (hφn : Measurable (fun x => φ (-x))) (hCn : ∀ x, ‖φ (-x)‖ ≤ C) :
    circleReflectionCLM ∘L
        (lpBoundedMulCLM (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) (p := 2) hφ hC0 hC) ∘L
        circleReflectionCLM
      = lpBoundedMulCLM (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) (p := 2) hφn hC0 hCn := by
  ext f
  set g : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) := circleReflectionCLM f with hg
  set Mg : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    lpBoundedMulCLM (μ := AddCircle.haarAddCircle (T := (1 : ℝ))) (p := 2) hφ hC0 hC g with hMg
  have h1 := circleReflectionCLM_coeFn Mg
  have h2 := lpBoundedMulCLM_coeFn hφ hC0 hC g
  have h2n : (fun x : AddCircle (1 : ℝ) => (Mg : AddCircle (1 : ℝ) → ℂ) (-x))
      =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))]
        fun x : AddCircle (1 : ℝ) => φ (-x) * (g : AddCircle (1 : ℝ) → ℂ) (-x) :=
    measurePreserving_neg_circle.quasiMeasurePreserving.ae
      (p := fun y : AddCircle (1 : ℝ) =>
        (Mg : AddCircle (1 : ℝ) → ℂ) y = φ y * (g : AddCircle (1 : ℝ) → ℂ) y) h2
  have h3 := circleReflectionCLM_coeFn f
  have h3n : (fun x : AddCircle (1 : ℝ) => (g : AddCircle (1 : ℝ) → ℂ) (-x))
      =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))]
        fun x : AddCircle (1 : ℝ) => (f : AddCircle (1 : ℝ) → ℂ) (- -x) :=
    measurePreserving_neg_circle.quasiMeasurePreserving.ae
      (p := fun y : AddCircle (1 : ℝ) =>
        (g : AddCircle (1 : ℝ) → ℂ) y = (f : AddCircle (1 : ℝ) → ℂ) (-y)) h3
  have h4 := lpBoundedMulCLM_coeFn hφn hC0 hCn f
  refine h1.trans ((?_ : _ =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))] _).trans h4.symm)
  filter_upwards [h2n, h3n] with x hx1 hx2
  rw [hx1, hx2, neg_neg]


theorem coe_period_one : ((1 : ℝ) : AddCircle (1 : ℝ)) = 0 := by
  simpa using AddCircle.coe_period (1 : ℝ)

/-- **The symbol identity** `b_p(1-x)² = p · b_p(x)^{-2}` on the circle, off the single point `0`. -/
theorem gaussPrimeScaleCircle_neg_sq {p : ℝ} (hp : 0 < p) {z : AddCircle (1 : ℝ)} (hz : z ≠ 0) :
    gaussPrimeScaleCircle p (-z) * gaussPrimeScaleCircle p (-z)
      = ((p : ℝ) : ℂ) * gaussPrimeScaleInvSqCircle p z := by
  set t : ℝ := ((AddCircle.equivIoc (1 : ℝ) 0 z : Set.Ioc (0 : ℝ) (0 + 1)) : ℝ) with ht
  have hmem : t ∈ Set.Ioc (0 : ℝ) (0 + 1) := (AddCircle.equivIoc (1 : ℝ) 0 z).2
  have hzt : ((t : ℝ) : AddCircle (1 : ℝ)) = z := AddCircle.coe_equivIoc
  have ht0 : 0 < t := hmem.1
  have htle : t ≤ 1 := by simpa using hmem.2
  have ht1 : t ≠ 1 := by
    intro h
    apply hz
    rw [← hzt, h, coe_period_one]
  have htlt : t < 1 := lt_of_le_of_ne htle ht1
  have hnegmem : (1 - t) ∈ Set.Ioc (0 : ℝ) (0 + 1) := by
    constructor
    · linarith
    · simp only [zero_add]; linarith
  have hcoe : ((1 - t : ℝ) : AddCircle (1 : ℝ))
      = ((1 : ℝ) : AddCircle (1 : ℝ)) - ((t : ℝ) : AddCircle (1 : ℝ)) :=
    QuotientAddGroup.mk_sub _ _ _
  have hneg : -z = (((1 - t : ℝ)) : AddCircle (1 : ℝ)) := by
    rw [hcoe, coe_period_one, hzt, zero_sub]
  rw [hneg]
  have hval1 : gaussPrimeScaleCircle p (((1 - t : ℝ)) : AddCircle (1 : ℝ))
      = ((gaussPrimeScale p (1 - t) : ℝ) : ℂ) := AddCircle.liftIoc_coe_apply hnegmem
  have hval2 : gaussPrimeScaleInvSqCircle p ((t : ℝ) : AddCircle (1 : ℝ))
      = ((gaussPrimeScaleInvSq p t : ℝ) : ℂ) := AddCircle.liftIoc_coe_apply hmem
  have hreal : gaussPrimeScale p (1 - t) * gaussPrimeScale p (1 - t)
      = p * gaussPrimeScaleInvSq p t := by
    rw [gaussPrimeScale, gaussPrimeScaleInvSq]
    have key : Real.exp ((1 - (1 - t)) * Real.log p / 2)
          * Real.exp ((1 - (1 - t)) * Real.log p / 2)
        = Real.exp (Real.log p) * Real.exp (-((1 - t) * Real.log p)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    rw [key, Real.exp_log hp]
  rw [hval1, ← hzt, hval2, ← Complex.ofReal_mul, ← Complex.ofReal_mul, hreal]


theorem volume_singleton_addCircle (x : AddCircle (1 : ℝ)) :
    volume ({x} : Set (AddCircle (1 : ℝ))) = 0 := by
  refine le_antisymm (ENNReal.le_of_forall_pos_le_add ?_) (by simp)
  intro ε hε _
  rw [zero_add]
  have hεr : (0 : ℝ) < (ε : ℝ) / 2 := by
    have : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
    linarith
  have hsub : ({x} : Set (AddCircle (1 : ℝ))) ⊆ Metric.closedBall x ((ε : ℝ) / 2) :=
    Set.singleton_subset_iff.mpr (Metric.mem_closedBall_self hεr.le)
  refine le_trans (measure_mono hsub) ?_
  rw [AddCircle.volume_closedBall]
  refine le_trans (ENNReal.ofReal_le_ofReal (min_le_right (1 : ℝ) _)) ?_
  rw [show (2 : ℝ) * ((ε : ℝ) / 2) = (ε : ℝ) by ring, ENNReal.ofReal_coe_nnreal]

theorem haar_singleton_addCircle (x : AddCircle (1 : ℝ)) :
    AddCircle.haarAddCircle (T := (1 : ℝ)) {x} = 0 := by
  have h := volume_singleton_addCircle x
  rw [AddCircle.volume_eq_smul_haarAddCircle] at h
  simp only [Measure.smul_apply, smul_eq_mul] at h
  rcases mul_eq_zero.mp h with h1 | h1
  · exact absurd h1 (by simp)
  · exact h1

theorem ae_ne_zero_addCircle :
    ∀ᵐ z ∂(AddCircle.haarAddCircle (T := (1 : ℝ))), z ≠ 0 := by
  have h := haar_singleton_addCircle (0 : AddCircle (1 : ℝ))
  rw [Filter.eventually_iff, mem_ae_iff]
  have hset : {z : AddCircle (1 : ℝ) | z ≠ 0}ᶜ = ({0} : Set (AddCircle (1 : ℝ))) := by
    ext z
    simp
  rw [hset]
  exact h

/-- **`I B² I = p · B^{-2}`.** -/
theorem circleReflection_gaussPrimeScaleSq_conj {p : ℝ} (hp : 1 < p) :
    circleReflectionCLM ∘L
        (gaussPrimeScaleBlock hp ∘L gaussPrimeScaleBlock hp) ∘L circleReflectionCLM
      = ((p : ℝ) : ℂ) • gaussPrimeScaleInvSqBlock hp := by
  have hp0 : (0 : ℝ) < p := lt_trans zero_lt_one hp
  ext f
  set g : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) := circleReflectionCLM f with hgdef
  have hD := circleReflectionCLM_coeFn f
  have hC := gaussPrimeScaleBlock_coeFn hp g
  have hB := gaussPrimeScaleBlock_coeFn hp (gaussPrimeScaleBlock hp g)
  have hinner : (gaussPrimeScaleBlock hp (gaussPrimeScaleBlock hp g)
        : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))]
        fun y => gaussPrimeScaleCircle p y *
          (gaussPrimeScaleCircle p y * (f : AddCircle (1 : ℝ) → ℂ) (-y)) := by
    filter_upwards [hB, hC, hD] with y h1 h2 h3
    rw [h1, h2, h3]
  have hA := circleReflectionCLM_coeFn (gaussPrimeScaleBlock hp (gaussPrimeScaleBlock hp g))
  have hAn : (fun x : AddCircle (1 : ℝ) =>
      (gaussPrimeScaleBlock hp (gaussPrimeScaleBlock hp g) : AddCircle (1 : ℝ) → ℂ) (-x))
      =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))]
        fun x : AddCircle (1 : ℝ) => gaussPrimeScaleCircle p (-x) *
          (gaussPrimeScaleCircle p (-x) * (f : AddCircle (1 : ℝ) → ℂ) (- -x)) :=
    measurePreserving_neg_circle.quasiMeasurePreserving.ae
      (p := fun y : AddCircle (1 : ℝ) =>
        (gaussPrimeScaleBlock hp (gaussPrimeScaleBlock hp g) : AddCircle (1 : ℝ) → ℂ) y
          = gaussPrimeScaleCircle p y *
            (gaussPrimeScaleCircle p y * (f : AddCircle (1 : ℝ) → ℂ) (-y))) hinner
  have hRHS : (((((p : ℝ) : ℂ) • gaussPrimeScaleInvSqBlock hp) f) : AddCircle (1 : ℝ) → ℂ)
      =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))]
        fun x => ((p : ℝ) : ℂ) *
          (gaussPrimeScaleInvSqCircle p x * (f : AddCircle (1 : ℝ) → ℂ) x) := by
    have h1 : ((((p : ℝ) : ℂ) • gaussPrimeScaleInvSqBlock hp) f)
        = ((p : ℝ) : ℂ) • (gaussPrimeScaleInvSqBlock hp f) := rfl
    rw [h1]
    have h2 := Lp.coeFn_smul (((p : ℝ) : ℂ)) (gaussPrimeScaleInvSqBlock hp f)
    have h3 : (gaussPrimeScaleInvSqBlock hp f : AddCircle (1 : ℝ) → ℂ)
        =ᵐ[AddCircle.haarAddCircle (T := (1 : ℝ))]
          fun z => gaussPrimeScaleInvSqCircle p z * (f : AddCircle (1 : ℝ) → ℂ) z :=
      MeasureTheory.lpBoundedMulCLM_coeFn _ _ _ f
    filter_upwards [h2, h3] with x hx1 hx2
    rw [hx1]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [hx2]
  refine hA.trans ((hAn.trans ?_).trans hRHS.symm)
  filter_upwards [ae_ne_zero_addCircle] with x hx
  rw [neg_neg, ← mul_assoc, gaussPrimeScaleCircle_neg_sq hp0 hx, mul_assoc]


/-- The paired block `C = B D I B` of the source reduction. -/
def gaussPairedBlock {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
      Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
  gaussPrimeScaleBlock (show (1 : ℝ) < (p : ℝ) by exact_mod_cast p.prop.one_lt) ∘L
    gaussDiagonalBlock hm k p ∘L circleReflectionCLM ∘L
      gaussPrimeScaleBlock (show (1 : ℝ) < (p : ℝ) by exact_mod_cast p.prop.one_lt)

/-- **Equation (1) of the source reduction**: `C² = p · B D B^{-2} D* B = G`. -/
theorem gaussPairedBlock_sq {m : ℕ} (hm : 1 ≤ m) (k : Fin m) (p : Nat.Primes) :
    gaussPairedBlock hm k p ∘L gaussPairedBlock hm k p = gaussQuasiInnerG hm k p := by
  have hp : (1 : ℝ) < (p : ℝ) := by exact_mod_cast p.prop.one_lt
  refine ContinuousLinearMap.ext fun f => ?_
  set u : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) := gaussPrimeScaleBlock hp f with hu
  set v : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) :=
    gaussDiagonalBlock hm k p (circleReflectionCLM u) with hv
  have hIv : circleReflectionCLM v = gaussDiagonalBlockStar hm k p u := by
    have h1 := congrArg (fun T : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
        Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) => T u)
      (circleReflection_gaussDiagonalBlock_conj hm k p)
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply] at h1
    rw [hv]
    exact h1
  have hkey : circleReflectionCLM (gaussPrimeScaleBlock hp (gaussPrimeScaleBlock hp v))
      = ((p : ℝ) : ℂ) • gaussPrimeScaleInvSqBlock hp (circleReflectionCLM v) := by
    have h1 := congrArg (fun T : Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) →L[ℂ]
        Lp ℂ 2 (AddCircle.haarAddCircle (T := (1 : ℝ))) => T (circleReflectionCLM v))
      (circleReflection_gaussPrimeScaleSq_conj hp)
    simp only [ContinuousLinearMap.coe_comp, Function.comp_apply,
      ContinuousLinearMap.coe_smul', Pi.smul_apply] at h1
    rw [circleReflectionCLM_apply_self v] at h1
    exact h1
  have hCf : gaussPairedBlock hm k p f = gaussPrimeScaleBlock hp v := by
    simp only [gaussPairedBlock, ContinuousLinearMap.coe_comp, Function.comp_apply]
    rw [hv, hu]
  have hCC : gaussPairedBlock hm k p (gaussPairedBlock hm k p f)
      = gaussPrimeScaleBlock hp (gaussDiagonalBlock hm k p
          (circleReflectionCLM (gaussPrimeScaleBlock hp (gaussPrimeScaleBlock hp v)))) := by
    rw [hCf]
    simp only [gaussPairedBlock, ContinuousLinearMap.coe_comp, Function.comp_apply]
  rw [ContinuousLinearMap.coe_comp, Function.comp_apply, hCC, hkey, hIv]
  rw [gaussQuasiInnerG]
  simp only [ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.coe_comp,
    Function.comp_apply, map_smul]
  rw [hu]

end

end RHTower