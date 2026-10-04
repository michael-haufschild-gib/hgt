import GaloisForLFunctions.RHTower.ChiRamanujanWeightedCubicTrace
import Mathlib.Analysis.Complex.LocallyUniformLimit
/-!
# Complete weighted cubic contractions and literal axis exclusion

Each valuation-axis sum has an exact two-zeta factorization, with a normally
convergent correction through the critical plane. The complete correction
has value one and derivative zero at frequency zero. The derivative is
proved after the infinite product via locally uniform derivative convergence.

`weightedOffAxesTrace` removes both zero valuation vectors in the full signed
sum. Its exact complete limit retains the six-zeta trace minus both full
axis transforms, restoring their common origin. Nothing here identifies
these arithmetic axes with physical prime diagonals or takes the singular
critical distributional limit.
-/

noncomputable section
open scoped BigOperators Topology
namespace RHTower.BAGTrace

def axisEuler (z x : ℂ) : ℂ := (1-x)⁻¹ + z^2/(1-z)^2*x⁻¹

def axisRegularFactor (z U : ℂ) : ℂ := 1-z^2*(1-U⁻¹)^2/(1-z)^2

theorem weightedAxis_hasSum (z y : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun i : ℤ => weightedLocal z x y (i,0)) (axisEuler z x) := by
  have h := (complexGeometric_hasSum hx).add
    ((complexAtom_hasSum (-1)).mul_left (z^2/(1-z)^2*x⁻¹))
  convert h using 1 <;> try rfl
  · funext i
    rw [weightedLocal_decomposition]
    simp [complexGeometric, complexAtom, complexTail]
  · simp [axisEuler]

theorem axisEuler_eq_regularFactor {z U : ℂ} (hU : U ≠ 0)
    (h1 : 1-z ≠ 0) (hx : 1-z*U ≠ 0) (hxi : 1-z/U ≠ 0) :
    axisEuler z (z*U) = axisRegularFactor z U / ((1-z*U)*(1-z/U)) := by
  have hu' : U-z ≠ 0 := by
    rw [show U-z=U*(1-z/U) by field_simp]
    exact mul_ne_zero hU hxi
  unfold axisEuler axisRegularFactor
  field_simp [hu']
  ring

def axisPrimeFactor (p : Nat.Primes) (σ α : ℂ) : ℂ :=
  axisRegularFactor (cubicPrimeBase p σ) (cubicPrimeBase p α)

def axisEulerCorrection (σ α : ℂ) : ℂ := ∏' p, axisPrimeFactor p σ α

def axisTube : Set (ℂ × ℂ) := {w | 7/8 < w.1.re ∧ |w.2.re| < 1/16}

def axisMajorant : ℝ := 4/(1-(2 : ℝ)^(-(3/4) : ℝ))^2

theorem norm_axisRegularFactor_sub_one_le {z U : ℂ} {a r c : ℝ}
    (hr : 1 ≤ r) (hc : c < 1) (hz : ‖z‖ ≤ a) (hzc : ‖z‖ ≤ c)
    (hUi : ‖U⁻¹‖ ≤ r) : ‖axisRegularFactor z U-1‖ ≤ 4*a^2*r^2/(1-c)^2 := by
  have hc0 : 0 < 1-c := sub_pos.mpr hc
  have hu1 : ‖1-U⁻¹‖ ≤ 2*r := by
    have h := norm_sub_le (1 : ℂ) U⁻¹
    rw [norm_one] at h
    linarith
  have hd : 1-c ≤ ‖1-z‖ := by
    have h := norm_sub_norm_le (1 : ℂ) z
    rw [norm_one] at h
    linarith
  have hden : (1-c)^2 ≤ ‖(1-z)^2‖ := by rw [norm_pow]; gcongr
  have hnum : ‖z^2*(1-U⁻¹)^2‖ ≤ 4*a^2*r^2 := by
    simp only [norm_mul, norm_pow]
    calc
      _ ≤ a^2*(2*r)^2 := by gcongr
      _ = _ := by ring
  unfold axisRegularFactor
  rw [sub_sub_cancel_left, norm_neg, norm_div]
  exact (div_le_div_of_nonneg_right hnum (norm_nonneg _)).trans
    (div_le_div_of_nonneg_left (by positivity) (by positivity) hden)

theorem norm_axisPrimeFactor_sub_one_le (p : Nat.Primes) {σ α : ℂ}
    (hσ : 7/8 ≤ σ.re) (hα : |α.re| ≤ 1/16) :
    ‖axisPrimeFactor p σ α-1‖ ≤ axisMajorant * (p : ℝ)^(-(13/8) : ℝ) := by
  let a : ℝ := (p : ℝ)^(-(7/8) : ℝ)
  let r : ℝ := (p : ℝ)^((1/16) : ℝ)
  let c : ℝ := (2 : ℝ)^(-(3/4) : ℝ)
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.property.pos
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast p.property.one_lt.le
  have hr : 1 ≤ r := Real.one_le_rpow hp1 (by norm_num)
  have hc : c < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hzc : ‖cubicPrimeBase p σ‖ ≤ c :=
    (norm_cubicPrimeBase_le (by linarith : (3/4 : ℝ) ≤ σ.re)).trans
      (Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast p.property.two_le) (by norm_num))
  have hz : ‖cubicPrimeBase p σ‖ ≤ a := norm_cubicPrimeBase_le hσ
  have hUi : ‖(cubicPrimeBase p α)⁻¹‖ ≤ r := by
    rw [cubicPrimeBase_inv]
    simpa only [neg_neg] using norm_cubicPrimeBase_le (p := p) (s := -α)
      (a := -(1/16)) (by simpa only [Complex.neg_re, neg_le_neg_iff] using le_of_abs_le hα)
  have h := norm_axisRegularFactor_sub_one_le hr hc hz hzc hUi
  refine h.trans_eq ?_
  have hpow : a^2*r^2 = (p : ℝ)^(-(13/8) : ℝ) := by
    dsimp [a,r]
    rw [← Real.rpow_mul_natCast hp0.le, ← Real.rpow_mul_natCast hp0.le, ← Real.rpow_add hp0]
    congr 1
    norm_num
  dsimp [axisMajorant, c]
  rw [← hpow]
  ring

theorem isOpen_axisTube : IsOpen axisTube :=
  (isOpen_lt continuous_const (Complex.continuous_re.comp continuous_fst)).inter
    (isOpen_lt ((Complex.continuous_re.comp continuous_snd).abs) continuous_const)

theorem differentiableOn_axisPrimeFactor (p : Nat.Primes) :
    DifferentiableOn ℂ (fun w : ℂ × ℂ => axisPrimeFactor p w.1 w.2) axisTube := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hz : Differentiable ℂ (fun w : ℂ × ℂ => cubicPrimeBase p w.1) :=
    differentiable_fst.neg.const_cpow (.inl hp0)
  have hu : Differentiable ℂ (fun w : ℂ × ℂ => cubicPrimeBase p w.2) :=
    differentiable_snd.neg.const_cpow (.inl hp0)
  have hui := hu.differentiableOn.inv (S := axisTube) (fun w _ => cubicPrimeBase_ne_zero p w.2)
  have hd := ((differentiableOn_const (s := axisTube) 1).sub hz.differentiableOn).pow 2
  have hi := hd.inv (fun w hw => pow_ne_zero 2
    (one_sub_cubicPrimeBase_ne_zero p (lt_trans (by norm_num) hw.1)))
  convert (differentiableOn_const 1).sub
    (((hz.differentiableOn.pow 2).mul (((differentiableOn_const 1).sub hui).pow 2)).mul hi)
      using 1 <;> try rfl

theorem hasProdLocallyUniformlyOn_axisPrimeFactor :
    HasProdLocallyUniformlyOn
      (fun p : Nat.Primes => fun w : ℂ × ℂ => axisPrimeFactor p w.1 w.2)
      (fun w => axisEulerCorrection w.1 w.2) axisTube := by
  have hpow : Summable (fun p : Nat.Primes => (p : ℝ)^(-(13/8) : ℝ)) :=
    (Real.summable_nat_rpow.mpr (by norm_num : (-(13/8) : ℝ) < -1)).subtype Nat.Prime
  have h := Summable.hasProdLocallyUniformlyOn_one_add isOpen_axisTube
    (hpow.mul_left axisMajorant)
    (f := fun p : Nat.Primes => fun w : ℂ × ℂ => axisPrimeFactor p w.1 w.2-1)
    (.of_forall (fun p w hw => norm_axisPrimeFactor_sub_one_le p hw.1.le hw.2.le))
    (fun p => (differentiableOn_axisPrimeFactor p).continuousOn.sub continuousOn_const)
  simpa only [add_sub_cancel, axisEulerCorrection] using h

theorem axisEulerCorrection_zero (σ : ℂ) : axisEulerCorrection σ 0 = 1 := by
  simp [axisEulerCorrection, axisPrimeFactor, axisRegularFactor, cubicPrimeBase]

def weightedAxisTrace (σ α : ℂ) (P : Finset Nat.Primes) : ℂ :=
  ∑' v : P → ℤ, ∏ p : P,
    weightedLocal (cubicPrimeBase p σ) (cubicPrimeBase p (σ+α)) 1 (v p,0)

theorem weightedAxisTrace_eq {σ α : ℂ} (hα : 0 < (σ+α).re)
    (P : Finset Nat.Primes) : weightedAxisTrace σ α P =
      ∏ p ∈ P, axisEuler (cubicPrimeBase p σ) (cubicPrimeBase p (σ+α)) := by
  have hn (p : Nat.Primes) : ‖cubicPrimeBase p (σ+α)‖ < 1 := by
    rw [norm_cubicPrimeBase]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.property.one_lt) (neg_neg_of_pos hα)
  exact (complex_finite_product_hasSum P
    (fun p i => weightedLocal (cubicPrimeBase p σ) (cubicPrimeBase p (σ+α)) 1 (i,0))
    (fun p => axisEuler (cubicPrimeBase p σ) (cubicPrimeBase p (σ+α)))
    (fun p => weightedAxis_hasSum _ _ (hn p))).tsum_eq.trans
      (Finset.prod_coe_sort P (fun p => axisEuler (cubicPrimeBase p σ) (cubicPrimeBase p (σ+α))))

private theorem axisEuler_prime_eq (p : Nat.Primes) {σ α : ℂ}
    (hσ : 1 < σ.re) (hα : α.re = 0) :
    axisEuler (cubicPrimeBase p σ) (cubicPrimeBase p (σ+α)) =
      axisPrimeFactor p σ α * (1-cubicPrimeBase p (σ+α))⁻¹ *
        (1-cubicPrimeBase p (σ-α))⁻¹ := by
  have hpos : 0 < σ.re := lt_trans zero_lt_one hσ
  have hx : 1-cubicPrimeBase p σ*cubicPrimeBase p α ≠ 0 := by
    rw [cubicPrimeBase_mul]
    exact one_sub_cubicPrimeBase_ne_zero p (by simpa [hα] using hpos)
  have hxi : 1-cubicPrimeBase p σ/cubicPrimeBase p α ≠ 0 := by
    rw [cubicPrimeBase_div]
    exact one_sub_cubicPrimeBase_ne_zero p (by simpa [hα] using hpos)
  have h := axisEuler_eq_regularFactor (cubicPrimeBase_ne_zero p α) (one_sub_cubicPrimeBase_ne_zero p hpos) hx hxi
  simp only [cubicPrimeBase_div, cubicPrimeBase_mul] at h
  rw [h]
  simp only [axisPrimeFactor, div_eq_mul_inv, mul_inv_rev]
  ring

theorem complete_weighted_axis_two_zeta {σ α : ℂ}
    (hσ : 1 < σ.re) (hα : α.re = 0) :
    Filter.Tendsto (weightedAxisTrace σ α) Filter.atTop
      (𝓝 (axisEulerCorrection σ α * riemannZeta (σ+α) * riemannZeta (σ-α))) := by
  have hmem : (σ,α) ∈ axisTube := ⟨by linarith, by simp [hα]⟩
  have hz (s : ℂ) (hs : s.re = σ.re) :
      HasProd (fun p : Nat.Primes => (1-cubicPrimeBase p s)⁻¹) (riemannZeta s) :=
    riemannZeta_eulerProduct_hasProd (hs ▸ hσ)
  have h := ((hasProdLocallyUniformlyOn_axisPrimeFactor.hasProd hmem).mul
    (hz (σ+α) (by simp [hα]))).mul (hz (σ-α) (by simp [hα]))
  have h' := h.congr_fun (fun p => axisEuler_prime_eq p hσ hα)
  have ha : 0 < (σ+α).re := by simp only [Complex.add_re, hα, add_zero]; linarith
  change Filter.Tendsto (fun P => weightedAxisTrace σ α P) _ _
  simpa only [HasProd, SummationFilter.unconditional, weightedAxisTrace_eq ha] using h'

private theorem complex_remove_axes_hasSum {X : Type} [Zero X] [DecidableEq X]
    {f : X × X → ℂ} {A B C : ℂ} (h : HasSum f A)
    (hl : HasSum (fun x => f (0,x)) B) (hr : HasSum (fun x => f (x,0)) C) :
    HasSum (fun v => if v.1 = 0 ∨ v.2 = 0 then 0 else f v) (A-B-C+f (0,0)) := by
  have hm {Y Z : Type} {a : Y → ℂ} {b : Z → ℂ} {x y : ℂ}
      (ha : HasSum a x) (hb : HasSum b y) :
      HasSum (fun v : Y × Z => a v.1*b v.2) (x*y) :=
    ha.mul hb (summable_mul_of_summable_norm ha.summable.norm hb.summable.norm)
  have hd := hasSum_ite_eq (0 : X) (1 : ℂ)
  have h' := ((h.sub (hm hd hl)).sub (hm hr hd)).add ((hm hd hd).mul_left (f (0,0)))
  simp only [one_mul, mul_one] at h'
  refine h'.congr_fun ?_
  intro v
  rcases v with ⟨x,y⟩
  by_cases hx : x = 0 <;> by_cases hy : y = 0 <;> simp [hx,hy]

def weightedOffAxesTrace (σ α β : ℂ) (P : Finset Nat.Primes) : ℂ := by
  classical
  exact ∑' v : (P → ℤ) × (P → ℤ),
    if v.1 = 0 ∨ v.2 = 0 then 0 else ∏ p : P,
      weightedLocal (cubicPrimeBase p σ) (cubicPrimeBase p (σ+α))
        (cubicPrimeBase p (σ+β)) (v.1 p,v.2 p)

/-- Literal removal of both valuation-vector axes, with their common origin restored once. -/
theorem weightedOffAxesTrace_eq {σ α β : ℂ}
    (hα : 0 < (σ+α).re) (hβ : 0 < (σ+β).re) (P : Finset Nat.Primes) :
    weightedOffAxesTrace σ α β P =
      weightedTrace σ α β P - weightedAxisTrace σ β P - weightedAxisTrace σ α P + 1 := by
  classical
  let f : (P → ℤ) × (P → ℤ) → ℂ := fun v => ∏ p : P,
    weightedLocal (cubicPrimeBase p σ) (cubicPrimeBase p (σ+α))
      (cubicPrimeBase p (σ+β)) (v.1 p,v.2 p)
  have hn (p : Nat.Primes) (s : ℂ) (hs : 0 < s.re) : ‖cubicPrimeBase p s‖ < 1 := by
    rw [norm_cubicPrimeBase]
    exact Real.rpow_lt_one_of_one_lt_of_neg
      (by exact_mod_cast p.property.one_lt) (neg_neg_of_pos hs)
  have hfinit := complex_finite_product_hasSum P
    (fun p => weightedLocal (cubicPrimeBase p σ) (cubicPrimeBase p (σ+α))
      (cubicPrimeBase p (σ+β)))
    (fun p => weightedEuler (cubicPrimeBase p σ) (cubicPrimeBase p (σ+α))
      (cubicPrimeBase p (σ+β)))
    (fun p => weightedLocal_hasSum _ (hn _ _ hα) (hn _ _ hβ))
  have hf : HasSum f (weightedTrace σ α β P) :=
    ((Equiv.arrowProdEquivProdArrow P (fun _ => ℤ) (fun _ => ℤ)).hasSum_iff
      (f := f)).mp hfinit.summable.hasSum
  have hr := complex_finite_product_hasSum P
    (fun p i => weightedLocal (cubicPrimeBase p σ) (cubicPrimeBase p (σ+α))
      (cubicPrimeBase p (σ+β)) (i,0))
    (fun p => axisEuler (cubicPrimeBase p σ) (cubicPrimeBase p (σ+α)))
    (fun p => weightedAxis_hasSum _ _ (hn _ _ hα))
  have hl' := complex_finite_product_hasSum P
    (fun p i => weightedLocal (cubicPrimeBase p σ) (cubicPrimeBase p (σ+β))
      (cubicPrimeBase p (σ+α)) (i,0))
    (fun p => axisEuler (cubicPrimeBase p σ) (cubicPrimeBase p (σ+β)))
    (fun p => weightedAxis_hasSum _ _ (hn _ _ hβ))
  have hl : HasSum (fun x => f (0,x))
      (∏ p : P, axisEuler (cubicPrimeBase p σ) (cubicPrimeBase p (σ+β))) := by
    refine hl'.congr_fun fun x => ?_
    apply Finset.prod_congr rfl
    intro p hp
    simp [weightedLocal, mul_comm]
  have h00 : f (0,0) = 1 := by simp [f, weightedLocal, complexCoefficient]
  have hmask := complex_remove_axes_hasSum hf hl hr
  rw [h00, Finset.prod_coe_sort P (fun p : Nat.Primes =>
    axisEuler (cubicPrimeBase p σ) (cubicPrimeBase p (σ+β))),
    Finset.prod_coe_sort P (fun p : Nat.Primes =>
    axisEuler (cubicPrimeBase p σ) (cubicPrimeBase p (σ+α))),
    ← weightedAxisTrace_eq hα, ← weightedAxisTrace_eq hβ] at hmask
  exact hmask.tsum_eq

/-- Complete signed trace after literal arithmetic-axis subtraction. This retains all
weighted frequencies; matching these axes to physical prime diagonals remains separate. -/
theorem complete_weighted_offAxes_trace {σ α β : ℂ}
    (hσ : 1 < σ.re) (hα : α.re = 0) (hβ : β.re = 0) :
    Filter.Tendsto (weightedOffAxesTrace σ α β) Filter.atTop
      (𝓝 (cubicEulerCorrection σ α β *
        ((riemannZeta (σ+(β-α)))⁻¹ * (riemannZeta (σ+(α-β)))⁻¹) *
        riemannZeta (σ+α) * riemannZeta (σ+β) * riemannZeta (σ-α) * riemannZeta (σ-β) -
        axisEulerCorrection σ β * riemannZeta (σ+β) * riemannZeta (σ-β) -
        axisEulerCorrection σ α * riemannZeta (σ+α) * riemannZeta (σ-α) + 1)) := by
  have ha : 0 < (σ+α).re := by simp only [Complex.add_re, hα, add_zero]; linarith
  have hb : 0 < (σ+β).re := by simp only [Complex.add_re, hβ, add_zero]; linarith
  have h := (((complete_weighted_trace_six_zeta hσ hα hβ).sub
    (complete_weighted_axis_two_zeta hσ hβ)).sub
    (complete_weighted_axis_two_zeta hσ hα)).add
    (tendsto_const_nhds (x := (1 : ℂ)) (f := Filter.atTop))
  simpa only [show weightedOffAxesTrace σ α β =
    (fun P => weightedTrace σ α β P - weightedAxisTrace σ β P - weightedAxisTrace σ α P + 1)
      from funext (weightedOffAxesTrace_eq ha hb)] using h

def axisFrequencyDomain : Set ℂ := {α | |α.re| < 1/16}

theorem isOpen_axisFrequencyDomain : IsOpen axisFrequencyDomain :=
  isOpen_lt Complex.continuous_re.abs continuous_const

private theorem differentiableOn_axisSliceFactor (p : Nat.Primes) {σ : ℂ}
    (hσ : 7/8 < σ.re) : DifferentiableOn ℂ (axisPrimeFactor p σ) axisFrequencyDomain :=
  (differentiableOn_axisPrimeFactor p).comp (f := fun α : ℂ => (σ,α))
    ((differentiable_const σ).prodMk differentiable_id).differentiableOn
    (fun _ hα => ⟨hσ,hα⟩)

theorem hasProdLocallyUniformlyOn_axisSlice {σ : ℂ} (hσ : 7/8 < σ.re) :
    HasProdLocallyUniformlyOn (fun p => axisPrimeFactor p σ)
      (axisEulerCorrection σ) axisFrequencyDomain := by
  exact hasProdLocallyUniformlyOn_axisPrimeFactor.comp (fun α : ℂ => (σ,α))
    (fun _ hα => ⟨hσ,hα⟩) (continuous_const.prodMk continuous_id).continuousOn

theorem hasDerivAt_axisPrimeFactor_zero (p : Nat.Primes) (σ : ℂ) :
    HasDerivAt (axisPrimeFactor p σ) 0 0 := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast p.property.ne_zero
  have hu : Differentiable ℂ (fun α : ℂ => cubicPrimeBase p α) :=
    differentiable_id.neg.const_cpow (.inl hp0)
  have hui := hu.inv (fun α => cubicPrimeBase_ne_zero p α)
  have h2 : HasDerivAt (fun α : ℂ => (1-(cubicPrimeBase p α)⁻¹)^2) 0 0 := by
    convert ((hui.differentiableAt (x := (0 : ℂ))).hasDerivAt.const_sub 1).pow 2 using 1 <;> try rfl
    simp [cubicPrimeBase]
  have h := (h2.const_mul ((cubicPrimeBase p σ)^2/(1-cubicPrimeBase p σ)^2)).const_sub 1
  convert h using 1 <;> try rfl
  · funext α
    simp only [axisPrimeFactor, axisRegularFactor, div_eq_mul_inv]
    ring
  · ring

private theorem hasDerivAt_axisProduct_zero (σ : ℂ) (P : Finset Nat.Primes) :
    HasDerivAt (fun α => ∏ p ∈ P, axisPrimeFactor p σ α) 0 0 := by
  classical
  simpa only [smul_zero, Finset.sum_const_zero] using
    HasDerivAt.fun_finsetProd (u := P) (fun p _ => hasDerivAt_axisPrimeFactor_zero p σ)

/-- The complete contraction correction has a double zero after subtracting one.
This derivative is taken after the entire prime product, not at a fixed cutoff. -/
theorem hasDerivAt_axisEulerCorrection_zero {σ : ℂ} (hσ : 7/8 < σ.re) :
    HasDerivAt (axisEulerCorrection σ) 0 0 := by
  have hp := hasProdLocallyUniformlyOn_axisSlice hσ
  have hdiff (P : Finset Nat.Primes) :
      DifferentiableOn ℂ (fun α => ∏ p ∈ P, axisPrimeFactor p σ α) axisFrequencyDomain :=
    DifferentiableOn.fun_finsetProd (fun p _ => differentiableOn_axisSliceFactor p hσ)
  have h0 : (0 : ℂ) ∈ axisFrequencyDomain := by norm_num [axisFrequencyDomain]
  have hd := (hp.deriv (.of_forall hdiff) isOpen_axisFrequencyDomain).tendsto_at h0
  have hd0 : deriv (axisEulerCorrection σ) 0 = 0 := by
    have hlim : Filter.Tendsto (fun _ : Finset Nat.Primes => (0 : ℂ)) Filter.atTop
        (𝓝 (deriv (axisEulerCorrection σ) 0)) := by
      simpa only [Function.comp_apply, (hasDerivAt_axisProduct_zero σ _).deriv] using hd
    exact tendsto_nhds_unique hlim tendsto_const_nhds
  have hh := hp.differentiableOn (.of_forall hdiff) isOpen_axisFrequencyDomain
  simpa only [hd0] using (hh.differentiableAt (isOpen_axisFrequencyDomain.mem_nhds h0)).hasDerivAt

end RHTower.BAGTrace
