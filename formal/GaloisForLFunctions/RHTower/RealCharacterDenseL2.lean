import GaloisForLFunctions.RHTower.DenseSpanDuality
import GaloisForLFunctions.RHTower.CyclicRadicalCollapse
import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Real Fourier characters are dense in finite-measure `L²`

This module formalizes the finite-measure character-uniqueness input needed
for the `L²` Wiener cyclicity of the Hedenmalm theta source.
-/

open Complex MeasureTheory Set
open scoped ENNReal

namespace RHTower

noncomputable section

/-- The probability-character convention used by `Measure.charFun`. -/
def realProbCharacter (t x : ℝ) : ℂ :=
  Complex.exp (((t * x : ℝ) : ℂ) * Complex.I)

@[simp] theorem norm_realProbCharacter (t x : ℝ) :
    ‖realProbCharacter t x‖ = 1 := by
  rw [realProbCharacter, Complex.norm_exp]
  simp

theorem memLp_realProbCharacter (mu : Measure ℝ) [IsFiniteMeasure mu] (t : ℝ) :
    MemLp (realProbCharacter t) 2 mu := by
  refine MemLp.of_bound (p := 2)
    (show AEStronglyMeasurable (realProbCharacter t) mu from
      (by unfold realProbCharacter; fun_prop : Continuous (realProbCharacter t)).aestronglyMeasurable)
    1 ?_
  filter_upwards with x
  simp

/-- A real Fourier character as an element of finite-measure `L²`. -/
def realProbCharacterLp (mu : Measure ℝ) [IsFiniteMeasure mu] (t : ℝ) :
    Lp ℂ 2 mu :=
  (memLp_realProbCharacter mu t).toLp _

theorem realProbCharacterLp_ae (mu : Measure ℝ) [IsFiniteMeasure mu] (t : ℝ) :
    realProbCharacterLp mu t =ᵐ[mu] realProbCharacter t :=
  (memLp_realProbCharacter mu t).coeFn_toLp

/-- Uniqueness for a real integrable density: if every probability-character
moment vanishes, then the density vanishes almost everywhere. -/
theorem ae_eq_zero_of_integral_realProbCharacter_mul_eq_zero
    (mu : Measure ℝ) [IsFiniteMeasure mu] {f : ℝ → ℝ}
    (hfmeas : Measurable f) (hf : Integrable f mu)
    (hfourier : ∀ t : ℝ,
      ∫ x, realProbCharacter t x * (f x : ℂ) ∂mu = 0) :
    f =ᵐ[mu] 0 := by
  let mup : Measure ℝ := mu.withDensity (fun x ↦ ENNReal.ofReal (f x))
  let mun : Measure ℝ := mu.withDensity (fun x ↦ ENNReal.ofReal (-f x))
  letI : IsFiniteMeasure mup :=
    isFiniteMeasure_withDensity_ofReal hf.hasFiniteIntegral
  letI : IsFiniteMeasure mun :=
    isFiniteMeasure_withDensity_ofReal hf.neg.hasFiniteIntegral
  have hchar : charFun mup = charFun mun := by
    funext t
    rw [charFun_apply_real, charFun_apply_real]
    rw [integral_withDensity_eq_integral_toReal_smul₀
      hfmeas.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    rw [integral_withDensity_eq_integral_toReal_smul₀
      hfmeas.neg.ennreal_ofReal.aemeasurable
      (Filter.Eventually.of_forall fun _ ↦ ENNReal.ofReal_lt_top)]
    simp_rw [ENNReal.toReal_ofReal']
    have hp : Integrable (fun x ↦
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * (max (f x) 0 : ℝ)) mu := by
      have hpos : Integrable (fun x ↦ max (f x) 0) mu :=
        ⟨(hfmeas.max measurable_const).aestronglyMeasurable,
          hf.hasFiniteIntegral.max_zero⟩
      exact hpos.ofReal.bdd_mul (c := 1)
        (by fun_prop : Continuous (fun x : ℝ ↦
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I))).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x ↦ by
          rw [Complex.norm_exp]
          simp)
    have hn : Integrable (fun x ↦
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * (max (-f x) 0 : ℝ)) mu := by
      have hneg : Integrable (fun x ↦ max (-f x) 0) mu :=
        ⟨(hfmeas.neg.max measurable_const).aestronglyMeasurable,
          hf.neg.hasFiniteIntegral.max_zero⟩
      exact hneg.ofReal.bdd_mul (c := 1)
        (by fun_prop : Continuous (fun x : ℝ ↦
          Complex.exp (((t * x : ℝ) : ℂ) * Complex.I))).aestronglyMeasurable
        (Filter.Eventually.of_forall fun x ↦ by
          rw [Complex.norm_exp]
          simp)
    have hz := hfourier t
    have hsplit : (fun x ↦
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * (f x : ℂ)) =
      fun x ↦
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * (max (f x) 0 : ℝ) -
        Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * (max (-f x) 0 : ℝ) := by
      funext x
      push_cast
      rw [← mul_sub]
      congr 1
      exact_mod_cast (max_zero_sub_max_neg_zero_eq_self (f x)).symm
    rw [show (fun x ↦ realProbCharacter t x * (f x : ℂ)) =
      (fun x ↦ Complex.exp (((t * x : ℝ) : ℂ) * Complex.I) * (f x : ℂ)) by
        funext x; rfl, hsplit, integral_sub hp hn] at hz
    simpa [smul_eq_mul, mul_comm] using (sub_eq_zero.mp hz)
  have heq : mup = mun := Measure.ext_of_charFun hchar
  have hsing : mup ⟂ₘ mun := by
    exact withDensity_ofReal_mutuallySingular hfmeas
  have hself : mup ⟂ₘ mup := by simpa [heq] using hsing
  have hmup : mup = 0 := by
    have := hself.disjoint
    simpa using this
  have hmun : mun = 0 := by rw [← heq, hmup]
  have hpzero : (fun x ↦ ENNReal.ofReal (f x)) =ᵐ[mu] (fun _ ↦ 0) :=
    (withDensity_eq_zero_iff hfmeas.ennreal_ofReal.aemeasurable).mp hmup
  have hnzero : (fun x ↦ ENNReal.ofReal (-f x)) =ᵐ[mu] (fun _ ↦ 0) :=
    (withDensity_eq_zero_iff hfmeas.neg.ennreal_ofReal.aemeasurable).mp hmun
  filter_upwards [hpzero, hnzero] with x hpx hnx
  have hle : f x ≤ 0 := by simpa using hpx
  have hge : 0 ≤ f x := by simpa using hnx
  exact le_antisymm hle hge

/-- Fourier conjugation for a real integrable density. -/
theorem integral_realProbCharacter_neg_mul_ofReal
    (mu : Measure ℝ) {f : ℝ → ℝ} (_hf : Integrable f mu) (t : ℝ) :
    ∫ x, realProbCharacter (-t) x * (f x : ℂ) ∂mu =
      starRingEnd ℂ (∫ x, realProbCharacter t x * (f x : ℂ) ∂mu) := by
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards with x
  simp [realProbCharacter, ← Complex.exp_conj]

/-- Uniqueness for a complex integrable density. -/
theorem ae_eq_zero_of_integral_realProbCharacter_mul_eq_zero_complex
    (mu : Measure ℝ) [IsFiniteMeasure mu] {f : ℝ → ℂ}
    (hfmeas : Measurable f) (hf : Integrable f mu)
    (hfourier : ∀ t : ℝ,
      ∫ x, realProbCharacter t x * f x ∂mu = 0) :
    f =ᵐ[mu] 0 := by
  let fr : ℝ → ℝ := fun x ↦ (f x).re
  let fi : ℝ → ℝ := fun x ↦ (f x).im
  have hfrmeas : Measurable fr := Complex.measurable_re.comp hfmeas
  have hfimeas : Measurable fi := Complex.measurable_im.comp hfmeas
  have hfrint : Integrable fr mu := hf.re
  have hfiint : Integrable fi mu := hf.im
  have hphaseMeas (s : ℝ) : AEStronglyMeasurable (realProbCharacter s) mu :=
    ((by unfold realProbCharacter; fun_prop : Continuous (realProbCharacter s))).aestronglyMeasurable
  have hphaseBound (s : ℝ) : ∀ᵐ x ∂mu, ‖realProbCharacter s x‖ ≤ 1 :=
    Filter.Eventually.of_forall fun x ↦ by simp
  have hfrzero : ∀ t : ℝ,
      ∫ x, realProbCharacter t x * (fr x : ℂ) ∂mu = 0 := by
    intro t
    let A : ℂ := ∫ x, realProbCharacter t x * (fr x : ℂ) ∂mu
    let B : ℂ := ∫ x, realProbCharacter t x * (fi x : ℂ) ∂mu
    have hAr : Integrable (fun x ↦ realProbCharacter t x * (fr x : ℂ)) mu :=
      hfrint.ofReal.bdd_mul (c := 1)
        (hphaseMeas t) (hphaseBound t)
    have hBi : Integrable (fun x ↦ realProbCharacter t x * (fi x : ℂ)) mu :=
      hfiint.ofReal.bdd_mul (c := 1)
        (hphaseMeas t) (hphaseBound t)
    have hplus : A + Complex.I * B = 0 := by
      have hz := hfourier t
      have hpoint : (fun x ↦ realProbCharacter t x * f x) =
          fun x ↦ realProbCharacter t x * (fr x : ℂ) +
            Complex.I * (realProbCharacter t x * (fi x : ℂ)) := by
        funext x
        apply Complex.ext
        · simp [fr, fi, realProbCharacter, Complex.mul_re, Complex.mul_im]
          ring
        · simp [fr, fi, realProbCharacter, Complex.mul_re, Complex.mul_im]
          ring
      rw [hpoint, integral_add hAr (hBi.const_mul Complex.I), integral_const_mul] at hz
      exact hz
    have hminus : A - Complex.I * B = 0 := by
      have hz := hfourier (-t)
      have hpoint : (fun x ↦ realProbCharacter (-t) x * f x) =
          fun x ↦ realProbCharacter (-t) x * (fr x : ℂ) +
            Complex.I * (realProbCharacter (-t) x * (fi x : ℂ)) := by
        funext x
        apply Complex.ext
        · simp [fr, fi, realProbCharacter, Complex.mul_re, Complex.mul_im]
          ring
        · simp [fr, fi, realProbCharacter, Complex.mul_re, Complex.mul_im]
          ring
      have hArneg : Integrable
          (fun x ↦ realProbCharacter (-t) x * (fr x : ℂ)) mu :=
        hfrint.ofReal.bdd_mul (c := 1)
          (hphaseMeas (-t)) (hphaseBound (-t))
      have hBineg : Integrable
          (fun x ↦ realProbCharacter (-t) x * (fi x : ℂ)) mu :=
        hfiint.ofReal.bdd_mul (c := 1)
          (hphaseMeas (-t)) (hphaseBound (-t))
      rw [hpoint, integral_add hArneg (hBineg.const_mul Complex.I),
        integral_const_mul,
        integral_realProbCharacter_neg_mul_ofReal mu hfrint,
        integral_realProbCharacter_neg_mul_ofReal mu hfiint] at hz
      have hzconj := congrArg (starRingEnd ℂ) hz
      dsimp [A, B]
      simpa using hzconj
    have htwoA : (2 : ℂ) * A = 0 := by
      calc
        (2 : ℂ) * A = (A + Complex.I * B) + (A - Complex.I * B) := by ring
        _ = 0 := by rw [hplus, hminus]; simp
    exact (mul_eq_zero.mp htwoA).resolve_left (by norm_num)
  have hfizero : ∀ t : ℝ,
      ∫ x, realProbCharacter t x * (fi x : ℂ) ∂mu = 0 := by
    intro t
    have hfr := hfrzero t
    have hz := hfourier t
    have hAr : Integrable (fun x ↦ realProbCharacter t x * (fr x : ℂ)) mu :=
      hfrint.ofReal.bdd_mul (c := 1)
        (hphaseMeas t) (hphaseBound t)
    have hBi : Integrable (fun x ↦ realProbCharacter t x * (fi x : ℂ)) mu :=
      hfiint.ofReal.bdd_mul (c := 1)
        (hphaseMeas t) (hphaseBound t)
    have hpoint : (fun x ↦ realProbCharacter t x * f x) =
        fun x ↦ realProbCharacter t x * (fr x : ℂ) +
          Complex.I * (realProbCharacter t x * (fi x : ℂ)) := by
      funext x
      apply Complex.ext
      · simp [fr, fi, realProbCharacter, Complex.mul_re, Complex.mul_im]
        ring
      · simp [fr, fi, realProbCharacter, Complex.mul_re, Complex.mul_im]
        ring
    rw [hpoint, integral_add hAr (hBi.const_mul Complex.I), integral_const_mul] at hz
    rw [hfr, zero_add] at hz
    exact (mul_eq_zero.mp hz).resolve_left Complex.I_ne_zero
  have hfre := ae_eq_zero_of_integral_realProbCharacter_mul_eq_zero mu hfrmeas hfrint hfrzero
  have hfim := ae_eq_zero_of_integral_realProbCharacter_mul_eq_zero mu hfimeas hfiint hfizero
  filter_upwards [hfre, hfim] with x hxre hxim
  apply Complex.ext
  · simpa [fr] using hxre
  · simpa [fi] using hxim

/-- The real probability characters have dense complex linear span in `L²`
of every finite Borel measure on the real line. -/
theorem isCyclicFamily_realProbCharacterLp
    (mu : Measure ℝ) [IsFiniteMeasure mu] :
    IsCyclicFamily (𝕜 := ℂ) (realProbCharacterLp mu) := by
  apply dense_span_of_forall_dual_eq_zero
  intro L hL
  let g : Lp ℂ 2 mu := (InnerProductSpace.toDual ℂ (Lp ℂ 2 mu)).symm L
  have hinner (t : ℝ) : inner ℂ g (realProbCharacterLp mu t) = 0 := by
    have h := hL t
    change L (realProbCharacterLp mu t) = 0 at h
    simpa [g, InnerProductSpace.toDual_symm_apply] using h
  have hgOne : Integrable (fun x : ℝ ↦ g x) mu := by
    rw [← memLp_one_iff_integrable]
    exact (Lp.memLp g).mono_exponent (by norm_num)
  have hgStarMeas : Measurable (fun x : ℝ ↦ (starRingEnd ℂ) (g x)) := by
    exact Complex.continuous_conj.comp_measurable g.stronglyMeasurable.measurable
  have hgStarInt : Integrable (fun x : ℝ ↦ (starRingEnd ℂ) (g x)) mu :=
    hgOne.conj
  have hfourier (t : ℝ) :
      ∫ x, realProbCharacter t x * (starRingEnd ℂ) (g x) ∂mu = 0 := by
    have ht := hinner t
    rw [L2.inner_def] at ht
    have hpoint :
        (fun x : ℝ ↦ inner ℂ (g x) (realProbCharacterLp mu t x)) =ᵐ[mu]
          fun x ↦ realProbCharacter t x * (starRingEnd ℂ) (g x) := by
      filter_upwards [realProbCharacterLp_ae mu t] with x hx
      rw [hx]
      simp [mul_comm]
    rw [integral_congr_ae hpoint] at ht
    exact ht
  have hgStarZero :=
    ae_eq_zero_of_integral_realProbCharacter_mul_eq_zero_complex
      mu hgStarMeas hgStarInt hfourier
  have hgZero : g = 0 := by
    apply Lp.ext
    filter_upwards [hgStarZero] with x hx
    have := congrArg (starRingEnd ℂ) hx
    simpa using this
  calc
    L = (InnerProductSpace.toDual ℂ (Lp ℂ 2 mu)) g := by
      symm
      exact (InnerProductSpace.toDual ℂ (Lp ℂ 2 mu)).apply_symm_apply L
    _ = 0 := by rw [hgZero]; simp

end

end RHTower
