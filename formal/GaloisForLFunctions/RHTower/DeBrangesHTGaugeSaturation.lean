import GaloisForLFunctions.HTGeometry.DiscreteHermitePassport
import GaloisForLFunctions.HTGeometry.DifferentiallyAlgebraicExponentialPencil
import GaloisForLFunctions.RHTower.DeBrangesExplicitGammaGauge
import GaloisForLFunctions.Bottcher.AnalyticDomain
import GaloisForLFunctions.RHTower.LandauGinzburgNodeGerm

/-!
# Hypertranscendental gauge saturation of a de Branges spectral class

This module realizes arbitrary closed discrete Hermite passports, symmetrizes their entire carrier,
and uses Hölder's reciprocal-Gamma theorem plus an exponential pencil to obtain a Schwarz-real HT
exponent.  Its real exponential gauges form an injective continuum, are positive and zero-free on
the real axis, preserve every prescribed finite jet, and are HT for every nonzero parameter.

Multiplying any entire Hermite--Biehler function by these gauges preserves the inner quotient,
canonical spectra with analytic multiplicity, and kernel geometry.  At most one representative in
the fixed class is DA; when the base is DA, every nonzero-parameter representative is HT.
-/

namespace GaloisForLFunctions.RHTower

open Complex Filter Topology Set
open GaloisForLFunctions.HTGeometry

noncomputable section

theorem analyticOnNhd_suzukiEntireSharp {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F Set.univ) :
    AnalyticOnNhd ℂ (suzukiEntireSharp F) Set.univ := by
  rw [Complex.analyticOnNhd_univ_iff_differentiable]
  intro z
  have hFz := (hF (star z) (Set.mem_univ _)).differentiableAt
  change DifferentiableAt ℂ (star ∘ F ∘ (starRingEnd ℂ)) z
  simpa [Function.comp_def] using hFz.star_conj

theorem suzukiEntireSharp_involutive (F : ℂ → ℂ) (z : ℂ) :
    suzukiEntireSharp (suzukiEntireSharp F) z = F z := by
  simp [suzukiEntireSharp]

theorem schwarzReal_mul_sharp (F : ℂ → ℂ) :
    SchwarzRealGauge (fun z => F z * suzukiEntireSharp F z) := by
  intro z
  simp [suzukiEntireSharp, mul_comm]

theorem exists_ne_zero_mul_sharp {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F Set.univ) (hFne : ∃ z, F z ≠ 0) :
    ∃ z, F z * suzukiEntireSharp F z ≠ 0 := by
  have hFs := analyticOnNhd_suzukiEntireSharp hF
  have hFnot : ¬ Set.EqOn F 0 Set.univ := by
    obtain ⟨z, hz⟩ := hFne
    intro h
    exact hz (h (Set.mem_univ z))
  have hFsnot : ¬ Set.EqOn (suzukiEntireSharp F) 0 Set.univ := by
    obtain ⟨z, hz⟩ := hFne
    intro h
    have hzsharp := h (Set.mem_univ (star z))
    have hzsharp' : star (F z) = 0 := by
      simpa [suzukiEntireSharp] using hzsharp
    have hz' := congrArg star hzsharp'
    simp only [star_star, star_zero] at hz'
    exact hz hz'
  have hprod := Bottcher.analyticOnNhd_mul_ne_zero
    hF hFs isPreconnected_univ isOpen_univ hFnot hFsnot
  by_contra hnone
  push Not at hnone
  exact hprod (fun z _ => hnone z)

theorem analyticOrderAt_mul_sharp_ge_left {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F Set.univ) (z : ℂ) :
    analyticOrderAt F z ≤
      analyticOrderAt (fun w => F w * suzukiEntireSharp F w) z := by
  have hFs := analyticOnNhd_suzukiEntireSharp hF
  change analyticOrderAt F z ≤ analyticOrderAt (F * suzukiEntireSharp F) z
  rw [analyticOrderAt_mul (hF z (Set.mem_univ z)) (hFs z (Set.mem_univ z))]
  exact le_add_right le_rfl

theorem reciprocalGammaEntire_schwarzReal : SchwarzRealGauge reciprocalGammaEntire := by
  intro z
  rw [suzukiEntireSharp, ← reciprocalGammaEntire_conj]
  simp

theorem schwarzReal_entireExponentialPencil {W h : ℂ → ℂ}
    (hW : SchwarzRealGauge W) (hh : SchwarzRealGauge h) (t : ℝ) :
    SchwarzRealGauge (entireExponentialPencil W h (t : ℂ)) := by
  intro z
  rw [suzukiEntireSharp]
  change (starRingEnd ℂ) (W (star z) * Complex.exp ((t : ℂ) * h (star z))) =
    W z * Complex.exp ((t : ℂ) * h z)
  rw [map_mul, ← Complex.exp_conj, map_mul]
  have hWt := hW z
  have hht := hh z
  rw [suzukiEntireSharp] at hWt hht
  change star (W (star z)) = W z at hWt
  change star (h (star z)) = h z at hht
  have hWt' : (starRingEnd ℂ) (W (star z)) = W z := hWt
  have hht' : (starRingEnd ℂ) (h (star z)) = h z := hht
  rw [hWt', hht']
  simp

theorem analyticOrderAt_cexp_const_mul_sub_one {Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q Set.univ) {a c : ℂ} (hQa : Q a = 0) (hc : c ≠ 0) :
    analyticOrderAt (fun z => Complex.exp (c * Q z) - 1) a = analyticOrderAt Q a := by
  let f : ℂ → ℂ := fun w => Complex.exp (c * w) - 1
  have hf : AnalyticAt ℂ f 0 := by
    dsimp [f]
    fun_prop
  have hfroot : f 0 = 0 := by simp [f]
  have hfderiv : deriv f 0 = c := by
    have h := ((hasDerivAt_id (x := (0 : ℂ))).const_mul c).cexp.sub_const 1
    simpa [f] using h.deriv
  have hforder : analyticOrderAt f 0 = (1 : ℕ) := by
    rw [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero (hf := hf)]
    refine ⟨fun k hk => ?_, ?_⟩
    · interval_cases k
      simpa using hfroot
    · simpa [hfderiv] using hc
  have hfQa : AnalyticAt ℂ f (Q a) := by simpa [hQa] using hf
  have hcomp := hfQa.analyticOrderAt_comp (hQ a (Set.mem_univ a))
  change analyticOrderAt (f ∘ Q) a = _ at hcomp
  rw [hQa, hforder] at hcomp
  norm_num at hcomp
  simpa [f, Function.comp_def] using hcomp

/-- A Schwarz-real hypertranscendental exponent carrying every prescribed discrete zero jet. -/
theorem exists_symmetric_hypertranscendental_passport_exponent
    {S : Set ℂ} (hSd : IsDiscrete S) (hSc : IsClosed S) (m : S → ℕ) :
    ∃ Q : ℂ → ℂ,
      AnalyticOnNhd ℂ Q Set.univ ∧
      SchwarzRealGauge Q ∧
      Hypertranscendental Q ∧
      (∃ z, Q z ≠ 0) ∧
      ∀ a : S, (m a + 1 : ℕ∞) ≤ analyticOrderAt Q a := by
  obtain ⟨W₀, hW₀diff, hW₀ne, hW₀order⟩ :=
    exists_entire_prescribed_discrete_vanishing_nontrivial hSd hSc m
  have hW₀ : AnalyticOnNhd ℂ W₀ Set.univ := by
    rw [Complex.analyticOnNhd_univ_iff_differentiable]
    exact hW₀diff
  let W : ℂ → ℂ := fun z => W₀ z * suzukiEntireSharp W₀ z
  have hW : AnalyticOnNhd ℂ W Set.univ := by
    exact hW₀.mul (analyticOnNhd_suzukiEntireSharp hW₀)
  have hWsym : SchwarzRealGauge W := schwarzReal_mul_sharp W₀
  have hWne : ∃ z, W z ≠ 0 := exists_ne_zero_mul_sharp hW₀ hW₀ne
  obtain ⟨t, htHT⟩ := exists_real_hypertranscendental_entireExponentialPencil
    hW analyticOnNhd_reciprocalGammaEntire hWne
      FixedModulusRealRootedness.hypertranscendental_reciprocalGammaEntire
  let Q : ℂ → ℂ := entireExponentialPencil W reciprocalGammaEntire (t : ℂ)
  have hQ : AnalyticOnNhd ℂ Q Set.univ :=
    analyticOnNhd_entireExponentialPencil hW analyticOnNhd_reciprocalGammaEntire (t : ℂ)
  have hQsym : SchwarzRealGauge Q :=
    schwarzReal_entireExponentialPencil hWsym reciprocalGammaEntire_schwarzReal t
  have hQne : ∃ z, Q z ≠ 0 := by
    obtain ⟨z, hz⟩ := hWne
    exact ⟨z, entireExponentialPencil_ne_zero_value hz (t : ℂ)⟩
  refine ⟨Q, hQ, hQsym, htHT, hQne, fun a => ?_⟩
  have hleft : (m a + 1 : ℕ∞) ≤ analyticOrderAt W a :=
    (hW₀order a).trans (analyticOrderAt_mul_sharp_ge_left hW₀ a)
  have hexp : AnalyticOnNhd ℂ
      (fun z => Complex.exp ((t : ℂ) * reciprocalGammaEntire z)) Set.univ :=
    (analyticOnNhd_const.mul analyticOnNhd_reciprocalGammaEntire).cexp
  have hexpOrder : analyticOrderAt
      (fun z => Complex.exp ((t : ℂ) * reciprocalGammaEntire z)) a = 0 :=
    (hexp a (Set.mem_univ a)).analyticOrderAt_eq_zero.mpr (Complex.exp_ne_zero _)
  change (m a + 1 : ℕ∞) ≤ analyticOrderAt
    (W * fun z => Complex.exp ((t : ℂ) * reciprocalGammaEntire z)) a
  rw [analyticOrderAt_mul (hW a (Set.mem_univ a)) (hexp a (Set.mem_univ a)), hexpOrder,
    add_zero]
  exact hleft

/-- Positive zero-free gauge generated by a Schwarz-real exponent. -/
def htPassportGauge (Q : ℂ → ℂ) (c : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((c : ℂ) * Q z)

theorem analyticOnNhd_htPassportGauge {Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q Set.univ) (c : ℝ) :
    AnalyticOnNhd ℂ (htPassportGauge Q c) Set.univ :=
  (analyticOnNhd_const.mul hQ).cexp

theorem zeroFree_htPassportGauge (Q : ℂ → ℂ) (c : ℝ) :
    ZeroFreeGauge (htPassportGauge Q c) :=
  fun _ => Complex.exp_ne_zero _

theorem schwarzReal_htPassportGauge {Q : ℂ → ℂ}
    (hQ : SchwarzRealGauge Q) (c : ℝ) :
    SchwarzRealGauge (htPassportGauge Q c) := by
  intro z
  rw [suzukiEntireSharp]
  change (starRingEnd ℂ) (Complex.exp ((c : ℂ) * Q (star z))) =
    Complex.exp ((c : ℂ) * Q z)
  rw [← Complex.exp_conj, map_mul]
  have hQz := hQ z
  rw [suzukiEntireSharp] at hQz
  have hQz' : (starRingEnd ℂ) (Q (star z)) = Q z := hQz
  rw [hQz']
  simp

theorem hypertranscendental_htPassportGauge {Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q Set.univ) (hQHT : Hypertranscendental Q)
    {c : ℝ} (hc : c ≠ 0) :
    Hypertranscendental (htPassportGauge Q c) := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  exact (hypertranscendental_cexp_const_mul_iff hQ hcC).2 hQHT

theorem schwarzReal_value_ofReal {Q : ℂ → ℂ} (hQ : SchwarzRealGauge Q) (x : ℝ) :
    Q (x : ℂ) = ((Q (x : ℂ)).re : ℂ) := by
  have hx := hQ (x : ℂ)
  rw [suzukiEntireSharp] at hx
  have hstar : star (Q (x : ℂ)) = Q (x : ℂ) := by simpa using hx
  apply Complex.ext
  · simp
  · have him := congrArg Complex.im hstar
    change -(Q (x : ℂ)).im = (Q (x : ℂ)).im at him
    change (Q (x : ℂ)).im = 0
    linarith

theorem htPassportGauge_positive_real {Q : ℂ → ℂ}
    (hQ : SchwarzRealGauge Q) (c x : ℝ) :
    (htPassportGauge Q c (x : ℂ)).im = 0 ∧
      0 < (htPassportGauge Q c (x : ℂ)).re := by
  rw [htPassportGauge, schwarzReal_value_ofReal hQ x]
  have harg : (c : ℂ) * ((Q (x : ℂ)).re : ℂ) =
      ((c * (Q (x : ℂ)).re : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul]
  constructor
  · rw [harg, Complex.exp_ofReal_im]
  · rw [harg, Complex.exp_ofReal_re]
    exact Real.exp_pos _

theorem eq_zero_of_one_le_analyticOrderAt {F : ℂ → ℂ}
    (hF : AnalyticOnNhd ℂ F Set.univ) {a : ℂ}
    (horder : (1 : ℕ∞) ≤ analyticOrderAt F a) : F a = 0 := by
  by_contra hne
  have hzero := (hF a (Set.mem_univ a)).analyticOrderAt_eq_zero.mpr hne
  rw [hzero] at horder
  norm_num at horder

theorem analyticOrderAt_htPassportGauge_sub_one {Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q Set.univ) {a : ℂ}
    (hQa : Q a = 0) {c : ℝ} (hc : c ≠ 0) :
    analyticOrderAt (fun z => htPassportGauge Q c z - 1) a = analyticOrderAt Q a := by
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  exact analyticOrderAt_cexp_const_mul_sub_one hQ hQa hcC

theorem htPassportGauge_preserves_order {Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q Set.univ) {a : ℂ} {k : ℕ}
    (horder : (k + 1 : ℕ∞) ≤ analyticOrderAt Q a) {c : ℝ} (hc : c ≠ 0) :
    (k + 1 : ℕ∞) ≤ analyticOrderAt (fun z => htPassportGauge Q c z - 1) a := by
  have hpos : (1 : ℕ∞) ≤ analyticOrderAt Q a :=
    le_trans (by norm_num) horder
  have hQa := eq_zero_of_one_le_analyticOrderAt hQ hpos
  rw [analyticOrderAt_htPassportGauge_sub_one hQ hQa hc]
  exact horder

theorem injective_htPassportGauge {Q : ℂ → ℂ}
    (hQ : AnalyticOnNhd ℂ Q Set.univ) (hQHT : Hypertranscendental Q) :
    Function.Injective (fun c : ℝ => htPassportGauge Q c) := by
  intro c d hcd
  by_contra hne
  have hsub : c - d ≠ 0 := sub_ne_zero.mpr hne
  have hsubC : ((c - d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsub
  have hHT : Hypertranscendental
      (fun z => Complex.exp (((c - d : ℝ) : ℂ) * Q z)) :=
    (hypertranscendental_cexp_const_mul_iff hQ hsubC).2 hQHT
  apply hHT
  have hone : (fun z => Complex.exp (((c - d : ℝ) : ℂ) * Q z)) =
      (fun _ : ℂ => (1 : ℂ)) := by
    funext z
    have hz := congrFun hcd z
    change Complex.exp ((c : ℂ) * Q z) = Complex.exp ((d : ℂ) * Q z) at hz
    rw [show ((c - d : ℝ) : ℂ) * Q z =
      (c : ℂ) * Q z - (d : ℂ) * Q z by push_cast; ring,
      Complex.exp_sub, hz, div_self (Complex.exp_ne_zero _)]
  rw [hone]
  exact differentiallyAlgebraic_const 1

/-- Complete continuum family of positive Schwarz-real HT gauges carrying one passport. -/
structure DeBrangesHTGaugeSaturationData (S : Set ℂ) (m : S → ℕ) where
  exponent : ℂ → ℂ
  exponent_analytic : AnalyticOnNhd ℂ exponent Set.univ
  exponent_schwarzReal : SchwarzRealGauge exponent
  exponent_hypertranscendental : Hypertranscendental exponent
  exponent_nontrivial : ∃ z, exponent z ≠ 0
  exponent_passport : ∀ a : S, (m a + 1 : ℕ∞) ≤ analyticOrderAt exponent a
  gauge_injective : Function.Injective (fun c : ℝ => htPassportGauge exponent c)
  gauge_analytic : ∀ c : ℝ, AnalyticOnNhd ℂ (htPassportGauge exponent c) Set.univ
  gauge_schwarzReal : ∀ c : ℝ, SchwarzRealGauge (htPassportGauge exponent c)
  gauge_zeroFree : ∀ c : ℝ, ZeroFreeGauge (htPassportGauge exponent c)
  gauge_positive_real : ∀ c x : ℝ,
    (htPassportGauge exponent c (x : ℂ)).im = 0 ∧
      0 < (htPassportGauge exponent c (x : ℂ)).re
  gauge_hypertranscendental : ∀ {c : ℝ}, c ≠ 0 →
    Hypertranscendental (htPassportGauge exponent c)
  gauge_passport : ∀ {c : ℝ}, c ≠ 0 → ∀ a : S,
    (m a + 1 : ℕ∞) ≤
      analyticOrderAt (fun z => htPassportGauge exponent c z - 1) a

/-- Continuum HT saturation with arbitrary closed discrete conjugation-stable Hermite passport. -/
theorem exists_deBrangesHTGaugeSaturationData
    {S : Set ℂ} (hSd : IsDiscrete S) (hSc : IsClosed S)
    (hSconj : ∀ z, z ∈ S → star z ∈ S) (m : S → ℕ)
    (_hmconj : ∀ a : S, m ⟨star (a : ℂ), hSconj a a.2⟩ = m a) :
    Nonempty (DeBrangesHTGaugeSaturationData S m) := by
  obtain ⟨Q, hQ, hQsym, hQHT, hQne, hQorder⟩ :=
    exists_symmetric_hypertranscendental_passport_exponent hSd hSc m
  refine ⟨{
    exponent := Q
    exponent_analytic := hQ
    exponent_schwarzReal := hQsym
    exponent_hypertranscendental := hQHT
    exponent_nontrivial := hQne
    exponent_passport := hQorder
    gauge_injective := injective_htPassportGauge hQ hQHT
    gauge_analytic := analyticOnNhd_htPassportGauge hQ
    gauge_schwarzReal := schwarzReal_htPassportGauge hQsym
    gauge_zeroFree := zeroFree_htPassportGauge Q
    gauge_positive_real := htPassportGauge_positive_real hQsym
    gauge_hypertranscendental := hypertranscendental_htPassportGauge hQ hQHT
    gauge_passport := fun hc a =>
      htPassportGauge_preserves_order hQ (hQorder a) hc
  }⟩

/-- Structure-function representative obtained from one saturated gauge. -/
def deBrangesGaugeRepresentative {S : Set ℂ} {m : S → ℕ}
    (D : DeBrangesHTGaugeSaturationData S m) (E : ℂ → ℂ) (c : ℝ) (z : ℂ) : ℂ :=
  htPassportGauge D.exponent c z * E z

theorem exists_ne_zero_of_suzukiHermiteBiehler {E : ℂ → ℂ}
    (hE : SuzukiHermiteBiehler E) : ∃ z, E z ≠ 0 := by
  refine ⟨Complex.I, ?_⟩
  intro hzero
  have hlt := hE Complex.I (by simp)
  rw [hzero, norm_zero] at hlt
  exact (not_lt_of_ge (norm_nonneg _)) hlt

theorem analyticOnNhd_deBrangesGaugeRepresentative
    {S : Set ℂ} {m : S → ℕ} (D : DeBrangesHTGaugeSaturationData S m)
    {E : ℂ → ℂ} (hE : AnalyticOnNhd ℂ E Set.univ) (c : ℝ) :
    AnalyticOnNhd ℂ (deBrangesGaugeRepresentative D E c) Set.univ :=
  (D.gauge_analytic c).mul hE

theorem suzukiHermiteBiehler_deBrangesGaugeRepresentative_iff
    {S : Set ℂ} {m : S → ℕ} (D : DeBrangesHTGaugeSaturationData S m)
    (E : ℂ → ℂ) (c : ℝ) :
    SuzukiHermiteBiehler (deBrangesGaugeRepresentative D E c) ↔
      SuzukiHermiteBiehler E :=
  suzukiHermiteBiehler_mul_iff (D.gauge_schwarzReal c) (D.gauge_zeroFree c)

theorem deBrangesGaugeRepresentative_innerQuotient
    {S : Set ℂ} {m : S → ℕ} (D : DeBrangesHTGaugeSaturationData S m)
    (E : ℂ → ℂ) (c : ℝ) (z : ℂ) :
    suzukiEntireSharp (deBrangesGaugeRepresentative D E c) z /
        deBrangesGaugeRepresentative D E c z =
      suzukiEntireSharp E z / E z :=
  deBrangesInnerQuotient_mul_of_schwarzReal
    (D.gauge_schwarzReal c) (D.gauge_zeroFree c) z

theorem deBrangesGaugeRepresentative_canonicalSpectrum
    {S : Set ℂ} {m : S → ℕ} (D : DeBrangesHTGaugeSaturationData S m)
    (E : ℂ → ℂ) (c α : ℝ) (z : ℂ) :
    deBrangesCanonicalPencil (deBrangesGaugeRepresentative D E c) α z = 0 ↔
      deBrangesCanonicalPencil E α z = 0 :=
  deBrangesCanonicalPencil_mul_eq_zero_iff
    (D.gauge_schwarzReal c) (D.gauge_zeroFree c) α z

theorem analyticOnNhd_deBrangesCanonicalPencil {E : ℂ → ℂ}
    (hE : AnalyticOnNhd ℂ E Set.univ) (α : ℝ) :
    AnalyticOnNhd ℂ (deBrangesCanonicalPencil E α) Set.univ := by
  have hEs := analyticOnNhd_suzukiEntireSharp hE
  intro z _
  unfold deBrangesCanonicalPencil deBrangesRealPart deBrangesImaginaryPart
  have hA : AnalyticAt ℂ
      (fun w => (E w + suzukiEntireSharp E w) / 2) z :=
    ((hE z (Set.mem_univ z)).add (hEs z (Set.mem_univ z))).div_const
  have hB : AnalyticAt ℂ
      (fun w => (suzukiEntireSharp E w - E w) / (2 * Complex.I)) z :=
    ((hEs z (Set.mem_univ z)).sub (hE z (Set.mem_univ z))).div_const
  exact (analyticAt_const.mul hA).sub (analyticAt_const.mul hB)

/-- Canonical spectra retain analytic multiplicity, not merely their zero sets. -/
theorem deBrangesGaugeRepresentative_canonicalSpectrum_multiplicity
    {S : Set ℂ} {m : S → ℕ} (D : DeBrangesHTGaugeSaturationData S m)
    {E : ℂ → ℂ} (hE : AnalyticOnNhd ℂ E Set.univ)
    (c α : ℝ) (z : ℂ) :
    analyticOrderAt (deBrangesCanonicalPencil
        (deBrangesGaugeRepresentative D E c) α) z =
      analyticOrderAt (deBrangesCanonicalPencil E α) z := by
  have hfactor : deBrangesCanonicalPencil
      (deBrangesGaugeRepresentative D E c) α =
        htPassportGauge D.exponent c * deBrangesCanonicalPencil E α := by
    funext w
    exact deBrangesCanonicalPencil_mul_of_schwarzReal
      (D.gauge_schwarzReal c) α w
  rw [hfactor, analyticOrderAt_mul
    ((D.gauge_analytic c) z (Set.mem_univ z))
    ((analyticOnNhd_deBrangesCanonicalPencil hE α) z (Set.mem_univ z)),
    ((D.gauge_analytic c) z (Set.mem_univ z)).analyticOrderAt_eq_zero.mpr
      (D.gauge_zeroFree c z), zero_add]

theorem deBrangesGaugeRepresentative_kernel
    {S : Set ℂ} {m : S → ℕ} (D : DeBrangesHTGaugeSaturationData S m)
    (E : ℂ → ℂ) (c : ℝ) (z w : ℂ) :
    deBrangesKernel (deBrangesGaugeRepresentative D E c) z w =
      htPassportGauge D.exponent c z *
        star (htPassportGauge D.exponent c w) * deBrangesKernel E z w :=
  deBrangesKernel_mul_of_schwarzReal (D.gauge_schwarzReal c) z w

/-- At most one representative in a fixed exact gauge class is differentially algebraic. -/
theorem differentiallyAlgebraic_deBrangesGaugeRepresentative_unique
    {S : Set ℂ} {m : S → ℕ} (D : DeBrangesHTGaugeSaturationData S m)
    {E : ℂ → ℂ} (hEan : AnalyticOnNhd ℂ E Set.univ)
    (hEHB : SuzukiHermiteBiehler E) {c d : ℝ}
    (hc : DifferentiallyAlgebraic (deBrangesGaugeRepresentative D E c))
    (hd : DifferentiallyAlgebraic (deBrangesGaugeRepresentative D E d)) : c = d := by
  have hc' : DifferentiallyAlgebraic
      (entireExponentialPencil E D.exponent (c : ℂ)) := by
    have heq : entireExponentialPencil E D.exponent (c : ℂ) =
        deBrangesGaugeRepresentative D E c := by
      funext z
      simp [deBrangesGaugeRepresentative, entireExponentialPencil, htPassportGauge, mul_comm]
    rw [heq]
    exact hc
  have hd' : DifferentiallyAlgebraic
      (entireExponentialPencil E D.exponent (d : ℂ)) := by
    have heq : entireExponentialPencil E D.exponent (d : ℂ) =
        deBrangesGaugeRepresentative D E d := by
      funext z
      simp [deBrangesGaugeRepresentative, entireExponentialPencil, htPassportGauge, mul_comm]
    rw [heq]
    exact hd
  have heq : (c : ℂ) = (d : ℂ) :=
    differentiallyAlgebraic_entireExponentialPencil_unique
      hEan D.exponent_analytic (exists_ne_zero_of_suzukiHermiteBiehler hEHB)
        D.exponent_hypertranscendental hc' hd'
  exact_mod_cast heq

/-- If the base representative is DA, every nonzero saturated representative is HT. -/
theorem hypertranscendental_deBrangesGaugeRepresentative_of_base_DA
    {S : Set ℂ} {m : S → ℕ} (D : DeBrangesHTGaugeSaturationData S m)
    {E : ℂ → ℂ} (hEan : AnalyticOnNhd ℂ E Set.univ)
    (hEHB : SuzukiHermiteBiehler E) (hEDA : DifferentiallyAlgebraic E)
    {c : ℝ} (hc : c ≠ 0) :
    Hypertranscendental (deBrangesGaugeRepresentative D E c) := by
  intro hcDA
  have hzeroDA : DifferentiallyAlgebraic (deBrangesGaugeRepresentative D E 0) := by
    have heq : deBrangesGaugeRepresentative D E 0 = E := by
      funext z
      simp [deBrangesGaugeRepresentative, htPassportGauge]
    rw [heq]
    exact hEDA
  exact hc (differentiallyAlgebraic_deBrangesGaugeRepresentative_unique
    D hEan hEHB hcDA hzeroDA)

theorem deBrangesGaugeRepresentative_passport
    {S : Set ℂ} {m : S → ℕ} (D : DeBrangesHTGaugeSaturationData S m)
    {E : ℂ → ℂ} (hE : AnalyticOnNhd ℂ E Set.univ)
    {c : ℝ} (hc : c ≠ 0) (a : S) :
    (m a + 1 : ℕ∞) ≤ analyticOrderAt
      (fun z => deBrangesGaugeRepresentative D E c z - E z) a := by
  have hH := D.gauge_passport hc a
  have hdiff : (fun z => deBrangesGaugeRepresentative D E c z - E z) =
      (fun z => htPassportGauge D.exponent c z - 1) * E := by
    funext z
    dsimp [deBrangesGaugeRepresentative]
    ring
  rw [hdiff, analyticOrderAt_mul
    (f := fun z => htPassportGauge D.exponent c z - 1) (g := E)
    (((D.gauge_analytic c).sub analyticOnNhd_const) a (Set.mem_univ a))
    (hE a (Set.mem_univ a))]
  exact hH.trans (le_add_right le_rfl)

end

end GaloisForLFunctions.RHTower
