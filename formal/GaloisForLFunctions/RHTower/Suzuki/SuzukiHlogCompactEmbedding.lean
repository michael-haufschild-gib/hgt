/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael
-/
import GaloisForLFunctions.RHTower.GaussianEvenCarrier
import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Basic

/-!
# Suzuki's logarithmic Fourier-space compact embedding

This file formalizes the compact embedding used in Suzuki (2026), Proposition 4.1, and proved in
Connes--Consani--Moscovici (2025), Theorem 3.6.  On a bounded interval, the unit ball for the
literal source weight

`1 + log⁺ |ξ|`

is precompact in `L²`.  Functions on `(-a,a)` are represented by their extension by zero to
`ℝ`; changing open to closed endpoints does not change the `L²` class.

The proof is the published one: a logarithmic moment gives a uniform high-frequency tail, while
time localization followed by frequency truncation is compact.  No spectral, zero-location, or
Riemann-hypothesis assumption is used.
-/

noncomputable section

open MeasureTheory Set Metric
open scoped ENNReal InnerProduct


namespace RHTower

/-- A positive interval half-width, bundling the source condition `a > 0`. -/
abbrev SuzukiPositiveAperture := {a : ℝ // 0 < a}

/-- A nonempty bounded real interval, with legality bundled into the source object. -/
structure SuzukiBoundedInterval where
  lower : ℝ
  upper : ℝ
  lower_le_upper : lower ≤ upper

/-- Closed representative of a bounded interval.  Endpoints are null for Lebesgue `L²`. -/
def SuzukiBoundedInterval.carrier (I : SuzukiBoundedInterval) : Set ℝ :=
  Set.Icc I.lower I.upper

/-- A strictly positive central radius containing a bounded interval. -/
def SuzukiBoundedInterval.centralRadius (I : SuzukiBoundedInterval) : ℝ :=
  max |I.lower| |I.upper| + 1

theorem SuzukiBoundedInterval.centralRadius_pos (I : SuzukiBoundedInterval) :
    0 < I.centralRadius := by
  unfold centralRadius
  nlinarith [abs_nonneg I.lower, le_max_left |I.lower| |I.upper|]

theorem SuzukiBoundedInterval.carrier_subset_central (I : SuzukiBoundedInterval) :
    I.carrier ⊆ centralInterval I.centralRadius := by
  intro x hx
  rw [carrier, Set.mem_Icc] at hx
  rw [centralInterval, Set.mem_Icc]
  constructor
  · have hl : |I.lower| ≤ max |I.lower| |I.upper| := le_max_left _ _
    change -(max |I.lower| |I.upper| + 1) ≤ x
    nlinarith [neg_abs_le I.lower]
  · have hu : |I.upper| ≤ max |I.lower| |I.upper| := le_max_right _ _
    change x ≤ max |I.lower| |I.upper| + 1
    nlinarith [le_abs_self I.upper]

/-- The source weight `1 + log⁺ |ξ|`. -/
def suzukiLogWeight (ξ : ℝ) : ℝ := 1 + max (Real.log |ξ|) 0

/-- The weighted Fourier density defining Suzuki's `H^log` space. -/
def suzukiHlogDensity (f : SoninL2) (ξ : ℝ) : ℝ :=
  suzukiLogWeight ξ * ‖(fourierUnitary f : ℝ → ℂ) ξ‖ ^ 2

/-- The `H^log` moment in Suzuki's normalization-free unitary Fourier realization. -/
def suzukiHlogMoment (f : SoninL2) : ℝ :=
  ∫ ξ : ℝ, suzukiHlogDensity f ξ

/-- Unit ball of `H^log(-a,a)`, realized inside `L²(ℝ)` by zero extension. -/
def suzukiHlogCentralUnitBall (a : SuzukiPositiveAperture) : Set SoninL2 :=
  {f | indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1) f = f ∧
    Integrable (suzukiHlogDensity f) ∧ suzukiHlogMoment f ≤ 1}

/-- Literal `H^log(I)` unit ball for an arbitrary bounded interval `I`. -/
def suzukiHlogUnitBall (I : SuzukiBoundedInterval) : Set SoninL2 :=
  {f | indicatorCutoff I.carrier measurableSet_Icc f = f ∧
    Integrable (suzukiHlogDensity f) ∧ suzukiHlogMoment f ≤ 1}

theorem one_le_suzukiLogWeight (ξ : ℝ) : 1 ≤ suzukiLogWeight ξ := by
  unfold suzukiLogWeight
  exact le_add_of_nonneg_right (le_max_right _ _)

theorem suzukiLogWeight_nonneg (ξ : ℝ) : 0 ≤ suzukiLogWeight ξ :=
  zero_le_one.trans (one_le_suzukiLogWeight ξ)

theorem suzukiHlogDensity_nonneg (f : SoninL2) (ξ : ℝ) :
    0 ≤ suzukiHlogDensity f ξ := by
  exact mul_nonneg (suzukiLogWeight_nonneg ξ) (sq_nonneg _)

/-- The literal weighted unit ball is contained in the ordinary `L²` unit ball. -/
theorem norm_le_one_of_mem_suzukiHlogCentralUnitBall
    (a : SuzukiPositiveAperture) {f : SoninL2}
    (hf : f ∈ suzukiHlogCentralUnitBall a) : ‖f‖ ≤ 1 := by
  have hplain : Integrable
      (fun ξ : ℝ => ‖(fourierUnitary f : ℝ → ℂ) ξ‖ ^ 2) :=
    (Lp.memLp (fourierUnitary f)).integrable_norm_pow (by norm_num)
  have hweighted : Integrable (suzukiHlogDensity f) := hf.2.1
  have hpoint : ∀ ξ : ℝ,
      ‖(fourierUnitary f : ℝ → ℂ) ξ‖ ^ 2 ≤ suzukiHlogDensity f ξ := by
    intro ξ
    unfold suzukiHlogDensity
    nlinarith [one_le_suzukiLogWeight ξ,
      sq_nonneg ‖(fourierUnitary f : ℝ → ℂ) ξ‖]
  have hintegral :
      (∫ ξ : ℝ, ‖(fourierUnitary f : ℝ → ℂ) ξ‖ ^ 2) ≤ suzukiHlogMoment f := by
    exact integral_mono hplain hweighted hpoint
  have hnormsq : ‖f‖ ^ 2 ≤ 1 := by
    calc
      ‖f‖ ^ 2 = ‖fourierUnitary f‖ ^ 2 := by rw [fourierUnitary.norm_map]
      _ = ∫ ξ : ℝ, ‖(fourierUnitary f : ℝ → ℂ) ξ‖ ^ 2 :=
        norm_sq_eq_integral (fourierUnitary f)
      _ ≤ suzukiHlogMoment f := hintegral
      _ ≤ 1 := hf.2.2
  nlinarith [norm_nonneg f]

/-- Exact Plancherel identity for the high-frequency truncation error. -/
theorem norm_sq_sub_fourierCutoff_central_eq_tailIntegral
    (t : ℝ) (f : SoninL2) :
    ‖f - fourierCutoff (centralInterval t) (measurableSet_centralInterval t) f‖ ^ 2 =
      ∫ ξ : ℝ, (centralInterval t)ᶜ.indicator
        (fun η : ℝ => ‖(fourierUnitary f : ℝ → ℂ) η‖ ^ 2) ξ := by
  set g : SoninL2 := fourierUnitary f with hg
  have hcoe : f - fourierCutoff (centralInterval t)
        (measurableSet_centralInterval t) f =
      fourierUnitary.symm
        (g - indicatorCutoff (centralInterval t)
          (measurableSet_centralInterval t) g) := by
    have h₁ : fourierCutoff (centralInterval t)
        (measurableSet_centralInterval t) f =
      fourierUnitary.symm
        (indicatorCutoff (centralInterval t) (measurableSet_centralInterval t) g) := by
      rw [fourierCutoff_apply, hg]
    have h₂ : f = fourierUnitary.symm g := by
      rw [hg, LinearIsometryEquiv.symm_apply_apply]
    rw [h₁, h₂, ← map_sub]
  have hnorm :
      ‖f - fourierCutoff (centralInterval t) (measurableSet_centralInterval t) f‖ =
        ‖g - indicatorCutoff (centralInterval t)
          (measurableSet_centralInterval t) g‖ := by
    rw [hcoe]
    exact fourierUnitary.symm.norm_map _
  rw [hnorm, norm_sq_eq_integral]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub g
      (indicatorCutoff (centralInterval t) (measurableSet_centralInterval t) g),
    indicatorCutoff_ae (centralInterval t) (measurableSet_centralInterval t) g]
      with ξ hsub hcut
  rw [hsub, Pi.sub_apply, hcut]
  by_cases hξ : ξ ∈ centralInterval t
  · rw [Set.indicator_of_mem hξ, Set.indicator_of_notMem (by simpa using hξ),
      sub_self, norm_zero]
    norm_num
  · rw [Set.indicator_of_notMem hξ, Set.indicator_of_mem (by simpa using hξ), sub_zero]

/-- Outside radius `exp A`, Suzuki's logarithmic weight is at least `A`. -/
theorem le_suzukiLogWeight_of_mem_exp_tail (A ξ : ℝ)
    (hξ : ξ ∈ (centralInterval (Real.exp A))ᶜ) : A ≤ suzukiLogWeight ξ := by
  have habs : Real.exp A < |ξ| := by
    have hnot : ¬|ξ| ≤ Real.exp A := by
      intro habs
      exact hξ (by
        rw [centralInterval, Set.mem_Icc]
        exact (abs_le.mp habs))
    exact lt_of_not_ge hnot
  have hlog : A < Real.log |ξ| := by
    rw [← Real.log_exp A]
    exact Real.log_lt_log (Real.exp_pos A) habs
  unfold suzukiLogWeight
  calc
    A ≤ Real.log |ξ| := hlog.le
    _ ≤ max (Real.log |ξ|) 0 := le_max_left _ _
    _ ≤ 1 + max (Real.log |ξ|) 0 := by linarith

/-- The weighted moment bounds the exact `L²` high-frequency error. -/
theorem mul_norm_sq_sub_fourierCutoff_exp_le_suzukiHlogMoment
    (a : SuzukiPositiveAperture) {f : SoninL2}
    (hf : f ∈ suzukiHlogCentralUnitBall a) (A : ℝ) :
    A * ‖f - fourierCutoff (centralInterval (Real.exp A))
      (measurableSet_centralInterval (Real.exp A)) f‖ ^ 2 ≤ suzukiHlogMoment f := by
  rw [norm_sq_sub_fourierCutoff_central_eq_tailIntegral, ← integral_const_mul]
  have hplain : Integrable
      (fun ξ : ℝ => ‖(fourierUnitary f : ℝ → ℂ) ξ‖ ^ 2) :=
    (Lp.memLp (fourierUnitary f)).integrable_norm_pow (by norm_num)
  have hleft : Integrable (fun ξ : ℝ =>
      A * (centralInterval (Real.exp A))ᶜ.indicator
        (fun η : ℝ => ‖(fourierUnitary f : ℝ → ℂ) η‖ ^ 2) ξ) :=
    (hplain.indicator (measurableSet_centralInterval (Real.exp A)).compl).const_mul A
  refine integral_mono hleft hf.2.1 ?_
  intro ξ
  by_cases hξ : ξ ∈ (centralInterval (Real.exp A))ᶜ
  · change A * (centralInterval (Real.exp A))ᶜ.indicator
        (fun η : ℝ => ‖(fourierUnitary f : ℝ → ℂ) η‖ ^ 2) ξ ≤
      suzukiHlogDensity f ξ
    rw [Set.indicator_of_mem hξ]
    unfold suzukiHlogDensity
    exact mul_le_mul_of_nonneg_right (le_suzukiLogWeight_of_mem_exp_tail A ξ hξ)
      (sq_nonneg _)
  · change A * (centralInterval (Real.exp A))ᶜ.indicator
        (fun η : ℝ => ‖(fourierUnitary f : ℝ → ℂ) η‖ ^ 2) ξ ≤
      suzukiHlogDensity f ξ
    rw [Set.indicator_of_notMem hξ]
    simpa using suzukiHlogDensity_nonneg f ξ

/-- Uniform high-frequency control on the literal `H^log` unit ball. -/
theorem norm_sub_fourierCutoff_exp_lt
    (a : SuzukiPositiveAperture) {f : SoninL2}
    (hf : f ∈ suzukiHlogCentralUnitBall a) {ε : ℝ} (hε : 0 < ε) :
    ‖f - fourierCutoff (centralInterval (Real.exp ((4 / ε) ^ 2)))
      (measurableSet_centralInterval (Real.exp ((4 / ε) ^ 2))) f‖ < ε / 2 := by
  let A : ℝ := (4 / ε) ^ 2
  let n : ℝ := ‖f - fourierCutoff (centralInterval (Real.exp A))
    (measurableSet_centralInterval (Real.exp A)) f‖
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hmul : A * n ^ 2 ≤ 1 := by
    calc
      A * n ^ 2 ≤ suzukiHlogMoment f :=
        mul_norm_sq_sub_fourierCutoff_exp_le_suzukiHlogMoment a hf A
      _ ≤ 1 := hf.2.2
  have hscale : A * (ε / 4) ^ 2 = 1 := by
    dsimp [A]
    field_simp [ne_of_gt hε]
  have hn_sq : n ^ 2 ≤ (ε / 4) ^ 2 := by
    have hn_sq' : n ^ 2 ≤ 1 / A := by
      rw [le_div_iff₀ hA]
      simpa [mul_comm] using hmul
    have hrecip : 1 / A = (ε / 4) ^ 2 := by
      dsimp [A]
      field_simp [ne_of_gt hε]
    exact hn_sq'.trans_eq hrecip
  have hn : n ≤ ε / 4 := by
    nlinarith [norm_nonneg (f - fourierCutoff (centralInterval (Real.exp A))
      (measurableSet_centralInterval (Real.exp A)) f)]
  change n < ε / 2
  nlinarith

/--
Published compact-approximation mechanism: a uniformly Fourier-tight, time-supported bounded set
is totally bounded in `L²`.
-/
theorem totallyBounded_of_centralSupport_of_uniformFourierTail
    (a : SuzukiPositiveAperture) (S : Set SoninL2)
    (hunit : ∀ f ∈ S, ‖f‖ ≤ 1)
    (hsupport : ∀ f ∈ S,
      indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1) f = f)
    (htail : ∀ ε > 0, ∃ t : ℝ, 0 < t ∧ ∀ f ∈ S,
      ‖f - fourierCutoff (centralInterval t) (measurableSet_centralInterval t) f‖ < ε) :
    TotallyBounded S := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨t, ht, htight⟩ := htail (ε / 2) (by positivity)
  let K : SoninL2 →L[ℂ] SoninL2 :=
    indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1) *
      fourierCutoff (centralInterval t) (measurableSet_centralInterval t)
  have hKcompact : IsCompactOperator K := by
    simpa [K] using isCompactOperator_indicatorCutoff_fourierCutoff_central a.1 t a.2
  have hcompact : IsCompact (closure (K '' Metric.closedBall 0 1)) :=
    hKcompact.isCompact_closure_image_closedBall 1
  obtain ⟨centers, hcentersFinite, hcover⟩ :=
    Metric.totallyBounded_iff.mp hcompact.totallyBounded (ε / 2) (by positivity)
  refine ⟨centers, hcentersFinite, ?_⟩
  intro f hf
  have hfball : f ∈ Metric.closedBall (0 : SoninL2) 1 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hunit f hf
  have hKmem : K f ∈ closure (K '' Metric.closedBall 0 1) :=
    subset_closure ⟨f, hfball, rfl⟩
  have hKcovered := hcover hKmem
  rcases Set.mem_iUnion.mp hKcovered with ⟨c, hKcovered⟩
  rcases Set.mem_iUnion.mp hKcovered with ⟨hc, hKball⟩
  refine Set.mem_iUnion.mpr ⟨c, Set.mem_iUnion.mpr ⟨hc, ?_⟩⟩
  rw [Metric.mem_ball] at hKball ⊢
  have happrox : dist f (K f) < ε / 2 := by
    rw [dist_eq_norm]
    have heq : f - K f =
        indicatorCutoff (centralInterval a.1) (measurableSet_centralInterval a.1)
          (f - fourierCutoff (centralInterval t) (measurableSet_centralInterval t) f) := by
      change f - indicatorCutoff (centralInterval a.1)
          (measurableSet_centralInterval a.1)
          (fourierCutoff (centralInterval t) (measurableSet_centralInterval t) f) = _
      rw [map_sub, hsupport f hf]
    rw [heq, indicatorCutoff_eq_physicalForbidden_starProjection]
    exact lt_of_le_of_lt
      ((physicalForbidden (centralInterval a.1)
        (measurableSet_centralInterval a.1)).norm_starProjection_apply_le _)
      (htight f hf)
  exact (dist_triangle f (K f) c).trans_lt (by linarith)

/-- Suzuki (2026), compact embedding proposition: the literal `H^log(-a,a)` unit ball is
precompact in `L²(-a,a)`. -/
theorem totallyBounded_suzukiHlogCentralUnitBall (a : SuzukiPositiveAperture) :
    TotallyBounded (suzukiHlogCentralUnitBall a) := by
  apply totallyBounded_of_centralSupport_of_uniformFourierTail a
  · intro f hf
    exact norm_le_one_of_mem_suzukiHlogCentralUnitBall a hf
  · intro f hf
    exact hf.1
  · intro ε hε
    refine ⟨Real.exp ((4 / ε) ^ 2), Real.exp_pos _, ?_⟩
    intro f hf
    exact (norm_sub_fourierCutoff_exp_lt a hf hε).trans (by linarith)

/-- Closed compact form of Suzuki's compact embedding theorem. -/
theorem isCompact_closure_suzukiHlogCentralUnitBall (a : SuzukiPositiveAperture) :
    IsCompact (closure (suzukiHlogCentralUnitBall a)) :=
  (totallyBounded_suzukiHlogCentralUnitBall a).closure.isCompact_of_isClosed isClosed_closure

/-- Support in a bounded interval implies support in its canonical containing central interval. -/
theorem indicatorCutoff_centralRadius_eq_self_of_interval_eq_self
    (I : SuzukiBoundedInterval) {f : SoninL2}
    (hf : indicatorCutoff I.carrier measurableSet_Icc f = f) :
    indicatorCutoff (centralInterval I.centralRadius)
      (measurableSet_centralInterval I.centralRadius) f = f := by
  apply Lp.ext
  have hinterval : (f : ℝ → ℂ) =ᵐ[volume] I.carrier.indicator fun x => f x := by
    have hcut := indicatorCutoff_ae I.carrier measurableSet_Icc f
    rw [hf] at hcut
    exact hcut
  filter_upwards [indicatorCutoff_ae (centralInterval I.centralRadius)
      (measurableSet_centralInterval I.centralRadius) f, hinterval] with x hcentral hI
  rw [hcentral]
  by_cases hx : x ∈ I.carrier
  · have hxc : x ∈ centralInterval I.centralRadius :=
      I.carrier_subset_central hx
    rw [Set.indicator_of_mem hxc]
  · have hfx : (f : ℝ → ℂ) x = 0 := by
      simpa [hx] using hI
    by_cases hxc : x ∈ centralInterval I.centralRadius
    · rw [Set.indicator_of_mem hxc, hfx]
    · rw [Set.indicator_of_notMem hxc, hfx]

/-- Every bounded-interval unit ball lies in a literal central-interval unit ball. -/
theorem suzukiHlogUnitBall_subset_central (I : SuzukiBoundedInterval) :
    suzukiHlogUnitBall I ⊆
      suzukiHlogCentralUnitBall
        ⟨I.centralRadius, I.centralRadius_pos⟩ := by
  intro f hf
  exact ⟨indicatorCutoff_centralRadius_eq_self_of_interval_eq_self I hf.1, hf.2⟩

/-- Suzuki (2026), Proposition 4.1 in its stated generality: for every bounded interval `I`,
the unit ball of `H^log(I)` is precompact in `L²(I)`. -/
theorem totallyBounded_suzukiHlogUnitBall (I : SuzukiBoundedInterval) :
    TotallyBounded (suzukiHlogUnitBall I) :=
  (totallyBounded_suzukiHlogCentralUnitBall
    ⟨I.centralRadius, I.centralRadius_pos⟩).subset
      (suzukiHlogUnitBall_subset_central I)

/-- Closed compact form of Suzuki's bounded-interval compact embedding theorem. -/
theorem isCompact_closure_suzukiHlogUnitBall (I : SuzukiBoundedInterval) :
    IsCompact (closure (suzukiHlogUnitBall I)) :=
  (totallyBounded_suzukiHlogUnitBall I).closure.isCompact_of_isClosed isClosed_closure

end RHTower
