import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerLogSchwartzLanding
import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerPaugamJDescent

/-!
# Meyer's all-weight logarithmic target

The ordinary Schwartz space in logarithmic radius is only a necessary shadow
of Meyer's multiplicative Bruhat--Schwartz target.  The correct radial
underlying space requires every derivative to decay against every
multiplicative power, equivalently against every exponential weight at both
logarithmic ends.

This file packages that all-weight condition as a complex submodule, constructs
the actual Poisson boundary map into it, and prepares the exact target on which
Paugam's weighted inversion acts.

No Riemann-hypothesis premise, positivity assumption, spectral realization,
numerical computation, or source-provenance hypothesis occurs.
-/

open Asymptotics Complex Filter Function Set Topology
open scoped ContDiff FourierTransform SchwartzMap
open GaloisForLFunctions.RHTower

namespace RHTower

noncomputable section

/-! ## Linear closure of the all-weight condition -/

theorem deningerMeyerStrongLogDecay_zero :
    DeningerMeyerStrongLogDecay (0 : ℝ → ℂ) where
  smooth := contDiff_const
  decayTop := by
    intro n a
    have hz :
        iteratedDeriv n (0 : ℝ → ℂ) =
          (0 : ℝ → ℂ) := by
      funext t
      exact iteratedDeriv_const_zero
    rw [hz]
    exact Asymptotics.isBigO_zero
      (fun t : ℝ => Real.exp t ^ (-a)) atTop
  decayBot := by
    intro n b
    have hz :
        iteratedDeriv n (0 : ℝ → ℂ) =
          (0 : ℝ → ℂ) := by
      funext t
      exact iteratedDeriv_const_zero
    rw [hz]
    exact Asymptotics.isBigO_zero
      (fun t : ℝ => Real.exp t ^ b) atBot

theorem DeningerMeyerStrongLogDecay.add
    {g h : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g)
    (hh : DeningerMeyerStrongLogDecay h) :
    DeningerMeyerStrongLogDecay (g + h) where
  smooth := hg.smooth.add hh.smooth
  decayTop := by
    intro n a
    have hsum :=
      (hg.decayTop n a).add (hh.decayTop n a)
    apply hsum.congr'
    · exact Filter.Eventually.of_forall fun t => by
        exact (
          iteratedDeriv_add
            (hg.smooth.contDiffAt.of_le
              (mod_cast le_top))
            (hh.smooth.contDiffAt.of_le
              (mod_cast le_top))).symm
    · rfl
  decayBot := by
    intro n b
    have hsum :=
      (hg.decayBot n b).add (hh.decayBot n b)
    apply hsum.congr'
    · exact Filter.Eventually.of_forall fun t => by
        exact (
          iteratedDeriv_add
            (hg.smooth.contDiffAt.of_le
              (mod_cast le_top))
            (hh.smooth.contDiffAt.of_le
              (mod_cast le_top))).symm
    · rfl

theorem DeningerMeyerStrongLogDecay.smul
    (c : ℂ) {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) :
    DeningerMeyerStrongLogDecay (c • g) where
  smooth := hg.smooth.const_smul c
  decayTop := by
    intro n a
    have hscaled :=
      (hg.decayTop n a).const_smul_left c
    apply hscaled.congr'
    · exact Filter.Eventually.of_forall fun t => by
        simp only [Pi.smul_apply,
          iteratedDeriv_const_smul_field]
    · rfl
  decayBot := by
    intro n b
    have hscaled :=
      (hg.decayBot n b).const_smul_left c
    apply hscaled.congr'
    · exact Filter.Eventually.of_forall fun t => by
        simp only [Pi.smul_apply,
          iteratedDeriv_const_smul_field]
    · rfl

/-- The two asymptotic halves of the strong logarithmic condition glue to one global
exponential-weight bound.  This is the literal bounded-range form of the seminorms used in the
paper: every iterated derivative remains bounded after multiplication by any real exponential
weight. -/
theorem DeningerMeyerStrongLogDecay.weighted_iteratedDeriv_isBounded
    {h : ℝ → ℂ} (hh : DeningerMeyerStrongLogDecay h)
    (n : ℕ) (a : ℝ) :
    Bornology.IsBounded (Set.range (fun t : ℝ =>
      ((Real.exp t ^ a : ℝ) : ℂ) * iteratedDeriv n h t)) := by
  have hweight : Continuous (fun t : ℝ => Real.exp t ^ a) :=
    Real.continuous_exp.rpow_const (fun t => Or.inl (Real.exp_ne_zero t))
  have hderiv : Continuous (iteratedDeriv n h) :=
    hh.smooth.continuous_iteratedDeriv n (by
      show ((n : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr (ENat.coe_lt_top n).le)
  have hcontinuous : Continuous (fun t : ℝ =>
      ((Real.exp t ^ a : ℝ) : ℂ) * iteratedDeriv n h t) :=
    (Complex.continuous_ofReal.comp hweight).mul hderiv
  rw [hcontinuous.isBounded_range_iff_isBigO_atTop_atBot]
  have hweighted (l : Filter ℝ)
      (hdecay : iteratedDeriv n h =O[l]
        fun t : ℝ => Real.exp t ^ (-a)) :
      (fun t : ℝ => ((Real.exp t ^ a : ℝ) : ℂ) *
        iteratedDeriv n h t) =O[l] (1 : ℝ → ℝ) := by
    obtain ⟨C, hC⟩ := hdecay.bound
    apply IsBigO.of_bound C
    filter_upwards [hC] with t ht
    have ht' : ‖iteratedDeriv n h t‖ ≤
        C * Real.exp t ^ (-a) := by
      simpa [Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos (Real.exp_pos t) (-a))] using ht
    rw [Pi.one_apply, norm_one, norm_mul, Complex.norm_real,
      Real.norm_eq_abs,
      abs_of_pos (Real.rpow_pos_of_pos (Real.exp_pos t) a)]
    calc
      Real.exp t ^ a * ‖iteratedDeriv n h t‖ ≤
          Real.exp t ^ a * (C * Real.exp t ^ (-a)) :=
        mul_le_mul_of_nonneg_left ht'
          (Real.rpow_nonneg (Real.exp_pos t).le a)
      _ = C * (Real.exp t ^ a * Real.exp t ^ (-a)) := by ring
      _ = C := by
        rw [← Real.rpow_add (Real.exp_pos t), add_neg_cancel,
          Real.rpow_zero, mul_one]
      _ = C * 1 := by ring
  exact ⟨hweighted atTop (hh.decayTop n a),
    hweighted atBot (hh.decayBot n (-a))⟩

/--
Exact radial all-weight Meyer target in logarithmic radius.

Its topology is not asserted here; this definition records the correct
underlying vector space, unlike the weaker ordinary log-Schwartz corollary.
-/
def DeningerMeyerStrongLogTarget :
    Submodule ℂ (ℝ → ℂ) where
  carrier := {g | DeningerMeyerStrongLogDecay g}
  zero_mem' := deningerMeyerStrongLogDecay_zero
  add_mem' := DeningerMeyerStrongLogDecay.add
  smul_mem' := fun c _ hg =>
    DeningerMeyerStrongLogDecay.smul c hg

theorem mem_deningerMeyerStrongLogTarget_iff
    (g : ℝ → ℂ) :
    g ∈ DeningerMeyerStrongLogTarget ↔
      DeningerMeyerStrongLogDecay g :=
  Iff.rfl

/-! ## Literal Poisson boundary -/

/--
Meyer's Poisson operator into the full all-derivative, all-weight logarithmic
target.
-/
def deningerMeyerStrongLogSumLM :
    DeningerMeyerCap →ₗ[ℂ]
      DeningerMeyerStrongLogTarget where
  toFun f :=
    ⟨deningerMeyerLogSum f,
      deningerMeyerLogSum_strongLogDecay f f.property⟩
  map_add' f g := by
    apply Subtype.ext
    funext t
    change deningerMeyerSum
        (↑(f + g) : SchwartzMap ℝ ℂ)
        (Real.exp t) =
      deningerMeyerSum f (Real.exp t) +
        deningerMeyerSum g (Real.exp t)
    exact
      (deningerMeyerPositiveSumLM
        (Real.exp t) (Real.exp_ne_zero t)).map_add f g
  map_smul' c f := by
    apply Subtype.ext
    funext t
    change deningerMeyerSum
        (↑(c • f) : SchwartzMap ℝ ℂ)
        (Real.exp t) =
      c • deningerMeyerSum f (Real.exp t)
    exact
      (deningerMeyerPositiveSumLM
        (Real.exp t) (Real.exp_ne_zero t)).map_smul c f

@[simp]
theorem deningerMeyerStrongLogSumLM_apply
    (f : DeningerMeyerCap) (t : ℝ) :
    ((deningerMeyerStrongLogSumLM f :
      DeningerMeyerStrongLogTarget) : ℝ → ℂ) t =
      deningerMeyerSum f (Real.exp t) :=
  rfl

/-- Actual algebraic middle quotient of the radial all-weight Meyer target by
the Poisson range. -/
abbrev DeningerMeyerStrongLogCohomology :=
  DeningerMeyerStrongLogTarget ⧸
    LinearMap.range deningerMeyerStrongLogSumLM

/-- Every Poisson boundary has zero class in the actual all-weight quotient. -/
@[simp]
theorem deningerMeyerStrongLog_boundary_class_zero
    (f : DeningerMeyerCap) :
    Submodule.Quotient.mk
        (deningerMeyerStrongLogSumLM f) =
      (0 : DeningerMeyerStrongLogCohomology) := by
  rw [Submodule.Quotient.mk_eq_zero]
  exact ⟨f, rfl⟩

/-! ## Paugam weighted inversion on the exact target -/

theorem DeningerMeyerStrongLogDecay.deriv
    {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) :
    DeningerMeyerStrongLogDecay (deriv g) where
  smooth := (contDiff_infty_iff_deriv.mp hg.smooth).2
  decayTop := by
    intro n a
    rw [← iteratedDeriv_succ']
    exact hg.decayTop (n + 1) a
  decayBot := by
    intro n b
    rw [← iteratedDeriv_succ']
    exact hg.decayBot (n + 1) b

theorem DeningerMeyerStrongLogDecay.neg
    {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) :
    DeningerMeyerStrongLogDecay (-g) := by
  rw [show (-g) = (-1 : ℂ) • g by
    funext t
    simp]
  exact hg.smul (-1)

/-- Conjugate Euler operator `A = -(1 + d/dt)` on raw log functions. -/
def deningerMeyerStrongReflectedEuler
    (g : ℝ → ℂ) : ℝ → ℂ :=
  -(g + deriv g)

/-- Iterates of the conjugate Euler operator. -/
def deningerMeyerStrongReflectedEulerIterate :
    ℕ → (ℝ → ℂ) → (ℝ → ℂ)
  | 0, g => g
  | n + 1, g =>
      deningerMeyerStrongReflectedEuler
        (deningerMeyerStrongReflectedEulerIterate n g)

@[simp]
theorem deningerMeyerStrongReflectedEulerIterate_zero
    (g : ℝ → ℂ) :
    deningerMeyerStrongReflectedEulerIterate 0 g = g :=
  rfl

theorem deningerMeyerStrongReflectedEulerIterate_succ
    (n : ℕ) (g : ℝ → ℂ) :
    deningerMeyerStrongReflectedEulerIterate (n + 1) g =
      deningerMeyerStrongReflectedEuler
        (deningerMeyerStrongReflectedEulerIterate n g) :=
  rfl

theorem DeningerMeyerStrongLogDecay.reflectedEuler
    {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) :
    DeningerMeyerStrongLogDecay
      (deningerMeyerStrongReflectedEuler g) := by
  exact (hg.add hg.deriv).neg

theorem DeningerMeyerStrongLogDecay.reflectedEulerIterate
    {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) (n : ℕ) :
    DeningerMeyerStrongLogDecay
      (deningerMeyerStrongReflectedEulerIterate n g) := by
  induction n with
  | zero =>
      exact hg
  | succ n ih =>
      exact ih.reflectedEuler

/-- Paugam's weighted reciprocal involution in logarithmic radius. -/
def deningerMeyerStrongLogJFun
    (g : ℝ → ℂ) (t : ℝ) : ℂ :=
  (Real.exp (-t) : ℂ) * g (-t)

private theorem hasDerivAt_deningerMeyerStrongLogJFun
    {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) (t : ℝ) :
    HasDerivAt (deningerMeyerStrongLogJFun g)
      (deningerMeyerStrongLogJFun
        (deningerMeyerStrongReflectedEuler g) t) t := by
  have hneg : HasDerivAt (fun s : ℝ => -s) (-1) t :=
    hasDerivAt_neg t
  have hexpR :
      HasDerivAt (fun s : ℝ => Real.exp (-s))
        (-Real.exp (-t)) t := by
    have hraw :
        HasDerivAt
          (Real.exp ∘ fun s : ℝ => -s)
          (-Real.exp (-t)) t :=
      ((Real.hasDerivAt_exp (-t)).comp t hneg).congr_deriv
        (by simp)
    apply hraw.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun _ => rfl
  have hexpC :
      HasDerivAt (fun s : ℝ => (Real.exp (-s) : ℂ))
        (-Real.exp (-t) : ℂ) t := by
    simpa only [Complex.ofReal_neg] using hexpR.ofReal_comp
  have hgAt :
      HasDerivAt g (deriv g (-t)) (-t) :=
    (hg.smooth.differentiable
      (by simp)).differentiableAt.hasDerivAt
  have hinnerRaw := hgAt.scomp t hneg
  have hinner :
      HasDerivAt (fun s : ℝ => g (-s))
        (-deriv g (-t)) t := by
    have h' :
        HasDerivAt (g ∘ fun s : ℝ => -s)
          (-deriv g (-t)) t :=
      hinnerRaw.congr_deriv (by
        simp only [Complex.real_smul,
          Complex.ofReal_neg, Complex.ofReal_one,
          neg_mul, one_mul])
    apply h'.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun _ => rfl
  have hmul := hexpC.mul hinner
  have hcoef :
      (-Real.exp (-t) : ℂ) * g (-t) +
        (Real.exp (-t) : ℂ) * -deriv g (-t) =
      (Real.exp (-t) : ℂ) *
        deningerMeyerStrongReflectedEuler g (-t) := by
    simp only [deningerMeyerStrongReflectedEuler,
      Pi.neg_apply, Pi.add_apply]
    ring
  apply (hmul.congr_deriv hcoef).congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun _ => rfl

theorem deriv_deningerMeyerStrongLogJFun
    {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) :
    deriv (deningerMeyerStrongLogJFun g) =
      deningerMeyerStrongLogJFun
        (deningerMeyerStrongReflectedEuler g) := by
  funext t
  exact
    (hasDerivAt_deningerMeyerStrongLogJFun hg t).deriv

theorem iteratedDeriv_deningerMeyerStrongLogJFun
    {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) (n : ℕ) :
    iteratedDeriv n (deningerMeyerStrongLogJFun g) =
      deningerMeyerStrongLogJFun
        (deningerMeyerStrongReflectedEulerIterate n g) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      rw [iteratedDeriv_succ, ih,
        deriv_deningerMeyerStrongLogJFun
          (hg.reflectedEulerIterate n)]
      rfl

private theorem deningerMeyerStrongLogJ_top_weight
    (t a : ℝ) :
    Real.exp (-t) *
        Real.exp (-t) ^ (a - 1) =
      Real.exp t ^ (-a) := by
  rw [← Real.exp_mul (-t) (a - 1),
    ← Real.exp_mul t (-a),
    ← Real.exp_add]
  congr 1
  ring

private theorem deningerMeyerStrongLogJ_bot_weight
    (t b : ℝ) :
    Real.exp (-t) *
        Real.exp (-t) ^ (-(b + 1)) =
      Real.exp t ^ b := by
  rw [← Real.exp_mul (-t) (-(b + 1)),
    ← Real.exp_mul t b,
    ← Real.exp_add]
  congr 1
  ring

theorem deningerMeyerStrongLogJFun_isBigO_atTop
    {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g)
    (a : ℝ) :
    deningerMeyerStrongLogJFun g =O[atTop]
      fun t : ℝ => Real.exp t ^ (-a) := by
  have hbase := hg.decayBot 0 (a - 1)
  rw [iteratedDeriv_zero] at hbase
  have hcomp :=
    hbase.comp_tendsto tendsto_neg_atTop_atBot
  obtain ⟨C, hC⟩ := hcomp.bound
  refine
    (Asymptotics.IsBigOWith.of_bound
      (c := C) ?_).isBigO
  filter_upwards [hC] with t ht
  have ht' :
      ‖g (-t)‖ ≤
        C * ‖Real.exp (-t) ^ (a - 1)‖ := by
    simpa only [Function.comp_apply] using ht
  have hw :
      0 ≤ Real.exp (-t) ^ (a - 1) :=
    Real.rpow_nonneg (Real.exp_pos (-t)).le _
  have htarget :
      0 ≤ Real.exp t ^ (-a) :=
    Real.rpow_nonneg (Real.exp_pos t).le _
  rw [deningerMeyerStrongLogJFun,
    norm_mul, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos (-t)),
    show ‖Real.exp t ^ (-a)‖ =
        Real.exp t ^ (-a) by
      rw [Real.norm_eq_abs, abs_of_nonneg htarget]]
  calc
    Real.exp (-t) * ‖g (-t)‖ ≤
        Real.exp (-t) *
          (C * ‖Real.exp (-t) ^ (a - 1)‖) :=
      mul_le_mul_of_nonneg_left ht'
        (Real.exp_pos (-t)).le
    _ = C * (Real.exp (-t) *
        Real.exp (-t) ^ (a - 1)) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hw]
      ring
    _ = C * Real.exp t ^ (-a) := by
      rw [deningerMeyerStrongLogJ_top_weight]

theorem deningerMeyerStrongLogJFun_isBigO_atBot
    {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g)
    (b : ℝ) :
    deningerMeyerStrongLogJFun g =O[atBot]
      fun t : ℝ => Real.exp t ^ b := by
  have hbase := hg.decayTop 0 (b + 1)
  rw [iteratedDeriv_zero] at hbase
  have hcomp :=
    hbase.comp_tendsto tendsto_neg_atBot_atTop
  obtain ⟨C, hC⟩ := hcomp.bound
  refine
    (Asymptotics.IsBigOWith.of_bound
      (c := C) ?_).isBigO
  filter_upwards [hC] with t ht
  have ht' :
      ‖g (-t)‖ ≤
        C * ‖Real.exp (-t) ^ (-(b + 1))‖ := by
    simpa only [Function.comp_apply] using ht
  have hw :
      0 ≤ Real.exp (-t) ^ (-(b + 1)) :=
    Real.rpow_nonneg (Real.exp_pos (-t)).le _
  have htarget :
      0 ≤ Real.exp t ^ b :=
    Real.rpow_nonneg (Real.exp_pos t).le _
  rw [deningerMeyerStrongLogJFun,
    norm_mul, Complex.norm_real,
    Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos (-t)),
    show ‖Real.exp t ^ b‖ =
        Real.exp t ^ b by
      rw [Real.norm_eq_abs, abs_of_nonneg htarget]]
  calc
    Real.exp (-t) * ‖g (-t)‖ ≤
        Real.exp (-t) *
          (C * ‖Real.exp (-t) ^ (-(b + 1))‖) :=
      mul_le_mul_of_nonneg_left ht'
        (Real.exp_pos (-t)).le
    _ = C * (Real.exp (-t) *
        Real.exp (-t) ^ (-(b + 1))) := by
      rw [Real.norm_eq_abs, abs_of_nonneg hw]
      ring
    _ = C * Real.exp t ^ b := by
      rw [deningerMeyerStrongLogJ_bot_weight]

/-- Paugam's weighted inversion preserves the full all-derivative,
all-exponential-weight target. -/
theorem deningerMeyerStrongLogDecay_J
    {g : ℝ → ℂ}
    (hg : DeningerMeyerStrongLogDecay g) :
    DeningerMeyerStrongLogDecay
      (deningerMeyerStrongLogJFun g) where
  smooth := by
    have hreal :
        ContDiff ℝ ∞
          (fun t : ℝ => Real.exp (-t)) := by
      fun_prop
    have hfactor :
        ContDiff ℝ ∞
          (fun t : ℝ => (Real.exp (-t) : ℂ)) := by
      exact Complex.ofRealCLM.contDiff.comp hreal
    have hreflect :
        ContDiff ℝ ∞ (fun t : ℝ => g (-t)) :=
      hg.smooth.comp (by fun_prop)
    exact hfactor.mul hreflect
  decayTop := by
    intro n a
    rw [iteratedDeriv_deningerMeyerStrongLogJFun hg]
    exact deningerMeyerStrongLogJFun_isBigO_atTop
      (hg.reflectedEulerIterate n) a
  decayBot := by
    intro n b
    rw [iteratedDeriv_deningerMeyerStrongLogJFun hg]
    exact deningerMeyerStrongLogJFun_isBigO_atBot
      (hg.reflectedEulerIterate n) b

/-- Paugam's `J` as a linear endomorphism of the exact all-weight target. -/
def deningerMeyerStrongLogJ :
    DeningerMeyerStrongLogTarget →ₗ[ℂ]
      DeningerMeyerStrongLogTarget where
  toFun g :=
    ⟨deningerMeyerStrongLogJFun g,
      deningerMeyerStrongLogDecay_J g.property⟩
  map_add' g h := by
    apply Subtype.ext
    funext t
    simp [deningerMeyerStrongLogJFun]
    ring
  map_smul' c g := by
    apply Subtype.ext
    funext t
    simp [deningerMeyerStrongLogJFun]
    ring

@[simp]
theorem deningerMeyerStrongLogJ_apply
    (g : DeningerMeyerStrongLogTarget) (t : ℝ) :
    ((deningerMeyerStrongLogJ g :
      DeningerMeyerStrongLogTarget) : ℝ → ℂ) t =
      (Real.exp (-t) : ℂ) *
        (g : ℝ → ℂ) (-t) :=
  rfl

@[simp]
theorem deningerMeyerStrongLogJ_sq
    (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogJ
        (deningerMeyerStrongLogJ g) = g := by
  apply Subtype.ext
  funext t
  simp only [deningerMeyerStrongLogJ_apply, neg_neg]
  rw [← mul_assoc]
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  simp

/-- Exact Poisson boundary intertwining: `J Z(f) = Z(𝓕 f)`. -/
@[simp]
theorem deningerMeyerStrongLogJ_boundary
    (f : DeningerMeyerCap) :
    deningerMeyerStrongLogJ
        (deningerMeyerStrongLogSumLM f) =
      deningerMeyerStrongLogSumLM
        (deningerMeyerCapFourierLM f) := by
  apply Subtype.ext
  funext t
  change (Real.exp (-t) : ℂ) *
      deningerMeyerLogSum f (-t) =
    deningerMeyerLogSum
      (FourierTransform.fourierCLE ℂ
        (SchwartzMap ℝ ℂ) f) t
  have href :=
    deningerMeyerLogSum_reflection f f.property (-t)
  have href' :
      deningerMeyerLogSum f (-t) =
      (Real.exp t : ℂ) *
        deningerMeyerLogSum
          (FourierTransform.fourierCLE ℂ
            (SchwartzMap ℝ ℂ) f) t := by
    simpa [deningerMeyerLogReflection] using href
  rw [href']
  rw [← mul_assoc]
  rw [← Complex.ofReal_mul, ← Real.exp_add]
  simp

theorem deningerMeyerStrongLogJ_range_le :
    LinearMap.range deningerMeyerStrongLogSumLM ≤
      (LinearMap.range
        deningerMeyerStrongLogSumLM).comap
          deningerMeyerStrongLogJ := by
  rintro _ ⟨f, rfl⟩
  exact
    ⟨deningerMeyerCapFourierLM f,
      (deningerMeyerStrongLogJ_boundary f).symm⟩

/-- Paugam's involution descended to actual all-weight middle cohomology. -/
def deningerMeyerStrongLogCohomologyJ :
    DeningerMeyerStrongLogCohomology →ₗ[ℂ]
      DeningerMeyerStrongLogCohomology :=
  (LinearMap.range
    deningerMeyerStrongLogSumLM).mapQ
      (LinearMap.range
        deningerMeyerStrongLogSumLM)
      deningerMeyerStrongLogJ
      deningerMeyerStrongLogJ_range_le

@[simp]
theorem deningerMeyerStrongLogCohomologyJ_mk
    (g : DeningerMeyerStrongLogTarget) :
    deningerMeyerStrongLogCohomologyJ
        (Submodule.Quotient.mk g) =
      Submodule.Quotient.mk
        (deningerMeyerStrongLogJ g) :=
  rfl

@[simp]
theorem deningerMeyerStrongLogCohomologyJ_sq
    (u : DeningerMeyerStrongLogCohomology) :
    deningerMeyerStrongLogCohomologyJ
        (deningerMeyerStrongLogCohomologyJ u) = u := by
  induction u using Submodule.Quotient.induction_on with
  | _ g =>
      simp

end

end RHTower
