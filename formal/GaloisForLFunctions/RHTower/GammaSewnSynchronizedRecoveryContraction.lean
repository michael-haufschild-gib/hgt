import GaloisForLFunctions.RHTower.GammaSewnSynchronizedLcmContraction
import GaloisForLFunctions.RHTower.GammaSewnMobiusXiWardHardyNonexpansive
import GaloisForLFunctions.RHTower.CothInfra
import GaloisForLFunctions.HTGeometry.LpCoordinateProjection
import Mathlib.Analysis.Calculus.LHopital

/-!
# Synchronized exponential-chord recovery contraction

The finite-aperture recovery multiplier in the Gamma-sewn synchronized-lcm source has a hidden
universal form.  Put

`f(t) = (1 - exp(-t)) / t`, with `f(0) = 1`.

The hyperbolic addition law gives the supermultiplicative chord inequality

`f(a) * f(b) ≤ f(a + b)` for `a,b ≥ 0`.

After exact cancellation of the Rees factors, the ratio between synchronized recovered density and
physical squarefree density is therefore controlled by

`prod_{p ∈ P} (cₓ(p) * f(x log p)) / f(x * sum_{p ∈ P} log p)`,

where every Gamma-sewn multiplier `cₓ(p)` is strictly between zero and one.  Consequently recovery
is nonexpansive on every finite prime support and is strictly contractive on every nonempty support
at every positive aperture.  This is not a singleton or rank-two estimate: it is the all-support
law required for a cofinal diagonal multiplier on the Boolean prime-support cube.
-/

open scoped BigOperators ComplexOrder
open Filter Set Topology

namespace RHTower

noncomputable section

/-- Normalized exponential chord, continuously completed at the origin. -/
def exponentialChordFactor (x : ℝ) : ℝ :=
  if x = 0 then 1 else (1 - Real.exp (-x)) / x

private theorem one_sub_exp_neg_eq
    (x : ℝ) :
    1 - Real.exp (-x) =
      2 * Real.exp (-(x / 2)) * Real.sinh (x / 2) := by
  rw [Real.sinh_eq]
  calc
    1 - Real.exp (-x) =
        Real.exp (-(x / 2)) * Real.exp (x / 2) -
          Real.exp (-(x / 2)) * Real.exp (-(x / 2)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      simp
      ring
    _ = 2 * Real.exp (-(x / 2)) *
        ((Real.exp (x / 2) - Real.exp (-(x / 2))) / 2) := by
      ring

theorem exponentialChordFactor_nonneg
    {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ exponentialChordFactor x := by
  by_cases hx0 : x = 0
  · simp [exponentialChordFactor, hx0]
  · rw [exponentialChordFactor, if_neg hx0]
    have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    exact div_nonneg
      (sub_nonneg.mpr (Real.exp_le_one_iff.mpr (by linarith))) hx

theorem exponentialChordFactor_pos
    {x : ℝ} (hx : 0 ≤ x) :
    0 < exponentialChordFactor x := by
  by_cases hx0 : x = 0
  · simp [exponentialChordFactor, hx0]
  · rw [exponentialChordFactor, if_neg hx0]
    have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    exact div_pos
      (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by linarith))) hxpos

/-- The continuous completion in `exponentialChordFactor` is genuine. -/
theorem continuousAt_exponentialChordFactor_zero :
    ContinuousAt exponentialChordFactor 0 := by
  let g : ℝ → ℝ := fun x => 1 - Real.exp (-x)
  have hg : HasDerivAt g 1 0 := by
    unfold g
    convert (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub
      ((Real.hasDerivAt_exp (-0)).comp 0 (hasDerivAt_neg 0)) using 1
    all_goals norm_num
  have heq : exponentialChordFactor = dslope g 0 := by
    funext x
    by_cases hx : x = 0
    · subst x
      rw [dslope_same, hg.deriv]
      simp [exponentialChordFactor]
    · rw [dslope_of_ne g hx, slope_def_field]
      simp [g, exponentialChordFactor, hx]
  rw [heq, continuousAt_dslope_same]
  exact hg.differentiableAt

/-- First jet of the normalized exponential chord at its lossless endpoint. -/
theorem hasDerivAt_exponentialChordFactor_zero :
    HasDerivAt exponentialChordFactor (-1 / 2) 0 := by
  have hbase :
      Tendsto (fun y : ℝ => -Real.exp (-y) / 2)
        (𝓝[≠] 0) (𝓝 (-1 / 2 : ℝ)) := by
    have hcont :
        ContinuousAt (fun y : ℝ => -Real.exp (-y) / 2) 0 := by
      fun_prop
    simpa using hcont.tendsto.mono_left inf_le_left
  have hfirst :
      Tendsto
        (fun y : ℝ => (Real.exp (-y) - 1) / (2 * y))
        (𝓝[≠] 0) (𝓝 (-1 / 2 : ℝ)) := by
    refine HasDerivAt.lhopital_zero_nhdsNE
      (f' := fun y : ℝ => -Real.exp (-y))
      (g' := fun _y : ℝ => 2) ?_ ?_ ?_ ?_ ?_ hbase
    · exact Filter.Eventually.of_forall fun y => by
        convert
          (((Real.hasDerivAt_exp (-y)).comp y (hasDerivAt_neg y)).sub_const 1)
            using 1
        all_goals simp
    · exact Filter.Eventually.of_forall fun y => by
        convert (hasDerivAt_id y).const_mul 2 using 1
        all_goals simp
    · exact Filter.Eventually.of_forall fun _ => by norm_num
    · have hcont :
          ContinuousAt (fun y : ℝ => Real.exp (-y) - 1) 0 := by
        fun_prop
      simpa using hcont.tendsto.mono_left inf_le_left
    · have hcont : ContinuousAt (fun y : ℝ => 2 * y) 0 := by
        fun_prop
      simpa using hcont.tendsto.mono_left inf_le_left
  have hmain :
      Tendsto
        (fun y : ℝ => (1 - Real.exp (-y) - y) / y ^ 2)
        (𝓝[≠] 0) (𝓝 (-1 / 2 : ℝ)) := by
    refine HasDerivAt.lhopital_zero_nhdsNE
      (f' := fun y : ℝ => Real.exp (-y) - 1)
      (g' := fun y : ℝ => 2 * y) ?_ ?_ ?_ ?_ ?_ hfirst
    · exact Filter.Eventually.of_forall fun y => by
        convert
          ((hasDerivAt_const (x := y) (c := (1 : ℝ))).sub
              ((Real.hasDerivAt_exp (-y)).comp y (hasDerivAt_neg y))).sub
            (hasDerivAt_id y) using 1
        all_goals simp
    · exact Filter.Eventually.of_forall fun y => by
        convert hasDerivAt_pow 2 y using 1
        simp
    · filter_upwards [self_mem_nhdsWithin] with y hy
      simp only [mem_compl_iff, mem_singleton_iff] at hy
      exact mul_ne_zero (by norm_num) hy
    · have hcont :
          ContinuousAt (fun y : ℝ => 1 - Real.exp (-y) - y) 0 := by
        fun_prop
      simpa using hcont.tendsto.mono_left inf_le_left
    · have hcont : ContinuousAt (fun y : ℝ => y ^ 2) 0 := by
        fun_prop
      simpa using hcont.tendsto.mono_left inf_le_left
  rw [hasDerivAt_iff_tendsto_slope]
  apply hmain.congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [mem_compl_iff, mem_singleton_iff] at hy
  rw [slope_def_field]
  simp [exponentialChordFactor, hy]
  field_simp [hy]

/-- **Universal exponential-chord law.**  Normalized exponential chords are supermultiplicative
under addition of nonnegative lengths. -/
theorem exponentialChordFactor_mul_le
    {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    exponentialChordFactor x * exponentialChordFactor y ≤
      exponentialChordFactor (x + y) := by
  by_cases hx0 : x = 0
  · subst x
    simp [exponentialChordFactor]
  by_cases hy0 : y = 0
  · subst y
    simp [exponentialChordFactor]
  have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
  have hypos : 0 < y := lt_of_le_of_ne hy (Ne.symm hy0)
  have hxy : 0 < x + y := add_pos hxpos hypos
  have ha : 0 ≤ x / 2 := by positivity
  have hb : 0 ≤ y / 2 := by positivity
  have hsa : Real.sinh (x / 2) ≤
      (x / 2) * Real.cosh (x / 2) :=
    sinh_le_mul_cosh ha
  have hsb : Real.sinh (y / 2) ≤
      (y / 2) * Real.cosh (y / 2) :=
    sinh_le_mul_cosh hb
  have hsapos : 0 ≤ Real.sinh (x / 2) :=
    Real.sinh_nonneg_iff.mpr ha
  have hsbpos : 0 ≤ Real.sinh (y / 2) :=
    Real.sinh_nonneg_iff.mpr hb
  have hleft :
      (x / 2) * Real.sinh (x / 2) * Real.sinh (y / 2) ≤
        (x / 2) * (y / 2) * Real.sinh (x / 2) * Real.cosh (y / 2) := by
    have := mul_le_mul_of_nonneg_left hsb
      (mul_nonneg ha hsapos)
    nlinarith
  have hright :
      (y / 2) * Real.sinh (x / 2) * Real.sinh (y / 2) ≤
        (x / 2) * (y / 2) * Real.cosh (x / 2) * Real.sinh (y / 2) := by
    have := mul_le_mul_of_nonneg_right hsa
      (mul_nonneg hy hsbpos)
    nlinarith
  have hsinh :
      ((x + y) / 2) * Real.sinh (x / 2) * Real.sinh (y / 2) ≤
        (x / 2) * (y / 2) * Real.sinh ((x + y) / 2) := by
    rw [show (x + y) / 2 = x / 2 + y / 2 by ring,
      Real.sinh_add]
    nlinarith
  simp only [exponentialChordFactor, hx0, hy0, hxy.ne', if_false]
  rw [one_sub_exp_neg_eq x, one_sub_exp_neg_eq y,
    one_sub_exp_neg_eq (x + y)]
  have hexp :
      Real.exp (-(x / 2)) * Real.exp (-(y / 2)) =
        Real.exp (-((x + y) / 2)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [div_mul_div_comm]
  rw [div_le_div_iff₀ (mul_pos hxpos hypos) hxy]
  calc
    (2 * Real.exp (-(x / 2)) * Real.sinh (x / 2) *
          (2 * Real.exp (-(y / 2)) * Real.sinh (y / 2))) *
        (x + y) =
      8 * Real.exp (-((x + y) / 2)) *
        (((x + y) / 2) * Real.sinh (x / 2) * Real.sinh (y / 2)) := by
          rw [← hexp]
          ring
    _ ≤ 8 * Real.exp (-((x + y) / 2)) *
        ((x / 2) * (y / 2) * Real.sinh ((x + y) / 2)) := by
          exact mul_le_mul_of_nonneg_left hsinh (by positivity)
    _ = (2 * Real.exp (-((x + y) / 2)) *
          Real.sinh ((x + y) / 2)) * (x * y) := by ring

/-- Finite-product form of the universal exponential-chord law. -/
theorem prod_exponentialChordFactor_le
    {α : Type*} [DecidableEq α]
    (s : Finset α) (y : α → ℝ)
    (hy : ∀ i ∈ s, 0 ≤ y i) :
    ∏ i ∈ s, exponentialChordFactor (y i) ≤
      exponentialChordFactor (∑ i ∈ s, y i) := by
  induction s using Finset.induction_on with
  | empty =>
      simp [exponentialChordFactor]
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      have hya : 0 ≤ y a := hy a (Finset.mem_insert_self a s)
      have hys : ∀ i ∈ s, 0 ≤ y i := by
        intro i hi
        exact hy i (Finset.mem_insert_of_mem hi)
      have hsum : 0 ≤ ∑ i ∈ s, y i :=
        Finset.sum_nonneg fun i hi ↦ hys i hi
      calc
        exponentialChordFactor (y a) *
              ∏ i ∈ s, exponentialChordFactor (y i) ≤
            exponentialChordFactor (y a) *
              exponentialChordFactor (∑ i ∈ s, y i) := by
                exact mul_le_mul_of_nonneg_left (ih hys)
                  (exponentialChordFactor_nonneg hya)
        _ ≤ exponentialChordFactor (y a + ∑ i ∈ s, y i) :=
          exponentialChordFactor_mul_le hya hsum

/-- Chord supermultiplicativity survives arbitrary coordinatewise contractions. -/
theorem prod_contracted_exponentialChordFactor_le
    {α : Type*} [DecidableEq α]
    (s : Finset α) (c y : α → ℝ)
    (hc0 : ∀ i ∈ s, 0 ≤ c i)
    (hc1 : ∀ i ∈ s, c i ≤ 1)
    (hy : ∀ i ∈ s, 0 ≤ y i) :
    ∏ i ∈ s, (c i * exponentialChordFactor (y i)) ≤
      exponentialChordFactor (∑ i ∈ s, y i) := by
  calc
    ∏ i ∈ s, (c i * exponentialChordFactor (y i)) ≤
        ∏ i ∈ s, exponentialChordFactor (y i) := by
      exact Finset.prod_le_prod
        (fun i hi ↦ mul_nonneg (hc0 i hi)
          (exponentialChordFactor_nonneg (hy i hi)))
        (fun i hi ↦ by
          simpa using mul_le_of_le_one_left
            (exponentialChordFactor_nonneg (hy i hi)) (hc1 i hi))
    _ ≤ exponentialChordFactor (∑ i ∈ s, y i) :=
      prod_exponentialChordFactor_le s y hy

/-- The synchronized lcm aperture node depends only on total prime-log length. -/
theorem gammaSewnSynchronizedLcmNode_eq_exp_sum
    (x : ℝ) (P : Finset Nat.Primes) :
    gammaSewnSynchronizedLcmNode x P =
      Real.exp (-x * ∑ p ∈ P, Real.log (p : ℝ)) := by
  classical
  unfold gammaSewnSynchronizedLcmNode
  simp only [xiMobiusContinuousApertureDiskNode]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum]

private theorem transverse_unit_fraction_eq
    (p : Nat.Primes) :
    xiTransversePrimeApertureDiskNode 1 p /
        (1 + xiTransversePrimeApertureDiskNode 1 p) =
      1 / ((p : ℝ) + 1) := by
  rw [xiTransversePrimeApertureDiskNode_one_eq_inv]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  field_simp

private theorem card_sub_one_add_one
    {α : Type*} [DecidableEq α] {P : Finset α} (hP : P.Nonempty) :
    P.card - 1 + 1 = P.card := by
  have hcard : 0 < P.card := Finset.card_pos.mpr hP
  omega

/-- Exact all-support Rees/chord cancellation identity. -/
theorem gammaSewnSynchronized_rees_chord_identity
    {x : ℝ} (hx : 0 < x)
    {P : Finset Nat.Primes} (hP : P.Nonempty) :
    gammaSewnSynchronizedLcmReesRenormalizedWeight x P *
        exponentialChordFactor
          (x * ∑ p ∈ P, Real.log (p : ℝ)) =
      gammaSewnSynchronizedLcmReesBoundary P *
        ∏ p ∈ P,
          (gammaSewnMobiusValuationContractionMultiplier x p *
            exponentialChordFactor (x * Real.log (p : ℝ))) := by
  classical
  have hlog (p : Nat.Primes) : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hsum : 0 < ∑ p ∈ P, Real.log (p : ℝ) :=
    Finset.sum_pos (fun p hp ↦ hlog p) hP
  have hxs : 0 < x * ∑ p ∈ P, Real.log (p : ℝ) :=
    mul_pos hx hsum
  have hxp (p : Nat.Primes) : 0 < x * Real.log (p : ℝ) :=
    mul_pos hx (hlog p)
  have htotal :
      1 - Real.exp (-(x * ∑ p ∈ P, Real.log (p : ℝ))) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact ne_of_gt (Real.exp_lt_one_iff.mpr (by linarith [hxs]))
  have hlocal (p : Nat.Primes) :
      (Real.log (p : ℝ) / ((p : ℝ) + 1)) *
          (gammaSewnMobiusValuationContractionMultiplier x p *
              (1 - Real.exp (-(x * Real.log (p : ℝ)))) /
            (x * Real.log (p : ℝ))) =
        (gammaSewnMobiusValuationContractionMultiplier x p *
              (1 - Real.exp (-(x * Real.log (p : ℝ)))) /
            ((p : ℝ) + 1)) / x := by
    field_simp [hx.ne', (hlog p).ne']
  have hprod :
      (∏ p ∈ P, Real.log (p : ℝ) / ((p : ℝ) + 1)) *
          (∏ p ∈ P,
            gammaSewnMobiusValuationContractionMultiplier x p *
                (1 - Real.exp (-(x * Real.log (p : ℝ)))) /
              (x * Real.log (p : ℝ))) =
        (∏ p ∈ P,
            gammaSewnMobiusValuationContractionMultiplier x p *
                (1 - Real.exp (-(x * Real.log (p : ℝ)))) /
              ((p : ℝ) + 1)) / x ^ P.card := by
    rw [← Finset.prod_mul_distrib]
    simp_rw [hlocal]
    rw [Finset.prod_div_distrib, Finset.prod_const]
  simp only [gammaSewnSynchronizedLcmReesRenormalizedWeight,
    gammaSewnSynchronizedLcmReesBoundary, if_neg hP.ne_empty,
    gammaSewnSynchronizedLcmWeight, gammaSewnSynchronizedLcmNumerator,
    exponentialChordFactor, hxs.ne', (hxp _).ne', if_false]
  rw [gammaSewnSynchronizedLcmNode_eq_exp_sum]
  simp_rw [transverse_unit_fraction_eq]
  simp_rw [xiMobiusContinuousApertureDiskNode]
  field_simp [hx.ne', hsum.ne', htotal, (hlog _).ne', (hxp _).ne',
    (show (0 : ℝ) < (↑(↑_ : Nat.Primes) : ℝ) + 1 by positivity).ne']
  rw [show
      (x * x ^ (P.card - 1) *
            ∏ p ∈ P, Real.log (p : ℝ) / ((p : ℝ) + 1)) *
          ∏ p ∈ P,
            gammaSewnMobiusValuationContractionMultiplier x p *
                (1 - Real.exp (-(x * Real.log (p : ℝ)))) /
              (x * Real.log (p : ℝ)) =
        (x * x ^ (P.card - 1)) *
          ((∏ p ∈ P, Real.log (p : ℝ) / ((p : ℝ) + 1)) *
            ∏ p ∈ P,
              gammaSewnMobiusValuationContractionMultiplier x p *
                  (1 - Real.exp (-(x * Real.log (p : ℝ)))) /
                (x * Real.log (p : ℝ))) by ring,
    hprod]
  have hxpow : x ^ P.card = x * x ^ (P.card - 1) := by
    conv_lhs => rw [← card_sub_one_add_one hP, pow_succ]
    ring
  rw [← hxpow]
  field_simp [hx.ne']

/-- Exact recovered/physical density identity exposing the universal chord quotient. -/
theorem gammaSewnSynchronized_recovered_chord_identity
    (nu : Nat.Primes → ℝ)
    {x : ℝ} (hx : 0 < x)
    {P : Finset Nat.Primes} (hP : P.Nonempty) :
    gammaSewnSynchronizedRecoveredDensity nu x P *
        exponentialChordFactor
          (x * ∑ p ∈ P, Real.log (p : ℝ)) =
      synchronizedSquarefreePhysicalDensity nu P *
        ∏ p ∈ P,
          (gammaSewnMobiusValuationContractionMultiplier x p *
            exponentialChordFactor (x * Real.log (p : ℝ))) := by
  rw [gammaSewnSynchronizedRecoveredDensity, if_neg hP.ne_empty]
  calc
    (gammaSewnSynchronizedDensityRecovery nu P *
          gammaSewnSynchronizedLcmReesRenormalizedWeight x P) *
        exponentialChordFactor (x * ∑ p ∈ P, Real.log (p : ℝ)) =
      gammaSewnSynchronizedDensityRecovery nu P *
        (gammaSewnSynchronizedLcmReesRenormalizedWeight x P *
          exponentialChordFactor (x * ∑ p ∈ P, Real.log (p : ℝ))) := by ring
    _ = gammaSewnSynchronizedDensityRecovery nu P *
        (gammaSewnSynchronizedLcmReesBoundary P *
          ∏ p ∈ P,
            (gammaSewnMobiusValuationContractionMultiplier x p *
              exponentialChordFactor (x * Real.log (p : ℝ)))) := by
          rw [gammaSewnSynchronized_rees_chord_identity hx hP]
    _ = (gammaSewnSynchronizedDensityRecovery nu P *
          gammaSewnSynchronizedLcmReesBoundary P) *
        ∏ p ∈ P,
          (gammaSewnMobiusValuationContractionMultiplier x p *
            exponentialChordFactor (x * Real.log (p : ℝ))) := by ring
    _ = synchronizedSquarefreePhysicalDensity nu P *
        ∏ p ∈ P,
          (gammaSewnMobiusValuationContractionMultiplier x p *
            exponentialChordFactor (x * Real.log (p : ℝ))) := by
          rw [gammaSewnSynchronizedDensityRecovery_mul_reesBoundary nu hP]

/-- **All-support synchronized recovery nonexpansiveness.**  Finite-aperture recovery never exceeds
physical squarefree density on any finite prime support. -/
theorem gammaSewnSynchronizedRecoveredDensity_le_physical
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 ≤ nu p)
    {x : ℝ} (hx : 0 < x)
    (P : Finset Nat.Primes) :
    gammaSewnSynchronizedRecoveredDensity nu x P ≤
      synchronizedSquarefreePhysicalDensity nu P := by
  classical
  by_cases hP0 : P = ∅
  · subst P
    simp [synchronizedSquarefreePhysicalDensity]
  have hP : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hP0
  have hlog (p : Nat.Primes) : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hsum : 0 < ∑ p ∈ P, Real.log (p : ℝ) :=
    Finset.sum_pos (fun p hp ↦ hlog p) hP
  have hphysical :
      0 ≤ synchronizedSquarefreePhysicalDensity nu P := by
    unfold synchronizedSquarefreePhysicalDensity
    exact Finset.prod_nonneg fun p hp ↦
      div_nonneg (hnu p) (by positivity)
  have hcontract :
      ∏ p ∈ P,
          (gammaSewnMobiusValuationContractionMultiplier x p *
            exponentialChordFactor (x * Real.log (p : ℝ))) ≤
        exponentialChordFactor
          (x * ∑ p ∈ P, Real.log (p : ℝ)) := by
    rw [Finset.mul_sum]
    exact prod_contracted_exponentialChordFactor_le P
      (gammaSewnMobiusValuationContractionMultiplier x)
      (fun p ↦ x * Real.log (p : ℝ))
      (fun p hp ↦
        (gammaSewnMobiusValuationContractionMultiplier_pos x p).le)
      (fun p hp ↦
        (gammaSewnMobiusValuationContractionMultiplier_lt_one hx p).le)
      (fun p hp ↦ (mul_pos hx (hlog p)).le)
  have hfactor :
      0 < exponentialChordFactor
        (x * ∑ p ∈ P, Real.log (p : ℝ)) :=
    exponentialChordFactor_pos (mul_pos hx hsum).le
  apply le_of_mul_le_mul_right _ hfactor
  rw [gammaSewnSynchronized_recovered_chord_identity nu hx hP]
  exact mul_le_mul_of_nonneg_left hcontract hphysical

/-- Every nonempty finite support is strictly contracted at every positive aperture. -/
theorem gammaSewnSynchronizedRecoveredDensity_lt_physical
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    {x : ℝ} (hx : 0 < x)
    {P : Finset Nat.Primes} (hP : P.Nonempty) :
    gammaSewnSynchronizedRecoveredDensity nu x P <
      synchronizedSquarefreePhysicalDensity nu P := by
  classical
  have hlog (p : Nat.Primes) : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hsum : 0 < ∑ p ∈ P, Real.log (p : ℝ) :=
    Finset.sum_pos (fun p hp ↦ hlog p) hP
  have hphysical :
      0 < synchronizedSquarefreePhysicalDensity nu P := by
    unfold synchronizedSquarefreePhysicalDensity
    exact Finset.prod_pos fun p hp ↦ div_pos (hnu p)
      (by exact_mod_cast p.2.pos)
  have hlocalProd :
      ∏ p ∈ P,
          (gammaSewnMobiusValuationContractionMultiplier x p *
            exponentialChordFactor (x * Real.log (p : ℝ))) <
        ∏ p ∈ P, exponentialChordFactor (x * Real.log (p : ℝ)) := by
    apply Finset.prod_lt_prod
    · intro p hp
      exact mul_pos
        (gammaSewnMobiusValuationContractionMultiplier_pos x p)
        (exponentialChordFactor_pos (mul_pos hx (hlog p)).le)
    · intro p hp
      exact mul_le_of_le_one_left
        (exponentialChordFactor_nonneg (mul_pos hx (hlog p)).le)
        (gammaSewnMobiusValuationContractionMultiplier_lt_one hx p).le
    · obtain ⟨p, hp⟩ := hP
      refine ⟨p, hp, ?_⟩
      exact mul_lt_of_lt_one_left
        (exponentialChordFactor_pos (mul_pos hx (hlog p)).le)
        (gammaSewnMobiusValuationContractionMultiplier_lt_one hx p)
  have hcontract :
      ∏ p ∈ P,
          (gammaSewnMobiusValuationContractionMultiplier x p *
            exponentialChordFactor (x * Real.log (p : ℝ))) <
        exponentialChordFactor
          (x * ∑ p ∈ P, Real.log (p : ℝ)) := by
    rw [Finset.mul_sum]
    exact hlocalProd.trans_le
      (prod_exponentialChordFactor_le P
        (fun p ↦ x * Real.log (p : ℝ))
        (fun p hp ↦ (mul_pos hx (hlog p)).le))
  have hfactor :
      0 < exponentialChordFactor
        (x * ∑ p ∈ P, Real.log (p : ℝ)) :=
    exponentialChordFactor_pos (mul_pos hx hsum).le
  apply lt_of_mul_lt_mul_right _ hfactor.le
  rw [gammaSewnSynchronized_recovered_chord_identity nu hx hP]
  exact mul_lt_mul_of_pos_left hcontract hphysical

/-! ## Cofinal signed-recovery multiplier -/

/-- Dimensionless multiplier from physical squarefree density to synchronized recovered density. -/
def gammaSewnSynchronizedRecoveryRatio
    (nu : Nat.Primes → ℝ) (x : ℝ) (P : Finset Nat.Primes) : ℝ :=
  gammaSewnSynchronizedRecoveredDensity nu x P /
    synchronizedSquarefreePhysicalDensity nu P

theorem synchronizedSquarefreePhysicalDensity_pos
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) :
    0 < synchronizedSquarefreePhysicalDensity nu P := by
  unfold synchronizedSquarefreePhysicalDensity
  exact Finset.prod_pos fun p hp ↦ div_pos (hnu p)
    (by exact_mod_cast p.2.pos)

theorem gammaSewnSynchronizedRecoveredDensity_pos
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    {x : ℝ} (hx : 0 < x)
    (P : Finset Nat.Primes) :
    0 < gammaSewnSynchronizedRecoveredDensity nu x P := by
  classical
  by_cases hP0 : P = ∅
  · subst P
    simp
  have hP : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hP0
  have hlog (p : Nat.Primes) : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hsum : 0 < ∑ p ∈ P, Real.log (p : ℝ) :=
    Finset.sum_pos (fun p hp ↦ hlog p) hP
  have hfactor :
      0 < exponentialChordFactor
        (x * ∑ p ∈ P, Real.log (p : ℝ)) :=
    exponentialChordFactor_pos (mul_pos hx hsum).le
  have hright :
      0 < synchronizedSquarefreePhysicalDensity nu P *
        ∏ p ∈ P,
          (gammaSewnMobiusValuationContractionMultiplier x p *
            exponentialChordFactor (x * Real.log (p : ℝ))) := by
    apply mul_pos (synchronizedSquarefreePhysicalDensity_pos nu hnu P)
    apply Finset.prod_pos
    intro p hp
    exact mul_pos
      (gammaSewnMobiusValuationContractionMultiplier_pos x p)
      (exponentialChordFactor_pos (mul_pos hx (hlog p)).le)
  have hmul :
      0 < gammaSewnSynchronizedRecoveredDensity nu x P *
        exponentialChordFactor
          (x * ∑ p ∈ P, Real.log (p : ℝ)) := by
    rw [gammaSewnSynchronized_recovered_chord_identity nu hx hP]
    exact hright
  exact pos_of_mul_pos_left hmul hfactor.le

theorem gammaSewnSynchronizedRecoveryRatio_pos_le_one
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    {x : ℝ} (hx : 0 < x)
    (P : Finset Nat.Primes) :
    0 < gammaSewnSynchronizedRecoveryRatio nu x P ∧
      gammaSewnSynchronizedRecoveryRatio nu x P ≤ 1 := by
  have hphysical := synchronizedSquarefreePhysicalDensity_pos nu hnu P
  exact ⟨div_pos
      (gammaSewnSynchronizedRecoveredDensity_pos nu hnu hx P) hphysical,
    (div_le_one hphysical).mpr
      (gammaSewnSynchronizedRecoveredDensity_le_physical nu
        (fun p ↦ (hnu p).le) hx P)⟩

theorem gammaSewnSynchronizedRecoveryRatio_lt_one
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    {x : ℝ} (hx : 0 < x)
    {P : Finset Nat.Primes} (hP : P.Nonempty) :
    gammaSewnSynchronizedRecoveryRatio nu x P < 1 := by
  exact (div_lt_one (synchronizedSquarefreePhysicalDensity_pos nu hnu P)).mpr
    (gammaSewnSynchronizedRecoveredDensity_lt_physical nu hnu hx hP)

/-- Exact quotient formula: all dependence on the prescribed density cancels. -/
theorem gammaSewnSynchronizedRecoveryRatio_eq_chordQuotient
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    {x : ℝ} (hx : 0 < x)
    {P : Finset Nat.Primes} (hP : P.Nonempty) :
    gammaSewnSynchronizedRecoveryRatio nu x P =
      (∏ p ∈ P,
          (gammaSewnMobiusValuationContractionMultiplier x p *
            exponentialChordFactor (x * Real.log (p : ℝ)))) /
        exponentialChordFactor
          (x * ∑ p ∈ P, Real.log (p : ℝ)) := by
  have hphysical :=
    (synchronizedSquarefreePhysicalDensity_pos nu hnu P).ne'
  have hlog (p : Nat.Primes) : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hsum : 0 < ∑ p ∈ P, Real.log (p : ℝ) :=
    Finset.sum_pos (fun p hp ↦ hlog p) hP
  have hfactor :
      exponentialChordFactor
        (x * ∑ p ∈ P, Real.log (p : ℝ)) ≠ 0 :=
    (exponentialChordFactor_pos (mul_pos hx hsum).le).ne'
  unfold gammaSewnSynchronizedRecoveryRatio
  rw [div_eq_iff hphysical, div_mul_eq_mul_div,
    eq_div_iff hfactor]
  simpa [mul_assoc, mul_comm] using
    gammaSewnSynchronized_recovered_chord_identity nu hx hP

private theorem tendsto_finset_prod_one
    {α : Type*} [DecidableEq α] (P : Finset α)
    (f : α → ℝ → ℝ)
    (hf : ∀ p ∈ P, Tendsto (f p) (𝓝 (0 : ℝ)) (𝓝 1)) :
    Tendsto (fun x ↦ ∏ p ∈ P, f p x) (𝓝 (0 : ℝ)) (𝓝 1) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
      rw [show (fun x ↦ ∏ q ∈ insert p P, f q x) =
          fun x ↦ f p x * ∏ q ∈ P, f q x by
        funext x
        rw [Finset.prod_insert hp]]
      convert (hf p (Finset.mem_insert_self p P)).mul
        (ih (fun q hq ↦ hf q (Finset.mem_insert_of_mem hq))) using 1
      simp

private theorem continuousAt_gammaSewnQuadraticGain_zero
    (p : Nat.Primes) :
    ContinuousAt
      (fun x : ℝ => gammaSewnMobiusValuationQuadraticDefectGain x p) 0 := by
  let q : ℝ → ℝ := fun x => xiMobiusContinuousApertureDiskNode x p
  let c : ℝ → ℝ :=
    fun x => gammaSewnMobiusValuationContractionMultiplier x p
  change ContinuousAt (fun x : ℝ =>
    (7 * q x ^ 2 + 10 * q x + 7) /
      (8 * (1 + q x ^ 4) * (1 + c x) * (1 + c x ^ 2))) 0
  have hq : ContinuousAt q 0 := by
    dsimp only [q, xiMobiusContinuousApertureDiskNode]
    fun_prop
  have hc : ContinuousAt c 0 := by
    simpa only [c] using
      continuousAt_gammaSewnMobiusValuationContractionMultiplier_zero p
  apply ContinuousAt.div
  · fun_prop
  · fun_prop
  · simp [q, c, gammaSewnMobiusValuationContractionMultiplier_zero]

/-- Gamma sewing is first-jet flat: its strict contraction begins only at quadratic order. -/
theorem tendsto_gammaSewnMobiusValuationContraction_sub_one_div_zero
    (p : Nat.Primes) :
    Tendsto
      (fun x : ℝ =>
        (gammaSewnMobiusValuationContractionMultiplier x p - 1) / x)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  let q : ℝ → ℝ := fun x => xiMobiusContinuousApertureDiskNode x p
  let g : ℝ → ℝ :=
    fun x => gammaSewnMobiusValuationQuadraticDefectGain x p
  have hgap :
      Tendsto (fun x : ℝ => (1 - q x) / x)
        (𝓝[>] (0 : ℝ)) (𝓝 (Real.log (p : ℝ))) := by
    simpa only [q, mul_one, one_mul] using
      tendsto_one_sub_xiMobiusContinuousApertureDiskNode_mul_div_nhdsGT_zero
        1 p
  have hgain :
      Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (3 / 8 : ℝ)) := by
    have h : Tendsto g (𝓝 (0 : ℝ))
        (𝓝 (gammaSewnMobiusValuationQuadraticDefectGain 0 p)) :=
      (continuousAt_gammaSewnQuadraticGain_zero p).tendsto
    have h' := h.mono_left
      (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    simpa only [g, gammaSewnMobiusValuationQuadraticDefectGain_zero] using h'
  have hid :
      Tendsto (fun x : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hzero :
      Tendsto
        (fun x : ℝ => -x * (((1 - q x) / x) ^ 2 * g x))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa using hid.neg.mul ((hgap.pow 2).mul hgain)
  apply hzero.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  rw [show gammaSewnMobiusValuationContractionMultiplier x p - 1 =
      -(1 - gammaSewnMobiusValuationContractionMultiplier x p) by ring]
  rw [one_sub_gammaSewnMobiusValuationContractionMultiplier_eq_sq_mul_gain]
  dsimp only [q, g]
  field_simp [hx.ne']

/-- The local sewn chord has the same first jet as its prime logarithmic chord; sewing contributes
no linear term. -/
theorem tendsto_gammaSewn_localChord_sub_one_div_zero
    (p : Nat.Primes) :
    Tendsto
      (fun x : ℝ =>
        (gammaSewnMobiusValuationContractionMultiplier x p *
            exponentialChordFactor (x * Real.log (p : ℝ)) - 1) / x)
      (𝓝[>] (0 : ℝ)) (𝓝 (-Real.log (p : ℝ) / 2)) := by
  have hc :
      Tendsto
        (fun x : ℝ => gammaSewnMobiusValuationContractionMultiplier x p)
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have h :
        Tendsto
          (fun x : ℝ => gammaSewnMobiusValuationContractionMultiplier x p)
          (𝓝 (0 : ℝ))
          (𝓝 (gammaSewnMobiusValuationContractionMultiplier 0 p)) :=
      (continuousAt_gammaSewnMobiusValuationContractionMultiplier_zero p).tendsto
    have h' := h.mono_left
      (inf_le_left : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
    simpa [gammaSewnMobiusValuationContractionMultiplier_zero] using h'
  have hfDeriv :
      HasDerivAt
        (fun x : ℝ =>
          exponentialChordFactor (x * Real.log (p : ℝ)))
        ((-1 / 2) * Real.log (p : ℝ)) 0 := by
    have hout :
        HasDerivAt exponentialChordFactor (-1 / 2)
          ((0 : ℝ) * Real.log (p : ℝ)) := by
      simpa using hasDerivAt_exponentialChordFactor_zero
    convert hout.comp 0
      ((hasDerivAt_id (0 : ℝ)).mul_const (Real.log (p : ℝ))) using 1
    all_goals simp
  have hf :
      Tendsto
        (fun x : ℝ =>
          (exponentialChordFactor (x * Real.log (p : ℝ)) - 1) / x)
        (𝓝[>] (0 : ℝ)) (𝓝 (-Real.log (p : ℝ) / 2)) := by
    simpa [exponentialChordFactor, div_eq_inv_mul, mul_comm, mul_left_comm,
      mul_assoc] using hfDeriv.tendsto_slope_zero_right
  have hcJet :=
    tendsto_gammaSewnMobiusValuationContraction_sub_one_div_zero p
  have hsum := hc.mul hf |>.add hcJet
  have heq :
      (fun x : ℝ =>
        gammaSewnMobiusValuationContractionMultiplier x p *
            ((exponentialChordFactor (x * Real.log (p : ℝ)) - 1) / x) +
          (gammaSewnMobiusValuationContractionMultiplier x p - 1) / x) =ᶠ[
        𝓝[>] (0 : ℝ)]
      (fun x : ℝ =>
        (gammaSewnMobiusValuationContractionMultiplier x p *
            exponentialChordFactor (x * Real.log (p : ℝ)) - 1) / x) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    field_simp [hx.ne']
    ring
  have hfinal := hsum.congr' heq
  convert hfinal using 1
  ring

private theorem tendsto_finset_prod_sub_one_div_zero
    {α : Type*} [DecidableEq α]
    (P : Finset α) (f : α → ℝ → ℝ) (a : α → ℝ)
    (hf0 : ∀ p ∈ P, Tendsto (f p) (𝓝 (0 : ℝ)) (𝓝 1))
    (hf1 : ∀ p ∈ P,
      Tendsto (fun x : ℝ => (f p x - 1) / x)
        (𝓝[>] (0 : ℝ)) (𝓝 (a p))) :
    Tendsto
      (fun x : ℝ => ((∏ p ∈ P, f p x) - 1) / x)
      (𝓝[>] (0 : ℝ)) (𝓝 (∑ p ∈ P, a p)) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
      have hp0 := hf0 p (Finset.mem_insert_self p P)
      have hp1 := hf1 p (Finset.mem_insert_self p P)
      have hP0 :
          Tendsto (fun x : ℝ => ∏ q ∈ P, f q x)
            (𝓝[>] (0 : ℝ)) (𝓝 1) :=
        (tendsto_finset_prod_one P f
          (fun q hq ↦ hf0 q (Finset.mem_insert_of_mem hq))).mono_left
            nhdsWithin_le_nhds
      have hP1 := ih
        (fun q hq ↦ hf0 q (Finset.mem_insert_of_mem hq))
        (fun q hq ↦ hf1 q (Finset.mem_insert_of_mem hq))
      have hlim := hp0.mono_left nhdsWithin_le_nhds |>.mul hP1 |>.add hp1
      rw [Finset.sum_insert hp]
      have heq :
          (fun x : ℝ =>
            f p x * (((∏ q ∈ P, f q x) - 1) / x) +
              (f p x - 1) / x) =ᶠ[𝓝[>] (0 : ℝ)]
            (fun x : ℝ => ((∏ q ∈ insert p P, f q x) - 1) / x) := by
        filter_upwards [self_mem_nhdsWithin] with x hx
        change 0 < x at hx
        rw [Finset.prod_insert hp]
        field_simp [hx.ne']
        ring
      have hfinal := hlim.congr' heq
      convert hfinal using 1
      ring

/-- The all-support recovery multiplier is cofinally lossless: every fixed finite support tends
to the signed physical boundary with multiplier one. -/
theorem tendsto_gammaSewnSynchronizedRecoveryRatio_zero
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) :
    Tendsto (fun x ↦ gammaSewnSynchronizedRecoveryRatio nu x P)
      (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  classical
  by_cases hP0 : P = ∅
  · subst P
    simp [gammaSewnSynchronizedRecoveryRatio,
      synchronizedSquarefreePhysicalDensity]
  have hP : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hP0
  have hlocal (p : Nat.Primes) :
      Tendsto
        (fun x ↦ gammaSewnMobiusValuationContractionMultiplier x p *
          exponentialChordFactor (x * Real.log (p : ℝ)))
        (𝓝 (0 : ℝ)) (𝓝 1) := by
    have hscale :
        ContinuousAt (fun x : ℝ => x * Real.log (p : ℝ)) 0 :=
      continuousAt_id.mul continuousAt_const
    have hchord :
        ContinuousAt
          (fun x : ℝ =>
            exponentialChordFactor (x * Real.log (p : ℝ))) 0 := by
      simpa [Function.comp_def] using
        continuousAt_exponentialChordFactor_zero.comp_of_eq hscale (by simp)
    simpa [gammaSewnMobiusValuationContractionMultiplier_zero,
      exponentialChordFactor] using
      (continuousAt_gammaSewnMobiusValuationContractionMultiplier_zero p).tendsto.mul
        hchord.tendsto
  have hnum :
      Tendsto
        (fun x ↦ ∏ p ∈ P,
          (gammaSewnMobiusValuationContractionMultiplier x p *
            exponentialChordFactor (x * Real.log (p : ℝ))))
        (𝓝 (0 : ℝ)) (𝓝 1) :=
    tendsto_finset_prod_one P
      (fun p x ↦ gammaSewnMobiusValuationContractionMultiplier x p *
        exponentialChordFactor (x * Real.log (p : ℝ)))
      (fun p hp ↦ hlocal p)
  have hden :
      Tendsto
        (fun x ↦ exponentialChordFactor
          (x * ∑ p ∈ P, Real.log (p : ℝ)))
        (𝓝 (0 : ℝ)) (𝓝 1) := by
    have hscale :
        ContinuousAt
          (fun x : ℝ => x * ∑ p ∈ P, Real.log (p : ℝ)) 0 :=
      continuousAt_id.mul continuousAt_const
    have hchord :
        ContinuousAt
          (fun x : ℝ => exponentialChordFactor
            (x * ∑ p ∈ P, Real.log (p : ℝ))) 0 := by
      simpa [Function.comp_def] using
        continuousAt_exponentialChordFactor_zero.comp_of_eq hscale (by simp)
    simpa [exponentialChordFactor] using hchord.tendsto
  have hquot :
      Tendsto
        (fun x ↦
          (∏ p ∈ P,
            (gammaSewnMobiusValuationContractionMultiplier x p *
              exponentialChordFactor (x * Real.log (p : ℝ)))) /
            exponentialChordFactor
              (x * ∑ p ∈ P, Real.log (p : ℝ)))
        (𝓝 (0 : ℝ)) (𝓝 1) := by
    convert hnum.div hden one_ne_zero using 1
    all_goals norm_num
  apply (hquot.mono_left nhdsWithin_le_nhds).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  exact (gammaSewnSynchronizedRecoveryRatio_eq_chordQuotient
    nu hnu hx hP).symm

/-- **First-jet invisibility of synchronized recovery.**  For every finite squarefree support,
the recovered/physical ratio has zero right derivative at the cofinal boundary.  Thus the
all-support contraction is nontrivial at every positive aperture but does not alter the boundary
Fisher tangent. -/
theorem tendsto_gammaSewnSynchronizedRecoveryRatio_sub_one_div_zero
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) :
    Tendsto
      (fun x : ℝ =>
        (gammaSewnSynchronizedRecoveryRatio nu x P - 1) / x)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  classical
  by_cases hP0 : P = ∅
  · subst P
    simp [gammaSewnSynchronizedRecoveryRatio,
      synchronizedSquarefreePhysicalDensity]
  have hP : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hP0
  let localChord : Nat.Primes → ℝ → ℝ := fun p x ↦
    gammaSewnMobiusValuationContractionMultiplier x p *
      exponentialChordFactor (x * Real.log (p : ℝ))
  let totalLog : ℝ := ∑ p ∈ P, Real.log (p : ℝ)
  have hlocal0 (p : Nat.Primes) :
      Tendsto (localChord p) (𝓝 (0 : ℝ)) (𝓝 1) := by
    have hscale :
        ContinuousAt (fun x : ℝ => x * Real.log (p : ℝ)) 0 :=
      continuousAt_id.mul continuousAt_const
    have hchord :
        ContinuousAt
          (fun x : ℝ =>
            exponentialChordFactor (x * Real.log (p : ℝ))) 0 := by
      simpa [Function.comp_def] using
        continuousAt_exponentialChordFactor_zero.comp_of_eq hscale (by simp)
    simpa [localChord, gammaSewnMobiusValuationContractionMultiplier_zero,
      exponentialChordFactor] using
      (continuousAt_gammaSewnMobiusValuationContractionMultiplier_zero p).tendsto.mul
        hchord.tendsto
  have hnumJet :
      Tendsto
        (fun x : ℝ => ((∏ p ∈ P, localChord p x) - 1) / x)
        (𝓝[>] (0 : ℝ))
        (𝓝 (-(totalLog) / 2)) := by
    have h := tendsto_finset_prod_sub_one_div_zero P localChord
      (fun p ↦ -Real.log (p : ℝ) / 2)
      (fun p hp ↦ hlocal0 p)
      (fun p hp ↦ by
        simpa only [localChord] using
          tendsto_gammaSewn_localChord_sub_one_div_zero p)
    have hsumJet :
        (∑ p ∈ P, -Real.log (p : ℝ) / 2) = -(totalLog) / 2 := by
      calc
        (∑ p ∈ P, -Real.log (p : ℝ) / 2) =
            ∑ p ∈ P, (-1 / 2) * Real.log (p : ℝ) := by
              apply Finset.sum_congr rfl
              intro p hp
              ring
        _ = (-1 / 2) * ∑ p ∈ P, Real.log (p : ℝ) := by
              rw [Finset.mul_sum]
        _ = -(totalLog) / 2 := by
              simp only [totalLog]
              ring
    simpa only [hsumJet] using h
  have hden0 :
      Tendsto
        (fun x : ℝ => exponentialChordFactor (x * totalLog))
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hscale : ContinuousAt (fun x : ℝ => x * totalLog) 0 :=
      continuousAt_id.mul continuousAt_const
    have hchord :
        ContinuousAt
          (fun x : ℝ => exponentialChordFactor (x * totalLog)) 0 := by
      simpa [Function.comp_def] using
        continuousAt_exponentialChordFactor_zero.comp_of_eq hscale (by simp)
    simpa [exponentialChordFactor] using
      hchord.tendsto.mono_left nhdsWithin_le_nhds
  have hdenJet :
      Tendsto
        (fun x : ℝ =>
          (exponentialChordFactor (x * totalLog) - 1) / x)
        (𝓝[>] (0 : ℝ)) (𝓝 (-(totalLog) / 2)) := by
    have hout :
        HasDerivAt exponentialChordFactor (-1 / 2)
          ((0 : ℝ) * totalLog) := by
      simpa using hasDerivAt_exponentialChordFactor_zero
    have hderiv :
        HasDerivAt
          (fun x : ℝ => exponentialChordFactor (x * totalLog))
          ((-1 / 2) * totalLog) 0 := by
      convert hout.comp 0
        ((hasDerivAt_id (0 : ℝ)).mul_const totalLog) using 1
      all_goals simp
    simpa [exponentialChordFactor, div_eq_inv_mul, mul_comm, mul_left_comm,
      mul_assoc] using hderiv.tendsto_slope_zero_right
  have hdiff :
      Tendsto
        (fun x : ℝ =>
          ((∏ p ∈ P, localChord p x) - 1) / x -
            (exponentialChordFactor (x * totalLog) - 1) / x)
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert hnumJet.sub hdenJet using 1
    ring
  have hquot :
      Tendsto
        (fun x : ℝ =>
          (((∏ p ∈ P, localChord p x) - 1) / x -
              (exponentialChordFactor (x * totalLog) - 1) / x) /
            exponentialChordFactor (x * totalLog))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert hdiff.div hden0 one_ne_zero using 1
    norm_num
  apply hquot.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  have hlog (p : Nat.Primes) : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hsum : 0 < totalLog := by
    dsimp only [totalLog]
    exact Finset.sum_pos (fun p hp ↦ hlog p) hP
  have hden :
      exponentialChordFactor (x * totalLog) ≠ 0 :=
    (exponentialChordFactor_pos (mul_pos hx hsum).le).ne'
  rw [gammaSewnSynchronizedRecoveryRatio_eq_chordQuotient
    nu hnu hx hP]
  change
    (((∏ p ∈ P, localChord p x) - 1) / x -
          (exponentialChordFactor (x * totalLog) - 1) / x) /
        exponentialChordFactor (x * totalLog) =
      (((∏ p ∈ P, localChord p x) /
          exponentialChordFactor (x * totalLog)) - 1) / x
  field_simp [hden]
  ring

/-! ## Infinite signed source transport -/

/-- Complex `ell²` space on the full Boolean cube of finite prime supports. -/
abbrev GammaSewnPrimeSupportL2 :=
  lp (fun _ : Finset Nat.Primes => ℂ) 2

/-- Generic coordinate multiplier on `ell²`, bundled from a pointwise unit-ball certificate. -/
noncomputable def lpCoordinatewiseContraction
    {ι : Type*} (m : ι → ℂ) (hm : ∀ i, ‖m i‖ ≤ 1) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 := by
  let L : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2 :=
    { toFun := fun x =>
        ⟨fun i => m i * x i,
          (lp.memℓp x).mono' (fun i => by
            rw [norm_mul]
            simpa using mul_le_of_le_one_left (norm_nonneg (x i)) (hm i))⟩
      map_add' := by
        intro x y
        apply lp.ext
        funext i
        simp only [lp.coeFn_add, Pi.add_apply]
        ring
      map_smul' := by
        intro c x
        apply lp.ext
        funext i
        change m i * (c * x i) = c * (m i * x i)
        ring }
  exact L.mkContinuous 1 (fun x => by
    simpa using lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) (fun i => by
      change ‖m i * x i‖ ≤ ‖x i‖
      rw [norm_mul]
      simpa using mul_le_of_le_one_left (norm_nonneg (x i)) (hm i)))

@[simp] theorem lpCoordinatewiseContraction_apply
    {ι : Type*} (m : ι → ℂ) (hm : ∀ i, ‖m i‖ ≤ 1)
    (x : lp (fun _ : ι => ℂ) 2) (i : ι) :
    lpCoordinatewiseContraction m hm x i = m i * x i :=
  rfl

theorem norm_lpCoordinatewiseContraction_apply_le
    {ι : Type*} (m : ι → ℂ) (hm : ∀ i, ‖m i‖ ≤ 1)
    (x : lp (fun _ : ι => ℂ) 2) :
    ‖lpCoordinatewiseContraction m hm x‖ ≤ ‖x‖ := by
  exact lp.norm_mono (by norm_num : (2 : ENNReal) ≠ 0) (fun i => by
    change ‖m i * x i‖ ≤ ‖x i‖
    rw [norm_mul]
    simpa using mul_le_of_le_one_left (norm_nonneg (x i)) (hm i))

/-- Möbius parity times the square root of synchronized recovered/physical density.  Its squared
modulus is exactly the recovery ratio, so this is the amplitude-level signed source transport. -/
def gammaSewnSynchronizedSignedRecoveryAmplitude
    (nu : Nat.Primes → ℝ) (x : ℝ) (P : Finset Nat.Primes) : ℂ :=
  (((-1 : ℝ) ^ P.card *
    Real.sqrt (gammaSewnSynchronizedRecoveryRatio nu x P) : ℝ) : ℂ)

theorem norm_gammaSewnSynchronizedSignedRecoveryAmplitude_le_one
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    {x : ℝ} (hx : 0 < x)
    (P : Finset Nat.Primes) :
    ‖gammaSewnSynchronizedSignedRecoveryAmplitude nu x P‖ ≤ 1 := by
  have hratio :=
    gammaSewnSynchronizedRecoveryRatio_pos_le_one nu hnu hx P
  rw [gammaSewnSynchronizedSignedRecoveryAmplitude, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact Real.sqrt_le_one.mpr hratio.2

theorem normSq_gammaSewnSynchronizedSignedRecoveryAmplitude
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    {x : ℝ} (hx : 0 < x)
    (P : Finset Nat.Primes) :
    Complex.normSq
        (gammaSewnSynchronizedSignedRecoveryAmplitude nu x P) =
      gammaSewnSynchronizedRecoveryRatio nu x P := by
  have hratio :=
    gammaSewnSynchronizedRecoveryRatio_pos_le_one nu hnu hx P
  rw [gammaSewnSynchronizedSignedRecoveryAmplitude, Complex.normSq_ofReal,
    show
      (-1 : ℝ) ^ P.card *
            Real.sqrt (gammaSewnSynchronizedRecoveryRatio nu x P) *
          ((-1 : ℝ) ^ P.card *
            Real.sqrt (gammaSewnSynchronizedRecoveryRatio nu x P)) =
        (((-1 : ℝ) ^ P.card) ^ 2) *
          (Real.sqrt (gammaSewnSynchronizedRecoveryRatio nu x P) ^ 2) by ring,
    Real.sq_sqrt hratio.1.le]
  rw [← pow_mul]
  norm_num

/-- The fixed all-support signed recovery transport on the infinite prime-support Hilbert space. -/
noncomputable def gammaSewnSynchronizedSignedRecoveryTransport
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (x : ℝ) (hx : 0 < x) :
    GammaSewnPrimeSupportL2 →L[ℂ] GammaSewnPrimeSupportL2 :=
  lpCoordinatewiseContraction
    (gammaSewnSynchronizedSignedRecoveryAmplitude nu x)
    (norm_gammaSewnSynchronizedSignedRecoveryAmplitude_le_one nu hnu hx)

@[simp] theorem gammaSewnSynchronizedSignedRecoveryTransport_apply
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (x : ℝ) (hx : 0 < x)
    (v : GammaSewnPrimeSupportL2) (P : Finset Nat.Primes) :
    gammaSewnSynchronizedSignedRecoveryTransport nu hnu x hx v P =
      gammaSewnSynchronizedSignedRecoveryAmplitude nu x P * v P :=
  rfl

/-- **Infinite signed source nonexpansiveness.**  Synchronized Gamma recovery followed by Möbius
parity cannot increase the norm of any vector on the full finite-support cube. -/
theorem norm_gammaSewnSynchronizedSignedRecoveryTransport_apply_le
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (x : ℝ) (hx : 0 < x)
    (v : GammaSewnPrimeSupportL2) :
    ‖gammaSewnSynchronizedSignedRecoveryTransport nu hnu x hx v‖ ≤ ‖v‖ :=
  norm_lpCoordinatewiseContraction_apply_le _ _ v

/-- Every non-vacuum coordinate is strictly damped at finite aperture. -/
theorem norm_gammaSewnSynchronizedSignedRecoveryAmplitude_lt_one
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    {x : ℝ} (hx : 0 < x)
    {P : Finset Nat.Primes} (hP : P.Nonempty) :
    ‖gammaSewnSynchronizedSignedRecoveryAmplitude nu x P‖ < 1 := by
  have hratio0 :=
    (gammaSewnSynchronizedRecoveryRatio_pos_le_one nu hnu hx P).1
  have hratio1 :=
    gammaSewnSynchronizedRecoveryRatio_lt_one nu hnu hx hP
  rw [gammaSewnSynchronizedSignedRecoveryAmplitude, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  exact (Real.sqrt_lt' one_pos).mpr (by simpa using hratio1)

/-- Cofinal amplitude limit: the signed transport converges coordinatewise to pure Möbius parity. -/
theorem tendsto_gammaSewnSynchronizedSignedRecoveryAmplitude_zero
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) :
    Tendsto
      (fun x ↦ gammaSewnSynchronizedSignedRecoveryAmplitude nu x P)
      (𝓝[>] (0 : ℝ)) (𝓝 ((((-1 : ℝ) ^ P.card : ℝ) : ℂ))) := by
  have hsqrt :
      Tendsto
        (fun x ↦ Real.sqrt
          (gammaSewnSynchronizedRecoveryRatio nu x P))
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using
      (Real.continuous_sqrt.continuousAt.tendsto.comp
        (tendsto_gammaSewnSynchronizedRecoveryRatio_zero nu hnu P))
  have hconst :
      Tendsto (fun _ : ℝ => (-1 : ℝ) ^ P.card)
        (𝓝[>] (0 : ℝ)) (𝓝 ((-1 : ℝ) ^ P.card)) :=
    tendsto_const_nhds
  simpa [gammaSewnSynchronizedSignedRecoveryAmplitude] using
    (hconst.mul hsqrt).ofReal

/-- Square-root recovery is first-jet flat as well. -/
theorem tendsto_sqrt_gammaSewnSynchronizedRecoveryRatio_sub_one_div_zero
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) :
    Tendsto
      (fun x : ℝ =>
        (Real.sqrt (gammaSewnSynchronizedRecoveryRatio nu x P) - 1) / x)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hratio :=
    tendsto_gammaSewnSynchronizedRecoveryRatio_zero nu hnu P
  have hsqrt :
      Tendsto
        (fun x : ℝ =>
          Real.sqrt (gammaSewnSynchronizedRecoveryRatio nu x P))
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa using Real.continuous_sqrt.continuousAt.tendsto.comp hratio
  have hden :
      Tendsto
        (fun x : ℝ =>
          Real.sqrt (gammaSewnSynchronizedRecoveryRatio nu x P) + 1)
        (𝓝[>] (0 : ℝ)) (𝓝 2) := by
    convert hsqrt.add tendsto_const_nhds using 1
    norm_num
  have hquot :
      Tendsto
        (fun x : ℝ =>
          ((gammaSewnSynchronizedRecoveryRatio nu x P - 1) / x) /
            (Real.sqrt (gammaSewnSynchronizedRecoveryRatio nu x P) + 1))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert
      (tendsto_gammaSewnSynchronizedRecoveryRatio_sub_one_div_zero
        nu hnu P).div hden (by norm_num : (2 : ℝ) ≠ 0) using 1
    norm_num
  apply hquot.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  have hratioPos :=
    (gammaSewnSynchronizedRecoveryRatio_pos_le_one nu hnu hx P).1
  have hsqrtNonneg :
      0 ≤ Real.sqrt (gammaSewnSynchronizedRecoveryRatio nu x P) :=
    Real.sqrt_nonneg _
  have hsqrtSq :
      Real.sqrt (gammaSewnSynchronizedRecoveryRatio nu x P) ^ 2 =
        gammaSewnSynchronizedRecoveryRatio nu x P :=
    Real.sq_sqrt hratioPos.le
  field_simp [hx.ne', (by positivity :
    Real.sqrt (gammaSewnSynchronizedRecoveryRatio nu x P) + 1 ≠ 0)]
  nlinarith

/-- **Signed first-jet preservation.**  Möbius sign is recovered with no linear amplitude error:
the cofinal signed multiplier has the same first jet as the constant parity character. -/
theorem tendsto_gammaSewnSynchronizedSignedRecoveryAmplitude_sub_parity_div_zero
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) :
    Tendsto
      (fun x : ℝ =>
        (gammaSewnSynchronizedSignedRecoveryAmplitude nu x P -
            ((((-1 : ℝ) ^ P.card : ℝ) : ℂ)) : ℂ) / (x : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hreal :
      Tendsto
        (fun x : ℝ =>
          ((-1 : ℝ) ^ P.card) *
            ((Real.sqrt
                (gammaSewnSynchronizedRecoveryRatio nu x P) - 1) / x))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    convert
      (tendsto_const_nhds.mul
        (tendsto_sqrt_gammaSewnSynchronizedRecoveryRatio_sub_one_div_zero
          nu hnu P)) using 1
    norm_num
  have hcomplex := hreal.ofReal
  apply hcomplex.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  simp only [gammaSewnSynchronizedSignedRecoveryAmplitude,
    Complex.ofReal_mul, Complex.ofReal_div]
  field_simp [hx.ne']
  push_cast
  ring

/-- **Recovery–Ward first-jet connector.**  On every squarefree coordinate, synchronized signed
recovery preserves an arbitrary continued complex boundary tangent, changing only its Möbius
parity.  This is the exact algebraic compatibility needed before a non-diagonal Julia weld: finite
aperture damping does not renormalize the Ward column at first order. -/
theorem gammaSewnSynchronizedSignedRecovery_preserves_complex_boundary_tangent
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes)
    (v : ℝ → ℂ) (v0 tangent : ℂ)
    (hvJet :
      Tendsto (fun x : ℝ => (v x - v0) / (x : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 tangent)) :
    Tendsto
      (fun x : ℝ =>
        (gammaSewnSynchronizedSignedRecoveryAmplitude nu x P * v x -
            ((((-1 : ℝ) ^ P.card : ℝ) : ℂ)) * v0) / (x : ℂ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((((-1 : ℝ) ^ P.card : ℝ) : ℂ)) * tangent)) := by
  let parity : ℂ := (((-1 : ℝ) ^ P.card : ℝ) : ℂ)
  have hamp0 :
      Tendsto
        (fun x : ℝ =>
          gammaSewnSynchronizedSignedRecoveryAmplitude nu x P)
        (𝓝[>] (0 : ℝ)) (𝓝 parity) := by
    simpa only [parity] using
      tendsto_gammaSewnSynchronizedSignedRecoveryAmplitude_zero nu hnu P
  have hampJet :
      Tendsto
        (fun x : ℝ =>
          (gammaSewnSynchronizedSignedRecoveryAmplitude nu x P - parity) /
            (x : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [parity] using
      tendsto_gammaSewnSynchronizedSignedRecoveryAmplitude_sub_parity_div_zero
        nu hnu P
  have hsum :=
    (hamp0.mul hvJet).add (hampJet.mul (tendsto_const_nhds : Tendsto
      (fun _ : ℝ => v0) (𝓝[>] (0 : ℝ)) (𝓝 v0)))
  have hsum' :
      Tendsto
        (fun x : ℝ =>
          gammaSewnSynchronizedSignedRecoveryAmplitude nu x P *
              ((v x - v0) / (x : ℂ)) +
            ((gammaSewnSynchronizedSignedRecoveryAmplitude nu x P - parity) /
              (x : ℂ)) * v0)
        (𝓝[>] (0 : ℝ)) (𝓝 (parity * tangent)) := by
    convert hsum using 1
    norm_num
  apply hsum'.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  dsimp only [parity]
  field_simp [hx.ne']
  ring

/-- A complex derivative restricts to the positive real aperture ray with the same quotient
tangent. -/
theorem hasDerivAt_tendsto_real_slope_zero_right
    {f : ℂ → ℂ} {f' : ℂ} (h : HasDerivAt f f' 0) :
    Tendsto
      (fun x : ℝ => (f (x : ℂ) - f 0) / (x : ℂ))
      (𝓝[>] (0 : ℝ)) (𝓝 f') := by
  have hofReal :
      Tendsto (fun x : ℝ => (x : ℂ))
        (𝓝[>] (0 : ℝ)) (nhdsWithin 0 ({0}ᶜ : Set ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact Complex.continuous_ofReal.continuousAt.tendsto.mono_left
        nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      change 0 < x at hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff,
        Complex.ofReal_eq_zero]
      exact hx.ne'
  have hslope := h.tendsto_slope_zero.comp hofReal
  simpa [Function.comp_def, div_eq_inv_mul, mul_comm] using hslope

@[simp] theorem xiWardAnchoredSourceTransportV_zero_value
    {z : ℂ} (hz : XiC z ≠ 0) :
    xiWardAnchoredSourceTransportV z 0 = 0 := by
  simp [xiWardAnchoredSourceTransportV, xiWardJuliaCrossDefect,
    xiWardSourcePhaseCrossRatio_zero, hz, XiC_zero_ne]

/-- **Recovered non-diagonal Xi Ward tangent.**  Synchronized signed source recovery can be
inserted before the actual common-anchor Julia transport without changing its continued Xi Ward
column at first order, except for the required squarefree Möbius parity. -/
theorem gammaSewnSynchronizedSignedRecovery_preserves_xiWardAnchoredSourceTangent
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) {z : ℂ}
    (hz : XiC z ≠ 0) (hz0 : z ≠ 0) :
    Tendsto
      (fun x : ℝ =>
        (gammaSewnSynchronizedSignedRecoveryAmplitude nu x P *
            xiWardAnchoredSourceTransportV z (x : ℂ)) / (x : ℂ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((((-1 : ℝ) ^ P.card : ℝ) : ℂ)) * logDeriv XiC z)) := by
  have hsource :=
    hasDerivAt_xiWardAnchoredSourceTransportV_zero hz hz0
  have hsourceJet :
      Tendsto
        (fun x : ℝ =>
          (xiWardAnchoredSourceTransportV z (x : ℂ) - 0) / (x : ℂ))
        (𝓝[>] (0 : ℝ)) (𝓝 (logDeriv XiC z)) := by
    simpa [xiWardAnchoredSourceTransportV_zero_value hz] using
      hasDerivAt_tendsto_real_slope_zero_right hsource
  have h :=
    gammaSewnSynchronizedSignedRecovery_preserves_complex_boundary_tangent
      nu hnu P
      (fun x : ℝ => xiWardAnchoredSourceTransportV z (x : ℂ))
      0 (logDeriv XiC z) hsourceJet
  simpa using h

/-- Continued-source form of the recovered non-diagonal tangent law. -/
theorem gammaSewnSynchronizedSignedRecovery_preserves_continuedXiWardSourceTangent
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) {z : ℂ}
    (hzdom : CCMContinuedCauchyDomain z) (hz0 : z ≠ 0) :
    Tendsto
      (fun x : ℝ =>
        (gammaSewnSynchronizedSignedRecoveryAmplitude nu x P *
            xiWardAnchoredSourceTransportV z (x : ℂ)) / (x : ℂ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((((-1 : ℝ) ^ P.card : ℝ) : ℂ)) *
        continuedPrimeArchSourceRelativeTrace z)) := by
  rw [continuedPrimeArchSourceRelativeTrace_eq_logDeriv_XiC_of_domain hzdom]
  exact
    gammaSewnSynchronizedSignedRecovery_preserves_xiWardAnchoredSourceTangent
      nu hnu P
      (XiC_ne_zero_of_continuedPrimeArch_domain
        hzdom.1 hzdom.2.1 hzdom.2.2.1) hz0

/-- **Recovered fixed Ward-column tangent.**  The signed recovery factor can be inserted directly
into the non-diagonal anti-causal Julia transport.  Its boundary derivative remains the actual
fixed Ward response `r`, with squarefree parity and no renormalization. -/
theorem gammaSewnSynchronizedSignedRecovery_preserves_antiCausalWardTangent
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) {w : ℂ} (hw : 0 < w.re) :
    Tendsto
      (fun x : ℝ =>
        (gammaSewnSynchronizedSignedRecoveryAmplitude nu x P *
            mobiusGammaXiAntiCausalWardTransportV w (x : ℂ)) / (x : ℂ))
      (𝓝[>] (0 : ℝ))
      (𝓝 (((((-1 : ℝ) ^ P.card : ℝ) : ℂ)) *
        continuedXiAntiCausalWardResponse w)) := by
  have htransport :=
    hasDerivAt_mobiusGammaXiAntiCausalWardTransportV_zero hw
  have hzero :
      mobiusGammaXiAntiCausalWardTransportV w 0 = 0 := by
    have hproduct : xiRightCanonicalProduct (Complex.I * w) ≠ 0 := by
      simpa using
        xiRightCanonicalProduct_boundary_shift_ne_zero hw
          (show (0 : ℝ) ≤ 0 by norm_num)
    rw [mobiusGammaXiAntiCausalWardTransportV_eq_one_sub_phase hw]
    rw [xiRightWardBoundarySourcePhaseCrossRatio,
      xiRightWardSourcePhase_zero hproduct,
      xiAntiCausalWardBoundarySourcePhase_zero]
    norm_num
  have htransportJet :
      Tendsto
        (fun x : ℝ =>
          (mobiusGammaXiAntiCausalWardTransportV w (x : ℂ) - 0) / (x : ℂ))
        (𝓝[>] (0 : ℝ))
        (𝓝 (continuedXiAntiCausalWardResponse w)) := by
    simpa [hzero] using
      hasDerivAt_tendsto_real_slope_zero_right htransport
  have h :=
    gammaSewnSynchronizedSignedRecovery_preserves_complex_boundary_tangent
      nu hnu P
      (fun x : ℝ => mobiusGammaXiAntiCausalWardTransportV w (x : ℂ))
      0 (continuedXiAntiCausalWardResponse w) htransportJet
  simpa using h

/-- At every positive aperture the recovered anti-causal transport remains inside the same
four-unit source ball. -/
theorem norm_gammaSewnSynchronizedRecoveredAntiCausalWardTransport_le_two
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) {w : ℂ} (hw : 0 < w.re)
    {x : ℝ} (hx : 0 < x) :
    ‖gammaSewnSynchronizedSignedRecoveryAmplitude nu x P *
        mobiusGammaXiAntiCausalWardTransportV w (x : ℂ)‖ ≤ 2 := by
  rw [norm_mul]
  calc
    ‖gammaSewnSynchronizedSignedRecoveryAmplitude nu x P‖ *
          ‖mobiusGammaXiAntiCausalWardTransportV w (x : ℂ)‖ ≤
        1 * ‖mobiusGammaXiAntiCausalWardTransportV w (x : ℂ)‖ :=
      mul_le_mul_of_nonneg_right
        (norm_gammaSewnSynchronizedSignedRecoveryAmplitude_le_one
          nu hnu hx P) (norm_nonneg _)
    _ ≤ 2 :=
      by simpa using
        norm_mobiusGammaXiAntiCausalWardTransportV_le_two hw hx.le

/-- Normalized non-diagonal Ward multiplier after synchronized signed recovery. -/
def gammaSewnSynchronizedRecoveredXiWardNormalizedMultiplier {n : ℕ}
    (nu : Nat.Primes → ℝ) (x : ℝ) (P : Finset Nat.Primes)
    (w : Fin n → ℂ) : Fin n → ℂ :=
  fun i =>
    gammaSewnSynchronizedSignedRecoveryAmplitude nu x P *
      xiWardNormalizedTransportMultiplier w x i

/-- **Signed source-holonomy nonexpansiveness.**  Synchronized recovery preserves the full
finite-packet Hardy Pick positivity of the non-diagonal Xi Ward transport, on every squarefree
support and every positive aperture. -/
theorem gammaSewnSynchronizedRecoveredXiWardNormalized_nonexpansive
    {n : ℕ} (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) {w : Fin n → ℂ}
    (hw : ∀ i, 0 < (w i).re) {x : ℝ} (hx : 0 < x) :
    (rightHalfPlanePickDefect w
      (gammaSewnSynchronizedRecoveredXiWardNormalizedMultiplier
        nu x P w)).PosSemidef := by
  let c : ℂ :=
    gammaSewnSynchronizedSignedRecoveryAmplitude nu x P
  have hratio :=
    gammaSewnSynchronizedRecoveryRatio_pos_le_one nu hnu hx P
  have hnormSq :
      Complex.normSq c =
        gammaSewnSynchronizedRecoveryRatio nu x P := by
    simpa only [c] using
      normSq_gammaSewnSynchronizedSignedRecoveryAmplitude nu hnu hx P
  have hcoef : (0 : ℂ) ≤ (1 - Complex.normSq c : ℝ) := by
    rw [Complex.nonneg_iff]
    simp only [Complex.ofReal_re, Complex.ofReal_im, and_true]
    rw [hnormSq]
    exact sub_nonneg.mpr hratio.2
  have hconst :
      (rightHalfPlanePickDefect w (fun _ => c)).PosSemidef := by
    have heq :
        rightHalfPlanePickDefect w (fun _ => c) =
          ((1 - Complex.normSq c : ℝ) : ℂ) •
            rightHalfPlaneHardyCauchyGram w := by
      ext i j
      change
        (1 - c * star c) / (w i + star (w j)) =
          ((1 - Complex.normSq c : ℝ) : ℂ) *
            (1 / (w i + star (w j)))
      rw [show c * star c = (Complex.normSq c : ℂ) by
        exact Complex.mul_conj c]
      push_cast
      ring
    rw [heq]
    exact (rightHalfPlaneHardyCauchyGram_posSemidef hw).smul hcoef
  have hward :
      (rightHalfPlanePickDefect w
        (xiWardNormalizedTransportMultiplier w x)).PosSemidef := by
    rw [rightHalfPlanePickDefect_eq_cauchy_sub_congruence]
    exact xiWardNormalizedTransport_nonexpansive hw hx.le
  have hprod :=
    rightHalfPlanePickDefect_mul_posSemidef hconst hward
  simpa only [
    gammaSewnSynchronizedRecoveredXiWardNormalizedMultiplier,
    Pi.mul_apply, c] using hprod

end

end RHTower
