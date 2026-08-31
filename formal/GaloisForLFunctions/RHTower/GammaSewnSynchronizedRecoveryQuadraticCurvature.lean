import GaloisForLFunctions.RHTower.GammaSewnSynchronizedRecoveryContraction
import GaloisForLFunctions.RHTower.PrimeSquareDeformedReflectionType

/-!
# Synchronized Gamma recovery: exact quadratic curvature

The fixed-support recovery multiplier is first-jet flat, but not curvature-flat.  This file
computes its exact coefficient-faithful second boundary jet:

`(R_P(x) - 1) / x² → -((1/3) ∑_{p∈P} log(p)² + (1/24)(∑_{p∈P} log(p))²)`.

The cost is strictly positive on every nonempty support and diverges on cofinal prime supports.
A diagonal-selection theorem therefore exposes arbitrarily large *normalized* recovery loss while
the aperture still tends to zero.  It deliberately does not claim unnormalized damping or a
moving-support Ward landing: those require a uniform two-parameter remainder law.
-/

open scoped BigOperators ComplexOrder
open Filter Set Topology

namespace RHTower

noncomputable section

theorem tendsto_exponentialChordFactor_quadraticJet_zero :
    Tendsto
      (fun x : ℝ =>
        (exponentialChordFactor x - 1 + x / 2) / x ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (1 / 6 : ℝ)) := by
  have hbase :
      Tendsto (fun y : ℝ => (1 - Real.exp (-y)) / (6 * y))
        (𝓝[≠] 0) (𝓝 (1 / 6 : ℝ)) := by
    have hder : HasDerivAt (fun y : ℝ => 1 - Real.exp (-y)) 1 0 := by
      have hraw :=
        (hasDerivAt_const (x := (0 : ℝ)) (c := (1 : ℝ))).sub
          ((Real.hasDerivAt_exp (-0)).comp 0 (hasDerivAt_neg 0))
      have hraw' := hraw.congr_deriv (g' := (1 : ℝ)) (by norm_num)
      simpa only [Function.comp_apply] using! hraw'
    have h := hder.tendsto_slope_zero
    have h' : Tendsto (fun y : ℝ => (1 / 6 : ℝ) *
        ((1 - Real.exp (-y)) / y)) (𝓝[≠] 0) (𝓝 (1 / 6 : ℝ)) := by
      simpa [slope_def_field, div_eq_mul_inv, mul_comm] using
        h.const_mul (1 / 6 : ℝ)
    apply h'.congr'
    filter_upwards [self_mem_nhdsWithin] with y hy
    change y ≠ 0 at hy
    field_simp [hy]
  have hsecond :
      Tendsto
        (fun y : ℝ => (Real.exp (-y) - 1 + y) / (3 * y ^ 2))
        (𝓝[≠] 0) (𝓝 (1 / 6 : ℝ)) := by
    refine HasDerivAt.lhopital_zero_nhdsNE
      (f' := fun y : ℝ => 1 - Real.exp (-y))
      (g' := fun y : ℝ => 6 * y) ?_ ?_ ?_ ?_ ?_ hbase
    · exact Filter.Eventually.of_forall fun y => by
        have hraw :=
          (((Real.hasDerivAt_exp (-y)).comp y (hasDerivAt_neg y)).sub_const 1).add
            (hasDerivAt_id y)
        have hraw' := hraw.congr_deriv (g' := 1 - Real.exp (-y)) (by ring)
        simpa only [Function.comp_apply] using! hraw'
    · exact Filter.Eventually.of_forall fun y => by
        have hraw := (hasDerivAt_pow 2 y).const_mul 3
        have hraw' := hraw.congr_deriv (g' := 6 * y) (by ring)
        simpa using! hraw'
    · filter_upwards [self_mem_nhdsWithin] with y hy
      change y ≠ 0 at hy
      exact mul_ne_zero (by norm_num) hy
    · have hcont : ContinuousAt
          (fun y : ℝ => Real.exp (-y) - 1 + y) 0 := by fun_prop
      simpa using! hcont.tendsto.mono_left nhdsWithin_le_nhds
    · have hcont : ContinuousAt (fun y : ℝ => 3 * y ^ 2) 0 := by fun_prop
      simpa using! hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hthird :
      Tendsto
        (fun y : ℝ =>
          (1 - Real.exp (-y) - y + y ^ 2 / 2) / y ^ 3)
        (𝓝[≠] 0) (𝓝 (1 / 6 : ℝ)) := by
    refine HasDerivAt.lhopital_zero_nhdsNE
      (f' := fun y : ℝ => Real.exp (-y) - 1 + y)
      (g' := fun y : ℝ => 3 * y ^ 2) ?_ ?_ ?_ ?_ ?_ hsecond
    · exact Filter.Eventually.of_forall fun y => by
        have hraw :=
          ((((hasDerivAt_const (x := y) (c := (1 : ℝ))).sub
              ((Real.hasDerivAt_exp (-y)).comp y (hasDerivAt_neg y))).sub
            (hasDerivAt_id y)).add
            ((hasDerivAt_pow 2 y).div_const 2))
        have hraw' := hraw.congr_deriv
          (g' := Real.exp (-y) - 1 + y) (by ring)
        simpa only [Function.comp_apply, Pi.sub_apply] using! hraw'
    · exact Filter.Eventually.of_forall fun y => by
        have hraw := (hasDerivAt_pow 3 y)
        have hraw' := hraw.congr_deriv (g' := 3 * y ^ 2) (by ring)
        simpa using! hraw'
    · filter_upwards [self_mem_nhdsWithin] with y hy
      change y ≠ 0 at hy
      exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hy)
    · have hcont : ContinuousAt
          (fun y : ℝ => 1 - Real.exp (-y) - y + y ^ 2 / 2) 0 := by fun_prop
      simpa using! hcont.tendsto.mono_left nhdsWithin_le_nhds
    · have hcont : ContinuousAt (fun y : ℝ => y ^ 3) 0 := by fun_prop
      simpa using! hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hright : 𝓝[>] (0 : ℝ) ≤ 𝓝[≠] (0 : ℝ) :=
    nhdsWithin_mono 0 (by
      intro x hx
      simp only [mem_compl_iff, mem_singleton_iff]
      exact hx.ne')
  apply (hthird.mono_left hright).congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  rw [exponentialChordFactor, if_neg hx.ne']
  field_simp [hx.ne']

theorem tendsto_exponentialChordFactor_scaledQuadraticJet_zero
    (a : ℝ) (ha : 0 < a) :
    Tendsto
      (fun x : ℝ =>
        (exponentialChordFactor (x * a) - 1 + x * a / 2) / x ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (a ^ 2 / 6)) := by
  have hscale :
      Tendsto (fun x : ℝ => x * a) (𝓝[>] (0 : ℝ)) (𝓝[>] (0 : ℝ)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h := (tendsto_id.const_mul a).mono_left
          (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
      convert h using 1
      · funext x
        simp only [id_eq]
        ring
      · ring
    · filter_upwards [self_mem_nhdsWithin] with x hx
      exact mul_pos hx ha
  have h := tendsto_exponentialChordFactor_quadraticJet_zero.comp hscale
  have hmul := h.const_mul (a ^ 2)
  have hmul' :
      Tendsto
        (fun x : ℝ => a ^ 2 *
          (((fun y : ℝ =>
              (exponentialChordFactor y - 1 + y / 2) / y ^ 2) ∘
            fun y : ℝ => y * a) x))
        (𝓝[>] (0 : ℝ)) (𝓝 (a ^ 2 / 6)) := by
    convert hmul using 1
    ring
  apply hmul'.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  simp only [Function.comp_apply]
  field_simp [hx.ne', ha.ne']

theorem tendsto_gammaSewnMobiusValuationContraction_quadraticJet_zero
    (p : Nat.Primes) :
    Tendsto
      (fun x : ℝ =>
        (gammaSewnMobiusValuationContractionMultiplier x p - 1) / x ^ 2)
      (𝓝[>] (0 : ℝ))
      (𝓝 (-(3 / 8 : ℝ) * Real.log (p : ℝ) ^ 2)) := by
  let q : ℝ → ℝ := fun x => xiMobiusContinuousApertureDiskNode x p
  let g : ℝ → ℝ :=
    fun x => gammaSewnMobiusValuationQuadraticDefectGain x p
  have hgap :
      Tendsto (fun x : ℝ => (1 - q x) / x)
        (𝓝[>] (0 : ℝ)) (𝓝 (Real.log (p : ℝ))) := by
    simpa only [q, mul_one, one_mul] using
      tendsto_one_sub_xiMobiusContinuousApertureDiskNode_mul_div_nhdsGT_zero
        1 p
  have hgain : Tendsto g (𝓝[>] (0 : ℝ)) (𝓝 (3 / 8 : ℝ)) := by
    have h : Tendsto g (𝓝 (0 : ℝ))
        (𝓝 (gammaSewnMobiusValuationQuadraticDefectGain 0 p)) :=
      (continuousAt_gammaSewnMobiusValuationQuadraticDefectGain_zero p).tendsto
    simpa only [g, gammaSewnMobiusValuationQuadraticDefectGain_zero] using!
      h.mono_left nhdsWithin_le_nhds
  have hmain := (hgap.pow 2).mul hgain |>.neg
  have hmain' :
      Tendsto (fun x : ℝ => -(((1 - q x) / x) ^ 2 * g x))
        (𝓝[>] (0 : ℝ))
        (𝓝 (-(3 / 8 : ℝ) * Real.log (p : ℝ) ^ 2)) := by
    convert hmain using 1 <;> ring
  apply hmain'.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  rw [show gammaSewnMobiusValuationContractionMultiplier x p - 1 =
      -(1 - gammaSewnMobiusValuationContractionMultiplier x p) by ring]
  rw [one_sub_gammaSewnMobiusValuationContractionMultiplier_eq_sq_mul_gain]
  dsimp only [q, g]
  field_simp [hx.ne']

theorem tendsto_gammaSewnLocalChord_quadraticJet_zero (p : Nat.Primes) :
    Tendsto
      (fun x : ℝ =>
        (gammaSewnMobiusValuationContractionMultiplier x p *
              exponentialChordFactor (x * Real.log (p : ℝ)) - 1 +
            x * Real.log (p : ℝ) / 2) / x ^ 2)
      (𝓝[>] (0 : ℝ))
      (𝓝 (-(5 / 24 : ℝ) * Real.log (p : ℝ) ^ 2)) := by
  let l : ℝ := Real.log (p : ℝ)
  have hl : 0 < l := Real.log_pos (by exact_mod_cast p.2.one_lt)
  let c : ℝ → ℝ := fun x => gammaSewnMobiusValuationContractionMultiplier x p
  let f : ℝ → ℝ := fun x => exponentialChordFactor (x * l)
  have hc2 : Tendsto (fun x : ℝ => (c x - 1) / x ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (-(3 / 8 : ℝ) * l ^ 2)) := by
    simpa only [c, l] using
      tendsto_gammaSewnMobiusValuationContraction_quadraticJet_zero p
  have hf2 : Tendsto (fun x : ℝ => (f x - 1 + x * l / 2) / x ^ 2)
      (𝓝[>] (0 : ℝ)) (𝓝 (l ^ 2 / 6)) := by
    simpa only [f] using
      tendsto_exponentialChordFactor_scaledQuadraticJet_zero l hl
  have hc1 : Tendsto (fun x : ℝ => (c x - 1) / x)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [c] using
      tendsto_gammaSewnMobiusValuationContraction_sub_one_div_zero p
  have hf1 : Tendsto (fun x : ℝ => (f x - 1) / x)
      (𝓝[>] (0 : ℝ)) (𝓝 (-l / 2)) := by
    have hout : HasDerivAt exponentialChordFactor (-1 / 2)
        ((0 : ℝ) * l) := by simpa using hasDerivAt_exponentialChordFactor_zero
    have hderiv : HasDerivAt f ((-1 / 2) * l) 0 := by
      have hraw := hout.comp 0 ((hasDerivAt_id (0 : ℝ)).mul_const l)
      have hraw' := hraw.congr_deriv (g' := (-1 / 2) * l) (by ring)
      simpa only [f, Function.comp_apply] using! hraw'
    simpa [f, exponentialChordFactor, div_eq_inv_mul, mul_comm, mul_left_comm,
      mul_assoc] using hderiv.tendsto_slope_zero_right
  have hmain := hc2.add hf2 |>.add (hc1.mul hf1)
  have hmain' :
      Tendsto
        (fun x : ℝ => (c x - 1) / x ^ 2 +
          (f x - 1 + x * l / 2) / x ^ 2 +
          (c x - 1) / x * ((f x - 1) / x))
        (𝓝[>] (0 : ℝ)) (𝓝 (-(5 / 24 : ℝ) * l ^ 2)) := by
    convert hmain using 1 <;> ring
  have hfinal :
      Tendsto
        (fun x : ℝ =>
          (c x * f x - 1 + x * l / 2) / x ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (-(5 / 24 : ℝ) * l ^ 2)) := by
    apply hmain'.congr'
    filter_upwards [self_mem_nhdsWithin] with x hx
    change 0 < x at hx
    field_simp [hx.ne']
    ring
  simpa only [c, f, l] using hfinal

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

private theorem tendsto_finset_prod_firstJet
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
      have hlim' :
          Tendsto
            (fun x : ℝ =>
              f p x * (((∏ q ∈ P, f q x) - 1) / x) +
                (f p x - 1) / x)
            (𝓝[>] (0 : ℝ)) (𝓝 (a p + ∑ q ∈ P, a q)) := by
        convert hlim using 1 <;> ring
      apply hlim'.congr'
      filter_upwards [self_mem_nhdsWithin] with x hx
      change 0 < x at hx
      rw [Finset.prod_insert hp]
      field_simp [hx.ne']
      ring

private theorem tendsto_finset_prod_secondJet
    {α : Type*} [DecidableEq α]
    (P : Finset α) (f : α → ℝ → ℝ) (a b : α → ℝ)
    (hf0 : ∀ p ∈ P, Tendsto (f p) (𝓝 (0 : ℝ)) (𝓝 1))
    (hf1 : ∀ p ∈ P,
      Tendsto (fun x : ℝ => (f p x - 1) / x)
        (𝓝[>] (0 : ℝ)) (𝓝 (a p)))
    (hf2 : ∀ p ∈ P,
      Tendsto (fun x : ℝ => (f p x - 1 - x * a p) / x ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (b p))) :
    Tendsto
      (fun x : ℝ =>
        ((∏ p ∈ P, f p x) - 1 - x * ∑ p ∈ P, a p) / x ^ 2)
      (𝓝[>] (0 : ℝ))
      (𝓝 ((∑ p ∈ P, b p) +
        (((∑ p ∈ P, a p) ^ 2 - ∑ p ∈ P, (a p) ^ 2) / 2))) := by
  induction P using Finset.induction_on with
  | empty => simp
  | @insert p P hp ih =>
      have hp1 := hf1 p (Finset.mem_insert_self p P)
      have hp2 := hf2 p (Finset.mem_insert_self p P)
      have hP1 := tendsto_finset_prod_firstJet P f a
        (fun q hq ↦ hf0 q (Finset.mem_insert_of_mem hq))
        (fun q hq ↦ hf1 q (Finset.mem_insert_of_mem hq))
      have hP2 := ih
        (fun q hq ↦ hf0 q (Finset.mem_insert_of_mem hq))
        (fun q hq ↦ hf1 q (Finset.mem_insert_of_mem hq))
        (fun q hq ↦ hf2 q (Finset.mem_insert_of_mem hq))
      have hmain := hp2.add hP2 |>.add (hp1.mul hP1)
      have hmain' :
          Tendsto
            (fun x : ℝ =>
              (f p x - 1 - x * a p) / x ^ 2 +
              ((∏ q ∈ P, f q x) - 1 - x * ∑ q ∈ P, a q) / x ^ 2 +
              ((f p x - 1) / x) *
                (((∏ q ∈ P, f q x) - 1) / x))
            (𝓝[>] (0 : ℝ))
            (𝓝 ((∑ q ∈ insert p P, b q) +
              (((∑ q ∈ insert p P, a q) ^ 2 -
                ∑ q ∈ insert p P, (a q) ^ 2) / 2))) := by
        rw [Finset.sum_insert hp, Finset.sum_insert hp,
          Finset.sum_insert hp]
        convert hmain using 1 <;> ring
      apply hmain'.congr'
      filter_upwards [self_mem_nhdsWithin] with x hx
      change 0 < x at hx
      rw [Finset.prod_insert hp, Finset.sum_insert hp]
      field_simp [hx.ne']
      ring

/-- Exact boundary-curvature cost of synchronized Gamma recovery on a finite prime support. -/
def gammaSewnSynchronizedRecoveryQuadraticCost
    (P : Finset Nat.Primes) : ℝ :=
  (1 / 3 : ℝ) * ∑ p ∈ P, Real.log (p : ℝ) ^ 2 +
    (1 / 24 : ℝ) * (∑ p ∈ P, Real.log (p : ℝ)) ^ 2

theorem gammaSewnSynchronizedRecoveryQuadraticCost_nonneg
    (P : Finset Nat.Primes) :
    0 ≤ gammaSewnSynchronizedRecoveryQuadraticCost P := by
  unfold gammaSewnSynchronizedRecoveryQuadraticCost
  positivity

theorem gammaSewnSynchronizedRecoveryQuadraticCost_pos
    {P : Finset Nat.Primes} (hP : P.Nonempty) :
    0 < gammaSewnSynchronizedRecoveryQuadraticCost P := by
  have hlog (p : Nat.Primes) : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hsq : 0 < ∑ p ∈ P, Real.log (p : ℝ) ^ 2 :=
    Finset.sum_pos (fun p hp ↦ sq_pos_of_pos (hlog p)) hP
  have htotal : 0 ≤ (∑ p ∈ P, Real.log (p : ℝ)) ^ 2 := sq_nonneg _
  unfold gammaSewnSynchronizedRecoveryQuadraticCost
  nlinarith

theorem tendsto_gammaSewnSynchronizedRecoveryRatio_quadraticJet_zero
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p)
    (P : Finset Nat.Primes) :
    Tendsto
      (fun x : ℝ =>
        (gammaSewnSynchronizedRecoveryRatio nu x P - 1) / x ^ 2)
      (𝓝[>] (0 : ℝ))
      (𝓝 (-gammaSewnSynchronizedRecoveryQuadraticCost P)) := by
  classical
  by_cases hP0 : P = ∅
  · subst P
    simp [gammaSewnSynchronizedRecoveryRatio,
      synchronizedSquarefreePhysicalDensity,
      gammaSewnSynchronizedRecoveryQuadraticCost]
  have hP : P.Nonempty := Finset.nonempty_iff_ne_empty.mpr hP0
  let localChord : Nat.Primes → ℝ → ℝ := fun p x ↦
    gammaSewnMobiusValuationContractionMultiplier x p *
      exponentialChordFactor (x * Real.log (p : ℝ))
  let totalLog : ℝ := ∑ p ∈ P, Real.log (p : ℝ)
  let squareLog : ℝ := ∑ p ∈ P, Real.log (p : ℝ) ^ 2
  have hlog (p : Nat.Primes) : 0 < Real.log (p : ℝ) :=
    Real.log_pos (by exact_mod_cast p.2.one_lt)
  have htotal : 0 < totalLog := by
    dsimp only [totalLog]
    exact Finset.sum_pos (fun p hp ↦ hlog p) hP
  have hlocal0 (p : Nat.Primes) :
      Tendsto (localChord p) (𝓝 (0 : ℝ)) (𝓝 1) := by
    have hscale : ContinuousAt
        (fun x : ℝ => x * Real.log (p : ℝ)) 0 := by fun_prop
    have hchord : ContinuousAt
        (fun x : ℝ => exponentialChordFactor
          (x * Real.log (p : ℝ))) 0 := by
      simpa [Function.comp_def] using
        continuousAt_exponentialChordFactor_zero.comp_of_eq hscale (by simp)
    simpa [localChord, gammaSewnMobiusValuationContractionMultiplier_zero,
      exponentialChordFactor] using
      (continuousAt_gammaSewnMobiusValuationContractionMultiplier_zero p).tendsto.mul
        hchord.tendsto
  have hlocal1 (p : Nat.Primes) :
      Tendsto (fun x : ℝ => (localChord p x - 1) / x)
        (𝓝[>] (0 : ℝ)) (𝓝 (-Real.log (p : ℝ) / 2)) := by
    simpa only [localChord] using
      tendsto_gammaSewn_localChord_sub_one_div_zero p
  have hlocal2 (p : Nat.Primes) :
      Tendsto
        (fun x : ℝ =>
          (localChord p x - 1 - x * (-Real.log (p : ℝ) / 2)) / x ^ 2)
        (𝓝[>] (0 : ℝ))
        (𝓝 (-(5 / 24 : ℝ) * Real.log (p : ℝ) ^ 2)) := by
    convert tendsto_gammaSewnLocalChord_quadraticJet_zero p using 1
    funext x
    ring
  have hnumRaw := tendsto_finset_prod_secondJet P localChord
    (fun p ↦ -Real.log (p : ℝ) / 2)
    (fun p ↦ -(5 / 24 : ℝ) * Real.log (p : ℝ) ^ 2)
    (fun p hp ↦ hlocal0 p)
    (fun p hp ↦ hlocal1 p)
    (fun p hp ↦ hlocal2 p)
  have hsumA :
      (∑ p ∈ P, -Real.log (p : ℝ) / 2) = -totalLog / 2 := by
    calc
      (∑ p ∈ P, -Real.log (p : ℝ) / 2) =
          ∑ p ∈ P, (-1 / 2 : ℝ) * Real.log (p : ℝ) := by
            apply Finset.sum_congr rfl
            intro p hp
            ring
      _ = (-1 / 2 : ℝ) * ∑ p ∈ P, Real.log (p : ℝ) :=
        by rw [Finset.mul_sum]
      _ = -totalLog / 2 := by
        dsimp only [totalLog]
        ring
  have hsumASq :
      (∑ p ∈ P, (-Real.log (p : ℝ) / 2) ^ 2) = squareLog / 4 := by
    calc
      (∑ p ∈ P, (-Real.log (p : ℝ) / 2) ^ 2) =
          ∑ p ∈ P, (1 / 4 : ℝ) * Real.log (p : ℝ) ^ 2 := by
            apply Finset.sum_congr rfl
            intro p hp
            ring
      _ = (1 / 4 : ℝ) * ∑ p ∈ P, Real.log (p : ℝ) ^ 2 :=
        by rw [Finset.mul_sum]
      _ = squareLog / 4 := by
        dsimp only [squareLog]
        ring
  have hsumB :
      (∑ p ∈ P, -(5 / 24 : ℝ) * Real.log (p : ℝ) ^ 2) =
        -(5 / 24 : ℝ) * squareLog := by
    dsimp only [squareLog]
    rw [Finset.mul_sum]
  have hnum :
      Tendsto
        (fun x : ℝ =>
          ((∏ p ∈ P, localChord p x) - 1 + x * totalLog / 2) / x ^ 2)
        (𝓝[>] (0 : ℝ))
        (𝓝 (totalLog ^ 2 / 8 - squareLog / 3)) := by
    rw [hsumA, hsumASq, hsumB] at hnumRaw
    convert hnumRaw using 1
    · funext x
      ring
    · ring
  have hden0 :
      Tendsto (fun x : ℝ => exponentialChordFactor (x * totalLog))
        (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hscale : ContinuousAt (fun x : ℝ => x * totalLog) 0 := by fun_prop
    have hchord : ContinuousAt
        (fun x : ℝ => exponentialChordFactor (x * totalLog)) 0 := by
      simpa [Function.comp_def] using
        continuousAt_exponentialChordFactor_zero.comp_of_eq hscale (by simp)
    simpa [exponentialChordFactor] using
      hchord.tendsto.mono_left nhdsWithin_le_nhds
  have hden2 :
      Tendsto
        (fun x : ℝ =>
          (exponentialChordFactor (x * totalLog) - 1 +
            x * totalLog / 2) / x ^ 2)
        (𝓝[>] (0 : ℝ)) (𝓝 (totalLog ^ 2 / 6)) :=
    tendsto_exponentialChordFactor_scaledQuadraticJet_zero totalLog htotal
  have hdiff := hnum.sub hden2
  have hquot := hdiff.div hden0 one_ne_zero
  have hquotPoint :
      Tendsto
        (fun x : ℝ =>
          ((((∏ p ∈ P, localChord p x) - 1 + x * totalLog / 2) / x ^ 2 -
              (exponentialChordFactor (x * totalLog) - 1 +
                x * totalLog / 2) / x ^ 2) /
            exponentialChordFactor (x * totalLog)))
        (𝓝[>] (0 : ℝ))
        (𝓝 ((totalLog ^ 2 / 8 - squareLog / 3 - totalLog ^ 2 / 6) / 1)) := by
    change Tendsto
      (fun x : ℝ =>
        (((∏ p ∈ P, localChord p x) - 1 + x * totalLog / 2) / x ^ 2 -
            (exponentialChordFactor (x * totalLog) - 1 +
              x * totalLog / 2) / x ^ 2) /
          exponentialChordFactor (x * totalLog))
      (𝓝[>] (0 : ℝ))
      (𝓝 ((totalLog ^ 2 / 8 - squareLog / 3 - totalLog ^ 2 / 6) / 1)) at hquot
    exact hquot
  have hquot' :
      Tendsto
        (fun x : ℝ =>
          ((((∏ p ∈ P, localChord p x) - 1 + x * totalLog / 2) / x ^ 2 -
              (exponentialChordFactor (x * totalLog) - 1 +
                x * totalLog / 2) / x ^ 2) /
            exponentialChordFactor (x * totalLog)))
        (𝓝[>] (0 : ℝ))
        (𝓝 (-gammaSewnSynchronizedRecoveryQuadraticCost P)) := by
    have hcost :
        gammaSewnSynchronizedRecoveryQuadraticCost P =
          squareLog / 3 + totalLog ^ 2 / 24 := by
      simp only [gammaSewnSynchronizedRecoveryQuadraticCost,
        squareLog, totalLog]
      ring
    rw [hcost]
    convert hquotPoint using 1
    ring
  apply hquot'.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  change 0 < x at hx
  have hden : exponentialChordFactor (x * totalLog) ≠ 0 :=
    (exponentialChordFactor_pos (mul_pos hx htotal).le).ne'
  rw [gammaSewnSynchronizedRecoveryRatio_eq_chordQuotient
    nu hnu hx hP]
  dsimp only [localChord, totalLog] at hden ⊢
  field_simp [hden, hx.ne']
  ring

theorem tendsto_gammaSewnSynchronizedRecoveryQuadraticCost_primesBelow_atTop :
    Tendsto
      (fun N : ℕ =>
        gammaSewnSynchronizedRecoveryQuadraticCost
          (GaloisForLFunctions.primesBelowSubtype N))
      atTop atTop := by
  have hsumEq (N : ℕ) :
      (∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
          Real.log (p : ℝ)) =
        ∑ p ∈ Nat.primesBelow N, Real.log (p : ℝ) := by
    unfold GaloisForLFunctions.primesBelowSubtype
    rw [Finset.sum_map]
    simpa using
      (Finset.sum_attach (Nat.primesBelow N)
        (fun p : ℕ => Real.log (p : ℝ)))
  rw [tendsto_atTop]
  intro B
  have hmass := (tendsto_atTop.1 tendsto_sum_primesBelow_log_atTop)
    (max 1 (24 * B))
  filter_upwards [hmass] with N hN
  let L : ℝ := ∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
    Real.log (p : ℝ)
  let S : ℝ := ∑ p ∈ GaloisForLFunctions.primesBelowSubtype N,
    Real.log (p : ℝ) ^ 2
  have hN' : max 1 (24 * B) ≤ L := by
    dsimp only [L]
    rw [hsumEq N]
    exact hN
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hN'
  have hLB : 24 * B ≤ L := le_trans (le_max_right _ _) hN'
  have hS : 0 ≤ S := by
    dsimp only [S]
    positivity
  change B ≤ (1 / 3 : ℝ) * S + (1 / 24 : ℝ) * L ^ 2
  nlinarith [sq_nonneg (L - 1)]

/-- A diagonal aperture can expose the diverging all-prime quadratic recovery curvature while
still tending to the physical boundary. -/
theorem exists_gammaSewnSynchronizedRecovery_cofinal_quadraticLoss_schedule
    (nu : Nat.Primes → ℝ) (hnu : ∀ p, 0 < nu p) :
    ∃ aperture : ℕ → ℝ,
      (∀ N, 0 < aperture N) ∧
      (∀ N, aperture N < 1 / ((N : ℝ) + 1)) ∧
      Tendsto aperture atTop (𝓝 0) ∧
      Tendsto
        (fun N : ℕ =>
          (1 - gammaSewnSynchronizedRecoveryRatio nu (aperture N)
              (GaloisForLFunctions.primesBelowSubtype N)) /
            (aperture N) ^ 2)
        atTop atTop := by
  have hlimit (N : ℕ) :
      Tendsto
        (fun x : ℝ =>
          (1 - gammaSewnSynchronizedRecoveryRatio nu x
              (GaloisForLFunctions.primesBelowSubtype N)) / x ^ 2)
        (𝓝[>] (0 : ℝ))
        (𝓝 (gammaSewnSynchronizedRecoveryQuadraticCost
          (GaloisForLFunctions.primesBelowSubtype N))) := by
    have h := (tendsto_gammaSewnSynchronizedRecoveryRatio_quadraticJet_zero nu hnu
      (GaloisForLFunctions.primesBelowSubtype N)).neg
    convert h using 1
    · funext x
      ring
    · ring
  have hexists (N : ℕ) :
      ∃ x : ℝ,
        0 < x ∧ x < 1 / ((N : ℝ) + 1) ∧
          gammaSewnSynchronizedRecoveryQuadraticCost
                (GaloisForLFunctions.primesBelowSubtype N) - 1 <
            (1 - gammaSewnSynchronizedRecoveryRatio nu x
                (GaloisForLFunctions.primesBelowSubtype N)) / x ^ 2 := by
    let C := gammaSewnSynchronizedRecoveryQuadraticCost
      (GaloisForLFunctions.primesBelowSubtype N)
    have hlarge :
        ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), C - 1 <
          (1 - gammaSewnSynchronizedRecoveryRatio nu x
              (GaloisForLFunctions.primesBelowSubtype N)) / x ^ 2 :=
      (hlimit N).eventually (Ioi_mem_nhds (by linarith : C - 1 < C))
    have hsmallNhds :
        ∀ᶠ x : ℝ in 𝓝 (0 : ℝ), x < 1 / ((N : ℝ) + 1) :=
      Iio_mem_nhds (by positivity)
    have hsmall := hsmallNhds.filter_mono
      (show 𝓝[>] (0 : ℝ) ≤ 𝓝 (0 : ℝ) from nhdsWithin_le_nhds)
    have hpos : ∀ᶠ x : ℝ in 𝓝[>] (0 : ℝ), 0 < x := self_mem_nhdsWithin
    obtain ⟨x, hxlarge, hxsmall, hxpos⟩ :=
      (hlarge.and (hsmall.and hpos)).exists
    exact ⟨x, hxpos, hxsmall, hxlarge⟩
  choose aperture hpos hsmall hloss using hexists
  refine ⟨aperture, hpos, hsmall, ?_, ?_⟩
  · rw [Metric.tendsto_atTop]
    intro ε hε
    obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
    refine ⟨M, fun N hMN => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_pos (hpos N)]
    have hMNreal : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
    have hM' : 1 < ε * (M : ℝ) := by
      rw [div_lt_iff₀ hε] at hM
      nlinarith
    have hbound : 1 / ((N : ℝ) + 1) < ε := by
      rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
      nlinarith
    exact (hsmall N).trans hbound
  · rw [tendsto_atTop]
    intro B
    have hcost :=
      (tendsto_atTop.1
        tendsto_gammaSewnSynchronizedRecoveryQuadraticCost_primesBelow_atTop) (B + 1)
    filter_upwards [hcost] with N hN
    linarith [hloss N]

end
end RHTower
