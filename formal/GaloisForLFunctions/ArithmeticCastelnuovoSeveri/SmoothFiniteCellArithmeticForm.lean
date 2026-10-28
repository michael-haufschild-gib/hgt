import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SmoothCompleteWeilTransfer
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.CompleteWeilSourceTransfer

/-!
# Smooth sections realize the existing complete-cell arithmetic form

The zero extension of the actual half-line cell section has the literal whole-cell
profile. Thus its prime translations are exactly the prime term of that profile,
and pole-preserving smoothing converges to the original finite arithmetic form.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped InnerProductSpace
open _root_.RHTower hiding mollifier
open _root_.RHTower.CHMDDoobGraph
open Zeta23

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open HTGeometry SpacingScaleHarmonicAnalysis

def wholeCellProfile (c : ℕ → ℝ) (X : ℕ) (x : ℝ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 X, c a * rawCell a x

theorem wholeCellProfile_regular (c : ℕ → ℝ) (X : ℕ) :
    BoundedVariationOn (wholeCellProfile c X) univ ∧ HasCompactSupport (wholeCellProfile c X) := by
  have hs (s : Finset ℕ) : BoundedVariationOn (fun x => ∑ a ∈ s, c a * rawCell a x) univ := by
    classical
    induction s using Finset.induction_on with
    | empty =>
      simpa only [Finset.sum_empty] using
        ((monotone_const : Monotone (fun _ : ℝ => (0 : ℝ))).monotoneOn univ).boundedVariationOn
          (C := 0) (fun _ _ => by simp)
    | @insert a s ha ih =>
      have hv := boundedVariationOn_sub (bv_const_mul (c a) (rawCell_bv a))
        (bv_const_mul (-1) ih)
      simpa only [Finset.sum_insert ha, neg_one_mul, sub_neg_eq_add] using hv
  refine ⟨hs (Finset.Icc 1 X), HasCompactSupport.intro
    (show IsCompact (Icc (0 : ℝ) (Real.log (X + 1 : ℕ))) from isCompact_Icc) ?_⟩
  intro x hx
  apply Finset.sum_eq_zero
  intro a ha
  have ha' := Finset.mem_Icc.mp ha
  have hn : x ∉ Ico (Real.log a) (Real.log (a + 1 : ℕ)) := by
    intro hi
    have hlo : 0 ≤ Real.log a := Real.log_nonneg (by exact_mod_cast ha'.1)
    have hhi : Real.log (a + 1 : ℕ) ≤ Real.log (X + 1 : ℕ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast Nat.add_le_add_right ha'.2 1
    exact hx ⟨hlo.trans hi.1, hi.2.le.trans hhi⟩
  rw [rawCell, indicator_of_notMem hn, mul_zero]

theorem wholeCellProfile_zero_neg (c : ℕ → ℝ) (X : ℕ) {x : ℝ} (hx : x < 0) :
    wholeCellProfile c X x = 0 := by
  apply Finset.sum_eq_zero
  intro a ha
  have hlog : 0 ≤ Real.log a := Real.log_nonneg (by exact_mod_cast (Finset.mem_Icc.mp ha).1)
  rw [rawCell, indicator_of_notMem (fun h => (not_le_of_gt hx) (hlog.trans h.1)), mul_zero]

theorem wholeCellProfile_supported (c : ℕ → ℝ) (X : ℕ) :
    SupportedIn (Real.log (X + 1 : ℕ)) (wholeCellProfile c X) := by
  intro x hx
  apply Finset.sum_eq_zero
  intro a ha
  have ha' := Finset.mem_Icc.mp ha
  have hn : x ∉ Ico (Real.log a) (Real.log (a + 1 : ℕ)) := by
    intro hi
    have h0 : 0 ≤ Real.log a := Real.log_nonneg (by exact_mod_cast ha'.1)
    have hh : Real.log (a + 1 : ℕ) ≤ Real.log (X + 1 : ℕ) := by
      apply Real.log_le_log (by positivity)
      exact_mod_cast Nat.add_le_add_right ha'.2 1
    rw [abs_of_nonneg (h0.trans hi.1)] at hx
    exact (not_lt_of_ge (hi.2.trans_le hh).le) hx
  rw [rawCell, indicator_of_notMem hn, mul_zero]

theorem cellSection_coeFn_wholeCellProfile (c : ℕ → ℝ) (X : ℕ) :
    (cellSection c 1 X : ℝ → ℂ) =ᵐ[halfLineMeasure]
      fun x => (wholeCellProfile c X x : ℂ) := by
  have hs := coeFn_finset_sum_smul (Finset.Icc 1 X) (fun a => (c a : ℂ)) cellAtom
  have ha : ∀ᵐ x ∂halfLineMeasure, ∀ a : ℕ,
      (cellAtom a : ℝ → ℂ) x =
        (Ico (Real.log a) (Real.log (a + 1 : ℕ))).indicator (fun _ => (1 : ℂ)) x :=
    ae_all_iff.mpr cellAtom_coeFn
  unfold cellSection
  filter_upwards [hs, ha] with x hx ha
  rw [hx, wholeCellProfile, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [ha a]
  by_cases hm : x ∈ Ico (Real.log a) (Real.log (a + 1 : ℕ))
  · simp only [rawCell, indicator_of_mem hm, mul_one]
  · simp only [rawCell, indicator_of_notMem hm, mul_zero, Complex.ofReal_zero]

theorem halfLineExtend_wholeCellProfile (c : ℕ → ℝ) (X : ℕ) :
    (halfLineExtend (cellSection c 1 X) : ℝ → ℂ) =ᵐ[volume]
      fun x => (wholeCellProfile c X x : ℂ) := by
  refine (halfLineExtend_coeFn _).trans
    ((indicator_ae_eq_of_halfLine (cellSection_coeFn_wholeCellProfile c X)).trans ?_)
  apply Eventually.of_forall
  intro x
  by_cases hx : x ∈ Ici (0 : ℝ)
  · exact indicator_of_mem hx _
  · simp only [indicator_of_notMem hx, wholeCellProfile_zero_neg c X (lt_of_not_ge hx), Complex.ofReal_zero]

/-- The actual half-line translation has the literal whole-line cell correlation. -/
theorem inner_shift_wholeCellProfile (c : ℕ → ℝ) (X : ℕ) (t : ℝ) :
    (inner ℂ (halfLineRightShift t (cellSection c 1 X)) (cellSection c 1 X)).re =
      ∫ x, wholeCellProfile c X x * wholeCellProfile c X (x + t) := by
  let u := cellSection c 1 X
  have hu := cellSection_coeFn_wholeCellProfile c X
  have he := halfLineExtend_wholeCellProfile c X
  have ht : ∀ᵐ x ∂halfLineMeasure,
      (halfLineExtend (cellSection c 1 X) : ℝ → ℂ) (x - t) =
        (wholeCellProfile c X (x - t) : ℂ) :=
    ae_restrict_of_ae ((measurePreserving_sub_right volume t).quasiMeasurePreserving.ae he)
  have hinner : Integrable (fun x =>
      inner ℂ ((halfLineRightShift t u : ℝ → ℂ) x) (u x)) halfLineMeasure :=
    L2.integrable_inner (halfLineRightShift t u) u
  have hre := integral_re hinner
  simp only [RCLike.re_to_complex] at hre
  rw [L2.inner_def, ← hre]
  have hi : (∫ x, (inner ℂ ((halfLineRightShift t u : ℝ → ℂ) x) (u x)).re ∂halfLineMeasure) =
      ∫ x, wholeCellProfile c X (x - t) * wholeCellProfile c X x ∂halfLineMeasure := by
    apply integral_congr_ae
    filter_upwards [halfLineRightShift_coeFn t u, hu, ht] with x hshift hx hxt
    rw [hshift, hx, hxt, RCLike.inner_apply]
    simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re, mul_comm]
  rw [hi]
  have hall : (∫ x, wholeCellProfile c X (x - t) * wholeCellProfile c X x ∂halfLineMeasure) =
      ∫ x, wholeCellProfile c X (x - t) * wholeCellProfile c X x := by
    rw [halfLineMeasure, ← integral_indicator measurableSet_Ici]
    apply integral_congr_ae
    filter_upwards [] with x
    by_cases hx : x ∈ Ici (0 : ℝ)
    · exact indicator_of_mem hx _
    · simp only [indicator_of_notMem hx, wholeCellProfile_zero_neg c X (lt_of_not_ge hx), mul_zero]
  rw [hall]
  have h := integral_sub_right_eq_self (μ := (volume : Measure ℝ))
    (fun x => wholeCellProfile c X x * wholeCellProfile c X (x + t)) t
  simpa only [sub_add_cancel] using h

/-- The existing complete-cell prime energy is precisely the full prime term. -/
theorem cellPrimeEnergy_eq_wholeCellProfile (c : ℕ → ℝ) (X : ℕ) :
    cellPrimeEnergy c 1 X = primeSum (wholeCellProfile c X) := by
  rw [← smoothPrimePair_self_eq_primeSum]
  unfold cellPrimeEnergy smoothPrimePair
  apply tsum_congr
  intro m
  rw [inner_shift_wholeCellProfile]

theorem finiteCellProfile_eq_wholeCellProfile (c : ℕ → ℝ) (X : ℕ) :
    finiteCellProfile c 0 1 X = wholeCellProfile c X := by
  funext x
  simp only [finiteCellProfile, wholeCellProfile, logEndpoint, Nat.cast_one,
    Real.log_one, sub_zero]
  apply Finset.sum_congr rfl
  intro a _
  by_cases hx : x ∈ Ico (Real.log a) (Real.log (a + 1 : ℕ))
  · simp only [rawCell, indicator_of_mem hx, mul_one]
  · simp only [rawCell, indicator_of_notMem hx, mul_zero]

theorem finiteCellWeil_eq_roughWeil (c : ℕ → ℝ) (X : ℕ) :
    finiteCellWeil c 0 1 X = roughWeil (wholeCellProfile c X) := by
  rw [finiteCellWeil, finiteCellProfile_eq_wholeCellProfile,
    cellPrimeEnergy_eq_wholeCellProfile]
  rfl

/-- The complete-cell arithmetic form on `[log 1, log (X+1))` is realized by smooth tests,
with no change in either pole coordinate and no discarded prime or Gamma term. -/
theorem finiteCellWeil_smooth_realization (c : ℕ → ℝ) (X : ℕ) :
    (∀ n, ContDiff ℝ 2 (poleSmooth (wholeCellProfile c X) n) ∧
      HasCompactSupport (poleSmooth (wholeCellProfile c X) n) ∧
      coshHalfMoment (poleSmooth (wholeCellProfile c X) n) = coshHalfMoment (wholeCellProfile c X) ∧
      sinhHalfMoment (poleSmooth (wholeCellProfile c X) n) = sinhHalfMoment (wholeCellProfile c X)) ∧
    Tendsto (fun n => weilQuad (poleSmooth (wholeCellProfile c X) n)) atTop
      (𝓝 (finiteCellWeil c 0 1 X)) := by
  have hv := (wholeCellProfile_regular c X).1
  have hc := (wholeCellProfile_regular c X).2
  refine ⟨fun n => ⟨poleSmooth_contDiff (memLp_compact_bv hv hc) n,
    poleSmooth_compact hc n, poleSmooth_halfMoments hv hc n⟩, ?_⟩
  rw [finiteCellWeil_eq_roughWeil]
  exact tendsto_poleSmooth_weilQuad hv hc (wholeCellProfile_supported c X)

/-- The same limit holds for the original zero-configuration intersection form. -/
theorem finiteCellWeil_original_surface_limit (c : ℕ → ℝ) (X : ℕ) :
    Tendsto (fun n => (zetaZeroConfig.W
      (fun u => (poleSmooth (wholeCellProfile c X) n u : ℂ))
      (fun u => (poleSmooth (wholeCellProfile c X) n u : ℂ))).re) atTop
      (𝓝 (finiteCellWeil c 0 1 X)) := by
  have hv := (wholeCellProfile_regular c X).1
  have hc := (wholeCellProfile_regular c X).2
  exact Filter.Tendsto.congr' (Eventually.of_forall fun n =>
    weilQuad_eq_zetaW (poleSmooth_contDiff (memLp_compact_bv hv hc) n)
      (poleSmooth_compact hc n)) (finiteCellWeil_smooth_realization c X).2

#print axioms cellPrimeEnergy_eq_wholeCellProfile
#print axioms finiteCellWeil_smooth_realization
#print axioms finiteCellWeil_original_surface_limit

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
