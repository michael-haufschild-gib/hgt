import GaloisForLFunctions.SignedArithmeticHodgeTheory.TheDyadicDetailsAreTheLiteralBalancedHaarSources
import GaloisForLFunctions.SignedArithmeticHodgeTheory.EveryFiniteCellSourceHasFiniteDyadicCoordinates
import GaloisForLFunctions.SignedArithmeticHodgeTheory.DyadicVarianceSplitsIntoTheLiteralHaarReadout
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.SmoothFiniteCellArithmeticForm

/-!
# Physical source realization of all dyadic Haar coordinates

Extension by zero intertwines nonnegative half-line shifts with literal
whole-line translations. Thus every dyadic Haar basis coefficient is the
normalized integral against the existing balanced source profile.
-/

noncomputable section
open MeasureTheory Set Filter RHTower
open scoped InnerProductSpace

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory
open HTGeometry ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry

local notation "CellH" => lp (fun _ : ℕ+ => ℂ) 2
local notation "LineH" => Lp ℂ 2 (volume : Measure ℝ)

/-- The actual complete-cell embedding into whole-line physical L². -/
def wholeLineLogCellEmbedding : CellH →L[ℂ] LineH :=
  halfLineExtend ∘L logCellEmbedding

theorem norm_wholeLineLogCellEmbedding (x : CellH) :
    ‖wholeLineLogCellEmbedding x‖ = ‖x‖ :=
  (norm_halfLineExtendLM (logCellEmbedding x)).trans (norm_logCellEmbedding_apply x)

theorem wholeLineLogCellEmbedding_adjoint_self (x : CellH) :
    wholeLineLogCellEmbedding.adjoint (wholeLineLogCellEmbedding x) = x := by
  have h := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self wholeLineLogCellEmbedding).mp
    norm_wholeLineLogCellEmbedding
  exact congrArg (fun T => T x) h

/-- Zero extension turns every nonnegative half-line shift into the literal full-line translate. -/
theorem halfLineExtend_rightShift_coeFn {s : ℝ} (hs : 0 ≤ s)
    (u : Lp ℂ 2 halfLineMeasure) :
    (halfLineExtend (halfLineRightShift s u) : ℝ → ℂ) =ᵐ[volume]
      fun x => (halfLineExtend u : ℝ → ℂ) (x - s) := by
  refine (halfLineExtend_coeFn _).trans
    ((indicator_ae_eq_of_halfLine (halfLineRightShift_coeFn s u)).trans ?_)
  filter_upwards [(measurePreserving_sub_right volume s).quasiMeasurePreserving.ae_eq_comp
    (halfLineExtend_coeFn u)] with x hx
  by_cases hx0 : x ∈ Ici (0 : ℝ)
  · exact indicator_of_mem hx0 _
  · rw [indicator_of_notMem hx0, hx,
      indicator_of_notMem (show x - s ∉ Ici (0 : ℝ) by
        simp only [mem_Ici] at hx0 ⊢; linarith only [hx0, hs])]

private theorem haarProfile_zero_neg (a : ℕ+) {x : ℝ} (hx : x < 0) :
    haarProfile a x = 0 := by
  have hraw (n : ℕ) (hn : 1 ≤ n) : rawCell n x = 0 := by
    apply indicator_of_notMem
    intro h
    have hl := Real.log_nonneg (by exact_mod_cast hn : (1 : ℝ) ≤ n)
    linarith only [h.1, hl, hx]
  have ha := a.pos
  simp only [haarProfile, hraw _ (by omega), mul_zero, sub_zero]

theorem halfLineExtend_haarAtom_coeFn (a : ℕ+) :
    (halfLineExtend (haarAtom a) : ℝ → ℂ) =ᵐ[volume]
      fun x => (haarProfile a x : ℂ) := by
  refine (halfLineExtend_coeFn _).trans
    ((indicator_ae_eq_of_halfLine (haarAtom_coeFn a)).trans (Eventually.of_forall ?_))
  intro x
  by_cases hx : x ∈ Ici (0 : ℝ)
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx, haarProfile_zero_neg a (lt_of_not_ge hx), Complex.ofReal_zero]

/-- Every power of the actual dyadic shift has the expected original profile. -/
theorem halfLineExtend_haarAtom_pow_coeFn (a : ℕ+) (j : ℕ) :
    (halfLineExtend ((halfLineRightShift (Real.log 2) ^ j) (haarAtom a)) : ℝ → ℂ) =ᵐ[volume]
      fun x => (haarProfile a (x - j * Real.log 2) : ℂ) := by
  induction j with
  | zero => simpa using halfLineExtend_haarAtom_coeFn a
  | succ j ih =>
    rw [pow_succ', mul_apply_eq_comp]
    refine (halfLineExtend_rightShift_coeFn (Real.log_nonneg (by norm_num)) _).trans ?_
    refine ((measurePreserving_sub_right volume (Real.log 2)).quasiMeasurePreserving.ae_eq_comp ih).trans
      (Eventually.of_forall ?_)
    intro x
    congr 2
    push_cast
    ring

/-- Exact whole-line waveform of a normalized dyadic detail basis vector. -/
theorem sqrt_mass_wholeLineLogCellOrbit_coeFn (a : ℕ+) (j : ℕ) :
    (fun x => (Real.sqrt (haarMass a) : ℂ) *
      (wholeLineLogCellEmbedding (logCellDyadicOrbit (j, some a)) : ℝ → ℂ) x) =ᵐ[volume]
        fun x => (haarProfile a (x - j * Real.log 2) : ℂ) := by
  have hv : (Real.sqrt (haarMass a) : ℂ) •
      wholeLineLogCellEmbedding (logCellDyadicOrbit (j, some a)) =
      halfLineExtend ((halfLineRightShift (Real.log 2) ^ j) (haarAtom a)) := by
    rw [wholeLineLogCellEmbedding, ContinuousLinearMap.comp_apply, ← map_smul]
    change halfLineExtend ((Real.sqrt (haarMass a) : ℂ) •
      logCellEmbedding ((logCellShift 2 ^ j) (logCellDyadicDetail a))) = _
    exact congrArg halfLineExtend (sqrt_haarMass_smul_logCellEmbedding_detail_pow a j)
  have h := Lp.coeFn_smul (Real.sqrt (haarMass a) : ℂ)
    (wholeLineLogCellEmbedding (logCellDyadicOrbit (j, some a)))
  rw [hv] at h
  exact h.symm.trans (halfLineExtend_haarAtom_pow_coeFn a j)

/-- The original real source, viewed in physical complex L². -/
def realSourceLp (f : ℝ → ℝ) (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) : LineH :=
  (memLp_compact_bv hv hc).ofReal.toLp (fun x => (f x : ℂ))

theorem realSourceLp_coeFn (f : ℝ → ℝ) (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    (realSourceLp f hv hc : ℝ → ℂ) =ᵐ[volume] fun x => (f x : ℂ) :=
  MemLp.coeFn_toLp _

/-- Coordinates of the actual source in the closed complete-cell space. -/
def physicalLogCellCoordinates (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    lp (fun _ : ℕ × Option ℕ+ => ℂ) 2 :=
  logCellDyadicCoordinates (wholeLineLogCellEmbedding.adjoint (realSourceLp f hv hc))

/-- The Hilbert coordinate is the actual translated Haar readout, including its exact mass. -/
theorem physicalLogCellCoordinates_detail (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) (j : ℕ) (a : ℕ+) :
    physicalLogCellCoordinates f hv hc (j, some a) = (logCellHaarReadout 0 (j, a) f : ℂ) := by
  let u := wholeLineLogCellEmbedding (logCellDyadicOrbit (j, some a))
  let v := realSourceLp f hv hc
  have hprofile := sqrt_mass_wholeLineLogCellOrbit_coeFn a j
  have hsource := realSourceLp_coeFn f hv hc
  have hinner : inner ℂ ((Real.sqrt (haarMass a) : ℂ) • u) v =
      ((∫ x, haarProfile a (x - j * Real.log 2) * f x : ℝ) : ℂ) := by
    rw [L2.inner_def]
    calc
      _ = ∫ x, ((haarProfile a (x - j * Real.log 2) * f x : ℝ) : ℂ) := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_smul (Real.sqrt (haarMass a) : ℂ) u,
          hprofile, hsource] with x hu hp hvx
        change inner ℂ (((Real.sqrt (haarMass a) : ℂ) • u : LineH) x) (v x) = _
        rw [hu, Pi.smul_apply, smul_eq_mul, hp, hvx, RCLike.inner_apply,
          Complex.conj_ofReal, ← Complex.ofReal_mul, mul_comm]
      _ = _ := integral_complex_ofReal
  have hscalar : (Real.sqrt (haarMass a) : ℂ) *
      physicalLogCellCoordinates f hv hc (j, some a) =
        (Real.sqrt (haarMass a) : ℂ) * (logCellHaarReadout 0 (j, a) f : ℂ) := by
    rw [physicalLogCellCoordinates, logCellDyadicCoordinates_apply,
      ContinuousLinearMap.adjoint_inner_right]
    rw [inner_smul_left, Complex.conj_ofReal] at hinner
    rw [show (∫ x, haarProfile a (x - j * Real.log 2) * f x) =
        Real.sqrt (haarMass a) * logCellHaarReadout 0 (j, a) f by
      simpa only [zero_add] using integral_translated_haarProfile_mul 0 (j, a)
        (memLp_compact_bv hv hc), Complex.ofReal_mul] at hinner
    exact hinner
  exact mul_left_cancel₀ (by exact_mod_cast (Real.sqrt_pos.mpr (haarMass_pos a.pos)).ne') hscalar

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.halfLineExtend_haarAtom_pow_coeFn
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.physicalLogCellCoordinates_detail
