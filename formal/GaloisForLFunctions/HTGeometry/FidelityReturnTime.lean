/-
# The fidelity first-return time of a weighted spectral packet

Anchoring a finite spectrum at its lowest level turns the return fidelity into a phase-return
problem for the anchored gaps: a continuous return of the gap packet is exactly a simultaneous
approximation of every anchored gap phase by a whole turn.  The quadratic comparison between
fidelity deficit and phase radius therefore converts a winding return into a fidelity return and
back.

The deficit never vanishes at a positive time unless every projective gap ratio is rational with a
common denominator, which makes the ratio vector very well approximable.  For a non-approximable
ratio vector the deficit is therefore bounded away from zero on every compact interval of positive
times, so no fidelity return can occur before the winding threshold.

Main results:
* `anchoredGapPacket`, `continuousReturn_iff_latticeClose` — the packet reading.
* `fidelityReturnTime` — the first fidelity return after a positive cutoff.
* `fidelityReturnTime_le_of_windingReturn` — **a winding return produces a fidelity return**.
* `continuousReturn_of_mem_fidelityReturnSet` — **a fidelity return is a phase return**.
* `spectralReturnDeficit_ne_zero`, `exists_pos_le_spectralReturnDeficit_on_Icc` — **the deficit is
  bounded away from zero on compact positive intervals**.
-/
import GaloisForLFunctions.HTGeometry.FidelityPhaseRadius
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.FirstReturnExponent
import GaloisForLFunctions.HTGeometry.FirstHitExponentLaw
import GaloisForLFunctions.HTGeometry.SpectralGapRatioExtremality

open Filter Topology Real
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedVariables false

noncomputable section

variable {e : ℕ}

/-- The gaps of a spectrum from its lowest level, with the first gap as the clock. -/
def anchoredGapPacket (E : Fin (e + 3) → ℝ) : Fin (e + 2) → ℝ := fun j => E j.succ - E 0

@[simp] theorem anchoredGapPacket_zero (E : Fin (e + 3) → ℝ) :
    anchoredGapPacket E 0 = E 1 - E 0 := rfl

theorem gapRatio_anchoredGapPacket_succ (E : Fin (e + 3) → ℝ) (i : Fin (e + 1)) :
    gapRatio (anchoredGapPacket E) i.succ
      = anchoredGapRatioMap E 0 1 (fun k => k.succ.succ) i := rfl

/-- Every anchored gap phase, read from the packet. -/
theorem gapTurn_anchoredGapPacket (E : Fin (e + 3) → ℝ) (t : ℝ) (j : Fin (e + 2)) :
    gapTurn (anchoredGapPacket E) t j = t * (E j.succ - E 0) / (2 * π) := rfl

/-- A continuous return of the packet is exactly a phase return of every level. -/
theorem continuousReturn_iff_latticeClose (E : Fin (e + 3) → ℝ) {r t : ℝ} (hr : 0 < r) :
    ContinuousReturn (anchoredGapPacket E) r t
      ↔ ∀ j : Fin (e + 3), latticeClose (t * (E j - E 0) / (2 * π)) r := by
  constructor
  · intro h j
    refine Fin.cases ?_ (fun i => ?_) j
    · refine ⟨0, ?_⟩
      simp [hr]
    · have := h i
      rw [gapTurn_anchoredGapPacket] at this
      exact this
  · intro h j
    rw [gapTurn_anchoredGapPacket]
    exact h j.succ

/-! ## The fidelity first-return time -/

/-- The times after the cutoff at which the return fidelity deficit is below `δ`. -/
def fidelityReturnSet {D : ℕ} (E p : Fin D → ℝ) (t₀ δ : ℝ) : Set ℝ :=
  {t : ℝ | t₀ ≤ t ∧ spectralReturnDeficit E p t < δ}

/-- The first fidelity return after the cutoff. -/
def fidelityReturnTime {D : ℕ} (E p : Fin D → ℝ) (t₀ δ : ℝ) : ℝ :=
  sInf (fidelityReturnSet E p t₀ δ)

theorem bddBelow_fidelityReturnSet {D : ℕ} (E p : Fin D → ℝ) (t₀ δ : ℝ) :
    BddBelow (fidelityReturnSet E p t₀ δ) := ⟨t₀, fun t ht => ht.1⟩

theorem le_fidelityReturnTime {D : ℕ} {E p : Fin D → ℝ} {t₀ δ : ℝ}
    (hne : (fidelityReturnSet E p t₀ δ).Nonempty) :
    t₀ ≤ fidelityReturnTime E p t₀ δ := le_csInf hne fun t ht => ht.1

/-- **A winding return produces a fidelity return.**  If a whole number of clock windings puts
every projective gap ratio within `r` of the integer lattice, the corresponding time realises a
fidelity deficit below `8 pi^(2 : ℕ) r^(2 : ℕ)`. -/
theorem fidelityReturnTime_le_of_windingReturn (E p : Fin (e + 3) → ℝ)
    (hp1 : ∑ j, p j = 1) (hpnn : ∀ j, 0 ≤ p j) (hg0 : 0 < E 1 - E 0)
    {r δ t₀ : ℝ} (hr : 0 < r) (hδ : 8 * π ^ 2 * r ^ 2 < δ) {q : ℕ} (hq1 : 1 ≤ q)
    (hy : ∀ i : Fin (e + 1),
      latticeClose ((q : ℝ) * anchoredGapRatioMap E 0 1 (fun k => k.succ.succ) i) r)
    (ht₀ : t₀ ≤ 2 * π * (q : ℝ) / (E 1 - E 0)) :
    (fidelityReturnSet E p t₀ δ).Nonempty ∧
      fidelityReturnTime E p t₀ δ ≤ 2 * π * (q : ℝ) / (E 1 - E 0) := by
  have hwind : WindingReturn (anchoredGapPacket E) r ((q : ℤ)) := by
    intro j
    refine Fin.cases ?_ (fun i => ?_) j
    · rw [gapRatio_zero (anchoredGapPacket E) (by rw [anchoredGapPacket_zero]; exact hg0.ne')]
      refine ⟨(q : ℤ), ?_⟩
      push_cast
      simpa using hr
    · rw [gapRatio_anchoredGapPacket_succ]
      have := hy i
      push_cast
      exact this
  have hcont := continuousReturn_of_windingReturn (anchoredGapPacket E)
    (by rw [anchoredGapPacket_zero]; exact hg0.ne') hwind
  rw [anchoredGapPacket_zero] at hcont
  have hcast : (((q : ℤ) : ℝ)) = (q : ℝ) := by push_cast; ring
  rw [hcast] at hcont
  have hlat := (continuousReturn_iff_latticeClose E hr).mp hcont
  have hdef := spectralReturnDeficit_le_of_latticeClose E p hp1 hpnn 0 hr.le hlat
  have hmem : 2 * π * (q : ℝ) / (E 1 - E 0) ∈ fidelityReturnSet E p t₀ δ :=
    ⟨ht₀, lt_of_le_of_lt hdef hδ⟩
  exact ⟨⟨_, hmem⟩, csInf_le (bddBelow_fidelityReturnSet E p t₀ δ) hmem⟩

/-- **A fidelity return is a phase return.**  Every time at which the deficit is below `δ` puts
every anchored gap phase within `sqrt δ / (2 c)` of a whole turn. -/
theorem continuousReturn_of_mem_fidelityReturnSet (E p : Fin (e + 3) → ℝ)
    (hp1 : ∑ j, p j = 1) (hpnn : ∀ j, 0 ≤ p j) {c δ t₀ t : ℝ} (hc : 0 < c)
    (hcp : ∀ j, c ≤ p j) (ht : t ∈ fidelityReturnSet E p t₀ δ) :
    ContinuousReturn (anchoredGapPacket E) (Real.sqrt δ / (2 * c)) t := by
  have hδ : 0 < δ := lt_of_le_of_lt (spectralReturnDeficit_nonneg E p hp1 hpnn t) ht.2
  have hpos : 0 < Real.sqrt δ / (2 * c) := by positivity
  refine (continuousReturn_iff_latticeClose E hpos).mpr fun j => ?_
  exact latticeClose_of_spectralReturnDeficit_lt E p hp1 hpnn 0 hc hcp ht.2 j

/-! ## The deficit is bounded away from zero on compact time intervals -/

theorem continuous_spectralReturnAmplitude {D : ℕ} (E p : Fin D → ℝ) :
    Continuous (spectralReturnAmplitude E p) := by
  unfold spectralReturnAmplitude
  refine continuous_finsetSum _ fun j _ => continuous_const.mul ?_
  refine Complex.continuous_exp.comp (Continuous.mul ?_ continuous_const)
  exact Complex.continuous_ofReal.comp (by fun_prop)

theorem continuous_spectralReturnDeficit {D : ℕ} (E p : Fin D → ℝ) :
    Continuous (spectralReturnDeficit E p) :=
  continuous_const.sub (((continuous_spectralReturnAmplitude E p).norm).pow 2)

/-- **A vanishing deficit rationalises the projective gap ratios.**  If the return fidelity is
exact at a positive time, every projective gap ratio is a ratio of integers, hence very well
approximable. -/
theorem spectralReturnDeficit_ne_zero (E p : Fin (e + 3) → ℝ)
    (hp1 : ∑ j, p j = 1) (hppos : ∀ j, 0 < p j) (hg0 : 0 < E 1 - E 0)
    (hnv : ¬ KleinbockMargulis.VWA (anchoredGapRatioMap E 0 1 (fun k => k.succ.succ)))
    {t : ℝ} (ht : 0 < t) : spectralReturnDeficit E p t ≠ 0 := by
  intro h0
  have hpi : (0 : ℝ) < π := Real.pi_pos
  have hnorm : ∀ j : Fin (e + 3),
      ‖Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I)‖ = 1 := fun j =>
    Complex.norm_exp_ofReal_mul_I _
  have hzero : (1 : ℝ) - ‖_root_.HTGeometry.finitePhaseOverlap p
      (fun j => Complex.exp (((-(t * E j) : ℝ) : ℂ) * Complex.I))‖ ^ 2 = 0 := by
    rw [← spectralReturnAmplitude_eq_finitePhaseOverlap]
    exact h0
  have hall := (_root_.HTGeometry.finitePhase_fidelityDeficit_eq_zero_iff p _ hp1 hppos
    hnorm).mp hzero
  have hM : ∀ j : Fin (e + 3), ∃ m : ℤ, t * (E j - E 0) = 2 * π * (m : ℝ) := by
    intro j
    have hj := hall j 0
    have hne : Complex.exp (((-(t * E 0) : ℝ) : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    have hone : Complex.exp ((((-(t * E j)) - (-(t * E 0)) : ℝ) : ℂ) * Complex.I) = 1 := by
      rw [show ((((-(t * E j)) - (-(t * E 0)) : ℝ) : ℂ)) * Complex.I
          = ((-(t * E j) : ℝ) : ℂ) * Complex.I - ((-(t * E 0) : ℝ) : ℂ) * Complex.I from by
        push_cast; ring, Complex.exp_sub, hj, div_self hne]
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hone
    refine ⟨-n, ?_⟩
    have hI : (Complex.I : ℂ) ≠ 0 := Complex.I_ne_zero
    have hcancel : ((((-(t * E j)) - (-(t * E 0)) : ℝ) : ℂ)) = (n : ℂ) * (2 * (π : ℂ)) := by
      have := hn
      rw [show ((n : ℂ)) * (2 * (π : ℂ) * Complex.I) = ((n : ℂ) * (2 * (π : ℂ))) * Complex.I from by
        ring] at this
      exact mul_right_cancel₀ hI this
    have hcancel' : ((((-(t * E j)) - (-(t * E 0)) : ℝ)) : ℂ) = ((((n : ℝ) * (2 * π) : ℝ)) : ℂ) := by
      rw [hcancel]
      push_cast
      ring
    have hreal : (-(t * E j)) - (-(t * E 0)) = (n : ℝ) * (2 * π) :=
      Complex.ofReal_inj.mp hcancel'
    push_cast
    linarith [hreal]
  choose M hM using hM
  have hM1 : t * (E 1 - E 0) = 2 * π * (M 1 : ℝ) := hM 1
  have hM1pos : (0 : ℝ) < (M 1 : ℝ) := by nlinarith [mul_pos ht hg0, hpi]
  have hM1nat : 1 ≤ (M 1).natAbs := by
    have : 0 < M 1 := by exact_mod_cast hM1pos
    omega
  have hratio : ∀ i : Fin (e + 1),
      anchoredGapRatioMap E 0 1 (fun k => k.succ.succ) i
        = (M (i.succ.succ) : ℝ) / (M 1 : ℝ) := by
    intro i
    have h1 := hM (i.succ.succ)
    have h2 := hM 1
    rw [anchoredGapRatioMap]
    have hpine : (π : ℝ) ≠ 0 := Real.pi_ne_zero
    have hM1ne : ((M 1 : ℤ) : ℝ) ≠ 0 := ne_of_gt hM1pos
    have hEj : E (i.succ.succ) - E 0 = 2 * π * (M (i.succ.succ) : ℝ) / t := by
      rw [eq_div_iff ht.ne', mul_comm]
      exact h1
    have hE1 : E 1 - E 0 = 2 * π * (M 1 : ℝ) / t := by
      rw [eq_div_iff ht.ne', mul_comm]
      exact h2
    rw [hEj, hE1]
    field_simp

  refine hnv ⟨1, one_pos, ?_⟩
  refine Set.infinite_of_injective_forall_mem
    (f := fun k : ℕ => (k + 1) * (M 1).natAbs) ?_ ?_
  · intro a b hab
    simp only at hab
    have : a + 1 = b + 1 := Nat.eq_of_mul_eq_mul_right (by omega) hab
    omega
  · intro k
    refine ⟨by
      calc 1 = 1 * 1 := by ring
        _ ≤ (k + 1) * (M 1).natAbs := Nat.mul_le_mul (by omega) hM1nat, ?_⟩
    refine ⟨fun i => ((k : ℤ) + 1) * M (i.succ.succ), fun i => ?_⟩
    have hq : ((((k + 1) * (M 1).natAbs : ℕ) : ℝ))
        * anchoredGapRatioMap E 0 1 (fun k => k.succ.succ) i
        = (((((k : ℤ) + 1) * M (i.succ.succ) : ℤ)) : ℝ) := by
      rw [hratio i]
      have hnat : ((((M 1).natAbs : ℕ) : ℝ)) = ((M 1 : ℤ) : ℝ) := by
        have hpos : 0 < M 1 := by exact_mod_cast hM1pos
        rw [← Int.cast_natCast, Int.natAbs_of_nonneg hpos.le]
      push_cast [hnat]
      field_simp
    rw [hq, sub_self, abs_zero]
    exact Real.rpow_nonneg (by positivity) _

/-- **The deficit is bounded away from zero on compact positive time intervals.** -/
theorem exists_pos_le_spectralReturnDeficit_on_Icc (E p : Fin (e + 3) → ℝ)
    (hp1 : ∑ j, p j = 1) (hppos : ∀ j, 0 < p j) (hg0 : 0 < E 1 - E 0)
    (hnv : ¬ KleinbockMargulis.VWA (anchoredGapRatioMap E 0 1 (fun k => k.succ.succ)))
    {t₀ T : ℝ} (ht₀ : 0 < t₀) :
    ∃ m : ℝ, 0 < m ∧ ∀ t ∈ Set.Icc t₀ T, m ≤ spectralReturnDeficit E p t := by
  rcases le_or_gt t₀ T with hle | hgt
  · obtain ⟨s, hs, hmin⟩ := (isCompact_Icc (a := t₀) (b := T)).exists_isMinOn
      ⟨t₀, Set.left_mem_Icc.mpr hle⟩ (continuous_spectralReturnDeficit E p).continuousOn
    have hspos : 0 < s := lt_of_lt_of_le ht₀ hs.1
    have hnn := spectralReturnDeficit_nonneg E p hp1 (fun j => (hppos j).le) s
    refine ⟨spectralReturnDeficit E p s,
      lt_of_le_of_ne hnn (Ne.symm (spectralReturnDeficit_ne_zero E p hp1 hppos hg0 hnv hspos)),
      fun t ht => hmin ht⟩
  · exact ⟨1, one_pos, fun t ht => absurd (le_trans ht.1 ht.2) (by linarith [hgt])⟩

end

end GaloisForLFunctions.HTGeometry
