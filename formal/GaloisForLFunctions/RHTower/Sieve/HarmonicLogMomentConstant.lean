import GaloisForLFunctions.RHTower.Sieve.HarmonicLogWindowLowerMoments

/-!
# Additive constants of the harmonic logarithmic moments

For `m ≤ 2` the partial sums `∑_{j ≤ N} (log j)^m / j` differ from the primitive
`(log (N+1))^{m+1} / (m+1)` by a quantity that converges as `N → ∞`.  Its limit is the `m`-th
harmonic logarithmic moment constant — Euler's `γ` when `m = 0` — and the approach to the limit is
`(log (N+1))^m / (N+1)`.

The construction is monotone: since `t ↦ (log t)^m / t` is antitone beyond `8`, the gap between the
partial sum and the primitive increases and stays bounded, so it has a supremum, and the telescoped
increment bound gives the two-sided estimate.

This constant is what a harmonic window starting at the origin costs: for a window `(A, B]` with
`A` large the two constants cancel, but for `(0, B]` the constant is a genuine main term.
-/

open Finset MeasureTheory Set

noncomputable section

namespace RHTower.Sieve

/-- Nonnegativity of the logarithmic harmonic density beyond `8`. -/
theorem logPowDivId_nonneg_of_eight_le {m : ℕ} {x : ℝ} (hx : 8 ≤ x) :
    0 ≤ RHTower.logPowDivId m x := by
  have hlog : 2 ≤ Real.log x := RHTower.two_le_log_of_eight_le hx
  have hx0 : (0 : ℝ) < x := by linarith
  rw [RHTower.logPowDivId]
  positivity

/-- On a unit step beyond `8` the integral of an antitone density is between its endpoint values. -/
theorem integral_logPowDivId_unit_bounds {m : ℕ} {a : ℝ} (ha : 8 ≤ a)
    (hanti : AntitoneOn (RHTower.logPowDivId m) (Set.Ici 8)) :
    RHTower.logPowDivId m (a + 1) ≤ (∫ x in a..(a + 1), RHTower.logPowDivId m x) ∧
      (∫ x in a..(a + 1), RHTower.logPowDivId m x) ≤ RHTower.logPowDivId m a := by
  have hle : a ≤ a + 1 := by linarith
  have hcont : ContinuousOn (RHTower.logPowDivId m) (Set.uIcc a (a + 1)) := by
    rw [Set.uIcc_of_le hle]
    intro x hx
    have hx0 : (0 : ℝ) < x := by
      have : a ≤ x := hx.1
      linarith
    exact (RHTower.hasDerivAt_logPowDivId m hx0).continuousAt.continuousWithinAt
  have hint : IntervalIntegrable (RHTower.logPowDivId m) volume a (a + 1) :=
    hcont.intervalIntegrable
  have hmemIci : ∀ x ∈ Set.Icc a (a + 1), x ∈ Set.Ici (8 : ℝ) := by
    intro x hx
    have : a ≤ x := hx.1
    exact le_trans ha this
  constructor
  · have hmono : ∀ x ∈ Set.Icc a (a + 1),
        RHTower.logPowDivId m (a + 1) ≤ RHTower.logPowDivId m x := by
      intro x hx
      exact hanti (hmemIci x hx) (le_trans ha hle) hx.2
    have := intervalIntegral.integral_mono_on (μ := volume) hle
      (intervalIntegrable_const (c := RHTower.logPowDivId m (a + 1))) hint hmono
    simpa using this
  · have hmono : ∀ x ∈ Set.Icc a (a + 1),
        RHTower.logPowDivId m x ≤ RHTower.logPowDivId m a := by
      intro x hx
      exact hanti (le_trans ha le_rfl) (hmemIci x hx) hx.1
    have := intervalIntegral.integral_mono_on (μ := volume) hle hint
      (intervalIntegrable_const (c := RHTower.logPowDivId m a)) hmono
    simpa using this

/-- The gap between the harmonic logarithmic partial sum from `8` and its primitive. -/
def harmonicLogMomentGap (m N : ℕ) : ℝ :=
  harmonicLogWindowMoment m 8 N - harmonicLogMomentPrimitive m ((N + 1 : ℕ) : ℝ)

/-- One step of the gap is the density value minus the integral over the unit step. -/
theorem harmonicLogMomentGap_succ_sub {m N : ℕ} (hN : 8 ≤ N) :
    harmonicLogMomentGap m (N + 1) - harmonicLogMomentGap m N =
      RHTower.logPowDivId m ((N + 1 : ℕ) : ℝ) -
        (∫ x in ((N + 1 : ℕ) : ℝ)..(((N + 1 : ℕ) : ℝ) + 1), RHTower.logPowDivId m x) := by
  have hpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
  have hle : ((N + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) + 1 := by linarith
  have hint := intervalIntegral_logPowDivId m hpos hle
  have hsum : harmonicLogWindowMoment m 8 (N + 1) =
      harmonicLogWindowMoment m 8 N + RHTower.logPowDivId m ((N + 1 : ℕ) : ℝ) := by
    rw [harmonicLogWindowMoment, harmonicLogWindowMoment,
      Finset.sum_Ioc_succ_top (by omega : (8 : ℕ) ≤ N)]
    rfl
  have hshift : ((N + 1 : ℕ) : ℝ) + 1 = ((N + 1 + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [harmonicLogMomentGap, harmonicLogMomentGap, hsum, hint, hshift]
  ring

/-- The gap increases and its increment is at most the drop of the density. -/
theorem harmonicLogMomentGap_step {m N : ℕ} (hN : 8 ≤ N)
    (hanti : AntitoneOn (RHTower.logPowDivId m) (Set.Ici 8)) :
    0 ≤ harmonicLogMomentGap m (N + 1) - harmonicLogMomentGap m N ∧
      harmonicLogMomentGap m (N + 1) - harmonicLogMomentGap m N ≤
        RHTower.logPowDivId m ((N + 1 : ℕ) : ℝ) -
          RHTower.logPowDivId m ((N + 1 + 1 : ℕ) : ℝ) := by
  have ha : (8 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
    have : (8 : ℕ) ≤ N + 1 := by omega
    exact_mod_cast this
  obtain ⟨hlow, hhigh⟩ := integral_logPowDivId_unit_bounds ha hanti
  have hshift : ((N + 1 : ℕ) : ℝ) + 1 = ((N + 1 + 1 : ℕ) : ℝ) := by push_cast; ring
  rw [harmonicLogMomentGap_succ_sub hN, ← hshift]
  constructor
  · linarith
  · linarith

/-- Telescoped two-sided control of the gap over a range of indices. -/
theorem harmonicLogMomentGap_range {m N : ℕ} (hN : 8 ≤ N)
    (hanti : AntitoneOn (RHTower.logPowDivId m) (Set.Ici 8)) :
    ∀ K : ℕ, N ≤ K →
      harmonicLogMomentGap m N ≤ harmonicLogMomentGap m K ∧
        harmonicLogMomentGap m K ≤ harmonicLogMomentGap m N +
          (RHTower.logPowDivId m ((N + 1 : ℕ) : ℝ) -
            RHTower.logPowDivId m ((K + 1 : ℕ) : ℝ)) := by
  intro K hK
  induction K, hK using Nat.le_induction with
  | base => exact ⟨le_rfl, by simp⟩
  | succ K hNK ih =>
      obtain ⟨ih1, ih2⟩ := ih
      obtain ⟨hs1, hs2⟩ := harmonicLogMomentGap_step (le_trans hN hNK) hanti
      exact ⟨by linarith, by linarith⟩

/-- The gap is bounded above beyond the antitone threshold. -/
theorem harmonicLogMomentGap_bddAbove {m : ℕ}
    (hanti : AntitoneOn (RHTower.logPowDivId m) (Set.Ici 8)) :
    BddAbove (Set.range (fun K : ℕ => harmonicLogMomentGap m (K + 8))) := by
  refine ⟨harmonicLogMomentGap m 8 + RHTower.logPowDivId m ((8 + 1 : ℕ) : ℝ), ?_⟩
  rintro y ⟨K, rfl⟩
  obtain ⟨-, h2⟩ := harmonicLogMomentGap_range (m := m) (N := 8) le_rfl hanti (K + 8) (by omega)
  have hnn : 0 ≤ RHTower.logPowDivId m ((K + 8 + 1 : ℕ) : ℝ) := by
    refine logPowDivId_nonneg_of_eight_le ?_
    have : (8 : ℕ) ≤ K + 8 + 1 := by omega
    exact_mod_cast this
  linarith

/-- The `m`-th harmonic logarithmic moment constant, as the supremum of the increasing gaps. -/
def harmonicLogMomentConstant (m : ℕ) : ℝ :=
  ⨆ K : ℕ, harmonicLogMomentGap m (K + 8)

/-- **Two-sided approach to the harmonic logarithmic moment constant.** -/
theorem harmonicLogMomentGap_sub_constant_bounds {m N : ℕ} (hN : 8 ≤ N)
    (hanti : AntitoneOn (RHTower.logPowDivId m) (Set.Ici 8)) :
    0 ≤ harmonicLogMomentConstant m - harmonicLogMomentGap m N ∧
      harmonicLogMomentConstant m - harmonicLogMomentGap m N ≤
        RHTower.logPowDivId m ((N + 1 : ℕ) : ℝ) := by
  have hbdd := harmonicLogMomentGap_bddAbove (m := m) hanti
  have hNrepr : N = (N - 8) + 8 := by omega
  constructor
  · have := le_ciSup hbdd (N - 8)
    rw [harmonicLogMomentConstant]
    rw [hNrepr]
    linarith [this]
  · have hub : ∀ K : ℕ, harmonicLogMomentGap m (K + 8) ≤
        harmonicLogMomentGap m N + RHTower.logPowDivId m ((N + 1 : ℕ) : ℝ) := by
      intro K
      by_cases hcase : N ≤ K + 8
      · obtain ⟨-, h2⟩ := harmonicLogMomentGap_range hN hanti (K + 8) hcase
        have hnn : 0 ≤ RHTower.logPowDivId m ((K + 8 + 1 : ℕ) : ℝ) := by
          refine logPowDivId_nonneg_of_eight_le ?_
          have : (8 : ℕ) ≤ K + 8 + 1 := by omega
          exact_mod_cast this
        linarith
      · have hKN : K + 8 ≤ N := by omega
        obtain ⟨h1, -⟩ := harmonicLogMomentGap_range (m := m) (N := K + 8) (by omega) hanti N hKN
        have hnn : 0 ≤ RHTower.logPowDivId m ((N + 1 : ℕ) : ℝ) := by
          refine logPowDivId_nonneg_of_eight_le ?_
          have : (8 : ℕ) ≤ N + 1 := by omega
          exact_mod_cast this
        linarith
    have := ciSup_le hub
    rw [harmonicLogMomentConstant]
    linarith [this]

/-- The full constant of a harmonic logarithmic moment starting at the origin. -/
def harmonicLogMomentTotalConstant (m : ℕ) : ℝ :=
  harmonicLogWindowMoment m 0 8 + harmonicLogMomentConstant m

/-- **The harmonic logarithmic moment from the origin, with its constant and sharp error.** -/
theorem abs_harmonicLogWindowMoment_zeroStart_sub_le {m N : ℕ} (hN : 8 ≤ N)
    (hanti : AntitoneOn (RHTower.logPowDivId m) (Set.Ici 8)) :
    |harmonicLogWindowMoment m 0 N -
        (harmonicLogMomentPrimitive m ((N + 1 : ℕ) : ℝ) +
          harmonicLogMomentTotalConstant m)| ≤
      RHTower.logPowDivId m ((N + 1 : ℕ) : ℝ) := by
  have hsplit : harmonicLogWindowMoment m 0 N =
      harmonicLogWindowMoment m 0 8 + harmonicLogWindowMoment m 8 N := by
    rw [harmonicLogWindowMoment, harmonicLogWindowMoment, harmonicLogWindowMoment,
      Finset.sum_Ioc_consecutive _ (by omega : (0 : ℕ) ≤ 8) hN]
  obtain ⟨h1, h2⟩ := harmonicLogMomentGap_sub_constant_bounds hN hanti
  rw [hsplit, harmonicLogMomentTotalConstant]
  rw [abs_le]
  rw [harmonicLogMomentGap] at h1 h2
  constructor <;> linarith

/-- The plain harmonic sum from the origin. -/
theorem abs_harmonicLogWindowMoment_zeroStart_zero_sub_le {N : ℕ} (hN : 8 ≤ N) :
    |harmonicLogWindowMoment 0 0 N -
        (harmonicLogMomentPrimitive 0 ((N + 1 : ℕ) : ℝ) +
          harmonicLogMomentTotalConstant 0)| ≤
      RHTower.logPowDivId 0 ((N + 1 : ℕ) : ℝ) :=
  abs_harmonicLogWindowMoment_zeroStart_sub_le hN antitoneOn_logPowDivId_zero

/-- The first logarithmic moment from the origin. -/
theorem abs_harmonicLogWindowMoment_zeroStart_one_sub_le {N : ℕ} (hN : 8 ≤ N) :
    |harmonicLogWindowMoment 1 0 N -
        (harmonicLogMomentPrimitive 1 ((N + 1 : ℕ) : ℝ) +
          harmonicLogMomentTotalConstant 1)| ≤
      RHTower.logPowDivId 1 ((N + 1 : ℕ) : ℝ) :=
  abs_harmonicLogWindowMoment_zeroStart_sub_le hN antitoneOn_logPowDivId_one

/-- The second logarithmic moment from the origin. -/
theorem abs_harmonicLogWindowMoment_zeroStart_two_sub_le {N : ℕ} (hN : 8 ≤ N) :
    |harmonicLogWindowMoment 2 0 N -
        (harmonicLogMomentPrimitive 2 ((N + 1 : ℕ) : ℝ) +
          harmonicLogMomentTotalConstant 2)| ≤
      RHTower.logPowDivId 2 ((N + 1 : ℕ) : ℝ) :=
  abs_harmonicLogWindowMoment_zeroStart_sub_le hN antitoneOn_logPowDivId_two

end RHTower.Sieve

end
