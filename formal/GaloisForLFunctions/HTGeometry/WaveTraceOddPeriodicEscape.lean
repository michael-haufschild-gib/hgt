import GaloisForLFunctions.HTGeometry.WaveTraceConvexRecurrence

/-!
# Cofinal sign escape reduces to non-vanishing

The convex-recurrence law assumes cofinal sign escape: every nonzero polynomial weight drives its
wave trace strictly negative after every time.  That is a dynamical hypothesis, and nothing
produced it.

Half of it is free.  Every wave trace is an odd function of time, because the only time dependence
sits inside a sine and the polynomial factor depends on the frequency through its square.  So a
trace that is nonzero anywhere is negative somewhere.  Adding periodicity in time upgrades "somewhere"
to "after every time", and the whole dynamical hypothesis collapses to the static statement that no
nonzero polynomial weight has an identically vanishing trace.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Odd and periodic real functions -/

/-- An odd function that is nonzero somewhere is negative somewhere. -/
theorem exists_neg_of_odd {f : ℝ → ℝ} (hodd : ∀ t, f (-t) = -f t)
    {t₀ : ℝ} (hne : f t₀ ≠ 0) : ∃ t, f t < 0 := by
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨t₀, h⟩
  · refine ⟨-t₀, ?_⟩
    rw [hodd]
    linarith

/-- An odd periodic function that is nonzero somewhere is negative after every time. -/
theorem cofinal_neg_of_odd_periodic {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hodd : ∀ t, f (-t) = -f t) (hper : Function.Periodic f p)
    {t₀ : ℝ} (hne : f t₀ ≠ 0) (T : ℝ) :
    ∃ t, T < t ∧ f t < 0 := by
  obtain ⟨s, hs⟩ := exists_neg_of_odd hodd hne
  obtain ⟨k, hk⟩ := exists_nat_gt ((T - s) / p)
  refine ⟨s + k * p, ?_, ?_⟩
  · have hlt := (div_lt_iff₀ hp).mp hk
    linarith
  · rw [(hper.nat_mul k) s]
    exact hs

namespace WaveSpectrum

variable {G : Type*} (S : WaveSpectrum G)

/-! ## Every wave trace is odd in time -/

/-- Each trace term is odd in time: the only time dependence is inside a sine. -/
theorem traceTerm_neg (P : Polynomial ℝ) (t : ℝ) (g : G) :
    S.traceTerm P (-t) g = -S.traceTerm P t g := by
  rw [traceTerm, traceTerm]
  rw [show S.gamma g * ((-t : ℝ) : ℂ) = -(S.gamma g * (t : ℝ)) by push_cast; ring]
  rw [Complex.sin_neg]
  ring

/-- Hence the wave trace is odd in time. -/
theorem waveTrace_neg (P : Polynomial ℝ) (t : ℝ) :
    S.waveTrace P (-t) = -S.waveTrace P t := by
  rw [waveTrace, waveTrace, ← tsum_neg]
  exact tsum_congr fun g => S.traceTerm_neg P t g

/-- And so is the real wave trace. -/
theorem realWaveTrace_neg (P : Polynomial ℝ) (t : ℝ) :
    S.realWaveTrace P (-t) = -S.realWaveTrace P t := by
  rw [realWaveTrace, realWaveTrace, S.waveTrace_neg P t, Complex.neg_re]

/-! ## The reduction -/

/-- A nonzero trace is negative somewhere, with no periodicity needed. -/
theorem exists_realWaveTrace_neg (P : Polynomial ℝ) {t₀ : ℝ}
    (hne : S.realWaveTrace P t₀ ≠ 0) :
    ∃ t, S.realWaveTrace P t < 0 :=
  exists_neg_of_odd (S.realWaveTrace_neg P) hne

/-- **Cofinal sign escape is non-vanishing, for a time-periodic spectrum.**  If every wave trace is
periodic in time, then cofinal sign escape holds exactly when no nonzero polynomial weight has an
identically vanishing trace. -/
theorem cofinalWaveSignEscape_of_periodic_of_exists_ne_zero
    {p : ℝ} (hp : 0 < p)
    (hper : ∀ P : Polynomial ℝ, Function.Periodic (S.realWaveTrace P) p)
    (hne : ∀ P : Polynomial ℝ, P ≠ 0 → ∃ t, S.realWaveTrace P t ≠ 0) :
    S.CofinalWaveSignEscape := by
  intro P hP T
  obtain ⟨t₀, ht₀⟩ := hne P hP
  exact cofinal_neg_of_odd_periodic hp (S.realWaveTrace_neg P) (hper P) ht₀ T

/-- Conversely, cofinal sign escape forces every nonzero weight to have a nonvanishing trace, so
for a time-periodic spectrum the two conditions are equivalent. -/
theorem exists_ne_zero_of_cofinalWaveSignEscape
    (h : S.CofinalWaveSignEscape) (P : Polynomial ℝ) (hP : P ≠ 0) :
    ∃ t, S.realWaveTrace P t ≠ 0 := by
  obtain ⟨t, _, hlt⟩ := h P hP 0
  exact ⟨t, ne_of_lt hlt⟩

/-- The equivalence, for a time-periodic spectrum. -/
theorem cofinalWaveSignEscape_iff_of_periodic
    {p : ℝ} (hp : 0 < p)
    (hper : ∀ P : Polynomial ℝ, Function.Periodic (S.realWaveTrace P) p) :
    S.CofinalWaveSignEscape ↔
      ∀ P : Polynomial ℝ, P ≠ 0 → ∃ t, S.realWaveTrace P t ≠ 0 :=
  ⟨fun h => S.exists_ne_zero_of_cofinalWaveSignEscape h,
    fun hne => S.cofinalWaveSignEscape_of_periodic_of_exists_ne_zero hp hper hne⟩

end WaveSpectrum

end

end GaloisForLFunctions.HTGeometry
