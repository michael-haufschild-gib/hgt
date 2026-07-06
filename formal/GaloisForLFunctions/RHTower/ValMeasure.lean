import GaloisForLFunctions.RHTower.ValuationProfile

/-!
# The depth profile and the valuation atomic measure

The window depth `windowDepth T` — the minimal 2-adic valuation of the enclosed jumps — is a
**monotone-decreasing `ℕ∞`-valued step function** of the height: enclosing more zeros can only lower
the minimal valuation.  It descends exactly at the low-valuation heights, stays `⊤` precisely while
the window is zero-free (equivalently, while the full rung tower holds), and it envelops the census:
below the depth the census profile vanishes mod `2^k`.

The **valuation atomic measure** `valMeasure T = ∑_t v₂(discJump t) · δ_t` weights each enclosed zero
height by its 2-adic valuation.  It is a genuine finite measure on ℝ whose total mass is the
valuation content `valMass T`, whose atoms sit on the off-line heights, and whose minimal atom is the
window depth.  The off-line heights `{t | discJump t ≠ 0}` are exactly the RH-forbidden locus: RH
holds iff they are empty.
-/

namespace RHTower

open Complex Set Metric MeasureTheory
open scoped ENNReal

/-! ## (a) The depth profile -/

/-- **The depth profile is monotone-decreasing.**  Raising the height encloses more zero heights, so
the minimal filtration length can only fall. -/
theorem windowDepth_antitone {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : windowDepth T₂ ≤ windowDepth T₁ :=
  Finset.inf_mono (Finset.image_subset_image (boxFinset_subset h))

/-- **Descent points are the low-valuation heights.**  The depth drops below a natural number `n`
exactly when the window encloses a zero whose filtration length is below `n`. -/
theorem windowDepth_lt_iff {T : ℝ} {n : ℕ} :
    windowDepth T < (n : ℕ∞) ↔ ∃ z ∈ boxZeros T, filtrationLength z.im < n := by
  rw [windowDepth, Finset.inf_lt_iff]
  constructor
  · rintro ⟨t, ht, hlt⟩
    obtain ⟨z, hz, hzt⟩ := Finset.mem_image.mp ht
    exact ⟨z, mem_boxFinset.mp hz, hzt ▸ by exact_mod_cast hlt⟩
  · rintro ⟨z, hz, hlt⟩
    exact ⟨z.im, Finset.mem_image_of_mem _ (mem_boxFinset.mpr hz), by exact_mod_cast hlt⟩

theorem image_im_eq_empty_iff (T : ℝ) :
    (boxFinset T).image Complex.im = ∅ ↔ boxZeros T = ∅ := by
  rw [Finset.image_eq_empty, boxFinset, Set.Finite.toFinset_eq_empty]

/-- **The depth stays `⊤` exactly while the window is zero-free.** -/
theorem windowDepth_eq_top_iff (T : ℝ) : windowDepth T = ⊤ ↔ boxZeros T = ∅ := by
  rw [← image_im_eq_empty_iff, ← Finset.not_nonempty_iff_eq_empty, ← windowDepth_lt_top_iff,
    not_lt, top_le_iff]

/-- **Staying `⊤` past `T` is the full rung tower through `T`.** -/
theorem windowDepth_eq_top_iff_forall_windowCertificate (T : ℝ) :
    windowDepth T = ⊤ ↔ ∀ k, WindowCertificate k T := by
  rw [windowDepth_eq_top_iff]
  exact (forall_windowCertificate_iff_boxZeros_empty T).symm

/-- Each enclosed atom's valuation is at least the window depth. -/
theorem windowDepth_le_filtrationLength {T t : ℝ}
    (ht : t ∈ (boxFinset T).image Complex.im) :
    windowDepth T ≤ (filtrationLength t : ℕ∞) :=
  Finset.inf_le ht

/-- The census vanishes on a window through every level below the depth: if `V k T = 0` then the
level-`k` census is zero. -/
theorem discCensusH_eq_zero_of_V_eq_zero {k : ℕ} {T : ℝ} (h : V k T = 0) :
    discCensusH k T = 0 := by
  haveI : NeZero (2 ^ k) := ⟨pow_ne_zero k two_ne_zero⟩
  rw [discCensusH, ZMod.natCast_eq_zero_iff, boxOrderSum_eq_sum_discJump]
  rw [V_eq_zero_iff] at h
  refine Finset.dvd_sum (fun t ht => ?_)
  obtain ⟨z, hz, hzt⟩ := Finset.mem_image.mp ht
  rw [← hzt]
  exact h z (mem_boxFinset.mp hz)

/-- **The depth envelops the census profile.**  While `k` is at most the window depth, the level-`k`
census is zero: the depth is the height to which the census stays trivial. -/
theorem discCensusH_eq_zero_of_le_windowDepth {k : ℕ} {T : ℝ}
    (h : (k : ℕ∞) ≤ windowDepth T) : discCensusH k T = 0 :=
  discCensusH_eq_zero_of_V_eq_zero ((V_eq_zero_iff_le_windowDepth k T).mpr h)

/-! ## (b) The valuation atomic measure -/

/-- **The valuation content**: the total 2-adic valuation of the enclosed jumps — the atomic
measure's mass on the window `[0, T)`, refining the Stieltjes content by valuation weights in place
of the jump size mod `2^k`. -/
noncomputable def valMass (T : ℝ) : ℕ :=
  ∑ t ∈ (boxFinset T).image Complex.im, filtrationLength t

theorem valMass_mono {T₁ T₂ : ℝ} (h : T₁ ≤ T₂) : valMass T₁ ≤ valMass T₂ :=
  Finset.sum_le_sum_of_subset (Finset.image_subset_image (boxFinset_subset h))

/-- A zero-free window has zero valuation mass. -/
theorem valMass_eq_zero_of_windowDepth_top {T : ℝ} (h : windowDepth T = ⊤) : valMass T = 0 := by
  rw [windowDepth_eq_top_iff, ← image_im_eq_empty_iff] at h
  rw [valMass, h, Finset.sum_empty]

/-- **The valuation atomic measure** `∑_t v₂(discJump t) · δ_t` over the enclosed zero heights. -/
noncomputable def valMeasure (T : ℝ) : Measure ℝ :=
  ∑ t ∈ (boxFinset T).image Complex.im, (filtrationLength t : ℝ≥0∞) • Measure.dirac t

/-- The total mass of the valuation measure is the valuation content. -/
theorem valMeasure_univ (T : ℝ) : valMeasure T Set.univ = (valMass T : ℝ≥0∞) := by
  rw [valMeasure]
  simp only [Measure.finsetSum_apply, Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
  rw [valMass, Nat.cast_sum]

/-- **The valuation measure is a finite measure** — a finite atomic combination on a window. -/
instance isFiniteMeasure_valMeasure (T : ℝ) : IsFiniteMeasure (valMeasure T) :=
  ⟨by rw [valMeasure_univ]; exact ENNReal.natCast_lt_top _⟩

/-! ## The off-line locus: the RH-forbidden heights -/

/-- **The off-line heights**: the heights carrying a box (off critical line) ξ-zero — where the jump
divisor is nonzero, equivalently where the valuation profile is finite. -/
def offLineHeights : Set ℝ := {t : ℝ | discJump t ≠ 0}

theorem offLineHeights_eq_valProfile_ne_top : offLineHeights = {t : ℝ | valProfile t ≠ ⊤} := by
  ext t
  rw [offLineHeights, Set.mem_setOf_eq, Set.mem_setOf_eq, ne_eq, ne_eq, valProfile_eq_top_iff]

/-- The atoms of the valuation measure lie on the off-line heights. -/
theorem image_im_subset_offLineHeights (T : ℝ) :
    ↑((boxFinset T).image Complex.im) ⊆ offLineHeights := by
  intro t ht
  obtain ⟨z, hz, hzt⟩ := Finset.mem_image.mp (Finset.mem_coe.mp ht)
  rw [offLineHeights, Set.mem_setOf_eq, ← hzt]
  exact discJump_ne_zero_of_mem_boxZeros (mem_boxFinset.mp hz)

/-- **RH is the emptiness of the off-line locus.**  The Riemann Hypothesis holds iff no height
carries an off-line ξ-zero — the atoms of the valuation measure vanish at every level. -/
theorem rh_iff_offLineHeights_empty : RiemannHypothesis ↔ offLineHeights = ∅ := by
  rw [rh_iff_forall_discJump_eq_zero, offLineHeights, Set.eq_empty_iff_forall_notMem]
  exact forall_congr' fun t => by rw [Set.mem_setOf_eq, not_not]

end RHTower
