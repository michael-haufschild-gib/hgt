import GaloisForLFunctions.RHTower.DeningerTraceBound

/-!
# The energy form is definite

The radial energy of a filling is nonnegative, and it vanishes only for the zero filling: a
vanishing integral of a nonnegative integrand forces the integrand to vanish almost everywhere, and
a continuous function vanishing almost everywhere on an open set vanishes there, because its
nonvanishing locus would be a nonempty open set of positive measure.

Definiteness is what makes the energy form an inner product on the filling core, hence what allows
its completion to be a Hilbert space.

* `deningerEnergy_nonneg` : the energy is nonnegative.
* `deningerEnergy_eq_zero` : a filling of zero energy vanishes.
-/

namespace RHTower

open MeasureTheory Set

section EnergyDefinite

variable {u v : ℝ → ℂ} {m : ℝ}

/-- **The energy is nonnegative.** -/
theorem deningerEnergy_nonneg :
    0 ≤ ∫ r in Ioi (0 : ℝ), (‖v r‖ ^ 2 + m ^ 2 * ‖u r‖ ^ 2) :=
  integral_nonneg fun r => by positivity

/-- **A filling of zero energy vanishes.**  The integrand is nonnegative, so it vanishes almost
everywhere; continuity then forces the filling to vanish on the whole half line. -/
theorem deningerEnergy_eq_zero (hm : m ≠ 0) (hcont : ContinuousOn u (Ioi (0 : ℝ)))
    (hint : IntegrableOn (fun r => ‖v r‖ ^ 2 + m ^ 2 * ‖u r‖ ^ 2) (Ioi (0 : ℝ)))
    (hzero : (∫ r in Ioi (0 : ℝ), (‖v r‖ ^ 2 + m ^ 2 * ‖u r‖ ^ 2)) = 0) :
    ∀ r ∈ Ioi (0 : ℝ), u r = 0 := by
  have hnonneg : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun r => ‖v r‖ ^ 2 + m ^ 2 * ‖u r‖ ^ 2 :=
    Filter.Eventually.of_forall fun r => by positivity
  have hae : (fun r => ‖v r‖ ^ 2 + m ^ 2 * ‖u r‖ ^ 2)
      =ᵐ[volume.restrict (Ioi (0 : ℝ))] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hnonneg hint).mp hzero
  -- the vanishing locus of `u` is almost all of the half line
  have hu_ae : ∀ᵐ r ∂(volume.restrict (Ioi (0 : ℝ))), u r = 0 := by
    filter_upwards [hae] with r hr
    have hr' : ‖v r‖ ^ 2 + m ^ 2 * ‖u r‖ ^ 2 = 0 := hr
    have h1 : (0 : ℝ) ≤ ‖v r‖ ^ 2 := by positivity
    have h2 : (0 : ℝ) ≤ m ^ 2 * ‖u r‖ ^ 2 := by positivity
    have h3 : m ^ 2 * ‖u r‖ ^ 2 = 0 := by linarith
    have hm2 : m ^ 2 ≠ 0 := pow_ne_zero 2 hm
    have h4 : ‖u r‖ ^ 2 = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · exact absurd h hm2
      · exact h
    have h5 : ‖u r‖ = 0 := by
      nlinarith [norm_nonneg (u r)]
    exact norm_eq_zero.mp h5
  -- a continuous function vanishing almost everywhere on an open set vanishes there
  intro r hr
  by_contra hne
  have hcontAt : ContinuousAt u r := hcont.continuousAt (isOpen_Ioi.mem_nhds hr)
  have hnbhd : {s : ℝ | u s ≠ 0} ∈ nhds r := hcontAt.eventually_ne hne
  have hnbhd2 : {s : ℝ | s ∈ Ioi (0 : ℝ) ∧ u s ≠ 0} ∈ nhds r :=
    Filter.inter_mem (isOpen_Ioi.mem_nhds hr) hnbhd
  have hpos : 0 < volume {s : ℝ | s ∈ Ioi (0 : ℝ) ∧ u s ≠ 0} := by
    refine lt_of_lt_of_le ?_ (measure_mono (interior_subset
      (s := {s : ℝ | s ∈ Ioi (0 : ℝ) ∧ u s ≠ 0})))
    exact isOpen_interior.measure_pos volume ⟨r, mem_interior_iff_mem_nhds.mpr hnbhd2⟩
  have hnull : volume {s : ℝ | s ∈ Ioi (0 : ℝ) ∧ u s ≠ 0} = 0 := by
    have h := (ae_restrict_iff' measurableSet_Ioi).mp hu_ae
    have hcompl : volume {s : ℝ | s ∈ Ioi (0 : ℝ) → u s = 0}ᶜ = 0 := mem_ae_iff.mp h
    refine measure_mono_null (fun s hs => ?_) hcompl
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_forall]
    exact ⟨hs.1, hs.2⟩
  rw [hnull] at hpos
  exact absurd hpos (lt_irrefl 0)

end EnergyDefinite

end RHTower
