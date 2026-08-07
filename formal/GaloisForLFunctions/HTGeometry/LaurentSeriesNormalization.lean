import Mathlib.RingTheory.LaurentSeries

/-!
# Projective normalization over a Laurent-series field

A finite vector over `K((T))` containing the coordinate `1` can be scaled so that every coordinate
lies in `K[[T]]` and one normalized coordinate is a unit.  This is the elementary valuative input
needed to turn absence of projective boundary points into integrality of affine solutions.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped LaurentSeries

theorem laurent_valuation_coe_powerSeries_eq_one_of_constantCoeff_ne_zero
    (K : Type*) [Field K] {f : PowerSeries K} (hf : PowerSeries.constantCoeff f ≠ 0) :
    Valued.v (f : K⸨X⸩) = 1 := by
  rw [LaurentSeries.valuation_def,
    ← LaurentSeries.coe_algebraMap]
  rw [IsDedekindDomain.HeightOneSpectrum.valuation_eq_one_iff_notMem]
  intro hmem
  have hdiv : PowerSeries.X ∣ f := by
    simpa [PowerSeries.idealX, Ideal.mem_span_singleton] using hmem
  exact hf (PowerSeries.X_dvd_iff.mp hdiv)

/-- A finite Laurent-series vector containing `1` admits a power-series normalization with a unit
coordinate. -/
theorem exists_laurent_powerSeries_normalization
    (K : Type*) [Field K] {ι : Type*} [Finite ι] [Nonempty ι]
    (v : ι → K⸨X⸩) (hone : ∃ i, v i = 1) :
    ∃ (c : K⸨X⸩) (_ : c ≠ 0) (w : ι → PowerSeries K) (i₀ : ι),
      v i₀ = c ∧
      (∀ i, (w i : K⸨X⸩) = v i / c) ∧
      w i₀ = 1 := by
  classical
  obtain ⟨i₀, hi₀⟩ := Finite.exists_max (fun i => Valued.v (v i))
  let c := v i₀
  have hvc : Valued.v c ≠ 0 := by
    obtain ⟨j, hj⟩ := hone
    have hle := hi₀ j
    rw [hj, map_one] at hle
    exact ne_of_gt (lt_of_lt_of_le zero_lt_one hle)
  have hc : c ≠ 0 := (Valuation.ne_zero_iff Valued.v).mp hvc
  have hint : ∀ i, Valued.v (v i / c) ≤ 1 := by
    intro i
    rw [Valuation.map_div]
    exact (div_le_one₀ (pos_iff_ne_zero.mpr hvc)).2 (hi₀ i)
  choose w hw using fun i => (LaurentSeries.val_le_one_iff_eq_coe K (v i / c)).mp (hint i)
  have hwi₀ : w i₀ = 1 := by
    apply (HahnSeries.ofPowerSeries_injective (Γ := ℤ))
    rw [hw i₀]
    simp [c, hc]
  exact ⟨c, hc, w, i₀, rfl, hw, hwi₀⟩

/-- If the distinguished affine coordinate remains nonzero after normalization, the scale has
valuation one; hence every original coordinate was already integral. -/
theorem laurent_all_val_le_one_of_normalized_coordinate
    (K : Type*) [Field K] {ι : Type*} [Finite ι] [Nonempty ι]
    {v : ι → K⸨X⸩} {a : ι} (ha : v a = 1)
    {c : K⸨X⸩} (_hc : c ≠ 0) {w : ι → PowerSeries K}
    (hmax : ∀ i, Valued.v (v i) ≤ Valued.v c)
    (hw : ∀ i, (w i : K⸨X⸩) = v i / c)
    (ha0 : PowerSeries.constantCoeff (w a) ≠ 0) :
    ∀ i, Valued.v (v i) ≤ 1 := by
  have hwval : Valued.v (w a : K⸨X⸩) = 1 :=
    laurent_valuation_coe_powerSeries_eq_one_of_constantCoeff_ne_zero K ha0
  have hcval : Valued.v c = 1 := by
    have h := congrArg Valued.v (hw a)
    rw [ha, Valuation.map_div, map_one] at h
    rw [hwval] at h
    rw [one_div] at h
    exact inv_eq_one.mp h.symm
  intro i
  simpa [hcval] using hmax i

end GaloisForLFunctions.HTGeometry
