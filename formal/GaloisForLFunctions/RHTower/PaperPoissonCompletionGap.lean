import GaloisForLFunctions.RHTower.PaperPoissonDiscretePort
import GaloisForLFunctions.RHTower.PaperPoissonNativeSource

/-!
# The continuum Poisson port is one unit from identity at every positive gap

The real-frequency port retains norm one but has no nonzero fixed vector at positive gap.
The sampled port has an undamped zero-frequency vector. This separates the completions at
the level of actual vectors as well as the proven paper ideal trace.
-/

namespace RHTower
noncomputable section
open MeasureTheory GaloisForLFunctions.HTGeometry Filter Classical
open scoped Topology ENNReal NNReal

theorem paperPoissonPort_sub_one_apply_ae (h d : ℝ≥0) (f : PaperPoissonSpace) :
    ((paperPoissonPort h d - 1) f : ℝ → ℂ) =ᵐ[volume]
      fun u => ((paperPoissonSymbol h d u : ℂ) - 1) * f u := by
  change ((paperPoissonPort h d f - f : PaperPoissonSpace) : ℝ → ℂ) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_sub (paperPoissonPort h d f) f,
    paperPoissonPort_apply_ae h d f] with u hs hu
  rw [hs, Pi.sub_apply, hu, sub_mul, one_mul]

/-- Every positive gap stays exactly one unit from identity in operator norm. -/
theorem norm_paperPoissonPort_sub_one (h d : ℝ≥0) :
    ‖paperPoissonPort h d - 1‖ = if d = 0 then 0 else 1 := by
  by_cases hd : d = 0
  · simp [hd]
  rw [if_neg hd]
  apply le_antisymm
  · exact norm_le_of_ae_mul zero_le_one (norm_paperPoissonSymbol_sub_one_le h d)
      (paperPoissonPort_sub_one_apply_ae h d)
  · have hm := Complex.continuous_ofReal.continuousAt.tendsto.comp
      (tendsto_paperPoissonSymbol_atTop h d)
    have hn := (hm.sub (tendsto_const_nhds (x := (1 : ℂ)))).norm
    simp only [if_neg hd, Complex.ofReal_zero, zero_sub, norm_neg, norm_one,
      Function.comp_apply] at hn
    apply le_of_tendsto' hn
    intro u
    exact norm_symbol_le_of_ae_mul_continuous
      ((Complex.continuous_ofReal.comp (continuous_paperPoissonSymbol h d)).sub continuous_const)
      (paperPoissonPort_sub_one_apply_ae h d) u

/-- This entire distance also survives passage to the compact quotient. -/
theorem compactIdealDistance_paperPoissonPort_sub_one (h d : ℝ≥0) :
    compactIdealDistance (paperPoissonPort h d - 1) = if d = 0 then 0 else 1 := by
  have hp := paperModulationCommutant_compactIdealDistance (paperPoissonPortCommutant h d - 1)
  change compactIdealDistance (paperPoissonPort h d - 1) = ‖paperPoissonPort h d - 1‖ at hp
  exact hp.trans (norm_paperPoissonPort_sub_one h d)

theorem paperPoissonPort_sub_one_compact_iff (h d : ℝ≥0) :
    IsCompactOperator (paperPoissonPort h d -
      (1 : PaperPoissonSpace →L[ℂ] PaperPoissonSpace)) ↔ d = 0 := by
  constructor
  · intro hc
    by_contra hd
    have hz := compactIdealDistance_eq_zero_of_isCompactOperator _ hc
    rw [compactIdealDistance_paperPoissonPort_sub_one, if_neg hd] at hz
    exact one_ne_zero hz
  · rintro rfl
    rw [paperPoissonPort_zero_gap, sub_self]
    change IsCompactOperator (0 : PaperPoissonSpace → PaperPoissonSpace)
    exact isCompactOperator_zero

theorem paperPoissonPort_sub_one_traceCost (h d : ℝ≥0) :
    compactOperatorTraceCost PaperPoissonSpace (paperPoissonPort h d - 1) =
      if d = 0 then 0 else ∞ := by
  rw [compactOperatorTraceCost_eq, paperPoissonPort_sub_one_compact_iff]
  split_ifs <;> rfl

/-- At positive gap, no nonzero continuum vector is exactly undamped. -/
theorem paperPoissonPort_fixed_iff (h d : ℝ≥0) (f : PaperPoissonSpace) :
    paperPoissonPort h d f = f ↔ d = 0 ∨ f = 0 := by
  constructor
  · intro hf
    by_cases hd : d = 0
    · exact Or.inl hd
    right
    have ha := paperPoissonPort_apply_ae h d f
    rw [hf] at ha
    apply Lp.ext
    filter_upwards [ha, volume.ae_ne (0 : ℝ), Lp.coeFn_zero ℂ 2 volume]
      with u hu hune hzero
    rw [hzero]
    have hm : (paperPoissonSymbol h d u : ℂ) - 1 ≠ 0 := by
      intro he
      have heR : paperPoissonSymbol h d u = 1 := by
        exact_mod_cast (sub_eq_zero.mp he)
      exact (not_or.mpr ⟨hd, hune⟩) ((paperPoissonSymbol_eq_one_iff h d u).1 heR)
    have he : ((paperPoissonSymbol h d u : ℂ) - 1) * f u = 0 := by
      rw [sub_mul, one_mul, ← hu, sub_self]
    exact (mul_eq_zero.mp he).resolve_left hm
  · rintro (rfl | rfl) <;> simp

/-- The whole discrete lattice has an actual undamped zero mode at every gap. -/
theorem paperPoissonDiscretePort_fixed_zero_mode (h d : ℝ≥0) :
    paperPoissonDiscretePort h d (HilbertSchmidt.lpBasis ℤ 0) =
      HilbertSchmidt.lpBasis ℤ 0 := by
  rw [paperPoissonDiscretePort_basis]
  simp only [Int.cast_zero, paperPoissonSymbol_zero_frequency, Complex.ofReal_one, one_smul]

/-- The actual horizon density and Xi density are distinct Hilbert-space vectors. -/
theorem paperCosineSourceProfile_horizon_ne_zero_depth :
    paperCosineSourceProfile (1 / 2) ≠ paperCosineSourceProfile 0 := by
  intro he
  have hf : paperPoissonPort 0 (1 / 2) (paperCosineSourceProfile (1 / 2)) =
      paperCosineSourceProfile (1 / 2) := by
    rw [paperPoissonPort_horizon_source, he]
  have hz := (paperPoissonPort_fixed_iff 0 (1 / 2) (paperCosineSourceProfile (1 / 2))).1 hf
  rcases hz with hd | hs
  · norm_num at hd
  · exact paperCosineSourceProfile_ne_zero _ hs

end
end RHTower
