import GaloisForLFunctions.RHTower.Sieve.DirichletIntegralMeanValue

/-!
# The measure of the large values of a Dirichlet polynomial

The corpus bounds the number of *well-spaced* points at which a Dirichlet polynomial is large.  The
form an averaging argument consumes is the Lebesgue measure of the whole level set: Chebyshev's
inequality applied to the integral mean value theorem gives, for `F(t) = ∑_{n ≤ N} a_n n^{it}`,

    V² · |{t ∈ (0, T] : |F(t)| ≥ V}|  ≤  (T + 4N(1 + log N)) ∑_{n ≤ N} |a_n|².

No spacing hypothesis and no choice of test points enter: the level set is measured directly.  This
is the estimate that replaces a pointwise bound when the pointwise bound cannot decay — the measure
of the exceptional frequencies is small even where their number cannot be controlled one by one.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

/-- **The level set of a Dirichlet polynomial has small measure.**  Chebyshev's inequality applied
to the integral mean value theorem. -/
theorem volume_largeValues_le (N : ℕ) (a : Fin N → ℂ) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V) :
    V ^ 2 * volume.real {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖}
      ≤ (T + 4 * (N : ℝ) * (1 + Real.log N)) * ∑ m : Fin N, ‖a m‖ ^ 2 := by
  classical
  set S : ℝ := ∑ m : Fin N, ‖a m‖ ^ 2 with hS
  set g : ℝ → ℝ := fun t => ‖dirPoly N a t‖ ^ 2 with hg
  have hgc : Continuous g := ((continuous_dirPoly N a).norm).pow 2
  have hint : IntegrableOn g (Set.Ioc (0 : ℝ) T) := hgc.integrableOn_Ioc
  -- the mean value theorem, in real form
  have hA : ∫ t in Set.Ioc (0 : ℝ) T, g t ≤ T * S + 4 * (N : ℝ) * (1 + Real.log N) * S := by
    have hcorp := norm_integral_normSq_dirPoly_sub_diag_le_log N a T
    rw [show (fun t : ℝ => ((‖dirPoly N a t‖ ^ 2 : ℝ) : ℂ)) = fun t : ℝ => ((g t : ℝ) : ℂ) from rfl]
      at hcorp
    rw [intervalIntegral.integral_ofReal, ← Complex.ofReal_sum, ← hS, ← Complex.ofReal_mul,
      ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hcorp
    have hbound := (abs_le.1 hcorp).2
    rw [← intervalIntegral.integral_of_le hT]
    linarith
  -- Chebyshev
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc (0 : ℝ) T)] g :=
    Filter.Eventually.of_forall fun t => by positivity
  have hmark := MeasureTheory.mul_meas_ge_le_integral_of_nonneg hnn hint (V ^ 2)
  -- the level set of `F` sits inside the level set of `g`
  have hmeas : MeasurableSet {x : ℝ | V ^ 2 ≤ g x} :=
    measurableSet_le measurable_const hgc.measurable
  have hsub : {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖}
      ⊆ {x : ℝ | V ^ 2 ≤ g x} ∩ Set.Ioc (0 : ℝ) T := by
    rintro t ⟨ht, hle⟩
    exact ⟨by simpa [hg] using pow_le_pow_left₀ hV hle 2, ht⟩
  have hfin : volume ({x : ℝ | V ^ 2 ≤ g x} ∩ Set.Ioc (0 : ℝ) T) ≠ ⊤ :=
    ne_top_of_le_ne_top (by simp [Real.volume_Ioc]) (measure_mono Set.inter_subset_right)
  have hmono : volume.real {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖}
      ≤ (volume.restrict (Set.Ioc (0 : ℝ) T)).real {x : ℝ | V ^ 2 ≤ g x} := by
    rw [measureReal_restrict_apply hmeas]
    exact measureReal_mono hsub hfin
  have hVsq : (0 : ℝ) ≤ V ^ 2 := by positivity
  calc V ^ 2 * volume.real {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖}
      ≤ V ^ 2 * (volume.restrict (Set.Ioc (0 : ℝ) T)).real {x : ℝ | V ^ 2 ≤ g x} :=
        mul_le_mul_of_nonneg_left hmono hVsq
    _ ≤ ∫ t in Set.Ioc (0 : ℝ) T, g t := hmark
    _ ≤ T * S + 4 * (N : ℝ) * (1 + Real.log N) * S := hA
    _ = (T + 4 * (N : ℝ) * (1 + Real.log N)) * S := by ring

/-- The same bound on the closed interval: the endpoint is a null set. -/
theorem volume_largeValues_Icc_le (N : ℕ) (a : Fin N → ℂ) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 ≤ V) :
    V ^ 2 * volume.real {t ∈ Set.Icc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖}
      ≤ (T + 4 * (N : ℝ) * (1 + Real.log N)) * ∑ m : Fin N, ‖a m‖ ^ 2 := by
  classical
  have hsub : {t ∈ Set.Icc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖}
      ⊆ {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖} ∪ {(0 : ℝ)} := by
    rintro t ⟨⟨ht0, htT⟩, hle⟩
    rcases eq_or_lt_of_le ht0 with h | h
    · exact Or.inr (by simp [← h])
    · exact Or.inl ⟨⟨h, htT⟩, hle⟩
  have hle : volume {t ∈ Set.Icc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖}
      ≤ volume {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖} := by
    refine le_trans (measure_mono hsub) ?_
    refine le_trans (measure_union_le _ _) ?_
    simp
  have hIoc : volume (Set.Ioc (0 : ℝ) T) ≠ ⊤ := by simp
  have hfin : volume {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖} ≠ ⊤ :=
    ne_top_of_le_ne_top hIoc (measure_mono (Set.sep_subset (Set.Ioc (0 : ℝ) T) _))
  have hreal : volume.real {t ∈ Set.Icc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖}
      ≤ volume.real {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖} := by
    rw [measureReal_def, measureReal_def]
    exact ENNReal.toReal_mono hfin hle
  have hVsq : (0 : ℝ) ≤ V ^ 2 := by positivity
  exact le_trans (mul_le_mul_of_nonneg_left hreal hVsq) (volume_largeValues_le N a hT hV)

end RHTower.Sieve
