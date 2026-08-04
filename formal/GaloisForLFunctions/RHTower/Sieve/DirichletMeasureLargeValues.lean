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

/-- The trivial sup bound: a Dirichlet polynomial is at most the `ℓ¹` norm of its coefficients. -/
theorem norm_dirPoly_le_sum_norm (N : ℕ) (a : Fin N → ℂ) (t : ℝ) :
    ‖dirPoly N a t‖ ≤ ∑ m : Fin N, ‖a m‖ := by
  refine le_trans (norm_sum_le _ _) (le_of_eq (Finset.sum_congr rfl ?_))
  intro m _
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one]

/-- **The small values are handled by the threshold, the large ones by the sup.**  Splitting the
frequency range at `V` costs `V·T` on the small side and `M` times the measure of the level set on
the large one. -/
theorem integral_norm_dirPoly_le_of_sup (N : ℕ) (a : Fin N → ℂ) {T V M : ℝ} (hT : 0 ≤ T)
    (hV : 0 ≤ V) (hM : ∀ t : ℝ, ‖dirPoly N a t‖ ≤ M) :
    ∫ t in Set.Ioc (0 : ℝ) T, ‖dirPoly N a t‖
      ≤ V * T + M * volume.real {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖} := by
  classical
  have hFc : Continuous fun t : ℝ => ‖dirPoly N a t‖ := (continuous_dirPoly N a).norm
  have hlev : MeasurableSet {t : ℝ | V ≤ ‖dirPoly N a t‖} :=
    measurableSet_le measurable_const hFc.measurable
  have hIocm : MeasurableSet (Set.Ioc (0 : ℝ) T) := measurableSet_Ioc
  have hIocfin : volume (Set.Ioc (0 : ℝ) T) ≠ ⊤ := by simp
  have hconst : IntegrableOn (fun _ : ℝ => V) (Set.Ioc (0 : ℝ) T) :=
    integrableOn_const hIocfin (by simp)
  have hindint : IntegrableOn (Set.indicator {t : ℝ | V ≤ ‖dirPoly N a t‖} fun _ : ℝ => M)
      (Set.Ioc (0 : ℝ) T) :=
    (integrableOn_const (s := Set.Ioc (0 : ℝ) T) (μ := volume) (C := M) hIocfin
      (by simp)).indicator hlev
  have hbound : ∀ t ∈ Set.Ioc (0 : ℝ) T, ‖dirPoly N a t‖
      ≤ ((fun _ : ℝ => V) + Set.indicator {t : ℝ | V ≤ ‖dirPoly N a t‖} fun _ : ℝ => M) t := by
    intro t _
    simp only [Pi.add_apply]
    by_cases h : V ≤ ‖dirPoly N a t‖
    · rw [Set.indicator_of_mem (show t ∈ {t : ℝ | V ≤ ‖dirPoly N a t‖} from h)]
      have := hM t
      linarith
    · rw [Set.indicator_of_notMem (show t ∉ {t : ℝ | V ≤ ‖dirPoly N a t‖} from h)]
      simp only [add_zero]
      exact le_of_lt (not_le.1 h)
  have hstep := setIntegral_mono_on hFc.integrableOn_Ioc (hconst.add hindint) hIocm hbound
  simp only [Pi.add_apply] at hstep
  rw [MeasureTheory.integral_add hconst hindint, setIntegral_const,
    setIntegral_indicator hlev, setIntegral_const] at hstep
  have hvol : volume.real (Set.Ioc (0 : ℝ) T) = T := by
    rw [measureReal_def, Real.volume_Ioc, ENNReal.toReal_ofReal (by linarith)]
    ring
  have hinter : Set.Ioc (0 : ℝ) T ∩ {t : ℝ | V ≤ ‖dirPoly N a t‖}
      = {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖} := rfl
  rw [hvol, hinter, smul_eq_mul, smul_eq_mul, mul_comm T V, mul_comm _ M] at hstep
  exact hstep

/-- **The mean-value form of the Halász bound.**  A uniform sup `M` on a Dirichlet polynomial and the
mean value theorem together bound its first moment: for every threshold `V > 0`,

    ∫₀^T |F| ≤ V·T + M·(T + 4N(1 + log N))·∑|a_n|² / V².

Only the *measure* of the large-value set is used, so no spacing hypothesis and no pointwise decay
at an individual frequency is needed. -/
theorem integral_norm_dirPoly_halasz (N : ℕ) (a : Fin N → ℂ) {T V M : ℝ} (hT : 0 ≤ T) (hV : 0 < V)
    (hM : ∀ t : ℝ, ‖dirPoly N a t‖ ≤ M) :
    ∫ t in Set.Ioc (0 : ℝ) T, ‖dirPoly N a t‖
      ≤ V * T
        + M * ((T + 4 * (N : ℝ) * (1 + Real.log N)) * ∑ m : Fin N, ‖a m‖ ^ 2) / V ^ 2 := by
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  have hV2 : (0 : ℝ) < V ^ 2 := by positivity
  have hlev := volume_largeValues_le N a hT hV.le
  have hmeas : volume.real {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖}
      ≤ ((T + 4 * (N : ℝ) * (1 + Real.log N)) * ∑ m : Fin N, ‖a m‖ ^ 2) / V ^ 2 := by
    rw [le_div_iff₀ hV2]
    linarith [hlev]
  refine le_trans (integral_norm_dirPoly_le_of_sup N a hT hV.le hM) ?_
  have := mul_le_mul_of_nonneg_left hmeas hM0
  have hdiv : M * (((T + 4 * (N : ℝ) * (1 + Real.log N)) * ∑ m : Fin N, ‖a m‖ ^ 2) / V ^ 2)
      = M * ((T + 4 * (N : ℝ) * (1 + Real.log N)) * ∑ m : Fin N, ‖a m‖ ^ 2) / V ^ 2 := by
    ring
  linarith [hdiv ▸ this]

/-- **The mean-value form of the Halász bound with no free sup.**  Taking the trivial sup
`‖F‖ ≤ ∑|a_n|` leaves a statement in the coefficients alone:

    ∫₀^T |F| ≤ V·T + (∑|a_n|)·(T + 4N(1 + log N))·∑|a_n|² / V². -/
theorem integral_norm_dirPoly_halasz_l1 (N : ℕ) (a : Fin N → ℂ) {T V : ℝ} (hT : 0 ≤ T)
    (hV : 0 < V) :
    ∫ t in Set.Ioc (0 : ℝ) T, ‖dirPoly N a t‖
      ≤ V * T
        + (∑ m : Fin N, ‖a m‖)
            * ((T + 4 * (N : ℝ) * (1 + Real.log N)) * ∑ m : Fin N, ‖a m‖ ^ 2) / V ^ 2 :=
  integral_norm_dirPoly_halasz N a hT hV (norm_dirPoly_le_sum_norm N a)

end RHTower.Sieve
