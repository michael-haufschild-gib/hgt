import GaloisForLFunctions.RHTower.Sieve.TwistedSeriesAsDirichletPoly
import GaloisForLFunctions.RHTower.Sieve.HalaszUniformDistance

/-!
# The mean-square estimate with the damped sup

The corpus's Halász mean-value bound takes a sup over *all* frequencies, while the Euler damping supplies
a sup only on the range `|t| ≤ T` that carries a uniform distance bound.  Weakening the hypothesis to the
range is enough: the proof only evaluates the sup inside the integral.

With that, the truncated twisted series can be fed its own damped sup rather than the trivial
`∑|aₙ| ≍ log L`:

`∫₀^T ‖F_L‖ ≤ V·T + (damped + L^{1-σ}/(σ−1))·(T + 4L(1+log L))·∑|aₙ|² / V²`.

This is the mean-square input whose absence bounds the pointwise route: the second term now carries the
`e^{-δ²}` saving, and `∑|aₙ|²` is `O(1)` rather than `log²L`.
-/

namespace RHTower.Sieve

open MeasureTheory Set Complex

/-- **The sup hypothesis only has to hold on the range.**  Range-restricted form of
`integral_norm_dirPoly_le_of_sup`. -/
theorem integral_norm_dirPoly_le_of_sup_on (N : ℕ) (a : Fin N → ℂ) {T V M : ℝ} (hT : 0 ≤ T)
    (hV : 0 ≤ V)
    (hM : ∀ t ∈ Set.Ioc (0 : ℝ) T, ‖dirPoly N a t‖ ≤ M) :
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
    intro t ht
    simp only [Pi.add_apply]
    by_cases h : V ≤ ‖dirPoly N a t‖
    · rw [Set.indicator_of_mem (show t ∈ {t : ℝ | V ≤ ‖dirPoly N a t‖} from h)]
      have := hM t ht
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

/-- **The Halász mean-value bound with a range-restricted sup.** -/
theorem integral_norm_dirPoly_halasz_on (N : ℕ) (a : Fin N → ℂ) {T V M : ℝ} (hT : 0 ≤ T)
    (hV : 0 < V) (hM0 : 0 ≤ M)
    (hM : ∀ t ∈ Set.Ioc (0 : ℝ) T, ‖dirPoly N a t‖ ≤ M) :
    ∫ t in Set.Ioc (0 : ℝ) T, ‖dirPoly N a t‖
      ≤ V * T
        + M * ((T + 4 * (N : ℝ) * (1 + Real.log N)) * ∑ m : Fin N, ‖a m‖ ^ 2) / V ^ 2 := by
  have hV2 : (0 : ℝ) < V ^ 2 := by positivity
  have hlev := volume_largeValues_le N a hT hV.le
  have hmeas : volume.real {t ∈ Set.Ioc (0 : ℝ) T | V ≤ ‖dirPoly N a t‖}
      ≤ ((T + 4 * (N : ℝ) * (1 + Real.log N)) * ∑ m : Fin N, ‖a m‖ ^ 2) / V ^ 2 := by
    rw [le_div_iff₀ hV2]
    linarith [hlev]
  refine le_trans (integral_norm_dirPoly_le_of_sup_on N a hT hV.le hM) ?_
  have hstep := mul_le_mul_of_nonneg_left hmeas hM0
  have hdiv : M * (((T + 4 * (N : ℝ) * (1 + Real.log N)) * ∑ m : Fin N, ‖a m‖ ^ 2) / V ^ 2)
      = M * ((T + 4 * (N : ℝ) * (1 + Real.log N)) * ∑ m : Fin N, ‖a m‖ ^ 2) / V ^ 2 := by
    ring
  linarith [hdiv ▸ hstep]

section

variable {f : ℕ → ℂ}

/-- **The mean-square estimate for a bounded multiplicative series, with the damped sup.**  The sup on
the range is the Euler-damped size plus the truncation error, so the second term carries the `e^{-δ²}`
saving that the trivial sup cannot. -/
theorem integral_norm_dirPoly_twisted_halasz
    (hf1 : f 1 = 1) (hmul : ∀ {m n : ℕ}, Nat.Coprime m n → f (m * n) = f m * f n)
    (hbdd : ∀ n, ‖f n‖ ≤ 1) (hf0 : f 0 = 0)
    {σ : ℝ} (hσ : 1 < σ) {z : ℕ} (hz : 1 ≤ z) {δ : ℝ} (hδ : 0 ≤ δ)
    {L : ℕ} (hL : 1 ≤ L) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 < V)
    (hunif : ∀ t : ℝ, |t| ≤ T →
      δ ≤ Real.sqrt (mulDistSqPair f (charFn t) (Nat.primesLE z))) :
    ∫ u in Set.Ioc (0 : ℝ) T, ‖dirPoly L (twistedTruncCoeff f σ L) u‖
      ≤ V * T
        + ((1 + 1 / (σ - 1)) *
              Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2)
            + ((L : ℝ)) ^ (1 - σ) / (σ - 1))
          * ((T + 4 * (L : ℝ) * (1 + Real.log L)) *
              ∑ m : Fin L, ‖twistedTruncCoeff f σ L m‖ ^ 2) / V ^ 2 := by
  set damped : ℝ := (1 + 1 / (σ - 1)) *
    Real.exp (7 / 2 + 2 * (σ - 1) * (Real.log z + Real.log 4) - δ ^ 2) with hdamped
  set trunc : ℝ := ((L : ℝ)) ^ (1 - σ) / (σ - 1) with htrunc
  have hσ1 : (0 : ℝ) < σ - 1 := by linarith
  have hdamped0 : 0 ≤ damped := by
    rw [hdamped]
    positivity
  have htrunc0 : 0 ≤ trunc := by
    rw [htrunc]
    have hL0 : (0 : ℝ) ≤ ((L : ℕ) : ℝ) := Nat.cast_nonneg L
    positivity
  refine integral_norm_dirPoly_halasz_on L (twistedTruncCoeff f σ L) hT hV
    (by linarith) (fun u hu => ?_)
  -- the truncated series at frequency `u` is the twisted series at `-u`
  have hid : ∑ n ∈ Finset.range (L + 1),
      twistedSummand f (((σ : ℝ) : ℂ) + (((-u : ℝ)) : ℂ) * Complex.I) n
      = dirPoly L (twistedTruncCoeff f σ L) u := by
    rw [sum_range_twistedSummand_eq_dirPoly hf0 σ (-u) L, neg_neg]
  have hsre : (1 : ℝ) < (((σ : ℝ) : ℂ) + (((-u : ℝ)) : ℂ) * Complex.I).re := by
    rw [re_ofReal_add_mul_I]
    exact hσ
  have habs : |(-u : ℝ)| ≤ T := by
    rw [abs_neg, abs_of_pos hu.1]
    exact hu.2
  have hfull : ‖∑' n : ℕ,
      twistedSummand f (((σ : ℝ) : ℂ) + (((-u : ℝ)) : ℂ) * Complex.I) n‖ ≤ damped :=
    norm_tsum_twistedSummand_le_damped_of_uniform hf1 hmul hbdd hσ hz hδ hunif habs
  have htail : ‖(∑' n : ℕ,
        twistedSummand f (((σ : ℝ) : ℂ) + (((-u : ℝ)) : ℂ) * Complex.I) n) -
      ∑ n ∈ Finset.range (L + 1),
        twistedSummand f (((σ : ℝ) : ℂ) + (((-u : ℝ)) : ℂ) * Complex.I) n‖ ≤ trunc := by
    have h := norm_tsum_sub_sum_range_le_pow hbdd hsre hL
    rwa [re_ofReal_add_mul_I] at h
  rw [← hid]
  have hsplit := norm_sub_le
    (∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + (((-u : ℝ)) : ℂ) * Complex.I) n)
    ((∑' n : ℕ, twistedSummand f (((σ : ℝ) : ℂ) + (((-u : ℝ)) : ℂ) * Complex.I) n) -
      ∑ n ∈ Finset.range (L + 1),
        twistedSummand f (((σ : ℝ) : ℂ) + (((-u : ℝ)) : ℂ) * Complex.I) n)
  rw [sub_sub_cancel] at hsplit
  linarith

end

end RHTower.Sieve
