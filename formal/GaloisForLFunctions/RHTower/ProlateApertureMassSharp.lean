import GaloisForLFunctions.RHTower.ProlateBandAmplitudeAnchor

/-!
# The aperture mass without the turning-layer prefactor

The corpus's uniform aperture envelope pays `c / sqrt s` for crossing the turning layer.  The
amplitude envelope crosses it for free: on the allowed interval `[0, y₀]` with `y₀² ≤ 4s` the
constant scale `K = c² s` matches the potential, so

```text
|1/p − Q/K|  =  1/(1−y²) − 1 + y²/s  ∈  [0, 5] ,     sqrt K = c sqrt s ,
```

and the envelope costs `exp(5 c sqrt s · y₀) = exp(O(c s))` — a constant for a fixed mode.  At the
matching point the two scales differ by the bounded factor `(y₀² − s)(1 − y₀²)/s ≤ 3`, so the
allowed amplitude passes into the band amplitude, and from there the band transport and the
loss-free endpoint bound cover the rest of the aperture.

The result is a pointwise envelope for `Phi²` on the whole aperture whose only `c`-dependence is the
sharp exponential and the scale ratio.
-/

noncomputable section

open Set MeasureTheory

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

open GaloisForLFunctions.HTGeometry

/-! ## The allowed interval -/

/-- At the matching point the constant scale `c² s` and the band scale differ by a bounded factor. -/
theorem sturmAmplitude_const_le_three_mul_band {c s y₀ : ℝ} {Φ DΦ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 < s) (hsy0 : s < y₀ ^ (2 : ℕ)) (hy0h : y₀ ^ (2 : ℕ) ≤ 1 / 2)
    (hratio : (y₀ ^ (2 : ℕ) - s) * (1 - y₀ ^ (2 : ℕ)) ≤ 3 * s) :
    sturmAmplitude (fun t => 1 - t ^ (2 : ℕ)) Φ DΦ (c ^ (2 : ℕ) * s) y₀
      ≤ 3 * prolateBandAmplitude c s Φ DΦ y₀ := by
  have hc2 : (0 : ℝ) < c ^ (2 : ℕ) := by positivity
  have h1 : (0 : ℝ) < y₀ ^ (2 : ℕ) - s := by linarith
  have h2 : (0 : ℝ) < 1 - y₀ ^ (2 : ℕ) := by linarith
  have hKb : prolateBandScale c s y₀ = c ^ (2 : ℕ) * ((y₀ ^ (2 : ℕ) - s) * (1 - y₀ ^ (2 : ℕ))) := by
    rw [prolateBandScale]; ring
  have hKbpos : (0 : ℝ) < c ^ (2 : ℕ) * ((y₀ ^ (2 : ℕ) - s) * (1 - y₀ ^ (2 : ℕ))) := by positivity
  have hcs : (0 : ℝ) < c ^ (2 : ℕ) * s := by positivity
  have hF : (0 : ℝ) ≤ ((1 - y₀ ^ (2 : ℕ)) * DΦ y₀) ^ (2 : ℕ) := sq_nonneg _
  have hfluxle : ((1 - y₀ ^ (2 : ℕ)) * DΦ y₀) ^ (2 : ℕ) / (c ^ (2 : ℕ) * s)
      ≤ 3 * (((1 - y₀ ^ (2 : ℕ)) * DΦ y₀) ^ (2 : ℕ) / (c ^ (2 : ℕ) * ((y₀ ^ (2 : ℕ) - s) * (1 - y₀ ^ (2 : ℕ))))) := by
    rw [div_le_iff₀ hcs]
    have hval : 3 * (((1 - y₀ ^ (2 : ℕ)) * DΦ y₀) ^ (2 : ℕ) / (c ^ (2 : ℕ) * ((y₀ ^ (2 : ℕ) - s) * (1 - y₀ ^ (2 : ℕ)))))
        * (c ^ (2 : ℕ) * s)
        = ((1 - y₀ ^ (2 : ℕ)) * DΦ y₀) ^ (2 : ℕ) * (3 * s / ((y₀ ^ (2 : ℕ) - s) * (1 - y₀ ^ (2 : ℕ)))) := by
      field_simp
    rw [hval]
    have hge : (1 : ℝ) ≤ 3 * s / ((y₀ ^ (2 : ℕ) - s) * (1 - y₀ ^ (2 : ℕ))) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    nlinarith [hF, hge]
  rw [sturmAmplitude, prolateBandAmplitude, sturmAmplitudeVar, hKb]
  nlinarith [hfluxle, sq_nonneg (Φ y₀)]

/-- **The allowed interval costs only `exp(O(c s))`.**  The constant scale `c² s` matches the
potential there, so the amplitude envelope crosses the turning layer with no polynomial loss. -/
theorem prolate_allowed_sq_le {c s y₀ y : ℝ} {Φ DΦ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 < s) (hy04 : y₀ ^ (2 : ℕ) ≤ 4 * s) (hy0h : y₀ ^ (2 : ℕ) ≤ 1 / 2)
    (hy0 : 0 ≤ y) (hyy0 : y ≤ y₀)
    (hΦ : ∀ t ∈ Icc y y₀, HasDerivAt Φ (DΦ t) t)
    (hfluxd : ∀ t ∈ Icc y y₀, HasDerivAt (fun u => (1 - u ^ (2 : ℕ)) * DΦ u)
      (-(c ^ (2 : ℕ) * (s - t ^ (2 : ℕ)) * Φ t)) t) :
    Φ y ^ (2 : ℕ) ≤ sturmAmplitude (fun t => 1 - t ^ (2 : ℕ)) Φ DΦ (c ^ (2 : ℕ) * s) y₀
      * Real.exp (5 * (c * Real.sqrt s) * y₀) := by
  have hcs : (0 : ℝ) < c ^ (2 : ℕ) * s := by positivity
  have hsqrtK : Real.sqrt (c ^ (2 : ℕ) * s) = c * Real.sqrt s := by
    rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc.le]
  have hmem : ∀ t ∈ Icc y y₀, 0 ≤ t ∧ t ^ (2 : ℕ) ≤ y₀ ^ (2 : ℕ) := by
    intro t ht
    have ht0 : 0 ≤ t := le_trans hy0 ht.1
    have hy0nn : 0 ≤ y₀ := le_trans ht0 ht.2
    exact ⟨ht0, by nlinarith [ht.2, ht0]⟩
  have hp : ∀ t ∈ Icc y y₀, (1 : ℝ) - t ^ (2 : ℕ) ≠ 0 := by
    intro t ht
    have := (hmem t ht).2
    intro hcon
    nlinarith [hy0h, hcon]
  have hbound : ∀ t ∈ Icc y y₀,
      |1 / (1 - t ^ (2 : ℕ)) - c ^ (2 : ℕ) * (s - t ^ (2 : ℕ)) / (c ^ (2 : ℕ) * s)| ≤ 5 := by
    intro t ht
    have ht2 : t ^ (2 : ℕ) ≤ y₀ ^ (2 : ℕ) := (hmem t ht).2
    have ht2nn : (0 : ℝ) ≤ t ^ (2 : ℕ) := sq_nonneg t
    have hden : (0 : ℝ) < 1 - t ^ (2 : ℕ) := by nlinarith [hy0h]
    have hval : 1 / (1 - t ^ (2 : ℕ)) - c ^ (2 : ℕ) * (s - t ^ (2 : ℕ)) / (c ^ (2 : ℕ) * s)
        = 1 / (1 - t ^ (2 : ℕ)) - 1 + t ^ (2 : ℕ) / s := by
      field_simp
      ring
    rw [hval, abs_le]
    have hinv1 : (1 : ℝ) ≤ 1 / (1 - t ^ (2 : ℕ)) := by
      rw [le_div_iff₀ hden]
      linarith
    have hinv2 : 1 / (1 - t ^ (2 : ℕ)) ≤ 2 := by
      rw [div_le_iff₀ hden]
      nlinarith [hy0h, ht2]
    have hts : t ^ (2 : ℕ) / s ≤ 4 := by
      rw [div_le_iff₀ hs0]
      nlinarith [hy04, ht2]
    have htsnn : (0 : ℝ) ≤ t ^ (2 : ℕ) / s := by positivity
    constructor <;> linarith
  have henv := sturmAmplitude_le_mul_exp (p := fun t : ℝ => 1 - t ^ (2 : ℕ))
    (Q := fun t : ℝ => c ^ (2 : ℕ) * (s - t ^ (2 : ℕ))) (R := Φ) (DR := DΦ) (K := c ^ (2 : ℕ) * s) (M := 5)
    hyy0 hcs (by norm_num) hp hΦ hfluxd hbound
  have hsq : Φ y ^ (2 : ℕ) ≤ sturmAmplitude (fun t => 1 - t ^ (2 : ℕ)) Φ DΦ (c ^ (2 : ℕ) * s) y := by
    rw [sturmAmplitude]
    have : (0 : ℝ) ≤ ((1 - y ^ (2 : ℕ)) * DΦ y) ^ (2 : ℕ) / (c ^ (2 : ℕ) * s) := by positivity
    linarith
  have hGnn : 0 ≤ sturmAmplitude (fun t => 1 - t ^ (2 : ℕ)) Φ DΦ (c ^ (2 : ℕ) * s) y₀ :=
    sturmAmplitude_nonneg hcs
  have hexp : Real.exp (5 * Real.sqrt (c ^ (2 : ℕ) * s) * (y₀ - y))
      ≤ Real.exp (5 * (c * Real.sqrt s) * y₀) := by
    rw [Real.exp_le_exp, hsqrtK]
    have hsqrt : (0 : ℝ) ≤ Real.sqrt s := Real.sqrt_nonneg s
    nlinarith [mul_nonneg (mul_nonneg hc.le hsqrt) hy0]
  calc Φ y ^ (2 : ℕ) ≤ sturmAmplitude (fun t => 1 - t ^ (2 : ℕ)) Φ DΦ (c ^ (2 : ℕ) * s) y := hsq
    _ ≤ sturmAmplitude (fun t => 1 - t ^ (2 : ℕ)) Φ DΦ (c ^ (2 : ℕ) * s) y₀
        * Real.exp (5 * Real.sqrt (c ^ (2 : ℕ) * s) * (y₀ - y)) := henv
    _ ≤ sturmAmplitude (fun t => 1 - t ^ (2 : ℕ)) Φ DΦ (c ^ (2 : ℕ) * s) y₀
        * Real.exp (5 * (c * Real.sqrt s) * y₀) := mul_le_mul_of_nonneg_left hexp hGnn

/-! ## The band and the endpoint collar -/

/-- The log-scale-ratio of the band transport, monotone in the left endpoint. -/
def prolateScaleLog (s y₀ α : ℝ) : ℝ :=
  (Real.log (α ^ (2 : ℕ) - s) - Real.log (y₀ ^ (2 : ℕ) - s)) + (Real.log (1 - y₀ ^ (2 : ℕ)) - Real.log (1 - α ^ (2 : ℕ)))

theorem prolateScaleLog_nonneg {s y₀ α : ℝ} (hsy0 : s < y₀ ^ (2 : ℕ)) (hy0α : y₀ ≤ α)
    (hy00 : 0 ≤ y₀) (hα1 : α < 1) : 0 ≤ prolateScaleLog s y₀ α := by
  have hsq : y₀ ^ (2 : ℕ) ≤ α ^ (2 : ℕ) := by nlinarith
  have h1 : (0 : ℝ) < y₀ ^ (2 : ℕ) - s := by linarith
  have h2 : (0 : ℝ) < 1 - α ^ (2 : ℕ) := by nlinarith [hy00, hy0α]
  have hlog1 : Real.log (y₀ ^ (2 : ℕ) - s) ≤ Real.log (α ^ (2 : ℕ) - s) :=
    Real.log_le_log h1 (by linarith)
  have hlog2 : Real.log (1 - α ^ (2 : ℕ)) ≤ Real.log (1 - y₀ ^ (2 : ℕ)) :=
    Real.log_le_log h2 (by linarith)
  rw [prolateScaleLog]
  linarith

/-- **The band region, uniformly.**  For every point of the band past the matching point the
amplitude is below its value at the matching point's transport. -/
theorem prolateBandAmplitude_le_uniform {c s y₀ α y : ℝ} {Φ DΦ : ℝ → ℝ}
    (hc : 0 < c) (hy00 : 0 < y₀) (hsy0 : s < y₀ ^ (2 : ℕ)) (hy0y : y₀ ≤ y) (hyα : y ≤ α)
    (hα1 : α < 1)
    (hΦ : ∀ t, HasDerivAt Φ (DΦ t) t)
    (hfluxd : ∀ t ∈ Icc y₀ α, HasDerivAt (fun u => (1 - u ^ (2 : ℕ)) * DΦ u)
      (-(c ^ (2 : ℕ) * (s - t ^ (2 : ℕ)) * Φ t)) t)
    (hpos : ∀ t ∈ Icc y₀ α, Φ t ≠ 0) :
    prolateBandAmplitude c s Φ DΦ y
      ≤ prolateBandAmplitude c s Φ DΦ α
        * Real.exp (2 * c * (bandEndpointPhase s y₀ - bandEndpointPhase s α)
            + prolateScaleLog s y₀ α) := by
  have hy0nn : 0 ≤ y := le_trans hy00.le hy0y
  have hsy : s < y ^ (2 : ℕ) := by nlinarith [hy0y, hy00]
  have hsub : Icc y α ⊆ Icc y₀ α := Icc_subset_Icc hy0y le_rfl
  have hmain := prolateBand_amplitude_le (c := c) (s := s) hc hy0nn hsy hyα hα1
    (fun t _ => hΦ t) (fun t ht => hfluxd t (hsub ht)) (fun t ht => hpos t (hsub ht))
  have hGnn : 0 ≤ prolateBandAmplitude c s Φ DΦ α := by
    have hK : 0 < prolateBandScale c s α :=
      prolateBandScale_pos hc (by nlinarith [hyα, hy0nn]) (by nlinarith [hα1, hy0nn, hyα])
    exact sturmAmplitudeVar_nonneg hK
  refine le_trans hmain (mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 ?_) hGnn)
  have hphase : bandEndpointPhase s y ≤ bandEndpointPhase s y₀ :=
    antitone_bandEndpointPhase s hy0y
  have hsq : y₀ ^ (2 : ℕ) ≤ y ^ (2 : ℕ) := by nlinarith
  have h1 : (0 : ℝ) < y₀ ^ (2 : ℕ) - s := by linarith
  have h2 : (0 : ℝ) < 1 - α ^ (2 : ℕ) := by nlinarith [hy0nn, hyα]
  have hlog1 : Real.log (y₀ ^ (2 : ℕ) - s) ≤ Real.log (y ^ (2 : ℕ) - s) :=
    Real.log_le_log h1 (by linarith)
  have hlog2 : Real.log (1 - y ^ (2 : ℕ)) ≤ Real.log (1 - y₀ ^ (2 : ℕ)) :=
    Real.log_le_log (by nlinarith [hyα, hα1, hy0nn]) (by linarith)
  rw [prolateScaleLog]
  nlinarith [hphase, hlog1, hlog2, hc.le]

/-! ## The pointwise aperture envelope -/

/-- **The aperture envelope with no turning-layer prefactor.**  Every point of `[-1, 1]` obeys the
same bound: the band amplitude at the collar anchor, transported by the sharp exponential and the
scale ratio, plus the endpoint collar's own contribution. -/
theorem prolate_sq_le_aperture_envelope {c s y₀ α : ℝ} {Φ DΦ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 < s) (hs1 : s < 1)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1) (heven : Function.Even Φ)
    (hsy0 : s < y₀ ^ (2 : ℕ)) (hy00 : 0 < y₀) (hy04 : y₀ ^ (2 : ℕ) ≤ 4 * s) (hy0h : y₀ ^ (2 : ℕ) ≤ 1 / 2)
    (hratio : (y₀ ^ (2 : ℕ) - s) * (1 - y₀ ^ (2 : ℕ)) ≤ 3 * s)
    (hy0α : y₀ ≤ α) (hα1 : α < 1)
    (houter : ∀ t ∈ Icc α 1, c ^ (2 : ℕ) * (1 - 2 * t ^ (2 : ℕ)) ≤ -(s * c ^ (2 : ℕ)))
    (hposΦ : ∀ t ∈ Icc y₀ 1, 0 < Φ t)
    (hΦd : ∀ t, HasDerivAt Φ (DΦ t) t)
    (hfluxd : ∀ t ∈ Icc (0 : ℝ) α, HasDerivAt (fun u => (1 - u ^ (2 : ℕ)) * DΦ u)
      (-(c ^ (2 : ℕ) * (s - t ^ (2 : ℕ)) * Φ t)) t)
    {y : ℝ} (hy : y ∈ Icc (-1 : ℝ) 1) :
    Φ y ^ (2 : ℕ)
      ≤ 3 * (prolateBandAmplitude c s Φ DΦ α
            * Real.exp (2 * c * (bandEndpointPhase s y₀ - bandEndpointPhase s α)
                + prolateScaleLog s y₀ α))
          * Real.exp (5 * (c * Real.sqrt s) * y₀)
        + Real.exp (2 * (c * bandEndpointPhase s α)) := by
  have hα0 : 0 < α := lt_of_lt_of_le hy00 hy0α
  have hsα : s < α ^ (2 : ℕ) := by nlinarith [hy0α, hy00]
  have hposband : ∀ t ∈ Icc y₀ α, Φ t ≠ 0 := fun t ht =>
    (hposΦ t ⟨ht.1, le_trans ht.2 hα1.le⟩).ne'
  set T : ℝ := prolateBandAmplitude c s Φ DΦ α
      * Real.exp (2 * c * (bandEndpointPhase s y₀ - bandEndpointPhase s α)
          + prolateScaleLog s y₀ α) with hTdef
  have hTnn : 0 ≤ T := by
    have hK : 0 < prolateBandScale c s α :=
      prolateBandScale_pos hc hsα (by nlinarith [hα1, hα0])
    have := sturmAmplitudeVar_nonneg (p := fun t : ℝ => 1 - t ^ (2 : ℕ)) (R := Φ) (DR := DΦ) hK
    rw [hTdef]
    have hexp : (0 : ℝ) < Real.exp (2 * c * (bandEndpointPhase s y₀ - bandEndpointPhase s α)
        + prolateScaleLog s y₀ α) := Real.exp_pos _
    exact mul_nonneg this hexp.le
  have hexp5 : (1 : ℝ) ≤ Real.exp (5 * (c * Real.sqrt s) * y₀) := by
    rw [Real.one_le_exp_iff]
    have hsqrt : (0 : ℝ) ≤ Real.sqrt s := Real.sqrt_nonneg s
    positivity
  have hcollarnn : (0 : ℝ) ≤ Real.exp (2 * (c * bandEndpointPhase s α)) := (Real.exp_pos _).le
  -- reduce to `|y|`
  have habs : |y| ∈ Icc (0 : ℝ) 1 := ⟨abs_nonneg y, (abs_le).2 ⟨by linarith [hy.1], hy.2⟩⟩
  have heq : Φ |y| = Φ y := by
    by_cases hy0 : 0 ≤ y
    · rw [abs_of_nonneg hy0]
    · rw [abs_of_neg (lt_of_not_ge hy0)]
      exact heven y
  rw [← heq]
  set z : ℝ := |y| with hzdef
  have hz0 : 0 ≤ z := habs.1
  have hz1 : z ≤ 1 := habs.2
  clear_value z
  rcases le_or_gt z y₀ with hzy0 | hzy0
  · -- the allowed interval
    have hsubz : Icc z y₀ ⊆ Icc (0 : ℝ) α := Icc_subset_Icc hz0 hy0α
    have hall := prolate_allowed_sq_le (c := c) (s := s) (y₀ := y₀) (y := z) hc hs0 hy04 hy0h
      hz0 hzy0 (fun t _ => hΦd t) (fun t ht => hfluxd t (hsubz ht))
    have hstep := sturmAmplitude_const_le_three_mul_band (c := c) (s := s) (y₀ := y₀)
      (Φ := Φ) (DΦ := DΦ) hc hs0 hsy0 hy0h hratio
    have hband := prolateBandAmplitude_le_uniform (c := c) (s := s) (y := y₀) hc hy00 hsy0
      le_rfl hy0α hα1 hΦd
      (fun t ht => hfluxd t ⟨le_trans hy00.le ht.1, ht.2⟩) hposband
    have hexp0 : (0 : ℝ) < Real.exp (5 * (c * Real.sqrt s) * y₀) := Real.exp_pos _
    have hchain : Φ z ^ (2 : ℕ) ≤ 3 * T * Real.exp (5 * (c * Real.sqrt s) * y₀) := by
      refine le_trans hall ?_
      have h1 : sturmAmplitude (fun t => 1 - t ^ (2 : ℕ)) Φ DΦ (c ^ (2 : ℕ) * s) y₀ ≤ 3 * T := by
        refine le_trans hstep ?_
        have := hband
        rw [← hTdef] at this
        linarith
      exact mul_le_mul_of_nonneg_right h1 hexp0.le
    linarith [hchain, hcollarnn]
  · rcases le_or_gt z α with hzα | hzα
    · -- the band
      have hband := prolateBandAmplitude_le_uniform (c := c) (s := s) (y := z) hc hy00 hsy0
        hzy0.le hzα hα1 hΦd (fun t ht => hfluxd t ⟨le_trans hy00.le ht.1, ht.2⟩) hposband
      have hsq : Φ z ^ (2 : ℕ) ≤ prolateBandAmplitude c s Φ DΦ z := by
        have hK : 0 < prolateBandScale c s z :=
          prolateBandScale_pos hc (by nlinarith [hzy0, hy00]) (by nlinarith [hzα, hα1, hz0])
        exact sq_le_sturmAmplitudeVar hK
      have hle : Φ z ^ (2 : ℕ) ≤ T := by
        rw [hTdef]
        exact le_trans hsq hband
      nlinarith [hle, hTnn, hexp5, hcollarnn]
    · -- the endpoint collar
      have hfirst : (0 : ℝ) ≤ 3 * T * Real.exp (5 * (c * Real.sqrt s) * y₀) := by
        have hexp0 : (0 : ℝ) < Real.exp (5 * (c * Real.sqrt s) * y₀) := Real.exp_pos _
        positivity
      have hphase : bandEndpointPhase s z ≤ bandEndpointPhase s α :=
        antitone_bandEndpointPhase s hzα.le
      have hcollar1 : (1 : ℝ) ≤ Real.exp (2 * (c * bandEndpointPhase s α)) := by
        rw [Real.one_le_exp_iff]
        have := bandEndpointPhase_nonneg s α
        positivity
      rcases eq_or_lt_of_le hz1 with hz1e | hz1l
      · have hval : Φ z = 1 := by
          rw [hz1e]
          exact hΦ1
        rw [hval, one_pow]
        linarith [hfirst, hcollar1]
      have hposz : ∀ t ∈ Icc z 1, 0 < Φ t := fun t ht =>
        hposΦ t ⟨le_trans (le_trans hy0α hzα.le) ht.1, ht.2⟩
      have hsz : s < z ^ (2 : ℕ) := by nlinarith [hzα, hα0, hsα]
      have hQz : ∀ t ∈ Icc z 1, 0 < -(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * t ^ (2 : ℕ) := by
        intro t ht
        have hzt : z ≤ t := ht.1
        have hsqz : z ^ (2 : ℕ) ≤ t ^ (2 : ℕ) := by nlinarith [hz0, hzt]
        nlinarith [mul_pos (pow_pos hc 2) (sub_pos.2 hsz)]
      have houterz : ∀ t ∈ Icc z 1, c ^ (2 : ℕ) * (1 - 2 * t ^ (2 : ℕ)) ≤ -(s * c ^ (2 : ℕ)) := fun t ht =>
        houter t ⟨le_trans hzα.le ht.1, ht.2⟩
      have hmain := prolate_anchor_le_exp_bandPhase hsm heig hc hs1
        hsz.le hz0 hz1l hposz hQz houterz
      rw [hΦ1, one_mul] at hmain
      have hΦz : 0 < Φ z := hposΦ z ⟨le_trans hy0α hzα.le, hz1⟩
      have hbound : Φ z ≤ Real.exp (c * bandEndpointPhase s α) :=
        le_trans hmain (Real.exp_le_exp.2 (by nlinarith [hphase, hc.le]))
      have hsq : Φ z ^ (2 : ℕ) ≤ Real.exp (c * bandEndpointPhase s α) ^ (2 : ℕ) :=
        pow_le_pow_left₀ hΦz.le hbound 2
      have hval : Real.exp (c * bandEndpointPhase s α) ^ (2 : ℕ)
          = Real.exp (2 * (c * bandEndpointPhase s α)) := by
        rw [← Real.exp_nat_mul]
        push_cast
        ring_nf
      rw [hval] at hsq
      linarith [hsq, hfirst]

/-- **The aperture mass with no turning-layer prefactor.** -/
theorem integral_sq_le_aperture_envelope {c s y₀ α : ℝ} {Φ DΦ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 < s) (hs1 : s < 1)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1) (heven : Function.Even Φ)
    (hsy0 : s < y₀ ^ (2 : ℕ)) (hy00 : 0 < y₀) (hy04 : y₀ ^ (2 : ℕ) ≤ 4 * s) (hy0h : y₀ ^ (2 : ℕ) ≤ 1 / 2)
    (hratio : (y₀ ^ (2 : ℕ) - s) * (1 - y₀ ^ (2 : ℕ)) ≤ 3 * s)
    (hy0α : y₀ ≤ α) (hα1 : α < 1)
    (houter : ∀ t ∈ Icc α 1, c ^ (2 : ℕ) * (1 - 2 * t ^ (2 : ℕ)) ≤ -(s * c ^ (2 : ℕ)))
    (hposΦ : ∀ t ∈ Icc y₀ 1, 0 < Φ t)
    (hΦd : ∀ t, HasDerivAt Φ (DΦ t) t)
    (hfluxd : ∀ t ∈ Icc (0 : ℝ) α, HasDerivAt (fun u => (1 - u ^ (2 : ℕ)) * DΦ u)
      (-(c ^ (2 : ℕ) * (s - t ^ (2 : ℕ)) * Φ t)) t) :
    (∫ y in (-1 : ℝ)..1, Φ y ^ (2 : ℕ))
      ≤ 2 * (3 * (prolateBandAmplitude c s Φ DΦ α
              * Real.exp (2 * c * (bandEndpointPhase s y₀ - bandEndpointPhase s α)
                  + prolateScaleLog s y₀ α))
            * Real.exp (5 * (c * Real.sqrt s) * y₀)
          + Real.exp (2 * (c * bandEndpointPhase s α))) := by
  have hint : IntervalIntegrable (fun y : ℝ => Φ y ^ (2 : ℕ)) volume (-1) 1 :=
    (hsm.continuous.pow 2).intervalIntegrable (-1) 1
  have hpoint : ∀ y ∈ Icc (-1 : ℝ) 1, Φ y ^ (2 : ℕ)
      ≤ 3 * (prolateBandAmplitude c s Φ DΦ α
            * Real.exp (2 * c * (bandEndpointPhase s y₀ - bandEndpointPhase s α)
                + prolateScaleLog s y₀ α))
          * Real.exp (5 * (c * Real.sqrt s) * y₀)
        + Real.exp (2 * (c * bandEndpointPhase s α)) := fun y hy =>
    prolate_sq_le_aperture_envelope hc hs0 hs1 hsm heig hΦ1 heven hsy0 hy00 hy04 hy0h hratio
      hy0α hα1 houter hposΦ hΦd hfluxd hy
  have hmono := intervalIntegral.integral_mono_on (by norm_num : (-1 : ℝ) ≤ 1)
    hint intervalIntegrable_const hpoint
  calc (∫ y in (-1 : ℝ)..1, Φ y ^ (2 : ℕ))
      ≤ ∫ _y in (-1 : ℝ)..1, (3 * (prolateBandAmplitude c s Φ DΦ α
            * Real.exp (2 * c * (bandEndpointPhase s y₀ - bandEndpointPhase s α)
                + prolateScaleLog s y₀ α))
          * Real.exp (5 * (c * Real.sqrt s) * y₀)
        + Real.exp (2 * (c * bandEndpointPhase s α))) := hmono
    _ = 2 * (3 * (prolateBandAmplitude c s Φ DΦ α
              * Real.exp (2 * c * (bandEndpointPhase s y₀ - bandEndpointPhase s α)
                  + prolateScaleLog s y₀ α))
            * Real.exp (5 * (c * Real.sqrt s) * y₀)
          + Real.exp (2 * (c * bandEndpointPhase s α))) := by
        simp only [intervalIntegral.integral_const, sub_neg_eq_add]
        ring

/-- **The aperture mass at the sharp action, explicitly.**  The only `c`-dependence left is the
sharp exponential `exp(2 c Xi_s(y₀))`, the scale ratio, and the `O(cs)` allowed-interval cost. -/
theorem integral_sq_le_exp_sharp_action_amplitude {c s y₀ α : ℝ} {Φ DΦ : ℝ → ℝ}
    (hc : 0 < c) (hs0 : 0 < s) (hs1 : s < 1) (hcs : 4 ≤ c * s)
    (hsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Φ)
    (heig : ∀ y ∈ Icc (-1 : ℝ) 1, prolateSLAction c Φ y = -(s * c ^ (2 : ℕ)) * Φ y)
    (hΦ1 : Φ 1 = 1) (heven : Function.Even Φ)
    (hsy0 : s < y₀ ^ (2 : ℕ)) (hy00 : 0 < y₀) (hy04 : y₀ ^ (2 : ℕ) ≤ 4 * s) (hy0h : y₀ ^ (2 : ℕ) ≤ 1 / 2)
    (hratio : (y₀ ^ (2 : ℕ) - s) * (1 - y₀ ^ (2 : ℕ)) ≤ 3 * s)
    (hy0α : y₀ ≤ α) (hα1 : α < 1)
    (houter : ∀ t ∈ Icc α 1, c ^ (2 : ℕ) * (1 - 2 * t ^ (2 : ℕ)) ≤ -(s * c ^ (2 : ℕ)))
    (hposΦ : ∀ t ∈ Icc y₀ 1, 0 < Φ t)
    (hΦd : ∀ t, HasDerivAt Φ (DΦ t) t)
    (hfluxd : ∀ t ∈ Icc (0 : ℝ) α, HasDerivAt (fun u => (1 - u ^ (2 : ℕ)) * DΦ u)
      (-(c ^ (2 : ℕ) * (s - t ^ (2 : ℕ)) * Φ t)) t) :
    (∫ y in (-1 : ℝ)..1, Φ y ^ (2 : ℕ))
      ≤ 2 * (3 * (1 + (1 - α ^ (2 : ℕ)) * (prolateRadialBarrier c s α + 6 / (1 - α)) ^ (2 : ℕ)
                / (c ^ (2 : ℕ) * (α ^ (2 : ℕ) - s))) + 1)
        * Real.exp (2 * c * bandEndpointPhase s y₀ + prolateScaleLog s y₀ α
            + 5 * (c * Real.sqrt s) * y₀) := by
  have hα0 : 0 < α := lt_of_lt_of_le hy00 hy0α
  have hsα : s < α ^ (2 : ℕ) := by nlinarith [hy0α, hy00]
  have hαpos : ∀ u ∈ Icc α 1, 0 < Φ u := fun u hu =>
    hposΦ u ⟨le_trans hy0α hu.1, hu.2⟩
  have hQα : ∀ t ∈ Icc α 1, 0 < -(s * c ^ (2 : ℕ)) + c ^ (2 : ℕ) * t ^ (2 : ℕ) := by
    intro t ht
    have hsqt : α ^ (2 : ℕ) ≤ t ^ (2 : ℕ) := by nlinarith [ht.1, hα0]
    nlinarith [mul_pos (pow_pos hc 2) (sub_pos.2 hsα)]
  have hEnv := integral_sq_le_aperture_envelope hc hs0 hs1 hsm heig hΦ1 heven hsy0 hy00 hy04
    hy0h hratio hy0α hα1 houter hposΦ hΦd hfluxd
  -- the anchor value and amplitude
  have hΦα : Φ α ≤ Real.exp (c * bandEndpointPhase s α) := by
    have := prolate_anchor_le_exp_bandPhase hsm heig hc hs1 hsα.le hα0.le hα1 hαpos hQα houter
    rwa [hΦ1, one_mul] at this
  have hB := abs_prolateLogDeriv_le_band hc hs0.le hs1 hcs hsm heig hΦ1 hα0 hα1 hsα hαpos
  have hGα := prolateBandAmplitude_anchor_le (c := c) (s := s) (α := α)
    (B := prolateRadialBarrier c s α + 6 / (1 - α)) hc hα0.le hα1 hsα
    (hαpos α ⟨le_rfl, hα1.le⟩) hΦd hB
  set C : ℝ := 1 + (1 - α ^ (2 : ℕ)) * (prolateRadialBarrier c s α + 6 / (1 - α)) ^ (2 : ℕ)
      / (c ^ (2 : ℕ) * (α ^ (2 : ℕ) - s)) with hCdef
  have hCnn : 0 ≤ C := by
    have h1 : (0 : ℝ) < α ^ (2 : ℕ) - s := by linarith
    have h2 : (0 : ℝ) < 1 - α ^ (2 : ℕ) := by nlinarith
    rw [hCdef]
    positivity
  have hΦαnn : 0 ≤ Φ α := (hαpos α ⟨le_rfl, hα1.le⟩).le
  have hZ : Φ α ^ (2 : ℕ) ≤ Real.exp (2 * (c * bandEndpointPhase s α)) := by
    have hsq := pow_le_pow_left₀ hΦαnn hΦα 2
    have hval : Real.exp (c * bandEndpointPhase s α) ^ (2 : ℕ)
        = Real.exp (2 * (c * bandEndpointPhase s α)) := by
      rw [← Real.exp_nat_mul]
      push_cast
      ring_nf
    rwa [hval] at hsq
  have hGZ : prolateBandAmplitude c s Φ DΦ α
      ≤ C * Real.exp (2 * (c * bandEndpointPhase s α)) := by
    refine le_trans hGα ?_
    have := mul_le_mul_of_nonneg_right hZ hCnn
    linarith [this]
  -- the exponents
  set X : ℝ := 2 * c * (bandEndpointPhase s y₀ - bandEndpointPhase s α)
      + prolateScaleLog s y₀ α with hXdef
  set Y : ℝ := 5 * (c * Real.sqrt s) * y₀ with hYdef
  set Z : ℝ := 2 * (c * bandEndpointPhase s α) with hZdef
  set W : ℝ := 2 * c * bandEndpointPhase s y₀ + prolateScaleLog s y₀ α
      + 5 * (c * Real.sqrt s) * y₀ with hWdef
  have hsum : Z + X + Y = W := by
    rw [hZdef, hXdef, hYdef, hWdef]
    ring
  have hZW : Z ≤ W := by
    have hphase : bandEndpointPhase s α ≤ bandEndpointPhase s y₀ :=
      antitone_bandEndpointPhase s hy0α
    have hΛ : 0 ≤ prolateScaleLog s y₀ α :=
      prolateScaleLog_nonneg hsy0 hy0α hy00.le hα1
    have hY0 : 0 ≤ Y := by
      rw [hYdef]
      have : (0 : ℝ) ≤ Real.sqrt s := Real.sqrt_nonneg s
      positivity
    rw [hZdef, hWdef]
    nlinarith [hphase, hΛ, hY0, hc.le]
  have hexpX : (0 : ℝ) < Real.exp X := Real.exp_pos _
  have hexpY : (0 : ℝ) < Real.exp Y := Real.exp_pos _
  have hstep : 3 * (prolateBandAmplitude c s Φ DΦ α * Real.exp X) * Real.exp Y
      + Real.exp Z ≤ (3 * C + 1) * Real.exp W := by
    have h1 : prolateBandAmplitude c s Φ DΦ α * Real.exp X * Real.exp Y
        ≤ C * Real.exp Z * Real.exp X * Real.exp Y := by
      have := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hGZ hexpX.le) hexpY.le
      linarith [this]
    have h2 : C * Real.exp Z * Real.exp X * Real.exp Y = C * Real.exp W := by
      rw [mul_assoc, mul_assoc, ← Real.exp_add, ← Real.exp_add, ← hsum]
      ring_nf
    have h3 : Real.exp Z ≤ Real.exp W := Real.exp_le_exp.2 hZW
    nlinarith [h1, h2.le, h2.ge, h3]
  refine le_trans hEnv ?_
  have hexpW : (0 : ℝ) < Real.exp W := Real.exp_pos _
  nlinarith [hstep, hexpW]

end GaloisForLFunctions.RHTower

end
