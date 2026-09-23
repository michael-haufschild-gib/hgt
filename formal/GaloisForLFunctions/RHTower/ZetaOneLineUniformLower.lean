import GaloisForLFunctions.RHTower.ZetaOneLineLogPowerLowerBound
import GaloisForLFunctions.RHTower.ZetaLineLowerBound

/-!
# A uniform power-of-log lower bound for `ζ` on the closed strip `1 < σ ≤ 5/4`

`exists_lower_bound_riemannZeta_near_one_line` is a lower bound only above a frequency threshold,
and `exists_pos_le_norm_riemannZeta_low_freq` only below one.  Between them lies a compact
rectangle on which `ζ` is continuous and zero-free — the pole is excluded because the frequency is
bounded away from zero there — so a minimum argument closes the gap and the three ranges assemble
into one statement valid at every frequency.

This is the shape a Perron contour consumes: the Möbius generating series is `1/ζ`, so the bound
below on `ζ` is a bound above on the series, uniformly along the shifted line.

* `exists_uniform_lower_bound_riemannZeta`;
* `exists_uniform_upper_bound_inv_riemannZeta`.
-/

namespace RHTower

open Complex

noncomputable section

/-- On a compact frequency band away from the pole, `ζ` has a positive minimum modulus. -/
theorem exists_pos_lower_bound_riemannZeta_band {t₀ : ℝ} (ht₀ : 1 ≤ t₀) :
    ∃ c : ℝ, 0 < c ∧ ∀ σ t : ℝ, 1 ≤ σ → σ ≤ 5 / 4 → 1 ≤ t → t ≤ t₀ →
      c ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  classical
  set R : Set (ℝ × ℝ) := Set.Icc (1 : ℝ) (5 / 4) ×ˢ Set.Icc (1 : ℝ) t₀ with hR
  have hRcompact : IsCompact R := (isCompact_Icc).prod isCompact_Icc
  have hRne : R.Nonempty := ⟨(1, 1), ⟨by constructor <;> norm_num, ⟨le_rfl, ht₀⟩⟩⟩
  have hne : ∀ p ∈ R, ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) ≠ 1 := by
    rintro ⟨σ, t⟩ ⟨_, ht⟩
    intro hcon
    have him : ((σ : ℂ) + (t : ℂ) * Complex.I).im = t := by simp
    rw [hcon] at him
    simp at him
    linarith [ht.1, him]
  have hcont : ContinuousOn (fun p : ℝ × ℝ =>
      ‖riemannZeta ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I)‖) R := by
    intro p hp
    have hdiff : DifferentiableAt ℂ riemannZeta ((p.1 : ℂ) + (p.2 : ℂ) * Complex.I) :=
      differentiableAt_riemannZeta (hne p hp)
    have hmap : ContinuousAt (fun q : ℝ × ℝ => ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)) p := by
      fun_prop
    have hcomp : ContinuousAt (fun q : ℝ × ℝ =>
        riemannZeta ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)) p :=
      ContinuousAt.comp (g := riemannZeta)
        (f := fun q : ℝ × ℝ => ((q.1 : ℂ) + (q.2 : ℂ) * Complex.I)) hdiff.continuousAt hmap
    exact (hcomp.norm).continuousWithinAt
  obtain ⟨p₀, hp₀, hmin⟩ := hRcompact.exists_isMinOn hRne hcont
  refine ⟨‖riemannZeta ((p₀.1 : ℂ) + (p₀.2 : ℂ) * Complex.I)‖, ?_, ?_⟩
  · have hz : riemannZeta ((p₀.1 : ℂ) + (p₀.2 : ℂ) * Complex.I) ≠ 0 := by
      refine riemannZeta_ne_zero_of_one_le_re ?_
      have hre : ((p₀.1 : ℂ) + (p₀.2 : ℂ) * Complex.I).re = p₀.1 := by simp
      rw [hre]
      exact hp₀.1.1
    exact norm_pos_iff.2 hz
  · intro σ t hσ1 hσ2 ht1 htt
    exact hmin (show (σ, t) ∈ R from ⟨⟨hσ1, hσ2⟩, ⟨ht1, htt⟩⟩)

/-- **A power-of-log lower bound for `ζ` at every frequency**, on `1 < σ ≤ 5/4`. -/
theorem exists_uniform_lower_bound_riemannZeta :
    ∃ c : ℝ, 0 < c ∧ ∀ σ t : ℝ, 1 < σ → σ ≤ 5 / 4 →
      c / (Real.log (|t| + Real.exp 1)) ^ (11 : ℕ)
        ≤ ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := by
  obtain ⟨cT, t₀, hcT0, ht₀9, hT⟩ := exists_lower_bound_riemannZeta_near_one_line
  obtain ⟨clow, hclow0, hlow⟩ := exists_pos_le_norm_riemannZeta_low_freq
  obtain ⟨cband, hcband0, hband⟩ := exists_pos_lower_bound_riemannZeta_band
    (t₀ := t₀) (by linarith)
  set c : ℝ := min cT (min clow cband) with hc
  have hc0 : 0 < c := lt_min hcT0 (lt_min hclow0 hcband0)
  refine ⟨c, hc0, ?_⟩
  intro σ t hσ1 hσ2
  have hlog1 : (1 : ℝ) ≤ Real.log (|t| + Real.exp 1) := by
    have h1 : Real.exp 1 ≤ |t| + Real.exp 1 := by
      have := abs_nonneg t; linarith
    have := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at this
  have hpow1 : (1 : ℝ) ≤ (Real.log (|t| + Real.exp 1)) ^ (11 : ℕ) :=
    one_le_pow₀ hlog1
  have hdiv : c / (Real.log (|t| + Real.exp 1)) ^ (11 : ℕ) ≤ c := by
    rw [div_le_iff₀ (by linarith)]
    nlinarith [hc0.le, hpow1]
  rcases lt_or_ge |t| t₀ with hsmall | hbig
  · rcases lt_or_ge 1 |t| with hmid | hlow1
    · -- the compact band
      have hband' : cband ≤ ‖riemannZeta ((σ : ℂ) + ((|t| : ℝ) : ℂ) * Complex.I)‖ :=
        hband σ |t| hσ1.le hσ2 hmid.le hsmall.le
      have hconj : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖
          = ‖riemannZeta ((σ : ℂ) + ((|t| : ℝ) : ℂ) * Complex.I)‖ := by
        rcases abs_cases t with ⟨heq, _⟩ | ⟨heq, _⟩
        · rw [heq]
        · rw [heq]
          have hstar : ((σ : ℂ) + ((-t : ℝ) : ℂ) * Complex.I)
              = (starRingEnd ℂ) ((σ : ℂ) + (t : ℂ) * Complex.I) := by
            refine Complex.ext ?_ ?_ <;> simp
          rw [hstar, ← Complex.norm_conj, riemannZeta_conj]
      rw [hconj]
      exact le_trans hdiv (le_trans (min_le_right _ _ |>.trans (min_le_right _ _)) hband')
    · -- low frequency
      have hpt : ((σ : ℂ) + (t : ℂ) * Complex.I)
          = (((1 + (σ - 1) : ℝ)) : ℂ) + Complex.I * (t : ℂ) := by
        push_cast; ring
      rw [hpt]
      refine le_trans hdiv (le_trans (min_le_right _ _ |>.trans (min_le_left _ _)) ?_)
      exact hlow (σ - 1) t (by linarith) (by linarith) hlow1
  · -- high frequency: the power-of-log bound
    have hzeta := hT σ t hσ1.le hσ2 hbig
    refine le_trans ?_ hzeta
    have hlt : Real.log |t| ≤ Real.log (|t| + Real.exp 1) := by
      refine Real.log_le_log ?_ (by linarith [Real.exp_pos 1])
      linarith [ht₀9, hbig]
    have hlogt1 : (1 : ℝ) ≤ Real.log |t| := by
      have h8 : (8 : ℝ) ≤ |t| := by linarith
      have := two_le_log_of_eight_le h8
      linarith
    have hpowle : (Real.log |t|) ^ (11 : ℕ) ≤ (Real.log (|t| + Real.exp 1)) ^ (11 : ℕ) :=
      pow_le_pow_left₀ (by linarith) hlt 11
    have hpos : (0 : ℝ) < (Real.log |t|) ^ (11 : ℕ) := by positivity
    have hcle : c ≤ cT := min_le_left _ _
    have hA : (0 : ℝ) < (Real.log (|t| + Real.exp 1)) ^ (11 : ℕ) := by positivity
    rw [div_le_iff₀ hA, div_mul_eq_mul_div, le_div_iff₀ hpos]
    nlinarith [hcle, hpowle, hpos, hA, hc0.le, hcT0.le]

/-- **Hence a uniform upper bound for the Möbius generating series `1/ζ`.** -/
theorem exists_uniform_upper_bound_inv_riemannZeta :
    ∃ K : ℝ, 0 < K ∧ ∀ σ t : ℝ, 1 < σ → σ ≤ 5 / 4 →
      ‖(riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I))⁻¹‖
        ≤ K * (Real.log (|t| + Real.exp 1)) ^ (11 : ℕ) := by
  obtain ⟨c, hc0, hc⟩ := exists_uniform_lower_bound_riemannZeta
  refine ⟨c⁻¹, by positivity, ?_⟩
  intro σ t hσ1 hσ2
  have hlow := hc σ t hσ1 hσ2
  have hlog1 : (1 : ℝ) ≤ Real.log (|t| + Real.exp 1) := by
    have h1 : Real.exp 1 ≤ |t| + Real.exp 1 := by
      have := abs_nonneg t; linarith
    have := Real.log_le_log (Real.exp_pos 1) h1
    rwa [Real.log_exp] at this
  have hpow0 : (0 : ℝ) < (Real.log (|t| + Real.exp 1)) ^ (11 : ℕ) := by positivity
  have hzpos : (0 : ℝ) < ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ :=
    lt_of_lt_of_le (by positivity) hlow
  rw [norm_inv]
  rw [inv_le_iff_one_le_mul₀ hzpos]
  have hmul := mul_le_mul_of_nonneg_left hlow (by positivity :
    (0 : ℝ) ≤ c⁻¹ * (Real.log (|t| + Real.exp 1)) ^ (11 : ℕ))
  calc (1 : ℝ) = c⁻¹ * (Real.log (|t| + Real.exp 1)) ^ (11 : ℕ)
        * (c / (Real.log (|t| + Real.exp 1)) ^ (11 : ℕ)) := by
        field_simp
    _ ≤ c⁻¹ * (Real.log (|t| + Real.exp 1)) ^ (11 : ℕ)
        * ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ := hmul

end

end RHTower
