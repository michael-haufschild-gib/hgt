import GaloisForLFunctions.RHTower.DigammaImaginaryVerticalAsymptotic
import GaloisForLFunctions.HTGeometry.DigammaFieldValuation
import GaloisForLFunctions.HTGeometry.HausdorffCDDPhaseKernel

/-!
# The digamma log asymptotic, uniformly on a vertical tube

`ψ(σ+it) − (log t + iπ/2) → 0` is proved on each vertical line, but both halves of that proof rest on
bounds that never see the abscissa:

* the real part obeys `|Re ψ(σ+it) − ½log(σ²+t²)| ≤ 1/t² + π/(2t)`, and the log gap
  `½log(σ²+t²) − log t = ½log(1+σ²/t²)` is at most `σ²/(2t²)`;
* the imaginary part is caught between `π/2 − arctan(σ/t)` and `1/t + (π/2 − arctan(σ/t))`, and
  `arctan(σ/t) ≤ σ/t`.

So on a tube `0 ≤ σ ≤ M` the whole difference is `O(1/t)` with one constant — the logarithmic level of
the tube form of eq. (19).
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The digamma log asymptotic, uniformly on a vertical tube.** -/
theorem exists_uniform_bound_digamma_sub_vertLog {M : ℝ} (hM : 0 < M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 0 ≤ σ → σ ≤ M → 1 ≤ t →
      ‖Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) - vertLog t‖ ≤ C / t := by
  refine ⟨2 + Real.pi / 2 + M ^ (2 : ℕ) / 2 + M, by positivity, ?_⟩
  intro σ t hσ hσM ht
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  set z : ℂ := Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) - vertLog t with hz
  have hre : z.re = (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).re - Real.log t := by
    rw [hz, vertLog]
    simp
  have him : z.im = (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).im - Real.pi / 2 := by
    rw [hz, vertLog]
    simp
  -- the real part: the sharp bound plus the logarithmic gap
  have hgap : (1 / 2) * Real.log (σ ^ (2 : ℕ) + t ^ (2 : ℕ)) - Real.log t ≤ σ ^ (2 : ℕ) / (2 * t ^ (2 : ℕ)) := by
    have ht2 : (0 : ℝ) < t ^ (2 : ℕ) := by positivity
    have hu : (0 : ℝ) < 1 + σ ^ (2 : ℕ) / t ^ (2 : ℕ) := by positivity
    have hsplit : (1 / 2) * Real.log (σ ^ (2 : ℕ) + t ^ (2 : ℕ)) - Real.log t
        = (1 / 2) * Real.log (1 + σ ^ (2 : ℕ) / t ^ (2 : ℕ)) := by
      rw [show σ ^ (2 : ℕ) + t ^ (2 : ℕ) = (1 + σ ^ (2 : ℕ) / t ^ (2 : ℕ)) * t ^ (2 : ℕ) by field_simp; ring,
        Real.log_mul (ne_of_gt hu) (ne_of_gt ht2), Real.log_pow]
      have hlt : Real.log t = (2 : ℝ)⁻¹ * (2 * Real.log t) := by ring
      rw [hlt]
      push_cast
      ring
    rw [hsplit]
    have hlog : Real.log (1 + σ ^ (2 : ℕ) / t ^ (2 : ℕ)) ≤ σ ^ (2 : ℕ) / t ^ (2 : ℕ) := by
      have := Real.log_le_sub_one_of_pos hu
      linarith
    calc (1 / 2) * Real.log (1 + σ ^ (2 : ℕ) / t ^ (2 : ℕ)) ≤ (1 / 2) * (σ ^ (2 : ℕ) / t ^ (2 : ℕ)) := by linarith
      _ = σ ^ (2 : ℕ) / (2 * t ^ (2 : ℕ)) := by ring
  have hgap' : -(σ ^ (2 : ℕ) / (2 * t ^ (2 : ℕ))) ≤ (1 / 2) * Real.log (σ ^ (2 : ℕ) + t ^ (2 : ℕ)) - Real.log t := by
    have ht2 : (0 : ℝ) < t ^ (2 : ℕ) := by positivity
    have hle : Real.log t ≤ (1 / 2) * Real.log (σ ^ (2 : ℕ) + t ^ (2 : ℕ)) := by
      have hmono : Real.log (t ^ (2 : ℕ)) ≤ Real.log (σ ^ (2 : ℕ) + t ^ (2 : ℕ)) :=
        Real.log_le_log (by positivity) (by nlinarith)
      rw [Real.log_pow] at hmono
      push_cast at hmono
      linarith
    have hpos : (0 : ℝ) ≤ σ ^ (2 : ℕ) / (2 * t ^ (2 : ℕ)) := by positivity
    linarith
  have hrebound : |z.re| ≤ 1 / t ^ (2 : ℕ) + Real.pi / (2 * t) + σ ^ (2 : ℕ) / (2 * t ^ (2 : ℕ)) := by
    have hsharp := RHTower.re_digamma_vertical_bound_uncond hσ htpos
    rw [hre]
    have hsplit : (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).re - Real.log t
        = ((Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)).re
            - (1 / 2) * Real.log (σ ^ (2 : ℕ) + t ^ (2 : ℕ)))
          + ((1 / 2) * Real.log (σ ^ (2 : ℕ) + t ^ (2 : ℕ)) - Real.log t) := by ring
    rw [hsplit]
    have h1 := abs_le.mp hsharp
    rw [abs_le]
    constructor
    · have : (0 : ℝ) ≤ 1 / t ^ (2 : ℕ) + Real.pi / (2 * t) := by positivity
      linarith [h1.1, hgap']
    · linarith [h1.2, hgap]
  -- the imaginary part: the sandwich plus `arctan x ≤ x`
  have himbound : |z.im| ≤ 1 / t + σ / t := by
    obtain ⟨hlow, hhigh⟩ := RHTower.im_digamma_vertical_sandwich hσ htpos
    have harc : Real.arctan (σ / t) ≤ σ / t := arctan_le_self (by positivity)
    have harc0 : 0 ≤ Real.arctan (σ / t) := Real.arctan_nonneg.mpr (by positivity)
    rw [him, abs_le]
    constructor
    · linarith
    · linarith
  -- combine
  have hnorm : ‖z‖ ≤ |z.re| + |z.im| := Complex.norm_le_abs_re_add_abs_im z
  have hinv2 : 1 / t ^ (2 : ℕ) ≤ 1 / t := by
    rw [div_le_div_iff₀ (by positivity) htpos]
    nlinarith [ht, htpos]
  have hσ2 : σ ^ (2 : ℕ) / (2 * t ^ (2 : ℕ)) ≤ M ^ (2 : ℕ) / 2 / t := by
    rw [div_le_div_iff₀ (by positivity) htpos]
    have hσle : σ ^ (2 : ℕ) ≤ M ^ (2 : ℕ) := by nlinarith
    have h1 : σ ^ (2 : ℕ) * t ≤ M ^ (2 : ℕ) * t := by nlinarith
    have h2 : M ^ (2 : ℕ) * t ≤ M ^ (2 : ℕ) * t ^ (2 : ℕ) := by
      have hmul := mul_nonneg (by positivity : (0 : ℝ) ≤ M ^ (2 : ℕ) * t)
        (by linarith : (0 : ℝ) ≤ t - 1)
      nlinarith [hmul]
    nlinarith
  have hσt : σ / t ≤ M / t := by
    gcongr
  have hpi : Real.pi / (2 * t) = Real.pi / 2 / t := by
    rw [div_div]
  calc ‖z‖ ≤ |z.re| + |z.im| := hnorm
    _ ≤ (1 / t ^ (2 : ℕ) + Real.pi / (2 * t) + σ ^ (2 : ℕ) / (2 * t ^ (2 : ℕ))) + (1 / t + σ / t) :=
        add_le_add hrebound himbound
    _ ≤ (1 / t + Real.pi / 2 / t + M ^ (2 : ℕ) / 2 / t) + (1 / t + M / t) := by
        rw [hpi]
        linarith
    _ = (2 + Real.pi / 2 + M ^ (2 : ℕ) / 2 + M) / t := by ring

end

end GaloisForLFunctions.HTGeometry
