import GaloisForLFunctions.HTGeometry.DigammaLogPowersUniform
import GaloisForLFunctions.HTGeometry.JetDatumUniform
import GaloisForLFunctions.HTGeometry.GammaVerticalUniformDecay

/-!
# A limit calculus for vertical tubes

The uniform statements of the residue chain all have the same shape: for every `ε` there is a height
beyond which a quantity is within `ε` of its limit *simultaneously for all abscissas in the tube*.
Naming that shape turns the remaining assembly into algebra: tube limits add, multiply, and are
produced by any `O(1/t)` bound with an abscissa-free constant.

The uniform inputs of the tube form of eq. (19) are then instances: the jets, the powers of the
logarithm, and the datum of a jet polynomial with rational coefficients.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- `f σ t → c` as `t → ∞`, uniformly for `0 < σ ≤ M`. -/
def TubeLimit (M : ℝ) (f : ℝ → ℝ → ℂ) (c : ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, ∀ σ t : ℝ, 0 < σ → σ ≤ M → T ≤ t → ‖f σ t - c‖ ≤ ε

/-- An `O(1/t)` bound with an abscissa-free constant is a tube limit. -/
theorem tubeLimit_of_bound {M : ℝ} {f : ℝ → ℝ → ℂ} {c : ℂ} {C : ℝ} (_hC : 0 ≤ C)
    (h : ∀ σ t : ℝ, 0 < σ → σ ≤ M → 1 ≤ t → ‖f σ t - c‖ ≤ C / t) : TubeLimit M f c := by
  intro ε hε
  refine ⟨max 1 (C / ε + 1), fun σ t hσ hσM ht => ?_⟩
  have ht1 : (1 : ℝ) ≤ t := le_trans (le_max_left _ _) ht
  have htC : C / ε + 1 ≤ t := le_trans (le_max_right _ _) ht
  have htpos : (0 : ℝ) < t := by linarith
  refine le_trans (h σ t hσ hσM ht1) ?_
  rw [div_le_iff₀ htpos]
  have hCe : C / ε ≤ t := by linarith
  rw [div_le_iff₀ hε] at hCe
  nlinarith

/-- A tube limit is eventually bounded on the tube. -/
theorem TubeLimit.exists_bound {M : ℝ} {f : ℝ → ℝ → ℂ} {c : ℂ} (h : TubeLimit M f c) :
    ∃ T : ℝ, ∀ σ t : ℝ, 0 < σ → σ ≤ M → T ≤ t → ‖f σ t‖ ≤ ‖c‖ + 1 := by
  obtain ⟨T, hT⟩ := h 1 one_pos
  refine ⟨T, fun σ t hσ hσM ht => ?_⟩
  have h1 := hT σ t hσ hσM ht
  have h2 : ‖f σ t‖ ≤ ‖f σ t - c‖ + ‖c‖ := by
    have := norm_add_le (f σ t - c) c
    simpa using this
  linarith

/-- Tube limits add. -/
theorem TubeLimit.add {M : ℝ} {f g : ℝ → ℝ → ℂ} {a b : ℂ} (hf : TubeLimit M f a)
    (hg : TubeLimit M g b) : TubeLimit M (fun σ t => f σ t + g σ t) (a + b) := by
  intro ε hε
  obtain ⟨T₁, hT₁⟩ := hf (ε / 2) (by positivity)
  obtain ⟨T₂, hT₂⟩ := hg (ε / 2) (by positivity)
  refine ⟨max T₁ T₂, fun σ t hσ hσM ht => ?_⟩
  have h1 := hT₁ σ t hσ hσM (le_trans (le_max_left _ _) ht)
  have h2 := hT₂ σ t hσ hσM (le_trans (le_max_right _ _) ht)
  have hsplit : f σ t + g σ t - (a + b) = (f σ t - a) + (g σ t - b) := by ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  linarith

/-- Tube limits multiply. -/
theorem TubeLimit.mul {M : ℝ} {f g : ℝ → ℝ → ℂ} {a b : ℂ} (hf : TubeLimit M f a)
    (hg : TubeLimit M g b) : TubeLimit M (fun σ t => f σ t * g σ t) (a * b) := by
  intro ε hε
  obtain ⟨T₀, hT₀⟩ := hf.exists_bound
  have hpos : 0 < ε / (2 * (‖a‖ + 1)) := by positivity
  have hpos' : 0 < ε / (2 * (‖b‖ + 1)) := by positivity
  obtain ⟨T₁, hT₁⟩ := hg (ε / (2 * (‖a‖ + 1))) hpos
  obtain ⟨T₂, hT₂⟩ := hf (ε / (2 * (‖b‖ + 1))) hpos'
  refine ⟨max T₀ (max T₁ T₂), fun σ t hσ hσM ht => ?_⟩
  have hb0 := hT₀ σ t hσ hσM (le_trans (le_max_left _ _) ht)
  have h1 := hT₁ σ t hσ hσM (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) ht)
  have h2 := hT₂ σ t hσ hσM (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) ht)
  have hsplit : f σ t * g σ t - a * b = f σ t * (g σ t - b) + b * (f σ t - a) := by ring
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have hfirst : ‖f σ t * (g σ t - b)‖ ≤ ε / 2 := by
    rw [norm_mul]
    calc ‖f σ t‖ * ‖g σ t - b‖ ≤ (‖a‖ + 1) * (ε / (2 * (‖a‖ + 1))) :=
          mul_le_mul hb0 h1 (norm_nonneg _) (by positivity)
      _ = ε / 2 := by
          field_simp
  have hsecond : ‖b * (f σ t - a)‖ ≤ ε / 2 := by
    rw [norm_mul]
    calc ‖b‖ * ‖f σ t - a‖ ≤ (‖b‖ + 1) * (ε / (2 * (‖b‖ + 1))) :=
          mul_le_mul (by linarith) h2 (norm_nonneg _) (by positivity)
      _ = ε / 2 := by
          field_simp
  linarith

/-- Tube limits transfer along a pointwise identity valid beyond some height. -/
theorem TubeLimit.congr {M : ℝ} {f g : ℝ → ℝ → ℂ} {c : ℂ} (hf : TubeLimit M f c) {T₀ : ℝ}
    (heq : ∀ σ t : ℝ, 0 < σ → σ ≤ M → T₀ ≤ t → f σ t = g σ t) : TubeLimit M g c := by
  intro ε hε
  obtain ⟨T, hT⟩ := hf ε hε
  refine ⟨max T T₀, fun σ t hσ hσM ht => ?_⟩
  rw [← heq σ t hσ hσM (le_trans (le_max_right _ _) ht)]
  exact hT σ t hσ hσM (le_trans (le_max_left _ _) ht)

/-- **The jets, as tube limits.** -/
theorem tubeLimit_pow_mul_iteratedDeriv_digamma {M : ℝ} (hM : 0 < M) (m : ℕ) :
    TubeLimit M (fun σ t => ((σ : ℂ) + (t : ℂ) * Complex.I) ^ (m + 1)
      * iteratedDeriv (m + 1) Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I))
      ((-1 : ℂ) ^ m * ((m.factorial : ℕ) : ℂ)) := by
  intro ε hε
  obtain ⟨T, hT⟩ := exists_uniform_height_pow_mul_iteratedDeriv_digamma m hM hε
  exact ⟨T, fun σ t hσ hσM ht => hT σ t hσ hσM ht⟩

/-- **The powers of the logarithm, as tube limits.** -/
theorem tubeLimit_digamma_pow_div_vertLog_pow {M : ℝ} (hM : 0 < M) (e : ℕ) :
    TubeLimit M (fun σ t => Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e
      / vertLog t ^ e) 1 := by
  intro ε hε
  obtain ⟨T, hT⟩ := exists_uniform_height_digamma_pow_div_vertLog_pow hM e hε
  exact ⟨T, fun σ t hσ hσM ht => hT σ t (le_of_lt hσ) hσM ht⟩

/-- **The datum of a non-flat jet polynomial with rational coefficients, as a tube limit.** -/
theorem tubeLimit_jetPolyCoeff_datum {M σ₀ : ℝ} (hM : 0 < M) (hσ₀ : 0 < σ₀)
    (N Mm W d : ℕ) (e : Fin Mm → Fin N → ℕ) (a : Fin Mm → Polynomial ℂ)
    (hdeg : ∀ α : Fin Mm, (a α).natDegree ≤ d)
    (hW : ∀ α : Fin Mm, W ≤ ∑ i : Fin N, ((i : ℕ) + 1) * e α i) {n : ℕ}
    (hnotflat : ¬ IsLineBigO σ₀ n (fun t : ℝ => ∑ α : Fin Mm,
      ((a α).eval ((σ₀ : ℂ) + (t : ℂ) * Complex.I) / ((σ₀ : ℂ) + (t : ℂ) * Complex.I) ^ d)
        * ∏ i : Fin N, iteratedDeriv ((i : ℕ) + 1) Complex.digamma
          ((σ₀ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)) :
    ∃ (p : ℕ) (c : ℂ), c ≠ 0 ∧ TubeLimit M (fun σ t =>
      ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p
        * (∑ α : Fin Mm, ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
            / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
          * ∏ i : Fin N, iteratedDeriv ((i : ℕ) + 1) Complex.digamma
            ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)) c := by
  obtain ⟨p, c, hc, hlim⟩ :=
    exists_uniform_jetPolyCoeff_datum hM hσ₀ N Mm W d e a hdeg hW hnotflat
  exact ⟨p, c, hc, fun ε hε => hlim ε hε⟩

/-- **The logarithmic level of a datum, uniformly on a tube.**  Multiplying a quantity with a tube
limit by a power of `ψ` and dividing by the corresponding power of the vertical logarithm keeps the
limit. -/
theorem TubeLimit.mul_digamma_pow_div_vertLog_pow {M : ℝ} (hM : 0 < M) {g : ℝ → ℝ → ℂ} {c : ℂ}
    (hg : TubeLimit M g c) (e : ℕ) :
    TubeLimit M (fun σ t => g σ t
      * (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e / vertLog t ^ e)) c := by
  have hmul := hg.mul (tubeLimit_digamma_pow_div_vertLog_pow hM e)
  rw [mul_one] at hmul
  exact hmul

end

end GaloisForLFunctions.HTGeometry
