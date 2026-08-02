import GaloisForLFunctions.HTGeometry.UniformGammaJetTerm
import GaloisForLFunctions.HTGeometry.RatCoeffJetPoly

/-!
# Equation (5) uniformly on a vertical tube

Dividing a finite family by a dominant member, every ratio converges uniformly in the abscissa: the
members sharing the dominant datum tend to the quotient of their residues, and every other member
tends to zero.

The proof is the factorisation `F_α/F_β = (F_α/S_α)·(S_α/S_β)·(S_β/F_β)`, three tube limits — the
residue of `α`, the dominance ratio of eq. (26), and the inverse of the residue of `β`, which exists
because a nonzero tube limit keeps its quantity away from zero uniformly.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- A tube limit with nonzero value is eventually bounded away from zero on the tube. -/
theorem TubeLimit.exists_lower_bound {M : ℝ} {f : ℝ → ℝ → ℂ} {c : ℂ} (h : TubeLimit M f c)
    (hc : c ≠ 0) : ∃ T : ℝ, ∀ σ t : ℝ, 0 < σ → σ ≤ M → T ≤ t → ‖c‖ / 2 ≤ ‖f σ t‖ := by
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  obtain ⟨T, hT⟩ := h (‖c‖ / 2) (by positivity)
  refine ⟨T, fun σ t hσ hσM ht => ?_⟩
  have h1 := hT σ t hσ hσM ht
  have h2 : ‖c‖ ≤ ‖f σ t‖ + ‖f σ t - c‖ := by
    have := norm_sub_le c (f σ t)
    have hrev : ‖c - f σ t‖ = ‖f σ t - c‖ := norm_sub_rev _ _
    calc ‖c‖ = ‖f σ t + (c - f σ t)‖ := by ring_nf
      _ ≤ ‖f σ t‖ + ‖c - f σ t‖ := norm_add_le _ _
      _ = ‖f σ t‖ + ‖f σ t - c‖ := by rw [hrev]
  linarith

/-- Tube limits invert away from zero. -/
theorem TubeLimit.inv {M : ℝ} {f : ℝ → ℝ → ℂ} {c : ℂ} (h : TubeLimit M f c) (hc : c ≠ 0) :
    TubeLimit M (fun σ t => (f σ t)⁻¹) c⁻¹ := by
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  obtain ⟨T₀, hT₀⟩ := h.exists_lower_bound hc
  intro ε hε
  obtain ⟨T₁, hT₁⟩ := h (ε * ‖c‖ ^ 2 / 2) (by positivity)
  refine ⟨max T₀ T₁, fun σ t hσ hσM ht => ?_⟩
  have hlow := hT₀ σ t hσ hσM (le_trans (le_max_left _ _) ht)
  have hclose := hT₁ σ t hσ hσM (le_trans (le_max_right _ _) ht)
  have hfne : f σ t ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hlow
    linarith
  have hsplit : (f σ t)⁻¹ - c⁻¹ = (c - f σ t) / (f σ t * c) := by
    field_simp
  rw [hsplit, norm_div, norm_mul, norm_sub_rev]
  rw [div_le_iff₀ (by positivity)]
  calc ‖f σ t - c‖ ≤ ε * ‖c‖ ^ 2 / 2 := hclose
    _ ≤ ε * (‖f σ t‖ * ‖c‖) := by
        have hmul : ‖c‖ / 2 * ‖c‖ ≤ ‖f σ t‖ * ‖c‖ :=
          mul_le_mul_of_nonneg_right hlow (norm_nonneg _)
        nlinarith [hε.le, norm_nonneg (f σ t)]

/-- **Equation (5), uniformly on a vertical tube.**  Dividing the family by a dominant member, every
ratio converges uniformly: to the quotient of the residues on the dominant class, and to zero
elsewhere.  The normalizing member has ratio `1`. -/
theorem exists_tubeLimit_dominant_ratio {M : ℝ} (hM : 0 < M) {N : ℕ} (hN : 0 < N)
    (F : Fin N → ℝ → ℝ → ℂ) (k a b : Fin N → ℤ) (c : Fin N → ℂ) (hc : ∀ α, c α ≠ 0)
    (hlim : ∀ α, TubeLimit M (fun σ t => F α σ t / gammaShapeZ σ (k α) (a α) (b α) t) (c α)) :
    ∃ (β : Fin N) (d : Fin N → ℂ), d β = 1 ∧
      ∀ α : Fin N, TubeLimit M (fun σ t => F α σ t / F β σ t) (d α) := by
  classical
  obtain ⟨β, hβ⟩ := exists_dominant_shapeZ_index hN k a b
  have hinv := (hlim β).inv (hc β)
  refine ⟨β, fun α => if (k α = k β ∧ a α = a β ∧ b α = b β) then c α * (c β)⁻¹ else 0, ?_, ?_⟩
  · dsimp only
    rw [if_pos ⟨rfl, rfl, rfl⟩, mul_inv_cancel₀ (hc β)]
  · intro α
    dsimp only
    by_cases htie : k α = k β ∧ a α = a β ∧ b α = b β
    · rw [if_pos htie]
      obtain ⟨h1, h2, h3⟩ := htie
      have hshape : ∀ σ t : ℝ, gammaShapeZ σ (k α) (a α) (b α) t
          = gammaShapeZ σ (k β) (a β) (b β) t := by
        intro σ t
        rw [h1, h2, h3]
      have hmul := (hlim α).mul hinv
      refine hmul.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
      have hSβ : gammaShapeZ σ (k β) (a β) (b β) t ≠ 0 := gammaShapeZ_ne_zero_of_le hσ ht _ _ _
      rw [hshape σ t]
      field_simp
    · rw [if_neg htie]
      have hsub : k β < k α ∨ (k α = k β ∧ a α < a β)
          ∨ (k α = k β ∧ a α = a β ∧ b α < b β) := (hβ α).resolve_left htie
      have hmul := ((hlim α).mul (tubeLimit_gammaShapeZ_ratio_zero hM hsub)).mul hinv
      rw [mul_zero, zero_mul] at hmul
      refine hmul.congr (T₀ := 3) fun σ t hσ hσM ht => ?_
      have hSα : gammaShapeZ σ (k α) (a α) (b α) t ≠ 0 := gammaShapeZ_ne_zero_of_le hσ ht _ _ _
      have hSβ : gammaShapeZ σ (k β) (a β) (b β) t ≠ 0 := gammaShapeZ_ne_zero_of_le hσ ht _ _ _
      field_simp

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **The tube datum of a nonzero jet polynomial, with no hypothesis but nonvanishing.**  The
non-flatness the dichotomy needs is supplied by the flat elimination at a single line, so a jet
polynomial with rational coefficients that is nonzero *as a polynomial* has a uniform datum on every
tube. -/
theorem exists_uniform_jetPolyCoeff_datum_of_ne_zero {M : ℝ} (hM : 0 < M)
    (N Mm W d : ℕ) (e : Fin Mm → Fin N → ℕ) (a : Fin Mm → Polynomial ℂ)
    (hdeg : ∀ α : Fin Mm, (a α).natDegree ≤ d)
    (hW : ∀ α : Fin Mm, W ≤ ∑ i : Fin N, ((i : ℕ) + 1) * e α i)
    (hne : jetPolyMvCoeff N Mm d a e ≠ 0) :
    ∃ (p : ℕ) (c : ℂ), c ≠ 0 ∧ TubeLimit M (fun σ t =>
      ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p
        * (∑ α : Fin Mm, ((a α).eval ((σ : ℂ) + (t : ℂ) * Complex.I)
            / ((σ : ℂ) + (t : ℂ) * Complex.I) ^ d)
          * ∏ i : Fin N, iteratedDeriv ((i : ℕ) + 1) Complex.digamma
            ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α i)) c := by
  obtain ⟨n, hnotflat⟩ :=
    exists_not_isLineBigO_jetPolyCoeff (σ := 1) one_pos N Mm W d a e hdeg hW hne
  exact tubeLimit_jetPolyCoeff_datum hM one_pos N Mm W d e a hdeg hW hnotflat

end

end GaloisForLFunctions.HTGeometry
