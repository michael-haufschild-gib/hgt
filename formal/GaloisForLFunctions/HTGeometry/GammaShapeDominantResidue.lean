import GaloisForLFunctions.HTGeometry.GammaJetRatioFamily
import GaloisForLFunctions.HTGeometry.DominantSumDatum
import GaloisForLFunctions.HTGeometry.StdRatDatum

/-!
# The residue of a sum of Gamma-jet terms

A term `Γ^u·g` whose digamma part has a residue against `polyJetShape σ a dP b` has the same residue
against `gammaJetShape σ u a dP b`.  A finite family of such terms with pairwise distinct data has a
dominant member — on a vertical line the smallest power of `Γ` wins, since `Γ` decays faster than any
power of `s` — and the sum inherits the dominant member's residue.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- **A power of Gamma multiplies both the term and its shape.** -/
theorem tendsto_div_gammaJetShape_of_polyDatum (hσ : 0 < σ) (u : ℕ) {g : ℝ → ℂ} {a dP b : ℕ}
    {c : ℂ} (h : Tendsto (fun t : ℝ => g t / polyJetShape σ a dP b t) atTop (nhds c)) :
    Tendsto (fun t : ℝ => (gammaLine σ t ^ u * g t) / gammaJetShape σ u a dP b t)
      atTop (nhds c) := by
  refine h.congr' ?_
  filter_upwards [eventually_polyJetShape_ne_zero hσ a dP b] with t hS
  have hΓ : gammaLine σ t ^ u ≠ 0 := pow_ne_zero _ (gammaLine_ne_zero hσ t)
  rw [gammaJetShape]
  field_simp

/-- **The residue of a sum of Gamma-jet terms with pairwise distinct data.** -/
theorem exists_dominant_gammaShape_residue (hσ : 0 < σ) {N : ℕ} (hN : 0 < N)
    (F : Fin N → ℝ → ℂ) (u a dP b : Fin N → ℕ) (c : Fin N → ℂ)
    (hdist : ∀ α β : Fin N, α ≠ β →
      ¬ (u α = u β ∧ dP α + b β = dP β + b α ∧ a α = a β))
    (hres : ∀ α : Fin N, Tendsto (fun t : ℝ =>
      F α t / gammaJetShape σ (u α) (a α) (dP α) (b α) t) atTop (nhds (c α))) :
    ∃ β : Fin N, Tendsto (fun t : ℝ =>
      (∑ α : Fin N, F α t) / gammaJetShape σ (u β) (a β) (dP β) (b β) t) atTop (nhds (c β)) := by
  obtain ⟨β, hβ⟩ := exists_dominant_gammaJet_index hN u a dP b
  refine ⟨β, tendsto_sum_div_dominant F
    (fun α t => gammaJetShape σ (u α) (a α) (dP α) (b α) t) β c
    (fun α => eventually_gammaJetShape_ne_zero hσ _ _ _ _) hres fun α hα => ?_⟩
  rcases hβ α with hcase | hγ | hcase | hcase
  · exact absurd hcase (hdist α β hα)
  · exact tendsto_gammaJetShape_ratio_of_gamma_lt hσ hγ
  · obtain ⟨hu, hdeg⟩ := hcase
    rw [hu]
    exact tendsto_gammaJetShape_ratio_of_gamma_eq hσ
      (tendsto_polyJetShape_ratio_zero_of_deg hσ hdeg)
  · obtain ⟨hu, hdeg, hlog⟩ := hcase
    rw [hu]
    exact tendsto_gammaJetShape_ratio_of_gamma_eq hσ
      (tendsto_polyJetShape_ratio_zero_of_log hσ hdeg hlog)

/-- **Distinct Gamma powers already separate the data.** -/
theorem exists_dominant_gammaShape_residue_of_injective (hσ : 0 < σ) {N : ℕ} (hN : 0 < N)
    (F : Fin N → ℝ → ℂ) (u a dP b : Fin N → ℕ) (c : Fin N → ℂ) (hu : Function.Injective u)
    (hres : ∀ α : Fin N, Tendsto (fun t : ℝ =>
      F α t / gammaJetShape σ (u α) (a α) (dP α) (b α) t) atTop (nhds (c α))) :
    ∃ β : Fin N, Tendsto (fun t : ℝ =>
      (∑ α : Fin N, F α t) / gammaJetShape σ (u β) (a β) (dP β) (b β) t) atTop (nhds (c β)) :=
  exists_dominant_gammaShape_residue hσ hN F u a dP b c
    (fun _ _ hαβ hcase => hαβ (hu hcase.1)) hres

/-- Increasing the denominator slot of a shape divides it by a power of the coordinate. -/
theorem gammaJetShape_denom_add (σ : ℝ) (u a d b k : ℕ) (t : ℝ) :
    gammaJetShape σ u a d (b + k) t
      = gammaJetShape σ u a d b t * (((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹) ^ k := by
  rw [gammaJetShape, gammaJetShape, polyJetShape, polyJetShape, pow_add]
  field_simp
  ring

/-- **Dividing a residue by a polynomial.**  The shape's denominator slot absorbs the degree and the
limit is divided by the leading coefficient. -/
theorem tendsto_div_poly_gammaJetShape (hσ : 0 < σ) {G : ℝ → ℂ} {u a d b : ℕ} {r : ℂ}
    (h : Tendsto (fun t : ℝ => G t / gammaJetShape σ u a d b t) atTop (nhds r))
    {q : Polynomial ℂ} (hq : q ≠ 0) :
    Tendsto (fun t : ℝ => (G t / q.eval ((σ : ℂ) + (t : ℂ) * Complex.I))
        / gammaJetShape σ u a d (b + q.natDegree) t)
      atTop (nhds (r / q.leadingCoeff)) := by
  have hlead : q.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  have hpoly := tendsto_polynomial_mul_inv_pow σ q
  have hlim : Tendsto (fun t : ℝ => (G t / gammaJetShape σ u a d b t)
      / (q.eval ((σ : ℂ) + (t : ℂ) * Complex.I)
        * (((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹) ^ q.natDegree))
      atTop (nhds (r / q.leadingCoeff)) := h.div hpoly hlead
  refine hlim.congr' ?_
  filter_upwards [eventually_vertical_ne_zero σ,
    eventually_gammaJetShape_ne_zero hσ u a d b, hpoly.eventually_ne hlead] with t hs hshape hne
  have hq0 : q.eval ((σ : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hne
    exact hne rfl
  have hinv : (((σ : ℂ) + (t : ℂ) * Complex.I)⁻¹) ^ q.natDegree ≠ 0 :=
    pow_ne_zero _ (inv_ne_zero hs)
  rw [gammaJetShape_denom_add]
  field_simp

end GaloisForLFunctions
