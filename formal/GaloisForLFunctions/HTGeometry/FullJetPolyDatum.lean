import GaloisForLFunctions.HTGeometry.DominantSumDatum

/-!
# The datum of a jet polynomial including the logarithmic level

Grouping a polynomial in the digamma jets by its `ψ`-degree gives a finite family
`∑_α ψ^{e_α}·G_α` whose log-degrees `e_α` are pairwise distinct and whose `G_α` are polynomials in
the *positive-order* jets, each with a datum `s^{p_α}·G_α(s) → c_α`.

Multiplying a datum by `ψ^{e}` multiplies it by `L^e`, the resulting residues are against the shapes
`L^{e_α}/s^{p_α}`, and distinct log-degrees make the family non-cancelling.  So the whole polynomial
has the residue of its dominant group: this is eq. (19) for the digamma field, assembled from the
data of its groups.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

variable {σ : ℝ}

/-- **The datum of a grouped jet polynomial.** -/
theorem exists_grouped_jetPoly_datum (hσ : 0 < σ) {N : ℕ} (hN : 0 < N)
    (G : Fin N → ℝ → ℂ) (e : Fin N → ℕ) (he : Function.Injective e) (p : Fin N → ℕ)
    (c : Fin N → ℂ)
    (hdat : ∀ α : Fin N, Tendsto (fun t : ℝ =>
      ((σ : ℂ) + (t : ℂ) * Complex.I) ^ p α * G α t) atTop (nhds (c α))) :
    ∃ β : Fin N, Tendsto (fun t : ℝ =>
      (∑ α : Fin N, Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α * G α t)
        / polyJetShape σ (e β) 0 (p β) t) atTop (nhds (c β)) := by
  have hres : ∀ α : Fin N, Tendsto (fun t : ℝ =>
      (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α * G α t)
        / polyJetShape σ (e α) 0 (p α) t) atTop (nhds (c α)) := by
    intro α
    refine tendsto_div_polyJetShape_of_datum hσ ?_
    exact tendsto_datum_mul_digamma_pow hσ.le (e α) (hdat α)
  exact exists_dominant_shape_residue hσ hN
    (fun α t => Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) ^ e α * G α t) e p c he hres

/-- **The Gamma level of a datum.**  Multiplying a residue by a power of `Γ` multiplies the shape by
the same power: the residue against the Gamma-jet shape is unchanged. -/
theorem tendsto_div_gammaJetShape_of_datum (hσ : 0 < σ) (u : ℕ) {g : ℝ → ℂ} {a p : ℕ} {c : ℂ}
    (h : Tendsto (fun t : ℝ => g t / polyJetShape σ a 0 p t) atTop (nhds c)) :
    Tendsto (fun t : ℝ => (gammaLine σ t ^ u * g t) / gammaJetShape σ u a 0 p t)
      atTop (nhds c) := by
  refine h.congr' ?_
  filter_upwards [eventually_polyJetShape_ne_zero hσ a 0 p] with t hS
  have hΓ : gammaLine σ t ^ u ≠ 0 := pow_ne_zero _ (gammaLine_ne_zero hσ t)
  rw [gammaJetShape]
  field_simp

end GaloisForLFunctions
