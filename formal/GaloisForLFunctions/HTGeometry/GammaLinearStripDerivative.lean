import GaloisForLFunctions.HTGeometry.GammaGradedStripCollapse

/-!
# The linear case of the collapse, read on the derivatives themselves

Specializing the graded collapse to the *linear* differential monomials `M_j(f) = f⁽ʲ⁾` turns its
abstract conclusion into a statement about an actual derivative: a holomorphic vertically Bohr
almost-periodic function on a strip that satisfies

`∑_j F_j(s) · f⁽ʲ⁾(s) = 0`

with coefficients in the graded Gamma algebra and a strictly dominant `F_β` has `f⁽ᵝ⁾ ≡ 0` on the
strip.  In particular, for a first-order relation the function is locally constant.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-- The differential monomial of a single derivative is that derivative. -/
theorem diffMonomial_single (f : ℂ → ℂ) (j : ℕ) (s : ℂ) :
    diffMonomial f (Finsupp.single j 1) s = iteratedDeriv j f s := by
  simp [diffMonomial]

/-- **The linear graded collapse, on the derivatives.**  A holomorphic Bohr almost-periodic `f` on
the strip satisfying a linear differential relation with graded coefficients and a strictly dominant
one has the corresponding derivative identically zero. -/
theorem gradedLinear_strip_iteratedDeriv_eq_zero
    {κ : Type*} [DecidableEq κ] (E : Finset ℕ) (P : ℕ → Finset κ)
    {w : ℂ → ℂ} (hw : ∀ x : ℝ, 0 < x → IsVerticalLogWeight w x)
    {σ η : ℝ} (hη : 0 < η) (hση : η ≤ σ) (f : ℂ → ℂ)
    (D : ℕ → κ → GammaRationalDatum) (c : ℕ → κ → Polynomial ℂ) (b : ℕ → κ → ℕ)
    (m : ℕ → κ) (β : ℕ) (hβ : β ∈ E)
    (hm : ∀ α ∈ E, m α ∈ P α)
    (hcm : ∀ α ∈ E, c α (m α) ≠ 0)
    (hinner : ∀ α ∈ E, ∀ q ∈ P α, q ≠ m α →
      StrictlySubordinateAt (D α q) (D α (m α)) (c α q).natDegree (b α q)
        (c α (m α)).natDegree (b α (m α)))
    (houter : ∀ α ∈ E, α ≠ β →
      StrictlySubordinateAt (D α (m α)) (D β (m β)) (c α (m α)).natDegree (b α (m α))
        (c β (m β)).natDegree (b β (m β)))
    (hf : DifferentiableOn ℂ f (openVerticalStrip σ η))
    (hap : ∀ η' : ℝ, 0 < η' → η' < η → HasVerticalUniformReturn (closedVerticalStrip σ η') f)
    (hrel : ∀ s : ℂ, ∑ α ∈ E,
      (∑ q ∈ P α, (D α q).polyWeightedFn (c α q) w (b α q) s) * iteratedDeriv α f s = 0) :
    ∀ z₀ ∈ openVerticalStrip σ η, iteratedDeriv β f z₀ = 0 := by
  have hrel' : ∀ s : ℂ, ∑ α ∈ E,
      (∑ q ∈ P α, (D α q).polyWeightedFn (c α q) w (b α q) s) *
        diffMonomial f (Finsupp.single α 1) s = 0 := by
    intro s
    rw [← hrel s]
    exact Finset.sum_congr rfl fun α _ => by rw [diffMonomial_single]
  intro z₀ hz₀
  have h := gradedSum_strip_relation_dominant_monomial_eq_zero E P hw hη hση f
    (fun α => Finsupp.single α 1) D c b m β hβ hm hcm hinner houter hf hap hrel' z₀ hz₀
  rwa [diffMonomial_single] at h

/-- **The digamma instance.** -/
theorem digammaLinear_strip_iteratedDeriv_eq_zero
    {κ : Type*} [DecidableEq κ] (E : Finset ℕ) (P : ℕ → Finset κ)
    {σ η : ℝ} (hη : 0 < η) (hση : η ≤ σ) (f : ℂ → ℂ)
    (D : ℕ → κ → GammaRationalDatum) (c : ℕ → κ → Polynomial ℂ) (b : ℕ → κ → ℕ)
    (m : ℕ → κ) (β : ℕ) (hβ : β ∈ E)
    (hm : ∀ α ∈ E, m α ∈ P α)
    (hcm : ∀ α ∈ E, c α (m α) ≠ 0)
    (hinner : ∀ α ∈ E, ∀ q ∈ P α, q ≠ m α →
      StrictlySubordinateAt (D α q) (D α (m α)) (c α q).natDegree (b α q)
        (c α (m α)).natDegree (b α (m α)))
    (houter : ∀ α ∈ E, α ≠ β →
      StrictlySubordinateAt (D α (m α)) (D β (m β)) (c α (m α)).natDegree (b α (m α))
        (c β (m β)).natDegree (b β (m β)))
    (hf : DifferentiableOn ℂ f (openVerticalStrip σ η))
    (hap : ∀ η' : ℝ, 0 < η' → η' < η → HasVerticalUniformReturn (closedVerticalStrip σ η') f)
    (hrel : ∀ s : ℂ, ∑ α ∈ E,
      (∑ q ∈ P α, (D α q).polyWeightedFn (c α q) Complex.digamma (b α q) s) *
        iteratedDeriv α f s = 0) :
    ∀ z₀ ∈ openVerticalStrip σ η, iteratedDeriv β f z₀ = 0 :=
  gradedLinear_strip_iteratedDeriv_eq_zero E P
    (fun _x hx => isVerticalLogWeight_digamma hx.le) hη hση f D c b m β hβ hm hcm
    hinner houter hf hap hrel

/-- A first-order dominant relation forces the derivative to vanish, hence `f` is locally constant
on the strip. -/
theorem gradedLinear_strip_deriv_eq_zero
    {κ : Type*} [DecidableEq κ] (E : Finset ℕ) (P : ℕ → Finset κ)
    {w : ℂ → ℂ} (hw : ∀ x : ℝ, 0 < x → IsVerticalLogWeight w x)
    {σ η : ℝ} (hη : 0 < η) (hση : η ≤ σ) (f : ℂ → ℂ)
    (D : ℕ → κ → GammaRationalDatum) (c : ℕ → κ → Polynomial ℂ) (b : ℕ → κ → ℕ)
    (m : ℕ → κ) (hβ : (1 : ℕ) ∈ E)
    (hm : ∀ α ∈ E, m α ∈ P α)
    (hcm : ∀ α ∈ E, c α (m α) ≠ 0)
    (hinner : ∀ α ∈ E, ∀ q ∈ P α, q ≠ m α →
      StrictlySubordinateAt (D α q) (D α (m α)) (c α q).natDegree (b α q)
        (c α (m α)).natDegree (b α (m α)))
    (houter : ∀ α ∈ E, α ≠ 1 →
      StrictlySubordinateAt (D α (m α)) (D 1 (m 1)) (c α (m α)).natDegree (b α (m α))
        (c 1 (m 1)).natDegree (b 1 (m 1)))
    (hf : DifferentiableOn ℂ f (openVerticalStrip σ η))
    (hap : ∀ η' : ℝ, 0 < η' → η' < η → HasVerticalUniformReturn (closedVerticalStrip σ η') f)
    (hrel : ∀ s : ℂ, ∑ α ∈ E,
      (∑ q ∈ P α, (D α q).polyWeightedFn (c α q) w (b α q) s) * iteratedDeriv α f s = 0) :
    ∀ z₀ ∈ openVerticalStrip σ η, deriv f z₀ = 0 := by
  intro z₀ hz₀
  have h := gradedLinear_strip_iteratedDeriv_eq_zero E P hw hη hση f D c b m 1 hβ hm hcm
    hinner houter hf hap hrel z₀ hz₀
  rwa [iteratedDeriv_one] at h

end

end GaloisForLFunctions
