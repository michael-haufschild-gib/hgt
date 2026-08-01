import GaloisForLFunctions.HTGeometry.GammaRationalFinitePhaseRank

/-!
# Observables of a recurrent object

An observable is *dominated* by `f` when its translates are uniformly close whenever the translates
of `f` are: a continuous, translation-equivariant reading of `f`.  Every frequency character of a
dominated observable is then uniformly continuous for the translation distance of `f`, so the
frequency group of the observable sits inside that of `f` and its rational rank is no larger.

Applied to the finite-phase law: every dominated observable of a strip almost periodic solution of a
Gamma-rational differential relation has finite rational Bohr frequency rank — the divisor clause of
the law.  Lipschitz functions of the values are dominated observables, so the class is inhabited.
-/

open Filter Topology Metric Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- An observable whose translation distance is dominated by that of `f`. -/
def IsDominatedObservable (f g : ℝ →ᵇ ℂ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s t : ℝ,
    dist (translateBC s f) (translateBC t f) < δ →
      dist (translateBC s g) (translateBC t g) < ε

/-- **The frequencies of a dominated observable are frequencies of the source.** -/
theorem isBohrHullFrequency_of_dominated {f g : ℝ →ᵇ ℂ} (h : IsDominatedObservable f g)
    {lam : ℝ} (hlam : IsBohrHullFrequency g lam) : IsBohrHullFrequency f lam := by
  rw [IsBohrHullFrequency, Metric.uniformContinuous_iff] at hlam ⊢
  intro ε hε
  obtain ⟨η, hη, hηlt⟩ := hlam ε hε
  obtain ⟨δ, hδ, hδlt⟩ := h η hη
  refine ⟨δ, hδ, fun {s t} hst => ?_⟩
  have hst' : dist (translateBC s.val g) (translateBC t.val g) < η :=
    hδlt s.val t.val (by simpa [BohrLine.dist_eq] using hst)
  exact hηlt (a := BohrLine.of g s.val) (b := BohrLine.of g t.val)
    (by simpa [BohrLine.dist_eq] using hst')

/-- The frequency group of a dominated observable is a subgroup of the source's. -/
theorem bohrHullFrequencies_le_of_dominated {f g : ℝ →ᵇ ℂ} (h : IsDominatedObservable f g) :
    bohrHullFrequencies g ≤ bohrHullFrequencies f := by
  intro lam hlam
  exact isBohrHullFrequency_of_dominated h hlam

/-- **A dominated observable has no larger phase rank.** -/
theorem rank_le_of_dominated {f g : ℝ →ᵇ ℂ} (h : IsDominatedObservable f g) :
    Module.rank ℤ (bohrHullFrequencies g) ≤ Module.rank ℤ (bohrHullFrequencies f) := by
  have hle := bohrHullFrequencies_le_of_dominated h
  have hinj : Function.Injective (AddSubgroup.inclusion hle) :=
    AddSubgroup.inclusion_injective hle
  exact LinearMap.rank_le_of_injective
    ((AddSubgroup.inclusion hle).toIntLinearMap) hinj

/-- A Lipschitz function of the values is a dominated observable. -/
theorem isDominatedObservable_comp {f g : ℝ →ᵇ ℂ} {φ : ℂ → ℂ} {L : NNReal}
    (hφ : LipschitzWith L φ) (hg : ∀ x : ℝ, g x = φ (f x)) : IsDominatedObservable f g := by
  intro ε hε
  refine ⟨ε / (L + 1), by positivity, fun s t hst => ?_⟩
  have hLnn : (0 : ℝ) ≤ (L : ℝ) := L.coe_nonneg
  have hbound : dist (translateBC s g) (translateBC t g)
      ≤ (L : ℝ) * dist (translateBC s f) (translateBC t f) := by
    refine (BoundedContinuousFunction.dist_le (by positivity)).mpr fun x => ?_
    have hx : dist (translateBC s g x) (translateBC t g x)
        ≤ (L : ℝ) * dist (translateBC s f x) (translateBC t f x) := by
      rw [translateBC_apply, translateBC_apply, hg, hg]
      exact hφ.dist_le_mul _ _
    refine hx.trans ?_
    have hle : dist (translateBC s f x) (translateBC t f x)
        ≤ dist (translateBC s f) (translateBC t f) :=
      BoundedContinuousFunction.dist_coe_le_dist x
    exact mul_le_mul_of_nonneg_left hle hLnn
  have hlt : (L : ℝ) * dist (translateBC s f) (translateBC t f) < ε := by
    have h1 : dist (translateBC s f) (translateBC t f) < ε / (L + 1) := hst
    have h2 : (L : ℝ) * dist (translateBC s f) (translateBC t f)
        ≤ ((L : ℝ) + 1) * dist (translateBC s f) (translateBC t f) := by
      have := dist_nonneg (x := translateBC s f) (y := translateBC t f)
      nlinarith
    have h3 : ((L : ℝ) + 1) * dist (translateBC s f) (translateBC t f) < ε := by
      have hpos : (0 : ℝ) < (L : ℝ) + 1 := by positivity
      have hstep : ((L : ℝ) + 1) * dist (translateBC s f) (translateBC t f)
          < ((L : ℝ) + 1) * (ε / ((L : ℝ) + 1)) := by
        exact mul_lt_mul_of_pos_left h1 hpos
      have heq : ((L : ℝ) + 1) * (ε / ((L : ℝ) + 1)) = ε := by field_simp
      linarith
    linarith
  exact lt_of_le_of_lt hbound hlt


/-- **The divisor clause of the finite-phase law.**  Every observable dominated by a strip almost
periodic solution of a Gamma-rational differential relation with distinct monomials has finite
rational Bohr frequency rank. -/
theorem rank_finite_of_dominated_gamma_rational {σ R r ρ : ℝ} {N n : ℕ}
    (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R) (hR : 0 < R) (hσR : R ≤ σ)
    {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic Φ σ R) (e : Fin N → Fin (n + 1) → ℕ) (Cf : Fin N → ℂ → ℂ)
    (pp qq : Fin N → Polynomial ℂ) (u v : Fin N → ℕ) (β : Fin N)
    (hq0 : ∀ α, (qq α).eval 0 ≠ 0) (hp0 : ∀ α, (pp α).eval 0 ≠ 0)
    (hCf : ∀ (α : Fin N), ∀ s ∈ verticalStrip σ R,
      Cf α s = ((Complex.Gamma s) ^ (u α) * (pp α).eval (Complex.Gamma s))
        / ((Complex.Gamma s) ^ (v α) * (qq α).eval (Complex.Gamma s)))
    (hrelC : ∀ s : ℂ,
      ∑ α, Cf α s * ∏ j : Fin (n + 1), (iteratedDeriv (j : ℕ) Φ s) ^ (e α j) = 0)
    (hmin : ∀ α, u β + v α ≤ u α + v β)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    (he : Function.Injective e) {g : ℝ →ᵇ ℂ} (hdom : IsDominatedObservable f g) :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies g) ≤ (K : Cardinal) := by
  obtain ⟨K, hK⟩ := rank_finite_of_gamma_rational_relation hr hρ hrρ hR hσR hΦ hap e Cf pp qq
    u v β hq0 hp0 hCf hrelC hmin hf hfu hftb he
  exact ⟨K, le_trans (rank_le_of_dominated hdom) hK⟩

end GaloisForLFunctions
