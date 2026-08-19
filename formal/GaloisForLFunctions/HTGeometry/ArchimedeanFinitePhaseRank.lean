import GaloisForLFunctions.HTGeometry.ArchimedeanStripCollapse
import GaloisForLFunctions.HTGeometry.PolynomialRelationPhaseRank

/-!
# Finite phase rank over the archimedean field

The autonomous collapse turns a differential relation with archimedean coefficients into a
constant-coefficient polynomial relation whose coefficient at the dominant index is `1`.  Distinct
monomials then make that polynomial nonzero, and a nonzero polynomial relation forces finite
rational Bohr frequency rank.
-/

open Filter Topology MvPolynomial

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The exponent vector of a jet monomial, as a finitely supported function on the jet orders. -/
def jetExpFinsupp {m : ℕ} (ee : Fin m → ℕ) : ℕ →₀ ℕ :=
  Finsupp.onFinset (Finset.range m) (fun j => if h : j < m then ee ⟨j, h⟩ else 0)
    (by
      intro j hj
      by_contra hmem
      rw [Finset.mem_range, not_lt] at hmem
      rw [dif_neg (by omega)] at hj
      exact hj rfl)

theorem jetExpFinsupp_apply {m : ℕ} (ee : Fin m → ℕ) (j : Fin m) :
    jetExpFinsupp ee (j : ℕ) = ee j := by
  rw [jetExpFinsupp]
  simp only [Finsupp.onFinset_apply, j.isLt, dif_pos, Fin.eta]

/-- The jet monomial of an exponent vector is the product over the jet orders. -/
theorem diffMonomial_jetExpFinsupp (f : ℂ → ℂ) {m : ℕ} (ee : Fin m → ℕ) (s : ℂ) :
    diffMonomial f (jetExpFinsupp ee) s
      = ∏ j : Fin m, (iteratedDeriv (j : ℕ) f s) ^ (ee j) := by
  classical
  have hsupp : (jetExpFinsupp ee).support ⊆ Finset.range m := Finsupp.support_onFinset_subset
  rw [diffMonomial, Finset.prod_subset hsupp ?_]
  · rw [← Fin.prod_univ_eq_prod_range
      (fun j : ℕ => (iteratedDeriv j f s) ^ (jetExpFinsupp ee j)) m]
    exact Finset.prod_congr rfl fun j _ => by rw [jetExpFinsupp_apply]
  · intro j _ hj
    rw [Finsupp.notMem_support_iff.mp hj, pow_zero]

/-- **Strip almost periodicity supplies uniform return on every closed substrip.**  The two
formalizations of the card's Bohr hypothesis agree: an almost period in `[N, N+L]` is in particular
a return time past `N`. -/
theorem hasVerticalUniformReturn_of_isStripAlmostPeriodic {Φ : ℂ → ℂ} {σ₀ R : ℝ}
    (hapS : IsStripAlmostPeriodic Φ σ₀ R) {η' : ℝ} (hη' : η' < R) :
    HasVerticalUniformReturn (closedVerticalStrip σ₀ η') Φ := by
  intro ε hε N
  obtain ⟨L, hL, hτ⟩ := hapS η' hη' ε hε
  obtain ⟨τ, hτmem, hτb⟩ := hτ N
  refine ⟨τ, hτmem.1, fun z hz => ?_⟩
  rw [verticalTranslate_apply]
  exact hτb z hz

/-- **Equation (9) over the archimedean field.**  A strip almost periodic holomorphic solution of a
differential relation whose coefficients have archimedean boundary data, with distinct jet monomials,
has finite rational Bohr frequency rank. -/
theorem rank_finite_of_archimedean_relation
    {dd : ℕ} (lam : Fin dd → ℝ) (μ : Fin dd → ℂ) (hlam : ∀ j, 0 < lam j) (hdd : 0 < dd)
    (aexp : ℝ) {σ₀ M r ρ R : ℝ} (hR : 0 < R) (hRσ : R ≤ σ₀) (hM : σ₀ + R ≤ M)
    (hσG : ∀ σ : ℝ, 0 < σ → σ ≤ M → ∀ j, 0 < lam j * σ + (μ j).re)
    (hr : 0 < r) (hρ : 0 < ρ) (hrρ : r + ρ < R)
    {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ₀ R))
    (hapS : IsStripAlmostPeriodic Φ σ₀ R)
    {N m : ℕ} (hN : 0 < N) (e : Fin N → Fin (m + 1) → ℕ) (he : Function.Injective e)
    (F : Fin N → ℂ → ℂ) (k : Fin N → ℤ) (ω : Fin N → ℝ) (b : Fin N → ℤ) (c : Fin N → ℂ)
    (hdat : ∀ a, HasArchimedeanTubeDatum lam μ aexp M (F a) (k a) (ω a) (b a) (c a))
    (hrel : ∀ s : ℂ,
      ∑ a : Fin N, F a s * ∏ j : Fin (m + 1), (iteratedDeriv (j : ℕ) Φ s) ^ (e a j) = 0)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ₀ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)] :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal) := by
  classical
  obtain ⟨β, rrc, hrrβ, hauto⟩ := archimedean_strip_autonomous_relation lam μ hlam hdd aexp
    hR hRσ hM hσG hN Φ (fun a => jetExpFinsupp (e a)) F k ω b c hdat hΦ
    (fun η' _ hlt => hasVerticalUniformReturn_of_isStripAlmostPeriodic hapS hlt)
    (by
      intro s
      simpa only [diffMonomial_jetExpFinsupp] using hrel s)
  refine rank_finite_of_polynomial_relation hr hρ hrρ hΦ hapS hf hfu hftb m
    (∑ a : Fin N, C (rrc a) * ∏ j : Fin (m + 1), (X j : MvPolynomial (Fin (m + 1)) ℂ) ^ (e a j))
    (monomialSum_ne_zero rrc e he β (by rw [hrrβ]; exact one_ne_zero)) ?_
  intro z hz
  have h := hauto z hz
  simp only [diffMonomial_jetExpFinsupp] at h
  simpa [map_sum] using h

end

end GaloisForLFunctions.HTGeometry
