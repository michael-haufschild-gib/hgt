import GaloisForLFunctions.HTGeometry.StripTranslateCurve
import GaloisForLFunctions.HTGeometry.GammaFieldFinitePhaseLaw

/-!
# Uniform limits, and the hypertranscendence consequence

Strip almost periodicity passes to uniform limits on each closed substrip: the classical `ε/3`
argument transports a relatively dense set of almost periods from an approximant to the limit.  This
is what makes uniformly convergent series — exponential sums, Dirichlet series — members of the class
the finite-phase law governs.

Read contrapositively, the law says that a holomorphic strip almost periodic function of *infinite*
rational Bohr frequency rank satisfies no differential relation with Gamma-field coefficients: it is
hypertranscendental over `ℂ(s)⟨Γ⟩`.
-/

open Filter Topology Complex

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- **Uniform limits of strip almost periodic functions are strip almost periodic.** -/
theorem isStripAlmostPeriodicOn_of_uniform_approx {F : ℂ → ℂ} {σ r : ℝ}
    (h : ∀ ε : ℝ, 0 < ε → ∃ G : ℂ → ℂ, IsStripAlmostPeriodicOn G σ r ∧
      ∀ z ∈ closedStrip σ r, ‖F z - G z‖ ≤ ε) :
    IsStripAlmostPeriodicOn F σ r := by
  intro ε hε
  obtain ⟨G, hGap, hGclose⟩ := h (ε / 3) (by linarith)
  obtain ⟨L, hL, hdense⟩ := hGap (ε / 3) (by linarith)
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτ⟩ := hdense a
  refine ⟨τ, hτmem, fun z hz => ?_⟩
  have hzs : z ∈ closedStrip σ r := hz
  have hzτ : z + (τ : ℂ) * Complex.I ∈ closedStrip σ r :=
    mem_closedStrip_add_I σ r z hzs τ
  have h1 : ‖F (z + (τ : ℂ) * Complex.I) - G (z + (τ : ℂ) * Complex.I)‖ ≤ ε / 3 :=
    hGclose _ hzτ
  have h2 : ‖G (z + (τ : ℂ) * Complex.I) - G z‖ ≤ ε / 3 := hτ z hz
  have h3 : ‖F z - G z‖ ≤ ε / 3 := hGclose z hzs
  have hsplit : F (z + (τ : ℂ) * Complex.I) - F z
      = (F (z + (τ : ℂ) * Complex.I) - G (z + (τ : ℂ) * Complex.I))
        + (G (z + (τ : ℂ) * Complex.I) - G z) + (G z - F z) := by ring
  have hnorm3 : ‖G z - F z‖ = ‖F z - G z‖ := by
    rw [← norm_neg]
    congr 1
    ring
  calc ‖F (z + (τ : ℂ) * Complex.I) - F z‖
      ≤ ‖(F (z + (τ : ℂ) * Complex.I) - G (z + (τ : ℂ) * Complex.I))
          + (G (z + (τ : ℂ) * Complex.I) - G z)‖ + ‖G z - F z‖ := by
        rw [hsplit]
        exact norm_add_le _ _
    _ ≤ ‖F (z + (τ : ℂ) * Complex.I) - G (z + (τ : ℂ) * Complex.I)‖
          + ‖G (z + (τ : ℂ) * Complex.I) - G z‖ + ‖G z - F z‖ := by
        gcongr
        exact norm_add_le _ _
    _ ≤ ε / 3 + ε / 3 + ε / 3 := by
        rw [hnorm3]
        gcongr
    _ = ε := by ring

/-- The strip version: uniform approximation on every closed substrip. -/
theorem isStripAlmostPeriodic_of_uniform_approx {F : ℂ → ℂ} {σ R : ℝ}
    (h : ∀ r : ℝ, r < R → ∀ ε : ℝ, 0 < ε → ∃ G : ℂ → ℂ, IsStripAlmostPeriodicOn G σ r ∧
      ∀ z ∈ closedStrip σ r, ‖F z - G z‖ ≤ ε) :
    IsStripAlmostPeriodic F σ R :=
  fun r hr => isStripAlmostPeriodicOn_of_uniform_approx (h r hr)

/-- **Eq. (31), the contrapositive form.**  A holomorphic strip almost periodic function of infinite
rational Bohr frequency rank satisfies no differential relation with Gamma-field coefficients: it is
hypertranscendental over `ℂ(s)⟨Γ⟩`. -/
theorem no_gammaField_relation_of_infinite_rank {n N k r : ℕ} {σ R rr ρ : ℝ} (hσ : 0 < σ)
    (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (hap : IsStripAlmostPeriodic Φ σ R)
    (e : Fin N → Fin (n + 1) → ℕ) (F : Fin N → ℂ → ℂ)
    (j : Fin N → Fin k → ℕ) (p q : Fin N → Fin k → Polynomial ℂ)
    (E : Fin N → Fin k → Fin (r + 1) → ℕ)
    (jb : ℕ) (pb qb : Polynomial ℂ) (Db : ℕ)
    (hq : ∀ a i, q a i ≠ 0) (hqb : qb ≠ 0) (hpb : pb ≠ 0)
    (hdom : ∀ a i, GammaMonomialDominates (j a i) (p a i) (q a i) (E a i 0) jb pb qb Db)
    (β : Fin N)
    (hc : (∑ i, gammaJetLimit (j β i) (p β i) (q β i) (E β i) jb pb qb Db) ≠ 0)
    (hF : ∀ (α : Fin N) (t : ℝ),
      F α ((σ : ℂ) + (t : ℂ) * Complex.I)
        = ∑ i, gammaJetEltG σ (j α i) (p α i) (q α i) (E α i) t)
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i) = 0)
    (he : Function.Injective e)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    (hinf : ∀ K : ℕ, ¬ (Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal))) : False := by
  obtain ⟨-, -, hrank⟩ := gammaField_finite_phase_law hσ hr hρ hrρ hR hΦ hap e F j p q E
    jb pb qb Db hq hqb hpb hdom β hc hF hrel he hf hfu hftb
  obtain ⟨K, hK⟩ := hrank
  exact hinf K hK

end GaloisForLFunctions
