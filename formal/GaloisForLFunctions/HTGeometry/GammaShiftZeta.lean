import GaloisForLFunctions.HTGeometry.GammaShiftFinitePhase
import GaloisForLFunctions.HTGeometry.ZetaGammaFieldHypertranscendence

/-!
# Zeta over a real Gamma-shift field

The finite phase law over a shift field bounds the rational Bohr rank of any strip almost periodic
solution of a relation whose coefficients have shifted data.  A Dirichlet series whose frequencies
contain arbitrarily large independent packets has no such bound, so it satisfies no such relation.

The logarithms of the primes are one such packet for `ζ`, which gives eq. (21) of the shifted law
with the coefficients presented by their data.
-/

open Filter Set Topology Function
open scoped BoundedContinuousFunction

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **Infinite rank excludes a shifted-data relation.** -/
theorem no_gammaShift_relation_of_infinite_rank {n N : ℕ} {σ lam R rr ρ : ℝ} (hσ : 0 < σ + lam)
    (hN : 0 < N) (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R) {Φ : ℂ → ℂ}
    (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R)) (hap : IsStripAlmostPeriodic Φ σ R)
    (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e)
    (F : Fin N → ℂ → ℂ) (d : Fin N → ℤ) (ω : Fin N → ℝ) (b : Fin N → ℤ) (c : Fin N → ℂ)
    (hc : ∀ α, c α ≠ 0)
    (hdat : ∀ α, Tendsto (fun t : ℝ => F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      / gammaShiftShape lam σ (d α) (ω α) (b α) t) atTop (nhds (c α)))
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) Φ s) ^ (e α i) = 0)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = Φ ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    (hinf : ∀ K : ℕ, ¬ (Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal))) : False := by
  obtain ⟨K, hK⟩ := rank_finite_of_gammaShift_data hσ hN hr hρ hrρ hR hΦ hap e he F d ω b c hc
    hdat hrel hf hfu hftb
  exact hinf K hK

/-- **A Dirichlet series with arbitrarily large independent frequency packets satisfies no relation
with shifted data.** -/
theorem dirichlet_no_gammaShift_relation {n N : ℕ} {σ lam R rr ρ : ℝ} (hσ : 0 < σ + lam)
    (hN : 0 < N) (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R)
    (a : ℕ → ℂ) (freq : ℕ → ℝ) (D : ℂ → ℂ) (hinj : Function.Injective freq)
    (hD : DifferentiableOn ℂ D (verticalStrip σ R))
    (hconv : ∀ r' : ℝ, r' < R → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ z ∈ closedStrip σ r',
      ‖D z - ∑ i ∈ Finset.range n₀, a i * Complex.exp (-(freq i : ℂ) * z)‖ ≤ ε)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = D ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    (hrank : ∀ K : ℕ, ∃ idx : Fin (K + 1) → ℕ, (∀ i, a (idx i) ≠ 0) ∧
      (∀ i : Fin (K + 1), ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, idx i < n₀ ∧ ∀ t : ℝ,
        ‖D ((σ : ℂ) + (t : ℂ) * Complex.I)
          - ∑ i' ∈ Finset.range n₀,
            a i' * Complex.exp (-(freq i' : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ ε) ∧
      LinearIndependent ℤ (fun i : Fin (K + 1) => -(freq (idx i))))
    (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e)
    (F : Fin N → ℂ → ℂ) (d : Fin N → ℤ) (ω : Fin N → ℝ) (b : Fin N → ℤ) (c : Fin N → ℂ)
    (hc : ∀ α, c α ≠ 0)
    (hdat : ∀ α, Tendsto (fun t : ℝ => F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      / gammaShiftShape lam σ (d α) (ω α) (b α) t) atTop (nhds (c α)))
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) D s) ^ (e α i) = 0) :
    False := by
  have hap : IsStripAlmostPeriodic D σ R := isStripAlmostPeriodic_dirichlet a freq D hconv
  have hDa : _root_.HTGeometry.IsBohrAlmostPeriodic
      fun t : ℝ => D ((σ : ℂ) + (t : ℂ) * Complex.I) := isBohrAlmostPeriodic_line hR hap
  have hinf : ∀ K : ℕ, ¬ (Module.rank ℤ (bohrHullFrequencies f) ≤ (K : Cardinal)) := by
    intro K
    obtain ⟨idx, ha, hm, hind⟩ := hrank K
    exact not_rank_le_of_dirichlet_independent a freq D hinj hf hDa K idx ha hm hind
  exact no_gammaShift_relation_of_infinite_rank hσ hN hr hρ hrρ hR hD hap e he F d ω b c hc
    hdat hrel hf hfu hftb hinf

/-- **Equation (21) of the shifted law.**  On a vertical strip inside `Re s > 1`, zeta satisfies no
nontrivial differential relation whose coefficients have data against the shifted boundary shapes:
the prime logarithms are `ℤ`-independent members of its Bohr spectrum, so its frequency rank exceeds
every natural number, while the shifted finite phase law would bound it. -/
theorem zeta_no_gammaShift_relation {n N : ℕ} {σ lam R rr ρ : ℝ} (hσ : 1 < σ)
    (hlam : 0 < σ + lam) (hN : 0 < N) (hr : 0 < rr) (hρ : 0 < ρ) (hrρ : rr + ρ < R) (hR : 0 < R)
    (hRσ : R ≤ σ - 1)
    (e : Fin N → Fin (n + 1) → ℕ) (he : Function.Injective e)
    (F : Fin N → ℂ → ℂ) (d : Fin N → ℤ) (ω : Fin N → ℝ) (b : Fin N → ℤ) (c : Fin N → ℂ)
    (hc : ∀ α, c α ≠ 0)
    (hdat : ∀ α, Tendsto (fun t : ℝ => F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      / gammaShiftShape lam σ (d α) (ω α) (b α) t) atTop (nhds (c α)))
    (hrel : ∀ s : ℂ,
      ∑ α, F α s * ∏ i : Fin (n + 1), (iteratedDeriv (i : ℕ) riemannZeta s) ^ (e α i) = 0) :
    False := by
  classical
  set A : ℕ → ℂ := fun _ => 1 with hAdef
  set freq : ℕ → ℝ := fun i => Real.log ((i : ℝ) + 1) with hfreqdef
  set f : ℝ →ᵇ ℂ := zetaLine hσ with hfdef
  have hconv : ∀ r' : ℝ, r' < R → ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, ∀ z ∈ closedStrip σ r',
      ‖riemannZeta z - ∑ i ∈ Finset.range n₀,
        A i * Complex.exp (-(freq i : ℂ) * z)‖ ≤ ε := zeta_dirichlet_conv hRσ
  have hD : DifferentiableOn ℂ riemannZeta (verticalStrip σ R) := by
    intro z hz
    have habs : |z.re - σ| < R := hz
    have h1 : σ - R < z.re := by
      have := (abs_lt.mp habs).1
      linarith
    have hne : z ≠ 1 := by
      intro h
      rw [h] at h1
      simp at h1
      linarith
    exact (differentiableAt_riemannZeta hne).differentiableWithinAt
  have hfval : ∀ x : ℝ, f x = riemannZeta ((σ : ℂ) + (x : ℂ) * Complex.I) := fun _ => rfl
  have hfcont : Continuous fun x : ℝ => f x := continuous_zeta_line hσ
  have hap : IsStripAlmostPeriodic riemannZeta σ R :=
    isStripAlmostPeriodic_dirichlet A freq riemannZeta hconv
  have hline : _root_.HTGeometry.IsBohrAlmostPeriodic
      fun t : ℝ => riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I) := isBohrAlmostPeriodic_line hR hap
  have hfap : _root_.HTGeometry.IsBohrAlmostPeriodic fun x : ℝ => f x := hline
  have hfu : UniformContinuous fun x : ℝ => f x :=
    uniformContinuous_of_isBohrAlmostPeriodic hfcont hfap
  have hftb : HasTotallyBoundedOrbit fun x : ℝ => f x :=
    hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hfcont hfap
  have hrank : ∀ K : ℕ, ∃ idx : Fin (K + 1) → ℕ, (∀ i, A (idx i) ≠ 0) ∧
      (∀ i : Fin (K + 1), ∀ ε : ℝ, 0 < ε → ∃ n₀ : ℕ, idx i < n₀ ∧ ∀ t : ℝ,
        ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)
          - ∑ i' ∈ Finset.range n₀,
            A i' * Complex.exp (-(freq i' : ℂ) * ((σ : ℂ) + (t : ℂ) * Complex.I))‖ ≤ ε) ∧
      LinearIndependent ℤ (fun i : Fin (K + 1) => -(freq (idx i))) := by
    intro K
    refine ⟨fun i => nthPrimeIndex (i : ℕ), fun _ => one_ne_zero, ?_, ?_⟩
    · intro i ε hε
      obtain ⟨M, hM⟩ := zeta_uniform_approx (c := σ) hσ hε
      refine ⟨max M (nthPrimeIndex (i : ℕ) + 1), lt_of_lt_of_le (Nat.lt_succ_self _)
        (le_max_right _ _), fun t => ?_⟩
      exact hM _ (le_max_left _ _) _ (by simp)
    · have hfun : (fun i : Fin (K + 1) => -(freq (nthPrimeIndex (i : ℕ))))
          = fun i : Fin (K + 1) => -(Real.log ((Nat.nth Nat.Prime (i : ℕ) : ℕ) : ℝ)) := by
        funext i
        rw [hfreqdef]
        simp only
        rw [nthPrimeIndex_cast]
      rw [hfun]
      exact linearIndependent_neg_log_firstPrimes K
  exact dirichlet_no_gammaShift_relation hlam hN hr hρ hrρ hR A freq riemannZeta
    zetaFrequency_injective hD hconv hfval hfu hftb hrank e he F d ω b c hc hdat hrel

end

end GaloisForLFunctions.HTGeometry
