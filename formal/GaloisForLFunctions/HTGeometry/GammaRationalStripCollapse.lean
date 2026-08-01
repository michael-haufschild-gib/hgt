import GaloisForLFunctions.HTGeometry.GammaRationalJetCollapse

/-!
# The autonomous relation holds on the whole strip

The limit coefficient vector of a Gamma-rational relation does not depend on the vertical line along
which the collapse is taken, so the collapsed relation holds at the centre of every vertical line
inside the strip.  Almost periodicity is inherited by every concentric substrip, so every such centre
is admissible, and the collapsed relation therefore vanishes on a real segment.  Being holomorphic on
a convex strip, it vanishes identically.

This is eq. (8): a strip almost periodic holomorphic function that is differentially algebraic over
the Gamma field is differentially algebraic over the constants, with the explicit constant relation
`gammaRatioLimit` and the normalization `gammaRatioLimit β = 1` witnessing nontriviality.
-/

open Filter Topology

namespace GaloisForLFunctions

open _root_.HTGeometry

variable {σ R : ℝ}

/-- A concentric substrip of a strip of half-width `R` centred at `σ'` sits inside the original. -/
theorem verticalStrip_shift_subset (σ' : ℝ) :
    verticalStrip σ' (R - |σ' - σ|) ⊆ verticalStrip σ R := by
  intro z hz
  simp only [verticalStrip, Set.mem_setOf_eq] at hz ⊢
  have := abs_sub_abs_le_abs_sub (z.re - σ) (σ' - σ)
  have h2 : |z.re - σ| ≤ |z.re - σ'| + |σ' - σ| := by
    have : z.re - σ = (z.re - σ') + (σ' - σ) := by ring
    rw [this]
    exact abs_add_le _ _
  linarith

/-- Strip almost periodicity is inherited by every strip centred at another interior point. -/
theorem isStripAlmostPeriodic_shift {F : ℂ → ℂ} (hap : IsStripAlmostPeriodic F σ R)
    (σ' : ℝ) : IsStripAlmostPeriodic F σ' (R - |σ' - σ|) := by
  intro r hr ε hε
  obtain ⟨L, hL, hτ⟩ := hap (r + |σ' - σ|) (by linarith) ε hε
  refine ⟨L, hL, fun a => ?_⟩
  obtain ⟨τ, hτmem, hτb⟩ := hτ a
  refine ⟨τ, hτmem, fun z hz => hτb z ?_⟩
  have h2 : |z.re - σ| ≤ |z.re - σ'| + |σ' - σ| := by
    have : z.re - σ = (z.re - σ') + (σ' - σ) := by ring
    rw [this]
    exact abs_add_le _ _
  linarith

/-- **Eq. (8): the collapsed relation holds identically on the strip.**  A strip almost periodic
holomorphic solution of a Gamma-rational differential relation satisfies the constant-coefficient
relation with coefficient vector `gammaRatioLimit` at every point of the strip. -/
theorem gamma_rational_autonomous_relation {n m : ℕ} (hR : 0 < R) (hσR : R ≤ σ)
    {Φ : ℂ → ℂ} (hΦ : DifferentiableOn ℂ Φ (verticalStrip σ R))
    (hap : IsStripAlmostPeriodic Φ σ R) (e : Fin n → Fin m → ℕ)
    (F : Fin n → ℂ → ℂ) (P Q : Fin n → Polynomial ℂ) (u v : Fin n → ℕ) (β : Fin n)
    (hQ0 : ∀ α, (Q α).eval 0 ≠ 0) (hP0 : ∀ α, (P α).eval 0 ≠ 0)
    (hF : ∀ (α : Fin n), ∀ s ∈ verticalStrip σ R,
      F α s = ((Complex.Gamma s) ^ (u α) * (P α).eval (Complex.Gamma s))
        / ((Complex.Gamma s) ^ (v α) * (Q α).eval (Complex.Gamma s)))
    (hrel : ∀ s : ℂ, ∑ α, F α s * ∏ j : Fin m, (iteratedDeriv (j : ℕ) Φ s) ^ (e α j) = 0)
    (hmin : ∀ α, u β + v α ≤ u α + v β) :
    Set.EqOn (fun s : ℂ => ∑ α, gammaRatioLimit P Q u v β α *
        ∏ j : Fin m, (iteratedDeriv (j : ℕ) Φ s) ^ (e α j)) 0 (verticalStrip σ R) := by
  classical
  set G : ℂ → ℂ := fun s => ∑ α, gammaRatioLimit P Q u v β α *
    ∏ j : Fin m, (iteratedDeriv (j : ℕ) Φ s) ^ (e α j) with hGdef
  -- `G` is holomorphic on the strip
  have hjet : ∀ j : ℕ, DifferentiableOn ℂ (iteratedDeriv j Φ) (verticalStrip σ R) :=
    differentiableOn_iteratedDeriv_verticalStrip hΦ
  have hprod : ∀ α : Fin n, DifferentiableOn ℂ
      (fun s : ℂ => ∏ j : Fin m, (iteratedDeriv (j : ℕ) Φ s) ^ (e α j)) (verticalStrip σ R) := by
    intro α
    have h1 : DifferentiableOn ℂ
        (∏ j : Fin m, fun s : ℂ => (iteratedDeriv (j : ℕ) Φ s) ^ (e α j)) (verticalStrip σ R) :=
      DifferentiableOn.finsetProd fun (j : Fin m) _ => (hjet (j : ℕ)).pow (e α j)
    have h2 : (∏ j : Fin m, fun s : ℂ => (iteratedDeriv (j : ℕ) Φ s) ^ (e α j))
        = fun s : ℂ => ∏ j : Fin m, (iteratedDeriv (j : ℕ) Φ s) ^ (e α j) := by
      funext s
      simp [Finset.prod_apply]
    rwa [h2] at h1
  have hG : DifferentiableOn ℂ G (verticalStrip σ R) := by
    have h1 : DifferentiableOn ℂ
        (∑ α : Fin n, fun s : ℂ => gammaRatioLimit P Q u v β α *
          ∏ j : Fin m, (iteratedDeriv (j : ℕ) Φ s) ^ (e α j)) (verticalStrip σ R) :=
      DifferentiableOn.sum fun α _ => (hprod α).const_mul _
    have h2 : (∑ α : Fin n, fun s : ℂ => gammaRatioLimit P Q u v β α *
        ∏ j : Fin m, (iteratedDeriv (j : ℕ) Φ s) ^ (e α j)) = G := by
      funext s
      simp [hGdef, Finset.sum_apply]
    rwa [h2] at h1
  -- `G` vanishes at every real point of the strip
  have hzero : ∀ σ' : ℝ, |σ' - σ| < R → G (σ' : ℂ) = 0 := by
    intro σ' hσ'
    have hpos : 0 < σ' := by
      have := abs_lt.mp hσ'
      linarith [this.1]
    have hr' : 0 < R - |σ' - σ| := by linarith
    have hsub := verticalStrip_shift_subset (σ := σ) (R := R) σ'
    have hΦ' : DifferentiableOn ℂ Φ (verticalStrip σ' (R - |σ' - σ|)) := hΦ.mono hsub
    have hap' : IsStripAlmostPeriodic Φ σ' (R - |σ' - σ|) := isStripAlmostPeriodic_shift hap σ'
    have hmem : ∀ t : ℝ, ((σ' : ℂ) + (t : ℂ) * Complex.I) ∈ verticalStrip σ R := by
      intro t
      have hre : ((σ' : ℂ) + (t : ℂ) * Complex.I).re = σ' := by simp
      simpa [verticalStrip, hre] using hσ'
    have hF' : ∀ (α : Fin n) (t : ℝ),
        F α ((σ' : ℂ) + (t : ℂ) * Complex.I)
          = ((Complex.Gamma ((σ' : ℂ) + (t : ℂ) * Complex.I)) ^ (u α)
              * (P α).eval (Complex.Gamma ((σ' : ℂ) + (t : ℂ) * Complex.I)))
            / ((Complex.Gamma ((σ' : ℂ) + (t : ℂ) * Complex.I)) ^ (v α)
              * (Q α).eval (Complex.Gamma ((σ' : ℂ) + (t : ℂ) * Complex.I))) :=
      fun α t => hF α _ (hmem t)
    exact (recurrence_collapse_gamma_rational_jets_explicit hpos hr' hΦ' hap' e F P Q u v β
      hQ0 hP0 hF' hrel hmin).1
  -- the zeros accumulate at the centre, so `G` vanishes identically
  have hcentre : ((σ : ℝ) : ℂ) ∈ verticalStrip σ R := by
    simp [verticalStrip, hR]
  have hsmall : ∀ᶠ k : ℕ in atTop, (1 : ℝ) / ((k : ℝ) + 1) < R :=
    tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hR)
  have hpos1 : ∀ k : ℕ, (0 : ℝ) < 1 / ((k : ℝ) + 1) := by
    intro k
    positivity
  have hseq : Tendsto (fun k : ℕ => ((σ + 1 / ((k : ℝ) + 1) : ℝ) : ℂ)) atTop
      (𝓝[≠] ((σ : ℝ) : ℂ)) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have hreal : Tendsto (fun k : ℕ => (σ + 1 / ((k : ℝ) + 1) : ℝ)) atTop (𝓝 σ) := by
        have hconst : Tendsto (fun _ : ℕ => σ) atTop (𝓝 σ) := tendsto_const_nhds
        simpa using hconst.add (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
      exact (Complex.continuous_ofReal.tendsto σ).comp hreal
    · filter_upwards with k
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Complex.ofReal_inj]
      have := hpos1 k
      intro hcon
      linarith [hcon]
  have hfreq : ∃ᶠ z in 𝓝[≠] ((σ : ℝ) : ℂ), G z = 0 := by
    refine hseq.frequently (Filter.Eventually.frequently ?_)
    filter_upwards [hsmall] with k hk
    refine hzero (σ + 1 / ((k : ℝ) + 1)) ?_
    have : σ + 1 / ((k : ℝ) + 1) - σ = 1 / ((k : ℝ) + 1) := by ring
    rw [this, abs_of_pos (hpos1 k)]
    exact hk
  exact (hG.analyticOnNhd (isOpen_verticalStrip σ R)).eqOn_zero_of_preconnected_of_frequently_eq_zero
    ((convex_verticalStrip σ R).isPreconnected) hcentre hfreq

end GaloisForLFunctions
