import GaloisForLFunctions.HTGeometry.VerticalStripBohrHull
import GaloisForLFunctions.HTGeometry.GammaJetProjectiveBoundary

/-!
# Unconditional finite-phase collapse against the Gamma jet tuple

The finite-phase theorem says that a holomorphic vertically almost-periodic function constrained by
finitely many Gamma-differential coefficients already satisfies a constant-coefficient algebraic
differential relation.  Two of its three inputs are now theorems rather than hypotheses: the
local-uniform translate return comes from the Bohr hull of the strip, and, for the canonical Gamma
jet tuple `(Γ, Γ', …, Γ⁽ʳ⁾)`, the one-point projective boundary is the all-orders Gamma-jet estimate
`Γ⁽ⁱ⁾/Γ⁽ʳ⁾ → 0`.

Combining them gives a collapse with no analytic hypotheses left at all.  The limiting autonomous
relation has coefficient vector `(0, …, 0, 1)`, so it says exactly that the differential monomial
attached to the *top* Gamma derivative vanishes identically on the strip: no vertically
almost-periodic holomorphic function admits a Gamma-jet differential relation whose top monomial is
somewhere nonzero.
-/

open Filter Topology

namespace GaloisForLFunctions

noncomputable section

open scoped BigOperators

/-- Every derivative of `Γ` is eventually nonzero along an upper vertical line in the open right
half-plane: `Γ` has no zero there, and the digamma Bell value has leading term `ψⁿ`, which is
eventually nonzero because `‖ψ‖ → ∞`. -/
theorem eventually_iteratedDeriv_Gamma_vertical_ne_zero (r : ℕ) {x : ℝ} (hx : 0 < x) :
    ∀ᶠ u : ℝ in atTop, iteratedDeriv r Complex.Gamma ((x : ℂ) + (u : ℂ) * Complex.I) ≠ 0 := by
  have hB := bellVal_div_pow_tendsto_one r hx
  have hbne : ∀ᶠ u : ℝ in atTop, bellVal r ((x : ℂ) + (u : ℂ) * Complex.I) ≠ 0 := by
    have hb := hB.eventually (isOpen_ne.mem_nhds (show (1 : ℂ) ≠ 0 by norm_num))
    filter_upwards [hb] with u hu
    intro h
    rw [h, zero_div] at hu
    exact hu rfl
  filter_upwards [hbne] with u hu
  have hpoles : ∀ p : ℕ, ((x : ℂ) + (u : ℂ) * Complex.I) ≠ -(p : ℂ) := by
    intro p heq
    have hre := congrArg Complex.re heq
    simp at hre
    linarith [Nat.cast_nonneg (α := ℝ) p]
  have hΓ : Complex.Gamma ((x : ℂ) + (u : ℂ) * Complex.I) ≠ 0 := Complex.Gamma_ne_zero hpoles
  rw [gamma_iteratedDeriv_eq_gamma_mul_eval_gammaBell r _ hpoles]
  exact mul_ne_zero hΓ hu

/-- The Gamma-jet projective boundary read along a vertical return sequence based at any point of
positive abscissa: `Γ⁽ⁱ⁾(z₀ + iT_l) / Γ⁽ʳ⁾(z₀ + iT_l) → 0` for `i < r`. -/
theorem tendsto_iteratedDeriv_Gamma_ratio_along_returns
    (i r : ℕ) (hir : i < r) {z₀ : ℂ} (hz : 0 < z₀.re) {T : ℕ → ℝ}
    (hT : Tendsto T atTop atTop) :
    Tendsto (fun l => iteratedDeriv i Complex.Gamma (z₀ + (T l : ℂ) * Complex.I) /
      iteratedDeriv r Complex.Gamma (z₀ + (T l : ℂ) * Complex.I)) atTop (nhds 0) := by
  have hshift : Tendsto (fun l : ℕ => z₀.im + T l) atTop atTop :=
    tendsto_atTop_add_const_left _ _ hT
  have hcomp :=
    (iteratedDeriv_Gamma_div_higher_vertical_tendsto_zero i r hir hz).comp hshift
  refine hcomp.congr (fun l => ?_)
  simp only [Function.comp_apply]
  rw [add_mul_I_eq_ofReal_re_add z₀ (T l)]

/-- The top Gamma derivative is eventually nonzero along a vertical return sequence based at a point
of positive abscissa. -/
theorem eventually_iteratedDeriv_Gamma_ne_zero_along_returns (r : ℕ) {z₀ : ℂ} (hz : 0 < z₀.re)
    {T : ℕ → ℝ} (hT : Tendsto T atTop atTop) :
    ∀ᶠ l in atTop, iteratedDeriv r Complex.Gamma (z₀ + (T l : ℂ) * Complex.I) ≠ 0 := by
  have hshift : Tendsto (fun l : ℕ => z₀.im + T l) atTop atTop :=
    tendsto_atTop_add_const_left _ _ hT
  have hev := hshift.eventually (eventually_iteratedDeriv_Gamma_vertical_ne_zero r hz)
  filter_upwards [hev] with l hl
  rw [add_mul_I_eq_ofReal_re_add z₀ (T l)]
  exact hl

/-- **Unconditional Gamma-jet finite-phase collapse (§5, eq. 8, jet coefficients).**  Let `f` be
holomorphic on the open vertical strip of half-width `η ≤ σ` about `σ`, and Bohr almost periodic
there: on every closed substrip its vertical translates return to it uniformly at arbitrarily late
times.  If `f` satisfies a differential relation whose coefficients are the Gamma jet tuple,
`∑_{i ≤ r} Γ⁽ⁱ⁾ · M_i(f) = 0`, then the top monomial vanishes identically on the strip:
`M_r(f) = 0`.

The Gamma jet tuple has the one-point projective boundary `(0, …, 0, 1)`, so the autonomous relation
produced by the recurrence collapse is `M_r(f) = 0` itself.  No analytic input remains hypothetical:
the return times come from almost periodicity and the coefficient boundary is the Gamma-jet
estimate. -/
theorem gammaJet_vertical_relation_top_monomial_eq_zero
    {σ η : ℝ} (hη : 0 < η) (hση : η ≤ σ) (f : ℂ → ℂ) (r : ℕ) (exps : Fin (r + 1) → (ℕ →₀ ℕ))
    (hf : DifferentiableOn ℂ f (openVerticalStrip σ η))
    (hap : ∀ η' : ℝ, 0 < η' → η' < η → HasVerticalUniformReturn (closedVerticalStrip σ η') f)
    (hrel : ∀ s : ℂ, ∑ i : Fin (r + 1),
      iteratedDeriv (i : ℕ) Complex.Gamma s * diffMonomial f (exps i) s = 0) :
    ∀ z₀ ∈ openVerticalStrip σ η, diffMonomial f (exps (Fin.last r)) z₀ = 0 := by
  obtain ⟨T, hT, hmain⟩ :=
    verticalStrip_recurrence_collapse (Finset.univ : Finset (Fin (r + 1))) hη f exps
      (fun i => iteratedDeriv (i : ℕ) Complex.Gamma) (Fin.last r) (Finset.mem_univ _) hf hap hrel
  intro z₀ hz₀
  have hzre : 0 < z₀.re := by
    have habs : |z₀.re - σ| < η := hz₀
    have hlt := (abs_lt.mp habs).1
    linarith
  have hFβ : ∀ᶠ l in atTop,
      iteratedDeriv ((Fin.last r : Fin (r + 1)) : ℕ) Complex.Gamma
        (z₀ + (T l : ℂ) * Complex.I) ≠ 0 := by
    simpa only [Fin.val_last] using
      eventually_iteratedDeriv_Gamma_ne_zero_along_returns r hzre hT
  have hcoeff : ∀ i ∈ (Finset.univ : Finset (Fin (r + 1))), Tendsto
      (fun l => iteratedDeriv (i : ℕ) Complex.Gamma (z₀ + (T l : ℂ) * Complex.I) /
        iteratedDeriv ((Fin.last r : Fin (r + 1)) : ℕ) Complex.Gamma
          (z₀ + (T l : ℂ) * Complex.I))
      atTop (nhds (if i = Fin.last r then (1 : ℂ) else 0)) := by
    intro i _
    rcases eq_or_ne i (Fin.last r) with hi | hi
    · subst hi
      have hone : Tendsto
          (fun l => iteratedDeriv ((Fin.last r : Fin (r + 1)) : ℕ) Complex.Gamma
              (z₀ + (T l : ℂ) * Complex.I) /
            iteratedDeriv ((Fin.last r : Fin (r + 1)) : ℕ) Complex.Gamma
              (z₀ + (T l : ℂ) * Complex.I))
          atTop (nhds (1 : ℂ)) := by
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hFβ] with l hl
        exact (div_self hl).symm
      simpa using hone
    · have hlt : (i : ℕ) < r := by
        have hle : (i : ℕ) < r + 1 := i.is_lt
        rcases Nat.lt_or_ge (i : ℕ) r with h | h
        · exact h
        · exfalso
          apply hi
          apply Fin.val_injective
          rw [Fin.val_last]
          omega
      simpa [hi, Fin.val_last] using
        tendsto_iteratedDeriv_Gamma_ratio_along_returns (i : ℕ) r hlt hzre hT
  have hcollapse := hmain z₀ hz₀ (fun i => if i = Fin.last r then (1 : ℂ) else 0) hFβ hcoeff
  have hred := Finset.sum_eq_single_of_mem (Fin.last r) (Finset.mem_univ _)
    (f := fun i : Fin (r + 1) =>
      (if i = Fin.last r then (1 : ℂ) else 0) * diffMonomial f (exps i) z₀)
    (by
      intro b _ hb
      simp [hb])
  have hzero := hcollapse.1
  rw [hred] at hzero
  simpa using hzero

end

end GaloisForLFunctions
