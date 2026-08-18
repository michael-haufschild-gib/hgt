import GaloisForLFunctions.RHTower.SteinhausLogTailMoment
import GaloisForLFunctions.HTGeometry.MeromorphicBoundaryLog
import GaloisForLFunctions.HTGeometry.HelsonZetaEulerProduct
import GaloisForLFunctions.HTGeometry.HelsonStratumMeasurable

/-!
# The Euler exponent of a random Helson zeta, and its boundary envelope

For a point of the Steinhaus phase space write

```text
E_ω(s) = ∑_p χ_ω(p) p^{-s} + ∑_p logTail(χ_ω(p) p^{-s}) .
```

Almost surely both layers are holomorphic on `Re s > 1/2` — the first by Kolmogorov's convergence
criterion, the second unconditionally — and on `Re s > 1` the Euler product of `χ_ω` is exactly
`exp E_ω`.  So if the phase lies in the continuation stratum, the meromorphic continuation `F`
satisfies `F = exp E_ω` on `Re s > 1`, and the boundary envelope theorem applies:

```text
| Re E_ω(σ) - m log(σ - 1/2) |  ≤  B        on some (1/2, 1/2 + δ) .
```

The real part is recorded through a `limsup`, which is measurable without any convergence
hypothesis and agrees with the true value on the full-measure convergence event; and the whole
quantity changes by a bounded amount, uniformly in `σ ≥ 1/2`, when finitely many phases are
modified.  Those two facts are what make the boundary envelope a *tail* event.
-/

noncomputable section

open MeasureTheory Filter Topology Complex GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.RHTower

open _root_.RHTower.SteinhausModel

/-- The unimodular phase of a point of the Steinhaus space, as a point of the phase torus. -/
def phaseTorusOf (ω : Omega) : PhaseTorus := fun p => ⟨X (p : ℕ) ω, norm_X _ _⟩

@[simp] theorem phaseTorusOf_coe (ω : Omega) (p : Nat.Primes) :
    ((phaseTorusOf ω p : ℂ)) = helsonPhaseOf ω p := rfl

/-- The Euler exponent of the random phase. -/
def helsonExponent (ω : Omega) (s : ℂ) : ℂ :=
  dirichletSum (primePhaseCoeff ω) s + helsonLogTail (helsonPhaseOf ω) s

theorem differentiableOn_helsonExponent {ω : Omega} (hω : ω ∈ primeHolomorphicEvent) :
    DifferentiableOn ℂ (helsonExponent ω) {s : ℂ | 1 / 2 < s.re} :=
  (differentiableOn_dirichletSum_primePhaseCoeff hω).add
    (differentiableOn_helsonLogTail (norm_helsonPhaseOf_le ω))

theorem hasProd_helsonExponent (ω : Omega) {s : ℂ} (hs : 1 < s.re) :
    HasProd (fun p : Nat.Primes => (1 - helsonPhaseOf ω p * ((p : ℕ) : ℂ) ^ (-s))⁻¹)
      (Complex.exp (helsonExponent ω s)) :=
  hasProd_helsonEuler_exp (norm_helsonPhaseOf_le ω) hs (hasSum_primePhase_dirichletSum hs)

/-- The event that the phase lies in the continuation stratum. -/
def contEvent : Set Omega := phaseTorusOf ⁻¹' continuableStratum

/-- **The boundary envelope for a continuable random phase.** -/
theorem exists_boundary_bound {ω : Omega} (hcont : ω ∈ contEvent)
    (hω : ω ∈ primeHolomorphicEvent) :
    ∃ (m : ℤ) (δ B : ℝ), 0 < δ ∧ ∀ σ : ℝ, 1 / 2 < σ → σ < 1 / 2 + δ →
      |(helsonExponent ω ((σ : ℝ) : ℂ)).re - (m : ℝ) * Real.log (σ - 1 / 2)| ≤ B := by
  obtain ⟨F, hFmero, hFprod⟩ := hcont
  refine exists_boundary_log_bound hFmero (differentiableOn_helsonExponent hω) ?_
  intro s hs
  exact (hFprod s hs).unique (hasProd_helsonExponent ω hs)


/-! ### A measurable version of the real part -/

theorem convergesAt_primePhaseCoeff_of_gt {ω : Omega} (hω : ω ∈ primeHolomorphicEvent)
    {s : ℂ} (hs : 1 / 2 < s.re) : DirichletConvergesAt (primePhaseCoeff ω) s := by
  obtain ⟨j, hj⟩ : ∃ j : ℕ, 1 / ((j : ℝ) + 1) < s.re - 1 / 2 :=
    exists_nat_one_div_lt (by linarith : (0:ℝ) < s.re - 1 / 2)
  have hconv : DirichletConvergesAt (primePhaseCoeff ω)
      (((1 / 2 + 1 / ((j : ℝ) + 1) : ℝ) : ℂ)) :=
    convergesAt_primePhaseCoeff (Set.mem_iInter.mp hω j)
  refine tendsto_dirichlet_partialSum_of_re_lt hconv ?_
  rw [Complex.ofReal_re]
  linarith

/-- The real part of the Euler exponent, recorded through a `limsup` so that it is measurable
without any convergence hypothesis. -/
def eulerExponentRe (σ : ℝ) (ω : Omega) : ℝ :=
  Filter.limsup (fun N => (dirichletPartialSum (primePhaseCoeff ω) N ((σ : ℝ) : ℂ)).re)
      Filter.atTop
    + (helsonLogTail (helsonPhaseOf ω) ((σ : ℝ) : ℂ)).re

theorem measurable_primePhaseCoeff (n : ℕ) : Measurable fun ω : Omega => primePhaseCoeff ω n := by
  show Measurable fun ω : Omega => if (n + 1).Prime then X (n + 1) ω else 0
  by_cases h : (n + 1).Prime
  · simp only [if_pos h]
    exact measurable_X (n + 1)
  · simp only [if_neg h]
    exact measurable_const

theorem measurable_dirichletPartialSum_re (σ : ℝ) (N : ℕ) :
    Measurable fun ω : Omega => (dirichletPartialSum (primePhaseCoeff ω) N ((σ : ℝ) : ℂ)).re := by
  refine Complex.measurable_re.comp ?_
  refine Finset.measurable_sum _ fun n _ => ?_
  exact (measurable_primePhaseCoeff n).mul measurable_const

theorem measurable_eulerExponentRe {σ : ℝ} (hσ : 1 / 2 < σ) : Measurable (eulerExponentRe σ) :=
  (Measurable.limsup fun N => measurable_dirichletPartialSum_re σ N).add
    (Complex.measurable_re.comp (measurable_logTailSum hσ))

theorem eulerExponentRe_eq {ω : Omega} (hω : ω ∈ primeHolomorphicEvent) {σ : ℝ}
    (hσ : 1 / 2 < σ) :
    eulerExponentRe σ ω = (helsonExponent ω ((σ : ℝ) : ℂ)).re := by
  have hconv : DirichletConvergesAt (primePhaseCoeff ω) ((σ : ℝ) : ℂ) := by
    refine convergesAt_primePhaseCoeff_of_gt hω ?_
    rw [Complex.ofReal_re]
    exact hσ
  have htend : Filter.Tendsto
      (fun N => (dirichletPartialSum (primePhaseCoeff ω) N ((σ : ℝ) : ℂ)).re) Filter.atTop
      (nhds ((dirichletSum (primePhaseCoeff ω) ((σ : ℝ) : ℂ)).re)) :=
    (Complex.continuous_re.tendsto _).comp (tendsto_dirichletSum hconv)
  rw [eulerExponentRe, htend.limsup_eq, helsonExponent, Complex.add_re]


/-! ### Finite modification changes the exponent by a bounded amount -/

theorem primePhaseCoeff_eq_of_coord_eq {ω ω' : Omega} {n : ℕ} (h : ω (n + 1) = ω' (n + 1)) :
    primePhaseCoeff ω n = primePhaseCoeff ω' n := by
  show (if (n + 1).Prime then X (n + 1) ω else 0)
    = (if (n + 1).Prime then X (n + 1) ω' else 0)
  by_cases hp : (n + 1).Prime
  · rw [if_pos hp, if_pos hp, X_prime_eq hp, X_prime_eq hp, h]
  · rw [if_neg hp, if_neg hp]

theorem helsonPhaseOf_eq_of_coord_eq {ω ω' : Omega} {p : Nat.Primes}
    (h : ω (p : ℕ) = ω' (p : ℕ)) : helsonPhaseOf ω p = helsonPhaseOf ω' p := by
  rw [helsonPhaseOf, helsonPhaseOf, X_prime_eq p.2, X_prime_eq p.2, h]

/-- The prime layer changes by a fixed finite sum. -/
theorem dirichletSum_sub_of_finiteModification {ω ω' : Omega}
    (hfin : {n : ℕ | ω n ≠ ω' n}.Finite)
    (hω : ω ∈ primeHolomorphicEvent) (hω' : ω' ∈ primeHolomorphicEvent) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, 1 / 2 < σ →
      ‖dirichletSum (primePhaseCoeff ω) ((σ : ℝ) : ℂ)
        - dirichletSum (primePhaseCoeff ω') ((σ : ℝ) : ℂ)‖ ≤ C := by
  classical
  set D : Set ℕ := {n : ℕ | primePhaseCoeff ω n ≠ primePhaseCoeff ω' n} with hDdef
  have hDfin : D.Finite := by
    refine Set.Finite.subset (hfin.preimage (f := fun n : ℕ => n + 1)
      (Set.injOn_of_injective (add_left_injective 1))) fun n hn => ?_
    by_contra hc
    exact hn (primePhaseCoeff_eq_of_coord_eq (not_not.mp hc))
  set T : Finset ℕ := hDfin.toFinset with hTdef
  refine ⟨∑ n ∈ T, 2 * (((n : ℝ) + 1) ^ (-(1 / 2 : ℝ))), Finset.sum_nonneg fun n _ => by
    positivity, ?_⟩
  intro σ hσ
  have hre : (((σ : ℝ) : ℂ)).re = σ := Complex.ofReal_re σ
  have hconv : DirichletConvergesAt (primePhaseCoeff ω) ((σ : ℝ) : ℂ) :=
    convergesAt_primePhaseCoeff_of_gt hω (by rw [hre]; exact hσ)
  have hconv' : DirichletConvergesAt (primePhaseCoeff ω') ((σ : ℝ) : ℂ) :=
    convergesAt_primePhaseCoeff_of_gt hω' (by rw [hre]; exact hσ)
  set c : ℂ := ∑ n ∈ T, (primePhaseCoeff ω n - primePhaseCoeff ω' n)
      * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ)) with hcdef
  have hdiff : ∀ N : ℕ, T ⊆ Finset.range N →
      dirichletPartialSum (primePhaseCoeff ω) N ((σ : ℝ) : ℂ)
        - dirichletPartialSum (primePhaseCoeff ω') N ((σ : ℝ) : ℂ) = c := by
    intro N hTN
    have hstep : dirichletPartialSum (primePhaseCoeff ω) N ((σ : ℝ) : ℂ)
        - dirichletPartialSum (primePhaseCoeff ω') N ((σ : ℝ) : ℂ)
        = ∑ n ∈ Finset.range N, (primePhaseCoeff ω n - primePhaseCoeff ω' n)
            * (((n : ℝ) + 1 : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ)) := by
      rw [dirichletPartialSum, dirichletPartialSum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun n _ => by ring
    rw [hstep, hcdef]
    refine (Finset.sum_subset hTN ?_).symm
    intro n _ hnT
    have : primePhaseCoeff ω n = primePhaseCoeff ω' n := by
      by_contra hc
      exact hnT (hDfin.mem_toFinset.mpr hc)
    rw [this, sub_self, zero_mul]
  have hlim : dirichletSum (primePhaseCoeff ω) ((σ : ℝ) : ℂ)
      - dirichletSum (primePhaseCoeff ω') ((σ : ℝ) : ℂ) = c := by
    have htend := (tendsto_dirichletSum hconv).sub (tendsto_dirichletSum hconv')
    refine tendsto_nhds_unique htend ?_
    refine tendsto_const_nhds.congr' ?_
    obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ n ∈ T, n < M := ⟨T.sup id + 1, fun n hn => by
      have h := Finset.le_sup (f := id) hn
      simp only [id] at h
      omega⟩
    filter_upwards [eventually_ge_atTop M] with N hN
    exact (hdiff N fun n hn => Finset.mem_range.mpr (lt_of_lt_of_le (hM n hn) hN)).symm
  rw [hlim, hcdef]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul]
  have hnorm : ‖(((n : ℝ) + 1 : ℝ) : ℂ) ^ (-((σ : ℝ) : ℂ))‖ = ((n : ℝ) + 1) ^ (-σ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), Complex.neg_re, hre]
  rw [hnorm]
  have hc1 : ‖primePhaseCoeff ω n - primePhaseCoeff ω' n‖ ≤ 2 := by
    have hb : ∀ ω'' : Omega, ‖primePhaseCoeff ω'' n‖ ≤ 1 := by
      intro ω''
      show ‖(if (n + 1).Prime then X (n + 1) ω'' else 0)‖ ≤ 1
      by_cases hp : (n + 1).Prime
      · rw [if_pos hp, norm_X]
      · rw [if_neg hp, norm_zero]; norm_num
    calc ‖primePhaseCoeff ω n - primePhaseCoeff ω' n‖
        ≤ ‖primePhaseCoeff ω n‖ + ‖primePhaseCoeff ω' n‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith [hb ω, hb ω']
  have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0:ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have h2 : ((n : ℝ) + 1) ^ (-σ) ≤ ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  have hpos : (0:ℝ) ≤ ((n : ℝ) + 1) ^ (-σ) := Real.rpow_nonneg (by positivity) _
  calc ‖primePhaseCoeff ω n - primePhaseCoeff ω' n‖ * ((n : ℝ) + 1) ^ (-σ)
      ≤ 2 * ((n : ℝ) + 1) ^ (-σ) := mul_le_mul_of_nonneg_right hc1 hpos
    _ ≤ 2 * ((n : ℝ) + 1) ^ (-(1 / 2 : ℝ)) := by linarith


/-- The tail layer changes by a fixed finite sum. -/
theorem helsonLogTail_sub_of_finiteModification {ω ω' : Omega}
    (hfin : {n : ℕ | ω n ≠ ω' n}.Finite) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, 1 / 2 < σ →
      ‖helsonLogTail (helsonPhaseOf ω) ((σ : ℝ) : ℂ)
        - helsonLogTail (helsonPhaseOf ω') ((σ : ℝ) : ℂ)‖ ≤ C := by
  classical
  set S : Set Nat.Primes := {p : Nat.Primes | helsonPhaseOf ω p ≠ helsonPhaseOf ω' p} with hSdef
  have hSfin : S.Finite := by
    refine Set.Finite.subset (hfin.preimage (f := fun p : Nat.Primes => (p : ℕ))
      (Set.injOn_of_injective (fun p q h => Subtype.ext h))) fun p hp => ?_
    by_contra hc
    exact hp (helsonPhaseOf_eq_of_coord_eq (not_not.mp hc))
  refine ⟨2 * (hSfin.toFinset.card : ℝ), by positivity, ?_⟩
  intro σ hσ
  have hre : (((σ : ℝ) : ℂ)).re = σ := Complex.ofReal_re σ
  have hσ' : 1 / 2 < (((σ : ℝ) : ℂ)).re := by rw [hre]; exact hσ
  have hs1 := summable_helsonLogTail (norm_helsonPhaseOf_le ω) hσ'
  have hs2 := summable_helsonLogTail (norm_helsonPhaseOf_le ω') hσ'
  rw [helsonLogTail, helsonLogTail, ← hs1.tsum_sub hs2]
  have hvanish : ∀ p ∉ hSfin.toFinset,
      logTail (helsonPhaseOf ω p * ((p : ℕ) : ℂ) ^ (-((σ : ℝ) : ℂ)))
        - logTail (helsonPhaseOf ω' p * ((p : ℕ) : ℂ) ^ (-((σ : ℝ) : ℂ))) = 0 := by
    intro p hp
    have heq : helsonPhaseOf ω p = helsonPhaseOf ω' p := by
      by_contra hc
      exact hp (hSfin.mem_toFinset.mpr hc)
    rw [heq, sub_self]
  rw [tsum_eq_sum hvanish]
  refine le_trans (norm_sum_le _ _) ?_
  have hterm : ∀ p ∈ hSfin.toFinset,
      ‖logTail (helsonPhaseOf ω p * ((p : ℕ) : ℂ) ^ (-((σ : ℝ) : ℂ)))
        - logTail (helsonPhaseOf ω' p * ((p : ℕ) : ℂ) ^ (-((σ : ℝ) : ℂ)))‖ ≤ 2 := by
    intro p _
    have hbnd : ∀ ω'' : Omega,
        ‖logTail (helsonPhaseOf ω'' p * ((p : ℕ) : ℂ) ^ (-((σ : ℝ) : ℂ)))‖ ≤ 1 := by
      intro ω''
      refine le_trans (norm_logTail_prime_le (norm_helsonPhaseOf_le ω'') p (le_of_lt hσ')) ?_
      rw [hre]
      have hp2 : (2 : ℝ) ≤ ((p : ℕ) : ℝ) := by exact_mod_cast p.2.two_le
      have h1 : ((p : ℕ) : ℝ) ^ (-(2 * σ)) ≤ (2 : ℝ) ^ (-(2 * σ)) :=
        Real.rpow_le_rpow_of_nonpos (by norm_num) hp2 (by linarith)
      have h2 : (2 : ℝ) ^ (-(2 * σ)) ≤ (2 : ℝ) ^ (-(1 : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      have h3 : (2 : ℝ) ^ (-(1 : ℝ)) = 1 / 2 := by
        rw [Real.rpow_neg_one]
        norm_num
      rw [h3] at h2
      linarith
    calc ‖logTail (helsonPhaseOf ω p * ((p : ℕ) : ℂ) ^ (-((σ : ℝ) : ℂ)))
          - logTail (helsonPhaseOf ω' p * ((p : ℕ) : ℂ) ^ (-((σ : ℝ) : ℂ)))‖
        ≤ ‖logTail (helsonPhaseOf ω p * ((p : ℕ) : ℂ) ^ (-((σ : ℝ) : ℂ)))‖
          + ‖logTail (helsonPhaseOf ω' p * ((p : ℕ) : ℂ) ^ (-((σ : ℝ) : ℂ)))‖ := norm_sub_le _ _
      _ ≤ 2 := by linarith [hbnd ω, hbnd ω']
  refine le_trans (Finset.sum_le_sum hterm) ?_
  rw [Finset.sum_const, nsmul_eq_mul]
  ring_nf
  exact le_refl _

/-- **Finite modification changes the Euler exponent by a bounded amount, uniformly past the half
line.** -/
theorem exists_bound_eulerExponentRe_sub {ω ω' : Omega} (hfin : {n : ℕ | ω n ≠ ω' n}.Finite)
    (hω : ω ∈ primeHolomorphicEvent) (hω' : ω' ∈ primeHolomorphicEvent) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ : ℝ, 1 / 2 < σ → |eulerExponentRe σ ω - eulerExponentRe σ ω'| ≤ C := by
  obtain ⟨C₁, hC₁0, hC₁⟩ := dirichletSum_sub_of_finiteModification hfin hω hω'
  obtain ⟨C₂, hC₂0, hC₂⟩ := helsonLogTail_sub_of_finiteModification hfin
  refine ⟨C₁ + C₂, by linarith, fun σ hσ => ?_⟩
  rw [eulerExponentRe_eq hω hσ, eulerExponentRe_eq hω' hσ]
  have hsplit : (helsonExponent ω ((σ : ℝ) : ℂ)).re - (helsonExponent ω' ((σ : ℝ) : ℂ)).re
      = (dirichletSum (primePhaseCoeff ω) ((σ : ℝ) : ℂ)
          - dirichletSum (primePhaseCoeff ω') ((σ : ℝ) : ℂ)).re
        + (helsonLogTail (helsonPhaseOf ω) ((σ : ℝ) : ℂ)
          - helsonLogTail (helsonPhaseOf ω') ((σ : ℝ) : ℂ)).re := by
    simp only [helsonExponent, Complex.add_re, Complex.sub_re]
    ring
  rw [hsplit]
  have h1 : |(dirichletSum (primePhaseCoeff ω) ((σ : ℝ) : ℂ)
      - dirichletSum (primePhaseCoeff ω') ((σ : ℝ) : ℂ)).re| ≤ C₁ :=
    le_trans (Complex.abs_re_le_norm _) (hC₁ σ hσ)
  have h2 : |(helsonLogTail (helsonPhaseOf ω) ((σ : ℝ) : ℂ)
      - helsonLogTail (helsonPhaseOf ω') ((σ : ℝ) : ℂ)).re| ≤ C₂ :=
    le_trans (Complex.abs_re_le_norm _) (hC₂ σ hσ)
  have habs := abs_add_le (dirichletSum (primePhaseCoeff ω) ((σ : ℝ) : ℂ)
      - dirichletSum (primePhaseCoeff ω') ((σ : ℝ) : ℂ)).re
    (helsonLogTail (helsonPhaseOf ω) ((σ : ℝ) : ℂ)
      - helsonLogTail (helsonPhaseOf ω') ((σ : ℝ) : ℂ)).re
  linarith


/-! ### The continuation event is measurable and finite-modification invariant -/

theorem measurable_phaseTorusOf : Measurable phaseTorusOf := by
  refine measurable_pi_lambda _ fun p => ?_
  exact Measurable.subtype_mk (measurable_X (p : ℕ))

theorem measurableSet_contEvent : MeasurableSet contEvent :=
  measurable_phaseTorusOf measurableSet_continuableStratum

theorem contEvent_invariant {ω ω' : Omega} (hfin : {n : ℕ | ω n ≠ ω' n}.Finite) :
    ω ∈ contEvent ↔ ω' ∈ contEvent := by
  have key : ∀ x y : Omega, {n : ℕ | x n ≠ y n}.Finite → x ∈ contEvent → y ∈ contEvent := by
    intro x y hxy hx
    refine mem_continuableStratum_of_finite_ne hx ?_
    refine Set.Finite.subset (hxy.preimage (f := fun p : Nat.Primes => (p : ℕ))
      (Set.injOn_of_injective (fun p q h => Subtype.ext h))) fun p hp => ?_
    by_contra hc
    exact hp (by
      show ((phaseTorusOf y p : ℂ)) = ((phaseTorusOf x p : ℂ))
      exact (helsonPhaseOf_eq_of_coord_eq (not_not.mp hc)).symm)
  have hsymm : {n : ℕ | ω' n ≠ ω n}.Finite := by
    refine hfin.subset fun n hn => ?_
    exact fun hc => hn hc.symm
  exact ⟨key ω ω' hfin, key ω' ω hsymm⟩

end GaloisForLFunctions.RHTower

end
