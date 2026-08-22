import GaloisForLFunctions.RHTower.ConnesDirichletSpectralDelta
import GaloisForLFunctions.RHTower.ConnesDeltaOrderBound

/-!
# Theorem III.1: the multiplicity statement, for the Grössencharakters of `ℚ`

Theorem 1 of §III together with Appendix I (25)(27)(28) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

At a spectral point `t₀` the solution space of `L(Χ, 1/2 + i·)·α = 0` is spanned by the first `n`
derivatives of the Dirac mass, where `n` is the order of vanishing of the `L`-function at that
point.  This is the multiplicity half of Connes' spectral realization, proved here for every
non-trivial Dirichlet character — i.e. for every Grössencharakter of `ℚ` — with no hypotheses
beyond the data.
-/

open Set Complex Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped ContDiff

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {N : ℕ} [NeZero N]

/-- Along the real line the iterated derivatives of an entire function are the complex ones. -/
theorem connes_iteratedDeriv_ofReal {F : ℂ → ℂ} (hF : ContDiff ℂ ∞ F) :
    ∀ (i : ℕ) (t : ℝ),
      iteratedDeriv i (fun s : ℝ => F (s : ℂ)) t = iteratedDeriv i F (t : ℂ) := by
  intro i
  induction i with
  | zero => intro t; simp
  | succ i ih =>
      intro t
      have hGdiff : Differentiable ℂ (iteratedDeriv i F) := by
        rw [iteratedDeriv_eq_iterate]
        exact (contDiff_infty_iff_deriv.mp (hF.iterate_deriv i)).1
      have hfun : iteratedDeriv i (fun s : ℝ => F (s : ℂ))
          = fun s : ℝ => iteratedDeriv i F (s : ℂ) := by
        funext s
        exact ih s
      have hstep : HasDerivAt (fun s : ℝ => iteratedDeriv i F (s : ℂ))
          (deriv (iteratedDeriv i F) (t : ℂ)) t :=
        ((hGdiff (t : ℂ)).hasDerivAt).comp_ofReal
      rw [iteratedDeriv_succ, hfun, hstep.deriv, iteratedDeriv_succ]

theorem connes_dirichletShift_contDiffC (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (t₀ : ℝ) :
    ContDiff ℂ ∞ (connesDirichletShift χ t₀) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  exact (connes_dirichletShift_analytic χ hχ t₀ z (mem_univ z)).contDiffAt

/-- **The order of vanishing at a spectral point is finite.** -/
theorem connes_dirichletShift_order (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (t₀ : ℝ) :
    ∃ n : ℕ,
      (∀ i, i < n →
        iteratedDeriv i (fun t : ℝ => connesDirichletShift χ t₀ (t : ℂ)) 0 = 0) ∧
      iteratedDeriv n (fun t : ℝ => connesDirichletShift χ t₀ (t : ℂ)) 0 ≠ 0 := by
  have hana : AnalyticAt ℂ (connesDirichletShift χ t₀) 0 :=
    connes_dirichletShift_analytic χ hχ t₀ 0 (mem_univ 0)
  have hnottop : analyticOrderAt (connesDirichletShift χ t₀) 0 ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]
    intro hzero
    have heq := (connes_dirichletShift_analytic χ hχ t₀).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ (0 : ℂ)) hzero
    exact connes_dirichletShift_ne_zero_somewhere χ hχ t₀ (heq (mem_univ _))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnottop
  have hiff := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hana (n := n)).mp hn.symm
  have htrans := connes_iteratedDeriv_ofReal (connes_dirichletShift_contDiffC χ hχ t₀)
  refine ⟨n, fun i hi => ?_, ?_⟩
  · rw [htrans i 0]
    simpa using hiff.1 i hi
  · rw [htrans n 0]
    simpa using hiff.2

theorem connes_hasCompactSupport_jetTest (m : ℕ) :
    HasCompactSupport ((jetTest m : SchwartzMap ℝ ℂ) : ℝ → ℂ) := by
  have h : ((jetTest m : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      = fun x : ℝ => cutoffScaled (1/2) x • (((x : ℂ)) ^ m / (Nat.factorial m : ℂ)) := by
    funext x
    exact jetTest_apply m x
  rw [h]
  exact (hasCompactSupport_cutoffScaled (by norm_num)).smul_right

/-- The multiplier times a jet test function, as a Schwartz map — compactly supported, so no
growth hypothesis on the multiplier is needed. -/
def connesShiftJet (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (t₀ : ℝ) (m : ℕ) :
    SchwartzMap ℝ ℂ :=
  HasCompactSupport.toSchwartzMap
    (f := fun x : ℝ =>
      connesDirichletShift χ t₀ (x : ℂ) * (jetTest m : ℝ → ℂ) x)
    ((connes_hasCompactSupport_jetTest m).mul_left)
    ((connes_dirichletShift_contDiff χ hχ t₀).mul (jetTest m).smooth')

@[simp] theorem connesShiftJet_apply (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (t₀ : ℝ)
    (m : ℕ) (x : ℝ) :
    ((connesShiftJet χ hχ t₀ m : SchwartzMap ℝ ℂ) : ℝ → ℂ) x
      = connesDirichletShift χ t₀ (x : ℂ) * (jetTest m : ℝ → ℂ) x := rfl

/-- **Theorem III.1, the multiplicity statement, for every Grössencharakter of `ℚ`.**  On a window
around a spectral point, a functional annihilated by every multiple of the critical-line multiplier
is a combination of exactly the first `n` derivatives of the Dirac mass, where `n` is the order of
vanishing of `L(Χ, ·)` at that point. -/
theorem connes_dirichlet_spectral_multiplicity {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (t₀ : ℝ)
    (u : SchwartzMap ℝ ℂ →L[ℂ] X)
    (hmul : ∀ ψ g : SchwartzMap ℝ ℂ,
      ((ψ : ℝ → ℂ)
        = fun t : ℝ => connesDirichletShift χ t₀ (t : ℂ) * (g : ℝ → ℂ) t) → u ψ = 0) :
    ∃ (n : ℕ) (R : ℝ), 0 < R ∧
      (∀ i, i < n →
        iteratedDeriv i (fun t : ℝ => connesDirichletShift χ t₀ (t : ℂ)) 0 = 0) ∧
      iteratedDeriv n (fun t : ℝ => connesDirichletShift χ t₀ (t : ℂ)) 0 ≠ 0 ∧
      ∀ η : SchwartzMap ℝ ℂ,
        tsupport ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆ Ioo (-R) R →
        ∃ c : ℕ → X, ∀ ψ : SchwartzMap ℝ ℂ,
          u (SchwartzMap.smulLeftCLM ℂ ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) ψ)
            = ∑ j ∈ Finset.range n, (iteratedDeriv j (ψ : ℝ → ℂ) 0) • c j := by
  obtain ⟨n, hvan, hnz⟩ := connes_dirichletShift_order χ hχ t₀
  obtain ⟨R, hR, hdelta⟩ := connes_dirichlet_spectral_delta χ hχ t₀ u hmul
  refine ⟨n, R, hR, hvan, hnz, fun η hη => ?_⟩
  obtain ⟨M, c, hc⟩ := hdelta η hη
  have hηtg : Function.HasTemperateGrowth ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) :=
    η.hasTemperateGrowth
  have hker : ∀ m : ℕ,
      ∑ j ∈ Finset.range (M + 1),
        (iteratedDeriv j (fun x : ℝ =>
          connesDirichletShift χ t₀ (x : ℂ) * (jetTest m : ℝ → ℂ) x) 0) • c j = 0 := by
    intro m
    have hΦ := hc (connesShiftJet χ hχ t₀ m)
    have hzero : u (SchwartzMap.smulLeftCLM ℂ ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ)
        (connesShiftJet χ hχ t₀ m)) = 0 := by
      refine hmul _ (SchwartzMap.smulLeftCLM ℂ ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ)
        (jetTest m)) ?_
      funext t
      rw [SchwartzMap.smulLeftCLM_apply_apply hηtg,
        SchwartzMap.smulLeftCLM_apply_apply hηtg, connesShiftJet_apply]
      simp only [smul_eq_mul]
      ring
    rw [hzero] at hΦ
    exact hΦ.symm
  have hcoef := connes_delta_coeffs_vanish_above_order_jet
    (φ := fun t : ℝ => connesDirichletShift χ t₀ (t : ℂ)) (n := n) (M := M)
    (connes_dirichletShift_contDiff χ hχ t₀) hvan hnz c hker
  refine ⟨fun j => if j ≤ M then c j else 0, fun ψ => ?_⟩
  rw [hc ψ]
  have hstep1 : (∑ j ∈ Finset.range (M + 1), (iteratedDeriv j (ψ : ℝ → ℂ) 0) • c j)
      = ∑ j ∈ Finset.range (max (M + 1) n),
        (iteratedDeriv j (ψ : ℝ → ℂ) 0) • (if j ≤ M then c j else 0) := by
    have hcongr : (∑ j ∈ Finset.range (M + 1), (iteratedDeriv j (ψ : ℝ → ℂ) 0) • c j)
        = ∑ j ∈ Finset.range (M + 1),
          (iteratedDeriv j (ψ : ℝ → ℂ) 0) • (if j ≤ M then c j else 0) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have hjM : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rw [if_pos hjM]
    rw [hcongr]
    have hsub : Finset.range (M + 1) ⊆ Finset.range (max (M + 1) n) := by
      intro j hj
      exact Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hj) (le_max_left _ _))
    refine Finset.sum_subset hsub ?_
    intro j _ hj
    have hjM : ¬ j ≤ M := fun hcon => hj (Finset.mem_range.mpr (by omega))
    rw [if_neg hjM, smul_zero]
  have hstep2 : (∑ j ∈ Finset.range n,
        (iteratedDeriv j (ψ : ℝ → ℂ) 0) • (if j ≤ M then c j else 0))
      = ∑ j ∈ Finset.range (max (M + 1) n),
        (iteratedDeriv j (ψ : ℝ → ℂ) 0) • (if j ≤ M then c j else 0) := by
    have hsub : Finset.range n ⊆ Finset.range (max (M + 1) n) := by
      intro j hj
      exact Finset.mem_range.mpr
        (lt_of_lt_of_le (Finset.mem_range.mp hj) (le_max_right _ _))
    refine Finset.sum_subset hsub ?_
    intro j _ hj
    have hjn : n ≤ j := by
      by_contra hcon
      exact hj (Finset.mem_range.mpr (by omega))
    by_cases hjM : j ≤ M
    · rw [if_pos hjM, hcoef j hjn hjM, smul_zero]
    · rw [if_neg hjM, smul_zero]
  rw [hstep1, ← hstep2]

end

end GaloisForLFunctions.RHTower
