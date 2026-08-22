import GaloisForLFunctions.RHTower.ConnesLocalDeltaStructure
import GaloisForLFunctions.RHTower.ConnesDeltaOrderBound
import GaloisForLFunctions.RHTower.ConnesDirichletSpectralMultiplicity

/-!
# Theorem III.1 for an arbitrary `L`-function

Theorem 1 of §III together with Appendix I (25)(27)(28) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

The spectral realization of §III is proved here for **any** entire, not-identically-zero function
`L` in place of the `L`-function with Grössencharakter: at every point of the critical line the
solution space of `L(½ + i·)·α = 0` is spanned by exactly the first `n` derivatives of the Dirac
mass, `n` the order of vanishing of `L` there.

Isolating the hypotheses this way makes the theorem independent of which `L`-functions are
available: `ConnesDirichletSpectralMultiplicity` is the instance for the Grössencharakters of `ℚ`,
and any future construction of Hecke `L`-functions of a number field plugs into the same theorem
by supplying entirety and one non-vanishing point.
-/

open Set Complex Filter Topology
open GaloisForLFunctions.HTGeometry
open scoped ContDiff

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- The critical-line multiplier of `L`, translated so that the spectral point sits at the
origin. -/
def connesShiftedMultiplier (L : ℂ → ℂ) (t₀ : ℝ) (z : ℂ) : ℂ :=
  L ((1 / 2 : ℂ) + ((t₀ : ℂ) + z) * Complex.I)

theorem connes_shiftedMultiplier_differentiable {L : ℂ → ℂ} (hL : Differentiable ℂ L) (t₀ : ℝ) :
    Differentiable ℂ (connesShiftedMultiplier L t₀) := by
  intro z
  have hinner : DifferentiableAt ℂ (fun w : ℂ => (1 / 2 : ℂ) + ((t₀ : ℂ) + w) * Complex.I) z := by
    fun_prop
  exact (hL _).comp z hinner

theorem connes_shiftedMultiplier_analytic {L : ℂ → ℂ} (hL : Differentiable ℂ L) (t₀ : ℝ) :
    AnalyticOnNhd ℂ (connesShiftedMultiplier L t₀) univ := by
  refine DifferentiableOn.analyticOnNhd ?_ isOpen_univ
  exact (connes_shiftedMultiplier_differentiable hL t₀).differentiableOn

theorem connes_shiftedMultiplier_contDiffC {L : ℂ → ℂ} (hL : Differentiable ℂ L) (t₀ : ℝ) :
    ContDiff ℂ ∞ (connesShiftedMultiplier L t₀) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  exact (connes_shiftedMultiplier_analytic hL t₀ z (mem_univ z)).contDiffAt

theorem connes_shiftedMultiplier_contDiff {L : ℂ → ℂ} (hL : Differentiable ℂ L) (t₀ : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => connesShiftedMultiplier L t₀ (t : ℂ)) := by
  have hR : ContDiff ℝ ∞ (connesShiftedMultiplier L t₀) :=
    (connes_shiftedMultiplier_contDiffC hL t₀).restrict_scalars ℝ
  exact hR.comp Complex.ofRealCLM.contDiff

/-- A non-vanishing point of `L` transports to a non-vanishing point of the shifted multiplier. -/
theorem connes_shiftedMultiplier_ne_zero_somewhere {L : ℂ → ℂ} {w : ℂ} (hw : L w ≠ 0) (t₀ : ℝ) :
    connesShiftedMultiplier L t₀ (-(t₀ : ℂ) + (w - (1 / 2 : ℂ)) * (-Complex.I)) ≠ 0 := by
  have harg : (1 / 2 : ℂ)
      + ((t₀ : ℂ) + (-(t₀ : ℂ) + (w - (1 / 2 : ℂ)) * (-Complex.I))) * Complex.I = w := by
    linear_combination ((1 / 2 : ℂ) - w) * Complex.I_sq
  rw [connesShiftedMultiplier, harg]
  exact hw

/-- **Isolated zeros.**  Around every spectral point there is a window on which the origin is the
only zero of the multiplier. -/
theorem connes_shiftedMultiplier_isolated {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    {w : ℂ} (hw : L w ≠ 0) (t₀ : ℝ) :
    ∃ R > 0, ∀ t : ℝ, t ∈ Ioo (-R) R → t ≠ 0 →
      connesShiftedMultiplier L t₀ (t : ℂ) ≠ 0 := by
  have hana := connes_shiftedMultiplier_analytic hL t₀
  have hz₀ := connes_shiftedMultiplier_ne_zero_somewhere hw t₀
  rcases (hana 0 (mem_univ 0)).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · exfalso
    have heq := hana.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ
      (mem_univ (0 : ℂ)) hzero
    exact hz₀ (heq (mem_univ _))
  · rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff] at hne
    obtain ⟨r, hr, hrne⟩ := hne
    refine ⟨r, hr, fun t ht htne => ?_⟩
    have hdist : dist ((t : ℂ)) (0 : ℂ) < r := by
      rw [dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
      exact abs_lt.mpr ⟨ht.1, ht.2⟩
    have hmemc : ((t : ℂ)) ∈ ({(0 : ℂ)}ᶜ : Set ℂ) := by
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact fun hcon => htne (by exact_mod_cast hcon)
    exact hrne hdist hmemc

/-- **The order of vanishing at a spectral point is finite.** -/
theorem connes_shiftedMultiplier_order {L : ℂ → ℂ} (hL : Differentiable ℂ L)
    {w : ℂ} (hw : L w ≠ 0) (t₀ : ℝ) :
    ∃ n : ℕ,
      (∀ i, i < n →
        iteratedDeriv i (fun t : ℝ => connesShiftedMultiplier L t₀ (t : ℂ)) 0 = 0) ∧
      iteratedDeriv n (fun t : ℝ => connesShiftedMultiplier L t₀ (t : ℂ)) 0 ≠ 0 := by
  have hana : AnalyticAt ℂ (connesShiftedMultiplier L t₀) 0 :=
    connes_shiftedMultiplier_analytic hL t₀ 0 (mem_univ 0)
  have hnottop : analyticOrderAt (connesShiftedMultiplier L t₀) 0 ≠ ⊤ := by
    rw [Ne, analyticOrderAt_eq_top]
    intro hzero
    have heq := (connes_shiftedMultiplier_analytic hL t₀).eqOn_zero_of_preconnected_of_eventuallyEq_zero
      isPreconnected_univ (mem_univ (0 : ℂ)) hzero
    exact connes_shiftedMultiplier_ne_zero_somewhere hw t₀ (heq (mem_univ _))
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hnottop
  have hiff := (analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero hana (n := n)).mp hn.symm
  have htrans := connes_iteratedDeriv_ofReal (connes_shiftedMultiplier_contDiffC hL t₀)
  refine ⟨n, fun i hi => ?_, ?_⟩
  · rw [htrans i 0]
    simpa using hiff.1 i hi
  · rw [htrans n 0]
    simpa using hiff.2

/-- The multiplier times a jet test function, as a compactly supported Schwartz map. -/
def connesEntireShiftJet {L : ℂ → ℂ} (hL : Differentiable ℂ L) (t₀ : ℝ) (m : ℕ) :
    SchwartzMap ℝ ℂ :=
  HasCompactSupport.toSchwartzMap
    (f := fun x : ℝ => connesShiftedMultiplier L t₀ (x : ℂ) * (jetTest m : ℝ → ℂ) x)
    ((connes_hasCompactSupport_jetTest m).mul_left)
    ((connes_shiftedMultiplier_contDiff hL t₀).mul (jetTest m).smooth')

@[simp] theorem connesEntireShiftJet_apply {L : ℂ → ℂ} (hL : Differentiable ℂ L) (t₀ : ℝ)
    (m : ℕ) :
    ((connesEntireShiftJet hL t₀ m : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      = fun x : ℝ => connesShiftedMultiplier L t₀ (x : ℂ) * (jetTest m : ℝ → ℂ) x := rfl

/-- **Theorem III.1, the multiplicity statement, for an arbitrary entire `L`-function.** -/
theorem connes_entire_spectral_multiplicity {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℂ X] {L : ℂ → ℂ} (hL : Differentiable ℂ L) {w : ℂ} (hw : L w ≠ 0) (t₀ : ℝ)
    (u : SchwartzMap ℝ ℂ →L[ℂ] X)
    (hmul : ∀ ψ g : SchwartzMap ℝ ℂ,
      ((ψ : ℝ → ℂ)
        = fun t : ℝ => connesShiftedMultiplier L t₀ (t : ℂ) * (g : ℝ → ℂ) t) → u ψ = 0) :
    ∃ (n : ℕ) (R : ℝ), 0 < R ∧
      (∀ i, i < n →
        iteratedDeriv i (fun t : ℝ => connesShiftedMultiplier L t₀ (t : ℂ)) 0 = 0) ∧
      iteratedDeriv n (fun t : ℝ => connesShiftedMultiplier L t₀ (t : ℂ)) 0 ≠ 0 ∧
      ∀ η : SchwartzMap ℝ ℂ,
        tsupport ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆ Ioo (-R) R →
        ∃ c : ℕ → X, ∀ ψ : SchwartzMap ℝ ℂ,
          u (SchwartzMap.smulLeftCLM ℂ ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) ψ)
            = ∑ j ∈ Finset.range n, (iteratedDeriv j (ψ : ℝ → ℂ) 0) • c j := by
  obtain ⟨n, hvan, hnz⟩ := connes_shiftedMultiplier_order hL hw t₀
  obtain ⟨R, hR, hne⟩ := connes_shiftedMultiplier_isolated hL hw t₀
  refine ⟨n, R, hR, hvan, hnz, fun η hη => ?_⟩
  obtain ⟨M, c, hc⟩ := connes_division_structure_local u
    (fun t : ℝ => connesShiftedMultiplier L t₀ (t : ℂ))
    (connes_shiftedMultiplier_contDiff hL t₀) hne hmul η hη
  have hηtg : Function.HasTemperateGrowth ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) :=
    η.hasTemperateGrowth
  have hker : ∀ m : ℕ,
      ∑ j ∈ Finset.range (M + 1),
        (iteratedDeriv j (fun x : ℝ =>
          connesShiftedMultiplier L t₀ (x : ℂ) * (jetTest m : ℝ → ℂ) x) 0) • c j = 0 := by
    intro m
    have hΦ := hc (connesEntireShiftJet hL t₀ m)
    have hzero : u (SchwartzMap.smulLeftCLM ℂ ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ)
        (connesEntireShiftJet hL t₀ m)) = 0 := by
      refine hmul _ (SchwartzMap.smulLeftCLM ℂ ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ)
        (jetTest m)) ?_
      funext t
      rw [SchwartzMap.smulLeftCLM_apply_apply hηtg,
        SchwartzMap.smulLeftCLM_apply_apply hηtg, connesEntireShiftJet_apply]
      simp only [smul_eq_mul]
      ring
    rw [hzero] at hΦ
    exact hΦ.symm
  have hcoef := connes_delta_coeffs_vanish_above_order_jet
    (φ := fun t : ℝ => connesShiftedMultiplier L t₀ (t : ℂ)) (n := n) (M := M)
    (connes_shiftedMultiplier_contDiff hL t₀) hvan hnz c hker
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
