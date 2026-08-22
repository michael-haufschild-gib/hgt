import GaloisForLFunctions.RHTower.ConnesLocalDeltaStructure
import GaloisForLFunctions.RHTower.ConnesDirichletLineTemperate

/-!
# Theorem III.1 at a spectral point, for the Grössencharakters of `ℚ`

Theorem 1 of §III together with Appendix I (25)(27)(28) of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068.

Connes' spectral realization says that a functional killed by every multiple of the critical-line
multiplier `L(Χ, 1/2 + i t)` is carried by the zeros of that multiplier, and at each zero is a
combination of derivatives of the Dirac mass of order below the multiplicity.  For the
Grössencharakters of `ℚ` — the Dirichlet characters — the multiplier is entire and not identically
zero, so its zeros are isolated, and the localized division theorem of `ConnesLocalDeltaStructure`
applies at each of them.  Everything here is unconditional.
-/

open Set Complex Filter Topology
open scoped ContDiff

namespace GaloisForLFunctions.RHTower

noncomputable section

variable {N : ℕ} [NeZero N]

/-- The critical-line multiplier of a Dirichlet `L`-function, translated so that the spectral
point `t₀` sits at the origin, as a function of a *complex* variable. -/
def connesDirichletShift (χ : DirichletCharacter ℂ N) (t₀ : ℝ) (z : ℂ) : ℂ :=
  DirichletCharacter.LFunction χ ((1 / 2 : ℂ) + ((t₀ : ℂ) + z) * Complex.I)

theorem connes_dirichletShift_differentiable (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (t₀ : ℝ) :
    Differentiable ℂ (connesDirichletShift χ t₀) := by
  intro z
  have hdiff := DirichletCharacter.differentiableAt_LFunction χ
    ((1 / 2 : ℂ) + ((t₀ : ℂ) + z) * Complex.I) (Or.inr hχ)
  have hinner : DifferentiableAt ℂ (fun w : ℂ => (1 / 2 : ℂ) + ((t₀ : ℂ) + w) * Complex.I) z := by
    fun_prop
  exact hdiff.comp z hinner

theorem connes_dirichletShift_analytic (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (t₀ : ℝ) :
    AnalyticOnNhd ℂ (connesDirichletShift χ t₀) univ :=
  (connes_dirichletShift_differentiable χ hχ t₀).differentiableOn.analyticOnNhd isOpen_univ

/-- The multiplier is smooth along the real line. -/
theorem connes_dirichletShift_contDiff (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (t₀ : ℝ) :
    ContDiff ℝ ∞ (fun t : ℝ => connesDirichletShift χ t₀ (t : ℂ)) := by
  have hC : ContDiff ℂ ∞ (connesDirichletShift χ t₀) := by
    rw [contDiff_iff_contDiffAt]
    intro z
    exact (connes_dirichletShift_analytic χ hχ t₀ z (mem_univ z)).contDiffAt
  have hR : ContDiff ℝ ∞ (connesDirichletShift χ t₀) := hC.restrict_scalars ℝ
  exact hR.comp Complex.ofRealCLM.contDiff

/-- The multiplier is not identically zero: at `s = 2` the `L`-function does not vanish. -/
theorem connes_dirichletShift_ne_zero_somewhere (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1)
    (t₀ : ℝ) : connesDirichletShift χ t₀ (-(t₀ : ℂ) - (3 / 2 : ℂ) * Complex.I) ≠ 0 := by
  have harg : (1 / 2 : ℂ) + ((t₀ : ℂ) + (-(t₀ : ℂ) - (3 / 2 : ℂ) * Complex.I)) * Complex.I
      = (2 : ℂ) := by
    linear_combination (-(3 : ℂ) / 2) * Complex.I_sq
  rw [connesDirichletShift, harg]
  exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) (by norm_num)

/-- **Isolated zeros.**  Around every spectral point there is a window on which the origin is the
only zero of the multiplier. -/
theorem connes_dirichletShift_isolated (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (t₀ : ℝ) :
    ∃ R > 0, ∀ t : ℝ, t ∈ Ioo (-R) R → t ≠ 0 →
      connesDirichletShift χ t₀ (t : ℂ) ≠ 0 := by
  have hana := connes_dirichletShift_analytic χ hχ t₀
  have hz₀ := connes_dirichletShift_ne_zero_somewhere χ hχ t₀
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

/-- **Theorem III.1 at a spectral point, for every Grössencharakter of `ℚ`.**  A functional
annihilated by every multiple of the critical-line multiplier of `L(Χ, ·)` is, on a window around
the spectral point, a finite combination of derivatives of the Dirac mass at that point. -/
theorem connes_dirichlet_spectral_delta {X : Type*} [NormedAddCommGroup X] [NormedSpace ℂ X]
    (χ : DirichletCharacter ℂ N) (hχ : χ ≠ 1) (t₀ : ℝ)
    (u : SchwartzMap ℝ ℂ →L[ℂ] X)
    (hmul : ∀ ψ g : SchwartzMap ℝ ℂ,
      ((ψ : ℝ → ℂ)
        = fun t : ℝ => connesDirichletShift χ t₀ (t : ℂ) * (g : ℝ → ℂ) t) → u ψ = 0) :
    ∃ R > 0, ∀ η : SchwartzMap ℝ ℂ,
      tsupport ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) ⊆ Ioo (-R) R →
      ∃ (M : ℕ) (c : ℕ → X), ∀ ψ : SchwartzMap ℝ ℂ,
        u (SchwartzMap.smulLeftCLM ℂ ((η : SchwartzMap ℝ ℂ) : ℝ → ℂ) ψ)
          = ∑ j ∈ Finset.range (M + 1), (iteratedDeriv j (ψ : ℝ → ℂ) 0) • c j := by
  obtain ⟨R, hR, hne⟩ := connes_dirichletShift_isolated χ hχ t₀
  refine ⟨R, hR, fun η hη => ?_⟩
  exact connes_division_structure_local u (fun t : ℝ => connesDirichletShift χ t₀ (t : ℂ))
    (connes_dirichletShift_contDiff χ hχ t₀) hne hmul η hη

end

end GaloisForLFunctions.RHTower
