import GaloisForLFunctions.RHTower.ThetaTemperedMultiplicityJets

/-!
# Actual compact Schwartz-test division away from Xi zeros

A smooth multiplier nonzero on a compact test's topological support divides
that test inside the original Schwartz space. The quotient retains compact
support. The actual Xi specialization lets its entire tempered kernel kill
every compact original test supported away from the actual real zero set.
-/

noncomputable section

open Set Filter
open scoped ContDiff SchwartzMap Topology

namespace RHTower

/-- Actual compact smooth division preserves the original Schwartz test and its support. -/
theorem thetaSchwartz_exists_compact_division
    (f : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
    (φ : 𝓢(ℝ, ℂ)) (hφ : HasCompactSupport (φ : ℝ → ℂ))
    (hne : ∀ x ∈ tsupport (φ : ℝ → ℂ), f x ≠ 0) :
    ∃ ψ : 𝓢(ℝ, ℂ), HasCompactSupport (ψ : ℝ → ℂ) ∧
      tsupport (ψ : ℝ → ℂ) ⊆ tsupport (φ : ℝ → ℂ) ∧
      (φ : ℝ → ℂ) = fun x => f x * ψ x := by
  let q : ℝ → ℂ := fun x => φ x / f x
  have hoff : ∀ x : ℝ, x ∉ tsupport (φ : ℝ → ℂ) → φ x = 0 :=
    fun _ hx => image_eq_zero_of_notMem_tsupport hx
  have hsmooth : ContDiff ℝ ∞ q := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    by_cases hx : f x = 0
    · have hnot : x ∉ tsupport (φ : ℝ → ℂ) := fun h => hne x h hx
      have hmem : (tsupport (φ : ℝ → ℂ))ᶜ ∈ 𝓝 x :=
        (isClosed_tsupport _).isOpen_compl.mem_nhds hnot
      have hgerm : q =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
        filter_upwards [hmem] with y hy
        change φ y / f y = 0
        rw [hoff y hy, zero_div]
      exact (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq hgerm
    · have hmul : ContDiffAt ℝ ∞ (fun y : ℝ => φ y * (f y)⁻¹) x :=
        φ.smooth'.contDiffAt.mul (hf.contDiffAt.inv hx)
      change ContDiffAt ℝ ∞ (fun y : ℝ => φ y / f y) x
      simpa only [div_eq_mul_inv] using hmul
  have hsupport : Function.support q ⊆ tsupport (φ : ℝ → ℂ) := by
    intro x hx
    by_contra hnot
    apply hx
    change φ x / f x = 0
    rw [hoff x hnot, zero_div]
  have htsupport : tsupport q ⊆ tsupport (φ : ℝ → ℂ) :=
    closure_minimal hsupport (isClosed_tsupport _)
  have hcompact : HasCompactSupport q :=
    IsCompact.of_isClosed_subset hφ (isClosed_tsupport q) htsupport
  refine ⟨hcompact.toSchwartzMap hsmooth, hcompact, htsupport, ?_⟩
  funext x
  change φ x = f x * (φ x / f x)
  by_cases hx : f x = 0
  · rw [hoff x (fun h => hne x h hx), hx, zero_mul]
  · field_simp

/-- The actual real Xi symbol is smooth by its original Schwartz realization. -/
theorem thetaXiRealSymbol_contDiff : ContDiff ℝ ∞ thetaXiRealSymbol := by
  rw [thetaXiRealSymbol_eq_coeSchwartz]
  exact thetaXiSchwartzSymbol.smooth'

/-- Compact original tests avoiding every actual real Xi zero have actual compact Xi quotients. -/
theorem thetaSchwartz_exists_compact_Xi_division
    (φ : 𝓢(ℝ, ℂ)) (hφ : HasCompactSupport (φ : ℝ → ℂ))
    (hne : ∀ x ∈ tsupport (φ : ℝ → ℂ), thetaXiRealSymbol x ≠ 0) :
    ∃ ψ : 𝓢(ℝ, ℂ), HasCompactSupport (ψ : ℝ → ℂ) ∧
      tsupport (ψ : ℝ → ℂ) ⊆ tsupport (φ : ℝ → ℂ) ∧
      (φ : ℝ → ℂ) = fun x => thetaXiRealSymbol x * ψ x :=
  thetaSchwartz_exists_compact_division thetaXiRealSymbol thetaXiRealSymbol_contDiff φ hφ hne

/-- Every actual Xi-kernel functional kills every compact original test supported away from Xi zeros. -/
theorem thetaXiTemperedKernel_eq_zero_of_compact_tsupport_nonvanishing
    (Q : 𝓢'(ℝ, ℂ)) (hQ : thetaXiTemperedMultiplier Q = 0)
    (φ : 𝓢(ℝ, ℂ)) (hφ : HasCompactSupport (φ : ℝ → ℂ))
    (hne : ∀ x ∈ tsupport (φ : ℝ → ℂ), thetaXiRealSymbol x ≠ 0) : Q φ = 0 := by
  obtain ⟨ψ, _, _, hfactor⟩ := thetaSchwartz_exists_compact_Xi_division φ hφ hne
  have hproduct : SchwartzMap.smulLeftCLM ℂ thetaXiRealSymbol ψ = φ := by
    ext x
    rw [SchwartzMap.smulLeftCLM_apply_apply thetaXiRealSymbol_hasTemperateGrowth,
      smul_eq_mul]
    exact (congrFun hfactor x).symm
  have h := congrArg (fun T : 𝓢'(ℝ, ℂ) => T ψ) hQ
  simpa only [thetaXiTemperedMultiplier, TemperedDistribution.smulLeftCLM_apply_apply,
    zero_apply, hproduct] using h

end RHTower
