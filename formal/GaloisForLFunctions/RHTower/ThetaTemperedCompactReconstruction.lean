import GaloisForLFunctions.RHTower.ThetaTemperedLocalization
import Mathlib.Topology.DiscreteSubset

/-!
# Exact finite reconstruction on original compact Schwartz tests

The actual real Xi zeros are closed and discrete, hence finite on every
compact set. Subtracting their genuine isolating-cutoff products leaves an
original compact Schwartz test whose closed support contains no Xi zero.
Every original Xi-kernel tempered functional therefore reconstructs exactly
as the finite sum of its canonical localized functionals on each compact test.
-/

noncomputable section

open Set Filter
open scoped BigOperators SchwartzMap Topology

namespace RHTower

/-- The actual real Xi zero set is closed by the genuine smooth symbol. -/
theorem thetaXiRealZeroSet_isClosed :
    IsClosed {t : ℝ | thetaXiRealSymbol t = 0} :=
  isClosed_eq thetaXiRealSymbol_contDiff.continuous continuous_const

/-- Actual isolated radii make the original real Xi zero set discrete. -/
theorem thetaXiRealZeroSet_isDiscrete :
    IsDiscrete {t : ℝ | thetaXiRealSymbol t = 0} := by
  apply isDiscrete_iff_forall_mem_exists_isOpen.mpr
  intro t ht
  obtain ⟨δ, hδ, hzero⟩ := thetaXiRealSymbol_exists_isolating_radius t
  refine ⟨Metric.ball t δ, Metric.isOpen_ball, ?_⟩
  ext x
  constructor
  · intro hx
    apply Set.mem_singleton_iff.mpr
    exact hzero x (by simpa only [Metric.mem_ball, Real.dist_eq] using hx.1) hx.2
  · intro hx
    have hxt : x = t := Set.mem_singleton_iff.mp hx
    subst x
    exact ⟨Metric.mem_ball_self hδ, ht⟩

/-- Every compact original real set contains only finitely many actual Xi zeros. -/
theorem thetaXiRealZeros_inter_compact_finite
    (K : Set ℝ) (hK : IsCompact K) :
    {t : ℝ | t ∈ K ∧ thetaXiRealSymbol t = 0}.Finite := by
  change (K ∩ {t : ℝ | thetaXiRealSymbol t = 0}).Finite
  exact (hK.inter_right thetaXiRealZeroSet_isClosed).finite
    (thetaXiRealZeroSet_isDiscrete.mono Set.inter_subset_right)

/-- Finiteness holds on the CLOSED support of every original compact Schwartz test. -/
theorem thetaXiRealZeros_in_compact_tsupport_finite
    (φ : 𝓢(ℝ, ℂ)) (hφ : HasCompactSupport (φ : ℝ → ℂ)) :
    {t : ℝ | t ∈ tsupport (φ : ℝ → ℂ) ∧ thetaXiRealSymbol t = 0}.Finite :=
  thetaXiRealZeros_inter_compact_finite (tsupport (φ : ℝ → ℂ)) hφ

/-- The exact finite set of actual Xi zeros in a compact test's CLOSED support. -/
def thetaXiCompactTestZeros
    (φ : 𝓢(ℝ, ℂ)) (hφ : HasCompactSupport (φ : ℝ → ℂ)) : Finset ℝ :=
  (thetaXiRealZeros_in_compact_tsupport_finite φ hφ).toFinset

theorem thetaXiCompactTestZeros_mem_iff
    (φ : 𝓢(ℝ, ℂ)) (hφ : HasCompactSupport (φ : ℝ → ℂ)) (t : ℝ) :
    t ∈ thetaXiCompactTestZeros φ hφ ↔
      t ∈ tsupport (φ : ℝ → ℂ) ∧ thetaXiRealSymbol t = 0 := by
  exact Set.Finite.mem_toFinset (thetaXiRealZeros_in_compact_tsupport_finite φ hφ)

/-- An original test minus the genuine finite isolating-cutoff products. -/
def thetaXiCompactTestRemainder (W : Finset ℝ) (φ : 𝓢(ℝ, ℂ)) : 𝓢(ℝ, ℂ) :=
  φ - ∑ t ∈ W, SchwartzMap.smulLeftCLM ℂ
    (thetaXiIsolatingCutoff t : ℝ → ℂ) φ

theorem thetaXiCompactTestRemainder_apply
    (W : Finset ℝ) (φ : 𝓢(ℝ, ℂ)) (x : ℝ) :
    thetaXiCompactTestRemainder W φ x =
      φ x - ∑ t ∈ W, thetaXiIsolatingCutoff t x * φ x := by
  simp only [thetaXiCompactTestRemainder, sub_apply, sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro t _
  rw [SchwartzMap.smulLeftCLM_apply_apply
    (thetaXiIsolatingCutoff t).hasTemperateGrowth, smul_eq_mul]

/-- No remainder support escapes the original test's CLOSED support. -/
theorem thetaXiCompactTestRemainder_tsupport_subset
    (W : Finset ℝ) (φ : 𝓢(ℝ, ℂ)) :
    tsupport (thetaXiCompactTestRemainder W φ : ℝ → ℂ) ⊆
      tsupport (φ : ℝ → ℂ) := by
  apply closure_minimal _ (isClosed_tsupport _)
  intro x hx
  by_contra hnot
  have hφx : φ x = 0 := image_eq_zero_of_notMem_tsupport hnot
  apply hx
  simp [thetaXiCompactTestRemainder_apply, hφx]

/-- The original remainder is compact whenever the original test is compact. -/
theorem thetaXiCompactTestRemainder_hasCompactSupport
    (W : Finset ℝ) (φ : 𝓢(ℝ, ℂ)) (hφ : HasCompactSupport (φ : ℝ → ℂ)) :
    HasCompactSupport (thetaXiCompactTestRemainder W φ : ℝ → ℂ) :=
  IsCompact.of_isClosed_subset hφ (isClosed_tsupport _)
    (thetaXiCompactTestRemainder_tsupport_subset W φ)

/-- A genuine isolating cutoff has zero germ at EVERY distinct actual real Xi zero. -/
theorem thetaXiIsolatingCutoff_vanish_germ_at_other_zero
    (s t : ℝ) (hst : t ≠ s) (ht : thetaXiRealSymbol t = 0) :
    (thetaXiIsolatingCutoff s : ℝ → ℂ) =ᶠ[𝓝 t] 0 := by
  apply notMem_tsupport_iff_eventuallyEq.mp
  intro hmem
  exact hst (thetaXiIsolatingCutoff_isolates_zero s t hmem ht)

/-- Finitely many genuine zero/one germs make the original remainder vanish near each listed zero. -/
theorem thetaXiCompactTestRemainder_vanish_germ_at_zero
    (W : Finset ℝ) (φ : 𝓢(ℝ, ℂ)) (t : ℝ)
    (htW : t ∈ W) (ht : thetaXiRealSymbol t = 0) :
    (thetaXiCompactTestRemainder W φ : ℝ → ℂ) =ᶠ[𝓝 t] 0 := by
  classical
  obtain ⟨δ, hδ, hone⟩ := thetaXiIsolatingCutoff_eq_one_near t
  have hown : ∀ᶠ x in 𝓝 t, thetaXiIsolatingCutoff t x = 1 :=
    Metric.eventually_nhds_iff.mpr ⟨δ, hδ, fun {x} hx => hone x (by
      rw [Real.dist_eq] at hx
      exact hx.le)⟩
  have hall : ∀ᶠ x in 𝓝 t, ∀ s ∈ W,
      thetaXiIsolatingCutoff s x = if s = t then 1 else 0 := by
    apply (Filter.eventually_all_finset W).mpr
    intro s _
    by_cases hst : s = t
    · subst s
      simpa using hown
    · have hother :=
        thetaXiIsolatingCutoff_vanish_germ_at_other_zero s t (fun h => hst h.symm) ht
      change ∀ᶠ x in 𝓝 t, thetaXiIsolatingCutoff s x = 0 at hother
      simpa only [if_neg hst] using hother
  filter_upwards [hall] with x hx
  have hsum : (∑ s ∈ W, thetaXiIsolatingCutoff s x * φ x) = φ x := by
    calc
      (∑ s ∈ W, thetaXiIsolatingCutoff s x * φ x) =
          thetaXiIsolatingCutoff t x * φ x :=
        Finset.sum_eq_single t (by
          intro s hs hst
          simp only [hx s hs, if_neg hst, zero_mul]) (by
          intro hnot
          exact (hnot htW).elim)
      _ = φ x := by simp [hx t htW]
  change thetaXiCompactTestRemainder W φ x = 0
  rw [thetaXiCompactTestRemainder_apply, hsum]
  simp

/-- Covering all zeros in the original CLOSED support excludes every zero from the remainder. -/
theorem thetaXiCompactTestRemainder_zero_free_tsupport
    (W : Finset ℝ) (φ : 𝓢(ℝ, ℂ))
    (hcover : ∀ t ∈ tsupport (φ : ℝ → ℂ), thetaXiRealSymbol t = 0 → t ∈ W) :
    ∀ t ∈ tsupport (thetaXiCompactTestRemainder W φ : ℝ → ℂ),
      thetaXiRealSymbol t ≠ 0 := by
  intro t ht hzero
  have htφ := thetaXiCompactTestRemainder_tsupport_subset W φ ht
  have hgerm := thetaXiCompactTestRemainder_vanish_germ_at_zero W φ t
    (hcover t htφ hzero) hzero
  exact (notMem_tsupport_iff_eventuallyEq.mpr hgerm) ht

/-- Exact reconstruction on EVERY compact original test for any finite covering set of actual zeros. -/
theorem thetaXiTemperedKernel_compact_reconstruction_of_cover
    (Q : 𝓢'(ℝ, ℂ)) (hQ : thetaXiTemperedMultiplier Q = 0)
    (W : Finset ℝ) (φ : 𝓢(ℝ, ℂ)) (hφ : HasCompactSupport (φ : ℝ → ℂ))
    (hcover : ∀ t ∈ tsupport (φ : ℝ → ℂ), thetaXiRealSymbol t = 0 → t ∈ W) :
    Q φ = ∑ t ∈ W, thetaXiTemperedLocalization t Q φ := by
  have hrem := thetaXiTemperedKernel_eq_zero_of_compact_tsupport_nonvanishing Q hQ
    (thetaXiCompactTestRemainder W φ)
    (thetaXiCompactTestRemainder_hasCompactSupport W φ hφ)
    (thetaXiCompactTestRemainder_zero_free_tsupport W φ hcover)
  have hlinear : Q φ - ∑ t ∈ W, Q (SchwartzMap.smulLeftCLM ℂ
      (thetaXiIsolatingCutoff t : ℝ → ℂ) φ) = 0 := by
    simpa only [thetaXiCompactTestRemainder, map_sub, map_sum] using hrem
  calc
    Q φ = ∑ t ∈ W, Q (SchwartzMap.smulLeftCLM ℂ
        (thetaXiIsolatingCutoff t : ℝ → ℂ) φ) := sub_eq_zero.mp hlinear
    _ = ∑ t ∈ W, thetaXiTemperedLocalization t Q φ := by
      apply Finset.sum_congr rfl
      intro t _
      simpa only [thetaXiTemperedLocalization] using
        (thetaTemperedLocalize_apply (thetaXiIsolatingCutoff t) Q φ).symm

/-- The actual Xi kernel reconstructs from its canonical localizers on ALL compact original tests. -/
theorem thetaXiTemperedKernel_compact_reconstruction
    (Q : 𝓢'(ℝ, ℂ)) (hQ : thetaXiTemperedMultiplier Q = 0)
    (φ : 𝓢(ℝ, ℂ)) (hφ : HasCompactSupport (φ : ℝ → ℂ)) :
    Q φ = ∑ t ∈ thetaXiCompactTestZeros φ hφ, thetaXiTemperedLocalization t Q φ := by
  apply thetaXiTemperedKernel_compact_reconstruction_of_cover Q hQ _ φ hφ
  intro t ht hzero
  exact (thetaXiCompactTestZeros_mem_iff φ hφ t).mpr ⟨ht, hzero⟩

end RHTower
