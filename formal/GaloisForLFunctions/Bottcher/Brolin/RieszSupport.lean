/-
# Böttcher tower — Brolin GAP-A: the support theorem `J ⊆ supp μ_c`

Third GAP-A limb.  The Brolin measure charges every ball centred on the Julia
frontier: `frontier (filledJulia c) ⊆ supp μ_c`.  This is the input that discharges
`BackwardOrbitDense` (via `BrolinJuliaBallPositiveAt`) and feeds the q62
both-connected endgame.

## The argument (Riesz + Weyl + minimum principle)

Suppose a Julia frontier point `p` had a ball `B = ball p ε` with `μ(B) = 0`.
Testing the smooth Riesz identity `∫ φ dμ = (2π)⁻¹ ∫ G_c Δφ` (STEP 2,
`isRieszMeasureOfSmooth_gapAMu_of_filledJulia_null`) against `φ` supported in `B`
gives `∫ φ dμ = 0`, hence `∫ G_c Δφ = 0`: `G_c` is **weakly harmonic** in `B`.
Weyl's lemma (`WeylOnBall`, the one mathlib-absent input here — distributional
harmonicity ⟹ pointwise harmonicity) upgrades this to `HarmonicOnNhd G_c B`.  But
`G_c(p) = 0` (`p ∈ J ⊆ K_c`) is an interior minimum of the nonnegative harmonic
`G_c`, so by the maximum principle (`harmonic_eqOn_const_of_isMaxOn`, applied to
`-G_c`) `G_c ≡ 0` on `B` — contradicting `G_c > 0` at the basin points `B` meets
because `p ∈ frontier`.

The reduction `frontier_filledJulia_subset_support_of_isRieszMeasureOfSmooth` is
measure-agnostic: it applies to any `μ` satisfying the smooth Riesz identity for
`G_c`, so it also carries the arbitrary-target Brolin measures once their Riesz
identity is available.  The two remaining unconditional inputs are `WeylOnBall`
(elliptic regularity) and `volume (filledJulia c) = 0` (hyperbolic Julia null).
-/
import GaloisForLFunctions.Bottcher.Brolin.RieszLimit
import GaloisForLFunctions.Bottcher.Brolin.TargetLimit
import GaloisForLFunctions.Bottcher.HarmonicMaxPrinciple
import Mathlib.MeasureTheory.Measure.Support

open MeasureTheory Complex Filter Metric Set Laplacian InnerProductSpace
open scoped Laplacian Real Topology

namespace Bottcher

noncomputable section

/-- **Weyl's lemma interface on balls.**  `WeylOnBall G` says: a function that is
*weakly harmonic* on a ball (annihilates `∫ G · Δφ` for every `C²` bump supported
in the ball) is genuinely `HarmonicOnNhd` there.  This is the mathlib-absent
elliptic-regularity input of the support theorem, isolated as one clean `Prop`. -/
def WeylOnBall (G : ℂ → ℝ) : Prop :=
  ∀ (p : ℂ) (ε : ℝ), 0 < ε →
    (∀ φ : ℂ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ Metric.ball p ε →
      ∫ z, G z * Δ φ z = 0) →
    HarmonicOnNhd G (Metric.ball p ε)

/-- **The GAP-A support theorem (reduction).**  If `μ` is the smooth-distributional
`(2π)⁻¹ Δ G_c` and Weyl's lemma holds for `G_c`, then `μ` charges every Julia-frontier
ball: `frontier (filledJulia c) ⊆ supp μ`.  Measure-agnostic — reusable for every
Brolin target measure once its Riesz identity is available. -/
theorem frontier_filledJulia_subset_support_of_isRieszMeasureOfSmooth
    {c : ℂ} {μ : Measure ℂ}
    (hRiesz : IsRieszMeasureOfSmooth μ (greenFunctionDyn c))
    (hWeyl : WeylOnBall (greenFunctionDyn c)) :
    frontier (filledJulia c) ⊆ μ.support := by
  intro p hp
  rw [Measure.mem_support_iff_forall]
  intro U hU
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp hU
  refine lt_of_lt_of_le ?_ (measure_mono hεU)
  by_contra hle
  rw [not_lt, le_zero_iff] at hle
  have hwh : ∀ φ : ℂ → ℝ, ContDiff ℝ 2 φ → HasCompactSupport φ → tsupport φ ⊆ Metric.ball p ε →
      ∫ z, greenFunctionDyn c z * Δ φ z = 0 := by
    intro φ hφ hφc hφsupp
    have hRz := hRiesz φ hφ hφc
    have hint0 : ∫ z, φ z ∂μ = 0 := by
      have hae : (fun z => φ z) =ᵐ[μ] (fun _ => (0:ℝ)) := by
        have hnull : ∀ᵐ z ∂μ, z ∉ Metric.ball p ε := by
          rw [ae_iff]; simp only [not_not]
          rwa [show {z : ℂ | z ∈ Metric.ball p ε} = Metric.ball p ε from rfl]
        filter_upwards [hnull] with z hz
        exact image_eq_zero_of_notMem_tsupport (fun h => hz (hφsupp h))
      rw [integral_congr_ae hae, integral_zero]
    rw [hint0] at hRz
    have h2π : (2 * Real.pi) ≠ 0 := ne_of_gt Real.two_pi_pos
    exact (mul_eq_zero.mp hRz.symm).resolve_left (inv_ne_zero h2π)
  have hharm : HarmonicOnNhd (greenFunctionDyn c) (Metric.ball p ε) := hWeyl p ε hε hwh
  have hGp : greenFunctionDyn c p = 0 :=
    (greenFunctionDyn_eq_zero_iff c p).mpr ((isClosed_filledJulia c).frontier_subset hp)
  have hmax : IsMaxOn (-greenFunctionDyn c) (Metric.ball p ε) p := by
    intro z _
    show (-greenFunctionDyn c) z ≤ (-greenFunctionDyn c) p
    simp only [Pi.neg_apply, hGp, neg_zero, neg_nonpos]
    exact greenFunctionDyn_nonneg c z
  have hconst : Set.EqOn (-greenFunctionDyn c) (fun _ => (-greenFunctionDyn c) p) (Metric.ball p ε) :=
    harmonic_eqOn_const_of_isMaxOn (convex_ball p ε).isPreconnected Metric.isOpen_ball
      hharm.neg (Metric.mem_ball_self hε) hmax
  have hpcl : p ∈ closure (filledJulia c)ᶜ := by
    rw [frontier_eq_closure_inter_closure] at hp; exact hp.2
  obtain ⟨q, hqJc, hqdist⟩ := Metric.mem_closure_iff.mp hpcl ε hε
  have hqball : q ∈ Metric.ball p ε := by rw [Metric.mem_ball']; exact hqdist
  have hGq_pos : 0 < greenFunctionDyn c q := by
    rcases (greenFunctionDyn_nonneg c q).lt_or_eq with h | h
    · exact h
    · exact absurd ((greenFunctionDyn_eq_zero_iff c q).mp h.symm) hqJc
  have hGq_zero : greenFunctionDyn c q = 0 := by
    have hh := hconst hqball
    simp only [Pi.neg_apply, hGp, neg_zero] at hh
    linarith [hh]
  linarith [hGq_pos, hGq_zero]

/-- **The GAP-A support theorem for the zero-target Brolin measure**, conditional on
the two named analytic inputs: Julia-set Lebesgue-nullity (`hnull`) and Weyl's lemma
(`hWeyl`).  Combines `isRieszMeasureOfSmooth_gapAMu_of_filledJulia_null` (STEP 2) with
the reduction above. -/
theorem frontier_filledJulia_subset_support_gapAMu (c : ℂ)
    (hnull : volume (filledJulia c) = 0)
    (hWeyl : WeylOnBall (greenFunctionDyn c)) :
    frontier (filledJulia c) ⊆ (gapAMu c).support :=
  frontier_filledJulia_subset_support_of_isRieszMeasureOfSmooth
    (isRieszMeasureOfSmooth_gapAMu_of_filledJulia_null c hnull) hWeyl

/-- **The GAP-A limit Riesz identity for the arbitrary-target Brolin measure.**
`limitingBrolinMeasureAt c a = (2π)⁻¹ Δ G_c` for every target `a`, conditional on
Julia-null.  Same Fubini bridge as the zero-target case, now using the target-`a`
basin representation `green_eq_neg_logPotential_limitingBrolinMeasureAt_on_basin`.
This is what the q62 support consumer reads (it is stated on `limitingBrolinMeasureAt`,
not `gapAMu`). -/
theorem isRieszMeasureOfSmooth_limitingBrolinMeasureAt_of_filledJulia_null (c a : ℂ)
    (hnull : volume (filledJulia c) = 0) :
    IsRieszMeasureOfSmooth (limitingBrolinMeasureAt c a) (greenFunctionDyn c) := by
  have hcarrier : limitingBrolinMeasureAt c a (Metric.closedBall 0 (max 2 ‖c‖))ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr (filledJulia_subset_closedBall c))
      (limitingBrolinMeasureAt_filledJulia_compl c a)
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ∉ filledJulia c := by
    rw [ae_iff]; simpa using hnull
  have hrep : (fun z => greenFunctionDyn c z)
      =ᵐ[volume] fun z => - logPotential (limitingBrolinMeasureAt c a) z := by
    filter_upwards [hae] with z hz
    exact green_eq_neg_logPotential_limitingBrolinMeasureAt_on_basin hz
  exact isRieszMeasureOfSmooth_of_potentialRep_ae_carrier
    (limitingBrolinMeasureAt c a) hcarrier _ hrep

/-- **The GAP-A support theorem for the arbitrary-target Brolin measure**, conditional
on Julia-null (`hnull`) and Weyl's lemma (`hWeyl`).  This conclusion is definitionally
`LimitingBrolinMeasureAtSupportsJulia c a`, the q62 both-connected support input. -/
theorem frontier_filledJulia_subset_support_limitingBrolinMeasureAt (c a : ℂ)
    (hnull : volume (filledJulia c) = 0)
    (hWeyl : WeylOnBall (greenFunctionDyn c)) :
    frontier (filledJulia c) ⊆ (limitingBrolinMeasureAt c a).support :=
  frontier_filledJulia_subset_support_of_isRieszMeasureOfSmooth
    (isRieszMeasureOfSmooth_limitingBrolinMeasureAt_of_filledJulia_null c a hnull) hWeyl

end

end Bottcher
