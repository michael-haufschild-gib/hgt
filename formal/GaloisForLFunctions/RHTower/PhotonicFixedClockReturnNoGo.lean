import GaloisForLFunctions.HTGeometry.AnalyticCofiniteTransfer
import GaloisForLFunctions.RHTower.PhotonicParabolicReturn
import GaloisForLFunctions.RHTower.ZetaTruncatedExtension
import Mathlib.NumberTheory.LSeries.RiemannZeta

open Filter Topology Complex
open scoped Matrix.Norms.Elementwise

/-!
# Fixed-clock Floquet alias obstruction for the PTR return

The corpus's literal temporal-Maxwell slabs realize a fixed parabolic cell.
The zeta return instead enters through an externally weighted Mellin sum.
Any stroboscopic source/reader depending only on one clock multiplier
`exp (-T*s)` is vertically periodic, even if its readout is arbitrary.
The zeta diagonal of `photonicReturn` is not. This kills that entire
single-multiplier landing, not nonlocal Mellin retiming, continuous-time
within-cycle data, or multi-clock sources.
-/

namespace RHTower

private theorem zeta_no_shift_cofinite (ω : ℂ) (hω : ω ≠ 0)
    (h : ∀ s : ℂ, s ≠ 1 → s + ω ≠ 1 → riemannZeta (s + ω) = riemannZeta s) :
    False := by
  have hωone : (1 : ℂ) + ω ≠ 1 := by
    intro he
    apply hω
    linear_combination he
  have hc : ContinuousAt (fun s : ℂ => riemannZeta (s + ω)) 1 := by
    have hshift : ContinuousAt (fun s : ℂ => s + ω) 1 :=
      (continuous_id.add continuous_const).continuousAt
    exact ContinuousAt.comp (f := fun s : ℂ => s + ω)
      (analyticOn_riemannZeta (1 + ω) hωone).continuousAt hshift
  have hlim0 : Tendsto (fun s : ℂ => (s - 1) * riemannZeta (s + ω))
      (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have hprod : ContinuousAt (fun s : ℂ => (s - 1) * riemannZeta (s + ω)) 1 :=
      (continuousAt_id.sub continuousAt_const).mul hc
    have ht : Tendsto (fun s : ℂ => (s - 1) * riemannZeta (s + ω))
        (𝓝[≠] (1 : ℂ)) (𝓝 ((1 - 1) * riemannZeta (1 + ω))) :=
      hprod.tendsto.mono_left nhdsWithin_le_nhds
    simpa using ht
  have hne1 : ∀ᶠ s : ℂ in 𝓝[≠] (1 : ℂ), s ≠ 1 := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    simpa using hs
  have hne2 : ∀ᶠ s : ℂ in 𝓝[≠] (1 : ℂ), s + ω ≠ 1 := by
    have ho : IsOpen {s : ℂ | s + ω ≠ 1} := by
      change IsOpen ((fun s : ℂ => s + ω) ⁻¹' ({(1 : ℂ)}ᶜ))
      exact isClosed_singleton.isOpen_compl.preimage
        (continuous_id.add continuous_const)
    exact nhdsWithin_le_nhds (ho.mem_nhds hωone)
  have heq : (fun s : ℂ => (s - 1) * riemannZeta (s + ω)) =ᶠ[𝓝[≠] (1 : ℂ)]
      (fun s : ℂ => (s - 1) * riemannZeta s) := by
    filter_upwards [hne1, hne2] with s hs ht
    rw [h s hs ht]
  have hlim1 : Tendsto (fun s : ℂ => (s - 1) * riemannZeta (s + ω))
      (𝓝[≠] (1 : ℂ)) (𝓝 1) := riemannZeta_residue_one.congr' heq.symm
  exact zero_ne_one (tendsto_nhds_unique hlim0 hlim1)

private theorem zeta_no_pure_imaginary_period_on_right_half_plane
    (ω : ℂ) (hω : ω ≠ 0) (hωre : ω.re = 0) :
    ¬ ∀ s : ℂ, 2 < s.re → riemannZeta (s + ω) = riemannZeta s := by
  intro hperiod
  let S : Set ℂ := {1, 1 - ω}
  have hS : S.Finite := by simp [S]
  have hA : AnalyticOnNhd ℂ riemannZeta Sᶜ := by
    intro s hs
    have hs' : s ≠ 1 ∧ s ≠ 1 - ω := by simpa [S] using hs
    exact analyticOn_riemannZeta s hs'.1
  have hB : AnalyticOnNhd ℂ (fun s : ℂ => riemannZeta (s + ω)) Sᶜ := by
    intro s hs
    have hs' : s ≠ 1 ∧ s ≠ 1 - ω := by simpa [S] using hs
    have hne : s + ω ≠ 1 := by
      intro he
      apply hs'.2
      linear_combination he
    exact (analyticOn_riemannZeta (s + ω) hne).comp
      (f := fun z : ℂ => z + ω) (analyticAt_id.add analyticAt_const)
  have hconn : IsPreconnected Sᶜ :=
    GaloisForLFunctions.HTGeometry.isPreconnected_compl_finite hS
  have h3S : (3 : ℂ) ∈ Sᶜ := by
    have h3two : (3 : ℂ) ≠ 1 - ω := by
      intro he
      have hre := congrArg Complex.re he
      simp only [Complex.sub_re, Complex.one_re] at hre
      norm_num [hωre] at hre
    simp [S, h3two]
  have hUopen : IsOpen {s : ℂ | 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have h3U : (3 : ℂ) ∈ {s : ℂ | 2 < s.re} := by norm_num
  have hevent : riemannZeta =ᶠ[𝓝 (3 : ℂ)]
      (fun s : ℂ => riemannZeta (s + ω)) := by
    filter_upwards [hUopen.mem_nhds h3U] with s hs
    exact (hperiod s hs).symm
  have heqon := hA.eqOn_of_preconnected_of_eventuallyEq hB hconn h3S hevent
  exact zeta_no_shift_cofinite ω hω (by
    intro s hs1 hs2
    have hsS : s ∈ Sᶜ := by
      simp only [S, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
      refine ⟨hs1, ?_⟩
      intro he
      exact hs2 (by linear_combination he)
    exact (heqon hsS).symm)

/-- No readout of one fixed-clock Floquet multiplier can equal zeta on its Dirichlet half-plane. The readout may be nonlinear or discontinuous. -/
theorem ptr_fixed_clock_factor_zeta_no_go (T : ℝ) (hT : 0 < T) :
    ¬ ∃ G : ℂ → ℂ, ∀ s : ℂ, 2 < s.re →
      G (Complex.exp (-(T : ℂ) * s)) = riemannZeta s := by
  let τ : ℝ := 2 * Real.pi / T
  let ω : ℂ := Complex.I * (τ : ℂ)
  have hτ : τ ≠ 0 := by
    dsimp [τ]
    exact div_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hT.ne'
  have hω : ω ≠ 0 := by
    dsimp [ω]
    exact mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hτ)
  have hωre : ω.re = 0 := by simp [ω]
  have hTτ : T * τ = 2 * Real.pi := by
    dsimp [τ]
    field_simp [hT.ne']
  have hexpneg : Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
    rw [Complex.exp_neg, Complex.exp_two_pi_mul_I]
    simp
  have hperiod (s : ℂ) :
      Complex.exp (-(T : ℂ) * (s + ω)) = Complex.exp (-(T : ℂ) * s) := by
    have harg : -(T : ℂ) * (s + ω) =
        -(T : ℂ) * s + -(2 * (Real.pi : ℂ) * Complex.I) := by
      dsimp [ω]
      have hcast : ((T * τ : ℝ) : ℂ) = 2 * (Real.pi : ℂ) := by
        rw [hTτ]
        push_cast
        ring
      push_cast at hcast
      linear_combination -Complex.I * hcast
    rw [harg, Complex.exp_add, hexpneg, mul_one]
  rintro ⟨G, hG⟩
  apply zeta_no_pure_imaginary_period_on_right_half_plane ω hω hωre
  intro s hs
  have hsω : 2 < (s + ω).re := by
    simp only [Complex.add_re, hωre, add_zero]
    exact hs
  calc
    riemannZeta (s + ω) = G (Complex.exp (-(T : ℂ) * (s + ω))) :=
      (hG (s + ω) hsω).symm
    _ = G (Complex.exp (-(T : ℂ) * s)) := by rw [hperiod]
    _ = riemannZeta s := hG s hs

/-- The literal parabolic return matrix cannot come from any one-multiplier fixed-clock readout. -/
theorem ptr_fixed_clock_factor_photonic_return_no_go (T : ℝ) (hT : 0 < T) :
    ¬ ∃ G : ℂ → Matrix (Fin 2) (Fin 2) ℂ,
      ∀ s : ℂ, 2 < s.re →
        G (Complex.exp (-(T : ℂ) * s)) = RHTower.photonicReturn s := by
  rintro ⟨G, hG⟩
  apply ptr_fixed_clock_factor_zeta_no_go T hT
  refine ⟨fun z => G z 0 0, ?_⟩
  intro s hs
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0)
    (hG s hs)
  simpa [RHTower.photonicReturn, RHTower.photonicUpper] using hentry

/-- A source response holomorphic throughout the positive Laplace half-plane
cannot have zeta as its diagonal transfer on the Dirichlet half-plane.  The
obstruction is the residue at `s = 1`, not a failure of the initial series. -/
theorem ptr_right_halfplane_holomorphic_zeta_no_go (F : ℂ → ℂ)
    (hF : AnalyticOnNhd ℂ F {s : ℂ | 0 < s.re})
    (h : ∀ s : ℂ, 2 < s.re → F s = riemannZeta s) : False := by
  let U : Set ℂ := {s : ℂ | 0 < s.re} \ {1}
  have hFo : AnalyticOnNhd ℂ F U := hF.mono (by
    intro s hs
    exact hs.1)
  have hZo : AnalyticOnNhd ℂ riemannZeta U := by
    intro s hs
    exact analyticOn_riemannZeta s hs.2
  have h3 : (3 : ℂ) ∈ U := by
    constructor
    · norm_num
    · norm_num
  have hO : IsOpen {s : ℂ | 2 < s.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hev : F =ᶠ[𝓝 (3 : ℂ)] riemannZeta := by
    filter_upwards [hO.mem_nhds (by norm_num : (3 : ℂ) ∈ {s : ℂ | 2 < s.re})]
      with s hs
    exact h s hs
  have heq := hFo.eqOn_of_preconnected_of_eventuallyEq hZo
    isPreconnected_halfplane_punctured h3 hev
  have hFc : ContinuousAt F 1 :=
    (hF (1 : ℂ) (by norm_num : (1 : ℂ) ∈ {s : ℂ | 0 < s.re})).continuousAt
  have hlim0 : Tendsto (fun s : ℂ => (s - 1) * F s)
      (𝓝[≠] (1 : ℂ)) (𝓝 0) := by
    have hprod : ContinuousAt (fun s : ℂ => (s - 1) * F s) 1 :=
      (continuousAt_id.sub continuousAt_const).mul hFc
    have ht : Tendsto (fun s : ℂ => (s - 1) * F s)
        (𝓝[≠] (1 : ℂ)) (𝓝 ((1 - 1) * F 1)) :=
      hprod.tendsto.mono_left nhdsWithin_le_nhds
    simpa using ht
  have hnear : ∀ᶠ s : ℂ in 𝓝[≠] (1 : ℂ), s ∈ U := by
    have ho : IsOpen {s : ℂ | 0 < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    filter_upwards [nhdsWithin_le_nhds (ho.mem_nhds (by norm_num :
        (1 : ℂ) ∈ {s : ℂ | 0 < s.re})), self_mem_nhdsWithin] with s hs hne
    exact ⟨hs, by simpa using hne⟩
  have heqev : (fun s : ℂ => (s - 1) * F s) =ᶠ[𝓝[≠] (1 : ℂ)]
      (fun s : ℂ => (s - 1) * riemannZeta s) := by
    filter_upwards [hnear] with s hs
    rw [heq hs]
  have hlim1 : Tendsto (fun s : ℂ => (s - 1) * F s)
      (𝓝[≠] (1 : ℂ)) (𝓝 1) := riemannZeta_residue_one.congr' heqev.symm
  exact zero_ne_one (tendsto_nhds_unique hlim0 hlim1)

/-- In particular, an ordinary right-half-plane holomorphic matrix transfer
cannot be the PTR zeta return, even when its within-cycle readout is not a
function solely of the Floquet multiplier. -/
theorem ptr_right_halfplane_holomorphic_photonic_return_no_go
    (F : ℂ → Matrix (Fin 2) (Fin 2) ℂ)
    (hF : AnalyticOnNhd ℂ F {s : ℂ | 0 < s.re})
    (h : ∀ s : ℂ, 2 < s.re → F s = photonicReturn s) : False := by
  have h00 : AnalyticOnNhd ℂ (fun s => F s 0 0) {s : ℂ | 0 < s.re} := by
    intro s hs
    exact (hF s hs).apply 0 |>.apply 0
  apply ptr_right_halfplane_holomorphic_zeta_no_go (fun s => F s 0 0) h00
  intro s hs
  have hentry := congrArg (fun M : Matrix (Fin 2) (Fin 2) ℂ => M 0 0) (h s hs)
  simpa [photonicReturn, photonicUpper] using hentry

end RHTower
