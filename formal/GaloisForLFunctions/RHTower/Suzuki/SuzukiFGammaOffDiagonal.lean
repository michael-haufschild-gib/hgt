import GaloisForLFunctions.RHTower.Suzuki.SuzukiHalfInnerLocalFactor
import GaloisForLFunctions.HTGeometry.UpperHalfPlaneCauchyVanishing

/-!
# Off-diagonal orthogonality of Suzuki's family `F_γ`

For two distinct zeros `γ ≠ δ` of `A = ξ(1/2 - iz)` the inner product of `F_γ` and `F_δ`
reduces to the real integral of the boundary energy `|A/E|²` against `1/((x-γ)(x-δ))`.  This
module shows that integral vanishes under the Riemann hypothesis.

The mechanism is Cauchy's theorem, not a residue computation.  The function
`(A/E) / ((z-γ)(z-δ))` — realized as the twice-iterated divided slope, which fills in the two
removable points — is holomorphic on the closed upper half-plane, is bounded there by `1`
times the Hermite--Biehler contraction bound, and decays like `‖z‖^{-2}`.  Hence its integral
over the real line is zero, and taking real parts converts `Re (A/E) = |A/E|²` into the
statement wanted.
-/

open Complex Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower
noncomputable section

theorem norm_dslope2_suzukiHalfInner_le (hRH : RiemannHypothesis) {γ δ : ℂ}
    (hγ : XiC γ = 0) (hδ : XiC δ = 0) (hne : δ ≠ γ) {z : ℂ} (hz : 0 ≤ z.im)
    (hR : 2 * (‖γ‖ + ‖δ‖ + 1) ≤ ‖z‖) :
    ‖dslope (dslope suzukiHalfInner γ) δ z‖ ≤ 4 / ‖z‖ ^ (2 : ℕ) := by
  have hzpos : 0 < ‖z‖ := by
    have h : (0 : ℝ) < 2 * (‖γ‖ + ‖δ‖ + 1) := by positivity
    linarith
  have hgz : ‖z‖ / 2 ≤ ‖z - γ‖ := by
    have h := norm_sub_norm_le z γ
    have : ‖γ‖ ≤ ‖z‖ / 2 := by linarith [norm_nonneg δ]
    linarith
  have hdz : ‖z‖ / 2 ≤ ‖z - δ‖ := by
    have h := norm_sub_norm_le z δ
    have : ‖δ‖ ≤ ‖z‖ / 2 := by linarith [norm_nonneg γ]
    linarith
  have hzγ : z ≠ γ := by
    intro h
    rw [h] at hzpos hgz
    rw [sub_self, norm_zero] at hgz
    linarith
  have hzδ : z ≠ δ := by
    intro h
    rw [h] at hzpos hdz
    rw [sub_self, norm_zero] at hdz
    linarith
  rw [dslope2_suzukiHalfInner_apply hγ hδ hne hzγ hzδ, norm_div, norm_mul]
  have hh := norm_suzukiHalfInner_le_one_of_rh hRH hz
  have hden : ‖z‖ ^ (2 : ℕ) / 4 ≤ ‖z - γ‖ * ‖z - δ‖ := by nlinarith [hgz, hdz, hzpos]
  have hpos : (0 : ℝ) < ‖z‖ ^ (2 : ℕ) / 4 := by positivity
  calc ‖suzukiHalfInner z‖ / (‖z - γ‖ * ‖z - δ‖) ≤ 1 / (‖z‖ ^ (2 : ℕ) / 4) := by gcongr
    _ = 4 / ‖z‖ ^ (2 : ℕ) := by field_simp

theorem integral_dslope2_suzukiHalfInner_eq_zero (hRH : RiemannHypothesis) {γ δ : ℂ}
    (hγ : XiC γ = 0) (hδ : XiC δ = 0) (hne : δ ≠ γ) :
    (∫ x : ℝ, dslope (dslope suzukiHalfInner γ) δ ((x : ℝ) : ℂ)) = 0 :=
  integral_eq_zero_of_upperHalfPlane_farDecay
    (M := 4) (R := 2 * (‖γ‖ + ‖δ‖ + 1))
    (fun z hz => differentiableAt_dslope2_suzukiHalfInner_of_rh hRH hγ hδ hne hz)
    (by positivity)
    (fun z hz hR => norm_dslope2_suzukiHalfInner_le hRH hγ hδ hne hz hR)

theorem integrable_dslope2_suzukiHalfInner (hRH : RiemannHypothesis) {γ δ : ℂ}
    (hγ : XiC γ = 0) (hδ : XiC δ = 0) (hne : δ ≠ γ) :
    Integrable (fun x : ℝ => dslope (dslope suzukiHalfInner γ) δ ((x : ℝ) : ℂ)) :=
  integrable_ofReal_of_farDecay
    (M := 4) (R := 2 * (‖γ‖ + ‖δ‖ + 1))
    (fun z hz => differentiableAt_dslope2_suzukiHalfInner_of_rh hRH hγ hδ hne hz)
    (by positivity)
    (fun z hz hR => norm_dslope2_suzukiHalfInner_le hRH hγ hδ hne hz hR)

theorem div_ofReal_re (z : ℂ) (c : ℝ) : (z / (c : ℂ)).re = z.re / c := by
  rw [Complex.div_re, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_ofReal]
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · rw [mul_zero, zero_div, add_zero]
    field_simp

/-- **The off-diagonal orthogonality integral.**  For distinct real zeros of `A` the boundary
energy `|A/E|²` integrates to zero against `1/((x-γ)(x-δ))`. -/
theorem integrable_and_integral_normSq_suzukiHalfInner_div_pair (hRH : RiemannHypothesis)
    {γ δ : ℝ} (hγ : XiC ((γ : ℝ) : ℂ) = 0) (hδ : XiC ((δ : ℝ) : ℂ) = 0) (hne : δ ≠ γ) :
    Integrable (fun x : ℝ => ‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ (2 : ℕ) / ((x - γ) * (x - δ))) ∧
      (∫ x : ℝ, ‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ (2 : ℕ) / ((x - γ) * (x - δ))) = 0 := by
  have hneC : ((δ : ℝ) : ℂ) ≠ ((γ : ℝ) : ℂ) := by
    simpa using hne
  have hint := integrable_dslope2_suzukiHalfInner hRH hγ hδ hneC
  have hzero := integral_dslope2_suzukiHalfInner_eq_zero hRH hγ hδ hneC
  have hcomm := Complex.reCLM.integral_comp_comm hint
  rw [hzero] at hcomm
  have hnull : volume ({γ, δ} : Set ℝ) = 0 :=
    (Set.Finite.insert γ (Set.finite_singleton δ)).measure_zero volume
  have hae : (fun x : ℝ =>
        Complex.reCLM (dslope (dslope suzukiHalfInner ((γ : ℝ) : ℂ)) ((δ : ℝ) : ℂ) ((x : ℝ) : ℂ)))
      =ᵐ[volume]
      fun x : ℝ => ‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ (2 : ℕ) / ((x - γ) * (x - δ)) := by
    filter_upwards [MeasureTheory.compl_mem_ae_iff.mpr hnull] with x hx
    have hxγ : ((x : ℝ) : ℂ) ≠ ((γ : ℝ) : ℂ) := by
      simp only [ne_eq, Complex.ofReal_inj]
      exact fun h => hx (by simp [h])
    have hxδ : ((x : ℝ) : ℂ) ≠ ((δ : ℝ) : ℂ) := by
      simp only [ne_eq, Complex.ofReal_inj]
      exact fun h => hx (by simp [h])
    have hcast : (((x : ℝ) : ℂ) - ((γ : ℝ) : ℂ)) * (((x : ℝ) : ℂ) - ((δ : ℝ) : ℂ))
        = (((x - γ) * (x - δ) : ℝ) : ℂ) := by push_cast; ring
    show (dslope (dslope suzukiHalfInner ((γ : ℝ) : ℂ)) ((δ : ℝ) : ℂ) ((x : ℝ) : ℂ)).re = _
    rw [dslope2_suzukiHalfInner_apply hγ hδ hneC hxγ hxδ, hcast, div_ofReal_re,
      ← norm_sq_suzukiHalfInner_ofReal x]
  refine ⟨hint.re.congr hae, ?_⟩
  rw [← MeasureTheory.integral_congr_ae hae]
  simpa using hcomm

theorem integrable_normSq_suzukiHalfInner_div_pair (hRH : RiemannHypothesis) {γ δ : ℝ}
    (hγ : XiC ((γ : ℝ) : ℂ) = 0) (hδ : XiC ((δ : ℝ) : ℂ) = 0) (hne : δ ≠ γ) :
    Integrable (fun x : ℝ => ‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ (2 : ℕ) / ((x - γ) * (x - δ))) :=
  (integrable_and_integral_normSq_suzukiHalfInner_div_pair hRH hγ hδ hne).1

/-- **The off-diagonal orthogonality integral.** -/
theorem integral_normSq_suzukiHalfInner_div_pair (hRH : RiemannHypothesis) {γ δ : ℝ}
    (hγ : XiC ((γ : ℝ) : ℂ) = 0) (hδ : XiC ((δ : ℝ) : ℂ) = 0) (hne : δ ≠ γ) :
    (∫ x : ℝ, ‖suzukiHalfInner ((x : ℝ) : ℂ)‖ ^ (2 : ℕ) / ((x - γ) * (x - δ))) = 0 :=
  (integrable_and_integral_normSq_suzukiHalfInner_div_pair hRH hγ hδ hne).2

end
end RHTower
