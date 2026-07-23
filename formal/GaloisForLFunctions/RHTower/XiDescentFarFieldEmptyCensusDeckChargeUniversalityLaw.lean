import GaloisForLFunctions.RHTower.XiDescentCircleLocalGlobalDeckChargeUniversalityLaw
import GaloisForLFunctions.RHTower.XiDescentFarFieldAllRungLoopDrainUniversalityLaw

/-!
# Xi-descent far-field empty-census deck-charge universality

The Euler-product far field is locally zero-free after square descent.  Intersecting that
zero-free radius with the all-rung loop-drain radius upgrades local charge triviality to an exact
global circle certificate: the enclosed Xi-descent zero census is empty, its additive sum and
multiplicative local-charge product are empty, and every charge avatar is trivial.
-/

open Complex Set Metric Filter

namespace RHTower

noncomputable section

/-- **Xi-descent far-field empty-census deck-charge universality law.**  Every far-right Xi point
has a descended zero-free ball such that every smaller circle has an empty exact zero census,
zero additive loop charge, unit deck character, and unit local carrier charges at every dyadic
rung. -/
theorem xiDescent_farField_emptyCensusDeckChargeUniversality
    {ρ : ℂ} (hfar : 1 < ρ.re) (k : ℕ) :
    ∃ R₀ > 0, ∀ r : ℝ, 0 < r → r < R₀ →
      ∃ t : Finset ℂ,
        t = ∅ ∧
        (∀ w, w ∈ t ↔
          ‖w - (ρ - (1 / 2 : ℂ)) ^ 2‖ < r ∧ xiDescent w = 0) ∧
        loopCharge k
            (fun θ => xiDescent ((ρ - (1 / 2 : ℂ)) ^ 2 +
              (r : ℂ) * exp (I * (θ : ℂ)))) 0 (2 * Real.pi) =
          ∑ w ∈ t,
            wCharge (2 ^ k) ((analyticOrderAt xiDescent w).toNat : ℤ) ∧
        deckChar (2 ^ k)
            (loopCharge k
              (fun θ => xiDescent ((ρ - (1 / 2 : ℂ)) ^ 2 +
                (r : ℂ) * exp (I * (θ : ℂ)))) 0 (2 * Real.pi)) =
          ∏ w ∈ t, carrierCharge xiDescent k w ∧
        (∀ w, ‖w - (ρ - (1 / 2 : ℂ)) ^ 2‖ < r →
          xiDescent w ≠ 0) ∧
        loopCharge k
            (fun θ => xiDescent ((ρ - (1 / 2 : ℂ)) ^ 2 +
              (r : ℂ) * exp (I * (θ : ℂ)))) 0 (2 * Real.pi) = 0 ∧
        deckChar (2 ^ k)
            (loopCharge k
              (fun θ => xiDescent ((ρ - (1 / 2 : ℂ)) ^ 2 +
                (r : ℂ) * exp (I * (θ : ℂ)))) 0 (2 * Real.pi)) = 1 ∧
        carrierCharge xiDescent k ((ρ - (1 / 2 : ℂ)) ^ 2) = 1 ∧
        carrierCharge xi k ρ = 1 := by
  let center : ℂ := (ρ - (1 / 2 : ℂ)) ^ 2
  have hright : ρ ∈ rightHalf := by
    rw [mem_rightHalf]
    linarith
  have hpositive : 0 < (ρ - (1 / 2 : ℂ)).re := by
    rw [Complex.sub_re]
    norm_num
    have := mem_rightHalf.mp hright
    linarith
  have hcenterSlit : center ∈ slitPlane := by
    exact sq_mem_slitPlane_of_re_pos hpositive
  have hcenterNe : xiDescent center ≠ 0 := by
    change xiDescent ((ρ - (1 / 2 : ℂ)) ^ 2) ≠ 0
    rw [← xi_eq_xiDescent ρ]
    exact xi_ne_zero_of_one_lt_re hfar
  have hnonzero : {w : ℂ | xiDescent w ≠ 0} ∈ nhds center :=
    (xiDescent_analyticAt hcenterSlit).continuousAt.eventually_ne hcenterNe
  obtain ⟨Rball, hRball, hball⟩ := Metric.mem_nhds_iff.mp hnonzero
  obtain ⟨Rdrain, hRdrain, hdrain⟩ :=
    xiDescent_farField_allRungLocalLoopDrain hfar k
  refine ⟨min Rball Rdrain, lt_min hRball hRdrain, ?_⟩
  intro r hr hrRadius
  have hrBall : r < Rball := lt_of_lt_of_le hrRadius (min_le_left _ _)
  have hrDrain : r < Rdrain := lt_of_lt_of_le hrRadius (min_le_right _ _)
  have hzeroFree :
      ∀ w, ‖w - center‖ < r → xiDescent w ≠ 0 := by
    intro w hw
    apply hball
    rw [Metric.mem_ball, Complex.dist_eq]
    exact hw.trans hrBall
  have hboundary :
      ∀ w, ‖w - center‖ = r → xiDescent w ≠ 0 := by
    intro w hw
    apply hball
    rw [Metric.mem_ball, Complex.dist_eq, hw]
    exact hrBall
  obtain ⟨t, ht, hsum, hproduct⟩ :=
    xiDescent_circle_localGlobalDeckCharge center hr hboundary k
  have htEmpty : t = ∅ := by
    ext w
    constructor
    · intro hw
      obtain ⟨hwInside, hwZero⟩ := (ht w).mp hw
      exact (hzeroFree w hwInside hwZero).elim
    · simp
  obtain ⟨hloop, hdeck, hdescent, hxi⟩ := hdrain r hr hrDrain
  refine ⟨t, htEmpty, ?_, ?_, ?_, ?_, hloop, hdeck, hdescent, hxi⟩
  · simpa only [center] using ht
  · simpa only [center] using hsum
  · simpa only [center] using hproduct
  · simpa only [center] using hzeroFree

end

end RHTower
