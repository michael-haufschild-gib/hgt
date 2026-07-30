import GaloisForLFunctions.RHTower.CCMShiftedXiCancellation
import GaloisForLFunctions.RHTower.XiDeck

/-!
# The local pole jet of a Xi-cancelled shifted-zeta term

At a right-half Xi zero of multiplicity `m`, the corresponding cancelled
shifted-zeta term has a zero of order exactly `m - 1`.  This is the local,
multiplicity-safe input for the rectangular shifted-zeta contradiction.
-/

open Complex Filter Function Metric Set

namespace RHTower

noncomputable section

/-- The multiplicity of the Xi zero underlying a right-half divisor copy. -/
def xiRightMultiplicity (q : XiRightZeroCopy) : ℕ :=
  (analyticOrderAt xi (q.1.1 : ℂ)).toNat

theorem xiRightMultiplicity_pos (q : XiRightZeroCopy) :
    0 < xiRightMultiplicity q := by
  apply Nat.pos_of_ne_zero
  unfold xiRightMultiplicity
  exact xi_order_toNat_ne_zero (xi_eq_zero_of_mem_divisor_support q.1.1)

/-- Analytic vanishing order and divisor-copy cardinality agree exactly. -/
theorem xi_divisor_toNat_eq_xiRightMultiplicity (q : XiRightZeroCopy) :
    Int.toNat ((MeromorphicOn.divisor xi Set.univ) (q.1.1 : ℂ)) =
      xiRightMultiplicity q := by
  rw [MeromorphicOn.AnalyticOnNhd.divisor_apply
    xi_analyticOnNhd_univ (Set.mem_univ _)]
  change Int.toNat
      ((ENat.map Nat.cast (analyticOrderAt xi (q.1.1 : ℂ))).untop₀) =
    (analyticOrderAt xi (q.1.1 : ℂ)).toNat
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp
    (xi_order_ne_top (q.1.1 : ℂ))
  rw [← hm]
  simp

/-- The finite multiplicity fiber over the Xi support underlying `q`. -/
abbrev XiRightSupportFiber (q : XiRightZeroCopy) :=
  {r : XiRightZeroCopy // r.1.1 = q.1.1}

/-- The right-half copy fiber is canonically the finite analytic
multiplicity index. -/
def xiRightSupportFiberEquiv (q : XiRightZeroCopy) :
    XiRightSupportFiber q ≃ Fin (xiRightMultiplicity q) where
  toFun r := Fin.cast (by
    rw [r.2]
    exact xi_divisor_toNat_eq_xiRightMultiplicity q) r.1.1.2
  invFun i := by
    let j : Fin (Int.toNat
        ((MeromorphicOn.divisor xi Set.univ) (q.1.1 : ℂ))) :=
      Fin.cast (xi_divisor_toNat_eq_xiRightMultiplicity q).symm i
    let r0 : XiZeroCopy := ⟨q.1.1, j⟩
    have hr0 : 0 < (I * xiSpectralPoint r0).re := by
      simpa only [r0, xiSpectralPoint] using q.2
    exact ⟨⟨r0, hr0⟩, rfl⟩
  left_inv r := by
    rcases r with ⟨⟨⟨rho, i⟩, hpos⟩, hrho⟩
    change rho = q.1.1 at hrho
    subst rho
    apply Subtype.ext
    apply Subtype.ext
    apply Sigma.ext rfl
    rfl
  right_inv i := by
    apply Fin.ext
    rfl

instance (q : XiRightZeroCopy) : Fintype (XiRightSupportFiber q) :=
  Fintype.ofEquiv (Fin (xiRightMultiplicity q))
    (xiRightSupportFiberEquiv q).symm

theorem card_xiRightSupportFiber (q : XiRightZeroCopy) :
    Fintype.card (XiRightSupportFiber q) = xiRightMultiplicity q := by
  simpa using Fintype.card_congr (xiRightSupportFiberEquiv q)

theorem xiRightCenteredZero_eq_of_support_eq {q r : XiRightZeroCopy}
    (h : q.1.1 = r.1.1) :
    xiRightCenteredZero q = xiRightCenteredZero r := by
  simp only [xiRightCenteredZero, xiSpectralPoint]
  rw [h]

theorem xiRightShiftedPole_eq_of_support_eq {q r : XiRightZeroCopy}
    (h : q.1.1 = r.1.1) :
    xiRightShiftedPole q = xiRightShiftedPole r := by
  rw [xiRightShiftedPole, xiRightShiftedPole,
    xiRightCenteredZero_eq_of_support_eq h]

theorem xiRightMultiplicity_eq_of_support_eq {q r : XiRightZeroCopy}
    (h : q.1.1 = r.1.1) :
    xiRightMultiplicity q = xiRightMultiplicity r := by
  rw [xiRightMultiplicity, xiRightMultiplicity, h]

theorem xiRectangularRightCoefficient_eq_of_support_eq
    (L : ℝ) {q r : XiRightZeroCopy} (h : q.1.1 = r.1.1) :
    xiRectangularRightCoefficient L q = xiRectangularRightCoefficient L r := by
  rw [xiRectangularRightCoefficient, xiRectangularRightCoefficient,
    xiRightCenteredZero_eq_of_support_eq h]

theorem xiShiftedZetaCancelledTerm_eq_of_support_eq
    {q r : XiRightZeroCopy} (h : q.1.1 = r.1.1) :
    xiShiftedZetaCancelledTerm q = xiShiftedZetaCancelledTerm r := by
  funext s
  rw [xiShiftedZetaCancelledTerm, xiShiftedZetaCancelledTerm,
    xiRightCenteredZero_eq_of_support_eq h,
    xiRightShiftedPole_eq_of_support_eq h, h]

theorem xiRightShiftedPole_ne_of_support_ne
    {q r : XiRightZeroCopy} (h : q.1.1 ≠ r.1.1) :
    xiRightShiftedPole q ≠ xiRightShiftedPole r := by
  intro hpole
  apply h
  apply Subtype.ext
  have hcenter : xiRightCenteredZero q = xiRightCenteredZero r := by
    rw [xiRightShiftedPole, xiRightShiftedPole] at hpole
    exact add_left_cancel hpole
  rw [xiRightCenteredZero_eq_support_sub_half,
    xiRightCenteredZero_eq_support_sub_half] at hcenter
  linear_combination hcenter

/-- At the shifted pole belonging to `q`, every term over a different Xi
support is divisible by the full multiplicity of `q`; only the equal-support
fiber can contribute to the preceding jet. -/
theorem exists_xiShiftedZetaCancelledTerm_off_support_factorization
    (q r : XiRightZeroCopy) (hqr : q.1.1 ≠ r.1.1) :
    ∃ u : ℂ → ℂ,
      AnalyticAt ℂ u (xiRightShiftedPole q) ∧
      xiShiftedZetaCancelledTerm r =ᶠ[nhds (xiRightShiftedPole q)]
        fun s => (s - xiRightShiftedPole q) ^ xiRightMultiplicity q * u s := by
  obtain ⟨R, hR, h, hhan, _hh0, hfact⟩ := xi_peel_ball (q.1.1 : ℂ)
  let u : ℂ → ℂ := fun s =>
    h (s - 1 / 2) * riemannZeta (s - xiRightCenteredZero r)
  have hball : (q.1.1 : ℂ) ∈ ball (q.1.1 : ℂ) R := mem_ball_self hR
  have hshift : xiRightShiftedPole q - 1 / 2 = (q.1.1 : ℂ) :=
    xiRightShiftedPole_sub_half q
  have hpoles : xiRightShiftedPole q ≠ xiRightShiftedPole r :=
    xiRightShiftedPole_ne_of_support_ne hqr
  have hzeta : xiRightShiftedPole q - xiRightCenteredZero r ≠ 1 := by
    intro hz
    apply hpoles
    simp only [xiRightShiftedPole] at hz ⊢
    linear_combination hz
  refine ⟨u, ?_, ?_⟩
  · apply AnalyticAt.mul
    · exact (hhan (q.1.1 : ℂ) hball).comp_of_eq
        (analyticAt_id.sub analyticAt_const) hshift
    · have houter : AnalyticAt ℂ riemannZeta
          (xiRightShiftedPole q - xiRightCenteredZero r) :=
        analyticOn_riemannZeta
          (xiRightShiftedPole q - xiRightCenteredZero r) hzeta
      have hinner : AnalyticAt ℂ
          (fun s : ℂ => s - xiRightCenteredZero r)
          (xiRightShiftedPole q) :=
        analyticAt_id.sub analyticAt_const
      have hcomp : AnalyticAt ℂ
          (riemannZeta ∘ fun s : ℂ => s - xiRightCenteredZero r)
          (xiRightShiftedPole q) :=
        AnalyticAt.comp_of_eq
          (g := riemannZeta)
          (f := fun s : ℂ => s - xiRightCenteredZero r)
          (y := xiRightShiftedPole q - xiRightCenteredZero r)
          (x := xiRightShiftedPole q) houter hinner rfl
      simpa only [Function.comp_apply] using! hcomp
  · have hpoleball : xiRightShiftedPole q - 1 / 2 ∈ ball (q.1.1 : ℂ) R := by
      rw [hshift]
      exact hball
    filter_upwards [((continuousAt_id.sub_const (1 / 2 : ℂ)).eventually
      (isOpen_ball.mem_nhds hpoleball)),
      (isOpen_ne.mem_nhds hpoles)] with s hsball hsne
    rw [xiShiftedZetaCancelledTerm, Function.update_of_ne hsne,
      hfact (s - 1 / 2) hsball]
    have hcoord : (s - 1 / 2) - (q.1.1 : ℂ) =
        s - xiRightShiftedPole q := by
      rw [xiRightShiftedPole, xiRightCenteredZero_eq_support_sub_half]
      ring
    rw [hcoord]
    simp only [u, xiRightMultiplicity]
    ring

/-- Near its shifted pole, a Xi-cancelled shifted-zeta term is exactly the
`(m - 1)`-st power of the local coordinate times a nonvanishing analytic Xi
cofactor and the pole-filled zeta factor. -/
theorem exists_xiShiftedZetaCancelledTerm_local_factorization
    (q : XiRightZeroCopy) :
    ∃ R > 0, ∃ h : ℂ → ℂ,
      AnalyticOnNhd ℂ h (ball (q.1.1 : ℂ) R) ∧
      (∀ z ∈ ball (q.1.1 : ℂ) R, h z ≠ 0) ∧
      ∀ s : ℂ, s - 1 / 2 ∈ ball (q.1.1 : ℂ) R →
        xiShiftedZetaCancelledTerm q s =
          (s - xiRightShiftedPole q) ^ (xiRightMultiplicity q - 1) *
            h (s - 1 / 2) *
              regularizedRiemannZeta (s - xiRightCenteredZero q) := by
  obtain ⟨R, hR, h, hhan, hh0, hfact⟩ := xi_peel_ball (q.1.1 : ℂ)
  refine ⟨R, hR, h, hhan, hh0, ?_⟩
  intro s hs
  have hcoord : (s - 1 / 2) - (q.1.1 : ℂ) = s - xiRightShiftedPole q := by
    rw [xiRightShiftedPole, xiRightCenteredZero_eq_support_sub_half]
    ring
  by_cases hsp : s = xiRightShiftedPole q
  · subst s
    rw [xiShiftedZetaCancelledTerm, Function.update_self,
      xiRightShiftedPole_sub_half, xiRightShiftedPole_sub_centeredZero,
      regularizedRiemannZeta_one]
    have hball : (q.1.1 : ℂ) ∈ ball (q.1.1 : ℂ) R := mem_ball_self hR
    have heq : xi =ᶠ[nhds (q.1.1 : ℂ)]
        fun z => (z - (q.1.1 : ℂ)) ^ xiRightMultiplicity q * h z := by
      filter_upwards [isOpen_ball.mem_nhds hball] with z hz
      simpa [xiRightMultiplicity] using hfact z hz
    have hderiv : deriv xi (q.1.1 : ℂ) =
        deriv (fun z => (z - (q.1.1 : ℂ)) ^ xiRightMultiplicity q * h z)
          (q.1.1 : ℂ) := heq.deriv_eq
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero
      (Nat.ne_of_gt (xiRightMultiplicity_pos q))
    rw [hk] at hderiv ⊢
    cases k with
    | zero =>
        rw [hderiv]
        have hh := (hhan (q.1.1 : ℂ) hball).differentiableAt.hasDerivAt
        simpa using!
          ((((hasDerivAt_id (q.1.1 : ℂ)).sub_const (q.1.1 : ℂ)).pow 1).mul hh).deriv
    | succ k =>
        rw [hderiv]
        have hh := (hhan (q.1.1 : ℂ) hball).differentiableAt.hasDerivAt
        simpa using!
          ((((hasDerivAt_id (q.1.1 : ℂ)).sub_const (q.1.1 : ℂ)).pow (k + 2)).mul hh).deriv
  · rw [xiShiftedZetaCancelledTerm, Function.update_of_ne hsp,
      hfact (s - 1 / 2) hs, regularizedRiemannZeta_of_ne_one]
    · rw [hcoord]
      have hm := xiRightMultiplicity_pos q
      obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hm)
      change (s - xiRightShiftedPole q) ^ xiRightMultiplicity q *
          h (s - 1 / 2) * riemannZeta (s - xiRightCenteredZero q) = _
      rw [hk]
      simp only [Nat.succ_sub_one]
      rw [pow_succ, xiRightShiftedPole]
      ring
    · intro hz
      apply hsp
      rw [xiRightShiftedPole]
      linear_combination hz

/-- The cancellation loses exactly one order: at a Xi zero of multiplicity
`m`, the corresponding pole-filled shifted-zeta term has order `m - 1`. -/
theorem xiShiftedZetaCancelledTerm_order
    (q : XiRightZeroCopy) :
    analyticOrderAt (xiShiftedZetaCancelledTerm q) (xiRightShiftedPole q) =
      (xiRightMultiplicity q - 1 : ℕ) := by
  obtain ⟨R, hR, h, hhan, hh0, hfact⟩ :=
    exists_xiShiftedZetaCancelledTerm_local_factorization q
  let u : ℂ → ℂ := fun s =>
    h (s - 1 / 2) * regularizedRiemannZeta (s - xiRightCenteredZero q)
  have hball : (q.1.1 : ℂ) ∈ ball (q.1.1 : ℂ) R := mem_ball_self hR
  have hshift : xiRightShiftedPole q - 1 / 2 = (q.1.1 : ℂ) :=
    xiRightShiftedPole_sub_half q
  have hcenter : xiRightShiftedPole q - xiRightCenteredZero q = 1 :=
    xiRightShiftedPole_sub_centeredZero q
  have hu : AnalyticAt ℂ u (xiRightShiftedPole q) := by
    apply AnalyticAt.mul
    · exact (hhan (q.1.1 : ℂ) hball).comp_of_eq
        (analyticAt_id.sub analyticAt_const) hshift
    · exact (differentiable_regularizedRiemannZeta.analyticAt 1).comp_of_eq
        (analyticAt_id.sub analyticAt_const) hcenter
  have hu0 : u (xiRightShiftedPole q) ≠ 0 := by
    dsimp [u]
    rw [hshift, hcenter, regularizedRiemannZeta_one]
    exact mul_ne_zero (hh0 (q.1.1 : ℂ) hball) one_ne_zero
  have hev : xiShiftedZetaCancelledTerm q =ᶠ[nhds (xiRightShiftedPole q)]
      fun s => (s - xiRightShiftedPole q) ^ (xiRightMultiplicity q - 1) * u s := by
    have hpoleball : xiRightShiftedPole q - 1 / 2 ∈ ball (q.1.1 : ℂ) R := by
      rw [hshift]
      exact hball
    filter_upwards [((continuousAt_id.sub_const (1 / 2 : ℂ)).eventually
      (isOpen_ball.mem_nhds hpoleball))] with s hs
    simpa [u, mul_assoc] using hfact s hs
  have hterm : AnalyticAt ℂ (xiShiftedZetaCancelledTerm q)
      (xiRightShiftedPole q) :=
    differentiable_xiShiftedZetaCancelledTerm q |>.analyticAt _
  exact (hterm.analyticOrderAt_eq_natCast (n := xiRightMultiplicity q - 1)).2
    ⟨u, hu, hu0, hev⟩

end

end RHTower
