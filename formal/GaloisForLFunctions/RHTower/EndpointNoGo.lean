/-
The endpoint no-go: the parity datum is not the raw endpoint orientation signs.

Two facts collide.  The deck class of the anchored member is prime-set-RIGID:
anchoring multiplies both chart roots by one global root of the anchor, leaving the
overlap cocycle untouched.  The endpoint orientations are prime-set-STEERABLE: at the
two annulus basepoints the incidence imaginary part is a positive multiple of
`sin(arg z± − φ±)`, where `z± = −completedSEM N (ρ ± ci)` is prime-free and
`φ± = anchorTilt P (ρ ± ci)` is the tilt pair, which reaches every target box.  So the
endpoint sign pair takes every value while the deck class never moves, and no
prime-set-independent function of the two endpoint imaginary-part signs computes the
deck class.  The dictionary between the two-point orientation reading and the mod-2
deck cocycle must therefore pass through data that co-varies with the anchor on both
sides — the argument variation along the boundary arcs, not the endpoint signs.
-/
import GaloisForLFunctions.RHTower.PairStaircase

noncomputable section

namespace RHTower

open Complex Metric Finset

/-- The imaginary part of a counter-rotated complex number, in polar form. -/
theorem im_rotated (φ : ℝ) (z : ℂ) :
    (Complex.exp (-(φ : ℂ) * I) * z).im = ‖z‖ * Real.sin (z.arg - φ) := by
  conv_lhs => rw [← Complex.norm_mul_exp_arg_mul_I z]
  rw [show Complex.exp (-(φ : ℂ) * I)
        * ((‖z‖ : ℂ) * Complex.exp ((z.arg : ℂ) * I))
      = (‖z‖ : ℂ) * Complex.exp ((z.arg : ℂ) * I + -(φ : ℂ) * I) from by
    rw [Complex.exp_add]
    ring]
  rw [show (z.arg : ℂ) * I + -(φ : ℂ) * I = ((z.arg - φ : ℝ) : ℂ) * I from by
    push_cast
    ring]
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_ofReal_mul_I_im]
  ring

/-- **Endpoint rotation steering**: for any two nonzero prime-free values `zp, zm`
and any prescribed sign pair, there are prime sets beyond any bound whose two
basepoint tilts counter-rotate the values into the prescribed imaginary-sign pair.
The targets are the value arguments shifted by a quarter turn and lifted into the
nonnegative cone by one period; the tolerance `π/4` leaves the sine a `√2/2`
margin. -/
theorem exists_anchor_rotated_sign_pair {ρ : ℂ} {c : ℝ}
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1)
    (hc : 0 < c) (hcτ : c < ρ.im)
    (hnarrow : 9 * (2 * c) ≤ ρ.im + c)
    (hcap : (ρ.im + c) * (4 * Real.log 2) < Real.pi)
    {zp zm : ℂ} (hzp : zp ≠ 0) (hzm : zm ≠ 0)
    (ε₁ ε₂ : Bool) (Q : ℕ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p ∧ Q < p) ∧
      (if ε₁ then
        0 < (Complex.exp (-((anchorTilt P (ρ + (c : ℂ) * I) : ℝ) : ℂ) * I) * zp).im
      else
        (Complex.exp (-((anchorTilt P (ρ + (c : ℂ) * I) : ℝ) : ℂ) * I) * zp).im < 0) ∧
      (if ε₂ then
        0 < (Complex.exp (-((anchorTilt P (ρ - (c : ℂ) * I) : ℝ) : ℂ) * I) * zm).im
      else
        (Complex.exp (-((anchorTilt P (ρ - (c : ℂ) * I) : ℝ) : ℂ) * I) * zm).im < 0) := by
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hargp := Complex.arg_mem_Ioc zp
  have hargm := Complex.arg_mem_Ioc zm
  have hnp : 0 < ‖zp‖ := norm_pos_iff.mpr hzp
  have hnm : 0 < ‖zm‖ := norm_pos_iff.mpr hzm
  have hε4 : (0 : ℝ) < Real.pi / 4 := by linarith
  -- the four sign quadrants, each with its own quarter-turn targets
  cases ε₁ <;> cases ε₂
  · -- (negative, negative)
    obtain ⟨P, hP, hup, hum⟩ := anchorTilt_pair_reachable_nonneg hre0 hre1 hc hcτ
      hnarrow hcap (Tp := zp.arg + Real.pi / 2 + 2 * Real.pi)
      (Tm := zm.arg + Real.pi / 2 + 2 * Real.pi)
      (by linarith [hargp.1]) (by linarith [hargm.1]) hε4 Q
    obtain ⟨h1p, h2p⟩ := abs_le.mp hup
    obtain ⟨h1m, h2m⟩ := abs_le.mp hum
    refine ⟨P, hP, ?_, ?_⟩
    · show (Complex.exp (-((anchorTilt P (ρ + (c : ℂ) * I) : ℝ) : ℂ) * I) * zp).im < 0
      rw [im_rotated]
      apply mul_neg_of_pos_of_neg hnp
      rw [show zp.arg - anchorTilt P (ρ + (c : ℂ) * I)
          = -(Real.pi / 2 - (zp.arg + Real.pi / 2 + 2 * Real.pi
              - anchorTilt P (ρ + (c : ℂ) * I))) - 2 * Real.pi from by ring,
        Real.sin_sub_two_pi, Real.sin_neg, Real.sin_pi_div_two_sub, neg_lt_zero]
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith
      · linarith
    · show (Complex.exp (-((anchorTilt P (ρ - (c : ℂ) * I) : ℝ) : ℂ) * I) * zm).im < 0
      rw [im_rotated]
      apply mul_neg_of_pos_of_neg hnm
      rw [show zm.arg - anchorTilt P (ρ - (c : ℂ) * I)
          = -(Real.pi / 2 - (zm.arg + Real.pi / 2 + 2 * Real.pi
              - anchorTilt P (ρ - (c : ℂ) * I))) - 2 * Real.pi from by ring,
        Real.sin_sub_two_pi, Real.sin_neg, Real.sin_pi_div_two_sub, neg_lt_zero]
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith
      · linarith
  · -- (negative, positive)
    obtain ⟨P, hP, hup, hum⟩ := anchorTilt_pair_reachable_nonneg hre0 hre1 hc hcτ
      hnarrow hcap (Tp := zp.arg + Real.pi / 2 + 2 * Real.pi)
      (Tm := zm.arg - Real.pi / 2 + 2 * Real.pi)
      (by linarith [hargp.1]) (by linarith [hargm.1]) hε4 Q
    obtain ⟨h1p, h2p⟩ := abs_le.mp hup
    obtain ⟨h1m, h2m⟩ := abs_le.mp hum
    refine ⟨P, hP, ?_, ?_⟩
    · show (Complex.exp (-((anchorTilt P (ρ + (c : ℂ) * I) : ℝ) : ℂ) * I) * zp).im < 0
      rw [im_rotated]
      apply mul_neg_of_pos_of_neg hnp
      rw [show zp.arg - anchorTilt P (ρ + (c : ℂ) * I)
          = -(Real.pi / 2 - (zp.arg + Real.pi / 2 + 2 * Real.pi
              - anchorTilt P (ρ + (c : ℂ) * I))) - 2 * Real.pi from by ring,
        Real.sin_sub_two_pi, Real.sin_neg, Real.sin_pi_div_two_sub, neg_lt_zero]
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith
      · linarith
    · show 0 < (Complex.exp (-((anchorTilt P (ρ - (c : ℂ) * I) : ℝ) : ℂ) * I) * zm).im
      rw [im_rotated]
      apply mul_pos hnm
      rw [show zm.arg - anchorTilt P (ρ - (c : ℂ) * I)
          = Real.pi / 2 - -(zm.arg - Real.pi / 2 + 2 * Real.pi
              - anchorTilt P (ρ - (c : ℂ) * I)) - 2 * Real.pi from by ring,
        Real.sin_sub_two_pi, Real.sin_pi_div_two_sub, Real.cos_neg]
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith
      · linarith
  · -- (positive, negative)
    obtain ⟨P, hP, hup, hum⟩ := anchorTilt_pair_reachable_nonneg hre0 hre1 hc hcτ
      hnarrow hcap (Tp := zp.arg - Real.pi / 2 + 2 * Real.pi)
      (Tm := zm.arg + Real.pi / 2 + 2 * Real.pi)
      (by linarith [hargp.1]) (by linarith [hargm.1]) hε4 Q
    obtain ⟨h1p, h2p⟩ := abs_le.mp hup
    obtain ⟨h1m, h2m⟩ := abs_le.mp hum
    refine ⟨P, hP, ?_, ?_⟩
    · show 0 < (Complex.exp (-((anchorTilt P (ρ + (c : ℂ) * I) : ℝ) : ℂ) * I) * zp).im
      rw [im_rotated]
      apply mul_pos hnp
      rw [show zp.arg - anchorTilt P (ρ + (c : ℂ) * I)
          = Real.pi / 2 - -(zp.arg - Real.pi / 2 + 2 * Real.pi
              - anchorTilt P (ρ + (c : ℂ) * I)) - 2 * Real.pi from by ring,
        Real.sin_sub_two_pi, Real.sin_pi_div_two_sub, Real.cos_neg]
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith
      · linarith
    · show (Complex.exp (-((anchorTilt P (ρ - (c : ℂ) * I) : ℝ) : ℂ) * I) * zm).im < 0
      rw [im_rotated]
      apply mul_neg_of_pos_of_neg hnm
      rw [show zm.arg - anchorTilt P (ρ - (c : ℂ) * I)
          = -(Real.pi / 2 - (zm.arg + Real.pi / 2 + 2 * Real.pi
              - anchorTilt P (ρ - (c : ℂ) * I))) - 2 * Real.pi from by ring,
        Real.sin_sub_two_pi, Real.sin_neg, Real.sin_pi_div_two_sub, neg_lt_zero]
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith
      · linarith
  · -- (positive, positive)
    obtain ⟨P, hP, hup, hum⟩ := anchorTilt_pair_reachable_nonneg hre0 hre1 hc hcτ
      hnarrow hcap (Tp := zp.arg - Real.pi / 2 + 2 * Real.pi)
      (Tm := zm.arg - Real.pi / 2 + 2 * Real.pi)
      (by linarith [hargp.1]) (by linarith [hargm.1]) hε4 Q
    obtain ⟨h1p, h2p⟩ := abs_le.mp hup
    obtain ⟨h1m, h2m⟩ := abs_le.mp hum
    refine ⟨P, hP, ?_, ?_⟩
    · show 0 < (Complex.exp (-((anchorTilt P (ρ + (c : ℂ) * I) : ℝ) : ℂ) * I) * zp).im
      rw [im_rotated]
      apply mul_pos hnp
      rw [show zp.arg - anchorTilt P (ρ + (c : ℂ) * I)
          = Real.pi / 2 - -(zp.arg - Real.pi / 2 + 2 * Real.pi
              - anchorTilt P (ρ + (c : ℂ) * I)) - 2 * Real.pi from by ring,
        Real.sin_sub_two_pi, Real.sin_pi_div_two_sub, Real.cos_neg]
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith
      · linarith
    · show 0 < (Complex.exp (-((anchorTilt P (ρ - (c : ℂ) * I) : ℝ) : ℂ) * I) * zm).im
      rw [im_rotated]
      apply mul_pos hnm
      rw [show zm.arg - anchorTilt P (ρ - (c : ℂ) * I)
          = Real.pi / 2 - -(zm.arg - Real.pi / 2 + 2 * Real.pi
              - anchorTilt P (ρ - (c : ℂ) * I)) - 2 * Real.pi from by ring,
        Real.sin_sub_two_pi, Real.sin_pi_div_two_sub, Real.cos_neg]
      apply Real.cos_pos_of_mem_Ioo
      constructor
      · linarith
      · linarith

/-- **The endpoint orientations of the anchored pencil take every sign pair**: at the
two annulus basepoints, the incidence imaginary part of the anchored symmetric member
is steerable to any prescribed sign pair over prime sets beyond any bound, provided
the member does not vanish at the basepoints.  Mirror-of-mirror bookkeeping: the
orientation at `ρ ± ci` is the counter-rotation of the prime-free value
`−completedSEM N (ρ ± ci)` by the anchor tilt at `ρ ± ci` itself, scaled by
`‖A_P(ρ ± ci)‖⁻¹ > 0`. -/
theorem incidence_endpoint_sign_steerable {ρ : ℂ} {c : ℝ}
    (hre0 : 0 < ρ.re) (hre1 : ρ.re < 1)
    (hc : 0 < c) (hcτ : c < ρ.im)
    (hnarrow : 9 * (2 * c) ≤ ρ.im + c)
    (hcap : (ρ.im + c) * (4 * Real.log 2) < Real.pi)
    {N : ℕ} (hzp : completedSEM N (ρ + (c : ℂ) * I) ≠ 0)
    (hzm : completedSEM N (ρ - (c : ℂ) * I) ≠ 0)
    (ε₁ ε₂ : Bool) (Q : ℕ) :
    ∃ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p ∧ Q < p) ∧
      (if ε₁ then
        0 < (incidence (eulerHeadAnchor P) (completedSEM N) (ρ + (c : ℂ) * I)).im
      else
        (incidence (eulerHeadAnchor P) (completedSEM N) (ρ + (c : ℂ) * I)).im < 0) ∧
      (if ε₂ then
        0 < (incidence (eulerHeadAnchor P) (completedSEM N) (ρ - (c : ℂ) * I)).im
      else
        (incidence (eulerHeadAnchor P) (completedSEM N) (ρ - (c : ℂ) * I)).im < 0) := by
  have hrep : (ρ + (c : ℂ) * I).re = ρ.re := by simp
  have hrem : (ρ - (c : ℂ) * I).re = ρ.re := by simp
  have hrep0 : 0 < (ρ + (c : ℂ) * I).re := by rw [hrep]; exact hre0
  have hrep1 : (ρ + (c : ℂ) * I).re < 1 := by rw [hrep]; exact hre1
  have hrem0 : 0 < (ρ - (c : ℂ) * I).re := by rw [hrem]; exact hre0
  have hrem1 : (ρ - (c : ℂ) * I).re < 1 := by rw [hrem]; exact hre1
  obtain ⟨P, hP, hsp, hsm⟩ := exists_anchor_rotated_sign_pair hre0 hre1 hc hcτ
    hnarrow hcap (neg_ne_zero.mpr hzp) (neg_ne_zero.mpr hzm) ε₁ ε₂ Q
  have hP2 : ∀ p ∈ P, 2 ≤ p := fun p hp => ((hP p hp).1).two_le
  -- the cancellation identity at the mirror points, folded back to the basepoints
  have hform : ∀ w : ℂ, 0 < w.re → w.re < 1 →
      (incidence (eulerHeadAnchor P) (completedSEM N) w).im
        = ‖eulerHeadAnchor P w‖⁻¹
          * (Complex.exp (-((anchorTilt P w : ℝ) : ℂ) * I)
              * -(completedSEM N w)).im := by
    intro w h0 h1
    have h0' : 0 < (1 - (starRingEnd ℂ) w).re := by
      simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    have h1' : (1 - (starRingEnd ℂ) w).re < 1 := by
      simp only [Complex.sub_re, Complex.one_re, Complex.conj_re]
      linarith
    have hmm : 1 - (starRingEnd ℂ) (1 - (starRingEnd ℂ) w) = w := by
      rw [map_sub, map_one, Complex.conj_conj]
      ring
    have h := im_incidence_anchoredSEM_mirror_tilt_only hP2 (N := N)
      (s := 1 - (starRingEnd ℂ) w) h0' h1'
    rw [hmm] at h
    have hG : completedSEM N (1 - (starRingEnd ℂ) w)
        = (starRingEnd ℂ) (completedSEM N w) := completedSEM_lineReflection h0 h1
    rw [hG, show (starRingEnd ℂ) (-(starRingEnd ℂ) (completedSEM N w))
        = -(completedSEM N w) from by rw [map_neg, Complex.conj_conj]] at h
    exact h
  have hAp : (0 : ℝ) < ‖eulerHeadAnchor P (ρ + (c : ℂ) * I)‖⁻¹ :=
    inv_pos.mpr (norm_pos_iff.mpr (eulerHeadAnchor_ne_zero hP2 hrep0))
  have hAm : (0 : ℝ) < ‖eulerHeadAnchor P (ρ - (c : ℂ) * I)‖⁻¹ :=
    inv_pos.mpr (norm_pos_iff.mpr (eulerHeadAnchor_ne_zero hP2 hrem0))
  refine ⟨P, hP, ?_, ?_⟩
  · rw [hform _ hrep0 hrep1]
    cases ε₁ with
    | false =>
      show ‖eulerHeadAnchor P (ρ + (c : ℂ) * I)‖⁻¹
          * (Complex.exp (-((anchorTilt P (ρ + (c : ℂ) * I) : ℝ) : ℂ) * I)
            * -(completedSEM N (ρ + (c : ℂ) * I))).im < 0
      exact mul_neg_of_pos_of_neg hAp hsp
    | true =>
      show 0 < ‖eulerHeadAnchor P (ρ + (c : ℂ) * I)‖⁻¹
          * (Complex.exp (-((anchorTilt P (ρ + (c : ℂ) * I) : ℝ) : ℂ) * I)
            * -(completedSEM N (ρ + (c : ℂ) * I))).im
      exact mul_pos hAp hsp
  · rw [hform _ hrem0 hrem1]
    cases ε₂ with
    | false =>
      show ‖eulerHeadAnchor P (ρ - (c : ℂ) * I)‖⁻¹
          * (Complex.exp (-((anchorTilt P (ρ - (c : ℂ) * I) : ℝ) : ℂ) * I)
            * -(completedSEM N (ρ - (c : ℂ) * I))).im < 0
      exact mul_neg_of_pos_of_neg hAm hsm
    | true =>
      show 0 < ‖eulerHeadAnchor P (ρ - (c : ℂ) * I)‖⁻¹
          * (Complex.exp (-((anchorTilt P (ρ - (c : ℂ) * I) : ℝ) : ℂ) * I)
            * -(completedSEM N (ρ - (c : ℂ) * I))).im
      exact mul_pos hAm hsm

/-- **The endpoint no-go**: two prime sets whose anchored members have the SAME deck
class but DIFFERENT endpoint orientation sign pairs.  Anchoring never moves the deck
class — both equal the plain member's — while the endpoint sign pair is freely
steerable.  Hence no prime-set-independent function of the two endpoint
imaginary-part signs computes the deck class, and the parity dictionary must route
through the boundary-arc argument variation rather than the endpoint signs. -/
theorem endpoint_orientation_no_go {ρ : ℂ} {r₀ R : ℝ}
    (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    (hstripb : ∀ z ∈ ball ρ R, 0 < z.re ∧ z.re < 1)
    (hcτ : (r₀ + R) / 2 < ρ.im)
    (hnarrow : 9 * (2 * ((r₀ + R) / 2)) ≤ ρ.im + (r₀ + R) / 2)
    (hcap : (ρ.im + (r₀ + R) / 2) * (4 * Real.log 2) < Real.pi)
    {N : ℕ} {H₁ H₂ : ℂ → ℂ}
    (hH₁ : AnalyticOnNhd ℂ H₁ (chartRA ρ r₀ R))
    (hH₂ : AnalyticOnNhd ℂ H₂ (chartLA ρ r₀ R))
    (hpH₁ : ∀ z ∈ chartRA ρ r₀ R, H₁ z ^ 2 = completedSEM N z)
    (hpH₂ : ∀ z ∈ chartLA ρ r₀ R, H₂ z ^ 2 = completedSEM N z)
    (hzp : completedSEM N (ρ + (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0)
    (hzm : completedSEM N (ρ - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ≠ 0) :
    ∃ (P₁ P₂ : Finset ℕ) (G₁ G₂ G₁' G₂' : ℂ → ℂ),
      (∀ p ∈ P₁, Nat.Prime p) ∧ (∀ p ∈ P₂, Nat.Prime p) ∧
      (∀ z ∈ chartRA ρ r₀ R, G₁ z ^ 2 = anchoredSEM P₁ N z) ∧
      (∀ z ∈ chartLA ρ r₀ R, G₂ z ^ 2 = anchoredSEM P₁ N z) ∧
      (∀ z ∈ chartRA ρ r₀ R, G₁' z ^ 2 = anchoredSEM P₂ N z) ∧
      (∀ z ∈ chartLA ρ r₀ R, G₂' z ^ 2 = anchoredSEM P₂ N z) ∧
      deckClass G₁ G₂ (ρ + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
          (ρ - (((r₀ + R) / 2 : ℝ) : ℂ) * I)
        = deckClass G₁' G₂' (ρ + (((r₀ + R) / 2 : ℝ) : ℂ) * I)
            (ρ - (((r₀ + R) / 2 : ℝ) : ℂ) * I) ∧
      0 < (incidence (eulerHeadAnchor P₁) (completedSEM N)
            (ρ + (((r₀ + R) / 2 : ℝ) : ℂ) * I)).im ∧
      0 < (incidence (eulerHeadAnchor P₁) (completedSEM N)
            (ρ - (((r₀ + R) / 2 : ℝ) : ℂ) * I)).im ∧
      0 < (incidence (eulerHeadAnchor P₂) (completedSEM N)
            (ρ + (((r₀ + R) / 2 : ℝ) : ℂ) * I)).im ∧
      (incidence (eulerHeadAnchor P₂) (completedSEM N)
        (ρ - (((r₀ + R) / 2 : ℝ) : ℂ) * I)).im < 0 := by
  have hR : 0 < R := lt_of_le_of_lt h0 hrR
  have hc : 0 < (r₀ + R) / 2 := by linarith
  obtain ⟨hre0, hre1⟩ := hstripb ρ (mem_ball_self hR)
  obtain ⟨P₁, hP₁, hs₁p, hs₁m⟩ := incidence_endpoint_sign_steerable hre0 hre1 hc hcτ
    hnarrow hcap hzp hzm true true 0
  obtain ⟨P₂, hP₂, hs₂p, hs₂m⟩ := incidence_endpoint_sign_steerable hre0 hre1 hc hcτ
    hnarrow hcap hzp hzm true false 0
  have hP₁2 : ∀ p ∈ P₁, 2 ≤ p := fun p hp => ((hP₁ p hp).1).two_le
  have hP₂2 : ∀ p ∈ P₂, 2 ≤ p := fun p hp => ((hP₂ p hp).1).two_le
  obtain ⟨G₁, G₂, hG₁an, hG₂an, hpG₁, hpG₂, hdeck₁⟩ :=
    anchoredSEM_roots_of_sem_roots hP₁2 h0 hrR hstripb hH₁ hH₂ hpH₁ hpH₂
  obtain ⟨G₁', G₂', hG₁'an, hG₂'an, hpG₁', hpG₂', hdeck₂⟩ :=
    anchoredSEM_roots_of_sem_roots hP₂2 h0 hrR hstripb hH₁ hH₂ hpH₁ hpH₂
  exact ⟨P₁, P₂, G₁, G₂, G₁', G₂',
    fun p hp => (hP₁ p hp).1, fun p hp => (hP₂ p hp).1,
    hpG₁, hpG₂, hpG₁', hpG₂', hdeck₁.trans hdeck₂.symm,
    hs₁p, hs₁m, hs₂p, hs₂m⟩

end RHTower
