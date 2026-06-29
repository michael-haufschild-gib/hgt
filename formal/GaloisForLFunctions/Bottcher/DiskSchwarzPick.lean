/-
# Schwarz-Pick estimate for disk-valued lifts

This file supplies the disk-metric estimate needed for the cusp-height producer.  A holomorphic
map from a Euclidean disk to the closed unit disk is contracted by the Blaschke factor based at
the center value.
-/
import Mathlib.Analysis.Complex.Schwarz
import GaloisForLFunctions.CayleySchur
import GaloisForLFunctions.Bottcher.ModularLambdaLift

open Complex Metric Set

namespace Bottcher

noncomputable section

/-- If `‖a‖ < 1` and `‖w‖ ≤ 1`, the Blaschke denominator `1 - conj a * w` is nonzero. -/
theorem one_sub_conj_mul_ne_zero_of_norm_lt_one_norm_le_one {a w : ℂ}
    (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1) :
    1 - (starRingEnd ℂ) a * w ≠ 0 := by
  intro h
  have hmul : (starRingEnd ℂ) a * w = 1 := by
    linear_combination -h
  have hnorm : ‖a‖ * ‖w‖ = 1 := by
    have := congrArg norm hmul
    simpa [norm_mul, map_star] using this
  have hle : ‖a‖ * ‖w‖ ≤ ‖a‖ * 1 := by
    exact mul_le_mul_of_nonneg_left hw (norm_nonneg a)
  have hone : (1 : ℝ) ≤ ‖a‖ := by
    nlinarith
  linarith

/-- Schwarz-Pick in one disk chart.  For a holomorphic closed-disk-valued map `g`, the Blaschke
factor based at `g c` is bounded by the normalized source distance. -/
theorem blaschke_lift_norm_le_dist_div {g : ℂ → ℂ} {c z : ℂ} {R : ℝ}
    (hR : 0 < R)
    (hgdiff : DifferentiableOn ℂ g (ball c R))
    (hgbd : ∀ y ∈ ball c R, ‖g y‖ ≤ 1)
    (hgc : ‖g c‖ < 1)
    (hz : z ∈ ball c R) :
    ‖(g z - g c) / (1 - (starRingEnd ℂ) (g c) * g z)‖ ≤ dist z c / R := by
  let B : ℂ → ℂ := fun w => (w - g c) / (1 - (starRingEnd ℂ) (g c) * w)
  have hc_mem : c ∈ ball c R := mem_ball_self hR
  have hden : ∀ y ∈ ball c R, 1 - (starRingEnd ℂ) (g c) * g y ≠ 0 := by
    intro y hy
    exact one_sub_conj_mul_ne_zero_of_norm_lt_one_norm_le_one hgc (hgbd y hy)
  have hBdiff : DifferentiableOn ℂ (fun y => B (g y)) (ball c R) := by
    intro y hy
    have hB_at : DifferentiableAt ℂ B (g y) := by
      dsimp [B]
      exact (differentiableAt_id.sub_const _).div
        ((differentiableAt_const (c := (starRingEnd ℂ) (g c))).mul differentiableAt_id |>.const_sub _)
        (hden y hy)
    exact (hB_at.comp y ((hgdiff y hy).differentiableAt (isOpen_ball.mem_nhds hy))).differentiableWithinAt
  have hmaps : MapsTo (fun y => B (g y)) (ball c R) (closedBall (B (g c)) 1) := by
    intro y hy
    rw [mem_closedBall]
    have hB0 : B (g c) = 0 := by
      dsimp [B]
      simp
    rw [hB0, dist_zero_right]
    exact GaloisForLFunctions.blaschke_schur (g c) (g y) (le_of_lt hgc) (hgbd y hy) (hden y hy)
  have hschwarz := dist_le_div_mul_dist_of_mapsTo_ball hBdiff hmaps hz
  have hB0 : B (g c) = 0 := by
    dsimp [B]
    simp
  simpa [B, hB0, one_div, mul_comm, mul_left_comm, mul_assoc] using hschwarz

/-- The boundary-one Poisson kernel on the unit disk.  Under `cayleyInv`, this is exactly the
upper-half-plane height. -/
def diskPoissonOne (z : ℂ) : ℝ := (1 - ‖z‖ ^ 2) / ‖1 - z‖ ^ 2

/-- The inverse Cayley transform has height equal to the boundary-one Poisson kernel. -/
theorem cayleyInv_im_eq_diskPoissonOne {θ : ℂ} (hθ : θ ≠ 1) :
    (cayleyInv θ).im = diskPoissonOne θ := by
  have hden : 0 < Complex.normSq (1 - θ) :=
    Complex.normSq_pos.mpr (sub_ne_zero.mpr (Ne.symm hθ))
  unfold cayleyInv diskPoissonOne
  rw [Complex.mul_im, Complex.I_re, Complex.I_im, one_mul, zero_mul, zero_add, Complex.div_re,
      ← add_div]
  simp only [Complex.add_re, Complex.one_re, Complex.sub_re, Complex.add_im, Complex.one_im,
    Complex.sub_im]
  rw [Complex.normSq_eq_norm_sq]
  have hnormsq : ‖θ‖ ^ 2 = θ.re ^ 2 + θ.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    ring
  rw [hnormsq]
  ring

/-- Numerator identity for the disk automorphism inverse. -/
theorem normsq_one_add_conj_mul_sub_normsq_add (a η : ℂ) :
    Complex.normSq (1 + (starRingEnd ℂ) a * η) - Complex.normSq (a + η)
      = (1 - Complex.normSq a) * (1 - Complex.normSq η) := by
  rw [Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.one_re, Complex.mul_re, Complex.conj_re, Complex.conj_im,
    Complex.add_im, Complex.one_im, Complex.mul_im]
  ring

/-- Division form of `1 - ‖x/d‖²`. -/
theorem one_sub_norm_sq_div {x d : ℂ} (hd : d ≠ 0) :
    1 - ‖x / d‖ ^ 2 = (‖d‖ ^ 2 - ‖x‖ ^ 2) / ‖d‖ ^ 2 := by
  have hd2 : ‖d‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hd)
  rw [norm_div]
  calc
    1 - (‖x‖ / ‖d‖) ^ 2 = 1 - ‖x‖ ^ 2 / ‖d‖ ^ 2 := by ring
    _ = (‖d‖ ^ 2 - ‖x‖ ^ 2) / ‖d‖ ^ 2 := by field_simp [hd2]

/-- Exact numerator transform for `w = (a + η)/(1 + āη)`. -/
theorem one_sub_norm_sq_mobius {a η : ℂ}
    (hden : 1 + (starRingEnd ℂ) a * η ≠ 0) :
    1 - ‖(a + η) / (1 + (starRingEnd ℂ) a * η)‖ ^ 2 =
      ((1 - ‖a‖ ^ 2) * (1 - ‖η‖ ^ 2)) / ‖1 + (starRingEnd ℂ) a * η‖ ^ 2 := by
  let den : ℂ := 1 + (starRingEnd ℂ) a * η
  have hdiv := one_sub_norm_sq_div (x := a + η) (d := den) hden
  have hkey := normsq_one_add_conj_mul_sub_normsq_add a η
  rw [Complex.normSq_eq_norm_sq (1 + (starRingEnd ℂ) a * η),
      Complex.normSq_eq_norm_sq (a + η), Complex.normSq_eq_norm_sq a,
      Complex.normSq_eq_norm_sq η] at hkey
  simpa [den, hkey] using hdiv

/-- The conjugate-side coefficient in the disk automorphism has the same norm as `1 - a`. -/
theorem norm_conj_sub_one_eq_norm_one_sub (a : ℂ) :
    ‖(starRingEnd ℂ) a - 1‖ = ‖1 - a‖ := by
  have h1 : (starRingEnd ℂ) a - 1 = (starRingEnd ℂ) (a - 1) := by simp
  rw [h1, RCLike.norm_conj, ← norm_neg (a - 1)]
  congr 1
  ring

/-- Denominator bound for the boundary-one Poisson kernel under the disk automorphism inverse. -/
theorem one_sub_mobius_norm_le {a η : ℂ}
    (hden : 1 + (starRingEnd ℂ) a * η ≠ 0) :
    ‖1 - (a + η) / (1 + (starRingEnd ℂ) a * η)‖ ≤
      ‖1 - a‖ * (1 + ‖η‖) / ‖1 + (starRingEnd ℂ) a * η‖ := by
  let den : ℂ := 1 + (starRingEnd ℂ) a * η
  have hden_norm_pos : 0 < ‖den‖ := norm_pos_iff.mpr hden
  have hrewrite : 1 - (a + η) / den =
      ((1 - a) + ((starRingEnd ℂ) a - 1) * η) / den := by
    field_simp [hden, den]
    change (1 + (starRingEnd ℂ) a * η) - (a + η) =
      1 - a + η * ((starRingEnd ℂ) a - 1)
    ring_nf
  rw [hrewrite, norm_div]
  have htri : ‖(1 - a) + ((starRingEnd ℂ) a - 1) * η‖ ≤
      ‖1 - a‖ + ‖((starRingEnd ℂ) a - 1) * η‖ := norm_add_le _ _
  have hmul : ‖((starRingEnd ℂ) a - 1) * η‖ = ‖1 - a‖ * ‖η‖ := by
    rw [norm_mul, norm_conj_sub_one_eq_norm_one_sub]
  have hnum :
      ‖(1 - a) + ((starRingEnd ℂ) a - 1) * η‖ ≤ ‖1 - a‖ * (1 + ‖η‖) := by
    calc
      ‖(1 - a) + ((starRingEnd ℂ) a - 1) * η‖
          ≤ ‖1 - a‖ + ‖((starRingEnd ℂ) a - 1) * η‖ := htri
      _ = ‖1 - a‖ + ‖1 - a‖ * ‖η‖ := by rw [hmul]
      _ = ‖1 - a‖ * (1 + ‖η‖) := by ring
  exact div_le_div_of_nonneg_right hnum (le_of_lt hden_norm_pos)

/-- The inverse disk automorphism denominator is nonzero for two strict disk points. -/
theorem one_add_conj_mul_ne_zero_of_norm_lt_one {a η : ℂ}
    (ha : ‖a‖ < 1) (hη : ‖η‖ < 1) :
    1 + (starRingEnd ℂ) a * η ≠ 0 := by
  intro h
  have hmul : (starRingEnd ℂ) a * η = -1 := by
    linear_combination h
  have hnorm : ‖a‖ * ‖η‖ = 1 := by
    have := congrArg norm hmul
    simpa [norm_mul, RCLike.norm_conj] using this
  have hprodlt : ‖a‖ * ‖η‖ < 1 := by
    nlinarith [ha, hη, norm_nonneg a, norm_nonneg η]
  linarith

/-- The boundary-one Poisson kernel is positive on the open unit disk. -/
theorem diskPoissonOne_pos_of_norm_lt_one {z : ℂ} (hz : ‖z‖ < 1) :
    0 < diskPoissonOne z := by
  have hne : 1 - z ≠ 0 := by
    intro h
    have hz1 : z = 1 := (sub_eq_zero.mp h).symm
    rw [hz1, norm_one] at hz
    linarith
  have hnum : 0 < 1 - ‖z‖ ^ 2 := by
    nlinarith [hz, norm_nonneg z]
  have hden : 0 < ‖1 - z‖ ^ 2 := pow_pos (norm_pos_iff.mpr hne) 2
  unfold diskPoissonOne
  exact div_pos hnum hden

/-- Harnack lower bound for the boundary-one Poisson kernel, parametrized by the disk
automorphism inverse. -/
theorem diskPoissonOne_mobius_lower_norm {a η : ℂ}
    (ha : ‖a‖ < 1) (hη : ‖η‖ < 1) :
    ((1 - ‖η‖) / (1 + ‖η‖)) * diskPoissonOne a ≤
      diskPoissonOne ((a + η) / (1 + (starRingEnd ℂ) a * η)) := by
  let den : ℂ := 1 + (starRingEnd ℂ) a * η
  let w : ℂ := (a + η) / den
  have hden : den ≠ 0 := one_add_conj_mul_ne_zero_of_norm_lt_one ha hη
  have hden_pos : 0 < ‖den‖ := norm_pos_iff.mpr hden
  have hden_sq_pos : 0 < ‖den‖ ^ 2 := pow_pos hden_pos 2
  have hden_sq_ne : ‖den‖ ^ 2 ≠ 0 := ne_of_gt hden_sq_pos
  have hη_factor_pos : 0 < 1 + ‖η‖ := by positivity
  have hη_factor_ne : 1 + ‖η‖ ≠ 0 := ne_of_gt hη_factor_pos
  have hB_pos : 0 < ‖1 - a‖ := by
    apply norm_pos_iff.mpr
    intro h
    have ha1 : a = 1 := (sub_eq_zero.mp h).symm
    rw [ha1, norm_one] at ha
    linarith
  have hB_sq_pos : 0 < ‖1 - a‖ ^ 2 := pow_pos hB_pos 2
  have hB_sq_ne : ‖1 - a‖ ^ 2 ≠ 0 := ne_of_gt hB_sq_pos
  have hnum_eq : 1 - ‖w‖ ^ 2 =
      ((1 - ‖a‖ ^ 2) * (1 - ‖η‖ ^ 2)) / ‖den‖ ^ 2 := by
    simpa [w, den] using one_sub_norm_sq_mobius (a := a) (η := η)
      (by simpa [den] using hden)
  have hnum_pos : 0 < 1 - ‖w‖ ^ 2 := by
    rw [hnum_eq]
    apply div_pos
    · apply mul_pos <;> nlinarith [ha, hη, norm_nonneg a, norm_nonneg η]
    · exact hden_sq_pos
  have hw_norm_lt : ‖w‖ < 1 := by
    nlinarith [hnum_pos, norm_nonneg w]
  have hdenom_pos : 0 < ‖1 - w‖ ^ 2 := by
    have hne : 1 - w ≠ 0 := by
      intro h
      have hw1 : w = 1 := (sub_eq_zero.mp h).symm
      rw [hw1, norm_one] at hw_norm_lt
      linarith
    exact pow_pos (norm_pos_iff.mpr hne) 2
  have hdenom_le : ‖1 - w‖ ^ 2 ≤
      (‖1 - a‖ * (1 + ‖η‖) / ‖den‖) ^ 2 := by
    have hle : ‖1 - w‖ ≤ ‖1 - a‖ * (1 + ‖η‖) / ‖den‖ := by
      simpa [w, den] using one_sub_mobius_norm_le (a := a) (η := η)
        (by simpa [den] using hden)
    have hbound_nonneg : 0 ≤ ‖1 - a‖ * (1 + ‖η‖) / ‖den‖ := by positivity
    nlinarith [hle, norm_nonneg (1 - w), hbound_nonneg]
  have hleft_le :
      (1 - ‖w‖ ^ 2) / ((‖1 - a‖ * (1 + ‖η‖) / ‖den‖) ^ 2)
        ≤ diskPoissonOne w := by
    unfold diskPoissonOne
    exact div_le_div_of_nonneg_left (le_of_lt hnum_pos) hdenom_pos hdenom_le
  have hfactor_eq :
      (1 - ‖w‖ ^ 2) / ((‖1 - a‖ * (1 + ‖η‖) / ‖den‖) ^ 2)
        = ((1 - ‖η‖) / (1 + ‖η‖)) * diskPoissonOne a := by
    rw [hnum_eq]
    unfold diskPoissonOne
    field_simp [hden_sq_ne, hB_sq_ne, hη_factor_ne]
    ring
  rw [← hfactor_eq]
  exact hleft_le

/-- Harnack lower bound with any larger radius parameter `q`. -/
theorem diskPoissonOne_mobius_lower_of_norm_le {a η : ℂ} {q : ℝ}
    (ha : ‖a‖ < 1) (hq0 : 0 ≤ q) (hq1 : q < 1) (hηq : ‖η‖ ≤ q) :
    ((1 - q) / (1 + q)) * diskPoissonOne a ≤
      diskPoissonOne ((a + η) / (1 + (starRingEnd ℂ) a * η)) := by
  have hη1 : ‖η‖ < 1 := lt_of_le_of_lt hηq hq1
  have hfac : (1 - q) / (1 + q) ≤ (1 - ‖η‖) / (1 + ‖η‖) := by
    have hdenq : 0 < 1 + q := by nlinarith
    have hdene : 0 < 1 + ‖η‖ := by positivity
    rw [div_le_div_iff₀ hdenq hdene]
    nlinarith [hηq]
  have hPnonneg : 0 ≤ diskPoissonOne a := le_of_lt (diskPoissonOne_pos_of_norm_lt_one ha)
  have hmul := mul_le_mul_of_nonneg_right hfac hPnonneg
  exact le_trans hmul (diskPoissonOne_mobius_lower_norm ha hη1)

/-- The Blaschke parameter inverts to the original disk point. -/
theorem mobius_of_blaschke {a w : ℂ}
    (ha : ‖a‖ < 1) (hden : 1 - (starRingEnd ℂ) a * w ≠ 0) :
    (a + (w - a) / (1 - (starRingEnd ℂ) a * w)) /
        (1 + (starRingEnd ℂ) a * ((w - a) / (1 - (starRingEnd ℂ) a * w))) = w := by
  have hden_comm : 1 - w * (starRingEnd ℂ) a ≠ 0 := by simpa [mul_comm] using hden
  have hnum_ne : 1 - (starRingEnd ℂ) a * a ≠ 0 := by
    intro h
    have hmul : (starRingEnd ℂ) a * a = 1 := by
      linear_combination -h
    have hnorm : ‖a‖ * ‖a‖ = 1 := by
      have := congrArg norm hmul
      simpa [norm_mul, RCLike.norm_conj] using this
    nlinarith [ha, norm_nonneg a]
  have hden2eq : 1 + (starRingEnd ℂ) a * ((w - a) / (1 - (starRingEnd ℂ) a * w)) =
      (1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * w) := by
    field_simp [hden, hden_comm]
    ring
  have hnumeq : a + (w - a) / (1 - (starRingEnd ℂ) a * w) =
      w * (1 - (starRingEnd ℂ) a * a) / (1 - (starRingEnd ℂ) a * w) := by
    field_simp [hden, hden_comm]
    ring
  rw [hden2eq, hnumeq]
  field_simp [hden, hden_comm, hnum_ne]

/-- Boundary-one Poisson Harnack estimate from a Blaschke-ratio bound. -/
theorem diskPoissonOne_lower_of_blaschke_norm_le {a w : ℂ} {q : ℝ}
    (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hδq : ‖(w - a) / (1 - (starRingEnd ℂ) a * w)‖ ≤ q) :
    ((1 - q) / (1 + q)) * diskPoissonOne a ≤ diskPoissonOne w := by
  let η : ℂ := (w - a) / (1 - (starRingEnd ℂ) a * w)
  have hden : 1 - (starRingEnd ℂ) a * w ≠ 0 :=
    one_sub_conj_mul_ne_zero_of_norm_lt_one_norm_le_one ha hw
  have hlower := diskPoissonOne_mobius_lower_of_norm_le (a := a) (η := η) (q := q)
    ha hq0 hq1 (by simpa [η] using hδq)
  have hmob : (a + η) / (1 + (starRingEnd ℂ) a * η) = w := by
    simpa [η] using mobius_of_blaschke (a := a) (w := w) ha hden
  rwa [hmob] at hlower

/-- Cayley-height Harnack estimate from a Blaschke-ratio bound. -/
theorem cayleyInv_im_lower_of_blaschke_norm_le {a w : ℂ} {q : ℝ}
    (ha : ‖a‖ < 1) (hwlt : ‖w‖ < 1) (hq0 : 0 ≤ q) (hq1 : q < 1)
    (hδq : ‖(w - a) / (1 - (starRingEnd ℂ) a * w)‖ ≤ q) :
    ((1 - q) / (1 + q)) * (cayleyInv a).im ≤ (cayleyInv w).im := by
  have hPa := diskPoissonOne_lower_of_blaschke_norm_le (a := a) (w := w) (q := q)
    ha (le_of_lt hwlt) hq0 hq1 hδq
  have hane : a ≠ 1 := by
    intro h
    rw [h, norm_one] at ha
    linarith
  have hwne : w ≠ 1 := by
    intro h
    rw [h, norm_one] at hwlt
    linarith
  rw [cayleyInv_im_eq_diskPoissonOne hane, cayleyInv_im_eq_diskPoissonOne hwne]
  exact hPa

/-- Pointwise Cayley-height Harnack estimate for a holomorphic disk-valued lift. -/
theorem cayleyInv_im_lower_of_lift {g : ℂ → ℂ} {c z : ℂ} {R : ℝ}
    (hR : 0 < R)
    (hgdiff : DifferentiableOn ℂ g (ball c R))
    (hglt : ∀ y ∈ ball c R, ‖g y‖ < 1)
    (hz : z ∈ ball c R)
    (hq : dist z c / R < 1) :
    ((1 - dist z c / R) / (1 + dist z c / R)) * (cayleyInv (g c)).im ≤
      (cayleyInv (g z)).im := by
  have hc_mem : c ∈ ball c R := mem_ball_self hR
  have hq0 : 0 ≤ dist z c / R := div_nonneg dist_nonneg hR.le
  have hδq := blaschke_lift_norm_le_dist_div hR hgdiff
    (fun y hy => le_of_lt (hglt y hy)) (hglt c hc_mem) hz
  exact cayleyInv_im_lower_of_blaschke_norm_le (a := g c) (w := g z)
    (q := dist z c / R) (hglt c hc_mem) (hglt z hz) hq0 hq hδq

/-- Uniform closed-ball Cayley-height Harnack estimate for a holomorphic disk-valued lift. -/
theorem cayleyInv_im_harnack_closedBall {g : ℂ → ℂ} {c : ℂ} {ρ R : ℝ}
    (hR : 0 < R) (hρ0 : 0 ≤ ρ) (hρR : ρ < R)
    (hgdiff : DifferentiableOn ℂ g (ball c R))
    (hglt : ∀ y ∈ ball c R, ‖g y‖ < 1) :
    ∀ z, z ∈ closedBall c ρ →
      ((1 - ρ / R) / (1 + ρ / R)) * (cayleyInv (g c)).im ≤
        (cayleyInv (g z)).im := by
  intro z hz
  have hzle : dist z c ≤ ρ := by
    simpa [closedBall, dist_comm] using hz
  have hzball : z ∈ ball c R := by
    rw [mem_ball]
    exact lt_of_le_of_lt hzle hρR
  have hqz : dist z c / R < 1 := by
    rw [div_lt_one hR]
    exact lt_of_le_of_lt hzle hρR
  have hpoint := cayleyInv_im_lower_of_lift (g := g) (c := c) (z := z) (R := R)
    hR hgdiff hglt hzball hqz
  have hρq0 : 0 ≤ ρ / R := div_nonneg hρ0 hR.le
  have hqle : dist z c / R ≤ ρ / R := div_le_div_of_nonneg_right hzle hR.le
  have hfac :
      (1 - ρ / R) / (1 + ρ / R) ≤
        (1 - dist z c / R) / (1 + dist z c / R) := by
    have hdenρ : 0 < 1 + ρ / R := by nlinarith
    have hdenz : 0 < 1 + dist z c / R := by positivity
    rw [div_le_div_iff₀ hdenρ hdenz]
    nlinarith [hqle]
  have hbase_nonneg : 0 ≤ (cayleyInv (g c)).im := by
    have hc_mem : c ∈ ball c R := mem_ball_self hR
    exact le_of_lt (by
      rw [cayleyInv_im_eq_diskPoissonOne]
      · exact diskPoissonOne_pos_of_norm_lt_one (hglt c hc_mem)
      · intro h
        have hc_lt := hglt c hc_mem
        rw [h, norm_one] at hc_lt
        linarith)
  exact le_trans (mul_le_mul_of_nonneg_right hfac hbase_nonneg) hpoint

/-- Positive Harnack factor for a smaller closed ball inside a disk. -/
theorem harnackFactor_pos {ρ R : ℝ} (hR : 0 < R) (hρ0 : 0 ≤ ρ) (hρR : ρ < R) :
    0 < (1 - ρ / R) / (1 + ρ / R) := by
  have hq0 : 0 ≤ ρ / R := div_nonneg hρ0 hR.le
  have hq1 : ρ / R < 1 := by
    rw [div_lt_one hR]
    exact hρR
  exact div_pos (by nlinarith) (by nlinarith)

end

end Bottcher
