import GaloisForLFunctions.HTGeometry.CayleySchur
import Mathlib.Analysis.Complex.Schwarz

/-!
# The sharp Schwarz--Pick displacement estimate

For a holomorphic map of the open unit disk into the closed unit disk, the Blaschke factor based at
the centre value is contracted by the Schwarz lemma.  Inverting the Blaschke factor turns that into
the sharp displacement bound

`‖f z - f 0‖ ≤ ‖z‖ (1 - ‖f 0‖²) / (1 - ‖f 0‖ ‖z‖)`,

whose factor `1 - ‖f 0‖` is what makes narrow-sector evaluation functionals attain their norm at
the constant function.
-/

open Complex Metric Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem one_sub_conj_mul_ne_zero {a w : ℂ} (ha : ‖a‖ < 1) (hw : ‖w‖ ≤ 1) :
    1 - (starRingEnd ℂ) a * w ≠ 0 := by
  intro h
  have hmul : (starRingEnd ℂ) a * w = 1 := by linear_combination -h
  have hnorm : ‖a‖ * ‖w‖ = 1 := by
    have hc := congrArg norm hmul
    simpa [norm_mul, map_star] using hc
  nlinarith [norm_nonneg a, norm_nonneg w]

/-- Schwarz--Pick in the unit chart: the Blaschke factor based at the centre value is bounded by
the source modulus. -/
theorem blaschke_norm_le_norm {f : ℂ → ℂ} {z : ℂ}
    (hdiff : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hbd : ∀ w ∈ ball (0 : ℂ) 1, ‖f w‖ ≤ 1)
    (h0 : ‖f 0‖ < 1) (hz : ‖z‖ < 1) :
    ‖(f z - f 0) / (1 - (starRingEnd ℂ) (f 0) * f z)‖ ≤ ‖z‖ := by
  classical
  set B : ℂ → ℂ := fun w => (w - f 0) / (1 - (starRingEnd ℂ) (f 0) * w) with hB
  have hzmem : z ∈ ball (0 : ℂ) 1 := by simpa [mem_ball, dist_zero_right] using hz
  have hcmem : (0 : ℂ) ∈ ball (0 : ℂ) 1 := by simp
  have hden : ∀ y ∈ ball (0 : ℂ) 1, 1 - (starRingEnd ℂ) (f 0) * f y ≠ 0 :=
    fun y hy => one_sub_conj_mul_ne_zero h0 (hbd y hy)
  have hBdiff : DifferentiableOn ℂ (fun y => B (f y)) (ball (0 : ℂ) 1) := by
    intro y hy
    have hBat : DifferentiableAt ℂ B (f y) := by
      rw [hB]
      exact (differentiableAt_id.sub_const _).div
        ((differentiableAt_const (c := (starRingEnd ℂ) (f 0))).mul
          differentiableAt_id |>.const_sub _) (hden y hy)
    exact (hBat.comp y ((hdiff y hy).differentiableAt
      (isOpen_ball.mem_nhds hy))).differentiableWithinAt
  have hB0 : B (f 0) = 0 := by rw [hB]; simp
  have hmaps : MapsTo (fun y => B (f y)) (ball (0 : ℂ) 1) (closedBall (B (f 0)) 1) := by
    intro y hy
    rw [mem_closedBall, hB0, dist_zero_right]
    exact blaschke_schur (f 0) (f y) h0.le (hbd y hy) (hden y hy)
  have hschwarz := dist_le_div_mul_dist_of_mapsTo_ball hBdiff hmaps hzmem
  rw [hB0, dist_zero_right, dist_zero_right] at hschwarz
  simpa [hB] using hschwarz

/-- **The sharp Schwarz--Pick displacement estimate.** -/
theorem norm_sub_le_schwarzPick {f : ℂ → ℂ} {z : ℂ}
    (hdiff : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hbd : ∀ w ∈ ball (0 : ℂ) 1, ‖f w‖ ≤ 1)
    (h0 : ‖f 0‖ < 1) (hz : ‖z‖ < 1) :
    ‖f z - f 0‖ ≤ ‖z‖ * (1 - ‖f 0‖ ^ 2) / (1 - ‖f 0‖ * ‖z‖) := by
  classical
  set c : ℂ := f 0 with hc
  set t : ℝ := ‖c‖ with ht
  have hzmem : z ∈ ball (0 : ℂ) 1 := by simpa [mem_ball, dist_zero_right] using hz
  have hden : 1 - (starRingEnd ℂ) c * f z ≠ 0 := one_sub_conj_mul_ne_zero h0 (hbd z hzmem)
  set b : ℂ := (f z - c) / (1 - (starRingEnd ℂ) c * f z) with hbdef
  have hb : ‖b‖ ≤ ‖z‖ := blaschke_norm_le_norm hdiff hbd h0 hz
  have hkey : b * (1 - (starRingEnd ℂ) c * f z) = f z - c := by
    rw [hbdef]
    exact div_mul_cancel₀ _ hden
  have hnormsq : (starRingEnd ℂ) c * c = ((t ^ 2 : ℝ) : ℂ) := by
    rw [← Complex.normSq_eq_conj_mul_self, ht, Complex.sq_norm]
  have hprod : (f z - c) * (1 + (starRingEnd ℂ) c * b) = b * (1 - ((t ^ 2 : ℝ) : ℂ)) := by
    have hexp : (f z - c) * (1 + (starRingEnd ℂ) c * b) =
        b * (1 - (starRingEnd ℂ) c * f z) * (1 + (starRingEnd ℂ) c * b) := by
      rw [hkey]
    rw [hexp, ← hnormsq]
    have hcancel : (1 - (starRingEnd ℂ) c * f z) * (1 + (starRingEnd ℂ) c * b) =
        (1 - (starRingEnd ℂ) c * f z) +
          (starRingEnd ℂ) c * (b * (1 - (starRingEnd ℂ) c * f z)) := by ring
    rw [mul_assoc, hcancel, hkey]
    ring
  have htnn : 0 ≤ t := by rw [ht]; exact norm_nonneg _
  have hcb : ‖(starRingEnd ℂ) c * b‖ ≤ t * ‖z‖ := by
    rw [norm_mul, Complex.norm_conj, ← ht]
    exact mul_le_mul_of_nonneg_left hb htnn
  have htz : t * ‖z‖ < 1 := by
    nlinarith [norm_nonneg z]
  have hlow : 1 - t * ‖z‖ ≤ ‖1 + (starRingEnd ℂ) c * b‖ := by
    have h1 : (1 : ℝ) ≤ ‖1 + (starRingEnd ℂ) c * b‖ + ‖(starRingEnd ℂ) c * b‖ := by
      have hsplit : ((1 : ℂ)) = (1 + (starRingEnd ℂ) c * b) - (starRingEnd ℂ) c * b := by ring
      calc (1 : ℝ) = ‖(1 : ℂ)‖ := by simp
        _ = ‖(1 + (starRingEnd ℂ) c * b) - (starRingEnd ℂ) c * b‖ := by rw [← hsplit]
        _ ≤ ‖1 + (starRingEnd ℂ) c * b‖ + ‖(starRingEnd ℂ) c * b‖ := norm_sub_le _ _
    linarith
  have hnorms : ‖f z - c‖ * ‖1 + (starRingEnd ℂ) c * b‖ = ‖b‖ * (1 - t ^ 2) := by
    have h := congrArg norm hprod
    rw [norm_mul, norm_mul] at h
    rw [h]
    congr 1
    have hcast : (1 : ℂ) - ((t ^ 2 : ℝ) : ℂ) = (((1 - t ^ 2 : ℝ)) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by nlinarith : (0:ℝ) ≤ 1 - t ^ 2)]
  have hpos : (0 : ℝ) < 1 - t * ‖z‖ := by linarith
  have hsq : (0 : ℝ) ≤ 1 - t ^ 2 := by nlinarith
  rw [le_div_iff₀ hpos]
  calc ‖f z - c‖ * (1 - t * ‖z‖) ≤ ‖f z - c‖ * ‖1 + (starRingEnd ℂ) c * b‖ :=
        mul_le_mul_of_nonneg_left hlow (norm_nonneg _)
    _ = ‖b‖ * (1 - t ^ 2) := hnorms
    _ ≤ ‖z‖ * (1 - t ^ 2) := mul_le_mul_of_nonneg_right hb hsq

/-! ## The narrow-sector Schur lemma -/

/-- **Narrow-sector Schur lemma.**  A summable family confined to a disk of radius `R < 1`, whose
total is a positive real `M` dominating twice its square mass through `2A ≤ (1-R)M`, has weighted
evaluation functional of norm at most `M` on the Schur class. -/
theorem narrowSectorSchur_norm_le
    {ι : Type*} {u : ι → ℂ} {R M A : ℝ}
    (hsum : Summable (fun j => ‖u j‖))
    (hR0 : 0 ≤ R) (hR1 : R < 1) (hbd : ∀ j, ‖u j‖ ≤ R)
    (hM : ∑' j, u j = (M : ℂ)) (hMpos : 0 < M)
    (hA : ∑' j, ‖u j‖ ^ 2 = A)
    (hbal : 2 * A ≤ (1 - R) * M)
    {f : ℂ → ℂ}
    (hdiff : DifferentiableOn ℂ f (ball (0 : ℂ) 1))
    (hf : ∀ w ∈ ball (0 : ℂ) 1, ‖f w‖ ≤ 1) :
    ‖∑' j, u j * f (u j)‖ ≤ M := by
  classical
  have hmem : ∀ j, u j ∈ ball (0 : ℂ) 1 := by
    intro j
    have := (hbd j).trans_lt hR1
    simpa [mem_ball, dist_zero_right] using this
  have hsq : Summable (fun j => ‖u j‖ ^ 2) := by
    refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) (hsum.mul_left R)
    have h1 : ‖u j‖ ^ 2 = ‖u j‖ * ‖u j‖ := by ring
    rw [h1]
    exact mul_le_mul_of_nonneg_right (hbd j) (norm_nonneg _)
  set c : ℂ := f 0 with hc
  set t : ℝ := ‖c‖ with ht
  have ht1 : t ≤ 1 := by
    rw [ht, hc]
    exact hf 0 (by simp)
  have htnn : 0 ≤ t := by rw [ht]; exact norm_nonneg _
  have hfsum : Summable (fun j => u j * f (u j)) := by
    refine Summable.of_norm_bounded hsum (fun j => ?_)
    rw [norm_mul]
    calc ‖u j‖ * ‖f (u j)‖ ≤ ‖u j‖ * 1 :=
          mul_le_mul_of_nonneg_left (hf _ (hmem j)) (norm_nonneg _)
      _ = ‖u j‖ := mul_one _
  rcases eq_or_lt_of_le ht1 with htop | htlt
  · -- the boundary case: the map is constant by the maximum modulus principle
    have hmax : IsMaxOn (norm ∘ f) (ball (0 : ℂ) 1) 0 := by
      intro w hw
      simp only [Function.comp_apply, Set.mem_setOf_eq]
      have h1 := hf w hw
      have h2 : (1 : ℝ) = ‖f 0‖ := by rw [← hc, ← ht, ← htop]
      rw [← h2]
      exact h1
    have hconst := Complex.eqOn_of_isPreconnected_of_isMaxOn_norm
      ((convex_ball (0 : ℂ) 1).isPreconnected) isOpen_ball hdiff (by simp) hmax
    have hval : ∀ j, f (u j) = c := fun j => hconst (hmem j)
    have hrw : (fun j => u j * f (u j)) = fun j => c * u j := by
      funext j
      rw [hval j]
      ring
    rw [hrw, tsum_mul_left, hM, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hMpos, ← ht, htop, one_mul]
  · -- the interior case: the sharp Schwarz--Pick estimate
    have hden : (0 : ℝ) < 1 - t * R := by nlinarith
    have hdisp : ∀ j, ‖u j‖ * ‖f (u j) - c‖ ≤ ((1 - t ^ 2) / (1 - t * R)) * ‖u j‖ ^ 2 := by
      intro j
      have hzj : ‖u j‖ < 1 := (hbd j).trans_lt hR1
      have hsp := norm_sub_le_schwarzPick hdiff hf htlt hzj
      have hdenj : (0 : ℝ) < 1 - t * ‖u j‖ := by nlinarith [norm_nonneg (u j)]
      have hmono : ‖u j‖ * (1 - t ^ 2) / (1 - t * ‖u j‖) ≤
          ‖u j‖ * (1 - t ^ 2) / (1 - t * R) := by
        have hmul : t * ‖u j‖ ≤ t * R := mul_le_mul_of_nonneg_left (hbd j) htnn
        have hsqle : t ^ 2 ≤ 1 := by nlinarith
        apply div_le_div_of_nonneg_left
          (mul_nonneg (norm_nonneg _) (by linarith)) hden
        linarith
      have hsp' : ‖f (u j) - c‖ ≤ ‖u j‖ * (1 - t ^ 2) / (1 - t * R) := by
        rw [← hc] at hsp
        exact le_trans hsp hmono
      calc ‖u j‖ * ‖f (u j) - c‖ ≤ ‖u j‖ * (‖u j‖ * (1 - t ^ 2) / (1 - t * R)) :=
            mul_le_mul_of_nonneg_left hsp' (norm_nonneg _)
        _ = ((1 - t ^ 2) / (1 - t * R)) * ‖u j‖ ^ 2 := by field_simp
    have htailsum : Summable (fun j => u j * (f (u j) - c)) := by
      refine Summable.of_norm_bounded (hsq.mul_left ((1 - t ^ 2) / (1 - t * R))) (fun j => ?_)
      rw [norm_mul]
      exact hdisp j
    have hsplit : ∑' j, u j * f (u j) = c * (M : ℂ) + ∑' j, u j * (f (u j) - c) := by
      have hrw : (fun j => u j * f (u j)) = fun j => c * u j + u j * (f (u j) - c) := by
        funext j; ring
      rw [hrw, (hsum.of_norm.mul_left c).tsum_add htailsum, tsum_mul_left, hM]
    have htail : ‖∑' j, u j * (f (u j) - c)‖ ≤ ((1 - t ^ 2) / (1 - t * R)) * A := by
      have hnormsum : Summable (fun j => ‖u j * (f (u j) - c)‖) := by
        refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
          (hsq.mul_left ((1 - t ^ 2) / (1 - t * R)))
        rw [norm_mul]
        exact hdisp j
      calc ‖∑' j, u j * (f (u j) - c)‖ ≤ ∑' j, ‖u j * (f (u j) - c)‖ :=
            norm_tsum_le_tsum_norm hnormsum
        _ ≤ ∑' j, ((1 - t ^ 2) / (1 - t * R)) * ‖u j‖ ^ 2 :=
            hnormsum.tsum_mono (hsq.mul_left _)
              (fun j => by dsimp only; rw [norm_mul]; exact hdisp j)
        _ = ((1 - t ^ 2) / (1 - t * R)) * A := by rw [tsum_mul_left, hA]
    have hAnn : 0 ≤ A := by
      rw [← hA]
      exact tsum_nonneg (fun j => by positivity)
    have hfrac : ((1 - t ^ 2) / (1 - t * R)) * A ≤ (1 - t) * M := by
      have hkey : (1 + t) / (1 - t * R) ≤ 2 / (1 - R) := by
        rw [div_le_div_iff₀ hden (by linarith : (0:ℝ) < 1 - R)]
        nlinarith
      have hexp : ((1 - t ^ 2) / (1 - t * R)) * A = (1 - t) * (((1 + t) / (1 - t * R)) * A) := by
        field_simp
        ring
      rw [hexp]
      have hstep : ((1 + t) / (1 - t * R)) * A ≤ (2 / (1 - R)) * A :=
        mul_le_mul_of_nonneg_right hkey hAnn
      have hstep2 : (2 / (1 - R)) * A ≤ M := by
        rw [div_mul_eq_mul_div, div_le_iff₀ (by linarith)]
        linarith
      nlinarith
    calc ‖∑' j, u j * f (u j)‖ = ‖c * (M : ℂ) + ∑' j, u j * (f (u j) - c)‖ := by rw [hsplit]
      _ ≤ ‖c * (M : ℂ)‖ + ‖∑' j, u j * (f (u j) - c)‖ := norm_add_le _ _
      _ ≤ t * M + (1 - t) * M := by
          have h1 : ‖c * (M : ℂ)‖ = t * M := by
            rw [norm_mul, ← ht, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hMpos]
          rw [h1]
          linarith [htail, hfrac]
      _ = M := by ring

/-- The constant function `1` attains the bound, so the narrow-sector norm is exactly `M`. -/
theorem narrowSectorSchur_const_one {ι : Type*} {u : ι → ℂ} {M : ℝ}
    (hM : ∑' j, u j = (M : ℂ)) :
    ∑' j, u j * (1 : ℂ) = (M : ℂ) := by
  simpa using hM

end

end GaloisForLFunctions.HTGeometry
