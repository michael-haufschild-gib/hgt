import GaloisForLFunctions.HTGeometry.ClockIterates
import GaloisForLFunctions.HTGeometry.ClockIteratedIntegralBound
import GaloisForLFunctions.HTGeometry.ClockOvsyannikovInduction

/-!
# The Ovsyannikov bound for the clock iterates

The iterates of the clock equation obey the bound the Ovsyannikov scheme predicts:

`‖W_m(s,t,z)‖ ≤ Kᵐ m^{2m} |s|ᵐ |t|ᵐ / ((m!)² (ρ₀-ρ)^{2m})`  for `|Im z| ≤ ρ < ρ₀`,

with `K = 4 + ‖V‖ρ₀²/4`. Each step is taken at the intermediate radius `σ = ρ + (ρ₀-ρ)/(m+1)`,
where the derivative loss of the step operator is `4/(σ-ρ)²` and the potential contributes `‖V‖/4`;
the double integration supplies `|s|ᵐ⁺¹|t|ᵐ⁺¹/(m+1)²`, and the three factors multiply to exactly
the next bound. The bound holds for null coordinates of either sign, so it covers a full rectangular
neighbourhood of the origin rather than one quadrant.

The stage `m = 0` uses the normalisation `W₀ = 1`, which holds on the whole plane, rather than the
inductive bound — at that stage the intermediate radius is `ρ₀` itself.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric MeasureTheory

/-- Continuity of the step operator applied to an iterate, at a point of the strip. -/
theorem continuousAt_clockStripStep_clockIterate {ρ : ℝ} {V : ℝ → ℝ → ℂ → ℂ}
    (hV : StripPotential V ρ) (m : ℕ)
    {q : (ℝ × ℝ) × ℂ} (hq : q.2 ∈ imStrip ρ) :
    ContinuousAt
      (fun r : (ℝ × ℝ) × ℂ =>
        clockStripStep (V r.1.1 r.1.2) (clockIterate V m r.1.1 r.1.2) r.2) q := by
  obtain ⟨holo, cont⟩ := clockIterate_regular hV m
  have him : |q.2.im| < ρ := mem_imStrip.mp hq
  have h1 : |q.2.im| < (|q.2.im| + ρ) / 2 := by linarith
  have h2 : (|q.2.im| + ρ) / 2 < ρ := by linarith
  have h0 : (0 : ℝ) ≤ (|q.2.im| + ρ) / 2 := le_trans (abs_nonneg _) h1.le
  have hsecond : ContinuousAt
      (fun q' : (ℝ × ℝ) × ℂ => deriv (deriv (clockIterate V m q'.1.1 q'.1.2)) q'.2) q :=
    continuousAt_deriv_deriv_of_strip (P := ℝ × ℝ) h2 h0
      (W := fun p : ℝ × ℝ => clockIterate V m p.1 p.2) cont (fun p => holo p.1 p.2)
      (mem_imStrip.mpr h1)
  have hVat : ContinuousAt (fun q' : (ℝ × ℝ) × ℂ => V q'.1.1 q'.1.2 q'.2) q :=
    hV.cont.continuousAt ((isOpen_univ.prod (isOpen_imStrip ρ)).mem_nhds ⟨mem_univ _, hq⟩)
  have hWat : ContinuousAt
      (fun q' : (ℝ × ℝ) × ℂ => clockIterate V m q'.1.1 q'.1.2 q'.2) q :=
    cont.continuousAt ((isOpen_univ.prod (isOpen_imStrip ρ)).mem_nhds ⟨mem_univ _, hq⟩)
  exact (hsecond.add (hVat.mul hWat)).div_const 4

/-- The step operator applied to an iterate is continuous in the null coordinates, at a fixed
transverse point of the strip. -/
theorem continuous_clockStripStep_slice {ρ : ℝ} {V : ℝ → ℝ → ℂ → ℂ}
    (hV : StripPotential V ρ) (m : ℕ) {z : ℂ} (hz : z ∈ imStrip ρ) :
    Continuous fun p : ℝ × ℝ => clockStripStep (V p.1 p.2) (clockIterate V m p.1 p.2) z := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  have hmap : ContinuousAt (fun p' : ℝ × ℝ => ((p', z) : (ℝ × ℝ) × ℂ)) p :=
    (continuous_id.prodMk continuous_const).continuousAt
  have hcomp := (continuousAt_clockStripStep_clockIterate hV m (q := (p, z)) hz).comp
    (x := p) (f := fun p' : ℝ × ℝ => ((p', z) : (ℝ × ℝ) × ℂ)) hmap
  exact hcomp

set_option maxHeartbeats 1000000 in
/-- **The Ovsyannikov bound for the clock iterates.** -/
theorem clockIterate_norm_le {ρ₀ Mv T : ℝ} (hρ₀ : 0 < ρ₀) {V : ℝ → ℝ → ℂ → ℂ}
    (hV : StripPotential V ρ₀)
    (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ imStrip ρ₀, ‖V s t z‖ ≤ Mv) :
    ∀ (m : ℕ) (ρ : ℝ), 0 ≤ ρ → ρ < ρ₀ → ∀ s t : ℝ, |s| ≤ T → |t| ≤ T →
      ∀ z : ℂ, |z.im| ≤ ρ →
      ‖clockIterate V m s t z‖
        ≤ (4 + Mv * ρ₀ ^ 2 / 4) ^ m * (m : ℝ) ^ (2 * m) * (|s| ^ m * |t| ^ m)
          / ((m.factorial : ℝ) ^ 2 * (ρ₀ - ρ) ^ (2 * m)) := by
  set K : ℝ := 4 + Mv * ρ₀ ^ 2 / 4 with hKdef
  have hK0 : (0 : ℝ) ≤ K := by rw [hKdef]; positivity
  intro m
  induction m with
  | zero =>
    intro ρ _ _ s t _ _ z _
    rw [clockIterate_zero]
    norm_num
  | succ m ih =>
    intro ρ hρ0 hρ s t hsT htT z hz
    have hG : (0 : ℝ) < ρ₀ - ρ := by linarith
    have hm1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    have hfrac : (0 : ℝ) < (ρ₀ - ρ) / ((m : ℝ) + 1) := by positivity
    set σ : ℝ := ρ + (ρ₀ - ρ) / ((m : ℝ) + 1) with hσdef
    have hρσ : ρ < σ := by rw [hσdef]; linarith
    have hle1 : (ρ₀ - ρ) / ((m : ℝ) + 1) ≤ ρ₀ - ρ := by
      rw [div_le_iff₀ hm1]
      nlinarith [hG]
    have hσρ₀ : σ ≤ ρ₀ := by rw [hσdef]; linarith
    have hσ0 : (0 : ℝ) ≤ σ := le_trans hρ0 hρσ.le
    have hgap : σ - ρ = (ρ₀ - ρ) / ((m : ℝ) + 1) := by rw [hσdef]; ring
    have hrem : ρ₀ - σ = (ρ₀ - ρ) * (m : ℝ) / ((m : ℝ) + 1) := by
      rw [hσdef]
      field_simp
      ring
    have hfacpos : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
    set c : ℝ := K ^ m * (m : ℝ) ^ (2 * m)
      / ((m.factorial : ℝ) ^ 2 * (ρ₀ - σ) ^ (2 * m)) with hcdef
    have hc0 : (0 : ℝ) ≤ c := by rw [hcdef]; positivity
    have hprev : ∀ s' t' : ℝ, |s'| ≤ T → |t'| ≤ T → ∀ w : ℂ, w ∈ imStrip σ →
        ‖clockIterate V m s' t' w‖ ≤ c * |s'| ^ m * |t'| ^ m := by
      intro s' t' hs' ht' w hw
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        rw [clockIterate_zero]
        have hc1 : c = 1 := by rw [hcdef]; norm_num
        rw [hc1]
        norm_num
      · have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        have hσlt : σ < ρ₀ := by
          rw [hσdef]
          have hlt : (ρ₀ - ρ) / ((m : ℝ) + 1) < ρ₀ - ρ := by
            rw [div_lt_iff₀ hm1]
            nlinarith [hG, hmpos]
          linarith
        have hbase := ih σ hσ0 hσlt s' t' hs' ht' w (le_of_lt (mem_imStrip.mp hw))
        have hpos : (0 : ℝ) < ρ₀ - σ := by rw [hrem]; positivity
        calc ‖clockIterate V m s' t' w‖
            ≤ K ^ m * (m : ℝ) ^ (2 * m) * (|s'| ^ m * |t'| ^ m)
              / ((m.factorial : ℝ) ^ 2 * (ρ₀ - σ) ^ (2 * m)) := hbase
          _ = c * |s'| ^ m * |t'| ^ m := by
              rw [hcdef]
              field_simp
    have hgap2 : (0 : ℝ) < (σ - ρ) ^ 2 := by positivity
    have hσρle : σ - ρ ≤ ρ₀ := by rw [hgap]; linarith
    have hsq : (σ - ρ) ^ 2 ≤ ρ₀ ^ 2 := by nlinarith [hρσ, hσρle]
    have hg2ne : (σ - ρ) ^ 2 ≠ 0 := ne_of_gt hgap2
    have hle : 4 / (σ - ρ) ^ 2 + Mv / 4 ≤ K / (σ - ρ) ^ 2 := by
      rw [le_div_iff₀ hgap2, add_mul, div_mul_cancel₀ _ hg2ne, hKdef]
      nlinarith [hMv0, hsq]
    have hstepbound : ∀ s' t' : ℝ, |s'| ≤ T → |t'| ≤ T →
        ‖clockStripStep (V s' t') (clockIterate V m s' t') z‖
          ≤ K / (σ - ρ) ^ 2 * c * |s'| ^ m * |t'| ^ m := by
      intro s' t' hs' ht'
      obtain ⟨holo, _⟩ := clockIterate_regular hV m
      have hwσ : DifferentiableOn ℂ (clockIterate V m s' t') (imStrip σ) :=
        (holo s' t').mono (imStrip_mono hσρ₀)
      have hMvσ : ∀ w ∈ imStrip σ, ‖V s' t' w‖ ≤ Mv :=
        fun w hw => hMv s' t' hs' ht' w (imStrip_mono hσρ₀ hw)
      have hbase := norm_clockStripStep_le hρσ hMv0 hwσ (hprev s' t' hs' ht') hMvσ hz
      have hMw0 : (0 : ℝ) ≤ c * |s'| ^ m * |t'| ^ m := by positivity
      calc ‖clockStripStep (V s' t') (clockIterate V m s' t') z‖
          ≤ (4 / (σ - ρ) ^ 2 + Mv / 4) * (c * |s'| ^ m * |t'| ^ m) := hbase
        _ ≤ K / (σ - ρ) ^ 2 * (c * |s'| ^ m * |t'| ^ m) :=
            mul_le_mul_of_nonneg_right hle hMw0
        _ = K / (σ - ρ) ^ 2 * c * |s'| ^ m * |t'| ^ m := by ring
    have hFc : Continuous fun p : ℝ × ℝ =>
        clockStripStep (V p.1 p.2) (clockIterate V m p.1 p.2) z :=
      continuous_clockStripStep_slice hV m (mem_imStrip.mpr (lt_of_le_of_lt hz hρ))
    have hint := norm_iterated_integral_le_abs (m := m) (c := K / (σ - ρ) ^ 2 * c)
      (x := s) (y := t) (mul_nonneg (div_nonneg hK0 (sq_nonneg _)) hc0) hFc
      (fun s' hs' t' ht' => hstepbound s' t'
        (le_trans (abs_le_abs_of_mem_uIcc_zero hs') hsT)
        (le_trans (abs_le_abs_of_mem_uIcc_zero ht') htT))
    have hloss : K / (σ - ρ) ^ 2 = K * ((m : ℝ) + 1) ^ 2 / (ρ₀ - ρ) ^ 2 := by
      rw [hgap]
      field_simp
    have hcval : c = K ^ m * ((m : ℝ) + 1) ^ (2 * m)
        / ((m.factorial : ℝ) ^ 2 * (ρ₀ - ρ) ^ (2 * m)) := by
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        rw [hcdef]
        norm_num
      · have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
        have hd1 : (0 : ℝ) < ((ρ₀ - ρ) * (m : ℝ) / ((m : ℝ) + 1)) ^ (2 * m) := by positivity
        have hd2 : (0 : ℝ) < (ρ₀ - ρ) ^ (2 * m) := by positivity
        have hratio := sq_pow_ratio_intermediate hG m
        rw [div_eq_div_iff (ne_of_gt hd1) (ne_of_gt hd2)] at hratio
        rw [hcdef, hrem, div_eq_div_iff (by positivity) (by positivity)]
        calc K ^ m * (m : ℝ) ^ (2 * m) * ((m.factorial : ℝ) ^ 2 * (ρ₀ - ρ) ^ (2 * m))
            = K ^ m * (m.factorial : ℝ) ^ 2 * ((m : ℝ) ^ (2 * m) * (ρ₀ - ρ) ^ (2 * m)) := by
              ring
          _ = K ^ m * (m.factorial : ℝ) ^ 2
              * (((m : ℝ) + 1) ^ (2 * m)
                * ((ρ₀ - ρ) * (m : ℝ) / ((m : ℝ) + 1)) ^ (2 * m)) := by rw [hratio]
          _ = K ^ m * ((m : ℝ) + 1) ^ (2 * m)
              * ((m.factorial : ℝ) ^ 2
                * ((ρ₀ - ρ) * (m : ℝ) / ((m : ℝ) + 1)) ^ (2 * m)) := by ring
    have hident := ovsyannikov_step_identity (K := K) (G := ρ₀ - ρ) (x := |s|) (y := |t|) hG m
    have hcast : (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    calc ‖clockIterate V (m + 1) s t z‖
        ≤ K / (σ - ρ) ^ 2 * c * (|s| ^ (m + 1) * |t| ^ (m + 1)) / ((m : ℝ) + 1) ^ 2 := hint
      _ = K * ((m : ℝ) + 1) ^ 2 / (ρ₀ - ρ) ^ 2
            * (K ^ m * ((m : ℝ) + 1) ^ (2 * m)
              / ((m.factorial : ℝ) ^ 2 * (ρ₀ - ρ) ^ (2 * m)))
            * (|s| ^ (m + 1) * |t| ^ (m + 1) / ((m : ℝ) + 1) ^ 2) := by
          rw [hloss, hcval]
          ring
      _ = K ^ (m + 1) * ((m : ℝ) + 1) ^ (2 * (m + 1)) * (|s| ^ (m + 1) * |t| ^ (m + 1))
            / (((m + 1).factorial : ℝ) ^ 2 * (ρ₀ - ρ) ^ (2 * (m + 1))) := hident

end GaloisForLFunctions.HTGeometry
