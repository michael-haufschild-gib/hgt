import GaloisForLFunctions.HTGeometry.ClockTubeIterates
import GaloisForLFunctions.HTGeometry.ClockIteratedIntegralBound
import GaloisForLFunctions.HTGeometry.ClockOvsyannikovInduction

/-!
# The Ovsyannikov bound with several coupled transverse coordinates

The iterates on a tube obey the same bound as in one transverse variable,

`‖W_m(s,t,z)‖ ≤ Kᵐ m^{2m} |s|ᵐ |t|ᵐ / ((m!)² (ρ₀-ρ)^{2m})`  for `|Im zᵢ| ≤ ρ < ρ₀`,

with the single change that `k` coordinates cost `k` times the derivative loss:

`K = 4k + ‖V‖ρ₀²/4`.

Each step is taken at the intermediate radius `σ = ρ + (ρ₀-ρ)/(m+1)`, the double integration supplies
`|s|ᵐ⁺¹|t|ᵐ⁺¹/(m+1)²`, and the arithmetic of the recursion is the one-variable arithmetic with this
`K` — the number of transverse coordinates enters the estimate only through that constant, never
through the shape of the recursion.
-/

namespace GaloisForLFunctions.HTGeometry

open Set Complex Metric MeasureTheory

variable {k : ℕ}

/-- Continuity of the step operator applied to an iterate, at a point of the tube. -/
theorem continuousAt_tubeStep_tubeIterate {ρ : ℝ} (hρ : 0 < ρ)
    {V : ℝ → ℝ → (Fin k → ℂ) → ℂ} (hV : TubePotential V ρ) (m : ℕ)
    {q : (ℝ × ℝ) × (Fin k → ℂ)} (hq : q.2 ∈ tube k ρ) :
    ContinuousAt (fun r : (ℝ × ℝ) × (Fin k → ℂ) =>
      tubeStep (V r.1.1 r.1.2) (tubeIterate V m r.1.1 r.1.2) r.2) q := by
  classical
  obtain ⟨holo, cont⟩ := tubeIterate_regular hρ hV m
  obtain ⟨ρ₁, hρ₁0, hρ₁, hq₁⟩ := exists_inner_radius hρ hq
  have hopen : IsOpen ((univ : Set ((ℝ : Type) × ℝ)) ×ˢ tube k ρ) :=
    isOpen_univ.prod (isOpen_tube k ρ)
  have hsecond : ∀ i : Fin k, ContinuousAt (fun r : (ℝ × ℝ) × (Fin k → ℂ) =>
      cpartial i (cpartial i (tubeIterate V m r.1.1 r.1.2)) r.2) q := fun i =>
    continuousAt_cpartial_cpartial_of_tube (P := ℝ × ℝ) hρ₁ hρ₁0
      (W := fun p : ℝ × ℝ => tubeIterate V m p.1 p.2) cont (fun p => holo p.1 p.2) i hq₁
  have hsum : ContinuousAt (fun r : (ℝ × ℝ) × (Fin k → ℂ) =>
      ∑ i, cpartial i (cpartial i (tubeIterate V m r.1.1 r.1.2)) r.2) q :=
    tendsto_finsetSum (f := fun (i : Fin k) (r : (ℝ × ℝ) × (Fin k → ℂ)) =>
      cpartial i (cpartial i (tubeIterate V m r.1.1 r.1.2)) r.2)
      (a := fun i => cpartial i (cpartial i (tubeIterate V m q.1.1 q.1.2)) q.2)
      Finset.univ fun i _ => hsecond i
  have hVat : ContinuousAt (fun r : (ℝ × ℝ) × (Fin k → ℂ) => V r.1.1 r.1.2 r.2) q :=
    hV.cont.continuousAt (hopen.mem_nhds ⟨mem_univ _, hq⟩)
  have hWat : ContinuousAt
      (fun r : (ℝ × ℝ) × (Fin k → ℂ) => tubeIterate V m r.1.1 r.1.2 r.2) q :=
    cont.continuousAt (hopen.mem_nhds ⟨mem_univ _, hq⟩)
  exact (hsum.add (hVat.mul hWat)).div_const 4

/-- The step operator applied to an iterate is continuous in the null coordinates, at a fixed
transverse point of the tube. -/
theorem continuous_tubeStep_slice {ρ : ℝ} (hρ : 0 < ρ) {V : ℝ → ℝ → (Fin k → ℂ) → ℂ}
    (hV : TubePotential V ρ) (m : ℕ) {z : Fin k → ℂ} (hz : z ∈ tube k ρ) :
    Continuous fun p : ℝ × ℝ => tubeStep (V p.1 p.2) (tubeIterate V m p.1 p.2) z := by
  refine continuous_iff_continuousAt.mpr fun p => ?_
  have hmap : ContinuousAt (fun p' : ℝ × ℝ => ((p', z) : (ℝ × ℝ) × (Fin k → ℂ))) p :=
    (continuous_id.prodMk continuous_const).continuousAt
  exact (continuousAt_tubeStep_tubeIterate hρ hV m (q := (p, z)) hz).comp
    (x := p) (f := fun p' : ℝ × ℝ => ((p', z) : (ℝ × ℝ) × (Fin k → ℂ))) hmap

set_option maxHeartbeats 1000000 in
/-- **The Ovsyannikov bound for the clock iterates on a tube.** The `k` transverse coordinates enter
only through the constant `K = 4k + Mv ρ₀²/4`. -/
theorem tubeIterate_norm_le {ρ₀ Mv T : ℝ} (hρ₀ : 0 < ρ₀) {V : ℝ → ℝ → (Fin k → ℂ) → ℂ}
    (hV : TubePotential V ρ₀) (hMv0 : 0 ≤ Mv)
    (hMv : ∀ s t : ℝ, |s| ≤ T → |t| ≤ T → ∀ z ∈ tube k ρ₀, ‖V s t z‖ ≤ Mv) :
    ∀ (m : ℕ) (ρ : ℝ), 0 ≤ ρ → ρ < ρ₀ → ∀ s t : ℝ, |s| ≤ T → |t| ≤ T →
      ∀ z : Fin k → ℂ, (∀ i, |(z i).im| ≤ ρ) →
      ‖tubeIterate V m s t z‖
        ≤ (4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4) ^ m * (m : ℝ) ^ (2 * m) * (|s| ^ m * |t| ^ m)
          / ((m.factorial : ℝ) ^ (2 : ℕ) * (ρ₀ - ρ) ^ (2 * m)) := by
  set K : ℝ := 4 * k + Mv * ρ₀ ^ (2 : ℕ) / 4 with hKdef
  have hK0 : (0 : ℝ) ≤ K := by rw [hKdef]; positivity
  intro m
  induction m with
  | zero =>
    intro ρ _ _ s t _ _ z _
    rw [tubeIterate_zero]
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
      / ((m.factorial : ℝ) ^ (2 : ℕ) * (ρ₀ - σ) ^ (2 * m)) with hcdef
    have hc0 : (0 : ℝ) ≤ c := by rw [hcdef]; positivity
    have hprev : ∀ s' t' : ℝ, |s'| ≤ T → |t'| ≤ T → ∀ w ∈ tube k σ,
        ‖tubeIterate V m s' t' w‖ ≤ c * |s'| ^ m * |t'| ^ m := by
      intro s' t' hs' ht' w hw
      rcases Nat.eq_zero_or_pos m with hm | hm
      · subst hm
        rw [tubeIterate_zero]
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
        have hbase := ih σ hσ0 hσlt s' t' hs' ht' w fun i => (hw i).le
        have hpos : (0 : ℝ) < ρ₀ - σ := by rw [hrem]; positivity
        calc ‖tubeIterate V m s' t' w‖
            ≤ K ^ m * (m : ℝ) ^ (2 * m) * (|s'| ^ m * |t'| ^ m)
              / ((m.factorial : ℝ) ^ (2 : ℕ) * (ρ₀ - σ) ^ (2 * m)) := hbase
          _ = c * |s'| ^ m * |t'| ^ m := by
              rw [hcdef]
              field_simp
    have hgap2 : (0 : ℝ) < (σ - ρ) ^ (2 : ℕ) := by positivity
    have hσρle : σ - ρ ≤ ρ₀ := by rw [hgap]; linarith
    have hsq : (σ - ρ) ^ (2 : ℕ) ≤ ρ₀ ^ (2 : ℕ) := by nlinarith [hρσ, hσρle]
    have hg2ne : (σ - ρ) ^ (2 : ℕ) ≠ 0 := ne_of_gt hgap2
    have hle : 4 * k / (σ - ρ) ^ (2 : ℕ) + Mv / 4 ≤ K / (σ - ρ) ^ (2 : ℕ) := by
      rw [le_div_iff₀ hgap2, add_mul, div_mul_cancel₀ _ hg2ne, hKdef]
      nlinarith [hMv0, hsq]
    have hstepbound : ∀ s' t' : ℝ, |s'| ≤ T → |t'| ≤ T →
        ‖tubeStep (V s' t') (tubeIterate V m s' t') z‖
          ≤ K / (σ - ρ) ^ (2 : ℕ) * c * |s'| ^ m * |t'| ^ m := by
      intro s' t' hs' ht'
      obtain ⟨holo, _⟩ := tubeIterate_regular hρ₀ hV m
      have hwσ : SliceHolo (tubeIterate V m s' t') σ := sliceHolo_mono (holo s' t') hσρ₀
      have hMvσ : ∀ w ∈ tube k σ, ‖V s' t' w‖ ≤ Mv :=
        fun w hw => hMv s' t' hs' ht' w (tube_mono hσρ₀ hw)
      have hbase := norm_tubeStep_le_of_sliceHolo hρσ hMv0 hwσ (hprev s' t' hs' ht') hMvσ hz
      have hMw0 : (0 : ℝ) ≤ c * |s'| ^ m * |t'| ^ m := by positivity
      calc ‖tubeStep (V s' t') (tubeIterate V m s' t') z‖
          ≤ (4 * k / (σ - ρ) ^ (2 : ℕ) + Mv / 4) * (c * |s'| ^ m * |t'| ^ m) := hbase
        _ ≤ K / (σ - ρ) ^ (2 : ℕ) * (c * |s'| ^ m * |t'| ^ m) :=
            mul_le_mul_of_nonneg_right hle hMw0
        _ = K / (σ - ρ) ^ (2 : ℕ) * c * |s'| ^ m * |t'| ^ m := by ring
    have hFc : Continuous fun p : ℝ × ℝ =>
        tubeStep (V p.1 p.2) (tubeIterate V m p.1 p.2) z :=
      continuous_tubeStep_slice hρ₀ hV m fun i => lt_of_le_of_lt (hz i) hρ
    have hint := norm_iterated_integral_le_abs (m := m) (c := K / (σ - ρ) ^ (2 : ℕ) * c)
      (x := s) (y := t) (mul_nonneg (div_nonneg hK0 (sq_nonneg _)) hc0) hFc
      (fun s' hs' t' ht' => hstepbound s' t'
        (le_trans (abs_le_abs_of_mem_uIcc_zero hs') hsT)
        (le_trans (abs_le_abs_of_mem_uIcc_zero ht') htT))
    have hloss : K / (σ - ρ) ^ (2 : ℕ) = K * ((m : ℝ) + 1) ^ (2 : ℕ) / (ρ₀ - ρ) ^ (2 : ℕ) := by
      rw [hgap]
      field_simp
    have hcval : c = K ^ m * ((m : ℝ) + 1) ^ (2 * m)
        / ((m.factorial : ℝ) ^ (2 : ℕ) * (ρ₀ - ρ) ^ (2 * m)) := by
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
        calc K ^ m * (m : ℝ) ^ (2 * m) * ((m.factorial : ℝ) ^ (2 : ℕ) * (ρ₀ - ρ) ^ (2 * m))
            = K ^ m * (m.factorial : ℝ) ^ (2 : ℕ) * ((m : ℝ) ^ (2 * m) * (ρ₀ - ρ) ^ (2 * m)) := by
              ring
          _ = K ^ m * (m.factorial : ℝ) ^ (2 : ℕ)
              * (((m : ℝ) + 1) ^ (2 * m)
                * ((ρ₀ - ρ) * (m : ℝ) / ((m : ℝ) + 1)) ^ (2 * m)) := by rw [hratio]
          _ = K ^ m * ((m : ℝ) + 1) ^ (2 * m)
              * ((m.factorial : ℝ) ^ (2 : ℕ)
                * ((ρ₀ - ρ) * (m : ℝ) / ((m : ℝ) + 1)) ^ (2 * m)) := by ring
    have hident := ovsyannikov_step_identity (K := K) (G := ρ₀ - ρ) (x := |s|) (y := |t|) hG m
    have hcast : (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 := by push_cast; ring
    rw [hcast]
    calc ‖tubeIterate V (m + 1) s t z‖
        ≤ K / (σ - ρ) ^ (2 : ℕ) * c * (|s| ^ (m + 1) * |t| ^ (m + 1)) / ((m : ℝ) + 1) ^ (2 : ℕ) := hint
      _ = K * ((m : ℝ) + 1) ^ (2 : ℕ) / (ρ₀ - ρ) ^ (2 : ℕ)
            * (K ^ m * ((m : ℝ) + 1) ^ (2 * m)
              / ((m.factorial : ℝ) ^ (2 : ℕ) * (ρ₀ - ρ) ^ (2 * m)))
            * (|s| ^ (m + 1) * |t| ^ (m + 1) / ((m : ℝ) + 1) ^ (2 : ℕ)) := by
          rw [hloss, hcval]
          ring
      _ = K ^ (m + 1) * ((m : ℝ) + 1) ^ (2 * (m + 1)) * (|s| ^ (m + 1) * |t| ^ (m + 1))
            / (((m + 1).factorial : ℝ) ^ (2 : ℕ) * (ρ₀ - ρ) ^ (2 * (m + 1))) := hident

end GaloisForLFunctions.HTGeometry
