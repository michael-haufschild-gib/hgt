import GaloisForLFunctions.RHTower.ChiCubicHyperbolicPrimeIntegral

/-!
# Actual physical-window cancellation at every hyperbolic band edge

The physical height window vanishes at both original band endpoints. A
truncated cell therefore gains its radius divided by the band scale. This
pays every edge with the same reciprocal-square gap budget as the bulk.
-/

noncomputable section

namespace RHTower

open Finset Filter Topology MeasureTheory
open GaloisForLFunctions.RHTower

private theorem height_window_lipschitz :
    ∃ L : ℝ, 0 < L ∧ ∀ x ∈ Set.Icc (0 : ℝ) 4, ∀ y ∈ Set.Icc (0 : ℝ) 4,
      |bagPhysicalHeightWindow y - bagPhysicalHeightWindow x| ≤ L * |y - x| := by
  have hc : Continuous (deriv (fun x : ℝ => bagPhysicalHeightWindow x)) :=
    (bagPhysicalHeightWindow.contDiff (n := 1)).continuous_deriv_one
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨|B| + 1, by positivity, ?_⟩
  intro x hx y hy
  have hb : ∀ t ∈ Set.Icc (0 : ℝ) 4,
      ‖deriv (fun x : ℝ => bagPhysicalHeightWindow x) t‖ ≤ |B| + 1 :=
    fun t ht => (hB t ht).trans (by linarith [le_abs_self B])
  simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_deriv_le
    (fun t _ => (bagPhysicalHeightWindow.contDiff (n := 1)).differentiable (by norm_num) t)
    hb (convex_Icc (0 : ℝ) 4) hx hy

private theorem norm_amplitude_le_window {N x : ℝ} (hN : 1 < N) {p r : ℕ}
    (hp : p ∈ primeProfileBand N) (hr : r ∈ primeProfileBand N)
    (hx : x ∈ Set.Icc N (2 * N)) :
    ‖chiCubicHyperbolicPrimeAmplitude N (p, r) x‖ ≤
      (2 * Real.pi / (N * Real.log N)) *
        bagPhysicalHeightWindow ((p : ℝ) * x / ((r : ℝ) * N)) := by
  have hN0 : 0 < N := by linarith
  obtain ⟨_, hpN, _⟩ := primeProfileBand_mem hN0.le hp
  obtain ⟨_, hrN, _⟩ := primeProfileBand_mem hN0.le hr
  have hx0 : 0 < x := by linarith [hx.1]
  have hlogN : 0 < Real.log N := Real.log_pos hN
  have hlogx : 0 < Real.log x := Real.log_pos (by linarith [hx.1])
  have hlogs := Real.log_le_log hN0 hx.1
  have hpV := norm_smoothAFECutoff_le_one (div_pos (hN0.trans hpN) hN0)
  have hrV := norm_smoothAFECutoff_le_one (div_pos (hN0.trans hrN) hN0)
  have hxV := norm_smoothAFECutoff_le_one (div_pos hx0 hN0)
  have hw0 : 0 ≤ bagPhysicalHeightWindow ((p : ℝ) * x / ((r : ℝ) * N)) :=
    bagPhysicalHeightWindow.nonneg
  simp only [chiCubicHyperbolicPrimeAmplitude, norm_div, norm_mul, Complex.norm_conj,
    Complex.norm_natCast, norm_bourgainOscillation, mul_one]
  rw [Complex.norm_of_nonneg (show 0 ≤ 2 * Real.pi by positivity),
    Complex.norm_of_nonneg bagPhysicalHeightWindow.nonneg, Complex.norm_of_nonneg hlogx.le]
  calc
    _ ≤ (2 * Real.pi) * 1 * 1 * 1 / (r : ℝ) *
        bagPhysicalHeightWindow ((p : ℝ) * x / ((r : ℝ) * N)) / Real.log x := by
      gcongr
    _ ≤ (2 * Real.pi) * 1 * 1 * 1 / N *
        bagPhysicalHeightWindow ((p : ℝ) * x / ((r : ℝ) * N)) / Real.log N := by
      gcongr
    _ = _ := by ring

private theorem window_le_of_near_endpoint {N x R e : ℝ} (hN : 0 < N)
    {p r : ℕ} (hp : p ∈ primeProfileBand N) (hr : r ∈ primeProfileBand N)
    (hx : x ∈ Set.Icc N (2 * N)) (he : e = 1 ∨ e = 2)
    (hrE : |(r : ℝ) - e * N| ≤ R) (hxR : |x - r| ≤ R)
    {L : ℝ} (hL : 0 < L)
    (hLip : ∀ a ∈ Set.Icc (0 : ℝ) 4, ∀ b ∈ Set.Icc (0 : ℝ) 4,
      |bagPhysicalHeightWindow b - bagPhysicalHeightWindow a| ≤ L * |b - a|) :
    bagPhysicalHeightWindow ((p : ℝ) * x / ((r : ℝ) * N)) ≤
      2 * L * (|(p : ℝ) - r| + R) / N := by
  obtain ⟨_, hpN, hp2⟩ := primeProfileBand_mem hN.le hp
  obtain ⟨_, hrN, _⟩ := primeProfileBand_mem hN.le hr
  have hr0 : (0 : ℝ) < r := hN.trans hrN
  have hx0 : 0 < x := hN.trans_le hx.1
  have hy : (p : ℝ) * x / ((r : ℝ) * N) ∈ Set.Icc (0 : ℝ) 4 := by
    refine ⟨by positivity, (div_le_iff₀ (mul_pos hr0 hN)).2 ?_⟩
    have hm := mul_le_mul hp2 hx.2 hx0.le (by positivity : 0 ≤ 2 * N)
    nlinarith
  have he0 : bagPhysicalHeightWindow e = 0 :=
    bagPhysicalHeightWindow.zero_of_le_dist (by
      change (1 / 2 : ℝ) ≤ dist e (3 / 2)
      rcases he with rfl | rfl <;> norm_num [Real.dist_eq])
  have heI : e ∈ Set.Icc (0 : ℝ) 4 := by rcases he with rfl | rfl <;> norm_num
  have hfirst : |(p : ℝ) * x / ((r : ℝ) * N) - x / N| ≤
      2 * |(p : ℝ) - r| / N := by
    have heq : (p : ℝ) * x / ((r : ℝ) * N) - x / N =
        ((p : ℝ) - r) * x / ((r : ℝ) * N) := by field_simp
    rw [heq, abs_div, abs_mul, abs_of_pos hx0, abs_of_pos (mul_pos hr0 hN)]
    apply (div_le_div_iff₀ (mul_pos hr0 hN) hN).2
    have hm := mul_le_mul_of_nonneg_left (show x ≤ 2 * r by linarith [hx.2])
      (abs_nonneg ((p : ℝ) - r))
    nlinarith [mul_le_mul_of_nonneg_right hm hN.le]
  have hsecond : |x / N - e| ≤ 2 * R / N := by
    have heq : x / N - e = (x - e * N) / N := by field_simp
    rw [heq, abs_div, abs_of_pos hN]
    exact div_le_div_of_nonneg_right
      ((abs_sub_le x (r : ℝ) (e * N)).trans (by linarith)) hN.le
  have hdist : |(p : ℝ) * x / ((r : ℝ) * N) - e| ≤
      2 * (|(p : ℝ) - r| + R) / N := by
    exact (abs_sub_le _ (x / N) _).trans ((add_le_add hfirst hsecond).trans_eq (by ring))
  have hw := hLip e heI _ hy
  rw [he0, sub_zero, abs_of_nonneg bagPhysicalHeightWindow.nonneg] at hw
  exact hw.trans ((mul_le_mul_of_nonneg_left hdist hL.le).trans_eq (by ring))

/-- A single unconditional source constant pays EVERY actual hyperbolic pair
integral, including truncated band-edge cells. No prime-count or regularity
premise remains. -/
theorem exists_chiCubicHyperbolicPrimePairIntegral_all_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℝ, 1 < N → 1 ≤ Real.log N → ∀ M : ℕ,
      ∀ p ∈ primeProfileBand N, ∀ r ∈ primeProfileBand N, p ≠ r →
      ‖chiCubicHyperbolicPrimePairIntegral N M (p, r)‖ ≤
        C * ((M : ℝ) + 1) ^ 2 *
          (1 / (|(p : ℝ) - r| ^ 2 * Real.log N) +
            |(p : ℝ) - r| / (N * Real.log N)) := by
  obtain ⟨A, hA, hbulk⟩ := exists_chiCubicHyperbolicPrimePairIntegral_bulk_bound
  obtain ⟨L, hL, hLip⟩ := height_window_lipschitz
  let C := A + 32 * Real.pi * L + 4 * Real.pi + 1
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro N hN hlog M p hp r hr hne
  have hN0 : 0 < N := by linarith
  have hlog0 : 0 < Real.log N := by linarith
  obtain ⟨_, hrN, hr2⟩ := primeProfileBand_mem hN0.le hr
  let d := |(p : ℝ) - r|
  let R : ℝ := (M : ℝ) * r / d
  have hd : 0 < d := abs_pos.2 (sub_ne_zero.2 (by exact_mod_cast hne))
  have hd1 : 1 ≤ d := by
    rcases lt_or_gt_of_ne hne with h | h
    · have hh : (p : ℝ) + 1 ≤ r := by exact_mod_cast h
      dsimp [d]
      rw [abs_of_nonpos (by linarith)]
      linarith
    · have hh : (r : ℝ) + 1 ≤ p := by exact_mod_cast h
      dsimp [d]
      rw [abs_of_nonneg (by linarith)]
      linarith
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hRle : R ≤ 2 * M * N / d := by
    dsimp [R]
    calc
      _ ≤ (M : ℝ) * (2 * N) / d := by gcongr
      _ = _ := by ring
  have hM : (M : ℝ) ^ 2 ≤ ((M : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) M]
  have hM1 : (M : ℝ) ≤ ((M : ℝ) + 1) ^ 2 := by nlinarith [sq_nonneg (M : ℝ)]
  have hPL : 0 < Real.pi * L := mul_pos Real.pi_pos hL
  have hA' : A ≤ C := by dsimp [C]; linarith [Real.pi_pos]
  have hpi : 4 * Real.pi ≤ C := by dsimp [C]; linarith
  by_cases hb : N < (r : ℝ) - R ∧ (r : ℝ) + R ≤ 2 * N
  · calc
      _ ≤ A * (M : ℝ) ^ 2 / (d ^ 2 * Real.log N) + 4 * Real.pi * d / (N * Real.log N) :=
        hbulk N hN hlog M p hp r hr hne hb.1 hb.2
      _ ≤ C * ((M : ℝ) + 1) ^ 2 / (d ^ 2 * Real.log N) +
          C * ((M : ℝ) + 1) ^ 2 * d / (N * Real.log N) := by
        apply add_le_add
        · exact div_le_div_of_nonneg_right
            (mul_le_mul hA' hM (sq_nonneg _) hC.le) (by positivity)
        · have hCq : C ≤ C * ((M : ℝ) + 1) ^ 2 := by
            calc
              C = C * 1 := by ring
              _ ≤ _ := mul_le_mul_of_nonneg_left
                (by nlinarith [sq_nonneg (M : ℝ), Nat.cast_nonneg (α := ℝ) M]) hC.le
          exact div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (hpi.trans hCq) hd.le) (by positivity)
      _ = _ := by ring
  obtain ⟨e, he, hrE⟩ : ∃ e : ℝ, (e = 1 ∨ e = 2) ∧ |(r : ℝ) - e * N| ≤ R := by
    by_cases hl : N < (r : ℝ) - R
    · refine ⟨2, Or.inr rfl, ?_⟩
      have hright : ¬(r : ℝ) + R ≤ 2 * N := fun h => hb ⟨hl, h⟩
      rw [abs_of_nonpos (by linarith)]
      linarith
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [one_mul, abs_of_nonneg (by linarith)]
      linarith
  have hxR : ∀ x ∈ chiCubicHyperbolicPrimeSupport N M (p, r), |x - r| ≤ R := by
    intro x hx
    apply (le_div_iff₀ hd).2
    simpa only [mul_comm] using hx.2.2
  have hsub : chiCubicHyperbolicPrimeSupport N M (p, r) ⊆
      Set.Icc ((r : ℝ) - R) ((r : ℝ) + R) := by
    intro x hx
    have hh := abs_le.1 (hxR x hx)
    exact ⟨by linarith, by linarith⟩
  have hfinite : volume (chiCubicHyperbolicPrimeSupport N M (p, r)) < ⊤ :=
    lt_of_le_of_lt (measure_mono hsub) isCompact_Icc.measure_lt_top
  have hamp : ∀ x ∈ chiCubicHyperbolicPrimeSupport N M (p, r),
      ‖chiCubicHyperbolicPrimeAmplitude N (p, r) x‖ ≤
        (2 * Real.pi / (N * Real.log N)) * (2 * L * (d + R) / N) := by
    intro x hx
    have hxb : x ∈ Set.Icc N (2 * N) := ⟨hx.1.1.le, hx.1.2⟩
    exact (norm_amplitude_le_window hN hp hr hxb).trans
      (mul_le_mul_of_nonneg_left (window_le_of_near_endpoint hN0 hp hr hxb he hrE
        (hxR x hx) hL hLip) (by positivity))
  have hmass : ‖chiCubicHyperbolicPrimePairIntegral N M (p, r)‖ ≤
      32 * Real.pi * L * (M : ℝ) ^ 2 / (d ^ 2 * Real.log N) +
        16 * Real.pi * L * M / (N * Real.log N) := by
    calc
      _ ≤ (2 * Real.pi / (N * Real.log N)) * (2 * L * (d + R) / N) *
          volume.real (chiCubicHyperbolicPrimeSupport N M (p, r)) :=
        norm_setIntegral_le_of_norm_le_const hfinite hamp
      _ ≤ (2 * Real.pi / (N * Real.log N)) * (2 * L * (d + R) / N) *
          volume.real (Set.Icc ((r : ℝ) - R) ((r : ℝ) + R)) :=
        mul_le_mul_of_nonneg_left (measureReal_mono hsub isCompact_Icc.measure_lt_top.ne)
          (by positivity)
      _ = (2 * Real.pi / (N * Real.log N)) * (2 * L * (d + R) / N) * (2 * R) := by
        rw [Real.volume_real_Icc_of_le (by linarith)]
        ring
      _ ≤ (2 * Real.pi / (N * Real.log N)) * (2 * L * (d + 2 * M * N / d) / N) *
          (2 * (2 * M * N / d)) := by gcongr
      _ = _ := by field_simp; ring
  have h32 : 32 * Real.pi * L ≤ C := by dsimp [C]; linarith [Real.pi_pos]
  have h16 : 16 * Real.pi * L ≤ C := by
    have hh : 0 < Real.pi * L := mul_pos Real.pi_pos hL
    dsimp [C]
    linarith
  calc
    _ ≤ _ := hmass
    _ ≤ C * ((M : ℝ) + 1) ^ 2 / (d ^ 2 * Real.log N) +
        C * ((M : ℝ) + 1) ^ 2 * d / (N * Real.log N) := by
      apply add_le_add
      · gcongr
      · apply div_le_div_of_nonneg_right _ (by positivity)
        calc
          _ ≤ C * ((M : ℝ) + 1) ^ 2 := by gcongr
          _ ≤ C * ((M : ℝ) + 1) ^ 2 * d := by nlinarith [mul_nonneg hC.le (sq_nonneg ((M : ℝ) + 1))]
    _ = _ := by ring

end RHTower
