import GaloisForLFunctions.RHTower.Sieve.InghamUniformDetectorMellinNegativeHalfContour
import GaloisForLFunctions.RHTower.Sieve.InghamDetectorHorizontalTube
import GaloisForLFunctions.RHTower.GammaDampedVerticalBound

/-!
# Route T: polylogarithmic horizontal control on the fixed negative-half contour

The Euler anchor `14/5 + iτ`, Jensen factorization, finite root separation, and conjugation
produce one symmetric height whose two horizontal edges are zero-free and carry an unconditional
`O((1 + log X)^(2 : ℕ))` bound for the regularized zeta logarithmic derivative.
-/

open Complex Filter Metric Set Finset

namespace RHTower.Sieve

noncomputable section

private theorem routeT_negativeHalf_zeta_tube_geometry
    {X : ℕ} {tau : ℝ} (hX : 12 ≤ X)
    (htlow : (X : ℝ) / 2 ≤ |tau|) (hthigh : |tau| ≤ 2 * (X : ℝ))
    {z : ℂ} (hz : z ∈ closedBall ((14 / 5 : ℂ) + (tau : ℂ) * I) 4) :
    |z.re| ≤ 7 ∧ 1 ≤ |z.im| ∧ |z.im| ≤ 3 * (X : ℝ) ∧
      ‖z - 1‖ ≤ 4 * (X : ℝ) := by
  let c0 : ℂ := (14 / 5 : ℂ) + (tau : ℂ) * I
  have hdist : ‖z - c0‖ ≤ 4 := by
    simpa only [mem_closedBall, dist_eq_norm] using hz
  have hreabs : |z.re - 14 / 5| ≤ 4 := by
    have h := Complex.abs_re_le_norm (z - c0)
    have hcRe : c0.re = 14 / 5 := by simp [c0]
    rw [sub_re, hcRe] at h
    exact h.trans hdist
  have himabs : |z.im - tau| ≤ 4 := by
    have h := Complex.abs_im_le_norm (z - c0)
    have hcIm : c0.im = tau := by simp [c0]
    rw [sub_im, hcIm] at h
    exact h.trans hdist
  have hrelo : -6 / 5 ≤ z.re := by linarith [(abs_le.mp hreabs).1]
  have hrehi : z.re ≤ 34 / 5 := by linarith [(abs_le.mp hreabs).2]
  have hre7 : |z.re| ≤ 7 := by rw [abs_le]; constructor <;> linarith
  have himhi0 : |z.im| ≤ |tau| + 4 := by
    calc
      |z.im| = |(z.im - tau) + tau| := by ring_nf
      _ ≤ |z.im - tau| + |tau| := abs_add_le _ _
      _ ≤ |tau| + 4 := by linarith
  have hXR : (12 : ℝ) ≤ X := by exact_mod_cast hX
  have himhi : |z.im| ≤ 3 * (X : ℝ) := by linarith
  have himlo0 : |tau| ≤ |z.im| + 4 := by
    calc
      |tau| = |(tau - z.im) + z.im| := by ring_nf
      _ ≤ |tau - z.im| + |z.im| := abs_add_le _ _
      _ = |z.im - tau| + |z.im| := by rw [abs_sub_comm]
      _ ≤ |z.im| + 4 := by linarith
  have himlo : 1 ≤ |z.im| := by linarith
  have hre1 : |(z - 1).re| ≤ 6 := by
    simp only [sub_re, one_re]
    rw [abs_le]
    constructor <;> linarith
  have hnorm := Complex.norm_le_abs_re_add_abs_im (z - 1)
  have himsub : |(z - 1).im| = |z.im| := by simp
  rw [himsub] at hnorm
  have hsub : ‖z - 1‖ ≤ 4 * (X : ℝ) := by linarith
  exact ⟨hre7, himlo, himhi, hsub⟩

theorem exists_norm_zetaResidueUnit_negativeHalf_horizontalTube_le :
    ∃ (C : ℝ) (Q : ℕ), 0 ≤ C ∧ ∀ {X : ℕ} {tau : ℝ}, 12 ≤ X →
      (X : ℝ) / 2 ≤ |tau| → |tau| ≤ 2 * (X : ℝ) →
      ∀ z ∈ closedBall ((14 / 5 : ℂ) + (tau : ℂ) * I) 4,
        ‖zetaResidueUnit z‖ ≤ C * (X : ℝ) ^ Q := by
  obtain ⟨Cz, N, hCz, hzeta⟩ := RHTower.exists_bound_norm_riemannZeta_strip 7
  let C : ℝ := 4 * Cz * 3 ^ N
  let Q : ℕ := N + 1
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C, Q, hC, ?_⟩
  intro X tau hX htlow hthigh z hz
  obtain ⟨hzre, hzim1, hzimX, hzsub⟩ :=
    routeT_negativeHalf_zeta_tube_geometry hX htlow hthigh hz
  have hz1 : z ≠ 1 := by
    intro h
    subst z
    norm_num at hzim1
  have hzetaBound : ‖riemannZeta z‖ ≤ Cz * |z.im| ^ N := by
    have hzrepr : (z.re : ℂ) + (z.im : ℂ) * I = z := by
      apply Complex.ext <;> simp
    simpa only [hzrepr] using hzeta z.re z.im hzre hzim1
  have hzimPow : |z.im| ^ N ≤ (3 * (X : ℝ)) ^ N :=
    pow_le_pow_left₀ (abs_nonneg _) hzimX N
  rw [zetaResidueUnit, Function.update_of_ne hz1, norm_mul]
  calc
    ‖z - 1‖ * ‖riemannZeta z‖ ≤
        (4 * (X : ℝ)) * (Cz * |z.im| ^ N) :=
      mul_le_mul hzsub hzetaBound (norm_nonneg _) (by positivity)
    _ ≤ (4 * (X : ℝ)) * (Cz * (3 * (X : ℝ)) ^ N) := by gcongr
    _ = C * (X : ℝ) ^ Q := by
      rw [mul_pow, pow_succ]
      dsimp only [C, Q]
      ring

theorem one_half_le_norm_zetaResidueUnit_fourteen_fifths
    (tau : ℝ) :
    (1 : ℝ) / 2 ≤
      ‖zetaResidueUnit ((14 / 5 : ℂ) + (tau : ℂ) * I)‖ := by
  let s : ℂ := (14 / 5 : ℂ) + (tau : ℂ) * I
  have hsre : s.re = 14 / 5 := by simp [s]
  have hs1 : s ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [hsre] at hre
    norm_num at hre
  have hzeta0 : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re (by rw [hsre]; norm_num)
  have hinv : ‖(riemannZeta s)⁻¹‖ ≤ 2 :=
    RHTower.norm_inv_riemannZeta_le_of_two_le_re (by rw [hsre]; norm_num)
  have hprod : ‖(riemannZeta s)⁻¹‖ * ‖riemannZeta s‖ = 1 := by
    rw [← norm_mul, inv_mul_cancel₀ hzeta0, norm_one]
  have hzetaLower : (1 : ℝ) / 2 ≤ ‖riemannZeta s‖ := by
    nlinarith [norm_nonneg (riemannZeta s)]
  have hsub : (9 : ℝ) / 5 ≤ ‖s - 1‖ := by
    have hre := Complex.abs_re_le_norm (s - 1)
    have heq : |(s - 1).re| = (9 : ℝ) / 5 := by simp [s]; norm_num
    rwa [heq] at hre
  rw [zetaResidueUnit, Function.update_of_ne hs1, norm_mul]
  nlinarith [norm_nonneg (s - 1)]

theorem exists_zetaResidueUnit_negativeHalf_horizontalTube_zeroMass_le_log :
    ∃ (C : ℝ) (Q : ℕ), 1 ≤ C ∧ ∀ {X : ℕ} {tau : ℝ}, 12 ≤ X →
      (X : ℝ) / 2 ≤ |tau| → |tau| ≤ 2 * (X : ℝ) →
      ((∑ᶠ u, MeromorphicOn.divisor zetaResidueUnit
          (closedBall ((14 / 5 : ℂ) + (tau : ℂ) * I) (15 / 4 : ℝ)) u : ℤ) : ℝ) ≤
        Real.log ((C * (X : ℝ) ^ Q) / ((1 : ℝ) / 2)) /
          Real.log ((4 : ℝ) / (15 / 4 : ℝ)) := by
  obtain ⟨C0, Q, hC0, henv⟩ :=
    exists_norm_zetaResidueUnit_negativeHalf_horizontalTube_le
  let C : ℝ := C0 + 1
  have hC : 1 ≤ C := by dsimp only [C]; linarith
  refine ⟨C, Q, hC, ?_⟩
  intro X tau hX htlow hthigh
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast (show 1 ≤ X by omega)
  have hpow1 : (1 : ℝ) ≤ (X : ℝ) ^ Q := one_le_pow₀ hX1
  have hM1 : (1 : ℝ) ≤ C * (X : ℝ) ^ Q := by nlinarith
  let c0 : ℂ := (14 / 5 : ℂ) + (tau : ℂ) * I
  have hsphere : ∀ z ∈ sphere c0 |(4 : ℝ)|,
      ‖zetaResidueUnit z‖ ≤ C * (X : ℝ) ^ Q := by
    intro z hz
    have hzball : z ∈ closedBall c0 4 := by
      have := sphere_subset_closedBall hz
      norm_num at this ⊢
      exact this
    have h0 := henv hX htlow hthigh z (by simpa only [c0] using hzball)
    exact h0.trans (mul_le_mul_of_nonneg_right
      (by dsimp only [C]; linarith) (by positivity))
  have hana : AnalyticOnNhd ℂ zetaResidueUnit (closedBall c0 |(4 : ℝ)|) :=
    zetaResidueUnit_analyticOnNhd_univ.mono (Set.subset_univ _)
  have hmain := GaloisForLFunctions.HTGeometry.sum_divisor_le_of_bounds
    (c := c0) (r := (15 / 4 : ℝ)) (R := 4)
    (M := C * (X : ℝ) ^ Q) (m := (1 : ℝ) / 2)
    (by norm_num) (by norm_num) hM1 (by norm_num) hana
    (one_half_le_norm_zetaResidueUnit_fourteen_fifths tau) hsphere
  have habs : |(15 / 4 : ℝ)| = (15 / 4 : ℝ) := by norm_num
  rw [habs] at hmain
  simpa only [c0] using hmain

theorem exists_zetaResidueUnit_negativeHalf_horizontalTube_factor_data :
    ∃ (Ce : ℝ) (Qe : ℕ) (Cj : ℝ) (Qj : ℕ), 1 ≤ Ce ∧ 1 ≤ Cj ∧
      ∀ {X : ℕ} {tau : ℝ}, 12 ≤ X →
      (X : ℝ) / 2 ≤ |tau| → |tau| ≤ 2 * (X : ℝ) →
      ∃ (T : Finset ℂ) (m : ℂ → ℕ) (g : ℂ → ℂ),
        AnalyticOnNhd ℂ g Set.univ ∧
        (∀ z ∈ closedBall ((14 / 5 : ℂ) + (tau : ℂ) * I) (15 / 4 : ℝ),
          g z ≠ 0) ∧
        (∀ a ∈ T, a ∈ closedBall
          ((14 / 5 : ℂ) + (tau : ℂ) * I) (15 / 4 : ℝ)) ∧
        (∀ a ∈ T, 1 ≤ m a) ∧
        (∀ z : ℂ, zetaResidueUnit z =
          (∏ a ∈ T, (z - a) ^ (m a)) * g z) ∧
        (((∑ a ∈ T, m a : ℕ) : ℝ) ≤
          inghamDetectorTubeJensenBound Cj Qj X) ∧
        (∀ z ∈ closedBall ((14 / 5 : ℂ) + (tau : ℂ) * I) 4,
          ‖g z‖ ≤ (Ce * (X : ℝ) ^ Qe) /
            ((1 : ℝ) / 4) ^ (∑ a ∈ T, m a)) ∧
        ((1 : ℝ) / 2) / ((15 : ℝ) / 4) ^ (∑ a ∈ T, m a) ≤
          ‖g ((14 / 5 : ℂ) + (tau : ℂ) * I)‖ := by
  obtain ⟨Ce0, Qe, hCe0, henv⟩ :=
    exists_norm_zetaResidueUnit_negativeHalf_horizontalTube_le
  obtain ⟨Cj, Qj, hCj, hcount⟩ :=
    exists_zetaResidueUnit_negativeHalf_horizontalTube_zeroMass_le_log
  let Ce : ℝ := Ce0 + 1
  have hCe : 1 ≤ Ce := by dsimp only [Ce]; linarith
  refine ⟨Ce, Qe, Cj, Qj, hCe, hCj, ?_⟩
  intro X tau hX htlow hthigh
  let c0 : ℂ := (14 / 5 : ℂ) + (tau : ℂ) * I
  have hcenter := one_half_le_norm_zetaResidueUnit_fourteen_fifths tau
  have hnz : ∀ a : ℂ, ¬ ∀ᶠ z in nhds a, zetaResidueUnit z = 0 := by
    intro a hevent
    exact zetaResidueUnit_order_ne_top a (analyticOrderAt_eq_top.mpr hevent)
  have hsphere : ∀ z ∈ sphere c0 4,
      ‖zetaResidueUnit z‖ ≤ Ce * (X : ℝ) ^ Qe := by
    intro z hz
    have h0 := henv hX htlow hthigh z
      (by simpa only [c0] using sphere_subset_closedBall hz)
    exact h0.trans (mul_le_mul_of_nonneg_right
      (by dsimp only [Ce]; linarith) (by positivity))
  have hmass : ((∑ᶠ u, MeromorphicOn.divisor zetaResidueUnit
      (closedBall c0 (15 / 4 : ℝ)) u : ℤ) : ℝ) ≤
      inghamDetectorTubeJensenBound Cj Qj X := by
    simpa only [c0, inghamDetectorTubeJensenBound] using
      hcount hX htlow hthigh
  simpa only [c0] using exists_tube_factor_data
    zetaResidueUnit_analyticOnNhd_univ hnz hsphere hcenter hmass

private theorem routeT_negativeHalf_horizontal_segment_norm_le_seventeen_fifths
    {x T tau : ℝ} (hx : x ∈ Icc (-1 / 2 : ℝ) 2)
    (hT : |T - tau| ≤ 1 / 2) :
    ‖((x : ℂ) + (T : ℂ) * I) -
        ((14 / 5 : ℂ) + (tau : ℂ) * I)‖ ≤ (17 : ℝ) / 5 := by
  let z : ℂ := (x : ℂ) + (T : ℂ) * I
  let c0 : ℂ := (14 / 5 : ℂ) + (tau : ℂ) * I
  have hre : (z - c0).re = x - 14 / 5 := by simp [z, c0]
  have him : (z - c0).im = T - tau := by simp [z, c0]
  have hxabs : |x - 14 / 5| ≤ 33 / 10 := by
    rw [abs_of_nonpos (by linarith [hx.2])]
    linarith [hx.1]
  have hsquares : ‖z - c0‖ ^ (2 : ℕ) = (x - 14 / 5) ^ (2 : ℕ) + (T - tau) ^ (2 : ℕ) := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    ring
  have hxSq : (x - 14 / 5) ^ (2 : ℕ) ≤ (33 / 10 : ℝ) ^ (2 : ℕ) := by
    have h := (sq_le_sq₀ (abs_nonneg (x - 14 / 5))
      (by norm_num : (0 : ℝ) ≤ 33 / 10)).2 hxabs
    simpa only [sq_abs] using h
  have hTSq : (T - tau) ^ (2 : ℕ) ≤ ((1 : ℝ) / 2) ^ (2 : ℕ) := by
    have h := (sq_le_sq₀ (abs_nonneg (T - tau))
      (by norm_num : (0 : ℝ) ≤ 1 / 2)).2 hT
    simpa only [sq_abs] using h
  have hn := norm_nonneg (z - c0)
  dsimp only [z, c0] at hsquares hn ⊢
  nlinarith

theorem zetaResidueUnit_conj_global (z : ℂ) :
    zetaResidueUnit ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (zetaResidueUnit z) := by
  by_cases hz : z = 1
  · subst z
    simp
  · have hzc : (starRingEnd ℂ) z ≠ 1 := by
      intro h
      have := congrArg (starRingEnd ℂ) h
      apply hz
      simpa using this
    rw [zetaResidueUnit, Function.update_of_ne hzc,
      Function.update_of_ne hz, riemannZeta_conj]
    simp

theorem logDeriv_zetaResidueUnit_conj_global (z : ℂ) :
    logDeriv zetaResidueUnit ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (logDeriv zetaResidueUnit z) := by
  have hfun : ((starRingEnd ℂ) ∘ zetaResidueUnit ∘ (starRingEnd ℂ)) =
      zetaResidueUnit := by
    funext w
    simp [Function.comp_def, zetaResidueUnit_conj_global]
  have hderiv := deriv_conj_conj (f := zetaResidueUnit)
  rw [hfun] at hderiv
  have hd : deriv zetaResidueUnit ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (deriv zetaResidueUnit z) := by
    have := congrFun hderiv ((starRingEnd ℂ) z)
    simpa [Function.comp_def] using this
  rw [logDeriv_apply, logDeriv_apply, hd, zetaResidueUnit_conj_global, map_div₀]

theorem zetaLogDerivReg_conj_global (z : ℂ) :
    zetaLogDerivReg ((starRingEnd ℂ) z) =
      (starRingEnd ℂ) (zetaLogDerivReg z) := by
  rw [zetaLogDerivReg, zetaLogDerivReg,
    logDeriv_zetaResidueUnit_conj_global, map_neg]

theorem exists_zetaResidueUnit_negativeHalf_horizontal_logDeriv_control :
    ∃ (Ce : ℝ) (Qe : ℕ) (Cj : ℝ) (Qj : ℕ), 1 ≤ Ce ∧ 1 ≤ Cj ∧
      ∀ {X : ℕ} {tau : ℝ}, 12 ≤ X →
      (X : ℝ) / 2 ≤ |tau| → |tau| ≤ 2 * (X : ℝ) →
      ∃ T ∈ Ioo (tau - 1 / 2) (tau + 1 / 2), ∃ N : ℕ,
        (N : ℝ) ≤ inghamDetectorTubeJensenBound Cj Qj X ∧
        ∀ x ∈ Icc (-1 / 2 : ℝ) 2,
          zetaResidueUnit ((x : ℂ) + (T : ℂ) * I) ≠ 0 ∧
            ‖zetaLogDerivReg ((x : ℂ) + (T : ℂ) * I)‖ ≤
              inghamDetectorHorizontalLogDerivBound Ce Qe Cj Qj X N := by
  classical
  obtain ⟨Ce, Qe, Cj, Qj, hCe, hCj, hfactor⟩ :=
    exists_zetaResidueUnit_negativeHalf_horizontalTube_factor_data
  refine ⟨Ce, Qe, Cj, Qj, hCe, hCj, ?_⟩
  intro X tau hX htlow hthigh
  obtain ⟨Z, m, g, hg, hgfree, hZmem, hmpos, hfac, hNL, hgball, hgcenter⟩ :=
    hfactor hX htlow hthigh
  let L : ℝ := inghamDetectorTubeJensenBound Cj Qj X
  let N : ℕ := ∑ a ∈ Z, m a
  let E : Finset ℝ := Z.image Complex.im
  let delta : ℝ := (4 * (L + 1))⁻¹
  have hL0 : 0 ≤ L := by
    exact inghamDetectorTubeJensenBound_nonneg (Q := Qj) hCj
      (show 1 ≤ X by omega)
  have hZN : Z.card ≤ N := by
    calc
      Z.card = ∑ _a ∈ Z, 1 := by simp
      _ ≤ ∑ a ∈ Z, m a := Finset.sum_le_sum fun a ha => hmpos a ha
      _ = N := rfl
  have hEcard : E.card ≤ Z.card := Finset.card_image_le
  have hEL : (E.card : ℝ) ≤ L := by
    have hEN : E.card ≤ N := hEcard.trans hZN
    exact (Nat.cast_le.mpr hEN).trans (by simpa only [N, L] using hNL)
  have hden : 0 < 4 * (L + 1) := by positivity
  have hdelta : 0 < delta := by dsimp only [delta]; positivity
  have hsmall : 2 * E.card * delta < 1 := by
    have hmul : 2 * (E.card : ℝ) ≤ 2 * L := by linarith
    dsimp only [delta]
    rw [← div_eq_mul_inv, div_lt_iff₀ hden]
    nlinarith
  obtain ⟨T, hT, hsepE⟩ :=
    exists_Ioo_add_one_separated_from_finset E (tau - 1 / 2) delta hdelta.le hsmall
  have hTband : T ∈ Ioo (tau - 1 / 2) (tau + 1 / 2) := by
    constructor <;> linarith [hT.1, hT.2]
  refine ⟨T, hTband, N, ?_, ?_⟩
  · simpa only [N, L] using hNL
  · intro x hx
    let z : ℂ := (x : ℂ) + (T : ℂ) * I
    let c0 : ℂ := (14 / 5 : ℂ) + (tau : ℂ) * I
    have hTtau : |T - tau| ≤ 1 / 2 := by
      rw [abs_le]
      constructor <;> linarith [hT.1, hT.2]
    have hzrho : ‖z - c0‖ ≤ (17 : ℝ) / 5 := by
      simpa only [z, c0] using
        routeT_negativeHalf_horizontal_segment_norm_le_seventeen_fifths hx hTtau
    have hsepZ : ∀ a ∈ Z, delta ≤ ‖z - a‖ := by
      intro a ha
      have haE : a.im ∈ E := Finset.mem_image.mpr ⟨a, ha, rfl⟩
      have hsepIm := hsepE a.im haE
      have himNorm := Complex.abs_im_le_norm (z - a)
      have him : (z - a).im = T - a.im := by simp [z]
      rw [him] at himNorm
      exact hsepIm.trans himNorm
    have hzK : z ∈ closedBall c0 (15 / 4 : ℝ) := by
      rw [mem_closedBall, dist_eq_norm]
      exact hzrho.trans (by norm_num)
    have hGne : zetaResidueUnit z ≠ 0 :=
      ne_zero_of_factor_data (hfac z)
        (hgfree z (by simpa only [c0] using hzK)) hdelta hsepZ
    have hpoint := norm_logDeriv_le_of_factor_data
      (f := zetaResidueUnit) (g := g) (c := c0) (z := z)
      (T := Z) (m := m) (Mf := Ce * (X : ℝ) ^ Qe)
      (m0 := (1 : ℝ) / 2) (d := delta)
      hg (by simpa only [c0] using hgfree) hfac
      (by simpa only [c0] using hgball) (by norm_num)
      (by simpa only [c0] using hgcenter) hdelta hsepZ hzrho
    refine ⟨by simpa only [z] using hGne, ?_⟩
    rw [zetaLogDerivReg, norm_neg]
    simpa only [z, N, L, delta, inghamDetectorHorizontalLogDerivBound] using hpoint

theorem exists_routeT_negativeHalf_two_horizontal_edges_polylog :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ {X : ℕ}, 12 ≤ X →
      ∃ T ∈ Ioo ((X : ℝ) - 3) ((X : ℝ) - 2),
        (∀ x ∈ Icc (-1 / 2 : ℝ) 2,
          zetaResidueUnit ((x : ℂ) + (T : ℂ) * I) ≠ 0 ∧
          ‖zetaLogDerivReg ((x : ℂ) + (T : ℂ) * I)‖ ≤
            K * (1 + Real.log X) ^ (2 : ℕ)) ∧
        (∀ x ∈ Icc (-1 / 2 : ℝ) 2,
          zetaResidueUnit ((x : ℂ) + ((-T : ℝ) : ℂ) * I) ≠ 0 ∧
          ‖zetaLogDerivReg ((x : ℂ) + ((-T : ℝ) : ℂ) * I)‖ ≤
            K * (1 + Real.log X) ^ (2 : ℕ)) := by
  obtain ⟨Ce, Qe, Cj, Qj, hCe, hCj, hcontrol⟩ :=
    exists_zetaResidueUnit_negativeHalf_horizontal_logDeriv_control
  let C : ℝ := inghamDetectorHorizontalPolylogConstant Ce Qe Cj Qj
  let K : ℝ := |C|
  have hK : 0 ≤ K := abs_nonneg C
  refine ⟨K, hK, ?_⟩
  intro X hX
  have hXR : (12 : ℝ) ≤ X := by exact_mod_cast hX
  let tau : ℝ := (X : ℝ) - 5 / 2
  have htauabs : |tau| = (X : ℝ) - 5 / 2 := by
    rw [abs_of_nonneg (by dsimp only [tau]; linarith)]
  have htaulo : (X : ℝ) / 2 ≤ |tau| := by rw [htauabs]; linarith
  have htauhi : |tau| ≤ 2 * (X : ℝ) := by rw [htauabs]; linarith
  obtain ⟨T, hT, N, hNL, hbound⟩ := hcontrol hX htaulo htauhi
  have hT' : T ∈ Ioo ((X : ℝ) - 3) ((X : ℝ) - 2) := by
    dsimp only [tau] at hT
    constructor <;> linarith [hT.1, hT.2]
  have hpoly := inghamDetectorHorizontalLogDerivBound_le_polylog
    (Ce := Ce) (Cj := Cj) (Qe := Qe) (Qj := Qj) (X := X) (N := N)
    hCe hCj (show 1 ≤ X by omega) hNL
  have hCabs : C ≤ K := by dsimp only [K]; exact le_abs_self C
  have hsq : 0 ≤ (1 + Real.log X) ^ (2 : ℕ) := sq_nonneg _
  have hraw : ∀ x ∈ Icc (-1 / 2 : ℝ) 2,
      zetaResidueUnit ((x : ℂ) + (T : ℂ) * I) ≠ 0 ∧
      ‖zetaLogDerivReg ((x : ℂ) + (T : ℂ) * I)‖ ≤
        K * (1 + Real.log X) ^ (2 : ℕ) := by
    intro x hx
    obtain ⟨hne, hb⟩ := hbound x hx
    refine ⟨hne, hb.trans (hpoly.trans ?_)⟩
    simpa only [C] using mul_le_mul_of_nonneg_right hCabs hsq
  refine ⟨T, hT', hraw, ?_⟩
  intro x hx
  obtain ⟨htopne, htopbound⟩ := hraw x hx
  let z : ℂ := (x : ℂ) + (T : ℂ) * I
  have hconj : (starRingEnd ℂ) z =
      (x : ℂ) + ((-T : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [z]
  constructor
  · rw [← hconj, zetaResidueUnit_conj_global]
    exact (map_ne_zero (starRingEnd ℂ)).2 htopne
  · rw [← hconj, zetaLogDerivReg_conj_global, RCLike.norm_conj]
    exact htopbound

end

end RHTower.Sieve
