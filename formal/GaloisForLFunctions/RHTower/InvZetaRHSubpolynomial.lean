import GaloisForLFunctions.RHTower.MobiusLaplaceCriterionFrontier
import GaloisForLFunctions.RHTower.DeningerZetaLowerBound
import GaloisForLFunctions.RHTower.Sieve.ZetaStripGrowth
import GaloisForLFunctions.RHTower.Sieve.ZetaRealBound
import GaloisForLFunctions.RHTower.Sieve.InvZetaLowBox
import GaloisForLFunctions.RHTower.GammaDampedVerticalBound
import GaloisForLFunctions.HTGeometry.ThreeCircles

/-!
# Reciprocal zeta has subpolynomial growth under RH

The RH zero-free theorem already makes the regular reciprocal `invZeta` holomorphic on every
closed strip strictly right of `Re s = 1/2`.  The missing quantitative input is supplied here.

At large height, three-circles is applied directly to `riemannZeta` on discs wholly avoiding its
pole.  The small disc lies in `Re s > 2`, where zeta is uniformly bounded above and below; the
large disc stays right of `Re s = 1/2`, where RH makes zeta zero-free and the fractional-part
continuation gives polynomial growth.  Interpolation therefore gives a lower bound whose
reciprocal grows more slowly than every power of the height.  Bounded height is absorbed by
compactness of the regular reciprocal, including its removable zero at `s = 1`.
-/

open Complex Metric
open GaloisForLFunctions.HTGeometry

namespace RHTower

open Sieve

/-- **RH three-circles lower bound for zeta.**  On every line a fixed positive distance right of
the critical line, and outside a fixed bounded-height box, zeta is bounded below by the
exponential of a strict sublinear power of the logarithmic height. -/
theorem exists_three_circles_zeta_lower_bound_of_rh (hRH : RiemannHypothesis)
    {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ B K θ : ℝ, 0 < B ∧ 0 < K ∧ 0 ≤ θ ∧ θ < 1 ∧ ∀ s : ℂ,
      1 / 2 + δ ≤ s.re → 6 ≤ |s.im| →
        (1 : ℝ) / 4 * Real.exp (-(B * (K * (1 + Real.log (2 + |s.im|))) ^ θ))
          ≤ ‖riemannZeta s‖ := by
  set a : ℝ := 3 with ha
  set r₃ : ℝ := a - (1 / 2 + δ / 2) with hr₃
  set R : ℝ := a - (1 / 2 + δ / 4) with hR
  have hr₃big : (2 : ℝ) < r₃ := by rw [hr₃, ha]; linarith
  have hRbig : r₃ < R := by rw [hr₃, hR]; linarith
  have hR0 : (0 : ℝ) ≤ R := by linarith
  have hR3 : R < 3 := by rw [hR, ha]; linarith
  have hr₁ρ : (1 : ℝ) / 4 < 1 / 2 := by norm_num
  have hρR : (1 : ℝ) / 2 ≤ R := by linarith
  have hr₁r₃ : (1 : ℝ) / 4 < r₃ := by linarith
  set E : ℝ := 3 * (1 + 4 / δ) with hE
  have hE0 : 0 < E := by rw [hE]; positivity
  have h4E : (1 : ℝ) ≤ 4 * E := by
    have hfrac : 0 ≤ 4 / δ := by positivity
    rw [hE]
    nlinarith
  have hdisc : ∀ t : ℝ, 6 ≤ |t| → ∀ z : ℂ,
      ‖z - ((a : ℂ) + (t : ℝ) * I)‖ ≤ R →
        ‖riemannZeta z‖ ≤ E * (2 + |t|) := by
    intro t ht z hz
    set c : ℂ := (a : ℂ) + (t : ℝ) * I with hc
    have hcre : c.re = a := by rw [hc]; simp
    have hcim : c.im = t := by rw [hc]; simp
    have hreabs := Complex.abs_re_le_norm (z - c)
    rw [Complex.sub_re, hcre] at hreabs
    have hrelo : a - R ≤ z.re := by
      have := (abs_le.mp (hreabs.trans hz)).1
      linarith
    have hzre : 0 < z.re := by
      have har : a - R = 1 / 2 + δ / 4 := by rw [hR]; ring
      rw [har] at hrelo
      linarith
    have hcNorm := Complex.norm_le_abs_re_add_abs_im c
    rw [hcre, hcim, abs_of_nonneg (by rw [ha]; norm_num)] at hcNorm
    have hnormz : ‖z‖ ≤ 3 * (2 + |t|) := by
      have htri : ‖z‖ ≤ ‖z - c‖ + ‖c‖ := by
        simpa only [sub_add_cancel] using norm_add_le (z - c) c
      linarith [abs_nonneg t]
    have htC : |t| ≤ ‖c - 1‖ := by
      have him := Complex.abs_im_le_norm (c - 1)
      rw [Complex.sub_im, hcim] at him
      simpa using him
    have hc1 : ‖c - 1‖ ≤ ‖c - z‖ + ‖z - 1‖ := by
      have hsplit : c - 1 = (c - z) + (z - 1) := by ring
      rw [hsplit]
      exact norm_add_le _ _
    have hcz : ‖c - z‖ = ‖z - c‖ := norm_sub_rev c z
    rw [hcz] at hc1
    have hden1 : 1 ≤ ‖z - 1‖ := by linarith
    have hz1 : z ≠ 1 := by
      intro h
      subst z
      norm_num at hden1
    have hreInv : 1 / z.re ≤ 4 / δ := by
      apply (div_le_div_iff₀ hzre hδ).2
      nlinarith
    have hfirst : ‖z‖ / ‖z - 1‖ ≤ ‖z‖ :=
      div_le_self (norm_nonneg z) hden1
    have hsecond : ‖z‖ / z.re ≤ ‖z‖ * (4 / δ) := by
      rw [div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left (by simpa only [one_div] using hreInv) (norm_nonneg z)
    have hzeta := Sieve.norm_riemannZeta_strip_le hzre hz1
    calc
      ‖riemannZeta z‖ ≤ ‖z‖ / ‖z - 1‖ + ‖z‖ / z.re := hzeta
      _ ≤ ‖z‖ + ‖z‖ * (4 / δ) := add_le_add hfirst hsecond
      _ = ‖z‖ * (1 + 4 / δ) := by ring
      _ ≤ (3 * (2 + |t|)) * (1 + 4 / δ) :=
        mul_le_mul_of_nonneg_right hnormz (by positivity)
      _ = E * (2 + |t|) := by rw [hE]; ring
  set B : ℝ :=
    2 * (Real.log (3 / (1 / 4 : ℝ)) + 1) * (1 / 4) / (1 / 2 - 1 / 4) with hB
  have hlog12 : 0 ≤ Real.log (3 / (1 / 4 : ℝ)) := Real.log_nonneg (by norm_num)
  have hB1 : (1 : ℝ) ≤ B := by
    rw [hB]
    have hsimp :
        2 * (Real.log (3 / (1 / 4 : ℝ)) + 1) * (1 / 4) / (1 / 2 - 1 / 4)
          = 2 * (Real.log (3 / (1 / 4 : ℝ)) + 1) := by ring
    rw [hsimp]
    linarith
  have hB0 : 0 < B := by linarith
  set K : ℝ := 8 * r₃ / δ * (Real.log (4 * E) + 2) with hK
  have hlogE : 0 ≤ Real.log (4 * E) := Real.log_nonneg h4E
  have hfac : (8 : ℝ) ≤ 8 * r₃ / δ := by
    rw [le_div_iff₀ hδ]
    nlinarith
  have hK0 : 0 < K := by rw [hK]; positivity
  have hK1 : (1 : ℝ) ≤ K := by rw [hK]; nlinarith
  set θ : ℝ :=
    (Real.log (a - 1 / 2 - δ) - Real.log (1 / 4)) /
      (Real.log r₃ - Real.log (1 / 4)) with hθ
  have hgap : (1 : ℝ) / 4 < a - 1 / 2 - δ := by rw [ha]; linarith
  have hgap2 : a - 1 / 2 - δ < r₃ := by rw [hr₃]; linarith
  have hden : 0 < Real.log r₃ - Real.log (1 / 4) := by
    have := Real.log_lt_log (by norm_num : (0 : ℝ) < 1 / 4) hr₁r₃
    linarith
  have hnum : 0 ≤ Real.log (a - 1 / 2 - δ) - Real.log (1 / 4) := by
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 4) hgap.le
    linarith
  have hθ0 : 0 ≤ θ := by rw [hθ]; exact div_nonneg hnum hden.le
  clear_value θ K B E R r₃ a
  have hθ1 : θ < 1 := by
    rw [hθ, div_lt_one hden]
    have := Real.log_lt_log (by linarith : (0 : ℝ) < a - 1 / 2 - δ) hgap2
    linarith
  refine ⟨B, K, θ, hB0, hK0, hθ0, hθ1, fun s hs ht => ?_⟩
  set t : ℝ := s.im with htdef
  have hbase : (1 : ℝ) ≤ 2 + |t| := by linarith [abs_nonneg t]
  have hlogbase : 0 ≤ Real.log (2 + |t|) := Real.log_nonneg hbase
  have hone : (1 : ℝ) ≤ 1 + Real.log (2 + |t|) := by linarith
  have hKpos : 0 ≤ K * (1 + Real.log (2 + |t|)) :=
    mul_nonneg hK0.le (by linarith)
  have hexpnn : 0 ≤ B * (K * (1 + Real.log (2 + |t|))) ^ θ :=
    mul_nonneg hB0.le (Real.rpow_nonneg hKpos _)
  rcases le_or_gt s.re (a - 1 / 4) with hleft | hright
  · set c : ℂ := (a : ℂ) + (t : ℝ) * I with hc
    have hcre : c.re = a := by rw [hc]; simp
    have hcim : c.im = t := by rw [hc]; simp
    have hsc : s - c = (((s.re - a : ℝ)) : ℂ) := by
      apply Complex.ext <;> simp [hc, htdef]
    have hscnorm : ‖s - c‖ = a - s.re := by
      rw [hsc, Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]
      ring
    have hz1 : (1 : ℝ) / 4 ≤ ‖s - c‖ := by rw [hscnorm]; linarith
    have hz3 : ‖s - c‖ ≤ r₃ := by rw [hscnorm, hr₃]; linarith
    have hballre : ∀ z ∈ ball c R, 1 / 2 < z.re := by
      intro z hz
      have hd : ‖z - c‖ < R := by rwa [mem_ball, dist_eq_norm] at hz
      have hre := Complex.abs_re_le_norm (z - c)
      rw [Complex.sub_re, hcre] at hre
      have h2 := abs_lt.mp (lt_of_le_of_lt hre hd)
      have hAR : a - R = 1 / 2 + δ / 4 := by rw [hR]; ring
      linarith
    have hpole : ∀ z ∈ ball c R, z ≠ 1 := by
      intro z hz hzone
      subst z
      have hd : ‖(1 : ℂ) - c‖ < R := by rwa [mem_ball, dist_eq_norm] at hz
      have him := Complex.abs_im_le_norm ((1 : ℂ) - c)
      rw [Complex.sub_im, hcim] at him
      simp only [Complex.one_im, zero_sub, abs_neg] at him
      have ht' : 6 ≤ |t| := by simpa [t] using ht
      linarith
    have hne : ∀ z ∈ ball c R, riemannZeta z ≠ 0 := by
      intro z hz
      exact (zetaResidueUnit_ne_zero_iff (hpole z hz)).1
        (zetaResidueUnit_ne_zero_of_riemannHypothesis hRH
          (mem_rightHalf.mpr (hballre z hz)))
    have hf : DifferentiableOn ℂ riemannZeta (ball c R) := by
      intro z hz
      exact (differentiableAt_riemannZeta (hpole z hz)).differentiableWithinAt
    have hMi : ∀ z ∈ ball c (1 / 2), ‖riemannZeta z‖ ≤ 3 := by
      intro z hz
      have hd : ‖z - c‖ < 1 / 2 := by rwa [mem_ball, dist_eq_norm] at hz
      have hre := Complex.abs_re_le_norm (z - c)
      rw [Complex.sub_re, hcre] at hre
      have h2 := abs_lt.mp (lt_of_le_of_lt hre hd)
      have hzeta := Sieve.norm_riemannZeta_le (s := z) (by rw [ha] at h2; linarith)
      have hinv : 1 / (z.re - 1) ≤ 1 := by
        rw [div_le_one (by rw [ha] at h2; linarith)]
        rw [ha] at h2
        linarith
      linarith
    have hmc : (1 : ℝ) / 4 ≤ ‖riemannZeta c‖ := by
      apply norm_riemannZeta_ge_of_two_le_re
      rw [hcre, ha]
      norm_num
    have hM : ∀ z ∈ ball c R, ‖riemannZeta z‖ ≤ E * (2 + |t|) := by
      intro z hz
      have hd : ‖z - c‖ < R := by rwa [mem_ball, dist_eq_norm] at hz
      exact hdisc t (by simpa [t] using ht) z hd.le
    have hmain := norm_lower_bound_of_two_radii
      (by norm_num : (0 : ℝ) < 1 / 4) hr₁ρ hρR hr₁r₃ hRbig hf hne hMi
      (by norm_num : (0 : ℝ) < 1 / 4) hmc hM
      (by norm_num : (0 : ℝ) < 1 / 4) hmc hz1 hz3
    set w : ℝ :=
      (Real.log ‖s - c‖ - Real.log (1 / 4)) /
        (Real.log r₃ - Real.log (1 / 4)) with hw
    have hw0 : 0 ≤ w := by
      rw [hw]
      have hnum' := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 4) hz1
      exact div_nonneg (by linarith) hden.le
    have hwθ : w ≤ θ := by
      rw [hw, hθ, div_le_div_iff_of_pos_right hden]
      have hle : ‖s - c‖ ≤ a - 1 / 2 - δ := by rw [hscnorm]; linarith
      have h2 := Real.log_le_log (by linarith : (0 : ℝ) < ‖s - c‖) hle
      linarith
    have hMm : E * (2 + |t|) / (1 / 4) = 4 * E * (2 + |t|) := by ring
    have hlogsplit : Real.log (4 * E * (2 + |t|)) =
        Real.log (4 * E) + Real.log (2 + |t|) := by
      rw [Real.log_mul (by positivity) (by positivity)]
    have hr₃0 : 0 < r₃ := by linarith
    have hRr : R - r₃ = δ / 4 := by rw [hR, hr₃]; ring
    have hRr0 : 0 < R - r₃ := by rw [hRr]; linarith
    have hfac0 : 0 < 8 * r₃ / δ := by positivity
    have houter :
        2 * (Real.log (E * (2 + |t|) / (1 / 4)) + 1) * r₃ / (R - r₃)
          ≤ K * (1 + Real.log (2 + |t|)) := by
      rw [hMm, hlogsplit, hRr, hK]
      have hkey : Real.log (4 * E) + Real.log (2 + |t|) + 1
          ≤ (Real.log (4 * E) + 2) * (1 + Real.log (2 + |t|)) := by
        have hexpand :
            (Real.log (4 * E) + 2) * (1 + Real.log (2 + |t|)) =
              Real.log (4 * E) + Real.log (2 + |t|) + 1 +
                (Real.log (4 * E) * Real.log (2 + |t|) +
                  Real.log (2 + |t|) + 1) := by ring
        rw [hexpand]
        have hprodlog : 0 ≤ Real.log (4 * E) * Real.log (2 + |t|) :=
          mul_nonneg hlogE hlogbase
        exact le_add_of_nonneg_right (by linarith only [hprodlog, hlogbase])
      calc
        2 * (Real.log (4 * E) + Real.log (2 + |t|) + 1) * r₃ / (δ / 4)
            = 8 * r₃ / δ *
                (Real.log (4 * E) + Real.log (2 + |t|) + 1) := by
                  field_simp
                  ring
        _ ≤ 8 * r₃ / δ *
              ((Real.log (4 * E) + 2) * (1 + Real.log (2 + |t|))) :=
                mul_le_mul_of_nonneg_left hkey hfac0.le
        _ = 8 * r₃ / δ * (Real.log (4 * E) + 2) *
              (1 + Real.log (2 + |t|)) :=
                (mul_assoc _ _ _).symm
    have houter1 : 1 ≤ K * (1 + Real.log (2 + |t|)) := by
      calc
        (1 : ℝ) ≤ K := hK1
        _ = K * 1 := (mul_one K).symm
        _ ≤ K * (1 + Real.log (2 + |t|)) :=
          mul_le_mul_of_nonneg_left hone hK0.le
    have hlogM : 0 ≤ Real.log (E * (2 + |t|) / (1 / 4)) := by
      apply Real.log_nonneg
      calc
        (1 : ℝ) ≤ 4 * E * (2 + |t|) :=
          le_trans h4E (by
            have hmul0 : 0 ≤ 4 * E * ((2 + |t|) - 1) :=
              mul_nonneg (by positivity) (by linarith only [hbase])
            nlinarith only [hmul0])
        _ = E * (2 + |t|) / (1 / 4) := hMm.symm
    have hbase0 :
        0 ≤ 2 * (Real.log (E * (2 + |t|) / (1 / 4)) + 1) * r₃ / (R - r₃) := by
      exact div_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (by linarith only [hlogM])) hr₃0.le)
        hRr0.le
    have hpow1 : B ^ (1 - w) ≤ B := by
      have hexp : 1 - w ≤ (1 : ℝ) := sub_le_one.mpr hw0
      simpa only [Real.rpow_one] using
        (Real.rpow_le_rpow_of_exponent_le hB1 hexp)
    have hpow3 :
        (2 * (Real.log (E * (2 + |t|) / (1 / 4)) + 1) * r₃ / (R - r₃)) ^ w
          ≤ (K * (1 + Real.log (2 + |t|))) ^ θ :=
      le_trans (Real.rpow_le_rpow hbase0 houter hw0)
        (Real.rpow_le_rpow_of_exponent_le houter1 hwθ)
    have hprod :
        B ^ (1 - w) *
            (2 * (Real.log (E * (2 + |t|) / (1 / 4)) + 1) * r₃ /
              (R - r₃)) ^ w
          ≤ B * (K * (1 + Real.log (2 + |t|))) ^ θ :=
      mul_le_mul hpow1 hpow3 (Real.rpow_nonneg hbase0 _) hB0.le
    rw [← hB] at hmain
    calc
      (1 : ℝ) / 4 * Real.exp (-(B * (K * (1 + Real.log (2 + |t|))) ^ θ))
          ≤ 1 / 4 * Real.exp (-(B ^ (1 - w) *
              (2 * (Real.log (E * (2 + |t|) / (1 / 4)) + 1) * r₃ /
                (R - r₃)) ^ w)) :=
            mul_le_mul_of_nonneg_left
              (Real.exp_le_exp.mpr (by linarith only [hprod])) (by norm_num)
      _ ≤ ‖riemannZeta c‖ * Real.exp (-(B ^ (1 - w) *
              (2 * (Real.log (E * (2 + |t|) / (1 / 4)) + 1) * r₃ /
                (R - r₃)) ^ w)) :=
            mul_le_mul_of_nonneg_right hmc (Real.exp_pos _).le
      _ ≤ ‖riemannZeta s‖ := hmain
  · have hge : 2 ≤ s.re := by rw [ha] at hright; linarith
    have hval := norm_riemannZeta_ge_of_two_le_re hge
    calc
      (1 : ℝ) / 4 * Real.exp (-(B * (K * (1 + Real.log (2 + |t|))) ^ θ))
          ≤ 1 / 4 * 1 := by
            refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
            exact Real.exp_le_one_iff.mpr (by linarith)
      _ = 1 / 4 := by ring
      _ ≤ ‖riemannZeta s‖ := hval

/-- **RH subpolynomial lower bound for zeta.** -/
theorem exists_zeta_lower_bound_subpolynomial_of_rh (hRH : RiemannHypothesis)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ s : ℂ, 1 / 2 + δ ≤ s.re → 6 ≤ |s.im| →
      κ * (2 + |s.im|) ^ (-ε) ≤ ‖riemannZeta s‖ := by
  obtain ⟨B, K, θ, hB, hK, hθ0, hθ1, hbd⟩ :=
    exists_three_circles_zeta_lower_bound_of_rh hRH hδ hδ1
  have hbasepos : ∀ u : ℝ, 2 ≤ u → 0 < K * (1 + Real.log u) :=
    fun u hu => mul_pos hK (by linarith [Real.log_nonneg (by linarith : (1 : ℝ) ≤ u)])
  have hcont : ContinuousOn (fun u : ℝ => Real.exp (ε * Real.log u -
      B * (K * (1 + Real.log u)) ^ θ)) (Set.Ici 2) := by
    refine Real.continuous_exp.comp_continuousOn (ContinuousOn.sub ?_ ?_)
    · refine continuousOn_const.mul (Real.continuousOn_log.mono ?_)
      intro u hu
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      have hu2 : (2 : ℝ) ≤ u := hu
      linarith
    · refine continuousOn_const.mul (ContinuousOn.rpow_const ?_ ?_)
      · refine continuousOn_const.mul (continuousOn_const.add (Real.continuousOn_log.mono ?_))
        intro u hu
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        have hu2 : (2 : ℝ) ≤ u := hu
        linarith
      · exact fun u hu => Or.inl (ne_of_gt (hbasepos u hu))
  have hlim : Filter.Tendsto (fun u : ℝ => Real.exp (ε * Real.log u -
      B * (K * (1 + Real.log u)) ^ θ)) Filter.atTop Filter.atTop := by
    refine Real.tendsto_exp_atTop.comp ?_
    have hinner : Filter.Tendsto (fun L : ℝ => ε * L - B * (K * (1 + L)) ^ θ)
        Filter.atTop Filter.atTop := by
      have hhalf : Filter.Tendsto (fun L : ℝ => ε / 2 * L) Filter.atTop Filter.atTop :=
        Filter.Tendsto.const_mul_atTop (by linarith) Filter.tendsto_id
      refine Filter.tendsto_atTop_mono' _ ?_ hhalf
      have hc := eventually_const_mul_rpow_le (c := B * (K ^ θ * 2 ^ θ)) hθ1
        (show (0 : ℝ) < ε / 2 by linarith)
      filter_upwards [hc, Filter.eventually_ge_atTop (1 : ℝ)] with L hL hL1
      have hsplit : (K * (1 + L)) ^ θ = K ^ θ * (1 + L) ^ θ :=
        Real.mul_rpow hK.le (by linarith)
      have h2L : (1 + L) ^ θ ≤ (2 * L) ^ θ :=
        Real.rpow_le_rpow (by linarith) (by linarith) hθ0
      have h2L' : (2 * L) ^ θ = 2 ^ θ * L ^ θ :=
        Real.mul_rpow (by norm_num) (by linarith)
      have hKθ : 0 ≤ K ^ θ := Real.rpow_nonneg hK.le _
      have hchain : B * (K * (1 + L)) ^ θ ≤ B * (K ^ θ * 2 ^ θ) * L ^ θ := by
        rw [hsplit]
        have hmid : K ^ θ * (1 + L) ^ θ ≤ K ^ θ * (2 ^ θ * L ^ θ) := by
          rw [← h2L']
          exact mul_le_mul_of_nonneg_left h2L hKθ
        nlinarith [hB.le, hmid]
      linarith
    exact hinner.comp Real.tendsto_log_atTop
  obtain ⟨κ, hκ0, hκ⟩ := exists_pos_lower_bound_of_tendsto_atTop hcont
    (fun u _ => Real.exp_pos _) hlim
  refine ⟨κ / 4, by positivity, fun s hs ht => ?_⟩
  have h1 := hbd s hs ht
  set u : ℝ := 2 + |s.im| with hu
  have hu2 : 2 ≤ u := by rw [hu]; linarith [abs_nonneg s.im]
  have hupos : 0 < u := by linarith
  have hκu := hκ u hu2
  have hrpow : u ^ (-ε) = Real.exp (-(ε * Real.log u)) := by
    rw [Real.rpow_def_of_pos hupos]
    ring_nf
  rw [hrpow]
  have hstep : κ * Real.exp (-(ε * Real.log u))
      ≤ Real.exp (-(B * (K * (1 + Real.log u)) ^ θ)) := by
    calc
      κ * Real.exp (-(ε * Real.log u))
          ≤ Real.exp (ε * Real.log u - B * (K * (1 + Real.log u)) ^ θ) *
              Real.exp (-(ε * Real.log u)) :=
            mul_le_mul_of_nonneg_right hκu (Real.exp_pos _).le
      _ = Real.exp (-(B * (K * (1 + Real.log u)) ^ θ)) := by
            rw [← Real.exp_add]
            ring_nf
  calc
    κ / 4 * Real.exp (-(ε * Real.log u))
        = 1 / 4 * (κ * Real.exp (-(ε * Real.log u))) := by ring
    _ ≤ 1 / 4 * Real.exp (-(B * (K * (1 + Real.log u)) ^ θ)) :=
      mul_le_mul_of_nonneg_left hstep (by norm_num)
    _ ≤ ‖riemannZeta s‖ := h1

/-- **The reciprocal-zeta shift datum under RH.**  On every strip strictly right of the critical
line, the regular reciprocal is holomorphic and grows slower than every positive power of height.
This is the exact analytic datum needed by shifted smoothed Perron. -/
theorem exists_invZeta_shift_data_of_rh (hRH : RiemannHypothesis)
    {δ ε : ℝ} (hδ : 0 < δ) (hδ1 : δ < 1) (hε : 0 < ε) (d : ℝ)
    (hd : 1 / 2 + δ ≤ d) :
    ∃ Kb : ℝ, 0 ≤ Kb ∧
      DifferentiableOn ℂ invZeta (verticalStrip (1 / 2 + δ) d) ∧
      ∀ s ∈ verticalStrip (1 / 2 + δ) d,
        ‖invZeta s‖ ≤ Kb * (2 + |s.im|) ^ ε := by
  obtain ⟨κ, hκ0, hκ⟩ :=
    exists_zeta_lower_bound_subpolynomial_of_rh hRH hδ hδ1 hε
  let K₀ : Set ℂ := Set.Icc (1 / 2 + δ) 2 ×ℂ Set.Icc (-6 : ℝ) 6
  have hKcompact : IsCompact K₀ := isCompact_reProdIm_Icc _ _ _ _
  have hKnonempty : K₀.Nonempty := by
    refine ⟨(2 : ℂ), ?_, ?_⟩
    · constructor
      · norm_num
        linarith
      · norm_num
    · constructor <;> norm_num
  have hKdiff : DifferentiableOn ℂ invZeta K₀ := by
    intro s hs
    have hsright : s ∈ rightHalf := by
      rw [mem_rightHalf]
      have hslo : 1 / 2 + δ ≤ s.re := hs.1.1
      linarith
    exact (differentiableAt_invZeta
      (zetaResidueUnit_ne_zero_of_riemannHypothesis hRH hsright)).differentiableWithinAt
  obtain ⟨z₀, hz₀, hmax⟩ :=
    hKcompact.exists_isMaxOn hKnonempty (hKdiff.continuousOn.norm)
  let D : ℝ := ‖invZeta z₀‖
  let Kb : ℝ := max (max κ⁻¹ D) 2
  have hKb : 0 ≤ Kb := by dsimp [Kb]; positivity
  have hdiff : DifferentiableOn ℂ invZeta (verticalStrip (1 / 2 + δ) d) := by
    intro s hs
    have hsright : s ∈ rightHalf := by
      rw [mem_rightHalf]
      linarith [hs.1]
    exact (differentiableAt_invZeta
      (zetaResidueUnit_ne_zero_of_riemannHypothesis hRH hsright)).differentiableWithinAt
  refine ⟨Kb, hKb, hdiff, fun s hs => ?_⟩
  have hbase : 1 ≤ (2 + |s.im|) ^ ε := by
    exact Real.one_le_rpow (by linarith [abs_nonneg s.im]) hε.le
  rcases le_or_gt 2 s.re with hre | hre
  · have hs1 : s ≠ 1 := by
      intro h
      subst s
      norm_num at hre
    have hfar := norm_inv_riemannZeta_le_of_two_le_re hre
    rw [norm_invZeta_eq hs1]
    calc
      ‖(riemannZeta s)⁻¹‖ ≤ 2 := hfar
      _ ≤ Kb := le_max_right _ _
      _ ≤ Kb * (2 + |s.im|) ^ ε := by
        nlinarith [hKb, hbase]
  · rcases le_or_gt 6 |s.im| with him | him
    · have hs1 : s ≠ 1 := by
        intro h
        subst s
        norm_num at him
      have hlow := hκ s hs.1 him
      have hpowpos : 0 < (2 + |s.im|) ^ (-ε) := by positivity
      have hzpos : 0 < ‖riemannZeta s‖ := by
        have : 0 < κ * (2 + |s.im|) ^ (-ε) := by positivity
        linarith
      rw [norm_invZeta_eq hs1, norm_inv]
      have hinv : (‖riemannZeta s‖)⁻¹
          ≤ (κ * (2 + |s.im|) ^ (-ε))⁻¹ :=
        (inv_le_inv₀ hzpos (by positivity)).mpr hlow
      calc
        (‖riemannZeta s‖)⁻¹
            ≤ (κ * (2 + |s.im|) ^ (-ε))⁻¹ := hinv
        _ = κ⁻¹ * (2 + |s.im|) ^ ε := by
          rw [mul_inv, Real.rpow_neg (by positivity), inv_inv]
        _ ≤ Kb * (2 + |s.im|) ^ ε := by
          exact mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _))
            (Real.rpow_nonneg (by positivity) _)
    · have hsK : s ∈ K₀ := by
        refine ⟨⟨hs.1, hre.le⟩, ?_⟩
        exact abs_le.mp him.le
      have hD : ‖invZeta s‖ ≤ D := hmax hsK
      calc
        ‖invZeta s‖ ≤ D := hD
        _ ≤ Kb := le_trans (le_max_right _ _) (le_max_left _ _)
        _ ≤ Kb * (2 + |s.im|) ^ ε := by
          nlinarith [hKb, hbase]

end RHTower
