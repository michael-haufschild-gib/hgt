import GaloisForLFunctions.RHTower.DyadicVonMangoldtSqrtMass
import GaloisForLFunctions.RHTower.DyadicVonMangoldtSqrtAsymptotic
import GaloisForLFunctions.HTGeometry.MassBesselDeepTimeCarrier
import GaloisForLFunctions.HTGeometry.MassBesselShellEstimate

/-!
# The mass-Bessel dyadic aperture

A dyadic aperture weights the massive radiation carrier of each prime power of a dyadic block by
its von Mangoldt coefficient over the square root of the level.  At a deep spectral point every
carrier of the block equals the common deep-time profile up to a small relative error, and the
coefficients are non-negative, so the aperture cannot cancel: its modulus is at least a fixed
fraction of the profile times the weighted prime mass of the block.
-/

open Filter ArithmeticFunction HTGeometry
open scoped Topology BigOperators

namespace RHTower

noncomputable section

/-- The finite mass-Bessel dyadic aperture. -/
def massBesselDyadicAperture (a σ X u : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
    (((vonMangoldt n : ℝ) / Real.sqrt n : ℝ) : ℂ) *
      massBesselCarrier a (apertureSpectralPoint σ u) (Real.log n)

theorem dyadicSqrtVonMangoldtMass_nonneg (X : ℝ) : 0 ≤ dyadicSqrtVonMangoldtMass X := by
  rw [dyadicSqrtVonMangoldtMass]
  refine Finset.sum_nonneg fun n _ => ?_
  positivity

/-- The aperture, centred at the common deep-time profile. -/
theorem massBesselDyadicAperture_sub (a σ X u : ℝ) :
    massBesselDyadicAperture a σ X u
        - massBesselLeading a (apertureSpectralPoint σ u) * ((dyadicSqrtVonMangoldtMass X : ℝ) : ℂ)
      = ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
          (((vonMangoldt n : ℝ) / Real.sqrt n : ℝ) : ℂ) *
            (massBesselCarrier a (apertureSpectralPoint σ u) (Real.log n)
              - massBesselLeading a (apertureSpectralPoint σ u)) := by
  rw [massBesselDyadicAperture, dyadicSqrtVonMangoldtMass, Complex.ofReal_sum,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  ring

/-- **The dyadic aperture cannot cancel.**  When every carrier of the block agrees with the common
profile to within half of it, plus a quarter of it in absolute terms, the aperture retains a
quarter of the profile times the weighted prime mass. -/
theorem norm_massBesselDyadicAperture_ge {a σ X u M : ℝ} (ha : 0 < a) (hσ : 0 < σ)
    (hu : 1 ≤ u) (hσu : σ ≤ u)
    (hlog : ∀ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, Real.log n ^ 2 ≤ M ^ 2)
    (h1 : 2 * M ^ 2 ≤ u) (h2 : 4 * M ^ 2 ≤ σ * u) (h3 : 2 * a * M ^ 2 ≤ u)
    (hR : (12 + 2 * a) * (M ^ 2 / u) ≤ 1 / 2)
    (hQ : 8 * Real.exp (-(a * σ / 2)) * Real.sqrt (2 * Real.pi / (a * σ)) / u
        ≤ ‖massBesselLeading a (apertureSpectralPoint σ u)‖ / 4) :
    ‖massBesselLeading a (apertureSpectralPoint σ u)‖ * dyadicSqrtVonMangoldtMass X / 4
      ≤ ‖massBesselDyadicAperture a σ X u‖ := by
  classical
  set L : ℂ := massBesselLeading a (apertureSpectralPoint σ u) with hLdef
  set S : ℝ := dyadicSqrtVonMangoldtMass X with hSdef
  have hS0 : 0 ≤ S := dyadicSqrtVonMangoldtMass_nonneg X
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  -- every carrier of the block is close to the profile
  have hterm : ∀ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
      ‖massBesselCarrier a (apertureSpectralPoint σ u) (Real.log n) - L‖ ≤ ‖L‖ / 2 + ‖L‖ / 4 := by
    intro n hn
    have hx := hlog n hn
    have hx2 : 2 * Real.log n ^ 2 ≤ u := by nlinarith [hx, h1]
    have hxσ : 4 * Real.log n ^ 2 ≤ σ * u := by nlinarith [hx, h2]
    have hax : 2 * a * Real.log n ^ 2 ≤ u := by nlinarith [hx, h3, ha]
    have hshell := norm_massBesselCarrier_sub_leading_le_shell (a := a) (σ := σ) (u := u)
      (x := Real.log n) ha hσ hu hσu hx2 hxσ hax
    rw [← hLdef] at hshell
    refine le_trans hshell ?_
    refine add_le_add ?_ hQ
    have hmono : (12 + 2 * a) * (Real.log n ^ 2 / u) ≤ (12 + 2 * a) * (M ^ 2 / u) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact div_le_div_of_nonneg_right hx hu0.le
    calc (12 + 2 * a) * (Real.log n ^ 2 / u) * ‖L‖
        ≤ (12 + 2 * a) * (M ^ 2 / u) * ‖L‖ :=
          mul_le_mul_of_nonneg_right hmono (norm_nonneg _)
      _ ≤ (1 / 2) * ‖L‖ := mul_le_mul_of_nonneg_right hR (norm_nonneg _)
      _ = ‖L‖ / 2 := by ring
  -- the centred aperture is small
  have hcentre : ‖massBesselDyadicAperture a σ X u - L * ((S : ℝ) : ℂ)‖ ≤ S * (‖L‖ / 2 + ‖L‖ / 4) := by
    rw [hLdef, hSdef, massBesselDyadicAperture_sub]
    refine le_trans (norm_sum_le _ _) ?_
    rw [dyadicSqrtVonMangoldtMass, Finset.sum_mul]
    refine Finset.sum_le_sum fun n hn => ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← hLdef]
    exact hterm n hn
  -- the reverse triangle inequality
  have hprod : ‖L * ((S : ℝ) : ℂ)‖ = ‖L‖ * S := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hS0]
  have hrev : ‖L * ((S : ℝ) : ℂ)‖ - ‖massBesselDyadicAperture a σ X u - L * ((S : ℝ) : ℂ)‖
      ≤ ‖massBesselDyadicAperture a σ X u‖ := by
    have h := norm_sub_le (massBesselDyadicAperture a σ X u)
      (massBesselDyadicAperture a σ X u - L * ((S : ℝ) : ℂ))
    have hval : massBesselDyadicAperture a σ X u
        - (massBesselDyadicAperture a σ X u - L * ((S : ℝ) : ℂ)) = L * ((S : ℝ) : ℂ) := by ring
    rw [hval] at h
    linarith
  rw [hprod] at hrev
  have hfinal : ‖L‖ * S - S * (‖L‖ / 2 + ‖L‖ / 4) = ‖L‖ * S / 4 := by ring
  linarith [hrev, hcentre, hfinal]

/-! ## The deep-time aperture diverges -/

theorem tendsto_sqrt_div_log_sq_atTop :
    Tendsto (fun X : ℝ => Real.sqrt X / Real.log X ^ 2) atTop atTop := by
  have h0 := Real.tendsto_pow_log_div_mul_add_atTop 1 0 2 one_ne_zero
  have h1 : Tendsto (fun y : ℝ => Real.log y ^ 2 / y) atTop (nhds 0) := by
    refine h0.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y _
    ring_nf
  have hpos : ∀ᶠ y : ℝ in atTop, Real.log y ^ 2 / y ∈ Set.Ioi (0 : ℝ) := by
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with y hy
    have hy0 : (0 : ℝ) < y := by linarith
    have hlog : 0 < Real.log y := Real.log_pos (by linarith)
    exact div_pos (by positivity) hy0
  have h2 : Tendsto (fun y : ℝ => Real.log y ^ 2 / y) atTop (nhdsWithin 0 (Set.Ioi 0)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h1 hpos
  have h3 : Tendsto (fun y : ℝ => (Real.log y ^ 2 / y)⁻¹) atTop atTop :=
    h2.inv_tendsto_nhdsGT_zero
  have h4 : Tendsto (fun y : ℝ => y / Real.log y ^ 2) atTop atTop := by
    refine h3.congr' ?_
    filter_upwards [eventually_gt_atTop (2 : ℝ)] with y hy
    have hy0 : (0 : ℝ) < y := by linarith
    have hlog : 0 < Real.log y := Real.log_pos (by linarith)
    rw [inv_div]
  have h5 : Tendsto (fun X : ℝ => Real.sqrt X / Real.log (Real.sqrt X) ^ 2) atTop atTop :=
    h4.comp Real.tendsto_sqrt_atTop
  have h6 : Tendsto (fun X : ℝ => 4 * (Real.sqrt X / Real.log X ^ 2)) atTop atTop := by
    refine h5.congr' ?_
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have hlogsqrt : Real.log (Real.sqrt X) = Real.log X / 2 := Real.log_sqrt hX.le
    simp only [hlogsqrt]
    ring
  simpa using h6.atTop_div_const (by norm_num : (0:ℝ) < 4)

/-- The deep-time profile constant of the aperture. -/
def apertureProfileConst (a σ : ℝ) : ℝ :=
  Real.sqrt (2 * Real.pi * a) * Real.exp (-(a * σ)) / Real.sqrt 2

/-- The absolute Schläfli budget of the aperture. -/
def apertureRemainderConst (a σ : ℝ) : ℝ :=
  8 * Real.exp (-(a * σ / 2)) * Real.sqrt (2 * Real.pi / (a * σ))

theorem apertureProfileConst_pos {a σ : ℝ} (ha : 0 < a) : 0 < apertureProfileConst a σ := by
  rw [apertureProfileConst]
  have : (0 : ℝ) < Real.sqrt (2 * Real.pi * a) :=
    Real.sqrt_pos.2 (by positivity)
  positivity

theorem apertureRemainderConst_nonneg (a σ : ℝ) : 0 ≤ apertureRemainderConst a σ := by
  rw [apertureRemainderConst]
  positivity

/-- The deep-time profile of the aperture is at least the profile constant over the square of the
logarithm. -/
theorem apertureProfileConst_div_le {a σ L : ℝ} (ha : 0 < a) (hσ : 0 < σ) (hL : 1 ≤ L)
    (hσL : σ ≤ L ^ 4) :
    apertureProfileConst a σ / L ^ 2
      ≤ ‖massBesselLeading a (apertureSpectralPoint σ (L ^ 4))‖ := by
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL
  have hre : 0 < (apertureSpectralPoint σ (L ^ 4)).re := by
    rw [spectralPoint_re]; exact hσ
  rw [norm_massBesselLeading a hre, spectralPoint_re]
  have hnorm : ‖apertureSpectralPoint σ (L ^ 4)‖ ≤ 2 * L ^ 4 :=
    norm_spectralPoint_le hσ hσL
  have hsqrt : Real.sqrt ‖apertureSpectralPoint σ (L ^ 4)‖ ≤ Real.sqrt 2 * L ^ 2 := by
    have h1 : Real.sqrt ‖apertureSpectralPoint σ (L ^ 4)‖ ≤ Real.sqrt (2 * L ^ 4) :=
      Real.sqrt_le_sqrt hnorm
    have h2 : Real.sqrt (2 * L ^ 4) = Real.sqrt 2 * L ^ 2 := by
      rw [Real.sqrt_mul (by norm_num)]
      congr 1
      rw [show L ^ 4 = (L ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
    linarith [h1, h2]
  have hsqrtpos : (0 : ℝ) < Real.sqrt ‖apertureSpectralPoint σ (L ^ 4)‖ := by
    refine Real.sqrt_pos.2 ?_
    have := le_norm_spectralPoint σ (L ^ 4)
    have hL4 : (0 : ℝ) < L ^ 4 := by positivity
    linarith
  rw [apertureProfileConst, div_le_div_iff₀ (by positivity) hsqrtpos]
  have hnum : (0 : ℝ) ≤ Real.sqrt (2 * Real.pi * a) * Real.exp (-(a * σ)) := by positivity
  have hs2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  rw [div_mul_eq_mul_div, div_le_iff₀ hs2]
  nlinarith [hsqrt, hnum, hsqrtpos, hs2]

/-- **The mass-Bessel dyadic aperture grows like `√X/(log X)²` along the deep-time ray.** -/
theorem exists_massBesselDyadicAperture_lower (a σ : ℝ) (ha : 0 < a) (hσ : 0 < σ) :
    ∃ c > 0, ∀ᶠ X : ℝ in atTop,
      c * (Real.sqrt X / Real.log X ^ 2)
        ≤ ‖massBesselDyadicAperture a σ X (Real.log X ^ 4)‖ := by
  classical
  refine ⟨apertureProfileConst a σ / 12,
    div_pos (apertureProfileConst_pos ha) (by norm_num), ?_⟩
  · have hlogtop : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
    set T2 : ℝ := Real.sqrt (16 / σ) with hT2
    set T3 : ℝ := Real.sqrt (8 * a) with hT3
    set T4 : ℝ := Real.sqrt (8 * (12 + 2 * a)) with hT4
    set T5 : ℝ := Real.sqrt (4 * apertureRemainderConst a σ / apertureProfileConst a σ) with hT5
    filter_upwards [eventually_ge_atTop (2 : ℝ),
      hlogtop.eventually (eventually_ge_atTop (3 : ℝ)),
      hlogtop.eventually (eventually_ge_atTop σ),
      hlogtop.eventually (eventually_ge_atTop T2),
      hlogtop.eventually (eventually_ge_atTop T3),
      hlogtop.eventually (eventually_ge_atTop T4),
      hlogtop.eventually (eventually_ge_atTop T5),
      eventually_dyadicSqrtVonMangoldtMass_ge] with
      X hX2 hL3 hLσ hLT2 hLT3 hLT4 hLT5 hS
    set L : ℝ := Real.log X with hLdef
    have hL1 : (1 : ℝ) ≤ L := by linarith
    have hL0 : (0 : ℝ) < L := by linarith
    have hL2ge : (1 : ℝ) ≤ L ^ 2 := one_le_pow₀ hL1
    have hL3ge : (1 : ℝ) ≤ L ^ 3 := one_le_pow₀ hL1
    have hL4 : (1 : ℝ) ≤ L ^ 4 := one_le_pow₀ hL1
    have hLle4 : L ≤ L ^ 4 := by nlinarith [hL3ge, hL0]
    have hsqT : ∀ T : ℝ, 0 ≤ T → Real.sqrt T ≤ L → T ≤ L ^ 2 := by
      intro T hT hle
      nlinarith [Real.sq_sqrt hT, Real.sqrt_nonneg T, hle]
    have hLσ4 : σ ≤ L ^ 4 := le_trans hLσ hLle4
    have hL2 : (8 : ℝ) ≤ L ^ 2 := by nlinarith [hL3]
    have h2' : (16 : ℝ) / σ ≤ L ^ 2 := hsqT _ (by positivity) hLT2
    have h3' : (8 : ℝ) * a ≤ L ^ 2 := hsqT _ (by positivity) hLT3
    have h4' : (8 : ℝ) * (12 + 2 * a) ≤ L ^ 2 := hsqT _ (by positivity) hLT4
    have h5' : 4 * apertureRemainderConst a σ / apertureProfileConst a σ ≤ L ^ 2 :=
      hsqT _ (div_nonneg (by linarith [apertureRemainderConst_nonneg a σ])
        (apertureProfileConst_pos ha).le) hLT5
    -- the shell hypothesis
    have hlog : ∀ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, Real.log n ^ 2 ≤ (2 * L) ^ 2 := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      have hX0 : (0 : ℝ) < X := by linarith
      have hn1 : 1 ≤ n := by
        have : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (1:ℝ) ≤ X))
        omega
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hnle : (n : ℝ) ≤ 2 * X := by
        have hfl := Nat.floor_le (by linarith : (0:ℝ) ≤ 2 * X)
        have hcast : (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by exact_mod_cast hn.2
        linarith
      have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
      have hlog2 : Real.log 2 ≤ L := by
        rw [hLdef]
        exact Real.log_le_log (by norm_num) hX2
      have hlognle : Real.log n ≤ 2 * L := by
        have h := Real.log_le_log hnpos hnle
        rw [Real.log_mul (by norm_num) (by linarith)] at h
        linarith
      nlinarith [hlogn0, hlognle, hL0]
    -- the shell conditions
    have hcond1 : 2 * (2 * L) ^ 2 ≤ L ^ 4 := by nlinarith [hL2, hL0]
    have hcond2 : 4 * (2 * L) ^ 2 ≤ σ * L ^ 4 := by
      have : 16 ≤ σ * L ^ 2 := by
        rw [div_le_iff₀ hσ] at h2'
        linarith
      nlinarith [this, hL2, hL0]
    have hcond3 : 2 * a * (2 * L) ^ 2 ≤ L ^ 4 := by nlinarith [h3', hL0, ha]
    have hcondR : (12 + 2 * a) * ((2 * L) ^ 2 / L ^ 4) ≤ 1 / 2 := by
      have hval : (2 * L) ^ 2 / L ^ 4 = 4 / L ^ 2 := by
        field_simp
        ring
      rw [hval, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by norm_num)]
      linarith [h4']
    have hprofile := apertureProfileConst_div_le (a := a) (σ := σ) (L := L) ha hσ hL1 hLσ4
    have hcondQ : apertureRemainderConst a σ / L ^ 4
        ≤ ‖massBesselLeading a (apertureSpectralPoint σ (L ^ 4))‖ / 4 := by
      refine le_trans ?_ (by linarith [hprofile] :
        apertureProfileConst a σ / L ^ 2 / 4
          ≤ ‖massBesselLeading a (apertureSpectralPoint σ (L ^ 4))‖ / 4)
      rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
      have hP : 0 < apertureProfileConst a σ := apertureProfileConst_pos ha
      rw [div_le_iff₀ hP] at h5'
      nlinarith [h5', hL0, apertureRemainderConst_nonneg a σ]
    have hmain := norm_massBesselDyadicAperture_ge (a := a) (σ := σ) (X := X) (u := L ^ 4)
      (M := 2 * L) ha hσ hL4 hLσ4 hlog hcond1 hcond2 hcond3 hcondR
      (by rw [apertureRemainderConst] at hcondQ; exact hcondQ)
    refine le_trans ?_ hmain
    have hPpos : 0 < apertureProfileConst a σ := apertureProfileConst_pos ha
    have hsqX : 0 ≤ Real.sqrt X := Real.sqrt_nonneg X
    have hstep : apertureProfileConst a σ / 12 * (Real.sqrt X / L ^ 2)
        ≤ (apertureProfileConst a σ / L ^ 2) * (Real.sqrt X / 3) / 4 := by
      rw [div_mul_eq_mul_div, div_le_div_iff₀ (by norm_num) (by norm_num)]
      have : apertureProfileConst a σ / L ^ 2 * (Real.sqrt X / 3) * 12
          = apertureProfileConst a σ * (Real.sqrt X / L ^ 2) * 4 := by
        field_simp
        ring
      linarith [this]
    refine le_trans hstep ?_
    have hmono : (apertureProfileConst a σ / L ^ 2) * (Real.sqrt X / 3) / 4
        ≤ ‖massBesselLeading a (apertureSpectralPoint σ (L ^ 4))‖ *
            dyadicSqrtVonMangoldtMass X / 4 := by
      refine div_le_div_of_nonneg_right ?_ (by norm_num) |>.trans_eq rfl
      refine mul_le_mul hprofile hS (by positivity) (norm_nonneg _)
    exact hmono

/-- **The finite mass-Bessel prime apertures are not uniformly bounded.** -/
theorem tendsto_norm_massBesselDyadicAperture_atTop (a σ : ℝ) (ha : 0 < a) (hσ : 0 < σ) :
    Tendsto (fun X : ℝ => ‖massBesselDyadicAperture a σ X (Real.log X ^ 4)‖) atTop atTop := by
  obtain ⟨c, hc, hbound⟩ := exists_massBesselDyadicAperture_lower a σ ha hσ
  have hgrow : Tendsto (fun X : ℝ => c * (Real.sqrt X / Real.log X ^ 2)) atTop atTop :=
    tendsto_sqrt_div_log_sq_atTop.const_mul_atTop hc
  exact tendsto_atTop_mono' atTop hbound hgrow

/-! ## The asymptotic form -/

/-- The aperture differs from the profile times the weighted prime mass by the shell error. -/
theorem norm_massBesselDyadicAperture_sub_le {a σ X u M : ℝ} (ha : 0 < a) (hσ : 0 < σ)
    (hu : 1 ≤ u) (hσu : σ ≤ u)
    (hlog : ∀ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, Real.log n ^ 2 ≤ M ^ 2)
    (h1 : 2 * M ^ 2 ≤ u) (h2 : 4 * M ^ 2 ≤ σ * u) (h3 : 2 * a * M ^ 2 ≤ u) :
    ‖massBesselDyadicAperture a σ X u
        - massBesselLeading a (apertureSpectralPoint σ u) *
          ((dyadicSqrtVonMangoldtMass X : ℝ) : ℂ)‖
      ≤ dyadicSqrtVonMangoldtMass X *
          ((12 + 2 * a) * (M ^ 2 / u) * ‖massBesselLeading a (apertureSpectralPoint σ u)‖
            + apertureRemainderConst a σ / u) := by
  classical
  set L : ℂ := massBesselLeading a (apertureSpectralPoint σ u) with hLdef
  have hu0 : (0 : ℝ) < u := lt_of_lt_of_le zero_lt_one hu
  have hterm : ∀ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊,
      ‖massBesselCarrier a (apertureSpectralPoint σ u) (Real.log n) - L‖
        ≤ (12 + 2 * a) * (M ^ 2 / u) * ‖L‖ + apertureRemainderConst a σ / u := by
    intro n hn
    have hx := hlog n hn
    have hx2 : 2 * Real.log n ^ 2 ≤ u := by nlinarith [hx, h1]
    have hxσ : 4 * Real.log n ^ 2 ≤ σ * u := by nlinarith [hx, h2]
    have hax : 2 * a * Real.log n ^ 2 ≤ u := by nlinarith [hx, h3, ha]
    have hshell := norm_massBesselCarrier_sub_leading_le_shell (a := a) (σ := σ) (u := u)
      (x := Real.log n) ha hσ hu hσu hx2 hxσ hax
    rw [← hLdef] at hshell
    refine le_trans hshell (add_le_add ?_ (le_of_eq (by rw [apertureRemainderConst])))
    have hmono : (12 + 2 * a) * (Real.log n ^ 2 / u) ≤ (12 + 2 * a) * (M ^ 2 / u) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact div_le_div_of_nonneg_right hx hu0.le
    exact mul_le_mul_of_nonneg_right hmono (norm_nonneg _)
  rw [hLdef, massBesselDyadicAperture_sub]
  refine le_trans (norm_sum_le _ _) ?_
  rw [dyadicSqrtVonMangoldtMass, Finset.sum_mul]
  refine Finset.sum_le_sum fun n hn => ?_
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  rw [← hLdef]
  exact hterm n hn

theorem tendsto_inv_log_sq :
    Tendsto (fun X : ℝ => 1 / Real.log X ^ 2) atTop (nhds 0) := by
  have hlog : Tendsto (fun X : ℝ => Real.log X ^ 2) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ Real.tendsto_log_atTop
    filter_upwards [Real.tendsto_log_atTop.eventually (eventually_ge_atTop (1 : ℝ))] with X hX
    nlinarith [hX]
  have h := hlog.inv_tendsto_atTop
  refine h.congr fun X => ?_
  simp [one_div]

/-- **The card's boxed asymptotic.**  Along the deep-time ray the aperture is the deep-time
profile times `2(√2−1)√X`, with relative error tending to zero. -/
theorem tendsto_massBesselDyadicAperture_asymptotic (a σ : ℝ) (ha : 0 < a) (hσ : 0 < σ) :
    Tendsto (fun X : ℝ =>
        ‖massBesselDyadicAperture a σ X (Real.log X ^ 4)
            - massBesselLeading a (apertureSpectralPoint σ (Real.log X ^ 4))
              * ((2 * (Real.sqrt 2 - 1) * Real.sqrt X : ℝ) : ℂ)‖
          / (‖massBesselLeading a (apertureSpectralPoint σ (Real.log X ^ 4))‖ * Real.sqrt X))
      atTop (nhds 0) := by
  classical
  set c : ℝ := 2 * (Real.sqrt 2 - 1) with hcdef
  set g : ℝ → ℝ := fun X =>
    (dyadicSqrtVonMangoldtMass X / Real.sqrt X) *
        ((12 + 2 * a) * (4 * (1 / Real.log X ^ 2))
          + apertureRemainderConst a σ / apertureProfileConst a σ * (1 / Real.log X ^ 2))
      + |dyadicSqrtVonMangoldtMass X / Real.sqrt X - c| with hgdef
  have hSlim := tendsto_dyadicSqrtVonMangoldtMass_div_sqrt
  have hinv := tendsto_inv_log_sq
  have hglim : Tendsto g atTop (nhds 0) := by
    have h1 : Tendsto (fun X : ℝ => (12 + 2 * a) * (4 * (1 / Real.log X ^ 2))
        + apertureRemainderConst a σ / apertureProfileConst a σ * (1 / Real.log X ^ 2))
        atTop (nhds 0) := by
      have ha1 := (hinv.const_mul (4 : ℝ)).const_mul (12 + 2 * a)
      have ha2 := hinv.const_mul (apertureRemainderConst a σ / apertureProfileConst a σ)
      simpa using ha1.add ha2
    have h2 : Tendsto (fun X : ℝ => |dyadicSqrtVonMangoldtMass X / Real.sqrt X - c|)
        atTop (nhds 0) := by
      have hzero : 2 * (Real.sqrt 2 - 1) - c = 0 := by rw [hcdef]; ring
      have hsub := hSlim.sub_const c
      rw [hzero] at hsub
      simpa using hsub.abs
    have := (hSlim.mul h1).add h2
    simpa [hgdef] using this
  refine squeeze_zero' ?_ ?_ hglim
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with X hX
    positivity
  · have hlogtop : Tendsto Real.log atTop atTop := Real.tendsto_log_atTop
    filter_upwards [eventually_ge_atTop (2 : ℝ),
      hlogtop.eventually (eventually_ge_atTop (3 : ℝ)),
      hlogtop.eventually (eventually_ge_atTop σ),
      hlogtop.eventually (eventually_ge_atTop (Real.sqrt (16 / σ))),
      hlogtop.eventually (eventually_ge_atTop (Real.sqrt (8 * a)))] with
      X hX2 hL3 hLσ hLT2 hLT3
    set Lg : ℝ := Real.log X with hLgdef
    have hL1 : (1 : ℝ) ≤ Lg := by linarith
    have hL0 : (0 : ℝ) < Lg := by linarith
    have hL3ge : (1 : ℝ) ≤ Lg ^ 3 := one_le_pow₀ hL1
    have hu : (1 : ℝ) ≤ Lg ^ 4 := one_le_pow₀ hL1
    have hLle4 : Lg ≤ Lg ^ 4 := by nlinarith [hL3ge, hL0]
    have hσu : σ ≤ Lg ^ 4 := le_trans hLσ hLle4
    have hsqT : ∀ T : ℝ, 0 ≤ T → Real.sqrt T ≤ Lg → T ≤ Lg ^ 2 := by
      intro T hT hle
      nlinarith [Real.sq_sqrt hT, Real.sqrt_nonneg T, hle]
    have hL2 : (8 : ℝ) ≤ Lg ^ 2 := by nlinarith [hL3]
    have h2' : (16 : ℝ) / σ ≤ Lg ^ 2 := hsqT _ (by positivity) hLT2
    have h3' : (8 : ℝ) * a ≤ Lg ^ 2 := hsqT _ (by positivity) hLT3
    have hX0 : (0 : ℝ) < X := by linarith
    have hXs : (0 : ℝ) < Real.sqrt X := Real.sqrt_pos.2 hX0
    have hlog : ∀ n ∈ Finset.Ioc ⌊X⌋₊ ⌊2 * X⌋₊, Real.log n ^ 2 ≤ (2 * Lg) ^ 2 := by
      intro n hn
      rw [Finset.mem_Ioc] at hn
      have hn1 : 1 ≤ n := by
        have : 1 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast (by linarith : (1:ℝ) ≤ X))
        omega
      have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
      have hnle : (n : ℝ) ≤ 2 * X := by
        have hfl := Nat.floor_le (by linarith : (0:ℝ) ≤ 2 * X)
        have hcast : (n : ℝ) ≤ (⌊2 * X⌋₊ : ℝ) := by exact_mod_cast hn.2
        linarith
      have hlogn0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
      have hlog2 : Real.log 2 ≤ Lg := by
        rw [hLgdef]
        exact Real.log_le_log (by norm_num) hX2
      have hlognle : Real.log n ≤ 2 * Lg := by
        have h := Real.log_le_log hnpos hnle
        rw [Real.log_mul (by norm_num) (by linarith)] at h
        linarith
      nlinarith [hlogn0, hlognle, hL0]
    have hcond1 : 2 * (2 * Lg) ^ 2 ≤ Lg ^ 4 := by nlinarith [hL2, hL0]
    have hcond2 : 4 * (2 * Lg) ^ 2 ≤ σ * Lg ^ 4 := by
      have hkey : 16 ≤ σ * Lg ^ 2 := by
        rw [div_le_iff₀ hσ] at h2'
        linarith
      nlinarith [hkey, hL2, hL0]
    have hcond3 : 2 * a * (2 * Lg) ^ 2 ≤ Lg ^ 4 := by nlinarith [h3', hL0, ha]
    have hupper := norm_massBesselDyadicAperture_sub_le (a := a) (σ := σ) (X := X)
      (u := Lg ^ 4) (M := 2 * Lg) ha hσ hu hσu hlog hcond1 hcond2 hcond3
    have hprofile := apertureProfileConst_div_le (a := a) (σ := σ) (L := Lg) ha hσ hL1 hσu
    have hPpos : 0 < apertureProfileConst a σ := apertureProfileConst_pos ha
    have hLnorm : 0 < ‖massBesselLeading a (apertureSpectralPoint σ (Lg ^ 4))‖ :=
      lt_of_lt_of_le (by positivity) hprofile
    have hS0 : 0 ≤ dyadicSqrtVonMangoldtMass X := dyadicSqrtVonMangoldtMass_nonneg X
    -- split the numerator
    have hsplit : ‖massBesselDyadicAperture a σ X (Lg ^ 4)
        - massBesselLeading a (apertureSpectralPoint σ (Lg ^ 4)) * ((c * Real.sqrt X : ℝ) : ℂ)‖
        ≤ ‖massBesselDyadicAperture a σ X (Lg ^ 4)
            - massBesselLeading a (apertureSpectralPoint σ (Lg ^ 4)) *
              ((dyadicSqrtVonMangoldtMass X : ℝ) : ℂ)‖
          + ‖massBesselLeading a (apertureSpectralPoint σ (Lg ^ 4))‖ *
              |dyadicSqrtVonMangoldtMass X - c * Real.sqrt X| := by
      have hval : massBesselDyadicAperture a σ X (Lg ^ 4)
          - massBesselLeading a (apertureSpectralPoint σ (Lg ^ 4)) * ((c * Real.sqrt X : ℝ) : ℂ)
          = (massBesselDyadicAperture a σ X (Lg ^ 4)
              - massBesselLeading a (apertureSpectralPoint σ (Lg ^ 4)) *
                ((dyadicSqrtVonMangoldtMass X : ℝ) : ℂ))
            + massBesselLeading a (apertureSpectralPoint σ (Lg ^ 4)) *
                (((dyadicSqrtVonMangoldtMass X - c * Real.sqrt X : ℝ)) : ℂ) := by
        push_cast
        ring
      rw [hval]
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rw [div_le_iff₀ (by positivity)]
    refine le_trans hsplit ?_
    have hbound1 : ‖massBesselDyadicAperture a σ X (Lg ^ 4)
        - massBesselLeading a (apertureSpectralPoint σ (Lg ^ 4)) *
          ((dyadicSqrtVonMangoldtMass X : ℝ) : ℂ)‖
        ≤ dyadicSqrtVonMangoldtMass X *
            ((12 + 2 * a) * ((2 * Lg) ^ 2 / Lg ^ 4) *
              ‖massBesselLeading a (apertureSpectralPoint σ (Lg ^ 4))‖
              + apertureRemainderConst a σ / Lg ^ 4) := hupper
    have hcoef : (2 * Lg) ^ 2 / Lg ^ 4 = 4 * (1 / Lg ^ 2) := by
      field_simp
      ring
    rw [hcoef] at hbound1
    have hQle : apertureRemainderConst a σ / Lg ^ 4
        ≤ apertureRemainderConst a σ / apertureProfileConst a σ * (1 / Lg ^ 2) *
            ‖massBesselLeading a (apertureSpectralPoint σ (Lg ^ 4))‖ := by
      have hstep : apertureProfileConst a σ / Lg ^ 2
          ≤ ‖massBesselLeading a (apertureSpectralPoint σ (Lg ^ 4))‖ := hprofile
      have hQ0 : 0 ≤ apertureRemainderConst a σ := apertureRemainderConst_nonneg a σ
      have hmul : apertureRemainderConst a σ / apertureProfileConst a σ * (1 / Lg ^ 2) *
          (apertureProfileConst a σ / Lg ^ 2) = apertureRemainderConst a σ / Lg ^ 4 := by
        field_simp
      calc apertureRemainderConst a σ / Lg ^ 4
          = apertureRemainderConst a σ / apertureProfileConst a σ * (1 / Lg ^ 2) *
              (apertureProfileConst a σ / Lg ^ 2) := hmul.symm
        _ ≤ apertureRemainderConst a σ / apertureProfileConst a σ * (1 / Lg ^ 2) *
              ‖massBesselLeading a (apertureSpectralPoint σ (Lg ^ 4))‖ :=
            mul_le_mul_of_nonneg_left hstep (by positivity)
    have hnormS : |dyadicSqrtVonMangoldtMass X - c * Real.sqrt X|
        = |dyadicSqrtVonMangoldtMass X / Real.sqrt X - c| * Real.sqrt X := by
      have hval : dyadicSqrtVonMangoldtMass X - c * Real.sqrt X
          = (dyadicSqrtVonMangoldtMass X / Real.sqrt X - c) * Real.sqrt X := by
        field_simp
      rw [hval, abs_mul, abs_of_pos hXs]
    rw [hnormS]
    have hSX : dyadicSqrtVonMangoldtMass X
        = dyadicSqrtVonMangoldtMass X / Real.sqrt X * Real.sqrt X := by
      field_simp
    have hfinal : dyadicSqrtVonMangoldtMass X *
          ((12 + 2 * a) * (4 * (1 / Lg ^ 2)) *
            ‖massBesselLeading a (apertureSpectralPoint σ (Lg ^ 4))‖
            + apertureRemainderConst a σ / apertureProfileConst a σ * (1 / Lg ^ 2) *
              ‖massBesselLeading a (apertureSpectralPoint σ (Lg ^ 4))‖)
        + ‖massBesselLeading a (apertureSpectralPoint σ (Lg ^ 4))‖ *
            (|dyadicSqrtVonMangoldtMass X / Real.sqrt X - c| * Real.sqrt X)
        = g X * (‖massBesselLeading a (apertureSpectralPoint σ (Lg ^ 4))‖ * Real.sqrt X) := by
      rw [hgdef, hLgdef]
      nth_rewrite 1 [hSX]
      ring
    refine le_trans (add_le_add ?_ le_rfl) (le_of_eq hfinal)
    refine le_trans hbound1 ?_
    refine mul_le_mul_of_nonneg_left ?_ hS0
    exact add_le_add le_rfl hQle

end

end RHTower
