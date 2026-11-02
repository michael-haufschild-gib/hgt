import GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision.BesselSzegoCertificate

/-!
# The Szegő cepstrum is a positive Bessel transform of the window energy

On a stage-`n` corridor window, the cepstral coefficients `S_k = ∑ m_z m_w (-ρ v_{z-w})^k` of the
exact outer multiplier of the collision loop are

`S_k = (-ρ)^k (c/2) ∫₀^∞ e^{-t/2} (I_{k-1}(ct) - I_{k+1}(ct)) |𝒵(t)|² dt`,

where `𝒵(t) = ∑ m_z e^{t(z - 1/2)}` is the window exponential sum (`cepstralCoeff_eq_bessel`).
Since `I_{k-1} ≥ I_{k+1}` on `[0, ∞)`, the cepstrum alternates in sign: `(-1)^k S_k ≥ 0`
(`neg_one_pow_mul_cepstralCoeff_nonneg`). The order-`K` Szegő certificate therefore depends on
the window only through the energy `t ↦ |𝒵(t)|²` (`besselSzegoCertificate`), and it certifies
sectoriality of the collision loop on every corridor window once `2D²(1-η)^{K+1}/η < π/2`.

Every analytic certificate is the exact multiplier times a Carathéodory factor
(`re_div_exactSzegoMultiplier_pos`): no multiplier carries less information than the cepstrum.

Proof: insert the Laplace identity `R(x) = ∫₀^∞ e^{-xt}|𝒵(t)|² dt` for the pair resolvent into
the resolvent form of the cepstrum, exchange the circle and Laplace integrals (the integrand is
dominated by `C e^{-ηt}`), and evaluate the Fourier coefficients of `e^{-tJ_n}` as Bessel
functions.
-/

set_option autoImplicit false

open Complex MeasureTheory Set Filter
open scoped BigOperators Topology

noncomputable section

namespace GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision

namespace ReflectedWindow

variable {W : ReflectedWindow} {n : ℕ}

/-- Circle integral of the mode weight against `e^{-t J_n}`: a difference of two Bessel
coefficients. -/
theorem integral_cepstralModeWeight_mul_exp (n : ℕ) {k : ℕ} (hk : 1 ≤ k) (t : ℝ) :
    ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), cepstralModeWeight n k θ *
        cexp (-(zhukovskyLoop n (HTGeometry.circleExp θ) * t)) =
      ((2 * Real.pi * (zhukovskyFocal n * zhukovskyRadius n / 2) * (-zhukovskyRadius n) ^ (k - 1) *
        (Real.exp (-(t / 2)) * (besselI (k - 1) (zhukovskyFocal n * t) -
          besselI (k + 1) (zhukovskyFocal n * t))) : ℝ) : ℂ) := by
  have hρ0 : (zhukovskyRadius n : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (zhukovskyRadius_pos n).ne'
  have hJcont : Continuous fun θ : ℝ => zhukovskyLoop n (HTGeometry.circleExp θ) :=
    (zhukovskyLoop n).continuous.comp HTGeometry.continuous_circleExp
  set X : ℝ → ℂ := fun θ => cexp (-(zhukovskyLoop n (HTGeometry.circleExp θ) * t)) with hX
  have hXc : Continuous X := by rw [hX]; fun_prop
  have hpt : ∀ θ : ℝ, cepstralModeWeight n k θ * X θ =
      ((zhukovskyFocal n * zhukovskyRadius n / 2 : ℝ) : ℂ) *
        (cexp (((-((k - 1 : ℕ) : ℤ) : ℤ) : ℂ) * I * θ) * X θ -
          ((zhukovskyRadius n : ℂ)⁻¹) ^ 2 *
            (cexp (((-((k + 1 : ℕ) : ℤ) : ℤ) : ℂ) * I * θ) * X θ)) := by
    intro θ
    unfold cepstralModeWeight
    have he1 : cexp (((-(k : ℤ) : ℤ) : ℂ) * I * θ) * cexp (θ * I) =
        cexp (((-((k - 1 : ℕ) : ℤ) : ℤ) : ℂ) * I * θ) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast [Nat.cast_sub hk]
      ring
    have he2 : cexp (((-(k : ℤ) : ℤ) : ℂ) * I * θ) * cexp (-(θ * I)) =
        cexp (((-((k + 1 : ℕ) : ℤ) : ℤ) : ℂ) * I * θ) := by
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [← he1, ← he2]
    ring
  have hint : ∀ j : ℕ, IntegrableOn (fun θ : ℝ =>
      cexp (((-(j : ℤ) : ℤ) : ℂ) * I * θ) * X θ) (Ioc 0 (2 * Real.pi)) := fun j =>
    (((by fun_prop : Continuous fun θ : ℝ => cexp (((-(j : ℤ) : ℤ) : ℂ) * I * θ)).mul
      hXc).integrableOn_Icc).mono_set Ioc_subset_Icc_self
  rw [setIntegral_congr_fun measurableSet_Ioc (fun θ _ => hpt θ), integral_const_mul,
    integral_sub (hint (k - 1)) ((hint (k + 1)).const_mul _), integral_const_mul,
    hX, integral_mode_mul_exp_neg_zhukovskyLoop, integral_mode_mul_exp_neg_zhukovskyLoop]
  have hpow : (-(zhukovskyRadius n : ℂ)) ^ (k + 1) =
      (-(zhukovskyRadius n : ℂ)) ^ (k - 1) * (zhukovskyRadius n : ℂ) ^ 2 := by
    rw [show k + 1 = (k - 1) + 2 by omega, pow_add]
    ring
  push_cast
  rw [hpow]
  field_simp

/-- **Alternating Bessel cepstrum.** On a corridor window, for `k ≥ 1`,
`S_k = (-ρ)^k (c/2) ∫₀^∞ e^{-t/2} (I_{k-1}(ct) - I_{k+1}(ct)) |𝒵(t)|² dt`. -/
theorem InCorridor.cepstralCoeff_eq_bessel {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hcorr : W.InCorridor n η) {k : ℕ} (hk : 1 ≤ k) :
    W.cepstralCoeff n k = (((-zhukovskyRadius n) ^ k * (zhukovskyFocal n / 2) *
      ∫ t in Ioi (0 : ℝ), Real.exp (-(t / 2)) *
        (besselI (k - 1) (zhukovskyFocal n * t) - besselI (k + 1) (zhukovskyFocal n * t)) *
          ‖W.expSum t‖ ^ 2 : ℝ) : ℂ) := by
  set c := zhukovskyFocal n with hc_def
  set ρ := zhukovskyRadius n with hρ_def
  have hρpos : 0 < ρ := zhukovskyRadius_pos n
  have hcpos : 0 < c := zhukovskyFocal_pos n
  set δ : ℝ := (1 / 2 - zhukovskyMajorAxis n - η) / 2 with hδ_def
  have hδ : ∀ z ∈ W.Z, z.re - 1 / 2 ≤ δ := fun z hz => by
    have := hcorr z hz; rw [hδ_def]; linarith
  have hJre : ∀ θ : ℝ, 1 / 2 - zhukovskyMajorAxis n ≤
      (zhukovskyLoop n (HTGeometry.circleExp θ)).re := re_zhukovskyLoop_circleExp_ge n
  have hJcont : Continuous fun θ : ℝ => zhukovskyLoop n (HTGeometry.circleExp θ) :=
    (zhukovskyLoop n).continuous.comp HTGeometry.continuous_circleExp
  set G : ℝ → ℝ → ℂ := fun θ t => cepstralModeWeight n k θ *
    (cexp (-(zhukovskyLoop n (HTGeometry.circleExp θ) * t)) * ((‖W.expSum t‖ ^ 2 : ℝ) : ℂ))
    with hG
  -- Laplace identity under the circle integral
  have hstep2 : ∀ θ : ℝ, cepstralModeWeight n k θ *
      W.pairResolvent (zhukovskyLoop n (HTGeometry.circleExp θ)) =
        ∫ t in Ioi (0 : ℝ), G θ t := by
    intro θ
    rw [W.pairResolvent_eq_integral hδ (by have := hJre θ; rw [hδ_def]; linarith),
      ← integral_const_mul]
  -- domination by `B e^{-ηt}` on the product
  set B : ℝ := c * ρ / 2 * (1 + (ρ⁻¹) ^ 2) * (W.degree : ℝ) ^ 2 with hB
  have hbound : ∀ θ t : ℝ, 0 ≤ t → ‖G θ t‖ ≤ B * Real.exp (-η * t) := by
    intro θ t ht
    have hw : ‖cepstralModeWeight n k θ‖ ≤ c * ρ / 2 * (1 + (ρ⁻¹) ^ 2) := by
      unfold cepstralModeWeight
      rw [norm_mul, norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by positivity : (0 : ℝ) < zhukovskyFocal n * zhukovskyRadius n / 2)]
      have h1 : (((((-(k : ℤ) : ℤ) : ℂ) * I * θ)).re) = 0 := by simp
      rw [h1, Real.exp_zero, one_mul]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      refine (norm_sub_le _ _).trans ?_
      rw [norm_mul, norm_pow, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hρpos,
        Complex.norm_exp_ofReal_mul_I,
        show -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I by push_cast; ring,
        Complex.norm_exp_ofReal_mul_I, mul_one]
    have he : ‖cexp (-(zhukovskyLoop n (HTGeometry.circleExp θ) * t))‖ ≤
        Real.exp (-((1 / 2 - zhukovskyMajorAxis n) * t)) := by
      rw [Complex.norm_exp]
      refine Real.exp_le_exp.mpr ?_
      have hre : (-(zhukovskyLoop n (HTGeometry.circleExp θ) * t)).re =
          -((zhukovskyLoop n (HTGeometry.circleExp θ)).re * t) := by simp
      rw [hre]
      nlinarith [hJre θ]
    have hE : ‖W.expSum t‖ ^ 2 ≤ ((W.degree : ℝ) * Real.exp (δ * t)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (W.norm_expSum_le hδ ht) 2
    rw [hG]
    simp only
    rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    have hexp : Real.exp (-((1 / 2 - zhukovskyMajorAxis n) * t)) * Real.exp (δ * t) ^ 2 =
        Real.exp (-η * t) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [hδ_def]
      ring
    calc ‖cepstralModeWeight n k θ‖ *
          (‖cexp (-(zhukovskyLoop n (HTGeometry.circleExp θ) * t))‖ * ‖W.expSum t‖ ^ 2)
        ≤ (c * ρ / 2 * (1 + (ρ⁻¹) ^ 2)) * (Real.exp (-((1 / 2 - zhukovskyMajorAxis n) * t)) *
            ((W.degree : ℝ) * Real.exp (δ * t)) ^ 2) := by
          gcongr
      _ = B * Real.exp (-η * t) := by rw [hB, ← hexp]; ring
  have hGint : Integrable (Function.uncurry G)
      ((volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
    have hdom : Integrable (fun p : ℝ × ℝ => B * Real.exp (-η * p.2))
        ((volume.restrict (Ioc (0 : ℝ) (2 * Real.pi))).prod (volume.restrict (Ioi (0 : ℝ)))) :=
      (integrable_const B).mul_prod (exp_neg_integrableOn_Ioi 0 hη)
    refine hdom.mono' ?_ ?_
    · refine Continuous.aestronglyMeasurable ?_
      rw [hG]
      exact ((continuous_cepstralModeWeight n k).comp continuous_fst).mul
        ((Complex.continuous_exp.comp ((hJcont.comp continuous_fst).mul
          (Complex.continuous_ofReal.comp continuous_snd)).neg).mul
          (Complex.continuous_ofReal.comp ((W.continuous_expSum.comp continuous_snd).norm.pow 2)))
    · rw [Measure.prod_restrict]
      refine ae_restrict_of_forall_mem (measurableSet_Ioc.prod measurableSet_Ioi) fun p hp => ?_
      exact hbound p.1 p.2 (mem_Ioi.mp (mem_prod.mp hp).2).le
  have h1 := hcorr.integral_cepstralModeWeight_mul_pairResolvent hη hη2 hk
  rw [setIntegral_congr_fun measurableSet_Ioc (fun θ _ => hstep2 θ),
    integral_integral_swap hGint] at h1
  have hinner : ∀ t : ℝ, ∫ θ in Ioc (0 : ℝ) (2 * Real.pi), G θ t =
      ((2 * Real.pi * (c * ρ / 2) * (-ρ) ^ (k - 1) *
        (Real.exp (-(t / 2)) * (besselI (k - 1) (c * t) - besselI (k + 1) (c * t)) *
          ‖W.expSum t‖ ^ 2) : ℝ) : ℂ) := by
    intro t
    have hpt : ∀ θ : ℝ, G θ t = (cepstralModeWeight n k θ *
        cexp (-(zhukovskyLoop n (HTGeometry.circleExp θ) * t))) *
          ((‖W.expSum t‖ ^ 2 : ℝ) : ℂ) := fun θ => by rw [hG]; ring
    rw [setIntegral_congr_fun measurableSet_Ioc (fun θ _ => hpt θ), integral_mul_const,
      integral_cepstralModeWeight_mul_exp n hk t]
    push_cast
    ring
  simp_rw [hinner] at h1
  rw [integral_complex_ofReal, integral_const_mul] at h1
  have h2π : ((2 * Real.pi : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (by positivity : (2 * Real.pi : ℝ) ≠ 0)
  have hpowk : (-ρ) ^ k = -ρ * (-ρ) ^ (k - 1) := by
    rw [← pow_succ', Nat.sub_add_cancel hk]
  set Int := ∫ t in Ioi (0 : ℝ), Real.exp (-(t / 2)) *
    (besselI (k - 1) (c * t) - besselI (k + 1) (c * t)) * ‖W.expSum t‖ ^ 2
  have hS : W.cepstralCoeff n k = -(((2 * Real.pi * (c * ρ / 2) * (-ρ) ^ (k - 1) * Int : ℝ) : ℂ)) /
      ((2 * Real.pi : ℝ) : ℂ) := by
    rw [h1]
    field_simp
  rw [hS, hpowk]
  push_cast
  field_simp

/-- **Alternating sign.** `(-1)^k S_k` is a nonnegative real number: it equals
`ρ^k (c/2) ∫₀^∞ e^{-t/2}(I_{k-1} - I_{k+1})(ct)|𝒵(t)|² dt` with nonnegative integrand. -/
theorem InCorridor.neg_one_pow_mul_cepstralCoeff_eq_nonneg {η : ℝ} (hη : 0 < η)
    (hη2 : η ≤ 1 / 2) (hcorr : W.InCorridor n η) {k : ℕ} (hk : 1 ≤ k) :
    ∃ s : ℝ, 0 ≤ s ∧ (-1) ^ k * W.cepstralCoeff n k = s := by
  refine ⟨zhukovskyRadius n ^ k * (zhukovskyFocal n / 2) *
    ∫ t in Ioi (0 : ℝ), Real.exp (-(t / 2)) *
      (besselI (k - 1) (zhukovskyFocal n * t) - besselI (k + 1) (zhukovskyFocal n * t)) *
        ‖W.expSum t‖ ^ 2, ?_, ?_⟩
  · have hI : 0 ≤ ∫ t in Ioi (0 : ℝ), Real.exp (-(t / 2)) *
        (besselI (k - 1) (zhukovskyFocal n * t) - besselI (k + 1) (zhukovskyFocal n * t)) *
          ‖W.expSum t‖ ^ 2 := by
      refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
      have ht0 : 0 ≤ zhukovskyFocal n * t :=
        mul_nonneg (zhukovskyFocal_pos n).le (mem_Ioi.mp ht).le
      have hle : besselI (k + 1) (zhukovskyFocal n * t) ≤ besselI (k - 1) (zhukovskyFocal n * t) := by
        have h := besselI_add_two_le (k - 1) ht0
        rwa [show k - 1 + 2 = k + 1 by omega] at h
      have : 0 ≤ besselI (k - 1) (zhukovskyFocal n * t) - besselI (k + 1) (zhukovskyFocal n * t) :=
        sub_nonneg.mpr hle
      positivity
    have hρ := zhukovskyRadius_pos n
    have hc := zhukovskyFocal_pos n
    positivity
  · rw [hcorr.cepstralCoeff_eq_bessel hη hη2 hk]
    set Int := ∫ t in Ioi (0 : ℝ), Real.exp (-(t / 2)) *
      (besselI (k - 1) (zhukovskyFocal n * t) - besselI (k + 1) (zhukovskyFocal n * t)) *
        ‖W.expSum t‖ ^ 2
    have h : ((-1 : ℂ)) ^ k * (-(zhukovskyRadius n : ℂ)) ^ k = (zhukovskyRadius n : ℂ) ^ k := by
      rw [← mul_pow, neg_one_mul, neg_neg]
    calc (-1 : ℂ) ^ k * (((-zhukovskyRadius n) ^ k * (zhukovskyFocal n / 2) * Int : ℝ) : ℂ)
        = ((-1 : ℂ) ^ k * (-(zhukovskyRadius n : ℂ)) ^ k) *
            ((zhukovskyFocal n / 2 * Int : ℝ) : ℂ) := by push_cast; ring
      _ = (zhukovskyRadius n : ℂ) ^ k * ((zhukovskyFocal n / 2 * Int : ℝ) : ℂ) := by rw [h]
      _ = ((zhukovskyRadius n ^ k * (zhukovskyFocal n / 2) * Int : ℝ) : ℂ) := by push_cast; ring

end ReflectedWindow

/-! ## The energy-built certificate -/

/-- Bessel transform of an energy profile `E`:
`(-ρ)^k (c/2) ∫₀^∞ e^{-t/2} (I_{k-1}(ct) - I_{k+1}(ct)) E(t) dt`. -/
def besselEnergyCepstrum (n : ℕ) (E : ℝ → ℝ) (k : ℕ) : ℂ :=
  (((-zhukovskyRadius n) ^ k * (zhukovskyFocal n / 2) *
    ∫ t in Ioi (0 : ℝ), Real.exp (-(t / 2)) *
      (besselI (k - 1) (zhukovskyFocal n * t) - besselI (k + 1) (zhukovskyFocal n * t)) * E t : ℝ) : ℂ)

/-- **Bessel–Szegő certificate of order `K`** built from an energy profile `E`. -/
def besselSzegoCertificate (n K : ℕ) (E : ℝ → ℝ) : ℂ → ℂ :=
  szegoCertificate n K (besselEnergyCepstrum n E)

theorem isDiskUnit_besselSzegoCertificate (n K : ℕ) (E : ℝ → ℝ) :
    IsDiskUnit (besselSzegoCertificate n K E) :=
  isDiskUnit_szegoCertificate n K _

namespace ReflectedWindow

variable {W : ReflectedWindow} {n : ℕ}

/-- On a corridor window the energy-built certificate coincides with the cepstral one. -/
theorem InCorridor.besselSzegoCertificate_eq {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (hcorr : W.InCorridor n η) (K : ℕ) :
    besselSzegoCertificate n K (fun t => ‖W.expSum t‖ ^ 2) = szegoCertificate n K (W.cepstralCoeff n) := by
  funext u
  unfold besselSzegoCertificate szegoCertificate
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · rw [hcorr.cepstralCoeff_eq_bessel hη hη2 hk]
    rfl

/-- **Energy-built certificate completeness.** On a corridor window with margin `η`, the order-`K`
Bessel–Szegő certificate of the energy `|𝒵(t)|²` makes the collision loop sectorial once
`2 D² (1 - η)^{K+1} / η < π / 2`. -/
theorem InCorridor.besselSzegoCertificate_mul_loop_pos {P : Polynomial ℂ}
    (heval : ∀ x : ℂ, P.eval x = ∏ z ∈ W.Z, ∏ w ∈ W.Z, (x - (z - w)) ^ (W.mult z * W.mult w))
    {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) (hcorr : W.InCorridor n η) {K : ℕ}
    (hK : 2 * (W.degree : ℝ) ^ 2 * (1 - η) ^ (K + 1) / η < Real.pi / 2)
    (u : HTGeometry.UnitCircle) :
    0 < (besselSzegoCertificate n K (fun t => ‖W.expSum t‖ ^ 2) u *
      polyZhukovskyLaurentLoop n P u).re := by
  rw [hcorr.besselSzegoCertificate_eq hη hη2 K]
  exact hcorr.szegoCertificate_mul_loop_pos heval hη hη2 hK u


/-! ## Rigidity of Szegő certificates -/

theorem InCorridor.differentiableOn_exactSzegoMultiplier {η : ℝ} (hη : 0 < η)
    (hη2 : η ≤ 1 / 2) (hcorr : W.InCorridor n η) :
    DifferentiableOn ℂ (W.exactSzegoMultiplier n) (Metric.closedBall 0 1) := by
  intro z hz
  rw [Metric.mem_closedBall, dist_zero_right] at hz
  refine DifferentiableAt.differentiableWithinAt ?_
  unfold exactSzegoMultiplier
  refine DifferentiableAt.fun_finsetProd fun x hx => DifferentiableAt.fun_finsetProd fun y hy => ?_
  refine DifferentiableAt.pow (DifferentiableAt.div ?_ ?_
    (hcorr.innerDen_ne_zero hη hη2 hx hy hz)) _
  · unfold innerNum; fun_prop
  · unfold innerDen; fun_prop

/-- **Rigidity of Szegő certificates.** On a corridor window, every multiplier `F'` holomorphic on
the open disk and continuous on its closure with `Re (F' Λ) > 0` on `S¹` satisfies
`Re (F'/F) > 0` on the closed disk, `F` the exact multiplier; in particular `F'` is zero-free.
Proof: `F Λ > 0` on `S¹`, so `Re (F'/F) > 0` there; minimum principle for `|exp(-F'/F)|`. -/
theorem InCorridor.re_div_exactSzegoMultiplier_pos {P : Polynomial ℂ}
    (heval : ∀ x : ℂ, P.eval x = ∏ z ∈ W.Z, ∏ w ∈ W.Z, (x - (z - w)) ^ (W.mult z * W.mult w))
    {η : ℝ} (hη : 0 < η) (hη2 : η ≤ 1 / 2) (hcorr : W.InCorridor n η) {F' : ℂ → ℂ}
    (hF' : DiffContOnCl ℂ F' (Metric.ball 0 1))
    (hpos : ∀ u : HTGeometry.UnitCircle, 0 < (F' u * polyZhukovskyLaurentLoop n P u).re) :
    ∀ z ∈ Metric.closedBall (0 : ℂ) 1, 0 < (F' z / W.exactSzegoMultiplier n z).re := by
  set F := W.exactSzegoMultiplier n with hF_def
  have hFd := hcorr.differentiableOn_exactSzegoMultiplier hη hη2
  have hFne : ∀ z ∈ Metric.closedBall (0 : ℂ) 1, F z ≠ 0 :=
    (W.isDiskUnit_exactSzegoMultiplier hη hη2 hcorr).2
  have hcl : closure (Metric.ball (0 : ℂ) 1) = Metric.closedBall 0 1 := closure_ball 0 one_ne_zero
  set Ω : ℂ → ℂ := fun z => F' z / F z with hΩ_def
  have hΩ : DiffContOnCl ℂ Ω (Metric.ball 0 1) :=
    ⟨hF'.differentiableOn.div (hFd.mono Metric.ball_subset_closedBall)
        (fun z hz => hFne z (Metric.ball_subset_closedBall hz)),
      hF'.continuousOn.div (by rw [hcl]; exact hFd.continuousOn) (by rw [hcl]; exact hFne)⟩
  have hbd : ∀ u : HTGeometry.UnitCircle, 0 < (Ω u).re := by
    intro u
    obtain ⟨r, hr, hr_eq⟩ := W.exactSzegoMultiplier_mul_loop_eq_pos heval hη hη2 hcorr u
    have hu : (u : ℂ) ∈ Metric.closedBall (0 : ℂ) 1 := by
      rw [Metric.mem_closedBall, dist_zero_right]; exact (HTGeometry.norm_coe_unitCircle u).le
    have h := hpos u
    have hsplit : F' u * polyZhukovskyLaurentLoop n P u =
        Ω u * (F u * polyZhukovskyLaurentLoop n P u) := by
      rw [hΩ_def]
      field_simp [hFne _ hu]
    rw [hsplit, hr_eq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
      sub_zero] at h
    exact pos_of_mul_pos_left h hr.le
  have hcont : ContinuousOn (fun z => (Ω z).re) (Metric.sphere (0 : ℂ) 1) :=
    Complex.continuous_re.comp_continuousOn
      (hΩ.continuousOn.mono (by rw [hcl]; exact Metric.sphere_subset_closedBall))
  obtain ⟨z₀, hz₀, hmin⟩ := (isCompact_sphere (0 : ℂ) 1).exists_isMinOn
    (NormedSpace.sphere_nonempty.mpr zero_le_one) hcont
  have hμ : 0 < (Ω z₀).re := hbd ⟨z₀, hz₀⟩
  have hg : DiffContOnCl ℂ (fun z => cexp (-Ω z)) (Metric.ball 0 1) :=
    Complex.differentiable_exp.comp_diffContOnCl hΩ.neg
  intro z hz
  have hfront : ∀ w ∈ frontier (Metric.ball (0 : ℂ) 1),
      ‖cexp (-Ω w)‖ ≤ Real.exp (-(Ω z₀).re) := by
    intro w hw
    rw [frontier_ball 0 one_ne_zero] at hw
    rw [Complex.norm_exp, Complex.neg_re]
    exact Real.exp_le_exp.mpr (neg_le_neg (hmin hw))
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le Metric.isBounded_ball hg hfront
    (by rw [hcl]; exact hz)
  rw [Complex.norm_exp, Complex.neg_re, Real.exp_le_exp] at h
  show 0 < (Ω z).re
  linarith

end ReflectedWindow

end GaloisForLFunctions.ConjugateDiagonalGeometry.SzegoCollision
