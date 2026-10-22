import GaloisForLFunctions.RHTower.CCM.CCMRadialGlobalDefectMass

/-!
# The two forced scales of the constrained radial-prolate tail

The constrained two-mode source has an exact exterior leakage, obtained from orthogonality of the
two exterior components; the exterior profile at *any* scale `α` has an exact total mass, obtained
from one translation and one dilation of the half-line; and the endpoint slope is normalized by the
inner scale `α = λ³` while the total mass is normalized by the outer scale `α = λ`.

The scale separation is therefore an identity, not an asymptotic statement: the two profiles are the
same function read at two dilations, and the ratio of their endpoint slopes is exactly `λ²`.
-/

open MeasureTheory Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-! ## Equation (3): the exact two-mode exterior leakage -/

/-- **Equation (3).**  The exterior energy of the normalized vanishing-integral two-mode source is
the orthogonality-weighted average of the two component leakages. -/
theorem norm_sq_twoModeExterior {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (P : E →ₗ[ℝ] E) (e₀ e₁ : E) {l₀ l₁ : ℝ} (hsum : 0 < l₀ ^ (2 : ℕ) + l₁ ^ (2 : ℕ))
    (horth : (inner ℝ (P e₀) (P e₁) : ℝ) = 0) :
    ‖P ((Real.sqrt (l₀ ^ (2 : ℕ) + l₁ ^ (2 : ℕ)))⁻¹ • (l₁ • e₀ - l₀ • e₁))‖ ^ (2 : ℕ)
      = (l₁ ^ (2 : ℕ) * ‖P e₀‖ ^ (2 : ℕ) + l₀ ^ (2 : ℕ) * ‖P e₁‖ ^ (2 : ℕ)) / (l₀ ^ (2 : ℕ) + l₁ ^ (2 : ℕ)) := by
  have hspos : (0 : ℝ) < Real.sqrt (l₀ ^ (2 : ℕ) + l₁ ^ (2 : ℕ)) := Real.sqrt_pos.mpr hsum
  have hsq : Real.sqrt (l₀ ^ (2 : ℕ) + l₁ ^ (2 : ℕ)) ^ (2 : ℕ) = l₀ ^ (2 : ℕ) + l₁ ^ (2 : ℕ) := Real.sq_sqrt hsum.le
  have hmap : P ((Real.sqrt (l₀ ^ (2 : ℕ) + l₁ ^ (2 : ℕ)))⁻¹ • (l₁ • e₀ - l₀ • e₁))
      = (Real.sqrt (l₀ ^ (2 : ℕ) + l₁ ^ (2 : ℕ)))⁻¹ • (l₁ • P e₀ - l₀ • P e₁) := by
    rw [map_smul, map_sub, map_smul, map_smul]
  have hinner : (inner ℝ (l₁ • P e₀) (l₀ • P e₁) : ℝ) = 0 := by
    rw [real_inner_smul_left, real_inner_smul_right, horth]
    ring
  have hnorm : ‖l₁ • P e₀ - l₀ • P e₁‖ ^ (2 : ℕ)
      = l₁ ^ (2 : ℕ) * ‖P e₀‖ ^ (2 : ℕ) + l₀ ^ (2 : ℕ) * ‖P e₁‖ ^ (2 : ℕ) := by
    rw [norm_sub_sq_real, hinner, norm_smul, norm_smul]
    simp only [Real.norm_eq_abs, mul_pow, sq_abs]
    ring
  rw [hmap, norm_smul, mul_pow, hnorm]
  simp only [norm_inv, Real.norm_eq_abs, abs_of_pos hspos]
  rw [inv_pow, hsq]
  field_simp

/-! ## The exterior profile at a scale -/

/-- The exterior profile of `q` at the scale `α`: `t ↦ q(λ + t/α)/q(λ)`. -/
def scaledProfile (lam alpha : ℝ) (q : ℝ → ℂ) (t : ℝ) : ℂ := q (lam + t / alpha) / q lam

/-- Its squared modulus. -/
def scaledProfileSq (lam alpha : ℝ) (q : ℝ → ℂ) (t : ℝ) : ℝ :=
  ‖q (lam + t / alpha)‖ ^ (2 : ℕ) / ‖q lam‖ ^ (2 : ℕ)

theorem scaledProfile_zero {lam alpha : ℝ} {q : ℝ → ℂ} (hq : q lam ≠ 0) :
    scaledProfile lam alpha q 0 = 1 := by
  unfold scaledProfile
  simp [hq]

/-- Translating the half-line moves the base point. -/
theorem integral_Ioi_shift (lam : ℝ) (f : ℝ → ℝ) :
    ∫ u in Ioi (0 : ℝ), f (lam + u) = ∫ y in Ioi lam, f y := by
  have hmp : MeasurePreserving (fun y : ℝ => lam + y) volume volume :=
    measurePreserving_add_left volume lam
  have hemb : MeasurableEmbedding (fun y : ℝ => lam + y) :=
    (Homeomorph.addLeft lam).measurableEmbedding
  have hpre : (fun y : ℝ => lam + y) ⁻¹' Ioi lam = Ioi (0 : ℝ) := by ext y; simp
  have h := hmp.setIntegral_preimage_emb hemb f (Ioi lam)
  rw [hpre] at h
  exact h

/-- Dilating the half-line rescales the integral. -/
theorem integral_Ioi_dilate {alpha : ℝ} (halpha : 0 < alpha) (g : ℝ → ℝ) :
    ∫ t in Ioi (0 : ℝ), g (t / alpha) = alpha * ∫ u in Ioi (0 : ℝ), g u := by
  have h := integral_comp_mul_left_Ioi g 0 (b := alpha⁻¹) (by positivity)
  simp only [mul_zero, smul_eq_mul, inv_inv] at h
  rw [show (fun t : ℝ => g (t / alpha)) = fun t : ℝ => g (alpha⁻¹ * t) from by
    funext t; rw [div_eq_inv_mul]]
  rw [h]

/-- **Equations (9) and (16).**  The exterior mass of the profile at any scale `α` is exactly
`α δ / (2 |q(λ)|²)`: one translation and one dilation of the half-line, no asymptotics. -/
theorem integral_Ioi_scaledProfileSq {lam alpha delta : ℝ} {q : ℝ → ℂ} (halpha : 0 < alpha)
    (hqeven : Function.Even q) (hqlam : ‖q lam‖ ≠ 0)
    (hexterior : (∫ y in Iic (-lam), ‖q y‖ ^ (2 : ℕ)) + ∫ y in Ioi lam, ‖q y‖ ^ (2 : ℕ) = delta) :
    ∫ t in Ioi (0 : ℝ), scaledProfileSq lam alpha q t = alpha * delta / (2 * ‖q lam‖ ^ (2 : ℕ)) := by
  have h2 : ‖q lam‖ ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hqlam
  have heven := integral_Iic_norm_sq_eq_integral_Ioi_of_even (lam := lam) hqeven
  have htail : ∫ y in Ioi lam, ‖q y‖ ^ (2 : ℕ) = delta / 2 := by
    rw [heven] at hexterior
    linarith
  have hstep : ∫ t in Ioi (0 : ℝ), ‖q (lam + t / alpha)‖ ^ (2 : ℕ)
      = alpha * ∫ y in Ioi lam, ‖q y‖ ^ (2 : ℕ) := by
    rw [integral_Ioi_dilate halpha (fun u => ‖q (lam + u)‖ ^ (2 : ℕ)),
      integral_Ioi_shift lam (fun y => ‖q y‖ ^ (2 : ℕ))]
  unfold scaledProfileSq
  rw [integral_div, hstep, htail]
  field_simp

/-- **Equation (10).**  The outer scale `α = λ` normalizes the total exterior mass to `1/(4π)`. -/
theorem tendsto_integral_Ioi_scaledProfileSq_outer
    {ι : Type*} {l : Filter ι} {lamf df deltaf : ι → ℝ} {qf : ι → ℝ → ℂ}
    (hparam : ∀ᶠ i in l, 0 < lamf i ∧ df i ≠ 0 ∧ ‖qf i (lamf i)‖ ≠ 0)
    (hqeven : ∀ i, Function.Even (qf i))
    (hexterior : ∀ i,
      (∫ y in Iic (-lamf i), ‖qf i y‖ ^ (2 : ℕ)) + ∫ y in Ioi (lamf i), ‖qf i y‖ ^ (2 : ℕ) = deltaf i)
    (hratio : Tendsto (fun i => deltaf i / df i) l (nhds (8 / 11)))
    (hheight : Tendsto (fun i => ‖qf i (lamf i)‖ ^ (2 : ℕ) / (lamf i * df i)) l
      (nhds (16 * Real.pi / 11))) :
    Tendsto (fun i => ∫ t in Ioi (0 : ℝ), scaledProfileSq (lamf i) (lamf i) (qf i) t) l
      (nhds (1 / (4 * Real.pi))) := by
  have hne : (16 * Real.pi / 11 : ℝ) ≠ 0 := by positivity
  have hlim := ((hratio.const_mul (1 / 2 : ℝ)).div hheight hne)
  have hval : (1 / 2 : ℝ) * (8 / 11) / (16 * Real.pi / 11) = 1 / (4 * Real.pi) := by
    have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
    field_simp
    ring
  rw [hval] at hlim
  refine hlim.congr' ?_
  filter_upwards [hparam] with i hi
  rw [integral_Ioi_scaledProfileSq hi.1 (hqeven i) hi.2.2 (hexterior i)]
  simp only [Pi.div_apply]
  have h2 : ‖qf i (lamf i)‖ ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hi.2.2
  have hd : df i ≠ 0 := hi.2.1
  have hl : lamf i ≠ 0 := hi.1.ne'
  field_simp

/-- **Equation (16).**  The inner scale `α = λ³` normalizes the endpoint derivative, not the mass:
its total mass diverges like `λ²/(4π)`. -/
theorem tendsto_integral_Ioi_scaledProfileSq_inner
    {ι : Type*} {l : Filter ι} {lamf df deltaf : ι → ℝ} {qf : ι → ℝ → ℂ}
    (hparam : ∀ᶠ i in l, 0 < lamf i ∧ df i ≠ 0 ∧ ‖qf i (lamf i)‖ ≠ 0)
    (hqeven : ∀ i, Function.Even (qf i))
    (hexterior : ∀ i,
      (∫ y in Iic (-lamf i), ‖qf i y‖ ^ (2 : ℕ)) + ∫ y in Ioi (lamf i), ‖qf i y‖ ^ (2 : ℕ) = deltaf i)
    (hratio : Tendsto (fun i => deltaf i / df i) l (nhds (8 / 11)))
    (hheight : Tendsto (fun i => ‖qf i (lamf i)‖ ^ (2 : ℕ) / (lamf i * df i)) l
      (nhds (16 * Real.pi / 11))) :
    Tendsto (fun i => (∫ t in Ioi (0 : ℝ), scaledProfileSq (lamf i) (lamf i ^ (3 : ℕ)) (qf i) t)
        / lamf i ^ (2 : ℕ)) l (nhds (1 / (4 * Real.pi))) := by
  refine (tendsto_integral_Ioi_scaledProfileSq_outer hparam hqeven hexterior hratio
    hheight).congr' ?_
  filter_upwards [hparam] with i hi
  have hl : lamf i ≠ 0 := hi.1.ne'
  have h2 : ‖qf i (lamf i)‖ ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hi.2.2
  rw [integral_Ioi_scaledProfileSq hi.1 (hqeven i) hi.2.2 (hexterior i),
    integral_Ioi_scaledProfileSq (pow_pos hi.1 3) (hqeven i) hi.2.2 (hexterior i)]
  field_simp

/-! ## The endpoint slope and the scale separation -/

theorem hasDerivAt_scaledProfile {lam alpha : ℝ} (halpha : alpha ≠ 0) {q : ℝ → ℂ} {qp : ℂ}
    (hq : HasDerivAt q qp lam) :
    HasDerivAt (scaledProfile lam alpha q) (qp / (alpha * q lam)) 0 := by
  have hlin : HasDerivAt (fun t : ℝ => lam + t / alpha) (1 / alpha) 0 := by
    have h : HasDerivAt (fun t : ℝ => t / alpha) (1 / alpha) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).div_const alpha
    simpa using h.const_add lam
  have hz : lam + (0 : ℝ) / alpha = lam := by simp
  have hq' : HasDerivAt q qp (lam + (0 : ℝ) / alpha) := by rw [hz]; exact hq
  have hcomp : HasDerivAt (fun t : ℝ => q (lam + t / alpha)) ((1 / alpha : ℝ) • qp) 0 :=
    hq'.scomp 0 hlin
  have hdiv := hcomp.div_const (q lam)
  have hval : ((1 / alpha : ℝ) • qp) / q lam = qp / ((alpha : ℂ) * q lam) := by
    rw [Complex.real_smul]
    have hac : (alpha : ℂ) ≠ 0 := by exact_mod_cast halpha
    push_cast
    field_simp
  rw [hval] at hdiv
  exact hdiv

/-- **Equations (11)–(12).**  In the CCM aperture `c = 2πλ²` the endpoint logarithmic derivative
splits into the universal cubic term and an eigenvalue remainder. -/
theorem endpointLogDeriv_eq {lam : ℝ} (hlam : lam ≠ 0) (kappa : ℝ) :
    (kappa - (2 * Real.pi * lam ^ (2 : ℕ)) ^ (2 : ℕ)) / (2 * lam)
      = -(2 * Real.pi ^ (2 : ℕ)) * lam ^ (3 : ℕ) + kappa / (2 * lam) := by
  field_simp
  ring

/-- **Equation (14).**  The inner scale normalizes the endpoint slope: its limit is the universal
constant `-2π²`. -/
theorem tendsto_endpointLogDeriv_div_cube
    {ι : Type*} {l : Filter ι} {lamf kappaf : ι → ℝ}
    (hlam : ∀ᶠ i in l, lamf i ≠ 0)
    (hkappa : Tendsto (fun i => kappaf i / lamf i ^ (4 : ℕ)) l (nhds 0)) :
    Tendsto (fun i => ((kappaf i - (2 * Real.pi * lamf i ^ (2 : ℕ)) ^ (2 : ℕ)) / (2 * lamf i)) / lamf i ^ (3 : ℕ))
      l (nhds (-(2 * Real.pi ^ (2 : ℕ)))) := by
  have hlim : Tendsto (fun i => (1 / 2 : ℝ) * (kappaf i / lamf i ^ (4 : ℕ)) + -(2 * Real.pi ^ (2 : ℕ))) l
      (nhds ((1 / 2 : ℝ) * 0 + -(2 * Real.pi ^ (2 : ℕ)))) :=
    (hkappa.const_mul (1 / 2 : ℝ)).add_const _
  rw [mul_zero, zero_add] at hlim
  refine hlim.congr' ?_
  filter_upwards [hlam] with i hi
  field_simp
  ring

/-- **Equation (15).**  The two endpoint slopes differ by exactly `λ²`: the outer coordinate has a
diverging boundary derivative, the inner one a finite limit.  The scale separation is an identity. -/
theorem outerSlope_eq_sq_mul_innerSlope {lam : ℝ} (hlam : lam ≠ 0) (q : ℝ → ℂ) (qp : ℂ) :
    qp / ((lam : ℂ) * q lam) = (lam : ℂ) ^ (2 : ℕ) * (qp / ((lam : ℂ) ^ (3 : ℕ) * q lam)) := by
  have hl : (lam : ℂ) ≠ 0 := by exact_mod_cast hlam
  field_simp

end GaloisForLFunctions.RHTower

end
