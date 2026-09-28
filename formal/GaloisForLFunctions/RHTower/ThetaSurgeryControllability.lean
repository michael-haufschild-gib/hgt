import GaloisForLFunctions.RHTower.ThetaProfileSurgeryVariation
import GaloisForLFunctions.HTGeometry.OscillatoryPacketFourier

/-!
# Mass-neutral high-frequency controllability of the theta profile surgery

The perturbation `g = ε₀ g₀ + ε₁ g₁ + ε₂ g₂` along the even directions `g₀ = ψ`,
`g₁ = ψ cos(T·)`, `g₂ = t ψ sin(T·)` has spectral value `E_T(g) = ∫ e^{-i z_T t} g(t) dt` at
`z_T = T + iv` and mass `M(g) = 2a ∫₀^∞ e^{at} g = ∫₀^∞ e^{at}(ag - g')`, `a = 1/4`.
By the Riemann–Lebesgue lemma `E_T(g₀) → 0`, `E_T(g₁) → ½∫e^{vt}ψ > 0`,
`E_T(g₂) → -(i/2)∫e^{vt} tψ` with `∫e^{vt} tψ = 2∫₀^∞ tψ sinh(vt) > 0`, `M(g₁), M(g₂) → 0` and
`M(g₀) > 0`.  Hence the real `3×3` matrix `(Re E_T, Im E_T, M)` converges to an invertible
matrix, and for large `T` the restriction of `E_T` to the mass-neutral directions is a
real-linear bijection onto `ℂ` whose inverse is bounded uniformly in `T`.
-/
open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped ContDiff ComplexConjugate

namespace RHTower

noncomputable section

/-! ## The envelope and the three directions -/

/-- The seam-flat envelope `ψ(t) = t^{2N+2} exp(-(e^{2t} + e^{-2t}))`. -/
def surgeryEnvelope (N : ℕ) (t : ℝ) : ℝ :=
  t ^ (2 * N + 2) * Real.exp (-(Real.exp (2 * t) + Real.exp (-(2 * t))))

theorem surgeryEnvelope_pos (N : ℕ) {t : ℝ} (ht : t ≠ 0) : 0 < surgeryEnvelope N t :=
  mul_pos (Even.pow_pos ⟨N + 1, by ring⟩ ht) (Real.exp_pos _)

theorem surgeryEnvelope_neg (N : ℕ) (t : ℝ) : surgeryEnvelope N (-t) = surgeryEnvelope N t := by
  have h : (-t) ^ (2 * N + 2) = t ^ (2 * N + 2) := Even.neg_pow ⟨N + 1, by ring⟩ t
  simp only [surgeryEnvelope, mul_neg, neg_neg, h]
  ring_nf

/-- The direction `g_j = g[e_j]`: `ψ`, `ψ cos(T·)`, `t ψ sin(T·)`. -/
def surgeryDirection (N : ℕ) (T : ℝ) (j : Fin 3) : ℝ → ℝ :=
  surgeryPerturbation N T (Pi.single j 1)

theorem surgeryDirection_zero (N : ℕ) (T t : ℝ) :
    surgeryDirection N T 0 t = surgeryEnvelope N t := by
  simp [surgeryDirection, surgeryPerturbation, surgeryEnvelope]

theorem surgeryDirection_one (N : ℕ) (T t : ℝ) :
    surgeryDirection N T 1 t = surgeryEnvelope N t * Real.cos (T * t) := by
  simp [surgeryDirection, surgeryPerturbation, surgeryEnvelope]

theorem surgeryDirection_two (N : ℕ) (T t : ℝ) :
    surgeryDirection N T 2 t = t * surgeryEnvelope N t * Real.sin (T * t) := by
  simp [surgeryDirection, surgeryPerturbation, surgeryEnvelope]; ring

theorem surgeryPerturbation_eq_sum (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) (t : ℝ) :
    surgeryPerturbation N T ε t = ∑ j, ε j * surgeryDirection N T j t := by
  rw [Fin.sum_univ_three, surgeryDirection_zero, surgeryDirection_one, surgeryDirection_two,
    surgeryPerturbation, surgeryEnvelope]
  ring

theorem integrable_exp_mul_surgeryPerturbation (N : ℕ) {T : ℝ} (hT : 0 ≤ T) (ε : Fin 3 → ℝ)
    (σ : ℝ) : Integrable fun t => Real.exp (σ * t) * surgeryPerturbation N T ε t := by
  have h := integrable_exp_mul_iteratedDeriv_surgeryPerturbation N 0 hT ε |σ|
  have hc := (contDiff_surgeryPerturbation N T ε).continuous
  refine h.mono' (by fun_prop) (Eventually.of_forall fun t => ?_)
  simp only [iteratedDeriv_zero, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
  rw [← abs_mul]; exact le_abs_self _

theorem integrable_exp_mul_mul_surgeryEnvelope (N : ℕ) (σ : ℝ) :
    Integrable fun t => Real.exp (σ * t) * (t * surgeryEnvelope N t) := by
  have h := integrable_exp_mul_iteratedDeriv_surgeryPerturbation N 0 le_rfl (Pi.single 0 1)
    (|σ| + 1)
  have hc : Continuous (surgeryEnvelope N) := by unfold surgeryEnvelope; fun_prop
  refine h.mono' (by fun_prop) (Eventually.of_forall fun t => ?_)
  have hd : surgeryPerturbation N 0 (Pi.single 0 1) t = surgeryEnvelope N t :=
    surgeryDirection_zero N 0 t
  simp only [iteratedDeriv_zero, hd, Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h1 : |t| ≤ Real.exp |t| := by linarith [Real.add_one_le_exp |t|]
  have h2 : Real.exp (σ * t) ≤ Real.exp (|σ| * |t|) :=
    Real.exp_le_exp.mpr (by rw [← abs_mul]; exact le_abs_self _)
  calc Real.exp (σ * t) * (|t| * |surgeryEnvelope N t|)
      ≤ Real.exp (|σ| * |t|) * (Real.exp |t| * |surgeryEnvelope N t|) := by gcongr
    _ = Real.exp ((|σ| + 1) * |t|) * |surgeryEnvelope N t| := by
        rw [add_mul, one_mul, Real.exp_add]; ring

theorem integrable_exp_mul_surgeryEnvelope (N : ℕ) (σ : ℝ) :
    Integrable fun t => Real.exp (σ * t) * surgeryEnvelope N t := by
  have h := integrable_exp_mul_surgeryPerturbation N le_rfl (Pi.single 0 1) σ
  refine h.congr (Eventually.of_forall fun t => ?_)
  simp only
  rw [show surgeryPerturbation N 0 (Pi.single 0 1) t = surgeryEnvelope N t from
    surgeryDirection_zero N 0 t]

/-! ## Linearity of the spectral value and of the mass -/

theorem surgeryTransform_eq_sum (N : ℕ) {T : ℝ} (hT : 0 ≤ T) (ε : Fin 3 → ℝ) (z : ℂ) :
    surgeryTransform N T ε z = ∑ j, (ε j : ℂ) * surgeryTransform N T (Pi.single j 1) z := by
  have hint : ∀ j, Integrable fun t : ℝ => cexp (-(I * z * t)) * (surgeryDirection N T j t : ℂ) :=
    fun j => by
      have := integrableOn_cexp_mul_iteratedDeriv N 0 hT (Pi.single j 1) (I * z)
      simpa only [iteratedDeriv_zero, surgeryDirection] using this
  calc surgeryTransform N T ε z
      = ∫ t : ℝ, ∑ j, (ε j : ℂ) * (cexp (-(I * z * t)) * (surgeryDirection N T j t : ℂ)) := by
        rw [surgeryTransform]
        congr 1; ext t
        rw [surgeryPerturbation_eq_sum]
        push_cast
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ j, ∫ t : ℝ, (ε j : ℂ) * (cexp (-(I * z * t)) * (surgeryDirection N T j t : ℂ)) :=
        integral_finsetSum _ fun j _ => (hint j).const_mul _
    _ = _ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul]
        rfl

/-- The mass functional `M(g) = 2a ∫₀^∞ e^{at} g`, `a = 1/4`. -/
def surgeryMass (N : ℕ) (T : ℝ) (ε : Fin 3 → ℝ) : ℝ :=
  1 / 2 * ∫ t in Ioi (0 : ℝ), Real.exp (1 / 4 * t) * surgeryPerturbation N T ε t

theorem surgeryMass_eq_sum (N : ℕ) {T : ℝ} (hT : 0 ≤ T) (ε : Fin 3 → ℝ) :
    surgeryMass N T ε = ∑ j, ε j * surgeryMass N T (Pi.single j 1) := by
  have hint : ∀ j, IntegrableOn (fun t => Real.exp (1 / 4 * t) * surgeryDirection N T j t) (Ioi 0) :=
    fun j => (integrable_exp_mul_surgeryPerturbation N hT (Pi.single j 1) (1 / 4)).integrableOn
  simp only [surgeryMass]
  calc 1 / 2 * ∫ t in Ioi (0 : ℝ), Real.exp (1 / 4 * t) * surgeryPerturbation N T ε t
      = 1 / 2 * ∫ t in Ioi (0 : ℝ), ∑ j, ε j * (Real.exp (1 / 4 * t) * surgeryDirection N T j t) := by
        congr 1
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        rw [surgeryPerturbation_eq_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
    _ = ∑ j, 1 / 2 * ∫ t in Ioi (0 : ℝ), ε j * (Real.exp (1 / 4 * t) * surgeryDirection N T j t) := by
        rw [integral_finsetSum _ fun j _ => (hint j).const_mul _, Finset.mul_sum]
    _ = _ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [integral_const_mul]
        simp only [surgeryDirection]
        ring

/-- **The two forms of the mass (3).** `∫₀^∞ e^{at}(a g - g') = 2a ∫₀^∞ e^{at} g`. -/
theorem integral_exp_mul_surgeryIncrement_sub (N : ℕ) {T : ℝ} (hT : 0 ≤ T) (ε : Fin 3 → ℝ) :
    ∫ t in Ioi (0 : ℝ), Real.exp (1 / 4 * t) *
      (1 / 4 * surgeryPerturbation N T ε t - deriv (surgeryPerturbation N T ε) t) =
      surgeryMass N T ε := by
  have hν : IntegrableOn (fun t => Real.exp (1 / 4 * t) * thetaRenewalIncrement t) (Ioi 0) := by
    have := integrableOn_exp_mul_thetaRenewalIncrement (-(1 / 4))
    simpa only [neg_mul, neg_neg] using this
  have hd : Integrable fun t => Real.exp (1 / 4 * t) *
      (1 / 4 * surgeryPerturbation N T ε t - deriv (surgeryPerturbation N T ε) t) := by
    have h1 := integrable_exp_mul_iteratedDeriv_surgeryPerturbation N 1 hT ε (1 / 4)
    have h0 := integrable_exp_mul_iteratedDeriv_surgeryPerturbation N 0 hT ε (1 / 4)
    have hc := (contDiff_surgeryPerturbation N T ε).continuous
    have hc' := continuous_deriv_surgeryPerturbation N T ε
    refine ((h0.const_mul (1 / 4)).add h1).mono' (by fun_prop) (Eventually.of_forall fun t => ?_)
    simp only [iteratedDeriv_zero, iteratedDeriv_one, Real.norm_eq_abs, abs_mul,
      abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (1 / 4 * t) ≤ Real.exp (1 / 4 * |t|) :=
      Real.exp_le_exp.mpr (by nlinarith [le_abs_self t])
    have hp := Real.exp_pos (1 / 4 * |t|)
    calc Real.exp (1 / 4 * t) * |1 / 4 * surgeryPerturbation N T ε t -
          deriv (surgeryPerturbation N T ε) t|
        ≤ Real.exp (1 / 4 * |t|) * (1 / 4 * |surgeryPerturbation N T ε t| +
          |deriv (surgeryPerturbation N T ε) t|) := by
          refine mul_le_mul he ?_ (abs_nonneg _) hp.le
          refine (abs_sub _ _).trans ?_
          rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
      _ = 1 / 4 * (Real.exp (1 / 4 * |t|) * |surgeryPerturbation N T ε t|) +
          Real.exp (1 / 4 * |t|) * |deriv (surgeryPerturbation N T ε) t| := by ring
  have h := integral_exp_mul_surgeryIncrement N hT ε
  have hsplit : ∫ t in Ioi (0 : ℝ), Real.exp (1 / 4 * t) * surgeryIncrement N T ε t =
      (∫ t in Ioi (0 : ℝ), Real.exp (1 / 4 * t) * thetaRenewalIncrement t) +
        ∫ t in Ioi (0 : ℝ), Real.exp (1 / 4 * t) *
          (1 / 4 * surgeryPerturbation N T ε t - deriv (surgeryPerturbation N T ε) t) := by
    rw [← integral_add hν hd.integrableOn]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    simp only [surgeryIncrement_eq]; ring
  rw [surgeryMass]
  linarith

/-! ## High-frequency limits -/

/-- `E_T(g₀) → 0`. -/
theorem tendsto_surgeryTransform_zero (N : ℕ) (v : ℝ) :
    Tendsto (fun T : ℝ => surgeryTransform N T (Pi.single 0 1) ((T : ℂ) + v * I)) atTop (𝓝 0) := by
  refine (tendsto_packet_fixed v (φ := surgeryEnvelope N)).congr fun T => ?_
  rw [surgeryTransform_eq_stripEval, stripEval]
  congr 1; ext x
  rw [show surgeryPerturbation N T (Pi.single 0 1) x = surgeryEnvelope N x from
    surgeryDirection_zero N T x]

/-- `E_T(g₁) → ½ ∫ e^{vx} ψ`. -/
theorem tendsto_surgeryTransform_one (N : ℕ) (v : ℝ) :
    Tendsto (fun T : ℝ => surgeryTransform N T (Pi.single 1 1) ((T : ℂ) + v * I)) atTop
      (𝓝 ((1 / 2 : ℂ) * ((∫ x, Real.exp (v * x) * surgeryEnvelope N x : ℝ) : ℂ))) := by
  refine (tendsto_packet_cos v (integrable_exp_mul_surgeryEnvelope N v)).congr fun T => ?_
  rw [surgeryTransform_eq_stripEval, stripEval]
  congr 1; ext x
  rw [show surgeryPerturbation N T (Pi.single 1 1) x = surgeryEnvelope N x * Real.cos (T * x) from
    surgeryDirection_one N T x]

/-- `E_T(g₂) → (-i/2) ∫ e^{vx} x ψ`. -/
theorem tendsto_surgeryTransform_two (N : ℕ) (v : ℝ) :
    Tendsto (fun T : ℝ => surgeryTransform N T (Pi.single 2 1) ((T : ℂ) + v * I)) atTop
      (𝓝 ((-I / 2) * ((∫ x, Real.exp (v * x) * (x * surgeryEnvelope N x) : ℝ) : ℂ))) := by
  refine (tendsto_packet_sin v (integrable_exp_mul_mul_surgeryEnvelope N v)).congr fun T => ?_
  rw [surgeryTransform_eq_stripEval, stripEval]
  congr 1; ext x
  rw [show surgeryPerturbation N T (Pi.single 2 1) x = x * surgeryEnvelope N x * Real.sin (T * x)
    from surgeryDirection_two N T x]

theorem tendsto_setIntegral_Ioi_mul_cos {w : ℝ → ℝ} (hw : IntegrableOn w (Ioi 0)) :
    Tendsto (fun u : ℝ => ∫ x in Ioi (0 : ℝ), w x * Real.cos (u * x)) atTop (𝓝 0) := by
  refine (tendsto_integral_mul_cos (hw.integrable_indicator measurableSet_Ioi)).congr fun u => ?_
  rw [← integral_indicator measurableSet_Ioi]
  congr 1; ext x
  by_cases hx : x ∈ Ioi (0 : ℝ) <;> simp [indicator, hx]

theorem tendsto_setIntegral_Ioi_mul_sin {w : ℝ → ℝ} (hw : IntegrableOn w (Ioi 0)) :
    Tendsto (fun u : ℝ => ∫ x in Ioi (0 : ℝ), w x * Real.sin (u * x)) atTop (𝓝 0) := by
  refine (tendsto_integral_mul_sin (hw.integrable_indicator measurableSet_Ioi)).congr fun u => ?_
  rw [← integral_indicator measurableSet_Ioi]
  congr 1; ext x
  by_cases hx : x ∈ Ioi (0 : ℝ) <;> simp [indicator, hx]

/-- The envelope mass `M(g₀) = ½ ∫₀^∞ e^{t/4} ψ`. -/
def surgeryEnvelopeMass (N : ℕ) : ℝ :=
  1 / 2 * ∫ t in Ioi (0 : ℝ), Real.exp (1 / 4 * t) * surgeryEnvelope N t

theorem surgeryMass_zero (N : ℕ) (T : ℝ) : surgeryMass N T (Pi.single 0 1) = surgeryEnvelopeMass N := by
  rw [surgeryMass, surgeryEnvelopeMass]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [show surgeryPerturbation N T (Pi.single 0 1) t = surgeryEnvelope N t from
    surgeryDirection_zero N T t]

theorem surgeryEnvelopeMass_pos (N : ℕ) : 0 < surgeryEnvelopeMass N := by
  refine mul_pos (by norm_num) (setIntegral_Ioi_pos
    (integrable_exp_mul_surgeryEnvelope N (1 / 4)).integrableOn fun t ht => ?_)
  exact mul_pos (Real.exp_pos _) (surgeryEnvelope_pos N (ne_of_gt ht))

/-- `M(g₁,T) → 0`. -/
theorem tendsto_surgeryMass_one (N : ℕ) :
    Tendsto (fun T => surgeryMass N T (Pi.single 1 1)) atTop (𝓝 0) := by
  have h := (tendsto_setIntegral_Ioi_mul_cos
    (integrable_exp_mul_surgeryEnvelope N (1 / 4)).integrableOn).const_mul (1 / 2)
  rw [mul_zero] at h
  refine h.congr fun T => ?_
  rw [surgeryMass]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [show surgeryPerturbation N T (Pi.single 1 1) t = surgeryEnvelope N t * Real.cos (T * t) from
    surgeryDirection_one N T t]
  ring

/-- `M(g₂,T) → 0`. -/
theorem tendsto_surgeryMass_two (N : ℕ) :
    Tendsto (fun T => surgeryMass N T (Pi.single 2 1)) atTop (𝓝 0) := by
  have h := (tendsto_setIntegral_Ioi_mul_sin
    (integrable_exp_mul_mul_surgeryEnvelope N (1 / 4)).integrableOn).const_mul (1 / 2)
  rw [mul_zero] at h
  refine h.congr fun T => ?_
  rw [surgeryMass]
  congr 1
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  rw [show surgeryPerturbation N T (Pi.single 2 1) t = t * surgeryEnvelope N t * Real.sin (T * t)
    from surgeryDirection_two N T t]
  ring

/-! ## Signs of the limiting coefficients -/

/-- Pairing `x` with `-x`: `∫ f = ∫₀^∞ (f(x) + f(-x))`. -/
theorem integral_eq_setIntegral_Ioi_add_neg {f : ℝ → ℝ} (hf : Integrable f) :
    ∫ x, f x = ∫ x in Ioi (0 : ℝ), (f x + f (-x)) := by
  have hneg : Integrable fun x => f (-x) := hf.comp_neg
  rw [integral_add hf.integrableOn hneg.integrableOn, ← intervalIntegral.integral_Iic_add_Ioi
    hf.integrableOn hf.integrableOn, add_comm]
  congr 1
  have h := integral_comp_neg_Iic 0 (fun x => f (-x))
  simp only [neg_neg, neg_zero] at h
  exact h

/-- `∫ e^{vx} ψ > 0`. -/
theorem integral_exp_mul_surgeryEnvelope_pos (N : ℕ) (v : ℝ) :
    0 < ∫ x, Real.exp (v * x) * surgeryEnvelope N x := by
  rw [integral_eq_setIntegral_Ioi_add_neg (integrable_exp_mul_surgeryEnvelope N v)]
  have hi : IntegrableOn (fun x => Real.exp (v * x) * surgeryEnvelope N x +
      Real.exp (v * -x) * surgeryEnvelope N (-x)) (Ioi 0) :=
    ((integrable_exp_mul_surgeryEnvelope N v).add
      (integrable_exp_mul_surgeryEnvelope N v).comp_neg).integrableOn
  refine setIntegral_Ioi_pos hi fun x hx => ?_
  have := surgeryEnvelope_pos N (ne_of_gt hx)
  rw [surgeryEnvelope_neg]
  positivity

/-- **The sine coefficient (4).** `∫ e^{vx} x ψ = 2 ∫₀^∞ x ψ(x) sinh(vx) > 0` for `v > 0`. -/
theorem integral_exp_mul_mul_surgeryEnvelope_eq (N : ℕ) (v : ℝ) :
    ∫ x, Real.exp (v * x) * (x * surgeryEnvelope N x) =
      2 * ∫ x in Ioi (0 : ℝ), x * surgeryEnvelope N x * Real.sinh (v * x) := by
  rw [integral_eq_setIntegral_Ioi_add_neg (integrable_exp_mul_mul_surgeryEnvelope N v),
    ← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [surgeryEnvelope_neg, Real.sinh_eq, mul_neg]
  ring

theorem integral_exp_mul_mul_surgeryEnvelope_pos (N : ℕ) {v : ℝ} (hv : 0 < v) :
    0 < ∫ x, Real.exp (v * x) * (x * surgeryEnvelope N x) := by
  rw [integral_exp_mul_mul_surgeryEnvelope_eq]
  have hi : IntegrableOn (fun x => x * surgeryEnvelope N x * Real.sinh (v * x)) (Ioi 0) := by
    have h := (((integrable_exp_mul_mul_surgeryEnvelope N v).sub
      (integrable_exp_mul_mul_surgeryEnvelope N (-v))).div_const 2).integrableOn (s := Ioi 0)
    refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
    simp only [Pi.sub_apply, Real.sinh_eq, neg_mul]
    ring
  refine mul_pos two_pos (setIntegral_Ioi_pos hi fun x hx => ?_)
  have h1 := surgeryEnvelope_pos N (ne_of_gt hx)
  have h2 : 0 < Real.sinh (v * x) := Real.sinh_pos_iff.mpr (mul_pos hv hx)
  have h3 : (0 : ℝ) < x := hx
  positivity

/-! ## The mass-neutral controllability isomorphism -/

/-- `E_T(g_j)` at `z_T = T + iv`. -/
def surgeryValue (N : ℕ) (v T : ℝ) (j : Fin 3) : ℂ :=
  surgeryTransform N T (Pi.single j 1) ((T : ℂ) + v * I)

/-- `E_T` of the mass-neutral combination `g_j - (M(g_j)/M(g₀)) g₀`. -/
def surgeryNeutralValue (N : ℕ) (v T : ℝ) (j : Fin 3) : ℂ :=
  surgeryValue N v T j -
    ((surgeryMass N T (Pi.single j 1) / surgeryEnvelopeMass N : ℝ) : ℂ) * surgeryValue N v T 0

/-- The real determinant `Im(conj(a) b)` of the two neutral spectral values. -/
def surgeryDet (N : ℕ) (v T : ℝ) : ℝ :=
  (conj (surgeryNeutralValue N v T 1) * surgeryNeutralValue N v T 2).im

/-- The cosine coefficient reaching the spectral value `w`. -/
def surgeryCoeffCos (N : ℕ) (v T : ℝ) (w : ℂ) : ℝ :=
  -(conj (surgeryNeutralValue N v T 2) * w).im / surgeryDet N v T

/-- The sine coefficient reaching the spectral value `w`. -/
def surgeryCoeffSin (N : ℕ) (v T : ℝ) (w : ℂ) : ℝ :=
  (conj (surgeryNeutralValue N v T 1) * w).im / surgeryDet N v T

/-- The mass-neutral coefficient vector reaching the spectral value `w` at `z_T`. -/
def surgeryCoeff (N : ℕ) (v T : ℝ) (w : ℂ) : Fin 3 → ℝ :=
  ![-(surgeryMass N T (Pi.single 1 1) * surgeryCoeffCos N v T w +
      surgeryMass N T (Pi.single 2 1) * surgeryCoeffSin N v T w) / surgeryEnvelopeMass N,
    surgeryCoeffCos N v T w, surgeryCoeffSin N v T w]

theorem tendsto_surgeryNeutralValue_one (N : ℕ) (v : ℝ) :
    Tendsto (fun T => surgeryNeutralValue N v T 1) atTop
      (𝓝 ((1 / 2 : ℂ) * ((∫ x, Real.exp (v * x) * surgeryEnvelope N x : ℝ) : ℂ))) := by
  have hm : Tendsto (fun T => ((surgeryMass N T (Pi.single 1 1) / surgeryEnvelopeMass N : ℝ) : ℂ))
      atTop (𝓝 0) := by
    have h := (tendsto_surgeryMass_one N).div_const (surgeryEnvelopeMass N)
    rw [zero_div] at h
    have := (Complex.continuous_ofReal.tendsto 0).comp h
    simpa [Function.comp_def] using this
  have h := (tendsto_surgeryTransform_one N v).sub (hm.mul (tendsto_surgeryTransform_zero N v))
  rw [mul_zero, sub_zero] at h
  exact h

theorem tendsto_surgeryNeutralValue_two (N : ℕ) (v : ℝ) :
    Tendsto (fun T => surgeryNeutralValue N v T 2) atTop
      (𝓝 ((-I / 2) * ((∫ x, Real.exp (v * x) * (x * surgeryEnvelope N x) : ℝ) : ℂ))) := by
  have hm : Tendsto (fun T => ((surgeryMass N T (Pi.single 2 1) / surgeryEnvelopeMass N : ℝ) : ℂ))
      atTop (𝓝 0) := by
    have h := (tendsto_surgeryMass_two N).div_const (surgeryEnvelopeMass N)
    rw [zero_div] at h
    have := (Complex.continuous_ofReal.tendsto 0).comp h
    simpa [Function.comp_def] using this
  have h := (tendsto_surgeryTransform_two N v).sub (hm.mul (tendsto_surgeryTransform_zero N v))
  rw [mul_zero, sub_zero] at h
  exact h

theorem surgeryLimitDet_ne_zero (N : ℕ) {v : ℝ} (hv : 0 < v) :
    (conj ((1 / 2 : ℂ) * ((∫ x, Real.exp (v * x) * surgeryEnvelope N x : ℝ) : ℂ)) *
      ((-I / 2) * ((∫ x, Real.exp (v * x) * (x * surgeryEnvelope N x) : ℝ) : ℂ))).im ≠ 0 := by
  have hα := integral_exp_mul_surgeryEnvelope_pos N v
  have hβ := integral_exp_mul_mul_surgeryEnvelope_pos N hv
  set α := ∫ x, Real.exp (v * x) * surgeryEnvelope N x
  set β := ∫ x, Real.exp (v * x) * (x * surgeryEnvelope N x)
  have : (conj ((1 / 2 : ℂ) * (α : ℂ)) * ((-I / 2) * (β : ℂ))).im = -(α * β / 4) := by
    simp [Complex.mul_im, Complex.mul_re, Complex.conj_ofReal]
    ring
  rw [this]
  have : 0 < α * β / 4 := by positivity
  linarith

/-- **Uniform high-frequency controllability.** For `v > 0` there are `K` and `U` such that for
every `T ≥ U` the spectral value at `z_T = T + iv` is a real-linear bijection from the mass-neutral
coefficient vectors onto `ℂ`: every `w` is reached by exactly one coefficient vector with
`M = 0`, namely `surgeryCoeff`, and its coefficients are bounded by `K |w|` uniformly in `T`. -/
theorem surgery_controllability (N : ℕ) {v : ℝ} (hv : 0 < v) :
    ∃ K U : ℝ, 0 ≤ K ∧ 0 ≤ U ∧ ∀ T, U ≤ T → ∀ w : ℂ,
      (surgeryMass N T (surgeryCoeff N v T w) = 0 ∧
        surgeryTransform N T (surgeryCoeff N v T w) ((T : ℂ) + v * I) = w) ∧
      (∀ ε : Fin 3 → ℝ, surgeryMass N T ε = 0 →
        surgeryTransform N T ε ((T : ℂ) + v * I) = w → ε = surgeryCoeff N v T w) ∧
      |surgeryCoeff N v T w 0| + |surgeryCoeff N v T w 1| + |surgeryCoeff N v T w 2| ≤
        K * ‖w‖ := by
  obtain ⟨K₁, U₁, hK₁, hsolve⟩ := exists_real_solve_bound (tendsto_surgeryNeutralValue_one N v)
    (tendsto_surgeryNeutralValue_two N v) (surgeryLimitDet_ne_zero N hv)
  have hm0 := surgeryEnvelopeMass_pos N
  obtain ⟨U₂, hU₂⟩ := eventually_atTop.mp ((tendsto_surgeryMass_one N).eventually
    (Metric.ball_mem_nhds 0 hm0))
  obtain ⟨U₃, hU₃⟩ := eventually_atTop.mp ((tendsto_surgeryMass_two N).eventually
    (Metric.ball_mem_nhds 0 hm0))
  refine ⟨2 * K₁, max (max U₁ U₂) (max U₃ 0), by positivity, le_max_of_le_right (le_max_right _ _),
    fun T hT w => ?_⟩
  have hT1 : U₁ ≤ T := le_trans (le_max_left _ _) (le_trans (le_max_left _ _) hT)
  have hT2 : U₂ ≤ T := le_trans (le_max_right _ _) (le_trans (le_max_left _ _) hT)
  have hT3 : U₃ ≤ T := le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hT)
  have hT0 : 0 ≤ T := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hT)
  obtain ⟨hdet, hbd⟩ := hsolve T hT1
  have hm1 : |surgeryMass N T (Pi.single 1 1)| < surgeryEnvelopeMass N := by
    simpa [Real.dist_eq] using hU₂ T hT2
  have hm2 : |surgeryMass N T (Pi.single 2 1)| < surgeryEnvelopeMass N := by
    simpa [Real.dist_eq] using hU₃ T hT3
  set a := surgeryNeutralValue N v T 1
  set b := surgeryNeutralValue N v T 2
  set m₁ := surgeryMass N T (Pi.single 1 1)
  set m₂ := surgeryMass N T (Pi.single 2 1)
  set m₀ := surgeryEnvelopeMass N
  set E₀ := surgeryValue N v T 0
  have hmass : ∀ ε : Fin 3 → ℝ, surgeryMass N T ε = ε 0 * m₀ + ε 1 * m₁ + ε 2 * m₂ := fun ε => by
    rw [surgeryMass_eq_sum N hT0, Fin.sum_univ_three, surgeryMass_zero]
  have htr : ∀ ε : Fin 3 → ℝ, surgeryMass N T ε = 0 →
      surgeryTransform N T ε ((T : ℂ) + v * I) = (ε 1 : ℂ) * a + (ε 2 : ℂ) * b := by
    intro ε hε
    have h0 : ε 0 = -(m₁ * ε 1 + m₂ * ε 2) / m₀ := by
      rw [hmass] at hε; field_simp; linarith
    rw [surgeryTransform_eq_sum N hT0, Fin.sum_univ_three, h0]
    simp only [a, b, surgeryNeutralValue, surgeryValue, m₁, m₂, m₀]
    push_cast
    field_simp
    ring
  have e0 : surgeryCoeff N v T w 0 =
      -(m₁ * surgeryCoeffCos N v T w + m₂ * surgeryCoeffSin N v T w) / m₀ := rfl
  have e1 : surgeryCoeff N v T w 1 = -(conj b * w).im / (conj a * b).im := rfl
  have e2 : surgeryCoeff N v T w 2 = (conj a * w).im / (conj a * b).im := rfl
  have hcoef : surgeryMass N T (surgeryCoeff N v T w) = 0 := by
    rw [hmass, e0, show surgeryCoeff N v T w 1 = surgeryCoeffCos N v T w from rfl,
      show surgeryCoeff N v T w 2 = surgeryCoeffSin N v T w from rfl]
    field_simp
    ring
  refine ⟨⟨hcoef, ?_⟩, fun ε hε hεw => ?_, ?_⟩
  · rw [htr _ hcoef, e1, e2]
    exact real_combination_eq hdet
  · rw [htr ε hε] at hεw
    have h2 : ε 2 = (conj a * w).im / (conj a * b).im := by
      rw [eq_div_iff hdet, ← hεw]
      simp [Complex.mul_im, Complex.mul_re]; ring
    have h1 : ε 1 = -(conj b * w).im / (conj a * b).im := by
      rw [eq_div_iff hdet, ← hεw]
      simp [Complex.mul_im, Complex.mul_re]; ring
    have h0 : ε 0 = -(m₁ * ε 1 + m₂ * ε 2) / m₀ := by
      have := hε; rw [hmass] at this; field_simp; linarith
    funext j
    fin_cases j
    · show ε 0 = surgeryCoeff N v T w 0
      rw [e0, h0, h1, h2]; rfl
    · show ε 1 = surgeryCoeff N v T w 1
      rw [e1, h1]
    · show ε 2 = surgeryCoeff N v T w 2
      rw [e2, h2]
  · rw [e0, e1, e2]
    set c₁ := -(conj b * w).im / (conj a * b).im
    set c₂ := (conj a * w).im / (conj a * b).im
    have hc : |c₁| + |c₂| ≤ K₁ * ‖w‖ := by
      simpa only [c₁, c₂, neg_div, abs_neg] using hbd w
    have hcc : surgeryCoeffCos N v T w = c₁ := rfl
    have hcs : surgeryCoeffSin N v T w = c₂ := rfl
    rw [hcc, hcs]
    have h0 : |-(m₁ * c₁ + m₂ * c₂) / m₀| ≤ |c₁| + |c₂| := by
      rw [abs_div, abs_neg, abs_of_pos hm0, div_le_iff₀ hm0]
      calc |m₁ * c₁ + m₂ * c₂| ≤ |m₁| * |c₁| + |m₂| * |c₂| := by
            rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
        _ ≤ m₀ * |c₁| + m₀ * |c₂| := by gcongr
        _ = (|c₁| + |c₂|) * m₀ := by ring
    linarith

/-! ## The limiting `3 × 3` matrix -/

/-- The real `3×3` matrix with rows `Re E_T`, `Im E_T`, `M` on the directions `g₀, g₁, g₂`. -/
def surgeryMatrix (N : ℕ) (v T : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  Matrix.of fun i j => ![(surgeryValue N v T j).re, (surgeryValue N v T j).im,
    surgeryMass N T (Pi.single j 1)] i

/-- **The matrix converges to an invertible matrix.** Its determinant tends to
`-(1/4) M(g₀) ∫ e^{vx}ψ ∫ e^{vx} x ψ`, which is nonzero for `v > 0`. -/
theorem tendsto_det_surgeryMatrix (N : ℕ) (v : ℝ) :
    Tendsto (fun T => (surgeryMatrix N v T).det) atTop
      (𝓝 (-(surgeryEnvelopeMass N * (∫ x, Real.exp (v * x) * surgeryEnvelope N x) *
        (∫ x, Real.exp (v * x) * (x * surgeryEnvelope N x)) / 4))) := by
  set α := ∫ x, Real.exp (v * x) * surgeryEnvelope N x
  set β := ∫ x, Real.exp (v * x) * (x * surgeryEnvelope N x)
  have hre := Complex.continuous_re.tendsto
  have him := Complex.continuous_im.tendsto
  have h0 := tendsto_surgeryTransform_zero N v
  have h1 := tendsto_surgeryTransform_one N v
  have h2 := tendsto_surgeryTransform_two N v
  have hR0 := (hre _).comp h0
  have hI0 := (him _).comp h0
  have hR1 := (hre _).comp h1
  have hI1 := (him _).comp h1
  have hR2 := (hre _).comp h2
  have hI2 := (him _).comp h2
  have hM0 : Tendsto (fun T => surgeryMass N T (Pi.single 0 1)) atTop (𝓝 (surgeryEnvelopeMass N)) := by
    simp only [surgeryMass_zero]; exact tendsto_const_nhds
  have hM1 := tendsto_surgeryMass_one N
  have hM2 := tendsto_surgeryMass_two N
  have hdet : ∀ T, (surgeryMatrix N v T).det =
      (surgeryValue N v T 0).re * (surgeryValue N v T 1).im * surgeryMass N T (Pi.single 2 1) -
      (surgeryValue N v T 0).re * (surgeryValue N v T 2).im * surgeryMass N T (Pi.single 1 1) -
      (surgeryValue N v T 1).re * (surgeryValue N v T 0).im * surgeryMass N T (Pi.single 2 1) +
      (surgeryValue N v T 1).re * (surgeryValue N v T 2).im * surgeryMass N T (Pi.single 0 1) +
      (surgeryValue N v T 2).re * (surgeryValue N v T 0).im * surgeryMass N T (Pi.single 1 1) -
      (surgeryValue N v T 2).re * (surgeryValue N v T 1).im * surgeryMass N T (Pi.single 0 1) := by
    intro T
    rw [Matrix.det_fin_three]
    simp [surgeryMatrix]
  simp only [hdet]
  have := ((((((hR0.mul hI1).mul hM2).sub ((hR0.mul hI2).mul hM1)).sub
    ((hR1.mul hI0).mul hM2)).add ((hR1.mul hI2).mul hM0)).add ((hR2.mul hI0).mul hM1)).sub
    ((hR2.mul hI1).mul hM0)
  convert this using 2
  · simp only [Function.comp_apply, surgeryValue]
  · simp [Complex.mul_re, Complex.mul_im]; ring

theorem surgeryMatrixLimit_ne_zero (N : ℕ) {v : ℝ} (hv : 0 < v) :
    -(surgeryEnvelopeMass N * (∫ x, Real.exp (v * x) * surgeryEnvelope N x) *
        (∫ x, Real.exp (v * x) * (x * surgeryEnvelope N x)) / 4) ≠ 0 := by
  have := surgeryEnvelopeMass_pos N
  have := integral_exp_mul_surgeryEnvelope_pos N v
  have := integral_exp_mul_mul_surgeryEnvelope_pos N hv
  have : 0 < surgeryEnvelopeMass N * (∫ x, Real.exp (v * x) * surgeryEnvelope N x) *
      (∫ x, Real.exp (v * x) * (x * surgeryEnvelope N x)) / 4 := by positivity
  linarith

end

end RHTower
