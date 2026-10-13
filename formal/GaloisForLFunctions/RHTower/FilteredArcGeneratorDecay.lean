import GaloisForLFunctions.RHTower.FilteredArcGenerator

/-!
# The filtered arc generators are in the decay class

Let `h = h_{K,u}` be the filtered generator of `FilteredArcGenerator`, with profile
`P(v) = e^{v/2} h(e^v) = Q_u(v) − (ǧ_K ⋆ Q_u)(v)`.

* **Edge asymptotics** (`abs_arcPairProfile_sub_le`). `Q_u(v) = 2√y e^{−|v|/2} + O(e^{−3|v|/2})`, uniformly
  on the arc. Proof: `(cosh v − c)^{−1/2} = √2 e^{−|v|/2} + O(e^{−3|v|/2})` for `|c| ≤ ½`
  (`abs_cosh_sub_rpow_sub_le`).
* **Decay** (`abs_filteredArcProfile_le`). `|P(v)| ≤ C_K e^{−3|v|/2}`. The leading edge term
  `2√y e^{−|v|/2}` is reproduced exactly by `ǧ_K ⋆`, because `∫ ǧ_K(w) e^{±w/2} dw = 1`. The remainders
  are controlled by `∫ |ǧ_K| e^{3|w|/2}`.
* Hence `|h(x)| ≤ 2C_K (1 + x²)^{−1}` (`abs_filteredArcVector_le`), `h(0) = 0`, and `h` is integrable.
* **Zero mean** (`integral_filteredArcVector_eq_zero`). `∫ h = 2 ∫ e^{v/2} P(v) dv = 0`.
  - For `0 ≤ λ < ½` Fubini gives `∫ e^{λv} P = (1 − e^{−K(¼−λ²)})² ∫ e^{λv} Q_u`.
  - The first factor is `≤ K²(¼ − λ²)²`, the second `≤ 20/(½ − λ)`.
  - Letting `λ → ½` by dominated convergence gives `∫ e^{v/2} P = 0`.

  This is the vanishing of the transform at `±i/2`, the second decay-class condition.
* `h'` is integrable (`integrable_filteredArcDeriv`), through the integrable two-variable kernel
  `ǧ_K(w) e^{−3w/2} ψ_u'(x e^{−w})` (`integrable_filteredArcDerivKernel`).
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

theorem integrable_rexp_neg_mul_abs {κ : ℝ} (hκ : 0 < κ) :
    Integrable fun u : ℝ => Real.exp (-(κ * |u|)) := by
  have h1 : IntegrableOn (fun u : ℝ => Real.exp (-(κ * |u|))) (Ioi 0) :=
    (integrableOn_exp_mul_Ioi (a := -κ) (by linarith) 0).congr_fun (fun u hu => by
      simp only; rw [abs_of_pos hu]; ring_nf) measurableSet_Ioi
  have h2 : IntegrableOn (fun u : ℝ => Real.exp (-(κ * |u|))) (Iic 0) :=
    (integrableOn_exp_mul_Iic hκ 0).congr_fun (fun u hu => by
      simp only; rw [abs_of_nonpos hu]; ring_nf) measurableSet_Iic
  have := h2.union h1
  rwa [Iic_union_Ioi, integrableOn_univ] at this

theorem integral_rexp_neg_mul_abs {κ : ℝ} (hκ : 0 < κ) :
    ∫ u : ℝ, Real.exp (-(κ * |u|)) = 2 / κ := by
  have h := integral_comp_abs (f := fun v => Real.exp (-(κ * v)))
  rw [h]
  have := integral_exp_mul_Ioi (a := -κ) (by linarith) 0
  simp only [mul_zero, Real.exp_zero] at this
  rw [show (fun x : ℝ => Real.exp (-(κ * x))) = fun x => Real.exp (-κ * x) by
    funext x; ring_nf, this]
  field_simp

/-- **Edge asymptotics of one Poisson factor**: for `|c| ≤ ½`,
`|(cosh v − c)^{−1/2} − √2 e^{−|v|/2}| ≤ 4 e^{−3|v|/2}`. -/
theorem abs_cosh_sub_rpow_sub_le {c : ℝ} (hc : |c| ≤ 1 / 2) (v : ℝ) :
    |(Real.cosh v - c) ^ (-1 / 2 : ℝ) - Real.sqrt 2 * Real.exp (-(|v| / 2))| ≤
      4 * Real.exp (-(3 * |v| / 2)) := by
  set E := Real.exp |v| with hE
  have hE0 : 0 < E := Real.exp_pos _
  have hE1 : 1 ≤ E := Real.one_le_exp (abs_nonneg v)
  have hcosh : Real.cosh v = (E + E⁻¹) / 2 := by
    rw [← Real.cosh_abs, Real.cosh_eq, hE, Real.exp_neg]
  have hc' := abs_le.mp hc
  have hEinv : 0 < E⁻¹ := inv_pos.mpr hE0
  have hEinv1 : E⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hE1
  set a := Real.cosh v - c with ha
  have hkey : 1 / 2 ≤ E / 4 + E⁻¹ / 2 := by
    have h1 : E * (E / 4 + E⁻¹ / 2 - 1 / 2) = (E - 1) ^ 2 / 4 + 1 / 4 := by
      field_simp; ring
    have h2 : 0 < E * (E / 4 + E⁻¹ / 2 - 1 / 2) := by rw [h1]; positivity
    have h3 := (pos_iff_pos_of_mul_pos h2).mp hE0
    linarith
  have ha4 : E / 4 ≤ a := by rw [ha, hcosh]; linarith [hc'.2]
  have ha0 : 0 < a := by linarith
  have hab : |E / 2 - a| ≤ 1 := by
    rw [ha, hcosh, abs_le]; constructor <;> linarith [hc'.1, hc'.2]
  set p := Real.sqrt a with hp
  set q := Real.sqrt (E / 2) with hq
  have hp0 : 0 < p := Real.sqrt_pos.mpr ha0
  have hq0 : 0 < q := Real.sqrt_pos.mpr (by positivity)
  have hp2 : p ^ 2 = a := Real.sq_sqrt ha0.le
  have hq2 : q ^ 2 = E / 2 := Real.sq_sqrt (by positivity)
  have hhalf : Real.exp (|v| / 2) ^ 2 = E := by rw [← Real.exp_nat_mul, hE]; ring_nf
  have hplow : Real.exp (|v| / 2) / 2 ≤ p := by
    rw [hp, Real.le_sqrt (by positivity) ha0.le, div_pow, hhalf]; linarith
  have hrpow : a ^ (-1 / 2 : ℝ) = p⁻¹ := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg ha0.le, ← Real.sqrt_eq_rpow]
  have hq' : Real.sqrt 2 * Real.exp (-(|v| / 2)) = q⁻¹ := by
    have hsq : q = Real.exp (|v| / 2) / Real.sqrt 2 := by
      rw [hq, Real.sqrt_div' _ (by norm_num : (0:ℝ) ≤ 2), hE, ← Real.exp_half]
    rw [hsq, inv_div, Real.exp_neg]; ring
  rw [hrpow, hq']
  have hident : p⁻¹ - q⁻¹ = (q ^ 2 - p ^ 2) / (p * q * (p + q)) := by
    field_simp; ring
  rw [hident, hp2, hq2, abs_div, abs_of_pos (by positivity : 0 < p * q * (p + q))]
  have hden : Real.exp (3 * |v| / 2) / 4 ≤ p * q * (p + q) := by
    have h1 : p * q * q ≤ p * q * (p + q) := by
      have : 0 < p * q := by positivity
      nlinarith
    have h2 : p * q * q = p * (E / 2) := by rw [mul_assoc, ← sq, hq2]
    have h3 : Real.exp (3 * |v| / 2) = Real.exp (|v| / 2) * E := by
      rw [hE, ← Real.exp_add]; ring_nf
    have h4 : Real.exp (|v| / 2) / 2 * (E / 2) ≤ p * (E / 2) :=
      mul_le_mul_of_nonneg_right hplow (by positivity)
    rw [h3]; nlinarith
  have hexp : 4 * Real.exp (-(3 * |v| / 2)) = 1 / (Real.exp (3 * |v| / 2) / 4) := by
    rw [Real.exp_neg]; field_simp
  rw [hexp]
  calc |E / 2 - a| / (p * q * (p + q)) ≤ 1 / (p * q * (p + q)) := by
        gcongr
    _ ≤ 1 / (Real.exp (3 * |v| / 2) / 4) := by
        gcongr

/-- The edge term `T_u(v) = 2√y e^{−|v|/2}` of the arc profile. -/
def arcPairTail (u : ArcParam) (v : ℝ) : ℝ :=
  2 * Real.sqrt (modularArcHeight u) * Real.exp (-(|v| / 2))

/-- **Edge asymptotics of the arc profile**: `|Q_u(v) − 2√y e^{−|v|/2}| ≤ 8 e^{−3|v|/2}`. -/
theorem abs_arcPairProfile_sub_le (u : ArcParam) (v : ℝ) :
    |arcPairProfile u v - arcPairTail u v| ≤ 8 * Real.exp (-(3 * |v| / 2)) := by
  have hu : |(u : ℝ)| ≤ 1 / 2 := abs_le.mpr ⟨by linarith [u.2.1], u.2.2⟩
  have hnu : |-(u : ℝ)| ≤ 1 / 2 := by rw [abs_neg]; exact hu
  have h1 := abs_cosh_sub_rpow_sub_le hu v
  have h2 := abs_cosh_sub_rpow_sub_le hnu v
  rw [sub_neg_eq_add] at h2
  have hy := modularArcHeight_pos u.2
  have hy1 := modularArcHeight_le_one u
  have hs : Real.sqrt (modularArcHeight u / 2) * Real.sqrt 2 = Real.sqrt (modularArcHeight u) := by
    rw [← Real.sqrt_mul (by positivity)]; congr 1; ring
  have hs1 : Real.sqrt (modularArcHeight u / 2) ≤ 1 := by
    rw [Real.sqrt_le_one]; linarith
  have hs0 : 0 ≤ Real.sqrt (modularArcHeight u / 2) := Real.sqrt_nonneg _
  have e : arcPairProfile u v - arcPairTail u v = Real.sqrt (modularArcHeight u / 2) *
      (((Real.cosh v + u) ^ (-1 / 2 : ℝ) - Real.sqrt 2 * Real.exp (-(|v| / 2))) +
        ((Real.cosh v - u) ^ (-1 / 2 : ℝ) - Real.sqrt 2 * Real.exp (-(|v| / 2)))) := by
    rw [arcPairProfile_eq, symCoshKernel, arcPairTail, ← hs]; ring
  rw [e, abs_mul, abs_of_nonneg hs0]
  have hsum := (abs_add_le _ _).trans (add_le_add h2 h1)
  have hpos : 0 ≤ 4 * Real.exp (-(3 * |v| / 2)) := by positivity
  calc Real.sqrt (modularArcHeight u / 2) * |((Real.cosh v + u) ^ (-1 / 2 : ℝ) -
        Real.sqrt 2 * Real.exp (-(|v| / 2))) + ((Real.cosh v - u) ^ (-1 / 2 : ℝ) -
          Real.sqrt 2 * Real.exp (-(|v| / 2)))|
      ≤ 1 * (4 * Real.exp (-(3 * |v| / 2)) + 4 * Real.exp (-(3 * |v| / 2))) :=
        mul_le_mul hs1 hsum (abs_nonneg _) zero_le_one
    _ = 8 * Real.exp (-(3 * |v| / 2)) := by ring

theorem continuous_arcPairTail (u : ArcParam) : Continuous (arcPairTail u) := by
  unfold arcPairTail; fun_prop

theorem abs_arcPairTail_le (u : ArcParam) (v : ℝ) : |arcPairTail u v| ≤ 2 := by
  have hy1 := modularArcHeight_le_one u
  unfold arcPairTail
  rw [abs_of_nonneg (by positivity)]
  have h1 : Real.sqrt (modularArcHeight u) ≤ 1 := Real.sqrt_le_one.mpr hy1
  have h2 : Real.exp (-(|v| / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := abs_nonneg v; linarith
  have h3 := Real.exp_pos (-(|v| / 2))
  have h4 := Real.sqrt_nonneg (modularArcHeight u)
  nlinarith [mul_le_mul h1 h2 h3.le zero_le_one]

theorem exp_neg_three_halves_le (v : ℝ) :
    Real.exp (-(3 * |v| / 2)) ≤ Real.exp (-(|v| / 2)) :=
  Real.exp_le_exp.mpr (by have := abs_nonneg v; linarith)

/-- `|Q_u(v)| ≤ 10 e^{−|v|/2}`. -/
theorem abs_arcPairProfile_le_exp (u : ArcParam) (v : ℝ) :
    |arcPairProfile u v| ≤ 10 * Real.exp (-(|v| / 2)) := by
  have h1 := abs_arcPairProfile_sub_le u v
  have hy1 := modularArcHeight_le_one u
  have hT : |arcPairTail u v| ≤ 2 * Real.exp (-(|v| / 2)) := by
    unfold arcPairTail
    rw [abs_of_nonneg (by positivity)]
    have : Real.sqrt (modularArcHeight u) ≤ 1 := Real.sqrt_le_one.mpr hy1
    have := Real.exp_pos (-(|v| / 2))
    nlinarith
  have h3 := exp_neg_three_halves_le v
  calc |arcPairProfile u v| = |(arcPairProfile u v - arcPairTail u v) + arcPairTail u v| := by ring_nf
    _ ≤ |arcPairProfile u v - arcPairTail u v| + |arcPairTail u v| := abs_add_le _ _
    _ ≤ 8 * Real.exp (-(|v| / 2)) + 2 * Real.exp (-(|v| / 2)) := by linarith
    _ = 10 * Real.exp (-(|v| / 2)) := by ring

theorem abs_arcPairProfile_le_ten (u : ArcParam) (v : ℝ) : |arcPairProfile u v| ≤ 10 := by
  have h := abs_arcPairProfile_le_exp u v
  have : Real.exp (-(|v| / 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]; have := abs_nonneg v; linarith
  nlinarith

/-! ### Decay of the filtered profile -/

/-- The weighted filter mass `M_K = ∫ (2e^{−K/4} g_K + e^{−K/2} g_{2K})(w) e^{3|w|/2} dw`. -/
def filterEdgeMass (K : ℝ) : ℝ := ∫ w, gaussPoleMajorant K w * Real.exp (3 / 2 * |w|)

theorem filterEdgeMass_nonneg {K : ℝ} (hK : 0 < K) : 0 ≤ filterEdgeMass K :=
  integral_nonneg fun w => mul_nonneg (gaussPoleMajorant_nonneg hK w) (Real.exp_pos _).le

theorem exp_neg_abs_sub_le (v w : ℝ) :
    Real.exp (-(3 * |v - w| / 2)) ≤ Real.exp (-(3 * |v| / 2)) * Real.exp (3 / 2 * |w|) := by
  rw [← Real.exp_add, Real.exp_le_exp]
  have := abs_sub_abs_le_abs_sub v w
  linarith

theorem abs_exp_sub_exp_abs_le {v : ℝ} (hv : 0 ≤ v) (w : ℝ) :
    |Real.exp (-((v - w) / 2)) - Real.exp (-(|v - w| / 2))| ≤
      Real.exp (-(3 * |v| / 2)) * Real.exp (3 / 2 * |w|) := by
  rw [abs_of_nonneg hv]
  rcases le_total w v with hw | hw
  · rw [abs_of_nonneg (by linarith : 0 ≤ v - w), sub_self, abs_zero]; positivity
  · rw [abs_of_nonpos (by linarith : v - w ≤ 0)]
    have h1 : Real.exp (-(-(v - w) / 2)) ≤ Real.exp (-((v - w) / 2)) :=
      Real.exp_le_exp.mpr (by linarith)
    rw [abs_of_nonneg (by linarith)]
    calc Real.exp (-((v - w) / 2)) - Real.exp (-(-(v - w) / 2))
        ≤ Real.exp (-((v - w) / 2)) := by linarith [Real.exp_pos (-(-(v - w) / 2))]
      _ ≤ Real.exp (-(3 * v / 2)) * Real.exp (3 / 2 * |w|) := by
          rw [← Real.exp_add, Real.exp_le_exp, abs_of_nonneg (by linarith : 0 ≤ w)]
          linarith

theorem filteredArcProfile_neg (K : ℝ) (u : ArcParam) (v : ℝ) :
    filteredArcProfile K u (-v) = filteredArcProfile K u v := by
  unfold filteredArcProfile
  rw [arcPairProfile_neg]
  congr 1
  rw [← integral_neg_eq_self (fun w => poleFilter K w * arcPairProfile u (-v - w)) volume]
  refine integral_congr_ae (Eventually.of_forall fun w => ?_)
  simp only
  rw [poleFilter_neg, show -v - -w = -(v - w) by ring, arcPairProfile_neg]

theorem integrable_poleFilter_mul_bdd {K : ℝ} (hK : 0 < K) {f : ℝ → ℝ} (hf : Continuous f)
    {C : ℝ} (hC : ∀ w, |f w| ≤ C) : Integrable fun w => poleFilter K w * f w :=
  (integrable_poleFilter hK).mul_bdd hf.aestronglyMeasurable
    (Eventually.of_forall fun w => by rw [Real.norm_eq_abs]; exact hC w)

theorem integrable_gaussPoleMajorant_mul_exp_three_halves {K : ℝ} (hK : 0 < K) :
    Integrable fun w => gaussPoleMajorant K w * Real.exp (3 / 2 * |w|) :=
  integrable_gaussPoleMajorant_mul_exp_abs hK (3 / 2)

theorem abs_filteredArcProfile_le_of_nonneg {K : ℝ} (hK : 0 < K) (u : ArcParam) {v : ℝ}
    (hv : 0 ≤ v) :
    |filteredArcProfile K u v| ≤ (8 + 10 * filterEdgeMass K) * Real.exp (-(3 * |v| / 2)) := by
  set y := modularArcHeight u
  set E : ℝ → ℝ := fun t => arcPairProfile u t - arcPairTail u t with hEdef
  have hEc : Continuous E := (continuous_arcPairProfile u).sub (continuous_arcPairTail u)
  have hEb : ∀ t, |E t| ≤ 12 := fun t => by
    have h1 := abs_arcPairProfile_le_ten u t
    have h2 := abs_arcPairTail_le u t
    simp only [hEdef]
    calc |arcPairProfile u t - arcPairTail u t| ≤ |arcPairProfile u t| + |arcPairTail u t| :=
          abs_sub _ _
      _ ≤ 12 := by linarith
  have hiE : Integrable fun w => poleFilter K w * E (v - w) :=
    integrable_poleFilter_mul_bdd hK (hEc.comp (by fun_prop)) fun w => hEb _
  have hiT : Integrable fun w => poleFilter K w * arcPairTail u (v - w) :=
    integrable_poleFilter_mul_bdd hK ((continuous_arcPairTail u).comp (by fun_prop))
      fun w => abs_arcPairTail_le u _
  set c := 2 * Real.sqrt y with hc
  have hiX : Integrable fun w => poleFilter K w * (c * Real.exp (-((v - w) / 2))) := by
    refine ((integrable_poleFilter_mul_rexp hK (1 / 2)).const_mul
      (c * Real.exp (-(v / 2)))).congr (Eventually.of_forall fun w => ?_)
    simp only
    rw [show -((v - w) / 2) = -(v / 2) + w * (1 / 2) by ring, Real.exp_add]; ring
  -- the edge term is reproduced by the filter
  have hT : arcPairTail u v = ∫ w, poleFilter K w * (c * Real.exp (-((v - w) / 2))) := by
    have e : ∀ w, poleFilter K w * (c * Real.exp (-((v - w) / 2))) =
        c * Real.exp (-(v / 2)) * (poleFilter K w * Real.exp (w * (1 / 2))) := fun w => by
      rw [show -((v - w) / 2) = -(v / 2) + w * (1 / 2) by ring, Real.exp_add]; ring
    simp_rw [e]
    rw [integral_const_mul, integral_poleFilter_mul_exp_half hK (1 / 2) (by norm_num), mul_one,
      arcPairTail, abs_of_nonneg hv]
  have hsplit : filteredArcProfile K u v = E v - (∫ w, poleFilter K w * E (v - w)) +
      ∫ w, poleFilter K w * (c * (Real.exp (-((v - w) / 2)) - Real.exp (-(|v - w| / 2)))) := by
    have h1 : ∫ w, poleFilter K w * arcPairProfile u (v - w) =
        (∫ w, poleFilter K w * E (v - w)) + ∫ w, poleFilter K w * arcPairTail u (v - w) := by
      rw [← integral_add hiE hiT]
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      simp only [hEdef]; ring
    have h2 : ∫ w, poleFilter K w * (c * (Real.exp (-((v - w) / 2)) -
        Real.exp (-(|v - w| / 2)))) = (∫ w, poleFilter K w * (c * Real.exp (-((v - w) / 2)))) -
          ∫ w, poleFilter K w * arcPairTail u (v - w) := by
      rw [← integral_sub hiX hiT]
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      simp only [arcPairTail, hc]; ring
    unfold filteredArcProfile
    rw [h1, h2, ← hT]
    simp only [hEdef]; ring
  have hM := integrable_gaussPoleMajorant_mul_exp_three_halves hK
  -- the remainder convolution
  have hb1 : |∫ w, poleFilter K w * E (v - w)| ≤
      8 * Real.exp (-(3 * |v| / 2)) * filterEdgeMass K := by
    rw [filterEdgeMass, ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono hiE.abs
      (hM.const_mul _) fun w => ?_)
    simp only
    rw [abs_mul]
    have h1 := abs_poleFilter_le hK w
    have h2 : |E (v - w)| ≤ 8 * Real.exp (-(3 * |v - w| / 2)) := abs_arcPairProfile_sub_le u _
    have h3 := exp_neg_abs_sub_le v w
    have h4 := gaussPoleMajorant_nonneg hK w
    calc |poleFilter K w| * |E (v - w)|
        ≤ gaussPoleMajorant K w * (8 * (Real.exp (-(3 * |v| / 2)) *
            Real.exp (3 / 2 * |w|))) :=
          mul_le_mul h1 (h2.trans (by linarith)) (abs_nonneg _) h4
      _ = 8 * Real.exp (-(3 * |v| / 2)) * (gaussPoleMajorant K w * Real.exp (3 / 2 * |w|)) := by
          ring
  -- the edge defect
  have hiD : Integrable fun w => poleFilter K w *
      (c * (Real.exp (-((v - w) / 2)) - Real.exp (-(|v - w| / 2)))) := by
    refine (hiX.sub hiT).congr (Eventually.of_forall fun w => ?_)
    simp only [Pi.sub_apply, arcPairTail, hc]; ring
  have hc2 : c ≤ 2 := by
    have : Real.sqrt y ≤ 1 := Real.sqrt_le_one.mpr (modularArcHeight_le_one u)
    rw [hc]; linarith
  have hc0 : 0 ≤ c := by rw [hc]; positivity
  have hb2 : |∫ w, poleFilter K w * (c * (Real.exp (-((v - w) / 2)) -
      Real.exp (-(|v - w| / 2))))| ≤ 2 * Real.exp (-(3 * |v| / 2)) * filterEdgeMass K := by
    rw [filterEdgeMass, ← integral_const_mul]
    refine (abs_integral_le_integral_abs).trans (integral_mono hiD.abs
      (hM.const_mul _) fun w => ?_)
    simp only
    rw [abs_mul, abs_mul, abs_of_nonneg hc0]
    have h1 := abs_poleFilter_le hK w
    have h2 := abs_exp_sub_exp_abs_le hv w
    have h4 := gaussPoleMajorant_nonneg hK w
    have h5 : 0 ≤ Real.exp (-(3 * |v| / 2)) * Real.exp (3 / 2 * |w|) := by positivity
    calc |poleFilter K w| * (c * |Real.exp (-((v - w) / 2)) - Real.exp (-(|v - w| / 2))|)
        ≤ gaussPoleMajorant K w * (2 * (Real.exp (-(3 * |v| / 2)) * Real.exp (3 / 2 * |w|))) :=
          mul_le_mul h1 (mul_le_mul hc2 h2 (abs_nonneg _) (by norm_num)) (by positivity) h4
      _ = 2 * Real.exp (-(3 * |v| / 2)) * (gaussPoleMajorant K w * Real.exp (3 / 2 * |w|)) := by
          ring
  have hb0 : |E v| ≤ 8 * Real.exp (-(3 * |v| / 2)) := abs_arcPairProfile_sub_le u v
  rw [hsplit]
  calc |E v - (∫ w, poleFilter K w * E (v - w)) + ∫ w, poleFilter K w *
        (c * (Real.exp (-((v - w) / 2)) - Real.exp (-(|v - w| / 2))))|
      ≤ |E v| + |∫ w, poleFilter K w * E (v - w)| + |∫ w, poleFilter K w *
        (c * (Real.exp (-((v - w) / 2)) - Real.exp (-(|v - w| / 2))))| := by
        exact (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
    _ ≤ (8 + 10 * filterEdgeMass K) * Real.exp (-(3 * |v| / 2)) := by nlinarith

/-- **The filtered profile is in the decay class**: `|P(v)| ≤ C_K e^{−3|v|/2}`. -/
theorem abs_filteredArcProfile_le {K : ℝ} (hK : 0 < K) (u : ArcParam) (v : ℝ) :
    |filteredArcProfile K u v| ≤ (8 + 10 * filterEdgeMass K) * Real.exp (-(3 * |v| / 2)) := by
  rcases le_total 0 v with hv | hv
  · exact abs_filteredArcProfile_le_of_nonneg hK u hv
  · rw [← filteredArcProfile_neg, ← abs_neg v]
    exact abs_filteredArcProfile_le_of_nonneg hK u (by linarith)

/-! ### The generator on the line -/

theorem continuous_filteredArcVector {K : ℝ} (hK : 0 < K) (u : ArcParam) :
    Continuous (filteredArcVector K u) :=
  continuous_iff_continuousAt.mpr fun x => (hasDerivAt_filteredArcVector hK u x).continuousAt

theorem filteredArcVector_zero {K : ℝ} (hK : 0 < K) (u : ArcParam) :
    filteredArcVector K u 0 = 0 := by
  unfold filteredArcVector
  have e : ∀ w, poleFilter K w * (Real.exp (-(w / 2)) * arcPairVector u (0 * Real.exp (-w))) =
      arcPairVector u 0 * (poleFilter K w * Real.exp (w * (-(1 / 2)))) := fun w => by
    rw [zero_mul, show w * -(1 / 2) = -(w / 2) by ring]; ring
  simp_rw [e]
  rw [integral_const_mul, integral_poleFilter_mul_exp_half hK (-(1 / 2)) (by norm_num), mul_one,
    sub_self]

theorem filteredArcVector_of_pos (K : ℝ) (u : ArcParam) {x : ℝ} (hx : 0 < x) :
    filteredArcVector K u x =
      Real.exp (-(Real.log x / 2)) * filteredArcProfile K u (Real.log x) := by
  rw [← exp_half_mul_filteredArcVector, Real.exp_log hx, ← mul_assoc, ← Real.exp_add]
  simp

theorem abs_filteredArcVector_le {K : ℝ} (hK : 0 < K) (u : ArcParam) (x : ℝ) :
    |filteredArcVector K u x| ≤ 2 * (8 + 10 * filterEdgeMass K) * (1 + x ^ 2)⁻¹ := by
  set C := 8 + 10 * filterEdgeMass K
  have hC : 0 ≤ C := by have := filterEdgeMass_nonneg hK; positivity
  have hpos : ∀ x : ℝ, 0 < x → |filteredArcVector K u x| ≤ 2 * C * (1 + x ^ 2)⁻¹ := by
    intro x hx
    rw [filteredArcVector_of_pos K u hx, abs_mul, abs_of_pos (Real.exp_pos _)]
    set v := Real.log x
    have hP := abs_filteredArcProfile_le hK u v
    have hev : Real.exp v = x := Real.exp_log hx
    have h1 : Real.exp (-(v / 2)) * |filteredArcProfile K u v| ≤
        C * Real.exp (-(v / 2) - 3 * |v| / 2) := by
      rw [sub_eq_add_neg, Real.exp_add, show -(3 * |v| / 2) = -(3 * |v| / 2) by rfl]
      nlinarith [Real.exp_pos (-(v / 2))]
    refine h1.trans ?_
    rcases le_total 0 v with hv | hv
    · rw [abs_of_nonneg hv, show -(v / 2) - 3 * v / 2 = -(2 * v) by ring, Real.exp_neg,
        show (2 : ℝ) * v = ((2 : ℕ) : ℝ) * v by norm_num, Real.exp_nat_mul, hev]
      have hx1 : 1 ≤ x := by rw [← hev]; exact Real.one_le_exp hv
      have key : (x ^ 2)⁻¹ ≤ 2 * (1 + x ^ 2)⁻¹ := by
        rw [show 2 * (1 + x ^ 2)⁻¹ = 2 / (1 + x ^ 2) by ring, inv_eq_one_div,
          div_le_div_iff₀ (by positivity) (by positivity)]
        nlinarith
      calc C * (x ^ 2)⁻¹ ≤ C * (2 * (1 + x ^ 2)⁻¹) := mul_le_mul_of_nonneg_left key hC
        _ = 2 * C * (1 + x ^ 2)⁻¹ := by ring
    · rw [abs_of_nonpos hv, show -(v / 2) - 3 * -v / 2 = v by ring, hev]
      have hx1 : x ≤ 1 := by rw [← hev]; exact Real.exp_le_one_iff.mpr hv
      have key : x ≤ 2 * (1 + x ^ 2)⁻¹ := by
        rw [show 2 * (1 + x ^ 2)⁻¹ = 2 / (1 + x ^ 2) by ring, le_div_iff₀ (by positivity)]
        nlinarith
      calc C * x ≤ C * (2 * (1 + x ^ 2)⁻¹) := mul_le_mul_of_nonneg_left key hC
        _ = 2 * C * (1 + x ^ 2)⁻¹ := by ring
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have := hpos (-x) (by linarith)
    rwa [filteredArcVector_neg, neg_sq] at this
  · rw [hx, filteredArcVector_zero hK, abs_zero]; positivity
  · exact hpos x hx

theorem integrable_filteredArcVector {K : ℝ} (hK : 0 < K) (u : ArcParam) :
    Integrable (filteredArcVector K u) :=
  (integrable_inv_one_add_sq.const_mul (2 * (8 + 10 * filterEdgeMass K))).mono'
    (continuous_filteredArcVector hK u).aestronglyMeasurable
    (Eventually.of_forall fun x => by
      rw [Real.norm_eq_abs]; exact abs_filteredArcVector_le hK u x)

/-! ### Zero mean -/

theorem setIntegral_Ioi_eq_integral_exp_mul (g : ℝ → ℝ) :
    ∫ x in Ioi 0, g x = ∫ v, Real.exp v * g (Real.exp v) := by
  have h := integral_image_eq_integral_abs_deriv_smul MeasurableSet.univ
    (fun x _ => (Real.hasDerivAt_exp x).hasDerivWithinAt) Real.exp_injective.injOn g
  rw [Set.image_univ, Real.range_exp, Measure.restrict_univ] at h
  rw [h]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [abs_of_pos (Real.exp_pos v), smul_eq_mul]

theorem continuous_filteredArcProfile {K : ℝ} (hK : 0 < K) (u : ArcParam) :
    Continuous (filteredArcProfile K u) := by
  have e : filteredArcProfile K u = fun v => Real.exp (v / 2) * filteredArcVector K u (Real.exp v) :=
    funext fun v => (exp_half_mul_filteredArcVector K u v).symm
  rw [e]
  exact (by fun_prop : Continuous fun v : ℝ => Real.exp (v / 2)).mul
    ((continuous_filteredArcVector hK u).comp Real.continuous_exp)

theorem one_sub_integral_poleFilter_mul_rexp {K : ℝ} (hK : 0 < K) (l : ℝ) :
    1 - ∫ w, poleFilter K w * Real.exp (w * l) = (1 - Real.exp (-(K * (1 / 4 - l ^ 2)))) ^ 2 := by
  rw [integral_poleFilter_mul_rexp hK]
  have a1 : Real.exp (-(K / 4)) * Real.exp (K * l ^ 2) = Real.exp (-(K * (1 / 4 - l ^ 2))) := by
    rw [← Real.exp_add]; congr 1; ring
  have a2 : Real.exp (-(K / 2)) * Real.exp (2 * K * l ^ 2) =
      Real.exp (-(K * (1 / 4 - l ^ 2))) ^ 2 := by
    rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  rw [mul_assoc, a1, a2]; ring

theorem abs_exp_mul_le {l v : ℝ} (hl : 0 ≤ l) : |Real.exp (l * v)| ≤ Real.exp (l * |v|) := by
  rw [abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (le_abs_self v) hl)

/-- **The tilted moments of the filtered profile.** For `0 ≤ λ < ½`,
`∫ e^{λv} P(v) dv = (1 − ∫ ǧ_K(w) e^{λw} dw) ∫ e^{λv} Q_u(v) dv`. -/
theorem integral_exp_mul_filteredArcProfile {K : ℝ} (hK : 0 < K) (u : ArcParam) {l : ℝ}
    (hl0 : 0 ≤ l) (hl : l < 1 / 2) :
    ∫ v, Real.exp (l * v) * filteredArcProfile K u v =
      (1 - ∫ w, poleFilter K w * Real.exp (w * l)) *
        ∫ v, Real.exp (l * v) * arcPairProfile u v := by
  have hκ : 0 < 1 / 2 - l := by linarith
  have hg : Integrable fun v => Real.exp (l * v) * arcPairProfile u v := by
    refine ((integrable_rexp_neg_mul_abs hκ).const_mul 10).mono'
      ((by fun_prop : Continuous fun v : ℝ => Real.exp (l * v)).mul
        (continuous_arcPairProfile u)).aestronglyMeasurable
      (Eventually.of_forall fun v => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := abs_exp_mul_le (v := v) hl0
    have h2 := abs_arcPairProfile_le_exp u v
    calc |Real.exp (l * v)| * |arcPairProfile u v|
        ≤ Real.exp (l * |v|) * (10 * Real.exp (-(|v| / 2))) :=
          mul_le_mul h1 h2 (abs_nonneg _) (Real.exp_pos _).le
      _ = 10 * Real.exp (-((1 / 2 - l) * |v|)) := by
          rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hf := integrable_poleFilter_mul_rexp hK l
  have hconv := hf.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hg
  simp only [ContinuousLinearMap.mul_apply'] at hconv
  have hF : ∀ v w, poleFilter K w * Real.exp (w * l) *
      (Real.exp (l * (v - w)) * arcPairProfile u (v - w)) =
      Real.exp (l * v) * (poleFilter K w * arcPairProfile u (v - w)) := fun v w => by
    have : Real.exp (w * l) * Real.exp (l * (v - w)) = Real.exp (l * v) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← this]; ring
  have hinner : ∀ v, ∫ w, poleFilter K w * Real.exp (w * l) *
      (Real.exp (l * (v - w)) * arcPairProfile u (v - w)) =
      Real.exp (l * v) * ∫ w, poleFilter K w * arcPairProfile u (v - w) := fun v => by
    simp_rw [hF v]; rw [integral_const_mul]
  have hconvI : Integrable fun v =>
      Real.exp (l * v) * ∫ w, poleFilter K w * arcPairProfile u (v - w) :=
    hconv.integral_prod_left.congr (Eventually.of_forall hinner)
  have hswap := integral_integral_swap (f := fun v w => poleFilter K w * Real.exp (w * l) *
    (Real.exp (l * (v - w)) * arcPairProfile u (v - w))) hconv
  have hsecond : ∫ v, Real.exp (l * v) * ∫ w, poleFilter K w * arcPairProfile u (v - w) =
      (∫ w, poleFilter K w * Real.exp (w * l)) * ∫ v, Real.exp (l * v) * arcPairProfile u v := by
    have h1 : ∫ v, Real.exp (l * v) * ∫ w, poleFilter K w * arcPairProfile u (v - w) =
        ∫ v, ∫ w, poleFilter K w * Real.exp (w * l) *
          (Real.exp (l * (v - w)) * arcPairProfile u (v - w)) :=
      integral_congr_ae (Eventually.of_forall fun v => (hinner v).symm)
    rw [h1, hswap]
    have h2 : ∀ w, ∫ v, poleFilter K w * Real.exp (w * l) *
        (Real.exp (l * (v - w)) * arcPairProfile u (v - w)) =
        poleFilter K w * Real.exp (w * l) * ∫ v, Real.exp (l * v) * arcPairProfile u v := by
      intro w
      rw [integral_const_mul, integral_sub_right_eq_self
        (fun v => Real.exp (l * v) * arcPairProfile u v) w]
    simp_rw [h2]
    rw [integral_mul_const]
  unfold filteredArcProfile
  simp_rw [mul_sub]
  rw [integral_sub hg hconvI, hsecond]; ring

/-- **The filtered profile has zero `e^{v/2}`-moment.** This is the vanishing of its transform at
`±i/2`. -/
theorem integral_exp_half_mul_filteredArcProfile {K : ℝ} (hK : 0 < K) (u : ArcParam) :
    ∫ v, Real.exp (v / 2) * filteredArcProfile K u v = 0 := by
  set C := 8 + 10 * filterEdgeMass K
  set I : ℝ → ℝ := fun l => ∫ v, Real.exp (l * v) * filteredArcProfile K u v with hIdef
  have hP := continuous_filteredArcProfile hK u
  -- bound for `0 ≤ λ < ½`
  have hbound : ∀ l, 0 ≤ l → l < 1 / 2 → |I l| ≤ 20 * K ^ 2 * (1 / 2 - l) := by
    intro l hl0 hl
    have hκ : 0 < 1 / 2 - l := by linarith
    rw [hIdef]
    simp only
    rw [integral_exp_mul_filteredArcProfile hK u hl0 hl, one_sub_integral_poleFilter_mul_rexp hK,
      abs_mul, abs_of_nonneg (sq_nonneg _)]
    have hQ : |∫ v, Real.exp (l * v) * arcPairProfile u v| ≤ 20 / (1 / 2 - l) := by
      refine (abs_integral_le_integral_abs).trans ?_
      calc ∫ v, |Real.exp (l * v) * arcPairProfile u v|
          ≤ ∫ v, 10 * Real.exp (-((1 / 2 - l) * |v|)) := by
            refine integral_mono_of_nonneg (Eventually.of_forall fun v => abs_nonneg _)
              ((integrable_rexp_neg_mul_abs hκ).const_mul 10) (Eventually.of_forall fun v => ?_)
            dsimp only
            rw [abs_mul]
            calc |Real.exp (l * v)| * |arcPairProfile u v|
                ≤ Real.exp (l * |v|) * (10 * Real.exp (-(|v| / 2))) :=
                  mul_le_mul (abs_exp_mul_le hl0) (abs_arcPairProfile_le_exp u v) (abs_nonneg _)
                    (Real.exp_pos _).le
              _ = 10 * Real.exp (-((1 / 2 - l) * |v|)) := by
                  rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
        _ = 20 / (1 / 2 - l) := by
            rw [integral_const_mul, integral_rexp_neg_mul_abs hκ]; ring
    have hE : 0 ≤ 1 - Real.exp (-(K * (1 / 4 - l ^ 2))) := by
      have : Real.exp (-(K * (1 / 4 - l ^ 2))) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        have : 0 ≤ 1 / 4 - l ^ 2 := by nlinarith
        have := mul_nonneg hK.le this; linarith
      linarith
    have hE2 : 1 - Real.exp (-(K * (1 / 4 - l ^ 2))) ≤ K * (1 / 4 - l ^ 2) := by
      have := Real.add_one_le_exp (-(K * (1 / 4 - l ^ 2))); linarith
    have hsq : (1 - Real.exp (-(K * (1 / 4 - l ^ 2)))) ^ 2 ≤ (K * (1 / 4 - l ^ 2)) ^ 2 :=
      pow_le_pow_left₀ hE hE2 2
    calc (1 - Real.exp (-(K * (1 / 4 - l ^ 2)))) ^ 2 * |∫ v, Real.exp (l * v) * arcPairProfile u v|
        ≤ (K * (1 / 4 - l ^ 2)) ^ 2 * (20 / (1 / 2 - l)) :=
          mul_le_mul hsq hQ (abs_nonneg _) (sq_nonneg _)
      _ = 20 * K ^ 2 * (1 / 2 - l) * (1 / 2 + l) ^ 2 := by
          have hne : (1 / 2 - l) ≠ 0 := hκ.ne'
          rw [show (1 : ℝ) / 4 - l ^ 2 = (1 / 2 - l) * (1 / 2 + l) by ring]
          field_simp
      _ ≤ 20 * K ^ 2 * (1 / 2 - l) * 1 := by
          gcongr
          nlinarith
      _ = 20 * K ^ 2 * (1 / 2 - l) := mul_one _
  -- `I(λ) → 0` as `λ → ½⁻`
  have hev : ∀ᶠ l in 𝓝[<] (1 / 2 : ℝ), l ∈ Ioo (0 : ℝ) (1 / 2) :=
    Ioo_mem_nhdsLT (by norm_num)
  have hzero : Tendsto I (𝓝[<] (1 / 2 : ℝ)) (𝓝 0) := by
    refine squeeze_zero_norm' (a := fun l => 20 * K ^ 2 * (1 / 2 - l)) ?_ ?_
    · filter_upwards [hev] with l hl
      rw [Real.norm_eq_abs]; exact hbound l hl.1.le hl.2
    · have hc : Continuous fun l : ℝ => 20 * K ^ 2 * (1 / 2 - l) := by fun_prop
      have h := hc.tendsto (1 / 2 : ℝ)
      simp only [sub_self, mul_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
  -- `I(λ) → I(½)` by dominated convergence
  have hlim : Tendsto I (𝓝[<] (1 / 2 : ℝ)) (𝓝 (I (1 / 2))) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun v => C * Real.exp (-(1 * |v|))) ?_ ?_ ?_ ?_
    · exact Eventually.of_forall fun l =>
        ((by fun_prop : Continuous fun v : ℝ => Real.exp (l * v)).mul hP).aestronglyMeasurable
    · filter_upwards [hev] with l hl
      refine Eventually.of_forall fun v => ?_
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |Real.exp (l * v)| ≤ Real.exp (|v| / 2) := by
        rw [abs_of_pos (Real.exp_pos _)]
        refine Real.exp_le_exp.mpr ?_
        have := le_abs_self v
        have := abs_nonneg v
        nlinarith [hl.1, hl.2]
      have h2 := abs_filteredArcProfile_le hK u v
      calc |Real.exp (l * v)| * |filteredArcProfile K u v|
          ≤ Real.exp (|v| / 2) * (C * Real.exp (-(3 * |v| / 2))) :=
            mul_le_mul h1 h2 (abs_nonneg _) (Real.exp_pos _).le
        _ = C * Real.exp (-(1 * |v|)) := by
            rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
    · exact (integrable_rexp_neg_mul_abs one_pos).const_mul C
    · refine Eventually.of_forall fun v => ?_
      have h := ((by fun_prop : Continuous fun l : ℝ => Real.exp (l * v) *
        filteredArcProfile K u v).tendsto (1 / 2 : ℝ))
      exact h.mono_left nhdsWithin_le_nhds
  have hI0 : I (1 / 2) = 0 := tendsto_nhds_unique hlim hzero
  rw [hIdef] at hI0
  simp only at hI0
  rw [← hI0]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  ring_nf

/-- **Zero mean**: `∫ h_{K,u} = 0`. -/
theorem integral_filteredArcVector_eq_zero {K : ℝ} (hK : 0 < K) (u : ArcParam) :
    ∫ x, filteredArcVector K u x = 0 := by
  have heven : ∀ x, filteredArcVector K u |x| = filteredArcVector K u x := fun x => by
    rcases le_total 0 x with hx | hx
    · rw [abs_of_nonneg hx]
    · rw [abs_of_nonpos hx, filteredArcVector_neg]
  have h1 : ∫ x, filteredArcVector K u x = 2 * ∫ x in Ioi 0, filteredArcVector K u x := by
    rw [← integral_comp_abs (f := filteredArcVector K u)]
    exact integral_congr_ae (Eventually.of_forall fun x => (heven x).symm)
  rw [h1, setIntegral_Ioi_eq_integral_exp_mul]
  have h2 : ∀ v, Real.exp v * filteredArcVector K u (Real.exp v) =
      Real.exp (v / 2) * filteredArcProfile K u v := fun v => by
    rw [← exp_half_mul_filteredArcVector, ← mul_assoc, ← Real.exp_add]; ring_nf
  simp_rw [h2]
  rw [integral_exp_half_mul_filteredArcProfile hK u, mul_zero]

/-! ### Integrability of the derivative -/

/-- The two-variable kernel `ǧ_K(w) e^{−3w/2} ψ_u'(x e^{−w})` of the filtered derivative. -/
def filteredArcDerivKernel (K : ℝ) (u : ArcParam) (x w : ℝ) : ℝ :=
  poleFilter K w * (Real.exp (-(3 * w / 2)) * arcPairDeriv u (x * Real.exp (-w)))

theorem continuous_filteredArcDerivKernel (K : ℝ) (u : ArcParam) :
    Continuous fun p : ℝ × ℝ => filteredArcDerivKernel K u p.1 p.2 := by
  unfold filteredArcDerivKernel
  exact ((continuous_poleFilter K).comp continuous_snd).mul
    ((by fun_prop : Continuous fun p : ℝ × ℝ => Real.exp (-(3 * p.2 / 2))).mul
      ((continuous_arcPairDeriv u).comp (by fun_prop)))

theorem abs_filteredArcDerivKernel_le (K : ℝ) (u : ArcParam) (x w : ℝ) :
    |filteredArcDerivKernel K u x w| ≤
      64 * |poleFilter K w| * Real.exp (-(3 * w / 2)) * (1 + (x * Real.exp (-w)) ^ 2)⁻¹ := by
  unfold filteredArcDerivKernel
  rw [abs_mul, abs_mul, abs_of_pos (Real.exp_pos _)]
  have h := abs_arcPairDeriv_le u (x * Real.exp (-w))
  have h0 := abs_nonneg (poleFilter K w)
  have h1 := Real.exp_pos (-(3 * w / 2))
  calc |poleFilter K w| * (Real.exp (-(3 * w / 2)) * |arcPairDeriv u (x * Real.exp (-w))|)
      ≤ |poleFilter K w| * (Real.exp (-(3 * w / 2)) *
          (64 * (1 + (x * Real.exp (-w)) ^ 2)⁻¹)) := by gcongr
    _ = 64 * |poleFilter K w| * Real.exp (-(3 * w / 2)) * (1 + (x * Real.exp (-w)) ^ 2)⁻¹ := by
        ring

theorem integral_inv_one_add_sq_mul (c : ℝ) (hc : 0 < c) :
    ∫ x : ℝ, (1 + (x * c) ^ 2)⁻¹ = c⁻¹ * Real.pi := by
  have h := Measure.integral_comp_mul_right (fun t : ℝ => (1 + t ^ 2)⁻¹) c
  rw [h, integral_univ_inv_one_add_sq, abs_of_pos (inv_pos.mpr hc), smul_eq_mul]

theorem integrable_filteredArcDerivKernel {K : ℝ} (hK : 0 < K) (u : ArcParam) :
    Integrable (fun p : ℝ × ℝ => filteredArcDerivKernel K u p.1 p.2) (volume.prod volume) := by
  have hmeas := (continuous_filteredArcDerivKernel K u).aestronglyMeasurable
    (μ := volume.prod volume)
  have hx : ∀ w, Integrable fun x => filteredArcDerivKernel K u x w := by
    intro w
    have hb : Integrable fun x : ℝ => 64 * |poleFilter K w| * Real.exp (-(3 * w / 2)) *
        (1 + (x * Real.exp (-w)) ^ 2)⁻¹ :=
      (integrable_inv_one_add_sq.comp_mul_right' (Real.exp_pos (-w)).ne').const_mul _
    refine hb.mono' ((continuous_filteredArcDerivKernel K u).comp
      (continuous_id.prodMk continuous_const)).aestronglyMeasurable
      (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs]; exact abs_filteredArcDerivKernel_le K u x w
  rw [integrable_prod_iff' hmeas]
  refine ⟨Eventually.of_forall hx, ?_⟩
  refine ((integrable_abs_poleFilter_mul_rexp hK (-(1 / 2))).const_mul (64 * Real.pi)).mono'
    hmeas.prod_swap.norm.integral_prod_right' (Eventually.of_forall fun w => ?_)
  rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun x => norm_nonneg _)]
  have hb : Integrable fun x : ℝ => 64 * |poleFilter K w| * Real.exp (-(3 * w / 2)) *
      (1 + (x * Real.exp (-w)) ^ 2)⁻¹ :=
    (integrable_inv_one_add_sq.comp_mul_right' (Real.exp_pos (-w)).ne').const_mul _
  calc ∫ x, ‖filteredArcDerivKernel K u x w‖
      ≤ ∫ x, 64 * |poleFilter K w| * Real.exp (-(3 * w / 2)) *
          (1 + (x * Real.exp (-w)) ^ 2)⁻¹ :=
        integral_mono (hx w).norm hb fun x => by
          rw [Real.norm_eq_abs]; exact abs_filteredArcDerivKernel_le K u x w
    _ = 64 * Real.pi * |poleFilter K w * Real.exp (w * -(1 / 2))| := by
        rw [integral_const_mul, integral_inv_one_add_sq_mul _ (Real.exp_pos _), abs_mul,
          abs_of_pos (Real.exp_pos _), ← Real.exp_neg]
        have : Real.exp (-(3 * w / 2)) * Real.exp (- -w) = Real.exp (w * -(1 / 2)) := by
          rw [← Real.exp_add]; congr 1; ring
        rw [← this]; ring

theorem integrable_filteredArcDeriv {K : ℝ} (hK : 0 < K) (u : ArcParam) :
    Integrable (filteredArcDeriv K u) := by
  have h1 : Integrable (arcPairDeriv u) :=
    (integrable_inv_one_add_sq.const_mul 64).mono' (continuous_arcPairDeriv u).aestronglyMeasurable
      (Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact abs_arcPairDeriv_le u x)
  have h2 := (integrable_filteredArcDerivKernel hK u).integral_prod_left
  exact h1.sub h2

end

end RHTower
