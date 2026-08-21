import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# Connes' Sobolev growth weight

Formalization of the growth-weight layer of

  A. Connes, *Trace formula in noncommutative geometry and the zeros of the Riemann zeta
  function*, arXiv:math/9811068 (Selecta Math. NS **5** (1999) 29-106),

namely §III (16)(17) and Appendix I (1)-(5), (29).

Connes builds the Polya-Hilbert space as a cokernel inside the weighted space `L^2_delta(C_k)`
whose square norm carries the factor `(1 + log^2 |g|)^{delta/2}`.  Everything the paper needs about
that weight is elementary and is proved here without hypotheses:

* `connesSobolevWeight_add_le` - Appendix I (2) / §III (17): the weight
  `rho_delta(u) = (1+u^2)^{delta/2}` is submultiplicative up to the constant `2^{delta/2}`.  This is
  exactly the inequality that produces the almost-unitarity estimate `‖V(g)‖ = O((log|g|)^{delta/2})`
  of §III (16), so the representation `V` is not unitary but has polynomial growth.
* `connesSobolevWeight_lintegral_translate_le` - Appendix I (4)(5): the resulting operator bound
  `‖V(v)‖ ≤ (c rho_delta(v))^{1/2}` for the translation `V(v) xi = xi(· - v)`, stated with lower
  Lebesgue integrals so that it needs no integrability side condition.
* `connesSobolevWeight_integrable_iff` - Appendix I (29): the vector
  `eta_{t,a}(x) = chi_0(x)|x|^{it}(log|x|)^a` lies in `L^2_{-delta}` exactly when `a < (delta-1)/2`.
  In the logarithmic coordinate this is the integrability criterion `2k - delta < -1` for
  `u ↦ u^{2k}(1+u^2)^{-delta/2}` on the whole line.

The printed paper states the last condition as `2k + delta < -1`; its own displayed conclusion
`k < (delta-1)/2` shows the intended inequality is `2k - delta < -1`, which is what is proved.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open MeasureTheory Real Filter Set

def connesSobolevWeight (δ u : ℝ) : ℝ := (1 + u ^ 2) ^ (δ / 2)

theorem connesSobolevWeight_pos (δ u : ℝ) : 0 < connesSobolevWeight δ u :=
  Real.rpow_pos_of_pos (by positivity) _

/-- Two-sided control of `t ^ z` when the base is confined to `[1,2]`. -/
theorem rpow_bounds_of_base_mem_Icc {t z : ℝ} (h1 : 1 ≤ t) (h2 : t ≤ 2) :
    (2:ℝ) ^ (-|z|) ≤ t ^ z ∧ t ^ z ≤ (2:ℝ) ^ |z| := by
  have ht : (0:ℝ) < t := lt_of_lt_of_le one_pos h1
  have hlog0 : 0 ≤ Real.log t := Real.log_nonneg h1
  have hlog2 : Real.log t ≤ Real.log 2 := Real.log_le_log ht h2
  have hkey : |Real.log t * z| ≤ Real.log 2 * |z| := by
    rw [abs_mul, abs_of_nonneg hlog0]
    exact mul_le_mul_of_nonneg_right hlog2 (abs_nonneg z)
  have hb1 : -(Real.log 2 * |z|) ≤ Real.log t * z := neg_le_of_abs_le hkey
  have hb2 : Real.log t * z ≤ Real.log 2 * |z| := le_of_abs_le hkey
  rw [Real.rpow_def_of_pos ht, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  constructor
  · exact Real.exp_le_exp.mpr (by linarith [hb1])
  · exact Real.exp_le_exp.mpr (by linarith [hb2])

/-- **Appendix I (29), factorized form.**  For `u ≥ 1` the Sobolev weight is the pure power
`u^{-δ}` corrected by a factor whose base lies in `[1,2]`. -/
theorem connesSobolevWeight_neg_factor {δ u : ℝ} (hu : 1 ≤ u) :
    connesSobolevWeight (-δ) u = ((1 + u ^ 2) / u ^ 2) ^ (-δ / 2) * u ^ (-δ) := by
  have hu0 : (0:ℝ) < u := lt_of_lt_of_le one_pos hu
  have hu2 : (0:ℝ) < u ^ 2 := by positivity
  have hsplit : (1 : ℝ) + u ^ 2 = ((1 + u ^ 2) / u ^ 2) * u ^ 2 := by
    field_simp
  have hpow : (u ^ 2 : ℝ) ^ (-δ / 2) = u ^ (-δ) := by
    rw [← Real.rpow_natCast u 2, ← Real.rpow_mul hu0.le]
    congr 1
    push_cast
    ring
  calc connesSobolevWeight (-δ) u = ((1 + u ^ 2) / u ^ 2 * u ^ 2) ^ (-δ / 2) := by
        rw [connesSobolevWeight, ← hsplit]
    _ = ((1 + u ^ 2) / u ^ 2) ^ (-δ / 2) * (u ^ 2 : ℝ) ^ (-δ / 2) :=
        Real.mul_rpow (by positivity) (by positivity)
    _ = ((1 + u ^ 2) / u ^ 2) ^ (-δ / 2) * u ^ (-δ) := by rw [hpow]

/-- The Connes integrand `u ↦ u^{2k} ρ_{-δ}(u)` is squeezed between two multiples of the pure
power `u^{2k-δ}` on `[1,∞)`. -/
theorem connesSobolevWeight_integrand_bounds (k : ℕ) (δ : ℝ) {u : ℝ} (hu : 1 ≤ u) :
    (2:ℝ) ^ (-(|δ| / 2)) * u ^ (2 * (k:ℝ) - δ)
        ≤ u ^ (2 * k) * connesSobolevWeight (-δ) u ∧
      u ^ (2 * k) * connesSobolevWeight (-δ) u
        ≤ (2:ℝ) ^ (|δ| / 2) * u ^ (2 * (k:ℝ) - δ) := by
  have hu0 : (0:ℝ) < u := lt_of_lt_of_le one_pos hu
  have hu2 : (0:ℝ) < u ^ 2 := by positivity
  set t : ℝ := (1 + u ^ 2) / u ^ 2 with ht
  have ht1 : (1:ℝ) ≤ t := by rw [ht, le_div_iff₀ hu2]; nlinarith
  have ht2 : t ≤ 2 := by rw [ht, div_le_iff₀ hu2]; nlinarith
  have habs : |(-δ / 2)| = |δ| / 2 := by
    rw [abs_div, abs_neg, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
  obtain ⟨hl, hr⟩ := rpow_bounds_of_base_mem_Icc (z := -δ / 2) ht1 ht2
  rw [habs] at hl hr
  have hnat : (u : ℝ) ^ (2 * k) = u ^ ((2 * k : ℕ) : ℝ) := (Real.rpow_natCast u (2 * k)).symm
  have hmul : u ^ ((2 * k : ℕ) : ℝ) * u ^ (-δ) = u ^ (2 * (k:ℝ) - δ) := by
    rw [← Real.rpow_add hu0]; push_cast; ring_nf
  have hfac : u ^ (2 * k) * connesSobolevWeight (-δ) u = t ^ (-δ / 2) * u ^ (2 * (k:ℝ) - δ) := by
    rw [connesSobolevWeight_neg_factor hu, hnat, ← ht]; rw [← hmul]; ring
  have hpow : (0:ℝ) < u ^ (2 * (k:ℝ) - δ) := Real.rpow_pos_of_pos hu0 _
  rw [hfac]
  exact ⟨mul_le_mul_of_nonneg_right hl hpow.le, mul_le_mul_of_nonneg_right hr hpow.le⟩


/-- The Connes integrand is continuous. -/
theorem continuous_connesSobolevIntegrand (k : ℕ) (δ : ℝ) :
    Continuous fun u : ℝ => u ^ (2 * k) * connesSobolevWeight (-δ) u := by
  refine (continuous_pow (2 * k)).mul ?_
  refine Continuous.rpow_const (by fun_prop) ?_
  intro x; left; positivity

theorem connesSobolevIntegrand_nonneg (k : ℕ) (δ : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    0 ≤ u ^ (2 * k) * connesSobolevWeight (-δ) u :=
  mul_nonneg (pow_nonneg hu _) (connesSobolevWeight_pos _ _).le

theorem connesSobolevIntegrand_even (k : ℕ) (δ : ℝ) (u : ℝ) :
    (-u) ^ (2 * k) * connesSobolevWeight (-δ) (-u) = u ^ (2 * k) * connesSobolevWeight (-δ) u := by
  rw [connesSobolevWeight, connesSobolevWeight, neg_pow, neg_sq]
  simp [pow_mul]

/-- Reflection transport for even functions on the two half lines. -/
theorem integrableOn_Iic_neg_one_iff_Ici_one {f : ℝ → ℝ} (heven : ∀ u, f (-u) = f u) :
    IntegrableOn f (Iic (-1)) ↔ IntegrableOn f (Ici 1) := by
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).integrableOn_comp_preimage
    (f := f) (s := Iic (-1)) (measurableEmbedding_neg (α := ℝ))
  have hpre : (Neg.neg : ℝ → ℝ) ⁻¹' (Iic (-1) : Set ℝ) = Ici 1 := by ext x; simp
  rw [hpre] at h
  have hfun : (f ∘ (Neg.neg : ℝ → ℝ)) = f := by funext x; simpa using heven x
  rw [hfun] at h
  exact h.symm

/-- **Appendix I (29).**  The vector `η_{t,a}(x) = χ₀(x)|x|^{it}(\log |x|)^a` lies in the Sobolev
space `L²_{-δ}` exactly when `a < (δ-1)/2`.  In the logarithmic coordinate this is the statement
that `u ↦ u^{2k}(1+u²)^{-δ/2}` is Lebesgue integrable on the line iff `2k - δ < -1`.

(The printed paper writes the condition as `2k + δ < -1`; the displayed conclusion `k < (δ-1)/2`
shows the intended inequality is `2k - δ < -1`, which is what is proved here.) -/
theorem connesSobolevWeight_integrable_iff (k : ℕ) (δ : ℝ) :
    Integrable (fun u : ℝ => u ^ (2 * k) * connesSobolevWeight (-δ) u) ↔ 2 * (k : ℝ) - δ < -1 := by
  set g : ℝ → ℝ := fun u : ℝ => u ^ (2 * k) * connesSobolevWeight (-δ) u with hg
  set s : ℝ := 2 * (k : ℝ) - δ with hs
  have hcont : Continuous g := continuous_connesSobolevIntegrand k δ
  have hC1 : (0:ℝ) < (2:ℝ) ^ (-(|δ| / 2)) := Real.rpow_pos_of_pos (by norm_num) _
  have hC2 : (0:ℝ) < (2:ℝ) ^ (|δ| / 2) := Real.rpow_pos_of_pos (by norm_num) _
  have hmeas : AEStronglyMeasurable (fun u : ℝ => u ^ s) (volume.restrict (Ioi (1:ℝ))) := by
    refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioi
    exact ContinuousOn.rpow_const continuousOn_id
      (fun x hx => Or.inl (ne_of_gt (lt_trans one_pos hx)))
  constructor
  · intro hint
    have hdom : IntegrableOn (fun u : ℝ => ((2:ℝ) ^ (-(|δ| / 2)))⁻¹ * g u) (Ioi (1:ℝ)) :=
      (hint.integrableOn (s := Ioi (1:ℝ))).const_mul _
    have hIoi : IntegrableOn (fun u : ℝ => u ^ s) (Ioi (1:ℝ)) := by
      refine Integrable.mono' hdom hmeas ?_
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (1:ℝ)))] with u hu
      have hu1 : (1:ℝ) ≤ u := le_of_lt hu
      have hpos : (0:ℝ) < u ^ s := Real.rpow_pos_of_pos (lt_of_lt_of_le one_pos hu1) _
      have hb := (connesSobolevWeight_integrand_bounds k δ hu1).1
      rw [Real.norm_eq_abs, abs_of_pos hpos]
      rw [inv_mul_eq_div, le_div_iff₀ hC1, mul_comm]
      exact hb
    exact (integrableOn_Ioi_rpow_iff one_pos).mp hIoi
  · intro hlt
    have hpow : IntegrableOn (fun u : ℝ => (2:ℝ) ^ (|δ| / 2) * u ^ s) (Ioi (1:ℝ)) :=
      ((integrableOn_Ioi_rpow_iff one_pos).mpr hlt).const_mul _
    have hIoi : IntegrableOn g (Ioi (1:ℝ)) := by
      refine Integrable.mono' hpow hcont.aestronglyMeasurable ?_
      filter_upwards [self_mem_ae_restrict (measurableSet_Ioi (a := (1:ℝ)))] with u hu
      have hu1 : (1:ℝ) ≤ u := le_of_lt hu
      have hnn : 0 ≤ g u := connesSobolevIntegrand_nonneg k δ (by linarith)
      rw [Real.norm_eq_abs, abs_of_nonneg hnn]
      exact (connesSobolevWeight_integrand_bounds k δ hu1).2
    have hIci : IntegrableOn g (Ici (1:ℝ)) := by
      rw [integrableOn_Ici_iff_integrableOn_Ioi]; exact hIoi
    have hIic : IntegrableOn g (Iic (-1:ℝ)) :=
      (integrableOn_Iic_neg_one_iff_Ici_one (f := g)
        (fun u => connesSobolevIntegrand_even k δ u)).mpr hIci
    have hIcc : IntegrableOn g (Icc (-1:ℝ) 1) := hcont.continuousOn.integrableOn_Icc
    have hcover : (Iic (-1:ℝ) ∪ Icc (-1:ℝ) 1) ∪ Ici (1:ℝ) = (univ : Set ℝ) := by
      ext x
      simp only [mem_union, mem_Iic, mem_Icc, mem_Ici, mem_univ, iff_true]
      rcases le_total x (-1 : ℝ) with h | h
      · exact Or.inl (Or.inl h)
      · rcases le_total x (1 : ℝ) with h' | h'
        · exact Or.inl (Or.inr ⟨h, h'⟩)
        · exact Or.inr h'
    have : IntegrableOn g univ := by
      rw [← hcover, integrableOn_union, integrableOn_union]
      exact ⟨⟨hIic, hIcc⟩, hIci⟩
    exact integrableOn_univ.mp this

/-- **Appendix I (2) / §III (17).**  The growth weight is submultiplicative up to `2^{δ/2}`. -/
theorem connesSobolevWeight_add_le {δ : ℝ} (hδ : 0 ≤ δ) (u v : ℝ) :
    connesSobolevWeight δ (u + v) ≤
      2 ^ (δ / 2) * (connesSobolevWeight δ u * connesSobolevWeight δ v) := by
  have hbase : (1 : ℝ) + (u + v) ^ 2 ≤ 2 * ((1 + u ^ 2) * (1 + v ^ 2)) := by
    nlinarith [sq_nonneg (u - v), sq_nonneg (u * v)]
  have h1 : (0:ℝ) ≤ 1 + (u + v) ^ 2 := by positivity
  have hexp : (0:ℝ) ≤ δ / 2 := by linarith
  calc connesSobolevWeight δ (u + v)
      ≤ (2 * ((1 + u ^ 2) * (1 + v ^ 2))) ^ (δ / 2) :=
        Real.rpow_le_rpow h1 hbase hexp
    _ = 2 ^ (δ / 2) * ((1 + u ^ 2) ^ (δ / 2) * (1 + v ^ 2) ^ (δ / 2)) := by
        rw [Real.mul_rpow (by norm_num) (by positivity),
          Real.mul_rpow (by positivity) (by positivity)]
    _ = 2 ^ (δ / 2) * (connesSobolevWeight δ u * connesSobolevWeight δ v) := rfl

/-- **Appendix I (4).**  The translation `V(v)ξ = ξ(· − v)` is bounded on the weighted space
`L²_δ(ℝ)` with norm at most `(2^{δ/2} ρ_δ(v))^{1/2}`.  Stated with lower integrals, so it carries
no integrability hypothesis. -/
theorem connesSobolevWeight_lintegral_translate_le {δ : ℝ} (hδ : 0 ≤ δ) (ξ : ℝ → ℂ) (v : ℝ) :
    ∫⁻ u, ‖ξ (u - v)‖ₑ ^ 2 * ENNReal.ofReal (connesSobolevWeight δ u) ≤
      ENNReal.ofReal (2 ^ (δ / 2) * connesSobolevWeight δ v) *
        ∫⁻ u, ‖ξ u‖ₑ ^ 2 * ENNReal.ofReal (connesSobolevWeight δ u) := by
  have hshift :
      ∫⁻ u, ‖ξ (u - v)‖ₑ ^ 2 * ENNReal.ofReal (connesSobolevWeight δ u)
        = ∫⁻ w, ‖ξ w‖ₑ ^ 2 * ENNReal.ofReal (connesSobolevWeight δ (w + v)) := by
    have := lintegral_sub_right_eq_self (μ := (volume : Measure ℝ))
      (fun w : ℝ => ‖ξ w‖ₑ ^ 2 * ENNReal.ofReal (connesSobolevWeight δ (w + v))) v
    simpa using this
  rw [hshift, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine lintegral_mono fun w => ?_
  have hle : connesSobolevWeight δ (w + v)
      ≤ 2 ^ (δ / 2) * connesSobolevWeight δ v * connesSobolevWeight δ w := by
    have := connesSobolevWeight_add_le hδ w v
    nlinarith [(connesSobolevWeight_pos δ w).le, (connesSobolevWeight_pos δ v).le,
      Real.rpow_pos_of_pos (show (0:ℝ) < 2 by norm_num) (δ / 2)]
  calc ‖ξ w‖ₑ ^ 2 * ENNReal.ofReal (connesSobolevWeight δ (w + v))
      ≤ ‖ξ w‖ₑ ^ 2 *
          ENNReal.ofReal (2 ^ (δ / 2) * connesSobolevWeight δ v * connesSobolevWeight δ w) :=
        by exact mul_le_mul_right (ENNReal.ofReal_le_ofReal hle) _
    _ = ENNReal.ofReal (2 ^ (δ / 2) * connesSobolevWeight δ v) *
          (‖ξ w‖ₑ ^ 2 * ENNReal.ofReal (connesSobolevWeight δ w)) := by
        have hc : (0:ℝ) ≤ 2 ^ (δ / 2) * connesSobolevWeight δ v :=
          le_of_lt (mul_pos (Real.rpow_pos_of_pos (by norm_num) _) (connesSobolevWeight_pos δ v))
        rw [ENNReal.ofReal_mul hc]; ring

end

end GaloisForLFunctions.RHTower
