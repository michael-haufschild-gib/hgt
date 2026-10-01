import GaloisForLFunctions.RHTower.FermiNymanConfluentCoupling

/-!
# Weighted witnesses of the alternating Fermi source

The source pairing stays fixed while the squared norm receives weight `t^(2a-1)`.
A power witness with parameter `z` belongs exactly when `Re z > 1-a`; logarithmic
jets satisfy the same strict admission bound. The dyadic form subtracts `2^(-2a)`
times the full weighted pairing, preserving neutrality of all spurious modes.
Its exact spurious/power coupling is a Cauchy kernel with nodes translated by
`1-2a`. At `a=1/2` the original witness class and form are recovered.

The twist `t^(a-1/2) w(t)` supplies ordinary square-integrability estimates.
For `a<1` weighted witnesses are integrable against the original generators,
and finite linear combinations preserve the source constraints. No zero-location
or source-positivity assertion enters these identities.
-/

open Complex MeasureTheory Set Filter Topology
noncomputable section
namespace RHTower

/-- Weighted source membership, with the original unweighted generator pairing. -/
def IsWeightedFermiWitness (a : ℝ) (w : ℝ → ℂ) : Prop :=
  ContinuousOn w (Ioc 0 1) ∧
    IntegrableOn (fun t => t ^ (2 * a - 1) * ‖w t‖ ^ 2) (Ioc 0 1) ∧
    ∀ b : ℝ, 1 ≤ b →
      ∫ t in Ioc (0 : ℝ) 1, fermiNymanGen b t * (starRingEnd ℂ) (w t) = 0

/-- Power weights shift the real Mellin parameter in the literal squared norm. -/
theorem weighted_normSq_logPowerWitness (a : ℝ) (z : ℂ) (j : ℕ) {t : ℝ}
    (ht : 0 < t) :
    t ^ (2 * a - 1) * ‖logPowerWitness z j t‖ ^ 2 =
      ‖logPowerWitness (z + (a : ℂ) - 1 / 2) j t‖ ^ 2 := by
  simp only [logPowerWitness, powerWitness, norm_mul, norm_pow,
    Complex.norm_real, Real.norm_eq_abs, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.one_re,
    mul_pow]
  norm_num
  rw [← Real.rpow_mul_natCast ht.le _ 2, ← Real.rpow_mul_natCast ht.le _ 2]
  rw [mul_left_comm, ← Real.rpow_add ht]
  congr 2
  ring

theorem integrableOn_weighted_normSq_logPowerWitness {a : ℝ} {z : ℂ}
    (hz : 1 - a < z.re) (j : ℕ) :
    IntegrableOn (fun t => t ^ (2 * a - 1) * ‖logPowerWitness z j t‖ ^ 2)
      (Ioc (0 : ℝ) 1) := by
  have hshift : 1 / 2 < (z + (a : ℂ) - 1 / 2).re := by
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re]
    norm_num
    linarith
  exact (integrableOn_normSq_logPowerWitness hshift j).congr_fun
    (fun t ht => (weighted_normSq_logPowerWitness a z j ht.1).symm) measurableSet_Ioc

theorem isWeightedFermiWitness_logPower_of_order {a : ℝ} (ha : a < 1) {ρ : ℂ}
    (h1 : 1 - a < ρ.re) (h2 : ρ.re < 1) (j : ℕ)
    (hj : ((j + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt riemannZeta ρ) :
    IsWeightedFermiWitness a (logPowerWitness ((starRingEnd ℂ) ρ) j) := by
  have hρpos : 0 < ρ.re := by linarith
  have hρ0 : ρ ≠ 0 := by intro h; subst ρ; simp at hρpos
  have hρ1 : ρ ≠ 1 := by intro h; subst ρ; simp at h2
  have hζa : AnalyticAt ℂ riemannZeta ρ := analyticOn_riemannZeta ρ hρ1
  refine ⟨continuousOn_logPowerWitness _ _, integrableOn_weighted_normSq_logPowerWitness
    (by simpa only [Complex.conj_re] using h1) j, fun b hb => ?_⟩
  rw [logPowerWitness_pairing hb hρpos hρ1]
  have hua := analyticAt_fermiNymanSourceUnit (lt_of_lt_of_le one_pos hb) hρ0
  have hFA : AnalyticAt ℂ (fermiNymanMellinRHS b) ρ := by
    rw [fermiNymanMellinRHS_eq_unit_mul_zeta]
    exact hua.mul hζa
  have horder : ((j + 1 : ℕ) : ℕ∞) ≤ analyticOrderAt (fermiNymanMellinRHS b) ρ := by
    rw [fermiNymanMellinRHS_eq_unit_mul_zeta, analyticOrderAt_mul hua hζa]
    exact hj.trans (le_add_of_nonneg_left (by exact zero_le))
  exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hFA).1 horder j (by omega)

theorem isWeightedFermiWitness_spurious {a : ℝ} (ha : 0 < a) {k : ℤ} (hk : k ≠ 0) :
    IsWeightedFermiWitness a (spuriousWitness k) := by
  have hw := isFermiNymanWitness_spurious hk
  refine ⟨hw.1, ?_, hw.2.2⟩
  have h := integrableOn_weighted_normSq_logPowerWitness
    (a := a) (z := (starRingEnd ℂ) (dyadicSpuriousMode k))
    (by simp only [Complex.conj_re, dyadicSpuriousMode_re]; linarith) 0
  simpa only [logPowerWitness, spuriousWitness, pow_zero, one_mul] using h

theorem isWeightedFermiWitness_half (w : ℝ → ℂ) :
    IsWeightedFermiWitness (1 / 2) w ↔ IsFermiNymanWitness w := by
  simp only [IsWeightedFermiWitness, IsFermiNymanWitness,
    show 2 * (1 / 2 : ℝ) - 1 = 0 by ring, Real.rpow_zero, one_mul]

/-- Literal weighted dyadic Hermitian form with the matching neutral coefficient. -/
def weightedDyadicForm (a : ℝ) (u v : ℝ → ℂ) : ℂ :=
  (∫ t in Ioc (0 : ℝ) (1 / 2), (t ^ (2 * a - 1) : ℝ) * u t * (starRingEnd ℂ) (v t)) -
    ((2 : ℝ) ^ (-2 * a) : ℝ) *
      ∫ t in Ioc (0 : ℝ) 1, (t ^ (2 * a - 1) : ℝ) * u t * (starRingEnd ℂ) (v t)

theorem weightedDyadicForm_half (u v : ℝ → ℂ) :
    weightedDyadicForm (1 / 2) u v = dyadicForm u v := by
  norm_num [weightedDyadicForm, dyadicForm, Real.rpow_neg_one]

theorem weightedDyadicForm_conj (a : ℝ) (u v : ℝ → ℂ) :
    weightedDyadicForm a v u = (starRingEnd ℂ) (weightedDyadicForm a u v) := by
  unfold weightedDyadicForm
  rw [map_sub, map_mul, ← integral_conj, ← integral_conj]
  simp only [Complex.conj_ofReal]
  congr 1
  · refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
    ring
  · congr 1
    refine setIntegral_congr_fun measurableSet_Ioc (fun t _ => ?_)
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
    ring

theorem weighted_powerWitness_pair (a : ℝ) (k : ℤ) (ρ : ℂ) {t : ℝ} (ht : 0 < t) :
    (t ^ (2 * a - 1) : ℝ) * spuriousWitness k t *
      (starRingEnd ℂ) (powerWitness ((starRingEnd ℂ) ρ) t) =
    spuriousWitness k t *
      (starRingEnd ℂ) (powerWitness ((starRingEnd ℂ) (ρ + (2 * a - 1 : ℝ))) t) := by
  simp only [spuriousWitness, powerWitness, conj_ofReal_cpow ht, map_sub, map_one,
    Complex.conj_conj]
  rw [Complex.ofReal_cpow ht.le, mul_assoc, mul_comm ((t : ℂ) ^ ((2 * a - 1 : ℝ) : ℂ)),
    mul_assoc, ← Complex.cpow_add _ _ (by exact_mod_cast ht.ne')]
  congr 2
  ring

theorem integral_weighted_spurious_power (a : ℝ) (k : ℤ) {ρ : ℂ}
    (hρ : 0 < ρ.re + 2 * a - 1) {c : ℝ} (hc : 0 ≤ c) :
    (∫ t in Ioc (0 : ℝ) c, (t ^ (2 * a - 1) : ℝ) * spuriousWitness k t *
      (starRingEnd ℂ) (powerWitness ((starRingEnd ℂ) ρ) t)) =
      (c : ℂ) ^ ((starRingEnd ℂ) (dyadicSpuriousMode k) + (ρ + (2 * a - 1 : ℝ)) - 1) /
        ((starRingEnd ℂ) (dyadicSpuriousMode k) + (ρ + (2 * a - 1 : ℝ)) - 1) := by
  rw [setIntegral_congr_fun measurableSet_Ioc
    (fun t ht => weighted_powerWitness_pair a k ρ ht.1)]
  exact integral_spurious_mul_conj_zeroWitness k
    (by simp only [Complex.add_re, Complex.ofReal_re]; linarith) hc

theorem weightedDyadicForm_spurious_power (a : ℝ) (k : ℤ) {ρ : ℂ}
    (hρ : 0 < ρ.re + 2 * a - 1) :
    weightedDyadicForm a (spuriousWitness k) (powerWitness ((starRingEnd ℂ) ρ)) =
      (2 : ℂ) ^ ((1 : ℂ) - (2 * a : ℝ)) * dyadicCoupling ρ /
        ((starRingEnd ℂ) (dyadicSpuriousMode k) + ρ + (2 * a : ℝ) - 2) := by
  unfold weightedDyadicForm
  rw [integral_weighted_spurious_power a k hρ (by norm_num),
    integral_weighted_spurious_power a k hρ zero_le_one,
    half_cpow_spurious_add, Complex.ofReal_one, Complex.one_cpow,
    Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
  have hexp : (2 : ℂ) ^ (-(ρ + (2 * a - 1 : ℝ))) =
      (2 : ℂ) ^ ((1 : ℂ) - (2 * a : ℝ)) * (2 : ℂ) ^ (-ρ) := by
    rw [← Complex.cpow_add _ _ (by norm_num)]
    congr 1
    push_cast
    ring
  have hhalf : (2 : ℂ) ^ ((-2 * a : ℝ) : ℂ) =
      (2 : ℂ) ^ ((1 : ℂ) - (2 * a : ℝ)) / 2 := by
    apply (eq_div_iff (by norm_num : (2 : ℂ) ≠ 0)).2
    calc
      _ = (2 : ℂ) ^ ((-2 * a : ℝ) : ℂ) * (2 : ℂ) ^ (1 : ℂ) := by rw [Complex.cpow_one]
      _ = _ := by
        rw [← Complex.cpow_add _ _ (by norm_num)]
        congr 1
        push_cast
        ring
  simp only [Complex.ofReal_ofNat]
  rw [hexp, hhalf]
  have hden : (starRingEnd ℂ) (dyadicSpuriousMode k) + (ρ + (2 * a - 1 : ℝ)) - 1 =
      (starRingEnd ℂ) (dyadicSpuriousMode k) + ρ + (2 * a : ℝ) - 2 := by
    push_cast
    ring
  rw [hden]
  unfold dyadicCoupling
  ring

theorem weightedDyadicForm_spurious_spurious {a : ℝ} (ha : 0 < a) (k l : ℤ) :
    weightedDyadicForm a (spuriousWitness k) (spuriousWitness l) = 0 := by
  change weightedDyadicForm a (spuriousWitness k)
    (powerWitness ((starRingEnd ℂ) (dyadicSpuriousMode l))) = 0
  rw [weightedDyadicForm_spurious_power a k
    (by rw [dyadicSpuriousMode_re]; linarith)]
  have h : dyadicCoupling (dyadicSpuriousMode l) = 0 := by
    unfold dyadicCoupling
    have hx := two_cpow_one_sub_dyadicSpuriousMode l
    rw [← two_mul_two_cpow_neg] at hx
    linear_combination hx / 2
  rw [h, mul_zero, zero_div]

theorem weighted_normSq_powerWitness (a : ℝ) (z : ℂ) {t : ℝ} (ht : 0 < t) :
    t ^ (2 * a - 1) * ‖powerWitness z t‖ ^ 2 = t ^ (2 * (a + z.re - 1) - 1) := by
  simp only [powerWitness, Complex.norm_cpow_eq_rpow_re_of_pos ht,
    Complex.sub_re, Complex.one_re]
  rw [← Real.rpow_mul_natCast ht.le _ 2, ← Real.rpow_add ht]
  congr 1
  ring

theorem integrableOn_weighted_normSq_powerWitness_iff (a : ℝ) (z : ℂ) :
    IntegrableOn (fun t => t ^ (2 * a - 1) * ‖powerWitness z t‖ ^ 2) (Ioc 0 1) ↔
      1 - a < z.re := by
  have hiff : IntegrableOn (fun t => t ^ (2 * a - 1) * ‖powerWitness z t‖ ^ 2) (Ioc 0 1) ↔
      IntegrableOn (fun t : ℝ => t ^ (2 * (a + z.re - 1) - 1)) (Ioc 0 1) := by
    constructor
    · intro h
      exact h.congr_fun (fun t ht => weighted_normSq_powerWitness a z ht.1) measurableSet_Ioc
    · intro h
      exact h.congr_fun (fun t ht => (weighted_normSq_powerWitness a z ht.1).symm) measurableSet_Ioc
  rw [hiff, integrableOn_Ioc_iff_integrableOn_Ioo,
    intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one]
  constructor <;> intro h <;> linarith

theorem integral_weighted_normSq_powerWitness {a : ℝ} {z : ℂ}
    (hz : 1 - a < z.re) {c : ℝ} (hc : 0 < c) :
    (∫ t in Ioc (0 : ℝ) c, t ^ (2 * a - 1) * ‖powerWitness z t‖ ^ 2) =
      c ^ (2 * (a + z.re - 1)) / (2 * (a + z.re - 1)) := by
  rw [setIntegral_congr_fun measurableSet_Ioc
    (fun t ht => weighted_normSq_powerWitness a z ht.1),
    ← intervalIntegral.integral_of_le hc.le, integral_rpow (Or.inl (by linarith)),
    Real.zero_rpow (by linarith)]
  congr 1 <;> ring_nf


/-- Isometry from the weighted square norm to ordinary square integrability. -/
def fermiWeightTwist (a : ℝ) (w : ℝ → ℂ) (t : ℝ) : ℂ :=
  (t ^ (a - 1 / 2) : ℝ) * w t

theorem continuousOn_fermiWeightTwist (a : ℝ) {w : ℝ → ℂ}
    (hc : ContinuousOn w (Ioc 0 1)) :
    ContinuousOn (fermiWeightTwist a w) (Ioc 0 1) :=
  (Complex.continuous_ofReal.comp_continuousOn
    (continuousOn_id.rpow_const fun _ ht => Or.inl ht.1.ne')).mul hc

theorem norm_fermiWeightTwist (a : ℝ) (w : ℝ → ℂ) {t : ℝ} (ht : 0 < t) :
    ‖fermiWeightTwist a w t‖ = t ^ (a - 1 / 2) * ‖w t‖ := by
  rw [fermiWeightTwist, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg ht.le _)]

theorem normSq_fermiWeightTwist (a : ℝ) (w : ℝ → ℂ) {t : ℝ} (ht : 0 < t) :
    ‖fermiWeightTwist a w t‖ ^ 2 = t ^ (2 * a - 1) * ‖w t‖ ^ 2 := by
  rw [norm_fermiWeightTwist a w ht, mul_pow, ← Real.rpow_mul_natCast ht.le]
  congr 2
  ring

theorem weightedMellinIntegrand_eq_twist (a x : ℝ) (w : ℝ → ℂ) {t : ℝ} (ht : 0 < t) :
    t ^ (x - 1) * ‖w t‖ =
      t ^ ((x - a + 1 / 2) - 1) * ‖fermiWeightTwist a w t‖ := by
  rw [norm_fermiWeightTwist a w ht, ← mul_assoc, ← Real.rpow_add ht]
  congr 2
  ring

theorem IsWeightedFermiWitness.integrableOn_normSq_twist {a : ℝ} {w : ℝ → ℂ}
    (hw : IsWeightedFermiWitness a w) :
    IntegrableOn (fun t => ‖fermiWeightTwist a w t‖ ^ 2) (Ioc 0 1) :=
  hw.2.1.congr_fun (fun _ ht => (normSq_fermiWeightTwist a w ht.1).symm) measurableSet_Ioc

theorem integrableOn_mellinMajorant_of_sq {w : ℝ → ℂ} (hc : ContinuousOn w (Ioc 0 1))
    (hsq : IntegrableOn (fun t => ‖w t‖ ^ 2) (Ioc 0 1)) {x : ℝ} (hx : 1 / 2 < x) :
    IntegrableOn (fun t : ℝ => t ^ (x - 1) * ‖w t‖) (Ioc 0 1) := by
  have hI : IntegrableOn (fun t : ℝ => (1 * t ^ (2 * x - 2) + ‖w t‖ ^ 2 / 1) / 2)
      (Ioc 0 1) :=
    (((integrableOn_rpow_two_mul_sub_two hx).const_mul 1).add (hsq.div_const 1)).div_const 2
  refine hI.mono' ?_ (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioc
    exact (continuousOn_id.rpow_const fun _ ht => Or.inl ht.1.ne').mul hc.norm
  · rw [Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (norm_nonneg _))]
    exact rpow_mul_le_amgm ht.1 one_pos

theorem IsWeightedFermiWitness.integrableOn_mellinMajorant {a : ℝ} {w : ℝ → ℂ}
    (hw : IsWeightedFermiWitness a w) {x : ℝ} (hx : a < x) :
    IntegrableOn (fun t : ℝ => t ^ (x - 1) * ‖w t‖) (Ioc 0 1) := by
  have h := integrableOn_mellinMajorant_of_sq (continuousOn_fermiWeightTwist a hw.1)
    hw.integrableOn_normSq_twist (x := x - a + 1 / 2) (by linarith)
  exact h.congr_fun (fun t ht => (weightedMellinIntegrand_eq_twist a x w ht.1).symm)
    measurableSet_Ioc

theorem IsWeightedFermiWitness.integrableOn_norm {a : ℝ} (ha : a < 1) {w : ℝ → ℂ}
    (hw : IsWeightedFermiWitness a w) : IntegrableOn (fun t => ‖w t‖) (Ioc 0 1) := by
  simpa only [sub_self, Real.rpow_zero, one_mul] using
    hw.integrableOn_mellinMajorant (x := 1) ha

theorem IsWeightedFermiWitness.integrableOn_mul_conj {a : ℝ} (ha : a < 1) {w : ℝ → ℂ}
    (hw : IsWeightedFermiWitness a w) {f : ℝ → ℂ} (hf : Measurable f)
    {M : ℝ} (hM : ∀ t, ‖f t‖ ≤ M) :
    IntegrableOn (fun t => f t * (starRingEnd ℂ) (w t)) (Ioc 0 1) := by
  refine ((hw.integrableOn_norm ha).const_mul M).mono'
    (hf.aestronglyMeasurable.mul (hw.1.aestronglyMeasurable measurableSet_Ioc).star)
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t _ => ?_)
  rw [norm_mul, Complex.norm_conj]
  exact mul_le_mul_of_nonneg_right (hM t) (norm_nonneg _)

theorem IsWeightedFermiWitness.add_smul {a : ℝ} (ha : a < 1) {u v : ℝ → ℂ}
    (hu : IsWeightedFermiWitness a u) (hv : IsWeightedFermiWitness a v) (ε : ℂ) :
    IsWeightedFermiWitness a (fun t => u t + ε * v t) := by
  refine ⟨hu.1.add (continuousOn_const.mul hv.1), ?_, fun b hb => ?_⟩
  · have hmeas : AEStronglyMeasurable
        (fun t => t ^ (2 * a - 1) * ‖u t + ε * v t‖ ^ 2)
        (volume.restrict (Ioc (0 : ℝ) 1)) :=
      ((continuousOn_id.rpow_const fun _ ht => Or.inl ht.1.ne').mul
        ((hu.1.add (continuousOn_const.mul hv.1)).norm.pow 2)).aestronglyMeasurable measurableSet_Ioc
    refine ((hu.2.1.const_mul 2).add (hv.2.1.const_mul (2 * ‖ε‖ ^ 2))).mono' hmeas
      (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
    simp only [Pi.add_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _) (sq_nonneg _))]
    have h1 : ‖u t + ε * v t‖ ≤ ‖u t‖ + ‖ε‖ * ‖v t‖ := by
      rw [← norm_mul]; exact norm_add_le _ _
    have h2 : ‖u t + ε * v t‖ ^ 2 ≤ 2 * ‖u t‖ ^ 2 + 2 * ‖ε‖ ^ 2 * ‖v t‖ ^ 2 := by
      nlinarith [norm_nonneg (u t + ε * v t), norm_nonneg (u t),
        mul_nonneg (norm_nonneg ε) (norm_nonneg (v t)), sq_nonneg (‖u t‖ - ‖ε‖ * ‖v t‖)]
    nlinarith [mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg ht.1.le (2 * a - 1))]
  · have iu := hu.integrableOn_mul_conj ha (measurable_fermiNymanGen b) (norm_fermiNymanGen_le b)
    have iv := hv.integrableOn_mul_conj ha (measurable_fermiNymanGen b) (norm_fermiNymanGen_le b)
    have hsplit : (fun t => fermiNymanGen b t * (starRingEnd ℂ) (u t + ε * v t)) =
        fun t => fermiNymanGen b t * (starRingEnd ℂ) (u t) +
          (starRingEnd ℂ) ε * (fermiNymanGen b t * (starRingEnd ℂ) (v t)) := by
      funext t; simp only [map_add, map_mul]; ring
    rw [hsplit, integral_add iu (iv.const_mul _), integral_const_mul, hu.2.2 b hb, hv.2.2 b hb]
    simp

theorem isWeightedFermiWitness_zero (a : ℝ) :
    IsWeightedFermiWitness a (fun _ => (0 : ℂ)) := by
  refine ⟨continuousOn_const, ?_, fun _ _ => by simp⟩
  simp only [norm_zero, zero_pow (by omega : 2 ≠ 0), mul_zero]
  exact integrableOn_zero

theorem isWeightedFermiWitness_finsetSum {a : ℝ} (ha : a < 1) {ι : Type*}
    (s : Finset ι) (f : ι → ℝ → ℂ) (c : ι → ℂ)
    (hf : ∀ i ∈ s, IsWeightedFermiWitness a (f i)) :
    IsWeightedFermiWitness a (fun t => ∑ i ∈ s, c i * f i t) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isWeightedFermiWitness_zero a
  | insert i s hi ih =>
    have h1 := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
    have h2 := h1.add_smul ha (hf i (Finset.mem_insert_self i s)) (c i)
    refine (show (fun t => ∑ j ∈ insert i s, c j * f j t) =
      (fun t => (∑ j ∈ s, c j * f j t) + c i * f i t) from ?_) ▸ h2
    funext t
    rw [Finset.sum_insert hi, add_comm]

theorem IsWeightedFermiWitness.integrableOn_weighted_mul_conj {a : ℝ} {u v : ℝ → ℂ}
    (hu : IsWeightedFermiWitness a u) (hv : IsWeightedFermiWitness a v) :
    IntegrableOn (fun t => (t ^ (2 * a - 1) : ℝ) * u t * (starRingEnd ℂ) (v t))
      (Ioc 0 1) := by
  have hcont : ContinuousOn
      (fun t => (t ^ (2 * a - 1) : ℝ) * u t * (starRingEnd ℂ) (v t)) (Ioc 0 1) :=
    ((Complex.continuous_ofReal.comp_continuousOn
      (continuousOn_id.rpow_const fun _ ht => Or.inl ht.1.ne')).mul hu.1).mul
        (Complex.continuous_conj.comp_continuousOn hv.1)
  refine ((hu.2.1.add hv.2.1).div_const 2).mono'
    (hcont.aestronglyMeasurable measurableSet_Ioc)
    (ae_restrict_of_forall_mem measurableSet_Ioc fun t ht => ?_)
  simp only [Pi.add_apply, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs]
  rw [abs_of_nonneg (Real.rpow_nonneg ht.1.le _)]
  nlinarith [mul_nonneg (Real.rpow_nonneg ht.1.le (2 * a - 1))
    (sq_nonneg (‖u t‖ - ‖v t‖))]

theorem weightedDyadicForm_sum_sum {a : ℝ} {ι : Type*} [Fintype ι]
    (f : ι → ℝ → ℂ) (c d : ι → ℂ)
    (hint : ∀ i j, IntegrableOn
      (fun t => (t ^ (2 * a - 1) : ℝ) * f i t * (starRingEnd ℂ) (f j t)) (Ioc 0 1)) :
    weightedDyadicForm a (fun t => ∑ i, c i * f i t) (fun t => ∑ j, d j * f j t) =
      ∑ i, ∑ j, c i * (starRingEnd ℂ) (d j) * weightedDyadicForm a (f i) (f j) := by
  have hexp : ∀ t : ℝ,
      (t ^ (2 * a - 1) : ℝ) * (∑ i, c i * f i t) * (starRingEnd ℂ) (∑ j, d j * f j t) =
      ∑ i, ∑ j, c i * (starRingEnd ℂ) (d j) *
        ((t ^ (2 * a - 1) : ℝ) * f i t * (starRingEnd ℂ) (f j t)) := by
    intro t
    rw [mul_assoc, map_sum, Finset.sum_mul_sum]
    simp only [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul]
    ring
  have hI : ∀ s : Set ℝ, s ⊆ Ioc 0 1 →
      (∫ t in s, (t ^ (2 * a - 1) : ℝ) * (∑ i, c i * f i t) *
        (starRingEnd ℂ) (∑ j, d j * f j t)) =
      ∑ i, ∑ j, c i * (starRingEnd ℂ) (d j) *
        ∫ t in s, (t ^ (2 * a - 1) : ℝ) * f i t * (starRingEnd ℂ) (f j t) := by
    intro s hs
    simp_rw [hexp]
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ fun j _ =>
      ((hint i j).mono_set hs).const_mul _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_finsetSum _ (fun j _ => ((hint i j).mono_set hs).const_mul _)]
    exact Finset.sum_congr rfl fun j _ => integral_const_mul _ _
  unfold weightedDyadicForm
  rw [hI _ (Ioc_subset_Ioc_right (by norm_num)), hI _ subset_rfl,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

end RHTower
