import GaloisForLFunctions.ArithmeticCriticalityTheory.QuarticGaugeWindowPotential

/-!
# Sharp Lévy moments and the sharp potential of the quartic gauge

The density `ω = 1/(4 sinh(u/2)) + 1/(4 cosh(u/2))` satisfies
`½ + u/4 − u²/48 − u³/32 ≤ u ω(u) ≤ ½ + u/4 − u²/48 − u³/32 + u⁴/1152 + u⁵/256` on `(0, 1]`
(`mul_archLevyDensity_ge_sharp`, `mul_archLevyDensity_le_sharper`): the cubic term is exact on both
sides. Hence the moments `m_k = ∫ u^k ω` are known to fourth order,
`P_k − E_k ≤ m_k ≤ P_k − E_k + E⁺_k` (`integral_pow_mul_archLevyDensity_le_sharper`).

The upper bound without the cubic term lost `E_k = s^{k+3}/(32(k+3))` on every moment of negative
coefficient in the potential of a quartic gauge: the inner first moment and the fourth moments,
together about `3·10⁻³` at `x ≈ 0.2` for `R ≈ 0.3`, more than the whole potential there. The sharp
potential (`neg_poleFreeWeilOperator_quarticWindowGauge_ge_sharp`) keeps them, for every radius
`R ≤ 1/3`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar
open Zeta23

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-- **The sharp upper bound** `u ω(u) ≤ ½ + u/4 − u²/48 − u³/32 + u⁴/1152 + u⁵/256` on `(0, 1]`:
the cubic term of `u ω` is kept, and the error is of fourth order. -/
theorem mul_archLevyDensity_le_sharper {u : ℝ} (h0 : 0 < u) (h1 : u ≤ 1) :
    u * archLevyDensity u ≤
      1 / 2 + u / 4 - u ^ 2 / 48 - u ^ 3 / 32 + u ^ 4 / 1152 + u ^ 5 / 256 := by
  set z := u / 2 with hz
  have hz0 : 0 < z := by rw [hz]; linarith
  obtain ⟨hs1, -, hc1, -⟩ := sinh_cosh_taylor_bounds hz0.le (by rw [hz]; linarith)
  have hS : 0 < Real.sinh z := by nlinarith [pow_pos hz0 3]
  have hC : 0 < Real.cosh z := Real.cosh_pos z
  rw [archLevyDensity_eq_inv_sinh_add_inv_cosh h0, ← hz]
  have e : u * (1 / (4 * Real.sinh z) + 1 / (4 * Real.cosh z)) =
      z / (2 * Real.sinh z) + z / (2 * Real.cosh z) := by
    rw [hz]; field_simp; ring
  rw [e]
  have hA : 0 ≤ 1 - z ^ 2 / 6 + z ^ 4 / 36 := by nlinarith [sq_nonneg (z ^ 2 / 6 - 1 / 2)]
  have hB : 0 ≤ 1 - z ^ 2 / 2 + z ^ 4 / 4 := by nlinarith [sq_nonneg (z ^ 2 / 2 - 1 / 2)]
  have k1 : z / (2 * Real.sinh z) ≤ (1 - z ^ 2 / 6 + z ^ 4 / 36) / 2 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hs1 hA, pow_pos hz0 7]
  have k2 : z / (2 * Real.cosh z) ≤ z / 2 * (1 - z ^ 2 / 2 + z ^ 4 / 4) := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_left hc1 (mul_nonneg hz0.le hB), pow_pos hz0 7]
  have hpoly : (1 - z ^ 2 / 6 + z ^ 4 / 36) / 2 + z / 2 * (1 - z ^ 2 / 2 + z ^ 4 / 4) =
      1 / 2 + u / 4 - u ^ 2 / 48 - u ^ 3 / 32 + u ^ 4 / 1152 + u ^ 5 / 256 := by
    rw [hz]; ring
  linarith

/-- The upper moment error `E⁺_k(s) = s^{k+4}/(1152(k+4)) + s^{k+5}/(256(k+5))`. -/
def levyMomentErrUp (k : ℕ) (s : ℝ) : ℝ :=
  s ^ (k + 4) / (1152 * (k + 4)) + s ^ (k + 5) / (256 * (k + 5))

theorem hasDerivAt_levyMomentErrUp (k : ℕ) (y : ℝ) :
    HasDerivAt (levyMomentErrUp k) (y ^ (k + 3) / 1152 + y ^ (k + 4) / 256) y := by
  have h := ((hasDerivAt_pow (k + 4) y).div_const (1152 * ((k : ℝ) + 4))).add
    ((hasDerivAt_pow (k + 5) y).div_const (256 * ((k : ℝ) + 5)))
  have e : levyMomentErrUp k = fun s => s ^ (k + 4) / (1152 * ((k : ℝ) + 4)) +
      s ^ (k + 5) / (256 * ((k : ℝ) + 5)) := by
    funext s; unfold levyMomentErrUp; ring
  rw [e]
  refine h.congr_deriv ?_
  simp only [show k + 4 - 1 = k + 3 by omega, show k + 5 - 1 = k + 4 by omega]
  push_cast
  have h4 : (k : ℝ) + 4 ≠ 0 := by positivity
  have h5 : (k : ℝ) + 5 ≠ 0 := by positivity
  field_simp

/-- **Sharp upper moment bound**
`∫_a^b u^k ω ≤ P_k(b) − P_k(a) − (E_k(b) − E_k(a)) + (E⁺_k(b) − E⁺_k(a))`, `0 ≤ a ≤ b ≤ 1`. -/
theorem integral_pow_mul_archLevyDensity_le_sharper {k : ℕ} (hk : 1 ≤ k) {a b : ℝ} (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 1) :
    (∫ u in Ioc a b, u ^ k * archLevyDensity u) ≤ levyMomentPoly k b - levyMomentPoly k a -
      (levyMomentErr k b - levyMomentErr k a) + (levyMomentErrUp k b - levyMomentErrUp k a) := by
  have hpc : Continuous fun u : ℝ => u ^ (k - 1) * (1 / 2 + u / 4 - u ^ 2 / 48) := by fun_prop
  have hec : Continuous fun u : ℝ => u ^ (k - 1) * (u ^ 3 / 32) := by fun_prop
  have huc : Continuous fun u : ℝ => u ^ (k + 3) / 1152 + u ^ (k + 4) / 256 := by fun_prop
  have hdE : ∀ y, HasDerivAt (levyMomentErr k) (y ^ (k - 1) * (y ^ 3 / 32)) y := fun y =>
    (hasDerivAt_levyMomentErr k y).resolve_right (by omega)
  have hval : (∫ u in Ioc a b, (u ^ (k - 1) * (1 / 2 + u / 4 - u ^ 2 / 48) -
      u ^ (k - 1) * (u ^ 3 / 32) + (u ^ (k + 3) / 1152 + u ^ (k + 4) / 256))) =
      levyMomentPoly k b - levyMomentPoly k a - (levyMomentErr k b - levyMomentErr k a) +
        (levyMomentErrUp k b - levyMomentErrUp k a) := by
    have i1 : IntervalIntegrable (fun u : ℝ => u ^ (k - 1) * (1 / 2 + u / 4 - u ^ 2 / 48) -
        u ^ (k - 1) * (u ^ 3 / 32)) volume a b := (hpc.sub hec).intervalIntegrable a b
    rw [← intervalIntegral.integral_of_le hab,
      intervalIntegral.integral_add i1 (huc.intervalIntegrable _ _),
      intervalIntegral.integral_sub (hpc.intervalIntegrable _ _) (hec.intervalIntegrable _ _),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hasDerivAt_levyMomentPoly hk y)
        (hpc.intervalIntegrable _ _),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hdE y)
        (hec.intervalIntegrable _ _),
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hasDerivAt_levyMomentErrUp k y)
        (huc.intervalIntegrable _ _)]
  rw [← hval]
  refine setIntegral_mono_on (integrableOn_pow_mul_archLevyDensity hk ha hb)
    (((hpc.sub hec).add huc).integrableOn_Icc.mono_set Ioc_subset_Icc_self) measurableSet_Ioc
    fun u hu => ?_
  have hu0 : 0 < u := lt_of_le_of_lt ha hu.1
  have h := mul_archLevyDensity_le_sharper hu0 (hu.2.trans hb)
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hpow : 0 ≤ u ^ m := by positivity
  have := mul_le_mul_of_nonneg_left h hpow
  have e1 : u ^ (m + 1) * archLevyDensity u = u ^ m * (u * archLevyDensity u) := by ring
  have e2 : u ^ (m + 1 + 3) / 1152 + u ^ (m + 1 + 4) / 256 =
      u ^ m * (u ^ 4 / 1152 + u ^ 5 / 256) := by ring
  rw [e1, e2]
  nlinarith [this]

theorem levyMomentErrUp_zero (k : ℕ) : levyMomentErrUp k 0 = 0 := by
  unfold levyMomentErrUp
  rw [zero_pow (by omega), zero_pow (by omega)]
  simp

/-- **The sharp potential of the quartic gauge** at a plateau point `0 ≤ x ≤ R − δ`, `R ≤ 1/3`: as
`neg_poleFreeWeilOperator_quarticWindowGauge_ge_max`, with the upper moment bounds
`P_k − E_k + E⁺_k` in place of `P_k` for the terms of negative coefficient. -/
theorem neg_poleFreeWeilOperator_quarticWindowGauge_ge_sharp {c d R δ x : ℝ} (hd : 0 ≤ d)
    (hdc2 : 2 * d * R ^ 2 ≤ c) (hqR : 0 ≤ 1 - c * R ^ 2 + d * R ^ 4) (hδ : 0 < δ)
    (hR : R ≤ 1 / 3) (hx0 : 0 ≤ x) (hx : x ≤ R - δ) :
    quarticProfile c d x *
        ((-(1 / 2) * Real.log (1 - Real.exp (-2 * (R - x))) - 3 / 4 * (R - x) +
            3 * (R - x) ^ 2 / 32 - (R - x) ^ 4 / 192) +
          (-(1 / 2) * Real.log (1 - Real.exp (-2 * (R + x))) - 3 / 4 * (R + x) +
            3 * (R + x) ^ 2 / 32 - (R + x) ^ 4 / 192) - 2 * archConstantReal) +
      ((c - 6 * d * x ^ 2) * (levyMomentPoly 2 (R - x) + levyMomentPoly 2 (R + x)) -
        (c - 6 * d * x ^ 2) * (levyMomentErr 2 (R - x) + levyMomentErr 2 (R + x)) +
        min (c - 6 * d * x ^ 2) 0 * (levyMomentErrUp 2 (R - x) + levyMomentErrUp 2 (R + x)) -
        d * (levyMomentPoly 4 (R - x) + levyMomentPoly 4 (R + x) -
          (levyMomentErr 4 (R - x) + levyMomentErr 4 (R + x)) +
          (levyMomentErrUp 4 (R - x) + levyMomentErrUp 4 (R + x))) -
        2 * x * (c - 2 * d * x ^ 2) * (levyMomentPoly 1 (R + x) - levyMomentPoly 1 (R - x) -
          (levyMomentErr 1 (R + x) - levyMomentErr 1 (R - x)) +
          (levyMomentErrUp 1 (R + x) - levyMomentErrUp 1 (R - x))) +
        4 * d * x * (levyMomentPoly 3 (R + x) - levyMomentPoly 3 (R - x) -
          (levyMomentErr 3 (R + x) - levyMomentErr 3 (R - x)))) ≤
      -poleFreeWeilOperator (quarticWindowGauge c d R δ) x := by
  set q := quarticProfile c d with hqdef
  set a : ℝ := R - x with hadef
  set b : ℝ := R + x with hbdef
  have hxabs : |x| ≤ R - δ := by rw [abs_of_nonneg hx0]; exact hx
  have ha : 0 < a := by rw [hadef]; linarith
  have hb : 0 < b := by rw [hbdef]; linarith
  have hab : a ≤ b := by rw [hadef, hbdef]; linarith
  have hb1 : b ≤ 1 := by rw [hbdef]; linarith
  have ha1 : a ≤ 1 := by linarith
  have hq0 : ∀ y, |y| ≤ R → 0 ≤ q y := fun y hy => by
    have := quarticProfile_ge_of_le hd hdc2 hy
    rw [hqdef]; linarith
  have hc : 0 ≤ c := le_trans (by positivity) hdc2
  have hx2 : x ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ hx0 (by linarith) 2
  have hdx := mul_le_mul_of_nonneg_left hx2 hd
  have hα1 : 0 ≤ 2 * x * (c - 2 * d * x ^ 2) := mul_nonneg (by linarith) (by linarith)
  have hα3 : 0 ≤ 4 * d * x := by positivity
  have im : ∀ k : ℕ, 1 ≤ k → ∀ s : ℝ, s ≤ 1 →
      IntegrableOn (fun u => u ^ k * archLevyDensity u) (Ioc 0 s) := fun k hk s hs =>
    integrableOn_pow_mul_archLevyDensity hk le_rfl hs
  have epa : ∀ u, archLevyDensity u * (q x - q (x + u)) = archLevyDensity u *
      ((2 * c * x - 4 * d * x ^ 3) * u + (c - 6 * d * x ^ 2) * u ^ 2 + (-(4 * d * x)) * u ^ 3 +
        (-d) * u ^ 4) := fun u => by rw [hqdef]; unfold quarticProfile; ring
  have epb : ∀ u, archLevyDensity u * (q x - q (x - u)) = archLevyDensity u *
      ((-(2 * c * x - 4 * d * x ^ 3)) * u + (c - 6 * d * x ^ 2) * u ^ 2 + (4 * d * x) * u ^ 3 +
        (-d) * u ^ 4) := fun u => by rw [hqdef]; unfold quarticProfile; ring
  have hcomb : ∀ s : ℝ, s ≤ 1 → ∀ α₁ α₂ α₃ α₄ : ℝ,
      IntegrableOn (fun u => archLevyDensity u * (α₁ * u + α₂ * u ^ 2 + α₃ * u ^ 3 + α₄ * u ^ 4))
        (Ioc 0 s) := fun s hs α₁ α₂ α₃ α₄ => by
    have h := ((((im 1 le_rfl s hs).const_mul α₁).add ((im 2 (by norm_num) s hs).const_mul α₂)).add
      ((im 3 (by norm_num) s hs).const_mul α₃)).add ((im 4 (by norm_num) s hs).const_mul α₄)
    exact IntegrableOn.congr_fun h (fun u _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioc
  have hia : IntegrableOn (fun u => archLevyDensity u * (q x - q (x + u))) (Ioc 0 a) := by
    simp_rw [epa]; exact hcomb a ha1 _ _ _ _
  have hib : IntegrableOn (fun u => archLevyDensity u * (q x - q (x - u))) (Ioc 0 b) := by
    simp_rw [epb]; exact hcomb b hb1 _ _ _ _
  have hgen := neg_poleFreeWeilOperator_profileGauge_ge (contDiff_quarticProfile c d) hδ hR hxabs
    hq0 hia hib
  have hgauge : (fun y => q y * plateauGauge R δ y) = quarticWindowGauge c d R δ := rfl
  rw [hgauge] at hgen
  obtain ⟨-, hVa⟩ := integral_one_sided_window_ge_cubic ha ha1
  obtain ⟨-, hVb⟩ := integral_one_sided_window_ge_cubic hb hb1
  have hqx : 0 ≤ q x := hq0 x (by linarith [hxabs])
  have hqV := mul_le_mul_of_nonneg_left (add_le_add hVa hVb) hqx
  have eA : (∫ u in Ioc 0 a, archLevyDensity u * (q x - q (x + u))) =
      (2 * c * x - 4 * d * x ^ 3) * (∫ u in Ioc 0 a, u ^ 1 * archLevyDensity u) +
        (c - 6 * d * x ^ 2) * (∫ u in Ioc 0 a, u ^ 2 * archLevyDensity u) +
        (-(4 * d * x)) * (∫ u in Ioc 0 a, u ^ 3 * archLevyDensity u) +
        (-d) * ∫ u in Ioc 0 a, u ^ 4 * archLevyDensity u := by
    simp_rw [epa]
    exact integral_archLevyDensity_mul_quartic (im 1 le_rfl a ha1) (im 2 (by norm_num) a ha1)
      (im 3 (by norm_num) a ha1) (im 4 (by norm_num) a ha1) _ _ _ _
  have eB : (∫ u in Ioc 0 b, archLevyDensity u * (q x - q (x - u))) =
      (-(2 * c * x - 4 * d * x ^ 3)) * (∫ u in Ioc 0 b, u ^ 1 * archLevyDensity u) +
        (c - 6 * d * x ^ 2) * (∫ u in Ioc 0 b, u ^ 2 * archLevyDensity u) +
        (4 * d * x) * (∫ u in Ioc 0 b, u ^ 3 * archLevyDensity u) +
        (-d) * ∫ u in Ioc 0 b, u ^ 4 * archLevyDensity u := by
    simp_rw [epb]
    exact integral_archLevyDensity_mul_quartic (im 1 le_rfl b hb1) (im 2 (by norm_num) b hb1)
      (im 3 (by norm_num) b hb1) (im 4 (by norm_num) b hb1) _ _ _ _
  have split : ∀ k : ℕ, 1 ≤ k → (∫ u in Ioc 0 b, u ^ k * archLevyDensity u) =
      (∫ u in Ioc 0 a, u ^ k * archLevyDensity u) + ∫ u in Ioc a b, u ^ k * archLevyDensity u :=
    fun k hk => by
      rw [← setIntegral_union (Ioc_disjoint_Ioc_of_le le_rfl) measurableSet_Ioc (im k hk a ha1)
        (integrableOn_pow_mul_archLevyDensity hk ha.le hb1), Ioc_union_Ioc_eq_Ioc ha.le hab]
  rw [split 1 le_rfl, split 3 (by norm_num)] at eB
  -- moment bounds
  have L2a := integral_pow_mul_archLevyDensity_ge (k := 2) (by norm_num) le_rfl ha.le ha1
  have L2b := integral_pow_mul_archLevyDensity_ge (k := 2) (by norm_num) le_rfl hb.le hb1
  have U2a := integral_pow_mul_archLevyDensity_le_sharper (k := 2) (by norm_num) le_rfl ha.le ha1
  have U2b := integral_pow_mul_archLevyDensity_le_sharper (k := 2) (by norm_num) le_rfl hb.le hb1
  have U4a := integral_pow_mul_archLevyDensity_le_sharper (k := 4) (by norm_num) le_rfl ha.le ha1
  have U4b := integral_pow_mul_archLevyDensity_le_sharper (k := 4) (by norm_num) le_rfl hb.le hb1
  have U1 := integral_pow_mul_archLevyDensity_le_sharper (k := 1) le_rfl ha.le hab hb1
  have L3 := integral_pow_mul_archLevyDensity_ge (k := 3) (by norm_num) ha.le hab hb1
  rw [levyMomentPoly_zero (by norm_num), levyMomentErr_zero] at L2a L2b
  rw [levyMomentPoly_zero (by norm_num), levyMomentErr_zero, levyMomentErrUp_zero] at U2a U2b U4a U4b
  simp only [sub_zero] at L2a L2b U2a U2b U4a U4b
  have k2 : (c - 6 * d * x ^ 2) * (levyMomentPoly 2 a + levyMomentPoly 2 b) -
      (c - 6 * d * x ^ 2) * (levyMomentErr 2 a + levyMomentErr 2 b) +
      min (c - 6 * d * x ^ 2) 0 * (levyMomentErrUp 2 a + levyMomentErrUp 2 b) ≤
      (c - 6 * d * x ^ 2) * ((∫ u in Ioc 0 a, u ^ 2 * archLevyDensity u) +
        ∫ u in Ioc 0 b, u ^ 2 * archLevyDensity u) := by
    rcases le_total 0 (c - 6 * d * x ^ 2) with hα2 | hα2
    · rw [min_eq_right hα2, zero_mul, add_zero]
      have := mul_le_mul_of_nonneg_left (add_le_add L2a L2b) hα2
      linarith
    · rw [min_eq_left hα2]
      have := mul_le_mul_of_nonpos_left (add_le_add U2a U2b) hα2
      linarith
  have k4 := mul_le_mul_of_nonneg_left (add_le_add U4a U4b) hd
  have k1 := mul_le_mul_of_nonneg_left U1 hα1
  have k3 := mul_le_mul_of_nonneg_left L3 hα3
  have hlinear : (2 * c * x - 4 * d * x ^ 3) = 2 * x * (c - 2 * d * x ^ 2) := by ring
  rw [hlinear] at eA eB
  linarith [hgen, hqV, eA, eB, k1, k2, k3, k4]

end GaloisForLFunctions.ArithmeticCriticalityTheory
