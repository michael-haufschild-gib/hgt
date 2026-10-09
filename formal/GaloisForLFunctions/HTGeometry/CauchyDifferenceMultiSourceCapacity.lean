import GaloisForLFunctions.HTGeometry.CauchyDifferenceTwoIntervalBound

/-!
# Coherent capacity of mean-zero sources on short intervals

On `(0, 1)` consider the boundary form
`b[u] = ¼ ∫∫ (u(x) − u(y))²/|x − y| dx dy − ½ ∫ log(x(1 − x)) u(x)² dx`,
the logarithmic difference energy plus its endpoint potential.

**Theorem** (`capacity_multiSource`). Let `I_ν = (a_ν, a_ν + ε) ⊆ (0, 1)` be pairwise disjoint
intervals of one common length `ε`, and let `u` have mean zero on every `I_ν`. Then
`b[u] ≥ (log(1/ε) + ½) Σ_ν ‖u‖²_{L²(I_ν)}`.

So `M` mean-zero sources cost exactly as much as `M` isolated ones: each interval of length `ε`
carries the capacity `log(1/ε) + ½`, and the sources do not lower one another's cost.

**Proof.** For `ν` let `W_ν(y) = 1/max(y − a_ν, a_ν + ε − y)` be the inverse distance to the far
end of `I_ν` (set to `0` on `I_ν`).
* On `I_ν × I_ν`, `|x − y| < ε` and the mean-zero identity give the energy `2‖u‖²_ν`.
* A free point `y ∉ ⋃ I` pays `∫_{I_ν} (u − u(y))²/|x − y| ≥ ‖u‖²_ν W_ν(y)`.
* A pair `I_ν, I_μ` pays both one-sided charges `‖u‖²_ν ∫_{I_μ} W_ν + ‖u‖²_μ ∫_{I_ν} W_μ`
  (`lintegral_twoInterval_ge`).

Summing, the complement of `I_ν` is covered exactly once, so
`¼ ∫∫ ≥ ½ Σ_ν ‖u‖²_ν (1 + ∫_{(0,1)} W_ν) ≥ ½ Σ_ν ‖u‖²_ν (1 + log((a_ν + ε)/ε) + log((1 − a_ν)/ε))`.
The potential gives at least `−½ log((a_ν + ε)(1 − a_ν)) ‖u‖²_ν` on `I_ν`, and every
`a_ν`-dependent logarithm cancels.
-/

open MeasureTheory Set Real
open scoped ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry.CauchyDifference

/-- The inverse distance to the far end of `(a, a + ε)`, set to `0` on the interval. -/
def farCharge (a ε y : ℝ) : ℝ≥0∞ :=
  if y ∈ Ioo a (a + ε) then 0 else ENNReal.ofReal (1 / max (y - a) (a + ε - y))

/-- The Cauchy difference density `(u(x) − u(y))²/|x − y|`. -/
def cauchyDensity (u : ℝ → ℝ) (x y : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal ((u x - u y) ^ 2 / |x - y|)

theorem cauchyDensity_comm (u : ℝ → ℝ) (x y : ℝ) : cauchyDensity u x y = cauchyDensity u y x := by
  unfold cauchyDensity
  rw [abs_sub_comm, show (u x - u y) ^ 2 = (u y - u x) ^ 2 by ring]

theorem measurable_cauchyDensity {u : ℝ → ℝ} (hum : Measurable u) :
    Measurable fun p : ℝ × ℝ => cauchyDensity u p.1 p.2 := by
  unfold cauchyDensity
  fun_prop

/-! ## The mean-zero square -/

/-- `∫_{(a,b)} (u − v)² = ‖u‖² + (b − a) v²` for mean-zero `u`. -/
theorem setIntegral_sub_const_sq {a b v : ℝ} (hab : a ≤ b) {u : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioo a b))) (hu0 : ∫ x in Ioo a b, u x = 0) :
    ∫ x in Ioo a b, (u x - v) ^ 2 = (∫ x in Ioo a b, u x ^ 2) + (b - a) * v ^ 2 := by
  have hi : IntegrableOn u (Ioo a b) := hu.integrable one_le_two
  have hi2 : IntegrableOn (fun x => u x ^ 2) (Ioo a b) := hu.integrable_sq
  have hc : IntegrableOn (fun _ : ℝ => v ^ 2) (Ioo a b) :=
    integrableOn_Ioo_of_continuous continuous_const
  have i1 : IntegrableOn (fun x => (2 * v) * u x) (Ioo a b) := hi.const_mul _
  have i2 : IntegrableOn (fun x => u x ^ 2 - (2 * v) * u x) (Ioo a b) := hi2.sub i1
  have hfun : (fun x => (u x - v) ^ 2) = fun x => (u x ^ 2 - (2 * v) * u x) + v ^ 2 := by
    funext x; ring
  rw [hfun, integral_add i2 hc, integral_sub hi2 i1, integral_const_mul, hu0, setIntegral_const,
    Real.volume_real_Ioo_of_le hab, smul_eq_mul]
  ring

/-! ## One interval against itself, against a free point, against another interval -/

/-- **Self-energy.** `∫_I ∫_I (u(x) − u(y))²/|x − y| ≥ 2‖u‖²` for mean-zero `u` on an interval of
length `ε`. -/
theorem lintegral_self_ge {a ε : ℝ} (hε : 0 < ε) {u : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioo a (a + ε)))) (hu0 : ∫ x in Ioo a (a + ε), u x = 0) :
    ENNReal.ofReal (2 * ∫ x in Ioo a (a + ε), u x ^ 2) ≤
      ∫⁻ x in Ioo a (a + ε), ∫⁻ y in Ioo a (a + ε), cauchyDensity u x y := by
  set N := ∫ x in Ioo a (a + ε), u x ^ 2 with hN
  have hi2 : IntegrableOn (fun x => u x ^ 2) (Ioo a (a + ε)) := hu.integrable_sq
  -- the kernel is at least `1/ε`
  have hpt : ∀ x ∈ Ioo a (a + ε), ∀ y ∈ Ioo a (a + ε),
      ENNReal.ofReal ((u x - u y) ^ 2 / ε) ≤ cauchyDensity u x y := by
    intro x hx y hy
    unfold cauchyDensity
    apply ENNReal.ofReal_le_ofReal
    rcases eq_or_ne x y with rfl | hxy
    · simp
    · have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
      have hlt : |x - y| ≤ ε := by
        rw [abs_le]; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
      exact div_le_div_of_nonneg_left (sq_nonneg _) hpos hlt
  have hinner : ∀ x, ∫ y in Ioo a (a + ε), (u x - u y) ^ 2 / ε = (N + ε * u x ^ 2) / ε := by
    intro x
    rw [integral_div]
    congr 1
    have h := setIntegral_sub_const_sq (v := u x) (by linarith) hu hu0
    rw [show a + ε - a = ε by ring] at h
    rw [← h]
    refine setIntegral_congr_fun measurableSet_Ioo fun y _ => ?_
    ring
  have hval : ∫ x in Ioo a (a + ε), ∫ y in Ioo a (a + ε), (u x - u y) ^ 2 / ε = 2 * N := by
    simp_rw [hinner]
    have hc : IntegrableOn (fun _ : ℝ => N) (Ioo a (a + ε)) :=
      integrableOn_Ioo_of_continuous continuous_const
    have i1 : IntegrableOn (fun x => ε * u x ^ 2) (Ioo a (a + ε)) := hi2.const_mul _
    rw [integral_div, integral_add hc i1, integral_const_mul, setIntegral_const,
      Real.volume_real_Ioo_of_le (by linarith), smul_eq_mul, ← hN]
    field_simp
    ring
  calc ENNReal.ofReal (2 * N)
      = ENNReal.ofReal (∫ x in Ioo a (a + ε), ∫ y in Ioo a (a + ε), (u x - u y) ^ 2 / ε) := by
        rw [hval]
    _ ≤ ∫⁻ x in Ioo a (a + ε), ENNReal.ofReal (∫ y in Ioo a (a + ε), (u x - u y) ^ 2 / ε) :=
        ofReal_setIntegral_le_setLIntegral fun x =>
          integral_nonneg fun y => div_nonneg (sq_nonneg _) hε.le
    _ ≤ ∫⁻ x in Ioo a (a + ε), ∫⁻ y in Ioo a (a + ε), ENNReal.ofReal ((u x - u y) ^ 2 / ε) :=
        lintegral_mono fun x => ofReal_setIntegral_le_setLIntegral fun y =>
          div_nonneg (sq_nonneg _) hε.le
    _ ≤ ∫⁻ x in Ioo a (a + ε), ∫⁻ y in Ioo a (a + ε), cauchyDensity u x y := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).mpr
          (Filter.Eventually.of_forall fun x hx => ?_))
        exact lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).mpr
          (Filter.Eventually.of_forall fun y hy => hpt x hx y hy))

/-- **Free point.** A point `y` outside `I = (a, a + ε)` pays at least `‖u‖² W(y)`. -/
theorem lintegral_free_ge {a ε y : ℝ} (hε : 0 < ε) (hy : y ∉ Ioo a (a + ε)) {u : ℝ → ℝ}
    (hu : MemLp u 2 (volume.restrict (Ioo a (a + ε)))) (hu0 : ∫ x in Ioo a (a + ε), u x = 0) :
    ENNReal.ofReal (∫ x in Ioo a (a + ε), u x ^ 2) * farCharge a ε y ≤
      ∫⁻ x in Ioo a (a + ε), cauchyDensity u x y := by
  set m := max (y - a) (a + ε - y) with hm
  have hyo : y ≤ a ∨ a + ε ≤ y := by
    by_contra h
    push Not at h
    exact hy ⟨h.1, h.2⟩
  have hm0 : ε ≤ m := by
    rcases hyo with h | h
    · exact le_max_of_le_right (by linarith)
    · exact le_max_of_le_left (by linarith)
  have hmpos : 0 < m := by linarith
  have hpt : ∀ x ∈ Ioo a (a + ε), ENNReal.ofReal ((u x - u y) ^ 2 / m) ≤ cauchyDensity u x y := by
    intro x hx
    unfold cauchyDensity
    apply ENNReal.ofReal_le_ofReal
    have hxy : x ≠ y := fun h => hy (h ▸ hx)
    have hpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr hxy)
    have hle : |x - y| ≤ m := by
      rw [abs_le]
      constructor
      · have := le_max_left (y - a) (a + ε - y); linarith [hx.1]
      · have := le_max_right (y - a) (a + ε - y); linarith [hx.2]
    exact div_le_div_of_nonneg_left (sq_nonneg _) hpos hle
  have hval : ∫ x in Ioo a (a + ε), (u x - u y) ^ 2 / m =
      ((∫ x in Ioo a (a + ε), u x ^ 2) + ε * u y ^ 2) / m := by
    rw [integral_div, setIntegral_sub_const_sq (by linarith) hu hu0, show a + ε - a = ε by ring]
  have hN : 0 ≤ ∫ x in Ioo a (a + ε), u x ^ 2 := integral_nonneg fun x => sq_nonneg _
  have hfc : farCharge a ε y = ENNReal.ofReal (1 / m) := by
    unfold farCharge
    rw [if_neg hy]
  rw [hfc, ← ENNReal.ofReal_mul hN]
  calc ENNReal.ofReal ((∫ x in Ioo a (a + ε), u x ^ 2) * (1 / m))
      ≤ ENNReal.ofReal (∫ x in Ioo a (a + ε), (u x - u y) ^ 2 / m) := by
        apply ENNReal.ofReal_le_ofReal
        rw [hval, mul_one_div]
        exact div_le_div_of_nonneg_right (by nlinarith [sq_nonneg (u y)]) hmpos.le
    _ ≤ ∫⁻ x in Ioo a (a + ε), ENNReal.ofReal ((u x - u y) ^ 2 / m) :=
        ofReal_setIntegral_le_setLIntegral fun x => div_nonneg (sq_nonneg _) hmpos.le
    _ ≤ ∫⁻ x in Ioo a (a + ε), cauchyDensity u x y :=
        lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).mpr
          (Filter.Eventually.of_forall hpt))

/-- **Pair.** Two disjoint intervals of length `ε` pay both one-sided charges in full. -/
theorem lintegral_pair_ge {a b ε : ℝ} (hε : 0 < ε) (hab : a + ε ≤ b ∨ b + ε ≤ a) {u : ℝ → ℝ}
    (hum : Measurable u) (hua : MemLp u 2 (volume.restrict (Ioo a (a + ε))))
    (hub : MemLp u 2 (volume.restrict (Ioo b (b + ε))))
    (hua0 : ∫ x in Ioo a (a + ε), u x = 0) (hub0 : ∫ y in Ioo b (b + ε), u y = 0) :
    ENNReal.ofReal (∫ x in Ioo a (a + ε), u x ^ 2) * (∫⁻ y in Ioo b (b + ε), farCharge a ε y) +
        ENNReal.ofReal (∫ y in Ioo b (b + ε), u y ^ 2) *
          (∫⁻ x in Ioo a (a + ε), farCharge b ε x) ≤
      ∫⁻ x in Ioo a (a + ε), ∫⁻ y in Ioo b (b + ε), cauchyDensity u x y := by
  rcases hab with hab | hba
  · have h := lintegral_twoInterval_ge (by linarith) hab (by linarith) hum hum hua hub hua0 hub0
    have hw1 : ∫⁻ y in Ioo b (b + ε), farCharge a ε y =
        ∫⁻ y in Ioo b (b + ε), ENNReal.ofReal (1 / (y - a)) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
      have hyn : y ∉ Ioo a (a + ε) := fun h' => by linarith [h'.2, hy.1]
      unfold farCharge
      rw [if_neg hyn, max_eq_left (by linarith [hy.1])]
    have hw2 : ∫⁻ x in Ioo a (a + ε), farCharge b ε x =
        ∫⁻ x in Ioo a (a + ε), ENNReal.ofReal (1 / (b + ε - x)) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      have hxn : x ∉ Ioo b (b + ε) := fun h' => by linarith [h'.1, hx.2]
      unfold farCharge
      rw [if_neg hxn, max_eq_right (by linarith [hx.2])]
    have hk : ∫⁻ x in Ioo a (a + ε), ∫⁻ y in Ioo b (b + ε), cauchyDensity u x y =
        ∫⁻ x in Ioo a (a + ε), ∫⁻ y in Ioo b (b + ε),
          ENNReal.ofReal ((u x - u y) ^ 2 / (y - x)) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun x hx =>
        setLIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
      unfold cauchyDensity
      rw [abs_of_neg (by linarith [hx.2, hy.1] : x - y < 0), neg_sub]
    rw [hw1, hw2, hk]
    exact h
  · have h := lintegral_twoInterval_ge (by linarith) hba (by linarith) hum hum hub hua hub0 hua0
    have hw1 : ∫⁻ y in Ioo b (b + ε), farCharge a ε y =
        ∫⁻ y in Ioo b (b + ε), ENNReal.ofReal (1 / (a + ε - y)) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
      have hyn : y ∉ Ioo a (a + ε) := fun h' => by linarith [h'.1, hy.2]
      unfold farCharge
      rw [if_neg hyn, max_eq_right (by linarith [hy.2])]
    have hw2 : ∫⁻ x in Ioo a (a + ε), farCharge b ε x =
        ∫⁻ x in Ioo a (a + ε), ENNReal.ofReal (1 / (x - b)) := by
      refine setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      have hxn : x ∉ Ioo b (b + ε) := fun h' => by linarith [h'.2, hx.1]
      unfold farCharge
      rw [if_neg hxn, max_eq_left (by linarith [hx.1])]
    have hk : ∫⁻ x in Ioo a (a + ε), ∫⁻ y in Ioo b (b + ε), cauchyDensity u x y =
        ∫⁻ y in Ioo b (b + ε), ∫⁻ x in Ioo a (a + ε),
          ENNReal.ofReal ((u y - u x) ^ 2 / (x - y)) := by
      rw [lintegral_lintegral_swap (measurable_cauchyDensity hum).aemeasurable]
      refine setLIntegral_congr_fun measurableSet_Ioo fun y hy =>
        setLIntegral_congr_fun measurableSet_Ioo fun x hx => ?_
      unfold cauchyDensity
      rw [abs_of_pos (by linarith [hx.1, hy.2] : 0 < x - y),
        show (u x - u y) ^ 2 = (u y - u x) ^ 2 by ring]
    rw [hw1, hw2, hk, add_comm]
    exact h

/-! ## Charges and potential on `(0, 1)` -/

/-- The far charge of `(a, a + ε) ⊆ (0, 1)` over `(0, 1)` is at least
`log((a + ε)/ε) + log((1 − a)/ε)`. -/
theorem farCharge_total_ge {a ε : ℝ} (hε : 0 < ε) (ha0 : 0 ≤ a) (ha1 : a + ε ≤ 1) :
    ENNReal.ofReal (Real.log ((a + ε) / ε) + Real.log ((1 - a) / ε)) ≤
      ∫⁻ y in Ioo 0 1, farCharge a ε y := by
  have h1 : ∫⁻ y in Ioo 0 a, farCharge a ε y = ENNReal.ofReal (Real.log ((a + ε) / ε)) := by
    have e := setLIntegral_one_div_sub_left (b := 0) (c := a) (d := a + ε) ha0 (by linarith)
    rw [sub_zero, add_sub_cancel_left] at e
    rw [← e]
    refine setLIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
    have hyn : y ∉ Ioo a (a + ε) := fun h => by linarith [h.1, hy.2]
    unfold farCharge
    rw [if_neg hyn, max_eq_right (by linarith [hy.2])]
  have h2 : ∫⁻ y in Ioo (a + ε) 1, farCharge a ε y = ENNReal.ofReal (Real.log ((1 - a) / ε)) := by
    have e := setLIntegral_one_div_sub_right (b := a + ε) (c := 1) (d := a) (by linarith) ha1
    rw [add_sub_cancel_left] at e
    rw [← e]
    refine setLIntegral_congr_fun measurableSet_Ioo fun y hy => ?_
    have hyn : y ∉ Ioo a (a + ε) := fun h => by linarith [h.2, hy.1]
    unfold farCharge
    rw [if_neg hyn, max_eq_left (by linarith [hy.1])]
  have hL1 : 0 ≤ Real.log ((a + ε) / ε) :=
    Real.log_nonneg ((le_div_iff₀ hε).mpr (by linarith))
  have hL2 : 0 ≤ Real.log ((1 - a) / ε) :=
    Real.log_nonneg ((le_div_iff₀ hε).mpr (by linarith))
  have hdisj : Disjoint (Ioo 0 a) (Ioo (a + ε) 1) :=
    Set.disjoint_left.mpr fun y hy hy' => by linarith [hy.2, hy'.1]
  rw [ENNReal.ofReal_add hL1 hL2, ← h1, ← h2, ← lintegral_union measurableSet_Ioo hdisj]
  exact lintegral_mono_set (union_subset (Ioo_subset_Ioo le_rfl (by linarith))
    (Ioo_subset_Ioo (by linarith) le_rfl))

/-- On `(a, a + ε) ⊆ (0, 1)` the endpoint potential is at least `−½ log((a + ε)(1 − a)) ‖u‖²`. -/
theorem potential_ge {a ε : ℝ} (hε : 0 < ε) (ha0 : 0 ≤ a) (ha1 : a + ε ≤ 1) {u : ℝ → ℝ} :
    ENNReal.ofReal (-(1 / 2) * Real.log ((a + ε) * (1 - a)) * ∫ x in Ioo a (a + ε), u x ^ 2) ≤
      ∫⁻ x in Ioo a (a + ε), ENNReal.ofReal (-(1 / 2) * Real.log (x * (1 - x)) * u x ^ 2) := by
  have hc : 0 ≤ -(1 / 2) * Real.log ((a + ε) * (1 - a)) := by
    have : Real.log ((a + ε) * (1 - a)) ≤ 0 :=
      Real.log_nonpos (mul_nonneg (by linarith) (by linarith)) (by nlinarith)
    linarith
  rw [← integral_const_mul]
  refine (ofReal_setIntegral_le_setLIntegral fun x => mul_nonneg hc (sq_nonneg _)).trans ?_
  refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioo).mpr
    (Filter.Eventually.of_forall fun x hx => ?_))
  apply ENNReal.ofReal_le_ofReal
  have hx0 : 0 < x * (1 - x) := mul_pos (by linarith [hx.1]) (by linarith [hx.2])
  have hle : x * (1 - x) ≤ (a + ε) * (1 - a) :=
    mul_le_mul hx.2.le (by linarith [hx.1]) (by linarith [hx.2]) (by linarith)
  have hlog := Real.log_le_log hx0 hle
  have := sq_nonneg (u x)
  nlinarith

/-! ## Decomposing the unit square -/

section Decomposition

variable {ι : Type*} [Fintype ι] {I : ι → Set ℝ}

/-- `∫_{(0,1)} = Σ_ν ∫_{I_ν} + ∫_F`, where `F = (0, 1) \ ⋃ I`. -/
theorem lintegral_Ioo_eq_sum (hIm : ∀ ν, MeasurableSet (I ν)) (hIsub : ∀ ν, I ν ⊆ Ioo 0 1)
    (hpd : Pairwise (Function.onFun Disjoint I)) (g : ℝ → ℝ≥0∞) :
    ∫⁻ x in Ioo 0 1, g x = (∑ ν, ∫⁻ x in I ν, g x) + ∫⁻ x in Ioo 0 1 \ ⋃ μ, I μ, g x := by
  have hU : Ioo (0 : ℝ) 1 = (⋃ μ, I μ) ∪ (Ioo 0 1 \ ⋃ μ, I μ) :=
    (union_sdiff_cancel (iUnion_subset hIsub)).symm
  have hFm : MeasurableSet (Ioo (0 : ℝ) 1 \ ⋃ μ, I μ) :=
    measurableSet_Ioo.diff (MeasurableSet.iUnion hIm)
  conv_lhs => rw [hU]
  rw [lintegral_union hFm disjoint_sdiff_right, lintegral_iUnion hIm hpd, tsum_fintype]

/-- The double integral over `(0, 1)²` dominates every source–source block once and every
source–free block twice. -/
theorem sum_blocks_le_lintegral_square (hIm : ∀ ν, MeasurableSet (I ν))
    (hIsub : ∀ ν, I ν ⊆ Ioo 0 1) (hpd : Pairwise (Function.onFun Disjoint I))
    {h : ℝ → ℝ → ℝ≥0∞} (hhm : Measurable fun p : ℝ × ℝ => h p.1 p.2)
    (hsymm : ∀ x y, h x y = h y x) :
    ∑ ν, ((∑ μ, ∫⁻ x in I ν, ∫⁻ y in I μ, h x y) +
        2 * ∫⁻ x in I ν, ∫⁻ y in Ioo 0 1 \ ⋃ μ, I μ, h x y) ≤
      ∫⁻ x in Ioo 0 1, ∫⁻ y in Ioo 0 1, h x y := by
  set F := Ioo (0 : ℝ) 1 \ ⋃ μ, I μ with hF
  have hGm : ∀ A : Set ℝ, Measurable fun x => ∫⁻ y in A, h x y := fun A =>
    hhm.lintegral_prod_right'
  have hinner : ∀ x, ∫⁻ y in Ioo 0 1, h x y = (∑ μ, ∫⁻ y in I μ, h x y) + ∫⁻ y in F, h x y :=
    fun x => lintegral_Ioo_eq_sum hIm hIsub hpd (h x)
  have hsrc : ∀ ν, ∫⁻ x in I ν, ∫⁻ y in Ioo 0 1, h x y =
      (∑ μ, ∫⁻ x in I ν, ∫⁻ y in I μ, h x y) + ∫⁻ x in I ν, ∫⁻ y in F, h x y := by
    intro ν
    rw [lintegral_congr fun x => hinner x,
      lintegral_add_left (Finset.measurable_sum _ fun μ _ => hGm (I μ)),
      lintegral_finsetSum _ fun μ _ => hGm (I μ)]
  have hfree : ∑ ν, ∫⁻ x in I ν, ∫⁻ y in F, h x y ≤ ∫⁻ x in F, ∫⁻ y in Ioo 0 1, h x y := by
    calc ∑ ν, ∫⁻ x in I ν, ∫⁻ y in F, h x y
        = ∑ ν, ∫⁻ x in F, ∫⁻ y in I ν, h x y := by
          refine Finset.sum_congr rfl fun ν _ => ?_
          rw [lintegral_lintegral_swap hhm.aemeasurable]
          exact lintegral_congr fun y => lintegral_congr fun x => hsymm x y
      _ = ∫⁻ x in F, ∑ ν, ∫⁻ y in I ν, h x y :=
          (lintegral_finsetSum _ fun ν _ => hGm (I ν)).symm
      _ ≤ ∫⁻ x in F, ∫⁻ y in Ioo 0 1, h x y :=
          lintegral_mono fun x => (hinner x).symm ▸ le_self_add
  calc ∑ ν, ((∑ μ, ∫⁻ x in I ν, ∫⁻ y in I μ, h x y) + 2 * ∫⁻ x in I ν, ∫⁻ y in F, h x y)
      = (∑ ν, ((∑ μ, ∫⁻ x in I ν, ∫⁻ y in I μ, h x y) + ∫⁻ x in I ν, ∫⁻ y in F, h x y)) +
          ∑ ν, ∫⁻ x in I ν, ∫⁻ y in F, h x y := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun ν _ => ?_
        rw [two_mul, add_assoc]
    _ ≤ (∑ ν, ∫⁻ x in I ν, ∫⁻ y in Ioo 0 1, h x y) + ∫⁻ x in F, ∫⁻ y in Ioo 0 1, h x y := by
        rw [Finset.sum_congr rfl fun ν _ => (hsrc ν).symm]
        exact add_le_add le_rfl hfree
    _ = ∫⁻ x in Ioo 0 1, ∫⁻ y in Ioo 0 1, h x y :=
        (lintegral_Ioo_eq_sum hIm hIsub hpd _).symm

end Decomposition

/-! ## Coherent multi-source capacity -/

/-- **Coherent multi-source capacity.** Let `I_ν = (a_ν, a_ν + ε) ⊆ (0, 1)` be pairwise disjoint and
let `u` have mean zero on every `I_ν`. Then the boundary form
`¼ ∫∫_{(0,1)²} (u(x) − u(y))²/|x − y| − ½ ∫_{(0,1)} log(x(1 − x)) u(x)²` is at least
`(log(1/ε) + ½) Σ_ν ‖u‖²_{L²(I_ν)}`. -/
theorem capacity_multiSource {ι : Type*} [Fintype ι] {ε : ℝ} (hε : 0 < ε) {a : ι → ℝ}
    (ha0 : ∀ ν, 0 ≤ a ν) (ha1 : ∀ ν, a ν + ε ≤ 1)
    (hdisj : ∀ ν μ, ν ≠ μ → a ν + ε ≤ a μ ∨ a μ + ε ≤ a ν)
    {u : ℝ → ℝ} (hum : Measurable u)
    (hu : ∀ ν, MemLp u 2 (volume.restrict (Ioo (a ν) (a ν + ε))))
    (hu0 : ∀ ν, ∫ x in Ioo (a ν) (a ν + ε), u x = 0) :
    ENNReal.ofReal ((Real.log (1 / ε) + 1 / 2) * ∑ ν, ∫ x in Ioo (a ν) (a ν + ε), u x ^ 2) ≤
      ENNReal.ofReal (1 / 4) * (∫⁻ x in Ioo 0 1, ∫⁻ y in Ioo 0 1, cauchyDensity u x y) +
        ∫⁻ x in Ioo 0 1, ENNReal.ofReal (-(1 / 2) * Real.log (x * (1 - x)) * u x ^ 2) := by
  classical
  set I : ι → Set ℝ := fun ν => Ioo (a ν) (a ν + ε) with hIdef
  set N : ι → ℝ := fun ν => ∫ x in Ioo (a ν) (a ν + ε), u x ^ 2 with hNdef
  set L : ι → ℝ := fun ν => Real.log ((a ν + ε) / ε) + Real.log ((1 - a ν) / ε) with hLdef
  set c : ι → ℝ := fun ν => -(1 / 2) * Real.log ((a ν + ε) * (1 - a ν)) with hcdef
  set F := Ioo (0 : ℝ) 1 \ ⋃ μ, I μ with hF
  have hIm : ∀ ν, MeasurableSet (I ν) := fun ν => measurableSet_Ioo
  have hFm : MeasurableSet F := measurableSet_Ioo.diff (MeasurableSet.iUnion hIm)
  have hIsub : ∀ ν, I ν ⊆ Ioo 0 1 := fun ν x hx =>
    ⟨by linarith [ha0 ν, hx.1], by linarith [ha1 ν, hx.2]⟩
  have hpd : Pairwise (Function.onFun Disjoint I) := by
    intro ν μ hne
    refine Set.disjoint_left.mpr fun x hx hx' => ?_
    rcases hdisj ν μ hne with h | h
    · linarith [hx.2, hx'.1]
    · linarith [hx.1, hx'.2]
  have hN0 : ∀ ν, 0 ≤ N ν := fun ν => integral_nonneg fun x => sq_nonneg _
  have hL0 : ∀ ν, 0 ≤ L ν := fun ν => add_nonneg
    (Real.log_nonneg ((le_div_iff₀ hε).mpr (by linarith [ha0 ν])))
    (Real.log_nonneg ((le_div_iff₀ hε).mpr (by linarith [ha1 ν])))
  have hc0 : ∀ ν, 0 ≤ c ν := fun ν => by
    have : Real.log ((a ν + ε) * (1 - a ν)) ≤ 0 :=
      Real.log_nonpos (mul_nonneg (by linarith [ha0 ν]) (by linarith [ha1 ν]))
        (by nlinarith [ha0 ν, ha1 ν])
    simp only [hcdef]
    linarith
  -- block bounds
  have hCdiag : ∀ ν, ∫⁻ y in I ν, farCharge (a ν) ε y = 0 := fun ν => by
    have : ∫⁻ y in I ν, farCharge (a ν) ε y = ∫⁻ y in I ν, (0 : ℝ≥0∞) :=
      setLIntegral_congr_fun (hIm ν) fun y hy => by
        unfold farCharge
        exact if_pos hy
    rw [this, lintegral_zero]
  have hP : ∀ ν μ, (if ν = μ then ENNReal.ofReal (2 * N ν) else 0) +
      ENNReal.ofReal (N ν) * (∫⁻ y in I μ, farCharge (a ν) ε y) +
      ENNReal.ofReal (N μ) * (∫⁻ y in I ν, farCharge (a μ) ε y) ≤
      ∫⁻ x in I ν, ∫⁻ y in I μ, cauchyDensity u x y := by
    intro ν μ
    by_cases hνμ : ν = μ
    · subst hνμ
      rw [if_pos rfl, hCdiag, mul_zero, add_zero, add_zero]
      exact lintegral_self_ge hε (hu ν) (hu0 ν)
    · rw [if_neg hνμ, zero_add]
      exact lintegral_pair_ge hε (hdisj ν μ hνμ) hum (hu ν) (hu μ) (hu0 ν) (hu0 μ)
  have hQ : ∀ ν, ENNReal.ofReal (N ν) * (∫⁻ y in F, farCharge (a ν) ε y) ≤
      ∫⁻ x in I ν, ∫⁻ y in F, cauchyDensity u x y := by
    intro ν
    rw [lintegral_lintegral_swap (measurable_cauchyDensity hum).aemeasurable,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_mono_ae ((ae_restrict_iff' hFm).mpr
      (Filter.Eventually.of_forall fun y hy => ?_))
    have hyn : y ∉ Ioo (a ν) (a ν + ε) := fun h => hy.2 (mem_iUnion.mpr ⟨ν, h⟩)
    exact lintegral_free_ge hε hyn (hu ν) (hu0 ν)
  -- the energy bound
  have hE : ENNReal.ofReal (∑ ν, 2 * N ν * (1 + L ν)) ≤
      ∫⁻ x in Ioo 0 1, ∫⁻ y in Ioo 0 1, cauchyDensity u x y := by
    refine le_trans ?_ (sum_blocks_le_lintegral_square hIm hIsub hpd
      (measurable_cauchyDensity hum) (cauchyDensity_comm u))
    set n : ι → ℝ≥0∞ := fun ν => ENNReal.ofReal (N ν) with hn
    set C : ι → ι → ℝ≥0∞ := fun ν μ => ∫⁻ y in I μ, farCharge (a ν) ε y with hC
    set G : ι → ℝ≥0∞ := fun ν => ∫⁻ y in F, farCharge (a ν) ε y with hG
    have hW : ∀ ν, ENNReal.ofReal (L ν) ≤ (∑ μ, C ν μ) + G ν := fun ν => by
      rw [← lintegral_Ioo_eq_sum hIm hIsub hpd]
      exact farCharge_total_ge hε (ha0 ν) (ha1 ν)
    have hsplit : ∀ ν, ENNReal.ofReal (2 * N ν * (1 + L ν)) =
        ENNReal.ofReal (2 * N ν) + 2 * (n ν * ENNReal.ofReal (L ν)) := fun ν => by
      have h2 : (0 : ℝ) ≤ 2 * N ν := by linarith [hN0 ν]
      have h3 : (0 : ℝ) ≤ 2 * (N ν * L ν) :=
        mul_nonneg (by norm_num) (mul_nonneg (hN0 ν) (hL0 ν))
      rw [show 2 * N ν * (1 + L ν) = 2 * N ν + 2 * (N ν * L ν) by ring,
        ENNReal.ofReal_add h2 h3]
      congr 1
      rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_mul (hN0 ν),
        ENNReal.ofReal_ofNat]
    have hcomm : ∑ ν, ∑ μ, n μ * C μ ν = ∑ ν, n ν * ∑ μ, C ν μ := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun ν _ => (Finset.mul_sum _ _ _).symm
    calc ENNReal.ofReal (∑ ν, 2 * N ν * (1 + L ν))
        = ∑ ν, (ENNReal.ofReal (2 * N ν) + 2 * (n ν * ENNReal.ofReal (L ν))) := by
          rw [ENNReal.ofReal_sum_of_nonneg fun ν _ => by
            have := hN0 ν; have := hL0 ν; positivity]
          exact Finset.sum_congr rfl fun ν _ => hsplit ν
      _ ≤ ∑ ν, (ENNReal.ofReal (2 * N ν) + 2 * (n ν * ((∑ μ, C ν μ) + G ν))) := by
          gcongr with ν
          exact hW ν
      _ = ∑ ν, ((∑ μ, ((if ν = μ then ENNReal.ofReal (2 * N ν) else 0) + n ν * C ν μ +
            n μ * C μ ν)) + 2 * (n ν * G ν)) := by
          simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
          rw [hcomm, ← Finset.mul_sum]
          simp only [mul_add, Finset.mul_sum, Finset.sum_add_distrib, two_mul]
          ring
      _ ≤ ∑ ν, ((∑ μ, ∫⁻ x in I ν, ∫⁻ y in I μ, cauchyDensity u x y) +
            2 * ∫⁻ x in I ν, ∫⁻ y in F, cauchyDensity u x y) := by
          gcongr with ν μ
          · exact hP ν μ
          · exact hQ ν
  -- the potential bound
  have hPot : ENNReal.ofReal (∑ ν, c ν * N ν) ≤
      ∫⁻ x in Ioo 0 1, ENNReal.ofReal (-(1 / 2) * Real.log (x * (1 - x)) * u x ^ 2) := by
    rw [lintegral_Ioo_eq_sum hIm hIsub hpd, ENNReal.ofReal_sum_of_nonneg fun ν _ =>
      mul_nonneg (hc0 ν) (hN0 ν)]
    refine le_trans ?_ le_self_add
    exact Finset.sum_le_sum fun ν _ => potential_ge hε (ha0 ν) (ha1 ν)
  -- the logarithms cancel
  have hid : ∀ ν, 2 * N ν * (1 + L ν) / 4 + c ν * N ν = (Real.log (1 / ε) + 1 / 2) * N ν := by
    intro ν
    have hae : 0 < a ν + ε := by linarith [ha0 ν]
    have h1a : 0 < 1 - a ν := by linarith [ha1 ν]
    simp only [hLdef, hcdef]
    rw [Real.log_div hae.ne' hε.ne', Real.log_div h1a.ne' hε.ne', Real.log_mul hae.ne' h1a.ne',
      Real.log_div one_ne_zero hε.ne', Real.log_one]
    ring
  have hfinal : (Real.log (1 / ε) + 1 / 2) * ∑ ν, N ν =
      (1 / 4) * (∑ ν, 2 * N ν * (1 + L ν)) + ∑ ν, c ν * N ν := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ν _ => ?_
    rw [← hid ν]
    ring
  have hS0 : 0 ≤ ∑ ν, 2 * N ν * (1 + L ν) := Finset.sum_nonneg fun ν _ => by
    have := hN0 ν; have := hL0 ν; positivity
  have hT0 : 0 ≤ ∑ ν, c ν * N ν := Finset.sum_nonneg fun ν _ => mul_nonneg (hc0 ν) (hN0 ν)
  calc ENNReal.ofReal ((Real.log (1 / ε) + 1 / 2) * ∑ ν, N ν)
      = ENNReal.ofReal (1 / 4) * ENNReal.ofReal (∑ ν, 2 * N ν * (1 + L ν)) +
          ENNReal.ofReal (∑ ν, c ν * N ν) := by
        rw [hfinal, ENNReal.ofReal_add (by positivity) hT0,
          ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
    _ ≤ ENNReal.ofReal (1 / 4) * (∫⁻ x in Ioo 0 1, ∫⁻ y in Ioo 0 1, cauchyDensity u x y) +
          ∫⁻ x in Ioo 0 1, ENNReal.ofReal (-(1 / 2) * Real.log (x * (1 - x)) * u x ^ 2) := by
        gcongr

end GaloisForLFunctions.HTGeometry.CauchyDifference
