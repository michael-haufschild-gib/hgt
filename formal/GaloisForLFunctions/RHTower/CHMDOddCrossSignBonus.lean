import GaloisForLFunctions.RHTower.CHMDOddWindowCrossSign

/-!
# The cross-sign bonus of the Lévy form on one-signed odd tests

For a test `f` that is nonpositive on `(−∞, 0]` and nonnegative on `[0, ∞)` (for instance `Θv`
with `v` odd and nonnegative on the right), the jump `(f(u) − f(u+x))²` across the origin equals
`(|f(u)| − |f(u+x)|)² + 4|f(u)||f(u+x)|`, while jumps on one side are unchanged. Integrating
against the archimedean Lévy density gives the exact identity

`Λ_∞(f) = Λ_∞(|f|) + 4 ∬_{s,t>0} |f|(s) |f|(t) ω(s+t) ds dt`

(the second factor is written on the quadrant after the shear `(s,t) ↦ (s+t, −s)`). The bonus is
nonnegative, so on the one-signed odd cone with support in `(−log 2, log 2)` the arithmetic Doob
energy dominates `Λ_∞(Θ|v|) + 4·bonus(Θ|v|)`.
-/

open MeasureTheory Set Filter Topology Zeta23
open scoped InnerProductSpace ENNReal
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph NonnegativeCone

/-! ## The bonus -/

/-- The cross-sign pairing `∫_{x>0} ω(x) ∫_{−x<u<0} g(u) g(u+x) du dx` as an extended real. -/
def crossSignBonusL (g : ℝ → ℝ) : ℝ≥0∞ :=
  ∫⁻ x in Ioi (0 : ℝ), ENNReal.ofReal (jumpKernel x * ∫ u in Ioo (-x) 0, g u * g (u + x))

/-- The cross-sign pairing as a real number. -/
def crossSignBonus (g : ℝ → ℝ) : ℝ := (crossSignBonusL g).toReal

theorem crossSignBonus_nonneg (g : ℝ → ℝ) : 0 ≤ crossSignBonus g := ENNReal.toReal_nonneg

/-! ## The pointwise and integrated jump identities -/

theorem sq_sub_eq_sq_abs_sub_add {f : ℝ → ℝ} (hpos : ∀ u, 0 ≤ u → 0 ≤ f u)
    (hneg : ∀ u, u ≤ 0 → f u ≤ 0) {x : ℝ} (hx : 0 < x) (u : ℝ) :
    (f u - f (u + x)) ^ 2 =
      (|f u| - |f (u + x)|) ^ 2 + 4 * (Ioo (-x) 0).indicator (fun u => |f u| * |f (u + x)|) u := by
  by_cases hu : u ∈ Ioo (-x) 0
  · rw [Set.indicator_of_mem hu]
    rw [abs_of_nonpos (hneg u hu.2.le), abs_of_nonneg (hpos _ (by linarith [hu.1]))]
    ring
  · rw [Set.indicator_of_notMem hu, mul_zero, add_zero]
    rw [Set.mem_Ioo, not_and_or, not_lt, not_lt] at hu
    rcases hu with hu | hu
    · rw [abs_of_nonpos (hneg u (by linarith)), abs_of_nonpos (hneg _ (by linarith))]
      ring
    · rw [abs_of_nonneg (hpos u hu), abs_of_nonneg (hpos _ (by linarith))]

theorem hasCompactSupport_abs_mul_shift {f : ℝ → ℝ} (hfc : HasCompactSupport f) (x : ℝ) :
    HasCompactSupport fun u => |f u| * |f (u + x)| :=
  (hfc.comp_left (g := abs) abs_zero).mul_right

theorem continuous_abs_mul_shift {f : ℝ → ℝ} (hf : Continuous f) (x : ℝ) :
    Continuous fun u => |f u| * |f (u + x)| :=
  hf.abs.mul (hf.abs.comp (continuous_id.add continuous_const))

theorem integrable_sq_abs_sub {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (x : ℝ) : Integrable fun u => (|f u| - |f (u + x)|) ^ 2 := by
  have hc : Continuous fun u => |f u| - |f (u + x)| :=
    hf.abs.sub (hf.abs.comp (continuous_id.add continuous_const))
  have hcs : HasCompactSupport fun u => |f u| - |f (u + x)| :=
    (hfc.comp_left (g := abs) abs_zero).sub
      ((hfc.comp_left (g := abs) abs_zero).comp_homeomorph (Homeomorph.addRight x))
  have e : (fun u => (|f u| - |f (u + x)|) ^ 2) =
      (fun u => |f u| - |f (u + x)|) * (fun u => |f u| - |f (u + x)|) := by
    funext u
    simp [pow_two]
  rw [e]
  exact (hc.mul hc).integrable_of_hasCompactSupport hcs.mul_left

/-- Integrated form: the jump integral splits into the absolute-value jump integral plus four
times the cross-sign pairing on `(−x, 0)`. -/
theorem integral_sq_sub_eq_abs_add {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hpos : ∀ u, 0 ≤ u → 0 ≤ f u) (hneg : ∀ u, u ≤ 0 → f u ≤ 0) {x : ℝ} (hx : 0 < x) :
    (∫ u, (f u - f (u + x)) ^ 2) =
      (∫ u, (|f u| - |f (u + x)|) ^ 2) + 4 * ∫ u in Ioo (-x) 0, |f u| * |f (u + x)| := by
  have hint1 := integrable_sq_abs_sub hf hfc x
  have hint2 : Integrable fun u => (Ioo (-x) 0).indicator (fun u => |f u| * |f (u + x)|) u :=
    ((continuous_abs_mul_shift hf x).integrable_of_hasCompactSupport
      (hasCompactSupport_abs_mul_shift hfc x)).indicator measurableSet_Ioo
  calc (∫ u, (f u - f (u + x)) ^ 2)
      = ∫ u, ((|f u| - |f (u + x)|) ^ 2 +
          4 * (Ioo (-x) 0).indicator (fun u => |f u| * |f (u + x)|) u) := by
        congr 1
        funext u
        exact sq_sub_eq_sq_abs_sub_add hpos hneg hx u
    _ = (∫ u, (|f u| - |f (u + x)|) ^ 2) +
          ∫ u, 4 * (Ioo (-x) 0).indicator (fun u => |f u| * |f (u + x)|) u :=
        integral_add hint1 (hint2.const_mul 4)
    _ = (∫ u, (|f u| - |f (u + x)|) ^ 2) +
          4 * ∫ u, (Ioo (-x) 0).indicator (fun u => |f u| * |f (u + x)|) u := by
        rw [integral_const_mul]
    _ = (∫ u, (|f u| - |f (u + x)|) ^ 2) + 4 * ∫ u in Ioo (-x) 0, |f u| * |f (u + x)| := by
        rw [integral_indicator measurableSet_Ioo]

/-! ## Measurability of the parametric integrals -/

theorem measurable_integral_sq_abs_sub {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable fun x => ∫ u, (|f u| - |f (u + x)|) ^ 2 := by
  have hc : Continuous fun p : ℝ × ℝ => (|f p.2| - |f (p.2 + p.1)|) ^ 2 :=
    ((hf.abs.comp continuous_snd).sub (hf.abs.comp (continuous_snd.add continuous_fst))).pow 2
  exact (hc.stronglyMeasurable.integral_prod_right').measurable

theorem measurable_integral_cross {f : ℝ → ℝ} (hf : Continuous f) :
    Measurable fun x => ∫ u in Ioo (-x) 0, |f u| * |f (u + x)| := by
  set G : ℝ × ℝ → ℝ := {q : ℝ × ℝ | -q.1 < q.2 ∧ q.2 < 0}.indicator
    (fun q => |f q.2| * |f (q.2 + q.1)|) with hG
  have hGm : StronglyMeasurable G := by
    refine Measurable.stronglyMeasurable (Measurable.indicator ?_ ?_)
    · exact ((hf.abs.comp continuous_snd).mul
        (hf.abs.comp (continuous_snd.add continuous_fst))).measurable
    · exact (measurableSet_lt measurable_fst.neg measurable_snd).inter
        (measurableSet_lt measurable_snd measurable_const)
  have e : (fun x => ∫ u in Ioo (-x) 0, |f u| * |f (u + x)|) = fun x => ∫ u, G (x, u) := by
    funext x
    rw [← integral_indicator measurableSet_Ioo]
    congr 1
  rw [e]
  exact (hGm.integral_prod_right').measurable

/-! ## The jump-energy identity -/

/-- **Cross-sign bonus of the jump energy.** -/
theorem jumpEnergy_eq_abs_add_bonus {f : ℝ → ℝ} (hf : Continuous f) (hfc : HasCompactSupport f)
    (hpos : ∀ u, 0 ≤ u → 0 ≤ f u) (hneg : ∀ u, u ≤ 0 → f u ≤ 0) :
    jumpEnergy f = jumpEnergy (fun u => |f u|) + 4 * crossSignBonusL (fun u => |f u|) := by
  rw [jumpEnergy_eq, jumpEnergy_eq]
  unfold crossSignBonusL
  have hm1 : Measurable fun x =>
      ENNReal.ofReal (jumpKernel x * ∫ u, (|f u| - |f (u + x)|) ^ 2) :=
    (measurable_jumpKernel.mul (measurable_integral_sq_abs_sub hf)).ennreal_ofReal
  have hm2 : Measurable fun x =>
      ENNReal.ofReal (jumpKernel x * ∫ u in Ioo (-x) 0, |f u| * |f (u + x)|) :=
    (measurable_jumpKernel.mul (measurable_integral_cross hf)).ennreal_ofReal
  have hsplit : Set.EqOn (fun x => ENNReal.ofReal (jumpKernel x * ∫ u, (f u - f (u + x)) ^ 2))
      (fun x => ENNReal.ofReal (jumpKernel x * ∫ u, (|f u| - |f (u + x)|) ^ 2) +
        4 * ENNReal.ofReal (jumpKernel x * ∫ u in Ioo (-x) 0, |f u| * |f (u + x)|))
      (Ioi 0) := by
    intro x hx
    simp only
    have hB : 0 ≤ ∫ u in Ioo (-x) 0, |f u| * |f (u + x)| :=
      setIntegral_nonneg measurableSet_Ioo fun u _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    rw [integral_sq_sub_eq_abs_add hf hfc hpos hneg hx, mul_add,
      ENNReal.ofReal_add (mul_nonneg (jumpKernel_nonneg x) (integral_nonneg fun u => sq_nonneg _))
        (mul_nonneg (jumpKernel_nonneg x) (mul_nonneg (by norm_num) hB))]
    congr 1
    rw [show jumpKernel x * (4 * ∫ u in Ioo (-x) 0, |f u| * |f (u + x)|) =
        4 * (jumpKernel x * ∫ u in Ioo (-x) 0, |f u| * |f (u + x)|) by ring,
      ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat]
  rw [setLIntegral_congr_fun measurableSet_Ioi hsplit, lintegral_add_left hm1,
    lintegral_const_mul 4 hm2]

/-- **Cross-sign bonus of the Lévy form.** For a test nonpositive on `(−∞,0]` and nonnegative on
`[0,∞)`, `Λ_∞(f) = Λ_∞(|f|) + 4·bonus(|f|)`. -/
theorem weilLevyForm_eq_abs_add_bonus {f : ℝ → ℝ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hpos : ∀ u, 0 ≤ u → 0 ≤ f u) (hneg : ∀ u, u ≤ 0 → f u ≤ 0) :
    weilLevyForm f = weilLevyForm (fun u => |f u|) + 4 * crossSignBonus (fun u => |f u|) := by
  have hJ := jumpEnergy_eq_abs_add_bonus hf.continuous hfc hpos hneg
  have hfin := jumpEnergy_ne_top_of_smooth hf hfc
  rw [hJ] at hfin
  obtain ⟨h1, h2⟩ := ENNReal.add_ne_top.mp hfin
  have h3 : crossSignBonusL (fun u => |f u|) ≠ ⊤ := by
    intro h
    rw [h] at h2
    exact h2 (ENNReal.mul_top (by norm_num))
  unfold weilLevyForm crossSignBonus
  rw [hJ, ENNReal.toReal_add h1 h2, ENNReal.toReal_mul, ENNReal.toReal_ofNat]
  have hsq : (∫ u, |f u| ^ 2) = ∫ u, f u ^ 2 := by
    congr 1
    funext u
    exact sq_abs _
  rw [hsq]
  ring

/-! ## The quadrant form of the bonus -/

/-- The shear `(s, t) ↦ (s + t, −s)` preserves planar Lebesgue measure. -/
theorem measurePreserving_shear :
    MeasurePreserving (fun q : ℝ × ℝ => (q.1 + q.2, -q.1))
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) := by
  have h1 := measurePreserving_prod_add (volume : Measure ℝ) volume
  have h2 : MeasurePreserving Prod.swap ((volume : Measure ℝ).prod volume)
      ((volume : Measure ℝ).prod volume) := Measure.measurePreserving_swap
  have h3 : MeasurePreserving (Prod.map (id : ℝ → ℝ) (Neg.neg : ℝ → ℝ))
      ((volume : Measure ℝ).prod volume) ((volume : Measure ℝ).prod volume) :=
    (MeasurePreserving.id _).prod (Measure.measurePreserving_neg volume)
  have h := (h3.comp h2).comp h1
  have e : (fun q : ℝ × ℝ => (q.1 + q.2, -q.1)) =
      Prod.map (id : ℝ → ℝ) (Neg.neg : ℝ → ℝ) ∘ (Prod.swap ∘ fun z : ℝ × ℝ => (z.1, z.1 + z.2)) := by
    funext q
    rfl
  rw [e]
  exact h

/-- The planar integrand of the bonus: the region `0 < x`, `−x < u < 0`. -/
def bonusPlanar (g : ℝ → ℝ) (p : ℝ × ℝ) : ℝ≥0∞ :=
  {q : ℝ × ℝ | 0 < q.1 ∧ -q.1 < q.2 ∧ q.2 < 0}.indicator
    (fun q => ENNReal.ofReal (jumpKernel q.1 * (g q.2 * g (q.2 + q.1)))) p

theorem measurableSet_bonusRegion :
    MeasurableSet {q : ℝ × ℝ | 0 < q.1 ∧ -q.1 < q.2 ∧ q.2 < 0} := by
  simp only [Set.setOf_and]
  exact (measurableSet_lt measurable_const measurable_fst).inter
    ((measurableSet_lt measurable_fst.neg measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_const))

theorem measurable_bonusPlanar {g : ℝ → ℝ} (hg : Continuous g) : Measurable (bonusPlanar g) :=
  Measurable.indicator ((measurable_jumpKernel.comp measurable_fst).mul
    ((hg.comp continuous_snd).mul (hg.comp (continuous_snd.add continuous_fst))).measurable
      |>.ennreal_ofReal) measurableSet_bonusRegion

theorem ofReal_inner_eq_lintegral {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ u, 0 ≤ g u) {x : ℝ}
    (_hx : 0 < x) :
    ENNReal.ofReal (jumpKernel x * ∫ u in Ioo (-x) 0, g u * g (u + x)) =
      ∫⁻ u in Ioo (-x) 0, ENNReal.ofReal (jumpKernel x * (g u * g (u + x))) := by
  have hc : Continuous fun u => g u * g (u + x) :=
    hg.mul (hg.comp (continuous_id.add continuous_const))
  have hint : IntegrableOn (fun u => g u * g (u + x)) (Ioo (-x) 0) :=
    hc.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hmeas : Measurable fun u => ENNReal.ofReal (g u * g (u + x)) :=
    hc.measurable.ennreal_ofReal
  rw [ENNReal.ofReal_mul (jumpKernel_nonneg x),
    ofReal_integral_eq_lintegral_ofReal hint
      (Eventually.of_forall fun u => mul_nonneg (hg0 u) (hg0 _)),
    ← lintegral_const_mul _ hmeas]
  congr 1
  funext u
  rw [← ENNReal.ofReal_mul (jumpKernel_nonneg x)]

/-- Tonelli: the bonus is the planar integral of `bonusPlanar`. -/
theorem crossSignBonusL_eq_planar {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ u, 0 ≤ g u) :
    crossSignBonusL g = ∫⁻ p, bonusPlanar g p ∂((volume : Measure ℝ).prod volume) := by
  rw [lintegral_prod _ (measurable_bonusPlanar hg).aemeasurable]
  unfold crossSignBonusL
  rw [← lintegral_indicator measurableSet_Ioi]
  congr 1
  funext x
  by_cases hx : 0 < x
  · rw [Set.indicator_of_mem (mem_Ioi.mpr hx), ofReal_inner_eq_lintegral hg hg0 hx,
      ← lintegral_indicator measurableSet_Ioo]
    congr 1
    funext u
    simp only [bonusPlanar, Set.indicator_apply, Set.mem_setOf_eq, Set.mem_Ioo, hx, true_and]
  · rw [Set.indicator_of_notMem (by simpa using hx)]
    have h0 : ∀ u, bonusPlanar g (x, u) = 0 := fun u => by
      simp only [bonusPlanar, Set.indicator_apply, Set.mem_setOf_eq]
      rw [if_neg]
      intro h
      exact hx h.1
    simp [h0]

/-- The shear turns the planar integrand into the quadrant integrand `ω(s+t) g(s) g(t)`. -/
theorem lintegral_bonusPlanar_eq_quadrant {g : ℝ → ℝ} (hg : Continuous g)
    (heven : ∀ u, g (-u) = g u) :
    ∫⁻ p, bonusPlanar g p ∂((volume : Measure ℝ).prod volume) =
      ∫⁻ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
        ENNReal.ofReal (archLevyDensity (q.1 + q.2) * (g q.1 * g q.2))
          ∂((volume : Measure ℝ).prod volume) := by
  rw [← measurePreserving_shear.lintegral_comp (measurable_bonusPlanar hg),
    ← lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioi)]
  congr 1
  funext q
  simp only [bonusPlanar, Set.indicator_apply, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ioi]
  by_cases h : 0 < q.1 ∧ 0 < q.2
  · rw [if_pos ⟨by linarith [h.1, h.2], by linarith [h.2], by linarith [h.1]⟩, if_pos h, heven,
      show -q.1 + (q.1 + q.2) = q.2 by ring, jumpKernel_of_pos (by linarith [h.1, h.2])]
  · rw [if_neg h, if_neg]
    intro h'
    exact h ⟨by linarith [h'.2.2], by linarith [h'.2.1]⟩

/-- **Quadrant form of the bonus**: `bonus(g) = ∬_{s,t>0} ω(s+t) g(s) g(t)` for continuous even
`g ≥ 0`. -/
theorem crossSignBonus_eq_quadrant {g : ℝ → ℝ} (hg : Continuous g) (hg0 : ∀ u, 0 ≤ g u)
    (heven : ∀ u, g (-u) = g u) :
    crossSignBonus g = ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ),
      archLevyDensity (q.1 + q.2) * (g q.1 * g q.2) ∂((volume : Measure ℝ).prod volume) := by
  unfold crossSignBonus
  rw [crossSignBonusL_eq_planar hg hg0, lintegral_bonusPlanar_eq_quadrant hg heven,
    integral_eq_lintegral_of_nonneg_ae]
  · exact ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi) fun q hq =>
      mul_nonneg (archLevyDensity_pos (by linarith [mem_Ioi.mp hq.1, mem_Ioi.mp hq.2])).le
        (mul_nonneg (hg0 _) (hg0 _))
  · exact ((measurable_archLevyDensity.comp (measurable_fst.add measurable_snd)).mul
      ((hg.comp continuous_fst).mul (hg.comp continuous_snd)).measurable).aestronglyMeasurable

/-! ## The Doob gauge: one-signed odd tests -/

theorem phiDoobTest_nonneg_of_nonneg {v : ℝ → ℝ} (hpos : ∀ u, 0 ≤ u → 0 ≤ v u) (u : ℝ)
    (hu : 0 ≤ u) : 0 ≤ phiDoobTest v u :=
  mul_nonneg (riemannKernelReal_pos u).le (hpos u hu)

theorem phiDoobTest_nonpos_of_odd {v : ℝ → ℝ} (hodd : ∀ x, v (-x) = -v x)
    (hpos : ∀ u, 0 ≤ u → 0 ≤ v u) (u : ℝ) (hu : u ≤ 0) : phiDoobTest v u ≤ 0 := by
  have h : v u ≤ 0 := by
    have := hpos (-u) (by linarith)
    rw [hodd] at this
    linarith
  exact mul_nonpos_iff.mpr (Or.inl ⟨(riemannKernelReal_pos u).le, h⟩)

theorem phiDoobTest_abs_even {v : ℝ → ℝ} (hodd : ∀ x, v (-x) = -v x) (u : ℝ) :
    phiDoobTest (fun y => |v y|) (-u) = phiDoobTest (fun y => |v y|) u := by
  show riemannKernelReal (-u) * |v (-u)| = riemannKernelReal u * |v u|
  rw [WeilExcess.riemannKernelReal_neg, hodd, abs_neg]

/-- **Cross-sign bonus identity in the Doob gauge**: for odd `v ≥ 0` on `[0,∞)`,
`Λ_∞(Θv) = Λ_∞(Θ|v|) + 4·bonus(Θ|v|)`. -/
theorem levy_phiDoob_eq_abs_add_bonus (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v) (hvc : HasCompactSupport v)
    (hodd : ∀ x, v (-x) = -v x) (hpos : ∀ u, 0 ≤ u → 0 ≤ v u) :
    weilLevyForm (phiDoobTest v) =
      weilLevyForm (phiDoobTest fun y => |v y|) + 4 * crossSignBonus (phiDoobTest fun y => |v y|) := by
  have h := weilLevyForm_eq_abs_add_bonus (contDiff_phiDoobTest hv) (hasCompactSupport_phiDoobTest hvc)
    (phiDoobTest_nonneg_of_nonneg hpos) (phiDoobTest_nonpos_of_odd hodd hpos)
  have e : (fun u => |phiDoobTest v u|) = phiDoobTest fun y => |v y| := funext (abs_phiDoobTest v)
  rw [e] at h
  exact h

/-- **Prime-free lower bound with bonus.** On the one-signed odd cone with support in
`(−log 2, log 2)`, the arithmetic Doob energy dominates `Λ_∞(Θ|v|) + 4·bonus(Θ|v|)`. -/
theorem levy_abs_add_bonus_le_sourceEnergy_of_odd_oneSigned (v : ℝ → ℝ) (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) (hodd : ∀ x, v (-x) = -v x) (hpos : ∀ x, 0 ≤ x → 0 ≤ v x)
    {L : ℝ} (hsupp : ∀ x ∉ Ioo (-(L / 2)) (L / 2), v x = 0) (hL : L ≤ 2 * Real.log 2) :
    weilLevyForm (phiDoobTest fun y => |v y|) + 4 * crossSignBonus (phiDoobTest fun y => |v y|) ≤
      sourceEnergy (compactLift v hv hvc) := by
  rw [← levy_phiDoob_eq_abs_add_bonus v hv hvc hodd hpos]
  exact levy_le_sourceEnergy_of_odd_oneSigned v hv hvc hodd hpos hsupp hL

/-- The bonus of `Θ|v|` in quadrant form. -/
theorem crossSignBonus_phiDoob_eq_quadrant (v : ℝ → ℝ) (hv : Continuous v)
    (hodd : ∀ x, v (-x) = -v x) :
    crossSignBonus (phiDoobTest fun y => |v y|) =
      ∫ q in Ioi (0 : ℝ) ×ˢ Ioi (0 : ℝ), archLevyDensity (q.1 + q.2) *
        (phiDoobTest (fun y => |v y|) q.1 * phiDoobTest (fun y => |v y|) q.2)
          ∂((volume : Measure ℝ).prod volume) :=
  crossSignBonus_eq_quadrant (continuous_riemannKernelReal.mul hv.abs)
    (fun u => mul_nonneg (riemannKernelReal_pos u).le (abs_nonneg _))
    (phiDoobTest_abs_even hodd)

end RHTower.CHMDPolar
