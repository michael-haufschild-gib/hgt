import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateTwoSidedRepresentation

/-!
# Fold domination for monotone profiles

For `u` even, nonnegative and nonincreasing on `[0, ∞)`, the reflected variation is dominated by a
same-side variation with the weight `m_a(t−x)` in place of `m_a(x+t)`: on `0 < x < t/2` one has
`x ≤ t − x ≤ x + t`, hence `0 ≤ u(x) − u(t−x) ≤ u(x) − u(x+t)`, and by the symmetry of the collar

    D_a(t) = 2∫_0^{t/2} m_a(x) m_a(t−x) (u(x) − u(t−x))² ≤ 2∫_0^{t/2} m_a(x) m_a(t−x) (u(x) − u(x+t))².

Writing `m_a(t−x) = m_a(x+t) + (m_a(t−x) − m_a(x+t))` and using `0 ≤ u(x) − u(x+t) ≤ u(x)`,

    D_a(t) ≤ 2 S_a(t) + 2 E_a(t),     E_a(t) = ∫_0^{t/2} m_a(x) (m_a(t−x) − m_a(x+t))⁺ u(x)² dx.

Integrating against the jump measure and exchanging the integrations, with the **fold excess weight**
`W_a(x) = ∫_{t>2x} dm(t) (m_a(t−x) − m_a(x+t))⁺`,

    markovEnergy(Φ(ω_a u)) ≥ 4 sinh(a/2) ∫_{x>0} u² m_a sinh(x/2) − 2 ∫_{x>0} u(x)² m_a(x) W_a(x) dx.

Hence Markov positivity on `Φ(ω_a u)` for every such `u` follows from the pointwise weight inequality
`W_a(x) ≤ 2 sinh(a/2) sinh(x/2)` on `(0, ∞)`, a statement about Riemann's kernel alone. The weight
vanishes on the window `x + t ≤ a`, because `m_a` is increasing on `[0, a]`: the fold excess comes
only from shifts beyond the peak of `m_a`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The fold excess density, jump, shift and weight -/

/-- `(m_a(t−x) − m_a(x+t))⁺` on `2x < t`, else `0`. -/
def foldExcessDensity (a t x : ℝ) : ℝ :=
  if 2 * x < t then max (shiftDifference a (t - x) - shiftDifference a (x + t)) 0 else 0

/-- `m_a(x) · foldExcessDensity · u(x)²`. -/
def foldExcessJump (a : ℝ) (u : ℝ → ℝ) (t x : ℝ) : ℝ :=
  shiftDifference a x * foldExcessDensity a t x * u x ^ 2

/-- `E_a(t) = ∫_{x>0} foldExcessJump a u t x dx = ∫_0^{t/2} m_a(x)(m_a(t−x) − m_a(x+t))⁺ u(x)² dx`. -/
def foldExcessShift (a : ℝ) (u : ℝ → ℝ) (t : ℝ) : ℝ :=
  ∫ x in Ioi (0 : ℝ), foldExcessJump a u t x

/-- The fold excess weight `W_a(x) = ∫ dm(t) foldExcessDensity a t x`. -/
def foldExcessWeight (a x : ℝ) : ℝ :=
  (∫ t in Ioi (0 : ℝ), archLevyDensity t * foldExcessDensity a t x) +
    ∑' n : ℕ, vonMangoldtAtom n * foldExcessDensity a (Real.log n) x

theorem foldExcessDensity_nonneg (a t x : ℝ) : 0 ≤ foldExcessDensity a t x := by
  unfold foldExcessDensity
  split_ifs
  · exact le_max_right _ _
  · exact le_rfl

theorem foldExcessDensity_le_max {a t x : ℝ} (ha : 0 ≤ a) (ht : 0 ≤ t) (hx : 0 ≤ x) :
    foldExcessDensity a t x ≤ max (shiftDifference a (t - x)) 0 := by
  unfold foldExcessDensity
  split_ifs
  · exact max_le_max (sub_le_self _ (shiftDifference_nonneg_of_nonneg ha (add_nonneg hx ht))) le_rfl
  · exact le_max_right _ _

theorem foldExcessDensity_of_lt {a t x : ℝ} (h : 2 * x < t) :
    foldExcessDensity a t x = max (shiftDifference a (t - x) - shiftDifference a (x + t)) 0 := by
  unfold foldExcessDensity
  rw [if_pos h]

theorem foldExcessDensity_of_le {a t x : ℝ} (h : t ≤ 2 * x) : foldExcessDensity a t x = 0 := by
  unfold foldExcessDensity
  rw [if_neg (not_lt.mpr h)]

theorem measurable_foldExcessDensity_uncurry (a : ℝ) :
    Measurable fun p : ℝ × ℝ => foldExcessDensity a p.1 p.2 := by
  unfold foldExcessDensity
  refine Measurable.ite (measurableSet_lt (measurable_const.mul measurable_snd) measurable_fst)
    ?_ measurable_const
  exact ((((continuous_shiftDifference a).comp (continuous_fst.sub continuous_snd)).sub
    ((continuous_shiftDifference a).comp (continuous_snd.add continuous_fst))).max
    continuous_const).measurable

theorem measurable_foldExcessDensity (a t : ℝ) : Measurable (foldExcessDensity a t) :=
  (measurable_foldExcessDensity_uncurry a).comp (measurable_const.prodMk measurable_id)

theorem foldExcessJump_nonneg {a : ℝ} (ha : 0 ≤ a) (u : ℝ → ℝ) (t : ℝ) {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ foldExcessJump a u t x :=
  mul_nonneg (mul_nonneg (shiftDifference_nonneg_of_nonneg ha hx) (foldExcessDensity_nonneg a t x))
    (sq_nonneg _)

theorem foldExcessJump_le_collar {a : ℝ} (ha : 0 ≤ a) (u : ℝ → ℝ) {t x : ℝ} (ht : 0 ≤ t)
    (hx : 0 ≤ x) :
    foldExcessJump a u t x ≤ shiftDifference a x * max (shiftDifference a (t - x)) 0 * u x ^ 2 := by
  unfold foldExcessJump
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (foldExcessDensity_le_max ha ht hx)
      (shiftDifference_nonneg_of_nonneg ha hx)) (sq_nonneg _)

theorem measurable_foldExcessJump (a : ℝ) {u : ℝ → ℝ} (hu : Continuous u) (t : ℝ) :
    Measurable (foldExcessJump a u t) := by
  unfold foldExcessJump
  exact ((continuous_shiftDifference a).measurable.mul (measurable_foldExcessDensity a t)).mul
    (hu.pow 2).measurable

theorem integrableOn_foldExcessJump {a : ℝ} (ha : 0 ≤ a) {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) {t : ℝ} (ht : 0 ≤ t) :
    IntegrableOn (foldExcessJump a u t) (Ioi 0) := by
  refine (integrable_atom_collar_term (a := a) hu huc t).mono'
    (measurable_foldExcessJump a hu t).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
  rw [Real.norm_eq_abs, abs_of_nonneg (foldExcessJump_nonneg ha u t (mem_Ioi.mp hx).le)]
  exact foldExcessJump_le_collar ha u ht (mem_Ioi.mp hx).le

theorem foldExcessShift_nonneg {a : ℝ} (ha : 0 ≤ a) (u : ℝ → ℝ) (t : ℝ) :
    0 ≤ foldExcessShift a u t :=
  setIntegral_nonneg measurableSet_Ioi fun _ hx => foldExcessJump_nonneg ha u t (mem_Ioi.mp hx).le

/-- The fold excess shift is bounded by the collar integral. -/
theorem foldExcessShift_le_collar {a : ℝ} (ha : 0 ≤ a) {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) {t : ℝ} (ht : 0 ≤ t) :
    foldExcessShift a u t ≤
      ∫ x in Ioo (0 : ℝ) t, shiftDifference a x * shiftDifference a (t - x) * u x ^ 2 := by
  rw [integral_Ioo_collar_eq_integral_Ioi_max ha]
  exact setIntegral_mono_on (integrableOn_foldExcessJump ha hu huc ht)
    (integrable_atom_collar_term hu huc t) measurableSet_Ioi
    fun x hx => foldExcessJump_le_collar ha u ht (mem_Ioi.mp hx).le

/-! ### Monotone fold domination of one shift -/

/-- Monotone profiles: on `0 < x < t/2` the fold difference is dominated by the shift difference. -/
theorem sq_fold_sub_le_sq_shift_sub {u : ℝ → ℝ} (hanti : AntitoneOn u (Ici 0)) {t x : ℝ}
    (hx : 0 < x) (hxt : x < t / 2) :
    (u x - u (t - x)) ^ 2 ≤ (u x - u (x + t)) ^ 2 := by
  have h1 : u (t - x) ≤ u x :=
    hanti (mem_Ici.mpr hx.le) (mem_Ici.mpr (by linarith)) (by linarith)
  have h2 : u (x + t) ≤ u (t - x) :=
    hanti (mem_Ici.mpr (by linarith)) (mem_Ici.mpr (by linarith)) (by linarith)
  exact pow_le_pow_left₀ (by linarith) (by linarith) 2

/-- The collar integral of a function symmetric under `x ↦ t − x` is twice its half-collar integral. -/
theorem integral_Ioo_eq_two_mul_half_of_symmetric {f : ℝ → ℝ} (hf : Continuous f) {t : ℝ}
    (ht : 0 ≤ t) (hsymm : ∀ x, f (t - x) = f x) :
    (∫ x in Ioo (0 : ℝ) t, f x) = 2 * ∫ x in Ioo (0 : ℝ) (t / 2), f x := by
  have hi1 : IntegrableOn f (Ioc (0 : ℝ) (t / 2)) :=
    hf.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hi2 : IntegrableOn f (Ioc (t / 2) t) :=
    hf.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self
  have hunion : Ioc (0 : ℝ) (t / 2) ∪ Ioc (t / 2) t = Ioc (0 : ℝ) t :=
    Ioc_union_Ioc_eq_Ioc (by linarith) (by linarith)
  have hdisj : Disjoint (Ioc (0 : ℝ) (t / 2)) (Ioc (t / 2) t) := Ioc_disjoint_Ioc_of_le le_rfl
  rw [← integral_Ioc_eq_integral_Ioo, ← hunion, setIntegral_union hdisj measurableSet_Ioc hi1 hi2,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo,
    RHTower.setIntegral_Ioo_reflect_midpoint f t,
    setIntegral_congr_fun measurableSet_Ioo fun x _ => hsymm x]
  ring

theorem hasCompactSupport_shift_sub_sq {u : ℝ → ℝ} (huc : HasCompactSupport u) (t : ℝ) :
    HasCompactSupport fun x => (u x - u (x + t)) ^ 2 :=
  hasCompactSupport_sq (huc.sub (hasCompactSupport_shift huc t))

theorem integrableOn_sameSideGroundJump_shiftedGroundState (a : ℝ) {u : ℝ → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u) (t : ℝ) (s : Set ℝ) :
    IntegrableOn (fun x => sameSideGroundJump (shiftedGroundState a) u t x) s := by
  have hωc : Continuous (shiftedGroundState a) := (contDiff_shiftedGroundState a).continuous
  have hΘ := continuous_riemannKernelReal
  have hg : Continuous fun x => riemannKernelReal x * riemannKernelReal (x + t) *
      shiftedGroundState a x * shiftedGroundState a (x + t) :=
    ((hΘ.mul (hΘ.comp (continuous_id.add continuous_const))).mul hωc).mul
      (hωc.comp (continuous_id.add continuous_const))
  have hsq : Continuous fun x => (u x - u (x + t)) ^ 2 :=
    (hu.sub (hu.comp (continuous_id.add continuous_const))).pow 2
  have hcs : HasCompactSupport fun x => (riemannKernelReal x * riemannKernelReal (x + t) *
      shiftedGroundState a x * shiftedGroundState a (x + t)) * (u x - u (x + t)) ^ 2 :=
    (hasCompactSupport_shift_sub_sq huc t).mul_left
  exact ((hg.mul hsq).integrable_of_hasCompactSupport hcs).integrableOn

/-- **Fold domination of one shift.** For `u` nonnegative and nonincreasing on `[0, ∞)` and `t > 0`,

    ∫_0^t reflectedDifferenceJump ≤ 2 ∫_{x>0} sameSideGroundJump + 2 E_a(t). -/
theorem integral_reflectedDifference_le_two_sameSide_add_two_foldExcess {a : ℝ} (ha : 0 < a)
    {u : ℝ → ℝ} (hu : Continuous u) (huc : HasCompactSupport u) (hnn : ∀ x, 0 ≤ u x)
    (hanti : AntitoneOn u (Ici 0)) {t : ℝ} (ht : 0 < t) :
    (∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x) ≤
      2 * (∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x) +
        2 * foldExcessShift a u t := by
  have hpos : ∀ x, 0 < x → 0 ≤ shiftedGroundState a x := fun x hx =>
    (shiftedGroundState_pos ha hx).le
  have hm := continuous_shiftDifference a
  have hf : Continuous fun x => shiftDifference a x * shiftDifference a (t - x) *
      (u x - u (t - x)) ^ 2 :=
    (hm.mul (hm.comp (continuous_const.sub continuous_id))).mul
      ((hu.sub (hu.comp (continuous_const.sub continuous_id))).pow 2)
  have hD : (∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x) =
      ∫ x in Ioo (0 : ℝ) t, shiftDifference a x * shiftDifference a (t - x) * (u x - u (t - x)) ^ 2 :=
    setIntegral_congr_fun measurableSet_Ioo fun x _ =>
      reflectedDifferenceJump_shiftedGroundState a u t x
  have hsymm : ∀ x, shiftDifference a (t - x) * shiftDifference a (t - (t - x)) *
      (u (t - x) - u (t - (t - x))) ^ 2 =
      shiftDifference a x * shiftDifference a (t - x) * (u x - u (t - x)) ^ 2 := by
    intro x
    rw [sub_sub_cancel]
    ring
  have hhalf := integral_Ioo_eq_two_mul_half_of_symmetric hf ht.le hsymm
  -- pointwise domination on the half collar
  have hpt : ∀ x ∈ Ioo (0 : ℝ) (t / 2),
      shiftDifference a x * shiftDifference a (t - x) * (u x - u (t - x)) ^ 2 ≤
        sameSideGroundJump (shiftedGroundState a) u t x + foldExcessJump a u t x := by
    intro x hx
    obtain ⟨hx0, hxt⟩ := hx
    have hsq := sq_fold_sub_le_sq_shift_sub hanti hx0 hxt
    have hsq2 : (u x - u (x + t)) ^ 2 ≤ u x ^ 2 := by
      have h1 : u (x + t) ≤ u x :=
        hanti (mem_Ici.mpr hx0.le) (mem_Ici.mpr (by linarith)) (by linarith)
      exact pow_le_pow_left₀ (by linarith) (by linarith [hnn (x + t)]) 2
    have hm0 := shiftDifference_nonneg_of_nonneg ha.le hx0.le
    have hmt := shiftDifference_nonneg_of_nonneg ha.le (show 0 ≤ t - x by linarith)
    rw [sameSideGroundJump_shiftedGroundState]
    unfold foldExcessJump
    rw [foldExcessDensity_of_lt (by linarith)]
    have hA : shiftDifference a x * shiftDifference a (t - x) * (u x - u (t - x)) ^ 2 ≤
        shiftDifference a x * shiftDifference a (t - x) * (u x - u (x + t)) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (mul_nonneg hm0 hmt)
    have hB : shiftDifference a x * (shiftDifference a (t - x) - shiftDifference a (x + t)) *
        (u x - u (x + t)) ^ 2 ≤
        shiftDifference a x * max (shiftDifference a (t - x) - shiftDifference a (x + t)) 0 *
          u x ^ 2 := by
      calc shiftDifference a x * (shiftDifference a (t - x) - shiftDifference a (x + t)) *
            (u x - u (x + t)) ^ 2
          ≤ shiftDifference a x * max (shiftDifference a (t - x) - shiftDifference a (x + t)) 0 *
            (u x - u (x + t)) ^ 2 :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (le_max_left _ _) hm0) (sq_nonneg _)
        _ ≤ _ := mul_le_mul_of_nonneg_left hsq2 (mul_nonneg hm0 (le_max_right _ _))
    calc shiftDifference a x * shiftDifference a (t - x) * (u x - u (t - x)) ^ 2
        ≤ shiftDifference a x * shiftDifference a (t - x) * (u x - u (x + t)) ^ 2 := hA
      _ = shiftDifference a x * shiftDifference a (x + t) * (u x - u (x + t)) ^ 2 +
          shiftDifference a x * (shiftDifference a (t - x) - shiftDifference a (x + t)) *
            (u x - u (x + t)) ^ 2 := by ring
      _ ≤ _ := add_le_add le_rfl hB
  have hiF : IntegrableOn (fun x => shiftDifference a x * shiftDifference a (t - x) *
      (u x - u (t - x)) ^ 2) (Ioo (0 : ℝ) (t / 2)) :=
    hf.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hiS := integrableOn_sameSideGroundJump_shiftedGroundState a hu huc t (Ioi 0)
  have hiSS : IntegrableOn (fun x => sameSideGroundJump (shiftedGroundState a) u t x)
      (Ioo (0 : ℝ) (t / 2)) := hiS.mono_set Ioo_subset_Ioi_self
  have hiE := integrableOn_foldExcessJump ha.le hu huc ht.le
  have hiEE : IntegrableOn (foldExcessJump a u t) (Ioo (0 : ℝ) (t / 2)) :=
    hiE.mono_set Ioo_subset_Ioi_self
  have hSmono : (∫ x in Ioo (0 : ℝ) (t / 2), sameSideGroundJump (shiftedGroundState a) u t x) ≤
      ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x :=
    setIntegral_mono_set hiS
      (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx =>
        sameSideGroundJump_nonneg hpos ht.le (mem_Ioi.mp hx))
      (LE.le.eventuallyLE Ioo_subset_Ioi_self)
  have hEmono : (∫ x in Ioo (0 : ℝ) (t / 2), foldExcessJump a u t x) ≤ foldExcessShift a u t :=
    setIntegral_mono_set hiE
      (ae_restrict_of_forall_mem measurableSet_Ioi fun x hx =>
        foldExcessJump_nonneg ha.le u t (mem_Ioi.mp hx).le)
      (LE.le.eventuallyLE Ioo_subset_Ioi_self)
  have hhalf_le : (∫ x in Ioo (0 : ℝ) (t / 2),
      shiftDifference a x * shiftDifference a (t - x) * (u x - u (t - x)) ^ 2) ≤
      (∫ x in Ioo (0 : ℝ) (t / 2), sameSideGroundJump (shiftedGroundState a) u t x) +
        ∫ x in Ioo (0 : ℝ) (t / 2), foldExcessJump a u t x := by
    rw [← integral_add hiSS hiEE]
    exact setIntegral_mono_on hiF (hiSS.add hiEE) measurableSet_Ioo hpt
  rw [hD, hhalf]
  linarith

/-! ### Integrability, summability and Fubini for the fold excess -/

theorem integrable_archLevy_foldExcess_prod {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) :
    Integrable (Function.uncurry fun t x => archLevyDensity t * foldExcessJump a u t x)
      ((volume.restrict (Ioi (0 : ℝ))).prod (volume.restrict (Ioi (0 : ℝ)))) := by
  refine (integrable_archLevy_collar_prod ha hu huc).mono' ?_ ?_
  · have hmeas : Measurable fun z : ℝ × ℝ => archLevyDensity z.1 * foldExcessJump a u z.1 z.2 := by
      unfold foldExcessJump
      exact (measurable_archLevyDensity.comp measurable_fst).mul
        ((((continuous_shiftDifference a).comp continuous_snd).measurable.mul
          (measurable_foldExcessDensity_uncurry a)).mul ((hu.comp continuous_snd).pow 2).measurable)
    exact hmeas.aestronglyMeasurable
  · rw [Measure.prod_restrict]
    refine ae_restrict_of_forall_mem (measurableSet_Ioi.prod measurableSet_Ioi) fun z hz => ?_
    have ht : 0 < z.1 := hz.1
    have hx : 0 < z.2 := hz.2
    have hL := archLevyDensity_pos ht
    show ‖archLevyDensity z.1 * foldExcessJump a u z.1 z.2‖ ≤
      archLevyDensity z.1 * (shiftDifference a z.2 * max (shiftDifference a (z.1 - z.2)) 0 * u z.2 ^ 2)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hL,
      abs_of_nonneg (foldExcessJump_nonneg ha.le u z.1 hx.le)]
    exact mul_le_mul_of_nonneg_left (foldExcessJump_le_collar ha.le u ht.le hx.le) hL.le

theorem integrableOn_archLevy_mul_foldExcessShift {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u) :
    IntegrableOn (fun t => archLevyDensity t * foldExcessShift a u t) (Ioi 0) := by
  have h := (integrable_archLevy_foldExcess_prod ha hu huc).integral_prod_left
  refine h.congr (Eventually.of_forall fun t => ?_)
  show (∫ x in Ioi (0 : ℝ), archLevyDensity t * foldExcessJump a u t x) =
    archLevyDensity t * foldExcessShift a u t
  unfold foldExcessShift
  rw [integral_const_mul]

theorem summable_atom_mul_foldExcessShift {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) :
    Summable fun n : ℕ => vonMangoldtAtom n * foldExcessShift a u (Real.log n) :=
  (summable_atom_mul_collarIntegral ha hu huc).of_nonneg_of_le
    (fun n => mul_nonneg (vonMangoldtAtom_nonneg n) (foldExcessShift_nonneg ha.le u _))
    (fun n => mul_le_mul_of_nonneg_left
      (foldExcessShift_le_collar ha.le hu huc (Real.log_natCast_nonneg n)) (vonMangoldtAtom_nonneg n))

/-- Fubini for the archimedean fold excess. -/
theorem integral_archLevy_foldExcessShift_eq {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) :
    (∫ t in Ioi (0 : ℝ), archLevyDensity t * foldExcessShift a u t) =
      ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x *
        ∫ t in Ioi (0 : ℝ), archLevyDensity t * foldExcessDensity a t x := by
  have hswap := integral_integral_swap (integrable_archLevy_foldExcess_prod ha hu huc)
  calc (∫ t in Ioi (0 : ℝ), archLevyDensity t * foldExcessShift a u t)
      = ∫ t in Ioi (0 : ℝ), ∫ x in Ioi (0 : ℝ), archLevyDensity t * foldExcessJump a u t x := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        unfold foldExcessShift
        rw [integral_const_mul]
    _ = ∫ x in Ioi (0 : ℝ), ∫ t in Ioi (0 : ℝ), archLevyDensity t * foldExcessJump a u t x := hswap
    _ = _ := by
        refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
        rw [← integral_const_mul]
        refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
        unfold foldExcessJump
        ring

theorem integrableOn_sq_mul_shiftDifference_mul_archFoldWeight {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u) :
    IntegrableOn (fun x => u x ^ 2 * shiftDifference a x *
      ∫ t in Ioi (0 : ℝ), archLevyDensity t * foldExcessDensity a t x) (Ioi 0) := by
  have h := (integrable_archLevy_foldExcess_prod ha hu huc).integral_prod_right
  refine h.congr (Eventually.of_forall fun x => ?_)
  show (∫ t in Ioi (0 : ℝ), archLevyDensity t * foldExcessJump a u t x) =
    u x ^ 2 * shiftDifference a x * ∫ t in Ioi (0 : ℝ), archLevyDensity t * foldExcessDensity a t x
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
  unfold foldExcessJump
  ring

theorem summable_integral_norm_atom_foldExcess {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) :
    Summable fun n : ℕ => ∫ x in Ioi (0 : ℝ), ‖vonMangoldtAtom n * foldExcessJump a u (Real.log n) x‖ := by
  refine (summable_integral_norm_atom_collar ha hu huc).of_nonneg_of_le
    (fun n => integral_nonneg fun x => norm_nonneg _) fun n => ?_
  refine integral_mono_of_nonneg (Eventually.of_forall fun x => norm_nonneg _)
    ((integrable_atom_collar_term hu huc (Real.log n)).const_mul _).norm ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
  have hΛ := vonMangoldtAtom_nonneg n
  have hx0 := (mem_Ioi.mp hx).le
  show ‖vonMangoldtAtom n * foldExcessJump a u (Real.log n) x‖ ≤
    ‖vonMangoldtAtom n * (shiftDifference a x * max (shiftDifference a (Real.log n - x)) 0 * u x ^ 2)‖
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hΛ,
    abs_of_nonneg (foldExcessJump_nonneg ha.le u _ hx0),
    abs_of_nonneg (mul_nonneg (mul_nonneg (shiftDifference_nonneg_of_nonneg ha.le hx0)
      (le_max_right _ _)) (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_left
    (foldExcessJump_le_collar ha.le u (Real.log_natCast_nonneg n) hx0) hΛ

/-- Fubini for the prime fold excess. -/
theorem tsum_atom_foldExcessShift_eq {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : Continuous u)
    (huc : HasCompactSupport u) :
    (∑' n : ℕ, vonMangoldtAtom n * foldExcessShift a u (Real.log n)) =
      ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x *
        ∑' n : ℕ, vonMangoldtAtom n * foldExcessDensity a (Real.log n) x := by
  have h1 : ∀ n : ℕ, vonMangoldtAtom n * foldExcessShift a u (Real.log n) =
      ∫ x in Ioi (0 : ℝ), vonMangoldtAtom n * foldExcessJump a u (Real.log n) x := by
    intro n
    unfold foldExcessShift
    rw [integral_const_mul]
  rw [tsum_congr h1, integral_tsum_of_summable_integral_norm
    (F := fun n : ℕ => fun x => vonMangoldtAtom n * foldExcessJump a u (Real.log n) x)
    (fun n => (integrableOn_foldExcessJump ha.le hu huc (Real.log_natCast_nonneg n)).const_mul _)
    (summable_integral_norm_atom_foldExcess ha hu huc)]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  rw [← tsum_mul_left]
  refine tsum_congr fun n => ?_
  unfold foldExcessJump
  ring

theorem summable_atom_mul_foldExcessDensity {a : ℝ} (ha : 0 ≤ a) {x : ℝ} (hx : 0 ≤ x) :
    Summable fun n : ℕ => vonMangoldtAtom n * foldExcessDensity a (Real.log n) x :=
  (summable_atom_max_shiftDifference a x).of_nonneg_of_le
    (fun n => mul_nonneg (vonMangoldtAtom_nonneg n) (foldExcessDensity_nonneg a _ x))
    (fun n => mul_le_mul_of_nonneg_left
      (foldExcessDensity_le_max ha (Real.log_natCast_nonneg n) hx) (vonMangoldtAtom_nonneg n))

theorem integrableOn_sq_mul_shiftDifference_mul_primeFoldWeight {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u) :
    IntegrableOn (fun x => u x ^ 2 * shiftDifference a x *
      ∑' n : ℕ, vonMangoldtAtom n * foldExcessDensity a (Real.log n) x) (Ioi 0) := by
  refine (integrableOn_sq_mul_shiftDifference_mul_primeCollar ha hu huc).mono' ?_ ?_
  · refine aestronglyMeasurable_of_tendsto_ae (f := fun N x => u x ^ 2 * shiftDifference a x *
      ∑ n ∈ Finset.range N, vonMangoldtAtom n * foldExcessDensity a (Real.log n) x)
      atTop (fun N => ?_) ?_
    · refine Measurable.aestronglyMeasurable (((hu.pow 2).mul (continuous_shiftDifference a)).measurable.mul ?_)
      exact Finset.measurable_sum _ fun n _ => measurable_const.mul (measurable_foldExcessDensity a _)
    · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
      exact ((summable_atom_mul_foldExcessDensity ha.le (mem_Ioi.mp hx).le).hasSum.tendsto_sum_nat).const_mul _
  · refine ae_restrict_of_forall_mem measurableSet_Ioi fun x hx => ?_
    have hx0 := (mem_Ioi.mp hx).le
    have hm0 := shiftDifference_nonneg_of_nonneg ha.le hx0
    have hS := summable_atom_mul_foldExcessDensity ha.le hx0
    have hC := summable_atom_max_shiftDifference a x
    have hle : (∑' n : ℕ, vonMangoldtAtom n * foldExcessDensity a (Real.log n) x) ≤
        ∑' n : ℕ, vonMangoldtAtom n * max (shiftDifference a (Real.log n - x)) 0 :=
      Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left
        (foldExcessDensity_le_max ha.le (Real.log_natCast_nonneg n) hx0) (vonMangoldtAtom_nonneg n))
        hS hC
    have h0 : 0 ≤ ∑' n : ℕ, vonMangoldtAtom n * foldExcessDensity a (Real.log n) x :=
      tsum_nonneg fun n => mul_nonneg (vonMangoldtAtom_nonneg n) (foldExcessDensity_nonneg a _ x)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mul_nonneg (sq_nonneg _) hm0), abs_of_nonneg h0]
    exact mul_le_mul_of_nonneg_left hle (mul_nonneg (sq_nonneg _) hm0)

/-- `u² m_a W_a` is integrable on the half line. -/
theorem integrableOn_sq_mul_shiftDifference_mul_foldExcessWeight {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : Continuous u) (huc : HasCompactSupport u) :
    IntegrableOn (fun x => u x ^ 2 * shiftDifference a x * foldExcessWeight a x) (Ioi 0) := by
  have h := (integrableOn_sq_mul_shiftDifference_mul_archFoldWeight ha hu huc).add
    (integrableOn_sq_mul_shiftDifference_mul_primeFoldWeight ha hu huc)
  refine h.congr_fun (fun x _ => ?_) measurableSet_Ioi
  unfold foldExcessWeight
  simp only [Pi.add_apply]
  ring

/-- **Fold excess Fubini.** `∫ dm(t) E_a(t) = ∫_{x>0} u² m_a W_a`. -/
theorem integral_dm_foldExcessShift_eq_integral_sq_mul_foldExcessWeight {a : ℝ} (ha : 0 < a)
    {u : ℝ → ℝ} (hu : Continuous u) (huc : HasCompactSupport u) :
    (∫ t in Ioi (0 : ℝ), archLevyDensity t * foldExcessShift a u t) +
      (∑' n : ℕ, vonMangoldtAtom n * foldExcessShift a u (Real.log n)) =
      ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * foldExcessWeight a x := by
  rw [integral_archLevy_foldExcessShift_eq ha hu huc, tsum_atom_foldExcessShift_eq ha hu huc,
    ← integral_add (integrableOn_sq_mul_shiftDifference_mul_archFoldWeight ha hu huc)
      (integrableOn_sq_mul_shiftDifference_mul_primeFoldWeight ha hu huc)]
  refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
  unfold foldExcessWeight
  ring

/-! ### Fold domination of the energies and the weight criterion -/

/-- **Fold domination.** For `u ∈ C¹_c` even, nonnegative and nonincreasing on `[0, ∞)`,
`D_a(u) ≤ 2 S_a(u) + 2 ∫_{x>0} u² m_a W_a`. -/
theorem reflectedDifferenceEnergy_le_of_antitone {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) (hnn : ∀ x, 0 ≤ u x)
    (hanti : AntitoneOn u (Ici 0)) :
    reflectedDifferenceEnergy (shiftedGroundState a) u ≤
      2 * sameSideEnergy (shiftedGroundState a) u +
        2 * ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * foldExcessWeight a x := by
  have hωc : Continuous (shiftedGroundState a) := (contDiff_shiftedGroundState a).continuous
  have hpos : ∀ x, 0 < x → 0 ≤ shiftedGroundState a x := fun x hx =>
    (shiftedGroundState_pos ha hx).le
  have hadm := foldedAdmissible_shiftedGroundState ha hu huc
  have hDint := integrableOn_archLevy_mul_reflectedDifferenceIntegral ha hu huc
  have hSint := integrableOn_archLevy_mul_sameSideIntegral hωc hu.continuous hpos hadm
  have hEint := integrableOn_archLevy_mul_foldExcessShift ha hu.continuous huc
  have hDsum := summable_atom_mul_reflectedDifferenceIntegral ha hu huc
  have hSsum := summable_atom_mul_sameSideIntegral hpos hadm
  have hEsum := summable_atom_mul_foldExcessShift ha hu.continuous huc
  have hpt := fun {t : ℝ} (ht : 0 < t) =>
    integral_reflectedDifference_le_two_sameSide_add_two_foldExcess ha hu.continuous huc hnn hanti ht
  have harch : (∫ t in Ioi (0 : ℝ), archLevyDensity t *
        ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x) ≤
      2 * (∫ t in Ioi (0 : ℝ), archLevyDensity t *
        ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x) +
        2 * ∫ t in Ioi (0 : ℝ), archLevyDensity t * foldExcessShift a u t := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hSint.const_mul 2) (hEint.const_mul 2)]
    refine setIntegral_mono_on hDint ((hSint.const_mul 2).add (hEint.const_mul 2)) measurableSet_Ioi
      fun t ht => ?_
    have hL := (archLevyDensity_pos (mem_Ioi.mp ht)).le
    have h := hpt (mem_Ioi.mp ht)
    calc archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x
        ≤ archLevyDensity t *
          (2 * (∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u t x) +
            2 * foldExcessShift a u t) := mul_le_mul_of_nonneg_left h hL
      _ = _ := by ring
  have hprime : (∑' n : ℕ, vonMangoldtAtom n *
        ∫ x in Ioo (0 : ℝ) (Real.log n),
          reflectedDifferenceJump (shiftedGroundState a) u (Real.log n) x) ≤
      2 * (∑' n : ℕ, vonMangoldtAtom n *
        ∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u (Real.log n) x) +
        2 * ∑' n : ℕ, vonMangoldtAtom n * foldExcessShift a u (Real.log n) := by
    rw [← tsum_mul_left, ← tsum_mul_left, ← (hSsum.mul_left 2).tsum_add (hEsum.mul_left 2)]
    refine Summable.tsum_le_tsum (fun n => ?_) hDsum ((hSsum.mul_left 2).add (hEsum.mul_left 2))
    have hΛ := vonMangoldtAtom_nonneg n
    rcases lt_or_ge n 2 with hn | hn
    · rw [vonMangoldtAtom_eq_zero_of_lt_two hn]
      simp
    · have h1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
      have h := hpt (Real.log_pos h1)
      calc vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n),
            reflectedDifferenceJump (shiftedGroundState a) u (Real.log n) x
          ≤ vonMangoldtAtom n *
            (2 * (∫ x in Ioi (0 : ℝ), sameSideGroundJump (shiftedGroundState a) u (Real.log n) x) +
              2 * foldExcessShift a u (Real.log n)) := mul_le_mul_of_nonneg_left h hΛ
        _ = _ := by ring
  have hfub := integral_dm_foldExcessShift_eq_integral_sq_mul_foldExcessWeight ha hu.continuous huc
  unfold reflectedDifferenceEnergy sameSideEnergy
  linarith

/-- **Lower bound of the Markov energy on monotone profiles.** For `u ∈ C²_c` even, nonnegative and
nonincreasing on `[0, ∞)`,

    markovEnergy(Φ(ω_a u)) ≥ 4 sinh(a/2) ∫_{x>0} u² m_a sinh(x/2) − 2 ∫_{x>0} u² m_a W_a. -/
theorem markovEnergy_phiDoob_shiftedGroundState_ge_of_antitone {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x)
    (hnn : ∀ x, 0 ≤ u x) (hanti : AntitoneOn u (Ici 0)) :
    4 * Real.sinh (a / 2) * (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) -
        2 * (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * foldExcessWeight a x) ≤
      markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) := by
  rw [markovEnergy_phiDoob_shiftedGroundState_eq_twoSided ha hu huc heven]
  have h := reflectedDifferenceEnergy_le_of_antitone ha (hu.of_le (by norm_num)) huc hnn hanti
  linarith

/-- **Weight criterion.** If `W_a(x) ≤ 2 sinh(a/2) sinh(x/2)` on `(0, ∞)`, the Markov energy is
nonnegative on `Φ(ω_a u)` for every even `u ∈ C²_c` that is nonnegative and nonincreasing on
`[0, ∞)`. -/
theorem markovEnergy_phiDoob_shiftedGroundState_nonneg_of_antitone_of_weight_le {a : ℝ} (ha : 0 < a)
    (hW : ∀ x, 0 < x → foldExcessWeight a x ≤ 2 * Real.sinh (a / 2) * Real.sinh (x / 2))
    {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x)
    (hnn : ∀ x, 0 ≤ u x) (hanti : AntitoneOn u (Ici 0)) :
    0 ≤ markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) := by
  refine le_trans ?_ (markovEnergy_phiDoob_shiftedGroundState_ge_of_antitone ha hu huc heven hnn hanti)
  have hI1 := integrableOn_sq_mul_shiftDifference_mul_foldExcessWeight ha hu.continuous huc
  have hI2 : IntegrableOn (fun x => (2 * Real.sinh (a / 2) * shiftDifference a x * Real.sinh (x / 2)) *
      u x ^ 2) (Ioi 0) :=
    integrableOn_continuous_mul_sq ((continuous_const.mul (continuous_shiftDifference a)).mul
      (Real.continuous_sinh.comp (continuous_id.div_const 2))) hu.continuous huc _
  have hI2' : IntegrableOn (fun x => 2 * Real.sinh (a / 2) *
      (u x ^ 2 * shiftDifference a x * Real.sinh (x / 2))) (Ioi 0) :=
    hI2.congr_fun (fun x _ => by ring) measurableSet_Ioi
  have hmono : (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * foldExcessWeight a x) ≤
      ∫ x in Ioi (0 : ℝ), 2 * Real.sinh (a / 2) *
        (u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) := by
    refine setIntegral_mono_on hI1 hI2' measurableSet_Ioi fun x hx => ?_
    have hm0 := shiftDifference_nonneg_of_nonneg ha.le (mem_Ioi.mp hx).le
    calc u x ^ 2 * shiftDifference a x * foldExcessWeight a x
        ≤ u x ^ 2 * shiftDifference a x * (2 * Real.sinh (a / 2) * Real.sinh (x / 2)) :=
          mul_le_mul_of_nonneg_left (hW x (mem_Ioi.mp hx)) (mul_nonneg (sq_nonneg _) hm0)
      _ = _ := by ring
  rw [integral_const_mul] at hmono
  linarith

/-! ### The vanishing window of the fold excess -/

/-- `m_a` is monotone on `[0, a]`. -/
theorem shiftDifference_le_of_le_of_le {a y₁ y₂ : ℝ} (h0 : 0 ≤ y₁) (h12 : y₁ ≤ y₂) (h2 : y₂ ≤ a) :
    shiftDifference a y₁ ≤ shiftDifference a y₂ := by
  unfold shiftDifference
  have e1 : riemannKernelReal (y₁ - a) = riemannKernelReal (a - y₁) := by
    rw [show y₁ - a = -(a - y₁) by ring, riemannKernelReal_neg']
  have e2 : riemannKernelReal (y₂ - a) = riemannKernelReal (a - y₂) := by
    rw [show y₂ - a = -(a - y₂) by ring, riemannKernelReal_neg']
  rw [e1, e2]
  have h3 : riemannKernelReal (a - y₁) ≤ riemannKernelReal (a - y₂) :=
    riemannKernelReal_antitone_of_nonneg (by linarith) (by linarith)
  have h4 : riemannKernelReal (y₂ + a) ≤ riemannKernelReal (y₁ + a) :=
    riemannKernelReal_antitone_of_nonneg (by linarith) (by linarith)
  linarith

/-- The fold excess density vanishes on the window `x + t ≤ a`. -/
theorem foldExcessDensity_eq_zero_of_add_le {a t x : ℝ} (hx : 0 ≤ x) (hxt : x ≤ t) (h : x + t ≤ a) :
    foldExcessDensity a t x = 0 := by
  unfold foldExcessDensity
  split_ifs with hlt
  · rw [max_eq_right]
    have := shiftDifference_le_of_le_of_le (sub_nonneg.mpr hxt)
      (show t - x ≤ x + t by linarith) h
    linarith
  · rfl

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
