import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateCollarFubini

/-!
# The two-sided (Dirichlet) ground-state representation of the shifted ground states

Splitting the reflected ground jump `Φ(x)Φ(t−x)ω(x)ω(t−x)(u(x) + u(t−x))²` against the reflected
difference jump `Φ(x)Φ(t−x)ω(x)ω(t−x)(u(x) − u(t−x))²`,

    reflected sum + reflected difference = 2Φ(x)Φ(t−x)ω(x)ω(t−x)(u(x)² + u(t−x)²),

and the reflection `x ↦ t − x` of the collar give, for `ω = ω_a` in test coordinates `m_a = Φ ω_a`,

    ∫_0^t reflected sum + ∫_0^t reflected difference = 4 ∫_0^t m_a(x) m_a(t−x) u(x)² dx.

Integrated against the jump measure this is `4 ∫_{x>0} u² m_a C_a` (collar Fubini), and the folded
representation turns into the two-sided one: for every even `u ∈ C²_c(ℝ)` and `a > 0`,

    markovEnergy(Φ(ω_a u)) = 2 S_a(u) − D_a(u) + 4 sinh(a/2) ∫_{x>0} u(x)² m_a(x) sinh(x/2) dx,

with `S_a` the same-side energy `∫ dm(t) ∫_{x>0} m_a(x) m_a(x+t)(u(x) − u(x+t))²` and `D_a` the
reflected difference energy `∫ dm(t) ∫_0^t m_a(x) m_a(t−x)(u(x) − u(t−x))²`. The source term is the
two-sided source `2 sinh(a/2) sinh(x/2) Φ` of `ω_a`; the only indefinite term is `−D_a`.
Nonnegativity of the Markov energy on `Φ(ω_a u)` is therefore the **variation inequality**

    D_a(u) ≤ 2 S_a(u) + 4 sinh(a/2) ∫_{x>0} u² m_a sinh(x/2),

and the Riemann Hypothesis implies it for every `a > 0` and every even `u ∈ C²_c(ℝ)`.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The reflected difference jump -/

/-- Reflected difference jump `Φ(x)Φ(t−x) ω(x)ω(t−x) (u(x) − u(t−x))²` on the collar `0 < x < t`. -/
def reflectedDifferenceJump (ω u : ℝ → ℝ) (t x : ℝ) : ℝ :=
  riemannKernelReal x * riemannKernelReal (t - x) * ω x * ω (t - x) * (u x - u (t - x)) ^ 2

theorem reflectedGroundJump_add_reflectedDifferenceJump (ω u : ℝ → ℝ) (t x : ℝ) :
    reflectedGroundJump ω u t x + reflectedDifferenceJump ω u t x =
      2 * (riemannKernelReal x * riemannKernelReal (t - x) * ω x * ω (t - x)) *
        (u x ^ 2 + u (t - x) ^ 2) := by
  unfold reflectedGroundJump reflectedDifferenceJump
  ring

theorem reflectedDifferenceJump_shiftedGroundState (a : ℝ) (u : ℝ → ℝ) (t x : ℝ) :
    reflectedDifferenceJump (shiftedGroundState a) u t x =
      shiftDifference a x * shiftDifference a (t - x) * (u x - u (t - x)) ^ 2 := by
  unfold reflectedDifferenceJump
  have h1 := riemannKernelReal_mul_shiftedGroundState a x
  have h2 := riemannKernelReal_mul_shiftedGroundState a (t - x)
  linear_combination (riemannKernelReal (t - x) * shiftedGroundState a (t - x) *
    (u x - u (t - x)) ^ 2) * h1 + (shiftDifference a x * (u x - u (t - x)) ^ 2) * h2

theorem continuous_reflectedDifferenceJump_uncurry {ω u : ℝ → ℝ} (hω : Continuous ω)
    (hu : Continuous u) : Continuous fun p : ℝ × ℝ => reflectedDifferenceJump ω u p.1 p.2 := by
  unfold reflectedDifferenceJump
  have hΘ := continuous_riemannKernelReal
  have h1 : Continuous fun p : ℝ × ℝ => p.1 - p.2 := continuous_fst.sub continuous_snd
  exact ((((hΘ.comp continuous_snd).mul (hΘ.comp h1)).mul (hω.comp continuous_snd)).mul
    (hω.comp h1)).mul (((hu.comp continuous_snd).sub (hu.comp h1)).pow 2)

/-- Collar duality in test coordinates: reflected sum plus reflected difference integrals equal four
times the collar integral of `u² m_a ⊗ m_a`. -/
theorem integral_reflectedSum_add_reflectedDifference_shiftedGroundState (a : ℝ) {u : ℝ → ℝ}
    (hu : Continuous u) (t : ℝ) :
    (∫ x in Ioo (0 : ℝ) t, reflectedGroundJump (shiftedGroundState a) u t x) +
      (∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x) =
      4 * ∫ x in Ioo (0 : ℝ) t, shiftDifference a x * shiftDifference a (t - x) * u x ^ 2 := by
  have hm := continuous_shiftDifference a
  have hmr : Continuous fun x => shiftDifference a (t - x) :=
    hm.comp (continuous_const.sub continuous_id)
  have hur : Continuous fun x => u (t - x) := hu.comp (continuous_const.sub continuous_id)
  have hc1 : Continuous fun x => shiftDifference a x * shiftDifference a (t - x) * u x ^ 2 :=
    (hm.mul hmr).mul (hu.pow 2)
  have hc2 : Continuous fun x => shiftDifference a (t - x) * shiftDifference a x * u (t - x) ^ 2 :=
    (hmr.mul hm).mul (hur.pow 2)
  have hint1 : IntegrableOn (fun x => shiftDifference a x * shiftDifference a (t - x) * u x ^ 2)
      (Ioo (0 : ℝ) t) := hc1.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hint2 : IntegrableOn (fun x => shiftDifference a (t - x) * shiftDifference a x * u (t - x) ^ 2)
      (Ioo (0 : ℝ) t) := hc2.continuousOn.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hωc : Continuous (shiftedGroundState a) := (contDiff_shiftedGroundState a).continuous
  have hintS : IntegrableOn (fun x => reflectedGroundJump (shiftedGroundState a) u t x)
      (Ioo (0 : ℝ) t) :=
    ((continuous_reflectedGroundJump_uncurry hωc hu).comp
      (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hintD : IntegrableOn (fun x => reflectedDifferenceJump (shiftedGroundState a) u t x)
      (Ioo (0 : ℝ) t) :=
    ((continuous_reflectedDifferenceJump_uncurry hωc hu).comp
      (continuous_const.prodMk continuous_id)).continuousOn.integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hpt : ∀ x, reflectedGroundJump (shiftedGroundState a) u t x +
      reflectedDifferenceJump (shiftedGroundState a) u t x =
      2 * (shiftDifference a x * shiftDifference a (t - x) * u x ^ 2) +
        2 * (shiftDifference a (t - x) * shiftDifference a x * u (t - x) ^ 2) := by
    intro x
    rw [reflectedGroundJump_shiftedGroundState, reflectedDifferenceJump_shiftedGroundState]
    ring
  have hrefl : (∫ x in Ioo (0 : ℝ) t, shiftDifference a (t - x) * shiftDifference a x * u (t - x) ^ 2) =
      ∫ x in Ioo (0 : ℝ) t, shiftDifference a x * shiftDifference a (t - x) * u x ^ 2 := by
    have h := RHTower.setIntegral_Ioo_reflect_self
      (fun y => shiftDifference a y * shiftDifference a (t - y) * u y ^ 2) t
    refine (setIntegral_congr_fun measurableSet_Ioo fun x _ => ?_).trans h
    show shiftDifference a (t - x) * shiftDifference a x * u (t - x) ^ 2 =
      shiftDifference a (t - x) * shiftDifference a (t - (t - x)) * u (t - x) ^ 2
    rw [sub_sub_cancel]
  rw [← integral_add hintS hintD, setIntegral_congr_fun measurableSet_Ioo fun x _ => hpt x,
    integral_add (hint1.const_mul 2) (hint2.const_mul 2), integral_const_mul, integral_const_mul,
    hrefl]
  ring

/-! ### The three energies -/

/-- The same-side energy `∫ dm(t) ∫_{x>0} sameSideGroundJump ω u t x dx`. -/
def sameSideEnergy (ω u : ℝ → ℝ) : ℝ :=
  (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioi (0 : ℝ), sameSideGroundJump ω u t x) +
    ∑' n : ℕ, vonMangoldtAtom n * ∫ x in Ioi (0 : ℝ), sameSideGroundJump ω u (Real.log n) x

/-- The reflected sum energy `∫ dm(t) ∫_0^t reflectedGroundJump ω u t x dx`. -/
def reflectedSumEnergy (ω u : ℝ → ℝ) : ℝ :=
  (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, reflectedGroundJump ω u t x) +
    ∑' n : ℕ, vonMangoldtAtom n *
      ∫ x in Ioo (0 : ℝ) (Real.log n), reflectedGroundJump ω u (Real.log n) x

/-- The reflected difference energy `∫ dm(t) ∫_0^t reflectedDifferenceJump ω u t x dx`. -/
def reflectedDifferenceEnergy (ω u : ℝ → ℝ) : ℝ :=
  (∫ t in Ioi (0 : ℝ), archLevyDensity t *
      ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump ω u t x) +
    ∑' n : ℕ, vonMangoldtAtom n *
      ∫ x in Ioo (0 : ℝ) (Real.log n), reflectedDifferenceJump ω u (Real.log n) x

theorem measurable_sameSideIntegral {ω u : ℝ → ℝ} (hω : Continuous ω) (hu : Continuous u) :
    Measurable fun t => ∫ x in Ioi (0 : ℝ), sameSideGroundJump ω u t x :=
  ((continuous_sameSideGroundJump_uncurry hω hu).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Ioi 0))).measurable

theorem measurable_reflectedSumIntegral {ω u : ℝ → ℝ} (hω : Continuous ω) (hu : Continuous u) :
    Measurable fun t => ∫ x in Ioo (0 : ℝ) t, reflectedGroundJump ω u t x := by
  have hF : Measurable fun p : ℝ × ℝ =>
      if 0 < p.2 ∧ p.2 < p.1 then reflectedGroundJump ω u p.1 p.2 else 0 := by
    refine Measurable.ite ?_ (continuous_reflectedGroundJump_uncurry hω hu).measurable
      measurable_const
    rw [Set.setOf_and]
    exact (measurableSet_lt measurable_const measurable_snd).inter
      (measurableSet_lt measurable_snd measurable_fst)
  have h := (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).measurable
  have heq : (fun t => ∫ x in Ioo (0 : ℝ) t, reflectedGroundJump ω u t x) =
      fun t => ∫ x, (if 0 < x ∧ x < t then reflectedGroundJump ω u t x else 0) := by
    funext t
    rw [← integral_indicator measurableSet_Ioo]
    congr 1
    funext x
    simp only [Set.indicator_apply, mem_Ioo]
  rw [heq]
  exact h

/-! ### Splitting the ground remainder -/

theorem integral_sameSideGroundJump_nonneg {ω u : ℝ → ℝ} (hpos : ∀ x, 0 < x → 0 ≤ ω x) {t : ℝ}
    (ht : 0 ≤ t) : 0 ≤ ∫ x in Ioi (0 : ℝ), sameSideGroundJump ω u t x :=
  setIntegral_nonneg measurableSet_Ioi fun _ hx => sameSideGroundJump_nonneg hpos ht hx

theorem integral_reflectedGroundJump_nonneg {ω u : ℝ → ℝ} (hpos : ∀ x, 0 < x → 0 ≤ ω x) (t : ℝ) :
    0 ≤ ∫ x in Ioo (0 : ℝ) t, reflectedGroundJump ω u t x :=
  setIntegral_nonneg measurableSet_Ioo fun _ hx => reflectedGroundJump_nonneg hpos hx.1 hx.2

theorem integrableOn_archLevy_mul_sameSideIntegral {ω u : ℝ → ℝ} (hω : Continuous ω)
    (hu : Continuous u) (hpos : ∀ x, 0 < x → 0 ≤ ω x) (hadm : FoldedAdmissible ω u) :
    IntegrableOn (fun t => archLevyDensity t * ∫ x in Ioi (0 : ℝ), sameSideGroundJump ω u t x)
      (Ioi 0) := by
  refine hadm.arch_remainder.mono'
    (measurable_archLevyDensity.mul (measurable_sameSideIntegral hω hu)).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
  have hL := archLevyDensity_pos (mem_Ioi.mp ht)
  have hS := integral_sameSideGroundJump_nonneg (u := u) hpos (mem_Ioi.mp ht).le
  have hR := integral_reflectedGroundJump_nonneg (u := u) hpos t
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hL, abs_of_nonneg hS]
  unfold groundRemainderShift
  exact mul_le_mul_of_nonneg_left (by linarith) hL.le

theorem integrableOn_archLevy_mul_reflectedSumIntegral {ω u : ℝ → ℝ} (hω : Continuous ω)
    (hu : Continuous u) (hpos : ∀ x, 0 < x → 0 ≤ ω x) (hadm : FoldedAdmissible ω u) :
    IntegrableOn (fun t => archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, reflectedGroundJump ω u t x)
      (Ioi 0) := by
  refine hadm.arch_remainder.mono'
    (measurable_archLevyDensity.mul (measurable_reflectedSumIntegral hω hu)).aestronglyMeasurable ?_
  refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
  have hL := archLevyDensity_pos (mem_Ioi.mp ht)
  have hS := integral_sameSideGroundJump_nonneg (u := u) hpos (mem_Ioi.mp ht).le
  have hR := integral_reflectedGroundJump_nonneg (u := u) hpos t
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos hL, abs_of_nonneg hR]
  unfold groundRemainderShift
  exact mul_le_mul_of_nonneg_left (by linarith) hL.le

theorem summable_atom_mul_sameSideIntegral {ω u : ℝ → ℝ} (hpos : ∀ x, 0 < x → 0 ≤ ω x)
    (hadm : FoldedAdmissible ω u) :
    Summable fun n : ℕ =>
      vonMangoldtAtom n * ∫ x in Ioi (0 : ℝ), sameSideGroundJump ω u (Real.log n) x := by
  refine hadm.prime_remainder.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact mul_nonneg (vonMangoldtAtom_nonneg n)
      (integral_sameSideGroundJump_nonneg hpos (Real.log_natCast_nonneg n))
  · have hS := integral_sameSideGroundJump_nonneg (u := u) hpos (Real.log_natCast_nonneg n)
    have hR := integral_reflectedGroundJump_nonneg (u := u) hpos (Real.log n)
    unfold groundRemainderShift
    exact mul_le_mul_of_nonneg_left (by linarith) (vonMangoldtAtom_nonneg n)

theorem summable_atom_mul_reflectedSumIntegral {ω u : ℝ → ℝ} (hpos : ∀ x, 0 < x → 0 ≤ ω x)
    (hadm : FoldedAdmissible ω u) :
    Summable fun n : ℕ => vonMangoldtAtom n *
      ∫ x in Ioo (0 : ℝ) (Real.log n), reflectedGroundJump ω u (Real.log n) x := by
  refine hadm.prime_remainder.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
  · exact mul_nonneg (vonMangoldtAtom_nonneg n) (integral_reflectedGroundJump_nonneg hpos _)
  · have hS := integral_sameSideGroundJump_nonneg (u := u) hpos (Real.log_natCast_nonneg n)
    have hR := integral_reflectedGroundJump_nonneg (u := u) hpos (Real.log n)
    unfold groundRemainderShift
    exact mul_le_mul_of_nonneg_left (by linarith) (vonMangoldtAtom_nonneg n)

/-- The ground remainder is twice the same-side energy plus the reflected sum energy. -/
theorem groundRemainder_eq_two_sameSide_add_reflectedSum {ω u : ℝ → ℝ} (hω : Continuous ω)
    (hu : Continuous u) (hpos : ∀ x, 0 < x → 0 ≤ ω x) (hadm : FoldedAdmissible ω u) :
    groundRemainder ω u = 2 * sameSideEnergy ω u + reflectedSumEnergy ω u := by
  have hSint := integrableOn_archLevy_mul_sameSideIntegral hω hu hpos hadm
  have hRint := integrableOn_archLevy_mul_reflectedSumIntegral hω hu hpos hadm
  have hSsum := summable_atom_mul_sameSideIntegral hpos hadm
  have hRsum := summable_atom_mul_reflectedSumIntegral hpos hadm
  have harch : (∫ t in Ioi (0 : ℝ), archLevyDensity t * groundRemainderShift ω u t) =
      2 * (∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioi (0 : ℝ), sameSideGroundJump ω u t x) +
        ∫ t in Ioi (0 : ℝ), archLevyDensity t * ∫ x in Ioo (0 : ℝ) t, reflectedGroundJump ω u t x := by
    rw [← integral_const_mul, ← integral_add (hSint.const_mul 2) hRint]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    unfold groundRemainderShift
    ring
  have hprime : (∑' n : ℕ, vonMangoldtAtom n * groundRemainderShift ω u (Real.log n)) =
      2 * (∑' n : ℕ, vonMangoldtAtom n *
          ∫ x in Ioi (0 : ℝ), sameSideGroundJump ω u (Real.log n) x) +
        ∑' n : ℕ, vonMangoldtAtom n *
          ∫ x in Ioo (0 : ℝ) (Real.log n), reflectedGroundJump ω u (Real.log n) x := by
    rw [← tsum_mul_left, ← (hSsum.mul_left 2).tsum_add hRsum]
    refine tsum_congr fun n => ?_
    unfold groundRemainderShift
    ring
  unfold groundRemainder sameSideEnergy reflectedSumEnergy
  rw [harch, hprime]
  ring

/-! ### Collar duality for the energies -/

theorem integrableOn_archLevy_mul_reflectedDifferenceIntegral {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    IntegrableOn (fun t => archLevyDensity t *
      ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x) (Ioi 0) := by
  have hωc : Continuous (shiftedGroundState a) := (contDiff_shiftedGroundState a).continuous
  have hpos : ∀ x, 0 < x → 0 ≤ shiftedGroundState a x := fun x hx =>
    (shiftedGroundState_pos ha hx).le
  have hadm := foldedAdmissible_shiftedGroundState ha hu huc
  have hR := integrableOn_archLevy_mul_reflectedSumIntegral hωc hu.continuous hpos hadm
  have hC := integrableOn_archLevy_mul_collarIntegral ha hu.continuous huc
  have hsub : IntegrableOn (fun t => 4 * (archLevyDensity t *
      ∫ x in Ioo (0 : ℝ) t, shiftDifference a x * shiftDifference a (t - x) * u x ^ 2) -
      archLevyDensity t *
        ∫ x in Ioo (0 : ℝ) t, reflectedGroundJump (shiftedGroundState a) u t x) (Ioi 0) :=
    (hC.const_mul 4).sub hR
  refine hsub.congr_fun (fun t _ => ?_) measurableSet_Ioi
  have h := integral_reflectedSum_add_reflectedDifference_shiftedGroundState a hu.continuous t
  linear_combination (-archLevyDensity t) * h

theorem summable_atom_mul_reflectedDifferenceIntegral {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    Summable fun n : ℕ => vonMangoldtAtom n *
      ∫ x in Ioo (0 : ℝ) (Real.log n), reflectedDifferenceJump (shiftedGroundState a) u (Real.log n) x := by
  have hpos : ∀ x, 0 < x → 0 ≤ shiftedGroundState a x := fun x hx =>
    (shiftedGroundState_pos ha hx).le
  have hadm := foldedAdmissible_shiftedGroundState ha hu huc
  have hR := summable_atom_mul_reflectedSumIntegral hpos hadm
  have hC := summable_atom_mul_collarIntegral ha hu.continuous huc
  refine ((hC.mul_left 4).sub hR).congr fun n => ?_
  have h := integral_reflectedSum_add_reflectedDifference_shiftedGroundState a hu.continuous
    (Real.log n)
  linear_combination (-vonMangoldtAtom n) * h

/-- Reflected sum energy plus reflected difference energy equals `4 ∫_{x>0} u² m_a C_a`. -/
theorem reflectedSumEnergy_add_reflectedDifferenceEnergy_shiftedGroundState {a : ℝ} (ha : 0 < a)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) :
    reflectedSumEnergy (shiftedGroundState a) u + reflectedDifferenceEnergy (shiftedGroundState a) u =
      4 * ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * shiftedCollarMass a x := by
  have hωc : Continuous (shiftedGroundState a) := (contDiff_shiftedGroundState a).continuous
  have hpos : ∀ x, 0 < x → 0 ≤ shiftedGroundState a x := fun x hx =>
    (shiftedGroundState_pos ha hx).le
  have hadm := foldedAdmissible_shiftedGroundState ha hu huc
  have hRint := integrableOn_archLevy_mul_reflectedSumIntegral hωc hu.continuous hpos hadm
  have hDint := integrableOn_archLevy_mul_reflectedDifferenceIntegral ha hu huc
  have hRsum := summable_atom_mul_reflectedSumIntegral hpos hadm
  have hDsum := summable_atom_mul_reflectedDifferenceIntegral ha hu huc
  have hpt := integral_reflectedSum_add_reflectedDifference_shiftedGroundState a hu.continuous
  have harch : (∫ t in Ioi (0 : ℝ), archLevyDensity t *
        ∫ x in Ioo (0 : ℝ) t, reflectedGroundJump (shiftedGroundState a) u t x) +
      (∫ t in Ioi (0 : ℝ), archLevyDensity t *
        ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x) =
      4 * ∫ t in Ioi (0 : ℝ), archLevyDensity t *
        ∫ x in Ioo (0 : ℝ) t, shiftDifference a x * shiftDifference a (t - x) * u x ^ 2 := by
    rw [← integral_add hRint hDint, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    rw [← mul_add, hpt t]
    ring
  have hprime : (∑' n : ℕ, vonMangoldtAtom n *
        ∫ x in Ioo (0 : ℝ) (Real.log n), reflectedGroundJump (shiftedGroundState a) u (Real.log n) x) +
      (∑' n : ℕ, vonMangoldtAtom n *
        ∫ x in Ioo (0 : ℝ) (Real.log n),
          reflectedDifferenceJump (shiftedGroundState a) u (Real.log n) x) =
      4 * ∑' n : ℕ, vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n),
        shiftDifference a x * shiftDifference a (Real.log n - x) * u x ^ 2 := by
    rw [← hRsum.tsum_add hDsum, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    rw [← mul_add, hpt]
    ring
  have hfub := integral_dm_collar_eq_integral_sq_mul_collarMass ha hu.continuous huc
  unfold reflectedSumEnergy reflectedDifferenceEnergy
  linear_combination harch + hprime + 4 * hfub

/-! ### The two-sided representation and the variation inequality -/

/-- **Two-sided ground-state representation of the shifted ground states.** For every `a > 0` and
every even `u ∈ C²_c(ℝ)`,

    markovEnergy(Φ(ω_a u)) = 2 S_a(u) − D_a(u) + 4 sinh(a/2) ∫_{x>0} u² m_a sinh(x/2). -/
theorem markovEnergy_phiDoob_shiftedGroundState_eq_twoSided {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ}
    (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) =
      2 * sameSideEnergy (shiftedGroundState a) u -
        reflectedDifferenceEnergy (shiftedGroundState a) u +
        4 * Real.sinh (a / 2) *
          ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) := by
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hωc : Continuous (shiftedGroundState a) := (contDiff_shiftedGroundState a).continuous
  have hpos : ∀ x, 0 < x → 0 ≤ shiftedGroundState a x := fun x hx =>
    (shiftedGroundState_pos ha hx).le
  have hadm := foldedAdmissible_shiftedGroundState ha hu1 huc
  have hsum := reflectedSumEnergy_add_reflectedDifferenceEnergy_shiftedGroundState ha hu1 huc
  have hI1 := integrableOn_sq_mul_shiftDifference_mul_collarMass ha hu.continuous huc
  have hI2 : IntegrableOn (fun x => (Real.sinh (a / 2) * shiftDifference a x * Real.sinh (x / 2)) *
      u x ^ 2) (Ioi 0) :=
    integrableOn_continuous_mul_sq ((continuous_const.mul (continuous_shiftDifference a)).mul
      (Real.continuous_sinh.comp (continuous_id.div_const 2))) hu.continuous huc _
  have hsplit : (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftedGroundState a x * riemannKernelReal x *
        (shiftedCollarMass a x - Real.sinh (a / 2) * Real.sinh (x / 2))) =
      (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * shiftedCollarMass a x) -
        Real.sinh (a / 2) * ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) := by
    have hI2' : IntegrableOn (fun x => Real.sinh (a / 2) *
        (u x ^ 2 * shiftDifference a x * Real.sinh (x / 2))) (Ioi 0) :=
      hI2.congr_fun (fun x _ => by ring) measurableSet_Ioi
    rw [← integral_const_mul, ← integral_sub hI1 hI2']
    refine setIntegral_congr_fun measurableSet_Ioi fun x _ => ?_
    rw [← riemannKernelReal_mul_shiftedGroundState a x]
    ring
  rw [markovEnergy_phiDoob_shiftedGroundState_eq_of_contDiff ha hu huc heven,
    groundRemainder_eq_two_sameSide_add_reflectedSum hωc hu.continuous hpos hadm, hsplit]
  linear_combination hsum

/-- Nonnegativity of the Markov energy on `Φ(ω_a u)` is the variation inequality
`D_a(u) ≤ 2 S_a(u) + 4 sinh(a/2) ∫_{x>0} u² m_a sinh(x/2)`. -/
theorem markovEnergy_phiDoob_shiftedGroundState_nonneg_iff_variation {a : ℝ} (ha : 0 < a)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    0 ≤ markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) ↔
      reflectedDifferenceEnergy (shiftedGroundState a) u ≤
        2 * sameSideEnergy (shiftedGroundState a) u +
          4 * Real.sinh (a / 2) *
            ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) := by
  rw [markovEnergy_phiDoob_shiftedGroundState_eq_twoSided ha hu huc heven]
  constructor <;> intro h <;> linarith

/-- **The Riemann Hypothesis implies the variation inequality** for every `a > 0` and every even
`u ∈ C²_c(ℝ)`. -/
theorem reflectedDifferenceEnergy_le_of_riemannHypothesis (hRH : RiemannHypothesis) {a : ℝ}
    (ha : 0 < a) {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u)
    (heven : ∀ x, u (-x) = u x) :
    reflectedDifferenceEnergy (shiftedGroundState a) u ≤
      2 * sameSideEnergy (shiftedGroundState a) u +
        4 * Real.sinh (a / 2) *
          ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) := by
  rw [← markovEnergy_phiDoob_shiftedGroundState_nonneg_iff_variation ha hu huc heven]
  have hv : ContDiff ℝ 2 fun y => shiftedGroundState a y * u y :=
    (contDiff_shiftedGroundState a).mul hu
  have hvc : HasCompactSupport fun y => shiftedGroundState a y * u y := huc.mul_left
  have hodd : ∀ x, (fun y => shiftedGroundState a y * u y) (-x) =
      -(fun y => shiftedGroundState a y * u y) x := fun x => by
    simp only
    rw [shiftedGroundState_neg, heven]
    ring
  exact (riemannHypothesis_iff_forall_odd_phiDoob_markovEnergy_nonneg.mp hRH) _ hv hvc hodd

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
