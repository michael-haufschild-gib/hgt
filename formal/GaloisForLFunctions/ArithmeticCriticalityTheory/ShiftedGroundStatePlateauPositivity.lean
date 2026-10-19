import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftAveragedEnergies

/-!
# Plateau positivity of the shifted ground states

The odd test `m_a = Φ(· − a) − Φ(· + a)` has half-line sinh moment

    ∫_{x>0} m_a(x) sinh(x/2) dx = sinh(a/2)/2,

so in the two-sided representation the source of the shifted ground state against the constant
profile `u ≡ 1` equals `2 sinh²(a/2)`: the pole term of the explicit formula, the Mellin transform
of `m_a` being `−2 sinh(a(s − 1/2)) ξ(s)`, which vanishes at every zero of `ξ`.

For a profile `u` with `0 ≤ u ≤ 1` and `u = 1` on `[−L, L]`, the reflected difference energy is
supported where one of the two points lies beyond `L`, hence is at most a constant times
`e^{−8L}`, and the source differs from `2 sinh²(a/2)` by at most a constant times `e^{−8L}`. The
same-side energy is nonnegative. Hence for every shift `a > 0` and every sufficiently wide plateau,

    markovEnergy(Φ(ω_a u)) ≥ sinh²(a/2) > 0

unconditionally: the shifted ground states are positive directions of the odd Markov form on
wide plateaus, with no restriction on the shift.
-/

open MeasureTheory Set Filter Topology
open RHTower RHTower.CHMDPolar

noncomputable section

namespace GaloisForLFunctions.ArithmeticCriticalityTheory

/-! ### The sinh moment of the shift difference -/

theorem integrable_shiftDifference_mul_sinh_half (a : ℝ) :
    Integrable fun x : ℝ => shiftDifference a x * Real.sinh (x / 2) := by
  have h1 := integrable_sinh_mul_kernel_sub a
  have h2 := integrable_sinh_mul_kernel_add a
  refine (h1.sub h2).congr (Eventually.of_forall fun x => ?_)
  simp only [Pi.sub_apply]
  unfold shiftDifference
  rw [show a - x = -(x - a) by ring, riemannKernelReal_neg', add_comm a x]
  ring

/-- `∫ m_a(x) sinh(x/2) dx = sinh(a/2)`. -/
theorem integral_shiftDifference_mul_sinh_half (a : ℝ) :
    (∫ x : ℝ, shiftDifference a x * Real.sinh (x / 2)) = Real.sinh (a / 2) := by
  have h1 := integrable_sinh_mul_kernel_sub a
  have h2 := integrable_sinh_mul_kernel_add a
  have e : (fun x : ℝ => shiftDifference a x * Real.sinh (x / 2)) = fun x =>
      Real.sinh (x / 2) * riemannKernelReal (a - x) - Real.sinh (x / 2) * riemannKernelReal (a + x) := by
    funext x
    unfold shiftDifference
    rw [show a - x = -(x - a) by ring, riemannKernelReal_neg', add_comm a x]
    ring
  rw [e, integral_sub h1 h2, integral_sinh_mul_kernel_sub, integral_sinh_mul_kernel_add]
  ring

/-- `∫_{x>0} m_a(x) sinh(x/2) dx = sinh(a/2)/2`. -/
theorem integral_Ioi_shiftDifference_mul_sinh_half (a : ℝ) :
    (∫ x in Ioi (0 : ℝ), shiftDifference a x * Real.sinh (x / 2)) = Real.sinh (a / 2) / 2 := by
  rw [integral_Ioi_eq_half_of_even (integrable_shiftDifference_mul_sinh_half a) (fun x => by
    rw [shiftDifference_neg, show -x / 2 = -(x / 2) by ring, Real.sinh_neg]
    ring), integral_shiftDifference_mul_sinh_half]
  ring

/-! ### Superexponential bounds -/

theorem exists_riemannKernelReal_le_exp_sixteen :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x, riemannKernelReal x ≤ C * Real.exp (-(16 * |x|)) := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_riemannPhiKernel_le_exp (B := 16) (by norm_num)
  refine ⟨C, hC0, fun x => ?_⟩
  have h := hC x
  rwa [riemannPhiKernel_eq_ofReal, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (riemannKernelReal_pos x)] at h

/-- The tail `∫_{x>L} m_a(x) sinh(x/2) dx ≤ C e^{16a} e^{−8L}` for `L ≥ 0`. -/
theorem integral_Ioi_shiftDifference_mul_sinh_half_tail_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, riemannKernelReal x ≤ C * Real.exp (-(16 * |x|))) (a : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    (∫ x in Ioi L, shiftDifference a x * Real.sinh (x / 2)) ≤
      C * Real.exp (16 * a) * Real.exp (-(8 * L)) := by
  have hb : ∀ x ∈ Ioi L, shiftDifference a x * Real.sinh (x / 2) ≤
      C * Real.exp (16 * a) * Real.exp (-(8 * L)) * Real.exp (-x) := by
    intro x hx
    have hx0 : 0 ≤ x := le_trans hL (le_of_lt hx)
    have hxL : L ≤ x := le_of_lt hx
    have hm : shiftDifference a x ≤ C * Real.exp (16 * a) * Real.exp (-(16 * x)) := by
      refine (shiftDifference_le_kernel a x).trans ((hC _).trans ?_)
      rw [mul_assoc, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0
      linarith [le_abs_self (x - a)]
    have hs : Real.sinh (x / 2) ≤ Real.exp x := by
      rw [Real.sinh_eq]
      have := Real.exp_pos (-(x / 2))
      have := Real.exp_pos x
      have h2 : Real.exp (x / 2) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
      linarith
    have hs0 : 0 ≤ Real.sinh (x / 2) := Real.sinh_nonneg_iff.mpr (by linarith)
    have hm0 : 0 ≤ C * Real.exp (16 * a) * Real.exp (-(16 * x)) := by positivity
    calc shiftDifference a x * Real.sinh (x / 2)
        ≤ (C * Real.exp (16 * a) * Real.exp (-(16 * x))) * Real.exp x := mul_le_mul hm hs hs0 hm0
      _ = C * Real.exp (16 * a) * Real.exp (-(15 * x)) := by
          rw [mul_assoc, ← Real.exp_add]
          congr 2
          ring
      _ ≤ C * Real.exp (16 * a) * (Real.exp (-(8 * L)) * Real.exp (-x)) := by
          rw [← Real.exp_add]
          refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
          linarith
      _ = _ := by ring
  calc (∫ x in Ioi L, shiftDifference a x * Real.sinh (x / 2))
      ≤ ∫ x in Ioi L, C * Real.exp (16 * a) * Real.exp (-(8 * L)) * Real.exp (-x) :=
        setIntegral_mono_on (integrable_shiftDifference_mul_sinh_half a).integrableOn
          ((integrableOn_exp_neg_Ioi L).const_mul _) measurableSet_Ioi hb
    _ = C * Real.exp (16 * a) * Real.exp (-(8 * L)) * Real.exp (-L) := by
        rw [integral_const_mul, integral_exp_neg_Ioi]
    _ ≤ C * Real.exp (16 * a) * Real.exp (-(8 * L)) * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.mpr (by linarith)
    _ = _ := mul_one _

/-- The source of a plateau profile: `∫_{x>0} u² m_a sinh(x/2) ≥ sinh(a/2)/2 − C e^{16a} e^{−8L}`
when `0 ≤ u ≤ 1` and `u = 1` on `[−L, L]`. -/
theorem integral_sq_mul_shiftDifference_mul_sinh_ge {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, riemannKernelReal x ≤ C * Real.exp (-(16 * |x|))) {a : ℝ} (ha : 0 < a)
    {u : ℝ → ℝ} (hu : Continuous u) (huc : HasCompactSupport u)
    {L : ℝ} (hL : 0 ≤ L) (hone : ∀ x, |x| ≤ L → u x = 1) :
    Real.sinh (a / 2) / 2 - C * Real.exp (16 * a) * Real.exp (-(8 * L)) ≤
      ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) := by
  have hint := integrable_shiftDifference_mul_sinh_half a
  have hI1 : IntegrableOn (fun x => shiftDifference a x * Real.sinh (x / 2) -
      (Ioi L).indicator (fun x => shiftDifference a x * Real.sinh (x / 2)) x) (Ioi 0) :=
    (hint.sub (hint.indicator measurableSet_Ioi)).integrableOn
  have hI2 : IntegrableOn (fun x => u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) (Ioi 0) := by
    have hg : Continuous fun x => shiftDifference a x * Real.sinh (x / 2) :=
      (continuous_shiftDifference a).mul (Real.continuous_sinh.comp (continuous_id.div_const 2))
    refine (integrableOn_continuous_mul_sq hg hu huc (Ioi 0)).congr_fun (fun x _ => ?_)
      measurableSet_Ioi
    show shiftDifference a x * Real.sinh (x / 2) * u x ^ 2 = _
    ring
  have hmono : (∫ x in Ioi (0 : ℝ), (shiftDifference a x * Real.sinh (x / 2) -
      (Ioi L).indicator (fun x => shiftDifference a x * Real.sinh (x / 2)) x)) ≤
      ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) := by
    refine setIntegral_mono_on hI1 hI2 measurableSet_Ioi fun x hx => ?_
    have hx0 : 0 < x := hx
    have hnn' : 0 ≤ shiftDifference a x * Real.sinh (x / 2) :=
      mul_nonneg (shiftDifference_nonneg_of_nonneg ha.le hx0.le)
        (Real.sinh_nonneg_iff.mpr (by linarith))
    rw [Set.indicator_apply]
    split_ifs with hxL
    · rw [sub_self]
      exact mul_nonneg (mul_nonneg (sq_nonneg _) (shiftDifference_nonneg_of_nonneg ha.le hx0.le))
        (Real.sinh_nonneg_iff.mpr (by linarith))
    · rw [sub_zero, hone x (by rw [abs_of_pos hx0]; exact not_lt.mp hxL)]
      ring_nf
      exact le_refl _
  have hsplit : (∫ x in Ioi (0 : ℝ), (shiftDifference a x * Real.sinh (x / 2) -
      (Ioi L).indicator (fun x => shiftDifference a x * Real.sinh (x / 2)) x)) =
      Real.sinh (a / 2) / 2 - ∫ x in Ioi L, shiftDifference a x * Real.sinh (x / 2) := by
    rw [integral_sub hint.integrableOn (hint.indicator measurableSet_Ioi).integrableOn,
      integral_Ioi_shiftDifference_mul_sinh_half, setIntegral_indicator measurableSet_Ioi,
      Ioi_inter_Ioi, max_eq_right hL]
  have htail := integral_Ioi_shiftDifference_mul_sinh_half_tail_le hC0 hC a hL
  linarith

/-! ### The reflected difference energy of a plateau profile -/

theorem sq_sub_le_one_of_mem_unit {u : ℝ → ℝ} (hnn : ∀ x, 0 ≤ u x) (hle : ∀ x, u x ≤ 1)
    (x y : ℝ) : (u x - u y) ^ 2 ≤ 1 := by
  have h : |u x - u y| ≤ 1 := abs_sub_le_iff.mpr ⟨by linarith [hnn y, hle x], by linarith [hnn x, hle y]⟩
  calc (u x - u y) ^ 2 = |u x - u y| ^ 2 := (sq_abs _).symm
    _ ≤ 1 ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = 1 := one_pow 2

/-- Pointwise bound of the reflected difference jump of a plateau profile:
`m_a(x) m_a(t−x) (u(x) − u(t−x))² ≤ Φ(0) C e^{16a} e^{−8L} e^{−4t}`. -/
theorem reflectedDifferenceJump_plateau_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, riemannKernelReal x ≤ C * Real.exp (-(16 * |x|))) {a : ℝ} (ha : 0 < a)
    {u : ℝ → ℝ} (hnn : ∀ x, 0 ≤ u x) (hle : ∀ x, u x ≤ 1) {L : ℝ}
    (hone : ∀ x, |x| ≤ L → u x = 1) {t x : ℝ} (hx : 0 < x) (hxt : x < t) :
    reflectedDifferenceJump (shiftedGroundState a) u t x ≤
      riemannKernelReal 0 * (C * Real.exp (16 * a)) * Real.exp (-(8 * L)) * Real.exp (-(4 * t)) := by
  rw [reflectedDifferenceJump_shiftedGroundState]
  have hΘ0 := (riemannKernelReal_pos 0).le
  have hm1 : 0 ≤ shiftDifference a x := shiftDifference_nonneg_of_nonneg ha.le hx.le
  have hm2 : 0 ≤ shiftDifference a (t - x) := shiftDifference_nonneg_of_nonneg ha.le (by linarith)
  have hRHS : 0 ≤ riemannKernelReal 0 * (C * Real.exp (16 * a)) * Real.exp (-(8 * L)) *
      Real.exp (-(4 * t)) := by positivity
  by_cases hboth : x ≤ L ∧ t - x ≤ L
  · rw [hone x (by rw [abs_of_pos hx]; exact hboth.1),
      hone (t - x) (by rw [abs_of_pos (by linarith)]; exact hboth.2), sub_self]
    simpa using hRHS
  · -- the kernel at the far point `M = max(x, t − x)`: `m_a(M) ≤ C e^{16a} e^{−16M}`, `16M ≥ 4t + 8L`
    have hfar : ∀ M, L < M → t / 2 ≤ M →
        shiftDifference a M ≤ C * Real.exp (16 * a) * Real.exp (-(8 * L)) * Real.exp (-(4 * t)) := by
      intro M hLM htM
      refine (shiftDifference_le_kernel a M).trans ((hC _).trans ?_)
      rw [mul_assoc (C * Real.exp (16 * a)), ← Real.exp_add, mul_assoc C, ← Real.exp_add]
      refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) hC0
      linarith [le_abs_self (M - a)]
    have hM : L < max x (t - x) ∧ t / 2 ≤ max x (t - x) := by
      rw [not_and_or] at hboth
      refine ⟨?_, by linarith [le_max_left x (t - x), le_max_right x (t - x)]⟩
      rcases hboth with h | h
      · exact lt_of_lt_of_le (not_le.mp h) (le_max_left _ _)
      · exact lt_of_lt_of_le (not_le.mp h) (le_max_right _ _)
    have hfarM := hfar (max x (t - x)) hM.1 hM.2
    have hsq := sq_sub_le_one_of_mem_unit hnn hle x (t - x)
    have hc0 : 0 ≤ C * Real.exp (16 * a) * Real.exp (-(8 * L)) * Real.exp (-(4 * t)) := by
      positivity
    have hprod : shiftDifference a x * shiftDifference a (t - x) ≤
        riemannKernelReal 0 *
          (C * Real.exp (16 * a) * Real.exp (-(8 * L)) * Real.exp (-(4 * t))) := by
      rcases max_choice x (t - x) with hmx | hmx
      · rw [hmx] at hfarM
        calc shiftDifference a x * shiftDifference a (t - x)
            ≤ (C * Real.exp (16 * a) * Real.exp (-(8 * L)) * Real.exp (-(4 * t))) *
              riemannKernelReal 0 :=
              mul_le_mul hfarM ((abs_le.mp (abs_shiftDifference_le a (t - x))).2) hm2 hc0
          _ = _ := by ring
      · rw [hmx] at hfarM
        exact mul_le_mul ((abs_le.mp (abs_shiftDifference_le a x)).2) hfarM hm2 hΘ0
    calc shiftDifference a x * shiftDifference a (t - x) * (u x - u (t - x)) ^ 2
        ≤ (riemannKernelReal 0 *
            (C * Real.exp (16 * a) * Real.exp (-(8 * L)) * Real.exp (-(4 * t)))) * 1 :=
          mul_le_mul hprod hsq (sq_nonneg _) (by positivity)
      _ = _ := by ring

/-- The reflected difference energy of a plateau profile is at most
`Φ(0) C e^{16a} (∫ archLevyDensity(t) t dt + Σ 1/n²) e^{−8L}`. -/
theorem reflectedDifferenceEnergy_plateau_le {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ x, riemannKernelReal x ≤ C * Real.exp (-(16 * |x|))) {a : ℝ} (ha : 0 < a)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 1 u) (huc : HasCompactSupport u) (hnn : ∀ x, 0 ≤ u x)
    (hle : ∀ x, u x ≤ 1) {L : ℝ} (hone : ∀ x, |x| ≤ L → u x = 1) :
    reflectedDifferenceEnergy (shiftedGroundState a) u ≤
      riemannKernelReal 0 * (C * Real.exp (16 * a)) *
        ((∫ t in Ioi (0 : ℝ), archLevyDensity t * t) + ∑' n : ℕ, 1 / (n : ℝ) ^ 2) *
        Real.exp (-(8 * L)) := by
  have hΘ0 := (riemannKernelReal_pos 0).le
  have hK0 : 0 ≤ riemannKernelReal 0 * (C * Real.exp (16 * a)) * Real.exp (-(8 * L)) := by
    positivity
  have hD : ∀ t, 0 < t →
      (∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x) ≤
        riemannKernelReal 0 * (C * Real.exp (16 * a)) * Real.exp (-(8 * L)) *
          Real.exp (-(4 * t)) * t := by
    intro t ht
    have hb : ∀ x ∈ Ioo (0 : ℝ) t, ‖reflectedDifferenceJump (shiftedGroundState a) u t x‖ ≤
        riemannKernelReal 0 * (C * Real.exp (16 * a)) * Real.exp (-(8 * L)) *
          Real.exp (-(4 * t)) := by
      intro x hx
      rw [Real.norm_eq_abs, abs_of_nonneg]
      · exact reflectedDifferenceJump_plateau_le hC0 hC ha hnn hle hone hx.1 hx.2
      · rw [reflectedDifferenceJump_shiftedGroundState]
        exact mul_nonneg (mul_nonneg (shiftDifference_nonneg_of_nonneg ha.le hx.1.le)
          (shiftDifference_nonneg_of_nonneg ha.le (by linarith [hx.2]))) (sq_nonneg _)
    have h := norm_setIntegral_le_of_norm_le_const (μ := volume) (s := Ioo (0 : ℝ) t)
      (by rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top) hb
    rw [Real.volume_real_Ioo, max_eq_left (by linarith), sub_zero, Real.norm_eq_abs] at h
    exact (le_abs_self _).trans h
  have hA : (∫ t in Ioi (0 : ℝ), archLevyDensity t *
      ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x) ≤
      (riemannKernelReal 0 * (C * Real.exp (16 * a)) * Real.exp (-(8 * L))) *
        ∫ t in Ioi (0 : ℝ), archLevyDensity t * t := by
    rw [← integral_const_mul]
    refine setIntegral_mono_on (integrableOn_archLevy_mul_reflectedDifferenceIntegral ha hu huc)
      (integrableOn_archLevyDensity_mul_id.const_mul _) measurableSet_Ioi fun t ht => ?_
    have ht0 : 0 < t := ht
    have hL' := archLevyDensity_pos ht0
    have he : Real.exp (-(4 * t)) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.mpr (by linarith)
    calc archLevyDensity t *
          ∫ x in Ioo (0 : ℝ) t, reflectedDifferenceJump (shiftedGroundState a) u t x
        ≤ archLevyDensity t * (riemannKernelReal 0 * (C * Real.exp (16 * a)) *
            Real.exp (-(8 * L)) * Real.exp (-(4 * t)) * t) :=
          mul_le_mul_of_nonneg_left (hD t ht0) hL'.le
      _ ≤ archLevyDensity t * (riemannKernelReal 0 * (C * Real.exp (16 * a)) *
            Real.exp (-(8 * L)) * 1 * t) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left he hK0) ht0.le) hL'.le
      _ = _ := by ring
  have hP : (∑' n : ℕ, vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n),
      reflectedDifferenceJump (shiftedGroundState a) u (Real.log n) x) ≤
      (riemannKernelReal 0 * (C * Real.exp (16 * a)) * Real.exp (-(8 * L))) *
        ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := by
    rw [← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun n => ?_)
      (summable_atom_mul_reflectedDifferenceIntegral ha hu huc)
      ((Real.summable_one_div_nat_pow.mpr (by norm_num)).mul_left _)
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      rw [vonMangoldtAtom_eq_zero_of_lt_two (by norm_num), zero_mul]
      positivity
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hlog0 : 0 ≤ Real.log n := Real.log_nonneg hn1
      have hΛlog := vonMangoldtAtom_le_log n
      have hlogn : Real.log n ≤ n := (Real.log_le_sub_one_of_pos hn0).trans (by linarith)
      rcases hlog0.lt_or_eq with hlog | hlog
      · have hDn := hD (Real.log n) hlog
        have hexp : Real.exp (-(4 * Real.log n)) = 1 / (n : ℝ) ^ 4 := by
          rw [Real.exp_neg, show (4 : ℝ) * Real.log n = ((4 : ℕ) : ℝ) * Real.log n by norm_num,
            Real.exp_nat_mul, Real.exp_log hn0, one_div]
        rw [hexp] at hDn
        have hn4 : (0 : ℝ) < (n : ℝ) ^ 4 := by positivity
        have hDn' : (∫ x in Ioo (0 : ℝ) (Real.log n),
            reflectedDifferenceJump (shiftedGroundState a) u (Real.log n) x) ≤
            riemannKernelReal 0 * (C * Real.exp (16 * a)) * Real.exp (-(8 * L)) *
              (1 / (n : ℝ) ^ 4) * n :=
          hDn.trans (mul_le_mul_of_nonneg_left hlogn (by positivity))
        calc vonMangoldtAtom n * ∫ x in Ioo (0 : ℝ) (Real.log n),
              reflectedDifferenceJump (shiftedGroundState a) u (Real.log n) x
            ≤ (n : ℝ) * (riemannKernelReal 0 * (C * Real.exp (16 * a)) * Real.exp (-(8 * L)) *
                (1 / (n : ℝ) ^ 4) * n) :=
              mul_le_mul (hΛlog.trans hlogn) hDn'
                (integral_reflectedDifference_shiftedGroundState_nonneg ha u _) hn0.le
          _ = _ := by
              field_simp
      · rw [← hlog, Set.Ioo_self, Measure.restrict_empty, integral_zero_measure, mul_zero]
        positivity
  unfold reflectedDifferenceEnergy
  linarith [hA, hP]

/-- **Plateau positivity of the shifted ground states.** For every shift `a > 0` there is `L₀`
such that for every `L ≥ L₀` and every even `u ∈ C²_c(ℝ)` with `0 ≤ u ≤ 1` and `u = 1` on
`[−L, L]`,

    markovEnergy(Φ(ω_a u)) ≥ sinh²(a/2) > 0. -/
theorem exists_plateau_markovEnergy_phiDoob_shiftedGroundState_ge {a : ℝ} (ha : 0 < a) :
    ∃ L₀ : ℝ, ∀ L, L₀ ≤ L → ∀ u : ℝ → ℝ, ContDiff ℝ 2 u → HasCompactSupport u →
      (∀ x, u (-x) = u x) → (∀ x, 0 ≤ u x) → (∀ x, u x ≤ 1) → (∀ x, |x| ≤ L → u x = 1) →
      Real.sinh (a / 2) ^ 2 ≤
        markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) := by
  obtain ⟨C, hC0, hC⟩ := exists_riemannKernelReal_le_exp_sixteen
  have hs : 0 < Real.sinh (a / 2) := Real.sinh_pos_iff.mpr (by positivity)
  have hΘ0 := (riemannKernelReal_pos 0).le
  have hArch : 0 ≤ ∫ t in Ioi (0 : ℝ), archLevyDensity t * t :=
    setIntegral_nonneg measurableSet_Ioi fun t ht => mul_nonneg (archLevyDensity_pos ht).le (le_of_lt ht)
  have hSum : 0 ≤ ∑' n : ℕ, 1 / (n : ℝ) ^ 2 := tsum_nonneg fun n => by positivity
  set K₁ : ℝ := riemannKernelReal 0 * (C * Real.exp (16 * a)) *
    ((∫ t in Ioi (0 : ℝ), archLevyDensity t * t) + ∑' n : ℕ, 1 / (n : ℝ) ^ 2) +
    4 * Real.sinh (a / 2) * (C * Real.exp (16 * a)) with hK₁
  have hK₁0 : 0 ≤ K₁ := by positivity
  have hs2 : 0 < Real.sinh (a / 2) ^ 2 := by positivity
  refine ⟨max 0 (Real.log (K₁ / Real.sinh (a / 2) ^ 2 + 1) / 8),
    fun L hL u hu huc heven hnn hle hone => ?_⟩
  have hL0 : 0 ≤ L := le_trans (le_max_left _ _) hL
  have hLlog : Real.log (K₁ / Real.sinh (a / 2) ^ 2 + 1) / 8 ≤ L := le_trans (le_max_right _ _) hL
  have hu1 : ContDiff ℝ 1 u := hu.of_le (by norm_num)
  have hexp : K₁ * Real.exp (-(8 * L)) ≤ Real.sinh (a / 2) ^ 2 := by
    have hpos : 0 < K₁ / Real.sinh (a / 2) ^ 2 + 1 := by positivity
    have h1 : Real.exp (-(8 * L)) ≤ (K₁ / Real.sinh (a / 2) ^ 2 + 1)⁻¹ := by
      rw [← Real.exp_log hpos, ← Real.exp_neg]
      exact Real.exp_le_exp.mpr (by linarith)
    have hden : 0 < K₁ + Real.sinh (a / 2) ^ 2 := by positivity
    have h2 : K₁ * (K₁ / Real.sinh (a / 2) ^ 2 + 1)⁻¹ ≤ Real.sinh (a / 2) ^ 2 := by
      rw [div_add_one hs2.ne', inv_div, ← sub_nonneg]
      have : Real.sinh (a / 2) ^ 2 - K₁ * (Real.sinh (a / 2) ^ 2 / (K₁ + Real.sinh (a / 2) ^ 2)) =
          Real.sinh (a / 2) ^ 2 * Real.sinh (a / 2) ^ 2 / (K₁ + Real.sinh (a / 2) ^ 2) := by
        field_simp
        ring
      rw [this]
      positivity
    calc K₁ * Real.exp (-(8 * L)) ≤ K₁ * (K₁ / Real.sinh (a / 2) ^ 2 + 1)⁻¹ :=
          mul_le_mul_of_nonneg_left h1 hK₁0
      _ ≤ _ := h2
  have hD := reflectedDifferenceEnergy_plateau_le hC0 hC ha hu1 huc hnn hle hone
  have hsrc := integral_sq_mul_shiftDifference_mul_sinh_ge hC0 hC ha hu.continuous huc hL0 hone
  have hS := sameSideEnergy_nonneg ha u
  have h4 := mul_le_mul_of_nonneg_left hsrc (by positivity : (0 : ℝ) ≤ 4 * Real.sinh (a / 2))
  have hKE : K₁ * Real.exp (-(8 * L)) =
      riemannKernelReal 0 * (C * Real.exp (16 * a)) *
        ((∫ t in Ioi (0 : ℝ), archLevyDensity t * t) + ∑' n : ℕ, 1 / (n : ℝ) ^ 2) *
        Real.exp (-(8 * L)) +
      4 * Real.sinh (a / 2) * (C * Real.exp (16 * a) * Real.exp (-(8 * L))) := by
    rw [hK₁]
    ring
  rw [markovEnergy_phiDoob_shiftedGroundState_eq_twoSided ha hu huc heven]
  nlinarith [hD, hS, h4, hexp, hKE]

end GaloisForLFunctions.ArithmeticCriticalityTheory

end
