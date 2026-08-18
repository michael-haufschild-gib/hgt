import GaloisForLFunctions.RHTower.CCMUnitRieszStirlingLaplace
import GaloisForLFunctions.RHTower.CCMComplexMellinColligation
import GaloisForLFunctions.RHTower.VonMangoldtLogMomentHankel
import GaloisForLFunctions.RHTower.XiMassCriticalErrorFlux

/-!
# The Laplace transform of the completed critical-Mellin current

The critically weighted completed error

```text
W(h) = exp(-h/2) E(h) = 2(1 - exp(-h)) - exp(-h/2) Σ_(k ≤ exp h) Λ(k)/√k
```

is bounded by `2(1+h)` on the positive ray, so its Laplace transform converges on the right
half-plane.  Splitting the prime staircase into its arithmetic atoms and integrating each one
exactly gives

```text
L[W](z) = 2/z - 2/(z+1) - LSeries Λ (1+z) / (z+1/2),      Re z > 0.
```

Unconditional; no zero-free input.
-/

open MeasureTheory Set Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- The critically weighted completed critical-Mellin current. -/
def unitRieszCompletedCurrent (h : ℝ) : ℝ :=
  Real.exp (-h / 2) * criticalMellinCompletedError h

/-- The critically weighted prime staircase. -/
def unitRieszPrimeCurrent (h : ℝ) : ℝ :=
  Real.exp (-h / 2) * criticalMellinPrimeMass h

private theorem exp_neg_half_mul_exp_half (h : ℝ) :
    Real.exp (-h / 2) * Real.exp (h / 2) = 1 := by
  rw [← Real.exp_add, show -h / 2 + h / 2 = (0 : ℝ) by ring, Real.exp_zero]

private theorem exp_neg_half_sq (h : ℝ) :
    Real.exp (-h / 2) * Real.exp (-(h / 2)) = Real.exp (-h) := by
  rw [← Real.exp_add]; congr 1; ring

theorem unitRieszCompletedCurrent_eq (h : ℝ) :
    unitRieszCompletedCurrent h = 2 * (1 - Real.exp (-h)) - unitRieszPrimeCurrent h := by
  rw [unitRieszCompletedCurrent, unitRieszPrimeCurrent,
    criticalMellinCompletedError_eq_polar_sub_primeMass, Real.sinh_eq]
  linear_combination (2 : ℝ) * exp_neg_half_mul_exp_half h - (2 : ℝ) * exp_neg_half_sq h

theorem measurable_criticalMellinPrimeMass : Measurable criticalMellinPrimeMass := by
  have h : criticalMellinPrimeMass =
      (fun N : ℕ => ∑ k ∈ Finset.Icc 0 N,
        ((k : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt k) ∘
          (fun h : ℝ => ⌊Real.exp h⌋₊) := rfl
  rw [h]
  exact measurable_from_top.comp (Nat.measurable_floor.comp Real.measurable_exp)

theorem measurable_criticalMellinCompletedError : Measurable criticalMellinCompletedError := by
  have h : criticalMellinCompletedError =
      fun s : ℝ => 4 * Real.sinh (s / 2) - criticalMellinPrimeMass s :=
    funext criticalMellinCompletedError_eq_polar_sub_primeMass
  rw [h]
  exact (measurable_const.mul (Real.measurable_sinh.comp (measurable_id.div_const 2))).sub
    measurable_criticalMellinPrimeMass

theorem measurable_unitRieszCompletedCurrent : Measurable unitRieszCompletedCurrent :=
  (Real.measurable_exp.comp (measurable_neg.div_const 2)).mul
    measurable_criticalMellinCompletedError

theorem abs_unitRieszCompletedCurrent_le {h : ℝ} (hh : 0 ≤ h) :
    |unitRieszCompletedCurrent h| ≤ 2 * (1 + h) := by
  have hE := abs_criticalMellinCompletedError_le_log_sqrt hh
  have hpos : (0 : ℝ) < Real.exp (-h / 2) := Real.exp_pos _
  have he := exp_neg_half_mul_exp_half h
  rw [unitRieszCompletedCurrent, abs_mul, abs_of_pos hpos]
  nlinarith [hE, hpos, he, abs_nonneg (criticalMellinCompletedError h)]

/-! ## The prime atoms -/

/-- The `r+1`-st arithmetic atom of the critically weighted prime staircase. -/
def unitRieszPrimeAtom (r : ℕ) (h : ℝ) : ℝ :=
  if Real.log ((r : ℝ) + 1) ≤ h then
    (((r : ℝ) + 1) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt (r + 1) *
      Real.exp (-h / 2)
  else 0

theorem unitRieszPrimeAtom_coefficient_nonneg (r : ℕ) :
    (0 : ℝ) ≤ (((r : ℝ) + 1) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt (r + 1) :=
  mul_nonneg (Real.rpow_nonneg (by positivity) _) ArithmeticFunction.vonMangoldt_nonneg

theorem unitRieszPrimeAtom_eq_of_le {r : ℕ} {h : ℝ} (hh : Real.log ((r : ℝ) + 1) ≤ h) :
    unitRieszPrimeAtom r h =
      (((r : ℝ) + 1) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt (r + 1) *
        Real.exp (-h / 2) := by
  rw [unitRieszPrimeAtom, if_pos hh]

theorem unitRieszPrimeAtom_eq_zero {r : ℕ} {h : ℝ} (hh : h < Real.log ((r : ℝ) + 1)) :
    unitRieszPrimeAtom r h = 0 := by
  rw [unitRieszPrimeAtom, if_neg (not_le.2 hh)]

theorem unitRieszPrimeAtom_nonneg (r : ℕ) (h : ℝ) : 0 ≤ unitRieszPrimeAtom r h := by
  rcases lt_or_ge h (Real.log ((r : ℝ) + 1)) with hh | hh
  · rw [unitRieszPrimeAtom_eq_zero hh]
  · rw [unitRieszPrimeAtom_eq_of_le hh]
    exact mul_nonneg (unitRieszPrimeAtom_coefficient_nonneg r) (Real.exp_pos _).le

theorem unitRieszPrimeCurrent_eq_tsum {h : ℝ} (hh : 0 ≤ h) :
    unitRieszPrimeCurrent h = ∑' r : ℕ, unitRieszPrimeAtom r h := by
  classical
  set N : ℕ := ⌊Real.exp h⌋₊ with hN
  have hMle : (N : ℝ) ≤ Real.exp h := Nat.floor_le (Real.exp_nonneg h)
  have hltM : Real.exp h < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsupp : ∀ r : ℕ, r ∉ Finset.range N → unitRieszPrimeAtom r h = 0 := by
    intro r hr
    have hrM : N ≤ r := by simpa using Finset.mem_range.not.1 hr
    have hlt : Real.exp h < (r : ℝ) + 1 := by
      have : (N : ℝ) + 1 ≤ (r : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hrM 1
      linarith
    refine unitRieszPrimeAtom_eq_zero ?_
    have hlog := Real.log_lt_log (Real.exp_pos h) hlt
    rwa [Real.log_exp] at hlog
  have hterm : ∀ r ∈ Finset.range N, unitRieszPrimeAtom r h =
      (((r : ℝ) + 1) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt (r + 1) *
        Real.exp (-h / 2) := by
    intro r hr
    refine unitRieszPrimeAtom_eq_of_le ?_
    have hrM : r + 1 ≤ N := Finset.mem_range.1 hr
    have hle : ((r : ℝ) + 1) ≤ Real.exp h := by
      have : ((r : ℝ) + 1) ≤ (N : ℝ) := by exact_mod_cast hrM
      linarith
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < (r : ℝ) + 1) hle
    rwa [Real.log_exp] at hlog
  have hsum : ∑' r : ℕ, unitRieszPrimeAtom r h =
      ∑ r ∈ Finset.range N, unitRieszPrimeAtom r h := tsum_eq_sum hsupp
  have hIcc : Finset.Icc 0 N = Finset.range (N + 1) := by
    ext k; simp
  have hzero : ((0 : ℝ) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt 0 = 0 := by
    simp
  have hmass : criticalMellinPrimeMass h =
      ∑ r ∈ Finset.range N,
        (((r : ℝ) + 1) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt (r + 1) := by
    rw [criticalMellinPrimeMass, ← hN, hIcc, Finset.sum_range_succ']
    simp only [Nat.cast_zero]
    rw [hzero, add_zero]
    refine Finset.sum_congr rfl ?_
    intro r _
    congr 2
    push_cast
    ring
  rw [hsum, Finset.sum_congr rfl hterm, unitRieszPrimeCurrent, hmass, ← Finset.sum_mul]
  ring


/-! ## Half-line splitting for atoms with a closed switch-on point -/

theorem integrableOn_Ioc_of_vanishing_Ioo {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {L : ℝ} {g : ℝ → E} (hzero : ∀ v, v < L → g v = 0) :
    IntegrableOn g (Ioc (0 : ℝ) L) volume := by
  have h : IntegrableOn g (Ioo (0 : ℝ) L) volume := by
    refine MeasureTheory.IntegrableOn.congr_fun integrableOn_zero ?_ measurableSet_Ioo
    intro v hv
    exact (hzero v hv.2).symm
  exact h.congr_set_ae Ioo_ae_eq_Ioc.symm

theorem setIntegral_Ioi_of_vanishing_lt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {L : ℝ} (hL : 0 ≤ L) {g : ℝ → E}
    (hzero : ∀ v, v < L → g v = 0) (hint : IntegrableOn g (Ioi L) volume) :
    ∫ v in Ioi (0 : ℝ), g v = ∫ v in Ioi L, g v := by
  have hintHead : IntegrableOn g (Ioc (0 : ℝ) L) volume :=
    integrableOn_Ioc_of_vanishing_Ioo hzero
  have hsplit : Ioi (0 : ℝ) = Ioc 0 L ∪ Ioi L := (Ioc_union_Ioi_eq_Ioi hL).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) L) (Ioi L) := Ioc_disjoint_Ioi le_rfl
  have hhead : ∫ v in Ioc (0 : ℝ) L, g v = 0 := by
    rw [← MeasureTheory.setIntegral_congr_set (Ioo_ae_eq_Ioc (a := (0 : ℝ)) (b := L)),
      setIntegral_congr_fun measurableSet_Ioo (fun v hv => hzero v hv.2)]
    simp
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioi hintHead hint, hhead, zero_add]

/-! ## The Laplace transform of the prime current -/

/-- The Laplace integrand of a single prime atom. -/
def unitRieszPrimeAtomIntegrand (z : ℂ) (r : ℕ) (h : ℝ) : ℂ :=
  Complex.exp (-(z * (h : ℂ))) * ((unitRieszPrimeAtom r h : ℝ) : ℂ)

theorem unitRieszPrimeAtomIntegrand_eq {z : ℂ} {r : ℕ} {h : ℝ}
    (hh : Real.log ((r : ℝ) + 1) ≤ h) :
    unitRieszPrimeAtomIntegrand z r h =
      (((((r : ℝ) + 1) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt (r + 1) : ℝ) : ℂ) *
        Complex.exp (-((z + 1 / 2) * (h : ℂ))) := by
  unfold unitRieszPrimeAtomIntegrand
  rw [unitRieszPrimeAtom_eq_of_le hh, Complex.ofReal_mul, Complex.ofReal_exp,
    show Complex.exp (-(z * (h : ℂ))) *
        ((((((r : ℝ) + 1) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt (r + 1) : ℝ) : ℂ) *
          Complex.exp (((-h / 2 : ℝ) : ℂ))) =
      (((((r : ℝ) + 1) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt (r + 1) : ℝ) : ℂ) *
        (Complex.exp (-(z * (h : ℂ))) * Complex.exp (((-h / 2 : ℝ) : ℂ))) from by ring]
  congr 1
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem unitRieszPrimeAtomIntegrand_eq_zero {z : ℂ} {r : ℕ} {h : ℝ}
    (hh : h < Real.log ((r : ℝ) + 1)) : unitRieszPrimeAtomIntegrand z r h = 0 := by
  unfold unitRieszPrimeAtomIntegrand
  rw [unitRieszPrimeAtom_eq_zero hh]
  simp

theorem unitRieszPrime_shift_re {z : ℂ} (hz : 0 < z.re) : 0 < (z + 1 / 2).re := by
  have h12 : ((1 : ℂ) / 2).re = 1 / 2 := by norm_num
  simp only [Complex.add_re, h12]
  linarith

theorem integrableOn_Ioi_log_unitRieszPrimeAtomIntegrand {z : ℂ} (hz : 0 < z.re) (r : ℕ) :
    IntegrableOn (unitRieszPrimeAtomIntegrand z r)
      (Ioi (Real.log ((r : ℝ) + 1))) volume := by
  have hL0 : 0 ≤ Real.log ((r : ℝ) + 1) := log_natCast_add_one_nonneg r
  refine MeasureTheory.IntegrableOn.congr_fun
    ((integrableOn_Ioi_cexp_neg_mul_shift (unitRieszPrime_shift_re hz) hL0).const_mul
      (((((r : ℝ) + 1) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt (r + 1) : ℝ) : ℂ))
    ?_ measurableSet_Ioi
  intro v hv
  exact (unitRieszPrimeAtomIntegrand_eq (le_of_lt hv)).symm

theorem integrableOn_unitRieszPrimeAtomIntegrand {z : ℂ} (hz : 0 < z.re) (r : ℕ) :
    IntegrableOn (unitRieszPrimeAtomIntegrand z r) (Ioi (0 : ℝ)) volume := by
  have hL0 : 0 ≤ Real.log ((r : ℝ) + 1) := log_natCast_add_one_nonneg r
  have hintHead : IntegrableOn (unitRieszPrimeAtomIntegrand z r)
      (Ioc (0 : ℝ) (Real.log ((r : ℝ) + 1))) volume :=
    integrableOn_Ioc_of_vanishing_Ioo
      (fun v hv => unitRieszPrimeAtomIntegrand_eq_zero hv)
  have hun := hintHead.union (integrableOn_Ioi_log_unitRieszPrimeAtomIntegrand hz r)
  rwa [Ioc_union_Ioi_eq_Ioi hL0] at hun

theorem integral_unitRieszPrimeAtomIntegrand {z : ℂ} (hz : 0 < z.re) (r : ℕ) :
    (∫ h in Ioi (0 : ℝ), unitRieszPrimeAtomIntegrand z r h) =
      (((((r : ℝ) + 1) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt (r + 1) : ℝ) : ℂ) *
        (Complex.exp (-((z + 1 / 2) * ((Real.log ((r : ℝ) + 1) : ℝ) : ℂ))) / (z + 1 / 2)) := by
  have hL0 : 0 ≤ Real.log ((r : ℝ) + 1) := log_natCast_add_one_nonneg r
  rw [setIntegral_Ioi_of_vanishing_lt hL0
      (fun v hv => unitRieszPrimeAtomIntegrand_eq_zero hv)
      (integrableOn_Ioi_log_unitRieszPrimeAtomIntegrand hz r),
    setIntegral_congr_fun measurableSet_Ioi
      (fun v hv => unitRieszPrimeAtomIntegrand_eq (le_of_lt hv)),
    MeasureTheory.integral_const_mul,
    integral_Ioi_cexp_neg_mul_shift (unitRieszPrime_shift_re hz) _]

theorem integral_norm_unitRieszPrimeAtomIntegrand {z : ℂ} (hz : 0 < z.re) (r : ℕ) :
    (∫ h in Ioi (0 : ℝ), ‖unitRieszPrimeAtomIntegrand z r h‖) =
      ((((r : ℝ) + 1) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt (r + 1)) *
        (Real.exp (-((z.re + 1 / 2) * Real.log ((r : ℝ) + 1))) / (z.re + 1 / 2)) := by
  have hL0 : 0 ≤ Real.log ((r : ℝ) + 1) := log_natCast_add_one_nonneg r
  have hb : (0 : ℝ) < z.re + 1 / 2 := by linarith
  have hzero : ∀ v : ℝ, v < Real.log ((r : ℝ) + 1) →
      ‖unitRieszPrimeAtomIntegrand z r v‖ = 0 := by
    intro v hv
    rw [unitRieszPrimeAtomIntegrand_eq_zero hv, norm_zero]
  have hintNorm : IntegrableOn (fun v => ‖unitRieszPrimeAtomIntegrand z r v‖)
      (Ioi (Real.log ((r : ℝ) + 1))) volume :=
    (integrableOn_Ioi_log_unitRieszPrimeAtomIntegrand hz r).norm
  rw [setIntegral_Ioi_of_vanishing_lt (E := ℝ) hL0 hzero hintNorm]
  have hpt : ∀ v : ℝ, v ∈ Ioi (Real.log ((r : ℝ) + 1)) →
      ‖unitRieszPrimeAtomIntegrand z r v‖ =
        ((((r : ℝ) + 1) ^ (-1 / 2 : ℝ)) * ArithmeticFunction.vonMangoldt (r + 1)) *
          Real.exp (-((z.re + 1 / 2) * v)) := by
    intro v hv
    rw [unitRieszPrimeAtomIntegrand_eq (le_of_lt hv), norm_mul, Complex.norm_real,
      Complex.norm_exp, Real.norm_eq_abs,
      abs_of_nonneg (unitRieszPrimeAtom_coefficient_nonneg r)]
    congr 2
    simp [Complex.mul_re, Complex.add_re, Complex.add_im]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, MeasureTheory.integral_const_mul,
    integral_Ioi_rexp_neg_mul_shift hb _]

/-! ## Summability and the transform -/

theorem summable_integral_norm_unitRieszPrimeAtomIntegrand {z : ℂ} (hz : 0 < z.re) :
    Summable (fun r : ℕ => ∫ h in Ioi (0 : ℝ), ‖unitRieszPrimeAtomIntegrand z r h‖) := by
  have hσ : (1 : ℝ) < 1 + z.re := by linarith
  have hbase : Summable (fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (-(1 + z.re))) :=
    _root_.RHTower.summable_vonMangoldt_rpow hσ
  have hshift : Summable (fun r : ℕ =>
      (ArithmeticFunction.vonMangoldt (r + 1) : ℝ) * ((r : ℝ) + 1) ^ (-(1 + z.re))) := by
    have h := (summable_nat_add_iff 1).2 hbase
    refine h.congr fun r => ?_
    congr 2
    push_cast
    ring
  refine (hshift.div_const (z.re + 1 / 2)).congr fun r => ?_
  rw [integral_norm_unitRieszPrimeAtomIntegrand hz r]
  have hpos : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hrpow : Real.exp (-((z.re + 1 / 2) * Real.log ((r : ℝ) + 1))) =
      ((r : ℝ) + 1) ^ (-(z.re + 1 / 2)) := by
    rw [Real.rpow_def_of_pos hpos]
    congr 1
    ring
  have hmul : (((r : ℝ) + 1) ^ (-1 / 2 : ℝ)) * ((r : ℝ) + 1) ^ (-(z.re + 1 / 2)) =
      ((r : ℝ) + 1) ^ (-(1 + z.re)) := by
    rw [← Real.rpow_add hpos]
    congr 1
    ring
  rw [hrpow]
  linear_combination
    (-((ArithmeticFunction.vonMangoldt (r + 1) : ℝ) / (z.re + 1 / 2))) * hmul

theorem tsum_unitRieszPrimeAtomIntegrand {z : ℂ} {h : ℝ} (hh : 0 ≤ h) :
    ∑' r : ℕ, unitRieszPrimeAtomIntegrand z r h =
      Complex.exp (-(z * (h : ℂ))) * ((unitRieszPrimeCurrent h : ℝ) : ℂ) := by
  classical
  set N : ℕ := ⌊Real.exp h⌋₊ with hN
  have hsupp : ∀ r : ℕ, r ∉ Finset.range N → unitRieszPrimeAtom r h = 0 := by
    intro r hr
    have hrM : N ≤ r := by simpa using Finset.mem_range.not.1 hr
    have hMle : (N : ℝ) ≤ Real.exp h := Nat.floor_le (Real.exp_nonneg h)
    have hltM : Real.exp h < (N : ℝ) + 1 := Nat.lt_floor_add_one _
    have hlt : Real.exp h < (r : ℝ) + 1 := by
      have : (N : ℝ) + 1 ≤ (r : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hrM 1
      linarith
    refine unitRieszPrimeAtom_eq_zero ?_
    have hlog := Real.log_lt_log (Real.exp_pos h) hlt
    rwa [Real.log_exp] at hlog
  have hsr : Summable (fun r : ℕ => unitRieszPrimeAtom r h) :=
    summable_of_ne_finset_zero (s := Finset.range N) hsupp
  have hpull : ∑' r : ℕ, unitRieszPrimeAtomIntegrand z r h =
      Complex.exp (-(z * (h : ℂ))) * ∑' r : ℕ, ((unitRieszPrimeAtom r h : ℝ) : ℂ) := by
    unfold unitRieszPrimeAtomIntegrand
    exact tsum_mul_left
  have hreal : ∑' r : ℕ, ((unitRieszPrimeAtom r h : ℝ) : ℂ) =
      ((∑' r : ℕ, unitRieszPrimeAtom r h : ℝ) : ℂ) :=
    (Complex.ofRealCLM.map_tsum hsr).symm
  rw [hpull, hreal, ← unitRieszPrimeCurrent_eq_tsum hh]

theorem integral_unitRieszPrimeAtomIntegrand_eq_term {z : ℂ} (hz : 0 < z.re) (r : ℕ) :
    (∫ h in Ioi (0 : ℝ), unitRieszPrimeAtomIntegrand z r h) =
      LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 + z) (r + 1) *
        (z + 1 / 2)⁻¹ := by
  have hposR : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  have hcast : ((r : ℂ) + 1) = (((r : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  have hne : ((r : ℂ) + 1) ≠ 0 := by
    rw [hcast]
    simp only [ne_eq, Complex.ofReal_eq_zero]
    positivity
  have hnat : (((r + 1 : ℕ) : ℂ)) = (r : ℂ) + 1 := by push_cast; ring
  have hlog : Complex.log ((r : ℂ) + 1) = ((Real.log ((r : ℝ) + 1) : ℝ) : ℂ) := by
    rw [hcast, ← Complex.ofReal_log hposR.le]
  have hexp : Complex.exp (-((z + 1 / 2) * ((Real.log ((r : ℝ) + 1) : ℝ) : ℂ))) =
      ((r : ℂ) + 1) ^ (-(z + 1 / 2)) := by
    rw [Complex.cpow_def_of_ne_zero hne, hlog]
    congr 1
    ring
  have hhalf : ((((r : ℝ) + 1) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) =
      ((r : ℂ) + 1) ^ (((-1 / 2 : ℝ) : ℂ)) := by
    rw [hcast, Complex.ofReal_cpow hposR.le]
  have hcomb : ((r : ℂ) + 1) ^ (((-1 / 2 : ℝ) : ℂ)) * ((r : ℂ) + 1) ^ (-(z + 1 / 2)) =
      ((r : ℂ) + 1) ^ (-(1 + z)) := by
    rw [← Complex.cpow_add _ _ hne]
    congr 1
    push_cast
    ring
  rw [integral_unitRieszPrimeAtomIntegrand hz r,
    LSeries.term_of_ne_zero (by omega : r + 1 ≠ 0), hnat, Complex.ofReal_mul]
  calc ((((r : ℝ) + 1) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
        ((ArithmeticFunction.vonMangoldt (r + 1) : ℝ) : ℂ) *
        (Complex.exp (-((z + 1 / 2) * ((Real.log ((r : ℝ) + 1) : ℝ) : ℂ))) / (z + 1 / 2))
      = ((ArithmeticFunction.vonMangoldt (r + 1) : ℝ) : ℂ) *
          (((((r : ℝ) + 1) ^ (-1 / 2 : ℝ) : ℝ) : ℂ) *
            Complex.exp (-((z + 1 / 2) * ((Real.log ((r : ℝ) + 1) : ℝ) : ℂ)))) *
          (z + 1 / 2)⁻¹ := by
        rw [div_eq_mul_inv]; ring
    _ = ((ArithmeticFunction.vonMangoldt (r + 1) : ℝ) : ℂ) *
          (((r : ℂ) + 1) ^ (-(1 + z)) : ℂ) * (z + 1 / 2)⁻¹ := by
        rw [hhalf, hexp, hcomb]
    _ = ((ArithmeticFunction.vonMangoldt (r + 1) : ℝ) : ℂ) /
          ((r : ℂ) + 1) ^ (1 + z) * (z + 1 / 2)⁻¹ := by
        rw [Complex.cpow_neg]; ring

/-- **The prime current transforms to the von Mangoldt Dirichlet series.** -/
theorem unitRieszPrimeCurrent_laplace {z : ℂ} (hz : 0 < z.re) :
    (∫ h in Ioi (0 : ℝ), Complex.exp (-(z * (h : ℂ))) * ((unitRieszPrimeCurrent h : ℝ) : ℂ)) =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 + z) / (z + 1 / 2) := by
  have hswap := integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun r : ℕ => unitRieszPrimeAtomIntegrand z r)
    (fun r => integrableOn_unitRieszPrimeAtomIntegrand hz r)
    (summable_integral_norm_unitRieszPrimeAtomIntegrand hz)
  have hpt : (∫ h in Ioi (0 : ℝ), ∑' r : ℕ, unitRieszPrimeAtomIntegrand z r h) =
      ∫ h in Ioi (0 : ℝ), Complex.exp (-(z * (h : ℂ))) *
        ((unitRieszPrimeCurrent h : ℝ) : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi
      (fun h hh => tsum_unitRieszPrimeAtomIntegrand (le_of_lt hh))
  have hsummable : Summable
      (LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 + z)) := by
    refine ArithmeticFunction.LSeriesSummable_vonMangoldt ?_
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hLS : LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 + z) =
      ∑' r : ℕ,
        LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 + z) (r + 1) := by
    rw [LSeries, hsummable.tsum_eq_zero_add, LSeries.term_zero, zero_add]
  have hsum : ∑' r : ℕ, (∫ h in Ioi (0 : ℝ), unitRieszPrimeAtomIntegrand z r h) =
      LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 + z) * (z + 1 / 2)⁻¹ := by
    rw [tsum_congr (integral_unitRieszPrimeAtomIntegrand_eq_term hz), tsum_mul_right, ← hLS]
  rw [hpt] at hswap
  rw [← hswap, hsum]
  ring

/-! ## The completed-current transform -/

theorem integrableOn_Ioi_linear_exp {C σ : ℝ} (hσ : 0 < σ) :
    IntegrableOn (fun h : ℝ => |C| * ((1 + h) * Real.exp (-(σ * h)))) (Ioi (0 : ℝ)) volume := by
  have h := integrableOn_Ioi_linear_exp_majorant (C := C) (σ := 2 * σ) (by linarith)
  simpa [show (2 : ℝ) * σ / 2 = σ from by ring] using h

theorem integrableOn_cexp_mul_of_linear_bound {z : ℂ} (hz : 0 < z.re) {φ : ℝ → ℝ} {C : ℝ}
    (hφ : Measurable φ) (hbnd : ∀ h : ℝ, 0 < h → |φ h| ≤ C * (1 + h)) :
    IntegrableOn (fun h : ℝ => Complex.exp (-(z * (h : ℂ))) * ((φ h : ℝ) : ℂ))
      (Ioi (0 : ℝ)) volume := by
  refine Integrable.mono' (integrableOn_Ioi_linear_exp (C := C) hz) ?_ ?_
  · exact ((Complex.measurable_exp.comp
      (measurable_const.mul Complex.measurable_ofReal).neg).mul
      (Complex.measurable_ofReal.comp hφ)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with h hh
    have hh0 : (0 : ℝ) < h := hh
    rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs]
    have hre : (-(z * (h : ℂ))).re = -(z.re * h) := by simp [Complex.mul_re]
    rw [hre]
    have hbC : |φ h| ≤ |C| * (1 + h) :=
      le_trans (hbnd h hh0) (by nlinarith [le_abs_self C])
    have hpos : (0 : ℝ) < Real.exp (-(z.re * h)) := Real.exp_pos _
    nlinarith [hbC, hpos]

theorem measurable_unitRieszPrimeCurrent : Measurable unitRieszPrimeCurrent :=
  (Real.measurable_exp.comp (measurable_neg.div_const 2)).mul measurable_criticalMellinPrimeMass

theorem abs_unitRieszPrimeCurrent_le {h : ℝ} (hh : 0 ≤ h) :
    |unitRieszPrimeCurrent h| ≤ 4 * (1 + h) := by
  have hW := abs_unitRieszCompletedCurrent_le hh
  have heq := unitRieszCompletedCurrent_eq h
  have he0 : (0 : ℝ) < Real.exp (-h) := Real.exp_pos _
  have he1 : Real.exp (-h) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  rw [abs_le] at hW ⊢
  constructor <;> nlinarith [hW.1, hW.2]

/-- **The exact Laplace transform of the completed critical-Mellin current.** -/
theorem unitRieszCompletedCurrent_laplace {z : ℂ} (hz : 0 < z.re) :
    (∫ h in Ioi (0 : ℝ),
        Complex.exp (-(z * (h : ℂ))) * ((unitRieszCompletedCurrent h : ℝ) : ℂ)) =
      2 / z - 2 / (z + 1) -
        LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) (1 + z) / (z + 1 / 2) := by
  have hA := integrableOn_cexp_mul_one hz
  have hB := integrableOn_cexp_mul_exp_neg hz
  have hP := integrableOn_cexp_mul_of_linear_bound hz measurable_unitRieszPrimeCurrent
    (fun h hh => abs_unitRieszPrimeCurrent_le hh.le)
  have hpt : ∀ h ∈ Ioi (0 : ℝ),
      Complex.exp (-(z * (h : ℂ))) * ((unitRieszCompletedCurrent h : ℝ) : ℂ) =
        (2 * (Complex.exp (-(z * (h : ℂ))) * ((1 : ℝ) : ℂ)) -
            2 * (Complex.exp (-(z * (h : ℂ))) * ((Real.exp (-h) : ℝ) : ℂ))) -
          Complex.exp (-(z * (h : ℂ))) * ((unitRieszPrimeCurrent h : ℝ) : ℂ) := by
    intro h _
    rw [unitRieszCompletedCurrent_eq]
    push_cast
    ring
  have hA2 : IntegrableOn
      (fun h : ℝ => 2 * (Complex.exp (-(z * (h : ℂ))) * ((1 : ℝ) : ℂ)))
      (Ioi (0 : ℝ)) volume := hA.const_mul 2
  have hB2 : IntegrableOn
      (fun h : ℝ => 2 * (Complex.exp (-(z * (h : ℂ))) * ((Real.exp (-h) : ℝ) : ℂ)))
      (Ioi (0 : ℝ)) volume := hB.const_mul 2
  have hAB : IntegrableOn
      (fun h : ℝ => 2 * (Complex.exp (-(z * (h : ℂ))) * ((1 : ℝ) : ℂ)) -
        2 * (Complex.exp (-(z * (h : ℂ))) * ((Real.exp (-h) : ℝ) : ℂ)))
      (Ioi (0 : ℝ)) volume := hA2.sub hB2
  rw [setIntegral_congr_fun measurableSet_Ioi hpt, integral_sub hAB hP,
    integral_sub hA2 hB2, MeasureTheory.integral_const_mul,
    MeasureTheory.integral_const_mul, integral_cexp_mul_one hz,
    integral_cexp_mul_exp_neg hz, unitRieszPrimeCurrent_laplace hz]
  ring

end GaloisForLFunctions.RHTower
