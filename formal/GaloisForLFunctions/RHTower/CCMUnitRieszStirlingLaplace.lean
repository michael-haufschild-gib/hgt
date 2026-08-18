import GaloisForLFunctions.RHTower.CCMUnitRieszVolterraLaplace
import GaloisForLFunctions.RHTower.CCMUnitRieszCompletedSourceWeld

/-!
# The Laplace transform of the unit-Riesz Stirling correction

The source-free correction of the unit-Riesz completed-source weld is the finite-floor Stirling
defect

```text
a(t) = exp(-t) [ N(t) t - log(N(t)!) ] - 1 - exp(-t),   N(t) = floor(exp t).
```

Its positive head `exp(-t) Σ_{n ≤ exp t} (t - log n)` is a sum of logarithmic atoms, one per
integer, switched on at `t = log n`, and each atom integrates in closed form against the Laplace
kernel.  Summing the resulting Dirichlet series gives

```text
L[a](z) = zeta(1+z)/(1+z)^2 - 1/z - 1/(z+1),     Re z > 0,
```

which is exactly the source-free factor `A` of the completed-source weld.

Unconditional; no zero-free input.
-/

open MeasureTheory Set Filter Topology Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-! ## The Stirling head and its atoms -/

/-- Positive head of the Stirling correction. -/
def unitRieszStirlingHead (t : ℝ) : ℝ :=
  Real.exp (-t) * ((⌊Real.exp t⌋₊ : ℝ) * t - unitRieszStirlingLogHead t)

theorem unitRieszStirlingCorrection_eq_head (t : ℝ) :
    unitRieszStirlingCorrection t = unitRieszStirlingHead t - 1 - Real.exp (-t) := by
  rw [unitRieszStirlingCorrection, unitRieszStirlingHead]

/-- The `r+1`-st logarithmic atom of the Stirling head. -/
def unitRieszStirlingAtom (r : ℕ) (t : ℝ) : ℝ :=
  if Real.log ((r : ℝ) + 1) ≤ t then Real.exp (-t) * (t - Real.log ((r : ℝ) + 1)) else 0

theorem unitRieszStirlingAtom_eq_of_le {r : ℕ} {t : ℝ} (ht : Real.log ((r : ℝ) + 1) ≤ t) :
    unitRieszStirlingAtom r t = Real.exp (-t) * (t - Real.log ((r : ℝ) + 1)) := by
  rw [unitRieszStirlingAtom, if_pos ht]

theorem unitRieszStirlingAtom_eq_zero {r : ℕ} {t : ℝ} (ht : t < Real.log ((r : ℝ) + 1)) :
    unitRieszStirlingAtom r t = 0 := by
  rw [unitRieszStirlingAtom, if_neg (not_le.2 ht)]

theorem unitRieszStirlingAtom_nonneg (r : ℕ) (t : ℝ) : 0 ≤ unitRieszStirlingAtom r t := by
  rcases lt_or_ge t (Real.log ((r : ℝ) + 1)) with h | h
  · rw [unitRieszStirlingAtom_eq_zero h]
  · rw [unitRieszStirlingAtom_eq_of_le h]
    have : (0 : ℝ) ≤ t - Real.log ((r : ℝ) + 1) := by linarith
    positivity

theorem unitRieszStirlingHead_eq_tsum {t : ℝ} (ht : 0 ≤ t) :
    unitRieszStirlingHead t = ∑' r : ℕ, unitRieszStirlingAtom r t := by
  classical
  set N : ℕ := ⌊Real.exp t⌋₊ with hN
  have hMle : (N : ℝ) ≤ Real.exp t := Nat.floor_le (Real.exp_nonneg t)
  have hltM : Real.exp t < (N : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsupp : ∀ r : ℕ, r ∉ Finset.range N → unitRieszStirlingAtom r t = 0 := by
    intro r hr
    have hrM : N ≤ r := by simpa using Finset.mem_range.not.1 hr
    have hlt : Real.exp t < (r : ℝ) + 1 := by
      have : (N : ℝ) + 1 ≤ (r : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hrM 1
      linarith
    refine unitRieszStirlingAtom_eq_zero ?_
    have hlog := Real.log_lt_log (Real.exp_pos t) hlt
    rwa [Real.log_exp] at hlog
  have hterm : ∀ r ∈ Finset.range N,
      unitRieszStirlingAtom r t = Real.exp (-t) * (t - Real.log ((r : ℝ) + 1)) := by
    intro r hr
    refine unitRieszStirlingAtom_eq_of_le ?_
    have hrM : r + 1 ≤ N := Finset.mem_range.1 hr
    have hle : ((r : ℝ) + 1) ≤ Real.exp t := by
      have : ((r : ℝ) + 1) ≤ (N : ℝ) := by exact_mod_cast hrM
      linarith
    have hpos : (0 : ℝ) < (r : ℝ) + 1 := by positivity
    have hlog := Real.log_le_log hpos hle
    rwa [Real.log_exp] at hlog
  have hsum : ∑' r : ℕ, unitRieszStirlingAtom r t =
      ∑ r ∈ Finset.range N, unitRieszStirlingAtom r t := tsum_eq_sum hsupp
  have hreindex : unitRieszStirlingLogHead t = ∑ r ∈ Finset.range N, Real.log ((r : ℝ) + 1) := by
    rw [unitRieszStirlingLogHead, ← hN, ← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl ?_
    intro r _
    congr 1
    push_cast
    ring
  rw [hsum, Finset.sum_congr rfl hterm, unitRieszStirlingHead, hreindex, ← Finset.mul_sum,
    Finset.sum_sub_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← hN]

/-! ## Measurability and elementary bounds -/

theorem measurable_unitRieszStirlingLogHead : Measurable unitRieszStirlingLogHead := by
  have h : unitRieszStirlingLogHead =
      (fun k : ℕ => ∑ n ∈ Finset.Icc 1 k, Real.log n) ∘ (fun t : ℝ => ⌊Real.exp t⌋₊) := rfl
  rw [h]
  exact measurable_from_top.comp (Nat.measurable_floor.comp Real.measurable_exp)

theorem measurable_unitRieszStirlingHead : Measurable unitRieszStirlingHead := by
  have hfloor : Measurable fun t : ℝ => ((⌊Real.exp t⌋₊ : ℕ) : ℝ) :=
    measurable_from_top.comp (Nat.measurable_floor.comp Real.measurable_exp)
  exact (Real.measurable_exp.comp measurable_neg).mul
    ((hfloor.mul measurable_id).sub measurable_unitRieszStirlingLogHead)

theorem measurable_unitRieszStirlingCorrection : Measurable unitRieszStirlingCorrection := by
  have h : unitRieszStirlingCorrection =
      fun t => unitRieszStirlingHead t - 1 - Real.exp (-t) :=
    funext unitRieszStirlingCorrection_eq_head
  rw [h]
  exact (measurable_unitRieszStirlingHead.sub measurable_const).sub
    (Real.measurable_exp.comp measurable_neg)

theorem unitRieszStirlingHead_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ unitRieszStirlingHead t := by
  rw [unitRieszStirlingHead_eq_tsum ht]
  exact tsum_nonneg fun r => unitRieszStirlingAtom_nonneg r t

theorem unitRieszStirlingHead_le_one {t : ℝ} (ht : 0 ≤ t) : unitRieszStirlingHead t ≤ 1 := by
  have h := unitRieszStirlingCorrection_le ht
  rw [unitRieszStirlingCorrection_eq_head] at h
  have hpos : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  linarith

theorem abs_unitRieszStirlingCorrection_le {t : ℝ} (ht : 0 ≤ t) :
    |unitRieszStirlingCorrection t| ≤ 4 * (1 + t) := by
  have h1 := unitRieszStirlingCorrection_le ht
  have h2 := unitRieszStirlingCorrection_lower ht
  have he : Real.exp (-t) ≤ 1 := by
    rw [Real.exp_le_one_iff]; linarith
  have he0 : (0 : ℝ) < Real.exp (-t) := Real.exp_pos _
  rw [abs_le]
  constructor <;> nlinarith

/-! ## The Laplace transform of the Stirling head -/

theorem unitRieszStirlingAtom_eq_zero_of_le {r : ℕ} {t : ℝ}
    (ht : t ≤ Real.log ((r : ℝ) + 1)) : unitRieszStirlingAtom r t = 0 := by
  rcases lt_or_eq_of_le ht with h | h
  · exact unitRieszStirlingAtom_eq_zero h
  · rw [unitRieszStirlingAtom_eq_of_le h.ge, h]
    ring

/-- The Laplace integrand of a single Stirling atom. -/
def unitRieszStirlingAtomIntegrand (z : ℂ) (r : ℕ) (t : ℝ) : ℂ :=
  Complex.exp (-(z * (t : ℂ))) * ((unitRieszStirlingAtom r t : ℝ) : ℂ)

theorem unitRieszStirlingAtomIntegrand_eq {z : ℂ} {r : ℕ} {t : ℝ}
    (ht : Real.log ((r : ℝ) + 1) ≤ t) :
    unitRieszStirlingAtomIntegrand z r t =
      Complex.exp (-((z + 1) * (t : ℂ))) * ((t - Real.log ((r : ℝ) + 1) : ℝ) : ℂ) := by
  unfold unitRieszStirlingAtomIntegrand
  rw [unitRieszStirlingAtom_eq_of_le ht, Complex.ofReal_mul, Complex.ofReal_exp,
    show Complex.exp (-(z * (t : ℂ))) *
        (Complex.exp (((-t : ℝ) : ℂ)) * ((t - Real.log ((r : ℝ) + 1) : ℝ) : ℂ)) =
      (Complex.exp (-(z * (t : ℂ))) * Complex.exp (((-t : ℝ) : ℂ))) *
        ((t - Real.log ((r : ℝ) + 1) : ℝ) : ℂ) from by ring]
  congr 1
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integrableOn_Ioi_log_unitRieszStirlingAtomIntegrand {z : ℂ} (hz : 0 < z.re) (r : ℕ) :
    IntegrableOn (unitRieszStirlingAtomIntegrand z r)
      (Ioi (Real.log ((r : ℝ) + 1))) volume := by
  have hL0 : 0 ≤ Real.log ((r : ℝ) + 1) := log_natCast_add_one_nonneg r
  have hb1 : 0 < (z + 1).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  refine MeasureTheory.IntegrableOn.congr_fun
    (integrableOn_Ioi_cexp_neg_mul_linear_shift hb1 hL0) ?_ measurableSet_Ioi
  intro v hv
  exact (unitRieszStirlingAtomIntegrand_eq (le_of_lt hv)).symm

theorem integrableOn_unitRieszStirlingAtomIntegrand {z : ℂ} (hz : 0 < z.re) (r : ℕ) :
    IntegrableOn (unitRieszStirlingAtomIntegrand z r) (Ioi (0 : ℝ)) volume := by
  have hL0 : 0 ≤ Real.log ((r : ℝ) + 1) := log_natCast_add_one_nonneg r
  have hintHead : IntegrableOn (unitRieszStirlingAtomIntegrand z r)
      (Ioc (0 : ℝ) (Real.log ((r : ℝ) + 1))) volume := by
    have hz0 : IntegrableOn (fun _ : ℝ => (0 : ℂ))
        (Ioc (0 : ℝ) (Real.log ((r : ℝ) + 1))) volume := integrableOn_zero
    refine MeasureTheory.IntegrableOn.congr_fun hz0 ?_ measurableSet_Ioc
    intro v hv
    unfold unitRieszStirlingAtomIntegrand
    rw [unitRieszStirlingAtom_eq_zero_of_le hv.2]
    simp
  have hun := hintHead.union (integrableOn_Ioi_log_unitRieszStirlingAtomIntegrand hz r)
  rwa [Ioc_union_Ioi_eq_Ioi hL0] at hun

theorem integral_unitRieszStirlingAtomIntegrand {z : ℂ} (hz : 0 < z.re) (r : ℕ) :
    (∫ t in Ioi (0 : ℝ), unitRieszStirlingAtomIntegrand z r t) =
      Complex.exp (-((z + 1) * ((Real.log ((r : ℝ) + 1) : ℝ) : ℂ))) / (z + 1) ^ 2 := by
  have hL0 : 0 ≤ Real.log ((r : ℝ) + 1) := log_natCast_add_one_nonneg r
  have hb1 : 0 < (z + 1).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hzero : ∀ v : ℝ, v ≤ Real.log ((r : ℝ) + 1) →
      unitRieszStirlingAtomIntegrand z r v = 0 := by
    intro v hv
    unfold unitRieszStirlingAtomIntegrand
    rw [unitRieszStirlingAtom_eq_zero_of_le hv]
    simp
  rw [setIntegral_Ioi_of_vanishing hL0 hzero
      (integrableOn_Ioi_log_unitRieszStirlingAtomIntegrand hz r),
    setIntegral_congr_fun measurableSet_Ioi
      (fun v hv => unitRieszStirlingAtomIntegrand_eq (le_of_lt hv))]
  exact integral_Ioi_cexp_neg_mul_linear_shift hb1 _

theorem integral_norm_unitRieszStirlingAtomIntegrand {z : ℂ} (hz : 0 < z.re) (r : ℕ) :
    (∫ t in Ioi (0 : ℝ), ‖unitRieszStirlingAtomIntegrand z r t‖) =
      Real.exp (-((z.re + 1) * Real.log ((r : ℝ) + 1))) / (z.re + 1) ^ 2 := by
  have hL0 : 0 ≤ Real.log ((r : ℝ) + 1) := log_natCast_add_one_nonneg r
  have hb1 : (0 : ℝ) < z.re + 1 := by linarith
  have hzero : ∀ v : ℝ, v ≤ Real.log ((r : ℝ) + 1) →
      ‖unitRieszStirlingAtomIntegrand z r v‖ = 0 := by
    intro v hv
    unfold unitRieszStirlingAtomIntegrand
    rw [unitRieszStirlingAtom_eq_zero_of_le hv]
    simp
  have hintNorm : IntegrableOn (fun v => ‖unitRieszStirlingAtomIntegrand z r v‖)
      (Ioi (Real.log ((r : ℝ) + 1))) volume :=
    (integrableOn_Ioi_log_unitRieszStirlingAtomIntegrand hz r).norm
  rw [setIntegral_Ioi_of_vanishing (E := ℝ) hL0 hzero hintNorm]
  have hpt : ∀ v : ℝ, v ∈ Ioi (Real.log ((r : ℝ) + 1)) →
      ‖unitRieszStirlingAtomIntegrand z r v‖ =
        Real.exp (-((z.re + 1) * v)) * (v - Real.log ((r : ℝ) + 1)) := by
    intro v hv
    have hvlt : Real.log ((r : ℝ) + 1) < v := hv
    rw [unitRieszStirlingAtomIntegrand_eq (le_of_lt hvlt), norm_mul, Complex.norm_exp,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ v - Real.log ((r : ℝ) + 1))]
    congr 2
    simp [Complex.mul_re, Complex.add_re, Complex.add_im]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_Ioi_rexp_neg_mul_linear_shift hb1 _]

theorem summable_integral_norm_unitRieszStirlingAtomIntegrand {z : ℂ} (hz : 0 < z.re) :
    Summable (fun r : ℕ => ∫ t in Ioi (0 : ℝ), ‖unitRieszStirlingAtomIntegrand z r t‖) := by
  have hp : (1 : ℝ) < z.re + 1 := by linarith
  have hcomp : Summable (fun r : ℕ => ((r : ℝ) + 1) ^ (-(z.re + 1)) / (z.re + 1) ^ 2) :=
    (summable_rpow_shift hp).div_const _
  refine hcomp.congr fun r => ?_
  rw [integral_norm_unitRieszStirlingAtomIntegrand hz r]
  congr 1
  rw [Real.rpow_def_of_pos (by positivity)]
  congr 1
  ring

theorem tsum_unitRieszStirlingAtomIntegrand {z : ℂ} {t : ℝ} (ht : 0 ≤ t) :
    ∑' r : ℕ, unitRieszStirlingAtomIntegrand z r t =
      Complex.exp (-(z * (t : ℂ))) * ((unitRieszStirlingHead t : ℝ) : ℂ) := by
  classical
  set N : ℕ := ⌊Real.exp t⌋₊ with hN
  have hsupp : ∀ r : ℕ, r ∉ Finset.range N → unitRieszStirlingAtom r t = 0 := by
    intro r hr
    have hrM : N ≤ r := by simpa using Finset.mem_range.not.1 hr
    have hMle : (N : ℝ) ≤ Real.exp t := Nat.floor_le (Real.exp_nonneg t)
    have hltM : Real.exp t < (N : ℝ) + 1 := Nat.lt_floor_add_one _
    have hlt : Real.exp t < (r : ℝ) + 1 := by
      have : (N : ℝ) + 1 ≤ (r : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hrM 1
      linarith
    refine unitRieszStirlingAtom_eq_zero ?_
    have hlog := Real.log_lt_log (Real.exp_pos t) hlt
    rwa [Real.log_exp] at hlog
  have hsr : Summable (fun r : ℕ => unitRieszStirlingAtom r t) :=
    summable_of_ne_finset_zero (s := Finset.range N) hsupp
  have hpull : ∑' r : ℕ, unitRieszStirlingAtomIntegrand z r t =
      Complex.exp (-(z * (t : ℂ))) * ∑' r : ℕ, ((unitRieszStirlingAtom r t : ℝ) : ℂ) := by
    unfold unitRieszStirlingAtomIntegrand
    exact tsum_mul_left
  have hreal : ∑' r : ℕ, ((unitRieszStirlingAtom r t : ℝ) : ℂ) =
      ((∑' r : ℕ, unitRieszStirlingAtom r t : ℝ) : ℂ) :=
    (Complex.ofRealCLM.map_tsum hsr).symm
  rw [hpull, hreal, ← unitRieszStirlingHead_eq_tsum ht]

/-- **The zeta Laplace transform of the Stirling head.** -/
theorem unitRieszStirlingHead_laplace {z : ℂ} (hz : 0 < z.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(z * (t : ℂ))) * ((unitRieszStirlingHead t : ℝ) : ℂ)) =
      riemannZeta (1 + z) / (1 + z) ^ 2 := by
  have hz1 : (z + 1) ≠ 0 := by
    intro h
    have hre : (z + 1).re = 0 := by rw [h]; simp
    simp only [Complex.add_re, Complex.one_re] at hre
    linarith
  have hswap := integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun r : ℕ => unitRieszStirlingAtomIntegrand z r)
    (fun r => integrableOn_unitRieszStirlingAtomIntegrand hz r)
    (summable_integral_norm_unitRieszStirlingAtomIntegrand hz)
  have hpt : (∫ t in Ioi (0 : ℝ), ∑' r : ℕ, unitRieszStirlingAtomIntegrand z r t) =
      ∫ t in Ioi (0 : ℝ), Complex.exp (-(z * (t : ℂ))) *
        ((unitRieszStirlingHead t : ℝ) : ℂ) :=
    setIntegral_congr_fun measurableSet_Ioi
      (fun t ht => tsum_unitRieszStirlingAtomIntegrand (le_of_lt ht))
  have hterm : ∀ r : ℕ, (∫ t in Ioi (0 : ℝ), unitRieszStirlingAtomIntegrand z r t) =
      (1 / ((r : ℂ) + 1) ^ (1 + z)) * (1 / (z + 1) ^ 2) := by
    intro r
    rw [integral_unitRieszStirlingAtomIntegrand hz r]
    have hne : ((r : ℂ) + 1) ≠ 0 := by
      have hcast : ((r : ℂ) + 1) = (((r : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [hcast]
      simp only [ne_eq, Complex.ofReal_eq_zero]
      positivity
    have hexp : Complex.exp (-((z + 1) * ((Real.log ((r : ℝ) + 1) : ℝ) : ℂ))) =
        1 / ((r : ℂ) + 1) ^ (1 + z) := by
      rw [Complex.cpow_def_of_ne_zero hne]
      have hlog : Complex.log ((r : ℂ) + 1) = ((Real.log ((r : ℝ) + 1) : ℝ) : ℂ) := by
        have hcast : ((r : ℂ) + 1) = (((r : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
        rw [hcast, ← Complex.ofReal_log (by positivity)]
      rw [hlog, one_div, ← Complex.exp_neg]
      congr 1
      ring
    rw [hexp]
    ring
  have hzeta : ∑' r : ℕ, (1 / ((r : ℂ) + 1) ^ (1 + z)) = riemannZeta (1 + z) := by
    have hre : 1 < (1 + z).re := by
      simp only [Complex.add_re, Complex.one_re]
      linarith
    exact (zeta_eq_tsum_one_div_nat_add_one_cpow hre).symm
  have hsum : ∑' r : ℕ, (∫ t in Ioi (0 : ℝ), unitRieszStirlingAtomIntegrand z r t) =
      riemannZeta (1 + z) * (1 / (z + 1) ^ 2) := by
    rw [tsum_congr hterm, tsum_mul_right, hzeta]
  rw [hpt] at hswap
  rw [← hswap, hsum]
  rw [show (z + 1) = (1 + z) from by ring]
  ring

/-! ## The Laplace transform of the full correction -/

theorem integrableOn_cexp_mul_unitRieszStirlingHead {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn
      (fun t : ℝ => Complex.exp (-(z * (t : ℂ))) * ((unitRieszStirlingHead t : ℝ) : ℂ))
      (Ioi (0 : ℝ)) volume := by
  refine Integrable.mono' ((integrableOn_Ioi_cexp_neg_mul hz).norm) ?_ ?_
  · exact ((Complex.measurable_exp.comp
      (measurable_const.mul Complex.measurable_ofReal).neg).mul
      (Complex.measurable_ofReal.comp measurable_unitRieszStirlingHead)).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : (0 : ℝ) ≤ t := le_of_lt ht
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (unitRieszStirlingHead_nonneg ht0)]
    have h1 := unitRieszStirlingHead_le_one ht0
    have h2 := norm_nonneg (Complex.exp (-(z * (t : ℂ))))
    nlinarith

theorem integrableOn_cexp_mul_one {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(z * (t : ℂ))) * ((1 : ℝ) : ℂ))
      (Ioi (0 : ℝ)) volume := by
  refine (integrableOn_Ioi_cexp_neg_mul hz).congr_fun ?_ measurableSet_Ioi
  intro t _
  simp

theorem integral_cexp_mul_one {z : ℂ} (hz : 0 < z.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(z * (t : ℂ))) * ((1 : ℝ) : ℂ)) = 1 / z := by
  rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => by simp :
    ∀ t ∈ Ioi (0 : ℝ), Complex.exp (-(z * (t : ℂ))) * ((1 : ℝ) : ℂ) =
      Complex.exp (-(z * (t : ℂ)))), integral_Ioi_cexp_neg_mul_shift hz 0]
  simp

theorem integrableOn_cexp_mul_exp_neg {z : ℂ} (hz : 0 < z.re) :
    IntegrableOn (fun t : ℝ => Complex.exp (-(z * (t : ℂ))) * ((Real.exp (-t) : ℝ) : ℂ))
      (Ioi (0 : ℝ)) volume := by
  have hb1 : 0 < (z + 1).re := by
    simp only [Complex.add_re, Complex.one_re]; linarith
  refine (integrableOn_Ioi_cexp_neg_mul hb1).congr_fun ?_ measurableSet_Ioi
  intro t _
  show Complex.exp (-((z + 1) * (t : ℂ))) =
    Complex.exp (-(z * (t : ℂ))) * ((Real.exp (-t) : ℝ) : ℂ)
  rw [Complex.ofReal_exp, ← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem integral_cexp_mul_exp_neg {z : ℂ} (hz : 0 < z.re) :
    (∫ t in Ioi (0 : ℝ), Complex.exp (-(z * (t : ℂ))) * ((Real.exp (-t) : ℝ) : ℂ)) =
      1 / (z + 1) := by
  have hb1 : 0 < (z + 1).re := by
    simp only [Complex.add_re, Complex.one_re]; linarith
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      Complex.exp (-(z * (t : ℂ))) * ((Real.exp (-t) : ℝ) : ℂ) =
        Complex.exp (-((z + 1) * (t : ℂ))) := by
    intro t _
    rw [Complex.ofReal_exp, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_Ioi_cexp_neg_mul_shift hb1 0]
  simp

/-- **Equations (10)–(12).**  The exact Laplace transform of the unit-Riesz Stirling correction is
the source-free factor of the completed-source weld. -/
theorem unitRieszStirlingCorrection_laplace {z : ℂ} (hz : 0 < z.re) :
    (∫ t in Ioi (0 : ℝ),
        Complex.exp (-(z * (t : ℂ))) * ((unitRieszStirlingCorrection t : ℝ) : ℂ)) =
      riemannZeta (1 + z) / (1 + z) ^ 2 - 1 / z - 1 / (z + 1) := by
  have hpt : ∀ t ∈ Ioi (0 : ℝ),
      Complex.exp (-(z * (t : ℂ))) * ((unitRieszStirlingCorrection t : ℝ) : ℂ) =
        Complex.exp (-(z * (t : ℂ))) * ((unitRieszStirlingHead t : ℝ) : ℂ) -
          Complex.exp (-(z * (t : ℂ))) * ((1 : ℝ) : ℂ) -
          Complex.exp (-(z * (t : ℂ))) * ((Real.exp (-t) : ℝ) : ℂ) := by
    intro t _
    rw [unitRieszStirlingCorrection_eq_head]
    push_cast
    ring
  have hA := integrableOn_cexp_mul_unitRieszStirlingHead hz
  have hB := integrableOn_cexp_mul_one hz
  have hC := integrableOn_cexp_mul_exp_neg hz
  have hAB : IntegrableOn
      (fun t : ℝ => Complex.exp (-(z * (t : ℂ))) * ((unitRieszStirlingHead t : ℝ) : ℂ) -
        Complex.exp (-(z * (t : ℂ))) * ((1 : ℝ) : ℂ)) (Ioi (0 : ℝ)) volume := hA.sub hB
  rw [setIntegral_congr_fun measurableSet_Ioi hpt,
    integral_sub hAB hC, integral_sub hA hB,
    unitRieszStirlingHead_laplace hz, integral_cexp_mul_one hz,
    integral_cexp_mul_exp_neg hz]

end GaloisForLFunctions.RHTower
