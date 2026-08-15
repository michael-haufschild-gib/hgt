import GaloisForLFunctions.RHTower.CCMUnitRieszMarkovDensity
import GaloisForLFunctions.RHTower.CCMQuartetPaleyWiener
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# The exact zeta Laplace transform of the unit-Riesz aperture profile

The unit-Riesz logarithmic profile is a sum of arithmetic atoms, one per integer `r ≥ 1`, switched
on at `v = log r`:

```text
w(v) = 3 sum_(r >= 1) 1_{log r <= v} (exp(-v) - sqrt r exp(-3v/2)).
```

Each atom is nonnegative on its own support and bounded there by `exp(-v)`, so the Laplace integral
converges absolutely in the right half-plane and may be summed term by term.  Every term integrates
in closed form, and the resulting Dirichlet series is `zeta(1+z)`:

```text
Lw(z) = (3/2) zeta(1+z) / ((z+1)(z+3/2)),      Re z > 0.
```

This is equation `(6)` of `ccm-unit-riesz-markov-virial-landau-law`, with no asymptotics and no
unproved interchange.
-/

open MeasureTheory Filter Set Topology Complex

noncomputable section

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-! ## Elementary half-line translation -/

/-- Translating the half-line moves the base point, for any Banach-valued integrand. -/
theorem integral_Ioi_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : ℝ) (f : ℝ → E) :
    ∫ u in Ioi (0 : ℝ), f (a + u) = ∫ y in Ioi a, f y := by
  have hmp : MeasurePreserving (fun y : ℝ => a + y) volume volume :=
    measurePreserving_add_left volume a
  have hemb : MeasurableEmbedding (fun y : ℝ => a + y) :=
    (Homeomorph.addLeft a).measurableEmbedding
  have hpre : (fun y : ℝ => a + y) ⁻¹' Ioi a = Ioi (0 : ℝ) := by ext y; simp
  have h := hmp.setIntegral_preimage_emb hemb f (Ioi a)
  rw [hpre] at h
  exact h

/-- The shifted exponential Laplace integral. -/
theorem integral_Ioi_cexp_neg_mul_shift {b : ℂ} (hb : 0 < b.re) (L : ℝ) :
    (∫ v in Ioi L, Complex.exp (-(b * (v : ℂ)))) = Complex.exp (-(b * (L : ℂ))) / b := by
  have hsplit : ∀ u : ℝ, Complex.exp (-(b * ((L + u : ℝ) : ℂ)))
      = Complex.exp (-(b * (L : ℂ))) * Complex.exp (-(b * (u : ℂ))) := by
    intro u
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have h := integral_Ioi_translate L (fun v : ℝ => Complex.exp (-(b * (v : ℂ))))
  rw [← h]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun u _ => hsplit u), integral_const_mul,
    integral_Ioi_cexp_neg_mul hb]
  rw [div_eq_mul_inv]

/-- Integrability of a shifted exponential on a half-line to the right of the origin. -/
theorem integrableOn_Ioi_cexp_neg_mul_shift {b : ℂ} (hb : 0 < b.re) {L : ℝ} (hL : 0 ≤ L) :
    IntegrableOn (fun v : ℝ => Complex.exp (-(b * (v : ℂ)))) (Ioi L) volume :=
  (integrableOn_Ioi_cexp_neg_mul hb).mono_set (Ioi_subset_Ioi hL)

/-- A function vanishing to the left of `L` integrates over `Ioi 0` as over `Ioi L`. -/
theorem setIntegral_Ioi_of_vanishing {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {L : ℝ} (hL : 0 ≤ L) {g : ℝ → E} (hzero : ∀ v, v ≤ L → g v = 0)
    (hint : IntegrableOn g (Ioi L) volume) :
    ∫ v in Ioi (0 : ℝ), g v = ∫ v in Ioi L, g v := by
  have hsplit : Ioi (0 : ℝ) = Ioc 0 L ∪ Ioi L := (Ioc_union_Ioi_eq_Ioi hL).symm
  have hdisj : Disjoint (Ioc (0 : ℝ) L) (Ioi L) := Ioc_disjoint_Ioi le_rfl
  have hint1 : IntegrableOn g (Ioc (0 : ℝ) L) volume := by
    have hz0 : IntegrableOn (fun _ : ℝ => (0 : E)) (Ioc (0 : ℝ) L) volume := integrableOn_zero
    refine MeasureTheory.IntegrableOn.congr_fun hz0 ?_ measurableSet_Ioc
    intro v hv
    exact (hzero v hv.2).symm
  have hzeroint : ∫ v in Ioc (0 : ℝ) L, g v = 0 := by
    rw [setIntegral_congr_fun measurableSet_Ioc (fun v hv => hzero v hv.2)]
    simp
  rw [hsplit, setIntegral_union hdisj measurableSet_Ioi hint1 hint, hzeroint, zero_add]

/-! ## The arithmetic atoms of the profile -/

/-- The `r+1`-st arithmetic atom of the unit-Riesz logarithmic profile. -/
def unitRieszAtom (r : ℕ) (v : ℝ) : ℝ :=
  if Real.log (r + 1) < v then Real.exp (-v) - Real.sqrt (r + 1) * Real.exp (-3 * v / 2) else 0

theorem sqrt_eq_exp_log_div_two {x : ℝ} (hx : 0 < x) :
    Real.sqrt x = Real.exp (Real.log x / 2) := by
  have hsq : Real.exp (Real.log x / 2) ^ 2 = x := by
    rw [← Real.exp_nat_mul,
      show ((2 : ℕ) : ℝ) * (Real.log x / 2) = Real.log x from by push_cast; ring]
    exact Real.exp_log hx
  calc Real.sqrt x = Real.sqrt (Real.exp (Real.log x / 2) ^ 2) := by rw [hsq]
    _ = Real.exp (Real.log x / 2) := Real.sqrt_sq (Real.exp_pos _).le

theorem unitRieszAtom_eq_of_le {r : ℕ} {v : ℝ} (hv : Real.log (r + 1) ≤ v) :
    unitRieszAtom r v = Real.exp (-v) - Real.sqrt (r + 1) * Real.exp (-3 * v / 2) := by
  rcases lt_or_eq_of_le hv with h | h
  · rw [unitRieszAtom, if_pos h]
  · have hpos : (0 : ℝ) < (r : ℝ) + 1 := by positivity
    have hsqrt : Real.sqrt ((r : ℝ) + 1) = Real.exp (v / 2) := by
      rw [sqrt_eq_exp_log_div_two hpos, ← h]
    have hzero : Real.exp (-v) - Real.sqrt ((r : ℝ) + 1) * Real.exp (-3 * v / 2) = 0 := by
      rw [hsqrt, ← Real.exp_add]
      have : v / 2 + -3 * v / 2 = -v := by ring
      rw [this]
      ring
    rw [unitRieszAtom, if_neg (by rw [h]; exact lt_irrefl _), hzero]

theorem unitRieszAtom_eq_zero {r : ℕ} {v : ℝ} (hv : v ≤ Real.log (r + 1)) :
    unitRieszAtom r v = 0 := by
  rw [unitRieszAtom, if_neg (not_lt.2 hv)]

theorem unitRieszAtom_nonneg (r : ℕ) (v : ℝ) : 0 ≤ unitRieszAtom r v := by
  rcases le_or_gt v (Real.log ((r : ℝ) + 1)) with h | h
  · rw [unitRieszAtom_eq_zero h]
  · rw [unitRieszAtom_eq_of_le h.le]
    have hpos : (0 : ℝ) < (r : ℝ) + 1 := by positivity
    have hsqrt : Real.sqrt ((r : ℝ) + 1) = Real.exp (Real.log ((r : ℝ) + 1) / 2) :=
      sqrt_eq_exp_log_div_two hpos
    have hle : Real.exp (Real.log ((r : ℝ) + 1) / 2) ≤ Real.exp (v / 2) :=
      Real.exp_le_exp.2 (by linarith)
    have hmul : Real.sqrt ((r : ℝ) + 1) * Real.exp (-3 * v / 2)
        ≤ Real.exp (v / 2) * Real.exp (-3 * v / 2) := by
      rw [hsqrt]
      exact mul_le_mul_of_nonneg_right hle (Real.exp_pos _).le
    have hval : Real.exp (v / 2) * Real.exp (-3 * v / 2) = Real.exp (-v) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hval] at hmul
    linarith

theorem unitRieszAtom_le (r : ℕ) (v : ℝ) : unitRieszAtom r v ≤ Real.exp (-v) := by
  rcases le_or_gt v (Real.log ((r : ℝ) + 1)) with h | h
  · rw [unitRieszAtom_eq_zero h]
    exact (Real.exp_pos _).le
  · rw [unitRieszAtom_eq_of_le h.le]
    have : 0 ≤ Real.sqrt ((r : ℝ) + 1) * Real.exp (-3 * v / 2) := by positivity
    linarith

/-- **The profile is the sum of its arithmetic atoms.** -/
theorem unitRieszLogProfile_eq_tsum {v : ℝ} (hv : 0 ≤ v) :
    unitRieszLogProfile v = 3 * ∑' r : ℕ, unitRieszAtom r v := by
  classical
  set M : ℕ := ⌊Real.exp v⌋₊ with hM
  have hexp1 : (1 : ℝ) ≤ Real.exp v := Real.one_le_exp hv
  have hMle : (M : ℝ) ≤ Real.exp v := Nat.floor_le (Real.exp_nonneg v)
  have hltM : Real.exp v < (M : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsupp : ∀ r : ℕ, r ∉ Finset.range M → unitRieszAtom r v = 0 := by
    intro r hr
    have hrM : M ≤ r := by simpa using Finset.mem_range.not.1 hr
    have hle : Real.exp v ≤ (r : ℝ) + 1 := by
      have : (M : ℝ) + 1 ≤ (r : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hrM 1
      linarith
    refine unitRieszAtom_eq_zero ?_
    have hpos : (0 : ℝ) < (r : ℝ) + 1 := by positivity
    have := Real.log_le_log (Real.exp_pos v) hle
    rwa [Real.log_exp] at this
  have hsum : ∑' r : ℕ, unitRieszAtom r v = ∑ r ∈ Finset.range M, unitRieszAtom r v :=
    tsum_eq_sum hsupp
  have hterm : ∀ r ∈ Finset.range M, unitRieszAtom r v
      = Real.exp (-v) - Real.sqrt (r + 1) * Real.exp (-3 * v / 2) := by
    intro r hr
    refine unitRieszAtom_eq_of_le ?_
    have hrM : r + 1 ≤ M := Finset.mem_range.1 hr
    have hle : ((r : ℝ) + 1) ≤ Real.exp v := by
      have : ((r : ℝ) + 1) ≤ (M : ℝ) := by exact_mod_cast hrM
      linarith
    have hpos : (0 : ℝ) < (r : ℝ) + 1 := by positivity
    have := Real.log_le_log hpos hle
    rwa [Real.log_exp] at this
  rw [hsum, Finset.sum_congr rfl hterm, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_range, ← Finset.sum_mul]
  rw [unitRieszLogProfile, unitRieszCellProfile, unitRieszSqrtPrefixMass]
  ring

/-! ## The Laplace transform -/

/-- The Laplace transform of the unit-Riesz logarithmic profile. -/
def unitRieszLaplace (z : ℂ) : ℂ :=
  ∫ v in Ioi (0 : ℝ), Complex.exp (-(z * (v : ℂ))) * ((unitRieszLogProfile v : ℝ) : ℂ)

/-- The Laplace integrand of a single atom. -/
def unitRieszAtomIntegrand (z : ℂ) (r : ℕ) (v : ℝ) : ℂ :=
  Complex.exp (-(z * (v : ℂ))) * ((unitRieszAtom r v : ℝ) : ℂ)

theorem log_natCast_add_one_nonneg (r : ℕ) : 0 ≤ Real.log ((r : ℝ) + 1) :=
  Real.log_nonneg (by simp)

theorem unitRieszAtomIntegrand_eq {z : ℂ} {r : ℕ} {v : ℝ} (hv : Real.log ((r : ℝ) + 1) ≤ v) :
    unitRieszAtomIntegrand z r v
      = Complex.exp (-((z + 1) * (v : ℂ)))
        - ((Real.sqrt ((r : ℝ) + 1) : ℝ) : ℂ) * Complex.exp (-((z + 3 / 2) * (v : ℂ))) := by
  unfold unitRieszAtomIntegrand
  rw [unitRieszAtom_eq_of_le hv]
  have h1 : ((Real.exp (-v) : ℝ) : ℂ) = Complex.exp (-(v : ℂ)) := by
    rw [Complex.ofReal_exp, Complex.ofReal_neg]
  have h2 : ((Real.exp (-3 * v / 2) : ℝ) : ℂ) = Complex.exp (-((3 / 2 : ℂ) * (v : ℂ))) := by
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  rw [Complex.ofReal_sub, Complex.ofReal_mul, h1, h2, mul_sub]
  congr 1
  · rw [← Complex.exp_add]
    congr 1
    ring
  · rw [show Complex.exp (-(z * (v : ℂ))) * (((Real.sqrt ((r : ℝ) + 1) : ℝ) : ℂ)
        * Complex.exp (-((3 / 2 : ℂ) * (v : ℂ))))
      = ((Real.sqrt ((r : ℝ) + 1) : ℝ) : ℂ)
        * (Complex.exp (-(z * (v : ℂ))) * Complex.exp (-((3 / 2 : ℂ) * (v : ℂ)))) from by ring]
    congr 1
    rw [← Complex.exp_add]
    congr 1
    ring

theorem integrableOn_unitRieszAtomIntegrand {z : ℂ} (hz : 0 < z.re) (r : ℕ) :
    IntegrableOn (unitRieszAtomIntegrand z r) (Ioi (0 : ℝ)) volume := by
  set L : ℝ := Real.log ((r : ℝ) + 1) with hL
  have hL0 : 0 ≤ L := log_natCast_add_one_nonneg r
  have hb1 : 0 < (z + 1).re := by simp [Complex.add_re]; linarith
  have hb2 : 0 < (z + 3 / 2).re := by
    have : ((3 : ℂ) / 2).re = 3 / 2 := by norm_num
    simp [Complex.add_re, this]
    linarith
  have hintTail : IntegrableOn (unitRieszAtomIntegrand z r) (Ioi L) volume := by
    refine MeasureTheory.IntegrableOn.congr_fun
      ((integrableOn_Ioi_cexp_neg_mul_shift hb1 hL0).sub
        ((integrableOn_Ioi_cexp_neg_mul_shift hb2 hL0).const_mul
          ((Real.sqrt ((r : ℝ) + 1) : ℝ) : ℂ))) ?_ measurableSet_Ioi
    intro v hv
    exact (unitRieszAtomIntegrand_eq (le_of_lt hv)).symm
  have hintHead : IntegrableOn (unitRieszAtomIntegrand z r) (Ioc (0 : ℝ) L) volume := by
    have hz0 : IntegrableOn (fun _ : ℝ => (0 : ℂ)) (Ioc (0 : ℝ) L) volume := integrableOn_zero
    refine MeasureTheory.IntegrableOn.congr_fun hz0 ?_ measurableSet_Ioc
    intro v hv
    unfold unitRieszAtomIntegrand
    rw [unitRieszAtom_eq_zero hv.2]
    simp
  have hun := hintHead.union hintTail
  rwa [Ioc_union_Ioi_eq_Ioi hL0] at hun

theorem integral_unitRieszAtomIntegrand {z : ℂ} (hz : 0 < z.re) (r : ℕ) :
    (∫ v in Ioi (0 : ℝ), unitRieszAtomIntegrand z r v)
      = Complex.exp (-((z + 1) * ((Real.log ((r : ℝ) + 1) : ℝ) : ℂ)))
        * ((z + 1)⁻¹ - (z + 3 / 2)⁻¹) := by
  set L : ℝ := Real.log ((r : ℝ) + 1) with hLdef
  have hL0 : 0 ≤ L := log_natCast_add_one_nonneg r
  have hb1 : 0 < (z + 1).re := by simp [Complex.add_re]; linarith
  have hb2 : 0 < (z + 3 / 2).re := by
    have : ((3 : ℂ) / 2).re = 3 / 2 := by norm_num
    simp [Complex.add_re, this]
    linarith
  have hzero : ∀ v : ℝ, v ≤ L → unitRieszAtomIntegrand z r v = 0 := by
    intro v hv
    unfold unitRieszAtomIntegrand
    rw [unitRieszAtom_eq_zero hv]
    simp
  have hintTail : IntegrableOn (unitRieszAtomIntegrand z r) (Ioi L) volume := by
    refine MeasureTheory.IntegrableOn.congr_fun
      ((integrableOn_Ioi_cexp_neg_mul_shift hb1 hL0).sub
        ((integrableOn_Ioi_cexp_neg_mul_shift hb2 hL0).const_mul
          ((Real.sqrt ((r : ℝ) + 1) : ℝ) : ℂ))) ?_ measurableSet_Ioi
    intro v hv
    exact (unitRieszAtomIntegrand_eq (le_of_lt hv)).symm
  rw [setIntegral_Ioi_of_vanishing hL0 hzero hintTail]
  rw [setIntegral_congr_fun measurableSet_Ioi
    (fun v hv => unitRieszAtomIntegrand_eq (le_of_lt hv))]
  rw [integral_sub (integrableOn_Ioi_cexp_neg_mul_shift hb1 hL0)
    ((integrableOn_Ioi_cexp_neg_mul_shift hb2 hL0).const_mul _),
    integral_const_mul, integral_Ioi_cexp_neg_mul_shift hb1 L,
    integral_Ioi_cexp_neg_mul_shift hb2 L]
  have hsqrt : ((Real.sqrt ((r : ℝ) + 1) : ℝ) : ℂ) = Complex.exp ((1 / 2 : ℂ) * (L : ℂ)) := by
    have hpos : (0 : ℝ) < (r : ℝ) + 1 := by positivity
    rw [sqrt_eq_exp_log_div_two hpos, Complex.ofReal_exp]
    congr 1
    rw [hLdef]
    push_cast
    ring
  rw [hsqrt]
  have hcollapse : Complex.exp ((1 / 2 : ℂ) * (L : ℂ)) * (Complex.exp (-((z + 3 / 2) * (L : ℂ)))
      / (z + 3 / 2)) = Complex.exp (-((z + 1) * (L : ℂ))) / (z + 3 / 2) := by
    rw [div_eq_mul_inv, div_eq_mul_inv, ← mul_assoc, ← Complex.exp_add]
    congr 2
    ring
  rw [hcollapse]
  field_simp

/-! ## Summability of the atom norms -/

theorem integral_Ioi_rexp_neg_mul_shift {b : ℝ} (hb : 0 < b) (L : ℝ) :
    (∫ v in Ioi L, Real.exp (-(b * v))) = Real.exp (-(b * L)) / b := by
  have hbc : (0 : ℝ) < ((b : ℂ)).re := by simpa using hb
  have hcomplex := integral_Ioi_cexp_neg_mul_shift hbc L
  have hcast : ∀ v : ℝ, ((Real.exp (-(b * v)) : ℝ) : ℂ)
      = Complex.exp (-((b : ℂ) * (v : ℂ))) := by
    intro v
    rw [Complex.ofReal_exp]
    congr 1
    push_cast
    ring
  have hint : ((∫ v in Ioi L, Real.exp (-(b * v)) : ℝ) : ℂ)
      = ∫ v in Ioi L, Complex.exp (-((b : ℂ) * (v : ℂ))) := by
    rw [← integral_complex_ofReal]
    exact setIntegral_congr_fun measurableSet_Ioi fun v _ => hcast v
  have hgoal : ((∫ v in Ioi L, Real.exp (-(b * v)) : ℝ) : ℂ)
      = ((Real.exp (-(b * L)) / b : ℝ) : ℂ) := by
    rw [hint, hcomplex, ← hcast L]
    push_cast
    ring
  exact_mod_cast hgoal

theorem summable_rpow_shift {p : ℝ} (hp : 1 < p) :
    Summable (fun r : ℕ => ((r : ℝ) + 1) ^ (-p)) := by
  have h : Summable (fun n : ℕ => 1 / (n : ℝ) ^ p) := (Real.summable_one_div_nat_rpow).2 hp
  have h2 := (summable_nat_add_iff 1).2 h
  refine h2.congr fun n => ?_
  push_cast
  rw [Real.rpow_neg (by positivity)]
  ring

theorem norm_unitRieszAtomIntegrand_le {z : ℂ} (r : ℕ) (v : ℝ) :
    ‖unitRieszAtomIntegrand z r v‖ ≤ Real.exp (-((z.re + 1) * v)) := by
  unfold unitRieszAtomIntegrand
  rw [norm_mul, Complex.norm_exp, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (unitRieszAtom_nonneg r v)]
  have hre : (-(z * (v : ℂ))).re = -(z.re * v) := by simp [Complex.mul_re]
  rw [hre]
  have hbound := unitRieszAtom_le r v
  have hpos : (0 : ℝ) < Real.exp (-(z.re * v)) := Real.exp_pos _
  have hval : Real.exp (-(z.re * v)) * Real.exp (-v) = Real.exp (-((z.re + 1) * v)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc Real.exp (-(z.re * v)) * unitRieszAtom r v
      ≤ Real.exp (-(z.re * v)) * Real.exp (-v) := mul_le_mul_of_nonneg_left hbound hpos.le
    _ = Real.exp (-((z.re + 1) * v)) := hval

theorem integral_norm_unitRieszAtomIntegrand_le {z : ℂ} (hz : 0 < z.re) (r : ℕ) :
    (∫ v in Ioi (0 : ℝ), ‖unitRieszAtomIntegrand z r v‖)
      ≤ ((r : ℝ) + 1) ^ (-(z.re + 1)) / (z.re + 1) := by
  set L : ℝ := Real.log ((r : ℝ) + 1) with hLdef
  have hL0 : 0 ≤ L := log_natCast_add_one_nonneg r
  have hp : (0 : ℝ) < z.re + 1 := by linarith
  have hzero : ∀ v : ℝ, v ≤ L → ‖unitRieszAtomIntegrand z r v‖ = 0 := by
    intro v hv
    unfold unitRieszAtomIntegrand
    rw [unitRieszAtom_eq_zero hv]
    simp
  have hintNorm : IntegrableOn (fun v => ‖unitRieszAtomIntegrand z r v‖) (Ioi L) volume :=
    ((integrableOn_unitRieszAtomIntegrand hz r).mono_set (Ioi_subset_Ioi hL0)).norm
  have hsplit := setIntegral_Ioi_of_vanishing (E := ℝ) hL0 hzero hintNorm
  rw [hsplit]
  have hcomp : IntegrableOn (fun v : ℝ => Real.exp (-((z.re + 1) * v))) (Ioi L) volume := by
    refine MeasureTheory.IntegrableOn.congr_fun (exp_neg_integrableOn_Ioi L hp) ?_
      measurableSet_Ioi
    intro v _
    simp
    ring
  have hmono : (∫ v in Ioi L, ‖unitRieszAtomIntegrand z r v‖)
      ≤ ∫ v in Ioi L, Real.exp (-((z.re + 1) * v)) :=
    setIntegral_mono_on hintNorm hcomp measurableSet_Ioi
      fun v _ => norm_unitRieszAtomIntegrand_le r v
  rw [integral_Ioi_rexp_neg_mul_shift hp L] at hmono
  refine hmono.trans (le_of_eq ?_)
  congr 1
  rw [hLdef, Real.rpow_def_of_pos (by positivity)]
  congr 1
  ring

theorem summable_integral_norm_unitRieszAtomIntegrand {z : ℂ} (hz : 0 < z.re) :
    Summable (fun r : ℕ => ∫ v in Ioi (0 : ℝ), ‖unitRieszAtomIntegrand z r v‖) := by
  have hp : (1 : ℝ) < z.re + 1 := by linarith
  have hcomp : Summable (fun r : ℕ => ((r : ℝ) + 1) ^ (-(z.re + 1)) / (z.re + 1)) :=
    (summable_rpow_shift hp).div_const _
  refine Summable.of_nonneg_of_le (fun r => ?_) (fun r => ?_) hcomp
  · exact setIntegral_nonneg measurableSet_Ioi fun v _ => norm_nonneg _
  · exact integral_norm_unitRieszAtomIntegrand_le hz r

/-! ## The exact transform -/

theorem tsum_unitRieszAtomIntegrand {z : ℂ} {v : ℝ} (hv : 0 ≤ v) :
    ∑' r : ℕ, unitRieszAtomIntegrand z r v
      = Complex.exp (-(z * (v : ℂ))) * ((unitRieszLogProfile v : ℝ) : ℂ) / 3 := by
  classical
  set M : ℕ := ⌊Real.exp v⌋₊ with hM
  have hsupp : ∀ r : ℕ, r ∉ Finset.range M → unitRieszAtom r v = 0 := by
    intro r hr
    have hrM : M ≤ r := by simpa using Finset.mem_range.not.1 hr
    have hle : Real.exp v ≤ (r : ℝ) + 1 := by
      have hMle : (M : ℝ) ≤ Real.exp v := Nat.floor_le (Real.exp_nonneg v)
      have hltM : Real.exp v < (M : ℝ) + 1 := Nat.lt_floor_add_one _
      have : (M : ℝ) + 1 ≤ (r : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hrM 1
      linarith
    refine unitRieszAtom_eq_zero ?_
    have := Real.log_le_log (Real.exp_pos v) hle
    rwa [Real.log_exp] at this
  have hsummable : Summable (fun r : ℕ => ((unitRieszAtom r v : ℝ) : ℂ)) := by
    refine summable_of_ne_finset_zero (s := Finset.range M) fun r hr => ?_
    rw [hsupp r hr]
    simp
  have hpull : ∑' r : ℕ, unitRieszAtomIntegrand z r v
      = Complex.exp (-(z * (v : ℂ))) * ∑' r : ℕ, ((unitRieszAtom r v : ℝ) : ℂ) := by
    unfold unitRieszAtomIntegrand
    exact tsum_mul_left
  have hreal : ∑' r : ℕ, ((unitRieszAtom r v : ℝ) : ℂ)
      = ((∑' r : ℕ, unitRieszAtom r v : ℝ) : ℂ) := by
    have hsr : Summable (fun r : ℕ => unitRieszAtom r v) :=
      summable_of_ne_finset_zero (s := Finset.range M) hsupp
    exact (Complex.ofRealCLM.map_tsum hsr).symm
  rw [hpull, hreal, unitRieszLogProfile_eq_tsum hv]
  push_cast
  ring

/-- **Equation (6).**  The exact zeta Laplace transform of the unit-Riesz aperture profile. -/
theorem unitRieszLaplace_eq {z : ℂ} (hz : 0 < z.re) :
    unitRieszLaplace z = 3 / 2 * riemannZeta (1 + z) / ((z + 1) * (z + 3 / 2)) := by
  have hz1 : (z + 1) ≠ 0 := by
    intro h
    have : (z + 1).re = 0 := by rw [h]; simp
    simp [Complex.add_re] at this
    linarith
  have hz32 : (z + 3 / 2) ≠ 0 := by
    intro h
    have hre : (z + 3 / 2).re = 0 := by rw [h]; simp
    have h32 : ((3 : ℂ) / 2).re = 3 / 2 := by norm_num
    simp [Complex.add_re, h32] at hre
    linarith
  have hswap := integral_tsum_of_summable_integral_norm
    (μ := volume.restrict (Ioi (0 : ℝ)))
    (F := fun r : ℕ => unitRieszAtomIntegrand z r)
    (fun r => integrableOn_unitRieszAtomIntegrand hz r)
    (summable_integral_norm_unitRieszAtomIntegrand hz)
  have hpt : ∫ v in Ioi (0 : ℝ), ∑' r : ℕ, unitRieszAtomIntegrand z r v
      = unitRieszLaplace z / 3 := by
    unfold unitRieszLaplace
    rw [setIntegral_congr_fun measurableSet_Ioi
      (fun v hv => tsum_unitRieszAtomIntegrand (le_of_lt hv)), integral_div]
  have hterm : ∀ r : ℕ, (∫ v in Ioi (0 : ℝ), unitRieszAtomIntegrand z r v)
      = (1 / ((r : ℂ) + 1) ^ (1 + z)) * ((z + 1)⁻¹ - (z + 3 / 2)⁻¹) := by
    intro r
    rw [integral_unitRieszAtomIntegrand hz r]
    congr 1
    have hne : ((r : ℂ) + 1) ≠ 0 := by
      have : ((r : ℂ) + 1) = (((r : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [this]
      simp only [ne_eq, Complex.ofReal_eq_zero]
      positivity
    rw [Complex.cpow_def_of_ne_zero hne]
    have hlog : Complex.log ((r : ℂ) + 1) = ((Real.log ((r : ℝ) + 1) : ℝ) : ℂ) := by
      have hcast : ((r : ℂ) + 1) = (((r : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
      rw [hcast, ← Complex.ofReal_log (by positivity)]
    rw [hlog, one_div, ← Complex.exp_neg]
    congr 1
    ring
  have hzeta : ∑' r : ℕ, (1 / ((r : ℂ) + 1) ^ (1 + z)) = riemannZeta (1 + z) := by
    have hre : 1 < (1 + z).re := by
      simp [Complex.add_re]
      linarith
    exact (zeta_eq_tsum_one_div_nat_add_one_cpow hre).symm
  have hsum : ∑' r : ℕ, (∫ v in Ioi (0 : ℝ), unitRieszAtomIntegrand z r v)
      = riemannZeta (1 + z) * ((z + 1)⁻¹ - (z + 3 / 2)⁻¹) := by
    rw [tsum_congr hterm, tsum_mul_right, hzeta]
  rw [hpt] at hswap
  rw [hswap] at hsum
  have hfinal : unitRieszLaplace z = 3 * (riemannZeta (1 + z) * ((z + 1)⁻¹ - (z + 3 / 2)⁻¹)) := by
    rw [← hsum]
    ring
  have hkey : ((z + 1)⁻¹ - (z + 3 / 2)⁻¹) * ((z + 1) * (z + 3 / 2)) = 1 / 2 := by
    have h1 : (z + 1)⁻¹ * (z + 1) = 1 := inv_mul_cancel₀ hz1
    have h2 : (z + 3 / 2)⁻¹ * (z + 3 / 2) = 1 := inv_mul_cancel₀ hz32
    calc ((z + 1)⁻¹ - (z + 3 / 2)⁻¹) * ((z + 1) * (z + 3 / 2))
        = ((z + 1)⁻¹ * (z + 1)) * (z + 3 / 2) - ((z + 3 / 2)⁻¹ * (z + 3 / 2)) * (z + 1) := by
          ring
      _ = (z + 3 / 2) - (z + 1) := by rw [h1, h2]; ring
      _ = 1 / 2 := by ring
  rw [hfinal, eq_div_iff (mul_ne_zero hz1 hz32),
    show (3 : ℂ) * (riemannZeta (1 + z) * ((z + 1)⁻¹ - (z + 3 / 2)⁻¹)) * ((z + 1) * (z + 3 / 2))
      = 3 * riemannZeta (1 + z) * (((z + 1)⁻¹ - (z + 3 / 2)⁻¹) * ((z + 1) * (z + 3 / 2)))
      from by ring, hkey]
  ring

/-! ## The Markov transform and the coefficient transform -/

/-- **Equation (7).**  The Markov transform of the unit-Riesz aperture density. -/
def unitRieszMarkovTransform (z : ℂ) : ℂ :=
  3 * z * riemannZeta (1 + z) / (2 * (z + 1) * (z + 3 / 2))

/-- **Equation (7).**  It is `z` times the profile transform, which is what integration by parts
against `w(0) = 0` and `w(∞) = 1` produces. -/
theorem unitRieszMarkovTransform_eq_mul {z : ℂ} (hz : 0 < z.re) :
    unitRieszMarkovTransform z = z * unitRieszLaplace z := by
  have hz1 : (z + 1) ≠ 0 := by
    intro h
    have : (z + 1).re = 0 := by rw [h]; simp
    simp [Complex.add_re] at this
    linarith
  have hz32 : (z + 3 / 2) ≠ 0 := by
    intro h
    have hre : (z + 3 / 2).re = 0 := by rw [h]; simp
    have h32 : ((3 : ℂ) / 2).re = 3 / 2 := by norm_num
    simp [Complex.add_re, h32] at hre
    linarith
  rw [unitRieszLaplace_eq hz, unitRieszMarkovTransform]
  field_simp

/-- **Equation (7), normalization.**  `D(0) = 1`: the unit-Riesz density is a probability law.
The zeta pole at `1` supplies exactly the mass. -/
theorem tendsto_unitRieszMarkovTransform_zero :
    Tendsto unitRieszMarkovTransform (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds 1) := by
  have hshift : Tendsto (fun z : ℂ => 1 + z) (nhdsWithin 0 {(0 : ℂ)}ᶜ)
      (nhdsWithin 1 {(1 : ℂ)}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun z : ℂ => 1 + z) (nhds 0) (nhds (1 + 0)) :=
        tendsto_const_nhds.add tendsto_id
      rw [add_zero] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      exact hz (by simpa using (by linear_combination h : z = 0))
  have hres := riemannZeta_residue_one.comp hshift
  have hres' : Tendsto (fun z : ℂ => z * riemannZeta (1 + z)) (nhdsWithin 0 {(0 : ℂ)}ᶜ)
      (nhds 1) := by
    refine hres.congr fun z => ?_
    simp only [Function.comp_apply, add_sub_cancel_left]
  have hpref : ContinuousAt (fun z : ℂ => 3 / (2 * (z + 1) * (z + 3 / 2))) 0 := by
    refine ContinuousAt.div continuousAt_const (by fun_prop) ?_
    norm_num
  have hden : Tendsto (fun z : ℂ => 3 / (2 * (z + 1) * (z + 3 / 2)))
      (nhdsWithin 0 {(0 : ℂ)}ᶜ) (nhds (3 / (2 * ((0 : ℂ) + 1) * ((0 : ℂ) + 3 / 2)))) :=
    hpref.continuousWithinAt
  have hval : (3 : ℂ) / (2 * ((0 : ℂ) + 1) * ((0 : ℂ) + 3 / 2)) = 1 := by norm_num
  rw [hval] at hden
  have hprod := hden.mul hres'
  rw [one_mul] at hprod
  refine hprod.congr fun z => ?_
  unfold unitRieszMarkovTransform
  ring

/-- **Equation (14).**  The causal transform of the critical Möbius complement. -/
def unitRieszCausalTransform (z : ℂ) : ℂ := (1 + z)⁻¹ - (z * riemannZeta (1 + z))⁻¹

/-- The derivative of the causal transform, off the zeta pole and off the zeta zeros. -/
theorem hasDerivAt_unitRieszCausalTransform {z : ℂ} (hz0 : z ≠ 0) (hz1 : 1 + z ≠ 0)
    (hzeta : riemannZeta (1 + z) ≠ 0) :
    HasDerivAt unitRieszCausalTransform
      (-1 / (1 + z) ^ 2
        + (riemannZeta (1 + z) + z * deriv riemannZeta (1 + z))
          / (z * riemannZeta (1 + z)) ^ 2) z := by
  have hne1 : (1 + z) ≠ 1 := by
    intro h
    exact hz0 (by linear_combination h)
  have hzz : DifferentiableAt ℂ riemannZeta (1 + z) := differentiableAt_riemannZeta hne1
  have hshift : HasDerivAt (fun w : ℂ => 1 + w) 1 z := (hasDerivAt_id z).const_add 1
  have hzcomp : HasDerivAt (fun w : ℂ => riemannZeta (1 + w)) (deriv riemannZeta (1 + z)) z :=
    (hzz.hasDerivAt).comp_const_add 1 z
  have hA : HasDerivAt (fun w : ℂ => (1 + w)⁻¹) (-1 / (1 + z) ^ 2) z := by
    have h := hshift.fun_inv hz1
    simpa using h
  have hprod : HasDerivAt (fun w : ℂ => w * riemannZeta (1 + w))
      (1 * riemannZeta (1 + z) + z * deriv riemannZeta (1 + z)) z :=
    (hasDerivAt_id z).fun_mul hzcomp
  have hpne : z * riemannZeta (1 + z) ≠ 0 := mul_ne_zero hz0 hzeta
  have hB := hprod.fun_inv hpne
  have hsub := hA.fun_sub hB
  refine hsub.congr_deriv ?_
  ring

/-- **Equations (15)–(16).**  The coefficient transform simplifies completely: the probability
multiplier cancels one order of the double reciprocal-zeta virial pole, and what survives is the
logarithmic-derivative pole.  The identity is algebraic in the symbol `Zp = zeta'(1+z)`. -/
theorem unitRieszCoefficientTransform_eq {z Zp : ℂ} (hz0 : z ≠ 0) (hz1 : 1 + z ≠ 0)
    (hzeta : riemannZeta (1 + z) ≠ 0) :
    unitRieszMarkovTransform z
        * (unitRieszCausalTransform z / z
          + (-1 / (1 + z) ^ 2 + (riemannZeta (1 + z) + z * Zp) / (z * riemannZeta (1 + z)) ^ 2))
      = 3 / (2 * (z + 1) * (z + 3 / 2))
        * (riemannZeta (1 + z) / (1 + z) ^ 2 + Zp / riemannZeta (1 + z)) := by
  have hz1' : z + 1 ≠ 0 := by
    intro h
    exact hz1 (by linear_combination h)
  unfold unitRieszMarkovTransform unitRieszCausalTransform
  field_simp
  ring

/-! ## Noncensorship: the residue at an off-critical zero -/

/-- **Equation (17).**  The continued coefficient transform keeps a genuine pole at every
nontrivial zeta zero, with residue `3 m / (2 rho (rho + 1/2))`: the probability multiplier vanishes
to first order there, but the logarithmic-derivative pole survives. -/
theorem tendsto_unitRieszCoefficientResidue {ρ : ℂ} {m : ℂ}
    (hρ0 : ρ ≠ 0) (hρ1 : ρ ≠ 1) (hρ : ρ + 1 / 2 ≠ 0)
    (hlog : Tendsto (fun s : ℂ => (s - ρ) * (deriv riemannZeta s / riemannZeta s))
      (nhdsWithin ρ {ρ}ᶜ) (nhds m)) :
    Tendsto (fun z : ℂ => (z - (ρ - 1))
        * (3 / (2 * (z + 1) * (z + 3 / 2))
          * (riemannZeta (1 + z) / (1 + z) ^ 2
            + deriv riemannZeta (1 + z) / riemannZeta (1 + z))))
      (nhdsWithin (ρ - 1) {ρ - 1}ᶜ) (nhds (3 * m / (2 * ρ * (ρ + 1 / 2)))) := by
  have hshift : Tendsto (fun z : ℂ => 1 + z) (nhdsWithin (ρ - 1) {ρ - 1}ᶜ)
      (nhdsWithin ρ {ρ}ᶜ) := by
    refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_ ?_
    · have h : Tendsto (fun z : ℂ => 1 + z) (nhds (ρ - 1)) (nhds (1 + (ρ - 1))) :=
        tendsto_const_nhds.add tendsto_id
      have hval : (1 : ℂ) + (ρ - 1) = ρ := by ring
      rw [hval] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with z hz
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      intro h
      exact hz (by simpa using (by linear_combination h : z = ρ - 1))
  have hlogshift : Tendsto (fun z : ℂ => (z - (ρ - 1))
      * (deriv riemannZeta (1 + z) / riemannZeta (1 + z)))
      (nhdsWithin (ρ - 1) {ρ - 1}ᶜ) (nhds m) := by
    refine (hlog.comp hshift).congr fun z => ?_
    simp only [Function.comp_apply]
    congr 1
    ring
  have hprefCont : ContinuousAt (fun z : ℂ => 3 / (2 * (z + 1) * (z + 3 / 2))) (ρ - 1) := by
    refine ContinuousAt.div continuousAt_const (by fun_prop) ?_
    have hval : 2 * ((ρ - 1) + 1) * ((ρ - 1) + 3 / 2) = 2 * ρ * (ρ + 1 / 2) := by ring
    rw [hval]
    exact mul_ne_zero (mul_ne_zero two_ne_zero hρ0) hρ
  have hprefLim : Tendsto (fun z : ℂ => 3 / (2 * (z + 1) * (z + 3 / 2)))
      (nhdsWithin (ρ - 1) {ρ - 1}ᶜ) (nhds (3 / (2 * ρ * (ρ + 1 / 2)))) := by
    have h : Tendsto (fun z : ℂ => 3 / (2 * (z + 1) * (z + 3 / 2)))
        (nhdsWithin (ρ - 1) {ρ - 1}ᶜ)
        (nhds (3 / (2 * ((ρ - 1) + 1) * ((ρ - 1) + 3 / 2)))) := hprefCont.continuousWithinAt
    have hval : (3 : ℂ) / (2 * ((ρ - 1) + 1) * ((ρ - 1) + 3 / 2)) = 3 / (2 * ρ * (ρ + 1 / 2)) := by
      congr 1
      ring
    rwa [hval] at h
  have hzero : Tendsto (fun z : ℂ => z - (ρ - 1)) (nhdsWithin (ρ - 1) {ρ - 1}ᶜ) (nhds 0) := by
    have h : Tendsto (fun z : ℂ => z - (ρ - 1)) (nhds (ρ - 1)) (nhds ((ρ - 1) - (ρ - 1))) :=
      tendsto_id.sub tendsto_const_nhds
    rw [sub_self] at h
    exact h.mono_left nhdsWithin_le_nhds
  have hcont : ContinuousAt (fun z : ℂ => riemannZeta (1 + z) / (1 + z) ^ 2) (ρ - 1) := by
    have hne1 : (1 : ℂ) + (ρ - 1) ≠ 1 := by
      intro h
      exact hρ1 (by linear_combination h)
    have hzz : DifferentiableAt ℂ riemannZeta (1 + (ρ - 1)) :=
      differentiableAt_riemannZeta hne1
    have hshiftC : ContinuousAt (fun z : ℂ => (1 : ℂ) + z) (ρ - 1) := by fun_prop
    refine ContinuousAt.div (hzz.continuousAt.comp hshiftC) (by fun_prop) ?_
    have hval : ((1 : ℂ) + (ρ - 1)) ^ 2 = ρ ^ 2 := by
      congr 1
      ring
    rw [hval]
    exact pow_ne_zero 2 hρ0
  have hzetaTerm : Tendsto (fun z : ℂ => (z - (ρ - 1)) * (riemannZeta (1 + z) / (1 + z) ^ 2))
      (nhdsWithin (ρ - 1) {ρ - 1}ᶜ) (nhds 0) := by
    have h := hzero.mul hcont.continuousWithinAt
    rwa [zero_mul] at h
  have hsum := hzetaTerm.add hlogshift
  rw [zero_add] at hsum
  have hfinal := hprefLim.mul hsum
  have hval : (3 : ℂ) / (2 * ρ * (ρ + 1 / 2)) * m = 3 * m / (2 * ρ * (ρ + 1 / 2)) := by ring
  rw [hval] at hfinal
  refine hfinal.congr fun z => ?_
  ring

end GaloisForLFunctions.RHTower

end
