import GaloisForLFunctions.HTGeometry.CanonicalEulerLog
import GaloisForLFunctions.RHTower.ChebyshevPsiScaling
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# The prime-tail co-Poisson interval current

The compact interval seed `g_{n,z}(x) = n^{-z} x^{-z} 1_{[1/n,1]}(x)` is exactly the reflected,
half-density normalized Burnol co-Poisson divided-difference cell, and its right Mellin transform
is the divided difference of `n^{-z}`.  Condensing the seeds against the divided-log prime
coefficients `Λ(n)/log n` produces the all-prime interval current whose Mellin scalarization is the
divided difference of the canonical Euler logarithm.

The normalized dilation and multiplicative inversion act on the divisor monodromy germ
`b_ρ(x) = 2πi m_ρ x^{-ρ}` by the source-inverse character `r^{1/2-ρ}` and on its reflected
conjugate by the analytic-adjoint character `r^{ρ̄-1/2}`; the two coincide in radial type exactly
on the critical line.
-/

namespace RHTower

open MeasureTheory Set intervalIntegral Filter Topology

noncomputable section

/-! ## The compact interval seed and its Mellin transform -/

/-- The compact interval seed `g_{n,z}(x) = n^{-z} x^{-z} 1_{[1/n,1]}(x)`. -/
def primeTailSeed (n : ℕ) (z : ℂ) (x : ℝ) : ℂ :=
  Set.indicator (Set.Icc ((n : ℝ)⁻¹) 1) (fun t : ℝ => (n : ℂ) ^ (-z) * (t : ℂ) ^ (-z)) x

/-- Burnol's centred character cell `γ_{n,ν}(x) = n^{ν-1/2} x^{ν-1} 1_{[1/n,1]}(x)`. -/
def burnolCell (n : ℕ) (ν : ℂ) (x : ℝ) : ℂ :=
  Set.indicator (Set.Icc ((n : ℝ)⁻¹) 1)
    (fun t : ℝ => (n : ℂ) ^ (ν - 1 / 2) * (t : ℂ) ^ (ν - 1)) x

/-- **Card equation (7).**  Each interval seed is exactly the reflected, half-density normalized
Burnol co-Poisson cell. -/
theorem primeTailSeed_eq_burnolCell {n : ℕ} (hn : n ≠ 0) (z : ℂ) (x : ℝ) :
    primeTailSeed n z x = (n : ℂ) ^ (-(1 / 2 : ℂ)) * burnolCell n (1 - z) x := by
  unfold primeTailSeed burnolCell
  have hnc : (n : ℂ) ≠ 0 := by
    simpa using hn
  by_cases hx : x ∈ Set.Icc ((n : ℝ)⁻¹) 1
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      show (1 - z) - 1 / 2 = -z + 1 / 2 from by ring, show (1 - z) - 1 = -z from by ring,
      ← mul_assoc, ← Complex.cpow_add _ _ hnc,
      show -(1 / 2 : ℂ) + (-z + 1 / 2) = -z from by ring]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    ring

/-- **Card equation (5).**  The right Mellin transform of the interval seed is the divided
difference of `n^{-z}`. -/
theorem integral_primeTailSeed {n : ℕ} (hn : 2 ≤ n) {z w : ℂ} (hzw : z ≠ w) :
    (∫ x in ((n : ℝ)⁻¹)..1, primeTailSeed n z x * (x : ℂ) ^ (w - 1))
      = ((n : ℂ) ^ (-w) - (n : ℂ) ^ (-z)) / (z - w) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hninv : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
  have hle : (n : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hn0]
    exact_mod_cast Nat.one_le_of_lt (by omega : 1 < n)
  have hintegrand : ∀ x ∈ Set.uIcc ((n : ℝ)⁻¹) 1,
      primeTailSeed n z x * (x : ℂ) ^ (w - 1) = (n : ℂ) ^ (-z) * (x : ℂ) ^ (w - z - 1) := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le hninv hx.1
    rw [primeTailSeed, Set.indicator_of_mem hx]
    have hxne : (x : ℂ) ≠ 0 := by
      simpa using ne_of_gt hxpos
    rw [mul_assoc, ← Complex.cpow_add _ _ hxne]
    ring_nf
  rw [intervalIntegral.integral_congr hintegrand]
  rw [intervalIntegral.integral_const_mul]
  have hr : w - z - 1 ≠ -1 := by
    intro h
    apply hzw
    have : w - z = 0 := by linear_combination h
    linear_combination -this
  have hzero : (0 : ℝ) ∉ Set.uIcc ((n : ℝ)⁻¹) 1 := by
    rw [Set.uIcc_of_le hle]
    intro hmem
    exact absurd hmem.1 (not_le.mpr hninv)
  rw [integral_cpow (Or.inr ⟨hr, hzero⟩)]
  have hexp : w - z - 1 + 1 = w - z := by ring
  rw [hexp]
  have hone : ((1 : ℝ) : ℂ) ^ (w - z) = 1 := by
    simp
  rw [hone]
  have hinv : (((n : ℝ)⁻¹ : ℝ) : ℂ) = ((n : ℂ))⁻¹ := by push_cast; ring
  rw [hinv]
  have hnc : (n : ℂ) ≠ 0 := by
    simpa using ne_of_gt hn0
  have harg : ((n : ℂ)).arg ≠ Real.pi := by
    have hpos : (0 : ℝ) < (n : ℝ) := hn0
    have : ((n : ℂ)) = ((n : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.arg_ofReal_of_nonneg hpos.le]
    exact ne_of_lt Real.pi_pos
  have hcast : ((n : ℂ))⁻¹ ^ (w - z) = (n : ℂ) ^ (z - w) := by
    rw [Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
    congr 1
    ring
  have hmul : (n : ℂ) ^ (-z) * (n : ℂ) ^ (z - w) = (n : ℂ) ^ (-w) := by
    rw [← Complex.cpow_add _ _ hnc]
    congr 1
    ring
  have hwz : w - z ≠ 0 := fun h => hzw (by linear_combination -h)
  have hzw' : z - w ≠ 0 := fun h => hzw (by linear_combination h)
  rw [hcast]
  field_simp
  linear_combination (w - z) * hmul

/-! ## The divisor monodromy germ and its reflected characters -/

theorem conj_ofReal_cpow {x : ℝ} (hx : 0 < x) (s : ℂ) :
    (starRingEnd ℂ) ((x : ℂ) ^ s) = (x : ℂ) ^ ((starRingEnd ℂ) s) := by
  have hxc : (x : ℂ) ≠ 0 := by simpa using ne_of_gt hx
  rw [Complex.cpow_def_of_ne_zero hxc, Complex.cpow_def_of_ne_zero hxc,
    ← Complex.exp_conj, map_mul]
  congr 2
  rw [← Complex.ofReal_log hx.le]
  exact Complex.conj_ofReal _

/-- The divisor monodromy germ `b_p(x) = 2*pi*i*m*x^{-rho}` of card equation (23). -/
def monodromyGerm (m : ℕ) (rho : ℂ) (x : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I) * (m : ℂ) * (x : ℂ) ^ (-rho)

/-- The `k`-th logarithmic jet of card equation (24). -/
def monodromyGermJet (m : ℕ) (rho : ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  (2 * Real.pi * Complex.I) * (m : ℂ) * (((-Real.log x : ℝ)) : ℂ) ^ k * (x : ℂ) ^ (-rho)

@[simp] theorem monodromyGermJet_zero (m : ℕ) (rho : ℂ) (x : ℝ) :
    monodromyGermJet m rho 0 x = monodromyGerm m rho x := by
  simp [monodromyGermJet, monodromyGerm]

/-- The reflected conjugate germ of card equation (29). -/
def reflectedGerm (m : ℕ) (rho : ℂ) (x : ℝ) : ℂ :=
  -(2 * Real.pi * Complex.I) * (m : ℂ) * (x : ℂ) ^ ((starRingEnd ℂ) rho - 1)

/-- Normalized dilation `(U_r f)(x) = r^{1/2} f(r x)` of card equation (25). -/
def normalizedDilation (r : ℝ) (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  ((Real.sqrt r : ℝ) : ℂ) * f (r * x)

/-- Multiplicative inversion `(I f)(x) = x^{-1} f(x^{-1})` of card equation (28). -/
def multiplicativeInversion (f : ℝ → ℂ) (x : ℝ) : ℂ := ((x : ℂ))⁻¹ * f x⁻¹

theorem ofReal_sqrt_eq_cpow {r : ℝ} (hr : 0 < r) :
    ((Real.sqrt r : ℝ) : ℂ) = (r : ℂ) ^ ((1 : ℂ) / 2) := by
  rw [show ((1 : ℂ) / 2) = (((1 / 2 : ℝ)) : ℂ) from by norm_num,
    ← Complex.ofReal_cpow hr.le]
  norm_cast
  exact Real.sqrt_eq_rpow r

theorem ofReal_mul_cpow {r x : ℝ} (hr : 0 ≤ r) (hx : 0 ≤ x) (s : ℂ) :
    ((r * x : ℝ) : ℂ) ^ s = (r : ℂ) ^ s * (x : ℂ) ^ s := by
  push_cast
  exact Complex.mul_cpow_ofReal_nonneg hr hx s

/-- **Card equations (26)-(27).**  The monodromy germ is a dilation eigenvector with the
source-inverse character `r^{1/2-rho}`. -/
theorem normalizedDilation_monodromyGerm {r : ℝ} (hr : 0 < r) (m : ℕ) (rho : ℂ) (x : ℝ)
    (hx : 0 ≤ x) :
    normalizedDilation r (monodromyGerm m rho) x
      = ((r : ℂ)) ^ ((1 : ℂ) / 2 - rho) * monodromyGerm m rho x := by
  have hrc : (r : ℂ) ≠ 0 := by simpa using ne_of_gt hr
  rw [normalizedDilation, monodromyGerm, monodromyGerm, ofReal_mul_cpow hr.le hx,
    ofReal_sqrt_eq_cpow hr, show ((1 : ℂ) / 2 - rho) = (1 : ℂ) / 2 + (-rho) from by ring,
    Complex.cpow_add _ _ hrc]
  ring

/-- **Card equations (30)-(31).**  The reflected germ is a dilation eigenvector with the
analytic-adjoint character `r^{conj rho - 1/2}`. -/
theorem normalizedDilation_reflectedGerm {r : ℝ} (hr : 0 < r) (m : ℕ) (rho : ℂ) (x : ℝ)
    (hx : 0 ≤ x) :
    normalizedDilation r (reflectedGerm m rho) x
      = ((r : ℂ)) ^ ((starRingEnd ℂ) rho - (1 : ℂ) / 2) * reflectedGerm m rho x := by
  have hrc : (r : ℂ) ≠ 0 := by simpa using ne_of_gt hr
  rw [normalizedDilation, reflectedGerm, reflectedGerm, ofReal_mul_cpow hr.le hx,
    ofReal_sqrt_eq_cpow hr,
    show ((starRingEnd ℂ) rho - (1 : ℂ) / 2) = (1 : ℂ) / 2 + ((starRingEnd ℂ) rho - 1) from by ring,
    Complex.cpow_add _ _ hrc]
  ring

/-- **Card equation (29).**  The reflected conjugate of the monodromy germ under inversion is
exactly the analytic-adjoint germ. -/
theorem multiplicativeInversion_conj_monodromyGerm (m : ℕ) (rho : ℂ) {x : ℝ} (hx : 0 < x) :
    multiplicativeInversion (fun t : ℝ => (starRingEnd ℂ) (monodromyGerm m rho t)) x
      = reflectedGerm m rho x := by
  have hxc : (x : ℂ) ≠ 0 := by simpa using ne_of_gt hx
  have harg : ((x : ℂ)).arg ≠ Real.pi := by
    rw [Complex.arg_ofReal_of_nonneg hx.le]
    exact ne_of_lt Real.pi_pos
  have hinvcast : (((x⁻¹ : ℝ)) : ℂ) = ((x : ℂ))⁻¹ := by push_cast; ring
  have hxinvpos : (0 : ℝ) < x⁻¹ := by positivity
  have hconj : (starRingEnd ℂ) (((x⁻¹ : ℝ) : ℂ) ^ (-rho))
      = ((x⁻¹ : ℝ) : ℂ) ^ (-(starRingEnd ℂ) rho) := by
    rw [conj_ofReal_cpow hxinvpos, map_neg]
  rw [multiplicativeInversion, monodromyGerm, reflectedGerm]
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_natCast, map_ofNat]
  rw [hconj, hinvcast, Complex.inv_cpow _ _ harg, ← Complex.cpow_neg,
    show -(-(starRingEnd ℂ) rho) = (starRingEnd ℂ) rho from by ring,
    show ((starRingEnd ℂ) rho - 1) = -(1 : ℂ) + (starRingEnd ℂ) rho from by ring,
    Complex.cpow_add _ _ hxc, Complex.cpow_neg_one]
  ring

/-- **The two characters coincide in radial type exactly on the critical line.** -/
theorem dilation_characters_eq_iff (rho : ℂ) :
    ((1 : ℝ) / 2 - rho.re = rho.re - 1 / 2) ↔ rho.re = 1 / 2 := by
  constructor <;> intro h <;> linarith

/-! ## The all-prime condensation -/

/-- **Card equation (3).**  The all-prime interval current
`G_z(x) = sum_{n} a_n g_{n,z}(x)` with `a_n = Lambda(n)/log n`. -/
def primeTailCurrent (z : ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, eulerLogDirichletCoeff n * primeTailSeed n z x

theorem norm_primeTailSeed {n : ℕ} (hn : 2 ≤ n) (z : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖primeTailSeed n z x‖
      = Set.indicator (Set.Icc ((n : ℝ)⁻¹) 1)
          (fun t : ℝ => (n : ℝ) ^ (-z.re) * t ^ (-z.re)) x := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  by_cases hmem : x ∈ Set.Icc ((n : ℝ)⁻¹) 1
  · rw [primeTailSeed, Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, norm_mul,
      Complex.norm_natCast_cpow_of_pos (by omega), Complex.norm_cpow_eq_rpow_re_of_pos hx,
      Complex.neg_re]
  · rw [primeTailSeed, Set.indicator_of_notMem hmem, Set.indicator_of_notMem hmem, norm_zero]

/-- The pointwise majorant of a single condensation term on the unit interval. -/
theorem norm_primeTailSeed_mul_le {n : ℕ} (hn : 2 ≤ n) (z w : ℂ) {x : ℝ}
    (hx : 0 < x) (hx1 : x ≤ 1) :
    ‖primeTailSeed n z x * (x : ℂ) ^ (w - 1)‖
      ≤ ((n : ℝ) ^ (-z.re) + (n : ℝ) ^ (-w.re))
        * Set.indicator (Set.Icc ((n : ℝ)⁻¹) 1) (fun t : ℝ => t⁻¹) x := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hpow1 : (0 : ℝ) < (n : ℝ) ^ (-z.re) := Real.rpow_pos_of_pos hn0 _
  have hpow2 : (0 : ℝ) < (n : ℝ) ^ (-w.re) := Real.rpow_pos_of_pos hn0 _
  by_cases hmem : x ∈ Set.Icc ((n : ℝ)⁻¹) 1
  · rw [norm_mul, primeTailSeed, Set.indicator_of_mem hmem, norm_mul,
      Complex.norm_natCast_cpow_of_pos (by omega), Complex.norm_cpow_eq_rpow_re_of_pos hx,
      Complex.norm_cpow_eq_rpow_re_of_pos hx, Complex.neg_re]
    have hsplit : x ^ (-z.re) * x ^ ((w - 1).re) = x ^ (w.re - z.re) * x⁻¹ := by
      rw [← Real.rpow_add hx, Complex.sub_re, Complex.one_re,
        show -z.re + (w.re - 1) = (w.re - z.re) + (-1) from by ring,
        Real.rpow_add hx, Real.rpow_neg_one]
    rw [Set.indicator_of_mem hmem, mul_assoc, hsplit, ← mul_assoc]
    have hkey : (n : ℝ) ^ (-z.re) * x ^ (w.re - z.re)
        ≤ (n : ℝ) ^ (-z.re) + (n : ℝ) ^ (-w.re) := by
      rcases lt_or_ge (w.re - z.re) 0 with hc | hc
      · have hinvpos : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
        have hxinv : x ^ (w.re - z.re) ≤ ((n : ℝ)⁻¹) ^ (w.re - z.re) :=
          Real.rpow_le_rpow_of_nonpos hinvpos hmem.1 hc.le
        have hrw : ((n : ℝ)⁻¹) ^ (w.re - z.re) = (n : ℝ) ^ (-(w.re - z.re)) := by
          rw [Real.inv_rpow hn0.le, ← Real.rpow_neg hn0.le]
        rw [hrw] at hxinv
        have hcomb : (n : ℝ) ^ (-z.re) * (n : ℝ) ^ (-(w.re - z.re)) = (n : ℝ) ^ (-w.re) := by
          rw [← Real.rpow_add hn0]
          congr 1
          ring
        nlinarith [hpow1, hpow2, hxinv, hcomb]
      · have hxc : x ^ (w.re - z.re) ≤ 1 := Real.rpow_le_one hx.le hx1 hc
        nlinarith [hpow1, hpow2]
    exact mul_le_mul_of_nonneg_right hkey (by positivity)
  · rw [primeTailSeed, Set.indicator_of_notMem hmem, zero_mul, norm_zero,
      Set.indicator_of_notMem hmem, mul_zero]

/-! ## Summability of the majorant -/

theorem summable_rpow_neg {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (n : ℝ) ^ (-σ)) := by
  rw [Real.summable_nat_rpow]
  linarith

theorem summable_rpow_neg_mul_log {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ => (n : ℝ) ^ (-σ) * Real.log n) := by
  set δ : ℝ := (σ - 1) / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hmaj : Summable (fun n : ℕ => δ⁻¹ * (n : ℝ) ^ (δ - σ)) :=
    (summable_rpow_neg (σ := σ - δ) (by rw [hδ]; linarith)).congr (fun n => by
      rw [show -(σ - δ) = δ - σ from by ring]) |>.mul_left _
  refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hmaj
  · have h1 : (0 : ℝ) ≤ (n : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg n) _
    have h2 : (0 : ℝ) ≤ Real.log n := Real.log_natCast_nonneg n
    positivity
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp
      positivity
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hnpos : (0 : ℝ) < (n : ℝ) := by linarith
      have hlog : Real.log n ≤ (n : ℝ) ^ δ / δ := Real.log_le_rpow_div hnpos.le hδpos
      have hsplit : (n : ℝ) ^ (-σ) * ((n : ℝ) ^ δ / δ) = δ⁻¹ * (n : ℝ) ^ (δ - σ) := by
        have hadd : (n : ℝ) ^ (-σ) * (n : ℝ) ^ δ = (n : ℝ) ^ (δ - σ) := by
          rw [← Real.rpow_add hnpos]
          congr 1
          ring
        field_simp
        linear_combination hadd
      calc (n : ℝ) ^ (-σ) * Real.log n
          ≤ (n : ℝ) ^ (-σ) * ((n : ℝ) ^ δ / δ) :=
            mul_le_mul_of_nonneg_left hlog (Real.rpow_nonneg hnpos.le _)
        _ = δ⁻¹ * (n : ℝ) ^ (δ - σ) := hsplit

theorem summable_primeTail_majorant {σ τ : ℝ} (hσ : 1 < σ) (hτ : 1 < τ) :
    Summable (fun n : ℕ => ((n : ℝ) ^ (-σ) + (n : ℝ) ^ (-τ)) * Real.log n) := by
  have h1 := summable_rpow_neg_mul_log hσ
  have h2 := summable_rpow_neg_mul_log hτ
  refine (h1.add h2).congr (fun n => ?_)
  ring

/-! ## Integrability of a single condensation term -/

theorem measurable_ofReal_cpow (s : ℂ) :
    Measurable (fun x : ℝ => (x : ℂ) ^ s) := by
  have hmeas : Measurable (fun x : ℝ => ((x : ℂ))) := Complex.measurable_ofReal
  exact hmeas.pow_const s

theorem aestronglyMeasurable_primeTailTerm (n : ℕ) (z w : ℂ) :
    AEStronglyMeasurable
      (fun x : ℝ => primeTailSeed n z x * (x : ℂ) ^ (w - 1))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
  refine AEStronglyMeasurable.mul ?_ ?_
  · refine (Measurable.aestronglyMeasurable ?_)
    unfold primeTailSeed
    exact (((measurable_ofReal_cpow (-z)).const_mul _).indicator measurableSet_Icc)
  · exact (measurable_ofReal_cpow (w - 1)).aestronglyMeasurable

theorem integral_indicator_inv {n : ℕ} (hn : 2 ≤ n) :
    ∫ x in Set.Ioc (0 : ℝ) 1,
        Set.indicator (Set.Icc ((n : ℝ)⁻¹) 1) (fun t : ℝ => t⁻¹) x = Real.log n := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hninv : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
  have hle : (n : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hn0]
    exact_mod_cast Nat.one_le_of_lt (by omega : 1 < n)
  have hsub : Set.Icc ((n : ℝ)⁻¹) 1 ∩ Set.Ioc (0 : ℝ) 1 = Set.Icc ((n : ℝ)⁻¹) 1 := by
    apply Set.inter_eq_self_of_subset_left
    intro x hx
    exact ⟨lt_of_lt_of_le hninv hx.1, hx.2⟩
  rw [MeasureTheory.integral_indicator measurableSet_Icc, Measure.restrict_restrict measurableSet_Icc,
    hsub]
  have hIcc : ∫ x in Set.Icc ((n : ℝ)⁻¹) 1, x⁻¹ = ∫ x in ((n : ℝ)⁻¹)..1, x⁻¹ := by
    rw [intervalIntegral.integral_of_le hle, MeasureTheory.integral_Icc_eq_integral_Ioc]
  rw [hIcc]
  have hzero : (0 : ℝ) ∉ Set.uIcc ((n : ℝ)⁻¹) 1 := by
    rw [Set.uIcc_of_le hle]
    intro hmem
    exact absurd hmem.1 (not_le.mpr hninv)
  rw [integral_inv hzero]
  rw [one_div, inv_inv]

theorem integrableOn_indicator_inv {n : ℕ} (hn : 2 ≤ n) :
    IntegrableOn
      (fun x : ℝ => Set.indicator (Set.Icc ((n : ℝ)⁻¹) 1) (fun t : ℝ => t⁻¹) x)
      (Set.Ioc (0 : ℝ) 1) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hninv : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
  have hcont : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc ((n : ℝ)⁻¹) 1) := by
    intro x hx
    exact (continuousAt_inv₀ (ne_of_gt (lt_of_lt_of_le hninv hx.1))).continuousWithinAt
  have hint : IntegrableOn (fun t : ℝ => t⁻¹) (Set.Icc ((n : ℝ)⁻¹) 1) :=
    hcont.integrableOn_compact isCompact_Icc
  have hglob : Integrable
      (fun x : ℝ => Set.indicator (Set.Icc ((n : ℝ)⁻¹) 1) (fun t : ℝ => t⁻¹) x) volume :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Icc).mpr hint
  exact hglob.integrableOn

/-- A single condensation term is integrable on the unit interval. -/
theorem integrableOn_primeTailTerm {n : ℕ} (hn : 2 ≤ n) (z w : ℂ) :
    IntegrableOn (fun x : ℝ => primeTailSeed n z x * (x : ℂ) ^ (w - 1))
      (Set.Ioc (0 : ℝ) 1) := by
  refine MeasureTheory.Integrable.mono'
    (((integrableOn_indicator_inv hn).const_mul
      ((n : ℝ) ^ (-z.re) + (n : ℝ) ^ (-w.re))))
    (aestronglyMeasurable_primeTailTerm n z w) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
  exact norm_primeTailSeed_mul_le hn z w hx.1 hx.2

/-- The `L¹` mass of a single condensation term is at most `(n^{-σ}+n^{-τ}) log n`. -/
theorem integral_norm_primeTailTerm_le {n : ℕ} (hn : 2 ≤ n) (z w : ℂ) :
    ∫ x in Set.Ioc (0 : ℝ) 1, ‖primeTailSeed n z x * (x : ℂ) ^ (w - 1)‖
      ≤ ((n : ℝ) ^ (-z.re) + (n : ℝ) ^ (-w.re)) * Real.log n := by
  have hmono : ∫ x in Set.Ioc (0 : ℝ) 1, ‖primeTailSeed n z x * (x : ℂ) ^ (w - 1)‖
      ≤ ∫ x in Set.Ioc (0 : ℝ) 1,
          ((n : ℝ) ^ (-z.re) + (n : ℝ) ^ (-w.re))
            * Set.indicator (Set.Icc ((n : ℝ)⁻¹) 1) (fun t : ℝ => t⁻¹) x := by
    refine MeasureTheory.integral_mono_of_nonneg (by
      filter_upwards with x using norm_nonneg _)
      (((integrableOn_indicator_inv hn).const_mul
        ((n : ℝ) ^ (-z.re) + (n : ℝ) ^ (-w.re)))) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
    exact norm_primeTailSeed_mul_le hn z w hx.1 hx.2
  refine le_trans hmono (le_of_eq ?_)
  rw [MeasureTheory.integral_const_mul, integral_indicator_inv hn]

/-! ## The Mellin scalarization -/

theorem setIntegral_Ioc_indicator {n : ℕ} (hn : 2 ≤ n) (g : ℝ → ℂ) :
    ∫ x in Set.Ioc (0 : ℝ) 1, Set.indicator (Set.Icc ((n : ℝ)⁻¹) 1) g x
      = ∫ x in ((n : ℝ)⁻¹)..1, g x := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hninv : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
  have hle : (n : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hn0]
    exact_mod_cast Nat.one_le_of_lt (by omega : 1 < n)
  have hsub : Set.Icc ((n : ℝ)⁻¹) 1 ∩ Set.Ioc (0 : ℝ) 1 = Set.Icc ((n : ℝ)⁻¹) 1 := by
    apply Set.inter_eq_self_of_subset_left
    intro x hx
    exact ⟨lt_of_lt_of_le hninv hx.1, hx.2⟩
  rw [MeasureTheory.integral_indicator measurableSet_Icc,
    Measure.restrict_restrict measurableSet_Icc, hsub,
    intervalIntegral.integral_of_le hle, MeasureTheory.integral_Icc_eq_integral_Ioc]

theorem primeTailSeed_mul_eq_indicator (n : ℕ) (z w : ℂ) (x : ℝ) :
    primeTailSeed n z x * (x : ℂ) ^ (w - 1)
      = Set.indicator (Set.Icc ((n : ℝ)⁻¹) 1)
          (fun t : ℝ => (n : ℂ) ^ (-z) * (t : ℂ) ^ (-z) * (t : ℂ) ^ (w - 1)) x := by
  unfold primeTailSeed
  by_cases hx : x ∈ Set.Icc ((n : ℝ)⁻¹) 1
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, zero_mul]

theorem integral_primeTailTerm {n : ℕ} (hn : 2 ≤ n) {z w : ℂ} (hzw : z ≠ w) :
    (∫ x in Set.Ioc (0 : ℝ) 1, primeTailSeed n z x * (x : ℂ) ^ (w - 1))
      = ((n : ℂ) ^ (-w) - (n : ℂ) ^ (-z)) / (z - w) := by
  rw [MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall (fun x => primeTailSeed_mul_eq_indicator n z w x)),
    setIntegral_Ioc_indicator hn]
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hle : (n : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hn0]
    exact_mod_cast Nat.one_le_of_lt (by omega : 1 < n)
  rw [← integral_primeTailSeed hn hzw]
  refine intervalIntegral.integral_congr (fun x hx => ?_)
  rw [Set.uIcc_of_le hle] at hx
  rw [primeTailSeed_mul_eq_indicator n z w x, Set.indicator_of_mem hx]

theorem eulerLogDirichletCoeff_eq_zero_of_lt_two {n : ℕ} (hn : n < 2) :
    eulerLogDirichletCoeff n = 0 := by
  interval_cases n
  · exact eulerLogDirichletCoeff_zero
  · exact eulerLogDirichletCoeff_one

theorem integrableOn_primeTailFullTerm (n : ℕ) {z w : ℂ} :
    IntegrableOn
      (fun x : ℝ => eulerLogDirichletCoeff n * (primeTailSeed n z x * (x : ℂ) ^ (w - 1)))
      (Set.Ioc (0 : ℝ) 1) := by
  rcases lt_or_ge n 2 with hn | hn
  · rw [eulerLogDirichletCoeff_eq_zero_of_lt_two hn]
    simp
  · exact (integrableOn_primeTailTerm hn z w).const_mul _

theorem integral_norm_primeTailFullTerm_le (n : ℕ) (z w : ℂ) :
    ∫ x in Set.Ioc (0 : ℝ) 1,
        ‖eulerLogDirichletCoeff n * (primeTailSeed n z x * (x : ℂ) ^ (w - 1))‖
      ≤ ((n : ℝ) ^ (-z.re) + (n : ℝ) ^ (-w.re)) * Real.log n := by
  rcases lt_or_ge n 2 with hn | hn
  · rw [eulerLogDirichletCoeff_eq_zero_of_lt_two hn]
    simp only [zero_mul, norm_zero, MeasureTheory.integral_zero]
    interval_cases n <;> simp
  · have hcoef : ∀ x : ℝ,
        ‖eulerLogDirichletCoeff n * (primeTailSeed n z x * (x : ℂ) ^ (w - 1))‖
          ≤ ‖primeTailSeed n z x * (x : ℂ) ^ (w - 1)‖ := by
      intro x
      rw [norm_mul]
      exact mul_le_of_le_one_left (norm_nonneg _) (norm_eulerLogDirichletCoeff_le_one n)
    refine le_trans ?_ (integral_norm_primeTailTerm_le hn z w)
    refine MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun x => norm_nonneg _))
      (integrableOn_primeTailTerm hn z w).norm
      (Filter.Eventually.of_forall hcoef)

/-- **Card equation (8).**  The right Mellin transform of the all-prime interval current is the
divided difference of the canonical Euler logarithm. -/
theorem primeTailCurrent_mellin {z w : ℂ} (hz : 1 < z.re) (hw : 1 < w.re) (hzw : z ≠ w) :
    (∫ x in Set.Ioc (0 : ℝ) 1, primeTailCurrent z x * (x : ℂ) ^ (w - 1))
      = (canonicalEulerLogZeta z - canonicalEulerLogZeta w) / (w - z) := by
  have hzw' : z - w ≠ 0 := fun h => hzw (by linear_combination h)
  have hwz : w - z ≠ 0 := fun h => hzw (by linear_combination -h)
  have hsum : Summable (fun n : ℕ =>
      ∫ x in Set.Ioc (0 : ℝ) 1,
        ‖eulerLogDirichletCoeff n * (primeTailSeed n z x * (x : ℂ) ^ (w - 1))‖) := by
    refine Summable.of_nonneg_of_le (fun n => MeasureTheory.integral_nonneg
      (fun x => norm_nonneg _)) (fun n => integral_norm_primeTailFullTerm_le n z w)
      (summable_primeTail_majorant hz hw)
  have hpoint : ∀ x : ℝ, primeTailCurrent z x * (x : ℂ) ^ (w - 1)
      = ∑' n : ℕ, eulerLogDirichletCoeff n * (primeTailSeed n z x * (x : ℂ) ^ (w - 1)) := by
    intro x
    rw [primeTailCurrent, ← tsum_mul_right]
    exact tsum_congr (fun n => by ring)
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint),
    ← MeasureTheory.integral_tsum_of_summable_integral_norm
      (fun n => integrableOn_primeTailFullTerm n) hsum]
  have hterm : ∀ n : ℕ,
      (∫ x in Set.Ioc (0 : ℝ) 1,
          eulerLogDirichletCoeff n * (primeTailSeed n z x * (x : ℂ) ^ (w - 1)))
        = eulerLogDirichletCoeff n * (((n : ℂ) ^ (-w) - (n : ℂ) ^ (-z)) / (z - w)) := by
    intro n
    rcases lt_or_ge n 2 with hn | hn
    · rw [eulerLogDirichletCoeff_eq_zero_of_lt_two hn]
      simp
    · rw [MeasureTheory.integral_const_mul, integral_primeTailTerm hn hzw]
  rw [tsum_congr hterm]
  have hsplit : ∀ n : ℕ,
      eulerLogDirichletCoeff n * (((n : ℂ) ^ (-w) - (n : ℂ) ^ (-z)) / (z - w))
        = (z - w)⁻¹ * (LSeries.term eulerLogDirichletCoeff w n
            - LSeries.term eulerLogDirichletCoeff z n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn0, LSeries.term_of_ne_zero hn0]
      have hnc : (n : ℂ) ≠ 0 := by simpa using hn0
      rw [Complex.cpow_neg, Complex.cpow_neg]
      field_simp
  rw [tsum_congr hsplit, tsum_mul_left,
    (canonicalEulerLogZeta_summable hw).tsum_sub (canonicalEulerLogZeta_summable hz)]
  show (z - w)⁻¹ * (canonicalEulerLogZeta w - canonicalEulerLogZeta z) = _
  field_simp
  ring

/-! ## The diagonal value -/

theorem integral_primeTailSeed_diag {n : ℕ} (hn : 2 ≤ n) (z : ℂ) :
    (∫ x in ((n : ℝ)⁻¹)..1, primeTailSeed n z x * (x : ℂ) ^ (z - 1))
      = (n : ℂ) ^ (-z) * (Real.log n : ℂ) := by
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hninv : (0 : ℝ) < (n : ℝ)⁻¹ := by positivity
  have hle : (n : ℝ)⁻¹ ≤ 1 := by
    rw [inv_le_one₀ hn0]
    exact_mod_cast Nat.one_le_of_lt (by omega : 1 < n)
  have hcongr : ∀ x ∈ Set.uIcc ((n : ℝ)⁻¹) 1,
      primeTailSeed n z x * (x : ℂ) ^ (z - 1) = (n : ℂ) ^ (-z) * ((x : ℂ))⁻¹ := by
    intro x hx
    rw [Set.uIcc_of_le hle] at hx
    have hxpos : (0 : ℝ) < x := lt_of_lt_of_le hninv hx.1
    have hxne : (x : ℂ) ≠ 0 := by simpa using ne_of_gt hxpos
    rw [primeTailSeed, Set.indicator_of_mem hx, mul_assoc, ← Complex.cpow_add _ _ hxne,
      show -z + (z - 1) = -(1 : ℂ) from by ring, Complex.cpow_neg_one]
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_const_mul]
  have hzero : (0 : ℝ) ∉ Set.uIcc ((n : ℝ)⁻¹) 1 := by
    rw [Set.uIcc_of_le hle]
    intro hmem
    exact absurd hmem.1 (not_le.mpr hninv)
  have hcomplex : (∫ x in ((n : ℝ)⁻¹)..1, ((x : ℂ))⁻¹)
      = ((∫ x in ((n : ℝ)⁻¹)..1, x⁻¹ : ℝ) : ℂ) := by
    rw [← intervalIntegral.integral_ofReal]
    exact intervalIntegral.integral_congr (fun x hx => by push_cast; ring)
  rw [hcomplex, integral_inv hzero, one_div, inv_inv]

theorem eulerLogDirichletCoeff_mul_log {n : ℕ} (hn : 2 ≤ n) :
    eulerLogDirichletCoeff n * (Real.log n : ℂ)
      = (ArithmeticFunction.vonMangoldt n : ℂ) := by
  have hn1 : (1 : ℝ) < (n : ℝ) := by
    have : 1 < n := by omega
    exact_mod_cast this
  have hlogR : Real.log n ≠ 0 := ne_of_gt (Real.log_pos hn1)
  have hlogne : ((Real.log n : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hlogR
  rw [eulerLogDirichletCoeff, ← Complex.natCast_log]
  field_simp

/-- **Card equation (9).**  The diagonal value of the Mellin scalarization is the von Mangoldt
Dirichlet series, that is minus the logarithmic derivative of zeta. -/
theorem primeTailCurrent_mellin_diag {z : ℂ} (hz : 1 < z.re) :
    (∫ x in Set.Ioc (0 : ℝ) 1, primeTailCurrent z x * (x : ℂ) ^ (z - 1))
      = LSeries (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) z := by
  have hsum : Summable (fun n : ℕ =>
      ∫ x in Set.Ioc (0 : ℝ) 1,
        ‖eulerLogDirichletCoeff n * (primeTailSeed n z x * (x : ℂ) ^ (z - 1))‖) := by
    refine Summable.of_nonneg_of_le (fun n => MeasureTheory.integral_nonneg
      (fun x => norm_nonneg _)) (fun n => integral_norm_primeTailFullTerm_le n z z)
      (summable_primeTail_majorant hz hz)
  have hpoint : ∀ x : ℝ, primeTailCurrent z x * (x : ℂ) ^ (z - 1)
      = ∑' n : ℕ, eulerLogDirichletCoeff n * (primeTailSeed n z x * (x : ℂ) ^ (z - 1)) := by
    intro x
    rw [primeTailCurrent, ← tsum_mul_right]
    exact tsum_congr (fun n => by ring)
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hpoint),
    ← MeasureTheory.integral_tsum_of_summable_integral_norm
      (fun n => integrableOn_primeTailFullTerm n) hsum]
  have hterm : ∀ n : ℕ,
      (∫ x in Set.Ioc (0 : ℝ) 1,
          eulerLogDirichletCoeff n * (primeTailSeed n z x * (x : ℂ) ^ (z - 1)))
        = LSeries.term (fun n => (ArithmeticFunction.vonMangoldt n : ℂ)) z n := by
    intro n
    rcases lt_or_ge n 2 with hn | hn
    · rw [eulerLogDirichletCoeff_eq_zero_of_lt_two hn]
      interval_cases n <;> simp [LSeries.term]
    · have hn0 : n ≠ 0 := by omega
      have hnc : (n : ℂ) ≠ 0 := by simpa using hn0
      rw [MeasureTheory.integral_const_mul,
        MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall (fun x => primeTailSeed_mul_eq_indicator n z z x)),
        setIntegral_Ioc_indicator hn]
      have hback : (∫ x in ((n : ℝ)⁻¹)..1,
            (n : ℂ) ^ (-z) * (x : ℂ) ^ (-z) * (x : ℂ) ^ (z - 1))
          = (n : ℂ) ^ (-z) * (Real.log n : ℂ) := by
        rw [← integral_primeTailSeed_diag hn z]
        have hn0' : (0 : ℝ) < (n : ℝ) := by
          have : (0 : ℕ) < n := by omega
          exact_mod_cast this
        have hle : (n : ℝ)⁻¹ ≤ 1 := by
          rw [inv_le_one₀ hn0']
          exact_mod_cast Nat.one_le_of_lt (by omega : 1 < n)
        refine intervalIntegral.integral_congr (fun x hx => ?_)
        rw [Set.uIcc_of_le hle] at hx
        rw [primeTailSeed_mul_eq_indicator n z z x, Set.indicator_of_mem hx]
      rw [hback, LSeries.term_of_ne_zero hn0, ← eulerLogDirichletCoeff_mul_log hn,
        Complex.cpow_neg]
      field_simp
  rw [tsum_congr hterm]
  rfl

/-! ## The divisor Bockstein -/

/-- The finite single-valued part of the current: the coefficients removed by the cutoff `n x < 1`.
It is a finite sum, hence an entire function of `z`. -/
def primeTailFinitePart (x : ℝ) (z : ℂ) : ℂ :=
  ∑ n ∈ Finset.range ⌈x⁻¹⌉₊, eulerLogDirichletCoeff n * (n : ℂ) ^ (-z)

/-- **Card equation (24).**  Every logarithmic jet of the homogeneous monodromy germ. -/
theorem iteratedDeriv_monodromyGerm {x : ℝ} (hx : 0 < x) (m : ℕ) (k : ℕ) (rho : ℂ) :
    iteratedDeriv k (fun z : ℂ => (2 * Real.pi * Complex.I) * (m : ℂ) * (x : ℂ) ^ (-z)) rho
      = monodromyGermJet m rho k x := by
  have hxc : (x : ℂ) ≠ 0 := by simpa using ne_of_gt hx
  have hlog : Complex.log (x : ℂ) = ((Real.log x : ℝ) : ℂ) := by
    rw [← Complex.ofReal_log hx.le]
  have hderiv : ∀ j : ℕ,
      iteratedDeriv j (fun z : ℂ => (2 * Real.pi * Complex.I) * (m : ℂ) * (x : ℂ) ^ (-z))
        = fun z : ℂ => (2 * Real.pi * Complex.I) * (m : ℂ)
            * ((-(Real.log x : ℝ) : ℝ) : ℂ) ^ j * (x : ℂ) ^ (-z) := by
    intro j
    induction j with
    | zero => funext z; simp
    | succ j ih =>
        rw [iteratedDeriv_succ, ih]
        funext z
        have hd : HasDerivAt (fun t : ℂ => (x : ℂ) ^ (-t))
            (-(Complex.log (x : ℂ)) * (x : ℂ) ^ (-z)) z := by
          have harg : ((x : ℂ)).arg ≠ Real.pi := by
            rw [Complex.arg_ofReal_of_nonneg hx.le]
            exact ne_of_lt Real.pi_pos
          have h := (Complex.hasStrictDerivAt_const_cpow (x := ((x : ℂ))⁻¹) (y := z)
            (Or.inl (inv_ne_zero hxc))).hasDerivAt
          have heq : (fun t : ℂ => ((x : ℂ)⁻¹) ^ t) = (fun t : ℂ => (x : ℂ) ^ (-t)) := by
            funext t
            rw [Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
          have hval : ((x : ℂ)⁻¹) ^ z = (x : ℂ) ^ (-z) := by
            rw [Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
          rw [heq, hval, Complex.log_inv _ harg] at h
          simpa [mul_comm] using h
        have hfull : HasDerivAt (fun t : ℂ => (2 * Real.pi * Complex.I) * (m : ℂ)
              * ((-(Real.log x : ℝ) : ℝ) : ℂ) ^ j * (x : ℂ) ^ (-t))
            ((2 * Real.pi * Complex.I) * (m : ℂ) * ((-(Real.log x : ℝ) : ℝ) : ℂ) ^ j
              * (-(Complex.log (x : ℂ)) * (x : ℂ) ^ (-z))) z :=
          hd.const_mul _
        rw [hfull.deriv, hlog]
        push_cast
        ring
  rw [hderiv k, monodromyGermJet]

theorem primeTailSeed_eq_of_mem_range {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : 0 < x) (_hx1 : x ≤ 1)
    (hmem : n ∈ Finset.range ⌈x⁻¹⌉₊) (z : ℂ) : primeTailSeed n z x = 0 := by
  rw [Finset.mem_range, Nat.lt_ceil] at hmem
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have : 0 < n := Nat.pos_of_ne_zero hn
    exact_mod_cast this
  refine Set.indicator_of_notMem ?_ _
  intro hx'
  have hle : (n : ℝ)⁻¹ ≤ x := (Set.mem_Icc.mp hx').1
  rw [inv_le_comm₀ hn0 hx] at hle
  linarith

theorem primeTailSeed_eq_of_notMem_range {n : ℕ} {x : ℝ} (hx : 0 < x) (hx1 : x ≤ 1)
    (hmem : n ∉ Finset.range ⌈x⁻¹⌉₊) (z : ℂ) :
    primeTailSeed n z x = (n : ℂ) ^ (-z) * (x : ℂ) ^ (-z) := by
  rw [Finset.mem_range, Nat.lt_ceil, not_lt] at hmem
  have hxpos : (0 : ℝ) < x⁻¹ := by positivity
  have hn0 : (0 : ℝ) < (n : ℝ) := lt_of_lt_of_le hxpos hmem
  refine Set.indicator_of_mem (Set.mem_Icc.mpr ⟨?_, hx1⟩) _
  rw [inv_le_comm₀ hn0 hx]
  exact hmem

/-- **Card equation (21).**  All branch monodromy of the current comes from the canonical Euler
logarithm: the removed part is a finite, single-valued, entire function of `z`. -/
theorem primeTailCurrent_eq_finitePart {z : ℂ} (hz : 1 < z.re) {x : ℝ} (hx : 0 < x)
    (hx1 : x ≤ 1) :
    primeTailCurrent z x
      = (x : ℂ) ^ (-z) * (canonicalEulerLogZeta z - primeTailFinitePart x z) := by
  have hsummable : Summable (fun n : ℕ => LSeries.term eulerLogDirichletCoeff z n) :=
    canonicalEulerLogZeta_summable hz
  have hterm : ∀ n : ℕ, eulerLogDirichletCoeff n * (n : ℂ) ^ (-z)
      = LSeries.term eulerLogDirichletCoeff z n := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [LSeries.term_zero]
    · rw [LSeries.term_of_ne_zero hn0, Complex.cpow_neg, div_eq_mul_inv]
  have hsum2 : Summable (fun n : ℕ => eulerLogDirichletCoeff n * (n : ℂ) ^ (-z)) :=
    hsummable.congr (fun n => (hterm n).symm)
  have hdecomp : ∀ n : ℕ, eulerLogDirichletCoeff n * primeTailSeed n z x
      = (x : ℂ) ^ (-z) * ((eulerLogDirichletCoeff n * (n : ℂ) ^ (-z))
        - Set.indicator (↑(Finset.range ⌈x⁻¹⌉₊))
            (fun m : ℕ => eulerLogDirichletCoeff m * (m : ℂ) ^ (-z)) n) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · have hz0 : eulerLogDirichletCoeff 0 = 0 := eulerLogDirichletCoeff_zero
      have hmem0 : (0 : ℕ) ∈ Finset.range ⌈x⁻¹⌉₊ := by
        rw [Finset.mem_range, Nat.lt_ceil]
        simpa using by positivity
      rw [hz0, Set.indicator_of_mem (by exact_mod_cast hmem0)]
      simp [hz0]
    by_cases hmem : n ∈ Finset.range ⌈x⁻¹⌉₊
    · rw [primeTailSeed_eq_of_mem_range hn0 hx hx1 hmem z,
        Set.indicator_of_mem (by exact_mod_cast hmem)]
      ring
    · rw [primeTailSeed_eq_of_notMem_range hx hx1 hmem z,
        Set.indicator_of_notMem (by exact_mod_cast hmem)]
      ring
  have hindsum : ∑' n : ℕ, Set.indicator (↑(Finset.range ⌈x⁻¹⌉₊))
        (fun m : ℕ => eulerLogDirichletCoeff m * (m : ℂ) ^ (-z)) n
      = primeTailFinitePart x z := by
    rw [tsum_eq_sum (s := Finset.range ⌈x⁻¹⌉₊) (fun i hi => Set.indicator_of_notMem
      (by exact_mod_cast hi) _)]
    exact Finset.sum_congr rfl (fun i hi => Set.indicator_of_mem (by exact_mod_cast hi) _)
  have hindsummable : Summable (fun n : ℕ => Set.indicator (↑(Finset.range ⌈x⁻¹⌉₊))
      (fun m : ℕ => eulerLogDirichletCoeff m * (m : ℂ) ^ (-z)) n) := by
    refine summable_of_hasFiniteSupport ?_
    refine Set.Finite.subset (Finset.range ⌈x⁻¹⌉₊).finite_toSet ?_
    intro n hn
    by_contra hcon
    exact hn (Set.indicator_of_notMem (by exact_mod_cast hcon) _)
  rw [primeTailCurrent, tsum_congr hdecomp, tsum_mul_left, hsum2.tsum_sub hindsummable,
    hindsum]
  congr 1
  congr 1
  rw [canonicalEulerLogZeta, LSeries]
  exact tsum_congr hterm

/-- The removed finite part is an entire function of the spectral parameter, hence single
valued: it contributes no monodromy. -/
theorem differentiable_primeTailFinitePart (x : ℝ) :
    Differentiable ℂ (primeTailFinitePart x) := by
  unfold primeTailFinitePart
  have hfun : (fun z : ℂ => ∑ n ∈ Finset.range ⌈x⁻¹⌉₊, eulerLogDirichletCoeff n * (n : ℂ) ^ (-z))
      = ∑ n ∈ Finset.range ⌈x⁻¹⌉₊, (fun z : ℂ => eulerLogDirichletCoeff n * (n : ℂ) ^ (-z)) := by
    funext z
    simp
  rw [hfun]
  refine Differentiable.sum (fun n _ => ?_)
  rcases eq_or_ne n 0 with rfl | hn0
  · have h0 : (fun z : ℂ => eulerLogDirichletCoeff 0 * ((0 : ℕ) : ℂ) ^ (-z))
        = fun _ : ℂ => (0 : ℂ) := by
      funext z
      rw [eulerLogDirichletCoeff_zero, zero_mul]
    rw [h0]
    exact differentiable_const (0 : ℂ)
  · have hnc : (n : ℂ) ≠ 0 := by simpa using hn0
    refine Differentiable.const_mul ?_ _
    intro z
    have h := (Complex.hasStrictDerivAt_const_cpow (x := ((n : ℂ))⁻¹) (y := z)
      (Or.inl (inv_ne_zero hnc))).hasDerivAt
    have harg : ((n : ℂ)).arg ≠ Real.pi := by
      have hpos : (0 : ℝ) < (n : ℝ) := by
        have : 0 < n := Nat.pos_of_ne_zero hn0
        exact_mod_cast this
      rw [show ((n : ℂ)) = (((n : ℝ)) : ℂ) from by push_cast; ring,
        Complex.arg_ofReal_of_nonneg hpos.le]
      exact ne_of_lt Real.pi_pos
    have heq : (fun t : ℂ => ((n : ℂ)⁻¹) ^ t) = (fun t : ℂ => (n : ℂ) ^ (-t)) := by
      funext t
      rw [Complex.inv_cpow _ _ harg, ← Complex.cpow_neg]
    rw [heq] at h
    exact h.differentiableAt

/-- **Card equation (22).**  All monodromy of the current is the divisor monodromy of the
canonical Euler logarithm: continuing once positively around a zero of multiplicity `m` changes
`P` by `2πi m` and therefore changes the current by exactly `2πi m x^{-z}`. -/
theorem primeTailCurrent_monodromy (z : ℂ) (P₁ P₂ : ℂ) (m : ℕ)
    (hP : P₁ - P₂ = 2 * Real.pi * Complex.I * (m : ℂ)) (x : ℝ) :
    (x : ℂ) ^ (-z) * (P₁ - primeTailFinitePart x z)
        - (x : ℂ) ^ (-z) * (P₂ - primeTailFinitePart x z)
      = monodromyGerm m z x := by
  rw [monodromyGerm]
  linear_combination ((x : ℂ) ^ (-z)) * hP

/-- **Card equation (23).**  The boundary value of the monodromy jump at `z = ρ` is the nonzero
germ `2πi m_ρ x^{-ρ}` whenever the multiplicity is positive and `x` is positive. -/
theorem monodromyGerm_ne_zero {m : ℕ} (hm : m ≠ 0) (rho : ℂ) {x : ℝ} (hx : 0 < x) :
    monodromyGerm m rho x ≠ 0 := by
  have hxc : (x : ℂ) ≠ 0 := by simpa using ne_of_gt hx
  have hcpow : (x : ℂ) ^ (-rho) ≠ 0 := by
    intro hzero
    rw [Complex.cpow_eq_zero_iff] at hzero
    exact hxc hzero.1
  rw [monodromyGerm]
  refine mul_ne_zero (mul_ne_zero ?_ ?_) hcpow
  · simp [Real.pi_ne_zero, Complex.I_ne_zero]
  · simpa using hm

/-! ## Riemann's log-divided prime-power counting function -/

open ArithmeticFunction in
/-- **Card equation (11).**  `J(X) = ∑_{2 ≤ n ≤ X} Λ(n)/log n = ∑_{p^k ≤ X} 1/k`. -/
def primeTailCount (X : ℝ) : ℝ :=
  ∑ n ∈ Finset.Ioc 0 ⌊X⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) / Real.log n

theorem primeTailCount_nonneg (X : ℝ) : 0 ≤ primeTailCount X := by
  refine Finset.sum_nonneg (fun n _ => ?_)
  exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.log_natCast_nonneg n)

/-- Splitting the counting function at a lower cut. -/
theorem primeTailCount_split {X : ℝ} {M : ℕ} (hM : M ≤ ⌊X⌋₊) :
    primeTailCount X
      = (∑ n ∈ Finset.Ioc 0 M, (ArithmeticFunction.vonMangoldt n : ℝ) / Real.log n)
        + ∑ n ∈ Finset.Ioc M ⌊X⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) / Real.log n := by
  rw [primeTailCount,
    ← Finset.sum_Ioc_consecutive (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℝ)
      / Real.log n) (Nat.zero_le M) hM]

/-- The low part is dominated by `psi` at the cut divided by `log 2`. -/
theorem primeTailCount_low_le (M : ℕ) :
    (∑ n ∈ Finset.Ioc 0 M, (ArithmeticFunction.vonMangoldt n : ℝ) / Real.log n)
      ≤ chebyshevPsi M / Real.log 2 := by
  rw [chebyshevPsi_eq_sum_Ioc, Finset.sum_div]
  refine Finset.sum_le_sum (fun n hn => ?_)
  rcases lt_or_ge n 2 with hn2 | hn2
  · interval_cases n
    · simp
    · simp [ArithmeticFunction.vonMangoldt_apply_one]
  · have hlog2 : Real.log 2 ≤ Real.log n := by
      apply Real.log_le_log (by norm_num)
      exact_mod_cast hn2
    have hlogpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg hlogpos hlog2

/-- Every von Mangoldt-supported index is at least `2`. -/
theorem two_le_of_vonMangoldt_ne_zero {n : ℕ} (h : (ArithmeticFunction.vonMangoldt n : ℝ) ≠ 0) :
    2 ≤ n := by
  rcases Nat.lt_or_ge n 2 with h2 | h2
  · interval_cases n
    · exact absurd (by simp) h
    · exact absurd (by simp [ArithmeticFunction.vonMangoldt_apply_one]) h
  · exact h2

/-- The high part is at least the `psi` difference divided by the logarithm of the top. -/
theorem primeTailCount_high_lower {M N : ℕ} (hMN : M ≤ N) (hN : 2 ≤ N) :
    (chebyshevPsi N - chebyshevPsi M) / Real.log N
      ≤ ∑ n ∈ Finset.Ioc M N, (ArithmeticFunction.vonMangoldt n : ℝ) / Real.log n := by
  have hdiff : chebyshevPsi N - chebyshevPsi M
      = ∑ n ∈ Finset.Ioc M N, (ArithmeticFunction.vonMangoldt n : ℝ) := chebyshevPsi_sub hMN
  have hlogN : (0 : ℝ) < Real.log N := by
    refine Real.log_pos ?_
    have : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  rw [hdiff, Finset.sum_div]
  refine Finset.sum_le_sum (fun n hn => ?_)
  rw [Finset.mem_Ioc] at hn
  rcases eq_or_ne (ArithmeticFunction.vonMangoldt n : ℝ) 0 with h0 | h0
  · simp [h0]
  · have hn2 : 2 ≤ n := two_le_of_vonMangoldt_ne_zero h0
    have hlogn : (0 : ℝ) < Real.log n := by
      refine Real.log_pos ?_
      have : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn2
      linarith
    have hle : Real.log n ≤ Real.log N :=
      Real.log_le_log (by positivity) (by exact_mod_cast hn.2)
    exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg hlogn hle

/-- The high part is at most the `psi` difference divided by any lower logarithm bound. -/
theorem primeTailCount_high_upper {M N : ℕ} (hMN : M ≤ N) {L : ℝ} (hL : 0 < L)
    (hlog : ∀ n : ℕ, M < n → (ArithmeticFunction.vonMangoldt n : ℝ) ≠ 0 → L ≤ Real.log n) :
    (∑ n ∈ Finset.Ioc M N, (ArithmeticFunction.vonMangoldt n : ℝ) / Real.log n)
      ≤ (chebyshevPsi N - chebyshevPsi M) / L := by
  have hdiff : chebyshevPsi N - chebyshevPsi M
      = ∑ n ∈ Finset.Ioc M N, (ArithmeticFunction.vonMangoldt n : ℝ) := chebyshevPsi_sub hMN
  rw [hdiff, Finset.sum_div]
  refine Finset.sum_le_sum (fun n hn => ?_)
  rw [Finset.mem_Ioc] at hn
  rcases eq_or_ne (ArithmeticFunction.vonMangoldt n : ℝ) 0 with h0 | h0
  · simp [h0]
  · exact div_le_div_of_nonneg_left ArithmeticFunction.vonMangoldt_nonneg hL (hlog n hn.1 h0)

/-- Every integer above the cut has logarithm at least `(1 − ε) log X`. -/
theorem log_ge_of_gt_floor_rpow {ε X : ℝ} (hX : 0 < X) {n : ℕ} (hn : ⌊X ^ (1 - ε)⌋₊ < n) :
    (1 - ε) * Real.log X ≤ Real.log n := by
  have hlt : X ^ (1 - ε) < (n : ℝ) := by
    refine lt_of_lt_of_le (Nat.lt_floor_add_one (X ^ (1 - ε))) ?_
    exact_mod_cast hn
  have hpos : (0 : ℝ) < X ^ (1 - ε) := Real.rpow_pos_of_pos hX _
  have := Real.log_le_log hpos hlt.le
  rwa [Real.log_rpow hX] at this

/-- The cut sits below the argument. -/
theorem floor_rpow_le_floor {ε X : ℝ} (hε : 0 ≤ ε) (hX : 1 ≤ X) :
    ⌊X ^ (1 - ε)⌋₊ ≤ ⌊X⌋₊ := by
  refine Nat.floor_mono ?_
  calc X ^ (1 - ε) ≤ X ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hX (by linarith)
    _ = X := Real.rpow_one X

/-- **Lower bound for `J`.**  Drop the low block and enlarge every logarithm to `log X`. -/
theorem primeTailCount_lower {ε X : ℝ} (hε : 0 ≤ ε) (hX : 2 ≤ X) :
    (chebyshevPsiReal X - chebyshevPsi ⌊X ^ (1 - ε)⌋₊) / Real.log X ≤ primeTailCount X := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hMN : ⌊X ^ (1 - ε)⌋₊ ≤ ⌊X⌋₊ := floor_rpow_le_floor hε hX1
  have hN2 : 2 ≤ ⌊X⌋₊ := Nat.le_floor (by exact_mod_cast hX)
  have hlogN : (0 : ℝ) < Real.log ⌊X⌋₊ := by
    refine Real.log_pos ?_
    have : (2 : ℝ) ≤ (⌊X⌋₊ : ℝ) := by exact_mod_cast hN2
    linarith
  have hlogNle : Real.log ⌊X⌋₊ ≤ Real.log X :=
    Real.log_le_log (by positivity) (Nat.floor_le hX0.le)
  have hsplit := primeTailCount_split (X := X) hMN
  have hlow : (0 : ℝ)
      ≤ ∑ n ∈ Finset.Ioc 0 ⌊X ^ (1 - ε)⌋₊, (ArithmeticFunction.vonMangoldt n : ℝ) / Real.log n :=
    Finset.sum_nonneg (fun n _ => div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.log_natCast_nonneg n))
  have hhigh := primeTailCount_high_lower hMN hN2
  have hpsi : chebyshevPsiReal X - chebyshevPsi ⌊X ^ (1 - ε)⌋₊
      = chebyshevPsi ⌊X⌋₊ - chebyshevPsi ⌊X ^ (1 - ε)⌋₊ := rfl
  have hnn : (0 : ℝ) ≤ chebyshevPsi ⌊X⌋₊ - chebyshevPsi ⌊X ^ (1 - ε)⌋₊ := by
    have := chebyshevPsi_mono hMN
    linarith
  have hmono : (chebyshevPsi ⌊X⌋₊ - chebyshevPsi ⌊X ^ (1 - ε)⌋₊) / Real.log X
      ≤ (chebyshevPsi ⌊X⌋₊ - chebyshevPsi ⌊X ^ (1 - ε)⌋₊) / Real.log ⌊X⌋₊ :=
    div_le_div_of_nonneg_left hnn hlogN hlogNle
  rw [hpsi, hsplit]
  linarith

/-- **Upper bound for `J`.**  Bound the low block by `psi` at the cut and every high logarithm
below by `(1 − ε) log X`. -/
theorem primeTailCount_upper {ε X : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) (hX : 2 ≤ X) :
    primeTailCount X ≤ chebyshevPsi ⌊X ^ (1 - ε)⌋₊ / Real.log 2
      + chebyshevPsiReal X / ((1 - ε) * Real.log X) := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hMN : ⌊X ^ (1 - ε)⌋₊ ≤ ⌊X⌋₊ := floor_rpow_le_floor hε0 hX1
  have hlogX : (0 : ℝ) < Real.log X := Real.log_pos (by linarith)
  have hL : (0 : ℝ) < (1 - ε) * Real.log X := mul_pos (by linarith) hlogX
  have hsplit := primeTailCount_split (X := X) hMN
  have hlow := primeTailCount_low_le ⌊X ^ (1 - ε)⌋₊
  have hhigh := primeTailCount_high_upper hMN hL
    (fun n hn _ => log_ge_of_gt_floor_rpow hX0 hn)
  have hpsiM : (0 : ℝ) ≤ chebyshevPsi ⌊X ^ (1 - ε)⌋₊ := by
    simpa [chebyshevPsiReal] using chebyshevPsiReal_nonneg (X ^ (1 - ε))
  have hdrop : (chebyshevPsi ⌊X⌋₊ - chebyshevPsi ⌊X ^ (1 - ε)⌋₊) / ((1 - ε) * Real.log X)
      ≤ chebyshevPsiReal X / ((1 - ε) * Real.log X) := by
    have : chebyshevPsi ⌊X⌋₊ - chebyshevPsi ⌊X ^ (1 - ε)⌋₊ ≤ chebyshevPsiReal X := by
      simpa [chebyshevPsiReal] using hpsiM
    gcongr
  rw [hsplit]
  linarith

/-! ### The prime number theorem in log-divided form -/

/-- The cut is negligible: `X^{1−ε} log X / X → 0`. -/
theorem tendsto_rpow_sub_mul_log {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun X : ℝ => X ^ (1 - ε) * Real.log X / X) atTop (𝓝 0) := by
  have hkey : ∀ᶠ X : ℝ in atTop,
      X ^ (1 - ε) * Real.log X / X = Real.log X / X ^ ε := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have h1 : X ^ (1 - ε) * X ^ ε = X := by
      rw [← Real.rpow_add hX]
      simp
    rw [div_eq_div_iff (ne_of_gt hX) (by positivity)]
    calc X ^ (1 - ε) * Real.log X * X ^ ε
        = (X ^ (1 - ε) * X ^ ε) * Real.log X := by ring
      _ = Real.log X * X := by rw [h1]; ring
  refine Tendsto.congr' (Filter.EventuallyEq.symm hkey) ?_
  simpa using (isLittleO_log_rpow_atTop hε).tendsto_div_nhds_zero

/-- The cut is negligible in the plain normalization: `X^{1−ε}/X → 0`. -/
theorem tendsto_rpow_sub_div {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun X : ℝ => X ^ (1 - ε) / X) atTop (𝓝 0) := by
  have hkey : ∀ᶠ X : ℝ in atTop, X ^ (1 - ε) / X = (X ^ ε)⁻¹ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with X hX
    have h1 : X ^ (1 - ε) * X ^ ε = X := by
      rw [← Real.rpow_add hX]; simp
    rw [inv_eq_one_div, div_eq_div_iff (ne_of_gt hX) (by positivity)]
    linarith [h1]
  refine Tendsto.congr' (Filter.EventuallyEq.symm hkey) ?_
  exact tendsto_inv_atTop_zero.comp (tendsto_rpow_atTop hε)

/-- The two-sided window: `J(X) log X / X` is trapped between a PNT quotient minus a negligible
cut and a negligible cut plus that quotient inflated by `(1 − ε)^{-1}`. -/
theorem primeTailCount_window {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) {C : ℝ}
    (hC : ∀ x : ℝ, 1 ≤ x → chebyshevPsiReal x ≤ C * x) :
    ∀ᶠ X : ℝ in atTop,
      chebyshevPsiReal X / X - C * (X ^ (1 - ε) / X) ≤ primeTailCount X * Real.log X / X
      ∧ primeTailCount X * Real.log X / X
          ≤ C * (X ^ (1 - ε) * Real.log X / X) / Real.log 2
            + chebyshevPsiReal X / X / (1 - ε) := by
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with X hX
  have hX0 : (0 : ℝ) < X := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hlogX : (0 : ℝ) < Real.log X := Real.log_pos (by linarith)
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hde : (0 : ℝ) < 1 - ε := by linarith
  have hcut1 : (1 : ℝ) ≤ X ^ (1 - ε) := Real.one_le_rpow hX1 (by linarith)
  have hMdef : chebyshevPsi ⌊X ^ (1 - ε)⌋₊ = chebyshevPsiReal (X ^ (1 - ε)) := rfl
  have hMle : chebyshevPsi ⌊X ^ (1 - ε)⌋₊ ≤ C * X ^ (1 - ε) := by
    rw [hMdef]; exact hC _ hcut1
  have hMnn : (0 : ℝ) ≤ chebyshevPsi ⌊X ^ (1 - ε)⌋₊ := by
    rw [hMdef]; exact chebyshevPsiReal_nonneg _
  constructor
  · have hAle : chebyshevPsiReal X - chebyshevPsi ⌊X ^ (1 - ε)⌋₊
        ≤ primeTailCount X * Real.log X :=
      (div_le_iff₀ hlogX).mp (primeTailCount_lower hε0.le hX)
    have h1 : (chebyshevPsiReal X - chebyshevPsi ⌊X ^ (1 - ε)⌋₊) / X
        ≤ primeTailCount X * Real.log X / X := by gcongr
    have h2 : chebyshevPsiReal X / X - C * (X ^ (1 - ε) / X)
        ≤ (chebyshevPsiReal X - chebyshevPsi ⌊X ^ (1 - ε)⌋₊) / X := by
      have hdiff : (chebyshevPsiReal X - chebyshevPsi ⌊X ^ (1 - ε)⌋₊) / X
          - (chebyshevPsiReal X / X - C * (X ^ (1 - ε) / X))
          = (C * X ^ (1 - ε) - chebyshevPsi ⌊X ^ (1 - ε)⌋₊) / X := by
        field_simp
        ring
      have hnn : (0 : ℝ) ≤ (C * X ^ (1 - ε) - chebyshevPsi ⌊X ^ (1 - ε)⌋₊) / X :=
        div_nonneg (by linarith) hX0.le
      linarith
    linarith
  · have hU := primeTailCount_upper hε0.le hε1 hX
    have hstep : primeTailCount X * Real.log X / X
        ≤ (chebyshevPsi ⌊X ^ (1 - ε)⌋₊ / Real.log 2
            + chebyshevPsiReal X / ((1 - ε) * Real.log X)) * Real.log X / X := by
      gcongr
    refine le_trans hstep ?_
    have hexp : (chebyshevPsi ⌊X ^ (1 - ε)⌋₊ / Real.log 2
        + chebyshevPsiReal X / ((1 - ε) * Real.log X)) * Real.log X / X
        = chebyshevPsi ⌊X ^ (1 - ε)⌋₊ * Real.log X / X / Real.log 2
          + chebyshevPsiReal X / X / (1 - ε) := by
      field_simp
    rw [hexp]
    have hfirst : chebyshevPsi ⌊X ^ (1 - ε)⌋₊ * Real.log X / X / Real.log 2
        ≤ C * (X ^ (1 - ε) * Real.log X / X) / Real.log 2 := by
      have hmul : chebyshevPsi ⌊X ^ (1 - ε)⌋₊ * Real.log X / X
          ≤ C * X ^ (1 - ε) * Real.log X / X := by
        gcongr
      have heq : C * X ^ (1 - ε) * Real.log X / X = C * (X ^ (1 - ε) * Real.log X / X) := by ring
      rw [heq] at hmul
      exact div_le_div_of_nonneg_right hmul hlog2.le
    linarith

/-- **Card equation (12).**  `J(X) log X / X → 1`: the prime number theorem in the log-divided
counting normalization. -/
theorem tendsto_primeTailCount :
    Tendsto (fun X : ℝ => primeTailCount X * Real.log X / X) atTop (𝓝 1) := by
  obtain ⟨C, -, hC⟩ := exists_chebyshevPsiReal_le_linear
  refine tendsto_order.2 ⟨fun a ha => ?_, fun b hb => ?_⟩
  · have hlim : Tendsto
        (fun X : ℝ => chebyshevPsiReal X / X - C * (X ^ (1 - (1 / 2 : ℝ)) / X)) atTop (𝓝 1) := by
      have := tendsto_chebyshevPsiReal_div.sub
        ((tendsto_rpow_sub_div (by norm_num : (0:ℝ) < 1/2)).const_mul C)
      simpa using this
    filter_upwards [primeTailCount_window (by norm_num : (0:ℝ) < 1/2) (by norm_num) hC,
      hlim.eventually (eventually_gt_nhds ha)] with X hwin hgt
    exact lt_of_lt_of_le hgt hwin.1
  · set ε : ℝ := (b - 1) / (2 * b) with hεdef
    have hb0 : (0 : ℝ) < b := by linarith
    have hε0 : (0 : ℝ) < ε := by
      rw [hεdef]; exact div_pos (by linarith) (by linarith)
    have hε1 : ε < 1 := by
      rw [hεdef, div_lt_one (by linarith)]; linarith
    have hde : (0 : ℝ) < 1 - ε := by linarith
    have hlim : Tendsto
        (fun X : ℝ => C * (X ^ (1 - ε) * Real.log X / X) / Real.log 2
          + chebyshevPsiReal X / X / (1 - ε)) atTop (𝓝 (1 / (1 - ε))) := by
      have h1 : Tendsto (fun X : ℝ => C * (X ^ (1 - ε) * Real.log X / X) / Real.log 2) atTop
          (𝓝 0) := by
        have := ((tendsto_rpow_sub_mul_log hε0).const_mul C).div_const (Real.log 2)
        simpa using this
      have h2 : Tendsto (fun X : ℝ => chebyshevPsiReal X / X / (1 - ε)) atTop
          (𝓝 (1 / (1 - ε))) := tendsto_chebyshevPsiReal_div.div_const _
      simpa using h1.add h2
    have hlt : 1 / (1 - ε) < b := by
      rw [div_lt_iff₀ hde, hεdef]
      have h2b : (0 : ℝ) < 2 * b := by linarith
      rw [show b * (1 - (b - 1) / (2 * b)) = b - (b - 1) / 2 by field_simp]
      linarith [sq_nonneg (b - 1)]
    filter_upwards [primeTailCount_window hε0 hε1 hC,
      hlim.eventually (eventually_lt_nhds hlt)] with X hwin hlt2
    exact lt_of_le_of_lt hwin.2 hlt2

end

end RHTower
