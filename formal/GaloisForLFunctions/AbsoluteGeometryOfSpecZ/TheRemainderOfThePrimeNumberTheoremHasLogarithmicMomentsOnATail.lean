import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.SumsOverTheDegreePointsOfATailAreRiemannSums
import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.TheFormOfLogarithmicTailsIsDeterminedByTheRowsOfTheFlatTail
import GaloisForLFunctions.RHTower.Sieve.ChebyshevPsiBigO

/-!
# The remainder of the prime number theorem has logarithmic moments on a tail

The row of the flat tail at the degree point `n` contains `N/n − ψ(N/n)`, the remainder of the
prime number theorem at the ratio `N/n`. In the coordinate `t = n/N` of the tail it is
`r(t) = 1/t − ψ(1/t)` (`primeRemainder`). This file proves, for every `j`,

`(1/N) Σ_{n ≤ N} log^j(N/n) (N/n − ψ(N/n)) → κ_j = ∫_0^1 log^j(1/t) (1/t − ψ(1/t)) dt`

(`tendsto_sum_logTail_mul_primeRemainder`), and the same for every profile `w` of a tail in
place of `log^j(1/t)` (`TailWeight`, `TailWeight.tendsto_tailRiemannSum_primeProfile`): `w` is
continuous on `(0, 1]`, at most `c log^j(1/t)`, and has convergent Riemann sums after every cut.

* **The majorant** (`exists_abs_logPow_mul_primeRemainder_le`). The prime number theorem with the
  error `x e^{−c√log x}` and Chebyshev's bound give
  `|log^j(1/t) r(t)| ≤ C_j /(t (1 + log(1/t))²)` on `(0, 1]`; the right side is integrable.
* **The points below `N/K`** (`sum_inv_mul_one_add_log_sq_le`). Their terms are at most
  `C_j/(n (1 + log(N/n))²)`; with `φ(n) = 1/(1 + log(N/n))` each is at most `2(φ(n+1) − φ(n))`,
  and the sum telescopes to at most `2/(1 + log(K/2))`.
* **The points above `N/K`** (`TailWeight.riemannOn_cut_primeProfile`). There
  `ψ(N/n) = Σ_{k ≤ K} Λ(k) 1[n ≤ N/k]`: the hyperbola method. The profile is a finite combination
  of a bounded continuous profile and of cuts of the profile, so its Riemann sums converge.
-/

open Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

open HodgeTheoryOfAFixedPart (chebyshev)

/-! ### The prime number theorem with a power of the logarithm to spare -/

/-- `(1 + u)^m e^{−c√u}` is bounded on `u ≥ 0`. -/
theorem one_add_pow_mul_exp_neg_sqrt_le {c : ℝ} (hc : 0 < c) (m : ℕ) {u : ℝ} (hu : 0 ≤ u) :
    (1 + u) ^ m * Real.exp (-c * Real.sqrt u) ≤
      2 ^ m * (1 + (2 * m).factorial / c ^ (2 * m)) := by
  have hy0 : 0 ≤ c * Real.sqrt u := mul_nonneg hc.le (Real.sqrt_nonneg u)
  have h1 : (c * Real.sqrt u) ^ (2 * m) / (2 * m).factorial ≤ Real.exp (c * Real.sqrt u) :=
    Real.pow_div_factorial_le_exp (c * Real.sqrt u) hy0 (2 * m)
  have h2 : (c * Real.sqrt u) ^ (2 * m) = c ^ (2 * m) * u ^ m := by
    rw [mul_pow, pow_mul (Real.sqrt u) 2 m, Real.sq_sqrt hu]
  have hcpos : 0 < c ^ (2 * m) := pow_pos hc _
  have hfac : (0 : ℝ) < (2 * m).factorial := by exact_mod_cast Nat.factorial_pos _
  have he : 0 < Real.exp (c * Real.sqrt u) := Real.exp_pos _
  have h3 : u ^ m * Real.exp (-(c * Real.sqrt u)) ≤ (2 * m).factorial / c ^ (2 * m) := by
    rw [Real.exp_neg, le_div_iff₀ hcpos]
    have h1' : c ^ (2 * m) * u ^ m ≤ (2 * m).factorial * Real.exp (c * Real.sqrt u) := by
      rw [← h2]
      exact (div_le_iff₀' hfac).mp h1
    calc u ^ m * (Real.exp (c * Real.sqrt u))⁻¹ * c ^ (2 * m)
        = (c ^ (2 * m) * u ^ m) * (Real.exp (c * Real.sqrt u))⁻¹ := by ring
      _ ≤ ((2 * m).factorial * Real.exp (c * Real.sqrt u)) * (Real.exp (c * Real.sqrt u))⁻¹ :=
          mul_le_mul_of_nonneg_right h1' (inv_nonneg.mpr he.le)
      _ = (2 * m).factorial := by field_simp
  have h4 : (1 + u) ^ m ≤ 2 ^ m * (1 + u ^ m) := by
    rcases le_total u 1 with h | h
    · calc (1 + u) ^ m ≤ 2 ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
        _ ≤ 2 ^ m * (1 + u ^ m) :=
          le_mul_of_one_le_right (by positivity) (by linarith [pow_nonneg hu m])
    · calc (1 + u) ^ m ≤ (2 * u) ^ m := pow_le_pow_left₀ (by linarith) (by linarith) m
        _ = 2 ^ m * u ^ m := mul_pow 2 u m
        _ ≤ 2 ^ m * (1 + u ^ m) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          linarith
  have h5 : Real.exp (-(c * Real.sqrt u)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hexp : Real.exp (-c * Real.sqrt u) = Real.exp (-(c * Real.sqrt u)) := by
    rw [neg_mul]
  rw [hexp]
  calc (1 + u) ^ m * Real.exp (-(c * Real.sqrt u))
      ≤ 2 ^ m * (1 + u ^ m) * Real.exp (-(c * Real.sqrt u)) :=
        mul_le_mul_of_nonneg_right h4 (Real.exp_pos _).le
    _ = 2 ^ m * (Real.exp (-(c * Real.sqrt u)) + u ^ m * Real.exp (-(c * Real.sqrt u))) := by ring
    _ ≤ 2 ^ m * (1 + (2 * m).factorial / c ^ (2 * m)) :=
        mul_le_mul_of_nonneg_left (add_le_add h5 h3) (by positivity)

/-- **The prime number theorem with powers of the logarithm to spare**:
`|x − ψ(x)| log^j x (1 + log x)² ≤ C_j x` for `x ≥ 1`. -/
theorem exists_abs_sub_psi_mul_log_pow_le (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 ≤ x →
      |x - Chebyshev.psi x| * Real.log x ^ j * (1 + Real.log x) ^ 2 ≤ C * x := by
  obtain ⟨c, hc, hO⟩ := RHTower.Sieve.chebyshevPsi_sub_id_isBigO
  obtain ⟨B, hB⟩ := hO.bound
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.mp hB
  have hX1 : (1 : ℝ) ≤ max X₀ 1 := le_max_right _ _
  have hlogX : 0 ≤ Real.log (max X₀ 1) := Real.log_nonneg hX1
  have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hD0 : (0 : ℝ) ≤ 2 ^ (j + 2) * (1 + (2 * (j + 2)).factorial / c ^ (2 * (j + 2))) := by
    positivity
  have hC₁0 : 0 ≤ (1 + Real.log 4 + 2 * Real.log (max X₀ 1)) *
      (1 + Real.log (max X₀ 1)) ^ (j + 2) := by positivity
  refine ⟨max (|B| * (2 ^ (j + 2) * (1 + (2 * (j + 2)).factorial / c ^ (2 * (j + 2)))))
    ((1 + Real.log 4 + 2 * Real.log (max X₀ 1)) * (1 + Real.log (max X₀ 1)) ^ (j + 2)),
    le_max_of_le_right hC₁0, fun x hx => ?_⟩
  have hx0 : 0 < x := by linarith
  have hu : 0 ≤ Real.log x := Real.log_nonneg hx
  have hpow : Real.log x ^ j * (1 + Real.log x) ^ 2 ≤ (1 + Real.log x) ^ (j + 2) := by
    rw [pow_add]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hu (by linarith) j) (by positivity)
  rcases le_total (max X₀ 1) x with hxX | hxX
  · -- the prime number theorem
    have h := hX₀ x ((le_max_left _ _).trans hxX)
    rw [Pi.sub_apply, id_eq, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_pos (mul_pos hx0 (Real.exp_pos _))] at h
    have h' : |x - Chebyshev.psi x| ≤ |B| * (x * Real.exp (-c * Real.sqrt (Real.log x))) := by
      rw [abs_sub_comm]
      exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self B) (by positivity))
    have hbd := one_add_pow_mul_exp_neg_sqrt_le hc (j + 2) hu
    calc |x - Chebyshev.psi x| * Real.log x ^ j * (1 + Real.log x) ^ 2
        = |x - Chebyshev.psi x| * (Real.log x ^ j * (1 + Real.log x) ^ 2) := by ring
      _ ≤ |B| * (x * Real.exp (-c * Real.sqrt (Real.log x))) * (1 + Real.log x) ^ (j + 2) :=
          mul_le_mul h' hpow (by positivity) (by positivity)
      _ = |B| * ((1 + Real.log x) ^ (j + 2) * Real.exp (-c * Real.sqrt (Real.log x))) * x := by
          ring
      _ ≤ |B| * (2 ^ (j + 2) * (1 + (2 * (j + 2)).factorial / c ^ (2 * (j + 2)))) * x :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hbd (abs_nonneg B)) hx0.le
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) hx0.le
  · -- Chebyshev's bound below the threshold
    have hψ := Chebyshev.psi_le hx
    have hψ0 : 0 ≤ Chebyshev.psi x := Chebyshev.psi_nonneg x
    have hsqrt : Real.sqrt x ≤ x := Real.sqrt_le_iff.mpr ⟨hx0.le, by nlinarith⟩
    have hlogx : Real.log x ≤ Real.log (max X₀ 1) := Real.log_le_log hx0 hxX
    have hprod : Real.sqrt x * Real.log x ≤ x * Real.log (max X₀ 1) :=
      mul_le_mul hsqrt hlogx hu hx0.le
    have h1 : |x - Chebyshev.psi x| ≤ (1 + Real.log 4 + 2 * Real.log (max X₀ 1)) * x := by
      have hlx : 0 ≤ Real.log 4 * x := mul_nonneg hlog4 hx0.le
      have hXx : 0 ≤ Real.log (max X₀ 1) * x := mul_nonneg hlogX hx0.le
      rw [abs_le]
      constructor <;> nlinarith
    have h2 : (1 + Real.log x) ^ (j + 2) ≤ (1 + Real.log (max X₀ 1)) ^ (j + 2) :=
      pow_le_pow_left₀ (by linarith) (by linarith) _
    calc |x - Chebyshev.psi x| * Real.log x ^ j * (1 + Real.log x) ^ 2
        = |x - Chebyshev.psi x| * (Real.log x ^ j * (1 + Real.log x) ^ 2) := by ring
      _ ≤ (1 + Real.log 4 + 2 * Real.log (max X₀ 1)) * x *
            (1 + Real.log (max X₀ 1)) ^ (j + 2) :=
          mul_le_mul h1 (hpow.trans h2) (by positivity) (by positivity)
      _ = (1 + Real.log 4 + 2 * Real.log (max X₀ 1)) * (1 + Real.log (max X₀ 1)) ^ (j + 2) * x := by
          ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) hx0.le

/-! ### The coordinate of the tail -/

/-- The profile `t ↦ log^j(1/t)` of the logarithmic tail of degree `j`. -/
def logPow (j : ℕ) (t : ℝ) : ℝ := Real.log (1 / t) ^ j

/-- The remainder of the prime number theorem in the coordinate of a tail: `1/t − ψ(1/t)`. -/
def primeRemainder (t : ℝ) : ℝ := 1 / t - Chebyshev.psi (1 / t)

/-- The majorant `1/(t (1 + log(1/t))²)`. -/
def logMajorant (t : ℝ) : ℝ := 1 / (t * (1 + Real.log (1 / t)) ^ 2)

/-- The moment `κ_j = ∫_0^1 log^j(1/t) (1/t − ψ(1/t)) dt`. -/
def primeMoment (j : ℕ) : ℝ := ∫ t in Set.Ioc 0 1, logPow j t * primeRemainder t

theorem one_le_one_div {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) : 1 ≤ 1 / t := by
  rw [le_div_iff₀ ht.1]
  simpa using ht.2

theorem log_one_div_nonneg {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) : 0 ≤ Real.log (1 / t) :=
  Real.log_nonneg (one_le_one_div ht)

theorem logPow_nonneg (j : ℕ) {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) : 0 ≤ logPow j t :=
  pow_nonneg (log_one_div_nonneg ht) j

theorem antitoneOn_logPow (j : ℕ) : AntitoneOn (logPow j) (Set.Ioc 0 1) := by
  intro s hs t ht hst
  refine pow_le_pow_left₀ (log_one_div_nonneg ht) (Real.log_le_log (by have := ht.1; positivity) ?_) j
  exact one_div_le_one_div_of_le hs.1 hst

theorem measurable_logPow (j : ℕ) : Measurable (logPow j) :=
  (Real.measurable_log.comp (measurable_const.div measurable_id)).pow_const j

theorem measurable_primeRemainder : Measurable primeRemainder :=
  (measurable_const.div measurable_id).sub
    (Chebyshev.psi_mono.measurable.comp (measurable_const.div measurable_id))

/-- `log^j(1/t) ≤ 2^j j! t^{−1/2}` on `(0, 1]`. -/
theorem logPow_le_rpow (j : ℕ) {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) :
    logPow j t ≤ 2 ^ j * j.factorial * t ^ (-(1 / 2) : ℝ) := by
  have hL := log_one_div_nonneg ht
  have h1 := Real.pow_div_factorial_le_exp (Real.log (1 / t) / 2) (by positivity) j
  have hfac : (0 : ℝ) < j.factorial := by exact_mod_cast Nat.factorial_pos j
  have hexp : Real.exp (Real.log (1 / t) / 2) = t ^ (-(1 / 2) : ℝ) := by
    rw [Real.rpow_def_of_pos ht.1, Real.log_div one_ne_zero ht.1.ne', Real.log_one]
    congr 1
    ring
  rw [hexp, div_le_iff₀ hfac, div_pow] at h1
  rw [logPow]
  have h2 : (0 : ℝ) < 2 ^ j := by positivity
  rw [div_le_iff₀ h2] at h1
  linarith

theorem integrableOn_logPow (j : ℕ) : IntegrableOn (logPow j) (Set.Ioc 0 1) := by
  have hr : IntegrableOn (fun t : ℝ => t ^ (-(1 / 2) : ℝ)) (Set.Ioc 0 1) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp
      (intervalIntegral.intervalIntegrable_rpow' (by norm_num))
  refine Integrable.mono' (hr.const_mul (2 ^ j * j.factorial))
    (measurable_logPow j).aestronglyMeasurable ?_
  exact (ae_restrict_mem measurableSet_Ioc).mono fun t ht => by
    rw [Real.norm_eq_abs, abs_of_nonneg (logPow_nonneg j ht)]
    exact logPow_le_rpow j ht

/-- **The majorant of the prime part of a row** on `(0, 1]`. -/
theorem exists_abs_logPow_mul_primeRemainder_le (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      |logPow j t * primeRemainder t| ≤ C * logMajorant t := by
  obtain ⟨C, hC, h⟩ := exists_abs_sub_psi_mul_log_pow_le j
  refine ⟨C, hC, fun t ht => ?_⟩
  have hL := log_one_div_nonneg ht
  have h' := h (1 / t) (one_le_one_div ht)
  have hpos : 0 < (1 + Real.log (1 / t)) ^ 2 := by positivity
  have hmaj : C * logMajorant t = C * (1 / t) / (1 + Real.log (1 / t)) ^ 2 := by
    rw [logMajorant]
    have := ht.1.ne'
    field_simp
  rw [abs_mul, abs_of_nonneg (logPow_nonneg j ht), primeRemainder, hmaj, le_div_iff₀ hpos, logPow]
  calc Real.log (1 / t) ^ j * |1 / t - Chebyshev.psi (1 / t)| * (1 + Real.log (1 / t)) ^ 2
      = |1 / t - Chebyshev.psi (1 / t)| * Real.log (1 / t) ^ j * (1 + Real.log (1 / t)) ^ 2 := by
        ring
    _ ≤ C * (1 / t) := h'

theorem logMajorant_nonneg {t : ℝ} (ht : t ∈ Set.Ioc (0 : ℝ) 1) : 0 ≤ logMajorant t := by
  have hL := log_one_div_nonneg ht
  have := ht.1
  rw [logMajorant]
  positivity

/-- The majorant is integrable on `(0, 1]`: it is the derivative of `1/(1 + log(1/t))`. -/
theorem integrableOn_logMajorant : IntegrableOn logMajorant (Set.Ioc 0 1) := by
  have hderiv : ∀ t : ℝ, 0 < t → t ≤ 1 →
      HasDerivAt (fun t => (1 - Real.log t)⁻¹) (logMajorant t) t := by
    intro t ht0 ht1
    have hl : 0 < 1 - Real.log t := by
      have := Real.log_nonpos ht0.le ht1
      linarith
    have h1 : HasDerivAt (fun t => 1 - Real.log t) (-(t⁻¹)) t :=
      (Real.hasDerivAt_log ht0.ne').const_sub 1
    have h2 := h1.inv hl.ne'
    have e : 1 + Real.log (1 / t) = 1 - Real.log t := by
      rw [Real.log_div one_ne_zero ht0.ne', Real.log_one]
      ring
    refine h2.congr_deriv ?_
    show -(-(t⁻¹)) / (1 - Real.log t) ^ 2 = 1 / (t * (1 + Real.log (1 / t)) ^ 2)
    rw [e, neg_neg, inv_eq_one_div, div_div]
  have hcontAt : ∀ t : ℝ, 0 < t → t ≤ 1 → ContinuousAt logMajorant t := by
    intro t ht0 ht1
    have hL := log_one_div_nonneg ⟨ht0, ht1⟩
    show ContinuousAt (fun t : ℝ => 1 / (t * (1 + Real.log (1 / t)) ^ 2)) t
    refine ContinuousAt.div continuousAt_const ?_ (by positivity)
    refine continuousAt_id.mul (ContinuousAt.pow ?_ 2)
    refine continuousAt_const.add ?_
    exact (Real.continuousAt_log (by positivity)).comp
      (continuousAt_const.div continuousAt_id ht0.ne')
  have hii : ∀ a : ℝ, 0 < a → a ≤ 1 → IntervalIntegrable logMajorant volume a 1 :=
    fun a ha0 ha1 => ContinuousOn.intervalIntegrable_of_Icc ha1 fun t ht =>
      (hcontAt t (ha0.trans_le ht.1) ht.2).continuousWithinAt
  have hval : ∀ a : ℝ, 0 < a → a ≤ 1 →
      ∫ t in a..1, logMajorant t = 1 - (1 - Real.log a)⁻¹ := by
    intro a ha0 ha1
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := fun t => (1 - Real.log t)⁻¹)
      (fun t ht => by
        rw [Set.uIcc_of_le ha1] at ht
        exact hderiv t (ha0.trans_le ht.1) ht.2) (hii a ha0 ha1)]
    simp
  have ha0 : ∀ n : ℕ, (0 : ℝ) < 1 / ((n : ℝ) + 1) := fun n => by positivity
  have ha1 : ∀ n : ℕ, 1 / ((n : ℝ) + 1) ≤ 1 := fun n => by
    rw [div_le_one (by positivity)]
    linarith [n.cast_nonneg (α := ℝ)]
  refine integrableOn_Ioc_of_intervalIntegral_norm_bounded_left
    (a := fun n : ℕ => 1 / ((n : ℝ) + 1)) (l := atTop) (I := 1) (fun n => ?_)
    tendsto_one_div_add_atTop_nhds_zero_nat (Eventually.of_forall fun n => ?_)
  · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (ha1 n)).mp (hii _ (ha0 n) (ha1 n))
  · have hnorm : ∫ t in Set.Ioc (1 / ((n : ℝ) + 1)) 1, ‖logMajorant t‖ =
        ∫ t in Set.Ioc (1 / ((n : ℝ) + 1)) 1, logMajorant t :=
      setIntegral_congr_fun measurableSet_Ioc fun t ht => by
        show ‖logMajorant t‖ = logMajorant t
        rw [Real.norm_eq_abs, abs_of_nonneg (logMajorant_nonneg ⟨(ha0 n).trans ht.1, ht.2⟩)]
    rw [hnorm, ← intervalIntegral.integral_of_le (ha1 n), hval _ (ha0 n) (ha1 n)]
    have hl : 0 < 1 - Real.log (1 / ((n : ℝ) + 1)) := by
      have := Real.log_nonpos (ha0 n).le (ha1 n)
      linarith
    linarith [inv_nonneg.mpr hl.le]

/-- The prime part of the row against a logarithmic profile is integrable on `(0, 1]`. -/
theorem integrableOn_logPow_mul_primeRemainder (j : ℕ) :
    IntegrableOn (fun t => logPow j t * primeRemainder t) (Set.Ioc 0 1) := by
  obtain ⟨C, hC, h⟩ := exists_abs_logPow_mul_primeRemainder_le j
  refine Integrable.mono' (integrableOn_logMajorant.const_mul C)
    ((measurable_logPow j).mul measurable_primeRemainder).aestronglyMeasurable ?_
  exact (ae_restrict_mem measurableSet_Ioc).mono fun t ht => by
    rw [Real.norm_eq_abs]
    exact h t ht

/-! ### The degree points below `N/K` -/

/-- **The telescoping bound.** For `2 ≤ K ≤ N`:
`Σ_{n ≤ N/K} 1/(n (1 + log(N/n))²) ≤ 2/(1 + log(K/2))`. -/
theorem sum_inv_mul_one_add_log_sq_le {N K : ℕ} (hK : 2 ≤ K) (hN : K ≤ N) :
    ∑ n ∈ Finset.Icc 1 (N / K), 1 / ((n : ℝ) * (1 + Real.log ((N : ℝ) / n)) ^ 2) ≤
      2 / (1 + Real.log ((K : ℝ) / 2)) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  have htel : ∀ m : ℕ, ∑ n ∈ Finset.Icc 1 m,
      (1 / (1 + Real.log ((N : ℝ) / (n + 1 : ℕ))) - 1 / (1 + Real.log ((N : ℝ) / n))) =
      1 / (1 + Real.log ((N : ℝ) / (m + 1 : ℕ))) - 1 / (1 + Real.log ((N : ℝ) / (1 : ℕ))) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [Finset.sum_Icc_succ_top (by omega), ih]
      ring
  have hmK : N / K * K ≤ N := Nat.div_mul_le_self N K
  have hm1 : N / K + 1 ≤ N := by
    have h2 : N / K * 2 ≤ N := (Nat.mul_le_mul_left _ hK).trans hmK
    omega
  have hterm : ∀ n ∈ Finset.Icc 1 (N / K),
      1 / ((n : ℝ) * (1 + Real.log ((N : ℝ) / n)) ^ 2) ≤
        2 * (1 / (1 + Real.log ((N : ℝ) / (n + 1 : ℕ))) - 1 / (1 + Real.log ((N : ℝ) / n))) := by
    intro n hn
    obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    have hn1' : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
    have hnN : ((n + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : n + 1 ≤ N)
    have hnle : (n : ℝ) ≤ N := by exact_mod_cast (by omega : n ≤ N)
    have ha : 0 ≤ Real.log ((N : ℝ) / n) :=
      Real.log_nonneg (by rw [le_div_iff₀ hn0]; linarith)
    have hb : 0 ≤ Real.log ((N : ℝ) / (n + 1 : ℕ)) :=
      Real.log_nonneg (by rw [le_div_iff₀ hn1']; linarith)
    have hab : 1 / (2 * (n : ℝ)) ≤ Real.log ((N : ℝ) / n) - Real.log ((N : ℝ) / (n + 1 : ℕ)) := by
      rw [Real.log_div hN0.ne' hn0.ne', Real.log_div hN0.ne' hn1'.ne']
      have h := Real.one_sub_inv_le_log_of_pos (div_pos hn1' hn0)
      rw [Real.log_div hn1'.ne' hn0.ne'] at h
      have h3 : 1 / (2 * (n : ℝ)) ≤ 1 - (((n + 1 : ℕ) : ℝ) / n)⁻¹ := by
        rw [inv_div, Nat.cast_succ, div_le_iff₀ (by positivity)]
        have : (1 - (n : ℝ) / ((n : ℝ) + 1)) * (2 * n) = 2 * n / ((n : ℝ) + 1) := by
          field_simp
          ring
        rw [this, le_div_iff₀ (by positivity)]
        have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
        linarith
      linarith
    have hdiff : 1 / (1 + Real.log ((N : ℝ) / (n + 1 : ℕ))) - 1 / (1 + Real.log ((N : ℝ) / n)) =
        (Real.log ((N : ℝ) / n) - Real.log ((N : ℝ) / (n + 1 : ℕ))) /
          ((1 + Real.log ((N : ℝ) / (n + 1 : ℕ))) * (1 + Real.log ((N : ℝ) / n))) := by
      field_simp
      ring
    have hhalf : (0 : ℝ) ≤ 1 / (2 * (n : ℝ)) := by positivity
    have hba : Real.log ((N : ℝ) / (n + 1 : ℕ)) ≤ Real.log ((N : ℝ) / n) := by linarith
    rw [hdiff, div_le_iff₀ (by positivity)]
    have hden : (1 + Real.log ((N : ℝ) / (n + 1 : ℕ))) * (1 + Real.log ((N : ℝ) / n)) ≤
        (1 + Real.log ((N : ℝ) / n)) ^ 2 := by nlinarith
    have hq : 0 ≤ (Real.log ((N : ℝ) / n) - Real.log ((N : ℝ) / (n + 1 : ℕ))) /
        ((1 + Real.log ((N : ℝ) / (n + 1 : ℕ))) * (1 + Real.log ((N : ℝ) / n))) := by
      apply div_nonneg <;> nlinarith
    have hstep : (Real.log ((N : ℝ) / n) - Real.log ((N : ℝ) / (n + 1 : ℕ))) /
        (1 + Real.log ((N : ℝ) / n)) ^ 2 ≤
        (Real.log ((N : ℝ) / n) - Real.log ((N : ℝ) / (n + 1 : ℕ))) /
          ((1 + Real.log ((N : ℝ) / (n + 1 : ℕ))) * (1 + Real.log ((N : ℝ) / n))) :=
      div_le_div_of_nonneg_left (by linarith) (by positivity) hden
    have hlow : 1 / (2 * (n : ℝ)) / (1 + Real.log ((N : ℝ) / n)) ^ 2 ≤
        (Real.log ((N : ℝ) / n) - Real.log ((N : ℝ) / (n + 1 : ℕ))) /
          (1 + Real.log ((N : ℝ) / n)) ^ 2 :=
      div_le_div_of_nonneg_right hab (by positivity)
    have hfin : 1 = 2 * (1 / (2 * (n : ℝ)) / (1 + Real.log ((N : ℝ) / n)) ^ 2) *
        ((n : ℝ) * (1 + Real.log ((N : ℝ) / n)) ^ 2) := by
      field_simp
    calc (1 : ℝ) = 2 * (1 / (2 * (n : ℝ)) / (1 + Real.log ((N : ℝ) / n)) ^ 2) *
          ((n : ℝ) * (1 + Real.log ((N : ℝ) / n)) ^ 2) := hfin
      _ ≤ 2 * ((Real.log ((N : ℝ) / n) - Real.log ((N : ℝ) / (n + 1 : ℕ))) /
            ((1 + Real.log ((N : ℝ) / (n + 1 : ℕ))) * (1 + Real.log ((N : ℝ) / n)))) *
          ((n : ℝ) * (1 + Real.log ((N : ℝ) / n)) ^ 2) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hlow.trans hstep) (by norm_num)) (by positivity)
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, htel]
  have hlast : (K : ℝ) / 2 ≤ (N : ℝ) / (N / K + 1 : ℕ) := by
    have hm0 : (0 : ℝ) < ((N / K + 1 : ℕ) : ℝ) := by positivity
    rw [div_le_div_iff₀ (by norm_num) hm0]
    have h1 : ((N / K * K : ℕ) : ℝ) ≤ N := by exact_mod_cast hmK
    have h2 : (K : ℝ) ≤ N := by exact_mod_cast hN
    push_cast at h1 ⊢
    nlinarith
  have hlogK : 0 ≤ Real.log ((K : ℝ) / 2) :=
    Real.log_nonneg (by rw [le_div_iff₀ (by norm_num)]; exact_mod_cast (by omega : 1 * 2 ≤ K))
  have hloglast : Real.log ((K : ℝ) / 2) ≤ Real.log ((N : ℝ) / (N / K + 1 : ℕ)) :=
    Real.log_le_log (by positivity) hlast
  have hfirst : 0 ≤ 1 / (1 + Real.log ((N : ℝ) / (1 : ℕ))) := by
    have : 0 ≤ Real.log ((N : ℝ) / (1 : ℕ)) :=
      Real.log_nonneg (by simpa using (by exact_mod_cast (by omega : 1 ≤ N) : (1 : ℝ) ≤ N))
    positivity
  have hle : 1 / (1 + Real.log ((N : ℝ) / (N / K + 1 : ℕ))) ≤ 1 / (1 + Real.log ((K : ℝ) / 2)) :=
    one_div_le_one_div_of_le (by linarith) (by linarith)
  rw [show (2 : ℝ) / (1 + Real.log ((K : ℝ) / 2)) = 2 * (1 / (1 + Real.log ((K : ℝ) / 2))) by ring]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  linarith

/-! ### Profiles of tails -/

/-- A profile of a tail that the row of the flat tail can be summed against: measurable,
continuous on `(0, 1]`, dominated by `c log^j(1/t)`, and with convergent Riemann sums after
every cut. -/
structure TailWeight (w : ℝ → ℝ) (j : ℕ) (c : ℝ) : Prop where
  measurable : Measurable w
  continuousOn : ContinuousOn w (Set.Ioc 0 1)
  abs_le : ∀ t ∈ Set.Ioc (0 : ℝ) 1, |w t| ≤ c * logPow j t
  cut : ∀ θ : ℝ, RiemannOn ((Set.Iic θ).indicator w)

theorem continuousOn_logPow (j : ℕ) : ContinuousOn (logPow j) (Set.Ioc 0 1) := fun t ht =>
  (((Real.continuousAt_log (one_div_pos.mpr ht.1).ne').comp
    (continuousAt_const.div continuousAt_id ht.1.ne')).pow j).continuousWithinAt

/-- The logarithmic profiles are profiles of tails. -/
theorem tailWeight_logPow (j : ℕ) : TailWeight (logPow j) j 1 where
  measurable := measurable_logPow j
  continuousOn := continuousOn_logPow j
  abs_le := fun t ht => by rw [abs_of_nonneg (logPow_nonneg j ht), one_mul]
  cut := fun θ => riemannOn_indicator_Iic (antitoneOn_logPow j) (fun t ht => logPow_nonneg j ht)
    (integrableOn_logPow j) θ

/-- The prime part of the row against a profile. -/
def primeProfile (w : ℝ → ℝ) (t : ℝ) : ℝ := w t * primeRemainder t

theorem psi_natCast_div (N n : ℕ) : Chebyshev.psi ((N : ℝ) / n) = chebyshev (N / n) := by
  rw [Chebyshev.psi_eq_sum_Icc, Nat.floor_div_eq_div, chebyshev]
  refine (Finset.sum_subset (Finset.Icc_subset_Icc_left (Nat.zero_le 1)) fun k hk hk' => ?_).symm
  have h1 := Finset.mem_Icc.mp hk
  have h2 : ¬ (1 ≤ k ∧ k ≤ N / n) := fun h => hk' (Finset.mem_Icc.mpr h)
  have h0 : k = 0 := by omega
  rw [h0, ArithmeticFunction.map_zero]

/-- Above `1/K` Chebyshev's function sees the first `K` prime powers only. -/
theorem psi_one_div_eq_sum {K : ℕ} (hK : 1 ≤ K) {t : ℝ} (ht0 : 0 < t) (htK : 1 / (K : ℝ) < t) :
    Chebyshev.psi (1 / t) = ∑ k ∈ Finset.Icc 1 K, if t ≤ 1 / (k : ℝ) then (Λ k : ℝ) else 0 := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hx0 : 0 ≤ 1 / t := by positivity
  have hfloor : ⌊1 / t⌋₊ ≤ K := Nat.floor_le_of_le ((one_div_lt hK0 ht0).mp htK).le
  have hfilter : (Finset.Icc 1 K).filter (fun k : ℕ => t ≤ 1 / (k : ℝ)) =
      Finset.Icc 1 ⌊1 / t⌋₊ := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hk1, -⟩, hk⟩
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      exact ⟨hk1, (Nat.le_floor_iff hx0).mpr ((le_one_div ht0 hk0).mp hk)⟩
    · rintro ⟨hk1, hk⟩
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
      exact ⟨⟨hk1, hk.trans hfloor⟩, (le_one_div ht0 hk0).mpr ((Nat.le_floor_iff hx0).mp hk)⟩
  rw [Chebyshev.psi_eq_sum_Icc, ← Finset.sum_filter, hfilter]
  refine (Finset.sum_subset (Finset.Icc_subset_Icc_left (Nat.zero_le 1)) fun k hk hk' => ?_).symm
  have h1 := Finset.mem_Icc.mp hk
  have h2 : ¬ (1 ≤ k ∧ k ≤ ⌊1 / t⌋₊) := fun h => hk' (Finset.mem_Icc.mpr h)
  have h0 : k = 0 := by omega
  rw [h0, ArithmeticFunction.map_zero]

/-- The prime part of the pairing of the flat tail with the tail of a profile is the Riemann
sum of the prime part of the row against the profile. -/
theorem tailRiemannSum_primeProfile_eq (w : ℝ → ℝ) (N : ℕ) :
    tailRiemannSum (primeProfile w) N =
      (∑ n ∈ Finset.Icc 1 N, w ((n : ℝ) / N) * ((N : ℝ) / n - chebyshev (N / n))) / N := by
  rw [tailRiemannSum]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [primeProfile, primeRemainder, one_div_div, psi_natCast_div]

namespace TailWeight

variable {w : ℝ → ℝ} {j : ℕ} {c : ℝ}

theorem const_nonneg (hw : TailWeight w j c) : 0 ≤ c := by
  have hmem : (1 / 2 : ℝ) ∈ Set.Ioc (0 : ℝ) 1 := ⟨by norm_num, by norm_num⟩
  have h := (abs_nonneg _).trans (hw.abs_le _ hmem)
  have hpos : 0 < logPow j (1 / 2) := by
    rw [logPow, one_div_one_div]
    exact pow_pos (Real.log_pos (by norm_num)) j
  exact nonneg_of_mul_nonneg_left h hpos

theorem measurable_primeProfile (hw : TailWeight w j c) : Measurable (primeProfile w) :=
  hw.measurable.mul measurable_primeRemainder

/-- The majorant of the prime part of the row against a profile. -/
theorem abs_primeProfile_le (hw : TailWeight w j c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1, |primeProfile w t| ≤ C * logMajorant t := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_logPow_mul_primeRemainder_le j
  refine ⟨c * C, mul_nonneg hw.const_nonneg hC0, fun t ht => ?_⟩
  have h1 := hw.abs_le t ht
  have h2 := hC t ht
  rw [abs_mul, abs_of_nonneg (logPow_nonneg j ht)] at h2
  rw [primeProfile, abs_mul]
  calc |w t| * |primeRemainder t| ≤ c * logPow j t * |primeRemainder t| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
    _ = c * (logPow j t * |primeRemainder t|) := by ring
    _ ≤ c * (C * logMajorant t) := mul_le_mul_of_nonneg_left h2 hw.const_nonneg
    _ = c * C * logMajorant t := by ring

theorem integrableOn_primeProfile (hw : TailWeight w j c) :
    IntegrableOn (primeProfile w) (Set.Ioc 0 1) := by
  obtain ⟨C, -, h⟩ := hw.abs_primeProfile_le
  refine Integrable.mono' (integrableOn_logMajorant.const_mul C)
    hw.measurable_primeProfile.aestronglyMeasurable ?_
  exact (ae_restrict_mem measurableSet_Ioc).mono fun t ht => by
    rw [Real.norm_eq_abs]
    exact h t ht

/-! ### The degree points above `N/K`: the hyperbola method -/

/-- **Above `1/K` the prime part of the row against a profile has convergent Riemann sums.** It
is the capped profile `w(t)/t` minus the cuts `Λ(k) w(t) 1[t ≤ 1/k]`, `k ≤ K`. -/
theorem riemannOn_cut_primeProfile (hw : TailWeight w j c) {K : ℕ} (hK : 1 ≤ K) :
    RiemannOn ((Set.Ioi (1 / (K : ℝ))).indicator (primeProfile w)) := by
  have hK0 : (0 : ℝ) < K := by exact_mod_cast hK
  have hc : (0 : ℝ) < 1 / (K : ℝ) := by positivity
  have hc1 : 1 / (K : ℝ) ≤ 1 := by
    rw [div_le_one hK0]
    exact_mod_cast hK
  have hc0 := hw.const_nonneg
  -- the capped smooth part
  have hA : RiemannOn (fun t : ℝ => w (max t (1 / (K : ℝ))) / max t (1 / (K : ℝ))) := by
    have hpos : ∀ t : ℝ, 0 < max t (1 / (K : ℝ)) := fun t => lt_max_of_lt_right hc
    have hmax : Continuous fun t : ℝ => max t (1 / (K : ℝ)) := continuous_id.max continuous_const
    have hmaps : Set.MapsTo (fun t : ℝ => max t (1 / (K : ℝ))) (Set.Ioc 0 1) (Set.Ioc 0 1) :=
      fun t ht => ⟨hpos t, max_le ht.2 hc1⟩
    have hcont : ContinuousOn (fun t : ℝ => w (max t (1 / (K : ℝ))) / max t (1 / (K : ℝ)))
        (Set.Ioc 0 1) :=
      (hw.continuousOn.comp hmax.continuousOn hmaps).div hmax.continuousOn
        fun t _ => (hpos t).ne'
    refine riemannOn_of_continuousOn_of_bounded (B := c * Real.log K ^ j * K) hcont
      fun t ht => ?_
    have hmem := hmaps ht
    have hinv : 1 / max t (1 / (K : ℝ)) ≤ K := by
      rw [div_le_iff₀ (hpos t)]
      calc (1 : ℝ) = K * (1 / K) := by field_simp
        _ ≤ K * max t (1 / (K : ℝ)) := mul_le_mul_of_nonneg_left (le_max_right _ _) hK0.le
    have hlog : Real.log (1 / max t (1 / (K : ℝ))) ≤ Real.log K :=
      Real.log_le_log (one_div_pos.mpr (hpos t)) hinv
    have hpowle : logPow j (max t (1 / (K : ℝ))) ≤ Real.log K ^ j :=
      pow_le_pow_left₀ (log_one_div_nonneg hmem) hlog j
    rw [abs_div, abs_of_pos (hpos t), div_eq_mul_one_div]
    exact mul_le_mul ((hw.abs_le _ hmem).trans (mul_le_mul_of_nonneg_left hpowle hc0)) hinv
      (one_div_nonneg.mpr (hpos t).le)
      (mul_nonneg hc0 (pow_nonneg (Real.log_nonneg (by exact_mod_cast hK)) j))
  -- the cuts
  have hone : RiemannOn ((Set.Iic (1 / (K : ℝ))).indicator fun _ : ℝ => (1 : ℝ)) :=
    riemannOn_indicator_Iic antitoneOn_const (fun _ _ => zero_le_one)
      (integrableOn_const (C := (1 : ℝ)) (by simp)) _
  have hcomb := (hA.sub (hone.const_mul (w (1 / (K : ℝ)) / (1 / (K : ℝ))))).sub
    (riemannOn_sum (Finset.Icc 1 K)
      (fun k t => (Λ k : ℝ) * ((Set.Iic (1 / (k : ℝ))).indicator w t -
        (Set.Iic (1 / (K : ℝ))).indicator w t))
      fun k _ => ((hw.cut _).sub (hw.cut _)).const_mul _)
  refine hcomb.congr fun t ht => ?_
  show w (max t (1 / (K : ℝ))) / max t (1 / (K : ℝ)) -
      w (1 / (K : ℝ)) / (1 / (K : ℝ)) *
        (Set.Iic (1 / (K : ℝ))).indicator (fun _ : ℝ => (1 : ℝ)) t -
      ∑ k ∈ Finset.Icc 1 K, (Λ k : ℝ) * ((Set.Iic (1 / (k : ℝ))).indicator w t -
        (Set.Iic (1 / (K : ℝ))).indicator w t) =
    (Set.Ioi (1 / (K : ℝ))).indicator (primeProfile w) t
  by_cases htK : t ≤ 1 / (K : ℝ)
  · -- below the cut everything cancels
    have hk : ∀ k ∈ Finset.Icc 1 K, t ≤ 1 / (k : ℝ) := fun k hk => by
      obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.mp hk
      exact htK.trans (one_div_le_one_div_of_le (by exact_mod_cast hk1) (by exact_mod_cast hk2))
    have hsum0 : ∑ k ∈ Finset.Icc 1 K, (Λ k : ℝ) *
        ((Set.Iic (1 / (k : ℝ))).indicator w t -
          (Set.Iic (1 / (K : ℝ))).indicator w t) = 0 :=
      Finset.sum_eq_zero fun k hk' => by
        rw [Set.indicator_of_mem (Set.mem_Iic.mpr (hk k hk')),
          Set.indicator_of_mem (Set.mem_Iic.mpr htK), sub_self, mul_zero]
    rw [hsum0, Set.indicator_of_notMem (s := Set.Ioi (1 / (K : ℝ))) (by simpa using htK),
      max_eq_right htK, Set.indicator_of_mem (Set.mem_Iic.mpr htK)]
    ring
  · -- above the cut: the hyperbola identity
    have htK' : 1 / (K : ℝ) < t := not_le.mp htK
    have hnot : t ∉ Set.Iic (1 / (K : ℝ)) := by simpa using htK'
    have hsum : ∑ k ∈ Finset.Icc 1 K, (Λ k : ℝ) *
        ((Set.Iic (1 / (k : ℝ))).indicator w t -
          (Set.Iic (1 / (K : ℝ))).indicator w t) =
        ∑ k ∈ Finset.Icc 1 K, w t * (if t ≤ 1 / (k : ℝ) then (Λ k : ℝ) else 0) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [Set.indicator_of_notMem hnot, sub_zero, Set.indicator_apply]
      simp only [Set.mem_Iic]
      split_ifs <;> ring
    rw [hsum, Set.indicator_of_mem (Set.mem_Ioi.mpr htK'), max_eq_left htK'.le,
      Set.indicator_of_notMem hnot, primeProfile, primeRemainder,
      psi_one_div_eq_sum hK ht.1 htK', mul_sub, Finset.mul_sum]
    ring

/-- The integrals over `(1/K, 1]` exhaust the integral. -/
theorem tendsto_integral_cut_primeProfile (hw : TailWeight w j c) :
    Tendsto (fun K : ℕ => ∫ t in Set.Ioc 0 1,
      (Set.Ioi (1 / (K : ℝ))).indicator (primeProfile w) t) atTop
      (𝓝 (∫ t in Set.Ioc 0 1, primeProfile w t)) := by
  refine tendsto_integral_of_dominated_convergence (fun t => |primeProfile w t|)
    (fun K => (hw.measurable_primeProfile.indicator measurableSet_Ioi).aestronglyMeasurable)
    hw.integrableOn_primeProfile.abs (fun K => Eventually.of_forall fun t => ?_) ?_
  · rw [Real.norm_eq_abs, Set.indicator_apply]
    split_ifs
    · exact le_rfl
    · rw [abs_zero]
      exact abs_nonneg _
  · refine (ae_restrict_mem measurableSet_Ioc).mono fun t ht => ?_
    refine tendsto_const_nhds.congr' ?_
    have h := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).eventually (gt_mem_nhds ht.1)
    filter_upwards [h] with K hK
    rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hK)]

/-! ### The limit -/

/-- **The prime part of the row integrates every profile of a tail**: the Riemann sums of
`w(t)(1/t − ψ(1/t))` at the degree points tend to its integral. -/
theorem tendsto_tailRiemannSum_primeProfile (hw : TailWeight w j c) :
    Tendsto (fun N : ℕ => tailRiemannSum (primeProfile w) N) atTop
      (𝓝 (∫ t in Set.Ioc 0 1, primeProfile w t)) := by
  obtain ⟨C, hC0, hC⟩ := hw.abs_primeProfile_le
  -- the points below `N/K`
  have hsmall : ∀ K N : ℕ, 2 ≤ K → K ≤ N →
      |tailRiemannSum (primeProfile w) N -
        tailRiemannSum ((Set.Ioi (1 / (K : ℝ))).indicator (primeProfile w)) N| ≤
        C * (2 / (1 + Real.log ((K : ℝ) / 2))) := by
    intro K N hK hN
    have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    have hK0 : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
    have hsub : Finset.Icc 1 (N / K) ⊆ Finset.Icc 1 N :=
      Finset.Icc_subset_Icc_right (Nat.div_le_self N K)
    have hdiff : tailRiemannSum (primeProfile w) N -
        tailRiemannSum ((Set.Ioi (1 / (K : ℝ))).indicator (primeProfile w)) N =
        (∑ n ∈ Finset.Icc 1 (N / K), primeProfile w ((n : ℝ) / N)) / N := by
      rw [tailRiemannSum, tailRiemannSum, ← sub_div, ← Finset.sum_sub_distrib]
      congr 1
      rw [← Finset.sum_subset hsub]
      · refine Finset.sum_congr rfl fun n hn => ?_
        obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
        have hnK : n * K ≤ N := (Nat.le_div_iff_mul_le (by omega)).mp hn2
        have hle : (n : ℝ) / N ≤ 1 / (K : ℝ) := by
          rw [div_le_div_iff₀ hN0 hK0, one_mul]
          exact_mod_cast hnK
        rw [Set.indicator_of_notMem (by simpa using hle), sub_zero]
      · intro n hn hn'
        obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.mp hn
        have h3 : ¬ n ≤ N / K := fun h => hn' (Finset.mem_Icc.mpr ⟨hn1, h⟩)
        have hnK : N < n * K := by
          rw [Nat.le_div_iff_mul_le (by omega)] at h3
          omega
        have hlt : 1 / (K : ℝ) < (n : ℝ) / N := by
          rw [div_lt_div_iff₀ hK0 hN0, one_mul]
          exact_mod_cast hnK
        rw [Set.indicator_of_mem (Set.mem_Ioi.mpr hlt), sub_self]
    have hterm : ∀ n ∈ Finset.Icc 1 (N / K), |primeProfile w ((n : ℝ) / N)| ≤
        C * N * (1 / ((n : ℝ) * (1 + Real.log ((N : ℝ) / n)) ^ 2)) := by
      intro n hn
      have hmem : (n : ℝ) / N ∈ Set.Ioc (0 : ℝ) 1 := natCast_div_mem_Ioc (hsub hn)
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (Finset.mem_Icc.mp hn).1
      have hpos : 0 < 1 + Real.log ((N : ℝ) / n) := by
        have := log_one_div_nonneg hmem
        rw [one_div_div] at this
        linarith
      refine (hC _ hmem).trans (le_of_eq ?_)
      rw [logMajorant, one_div_div]
      field_simp
    rw [hdiff, abs_div, abs_of_pos hN0, div_le_iff₀ hN0]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
    rw [← Finset.mul_sum]
    calc C * N * ∑ n ∈ Finset.Icc 1 (N / K), 1 / ((n : ℝ) * (1 + Real.log ((N : ℝ) / n)) ^ 2)
        ≤ C * N * (2 / (1 + Real.log ((K : ℝ) / 2))) :=
          mul_le_mul_of_nonneg_left (sum_inv_mul_one_add_log_sq_le hK hN) (by positivity)
      _ = C * (2 / (1 + Real.log ((K : ℝ) / 2))) * N := by ring
  -- the choice of `K`
  have hK1 := hw.tendsto_integral_cut_primeProfile
  have hK2 : Tendsto (fun K : ℕ => C * (2 / (1 + Real.log ((K : ℝ) / 2)))) atTop (𝓝 0) := by
    have h1 : Tendsto (fun K : ℕ => 1 + Real.log ((K : ℝ) / 2)) atTop atTop :=
      tendsto_atTop_add_const_left _ 1 (Real.tendsto_log_atTop.comp
        ((tendsto_natCast_atTop_atTop (R := ℝ)).atTop_div_const (by norm_num)))
    have h2 := ((tendsto_const_nhds (x := (2 : ℝ))).div_atTop h1).const_mul C
    rwa [mul_zero] at h2
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨K1, hK1'⟩ := (Metric.tendsto_atTop.mp hK1) (ε / 3) (by positivity)
  obtain ⟨K2, hK2'⟩ := (Metric.tendsto_atTop.mp hK2) (ε / 3) (by positivity)
  obtain ⟨K, hKdef⟩ : ∃ K : ℕ, K = max 2 (max K1 K2) := ⟨_, rfl⟩
  have hKa : 2 ≤ K := hKdef ▸ le_max_left _ _
  have hKb := hK1' K (hKdef ▸ (le_max_left K1 K2).trans (le_max_right _ _))
  have hKc := hK2' K (hKdef ▸ (le_max_right K1 K2).trans (le_max_right _ _))
  obtain ⟨N₀, hN₀⟩ := (Metric.tendsto_atTop.mp
    (hw.riemannOn_cut_primeProfile (by omega : 1 ≤ K)).2) (ε / 3) (by positivity)
  refine ⟨max N₀ K, fun N hN => ?_⟩
  have h1 := hN₀ N (le_of_max_le_left hN)
  have h2 := hsmall K N hKa (le_of_max_le_right hN)
  rw [Real.dist_eq] at h1 hKb hKc
  rw [sub_zero] at hKc
  have h3 : C * (2 / (1 + Real.log ((K : ℝ) / 2))) < ε / 3 := lt_of_le_of_lt (le_abs_self _) hKc
  rw [Real.dist_eq]
  have hsplit : tailRiemannSum (primeProfile w) N - ∫ t in Set.Ioc 0 1, primeProfile w t =
      (tailRiemannSum (primeProfile w) N -
        tailRiemannSum ((Set.Ioi (1 / (K : ℝ))).indicator (primeProfile w)) N) +
      (tailRiemannSum ((Set.Ioi (1 / (K : ℝ))).indicator (primeProfile w)) N -
        ∫ t in Set.Ioc 0 1, (Set.Ioi (1 / (K : ℝ))).indicator (primeProfile w) t) +
      ((∫ t in Set.Ioc 0 1, (Set.Ioi (1 / (K : ℝ))).indicator (primeProfile w) t) -
        ∫ t in Set.Ioc 0 1, primeProfile w t) := by ring
  rw [hsplit]
  exact (abs_add_three _ _ _).trans_lt (by linarith)

end TailWeight

/-- **The prime part of the row has logarithmic moments**:
`(1/N) Σ_{n ≤ N} log^j(N/n) (N/n − ψ(N/n)) → κ_j`. -/
theorem tendsto_sum_logTail_mul_primeRemainder (j : ℕ) :
    Tendsto (fun N : ℕ =>
      (∑ n ∈ Finset.Icc 1 N, logTail j N n * ((N : ℝ) / n - chebyshev (N / n))) / N) atTop
      (𝓝 (primeMoment j)) := by
  refine (tailWeight_logPow j).tendsto_tailRiemannSum_primeProfile.congr fun N => ?_
  rw [tailRiemannSum_primeProfile_eq]
  congr 1
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [logPow, one_div_div, logTail]

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
