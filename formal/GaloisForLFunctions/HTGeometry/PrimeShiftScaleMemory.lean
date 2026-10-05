import GaloisForLFunctions.HTGeometry.ArithmeticPrimeShiftSource

/-!
# Ordered two-letter scale memory of the prime-shift source

Multiplicative endpoints commute, `V_m V_n = V_n V_m`, but the generated second responses
`D^{(2)}_{m|n}(t) = ∫_{0<r<s<t} S_{t-s} V_m S_{s-r} V_n S_r dr ds` `(APS.16)` do not.  The
intertwining `S_t V_m = m^{-t} V_m S_t` collapses each to a scalar multiple of `V_{mn} S_t`:
`D^{(2)}_{m|n}(t) = B_{a,b}(t) V_{mn} S_t`, `a = log m`, `b = log n`, with the simplex kernel
`B_{a,b}(t) = ∫∫_{u,v ≥ 0, u+v ≤ t} e^{-(a+b)u - bv}` `(APS.17)`–`(APS.18)`.  The ordered defect
is `Ω_{m,n}(t) = ω_t(a,b) V_{mn} S_t` with
`ω_t(a,b) = ∫∫ e^{-(a+b)u} (e^{-bv} - e^{-av})` `(APS.19)`–`(APS.20)`; for `t > 0` its sign is the
sign of `a - b` and it vanishes exactly when `m = n` `(APS.21)`.  For the normalized letters the
defect is `ab ω_t(a,b) V_{mn} S_t` `(APS.22)`, whose vacuum work `a² b² ω_t(a,b)²` keeps the
magnitude and loses the sign `(APS.23)`.
-/

open scoped InnerProductSpace
open MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry.PrimeShiftSource

/-- The ordered second response `∫₀ᵗ ∫₀ˢ S_{t-s} X S_{s-r} Y S_r dr ds` `(APS.16)`. -/
def orderedResponse (X Y : ArithSpace →L[ℂ] ArithSpace) (t : ℝ) : ArithSpace →L[ℂ] ArithSpace :=
  ∫ s in (0 : ℝ)..t, ∫ r in (0 : ℝ)..s, heat (t - s) * X * heat (s - r) * Y * heat r

/-- The simplex kernel `B_{a,b}(t) = ∫₀ᵗ ∫₀^{t-u} e^{-(a+b)u - bv} dv du` `(APS.17)`. -/
def simplexKernel (a b t : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..(t - u), Real.exp (-(a + b) * u - b * v)

/-- The ordered defect kernel `ω_t(a,b) = B_{a,b}(t) - B_{b,a}(t)`. -/
def defectKernel (t a b : ℝ) : ℝ := simplexKernel a b t - simplexKernel b a t

theorem rpow_eq_exp {m : ℕ+} (x : ℝ) :
    ((m : ℕ) : ℝ) ^ x = Real.exp (Real.log ((m : ℕ) : ℝ) * x) :=
  Real.rpow_def_of_pos (by exact_mod_cast m.pos) x

/-- The integrand of `(APS.16)` collapses: for `0 ≤ r ≤ s ≤ t`,
`S_{t-s} V_m S_{s-r} V_n S_r = m^{-(t-s)} n^{-(t-r)} V_{mn} S_t`. -/
theorem orderedIntegrand_eq (m n : ℕ+) {r s t : ℝ} (hr : 0 ≤ r) (hrs : r ≤ s) (hst : s ≤ t) :
    heat (t - s) * shift m * heat (s - r) * shift n * heat r =
      (((((m : ℕ) : ℝ) ^ (-(t - s)) * ((n : ℕ) : ℝ) ^ (-(t - r))) : ℝ) : ℂ) •
        (shift (m * n) * heat t) := by
  have hts : 0 ≤ t - s := sub_nonneg.mpr hst
  have hsr : 0 ≤ s - r := sub_nonneg.mpr hrs
  have htr : 0 ≤ t - r := by linarith
  have h1 : heat (t - s) * heat (s - r) = heat (t - r) := by
    rw [← heat_add hts hsr]
    ring_nf
  have h2 : heat (t - r) * heat r = heat t := by
    rw [← heat_add htr hr]
    ring_nf
  calc heat (t - s) * shift m * heat (s - r) * shift n * heat r
      = (heat (t - s) * shift m) * heat (s - r) * shift n * heat r := rfl
    _ = ((((m : ℕ) : ℝ) ^ (-(t - s)) : ℝ) : ℂ) •
          (shift m * (heat (t - s) * heat (s - r)) * shift n * heat r) := by
        rw [heat_mul_shift hts]
        simp only [smul_mul_assoc, mul_assoc]
    _ = ((((m : ℕ) : ℝ) ^ (-(t - s)) : ℝ) : ℂ) •
          (shift m * (heat (t - r) * shift n) * heat r) := by
        rw [h1]
        simp only [mul_assoc]
    _ = ((((m : ℕ) : ℝ) ^ (-(t - s)) : ℝ) : ℂ) • ((((n : ℕ) : ℝ) ^ (-(t - r)) : ℝ) : ℂ) •
          (shift m * shift n * (heat (t - r) * heat r)) := by
        rw [heat_mul_shift htr]
        simp only [mul_smul_comm, smul_mul_assoc, mul_assoc]
    _ = _ := by
        rw [h2, shift_mul, smul_smul, ← Complex.ofReal_mul]

/-- The scalar coefficient of `(APS.16)` is the simplex kernel. -/
theorem iterated_eq_simplexKernel (a b t : ℝ) :
    ∫ s in (0 : ℝ)..t, Real.exp (a * (-(t - s))) * ∫ r in (0 : ℝ)..s, Real.exp (b * (-(t - r))) =
      simplexKernel a b t := by
  have hinner : ∀ s, ∫ r in (0 : ℝ)..s, Real.exp (b * (-(t - r))) =
      ∫ v in (0 : ℝ)..s, Real.exp (-b * (t - s + v)) := fun s => by
    have h := intervalIntegral.integral_comp_sub_left
      (fun v => Real.exp (-b * (t - s + v))) (a := 0) (b := s) s
    simp only [sub_self, sub_zero] at h
    rw [← h]
    refine intervalIntegral.integral_congr fun r _ => ?_
    show Real.exp (b * (-(t - r))) = Real.exp (-b * (t - s + (s - r)))
    ring_nf
  simp_rw [hinner]
  set g : ℝ → ℝ := fun u => Real.exp (a * (-u)) * ∫ v in (0 : ℝ)..(t - u), Real.exp (-b * (u + v))
  have hg : ∀ s, Real.exp (a * (-(t - s))) * ∫ v in (0 : ℝ)..s, Real.exp (-b * (t - s + v)) =
      g (t - s) := fun s => by
    simp only [g, sub_sub_cancel]
  simp_rw [hg]
  rw [intervalIntegral.integral_comp_sub_left g t]
  simp only [sub_self, sub_zero, simplexKernel]
  refine intervalIntegral.integral_congr fun u _ => ?_
  simp only [g]
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun v _ => ?_
  show Real.exp (a * (-u)) * Real.exp (-b * (u + v)) = Real.exp (-(a + b) * u - b * v)
  rw [← Real.exp_add]
  ring_nf

/-- **`(APS.18)`**: `D^{(2)}_{m|n}(t) = B_{log m, log n}(t) V_{mn} S_t`. -/
theorem orderedResponse_shift {t : ℝ} (ht : 0 ≤ t) (m n : ℕ+) :
    orderedResponse (shift m) (shift n) t =
      ((simplexKernel (Real.log ((m : ℕ) : ℝ)) (Real.log ((n : ℕ) : ℝ)) t : ℝ) : ℂ) •
        (shift (m * n) * heat t) := by
  have hinner : ∀ s ∈ uIcc (0 : ℝ) t,
      ∫ r in (0 : ℝ)..s, heat (t - s) * shift m * heat (s - r) * shift n * heat r =
        (((Real.exp (Real.log ((m : ℕ) : ℝ) * (-(t - s))) *
          ∫ r in (0 : ℝ)..s, Real.exp (Real.log ((n : ℕ) : ℝ) * (-(t - r)))) : ℝ) : ℂ) •
          (shift (m * n) * heat t) := fun s hs => by
    rw [uIcc_of_le ht] at hs
    have hcongr : ∀ r ∈ uIcc (0 : ℝ) s,
        heat (t - s) * shift m * heat (s - r) * shift n * heat r =
          (((Real.exp (Real.log ((m : ℕ) : ℝ) * (-(t - s))) *
            Real.exp (Real.log ((n : ℕ) : ℝ) * (-(t - r)))) : ℝ) : ℂ) •
            (shift (m * n) * heat t) := fun r hr => by
      rw [uIcc_of_le hs.1] at hr
      rw [orderedIntegrand_eq m n hr.1 hr.2 hs.2, rpow_eq_exp, rpow_eq_exp]
    rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_smul_const,
      intervalIntegral.integral_ofReal, intervalIntegral.integral_const_mul]
  rw [orderedResponse, intervalIntegral.integral_congr hinner, intervalIntegral.integral_smul_const,
    intervalIntegral.integral_ofReal, iterated_eq_simplexKernel]

/-- **`(APS.19)`: the ordered response defect** `Ω_{m,n}(t) = ω_t(a,b) V_{mn} S_t`. -/
theorem orderedDefect_shift {t : ℝ} (ht : 0 ≤ t) (m n : ℕ+) :
    orderedResponse (shift m) (shift n) t - orderedResponse (shift n) (shift m) t =
      ((defectKernel t (Real.log ((m : ℕ) : ℝ)) (Real.log ((n : ℕ) : ℝ)) : ℝ) : ℂ) •
        (shift (m * n) * heat t) := by
  rw [orderedResponse_shift ht, orderedResponse_shift ht, mul_comm n m, ← sub_smul,
    defectKernel, Complex.ofReal_sub]

/-! ### The defect kernel -/

theorem continuous_exp_primitive (b : ℝ) :
    Continuous fun x => ∫ v in (0 : ℝ)..x, Real.exp (-b * v) :=
  intervalIntegral.continuous_primitive (fun _ _ => (by fun_prop : Continuous fun v : ℝ =>
    Real.exp (-b * v)).intervalIntegrable _ _) 0

theorem inner_simplex_eq (a b t u : ℝ) :
    ∫ v in (0 : ℝ)..(t - u), Real.exp (-(a + b) * u - b * v) =
      Real.exp (-(a + b) * u) * ∫ v in (0 : ℝ)..(t - u), Real.exp (-b * v) := by
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr fun v _ => ?_
  show Real.exp (-(a + b) * u - b * v) = Real.exp (-(a + b) * u) * Real.exp (-b * v)
  rw [← Real.exp_add]
  ring_nf

theorem continuous_inner_simplex (a b t : ℝ) :
    Continuous fun u => ∫ v in (0 : ℝ)..(t - u), Real.exp (-(a + b) * u - b * v) := by
  simp_rw [inner_simplex_eq]
  exact (by fun_prop : Continuous fun u : ℝ => Real.exp (-(a + b) * u)).mul
    ((continuous_exp_primitive b).comp (continuous_const.sub continuous_id))

/-- The difference kernel `K_{a,b}(x) = ∫₀ˣ (e^{-bv} - e^{-av}) dv`. -/
def differenceKernel (a b x : ℝ) : ℝ := ∫ v in (0 : ℝ)..x, (Real.exp (-b * v) - Real.exp (-a * v))

theorem continuous_differenceKernel (a b : ℝ) : Continuous (differenceKernel a b) :=
  intervalIntegral.continuous_primitive (fun _ _ => (by fun_prop : Continuous fun v : ℝ =>
    Real.exp (-b * v) - Real.exp (-a * v)).intervalIntegrable _ _) 0

/-- **`(APS.20)`**: `ω_t(a,b) = ∫₀ᵗ ∫₀^{t-u} e^{-(a+b)u} (e^{-bv} - e^{-av}) dv du`. -/
theorem defectKernel_eq (t a b : ℝ) :
    defectKernel t a b =
      ∫ u in (0 : ℝ)..t, ∫ v in (0 : ℝ)..(t - u),
        Real.exp (-(a + b) * u) * (Real.exp (-b * v) - Real.exp (-a * v)) := by
  rw [defectKernel, simplexKernel, simplexKernel, ← intervalIntegral.integral_sub
    ((continuous_inner_simplex a b t).intervalIntegrable _ _)
    ((continuous_inner_simplex b a t).intervalIntegrable _ _)]
  refine intervalIntegral.integral_congr fun u _ => ?_
  show (∫ v in (0 : ℝ)..(t - u), Real.exp (-(a + b) * u - b * v)) -
      ∫ v in (0 : ℝ)..(t - u), Real.exp (-(b + a) * u - a * v) = _
  rw [inner_simplex_eq, inner_simplex_eq, add_comm b a, ← mul_sub,
    ← intervalIntegral.integral_sub ((by fun_prop : Continuous fun v : ℝ =>
      Real.exp (-b * v)).intervalIntegrable _ _) ((by fun_prop : Continuous fun v : ℝ =>
      Real.exp (-a * v)).intervalIntegrable _ _), ← intervalIntegral.integral_const_mul]

theorem defectKernel_eq_outer (t a b : ℝ) :
    defectKernel t a b =
      ∫ u in (0 : ℝ)..t, Real.exp (-(a + b) * u) * differenceKernel a b (t - u) := by
  rw [defectKernel_eq]
  refine intervalIntegral.integral_congr fun u _ => ?_
  rw [differenceKernel, intervalIntegral.integral_const_mul]

theorem defectKernel_swap (t a b : ℝ) : defectKernel t b a = -defectKernel t a b := by
  rw [defectKernel, defectKernel, neg_sub]

theorem defectKernel_self (t a : ℝ) : defectKernel t a a = 0 := sub_self _

theorem differenceKernel_pos {a b x : ℝ} (hab : b < a) (hx : 0 < x) :
    0 < differenceKernel a b x :=
  intervalIntegral.intervalIntegral_pos_of_pos_on
    ((by fun_prop : Continuous fun v : ℝ =>
      Real.exp (-b * v) - Real.exp (-a * v)).intervalIntegrable _ _)
    (fun v hv => sub_pos.mpr (Real.exp_lt_exp.mpr (by nlinarith [hv.1]))) hx

/-- **`(APS.21)`, positive orientation**: `a > b`, `t > 0` give `ω_t(a,b) > 0`. -/
theorem defectKernel_pos {t a b : ℝ} (ht : 0 < t) (hab : b < a) : 0 < defectKernel t a b := by
  rw [defectKernel_eq_outer]
  refine intervalIntegral.intervalIntegral_pos_of_pos_on
    (((by fun_prop : Continuous fun u : ℝ => Real.exp (-(a + b) * u)).mul
      ((continuous_differenceKernel a b).comp
        (continuous_const.sub continuous_id))).intervalIntegrable _ _) (fun u hu => mul_pos (Real.exp_pos _) (differenceKernel_pos hab (by linarith [hu.2]))) ht

/-- **`(APS.21)`**: `sgn ω_t(a,b) = sgn(a - b)` for `t > 0`. -/
theorem sign_defectKernel {t : ℝ} (ht : 0 < t) (a b : ℝ) :
    SignType.sign (defectKernel t a b) = SignType.sign (a - b) := by
  rcases lt_trichotomy b a with hab | hab | hab
  · rw [sign_pos (defectKernel_pos ht hab), sign_pos (sub_pos.mpr hab)]
  · rw [hab, defectKernel_self, sub_self]
  · rw [← neg_neg (defectKernel t a b), ← defectKernel_swap, sign_neg (neg_neg_of_pos
      (defectKernel_pos ht hab)), sign_neg (sub_neg.mpr hab)]

/-- **`(APS.21)`**: `ω_t(log m, log n) = 0` exactly when `m = n`. -/
theorem defectKernel_eq_zero_iff {t : ℝ} (ht : 0 < t) (m n : ℕ+) :
    defectKernel t (Real.log ((m : ℕ) : ℝ)) (Real.log ((n : ℕ) : ℝ)) = 0 ↔ m = n := by
  constructor
  · intro h
    have hs := sign_defectKernel ht (Real.log ((m : ℕ) : ℝ)) (Real.log ((n : ℕ) : ℝ))
    rw [h, sign_zero, eq_comm, sign_eq_zero_iff, sub_eq_zero] at hs
    have hm : (0 : ℝ) < ((m : ℕ) : ℝ) := by exact_mod_cast m.pos
    have hn : (0 : ℝ) < ((n : ℕ) : ℝ) := by exact_mod_cast n.pos
    have := Real.log_injOn_pos (Set.mem_Ioi.mpr hm) (Set.mem_Ioi.mpr hn) hs
    exact PNat.coe_inj.mp (by exact_mod_cast this)
  · rintro rfl
    exact defectKernel_self t _

/-! ### Normalized letters -/

/-- `(APS.22)`, letters: `A_m = (log m) V_m` gives the second response `ab D^{(2)}_{m|n}`. -/
theorem orderedResponse_letter (m n : ℕ+) (t : ℝ) :
    orderedResponse (letter m) (letter n) t =
      ((Real.log ((m : ℕ) : ℝ) * Real.log ((n : ℕ) : ℝ) : ℝ) : ℂ) •
        orderedResponse (shift m) (shift n) t := by
  have h : ∀ s r, heat (t - s) * letter m * heat (s - r) * letter n * heat r =
      ((Real.log ((m : ℕ) : ℝ) * Real.log ((n : ℕ) : ℝ) : ℝ) : ℂ) •
        (heat (t - s) * shift m * heat (s - r) * shift n * heat r) := fun s r => by
    simp only [letter, mul_smul_comm, smul_mul_assoc, smul_smul, Complex.ofReal_mul]
    ring_nf
  simp_rw [orderedResponse, h, intervalIntegral.integral_smul]

/-- **`(APS.22)`: the normalized ordered defect** `Ω̃_{m,n}(t) = ab ω_t(a,b) V_{mn} S_t`. -/
theorem orderedDefect_letter {t : ℝ} (ht : 0 ≤ t) (m n : ℕ+) :
    orderedResponse (letter m) (letter n) t - orderedResponse (letter n) (letter m) t =
      ((Real.log ((m : ℕ) : ℝ) * Real.log ((n : ℕ) : ℝ) *
        defectKernel t (Real.log ((m : ℕ) : ℝ)) (Real.log ((n : ℕ) : ℝ)) : ℝ) : ℂ) •
        (shift (m * n) * heat t) := by
  rw [orderedResponse_letter, orderedResponse_letter, mul_comm (Real.log ((n : ℕ) : ℝ)),
    ← smul_sub, orderedDefect_shift ht, smul_smul, ← Complex.ofReal_mul]

/-- **`(APS.22)`, orientation**: on the vacuum the oriented coefficient has the sign of
`log m - log n`. -/
theorem sign_normalizedDefect {t : ℝ} (ht : 0 < t) {m n : ℕ+} (hm : 2 ≤ (m : ℕ))
    (hn : 2 ≤ (n : ℕ)) :
    SignType.sign (Real.log ((m : ℕ) : ℝ) * Real.log ((n : ℕ) : ℝ) *
        defectKernel t (Real.log ((m : ℕ) : ℝ)) (Real.log ((n : ℕ) : ℝ))) =
      SignType.sign (Real.log ((m : ℕ) : ℝ) - Real.log ((n : ℕ) : ℝ)) := by
  have ha : 0 < Real.log ((m : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast hm)
  have hb : 0 < Real.log ((n : ℕ) : ℝ) := Real.log_pos (by exact_mod_cast hn)
  rw [sign_mul, sign_pos (mul_pos ha hb), one_mul, sign_defectKernel ht]

/-- **`(APS.23)`: positive work** `‖Ω̃_{m,n}(t) e_1‖² = a² b² ω_t(a,b)²`; it erases the sign. -/
theorem norm_normalizedDefect_vacuum_sq {t : ℝ} (ht : 0 ≤ t) (m n : ℕ+) :
    ‖(orderedResponse (letter m) (letter n) t - orderedResponse (letter n) (letter m) t)
        (basisVec 1)‖ ^ 2 =
      Real.log ((m : ℕ) : ℝ) ^ 2 * Real.log ((n : ℕ) : ℝ) ^ 2 *
        defectKernel t (Real.log ((m : ℕ) : ℝ)) (Real.log ((n : ℕ) : ℝ)) ^ 2 := by
  rw [orderedDefect_letter ht, smul_apply, mul_apply_eq_comp, heat_vacuum, shift_vacuum,
    norm_smul, norm_basisVec, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  ring

end GaloisForLFunctions.HTGeometry.PrimeShiftSource
