import GaloisForLFunctions.HTGeometry.HolderShiftElimination
import GaloisForLFunctions.HTGeometry.QPochhammer

/-!
# The two-variable q-shift field

Pastro's q-analogue of Hölder's theorem runs the shift elimination over `ℂ(z, u)` with `u = qᶻ`,
where the shift acts by `z ↦ z+1` on the coefficients and by `u ↦ q·u` on the variable.  This file
builds that field and its shift endomorphism, and proves the scaled form of the shift-periodicity
brick: a nonzero rational function whose unit shift is a constant multiple of itself forces the
constant to be one.
-/

namespace GaloisForLFunctions.HTGeometry

set_option maxSynthPendingDepth 4

open Polynomial nonZeroDivisors

noncomputable section

/-- The nome as a constant of the coefficient field `ℂ(z)`. -/
def qConst (q : RealEulerNome) : RatFunc ℂ := algebraMap ℂ (RatFunc ℂ) (q.val : ℂ)

theorem qConst_ne_zero (q : RealEulerNome) : qConst q ≠ 0 := by
  intro h0
  rw [qConst] at h0
  exact q.complex_ne_zero
    ((algebraMap ℂ (RatFunc ℂ)).injective (h0.trans (map_zero _).symm))

/-- The polynomial-level q-shift: coefficients shift by `z ↦ z+1`, the variable scales by `q`. -/
def qShiftPolyMap (q : RealEulerNome) : Polynomial (RatFunc ℂ) →+* Polynomial (RatFunc ℂ) :=
  (Polynomial.eval₂RingHom Polynomial.C (Polynomial.C (qConst q) * Polynomial.X)).comp
    (Polynomial.mapRingHom GaloisForLFunctions.ratShift)

theorem qShiftPolyMap_apply (q : RealEulerNome) (p : Polynomial (RatFunc ℂ)) :
    qShiftPolyMap q p
      = (p.map GaloisForLFunctions.ratShift).comp (Polynomial.C (qConst q) * Polynomial.X) := rfl

theorem qShiftPolyMap_ne_zero (q : RealEulerNome) {p : Polynomial (RatFunc ℂ)} (hp : p ≠ 0) :
    qShiftPolyMap q p ≠ 0 := by
  rw [qShiftPolyMap_apply]
  have hmap : p.map GaloisForLFunctions.ratShift ≠ 0 := by
    intro h0
    exact hp (Polynomial.map_injective _ GaloisForLFunctions.ratShift_injective
      (by rw [h0, Polynomial.map_zero]))
  intro h0
  have hlead : ((p.map GaloisForLFunctions.ratShift).comp
      (Polynomial.C (qConst q) * Polynomial.X)).leadingCoeff = 0 := by
    rw [h0, Polynomial.leadingCoeff_zero]
  rw [Polynomial.leadingCoeff_comp (by
    rw [Polynomial.natDegree_C_mul_X _ (qConst_ne_zero q)]
    exact one_ne_zero)] at hlead
  have hlc : (Polynomial.C (qConst q) * Polynomial.X : Polynomial (RatFunc ℂ)).leadingCoeff
      = qConst q := by
    rw [Polynomial.leadingCoeff_C_mul_X]
  rw [hlc] at hlead
  rcases mul_eq_zero.mp hlead with h | h
  · exact hmap (Polynomial.leadingCoeff_eq_zero.mp h)
  · exact qConst_ne_zero q (pow_eq_zero_iff'.mp h).1

/-- The polynomial-level q-shift, landing in the field. -/
def qShiftCompHom (q : RealEulerNome) : Polynomial (RatFunc ℂ) →+* RatFunc (RatFunc ℂ) :=
  (algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))).comp (qShiftPolyMap q)

theorem qShiftCompHom_apply (q : RealEulerNome) (p : Polynomial (RatFunc ℂ)) :
    qShiftCompHom q p = algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (qShiftPolyMap q p) := rfl

theorem qShiftCompHom_mem_nonZeroDivisors (q : RealEulerNome) :
    (Polynomial (RatFunc ℂ))⁰ ≤ (RatFunc (RatFunc ℂ))⁰.comap (qShiftCompHom q) := by
  intro p hp
  rw [Submonoid.mem_comap]
  refine mem_nonZeroDivisors_of_ne_zero ?_
  have hp0 : p ≠ 0 := nonZeroDivisors.ne_zero hp
  rw [qShiftCompHom_apply]
  intro h0
  exact qShiftPolyMap_ne_zero q hp0
    (RatFunc.algebraMap_injective (RatFunc ℂ) (by rw [h0, map_zero]))

/-- **The q-shift** `f(z, u) ↦ f(z+1, q·u)` of the two-variable field. -/
def qShift (q : RealEulerNome) : RatFunc (RatFunc ℂ) →+* RatFunc (RatFunc ℂ) :=
  RatFunc.liftRingHom (qShiftCompHom q) (qShiftCompHom_mem_nonZeroDivisors q)

theorem qShift_injective (q : RealEulerNome) : Function.Injective (qShift q) :=
  (qShift q).injective

theorem qShift_algebraMap (q : RealEulerNome) (p : Polynomial (RatFunc ℂ)) :
    qShift q (algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) p)
      = algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (qShiftPolyMap q p) := by
  have h := RatFunc.liftRingHom_apply_div (qShiftCompHom q)
    (qShiftCompHom_mem_nonZeroDivisors q) p 1
  simp [qShift, qShiftCompHom_apply]

theorem algebraMap_polyC_qShiftField (c : RatFunc ℂ) :
    algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (Polynomial.C c)
      = algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ)) c := by
  rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

theorem qShift_coeff (q : RealEulerNome) (c : RatFunc ℂ) :
    qShift q (algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ)) c)
      = algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ)) (GaloisForLFunctions.ratShift c) := by
  rw [← algebraMap_polyC_qShiftField, qShift_algebraMap, qShiftPolyMap_apply,
    Polynomial.map_C, Polynomial.C_comp, algebraMap_polyC_qShiftField]

theorem qShift_const (q : RealEulerNome) (t : ℂ) :
    qShift q (algebraMap ℂ (RatFunc (RatFunc ℂ)) t) = algebraMap ℂ (RatFunc (RatFunc ℂ)) t := by
  have hstep : algebraMap ℂ (RatFunc (RatFunc ℂ)) t
      = algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ)) (algebraMap ℂ (RatFunc ℂ) t) := by
    rw [← IsScalarTower.algebraMap_apply]
  rw [hstep, qShift_coeff, GaloisForLFunctions.ratShift_const]

/-! ## The scaled shift-periodicity brick -/

theorem leadingCoeff_comp_X_add_one (p : Polynomial ℂ) :
    (p.comp (Polynomial.X + Polynomial.C 1)).leadingCoeff = p.leadingCoeff := by
  rw [Polynomial.leadingCoeff_comp (by
    rw [Polynomial.natDegree_X_add_C]
    exact one_ne_zero)]
  rw [Polynomial.leadingCoeff_X_add_C, one_pow, mul_one]

/-- **The scaled shift brick, polynomial form.**  If `p(X+1)·q = c·p·q(X+1)` with `p, q ≠ 0`, then
`c = 1`: the unit shift does not change leading coefficients. -/
theorem shift_scaled_cross_const {p r : Polynomial ℂ} {c : ℂ} (hp : p ≠ 0) (hr : r ≠ 0)
    (h : p.comp (Polynomial.X + Polynomial.C 1) * r
      = Polynomial.C c * (p * r.comp (Polynomial.X + Polynomial.C 1))) : c = 1 := by
  have hpc : p.comp (Polynomial.X + Polynomial.C 1) ≠ 0 :=
    GaloisForLFunctions.comp_X_add_C_one_ne_zero hp
  have hrc : r.comp (Polynomial.X + Polynomial.C 1) ≠ 0 :=
    GaloisForLFunctions.comp_X_add_C_one_ne_zero hr
  have hlhs : (p.comp (Polynomial.X + Polynomial.C 1) * r).leadingCoeff
      = p.leadingCoeff * r.leadingCoeff := by
    rw [Polynomial.leadingCoeff_mul, leadingCoeff_comp_X_add_one]
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at h
    exact (mul_ne_zero hpc hr) h
  have hrhs : (Polynomial.C c * (p * r.comp (Polynomial.X + Polynomial.C 1))).leadingCoeff
      = c * (p.leadingCoeff * r.leadingCoeff) := by
    rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, Polynomial.leadingCoeff_mul,
      leadingCoeff_comp_X_add_one]
  have hcross : p.leadingCoeff * r.leadingCoeff = c * (p.leadingCoeff * r.leadingCoeff) := by
    calc p.leadingCoeff * r.leadingCoeff
        = (p.comp (Polynomial.X + Polynomial.C 1) * r).leadingCoeff := hlhs.symm
      _ = (Polynomial.C c * (p * r.comp (Polynomial.X + Polynomial.C 1))).leadingCoeff := by
          rw [h]
      _ = c * (p.leadingCoeff * r.leadingCoeff) := hrhs
  have hne : p.leadingCoeff * r.leadingCoeff ≠ 0 :=
    mul_ne_zero (Polynomial.leadingCoeff_ne_zero.mpr hp) (Polynomial.leadingCoeff_ne_zero.mpr hr)
  have h1 : c * (p.leadingCoeff * r.leadingCoeff) = 1 * (p.leadingCoeff * r.leadingCoeff) := by
    rw [one_mul]
    exact hcross.symm
  exact mul_right_cancel₀ hne h1

/-- **The scaled shift brick.**  A nonzero rational function whose unit shift is a constant
multiple of itself forces the constant to be one. -/
theorem ratShift_eq_const_mul_self {r : RatFunc ℂ} {c : ℂ} (hr : r ≠ 0)
    (h : GaloisForLFunctions.ratShift r = algebraMap ℂ (RatFunc ℂ) c * r) : c = 1 := by
  set p := r.num with hp_def
  set d := r.denom with hd_def
  have hd : d ≠ 0 := r.denom_ne_zero
  have hp : p ≠ 0 := by
    intro h0
    exact hr (by rw [← RatFunc.num_div_denom r, ← hp_def, h0, map_zero, zero_div])
  have hr' : algebraMap (Polynomial ℂ) (RatFunc ℂ) p
      / algebraMap (Polynomial ℂ) (RatFunc ℂ) d = r := RatFunc.num_div_denom r
  have hdK : algebraMap (Polynomial ℂ) (RatFunc ℂ) d ≠ 0 := fun h0 =>
    hd (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))
  have hdcK : algebraMap (Polynomial ℂ) (RatFunc ℂ) (d.comp (Polynomial.X + Polynomial.C 1)) ≠ 0 :=
    fun h0 => GaloisForLFunctions.comp_X_add_C_one_ne_zero hd
      (RatFunc.algebraMap_injective ℂ (by rw [h0, map_zero]))
  have hshift : algebraMap (Polynomial ℂ) (RatFunc ℂ) (p.comp (Polynomial.X + Polynomial.C 1))
      / algebraMap (Polynomial ℂ) (RatFunc ℂ) (d.comp (Polynomial.X + Polynomial.C 1))
      = algebraMap ℂ (RatFunc ℂ) c * r := by
    rw [← GaloisForLFunctions.ratShift_algebraMap, ← GaloisForLFunctions.ratShift_algebraMap,
      ← map_div₀, hr', h]
  have hcross : p.comp (Polynomial.X + Polynomial.C 1) * d
      = Polynomial.C c * (p * d.comp (Polynomial.X + Polynomial.C 1)) := by
    apply RatFunc.algebraMap_injective ℂ
    have h2 : algebraMap (Polynomial ℂ) (RatFunc ℂ) (p.comp (Polynomial.X + Polynomial.C 1))
          / algebraMap (Polynomial ℂ) (RatFunc ℂ) (d.comp (Polynomial.X + Polynomial.C 1))
        = algebraMap (Polynomial ℂ) (RatFunc ℂ) (Polynomial.C c)
          * (algebraMap (Polynomial ℂ) (RatFunc ℂ) p
            / algebraMap (Polynomial ℂ) (RatFunc ℂ) d) := by
      rw [GaloisForLFunctions.algebraMap_polyC, hshift, hr']
    field_simp at h2
    rw [map_mul, map_mul, map_mul]
    linear_combination h2
  exact shift_scaled_cross_const hp hd hcross

/-! ## The invariants of the q-shift -/

theorem qShiftPolyMap_coeff (q : RealEulerNome) (P : Polynomial (RatFunc ℂ)) (i : ℕ) :
    (qShiftPolyMap q P).coeff i
      = GaloisForLFunctions.ratShift (P.coeff i) * (qConst q) ^ i := by
  rw [qShiftPolyMap_apply, Polynomial.comp_C_mul_X_coeff, Polynomial.coeff_map]

theorem qShiftPolyMap_natDegree (q : RealEulerNome) (P : Polynomial (RatFunc ℂ)) :
    (qShiftPolyMap q P).natDegree = P.natDegree := by
  rcases eq_or_ne P 0 with rfl | hP
  · simp [qShiftPolyMap_apply]
  · have hmapdeg : (P.map GaloisForLFunctions.ratShift).natDegree = P.natDegree := by
      refine Polynomial.natDegree_map_of_leadingCoeff_ne_zero _ ?_
      intro h0
      exact (Polynomial.leadingCoeff_ne_zero.mpr hP)
        (GaloisForLFunctions.ratShift_injective (by rw [h0, map_zero]))
    rw [qShiftPolyMap_apply, Polynomial.natDegree_comp, hmapdeg,
      Polynomial.natDegree_C_mul_X _ (qConst_ne_zero q), mul_one]

theorem qConst_pow_eq (q : RealEulerNome) (k : ℕ) :
    (qConst q) ^ k = algebraMap ℂ (RatFunc ℂ) ((q.val : ℂ) ^ k) := by
  rw [qConst, ← map_pow]

theorem qpow_injective (q : RealEulerNome) : Function.Injective fun k : ℕ => q.val ^ k := by
  have hanti : StrictAnti fun k : ℕ => q.val ^ k := by
    intro m n hmn
    exact pow_lt_pow_right_of_lt_one₀ q.pos q.lt_one hmn
  exact hanti.injective

/-- **A q-shift eigenpolynomial is a monomial.**  Two nonzero coefficients would produce a
rational function whose unit shift is `q^{j−i}` times itself, forcing `i = j`. -/
theorem monomial_of_qShift_eigen (q : RealEulerNome) {P : Polynomial (RatFunc ℂ)}
    {c : RatFunc ℂ} (hP : P ≠ 0) (h : qShiftPolyMap q P = Polynomial.C c * P) :
    ∃ a : RatFunc ℂ, a ≠ 0 ∧ P = Polynomial.C a * Polynomial.X ^ P.natDegree := by
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at h
    exact qShiftPolyMap_ne_zero q hP h
  have hcoeff : ∀ i : ℕ,
      GaloisForLFunctions.ratShift (P.coeff i) * (qConst q) ^ i = c * P.coeff i := by
    intro i
    have hi := congrArg (fun p => Polynomial.coeff p i) h
    rw [qShiftPolyMap_coeff] at hi
    simpa using hi
  have hsingle : ∀ i j : ℕ, P.coeff i ≠ 0 → P.coeff j ≠ 0 → i = j := by
    intro i j hi hj
    have hqi : (qConst q) ^ i ≠ 0 := pow_ne_zero _ (qConst_ne_zero q)
    have hqj : (qConst q) ^ j ≠ 0 := pow_ne_zero _ (qConst_ne_zero q)
    set r : RatFunc ℂ := P.coeff i / P.coeff j with hr_def
    have hr0 : r ≠ 0 := div_ne_zero hi hj
    have hshift : GaloisForLFunctions.ratShift r
        = algebraMap ℂ (RatFunc ℂ) ((q.val : ℂ) ^ j / (q.val : ℂ) ^ i) * r := by
      have hi' := hcoeff i
      have hj' := hcoeff j
      have hqpow : algebraMap ℂ (RatFunc ℂ) ((q.val : ℂ) ^ j / (q.val : ℂ) ^ i)
          = (qConst q) ^ j / (qConst q) ^ i := by
        rw [map_div₀, ← qConst_pow_eq, ← qConst_pow_eq]
      have hrsi : GaloisForLFunctions.ratShift (P.coeff i)
          = c * P.coeff i / (qConst q) ^ i := by
        rw [eq_div_iff hqi]
        exact hi'
      have hrsj : GaloisForLFunctions.ratShift (P.coeff j)
          = c * P.coeff j / (qConst q) ^ j := by
        rw [eq_div_iff hqj]
        exact hj'
      rw [hr_def, map_div₀, hrsi, hrsj, hqpow]
      field_simp
    have hone := ratShift_eq_const_mul_self hr0 hshift
    have hqpos : (0 : ℝ) < q.val := q.pos
    have habs : ‖((q.val : ℂ) ^ j / (q.val : ℂ) ^ i)‖ = q.val ^ j / q.val ^ i := by
      rw [norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqpos]
    rw [hone, norm_one] at habs
    have hipos : (0 : ℝ) < q.val ^ i := pow_pos hqpos i
    have hij : q.val ^ j = q.val ^ i := by
      field_simp at habs
      linarith [habs]
    exact (qpow_injective q hij).symm
  refine ⟨P.coeff P.natDegree, Polynomial.leadingCoeff_ne_zero.mpr hP, ?_⟩
  ext i
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  by_cases hid : i = P.natDegree
  · rw [hid, if_pos rfl, mul_one]
  · rw [if_neg hid, mul_zero]
    by_contra hne0
    exact hid (hsingle i P.natDegree hne0 (Polynomial.leadingCoeff_ne_zero.mpr hP))

/-- A `q`-shift eigenrelation for a nonzero polynomial, extracted from the coprime factorisation. -/
theorem exists_qShift_eigen_const (q : RealEulerNome) {P : Polynomial (RatFunc ℂ)}
    (hP : P ≠ 0) (hdvd : P ∣ qShiftPolyMap q P) :
    ∃ c : RatFunc ℂ, qShiftPolyMap q P = Polynomial.C c * P := by
  obtain ⟨t, ht⟩ := hdvd
  have hσP : qShiftPolyMap q P ≠ 0 := qShiftPolyMap_ne_zero q hP
  have ht0 : t ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at ht
    exact hσP ht
  have hdeg : (qShiftPolyMap q P).natDegree = P.natDegree := qShiftPolyMap_natDegree q P
  have hdegt : t.natDegree = 0 := by
    rw [ht, Polynomial.natDegree_mul hP ht0] at hdeg
    omega
  obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hdegt
  exact ⟨c, by rw [ht, ← hc, mul_comm]⟩

/-- **The invariants of the q-shift are the constants.**  A rational function of `z` and `u` fixed
by `z ↦ z+1`, `u ↦ q·u` lies in `ℂ`. -/
theorem qShift_fixed_eq_const (q : RealEulerNome) {f : RatFunc (RatFunc ℂ)}
    (h : qShift q f = f) : ∃ t : ℂ, f = algebraMap ℂ (RatFunc (RatFunc ℂ)) t := by
  rcases eq_or_ne f 0 with rfl | hf0
  · exact ⟨0, by rw [map_zero]⟩
  set P := f.num with hP_def
  set Q := f.denom with hQ_def
  have hQ : Q ≠ 0 := f.denom_ne_zero
  have hco : IsCoprime P Q := f.isCoprime_num_denom
  have hfrac : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) P
      / algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) Q = f := RatFunc.num_div_denom f
  have hP : P ≠ 0 := by
    intro h0
    apply hf0
    rw [← hfrac, h0, map_zero, zero_div]
  have hQK : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) Q ≠ 0 := fun h0 =>
    hQ (RatFunc.algebraMap_injective (RatFunc ℂ) (by rw [h0, map_zero]))
  have hσQ : qShiftPolyMap q Q ≠ 0 := qShiftPolyMap_ne_zero q hQ
  have hσQK : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (qShiftPolyMap q Q) ≠ 0 :=
    fun h0 => hσQ (RatFunc.algebraMap_injective (RatFunc ℂ) (by rw [h0, map_zero]))
  -- cross multiplication of the invariance
  have hcross : qShiftPolyMap q P * Q = P * qShiftPolyMap q Q := by
    apply RatFunc.algebraMap_injective (RatFunc ℂ)
    have hshift : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (qShiftPolyMap q P)
        / algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (qShiftPolyMap q Q) = f := by
      rw [← qShift_algebraMap, ← qShift_algebraMap, ← map_div₀, hfrac, h]
    have h2 := hshift.trans hfrac.symm
    rw [div_eq_div_iff hσQK hQK] at h2
    rw [map_mul, map_mul]
    linear_combination h2
  -- eigenrelations
  obtain ⟨c, hcP⟩ := exists_qShift_eigen_const q hP
    (hco.dvd_of_dvd_mul_right ⟨qShiftPolyMap q Q, hcross⟩)
  obtain ⟨c', hcQ⟩ := exists_qShift_eigen_const q hQ
    (hco.symm.dvd_of_dvd_mul_right ⟨qShiftPolyMap q P, by linear_combination -hcross⟩)
  have hcc' : c = c' := by
    have hPQ : Polynomial.C c * P * Q = P * (Polynomial.C c' * Q) := by
      rw [← hcP, ← hcQ, hcross]
    have hne : P * Q ≠ 0 := mul_ne_zero hP hQ
    have hCC : (Polynomial.C c - Polynomial.C c') * (P * Q) = 0 := by
      linear_combination hPQ
    rcases mul_eq_zero.mp hCC with hz | hz
    · have := sub_eq_zero.mp hz
      exact Polynomial.C_injective this
    · exact absurd hz hne
  -- monomial shapes
  obtain ⟨a, ha0, haP⟩ := monomial_of_qShift_eigen q hP hcP
  obtain ⟨b, hb0, hbQ⟩ := monomial_of_qShift_eigen q hQ hcQ
  set d := P.natDegree with hd_def
  set e := Q.natDegree with he_def
  -- coprimality forbids a common factor of `X`
  have hmin : d = 0 ∨ e = 0 := by
    by_contra hcon
    have hd0 : d ≠ 0 := fun hh => hcon (Or.inl hh)
    have he0 : e ≠ 0 := fun hh => hcon (Or.inr hh)
    have hXP : (Polynomial.X : Polynomial (RatFunc ℂ)) ∣ P := by
      rw [haP]
      exact Dvd.dvd.mul_left (dvd_pow_self _ hd0) _
    have hXQ : (Polynomial.X : Polynomial (RatFunc ℂ)) ∣ Q := by
      rw [hbQ]
      exact Dvd.dvd.mul_left (dvd_pow_self _ he0) _
    exact Polynomial.not_isUnit_X (hco.isUnit_of_dvd' hXP hXQ)
  -- the leading coefficients
  have hcoeffP : GaloisForLFunctions.ratShift a * (qConst q) ^ d = c * a := by
    have hi := congrArg (fun p => Polynomial.coeff p d) hcP
    rw [qShiftPolyMap_coeff] at hi
    have hPa : P.coeff d = a := by
      rw [haP, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    simpa [hPa] using hi
  have hcoeffQ : GaloisForLFunctions.ratShift b * (qConst q) ^ e = c * b := by
    have hi := congrArg (fun p => Polynomial.coeff p e) hcQ
    rw [qShiftPolyMap_coeff] at hi
    have hQb : Q.coeff e = b := by
      rw [hbQ, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one]
    rw [← hcc'] at hi
    simpa [hQb] using hi
  have hc0 : c ≠ 0 := by
    intro h0
    rw [h0, map_zero, zero_mul] at hcP
    exact qShiftPolyMap_ne_zero q hP hcP
  -- the two degrees agree
  have hde : d = e := by
    set r : RatFunc ℂ := a / b with hr_def
    have hr0 : r ≠ 0 := div_ne_zero ha0 hb0
    have hqd : (qConst q) ^ d ≠ 0 := pow_ne_zero _ (qConst_ne_zero q)
    have hqe : (qConst q) ^ e ≠ 0 := pow_ne_zero _ (qConst_ne_zero q)
    have hshift : GaloisForLFunctions.ratShift r
        = algebraMap ℂ (RatFunc ℂ) ((q.val : ℂ) ^ e / (q.val : ℂ) ^ d) * r := by
      have hrsa : GaloisForLFunctions.ratShift a = c * a / (qConst q) ^ d := by
        rw [eq_div_iff hqd]
        exact hcoeffP
      have hrsb : GaloisForLFunctions.ratShift b = c * b / (qConst q) ^ e := by
        rw [eq_div_iff hqe]
        exact hcoeffQ
      have hqpow : algebraMap ℂ (RatFunc ℂ) ((q.val : ℂ) ^ e / (q.val : ℂ) ^ d)
          = (qConst q) ^ e / (qConst q) ^ d := by
        rw [map_div₀, ← qConst_pow_eq, ← qConst_pow_eq]
      rw [hr_def, map_div₀, hrsa, hrsb, hqpow]
      field_simp
    have hone := ratShift_eq_const_mul_self hr0 hshift
    have hqpos : (0 : ℝ) < q.val := q.pos
    have habs : ‖((q.val : ℂ) ^ e / (q.val : ℂ) ^ d)‖ = q.val ^ e / q.val ^ d := by
      rw [norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqpos]
    rw [hone, norm_one] at habs
    have hdpos : (0 : ℝ) < q.val ^ d := pow_pos hqpos d
    have hqq : q.val ^ e = q.val ^ d := by
      field_simp at habs
      linarith [habs]
    exact (qpow_injective q hqq).symm
  have hd0 : d = 0 := by
    rcases hmin with h1 | h1
    · exact h1
    · rw [hde]; exact h1
  have he0 : e = 0 := by rw [← hde]; exact hd0
  -- both numerator and denominator are constants
  have hPa : P = Polynomial.C a := by rw [haP, hd0, pow_zero, mul_one]
  have hQb : Q = Polynomial.C b := by rw [hbQ, he0, pow_zero, mul_one]
  -- the constant is shift invariant
  have hratio : GaloisForLFunctions.ratShift (a / b) = a / b := by
    have hrsa : GaloisForLFunctions.ratShift a = c * a := by
      have := hcoeffP
      rw [hd0, pow_zero, mul_one] at this
      exact this
    have hrsb : GaloisForLFunctions.ratShift b = c * b := by
      have := hcoeffQ
      rw [he0, pow_zero, mul_one] at this
      exact this
    rw [map_div₀, hrsa, hrsb]
    field_simp
  obtain ⟨t, ht⟩ := GaloisForLFunctions.ratShift_fixed_eq_const hratio
  refine ⟨t, ?_⟩
  have hfval : f = algebraMap (RatFunc ℂ) (RatFunc (RatFunc ℂ)) (a / b) := by
    rw [← hfrac, hPa, hQb, algebraMap_polyC_qShiftField,
      algebraMap_polyC_qShiftField, ← map_div₀]
  rw [hfval, ht, ← IsScalarTower.algebraMap_apply]

/-! ## Evaluation at complex points and the coboundary obstruction -/

/-- Evaluation of a polynomial over `ℂ(z)` at a complex constant. -/
def evalConst (P : Polynomial (RatFunc ℂ)) (c : ℂ) : RatFunc ℂ :=
  P.eval (algebraMap ℂ (RatFunc ℂ) c)

@[simp] theorem evalConst_mul (P R : Polynomial (RatFunc ℂ)) (c : ℂ) :
    evalConst (P * R) c = evalConst P c * evalConst R c := by
  rw [evalConst, evalConst, evalConst, Polynomial.eval_mul]

@[simp] theorem evalConst_sub (P R : Polynomial (RatFunc ℂ)) (c : ℂ) :
    evalConst (P - R) c = evalConst P c - evalConst R c := by
  rw [evalConst, evalConst, evalConst, Polynomial.eval_sub]

/-- **The q-shift moves evaluation points by `q`.** -/
theorem evalConst_qShiftPolyMap (q : RealEulerNome) (P : Polynomial (RatFunc ℂ)) (c : ℂ) :
    evalConst (qShiftPolyMap q P) c
      = GaloisForLFunctions.ratShift (evalConst P ((q.val : ℂ) * c)) := by
  rw [evalConst, evalConst, qShiftPolyMap_apply, Polynomial.eval_comp]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  rw [Polynomial.eval_map]
  have hpt : qConst q * algebraMap ℂ (RatFunc ℂ) c
      = GaloisForLFunctions.ratShift (algebraMap ℂ (RatFunc ℂ) ((q.val : ℂ) * c)) := by
    rw [GaloisForLFunctions.ratShift_const, qConst, ← map_mul]
  rw [hpt, Polynomial.eval₂_at_apply]

theorem evalConst_qShiftPolyMap_eq_zero_iff (q : RealEulerNome) (P : Polynomial (RatFunc ℂ))
    (c : ℂ) : evalConst (qShiftPolyMap q P) c = 0 ↔ evalConst P ((q.val : ℂ) * c) = 0 := by
  rw [evalConst_qShiftPolyMap]
  constructor
  · intro h0
    exact GaloisForLFunctions.ratShift_injective (by rw [h0, map_zero])
  · intro h0
    rw [h0, map_zero]

/-- Coprime polynomials cannot both vanish at a point. -/
theorem not_both_evalConst_zero {P R : Polynomial (RatFunc ℂ)} (hco : IsCoprime P R) (c : ℂ)
    (hP : evalConst P c = 0) (hR : evalConst R c = 0) : False := by
  obtain ⟨A, B, hAB⟩ := hco
  have hev := congrArg (fun p => evalConst p c) hAB
  simp only [evalConst, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one] at hev
  rw [show Polynomial.eval (algebraMap ℂ (RatFunc ℂ) c) P = 0 from hP,
    show Polynomial.eval (algebraMap ℂ (RatFunc ℂ) c) R = 0 from hR, mul_zero, mul_zero,
    add_zero] at hev
  exact zero_ne_one hev

theorem finite_evalConst_zero {R : Polynomial (RatFunc ℂ)} (hR : R ≠ 0) :
    {c : ℂ | evalConst R c = 0}.Finite := by
  have hroot : {x : RatFunc ℂ | R.IsRoot x}.Finite := by
    rw [← Set.not_infinite]
    intro hinf
    exact hR (Polynomial.eq_zero_of_infinite_isRoot R hinf)
  have hinj : Set.InjOn (algebraMap ℂ (RatFunc ℂ))
      ((algebraMap ℂ (RatFunc ℂ)) ⁻¹' {x : RatFunc ℂ | R.IsRoot x}) :=
    fun a _ b _ hab => (algebraMap ℂ (RatFunc ℂ)).injective hab
  exact hroot.preimage hinj

/-- **The coboundary obstruction.**  No element of `ℂ(z,u)` has `σw − w` equal to a rational
function whose only complex pole is `u = 1`: the largest and the smallest nonzero modulus among
the poles of `w` would have to be `q` and `1` at the same time. -/
theorem qShift_sub_self_ne (q : RealEulerNome) (w D : RatFunc (RatFunc ℂ))
    (hDpole : evalConst D.denom 1 = 0)
    (hDonly : ∀ c : ℂ, evalConst D.denom c = 0 → c = 1) :
    qShift q w - w ≠ D := by
  classical
  intro hEq
  set P := w.num with hP_def
  set R := w.denom with hR_def
  set A := D.num with hA_def
  set B := D.denom with hB_def
  have hR : R ≠ 0 := w.denom_ne_zero
  have hB : B ≠ 0 := D.denom_ne_zero
  have hco : IsCoprime P R := w.isCoprime_num_denom
  have hcoD : IsCoprime A B := D.isCoprime_num_denom
  have hσR : qShiftPolyMap q R ≠ 0 := qShiftPolyMap_ne_zero q hR
  have hcoσ : IsCoprime (qShiftPolyMap q P) (qShiftPolyMap q R) := hco.map (qShiftPolyMap q)
  have hqpos : (0 : ℝ) < q.val := q.pos
  have hqne : ((q.val : ℂ)) ≠ 0 := q.complex_ne_zero
  have hqnorm : ‖((q.val : ℂ))‖ = q.val := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hqpos]
  -- the cleared identity
  have hclear : qShiftPolyMap q P * R * B - P * (qShiftPolyMap q R * B)
      = A * (qShiftPolyMap q R * R) := by
    apply RatFunc.algebraMap_injective (RatFunc ℂ)
    have hRK : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) R ≠ 0 := fun h0 =>
      hR (RatFunc.algebraMap_injective (RatFunc ℂ) (by rw [h0, map_zero]))
    have hBK : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) B ≠ 0 := fun h0 =>
      hB (RatFunc.algebraMap_injective (RatFunc ℂ) (by rw [h0, map_zero]))
    have hσRK : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ))
        (qShiftPolyMap q R) ≠ 0 := fun h0 =>
      hσR (RatFunc.algebraMap_injective (RatFunc ℂ) (by rw [h0, map_zero]))
    have hw : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) P
        / algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) R = w :=
      RatFunc.num_div_denom w
    have hDfrac : algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) A
        / algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) B = D :=
      RatFunc.num_div_denom D
    have hσw : qShift q w
        = algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (qShiftPolyMap q P)
          / algebraMap (Polynomial (RatFunc ℂ)) (RatFunc (RatFunc ℂ)) (qShiftPolyMap q R) := by
      rw [← hw, map_div₀, qShift_algebraMap, qShift_algebraMap]
    rw [hσw, ← hw, ← hDfrac] at hEq
    rw [div_sub_div _ _ hσRK hRK, div_eq_div_iff (mul_ne_zero hσRK hRK) hBK] at hEq
    simp only [map_sub, map_mul]
    linear_combination hEq
  have hkey : ∀ c : ℂ,
      evalConst (qShiftPolyMap q P) c * evalConst R c * evalConst B c
        - evalConst P c * (evalConst (qShiftPolyMap q R) c * evalConst B c)
        = evalConst A c * (evalConst (qShiftPolyMap q R) c * evalConst R c) := by
    intro c
    have hev := congrArg (fun p => evalConst p c) hclear
    simpa using hev
  have hA1 : evalConst A 1 ≠ 0 := fun h0 => not_both_evalConst_zero hcoD 1 h0 hDpole
  by_cases hcase : evalConst R 1 = 0 ∨ evalConst R ((q.val : ℂ)) = 0
  · -- `w` has a pole at `1` or at `q`; compare the extreme moduli of its pole set
    have hfin : {c : ℂ | evalConst R c = 0}.Finite := finite_evalConst_zero hR
    set S := hfin.toFinset with hS_def
    have hmemS : ∀ c : ℂ, c ∈ S ↔ evalConst R c = 0 := by
      intro c
      rw [hS_def, Set.Finite.mem_toFinset]
      exact Iff.rfl
    have hS0ne : (S.erase 0).Nonempty := by
      rcases hcase with h | h
      · exact ⟨1, Finset.mem_erase.mpr ⟨one_ne_zero, (hmemS 1).mpr h⟩⟩
      · exact ⟨(q.val : ℂ), Finset.mem_erase.mpr ⟨hqne, (hmemS _).mpr h⟩⟩
    obtain ⟨e, heS0⟩ := hS0ne
    have hSne : S.Nonempty := ⟨e, Finset.mem_of_mem_erase heS0⟩
    obtain ⟨b, hbS, hbmax⟩ := S.exists_max_image (fun c => ‖c‖) hSne
    obtain ⟨a, haS0, hamin⟩ := (S.erase 0).exists_min_image (fun c => ‖c‖) ⟨e, heS0⟩
    have hbR : evalConst R b = 0 := (hmemS b).mp hbS
    have haR : evalConst R a = 0 := (hmemS a).mp (Finset.mem_of_mem_erase haS0)
    have hane : a ≠ 0 := (Finset.mem_erase.mp haS0).1
    have hbne : b ≠ 0 := by
      intro h0
      have hle := hbmax e (Finset.mem_of_mem_erase heS0)
      rw [h0, norm_zero] at hle
      exact (Finset.mem_erase.mp heS0).1 (norm_eq_zero.mp (le_antisymm hle (norm_nonneg e)))
    -- the largest pole is `q`
    have hbq : b = (q.val : ℂ) := by
      set c : ℂ := b / (q.val : ℂ) with hc_def
      have hbc : (q.val : ℂ) * c = b := by
        rw [hc_def]
        field_simp
      have hcnorm : ‖b‖ < ‖c‖ := by
        have hbpos : 0 < ‖b‖ := norm_pos_iff.mpr hbne
        rw [hc_def, norm_div, hqnorm]
        rw [lt_div_iff₀ hqpos]
        nlinarith [q.lt_one, hbpos]
      have hcR : evalConst R c ≠ 0 := by
        intro h0
        exact absurd (hbmax c ((hmemS c).mpr h0)) (by simpa using hcnorm)
      have hσRc : evalConst (qShiftPolyMap q R) c = 0 := by
        rw [evalConst_qShiftPolyMap_eq_zero_iff, hbc]
        exact hbR
      have hσPc : evalConst (qShiftPolyMap q P) c ≠ 0 := fun h0 =>
        not_both_evalConst_zero hcoσ c h0 hσRc
      have hk := hkey c
      rw [hσRc] at hk
      have hk0 : evalConst (qShiftPolyMap q P) c * evalConst R c * evalConst B c = 0 := by
        linear_combination hk
      have hBc : evalConst B c = 0 := by
        rcases mul_eq_zero.mp hk0 with h | h
        · rcases mul_eq_zero.mp h with h' | h'
          · exact absurd h' hσPc
          · exact absurd h' hcR
        · exact h
      have hc1 : c = 1 := hDonly c hBc
      rw [← hbc, hc1, mul_one]
    -- the smallest nonzero pole is `1`
    have ha1 : a = 1 := by
      have hqaS : evalConst R ((q.val : ℂ) * a) ≠ 0 := by
        intro h0
        have hqane : ((q.val : ℂ)) * a ≠ 0 := mul_ne_zero hqne hane
        have hmem : ((q.val : ℂ)) * a ∈ S.erase 0 :=
          Finset.mem_erase.mpr ⟨hqane, (hmemS _).mpr h0⟩
        have hle := hamin _ hmem
        have hlt : ‖((q.val : ℂ)) * a‖ < ‖a‖ := by
          rw [norm_mul, hqnorm]
          have hapos : 0 < ‖a‖ := norm_pos_iff.mpr hane
          nlinarith [q.lt_one, hapos]
        exact absurd hle (by simpa using hlt)
      have hσRa : evalConst (qShiftPolyMap q R) a ≠ 0 := by
        intro h0
        rw [evalConst_qShiftPolyMap_eq_zero_iff] at h0
        exact hqaS h0
      have hPa : evalConst P a ≠ 0 := fun h0 => not_both_evalConst_zero hco a h0 haR
      have hk := hkey a
      rw [haR] at hk
      have hBa : evalConst B a = 0 := by
        have hzero : evalConst P a * (evalConst (qShiftPolyMap q R) a * evalConst B a) = 0 := by
          linear_combination -hk
        rcases mul_eq_zero.mp hzero with h | h
        · exact absurd h hPa
        · rcases mul_eq_zero.mp h with h' | h'
          · exact absurd h' hσRa
          · exact h'
      exact hDonly a hBa
    -- the two extremes contradict each other
    have h1S : (1 : ℂ) ∈ S := by
      rw [← ha1]
      exact Finset.mem_of_mem_erase haS0
    have hle := hbmax 1 h1S
    rw [hbq] at hle
    simp only [norm_one, hqnorm] at hle
    exact absurd hle (by simpa using q.lt_one)
  · -- `w` is regular at `1` and at `q`: evaluate the identity at `1`
    have h1 : evalConst R 1 ≠ 0 := fun h => hcase (Or.inl h)
    have hq1 : evalConst R ((q.val : ℂ)) ≠ 0 := fun h => hcase (Or.inr h)
    have hσR1 : evalConst (qShiftPolyMap q R) 1 ≠ 0 := by
      intro h0
      rw [evalConst_qShiftPolyMap_eq_zero_iff, mul_one] at h0
      exact hq1 h0
    have hk := hkey 1
    rw [hDpole] at hk
    have hz : evalConst A 1 * (evalConst (qShiftPolyMap q R) 1 * evalConst R 1) = 0 := by
      linear_combination -hk
    exact (mul_ne_zero hA1 (mul_ne_zero hσR1 h1)) hz

end

end GaloisForLFunctions.HTGeometry
