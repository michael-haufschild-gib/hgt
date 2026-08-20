import GaloisForLFunctions.HTGeometry.RatFuncShiftDegreeCalculus

/-!
# The unit shift on rational functions over an arbitrary base field

The shift `X ↦ X + 1` and its degree calculus, developed over any field of characteristic zero:
the finite difference of a polynomial drops the degree by exactly one with leading coefficient
multiplied by the degree, and the shift difference of a rational function drops the degree at
infinity by exactly one — by at least two when the degree is zero and the function is not
shift invariant.

These are the statements the parameterised Galois theory of the Bessel order recurrence needs over a
base whose constants carry a nontrivial derivation, where the complex-coefficient versions do not
apply.
-/

namespace GaloisForLFunctions.HTGeometry.FieldShift

open Polynomial nonZeroDivisors

noncomputable section

variable {F : Type*} [Field F] [CharZero F]

theorem comp_X_add_one_eq_self {p : Polynomial F}
    (h : p.comp (X + C 1) = p) : p = C (p.eval 0) := by
  have hval : ∀ n : ℕ, p.eval (n : F) = p.eval 0 := by
    intro n
    induction n with
    | zero => norm_num
    | succ k ih =>
      have hk := congrArg (Polynomial.eval (k : F)) h
      simp only [eval_comp, eval_add, eval_X, eval_C] at hk
      push_cast
      rw [hk]
      exact ih
  have hsub : p - C (p.eval 0) = 0 := by
    apply Polynomial.eq_zero_of_infinite_isRoot
    apply Set.infinite_of_injective_forall_mem
      (f := fun n : ℕ => (n : F)) Nat.cast_injective
    intro n
    simp only [Set.mem_setOf_eq, IsRoot, eval_sub, eval_C, hval n, sub_self]
  exact eq_of_sub_eq_zero hsub

/-- **Shift-periodic rational functions are constant**: if `p(X+1)·q = p·q(X+1)` with
`p, q` coprime, both polynomials are constant. -/
theorem shift_periodic_quotient_constant {p q : Polynomial F}
    (hco : IsCoprime p q) (h : p.comp (X + C 1) * q = p * q.comp (X + C 1)) :
    ∃ a b : F, p = C a ∧ q = C b := by
  rcases eq_or_ne p 0 with rfl | hp
  · obtain ⟨c, _, hcq⟩ := Polynomial.isUnit_iff.mp (isCoprime_zero_left.mp hco)
    exact ⟨0, c, by simp, hcq.symm⟩
  · have hdvd0 : p ∣ p.comp (X + C 1) * q := ⟨q.comp (X + C 1), h⟩
    have hdvd : p ∣ p.comp (X + C 1) := hco.dvd_of_dvd_mul_right hdvd0
    obtain ⟨t, ht⟩ := hdvd
    have hcompne : p.comp (X + C 1) ≠ 0 := by
      intro h0
      exact hp ((Polynomial.comp_eq_zero_iff.mp h0).resolve_right
        (fun hh => by simpa using hh.2))
    have htne : t ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at ht
      exact hcompne ht
    have hdegX : (X + C (1 : F)).natDegree = 1 := by
      simpa using Polynomial.natDegree_X_add_C (1 : F)
    have hdegcomp : (p.comp (X + C 1)).natDegree = p.natDegree := by
      rw [Polynomial.natDegree_comp, hdegX, mul_one]
    have hdegt : t.natDegree = 0 := by
      have := hdegcomp
      rw [ht, Polynomial.natDegree_mul hp htne] at this
      omega
    obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hdegt
    have hlead : (p.comp (X + C 1)).leadingCoeff = p.leadingCoeff := by
      rw [Polynomial.leadingCoeff_comp (by rw [hdegX]; norm_num),
        Polynomial.leadingCoeff_X_add_C, one_pow, mul_one]
    have hc1 : c = 1 := by
      have h2 : p.leadingCoeff * c = p.leadingCoeff := by
        have h3 := hlead
        rw [ht, ← hc, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C] at h3
        exact h3
      have hlp : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
      exact mul_left_cancel₀ hlp (h2.trans (mul_one p.leadingCoeff).symm)
    have hshift : p.comp (X + C 1) = p := by
      rw [ht, ← hc, hc1]
      simp
    have hpconst := comp_X_add_one_eq_self hshift
    -- transfer to q
    have hq' : C (p.eval 0) * q = C (p.eval 0) * q.comp (X + C 1) := by
      have := h
      rw [hshift, hpconst] at this
      linear_combination this
    have hp0 : (C (p.eval 0) : Polynomial F) ≠ 0 := by
      rw [← hpconst]
      exact hp
    have hqshift : q.comp (X + C 1) = q := (mul_left_cancel₀ hp0 hq').symm
    exact ⟨p.eval 0, q.eval 0, hpconst, comp_X_add_one_eq_self hqshift⟩


omit [CharZero F] in
theorem comp_X_add_C_one_ne_zero {p : Polynomial F} (hp : p ≠ 0) :
    p.comp (X + C 1) ≠ 0 := by
  intro h0
  exact hp ((Polynomial.comp_eq_zero_iff.mp h0).resolve_right
    (fun hh => by simpa using hh.2))

/-- The unit shift `p(X) ↦ p(X+1)` on polynomials, valued in the rational-function field. -/
def shiftCompHom : Polynomial F →+* RatFunc F :=
  (algebraMap (Polynomial F) (RatFunc F)).comp
    (Polynomial.eval₂RingHom Polynomial.C (X + C 1))

omit [CharZero F] in
theorem shiftCompHom_apply (p : Polynomial F) :
    shiftCompHom p = algebraMap (Polynomial F) (RatFunc F) (p.comp (X + C 1)) := rfl

omit [CharZero F] in
theorem shiftCompHom_mem_nonZeroDivisors :
    (Polynomial F)⁰ ≤ (RatFunc F)⁰.comap shiftCompHom := by
  intro p hp
  rw [Submonoid.mem_comap, mem_nonZeroDivisors_iff_ne_zero]
  rw [mem_nonZeroDivisors_iff_ne_zero] at hp
  rw [shiftCompHom_apply]
  intro h0
  exact comp_X_add_C_one_ne_zero hp
    (RatFunc.algebraMap_injective F (by rw [h0, map_zero]))

/-- The unit-shift endomorphism `r(X) ↦ r(X+1)` of the rational-function field. -/
def ratShift : RatFunc F →+* RatFunc F :=
  RatFunc.liftRingHom shiftCompHom shiftCompHom_mem_nonZeroDivisors

omit [CharZero F] in
theorem ratShift_algebraMap (p : Polynomial F) :
    ratShift (algebraMap (Polynomial F) (RatFunc F) p)
      = algebraMap (Polynomial F) (RatFunc F) (p.comp (X + C 1)) := by
  have h := RatFunc.liftRingHom_apply_div shiftCompHom
    shiftCompHom_mem_nonZeroDivisors p 1
  simp only [map_one, div_one] at h
  exact h

omit [CharZero F] in
theorem algebraMap_polyC (c : F) :
    algebraMap (Polynomial F) (RatFunc F) (Polynomial.C c)
      = algebraMap F (RatFunc F) c := by
  rw [← Polynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]

omit [CharZero F] in
theorem ratShift_injective : Function.Injective (ratShift : RatFunc F →+* RatFunc F) :=
  ratShift.injective

omit [CharZero F] in
theorem ratShift_const (t : F) :
    ratShift (algebraMap F (RatFunc F) t) = algebraMap F (RatFunc F) t := by
  rw [IsScalarTower.algebraMap_apply F (Polynomial F) (RatFunc F) t,
    Polynomial.algebraMap_eq, ratShift_algebraMap, Polynomial.C_comp]

/-- **Shift-invariant rational functions are constant.**  The rational-function form of the
shift-periodic quotient brick: `r(X+1) = r(X)` in `F(X)` forces `r ∈ F`. -/
theorem ratShift_fixed_eq_const {r : RatFunc F} (h : ratShift r = r) :
    ∃ t : F, r = algebraMap F (RatFunc F) t := by
  set p := r.num with hp_def
  set q := r.denom with hq_def
  have hq : q ≠ 0 := r.denom_ne_zero
  have hco : IsCoprime p q := r.isCoprime_num_denom
  have hr : algebraMap (Polynomial F) (RatFunc F) p
      / algebraMap (Polynomial F) (RatFunc F) q = r := RatFunc.num_div_denom r
  have hqK : algebraMap (Polynomial F) (RatFunc F) q ≠ 0 := fun h0 =>
    hq (RatFunc.algebraMap_injective F (by rw [h0, map_zero]))
  have hqcK : algebraMap (Polynomial F) (RatFunc F) (q.comp (X + C 1)) ≠ 0 := fun h0 =>
    comp_X_add_C_one_ne_zero hq (RatFunc.algebraMap_injective F (by rw [h0, map_zero]))
  have hshift : algebraMap (Polynomial F) (RatFunc F) (p.comp (X + C 1))
      / algebraMap (Polynomial F) (RatFunc F) (q.comp (X + C 1)) = r := by
    rw [← ratShift_algebraMap, ← ratShift_algebraMap, ← map_div₀, hr, h]
  have hcross : p.comp (X + C 1) * q = p * q.comp (X + C 1) := by
    apply RatFunc.algebraMap_injective F
    have h2 : algebraMap (Polynomial F) (RatFunc F) (p.comp (X + C 1))
          / algebraMap (Polynomial F) (RatFunc F) (q.comp (X + C 1))
        = algebraMap (Polynomial F) (RatFunc F) p
          / algebraMap (Polynomial F) (RatFunc F) q := by
      rw [hshift, hr]
    rw [div_eq_div_iff hqcK hqK] at h2
    rw [map_mul, map_mul]
    linear_combination h2
  obtain ⟨a, b, hpa, hqb⟩ := shift_periodic_quotient_constant hco hcross
  have hb : b ≠ 0 := fun h0 => hq (by rw [hqb, h0, map_zero])
  refine ⟨a / b, ?_⟩
  rw [← hr, hpa, hqb, algebraMap_polyC, algebraMap_polyC, ← map_div₀]

omit [CharZero F] in
/-- Shifting a polynomial preserves its degree. -/
theorem natDegree_comp_X_add_one (p : F[X]) :
    (p.comp (X + C 1)).natDegree = p.natDegree := by
  have hdeg : (X + C (1 : F)).natDegree = 1 := by
    simpa using Polynomial.natDegree_X_add_C (1 : F)
  rw [Polynomial.natDegree_comp, hdeg, mul_one]

omit [CharZero F] in
/-- Shifting a polynomial preserves its leading coefficient. -/
theorem leadingCoeff_comp_X_add_one' (p : F[X]) :
    (p.comp (X + C 1)).leadingCoeff = p.leadingCoeff := by
  have hdeg : (X + C (1 : F)).natDegree = 1 := by
    simpa using Polynomial.natDegree_X_add_C (1 : F)
  rw [Polynomial.leadingCoeff_comp (by rw [hdeg]; norm_num),
    Polynomial.leadingCoeff_X_add_C, one_pow, mul_one]

/-! ### The finite difference of a polynomial -/

/-- The unit finite difference `p(X+1) - p(X)`. -/
def shiftDelta (p : F[X]) : F[X] := p.comp (X + C 1) - p

omit [CharZero F] in
theorem degree_shiftDelta_lt {p : F[X]} (hp : p ≠ 0) : (shiftDelta p).degree < p.degree := by
  have hne : p.comp (X + C 1) ≠ 0 := comp_X_add_C_one_ne_zero hp
  have hdeg : (p.comp (X + C 1)).degree = p.degree := by
    rw [degree_eq_natDegree hne, degree_eq_natDegree hp, natDegree_comp_X_add_one]
  have h := degree_sub_lt hdeg hne (leadingCoeff_comp_X_add_one' p)
  rwa [hdeg] at h

omit [CharZero F] in
theorem shiftDelta_eq_zero_of_natDegree_zero {p : F[X]} (h : p.natDegree = 0) :
    shiftDelta p = 0 := by
  obtain ⟨c, rfl⟩ := Polynomial.natDegree_eq_zero.mp h
  simp [shiftDelta]

theorem coeff_shiftDelta_pred {p : F[X]} (hd : 1 ≤ p.natDegree) :
    (shiftDelta p).coeff (p.natDegree - 1) = (p.natDegree : F) * p.leadingCoeff := by
  have hnd : (hasseDeriv (p.natDegree - 1) p).natDegree = p.natDegree - (p.natDegree - 1) :=
    natDegree_hasseDeriv p _
  have hlt : (hasseDeriv (p.natDegree - 1) p).natDegree < 2 := by omega
  have h1 : (p.comp (X + C 1)).coeff (p.natDegree - 1)
      = eval 1 (hasseDeriv (p.natDegree - 1) p) := by
    rw [← taylor_apply, taylor_coeff]
  have h2 : eval (1 : F) (hasseDeriv (p.natDegree - 1) p)
      = ∑ i ∈ Finset.range 2, (hasseDeriv (p.natDegree - 1) p).coeff i * (1 : F) ^ i :=
    eval_eq_sum_range' hlt 1
  have hc0 : (hasseDeriv (p.natDegree - 1) p).coeff 0 = p.coeff (p.natDegree - 1) := by
    rw [hasseDeriv_coeff]
    simp
  have hc1 : (hasseDeriv (p.natDegree - 1) p).coeff 1 = (p.natDegree : F) * p.leadingCoeff := by
    rw [hasseDeriv_coeff]
    have he : 1 + (p.natDegree - 1) = p.natDegree := by omega
    rw [he]
    have hch : p.natDegree.choose (p.natDegree - 1) = p.natDegree := by
      rw [Nat.choose_symm hd, Nat.choose_one_right]
    rw [hch, Polynomial.coeff_natDegree]
  have hsum : eval (1 : F) (hasseDeriv (p.natDegree - 1) p)
      = p.coeff (p.natDegree - 1) + (p.natDegree : F) * p.leadingCoeff := by
    rw [h2]
    simp [Finset.sum_range_succ, hc0, hc1]
  rw [shiftDelta, Polynomial.coeff_sub, h1, hsum]
  ring

theorem shiftDelta_ne_zero {p : F[X]} (hd : 1 ≤ p.natDegree) : shiftDelta p ≠ 0 := by
  intro h
  have hc := coeff_shiftDelta_pred hd
  rw [h, Polynomial.coeff_zero] at hc
  have hlead : p.leadingCoeff ≠ 0 := by
    refine Polynomial.leadingCoeff_ne_zero.mpr ?_
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hd
    exact absurd hd (by omega)
  have hn : (p.natDegree : F) ≠ 0 := by
    simpa using (by omega : p.natDegree ≠ 0)
  exact (mul_ne_zero hn hlead) hc.symm

theorem natDegree_shiftDelta {p : F[X]} (hd : 1 ≤ p.natDegree) :
    (shiftDelta p).natDegree = p.natDegree - 1 := by
  have hp : p ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hd
    exact absurd hd (by omega)
  have hne := shiftDelta_ne_zero hd
  have hlt : (shiftDelta p).natDegree < p.natDegree :=
    Polynomial.natDegree_lt_natDegree hne (degree_shiftDelta_lt hp)
  have hge : p.natDegree - 1 ≤ (shiftDelta p).natDegree := by
    refine Polynomial.le_natDegree_of_ne_zero ?_
    rw [coeff_shiftDelta_pred hd]
    have hlead : p.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
    have hn : (p.natDegree : F) ≠ 0 := by
      simpa using (by omega : p.natDegree ≠ 0)
    exact mul_ne_zero hn hlead
  omega

theorem leadingCoeff_shiftDelta {p : F[X]} (hd : 1 ≤ p.natDegree) :
    (shiftDelta p).leadingCoeff = (p.natDegree : F) * p.leadingCoeff := by
  rw [Polynomial.leadingCoeff, natDegree_shiftDelta hd, coeff_shiftDelta_pred hd]

/-! ### The degree at infinity of the shift difference -/

omit [CharZero F] in
theorem algebraMap_poly_ne_zero {p : F[X]} (hp : p ≠ 0) :
    algebraMap F[X] (RatFunc F) p ≠ 0 :=
  fun h => hp (RatFunc.algebraMap_injective F (by rw [h, map_zero]))

omit [CharZero F] in
theorem intDegree_algebraMap_div {p q : F[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    (algebraMap F[X] (RatFunc F) p / algebraMap F[X] (RatFunc F) q).intDegree
      = (p.natDegree : ℤ) - (q.natDegree : ℤ) := by
  rw [RatFunc.intDegree_div (algebraMap_poly_ne_zero hp) (algebraMap_poly_ne_zero hq),
    RatFunc.intDegree_polynomial, RatFunc.intDegree_polynomial]

/-- The numerator of the shift difference in the reduced presentation. -/
def shiftDiffNum (f : RatFunc F) : F[X] :=
  shiftDelta f.num * f.denom - f.num * shiftDelta f.denom

omit [CharZero F] in
theorem ratShift_mul_denom_comp (f : RatFunc F) :
    ratShift f * algebraMap F[X] (RatFunc F) (f.denom.comp (X + C 1))
      = algebraMap F[X] (RatFunc F) (f.num.comp (X + C 1)) := by
  have ha1 : algebraMap F[X] (RatFunc F) f.denom ≠ 0 :=
    algebraMap_poly_ne_zero f.denom_ne_zero
  have h2 := div_mul_cancel₀ (algebraMap F[X] (RatFunc F) f.num) ha1
  rw [RatFunc.num_div_denom] at h2
  have h3 := congrArg ratShift h2
  rw [map_mul, ratShift_algebraMap, ratShift_algebraMap] at h3
  exact h3

omit [CharZero F] in
theorem mul_denom_eq_num (f : RatFunc F) :
    f * algebraMap F[X] (RatFunc F) f.denom = algebraMap F[X] (RatFunc F) f.num := by
  have ha1 : algebraMap F[X] (RatFunc F) f.denom ≠ 0 :=
    algebraMap_poly_ne_zero f.denom_ne_zero
  have h2 := div_mul_cancel₀ (algebraMap F[X] (RatFunc F) f.num) ha1
  rwa [RatFunc.num_div_denom] at h2

omit [CharZero F] in
theorem ratShift_sub_self_eq (f : RatFunc F) :
    ratShift f - f = algebraMap F[X] (RatFunc F) (shiftDiffNum f)
      / algebraMap F[X] (RatFunc F) (f.denom.comp (X + C 1) * f.denom) := by
  have hden : f.denom ≠ 0 := f.denom_ne_zero
  have hdenS : f.denom.comp (X + C 1) ≠ 0 := comp_X_add_C_one_ne_zero hden
  have ha1 : algebraMap F[X] (RatFunc F) f.denom ≠ 0 := algebraMap_poly_ne_zero hden
  have ha2 : algebraMap F[X] (RatFunc F) (f.denom.comp (X + C 1)) ≠ 0 :=
    algebraMap_poly_ne_zero hdenS
  have h1 := ratShift_mul_denom_comp f
  have h2 := mul_denom_eq_num f
  have hN : shiftDiffNum f
      = f.num.comp (X + C 1) * f.denom - f.num * f.denom.comp (X + C 1) := by
    rw [shiftDiffNum, shiftDelta, shiftDelta]; ring
  rw [eq_div_iff (by rw [map_mul]; exact mul_ne_zero ha2 ha1), hN, map_sub, map_mul, map_mul,
    map_mul, ← h1, ← h2]
  ring

theorem shiftDiffNum_spec {f : RatFunc F} (hf : f ≠ 0)
    (hne : f.num.natDegree ≠ f.denom.natDegree) :
    shiftDiffNum f ≠ 0 ∧
      (shiftDiffNum f).natDegree = f.num.natDegree + f.denom.natDegree - 1 := by
  classical
  have hp : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hq : f.denom ≠ 0 := f.denom_ne_zero
  rcases Nat.eq_zero_or_pos f.num.natDegree with hm0 | hm1
  · have hn1 : 1 ≤ f.denom.natDegree := by omega
    have hdp : shiftDelta f.num = 0 := shiftDelta_eq_zero_of_natDegree_zero hm0
    have hdq : shiftDelta f.denom ≠ 0 := shiftDelta_ne_zero hn1
    refine ⟨?_, ?_⟩
    · rw [shiftDiffNum, hdp, zero_mul, zero_sub, neg_ne_zero]
      exact mul_ne_zero hp hdq
    · rw [shiftDiffNum, hdp, zero_mul, zero_sub, Polynomial.natDegree_neg,
        Polynomial.natDegree_mul hp hdq, natDegree_shiftDelta hn1, hm0]
      omega
  · rcases Nat.eq_zero_or_pos f.denom.natDegree with hn0 | hn1
    · have hdq : shiftDelta f.denom = 0 := shiftDelta_eq_zero_of_natDegree_zero hn0
      have hdp : shiftDelta f.num ≠ 0 := shiftDelta_ne_zero hm1
      refine ⟨?_, ?_⟩
      · rw [shiftDiffNum, hdq, mul_zero, sub_zero]
        exact mul_ne_zero hdp hq
      · rw [shiftDiffNum, hdq, mul_zero, sub_zero, Polynomial.natDegree_mul hdp hq,
          natDegree_shiftDelta hm1, hn0]
        omega
    · have hdp : shiftDelta f.num ≠ 0 := shiftDelta_ne_zero hm1
      have hdq : shiftDelta f.denom ≠ 0 := shiftDelta_ne_zero hn1
      have hA : (shiftDelta f.num * f.denom).natDegree
          = f.num.natDegree + f.denom.natDegree - 1 := by
        rw [Polynomial.natDegree_mul hdp hq, natDegree_shiftDelta hm1]
        omega
      have hB : (f.num * shiftDelta f.denom).natDegree
          = f.num.natDegree + f.denom.natDegree - 1 := by
        rw [Polynomial.natDegree_mul hp hdq, natDegree_shiftDelta hn1]
        omega
      have hcA : (shiftDelta f.num * f.denom).coeff (f.num.natDegree + f.denom.natDegree - 1)
          = (f.num.natDegree : F) * f.num.leadingCoeff * f.denom.leadingCoeff := by
        rw [← hA, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_mul,
          leadingCoeff_shiftDelta hm1]
      have hcB : (f.num * shiftDelta f.denom).coeff (f.num.natDegree + f.denom.natDegree - 1)
          = f.num.leadingCoeff * ((f.denom.natDegree : F) * f.denom.leadingCoeff) := by
        rw [← hB, Polynomial.coeff_natDegree, Polynomial.leadingCoeff_mul,
          leadingCoeff_shiftDelta hn1]
      have hlp : f.num.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
      have hlq : f.denom.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
      have hcast : (f.num.natDegree : F) - (f.denom.natDegree : F) ≠ 0 := by
        intro h
        exact hne (Nat.cast_injective (sub_eq_zero.mp h))
      have hcoeff : (shiftDiffNum f).coeff (f.num.natDegree + f.denom.natDegree - 1)
          = ((f.num.natDegree : F) - (f.denom.natDegree : F))
              * (f.num.leadingCoeff * f.denom.leadingCoeff) := by
        rw [shiftDiffNum, Polynomial.coeff_sub, hcA, hcB]
        ring
      have hne0 : (shiftDiffNum f).coeff (f.num.natDegree + f.denom.natDegree - 1) ≠ 0 := by
        rw [hcoeff]
        exact mul_ne_zero hcast (mul_ne_zero hlp hlq)
      refine ⟨fun h => hne0 (by rw [h, Polynomial.coeff_zero]), ?_⟩
      have hge : f.num.natDegree + f.denom.natDegree - 1 ≤ (shiftDiffNum f).natDegree :=
        Polynomial.le_natDegree_of_ne_zero hne0
      have hle : (shiftDiffNum f).natDegree ≤ f.num.natDegree + f.denom.natDegree - 1 := by
        refine le_trans (Polynomial.natDegree_sub_le _ _) ?_
        rw [hA, hB]
        exact le_of_eq (max_self _)
      omega

/-- **The shift difference drops the degree at infinity by exactly one**, for a rational function
of nonzero degree. -/
theorem intDegree_ratShift_sub {f : RatFunc F} (hf : f ≠ 0) (hd : f.intDegree ≠ 0) :
    ratShift f - f ≠ 0 ∧ (ratShift f - f).intDegree = f.intDegree - 1 := by
  have hp : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hq : f.denom ≠ 0 := f.denom_ne_zero
  have hqS : f.denom.comp (X + C 1) ≠ 0 := comp_X_add_C_one_ne_zero hq
  have hid : f.intDegree = (f.num.natDegree : ℤ) - (f.denom.natDegree : ℤ) := rfl
  have hne : f.num.natDegree ≠ f.denom.natDegree := by
    intro h
    exact hd (by rw [hid, h, sub_self])
  obtain ⟨hN, hNdeg⟩ := shiftDiffNum_spec hf hne
  have hD : (f.denom.comp (X + C 1) * f.denom).natDegree = 2 * f.denom.natDegree := by
    rw [Polynomial.natDegree_mul hqS hq, natDegree_comp_X_add_one]
    omega
  have hDne : f.denom.comp (X + C 1) * f.denom ≠ 0 := mul_ne_zero hqS hq
  constructor
  · rw [ratShift_sub_self_eq f]
    exact div_ne_zero (algebraMap_poly_ne_zero hN) (algebraMap_poly_ne_zero hDne)
  · rw [ratShift_sub_self_eq f, intDegree_algebraMap_div hN hDne, hNdeg, hD, RatFunc.intDegree]
    have h1 : 1 ≤ f.num.natDegree + f.denom.natDegree := by omega
    omega

/-- A shift-invariant rational function is constant, so a nonconstant rational function of degree
zero at infinity has shift difference of degree at most `-2`. -/
theorem intDegree_ratShift_sub_le_of_intDegree_zero {f : RatFunc F}
    (h0 : f.intDegree = 0) (hnc : ratShift f ≠ f) :
    ratShift f - f ≠ 0 ∧ (ratShift f - f).intDegree ≤ -2 := by
  have hf : f ≠ 0 := by
    intro h
    exact hnc (by rw [h, map_zero])
  have hp : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hq : f.denom ≠ 0 := f.denom_ne_zero
  have hid : f.intDegree = (f.num.natDegree : ℤ) - (f.denom.natDegree : ℤ) := rfl
  have hmn : f.num.natDegree = f.denom.natDegree := by
    have h1 := h0
    rw [hid, sub_eq_zero] at h1
    exact_mod_cast h1
  set c : F := f.num.leadingCoeff / f.denom.leadingCoeff with hc
  have hlp : f.num.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hp
  have hlq : f.denom.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hq
  have hcne : c ≠ 0 := div_ne_zero hlp hlq
  set g : RatFunc F := f - algebraMap F (RatFunc F) c with hg
  have hshiftg : ratShift g - g = ratShift f - f := by
    rw [hg, map_sub, ratShift_const]
    ring
  have hgne : g ≠ 0 := by
    intro h
    have hz : f - algebraMap F (RatFunc F) c = 0 := by rw [← hg]; exact h
    have hfc : f = algebraMap F (RatFunc F) c := sub_eq_zero.mp hz
    exact hnc (by rw [hfc, ratShift_const])
  have hnum : f.num - Polynomial.C c * f.denom ≠ 0 := by
    intro h
    have : f = algebraMap F (RatFunc F) c := by
      have hd : algebraMap F[X] (RatFunc F) f.num
          = algebraMap F[X] (RatFunc F) (Polynomial.C c * f.denom) := by
        rw [← sub_eq_zero, ← map_sub, h, map_zero]
      have hfd : f = algebraMap F[X] (RatFunc F) f.num
          / algebraMap F[X] (RatFunc F) f.denom := (RatFunc.num_div_denom f).symm
      rw [hfd, hd, map_mul, algebraMap_polyC,
        mul_div_assoc, div_self (algebraMap_poly_ne_zero hq), mul_one]
    exact hnc (by rw [this, ratShift_const])
  have hdlt : (f.num - Polynomial.C c * f.denom).natDegree < f.denom.natDegree := by
    have hdeg : f.num.degree = (Polynomial.C c * f.denom).degree := by
      rw [Polynomial.degree_mul, Polynomial.degree_C hcne, zero_add,
        Polynomial.degree_eq_natDegree hp, Polynomial.degree_eq_natDegree hq, hmn]
    have hlead : f.num.leadingCoeff = (Polynomial.C c * f.denom).leadingCoeff := by
      rw [Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hc]
      field_simp
    have := Polynomial.degree_sub_lt hdeg hp hlead
    have h2 : (f.num - Polynomial.C c * f.denom).natDegree < f.num.natDegree :=
      Polynomial.natDegree_lt_natDegree hnum this
    omega
  have hgdeg : g.intDegree < 0 := by
    have ha1 : algebraMap F[X] (RatFunc F) f.denom ≠ 0 := algebraMap_poly_ne_zero hq
    have hgeq : g = algebraMap F[X] (RatFunc F) (f.num - Polynomial.C c * f.denom)
        / algebraMap F[X] (RatFunc F) f.denom := by
      rw [eq_div_iff ha1, hg, sub_mul, mul_denom_eq_num f, map_sub, map_mul, algebraMap_polyC]
    rw [hgeq, intDegree_algebraMap_div hnum hq]
    omega
  obtain ⟨hgs, hgsdeg⟩ := intDegree_ratShift_sub hgne (by omega)
  refine ⟨by rw [← hshiftg]; exact hgs, ?_⟩
  rw [← hshiftg, hgsdeg]
  omega


omit [CharZero F] in
theorem intDegree_ratShift (f : RatFunc F) : (ratShift f).intDegree = f.intDegree := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hp : f.num ≠ 0 := RatFunc.num_ne_zero hf
  have hq : f.denom ≠ 0 := f.denom_ne_zero
  have hpS : f.num.comp (X + C 1) ≠ 0 := comp_X_add_C_one_ne_zero hp
  have hqS : f.denom.comp (X + C 1) ≠ 0 := comp_X_add_C_one_ne_zero hq
  have hsh : ratShift f = algebraMap F[X] (RatFunc F) (f.num.comp (X + C 1))
      / algebraMap F[X] (RatFunc F) (f.denom.comp (X + C 1)) := by
    rw [eq_div_iff (algebraMap_poly_ne_zero hqS)]
    exact ratShift_mul_denom_comp f
  rw [hsh, intDegree_algebraMap_div hpS hqS, natDegree_comp_X_add_one, natDegree_comp_X_add_one]
  rfl

omit [CharZero F] in
theorem intDegree_algebraMap_const (κ : F) :
    (algebraMap F (RatFunc F) κ).intDegree = 0 := by
  rw [← algebraMap_polyC, RatFunc.intDegree_polynomial, Polynomial.natDegree_C]
  rfl

omit [CharZero F] in
theorem intDegree_add_le_of_le {x y : RatFunc F} {t : ℤ}
    (hx : x = 0 ∨ x.intDegree ≤ t) (hy : y = 0 ∨ y.intDegree ≤ t) :
    x + y = 0 ∨ (x + y).intDegree ≤ t := by
  rcases hx with rfl | hx
  · rcases hy with rfl | hy
    · left; simp
    · right; simpa using hy
  · rcases hy with rfl | hy
    · right; simpa using hx
    · rcases eq_or_ne y 0 with rfl | hy0
      · right; simpa using hx
      · rcases eq_or_ne (x + y) 0 with h | h
        · left; exact h
        · right
          exact le_trans (RatFunc.intDegree_add_le hy0 h) (max_le hx hy)

omit [CharZero F] in
theorem intDegree_mul_le_of_le {b x : RatFunc F} {t : ℤ} (hb : b ≠ 0)
    (hx : x = 0 ∨ x.intDegree ≤ t) :
    b * x = 0 ∨ (b * x).intDegree ≤ b.intDegree + t := by
  rcases hx with rfl | hx
  · left; simp
  · rcases eq_or_ne x 0 with rfl | hx0
    · left; simp
    · right
      rw [RatFunc.intDegree_mul hb hx0]
      omega

omit [CharZero F] in
theorem intDegree_add_eq_left {u v : RatFunc F} (hu : u ≠ 0)
    (hlt : v = 0 ∨ v.intDegree < u.intDegree) :
    u + v ≠ 0 ∧ (u + v).intDegree = u.intDegree := by
  rcases hlt with rfl | hlt
  · simpa using hu
  have hne : u + v ≠ 0 := by
    intro h
    have huv : u = -v := by linear_combination h
    rw [huv, RatFunc.intDegree_neg] at hlt
    exact lt_irrefl _ hlt
  refine ⟨hne, le_antisymm ?_ ?_⟩
  · rcases eq_or_ne v 0 with rfl | hv
    · simp
    · exact le_trans (RatFunc.intDegree_add_le hv hne) (max_le le_rfl hlt.le)
  · rcases eq_or_ne v 0 with rfl | hv
    · simp
    · have h2 : u = (u + v) + (-v) := by ring
      have hvneg : (-v) ≠ 0 := neg_ne_zero.mpr hv
      have hsum : (u + v) + (-v) ≠ 0 := by rw [← h2]; exact hu
      have hbnd := RatFunc.intDegree_add_le hvneg hsum
      rw [← h2, RatFunc.intDegree_neg] at hbnd
      rcases max_cases (u + v).intDegree v.intDegree with ⟨hm, _⟩ | ⟨hm, _⟩
      · rw [hm] at hbnd; exact hbnd
      · rw [hm] at hbnd; exact absurd (lt_of_le_of_lt hbnd hlt) (lt_irrefl _)

/-- The shift difference drops the degree at infinity by at least one. -/
theorem ratShift_sub_le (f : RatFunc F) :
    ratShift f - f = 0 ∨ (ratShift f - f).intDegree ≤ f.intDegree - 1 := by
  rcases eq_or_ne (ratShift f) f with h | h
  · left; rw [h, sub_self]
  rcases eq_or_ne f 0 with rfl | hf
  · left; simp
  rcases eq_or_ne f.intDegree 0 with h0 | h0
  · obtain ⟨-, hb⟩ := intDegree_ratShift_sub_le_of_intDegree_zero h0 h
    right; omega
  · obtain ⟨-, hb⟩ := intDegree_ratShift_sub hf h0
    right; omega

/-- Twice-shifted difference. -/
theorem ratShift_two_sub_le (f : RatFunc F) :
    ratShift (ratShift f) - f = 0 ∨
      (ratShift (ratShift f) - f).intDegree ≤ f.intDegree - 1 := by
  have hsplit : ratShift (ratShift f) - f
      = (ratShift (ratShift f) - ratShift f) + (ratShift f - f) := by ring
  have h1 : ratShift (ratShift f) - ratShift f = 0 ∨
      (ratShift (ratShift f) - ratShift f).intDegree ≤ f.intDegree - 1 := by
    have := ratShift_sub_le (ratShift f)
    rwa [intDegree_ratShift f] at this
  have h2 := ratShift_sub_le f
  rw [hsplit]
  exact intDegree_add_le_of_le h1 h2


end

end GaloisForLFunctions.HTGeometry.FieldShift
