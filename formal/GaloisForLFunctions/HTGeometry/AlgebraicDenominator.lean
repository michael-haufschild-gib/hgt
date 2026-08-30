import Mathlib

/-!
# Denominators of algebraic numbers

A natural number `d` is a *denominator* for a complex number `x` when `d x` is an algebraic
integer.  Denominators are monotone under divisibility, stable under sums with a common
denominator, and multiply under products.  The field norm of a nonzero algebraic integer is a
denominator for its inverse whose size is the product of the moduli of all its conjugates; this is
the arithmetic bookkeeping behind Pólya's denominator induction.
-/

open NumberField

namespace GaloisForLFunctions.HTGeometry

/-- `d` is a denominator for `x`: the multiple `d x` is an algebraic integer. -/
def DenBy (d : ℕ) (x : ℂ) : Prop := IsIntegral ℤ ((d : ℂ) * x)

theorem intCast_isIntegral (d : ℕ) : IsIntegral ℤ ((d : ℂ)) := isIntegral_natCast d

theorem denBy_of_isIntegral {x : ℂ} (h : IsIntegral ℤ x) (d : ℕ) : DenBy d x :=
  IsIntegral.mul (intCast_isIntegral d) h

theorem DenBy.mono {d e : ℕ} {x : ℂ} (hde : d ∣ e) (h : DenBy d x) : DenBy e x := by
  obtain ⟨k, rfl⟩ := hde
  have hk : IsIntegral ℤ ((k : ℂ) * ((d : ℂ) * x)) :=
    IsIntegral.mul (intCast_isIntegral k) h
  have hrw : ((k : ℂ)) * ((d : ℂ) * x) = ((d * k : ℕ) : ℂ) * x := by push_cast; ring
  rwa [hrw] at hk

theorem DenBy.add {d : ℕ} {x y : ℂ} (hx : DenBy d x) (hy : DenBy d y) : DenBy d (x + y) := by
  have h : IsIntegral ℤ ((d : ℂ) * x + (d : ℂ) * y) := IsIntegral.add hx hy
  unfold DenBy
  have hrw : (d : ℂ) * x + (d : ℂ) * y = (d : ℂ) * (x + y) := by ring
  rwa [hrw] at h

theorem DenBy.mul {d e : ℕ} {x y : ℂ} (hx : DenBy d x) (hy : DenBy e y) :
    DenBy (d * e) (x * y) := by
  have h : IsIntegral ℤ (((d : ℂ) * x) * ((e : ℂ) * y)) := IsIntegral.mul hx hy
  unfold DenBy
  have hrw : ((d : ℂ) * x) * ((e : ℂ) * y) = ((d * e : ℕ) : ℂ) * (x * y) := by push_cast; ring
  rwa [hrw] at h

theorem DenBy.neg {d : ℕ} {x : ℂ} (hx : DenBy d x) : DenBy d (-x) := by
  have h : IsIntegral ℤ (-((d : ℂ) * x)) := IsIntegral.neg hx
  unfold DenBy
  have hrw : -((d : ℂ) * x) = (d : ℂ) * (-x) := by ring
  rwa [hrw] at h

theorem DenBy.sub {d : ℕ} {x y : ℂ} (hx : DenBy d x) (hy : DenBy d y) : DenBy d (x - y) := by
  simpa [sub_eq_add_neg] using hx.add hy.neg

@[simp] theorem DenBy.zero (d : ℕ) : DenBy d 0 := by
  unfold DenBy
  rw [mul_zero]
  exact isIntegral_zero

theorem DenBy.sum {ι : Type*} {d : ℕ} {s : Finset ι} {f : ι → ℂ}
    (h : ∀ i ∈ s, DenBy d (f i)) : DenBy d (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (h a (Finset.mem_insert_self a s)).add
        (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem DenBy.intMul {d : ℕ} {x : ℂ} (m : ℤ) (hx : DenBy d x) : DenBy d ((m : ℂ) * x) := by
  have hm : IsIntegral ℤ ((m : ℂ)) := isIntegral_intCast m
  have h : IsIntegral ℤ ((m : ℂ) * ((d : ℂ) * x)) := IsIntegral.mul hm hx
  unfold DenBy
  have hrw : (m : ℂ) * ((d : ℂ) * x) = (d : ℂ) * ((m : ℂ) * x) := by ring
  rwa [hrw] at h

theorem DenBy.natMul {d : ℕ} {x : ℂ} (m : ℕ) (hx : DenBy d x) : DenBy d ((m : ℂ) * x) := by
  have h : IsIntegral ℤ ((m : ℂ) * ((d : ℂ) * x)) := IsIntegral.mul (intCast_isIntegral m) hx
  unfold DenBy
  have hrw : (m : ℂ) * ((d : ℂ) * x) = (d : ℂ) * ((m : ℂ) * x) := by ring
  rwa [hrw] at h

theorem DenBy.pow {d : ℕ} {x : ℂ} (hx : DenBy d x) (k : ℕ) : DenBy (d ^ k) (x ^ k) := by
  induction k with
  | zero => simpa using denBy_of_isIntegral (isIntegral_one) 1
  | succ k ih =>
      have := DenBy.mul ih hx
      rwa [← pow_succ, ← pow_succ] at this

/-- The rationals are algebraic over the integers. -/
theorem rat_isAlgebraic_int : Algebra.IsAlgebraic ℤ ℚ := by
  constructor
  intro q
  refine ⟨Polynomial.C (q.den : ℤ) * Polynomial.X - Polynomial.C q.num, ?_, ?_⟩
  · intro h
    have hc := congrArg (fun p : Polynomial ℤ => Polynomial.coeff p 1) h
    simp only [Polynomial.coeff_sub, Polynomial.coeff_C_mul, Polynomial.coeff_X_one,
      Polynomial.coeff_C, mul_one, Polynomial.coeff_zero,
      if_neg (by norm_num : ¬(1 = 0))] at hc
    rw [sub_zero] at hc
    exact q.den_nz (by exact_mod_cast hc)
  · rw [map_sub, map_mul, Polynomial.aeval_C, Polynomial.aeval_X, Polynomial.aeval_C]
    have h1 : (algebraMap ℤ ℚ) (q.den : ℤ) = (q.den : ℚ) := by norm_num
    have h2 : (algebraMap ℤ ℚ) q.num = (q.num : ℚ) := by norm_num
    rw [h1, h2, mul_comm]
    have := Rat.mul_den_eq_num q
    linarith [this]

/-- Every algebraic number has a positive denominator. -/
theorem exists_denBy {x : ℂ} (hx : IsAlgebraic ℚ x) : ∃ d : ℕ, 0 < d ∧ DenBy d x := by
  haveI := rat_isAlgebraic_int
  have hxz : IsAlgebraic ℤ x := hx.restrictScalars ℤ
  obtain ⟨y, hy0, hy⟩ := hxz.exists_integral_multiple
  have hy' : IsIntegral ℤ ((y : ℂ) * x) := by
    simpa [Algebra.smul_def] using hy
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy0, ?_⟩
  unfold DenBy
  have hcast : ((y.natAbs : ℕ) : ℂ) = ((y.natAbs : ℤ) : ℂ) := by
    exact (Int.cast_natCast _).symm
  rw [hcast]
  rcases Int.natAbs_eq y with h | h
  · rw [← h]; exact hy'
  · have hEq : ((y.natAbs : ℤ) : ℂ) * x = -((y : ℂ) * x) := by
      have : ((y : ℤ) : ℂ) = -((y.natAbs : ℤ) : ℂ) := by
        conv_lhs => rw [h]
        push_cast
        ring
      rw [this]; ring
    rw [hEq]; exact hy'.neg

end GaloisForLFunctions.HTGeometry

section NumberFieldDenominator

variable {K : Type*} [Field K] [NumberField K]

/-- **The norm is a denominator for the inverse.**  For a nonzero algebraic integer of a number
field, the absolute norm is a natural number, equal to the product of the moduli of all its
conjugates, whose quotient by the number itself is again an algebraic integer. -/
theorem exists_norm_denominator (β : K) (hβ : β ≠ 0) (hint : IsIntegral ℤ β) (φ : K →+* ℂ) :
    ∃ A : ℕ, 0 < A ∧ (A : ℝ) = ∏ σ : K →+* ℂ, ‖σ β‖ ∧ IsIntegral ℤ ((A : ℂ) / φ β) := by
  classical
  set b : 𝓞 K := ⟨β, hint⟩ with hb
  have hb0 : b ≠ 0 := by
    intro h
    exact hβ (congrArg (fun z : 𝓞 K => (z : K)) h)
  have hnorm : Algebra.norm ℤ b ≠ 0 := Algebra.norm_ne_zero_iff.mpr hb0
  have hcast : ((Algebra.norm ℤ b : ℤ) : ℚ) = Algebra.norm ℚ (b : K) := Algebra.coe_norm_int b
  have hprod : (algebraMap ℚ ℂ) (Algebra.norm ℚ (b : K)) = ∏ σ : K →+* ℂ, σ (b : K) := by
    have h := Algebra.norm_eq_prod_embeddings (L := K) ℚ ℂ (b : K)
    refine h.trans ?_
    exact Fintype.prod_equiv
      (RingHom.equivRatAlgHom (R := K) (S := ℂ)).symm _ _ fun σ => rfl
  have hbK : (b : K) = β := rfl
  have hcast2 : ((Algebra.norm ℤ b : ℤ) : ℂ) = ∏ σ : K →+* ℂ, σ β := by
    rw [← hbK, ← hprod, ← hcast]
    simp
  refine ⟨(Algebra.norm ℤ b).natAbs, Int.natAbs_pos.mpr hnorm, ?_, ?_⟩
  · have hn : ‖((Algebra.norm ℤ b : ℤ) : ℂ)‖ = ∏ σ : K →+* ℂ, ‖σ β‖ := by
      rw [hcast2, norm_prod]
    rw [← hn, Complex.norm_intCast, ← Int.cast_abs, Int.abs_eq_natAbs]
    exact (Int.cast_natCast _).symm
  · have hφ0 : φ β ≠ 0 := by
      intro h
      exact hβ (φ.injective (by simpa using h))
    have hsplit : (∏ σ : K →+* ℂ, σ β)
        = φ β * ∏ σ ∈ Finset.univ.erase φ, σ β :=
      (Finset.mul_prod_erase _ _ (Finset.mem_univ φ)).symm
    have hrest : IsIntegral ℤ (∏ σ ∈ Finset.univ.erase φ, σ β) :=
      IsIntegral.prod _ fun σ _ => map_isIntegral_int σ hint
    have hAeq : (((Algebra.norm ℤ b).natAbs : ℕ) : ℂ) = ((Algebra.norm ℤ b : ℤ) : ℂ)
        ∨ (((Algebra.norm ℤ b).natAbs : ℕ) : ℂ) = -((Algebra.norm ℤ b : ℤ) : ℂ) := by
      rcases Int.natAbs_eq (Algebra.norm ℤ b) with h | h
      · left
        have : ((((Algebra.norm ℤ b).natAbs : ℤ)) : ℂ) = ((Algebra.norm ℤ b : ℤ) : ℂ) := by
          conv_rhs => rw [h]
        simpa using this
      · right
        have : ((((Algebra.norm ℤ b).natAbs : ℤ)) : ℂ) = -((Algebra.norm ℤ b : ℤ) : ℂ) := by
          conv_rhs => rw [h]
          push_cast
          ring
        simpa using this
    have hdiv : ((Algebra.norm ℤ b : ℤ) : ℂ) / φ β = ∏ σ ∈ Finset.univ.erase φ, σ β := by
      rw [hcast2, hsplit, mul_comm]
      field_simp
    rcases hAeq with h | h
    · rw [h, hdiv]; exact hrest
    · rw [h, neg_div, hdiv]; exact hrest.neg

end NumberFieldDenominator
