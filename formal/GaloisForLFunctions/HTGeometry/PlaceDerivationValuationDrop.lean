import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Derivation.Basic

/-!
# A cleared derivation drops the adic valuation by a bounded amount

Let `R` be a Dedekind domain with fraction field `K`, let `v` be a height-one prime of `R`, and
let `D` be a derivation of `K`.  Suppose one nonzero `c` clears `D` at the place: `c·D x` is
`v`-integral for every `x ∈ R`.  Then for every `f ∈ K`

`v(c · D f) ≤ v(f) · exp 1`,

i.e. the cleared derivation lowers the order at `v` by at most one.  The proof is an induction on
ideal powers: on `Q^{n+1} = Q^n·Q` the Leibniz rule splits a generator `x·y` into two terms, each
losing exactly one factor, and the quotient rule extends the bound from `R` to `K`.

If moreover `c ∉ Qᵉ`, the clearing factor can be removed at the cost of `e`:

`v(D f) ≤ v(f) · exp e`,

which is the statement that the derivation lowers the order at the place by at most the order of
the different generator.
-/

namespace GaloisForLFunctions.HTGeometry

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
variable {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]
variable {A : Type*} [CommRing A] [Algebra A K]
variable (v : HeightOneSpectrum R)

theorem one_le_exp_one : (1 : ℤᵐ⁰) ≤ exp (1 : ℤ) := by
  rw [← exp_zero]
  exact exp_le_exp.mpr zero_le_one

/-- **The cleared derivation on an ideal power.**  An element of `Qⁿ` is sent by `c·D` to an
element of valuation at most `exp (1 − n)`: each Leibniz split loses exactly one factor. -/
theorem valuation_mul_deriv_le_exp_of_mem_pow (D : Derivation A K K) {c : K}
    (hclear : ∀ x : R, v.valuation K (c * D (algebraMap R K x)) ≤ 1)
    {n : ℕ} {a : R} (ha : a ∈ v.asIdeal ^ n) :
    v.valuation K (c * D (algebraMap R K a)) ≤ exp (1 - (n : ℤ)) := by
  induction n generalizing a with
  | zero =>
      refine le_trans (hclear a) ?_
      rw [← exp_zero]
      exact exp_le_exp.mpr (by norm_num)
  | succ n ih =>
      rw [pow_succ] at ha
      induction ha using Submodule.mul_induction_on with
      | mem_mul_mem x hx y hy =>
          have hsplit : c * D (algebraMap R K (x * y))
              = algebraMap R K x * (c * D (algebraMap R K y))
                + algebraMap R K y * (c * D (algebraMap R K x)) := by
            rw [map_mul, Derivation.leibniz]
            simp only [smul_eq_mul]
            ring
          rw [hsplit]
          refine le_trans (Valuation.map_add _ _ _) (max_le ?_ ?_)
          · rw [Valuation.map_mul]
            have h1 : v.valuation K (algebraMap R K x) ≤ exp (-(n : ℤ)) := by
              rw [valuation_of_algebraMap]
              exact (intValuation_le_pow_iff_mem v x n).mpr hx
            have h2 : v.valuation K (c * D (algebraMap R K y)) ≤ 1 := hclear y
            calc v.valuation K (algebraMap R K x) * v.valuation K (c * D (algebraMap R K y))
                ≤ exp (-(n : ℤ)) * 1 := mul_le_mul' h1 h2
              _ = exp (1 - ((n + 1 : ℕ) : ℤ)) := by
                  rw [mul_one]
                  congr 1
                  push_cast
                  ring
          · rw [Valuation.map_mul]
            have h1 : v.valuation K (algebraMap R K y) ≤ exp (-(1 : ℤ)) := by
              rw [valuation_of_algebraMap]
              exact (intValuation_le_pow_iff_mem v y 1).mpr (by rwa [pow_one])
            have h2 := ih hy
            calc v.valuation K (algebraMap R K y) * v.valuation K (c * D (algebraMap R K x))
                ≤ exp (-(1 : ℤ)) * exp (1 - (n : ℤ)) := mul_le_mul' h1 h2
              _ = exp (1 - ((n + 1 : ℕ) : ℤ)) := by
                  rw [← exp_add]
                  congr 1
                  push_cast
                  ring
      | add x y hx hy ihx ihy =>
          rw [map_add, map_add, mul_add]
          exact le_trans (Valuation.map_add _ _ _) (max_le ihx ihy)

/-- **The relative drop on `R`.** -/
theorem valuation_mul_deriv_algebraMap_le (D : Derivation A K K) {c : K}
    (hclear : ∀ x : R, v.valuation K (c * D (algebraMap R K x)) ≤ 1) (a : R) :
    v.valuation K (c * D (algebraMap R K a))
      ≤ v.valuation K (algebraMap R K a) * exp (1 : ℤ) := by
  rcases eq_or_ne a 0 with rfl | ha
  · rw [map_zero, map_zero, mul_zero, Valuation.map_zero]
    exact zero_le'
  · have hval : v.intValuation a
        = exp (-(multiplicity v.asIdeal (Ideal.span {a}) : ℤ)) :=
      v.intValuation_eq_exp_neg_multiplicity ha
    set n : ℕ := multiplicity v.asIdeal (Ideal.span {a}) with hn
    have hmem : a ∈ v.asIdeal ^ n :=
      (intValuation_le_pow_iff_mem v a n).mp (le_of_eq hval)
    refine le_trans (valuation_mul_deriv_le_exp_of_mem_pow v D hclear hmem) ?_
    rw [valuation_of_algebraMap, hval, ← exp_add]
    exact exp_le_exp.mpr (by omega)

/-- **The relative drop on the fraction field.** -/
theorem valuation_mul_deriv_le (D : Derivation A K K) {c : K}
    (hclear : ∀ x : R, v.valuation K (c * D (algebraMap R K x)) ≤ 1) (f : K) :
    v.valuation K (c * D f) ≤ v.valuation K f * exp (1 : ℤ) := by
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := R) f
  have hbne : algebraMap R K b ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors hb
  have hvb : v.valuation K (algebraMap R K b) ≠ 0 :=
    (Valuation.ne_zero_iff _).mpr hbne
  have hsplit : c * D (algebraMap R K a / algebraMap R K b)
      = (algebraMap R K b)⁻¹ ^ 2
        * (algebraMap R K b * (c * D (algebraMap R K a))
          - algebraMap R K a * (c * D (algebraMap R K b))) := by
    rw [Derivation.leibniz_div]
    simp only [smul_eq_mul]
    ring
  rw [hsplit, Valuation.map_mul, Valuation.map_pow, Valuation.map_inv]
  have hnum : v.valuation K
      (algebraMap R K b * (c * D (algebraMap R K a))
        - algebraMap R K a * (c * D (algebraMap R K b)))
      ≤ v.valuation K (algebraMap R K a) * v.valuation K (algebraMap R K b) * exp (1 : ℤ) := by
    refine le_trans (Valuation.map_sub _ _ _) (max_le ?_ ?_)
    · rw [Valuation.map_mul]
      calc v.valuation K (algebraMap R K b) * v.valuation K (c * D (algebraMap R K a))
          ≤ v.valuation K (algebraMap R K b)
            * (v.valuation K (algebraMap R K a) * exp (1 : ℤ)) :=
            mul_le_mul' le_rfl (valuation_mul_deriv_algebraMap_le v D hclear a)
        _ = v.valuation K (algebraMap R K a) * v.valuation K (algebraMap R K b)
            * exp (1 : ℤ) := by ring
    · rw [Valuation.map_mul]
      calc v.valuation K (algebraMap R K a) * v.valuation K (c * D (algebraMap R K b))
          ≤ v.valuation K (algebraMap R K a)
            * (v.valuation K (algebraMap R K b) * exp (1 : ℤ)) :=
            mul_le_mul' le_rfl (valuation_mul_deriv_algebraMap_le v D hclear b)
        _ = v.valuation K (algebraMap R K a) * v.valuation K (algebraMap R K b)
            * exp (1 : ℤ) := by ring
  calc (v.valuation K (algebraMap R K b))⁻¹ ^ 2
      * v.valuation K
        (algebraMap R K b * (c * D (algebraMap R K a))
          - algebraMap R K a * (c * D (algebraMap R K b)))
      ≤ (v.valuation K (algebraMap R K b))⁻¹ ^ 2
        * (v.valuation K (algebraMap R K a) * v.valuation K (algebraMap R K b)
          * exp (1 : ℤ)) := mul_le_mul' le_rfl hnum
    _ = v.valuation K (algebraMap R K a / algebraMap R K b) * exp (1 : ℤ) := by
        rw [Valuation.map_div]
        field_simp
        ring

/-- **Removing the clearing factor costs its order.**  If the clearing element avoids `Qᵉ`, the
derivation itself lowers the valuation at the place by at most `e`. -/
theorem valuation_deriv_le_of_not_mem_pow (D : Derivation A K K) {c : R}
    (hclear : ∀ x : R, v.valuation K (algebraMap R K c * D (algebraMap R K x)) ≤ 1)
    {e : ℕ} (hce : c ∉ v.asIdeal ^ e) (f : K) :
    v.valuation K (D f) ≤ v.valuation K f * exp (e : ℤ) := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact hce (Submodule.zero_mem _)
  set n : ℕ := multiplicity v.asIdeal (Ideal.span {c}) with hn
  have hval : v.intValuation c = exp (-(n : ℤ)) :=
    v.intValuation_eq_exp_neg_multiplicity hc0
  have hne : n < e := by
    by_contra hcon
    push_neg at hcon
    refine hce ?_
    have hmem : c ∈ v.asIdeal ^ n :=
      (intValuation_le_pow_iff_mem v c n).mp (le_of_eq hval)
    exact Ideal.pow_le_pow_right hcon hmem
  have hvc : v.valuation K (algebraMap R K c) = exp (-(n : ℤ)) := by
    rw [valuation_of_algebraMap, hval]
  have hvcne : v.valuation K (algebraMap R K c) ≠ 0 := by
    rw [hvc]
    exact exp_ne_zero _
  have hmain := valuation_mul_deriv_le v D hclear f
  rw [Valuation.map_mul, hvc] at hmain
  have hstep : exp (-(n : ℤ)) * v.valuation K (D f) ≤ v.valuation K f * exp (1 : ℤ) →
      v.valuation K (D f) ≤ v.valuation K f * exp (1 + (n : ℤ)) := by
    intro h
    have h2 := mul_le_mul' (le_refl (exp (n : ℤ))) h
    rw [← mul_assoc, ← exp_add] at h2
    simp only [add_neg_cancel, exp_zero, one_mul] at h2
    calc v.valuation K (D f) ≤ exp (n : ℤ) * (v.valuation K f * exp (1 : ℤ)) := h2
      _ = v.valuation K f * exp (1 + (n : ℤ)) := by
          rw [exp_add]
          ring
  refine le_trans (hstep hmain) ?_
  exact mul_le_mul' le_rfl (exp_le_exp.mpr (by omega))

end GaloisForLFunctions.HTGeometry
