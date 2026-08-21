import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Tactic

/-!
# The order of a rational function at a point, and the square criterion

Zeros count positively and poles negatively, and the resulting integer order is additive on
products.  Its use here is a parity criterion: over an algebraically closed field a rational
function whose order is even at every point is a square.

The mechanism is unique factorisation twice.  Coprimality of the reduced numerator and denominator
means at most one of them vanishes at a given point, so an even difference of multiplicities forces
both multiplicities even; and a polynomial over an algebraically closed field whose root
multiset has all multiplicities even is a constant times a square, because that multiset is twice
another one.  The leftover constant is a square because the field is algebraically closed.

* `ratOrd`, `ratOrd_of_rep`, `ratOrd_mul`;
* `exists_sq_of_even_rootMultiplicity`;
* `isSquare_of_even_ratOrd`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

variable {K : Type*} [Field K]

theorem algebraMap_polynomial_ne_zero {P : Polynomial K} (hP : P ≠ 0) :
    algebraMap (Polynomial K) (RatFunc K) P ≠ 0 :=
  (map_ne_zero_iff _ (IsFractionRing.injective (Polynomial K) (RatFunc K))).mpr hP

theorem algebraMap_num_eq (g : RatFunc K) :
    algebraMap (Polynomial K) (RatFunc K) g.num
      = g * algebraMap (Polynomial K) (RatFunc K) g.denom :=
  (div_eq_iff (algebraMap_polynomial_ne_zero (RatFunc.denom_ne_zero g))).mp
    (RatFunc.num_div_denom g)

/-- The order of a rational function at a point: zeros count positively, poles negatively. -/
noncomputable def ratOrd (g : RatFunc K) (c : K) : ℤ :=
  (g.num.rootMultiplicity c : ℤ) - (g.denom.rootMultiplicity c : ℤ)

/-- **The order can be read off any representation as a quotient of nonzero polynomials.** -/
theorem ratOrd_of_rep {g : RatFunc K} {A B : Polynomial K} (hA : A ≠ 0) (hB : B ≠ 0)
    (hg : g * algebraMap (Polynomial K) (RatFunc K) B
      = algebraMap (Polynomial K) (RatFunc K) A) (c : K) :
    ratOrd g c = (A.rootMultiplicity c : ℤ) - (B.rootMultiplicity c : ℤ) := by
  have hinj : Function.Injective (algebraMap (Polynomial K) (RatFunc K)) :=
    IsFractionRing.injective _ _
  have hnum : g.num ≠ 0 := RatFunc.num_ne_zero (by
    intro h0
    rw [h0, zero_mul] at hg
    exact hA (hinj (by rw [← hg, map_zero])))
  have hden : g.denom ≠ 0 := RatFunc.denom_ne_zero g
  have hcross : g.num * B = A * g.denom := by
    refine hinj ?_
    rw [map_mul, map_mul]
    rw [algebraMap_num_eq g, ← hg]
    ring
  have hmul := congrArg (fun P => Polynomial.rootMultiplicity c P) hcross
  simp only [Polynomial.rootMultiplicity_mul (mul_ne_zero hnum hB),
    Polynomial.rootMultiplicity_mul (mul_ne_zero hA hden)] at hmul
  rw [ratOrd]
  omega

theorem ratOrd_mul {f g : RatFunc K} (hf : f ≠ 0) (hg : g ≠ 0) (c : K) :
    ratOrd (f * g) c = ratOrd f c + ratOrd g c := by
  have hinj : Function.Injective (algebraMap (Polynomial K) (RatFunc K)) :=
    IsFractionRing.injective _ _
  have hrep : f * g * algebraMap (Polynomial K) (RatFunc K) (f.denom * g.denom)
      = algebraMap (Polynomial K) (RatFunc K) (f.num * g.num) := by
    rw [map_mul, map_mul]
    rw [algebraMap_num_eq f, algebraMap_num_eq g]
    ring
  rw [ratOrd_of_rep (mul_ne_zero (RatFunc.num_ne_zero hf) (RatFunc.num_ne_zero hg))
      (mul_ne_zero (RatFunc.denom_ne_zero f) (RatFunc.denom_ne_zero g)) hrep c,
    Polynomial.rootMultiplicity_mul
      (mul_ne_zero (RatFunc.num_ne_zero hf) (RatFunc.num_ne_zero hg)),
    Polynomial.rootMultiplicity_mul
      (mul_ne_zero (RatFunc.denom_ne_zero f) (RatFunc.denom_ne_zero g)),
    ratOrd, ratOrd]
  push_cast
  ring

/-- **A polynomial with everywhere-even root multiplicity is a constant times a square.** -/
theorem exists_sq_of_even_rootMultiplicity [IsAlgClosed K] {A : Polynomial K} (hA : A ≠ 0)
    (h : ∀ c, Even (A.rootMultiplicity c)) :
    ∃ (a : K) (q : Polynomial K), a ≠ 0 ∧ A = Polynomial.C a * q ^ 2 := by
  classical
  have hcount : ∀ c ∈ A.roots, 2 ∣ Multiset.count c A.roots := by
    intro c _
    rw [Polynomial.count_roots]
    exact (h c).two_dvd
  obtain ⟨M, hM⟩ := Multiset.exists_smul_of_dvd_count A.roots hcount
  refine ⟨A.leadingCoeff, (M.map (fun r => Polynomial.X - Polynomial.C r)).prod,
    Polynomial.leadingCoeff_ne_zero.mpr hA, ?_⟩
  have hsplit := Polynomial.Splits.eq_prod_roots (IsAlgClosed.splits (p := A) (k := K))
  rw [hM, Multiset.map_nsmul, Multiset.prod_nsmul] at hsplit
  exact hsplit

/-- **A rational function of everywhere-even order is a square.** -/
theorem isSquare_of_even_ratOrd [IsAlgClosed K] {g : RatFunc K} (hg : g ≠ 0)
    (h : ∀ c, Even (ratOrd g c)) : IsSquare g := by
  classical
  have hnum : g.num ≠ 0 := RatFunc.num_ne_zero hg
  have hden : g.denom ≠ 0 := RatFunc.denom_ne_zero g
  have hcop : IsCoprime g.num g.denom := RatFunc.isCoprime_num_denom g
  have hsep : ∀ c, Even (g.num.rootMultiplicity c) ∧ Even (g.denom.rootMultiplicity c) := by
    intro c
    have hc := h c
    rw [ratOrd] at hc
    by_cases hz : g.num.rootMultiplicity c = 0
    · refine ⟨by rw [hz]; exact ⟨0, rfl⟩, ?_⟩
      rw [hz] at hc
      simpa using hc.neg
    · have hroot : g.num.IsRoot c := (Polynomial.rootMultiplicity_pos hnum).mp (by omega)
      have hden0 : g.denom.rootMultiplicity c = 0 := by
        by_contra hne
        have hroot' : g.denom.IsRoot c := (Polynomial.rootMultiplicity_pos hden).mp (by omega)
        obtain ⟨u, v, huv⟩ := hcop
        have := congrArg (fun P => Polynomial.eval c P) huv
        simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one] at this
        rw [Polynomial.IsRoot.def.mp hroot, Polynomial.IsRoot.def.mp hroot'] at this
        simp at this
      refine ⟨?_, by rw [hden0]; exact ⟨0, rfl⟩⟩
      rw [hden0] at hc
      simpa using hc
  obtain ⟨a, q, ha, hq⟩ := exists_sq_of_even_rootMultiplicity hnum fun c => (hsep c).1
  obtain ⟨b, s, hb, hs⟩ := exists_sq_of_even_rootMultiplicity hden fun c => (hsep c).2
  obtain ⟨t, ht⟩ := IsAlgClosed.exists_pow_nat_eq (a / b) (n := 2) (by norm_num)
  refine ⟨algebraMap K (RatFunc K) t * (algebraMap (Polynomial K) (RatFunc K) q
    / algebraMap (Polynomial K) (RatFunc K) s), ?_⟩
  have hs0 : s ≠ 0 := by
    intro h0
    apply hden
    rw [hs, h0]
    ring
  have hqne : algebraMap (Polynomial K) (RatFunc K) s ≠ 0 := algebraMap_polynomial_ne_zero hs0
  have hgval : g = algebraMap (Polynomial K) (RatFunc K) g.num
      / algebraMap (Polynomial K) (RatFunc K) g.denom := (RatFunc.num_div_denom g).symm
  rw [hgval, hq, hs]
  have hb' : algebraMap K (RatFunc K) b ≠ 0 := by
    simpa using (fun h0 => hb ((algebraMap K (RatFunc K)).injective h0))
  have hbb : algebraMap (Polynomial K) (RatFunc K) (Polynomial.C b) = algebraMap K (RatFunc K) b :=
    by simp
  have haa : algebraMap (Polynomial K) (RatFunc K) (Polynomial.C a) = algebraMap K (RatFunc K) a :=
    by simp
  rw [map_mul, map_mul, map_pow, map_pow, hbb, haa]
  have hteq : algebraMap K (RatFunc K) a
      = (algebraMap K (RatFunc K) t) ^ 2 * algebraMap K (RatFunc K) b := by
    rw [← map_pow, ← map_mul, ht]
    congr 1
    field_simp
  rw [hteq]
  field_simp

end GaloisForLFunctions.HTGeometry
