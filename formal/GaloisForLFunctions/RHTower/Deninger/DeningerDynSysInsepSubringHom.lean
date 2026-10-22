import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysInseparableDegree
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.IsAlgClosed.Basic
import Mathlib.Algebra.MonoidAlgebra.Defs
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysIntegralLift

/-!
# Homomorphisms of `ℤ̲κ` are determined by their restriction to `ℤ̲κ / κ₀`

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Corollary 1.5(1).

The subring `ℤ̲κ / κ₀` consists of the integral combinations `∑ n_r (r)` with `d_r ∣ n_r`.  It
contains, for every atom `(a)`, both the additive multiple `d_a · (a)` and the ring power
`(a) ^ d_a = (a ^ d_a)` — the latter because `a ^ d_a` is separable over `κ₀`, so its degree of
inseparability is `1`.

Consequently a ring homomorphism of `ℤ̲κ` into an algebraically closed field `C` is determined by
its restriction: if `d_a` is invertible in `C` the additive relation determines the value, and
otherwise `C` has characteristic `p` and is perfect, so the multiplicative relation does.
-/

namespace RHTower

open MonoidAlgebra

variable {F E : Type*} [Field F] [Field E] [Algebra F E] (q : ℕ) [ExpChar F q]

/-- The degree of inseparability of `x ^ d_x` is `1`. -/
theorem deningerInsepDegree_pow_self [Algebra.IsAlgebraic F E] (x : E) :
    deningerInsepDegree F E q (x ^ deningerInsepDegree F E q x) = 1 := by
  have hmem := deningerInsepExp_mem (F := F) (E := E) (q := q) x
  rw [deningerMem_insepExpSet_iff] at hmem
  have h0 : (0 : ℕ) ∈ deningerInsepExpSet F E q (x ^ deningerInsepDegree F E q x) := by
    rw [deningerMem_insepExpSet_iff, pow_zero, pow_one, deningerInsepDegree]
    exact hmem
  have := deningerInsepExp_le (F := F) (E := E) (q := q) h0
  rw [deningerInsepDegree, Nat.le_zero.1 this, pow_zero]

variable {q}

/-- The atoms raised to their degree of inseparability lie in `ℤ̲κ / κ₀`. -/
theorem deningerAtomPow_mem_insepSubring [Algebra.IsAlgebraic F E] (a : Eˣ) :
    (MonoidAlgebra.single a (1 : ℤ)) ^ deningerInsepDegree F E q (a : E)
      ∈ deningerInsepSubring F E q := by
  classical
  intro r
  rw [MonoidAlgebra.single_pow, one_pow]
  show (deningerInsepDegree F E q (r : E) : ℤ) ∣ (Finsupp.single (a ^ deningerInsepDegree F E q (a : E)) (1:ℤ)) r
  rw [Finsupp.single_apply]
  by_cases hr : a ^ deningerInsepDegree F E q (a : E) = r
  · rw [if_pos hr]
    have hval : ((a ^ deningerInsepDegree F E q (a : E) : Eˣ) : E)
        = (a : E) ^ deningerInsepDegree F E q (a : E) := by
      simp
    have : deningerInsepDegree F E q (r : E) = 1 := by
      rw [← hr, hval]
      exact deningerInsepDegree_pow_self q (a : E)
    rw [this]
    simp
  · rw [if_neg hr]
    simp

/-- The additive multiples `d_a · (a)` lie in `ℤ̲κ / κ₀`. -/
theorem deningerAtomNsmul_mem_insepSubring [Algebra.IsAlgebraic F E] (a : Eˣ) :
    (deningerInsepDegree F E q (a : E) : ℤ) • (MonoidAlgebra.single a (1 : ℤ))
      ∈ deningerInsepSubring F E q := by
  classical
  intro r
  rw [MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
  show (deningerInsepDegree F E q (r : E) : ℤ) ∣ (Finsupp.single a ((deningerInsepDegree F E q (a : E) : ℤ))) r
  rw [Finsupp.single_apply]
  by_cases hr : a = r
  · rw [if_pos hr, hr]
  · rw [if_neg hr]
    exact dvd_zero _

/-- **Deninger, Corollary 1.5(1).**  A ring homomorphism of `ℤ̲κ` into an algebraically closed
field is determined by its restriction to `ℤ̲κ / κ₀`. -/
theorem deningerInsepSubring_restrict_injective [Algebra.IsAlgebraic F E] {C : Type*} [Field C]
    [IsAlgClosed C] (φ ψ : MonoidAlgebra ℤ Eˣ →+* C)
    (h : ∀ ξ ∈ deningerInsepSubring F E q, φ ξ = ψ ξ) : φ = ψ := by
  classical
  refine MonoidAlgebra.ringHom_ext ?_ ?_
  · intro r
    have h1 : (MonoidAlgebra.single (1 : Eˣ) r : MonoidAlgebra ℤ Eˣ)
        = r • (1 : MonoidAlgebra ℤ Eˣ) := by
      rw [MonoidAlgebra.one_def, MonoidAlgebra.smul_single, smul_eq_mul, mul_one]
    rw [h1, map_zsmul, map_one, map_zsmul, map_one]
  · intro a
    set d := deningerInsepDegree F E q (a : E) with hd
    have hdpos : 0 < d := by
      rw [hd, deningerInsepDegree]
      exact pow_pos (expChar_pos F q) _
    have hpow : φ (MonoidAlgebra.single a (1 : ℤ)) ^ d
        = ψ (MonoidAlgebra.single a (1 : ℤ)) ^ d := by
      have := h _ (deningerAtomPow_mem_insepSubring (q := q) a)
      rwa [map_pow, map_pow] at this
    have hsmul : (d : ℤ) • φ (MonoidAlgebra.single a (1 : ℤ))
        = (d : ℤ) • ψ (MonoidAlgebra.single a (1 : ℤ)) := by
      have := h _ (deningerAtomNsmul_mem_insepSubring (q := q) a)
      rwa [map_zsmul, map_zsmul] at this
    by_cases hdC : (d : C) = 0
    · -- `C` has characteristic `q` and is perfect
      have hqprime : q.Prime ∨ q = 1 := expChar_is_prime_or_one F q
      rcases hqprime with hqp | hq1
      · haveI : Fact q.Prime := ⟨hqp⟩
        have hqC : (q : C) = 0 := by
          obtain ⟨n, hn⟩ : ∃ n : ℕ, d = q ^ n := ⟨deningerInsepExp F E q (a : E), hd⟩
          have hqn : ((q : C)) ^ n = 0 := by
            rw [← Nat.cast_pow, ← hn]
            exact hdC
          exact pow_eq_zero_iff'.1 hqn |>.1
        haveI : CharP C q := by
          refine (CharP.charP_iff_prime_eq_zero hqp).2 hqC
        haveI : ExpChar C q := ExpChar.prime hqp
        haveI : PerfectField C := IsAlgClosed.perfectField C
        haveI : PerfectRing C q := PerfectField.toPerfectRing (K := C) (p := q)
        obtain ⟨n, hn⟩ : ∃ n : ℕ, d = q ^ n := ⟨deningerInsepExp F E q (a : E), hd⟩
        have hinj : Function.Injective fun x : C => x ^ d := by
          rw [hn]
          intro x y hxy
          have h1 : (iterateFrobenius C q n) x = (iterateFrobenius C q n) y := by
            rw [iterateFrobenius_def, iterateFrobenius_def]
            exact hxy
          exact (iterateFrobeniusEquiv C q n).injective h1
        exact hinj hpow
      · exfalso
        rw [hq1] at hd
        have : d = 1 := by rw [hd, deningerInsepDegree, one_pow]
        rw [this] at hdC
        simp at hdC
    · have hdz : ((d : ℤ) : C) ≠ 0 := by
        rw [Int.cast_natCast]
        exact hdC
      have := hsmul
      rw [zsmul_eq_mul, zsmul_eq_mul] at this
      exact mul_left_cancel₀ hdz this

end RHTower

namespace RHTower

open MonoidAlgebra

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {q : ℕ} [ExpChar F q]

/-- The atoms with arbitrary integral coefficients are integral over `ℤ̲κ / κ₀`: the `d_a`-th
power of `(a) n` is the atom `(a ^ d_a) n ^ d_a`, which lies in the subring. -/
theorem deningerSinglePow_mem_insepSubring [Algebra.IsAlgebraic F E] (a : Eˣ) (n : ℤ) :
    (MonoidAlgebra.single a n) ^ deningerInsepDegree F E q (a : E)
      ∈ deningerInsepSubring F E q := by
  classical
  intro r
  rw [MonoidAlgebra.single_pow]
  show (deningerInsepDegree F E q (r : E) : ℤ) ∣
    (Finsupp.single (a ^ deningerInsepDegree F E q (a : E))
      (n ^ deningerInsepDegree F E q (a : E))) r
  rw [Finsupp.single_apply]
  by_cases hr : a ^ deningerInsepDegree F E q (a : E) = r
  · rw [if_pos hr]
    have hval : ((a ^ deningerInsepDegree F E q (a : E) : Eˣ) : E)
        = (a : E) ^ deningerInsepDegree F E q (a : E) := by simp
    have hone : deningerInsepDegree F E q (r : E) = 1 := by
      rw [← hr, hval]
      exact deningerInsepDegree_pow_self q (a : E)
    rw [hone]
    simp
  · rw [if_neg hr]
    exact dvd_zero _

/-- Every atom is integral over `ℤ̲κ / κ₀`. -/
theorem deningerSingle_isIntegral [Algebra.IsAlgebraic F E] (a : Eˣ) (n : ℤ) :
    IsIntegral ↥(deningerInsepSubring F E q) (MonoidAlgebra.single a n) := by
  classical
  set d := deningerInsepDegree F E q (a : E) with hd
  have hdpos : 0 < d := by
    rw [hd, deningerInsepDegree]
    exact pow_pos (expChar_pos F q) _
  refine ⟨Polynomial.X ^ d - Polynomial.C
    (⟨(MonoidAlgebra.single a n) ^ d, deningerSinglePow_mem_insepSubring a n⟩ :
      ↥(deningerInsepSubring F E q)), ?_, ?_⟩
  · exact (Polynomial.monic_X_pow d).sub_of_left (by
      refine lt_of_le_of_lt (Polynomial.degree_C_le) ?_
      rw [Polynomial.degree_X_pow]
      exact_mod_cast Nat.cast_pos.2 hdpos)
  · simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C]
    exact sub_self _

/-- `ℤ̲κ` is integral over `ℤ̲κ / κ₀`. -/
instance deningerInsepSubring_isIntegral [Algebra.IsAlgebraic F E] :
    Algebra.IsIntegral ↥(deningerInsepSubring F E q) (MonoidAlgebra ℤ Eˣ) := by
  classical
  constructor
  intro x
  refine MonoidAlgebra.induction_on x ?_ ?_ ?_
  · intro g
    exact deningerSingle_isIntegral g 1
  · intro f g hf hg
    exact hf.add hg
  · intro r f hf
    have hr : (r • f : MonoidAlgebra ℤ Eˣ) = (r : MonoidAlgebra ℤ Eˣ) * f := by
      rw [zsmul_eq_mul]
    rw [hr]
    refine IsIntegral.mul ?_ hf
    have hmem : ((r : MonoidAlgebra ℤ Eˣ)) ∈ deningerInsepSubring F E q := by
      have h1 : ((r : MonoidAlgebra ℤ Eˣ)) = r • (1 : MonoidAlgebra ℤ Eˣ) := by
        rw [zsmul_eq_mul, mul_one]
      rw [h1]
      exact zsmul_mem (one_mem _) r
    refine ⟨Polynomial.X - Polynomial.C ⟨(r : MonoidAlgebra ℤ Eˣ), hmem⟩,
      Polynomial.monic_X_sub_C _, ?_⟩
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_X, Polynomial.eval₂_C]
    exact sub_self _

/-- **Deninger, Corollary 1.5(1).**  Restriction of homomorphisms into an algebraically closed
field along `ℤ̲κ / κ₀ ⊆ ℤ̲κ` is surjective. -/
theorem deningerInsepSubring_restrict_surjective [Algebra.IsAlgebraic F E] {C : Type*} [Field C]
    [IsAlgClosed C] :
    Function.Surjective (fun ψ : MonoidAlgebra ℤ Eˣ →+* C =>
      ψ.comp (algebraMap ↥(deningerInsepSubring F E q) (MonoidAlgebra ℤ Eˣ))) :=
  deningerHom_restrict_surjective_of_isIntegral

/-- **Deninger, Corollary 1.5(1).**  Restriction along `ℤ̲κ / κ₀ ⊆ ℤ̲κ` is a bijection on
homomorphisms into an algebraically closed field. -/
theorem deningerInsepSubring_restrict_bijective [Algebra.IsAlgebraic F E] {C : Type*} [Field C]
    [IsAlgClosed C] :
    Function.Bijective (fun ψ : MonoidAlgebra ℤ Eˣ →+* C =>
      ψ.comp (algebraMap ↥(deningerInsepSubring F E q) (MonoidAlgebra ℤ Eˣ))) := by
  refine ⟨?_, deningerInsepSubring_restrict_surjective⟩
  intro φ ψ h
  refine deningerInsepSubring_restrict_injective (F := F) (E := E) (q := q) φ ψ ?_
  intro ξ hξ
  exact congrArg (fun F : ↥(deningerInsepSubring F E q) →+* C => F ⟨ξ, hξ⟩) h

end RHTower
