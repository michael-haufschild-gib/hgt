import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysInseparableDegree

/-!
# Vanishing of inseparable atoms in characteristic `p`

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Corollary 1.5(2)
(`t28n`): when the base field and the target both have characteristic `p`, a ring homomorphism
`ℤ̲κ/κ₀ → C` is determined by its restriction to `ℤ̲κ₀^sep`, because it kills the atom of every
inseparable element.

The mechanism is the source's: writing `φ (r) = P (d_r · (r))`, the relation
`φ (r) ^ 2 = (d_r ^ 2 / d_{r^(2 : ℕ)}) φ (r ^ 2)` holds, and `d_{r^(2 : ℕ)} ∣ d_r`, so for inseparable `r` the
scalar `d_r ^ 2 / d_{r^(2 : ℕ)}` is a positive power of `p` and hence zero in `C`.  Thus `φ (r)` is
nilpotent, so zero in a reduced ring.
-/

namespace RHTower

variable {F E : Type*} [Field F] [Field E] [Algebra F E] {q : ℕ} [ExpChar F q]

/-- Squaring does not increase the inseparability exponent. -/
theorem deningerInsepExp_sq_le [Algebra.IsAlgebraic F E] (x : E) :
    deningerInsepExp F E q (x * x) ≤ deningerInsepExp F E q x := by
  refine deningerInsepExp_le ?_
  rw [deningerMem_insepExpSet_iff, mul_pow]
  exact mul_mem (deningerInsepExp_mem x) (deningerInsepExp_mem x)

variable (F E q)

/-- The atom `d_r · (r)` of the subring `ℤ̲κ/κ₀`. -/
noncomputable def deningerInsepAtom [Algebra.IsAlgebraic F E] (r : Eˣ) :
    deningerInsepSubring F E q :=
  ⟨(deningerInsepDegree F E q (r : E) : ℤ) • MonoidAlgebra.single r (1 : ℤ), by
    classical
    intro s
    rw [MonoidAlgebra.coeff_smul, MonoidAlgebra.coeff_single]
    by_cases hs : r = s
    · subst hs
      simp
    · simp [hs]⟩

variable {F E q}

theorem deningerInsepAtom_val [Algebra.IsAlgebraic F E] (r : Eˣ) :
    (deningerInsepAtom F E q r : MonoidAlgebra ℤ Eˣ)
      = (deningerInsepDegree F E q (r : E) : ℤ) • MonoidAlgebra.single r (1 : ℤ) := rfl

/-- The square of an inseparable atom is a `q`-power multiple of the atom at `r ^ 2`. -/
theorem deningerInsepAtom_sq [Algebra.IsAlgebraic F E] (r : Eˣ) :
    deningerInsepAtom F E q r * deningerInsepAtom F E q r
      = ((q ^ (2 * deningerInsepExp F E q (r : E)
            - deningerInsepExp F E q ((r : E) * (r : E))) : ℕ) : ℤ)
        * deningerInsepAtom F E q (r * r) := by
  have hle : deningerInsepExp F E q ((r : E) * (r : E)) ≤ deningerInsepExp F E q (r : E) :=
    deningerInsepExp_sq_le (r : E)
  apply Subtype.ext
  rw [Subring.coe_mul, Subring.coe_mul, Subring.coe_intCast,
    deningerInsepAtom_val, deningerInsepAtom_val]
  rw [smul_mul_smul_comm, MonoidAlgebra.single_mul_single, one_mul]
  rw [← zsmul_eq_mul, smul_smul]
  congr 1
  · have hval : ((r * r : Eˣ) : E) = (r : E) * (r : E) := rfl
    rw [hval]
    simp only [deningerInsepDegree]
    have hpow : q ^ deningerInsepExp F E q (r : E) * q ^ deningerInsepExp F E q (r : E)
        = q ^ (2 * deningerInsepExp F E q (r : E)
            - deningerInsepExp F E q ((r : E) * (r : E)))
          * q ^ deningerInsepExp F E q ((r : E) * (r : E)) := by
      rw [← pow_add, ← pow_add]
      congr 1
      omega
    exact_mod_cast hpow

/-- **Deninger, Corollary 1.5(2), the key vanishing.**  In characteristic `p`, a ring
homomorphism from `ℤ̲κ/κ₀` into a reduced ring of characteristic `p` kills the atom of every
inseparable element. -/
theorem deningerInsepAtom_map_eq_zero [Algebra.IsAlgebraic F E] {p : ℕ} [Fact p.Prime]
    (hqp : q = p) {C : Type*} [CommRing C] [CharP C p] [IsReduced C]
    (P : deningerInsepSubring F E q →+* C) (r : Eˣ)
    (hr : 0 < deningerInsepExp F E q (r : E)) :
    P (deningerInsepAtom F E q r) = 0 := by
  have hle : deningerInsepExp F E q ((r : E) * (r : E)) ≤ deningerInsepExp F E q (r : E) :=
    deningerInsepExp_sq_le (r : E)
  have hq0 : (q : C) = 0 := by
    rw [hqp]
    exact CharP.cast_eq_zero C p
  have hk : 2 * deningerInsepExp F E q (r : E)
      - deningerInsepExp F E q ((r : E) * (r : E)) ≠ 0 := by omega
  have hsquare : P (deningerInsepAtom F E q r) * P (deningerInsepAtom F E q r) = 0 := by
    rw [← map_mul, deningerInsepAtom_sq, map_mul, map_intCast]
    push_cast
    rw [hq0, zero_pow hk, zero_mul]
  have hnil : IsNilpotent (P (deningerInsepAtom F E q r)) := ⟨2, by rw [pow_two]; exact hsquare⟩
  exact hnil.eq_zero

end RHTower
