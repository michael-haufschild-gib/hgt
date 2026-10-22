/-
Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 1.3
(`t26n`): the exponent of the correspondence is the degree of inseparability.

`DeningerDynSysNormalizedCorrespondence` matches the normalized irreducibles over `κ₀` with those
over `κ₀^perf` by `α = α̃ ^ d`.  Here `d` is identified as a power of the exponential
characteristic — the classical degree of inseparability of a root of `α`.

The argument writes the minimal polynomial as `expand F (q^m) g` with `g` separable irreducible
(`Polynomial.exists_separable_of_irreducible`), notes that `g` stays irreducible over the perfect
closure (`deningerIrreducible_map_of_separable`), and pulls the expansion back through the
iterated Frobenius, which is bijective there.  The resulting monic irreducible `h` satisfies
`h ^ q ^ m = (minpoly F x).map = (minpoly L x) ^ d`, so `h = minpoly L x` and `d = q ^ m`.

Also proved: an expansion `expand F n g` is irreducible only if `g` is.
-/
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysNormalizedCorrespondence

namespace RHTower

open Polynomial

variable {F : Type*} [Field F]

/-- An expansion of a polynomial is irreducible only if the polynomial is. -/
theorem deningerIrreducible_of_expand {n : ℕ} (hn : 0 < n) {g : Polynomial F}
    (h : Irreducible ((Polynomial.expand F n) g)) : Irreducible g := by
  have hgne : g ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h
    exact h.ne_zero rfl
  refine ⟨fun hu => h.not_isUnit (hu.map (Polynomial.expand F n)), ?_⟩
  intro a b hab
  have hexp : (Polynomial.expand F n) g
      = (Polynomial.expand F n) a * (Polynomial.expand F n) b := by
    rw [hab, map_mul]
  have hane : a ≠ 0 := fun h0 => hgne (by rw [hab, h0, zero_mul])
  have hbne : b ≠ 0 := fun h0 => hgne (by rw [hab, h0, mul_zero])
  have hkey : ∀ c : Polynomial F, c ≠ 0 → IsUnit ((Polynomial.expand F n) c) → IsUnit c := by
    intro c hc hu
    have hd : c.natDegree * n = 0 := by
      rw [← Polynomial.natDegree_expand]
      exact Polynomial.natDegree_eq_zero_of_isUnit hu
    have hc0 : c.natDegree = 0 := by
      rcases Nat.mul_eq_zero.1 hd with h' | h'
      · exact h'
      · omega
    refine Polynomial.isUnit_iff.2 ⟨c.coeff 0, ?_, (Polynomial.eq_C_of_natDegree_eq_zero hc0).symm⟩
    refine Ne.isUnit (fun h0 => hc ?_)
    rw [Polynomial.eq_C_of_natDegree_eq_zero hc0, h0, map_zero]
  rcases h.isUnit_or_isUnit hexp with hu | hu
  · exact Or.inl (hkey a hane hu)
  · exact Or.inr (hkey b hbne hu)

/-- **Deninger, Proposition 1.3 (`t26n`), the exponent is a power of the characteristic.**  Over
the perfect closure the exponent in `(minpoly F x).map = (minpoly L x) ^ d` is `d = q ^ m` for the
exponential characteristic `q`, where `expand F (q ^ m) g = minpoly F x` is the separable
contraction of the minimal polynomial; `q ^ m` is the classical degree of inseparability of `x`. -/
theorem deningerMinpoly_map_perfectClosure_eq_pow_expChar {E : Type*} [Field E] [Algebra F E]
    [IsAlgClosed E] (q : ℕ) [hq : ExpChar F q] {x : E} (hx : IsIntegral F x) :
    ∃ (m : ℕ) (g : Polynomial F), g.Separable ∧ Polynomial.expand F (q ^ m) g = minpoly F x ∧
      (minpoly F x).map (algebraMap F (perfectClosure F E))
        = (minpoly (perfectClosure F E) x) ^ q ^ m := by
  classical
  haveI : ExpChar E q := expChar_of_injective_ringHom (algebraMap F E).injective q
  have hqpos : 0 < q := expChar_pos F q
  have hxL : IsIntegral (perfectClosure F E) x := hx.tower_top
  obtain ⟨k, hk, heq⟩ :=
    deningerMinpoly_map_eq_pow (F := F) (L := perfectClosure F E) (E := E) q x hx
  obtain ⟨m, g, hgsep, hgexp, h, hhmonic, hhirr, hhpow⟩ :
      ∃ (m : ℕ) (g : Polynomial F), g.Separable ∧ Polynomial.expand F (q ^ m) g = minpoly F x ∧
        ∃ h : Polynomial (perfectClosure F E), h.Monic ∧ Irreducible h ∧
          h ^ q ^ m = (minpoly F x).map (algebraMap F (perfectClosure F E)) := by
    cases hq with
    | zero =>
        haveI : ExpChar F 1 := ExpChar.zero
        refine ⟨0, minpoly F x, Irreducible.separable (minpoly.irreducible hx), by simp,
          (minpoly F x).map (algebraMap F (perfectClosure F E)),
          (minpoly.monic hx).map _, ?_, by simp⟩
        exact deningerIrreducible_map_of_separable 1 (minpoly.monic hx) (minpoly.irreducible hx)
          (Irreducible.separable (minpoly.irreducible hx))
    | prime hqprime =>
        haveI : ExpChar F q := ExpChar.prime hqprime
        obtain ⟨n, g, hgsep, hgexp⟩ := Polynomial.exists_separable_of_irreducible q
          (minpoly.irreducible hx) hqprime.ne_zero
        have hqn : 0 < q ^ n := pow_pos hqpos n
        have hgmonic : g.Monic := by
          have hm := minpoly.monic hx
          rw [← hgexp, Polynomial.Monic, Polynomial.leadingCoeff_expand hqn] at hm
          exact hm
        have hgirr : Irreducible g :=
          deningerIrreducible_of_expand hqn (by rw [hgexp]; exact minpoly.irreducible hx)
        have hgmapirr : Irreducible (g.map (algebraMap F (perfectClosure F E))) :=
          deningerIrreducible_map_of_separable q hgmonic hgirr hgsep
        haveI : PerfectRing (perfectClosure F E) q := inferInstance
        set e : (perfectClosure F E) ≃+* (perfectClosure F E) :=
          iterateFrobeniusEquiv (perfectClosure F E) q n with he
        refine ⟨n, g, hgsep, hgexp,
          (g.map (algebraMap F (perfectClosure F E))).map (e.symm : _ →+* _), ?_, ?_, ?_⟩
        · exact (hgmonic.map _).map _
        · exact (MulEquiv.irreducible_iff (Polynomial.mapEquiv e.symm)).2 hgmapirr
        · have hcomp : (iterateFrobenius (perfectClosure F E) q n).comp
              (e.symm : _ →+* _) = RingHom.id _ := by
            refine RingHom.ext fun y => ?_
            show (iterateFrobenius (perfectClosure F E) q n) (e.symm y) = y
            rw [← iterateFrobeniusEquiv_apply, he]
            exact (iterateFrobeniusEquiv (perfectClosure F E) q n).apply_symm_apply y
          rw [deningerPow_eq_expand q n, Polynomial.map_map, hcomp, Polynomial.map_id,
            ← Polynomial.map_expand, hgexp]
  -- compare the two factorizations
  have hpirr : Irreducible (minpoly (perfectClosure F E) x) := minpoly.irreducible hxL
  have hcombine : h ^ q ^ m = (minpoly (perfectClosure F E) x) ^ k := by rw [hhpow, heq]
  have hdvd : h ∣ minpoly (perfectClosure F E) x := by
    have hd : h ∣ (minpoly (perfectClosure F E) x) ^ k := by
      rw [← hcombine]
      exact dvd_pow_self h (pow_pos hqpos m).ne'
    exact hhirr.prime.dvd_of_dvd_pow hd
  have heqpoly : h = minpoly (perfectClosure F E) x :=
    Polynomial.eq_of_monic_of_associated hhmonic (minpoly.monic hxL)
      (hhirr.associated_of_dvd hpirr hdvd)
  rw [heqpoly] at hcombine
  have hdegpos : 0 < (minpoly (perfectClosure F E) x).natDegree := minpoly.natDegree_pos hxL
  have hd := congrArg Polynomial.natDegree hcombine
  rw [Polynomial.natDegree_pow, Polynomial.natDegree_pow] at hd
  have hkm : q ^ m = k := Nat.eq_of_mul_eq_mul_right hdegpos hd
  exact ⟨m, g, hgsep, hgexp, by rw [heq, hkm]⟩

end RHTower
