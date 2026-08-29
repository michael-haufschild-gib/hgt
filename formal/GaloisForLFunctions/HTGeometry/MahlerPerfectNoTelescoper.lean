import GaloisForLFunctions.HTGeometry.MahlerIncrementJets
import GaloisForLFunctions.HTGeometry.MahlerRationalNoTelescoper

/-!
# No telescoper in the perfect base

Every element of the perfect base is rational in `w^(1/p^N)` for some `N`, and the Mahler
substitution acts there as the substitution of the level coordinate.  Transporting a putative
telescoper down to that level turns it into a rational solution of a two-term inhomogeneous Mahler
equation, which does not exist unless the resonance vanishes.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped RatFunc

noncomputable section

variable {k : Type*} [Field k]

theorem ratFuncPow_X (q : ℕ) (hq : 0 < q) :
    ratFuncPow q hq (RatFunc.X : RatFunc k) = RatFunc.X ^ q := by
  have hX : (RatFunc.X : RatFunc k)
      = algebraMap (Polynomial k) (RatFunc k) Polynomial.X := (RatFunc.algebraMap_X).symm
  rw [hX, ratFuncPow_algebraMap, ← map_pow]
  congr 1
  rw [polyPow_apply, Polynomial.X_comp]

theorem ratFuncPow_iterate_X (q : ℕ) (hq : 0 < q) (N : ℕ) :
    (ratFuncPow q hq)^[N] (RatFunc.X : RatFunc k) = RatFunc.X ^ (q ^ N) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Function.iterate_succ_apply', ih, map_pow, ratFuncPow_X, ← pow_mul, pow_succ,
        mul_comm]

theorem ratFuncPow_iterate_const (q : ℕ) (hq : 0 < q) (N : ℕ) (c : k) :
    (ratFuncPow q hq)^[N] (algebraMap k (RatFunc k) c) = algebraMap k (RatFunc k) c := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Function.iterate_succ_apply', ih, algebraMap_eq_toRF_C, toRF, ratFuncPow_algebraMap,
        polyPow_C]

/-- The Mahler substitution acts on a level by substituting the level coordinate. -/
theorem mahlerHom_level (p : ℕ) (hp : 1 < p) (N : ℕ) (r : RatFunc k) :
    mahlerHom p (by omega) (ramifiedLevelHom p (by omega) N r)
      = ramifiedLevelHom p (by omega) N (ratFuncPow p (by omega) r) := by
  rw [ramifiedLevelHom_succ p hp N r, mahlerHom_ramifiedLevelHom p hp]

theorem wCoord_eq_level (p : ℕ) (hp : 1 < p) (N : ℕ) :
    ((wCoord (k := k) p hp : perfectBase (k := k) p hp) : HahnSeries ℚ k)
      = ramifiedLevelHom p (by omega) N ((RatFunc.X : RatFunc k) ^ (p ^ N)) := by
  have h := ramifiedLevelHom_add p hp 0 N (RatFunc.X : RatFunc k)
  rw [zero_add, ramifiedLevelHom_zero, ratFuncPow_iterate_X] at h
  exact h

theorem perfectConst_eq_level (p : ℕ) (hp : 1 < p) (N : ℕ) (c : k) :
    ((perfectConst p hp c : perfectBase (k := k) p hp) : HahnSeries ℚ k)
      = ramifiedLevelHom p (by omega) N (algebraMap k (RatFunc k) c) := by
  have h := ramifiedLevelHom_add p hp 0 N (algebraMap k (RatFunc k) c)
  rw [zero_add, ramifiedLevelHom_zero, ratFuncPow_iterate_const, ratFuncToHahn_const] at h
  exact h

theorem ramifiedLevelHom_injective (p : ℕ) (hp : 1 < p) (N : ℕ) :
    Function.Injective (ramifiedLevelHom (k := k) p (by omega) N) :=
  (ramifiedLevelHom p (by omega) N).injective

/-- **No two-term telescoper in the perfect base.** -/
theorem no_perfectBase_telescoper [CharZero k] (p : ℕ) (hp : 1 < p) (m : ℕ)
    (a b : k) (hab : ((p : k)) ^ m * a + b ≠ 0) (z : perfectBase (k := k) p hp) :
    perfectConst p hp (((p : k)) ^ m) * (perfectBaseEquiv p hp z) - z
      ≠ perfectConst p hp a * wCoord p hp + perfectConst p hp b * wCoord p hp ^ p := by
  intro heq
  obtain ⟨N, ζ, hζ⟩ := z.2
  have hval := congrArg (perfectBase (k := k) p hp).subtype heq
  rw [map_sub, map_mul, map_add, map_mul, map_mul, map_pow] at hval
  have hval' : ((perfectConst p hp (((p : k)) ^ m) : perfectBase (k := k) p hp) : HahnSeries ℚ k)
        * ((perfectBaseEquiv p hp z : perfectBase (k := k) p hp) : HahnSeries ℚ k)
        - ((z : perfectBase (k := k) p hp) : HahnSeries ℚ k)
      = ((perfectConst p hp a : perfectBase (k := k) p hp) : HahnSeries ℚ k)
          * ((wCoord (k := k) p hp : perfectBase (k := k) p hp) : HahnSeries ℚ k)
        + ((perfectConst p hp b : perfectBase (k := k) p hp) : HahnSeries ℚ k)
          * (((wCoord (k := k) p hp : perfectBase (k := k) p hp) : HahnSeries ℚ k)) ^ p := hval
  clear hval
  rw [perfectBaseEquiv_coe, ← hζ, mahlerHom_level p hp N, wCoord_eq_level p hp N,
    perfectConst_eq_level p hp N, perfectConst_eq_level p hp N,
    perfectConst_eq_level p hp N, ← map_pow] at hval'
  have hlevel : ramifiedLevelHom p (by omega) N
        (algebraMap k (RatFunc k) (((p : k)) ^ m) * ratFuncPow p (by omega) ζ - ζ)
      = ramifiedLevelHom p (by omega) N
        (algebraMap k (RatFunc k) a * (RatFunc.X : RatFunc k) ^ (p ^ N)
          + algebraMap k (RatFunc k) b * ((RatFunc.X : RatFunc k) ^ (p ^ N)) ^ p) := by
    rw [map_sub, map_mul, map_add, map_mul, map_mul]
    exact hval'
  have hkey := ramifiedLevelHom_injective p hp N hlevel
  have hpk : ((p : k)) ≠ 0 := by
    have : (0 : ℕ) < p := by omega
    exact Nat.cast_ne_zero.mpr this.ne'
  refine no_ratFunc_mahler_solution (k := k) (p := p) (n := N) hp (pow_ne_zero m hpk) hab ζ ?_
  rw [show (((RatFunc.X : RatFunc k) ^ (p ^ N)) ^ p) = (RatFunc.X : RatFunc k) ^ (p ^ (N + 1))
      from by rw [← pow_mul, ← pow_succ]] at hkey
  have e1 : algebraMap (Polynomial k) (RatFunc k) (Polynomial.C (((p : k)) ^ m))
      = algebraMap k (RatFunc k) (((p : k)) ^ m) := RatFunc.algebraMap_C _
  have e2 : algebraMap (Polynomial k) (RatFunc k)
        (Polynomial.C a * Polynomial.X ^ (p ^ N) + Polynomial.C b * Polynomial.X ^ (p ^ (N + 1)))
      = algebraMap k (RatFunc k) a * (RatFunc.X : RatFunc k) ^ (p ^ N)
        + algebraMap k (RatFunc k) b * (RatFunc.X : RatFunc k) ^ (p ^ (N + 1)) := by
    rw [map_add, map_mul, map_mul, map_pow, map_pow, RatFunc.algebraMap_X,
      RatFunc.algebraMap_C, RatFunc.algebraMap_C]
    rfl
  rw [e1, e2]
  exact hkey

end

end GaloisForLFunctions.HTGeometry
