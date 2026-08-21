/-
# The monic scaling of a bivariate polynomial

For `f = ∑_{k ≤ n} a_k Y^k` of degree `n ≥ 1` in `Y`, the polynomial

  `f̂ = Y ^ n + ∑_{k < n} a_k a_n^{n-1-k} Y^k`

is monic in `Y` over the same coefficient ring, and satisfies `f̂(s, a_n(s)·y) = a_n(s)^{n-1} f(s,y)`.
Hence every root `y` of `f(s, ·)` gives a root `a_n(s)·y` of a *monic* integral relation: the scaled
branches are integral over `ℤ[X]`, which is what the germ-integrality argument consumes.
-/
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.GermIntegral

namespace GaloisForLFunctions.HTGeometry.HilbertIrreducibility

open Polynomial

variable {R : Type*} [CommRing R] [Algebra R ℂ]

/-- The monic scaling of `f`. -/
noncomputable def monicScale (f : Polynomial (Polynomial R)) (n : ℕ) :
    Polynomial (Polynomial R) :=
  Polynomial.X ^ n + ∑ k ∈ Finset.range n,
    Polynomial.C (f.coeff k * f.leadingCoeff ^ (n - 1 - k)) * Polynomial.X ^ k

omit [Algebra R ℂ] in
theorem monic_monicScale (f : Polynomial (Polynomial R)) (n : ℕ) : (monicScale f n).Monic := by
  refine Polynomial.monic_X_pow_add ?_
  refine lt_of_le_of_lt (Polynomial.degree_sum_le _ _) ?_
  refine (Finset.sup_lt_iff (by exact_mod_cast WithBot.bot_lt_coe n)).mpr fun k hk => ?_
  have hkn : k < n := Finset.mem_range.mp hk
  refine lt_of_le_of_lt (Polynomial.degree_mul_le _ _) ?_
  calc (Polynomial.C (f.coeff k * f.leadingCoeff ^ (n - 1 - k))).degree
        + ((Polynomial.X : Polynomial (Polynomial R)) ^ k).degree
      ≤ 0 + (k : WithBot ℕ) := add_le_add Polynomial.degree_C_le (Polynomial.degree_X_pow_le k)
    _ = (k : WithBot ℕ) := zero_add _
    _ < (n : WithBot ℕ) := by exact_mod_cast hkn

/-- **The scaling identity.**  `f̂(s, a_n(s)·y) = a_n(s)^{n-1} · f(s, y)`. -/
theorem bivEval_monicScale {f : Polynomial (Polynomial R)} {n : ℕ} (hn : f.natDegree = n)
    (hn1 : 1 ≤ n) (s y : ℂ) :
    bivEval (monicScale f n) s ((Polynomial.aeval s f.leadingCoeff) * y)
      = (Polynomial.aeval s f.leadingCoeff) ^ (n - 1) * bivEval f s y := by
  classical
  set c : ℂ := Polynomial.aeval s f.leadingCoeff with hc
  have hcn : c = Polynomial.aeval s (f.coeff n) := by
    rw [hc, Polynomial.leadingCoeff, hn]
  have hRHS : bivEval f s y
      = ∑ k ∈ Finset.range (n + 1), Polynomial.aeval s (f.coeff k) * y ^ k := by
    rw [bivEval]
    exact Polynomial.eval₂_eq_sum_range' _ (by omega) _
  rw [monicScale, bivEval, Polynomial.eval₂_add, Polynomial.eval₂_X_pow,
    Polynomial.eval₂_finsetSum]
  simp only [Polynomial.eval₂_mul, Polynomial.eval₂_pow, Polynomial.eval₂_C,
    Polynomial.eval₂_X_pow, Polynomial.eval₂_X, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    map_mul, map_pow]
  rw [hRHS, Finset.sum_range_succ, mul_add, Finset.mul_sum]
  have hterm : ∀ k ∈ Finset.range n,
      Polynomial.aeval s (f.coeff k) * (Polynomial.aeval s f.leadingCoeff) ^ (n - 1 - k)
          * (c * y) ^ k
        = c ^ (n - 1) * (Polynomial.aeval s (f.coeff k) * y ^ k) := by
    intro k hk
    have hkn : k < n := Finset.mem_range.mp hk
    have hexp : (n - 1 - k) + k = n - 1 := by omega
    rw [mul_pow, ← hc, show (Polynomial.aeval s (f.coeff k) : ℂ) * c ^ (n - 1 - k) * (c ^ k * y ^ k)
        = (c ^ (n - 1 - k) * c ^ k) * (Polynomial.aeval s (f.coeff k) * y ^ k) from by ring,
      ← pow_add, hexp]
  rw [Finset.sum_congr rfl hterm]
  have hlast : (c * y) ^ n = c ^ (n - 1) * (Polynomial.aeval s (f.coeff n) * y ^ n) := by
    rw [mul_pow, ← hcn]
    have : c ^ n = c ^ (n - 1) * c := by
      rw [← pow_succ]
      congr 1
      omega
    rw [this]
    ring
  rw [hlast]
  ring

end GaloisForLFunctions.HTGeometry.HilbertIrreducibility
