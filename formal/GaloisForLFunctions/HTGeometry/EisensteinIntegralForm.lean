import GaloisForLFunctions.HTGeometry.EisensteinScaling
import GaloisForLFunctions.HTGeometry.PadicPowerSeriesEvaluation
import Mathlib.RingTheory.Polynomial.ScaleRoots

/-!
# Putting an algebraic power series into integral form

Eisenstein's theorem bounds the denominators of a branch: `D · q^{2N} · y_N` lies in the base ring
for every `N`.  Rescaling by exactly that amount turns the branch into a series with coefficients
in the base ring, and rescaling the defining polynomial to match keeps it integral and monic:

`z = D · y(q² t)`,   `g(t, X) = D^{deg f} · f(q² t, X / D)`,   `g(t, z(t)) = 0`.

Both operations are already in the library — `PowerSeries.rescale` for the variable and
`Polynomial.scaleRoots` for the root — so the content here is that the two match up and that
integrality is preserved.

Together with the lifting lemma along an injective ring homomorphism, this places the whole branch
datum in `ℤ⟦t⟧`, which is exactly the domain of `PadicPowerSeriesEvaluation.padicEval`.
-/

namespace GaloisForLFunctions.HTGeometry

open PowerSeries

variable {K : Type*} [Field K]

/-! ## The rescaled branch and the rescaled polynomial -/

/-- The branch rescaled to have coefficients in the base ring. -/
noncomputable def scaledRoot (D q : K) (y : PowerSeries K) : PowerSeries K :=
  PowerSeries.C D * PowerSeries.rescale (q ^ (2 : ℕ)) y

theorem coeff_scaledRoot (D q : K) (y : PowerSeries K) (N : ℕ) :
    PowerSeries.coeff N (scaledRoot D q y) = D * (q ^ (2 * N) * PowerSeries.coeff N y) := by
  rw [scaledRoot, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale, ← pow_mul]

/-- The polynomial rescaled to match. -/
noncomputable def scaledPoly (D q : K) (f : Polynomial (PowerSeries K)) :
    Polynomial (PowerSeries K) :=
  (f.map (PowerSeries.rescale (q ^ (2 : ℕ)))).scaleRoots (PowerSeries.C D)

/-- **The rescaled branch is a root of the rescaled polynomial.** -/
theorem eval_scaledPoly (D q : K) {f : Polynomial (PowerSeries K)} {y : PowerSeries K}
    (hroot : f.eval y = 0) : (scaledPoly D q f).eval (scaledRoot D q y) = 0 := by
  have hp : (f.map (PowerSeries.rescale (q ^ (2 : ℕ)))).eval (PowerSeries.rescale (q ^ (2 : ℕ)) y) = 0 := by
    rw [← eval_map_of_eval, hroot, map_zero]
  have hsr := Polynomial.scaleRoots_eval₂_mul (R := PowerSeries K) (RingHom.id (PowerSeries K))
    (PowerSeries.rescale (q ^ (2 : ℕ)) y) (PowerSeries.C D)
    (p := f.map (PowerSeries.rescale (q ^ (2 : ℕ))))
  simp only [Polynomial.eval₂_id, RingHom.id_apply] at hsr
  rw [scaledPoly, scaledRoot, hsr, hp, mul_zero]

theorem coeffMem_scaledRoot {A : Subring K} {D q : K} {y : PowerSeries K}
    (h : ∀ N, D * (q ^ (2 * N) * PowerSeries.coeff N y) ∈ A) :
    ∀ N, PowerSeries.coeff N (scaledRoot D q y) ∈ A := by
  intro N
  rw [coeff_scaledRoot]
  exact h N

theorem coeffMem_scaledPoly {A : Subring K} {D q : K} (hD : D ∈ A) (hq : q ∈ A)
    {f : Polynomial (PowerSeries K)} (hf : ∀ i N, PowerSeries.coeff N (f.coeff i) ∈ A) :
    ∀ i N, PowerSeries.coeff N ((scaledPoly D q f).coeff i) ∈ A := by
  intro i N
  rw [scaledPoly, Polynomial.coeff_scaleRoots, Polynomial.coeff_map, ← map_pow,
    mul_comm, PowerSeries.coeff_C_mul, PowerSeries.coeff_rescale]
  exact A.mul_mem (A.pow_mem hD _) (A.mul_mem (A.pow_mem (A.pow_mem hq 2) N) (hf i N))

/-! ## Lifting along an injective ring homomorphism -/

/-- A power series whose coefficients lie in the range of an injective ring homomorphism is the
image of a power series over the source. -/
theorem exists_map_eq_of_coeff_mem_range {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {f : PowerSeries S} (h : ∀ N, PowerSeries.coeff N f ∈ φ.range) :
    ∃ g : PowerSeries R, g.map φ = f := by
  classical
  choose c hc using h
  refine ⟨PowerSeries.mk c, ?_⟩
  ext N
  rw [PowerSeries.coeff_map, PowerSeries.coeff_mk, hc]

/-- The same for a polynomial with power-series coefficients. -/
theorem exists_polyMap_eq_of_coeff_mem_range {R S : Type*} [CommRing R] [CommRing S] (φ : R →+* S)
    {f : Polynomial (PowerSeries S)} (h : ∀ i N, PowerSeries.coeff N (f.coeff i) ∈ φ.range) :
    ∃ g : Polynomial (PowerSeries R), g.map (PowerSeries.map φ) = f := by
  classical
  have hcoeff : ∀ i, ∃ u : PowerSeries R, u.map φ = f.coeff i :=
    fun i => exists_map_eq_of_coeff_mem_range φ (h i)
  choose u hu using hcoeff
  refine ⟨∑ i ∈ Finset.range (f.natDegree + 1), Polynomial.C (u i) * Polynomial.X ^ i, ?_⟩
  ext i
  rw [Polynomial.coeff_map, Polynomial.finsetSum_coeff]
  by_cases hi : i ≤ f.natDegree
  · rw [Finset.sum_eq_single i]
    · rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_pos rfl, mul_one, hu]
    · intro b _ hb
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg (Ne.symm hb), mul_zero]
    · intro hcon
      exact absurd (Finset.mem_range.2 (by omega)) hcon
  · have hsum : (∑ b ∈ Finset.range (f.natDegree + 1),
        (Polynomial.C (u b) * Polynomial.X ^ b).coeff i) = 0 := by
      refine Finset.sum_eq_zero fun b hb => ?_
      have hbd : b < f.natDegree + 1 := Finset.mem_range.1 hb
      have hne : i ≠ b := by omega
      rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, if_neg hne, mul_zero]
    rw [hsum, map_zero, Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]

end GaloisForLFunctions.HTGeometry
