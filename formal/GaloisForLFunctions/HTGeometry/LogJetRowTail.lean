import GaloisForLFunctions.HTGeometry.ScaledLogModel

/-!
# Every row of the logarithmic Jacobian sees only the tail above its coordinate

The flag structure of a product law gives the shape of the whole matrix at once, at every order of
the derivation and not just at the first: the logarithmic sum through level `j` lies in the low
subalgebra at `j`, the low subalgebra is stable under the product law, and coordinates above `j`
annihilate it.  Hence

`∂_(j+1) δ^r (logSum Q v (n+2)) = ∂_(j+1) δ^r (logSum Q v (n+2) − logSum Q v (j+1))`

for every `r`.  At the newest coordinate only the newest term of the sum survives, which is the
column the height induction peels.

The derivation laws of the logarithmic factors are recorded here too: the product law differentiates
a logarithmic factor into the Wronskian of the factor against the constant `1`, so the whole first
derivative of the logarithmic sum is a closed form in the same vocabulary.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

variable (Q v : ℕ → Polynomial ℂ)

/-! ## The derivation of a logarithmic factor -/

@[simp] theorem scaledLogWronskian_one_right (p : Polynomial ℂ) :
    scaledLogWronskian p 1 = p.derivative.derivative * p - p.derivative ^ 2 := by
  simp [scaledLogWronskian]

/-- **The product law differentiates a logarithmic factor into a Wronskian.** -/
theorem prodDerivation_logFactor (p : Polynomial ℂ) (k : ℕ) :
    prodDerivation Q v (logFactor p k)
      = fact (scaledLogWronskian p 1) k * prodJet Q v k / fact p k ^ 2 := by
  rcases eq_or_ne p 0 with rfl | hp
  · have h0 : fact (0 : Polynomial ℂ) k = 0 := by
      rw [fact, univFactor]
      simp
    rw [logFactor, h0]
    simp
  · have hne : fact p k ≠ 0 := fact_ne_zero hp k
    rw [logFactor, div_eq_mul_inv, Derivation.leibniz, Derivation.leibniz_inv,
      prodDerivation_fact, prodDerivation_fact]
    simp only [smul_eq_mul, scaledLogWronskian_one_right, fact_sub, fact_mul, fact_pow]
    field_simp
    ring

/-- **The first derivative of the logarithmic sum, in closed form.** -/
theorem prodDerivation_logSum {Q : ℕ → Polynomial ℂ} (v : ℕ → Polynomial ℂ)
    (hQ : ∀ j, Q j ≠ 0) (N : ℕ) :
    prodDerivation Q v (logSum Q v N)
      = ∑ k ∈ Finset.range N,
          (fact (scaledLogWronskian (Q k) 1) k * prodJet Q v k ^ 2 / fact (Q k) k ^ 2
            + logFactor (Q k) k * prodJet Q v k
                * (logSum Q v k + logFactor (v k) k * prodJet Q v k)) := by
  rw [logSum, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Derivation.leibniz, prodDerivation_logFactor, prodDerivation_prodJet hQ]
  simp only [smul_eq_mul]
  ring

/-! ## The flag: the low subalgebra absorbs the sum through its own level -/

/-- **Sharp membership.**  The logarithmic sum through level `m` already lies in the low subalgebra
at `m`: its last term involves the coordinate `m` and no later one. -/
theorem logSum_mem_lowSub_succ {k m : ℕ} (h : k ≤ m + 1) : logSum Q v k ∈ lowSub Q v m := by
  refine Subalgebra.sum_mem _ fun j hj => ?_
  have hjk : j < k := Finset.mem_range.mp hj
  exact Subalgebra.mul_mem _ (logFactorQ_mem_lowSub Q v (by omega))
    (prodJet_mem_lowSub Q v (by omega))

/-- Iterating a derivation is additive. -/
theorem iterate_prodDerivation_sub (r : ℕ) (P R : CascadeField) :
    ((prodDerivation Q v : CascadeField → CascadeField)^[r]) (P - R)
      = ((prodDerivation Q v : CascadeField → CascadeField)^[r]) P
        - ((prodDerivation Q v : CascadeField → CascadeField)^[r]) R := by
  induction r generalizing P R with
  | zero => simp
  | succ r ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
        Function.iterate_succ_apply, map_sub, ih]

/-! ## The row of the logarithmic Jacobian, at every order -/

/-- **Every row sees only the tail above its coordinate.**  This is the shape of the whole matrix:
differentiating any iterate of the logarithmic sum at a coordinate kills everything up to and
including that coordinate's own level. -/
theorem fpderiv_iterate_logSum_tail (r j N : ℕ) :
    fpderiv (j + 1) (((prodDerivation Q v : CascadeField → CascadeField)^[r]) (logSum Q v N))
      = fpderiv (j + 1) (((prodDerivation Q v : CascadeField → CascadeField)^[r])
          (logSum Q v N - logSum Q v (j + 1))) := by
  have hlow : logSum Q v (j + 1) ∈ lowSub Q v j :=
    logSum_mem_lowSub_succ Q v (le_refl (j + 1))
  have hzero : fpderiv (j + 1)
      (((prodDerivation Q v : CascadeField → CascadeField)^[r]) (logSum Q v (j + 1))) = 0 :=
    fpderiv_eq_zero_of_mem_lowSub Q v (by omega) (iterate_prodDerivation_mem_lowSub Q v hlow r)
  rw [iterate_prodDerivation_sub, map_sub, hzero, sub_zero]

/-- **The newest column of the logarithmic Jacobian depends only on the newest term of the sum.** -/
theorem fpderiv_iterate_logSum_newest (r n : ℕ) :
    fpderiv (n + 1)
        (((prodDerivation Q v : CascadeField → CascadeField)^[r]) (logSum Q v (n + 2)))
      = fpderiv (n + 1) (((prodDerivation Q v : CascadeField → CascadeField)^[r])
          (logFactor (Q (n + 1)) (n + 1) * prodJet Q v (n + 1))) := by
  have h := fpderiv_iterate_logSum_tail Q v r n (n + 2)
  rw [h, show n + 2 = (n + 1) + 1 from rfl, logSum_succ]
  congr 2
  ring

end GaloisForLFunctions.HTGeometry
