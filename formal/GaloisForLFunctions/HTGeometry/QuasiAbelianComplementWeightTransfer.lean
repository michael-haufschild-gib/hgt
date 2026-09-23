import GaloisForLFunctions.HTGeometry.QuasiAbelianScaledFlatSeedDamping

/-!
# Transferring a seed bound to the complement index

The damped seed bound is indexed by the ambient coordinates `Fin d`, through the real vector the
complement realizes; the Poincaré majorant is indexed by the complement `Fin c`.  Two properties of
the complement convert one into the other: uniform discreteness turns the ambient Gaussian into a
Gaussian in the index, and boundedness turns the ambient polynomial factor into a polynomial in the
index.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The Weierstrass product inequality. -/
theorem one_add_sum_le_prod_one_add {ι : Type*} (s : Finset ι) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) : 1 + ∑ i ∈ s, a i ≤ ∏ i ∈ s, (1 + a i) := by
  classical
  refine Finset.induction_on s (by simp) ?_
  intro i s hi ih
  rw [Finset.sum_insert hi, Finset.prod_insert hi]
  have hprod : (1 : ℝ) ≤ ∏ j ∈ s, (1 + a j) := by
    calc (1 : ℝ) = ∏ _j ∈ s, (1 : ℝ) := by simp
      _ ≤ ∏ j ∈ s, (1 + a j) :=
        Finset.prod_le_prod (fun j _ => zero_le_one) (fun j _ => by linarith [ha j])
  nlinarith [ha i, ih, hprod]

/-- A bounded linear image is dominated by the product of the index factors. -/
theorem one_add_lin_sum_le {c : ℕ} {lin : ℝ} (hlin : 0 ≤ lin) (z : Fin c → ℤ) :
    1 + lin * ∑ j, |((z j : ℤ) : ℝ)| ≤ (1 + lin) * ∏ j, (1 + |((z j : ℤ) : ℝ)|) := by
  have hsum := one_add_sum_le_prod_one_add (Finset.univ : Finset (Fin c))
    (fun j => |((z j : ℤ) : ℝ)|) (fun j => abs_nonneg _)
  have hprod1 : (1 : ℝ) ≤ ∏ j, (1 + |((z j : ℤ) : ℝ)|) := by
    calc (1 : ℝ) = ∏ _j : Fin c, (1 : ℝ) := by simp
      _ ≤ ∏ j, (1 + |((z j : ℤ) : ℝ)|) :=
        Finset.prod_le_prod (fun j _ => zero_le_one)
          (fun j _ => by linarith [abs_nonneg ((z j : ℤ) : ℝ)])
  nlinarith [hsum, hprod1, hlin]

/-- **The complement transfer.**  A bound indexed by the ambient coordinates becomes a
polynomial-Gaussian bound indexed by the complement. -/
theorem prod_mul_exp_le_polynomialGaussianLatticeWeight {c d : ℕ}
    (vec : (Fin c → ℤ) → Fin d → ℝ) (deg : Fin d → ℕ)
    {kappa lin eps : ℝ} (hlin : 0 ≤ lin) (heps : 0 ≤ eps)
    (hdiscrete : ∀ z : Fin c → ℤ, kappa * ∑ j, (((z j : ℤ) : ℝ)) ^ (2 : ℕ) ≤ ∑ i, (vec z i) ^ (2 : ℕ))
    (hbounded : ∀ (z : Fin c → ℤ) (i : Fin d), |vec z i| ≤ lin * ∑ j, |((z j : ℤ) : ℝ)|)
    (z : Fin c → ℤ) :
    (∏ i, (1 + |vec z i|) ^ (deg i)) * Real.exp (-(eps * ∑ i, (vec z i) ^ (2 : ℕ)))
      ≤ (1 + lin) ^ (∑ i, deg i)
        * polynomialGaussianLatticeWeight (Fin c) (fun _ => ∑ i, deg i)
            (fun _ => eps * kappa) z := by
  classical
  set S : ℝ := ∑ j, |((z j : ℤ) : ℝ)| with hS
  set Q : ℝ := ∏ j, (1 + |((z j : ℤ) : ℝ)|) with hQ
  have hQ1 : (1 : ℝ) ≤ Q := by
    rw [hQ]
    calc (1 : ℝ) = ∏ _j : Fin c, (1 : ℝ) := by simp
      _ ≤ ∏ j, (1 + |((z j : ℤ) : ℝ)|) :=
        Finset.prod_le_prod (fun j _ => zero_le_one)
          (fun j _ => by linarith [abs_nonneg ((z j : ℤ) : ℝ)])
  -- the polynomial factor
  have hpoly : (∏ i, (1 + |vec z i|) ^ (deg i)) ≤ ((1 + lin) * Q) ^ (∑ i, deg i) := by
    have hstep : ∀ i : Fin d, 1 + |vec z i| ≤ (1 + lin) * Q := by
      intro i
      have h1 : 1 + |vec z i| ≤ 1 + lin * S := by
        have hb := hbounded z i
        rw [hS]
        linarith
      have h2 : 1 + lin * S ≤ (1 + lin) * Q := one_add_lin_sum_le hlin z
      linarith
    calc (∏ i, (1 + |vec z i|) ^ (deg i))
        ≤ ∏ i, ((1 + lin) * Q) ^ (deg i) :=
          Finset.prod_le_prod (fun i _ => by positivity)
            (fun i _ => pow_le_pow_left₀ (by positivity) (hstep i) _)
      _ = ((1 + lin) * Q) ^ (∑ i, deg i) := by rw [← Finset.prod_pow_eq_pow_sum]
  -- the Gaussian factor
  have hgauss : Real.exp (-(eps * ∑ i, (vec z i) ^ (2 : ℕ)))
      ≤ Real.exp (-(eps * kappa * ∑ j, (((z j : ℤ) : ℝ)) ^ (2 : ℕ))) := by
    refine Real.exp_le_exp.mpr ?_
    have := hdiscrete z
    nlinarith [heps]
  have hweight : polynomialGaussianLatticeWeight (Fin c) (fun _ => ∑ i, deg i)
      (fun _ => eps * kappa) z
      = Q ^ (∑ i, deg i) * Real.exp (-(eps * kappa * ∑ j, (((z j : ℤ) : ℝ)) ^ (2 : ℕ))) := by
    rw [polynomialGaussianLatticeWeight_eq, hQ]
    congr 1
    · rw [← Finset.prod_pow]
      refine Finset.prod_congr rfl fun j _ => ?_
      congr 2
      rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
    · congr 1
      rw [← Finset.mul_sum]
  rw [hweight]
  have hpolynn : (0 : ℝ) ≤ ∏ i, (1 + |vec z i|) ^ (deg i) :=
    Finset.prod_nonneg fun i _ => by positivity
  calc (∏ i, (1 + |vec z i|) ^ (deg i)) * Real.exp (-(eps * ∑ i, (vec z i) ^ (2 : ℕ)))
      ≤ ((1 + lin) * Q) ^ (∑ i, deg i)
        * Real.exp (-(eps * kappa * ∑ j, (((z j : ℤ) : ℝ)) ^ (2 : ℕ))) :=
        mul_le_mul hpoly hgauss (Real.exp_pos _).le (by positivity)
    _ = (1 + lin) ^ (∑ i, deg i)
        * (Q ^ (∑ i, deg i) * Real.exp (-(eps * kappa * ∑ j, (((z j : ℤ) : ℝ)) ^ (2 : ℕ)))) := by
        rw [mul_pow]; ring

end

end GaloisForLFunctions.HTGeometry
