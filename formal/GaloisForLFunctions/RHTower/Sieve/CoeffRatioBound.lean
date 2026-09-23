import GaloisForLFunctions.RHTower.Sieve.CoeffMajorantProd

/-!
# The majorant at the chosen width, in the variable `v`

Assembling the four steps — monotone in `t`, monotone in the constants, scale the constants out,
bound the sum by a product — turns the majorant times the saving into exactly the shape
`tendsto_poly_exp_two_sub_sq` handles.
-/

namespace RHTower.Sieve

open Filter Topology Real

/-- **The majorant times the saving, in the variable `v`.** -/
theorem coeffMajorant_ratio_le {C C' M₀ a κ v t L : ℝ}
    (hC : 0 ≤ C) (hC' : 0 ≤ C') (hM₀ : 0 ≤ M₀) (ha : 0 ≤ a) (hκ : 0 ≤ κ)
    (hv : 0 ≤ v) (ht0 : 0 ≤ t) (htlo : v ^ (2 : ℕ) ≤ t) (hthi : t ≤ 2 * v ^ (2 : ℕ))
    (hL : L + 2 ≤ 3 * Real.exp v) (hL0 : 0 ≤ L + 2) :
    coeffMajorant (C * (L + 2) ^ (2 : ℕ)) (C' * (L + 2)) M₀ a t * Real.exp (-(κ * t))
      ≤ (1 + (512 * a) * (v ^ (2 : ℕ)) ^ (9 : ℕ))
          * ((8 * (9 * C) * Real.exp (22 / 4)
                + (8 * (3 * C') + 4 + 2 * (9 * C)) * (2 * Real.exp (22 / 4)) * (5 / 2)
                + M₀ * (4 + 2 * (9 * C)))
              + ((8 * (3 * C') + 4 + 2 * (9 * C)) * (2 * Real.exp (22 / 4)) * 4) * v ^ (2 : ℕ))
          * Real.exp (2 * v) * Real.exp (-(κ * v ^ (2 : ℕ))) := by
  have hE : (1 : ℝ) ≤ Real.exp (2 * v) := Real.one_le_exp (by linarith)
  have hEv : Real.exp v ≤ Real.exp (2 * v) := Real.exp_le_exp.2 (by linarith)
  have hĈ : (0 : ℝ) ≤ C * (L + 2) ^ (2 : ℕ) := by positivity
  have hĈ' : (0 : ℝ) ≤ C' * (L + 2) := by positivity
  have hv2 : (0 : ℝ) ≤ v ^ (2 : ℕ) := by positivity
  -- step one: move the variable to `2v²`
  have h1 : coeffMajorant (C * (L + 2) ^ (2 : ℕ)) (C' * (L + 2)) M₀ a t
      ≤ coeffMajorant (C * (L + 2) ^ (2 : ℕ)) (C' * (L + 2)) M₀ a (2 * v ^ (2 : ℕ)) :=
    coeffMajorant_mono_t hĈ hĈ' ha ht0 hthi
  -- step two: bound the constants
  have hsq : (L + 2) ^ (2 : ℕ) ≤ 9 * Real.exp (2 * v) := by
    have hexp : (0 : ℝ) < Real.exp v := Real.exp_pos v
    have hsq' : (L + 2) ^ (2 : ℕ) ≤ (3 * Real.exp v) ^ (2 : ℕ) := by
      exact pow_le_pow_left₀ hL0 hL 2
    have hrw : (3 * Real.exp v) ^ (2 : ℕ) = 9 * Real.exp (2 * v) := by
      rw [mul_pow, pow_two (Real.exp v), ← Real.exp_add, show v + v = 2 * v by ring]
      norm_num
    rw [hrw] at hsq'
    exact hsq'
  have hcst : C * (L + 2) ^ (2 : ℕ) ≤ 9 * C * Real.exp (2 * v) := by nlinarith [hsq, hC]
  have hcst' : C' * (L + 2) ≤ 3 * C' * Real.exp (2 * v) := by
    have hL3 : L + 2 ≤ 3 * Real.exp (2 * v) := by linarith
    nlinarith [hL3, hC']
  have h2 : coeffMajorant (C * (L + 2) ^ (2 : ℕ)) (C' * (L + 2)) M₀ a (2 * v ^ (2 : ℕ))
      ≤ coeffMajorant ((9 * C) * Real.exp (2 * v)) ((3 * C') * Real.exp (2 * v)) M₀ a
          (2 * v ^ (2 : ℕ)) :=
    coeffMajorant_mono_const (by linarith) (by linarith) hM₀ ha (by linarith)
  -- step three: pull the scale out
  have h3 : coeffMajorant ((9 * C) * Real.exp (2 * v)) ((3 * C') * Real.exp (2 * v)) M₀ a
      (2 * v ^ (2 : ℕ))
      ≤ Real.exp (2 * v) * coeffMajorant (9 * C) (3 * C') M₀ a (2 * v ^ (2 : ℕ)) :=
    coeffMajorant_scale hE hM₀ ha (by linarith)
  -- step four: bound the sum by a product
  have h4 := coeffMajorant_le_prod (C := 9 * C) (C' := 3 * C') (M₀ := M₀) (a := a) (w := v ^ (2 : ℕ))
    (by linarith) hM₀ ha hv2
  -- the saving
  have h5 : Real.exp (-(κ * t)) ≤ Real.exp (-(κ * v ^ (2 : ℕ))) := by
    refine Real.exp_le_exp.2 ?_
    nlinarith [hκ, htlo]
  have hSpos : (0 : ℝ) < Real.exp (-(κ * t)) := Real.exp_pos _
  have hchain : coeffMajorant (C * (L + 2) ^ (2 : ℕ)) (C' * (L + 2)) M₀ a t
      ≤ Real.exp (2 * v)
          * ((1 + (512 * a) * (v ^ (2 : ℕ)) ^ (9 : ℕ))
              * ((8 * (9 * C) * Real.exp (22 / 4)
                    + (8 * (3 * C') + 4 + 2 * (9 * C)) * (2 * Real.exp (22 / 4)) * (5 / 2)
                    + M₀ * (4 + 2 * (9 * C)))
                  + ((8 * (3 * C') + 4 + 2 * (9 * C)) * (2 * Real.exp (22 / 4)) * 4)
                      * v ^ (2 : ℕ))) := by
    refine le_trans h1 (le_trans h2 (le_trans h3 ?_))
    exact mul_le_mul_of_nonneg_left h4 (by linarith)
  have hprod0 : (0 : ℝ) ≤ Real.exp (2 * v)
      * ((1 + (512 * a) * (v ^ (2 : ℕ)) ^ (9 : ℕ))
          * ((8 * (9 * C) * Real.exp (22 / 4)
                + (8 * (3 * C') + 4 + 2 * (9 * C)) * (2 * Real.exp (22 / 4)) * (5 / 2)
                + M₀ * (4 + 2 * (9 * C)))
              + ((8 * (3 * C') + 4 + 2 * (9 * C)) * (2 * Real.exp (22 / 4)) * 4) * v ^ (2 : ℕ))) := by
    positivity
  calc coeffMajorant (C * (L + 2) ^ (2 : ℕ)) (C' * (L + 2)) M₀ a t * Real.exp (-(κ * t))
      ≤ (Real.exp (2 * v)
          * ((1 + (512 * a) * (v ^ (2 : ℕ)) ^ (9 : ℕ))
              * ((8 * (9 * C) * Real.exp (22 / 4)
                    + (8 * (3 * C') + 4 + 2 * (9 * C)) * (2 * Real.exp (22 / 4)) * (5 / 2)
                    + M₀ * (4 + 2 * (9 * C)))
                  + ((8 * (3 * C') + 4 + 2 * (9 * C)) * (2 * Real.exp (22 / 4)) * 4) * v ^ (2 : ℕ))))
          * Real.exp (-(κ * t)) := mul_le_mul_of_nonneg_right hchain hSpos.le
    _ ≤ (Real.exp (2 * v)
          * ((1 + (512 * a) * (v ^ (2 : ℕ)) ^ (9 : ℕ))
              * ((8 * (9 * C) * Real.exp (22 / 4)
                    + (8 * (3 * C') + 4 + 2 * (9 * C)) * (2 * Real.exp (22 / 4)) * (5 / 2)
                    + M₀ * (4 + 2 * (9 * C)))
                  + ((8 * (3 * C') + 4 + 2 * (9 * C)) * (2 * Real.exp (22 / 4)) * 4) * v ^ (2 : ℕ))))
          * Real.exp (-(κ * v ^ (2 : ℕ))) := mul_le_mul_of_nonneg_left h5 hprod0
    _ = _ := by ring

end RHTower.Sieve
