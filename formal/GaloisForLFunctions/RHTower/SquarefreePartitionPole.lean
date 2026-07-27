import GaloisForLFunctions.RHTower.MobiusCoMovingDiffuseCodiagonal

/-!
# The critical pole scaling of the squarefree partition

The squarefree partition function `Z(σ) = ∑_d μ(d)² d^(-σ) = ζ(σ)/ζ(2σ)` has a simple pole at
`σ = 1` with residue `1/ζ(2)`.  The corpus records this in reciprocal form; here it is stated
directly, with the closed real value:

```text
(σ - 1) Z(σ) → 1/ζ(2) = 6/π²      (σ → 1+).
```

Together with the already proved first logarithmic moment scaling `(σ-1) m_σ → 1` this is the
critical pole normalisation used by the damped orbit computations.
-/

open Filter Topology

namespace RHTower

/-- The real part of `ζ(2)` is `π²/6`. -/
theorem re_riemannZeta_two : (riemannZeta (2 : ℂ)).re = Real.pi ^ 2 / 6 := by
  rw [riemannZeta_two]
  rw [show ((Real.pi : ℂ) ^ 2 / 6) = (((Real.pi ^ 2 / 6 : ℝ)) : ℂ) by push_cast; ring]
  exact Complex.ofReal_re _

/-- **Critical pole scaling of the squarefree partition.**  `(σ-1) Z(σ) → 6/π²` as `σ ↓ 1`. -/
theorem tendsto_sub_one_mul_squarefreeMobiusTotal :
    Tendsto (fun sigma : ℝ => (sigma - 1) * squarefreeMobiusTotal sigma)
      (nhdsWithin 1 (Set.Ioi 1)) (nhds (6 / Real.pi ^ 2)) := by
  have hbase := tendsto_inv_squarefreeMobiusTotal_div_sub_one
  rw [re_riemannZeta_two] at hbase
  have hne : (Real.pi ^ 2 / 6 : ℝ) ≠ 0 := by
    have := Real.pi_pos
    positivity
  have hinv := hbase.inv₀ hne
  have hval : ((Real.pi ^ 2 / 6 : ℝ))⁻¹ = 6 / Real.pi ^ 2 := by
    rw [inv_div]
  rw [hval] at hinv
  refine hinv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with sigma hsigma
  have hgt : (1 : ℝ) < sigma := hsigma
  have hpos : 0 < squarefreeMobiusTotal sigma := squarefreeMobiusTotal_pos hgt
  have hsub : (0 : ℝ) < sigma - 1 := by linarith
  field_simp

end RHTower
