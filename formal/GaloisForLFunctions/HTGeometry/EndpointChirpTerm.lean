import GaloisForLFunctions.HTGeometry.EndpointChirpGlue
import GaloisForLFunctions.HTGeometry.FactorialSlopeCoeffRatio

/-!
# An endpoint term is a chirp

For a sequence with a complex factorial slope, the endpoint contribution of the jet `j` at the
forward shift `u`,

`C · (M+u)_j · a_{M+u} / a_M`,

is exactly a chirp of real exponent `j + (Re α)u` and integer frequency `u`, times a factor tending
to one:

`= chirpTerm (Im α) (j + (Re α)u) u (C Λ^u α^{αu}) (log M) · ε(M)`,   `ε → 1`.

The identity is exact for every `M ≥ 1` with `a_M ≠ 0`; the whole asymptotic content sits in the
explicit factor `ε`, which is the product of the fixed-shift coefficient ratio `(3)` and the
descending-factorial weight.  Splitting `M^w` into `e^{(Re w) log M}` and the unimodular
`e^{i (Im w) log M}` is the only place a complex power is opened.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Splitting a complex power of a natural number -/

/-- **A complex power of a positive integer is a chirp.** -/
theorem natCast_cpow_eq_chirp (w : ℂ) {M : ℕ} (hM : 1 ≤ M) :
    (M : ℂ) ^ w = ((Real.exp (w.re * Real.log M) : ℝ) : ℂ)
      * Complex.exp (((w.im * Real.log M : ℝ)) * Complex.I) := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hMne : (M : ℂ) ≠ 0 := by simpa using ne_of_gt hMpos
  have hlog : Complex.log (M : ℂ) = ((Real.log M : ℝ) : ℂ) := by
    rw [show ((M : ℂ)) = (((M : ℝ)) : ℂ) from by push_cast; ring]
    exact log_ofReal_of_pos hMpos
  rw [Complex.cpow_def_of_ne_zero hMne, hlog]
  have hval : ((Real.log M : ℝ) : ℂ) * w
      = ((w.re * Real.log M : ℝ) : ℂ) + ((w.im * Real.log M : ℝ) : ℂ) * Complex.I := by
    apply Complex.ext <;> simp <;> ring
  rw [hval, Complex.exp_add, Complex.ofReal_exp]

/-! ## The endpoint term -/

variable {a : ℕ → ℂ} {α Λ Cc : ℂ} {c : ℝ}

/-- The explicit vanishing factor of an endpoint term. -/
def slopeShiftDefect (a : ℕ → ℂ) (α Λ : ℂ) (u j : ℕ) (M : ℕ) : ℂ :=
  (a (M + u) / (a M * (Λ ^ u * (α ^ (α * (u : ℂ)) * (M : ℂ) ^ (α * (u : ℂ))))))
    * ((((M + u).descFactorial j : ℕ) : ℂ) / ((M : ℂ) ^ j))

theorem tendsto_slopeShiftDefect (hyp : FactorialSlope a α Λ Cc c) (u j : ℕ) :
    Tendsto (slopeShiftDefect a α Λ u j) atTop (𝓝 1) := by
  have h1 := tendsto_coeff_shift_ratio_split hyp u
  have h2 := tendsto_descFactorial_div_pow_endpointChirpGlue u j
  have := h1.mul h2
  rw [one_mul] at this
  refine this.congr fun M => ?_
  rw [slopeShiftDefect]

/-- **An endpoint term is a chirp.** -/
theorem endpoint_term_eq_chirp (hyp : FactorialSlope a α Λ Cc c) (u j : ℕ) (C : ℂ)
    {M : ℕ} (hM : 1 ≤ M) (haM : a M ≠ 0) :
    C * ((((M + u).descFactorial j : ℕ) : ℂ) * a (M + u)) / a M
      = chirpTerm α.im ((j : ℝ) + α.re * (u : ℝ)) (u : ℤ)
          (C * Λ ^ u * α ^ (α * (u : ℂ))) (Real.log M)
        * slopeShiftDefect a α Λ u j M := by
  have hMpos : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  have hMne : (M : ℂ) ≠ 0 := by simpa using ne_of_gt hMpos
  have hre := hyp.re_pos
  have hα : α ≠ 0 := by
    intro hc
    rw [hc] at hre
    simp at hre
  have hlam := hyp.lam_ne
  have hlamu : Λ ^ u ≠ 0 := pow_ne_zero _ hlam
  have hαu : α ^ (α * (u : ℂ)) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hα]
    exact Complex.exp_ne_zero _
  have hMu : (M : ℂ) ^ (α * (u : ℂ)) ≠ 0 := by
    rw [Complex.cpow_def_of_ne_zero hMne]
    exact Complex.exp_ne_zero _
  have hMj : (M : ℂ) ^ j ≠ 0 := pow_ne_zero _ hMne
  -- the chirp is the complex power
  have hw : ((((j : ℝ) : ℂ) + α * (u : ℂ)).re) = (j : ℝ) + α.re * (u : ℝ) := by
    simp [Complex.add_re, Complex.mul_re]
  have hwim : ((((j : ℝ) : ℂ) + α * (u : ℂ)).im) = α.im * (u : ℝ) := by
    simp [Complex.add_im, Complex.mul_im]
  have hpow : (M : ℂ) ^ (((j : ℝ) : ℂ) + α * (u : ℂ))
      = (M : ℂ) ^ j * (M : ℂ) ^ (α * (u : ℂ)) := by
    rw [Complex.cpow_add _ _ hMne]
    congr 1
    rw [show (((j : ℝ) : ℂ)) = ((j : ℕ) : ℂ) from by push_cast; ring, Complex.cpow_natCast]
  have hcast : ((u : ℤ) : ℝ) = (u : ℝ) := by push_cast; ring
  rw [chirpTerm, slopeShiftDefect, hcast]
  set E : ℂ := ((Real.exp (((j : ℝ) + α.re * (u : ℝ)) * Real.log M) : ℝ) : ℂ) with hE
  set U : ℂ := Complex.exp (((α.im * (u : ℝ) * Real.log M : ℝ)) * Complex.I) with hU
  have hEU : E * U = (M : ℂ) ^ j * (M : ℂ) ^ (α * (u : ℂ)) := by
    have h1 : (M : ℂ) ^ (((j : ℝ) : ℂ) + α * (u : ℂ)) = E * U := by
      rw [hE, hU, natCast_cpow_eq_chirp _ hM, hw, hwim]
    rw [← h1, hpow]
  have hgroup : C * Λ ^ u * α ^ (α * (u : ℂ)) * E * U
      * (a (M + u) / (a M * (Λ ^ u * (α ^ (α * (u : ℂ)) * (M : ℂ) ^ (α * (u : ℂ)))))
        * ((((M + u).descFactorial j : ℕ) : ℂ) / ((M : ℂ) ^ j)))
      = (C * Λ ^ u * α ^ (α * (u : ℂ))) * (E * U)
        * (a (M + u) / (a M * (Λ ^ u * (α ^ (α * (u : ℂ)) * (M : ℂ) ^ (α * (u : ℂ)))))
          * ((((M + u).descFactorial j : ℕ) : ℂ) / ((M : ℂ) ^ j))) := by ring
  rw [hgroup, hEU]
  field_simp

end

end GaloisForLFunctions.HTGeometry
