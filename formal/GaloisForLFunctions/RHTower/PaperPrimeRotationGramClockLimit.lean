import GaloisForLFunctions.RHTower.PaperPrimeRotationCompressionDeterminants

/-! # A prime invariant surviving the quadratic compression clock

Along clock `q+1`, the literal window has `(q+1)^2` edges. Every compression
has zero paper ideal cost and tends to zero in operator norm. Its ordinary
Fredholm determinant stays one, but its Gram determinant tends to
`exp((log p)^2)`, an injective invariant of the native prime.
-/

namespace RHTower
noncomputable section
open GaloisForLFunctions.HTGeometry HilbertSchmidt Filter
open scoped Topology

def paperPrimeRotationQuadraticGramValue (p : Nat.Primes) (q : ℕ) : ℂ :=
  fredholmDetOp (lpBasis ℤ)
    ((paperPrimeRotationCompression p (q + 1) ((q + 1) ^ 2)).adjoint ∘L
      paperPrimeRotationCompression p (q + 1) ((q + 1) ^ 2))

def paperPrimeRotationQuadraticGramExponent (p : Nat.Primes) (q : ℕ) : ℝ :=
  ((q : ℝ) + 1) ^ 2 * Real.log (1 + ‖paperPrimeRotationCommutator p (q + 1) 0 1 1 0‖ ^ 2)

def paperPrimeRotationGramLimit (p : Nat.Primes) : ℝ := Real.exp (Real.log p ^ 2)

theorem paperPrimeRotationQuadraticGramExponent_tendsto (p : Nat.Primes) :
    Tendsto (paperPrimeRotationQuadraticGramExponent p) atTop (𝓝 (Real.log p ^ 2)) := by
  have hx : Tendsto (fun q : ℕ => ‖paperPrimeRotationCommutator p (q + 1) 0 1 1 0‖ ^ 2)
      atTop (𝓝 0) := by
    simpa using ((paperPrimeRotationCommutator_tendsto_zero p 0 1 1 0).comp
      (tendsto_add_atTop_nat 1)).norm.pow 2
  have hs : Tendsto (fun q : ℕ => ((q : ℝ) + 1) ^ 2 *
      ‖paperPrimeRotationCommutator p (q + 1) 0 1 1 0‖ ^ 2)
      atTop (𝓝 (Real.log p ^ 2)) := by
    simpa only [mul_pow] using (paperPrimeRotationPrimitive_scaled_norm_tendsto p).pow 2
  have hd : Tendsto (fun q : ℕ => 1 + ‖paperPrimeRotationCommutator p (q + 1) 0 1 1 0‖ ^ 2)
      atTop (𝓝 1) := by simpa using tendsto_const_nhds.add hx
  have hlo := hs.div hd (by norm_num : (1 : ℝ) ≠ 0)
  simp only [div_one] at hlo
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hlo hs
  · intro q
    let x := ‖paperPrimeRotationCommutator p (q + 1) 0 1 1 0‖ ^ 2
    change ((q : ℝ) + 1) ^ 2 * x / (1 + x) ≤
      ((q : ℝ) + 1) ^ 2 * Real.log (1 + x)
    have hx0 : 0 ≤ x := sq_nonneg _
    have hp : 0 < 1 + x := by positivity
    have he : 1 - (1 + x)⁻¹ = x / (1 + x) := by
      field_simp [ne_of_gt hp]
      ring
    have h := mul_le_mul_of_nonneg_left (Real.one_sub_inv_le_log_of_pos hp)
      (sq_nonneg ((q : ℝ) + 1))
    rw [he] at h
    simpa only [mul_div_assoc] using h
  · intro q
    have h := Real.log_le_sub_one_of_pos
      (show 0 < 1 + ‖paperPrimeRotationCommutator p (q + 1) 0 1 1 0‖ ^ 2 by positivity)
    simpa only [paperPrimeRotationQuadraticGramExponent, add_sub_cancel_left] using
      mul_le_mul_of_nonneg_left h (sq_nonneg ((q : ℝ) + 1))

theorem paperPrimeRotationQuadraticGramValue_exact (p : Nat.Primes) (q : ℕ) :
    paperPrimeRotationQuadraticGramValue p q =
      (Real.exp (paperPrimeRotationQuadraticGramExponent p q) : ℂ) := by
  rw [paperPrimeRotationQuadraticGramValue, paperPrimeRotationCompression_gram_fredholmDet]
  have he : paperPrimeRotationQuadraticGramExponent p q =
      (((q + 1) ^ 2 : ℕ) : ℝ) *
        Real.log (1 + ‖paperPrimeRotationCommutator p (q + 1) 0 1 1 0‖ ^ 2) := by
    simp [paperPrimeRotationQuadraticGramExponent]
  rw [he, Real.exp_nat_mul, Real.exp_log (by positivity)]
  push_cast
  rfl

theorem paperPrimeRotationQuadraticGramValue_tendsto (p : Nat.Primes) :
    Tendsto (paperPrimeRotationQuadraticGramValue p) atTop (𝓝 (paperPrimeRotationGramLimit p : ℂ)) := by
  have hr := (Real.continuous_exp.tendsto (Real.log p ^ 2)).comp
    (paperPrimeRotationQuadraticGramExponent_tendsto p)
  have hc := (Complex.continuous_ofReal.tendsto _).comp hr
  exact hc.congr' (Eventually.of_forall fun q => (paperPrimeRotationQuadraticGramValue_exact p q).symm)

theorem paperPrimeRotationQuadraticCompression_tendsto_zero (p : Nat.Primes) :
    Tendsto (fun q : ℕ => paperPrimeRotationCompression p (q + 1) ((q + 1) ^ 2))
      atTop (𝓝 0) := by
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact (paperPrimeRotationCompression_norm_tendsto p (fun q => q ^ 2)).comp
    (tendsto_add_atTop_nat 1)

theorem paperPrimeRotationGramLimit_injective : Function.Injective paperPrimeRotationGramLimit := by
  intro p r h
  have hs : Real.log (p : ℝ) ^ 2 = Real.log (r : ℝ) ^ 2 := Real.exp_injective h
  have hp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.2.one_lt)
  have hr : 0 < Real.log (r : ℝ) := Real.log_pos (by exact_mod_cast r.2.one_lt)
  have hl : Real.log (p : ℝ) = Real.log (r : ℝ) := by nlinarith
  have he : (p : ℝ) = (r : ℝ) := Real.log_injOn_pos
    (by change (0 : ℝ) < (p : ℝ); exact_mod_cast p.2.pos)
    (by change (0 : ℝ) < (r : ℝ); exact_mod_cast r.2.pos) hl
  apply Subtype.ext
  exact_mod_cast he

theorem paperPrimeRotationGramLimit_gt_one (p : Nat.Primes) : 1 < paperPrimeRotationGramLimit p := by
  have hp : 0 < Real.log (p : ℝ) := Real.log_pos (by exact_mod_cast p.2.one_lt)
  exact Real.one_lt_exp_iff.mpr (sq_pos_of_pos hp)

end
end RHTower
