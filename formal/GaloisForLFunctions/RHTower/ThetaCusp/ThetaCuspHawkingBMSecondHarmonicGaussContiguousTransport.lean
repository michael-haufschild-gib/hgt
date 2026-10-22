import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMSecondHarmonicComplementaryHypergeometric

/-!
# Gauss-summation contiguous transport

Simultaneous hypergeometric parameter shifts `(b,c) -> (b+1,c+1)` and
`(a,c) -> (a+1,c+1)` preserve `c-a-b`. Their coefficient differences are exact coboundaries.
Finite sums therefore telescope to one boundary term; convergent endpoint sums transport whenever
that term tends to zero. This is algebraic infrastructure for moving BM parameters into an Euler
integral chamber without parameter-space analytic continuation.
-/

open Complex Nat Polynomial Filter Topology

namespace RHTower

noncomputable section

theorem ascPochhammer_eval_add_one_transport
    (x : ℂ) (j : ℕ) :
    x * (ascPochhammer ℂ j).eval (x + 1) =
      (x + (j : ℂ)) * (ascPochhammer ℂ j).eval x := by
  calc
    x * (ascPochhammer ℂ j).eval (x + 1) =
        (ascPochhammer ℂ (j + 1)).eval x := by
      rw [ascPochhammer_succ_left, eval_mul, eval_X,
        eval_comp, eval_add, eval_X, eval_one]
    _ = (ascPochhammer ℂ j).eval x * (x + (j : ℂ)) := by
      exact ascPochhammer_succ_eval j x
    _ = _ := by ring

theorem ordinaryHypergeometricCoefficient_shift_b_c_transport
    (a b c : ℂ) (j : ℕ)
    (hpc : (ascPochhammer ℂ j).eval c ≠ 0)
    (hcj : c + (j : ℂ) ≠ 0) :
    c * (b + (j : ℂ)) *
        ordinaryHypergeometricCoefficient a b c j =
      b * (c + (j : ℂ)) *
        ordinaryHypergeometricCoefficient a (b + 1) (c + 1) j := by
  have hbshift := ascPochhammer_eval_add_one_transport b j
  have hcshift := ascPochhammer_eval_add_one_transport c j
  have hpcshift : (ascPochhammer ℂ j).eval (c + 1) ≠ 0 := by
    intro h
    apply hcj
    apply mul_right_cancel₀ hpc
    calc
      (c + (j : ℂ)) * (ascPochhammer ℂ j).eval c =
          c * (ascPochhammer ℂ j).eval (c + 1) := hcshift.symm
      _ = 0 := by rw [h, mul_zero]
      _ = 0 * (ascPochhammer ℂ j).eval c := by rw [zero_mul]
  have hbase :
      c * (b + (j : ℂ)) * (ascPochhammer ℂ j).eval b *
          ((ascPochhammer ℂ j).eval c)⁻¹ =
        b * (c + (j : ℂ)) * (ascPochhammer ℂ j).eval (b + 1) *
          ((ascPochhammer ℂ j).eval (c + 1))⁻¹ := by
    field_simp [hpc, hpcshift]
    linear_combination
      -c * (ascPochhammer ℂ j).eval (c + 1) * hbshift +
        b * (ascPochhammer ℂ j).eval (b + 1) * hcshift
  simp only [ordinaryHypergeometricCoefficient]
  calc
    c * (b + (j : ℂ)) *
          ((j ! : ℂ)⁻¹ * (ascPochhammer ℂ j).eval a *
            (ascPochhammer ℂ j).eval b * ((ascPochhammer ℂ j).eval c)⁻¹) =
        ((j ! : ℂ)⁻¹ * (ascPochhammer ℂ j).eval a) *
          (c * (b + (j : ℂ)) * (ascPochhammer ℂ j).eval b *
            ((ascPochhammer ℂ j).eval c)⁻¹) := by ring
    _ = ((j ! : ℂ)⁻¹ * (ascPochhammer ℂ j).eval a) *
          (b * (c + (j : ℂ)) * (ascPochhammer ℂ j).eval (b + 1) *
            ((ascPochhammer ℂ j).eval (c + 1))⁻¹) := by rw [hbase]
    _ = b * (c + (j : ℂ)) *
          ((j ! : ℂ)⁻¹ * (ascPochhammer ℂ j).eval a *
            (ascPochhammer ℂ j).eval (b + 1) *
              ((ascPochhammer ℂ j).eval (c + 1))⁻¹) := by ring

private theorem gaussShiftCoboundary_of_transport_recurrence
    (a b c J T U V : ℂ) (hb : b ≠ 0) (hc : c ≠ 0)
    (hcJ : c + J ≠ 0)
    (hshift : c * (b + J) * T = b * (c + J) * U)
    (hrec : (J + 1) * (c + J) * V = (a + J) * (b + J) * T) :
    (c - a) / c * U - T = J / b * T - (J + 1) / b * V := by
  have hbcJ : b * (c + J) ≠ 0 := mul_ne_zero hb hcJ
  have hU : U = c * (b + J) * T / (b * (c + J)) := by
    apply (eq_div_iff hbcJ).2
    linear_combination -hshift
  have hJV : (J + 1) * V = (a + J) * (b + J) * T / (c + J) := by
    apply (eq_div_iff hcJ).2
    linear_combination hrec
  rw [hU, show (J + 1) / b * V = ((J + 1) * V) / b by ring, hJV]
  field_simp [hb, hc, hcJ]
  ring

/-- One simultaneous `(b,c) -> (b+1,c+1)` shift is an exact coefficient coboundary. -/
theorem ordinaryHypergeometricCoefficient_shift_b_c_coboundary
    (a b c : ℂ) (j : ℕ)
    (hb : b ≠ 0) (hc : c ≠ 0)
    (hpc : (ascPochhammer ℂ j).eval c ≠ 0)
    (hcj : c + (j : ℂ) ≠ 0) :
    (c - a) / c * ordinaryHypergeometricCoefficient a (b + 1) (c + 1) j -
        ordinaryHypergeometricCoefficient a b c j =
      (j : ℂ) / b * ordinaryHypergeometricCoefficient a b c j -
        ((j + 1 : ℕ) : ℂ) / b *
          ordinaryHypergeometricCoefficient a b c (j + 1) := by
  have hshift := ordinaryHypergeometricCoefficient_shift_b_c_transport
    a b c j hpc hcj
  have hrec := ordinaryHypergeometricCoefficient_succ_recurrence
    a b c j hpc hcj
  simpa only [Nat.cast_add, Nat.cast_one] using
    gaussShiftCoboundary_of_transport_recurrence
    a b c (j : ℂ)
    (ordinaryHypergeometricCoefficient a b c j)
    (ordinaryHypergeometricCoefficient a (b + 1) (c + 1) j)
      (ordinaryHypergeometricCoefficient a b c (j + 1)) hb hc hcj hshift
      (by simpa only [Nat.cast_add, Nat.cast_one] using hrec)

/-- Finite Gauss transport: simultaneous parameter shift telescopes to one boundary term. -/
theorem ordinaryHypergeometricCoefficient_sum_shift_b_c
    (a b c : ℂ) (N : ℕ) (hb : b ≠ 0)
    (hcavoid : ∀ k : ℕ, (k : ℂ) ≠ -c) :
    (c - a) / c *
          (∑ j ∈ Finset.range N,
            ordinaryHypergeometricCoefficient a (b + 1) (c + 1) j) -
        ∑ j ∈ Finset.range N, ordinaryHypergeometricCoefficient a b c j =
      -((N : ℂ) / b * ordinaryHypergeometricCoefficient a b c N) := by
  have hc : c ≠ 0 := by
    intro hc0
    apply hcavoid 0
    simp [hc0]
  let f : ℕ → ℂ := fun j =>
    (j : ℂ) / b * ordinaryHypergeometricCoefficient a b c j
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  calc
    (∑ j ∈ Finset.range N,
        ((c - a) / c * ordinaryHypergeometricCoefficient a (b + 1) (c + 1) j -
          ordinaryHypergeometricCoefficient a b c j)) =
        ∑ j ∈ Finset.range N, (f j - f (j + 1)) := by
      apply Finset.sum_congr rfl
      intro j hj
      apply ordinaryHypergeometricCoefficient_shift_b_c_coboundary a b c j hb hc
      · rw [ne_eq, ascPochhammer_eval_eq_zero_iff]
        push Not
        intro k hk hkc
        exact hcavoid k hkc
      · intro hcj
        apply hcavoid j
        linear_combination hcj
    _ = f 0 - f N := Finset.sum_range_sub' f N
    _ = -((N : ℂ) / b * ordinaryHypergeometricCoefficient a b c N) := by simp [f]

/-- Infinite Gauss transport once both endpoint series converge and telescoping boundary dies. -/
theorem tsum_ordinaryHypergeometricCoefficient_shift_b_c
    (a b c : ℂ) (hb : b ≠ 0) (hcavoid : ∀ k : ℕ, (k : ℂ) ≠ -c)
    (hsum : Summable (ordinaryHypergeometricCoefficient a b c))
    (hsumshift : Summable (ordinaryHypergeometricCoefficient a (b + 1) (c + 1)))
    (htail : Tendsto
      (fun N : ℕ => (N : ℂ) / b * ordinaryHypergeometricCoefficient a b c N)
      atTop (𝓝 0)) :
    (c - a) / c *
        (∑' j : ℕ, ordinaryHypergeometricCoefficient a (b + 1) (c + 1) j) =
      ∑' j : ℕ, ordinaryHypergeometricCoefficient a b c j := by
  let L : ℕ → ℂ := fun N =>
    (c - a) / c *
          (∑ j ∈ Finset.range N,
            ordinaryHypergeometricCoefficient a (b + 1) (c + 1) j) -
        ∑ j ∈ Finset.range N, ordinaryHypergeometricCoefficient a b c j
  have hL : Tendsto L atTop
      (𝓝 ((c - a) / c *
          (∑' j : ℕ, ordinaryHypergeometricCoefficient a (b + 1) (c + 1) j) -
        ∑' j : ℕ, ordinaryHypergeometricCoefficient a b c j)) := by
    exact (((hsumshift.hasSum.tendsto_sum_nat).const_mul ((c - a) / c)).sub
      hsum.hasSum.tendsto_sum_nat)
  have hL0 : Tendsto L atTop (𝓝 0) := by
    have hneg : Tendsto
        (fun N : ℕ => -((N : ℂ) / b * ordinaryHypergeometricCoefficient a b c N))
        atTop (𝓝 0) := by simpa using htail.neg
    apply hneg.congr'
    exact Eventually.of_forall fun N =>
      (ordinaryHypergeometricCoefficient_sum_shift_b_c a b c N hb hcavoid).symm
  exact sub_eq_zero.mp (tendsto_nhds_unique hL hL0)

theorem ordinaryHypergeometricCoefficient_symm
    (a b c : ℂ) (j : ℕ) :
    ordinaryHypergeometricCoefficient a b c j =
      ordinaryHypergeometricCoefficient b a c j := by
  simp only [ordinaryHypergeometricCoefficient]
  ring

/-- Symmetric finite Gauss transport for `(a,c) -> (a+1,c+1)`. -/
theorem ordinaryHypergeometricCoefficient_sum_shift_a_c
    (a b c : ℂ) (N : ℕ) (ha : a ≠ 0)
    (hcavoid : ∀ k : ℕ, (k : ℂ) ≠ -c) :
    (c - b) / c *
          (∑ j ∈ Finset.range N,
            ordinaryHypergeometricCoefficient (a + 1) b (c + 1) j) -
        ∑ j ∈ Finset.range N, ordinaryHypergeometricCoefficient a b c j =
      -((N : ℂ) / a * ordinaryHypergeometricCoefficient a b c N) := by
  simpa only [ordinaryHypergeometricCoefficient_symm] using
    ordinaryHypergeometricCoefficient_sum_shift_b_c b a c N ha hcavoid

/-- Symmetric infinite Gauss transport for `(a,c) -> (a+1,c+1)`. -/
theorem tsum_ordinaryHypergeometricCoefficient_shift_a_c
    (a b c : ℂ) (ha : a ≠ 0) (hcavoid : ∀ k : ℕ, (k : ℂ) ≠ -c)
    (hsum : Summable (ordinaryHypergeometricCoefficient a b c))
    (hsumshift : Summable (ordinaryHypergeometricCoefficient (a + 1) b (c + 1)))
    (htail : Tendsto
      (fun N : ℕ => (N : ℂ) / a * ordinaryHypergeometricCoefficient a b c N)
      atTop (𝓝 0)) :
    (c - b) / c *
        (∑' j : ℕ, ordinaryHypergeometricCoefficient (a + 1) b (c + 1) j) =
      ∑' j : ℕ, ordinaryHypergeometricCoefficient a b c j := by
  have hsum' : Summable (ordinaryHypergeometricCoefficient b a c) := by
    exact hsum.congr (ordinaryHypergeometricCoefficient_symm a b c)
  have hsumshift' : Summable (ordinaryHypergeometricCoefficient b (a + 1) (c + 1)) := by
    exact hsumshift.congr (ordinaryHypergeometricCoefficient_symm (a + 1) b (c + 1))
  have htail' : Tendsto
      (fun N : ℕ => (N : ℂ) / a * ordinaryHypergeometricCoefficient b a c N)
      atTop (𝓝 0) := by
    simpa only [ordinaryHypergeometricCoefficient_symm] using htail
  simpa only [ordinaryHypergeometricCoefficient_symm] using
    tsum_ordinaryHypergeometricCoefficient_shift_b_c
      b a c ha hcavoid hsum' hsumshift' htail'

end

end RHTower
