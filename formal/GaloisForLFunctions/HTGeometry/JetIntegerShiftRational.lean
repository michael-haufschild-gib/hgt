import GaloisForLFunctions.HTGeometry.ComplexShiftJetApprox

/-!
# Transferring a digamma jet across an integer shift

Two shifts that differ by an integer generate the same differential field over `ℂ(s)`: the digamma
recurrence expresses one jet as the other plus a finite sum of inverse powers, and that sum is a
single quotient of polynomials.  This is what lets an arbitrary finite family of complex shifts be
replaced by pairwise incongruent representatives.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- The common denominator of the first `k` inverse powers at a shift. -/
def jetShiftDenom (mu : ℂ) (n k : ℕ) : Polynomial ℂ :=
  ∏ i ∈ Finset.range k, (Polynomial.X + Polynomial.C (mu + (i : ℂ))) ^ (n + 1)

theorem jetShiftDenom_ne_zero (mu : ℂ) (n k : ℕ) : jetShiftDenom mu n k ≠ 0 := by
  refine Finset.prod_ne_zero_iff.mpr fun i _ => ?_
  exact pow_ne_zero _ (Polynomial.X_add_C_ne_zero _)

theorem eval_jetShiftDenom (mu : ℂ) (n k : ℕ) (z : ℂ) :
    (jetShiftDenom mu n k).eval z = ∏ i ∈ Finset.range k, (z + (mu + (i : ℂ))) ^ (n + 1) := by
  rw [jetShiftDenom, Polynomial.eval_prod]
  exact Finset.prod_congr rfl fun i _ => by simp

theorem eval_jetShiftDenom_ne_zero {mu : ℂ} {n k : ℕ} {z : ℂ}
    (hz : ∀ i ∈ Finset.range k, z + (mu + (i : ℂ)) ≠ 0) : (jetShiftDenom mu n k).eval z ≠ 0 := by
  rw [eval_jetShiftDenom]
  exact Finset.prod_ne_zero_iff.mpr fun i hi => pow_ne_zero _ (hz i hi)

/-- **A finite sum of inverse powers at consecutive shifts is a quotient of polynomials.** -/
theorem exists_poly_sum_inv_pow (c mu : ℂ) (n k : ℕ) :
    ∃ p : Polynomial ℂ, ∀ z : ℂ, (∀ i ∈ Finset.range k, z + (mu + (i : ℂ)) ≠ 0) →
      ∑ i ∈ Finset.range k, c / (z + (mu + (i : ℂ))) ^ (n + 1)
        = p.eval z / (jetShiftDenom mu n k).eval z := by
  induction k with
  | zero => exact ⟨0, fun z _ => by simp [jetShiftDenom]⟩
  | succ k ih =>
      obtain ⟨p, hp⟩ := ih
      refine ⟨p * (Polynomial.X + Polynomial.C (mu + (k : ℂ))) ^ (n + 1)
        + Polynomial.C c * jetShiftDenom mu n k, fun z hz => ?_⟩
      have hsub : ∀ i ∈ Finset.range k, z + (mu + (i : ℂ)) ≠ 0 := fun i hi =>
        hz i (Finset.mem_range.mpr (lt_trans (Finset.mem_range.mp hi) (Nat.lt_succ_self k)))
      have hA : (jetShiftDenom mu n k).eval z ≠ 0 := eval_jetShiftDenom_ne_zero hsub
      have hBne : z + (mu + (k : ℂ)) ≠ 0 :=
        hz k (Finset.mem_range.mpr (Nat.lt_succ_self k))
      have hB : (z + (mu + (k : ℂ))) ^ (n + 1) ≠ 0 := pow_ne_zero _ hBne
      have hden : (jetShiftDenom mu n (k + 1)).eval z
          = (jetShiftDenom mu n k).eval z * (z + (mu + (k : ℂ))) ^ (n + 1) := by
        rw [eval_jetShiftDenom, eval_jetShiftDenom, Finset.prod_range_succ]
      rw [Finset.sum_range_succ, hp z hsub, hden]
      simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
        Polynomial.eval_X, Polynomial.eval_C]
      field_simp

/-- **A digamma jet transfers across a natural shift by a rational function.** -/
theorem exists_ratEval_jet_natCast_shift (mu : ℂ) (n k : ℕ) :
    ∃ p : Polynomial ℂ, ∀ z : ℂ, (∀ q : ℕ, z + mu ≠ -(q : ℂ)) →
      (jetShiftDenom mu n k).eval z ≠ 0 ∧
      iteratedDeriv n Complex.digamma (z + (mu + (k : ℂ)))
        = iteratedDeriv n Complex.digamma (z + mu)
          + p.eval z / (jetShiftDenom mu n k).eval z := by
  obtain ⟨p, hp⟩ := exists_poly_sum_inv_pow ((-1) ^ n * ((n.factorial : ℕ) : ℂ)) mu n k
  refine ⟨p, fun z hz => ?_⟩
  have hpole : ∀ i ∈ Finset.range k, z + (mu + (i : ℂ)) ≠ 0 := by
    intro i _ h0
    refine hz i ?_
    have : z + mu = -(i : ℂ) := by linear_combination h0
    exact this
  refine ⟨eval_jetShiftDenom_ne_zero hpole, ?_⟩
  have hrec := digammaJet_add_natCast n hz k
  have hassoc : z + mu + (k : ℂ) = z + (mu + (k : ℂ)) := by ring
  rw [hassoc] at hrec
  rw [hrec, ← hp z hpole]
  refine congrArg _ (Finset.sum_congr rfl fun i _ => ?_)
  rw [show z + mu + (i : ℂ) = z + (mu + (i : ℂ)) by ring]

/-- **A digamma jet transfers across an arbitrary integer shift by a quotient of polynomials.** -/
theorem exists_ratEval_jet_int_shift (mu : ℂ) (n : ℕ) (m : ℤ) :
    ∃ (p q : Polynomial ℂ), q ≠ 0 ∧ ∀ z : ℂ, (∀ j : ℤ, z + mu ≠ (j : ℂ)) →
      q.eval z ≠ 0 ∧
      iteratedDeriv n Complex.digamma (z + (mu + (m : ℂ)))
        = iteratedDeriv n Complex.digamma (z + mu) + p.eval z / q.eval z := by
  rcases le_or_gt 0 m with hm | hm
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, m = (k : ℤ) := ⟨m.toNat, (Int.toNat_of_nonneg hm).symm⟩
    obtain ⟨p, hp⟩ := exists_ratEval_jet_natCast_shift mu n k
    refine ⟨p, jetShiftDenom mu n k, jetShiftDenom_ne_zero mu n k, fun z hz => ?_⟩
    have hcast : ((m : ℤ) : ℂ) = ((k : ℕ) : ℂ) := by rw [hk]; push_cast; ring
    rw [hcast]
    exact hp z fun q hq => hz (-(q : ℤ)) (by push_cast; exact hq)

  · set k : ℕ := (-m).toNat with hkdef
    have hmk : ((k : ℕ) : ℤ) = -m := by rw [hkdef]; exact Int.toNat_of_nonneg (by omega)
    have hk : (m : ℂ) + (k : ℂ) = 0 := by
      have hcast : ((k : ℕ) : ℂ) = (((k : ℕ) : ℤ) : ℂ) := by push_cast; ring
      rw [hcast, hmk]
      push_cast
      ring
    set mu' : ℂ := mu + (m : ℂ) with hmu'
    obtain ⟨p, hp⟩ := exists_ratEval_jet_natCast_shift mu' n k
    refine ⟨-p, jetShiftDenom mu' n k, jetShiftDenom_ne_zero mu' n k, fun z hz => ?_⟩
    have hback : mu' + (k : ℂ) = mu := by rw [hmu']; linear_combination hk
    have hpole : ∀ q : ℕ, z + mu' ≠ -(q : ℂ) := by
      intro q hq
      refine hz (-(q : ℤ) - m) ?_
      push_cast
      rw [hmu'] at hq
      linear_combination hq
    obtain ⟨hQne, hstep⟩ := hp z hpole
    rw [hback] at hstep
    refine ⟨hQne, ?_⟩
    rw [hstep]
    simp only [Polynomial.eval_neg]
    ring

end

end GaloisForLFunctions.HTGeometry
