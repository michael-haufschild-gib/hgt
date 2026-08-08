import GaloisForLFunctions.HTGeometry.MeromorphicLaurentDerivative

/-!
# The Laurent transform of a jet

Iterating the differentiation law gives the Laurent coefficients of every derivative:

`c_ℓ(f⁽ʲ⁾, a) = (ℓ+1)(ℓ+2)⋯(ℓ+j) · c_{ℓ+j}(f, a)`.

Two evaluations of the falling product shape the jets of a simple pole.  It vanishes for
`-j ≤ ℓ ≤ -1`, so no jet has a Laurent coefficient strictly between its own pole order and zero; and
at `ℓ = -(j+1)` it equals `(-1)ʲ j!`.  A `j`-th derivative of a function with a simple pole of
residue `r` therefore has principal part exactly `(-1)ʲ j! r · (z-a)^{-(j+1)}`.

* `meromorphicAt_iteratedDeriv`;
* `laurentCoeff_iteratedDeriv_eq` — the jet law;
* `prod_range_eq_zero_of_mem`, `prod_range_neg_succ` — the two evaluations.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

theorem meromorphicAt_iteratedDeriv {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a) (j : ℕ) :
    MeromorphicAt (iteratedDeriv j f) a := by
  induction j with
  | zero => simpa [iteratedDeriv_zero] using hf
  | succ k ih =>
      rw [iteratedDeriv_succ]
      exact ih.deriv

/-- **The jet law of the Laurent transform.** -/
theorem laurentCoeff_iteratedDeriv_eq {f : ℂ → ℂ} {a : ℂ} (hf : MeromorphicAt f a) :
    ∀ (j : ℕ) (ℓ : ℤ), laurentCoeff (iteratedDeriv j f) a ℓ
      = (∏ i ∈ Finset.range j, ((ℓ : ℂ) + (i : ℂ) + 1)) * laurentCoeff f a (ℓ + (j : ℤ)) := by
  intro j
  induction j with
  | zero => intro ℓ; simp [iteratedDeriv_zero]
  | succ k ih =>
      intro ℓ
      rw [iteratedDeriv_succ, laurentCoeff_deriv (meromorphicAt_iteratedDeriv hf k) ℓ,
        ih (ℓ + 1), Finset.prod_range_succ']
      have hidx : ℓ + 1 + (k : ℤ) = ℓ + ((k + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [hidx]
      have hprod : (∏ i ∈ Finset.range k, (((ℓ + 1 : ℤ) : ℂ) + (i : ℂ) + 1))
          = ∏ i ∈ Finset.range k, ((ℓ : ℂ) + ((i + 1 : ℕ) : ℂ) + 1) := by
        refine Finset.prod_congr rfl fun i _ => ?_
        push_cast
        ring
      rw [hprod]
      push_cast
      ring

/-- Between its own pole order and zero a jet has no Laurent coefficient: the falling product
contains a zero factor. -/
theorem prod_range_eq_zero_of_mem {j : ℕ} {ℓ : ℤ} (h1 : -(j : ℤ) ≤ ℓ) (h2 : ℓ ≤ -1) :
    (∏ i ∈ Finset.range j, ((ℓ : ℂ) + (i : ℂ) + 1)) = 0 := by
  refine Finset.prod_eq_zero (i := (-ℓ - 1).toNat) ?_ ?_
  · rw [Finset.mem_range]
    omega
  · have hz : (((-ℓ - 1).toNat : ℕ) : ℤ) = -ℓ - 1 := by omega
    have hcast : (((-ℓ - 1).toNat : ℕ) : ℂ) = ((-ℓ - 1 : ℤ) : ℂ) := by
      rw [show (((-ℓ - 1).toNat : ℕ) : ℂ) = ((((-ℓ - 1).toNat : ℕ) : ℤ) : ℂ) from by norm_cast, hz]
    rw [hcast]
    push_cast
    ring

/-- The falling product of length `j` starting at `-j`. -/
theorem prod_range_sub_self (j : ℕ) :
    (∏ i ∈ Finset.range j, ((i : ℂ) - (j : ℂ))) = (-1) ^ j * (j.factorial : ℂ) := by
  induction j with
  | zero => simp
  | succ k ih =>
      rw [Finset.prod_range_succ']
      have hcongr : ∀ i ∈ Finset.range k,
          (((i + 1 : ℕ) : ℂ) - ((k + 1 : ℕ) : ℂ)) = ((i : ℂ) - (k : ℂ)) := by
        intro i _
        push_cast
        ring
      rw [Finset.prod_congr rfl hcongr, ih, Nat.factorial_succ]
      push_cast
      ring

/-- **At its own pole order the falling product is `(-1)ʲ j!`.** -/
theorem prod_range_neg_succ (j : ℕ) :
    (∏ i ∈ Finset.range j, (((-((j : ℤ) + 1) : ℤ) : ℂ) + (i : ℂ) + 1))
      = (-1) ^ j * (j.factorial : ℂ) := by
  rw [← prod_range_sub_self j]
  refine Finset.prod_congr rfl fun i _ => ?_
  push_cast
  ring

end GaloisForLFunctions.HTGeometry
