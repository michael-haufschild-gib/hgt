import GaloisForLFunctions.RHTower.Sieve.ResidueSum
import GaloisForLFunctions.RHTower.Sieve.DiscreteParseval

/-!
# Parseval over the residues

Summing the exponential sum of a set over *all* fractions with denominator `q` returns the second
moment of its residue counts:

`∑_{a < q} |∑_{n ∈ A} e(na/q)|² = q ∑_{h < q} #{n ∈ A : n ≡ h}²`.

Once `ResidueSum.lean` has collapsed the exponential sum to the residue counts, this is Parseval for
the finite Fourier transform on `ℤ/q`, which the corpus already owns in the form of the orthonormal
root basis of `DiscreteParseval.lean`: the count vector is exactly the vector whose coefficients
against the exponential rows are the values of the exponential sum.

This is the identity by which a sieve hypothesis becomes a count: bounding the left side from below
by the classes `A` avoids, and from above by the large sieve, bounds `|A|`.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- The residue counts of a set, as a Euclidean vector. -/
noncomputable def countVec (q : ℕ) (A : Finset ℕ) : EuclideanSpace ℂ (Fin q) :=
  WithLp.toLp 2 (fun h : Fin q => ((residueCount q A (h : ℕ) : ℕ) : ℂ))

/-- The coefficient of the count vector against an exponential row is the exponential sum. -/
theorem norm_inner_expRow_countVec (q : ℕ) (A : Finset ℕ) (j : Fin q) :
    ‖⟪expRow q ((rootOfUnity q) ^ (j : ℕ)), countVec q A⟫_ℂ‖
      = ‖∑ h ∈ Finset.range q,
          ((residueCount q A h : ℕ) : ℂ)
            * circleFreq (((h * (j : ℕ) : ℕ) : ℝ) / (q : ℝ))‖ := by
  rw [inner_expRow_apply]
  have hstep : ∑ h : Fin q,
        (starRingEnd ℂ) (((rootOfUnity q) ^ (j : ℕ)) ^ (h : ℕ)) * (countVec q A) h
      = (starRingEnd ℂ) (∑ h : Fin q,
          ((rootOfUnity q) ^ (j : ℕ)) ^ (h : ℕ) * ((residueCount q A (h : ℕ) : ℕ) : ℂ)) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [map_mul]
    simp [countVec]
  rw [hstep]
  have hnorm : ‖(starRingEnd ℂ) (∑ h : Fin q,
      ((rootOfUnity q) ^ (j : ℕ)) ^ (h : ℕ) * ((residueCount q A (h : ℕ) : ℕ) : ℂ))‖
      = ‖∑ h : Fin q,
          ((rootOfUnity q) ^ (j : ℕ)) ^ (h : ℕ) * ((residueCount q A (h : ℕ) : ℕ) : ℂ)‖ :=
    RCLike.norm_conj _
  rw [hnorm,
    Fin.sum_univ_eq_sum_range
      (fun h => ((rootOfUnity q) ^ (j : ℕ)) ^ h * ((residueCount q A h : ℕ) : ℂ)) q]
  congr 1
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [circleFreq_div_eq_rootOfUnity_pow, ← pow_mul, mul_comm (j : ℕ) h, mul_comm]

/-- The energy of the count vector. -/
theorem norm_sq_countVec (q : ℕ) (A : Finset ℕ) :
    ‖countVec q A‖ ^ 2 = ∑ h ∈ Finset.range q, ((residueCount q A h : ℕ) : ℝ) ^ 2 := by
  rw [countVec, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity),
    ← Fin.sum_univ_eq_sum_range (fun h => ((residueCount q A h : ℕ) : ℝ) ^ 2) q]
  refine Finset.sum_congr rfl fun h _ => ?_
  simp

/-- **Parseval over the residues.** -/
theorem sum_residue_parseval {q : ℕ} (hq : 0 < q) (A : Finset ℕ) :
    ∑ j : Fin q, ‖∑ h ∈ Finset.range q,
        ((residueCount q A h : ℕ) : ℂ) * circleFreq (((h * (j : ℕ) : ℕ) : ℝ) / (q : ℝ))‖ ^ 2
      = (q : ℝ) * ∑ h ∈ Finset.range q, ((residueCount q A h : ℕ) : ℝ) ^ 2 := by
  have hζ : IsPrimitiveRoot (rootOfUnity q) q := isPrimitiveRoot_rootOfUnity (by omega)
  have hbase := sum_norm_inner_expRow_root hq hζ (countVec q A)
  rw [norm_sq_countVec] at hbase
  rw [← hbase]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [norm_inner_expRow_countVec]

/-- **The full sum over fractions with denominator `q` is the second moment of the residue
counts.** -/
theorem sum_full_expSum_sq {q : ℕ} (hq : 0 < q) (A : Finset ℕ) :
    ∑ j : Fin q, ‖∑ n ∈ A, circleFreq (((n * (j : ℕ) : ℕ) : ℝ) / (q : ℝ))‖ ^ 2
      = (q : ℝ) * ∑ h ∈ Finset.range q, ((residueCount q A h : ℕ) : ℝ) ^ 2 := by
  rw [← sum_residue_parseval hq A]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [sum_circleFreq_eq_residue hq]

end RHTower.Sieve
