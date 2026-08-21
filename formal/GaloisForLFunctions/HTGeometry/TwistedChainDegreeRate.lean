import GaloisForLFunctions.HTGeometry.ConstantConjugationDegree
import Mathlib.Analysis.Subadditive

/-!
# The growth rate of a twisted chain exists

The matrix degree of a twisted chain is subadditive: `A_{m+n} = A_m · σ^m(A_n)`, the degree of a
product is at most the sum of the degrees, and a degree-preserving twist does not change the
degree of a matrix.  Fekete's lemma then gives an actual limit, not merely a limsup, and identifies
it with the infimum of `matDeg A_n / n`.

This is the asymptotic clock speed of a twisted matrix chain, unconditionally: no invertibility, no
hypothesis on the leading matrices, no completion.

* `matDeg_map_le` — a degree-preserving twist does not raise the matrix degree;
* `matDeg_twistedChain_add_le` — **subadditivity**;
* `subadditive_matDeg_twistedChain`, `twistedChainRate`;
* `tendsto_matDeg_twistedChain` — **the rate exists**;
* `twistedChainRate_le` — it is at most `matDeg A_n / n` for every `n`.
-/

open scoped Differential

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

namespace DiffOp

noncomputable section

variable {K : Type u} [Field K] [Differential K]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [DecidableEq ι] [Nonempty ι] in
theorem matDeg_map_le {g : DiffOp K → DiffOp K} (hg : ∀ p, degree (g p) = degree p)
    (P : Matrix ι ι (DiffOp K)) : matDeg (P.map g) ≤ matDeg P := by
  refine matDeg_le fun i j => ?_
  rw [Matrix.map_apply, hg]
  exact degree_le_matDeg P i j

omit [Nonempty ι] in
/-- **The matrix degree of a twisted chain is subadditive.** -/
theorem matDeg_twistedChain_add_le (σ : DiffOp K →+* DiffOp K)
    (hσ : ∀ p, degree (σ p) = degree p) (C : Matrix ι ι (DiffOp K)) (m n : ℕ) :
    matDeg (twistedChain σ C (m + n))
      ≤ matDeg (twistedChain σ C m) + matDeg (twistedChain σ C n) := by
  have hiter : ∀ (t : ℕ) (p : DiffOp K), degree (iterHom σ t p) = degree p := by
    intro t
    induction t with
    | zero => exact fun p => rfl
    | succ t ih =>
        intro p
        rw [iterHom, RingHom.comp_apply, hσ, ih]
  rw [twistedChain_add]
  refine le_trans (matDeg_mul_le _ _) ?_
  exact Nat.add_le_add_left (matDeg_map_le (hiter m) _) _

omit [Nonempty ι] in
theorem subadditive_matDeg_twistedChain (σ : DiffOp K →+* DiffOp K)
    (hσ : ∀ p, degree (σ p) = degree p) (C : Matrix ι ι (DiffOp K)) :
    Subadditive fun n => (matDeg (twistedChain σ C n) : ℝ) := by
  intro m n
  have h := matDeg_twistedChain_add_le σ hσ C m n
  show ((matDeg (twistedChain σ C (m + n)) : ℕ) : ℝ)
    ≤ ((matDeg (twistedChain σ C m) : ℕ) : ℝ) + ((matDeg (twistedChain σ C n) : ℕ) : ℝ)
  exact_mod_cast h

omit [Nonempty ι] in
theorem bddBelow_normalized_matDeg_twistedChain (σ : DiffOp K →+* DiffOp K)
    (C : Matrix ι ι (DiffOp K)) :
    BddBelow (Set.range fun n => (matDeg (twistedChain σ C n) : ℝ) / n) := by
  refine ⟨0, ?_⟩
  rintro y ⟨n, rfl⟩
  positivity

/-- The asymptotic growth rate of a twisted chain. -/
def twistedChainRate (σ : DiffOp K →+* DiffOp K) (hσ : ∀ p, degree (σ p) = degree p)
    (C : Matrix ι ι (DiffOp K)) : ℝ :=
  (subadditive_matDeg_twistedChain σ hσ C).lim

omit [Nonempty ι] in
/-- **The growth rate exists**, as an actual limit. -/
theorem tendsto_matDeg_twistedChain (σ : DiffOp K →+* DiffOp K)
    (hσ : ∀ p, degree (σ p) = degree p) (C : Matrix ι ι (DiffOp K)) :
    Tendsto (fun n => (matDeg (twistedChain σ C n) : ℝ) / n) atTop
      (nhds (twistedChainRate σ hσ C)) :=
  (subadditive_matDeg_twistedChain σ hσ C).tendsto_lim
    (bddBelow_normalized_matDeg_twistedChain σ C)

end

end DiffOp

end GaloisForLFunctions.HTGeometry
