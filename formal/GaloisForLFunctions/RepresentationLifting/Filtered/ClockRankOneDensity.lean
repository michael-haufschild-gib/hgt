import GaloisForLFunctions.HTGeometry.SimpleClockRankOneAlgebraSaturation

/-!
# Bounded-degree density of a clock and a rank-one operator

The diagonal clock with labels `0,…,n-1` and the all-ones matrix span the
full matrix algebra through the ordered words `Dᵃ J Dᵇ`, with `a,b<n`.
Lagrange interpolation gives degree at most `n-1` on either side of `J`.
Thus generator words of length at most `2n-1` suffice, an explicit finite
model of the bounded PBW density in Zehavi, Claim 3.32, arXiv:2611.18218.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.Filtered

open Polynomial GaloisForLFunctions.HTGeometry

/-- The canonical clock has distinct integral labels in every dimension. -/
def naturalClock (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (fun i => (i.val : ℝ))

/-- A single rank-one operator connects every pair of clock eigenspaces. -/
def clockBoundary (n : ℕ) : Matrix (Fin n) (Fin n) ℝ := fun _ _ => 1

/-- Ordered words with fewer than `n` clock factors on each side of the boundary. -/
def clockWordSpan (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) :=
  Submodule.span ℝ (Set.range fun ab : Fin n × Fin n =>
    naturalClock n ^ ab.1.val * clockBoundary n * naturalClock n ^ ab.2.val)

/-- The selector polynomial has uniformly bounded degree. -/
theorem naturalClock_selector_degree (n : ℕ) (i : Fin n) :
    (simpleClockLagrangePolynomial (fun j : Fin n => (j.val : ℝ)) i).natDegree < n := by
  have hbound := Polynomial.natDegree_prod_le (Finset.univ.erase i)
    (fun j : Fin n => C ((i.val : ℝ) - j.val)⁻¹ * (X - C (j.val : ℝ)))
  have hfactor (j : Fin n) :
      (C ((i.val : ℝ) - j.val)⁻¹ * (X - C (j.val : ℝ))).natDegree ≤ 1 := by
    calc
      _ ≤ (C ((i.val : ℝ) - j.val)⁻¹).natDegree + (X - C (j.val : ℝ)).natDegree :=
        Polynomial.natDegree_mul_le
      _ = 1 := by rw [Polynomial.natDegree_C, Polynomial.natDegree_X_sub_C]
  have hs := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ.erase i) => hfactor j)
  have hc : (∑ _j ∈ Finset.univ.erase i, (1 : ℕ)) = n - 1 := by simp
  rw [hc] at hs
  change (simpleClockLagrangePolynomial (fun j : Fin n => (j.val : ℝ)) i).natDegree ≤ _ at hbound
  have hi := i.isLt
  omega

private theorem aeval_eq_clock_sum {n : ℕ} (p : ℝ[X]) (hp : p.natDegree < n) :
    aeval (naturalClock n) p =
      ∑ a ∈ Finset.range n, p.coeff a • naturalClock n ^ a := by
  rw [aeval_def, Polynomial.eval₂_eq_sum_range' _ hp]
  apply Finset.sum_congr rfl
  intro a _
  rw [Algebra.smul_def]

/-- Every matrix unit is obtained inside the same bounded word space. -/
theorem naturalClock_matrixUnit_mem (n : ℕ) (i j : Fin n) :
    Matrix.single i j (1 : ℝ) ∈ clockWordSpan n := by
  have hinj : Function.Injective (fun k : Fin n => (k.val : ℝ)) := by
    intro a b h
    apply Fin.ext
    change (a.val : ℝ) = (b.val : ℝ) at h
    exact_mod_cast h
  have hselector (k : Fin n) := aeval_simpleClockLagrangePolynomial
    (fun k : Fin n => (k.val : ℝ)) hinj k
  have he : Matrix.single i j (1 : ℝ) =
      aeval (naturalClock n) (simpleClockLagrangePolynomial (fun k : Fin n => (k.val : ℝ)) i) *
        clockBoundary n *
          aeval (naturalClock n) (simpleClockLagrangePolynomial (fun k : Fin n => (k.val : ℝ)) j) := by
    rw [naturalClock, hselector i, hselector j]
    simp [clockBoundary]
  rw [he, aeval_eq_clock_sum _ (naturalClock_selector_degree n i),
    aeval_eq_clock_sum _ (naturalClock_selector_degree n j)]
  simp_rw [Finset.sum_mul, Finset.mul_sum, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  apply Submodule.sum_mem
  intro a ha
  apply Submodule.sum_mem
  intro b hb
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨(⟨a, Finset.mem_range.mp ha⟩, ⟨b, Finset.mem_range.mp hb⟩), rfl⟩

/-- Bounded ordered words already span every endomorphism, including dimension zero. -/
theorem naturalClock_bounded_density (n : ℕ) : clockWordSpan n = ⊤ := by
  apply top_unique
  intro M _
  rw [Matrix.matrix_eq_sum_single M]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.sum_mem
  intro j _
  simpa only [Matrix.smul_single, smul_eq_mul, mul_one] using
    (clockWordSpan n).smul_mem (M i j) (naturalClock_matrixUnit_mem n i j)

end GaloisForLFunctions.RepresentationLifting.Filtered

#print axioms GaloisForLFunctions.RepresentationLifting.Filtered.naturalClock_selector_degree
#print axioms GaloisForLFunctions.RepresentationLifting.Filtered.naturalClock_bounded_density
