import GaloisForLFunctions.HTGeometry.SpectralDiscriminantPolynomial
import Mathlib.Algebra.MvPolynomial.CommRing

/-! # Eliminating eigenvalue labels by traces

A polynomial in the couplings and one spectral variable can be summed over
the spectrum by replacing each spectral power by a power trace. For a
linear pencil this operation does not increase total degree.
-/
open MvPolynomial Matrix
namespace GaloisForLFunctions.HTGeometry.SpectralJets
noncomputable section
variable {ι R S : Type*} [Fintype ι] [CommRing R] [CommRing S] {D : ℕ}

/-- Replace each power of the distinguished variable by the corresponding
power trace. In particular its zeroth power contributes the matrix size. -/
def spectralSum (M : Matrix (Fin D) (Fin D) (MvPolynomial ι R))
    (b : MvPolynomial (Option ι) R) : MvPolynomial ι R :=
  ∑ d ∈ b.support, C (b.coeff d) * (∏ i, X i^(d (some i))) * (M^(d none)).trace

omit [Fintype ι] in
private theorem trace_power_degree (M : Matrix (Fin D) (Fin D) (MvPolynomial ι R))
    (hM : ∀ i j, (M i j).totalDegree ≤ 1) (k : ℕ) :
    (M^k).trace.totalDegree ≤ k := by
  have hb (k : ℕ) : ∀ i j, ((M^k) i j).totalDegree ≤ k := by
    induction k with
    | zero =>
      intro i j
      simp only [pow_zero,Matrix.one_apply]
      split <;> simp
    | succ k ih =>
      intro i j
      rw [pow_succ,Matrix.mul_apply]
      exact totalDegree_finsetSum_le fun a _ =>
        (totalDegree_mul _ _).trans (Nat.add_le_add (ih i a) (hM a j))
  exact totalDegree_finsetSum_le fun i _ => hb k i i

theorem spectralSum_degree [Nontrivial R] (M : Matrix (Fin D) (Fin D) (MvPolynomial ι R))
    (hM : ∀ i j, (M i j).totalDegree ≤ 1) (b : MvPolynomial (Option ι) R) :
    (spectralSum M b).totalDegree ≤ b.totalDegree := by
  classical
  apply totalDegree_finsetSum_le
  intro d hd
  have hprod : (∏ i, (X i : MvPolynomial ι R)^(d (some i))).totalDegree ≤ ∑ i, d (some i) := by
    simpa only [totalDegree_X_pow] using totalDegree_finsetProd Finset.univ
      (fun i => (X i : MvPolynomial ι R)^(d (some i)))
  have hdegree := le_totalDegree hd
  rw [Finsupp.sum_fintype _ _ (by simp),Fintype.sum_option] at hdegree
  apply (totalDegree_mul _ _).trans
  have hcoeff := totalDegree_mul (C (b.coeff d)) (∏ i, (X i : MvPolynomial ι R)^(d (some i)))
  rw [totalDegree_C,zero_add] at hcoeff
  have htrace := trace_power_degree M hM (d none)
  omega

/-- The polynomial power-trace sum commutes with specialization and is
the sum of the original row polynomial on the roots. -/
theorem eval_spectralSum (M : Matrix (Fin D) (Fin D) (MvPolynomial ι R))
    (φ : R →+* S) (x : ι → S) (E : Fin D → S)
    (htr : ∀ k : ℕ, eval₂Hom φ x (M^k).trace = ∑ j, (E j)^k)
    (b : MvPolynomial (Option ι) R) :
    eval₂Hom φ x (spectralSum M b) = ∑ j, eval₂ φ (fun o : Option ι => o.elim (E j) x) b := by
  classical
  simp only [spectralSum,map_sum,map_mul,map_prod,map_pow,eval₂Hom_C,eval₂Hom_X',htr,
    eval₂_eq',Fintype.prod_option,Option.elim_none,Option.elim_some]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Trace Gram determinant of a square family of polynomial rows. -/
def gram (M : Matrix (Fin D) (Fin D) (MvPolynomial ι R))
    (b : Fin D → MvPolynomial (Option ι) R) : MvPolynomial ι R :=
  (Matrix.of fun i j => spectralSum M (b i*b j)).det

theorem determinant_degree {σ : Type*} (A : Matrix (Fin D) (Fin D) (MvPolynomial σ R))
    (B : ℕ) (h : ∀ i j, (A i j).totalDegree ≤ B) : A.det.totalDegree ≤ D*B := by
  classical
  rw [Matrix.det_apply']
  apply totalDegree_finsetSum_le
  intro e _
  have hC : ((Equiv.Perm.sign e : ℤ) : MvPolynomial σ R) = C ((Equiv.Perm.sign e : ℤ) : R) :=
    (map_intCast (C : R →+* MvPolynomial σ R) _).symm
  rw [hC]
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C,zero_add]
  apply (totalDegree_finsetProd ..).trans
  simpa using (Finset.sum_le_sum (s := Finset.univ) fun (i : Fin D) _ => h (e i) i)

theorem gram_degree [Nontrivial R] (M : Matrix (Fin D) (Fin D) (MvPolynomial ι R))
    (hM : ∀ i j, (M i j).totalDegree ≤ 1) (b : Fin D → MvPolynomial (Option ι) R)
    (B : ℕ) (hb : ∀ i, (b i).totalDegree ≤ B) :
    (gram M b).totalDegree ≤ D*(2*B) := by
  apply determinant_degree
  intro i j
  exact (spectralSum_degree M hM _).trans ((totalDegree_mul _ _).trans (by simpa only [two_mul] using Nat.add_le_add (hb i) (hb j)))

/-- Squaring the determinant cancels every possible permutation of the
roots. No product indexed by labelings occurs in the polynomial. -/
theorem eval_gram (M : Matrix (Fin D) (Fin D) (MvPolynomial ι R))
    (φ : R →+* S) (x : ι → S) (E : Fin D → S)
    (htr : ∀ k : ℕ, eval₂Hom φ x (M^k).trace = ∑ j, (E j)^k)
    (b : Fin D → MvPolynomial (Option ι) R) :
    eval₂Hom φ x (gram M b) =
      (Matrix.of fun i j => eval₂ φ (fun o : Option ι => o.elim (E j) x) (b i)).det^2 := by
  let A := Matrix.of fun i j => eval₂ φ (fun o : Option ι => o.elim (E j) x) (b i)
  rw [gram,RingHom.map_det]
  have he : (eval₂Hom φ x).mapMatrix (Matrix.of fun i j => spectralSum M (b i*b j)) = A*Aᵀ := by
    ext i j
    change eval₂Hom φ x (spectralSum M (b i*b j)) = _
    rw [eval_spectralSum M φ x E htr]
    simp only [eval₂_mul,A,Matrix.mul_apply,Matrix.transpose_apply,Matrix.of_apply]
  rw [he,Matrix.det_mul,Matrix.det_transpose,pow_two]

#print axioms eval_gram
#print axioms gram_degree
end
end GaloisForLFunctions.HTGeometry.SpectralJets
