import GaloisForLFunctions.HTGeometry.BorelWeil.CompleteReducibility
import GaloisForLFunctions.HTGeometry.BorelWeil.PolyVanishing

/-!
# The determinant twist and divisibility of sections

Multiplication by the determinant identifies `H⁰(λ)` with `H⁰(λ + 1)`: the image is a nonzero
`GL`-stable subspace of `H⁰(λ + 1)`, so in characteristic zero irreducibility forces it to be
everything.  In particular **every section of weight `λ + c·1` is divisible by `detᶜ`** — the
statement that, in the classical account, is extracted from the irreducibility of the determinant
polynomial.  Here it comes for free from the Borel–Weil theorem itself.

## Main definitions

* `GaloisForLFunctions.HTGeometry.BorelWeil.detPoly` — the determinant of the generic matrix.
* `GaloisForLFunctions.HTGeometry.BorelWeil.substRight` — right translation of polynomials.

## Main results

* `detPow_mem_polySections` — `detᶜ · H⁰(λ) ⊆ H⁰(λ + c)`.
* `exists_eq_detPow_mul` — the converse: every section of weight `λ + c` is `detᶜ` times one of
  weight `λ`.
-/

set_option linter.unusedSectionVars false

namespace GaloisForLFunctions.HTGeometry.BorelWeil

open Matrix MvPolynomial

variable {N : ℕ} {k : Type*} [Field k]

/-- The determinant of the generic matrix. -/
noncomputable def detPoly (N : ℕ) (k : Type*) [Field k] : MvPolynomial (Fin N × Fin N) k :=
  minorPoly N N k

theorem detPoly_def : detPoly N k = minorPoly N N k := rfl

@[simp] theorem matEval_detPoly (g : Matrix (Fin N) (Fin N) k) :
    matEval g (detPoly N k) = g.det := matEval_minorPoly_top g

theorem detPoly_ne_zero : detPoly N k ≠ 0 := minorPoly_top_ne_zero

/-- Right translation of polynomials: `substRight x p` evaluates at `g * x` what `p` evaluates
at `g`. -/
noncomputable def substRight (x : Matrix (Fin N) (Fin N) k) :
    MvPolynomial (Fin N × Fin N) k →ₐ[k] MvPolynomial (Fin N × Fin N) k :=
  MvPolynomial.aeval fun ij : Fin N × Fin N =>
    ∑ r : Fin N, MvPolynomial.C (x r ij.2) * MvPolynomial.X (ij.1, r)

theorem matEval_substRight (x g : Matrix (Fin N) (Fin N) k)
    (p : MvPolynomial (Fin N × Fin N) k) :
    matEval g (substRight x p) = matEval (g * x) p := by
  have h1 : (MvPolynomial.eval (fun ij : Fin N × Fin N => g ij.1 ij.2)).comp
      (substRight x).toRingHom
      = MvPolynomial.eval (fun ij : Fin N × Fin N => (g * x) ij.1 ij.2) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [substRight]
    · intro ij
      simp [substRight, Matrix.mul_apply, mul_comm]
  exact congrFun (congrArg (fun φ : MvPolynomial (Fin N × Fin N) k →+* k => (φ : _ → k)) h1) p

theorem borelCharMat_add_const (lam : Fin N → ℕ) (c : ℕ) {B : Matrix (Fin N) (Fin N) k}
    (hB : B.BlockTriangular id) :
    borelCharMat (fun i => lam i + c) B = borelCharMat lam B * B.det ^ c := by
  rw [borelCharMat, borelCharMat, Matrix.det_of_upperTriangular hB, ← Finset.prod_pow,
    ← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun i _ => by rw [pow_add]

/-- **The determinant twist lands in the shifted section space.** -/
theorem detPow_mem_polySections {lam : Fin N → ℕ} {P : MvPolynomial (Fin N × Fin N) k}
    (hP : P ∈ polySections lam) (c : ℕ) :
    (detPoly N k) ^ c * P ∈ polySections (fun i => lam i + c) := by
  intro g B hB
  rw [matEval_mul, matEval_mul, matEval_pow, matEval_pow, matEval_detPoly, matEval_detPoly,
    hP g B hB, borelCharMat_add_const lam c hB.1, Matrix.det_mul, mul_pow]
  ring

/-- The image of `H⁰(λ)` under multiplication by `detᶜ`. -/
noncomputable def detTwist (lam : Fin N → ℕ) (c : ℕ) (k : Type*) [Field k] :
    Submodule k (MvPolynomial (Fin N × Fin N) k) :=
  Submodule.map (LinearMap.mulLeft k ((detPoly N k) ^ c)) (polySections lam)

theorem detTwist_le {lam : Fin N → ℕ} (c : ℕ) :
    detTwist lam c k ≤ polySections (fun i => lam i + c) := by
  rintro p ⟨q, hq, rfl⟩
  exact detPow_mem_polySections hq c

theorem detTwist_isGStable [Infinite k] (lam : Fin N → ℕ) (c : ℕ) :
    IsGStable (detTwist lam c k) := by
  rintro x hx p ⟨q, hq, rfl⟩
  have hdet : substLeft x (detPoly N k) = MvPolynomial.C x.det * detPoly N k := by
    refine matEval_injective fun g => ?_
    rw [matEval_substLeft, matEval_detPoly, matEval_mul, matEval_detPoly, Matrix.det_mul]
    simp [matEval]
  refine ⟨MvPolynomial.C (x.det ^ c) * substLeft x q, ?_, ?_⟩
  · rw [← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (polySections_substLeft x hq)
  · simp only [LinearMap.mulLeft_apply]
    rw [map_mul, _root_.map_pow (substLeft x) (detPoly N k) c, hdet, mul_pow,
      ← MvPolynomial.C_pow]
    ring

theorem detTwist_ne_bot [Infinite k] {lam : Fin N → ℕ} (hlam : Antitone lam) (c : ℕ) :
    detTwist lam c k ≠ ⊥ := by
  intro hbot
  have hmem : (detPoly N k) ^ c * bwPoly (multOfWeight lam) k ∈ detTwist lam c k := by
    refine ⟨bwPoly (multOfWeight lam) k, ?_, rfl⟩
    have h := bwPoly_mem_polySections (k := k) (multOfWeight lam)
    rwa [weightOfMult_multOfWeight hlam] at h
  rw [hbot, Submodule.mem_bot] at hmem
  rcases mul_eq_zero.mp hmem with h | h
  · exact (pow_ne_zero c detPoly_ne_zero) h
  · exact bwPoly_ne_zero _ h

/-- **Divisibility of sections by the determinant.**  In characteristic zero every section of
weight `λ + c` is `detᶜ` times a section of weight `λ`. -/
theorem exists_eq_detPow_mul [CharZero k] {lam : Fin N → ℕ} (hlam : Antitone lam) (c : ℕ)
    {P : MvPolynomial (Fin N × Fin N) k} (hP : P ∈ polySections (fun i => lam i + c)) :
    ∃ Q, Q ∈ polySections lam ∧ P = (detPoly N k) ^ c * Q := by
  have hanti : Antitone (fun i => lam i + c) := fun i j hij => Nat.add_le_add_right (hlam hij) c
  have hfull : detTwist lam c k = polySections (fun i => lam i + c) :=
    polySections_irreducible hanti (detTwist_le c) (detTwist_isGStable lam c)
      (detTwist_ne_bot hlam c)
  rw [← hfull] at hP
  obtain ⟨Q, hQ, hPQ⟩ := hP
  exact ⟨Q, hQ, hPQ.symm⟩

end GaloisForLFunctions.HTGeometry.BorelWeil
