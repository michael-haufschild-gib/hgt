import Mathlib

/-!
# The evaluation lemma for linearly independent polynomials

The elementary evaluation lemma of the affine-jet packet-collision argument
(`affine-jet-packet-collision-completeness`, step (11)): a `K`-linearly independent finite family of
multivariate polynomials over an infinite field admits evaluation points at which the sampling matrix
is nonsingular.  This is exactly what turns "the decorated monomials are linearly independent
polynomials" into "the evaluation determinant `Δ_S` can be made nonzero", so that the finitely many
determinant conditions certify linear independence of the associated analytic functions.

The proof is the classical induction on the family size.  At the inductive step, the polynomial

`g(x) = det (matrix whose last column is the tuple (fᵢ) and whose other columns are constant
        evaluations of the fᵢ at the previously chosen points q₁,…,qₙ)`

is, by column-linearity of the determinant (`Matrix.cramer`), a `K`-linear combination `∑ᵢ (det Nᵢ)·fᵢ`
whose coefficient of `f_last` is the previous nonsingular determinant, hence nonzero; linear
independence makes `g ≠ 0`, and a nonzero polynomial over an infinite field has a nonvanishing point,
supplying the next evaluation point.
-/

open MvPolynomial Matrix

namespace AffineJet

variable {K : Type*} [Field K] [Infinite K] {σ : Type*}

/-- A nonzero multivariate polynomial over an infinite field has a nonvanishing evaluation point. -/
theorem exists_eval_ne_zero {p : MvPolynomial σ K} (hp : p ≠ 0) :
    ∃ x : σ → K, eval x p ≠ 0 := by
  by_contra h
  simp only [not_exists, not_not] at h
  exact hp (MvPolynomial.funext (fun x => by rw [h x, map_zero]))

/-- **Evaluation lemma.** A `K`-linearly independent family `f : Fin n → MvPolynomial σ K` over an
infinite field `K` admits evaluation points `p : Fin n → (σ → K)` at which the evaluation matrix
`(eval (p j) (f i))` is nonsingular. -/
theorem exists_eval_matrix_det_ne_zero :
    ∀ (n : ℕ) (f : Fin n → MvPolynomial σ K), LinearIndependent K f →
      ∃ p : Fin n → (σ → K), (Matrix.of fun i j => eval (p j) (f i)).det ≠ 0 := by
  intro n
  induction n with
  | zero => intro f _; exact ⟨Fin.elim0, by simp⟩
  | succ n ih =>
    intro f hf
    have hinit : LinearIndependent K (f ∘ Fin.castSucc) :=
      hf.comp Fin.castSucc (Fin.castSucc_injective n)
    obtain ⟨q, hq⟩ := ih (f ∘ Fin.castSucc) hinit
    set M : Matrix (Fin (n+1)) (Fin (n+1)) (MvPolynomial σ K) :=
      Matrix.of fun i j => Fin.lastCases (f i) (fun j' => C (eval (q j') (f i))) j with hMdef
    have hM_last : ∀ i, M i (Fin.last n) = f i := by intro i; simp [hMdef]
    set N : Fin (n+1) → Matrix (Fin (n+1)) (Fin (n+1)) K :=
      fun i₀ => Matrix.of fun i j =>
        Fin.lastCases (if i₀ = i then (1:K) else 0) (fun j' => eval (q j') (f i)) j with hNdef
    have hcoef : ∀ i₀, (M.cramer (Pi.single i₀ (1 : MvPolynomial σ K))) (Fin.last n)
        = C ((N i₀).det) := by
      intro i₀
      rw [cramer_apply]
      have hmat : M.updateCol (Fin.last n) (Pi.single i₀ (1 : MvPolynomial σ K))
          = (MvPolynomial.C (σ := σ) (R := K)).mapMatrix (N i₀) := by
        funext i j
        induction j using Fin.lastCases with
        | last =>
            simp only [Matrix.updateCol_self, RingHom.mapMatrix_apply, Matrix.map_apply, hNdef,
              Matrix.of_apply, Fin.lastCases_last, Pi.single_apply,
              apply_ite (MvPolynomial.C (σ := σ) (R := K)), map_one, map_zero]
            by_cases h : i = i₀
            · subst h; simp
            · rw [if_neg h, if_neg (fun h' => h h'.symm)]
        | cast j' =>
            have hne : (Fin.castSucc j') ≠ Fin.last n := (Fin.castSucc_lt_last j').ne
            simp only [Matrix.updateCol_ne hne, RingHom.mapMatrix_apply, Matrix.map_apply, hMdef,
              hNdef, Matrix.of_apply, Fin.lastCases_castSucc]
      rw [hmat, ← RingHom.map_det]
    have hcomb : M.det = ∑ i₀, ((N i₀).det) • f i₀ := by
      have hb : (fun i => f i) = ∑ i₀, (f i₀) • Pi.single i₀ (1 : MvPolynomial σ K) := by
        funext k
        rw [Finset.sum_apply]
        simp [Pi.single_apply, Finset.sum_ite_eq]
      have hself : M.updateCol (Fin.last n) (fun i => f i) = M := by
        have he : (fun i => f i) = (fun j => M j (Fin.last n)) := by funext j; rw [hM_last]
        rw [he]; exact Matrix.updateCol_eq_self M (Fin.last n)
      have hMdet : M.det = (M.cramer (fun i => f i)) (Fin.last n) := by
        rw [cramer_apply, hself]
      rw [hMdet, hb, map_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl (fun i₀ _ => ?_)
      rw [map_smul, Pi.smul_apply, hcoef i₀, smul_eq_mul, MvPolynomial.smul_eq_C_mul]
      ring
    have hsub : (N (Fin.last n)).submatrix (Fin.last n).succAbove (Fin.last n).succAbove
        = Matrix.of fun i j => eval (q j) ((f ∘ Fin.castSucc) i) := by
      funext i' j'
      simp only [Fin.succAbove_last, Matrix.submatrix_apply, hNdef, Matrix.of_apply,
        Fin.lastCases_castSucc, Function.comp_apply]
    have hval : (N (Fin.last n)) (Fin.last n) (Fin.last n) = 1 := by simp [hNdef]
    have hsign : ((-1 : K)) ^ ((Fin.last n : ℕ) + (Fin.last n : ℕ)) = 1 := by
      rw [Fin.val_last]; exact Even.neg_one_pow ⟨n, by ring⟩
    have hterm0 : ∀ i ∈ Finset.univ, i ≠ Fin.last n →
        (-1:K)^((i:ℕ)+(Fin.last n:ℕ)) * (N (Fin.last n)) i (Fin.last n)
          * ((N (Fin.last n)).submatrix i.succAbove (Fin.last n).succAbove).det = 0 := by
      intro i _ hi
      have h0 : (N (Fin.last n)) i (Fin.last n) = 0 := by
        simp only [hNdef, Matrix.of_apply, Fin.lastCases_last]; rw [if_neg (fun h => hi h.symm)]
      rw [h0]; ring
    have hExp : (N (Fin.last n)).det
        = (-1:K)^((Fin.last n:ℕ)+(Fin.last n:ℕ)) * (N (Fin.last n)) (Fin.last n) (Fin.last n)
          * ((N (Fin.last n)).submatrix (Fin.last n).succAbove (Fin.last n).succAbove).det := by
      rw [Matrix.det_succ_column (N (Fin.last n)) (Fin.last n)]
      exact Finset.sum_eq_single_of_mem (Fin.last n) (Finset.mem_univ _) hterm0
    have hdetN : (N (Fin.last n)).det ≠ 0 := by
      rw [hExp, hval, hsign, hsub, one_mul, one_mul]; exact hq
    have hgne : M.det ≠ 0 := by
      rw [hcomb]
      intro hzero
      exact hdetN (Fintype.linearIndependent_iff.mp hf (fun i₀ => (N i₀).det) hzero (Fin.last n))
    obtain ⟨x, hx⟩ := exists_eval_ne_zero hgne
    refine ⟨Fin.snoc q x, ?_⟩
    have hfinal : (Matrix.of fun i j =>
        eval ((Fin.snoc q x : Fin (n + 1) → (σ → K)) j) (f i)).det = eval x M.det := by
      rw [RingHom.map_det]
      congr 1
      funext i j
      induction j using Fin.lastCases with
      | last =>
          simp only [Fin.snoc_last, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
            hMdef, Fin.lastCases_last]
      | cast j' =>
          simp only [Fin.snoc_castSucc, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
            hMdef, Fin.lastCases_castSucc, eval_C]
    rw [hfinal]; exact hx

/-- **Linear independence of evaluated polynomials.**  A `K`-linearly independent family of
multivariate polynomials over an infinite field is linearly independent as a family of functions
`(σ → K) → K` under evaluation.  This is the conclusion the affine-jet argument extracts from the
nonsingular evaluation matrix: a vanishing `K`-combination of the evaluation functions, sampled at the
points supplied by `exists_eval_matrix_det_ne_zero`, lies in the kernel of a nonsingular matrix, hence
is zero. -/
theorem linearIndependent_eval {n : ℕ} {f : Fin n → MvPolynomial σ K}
    (hf : LinearIndependent K f) :
    LinearIndependent K (fun i => (fun x : σ → K => eval x (f i))) := by
  obtain ⟨p, hp⟩ := exists_eval_matrix_det_ne_zero n f hf
  rw [Fintype.linearIndependent_iff]
  intro c hc
  set M : Matrix (Fin n) (Fin n) K := Matrix.of fun i j => eval (p j) (f i) with hM
  have hvec : c ᵥ* M = 0 := by
    funext j
    have hcj := congrFun hc (p j)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hcj
    simp only [Matrix.vecMul, dotProduct, hM, Matrix.of_apply, Pi.zero_apply]
    exact hcj
  have hc0 : c = 0 := eq_zero_of_vecMul_eq_zero hp hvec
  intro i
  exact congrFun hc0 i

end AffineJet
