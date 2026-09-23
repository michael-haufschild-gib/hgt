import GaloisForLFunctions.RHTower.CCMParityCompressionDeterminant

/-!
# Hankel sections of an atomic moment sequence

The corpus proves that positive weights on `n` distinct nodes make the order-`n` atomic moment
Hankel matrix positive definite, and, separately, that a *redundant* node packet with the nodes
themselves as weights has positive-definite monomial Gram sections.  What the short-interval prime
construction needs is the common generalization: independent positive weights on `N` nodes and a
Hankel section of any order `J ≤ #{distinct nodes}`.

The quadratic form is the weighted nodal polynomial energy, so positive definiteness is again
Vandermonde injectivity, and the Rayleigh bound turns a lower bound for that energy into a solution
bound for the linear system.
-/

noncomputable section

open Matrix Polynomial

namespace GaloisForLFunctions.HTGeometry

/-- The atomic moment Hankel section of order `J` built from `N` weighted nodes. -/
def atomicHankel {N : ℕ} (w x : Fin N → ℝ) (J : ℕ) : Matrix (Fin J) (Fin J) ℝ :=
  _root_.HTGeometry.momentHankelMatrix (RHTower.ccmAtomicMixedMoment w x) J

theorem atomicHankel_apply {N : ℕ} (w x : Fin N → ℝ) (J : ℕ) (i j : Fin J) :
    atomicHankel w x J i j = ∑ r : Fin N, w r * x r ^ ((i : ℕ) + (j : ℕ)) := by
  rw [atomicHankel, _root_.HTGeometry.momentHankelMatrix, RHTower.ccmAtomicMixedMoment]

theorem atomicHankel_isHermitian {N : ℕ} (w x : Fin N → ℝ) (J : ℕ) :
    (atomicHankel w x J).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  simp only [atomicHankel_apply, star_trivial]
  congr 1
  funext r
  rw [add_comm]

/-- **The Hankel quadratic form is the weighted nodal polynomial energy.** -/
theorem dotProduct_mulVec_atomicHankel {N J : ℕ} (w x : Fin N → ℝ) (a : Fin J → ℝ) :
    a ⬝ᵥ (atomicHankel w x J).mulVec a
      = ∑ r : Fin N, w r * (Polynomial.eval (x r) (Polynomial.ofFn J a)) ^ (2 : ℕ) := by
  have hpoly : ∀ r : Fin N,
      Polynomial.eval (x r) (Polynomial.ofFn J a) = ∑ i : Fin J, a i * x r ^ (i : ℕ) := by
    intro r
    rw [Polynomial.ofFn_eq_sum_monomial, Polynomial.eval_finsetSum]
    exact Finset.sum_congr rfl fun i _ => by rw [Polynomial.eval_monomial]
  have hlhs : a ⬝ᵥ (atomicHankel w x J).mulVec a
      = ∑ i : Fin J, ∑ j : Fin J, ∑ r : Fin N,
          w r * (a i * x r ^ (i : ℕ)) * (a j * x r ^ (j : ℕ)) := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hmv : (atomicHankel w x J).mulVec a i
        = ∑ j : Fin J, (∑ r : Fin N, w r * x r ^ ((i : ℕ) + (j : ℕ))) * a j := by
      rw [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun j _ => by rw [atomicHankel_apply]
    rw [hmv, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [pow_add]
    ring
  have hrhs : ∑ r : Fin N, w r * (Polynomial.eval (x r) (Polynomial.ofFn J a)) ^ (2 : ℕ)
      = ∑ r : Fin N, ∑ i : Fin J, ∑ j : Fin J,
          w r * (a i * x r ^ (i : ℕ)) * (a j * x r ^ (j : ℕ)) := by
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [hpoly r, sq, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hlhs, hrhs]
  calc ∑ i : Fin J, ∑ j : Fin J, ∑ r : Fin N,
        w r * (a i * x r ^ (i : ℕ)) * (a j * x r ^ (j : ℕ))
      = ∑ i : Fin J, ∑ r : Fin N, ∑ j : Fin J,
          w r * (a i * x r ^ (i : ℕ)) * (a j * x r ^ (j : ℕ)) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = ∑ r : Fin N, ∑ i : Fin J, ∑ j : Fin J,
          w r * (a i * x r ^ (i : ℕ)) * (a j * x r ^ (j : ℕ)) := Finset.sum_comm

/-- **Positive weights and enough distinct nodes make the Hankel section strict.** -/
theorem atomicHankel_posDef {N J : ℕ} (hJ : 0 < J) (w x : Fin N → ℝ) (hw : ∀ r, 0 < w r)
    (hcard : J ≤ ((Finset.univ : Finset (Fin N)).image x).card) :
    (atomicHankel w x J).PosDef := by
  classical
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  refine ⟨atomicHankel_isHermitian w x J, ?_⟩
  intro a ha
  rw [star_trivial, dotProduct_mulVec_atomicHankel]
  set p : Polynomial ℝ := Polynomial.ofFn J a with hpdef
  have hp : p ≠ 0 := by
    intro hp0
    apply ha
    apply Polynomial.injective_ofFn J
    simpa [hpdef] using hp0
  have hnonneg : 0 ≤ ∑ r : Fin N, w r * Polynomial.eval (x r) p ^ (2 : ℕ) :=
    Finset.sum_nonneg fun r _ => mul_nonneg (hw r).le (sq_nonneg _)
  refine lt_of_le_of_ne hnonneg ?_
  intro hzero
  have heach : ∀ r : Fin N, Polynomial.eval (x r) p = 0 := by
    intro r
    have hr := (Finset.sum_eq_zero_iff_of_nonneg fun s (_ : s ∈
        (Finset.univ : Finset (Fin N))) =>
      mul_nonneg (hw s).le (sq_nonneg (Polynomial.eval (x s) p))).mp
        (by simpa only [hpdef] using hzero.symm) r (Finset.mem_univ r)
    rcases mul_eq_zero.mp hr with hxr | hsquare
    · exact False.elim ((hw r).ne' hxr)
    · exact sq_eq_zero_iff.mp hsquare
  set T : Finset ℝ := (Finset.univ : Finset (Fin N)).image x with hTdef
  have heval : ∀ t : T, Polynomial.eval (t : ℝ) p = 0 := by
    intro t
    obtain ⟨r, _, hr⟩ := Finset.mem_image.mp t.property
    simpa only [hr] using heach r
  apply hp
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero
    p (f := fun t : T => (t : ℝ)) Subtype.val_injective heval
  exact (Polynomial.ofFn_natDegree_lt hJ a).trans_le (by simpa [hTdef] using hcard)

/-- **Rayleigh solvability.**  A uniform quadratic lower bound solves the linear system with an
explicit size bound on the solution. -/
theorem exists_solve_atomicHankel {N J : ℕ} (w x : Fin N → ℝ) {lam : ℝ} (hlam : 0 < lam)
    (hquad : ∀ a : Fin J → ℝ, lam * (∑ i, a i ^ (2 : ℕ)) ≤ a ⬝ᵥ (atomicHankel w x J).mulVec a)
    (ξ : Fin J → ℝ) :
    ∃ c : Fin J → ℝ, (atomicHankel w x J).mulVec c = ξ ∧
      lam ^ (2 : ℕ) * (∑ i, c i ^ (2 : ℕ)) ≤ ∑ i, ξ i ^ (2 : ℕ) := by
  classical
  have hpd : (atomicHankel w x J).PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨atomicHankel_isHermitian w x J, ?_⟩
    intro a ha
    have hsum : 0 < ∑ i, a i ^ (2 : ℕ) := by
      rcases Function.ne_iff.mp ha with ⟨i, hi⟩
      refine Finset.sum_pos' (fun j _ => sq_nonneg _) ⟨i, Finset.mem_univ i, ?_⟩
      exact pow_pos (abs_pos.mpr hi) 2 |>.trans_le (le_of_eq (sq_abs _))
    rw [star_trivial]
    exact lt_of_lt_of_le (mul_pos hlam hsum) (hquad a)
  have hdet : (atomicHankel w x J).det ≠ 0 := ne_of_gt hpd.det_pos
  refine ⟨(atomicHankel w x J)⁻¹.mulVec ξ, ?_, ?_⟩
  · rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  · set c : Fin J → ℝ := (atomicHankel w x J)⁻¹.mulVec ξ with hcdef
    have hMc : (atomicHankel w x J).mulVec c = ξ := by
      rw [hcdef, Matrix.mulVec_mulVec,
        Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hdet), Matrix.one_mulVec]
    have hlow := hquad c
    rw [hMc] at hlow
    have hCS : (∑ i, c i * ξ i) ^ (2 : ℕ) ≤ (∑ i, c i ^ (2 : ℕ)) * ∑ i, ξ i ^ (2 : ℕ) :=
      Finset.sum_mul_sq_le_sq_mul_sq Finset.univ c ξ
    have hdot : c ⬝ᵥ ξ = ∑ i, c i * ξ i := rfl
    rw [hdot] at hlow
    have hSc : 0 ≤ ∑ i, c i ^ (2 : ℕ) := Finset.sum_nonneg fun i _ => sq_nonneg _
    have hSx : 0 ≤ ∑ i, ξ i ^ (2 : ℕ) := Finset.sum_nonneg fun i _ => sq_nonneg _
    rcases eq_or_lt_of_le hSc with hzero | hpos
    · rw [← hzero]
      simpa using hSx
    · have hdotpos : 0 < ∑ i, c i * ξ i := lt_of_lt_of_le (mul_pos hlam hpos) hlow
      have hsq : (lam * ∑ i, c i ^ (2 : ℕ)) ^ (2 : ℕ) ≤ (∑ i, c i * ξ i) ^ (2 : ℕ) := by
        nlinarith [hlow, mul_pos hlam hpos, hdotpos]
      nlinarith [hsq, hCS, hpos]

end GaloisForLFunctions.HTGeometry

end
