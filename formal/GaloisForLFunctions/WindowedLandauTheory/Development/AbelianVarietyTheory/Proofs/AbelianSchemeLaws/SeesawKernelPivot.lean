import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! A nonzero coordinate of a one-dimensional fibre kernel gives a determinantal neighborhood. -/

noncomputable section

namespace GlobalTheory.AbLaw.Seesaw

private theorem exists_minor {K m n : Type} [Field K] [Fintype m] [Fintype n] [DecidableEq n]
    (A : Matrix m n K) (hA : ∀ w, A.mulVec w = 0 → w = 0) :
    ∃ ρ : n → m, (A.submatrix ρ id).det ≠ 0 := by
  classical
  obtain ⟨L, hL⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' A)
    (LinearMap.ker_eq_bot'.2 fun w hw => hA w (by simpa using hw))
  have h1 : LinearMap.toMatrix' L * A = 1 := by
    have := congrArg LinearMap.toMatrix' hL
    rwa [LinearMap.toMatrix'_comp, LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at this
  by_contra! hzero
  let B := LinearMap.toMatrix' L
  have h2 : (B * A).det = ∑ ρ : n → m, (∏ i, B i (ρ i)) * (A.submatrix ρ id).det := by
    have e : B * A = fun i => ∑ j, B i j • A j := by
      ext i k
      simp [Matrix.mul_apply, Finset.sum_apply]
    have := (Matrix.detRowAlternating (n := n) (R := K)).toMultilinearMap.map_sum
      (fun i j => B i j • A j)
    rw [e]
    refine this.trans (Finset.sum_congr rfl fun ρ _ => ?_)
    exact (Matrix.detRowAlternating (n := n) (R := K)).toMultilinearMap.map_smul_univ _ _
  change B * A = 1 at h1
  rw [h1, Matrix.det_one] at h2
  simp [hzero] at h2

/-- After inverting a minor nonzero on the fibre, every kernel vector is proportional to one
fixed vector. The adjugate gives this vector uniformly under change of coefficient ring. -/
theorem exists_kernel_vector {R K : Type} [CommRing R] [Field K] (g₀ : R →+* K)
    {a b : ℕ} (D : Matrix (Fin b) (Fin a) R) (v : Fin a → K) (hv : v ≠ 0)
    (hker : ∀ w, (D.map g₀).mulVec w = 0 → ∃ c : K, w = c • v) :
    ∃ (δ : R) (v₀ : Fin a → R), g₀ δ ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'),
      IsUnit (g δ) → ∀ w, (D.map g).mulVec w = 0 → ∃ c : R', w = c • (g ∘ v₀) := by
  classical
  obtain ⟨k, hk⟩ := Function.ne_iff.1 hv
  let A : Matrix (Option (Fin b)) (Fin a) R := fun i => i.elim (Pi.single k 1) D
  have row (R' : Type) [CommRing R'] (g : R →+* R') (w : Fin a → R')
      (hw : (D.map g).mulVec w = 0) :
      (A.map g).mulVec w = fun i => w k * g (i.elim 1 fun _ => 0) := by
    funext i
    cases i with
    | none =>
      change ∑ x, g ((Pi.single k 1 : Fin a → R) x) * w x = w k * g 1
      simp only [Pi.single_apply, apply_ite g, map_one, map_zero, ite_mul, one_mul, zero_mul,
        Finset.sum_ite_eq', Finset.mem_univ, if_true, mul_one]
    | some i =>
      exact (congrFun hw i).trans ((congrArg (w k * ·) (map_zero g)).trans (mul_zero _)).symm
  obtain ⟨ρ, hρ⟩ := exists_minor (A.map g₀) (fun w hw => by
    have hD : (D.map g₀).mulVec w = 0 := funext fun i => congrFun hw (some i)
    have hk₀ := congrFun ((row K g₀ w hD).symm.trans hw) none
    obtain ⟨c, rfl⟩ := hker w hD
    have : c = 0 := by simpa [show v k ≠ 0 from hk] using hk₀
    simp [this])
  let N := A.submatrix ρ id
  let e : Fin a → R := fun j => (ρ j).elim 1 fun _ => 0
  refine ⟨N.det, N.adjugate.mulVec e, by rwa [RingHom.map_det], fun R' _ g hδ w hw => ?_⟩
  obtain ⟨u, hu⟩ := hδ
  have hN : (N.map g).mulVec w = w k • (g ∘ e) := funext fun j => congrFun (row R' g w hw) (ρ j)
  have hE : g ∘ N.adjugate.mulVec e = (N.map g).adjugate.mulVec (g ∘ e) := by
    funext j
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_adjugate]
    exact RingHom.map_mulVec g _ _ j
  have h := congrArg (N.map g).adjugate.mulVec hN
  rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.mulVec_smul, ← hE, Matrix.smul_mulVec,
    Matrix.one_mulVec, ← RingHom.mapMatrix_apply, ← RingHom.map_det, ← hu] at h
  refine ⟨u⁻¹.val * w k, ?_⟩
  rw [mul_smul, ← h, smul_smul, Units.inv_mul, one_smul]

end GlobalTheory.AbLaw.Seesaw
