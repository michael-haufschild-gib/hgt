import GaloisForLFunctions.HTGeometry.CommutingTermTemporalRankBound
import Mathlib

/-!
# Every eigenvalue of a commuting Hermitian sum splits

For pairwise commuting Hermitian matrices, each eigenvalue of the sum is a sum of eigenvalues of
the summands.  The proof needs no simultaneous eigenbasis: in the eigenbasis of one summand the
other is block diagonal across equal eigenvalues, so restricting an eigenvector of the sum to one
eigenvalue block of the first summand produces a joint eigenvector of both.

Consequently a Hamiltonian written as `m` commuting terms with at most four levels each — for
instance two-qubit terms — has anchored temporal rank at most `3 m`, linear rather than
exponential in the number of sites.
-/

open Matrix
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A nonzero eigenvector exhibits its eigenvalue in the Hermitian eigenvalue list. -/
theorem exists_eigenvalues_eq_of_mulVec {B : Matrix n n ℂ} (hB : B.IsHermitian)
    {mu : ℝ} {w : n → ℂ} (hw : w ≠ 0) (hBw : B *ᵥ w = (mu : ℂ) • w) :
    ∃ i, hB.eigenvalues i = mu := by
  classical
  set V : Matrix n n ℂ := (hB.eigenvectorUnitary : Matrix n n ℂ) with hV
  have hVstar : star V * V = 1 := UnitaryGroup.star_mul_self _
  have hVmul : V * star V = 1 := by
    have := (Matrix.mem_unitaryGroup_iff (A := (hB.eigenvectorUnitary : Matrix n n ℂ))).mp
      (hB.eigenvectorUnitary).2
    simpa [hV] using this
  set x : n → ℂ := star V *ᵥ w with hx
  have hxne : x ≠ 0 := by
    intro hzero
    apply hw
    have : V *ᵥ x = w := by
      rw [hx, Matrix.mulVec_mulVec, hVmul, Matrix.one_mulVec]
    rw [hzero, Matrix.mulVec_zero] at this
    exact this.symm
  have hspec : B = V * Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues) * star V :=
    hB.spectral_theorem
  have hconj : star V * B * V = Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues) := by
    conv_lhs => rw [hspec]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hVstar, Matrix.one_mul,
      Matrix.mul_assoc, hVstar, Matrix.mul_one]
  have hdiag : Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues) *ᵥ x = (mu : ℂ) • x := by
    have hwx : V *ᵥ x = w := by
      rw [hx, Matrix.mulVec_mulVec, hVmul, Matrix.one_mulVec]
    calc Matrix.diagonal (RCLike.ofReal ∘ hB.eigenvalues) *ᵥ x
        = (star V * B * V) *ᵥ x := by rw [hconj]
      _ = star V *ᵥ (B *ᵥ (V *ᵥ x)) := by
          simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = star V *ᵥ (B *ᵥ w) := by rw [hwx]
      _ = (mu : ℂ) • x := by rw [hBw, Matrix.mulVec_smul, hx]
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
    by_contra hcon
    exact hxne (funext fun i => not_not.mp (fun h => hcon ⟨i, h⟩))
  refine ⟨i, ?_⟩
  have := congrFun hdiag i
  simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul, Function.comp_apply] at this
  have hcast : ((hB.eigenvalues i : ℝ) : ℂ) = ((mu : ℝ) : ℂ) := by
    have hfac : (((hB.eigenvalues i : ℝ) : ℂ) - ((mu : ℝ) : ℂ)) * x i = 0 := by
      rw [sub_mul, this]; ring
    rcases mul_eq_zero.mp hfac with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hi
  exact_mod_cast hcast

/-- **Commuting Hermitian eigenvalue splitting.**  For a commuting Hermitian pair, every
eigenvector of the sum yields a joint eigenvector, so the eigenvalue splits. -/
theorem exists_joint_eigenvector_of_commute
    {A B : Matrix n n ℂ} (hA : A.IsHermitian) (hcomm : A * B = B * A)
    {E : ℝ} {v : n → ℂ} (hv : v ≠ 0) (hEv : (A + B) *ᵥ v = (E : ℂ) • v) :
    ∃ (lam : ℝ) (w : n → ℂ), w ≠ 0 ∧ (∃ i, hA.eigenvalues i = lam) ∧
      A *ᵥ w = (lam : ℂ) • w ∧ B *ᵥ w = ((E - lam : ℝ) : ℂ) • w := by
  classical
  set V : Matrix n n ℂ := (hA.eigenvectorUnitary : Matrix n n ℂ) with hV
  have hVstar : star V * V = 1 := UnitaryGroup.star_mul_self _
  have hVmul : V * star V = 1 := by
    have := (Matrix.mem_unitaryGroup_iff (A := (hA.eigenvectorUnitary : Matrix n n ℂ))).mp
      (hA.eigenvectorUnitary).2
    simpa [hV] using this
  set eig : n → ℝ := hA.eigenvalues with heig
  set C : Matrix n n ℂ := Matrix.diagonal (RCLike.ofReal ∘ eig) with hC
  set D : Matrix n n ℂ := star V * B * V with hD
  have hspec : A = V * C * star V := hA.spectral_theorem
  -- the conjugated pair still commutes
  have hCD : C * D = D * C := by
    have hAV : star V * A * V = C := by
      conv_lhs => rw [hspec]
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hVstar, Matrix.one_mul,
        Matrix.mul_assoc, hVstar, Matrix.mul_one]
    calc C * D = (star V * A * V) * (star V * B * V) := by rw [hAV]
      _ = star V * A * (V * star V) * B * V := by noncomm_ring
      _ = star V * (A * B) * V := by rw [hVmul]; noncomm_ring
      _ = star V * (B * A) * V := by rw [hcomm]
      _ = star V * B * (V * star V) * A * V := by rw [hVmul]; noncomm_ring
      _ = (star V * B * V) * (star V * A * V) := by noncomm_ring
      _ = D * C := by rw [hAV]
  have hblock : ∀ i j, eig i ≠ eig j → D i j = 0 := by
    intro i j hij
    have hcd := congrFun (congrFun hCD i) j
    simp only [hC, Matrix.diagonal_mul, Matrix.mul_diagonal, Function.comp_apply] at hcd
    have hne : ((eig i : ℝ) : ℂ) - ((eig j : ℝ) : ℂ) ≠ 0 := by
      simp only [sub_ne_zero]
      exact_mod_cast hij
    have : (((eig i : ℝ) : ℂ) - ((eig j : ℝ) : ℂ)) * D i j = 0 := by
      rw [sub_mul, hcd]; ring
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hne
    · exact h
  -- transport the eigenvector
  set x : n → ℂ := star V *ᵥ v with hx
  have hxv : V *ᵥ x = v := by rw [hx, Matrix.mulVec_mulVec, hVmul, Matrix.one_mulVec]
  have hxne : x ≠ 0 := by
    intro hzero
    apply hv
    rw [← hxv, hzero, Matrix.mulVec_zero]
  have hCDx : (C + D) *ᵥ x = (E : ℂ) • x := by
    have hconj : star V * (A + B) * V = C + D := by
      have hAV : star V * A * V = C := by
        conv_lhs => rw [hspec]
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hVstar, Matrix.one_mul,
          Matrix.mul_assoc, hVstar, Matrix.mul_one]
      rw [Matrix.add_mul, Matrix.mul_add, hAV, hD]
    have := congrArg (fun u => star V *ᵥ u) hEv
    simp only at this
    rw [Matrix.mulVec_smul] at this
    rw [← hconj]
    calc (star V * (A + B) * V) *ᵥ x
        = star V *ᵥ ((A + B) *ᵥ (V *ᵥ x)) := by
          simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = star V *ᵥ ((A + B) *ᵥ v) := by rw [hxv]
      _ = (E : ℂ) • x := by rw [this]; rfl
  obtain ⟨i0, hi0⟩ : ∃ i, x i ≠ 0 := by
    by_contra hcon
    exact hxne (funext fun i => not_not.mp (fun h => hcon ⟨i, h⟩))
  set lam : ℝ := eig i0 with hlam
  set y : n → ℂ := fun i => if eig i = lam then x i else 0 with hy
  have hyne : y ≠ 0 := by
    intro hzero
    apply hi0
    have := congrFun hzero i0
    simpa [hy, hlam] using this
  have hCy : C *ᵥ y = (lam : ℂ) • y := by
    funext i
    simp only [hC, Matrix.mulVec_diagonal, Function.comp_apply, Pi.smul_apply, smul_eq_mul, hy]
    by_cases hi : eig i = lam
    · simp [hi]
    · simp [hi]
  have hDy : D *ᵥ y = ((E - lam : ℝ) : ℂ) • y := by
    funext i
    have hsum : (D *ᵥ y) i = ∑ j, D i j * y j := rfl
    by_cases hi : eig i = lam
    · have hDx : (D *ᵥ y) i = (D *ᵥ x) i := by
        rw [hsum]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases hj : eig j = lam
        · simp [hy, hj]
        · have : D i j = 0 := hblock i j (by rw [hi]; exact fun hcon => hj hcon.symm)
          simp [hy, hj, this]
      have hCx := congrFun hCDx i
      simp only [Matrix.add_mulVec, Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hCx
      have hCxi : (C *ᵥ x) i = ((eig i : ℝ) : ℂ) * x i := by
        simp [hC, Matrix.mulVec_diagonal]
      rw [hCxi, hi] at hCx
      have hyi : y i = x i := by simp [hy, hi]
      rw [hDx, hyi]
      have : (D *ᵥ x) i = (E : ℂ) * x i - ((lam : ℝ) : ℂ) * x i := by linear_combination hCx
      rw [this]
      push_cast
      ring
    · have hzero : (D *ᵥ y) i = 0 := by
        rw [hsum]
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hj : eig j = lam
        · have : D i j = 0 := hblock i j (by rw [hj]; exact hi)
          simp [this]
        · simp [hy, hj]
      have hyi : y i = 0 := by simp [hy, hi]
      rw [hzero, hyi]
      simp
  refine ⟨lam, V *ᵥ y, ?_, ⟨i0, rfl⟩, ?_, ?_⟩
  · intro hcon
    apply hyne
    have : star V *ᵥ (V *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, hVstar, Matrix.one_mulVec]
    rw [hcon, Matrix.mulVec_zero] at this
    exact this.symm
  · calc A *ᵥ (V *ᵥ y) = (V * C * star V * V) *ᵥ y := by
          rw [hspec]; simp [Matrix.mulVec_mulVec, Matrix.mul_assoc]
      _ = (V * C) *ᵥ y := by rw [Matrix.mul_assoc, hVstar, Matrix.mul_one]
      _ = V *ᵥ (C *ᵥ y) := by rw [Matrix.mulVec_mulVec]
      _ = (lam : ℂ) • (V *ᵥ y) := by rw [hCy, Matrix.mulVec_smul]
  · calc B *ᵥ (V *ᵥ y) = (B * V) *ᵥ y := by rw [Matrix.mulVec_mulVec]
      _ = (V * (star V * B * V)) *ᵥ y := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hVmul, Matrix.one_mul]
      _ = V *ᵥ (D *ᵥ y) := by rw [← hD, Matrix.mulVec_mulVec]
      _ = ((E - lam : ℝ) : ℂ) • (V *ᵥ y) := by rw [hDy, Matrix.mulVec_smul]

end

end GaloisForLFunctions.HTGeometry
