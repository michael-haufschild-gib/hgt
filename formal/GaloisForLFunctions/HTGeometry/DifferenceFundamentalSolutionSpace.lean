import GaloisForLFunctions.HTGeometry.DifferenceGaloisMatrix

/-!
# A fundamental matrix carries the whole solution space

In a difference ring containing an invertible fundamental solution matrix `Y` of the system
`σ Y = B Y`, every solution of the system is `Y` applied to a vector of *constants*, and distinct
constant vectors give distinct solutions.  So the solution space is a free module of rank `n` over
the constants: exactly the rank of the system, and no more.

Together with `DifferenceSigmaSimple.isField_sigmaConstantsSubring_of_isSigmaSimple` — the
constants of a `σ`-simple ring form a field — this says the solution space inside a
Picard--Vessiot ring is an `n`-dimensional vector space over a field.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {R : Type*} [CommRing R] {n : ℕ}

/-- The difference operator transports a matrix-vector product coefficientwise. -/
theorem sigma_apply_mulVec (σR : R ≃+* R) (M : Matrix (Fin n) (Fin n) R) (v : Fin n → R) (i : Fin n) :
    σR ((M.mulVec v) i) = ((M.map (σR : R → R)).mulVec (fun j => σR (v j))) i := by
  simp [Matrix.mulVec, dotProduct, map_sum]

/-- Solutions of the first-order system with matrix `B`. -/
def IsSystemSolution (σR : R ≃+* R) (B : Matrix (Fin n) (Fin n) R) (v : Fin n → R) : Prop :=
  ∀ i, σR (v i) = (B.mulVec v) i

/-- The columns of a fundamental matrix are solutions. -/
theorem isSystemSolution_col (σR : R ≃+* R) (B Y : Matrix (Fin n) (Fin n) R)
    (hY : Y.map (σR : R → R) = B * Y) (j : Fin n) :
    IsSystemSolution σR B (fun i => Y i j) := by
  intro i
  have h := congrFun (congrFun hY i) j
  simpa [Matrix.map_apply, Matrix.mul_apply, Matrix.mulVec, dotProduct] using h

/-- **Every solution has constant coordinates in a fundamental matrix.** -/
theorem exists_constant_coords (σR : R ≃+* R) (B Y : Matrix (Fin n) (Fin n) R)
    [Invertible Y] [Invertible B] (hY : Y.map (σR : R → R) = B * Y)
    {v : Fin n → R} (hv : IsSystemSolution σR B v) :
    ∃ w : Fin n → R, (∀ i, σR (w i) = w i) ∧ v = Y.mulVec w := by
  classical
  refine ⟨(⅟Y).mulVec v, ?_, ?_⟩
  · intro i
    have hkey : (⅟Y).map (σR : R → R) * B = ⅟Y := by
      have h1 : ((⅟Y).map (σR : R → R) * B) * Y = 1 := by
        rw [mul_assoc, ← hY, ← Matrix.map_mul, invOf_mul_self]
        exact Matrix.map_one _ (map_zero _) (map_one _)
      calc (⅟Y).map (σR : R → R) * B
          = ((⅟Y).map (σR : R → R) * B * Y) * ⅟Y := by
            rw [mul_assoc, mul_invOf_self, mul_one]
        _ = ⅟Y := by rw [h1, one_mul]
    have hv' : (fun j => σR (v j)) = B.mulVec v := funext hv
    rw [sigma_apply_mulVec, hv', Matrix.mulVec_mulVec, hkey]
  · rw [Matrix.mulVec_mulVec, mul_invOf_self, Matrix.one_mulVec]

/-- **Constant coordinates are unique.** -/
theorem constant_coords_unique (Y : Matrix (Fin n) (Fin n) R) [Invertible Y]
    {w w' : Fin n → R} (h : Y.mulVec w = Y.mulVec w') : w = w' := by
  have := congrArg (fun u => (⅟Y).mulVec u) h
  simpa [Matrix.mulVec_mulVec, invOf_mul_self, Matrix.one_mulVec] using this

/-- **The solution space is exactly the constant span of a fundamental matrix.** -/
theorem isSystemSolution_iff_exists_constant_coords (σR : R ≃+* R)
    (B Y : Matrix (Fin n) (Fin n) R) [Invertible Y] [Invertible B]
    (hY : Y.map (σR : R → R) = B * Y) (v : Fin n → R) :
    IsSystemSolution σR B v ↔
      ∃ w : Fin n → R, (∀ i, σR (w i) = w i) ∧ v = Y.mulVec w := by
  refine ⟨exists_constant_coords σR B Y hY, ?_⟩
  rintro ⟨w, hw, rfl⟩
  intro i
  have hstep : ∀ j, σR ((Y.mulVec w) j) = ((Y.map (σR : R → R)).mulVec w) j := by
    intro j
    rw [sigma_apply_mulVec]
    congr 1
    exact funext fun k => hw k
  rw [hstep i, hY, ← Matrix.mulVec_mulVec]

end

end GaloisForLFunctions.HTGeometry
