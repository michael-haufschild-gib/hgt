import GaloisForLFunctions.HTGeometry.ReducedDiagonalBound

/-!
# Finiteness of Gram values

The Gram determinants of integral frames in a fixed positive definite form take only finitely many
values below any bound.  Reducing the frame by the integral reduction theory one dimension down does
not change the determinant, and after reduction the columns of the frame have bounded length: the
leading minors are bounded below by the ellipticity of the ambient form together with the
integrality of the standard Gram matrix, the determinant is bounded above by hypothesis, and the
Siegel ordering turns those two into a bound on each Jacobi diagonal entry, hence on each diagonal
entry of the Gram matrix, which is the length of a column.

This is the termination input of reduction theory over an order, where no Lovász swap can contract
the potential.

* `intGram` : the Gram matrix of an integral frame.
* `finite_intGram_values` : **finitely many Gram values below a bound.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {N k : ℕ}

/-- An integral frame, read over `ℝ`. -/
def intFrame (Z : Matrix (Fin N) (Fin k) ℤ) : Matrix (Fin N) (Fin k) ℝ :=
  Z.map (fun z : ℤ => (z : ℝ))

theorem intFrame_mul (Z : Matrix (Fin N) (Fin k) ℤ) (g : Matrix (Fin k) (Fin k) ℤ) :
    intFrame (Z * g) = intFrame Z * g.map (fun z : ℤ => (z : ℝ)) := by
  classical
  ext p i
  show ((Z * g) p i : ℝ) = _
  rw [Matrix.mul_apply, Matrix.mul_apply]
  push_cast
  exact Finset.sum_congr rfl fun m _ => rfl

/-- The Gram matrix of an integral frame. -/
def intGram (A : Matrix (Fin N) (Fin N) ℝ) (Z : Matrix (Fin N) (Fin k) ℤ) :
    Matrix (Fin k) (Fin k) ℝ :=
  (intFrame Z)ᵀ * A * intFrame Z

theorem intGram_mul (A : Matrix (Fin N) (Fin N) ℝ) (Z : Matrix (Fin N) (Fin k) ℤ)
    (g : Matrix (Fin k) (Fin k) ℤ) :
    intGram A (Z * g)
      = (g.map (fun z : ℤ => (z : ℝ)))ᵀ * intGram A Z * (g.map (fun z : ℤ => (z : ℝ))) := by
  rw [intGram, intGram, intFrame_mul, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

theorem intGram_diag (A : Matrix (Fin N) (Fin N) ℝ) (Z : Matrix (Fin N) (Fin k) ℤ) (i : Fin k) :
    intGram A Z i i
      = (fun p => ((Z p i : ℤ) : ℝ)) ⬝ᵥ (A *ᵥ fun p => ((Z p i : ℤ) : ℝ)) := by
  classical
  show ((intFrame Z)ᵀ * A * intFrame Z) i i = _
  rw [Matrix.mul_apply]
  have hstep : ∀ q : Fin N, ((intFrame Z)ᵀ * A) i q = ∑ p, ((Z p i : ℤ) : ℝ) * A p q := by
    intro q
    rw [Matrix.mul_apply]
    exact Finset.sum_congr rfl fun p _ => rfl
  show (∑ q, ((intFrame Z)ᵀ * A) i q * intFrame Z q i) = ∑ p, _
  calc (∑ q, ((intFrame Z)ᵀ * A) i q * intFrame Z q i)
      = ∑ q, ∑ p, ((Z p i : ℤ) : ℝ) * A p q * ((Z q i : ℤ) : ℝ) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [hstep q, Finset.sum_mul]
        rfl
    _ = ∑ p, ∑ q, ((Z p i : ℤ) : ℝ) * A p q * ((Z q i : ℤ) : ℝ) := Finset.sum_comm
    _ = ∑ p, ((Z p i : ℤ) : ℝ) * ∑ q, A p q * ((Z q i : ℤ) : ℝ) := by
        refine Finset.sum_congr rfl fun p _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun q _ => by ring

/-- **Finitely many Gram values below a bound.** -/
theorem finite_intGram_values {A : Matrix (Fin N) (Fin N) ℝ} (hA : A.PosDef) (hN : 0 < N)
    (B : ℝ) :
    {r : ℝ | ∃ Z : Matrix (Fin N) (Fin k) ℤ, (intGram A Z).PosDef
      ∧ (intGram A Z).det ≤ B ∧ r = (intGram A Z).det}.Finite := by
  classical
  have hsymm : A ∈ symmMatrices N := by
    show Aᵀ = A
    have h : Aᴴ = A := hA.isHermitian
    rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  set P : posDefCone N := ⟨⟨A, hsymm⟩, hA⟩ with hP
  obtain ⟨lam₀, hlam₀, hell⟩ := exists_ellipticity hA hN
  set lam : ℝ := min lam₀ 1 with hlamdef
  have hlam : 0 < lam := lt_min hlam₀ zero_lt_one
  have hlam1 : lam ≤ 1 := min_le_right _ _
  have hell' : ∀ v : Fin N → ℝ, lam * (v ⬝ᵥ v) ≤ v ⬝ᵥ (A *ᵥ v) := by
    intro v
    refine le_trans (mul_le_mul_of_nonneg_right (min_le_left lam₀ 1) ?_) (hell v)
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  set Dmax : ℝ := max 1 (2 ^ (k * k) * B / lam ^ k) with hDmax
  set Bcol : ℝ := (k : ℝ) * 1 ^ 2 * 2 ^ k * Dmax with hBcol
  have hSfin : {w : Fin N → ℤ | quadForm P (intVec w) ≤ Bcol}.Finite :=
    finite_latticePoints_le P hN Bcol
  have hpi : {W : Fin k → (Fin N → ℤ) | ∀ i, quadForm P (intVec (W i)) ≤ Bcol}.Finite := by
    have heq : {W : Fin k → (Fin N → ℤ) | ∀ i, quadForm P (intVec (W i)) ≤ Bcol}
        = Set.pi Set.univ (fun _ : Fin k => {w : Fin N → ℤ | quadForm P (intVec w) ≤ Bcol}) := by
      ext W
      constructor
      · intro h i _
        exact h i
      · intro h i
        exact h i (Set.mem_univ i)
    rw [heq]
    exact Set.Finite.pi fun _ => hSfin
  refine Set.Finite.subset (hpi.image
    (fun W : Fin k → (Fin N → ℤ) => (intGram A (Matrix.of fun p i => W i p)).det)) ?_
  rintro r ⟨Z, hZpos, hZdet, rfl⟩
  obtain ⟨g, J, hgdet, hJform, hJS⟩ := exists_siegel_inOrbit_det_one hZpos
  set W : Matrix (Fin N) (Fin k) ℤ := Z * g with hW
  have hgcast : (g.map (fun z : ℤ => (z : ℝ))).det = 1 := by
    have h : (g.map (fun z : ℤ => (z : ℝ))).det = ((g.det : ℤ) : ℝ) :=
      (RingHom.map_det (Int.castRingHom ℝ) g).symm
    rw [h, hgdet]
    norm_num
  have hJW : J.form = intGram A W := by rw [hW, intGram_mul, hJform]
  have hdetJ : J.form.det = (intGram A Z).det := by
    rw [hJform, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hgcast]
    ring
  have hinjW : ∀ x : Fin k → ℝ, intFrame W *ᵥ x = 0 → x = 0 := by
    intro x hx
    by_contra hne
    have hp := (Matrix.posDef_iff_dotProduct_mulVec.mp J.posDef).2 hne
    have hval : x ⬝ᵥ (J.form *ᵥ x) = (intFrame W *ᵥ x) ⬝ᵥ (A *ᵥ (intFrame W *ᵥ x)) := by
      rw [hJW, intGram]
      exact dotProduct_congr_mulVec A (intFrame W) x
    rw [hx, Matrix.mulVec_zero, dotProduct_zero] at hval
    have hp' : 0 < x ⬝ᵥ (J.form *ᵥ x) := by simpa using hp
    linarith [hp', hval]
  have hKpos : ((intFrame W)ᵀ * (1 : Matrix (Fin N) (Fin N) ℝ) * intFrame W).PosDef :=
    posDef_congr Matrix.PosDef.one hinjW
  obtain ⟨K, hK⟩ := exists_jacobiData hKpos
  have hKB : ∀ a b : Fin k, K.form a b = (((Wᵀ * W) a b : ℤ) : ℝ) := by
    intro a b
    rw [hK]
    show ((intFrame W)ᵀ * (1 : Matrix (Fin N) (Fin N) ℝ) * intFrame W) a b = _
    rw [Matrix.mul_one, Matrix.mul_apply, Matrix.mul_apply]
    push_cast
    exact Finset.sum_congr rfl fun p _ => rfl
  have hdom : ∀ v : Fin k → ℝ, lam * (v ⬝ᵥ (K.form *ᵥ v)) ≤ v ⬝ᵥ (J.form *ᵥ v) := by
    intro v
    have h1 : v ⬝ᵥ (K.form *ᵥ v) = (intFrame W *ᵥ v) ⬝ᵥ (intFrame W *ᵥ v) := by
      rw [hK]
      have := dotProduct_congr_mulVec (1 : Matrix (Fin N) (Fin N) ℝ) (intFrame W) v
      rw [this, Matrix.one_mulVec]
    have h2 : v ⬝ᵥ (J.form *ᵥ v) = (intFrame W *ᵥ v) ⬝ᵥ (A *ᵥ (intFrame W *ᵥ v)) := by
      rw [hJW, intGram]
      exact dotProduct_congr_mulVec A (intFrame W) v
    rw [h1, h2]
    exact hell' _
  have hlow : ∀ (j : ℕ) (hj : j ≤ k), lam ^ j ≤ (leadingBlock hj J.form).det :=
    fun j hj => pow_le_det_leadingBlock hlam.le hdom hKB hj
  have hdetB : J.form.det ≤ B := by rw [hdetJ]; exact hZdet
  refine ⟨fun i => fun p => W p i, fun i => ?_, ?_⟩
  · have hd := d_le_bound_of_siegel hlam hlam1 hJS hlow hdetB i
    have hdiag := J.form_diag_le_siegel (by norm_num : (1 : ℝ) ≤ 2) hJS i
    have hval : quadForm P (intVec fun p => W p i) = J.form i i := by
      rw [hJW, intGram_diag]
      rfl
    rw [hval]
    refine le_trans hdiag ?_
    rw [hBcol]
    refine mul_le_mul_of_nonneg_left hd ?_
    positivity
  · show (intGram A W).det = (intGram A Z).det
    rw [← hJW]
    exact hdetJ

end GaloisForLFunctions.HTGeometry
