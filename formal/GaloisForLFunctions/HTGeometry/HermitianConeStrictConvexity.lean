import GaloisForLFunctions.HTGeometry.PrimitivePairInteriorDimension

/-!
# Strict convexity of the complex positive cone happens exactly in size two

The closed cone `H_q(ℂ)_+` of positive semidefinite complex Hermitian matrices is called
*elementary* when any two nonzero non-proportional boundary points have positive definite sum.  For
the Lorentz cone this says that two nonparallel future-null momenta add to a future-timelike
momentum.

This file proves that a nonzero boundary point in size two is exactly a rank-one record
`primitiveRootGram u`, and deduces the exact dimension classification

`ElementaryFuture q ↔ q = 2`  (for `q ≥ 2`).

The positive direction is genuine arbitrary-boundary strict convexity, not only the previously
available primitive-pair form.
-/

open Matrix
open scoped ComplexOrder Matrix

noncomputable section

namespace GaloisForLFunctions.HTGeometry

section HermitianReality

variable {q : ℕ}

/-- A Hermitian quadratic value is fixed by conjugation. -/
theorem star_dotProduct_mulVec_self_of_isHermitian
    {A : Matrix (Fin q) (Fin q) ℂ} (hA : A.IsHermitian) (x : Fin q → ℂ) :
    star (star x ⬝ᵥ A *ᵥ x) = star x ⬝ᵥ A *ᵥ x := by
  rw [← Matrix.star_dotProduct_star, star_star, Matrix.star_mulVec, hA.eq,
    ← Matrix.dotProduct_mulVec]

/-- A Hermitian quadratic value is real. -/
theorem dotProduct_mulVec_im_eq_zero
    {A : Matrix (Fin q) (Fin q) ℂ} (hA : A.IsHermitian) (x : Fin q → ℂ) :
    (star x ⬝ᵥ A *ᵥ x).im = 0 :=
  Complex.conj_eq_iff_im.1 (star_dotProduct_mulVec_self_of_isHermitian hA x)

end HermitianReality

section RankOne

/-- The Gram record of a single root is positive semidefinite. -/
theorem posSemidef_primitiveRootGram {n : Type*} [Fintype n] (u : n → ℂ) :
    (primitiveRootGram u).PosSemidef :=
  Matrix.posSemidef_vecMulVec_star_self u

/-- A diagonal entry of a positive semidefinite matrix is a nonnegative real. -/
theorem posSemidef_diag_nonneg {q : ℕ} {A : Matrix (Fin q) (Fin q) ℂ}
    (hA : A.PosSemidef) (i : Fin q) : 0 ≤ A i i := by
  have h := hA.dotProduct_mulVec_nonneg (Pi.single i (1 : ℂ))
  have hval : star (Pi.single i (1 : ℂ)) ⬝ᵥ A *ᵥ Pi.single i (1 : ℂ) = A i i := by
    simp [Matrix.mulVec_single]
  rwa [hval] at h

/-- **Every nonzero boundary point in size two is a rank-one record.**  A nonzero singular positive
semidefinite `2 × 2` matrix is the Gram record of a single nonzero root. -/
theorem exists_primitiveRoot_of_posSemidef_det_zero
    (A : Matrix (Fin 2) (Fin 2) ℂ) (hA : A.PosSemidef) (hdet : A.det = 0) (hne : A ≠ 0) :
    ∃ u : Fin 2 → ℂ, u ≠ 0 ∧ A = primitiveRootGram u := by
  have hherm : A.IsHermitian := hA.1
  have h00 : 0 ≤ A 0 0 := posSemidef_diag_nonneg hA 0
  have h11 : 0 ≤ A 1 1 := posSemidef_diag_nonneg hA 1
  obtain ⟨a, hanonneg, ha⟩ : ∃ a : ℝ, 0 ≤ a ∧ A 0 0 = (a : ℂ) :=
    ⟨(A 0 0).re, (Complex.le_def.1 h00).1,
      Complex.ext rfl (by simpa using ((Complex.le_def.1 h00).2).symm)⟩
  obtain ⟨c, hcnonneg, hc⟩ : ∃ c : ℝ, 0 ≤ c ∧ A 1 1 = (c : ℂ) :=
    ⟨(A 1 1).re, (Complex.le_def.1 h11).1,
      Complex.ext rfl (by simpa using ((Complex.le_def.1 h11).2).symm)⟩
  have hdet' : A 0 0 * A 1 1 = A 0 1 * A 1 0 := by
    have h := hdet
    rw [Matrix.det_fin_two] at h
    linear_combination h
  have hconj : A 1 0 = star (A 0 1) := by
    have h := congrFun (congrFun hherm.eq 1) 0
    simpa [Matrix.conjTranspose_apply] using h.symm
  by_cases hzero : a = 0
  · -- The first column vanishes, so the record is carried by the second root.
    have hA00 : A 0 0 = 0 := by rw [ha, hzero]; simp
    have hquad : star (Pi.single (0 : Fin 2) (1 : ℂ)) ⬝ᵥ A *ᵥ Pi.single (0 : Fin 2) (1 : ℂ) = 0 := by
      simpa [Matrix.mulVec_single] using hA00
    have hcol : A *ᵥ Pi.single (0 : Fin 2) (1 : ℂ) = 0 :=
      (hA.dotProduct_mulVec_zero_iff _).1 hquad
    have h10 : A 1 0 = 0 := by
      have h := congrFun hcol 1
      simpa [Matrix.mulVec_single] using h
    have h01 : A 0 1 = 0 := by
      have h := congrArg star h10
      rw [hconj, star_star] at h
      simpa using h
    have hcne : c ≠ 0 := by
      intro hcon
      apply hne
      have hA11 : A 1 1 = 0 := by rw [hc, hcon]; simp
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hA00, h01, h10, hA11]
    have hsq : (Real.sqrt c : ℂ) * (Real.sqrt c : ℂ) = A 1 1 := by
      rw [hc]
      exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) (Real.mul_self_sqrt hcnonneg)
    have hsne : (Real.sqrt c : ℂ) ≠ 0 := by
      have : Real.sqrt c ≠ 0 := by
        intro hcon
        apply hcne
        have := Real.mul_self_sqrt hcnonneg
        rw [hcon] at this
        simpa using this.symm
      exact_mod_cast this
    refine ⟨![0, (Real.sqrt c : ℂ)], ?_, ?_⟩
    · intro hcon
      exact hsne (by simpa using congrFun hcon 1)
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp [primitiveRootGram, Matrix.vecMulVec_apply, hA00, h01, h10, ← hsq]
  · -- The first diagonal entry is positive; normalize the first column.
    have hpos : 0 < a := lt_of_le_of_ne hanonneg (Ne.symm hzero)
    have hrpos : 0 < Real.sqrt a := Real.sqrt_pos.2 hpos
    have hrne : ((Real.sqrt a : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hrpos.ne'
    have hrsq : ((Real.sqrt a : ℝ) : ℂ) * ((Real.sqrt a : ℝ) : ℂ) = A 0 0 := by
      rw [ha]
      exact_mod_cast congrArg (fun t : ℝ => (t : ℂ)) (Real.mul_self_sqrt hanonneg)
    have hstar_r : star ((Real.sqrt a : ℝ) : ℂ) = ((Real.sqrt a : ℝ) : ℂ) :=
      Complex.conj_ofReal _
    have key : A 1 0 * A 0 1 = A 1 1 * (((Real.sqrt a : ℝ) : ℂ) * ((Real.sqrt a : ℝ) : ℂ)) := by
      rw [hrsq]
      linear_combination -hdet'
    have h11eq :
        star (A 0 1 / ((Real.sqrt a : ℝ) : ℂ)) * (A 0 1 / ((Real.sqrt a : ℝ) : ℂ)) = A 1 1 := by
      rw [star_div₀, hstar_r, ← hconj, div_mul_div_comm, key, mul_div_assoc,
        div_self (mul_ne_zero hrne hrne), mul_one]
    have h01eq : ((Real.sqrt a : ℝ) : ℂ) * (A 0 1 / ((Real.sqrt a : ℝ) : ℂ)) = A 0 1 := by
      field_simp
    have h10eq :
        star (A 0 1 / ((Real.sqrt a : ℝ) : ℂ)) * ((Real.sqrt a : ℝ) : ℂ) = A 1 0 := by
      rw [star_div₀, hstar_r, ← hconj]
      field_simp
    refine ⟨![((Real.sqrt a : ℝ) : ℂ), A 0 1 / ((Real.sqrt a : ℝ) : ℂ)], ?_, ?_⟩
    · intro hcon
      exact hrne (by simpa using congrFun hcon 0)
    · ext i j
      fin_cases i <;> fin_cases j <;>
        simp only [primitiveRootGram, Matrix.vecMulVec_apply, Pi.star_apply,
          Fin.zero_eta, Fin.mk_one, Matrix.cons_val_zero, Matrix.cons_val_one,
          Fin.isValue]
      · rw [hstar_r, hrsq]
      · rw [hstar_r, h01eq]
      · rw [h10eq]
      · rw [h11eq]

end RankOne

section Classification

variable {q : ℕ}

/-- Scaling a root scales its Gram record by the squared modulus. -/
theorem primitiveRootGram_smul {n : Type*} (a : ℂ) (v : n → ℂ) :
    primitiveRootGram (a • v) = (star a * a) • primitiveRootGram v := by
  ext i j
  simp only [primitiveRootGram, Matrix.vecMulVec_apply, Pi.star_apply, Pi.smul_apply,
    smul_eq_mul, star_mul, Matrix.smul_apply]
  ring

/-- **Elementary future fusion.**  Any two nonzero, non-proportional boundary points of the positive
cone have positive definite sum. -/
def ElementaryFuture (q : ℕ) : Prop :=
  ∀ A B : Matrix (Fin q) (Fin q) ℂ, A.PosSemidef → B.PosSemidef →
    A.det = 0 → B.det = 0 → A ≠ 0 → B ≠ 0 →
    (∀ t : ℝ, 0 < t → A ≠ (t : ℂ) • B) → (A + B).PosDef

/-- Non-proportional rank-one records have independent roots. -/
theorem linearIndependent_of_not_proportional {n : Type*} (u v : n → ℂ)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hprop : ∀ t : ℝ, 0 < t →
      primitiveRootGram u ≠ (t : ℂ) • primitiveRootGram v) :
    LinearIndependent ℂ (primitiveRootPair u v) := by
  rw [linearIndependent_fin2]
  refine ⟨by simpa [primitiveRootPair] using hv, ?_⟩
  intro a hcon
  have hcon' : u = a • v := by simpa [primitiveRootPair] using hcon.symm
  have hane : a ≠ 0 := by
    intro hzero
    apply hu
    rw [hcon', hzero, zero_smul]
  have hpos : 0 < Complex.normSq a := Complex.normSq_pos.2 hane
  refine hprop (Complex.normSq a) hpos ?_
  rw [hcon', primitiveRootGram_smul]
  congr 1
  rw [Complex.normSq_eq_conj_mul_self]
  rfl

/-- In size two every nonzero boundary pair fuses to an interior point. -/
theorem elementaryFuture_two : ElementaryFuture 2 := by
  intro A B hA hB hdetA hdetB hAne hBne hprop
  obtain ⟨u, hu, rfl⟩ := exists_primitiveRoot_of_posSemidef_det_zero A hA hdetA hAne
  obtain ⟨v, hv, rfl⟩ := exists_primitiveRoot_of_posSemidef_det_zero B hB hdetB hBne
  exact primitivePairInterior_finTwo u v
    (linearIndependent_of_not_proportional u v hu hv hprop)

/-- The coordinate-root record has determinant zero in every dimension at least three. -/
theorem det_primitiveCoordinateRootGram_eq_zero (n : ℕ) (i : Fin (n + 3)) (k : Fin (n + 3))
    (hik : i ≠ k) :
    (primitiveRootGram (Pi.single i (1 : ℂ))).det = 0 := by
  refine Matrix.exists_mulVec_eq_zero_iff.1 ⟨Pi.single k (1 : ℂ), ?_, ?_⟩
  · intro hcon
    have h := congrFun hcon k
    simp at h
  · exact primitiveCoordinateRootGram_mulVec_of_ne i k hik

/-- Beyond size two, elementary future fusion fails. -/
theorem not_elementaryFuture_finAddThree (n : ℕ) : ¬ ElementaryFuture (n + 3) := by
  intro hfuse
  have h02 : (0 : Fin (n + 3)) ≠ 2 := by
    intro h
    have hval := congrArg Fin.val h
    change 0 = 2 % (n + 3) at hval
    rw [Nat.mod_eq_of_lt (by omega : 2 < n + 3)] at hval
    omega
  have h12 : (1 : Fin (n + 3)) ≠ 2 := by
    intro h
    have hval := congrArg Fin.val h
    change 1 = 2 % (n + 3) at hval
    rw [Nat.mod_eq_of_lt (by omega : 2 < n + 3)] at hval
    omega
  have h01 : (0 : Fin (n + 3)) ≠ 1 := by
    intro h
    have hval := congrArg Fin.val h
    change 0 = 1 % (n + 3) at hval
    rw [Nat.mod_eq_of_lt (by omega : 1 < n + 3)] at hval
    omega
  set A := primitiveRootGram (Pi.single (0 : Fin (n + 3)) (1 : ℂ)) with hAdef
  set B := primitiveRootGram (Pi.single (1 : Fin (n + 3)) (1 : ℂ)) with hBdef
  have hA00 : A 0 0 = 1 := by
    simp [hAdef, primitiveRootGram, Matrix.vecMulVec_apply]
  have hB00 : B 0 0 = 0 := by
    simp [hBdef, primitiveRootGram, Matrix.vecMulVec_apply]
  have hAne : A ≠ 0 := by
    intro hcon
    have h := congrFun (congrFun hcon 0) 0
    rw [hA00] at h
    exact one_ne_zero h
  have hBne : B ≠ 0 := by
    intro hcon
    have h := congrFun (congrFun hcon 1) 1
    have hB11 : B 1 1 = 1 := by
      simp [hBdef, primitiveRootGram, Matrix.vecMulVec_apply]
    rw [hB11] at h
    exact one_ne_zero h
  have hprop : ∀ t : ℝ, 0 < t → A ≠ (t : ℂ) • B := by
    intro t _ hcon
    have h := congrFun (congrFun hcon 0) 0
    rw [hA00] at h
    simp [hB00] at h
  have hpos := hfuse A B (posSemidef_primitiveRootGram _) (posSemidef_primitiveRootGram _)
    (det_primitiveCoordinateRootGram_eq_zero n 0 2 h02)
    (det_primitiveCoordinateRootGram_eq_zero n 1 2 h12) hAne hBne hprop
  have hx : (Pi.single (2 : Fin (n + 3)) (1 : ℂ) : Fin (n + 3) → ℂ) ≠ 0 := by
    intro hcon
    have h := congrFun hcon 2
    simp at h
  have hmul : (A + B) *ᵥ (Pi.single (2 : Fin (n + 3)) (1 : ℂ) : Fin (n + 3) → ℂ) = 0 := by
    rw [Matrix.add_mulVec, hAdef, hBdef,
      primitiveCoordinateRootGram_mulVec_of_ne 0 2 h02,
      primitiveCoordinateRootGram_mulVec_of_ne 1 2 h12]
    exact add_zero 0
  have hstrict := hpos.dotProduct_mulVec_pos hx
  rw [hmul, dotProduct_zero] at hstrict
  exact (lt_irrefl 0) hstrict

/-- **Arbitrary-boundary strict convexity happens exactly in size two.** -/
theorem elementaryFuture_iff (hq : 2 ≤ q) : ElementaryFuture q ↔ q = 2 := by
  constructor
  · intro hfuse
    by_contra hne
    have hthree : 3 ≤ q := by omega
    obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' hthree
    exact (not_elementaryFuture_finAddThree n) hfuse
  · rintro rfl
    exact elementaryFuture_two

end Classification

section Topology

variable {q : ℕ}

/-- Complex Hermitian matrices, as a topological subspace of all complex matrices. -/
abbrev HermitianMatrix (q : ℕ) := {A : Matrix (Fin q) (Fin q) ℂ // A.IsHermitian}

/-- The closed positive cone inside the Hermitian matrices. -/
def positiveCone (q : ℕ) : Set (HermitianMatrix q) :=
  {A | (A : Matrix (Fin q) (Fin q) ℂ).PosSemidef}

/-- The quadratic value of a matrix at a fixed vector depends continuously on the matrix. -/
theorem continuous_quadraticValue (x : Fin q → ℂ) :
    Continuous (fun A : Matrix (Fin q) (Fin q) ℂ => star x ⬝ᵥ A *ᵥ x) := by
  simp only [dotProduct, Matrix.mulVec]
  refine continuous_finsetSum _ fun i _ => ?_
  refine continuous_const.mul ?_
  refine continuous_finsetSum _ fun j _ => ?_
  exact (continuous_apply_apply i j).mul continuous_const

/-- Positive semidefiniteness of a Hermitian matrix is nonnegativity of the real quadratic form. -/
theorem posSemidef_iff_re_nonneg {A : Matrix (Fin q) (Fin q) ℂ} (hA : A.IsHermitian) :
    A.PosSemidef ↔ ∀ x : Fin q → ℂ, 0 ≤ (star x ⬝ᵥ A *ᵥ x).re := by
  constructor
  · intro h x
    simpa using (Complex.le_def.1 (h.dotProduct_mulVec_nonneg x)).1
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hA fun x => ?_
    rw [Complex.le_def]
    exact ⟨by simpa using h x, by simpa using (dotProduct_mulVec_im_eq_zero hA x).symm⟩

/-- Positive definiteness of a Hermitian matrix is positivity of the real quadratic form. -/
theorem posDef_iff_re_pos {A : Matrix (Fin q) (Fin q) ℂ} (hA : A.IsHermitian) :
    A.PosDef ↔ ∀ x : Fin q → ℂ, x ≠ 0 → 0 < (star x ⬝ᵥ A *ᵥ x).re := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨-, hpos⟩ x hx
    simpa using (Complex.lt_def.1 (hpos hx)).1
  · intro h
    refine ⟨hA, fun x hx => ?_⟩
    rw [Complex.lt_def]
    exact ⟨by simpa using h x hx, by simpa using (dotProduct_mulVec_im_eq_zero hA x).symm⟩

/-- Positive definiteness is tested on the unit sphere. -/
theorem posDef_iff_sphere {A : Matrix (Fin q) (Fin q) ℂ} (hA : A.IsHermitian) :
    A.PosDef ↔ ∀ x : Fin q → ℂ, ‖x‖ = 1 → 0 < (star x ⬝ᵥ A *ᵥ x).re := by
  rw [posDef_iff_re_pos hA]
  constructor
  · intro h x hx
    refine h x ?_
    intro hcon
    rw [hcon, norm_zero] at hx
    exact zero_ne_one hx
  · intro hsph x hx
    have hnorm : ‖x‖ ≠ 0 := by simpa using hx
    set c : ℝ := ‖x‖⁻¹ with hc
    have hcpos : 0 < c := by
      rw [hc]
      exact inv_pos.2 (lt_of_le_of_ne (norm_nonneg x) (Ne.symm hnorm))
    have hy : ‖((c : ℂ)) • x‖ = 1 := by
      rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hcpos, hc]
      exact inv_mul_cancel₀ hnorm
    have hval := hsph _ hy
    have hscale : star ((c : ℂ) • x) ⬝ᵥ A *ᵥ ((c : ℂ) • x)
        = ((c : ℂ) * (c : ℂ)) * (star x ⬝ᵥ A *ᵥ x) := by
      rw [Matrix.mulVec_smul, dotProduct_smul, star_smul]
      simp only [Complex.star_def, Complex.conj_ofReal, smul_eq_mul, smul_dotProduct]
      ring
    rw [hscale] at hval
    have hre : (((c : ℂ) * (c : ℂ)) * (star x ⬝ᵥ A *ᵥ x)).re
        = (c * c) * (star x ⬝ᵥ A *ᵥ x).re := by
      simp [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    rw [hre] at hval
    nlinarith [hval, mul_pos hcpos hcpos]

/-- The positive cone is closed inside the Hermitian matrices. -/
theorem isClosed_positiveCone : IsClosed (positiveCone q) := by
  have hrep : positiveCone q =
      ⋂ x : Fin q → ℂ,
        {A : HermitianMatrix q | 0 ≤ (star x ⬝ᵥ (A : Matrix (Fin q) (Fin q) ℂ) *ᵥ x).re} := by
    ext A
    simp only [positiveCone, Set.mem_setOf_eq, Set.mem_iInter]
    exact posSemidef_iff_re_nonneg A.2
  rw [hrep]
  refine isClosed_iInter fun x => ?_
  have hc : Continuous
      (fun A : HermitianMatrix q => (star x ⬝ᵥ (A : Matrix (Fin q) (Fin q) ℂ) *ᵥ x).re) :=
    (Complex.continuous_re.comp (continuous_quadraticValue x)).comp continuous_subtype_val
  exact isClosed_Ici.preimage hc

/-- The positive definite locus is open inside the Hermitian matrices. -/
theorem isOpen_posDefLocus :
    IsOpen {A : HermitianMatrix q | (A : Matrix (Fin q) (Fin q) ℂ).PosDef} := by
  classical
  haveI : CompactSpace (Metric.sphere (0 : Fin q → ℂ) 1) :=
    isCompact_iff_compactSpace.mp (isCompact_sphere _ _)
  have hcont : Continuous
      (fun p : HermitianMatrix q × (Metric.sphere (0 : Fin q → ℂ) 1) =>
        (star ((p.2 : Fin q → ℂ)) ⬝ᵥ (p.1 : Matrix (Fin q) (Fin q) ℂ) *ᵥ
          ((p.2 : Fin q → ℂ))).re) := by
    refine Complex.continuous_re.comp ?_
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    refine continuous_finsetSum _ fun i _ => ?_
    refine Continuous.mul ?_ ?_
    · exact continuous_star.comp
        ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd))
    · refine continuous_finsetSum _ fun j _ => ?_
      exact ((continuous_apply_apply i j).comp
        (continuous_subtype_val.comp continuous_fst)).mul
        ((continuous_apply j).comp (continuous_subtype_val.comp continuous_snd))
  have hbadclosed : IsClosed
      {A : HermitianMatrix q |
        ∃ x : Metric.sphere (0 : Fin q → ℂ) 1,
          (star ((x : Fin q → ℂ)) ⬝ᵥ (A : Matrix (Fin q) (Fin q) ℂ) *ᵥ
            ((x : Fin q → ℂ))).re ≤ 0} := by
    have hclosedset : IsClosed
        {p : HermitianMatrix q × (Metric.sphere (0 : Fin q → ℂ) 1) |
          (star ((p.2 : Fin q → ℂ)) ⬝ᵥ (p.1 : Matrix (Fin q) (Fin q) ℂ) *ᵥ
            ((p.2 : Fin q → ℂ))).re ≤ 0} :=
      IsClosed.preimage hcont (isClosed_Iic (a := (0 : ℝ)))
    have himg := isClosedMap_fst_of_compactSpace _ hclosedset
    convert himg using 1
    ext A
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨(A, x), hx, rfl⟩
    · rintro ⟨p, hp, rfl⟩
      exact ⟨p.2, hp⟩
  have hset : {A : HermitianMatrix q | (A : Matrix (Fin q) (Fin q) ℂ).PosDef} =
      {A : HermitianMatrix q |
        ∃ x : Metric.sphere (0 : Fin q → ℂ) 1,
          (star ((x : Fin q → ℂ)) ⬝ᵥ (A : Matrix (Fin q) (Fin q) ℂ) *ᵥ
            ((x : Fin q → ℂ))).re ≤ 0}ᶜ := by
    ext A
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, not_exists, not_le]
    rw [posDef_iff_sphere A.2]
    constructor
    · intro h x
      exact h _ (mem_sphere_zero_iff_norm.1 x.2)
    · intro h x hx
      exact h ⟨x, by simpa using hx⟩
  rw [hset]
  exact hbadclosed.isOpen_compl

/-- A real multiple of a Hermitian matrix is Hermitian. -/
theorem isHermitian_real_smul {R : Matrix (Fin q) (Fin q) ℂ} (hR : R.IsHermitian) (δ : ℝ) :
    (((δ : ℝ) : ℂ) • R).IsHermitian := by
  have hRij : ∀ i j, (starRingEnd ℂ) (R j i) = R i j := by
    intro i j
    have h := congrFun (congrFun hR.eq i) j
    simpa [Matrix.conjTranspose_apply] using h
  ext i j
  simp only [Matrix.conjTranspose_apply, Matrix.smul_apply, smul_eq_mul, star_mul,
    Complex.star_def, Complex.conj_ofReal, hRij]
  ring

/-- The interior of the positive cone is exactly the positive definite locus. -/
theorem interior_positiveCone :
    interior (positiveCone q) = {A : HermitianMatrix q | (A : Matrix (Fin q) (Fin q) ℂ).PosDef} := by
  apply Set.Subset.antisymm
  · intro A hA
    have hAcone : A ∈ positiveCone q := interior_subset hA
    have hpsd : (A : Matrix (Fin q) (Fin q) ℂ).PosSemidef := hAcone
    by_contra hcon
    have hdet : (A : Matrix (Fin q) (Fin q) ℂ).det = 0 := by
      by_contra hne
      exact hcon ((hpsd.posDef_iff_det_ne_zero).2 hne)
    obtain ⟨x, hxne, hx⟩ := Matrix.exists_mulVec_eq_zero_iff.2 hdet
    set R : Matrix (Fin q) (Fin q) ℂ := primitiveRootGram (star x) with hR
    have hRherm : R.IsHermitian := (posSemidef_primitiveRootGram (star x)).1
    have hquadR : star x ⬝ᵥ R *ᵥ x = (star x ⬝ᵥ x) * (star x ⬝ᵥ x) := by
      rw [hR]
      simp only [primitiveRootGram, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct,
        Pi.star_apply, star_star]
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hxpos : 0 < (star x ⬝ᵥ x).re := by
      have hnonneg : (0 : ℂ) ≤ star x ⬝ᵥ x := dotProduct_star_self_nonneg x
      have hne : star x ⬝ᵥ x ≠ 0 := fun hcon' => hxne (dotProduct_star_self_eq_zero.1 hcon')
      have h1 : 0 ≤ (star x ⬝ᵥ x).re := (Complex.le_def.1 hnonneg).1
      rcases lt_or_eq_of_le h1 with h | h
      · exact h
      · exfalso
        apply hne
        have him : (star x ⬝ᵥ x).im = 0 := by
          simpa using ((Complex.le_def.1 hnonneg).2).symm
        exact Complex.ext (by simpa using h.symm) (by simpa using him)
    set f : ℝ → HermitianMatrix q := fun δ =>
      ⟨(A : Matrix (Fin q) (Fin q) ℂ) - ((δ : ℝ) : ℂ) • R,
        A.2.sub (isHermitian_real_smul hRherm δ)⟩ with hf
    have hfcont : Continuous f := by
      refine Continuous.subtype_mk ?_ _
      exact continuous_const.sub (Continuous.smul
        (Complex.continuous_ofReal.comp continuous_id) continuous_const)
    have hf0 : f 0 = A := by
      apply Subtype.ext
      show (A : Matrix (Fin q) (Fin q) ℂ) - (((0 : ℝ) : ℂ)) • R = (A : Matrix (Fin q) (Fin q) ℂ)
      rw [Complex.ofReal_zero, zero_smul, sub_zero]
    have hopen : IsOpen (f ⁻¹' interior (positiveCone q)) :=
      isOpen_interior.preimage hfcont
    have hmem : (0 : ℝ) ∈ f ⁻¹' interior (positiveCone q) := by
      simp only [Set.mem_preimage, hf0]
      exact hA
    obtain ⟨ε, hεpos, hball⟩ := Metric.isOpen_iff.1 hopen 0 hmem
    have hδmem : (ε / 2) ∈ f ⁻¹' interior (positiveCone q) := by
      apply hball
      simp only [Metric.mem_ball, dist_zero_right, Real.norm_eq_abs]
      rw [abs_of_pos (by linarith)]
      linarith
    have hδcone : f (ε / 2) ∈ positiveCone q := interior_subset hδmem
    have hδpsd : ((f (ε / 2)) : Matrix (Fin q) (Fin q) ℂ).PosSemidef := hδcone
    have hbad : (star x ⬝ᵥ ((f (ε / 2)) : Matrix (Fin q) (Fin q) ℂ) *ᵥ x).re < 0 := by
      have hval : star x ⬝ᵥ ((f (ε / 2)) : Matrix (Fin q) (Fin q) ℂ) *ᵥ x
          = - (((ε / 2 : ℝ) : ℂ) * ((star x ⬝ᵥ x) * (star x ⬝ᵥ x))) := by
        simp only [hf, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
          dotProduct_smul, smul_eq_mul, hx, dotProduct_zero, hquadR]
        ring
      rw [hval]
      have hsq : ((star x ⬝ᵥ x) * (star x ⬝ᵥ x)).re = (star x ⬝ᵥ x).re * (star x ⬝ᵥ x).re := by
        have him : (star x ⬝ᵥ x).im = 0 := by
          have hnonneg : (0 : ℂ) ≤ star x ⬝ᵥ x := dotProduct_star_self_nonneg x
          simpa using ((Complex.le_def.1 hnonneg).2).symm
        simp [Complex.mul_re, him]
      simp only [Complex.neg_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero, hsq]
      nlinarith [mul_pos hxpos hxpos, hεpos]
    have := (posSemidef_iff_re_nonneg (f (ε / 2)).2).1 hδpsd x
    linarith
  · intro A hA
    refine interior_maximal (fun B hB => ?_) isOpen_posDefLocus hA
    exact Matrix.PosDef.posSemidef hB

/-- **The boundary of the positive cone is exactly the singular positive semidefinite locus.** -/
theorem frontier_positiveCone :
    frontier (positiveCone q) =
      {A : HermitianMatrix q |
        (A : Matrix (Fin q) (Fin q) ℂ).PosSemidef ∧ (A : Matrix (Fin q) (Fin q) ℂ).det = 0} := by
  rw [frontier, isClosed_positiveCone.closure_eq, interior_positiveCone]
  ext A
  simp only [Set.mem_sdiff, Set.mem_setOf_eq, positiveCone]
  constructor
  · rintro ⟨hpsd, hnot⟩
    refine ⟨hpsd, ?_⟩
    by_contra hne
    exact hnot ((hpsd.posDef_iff_det_ne_zero).2 hne)
  · rintro ⟨hpsd, hdet⟩
    refine ⟨hpsd, ?_⟩
    intro hposdef
    exact (hpsd.posDef_iff_det_ne_zero.1 hposdef) hdet

/-- Elementary future fusion phrased on the genuine topological boundary of the positive cone. -/
def ElementaryFutureCone (q : ℕ) : Prop :=
  ∀ A B : HermitianMatrix q, A ∈ frontier (positiveCone q) → B ∈ frontier (positiveCone q) →
    (A : Matrix (Fin q) (Fin q) ℂ) ≠ 0 → (B : Matrix (Fin q) (Fin q) ℂ) ≠ 0 →
    (∀ t : ℝ, 0 < t →
      (A : Matrix (Fin q) (Fin q) ℂ) ≠ (t : ℂ) • (B : Matrix (Fin q) (Fin q) ℂ)) →
    ((A : Matrix (Fin q) (Fin q) ℂ) + (B : Matrix (Fin q) (Fin q) ℂ)).PosDef

/-- **Strict convexity of the complex positive cone holds exactly in size two.** -/
theorem elementaryFutureCone_iff_two (hq : 2 ≤ q) : ElementaryFutureCone q ↔ q = 2 := by
  rw [← elementaryFuture_iff hq]
  constructor
  · intro h A B hA hB hdetA hdetB hAne hBne hprop
    exact h ⟨A, hA.1⟩ ⟨B, hB.1⟩
      (by rw [frontier_positiveCone]; exact ⟨hA, hdetA⟩)
      (by rw [frontier_positiveCone]; exact ⟨hB, hdetB⟩) hAne hBne hprop
  · intro h A B hA hB hAne hBne hprop
    rw [frontier_positiveCone] at hA hB
    exact h _ _ hA.1 hB.1 hA.2 hB.2 hAne hBne hprop

end Topology

end GaloisForLFunctions.HTGeometry
