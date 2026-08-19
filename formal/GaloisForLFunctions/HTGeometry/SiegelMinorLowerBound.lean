import GaloisForLFunctions.HTGeometry.SiegelGramDomination
import GaloisForLFunctions.HTGeometry.SiegelOrbit

/-!
# Minimality of the leading minors of a reduced form

A leading minor of a congruate `γᵀ A γ` is the weighted Gram determinant of the frame formed by the
first columns of `γ`.  Cauchy–Binet expands that determinant into the squares of the frame's maximal
minors, weighted by products of Jacobi diagonal entries.  The frame is integral, so one of its
maximal minors is a nonzero integer and contributes at least its weight; the Siegel growth bound
compares any such weight with the product of the leading diagonal entries, which is the leading minor
of `A` itself.

Hence a Siegel-reduced form has, up to a constant depending only on the dimension and the Siegel
parameters, the smallest leading minors in its orbit.  Two reduced forms in one orbit therefore have
comparable minors, and consecutive ratios of minors are the Jacobi diagonal entries.

* `leadingBlock_congr_frame` : a leading block is a congruence by the leading columns.
* `IsIntUnimodular.exists_inv` : the integral inverse.
* `exists_minor_lower_bound` : **the leading minors of a reduced form are minimal in its orbit.**
* `exists_d_comparable_of_siegel` : **two reduced forms in one orbit have comparable diagonals.**
-/

namespace GaloisForLFunctions.HTGeometry

open Matrix

variable {n : ℕ}

/-- The leading block of a congruate is the congruate by the leading columns. -/
theorem leadingBlock_congr_frame {k n : ℕ} (hk : k ≤ n) (M γ : Matrix (Fin n) (Fin n) ℝ) :
    leadingBlock hk (γᵀ * M * γ)
      = (γ.submatrix id (Fin.castLE hk))ᵀ * M * (γ.submatrix id (Fin.castLE hk)) := by
  ext a b
  show (γᵀ * M * γ) (Fin.castLE hk a) (Fin.castLE hk b) = _
  rw [Matrix.mul_apply, Matrix.mul_apply]
  refine Finset.sum_congr rfl fun p _ => ?_
  congr 1

/-- An invertible matrix has injective leading columns. -/
theorem frame_mulVec_eq_zero {k n : ℕ} (hk : k ≤ n) {γ δ : Matrix (Fin n) (Fin n) ℝ}
    (hδγ : δ * γ = 1) {x : Fin k → ℝ}
    (hx : (γ.submatrix id (Fin.castLE hk)) *ᵥ x = 0) : x = 0 := by
  classical
  set y : Fin n → ℝ := fun m => if h : (m : ℕ) < k then x ⟨(m : ℕ), h⟩ else 0 with hy
  have hinj : Set.InjOn (Fin.castLE hk) ((Finset.univ : Finset (Fin k)) : Set (Fin k)) := by
    intro a _ b _ hab
    exact Fin.ext (by simpa using congrArg Fin.val hab)
  have hcast : ∀ b : Fin k, y (Fin.castLE hk b) = x b := by
    intro b
    have hb : ((Fin.castLE hk b : Fin n) : ℕ) < k := by simp
    rw [hy]
    simp only [dif_pos hb]
    exact congrArg x (Fin.ext rfl)
  have hgy : γ *ᵥ y = 0 := by
    funext p
    have hstep : (γ *ᵥ y) p = ∑ b : Fin k, γ p (Fin.castLE hk b) * x b := by
      show ∑ m, γ p m * y m = _
      have hre : (∑ b : Fin k, γ p (Fin.castLE hk b) * x b)
          = ∑ m ∈ Finset.univ.image (Fin.castLE hk), γ p m * y m := by
        rw [Finset.sum_image (f := fun m : Fin n => γ p m * y m) hinj]
        exact Finset.sum_congr rfl fun b _ => by rw [hcast b]
      rw [hre]
      refine (Finset.sum_subset (Finset.subset_univ _) fun m _ hm => ?_).symm
      have hmk : k ≤ (m : ℕ) := by
        by_contra hcon
        exact hm (Finset.mem_image.2 ⟨⟨(m : ℕ), by omega⟩, Finset.mem_univ _, Fin.ext rfl⟩)
      have hym : y m = 0 := by
        rw [hy]
        simp only [dif_neg (by omega : ¬ ((m : ℕ) < k))]
      rw [hym, mul_zero]
    have hxp : (γ.submatrix id (Fin.castLE hk) *ᵥ x) p
        = ∑ b : Fin k, γ p (Fin.castLE hk b) * x b := rfl
    rw [hstep, ← hxp, hx]
  have hyzero : y = 0 := by
    have h1 : δ *ᵥ (γ *ᵥ y) = y := by
      rw [Matrix.mulVec_mulVec, hδγ, Matrix.one_mulVec]
    rw [hgy, Matrix.mulVec_zero] at h1
    exact h1.symm
  funext b
  rw [← hcast b, hyzero]
  rfl

/-- **The integral inverse of an integral unimodular matrix.** -/
theorem IsIntUnimodular.exists_inv {γ : Matrix (Fin n) (Fin n) ℝ} (hγ : IsIntUnimodular γ) :
    ∃ δ : Matrix (Fin n) (Fin n) ℝ, IsIntUnimodular δ ∧ γ * δ = 1 ∧ δ * γ = 1 := by
  classical
  obtain ⟨g, hgu, hg⟩ := hγ
  obtain ⟨G, rfl⟩ := hgu
  set F : Matrix (Fin n) (Fin n) ℤ →+* Matrix (Fin n) (Fin n) ℝ :=
    (Int.castRingHom ℝ).mapMatrix with hF
  have hγeq : γ = F ((G : Matrix (Fin n) (Fin n) ℤ)) := by
    ext a b
    exact hg a b
  refine ⟨F ((G⁻¹ : (Matrix (Fin n) (Fin n) ℤ)ˣ) : Matrix (Fin n) (Fin n) ℤ),
    ⟨((G⁻¹ : (Matrix (Fin n) (Fin n) ℤ)ˣ) : Matrix (Fin n) (Fin n) ℤ), ⟨G⁻¹, rfl⟩,
      fun a b => rfl⟩, ?_, ?_⟩
  · rw [hγeq, ← map_mul, G.mul_inv, map_one]
  · rw [hγeq, ← map_mul, G.inv_mul, map_one]


/-- The value of a diagonal form. -/
theorem dotProduct_diagonal_mulVec (d v : Fin n → ℝ) :
    v ⬝ᵥ (Matrix.diagonal d *ᵥ v) = ∑ m, d m * (v m) ^ 2 := by
  classical
  show ∑ i, v i * (Matrix.diagonal d *ᵥ v) i = _
  refine Finset.sum_congr rfl fun i _ => ?_
  have hentry : (Matrix.diagonal d *ᵥ v) i = d i * v i := by
    show ∑ j, Matrix.diagonal d i j * v j = _
    rw [Finset.sum_eq_single i
      (fun p _ hp => by rw [Matrix.diagonal_apply_ne _ (Ne.symm hp), zero_mul])
      (fun hcon => absurd (Finset.mem_univ i) hcon), Matrix.diagonal_apply_eq]
  rw [hentry]
  ring

/-- **The leading minors of a Siegel-reduced form are minimal in its orbit.**  Each leading minor of
a congruate is the weighted Gram determinant of the corresponding integral frame, which Cauchy–Binet
expands into weighted squares of the frame's maximal minors; one of these minors is a nonzero
integer, and the Siegel growth bound compares its weight with the leading one. -/
theorem exists_minor_lower_bound (n : ℕ) (t u : ℝ) (ht : 1 ≤ t) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∀ (J J' : JacobiData n), J.IsSiegel t u →
      ∀ γ : Matrix (Fin n) (Fin n) ℝ, IsIntUnimodular γ → J'.form = γᵀ * J.form * γ →
      ∀ (k : ℕ) (hk : k ≤ n),
        (leadingBlock hk J.form).det ≤ Cst * (leadingBlock hk J'.form).det := by
  classical
  obtain ⟨c, hc, hquasi⟩ := exists_quasiDiagonal n t u ht
  set c₁ : ℝ := min c 1 with hc₁def
  have hc₁pos : 0 < c₁ := lt_min hc zero_lt_one
  have hc₁le1 : c₁ ≤ 1 := min_le_right _ _
  have hc₁lec : c₁ ≤ c := min_le_left _ _
  set K : ℝ := t ^ n with hKdef
  have hK1 : 1 ≤ K := one_le_pow₀ ht
  refine ⟨(Nat.factorial n : ℝ) * K ^ n / c₁ ^ n, by positivity, ?_⟩
  intro J J' hS γ hγ hform k hk
  obtain ⟨δ, -, -, hδγ⟩ := hγ.exists_inv
  obtain ⟨g, hgu, hg⟩ := hγ
  set C : Matrix (Fin n) (Fin k) ℝ := γ.submatrix id (Fin.castLE hk) with hCdef
  set Z : Matrix (Fin n) (Fin k) ℤ := g.submatrix id (Fin.castLE hk) with hZdef
  have hCZ : C = Z.map (fun z : ℤ => (z : ℝ)) := by
    ext a b
    exact hg a (Fin.castLE hk b)
  have hinjC : ∀ x : Fin k → ℝ, C *ᵥ x = 0 → x = 0 := fun x hx =>
    frame_mulVec_eq_zero hk hδγ hx
  have hD0pos : (Matrix.diagonal J.d).PosDef := Matrix.posDef_diagonal_iff.mpr J.pos
  have hGpos : (Cᵀ * Matrix.diagonal J.d * C).PosDef := posDef_congr hD0pos hinjC
  obtain ⟨JG₀, hJG₀⟩ := exists_jacobiData hGpos
  have hJG : (J'.trunc hk).form = Cᵀ * J.form * C := by
    rw [J'.trunc_form hk, hform, leadingBlock_congr_frame]
  have hcmp : ∀ v : Fin n → ℝ,
      c * (v ⬝ᵥ (Matrix.diagonal J.d *ᵥ v)) ≤ v ⬝ᵥ (J.form *ᵥ v) := by
    intro v
    rw [dotProduct_diagonal_mulVec]
    exact hquasi J hS v
  have hdom : c ^ k * (Cᵀ * Matrix.diagonal J.d * C).det ≤ (Cᵀ * J.form * C).det :=
    det_congr_ge hc hcmp hJG hJG₀
  have hmono : ∀ i j : Fin n, (i : ℕ) ≤ (j : ℕ) → J.d i ≤ K * J.d j :=
    fun i j hij => J.d_le_pow_n ht hS hij
  have hposdet : 0 < ((Z.map (fun z : ℤ => (z : ℝ)))ᵀ * Matrix.diagonal J.d
      * (Z.map (fun z : ℤ => (z : ℝ)))).det := by
    rw [← hCZ]
    exact hGpos.det_pos
  have hlow := prod_d_le_det_weightedGram hk J.pos hK1 hmono Z hposdet
  rw [← hCZ] at hlow
  have hPdet : (leadingBlock hk J.form).det = ∏ j : Fin k, J.d (Fin.castLE hk j) :=
    det_leadingBlock_form hk J
  have hYdet : (leadingBlock hk J'.form).det = (Cᵀ * J.form * C).det := by
    rw [hform, leadingBlock_congr_frame]
  have hYpos : 0 < (leadingBlock hk J'.form).det := by
    rw [det_leadingBlock_form hk J']
    exact Finset.prod_pos fun m _ => J'.pos _
  set P : ℝ := (leadingBlock hk J.form).det with hPdef
  set X : ℝ := (Cᵀ * Matrix.diagonal J.d * C).det with hXdef
  set Y : ℝ := (leadingBlock hk J'.form).det with hYdef
  have hP : P ≤ (Nat.factorial k : ℝ) * K ^ k * X := by rw [hPdet]; exact hlow
  have hXY : c ^ k * X ≤ Y := by rw [hYdet]; exact hdom
  have hPnn : 0 ≤ P := by
    rw [hPdet]
    exact Finset.prod_nonneg fun m _ => (J.pos _).le
  have hXnn : 0 ≤ X := hGpos.det_pos.le
  have hYnn : 0 ≤ Y := hYpos.le
  have hfacK : (0 : ℝ) ≤ (Nat.factorial k : ℝ) * K ^ k := by positivity
  have hfinal : c₁ ^ n * P ≤ (Nat.factorial n : ℝ) * K ^ n * Y := by
    calc c₁ ^ n * P ≤ c₁ ^ k * P :=
          mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hc₁pos.le hc₁le1 hk) hPnn
      _ ≤ c₁ ^ k * ((Nat.factorial k : ℝ) * K ^ k * X) :=
          mul_le_mul_of_nonneg_left hP (pow_nonneg hc₁pos.le k)
      _ = (Nat.factorial k : ℝ) * K ^ k * (c₁ ^ k * X) := by ring
      _ ≤ (Nat.factorial k : ℝ) * K ^ k * Y :=
          mul_le_mul_of_nonneg_left
            (le_trans (mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ hc₁pos.le hc₁lec k) hXnn) hXY) hfacK
      _ ≤ (Nat.factorial n : ℝ) * K ^ n * Y := by
          refine mul_le_mul_of_nonneg_right ?_ hYnn
          refine mul_le_mul ?_ (pow_le_pow_right₀ hK1 hk) (by positivity) (by positivity)
          exact_mod_cast Nat.factorial_le hk
  rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < c₁ ^ n), mul_comm P (c₁ ^ n)]
  exact hfinal

/-- **Two Siegel-reduced forms in one orbit have comparable Jacobi diagonals.**  Each has minimal
leading minors in the orbit, so the two families of minors are comparable, and consecutive ratios of
minors are the diagonal entries. -/
theorem exists_d_comparable_of_siegel (n : ℕ) (t u : ℝ) (ht : 1 ≤ t) :
    ∃ Cst : ℝ, 0 < Cst ∧ ∀ (J J' : JacobiData n), J.IsSiegel t u → J'.IsSiegel t u →
      ∀ γ : Matrix (Fin n) (Fin n) ℝ, IsIntUnimodular γ → J'.form = γᵀ * J.form * γ →
      ∀ l : Fin n, J.d l ≤ Cst * J'.d l := by
  obtain ⟨Cst, hCst, hbound⟩ := exists_minor_lower_bound n t u ht
  refine ⟨Cst ^ 2, by positivity, ?_⟩
  intro J J' hS hS' γ hγ hform l
  obtain ⟨δ, hδ, hγδ, -⟩ := hγ.exists_inv
  have hrev : J.form = δᵀ * J'.form * δ := by
    have h1 : δᵀ * J'.form * δ = (γ * δ)ᵀ * J.form * (γ * δ) := by
      rw [hform, Matrix.transpose_mul]
      simp only [Matrix.mul_assoc]
    rw [h1, hγδ, Matrix.transpose_one, Matrix.one_mul, Matrix.mul_one]
  exact d_le_of_det_le hCst (hbound J J' hS γ hγ hform) (hbound J' J hS' δ hδ hrev) l

end GaloisForLFunctions.HTGeometry
