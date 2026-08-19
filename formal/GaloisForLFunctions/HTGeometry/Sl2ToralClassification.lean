import GaloisForLFunctions.HTGeometry.Sl2DiagonaliseRegular

/-!
# Cassidy's classification for `sl₂`: a subalgebra containing a torus

Let `C ⊆ U` be fields, `C` algebraically closed, and let `L ⊆ sl₂(U)` be a `C`-subspace closed under
the bracket whose `U`-span is all of `sl₂(U)`, and whose `U`-line stabilisers are trivial: `c A ∈ L`
for `0 ≠ A ∈ L` forces `c ∈ C`.  If `L` contains a toral element `μ h`, then `L` is the `C`-span of
`h`, `v₀ e` and `w₀ f` with `v₀ w₀ ∈ C`.

The mechanism is a chain of three brackets.  Doubling the bracket with `μ h` projects `L` onto the
root part, so `L` contains a root element `b e + c f` of nonzero determinant; bracketing it against
its own image under `ad(μ h)` returns `(b c) · (μ h)`, and bracketing that image against `μ h`
returns `μ² · (b e + c f)`.  The line-stabiliser hypothesis therefore puts both `b c` and `μ²` in
`C`, and since `C` is algebraically closed `μ ∈ C`, so `h` itself lies in `L`.  With `h` present the
eigenvalues `0, ±2` of `ad(h)` lie in `C`, so `L` splits into root spaces, and the product of the
two root spaces lands in `C` — which is exactly the hypothesis of the graded classification.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {C U : Type*} [Field C] [Field U] [Algebra C U]

/-- The adjoint action `Z ↦ X Z - Z X`, as a `C`-linear map. -/
def adMap (C : Type*) [Field C] {U : Type*} [Field U] [Algebra C U]
    (X : Matrix (Fin 2) (Fin 2) U) :
    Matrix (Fin 2) (Fin 2) U →ₗ[C] Matrix (Fin 2) (Fin 2) U where
  toFun Z := X * Z - Z * X
  map_add' Z W := by
    simp only [Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c Z := by
    simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul, smul_sub]

@[simp] theorem adMap_apply (X Z : Matrix (Fin 2) (Fin 2) U) :
    adMap C X Z = X * Z - Z * X := rfl

/-- Conjugation `Z ↦ P Z Q`, as a `C`-linear map. -/
def conjLinear (C : Type*) [Field C] {U : Type*} [Field U] [Algebra C U]
    (P Q : Matrix (Fin 2) (Fin 2) U) :
    Matrix (Fin 2) (Fin 2) U →ₗ[C] Matrix (Fin 2) (Fin 2) U where
  toFun Z := P * Z * Q
  map_add' Z W := by simp only [Matrix.mul_add, Matrix.add_mul]
  map_smul' c Z := by simp only [RingHom.id_apply, Matrix.mul_smul, Matrix.smul_mul]

@[simp] theorem conjLinear_apply (P Q Z : Matrix (Fin 2) (Fin 2) U) :
    conjLinear C P Q Z = P * Z * Q := rfl

/-- Scaling a fixed matrix, as a `C`-linear map on the scalars. -/
def smulMat (C : Type*) [Field C] {U : Type*} [Field U] [Algebra C U]
    (M : Matrix (Fin 2) (Fin 2) U) : U →ₗ[C] Matrix (Fin 2) (Fin 2) U where
  toFun u := u • M
  map_add' u v := by rw [add_smul]
  map_smul' c u := by simp only [RingHom.id_apply, smul_assoc]

@[simp] theorem smulMat_apply (M : Matrix (Fin 2) (Fin 2) U) (u : U) :
    smulMat C M u = u • M := rfl

/-- The bracket with a toral element. -/
theorem bracket_toral (μ : U) (Z : Matrix (Fin 2) (Fin 2) U) :
    (μ • sl2H U) * Z - Z * (μ • sl2H U)
      = (2 * μ * Z 0 1) • sl2E U - (2 * μ * Z 1 0) • sl2F U := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, smul_eq_mul] <;>
    simp [sl2H, sl2E, sl2F] <;> ring

/-- The square of the bracket with a toral element. -/
theorem bracket_toral_sq (μ : U) (Z : Matrix (Fin 2) (Fin 2) U) :
    (μ • sl2H U) * ((μ • sl2H U) * Z - Z * (μ • sl2H U))
        - ((μ • sl2H U) * Z - Z * (μ • sl2H U)) * (μ • sl2H U)
      = (4 * μ ^ 2 * Z 0 1) • sl2E U + (4 * μ ^ 2 * Z 1 0) • sl2F U := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, smul_eq_mul] <;>
    simp [sl2H, sl2E, sl2F] <;> ring

/-- The bracket of two elements of the root part. -/
theorem bracket_root (b c b' c' : U) :
    (b • sl2E U + c • sl2F U) * (b' • sl2E U + c' • sl2F U)
      - (b' • sl2E U + c' • sl2F U) * (b • sl2E U + c • sl2F U)
      = (b * c' - c * b') • sl2H U := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
      Matrix.smul_apply, smul_eq_mul] <;>
    simp [sl2H, sl2E, sl2F] <;> ring

/-- A traceless matrix in the `h, e, f` basis. -/
theorem traceless_decomp {Z : Matrix (Fin 2) (Fin 2) U} (hZ : Z.trace = 0) :
    Z = (Z 0 0) • sl2H U + (Z 0 1) • sl2E U + (Z 1 0) • sl2F U := by
  have h11 : Z 1 1 = -(Z 0 0) := by
    rw [Matrix.trace_fin_two] at hZ
    linear_combination hZ
  ext i j
  fin_cases i <;> fin_cases j <;> simp [sl2H, sl2E, sl2F, h11]

/-- **Cassidy's classification for `sl₂`, toral case.** -/
theorem cassidy_sl2_of_toral [IsAlgClosed C] [CharZero U]
    (L : Submodule C (Matrix (Fin 2) (Fin 2) U))
    (htr : ∀ A ∈ L, A.trace = 0)
    (hbr : ∀ A ∈ L, ∀ B ∈ L, A * B - B * A ∈ L)
    (hdense : ∀ Z : Matrix (Fin 2) (Fin 2) U, Z.trace = 0 →
      Z ∈ Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U)))
    (hline : ∀ A ∈ L, A.det ≠ 0 → ∀ c : U, c • A ∈ L → ∃ c₀ : C, c = algebraMap C U c₀)
    {μ : U} (hμ : μ ≠ 0) (hXmem : μ • sl2H U ∈ L) :
    ∃ (v₀ w₀ : U) (b₀ : C), v₀ ≠ 0 ∧ w₀ ≠ 0 ∧ b₀ ≠ 0 ∧ v₀ * w₀ = algebraMap C U b₀ ∧
      L = Submodule.span C {sl2H U, v₀ • sl2E U, w₀ • sl2F U} := by
  classical
  haveI : CharZero C := (algebraMap C U).charZero
  have hCsmul : ∀ (c₀ : C) (M : Matrix (Fin 2) (Fin 2) U), M ∈ L →
      (algebraMap C U c₀) • M ∈ L := by
    intro c₀ M hM
    rw [algebraMap_smul U]
    exact L.smul_mem c₀ hM
  have hHdet : (sl2H U).det ≠ 0 := by
    simp [sl2H, Matrix.det_fin_two]
  set X : Matrix (Fin 2) (Fin 2) U := μ • sl2H U with hXdef
  have hXdet : X.det ≠ 0 := by
    rw [hXdef]
    have hval : ((μ • sl2H U : Matrix (Fin 2) (Fin 2) U)).det = -(μ * μ) := by
      simp [sl2H, Matrix.det_fin_two]
    rw [hval]
    exact neg_ne_zero.mpr (mul_ne_zero hμ hμ)
  set Φ : Matrix (Fin 2) (Fin 2) U →ₗ[C] Matrix (Fin 2) (Fin 2) U :=
    (adMap C X).comp (adMap C X) with hΦdef
  set ΦU : Matrix (Fin 2) (Fin 2) U →ₗ[U] Matrix (Fin 2) (Fin 2) U :=
    (adMap U X).comp (adMap U X) with hΦUdef
  have hΦval : ∀ Z : Matrix (Fin 2) (Fin 2) U,
      Φ Z = (4 * μ ^ 2 * Z 0 1) • sl2E U + (4 * μ ^ 2 * Z 1 0) • sl2F U := by
    intro Z
    show X * (X * Z - Z * X) - (X * Z - Z * X) * X = _
    rw [hXdef]
    exact bracket_toral_sq μ Z
  have hΦmemL : ∀ Z ∈ L, Φ Z ∈ L := fun Z hZ => hbr _ hXmem _ (hbr _ hXmem _ hZ)
  have htrEF : (sl2E U + sl2F U).trace = 0 := by
    simp [sl2E, sl2F, Matrix.trace_fin_two]
  have hspan : Φ (sl2E U + sl2F U) ∈
      Submodule.span U ((L.map Φ : Submodule C (Matrix (Fin 2) (Fin 2) U)) :
        Set (Matrix (Fin 2) (Fin 2) U)) := by
    have h1 : (sl2E U + sl2F U) ∈ Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U)) :=
      hdense _ htrEF
    have h3 : ΦU (sl2E U + sl2F U) ∈
        Submodule.map ΦU (Submodule.span U (L : Set (Matrix (Fin 2) (Fin 2) U))) :=
      Submodule.mem_map_of_mem h1
    rw [Submodule.map_span] at h3
    have h4 : ⇑ΦU '' (L : Set (Matrix (Fin 2) (Fin 2) U))
        = ((L.map Φ : Submodule C (Matrix (Fin 2) (Fin 2) U)) :
            Set (Matrix (Fin 2) (Fin 2) U)) := by
      rw [Submodule.map_coe]
      rfl
    rw [h4] at h3
    exact h3
  have hdetΦef : (Φ (sl2E U + sl2F U)).det ≠ 0 := by
    have hE01 : (sl2E U + sl2F U) 0 1 = 1 := by simp [sl2E, sl2F]
    have hE10 : (sl2E U + sl2F U) 1 0 = 1 := by simp [sl2E, sl2F]
    rw [hΦval, hE01, hE10]
    have hval : ((4 * μ ^ 2 * 1 : U) • sl2E U + (4 * μ ^ 2 * 1 : U) • sl2F U).det
        = -((4 * μ ^ 2) * (4 * μ ^ 2)) := by
      simp [Matrix.det_fin_two, sl2E, sl2F]
    rw [hval]
    have h4 : (4 * μ ^ 2 : U) ≠ 0 := mul_ne_zero (by norm_num) (pow_ne_zero 2 hμ)
    exact neg_ne_zero.mpr (mul_ne_zero h4 h4)
  obtain ⟨A₂, hA₂map, hA₂det⟩ := exists_det_ne_zero_of_mem_span (L.map Φ) hspan hdetΦef
  obtain ⟨Z₀, hZ₀L, hZ₀⟩ := hA₂map
  have hA₂L : A₂ ∈ L := by rw [← hZ₀]; exact hΦmemL Z₀ hZ₀L
  obtain ⟨b, c, hA₂eq⟩ : ∃ b c : U, A₂ = b • sl2E U + c • sl2F U :=
    ⟨_, _, by rw [← hZ₀, hΦval]⟩
  have h01 : A₂ 0 1 = b := by rw [hA₂eq]; simp [sl2E, sl2F]
  have h10 : A₂ 1 0 = c := by rw [hA₂eq]; simp [sl2E, sl2F]
  have hdetbc : A₂.det = -(b * c) := by
    rw [hA₂eq]
    simp [Matrix.det_fin_two, sl2E, sl2F]
  have hbne : b ≠ 0 := by
    intro h0
    apply hA₂det
    rw [hdetbc, h0]
    ring
  have hcne : c ≠ 0 := by
    intro h0
    apply hA₂det
    rw [hdetbc, h0]
    ring
  have hA₃eq : X * A₂ - A₂ * X = (2 * μ * b) • sl2E U + (-(2 * μ * c)) • sl2F U := by
    rw [hXdef, bracket_toral, h01, h10, neg_smul, ← sub_eq_add_neg]
  have hA₃L : X * A₂ - A₂ * X ∈ L := hbr _ hXmem _ hA₂L
  have hbcX : (-(4 * b * c) : U) • X ∈ L := by
    have hbrk := hbr _ hA₂L _ hA₃L
    rw [hA₃eq, hA₂eq, bracket_root] at hbrk
    have hconv : (b * -(2 * μ * c) - c * (2 * μ * b)) • sl2H U = (-(4 * b * c) : U) • X := by
      rw [hXdef, smul_smul]
      congr 1
      ring
    rwa [hconv] at hbrk
  obtain ⟨t, ht⟩ := hline X hXmem hXdet (-(4 * b * c)) hbcX
  have hA₃X : (X * A₂ - A₂ * X) * X - X * (X * A₂ - A₂ * X) = (-(4 * μ ^ 2) : U) • A₂ := by
    rw [hA₃eq, hA₂eq, hXdef]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply, Fin.sum_univ_two,
        Matrix.smul_apply, smul_eq_mul] <;>
      simp [sl2H, sl2E, sl2F] <;> ring
  have hμ2mem : (-(4 * μ ^ 2) : U) • A₂ ∈ L := by
    rw [← hA₃X]
    exact hbr _ hA₃L _ hXmem
  obtain ⟨s, hs⟩ := hline A₂ hA₂L hA₂det _ hμ2mem
  obtain ⟨ν, hν⟩ : ∃ ν : C, μ = algebraMap C U ν := by
    obtain ⟨ν₀, hν₀⟩ := IsAlgClosed.exists_pow_nat_eq (-(s / 4)) (n := 2) (by norm_num)
    have hsq : (algebraMap C U ν₀) ^ 2 = μ ^ 2 := by
      rw [← map_pow, hν₀, map_neg, map_div₀, map_ofNat]
      linear_combination hs / 4
    have hfac : (μ - algebraMap C U ν₀) * (μ + algebraMap C U ν₀) = 0 := by
      linear_combination -hsq
    rcases mul_eq_zero.mp hfac with h | h
    · exact ⟨ν₀, by linear_combination h⟩
    · exact ⟨-ν₀, by rw [map_neg]; linear_combination h⟩
  have hν0 : ν ≠ 0 := by
    intro h0
    apply hμ
    rw [hν, h0, map_zero]
  have hHmem : sl2H U ∈ L := by
    have h := hCsmul ν⁻¹ X hXmem
    rw [hXdef, smul_smul, hν, ← map_mul, inv_mul_cancel₀ hν0, map_one, one_smul] at h
    exact h
  have hsplit : ∀ Z ∈ L, (Z 0 1) • sl2E U ∈ L ∧ (Z 1 0) • sl2F U ∈ L := by
    intro Z hZ
    have h1 : sl2H U * Z - Z * sl2H U ∈ L := hbr _ hHmem _ hZ
    have h2 : sl2H U * (sl2H U * Z - Z * sl2H U) - (sl2H U * Z - Z * sl2H U) * sl2H U ∈ L :=
      hbr _ hHmem _ h1
    have e1 : sl2H U * Z - Z * sl2H U = (2 * Z 0 1) • sl2E U - (2 * Z 1 0) • sl2F U := by
      have h := bracket_toral (1 : U) Z
      simpa using h
    have e2 : sl2H U * (sl2H U * Z - Z * sl2H U) - (sl2H U * Z - Z * sl2H U) * sl2H U
        = (4 * Z 0 1) • sl2E U + (4 * Z 1 0) • sl2F U := by
      have h := bracket_toral_sq (1 : U) Z
      simpa using h
    rw [e1] at h1
    rw [e2] at h2
    have h2' : (algebraMap C U (2 : C)) • ((2 * Z 0 1) • sl2E U - (2 * Z 1 0) • sl2F U) ∈ L :=
      hCsmul 2 _ h1
    have h2'' : ((2 : U)) • ((2 * Z 0 1) • sl2E U - (2 * Z 1 0) • sl2F U) ∈ L := by
      rwa [map_ofNat] at h2'
    have hn2 : (algebraMap C U (-2 : C)) • ((2 * Z 0 1) • sl2E U - (2 * Z 1 0) • sl2F U) ∈ L :=
      hCsmul (-2) _ h1
    have hn2' : ((-2 : U)) • ((2 * Z 0 1) • sl2E U - (2 * Z 1 0) • sl2F U) ∈ L := by
      rw [map_neg, map_ofNat] at hn2
      exact hn2
    constructor
    · have hsum := L.add_mem h2 h2''
      have hscal := hCsmul (8 : C)⁻¹ _ hsum
      rw [map_inv₀, map_ofNat] at hscal
      have heq : ((8 : U))⁻¹ • (((4 * Z 0 1) • sl2E U + (4 * Z 1 0) • sl2F U)
          + (2 : U) • ((2 * Z 0 1) • sl2E U - (2 * Z 1 0) • sl2F U)) = (Z 0 1) • sl2E U := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] <;>
          simp [sl2E, sl2F] <;> field_simp <;> ring
      rwa [heq] at hscal
    · have hsum := L.add_mem h2 hn2'
      have hscal := hCsmul (8 : C)⁻¹ _ hsum
      rw [map_inv₀, map_ofNat] at hscal
      have heq : ((8 : U))⁻¹ • (((4 * Z 0 1) • sl2E U + (4 * Z 1 0) • sl2F U)
          + (-2 : U) • ((2 * Z 0 1) • sl2E U - (2 * Z 1 0) • sl2F U)) = (Z 1 0) • sl2F U := by
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul] <;>
          simp [sl2E, sl2F] <;> field_simp <;> ring
      rwa [heq] at hscal
  have hHpart : ∀ Z ∈ L, (Z 0 0) • sl2H U ∈ L := by
    intro Z hZ
    obtain ⟨hE, hF⟩ := hsplit Z hZ
    have hmem := L.sub_mem (L.sub_mem hZ hE) hF
    have heq : Z - (Z 0 1) • sl2E U - (Z 1 0) • sl2F U = (Z 0 0) • sl2H U := by
      have h11 : Z 1 1 = -(Z 0 0) := by
        have h := htr Z hZ
        rw [Matrix.trace_fin_two] at h
        linear_combination h
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [sl2H, sl2E, sl2F, h11]
    rwa [heq] at hmem
  set V : Submodule C U := L.comap (smulMat C (sl2E U)) with hVdef
  set W : Submodule C U := L.comap (smulMat C (sl2F U)) with hWdef
  have hVmem : ∀ u : U, u ∈ V ↔ u • sl2E U ∈ L := fun u => Iff.rfl
  have hWmem : ∀ u : U, u ∈ W ↔ u • sl2F U ∈ L := fun u => Iff.rfl
  have hbV : b ∈ V := by
    rw [hVmem, ← h01]
    exact (hsplit A₂ hA₂L).1
  have hcW : c ∈ W := by
    rw [hWmem, ← h10]
    exact (hsplit A₂ hA₂L).2
  have hVne : V ≠ ⊥ := fun h0 => hbne (by rw [h0] at hbV; simpa using hbV)
  have hWne : W ≠ ⊥ := fun h0 => hcne (by rw [h0] at hcW; simpa using hcW)
  have hclosed : ∀ v ∈ V, ∀ w ∈ W, ∃ q : C,
      (v • sl2E U) * (w • sl2F U) - (w • sl2F U) * (v • sl2E U)
        = (algebraMap C U q) • sl2H U := by
    intro v hv w hw
    have hbrk : (v • sl2E U) * (w • sl2F U) - (w • sl2F U) * (v • sl2E U) ∈ L :=
      hbr _ ((hVmem v).mp hv) _ ((hWmem w).mp hw)
    rw [sl2_bracket_smul_E_F] at hbrk
    obtain ⟨q, hq⟩ := hline (sl2H U) hHmem hHdet (v * w) hbrk
    exact ⟨q, by rw [sl2_bracket_smul_E_F, hq]⟩
  obtain ⟨v₀, w₀, b₀, hv₀, hw₀, hb₀, hVspan, hWspan, hprod, -, -, -⟩ :=
    graded_cassidy_sl2 V W hVne hWne hclosed
  refine ⟨v₀, w₀, b₀, hv₀, hw₀, hb₀, hprod, le_antisymm ?_ ?_⟩
  · intro Z hZ
    obtain ⟨hE, hF⟩ := hsplit Z hZ
    have hH := hHpart Z hZ
    obtain ⟨a₀, ha₀⟩ := hline (sl2H U) hHmem hHdet (Z 0 0) hH
    have hZ01 : Z 0 1 ∈ V := (hVmem _).mpr hE
    have hZ10 : Z 1 0 ∈ W := (hWmem _).mpr hF
    rw [hVspan, Submodule.mem_span_singleton] at hZ01
    rw [hWspan, Submodule.mem_span_singleton] at hZ10
    obtain ⟨q₁, hq₁⟩ := hZ01
    obtain ⟨q₂, hq₂⟩ := hZ10
    have hdecomp : Z = (Z 0 0) • sl2H U + (Z 0 1) • sl2E U + (Z 1 0) • sl2F U :=
      traceless_decomp (htr Z hZ)
    rw [hdecomp, ha₀, ← hq₁, ← hq₂]
    have hs1 : sl2H U ∈ Submodule.span C ({sl2H U, v₀ • sl2E U, w₀ • sl2F U} :
        Set (Matrix (Fin 2) (Fin 2) U)) := Submodule.subset_span (by simp)
    have hs2 : v₀ • sl2E U ∈ Submodule.span C ({sl2H U, v₀ • sl2E U, w₀ • sl2F U} :
        Set (Matrix (Fin 2) (Fin 2) U)) := Submodule.subset_span (by simp)
    have hs3 : w₀ • sl2F U ∈ Submodule.span C ({sl2H U, v₀ • sl2E U, w₀ • sl2F U} :
        Set (Matrix (Fin 2) (Fin 2) U)) := Submodule.subset_span (by simp)
    refine Submodule.add_mem _ (Submodule.add_mem _ ?_ ?_) ?_
    · rw [algebraMap_smul U]
      exact Submodule.smul_mem _ _ hs1
    · rw [smul_assoc]
      exact Submodule.smul_mem _ _ hs2
    · rw [smul_assoc]
      exact Submodule.smul_mem _ _ hs3
  · rw [Submodule.span_le]
    rintro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact hHmem
    · exact (hVmem v₀).mp (by rw [hVspan]; exact Submodule.mem_span_singleton_self v₀)
    · exact (hWmem w₀).mp (by rw [hWspan]; exact Submodule.mem_span_singleton_self w₀)

end

end GaloisForLFunctions.HTGeometry
