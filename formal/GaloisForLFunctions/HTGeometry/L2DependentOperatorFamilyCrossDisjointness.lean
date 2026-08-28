import GaloisForLFunctions.HTGeometry.L2OperatorFamilyAmplificationDisjointness

/-!
# Cross-disjoint operator families on dependent ell-two sums

This module constructs uniformly bounded coordinatewise operators on dependent Hilbert `ell²`
sums. If every left coordinate representation is disjoint from every right coordinate
representation, the two dependent direct-sum representations remain disjoint. Every matrix block
of an intertwiner is a forbidden coordinate intertwiner, and coordinate-single density kills the
whole map.
-/

open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {Γ : Type*} [DecidableEq Γ]
  {E : Γ → Type*} {F : Γ → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, NormedAddCommGroup (F i)]
  [∀ i, InnerProductSpace ℂ (E i)] [∀ i, InnerProductSpace ℂ (F i)]

/-- Dependent Hilbert `ell²` sum. -/
abbrev L2DependentSum (Γ : Type*) (E : Γ → Type*) [DecidableEq Γ]
    [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℂ (E i)] :=
  lp E 2

theorem memLp_l2DependentDiagonal
    (T : ∀ i, E i →L[ℂ] F i) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ i, ‖T i‖ ≤ C) (f : L2DependentSum Γ E) :
    Memℓp (fun i => T i (f i)) 2 := by
  refine memℓp_gen ?_
  have hsum : Summable fun i => ‖f i‖ ^ (2 : ℝ) :=
    (lp.memℓp f).summable (by norm_num)
  refine Summable.of_nonneg_of_le
    (fun i => Real.rpow_nonneg (norm_nonneg _) 2) ?_
    (hsum.mul_left (C ^ (2 : ℝ)))
  intro i
  have happly : ‖T i (f i)‖ ≤ C * ‖f i‖ :=
    (T i).le_opNorm (f i) |>.trans
      (mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _))
  calc
    ‖T i (f i)‖ ^ (2 : ℝ) ≤ (C * ‖f i‖) ^ (2 : ℝ) :=
      Real.rpow_le_rpow (norm_nonneg _) happly (by norm_num)
    _ = C ^ (2 : ℝ) * ‖f i‖ ^ (2 : ℝ) := by
      rw [Real.mul_rpow hC0 (norm_nonneg _)]

/-- Uniformly bounded coordinatewise operator on a dependent `ell²` sum, as a linear map. -/
def l2DependentDiagonalLM
    (T : ∀ i, E i →L[ℂ] F i) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ i, ‖T i‖ ≤ C) :
    L2DependentSum Γ E →ₗ[ℂ] L2DependentSum Γ F where
  toFun f := ⟨fun i => T i (f i), memLp_l2DependentDiagonal T C hC0 hC f⟩
  map_add' f g := by
    ext i
    simp
  map_smul' c f := by
    ext i
    simp

@[simp] theorem l2DependentDiagonalLM_apply
    (T : ∀ i, E i →L[ℂ] F i) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ i, ‖T i‖ ≤ C) (f : L2DependentSum Γ E) (i : Γ) :
    l2DependentDiagonalLM T C hC0 hC f i = T i (f i) := rfl

theorem norm_l2DependentDiagonalLM_le
    (T : ∀ i, E i →L[ℂ] F i) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ i, ‖T i‖ ≤ C) (f : L2DependentSum Γ E) :
    ‖l2DependentDiagonalLM T C hC0 hC f‖ ≤ C * ‖f‖ := by
  have hnn : 0 ≤ ‖l2DependentDiagonalLM T C hC0 hC f‖ := norm_nonneg _
  have hrhs : 0 ≤ C * ‖f‖ := mul_nonneg hC0 (norm_nonneg _)
  have hout : ‖l2DependentDiagonalLM T C hC0 hC f‖ ^ (2 : ℝ) =
      ∑' i, ‖l2DependentDiagonalLM T C hC0 hC f i‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := F) (by norm_num)
      (l2DependentDiagonalLM T C hC0 hC f)
  have hin : ‖f‖ ^ (2 : ℝ) = ∑' i, ‖f i‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2) (E := E) (by norm_num) f
  have hsumin : Summable fun i => ‖f i‖ ^ (2 : ℝ) :=
    (lp.memℓp f).summable (by norm_num)
  have hsumout : Summable fun i =>
      ‖l2DependentDiagonalLM T C hC0 hC f i‖ ^ (2 : ℝ) :=
    (lp.memℓp (l2DependentDiagonalLM T C hC0 hC f)).summable (by norm_num)
  have hterm : ∀ i, ‖l2DependentDiagonalLM T C hC0 hC f i‖ ^ (2 : ℝ) ≤
      C ^ (2 : ℝ) * ‖f i‖ ^ (2 : ℝ) := by
    intro i
    rw [l2DependentDiagonalLM_apply]
    have happly : ‖T i (f i)‖ ≤ C * ‖f i‖ :=
      (T i).le_opNorm (f i) |>.trans
        (mul_le_mul_of_nonneg_right (hC i) (norm_nonneg _))
    calc
      ‖T i (f i)‖ ^ (2 : ℝ) ≤ (C * ‖f i‖) ^ (2 : ℝ) :=
        Real.rpow_le_rpow (norm_nonneg _) happly (by norm_num)
      _ = _ := by rw [Real.mul_rpow hC0 (norm_nonneg _)]
  have hpow : ‖l2DependentDiagonalLM T C hC0 hC f‖ ^ (2 : ℝ) ≤
      (C * ‖f‖) ^ (2 : ℝ) := by
    rw [hout, Real.mul_rpow hC0 (norm_nonneg _), hin, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm hsumout
      (hsumin.mul_left (C ^ (2 : ℝ)))
  have hx2 : ‖l2DependentDiagonalLM T C hC0 hC f‖ ^ (2 : ℝ) =
      ‖l2DependentDiagonalLM T C hC0 hC f‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  have hy2 : (C * ‖f‖) ^ (2 : ℝ) = (C * ‖f‖) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  rw [hx2, hy2] at hpow
  have hs := Real.sqrt_le_sqrt hpow
  rwa [Real.sqrt_sq hnn, Real.sqrt_sq hrhs] at hs

/-- Uniformly bounded coordinatewise operator on a dependent `ell²` sum. -/
def l2DependentDiagonal
    (T : ∀ i, E i →L[ℂ] F i) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ i, ‖T i‖ ≤ C) :
    L2DependentSum Γ E →L[ℂ] L2DependentSum Γ F :=
  LinearMap.mkContinuous (l2DependentDiagonalLM T C hC0 hC) C
    (norm_l2DependentDiagonalLM_le T C hC0 hC)

@[simp] theorem l2DependentDiagonal_apply
    (T : ∀ i, E i →L[ℂ] F i) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ i, ‖T i‖ ≤ C) (f : L2DependentSum Γ E) (i : Γ) :
    l2DependentDiagonal T C hC0 hC f i = T i (f i) := rfl

/-- Injection into one dependent-sum coordinate. -/
noncomputable def l2DependentSingle (i : Γ) :
    E i →L[ℂ] L2DependentSum Γ E :=
  LinearMap.mkContinuous (lp.lsingle (E := E) (𝕜 := ℂ) 2 i) 1 (fun x => by
    rw [one_mul]
    show ‖lp.single (E := E) 2 i x‖ ≤ ‖x‖
    rw [lp.norm_single (by norm_num)])

@[simp] theorem l2DependentSingle_apply (i : Γ) (x : E i) :
    l2DependentSingle i x = lp.single 2 i x := rfl

/-- Projection from a dependent sum onto one coordinate. -/
noncomputable def l2DependentCoordinate (i : Γ) :
    L2DependentSum Γ E →L[ℂ] E i :=
  lp.evalCLM ℂ E 2 i

@[simp] theorem l2DependentCoordinate_apply (i : Γ)
    (f : L2DependentSum Γ E) : l2DependentCoordinate i f = f i := rfl

@[simp] theorem l2DependentDiagonal_single
    (T : ∀ i, E i →L[ℂ] F i) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ i, ‖T i‖ ≤ C) (i : Γ) (x : E i) :
    l2DependentDiagonal T C hC0 hC (l2DependentSingle i x) =
      l2DependentSingle i (T i x) := by
  ext j
  simp only [l2DependentDiagonal_apply, l2DependentSingle_apply, lp.single_apply]
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

/-- The dependent coordinatewise operator commutes with adjoints. -/
theorem adjoint_l2DependentDiagonal
    [∀ i, CompleteSpace (E i)]
    (T : ∀ i, E i →L[ℂ] E i) (C : ℝ) (hC0 : 0 ≤ C)
    (hC : ∀ i, ‖T i‖ ≤ C) :
    (l2DependentDiagonal T C hC0 hC).adjoint =
      l2DependentDiagonal (fun i => (T i).adjoint) C hC0
        (fun i => by simpa using hC i) := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  change inner ℂ ((T i).adjoint (x i)) (y i) = inner ℂ (x i) (T i (y i))
  rw [ContinuousLinearMap.adjoint_inner_left]

variable {Γ₁ Γ₂ I : Type*} [DecidableEq Γ₁] [DecidableEq Γ₂]
  {E₁ : Γ₁ → Type*} {E₂ : Γ₂ → Type*}
  [∀ i, NormedAddCommGroup (E₁ i)] [∀ i, NormedAddCommGroup (E₂ i)]
  [∀ i, InnerProductSpace ℂ (E₁ i)] [∀ i, InnerProductSpace ℂ (E₂ i)]

/-- Pairwise cross-disjoint coordinate representations remain disjoint after dependent Hilbert
`ell²` direct-sum completion. -/
theorem operatorFamiliesDisjoint_l2DependentCrossSum
    (A : (γ : Γ₁) → I → E₁ γ →L[ℂ] E₁ γ)
    (B : (δ : Γ₂) → I → E₂ δ →L[ℂ] E₂ δ)
    (C : I → ℝ) (hC0 : ∀ i, 0 ≤ C i)
    (hA : ∀ i γ, ‖A γ i‖ ≤ C i)
    (hB : ∀ i δ, ‖B δ i‖ ≤ C i)
    (hcross : ∀ γ δ, OperatorFamiliesDisjoint (A γ) (B δ)) :
    OperatorFamiliesDisjoint
      (fun i => l2DependentDiagonal (fun γ => A γ i) (C i) (hC0 i) (hA i))
      (fun i => l2DependentDiagonal (fun δ => B δ i) (C i) (hC0 i) (hB i)) := by
  constructor
  · intro V hV
    apply ext_of_eq_on_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro γ x
    apply lp.ext
    funext δ
    let W : E₁ γ →L[ℂ] E₂ δ :=
      l2DependentCoordinate δ ∘L V ∘L l2DependentSingle γ
    have hWinter : ∀ i, W ∘L A γ i = B δ i ∘L W := by
      intro i
      ext y
      have h :
          V (l2DependentDiagonal (fun γ => A γ i) (C i) (hC0 i) (hA i)
              (l2DependentSingle γ y)) =
            l2DependentDiagonal (fun δ => B δ i) (C i) (hC0 i) (hB i)
              (V (l2DependentSingle γ y)) := by
        simpa only [ContinuousLinearMap.comp_apply] using
          DFunLike.congr_fun (hV i) (l2DependentSingle γ y)
      rw [l2DependentDiagonal_single] at h
      simpa [W, ContinuousLinearMap.comp_apply, l2DependentCoordinate_apply] using
        congrArg (l2DependentCoordinate δ) h
    have hW : W = 0 := (hcross γ δ).1 W hWinter
    have hwx := DFunLike.congr_fun hW x
    simpa [W, ContinuousLinearMap.comp_apply, l2DependentCoordinate_apply] using hwx
  · intro W hW
    apply ext_of_eq_on_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro δ y
    apply lp.ext
    funext γ
    let V : E₂ δ →L[ℂ] E₁ γ :=
      l2DependentCoordinate γ ∘L W ∘L l2DependentSingle δ
    have hVinter : ∀ i, V ∘L B δ i = A γ i ∘L V := by
      intro i
      ext x
      have h :
          W (l2DependentDiagonal (fun δ => B δ i) (C i) (hC0 i) (hB i)
              (l2DependentSingle δ x)) =
            l2DependentDiagonal (fun γ => A γ i) (C i) (hC0 i) (hA i)
              (W (l2DependentSingle δ x)) := by
        simpa only [ContinuousLinearMap.comp_apply] using
          DFunLike.congr_fun (hW i) (l2DependentSingle δ x)
      rw [l2DependentDiagonal_single] at h
      simpa [V, ContinuousLinearMap.comp_apply, l2DependentCoordinate_apply] using
        congrArg (l2DependentCoordinate γ) h
    have hV : V = 0 := (hcross γ δ).2 V hVinter
    have hvy := DFunLike.congr_fun hV y
    simpa [V, ContinuousLinearMap.comp_apply, l2DependentCoordinate_apply] using hvy

end

end GaloisForLFunctions.HTGeometry
