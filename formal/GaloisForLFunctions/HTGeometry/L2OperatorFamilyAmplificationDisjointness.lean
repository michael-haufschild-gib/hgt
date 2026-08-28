import GaloisForLFunctions.HTGeometry.LpSingleExtension
import GaloisForLFunctions.HTGeometry.SourceLinearClosedRelationSplitting

/-!
# Disjoint operator families remain disjoint under arbitrary ell-two amplification

Let `A_i` and `B_i` be disjoint bounded operator families. Their coordinatewise actions on
`ell2(Gamma, H1)` and `ell2(Gamma, H2)` remain disjoint for an arbitrary multiplicity type
`Gamma`. Indeed, every matrix coefficient of an amplified intertwiner is a base intertwiner and
hence zero; density of coordinate singles then kills the full amplified map.

This module also constructs the coordinatewise amplification as a bounded operator and proves
that it commutes with Hilbert adjoints.
-/

open scoped ENNReal

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {Γ H₁ H₂ : Type*} [DecidableEq Γ]
  [NormedAddCommGroup H₁] [NormedAddCommGroup H₂]
  [InnerProductSpace ℂ H₁] [InnerProductSpace ℂ H₂]

/-- Hilbert `ell²` multiplicity amplification of a Hilbert space. -/
abbrev L2Amplification (Γ H : Type*) [DecidableEq Γ]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] :=
  lp (fun _ : Γ => H) 2

theorem memLp_l2Amplification (T : H₁ →L[ℂ] H₂)
    (f : L2Amplification Γ H₁) :
    Memℓp (fun i => T (f i)) 2 := by
  refine memℓp_gen ?_
  have hsum : Summable fun i => ‖f i‖ ^ (2 : ℝ) :=
    (lp.memℓp f).summable (by norm_num)
  refine Summable.of_nonneg_of_le
    (fun i => Real.rpow_nonneg (norm_nonneg _) 2) ?_
    (hsum.mul_left (‖T‖ ^ (2 : ℝ)))
  intro i
  calc
    ‖T (f i)‖ ^ (2 : ℝ) ≤ (‖T‖ * ‖f i‖) ^ (2 : ℝ) :=
      Real.rpow_le_rpow (norm_nonneg _) (T.le_opNorm _) (by norm_num)
    _ = ‖T‖ ^ (2 : ℝ) * ‖f i‖ ^ (2 : ℝ) := by
      rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]

/-- Coordinatewise amplification of a bounded operator, as a linear map. -/
def l2AmplificationLM (T : H₁ →L[ℂ] H₂) :
    L2Amplification Γ H₁ →ₗ[ℂ] L2Amplification Γ H₂ where
  toFun f := ⟨fun i => T (f i), memLp_l2Amplification T f⟩
  map_add' f g := by
    ext i
    simp
  map_smul' c f := by
    ext i
    simp

@[simp] theorem l2AmplificationLM_apply (T : H₁ →L[ℂ] H₂)
    (f : L2Amplification Γ H₁) (i : Γ) :
    l2AmplificationLM T f i = T (f i) := rfl

theorem norm_l2AmplificationLM_le (T : H₁ →L[ℂ] H₂)
    (f : L2Amplification Γ H₁) :
    ‖l2AmplificationLM T f‖ ≤ ‖T‖ * ‖f‖ := by
  have hnn : 0 ≤ ‖l2AmplificationLM T f‖ := norm_nonneg _
  have hrhs : 0 ≤ ‖T‖ * ‖f‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hout : ‖l2AmplificationLM T f‖ ^ (2 : ℝ) =
      ∑' i, ‖l2AmplificationLM T f i‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2)
      (E := fun _ : Γ => H₂) (by norm_num) (l2AmplificationLM T f)
  have hin : ‖f‖ ^ (2 : ℝ) = ∑' i, ‖f i‖ ^ (2 : ℝ) := by
    simpa using lp.norm_rpow_eq_tsum (p := 2)
      (E := fun _ : Γ => H₁) (by norm_num) f
  have hsumin : Summable fun i => ‖f i‖ ^ (2 : ℝ) :=
    (lp.memℓp f).summable (by norm_num)
  have hsumout : Summable fun i => ‖l2AmplificationLM T f i‖ ^ (2 : ℝ) :=
    (lp.memℓp (l2AmplificationLM T f)).summable (by norm_num)
  have hterm : ∀ i, ‖l2AmplificationLM T f i‖ ^ (2 : ℝ) ≤
      ‖T‖ ^ (2 : ℝ) * ‖f i‖ ^ (2 : ℝ) := by
    intro i
    rw [l2AmplificationLM_apply]
    calc
      ‖T (f i)‖ ^ (2 : ℝ) ≤ (‖T‖ * ‖f i‖) ^ (2 : ℝ) :=
        Real.rpow_le_rpow (norm_nonneg _) (T.le_opNorm _) (by norm_num)
      _ = _ := by rw [Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  have hpow : ‖l2AmplificationLM T f‖ ^ (2 : ℝ) ≤
      (‖T‖ * ‖f‖) ^ (2 : ℝ) := by
    rw [hout, Real.mul_rpow (norm_nonneg _) (norm_nonneg _), hin, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hterm hsumout
      (hsumin.mul_left (‖T‖ ^ (2 : ℝ)))
  have hx2 : ‖l2AmplificationLM T f‖ ^ (2 : ℝ) =
      ‖l2AmplificationLM T f‖ ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  have hy2 : (‖T‖ * ‖f‖) ^ (2 : ℝ) =
      (‖T‖ * ‖f‖) ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast _ 2]
    norm_num
  rw [hx2, hy2] at hpow
  have hs := Real.sqrt_le_sqrt hpow
  rwa [Real.sqrt_sq hnn, Real.sqrt_sq hrhs] at hs

/-- Coordinatewise amplification of a bounded operator. -/
def l2Amplification (T : H₁ →L[ℂ] H₂) :
    L2Amplification Γ H₁ →L[ℂ] L2Amplification Γ H₂ :=
  LinearMap.mkContinuous (l2AmplificationLM T) ‖T‖
    (norm_l2AmplificationLM_le T)

@[simp] theorem l2Amplification_apply (T : H₁ →L[ℂ] H₂)
    (f : L2Amplification Γ H₁) (i : Γ) :
    l2Amplification T f i = T (f i) := rfl

/-- Injection into one amplification coordinate. -/
noncomputable def l2Single (i : Γ) : H₁ →L[ℂ] L2Amplification Γ H₁ :=
  LinearMap.mkContinuous
    (lp.lsingle (E := fun _ : Γ => H₁) (𝕜 := ℂ) 2 i) 1 (fun x => by
      rw [one_mul]
      show ‖lp.single (E := fun _ : Γ => H₁) 2 i x‖ ≤ ‖x‖
      rw [lp.norm_single (by norm_num)])

@[simp] theorem l2Single_apply (i : Γ) (x : H₁) :
    l2Single i x = lp.single 2 i x := rfl

/-- Projection from an amplification onto one coordinate. -/
noncomputable def l2Coordinate (i : Γ) : L2Amplification Γ H₁ →L[ℂ] H₁ :=
  lp.evalCLM ℂ (fun _ : Γ => H₁) 2 i

@[simp] theorem l2Coordinate_apply (i : Γ)
    (f : L2Amplification Γ H₁) : l2Coordinate i f = f i := rfl

@[simp] theorem l2Coordinate_single_same (i : Γ) (x : H₁) :
    l2Coordinate i (l2Single i x) = x := by
  simp [l2Coordinate_apply, l2Single_apply, lp.single_apply]

@[simp] theorem l2Amplification_single (T : H₁ →L[ℂ] H₂)
    (i : Γ) (x : H₁) :
    l2Amplification T (l2Single i x) = l2Single i (T x) := by
  ext j
  simp only [l2Amplification_apply, l2Single_apply, lp.single_apply]
  by_cases h : i = j
  · subst j
    simp
  · simp [h]

/-- Coordinatewise amplification commutes with Hilbert adjoints. -/
theorem adjoint_l2Amplification [CompleteSpace H₁] (T : H₁ →L[ℂ] H₁) :
    (l2Amplification (Γ := Γ) T).adjoint =
      l2Amplification (Γ := Γ) T.adjoint := by
  symm
  rw [ContinuousLinearMap.eq_adjoint_iff]
  intro x y
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr fun i => ?_
  change inner ℂ (T.adjoint (x i)) (y i) = inner ℂ (x i) (T (y i))
  rw [ContinuousLinearMap.adjoint_inner_left]

/-- Disjointness is stable under arbitrary Hilbert `ell²` multiplicity amplification. -/
theorem operatorFamiliesDisjoint_l2Amplification
    {I : Type*} {A : I → H₁ →L[ℂ] H₁} {B : I → H₂ →L[ℂ] H₂}
    (hdisj : OperatorFamiliesDisjoint A B) :
    OperatorFamiliesDisjoint
      (fun i => l2Amplification (Γ := Γ) (A i))
      (fun i => l2Amplification (Γ := Γ) (B i)) := by
  constructor
  · intro V hV
    apply ext_of_eq_on_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro k x
    apply lp.ext
    funext j
    let W : H₁ →L[ℂ] H₂ :=
      l2Coordinate j ∘L V ∘L l2Single k
    have hWinter : ∀ i, W ∘L A i = B i ∘L W := by
      intro i
      ext y
      have h :
          V (l2Amplification (Γ := Γ) (A i) (l2Single k y)) =
            l2Amplification (Γ := Γ) (B i) (V (l2Single k y)) := by
        simpa only [ContinuousLinearMap.comp_apply] using
          DFunLike.congr_fun (hV i) (l2Single k y)
      have hsingleA : l2Amplification (Γ := Γ) (A i) (l2Single k y) =
          l2Single k (A i y) := l2Amplification_single (A i) k y
      rw [hsingleA] at h
      simpa [W, ContinuousLinearMap.comp_apply, l2Coordinate_apply] using
        congrArg (l2Coordinate j) h
    have hW : W = 0 := hdisj.1 W hWinter
    have hwx := DFunLike.congr_fun hW x
    simpa [W, ContinuousLinearMap.comp_apply, l2Coordinate_apply] using hwx
  · intro W hW
    apply ext_of_eq_on_single (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    intro k y
    apply lp.ext
    funext j
    let V : H₂ →L[ℂ] H₁ :=
      l2Coordinate j ∘L W ∘L l2Single k
    have hVinter : ∀ i, V ∘L B i = A i ∘L V := by
      intro i
      ext x
      have h :
          W (l2Amplification (Γ := Γ) (B i) (l2Single k x)) =
            l2Amplification (Γ := Γ) (A i) (W (l2Single k x)) := by
        simpa only [ContinuousLinearMap.comp_apply] using
          DFunLike.congr_fun (hW i) (l2Single k x)
      have hsingleB : l2Amplification (Γ := Γ) (B i) (l2Single k x) =
          l2Single k (B i x) := l2Amplification_single (B i) k x
      rw [hsingleB] at h
      simpa [V, ContinuousLinearMap.comp_apply, l2Coordinate_apply] using
        congrArg (l2Coordinate j) h
    have hV : V = 0 := hdisj.2 V hVinter
    have hvy := DFunLike.congr_fun hV y
    simpa [V, ContinuousLinearMap.comp_apply, l2Coordinate_apply] using hvy

end

end GaloisForLFunctions.HTGeometry
