import GaloisForLFunctions.HTGeometry.PoincareHopf.GeneralDivergenceForm
import GaloisForLFunctions.HTGeometry.PoincareHopf.JacobiFormula
import GaloisForLFunctions.HTGeometry.PoincareHopf.TranslationInvariance

/-!
# The parameter derivative along a linear homotopy

Along the affine path `H t = f + t (g - f)` the integrand `φ (H t x) · det (D H t x)` of the degree
integral has `t`-derivative

  `(Dφ (H t x)) (g x - f x) · det (D H t x)
      + φ (H t x) · ∑ i j, cof (D H t x)_{i j} · (D g x - D f x)_{i j}`,

by the chain rule and Jacobi's formula.  That expression is the cofactor pairing of `D H t` with the
Jacobian of the field `x ↦ φ (H t x) · (g x - f x)`: the cofactor row contraction converts the
column derivatives of `H` back into the coordinate derivatives of `φ`.  So the parameter derivative
is exactly the integrand of the vanishing lemma for cofactor transforms.
-/

open Matrix Finset Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry.PoincareHopf

variable {n : ℕ} {f g : (Fin n → ℝ) → (Fin n → ℝ)} {φ : (Fin n → ℝ) → ℝ}

/-- The affine path from `f` to `g`. -/
noncomputable def linPath (f g : (Fin n → ℝ) → (Fin n → ℝ)) (t : ℝ) :
    (Fin n → ℝ) → (Fin n → ℝ) := fun x => f x + t • (g x - f x)

@[simp] theorem linPath_zero : linPath f g 0 = f := by funext x; simp [linPath]

@[simp] theorem linPath_one : linPath f g 1 = g := by funext x; simp [linPath]

theorem contDiff_linPath (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (t : ℝ) :
    ContDiff ℝ 2 (linPath f g t) :=
  hf.add (ContDiff.const_smul t (hg.sub hf))

theorem jac_linPath (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (t : ℝ) (x : Fin n → ℝ)
    (i j : Fin n) :
    jac (linPath f g t) x i j = jac f x i j + t * (jac g x i j - jac f x i j) := by
  have hf' : HasFDerivAt f (fderiv ℝ f x) x := (hf.differentiable (by simp) x).hasFDerivAt
  have hg' : HasFDerivAt g (fderiv ℝ g x) x := (hg.differentiable (by simp) x).hasFDerivAt
  have hp : HasFDerivAt (linPath f g t)
      (fderiv ℝ f x + t • (fderiv ℝ g x - fderiv ℝ f x)) x :=
    hf'.add ((hg'.sub hf').const_smul t)
  rw [jac, Matrix.of_apply, hp.fderiv]
  simp [jac]

theorem jac_sub (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (x : Fin n → ℝ) (i j : Fin n) :
    jac (fun y => g y - f y) x i j = jac g x i j - jac f x i j := by
  have hf' : HasFDerivAt f (fderiv ℝ f x) x := (hf.differentiable (by simp) x).hasFDerivAt
  have hg' : HasFDerivAt g (fderiv ℝ g x) x := (hg.differentiable (by simp) x).hasFDerivAt
  have hd : HasFDerivAt (fun y => g y - f y) (fderiv ℝ g x - fderiv ℝ f x) x := hg'.sub hf'
  rw [jac, Matrix.of_apply, hd.fderiv]
  simp [jac]

/-- The field whose cofactor transform carries the parameter derivative. -/
noncomputable def homField (f g : (Fin n → ℝ) → (Fin n → ℝ)) (φ : (Fin n → ℝ) → ℝ) (t : ℝ) :
    (Fin n → ℝ) → (Fin n → ℝ) := fun x => φ (linPath f g t x) • (g x - f x)

/-- The parameter derivative of the degree integrand. -/
noncomputable def homDeriv (f g : (Fin n → ℝ) → (Fin n → ℝ)) (φ : (Fin n → ℝ) → ℝ) (t : ℝ)
    (x : Fin n → ℝ) : ℝ :=
  (fderiv ℝ φ (linPath f g t x)) (g x - f x) * (jac (linPath f g t) x).det
    + φ (linPath f g t x) *
        ∑ i, ∑ j, cofSum (jac (linPath f g t) x) i j * (jac g x i j - jac f x i j)

/-- Row contraction of the cofactor matrix against the columns of the Jacobian. -/
theorem sum_cofSum_mul_apply_col {u : (Fin n → ℝ) → (Fin n → ℝ)} (L : (Fin n → ℝ) →L[ℝ] ℝ)
    (x : Fin n → ℝ) (i : Fin n) :
    ∑ j, cofSum (jac u x) i j * L (fderiv ℝ u x (Pi.single j 1))
      = L (Pi.single i 1) * (jac u x).det := by
  have hcol : ∀ j : Fin n,
      L (fderiv ℝ u x (Pi.single j 1)) = ∑ k, jac u x k j * L (Pi.single k 1) := by
    intro j
    rw [clm_apply_eq_sum (F := ℝ) L (fderiv ℝ u x (Pi.single j 1))]
    exact Finset.sum_congr rfl fun k _ => by simp [jac, smul_eq_mul]
  calc ∑ j, cofSum (jac u x) i j * L (fderiv ℝ u x (Pi.single j 1))
      = ∑ j, ∑ k, L (Pi.single k 1) * (cofSum (jac u x) i j * jac u x k j) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hcol j, Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
    _ = ∑ k, L (Pi.single k 1) * ∑ j, cofSum (jac u x) i j * jac u x k j := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun k _ => (Finset.mul_sum _ _ _).symm
    _ = ∑ k, L (Pi.single k 1) * (if k = i then (jac u x).det else 0) :=
        Finset.sum_congr rfl fun k _ => by rw [sum_cofSum_mul]
    _ = L (Pi.single i 1) * (jac u x).det := by simp

/-- Product rule for a scalar multiple of a vector field, read off the Jacobian. -/
theorem jac_smul_field {s : (Fin n → ℝ) → ℝ} {Y : (Fin n → ℝ) → (Fin n → ℝ)} {x : Fin n → ℝ}
    (hs : DifferentiableAt ℝ s x) (hY : DifferentiableAt ℝ Y x) (i j : Fin n) :
    jac (fun y => s y • Y y) x i j
      = (fderiv ℝ s x) (Pi.single j 1) * Y x i + s x * jac Y x i j := by
  have h : HasFDerivAt (fun y => s y • Y y)
      (s x • fderiv ℝ Y x + (fderiv ℝ s x).smulRight (Y x)) x :=
    hs.hasFDerivAt.smul hY.hasFDerivAt
  rw [jac, Matrix.of_apply, h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, jac,
    Matrix.of_apply]
  ring

/-- The `t`-derivative of the degree integrand along the affine path. -/
theorem hasDerivAt_homIntegrand (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hφ : ContDiff ℝ 1 φ)
    (t : ℝ) (x : Fin n → ℝ) :
    HasDerivAt (fun s => φ (linPath f g s x) * (jac (linPath f g s) x).det)
      (homDeriv f g φ t x) t := by
  have hpath : HasDerivAt (fun s : ℝ => linPath f g s x) (g x - f x) t := by
    simpa [linPath] using ((hasDerivAt_id t).smul_const (g x - f x)).const_add (f x)
  have hφ' : HasDerivAt (fun s : ℝ => φ (linPath f g s x))
      ((fderiv ℝ φ (linPath f g t x)) (g x - f x)) t := by
    have hc := ((hφ.differentiable (by simp)) (linPath f g t x)).hasFDerivAt.comp_hasDerivAt t hpath
    simpa [Function.comp_def] using hc
  have hentry : ∀ i j : Fin n, HasDerivAt (fun s => jac (linPath f g s) x i j)
      (jac g x i j - jac f x i j) t := by
    intro i j
    have heq : (fun s : ℝ => jac (linPath f g s) x i j)
        = fun s : ℝ => jac f x i j + s * (jac g x i j - jac f x i j) := by
      funext s
      exact jac_linPath hf hg s x i j
    rw [heq]
    simpa using ((hasDerivAt_id t).mul_const (jac g x i j - jac f x i j)).const_add (jac f x i j)
  have hdet := hasDerivAt_det (M := fun s => jac (linPath f g s) x)
    (M' := Matrix.of fun i j => jac g x i j - jac f x i j) (t := t) hentry
  have hmul := hφ'.mul hdet
  simp only [Pi.mul_def] at hmul
  exact hmul.congr_deriv (by simp [homDeriv, map_sub])

/-- The parameter derivative is the cofactor pairing of the Jacobian of `homField`. -/
theorem homDeriv_eq_cofPairing (hf : ContDiff ℝ 2 f) (hg : ContDiff ℝ 2 g) (hφ : ContDiff ℝ 1 φ)
    (t : ℝ) (x : Fin n → ℝ) :
    homDeriv f g φ t x
      = ∑ i, ∑ j, cofSum (jac (linPath f g t) x) i j * jac (homField f g φ t) x i j := by
  have hud : DifferentiableAt ℝ (linPath f g t) x :=
    ((contDiff_linPath hf hg t).differentiable (by simp)) x
  have hsd : DifferentiableAt ℝ (fun y => φ (linPath f g t y)) x :=
    ((hφ.differentiable (by simp)) (linPath f g t x)).comp x hud
  have hYd : DifferentiableAt ℝ (fun y => g y - f y) x :=
    ((hg.differentiable (by simp)) x).sub ((hf.differentiable (by simp)) x)
  have hchain : fderiv ℝ (fun y => φ (linPath f g t y)) x
      = (fderiv ℝ φ (linPath f g t x)).comp (fderiv ℝ (linPath f g t) x) :=
    (((hφ.differentiable (by simp)) (linPath f g t x)).hasFDerivAt.comp x hud.hasFDerivAt).fderiv
  have hterm : ∀ i j : Fin n, jac (homField f g φ t) x i j
      = (fderiv ℝ φ (linPath f g t x)) (fderiv ℝ (linPath f g t) x (Pi.single j 1))
          * (g x i - f x i)
        + φ (linPath f g t x) * (jac g x i j - jac f x i j) := by
    intro i j
    have hunfold : jac (homField f g φ t) x i j
        = jac (fun y => φ (linPath f g t y) • (g y - f y)) x i j := rfl
    rw [hunfold, jac_smul_field hsd hYd i j, hchain, jac_sub hf hg x i j]
    simp
  have hsplit : (∑ i, ∑ j, cofSum (jac (linPath f g t) x) i j * jac (homField f g φ t) x i j)
      = (∑ i, (g x i - f x i) *
            ∑ j, cofSum (jac (linPath f g t) x) i j *
              (fderiv ℝ φ (linPath f g t x)) (fderiv ℝ (linPath f g t) x (Pi.single j 1)))
        + φ (linPath f g t x) *
            ∑ i, ∑ j, cofSum (jac (linPath f g t) x) i j * (jac g x i j - jac f x i j) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hterm i j]
    ring
  have hcontract : (∑ i, (g x i - f x i) *
        ∑ j, cofSum (jac (linPath f g t) x) i j *
          (fderiv ℝ φ (linPath f g t x)) (fderiv ℝ (linPath f g t) x (Pi.single j 1)))
      = (fderiv ℝ φ (linPath f g t x)) (g x - f x) * (jac (linPath f g t) x).det := by
    have hstep : ∀ i : Fin n, (∑ j, cofSum (jac (linPath f g t) x) i j *
          (fderiv ℝ φ (linPath f g t x)) (fderiv ℝ (linPath f g t) x (Pi.single j 1)))
        = (fderiv ℝ φ (linPath f g t x)) (Pi.single i 1) * (jac (linPath f g t) x).det :=
      fun i => sum_cofSum_mul_apply_col _ _ _
    rw [Finset.sum_congr rfl fun i _ => by rw [hstep i]]
    rw [clm_apply_eq_sum (F := ℝ) (fderiv ℝ φ (linPath f g t x)) (g x - f x), Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [smul_eq_mul]
    ring
  rw [hsplit, hcontract, homDeriv]

end GaloisForLFunctions.HTGeometry.PoincareHopf
