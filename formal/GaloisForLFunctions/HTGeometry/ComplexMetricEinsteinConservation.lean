import GaloisForLFunctions.HTGeometry.ComplexMetricContractedDerivative

set_option autoImplicit false
namespace GaloisForLFunctions.HTGeometry.ComplexCoordinateConnection
open ScalarTwoJet CurvatureContraction
noncomputable section
variable {d : ℕ}

/-- Covariant derivative of a tensor plus a scalar multiple of another tensor. -/
theorem covariantTwo_add_smul (A : Field d d)
    (S G : (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℂ) (φ : (Fin d → ℝ) → ℂ)
    (x : Fin d → ℝ) (hS : ∀ u v, DifferentiableAt ℝ (fun y => S y u v) x)
    (hG : ∀ u v, DifferentiableAt ℝ (fun y => G y u v) x)
    (hφ : DifferentiableAt ℝ φ x) (k : Fin d) :
    covariantTwo A (fun y => S y+φ y • G y) x k =
      covariantTwo A S x k+coordDeriv k φ x • G x+φ x • covariantTwo A G x k := by
  have hd : matrixPartial (fun y => φ y • G y) x k =
      coordDeriv k φ x • G x+φ x • matrixPartial G x k := by
    ext u v
    exact coordDeriv_mul hφ (hG u v) k
  unfold covariantTwo
  rw [matrixPartial_add S (fun y => φ y • G y) x hS
    (fun u v => hφ.mul (hG u v)) k,hd]
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul,
    smul_sub]
  abel

/-- The inverse metric contracts a differentiated scalar-metric term exactly. -/
theorem inverse_contract_metric (G : Matrix (Fin d) (Fin d) ℂ)
    (hdet : G.det ≠ 0) (hs : G.transpose = G) (a : Fin d → ℂ) (j : Fin d) :
    (∑ k, ∑ b, G⁻¹ b k*(a k*G b j)) = a j := by
  have hi : (G⁻¹).transpose = G⁻¹ := by rw [Matrix.transpose_nonsing_inv,hs]
  have he (k : Fin d) : (∑ b, G⁻¹ b k*(a k*G b j)) =
      a k*(1 : Matrix (Fin d) (Fin d) ℂ) k j := by
    calc
      _ = a k*(G⁻¹.transpose*G) k j := by
        simp only [Matrix.mul_apply,Matrix.transpose_apply,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro b _
        ring
      _ = _ := by rw [hi,Matrix.nonsing_inv_mul G (isUnit_iff_ne_zero.mpr hdet)]
  simp_rw [he]
  simp [Matrix.one_apply]

end
end GaloisForLFunctions.HTGeometry.ComplexCoordinateConnection

namespace GaloisForLFunctions.HTGeometry.ComplexMetricField
open ScalarTwoJet ComplexCoordinateConnection CurvatureContraction Filter Topology
noncomputable section
variable {d : ℕ}

/-- Actual scalar curvature via the actual metric connection. -/
def connectionScalar (g : Field d) (x : Fin d → ℝ) : ℂ :=
  tensorPair (g x)⁻¹ (ricciField (connection g) x)

/-- Actual cosmological Einstein tensor via the metric-derived connection. -/
def connectionEinstein (g : Field d) (Λ : ℂ) : Field d :=
  fun x => ricciField (connection g) x+(Λ-(1/2 : ℂ)*connectionScalar g x) • g x

/-- Literal covariant divergence, including the original two index actions. -/
def tensorDivergence (g S : Field d) (x : Fin d → ℝ) (j : Fin d) : ℂ :=
  ∑ k, ∑ b, (g x)⁻¹ b k*covariantTwo (connection g) S x k b j

/-- Contracted differential Bianchi gives conservation of the actual cosmological
Einstein tensor. No divergence or conservation premise is supplied. -/
theorem connectionEinstein_divergence (g : Field d) (Λ : ℂ) (x : Fin d → ℝ)
    (hg : ∀ u v, ContDiffAt ℝ 3 (fun y => g y u v) x)
    (hdet : (g x).det ≠ 0) (hs : ∀ y u v, g y u v = g y v u) (j : Fin d) :
    tensorDivergence g (connectionEinstein g Λ) x j = 0 := by
  have hA := connection_contDiffAt g x hg hdet
  have hG (u v : Fin d) := (hg u v).differentiableAt (by norm_num)
  have hR (u v : Fin d) : DifferentiableAt ℝ (fun y => ricciField (connection g) y u v) x :=
    DifferentiableAt.fun_sum (fun a _ => curvature_differentiableAt (connection g) x hA a v a u)
  have hH := inverse_differentiableAt g x hG hdet
  have hSc : DifferentiableAt ℝ (connectionScalar g) x := by
    unfold connectionScalar tensorPair
    exact DifferentiableAt.fun_sum (fun u _ => DifferentiableAt.fun_sum (fun v _ => (hH u v).mul (hR u v)))
  let φ : (Fin d → ℝ) → ℂ := fun y => Λ-(1/2 : ℂ)*connectionScalar g y
  have hφ : DifferentiableAt ℝ φ x := (differentiableAt_const Λ).sub ((differentiableAt_const (1/2 : ℂ)).mul hSc)
  have hφd (k : Fin d) : coordDeriv k φ x = -(1/2 : ℂ)*coordDeriv k (connectionScalar g) x := by
    unfold φ
    rw [coordDeriv_sub (f := fun _ => Λ) (g := fun y => (1/2 : ℂ)*connectionScalar g y)
        (differentiableAt_const Λ) ((differentiableAt_const (1/2 : ℂ)).mul hSc),
      coordDeriv_mul (f := fun _ => (1/2 : ℂ)) (g := connectionScalar g)
        (differentiableAt_const (1/2 : ℂ)) hSc]
    simp [coordDeriv]
  have hCovG (k : Fin d) : covariantTwo (connection g) g x k = 0 := by
    unfold covariantTwo
    rw [metric_compatibility g x hdet hs k]
    abel
  have hE (k : Fin d) : covariantTwo (connection g) (connectionEinstein g Λ) x k =
      covariantTwo (connection g) (ricciField (connection g)) x k+
        coordDeriv k φ x • g x := by
    change covariantTwo (connection g) (fun y => ricciField (connection g) y+φ y • g y) x k = _
    rw [covariantTwo_add_smul _ _ _ φ x hR hG hφ k,hCovG]
    simp
  have hd : tensorDivergence g (connectionEinstein g Λ) x j =
      divergenceTrace (g x)⁻¹ (tensorPartial (connection g) x) j+coordDeriv j φ x := by
    unfold tensorDivergence divergenceTrace
    simp_rw [hE,Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,mul_add,Finset.sum_add_distrib,
      ricciTrace_tensorPartial (connection g) x hA]
    rw [inverse_contract_metric (g x) hdet (by ext u v; exact hs x v u)]
  rw [hd,hφd]
  have hb := bianchi_double_contracted g x hg hdet hs j
  rw [scalarTrace_eq_partial g x hg hdet hs j] at hb
  change 2*divergenceTrace (g x)⁻¹ (tensorPartial (connection g) x) j =
    coordDeriv j (connectionScalar g) x at hb
  linear_combination (1/2 : ℂ)*hb


/-- The actual connection Ricci tensor equals the original full metric-jet contraction. -/
theorem ricciField_eq_twoJet (g : Field d) (x : Fin d → ℝ)
    (hg : ∀ u v, ContDiffAt ℝ 3 (fun y => g y u v) x) (hdet : (g x).det ≠ 0) :
    ricciField (connection g) x = (twoJet g x).ricci := by
  ext b j
  unfold ricciField CoordinateMetricTwoJet.ricci
  apply Finset.sum_congr rfl
  intro u _
  exact curvature_eq_twoJet g x hg hdet u b u j

/-- The scalar contraction is the scalar curvature of the original complete two-jet. -/
theorem connectionScalar_eq_twoJet (g : Field d) (x : Fin d → ℝ)
    (hg : ∀ u v, ContDiffAt ℝ 3 (fun y => g y u v) x) (hdet : (g x).det ≠ 0) :
    connectionScalar g x = (twoJet g x).scalar := by
  unfold connectionScalar
  rw [ricciField_eq_twoJet g x hg hdet]
  rfl

/-- Original cosmological Einstein tensor, using every slot of the actual metric two-jet. -/
def literalEinstein (g : Field d) (Λ : ℂ) : Field d :=
  fun x => (twoJet g x).einstein+Λ • g x

/-- The connection construction and original full Einstein tensor agree. -/
theorem connectionEinstein_eq_literal (g : Field d) (Λ : ℂ) (x : Fin d → ℝ)
    (hg : ∀ u v, ContDiffAt ℝ 3 (fun y => g y u v) x) (hdet : (g x).det ≠ 0) :
    connectionEinstein g Λ x = literalEinstein g Λ x := by
  unfold connectionEinstein literalEinstein
  rw [ricciField_eq_twoJet g x hg hdet,connectionScalar_eq_twoJet g x hg hdet]
  ext u v
  simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,CoordinateMetricTwoJet.einstein,
    twoJet]
  ring

/-- The original cosmological Einstein tensor has zero actual covariant divergence.
The identification holds on a neighborhood, so its spatial derivatives are also the original ones. -/
theorem literalEinstein_divergence (g : Field d) (Λ : ℂ) (x : Fin d → ℝ)
    (hg : ∀ u v, ContDiffAt ℝ 3 (fun y => g y u v) x)
    (hdet : (g x).det ≠ 0) (hs : ∀ y u v, g y u v = g y v u) (j : Fin d) :
    tensorDivergence g (literalEinstein g Λ) x j = 0 := by
  have hgn : ∀ᶠ y in 𝓝 x, ∀ u v, ContDiffAt ℝ 3 (fun z => g z u v) y :=
    Filter.eventually_all.mpr fun u => Filter.eventually_all.mpr fun v =>
      (hg u v).eventually (by norm_num)
  have hc (u v : Fin d) : ContinuousAt (fun y => g y u v) x := (hg u v).continuousAt
  have hd : ContinuousAt (fun y => (g y).det) x := by
    simp only [Matrix.det_apply']
    fun_prop
  have he : literalEinstein g Λ =ᶠ[𝓝 x] connectionEinstein g Λ := by
    filter_upwards [hgn,hd.eventually_ne hdet] with y hy hdy
    exact (connectionEinstein_eq_literal g Λ y hy hdy).symm
  have hp (k : Fin d) := matrixPartial_congr he k
  have hv : literalEinstein g Λ x = connectionEinstein g Λ x := he.self_of_nhds
  have hcov (k : Fin d) : covariantTwo (connection g) (literalEinstein g Λ) x k =
      covariantTwo (connection g) (connectionEinstein g Λ) x k := by
    unfold covariantTwo
    rw [hp,hv]
  unfold tensorDivergence
  simp_rw [hcov]
  exact connectionEinstein_divergence g Λ x hg hdet hs j

end
end GaloisForLFunctions.HTGeometry.ComplexMetricField
