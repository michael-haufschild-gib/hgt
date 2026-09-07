import GaloisForLFunctions.HTGeometry.ComplexCoordinateConnectionBianchi
import GaloisForLFunctions.HTGeometry.CoordinateCurvatureTwoJet

set_option autoImplicit false

/-!
# Differential Bianchi identity of an actual complex metric field

The connection comes from the complete actual metric jet. Local C3 regularity
and nondegeneracy imply C2 regularity of that connection. Its curvature agrees
with the literal metric-jet curvature, and the full differential Bianchi identity
retains the connection action on every tensor index.
-/

namespace GaloisForLFunctions.HTGeometry.ComplexMetricField
open ScalarTwoJet Filter Topology
open scoped ContDiff
noncomputable section
variable {d : ℕ}

/-- Complex metric coefficients on real coordinates. -/
abbrev Field (d : ℕ) := (Fin d → ℝ) → Matrix (Fin d) (Fin d) ℂ

/-- Complete actual spatial two-jet in arbitrary dimension. -/
def twoJet (g : Field d) (x : Fin d → ℝ) : CoordinateMetricTwoJet d ℂ where
  metric := g x
  first k i j := coordDeriv k (fun y => g y i j) x
  second k l i j := coordDeriv k (coordDeriv l (fun y => g y i j)) x

/-- The metric-derived connection with its connection-matrix index first. -/
def connection (g : Field d) : ComplexCoordinateConnection.Field d d :=
  fun x k u v => (twoJet g x).christoffel u k v

private theorem det_smooth {m : ℕ∞ω} (g : Field d) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ m (fun y => g y i j) x) :
    ContDiffAt ℝ m (fun y => (g y).det) x := by
  have he : (fun y => (g y).det) = fun y =>
      ∑ σ : Equiv.Perm (Fin d), (Equiv.Perm.sign σ : ℂ) * ∏ i, g y (σ i) i := by
    funext y
    exact Matrix.det_apply' (g y)
  rw [he]
  exact ContDiffAt.sum fun σ _ => contDiffAt_const.mul (contDiffAt_prod fun i _ => hg (σ i) i)

private theorem adjugate_smooth {m : ℕ∞ω} (g : Field d) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ m (fun y => g y i j) x) (i j : Fin d) :
    ContDiffAt ℝ m (fun y => (g y).adjugate i j) x := by
  have he : (fun y => (g y).adjugate i j) = fun y => ((g y).updateRow j (Pi.single i 1)).det := by
    funext y
    exact Matrix.adjugate_apply (g y) i j
  rw [he]
  apply det_smooth
  intro a b
  by_cases ha : a = j
  · simpa [Matrix.updateRow_apply, ha] using
      (contDiffAt_const : ContDiffAt ℝ m (fun _ : Fin d → ℝ => (Pi.single i (1 : ℂ) : Fin d → ℂ) b) x)
  · simpa [Matrix.updateRow_apply, ha] using hg a b

private theorem inverse_smooth {m : ℕ∞ω} (g : Field d) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ m (fun y => g y i j) x) (hdet : (g x).det ≠ 0) (i j : Fin d) :
    ContDiffAt ℝ m (fun y => (g y)⁻¹ i j) x := by
  have he : (fun y => (g y)⁻¹ i j) = fun y => ((g y).det)⁻¹ * (g y).adjugate i j := by
    funext y
    rw [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  rw [he]
  exact ((det_smooth g x hg).inv hdet).mul (adjugate_smooth g x hg i j)

/-- The actual metric connection has the regularity required by differential Bianchi. -/
theorem connection_contDiffAt (g : Field d) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x) (hdet : (g x).det ≠ 0)
    (k u v : Fin d) : ContDiffAt ℝ 2 (fun y => connection g y k u v) x := by
  have hg2 (i j : Fin d) := (hg i j).of_le (show (2 : ℕ∞ω) ≤ 3 by norm_num)
  have hf (a i j : Fin d) := coordDeriv_contDiffAt (m := 2) (hg i j) (by norm_num) a
  dsimp only [connection, CoordinateMetricTwoJet.christoffel, twoJet]
  apply contDiffAt_const.mul
  apply ContDiffAt.sum
  intro m _
  exact (inverse_smooth g x hg2 hdet u m).mul (((hf k m v).add (hf v m k)).sub (hf m k v))

/-- Actual symmetry of the metric makes its coordinate connection torsion-free. -/
theorem connection_torsion_free (g : Field d) (x : Fin d → ℝ)
    (hSym : ∀ y i j, g y i j = g y j i) (k i u : Fin d) :
    connection g x k u i = connection g x i u k := by
  have hs (a b c : Fin d) : coordDeriv a (fun y => g y b c) x = coordDeriv a (fun y => g y c b) x :=
    congrArg (fun f => coordDeriv a f x) (funext fun y => hSym y b c)
  dsimp only [connection, CoordinateMetricTwoJet.christoffel, twoJet]
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  rw [hs m k i]
  ring

/-- Full differential Bianchi identity of the actual metric-derived curvature. -/
theorem bianchi (g : Field d) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x) (hdet : (g x).det ≠ 0)
    (hSym : ∀ y i j, g y i j = g y j i) (k i j u v : Fin d) :
    ComplexCoordinateConnection.tensorPartial (connection g) x k i j u v +
      ComplexCoordinateConnection.tensorPartial (connection g) x i j k u v +
      ComplexCoordinateConnection.tensorPartial (connection g) x j k i u v = 0 :=
  ComplexCoordinateConnection.tensor_bianchi (connection g) x
    (connection_contDiffAt g x hg hdet) (connection_torsion_free g x hSym) k i j u v

/-- Differentiating the local inverse identity yields the exact inverse-metric derivative. -/
theorem inverse_partial (g : Field d) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x) (hdet : (g x).det ≠ 0) (k : Fin d) :
    ComplexCoordinateConnection.matrixPartial (fun y => (g y)⁻¹) x k = (twoJet g x).inverseDerivative k := by
  let Q := ComplexCoordinateConnection.matrixPartial (fun y => (g y)⁻¹) x k
  let H := (twoJet g x).first k
  let G := (g x)⁻¹
  have hd (i j : Fin d) := (hg i j).differentiableAt (by norm_num)
  have hi (i j : Fin d) := (inverse_smooth g x hg hdet i j).differentiableAt (by norm_num)
  have hn := (det_smooth g x hg).continuousAt.eventually_ne hdet
  have hprod : Q * g x + G * H = 0 := by
    ext i j
    have he : (fun y => ∑ m, (g y)⁻¹ i m * g y m j) =ᶠ[𝓝 x]
        (fun _ => (1 : Matrix (Fin d) (Fin d) ℂ) i j) := by
      filter_upwards [hn] with y hy
      exact congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M i j)
        (Matrix.nonsing_inv_mul (g y) (isUnit_iff_ne_zero.mpr hy))
    have hz : coordDeriv k (fun y => ∑ m, (g y)⁻¹ i m * g y m j) x = 0 := by
      unfold coordDeriv
      rw [he.fderiv_eq]
      simp
    rw [coordDeriv_sum (s := Finset.univ) (F := fun m y => (g y)⁻¹ i m * g y m j) (fun m _ => (hi i m).mul (hd m j))] at hz
    simp_rw [coordDeriv_mul (hi i _) (hd _ j)] at hz
    simpa [Q, H, G, ComplexCoordinateConnection.matrixPartial, twoJet,
      Matrix.add_apply, Matrix.mul_apply, Finset.sum_add_distrib] using hz
  have hinv : g x * G = 1 := Matrix.mul_nonsing_inv (g x) (isUnit_iff_ne_zero.mpr hdet)
  change Q = -(G * H * G)
  have hr := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M * G) hprod
  rw [Matrix.add_mul, Matrix.mul_assoc Q, hinv, Matrix.mul_one, Matrix.zero_mul] at hr
  exact eq_neg_of_add_eq_zero_left hr

/-- The actual connection derivative equals the complete metric-jet curvature formula. -/
theorem connection_partial (g : Field d) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x) (hdet : (g x).det ≠ 0)
    (k u i j : Fin d) :
    coordDeriv k (fun y => connection g y i u j) x = (twoJet g x).christoffelDerivative k u i j := by
  have hi (a b : Fin d) := (inverse_smooth g x hg hdet a b).differentiableAt (by norm_num)
  have hf (a b c : Fin d) : DifferentiableAt ℝ (coordDeriv a (fun y => g y b c)) x :=
    (coordDeriv_hasFDerivAt ((hg b c).of_le (show (2 : ℕ∞ω) ≤ 3 by norm_num)) a).differentiableAt
  have hlin (m : Fin d) : DifferentiableAt ℝ
      (fun y => coordDeriv i (fun z => g z m j) y + coordDeriv j (fun z => g z m i) y -
        coordDeriv m (fun z => g z i j) y) x := ((hf i m j).add (hf j m i)).sub (hf m i j)
  have hterm (m : Fin d) : DifferentiableAt ℝ
      (fun y => (g y)⁻¹ u m * (coordDeriv i (fun z => g z m j) y +
        coordDeriv j (fun z => g z m i) y - coordDeriv m (fun z => g z i j) y)) x :=
    (hi u m).mul (hlin m)
  dsimp only [connection, CoordinateMetricTwoJet.christoffel, twoJet]
  rw [coordDeriv_mul (differentiableAt_const (1 / 2 : ℂ)) (DifferentiableAt.fun_sum (u := Finset.univ) (fun m _ => hterm m))]
  have hc : coordDeriv k (fun _ : Fin d → ℝ => (1 / 2 : ℂ)) x = 0 := by simp [coordDeriv]
  rw [hc, zero_mul, zero_add]
  change (1 / 2 : ℂ) * coordDeriv k (fun y => ∑ m, (g y)⁻¹ u m *
    (coordDeriv i (fun z => g z m j) y + coordDeriv j (fun z => g z m i) y -
      coordDeriv m (fun z => g z i j) y)) x = _
  rw [coordDeriv_sum (s := Finset.univ) (fun m _ => hterm m)]
  unfold CoordinateMetricTwoJet.christoffelDerivative
  congr 1
  apply Finset.sum_congr rfl
  intro m _
  have hadd : DifferentiableAt ℝ (fun y => coordDeriv i (fun z => g z m j) y +
      coordDeriv j (fun z => g z m i) y) x := (hf i m j).add (hf j m i)
  rw [coordDeriv_mul (hi u m) (hlin m), coordDeriv_sub hadd (hf m i j),
    coordDeriv_add (hf i m j) (hf j m i)]
  have hG := congrArg (fun M : Matrix (Fin d) (Fin d) ℂ => M u m) (inverse_partial g x hg hdet k)
  rw [show coordDeriv k (fun y => (g y)⁻¹ u m) x = (twoJet g x).inverseDerivative k u m from hG]
  rfl

/-- Literal metric-jet Riemann curvature is the curvature of the actual metric connection. -/
theorem curvature_eq_twoJet (g : Field d) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x) (hdet : (g x).det ≠ 0)
    (u v i j : Fin d) :
    ComplexCoordinateConnection.curvature (connection g) x i j u v = (twoJet g x).riemann u v i j := by
  simp only [ComplexCoordinateConnection.curvature, ConnectionBianchi.curvature,
    ComplexCoordinateConnection.first, Matrix.add_apply, Matrix.sub_apply]
  rw [connection_partial g x hg hdet, connection_partial g x hg hdet]
  simp only [CoordinateMetricTwoJet.riemann, connection, Matrix.mul_apply, Finset.sum_sub_distrib]
  ring

end
end GaloisForLFunctions.HTGeometry.ComplexMetricField
