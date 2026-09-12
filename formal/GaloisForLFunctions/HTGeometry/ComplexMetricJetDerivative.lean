import GaloisForLFunctions.HTGeometry.ComplexMetricFieldBianchi
import GaloisForLFunctions.HTGeometry.CoordinateEinsteinQuadraticSpatialDerivative

set_option autoImplicit false
namespace GaloisForLFunctions.HTGeometry.ComplexMetricField
open ScalarTwoJet ComplexCoordinateMetricTwoJet Filter Topology
noncomputable section
variable {d : ℕ}

/-- Actual real coordinate line through the given field point. -/
def coordinateLine (x : Fin d → ℝ) (k : Fin d) (t : ℝ) : Fin d → ℝ :=
  x+t • Pi.single k 1

/-- Normed coordinates of the original complete field two-jet. -/
def jetSpace (g : Field d) (x : Fin d → ℝ) : ComplexMetricTwoJetSpace d :=
  toSpace (twoJet g x)

/-- Actual directional derivative in every slot of the original complete two-jet.
All third spatial derivatives retain their original order. -/
def jetSpacePartial (g : Field d) (x : Fin d → ℝ) (k : Fin d) :
    ComplexMetricTwoJetSpace d :=
  (fun i j => coordDeriv k (fun y => g y i j) x,
   fun a i j => coordDeriv k (coordDeriv a (fun y => g y i j)) x,
   fun a b i j => coordDeriv k (coordDeriv a (coordDeriv b (fun y => g y i j))) x)

theorem coordinateLine_hasDerivAt (x : Fin d → ℝ) (k : Fin d) :
    HasDerivAt (coordinateLine x k) (Pi.single k 1) 0 := by
  convert! (((hasDerivAt_id (0 : ℝ)).smul_const (Pi.single k (1 : ℝ))).const_add x) using 1
  simp

/-- Restriction to the coordinate line yields the actual coordinate derivative. -/
theorem field_coordinateLine_hasDerivAt {f : (Fin d → ℝ) → ℂ} {x : Fin d → ℝ}
    (hf : DifferentiableAt ℝ f x) (k : Fin d) :
    HasDerivAt (fun t => f (coordinateLine x k t)) (coordDeriv k f x) 0 := by
  have hF : HasFDerivAt f (fderiv ℝ f x) (coordinateLine x k 0) := by
    simpa [coordinateLine] using hf.hasFDerivAt
  exact hF.comp_hasDerivAt 0 (coordinateLine_hasDerivAt x k)

/-- A C3 actual metric produces the derivative of its complete two-jet.
There is no independent jet-realization or derivative-array premise. -/
theorem jetSpace_coordinateLine_hasDerivAt (g : Field d) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x) (k : Fin d) :
    HasDerivAt (fun t => jetSpace g (coordinateLine x k t)) (jetSpacePartial g x k) 0 := by
  have h0 (i j : Fin d) := field_coordinateLine_hasDerivAt
    ((hg i j).differentiableAt (by norm_num)) k
  have hc1 (a i j : Fin d) : ContDiffAt ℝ 2 (coordDeriv a (fun y => g y i j)) x :=
    coordDeriv_contDiffAt (hg i j) (by norm_num) a
  have h1 (a i j : Fin d) := field_coordinateLine_hasDerivAt
    ((hc1 a i j).differentiableAt (by norm_num)) k
  have hc2 (a b i j : Fin d) :
      ContDiffAt ℝ 1 (coordDeriv a (coordDeriv b (fun y => g y i j))) x :=
    coordDeriv_contDiffAt (hc1 b i j) (by norm_num) a
  have h2 (a b i j : Fin d) := field_coordinateLine_hasDerivAt
    ((hc2 a b i j).differentiableAt (by norm_num)) k
  have H0 := hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => h0 i j
  have H1 := hasDerivAt_pi.mpr fun a => hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => h1 a i j
  have H2 := hasDerivAt_pi.mpr fun a => hasDerivAt_pi.mpr fun b =>
    hasDerivAt_pi.mpr fun i => hasDerivAt_pi.mpr fun j => h2 a b i j
  exact H0.prodMk (H1.prodMk H2)

/-- C3 field regularity produces differentiability of the full jet map. -/
theorem jetSpace_differentiableAt (g : Field d) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x) :
    DifferentiableAt ℝ (jetSpace g) x := by
  have h0 (i j : Fin d) := (hg i j).differentiableAt (by norm_num)
  have h1 (a i j : Fin d) :=
    (coordDeriv_contDiffAt (m := 2) (hg i j) (by norm_num) a).differentiableAt (by norm_num)
  have h2 (a b i j : Fin d) :=
    (coordDeriv_contDiffAt (m := 1)
      (coordDeriv_contDiffAt (m := 2) (hg i j) (by norm_num) b) (by norm_num) a).differentiableAt
        (by norm_num)
  have H0 := differentiableAt_pi.mpr fun i => differentiableAt_pi.mpr fun j => h0 i j
  have H1 := differentiableAt_pi.mpr fun a => differentiableAt_pi.mpr fun i =>
    differentiableAt_pi.mpr fun j => h1 a i j
  have H2 := differentiableAt_pi.mpr fun a => differentiableAt_pi.mpr fun b =>
    differentiableAt_pi.mpr fun i => differentiableAt_pi.mpr fun j => h2 a b i j
  exact H0.prodMk (H1.prodMk H2)

/-- The original full Einstein tensor is differentiable on the actual field. -/
theorem einsteinField_differentiableAt (g : Field d) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x) (hdet : (g x).det ≠ 0) (i j : Fin d) :
    DifferentiableAt ℝ (fun y => (twoJet g y).einstein i j) x := by
  have hF := (contDiffAt_einsteinComponent (n := 1) (jetSpace g x) hdet i j).differentiableAt
    (by norm_num)
  have hFr := hF.restrictScalars ℝ
  convert! hFr.comp x (jetSpace_differentiableAt g x hg) using 1

/-- Spatial differentiation of the original Einstein tensor uses the genuine derivative
of the complete actual field jet. -/
theorem einsteinField_coordDeriv (g : Field d) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x) (hdet : (g x).det ≠ 0) (k i j : Fin d) :
    coordDeriv k (fun y => (twoJet g y).einstein i j) x =
      fderiv ℂ (einsteinComponent i j) (jetSpace g x) (jetSpacePartial g x k) := by
  have hd : Matrix.det (jetSpace g (coordinateLine x k 0)).1 ≠ 0 := by
    simpa [jetSpace,toSpace,twoJet,coordinateLine] using hdet
  have hF := ((contDiffAt_einsteinComponent (n := 1)
    (jetSpace g (coordinateLine x k 0)) hd i j).differentiableAt (by norm_num)).hasFDerivAt
  have hFr := HasFDerivAt.restrictScalars (𝕜' := ℂ) (E := ComplexMetricTwoJetSpace d) (F := ℂ) ℝ hF
  have hE := hFr.comp_hasDerivAt 0 (jetSpace_coordinateLine_hasDerivAt g x hg k)
  have hE' : HasDerivAt (fun t => (twoJet g (coordinateLine x k t)).einstein i j)
      (fderiv ℂ (einsteinComponent i j) (jetSpace g x) (jetSpacePartial g x k)) 0 := by
    convert! hE using 1
    simp [coordinateLine]
  exact (field_coordinateLine_hasDerivAt (einsteinField_differentiableAt g x hg hdet i j) k).unique hE'

/-- Actual metric-jet extraction commutes with an affine field variation. -/
theorem jetSpace_add_smul (g h : Field d) (x : Fin d → ℝ) (e : ℂ)
    (hg : ∀ i j, ContDiffAt ℝ 2 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 2 (fun y => h y i j) x) :
    jetSpace (fun y => g y+e • h y) x = jetSpace g x+e • jetSpace h x := by
  have hs (i j : Fin d) :
      ofField (fun y => g y i j+e*h y i j) x =
        ScalarTwoJet.add (ofField (fun y => g y i j) x)
          (ScalarTwoJet.mul (constant e) (ofField (fun y => h y i j) x)) := by
    rw [ofField_add (hg i j) (contDiffAt_const.mul (hh i j)),
      ofField_mul contDiffAt_const (hh i j),ofField_constant]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · funext a i j
      change (ofField (fun y => g y i j+e*h y i j) x).first a = _
      rw [hs]
      simp [ScalarTwoJet.add,ScalarTwoJet.mul,constant,jetSpace,toSpace,twoJet,ofField]
    · funext a b i j
      change (ofField (fun y => g y i j+e*h y i j) x).second a b = _
      rw [hs]
      simp [ScalarTwoJet.add,ScalarTwoJet.mul,constant,jetSpace,toSpace,twoJet,ofField]

/-- The genuine spatial derivative of the complete jet respects affine field variation. -/
theorem jetSpacePartial_add_smul (g h : Field d) (x : Fin d → ℝ) (e : ℂ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 3 (fun y => h y i j) x) (k : Fin d) :
    jetSpacePartial (fun y => g y+e • h y) x k = jetSpacePartial g x k+e • jetSpacePartial h x k := by
  have hgn : ∀ᶠ y in 𝓝 x, ∀ i j, ContDiffAt ℝ 3 (fun w => g w i j) y :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
      (hg i j).eventually (by norm_num)
  have hhn : ∀ᶠ y in 𝓝 x, ∀ i j, ContDiffAt ℝ 3 (fun w => h w i j) y :=
    Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr fun j =>
      (hh i j).eventually (by norm_num)
  have hline : Tendsto (coordinateLine x k) (𝓝 0) (𝓝 x) := by
    simpa [coordinateLine] using (coordinateLine_hasDerivAt x k).continuousAt.tendsto
  have he : (fun t => jetSpace (fun y => g y+e • h y) (coordinateLine x k t)) =ᶠ[𝓝 0]
      fun t => jetSpace g (coordinateLine x k t)+e • jetSpace h (coordinateLine x k t) := by
    filter_upwards [hline hgn,hline hhn] with t hgt hht
    exact jetSpace_add_smul g h (coordinateLine x k t) e
      (fun i j => (hgt i j).of_le (by norm_num)) (fun i j => (hht i j).of_le (by norm_num))
  have hL := jetSpace_coordinateLine_hasDerivAt (fun y => g y+e • h y) x
    (fun i j => (hg i j).add (contDiffAt_const.mul (hh i j))) k
  have hR := (jetSpace_coordinateLine_hasDerivAt g x hg k).add
    ((jetSpace_coordinateLine_hasDerivAt h x hh k).const_smul e)
  exact (hL.congr_of_eventuallyEq he.symm).unique hR

/-- The original quadratic Einstein coefficient differentiated in an actual spatial direction. -/
theorem hessian_coordinateLine_hasDerivAt (g h : Field d) (x : Fin d → ℝ)
    (hg : ∀ i j, ContDiffAt ℝ 3 (fun y => g y i j) x)
    (hh : ∀ i j, ContDiffAt ℝ 3 (fun y => h y i j) x)
    (hdet : (g x).det ≠ 0) (k i j : Fin d) :
    HasDerivAt (fun t => secondVariation (jetSpace g (coordinateLine x k t)) i j
      (jetSpace h (coordinateLine x k t)) (jetSpace h (coordinateLine x k t)))
      (thirdVariation (jetSpace g x) i j (jetSpace h x) (jetSpace h x) (jetSpacePartial g x k)+
        2*secondVariation (jetSpace g x) i j (jetSpace h x) (jetSpacePartial h x k)) 0 := by
  have hG := jetSpace_coordinateLine_hasDerivAt g x hg k
  have hH := jetSpace_coordinateLine_hasDerivAt h x hh k
  have hd : Matrix.det (jetSpace g (coordinateLine x k 0)).1 ≠ 0 := by
    simpa [jetSpace,toSpace,twoJet,coordinateLine] using hdet
  have he := secondVariation_hasDerivAt_real_symmetric hG hH hd i j
  simpa only [coordinateLine,zero_smul,add_zero] using he

end
end GaloisForLFunctions.HTGeometry.ComplexMetricField
