import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSquareSourceDifferential

/-! Actual squared-source covector calculus, divergence and forced rough Laplacian. -/

open Set Filter Topology
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open scoped ContDiff
namespace RHTower.D4BMModularCore
open D4BMGlobalAngularResponse D4BMAngularSeries D4BMHorizon
noncomputable section

private theorem covariant_germ {V W : Covector} {z : Point}
    (h : ∀ k, V k =ᶠ[𝓝 z] W k) (i j : Fin 2) :
    covariant V i j =ᶠ[𝓝 z] covariant W i j := by
  have hv : ∀ᶠ w in 𝓝 z, ∀ k, V k w = W k w := Filter.eventually_all.mpr h
  filter_upwards [hv,(h j).fderiv (𝕜 := ℝ)] with w hw hd
  simp only [covariant,coordDeriv,hd]
  simp_rw [hw]

/-- Equality of actual covector germs preserves the complete rough Laplacian. -/
theorem roughLaplacian_germ {V W : Covector} {z : Point}
    (h : ∀ k, V k =ᶠ[𝓝 z] W k) (k : Fin 2) :
    roughLaplacian V k z = roughLaplacian W k z := by
  have hv (i j : Fin 2) := (covariant_germ h i j).eq_of_nhds
  have hd (i j : Fin 2) : coordDeriv i (covariant V j k) z = coordDeriv i (covariant W j k) z :=
    congrArg (fun a => a (Pi.single i 1)) ((covariant_germ h j k).fderiv_eq (𝕜 := ℝ))
  simp only [roughLaplacian,hd,hv]

/-- Equality of actual covector germs preserves the covariant divergence. -/
theorem divergence_germ {V W : Covector} {z : Point}
    (h : ∀ k, V k =ᶠ[𝓝 z] W k) : divergence V z = divergence W z := by
  have hv (i j : Fin 2) := (covariant_germ h i j).eq_of_nhds
  simp only [divergence,hv]

private theorem square_germ (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) (k : Fin 2) :
    fullSquareCovector q k =ᶠ[𝓝 z] coexact (fullSquarePotential q) k := by
  filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
  exact (fullSquarePotential_coexact q w hw k).symm

/-- Every finite jet of the actual quadratic covector exists. -/
theorem fullSquareCovector_smooth (q : XiZeroCopy) (z : Point) (hz : 0 < z 1)
    (n : ℕ) (k : Fin 2) : ContDiffAt ℝ n (fullSquareCovector q k) z := by
  apply (coexact_contDiffAt (fullSquarePotential_smooth q z hz (n+1)) k).congr_of_eventuallyEq
  exact square_germ q z hz k

/-- The original squared-source covector satisfies the actual divergence constraint. -/
theorem fullSquareCovector_divergence (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    divergence (fullSquareCovector q) z = 0 := by
  rw [divergence_germ (square_germ q z hz)]
  apply coexact_divergence _ z hz
  simpa using fullSquarePotential_smooth q z hz 2

private theorem gradient_smooth (q : XiZeroCopy) (z : Point) (hz : 0 < z 1) :
    DifferentiableAt ℝ (fullGradientEnergy q) z := by
  have hs : ContDiffAt ℝ 2 (scalar (center q)) z := by
    have h := cuspLeg_contDiffAt .scalar (center q) 2 z hz
    norm_num at h
    exact h
  have hY := Complex.ofRealCLM.hasFDerivAt.comp z
    ((ContinuousLinearMap.proj 1 : Point →L[ℝ] ℝ).hasFDerivAt)
  exact (hY.differentiableAt.pow 2).mul
    (((coordDeriv_hasFDerivAt hs 0).differentiableAt.pow 2).add
      ((coordDeriv_hasFDerivAt hs 1).differentiableAt.pow 2))

/-- The original prescribed square-source Laplacian is the actual covariant operator
on the full literal J field, with all gradient-source and curvature terms retained. -/
theorem fullSquareCovector_rough_equation (q : XiZeroCopy) (branch : Bool)
    (z : Point) (hz : 0 < z 1) (k : Fin 2) :
    roughLaplacian (fullSquareCovector q) k z+fullSquareCovector q k z =
      2*(physicalRate q branch+1)*(physicalRate q branch+2)*fullSquareCovector q k z+
        2*fullGradientCovector q branch k z := by
  let P := fullSquarePotential q
  let E := 2*(physicalRate q branch+1)*(physicalRate q branch+2)
  have hP : ContDiffAt ℝ 3 P z := by simpa [P] using fullSquarePotential_smooth q z hz 3
  have he : scalarLaplacian P =ᶠ[𝓝 z] (fun w => E*P w+fullGradientEnergy q w) := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
    exact fullSquarePotential_laplacian q branch w hw
  have hd := (((hP.differentiableAt (by norm_num)).hasFDerivAt.const_mul E).add
    (gradient_smooth q z hz).hasFDerivAt).congr_of_eventuallyEq he
  have hi (j : Fin 2) : coordDeriv j (scalarLaplacian P) z =
      E*coordDeriv j P z+coordDeriv j (fullGradientEnergy q) z := by
    rw [coordDeriv,hd.fderiv]
    simp [coordDeriv,smul_eq_mul]
  have hc : coexact (scalarLaplacian P) k z = E*coexact P k z+coexact (fullGradientEnergy q) k z := by
    fin_cases k <;> simp [coexact,hi]
    ring
  rw [roughLaplacian_germ (square_germ q z hz),coexact_roughLaplacian _ z hz hP,
    ← fullSquarePotential_coexact q z hz k,sub_add_cancel,hc,
    fullSquarePotential_coexact q z hz k,fullGradientEnergy_coexact q branch z hz k]

end
end RHTower.D4BMModularCore
