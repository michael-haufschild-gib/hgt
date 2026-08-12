import GaloisForLFunctions.HTGeometry.NevTruncCauchyTransform
import GaloisForLFunctions.HTGeometry.QuasiMeasureCauchy
import GaloisForLFunctions.HTGeometry.CauchyKernelWeakConvergence
import GaloisForLFunctions.HTGeometry.NevLeafApproxLimit
import GaloisForLFunctions.HTGeometry.SecondKindGlobal

/-!
# The Cauchy transform of a leaf is the Nevanlinna Möbius image of its parameter

At each finite level the quadrature measure attached to the parameter `τ` satisfies the cleared
Nevanlinna identity

`(Bₙ(z)·τ − Dₙ(z))·∫(x − z)⁻¹ dμₙ = −s₀·(Aₙ(z)·τ − Cₙ(z))`,

obtained by multiplying the divided-difference identity for the quadrature measure by the common
factor that turns the quasi-orthogonal polynomial pair into the truncated Nevanlinna entries.
The quadrature levels converge weakly to the leaf and the truncated entries converge to the entire
ones, so the identity passes to the limit:

`(B(z)·τ − D(z))·∫(x − z)⁻¹ dν_τ = −(A(z)·τ − C(z))`.

The determinant identity `AD − BC = 1` then forbids the denominator from vanishing off the real
axis, giving the Weyl-disc closed form

`∫(x − z)⁻¹ dν_τ = −(A(z)·τ − C(z))/(B(z)·τ − D(z))`.
-/

open scoped BigOperators
open MeasureTheory Filter Topology OnePoint
open scoped OnePoint

namespace HTGeometry

variable {s : ℕ → ℝ}

/-! ## The finite stage, cleared of denominators -/

/-- **The finite-stage Nevanlinna identity.**  The truncated denominator applied to the level-`n`
quadrature Cauchy transform is the truncated numerator, with no division anywhere. -/
theorem nevTrunc_cauchy_identity (h : PositiveMomentForm s) (n : ℕ) {tau : ℝ}
    (hα : nevAlpha s n tau ≠ 0) {z : ℂ} (hz : z.im ≠ 0) :
    (nevBtruncC s n z * (tau : ℂ) - nevDtruncC s n z) *
        ∫ x, ((x : ℂ) - z)⁻¹ ∂(quasiMeasure s n (nevBeta s n tau / nevAlpha s n tau))
      = -((s 0 : ℝ) : ℂ) * (nevAtruncC s n z * (tau : ℂ) - nevCtruncC s n z) := by
  have hq := quasiMeasure_cauchy_identity_of_im_ne_zero h n
    (nevBeta s n tau / nevAlpha s n tau) hz
  rw [nevTruncDenominatorC_eq_quasi h n hα z, nevTruncNumeratorC_eq_quasi h n hα z,
    aeval_quasiSecondKind]
  linear_combination (((momentInner s (monicOrtho s 0) (monicOrtho s 0) : ℝ) : ℂ) /
      ((momentInner s (monicOrtho s n) (monicOrtho s n) : ℝ) : ℂ) *
      ((nevAlpha s n tau : ℝ) : ℂ)) * hq

/-! ## Passage to the leaf -/

/-- **The Nevanlinna identity for the leaf.**  The entire Nevanlinna denominator applied to the
Cauchy transform of the leaf at parameter `τ` is the entire numerator. -/
theorem nevInf_cauchy_identity (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (tau : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    (nevBinf s z * (tau : ℂ) - nevDinf s z) *
        ∫ x, ((x : ℂ) - z)⁻¹ ∂(nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ)
      = -(nevAinf s z * (tau : ℂ) - nevCinf s z) := by
  obtain ⟨S, P, _, _, hS, hP⟩ := id h0b
  obtain ⟨φ, hφ, hlim⟩ := exists_tendsto_quasiProbMeasure_nevLeaf h h0b h0 tau
  have hNtop : Tendsto (fun i => goodLevel h tau (φ i)) atTop atTop := by
    refine tendsto_atTop_mono (fun i => ?_) tendsto_id
    show i ≤ goodLevel h tau (φ i)
    have h1 : φ i + 1 ≤ goodLevel h tau (φ i) := goodLevel_ge h tau (φ i)
    have h2 : i ≤ φ i := hφ.le_apply
    omega
  have hcauchy : Tendsto (fun i => ∫ x, ((x : ℂ) - z)⁻¹
        ∂((quasiProbMeasure h (goodLevel h tau (φ i)) (leafParam h tau (φ i)) :
          ProbabilityMeasure ℝ) : Measure ℝ)) atTop
      (𝓝 (∫ x, ((x : ℂ) - z)⁻¹ ∂(nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ))) :=
    tendsto_cauchyTransform_of_tendsto hlim hz
  have hA : Tendsto (fun i => nevAtruncC s (goodLevel h tau (φ i)) z) atTop
      (𝓝 (nevAinf s z)) := (tendsto_nevAtruncC h hS hP z).comp hNtop
  have hB : Tendsto (fun i => nevBtruncC s (goodLevel h tau (φ i)) z) atTop
      (𝓝 (nevBinf s z)) := (tendsto_nevBtruncC h hS hP z).comp hNtop
  have hC : Tendsto (fun i => nevCtruncC s (goodLevel h tau (φ i)) z) atTop
      (𝓝 (nevCinf s z)) := (tendsto_nevCtruncC h hS hP z).comp hNtop
  have hD : Tendsto (fun i => nevDtruncC s (goodLevel h tau (φ i)) z) atTop
      (𝓝 (nevDinf s z)) := (tendsto_nevDtruncC h hS hP z).comp hNtop
  have hLHS : Tendsto (fun i =>
      (nevBtruncC s (goodLevel h tau (φ i)) z * (tau : ℂ) -
          nevDtruncC s (goodLevel h tau (φ i)) z) *
        ∫ x, ((x : ℂ) - z)⁻¹
          ∂((quasiProbMeasure h (goodLevel h tau (φ i)) (leafParam h tau (φ i)) :
            ProbabilityMeasure ℝ) : Measure ℝ)) atTop
      (𝓝 ((nevBinf s z * (tau : ℂ) - nevDinf s z) *
        ∫ x, ((x : ℂ) - z)⁻¹ ∂(nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ))) :=
    ((hB.mul_const _).sub hD).mul hcauchy
  have hRHS : Tendsto (fun i =>
      -((s 0 : ℝ) : ℂ) * (nevAtruncC s (goodLevel h tau (φ i)) z * (tau : ℂ) -
        nevCtruncC s (goodLevel h tau (φ i)) z)) atTop
      (𝓝 (-((s 0 : ℝ) : ℂ) * (nevAinf s z * (tau : ℂ) - nevCinf s z))) :=
    ((hA.mul_const _).sub hC).const_mul _
  have heq : ∀ i,
      (nevBtruncC s (goodLevel h tau (φ i)) z * (tau : ℂ) -
          nevDtruncC s (goodLevel h tau (φ i)) z) *
        (∫ x, ((x : ℂ) - z)⁻¹
          ∂((quasiProbMeasure h (goodLevel h tau (φ i)) (leafParam h tau (φ i)) :
            ProbabilityMeasure ℝ) : Measure ℝ))
        = -((s 0 : ℝ) : ℂ) * (nevAtruncC s (goodLevel h tau (φ i)) z * (tau : ℂ) -
            nevCtruncC s (goodLevel h tau (φ i)) z) := by
    intro i
    have hcoe : ((quasiProbMeasure h (goodLevel h tau (φ i)) (leafParam h tau (φ i)) :
          ProbabilityMeasure ℝ) : Measure ℝ)
        = quasiMeasure s (goodLevel h tau (φ i))
            (nevBeta s (goodLevel h tau (φ i)) tau / nevAlpha s (goodLevel h tau (φ i)) tau) := by
      show quasiProb s (goodLevel h tau (φ i)) (leafParam h tau (φ i)) = _
      rw [quasiProb_eq_quasiMeasure h0]
      rfl
    rw [hcoe]
    exact nevTrunc_cauchy_identity h _ (goodLevel_nevAlpha_ne_zero h tau (φ i)) hz
  have hmain := tendsto_nhds_unique (hLHS.congr heq) hRHS
  rw [h0] at hmain
  simpa using hmain

/-! ## The denominator never vanishes off the real axis -/

/-- **The entire Nevanlinna denominator is nonzero off the real axis.**  If it vanished, the
identity for the leaf would force the numerator to vanish too, and then the determinant
`A·D − B·C` would be `0` instead of `1`. -/
theorem nevInf_denominator_ne_zero (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (tau : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    nevBinf s z * (tau : ℂ) - nevDinf s z ≠ 0 := by
  intro hden
  have hid := nevInf_cauchy_identity h h0b h0 tau hz
  rw [hden, zero_mul] at hid
  have hnum : nevAinf s z * (tau : ℂ) - nevCinf s z = 0 := by linear_combination hid
  have hdet := nevAinf_mul_nevDinf_sub_nevBinf_mul_nevCinf h z h0b
    (boundedKernel_global h h0b z)
  have hCz : nevCinf s z = nevAinf s z * (tau : ℂ) := by linear_combination -hnum
  have hDz : nevDinf s z = nevBinf s z * (tau : ℂ) := by linear_combination -hden
  rw [hCz, hDz] at hdet
  have : (0 : ℂ) = 1 := by linear_combination hdet
  exact one_ne_zero this.symm

/-- **The Weyl-disc closed form.**  The Cauchy transform of the leaf at a finite parameter is the
Möbius image of that parameter under the entire Nevanlinna matrix. -/
theorem cauchyTransform_nevLeaf_eq_moebius (h : PositiveMomentForm s) (h0b : BoundedKernel s 0)
    (h0 : s 0 = 1) (tau : ℝ) {z : ℂ} (hz : z.im ≠ 0) :
    ∫ x, ((x : ℂ) - z)⁻¹ ∂(nevLeaf h h0b h0 (tau : OnePoint ℝ) : Measure ℝ)
      = -(nevAinf s z * (tau : ℂ) - nevCinf s z) /
          (nevBinf s z * (tau : ℂ) - nevDinf s z) := by
  have hden := nevInf_denominator_ne_zero h h0b h0 tau hz
  rw [eq_div_iff hden]
  rw [mul_comm]
  exact nevInf_cauchy_identity h h0b h0 tau hz

end HTGeometry
