import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.EnergyMesh.GaussianCover
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ThermodynamicEdges.FirstExit

/-! # First scalar exit at all physical errors and the full inverse-size profile -/

open Filter MeasureTheory Set Real
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.EnergyMesh
open ThermodynamicEdges
noncomputable section

/-- All dates through the closure of the exterior gap have the exact
unwrapped arc length. This determines the first exit whenever that gap
still dominates at the proposed exit. -/
private theorem exit_from_cover (ω : PathPauliDisorder) (n : ℕ) {q ε : ℝ} (hq : 0 ≤ q)
    (hε : ε∈Ioo (0:ℝ) 2)
    (hc : let H := shellOperator (pathPauliDisorderShell ω n)
      ∀ y ∈ Icc (lower H) (upper H), ∃ i, |H.2.isHermitian.eigenvalues i-y| ≤ q)
    (hW : 0<physicalWidth ω n)
    (hgap : 4*arcsin (ε/2)*(1+2*(q/physicalWidth ω n))<2*π) :
    emptyExit ω n ε=4*arcsin (ε/2)/physicalWidth ω n := by
  let H := shellOperator (pathPauliDisorderShell ω n)
  let W := physicalWidth ω n
  let θ := 4*arcsin (ε/2)
  have hp : 0<W+2*q := add_pos_of_pos_of_nonneg hW (mul_nonneg zero_le_two hq)
  have ht : θ/W<2*π/(W+2*q) := by
    apply (div_lt_div_iff₀ hW hp).mpr
    calc θ*(W+2*q) = θ*(1+2*(q/W))*W := by field_simp [show W ≠ 0 from hW.ne']
         _ < _ := mul_lt_mul_of_pos_right hgap hW
  apply first_failure (div_nonneg (mul_nonneg (by norm_num) (arcsin_pos.mpr (half_pos hε.1)).le) hW.le) ht
  intro t htime
  have h := physical_arc_bounds H hc htime.1
  have hsep : t*W ≤ 2*π-2*t*q := by linarith only [(le_div_iff₀ hp).mp htime.2]
  change min (t*W) _ ≤ orbitSpectralEnclosingArcLength H t ∧ orbitSpectralEnclosingArcLength H t ≤ min (t*W) _ at h
  rw [min_eq_left hsep] at h
  have he := le_antisymm (h.2.trans (min_le_left ..)) h.1
  exact (zeroGateApproximation_iff_enclosingArc H t ⟨ε,hε.1.le,hε.2.le⟩).trans (by
    rw [he]; exact (le_div_iff₀ hW).symm)

/-- The same frozen chain has the deterministic inverse-size exit date
at every error below two. The scalar distance at scaled time x follows
the limiting chord until it reaches two. -/
theorem gaussian_full_ascent :
    ∃ w : ℝ, 0<w ∧ ∀ᵐ ω ∂pathPauliDisorderLaw,
      let N := fun n : ℕ => ((n+2 : ℕ):ℝ)
      Tendsto (fun n => physicalWidth ω n/N n) atTop (𝓝 w) ∧
      (∀ ε∈Ioo (0:ℝ) 2, (∀ᶠ n in atTop, emptyExit ω n ε=4*arcsin (ε/2)/physicalWidth ω n) ∧
        Tendsto (fun n => N n*emptyExit ω n ε) atTop (𝓝 (4*arcsin (ε/2)/w))) ∧
      ∀ (u : ℕ→ℝ) (x : ℝ), Tendsto u atTop (𝓝 x) → (∀ᶠ n in atTop, 0 ≤ u n) →
        Tendsto (fun n => orbitCircuitDistance (shellOperator (pathPauliDisorderShell ω n)) 0 (u n/N n))
          atTop (𝓝 (2*sin (min (x*w) (2*π)/4))) := by
  obtain ⟨B,hB,hcover⟩ := gaussian_energy_cover
  obtain ⟨w,hw,_,hdensity⟩ := gaussian_energy_density
  refine ⟨w,hw,?_⟩
  filter_upwards [hdensity,hcover] with ω hd hcover
  intro N
  let q := fun n => 42*sqrt (log (B*N n))
  let W := physicalWidth ω
  have hm : Tendsto (fun n => q n/N n) atTop (𝓝 0) := normalized_mesh hB
  have hratio : Tendsto (fun n => q n/W n) atTop (𝓝 0) := by
    have h := hm.div hd hw.ne'
    rw [zero_div] at h
    apply h.congr
    intro n
    change (q n/N n)/(W n/N n)=q n/W n
    exact div_div_div_cancel_right₀ (by dsimp only [N]; positivity) _ _
  refine ⟨hd,?_,?_⟩
  · intro ε hε
    let θ := 4*arcsin (ε/2)
    have hθ : θ<2*π := by
      have ha := arcsin_lt_arcsin (show -1 ≤ ε/2 by linarith only [hε.1]) (show ε/2<1 by linarith only [hε.2]) le_rfl
      rw [arcsin_one] at ha
      dsimp only [θ]; linarith only [ha]
    have hlim : Tendsto (fun n => θ*(1+2*(q n/W n))) atTop (𝓝 θ) := by
      simpa only [mul_zero,add_zero,mul_one] using ((hratio.const_mul 2).const_add 1).const_mul θ
    have he : ∀ᶠ n in atTop, emptyExit ω n ε=θ/W n := by
      filter_upwards [hcover,hlim.eventually_lt_const hθ,hd.eventually_const_lt hw] with n hn hs hW
      exact exit_from_cover ω n (mul_nonneg (by norm_num) (sqrt_nonneg _)) hε hn
        ((div_pos_iff_of_pos_right (show 0 < N n by dsimp only [N]; positivity)).mp hW) hs
    refine ⟨he,((tendsto_const_nhds (x:=θ)).div hd hw.ne').congr' ?_⟩
    filter_upwards [he] with n hn
    change θ/(W n/N n)=N n*emptyExit ω n ε
    rw [hn]
    simp only [div_eq_mul_inv,mul_inv_rev,inv_inv]
    ring
  · intro u x hu hn
    let H := fun n => shellOperator (pathPauliDisorderShell ω n)
    let t := fun n => u n/N n
    let A := fun n => orbitSpectralEnclosingArcLength (H n) (t n)
    have hspan : Tendsto (fun n => t n*W n) atTop (𝓝 (x*w)) := by
      apply (hu.mul hd).congr
      intro n
      change u n*(W n/N n)=u n/N n*W n
      ring
    have herr : Tendsto (fun n => 2*t n*q n) atTop (𝓝 0) := by
      have h := (hu.mul hm).const_mul 2
      rw [mul_zero,mul_zero] at h
      apply h.congr
      intro n
      change 2*(u n*(q n/N n))=2*(u n/N n)*q n
      ring
    have ha : Tendsto A atTop (𝓝 (min (x*w) (2*π))) := by
      have hl := hspan.min (tendsto_const_nhds (x:=2*π) |>.sub herr)
      rw [sub_zero] at hl
      have h := (hn.and hcover).mono fun n ⟨h₁,h₂⟩ => physical_arc_bounds (H n) h₂
        (div_nonneg h₁ (show 0 ≤ N n by dsimp only [N]; positivity))
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl (hspan.min tendsto_const_nhds)
        (h.mono fun _ h => h.1) (h.mono fun _ h => h.2)
    apply (((continuous_sin.tendsto _).comp (ha.div_const 4)).const_mul 2).congr
    intro n
    exact (orbitCircuitDistance_zeroGate_eq_enclosingArc (H n) (t n)).symm

#print axioms gaussian_full_ascent
end
end GaloisForLFunctions.HTGeometry.FirstAscent.EnergyMesh
