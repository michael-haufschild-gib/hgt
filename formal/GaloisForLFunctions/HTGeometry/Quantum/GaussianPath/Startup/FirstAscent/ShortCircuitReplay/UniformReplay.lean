import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.EnergyMesh.ClippedChord
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.ShortCircuitReplay.GateTranslation

/-! # Uniform inverse-size gate profile after a short-circuit visit -/

open MeasureTheory Filter Set Real
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FirstAscent.ShortCircuitReplay
open ThermodynamicEdges EnergyMesh
noncomputable section

private theorem finite_replay {n k s : ℕ} (u : PathShell n) (v : ℝ) {x w q b : ℝ}
    (hx : 0 ≤ x) (hq : 0 ≤ q) (hb : 0 ≤ b) (hks : k ≤ s)
    (hu : ‖u‖^2 ≤ b*((n+2 : ℕ):ℝ))
    (hc : let H := shellOperator u
      ∀ y ∈ Icc (lower H) (upper H), ∃ i, |H.2.isHermitian.eigenvalues i-y| ≤ q) :
    let N : ℝ := (n+2 : ℕ)
    let H := shellOperator u
    let W := circuitHamiltonianSpectralWidth H
    |orbitCircuitDistance H s (v+x/N)-clippedChord (x*w)| ≤ orbitCircuitDistance H k v+
      x*(q/N+|W/N-w|/2+2*sqrt ((42*b)*(((k+s : ℕ):ℝ)/N))) := by
  intro N H W
  let d := orbitCircuitDistance H
  let t := x/N
  let r := sqrt ((42*b)*(((k+s : ℕ):ℝ)/N))
  have hN : 0 < N := by dsimp only [N]; positivity
  have ht : 0 ≤ t := div_nonneg hx hN.le
  have h₁ := scalar_chord_error H hq ht hc
  have h₂ := clippedChord_lipschitz (t*W) (x*w)
  have hdiff : |t*W-x*w| = x*|W/N-w| := by
    rw [show t*W-x*w=x*(W/N-w) by dsimp only [t]; ring,abs_mul,abs_of_nonneg hx]
  rw [hdiff] at h₂
  have hm : |d 0 t-clippedChord (x*w)| ≤ x*(q/N+|W/N-w|/2) := by
    apply (abs_sub_le _ (clippedChord (t*W)) _).trans
    apply (add_le_add h₁ h₂).trans_eq
    dsimp only [t]; ring
  obtain ⟨hf,hr⟩ := translate_distance H v t hks
  have hs := scaled_advantage u (k+s) x hb hu
  change d 0 t ≤ d (k+s) t+2*|x|*r at hs
  rw [abs_of_nonneg hx] at hs
  have hxr := mul_nonneg hx (sqrt_nonneg ((42*b)*(((k+s : ℕ):ℝ)/N)))
  change 0 ≤ x*r at hxr
  change d s (v+t) ≤ d k v+d 0 t at hf
  change d (k+s) t ≤ d k v+d s (v+t) at hr
  change |d s (v+t)-clippedChord (x*w)| ≤ d k v+x*(q/N+|W/N-w|/2+2*r)
  rw [mul_add]
  exact abs_le.mpr ⟨by linarith only [(abs_le.mp hm).1,hr,hs],
    by linarith only [(abs_le.mp hm).2,hf,hxr]⟩

/-- One vanishing slope controls every nonnegative scaled lag and every
visit on the draw. Its intercept is exactly the best return error at
the smaller gate budget. -/
theorem gaussian_uniform_gate_replay :
    ∃ w : ℝ, 0 < w ∧ ∀ᵐ ω ∂pathPauliDisorderLaw,
      let N := fun n : ℕ => ((n+2 : ℕ):ℝ)
      let H := fun n => shellOperator (pathPauliDisorderShell ω n)
      Tendsto (fun n => physicalWidth ω n/N n) atTop (𝓝 w) ∧
      ∀ (k s : ℕ→ℕ), (∀ᶠ n in atTop, k n ≤ s n) →
        Tendsto (fun n => (s n:ℝ)/N n) atTop (𝓝 0) →
        ∃ f : ℕ→ℝ, Tendsto f atTop (𝓝 0) ∧ ∀ᶠ n in atTop, ∀ v x : ℝ, 0 ≤ x →
          |orbitCircuitDistance (H n) (s n) (v+x/N n)-clippedChord (x*w)| ≤
            orbitCircuitDistance (H n) (k n) v+x*f n := by
  obtain ⟨w,hw,_,hwidth⟩ := gaussian_energy_density
  obtain ⟨B,hB,hcover⟩ := gaussian_energy_cover
  obtain ⟨_,b,_,hb,hmass⟩ := gaussian_path_eventual_coefficient_mass
  refine ⟨w,hw,?_⟩
  filter_upwards [hwidth,hcover,hmass] with ω hW hc hm
  intro N H
  refine ⟨hW,?_⟩
  intro k s hk hs
  let q := fun n => 42*sqrt (log (B*N n))
  have hq : Tendsto (fun n => q n/N n) atTop (𝓝 0) := normalized_mesh hB
  have hd : Tendsto (fun n => |physicalWidth ω n/N n-w|/2) atTop (𝓝 0) := by
    simpa only [sub_self,abs_zero,zero_div] using (hW.sub_const w).abs.div_const 2
  have hsum : Tendsto (fun n => (((k n+s n : ℕ):ℝ)/N n)) atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds
      (by simpa only [zero_add] using hs.add hs)
    · filter_upwards with n; dsimp only [N]; positivity
    · filter_upwards [hk] with n hn
      rw [Nat.cast_add,add_div]
      exact add_le_add (div_le_div_of_nonneg_right (Nat.cast_le.mpr hn) (by dsimp only [N]; positivity)) le_rfl
  have hr := ((hsum.const_mul (42*b)).sqrt).const_mul 2
  simp only [mul_zero,sqrt_zero] at hr
  refine ⟨_,by simpa only [add_zero] using (hq.add hd).add hr,?_⟩
  filter_upwards [hk,hc,hm] with n hn hc hm
  intro v x hx
  exact finite_replay _ v hx (mul_nonneg (by norm_num) (sqrt_nonneg _)) hb.le hn hm.2 hc

#print axioms gaussian_uniform_gate_replay
end
end GaloisForLFunctions.HTGeometry.FirstAscent.ShortCircuitReplay
