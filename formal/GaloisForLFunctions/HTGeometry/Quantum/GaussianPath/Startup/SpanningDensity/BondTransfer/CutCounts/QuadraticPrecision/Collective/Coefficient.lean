import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutCounts.QuadraticPrecision.Collective.GateError
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.CutCounts.QuadraticPrecision.InitialCoefficient

/-! # Growth of the above-sweep quadratic coefficient along frozen prefixes -/
open MeasureTheory Set Filter Real Topology
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
noncomputable section

/-- For a whole above-sweep band, the exact quadratic coefficient is
at least a deterministic multiple of √(K−1) and at most a deterministic
multiple of K, simultaneously on all sufficiently long prefixes. -/
theorem gaussian_growing_quadratic_coefficient :
    ∃ c>(0:ℝ), ∃ b>(0:ℝ), ∃ A>(0:ℝ), ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N : ℝ := (n+1:ℕ)
      let H := (⟨_,isSelfAdjoint_pathHamiltonian (pathPauliDisorderShell ω n)⟩ :
        selfAdjoint (Matrix (Fin (n+2)→Bool) (Fin (n+2)→Bool) ℂ))
      ∀ k : ℕ, n+1≤k → (k:ℝ)≤(1+b)*N →
        ∃ v∈Icc (c*sqrt N) (A*((n+2:ℕ):ℝ)),
          Tendsto (fun t => orbitCircuitDistance H k t/t^2) (𝓝[≠] 0) (𝓝 v) := by
  obtain ⟨c,hc,b,hb,hphys⟩ := gaussian_collective_precision_excess
  obtain ⟨s,hs,hlim⟩ := gaussian_sweep_quadratic_coefficient
  obtain ⟨_,A,_,hA,hmass⟩ := gaussian_path_eventual_coefficient_mass
  refine ⟨c,hc,min b s,lt_min hb hs,84*A,by positivity,?_⟩
  filter_upwards [hphys,hlim,hmass] with ω hw hω hμ
  filter_upwards [hw,hω,hμ] with n hn hl hm
  intro N H k hlo hhi
  have hN : 0≤N := Nat.cast_nonneg _
  have h₁ := hhi.trans (mul_le_mul_of_nonneg_right (add_le_add (le_refl 1) (min_le_left b s)) hN)
  have h₂ := hhi.trans (mul_le_mul_of_nonneg_right (add_le_add (le_refl 1) (min_le_right b s)) hN)
  obtain ⟨v,hv,ht⟩ := hl k hlo h₂
  refine ⟨v,⟨?_,hv.2.trans (by linarith only [hm.2])⟩,ht⟩
  have hsub : Ioi (0:ℝ)⊆({0}:Set ℝ)ᶜ := by
    intro x hx
    exact (show 0<x from hx).ne'
  apply ge_of_tendsto (ht.mono_left (nhdsWithin_mono 0 hsub))
  have hsp : 0<sqrt N+1 := by positivity
  filter_upwards [self_mem_nhdsWithin,nhdsWithin_le_nhds (gt_mem_nhds
    (show (0:ℝ) < min 1 (1/(sqrt N+1)) from lt_min zero_lt_one (one_div_pos.mpr hsp)))] with t hp hx
  have hp' : 0<t := hp
  have hsmall := (le_div_iff₀ hsp).mp (hx.le.trans (min_le_right ..))
  have hmin : sqrt N*t^2≤t := by linarith only [mul_le_mul_of_nonneg_right hsmall hp'.le,sq_nonneg t]
  apply (le_div_iff₀ (sq_pos_of_pos hp')).mpr
  by_contra! h
  have hfit : HasProjectiveCircuitApproximation (n+2) (c*min t (sqrt N*t^2)) k (unitaryEvolution H.val t) :=
    (hasProjectiveCircuitApproximation_iff_infDist ..).mpr (by
      change orbitCircuitDistance H k t≤_
      rw [min_eq_right hmin]
      linarith only [h])
  exact h₁.not_gt (hn t ⟨hp',hx.le.trans (min_le_left ..)⟩ k hfit)

#print axioms gaussian_growing_quadratic_coefficient
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
