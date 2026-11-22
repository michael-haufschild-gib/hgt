import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.SpanningOccupation.EntryBands
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.ConnectedGates.ReturnAnnulus

/-! # Long-time occupation at exactly one gate per physical bond -/
open Filter MeasureTheory Set Real Matrix
open scoped Topology Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningOccupation
noncomputable section
open EmptyVisitFlux SharpOccupation

/-- Dates at which the least affordable circuit has exactly j gates. -/
def exactCount {N : ℕ} (H : selfAdjoint (Register N)) (ε : ℝ) (j : ℕ) : Set ℝ :=
  {v | ∀ s : ℕ, HasProjectiveCircuitApproximation N ε s (unitaryEvolution H.val v) ↔ j ≤ s}

/-- Dates of exact cost N−1 simultaneously at errors ε and B√ε occupy
at least a constant times √ε · ε^(2ᴺ−2). Monotonicity in error then keeps
the cost fixed throughout the intervening range. -/
theorem gaussian_two_tolerance_spanning_occupation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) :=
        ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∃ B C : ℝ, 0 < B ∧ 0 < C ∧ ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ a : ℝ, ∀ᶠ T : ℝ in atTop,
        C*sqrt ε*ε^(2^N-2:ℕ) ≤ volume.real
          ((exactCount H ε (N-1)∩exactCount H (B*sqrt ε) (N-1))∩Icc a T)/(T-a) := by
  filter_upwards [ConnectedGates.gaussian_exact_count_around_returns,
    gaussian_path_all_prefixes_maximally_projective] with ω hann hspec k
  intro N H
  obtain ⟨A,c,hA,hc,hshort⟩ := hann (k+1)
  have hmono : 𝓝[>] (0:ℝ) ≤ 𝓝[≠] 0 := nhdsWithin_mono _ (fun _ hx => (ne_of_gt hx))
  obtain ⟨η,hη,hband⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (hshort.filter_mono hmono)
  let E := fun i => -H.2.isHermitian.eigenvalues i
  let w := fun i => E i/(2*π)
  let W := Finset.univ.sup' Finset.univ_nonempty w-Finset.univ.inf' Finset.univ_nonempty w
  let L := 1+|W|
  let r := 1/(A+1)
  let R := pairTurnRate E
  let d := 2^N-2
  have hL : 0 < L := by dsimp [L]; positivity
  have hr : 0 < r := by dsimp [r]; positivity
  have hcoeff : A*r^2 ≤ 1 := by
    dsimp [r]; rw [_root_.one_div_pow,←div_eq_mul_one_div,div_le_one (by positivity)]
    nlinarith only [sq_nonneg A,hA]
  have hE : MaximallyProjectiveEnergy E := maximallyProjectiveEnergy_neg (hspec k)
  have hR : 0 < R := pair_rate_pos E hE
  let C := r*(1/(2*π))^d*R/8
  let B := c*r/2
  refine ⟨B,C,by dsimp [B]; positivity,by dsimp [C]; positivity,?_⟩
  have hroot : Tendsto Real.sqrt (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [Real.sqrt_zero] using (Real.continuous_sqrt.tendsto (0:ℝ)).mono_left nhdsWithin_le_nhds
  have hs : Tendsto (fun ε => r*sqrt ε) (𝓝[>] (0:ℝ)) (𝓝 0) := by
    simpa only [mul_zero] using hroot.const_mul r
  filter_upwards [Ioo_mem_nhdsGT (zero_lt_one' ℝ),hs.eventually_lt_const hη,
    hs.eventually_lt_const (div_pos one_pos (show 0 < 2*L by positivity)),
    hroot.eventually_lt_const (show 0 < c*r/2 by positivity)] with ε hε hη' hL' hc'
  let h := r*sqrt ε
  have hh : 0 < h := mul_pos hr (sqrt_pos.mpr hε.1)
  have hδ : 0 < ε/2 := half_pos hε.1
  have hδs : ε/2 < sqrt 2 := by
    have h1 : (1:ℝ) ≤ sqrt 2 := (Real.le_sqrt (by norm_num) (by norm_num)).mpr (by norm_num)
    linarith only [h1,hε.2]
  let x := physicalArc (ε/2)
  obtain ⟨hx,_⟩ := physicalArc_spec hδ hδs
  have hxl : (1/(2*π))*ε ≤ x := by
    convert (ShortTimeProducts.physical_arc_bounds hδ hδs).1 using 1; ring
  have hxu : x ≤ 1/4 := by
    have hz := (ShortTimeProducts.physical_arc_bounds hδ hδs).2
    linarith only [hz,hε.2]
  intro a
  have hgap (v w' : ℝ) (hvw : v < w') (hv : visitEntry w x v) (hw : visitEntry w x w') : v+h ≤ w' := by
    have hg := FluxOccupation.entries_separated w hx.1.le hx.2 hvw hv hw
    have hlow : 1/2 ≤ (w'-v)*L := by
      have hl : W ≤ L := by dsimp only [L]; linarith only [le_abs_self W]
      have hm := mul_le_mul_of_nonneg_left hl (sub_nonneg.mpr hvw.le)
      change 1-2*x ≤ (w'-v)*W at hg
      linarith only [hm,hg,hxu]
    have hl := (lt_div_iff₀ (show 0 < 2*L by positivity)).mp hL'
    have hle : h ≤ w'-v := (le_of_mul_le_mul_right (show h*L ≤ (w'-v)*L by
      change h*(2*L)<1 at hl; linarith only [hl,hlow]) hL)
    linarith only [hle]
  have hcovered (v : ℝ) (hv : visitEntry w x v) (t : ℝ) (ht : t ∈ Icc (h/2) h) :
      v+t ∈ exactCount H ε (N-1)∩exactCount H (B*sqrt ε) (N-1) := by
    have ht0 := (half_pos hh).trans_le ht.1
    have hab : A*t^2 ≤ ε := by
      have hs₁ := pow_le_pow_left₀ ht0.le ht.2 2
      have hs₂ := mul_le_mul_of_nonneg_right hcoeff hε.1.le
      dsimp only [h] at hs₁
      rw [mul_pow,Real.sq_sqrt hε.1.le] at hs₁
      nlinarith only [mul_le_mul_of_nonneg_left hs₁ hA.le,hs₂]
    have hgain : ε ≤ B*sqrt ε := by
      have ho := mul_le_mul_of_nonneg_right hc'.le (sqrt_nonneg ε)
      rwa [←sq,Real.sq_sqrt hε.1.le] at ho
    have hct : B*sqrt ε ≤ c*|t| := by
      rw [abs_of_pos ht0]
      have hht := mul_le_mul_of_nonneg_left ht.1 hc.le
      dsimp only [h] at hht
      dsimp only [B]
      linarith only [hht]
    have hv₀ := (physical_visit H hδ hδs v).mp hv.1
    have hv₁ : v ∈ visitSet H 0 (B*sqrt ε/2) := by
      obtain ⟨z,hz,Q,hQ,he⟩ := hv₀
      exact ⟨z,hz,Q,hQ,he.trans (by linarith only [hgain])⟩
    have htη : t ∈ Ioo 0 η := ⟨ht0,ht.2.trans_lt hη'⟩
    exact ⟨hband htη ε hab (hgain.trans hct) v hv₀,
      hband htη _ (hab.trans hgain) hct v hv₁⟩
  have hcT := event_fraction_of_entries E hE _ hx.1 hx.2 hh hR hgap hcovered a
  filter_upwards [hcT] with T hT
  apply le_trans _ hT
  rw [show Fintype.card (Fin N→Bool)=2^N by simp]
  have hpow := pow_le_pow_left₀ (mul_nonneg (by positivity : 0 ≤ 1/(2*π)) hε.1.le) hxl d
  rw [mul_pow] at hpow
  dsimp only [C,h]
  change _ ≤ (r*sqrt ε)*(x^d*R)/8
  nlinarith only [mul_le_mul_of_nonneg_right hpow (show 0 ≤ r*sqrt ε*R by positivity)]

/-- Exact spanning cost at a single prescribed precision and arbitrary origin. -/
theorem gaussian_exact_spanning_occupation :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ k : ℕ,
      let N := k+3
      let H : selfAdjoint (Register N) :=
        ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      ∃ C > (0:ℝ), ∀ᶠ ε : ℝ in 𝓝[>] 0, ∀ a : ℝ, ∀ᶠ T : ℝ in atTop,
        C*sqrt ε*ε^(2^N-2:ℕ) ≤ volume.real (exactCount H ε (N-1)∩Icc a T)/(T-a) := by
  filter_upwards [gaussian_two_tolerance_spanning_occupation] with ω hω k
  intro N H
  obtain ⟨B,C,_,hC,h⟩ := hω k
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with ε hε a
  filter_upwards [hε a,eventually_ge_atTop a] with T hT ha
  apply hT.trans
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr ha)
  exact measureReal_mono (inter_subset_inter_left _ inter_subset_left)
    (measure_ne_top_of_subset inter_subset_right measure_Icc_lt_top.ne)

#print axioms gaussian_two_tolerance_spanning_occupation
#print axioms gaussian_exact_spanning_occupation
end
end GaloisForLFunctions.HTGeometry.SpanningOccupation
