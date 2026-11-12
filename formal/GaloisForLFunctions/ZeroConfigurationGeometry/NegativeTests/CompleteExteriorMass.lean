import GaloisForLFunctions.ZeroConfigurationGeometry.NegativeTests.SharpLocation

/-!
# Adaptive clusters pay their complete exterior Fourier mass

An empty annulus selects the cluster; the normalized camera annihilates
its nearby exterior. Its summable distant tail therefore bounds the whole
exterior, including every multiplicity. No separation or mass hypothesis
is required of the input zero.
-/

noncomputable section

open Complex Set MeasureTheory
open scoped Real

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-- The full exterior Fourier norm mass, with the zero multiplicities. -/
def clusterExteriorFourierTerm (s : Finset ℂ) (f : ℝ → ℂ) (z : ℂ) : ℝ := by
  classical
  exact if z ∈ s then 0 else
    ‖multDiff zetaZeroConfig emptyZeroConfig z‖ * ‖paperFT f (gammaOf z)‖

theorem clusterExteriorFourierTerm_nonneg (s : Finset ℂ) (f : ℝ → ℂ) (z : ℂ) :
    0 ≤ clusterExteriorFourierTerm s f z := by
  classical
  unfold clusterExteriorFourierTerm
  split_ifs <;> positivity

/-- Exact local annihilation turns the distant-tail estimate into a bound
for the complete exterior, without any estimate for the number of its zeros. -/
theorem clusterExteriorFourierTerm_le_far
    {s : Finset ℂ} {f : ℝ → ℂ} {T R : ℝ}
    (hkill : ∀ z ∈ zetaZeroConfig.carrier, |z.im - T| ≤ R → z ∉ s →
      paperFT f (gammaOf z) = 0) (z : ℂ) :
    clusterExteriorFourierTerm s f z ≤
      fourierFarTerm (multDiff zetaZeroConfig emptyZeroConfig) f T R z := by
  classical
  by_cases hz : z ∈ s
  · simp only [clusterExteriorFourierTerm, hz, if_true]
    exact fourierFarTerm_nonneg _ _ _ _ _
  by_cases hfar : R < |z.im - T|
  · simp only [clusterExteriorFourierTerm, hz, if_false, fourierFarTerm, hfar, if_true]
    exact le_refl _
  have he : ‖multDiff zetaZeroConfig emptyZeroConfig z‖ * ‖paperFT f (gammaOf z)‖ = 0 := by
    by_cases hc : multDiff zetaZeroConfig emptyZeroConfig z = 0
    · rw [hc, norm_zero, zero_mul]
    · rw [hkill z ((multDiff_empty_ne_zero_iff _ _).mp hc) (le_of_not_gt hfar) hz,
        norm_zero, mul_zero]
  simp only [clusterExteriorFourierTerm, hz, if_false, he, fourierFarTerm, hfar]
  exact le_refl _

/-- Every zero above the cubic-logarithmic depth threshold has a finite
coherent cluster whose complete exterior mass is at most a quarter.
The cluster and its isolation are constructed, not assumed. -/
theorem exists_zeta_cluster_with_complete_exterior_mass
    {lam c T : ℝ} (hlam : 1 < lam) (hc : 0 ≤ c)
    (hT : zetaNegativeCameraHeight lam c ≤ T)
    {p : ℂ} (hp : p ∈ zetaZeroConfig.carrier) (hpT : p.im = T)
    (hdepth : Real.exp (-(c * Real.log (T / (2 * π)) ^ 3)) ≤ |depth p|) :
    ∃ (r : ℝ) (s : Finset ℂ) (f : ℝ → ℂ),
      0 ≤ r ∧ r < |depth p| ∧ p ∈ s ∧
      (∀ z, z ∈ s ↔ z ∈ zetaZeroConfig.carrier ∧ ‖z - p‖ ≤ r) ∧
      ApertureWindow (lam * (Real.log (T / (2 * π)) / 2)) f ∧
      (∀ z ∈ s, ‖paperFT f (gammaOf z) - 1‖ ≤ 1 / 4) ∧
      Summable (clusterExteriorFourierTerm s f) ∧
      (∑' z, clusterExteriorFourierTerm s f z) ≤ 1 / 4 ∧
      (∀ F : Finset ℂ, (∀ z ∈ F, z ∈ zetaZeroConfig.carrier) → Disjoint F s →
        (∑ z ∈ F, (zetaZeroConfig.mult z : ℝ) * ‖paperFT f (gammaOf z)‖) ≤ 1 / 4) := by
  classical
  have hlamhalf : 1 / 2 < lam / 2 := by linarith only [hlam]
  have hκ0 : 0 ≤ slowExponent (lam / 2) := by
    unfold slowExponent
    linarith only [mul_pos Real.pi_pos (show 0 < lam / 2 by linarith only [hlam]), hlam]
  have hC0 := zetaClusterCountConstant_nonneg hlamhalf
  have hLη0 : 0 ≤ c + 2 + 8 * (slowExponent (lam / 2) + 2) *
      zetaClusterCountConstant (lam / 2) := by positivity
  have hTh : zetaCubicCameraHeight (lam / 2)
      (c + 2 + 8 * (slowExponent (lam / 2) + 2) * zetaClusterCountConstant (lam / 2)) ≤ T := hT
  have hcountT : zetaCameraCountHeight (lam / 2 + 1 / 2) ≤ T :=
    (le_max_left _ _).trans hTh
  have hbase : 2 * π * Real.exp 1 ≤ T :=
    (cameraCubicIsolationHeight_ge (lam / 2 + 1 / 2) (lam / 2)
      (zetaCameraCountConstant (lam / 2 + 1 / 2)) (33 / 100)
      (c + 2 + 8 * (slowExponent (lam / 2) + 2) * zetaClusterCountConstant (lam / 2))).trans
      ((le_max_right _ _).trans hTh)
  have hT0 : 0 < T := (by positivity : 0 < 2 * π * Real.exp 1).trans_le hbase
  let u := Real.log (T / (2 * π))
  have hu1 : 1 ≤ u := by
    dsimp only [u]
    rw [Real.le_log_iff_exp_le (by positivity), le_div_iff₀ (by positivity)]
    linarith only [hbase]
  have hTu : T = 2 * π * Real.exp u := by
    dsimp only [u]
    rw [Real.exp_log (by positivity : 0 < T / (2 * π))]
    field_simp
  obtain ⟨η, r, hη0, hη1, hr0, hre, hrδ, hlogη, hiso⟩ :=
    exists_zeta_camera_cluster hlamhalf hc hu1 hTu hcountT hp hpT hdepth
  obtain ⟨f, hfw, hkill, haccurate, hfar, hfarBound⟩ :=
    zeta_cluster_camera_explicit hlamhalf hLη0 hTh hp hpT
      hη0 hη1 hlogη hr0 hre.le (fun z hz _ => hiso z hz)
  have hfin : {z : ℂ | z ∈ zetaZeroConfig.carrier ∧ ‖z - p‖ ≤ r}.Finite :=
    (zetaZeroConfig.window_finite (T - r - 1) (T + r)).subset fun z hz => by
      have hb := (Complex.abs_im_le_norm (z - p)).trans hz.2
      simp only [Complex.sub_im, hpT] at hb
      exact ⟨hz.1, by linarith only [(abs_le.mp hb).1],
        by linarith only [(abs_le.mp hb).2]⟩
  let s := hfin.toFinset
  have hmem (z : ℂ) : z ∈ s ↔ z ∈ zetaZeroConfig.carrier ∧ ‖z - p‖ ≤ r :=
    Set.Finite.mem_toFinset hfin
  have hdom (z : ℂ) : clusterExteriorFourierTerm s f z ≤
      fourierFarTerm (multDiff zetaZeroConfig emptyZeroConfig) f T (T / 4) z := by
    apply clusterExteriorFourierTerm_le_far
    intro w hw hwT hws
    exact hkill w hw hwT (fun hwr => hws ((hmem w).mpr ⟨hw, hwr⟩))
  have hs : Summable (clusterExteriorFourierTerm s f) :=
    hfar.of_nonneg_of_le (clusterExteriorFourierTerm_nonneg s f) hdom
  have hmass : (∑' z, clusterExteriorFourierTerm s f z) ≤ 1 / 4 :=
    (hs.tsum_le_tsum hdom hfar).trans hfarBound
  refine ⟨r, s, f, hr0, hrδ, (hmem p).mpr ⟨hp, ?_⟩, hmem, ?_,
    (fun z hz => haccurate z ((hmem z).mp hz).2), hs, hmass, ?_⟩
  · simpa only [sub_self, norm_zero] using hr0
  · simpa only [show 2 * (lam / 2 * (Real.log (T / (2 * π)) / 2)) =
      lam * (Real.log (T / (2 * π)) / 2) by ring] using hfw
  · intro F hF hdis
    have heq : (∑ z ∈ F, (zetaZeroConfig.mult z : ℝ) * ‖paperFT f (gammaOf z)‖) =
        ∑ z ∈ F, clusterExteriorFourierTerm s f z := by
      apply Finset.sum_congr rfl
      intro z hz
      have hzs : z ∉ s := fun hzs => Finset.disjoint_left.mp hdis hz hzs
      simp only [clusterExteriorFourierTerm, hzs, if_false,
        multDiff_emptyZeroConfig, Set.indicator_of_mem (hF z hz), Complex.norm_natCast]
    rw [heq]
    exact (hs.sum_le_tsum F (fun z _ => clusterExteriorFourierTerm_nonneg s f z)).trans hmass

end GaloisForLFunctions.ZeroConfigurationGeometry
