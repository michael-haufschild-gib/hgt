import GaloisForLFunctions.RHTower.SelbergCompactTestApproximation
import GaloisForLFunctions.RHTower.SelbergMaassWeakCurvature

/-!
# Actual retained curvature on continuous compact tests

Common-compact C² approximation and positivity prove convergence of the original
regularized curvature integral on every continuous test supported compactly at
positive height. Its limit is a positive real linear extension of the actual
weak curvature, with no assumed measure or approximate source substituted.
-/

open Set Filter Topology MeasureTheory UpperHalfPlane
open scoped ContDiff CompactlySupported
namespace GaloisForLFunctions.RHTower.SelbergMaassContinuousCurvature
open SelbergMaassMean SelbergMaassWeakCurvature SelbergMaassRegulatorMass
  SelbergLocalTestGreen SelbergCompactTestApproximation
noncomputable section

variable (N : ℕ) {lam : ℝ}
    (f : MaassCuspEigenform (realImage (CongruenceSubgroup.Gamma (N + 1))) lam)

/-- Actual regularized curvature respects subtraction of integrable compact test pairings. -/
theorem testedCurvature_sub {phi psi : ℂ → ℝ}
    (hp : Continuous phi) (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im})
    (hq : Continuous psi) (hd : HasCompactSupport psi) (ht : tsupport psi ⊆ {z : ℂ | 0 < z.im})
    (e : Ioi (0 : ℝ)) :
    testedCurvature N f e (fun z => phi z - psi z) =
      testedCurvature N f e phi - testedCurvature N f e psi := by
  unfold testedCurvature
  simp_rw [sub_mul]
  exact integral_sub (test_curvature_integrable N f hp hc hs e)
    (test_curvature_integrable N f hq hd ht e)

/-- A common compact cutoff controls the actual curvature pairing error by the uniform difference of two continuous tests. -/
theorem testedCurvature_cutoff_error {K : Set ℂ} (hKU : K ⊆ {z : ℂ | 0 < z.im})
    {phi psi chi : ℂ → ℝ}
    (hp : Continuous phi) (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ K)
    (hq : Continuous psi) (hd : HasCompactSupport psi) (ht : tsupport psi ⊆ K)
    (hr : Continuous chi) (hk : HasCompactSupport chi) (hu : tsupport chi ⊆ {z : ℂ | 0 < z.im})
    (hn : ∀ z, 0 ≤ chi z) (hone : ∀ z ∈ K, chi z = 1)
    {c : ℝ} (hc0 : 0 ≤ c) (hb : ∀ z, ‖phi z - psi z‖ ≤ c) (e : Ioi (0 : ℝ)) :
    ‖testedCurvature N f e phi - testedCurvature N f e psi‖ ≤ c * testedCurvature N f e chi := by
  rw [← testedCurvature_sub N f hp hc (hs.trans hKU) hq hd (ht.trans hKU)]
  apply testedCurvature_norm_le N f hr hk hu
  intro z
  by_cases hz : z ∈ K
  · rw [hone z hz, mul_one]
    exact hb z
  · have hpz : phi z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hs h))
    have hqz : psi z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (ht h))
    simp only [hpz, hqz, sub_self, norm_zero]
    exact mul_nonneg hc0 (hn z)

/-- Every continuous compact test in the upper half-plane has an actual retained-curvature limit, constructed using common-compact C² approximation. -/
theorem exists_testedCurvature_limit {phi : ℂ → ℝ} (hp : Continuous phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) :
    ∃ a : ℝ, Tendsto (fun e : Ioi (0 : ℝ) => testedCurvature N f e phi) regulatorAtZero (𝓝 a) := by
  obtain ⟨K, hK, hKU, hsK, happ⟩ := exists_common_compact_approximation hp hc hs
  obtain ⟨chi, hq, hd, ht, hn, hone⟩ := exists_nonnegative_cutoff hK hKU
  let M : ℝ := weakCurvature N f chi + 1
  have hM : 0 < M := by
    have h := weakCurvature_nonneg N f hq hd ht hn
    dsimp [M]
    linarith
  have hMb : ∀ᶠ e : Ioi (0 : ℝ) in regulatorAtZero, testedCurvature N f e chi < M :=
    (tendsto_order.1 (testedCurvature_limit N f hq hd ht)).2 M (by dsimp [M]; linarith)
  apply exists_limit_of_eventual_approximation
  intro ε hε
  obtain ⟨psi, hr, hu, he⟩ := happ (ε / M) (div_pos hε hM)
  have hk : HasCompactSupport psi := hK.of_isClosed_subset isClosed_closure hu
  refine ⟨fun e => testedCurvature N f e psi, weakCurvature N f psi,
    testedCurvature_limit N f hr hk (hu.trans hKU), ?_⟩
  filter_upwards [hMb] with e heM
  calc
    ‖testedCurvature N f e phi - testedCurvature N f e psi‖ ≤ ε / M * testedCurvature N f e chi :=
      testedCurvature_cutoff_error N f hKU hp hc hsK hr.continuous hk hu hq.continuous hd ht hn hone
        (div_pos hε hM).le (fun z => by simpa only [norm_sub_rev] using he z) e
    _ ≤ ε / M * M := mul_le_mul_of_nonneg_left heM.le (div_pos hε hM).le
    _ = ε := div_mul_cancel₀ ε hM.ne'

/-- The actual positive-regulator limit of a continuous test pairing; convergence is proved on the admissible compact test space. -/
def continuousCurvature (phi : ℂ → ℝ) : ℝ :=
  limUnder regulatorAtZero (fun e : Ioi (0 : ℝ) => testedCurvature N f e phi)

/-- The original regularized source integrals converge to the constructed continuous-test curvature value. -/
theorem continuousCurvature_limit {phi : ℂ → ℝ} (hp : Continuous phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) :
    Tendsto (fun e : Ioi (0 : ℝ) => testedCurvature N f e phi)
      regulatorAtZero (𝓝 (continuousCurvature N f phi)) :=
  tendsto_nhds_limUnder (exists_testedCurvature_limit N f hp hc hs)

/-- The continuous-test extension recovers the exact original weak-curvature formula on C² tests. -/
theorem continuousCurvature_eq_weak {phi : ℂ → ℝ} (hp : ContDiff ℝ 2 phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) :
    continuousCurvature N f phi = weakCurvature N f phi :=
  (testedCurvature_limit N f hp hc hs).limUnder_eq

/-- The actual continuous-test limit is nonnegative on nonnegative admissible tests. -/
theorem continuousCurvature_nonneg {phi : ℂ → ℝ} (hp : Continuous phi)
    (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im}) (hn : ∀ z, 0 ≤ phi z) :
    0 ≤ continuousCurvature N f phi :=
  ge_of_tendsto (continuousCurvature_limit N f hp hc hs)
    (Eventually.of_forall (testedCurvature_nonneg N f hn))

/-- The actual continuous-test curvature is additive. -/
theorem continuousCurvature_add {phi psi : ℂ → ℝ}
    (hp : Continuous phi) (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im})
    (hq : Continuous psi) (hd : HasCompactSupport psi) (ht : tsupport psi ⊆ {z : ℂ | 0 < z.im}) :
    continuousCurvature N f (fun z => phi z + psi z) =
      continuousCurvature N f phi + continuousCurvature N f psi := by
  have hleft := continuousCurvature_limit N f (hp.add hq) (hc.add hd)
    ((tsupport_add phi psi).trans (union_subset hs ht))
  have hright := (continuousCurvature_limit N f hp hc hs).add (continuousCurvature_limit N f hq hd ht)
  change Tendsto (fun e : Ioi (0 : ℝ) => testedCurvature N f e (fun z => phi z + psi z))
    regulatorAtZero (𝓝 (continuousCurvature N f (fun z => phi z + psi z))) at hleft
  simp only [testedCurvature_add N f hp hc hs hq hd ht] at hleft
  exact tendsto_nhds_unique hleft hright

/-- The actual continuous-test curvature commutes with real scalar multiplication. -/
theorem continuousCurvature_const_mul {phi : ℂ → ℝ}
    (hp : Continuous phi) (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im})
    (c : ℝ) : continuousCurvature N f (fun z => c * phi z) = c * continuousCurvature N f phi := by
  have hleft := continuousCurvature_limit N f (hp.const_mul c) hc.mul_left
    ((tsupport_mul_subset_right (f := fun _ => c) (g := phi)).trans hs)
  simp only [testedCurvature_const_mul] at hleft
  exact tendsto_nhds_unique hleft ((continuousCurvature_limit N f hp hc hs).const_mul c)

/-- Pointwise test ordering passes to the actual continuous-test curvature limit. -/
theorem continuousCurvature_mono {phi psi : ℂ → ℝ}
    (hp : Continuous phi) (hc : HasCompactSupport phi) (hs : tsupport phi ⊆ {z : ℂ | 0 < z.im})
    (hq : Continuous psi) (hd : HasCompactSupport psi) (ht : tsupport psi ⊆ {z : ℂ | 0 < z.im})
    (h : ∀ z, phi z ≤ psi z) : continuousCurvature N f phi ≤ continuousCurvature N f psi :=
  le_of_tendsto_of_tendsto (continuousCurvature_limit N f hp hc hs) (continuousCurvature_limit N f hq hd ht)
    (Eventually.of_forall (testedCurvature_mono N f hp hc hs hq hd ht h))

end
end GaloisForLFunctions.RHTower.SelbergMaassContinuousCurvature
