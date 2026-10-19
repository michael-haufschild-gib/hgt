import GaloisForLFunctions.SquareRootThreshold.ClusterTotalVariationBlindness
import GaloisForLFunctions.SquareRootThreshold.SmoothDepthProfileHidingLaw
import GaloisForLFunctions.SquareRootThreshold.WindowedPositivityNoGoForOffLineConfigurations

/-!
# Height averages are blind to small-variation clusters and to Toeplitz-positive profiles

A windowed Weil form with window `η` supported in `[-r, r]` is a height average of localized
Weil forms (`windowedW_eq_integral_heightShift`) and an integral of aperture-`r` Weil forms of the
window slices (`windowedW_eq_integral_W`). Hence positivity at aperture `r` passes to every
windowed form at resolution `r`, **whatever the aperture of the test**
(`re_windowedW_nonneg_of_aperture_nonneg`).

Combined with the configuration laws this extends the averaging no-go from off-line lattices to:

* **clusters** (`re_windowedW_clusterConfig_nonneg`): every cluster of off-line zeros with
  `r · TV(d) · sinh(2δr) ≤ 1`, `4r ≤ L`, of any length, position and profile shape;
* **periodic depth profiles** (`re_windowedW_profileConfig_nonneg`): every profile whose Toeplitz
  matrix of size `⌈2rP/L⌉` is positive semidefinite, in particular every smooth profile in the
  range of `SmoothDepthProfileHidingLaw` and every uniform depth for `r ≤ L/2`.

A cluster with an edge is visible at aperture `O(1/δ)` for single tests
(`OffLineRunEdgeVisibilityLaw`), yet every height average at resolution `r ≲ 1/δ` of every test is
nonnegative: averaging over heights at a fixed resolution cannot read the edge.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Temperedness -/

/-- A cluster configuration is tempered. -/
theorem temperedConfig_clusterConfig {L : ℝ} (hL : 0 < L) (S : Finset ℤ) (d : ℤ → ℝ)
    (hd0 : ∀ k ∈ S, 0 < d k) (hd1 : ∀ k ∈ S, d k ≤ 1 / 2) :
    TemperedConfig (clusterConfig hL S d hd0 hd1) := by
  set Z := clusterConfig hL S d hd0 hd1 with hZ
  set G : ℂ → ℝ := fun ρ => (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) with hG
  have hmult : ∀ ρ, Z.mult ρ = if ρ.re = 1 / 2 then 2 else 1 := fun _ => rfl
  -- the on-line points off the cluster
  have hA : Summable fun ρ : Set.range (fun k : {k : ℤ // k ∉ S} => verticalLatticePoint L 0 k) =>
      G ρ := by
    have hinj : Function.Injective (fun k : {k : ℤ // k ∉ S} => verticalLatticePoint L 0 k) :=
      fun k k' h => Subtype.ext (verticalLatticePoint_injective hL 0 h)
    have hs := ((summable_lattice_weight hL 0).mul_left 2).subtype {k : ℤ | k ∉ S}
    have hs' : Summable (G ∘ fun k : {k : ℤ // k ∉ S} => verticalLatticePoint L 0 k) := by
      refine hs.congr fun k => ?_
      simp only [Function.comp_apply, hG, hmult, verticalLatticePoint, add_zero, if_true,
        Nat.cast_ofNat]
      ring
    obtain ⟨a, ha⟩ := hs'
    exact ⟨a, hinj.hasSum_range_iff.mpr ha⟩
  have hBp : Summable fun ρ : Set.range (fun k : S => verticalLatticePoint L (d k) k) => G ρ :=
    (Set.finite_range _).summable G
  have hBm : Summable fun ρ : Set.range (fun k : S => verticalLatticePoint L (-d k) k) => G ρ :=
    (Set.finite_range _).summable G
  have hd₁ : Disjoint (Set.range fun k : {k : ℤ // k ∉ S} => verticalLatticePoint L 0 k)
      (Set.range fun k : S => verticalLatticePoint L (d k) k) := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ ⟨k', hk'⟩
    have := congrArg Complex.re hk'
    simp only [verticalLatticePoint] at this
    linarith [hd0 k' k'.2]
  have hd₂ : Disjoint ((Set.range fun k : {k : ℤ // k ∉ S} => verticalLatticePoint L 0 k) ∪
      Set.range fun k : S => verticalLatticePoint L (d k) k)
      (Set.range fun k : S => verticalLatticePoint L (-d k) k) := by
    rw [Set.disjoint_left]
    rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩) ⟨k', hk'⟩
    · have := congrArg Complex.re hk'
      simp only [verticalLatticePoint] at this
      linarith [hd0 k' k'.2]
    · have := congrArg Complex.re hk'
      simp only [verticalLatticePoint] at this
      linarith [hd0 k' k'.2, hd0 k k.2]
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hBp
  obtain ⟨c, hc⟩ := hBm
  exact ⟨_, HasSum.add_disjoint (f := G) hd₂ (HasSum.add_disjoint (f := G) hd₁ ha hb) hc⟩

/-- A periodic depth-profile configuration is tempered. -/
theorem temperedConfig_profileConfig {L : ℝ} (hL : 0 < L) {P : ℕ} (hP : 0 < P) (d : Fin P → ℝ)
    (hd0 : ∀ r, 0 ≤ d r) (hd1 : ∀ r, d r ≤ 1 / 2) :
    TemperedConfig (profileConfig hL hP d hd0 hd1) := by
  set Z := profileConfig hL hP d hd0 hd1 with hZ
  set G : ℂ → ℝ := fun ρ => (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) with hG
  have hw : ∀ (δ : ℝ) (k : ℤ), G (verticalLatticePoint L δ k) ≤
      2 * (1 / (1 + Complex.normSq (gammaOf (verticalLatticePoint L 0 k)))) := by
    intro δ k
    have hm : (Z.mult (verticalLatticePoint L δ k) : ℝ) ≤ 2 := by
      show ((if _ then 2 else 1 : ℕ) : ℝ) ≤ 2
      split_ifs <;> norm_num
    show (Z.mult (verticalLatticePoint L δ k) : ℝ) /
        (1 + Complex.normSq (gammaOf (verticalLatticePoint L δ k))) ≤
      2 * (1 / (1 + Complex.normSq (gammaOf (verticalLatticePoint L 0 k))))
    rw [normSq_gammaOf_verticalLatticePoint, normSq_gammaOf_verticalLatticePoint]
    rw [div_le_iff₀ (by positivity)]
    have h1 : 0 < 1 + (((k : ℝ) * (2 * π / L)) ^ 2 + (0 : ℝ) ^ 2) := by positivity
    calc (Z.mult (verticalLatticePoint L δ k) : ℝ) ≤ 2 := hm
      _ ≤ 2 * (1 / (1 + (((k : ℝ) * (2 * π / L)) ^ 2 + (0 : ℝ) ^ 2))) *
          (1 + (((k : ℝ) * (2 * π / L)) ^ 2 + δ ^ 2)) := by
        rw [mul_assoc, one_div, inv_mul_eq_div, le_mul_iff_one_le_right (by norm_num),
          one_le_div h1]
        nlinarith [sq_nonneg δ]
  have hsumℤ := (summable_lattice_weight hL 0).mul_left 2
  have hsumP : Summable fun rj : Fin P × ℤ =>
      2 * (1 / (1 + Complex.normSq (gammaOf (verticalLatticePoint L 0 (profileIndex P rj))))) :=
    hsumℤ.comp_injective (profileIndex_injective hP)
  have hGnn : ∀ ρ, 0 ≤ G ρ := fun ρ => by
    have := Complex.normSq_nonneg (gammaOf ρ); positivity
  have hA : Summable fun ρ : Set.range (fun rj : Fin P × ℤ =>
      verticalLatticePoint L (d rj.1) (profileIndex P rj)) => G ρ := by
    have hinj : Function.Injective (fun rj : Fin P × ℤ =>
        verticalLatticePoint L (d rj.1) (profileIndex P rj)) :=
      fun rj rj' h => profilePoint_eq_imp hL hP h
    obtain ⟨a, ha⟩ := (hsumP.of_nonneg_of_le (fun rj => hGnn _) fun rj => hw _ _ :
      Summable (G ∘ fun rj : Fin P × ℤ => verticalLatticePoint L (d rj.1) (profileIndex P rj)))
    exact ⟨a, hinj.hasSum_range_iff.mpr ha⟩
  have hB : Summable fun ρ : Set.range (fun rj : {rj : Fin P × ℤ // d rj.1 ≠ 0} =>
      verticalLatticePoint L (-d rj.1.1) (profileIndex P rj.1)) => G ρ := by
    have hinj : Function.Injective (fun rj : {rj : Fin P × ℤ // d rj.1 ≠ 0} =>
        verticalLatticePoint L (-d rj.1.1) (profileIndex P rj.1)) :=
      fun rj rj' h => Subtype.ext (profilePoint_eq_imp hL hP h)
    obtain ⟨a, ha⟩ := ((hsumP.subtype _).of_nonneg_of_le (fun rj => hGnn _) fun rj => hw _ _ :
      Summable (G ∘ fun rj : {rj : Fin P × ℤ // d rj.1 ≠ 0} =>
        verticalLatticePoint L (-d rj.1.1) (profileIndex P rj.1)))
    exact ⟨a, hinj.hasSum_range_iff.mpr ha⟩
  have hd : Disjoint (Set.range fun rj : Fin P × ℤ =>
      verticalLatticePoint L (d rj.1) (profileIndex P rj))
      (Set.range fun rj : {rj : Fin P × ℤ // d rj.1 ≠ 0} =>
        verticalLatticePoint L (-d rj.1.1) (profileIndex P rj.1)) := by
    rw [Set.disjoint_left]
    rintro _ ⟨rj, rfl⟩ ⟨rj', hrj'⟩
    have hre := congrArg Complex.re hrj'
    simp only [verticalLatticePoint] at hre
    have h0 := hd0 rj'.1.1
    have h1 := hd0 rj.1
    exact rj'.2 (by linarith)
  obtain ⟨a, ha⟩ := hA
  obtain ⟨b, hb⟩ := hB
  exact ⟨_, HasSum.add_disjoint (f := G) hd ha hb⟩

/-! ### Windowed blindness -/

/-- **Height averages are blind to small-variation clusters.** If `4r ≤ L` and
`r · TV(d) · sinh(2δr) ≤ 1`, every windowed Weil form of the cluster with window supported in
`[-r, r]` is nonnegative, for tests of every aperture. -/
theorem re_windowedW_clusterConfig_nonneg {L δ r : ℝ} (hL : 0 < L) (S : Finset ℤ) (d : ℤ → ℝ)
    (hd0 : ∀ k ∈ S, 0 < d k) (hd1 : ∀ k ∈ S, d k ≤ 1 / 2) (hdδ : ∀ k ∈ S, d k ≤ δ) (hδ : 0 ≤ δ)
    (hr : 0 ≤ r) (hrL : 4 * r ≤ L) (hTV : r * depthVariation S d * Real.sinh (2 * δ * r) ≤ 1)
    {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hη : ContDiff ℝ 2 η)
    (hηs : tsupport η ⊆ Icc (-r) r) :
    0 ≤ (windowedW (clusterConfig hL S d hd0 hd1) f η).re :=
  re_windowedW_nonneg_of_aperture_nonneg _ (temperedConfig_clusterConfig hL S d hd0 hd1)
    (fun _ hg hgs => re_W_clusterConfig_nonneg hL S d hd0 hd1 hdδ hδ hr hrL hTV hg hgs)
    hf hfc hη hηs

/-- **Height averages are blind to Toeplitz-positive profiles.** If the Toeplitz matrix of size
`⌈2rP/L⌉` of the depth symbol is positive semidefinite, every windowed Weil form with window
supported in `[-r, r]` is nonnegative, for tests of every aperture. -/
theorem re_windowedW_profileConfig_nonneg {L : ℝ} (hL : 0 < L) {P : ℕ} (hP : 0 < P)
    (d : Fin P → ℝ) (hd0 : ∀ r, 0 ≤ d r) (hd1 : ∀ r, d r ≤ 1 / 2) {r : ℝ} (hr : 0 < r)
    (hT : ∀ c : Fin ⌈2 * r * P / L⌉₊ → ℂ,
      0 ≤ (toeplitzForm (depthSymbol L d) ⌈2 * r * P / L⌉₊ c).re)
    {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hη : ContDiff ℝ 2 η)
    (hηs : tsupport η ⊆ Icc (-r) r) :
    0 ≤ (windowedW (profileConfig hL hP d hd0 hd1) f η).re :=
  re_windowedW_nonneg_of_aperture_nonneg _ (temperedConfig_profileConfig hL hP d hd0 hd1)
    ((profileConfig_weil_nonneg_iff hL hP d hd0 hd1 hr).mpr hT) hf hfc hη hηs

/-- **Smooth modulations pass every height average** at a resolution `r` in the range of the
smooth hiding law. -/
theorem re_windowedW_profileConfig_nonneg_of_smooth {L : ℝ} (hL : 0 < L) {k : ℕ}
    (d : Fin (k + 1) → ℝ) (hd0 : ∀ r, 0 ≤ d r) (hd1 : ∀ r, d r ≤ 1 / 2) {δ κ₁ κ₂ r : ℝ}
    (hdδ : ∀ s, d s ≤ δ) (h1 : ∀ s, |d (finRotate (k + 1) s) - d s| ≤ κ₁)
    (h2 : ∀ s, |d (finRotate (k + 1) s) - 2 * d s + d ((finRotate (k + 1)).symm s)| ≤ κ₂)
    (hr : 0 < r) (hrL : 4 * r ≤ L)
    (hcond : ((k + 1 : ℕ) : ℝ) * L * κ₂ * Real.sinh (2 * δ * r) *
        (1 + Real.log ⌈2 * r * ((k + 1 : ℕ) : ℝ) / L⌉₊) / 8 +
      ⌈2 * r * ((k + 1 : ℕ) : ℝ) / L⌉₊ * L ^ 2 * κ₁ ^ 2 * Real.cosh (2 * δ * r) / 4 ≤ 1)
    {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hη : ContDiff ℝ 2 η)
    (hηs : tsupport η ⊆ Icc (-r) r) :
    0 ≤ (windowedW (profileConfig hL (Nat.succ_pos k) d hd0 hd1) f η).re :=
  re_windowedW_nonneg_of_aperture_nonneg _
    (temperedConfig_profileConfig hL (Nat.succ_pos k) d hd0 hd1)
    (fun _ hg hgs => profileConfig_weil_nonneg_of_smooth hL d hd0 hd1 hdδ h1 h2 hr hrL hcond
      hg hgs) hf hfc hη hηs

end GaloisForLFunctions.SquareRootThreshold
