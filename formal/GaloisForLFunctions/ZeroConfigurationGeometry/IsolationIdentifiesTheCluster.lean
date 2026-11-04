import GaloisForLFunctions.ZeroConfigurationGeometry.FiniteModificationsAreSeenAtEveryAperture
import GaloisForLFunctions.ZeroConfigurationGeometry.IsolatingWindows
import GaloisForLFunctions.ZeroConfigurationGeometry.BlindWindowsForPerturbedLattices
import GaloisForLFunctions.ZeroConfigurationGeometry.DifferentialWindowsInvertTheCamera

/-!
# Isolation identifies the cluster

Two tempered configurations `Z, Z'` are mimics at aperture `a` when every window of aperture `a`
gives them the same image. Their **cluster** is the support of the signed multiplicity
`c = m_Z − m_{Z'}`. `FiniteModificationsAreSeenAtEveryAperture` shows that finite clusters never
cancel. Here the finiteness is replaced by a property of the camera: a cluster cannot cancel at a
point that some window of aperture `a` isolates from the rest of the cluster.

* **Infinite polarization** (`W_eq_of_mimic`). The image difference is the absolutely convergent
  sum `Σ_z c(z) f̂(γ_z) conj ĝ(conj γ_z)` (`W_sub_W_eq_tsum`); it is sesquilinear in the window, so
  equal diagonal images force equal images on every pair of windows of the aperture.
* **Isolation forces a zero coefficient** (`multDiff_eq_zero_of_isolated`). If a window `f₀` of
  aperture `a` sees `γ_{z₀}` and is blind to every other point of the cluster, pairing it with a
  window `g` with `ĝ(conj γ_{z₀}) = 1` collapses the difference to `c(z₀) f̂₀(γ_{z₀})`: hence
  `c(z₀) = 0`.
* **Isolable clusters do not cancel** (`eq_of_mimic_of_isolable`). Mimics whose cluster admits an
  isolating window at each of its points are equal.
* **Simple zero sets** (`eq_of_mimic_of_simple_zeros`). If the cluster lies in the simple zero
  set of the transform of one window of aperture `a`, dividing at each point gives the isolating
  windows: mimics at aperture `a` never differ only on the simple zeros of one aperture-`a`
  transform.
* **Lattices** (`eq_of_mimic_of_onLine_lattice`). Mimics at an aperture `a > π/h` whose cluster
  lies on the on-line lattice `{½ + ikh}` are equal, whatever the multiplicities.
* **Perturbed lattices** (`eq_of_mimic_of_perturbed_lattice`, `eq_of_mimic_of_perturbed_lattices`).
  The same holds for clusters on the critical line inside a bounded perturbation `|ν_k − kh| ≤ L` of
  a lattice, with no separation, and inside finite unions of such perturbations of total density
  `D` above the aperture `πD`. To isolate a point one moves every index that hits it off it and
  takes the blind window of the moved perturbation
  (`exists_window_isolating_in_perturbed_lattices`).
* **Thin real backgrounds hide no tilted point** (`eq_of_mimic_of_perturbed_lattices_and_finset`).
  A finite set of arbitrary points may be added to the cluster: convolving with a window of small
  aperture that vanishes on all but one of them (`exists_window_vanishing_on_finset`) isolates
  each point at the same aperture. A tilted configuration therefore has no mimic at aperture `a`
  that differs from it by finitely many points and a real cluster of density `< a/π` inside
  perturbed lattices.

Together with `BlindnessCostsTheDensityAperture` this is a density criterion for cancelling
clusters: a window of aperture `a` can be blind only to configurations of lower density `≤ a/π`, and
clusters inside the simple zero sets of such windows cannot cancel. The Euler columns
(`offLineLattice_mimic_iff`) cancel exactly up to the aperture `π/h` of their spacing `h`.
-/

open MeasureTheory Complex Set Filter
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

theorem summable_multDiff_pointImage {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) :
    Summable fun z => multDiff Z Z' z * pointImage f g z :=
  ((summable_indicator_pointImage Z hZ hf hfc hg hgc).sub
    (summable_indicator_pointImage Z' hZ' hf hfc hg hgc)).congr fun z => by rw [multDiff, sub_mul]

/-- **The image difference is the image of the signed modification**, for every tempered pair. -/
theorem W_sub_W_eq_tsum {Z Z' : ZeroConfig} (hZ : TemperedConfig Z) (hZ' : TemperedConfig Z')
    {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) :
    Z.W f g - Z'.W f g = ∑' z, multDiff Z Z' z * pointImage f g z := by
  rw [W_eq_tsum_indicator, W_eq_tsum_indicator,
    ← (summable_indicator_pointImage Z hZ hf hfc hg hgc).tsum_sub
      (summable_indicator_pointImage Z' hZ' hf hfc hg hgc)]
  exact tsum_congr fun z => by rw [multDiff, sub_mul]

/-- The image of the signed multiplicity of two configurations on the window pair `(f, g)`. -/
def imageDiff (Z Z' : ZeroConfig) (f g : ℝ → ℂ) : ℂ := ∑' z, multDiff Z Z' z * pointImage f g z

/-- The image difference is sesquilinear in the window. -/
theorem imageDiff_add_smul {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (c : ℂ) :
    imageDiff Z Z' (fun u => f u + c * g u) (fun u => f u + c * g u) =
      imageDiff Z Z' f f + c * imageDiff Z Z' g f + conj c * imageDiff Z Z' f g +
        c * conj c * imageDiff Z Z' g g := by
  have hA := summable_multDiff_pointImage hZ hZ' hf hfc hf hfc
  have hB := summable_multDiff_pointImage hZ hZ' hg hgc hf hfc
  have hC := summable_multDiff_pointImage hZ hZ' hf hfc hg hgc
  have hE := summable_multDiff_pointImage hZ hZ' hg hgc hg hgc
  have hsum : ∀ z, multDiff Z Z' z * pointImage (fun u => f u + c * g u)
      (fun u => f u + c * g u) z =
      multDiff Z Z' z * pointImage f f z + c * (multDiff Z Z' z * pointImage g f z) +
        conj c * (multDiff Z Z' z * pointImage f g z) +
          c * conj c * (multDiff Z Z' z * pointImage g g z) := fun z => by
    rw [pointImage_add_smul hf.continuous hfc hg.continuous hgc c z]; ring
  rw [imageDiff, tsum_congr hsum,
    ((hA.add (hB.mul_left c)).add (hC.mul_left (conj c))).tsum_add (hE.mul_left (c * conj c)),
    (hA.add (hB.mul_left c)).tsum_add (hC.mul_left (conj c)), hA.tsum_add (hB.mul_left c),
    tsum_mul_left, tsum_mul_left, tsum_mul_left]
  rfl

/-- **Infinite polarization.** Mimics at aperture `a` have equal images on every pair of windows
of aperture `a`. -/
theorem W_eq_of_mimic {Z Z' : ZeroConfig} (hZ : TemperedConfig Z) (hZ' : TemperedConfig Z')
    {a : ℝ} (hW : ∀ f, ApertureWindow a f → Z.W f f = Z'.W f f) {f g : ℝ → ℂ}
    (hf : ApertureWindow a f) (hg : ApertureWindow a g) : Z.W f g = Z'.W f g := by
  have hdiag : ∀ f, ApertureWindow a f → imageDiff Z Z' f f = 0 := fun f hf => by
    rw [imageDiff, ← W_sub_W_eq_tsum hZ hZ' hf.1 hf.hasCompactSupport hf.1 hf.hasCompactSupport,
      hW f hf, sub_self]
  have hfc := hf.hasCompactSupport
  have hgc := hg.hasCompactSupport
  have e1 := imageDiff_add_smul hZ hZ' hf.1 hfc hg.1 hgc 1
  have eI := imageDiff_add_smul hZ hZ' hf.1 hfc hg.1 hgc I
  rw [hdiag _ (hf.add_smul hg 1), hdiag f hf, hdiag g hg] at e1
  rw [hdiag _ (hf.add_smul hg I), hdiag f hf, hdiag g hg] at eI
  simp only [map_one, Complex.conj_I, zero_add, add_zero, one_mul, mul_zero] at e1 eI
  have h2 : imageDiff Z Z' g f - imageDiff Z Z' f g = 0 := by
    have : I * (imageDiff Z Z' g f - imageDiff Z Z' f g) = 0 := by linear_combination -eI
    exact (mul_eq_zero.mp this).resolve_left Complex.I_ne_zero
  have hfg : imageDiff Z Z' f g = 0 := by linear_combination (-1 / 2 : ℂ) * e1 - (1 / 2 : ℂ) * h2
  have h := W_sub_W_eq_tsum hZ hZ' hf.1 hfc hg.1 hgc
  rw [← imageDiff, hfg] at h
  exact sub_eq_zero.mp h

/-- **Isolation forces a zero coefficient.** If a window of aperture `a` sees `γ_{z₀}` and is blind
to every other point of the cluster of two mimics, the cluster does not contain `z₀`. -/
theorem multDiff_eq_zero_of_isolated {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {a : ℝ} (ha : 0 < a)
    (hW : ∀ f, ApertureWindow a f → Z.W f f = Z'.W f f) {z₀ : ℂ} {f₀ : ℝ → ℂ}
    (hf₀ : ApertureWindow a f₀)
    (hblind : ∀ z, z ≠ z₀ → multDiff Z Z' z ≠ 0 → paperFT f₀ (gammaOf z) = 0)
    (hsee : paperFT f₀ (gammaOf z₀) ≠ 0) : multDiff Z Z' z₀ = 0 := by
  obtain ⟨g, hg, hg1⟩ := exists_window_paperFT_eq_one ha (conj (gammaOf z₀))
  have h := W_sub_W_eq_tsum hZ hZ' hf₀.1 hf₀.hasCompactSupport hg.1 hg.hasCompactSupport
  rw [W_eq_of_mimic hZ hZ' hW hf₀ hg, sub_self, tsum_eq_single z₀ fun z hz => ?_] at h
  · rw [pointImage, hg1, map_one, mul_one] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hsee
  · by_cases hc : multDiff Z Z' z = 0
    · rw [hc, zero_mul]
    · rw [pointImage, hblind z hz hc, zero_mul, mul_zero]

/-- **Isolable clusters do not cancel.** -/
theorem eq_of_mimic_of_isolable {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {a : ℝ} (ha : 0 < a)
    (hW : ∀ f, ApertureWindow a f → Z.W f f = Z'.W f f)
    (hiso : ∀ z₀, multDiff Z Z' z₀ ≠ 0 → ∃ f₀, ApertureWindow a f₀ ∧
      (∀ z, z ≠ z₀ → multDiff Z Z' z ≠ 0 → paperFT f₀ (gammaOf z) = 0) ∧
        paperFT f₀ (gammaOf z₀) ≠ 0) :
    Z.carrier = Z'.carrier ∧ ∀ ρ ∈ Z.carrier, Z.mult ρ = Z'.mult ρ := by
  refine eq_of_multDiff_eq_zero fun z₀ => ?_
  by_contra hc
  obtain ⟨f₀, hf₀, hblind, hsee⟩ := hiso z₀ hc
  exact hc (multDiff_eq_zero_of_isolated hZ hZ' ha hW hf₀ hblind hsee)

/-- **Clusters in a simple zero set do not cancel.** Mimics at aperture `a` whose cluster lies in
the simple zero set of the transform of one window of aperture `a` are equal. -/
theorem eq_of_mimic_of_simple_zeros {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {a : ℝ} (ha : 0 < a)
    (hW : ∀ f, ApertureWindow a f → Z.W f f = Z'.W f f) {f : ℝ → ℂ} (hf : ApertureWindow a f)
    (hzero : ∀ z, multDiff Z Z' z ≠ 0 → paperFT f (gammaOf z) = 0)
    (hsimple : ∀ z, multDiff Z Z' z ≠ 0 → deriv (paperFT f) (gammaOf z) ≠ 0) :
    Z.carrier = Z'.carrier ∧ ∀ ρ ∈ Z.carrier, Z.mult ρ = Z'.mult ρ := by
  set Λ : Set ℂ := gammaOf '' {z | multDiff Z Z' z ≠ 0} with hΛ
  refine eq_of_mimic_of_isolable hZ hZ' ha hW fun z₀ hz₀ => ?_
  obtain ⟨g, hg, hgΛ, hgκ⟩ := exists_isolating_window hf (Λ := Λ)
    (by rintro _ ⟨z, hz, rfl⟩; exact hzero z hz) ⟨z₀, hz₀, rfl⟩ (hsimple z₀ hz₀)
  exact ⟨g, hg, fun z hz hc => hgΛ _ ⟨z, hc, rfl⟩ fun h => hz (gammaOf_injective h), hgκ⟩

/-- **Lattice clusters do not cancel above the lattice aperture.** Mimics at an aperture
`a > π/h` whose cluster lies on the on-line lattice `{½ + ikh}` are equal. -/
theorem eq_of_mimic_of_onLine_lattice {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {h a : ℝ} (hh : 0 < h) (ha : Real.pi / h < a)
    (hW : ∀ f, ApertureWindow a f → Z.W f f = Z'.W f f)
    (hlat : ∀ z, multDiff Z Z' z ≠ 0 → ∃ k : ℤ, gammaOf z = (k : ℂ) * h) :
    Z.carrier = Z'.carrier ∧ ∀ ρ ∈ Z.carrier, Z.mult ρ = Z'.mult ρ := by
  have ha0 : 0 < a := (by positivity : 0 < Real.pi / h).trans ha
  refine eq_of_mimic_of_isolable hZ hZ' ha0 hW fun z₀ hz₀ => ?_
  obtain ⟨k₀, hk₀⟩ := hlat z₀ hz₀
  obtain ⟨g, hg, hgk, hgk₀⟩ := exists_window_isolating_lattice_point hh ha k₀
  refine ⟨g, hg, fun z hz hc => ?_, by rw [hk₀]; exact hgk₀⟩
  obtain ⟨k, hk⟩ := hlat z hc
  have hkk : k ≠ k₀ := fun hkk => hz (gammaOf_injective (by rw [hk, hk₀, hkk]))
  rw [hk]
  exact hgk k hkk

/-- **Isolating a point from perturbed lattices.** For finitely many bounded perturbations `ν_j` of
lattices of total density `D = Σ_j 1/h_j` and every aperture `r > πD`, each `z₀ ∈ ℂ` has a window
of aperture `r` that sees `z₀` and is blind to every `ν_j k ≠ z₀`. Every index hitting `z₀` is moved
off it by one unit, and the moved family is still a bounded perturbation. -/
theorem exists_window_isolating_in_perturbed_lattices {ι : Type*} [DecidableEq ι] (T : Finset ι)
    (h L : ι → ℝ) (hh : ∀ j ∈ T, 0 < h j) (ν : ι → ℤ → ℝ)
    (hν : ∀ j ∈ T, ∀ k : ℤ, |ν j k - k * h j| ≤ L j) {r : ℝ}
    (hr : Real.pi * ∑ j ∈ T, (h j)⁻¹ < r) (z₀ : ℂ) :
    ∃ f : ℝ → ℂ, ApertureWindow r f ∧
      (∀ j ∈ T, ∀ k, (ν j k : ℂ) ≠ z₀ → paperFT f (ν j k) = 0) ∧ paperFT f z₀ ≠ 0 := by
  classical
  set ν' : ι → ℤ → ℝ := fun j k => if (ν j k : ℂ) = z₀ then ν j k + 1 else ν j k with hν'
  have hν'b : ∀ j ∈ T, ∀ k : ℤ, |ν' j k - k * h j| ≤ L j + 1 := by
    intro j hj k
    have h0 := hν j hj k
    by_cases hk : (ν j k : ℂ) = z₀
    · simp only [hν', if_pos hk]
      calc |ν j k + 1 - k * h j| = |(ν j k - k * h j) + 1| := by congr 1; ring
        _ ≤ |ν j k - k * h j| + |(1 : ℝ)| := abs_add_le _ _
        _ ≤ L j + 1 := by rw [abs_one]; linarith
    · simp only [hν', if_neg hk]; linarith
  have hz₀' : ∀ j ∈ T, ∀ k, z₀ ≠ (ν' j k : ℂ) := by
    intro j _ k hk
    by_cases hkk : (ν j k : ℂ) = z₀
    · simp only [hν', if_pos hkk] at hk
      have := Complex.ofReal_injective (hkk.trans hk)
      linarith
    · simp only [hν', if_neg hkk] at hk
      exact hkk hk.symm
  obtain ⟨f, hf, hblind, hsee⟩ :=
    exists_window_blind_to_perturbed_lattices T h (fun j => L j + 1) hh ν' hν'b hr hz₀'
  refine ⟨f, hf, fun j hj k hk => ?_, hsee⟩
  have : ν' j k = ν j k := by simp only [hν', if_neg hk]
  rw [← this]
  exact hblind j hj k

/-- A window of any aperture `δ > 0` vanishing on a finite set `T` of frequencies and seeing a
frequency `w₀ ∉ T`: the transform is `∏_{t ∈ T} (−i(w − t)) b̂(w)` with `b̂(w₀) = 1`. -/
theorem exists_window_vanishing_on_finset {δ : ℝ} (hδ : 0 < δ) (T : Finset ℂ) {w₀ : ℂ}
    (hw₀ : w₀ ∉ T) :
    ∃ g : ℝ → ℂ, ApertureWindow δ g ∧ (∀ w ∈ T, paperFT g w = 0) ∧ paperFT g w₀ ≠ 0 := by
  obtain ⟨b, hb, hbc, hbs, hb1⟩ := exists_smooth_window_paperFT_eq_one hδ w₀
  obtain ⟨f, hf, hfs, hfw⟩ := exists_annihilating_window T hb hbc
  refine ⟨f, ⟨hf.of_le (by norm_cast), hfs.trans hbs⟩, fun w hw => ?_, ?_⟩
  · rw [hfw, Finset.prod_eq_zero hw (by ring), zero_mul]
  · rw [hfw, hb1, mul_one]
    exact Finset.prod_ne_zero_iff.mpr fun z hz =>
      mul_ne_zero (neg_ne_zero.mpr I_ne_zero) (sub_ne_zero.mpr fun h => hw₀ (h ▸ hz))

/-- **Isolation in thin sets.** Let `S` be a set of points whose ordinates lie on finitely many
bounded perturbations `{ν_j k}` of lattices of total density `D`, apart from a finite set `F`. For
every aperture `a > πD` each point `z₀` has a window of aperture `a` that sees `γ_{z₀}` and is
blind to every other point of `S`: the window blind to the lattices away from `γ_{z₀}` is convolved
with a window of small aperture vanishing on `γ(F) ∖ {γ_{z₀}}`. -/
theorem exists_isolating_window_of_lattices_and_finset {ι : Type*} [DecidableEq ι]
    (T : Finset ι) (h L : ι → ℝ) (hh : ∀ j ∈ T, 0 < h j) (ν : ι → ℤ → ℝ)
    (hν : ∀ j ∈ T, ∀ k : ℤ, |ν j k - k * h j| ≤ L j) {a : ℝ}
    (ha : Real.pi * ∑ j ∈ T, (h j)⁻¹ < a) (F : Finset ℂ) {S : Set ℂ}
    (hS : ∀ z ∈ S, (∃ j ∈ T, ∃ k : ℤ, gammaOf z = (ν j k : ℂ)) ∨ z ∈ F) (z₀ : ℂ) :
    ∃ f : ℝ → ℂ, ApertureWindow a f ∧ (∀ z ∈ S, z ≠ z₀ → paperFT f (gammaOf z) = 0) ∧
      paperFT f (gammaOf z₀) ≠ 0 := by
  classical
  set δ := (a - Real.pi * ∑ j ∈ T, (h j)⁻¹) / 2 with hδ
  have hδ0 : 0 < δ := by rw [hδ]; linarith
  obtain ⟨f₁, hf₁, hf₁lat, hf₁0⟩ := exists_window_isolating_in_perturbed_lattices T h L hh ν hν
    (r := a - δ) (by rw [hδ]; linarith) (gammaOf z₀)
  obtain ⟨g, hg, hgF, hg0⟩ := exists_window_vanishing_on_finset hδ0
    ((F.image gammaOf).erase (gammaOf z₀)) (Finset.notMem_erase _ _)
  obtain ⟨hw, hwt⟩ := apertureWindow_convolution hf₁ hg
  refine ⟨_, by rwa [sub_add_cancel] at hw, fun z hzS hz => ?_,
    by rw [hwt]; exact mul_ne_zero hf₁0 hg0⟩
  rw [hwt]
  rcases hS z hzS with ⟨j, hj, k, hk⟩ | hF
  · rw [hk, hf₁lat j hj k (by rw [← hk]; exact fun h' => hz (gammaOf_injective h')), zero_mul]
  · rw [hgF _ (Finset.mem_erase.mpr ⟨fun h' => hz (gammaOf_injective h'),
      Finset.mem_image_of_mem _ hF⟩), mul_zero]

/-- **Thin real backgrounds hide no tilted point.** Mimics at an aperture `a > π Σ_j 1/h_j` whose
cluster lies in the union of finitely many bounded perturbations `{ν_j k}` of lattices on the
critical line and a finite set `F` of arbitrary points, tilted or not, are equal. -/
theorem eq_of_mimic_of_perturbed_lattices_and_finset {ι : Type*} [DecidableEq ι]
    {Z Z' : ZeroConfig} (hZ : TemperedConfig Z) (hZ' : TemperedConfig Z') (T : Finset ι)
    (h L : ι → ℝ) (hh : ∀ j ∈ T, 0 < h j) (ν : ι → ℤ → ℝ)
    (hν : ∀ j ∈ T, ∀ k : ℤ, |ν j k - k * h j| ≤ L j) {a : ℝ}
    (ha : Real.pi * ∑ j ∈ T, (h j)⁻¹ < a) (hW : ∀ f, ApertureWindow a f → Z.W f f = Z'.W f f)
    (F : Finset ℂ)
    (hcl : ∀ z, multDiff Z Z' z ≠ 0 → (∃ j ∈ T, ∃ k : ℤ, gammaOf z = (ν j k : ℂ)) ∨ z ∈ F) :
    Z.carrier = Z'.carrier ∧ ∀ ρ ∈ Z.carrier, Z.mult ρ = Z'.mult ρ := by
  have hD0 : 0 ≤ Real.pi * ∑ j ∈ T, (h j)⁻¹ :=
    mul_nonneg Real.pi_pos.le (Finset.sum_nonneg fun j hj => (inv_pos.mpr (hh j hj)).le)
  refine eq_of_mimic_of_isolable hZ hZ' (lt_of_le_of_lt hD0 ha) hW fun z₀ _ => ?_
  obtain ⟨f, hf, hblind, hsee⟩ := exists_isolating_window_of_lattices_and_finset T h L hh ν hν ha F
    (S := {z | multDiff Z Z' z ≠ 0}) (fun z hz => hcl z hz) z₀
  exact ⟨f, hf, fun z hz hc => hblind z hc hz, hsee⟩

/-- **Clusters on finitely many perturbed lattices do not cancel above `πD`.** Mimics at an aperture
`a > π Σ_j 1/h_j` whose cluster lies on the critical line inside `⋃_j {ν_j k}`,
`|ν_j k − k h_j| ≤ L_j`, are equal. -/
theorem eq_of_mimic_of_perturbed_lattices {ι : Type*} [DecidableEq ι] {Z Z' : ZeroConfig}
    (hZ : TemperedConfig Z) (hZ' : TemperedConfig Z') (T : Finset ι) (h L : ι → ℝ)
    (hh : ∀ j ∈ T, 0 < h j) (ν : ι → ℤ → ℝ) (hν : ∀ j ∈ T, ∀ k : ℤ, |ν j k - k * h j| ≤ L j)
    {a : ℝ} (ha : Real.pi * ∑ j ∈ T, (h j)⁻¹ < a)
    (hW : ∀ f, ApertureWindow a f → Z.W f f = Z'.W f f)
    (hcl : ∀ z, multDiff Z Z' z ≠ 0 → ∃ j ∈ T, ∃ k : ℤ, gammaOf z = (ν j k : ℂ)) :
    Z.carrier = Z'.carrier ∧ ∀ ρ ∈ Z.carrier, Z.mult ρ = Z'.mult ρ :=
  eq_of_mimic_of_perturbed_lattices_and_finset hZ hZ' T h L hh ν hν ha hW ∅
    fun z hz => Or.inl (hcl z hz)

/-- **Clusters on a perturbed lattice do not cancel above `π/h`.** Mimics at an aperture `a > π/h`
whose cluster lies on the critical line inside `{ν_k}`, `|ν_k − kh| ≤ L`, are equal. -/
theorem eq_of_mimic_of_perturbed_lattice {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {h L a : ℝ} (hh : 0 < h) (ν : ℤ → ℝ)
    (hν : ∀ k : ℤ, |ν k - k * h| ≤ L) (ha : Real.pi / h < a)
    (hW : ∀ f, ApertureWindow a f → Z.W f f = Z'.W f f)
    (hcl : ∀ z, multDiff Z Z' z ≠ 0 → ∃ k : ℤ, gammaOf z = (ν k : ℂ)) :
    Z.carrier = Z'.carrier ∧ ∀ ρ ∈ Z.carrier, Z.mult ρ = Z'.mult ρ :=
  eq_of_mimic_of_perturbed_lattices hZ hZ' ({()} : Finset Unit) (fun _ => h) (fun _ => L)
    (fun _ _ => hh) (fun _ => ν) (fun _ _ => hν) (by simpa [div_eq_mul_inv] using ha) hW
    fun z hz => by
      obtain ⟨k, hk⟩ := hcl z hz
      exact ⟨(), Finset.mem_singleton_self _, k, hk⟩

end GaloisForLFunctions.ZeroConfigurationGeometry
