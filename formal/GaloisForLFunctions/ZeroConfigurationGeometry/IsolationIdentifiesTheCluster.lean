import GaloisForLFunctions.ZeroConfigurationGeometry.FiniteModificationsAreSeenAtEveryAperture
import GaloisForLFunctions.ZeroConfigurationGeometry.IsolatingWindows

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
* **Simple zero sets** (`eq_of_mimic_of_simple_zeros`). If the cluster lies in the simple zero set of
  the transform of one window of aperture `a`, dividing at each point gives the isolating windows:
  mimics at aperture `a` never differ only on the simple zeros of one aperture-`a` transform.
* **Lattices** (`eq_of_mimic_of_onLine_lattice`). Mimics at an aperture `a > π/h` whose cluster lies on
  the on-line lattice `{½ + ikh}` are equal, whatever the multiplicities.

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

/-- The image difference is sesquilinear in the window. -/
theorem tsum_multDiff_pointImage_add_smul {Z Z' : ZeroConfig} (hZ : TemperedConfig Z)
    (hZ' : TemperedConfig Z') {f g : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f)
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (c : ℂ) :
    ∑' z, multDiff Z Z' z * pointImage (fun u => f u + c * g u) (fun u => f u + c * g u) z =
      ∑' z, multDiff Z Z' z * pointImage f f z + c * ∑' z, multDiff Z Z' z * pointImage g f z +
        conj c * ∑' z, multDiff Z Z' z * pointImage f g z +
          c * conj c * ∑' z, multDiff Z Z' z * pointImage g g z := by
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
  rw [tsum_congr hsum]
  rw [((hA.add (hB.mul_left c)).add (hC.mul_left (conj c))).tsum_add (hE.mul_left (c * conj c)),
    (hA.add (hB.mul_left c)).tsum_add (hC.mul_left (conj c)), hA.tsum_add (hB.mul_left c),
    tsum_mul_left, tsum_mul_left, tsum_mul_left]

/-- **Infinite polarization.** Mimics at aperture `a` have equal images on every pair of windows
of aperture `a`. -/
theorem W_eq_of_mimic {Z Z' : ZeroConfig} (hZ : TemperedConfig Z) (hZ' : TemperedConfig Z')
    {a : ℝ} (hW : ∀ f, ApertureWindow a f → Z.W f f = Z'.W f f) {f g : ℝ → ℂ}
    (hf : ApertureWindow a f) (hg : ApertureWindow a g) : Z.W f g = Z'.W f g := by
  set D : (ℝ → ℂ) → (ℝ → ℂ) → ℂ := fun f g => ∑' z, multDiff Z Z' z * pointImage f g z with hD
  have hdiag : ∀ f, ApertureWindow a f → D f f = 0 := fun f hf => by
    show (∑' z, multDiff Z Z' z * pointImage f f z) = 0
    rw [← W_sub_W_eq_tsum hZ hZ' hf.1 hf.hasCompactSupport hf.1 hf.hasCompactSupport,
      hW f hf, sub_self]
  have hfc := hf.hasCompactSupport
  have hgc := hg.hasCompactSupport
  have e1 := tsum_multDiff_pointImage_add_smul hZ hZ' hf.1 hfc hg.1 hgc 1
  have eI := tsum_multDiff_pointImage_add_smul hZ hZ' hf.1 hfc hg.1 hgc I
  rw [show (∑' z, multDiff Z Z' z * pointImage (fun u => f u + 1 * g u) (fun u => f u + 1 * g u) z)
      = D (fun u => f u + 1 * g u) (fun u => f u + 1 * g u) from rfl,
    hdiag _ (hf.add_smul hg 1)] at e1
  rw [show (∑' z, multDiff Z Z' z * pointImage (fun u => f u + I * g u) (fun u => f u + I * g u) z)
      = D (fun u => f u + I * g u) (fun u => f u + I * g u) from rfl,
    hdiag _ (hf.add_smul hg I)] at eI
  have hff : D f f = 0 := hdiag f hf
  have hgg : D g g = 0 := hdiag g hg
  change 0 = D f f + 1 * D g f + conj 1 * D f g + 1 * conj 1 * D g g at e1
  change 0 = D f f + I * D g f + conj I * D f g + I * conj I * D g g at eI
  rw [hff, hgg] at e1 eI
  simp only [map_one, Complex.conj_I, zero_add, add_zero, one_mul, mul_zero] at e1 eI
  have h2 : D g f - D f g = 0 := by
    have : I * (D g f - D f g) = 0 := by linear_combination -eI
    exact (mul_eq_zero.mp this).resolve_left Complex.I_ne_zero
  have hfg : D f g = 0 := by linear_combination (-1 / 2 : ℂ) * e1 - (1 / 2 : ℂ) * h2
  have h := W_sub_W_eq_tsum hZ hZ' hf.1 hfc hg.1 hgc
  rw [show (∑' z, multDiff Z Z' z * pointImage f g z) = D f g from rfl, hfg] at h
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

theorem gammaOf_injective : Function.Injective gammaOf := fun z w h => by
  have h' : (z - 1 / 2) / I = (w - 1 / 2) / I := h
  rw [div_left_inj' Complex.I_ne_zero] at h'
  linear_combination h'

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

end GaloisForLFunctions.ZeroConfigurationGeometry
