import GaloisForLFunctions.ZeroConfigurationGeometry.IsolationIdentifiesTheCluster
import GaloisForLFunctions.ZeroConfigurationGeometry.EulerColumnsAreSeenJustAboveTheirPrime

/-!
# Positivity certifies isolable tilts

Weil's criterion read through the camera. The image of a configuration on the diagonal window pair
is `W_Z(f, f) = Σ_ρ m_ρ f̂(γ_ρ) conj f̂(conj γ_ρ)`. A point on the critical line has a real `γ_ρ`
and contributes `m_ρ |f̂(γ_ρ)|² ≥ 0`. A point `ρ` off the line pairs with its partner `1 − ρ̄`,
whose ordinate is `conj γ_ρ` (`gammaOf_reflect_eq_conj`), into
`2 m_ρ Re(f̂(γ_ρ) conj f̂(conj γ_ρ))`, which has no sign.

* **An isolated tilt makes the image negative** (`exists_window_re_W_neg`). If `ρ₀` is off the
  line and both `ρ₀` and `1 − ρ̄₀` have windows of aperture `a` isolating them in the carrier,
  the combination `f = f_A + c f_B` with `f̂(conj γ₀) = −f̂(γ₀)` has
  `W_Z(f, f) = −2 m_{ρ₀} |f̂(γ₀)|² < 0`. No temperedness is used: the image is a finite sum.
* **Positivity certifies what the camera isolates** (`re_eq_half_of_re_W_nonneg`). If
  `Re W_Z(f, f) ≥ 0` on every window of aperture `a`, every point of `Z` that windows of
  aperture `a` isolate, together with its partner, lies on the critical line.
* **Thin configurations** (`re_eq_half_of_re_W_nonneg_of_lattices_and_finset`). If the carrier lies
  on finitely many bounded perturbations of lattices on the line, of total density `D`, apart from
  finitely many arbitrary points, positivity at a single aperture `a > πD` puts every point on
  the line; a finite configuration is put on the line by positivity at any one aperture
  (`re_eq_half_of_re_W_nonneg_of_finite`).

* **Positivity has a density threshold** (`offLineLattice_re_W_nonneg`). The off-line lattice
  `{½ ± δ + 2πik/L}`, with `L/π` points per unit height, is positive on every window of aperture
  `≤ L/2` although no point of it is on the line. A single aperture `a` can therefore certify at
  best configurations of height density `< 2a/π`.

For `ζ`, positivity at every aperture is RH (Weil). The camera reading locates the difficulty:
the ordinates of `ζ` have unbounded density, no window of finite aperture is blind to them
(`eq_zero_of_blind_to_real_zeros_of_xi`), so no aperture isolates a tilt among them, and
positivity has to be used at all apertures at once.
-/

open MeasureTheory Complex Set
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.ZeroConfigurationGeometry

open Zeta23 SquareRootThreshold

/-- The partner `1 − ρ̄` of `ρ` has the conjugate ordinate. -/
theorem gammaOf_reflect_eq_conj (ρ : ℂ) : gammaOf (reflect ρ) = conj (gammaOf ρ) := by
  apply Complex.ext <;> simp [gammaOf, reflect, Complex.div_re, Complex.div_im]

/-- An image whose transform vanishes off a finite set is a finite sum. -/
theorem W_eq_sum_of_support (Z : ZeroConfig) {f g : ℝ → ℂ} (S : Finset ℂ)
    (hS : ∀ z ∈ Z.carrier, z ∉ S → pointImage f g z = 0) :
    Z.W f g = ∑ z ∈ S, Z.carrier.indicator (fun z => (Z.mult z : ℂ)) z * pointImage f g z := by
  rw [W_eq_tsum_indicator]
  exact tsum_eq_sum fun z hz => by
    by_cases hc : z ∈ Z.carrier
    · rw [hS z hc hz, mul_zero]
    · rw [Set.indicator_of_notMem hc, zero_mul]

/-- **An isolated tilt makes the image negative.** -/
theorem exists_window_re_W_neg {Z : ZeroConfig} {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier)
    (hoff : ρ₀.re ≠ 1 / 2) {a : ℝ} {fA fB : ℝ → ℂ} (hfA : ApertureWindow a fA)
    (hfB : ApertureWindow a fB) (hA : ∀ z ∈ Z.carrier, z ≠ ρ₀ → paperFT fA (gammaOf z) = 0)
    (hA0 : paperFT fA (gammaOf ρ₀) ≠ 0)
    (hB : ∀ z ∈ Z.carrier, z ≠ reflect ρ₀ → paperFT fB (gammaOf z) = 0)
    (hB0 : paperFT fB (gammaOf (reflect ρ₀)) ≠ 0) :
    ∃ f : ℝ → ℂ, ApertureWindow a f ∧ (Z.W f f).re < 0 := by
  classical
  set u := paperFT fA (gammaOf ρ₀) with hu
  set c := -u / paperFT fB (gammaOf (reflect ρ₀)) with hc
  have hf : ApertureWindow a fun t => fA t + c * fB t := hfA.add_smul hfB c
  have hft : ∀ w, paperFT (fun t => fA t + c * fB t) w = paperFT fA w + c * paperFT fB w :=
    paperFT_add_smul hfA.1.continuous hfA.hasCompactSupport hfB.1.continuous
      hfB.hasCompactSupport c
  have hρ₁ : reflect ρ₀ ∈ Z.carrier := Z.reflect_mem ρ₀ hρ₀
  have hne : reflect ρ₀ ≠ ρ₀ := fun h => hoff (by
    have := congrArg Complex.re h
    simp only [reflect, Complex.sub_re, Complex.one_re, Complex.conj_re] at this
    linarith)
  have v0 : paperFT (fun t => fA t + c * fB t) (gammaOf ρ₀) = u := by
    rw [hft, hB ρ₀ hρ₀ hne.symm, mul_zero, add_zero]
  have v1 : paperFT (fun t => fA t + c * fB t) (gammaOf (reflect ρ₀)) = -u := by
    rw [hft, hA _ hρ₁ hne, zero_add, hc, div_mul_cancel₀ _ hB0]
  have hS : ∀ z ∈ Z.carrier, z ∉ ({ρ₀, reflect ρ₀} : Finset ℂ) →
      pointImage (fun t => fA t + c * fB t) (fun t => fA t + c * fB t) z = 0 := by
    intro z hz hzS
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hzS
    rw [pointImage, hft, hA z hz hzS.1, hB z hz hzS.2, mul_zero, add_zero, zero_mul]
  have p0 : pointImage (fun t => fA t + c * fB t) (fun t => fA t + c * fB t) ρ₀ =
      -(u * conj u) := by
    rw [pointImage, v0, ← gammaOf_reflect_eq_conj, v1, map_neg, mul_neg]
  have p1 : pointImage (fun t => fA t + c * fB t) (fun t => fA t + c * fB t) (reflect ρ₀) =
      -(u * conj u) := by
    rw [pointImage, v1, gammaOf_reflect_eq_conj, Complex.conj_conj, v0]
    ring
  refine ⟨_, hf, ?_⟩
  rw [W_eq_sum_of_support Z _ hS, Finset.sum_pair hne.symm, Set.indicator_of_mem hρ₀,
    Set.indicator_of_mem hρ₁, Z.mult_reflect ρ₀ hρ₀, p0, p1, Complex.mul_conj]
  have hpos : 0 < Complex.normSq u := Complex.normSq_pos.mpr hA0
  have hm : (1 : ℝ) ≤ Z.mult ρ₀ := by exact_mod_cast Z.one_le_mult ρ₀ hρ₀
  have e : ((Z.mult ρ₀ : ℂ) * -((Complex.normSq u : ℝ) : ℂ) +
      (Z.mult ρ₀ : ℂ) * -((Complex.normSq u : ℝ) : ℂ)) =
      ((-(2 * (Z.mult ρ₀ : ℝ) * Complex.normSq u) : ℝ) : ℂ) := by push_cast; ring
  rw [e, Complex.ofReal_re]
  nlinarith

/-- **Positivity certifies what the camera isolates.** If `Re W_Z(f, f) ≥ 0` for every window of
aperture `a`, a point `ρ₀` of `Z` lies on the critical line as soon as `ρ₀` and its partner
`1 − ρ̄₀` each have a window of aperture `a` isolating them in the carrier. -/
theorem re_eq_half_of_re_W_nonneg {Z : ZeroConfig} {a : ℝ}
    (hpos : ∀ f, ApertureWindow a f → 0 ≤ (Z.W f f).re) {ρ₀ : ℂ} (hρ₀ : ρ₀ ∈ Z.carrier)
    (hiso : ∀ z₀ ∈ ({ρ₀, reflect ρ₀} : Set ℂ), ∃ f : ℝ → ℂ, ApertureWindow a f ∧
      (∀ z ∈ Z.carrier, z ≠ z₀ → paperFT f (gammaOf z) = 0) ∧ paperFT f (gammaOf z₀) ≠ 0) :
    ρ₀.re = 1 / 2 := by
  by_contra hoff
  obtain ⟨fA, hfA, hA, hA0⟩ := hiso ρ₀ (Set.mem_insert _ _)
  obtain ⟨fB, hfB, hB, hB0⟩ := hiso (reflect ρ₀) (Set.mem_insert_of_mem _ rfl)
  obtain ⟨f, hf, hneg⟩ := exists_window_re_W_neg hρ₀ hoff hfA hfB hA hA0 hB hB0
  exact absurd (hpos f hf) (not_le.mpr hneg)

/-- **Positivity at one aperture puts a thin configuration on the line.** If the ordinates of the
carrier lie on finitely many bounded perturbations `{ν_j k}` of lattices of total density
`D = Σ_j 1/h_j`, apart from a finite set `F`, and `Re W_Z(f, f) ≥ 0` for every window of one
aperture `a > πD`, every point of `Z` lies on the critical line. -/
theorem re_eq_half_of_re_W_nonneg_of_lattices_and_finset {ι : Type*} [DecidableEq ι]
    {Z : ZeroConfig} (T : Finset ι) (h L : ι → ℝ) (hh : ∀ j ∈ T, 0 < h j) (ν : ι → ℤ → ℝ)
    (hν : ∀ j ∈ T, ∀ k : ℤ, |ν j k - k * h j| ≤ L j) {a : ℝ}
    (ha : Real.pi * ∑ j ∈ T, (h j)⁻¹ < a) (F : Finset ℂ)
    (hS : ∀ z ∈ Z.carrier, (∃ j ∈ T, ∃ k : ℤ, gammaOf z = (ν j k : ℂ)) ∨ z ∈ F)
    (hpos : ∀ f, ApertureWindow a f → 0 ≤ (Z.W f f).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 := fun ρ hρ =>
  re_eq_half_of_re_W_nonneg hpos hρ fun z₀ _ =>
    exists_isolating_window_of_lattices_and_finset T h L hh ν hν ha F hS z₀

/-- **Finite configurations: positivity at any single aperture.** A configuration with finitely
many points and `Re W_Z(f, f) ≥ 0` on every window of one aperture `a > 0` lies on the critical
line. -/
theorem re_eq_half_of_re_W_nonneg_of_finite {Z : ZeroConfig} (F : Finset ℂ) (hF : Z.carrier ⊆ F)
    {a : ℝ} (ha : 0 < a) (hpos : ∀ f, ApertureWindow a f → 0 ≤ (Z.W f f).re) :
    ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2 :=
  re_eq_half_of_re_W_nonneg_of_lattices_and_finset (∅ : Finset Unit) (fun _ => 1) (fun _ => 0)
    (by simp) (fun _ _ => 0) (by simp) (by simpa using ha) F (fun z hz => Or.inr (hF hz)) hpos

/-! ### Positivity has a density threshold -/

/-- A configuration on the critical line has a nonnegative image: each point contributes
`m_ρ |f̂(γ_ρ)|²`. -/
theorem re_W_nonneg_of_onLine (Z : ZeroConfig) (hZ : ∀ ρ ∈ Z.carrier, ρ.re = 1 / 2)
    (f : ℝ → ℂ) : 0 ≤ (Z.W f f).re := by
  have hterm : ∀ z, Z.carrier.indicator (fun z => (Z.mult z : ℂ)) z * pointImage f f z =
      (((Z.carrier.indicator (fun z => (Z.mult z : ℝ)) z) * Complex.normSq (paperFT f (gammaOf z))
        : ℝ) : ℂ) := by
    intro z
    by_cases hz : z ∈ Z.carrier
    · have hγ : conj (gammaOf z) = gammaOf z := by
        rw [Complex.conj_eq_iff_im]
        simp [gammaOf, Complex.div_im, hZ z hz]
      rw [Set.indicator_of_mem hz, Set.indicator_of_mem hz, pointImage, hγ, Complex.mul_conj]
      push_cast; ring
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem hz]; simp
  rw [W_eq_tsum_indicator, tsum_congr hterm]
  by_cases hs : Summable fun z => Z.carrier.indicator (fun z => (Z.mult z : ℝ)) z *
      Complex.normSq (paperFT f (gammaOf z))
  · rw [← Complex.ofReal_tsum, Complex.ofReal_re]
    exact tsum_nonneg fun z => mul_nonneg
      (Set.indicator_nonneg (fun _ _ => Nat.cast_nonneg _) z) (Complex.normSq_nonneg _)
  · rw [← Complex.ofReal_tsum, tsum_eq_zero_of_not_summable hs, Complex.ofReal_zero,
      Complex.zero_re]

/-- **Positivity has a density threshold.** The off-line lattice
`{½ ± δ + 2πik/L}`, whose ordinates have `L/π` points per unit height, has `Re W(f, f) ≥ 0` on every
window of aperture `a ≤ L/2`, and none of its points lies on the critical line: below that
aperture it has the image of the doubled on-line lattice (`offLineLattice_mimic_iff`). -/
theorem offLineLattice_re_W_nonneg {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2) {a : ℝ}
    (ha : a ≤ L / 2) :
    (∀ f, ApertureWindow a f → 0 ≤ ((offLineLatticeConfig hL hδ hδ').W f f).re) ∧
      ∀ ρ ∈ (offLineLatticeConfig hL hδ hδ').carrier, ρ.re ≠ 1 / 2 := by
  refine ⟨fun f hf => ?_, ?_⟩
  · rw [(offLineLattice_mimic_iff hL hδ hδ' a).mpr ha f hf]
    refine re_W_nonneg_of_onLine _ (fun ρ hρ => ?_) f
    obtain ⟨k, rfl⟩ := hρ
    simp [_root_.RHTower.verticalLatticePoint]
  · rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩) h <;>
      simp only [_root_.RHTower.verticalLatticePoint] at h <;> linarith

end GaloisForLFunctions.ZeroConfigurationGeometry
