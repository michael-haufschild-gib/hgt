import GaloisForLFunctions.SquareRootThreshold.WindowedWeilFormSliceTransfer

/-!
# Window-averaged positivity holds for configurations with off-line zeros

The lattice configurations of `RHTower.ZeroLatticeDepthNyquistLaw` and the isolated-pair
configurations of `IsolatedOffLinePairVisibilityLaw` are tempered. Combined with the slice
transfer law, this gives the no-go theorems of the programme:

* **Dense off-line configurations.** For every depth `δ ∈ (0, ½]` and every window radius `r > 0`,
  the off-line lattice pair of spacing `2π/(2r)` has nonnegative windowed Weil forms, for windows
  supported in `[-r, r]` and tests of every aperture.
* **Isolated off-line zeros.** For every depth and window radius there is a doubled on-line
  lattice into which one reflected off-line pair can be inserted so that every such windowed form
  stays nonnegative. The background spacing only has to satisfy `sinh(2δr)/δ ≤ 2L + 2r` and
  `r ≤ L/2`.

Hence nonnegativity of height-window averages of the localized Weil forms at a fixed resolution
is compatible with off-line zeros of every depth. Window-averaged positivity cannot imply the
Riemann hypothesis.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 RHTower

/-! ### Lattices are tempered -/

theorem normSq_gammaOf_verticalLatticePoint (L δ : ℝ) (k : ℤ) :
    Complex.normSq (gammaOf (verticalLatticePoint L δ k)) = ((k : ℝ) * (2 * π / L)) ^ 2 + δ ^ 2 := by
  rw [gammaOf_verticalLatticePoint, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
    Complex.I_im, Complex.sub_im, Complex.mul_im]
  ring

/-- The inverse-square lattice weight is summable over `ℤ`. -/
theorem summable_lattice_weight {L : ℝ} (hL : 0 < L) (δ : ℝ) :
    Summable fun k : ℤ => 1 / (1 + Complex.normSq (gammaOf (verticalLatticePoint L δ k))) := by
  set c : ℝ := 2 * π / L with hc
  have hc0 : 0 < c := by positivity
  set m : ℝ := min 1 (c ^ 2) with hm
  have hm0 : 0 < m := lt_min one_pos (by positivity)
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    (RHTower.hasSum_inv_one_add_abs_sq.summable.mul_left (2 / m))
  · have := Complex.normSq_nonneg (gammaOf (verticalLatticePoint L δ k))
    positivity
  · rw [normSq_gammaOf_verticalLatticePoint, ← hc]
    set x : ℝ := (k : ℝ) with hx
    have h1 : m ≤ 1 := min_le_left _ _
    have h2 : m ≤ c ^ 2 := min_le_right _ _
    have hlow : m / 2 * (1 + |x|) ^ 2 ≤ 1 + (x * c) ^ 2 + δ ^ 2 := by
      have hsq : (1 + |x|) ^ 2 ≤ 2 * (1 + x ^ 2) := by
        nlinarith [sq_abs x, sq_nonneg (|x| - 1)]
      have hcx : m * x ^ 2 ≤ (x * c) ^ 2 := by
        rw [mul_pow]
        nlinarith [sq_nonneg x]
      nlinarith [sq_nonneg δ]
    have hpos : 0 < (1 + |x|) ^ 2 := by positivity
    have hden : 0 < 1 + ((x * c) ^ 2 + δ ^ 2) := by positivity
    rw [div_le_iff₀ hden]
    calc (1 : ℝ) = 2 / m * (1 / (1 + |x|) ^ 2) * (m / 2 * (1 + |x|) ^ 2) := by
          field_simp
      _ ≤ 2 / m * (1 / (1 + |x|) ^ 2) * (1 + ((x * c) ^ 2 + δ ^ 2)) := by
          gcongr
          linarith

theorem hasSum_lattice_weight {L : ℝ} (hL : 0 < L) (δ : ℝ) (c : ℝ) :
    ∃ a, HasSum (fun ρ : Set.range (verticalLatticePoint L δ) =>
      c / (1 + Complex.normSq (gammaOf ρ))) a := by
  obtain ⟨a, ha⟩ := (summable_lattice_weight hL δ).mul_left c
  refine ⟨a, ?_⟩
  rw [(verticalLatticePoint_injective hL δ).hasSum_range_iff (f := fun ρ : ℂ =>
    c / (1 + Complex.normSq (gammaOf ρ)))]
  have hfun : (fun ρ : ℂ => c / (1 + Complex.normSq (gammaOf ρ))) ∘ verticalLatticePoint L δ =
      fun k => c * (1 / (1 + Complex.normSq (gammaOf (verticalLatticePoint L δ k)))) := by
    funext k
    simp only [Function.comp_apply]
    ring
  rw [hfun]
  exact ha

theorem temperedConfig_onLineLatticeConfig {L : ℝ} (hL : 0 < L) :
    TemperedConfig (onLineLatticeConfig hL) := by
  obtain ⟨a, ha⟩ := hasSum_lattice_weight hL 0 2
  exact ⟨a, by simpa [onLineLatticeConfig] using ha⟩

theorem temperedConfig_offLineLatticeConfig {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) : TemperedConfig (offLineLatticeConfig hL hδ hδ') := by
  set G : ℂ → ℝ := fun ρ => ((offLineLatticeConfig hL hδ hδ').mult ρ : ℝ) /
    (1 + Complex.normSq (gammaOf ρ)) with hG
  obtain ⟨a, ha⟩ := hasSum_lattice_weight hL δ 1
  obtain ⟨b, hb⟩ := hasSum_lattice_weight hL (-δ) 1
  have hdisj : Disjoint (Set.range (verticalLatticePoint L δ))
      (Set.range (verticalLatticePoint L (-δ))) := by
    rw [Set.disjoint_left]
    rintro _ ⟨k, rfl⟩ ⟨k', hk'⟩
    have := congrArg Complex.re hk'
    simp only [verticalLatticePoint] at this
    linarith
  have ha' : HasSum (fun ρ : Set.range (verticalLatticePoint L δ) => G ρ) a := by
    simpa [hG, offLineLatticeConfig] using ha
  have hb' : HasSum (fun ρ : Set.range (verticalLatticePoint L (-δ)) => G ρ) b := by
    simpa [hG, offLineLatticeConfig] using hb
  exact ⟨a + b, HasSum.add_disjoint (f := G) hdisj ha' hb'⟩

theorem temperedConfig_isolatedPairConfig {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ) : TemperedConfig (isolatedPairConfig hL hδ hδ' γ₀) := by
  set Z := isolatedPairConfig hL hδ hδ' γ₀ with hZ
  set G : ℂ → ℝ := fun ρ => (Z.mult ρ : ℝ) / (1 + Complex.normSq (gammaOf ρ)) with hG
  obtain ⟨a, ha⟩ := hasSum_lattice_weight hL 0 2
  have hmult : ∀ ρ, Z.mult ρ = if ρ.re = 1 / 2 then 2 else 1 := fun _ => rfl
  have ha' : HasSum (fun ρ : Set.range (verticalLatticePoint L 0) => G ρ) a := by
    convert ha using 2 with ρ
    obtain ⟨_, k, rfl⟩ := ρ
    simp only [hG, hmult, verticalLatticePoint, add_zero, if_true, Nat.cast_ofNat]
  have hd₁ : Disjoint (Set.range (verticalLatticePoint L 0)) {offLinePoint δ γ₀} := by
    rw [Set.disjoint_singleton_right]
    rintro ⟨k, hk⟩
    have := congrArg Complex.re hk
    simp only [verticalLatticePoint, offLinePoint] at this
    linarith
  have hd₂ : Disjoint (Set.range (verticalLatticePoint L 0) ∪ {offLinePoint δ γ₀})
      {offLinePoint (-δ) γ₀} := by
    rw [Set.disjoint_singleton_right]
    rintro (⟨k, hk⟩ | hk)
    · have := congrArg Complex.re hk
      simp only [verticalLatticePoint, offLinePoint] at this
      linarith
    · rw [Set.mem_singleton_iff] at hk
      have := congrArg Complex.re hk
      simp only [offLinePoint] at this
      linarith
  exact ⟨_, HasSum.add_disjoint (f := G) hd₂
    (HasSum.add_disjoint (f := G) hd₁ ha' (hasSum_singleton _ G)) (hasSum_singleton _ G)⟩

/-! ### The no-go theorems -/

/-- Windowed positivity for the isolated pair below its visibility threshold, at every test
aperture. -/
theorem re_windowedW_isolatedPairConfig_nonneg {L δ : ℝ} (hL : 0 < L) (hδ : 0 < δ)
    (hδ' : δ ≤ 1 / 2) (γ₀ : ℝ) {a : ℝ} (ha : 0 < a) (haL : a ≤ L / 2)
    (hth : Real.sinh (2 * δ * a) / δ ≤ 2 * L + 2 * a) {f η : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) (hη : ContDiff ℝ 2 η) (hηs : tsupport η ⊆ Icc (-a) a) :
    0 ≤ (windowedW (isolatedPairConfig hL hδ hδ' γ₀) f η).re :=
  re_windowedW_nonneg_of_aperture_nonneg _ (temperedConfig_isolatedPairConfig hL hδ hδ' γ₀)
    ((isolatedPairConfig_weil_nonneg_iff hL hδ hδ' γ₀ ha haL).mpr hth) hf hfc hη hηs

/-- **Dense off-line configurations pass every window average.** For every depth `δ ∈ (0, ½]` and
every window radius `r > 0` there is a configuration with an off-line zero of depth `δ` whose
windowed Weil forms are nonnegative for every window supported in `[-r, r]` and every test of
arbitrary aperture. -/
theorem exists_offLine_lattice_windowed_nonneg {δ r : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hr : 0 < r) :
    ∃ Z : ZeroConfig, (∃ ρ ∈ Z.carrier, ρ.re = 1 / 2 + δ) ∧
      ∀ f η : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f → ContDiff ℝ 2 η →
        tsupport η ⊆ Icc (-r) r → 0 ≤ (windowedW Z f η).re := by
  have hL : (0 : ℝ) < 2 * r := by positivity
  refine ⟨offLineLatticeConfig hL hδ hδ', ⟨verticalLatticePoint (2 * r) δ 0,
    Or.inl ⟨0, rfl⟩, by simp [verticalLatticePoint]⟩, fun f η hf hfc hη hηs => ?_⟩
  exact re_windowedW_offLineLatticeConfig_nonneg hL hδ hδ' hf hfc hη
    (by rwa [show 2 * r / 2 = r by ring])

/-- **A single off-line pair passes every window average in a dense enough background.** For
every depth `δ ∈ (0, ½]`, every ordinate `γ₀` and every window radius `r > 0`, a doubled on-line
lattice of spacing `2π/L` with `L ≥ max (2r) (sinh(2δr)/(2δ))` keeps every windowed form with
window in `[-r, r]` nonnegative after the pair `½ ± δ + iγ₀` is inserted. -/
theorem exists_isolatedPair_windowed_nonneg {δ r : ℝ} (hδ : 0 < δ) (hδ' : δ ≤ 1 / 2)
    (hr : 0 < r) (γ₀ : ℝ) :
    ∃ L : ℝ, ∃ hL : 0 < L, offLinePoint δ γ₀ ∈ (isolatedPairConfig hL hδ hδ' γ₀).carrier ∧
      ∀ f η : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f → ContDiff ℝ 2 η →
        tsupport η ⊆ Icc (-r) r → 0 ≤ (windowedW (isolatedPairConfig hL hδ hδ' γ₀) f η).re := by
  set L : ℝ := max (2 * r) (Real.sinh (2 * δ * r) / (2 * δ)) with hLdef
  have hL : 0 < L := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  refine ⟨L, hL, Or.inl (Or.inr rfl), fun f η hf hfc hη hηs => ?_⟩
  refine re_windowedW_isolatedPairConfig_nonneg hL hδ hδ' γ₀ hr ?_ ?_ hf hfc hη hηs
  · have := le_max_left (2 * r) (Real.sinh (2 * δ * r) / (2 * δ))
    linarith
  · have h1 := le_max_right (2 * r) (Real.sinh (2 * δ * r) / (2 * δ))
    rw [div_le_iff₀ hδ]
    rw [div_le_iff₀ (by positivity)] at h1
    nlinarith

end GaloisForLFunctions.SquareRootThreshold
