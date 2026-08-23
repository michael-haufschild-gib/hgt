import GaloisForLFunctions.RHTower.MellinContinuationOrder
import GaloisForLFunctions.RHTower.MellinTrivialZeros
import GaloisForLFunctions.RHTower.SoninEntireMellin
import GaloisForLFunctions.RHTower.BurnolPowerLineShift
import GaloisForLFunctions.RHTower.BurnolRectangleResidue

/-!
# The Mellin transform of a genuine Sonine vector at `0` and at `1`

For a vector of the *extended* Sonine space the continued Mellin transform is analytic at `0` and
has at worst a simple pole at `1`.  When both aperture constants vanish — that is, on the Sonine
space `K_a` itself — both statements improve by one:

* at `s = 1` the residue is the physical aperture constant, so the transform is analytic there;
* at `s = 0` the left branch of the numerator is `(1 − s)·χ(s)·s·T(1 − s)`, and `χ(0) = 0`, so the
  numerator vanishes to order two and the transform vanishes.

These are exactly the two facts that let one divide by `s(s − 1)` in Burnol's Proposition 6.5.

## Main results

* `two_le_analyticOrderAt_extendedMellinNumerator_zero`
* `one_le_meromorphicOrderAt_extendedMellinContinuation_zero`
* `zero_le_meromorphicOrderAt_extendedMellinContinuation_one`
-/

open Complex Set Topology Filter MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

theorem burnolChiFactor_zero : burnolChiFactor 0 = 0 := by
  have h := burnolChiFactor_neg_two_mul_nat 0
  simpa using h

theorem analyticAt_burnolChiFactor_zero : AnalyticAt ℂ burnolChiFactor 0 := by
  refine DifferentiableOn.analyticAt (s := {v : ℂ | v.re < 1}) ?_ ?_
  · intro s hs
    exact (differentiableAt_burnolChiFactor hs).differentiableWithinAt
  · refine (isOpen_lt Complex.continuous_re continuous_const).mem_nhds ?_
    simp

/-- **The numerator vanishes to order two at the origin** when the cosine-side aperture constant is
zero: the left branch is `(1 − s)·χ(s)·(s·T(1 − s))`, and both factors vanish at `0`. -/
theorem two_le_analyticOrderAt_extendedMellinNumerator_zero {a : ℝ} (ha : 0 < a) {f : SoninL2}
    {d : ℂ} (hev : f ∈ evenSubspace)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d) :
    ((2 : ℕ) : ℕ∞) ≤ analyticOrderAt (extendedMellinNumerator a 0 d f) 0 := by
  have hff : fourierUnitary (fourierUnitary f) = f :=
    fourierUnitary_fourierUnitary_of_mem_evenSubspace hev
  have hdF : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary (fourierUnitary f) : SoninL2) : ℝ → ℂ) u = d := by
    rw [hff]; exact hd
  set A : ℂ → ℂ := fun s : ℂ => (1 - s) * burnolChiFactor s with hAdef
  set B : ℂ → ℂ := fun s : ℂ => s * extendedTailMellin a d (fourierUnitary f) (1 - s) with hBdef
  have hA : AnalyticAt ℂ A 0 :=
    (analyticAt_const.sub analyticAt_id).mul analyticAt_burnolChiFactor_zero
  have hB : AnalyticAt ℂ B 0 := by
    have hopen1 : IsOpen {v : ℂ | v.re < 1} := isOpen_lt Complex.continuous_re continuous_const
    have hopen : IsOpen {v : ℂ | 0 < v.re} := isOpen_lt continuous_const Complex.continuous_re
    refine DifferentiableOn.analyticAt (s := {v : ℂ | v.re < 1}) ?_ (hopen1.mem_nhds (by simp))
    intro s hs
    have hs1 : s.re < 1 := hs
    refine DifferentiableAt.differentiableWithinAt ?_
    have hre : (0 : ℝ) < ((1 : ℂ) - s).re := by
      simp only [Complex.sub_re, Complex.one_re]
      linarith
    have hbase : DifferentiableAt ℂ (extendedTailMellin a d (fourierUnitary f)) ((1 : ℂ) - s) :=
      (differentiableOn_extendedTailMellin ha hdF).differentiableAt (hopen.mem_nhds hre)
    have hsub : DifferentiableAt ℂ (fun z : ℂ => 1 - z) s :=
      (differentiableAt_const (1 : ℂ)).sub differentiableAt_id
    have htail : DifferentiableAt ℂ
        (fun z : ℂ => extendedTailMellin a d (fourierUnitary f) (1 - z)) s := by
      simpa [Function.comp_def] using hbase.comp s hsub
    rw [hBdef]
    exact differentiableAt_id.mul htail
  have hfac : extendedMellinNumerator a 0 d f =ᶠ[𝓝 (0 : ℂ)] A * B := by
    have hopen : IsOpen {v : ℂ | v.re < 1 / 2} :=
      isOpen_lt Complex.continuous_re continuous_const
    have hmem : (0 : ℂ) ∈ {v : ℂ | v.re < 1 / 2} := by simp
    filter_upwards [hopen.eventually_mem hmem] with s hs
    rw [extendedMellinNumerator_eq_left a 0 d f hs, extendedMellinNumeratorLeft]
    show _ = A s * B s
    rw [hAdef, hBdef]
    ring
  rw [analyticOrderAt_congr hfac, analyticOrderAt_mul hA hB]
  have hA1 : (1 : ℕ∞) ≤ analyticOrderAt A 0 := by
    rw [Order.one_le_iff_ne_zero, Ne, hA.analyticOrderAt_eq_zero]
    simp [hAdef, burnolChiFactor_zero]
  have hB1 : (1 : ℕ∞) ≤ analyticOrderAt B 0 := by
    rw [Order.one_le_iff_ne_zero, Ne, hB.analyticOrderAt_eq_zero]
    simp [hBdef]
  refine le_trans ?_ (add_le_add hA1 hB1)
  norm_num

/-- **The transform of a Sonine vector vanishes at the origin.** -/
theorem one_le_meromorphicOrderAt_extendedMellinContinuation_zero {a : ℝ} (ha : 0 < a)
    {f : SoninL2} {d : ℂ} (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = 0)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = d) :
    ((1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (extendedMellinContinuation a 0 d f) 0 := by
  have hana : AnalyticAt ℂ (extendedMellinNumerator a 0 d f) 0 :=
    analyticAt_extendedMellinNumerator ha hev hc hd 0
  have h2 := two_le_analyticOrderAt_extendedMellinNumerator_zero ha hev hd
  have hN : ((2 : ℤ) : WithTop ℤ)
      ≤ meromorphicOrderAt (extendedMellinNumerator a 0 d f) 0 := by
    rw [hana.meromorphicOrderAt_eq]
    induction hx : analyticOrderAt (extendedMellinNumerator a 0 d f) 0 with
    | top => simp
    | coe n =>
        rw [hx] at h2
        have hn : (2 : ℕ) ≤ n := by exact_mod_cast h2
        have h2' : (2 : ℤ) ≤ (n : ℤ) := by exact_mod_cast hn
        simpa using h2'
  rw [meromorphicOrderAt_extendedMellinContinuation ha hev hc hd,
    meromorphicOrderAt_mellinDenominator_zero]
  induction hx : meromorphicOrderAt (extendedMellinNumerator a 0 d f) 0 with
  | top => simp
  | coe n =>
      rw [hx] at hN
      have hn : (2 : ℤ) ≤ n := by exact_mod_cast hN
      have h1 : (1 : ℤ) ≤ n - 1 := by omega
      exact_mod_cast h1

/-- **The transform of a Sonine vector is regular at `s = 1`.** -/
theorem zero_le_meromorphicOrderAt_extendedMellinContinuation_one {a : ℝ} (ha : 0 < a)
    {f : SoninL2} {c : ℂ} (hev : f ∈ evenSubspace)
    (hc : ∀ᵐ u ∂(volume : Measure ℝ), u ∈ centralInterval a →
      ((fourierUnitary f : SoninL2) : ℝ → ℂ) u = c)
    (hd : ∀ᵐ t ∂(volume : Measure ℝ), t ∈ centralInterval a → (f : ℝ → ℂ) t = 0) :
    ((0 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt (extendedMellinContinuation a c 0 f) 1 := by
  have hN : ((1 : ℤ) : WithTop ℤ)
      ≤ meromorphicOrderAt (extendedMellinNumerator a c 0 f) 1 :=
    one_le_meromorphicOrderAt_of_eq_zero (analyticAt_extendedMellinNumerator ha hev hc hd 1)
      (extendedMellinNumerator_one ha c 0 f)
  rw [meromorphicOrderAt_extendedMellinContinuation ha hev hc hd,
    meromorphicOrderAt_mellinDenominator_one]
  induction hx : meromorphicOrderAt (extendedMellinNumerator a c 0 f) 1 with
  | top => simp
  | coe n =>
      rw [hx] at hN
      have hn : (1 : ℤ) ≤ n := by exact_mod_cast hN
      have h0 : (0 : ℤ) ≤ n - 1 := by omega
      exact_mod_cast h0

end

end RHTower
