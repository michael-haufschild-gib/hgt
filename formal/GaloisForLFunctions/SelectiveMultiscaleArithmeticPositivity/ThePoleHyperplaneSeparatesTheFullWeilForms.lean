import GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity.ThePoleHyperplaneIsTheHarmonicHyperplane
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.ThePoleHyperplaneSeparatesZetaFromItsLiouvilleTwin
import GaloisForLFunctions.ArithmeticLorentzianGeometry.HyperbolicityIsBlindTheSignIsNot

/-!
# The pole hyperplane separates the full Weil forms

Every positivity that the corpus proves on atomic tests is shared by the sign twins of `ζ`: the
stability law is gauge blind, the narrow Hodge index holds for the Liouville twin, and on the
positive cone `ζ` is even the minimum of its gauge orbit (ArithmeticElectrostatics). The pole
hyperplane `Σ_{n ≤ N} x_n/√n = 0` is where this changes. There the pole term vanishes
(`ThePoleHyperplaneIsTheHarmonicHyperplane`), the prime form of `ζ` has a uniform gap below its
ceiling, and the Liouville twin's prime form reaches the ceiling
(RenormalizedArithmeticPotentialTheory).

* **The gap pays on the hyperplane** (`exists_weilQuad_atomicTest_ge_of_harmonic`): eventually in
  `N`, at narrow widths, every atomic test on the hyperplane has
  `W(f) ≥ (φ₀ + c₀ G)‖f‖²`, where `φ₀` is the finite part of the Markov form and `c₀` the
  retained fraction of the prime defect. The gap `G` is added to the finite part, with no pole cost.
* **The Liouville twin falls below `ζ`** (`exists_liouville_weilQuad_add_le_of_harmonic`): for every
  `ε > 0`, eventually in `N` there is a nonzero `x` on the hyperplane such that for *every* narrow
  atom profile the full Weil forms satisfy `W_λ(f_x) + (G − 2ε)‖f_x‖² ≤ W(f_x)`.
* **Selective separation** (`exists_pole_hyperplane_separates_full_weil_forms`,
  `exists_liouville_weilQuad_lt_of_harmonic`): one constant `G > 0` does both. On the positive cone
  `ζ` is the minimum of its gauge orbit; on the pole hyperplane its Liouville twin lies strictly
  below it, by a margin uniform in `N`.

Both statements keep the archimedean term and both pole moments. The separation is a property of
the full forms, carried by the prime gap that `Λ` has and its Liouville twin lacks.
-/

noncomputable section

open MeasureTheory Finset RHTower

namespace GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.ArithmeticLorentzianGeometry
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

local notation "γ" => Real.eulerMascheroniConstant

/-- The finite part `φ₀` of the Markov form at width `w` and window `N` (profile `φ`, slack `ε`). -/
def markovFinitePart (φ : ℝ → ℝ) (ε w : ℝ) (N : ℕ) : ℝ :=
  2 * gammaHardyPhaseRate 0 + Real.log (1 / (w * N)) + profileRobin φ + γ - ε -
    Real.exp (1 / 2) / 2 * w - markovCrossConstant * (w * N)

/-- The retained fraction `c₀` of the prime defect at width `w` and window `N`. -/
def defectFractionRetained (ε w : ℝ) (N : ℕ) : ℝ := 1 - ε - 32 * Real.exp 2 * (w * N)

/-- **The gap pays on the harmonic hyperplane.** There is `G > 0` such that, for every admissible
profile and slack, eventually in `N` every atomic test of width `w ≤ δ_N/2` on the hyperplane
`Σ x_n/√n = 0` has `W(f) ≥ (φ₀ + c₀ G)‖f‖²` whenever the retained defect fraction is nonnegative. -/
theorem exists_weilQuad_atomicTest_ge_of_harmonic :
    ∃ G : ℝ, 0 < G ∧ ∀ {φ : ℝ → ℝ}, ContDiff ℝ 2 φ → (∀ u, u ∉ Set.Icc 0 1 → φ u = 0) →
      0 < (∫ u, φ u ^ 2) → ∀ {K : ℝ}, (∀ u v, |φ u - φ v| ≤ K * |u - v|) →
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 2 →
      ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : ℝ, 0 < w → w ≤ atomSpacing N / 2 →
        w * N ≤ markovOverlapBound → 0 ≤ defectFractionRetained ε w N →
        ∀ x : ℕ → ℝ, ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 →
          (markovFinitePart φ ε w N + defectFractionRetained ε w N * G) *
              (∫ u, atomicTest N x (atomDilate φ w) u ^ 2) ≤
            weilQuad (atomicTest N x (atomDilate φ w)) := by
  obtain ⟨G, hG, hgap⟩ := exists_poleDefect_ge
  refine ⟨G, hG, fun {φ} hφ hφsupp hφ0 {K} hK {ε} hε hε1 => ?_⟩
  obtain ⟨N₀, hN₀⟩ := eventually_markovEnergy_ge_defect hφ hφsupp hφ0 hK hε hε1
  refine ⟨max N₀ 1, fun N hN w hw0 hw hwN hc₀ x hx => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hM := hN₀ N (le_trans (le_max_left _ _) hN) w hw0 hw hwN x
  obtain ⟨hgc2, hgsupp, hgc⟩ := atomDilate_facts hφ hφsupp hw0
  have hw' : w < atomSpacing N := by linarith [atomSpacing_pos hN1]
  rw [weilQuad_atomicTest_eq_markov_of_harmonic hgc2 hgsupp N hx]
  rw [integral_atomicTest_sq hgc2 hgc hgsupp hw' x] at hM ⊢
  unfold markovFinitePart defectFractionRetained at *
  set A := ∫ u, atomDilate φ w u ^ 2
  set c₀ := 1 - ε - 32 * Real.exp 2 * (w * N)
  have hA : 0 ≤ A := integral_nonneg fun _ => sq_nonneg _
  -- the gap: `D_N(x) ≥ G Σ x_n²` on the hyperplane, kept with the factor `A c₀ ≥ 0`
  have h1 : A * c₀ * (G * ∑ n ∈ Icc 1 N, x n ^ 2) ≤ A * c₀ * poleDefect N x :=
    mul_le_mul_of_nonneg_left (hgap N x hx) (mul_nonneg hA hc₀)
  nlinarith

/-- **Gap-paid positivity on the harmonic hyperplane**: where the finite part plus the paid gap is
nonnegative, Weil's form is nonnegative on every atomic test of the hyperplane. -/
theorem exists_weilQuad_atomicTest_nonneg_of_harmonic :
    ∃ G : ℝ, 0 < G ∧ ∀ {φ : ℝ → ℝ}, ContDiff ℝ 2 φ → (∀ u, u ∉ Set.Icc 0 1 → φ u = 0) →
      0 < (∫ u, φ u ^ 2) → ∀ {K : ℝ}, (∀ u v, |φ u - φ v| ≤ K * |u - v|) →
      ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 2 →
      ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : ℝ, 0 < w → w ≤ atomSpacing N / 2 →
        w * N ≤ markovOverlapBound → 0 ≤ defectFractionRetained ε w N →
        0 ≤ markovFinitePart φ ε w N + defectFractionRetained ε w N * G →
        ∀ x : ℕ → ℝ, ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 →
          0 ≤ weilQuad (atomicTest N x (atomDilate φ w)) := by
  obtain ⟨G, hG, hge⟩ := exists_weilQuad_atomicTest_ge_of_harmonic
  refine ⟨G, hG, fun {φ} hφ hφsupp hφ0 {K} hK {ε} hε hε1 => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hge hφ hφsupp hφ0 hK hε hε1
  exact ⟨N₀, fun N hN w hw0 hw hwN hc₀ hφ₀ x hx =>
    (mul_nonneg hφ₀ (integral_nonneg fun _ => sq_nonneg _)).trans
      (hN₀ N hN w hw0 hw hwN hc₀ x hx)⟩

/-- The Liouville gauge agrees with the Liouville sign on positive integers. -/
theorem liouvilleTwin_eq_liouvilleSign {n : ℕ} (hn : 0 < n) :
    liouvilleTwin n = liouvilleSign n := by
  rw [liouvilleTwin_apply, ArithmeticFunction.liouville_apply hn.ne', liouvilleSign]
  push_cast
  rfl

/-- The Liouville twin's atomic prime form is `ζ`'s at the Liouville-signed weights. -/
theorem twistedAtomicWeilForm_liouvilleTwin (N : ℕ) (x : ℕ → ℝ) :
    twistedAtomicWeilForm liouvilleTwin N x =
      atomicWeilForm N (fun n => liouvilleSign n * x n) := by
  rw [twistedAtomicWeilForm_eq liouvilleTwin_mul liouvilleTwin_sign, atomicWeilForm,
    atomicWeilForm]
  refine sum_congr rfl fun m hm => sum_congr rfl fun n hn => ?_
  rw [liouvilleTwin_eq_liouvilleSign (mem_Icc.mp hm).1, liouvilleTwin_eq_liouvilleSign
    (mem_Icc.mp hn).1]

/-- **The Liouville twin falls below `ζ` on the hyperplane.** There is `G > 0` such that for every
`ε > 0`, eventually in `N`, some nonzero `x` on the hyperplane `Σ x_n/√n = 0` has, for every narrow
atom profile `g`, `W_λ(f_x) + (G − 2ε)‖f_x‖² ≤ W(f_x)` for the full Weil forms. -/
theorem exists_liouville_weilQuad_add_le_of_harmonic :
    ∃ G : ℝ, 0 < G ∧ ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      ∃ x : ℕ → ℝ, ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 ∧ 0 < ∑ n ∈ Icc 1 N, x n ^ 2 ∧
        ∀ (g : ℝ → ℝ) (w : ℝ), ContDiff ℝ 2 g → HasCompactSupport g →
          (∀ u, u ∉ Set.Icc 0 w → g u = 0) → w < atomSpacing N →
          weilQuadTw (fun n => liouvilleTwin n * ArithmeticFunction.vonMangoldt n)
              (atomicTest N x g) + (G - 2 * ε) * ∫ u, atomicTest N x g u ^ 2 ≤
            weilQuad (atomicTest N x g) := by
  obtain ⟨G, hG, hsep⟩ := exists_pole_hyperplane_separates_liouville
  refine ⟨G, hG, fun ε hε => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hsep ε hε
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨hzeta, x, hx, hmass, hliou⟩ := hN₀ N hN
  refine ⟨x, hx, hmass, fun g w hg hgc hgsupp hw => ?_⟩
  have hdiff := weilQuadTw_atomicTest_sub_weilQuad liouvilleTwin_mul liouvilleTwin_sign hg hgc
    hgsupp hw x
  rw [twistedAtomicWeilForm_liouvilleTwin] at hdiff
  have hz := hzeta x hx
  rw [integral_atomicTest_sq hg hgc hgsupp hw x]
  have hA : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun _ => sq_nonneg _
  have hP : atomicWeilForm N x - atomicWeilForm N (fun n => liouvilleSign n * x n) ≤
      -((G - 2 * ε) * ∑ n ∈ Icc 1 N, x n ^ 2) := by linarith
  nlinarith [mul_le_mul_of_nonneg_left hP hA]

/-- **The pole hyperplane separates the full Weil forms of `ζ` and its Liouville twin.** One
constant `G > 0` gives both: the gap-paid lower bound for `ζ` on every hyperplane atomic test, and
a hyperplane witness below which the Liouville twin's full form falls by `(G − 2ε)‖f‖²`. -/
theorem exists_pole_hyperplane_separates_full_weil_forms :
    ∃ G : ℝ, 0 < G ∧
      (∀ {φ : ℝ → ℝ}, ContDiff ℝ 2 φ → (∀ u, u ∉ Set.Icc 0 1 → φ u = 0) →
        0 < (∫ u, φ u ^ 2) → ∀ {K : ℝ}, (∀ u v, |φ u - φ v| ≤ K * |u - v|) →
        ∀ {ε : ℝ}, 0 < ε → ε ≤ 1 / 2 →
        ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : ℝ, 0 < w → w ≤ atomSpacing N / 2 →
          w * N ≤ markovOverlapBound → 0 ≤ defectFractionRetained ε w N →
          ∀ x : ℕ → ℝ, ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 →
            (markovFinitePart φ ε w N + defectFractionRetained ε w N * G) *
                (∫ u, atomicTest N x (atomDilate φ w) u ^ 2) ≤
              weilQuad (atomicTest N x (atomDilate φ w))) ∧
      ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
        ∃ x : ℕ → ℝ, ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 ∧ 0 < ∑ n ∈ Icc 1 N, x n ^ 2 ∧
          ∀ (g : ℝ → ℝ) (w : ℝ), ContDiff ℝ 2 g → HasCompactSupport g →
            (∀ u, u ∉ Set.Icc 0 w → g u = 0) → w < atomSpacing N →
            weilQuadTw (fun n => liouvilleTwin n * ArithmeticFunction.vonMangoldt n)
                (atomicTest N x g) + (G - 2 * ε) * ∫ u, atomicTest N x g u ^ 2 ≤
              weilQuad (atomicTest N x g) := by
  obtain ⟨G₁, hG₁, h₁⟩ := exists_weilQuad_atomicTest_ge_of_harmonic
  obtain ⟨G₂, hG₂, h₂⟩ := exists_liouville_weilQuad_add_le_of_harmonic
  refine ⟨min G₁ G₂, lt_min hG₁ hG₂, fun {φ} hφ hφsupp hφ0 {K} hK {ε} hε hε1 => ?_,
    fun ε hε => ?_⟩
  · obtain ⟨N₀, hN₀⟩ := h₁ hφ hφsupp hφ0 hK hε hε1
    refine ⟨N₀, fun N hN w hw0 hw hwN hc₀ x hx => le_trans ?_ (hN₀ N hN w hw0 hw hwN hc₀ x hx)⟩
    have hF : 0 ≤ ∫ u, atomicTest N x (atomDilate φ w) u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have hc : defectFractionRetained ε w N * min G₁ G₂ ≤ defectFractionRetained ε w N * G₁ :=
      mul_le_mul_of_nonneg_left (min_le_left _ _) hc₀
    nlinarith
  · obtain ⟨N₀, hN₀⟩ := h₂ ε hε
    refine ⟨N₀, fun N hN => ?_⟩
    obtain ⟨x, hx, hmass, hle⟩ := hN₀ N hN
    refine ⟨x, hx, hmass, fun g w hg hgc hgsupp hw => le_trans ?_ (hle g w hg hgc hgsupp hw)⟩
    have hF : 0 ≤ ∫ u, atomicTest N x g u ^ 2 := integral_nonneg fun _ => sq_nonneg _
    have hm : min G₁ G₂ ≤ G₂ := min_le_right _ _
    nlinarith

/-- **On the pole hyperplane `ζ` is not the minimum of its gauge orbit**: eventually in `N` there is
a nonzero `x` on the hyperplane such that every narrow atom profile with `∫ g² > 0` has
`W_λ(f_x) < W(f_x)`. On nonnegative atomic tests the inequality goes the other way. -/
theorem exists_liouville_weilQuad_lt_of_harmonic :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
      ∃ x : ℕ → ℝ, ∑ n ∈ Icc 1 N, x n / Real.sqrt n = 0 ∧ 0 < ∑ n ∈ Icc 1 N, x n ^ 2 ∧
        ∀ (g : ℝ → ℝ) (w : ℝ), ContDiff ℝ 2 g → HasCompactSupport g →
          (∀ u, u ∉ Set.Icc 0 w → g u = 0) → w < atomSpacing N → 0 < ∫ u, g u ^ 2 →
          weilQuadTw (fun n => liouvilleTwin n * ArithmeticFunction.vonMangoldt n)
              (atomicTest N x g) < weilQuad (atomicTest N x g) := by
  obtain ⟨G, hG, h⟩ := exists_liouville_weilQuad_add_le_of_harmonic
  obtain ⟨N₀, hN₀⟩ := h (G / 4) (by positivity)
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨x, hx, hmass, hle⟩ := hN₀ N hN
  refine ⟨x, hx, hmass, fun g w hg hgc hgsupp hw hg0 => ?_⟩
  have hle' := hle g w hg hgc hgsupp hw
  rw [integral_atomicTest_sq hg hgc hgsupp hw x] at hle'
  have hpos : 0 < (∑ n ∈ Icc 1 N, x n ^ 2) * ∫ u, g u ^ 2 := mul_pos hmass hg0
  nlinarith

end GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
