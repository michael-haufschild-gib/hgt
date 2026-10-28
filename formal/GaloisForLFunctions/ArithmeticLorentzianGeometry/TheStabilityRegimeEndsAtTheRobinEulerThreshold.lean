import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheAtomicFormIsMetzlerBelowTheSpacing
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheFinitePartOfTheMarkovFormAtTheSpacing
import GaloisForLFunctions.SpacingScaleHarmonicAnalysis.TheDiamagneticInequality

/-!
# The stability regime ends at the Robin–Euler threshold

Below the spacing the atomic intersection Gram of `ζ` is Metzler, and the Metzler dichotomy
splits it into two regimes: the **stability regime**, where a positive weight `π` has `Qπ ≤ 0` and
the form is nonpositive without help, and the **trickle-down regime**, where the Hodge index is
the inequality `(TD_π)`. Where does the atom block `−M` leave the stability regime?

The finite part of the Markov form at the spacing scale (RenormalizedArithmeticPotentialTheory)
is `2θ′(0) + log(1/(wN)) + κ_L(φ) + γ`: the archimedean slope, the Nyquist margin, the Robin
constant of the profile and Euler's constant of the pole, and the pole vector `x_n = n^{−1/2}`
attains it.

* **The Markov form is negative on the pole vector beyond the threshold**
  (`eventually_markovEnergy_poleTest_neg`): eventually in `N`, at every width `w ≤ δ_N/2` with
  `2θ′(0) + log(1/(wN)) + κ_L(φ) + γ + ε + (e^{1/2}/2) w < 0`, the pole test has `M(f) < 0`.
* **The atom block leaves the stability regime** (`eventually_not_stability_atomBlock`): at those
  widths no positive weight `π` has `(−M)π ≤ 0`; the atom block of the Gram has a positive square,
  carried by the pole vector.

So for overlap ratios `wN` above `exp(2θ′(0) + κ_L(φ) + γ)` the atom block alone has a positive
square; the Hodge index of the full Gram then holds only if the pole plane absorbs it, and it is
exactly the weighted trickle-down inequality. The stability regime ends at the Robin–Euler
threshold; the window up to the spacing is the trickle-down regime proper.
-/

noncomputable section

open MeasureTheory Finset Matrix RHTower

namespace GaloisForLFunctions.ArithmeticLorentzianGeometry

open GaloisForLFunctions.SpacingScaleHarmonicAnalysis GaloisForLFunctions.ArithmeticElectrostatics
  GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

local notation "γ" => Real.eulerMascheroniConstant

variable {φ : ℝ → ℝ}

/-- The pole vector `n^{−1/2}` on the atoms `1, …, N`. -/
def finPole (N : ℕ) : Fin N → ℝ := fun j => poleVector ((j : ℕ) + 1)

theorem finAtomicTest_finPole (g : ℝ → ℝ) (N : ℕ) :
    finAtomicTest g N (finPole N) = atomicTest N (truncPole N) g := by
  funext u
  rw [atomicTest, sum_Icc_one_eq_sum_fin]
  refine sum_congr rfl fun j _ => ?_
  simp only [finPole, truncPole, atom, if_pos (show (j : ℕ) + 1 ≤ N by omega)]

/-- The Markov Gram evaluates the Markov form: `(−M)[d] = −M(Σ_j d_j g_{j+1})`. -/
theorem qf_neg_atomicMarkovGram {g : ℝ → ℝ} {w : ℝ} (hg : ContDiff ℝ 2 g)
    (hgsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) (hw0 : 0 ≤ w) (N : ℕ) (d : Fin N → ℝ) :
    qf (-atomicMarkovGram g N) d = -levyMarkovForm (finAtomicTest g N d) := by
  rw [show finAtomicTest g N d = fun u => ∑ j, d j * atom g ((j : ℕ) + 1) u from rfl,
    levyMarkovForm_sum_eq _ (fun j => contDiff_atom hg _) (fun j => hasCompactSupport_atom hgsupp _)
      (fun j => supportedIn_atom hgsupp hw0 (mem_Icc_succ j)), qf_eq_sum, ← sum_neg_distrib]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_neg_distrib]
  refine sum_congr rfl fun j _ => ?_
  simp only [Matrix.neg_apply, atomicMarkovGram, Matrix.of_apply]
  ring

/-- **The Markov form is negative on the pole vector beyond the Robin–Euler threshold.** -/
theorem eventually_markovEnergy_poleTest_neg (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {K : ℝ}
    (hK : ∀ u v, |φ u - φ v| ≤ K * |u - v|) (hφnn : ∀ u, 0 ≤ φ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : ℝ, 0 < w → w ≤ atomSpacing N / 2 →
      2 * gammaHardyPhaseRate 0 + Real.log (1 / (w * N)) + profileRobin φ + γ + ε +
          Real.exp (1 / 2) / 2 * w < 0 →
        markovEnergy (fun u => (atomicTest N (truncPole N) (atomDilate φ w) u : ℂ)) < 0 := by
  obtain ⟨N₀, hN₀⟩ := eventually_markovEnergy_truncPole_le hφ hφsupp hφ0 hK hφnn hε
  refine ⟨max N₀ 1, fun N hN w hw0 hw hneg => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hup := hN₀ N (le_trans (le_max_left _ _) hN) w hw0 hw
  obtain ⟨hgc2, hgsupp, hgc⟩ := atomDilate_facts hφ hφsupp hw0
  have hw' : w < atomSpacing N := by linarith [atomSpacing_pos hN1]
  -- the pole test has positive mass
  have hmass : 0 < ∫ u, atomicTest N (truncPole N) (atomDilate φ w) u ^ 2 := by
    rw [integral_atomicTest_sq hgc2 hgc hgsupp hw', integral_atomDilate_sq hw0]
    have h1 : (1 : ℝ) ≤ ∑ n ∈ Icc 1 N, truncPole N n ^ 2 := by
      have hmem : 1 ∈ Icc 1 N := Finset.mem_Icc.mpr ⟨le_rfl, hN1⟩
      have := Finset.single_le_sum (f := fun n => truncPole N n ^ 2)
        (fun n _ => sq_nonneg _) hmem
      simpa [truncPole, if_pos hN1, poleVector] using this
    have : 0 < w * ∫ u, φ u ^ 2 := mul_pos hw0 hφ0
    nlinarith
  calc markovEnergy (fun u => (atomicTest N (truncPole N) (atomDilate φ w) u : ℂ))
      ≤ _ := hup
    _ < 0 := mul_neg_of_neg_of_pos hneg hmass

/-- **The atom block leaves the stability regime beyond the Robin–Euler threshold**: at those
widths no positive weight `π` on the atoms has `(−M)π ≤ 0`. -/
theorem eventually_not_stability_atomBlock (hφ : ContDiff ℝ 2 φ)
    (hφsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0) (hφ0 : 0 < ∫ u, φ u ^ 2) {K : ℝ}
    (hK : ∀ u v, |φ u - φ v| ≤ K * |u - v|) (hφnn : ∀ u, 0 ≤ φ u) {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ w : ℝ, 0 < w → w ≤ atomSpacing N / 2 →
      2 * gammaHardyPhaseRate 0 + Real.log (1 / (w * N)) + profileRobin φ + γ + ε +
          Real.exp (1 / 2) / 2 * w < 0 →
        ¬ ∃ π : Fin N → ℝ, (∀ i, 0 < π i) ∧
          ∀ i, ((-atomicMarkovGram (atomDilate φ w) N) *ᵥ π) i ≤ 0 := by
  obtain ⟨N₀, hN₀⟩ := eventually_markovEnergy_poleTest_neg hφ hφsupp hφ0 hK hφnn hε
  refine ⟨max N₀ 1, fun N hN w hw0 hw hneg => ?_⟩
  rintro ⟨π, hπ, hQπ⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hM := hN₀ N (le_trans (le_max_left _ _) hN) w hw0 hw hneg
  obtain ⟨hgc2, hgsupp, hgc⟩ := atomDilate_facts hφ hφsupp hw0
  have hw' : w < atomSpacing N := by linarith [atomSpacing_pos hN1]
  -- the atom block is symmetric and Metzler below the spacing
  have hsymm : (-atomicMarkovGram (atomDilate φ w) N).IsSymm := by
    unfold Matrix.IsSymm; rw [transpose_neg, (atomicMarkovGram_isSymm _ N).eq]
  have hmetz : IsMetzler (-atomicMarkovGram (atomDilate φ w) N) := fun i j hij => by
    have h := atomicIntersectionGram_isMetzler (fun u => hφnn _) hgsupp hw' (Sum.inr i)
      (Sum.inr j) (by simpa using hij)
    simp only [atomicIntersectionGram, fromBlocks_apply₂₂] at h
    exact h
  have hle := qf_nonpos_of_mulVec_nonpos hsymm hmetz hπ hQπ (finPole N)
  rw [qf_neg_atomicMarkovGram hgc2 hgsupp hw0.le, finAtomicTest_finPole,
    levyMarkovForm_eq_markovEnergy (contDiff_atomicTest hgc2 N _)
      (hasCompactSupport_atomicTest hgsupp N _)] at hle
  linarith

end GaloisForLFunctions.ArithmeticLorentzianGeometry
