import GaloisForLFunctions.CriticalArithmeticCorrelationTheory.TheCompleteWeilMatrixKeepsItsBoundaryCorrection

/-!
# The complete Weil matrix at every overlap

At width `w = c/N` with `c > 1` neighbouring atoms overlap. Each entry of the complete matrix is
`(Arch(n,j) − Prime(n,j) + Pole(n,j))/(w∫φ²)`, where
`Arch(n,j) = 2θ′(0)⟨a_n, a_j⟩ + ∫_{y>0} levyMixed(a_n, a_j)` is the archimedean pairing of the
atoms. For separated pairs `|log j − log n| > w` it is minus the cross term, as below touching. For
overlapping pairs it is kept literally.

`completeWeilMatrix_eq_decomposition_at_every_overlap` is the exact identity

`W = (log N + self(c) − γ + selfErr)·I − P + Center(cq) − CrossErr^sep + PoleErr + Ov − NR`,

valid for every `c > 0`: the cross error is restricted to far pairs (log-distance `> 2w`), the
overlap matrix `Ov` carries the literal archimedean pairing of near atoms (log-distance `≤ 2w`,
with the center kernel added back), and `NR` is the non-ratio prime matrix. The threshold `2w`
keeps the far cross error under its reciprocal-square bound.
-/

noncomputable section

open MeasureTheory Finset Matrix Set
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticElectrostatics SpacingScaleHarmonicAnalysis ArithmeticLorentzianGeometry
  CriticalArithmeticCorrelationTheory
open _root_.RHTower (archLevyDensity gammaHardyPhaseRate levyEnergy)

/-- The archimedean pairing `2θ′(0)⟨a_n, a_j⟩ + ∫_{y>0} levyMixed(a_n, a_j)` of two atoms. -/
def atomArchPair (g : ℝ → ℝ) (n j : ℕ) : ℝ :=
  2 * gammaHardyPhaseRate 0 * (∫ u, atom g n u * atom g j u) +
    ∫ y in Ioi 0, levyMixed (atom g n) (atom g j) y

theorem markovPair_eq_atomArchPair_sub (g : ℝ → ℝ) (n j : ℕ) :
    markovPair (atom g n) (atom g j) = atomArchPair g n j - primePair (atom g n) (atom g j) := rfl

theorem atomArchPair_comm (g : ℝ → ℝ) (n j : ℕ) : atomArchPair g n j = atomArchPair g j n := by
  have h1 : (∫ u, atom g n u * atom g j u) = ∫ u, atom g j u * atom g n u :=
    integral_congr_ae (Filter.Eventually.of_forall fun u => mul_comm _ _)
  have h2 : (∫ y in Ioi 0, levyMixed (atom g n) (atom g j) y) =
      ∫ y in Ioi 0, levyMixed (atom g j) (atom g n) y := by
    refine setIntegral_congr_fun measurableSet_Ioi fun y _ => ?_
    unfold levyMixed
    rw [integral_congr_ae (Filter.Eventually.of_forall fun u => mul_comm
      (atom g n u - atom g n (u + y)) (atom g j u - atom g j (u + y)))]
  rw [atomArchPair, atomArchPair, h1, h2]

/-- The diagonal archimedean pairing is the atom self-energy. -/
theorem atomArchPair_self (g : ℝ → ℝ) (n : ℕ) :
    atomArchPair g n n = 2 * gammaHardyPhaseRate 0 * (∫ u, g u ^ 2) + levyEnergy g := by
  have h1 : (∫ u, atom g n u * atom g n u) = ∫ u, g u ^ 2 := by
    simp only [atom, ← pow_two]
    exact integral_sub_right_eq_self (fun u => g u ^ 2) (Real.log n)
  have h2 : (∫ y in Ioi 0, levyMixed (atom g n) (atom g n) y) = levyEnergy g := by
    simp only [levyMixed, ← sq]
    change levyEnergy (atom g n) = levyEnergy g
    exact levyEnergy_translate (Real.log n)
  rw [atomArchPair, h1, h2]

/-- A separated pair of atoms pairs through minus the archimedean cross term. -/
theorem atomArchPair_of_separated {g : ℝ → ℝ} {w : ℝ}
    (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0) {n j : ℕ} (hn : 0 < n) (hj : 0 < j)
    (hsep : w < |Real.log j - Real.log n|) :
    atomArchPair g n j = -atomCrossTerm g |Real.log j - Real.log n| := by
  -- the ordered case `a < b`
  have hordered : ∀ a b : ℕ, 0 < a → 0 < b → w < Real.log b - Real.log a →
      atomArchPair g a b = -atomCrossTerm g (Real.log b - Real.log a) := by
    intro a b _ _ hab
    have hdisj : (∫ u, atom g a u * atom g b u) = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [] with u
      change atom g a u * atom g b u = 0
      by_cases hau : u - Real.log a ∈ Set.Icc 0 w
      · have hbu : u - Real.log b ∉ Set.Icc 0 w := by
          intro hbu
          linarith only [hau.1, hau.2, hbu.1, hbu.2, hab]
        simp only [atom, hsupp _ hbu, mul_zero]
      · simp only [atom, hsupp _ hau, zero_mul]
    have htr : ∀ y, levyMixed (atom g a) (atom g b) y =
        levyMixed g (fun u => g (u - (Real.log b - Real.log a))) y := by
      intro y
      unfold levyMixed atom
      congr 1
      rw [← integral_sub_right_eq_self
        (fun u => (g u - g (u + y)) *
          (g (u - (Real.log b - Real.log a)) -
            g (u + y - (Real.log b - Real.log a)))) (Real.log a)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun u => by ring_nf
    rw [atomArchPair, hdisj, mul_zero, zero_add, atomCrossTerm, ← integral_neg]
    refine setIntegral_congr_fun measurableSet_Ioi fun y hy => ?_
    rw [htr, levyMixed_atom_shift hsupp hab hy]
  rcases le_or_gt (Real.log j - Real.log n) 0 with h | h
  · rw [abs_of_nonpos h] at hsep ⊢
    rw [atomArchPair_comm, hordered j n hj hn (by linarith), show -(Real.log j - Real.log n) =
      Real.log n - Real.log j by ring]
  · rw [abs_of_pos h] at hsep ⊢
    exact hordered n j hn hj hsep

private theorem integral_atomDilate' (φ : ℝ → ℝ) {w : ℝ} (hw : 0 < w) :
    (∫ u, atomDilate φ w u) = w * ∫ u, φ u := by
  simpa only [atomDilate, smul_eq_mul, abs_of_pos hw] using
    MeasureTheory.Measure.integral_comp_div φ w

private theorem pole_product_eq_center_add_error' (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    ((∫ u, atomDilate φ (c / N) u * Real.exp (-(u / 2))) *
      (∫ u, atomDilate φ (c / N) u * Real.exp (u / 2)) /
        (∫ u, atomDilate φ (c / N) u ^ 2)) =
      atomPoleErrorCoefficient φ c N + completeWeilPoleShift φ c / N := by
  have hneg : atomExponentialMoment (atomDilate φ (c / N)) (-(1 / 2)) =
      ∫ u, atomDilate φ (c / N) u * Real.exp (-(u / 2)) := by
    unfold atomExponentialMoment
    congr 1
    funext u
    congr 2
    ring
  have hpos : atomExponentialMoment (atomDilate φ (c / N)) (1 / 2) =
      ∫ u, atomDilate φ (c / N) u * Real.exp (u / 2) := by
    unfold atomExponentialMoment
    congr 1
    funext u
    congr 2
    ring
  rw [atomPoleErrorCoefficient, hneg, hpos]
  ring

/-- The cross replacement error restricted to far pairs, at log-distance beyond twice the width. -/
def separatedCrossErrorMatrix (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ :=
  fun n j => if 2 * (c / N) < |Real.log (j : ℕ) - Real.log (n : ℕ)| then
    atomCrossErrorKernel (atomDilate φ (c / N)) n j else 0

/-- The literal archimedean pairing of near distinct atoms (log-distance at most twice the width),
with the center kernel added back. It vanishes off the near pairs. -/
def overlapMatrix (φ : ℝ → ℝ) (c : ℝ) (N : ℕ) :
    Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ :=
  fun n j => if (n : ℕ) ≠ j ∧ |Real.log (j : ℕ) - Real.log (n : ℕ)| ≤ 2 * (c / N) then
    atomArchPair (atomDilate φ (c / N)) n j / (∫ u, atomDilate φ (c / N) u ^ 2) +
      (completeWeilPoleShift φ c / N) * archimedeanCenterKernel n j else 0

/-- **Exact decomposition at every overlap.** -/
theorem completeWeilMatrix_eq_decomposition_at_every_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) {N : ℕ} (hN : 1 ≤ N) :
    completeWeilMatrix φ c N =
      (Real.log N + completeWeilSelfFinitePart φ c - Real.eulerMascheroniConstant +
        completeWeilSelfError φ c N) • (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) -
      fullPrimeMatrix N + fullWeilCenterMatrix (completeWeilPoleShift φ c) N -
        separatedCrossErrorMatrix φ c N + fullWeilPoleErrorMatrix φ c N +
          overlapMatrix φ c N - fullWeilNonRatioMatrix φ c N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hw := div_pos hc0 hN0
  obtain ⟨hg, hgs, hgc⟩ := atomDilate_facts hφ hsupp hw
  set g := atomDilate φ (c / N) with hgdef
  have hG : 0 < ∫ u, g u ^ 2 := by
    rw [hgdef, integral_atomDilate_sq hw]
    exact mul_pos hw hM
  have hcharge : (∫ u, g u) ^ 2 / (∫ u, g u ^ 2) = completeWeilPoleShift φ c / N := by
    rw [hgdef, integral_atomDilate' φ hw, integral_atomDilate_sq hw, completeWeilPoleShift]
    field_simp [hN0.ne', hc0.ne', hM.ne']
  ext n j
  have hraw : fullWeilHorizonMatrix g N n j =
      (atomArchPair g n j - primePair (atom g n) (atom g j)) +
        ((∫ u, g u * Real.exp (-(u / 2))) * (∫ u, g u * Real.exp (u / 2))) *
          arithmeticPoleKernel n j := by
    simp only [fullWeilHorizonMatrix, atomicWeilGram, atomicMarkovGram, Matrix.of_apply,
      primeHorizonFinEquiv_val_add_one, markovPair_eq_atomArchPair_sub,
      atomPoleRow_primeHorizonFinEquiv_zero, atomPoleRow_primeHorizonFinEquiv_one,
      arithmeticPoleKernel]
    ring
  have hentry : completeWeilMatrix φ c N n j =
      (atomArchPair g n j - primePair (atom g n) (atom g j)) / (∫ u, g u ^ 2) +
        ((∫ u, g u * Real.exp (-(u / 2))) * (∫ u, g u * Real.exp (u / 2)) /
          (∫ u, g u ^ 2)) * arithmeticPoleKernel n j := by
    rw [completeWeilMatrix, normalizedFullWeilHorizonMatrix, ← hgdef, hraw]
    ring
  rw [hentry, pole_product_eq_center_add_error']
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply, fullPrimeMatrix, fullWeilCenterMatrix, separatedCrossErrorMatrix,
    fullWeilPoleErrorMatrix, overlapMatrix, fullWeilNonRatioMatrix_apply, atomCrossErrorKernel]
  have hn0 : 0 < (n : ℕ) := (mem_Icc.mp n.property).1
  have hj0 : 0 < (j : ℕ) := (mem_Icc.mp j.property).1
  by_cases hnj : n = j
  · subst j
    simp only [ite_true, sub_self, abs_zero, not_lt.mpr (by positivity : (0 : ℝ) ≤ 2 * (c / N)),
      if_false, ne_eq,
      not_true_eq_false, false_and, archimedeanCenterKernel_self, atomArchPair_self,
      completeWeilSelfError, ← hgdef]
    have hG' := hG.ne'
    field_simp
    ring
  · have hval : (n : ℕ) ≠ (j : ℕ) := fun h => hnj (Subtype.ext h)
    rw [if_neg hnj]
    rcases lt_or_ge (2 * (c / N)) |Real.log (j : ℕ) - Real.log (n : ℕ)| with hs | hs
    · rw [if_pos hs, if_neg hval, if_neg (fun h => absurd h.2 (not_le.mpr hs)),
        atomArchPair_of_separated hgs hn0 hj0 (by linarith), ← hcharge]
      ring
    · rw [if_neg (not_lt.mpr hs), if_pos ⟨hval, hs⟩, ← hcharge]
      ring

private theorem identity_matrix_action' {N : ℕ}
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    Matrix.toEuclideanLin (1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) x = x := by
  ext n
  change ((1 : Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ) *ᵥ x) n = x n
  rw [Matrix.one_mulVec]

/-- The complete energy at every overlap, split along the exact decomposition. -/
theorem completeWeilMatrix_inner_eq_decomposition_at_every_overlap {φ : ℝ → ℝ}
    (hφ : ContDiff ℝ 2 φ) (hsupp : ∀ u, u ∉ Set.Icc 0 1 → φ u = 0)
    (hM : 0 < ∫ u, φ u ^ 2) {c : ℝ} (hc0 : 0 < c) {N : ℕ} (hN : 1 ≤ N)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin (completeWeilMatrix φ c N) x, x⟫ =
      (Real.log N * ‖x‖ ^ 2 - ⟪Matrix.toEuclideanLin (fullPrimeMatrix N) x, x⟫) +
      (completeWeilSelfFinitePart φ c - Real.eulerMascheroniConstant +
        completeWeilSelfError φ c N) * ‖x‖ ^ 2 +
      ⟪Matrix.toEuclideanLin (fullWeilCenterMatrix (completeWeilPoleShift φ c) N) x, x⟫ -
      ⟪Matrix.toEuclideanLin (separatedCrossErrorMatrix φ c N) x, x⟫ +
      ⟪Matrix.toEuclideanLin (fullWeilPoleErrorMatrix φ c N) x, x⟫ +
      (⟪Matrix.toEuclideanLin (overlapMatrix φ c N) x, x⟫ -
        ⟪Matrix.toEuclideanLin (fullWeilNonRatioMatrix φ c N) x, x⟫) := by
  rw [completeWeilMatrix_eq_decomposition_at_every_overlap hφ hsupp hM hc0 hN]
  simp only [map_add, map_sub, map_smul, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.smul_apply, identity_matrix_action', inner_add_left, inner_sub_left,
    real_inner_smul_left, real_inner_self_eq_norm_sq]
  ring

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
