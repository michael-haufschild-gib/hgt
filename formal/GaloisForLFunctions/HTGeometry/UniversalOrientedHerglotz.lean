import GaloisForLFunctions.HTGeometry.UniversalConstraintOrientation

/-!
# An oriented Herglotz cube over the universal HT field

Adjoin finitely many canonical real Cauchy atoms at negative integers, disjoint from the positive
prime-log support.  Their residue signs form a finite cube.  The associated meromorphic function is
Herglotz exactly in the distinguished all-positive chamber; every chamber with a negative
coordinate has an explicit upper-half-plane negativity witness.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Canonical real gauge poles, disjoint from the positive prime-log support. -/
def orientationPole (n : ℕ) : ℝ := -(n + 1 : ℝ)

theorem orientationPole_injective : Function.Injective orientationPole := by
  intro m n h
  simp [orientationPole] at h
  exact_mod_cast h

theorem orientationPole_neg (n : ℕ) : orientationPole n < 0 := by
  simp only [orientationPole]
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem orientationPole_not_mem_primeLogPoleSet (n : ℕ) :
    (orientationPole n : ℂ) ∈ primeLogPoleSetᶜ := by
  rw [Set.mem_compl_iff]
  rintro ⟨p, hp⟩
  have hre := congrArg Complex.re hp
  simp only [Complex.ofReal_re] at hre
  linarith [orientationPole_neg n, primeLogSupport_pos p]

/-- The fixed universal prime-log source is regular at every orientation pole. -/
theorem continuousAt_universalPrimeLog_orientationPole (n : ℕ) :
    ContinuousAt (primeLogHerglotz (fun q => universalFacetOrbitGauge q))
      (orientationPole n : ℂ) := by
  have hdiff := differentiableOn_primeLogHerglotz_off_poles
    (fun q => universalFacetOrbitGauge q) ‖universalFacetOrbitGauge‖
    (fun q => (le_abs_self (universalFacetOrbitGauge q)).trans
      (universalFacetOrbitGauge.norm_coe_le_norm q))
  exact ((hdiff _ (orientationPole_not_mem_primeLogPoleSet n)).differentiableAt
    (isOpen_compl_primeLogPoleSet.mem_nhds
      (orientationPole_not_mem_primeLogPoleSet n))).continuousAt

/-- A negative Cauchy atom dominates every continuous background near its real pole. -/
theorem exists_upper_im_neg_of_continuous_add_negativeAtom
    (a : ℝ) (g : ℂ → ℂ) (hg : ContinuousAt g (a : ℂ)) :
    ∃ z : ℂ, 0 < z.im ∧ (g z - ((a : ℂ) - z)⁻¹).im < 0 := by
  obtain ⟨δ, hδ, hcontrol⟩ := (Metric.continuousAt_iff.mp hg) 1 zero_lt_one
  let M : ℝ := |(g (a : ℂ)).im| + 1
  have hM : 0 < M := by
    dsimp [M]
    linarith [abs_nonneg (g (a : ℂ)).im]
  let y : ℝ := min (δ / 2) (1 / (2 * M))
  have hy : 0 < y :=
    lt_min (half_pos hδ) (one_div_pos.mpr (mul_pos (by norm_num) hM))
  have hyδ : y < δ := lt_of_le_of_lt (min_le_left _ _) (half_lt_self hδ)
  have hyM : y * M < 1 := by
    have hyle : y ≤ 1 / (2 * M) := min_le_right _ _
    have hmul := mul_le_mul_of_nonneg_right hyle hM.le
    have heq : (1 / (2 * M)) * M = 1 / 2 := by field_simp
    rw [heq] at hmul
    linarith
  let z : ℂ := (a : ℂ) + (y : ℂ) * Complex.I
  have hzdist : dist z (a : ℂ) < δ := by
    rw [Complex.dist_eq, ← norm_sub_rev]
    simp [z, abs_of_pos hy, hyδ]
  have hgdist := hcontrol hzdist
  have hgim : (g z).im < M := by
    have habs : |(g z).im - (g (a : ℂ)).im| < 1 := by
      have hle := Complex.abs_im_le_norm (g z - g (a : ℂ))
      have hnorm : ‖g z - g (a : ℂ)‖ < 1 := by
        simpa [Complex.dist_eq] using hgdist
      exact lt_of_le_of_lt hle hnorm
    dsimp [M]
    have hga : (g (a : ℂ)).im ≤ |(g (a : ℂ)).im| := le_abs_self _
    linarith [lt_of_abs_lt habs]
  have hMinv : M < y⁻¹ := by
    rw [inv_eq_one_div, lt_div_iff₀ hy]
    simpa [mul_comm] using hyM
  refine ⟨z, ?_, ?_⟩
  · simp [z, hy]
  · have hatom : (-(((a : ℂ) - z)⁻¹)).im = -y⁻¹ := by
      simp [z, Complex.inv_im, Complex.normSq]
    change (g z).im + (-((a : ℂ) - z)⁻¹).im < 0
    rw [hatom]
    linarith

/-- Residue sign in a finite orientation chamber. -/
def orientedAtomCoefficient (J : Finset ℕ) (n : ℕ) : ℝ :=
  if n ∈ J then -1 else 1

/-- The fixed prime-log source with a finite signed Cauchy-atom chamber attached. -/
def universalOrientedHerglotz (S J : Finset ℕ) (z : ℂ) : ℂ :=
  primeLogHerglotz (fun q => universalFacetOrbitGauge q) z +
    ∑ n ∈ S, (orientedAtomCoefficient J n : ℂ) *
      ((orientationPole n : ℂ) - z)⁻¹

theorem orientedAtom_im_nonneg {n : ℕ} {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (((1 : ℂ) * ((orientationPole n : ℂ) - z)⁻¹)).im := by
  rw [Complex.mul_im, Complex.one_re, Complex.one_im, zero_mul, add_zero,
    Complex.inv_im, Complex.sub_im, Complex.ofReal_im, zero_sub, neg_neg]
  simpa using div_nonneg hz.le (Complex.normSq_nonneg _)

theorem universalOrientedHerglotz_im_nonneg_of_disjoint
    (S J : Finset ℕ) (hSJ : Disjoint S J) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (universalOrientedHerglotz S J z).im := by
  have hbase := universalFacetOrbitGauge_primeLogHerglotz_im_nonneg hz
  rw [universalOrientedHerglotz, Complex.add_im]
  change 0 ≤ _ + Complex.imLm (∑ n ∈ S, _)
  rw [map_sum Complex.imLm]
  apply add_nonneg hbase
  apply Finset.sum_nonneg
  intro n hn
  have hnJ : n ∉ J := fun hnJ => Finset.disjoint_left.mp hSJ hn hnJ
  simp only [orientedAtomCoefficient, if_neg hnJ, Complex.ofReal_one]
  exact orientedAtom_im_nonneg hz

/-- Remove one chosen atom to expose a continuous background at its pole. -/
def universalOrientedHerglotzRegular
    (S J : Finset ℕ) (n : ℕ) (z : ℂ) : ℂ :=
  primeLogHerglotz (fun q => universalFacetOrbitGauge q) z +
    ∑ q ∈ S.erase n, (orientedAtomCoefficient J q : ℂ) *
      ((orientationPole q : ℂ) - z)⁻¹

theorem continuousAt_universalOrientedHerglotzRegular
    (S J : Finset ℕ) (n : ℕ) :
    ContinuousAt (universalOrientedHerglotzRegular S J n) (orientationPole n : ℂ) := by
  apply ContinuousAt.add (continuousAt_universalPrimeLog_orientationPole n)
  let T := S.erase n
  change ContinuousAt (fun z : ℂ => ∑ q ∈ T,
    (orientedAtomCoefficient J q : ℂ) * ((orientationPole q : ℂ) - z)⁻¹) _
  have hnT : n ∉ T := by simp [T]
  revert hnT
  induction T using Finset.induction_on with
  | empty =>
      intro hnT
      simpa only [Finset.sum_empty] using
        (continuousAt_const : ContinuousAt (fun _ : ℂ => (0 : ℂ)) _)
  | @insert q T hq ih =>
      intro hnInsert
      have hqn : q ≠ n := by
        intro h
        subst q
        exact hnInsert (by simp)
      have hnT : n ∉ T := by
        intro hn
        exact hnInsert (by simp [hn])
      have hterm : ContinuousAt (fun z : ℂ =>
          (orientedAtomCoefficient J q : ℂ) * ((orientationPole q : ℂ) - z)⁻¹)
          (orientationPole n : ℂ) := by
        apply ContinuousAt.const_mul
        apply ContinuousAt.inv₀ (continuousAt_const.sub continuousAt_id)
        intro heq
        have hpole : orientationPole q = orientationPole n := by
          exact Complex.ofReal_injective (sub_eq_zero.mp heq)
        exact hqn (orientationPole_injective hpole)
      have hsum := hterm.add (ih hnT)
      simpa [Finset.sum_insert hq] using! hsum

theorem universalOrientedHerglotz_eq_regular_sub_atom
    {S J : Finset ℕ} {n : ℕ} (hnS : n ∈ S) (hnJ : n ∈ J) (z : ℂ) :
    universalOrientedHerglotz S J z =
      universalOrientedHerglotzRegular S J n z -
        ((orientationPole n : ℂ) - z)⁻¹ := by
  rw [universalOrientedHerglotz, universalOrientedHerglotzRegular]
  have hsplit := Finset.sum_erase_add (s := S) (f := fun q =>
    (orientedAtomCoefficient J q : ℂ) * ((orientationPole q : ℂ) - z)⁻¹) hnS
  rw [← hsplit]
  simp [orientedAtomCoefficient, hnJ]
  ring

theorem universalOrientedHerglotz_not_nonneg_of_not_disjoint
    (S J : Finset ℕ) (hSJ : ¬ Disjoint S J) :
    ¬ ∀ z : ℂ, 0 < z.im → 0 ≤ (universalOrientedHerglotz S J z).im := by
  rw [Finset.not_disjoint_iff] at hSJ
  obtain ⟨n, hnS, hnJ⟩ := hSJ
  obtain ⟨z, hz, hneg⟩ := exists_upper_im_neg_of_continuous_add_negativeAtom
    (orientationPole n) (universalOrientedHerglotzRegular S J n)
    (continuousAt_universalOrientedHerglotzRegular S J n)
  intro hnonneg
  have h := hnonneg z hz
  rw [universalOrientedHerglotz_eq_regular_sub_atom hnS hnJ z] at h
  exact (not_lt_of_ge h) hneg

/-- **Exact oriented Herglotz chamber law.**  The finite signed Cauchy-atom representative is
Herglotz exactly when no active atom has negative orientation. -/
theorem universalOrientedHerglotz_nonneg_iff_disjoint (S J : Finset ℕ) :
    (∀ z : ℂ, 0 < z.im → 0 ≤ (universalOrientedHerglotz S J z).im) ↔
      Disjoint S J := by
  constructor
  · intro h
    by_contra hdisj
    exact universalOrientedHerglotz_not_nonneg_of_not_disjoint S J hdisj h
  · intro h z hz
    exact universalOrientedHerglotz_im_nonneg_of_disjoint S J h hz

/-- The number of active negative residue coordinates. -/
def orientedNegativeIndex (S J : Finset ℕ) : ℕ := (S ∩ J).card

theorem orientedNegativeIndex_eq_card_of_subset
    {S J : Finset ℕ} (hJS : J ⊆ S) : orientedNegativeIndex S J = J.card := by
  rw [orientedNegativeIndex, Finset.inter_eq_right.mpr hJS]

/-- Analytic Herglotz positivity is exactly the zero level of the residue index. -/
theorem universalOrientedHerglotz_nonneg_iff_negativeIndex_zero (S J : Finset ℕ) :
    (∀ z : ℂ, 0 < z.im → 0 ≤ (universalOrientedHerglotz S J z).im) ↔
      orientedNegativeIndex S J = 0 := by
  rw [universalOrientedHerglotz_nonneg_iff_disjoint, orientedNegativeIndex,
    Finset.card_eq_zero, Finset.disjoint_iff_inter_eq_empty]

/-- Inside the finite cube `J ⊆ S`, the all-positive vertex is the unique Herglotz chamber. -/
theorem universalOrientedHerglotz_nonneg_iff_empty_of_subset
    {S J : Finset ℕ} (hJS : J ⊆ S) :
    (∀ z : ℂ, 0 < z.im → 0 ≤ (universalOrientedHerglotz S J z).im) ↔ J = ∅ := by
  rw [universalOrientedHerglotz_nonneg_iff_negativeIndex_zero,
    orientedNegativeIndex_eq_card_of_subset hJS, Finset.card_eq_zero]

/-- The finite orientation fiber over an active support `S` has exactly `2^|S|` chambers. -/
theorem orientedChamber_count (S : Finset ℕ) : S.powerset.card = 2 ^ S.card := by
  exact Finset.card_powerset S

end

end GaloisForLFunctions.HTGeometry
