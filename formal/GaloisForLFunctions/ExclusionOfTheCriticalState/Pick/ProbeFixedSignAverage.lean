import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.ProbeDiagonalBudget
import GaloisForLFunctions.HilbertMetric.QuantumInformation.PermutationTwirl
import GaloisForLFunctions.HTGeometry.PSDKernelOperations

/-!
# Fixed-sign permutation averages of Weil energies

The exact average splits into the diagonal-budget deficit and a
nonnegative sign-imbalance term. Vanishing forces balanced signs and
complete node collision with equal magnitudes, unless all coefficients
vanish. Odd-dimensional sign patterns therefore have strict mean energy.
-/

noncomputable section
open scoped BigOperators ComplexOrder
namespace GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeCuts
open Pick HilbertMetric.PermutationTwirl

/-- The prescribed real sign at a coefficient position. -/
def signCoefficient {n : ℕ} (τ : Fin n → Bool) (i : Fin n) : ℝ :=
  if τ i then 1 else -1

/-- Excess of positive signs over negative signs. -/
def signImbalance {n : ℕ} (τ : Fin n → Bool) : ℝ := ∑ i, signCoefficient τ i

/-- Sign imbalance is determined solely by the prescribed number of negative signs. -/
theorem signImbalance_count {n : ℕ} (τ : Fin n → Bool) :
    signImbalance τ = (n : ℝ) -
      2 * ((Finset.univ.filter (fun i => τ i = false)).card : ℝ) := by
  classical
  have he (i : Fin n) : signCoefficient τ i =
      1 - 2 * (if τ i = false then (1 : ℝ) else 0) := by
    cases hi : τ i <;> norm_num [signCoefficient, hi]
  have hc : (∑ i : Fin n, if τ i = false then (1 : ℝ) else 0) =
      ((Finset.univ.filter (fun i => τ i = false)).card : ℝ) := by
    rw [Finset.sum_ite]
    simp only [Finset.sum_const, Finset.sum_const_zero, nsmul_eq_mul, mul_one, add_zero]
  rw [signImbalance]
  simp_rw [he, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [hc]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- The literal arithmetic energy averaged over all relabelings of a fixed sign pattern. -/
def permutedSignEnergy {n : ℕ} (p a : Fin n → ℝ) (τ : Fin n → Bool) : ℝ :=
  (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ *
    ∑ σ : Equiv.Perm (Fin n), sourceQuadratic n (p ∘ σ) (signedCoefficients (a ∘ σ) τ)

/-- The actual magnitude-weighted Weil matrix. -/
def weightedProbeMatrix {n : ℕ} (p a : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => (weight p a i j : ℂ)

private theorem weightedProbeMatrix_trace {n : ℕ} (p a : Fin n → ℝ) :
    Matrix.trace (weightedProbeMatrix p a) = (probeDiagonalEnergy p a : ℂ) := by
  change (∑ i, ((|a i| * |a i| * safeProbeEntry (p i) (p i) : ℝ) : ℂ)) = _
  rw [probeDiagonalEnergy, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ring

private theorem weightedProbeMatrix_sum {n : ℕ} (p a : Fin n → ℝ) :
    (∑ i, ∑ j, weightedProbeMatrix p a i j) = (alignedEnergy p a : ℂ) := by
  simp only [weightedProbeMatrix, weight, alignedEnergy, sourceQuadratic, Complex.ofReal_sum]

private theorem signCoefficient_sq_sum {n : ℕ} (τ : Fin n → Bool) :
    (∑ i, signCoefficient τ i ^ 2) = (n : ℝ) := by
  have h (i : Fin n) : signCoefficient τ i ^ 2 = 1 := by
    cases hi : τ i <;> norm_num [signCoefficient, hi]
  simp only [h, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- Permutation averaging makes the actual magnitude-weighted Weil matrix positive semidefinite. -/
theorem twirl_weightedProbeMatrix_posSemidef {n : ℕ} (p a : Fin (n + 2) → ℝ) :
    (twirl (weightedProbeMatrix p a)).PosSemidef := by
  let q : ℝ := (alignedEnergy p a - probeDiagonalEnergy p a) /
    ((n + 2 : ℝ) * (n + 1))
  let b : ℝ := ((n + 2 : ℝ) * probeDiagonalEnergy p a - alignedEnergy p a) /
    ((n + 2 : ℝ) * (n + 1))
  have hq : 0 ≤ q := div_nonneg (aligned_cross_energy_bounds p a).1 (by positivity)
  have hbudget := alignedEnergy_le_card_diagonal p a
  simp only [Nat.cast_add, Nat.cast_ofNat] at hbudget
  have hb : 0 ≤ b := div_nonneg (sub_nonneg.mpr hbudget) (by positivity)
  have hqval : twirl (weightedProbeMatrix p a) 0 1 = (q : ℂ) := by
    rw [twirl_offDiagonal_value, weightedProbeMatrix_sum, weightedProbeMatrix_trace]
    simp only [q, Complex.ofReal_div, Complex.ofReal_sub, Complex.ofReal_mul,
      Complex.ofReal_add, Complex.ofReal_natCast, Complex.ofReal_one, Complex.ofReal_ofNat]
  have hbval : twirl (weightedProbeMatrix p a) 0 0 -
      twirl (weightedProbeMatrix p a) 0 1 = (b : ℂ) := by
    rw [twirl_diagonal_value, weightedProbeMatrix_trace, hqval]
    dsimp only [q, b]
    push_cast
    have hn : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
    have hm : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
    field_simp [hn, hm]
    ring
  rw [twirl_two_parameter_decomposition, hqval, hbval]
  have hones : Matrix.PosSemidef (fun (_ _ : Fin (n + 2)) => (1 : ℂ)) :=
    HTGeometry.isPSDKernel_one.posSemidef (fun i : Fin (n + 2) => i)
  have hI : (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ).PosSemidef := by
    simpa only [Matrix.conjTranspose_one, one_mul] using
      Matrix.posSemidef_conjTranspose_mul_self (1 : Matrix (Fin (n + 2)) (Fin (n + 2)) ℂ)
  exact (hones.smul (Complex.zero_le_real.mpr hq)).add
    (hI.smul (Complex.zero_le_real.mpr hb))

/-- Permutation twirling computes the actual finite average of signed Weil energies. -/
theorem permutedSignEnergy_eq_twirl {n : ℕ} (p a : Fin n → ℝ) (τ : Fin n → Bool) :
    (permutedSignEnergy p a τ : ℂ) =
      ∑ i, ∑ j, (signCoefficient τ i : ℂ) * twirl (weightedProbeMatrix p a) i j *
        (signCoefficient τ j : ℂ) := by
  rw [twirl_bilinear_average]
  simp only [permutedSignEnergy, Complex.ofReal_mul, Complex.ofReal_inv,
    Complex.ofReal_natCast, Complex.ofReal_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro σ _
  simp only [sourceQuadratic, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change (((|a (σ i)| * signCoefficient τ i) * (|a (σ j)| * signCoefficient τ j) *
    safeProbeEntry (p (σ i)) (p (σ j)) : ℝ) : ℂ) =
    (signCoefficient τ i : ℂ) *
      ((|a (σ i)| * |a (σ j)| * safeProbeEntry (p (σ i)) (p (σ j)) : ℝ) *
        (signCoefficient τ j : ℂ)
  push_cast
  ring

/-- The fixed-sign average splits into the diagonal-budget defect and an imbalance penalty. -/
theorem permutedSignEnergy_formula {n : ℕ}
    (p a : Fin (n + 2) → ℝ) (τ : Fin (n + 2) → Bool) :
    permutedSignEnergy p a τ =
      ((n + 2 : ℝ) * probeDiagonalEnergy p a - alignedEnergy p a) / (n + 1) +
        signImbalance τ ^ 2 * (alignedEnergy p a - probeDiagonalEnergy p a) /
          ((n + 2 : ℝ) * (n + 1)) := by
  have hs : (∑ i, (signCoefficient τ i : ℂ)) = (signImbalance τ : ℂ) := by
    rw [signImbalance, Complex.ofReal_sum]
  have hsq : (∑ i, (signCoefficient τ i : ℂ) ^ 2) = (n + 2 : ℂ) := by
    exact_mod_cast signCoefficient_sq_sum τ
  apply Complex.ofReal_injective
  rw [permutedSignEnergy_eq_twirl, twirl_bilinear_energy, twirl_diagonal_value,
    twirl_offDiagonal_value, weightedProbeMatrix_trace, weightedProbeMatrix_sum, hs, hsq]
  push_cast
  have hn : (n + 2 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 2 ≠ 0)
  have hm : (n + 1 : ℂ) ≠ 0 := by exact_mod_cast (by omega : n + 1 ≠ 0)
  field_simp [hn, hm]
  ring

/-- Every fixed-sign permutation average is nonnegative for the actual Weil kernel. -/
theorem permutedSignEnergy_nonneg {n : ℕ}
    (p a : Fin (n + 2) → ℝ) (τ : Fin (n + 2) → Bool) :
    0 ≤ permutedSignEnergy p a τ := by
  rw [permutedSignEnergy_formula]
  have hb := alignedEnergy_le_card_diagonal p a
  simp only [Nat.cast_add, Nat.cast_ofNat] at hb
  have hg := sub_nonneg.mpr hb
  have hc := (aligned_cross_energy_bounds p a).1
  exact add_nonneg (div_nonneg hg (by positivity))
    (div_nonneg (mul_nonneg (sq_nonneg _) hc) (by positivity))

private theorem probeDiagonalEnergy_zero_iff {n : ℕ} (p a : Fin n → ℝ) :
    probeDiagonalEnergy p a = 0 ↔ ∀ i, a i = 0 := by
  constructor
  · intro h i
    have hn (j : Fin n) : 0 ≤ |a j| ^ 2 * safeProbeEntry (p j) (p j) :=
      mul_nonneg (sq_nonneg _) (probeEntry_pos _ _).le
    have hi := Finset.single_le_sum (fun j _ => hn j) (Finset.mem_univ i)
    change |a i| ^ 2 * safeProbeEntry (p i) (p i) ≤ probeDiagonalEnergy p a at hi
    rw [h] at hi
    have hz := le_antisymm hi (hn i)
    have hs := (mul_eq_zero.mp hz).resolve_right (probeEntry_pos (p i) (p i)).ne'
    exact abs_eq_zero.mp (sq_eq_zero_iff.mp hs)
  · intro h
    simp only [probeDiagonalEnergy, h, abs_zero, zero_pow (by decide : 2 ≠ 0),
      zero_mul, Finset.sum_const_zero]

/-- Zero average has a sharp rigidity law: balanced signs, coincident nodes, equal magnitudes. -/
theorem permutedSignEnergy_zero_iff {n : ℕ}
    (p a : Fin (n + 2) → ℝ) (τ : Fin (n + 2) → Bool) :
    permutedSignEnergy p a τ = 0 ↔
      (∀ i, a i = 0) ∨
        (signImbalance τ = 0 ∧ ∀ i j, node (p i) = node (p j) ∧ |a i| = |a j|) := by
  constructor
  · intro h
    by_cases ha : ∀ i, a i = 0
    · exact Or.inl ha
    · have hd : 0 < probeDiagonalEnergy p a := lt_of_le_of_ne
        (probeDiagonalEnergy_nonneg p a)
          (Ne.symm (fun h => ha ((probeDiagonalEnergy_zero_iff p a).mp h)))
      have hn : (0 : ℝ) < n + 2 := by positivity
      have hm : (0 : ℝ) < n + 1 := by positivity
      have hb := alignedEnergy_le_card_diagonal p a
      simp only [Nat.cast_add, Nat.cast_ofNat] at hb
      have hg := sub_nonneg.mpr hb
      have hc := (aligned_cross_energy_bounds p a).1
      rw [permutedSignEnergy_formula] at h
      have hfirst := div_nonneg hg hm.le
      have hsecond := div_nonneg (mul_nonneg (sq_nonneg (signImbalance τ)) hc)
        (mul_pos hn hm).le
      have heq : ((n + 2 : ℝ) * probeDiagonalEnergy p a - alignedEnergy p a) / (n + 1) = 0 := by
        linarith only [h, hfirst, hsecond]
      have hgap := (div_eq_zero_iff.mp heq).resolve_right hm.ne'
      have hA : alignedEnergy p a = (n + 2 : ℝ) * probeDiagonalEnergy p a :=
        (sub_eq_zero.mp hgap).symm
      have hcross : 0 < alignedEnergy p a - probeDiagonalEnergy p a := by
        rw [hA]
        have he : (n + 2 : ℝ) * probeDiagonalEnergy p a - probeDiagonalEnergy p a =
            (n + 1 : ℝ) * probeDiagonalEnergy p a := by ring
        rw [he]
        exact mul_pos hm hd
      have hs : signImbalance τ ^ 2 * (alignedEnergy p a - probeDiagonalEnergy p a) /
          ((n + 2 : ℝ) * (n + 1)) = 0 := by linarith only [h, heq]
      have hnum := (div_eq_zero_iff.mp hs).resolve_right (mul_pos hn hm).ne'
      have hsign := sq_eq_zero_iff.mp ((mul_eq_zero.mp hnum).resolve_right hcross.ne')
      have hnodes := ((alignedEnergy_eq_card_diagonal_iff p a).mp
        (by simpa only [Nat.cast_add, Nat.cast_ofNat] using hA)).resolve_left ha
      exact Or.inr ⟨hsign, hnodes⟩
  · rintro (ha | ⟨hs, hnodes⟩)
    · have hd := (probeDiagonalEnergy_zero_iff p a).mpr ha
      have hA := (alignedEnergy_eq_card_diagonal_iff p a).mpr (Or.inl ha)
      simp only [Nat.cast_add, Nat.cast_ofNat] at hA
      rw [permutedSignEnergy_formula, hA, hd]
      ring

    · have hA := (alignedEnergy_eq_card_diagonal_iff p a).mpr (Or.inr hnodes)
      simp only [Nat.cast_add, Nat.cast_ofNat] at hA
      rw [permutedSignEnergy_formula, hA, hs]
      ring

private theorem signImbalance_odd_ne_zero {n : ℕ} (τ : Fin (2 * n + 3) → Bool) :
    signImbalance τ ≠ 0 := by
  classical
  intro h
  rw [signImbalance_count] at h
  have he : ((2 * n + 3 : ℕ) : ℝ) =
      2 * ((Finset.univ.filter (fun i => τ i = false)).card : ℝ) := by linarith only [h]
  have hn : 2 * n + 3 = 2 * (Finset.univ.filter (fun i => τ i = false)).card := by
    exact_mod_cast he
  omega

/-- For odd dimension at least three, every nonzero coefficient family has strictly positive average. -/
theorem permutedSignEnergy_odd_pos_iff {n : ℕ}
    (p a : Fin (2 * n + 3) → ℝ) (τ : Fin (2 * n + 3) → Bool) :
    0 < permutedSignEnergy p a τ ↔ ∃ i, a i ≠ 0 := by
  classical
  constructor
  · intro h
    by_contra ha
    push_neg at ha
    have hz := (permutedSignEnergy_zero_iff p a τ).mpr (Or.inl ha)
    rw [hz] at h
    exact (lt_irrefl 0) h
  · rintro ⟨i, hi⟩
    apply lt_of_le_of_ne (permutedSignEnergy_nonneg p a τ)
    intro hz
    rcases (permutedSignEnergy_zero_iff p a τ).mp hz.symm with ha | ⟨hs, _⟩
    · exact hi (ha i)
    · exact signImbalance_odd_ne_zero τ hs

#print axioms permutedSignEnergy_eq_twirl
#print axioms twirl_weightedProbeMatrix_posSemidef
#print axioms permutedSignEnergy_formula
#print axioms permutedSignEnergy_nonneg
#print axioms permutedSignEnergy_zero_iff
#print axioms signImbalance_count
#print axioms permutedSignEnergy_odd_pos_iff
end GaloisForLFunctions.ExclusionOfTheCriticalState.ProbeCuts
