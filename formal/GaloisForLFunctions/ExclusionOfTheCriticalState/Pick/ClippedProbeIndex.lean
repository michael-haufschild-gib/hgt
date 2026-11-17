import GaloisForLFunctions.ExclusionOfTheCriticalState.Pick.TheConfinedPickMatricesCountTheZerosRightOfTheLine
import GaloisForLFunctions.HilbertMetric.Spectral.ClippedThreshold
import GaloisForLFunctions.HilbertMetric.Spectral.ClippedRankComparison
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheHodgeDefectIsCyclic

/-!
# Clipped energy bounds for the actual confined probe matrices

Write `K_R = B + P_R`, where `B` is the bare Weil probe matrix and
`P_R = a(R) (1/(pᵢ+pⱼ−8))` is positive. The clipped threshold inequality
applied to `P_R − K_R = −B` bounds the confinement's clipped energy by the
bare arithmetic square mass, the trace of `K_R`, and one cutoff square per
negative direction of `K_R`. Positive excess therefore certifies negative
directions and, through the probe index law, zeros right of the line.
Arbitrary rectangular coefficient matrices retain the orientation of the
tested probe combinations, which the uncompressed trace can lose.
-/

open Matrix
open scoped ComplexOrder NNReal
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations HTGeometry ArithmeticCastelnuovoSeveri _root_.RHTower
open HilbertMetric.Clipped
noncomputable section

/-- The positive confinement block in the confined probe matrix. -/
def probeConfinementBlock (R : ℝ) {N : ℕ} (p : Fin N → ℝ) : Matrix (Fin N) (Fin N) ℂ :=
  (criticalAliasCoefficient R : ℂ) • probeConfinementGram p

theorem probeConfinementGram_isHermitian {N : ℕ} (p : Fin N → ℝ) :
    (probeConfinementGram p).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, probeConfinementGram,
    Complex.star_def, Complex.conj_ofReal, add_comm]

/-- The integral Gram positivity is also positivity in the spectral matrix API. -/
theorem probeConfinementGram_posSemidef {N : ℕ} {p : Fin N → ℝ} (hp : ∀ i, 4 < p i) :
    (probeConfinementGram p).PosSemidef := by
  have hC := probeConfinementGram_isHermitian p
  rw [hC.posSemidef_iff_eigenvalues_nonneg]
  intro i
  rw [hC.eigenvalues_eq]
  exact hermQuad_probeConfinementGram_nonneg hp _

theorem probeConfinementBlock_posSemidef {R : ℝ} (hR : 0 < R)
    {N : ℕ} {p : Fin N → ℝ} (hp : ∀ i, 4 < p i) :
    (probeConfinementBlock R p).PosSemidef := by
  exact (probeConfinementGram_posSemidef hp).smul
    (show (0 : ℂ) ≤ (criticalAliasCoefficient R : ℂ) from
      Complex.nonneg_iff.mpr ⟨(criticalAliasCoefficient_positive hR).le, rfl⟩)

theorem confinedProbeGram_isHermitian {R : ℝ} (hR : 0 < R)
    {N : ℕ} {p : Fin N → ℝ} (hp : ∀ i, 4 < p i) :
    (confinedProbeGram R p).IsHermitian := by
  rw [confinedProbeGram_eq R hp]
  exact (probeGram_isHermitian (fun i => by linarith only [hp i])).add
    (probeConfinementBlock_posSemidef hR hp).isHermitian

/-- Squared entries of the bare kernel, expressed entirely through its arithmetic symbol. -/
theorem probeGram_trace_square {N : ℕ} {p : Fin N → ℝ} (hp : ∀ i, 4 < p i) :
    (trace (probeGram p * probeGram p)).re =
      ∑ i, ∑ j, ((probeSymbol (p i) + probeSymbol (p j)) / (p i + p j)) ^ 2 := by
  rw [trace_square (probeGram_isHermitian (fun i => by linarith only [hp i]))]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [probeGram, bareMixedEnergy_probe (by linarith only [hp i])
    (by linarith only [hp j])]
  simp only [Complex.normSq_apply, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, add_zero, pow_two]

/-- The clipped confinement energy is controlled by bare arithmetic energy and
one cutoff square for each negative direction of the confined form. -/
theorem clipped_probe_negative_index {R : ℝ} (hR : 0 < R)
    {N : ℕ} {p : Fin N → ℝ} (hp : ∀ i, 4 < p i) (c : ℝ) :
    energy c (probeConfinementBlock R p) - 2 * c * (trace (confinedProbeGram R p)).re -
      c ^ 2 * hermNegIndex (confinedProbeGram R p) ≤
        ∑ i, ∑ j, ((probeSymbol (p i) + probeSymbol (p j)) / (p i + p j)) ^ 2 := by
  have hK := confinedProbeGram_isHermitian hR hp
  have h := threshold (probeConfinementBlock_posSemidef hR hp) hK.neg c
  have hi : RiemannGaussian.HermitianRankTrace.posIndex hK.neg =
      hermNegIndex (confinedProbeGram R p) :=
    (posIndex_eq_card_pos_eigenvalues hK.neg).symm
  have he : probeConfinementBlock R p + -confinedProbeGram R p = -probeGram p := by
    rw [confinedProbeGram_eq R hp]
    change probeConfinementBlock R p + -(probeGram p + probeConfinementBlock R p) = _
    abel
  rw [hi, he, neg_mul_neg, Matrix.trace_neg, Complex.neg_re,
    probeGram_trace_square hp] at h
  linarith only [h]

/-- The same index bound for arbitrary finite families of complex probe combinations.
Compression cannot create negative directions, so the original index pays the penalty. -/
theorem clipped_compressed_probe_negative_index {R : ℝ} (hR : 0 < R)
    {N M : ℕ} {p : Fin N → ℝ} (hp : ∀ i, 4 < p i)
    (V : Matrix (Fin M) (Fin N) ℂ) (c : ℝ) :
    energy c (V * probeConfinementBlock R p * Vᴴ) -
      2 * c * (trace (V * confinedProbeGram R p * Vᴴ)).re -
      c ^ 2 * hermNegIndex (confinedProbeGram R p) ≤
        ∑ i, ∑ j, Complex.normSq ((V * probeGram p * Vᴴ) i j) := by
  have hK := Matrix.isHermitian_mul_mul_conjTranspose V (confinedProbeGram_isHermitian hR hp)
  have hB := Matrix.isHermitian_mul_mul_conjTranspose V
    (probeGram_isHermitian (p := p) (fun i => by linarith only [hp i]))
  have h := threshold ((probeConfinementBlock_posSemidef hR hp).mul_mul_conjTranspose_same V)
    hK.neg c
  have hi : RiemannGaussian.HermitianRankTrace.posIndex hK.neg =
      hermNegIndex (V * confinedProbeGram R p * Vᴴ) :=
    (posIndex_eq_card_pos_eigenvalues hK.neg).symm
  have he : V * probeConfinementBlock R p * Vᴴ + -(V * confinedProbeGram R p * Vᴴ) =
      -(V * probeGram p * Vᴴ) := by
    rw [confinedProbeGram_eq R hp, Matrix.mul_add, Matrix.add_mul]
    change V * probeConfinementBlock R p * Vᴴ +
      -(V * probeGram p * Vᴴ + V * probeConfinementBlock R p * Vᴴ) = _
    abel
  rw [hi, he, neg_mul_neg, Matrix.trace_neg, Complex.neg_re, trace_square hB] at h
  have hindex : (hermNegIndex (V * confinedProbeGram R p * Vᴴ) : ℝ) ≤
      hermNegIndex (confinedProbeGram R p) := by
    exact_mod_cast hermNegIndex_mul_mul_conjTranspose_le V (confinedProbeGram R p)
  have hc := mul_le_mul_of_nonneg_left hindex (sq_nonneg c)
  linarith only [h, hc]

/-- Each additional cutoff-square excess forces another zero right of the critical line. -/
theorem rightZero_count_of_clipped_excess {R : ℝ} (hR : 0 < R)
    {N M : ℕ} {p : Fin N → ℝ} (hp : ∀ i, 4 < p i)
    (V : Matrix (Fin M) (Fin N) ℂ) (c : ℝ) (m : ℕ)
    (hexcess : (∑ i, ∑ j, Complex.normSq ((V * probeGram p * Vᴴ) i j)) +
      c ^ 2 * m < energy c (V * probeConfinementBlock R p * Vᴴ) -
        2 * c * (trace (V * confinedProbeGram R p * Vᴴ)).re) :
    ((m + 1 : ℕ) : ℕ∞) ≤ (rightZeros Zeta23.zetaZeroConfig).encard := by
  have h := clipped_compressed_probe_negative_index hR hp V c
  have hlt : m < hermNegIndex (confinedProbeGram R p) := by
    by_contra hn
    have hcard : (hermNegIndex (confinedProbeGram R p) : ℝ) ≤ m := by
      exact_mod_cast Nat.le_of_not_gt hn
    have hc := mul_le_mul_of_nonneg_left hcard (sq_nonneg c)
    linarith only [h, hexcess, hc]
  exact (ENat.coe_le_coe.mpr (Nat.succ_le_of_lt hlt)).trans
    (hermNegIndex_confinedProbeGram_le hR hp)

/-- The retained clipped term dominates the former affine rank–trace estimate. -/
theorem probeConfinement_clipped_dominates_rank {R : ℝ} (hR : 0 < R)
    {N M : ℕ} {p : Fin N → ℝ} (hp : ∀ i, 4 < p i)
    (V : Matrix (Fin M) (Fin N) ℂ) (c : ℝ≥0) :
    (c : ℝ) * (trace (V * probeConfinementBlock R p * Vᴴ)).re -
      (c : ℝ) ^ 2 / 4 * (V * probeConfinementBlock R p * Vᴴ).rank ≤
        energy c (V * probeConfinementBlock R p * Vᴴ) :=
  rank_lower_bound
    ((probeConfinementBlock_posSemidef hR hp).mul_mul_conjTranspose_same V).isHermitian c

/-- Below the global threshold every finite confined probe matrix has zero negative index. -/
theorem confinedProbeGram_index_zero_of_le_threshold {R : ℝ} (hR : 0 < R)
    (hle : (R : EReal) ≤ ⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A)
    {N : ℕ} {p : Fin N → ℝ} (hp : ∀ i, 4 < p i) :
    hermNegIndex (confinedProbeGram R p) = 0 := by
  have hreal (x : Fin N → ℝ) :
      hermQuad (confinedProbeGram R p) (fun i => (x i : ℂ)) =
        criticalHalfLineFullEnergy R (probeSum p x) := by
    rw [criticalHalfLineFullEnergy_probeSum R hp]
    change hermQuad (fun i j => (criticalHalfLineMixedEnergy R
      (probe (p i)) (probe (p j)) : ℂ)) (fun i => (x i : ℂ)) = _
    rw [hermQuad_ofReal_eq]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hnn (x : Fin N → ℂ) : 0 ≤ hermQuad (confinedProbeGram R p) x := by
    rw [hermQuad_eq_re_add_im (G := confinedProbeGram R p)
      (fun _ _ => Complex.ofReal_im _), hreal, hreal]
    apply add_nonneg
    · exact fullEnergy_nonneg_of_le_iInf hR hle
        (criticalHalfLineEnergyDomain_finsetSum _
          (fun i => criticalHalfLineEnergyDomain_probe (hp i)) _)
    · exact fullEnergy_nonneg_of_le_iInf hR hle
        (criticalHalfLineEnergyDomain_finsetSum _
          (fun i => criticalHalfLineEnergyDomain_probe (hp i)) _)
  have hK := confinedProbeGram_isHermitian hR hp
  rw [negIndex_eq_card_neg_eigenvalues hK]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt]
  intro i
  rw [hK.eigenvalues_eq]
  exact hnn _

/-- At the actual critical ratio the index penalty disappears, giving a necessary
arithmetic bound on every finite probe family. -/
theorem criticalRatio_clipped_probe_bound {W₀ : ℝ} (hW : 0 < W₀)
    (ht : (⨅ (A : ℝ) (_ : 0 ≤ A), windowThreshold A) = (W₀ : EReal))
    {N M : ℕ} {p : Fin N → ℝ} (hp : ∀ i, 4 < p i)
    (V : Matrix (Fin M) (Fin N) ℂ) (c : ℝ) :
    energy c (V * probeConfinementBlock W₀ p * Vᴴ) -
      2 * c * (trace (V * confinedProbeGram W₀ p * Vᴴ)).re ≤
        ∑ i, ∑ j, Complex.normSq ((V * probeGram p * Vᴴ) i j) := by
  have h := clipped_compressed_probe_negative_index hW hp V c
  rw [confinedProbeGram_index_zero_of_le_threshold hW ht.ge hp,
    Nat.cast_zero, mul_zero, sub_zero] at h
  exact h

#print axioms clipped_probe_negative_index
#print axioms clipped_compressed_probe_negative_index
#print axioms rightZero_count_of_clipped_excess
#print axioms probeConfinement_clipped_dominates_rank
#print axioms criticalRatio_clipped_probe_bound

end
end GaloisForLFunctions.ExclusionOfTheCriticalState
