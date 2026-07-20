import GaloisForLFunctions.HilbertMetric.QuadraticGraphCompletion

/-!
# Transverse-degree Fano phase law

This module formalizes the finite Hilbert-coordinate core of the transverse-degree phase
transition.  A top Fock channel of degree `M`, completed by an orthogonal one-particle channel,
has Gram determinant `(t ^ M + λ ^ 2 * t) ^ k`.  Its degree gap is therefore `M - 1`.

The exact square completion below shows that the sign of the mean-minus-variance margin is
controlled by one quantity: the lowering charge per top direction minus `M * (M - 4) / 4`.
The degree-five, base-dimension-sixteen specialization has strictly negative margin.  These are
unconditional algebraic theorems; the coherent-collision connector is kept in the paper card
until its analytic convergence argument is formalized.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HilbertMetric

noncomputable section

section GraphDeterminant

variable {κ : Type*} [Fintype κ]

/-- Gram matrix of an arbitrary graph from a degree-`M` top channel to an orthogonal
one-particle channel. -/
def higherDegreeGraphGram {k : ℕ} (L : Matrix κ (Fin k) ℝ) (M : ℕ) (t : ℝ) :
    Matrix (Fin k) (Fin k) ℝ :=
  standardFeatureGram
    (graphFeatureRow L ((Real.sqrt t) ^ M) (Real.sqrt t))

/-- **Arbitrary higher-degree graph Gram law.** -/
theorem higherDegreeGraphGram_eq {k : ℕ} (L : Matrix κ (Fin k) ℝ)
    (M : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    higherDegreeGraphGram L M t =
      t ^ M • (1 : Matrix (Fin k) (Fin k) ℝ) +
        t • (L.transpose * L) := by
  unfold higherDegreeGraphGram
  rw [standardFeatureGram_graphFeatureRow]
  have htop : ((Real.sqrt t) ^ M) ^ 2 = t ^ M := by
    rw [← pow_mul, Nat.mul_comm M 2, pow_mul, Real.sq_sqrt ht]
  rw [htop, Real.sq_sqrt ht]

/-- Factoring the forced one-particle contribution from an arbitrary higher-degree graph. -/
theorem higherDegreeGraphGram_eq_smul {k : ℕ} (L : Matrix κ (Fin k) ℝ)
    (M : ℕ) (t : ℝ) (ht : 0 ≤ t) (hM : 1 ≤ M) :
    higherDegreeGraphGram L M t =
      t • (t ^ (M - 1) • (1 : Matrix (Fin k) (Fin k) ℝ) + L.transpose * L) := by
  rw [higherDegreeGraphGram_eq L M t ht]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hM
  simp only [Nat.add_sub_cancel_left]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [show 1 + m = m + 1 by omega, pow_succ]
  ring

/-- **Arbitrary higher-degree graph determinant law.**  The residual determinant contains the
whole singular-value geometry of the completion map. -/
theorem det_higherDegreeGraphGram {k : ℕ} (L : Matrix κ (Fin k) ℝ)
    (M : ℕ) (t : ℝ) (ht : 0 ≤ t) (hM : 1 ≤ M) :
    (higherDegreeGraphGram L M t).det =
      t ^ k *
        (t ^ (M - 1) • (1 : Matrix (Fin k) (Fin k) ℝ) + L.transpose * L).det := by
  rw [higherDegreeGraphGram_eq_smul L M t ht hM, Matrix.det_smul]
  simp

/-- Orthogonal coordinates of a degree-`M` top channel and its transverse one-particle
completion. -/
def transverseDegreeFeatureRow {k : ℕ} (M : ℕ) (lam t : ℝ) (i : Fin k) :
    Fin k ⊕ Fin k → ℝ :=
  graphFeatureRow (1 : Matrix (Fin k) (Fin k) ℝ)
    ((Real.sqrt t) ^ M) (lam * Real.sqrt t) i

/-- Gram matrix of `k` orthogonal top directions after transverse completion. -/
def transverseDegreeGram (k M : ℕ) (lam t : ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  standardFeatureGram (transverseDegreeFeatureRow M lam t)

/-- **Transverse graph Gram law.**  Degree `M` and degree `1` channels add orthogonally. -/
theorem transverseDegreeGram_eq (k M : ℕ) (lam t : ℝ) (ht : 0 ≤ t) :
    transverseDegreeGram k M lam t =
      (t ^ M + lam ^ 2 * t) • (1 : Matrix (Fin k) (Fin k) ℝ) := by
  unfold transverseDegreeGram transverseDegreeFeatureRow
  rw [standardFeatureGram_graphFeatureRow]
  simp only [Matrix.transpose_one, Matrix.one_mul]
  have htop : ((Real.sqrt t) ^ M) ^ 2 = t ^ M := by
    rw [← pow_mul, Nat.mul_comm M 2, pow_mul, Real.sq_sqrt ht]
  have hlinear : (lam * Real.sqrt t) ^ 2 = lam ^ 2 * t := by
    rw [mul_pow, Real.sq_sqrt ht]
  rw [htop, hlinear]
  ext i j
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- **Transverse graph determinant law.**  Every orthogonal top direction contributes the
same two-degree factor. -/
theorem det_transverseDegreeGram (k M : ℕ) (lam t : ℝ) (ht : 0 ≤ t) :
    (transverseDegreeGram k M lam t).det =
      (t ^ M + lam ^ 2 * t) ^ k := by
  rw [transverseDegreeGram_eq k M lam t ht, Matrix.det_smul]
  simp

/-- Determinant partition after adjoining a homogeneous lowering skeleton of total degree
`loweringCharge`. -/
def transverseDegreePartition (loweringCharge k M : ℕ) (lam t : ℝ) : ℝ :=
  t ^ loweringCharge * (transverseDegreeGram k M lam t).det

/-- Exact factorization of the transverse-degree determinant partition. -/
theorem transverseDegreePartition_eq (loweringCharge k M : ℕ) (lam t : ℝ)
    (ht : 0 ≤ t) (hM : 1 ≤ M) :
    transverseDegreePartition loweringCharge k M lam t =
      t ^ (loweringCharge + k) * (t ^ (M - 1) + lam ^ 2) ^ k := by
  rw [transverseDegreePartition, det_transverseDegreeGram k M lam t ht]
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hM
  simp only [Nat.add_sub_cancel_left]
  rw [show t ^ (1 + m) + lam ^ 2 * t = t * (t ^ m + lam ^ 2) by
    rw [pow_succ']
    ring]
  rw [mul_pow, ← mul_assoc, ← pow_add]

end GraphDeterminant

section FanoPhase

variable {ι : Type*} [Fintype ι]

/-- Mean degree of a fixed lowering skeleton and arbitrary transverse Bernoulli channels. -/
def transverseChannelMean (loweringCharge topDegree : ℝ) (p : ι → ℝ) : ℝ :=
  loweringCharge + ∑ i, (1 + (topDegree - 1) * p i)

/-- Variance of arbitrary transverse Bernoulli channels, each with jump `topDegree - 1`. -/
def transverseChannelVariance (topDegree : ℝ) (p : ι → ℝ) : ℝ :=
  ∑ i, (topDegree - 1) ^ 2 * p i * (1 - p i)

/-- Mean-minus-variance margin of arbitrary transverse channels. -/
def transverseChannelFanoMargin (loweringCharge topDegree : ℝ) (p : ι → ℝ) : ℝ :=
  transverseChannelMean loweringCharge topDegree p -
    transverseChannelVariance topDegree p

/-- **Universal transverse channel-square law.**  Every singular channel contributes one exact
square around the phase-balancing probability. -/
theorem transverseChannelFanoMargin_square
    (loweringCharge topDegree : ℝ) (p : ι → ℝ) :
    transverseChannelFanoMargin loweringCharge topDegree p =
      loweringCharge +
        ∑ i, (-topDegree * (topDegree - 4) / 4 +
          ((topDegree - 1) * p i - (topDegree - 2) / 2) ^ 2) := by
  unfold transverseChannelFanoMargin transverseChannelMean transverseChannelVariance
  rw [show loweringCharge + (∑ i, (1 + (topDegree - 1) * p i)) -
      ∑ i, (topDegree - 1) ^ 2 * p i * (1 - p i) =
      loweringCharge + ((∑ i, (1 + (topDegree - 1) * p i)) -
        ∑ i, (topDegree - 1) ^ 2 * p i * (1 - p i)) by ring]
  rw [← Finset.sum_sub_distrib]
  apply congrArg (loweringCharge + ·)
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Cardinality form of the channel-square law. -/
theorem transverseChannelFanoMargin_square_card
    (loweringCharge topDegree : ℝ) (p : ι → ℝ) :
    transverseChannelFanoMargin loweringCharge topDegree p =
      loweringCharge - (Fintype.card ι : ℝ) *
          (topDegree * (topDegree - 4) / 4) +
        ∑ i, ((topDegree - 1) * p i - (topDegree - 2) / 2) ^ 2 := by
  rw [transverseChannelFanoMargin_square]
  rw [Finset.sum_add_distrib]
  simp
  ring

/-- The channel squares give the universal sharp lower phase bound. -/
theorem transverseChannelFanoMargin_lower_bound
    (loweringCharge topDegree : ℝ) (p : ι → ℝ) :
    loweringCharge - (Fintype.card ι : ℝ) *
        (topDegree * (topDegree - 4) / 4) ≤
      transverseChannelFanoMargin loweringCharge topDegree p := by
  rw [transverseChannelFanoMargin_square_card]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun i _ => sq_nonneg
      ((topDegree - 1) * p i - (topDegree - 2) / 2))

/-! ### Unequal-gap multichannel law -/

/-- Mean degree of an arbitrary orthogonal graph completion.  Each channel starts at its own
lower degree and makes its own homogeneous degree jump. -/
def unequalGapChannelMean (loweringCharge : ℝ) (lowerDegree gap p : ι → ℝ) : ℝ :=
  loweringCharge + ∑ i, (lowerDegree i + gap i * p i)

/-- Variance of independent Bernoulli channels with channel-dependent degree gaps. -/
def unequalGapChannelVariance (gap p : ι → ℝ) : ℝ :=
  ∑ i, (gap i) ^ 2 * p i * (1 - p i)

/-- Mean-minus-variance margin for an arbitrary unequal-gap graph completion. -/
def unequalGapChannelFanoMargin
    (loweringCharge : ℝ) (lowerDegree gap p : ι → ℝ) : ℝ :=
  unequalGapChannelMean loweringCharge lowerDegree gap p -
    unequalGapChannelVariance gap p

/-- **Unequal-gap channel-square law.**  Every orthogonal graph channel contributes one exact
square, with its lower endpoint charged separately. -/
theorem unequalGapChannelFanoMargin_square
    (loweringCharge : ℝ) (lowerDegree gap p : ι → ℝ) :
    unequalGapChannelFanoMargin loweringCharge lowerDegree gap p =
      loweringCharge +
        ∑ i, (lowerDegree i - (gap i - 1) ^ 2 / 4 +
          (gap i * p i - (gap i - 1) / 2) ^ 2) := by
  unfold unequalGapChannelFanoMargin unequalGapChannelMean unequalGapChannelVariance
  rw [show loweringCharge + (∑ i, (lowerDegree i + gap i * p i)) -
      ∑ i, (gap i) ^ 2 * p i * (1 - p i) =
      loweringCharge + ((∑ i, (lowerDegree i + gap i * p i)) -
        ∑ i, (gap i) ^ 2 * p i * (1 - p i)) by ring]
  rw [← Finset.sum_sub_distrib]
  apply congrArg (loweringCharge + ·)
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Separated form of the unequal-gap law: deterministic lowering budget, sharp phase credit,
and a sum of manifest channel squares. -/
theorem unequalGapChannelFanoMargin_square_separated
    (loweringCharge : ℝ) (lowerDegree gap p : ι → ℝ) :
    unequalGapChannelFanoMargin loweringCharge lowerDegree gap p =
      loweringCharge +
          ∑ i, (lowerDegree i - (gap i - 1) ^ 2 / 4) +
        ∑ i, (gap i * p i - (gap i - 1) / 2) ^ 2 := by
  rw [unequalGapChannelFanoMargin_square]
  rw [Finset.sum_add_distrib]
  ring

/-- The unequal-gap squares give the sharp channelwise phase lower bound. -/
theorem unequalGapChannelFanoMargin_lower_bound
    (loweringCharge : ℝ) (lowerDegree gap p : ι → ℝ) :
    loweringCharge + ∑ i, (lowerDegree i - (gap i - 1) ^ 2 / 4) ≤
      unequalGapChannelFanoMargin loweringCharge lowerDegree gap p := by
  rw [unequalGapChannelFanoMargin_square_separated]
  exact le_add_of_nonneg_right
    (Finset.sum_nonneg fun i _ => sq_nonneg
      (gap i * p i - (gap i - 1) / 2))

/-- Mean degree of a lowering skeleton plus `topCount` identical Bernoulli jumps from degree
`1` to degree `topDegree`. -/
def transverseDegreeMean (loweringCharge topCount topDegree p : ℝ) : ℝ :=
  loweringCharge + topCount + (topDegree - 1) * topCount * p

/-- Variance of `topCount` identical Bernoulli jumps of size `topDegree - 1`. -/
def transverseDegreeVariance (topCount topDegree p : ℝ) : ℝ :=
  (topDegree - 1) ^ 2 * topCount * p * (1 - p)

/-- Mean-minus-variance margin for a transverse-degree completion. -/
def transverseDegreeFanoMargin (loweringCharge topCount topDegree p : ℝ) : ℝ :=
  transverseDegreeMean loweringCharge topCount topDegree p -
    transverseDegreeVariance topCount topDegree p

/-- **Transverse-degree square law.**  The entire Fano margin splits into the lowering-charge
phase term and one manifest square. -/
theorem transverseDegreeFanoMargin_square
    (loweringCharge topCount topDegree p : ℝ) :
    transverseDegreeFanoMargin loweringCharge topCount topDegree p =
      loweringCharge - topCount * (topDegree * (topDegree - 4) / 4) +
        topCount *
          ((topDegree - 1) * p - (topDegree - 2) / 2) ^ 2 := by
  unfold transverseDegreeFanoMargin transverseDegreeMean transverseDegreeVariance
  ring

/-- At the phase-balancing probability, the square term vanishes exactly. -/
theorem transverseDegreeFanoMargin_at_phase
    (loweringCharge topCount topDegree : ℝ) (hdegree : topDegree ≠ 1) :
    transverseDegreeFanoMargin loweringCharge topCount topDegree
        ((topDegree - 2) / (2 * (topDegree - 1))) =
      loweringCharge - topCount * (topDegree * (topDegree - 4) / 4) := by
  rw [transverseDegreeFanoMargin_square]
  have hden : 2 * (topDegree - 1) ≠ 0 :=
    mul_ne_zero (by exact (OfNat.zero_ne_ofNat 2 : (0 : ℝ) ≠ 2).symm)
      (sub_ne_zero.mpr hdegree)
  have hsquare :
      (topDegree - 1) * ((topDegree - 2) / (2 * (topDegree - 1))) -
          (topDegree - 2) / 2 = 0 := by
    field_simp [hden]
    ring
  rw [hsquare]
  ring

/-- **Sharp phase criterion.**  At the balancing scale, super-Poissonity is equivalent to the
lowering charge being smaller than the transverse degree threshold. -/
theorem transverseDegreeFanoMargin_at_phase_lt_zero_iff
    (loweringCharge topCount topDegree : ℝ) (hdegree : topDegree ≠ 1) :
    transverseDegreeFanoMargin loweringCharge topCount topDegree
        ((topDegree - 2) / (2 * (topDegree - 1))) < 0 ↔
      loweringCharge < topCount * (topDegree * (topDegree - 4) / 4) := by
  rw [transverseDegreeFanoMargin_at_phase loweringCharge topCount topDegree hdegree]
  exact sub_lt_zero

/-- Total degree carried by the forced lowering skeleton of the full symmetric top space. -/
def fullTopLoweringCharge (d M : ℕ) : ℕ :=
  ∑ n ∈ Finset.range M, n * Nat.choose (d + n - 1) n

/-- Dimension of the degree-`M` symmetric power on `d` generators. -/
def fullTopCount (d M : ℕ) : ℕ :=
  Nat.choose (d + M - 1) M

/-- The full symmetric lowering charge is one shifted binomial coefficient. -/
theorem fullTopLoweringCharge_eq (d r : ℕ) :
    fullTopLoweringCharge d (r + 2) =
      d * Nat.choose (d + r + 1) r := by
  induction r with
  | zero =>
      simp [fullTopLoweringCharge, Finset.sum_range_succ, Nat.choose_one_right]
  | succ r ihr =>
      rw [show r + 1 + 2 = (r + 2) + 1 by omega]
      rw [fullTopLoweringCharge, Finset.sum_range_succ]
      change fullTopLoweringCharge d (r + 2) +
          (r + 2) * Nat.choose (d + (r + 2) - 1) (r + 2) =
        d * Nat.choose (d + (r + 1) + 1) (r + 1)
      rw [ihr]
      have hsub : d + (r + 2) - 1 = d + r + 1 := by omega
      rw [hsub]
      have hterm := Nat.choose_succ_right_eq (d + r + 1) (r + 1)
      have hsub' : d + r + 1 - (r + 1) = d := by omega
      simp only [hsub'] at hterm
      rw [show r + 1 + 1 = r + 2 by omega] at hterm
      have hterm' :
          (r + 2) * Nat.choose (d + r + 1) (r + 2) =
            d * Nat.choose (d + r + 1) (r + 1) := by
        calc
          _ = Nat.choose (d + r + 1) (r + 2) * (r + 2) := Nat.mul_comm _ _
          _ = Nat.choose (d + r + 1) (r + 1) * d := hterm
          _ = _ := Nat.mul_comm _ _
      rw [hterm']
      rw [← Nat.mul_add]
      rw [show d + (r + 1) + 1 = (d + r + 1) + 1 by omega]
      rw [Nat.choose_succ_succ' (d + r + 1) r]

/-- Integral cross-multiplied form of the full-top lowering-charge density law. -/
theorem fullTopLoweringCharge_cross (d r : ℕ) :
    (d + 1) * fullTopLoweringCharge d (r + 2) =
      (r + 2) * (r + 1) * fullTopCount d (r + 2) := by
  rw [fullTopLoweringCharge_eq]
  unfold fullTopCount
  have hn : d + (r + 2) - 1 = d + r + 1 := by omega
  rw [hn]
  have htop := Nat.choose_succ_right_eq (d + r + 1) (r + 1)
  have htopSub : d + r + 1 - (r + 1) = d := by omega
  simp only [htopSub] at htop
  rw [show r + 1 + 1 = r + 2 by omega] at htop
  have hlower := Nat.choose_succ_right_eq (d + r + 1) r
  have hlowerSub : d + r + 1 - r = d + 1 := by omega
  simp only [hlowerSub] at hlower
  calc
    (d + 1) * (d * Nat.choose (d + r + 1) r) =
        (Nat.choose (d + r + 1) r * (d + 1)) * d := by ac_rfl
    _ = (Nat.choose (d + r + 1) (r + 1) * (r + 1)) * d := by rw [hlower]
    _ = (Nat.choose (d + r + 1) (r + 1) * d) * (r + 1) := by ac_rfl
    _ = (Nat.choose (d + r + 1) (r + 2) * (r + 2)) * (r + 1) := by rw [htop]
    _ = (r + 2) * (r + 1) * Nat.choose (d + r + 1) (r + 2) := by ac_rfl

/-- The full-top lowering-charge density in base dimension `d` and top degree `M`. -/
def fullTopLoweringChargeDensity (d M : ℝ) : ℝ :=
  M * (M - 1) / (d + 1)

/-- The combinatorial lowering charge divided by the symmetric-top dimension is exactly the
closed density used by the phase law. -/
theorem fullTopLoweringCharge_ratio_eq_density (d r : ℕ) (hd : 0 < d) :
    ((fullTopLoweringCharge d (r + 2) : ℕ) : ℝ) /
        ((fullTopCount d (r + 2) : ℕ) : ℝ) =
      fullTopLoweringChargeDensity (d : ℝ) ((r + 2 : ℕ) : ℝ) := by
  have hle : r + 2 ≤ d + (r + 2) - 1 := by omega
  have hcountNat : fullTopCount d (r + 2) ≠ 0 :=
    Nat.ne_of_gt (Nat.choose_pos hle)
  have hcount : ((fullTopCount d (r + 2) : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast hcountNat
  have hd1Nat : d + 1 ≠ 0 := by omega
  have hd1 : (((d + 1 : ℕ) : ℝ)) ≠ 0 := by
    exact_mod_cast hd1Nat
  have hcross := fullTopLoweringCharge_cross d r
  have hcross' :
      fullTopLoweringCharge d (r + 2) * (d + 1) =
        fullTopCount d (r + 2) * (r + 2) * (r + 1) := by
    calc
      _ = (d + 1) * fullTopLoweringCharge d (r + 2) := Nat.mul_comm _ _
      _ = (r + 2) * (r + 1) * fullTopCount d (r + 2) := hcross
      _ = _ := by ac_rfl
  have hratio :
      ((fullTopLoweringCharge d (r + 2) : ℕ) : ℝ) /
          ((fullTopCount d (r + 2) : ℕ) : ℝ) =
        (((r + 2 : ℕ) : ℝ) * ((r + 1 : ℕ) : ℝ)) /
          (((d + 1 : ℕ) : ℝ)) := by
    field_simp [hcount, hd1]
    exact_mod_cast hcross'
  rw [hratio]
  unfold fullTopLoweringChargeDensity
  push_cast
  ring

/-- **Full-top transverse phase law.**  The normalized margin at the balancing scale is the
exact competition between symmetric-power lowering charge and transverse degree. -/
theorem fullTopTransverse_phase_at_balance (d M : ℝ) (hM : M ≠ 1) :
    transverseDegreeFanoMargin (fullTopLoweringChargeDensity d M) 1 M
        ((M - 2) / (2 * (M - 1))) =
      M * (M - 1) / (d + 1) - M * (M - 4) / 4 := by
  rw [transverseDegreeFanoMargin_at_phase _ _ _ hM]
  unfold fullTopLoweringChargeDensity
  ring

/-- **Exact degree-five crossing.**  Base dimension sixteen lies strictly across the
transverse Poisson boundary: the normalized margin is `-5/68`. -/
theorem fifthDegree_sixteenDim_fano_margin :
    transverseDegreeFanoMargin (20 / 17) 1 5 (3 / 8) = -(5 / 68) := by
  unfold transverseDegreeFanoMargin transverseDegreeMean transverseDegreeVariance
  ring

/-- The degree-five, base-dimension-sixteen transverse completion is strictly super-Poisson. -/
theorem fifthDegree_sixteenDim_superPoisson :
    transverseDegreeMean (20 / 17) 1 5 (3 / 8) <
      transverseDegreeVariance 1 5 (3 / 8) := by
  have h := fifthDegree_sixteenDim_fano_margin
  unfold transverseDegreeFanoMargin at h
  linarith

end FanoPhase

end

end GaloisForLFunctions.HilbertMetric
