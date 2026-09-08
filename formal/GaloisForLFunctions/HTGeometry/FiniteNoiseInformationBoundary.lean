import GaloisForLFunctions.HTGeometry.FiniteNoiseMixingApplications

/-!
# Information orientation and the boundary of pattern-dependent noise

Sapienza, arXiv:2608.22463v1, Section 2.2 relates ordinal mixing to entropy and
Jensen--Shannon divergence. Complete uniform mixing increases entropy but
annihilates divergence from uniform; the divergence inequality consequently
has the opposite orientation to the displayed equation (6).

The relative-permutation argument also has a sharp finite boundary: a binary
pattern-dependent flip channel is bistochastic exactly when its two flip rates
agree. Unequal rates increase the collision probability of a uniform input.
-/

open scoped BigOperators NNReal
open Matrix
namespace GaloisForLFunctions.HTGeometry
noncomputable section

/-- Scalar contribution to the finite Jensen--Shannon divergence. -/
def finiteEntropyJensenGap (x y : ℝ≥0) : ℝ :=
  Real.negMulLog (((x : ℝ) + y) / 2) - (Real.negMulLog x + Real.negMulLog y) / 2

/-- Concavity makes each Jensen--Shannon contribution nonnegative. -/
theorem finiteEntropyJensenGap_nonneg (x y : ℝ≥0) : 0 ≤ finiteEntropyJensenGap x y := by
  have h := Real.concaveOn_negMulLog.2 x.property y.property
    (show (0 : ℝ) ≤ 1 / 2 by positivity) (show (0 : ℝ) ≤ 1 / 2 by positivity)
    (show (1 / 2 : ℝ) + 1 / 2 = 1 by ring)
  simp only [smul_eq_mul] at h
  change (1 / 2 : ℝ) * Real.negMulLog (x : ℝ) + (1 / 2 : ℝ) * Real.negMulLog (y : ℝ) ≤
    Real.negMulLog ((1 / 2 : ℝ) * (x : ℝ) + (1 / 2 : ℝ) * (y : ℝ)) at h
  rw [show (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y = ((x : ℝ) + y) / 2 by ring] at h
  unfold finiteEntropyJensenGap
  linarith

/-- A scalar contribution vanishes exactly when the two masses agree. -/
theorem finiteEntropyJensenGap_eq_zero_iff (x y : ℝ≥0) :
    finiteEntropyJensenGap x y = 0 ↔ x = y := by
  constructor
  · intro hz
    by_contra hne
    have hn : (x : ℝ) ≠ (y : ℝ) := fun h => hne (Subtype.ext h)
    have h := Real.strictConcaveOn_negMulLog.2 x.property y.property hn
      (show (0 : ℝ) < 1 / 2 by positivity) (show (0 : ℝ) < 1 / 2 by positivity)
      (show (1 / 2 : ℝ) + 1 / 2 = 1 by ring)
    simp only [smul_eq_mul] at h
    change (1 / 2 : ℝ) * Real.negMulLog (x : ℝ) + (1 / 2 : ℝ) * Real.negMulLog (y : ℝ) <
      Real.negMulLog ((1 / 2 : ℝ) * (x : ℝ) + (1 / 2 : ℝ) * (y : ℝ)) at h
    rw [show (1 / 2 : ℝ) * x + (1 / 2 : ℝ) * y = ((x : ℝ) + y) / 2 by ring] at h
    unfold finiteEntropyJensenGap at hz
    linarith
  · rintro rfl
    unfold finiteEntropyJensenGap
    rw [show ((x : ℝ) + x) / 2 = x by ring]
    ring

variable {ι : Type*} [Fintype ι]

/-- Jensen--Shannon divergence in the corpus's finite probability coordinates. -/
def finiteLawJensenShannon (p q : FiniteProbabilityLaw ι) : ℝ :=
  ∑ i, finiteEntropyJensenGap ⟨p.prob i, p.nonneg i⟩ ⟨q.prob i, q.nonneg i⟩

theorem finiteLawJensenShannon_nonneg (p q : FiniteProbabilityLaw ι) :
    0 ≤ finiteLawJensenShannon p q :=
  Finset.sum_nonneg fun i _ => finiteEntropyJensenGap_nonneg
    ⟨p.prob i, p.nonneg i⟩ ⟨q.prob i, q.nonneg i⟩

/-- Zero divergence is faithful even when some probabilities vanish. -/
theorem finiteLawJensenShannon_eq_zero_iff (p q : FiniteProbabilityLaw ι) :
    finiteLawJensenShannon p q = 0 ↔ p.prob = q.prob := by
  classical
  rw [finiteLawJensenShannon, Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => finiteEntropyJensenGap_nonneg _ _)]
  simp only [Finset.mem_univ, forall_const, finiteEntropyJensenGap_eq_zero_iff]
  constructor
  · intro h
    funext i
    exact congrArg (fun x : ℝ≥0 => (x : ℝ)) (h i)
  · intro h i
    apply Subtype.ext
    exact congrFun h i

/-- Agreement with the existing Shannon-entropy functional. -/
theorem finiteLawJensenShannon_eq_entropy (p q : FiniteProbabilityLaw ι) :
    finiteLawJensenShannon p q =
      entropy (fun i => (p.prob i + q.prob i) / 2) - (entropy p.prob + entropy q.prob) / 2 := by
  change (∑ i, (Real.negMulLog ((p.prob i + q.prob i) / 2) -
    (Real.negMulLog (p.prob i) + Real.negMulLog (q.prob i)) / 2)) = _
  simp only [entropy, tsum_fintype, Real.negMulLog, neg_mul,
    Finset.sum_sub_distrib, ← Finset.sum_div, Finset.sum_add_distrib]


section Uniform
variable [DecidableEq ι] [Nonempty ι]

/-- Complete uniform noise, with both stochastic marginals proved. -/
def uniformNoiseMatrix : doublyStochastic ℝ ι := by
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  refine ⟨fun _ _ => (Fintype.card ι : ℝ)⁻¹, mem_doublyStochastic_iff_sum.mpr
    ⟨fun _ _ => by positivity, ?_, ?_⟩⟩ <;>
    intro i <;> simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hn]

/-- The finite uniform law represented in the same probability simplex. -/
def uniformNoiseLaw : FiniteProbabilityLaw ι where
  prob _ := (Fintype.card ι : ℝ)⁻¹
  nonneg _ := by positivity
  sum_prob := by
    have hn : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀ hn]

/-- Complete uniform noise erases the input distribution. -/
theorem mix_uniformNoise_prob (p : FiniteProbabilityLaw ι) :
    (p.mix uniformNoiseMatrix).prob = (uniformNoiseLaw (ι := ι)).prob := by
  ext i
  change (∑ j, (Fintype.card ι : ℝ)⁻¹ * p.prob j) = (Fintype.card ι : ℝ)⁻¹
  rw [← Finset.mul_sum, p.sum_prob, mul_one]

/-- Divergence from uniform is annihilated, rather than increased, by full mixing. -/
theorem finiteLawJensenShannon_uniformNoise_eq_zero (p : FiniteProbabilityLaw ι) :
    finiteLawJensenShannon (p.mix uniformNoiseMatrix) uniformNoiseLaw = 0 :=
  (finiteLawJensenShannon_eq_zero_iff _ _).mpr (mix_uniformNoise_prob p)

/-- Correct divergence orientation for every finite probability input. -/
theorem finiteLawJensenShannon_uniformNoise_le (p : FiniteProbabilityLaw ι) :
    finiteLawJensenShannon (p.mix uniformNoiseMatrix) uniformNoiseLaw ≤
      finiteLawJensenShannon p uniformNoiseLaw := by
  rw [finiteLawJensenShannon_uniformNoise_eq_zero]
  exact finiteLawJensenShannon_nonneg _ _

/-- The reversed divergence inequality survives only at the already-uniform law. -/
theorem finiteLawJensenShannon_reverse_uniformNoise_iff (p : FiniteProbabilityLaw ι) :
    finiteLawJensenShannon p uniformNoiseLaw ≤
      finiteLawJensenShannon (p.mix uniformNoiseMatrix) uniformNoiseLaw ↔
        p.prob = (uniformNoiseLaw (ι := ι)).prob := by
  rw [finiteLawJensenShannon_uniformNoise_eq_zero]
  constructor
  · intro h
    exact (finiteLawJensenShannon_eq_zero_iff _ _).mp
      (le_antisymm h (finiteLawJensenShannon_nonneg _ _))
  · intro h
    rw [(finiteLawJensenShannon_eq_zero_iff _ _).mpr h]


end Uniform

/-- Independent flip probabilities attached to the two input patterns. -/
def patternDependentBinaryNoise (a b : unitInterval) : Matrix Bool Bool ℝ :=
  fun i j => if j then (if i then 1 - (b : ℝ) else (b : ℝ))
    else (if i then (a : ℝ) else 1 - (a : ℝ))

/-- Such a channel always preserves total mass. -/
theorem patternDependentBinaryNoise_column (a b : unitInterval) (j : Bool) :
    ∑ i, patternDependentBinaryNoise a b i j = 1 := by
  cases j <;> simp only [patternDependentBinaryNoise, Fintype.sum_bool,
    Bool.false_eq_true, if_false, if_true] <;> ring

/-- Relative-pattern symmetry is exactly equality of the two flip rates. -/
theorem patternDependentBinaryNoise_bistochastic_iff (a b : unitInterval) :
    patternDependentBinaryNoise a b ∈ doublyStochastic ℝ Bool ↔ a = b := by
  rw [mem_doublyStochastic_iff_sum]
  constructor
  · intro h
    have hf := h.2.1 false
    simp only [patternDependentBinaryNoise, Fintype.sum_bool, Bool.false_eq_true, if_false, if_true] at hf
    apply Subtype.ext
    linarith
  · rintro rfl
    refine ⟨?_, ?_, patternDependentBinaryNoise_column a a⟩
    · intro i j
      cases i <;> cases j <;> simp only [patternDependentBinaryNoise,
        Bool.false_eq_true, if_false, if_true] <;> linarith [a.property.1, a.property.2]
    · intro i
      cases i <;> simp only [patternDependentBinaryNoise, Fintype.sum_bool,
        Bool.false_eq_true, if_false, if_true] <;> ring

/-- Unequal pattern-dependent noise creates concentration from a uniform input. -/
theorem patternDependentBinaryNoise_uniform_collision (a b : unitInterval) :
    (∑ i, (patternDependentBinaryNoise a b *ᵥ (fun _ => (1 / 2 : ℝ))) i ^ 2) =
      1 / 2 + ((a : ℝ) - (b : ℝ)) ^ 2 / 2 := by
  simp only [Matrix.mulVec, dotProduct, Fintype.sum_bool, patternDependentBinaryNoise,
    Bool.false_eq_true, if_false, if_true]
  ring

end
end GaloisForLFunctions.HTGeometry
