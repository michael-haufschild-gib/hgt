import GaloisForLFunctions.HTGeometry.WoldThermofieldStandardForm
import GaloisForLFunctions.HTGeometry.CanonicalThermalReesFormationField
import GaloisForLFunctions.HTGeometry.ConstitutiveThetaHasseKMSExecutionBalance
import Mathlib

/-!
# Thermal radiation as a concrete corpus thermofield state

Equations (23)--(26) of arXiv:2601.07437 specialize the corpus geometric
occupation and Rees thermal laws. The inverse temperature-frequency product is
`exp tau`, so the infinite state is normalized and nontrivial for every real
parameter, without summability or positivity premises.
-/
noncomputable section
namespace GaloisForLFunctions.HTGeometry.CPV
open scoped BigOperators

/-- Thermal occupation ratio with strictly positive inverse thermal scale. -/
def thermalRatio (tau : ℝ) : ℝ := Real.exp (-Real.exp tau)

theorem thermalRatio_pos (tau : ℝ) : 0 < thermalRatio tau := Real.exp_pos _
theorem thermalRatio_lt_one (tau : ℝ) : thermalRatio tau < 1 := by
  unfold thermalRatio
  exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos (Real.exp_pos tau))

/-- The emitted number distribution, using the existing Rees thermal mass. -/
def radiationMass (tau : ℝ) : ℕ → ℝ := canonicalThermalMass (thermalRatio tau)

/-- The Rees mass and the Wold occupation law coincide at the physical thermal ratio. -/
theorem radiationMass_eq_occupation (tau : ℝ) :
    radiationMass tau = geometricOccupationProbability (thermalRatio tau) := rfl

theorem radiationMass_pos (tau : ℝ) (n : ℕ) : 0 < radiationMass tau n := by
  unfold radiationMass canonicalThermalMass
  exact mul_pos (sub_pos.mpr (thermalRatio_lt_one tau)) (pow_pos (thermalRatio_pos tau) n)

/-- The full infinite number distribution has mass one. -/
theorem radiationMass_hasSum (tau : ℝ) : HasSum (radiationMass tau) 1 := by
  have h := (hasSum_geometric_of_lt_one (thermalRatio_pos tau).le
    (thermalRatio_lt_one tau)).mul_left (1 - thermalRatio tau)
  have hn : 1 - thermalRatio tau ≠ 0 := ne_of_gt (sub_pos.mpr (thermalRatio_lt_one tau))
  convert! h using 1
  simp [hn]

/-- Exact detailed balance between successive occupation levels. -/
theorem radiationMass_successor (tau : ℝ) (n : ℕ) :
    radiationMass tau (n + 1) = Real.exp (-Real.exp tau) * radiationMass tau n := by
  unfold radiationMass canonicalThermalMass thermalRatio
  rw [pow_succ]
  ring

/-- Unit half-density supplied by the existing infinite-dimensional occupation space. -/
def radiationVector (tau : ℝ) : lp (fun _ : ℕ => ℂ) 2 :=
  geometricOccupationHalfDensity (thermalRatio tau) (thermalRatio_pos tau).le
    (thermalRatio_lt_one tau)

@[simp] theorem radiationVector_apply (tau : ℝ) (n : ℕ) :
    radiationVector tau n = (Real.sqrt (radiationMass tau n) : ℂ) := rfl

/-- The infinite occupation vector is genuinely normalized. -/
theorem radiationVector_norm_sq (tau : ℝ) : ‖radiationVector tau‖ ^ 2 = 1 :=
  norm_sq_geometricOccupationHalfDensity _ _

/-- Two-mode purification, realized as an existing Hilbert--Schmidt kernel. -/
def radiationPair (tau : ℝ) : ℕ × ℕ → ℂ := thermofieldDiagonalKernel (radiationVector tau)

/-- Square summability is proved, rather than assumed as a state interface. -/
theorem radiationPair_isHS (tau : ℝ) : HilbertSchmidt.IsHS (radiationPair tau) :=
  thermofieldDiagonalKernel_isHS _

/-- The complete two-mode state has norm one. -/
theorem radiationPair_norm_sq (tau : ℝ) : HilbertSchmidt.hsNormSq (radiationPair tau) = 1 := by
  rw [radiationPair, hsNormSq_thermofieldDiagonalKernel, radiationVector_norm_sq]

/-- The Page--Wootters energy-difference constraint for every diagonal spectrum. -/
theorem radiationPair_stationary (tau : ℝ) (E : ℕ → ℂ) :
    thermofieldLeftAction E (radiationPair tau) -
      thermofieldRightAction E (radiationPair tau) = 0 := by
  rw [radiationPair, thermofieldDiagonalKernel_central, sub_self]

/-- The actual partial-trace kernel of the two-mode pure state. -/
def radiationReduced (tau : ℝ) (i j : ℕ) : ℂ :=
  ∑' k, radiationPair tau (i, k) * star (radiationPair tau (j, k))

/-- Tracing out either partner gives exactly the thermal diagonal density. -/
theorem radiationReduced_eq (tau : ℝ) (i j : ℕ) :
    radiationReduced tau i j = if i = j then (radiationMass tau i : ℂ) else 0 := by
  rw [radiationReduced, tsum_eq_single i]
  · by_cases h : i = j
    · subst j
      simp only [radiationPair, thermofieldDiagonalKernel, ite_true, radiationVector_apply,
        Complex.star_def, Complex.conj_ofReal, ← Complex.ofReal_mul]
      rw [← sq, Real.sq_sqrt (radiationMass_pos tau i).le]
    · simp [radiationPair, thermofieldDiagonalKernel, h, Ne.symm h]
  · intro k hk
    simp [radiationPair, thermofieldDiagonalKernel, Ne.symm hk]

/-- The reduced state's trace is one. -/
theorem radiationReduced_trace (tau : ℝ) :
    (∑' i, radiationReduced tau i i) = 1 := by
  simp only [radiationReduced_eq, ite_true]
  rw [← Complex.ofReal_tsum, (radiationMass_hasSum tau).tsum_eq, Complex.ofReal_one]

/-- A nonzero two-by-two minor witnesses entanglement at every thermal scale. -/
theorem radiationPair_minor_ne_zero (tau : ℝ) :
    radiationPair tau (0, 0) * radiationPair tau (1, 1) -
      radiationPair tau (0, 1) * radiationPair tau (1, 0) ≠ 0 := by
  simp only [radiationPair, thermofieldDiagonalKernel, radiationVector_apply,
    Nat.zero_ne_one, Nat.one_ne_zero, ite_true, ite_false, mul_zero, sub_zero]
  apply mul_ne_zero <;> exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (radiationMass_pos tau _)))

/-- No factorization into a pair of one-mode wavefunctions exists. -/
theorem radiationPair_not_product (tau : ℝ) :
    ¬ ∃ f g : ℕ → ℂ, ∀ i j, radiationPair tau (i, j) = f i * g j := by
  rintro ⟨f, g, h⟩
  apply radiationPair_minor_ne_zero tau
  rw [h, h, h, h]
  ring

/-- Exact purity of the thermal reduced state. -/
theorem radiationMass_purity (tau : ℝ) :
    (∑' n, radiationMass tau n ^ 2) =
      (1 - thermalRatio tau) / (1 + thermalRatio tau) := by
  exact tsum_sq_geometricLayerMass (thermalRatio_pos tau).le (thermalRatio_lt_one tau)

/-- The radiation is strictly mixed, despite its pure two-mode purification. -/
theorem radiationMass_purity_lt_one (tau : ℝ) :
    (∑' n, radiationMass tau n ^ 2) < 1 := by
  rw [radiationMass_purity]
  apply (div_lt_one (by linarith [thermalRatio_pos tau] : 0 < 1 + thermalRatio tau)).mpr
  linarith [thermalRatio_pos tau]

/-- Mean occupation from the convergent weighted geometric series. -/
theorem radiationMass_mean (tau : ℝ) :
    HasSum (fun n : ℕ => (n : ℝ) * radiationMass tau n)
      (thermalRatio tau / (1 - thermalRatio tau)) := by
  have hs := AbelianZetaParameters.summable_natCast_mul_geometric
    (thermalRatio_pos tau).le (thermalRatio_lt_one tau)
  have ht := AbelianZetaParameters.tsum_natCast_mul_geometric
    (thermalRatio_pos tau).le (thermalRatio_lt_one tau)
  convert! hs.hasSum using 1
  · funext n
    unfold radiationMass canonicalThermalMass
    ring
  · exact ht.symm

/-- The Bose occupation formula at the effective inverse thermal scale. -/
theorem radiationMass_bose_mean (tau : ℝ) :
    (∑' n : ℕ, (n : ℝ) * radiationMass tau n) = 1 / (Real.exp (Real.exp tau) - 1) := by
  rw [(radiationMass_mean tau).tsum_eq]
  unfold thermalRatio
  rw [Real.exp_neg]
  have he : Real.exp (Real.exp tau) ≠ 1 := ne_of_gt (Real.one_lt_exp_iff.mpr (Real.exp_pos tau))
  field_simp

/-- Radiation entropy is the corpus KMS entropy of the same geometric state. -/
theorem radiationMass_entropy (tau : ℝ) :
    (∑' n, -radiationMass tau n * Real.log (radiationMass tau n)) =
      -Real.log (1 - thermalRatio tau) +
        Real.exp tau * thermalRatio tau / (1 - thermalRatio tau) := by
  have h := tsum_geometricLayerShannonTerm (thermalRatio_pos tau) (thermalRatio_lt_one tau)
  change (∑' n, geometricLayerShannonTerm (thermalRatio tau) n) = _
  rw [h, geometricExecutionEntropy]
  have hl : Real.log (thermalRatio tau) = -Real.exp tau := by
    simp [thermalRatio]
  rw [hl]
  ring

/-- The corpus collision-loss observable is exactly radiation linear entropy. -/
theorem radiationMass_collision_loss (tau : ℝ) :
    geometricExecutionTV (thermalRatio tau) = 1 - ∑' n, radiationMass tau n ^ 2 :=
  geometricExecutionTV_eq_one_sub_purity (thermalRatio_pos tau).le (thermalRatio_lt_one tau)

end GaloisForLFunctions.HTGeometry.CPV
