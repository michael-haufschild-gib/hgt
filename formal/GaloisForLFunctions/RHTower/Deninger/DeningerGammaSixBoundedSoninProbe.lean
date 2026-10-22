import GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixFullSourceScalarization
import GaloisForLFunctions.RHTower.BurnolCoPoissonMellinHasse
import GaloisForLFunctions.RHTower.BurnolSoninCompletedJetBridge

/-!
# Bounded Sonin probes of the complete Gamma-six source

Every bounded tensor probe reads the literal complete source as its leading
coefficient times the reciprocal Green diagonal plus a summable correction.
The diagonal is summable exactly when that coefficient is zero. Prime-pair
cyclicity for the fixed open Gibbs reader forces the same vanishing.

Pulling back Burnol's actual completed-Mellin evaluation vectors through any
bounded quotient map makes this an obstruction in the physical quotient:
simultaneous prime cyclicity forces the image of the leading tensor to zero.
Every finite literal completed-Mellin jet on the extended Sonin carrier has
the same exact principal-coefficient classification.

No source-to-Sonin map or cyclicity law is assumed as an RH input or constructed
here. The zero-leading case can retain a nonzero complete remainder. Singular
comparisons and the identification with Xi divisor jets remain open.
-/

namespace RHTower
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

abbrev DeningerGammaSixBoundedProbe := DeningerGammaSixTensorSourceL2 →L[ℂ] ℂ

def deningerGammaSixProbeColumn (L : DeningerGammaSixBoundedProbe) (n : ℕ) : ℂ :=
  (deningerGammaSixShellFlattening n : ℂ) *
    L (deningerGammaSixSourceTensorSquare (deningerGammaSixShellHonestDepth n))

def deningerGammaSixProbeRemainder (L : DeningerGammaSixBoundedProbe) (n : ℕ) : ℂ :=
  (deningerGammaSixShellFlattening n : ℂ) * L (deningerGammaSixSourceTensorRemainderColumn n)

/-- The whole tensor source, including its full remainder, is evaluated by the same probe. -/
theorem deningerGammaSixProbeColumn_decomposition
    (L : DeningerGammaSixBoundedProbe) (n : ℕ) :
    deningerGammaSixProbeColumn L n =
      L deningerGammaSixLeadingTensorVector * ((n : ℂ) + 216)⁻¹ +
        deningerGammaSixProbeRemainder L n := by
  have hp : (deningerGammaSixShellFlattening n : ℂ) *
      (deningerGammaSixShellEigenvalue n : ℂ) = ((n : ℂ) + 216)⁻¹ := by
    have hh := congrArg Complex.ofReal (deningerGammaSixShellFlattening_principal n)
    push_cast at hh
    exact hh
  have hpcol : L (deningerGammaSixSourceTensorPrincipal
      (deningerGammaSixShellHonestDepth n)) =
      (deningerGammaSixShellEigenvalue n : ℂ) * L deningerGammaSixLeadingTensorVector := by
    rw [deningerGammaSixSourceTensorPrincipal_eq, map_smul]
    rfl
  unfold deningerGammaSixProbeColumn deningerGammaSixProbeRemainder
    deningerGammaSixSourceTensorRemainderColumn deningerGammaSixSourceTensorRemainder
  rw [map_sub, hpcol]
  linear_combination L deningerGammaSixLeadingTensorVector * hp

theorem norm_deningerGammaSixProbeRemainder_le
    (L : DeningerGammaSixBoundedProbe) (n : ℕ) :
    ‖deningerGammaSixProbeRemainder L n‖ ≤ ‖L‖ * ‖deningerGammaSixSourceTensorRemainderColumn n‖ := by
  unfold deningerGammaSixProbeRemainder
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (deningerGammaSixShellFlattening_pos n)]
  exact (mul_le_of_le_one_left (norm_nonneg _)
    (deningerGammaSixShellFlattening_bounds n).2).trans (L.le_opNorm _)

theorem summable_deningerGammaSixProbeRemainder (L : DeningerGammaSixBoundedProbe) :
    Summable (deningerGammaSixProbeRemainder L) :=
  Summable.of_norm_bounded
    (summable_norm_deningerGammaSixSourceTensorRemainderColumn.mul_left ‖L‖)
    (norm_deningerGammaSixProbeRemainder_le L)

def deningerGammaSixProbeNatColumn (L : DeningerGammaSixBoundedProbe) (k : ℕ) : ℂ :=
  if 216 ≤ k then deningerGammaSixProbeColumn L (k - 216) else 0

def deningerGammaSixProbeDiagonal (L : DeningerGammaSixBoundedProbe) (k : PNat) : ℂ :=
  deningerGammaSixProbeNatColumn L k

/-- The finite omitted head is part of the summable correction. -/
theorem summable_deningerGammaSixProbeDiagonal_sub_principal (L : DeningerGammaSixBoundedProbe) :
    Summable (fun k : PNat => deningerGammaSixProbeDiagonal L k -
      L deningerGammaSixLeadingTensorVector * (((k : ℕ) : ℂ))⁻¹) := by
  apply (summable_pnat_iff_summable_nat
    (f := fun k : ℕ => deningerGammaSixProbeNatColumn L k -
      L deningerGammaSixLeadingTensorVector * (k : ℂ)⁻¹)).2
  apply (summable_nat_add_iff 216).1
  refine (summable_deningerGammaSixProbeRemainder L).congr (fun n => ?_)
  have hn : 216 ≤ n + 216 := by omega
  rw [deningerGammaSixProbeNatColumn, if_pos hn, Nat.add_sub_cancel,
    deningerGammaSixProbeColumn_decomposition]
  push_cast
  ring

theorem not_summable_deningerOrdinaryIntegerReciprocal :
    ¬ Summable (fun k : PNat => (((k : ℕ) : ℂ))⁻¹) := by
  intro hQ
  have hmass : Summable (fun k : PNat => (deningerOrdinaryIntegerGibbsMass (1 / 2) k : ℂ)) := by
    refine hQ.congr fun k => ?_
    norm_num [deningerOrdinaryIntegerGibbsMass, Real.rpow_neg_one]
  have hbad := (summable_deningerOrdinaryIntegerGibbsMass_iff (1 / 2)).1
    (Complex.summable_ofReal.mp hmass)
  exact (lt_irrefl (1 / 2 : ℝ)) hbad

/-- Sharp scalar source-class criterion for every bounded tensor probe. -/
theorem summable_deningerGammaSixProbeDiagonal_iff (L : DeningerGammaSixBoundedProbe) :
    Summable (deningerGammaSixProbeDiagonal L) ↔ L deningerGammaSixLeadingTensorVector = 0 := by
  constructor
  · intro h
    have hc := h.sub (summable_deningerGammaSixProbeDiagonal_sub_principal L)
    by_contra hn
    apply not_summable_deningerOrdinaryIntegerReciprocal
    refine (hc.mul_left (L deningerGammaSixLeadingTensorVector)⁻¹).congr (fun k => ?_)
    simp only [sub_sub_cancel]
    field_simp
  · intro h
    simpa only [h, zero_mul, sub_zero] using
      summable_deningerGammaSixProbeDiagonal_sub_principal L

def deningerGammaSixProbeOperator (L : DeningerGammaSixBoundedProbe) : DeningerOrdinaryIntegerEnd where
  toFun x k := deningerGammaSixProbeDiagonal L k * x k
  map_add' x y := by funext k; exact mul_add _ _ _
  map_smul' c x := by funext k; change _ * (c * x k) = c * (_ * x k); ring

theorem deningerGammaSixProbeOperator_diagonal (L : DeningerGammaSixBoundedProbe) (k : PNat) :
    deningerOrdinaryIntegerDiagonalCoefficient k (deningerGammaSixProbeOperator L) =
      deningerGammaSixProbeDiagonal L k := by
  change deningerGammaSixProbeDiagonal L k * deningerOrdinaryIntegerBasisVector k k = _
  rw [deningerOrdinaryIntegerBasisVector_self, mul_one]

theorem deningerGammaSixProbeOperator_smul (L : DeningerGammaSixBoundedProbe) (c : ℂ) :
    deningerGammaSixProbeOperator (c • L) = c • deningerGammaSixProbeOperator L := by
  ext x k
  change deningerGammaSixProbeNatColumn (c • L) (k : ℕ) * x k =
    c * (deningerGammaSixProbeNatColumn L (k : ℕ) * x k)
  simp only [deningerGammaSixProbeNatColumn, deningerGammaSixProbeColumn,
    smul_apply, smul_eq_mul]
  split_ifs <;> ring

/-- Every bounded full-source probe is admitted in each open Gibbs domain. -/
theorem deningerGammaSixProbeOperator_mem_gibbsDomain
    (L : DeningerGammaSixBoundedProbe) {sigma : ℝ} (h : 1 / 2 < sigma) :
    deningerGammaSixProbeOperator L ∈ deningerOrdinaryIntegerGibbsDomain sigma := by
  have hs := summable_deningerGammaSixProbeDiagonal_sub_principal L
  have hw : Summable (fun k : PNat =>
      ((deningerOrdinaryIntegerGibbsMass sigma k : ℂ) * ((k : ℕ) : ℂ)) *
        (deningerGammaSixProbeDiagonal L k -
          L deningerGammaSixLeadingTensorVector * (((k : ℕ) : ℂ))⁻¹)) := by
    apply Summable.of_norm_bounded hs.norm
    intro k
    rw [norm_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (mul_pos (deningerOrdinaryIntegerGibbsMass_pos sigma k)
        (by exact_mod_cast k.pos))]
    exact mul_le_of_le_one_left (norm_nonneg _) (deningerOrdinaryIntegerGibbsWeight_le_one h.le k)
  have hq : Summable (fun k : PNat => (deningerOrdinaryIntegerGibbsMass sigma k : ℂ)) :=
    Complex.summable_ofReal.mpr ((summable_deningerOrdinaryIntegerGibbsMass_iff sigma).2 h)
  refine ((hq.mul_left (L deningerGammaSixLeadingTensorVector)).add hw).congr (fun k => ?_)
  change L deningerGammaSixLeadingTensorVector * (deningerOrdinaryIntegerGibbsMass sigma k : ℂ) + _ =
    ((deningerOrdinaryIntegerGibbsMass sigma k : ℂ) * ((k : ℕ) : ℂ)) *
      deningerOrdinaryIntegerDiagonalCoefficient k (deningerGammaSixProbeOperator L)
  rw [deningerGammaSixProbeOperator_diagonal]
  have hk : (((k : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast k.ne_zero
  field_simp
  ring

/-- Prime-pair cyclicity is homogeneous on the actual Gibbs domain. -/
theorem deningerOrdinaryIntegerGibbsPrimePairCyclic_smul
    {sigma : ℝ} (h : 1 / 2 < sigma) (T : deningerOrdinaryIntegerGibbsDomain sigma)
    (hc : DeningerOrdinaryIntegerGibbsPrimePairCyclic sigma h T) (c : ℂ) :
    DeningerOrdinaryIntegerGibbsPrimePairCyclic sigma h (c • T) := by
  intro n hn
  have hcomp :
      (⟨deningerOrdinaryIntegerWoldBackward n * ((c • T).val * deningerOrdinaryIntegerWoldShift n),
        deningerOrdinaryIntegerGibbsDomain_compression (c • T) n⟩ : deningerOrdinaryIntegerGibbsDomain sigma) =
      c • ⟨deningerOrdinaryIntegerWoldBackward n * (T.val * deningerOrdinaryIntegerWoldShift n),
        deningerOrdinaryIntegerGibbsDomain_compression T n⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, smul_mul_assoc, mul_smul_comm]
  have hproj :
      (⟨(c • T).val * deningerOrdinaryIntegerDivisibilityProjection n,
        deningerOrdinaryIntegerGibbsDomain_rightProjection (c • T) n⟩ : deningerOrdinaryIntegerGibbsDomain sigma) =
      c • ⟨T.val * deningerOrdinaryIntegerDivisibilityProjection n,
        deningerOrdinaryIntegerGibbsDomain_rightProjection T n⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, smul_mul_assoc]
  rw [hcomp, hproj, map_smul, map_smul, hc n hn]

/-- Every bounded probe with nonzero leading coefficient fails the prime tests. -/
theorem deningerGammaSixProbe_prime_cyclic_leading_zero
    (L : DeningerGammaSixBoundedProbe) (sigma : ℝ) (h : 1 / 2 < sigma)
    (hc : DeningerOrdinaryIntegerGibbsPrimePairCyclic sigma h
      ⟨deningerGammaSixProbeOperator L, deningerGammaSixProbeOperator_mem_gibbsDomain L h⟩) :
    L deningerGammaSixLeadingTensorVector = 0 := by
  by_contra hn
  let c := L deningerGammaSixLeadingTensorVector
  let M : DeningerGammaSixBoundedProbe := c⁻¹ • L
  have hm : M deningerGammaSixLeadingTensorVector = 1 := by
    change c⁻¹ * c = 1
    exact inv_mul_cancel₀ hn
  let T : deningerOrdinaryIntegerGibbsDomain sigma :=
    ⟨deningerGammaSixProbeOperator L, deningerGammaSixProbeOperator_mem_gibbsDomain L h⟩
  have heq :
      (⟨deningerGammaSixProbeOperator M, deningerGammaSixProbeOperator_mem_gibbsDomain M h⟩ :
        deningerOrdinaryIntegerGibbsDomain sigma) = c⁻¹ • T := by
    apply Subtype.ext
    exact deningerGammaSixProbeOperator_smul L c⁻¹
  apply deningerOrdinaryIntegerGibbs_no_summable_prime_cyclic_green_repair sigma h
  refine ⟨⟨deningerGammaSixProbeOperator M, deningerGammaSixProbeOperator_mem_gibbsDomain M h⟩, ?_, ?_⟩
  · simpa only [map_sub, deningerGammaSixProbeOperator_diagonal,
      deningerOrdinaryIntegerDiagonalCoefficient_reciprocalGreen, hm, one_mul] using
        summable_deningerGammaSixProbeDiagonal_sub_principal M
  · rw [heq]
    exact deningerOrdinaryIntegerGibbsPrimePairCyclic_smul h T hc c⁻¹

/-- Complete-source summability is necessary for a bounded probe to pass every prime test. -/
theorem deningerGammaSixProbe_prime_cyclic_summable
    (L : DeningerGammaSixBoundedProbe) (sigma : ℝ) (h : 1 / 2 < sigma)
    (hc : DeningerOrdinaryIntegerGibbsPrimePairCyclic sigma h
      ⟨deningerGammaSixProbeOperator L, deningerGammaSixProbeOperator_mem_gibbsDomain L h⟩) :
    Summable (deningerGammaSixProbeDiagonal L) :=
  (summable_deningerGammaSixProbeDiagonal_iff L).2
    (deningerGammaSixProbe_prime_cyclic_leading_zero L sigma h hc)

/-- Pullback of an actual completed-Mellin evaluation vector, with its physical aperture fixed. -/
def deningerGammaSixSoninMellinProbe
    (b : Set.Ioi (0 : ℝ))
    (B : DeningerGammaSixTensorSourceL2 →L[ℂ] burnolCoPoissonQuotientSpace (b : ℝ))
    (w : BurnolRightStrip) : DeningerGammaSixBoundedProbe :=
  (innerSL ℂ (burnolCoPoissonQuotientEvaluationVector (w : ℂ) (b : ℝ)
    w.property.1 w.property.2 b.property)).comp B

theorem deningerGammaSixSoninMellinProbe_apply
    (b : Set.Ioi (0 : ℝ))
    (B : DeningerGammaSixTensorSourceL2 →L[ℂ] burnolCoPoissonQuotientSpace (b : ℝ))
    (w : BurnolRightStrip) (v : DeningerGammaSixTensorSourceL2) :
    deningerGammaSixSoninMellinProbe b B w v =
      burnolCoPoissonMellinProfile b (B v) w := by
  change inner ℂ (burnolCoPoissonQuotientEvaluationVector (w : ℂ) (b : ℝ)
    w.property.1 w.property.2 b.property) (B v) = _
  rw [inner_burnolCoPoissonQuotientEvaluationVector, burnolCoPoissonMellinProfile_apply]

/-- The real part of each actual Mellin point sets its own fixed Gibbs reader. -/
def DeningerGammaSixSoninMellinPrimeCyclic
    (b : Set.Ioi (0 : ℝ))
    (B : DeningerGammaSixTensorSourceL2 →L[ℂ] burnolCoPoissonQuotientSpace (b : ℝ)) : Prop :=
  ∀ w : BurnolRightStrip,
    DeningerOrdinaryIntegerGibbsPrimePairCyclic (w : ℂ).re w.property.1
      ⟨deningerGammaSixProbeOperator (deningerGammaSixSoninMellinProbe b B w),
        deningerGammaSixProbeOperator_mem_gibbsDomain _ w.property.1⟩

/-- Simultaneous physical prime cyclicity destroys the leading vector in the actual quotient. -/
theorem deningerGammaSixSoninMellinPrimeCyclic_leading_zero
    (b : Set.Ioi (0 : ℝ))
    (B : DeningerGammaSixTensorSourceL2 →L[ℂ] burnolCoPoissonQuotientSpace (b : ℝ))
    (hB : DeningerGammaSixSoninMellinPrimeCyclic b B) :
    B deningerGammaSixLeadingTensorVector = 0 := by
  apply (burnolCoPoissonQuotient_eq_zero_mellin_hasse_iff b _).2
  intro w
  rw [← deningerGammaSixSoninMellinProbe_apply]
  exact deningerGammaSixProbe_prime_cyclic_leading_zero _ (w : ℂ).re w.property.1 (hB w)

/-- A nonzero physical leading vector supplies a detecting strip point and a failed prime test. -/
theorem deningerGammaSixSoninMellin_exists_noncyclic_probe
    (b : Set.Ioi (0 : ℝ))
    (B : DeningerGammaSixTensorSourceL2 →L[ℂ] burnolCoPoissonQuotientSpace (b : ℝ))
    (hB : B deningerGammaSixLeadingTensorVector ≠ 0) :
    ∃ w : BurnolRightStrip,
      deningerGammaSixSoninMellinProbe b B w deningerGammaSixLeadingTensorVector ≠ 0 ∧
      ¬ DeningerOrdinaryIntegerGibbsPrimePairCyclic (w : ℂ).re w.property.1
        ⟨deningerGammaSixProbeOperator (deningerGammaSixSoninMellinProbe b B w),
          deningerGammaSixProbeOperator_mem_gibbsDomain _ w.property.1⟩ := by
  obtain ⟨w, hw⟩ := exists_burnolRightStrip_mellin_ne_zero_of_ne_zero b _ hB
  have hn : deningerGammaSixSoninMellinProbe b B w deningerGammaSixLeadingTensorVector ≠ 0 := by
    rwa [deningerGammaSixSoninMellinProbe_apply]
  exact ⟨w, hn, fun hc => hn
    (deningerGammaSixProbe_prime_cyclic_leading_zero _ (w : ℂ).re w.property.1 hc)⟩

/-- No bounded injective quotient comparison can make all these literal probes prime cyclic. -/
theorem deningerGammaSixSoninMellin_no_faithful_bounded_cyclic_comparison
    (b : Set.Ioi (0 : ℝ)) :
    ¬ ∃ B : DeningerGammaSixTensorSourceL2 →L[ℂ] burnolCoPoissonQuotientSpace (b : ℝ),
      Function.Injective B ∧ DeningerGammaSixSoninMellinPrimeCyclic b B := by
  rintro ⟨B, hinj, hc⟩
  apply deningerGammaSixLeadingTensorVector_ne_zero
  apply hinj
  rw [map_zero]
  exact deningerGammaSixSoninMellinPrimeCyclic_leading_zero b B hc

/-- Every finite literal completed-Mellin jet pulls back to a bounded tensor probe. -/
theorem deningerGammaSix_exists_bounded_completed_jet_probe
    (a : ℝ) (ha : 0 < a)
    (B : DeningerGammaSixTensorSourceL2 →L[ℂ] soninExtendedSpace a)
    (k : ℕ) (w : BurnolRightStrip) :
    ∃ L : DeningerGammaSixBoundedProbe, ∀ v : DeningerGammaSixTensorSourceL2,
      L v = iteratedDeriv k
        (fun s : ℂ => soninMellinEvaluation s
          ((((B v : soninExtendedSpace a) : evenSubspace) : SoninL2))) (w : ℂ) := by
  obtain ⟨E, hE⟩ := exists_soninExtendedCompletedMellinJetEvaluator ha k w.property.1 w.property.2
  exact ⟨E.comp B, fun v => hE (B v)⟩

/-- The complete-source diagonal is summable exactly when its literal physical jet coefficient vanishes. -/
theorem deningerGammaSix_completed_jet_probe_classification
    (a : ℝ) (ha : 0 < a)
    (B : DeningerGammaSixTensorSourceL2 →L[ℂ] soninExtendedSpace a)
    (k : ℕ) (w : BurnolRightStrip) :
    ∃ L : DeningerGammaSixBoundedProbe,
      (∀ v : DeningerGammaSixTensorSourceL2,
        L v = iteratedDeriv k
          (fun s : ℂ => soninMellinEvaluation s
            ((((B v : soninExtendedSpace a) : evenSubspace) : SoninL2))) (w : ℂ)) ∧
      (Summable (deningerGammaSixProbeDiagonal L) ↔
        iteratedDeriv k
          (fun s : ℂ => soninMellinEvaluation s
            ((((B deningerGammaSixLeadingTensorVector : soninExtendedSpace a) : evenSubspace) : SoninL2)))
          (w : ℂ) = 0) ∧
      (DeningerOrdinaryIntegerGibbsPrimePairCyclic (w : ℂ).re w.property.1
        ⟨deningerGammaSixProbeOperator L, deningerGammaSixProbeOperator_mem_gibbsDomain L w.property.1⟩ →
        iteratedDeriv k
          (fun s : ℂ => soninMellinEvaluation s
            ((((B deningerGammaSixLeadingTensorVector : soninExtendedSpace a) : evenSubspace) : SoninL2)))
          (w : ℂ) = 0) := by
  obtain ⟨L, hL⟩ := deningerGammaSix_exists_bounded_completed_jet_probe a ha B k w
  refine ⟨L, hL, ?_, ?_⟩
  · rw [summable_deningerGammaSixProbeDiagonal_iff, hL]
  · intro hc
    rw [← hL]
    exact deningerGammaSixProbe_prime_cyclic_leading_zero L (w : ℂ).re w.property.1 hc

end
end RHTower
