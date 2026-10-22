import GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixSingularGreenStokesCoface
import GaloisForLFunctions.RHTower.Deninger.DeningerGibbsPrimeIncidenceRepair
import GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixLogarithmicWoldJordanTransgression

/-!
# Source-defined scalarization of the full Gamma-six tensor

The canonical leading-tensor reader and a bounded, degree-six invariant shell
profile map the complete corrected source to a reciprocal Green principal part
plus a summable diagonal correction. The bounded operator comparison intertwines
literal Wold compression and retains the first logarithmic normal residue.

The resulting actual ordinary-integer operator is admitted by every open Gibbs
domain and cannot make the fixed reader prime-pair cyclic. This does not construct
the missing singular cyclic-to-physical comparison or prove the Riemann hypothesis.
-/

namespace RHTower
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p

def deningerGammaSixShellFlattening (n : ℕ) : ℝ :=
  (((n : ℝ) + 216) * deningerGammaSixShellEigenvalue n)⁻¹

theorem deningerGammaSixShellFlattening_pos (n : ℕ) :
    0 < deningerGammaSixShellFlattening n := by
  unfold deningerGammaSixShellFlattening deningerGammaSixShellEigenvalue
  positivity

theorem deningerGammaSixShellFlattening_bounds (n : ℕ) :
    1 / 6 ≤ deningerGammaSixShellFlattening n ∧ deningerGammaSixShellFlattening n ≤ 1 := by
  have hx : (0 : ℝ) < (n : ℝ) + 216 := by positivity
  have hl := (div_le_iff₀ hx).1 (deningerGammaSixShellEigenvalue_lower n)
  have hu := (le_div_iff₀ hx).1 (deningerGammaSixShellEigenvalue_upper n)
  have hp : 0 < ((n : ℝ) + 216) * deningerGammaSixShellEigenvalue n := by
    unfold deningerGammaSixShellEigenvalue
    positivity
  constructor
  · simpa only [one_div, deningerGammaSixShellFlattening] using
      one_div_le_one_div_of_le hp (by simpa only [mul_comm] using hu)
  · simpa only [one_div, inv_one, deningerGammaSixShellFlattening] using
      one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1)
        (by simpa only [mul_comm] using hl)

theorem deningerGammaSixShellFlattening_wold (n : ℕ) :
    deningerGammaSixShellFlattening (deningerGammaSixWoldCoordinate n) =
      deningerGammaSixShellFlattening n := by
  unfold deningerGammaSixShellFlattening
  rw [deningerGammaSixShellEigenvalue_wold, deningerGammaSixWoldCoordinate]
  push_cast
  congr 1
  ring

theorem deningerGammaSixShellFlattening_principal (n : ℕ) :
    deningerGammaSixShellFlattening n * deningerGammaSixShellEigenvalue n =
      ((n : ℝ) + 216)⁻¹ := by
  have hn : (n : ℝ) + 216 ≠ 0 := by positivity
  have he : deningerGammaSixShellEigenvalue n ≠ 0 := by
    unfold deningerGammaSixShellEigenvalue
    positivity
  unfold deningerGammaSixShellFlattening
  field_simp

theorem deningerGammaSixLeadingTensorCoefficient_principalColumn (n : ℕ) :
    deningerGammaSixLeadingTensorCoefficient
      (deningerGammaSixSourceTensorPrincipal (deningerGammaSixShellHonestDepth n)) =
      (deningerGammaSixShellEigenvalue n : ℂ) := by
  rw [deningerGammaSixSourceTensorPrincipal_eq, map_smul,
    deningerGammaSixLeadingTensorCoefficient_leading]
  simp only [smul_eq_mul, mul_one]
  rfl

def deningerGammaSixFlattenedFullColumn (n : ℕ) : ℂ :=
  (deningerGammaSixShellFlattening n : ℂ) *
    deningerGammaSixLeadingTensorCoefficient
      (deningerGammaSixSourceTensorSquare (deningerGammaSixShellHonestDepth n))

def deningerGammaSixFlattenedRemainder (n : ℕ) : ℂ :=
  (deningerGammaSixShellFlattening n : ℂ) *
    deningerGammaSixLeadingTensorCoefficient (deningerGammaSixSourceTensorRemainderColumn n)

/-- The complete corrected tensor is retained; its entire tail occurs in the remainder. -/
theorem deningerGammaSixFlattenedFullColumn_decomposition (n : ℕ) :
    deningerGammaSixFlattenedFullColumn n =
      ((n : ℂ) + 216)⁻¹ + deningerGammaSixFlattenedRemainder n := by
  have hp : (deningerGammaSixShellFlattening n : ℂ) *
      (deningerGammaSixShellEigenvalue n : ℂ) = ((n : ℂ) + 216)⁻¹ := by
    have hh := congrArg Complex.ofReal (deningerGammaSixShellFlattening_principal n)
    push_cast at hh
    exact hh
  unfold deningerGammaSixFlattenedFullColumn deningerGammaSixFlattenedRemainder
    deningerGammaSixSourceTensorRemainderColumn deningerGammaSixSourceTensorRemainder
  rw [map_sub, deningerGammaSixLeadingTensorCoefficient_principalColumn]
  linear_combination hp

theorem norm_deningerGammaSixFlattenedRemainder_le (n : ℕ) :
    ‖deningerGammaSixFlattenedRemainder n‖ ≤
      ‖deningerGammaSixLeadingTensorCoefficient‖ *
        ‖deningerGammaSixSourceTensorRemainderColumn n‖ := by
  unfold deningerGammaSixFlattenedRemainder
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (deningerGammaSixShellFlattening_pos n)]
  calc deningerGammaSixShellFlattening n *
      ‖deningerGammaSixLeadingTensorCoefficient (deningerGammaSixSourceTensorRemainderColumn n)‖
    _ ≤ ‖deningerGammaSixLeadingTensorCoefficient (deningerGammaSixSourceTensorRemainderColumn n)‖ :=
      mul_le_of_le_one_left (norm_nonneg _) (deningerGammaSixShellFlattening_bounds n).2
    _ ≤ _ := deningerGammaSixLeadingTensorCoefficient.le_opNorm _

theorem summable_deningerGammaSixFlattenedRemainder :
    Summable deningerGammaSixFlattenedRemainder := by
  exact Summable.of_norm_bounded
    (summable_norm_deningerGammaSixSourceTensorRemainderColumn.mul_left
      ‖deningerGammaSixLeadingTensorCoefficient‖)
    norm_deningerGammaSixFlattenedRemainder_le

/-- Natural-number placement of the entire flattened tensor, retaining the actual shell offset. -/
def deningerGammaSixFlattenedFullNatColumn (k : ℕ) : ℂ :=
  if 216 ≤ k then deningerGammaSixFlattenedFullColumn (k - 216) else 0

def deningerGammaSixFlattenedFullDiagonal (k : PNat) : ℂ :=
  deningerGammaSixFlattenedFullNatColumn k

/-- The omitted finite head is included in the summable correction. -/
theorem summable_deningerGammaSixFlattenedFullDiagonal_sub_green :
    Summable (fun k : PNat => deningerGammaSixFlattenedFullDiagonal k -
      (((k : ℕ) : ℂ))⁻¹) := by
  apply (summable_pnat_iff_summable_nat
    (f := fun k : ℕ => deningerGammaSixFlattenedFullNatColumn k - (k : ℂ)⁻¹)).2
  apply (summable_nat_add_iff 216).1
  refine summable_deningerGammaSixFlattenedRemainder.congr (fun n => ?_)
  have hn : 216 ≤ n + 216 := by omega
  rw [deningerGammaSixFlattenedFullNatColumn, if_pos hn, Nat.add_sub_cancel,
    deningerGammaSixFlattenedFullColumn_decomposition]
  push_cast
  ring

/-- Literal diagonal endomorphism obtained from the full corrected Gamma tensor. -/
def deningerGammaSixFlattenedFullOperator : DeningerOrdinaryIntegerEnd where
  toFun x k := deningerGammaSixFlattenedFullDiagonal k * x k
  map_add' x y := by
    funext k
    exact mul_add _ _ _
  map_smul' c x := by
    funext k
    change _ * (c * x k) = c * (_ * x k)
    ring

theorem deningerOrdinaryIntegerDiagonalCoefficient_flattenedFull (k : PNat) :
    deningerOrdinaryIntegerDiagonalCoefficient k deningerGammaSixFlattenedFullOperator =
      deningerGammaSixFlattenedFullDiagonal k := by
  change deningerGammaSixFlattenedFullDiagonal k * deningerOrdinaryIntegerBasisVector k k = _
  rw [deningerOrdinaryIntegerBasisVector_self, mul_one]

theorem summable_deningerGammaSixFlattenedFullOperator_sub_green :
    Summable (fun k : PNat => deningerOrdinaryIntegerDiagonalCoefficient k
      (deningerGammaSixFlattenedFullOperator - deningerOrdinaryIntegerReciprocalGreen)) := by
  simpa only [map_sub, deningerOrdinaryIntegerDiagonalCoefficient_flattenedFull,
    deningerOrdinaryIntegerDiagonalCoefficient_reciprocalGreen] using
      summable_deningerGammaSixFlattenedFullDiagonal_sub_green

theorem deningerOrdinaryIntegerGibbsWeight_le_one
    {sigma : ℝ} (h : 1 / 2 ≤ sigma) (k : PNat) :
    deningerOrdinaryIntegerGibbsMass sigma k * ((k : ℕ) : ℝ) ≤ 1 := by
  have hk : (0 : ℝ) < ((k : ℕ) : ℝ) := by exact_mod_cast k.pos
  have hk1 : (1 : ℝ) ≤ ((k : ℕ) : ℝ) := by exact_mod_cast k.pos
  have he : -(2 * sigma) + 1 ≤ 0 := by linarith
  unfold deningerOrdinaryIntegerGibbsMass
  conv_lhs => rhs; rw [← Real.rpow_one (((k : ℕ) : ℝ))]
  rw [← Real.rpow_add hk]
  exact Real.rpow_le_one_of_one_le_of_nonpos hk1 he

/-- The source-derived scalar operator lies in every actual open Gibbs domain. -/
theorem deningerGammaSixFlattenedFullOperator_mem_gibbsDomain
    {sigma : ℝ} (h : 1 / 2 < sigma) :
    deningerGammaSixFlattenedFullOperator ∈ deningerOrdinaryIntegerGibbsDomain sigma := by
  have hs := summable_deningerGammaSixFlattenedFullDiagonal_sub_green
  have hw : Summable (fun k : PNat =>
      ((deningerOrdinaryIntegerGibbsMass sigma k : ℂ) * ((k : ℕ) : ℂ)) *
        (deningerGammaSixFlattenedFullDiagonal k - (((k : ℕ) : ℂ))⁻¹)) := by
    apply Summable.of_norm_bounded hs.norm
    intro k
    rw [norm_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos (mul_pos (deningerOrdinaryIntegerGibbsMass_pos sigma k)
        (by exact_mod_cast k.pos))]
    exact mul_le_of_le_one_left (norm_nonneg _) (deningerOrdinaryIntegerGibbsWeight_le_one h.le k)
  have hq : Summable (fun k : PNat => (deningerOrdinaryIntegerGibbsMass sigma k : ℂ)) :=
    Complex.summable_ofReal.mpr ((summable_deningerOrdinaryIntegerGibbsMass_iff sigma).2 h)
  refine (hq.add hw).congr (fun k => ?_)
  change (deningerOrdinaryIntegerGibbsMass sigma k : ℂ) + _ =
    ((deningerOrdinaryIntegerGibbsMass sigma k : ℂ) * ((k : ℕ) : ℂ)) *
      deningerOrdinaryIntegerDiagonalCoefficient k deningerGammaSixFlattenedFullOperator
  rw [deningerOrdinaryIntegerDiagonalCoefficient_flattenedFull]
  have hk : (((k : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast k.ne_zero
  field_simp
  ring

/-- The full-source scalarization does not produce prime cyclicity for the fixed reader. -/
theorem deningerGammaSixFlattenedFullOperator_not_prime_cyclic
    (sigma : ℝ) (h : 1 / 2 < sigma) :
    ¬ DeningerOrdinaryIntegerGibbsPrimePairCyclic sigma h
      ⟨deningerGammaSixFlattenedFullOperator, deningerGammaSixFlattenedFullOperator_mem_gibbsDomain h⟩ := by
  intro hc
  exact deningerOrdinaryIntegerGibbs_no_summable_prime_cyclic_green_repair sigma h
    ⟨⟨deningerGammaSixFlattenedFullOperator, deningerGammaSixFlattenedFullOperator_mem_gibbsDomain h⟩,
      summable_deningerGammaSixFlattenedFullOperator_sub_green, hc⟩

/-- The literal first normal variation, after the same source-defined flattening. -/
def deningerGammaSixFlattenedLogWeight (n : ℕ) : ℝ :=
  deningerGammaSixShellFlattening n * deningerGammaSixLogWeight n

theorem deningerGammaSixFlattenedLogWeight_wold (n : ℕ) :
    deningerGammaSixFlattenedLogWeight (deningerGammaSixWoldCoordinate n) -
      (1 / 6 : ℝ) * deningerGammaSixFlattenedLogWeight n =
      (Real.log 6 / 6) * ((n : ℝ) + 216)⁻¹ := by
  unfold deningerGammaSixFlattenedLogWeight
  rw [deningerGammaSixShellFlattening_wold]
  calc _ = deningerGammaSixShellFlattening n *
      (deningerGammaSixLogWeight (deningerGammaSixWoldCoordinate n) -
        (1 / 6 : ℝ) * deningerGammaSixLogWeight n) := by ring
    _ = deningerGammaSixShellFlattening n *
      ((Real.log 6 / 6) * deningerGammaSixShellEigenvalue n) := by
      rw [deningerGammaSixLogWeight_wold]
    _ = (Real.log 6 / 6) *
      (deningerGammaSixShellFlattening n * deningerGammaSixShellEigenvalue n) := by ring
    _ = _ := by rw [deningerGammaSixShellFlattening_principal]

theorem deningerGammaSixFlattenedLogWeight_wold_pos (n : ℕ) :
    0 < deningerGammaSixFlattenedLogWeight (deningerGammaSixWoldCoordinate n) -
      (1 / 6 : ℝ) * deningerGammaSixFlattenedLogWeight n := by
  rw [deningerGammaSixFlattenedLogWeight_wold]
  have hlog : 0 < Real.log 6 := Real.log_pos (by norm_num)
  positivity

theorem norm_deningerGammaSixShellFlattening_le_one (n : ℕ) :
    ‖(deningerGammaSixShellFlattening n : ℂ)‖ ≤ 1 := by
  simpa only [Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (deningerGammaSixShellFlattening_pos n)] using
      (deningerGammaSixShellFlattening_bounds n).2

/-- Bounded shell multiplier selected by the actual eigenvalue and integer coordinate. -/
def deningerGammaSixShellFlatteningOperator : EllTwo →L[ℂ] EllTwo :=
  diagonalOperator (fun n => (deningerGammaSixShellFlattening n : ℂ))
    norm_deningerGammaSixShellFlattening_le_one

theorem norm_deningerGammaSixShellFlatteningOperator_le_one :
    ‖deningerGammaSixShellFlatteningOperator‖ ≤ 1 :=
  norm_diagonalOperator_le _ norm_deningerGammaSixShellFlattening_le_one

/-- Source-defined bounded scalarization of the complete rectangular tensor carrier. -/
def deningerGammaSixFlattenedTensorReader :
    lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2 →L[ℂ] EllTwo :=
  deningerGammaSixShellFlatteningOperator ∘L deningerGammaSixLeadingTensorReader

theorem deningerGammaSixFlattenedTensorReader_apply
    (y : lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2) (n : ℕ) :
    deningerGammaSixFlattenedTensorReader y n =
      (deningerGammaSixShellFlattening n : ℂ) * deningerGammaSixLeadingTensorCoefficient (y n) := by
  rw [deningerGammaSixFlattenedTensorReader, ContinuousLinearMap.comp_apply,
    deningerGammaSixShellFlatteningOperator, diagonalOperator_apply,
    deningerGammaSixLeadingTensorReader, rectangularBlockOperator_apply]

theorem deningerGammaSixFlattenedTensorReader_full_apply (x : EllTwo) (n : ℕ) :
    deningerGammaSixFlattenedTensorReader (deningerGammaSixFullSourceTensorOperator x) n =
      x n * deningerGammaSixFlattenedFullColumn n := by
  rw [deningerGammaSixFlattenedTensorReader_apply,
    deningerGammaSixFullSourceTensorOperator_apply, map_smul]
  change _ * (x n * _) = _
  unfold deningerGammaSixFlattenedFullColumn
  ring

theorem deningerGammaSixFlattenedTensorReader_principal_apply (x : EllTwo) (n : ℕ) :
    deningerGammaSixFlattenedTensorReader (deningerGammaSixSourceTensorPrincipalOperator x) n =
      x n * ((n : ℂ) + 216)⁻¹ := by
  rw [deningerGammaSixFlattenedTensorReader_apply,
    deningerGammaSixSourceTensorPrincipalOperator_apply, map_smul,
    deningerGammaSixLeadingTensorCoefficient_principalColumn]
  have hp := congrArg Complex.ofReal (deningerGammaSixShellFlattening_principal n)
  push_cast at hp
  change _ * (x n * _) = _
  linear_combination x n * hp

/-- The complete bounded operator comparison retains a trace-class remainder. -/
theorem deningerGammaSixFlattenedTensorReader_full_remainder_traceClass :
    MemRectSchattenClass 1
      (deningerGammaSixFlattenedTensorReader ∘L deningerGammaSixFullSourceTensorOperator -
        deningerGammaSixFlattenedTensorReader ∘L deningerGammaSixSourceTensorPrincipalOperator) := by
  rw [← ContinuousLinearMap.comp_sub,
    deningerGammaSixFullSourceTensorOperator_sub_principal]
  exact deningerGammaSixSourceTensorRemainderOperator_traceClass.one_comp_left
    deningerGammaSixFlattenedTensorReader

def deningerGammaSixScalarWoldPullback : EllTwo →L[ℂ] EllTwo :=
  lpCoordinatePullback deningerGammaSixWoldCoordinate deningerGammaSixWoldCoordinate_injective

/-- Exact degree-six naturality of the same bounded source scalarization. -/
theorem deningerGammaSixFlattenedTensorReader_wold_natural :
    deningerGammaSixFlattenedTensorReader ∘L deningerGammaSixTensorWoldPullback =
      deningerGammaSixScalarWoldPullback ∘L deningerGammaSixFlattenedTensorReader := by
  apply ContinuousLinearMap.ext
  intro y
  apply lp.ext
  funext n
  rw [ContinuousLinearMap.comp_apply, deningerGammaSixFlattenedTensorReader_apply,
    deningerGammaSixTensorWoldPullback_apply]
  change _ = deningerGammaSixFlattenedTensorReader y (deningerGammaSixWoldCoordinate n)
  rw [deningerGammaSixFlattenedTensorReader_apply, deningerGammaSixShellFlattening_wold]

theorem deningerGammaSixFlattenedTensorReader_woldCompression
    (T : EllTwo →L[ℂ] lp (fun _ : ℕ => DeningerGammaSixTensorSourceL2) 2) :
    deningerGammaSixFlattenedTensorReader ∘L deningerGammaSixWoldCompression T =
      deningerGammaSixScalarWoldPullback ∘L
        (deningerGammaSixFlattenedTensorReader ∘L T) ∘L
          deningerGammaSixWoldShift.toContinuousLinearMap := by
  calc _ = (deningerGammaSixFlattenedTensorReader ∘L deningerGammaSixTensorWoldPullback) ∘L
      T ∘L deningerGammaSixWoldShift.toContinuousLinearMap := rfl
    _ = _ := by rw [deningerGammaSixFlattenedTensorReader_wold_natural]; rfl

end
end RHTower
