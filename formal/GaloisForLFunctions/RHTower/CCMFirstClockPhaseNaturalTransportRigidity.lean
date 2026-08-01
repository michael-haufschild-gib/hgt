import GaloisForLFunctions.HilbertMetric.RankOneSchurGaussianConcavity
import GaloisForLFunctions.RHTower.CCMRawStieltjesChamberIndexInflation

/-!
# Phase-natural transport rigidity for the CCM first clock

The moving physical first-clock phases separate every pair of positive logarithmic source labels.
Consequently an aperture-independent finite transport intertwining every physical phase is
diagonal. If it also fixes a nowhere-zero source vector, it is the identity.

For duplicate-free packets of actual prime powers, the labels are the injective logarithms and
the source vector consists of strictly positive critical-Mellin weights. Thus every nontrivial
source-faithful cross-prime transport has a nonzero phase-connection defect at the explicit
aperture `4 * (log kᵢ + log kⱼ)` selected by one nonzero off-diagonal entry.

This is unconditional and uses no source sign, zero-location premise, RH, or computation. It does
not orient the surviving connection defect.
-/

open scoped Matrix

namespace RHTower

noncomputable section

/-- Physical first-clock phase attached to positive logarithmic label `h` at aperture `L`. -/
def ccmFirstClockPhase (L h : ℝ) : ℝ :=
  Real.sin ((2 * Real.pi / L) * h)

/-- Diagonal physical first-clock phase on a finite labelled packet. -/
def ccmFirstClockPhaseDiagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (clock : ι → ℝ) (L : ℝ) : Matrix ι ι ℝ :=
  Matrix.diagonal fun i => ccmFirstClockPhase L (clock i)

/-- Failure of a fixed packet transport to intertwine the physical first clock. -/
def ccmFirstClockPhaseConnectionDefect
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (clock : ι → ℝ) (M : Matrix ι ι ℝ) (L : ℝ) : Matrix ι ι ℝ :=
  ccmFirstClockPhaseDiagonal clock L * M -
    M * ccmFirstClockPhaseDiagonal clock L

/-- Aperture-independent naturality for the complete physical first-clock phase family. -/
def CCMFirstClockPhaseNatural
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (clock : ι → ℝ) (M : Matrix ι ι ℝ) : Prop :=
  ∀ L : ℝ, 0 < L → ccmFirstClockPhaseConnectionDefect clock M L = 0

/-- **Explicit phase separation.** Distinct positive clock labels are separated at aperture
`4 * (a + b)`. Both resulting arguments lie in the interval where sine is strictly increasing. -/
theorem ccmFirstClockPhase_pair_ne_at_four_add
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    ccmFirstClockPhase (4 * (a + b)) a ≠
      ccmFirstClockPhase (4 * (a + b)) b := by
  have habpos : 0 < a + b := add_pos ha hb
  have hden : 0 < 2 * (a + b) := by positivity
  have harg_a :
      (2 * Real.pi / (4 * (a + b))) * a =
        Real.pi * a / (2 * (a + b)) := by
    field_simp
    ring
  have harg_b :
      (2 * Real.pi / (4 * (a + b))) * b =
        Real.pi * b / (2 * (a + b)) := by
    field_simp
    ring
  have hxa_pos : 0 < Real.pi * a / (2 * (a + b)) := by positivity
  have hxb_pos : 0 < Real.pi * b / (2 * (a + b)) := by positivity
  have hxa_lt : Real.pi * a / (2 * (a + b)) < Real.pi / 2 := by
    rw [div_lt_iff₀ hden]
    nlinarith [mul_pos Real.pi_pos hb]
  have hxb_lt : Real.pi * b / (2 * (a + b)) < Real.pi / 2 := by
    rw [div_lt_iff₀ hden]
    nlinarith [mul_pos Real.pi_pos ha]
  have hxa : Real.pi * a / (2 * (a + b)) ∈
      Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith, hxa_lt.le⟩
  have hxb : Real.pi * b / (2 * (a + b)) ∈
      Set.Icc (-(Real.pi / 2)) (Real.pi / 2) :=
    ⟨by linarith, hxb_lt.le⟩
  intro hs
  rw [ccmFirstClockPhase, ccmFirstClockPhase, harg_a, harg_b] at hs
  have hargs : Real.pi * a / (2 * (a + b)) =
      Real.pi * b / (2 * (a + b)) :=
    Real.strictMonoOn_sin.injOn hxa hxb hs
  field_simp [ne_of_gt habpos, Real.pi_ne_zero] at hargs
  exact hab (by linarith)

/-- The common commutant of all physical first-clock phases has no off-diagonal entries when the
positive clock labels are injective. Raw logarithmic-clock commutation is not assumed. -/
theorem ccmFirstClockPhaseNatural_zero_offDiagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (clock : ι → ℝ) (M : Matrix ι ι ℝ)
    (hclockpos : ∀ i, 0 < clock i)
    (hclockinj : Function.Injective clock)
    (hnat : CCMFirstClockPhaseNatural clock M) :
    ∀ i j, i ≠ j → M i j = 0 := by
  intro i j hij
  have hclockne : clock i ≠ clock j := fun h => hij (hclockinj h)
  let L := 4 * (clock i + clock j)
  have hL : 0 < L := by
    dsimp [L]
    exact mul_pos (by norm_num) (add_pos (hclockpos i) (hclockpos j))
  have hphase :
      ccmFirstClockPhase L (clock i) ≠ ccmFirstClockPhase L (clock j) := by
    dsimp [L]
    exact ccmFirstClockPhase_pair_ne_at_four_add
      (hclockpos i) (hclockpos j) hclockne
  have hcomm :
      ccmFirstClockPhaseDiagonal clock L * M =
        M * ccmFirstClockPhaseDiagonal clock L :=
    sub_eq_zero.mp (hnat L hL)
  exact
    ((GaloisForLFunctions.HilbertMetric.diagonal_commutes_matrix_iff_zero_off_label_blocks
      M (fun r => ccmFirstClockPhase L (clock r))).1 hcomm) i j hphase

/-- A matrix with zero off-diagonal entries which fixes a nowhere-zero source vector is the
identity. -/
theorem matrix_eq_one_of_sourceFixed_of_zero_offDiagonal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (source : ι → ℝ) (M : Matrix ι ι ℝ)
    (hsource : ∀ i, source i ≠ 0)
    (hfix : M *ᵥ source = source)
    (hoff : ∀ i j, i ≠ j → M i j = 0) :
    M = 1 := by
  ext i j
  by_cases hij : i = j
  · subst j
    have hi := congrFun hfix i
    simp only [Matrix.mulVec, dotProduct] at hi
    rw [Finset.sum_eq_single i] at hi
    · apply mul_right_cancel₀ (hsource i)
      simpa using hi
    · intro j _ hji
      rw [hoff i j hji.symm]
      simp
    · simp
  · rw [hoff i j hij]
    simp [hij]

/-- **Phase-natural source-transport rigidity.** Exact source faithfulness and naturality for all
physical first clocks are equivalent to the identity transport. Signed matrix entries are allowed;
positivity is unnecessary. -/
theorem ccmFirstClockPhaseNatural_sourceFaithful_iff_eq_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (clock source : ι → ℝ) (M : Matrix ι ι ℝ)
    (hclockpos : ∀ i, 0 < clock i)
    (hclockinj : Function.Injective clock)
    (hsource : ∀ i, source i ≠ 0) :
    (M *ᵥ source = source ∧ CCMFirstClockPhaseNatural clock M) ↔ M = 1 := by
  constructor
  · rintro ⟨hfix, hnat⟩
    exact matrix_eq_one_of_sourceFixed_of_zero_offDiagonal source M hsource hfix
      (ccmFirstClockPhaseNatural_zero_offDiagonal clock M hclockpos hclockinj hnat)
  · rintro rfl
    constructor
    · simp
    · intro L _hL
      simp [ccmFirstClockPhaseConnectionDefect]

/-- Source faithfulness makes every nonidentity finite transport genuinely off-diagonal. -/
theorem exists_offDiagonal_of_sourceFixed_of_ne_one
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (source : ι → ℝ) (M : Matrix ι ι ℝ)
    (hsource : ∀ i, source i ≠ 0)
    (hfix : M *ᵥ source = source)
    (hM : M ≠ 1) :
    ∃ i j, i ≠ j ∧ M i j ≠ 0 := by
  by_contra h
  push_neg at h
  exact hM (matrix_eq_one_of_sourceFixed_of_zero_offDiagonal source M hsource hfix h)

/-- **Unavoidable phase-connection current.** Every nonidentity source-faithful transport has a
nonzero off-diagonal entry, and the two labels of that entry select an explicit aperture where the
physical phase-naturality defect is nonzero. -/
theorem ccmFirstClockSourceFaithful_ne_one_has_explicit_phaseConnectionDefect
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (clock source : ι → ℝ) (M : Matrix ι ι ℝ)
    (hclockpos : ∀ i, 0 < clock i)
    (hclockinj : Function.Injective clock)
    (hsource : ∀ i, source i ≠ 0)
    (hfix : M *ᵥ source = source)
    (hM : M ≠ 1) :
    ∃ i j, i ≠ j ∧ M i j ≠ 0 ∧
      let L := 4 * (clock i + clock j)
      0 < L ∧ ccmFirstClockPhaseConnectionDefect clock M L ≠ 0 := by
  obtain ⟨i, j, hij, hMij⟩ :=
    exists_offDiagonal_of_sourceFixed_of_ne_one source M hsource hfix hM
  refine ⟨i, j, hij, hMij, ?_, ?_⟩
  · exact mul_pos (by norm_num) (add_pos (hclockpos i) (hclockpos j))
  · intro hdefect
    have hcomm :
        ccmFirstClockPhaseDiagonal clock (4 * (clock i + clock j)) * M =
          M * ccmFirstClockPhaseDiagonal clock (4 * (clock i + clock j)) :=
      sub_eq_zero.mp hdefect
    have hphase :
        ccmFirstClockPhase (4 * (clock i + clock j)) (clock i) ≠
          ccmFirstClockPhase (4 * (clock i + clock j)) (clock j) :=
      ccmFirstClockPhase_pair_ne_at_four_add (hclockpos i) (hclockpos j)
        (fun h => hij (hclockinj h))
    exact hMij
      (((GaloisForLFunctions.HilbertMetric.diagonal_commutes_matrix_iff_zero_off_label_blocks
        M (fun r => ccmFirstClockPhase (4 * (clock i + clock j)) (clock r))).1 hcomm)
          i j hphase)

/-- Injective logarithmic clock on a duplicate-free finite packet of actual prime powers. -/
def ccmFirstClockPrimePowerPacketClock {d : ℕ} (k : Fin d → ℕ) : Fin d → ℝ :=
  fun i => Real.log (k i)

/-- Literal critical-Mellin source vector on a finite packet of actual prime powers. -/
def ccmFirstClockPrimePowerPacketSource {d : ℕ} (k : Fin d → ℕ) : Fin d → ℝ :=
  fun i => criticalMellinAtomWeight (k i)

/-- **Literal finite-packet rigidity.** On every duplicate-free actual prime-power packet, the
only source-faithful transport natural for all physical first-clock phases is the identity. -/
theorem ccmFirstClockPrimePowerPacket_phaseNatural_sourceFaithful_iff_eq_one
    {d : ℕ} (k : Fin d → ℕ)
    (hk : ∀ i, IsPrimePow (k i)) (hkinj : Function.Injective k)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    (M *ᵥ ccmFirstClockPrimePowerPacketSource k =
        ccmFirstClockPrimePowerPacketSource k ∧
      CCMFirstClockPhaseNatural (ccmFirstClockPrimePowerPacketClock k) M) ↔
        M = 1 := by
  apply ccmFirstClockPhaseNatural_sourceFaithful_iff_eq_one
  · intro i
    exact Real.log_pos (by exact_mod_cast (hk i).one_lt)
  · exact criticalMellinSelectedNodes_injective hk hkinj
  · intro i
    exact ne_of_gt (criticalMellinAtomWeight_pos (hk i))

/-- **Literal finite-packet connection-defect dichotomy.** A nonidentity transport fixing every
actual critical-Mellin packet weight has a nonzero physical phase defect at an aperture selected
explicitly by one mixed prime-power pair. -/
theorem ccmFirstClockPrimePowerPacket_nontrivial_has_explicit_phaseConnectionDefect
    {d : ℕ} (k : Fin d → ℕ)
    (hk : ∀ i, IsPrimePow (k i)) (hkinj : Function.Injective k)
    (M : Matrix (Fin d) (Fin d) ℝ)
    (hfix : M *ᵥ ccmFirstClockPrimePowerPacketSource k =
      ccmFirstClockPrimePowerPacketSource k)
    (hM : M ≠ 1) :
    ∃ i j, i ≠ j ∧ M i j ≠ 0 ∧
      let L := 4 *
        (ccmFirstClockPrimePowerPacketClock k i +
          ccmFirstClockPrimePowerPacketClock k j)
      0 < L ∧
        ccmFirstClockPhaseConnectionDefect
          (ccmFirstClockPrimePowerPacketClock k) M L ≠ 0 := by
  apply ccmFirstClockSourceFaithful_ne_one_has_explicit_phaseConnectionDefect
  · intro i
    exact Real.log_pos (by exact_mod_cast (hk i).one_lt)
  · exact criticalMellinSelectedNodes_injective hk hkinj
  · intro i
    exact ne_of_gt (criticalMellinAtomWeight_pos (hk i))
  · exact hfix
  · exact hM

end

end RHTower
