import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingTeukolskyThermalDealiasingEndpoint

/-!
# Quadratic QNM Matsubara coordinates

Algebraic identities for quadratic Birmingham--Mokhtari frequency coordinates.
-/

open Complex Real Set Filter Topology

namespace RHTower

noncomputable section

/-- Matsubara coordinate of the plus-branch self-coupling. -/
def d4QuadraticQNMHawkingIndexPlus (n : ℕ) (z : ℂ) : ℂ :=
  Complex.I * (2 * thetaCuspHawkingTopologicalBlackHoleQNMPlus n z)

/-- Matsubara coordinate of the minus-branch self-coupling. -/
def d4QuadraticQNMHawkingIndexMinus (n : ℕ) (z : ℂ) : ℂ :=
  Complex.I * (2 * thetaCuspHawkingTopologicalBlackHoleQNMMinus n z)

/-- Matsubara coordinate of the cross-branch coupling. -/
def d4CrossBranchQNMHawkingIndex (n : ℕ) (z : ℂ) : ℂ :=
  Complex.I * (thetaCuspHawkingTopologicalBlackHoleQNMPlus n z +
    thetaCuspHawkingTopologicalBlackHoleQNMMinus n z)

lemma d4QuadraticQNMHawkingIndexPlus_eq (n : ℕ) (z : ℂ) :
    d4QuadraticQNMHawkingIndexPlus n z =
      ((4 * n + 2 : ℕ) : ℂ) + d4ThetaTeukolskyRho z := by
  unfold d4QuadraticQNMHawkingIndexPlus
    thetaCuspHawkingTopologicalBlackHoleQNMPlus
    thetaCuspHawkingTopologicalBlackHoleConformalDecay
  rw [d4ThetaTeukolskyAngularMomentum_eq_rho]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

lemma d4QuadraticQNMHawkingIndexMinus_eq (n : ℕ) (z : ℂ) :
    d4QuadraticQNMHawkingIndexMinus n z =
      ((4 * n + 4 : ℕ) : ℂ) - d4ThetaTeukolskyRho z := by
  unfold d4QuadraticQNMHawkingIndexMinus
    thetaCuspHawkingTopologicalBlackHoleQNMMinus
    thetaCuspHawkingTopologicalBlackHoleConformalDecay
  rw [d4ThetaTeukolskyAngularMomentum_eq_rho]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem d4CrossBranchQNMHawkingIndex_eq (n : ℕ) (z : ℂ) :
    d4CrossBranchQNMHawkingIndex n z = ((4 * n + 3 : ℕ) : ℂ) := by
  unfold d4CrossBranchQNMHawkingIndex
    thetaCuspHawkingTopologicalBlackHoleQNMPlus
    thetaCuspHawkingTopologicalBlackHoleQNMMinus
    thetaCuspHawkingTopologicalBlackHoleConformalDecay
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

/-- Fractional real offset of the plus branch above level `4*n+2`. -/
def d4QuadraticQNMPlusBranchFractionalOffset (n : ℕ) (z : ℂ) : ℝ :=
  (d4QuadraticQNMHawkingIndexPlus n z).re - (4 * n + 2 : ℕ)

/-- Fractional real offset of the minus branch above level `4*n+3`. -/
def d4QuadraticQNMMinusBranchFractionalOffset (n : ℕ) (z : ℂ) : ℝ :=
  (d4QuadraticQNMHawkingIndexMinus n z).re - (4 * n + 3 : ℕ)

/-- Centered plus-branch asymmetry. -/
def d4QuadraticQNMPlusBranchAsymmetry (n : ℕ) (z : ℂ) : ℝ :=
  1 - 2 * d4QuadraticQNMPlusBranchFractionalOffset n z

/-- Centered minus-branch asymmetry. -/
def d4QuadraticQNMMinusBranchAsymmetry (n : ℕ) (z : ℂ) : ℝ :=
  1 - 2 * d4QuadraticQNMMinusBranchFractionalOffset n z

lemma d4QuadraticQNMPlusBranchFractionalOffset_eq (n : ℕ) (z : ℂ) :
    d4QuadraticQNMPlusBranchFractionalOffset n z = (d4ThetaTeukolskyRho z).re := by
  rw [d4QuadraticQNMPlusBranchFractionalOffset, d4QuadraticQNMHawkingIndexPlus_eq]
  simp

lemma d4QuadraticQNMMinusBranchFractionalOffset_eq (n : ℕ) (z : ℂ) :
    d4QuadraticQNMMinusBranchFractionalOffset n z = 1 - (d4ThetaTeukolskyRho z).re := by
  rw [d4QuadraticQNMMinusBranchFractionalOffset, d4QuadraticQNMHawkingIndexMinus_eq]
  simp
  ring

/-- Self-coupled branch coordinates are centered on the cross-branch coordinate. -/
theorem d4QuadraticQNMHawkingIndices_add_eq_twice_crossBranch
    (n : ℕ) (z : ℂ) :
    d4QuadraticQNMHawkingIndexPlus n z +
        d4QuadraticQNMHawkingIndexMinus n z =
      2 * d4CrossBranchQNMHawkingIndex n z := by
  rw [d4QuadraticQNMHawkingIndexPlus_eq,
    d4QuadraticQNMHawkingIndexMinus_eq,
    d4CrossBranchQNMHawkingIndex_eq]
  push_cast
  ring

/-- Branch fractional offsets sum to one. -/
theorem d4QuadraticQNMBranchFractionalOffsets_add_eq_one (n : ℕ) (z : ℂ) :
    d4QuadraticQNMPlusBranchFractionalOffset n z +
      d4QuadraticQNMMinusBranchFractionalOffset n z = 1 := by
  rw [d4QuadraticQNMPlusBranchFractionalOffset_eq,
    d4QuadraticQNMMinusBranchFractionalOffset_eq]
  ring

/-- Branch asymmetries cancel. -/
theorem d4QuadraticQNMBranchAsymmetry_sum_eq_zero (n : ℕ) (z : ℂ) :
    d4QuadraticQNMPlusBranchAsymmetry n z +
      d4QuadraticQNMMinusBranchAsymmetry n z = 0 := by
  rw [d4QuadraticQNMPlusBranchAsymmetry,
    d4QuadraticQNMMinusBranchAsymmetry,
    d4QuadraticQNMPlusBranchFractionalOffset_eq,
    d4QuadraticQNMMinusBranchFractionalOffset_eq]
  ring

lemma d4QuadraticQNMPlusBranchAsymmetry_xi_eq (n : ℕ) (q : XiZeroCopy) :
    d4QuadraticQNMPlusBranchAsymmetry n (xiSpectralPoint q) =
      1 - 2 * (q.1 : ℂ).re := by
  rw [d4QuadraticQNMPlusBranchAsymmetry,
    d4QuadraticQNMPlusBranchFractionalOffset_eq,
    d4ThetaTeukolskyRho_xiSpectralPoint]

lemma d4QuadraticQNMMinusBranchAsymmetry_xi_eq (n : ℕ) (q : XiZeroCopy) :
    d4QuadraticQNMMinusBranchAsymmetry n (xiSpectralPoint q) =
      2 * (q.1 : ℂ).re - 1 := by
  rw [d4QuadraticQNMMinusBranchAsymmetry,
    d4QuadraticQNMMinusBranchFractionalOffset_eq,
    d4ThetaTeukolskyRho_xiSpectralPoint]
  ring

lemma d4QuadraticQNMPlusBranchAsymmetry_xi_eq_twice_im
    (n : ℕ) (q : XiZeroCopy) :
    d4QuadraticQNMPlusBranchAsymmetry n (xiSpectralPoint q) =
      2 * (xiSpectralPoint q).im := by
  rw [d4QuadraticQNMPlusBranchAsymmetry_xi_eq]
  simp [xiSpectralPoint]
  ring

theorem d4QuadraticQNMPlusBranchAsymmetry_xi_eq_zero_iff
    (n : ℕ) (q : XiZeroCopy) :
    d4QuadraticQNMPlusBranchAsymmetry n (xiSpectralPoint q) = 0 ↔
      (xiSpectralPoint q).im = 0 := by
  rw [d4QuadraticQNMPlusBranchAsymmetry_xi_eq_twice_im]
  constructor <;> intro h
  · linarith
  · rw [h]
    ring

lemma d4QuadraticQNMHawkingIndexPlus_xi_eq (n : ℕ) (q : XiZeroCopy) :
    d4QuadraticQNMHawkingIndexPlus n (xiSpectralPoint q) =
      ((4 * n + 2 : ℕ) : ℂ) + (q.1 : ℂ) := by
  rw [d4QuadraticQNMHawkingIndexPlus_eq,
    d4ThetaTeukolskyRho_xiSpectralPoint]

lemma d4QuadraticQNMHawkingIndexMinus_xi_eq (n : ℕ) (q : XiZeroCopy) :
    d4QuadraticQNMHawkingIndexMinus n (xiSpectralPoint q) =
      ((4 * n + 4 : ℕ) : ℂ) - (q.1 : ℂ) := by
  rw [d4QuadraticQNMHawkingIndexMinus_eq,
    d4ThetaTeukolskyRho_xiSpectralPoint]

theorem d4QuadraticQNMHawkingIndexPlus_xi_ne_matsubara
    (n : ℕ) (q : XiZeroCopy) (k : ℕ) :
    d4QuadraticQNMHawkingIndexPlus n (xiSpectralPoint q) ≠ (k : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  rw [d4QuadraticQNMHawkingIndexPlus_xi_eq] at him
  have him' : (q.1 : ℂ).im = 0 := by simpa using him
  exact xi_divisor_support_im_ne_zero q.1 him'

theorem d4QuadraticQNMHawkingIndexMinus_xi_ne_matsubara
    (n : ℕ) (q : XiZeroCopy) (k : ℕ) :
    d4QuadraticQNMHawkingIndexMinus n (xiSpectralPoint q) ≠ (k : ℂ) := by
  intro h
  have him := congrArg Complex.im h
  rw [d4QuadraticQNMHawkingIndexMinus_xi_eq] at him
  have him' : -(q.1 : ℂ).im = 0 := by simpa using him
  exact xi_divisor_support_im_ne_zero q.1 (neg_eq_zero.mp him')

lemma d4QuadraticQNMPlusBranchFractionalOffset_xi_eq (n : ℕ) (q : XiZeroCopy) :
    d4QuadraticQNMPlusBranchFractionalOffset n (xiSpectralPoint q) = (q.1 : ℂ).re := by
  rw [d4QuadraticQNMPlusBranchFractionalOffset_eq,
    d4ThetaTeukolskyRho_xiSpectralPoint]

lemma d4QuadraticQNMMinusBranchFractionalOffset_xi_eq (n : ℕ) (q : XiZeroCopy) :
    d4QuadraticQNMMinusBranchFractionalOffset n (xiSpectralPoint q) = 1 - (q.1 : ℂ).re := by
  rw [d4QuadraticQNMMinusBranchFractionalOffset_eq,
    d4ThetaTeukolskyRho_xiSpectralPoint]

/-- Plus-branch fractional offset lies in the open unit interval. -/
theorem d4QuadraticQNMPlusBranchFractionalOffset_xi_mem_openUnit
    (n : ℕ) (q : XiZeroCopy) :
    d4QuadraticQNMPlusBranchFractionalOffset n (xiSpectralPoint q) ∈ Set.Ioo 0 1 := by
  rw [d4QuadraticQNMPlusBranchFractionalOffset_xi_eq]
  exact xi_divisor_support_re_mem_open_unit q.1

/-- Minus-branch fractional offset lies in the open unit interval. -/
theorem d4QuadraticQNMMinusBranchFractionalOffset_xi_mem_openUnit
    (n : ℕ) (q : XiZeroCopy) :
    d4QuadraticQNMMinusBranchFractionalOffset n (xiSpectralPoint q) ∈ Set.Ioo 0 1 := by
  rw [d4QuadraticQNMMinusBranchFractionalOffset_xi_eq]
  have hstrip := xi_divisor_support_re_mem_open_unit q.1
  constructor <;> linarith

def D4QuadraticQNMBranchAsymmetryVanishes : Prop :=
  ∀ (n : ℕ) (q : XiZeroCopy),
    d4QuadraticQNMPlusBranchAsymmetry n (xiSpectralPoint q) = 0

theorem riemannHypothesis_iff_d4QuadraticQNMBranchAsymmetryVanishes :
    RiemannHypothesis ↔ D4QuadraticQNMBranchAsymmetryVanishes := by
  constructor
  · intro hRH n q
    exact (d4QuadraticQNMPlusBranchAsymmetry_xi_eq_zero_iff n q).2
      (xiSpectralPoint_im_eq_zero_of_riemannHypothesis hRH q)
  · intro hbalanced
    apply riemannHypothesis_of_xiSpectralPoint_real
    intro q
    refine ⟨(xiSpectralPoint q).re, ?_⟩
    apply Complex.ext
    · simp
    · simp [(d4QuadraticQNMPlusBranchAsymmetry_xi_eq_zero_iff 0 q).1
        (hbalanced 0 q)]

end

end RHTower
