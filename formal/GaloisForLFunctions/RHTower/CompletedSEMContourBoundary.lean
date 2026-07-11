import GaloisForLFunctions.RHTower.SEMFittingCharge
import GaloisForLFunctions.RHTower.WindingFull

/-!
# The completed symmetric-EM contour boundary

The algebraic defect `semHoleDefectZ` is labelled by a chosen zero list.  This file constructs the
integer before any such list is chosen: it is the winding number of the actual completed symmetric
Euler--Maclaurin member on the intermediate circle of an isolating annulus.

For every `SEMSplitData`, the argument principle identifies this source-defined winding with the
length of the split list.  Consequently its universal integral defect and its divisor-jet boundary
equal the previously attached SEM model.  The construction uses only `rho`, the annulus radii, the
finite member index, and `completedSEM`; the split list occurs only in the comparison proof.
-/

open Complex Metric Set

namespace RHTower

open Polynomial

noncomputable section

/-- The source-selected circle between the inner hole and the outer domination boundary. -/
def semContourRadius (r₀ R : ℝ) : ℝ := (r₀ + R) / 2

/-- The actual completed symmetric Euler--Maclaurin member restricted to its intermediate circle. -/
def completedSEMContourLoop (ρ : ℂ) (r₀ R : ℝ) (N : ℕ) : ℝ → ℂ :=
  fun θ => completedSEM N
    (ρ + (semContourRadius r₀ R : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- The integral topological boundary of the completed finite member.  This definition is
source-pure: it does not mention a zero list, a vanishing order, or a proof that `xi ρ = 0`. -/
def completedSEMContourIndexZ (ρ : ℂ) (r₀ R : ℝ) (N : ℕ) : ℤ :=
  windingNumber (completedSEMContourLoop ρ r₀ R N) 0 (2 * Real.pi)

/-- The universal integral unipotent realization of the source-defined contour index. -/
def completedSEMContourDefectZ (ρ : ℂ) (r₀ R : ℝ) (N : ℕ) :
    Matrix (Fin 2) (Fin 2) (Polynomial ℤ) :=
  seamDefZ (-completedSEMContourIndexZ ρ r₀ R N)

/-- The fixed universal map from an oriented nonzero complex loop to the integral divisor-jet
boundary.  It is defined for every loop-like function, independently of `xi` and of SEM data. -/
def windingBoundaryZ (m : ℕ) (γ : ℝ → ℂ) (a b : ℝ) : LocalDivisorJet ℤ m :=
  jetClass ℤ m (C (windingNumber γ a b))

/-- The universal boundary map is additive under multiplication of nonvanishing loops. -/
theorem windingBoundaryZ_mul {m : ℕ} {γ₁ γ₂ : ℝ → ℂ} {a b : ℝ}
    (h₁ : IsLoop γ₁ a b) (h₂ : IsLoop γ₂ a b) :
    windingBoundaryZ m (fun t => γ₁ t * γ₂ t) a b =
      windingBoundaryZ m γ₁ a b + windingBoundaryZ m γ₂ a b := by
  simp only [windingBoundaryZ]
  rw [windingNumber_mul h₁ h₂]
  simp only [map_add]
  rfl

/-- The presentation-invariant integral divisor-jet boundary carried by the completed finite
member's contour index. -/
def completedSEMContourBoundaryZ (ρ : ℂ) (r₀ R : ℝ) (N m : ℕ) :
    LocalDivisorJet ℤ m :=
  windingBoundaryZ m (completedSEMContourLoop ρ r₀ R N) 0 (2 * Real.pi)

/-- The specialized boundary is the constant integral jet of the source-defined index. -/
theorem completedSEMContourBoundaryZ_eq_indexJet
    (ρ : ℂ) (r₀ R : ℝ) (N m : ℕ) :
    completedSEMContourBoundaryZ ρ r₀ R N m =
      jetClass ℤ m (C (completedSEMContourIndexZ ρ r₀ R N)) := by
  rfl

/-- The intermediate radius lies strictly between the two annulus radii. -/
theorem semContourRadius_between {r₀ R : ℝ} (hrR : r₀ < R) :
    r₀ < semContourRadius r₀ R ∧ semContourRadius r₀ R < R := by
  simp only [semContourRadius]
  constructor <;> linarith

/-- **Source-to-divisor identification.**  For every dominating split, the winding of the actual
completed symmetric Euler--Maclaurin member on the source-selected intermediate circle is exactly
the split multiplicity.  The left-hand side is defined without the split list. -/
theorem completedSEMContourIndexZ_eq_splitCount
    {ρ : ℂ} {r₀ R : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (h : SEMSplitData ρ r₀ R N zs u) :
    completedSEMContourIndexZ ρ r₀ R N = (zs.length : ℤ) := by
  obtain ⟨h0, hrR, _hstrip, _hiso, hzs, huan, hune, hfact, _hdom⟩ := h
  have hr := semContourRadius_between hrR
  have hrpos : 0 < semContourRadius r₀ R := lt_of_le_of_lt h0 hr.1
  have hin : ∀ i ∈ (Finset.univ : Finset (Fin zs.length)),
      ‖zs.get i - ρ‖ < semContourRadius r₀ R := by
    intro i _
    exact lt_of_le_of_lt (hzs (zs.get i) (List.get_mem zs i)) hr.1
  have hfactor : ∀ z ∈ ball ρ R,
      completedSEM N z =
        (∏ i ∈ (Finset.univ : Finset (Fin zs.length)), (z - zs.get i) ^ (1 : ℕ)) * u z := by
    intro z hz
    rw [hfact z hz, list_prod_map_eq_fin_prod]
    simp
  unfold completedSEMContourIndexZ completedSEMContourLoop
  rw [windingNumber_argument_principle (Finset.univ : Finset (Fin zs.length))
    (fun i => zs.get i) (fun _ => 1) hr.2 hrpos hin huan.continuousOn hune hfactor]
  simp

/-- The source-defined integral defect is exactly the attached SEM defect whenever a dominating
split is used to evaluate it.  This is a theorem, not the definition of the source defect. -/
theorem completedSEMContourDefectZ_eq_semHoleDefectZ
    {ρ : ℂ} {r₀ R : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (h : SEMSplitData ρ r₀ R N zs u) :
    completedSEMContourDefectZ ρ r₀ R N = semHoleDefectZ h := by
  rw [completedSEMContourDefectZ, semHoleDefectZ,
    completedSEMContourIndexZ_eq_splitCount h]

/-- **Integral boundary identification.**  The presentation-invariant divisor-jet boundary defined
from the actual completed finite member equals the Fitting boundary of the attached SEM model. -/
theorem completedSEMContourBoundaryZ_eq_semHoleFittingBoundary
    {ρ : ℂ} {r₀ R : ℝ} {N m : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (h : SEMSplitData ρ r₀ R N zs u) :
    completedSEMContourBoundaryZ ρ r₀ R N m =
      fittingBoundaryClass m (standardPresZ m) (semHoleDefectZ h) := by
  rw [completedSEMContourBoundaryZ_eq_indexJet,
    completedSEMContourIndexZ_eq_splitCount h,
    semHoleDefectZ_fittingClass]

/-- Every finite additive integral charge reads the source contour index as the SEM count modulo
its modulus. -/
theorem integralJetCharge_completedSEMContourBoundaryZ
    {ρ : ℂ} {r₀ R : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (h : SEMSplitData ρ r₀ R N zs u) {m n : ℕ} (hm : 1 ≤ m) :
    integralJetCharge m n hm (completedSEMContourBoundaryZ ρ r₀ R N m) =
      (zs.length : ZMod n) := by
  rw [completedSEMContourBoundaryZ_eq_semHoleFittingBoundary h,
    integralJetCharge_semHoleDefectZ h hm]

/-- Each RH-ladder rung is exactly all-level annihilation of the source-defined completed-SEM
contour boundary, rather than of a zero-list-labelled matrix. -/
theorem rhLadder_iff_completedSEMContourCharges_zero (k : ℕ) :
    RHLadder k ↔
      ∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∀ (r₀ R : ℝ) (N : ℕ),
          (∃ (zs : List ℂ) (u : ℂ → ℂ), SEMSplitData ρ r₀ R N zs u) →
          integralJetCharge 1 (2 ^ k) (by omega)
            (completedSEMContourBoundaryZ ρ r₀ R N 1) = 0 := by
  constructor
  · intro hlad ρ hρ hzero r₀ R N hex
    obtain ⟨zs, u, h⟩ := hex
    have hs := (rhLadder_iff_semHoleFittingCharge_zero k).mp hlad
      ρ hρ hzero r₀ R N zs u h
    rwa [completedSEMContourBoundaryZ_eq_semHoleFittingBoundary h]
  · intro hsource
    apply (rhLadder_iff_semHoleFittingCharge_zero k).mpr
    intro ρ hρ hzero r₀ R N zs u h
    have hs := hsource ρ hρ hzero r₀ R N ⟨zs, u, h⟩
    rwa [completedSEMContourBoundaryZ_eq_semHoleFittingBoundary h] at hs

/-- RH is exactly simultaneous dyadic annihilation of all source-defined completed-SEM contour
boundaries.  This is an arithmetic/topological reformulation, not an annihilation theorem. -/
theorem riemannHypothesis_iff_all_completedSEMContourCharges_zero :
    RiemannHypothesis ↔
      ∀ k : ℕ, ∀ ρ ∈ rightHalf, xi ρ = 0 →
        ∀ (r₀ R : ℝ) (N : ℕ),
          (∃ (zs : List ℂ) (u : ℂ → ℂ), SEMSplitData ρ r₀ R N zs u) →
          integralJetCharge 1 (2 ^ k) (by omega)
            (completedSEMContourBoundaryZ ρ r₀ R N 1) = 0 := by
  rw [rh_iff_forall_ladder]
  exact forall_congr' rhLadder_iff_completedSEMContourCharges_zero

/-- After rational scalar extension, every additive finite charge kills the source-defined contour
boundary.  Hence any mechanism capable of annihilating the integral RH charge must retain the
integral lattice or use a non-additive boundary operation. -/
theorem rat_additive_charge_baseChange_completedSEMContour_eq_zero
    {ρ : ℂ} {r₀ R : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (h : SEMSplitData ρ r₀ R N zs u) {m n : ℕ} [NeZero n]
    (φ : LocalDivisorJet ℚ m →+ ZMod n) :
    φ (baseChangeZQ m (completedSEMContourBoundaryZ ρ r₀ R N m)) = 0 := by
  rw [completedSEMContourBoundaryZ_eq_semHoleFittingBoundary h]
  exact rat_additive_charge_baseChange_semHole_eq_zero h φ

/-- The source-defined contour index is independent of every admissible annulus, truncation, and
factorization at a fixed centre. -/
theorem completedSEMContourIndexZ_rigid
    {ρ : ℂ} {r₀ R r₀' R' : ℝ} {N N' : ℕ}
    {zs zs' : List ℂ} {u u' : ℂ → ℂ}
    (h : SEMSplitData ρ r₀ R N zs u) (h' : SEMSplitData ρ r₀' R' N' zs' u') :
    completedSEMContourIndexZ ρ r₀ R N = completedSEMContourIndexZ ρ r₀' R' N' := by
  rw [completedSEMContourIndexZ_eq_splitCount h,
    completedSEMContourIndexZ_eq_splitCount h']
  exact_mod_cast (by rw [← semSplitData_count_eq h, ← semSplitData_count_eq h'])

/-- Intrinsically, the source-defined contour index equals the finite central order of `xi`. -/
theorem completedSEMContourIndexZ_eq_xiOrder
    {ρ : ℂ} {r₀ R : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ}
    (h : SEMSplitData ρ r₀ R N zs u) :
    completedSEMContourIndexZ ρ r₀ R N = ((analyticOrderAt xi ρ).toNat : ℤ) := by
  rw [completedSEMContourIndexZ_eq_splitCount h, semSplitData_count_eq h]

end

end RHTower
