import GaloisForLFunctions.RHTower.PaperPrimeCoShiftCalkin
import GaloisForLFunctions.RHTower.PrimeCoShiftSpectralGap

/-!
# Finite arithmetic co-shift kernels inside the closed shift algebra

The Neumann formula places every one-prime kernel projection in the closed arithmetic shift
algebra. Commuting intersections keep every finite-prime projection there. Each finite system
has a nonzero vector, constructed from the vacuum by successive Neumann inverses while retaining
zero co-shift responses at all unused primes.
-/

namespace RHTower.PrimeCoShift

noncomputable section

open GaloisForLFunctions.HTGeometry
open scoped Classical ENNReal

/-- Parameters for which every one-prime Neumann inverse exists. -/
abbrev PaperCoShiftParameter := {s : ℂ // 0 < s.re}

local instance : CompleteSpace paperPrimeCoShiftAlgebra := by
  unfold paperPrimeCoShiftAlgebra
  infer_instance

private theorem Bop_mem_algebra (p : ℕ+) {a : ℂ} (ha : ‖a‖ < 1) :
    Bop p ha ∈ paperPrimeCoShiftAlgebra := by
  let A : paperPrimeCoShiftAlgebra :=
    ⟨a • Vop p, paperPrimeCoShiftAlgebra.smul_mem (paperPrimeCoShiftAlgebra_shift_mem p) a⟩
  have hA : ‖A‖ < 1 := norm_smul_Vop_lt p ha
  let u := Units.oneSub A hA
  let b : paperPrimeCoShiftAlgebra := ↑u⁻¹
  have hu : (1 - A) * b = 1 := by
    rw [← Units.val_oneSub A hA]
    exact u.mul_inv
  have hmul : (1 - a • Vop p) * (b : H →L[ℂ] H) = 1 :=
    congrArg (fun T : paperPrimeCoShiftAlgebra => (T : H →L[ℂ] H)) hu
  have hb : (b : H →L[ℂ] H) = Bop p ha := by
    calc
      (b : H →L[ℂ] H) = 1 * (b : H →L[ℂ] H) := (one_mul _).symm
      _ = (Bop p ha * (1 - a • Vop p)) * (b : H →L[ℂ] H) := by rw [Bop_mul_right]
      _ = Bop p ha * ((1 - a • Vop p) * (b : H →L[ℂ] H)) := mul_assoc _ _ _
      _ = Bop p ha := by rw [hmul, mul_one]
  rw [← hb]
  exact b.property

/-- The actual prime resolvent belongs to the closed arithmetic shift algebra. -/
theorem paperPrimeCoShiftAlgebra_resolvent_mem (s : PaperCoShiftParameter) (p : Nat.Primes) :
    Bop (primePNat p) (norm_primeScalar_lt_one s.property p) ∈ paperPrimeCoShiftAlgebra :=
  Bop_mem_algebra _ _

/-- The existing closed-form row-kernel projection belongs to the same algebra. -/
theorem paperPrimeCoShiftAlgebra_rowProjection_mem (s : PaperCoShiftParameter) (p : Nat.Primes) :
    rowProjection s.1 s.property p ∈ paperPrimeCoShiftAlgebra := by
  exact paperPrimeCoShiftAlgebra.smul_mem
    (mul_mem (mul_mem (paperPrimeCoShiftAlgebra_resolvent_mem s p)
      (paperPrimeCoShiftAlgebra_defect_mem _))
      (star_mem (paperPrimeCoShiftAlgebra_resolvent_mem s p))) _

/-- Orthogonal projection onto the simultaneous kernel of a finite prime packet. -/
def paperCoShiftFiniteProjection (s : PaperCoShiftParameter) (F : Finset Nat.Primes) : H →L[ℂ] H :=
  (F.inf (rowKer s.1)).starProjection

theorem paperCoShiftFiniteProjection_empty (s : PaperCoShiftParameter) :
    paperCoShiftFiniteProjection s ∅ = 1 := by
  simp only [paperCoShiftFiniteProjection, Finset.inf_empty, Submodule.starProjection_top]
  rfl

theorem paperCoShiftFiniteProjection_insert (s : PaperCoShiftParameter)
    (p : Nat.Primes) (F : Finset Nat.Primes) :
    paperCoShiftFiniteProjection s (insert p F) =
      rowProjection s.1 s.property p * paperCoShiftFiniteProjection s F := by
  apply ContinuousLinearMap.ext
  intro x
  letI : (rowKer s.1 p ⊓ F.inf (rowKer s.1)).HasOrthogonalProjection := by
    rw [← Finset.inf_insert]
    infer_instance
  have hc := starProjection_finsetInf_comm (rowKer s.1)
    (starProjection_rowKer_commute s.property) F p
  have h := starProjection_inf_of_commute (M := rowKer s.1 p) (N := F.inf (rowKer s.1))
    (fun y => (hc y).symm) x
  simpa only [paperCoShiftFiniteProjection, Finset.inf_insert,
    starProjection_rowKer_eq s.property, mul_apply_eq_comp, Function.comp_apply] using h

/-- Every finite-prime kernel projection remains inside the norm-closed shift algebra. -/
theorem paperCoShiftFiniteProjection_mem_algebra (s : PaperCoShiftParameter)
    (F : Finset Nat.Primes) : paperCoShiftFiniteProjection s F ∈ paperPrimeCoShiftAlgebra := by
  induction F using Finset.induction_on with
  | empty => rw [paperCoShiftFiniteProjection_empty]; exact one_mem _
  | @insert p F _ ih =>
    rw [paperCoShiftFiniteProjection_insert]
    exact mul_mem (paperPrimeCoShiftAlgebra_rowProjection_mem s p) ih

private theorem vacuum_coShift (p : Nat.Primes) :
    primeCoShift (primePNat p) (lp.single 2 1 (1 : ℂ)) = 0 := by
  apply lp.ext
  funext n
  have hn : primePNat p * n ≠ 1 := by
    intro h
    have he := congrArg (fun k : ℕ+ => (k : ℕ)) h
    change (p : ℕ) * (n : ℕ) = 1 at he
    have hp : 2 ≤ (p : ℕ) := p.property.two_le
    have hn : 1 ≤ (n : ℕ) := n.property
    nlinarith
  simp [primeCoShift_apply, lp.single_apply, hn]

/-- Finite prime equations admit a nonzero solution which stays in the kernels of all unused
co-shifts. No common all-prime ground state is required for this finite construction. -/
theorem paperCoShiftFiniteKernel_witness (s : PaperCoShiftParameter) (F : Finset Nat.Primes) :
    ∃ x : H, x ≠ 0 ∧ (∀ p ∈ F, rowOp s.1 p x = 0) ∧
      ∀ p ∉ F, primeCoShift (primePNat p) x = 0 := by
  induction F using Finset.induction_on with
  | empty =>
    refine ⟨lp.single 2 1 (1 : ℂ), ?_, by simp, fun p _ => vacuum_coShift p⟩
    intro h
    have h1 := congrArg (fun x : H => x 1) h
    simp at h1
  | @insert p F hp ih =>
    obtain ⟨x, hx, hrow, hrest⟩ := ih
    let B := Bop (primePNat p) (norm_primeScalar_lt_one s.property p)
    have hcomm (q : Nat.Primes) (hqp : q ≠ p) :
        Commute (primeCoShift (primePNat q)) B := by
      apply commute_Bop_right
      apply coShift_commute_Vop
      exact (Nat.coprime_primes p.property q.property).mpr
        (fun h => hqp (Subtype.ext h.symm))
    refine ⟨B x, ?_, ?_, ?_⟩
    · intro hzero
      have h := congrArg (fun T : H →L[ℂ] H => T x)
        (Bop_mul_left (primePNat p) (norm_primeScalar_lt_one s.property p))
      change (1 - primeScalar s.1 p • Vop (primePNat p)) (B x) = x at h
      rw [hzero, map_zero] at h
      exact hx h.symm
    · intro q hq
      rcases Finset.mem_insert.mp hq with hqp | hq
      · subst q
        have h := congrArg (fun T : H →L[ℂ] H => T x)
          (Top_mul_Bop (primePNat p) (norm_primeScalar_lt_one s.property p))
        exact h.trans (hrest p hp)
      · have hqp : q ≠ p := fun h => hp (h ▸ hq)
        have hc : Commute (rowOp s.1 q) B :=
          (hcomm q hqp).sub_left (commute_smul_left (Commute.one_left B) _)
        have h := congrArg (fun T : H →L[ℂ] H => T x) hc.eq
        change rowOp s.1 q (B x) = B (rowOp s.1 q x) at h
        rw [hrow q hq, map_zero] at h
        exact h
    · intro q hq
      have hqp : q ≠ p := fun h => hq (Finset.mem_insert.mpr (Or.inl h))
      have hqF : q ∉ F := fun h => hq (Finset.mem_insert.mpr (Or.inr h))
      have h := congrArg (fun T : H →L[ℂ] H => T x) (hcomm q hqp).eq
      change primeCoShift (primePNat q) (B x) = B (primeCoShift (primePNat q) x) at h
      rw [hrest q hqF, map_zero] at h
      exact h

/-- Every finite-prime kernel is nontrivial throughout the positive real half-plane. -/
theorem paperCoShiftFiniteKernel_ne_bot (s : PaperCoShiftParameter) (F : Finset Nat.Primes) :
    F.inf (rowKer s.1) ≠ ⊥ := by
  obtain ⟨x, hx, hrow, _⟩ := paperCoShiftFiniteKernel_witness s F
  have hmem : x ∈ F.inf (rowKer s.1) := by
    rw [Finset.inf_eq_iInf]
    exact (Submodule.mem_iInf _).mpr fun p => (Submodule.mem_iInf _).mpr fun hp => hrow p hp
  intro hzero
  rw [hzero] at hmem
  exact hx hmem

/-- No finite packet loses its unit projection norm. -/
theorem paperCoShiftFiniteProjection_norm (s : PaperCoShiftParameter) (F : Finset Nat.Primes) :
    ‖paperCoShiftFiniteProjection s F‖ = 1 :=
  Submodule.norm_starProjection _ (paperCoShiftFiniteKernel_ne_bot s F)

/-- Every finite packet has essential norm exactly one. -/
theorem paperCoShiftFiniteProjection_compactIdealDistance
    (s : PaperCoShiftParameter) (F : Finset Nat.Primes) :
    compactIdealDistance (paperCoShiftFiniteProjection s F) = 1 := by
  rw [paperPrimeCoShiftAlgebra_compactIdealDistance
    ⟨_, paperCoShiftFiniteProjection_mem_algebra s F⟩, paperCoShiftFiniteProjection_norm]

/-- Every finite-prime kernel projection is noncompact. -/
theorem paperCoShiftFiniteProjection_not_compact
    (s : PaperCoShiftParameter) (F : Finset Nat.Primes) :
    ¬ IsCompactOperator (paperCoShiftFiniteProjection s F) := by
  intro h
  have hz := compactIdealDistance_eq_zero_of_isCompactOperator _ h
  rw [paperCoShiftFiniteProjection_compactIdealDistance] at hz
  exact one_ne_zero hz

/-- The proven compact-ideal weight gives infinite cost at every finite prime packet. -/
theorem paperCoShiftFiniteProjection_traceCost
    (s : PaperCoShiftParameter) (F : Finset Nat.Primes) :
    compactOperatorTraceCost H (paperCoShiftFiniteProjection s F) = ∞ :=
  (compactOperatorTraceCost_eq_top_iff _).mpr (paperCoShiftFiniteProjection_not_compact s F)

end

end RHTower.PrimeCoShift
