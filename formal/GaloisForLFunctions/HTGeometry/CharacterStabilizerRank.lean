import GaloisForLFunctions.HTGeometry.ActiveLatticeAnnihilatorDimension
import GaloisForLFunctions.HTGeometry.RationalTorusInvariantRank

/-!
# Rank of a complex character stabilizer

The full complex-torus stabilizer of an integer character set has no new
integer characters beyond the rational span of the original set.  For the
rank bound needed here, it is enough to exponentiate every vector in the
complex annihilator and use finite-dimensional duality.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {r : ℕ}

/-- Complex torus points annihilating every integer character in `A`. -/
def complexCharacterStabilizer (A : Set (Fin r → ℤ)) : Set (Fin r → ℂˣ) :=
  {u | ∀ m ∈ A, ∏ i, ((u i : ℂ)) ^ (m i) = 1}

@[simp] theorem mem_complexCharacterStabilizer {A : Set (Fin r → ℤ)}
    {u : Fin r → ℂˣ} :
    u ∈ complexCharacterStabilizer A ↔
      ∀ m ∈ A, ∏ i, ((u i : ℂ)) ^ (m i) = 1 := Iff.rfl

private theorem exp_one_ne_one : Complex.exp 1 ≠ 1 := by
  intro h
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  have hre := congrArg Complex.re hn
  norm_num at hre

private theorem expCharacter_eq_one_of_annihilates
    {A : Set (Fin r → ℤ)} {c : Fin r → ℂ}
    (hc : ∀ m ∈ A, ∑ i, c i * (m i : ℂ) = 0)
    (t : ℂ) :
    (fun i => Units.mk0 (Complex.exp (t * c i)) (Complex.exp_ne_zero _)) ∈
      complexCharacterStabilizer A := by
  intro m hm
  change ∏ i, Complex.exp (t * c i) ^ (m i) = 1
  simp_rw [← Complex.exp_int_mul]
  rw [← Complex.exp_sum]
  have hsum :
    ∑ i, (m i : ℂ) * (t * c i) = t * ∑ i, c i * (m i : ℂ) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
  rw [hsum, hc m hm, mul_zero, Complex.exp_zero]

/-- The double annihilator of an integer character set has no larger rank than
that character set. -/
theorem rank_scaleAnnihilator_complexCharacterStabilizer_le
    (A : Set (Fin r → ℤ)) :
    Module.rank ℚ
        (Submodule.span ℚ
          (intCharacterToRat '' scaleAnnihilator ℂ (complexCharacterStabilizer A))) ≤
      Module.rank ℤ (Submodule.span ℤ A) := by
  classical
  let T := scaleAnnihilator ℂ (complexCharacterStabilizer A)
  have hfin : Module.finrank ℂ
        (Submodule.span ℂ (intCharacterToComplex '' T)) ≤
      Module.finrank ℂ
        (Submodule.span ℂ (intCharacterToComplex '' A)) := by
    apply finrank_span_le_of_annihilator
    intro c hc _
    rintro ⟨a, ha, rfl⟩
    have hdot : ∑ i, c i * (a i : ℂ) = 0 := by
      by_contra hne
      let q : ℂ := ∑ i, c i * (a i : ℂ)
      let t : ℂ := q⁻¹
      let u : Fin r → ℂˣ := fun i =>
        Units.mk0 (Complex.exp (t * c i)) (Complex.exp_ne_zero _)
      have hcA : ∀ m ∈ A, ∑ i, c i * (m i : ℂ) = 0 := by
        intro m hm
        exact hc (intCharacterToComplex m) ⟨m, hm, rfl⟩
      have hu : u ∈ complexCharacterStabilizer A :=
        expCharacter_eq_one_of_annihilates hcA t
      have hua := ha u hu
      have hexp : Complex.exp (t * q) = 1 := by
        have hprod : ∏ i, Complex.exp (t * c i) ^ (a i) = 1 := by
          simpa only [u, Units.val_mk0] using hua
        simp_rw [← Complex.exp_int_mul] at hprod
        rw [← Complex.exp_sum] at hprod
        have hsum : ∑ i, (a i : ℂ) * (t * c i) = t * q := by
          change ∑ i, (a i : ℂ) * (t * c i) =
            t * ∑ i, c i * (a i : ℂ)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        rw [hsum] at hprod
        exact hprod
      have htq : t * q = 1 := inv_mul_cancel₀ hne
      rw [htq] at hexp
      exact exp_one_ne_one hexp
    simpa [intCharacterToComplex] using hdot
  have hTmap : Module.rank ℤ (Submodule.span ℤ T) =
      Module.rank ℤ (Submodule.span ℤ (intCharacterToRat '' T)) := by
    rw [← Submodule.map_span]
    exact (Submodule.equivMapOfInjective _ injective_intCharacterToRat
      (Submodule.span ℤ T)).rank_eq
  rw [← rank_span_int_eq_rank_span_rat, ← hTmap,
    ← finrank_span_intCharacterToComplex T,
    ← finrank_span_intCharacterToComplex A]
  exact_mod_cast hfin

end

end GaloisForLFunctions.HTGeometry
