import GaloisForLFunctions.BezoutValuationIncidence.Sieve.AffineMangoldtProgressions
import GaloisForLFunctions.BezoutValuationIncidence.Sieve.CollisionMass

/-!
# Reciprocal Mangoldt mass of an affine collision row

Two inverse-multiplier residues collide precisely on one affine progression.
The prime part gains a reciprocal modulus above its square; all proper
prime powers are retained in the explicit fractional-power remainder.
-/

noncomputable section
set_option autoImplicit false
open Finset ArithmeticFunction
namespace GaloisForLFunctions.BezoutValuationIncidence

/-- The exact affine collision condition confines every nonzero weighted term to one progression. -/
theorem affine_collision_weight_le {p H X Y l b c : ℕ}
    (hpl : p.Coprime l) (f : ℕ → ℝ) {U : ℝ} (hU : 0 ≤ U)
    (hf : ∀ k ∈ Icc 1 Y, |f k| ≤ U)
    (hsupp : ∀ k ∈ Icc 1 Y, f k ≠ 0 → k ∈ Icc H X) :
    (∑ k ∈ (Icc 1 Y).filter (fun k => p.Coprime k ∧
        multiplierResidue p k b ≡ multiplierResidue p l c [MOD p]),
      (vonMangoldt k / (k : ℝ)) * f k) ≤
      U * ∑ k ∈ (Icc H X).filter (fun k => c * k ≡ l * b [MOD p]),
        vonMangoldt k / (k : ℝ) := by
  classical
  let S := (Icc 1 Y).filter (fun k => p.Coprime k ∧
    multiplierResidue p k b ≡ multiplierResidue p l c [MOD p])
  let T := (Icc H X).filter (fun k => c * k ≡ l * b [MOD p])
  have hterm (k : ℕ) (hk : k ∈ S) : (vonMangoldt k / (k : ℝ)) * f k ≤
      if k ∈ T then U * (vonMangoldt k / (k : ℝ)) else 0 := by
    obtain ⟨hkY, hpk, hcollision⟩ := mem_filter.mp hk
    by_cases hkT : k ∈ T
    · rw [if_pos hkT]
      exact (mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hf k hkY))
        (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))).trans_eq (mul_comm _ _)
    · have hz : f k = 0 := by
        by_contra hne
        apply hkT
        refine mem_filter.mpr ⟨hsupp k hkY hne, ?_⟩
        have h := (multiplierResidue_collision_iff hpk hpl).mp hcollision
        simpa only [mul_comm] using h.symm
      simp only [hz, mul_zero, if_neg hkT, le_refl]
  calc
    _ ≤ ∑ k ∈ S, if k ∈ T then U * (vonMangoldt k / (k : ℝ)) else 0 :=
      sum_le_sum hterm
    _ = ∑ k ∈ S.filter (fun k => k ∈ T), U * (vonMangoldt k / (k : ℝ)) := by
      rw [sum_filter]
    _ ≤ ∑ k ∈ T, U * (vonMangoldt k / (k : ℝ)) := by
      apply sum_le_sum_of_subset_of_nonneg (fun k hk => (mem_filter.mp hk).2)
      intro k _ _
      exact mul_nonneg hU (div_nonneg vonMangoldt_nonneg (Nat.cast_nonneg k))
    _ = _ := by rw [mul_sum]

/-- Every collision row has a prime-progression term and the full proper-power remainder. -/
theorem exists_affine_collision_mass_upper :
    ∃ p₀ : ℕ, 8 ≤ p₀ ∧ ∀ p H X Y l b c : ℕ,
      p.Prime → p₀ ≤ p → p ^ 2 ≤ H → H ≤ X → p.Coprime l → p.Coprime c →
      ∀ (f : ℕ → ℝ) (U : ℝ), 0 ≤ U →
      (∀ k ∈ Icc 1 Y, |f k| ≤ U) →
      (∀ k ∈ Icc 1 Y, f k ≠ 0 → k ∈ Icc H X) →
      (∑ k ∈ (Icc 1 Y).filter (fun k => p.Coprime k ∧
          multiplierResidue p k b ≡ multiplierResidue p l c [MOD p]),
        (vonMangoldt k / (k : ℝ)) * f k) ≤
        U * ((1026 / (p : ℝ)) * (1 + Real.log X - Real.log H) +
          576 * (H : ℝ) ^ (-(7 / 16 : ℝ))) := by
  obtain ⟨p₀, hp₀, hbound⟩ := exists_weighted_affine_mangoldt_upper
  refine ⟨p₀, hp₀, ?_⟩
  intro p H X Y l b c hp hpp hpH hHX hpl hpc f U hU hf hsupp
  exact (affine_collision_weight_le hpl f hU hf hsupp).trans
    (mul_le_mul_of_nonneg_left (hbound p H X c (l * b) hp hpp hpH hHX hpc) hU)

/-- A unit affine target cannot select the zero residue. -/
theorem multiplierResidue_not_zero_mod {p k b : ℕ} (hp : p.Prime)
    (hpk : p.Coprime k) (hpb : p.Coprime b) :
    ¬multiplierResidue p k b ≡ 0 [MOD p] := by
  intro hzero
  have hmul := hzero.mul_left k
  simp only [mul_zero] at hmul
  have hb : b ≡ 0 [MOD p] := (multiplierResidue_spec hpk).1.symm.trans hmul
  exact (hp.coprime_iff_not_dvd.mp hpb) (Nat.modEq_zero_iff_dvd.mp hb)

/-- A nonunit comparison multiplier has zero collision mass against every unit-target source. -/
theorem affine_collision_sum_eq_zero_of_nonunit {p l b c Y : ℕ} (hp : p.Prime)
    (hpl : ¬p.Coprime l) (hpb : p.Coprime b) (f : ℕ → ℝ) :
    (∑ k ∈ (Icc 1 Y).filter (fun k => p.Coprime k ∧
        multiplierResidue p k b ≡ multiplierResidue p l c [MOD p]), f k) = 0 := by
  apply sum_eq_zero
  intro k hk
  obtain ⟨_, hpk, hres⟩ := mem_filter.mp hk
  have hl : multiplierResidue p l c = 0 := by rw [multiplierResidue, dif_neg hpl]
  rw [hl] at hres
  exact False.elim (multiplierResidue_not_zero_mod hp hpk hpb hres)

/-- Unit offset targets give the collision bound even for comparison multipliers removed by the unit restriction. -/
theorem exists_affine_collision_mass_upper_unit_offsets :
    ∃ p₀ : ℕ, 8 ≤ p₀ ∧ ∀ p H X Y l b c : ℕ,
      p.Prime → p₀ ≤ p → p ^ 2 ≤ H → H ≤ X → p.Coprime b → p.Coprime c →
      ∀ (f : ℕ → ℝ) (U : ℝ), 0 ≤ U →
      (∀ k ∈ Icc 1 Y, |f k| ≤ U) →
      (∀ k ∈ Icc 1 Y, f k ≠ 0 → k ∈ Icc H X) →
      (∑ k ∈ (Icc 1 Y).filter (fun k => p.Coprime k ∧
          multiplierResidue p k b ≡ multiplierResidue p l c [MOD p]),
        (vonMangoldt k / (k : ℝ)) * f k) ≤
        U * ((1026 / (p : ℝ)) * (1 + Real.log X - Real.log H) +
          576 * (H : ℝ) ^ (-(7 / 16 : ℝ))) := by
  obtain ⟨p₀, hp₀, hbound⟩ := exists_affine_collision_mass_upper
  refine ⟨p₀, hp₀, ?_⟩
  intro p H X Y l b c hp hpp hpH hHX hpb hpc f U hU hf hsupp
  by_cases hpl : p.Coprime l
  · exact hbound p H X Y l b c hp hpp hpH hHX hpl hpc f U hU hf hsupp
  · rw [affine_collision_sum_eq_zero_of_nonunit hp hpl hpb]
    have hH : 1 ≤ H := (Nat.one_le_pow 2 p hp.pos).trans hpH
    have hlog : Real.log H ≤ Real.log X := Real.log_le_log
      (by exact_mod_cast hH) (by exact_mod_cast hHX)
    have hwidth : 0 ≤ 1 + Real.log X - Real.log H := by linarith only [hlog]
    exact mul_nonneg hU (add_nonneg (mul_nonneg (by positivity) hwidth)
      (mul_nonneg (by norm_num) (Real.rpow_nonneg (Nat.cast_nonneg H) _)))

#print axioms affine_collision_sum_eq_zero_of_nonunit
#print axioms exists_affine_collision_mass_upper_unit_offsets

#print axioms affine_collision_weight_le
#print axioms exists_affine_collision_mass_upper

end GaloisForLFunctions.BezoutValuationIncidence
