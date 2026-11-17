import GaloisForLFunctions.RepresentationLifting.Differential.LogarithmicCartier
import GaloisForLFunctions.ArithmeticEffectivityTheory.Semigroups.ResidueColumns

/-!
# Exact Cartier contraction of missing exponent columns

The logarithmic Euler operator acts on each coefficient by its exponent
in the prime field. Retaining an additive spectrum preserves all horizontal
modes exactly when the characteristic belongs to that spectrum. Division by
the remaining nonzero exponents gives an explicit two-sided gap contraction.
This realizes the local eigensplitting mechanism of Shen, arXiv:2611.18317.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting.DividedPower
variable (p : ℕ) [Fact p.Prime]
local instance (S : AddSubmonoid ℕ) (n : ℕ) : Decidable (n ∈ S) := Classical.propDecidable _

/-- Projection onto the coefficients belonging to an additive exponent spectrum. -/
def spectrumProjection (S : AddSubmonoid ℕ) : Module.End (ZMod p) (ℕ →₀ ZMod p) := by
  classical
  refine {
    toFun := fun f => Finsupp.onFinset f.support (fun n => if n ∈ S then f n else 0) ?_
    map_add' := ?_
    map_smul' := ?_ }
  · intro n hn
    apply Finsupp.mem_support_iff.mpr
    intro hf
    exact hn (by rw [hf]; split_ifs <;> rfl)
  · intro f g
    apply Finsupp.ext
    intro n
    change (if n ∈ S then f n + g n else 0) =
      (if n ∈ S then f n else 0) + (if n ∈ S then g n else 0)
    split_ifs <;> simp
  · intro c f
    apply Finsupp.ext
    intro n
    change (if n ∈ S then c * f n else 0) = c * (if n ∈ S then f n else 0)
    split_ifs <;> simp

@[simp] theorem spectrumProjection_apply (S : AddSubmonoid ℕ) (f : ℕ →₀ ZMod p) (n : ℕ) :
    spectrumProjection p S f n = if n ∈ S then f n else 0 := by classical rfl

omit [Fact p.Prime] in
private theorem multiple_mem_of_period (S : AddSubmonoid ℕ) (hp : p ∈ S) (k : ℕ) :
    p * k ∈ S := by
  induction k with
  | zero => simpa only [Nat.mul_zero] using S.zero_mem
  | succ k hk => simpa only [Nat.mul_succ] using S.add_mem hk hp

private theorem gap_cast_ne_zero (S : AddSubmonoid ℕ) (hp : p ∈ S) {n : ℕ}
    (hn : n ∉ S) : (n : ZMod p) ≠ 0 := by
  intro hz
  obtain ⟨k, rfl⟩ := (ZMod.natCast_eq_zero_iff n p).mp hz
  exact hn (multiple_mem_of_period p S hp k)

/-- The coefficient inverse restricted to missing exponents. -/
def gapGreen (S : AddSubmonoid ℕ) : Module.End (ZMod p) (ℕ →₀ ZMod p) :=
  (1 - spectrumProjection p S) * cartierGreen p

@[simp] theorem gapGreen_apply (S : AddSubmonoid ℕ) (f : ℕ →₀ ZMod p) (n : ℕ) :
    gapGreen p S f n = if n ∈ S then 0 else (n : ZMod p)⁻¹ * f n := by
  classical
  change (n : ZMod p)⁻¹ * f n - spectrumProjection p S (cartierGreen p f) n = _
  rw [spectrumProjection_apply]
  change (n : ZMod p)⁻¹ * f n - (if n ∈ S then (n : ZMod p)⁻¹ * f n else 0) = _
  split_ifs <;> simp

/-- The missing-exponent complex is contracted by division by its nonzero logarithmic eigenvalues. -/
theorem logarithmicEuler_gapGreen (S : AddSubmonoid ℕ) (hp : p ∈ S) :
    logarithmicEuler p * gapGreen p S = 1 - spectrumProjection p S := by
  classical
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro n
  change (n : ZMod p) * gapGreen p S f n = f n - spectrumProjection p S f n
  rw [gapGreen_apply, spectrumProjection_apply]
  by_cases hn : n ∈ S
  · simp only [if_pos hn, mul_zero, sub_self]
  · simp only [if_neg hn, sub_zero, ← mul_assoc, mul_inv_cancel₀ (gap_cast_ne_zero p S hp hn), one_mul]

/-- The same explicit contraction is a right inverse on all missing exponents. -/
theorem gapGreen_logarithmicEuler (S : AddSubmonoid ℕ) (hp : p ∈ S) :
    gapGreen p S * logarithmicEuler p = 1 - spectrumProjection p S := by
  classical
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro n
  change gapGreen p S (logarithmicEuler p f) n = f n - spectrumProjection p S f n
  rw [gapGreen_apply, logarithmicEuler_apply, spectrumProjection_apply]
  by_cases hn : n ∈ S
  · simp only [if_pos hn, sub_self]
  · simp only [if_neg hn, sub_zero, ← mul_assoc, inv_mul_cancel₀ (gap_cast_ne_zero p S hp hn), one_mul]

/-- The characteristic belongs to the spectrum exactly when no horizontal coefficient is lost. -/
theorem horizontal_retention_iff (S : AddSubmonoid ℕ) :
    (∀ f : ℕ →₀ ZMod p, logarithmicEuler p f = 0 → spectrumProjection p S f = f) ↔ p ∈ S := by
  classical
  have hpzero : (p : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff p p).mpr (dvd_refl p)
  constructor
  · intro h
    have hd : logarithmicEuler p (Finsupp.single p 1) = 0 := by
      apply Finsupp.ext
      intro n
      rw [logarithmicEuler_apply]
      by_cases hn : n = p
      · subst n
        simp only [Finsupp.single_eq_same, hpzero, zero_mul, Finsupp.zero_apply]
      · simp [hn]
    have hh := congrArg (fun f : ℕ →₀ ZMod p => f p) (h _ hd)
    by_contra hp
    simpa only [spectrumProjection_apply, if_neg hp, Finsupp.single_eq_same,
      zero_ne_one] using hh
  · intro hp f hf
    apply Finsupp.ext
    intro n
    rw [spectrumProjection_apply]
    by_cases hn : n ∈ S
    · exact if_pos hn
    · rw [if_neg hn]
      have hh := congrArg (fun g : ℕ →₀ ZMod p => g n) hf
      change (n : ZMod p) * f n = 0 at hh
      exact ((mul_eq_zero.mp hh).resolve_left (gap_cast_ne_zero p S hp hn)).symm

/-- Membership of the characteristic is the exact boundary for the explicit gap contraction. -/
theorem gap_homotopy_iff (S : AddSubmonoid ℕ) :
    logarithmicEuler p * gapGreen p S = 1 - spectrumProjection p S ↔ p ∈ S := by
  classical
  constructor
  · intro h
    have hh := congrArg (fun T : Module.End (ZMod p) (ℕ →₀ ZMod p) => T (Finsupp.single p 1) p) h
    change (p : ZMod p) * gapGreen p S (Finsupp.single p 1) p =
      Finsupp.single p (1 : ZMod p) p - spectrumProjection p S (Finsupp.single p 1) p at hh
    have hpzero := (ZMod.natCast_eq_zero_iff p p).mpr (dvd_refl p)
    rw [hpzero, zero_mul, spectrumProjection_apply, Finsupp.single_eq_same] at hh
    by_contra hp
    simp only [if_neg hp, sub_zero, zero_ne_one] at hh
  · exact logarithmicEuler_gapGreen p S

/-- Coefficient retention is an actual idempotent endomorphism. -/
theorem spectrumProjection_idempotent (S : AddSubmonoid ℕ) :
    spectrumProjection p S * spectrumProjection p S = spectrumProjection p S := by
  classical
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro n
  change spectrumProjection p S (spectrumProjection p S f) n = spectrumProjection p S f n
  simp only [spectrumProjection_apply]
  split_ifs <;> rfl

/-- Every exponent projection commutes with the logarithmic differential. -/
theorem spectrumProjection_commutes (S : AddSubmonoid ℕ) :
    spectrumProjection p S * logarithmicEuler p = logarithmicEuler p * spectrumProjection p S := by
  classical
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro n
  change spectrumProjection p S (logarithmicEuler p f) n =
    (n : ZMod p) * spectrumProjection p S f n
  rw [spectrumProjection_apply, logarithmicEuler_apply, spectrumProjection_apply]
  split_ifs <;> simp only [mul_zero]

/-- The explicit homotopy annihilates retained coefficients on either side. -/
theorem gapGreen_projection_zero (S : AddSubmonoid ℕ) :
    spectrumProjection p S * gapGreen p S = 0 ∧ gapGreen p S * spectrumProjection p S = 0 := by
  classical
  constructor
  · apply LinearMap.ext
    intro f
    apply Finsupp.ext
    intro n
    change spectrumProjection p S (gapGreen p S f) n = 0
    rw [spectrumProjection_apply, gapGreen_apply]
    split_ifs <;> rfl
  · apply LinearMap.ext
    intro f
    apply Finsupp.ext
    intro n
    change gapGreen p S (spectrumProjection p S f) n = 0
    rw [gapGreen_apply, spectrumProjection_apply]
    split_ifs <;> simp only [mul_zero]

/-- The complete projection-and-homotopy identities hold exactly when the characteristic is retained. -/
theorem gap_deformation_retract_iff (S : AddSubmonoid ℕ) :
    (spectrumProjection p S * spectrumProjection p S = spectrumProjection p S ∧
      spectrumProjection p S * logarithmicEuler p = logarithmicEuler p * spectrumProjection p S ∧
      logarithmicEuler p * gapGreen p S = 1 - spectrumProjection p S ∧
      gapGreen p S * logarithmicEuler p = 1 - spectrumProjection p S ∧
      spectrumProjection p S * gapGreen p S = 0 ∧ gapGreen p S * spectrumProjection p S = 0) ↔ p ∈ S := by
  constructor
  · intro h
    exact (gap_homotopy_iff p S).mp h.2.2.1
  · intro hp
    exact ⟨spectrumProjection_idempotent p S, spectrumProjection_commutes p S,
      logarithmicEuler_gapGreen p S hp, gapGreen_logarithmicEuler p S hp, gapGreen_projection_zero p S⟩

#print axioms gap_deformation_retract_iff

open ArithmeticEffectivityTheory.ResidueColumns in
/-- Every prime-period Kunz spectrum retains all horizontal modes and contracts its complete gap space. -/
theorem kunz_gap_contraction (m : ℕ) [Fact (m + 1).Prime] (k : ℕ → ℕ)
    (h0 : k 0 = 0) (hK : Kunz m k) :
    logarithmicEuler (m + 1) * gapGreen (m + 1) (columnSubmonoid m k h0 hK) =
      1 - spectrumProjection (m + 1) (columnSubmonoid m k h0 hK) := by
  apply logarithmicEuler_gapGreen
  change m + 1 ∈ carrier m k
  have h := (mem_column m k 1 0 (Nat.succ_pos m)).mpr (by omega)
  simpa only [Nat.one_mul, Nat.add_zero] using h

#print axioms logarithmicEuler_gapGreen
#print axioms gapGreen_logarithmicEuler
#print axioms horizontal_retention_iff
#print axioms gap_homotopy_iff
#print axioms kunz_gap_contraction
end GaloisForLFunctions.RepresentationLifting.DividedPower
