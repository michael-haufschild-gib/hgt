import GaloisForLFunctions.RHTower.Sieve.PairDensityRootCount
import GaloisForLFunctions.RHTower.Sieve.ResiduePartitionCount

/-!
# The remainder of the shifted-pair sieve

The sieve's remainder compares the number of `m ≤ Y` whose shifted product `m(m+d)` is divisible by
a modulus with the expected count `Y·ν`.  Because `ν` is the *true* root density — the count of
solutions of `r(r+d) ≡ 0` divided by the modulus — the comparison splits over the roots, and each
root contributes an interval-in-a-residue-class count that is within one of its expectation.

So the remainder is at most twice the number of roots, hence at most `2^{ω+1}`, uniformly in the
modulus and the shift.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- **The multiple sum of the pair sieve counts the shifted products divisible by the modulus.** -/
theorem multSum_roughPairSieve (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h d : ℕ) {z : ℝ} (hz : 1 ≤ z)
    (e : ℕ) :
    BoundingSieve.multSum (s := (roughPairSieve Y hP₁ h d hz).toBoundingSieve) e
      = ((((Finset.Icc 1 ⌊Y⌋₊).filter (fun m => e ∣ m * (m + d))).card : ℕ) : ℝ) := by
  classical
  have hinj : Set.InjOn (fun m : ℕ => m * (m + d))
      ((Finset.Icc 1 ⌊Y⌋₊ : Finset ℕ) : Set ℕ) := by
    refine Set.InjOn.mono ?_ (shiftMul_injOn d)
    intro m hm
    rw [Finset.mem_coe, Finset.mem_Icc] at hm
    exact hm.1
  show (∑ v ∈ (Finset.Icc 1 ⌊Y⌋₊).image (fun m => m * (m + d)),
      if e ∣ v then (1 : ℝ) else 0) = _
  rw [Finset.sum_image hinj, Finset.sum_boole]

/-- **The remainder of the pair sieve is at most twice the root count.** -/
theorem abs_rem_roughPairSieve_le (Y : ℝ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h d : ℕ) {z : ℝ} (hz : 1 ≤ z)
    (hY : 0 ≤ Y) {e : ℕ} (he : 0 < e) (hsq : Squarefree e) :
    |BoundingSieve.rem (s := (roughPairSieve Y hP₁ h d hz).toBoundingSieve) e|
      ≤ 2 * ((quadraticCongruenceRootCountTotal e (d : ℤ) : ℕ) : ℝ) := by
  classical
  have heR : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he
  set M : ℕ := ⌊Y⌋₊ with hM
  set S : Finset ℕ := (Finset.range e).filter (fun r => e ∣ r * (r + d)) with hS
  set ρ : ℝ := ((quadraticCongruenceRootCountTotal e (d : ℤ) : ℕ) : ℝ) with hρ
  have hcardS : ((S.card : ℕ) : ℝ) = ρ := by
    rw [hS, hρ]
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) (card_rootResidues_eq he d)
  -- the multiple sum splits over the roots
  have hcongr : ∀ m₁ m₂ : ℕ, m₁ % e = m₂ % e → (e ∣ m₁ * (m₁ + d) ↔ e ∣ m₂ * (m₂ + d)) := by
    intro m₁ m₂ hmod
    have hkey : (m₁ * (m₁ + d)) % e = (m₂ * (m₂ + d)) % e := by
      conv_lhs => rw [Nat.mul_mod, Nat.add_mod, hmod]
      conv_rhs => rw [Nat.mul_mod, Nat.add_mod]
    constructor
    · intro hd
      exact Nat.dvd_iff_mod_eq_zero.2 (by rw [← hkey]; exact Nat.dvd_iff_mod_eq_zero.1 hd)
    · intro hd
      exact Nat.dvd_iff_mod_eq_zero.2 (by rw [hkey]; exact Nat.dvd_iff_mod_eq_zero.1 hd)
  have hsplit := card_filter_eq_sum_residues he M (fun m => e ∣ m * (m + d)) hcongr
  show |BoundingSieve.multSum (s := (roughPairSieve Y hP₁ h d hz).toBoundingSieve) e
      - pairNu d e * Y| ≤ 2 * ρ
  rw [multSum_roughPairSieve Y hP₁ h d hz e]
  rw [pairNu_eq_rootDensity hsq d, ← hρ]
  have hcast : ((((Finset.Icc 1 M).filter (fun m => e ∣ m * (m + d))).card : ℕ) : ℝ)
      = ∑ r ∈ S, ((((Finset.Icc 1 M).filter (fun m => m % e = r)).card : ℕ) : ℝ) := by
    rw [hS]
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hsplit
  rw [hcast]
  -- each residue class is within one of `M/e`
  have hterm : ∀ r ∈ S, |((((Finset.Icc 1 M).filter (fun m => m % e = r)).card : ℕ) : ℝ)
      - (M : ℝ) / (e : ℝ)| ≤ 1 := by
    intro r hr
    rw [hS, Finset.mem_filter, Finset.mem_range] at hr
    have hup := card_residue_class_le he M r
    have hlo := card_residue_class_ge he M hr.1
    rw [abs_le]
    exact ⟨by linarith, by linarith⟩
  have hsum : |(∑ r ∈ S, ((((Finset.Icc 1 M).filter (fun m => m % e = r)).card : ℕ) : ℝ))
      - ((S.card : ℕ) : ℝ) * ((M : ℝ) / (e : ℝ))| ≤ ((S.card : ℕ) : ℝ) := by
    have hrw : (∑ r ∈ S, ((((Finset.Icc 1 M).filter (fun m => m % e = r)).card : ℕ) : ℝ))
        - ((S.card : ℕ) : ℝ) * ((M : ℝ) / (e : ℝ))
        = ∑ r ∈ S, (((((Finset.Icc 1 M).filter (fun m => m % e = r)).card : ℕ) : ℝ)
            - (M : ℝ) / (e : ℝ)) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    rw [hrw]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [hcardS] at hsum
  -- and `⌊Y⌋` differs from `Y` by at most one
  have hfloor : |(M : ℝ) - Y| ≤ 1 := by
    have h1 : ((M : ℕ) : ℝ) ≤ Y := Nat.floor_le hY
    have h2 : Y < ((M : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one Y
    rw [abs_le]
    constructor <;> linarith
  have hρ0 : (0 : ℝ) ≤ ρ := Nat.cast_nonneg _
  have hdiff : |ρ * ((M : ℝ) / (e : ℝ)) - ρ / (e : ℝ) * Y| ≤ ρ := by
    have hval : ρ * ((M : ℝ) / (e : ℝ)) - ρ / (e : ℝ) * Y
        = (ρ / (e : ℝ)) * ((M : ℝ) - Y) := by
      field_simp
    rw [hval, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ ρ / (e : ℝ))]
    have he1 : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
    have hle : ρ / (e : ℝ) ≤ ρ := by
      rw [div_le_iff₀ heR]
      nlinarith [hρ0, he1]
    nlinarith [hfloor, hle, abs_nonneg ((M : ℝ) - Y), hρ0]
  calc |(∑ r ∈ S, ((((Finset.Icc 1 M).filter (fun m => m % e = r)).card : ℕ) : ℝ))
        - ρ / (e : ℝ) * Y|
      = |((∑ r ∈ S, ((((Finset.Icc 1 M).filter (fun m => m % e = r)).card : ℕ) : ℝ))
          - ρ * ((M : ℝ) / (e : ℝ)))
        + (ρ * ((M : ℝ) / (e : ℝ)) - ρ / (e : ℝ) * Y)| := by ring_nf
    _ ≤ _ := by
        refine (abs_add_le _ _).trans ?_
        linarith [hsum, hdiff]

end

end RHTower.Sieve
