import GaloisForLFunctions.RHTower.MobiusCoprimeIncidence
import GaloisForLFunctions.RHTower.Sieve.GcdPowerDiagonalization
import GaloisForLFunctions.RHTower.EulerDeletionQuasiShuffleConvergence
import GaloisForLFunctions.RHTower.DivisorStationaryKernelPositivity

/-!
# Signed coprime-kernel diagonalization for Euler deletion

The all-gcd harmonic head of Euler deletion is not a positive quadratic form.
This module supplies its exact finite diagonalization: the coprimality
indicator is the Möbius sum over common divisors, so a coprime-pair quadratic
form is a signed sum of squares of its common-multiple coordinates.  It
retains every Möbius sign and is the finite kernel behind the EDQ `J_q`
family.
-/

open Finset ArithmeticFunction
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-- Exact signed diagonalization of a finite coprime-pair quadratic form. -/
theorem sum_coprime_diagonal (S : Finset ℕ) (hS : ∀ m ∈ S, 0 < m) (a : ℕ → ℝ) :
    ∑ p ∈ S ×ˢ S,
      (if p.1.Coprime p.2 then (1 : ℝ) else 0) *
        ((a p.1 / (p.1 : ℝ)) * (a p.2 / (p.2 : ℝ))) =
      ∑ e ∈ S.biUnion Nat.divisors, ((μ e : ℤ) : ℝ) *
        (∑ m ∈ S.filter (fun m => e ∣ m), a m / (m : ℝ)) ^ (2 : ℕ) := by
  classical
  have hexp : ∀ p ∈ S ×ˢ S,
      (if p.1.Coprime p.2 then (1 : ℝ) else 0) *
          ((a p.1 / (p.1 : ℝ)) * (a p.2 / (p.2 : ℝ))) =
        ∑ e ∈ (Nat.gcd p.1 p.2).divisors,
          ((μ e : ℤ) : ℝ) *
            ((a p.1 / (p.1 : ℝ)) * (a p.2 / (p.2 : ℝ))) := by
    intro p hp
    have hind : ∑ e ∈ (Nat.gcd p.1 p.2).divisors, ((μ e : ℤ) : ℝ) =
        if p.1.Coprime p.2 then (1 : ℝ) else 0 := by
      have h := congrArg (fun z : ℤ => (z : ℝ))
        (RHTower.mobiusCommonDivisorKernel_eq_coprimeIndicator p.1 p.2)
      simpa [RHTower.mobiusCommonDivisorKernel] using h
    rw [← hind, Finset.sum_mul]
  rw [Finset.sum_congr rfl hexp]
  have hmem : ∀ (p : ℕ × ℕ) (e : ℕ),
      p ∈ S ×ˢ S ∧ e ∈ (Nat.gcd p.1 p.2).divisors
        ↔ p ∈ (S ×ˢ S).filter (fun q => e ∣ q.1 ∧ e ∣ q.2) ∧ e ∈ S.biUnion Nat.divisors := by
    intro p e
    constructor
    · rintro ⟨hp, he⟩
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      have hgcd : e ∣ Nat.gcd p.1 p.2 := Nat.dvd_of_mem_divisors he
      have hd1 : e ∣ p.1 := dvd_trans hgcd (Nat.gcd_dvd_left _ _)
      have hd2 : e ∣ p.2 := dvd_trans hgcd (Nat.gcd_dvd_right _ _)
      refine ⟨Finset.mem_filter.mpr ⟨hp, hd1, hd2⟩, Finset.mem_biUnion.mpr ⟨p.1, hp1, ?_⟩⟩
      exact Nat.mem_divisors.mpr ⟨hd1, (hS _ hp1).ne'⟩
    · rintro ⟨hpf, -⟩
      obtain ⟨hp, hd1, hd2⟩ := Finset.mem_filter.mp hpf
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      refine ⟨hp, Nat.mem_divisors.mpr ⟨Nat.dvd_gcd hd1 hd2, ?_⟩⟩
      exact (Nat.gcd_pos_of_pos_left _ (hS _ hp1)).ne'
  rw [Finset.sum_comm' hmem]
  refine Finset.sum_congr rfl fun e _ => ?_
  have hfilter : (S ×ˢ S).filter (fun q => e ∣ q.1 ∧ e ∣ q.2)
      = (S.filter (fun m => e ∣ m)) ×ˢ (S.filter (fun m => e ∣ m)) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_product]
    tauto
  rw [hfilter, ← Finset.mul_sum, sq, Finset.sum_mul_sum, Finset.sum_product]

/-- The Möbius divisor kernel behind a coprime-pair form is not positive
semidefinite once the coordinate `2` is present. -/
theorem mobius_divisorKernel_not_posSemidef {N : ℕ} (hN : 2 ≤ N) :
    ¬ (RHTower.finiteDivisorStationaryKernel
      (fun e => ((μ e : ℤ) : ℝ)) N).PosSemidef := by
  intro h
  have htwo_mem : 2 ∈ Finset.Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, hN⟩
  have htwo := (RHTower.finiteDivisorStationaryKernel_posSemidef_iff
    (fun e => ((μ e : ℤ) : ℝ)) N).mp h ⟨2, htwo_mem⟩
  rw [ArithmeticFunction.moebius_apply_prime Nat.prime_two] at htwo
  norm_num at htwo

/-- The exact fixed-cutoff Möbius-harmonic sum over multiples of `q`. -/
def harmonicMultiple (q N : ℕ) : ℝ :=
  ∑ d ∈ (Finset.Icc 1 N).filter (fun d => q ∣ d), ((μ d : ℤ) : ℝ) / (d : ℝ)

/-- The literal coprime-cofactor harmonic coefficient at gcd scale `r`. -/
def coprimeHarmonicQuadratic (r N : ℕ) : ℝ :=
  ∑ a ∈ Finset.Icc 1 (N / r), ∑ b ∈ Finset.Icc 1 (N / r),
    (if a.Coprime b then (1 : ℝ) else 0) *
      (((μ (r * a) : ℤ) : ℝ) / ((r * a : ℕ) : ℝ)) *
      (((μ (r * b) : ℤ) : ℝ) / ((r * b : ℕ) : ℝ))

/-- Reindexing a diagonal multiple coordinate gives the exact EDQ harmonic sum. -/
theorem filtered_cofactor_eq_harmonicMultiple {r e N : ℕ}
    (hr : 0 < r) (he : 0 < e) :
    ∑ m ∈ (Finset.Icc 1 (N / r)).filter (fun m => e ∣ m),
      (((μ (r * m) : ℤ) : ℝ) / (r : ℝ)) / (m : ℝ) =
      harmonicMultiple (r * e) N := by
  rw [RHTower.sum_Icc_filter_dvd_reindex e (N / r) he]
  unfold harmonicMultiple
  rw [RHTower.sum_Icc_filter_dvd_reindex (r * e) N (Nat.mul_pos hr he)]
  rw [Nat.div_div_eq_div_mul]
  apply Finset.sum_congr rfl
  intro m hm
  have hm0 : m ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hm).1
  have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  have he0 : (e : ℝ) ≠ 0 := by exact_mod_cast he.ne'
  have hmR0 : (m : ℝ) ≠ 0 := by exact_mod_cast hm0
  rw [show r * (e * m) = (r * e) * m by ring]
  push_cast
  field_simp

private theorem Icc_biUnion_divisors (Q : ℕ) :
    (Finset.Icc 1 Q).biUnion Nat.divisors = Finset.Icc 1 Q := by
  classical
  ext e
  simp only [Finset.mem_biUnion, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨m, hm, hem⟩
    exact ⟨Nat.pos_of_dvd_of_pos hem.1 hm.1,
      le_trans (Nat.le_of_dvd (by omega) hem.1) hm.2⟩
  · intro he
    exact ⟨e, he, ⟨dvd_rfl, Nat.ne_of_gt he.1⟩⟩

/-- The complete fixed-cutoff all-gcd harmonic coefficient is the signed
Möbius inversion of the squared EDQ multiple sums. -/
theorem coprimeHarmonicQuadratic_eq_signedMultiples {r N : ℕ} (hr : 0 < r) :
    coprimeHarmonicQuadratic r N =
      ∑ e ∈ Finset.Icc 1 (N / r), ((μ e : ℤ) : ℝ) *
        harmonicMultiple (r * e) N ^ (2 : ℕ) := by
  let S : Finset ℕ := Finset.Icc 1 (N / r)
  let a : ℕ → ℝ := fun m => ((μ (r * m) : ℤ) : ℝ) / (r : ℝ)
  have hS : ∀ m ∈ S, 0 < m := by
    intro m hm
    exact (Finset.mem_Icc.mp hm).1
  have hleft : coprimeHarmonicQuadratic r N =
      ∑ p ∈ S ×ˢ S,
        (if p.1.Coprime p.2 then (1 : ℝ) else 0) *
          ((a p.1 / (p.1 : ℝ)) * (a p.2 / (p.2 : ℝ))) := by
    unfold coprimeHarmonicQuadratic
    dsimp [S, a]
    rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro u hu
    apply Finset.sum_congr rfl
    intro v hv
    have hu0 : (u : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hu).1)
    have hv0 : (v : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hv).1)
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    push_cast
    field_simp
  have hdiag := sum_coprime_diagonal S hS a
  have hbi : S.biUnion Nat.divisors = S := by
    dsimp [S]
    exact Icc_biUnion_divisors (N / r)
  calc
    coprimeHarmonicQuadratic r N =
        ∑ p ∈ S ×ˢ S,
          (if p.1.Coprime p.2 then (1 : ℝ) else 0) *
            ((a p.1 / (p.1 : ℝ)) * (a p.2 / (p.2 : ℝ))) := hleft
    _ = ∑ e ∈ S.biUnion Nat.divisors, ((μ e : ℤ) : ℝ) *
          (∑ m ∈ S.filter (fun m => e ∣ m), a m / (m : ℝ)) ^ (2 : ℕ) := hdiag
    _ = ∑ e ∈ S, ((μ e : ℤ) : ℝ) * harmonicMultiple (r * e) N ^ (2 : ℕ) := by
      rw [hbi]
      apply Finset.sum_congr rfl
      intro e he
      have he0 : 0 < e := (Finset.mem_Icc.mp he).1
      dsimp [S, a] at he ⊢
      rw [filtered_cofactor_eq_harmonicMultiple hr he0]
    _ = _ := by rfl

end

end RHTower.Sieve
