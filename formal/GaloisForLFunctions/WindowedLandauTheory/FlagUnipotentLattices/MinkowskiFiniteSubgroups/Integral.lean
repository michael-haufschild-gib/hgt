import GaloisForLFunctions.WindowedLandauTheory.FlagUnipotentLattices.MinkowskiFiniteSubgroups.FiniteOrderTrace
import GaloisForLFunctions.WindowedLandauTheory.FlagUnipotentLattices.MinkowskiFiniteSubgroups.TracePowerSums
import GaloisForLFunctions.WindowedLandauTheory.LocalRingCardinality.MinkMEqMinkowskiNumber

/-! The Schur polynomial isolates the identity in a prime-power subgroup. -/

namespace WindowedLandauTheory.MinkowskiFiniteSubgroups

open Finset Polynomial WindowedLandauTheory.BasicNotions

noncomputable def schurPoly (N ℓ m : ℕ) : ℤ[X] :=
  ∏ y ∈ range m, (X - C ((N : ℤ) - (ℓ : ℤ) * ((y + 1 : ℕ) : ℤ)))

theorem schurPoly_eval_top (N ℓ m : ℕ) :
    (schurPoly N ℓ m).eval (N : ℤ) = ((ℓ ^ m * m.factorial : ℕ) : ℤ) := by
  unfold schurPoly
  rw [eval_prod]
  simp only [eval_sub, eval_X, eval_C, sub_sub_cancel]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_range, ← Nat.cast_prod,
    Finset.prod_range_add_one_eq_factorial]
  push_cast
  ring

theorem schurPoly_eval_zero (N ℓ m y : ℕ) (h1 : y ≠ 0) (h2 : y ≤ m) :
    (schurPoly N ℓ m).eval ((N : ℤ) - (ℓ : ℤ) * (y : ℤ)) = 0 := by
  unfold schurPoly
  rw [eval_prod]
  apply Finset.prod_eq_zero (i := y - 1) (Finset.mem_range.2 (by omega))
  have : y - 1 + 1 = y := by omega
  simp [this]

private theorem dvd_sum_eval (N : ℕ)
    (P : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℤ)) [Fintype P] (f : ℤ[X]) :
    (Fintype.card P : ℤ) ∣ ∑ g : P, f.eval (Matrix.trace
      ((g : Matrix.GeneralLinearGroup (Fin N) ℤ) : Matrix (Fin N) (Fin N) ℤ)) := by
  simp_rw [eval_eq_sum_range]
  rw [Finset.sum_comm]
  apply Finset.dvd_sum
  intro k _
  rw [← Finset.mul_sum]
  exact Dvd.dvd.mul_left (card_dvd_sum_trace_pow N P k) _

private theorem pGroup_card_dvd (N ℓ : ℕ) (hℓ : ℓ.Prime)
    (P : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℤ)) (hfin : Finite P) (hP : IsPGroup ℓ P) :
    Nat.card P ∣ ℓ ^ (N / (ℓ - 1)) * (N / (ℓ - 1)).factorial := by
  letI : Finite P := hfin
  have : Fintype P := Fintype.ofFinite P
  set m := N / (ℓ - 1) with hm
  have hdvd := dvd_sum_eval N P (schurPoly N ℓ m)
  rw [Finset.sum_eq_single (1 : P)] at hdvd
  · have h1 : Matrix.trace (((1 : P) : Matrix.GeneralLinearGroup (Fin N) ℤ) :
        Matrix (Fin N) (Fin N) ℤ) = (N : ℤ) := by
      simp
    rw [h1, schurPoly_eval_top, Int.natCast_dvd_natCast, ← Nat.card_eq_fintype_card] at hdvd
    exact hdvd
  · intro g _ hg
    obtain ⟨a, hga⟩ := hP g
    have hmat : ((g : Matrix.GeneralLinearGroup (Fin N) ℤ) : Matrix (Fin N) (Fin N) ℤ) ^ (ℓ ^ a)
        = 1 := by
      have := congrArg (fun x : P => ((x : Matrix.GeneralLinearGroup (Fin N) ℤ) :
        Matrix (Fin N) (Fin N) ℤ)) hga
      simpa using this
    obtain ⟨y, hy, htr, hy0⟩ := trace_of_prime_power_order N ℓ a hℓ _ hmat
    rw [htr]
    apply schurPoly_eval_zero _ _ _ _ _ hy
    intro h0
    apply hg
    apply Subtype.ext
    apply Units.ext
    simpa using hy0 h0
  · intro h
    exact absurd (Finset.mem_univ _) h

private theorem term_eq (N p i : ℕ) : N / (p ^ i * (p - 1)) = (N / (p - 1)) / p ^ i := by
  rw [mul_comm, Nat.div_div_eq_div_mul]

private theorem padicValNat_pow_mul_factorial (N ℓ : ℕ) (hℓ : ℓ.Prime) :
    padicValNat ℓ (ℓ ^ (N / (ℓ - 1)) * (N / (ℓ - 1)).factorial) = padicValNat ℓ (minkM N) := by
  rw [padicValNat_minkM N ℓ hℓ]
  have : Fact ℓ.Prime := ⟨hℓ⟩
  set m := N / (ℓ - 1) with hm
  have hmN : m ≤ N := Nat.div_le_self _ _
  have hlog : Nat.log ℓ m < N + 1 := lt_of_le_of_lt (Nat.log_le_self _ _) (Nat.lt_succ_of_le hmN)
  rw [padicValNat.mul (pow_ne_zero _ hℓ.ne_zero) (Nat.factorial_ne_zero _), padicValNat.prime_pow,
    padicValNat_factorial hlog]
  simp_rw [term_eq, ← hm]
  rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot (Nat.succ_pos N)]
  simp

/-- The integral Minkowski divisibility bound, checked prime power by prime power. -/
theorem card_dvd_minkowskiNumber (N : ℕ) (G : Subgroup (Matrix.GeneralLinearGroup (Fin N) ℤ))
    (hG : Finite G) : Nat.card G ∣ minkM N := by
  letI : Finite G := hG
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro ℓ k hℓ hk
  have : Fact ℓ.Prime := ⟨hℓ⟩
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime ℓ hk
  have hinj : Function.Injective G.subtype := G.subtype_injective
  have hcard : Nat.card (K.map G.subtype) = ℓ ^ k := by
    rw [Subgroup.card_map_of_injective hinj, hK]
  have hfin : Finite (K.map G.subtype) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hℓ.ne_zero)
  have hp : IsPGroup ℓ (K.map G.subtype) := IsPGroup.of_card hcard
  have hdvd := pGroup_card_dvd N ℓ hℓ (K.map G.subtype) hfin hp
  rw [hcard] at hdvd
  have hne : ℓ ^ (N / (ℓ - 1)) * (N / (ℓ - 1)).factorial ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ hℓ.ne_zero) (Nat.factorial_ne_zero _)
  have hle : k ≤ padicValNat ℓ (minkM N) := by
    rw [← padicValNat_pow_mul_factorial N ℓ hℓ]
    exact (padicValNat_dvd_iff_le hne).1 hdvd
  exact (padicValNat_dvd_iff_le (minkM_pos N).ne').2 hle

end WindowedLandauTheory.MinkowskiFiniteSubgroups
