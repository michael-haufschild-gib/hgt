import GaloisForLFunctions.RHTower.RetainedPrimeTopHomothety

noncomputable section
open Finset
namespace RHTower

/-- Splitting the complete coprime head at a fresh prime gives an exact
two-scale deletion renewal law. -/
theorem mobiusDivisorCoprimeHead_prime_deletion
    (r p N : ℕ) (hp : p.Prime) (hrp : r.Coprime p) :
    mobiusDivisorCoprimeHead r N =
      mobiusDivisorCoprimeHead (r * p) N +
        Real.sqrt p * ((ArithmeticFunction.moebius p : ℤ) : ℝ) *
          ((1 - divisorPrimeClipWeight N p) *
              mobiusDivisorCoprimeHead (r * p) (N / p) +
            divisorPrimeClipWeight N p *
              mobiusDivisorCoprimeHead (r * p) (N / p + 1)) := by
  classical
  have hsplit (d : ℕ) :
      (if r.Coprime d then mobiusDivisorDilationChannel N d else 0) =
        (if (r * p).Coprime d then mobiusDivisorDilationChannel N d else 0) +
          if p ∣ d then (if r.Coprime d then mobiusDivisorDilationChannel N d else 0) else 0 := by
    by_cases hrd : r.Coprime d
    · by_cases hpd : p ∣ d
      · have hrpd : ¬(r * p).Coprime d := by
          intro h
          have hpdiv : p ∣ r * p := by simp
          exact (hp.coprime_iff_not_dvd.mp (Nat.Coprime.of_dvd_left hpdiv h)) hpd
        rw [if_pos hrd, if_neg hrpd]
        simp [hpd]
      · have hpc : p.Coprime d := hp.coprime_iff_not_dvd.mpr hpd
        have hrpc : (r * p).Coprime d := Nat.coprime_mul_iff_left.mpr ⟨hrd, hpc⟩
        rw [if_pos hrd, if_pos hrpc]
        simp [hpd]
    · have hrpd : ¬(r * p).Coprime d := by
        intro h
        exact hrd (Nat.Coprime.of_dvd_left (Nat.dvd_mul_right r p) h)
      rw [if_neg hrd, if_neg hrpd]
      simp
  have hterm (e : ℕ) :
      (if r.Coprime (p * e) then mobiusDivisorDilationChannel N (p * e) else 0) =
        Real.sqrt p * ((ArithmeticFunction.moebius p : ℤ) : ℝ) *
          (if (r * p).Coprime e then
            (1 - divisorPrimeClipWeight N p) * mobiusDivisorDilationChannel (N / p) e +
              divisorPrimeClipWeight N p * mobiusDivisorDilationChannel (N / p + 1) e
          else 0) := by
    rw [mobiusDivisorDilationChannel_interpolation_masked p N e hp.pos]
    by_cases hpe : p.Coprime e
    · have hiff : r.Coprime (p * e) ↔ (r * p).Coprime e := by
        constructor
        · intro h
          exact Nat.coprime_mul_iff_left.mpr ⟨(Nat.coprime_mul_iff_right.mp h).2, hpe⟩
        · intro h
          exact Nat.coprime_mul_iff_right.mpr ⟨hrp, (Nat.coprime_mul_iff_left.mp h).1⟩
      by_cases h : (r * p).Coprime e
      · rw [if_pos (hiff.mpr h), if_pos hpe, if_pos h]
      · have h' : ¬r.Coprime (p * e) := fun h' => h (hiff.mp h')
        rw [if_neg h', if_neg h]
        simp
    · have h : ¬(r * p).Coprime e := by
        intro h
        have hpdiv : p ∣ r * p := by simp
        exact hpe (Nat.Coprime.of_dvd_left hpdiv h)
      simp [hpe, h]
  have htail :
      (∑ e ∈ Icc 1 (N / p),
        if (r * p).Coprime e then
          (1 - divisorPrimeClipWeight N p) * mobiusDivisorDilationChannel (N / p) e +
            divisorPrimeClipWeight N p * mobiusDivisorDilationChannel (N / p + 1) e
        else 0) =
          (1 - divisorPrimeClipWeight N p) * mobiusDivisorCoprimeHead (r * p) (N / p) +
            divisorPrimeClipWeight N p * mobiusDivisorCoprimeHead (r * p) (N / p + 1) := by
    rw [mobiusDivisorCoprimeHead, mobiusDivisorCoprimeHead_succ_eq_sum]
    calc
      _ = ∑ j ∈ Icc 1 (N / p),
        ((1 - divisorPrimeClipWeight N p) *
            (if (r * p).Coprime j then mobiusDivisorDilationChannel (N / p) j else 0) +
          divisorPrimeClipWeight N p *
            (if (r * p).Coprime j then mobiusDivisorDilationChannel (N / p + 1) j else 0)) := by
          apply Finset.sum_congr rfl
          intro j hj
          by_cases h : (r * p).Coprime j
          · simp only [if_pos h]
          · simp only [if_neg h]
            ring
      _ = _ := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
  unfold mobiusDivisorCoprimeHead
  have hdecomp :
      (∑ d ∈ Icc 1 N, if r.Coprime d then mobiusDivisorDilationChannel N d else 0) =
        ∑ d ∈ Icc 1 N,
          ((if (r * p).Coprime d then mobiusDivisorDilationChannel N d else 0) +
            if p ∣ d then (if r.Coprime d then mobiusDivisorDilationChannel N d else 0) else 0) := by
    apply Finset.sum_congr rfl
    intro d hd
    exact hsplit d
  rw [hdecomp, Finset.sum_add_distrib]
  rw [← Finset.sum_filter (s := Icc 1 N) (p := fun x : ℕ => p ∣ x),
    sum_Icc_filter_dvd_reindex p N hp.pos]
  simp_rw [hterm]
  rw [← Finset.mul_sum, htail]
  rfl

end RHTower
