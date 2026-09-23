import GaloisForLFunctions.RHTower.Sieve.TwistedDiagonalGCDReindex
import GaloisForLFunctions.RHTower.Sieve.SelbergDiagonalUpperAsymptotic
import GaloisForLFunctions.HTGeometry.HarmonicLogWindow

/-!
# Evaluation of the twisted second-moment diagonal

The diagonal of the twisted second moment of `ζ` on the critical line carries the weight
`(mn)^{-1/2}` over the pairs with `n k = m h`.  Reindexing along the reduced coprime direction
turns that weight into a pure harmonic sum, and the reduction constant is exactly the classical
`(h,k)/√(hk)`:

```text
∑_{m,n ≤ X, nk = mh} (mn)^{-1/2}
      = ((h,k)/√(hk)) · H_{⌊X / max(h/(h,k), k/(h,k))⌋}
      = ((h,k)/√(hk)) · ( log⌊X / max(h', k')⌋ + γ ) + O( (h,k)/(√(hk)·D) ).
```

This is the main term of the Balasubramanian--Conrey--Heath-Brown twisted second moment, in the
shape the Levinson mollifier sum consumes: the weight `log X − log max(h',k')` is exactly
`log X − log[h,k] + log min(h,k)`.
-/

open Finset

noncomputable section

namespace RHTower.Sieve

/-- The diagonal weight collapses to the reduction constant times a harmonic term. -/
theorem twistedDiagonalSqrtWeight {h k : ℕ} (hh : 0 < h) (hk : 0 < k) {d : ℕ} (hd : 0 < d) :
    (1 : ℝ) / Real.sqrt ((((k / Nat.gcd h k) * d : ℕ) : ℝ) *
        (((h / Nat.gcd h k) * d : ℕ) : ℝ)) =
      ((Nat.gcd h k : ℝ) / Real.sqrt ((h : ℝ) * (k : ℝ))) * (1 / (d : ℝ)) := by
  have hg : 0 < Nat.gcd h k := Nat.gcd_pos_of_pos_left k hh
  have hgR : (0 : ℝ) < (Nat.gcd h k : ℝ) := by exact_mod_cast hg
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hgh : (Nat.gcd h k) * (h / Nat.gcd h k) = h :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_left h k)
  have hgk : (Nat.gcd h k) * (k / Nat.gcd h k) = k :=
    Nat.mul_div_cancel' (Nat.gcd_dvd_right h k)
  have hghR : (Nat.gcd h k : ℝ) * (((h / Nat.gcd h k : ℕ)) : ℝ) = (h : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hgh
  have hgkR : (Nat.gcd h k : ℝ) * (((k / Nat.gcd h k : ℕ)) : ℝ) = (k : ℝ) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) hgk
  have hprod : (((k / Nat.gcd h k) * d : ℕ) : ℝ) * (((h / Nat.gcd h k) * d : ℕ) : ℝ) =
      ((h : ℝ) * (k : ℝ) / (Nat.gcd h k : ℝ) ^ (2 : ℕ)) * (d : ℝ) ^ (2 : ℕ) := by
    push_cast
    field_simp
    nlinarith [hghR, hgkR]
  rw [hprod]
  have hpos : (0 : ℝ) < (h : ℝ) * (k : ℝ) / (Nat.gcd h k : ℝ) ^ (2 : ℕ) := by positivity
  rw [Real.sqrt_mul hpos.le, Real.sqrt_sq hdR.le,
    Real.sqrt_div' _ (by positivity), Real.sqrt_sq hgR.le]
  have hsqrt : (0 : ℝ) < Real.sqrt ((h : ℝ) * (k : ℝ)) :=
    Real.sqrt_pos.mpr (by positivity)
  field_simp

/-- Membership description of the reduced scale range. -/
theorem twistedDiagonalSqrt_membership {h k : ℕ} (hh : 0 < h) (hk : 0 < k) (X d : ℕ) :
    d ∈ Finset.Icc 1 (X / max (h / Nat.gcd h k) (k / Nat.gcd h k)) ↔
      ((k / Nat.gcd h k) * d ∈ Finset.Icc 1 X ∧
        (h / Nat.gcd h k) * d ∈ Finset.Icc 1 X) := by
  have hg : 0 < Nat.gcd h k := Nat.gcd_pos_of_pos_left k hh
  have hh' : 0 < h / Nat.gcd h k :=
    Nat.div_pos (Nat.le_of_dvd hh (Nat.gcd_dvd_left h k)) hg
  have hk' : 0 < k / Nat.gcd h k :=
    Nat.div_pos (Nat.le_of_dvd hk (Nat.gcd_dvd_right h k)) hg
  have hmax : 0 < max (h / Nat.gcd h k) (k / Nat.gcd h k) := lt_of_lt_of_le hh' (le_max_left _ _)
  simp only [Finset.mem_Icc]
  constructor
  · rintro ⟨hd1, hd2⟩
    have hdmax : d * max (h / Nat.gcd h k) (k / Nat.gcd h k) ≤ X :=
      (Nat.le_div_iff_mul_le hmax).1 hd2
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
    · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hk'.ne' (by omega))
    · calc (k / Nat.gcd h k) * d ≤ max (h / Nat.gcd h k) (k / Nat.gcd h k) * d :=
            Nat.mul_le_mul_right d (le_max_right _ _)
        _ = d * max (h / Nat.gcd h k) (k / Nat.gcd h k) := Nat.mul_comm _ _
        _ ≤ X := hdmax
    · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hh'.ne' (by omega))
    · calc (h / Nat.gcd h k) * d ≤ max (h / Nat.gcd h k) (k / Nat.gcd h k) * d :=
            Nat.mul_le_mul_right d (le_max_left _ _)
        _ = d * max (h / Nat.gcd h k) (k / Nat.gcd h k) := Nat.mul_comm _ _
        _ ≤ X := hdmax
  · rintro ⟨⟨hk1, hk2⟩, ⟨hh1, hh2⟩⟩
    have hd1 : 1 ≤ d := by
      by_contra hcon
      have : d = 0 := by omega
      rw [this, Nat.mul_zero] at hk1
      omega
    refine ⟨hd1, ?_⟩
    have hdk : d ≤ X / (k / Nat.gcd h k) :=
      (Nat.le_div_iff_mul_le hk').2 (by rw [Nat.mul_comm]; exact hk2)
    have hdh : d ≤ X / (h / Nat.gcd h k) :=
      (Nat.le_div_iff_mul_le hh').2 (by rw [Nat.mul_comm]; exact hh2)
    have hmin := min_natDiv_eq_natDiv_max X (h / Nat.gcd h k) (k / Nat.gcd h k) hh' hk'
    rw [← hmin]
    exact le_min hdh hdk

/-- **The twisted diagonal with the critical-line weight is a harmonic sum.** -/
theorem twistedDiagonalSqrt_sum_eq {h k : ℕ} (hh : 0 < h) (hk : 1 ≤ k) (X : ℕ) :
    (∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 X).filter (fun n => n * k = m * h),
        (1 : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ))) =
      ((Nat.gcd h k : ℝ) / Real.sqrt ((h : ℝ) * (k : ℝ))) *
        (harmonic (X / max (h / Nat.gcd h k) (k / Nat.gcd h k)) : ℝ) := by
  rw [twisted_diagonal_reindex_gcd (fun m n => (1 : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ)))
    (Finset.Icc 1 X) hk (Finset.Icc 1 (X / max (h / Nat.gcd h k) (k / Nat.gcd h k)))
    (twistedDiagonalSqrt_membership hh (by omega) X)]
  rw [← sum_Icc_one_div_eq_harmonic, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  exact twistedDiagonalSqrtWeight hh (by omega) (Finset.mem_Icc.mp hd).1

/-- **The twisted diagonal main term, with its explicit error.**  This is the
Balasubramanian--Conrey--Heath-Brown weight `((h,k)/√(hk))·(log X − log max(h',k') + γ)` in the
form the Levinson mollifier sum consumes. -/
theorem abs_twistedDiagonalSqrt_sub_main_le {h k : ℕ} (hh : 0 < h) (hk : 1 ≤ k) {X : ℕ}
    (hD : 1 ≤ X / max (h / Nat.gcd h k) (k / Nat.gcd h k)) :
    |(∑ m ∈ Finset.Icc 1 X, ∑ n ∈ (Finset.Icc 1 X).filter (fun n => n * k = m * h),
          (1 : ℝ) / Real.sqrt ((m : ℝ) * (n : ℝ))) -
        ((Nat.gcd h k : ℝ) / Real.sqrt ((h : ℝ) * (k : ℝ))) *
          (Real.log ((X / max (h / Nat.gcd h k) (k / Nat.gcd h k) : ℕ) : ℝ) +
            Real.eulerMascheroniConstant)| ≤
      ((Nat.gcd h k : ℝ) / Real.sqrt ((h : ℝ) * (k : ℝ))) *
        (1 / ((X / max (h / Nat.gcd h k) (k / Nat.gcd h k) : ℕ) : ℝ)) := by
  have hhR : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh
  have hkR : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hconst : (0 : ℝ) ≤ (Nat.gcd h k : ℝ) / Real.sqrt ((h : ℝ) * (k : ℝ)) := by
    have : (0 : ℝ) < Real.sqrt ((h : ℝ) * (k : ℝ)) := Real.sqrt_pos.mpr (by positivity)
    positivity
  rw [twistedDiagonalSqrt_sum_eq hh hk X, ← mul_sub, abs_mul, abs_of_nonneg hconst]
  refine mul_le_mul_of_nonneg_left ?_ hconst
  have hsub : (harmonic (X / max (h / Nat.gcd h k) (k / Nat.gcd h k)) : ℝ) -
      (Real.log ((X / max (h / Nat.gcd h k) (k / Nat.gcd h k) : ℕ) : ℝ) +
        Real.eulerMascheroniConstant) =
      (harmonic (X / max (h / Nat.gcd h k) (k / Nat.gcd h k)) : ℝ) -
        Real.log ((X / max (h / Nat.gcd h k) (k / Nat.gcd h k) : ℕ) : ℝ) -
        Real.eulerMascheroniConstant := by ring
  rw [hsub]
  exact HTGeometry.abs_harmonic_sub_log_sub_eulerMascheroni_le hD

/-- The reduced maximum is the lcm divided by the minimum: the diagonal weight
`log X − log max(h',k')` is exactly `log X − log[h,k] + log min(h,k)`. -/
theorem reducedMax_mul_min_eq_lcm {h k : ℕ} (hh : 0 < h) (_hk : 0 < k) :
    max (h / Nat.gcd h k) (k / Nat.gcd h k) * min h k = Nat.lcm h k := by
  have hg : 0 < Nat.gcd h k := Nat.gcd_pos_of_pos_left k hh
  have hdh : Nat.gcd h k ∣ h := Nat.gcd_dvd_left h k
  have hdk : Nat.gcd h k ∣ k := Nat.gcd_dvd_right h k
  have hmax : max (h / Nat.gcd h k) (k / Nat.gcd h k) = max h k / Nat.gcd h k := by
    rcases le_total h k with hle | hle
    · rw [max_eq_right hle, max_eq_right (Nat.div_le_div_right hle)]
    · rw [max_eq_left hle, max_eq_left (Nat.div_le_div_right hle)]
  have hdmax : Nat.gcd h k ∣ max h k := by
    rcases le_total h k with hle | hle
    · rw [max_eq_right hle]; exact hdk
    · rw [max_eq_left hle]; exact hdh
  have hmulmin : max h k * min h k = h * k := by
    rcases le_total h k with hle | hle
    · rw [max_eq_right hle, min_eq_left hle, Nat.mul_comm]
    · rw [max_eq_left hle, min_eq_right hle]
  have hlcm : Nat.gcd h k * Nat.lcm h k = h * k := Nat.gcd_mul_lcm h k
  rw [hmax]
  apply Nat.eq_of_mul_eq_mul_left hg
  calc Nat.gcd h k * (max h k / Nat.gcd h k * min h k)
      = (Nat.gcd h k * (max h k / Nat.gcd h k)) * min h k := by ring
    _ = max h k * min h k := by rw [Nat.mul_div_cancel' hdmax]
    _ = h * k := hmulmin
    _ = Nat.gcd h k * Nat.lcm h k := hlcm.symm

end RHTower.Sieve
