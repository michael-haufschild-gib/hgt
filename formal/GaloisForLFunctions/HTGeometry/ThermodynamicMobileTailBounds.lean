import GaloisForLFunctions.HTGeometry.StaticLocalNestedThermodynamicRampReturnLaw

/-!
# Uniform mobile-tail bounds

At laboratory shell index `K`, cut the compatible nested chain after pair `2K`.  The deleted
inverse-fourth boundary bond and a perturbation tail bounded by twelve copies of a
`10⁻⁶ n⁻²` sequence each contribute less than half the target error throughout the complete
shell.  These are the quantitative estimates needed to retain the inverse-square phase block on
pairs `4K+1,...,8K` while allowing an arbitrary noncommuting prefix.
-/

namespace GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw

/-- Elementary inverse-square tail bound by telescoping `1/n - 1/(n+1)`. -/
theorem sum_inv_square_Ioc_le (K : ℕ) (hK : 1 ≤ K) :
    ∀ L : ℕ, K ≤ L →
      ∑ n ∈ Finset.Ioc K L, (1 : ℝ) / (n : ℝ) ^ (2 : ℕ)
        ≤ 1 / (K : ℝ) - 1 / (L : ℝ) := by
  intro L
  induction L with
  | zero =>
      intro h
      have : K = 0 := Nat.le_zero.mp h
      omega
  | succ L ih =>
      intro hKL
      rcases Nat.lt_or_ge K (L + 1) with hlt | hge
      · have hKle : K ≤ L := Nat.lt_succ_iff.mp hlt
        rw [Finset.sum_Ioc_succ_top hKle]
        have hprev := ih hKle
        have hLpos : (0 : ℝ) < L := by
          have : 1 ≤ L := le_trans hK hKle
          exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
        have hL1pos : (0 : ℝ) < (L : ℝ) + 1 := by linarith
        have hstep : (1 : ℝ) / ((L : ℝ) + 1) ^ (2 : ℕ) ≤
            1 / (L : ℝ) - 1 / ((L : ℝ) + 1) := by
          rw [div_le_iff₀ (pow_pos hL1pos 2)]
          field_simp
          nlinarith
        have hcast : ((L + 1 : ℕ) : ℝ) = (L : ℝ) + 1 := by push_cast; ring
        rw [hcast]
        linarith
      · have hKeq : K = L + 1 := le_antisymm hKL hge
        subst hKeq
        simp

/-- A finite suffix indexed by `j+1>K` is bounded by `1/K`. -/
theorem sum_fin_succ_inv_square_indicator_le
    (N K : ℕ) (hK : 1 ≤ K) (hKN : K ≤ N) :
    (∑ j : Fin N, if K < j.val + 1 then (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ) ^ (2 : ℕ) else 0)
      ≤ 1 / (K : ℝ) := by
  have heq :
      (∑ j : Fin N,
        if K < j.val + 1 then (1 : ℝ) / ((j.val + 1 : ℕ) : ℝ) ^ (2 : ℕ) else 0) =
        ∑ n ∈ Finset.Ioc K N, (1 : ℝ) / (n : ℝ) ^ (2 : ℕ) := by
    rw [← Finset.sum_filter]
    refine Finset.sum_bij (fun j _ => j.val + 1) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [Finset.mem_Ioc]
      exact ⟨(Finset.mem_filter.mp hj).2, j.isLt⟩
    · intro i hi j hj hij
      exact Fin.ext (Nat.add_right_cancel hij)
    · intro n hn
      have hnK : K < n := (Finset.mem_Ioc.mp hn).1
      have hnN : n ≤ N := (Finset.mem_Ioc.mp hn).2
      have hn0 : 0 < n := by omega
      let j : Fin N := ⟨n - 1, by omega⟩
      refine ⟨j, ?_, ?_⟩
      · simp [j]
        omega
      · dsimp [j]
        omega
    · intro j hj
      rfl
  rw [heq]
  have htail := sum_inv_square_Ioc_le K hK N hKN
  have hnonneg : 0 ≤ 1 / (N : ℝ) := by positivity
  linarith

/-- Scaled finite inverse-square suffix with the perturbation normalization used below. -/
theorem sum_fin_succ_inv_square_over_million_le
    (N K : ℕ) (m : ℝ) (hm : 0 ≤ m) (hK : 1 ≤ K) (hKN : K ≤ N) :
    (∑ j : Fin N,
      if K < j.val + 1 then m / (1000000 * (((j.val + 1 : ℕ) : ℝ) ^ (2 : ℕ))) else 0)
      ≤ m / (1000000 * (K : ℝ)) := by
  have hbase := sum_fin_succ_inv_square_indicator_le N K hK hKN
  have hscale : 0 ≤ m / 1000000 := by positivity
  have hmul := mul_le_mul_of_nonneg_left hbase hscale
  calc
    (∑ j : Fin N,
      if K < j.val + 1 then m / (1000000 * (((j.val + 1 : ℕ) : ℝ) ^ (2 : ℕ))) else 0) =
        (m / 1000000) *
          (∑ j : Fin N,
            if K < j.val + 1 then (1 : ℝ) / (((j.val + 1 : ℕ) : ℝ) ^ (2 : ℕ)) else 0) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      split_ifs
      · field_simp
      · simp
    _ ≤ (m / 1000000) * (1 / (K : ℝ)) := hmul
    _ = m / (1000000 * (K : ℝ)) := by field_simp

/-- The inverse-fourth base bond crossing the cut after pair `2K` costs less than half the error. -/
theorem mobileCut_baseDuhamel_lt_half {K : ℕ} {t ε : ℝ}
    (hK : 8 ≤ K) (hε : 0 < ε)
    (ht : t < 256 * Real.pi * ε * (K + 1)) :
    t * (1 / (((2 * K + 1 : ℕ) : ℝ) ^ (4 : ℕ))) < ε / 2 := by
  have hk : (8 : ℝ) ≤ K := by exact_mod_cast hK
  have hk0 : (0 : ℝ) < K := lt_of_lt_of_le (by norm_num) hk
  have hk3 : (8 : ℝ) ^ (3 : ℕ) ≤ (K : ℝ) ^ (3 : ℕ) := by gcongr
  have hk4 : 512 * (K : ℝ) ≤ (K : ℝ) ^ (4 : ℕ) := by
    have hm := mul_le_mul_of_nonneg_left hk3 (le_of_lt hk0)
    norm_num [pow_succ] at hm ⊢
    nlinarith
  have hpoly : 2048 * ((K : ℝ) + 1) < (2 * (K : ℝ) + 1) ^ (4 : ℕ) := by
    have hrough : 2048 * ((K : ℝ) + 1) < 16 * (K : ℝ) ^ (4 : ℕ) := by
      nlinarith
    have hsquare : (2 * (K : ℝ)) ^ (4 : ℕ) < (2 * (K : ℝ) + 1) ^ (4 : ℕ) := by
      gcongr
      norm_num
    norm_num [mul_pow] at hsquare
    nlinarith
  have htScale : t < 1024 * ε * ((K : ℝ) + 1) := by
    have hpi := Real.pi_lt_four
    have hk1 : 0 < (K : ℝ) + 1 := by positivity
    have hm := mul_lt_mul_of_pos_right hpi
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 256) hε) hk1)
    refine lt_trans (by simpa using ht) ?_
    convert hm using 1 <;> ring
  have hden : (0 : ℝ) < (2 * (K : ℝ) + 1) ^ (4 : ℕ) := by positivity
  norm_num [Nat.cast_add, Nat.cast_mul]
  rw [← div_eq_mul_inv, div_lt_iff₀ hden]
  nlinarith

/-- A twelve-coordinate inverse-square perturbation tail costs less than half the error. -/
theorem mobileCut_perturbDuhamel_lt_half {K : ℕ} {t ε R : ℝ}
    (hK : 8 ≤ K) (hε : 0 < ε) (ht0 : 0 ≤ t)
    (ht : t < 256 * Real.pi * ε * (K + 1))
    (hR : R ≤ 12 / (1000000 * (K : ℝ))) :
    t * R < ε / 2 := by
  have hk : (8 : ℝ) ≤ K := by exact_mod_cast hK
  have hk0 : (0 : ℝ) < K := lt_of_lt_of_le (by norm_num) hk
  have htScale : t < 1024 * ε * ((K : ℝ) + 1) := by
    have hpi := Real.pi_lt_four
    have hk1 : 0 < (K : ℝ) + 1 := by positivity
    have hm := mul_lt_mul_of_pos_right hpi
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 256) hε) hk1)
    refine lt_trans (by simpa using ht) ?_
    convert hm using 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_left hR ht0
  have hrough : t * (12 / (1000000 * (K : ℝ))) < ε / 2 := by
    have hden : (0 : ℝ) < 1000000 * (K : ℝ) := by positivity
    rw [show t * (12 / (1000000 * (K : ℝ))) =
      (12 * t) / (1000000 * (K : ℝ)) by ring]
    rw [div_lt_iff₀ hden]
    have hk1 : (K : ℝ) + 1 ≤ 2 * K := by nlinarith
    have htScale' : 12 * t < 12 * (1024 * ε * ((K : ℝ) + 1)) := by nlinarith
    nlinarith
  exact lt_of_le_of_lt hmul hrough

/-- Sharpened boundary-bond budget used when physical approximation and circuit approximation must
share one four-phase error allowance. -/
theorem mobileCut_baseDuhamel_lt_eighth {K : ℕ} {t ε : ℝ}
    (hK : 8 ≤ K) (hε : 0 < ε)
    (ht : t < 256 * Real.pi * ε * (K + 1)) :
    t * (1 / (((2 * K + 1 : ℕ) : ℝ) ^ (4 : ℕ))) < ε / 8 := by
  have hk : (8 : ℝ) ≤ K := by exact_mod_cast hK
  have hk0 : (0 : ℝ) < K := lt_of_lt_of_le (by norm_num) hk
  have hqpos : 0 <
      16 * (K : ℝ) ^ (3 : ℕ) + 160 * (K : ℝ) ^ (2 : ℕ) + 1304 * K + 10440 := by positivity
  have hfactor : 0 ≤ ((K : ℝ) - 8) *
      (16 * (K : ℝ) ^ (3 : ℕ) + 160 * (K : ℝ) ^ (2 : ℕ) + 1304 * K + 10440) :=
    mul_nonneg (sub_nonneg.mpr hk) (le_of_lt hqpos)
  have hpoly : 8192 * ((K : ℝ) + 1) < (2 * (K : ℝ) + 1) ^ (4 : ℕ) := by
    nlinarith [hfactor]
  have htScale : t < 1024 * ε * ((K : ℝ) + 1) := by
    have hpi := Real.pi_lt_four
    have hk1 : 0 < (K : ℝ) + 1 := by positivity
    have hm := mul_lt_mul_of_pos_right hpi
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 256) hε) hk1)
    refine lt_trans (by simpa using ht) ?_
    convert hm using 1 <;> ring
  have hden : (0 : ℝ) < (2 * (K : ℝ) + 1) ^ (4 : ℕ) := by positivity
  norm_num [Nat.cast_add, Nat.cast_mul]
  rw [← div_eq_mul_inv, div_lt_iff₀ hden]
  nlinarith

/-- Sharpened perturbation-tail budget: the `10⁻⁶` envelope consumes less than one sixty-fourth
of the target error throughout the shell. -/
theorem mobileCut_perturbDuhamel_lt_sixtyfourth {K : ℕ} {t ε R : ℝ}
    (hK : 8 ≤ K) (hε : 0 < ε) (ht0 : 0 ≤ t)
    (ht : t < 256 * Real.pi * ε * (K + 1))
    (hR : R ≤ 12 / (1000000 * (K : ℝ))) :
    t * R < ε / 64 := by
  have hk : (8 : ℝ) ≤ K := by exact_mod_cast hK
  have hk0 : (0 : ℝ) < K := lt_of_lt_of_le (by norm_num) hk
  have htScale : t < 1024 * ε * ((K : ℝ) + 1) := by
    have hpi := Real.pi_lt_four
    have hk1 : 0 < (K : ℝ) + 1 := by positivity
    have hm := mul_lt_mul_of_pos_right hpi
      (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 256) hε) hk1)
    refine lt_trans (by simpa using ht) ?_
    convert hm using 1 <;> ring
  have hmul := mul_le_mul_of_nonneg_left hR ht0
  have hrough : t * (12 / (1000000 * (K : ℝ))) < ε / 64 := by
    have hden : (0 : ℝ) < 1000000 * (K : ℝ) := by positivity
    rw [show t * (12 / (1000000 * (K : ℝ))) =
      (12 * t) / (1000000 * (K : ℝ)) by ring]
    rw [div_lt_iff₀ hden]
    have hk1 : 8 * ((K : ℝ) + 1) ≤ 9 * K := by nlinarith
    have htScale' : 12 * t < 12 * (1024 * ε * ((K : ℝ) + 1)) := by nlinarith
    nlinarith
  exact lt_of_le_of_lt hmul hrough

/-- The complete inverse-fourth bridge tail beyond the selected block consumes less than one
quarter of the phase window. -/
theorem mobilePhaseBridgeTail_lt_quarter {K : ℕ} {t ε : ℝ}
    (hK : 8 ≤ K) (hε : 0 < ε)
    (ht : t < 128 * Real.pi * ε * (K + 1)) :
    t * (1 / ((4 * K : ℕ) : ℝ) ^ (3 : ℕ)) < ε / 4 := by
  have hKreal : (8 : ℝ) ≤ K := by exact_mod_cast hK
  have hKpos : (0 : ℝ) < K := by positivity
  have hscale : 128 * Real.pi * ε * ((K : ℝ) + 1) <
      ε / 4 * (4 * (K : ℝ)) ^ (3 : ℕ) := by
    have hpoly : 32 * ((K : ℝ) + 1) < (K : ℝ) ^ (3 : ℕ) := by
      nlinarith [sq_nonneg ((K : ℝ) - 8)]
    have hpi : Real.pi < 4 := Real.pi_lt_four
    have hpiScale : 8 * Real.pi * ((K : ℝ) + 1) < (K : ℝ) ^ (3 : ℕ) := by
      nlinarith
    have hm := mul_lt_mul_of_pos_left hpiScale
      (mul_pos hε (by norm_num : (0 : ℝ) < 16))
    nlinarith
  have htScale : t < ε / 4 * (4 * (K : ℝ)) ^ (3 : ℕ) := by
    have ht' : t < 128 * Real.pi * ε * ((K : ℝ) + 1) := by
      exact_mod_cast ht
    exact lt_trans ht' hscale
  have hden : (0 : ℝ) < (4 * (K : ℝ)) ^ (3 : ℕ) := by positivity
  norm_num [Nat.cast_mul]
  rw [← div_eq_mul_inv, div_lt_iff₀ hden]
  exact htScale

end GaloisForLFunctions.HTGeometry.StaticLocalLaboratoryComplexityGrowthLaw
