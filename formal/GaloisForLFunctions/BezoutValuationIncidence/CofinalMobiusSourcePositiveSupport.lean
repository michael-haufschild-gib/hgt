import GaloisForLFunctions.BezoutValuationIncidence.CofinalMobiusSourceValueLaw

/-!
# Exact positive support of the cofinal Möbius source law

Coprime Möbius sign bands inject into every finite quotient state, supplying
an explicit positive lower mass for either source sign. The initial zero
block contributes at least the reciprocal horizon ratio. Thus the complete
cofinal alphabet is exactly the positive support of the limiting law.

This arithmetic argument complements the preceding moment interpolation:
cofinal attainment alone would not imply positive limiting frequency.
-/

open Filter Topology Finset ArithmeticFunction
open RHTower RHTower.Sieve
open GaloisForLFunctions.TransHorizonIncidenceMechanics
open scoped BigOperators ArithmeticFunction.Moebius

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

private theorem quotient_moebius {R d : ℕ} (hR : Squarefree R) (hd : d ∣ R) :
    moebiusReal (R / d) = moebiusReal R * moebiusReal d := by
  have hsf : Squarefree d := hR.squarefree_of_dvd hd
  have hcop : Nat.Coprime d (R / d) := Nat.coprime_of_squarefree_mul
    (by simpa only [Nat.mul_div_cancel' hd] using hR)
  have heq := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
  rw [Nat.mul_div_cancel' hd] at heq
  have heq' : moebiusReal R = moebiusReal d * moebiusReal (R / d) := by
    unfold moebiusReal
    exact_mod_cast heq
  have hs : moebiusReal d ^ 2 = 1 := by
    unfold moebiusReal
    exact_mod_cast ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsf
  calc
    moebiusReal (R / d) = moebiusReal (R / d) * 1 := by ring
    _ = moebiusReal (R / d) * moebiusReal d ^ 2 := by rw [hs]
    _ = (moebiusReal d * moebiusReal (R / d)) * moebiusReal d := by ring
    _ = moebiusReal R * moebiusReal d := by rw [← heq']

private theorem source_reflection {N l R : ℕ} (hN : 1 ≤ N) (hl : 1 ≤ l)
    (hR : Squarefree R) (hlo : l * N < R) (hhi : R ≤ (l + 1) * N) :
    sieveSeq N moebiusReal R = -moebiusReal R * sieveSeq l moebiusReal R := by
  have hR2 : 2 ≤ R := by nlinarith
  rw [sieveSeq_band_eq_sum_divisors_sub_quotients hlo hhi,
    sum_divisors_moebiusReal_eq_zero hR2, zero_sub, sieveSeq,
    Finset.sum_filter, neg_mul, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : d ∣ R
  · simp only [if_pos h, quotient_moebius hR h]
  · simp only [if_neg h, mul_zero]

private theorem source_coprime_primorial {l m : ℕ}
    (hm : Nat.Coprime (primorial l) m) (d : ℕ) :
    sieveSeq l moebiusReal (d * m) = sieveSeq l moebiusReal d := by
  apply (horizonRadicalState_eq_iff_all_squarefree_sieveSeq l (d * m) d).mp ?_
    moebiusReal moebiusReal_eq_zero_of_not_squarefree
  rw [horizonRadicalState_mul]
  have hstate : horizonRadicalState l m = 1 := hm.symm.gcd_eq_one
  rw [hstate]
  simp

-- A complete coprime sign band injects into one literal source level.
private theorem state_count_bound {B l d N : ℕ} (hl : 1 ≤ l) (hlB : l ≤ B + 1)
    (hd : d ∈ (primorial l).divisors) (hN : 1 ≤ N) (positive : Bool) :
    coprimeMoebiusSignCount (primorial l) ((l + 1) * N / d) positive ≤
      coprimeMoebiusSignCount (primorial l) (l * N / d) positive +
        moebiusSourceLevelCount B N
          (-moebiusReal d * (if positive then 1 else -1) * sieveSeq l moebiusReal d) := by
  classical
  have hdvd := (Nat.mem_divisors.mp hd).1
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdsf : Squarefree d := (squarefree_primorial l).squarefree_of_dvd hdvd
  let U := (Icc 1 ((l + 1) * N / d)).filter (fun m =>
    Nat.Coprime (primorial l) m ∧ μ m = (if positive then 1 else -1))
  let L := (Icc 1 (l * N / d)).filter (fun m =>
    Nat.Coprime (primorial l) m ∧ μ m = (if positive then 1 else -1))
  let S := (Icc 1 ((B + 2) * N)).filter (fun k => sieveSeq N moebiusReal k =
    -moebiusReal d * (if positive then 1 else -1) * sieveSeq l moebiusReal d)
  have hinj : (U \ L).card ≤ S.card := by
    apply Finset.card_le_card_of_injOn (fun m => d * m)
    · intro m hm
      rcases Finset.mem_sdiff.mp hm with ⟨hmU, hmL⟩
      rcases Finset.mem_filter.mp hmU with ⟨hmI, hcop, hsign⟩
      have hm1 := (mem_Icc.mp hmI).1
      have hmhi := (mem_Icc.mp hmI).2
      have hmlo : l * N / d < m := by
        by_contra! h
        exact hmL (Finset.mem_filter.mpr ⟨mem_Icc.mpr ⟨hm1, h⟩, hcop, hsign⟩)
      have hlo : l * N < d * m := by
        simpa only [mul_comm m d] using (Nat.div_lt_iff_lt_mul hdpos).mp hmlo
      have hhi : d * m ≤ (l + 1) * N := by
        simpa only [mul_comm m d] using (Nat.le_div_iff_mul_le hdpos).mp hmhi
      have hmsf : Squarefree m := by
        apply ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp
        rw [hsign]
        cases positive <;> norm_num
      have hdm : Nat.Coprime d m := hcop.of_dvd_left hdvd
      have hprod : moebiusReal (d * m) = moebiusReal d *
          (if positive then 1 else -1) := by
        have h := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hdm
        rw [hsign] at h
        cases positive <;> simpa [moebiusReal] using congrArg (Int.cast : ℤ → ℝ) h
      refine Finset.mem_filter.mpr ⟨mem_Icc.mpr ⟨by nlinarith,
        hhi.trans (Nat.mul_le_mul_right N (by omega))⟩, ?_⟩
      rw [source_reflection hN hl ((Nat.squarefree_mul hdm).mpr ⟨hdsf, hmsf⟩) hlo hhi,
        source_coprime_primorial hcop d, hprod]
      ring
    · intro m hm n hn h
      exact Nat.eq_of_mul_eq_mul_left hdpos h
  have hcard : U.card ≤ (U \ L).card + L.card := Finset.card_le_card_sdiff_add_card
  change U.card ≤ L.card + S.card
  omega

private theorem state_density_lower {B l d : ℕ} (hl : 1 ≤ l) (hlB : l ≤ B + 1)
    (hd : d ∈ (primorial l).divisors) (positive : Bool) :
    coprimeSquarefreeDensity (primorial l) / (2 * (d : ℝ) * ((B + 2 : ℕ) : ℝ)) ≤
      cofinalMobiusSourceDensity B
        (-moebiusReal d * (if positive then 1 else -1) * sieveSeq l moebiusReal d) := by
  have hdpos : 0 < d := Nat.pos_of_mem_divisors hd
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hdpos)
  have hA : (0 : ℝ) < ((B + 2 : ℕ) : ℝ) := by positivity
  let Q : ℕ+ := ⟨primorial l, primorial_pos l⟩
  let D : ℕ+ := ⟨d, hdpos⟩
  have hlim := ((tendsto_coprimeMoebiusSignCount_scaled Q ⟨l + 1, by omega⟩ D positive).sub
    (tendsto_coprimeMoebiusSignCount_scaled Q ⟨l, by omega⟩ D positive)).div_const
      (((B + 2 : ℕ) : ℝ))
  have hlim' : Tendsto (fun N : ℕ =>
      (((coprimeMoebiusSignCount (primorial l) ((l + 1) * N / d) positive : ℝ) -
        (coprimeMoebiusSignCount (primorial l) (l * N / d) positive : ℝ)) / (N : ℝ)) /
          (((B + 2 : ℕ) : ℝ))) atTop
      (𝓝 (coprimeSquarefreeDensity (primorial l) /
        (2 * (d : ℝ) * ((B + 2 : ℕ) : ℝ)))) := by
    convert hlim using 1
    · funext N
      simp only [Q, D, PNat.mk_coe, sub_div]
    · congr 1
      simp only [Q, D, PNat.mk_coe, Nat.cast_add, Nat.cast_one]
      field_simp
      ring
  apply le_of_tendsto_of_tendsto hlim' (tendsto_moebiusSourceLevelFrequency B _) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hcount := state_count_bound hl hlB hd hN positive
  have hreal : (coprimeMoebiusSignCount (primorial l) ((l + 1) * N / d) positive : ℝ) -
      (coprimeMoebiusSignCount (primorial l) (l * N / d) positive : ℝ) ≤
        (moebiusSourceLevelCount B N
          (-moebiusReal d * (if positive then 1 else -1) * sieveSeq l moebiusReal d) : ℝ) := by
    have hc : (coprimeMoebiusSignCount (primorial l) ((l + 1) * N / d) positive : ℝ) ≤
        (coprimeMoebiusSignCount (primorial l) (l * N / d) positive : ℝ) +
        (moebiusSourceLevelCount B N
          (-moebiusReal d * (if positive then 1 else -1) * sieveSeq l moebiusReal d) : ℝ) := by
      exact_mod_cast hcount
    linarith
  rw [div_div, Nat.cast_mul, mul_comm (N : ℝ)]
  exact (div_le_div_iff_of_pos_right
    (mul_pos hA (by exact_mod_cast (show 0 < N by omega)))).mpr hreal

private theorem signed_state_density_lower {B l d : ℕ} (hl : 1 ≤ l) (hlB : l ≤ B + 1)
    (hd : d ∈ (primorial l).divisors) (positive : Bool) :
    coprimeSquarefreeDensity (primorial l) / (2 * (d : ℝ) * ((B + 2 : ℕ) : ℝ)) ≤
      cofinalMobiusSourceDensity B
        (if positive then sieveSeq l moebiusReal d else -sieveSeq l moebiusReal d) := by
  have hp := state_density_lower hl hlB hd true
  have hn := state_density_lower hl hlB hd false
  have hdsf : Squarefree d := (squarefree_primorial l).squarefree_of_dvd
    (Nat.mem_divisors.mp hd).1
  have hd0 := ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hdsf
  rcases ArithmeticFunction.moebius_eq_or d with hm | hm | hm
  · exact (hd0 hm).elim
  · have hreal : moebiusReal d = 1 := by
      simpa [moebiusReal] using congrArg (Int.cast : ℤ → ℝ) hm
    simp [hreal] at hp hn
    cases positive
    · simpa using hp
    · simpa using hn
  · have hreal : moebiusReal d = -1 := by
      simpa [moebiusReal] using congrArg (Int.cast : ℤ → ℝ) hm
    simp [hreal] at hp hn
    cases positive
    · simpa using hn
    · simpa using hp

/-- Every finite quotient state supplies an explicit positive mass for either sign. -/
theorem cofinalMobiusSourceDensity_state_lower (B : ℕ) (l : Fin (B + 1))
    (d : {d : ℕ // d ∈ (primorial (l.val + 1)).divisors}) (positive : Bool) :
    coprimeSquarefreeDensity (primorial (l.val + 1)) /
        (2 * (d.val : ℝ) * ((B + 2 : ℕ) : ℝ)) ≤
      cofinalMobiusSourceDensity B
        (if positive then sieveSeq (l.val + 1) moebiusReal d.val
          else -sieveSeq (l.val + 1) moebiusReal d.val) :=
  signed_state_density_lower (by omega) (by omega) d.property positive

/-- The initial zero block survives as an atom of mass at least the reciprocal horizon ratio. -/
theorem cofinalMobiusSourceDensity_zero_lower (B : ℕ) :
    1 / ((B + 2 : ℕ) : ℝ) ≤ cofinalMobiusSourceDensity B 0 := by
  classical
  have hA : (0 : ℝ) < ((B + 2 : ℕ) : ℝ) := by positivity
  have hinv : Tendsto (fun N : ℕ => 1 / (N : ℝ)) atTop (𝓝 0) := by
    simpa only [one_div, Function.comp_def] using
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop :
        Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop)
  have hlim : Tendsto (fun N : ℕ => (1 - 1 / (N : ℝ)) / ((B + 2 : ℕ) : ℝ))
      atTop (𝓝 (1 / ((B + 2 : ℕ) : ℝ))) := by
    simpa only [sub_zero] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).sub hinv).div_const
        (((B + 2 : ℕ) : ℝ))
  apply le_of_tendsto_of_tendsto hlim (tendsto_moebiusSourceLevelFrequency B 0) ?_
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hcard : (Icc 2 N).card ≤ moebiusSourceLevelCount B N 0 := by
    unfold moebiusSourceLevelCount
    apply Finset.card_le_card
    intro k hk
    have hk1 := (mem_Icc.mp hk).1
    have hkN := (mem_Icc.mp hk).2
    have hNM : N ≤ (B + 2) * N := by
      simpa only [one_mul] using Nat.mul_le_mul_right N (show 1 ≤ B + 2 by omega)
    refine Finset.mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, hkN.trans hNM⟩, ?_⟩
    rw [sieveSeq_moebiusReal_eq_ite_of_le (by omega) hkN]
    simp [show k ≠ 1 by omega]
  have hNat : N - 1 ≤ moebiusSourceLevelCount B N 0 := by
    simpa only [Nat.card_Icc, show N + 1 - 2 = N - 1 by omega] using hcard
  have hreal : (N : ℝ) - 1 ≤ (moebiusSourceLevelCount B N 0 : ℝ) := by
    have h : ((N - 1 : ℕ) : ℝ) ≤ (moebiusSourceLevelCount B N 0 : ℝ) := by
      exact_mod_cast hNat
    simpa only [Nat.cast_sub hN, Nat.cast_one] using h
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have he : (1 - 1 / (N : ℝ)) / ((B + 2 : ℕ) : ℝ) =
      ((N : ℝ) - 1) / (((B + 2 : ℕ) : ℝ) * (N : ℝ)) := by
    field_simp
  rw [he, Nat.cast_mul]
  exact (div_le_div_iff_of_pos_right (mul_pos hA hNR)).mpr hreal

/-- Cofinal attainability and positive limiting frequency have exactly the same alphabet. -/
theorem cofinalMobiusSourceDensity_pos_iff_mem (B : ℕ) (a : ℝ) :
    0 < cofinalMobiusSourceDensity B a ↔ a ∈ moebiusLinearHorizonAlphabet (B + 1) := by
  classical
  constructor
  · intro h
    rcases cofinalMobiusSourceDensity_support B a with hz | ha
    · rw [hz] at h
      linarith
    · exact ha
  · intro ha
    simp only [moebiusLinearHorizonAlphabet, mem_union, mem_singleton,
      mem_biUnion, mem_insert] at ha
    rcases ha with h | ⟨l, hl, d, hd, h | h⟩
    · subst a
      exact lt_of_lt_of_le (div_pos (by norm_num) (by positivity))
        (cofinalMobiusSourceDensity_zero_lower B)
    · subst a
      have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
      exact lt_of_lt_of_le (div_pos (coprimeSquarefreeDensity_pos _) (by positivity))
        (signed_state_density_lower (mem_Icc.mp hl).1 (mem_Icc.mp hl).2 hd true)
    · subst a
      have hdR : (0 : ℝ) < d := by exact_mod_cast Nat.pos_of_mem_divisors hd
      exact lt_of_lt_of_le (div_pos (coprimeSquarefreeDensity_pos _) (by positivity))
        (signed_state_density_lower (mem_Icc.mp hl).1 (mem_Icc.mp hl).2 hd false)

end
end GaloisForLFunctions.BezoutValuationIncidence
