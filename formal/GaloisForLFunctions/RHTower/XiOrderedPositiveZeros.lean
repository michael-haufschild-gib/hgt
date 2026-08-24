import GaloisForLFunctions.RHTower.XiZeroCountRVMRemainder

open Complex Set

namespace RHTower

noncomputable section

theorem xiZeroCount_zero : xiZeroCount 0 = 0 := by
  rw [xiZeroCount_eq_pos_sum (le_refl 0)]
  apply Finset.sum_eq_zero
  intro rho hrho
  rw [mem_xiSupportsPos] at hrho
  have := hrho.1
  rw [abs_of_pos hrho.2] at this
  exfalso
  linarith

theorem exists_xiZeroCount_eq_on_right {T : ℝ} (hT : 0 ≤ T) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ U : ℝ, T ≤ U → U ≤ T + δ → xiZeroCount U = xiZeroCount T := by
  classical
  set F : Finset ℝ := ((xiSupportsPos (T + 1)).filter
    (fun rho : XiDivisorSupport => T < (rho : ℂ).im)).image
      (fun rho : XiDivisorSupport => (rho : ℂ).im) with hFdef
  by_cases hF : F.Nonempty
  · set m : ℝ := F.min' hF with hm
    have hmmem : m ∈ F := by rw [hm]; exact F.min'_mem hF
    rw [hFdef, Finset.mem_image] at hmmem
    obtain ⟨rho, hrho, hrfl⟩ := hmmem
    rw [Finset.mem_filter, mem_xiSupportsPos] at hrho
    have hmT : T < m := by simpa [hrfl] using hrho.2
    have hmT1 : m ≤ T + 1 := by
      rw [hrfl, abs_of_pos hrho.1.2] at hrho
      exact hrho.1.1
    refine ⟨(m - T) / 2, by linarith, fun U hTU hU => ?_⟩
    apply le_antisymm
    · by_contra hnot
      have hlt : xiZeroCount T < xiZeroCount U := lt_of_not_ge hnot
      obtain ⟨z, hz, _hzre, hzim⟩ := exists_xi_zero_im_mem_Ioc_of_lt hTU hlt
      have hzmem := mem_xi_divisor_support_of_eq_zero hz
      set sigma : XiDivisorSupport := ⟨z, hzmem⟩ with hsigma
      have hzimL : T < z.im := hzim.1
      have hzimR : z.im ≤ U := hzim.2
      have hzimPos : 0 < z.im := lt_of_le_of_lt hT hzimL
      have hzimM : z.im < m := by linarith
      have hzimT1 : z.im ≤ T + 1 := by linarith
      have hmemF : z.im ∈ F := by
        rw [hFdef, Finset.mem_image]
        refine ⟨sigma, ?_, by simp [hsigma]⟩
        rw [Finset.mem_filter, mem_xiSupportsPos]
        simp only [hsigma]
        rw [abs_of_pos hzimPos]
        exact ⟨⟨hzimT1, hzimPos⟩, hzim.1⟩
      have hmin := F.min'_le z.im hmemF
      rw [← hm] at hmin
      linarith
    · exact xiZeroCount_mono hTU
  · refine ⟨1, by norm_num, fun U hTU hU => ?_⟩
    apply le_antisymm
    · by_contra hnot
      have hlt : xiZeroCount T < xiZeroCount U := lt_of_not_ge hnot
      obtain ⟨z, hz, _hzre, hzim⟩ := exists_xi_zero_im_mem_Ioc_of_lt hTU hlt
      have hzmem := mem_xi_divisor_support_of_eq_zero hz
      set sigma : XiDivisorSupport := ⟨z, hzmem⟩ with hsigma
      have hzimL : T < z.im := hzim.1
      have hzimR : z.im ≤ U := hzim.2
      have hzimPos : 0 < z.im := lt_of_le_of_lt hT hzimL
      have hzimT1 : z.im ≤ T + 1 := by linarith
      apply hF
      refine ⟨z.im, ?_⟩
      rw [hFdef, Finset.mem_image]
      refine ⟨sigma, ?_, by simp [hsigma]⟩
      rw [Finset.mem_filter, mem_xiSupportsPos]
      simp only [hsigma]
      rw [abs_of_pos hzimPos]
      exact ⟨⟨hzimT1, hzimPos⟩, hzim.1⟩
    · exact xiZeroCount_mono hTU

theorem exists_xiZeroCount_eq_on_left_of_no_zero {T : ℝ} (hT : 0 < T)
    (hno : ∀ z : ℂ, xi z = 0 → z.im ≠ T) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ T ∧ ∀ L : ℝ, T - δ ≤ L → L ≤ T →
      xiZeroCount L = xiZeroCount T := by
  classical
  set F : Finset ℝ := ((xiSupportsPos T).filter
    (fun rho : XiDivisorSupport => (rho : ℂ).im < T)).image
      (fun rho : XiDivisorSupport => (rho : ℂ).im) with hFdef
  by_cases hF : F.Nonempty
  · set m : ℝ := F.max' hF with hm
    have hmmem : m ∈ F := by rw [hm]; exact F.max'_mem hF
    rw [hFdef, Finset.mem_image] at hmmem
    obtain ⟨rho, hrho, hrfl⟩ := hmmem
    rw [Finset.mem_filter, mem_xiSupportsPos] at hrho
    have hm0 : 0 < m := by simpa [hrfl] using hrho.1.2
    have hmT : m < T := by simpa [hrfl] using hrho.2
    refine ⟨(T - m) / 2, by linarith, by linarith, fun L hL hLT => ?_⟩
    apply le_antisymm
    · exact xiZeroCount_mono hLT
    · by_contra hnot
      have hlt : xiZeroCount L < xiZeroCount T := lt_of_not_ge hnot
      obtain ⟨z, hz, _hzre, hzim⟩ := exists_xi_zero_im_mem_Ioc_of_lt hLT hlt
      have hzimT : z.im < T := lt_of_le_of_ne hzim.2 (hno z hz)
      have hLpos : 0 < L := by linarith
      have hzimPos : 0 < z.im := lt_trans hLpos hzim.1
      have hzmem := mem_xi_divisor_support_of_eq_zero hz
      set sigma : XiDivisorSupport := ⟨z, hzmem⟩ with hsigma
      have hmemF : z.im ∈ F := by
        rw [hFdef, Finset.mem_image]
        refine ⟨sigma, ?_, by simp [hsigma]⟩
        rw [Finset.mem_filter, mem_xiSupportsPos]
        simp only [hsigma]
        rw [abs_of_pos hzimPos]
        exact ⟨⟨hzim.2, hzimPos⟩, hzimT⟩
      have hmax := F.le_max' z.im hmemF
      rw [← hm] at hmax
      have hLz : L < z.im := hzim.1
      linarith
  · refine ⟨T / 2, by positivity, by linarith, fun L hL hLT => ?_⟩
    apply le_antisymm
    · exact xiZeroCount_mono hLT
    · by_contra hnot
      have hlt : xiZeroCount L < xiZeroCount T := lt_of_not_ge hnot
      obtain ⟨z, hz, _hzre, hzim⟩ := exists_xi_zero_im_mem_Ioc_of_lt hLT hlt
      have hzimT : z.im < T := lt_of_le_of_ne hzim.2 (hno z hz)
      have hLpos : 0 < L := by linarith
      have hzimPos : 0 < z.im := lt_trans hLpos hzim.1
      have hzmem := mem_xi_divisor_support_of_eq_zero hz
      set sigma : XiDivisorSupport := ⟨z, hzmem⟩ with hsigma
      apply hF
      refine ⟨z.im, ?_⟩
      rw [hFdef, Finset.mem_image]
      refine ⟨sigma, ?_, by simp [hsigma]⟩
      rw [Finset.mem_filter, mem_xiSupportsPos]
      simp only [hsigma]
      rw [abs_of_pos hzimPos]
      exact ⟨⟨hzim.2, hzimPos⟩, hzimT⟩

theorem exists_nat_succ_le_xiZeroCount (n : ℕ) :
    ∃ T : ℝ, ((n + 1 : ℕ) : ℤ) ≤ xiZeroCount T := by
  have hpi : 0 < Real.pi := Real.pi_pos
  obtain ⟨T₀, hT₀, hclose⟩ := exists_xiZeroCount_close (1 / (4 * Real.pi)) (by positivity)
  set T : ℝ := max (max T₀ 4) (4 * Real.pi * ((n : ℝ) + 1)) with hTdef
  have hTT₀ : T₀ ≤ T := le_trans (le_max_left _ _) (le_max_left _ _)
  have hT4 : (4 : ℝ) ≤ T := le_trans (le_max_right _ _) (le_max_left _ _)
  have hTn : 4 * Real.pi * ((n : ℝ) + 1) ≤ T := le_max_right _ _
  have hTpos : 0 < T := by linarith
  have hlog1 : 1 ≤ Real.log T := by
    rw [Real.le_log_iff_exp_le hTpos]
    linarith [Real.exp_one_lt_d9]
  have hb := hclose T hTT₀
  rw [abs_le] at hb
  have hreal : ((n : ℝ) + 1) ≤ (xiZeroCount T : ℝ) := by
    set E : ℝ := (1 / (4 * Real.pi)) * (T * Real.log T) with hE
    have hmain : ((n : ℝ) + 1) ≤ E := by
      have hprod : 4 * Real.pi * ((n : ℝ) + 1) ≤ T * Real.log T := by
        nlinarith
      rw [hE, show (1 / (4 * Real.pi)) * (T * Real.log T) =
        (T * Real.log T) / (4 * Real.pi) by ring,
        le_div_iff₀ (by positivity : (0 : ℝ) < 4 * Real.pi)]
      simpa [mul_comm, mul_left_comm, mul_assoc] using hprod
    have hcoeff : (1 / (2 * Real.pi)) * (T * Real.log T) = 2 * E := by
      rw [hE]
      field_simp [Real.pi_ne_zero]
      ring
    nlinarith
  refine ⟨T, ?_⟩
  exact_mod_cast hreal

def xiPositiveOrdinateUpperSet (n : ℕ) : Set ℝ :=
  {T : ℝ | ((n + 1 : ℕ) : ℤ) ≤ xiZeroCount T}

/-- Positive Xi ordinates in nondecreasing order, with multiplicity encoded by the count inverse. -/
def xiOrderedPositiveOrdinate (n : ℕ) : ℝ :=
  sInf (xiPositiveOrdinateUpperSet n)

theorem xiPositiveOrdinateUpperSet_nonempty (n : ℕ) :
    (xiPositiveOrdinateUpperSet n).Nonempty := by
  obtain ⟨T, hT⟩ := exists_nat_succ_le_xiZeroCount n
  exact ⟨T, hT⟩

theorem xiPositiveOrdinateUpperSet_bddBelow (n : ℕ) :
    BddBelow (xiPositiveOrdinateUpperSet n) := by
  refine ⟨0, fun T hT => ?_⟩
  by_contra hneg
  have hT0 : T ≤ 0 := le_of_not_ge hneg
  have hcount := xiZeroCount_mono hT0
  rw [xiZeroCount_zero] at hcount
  have hmem : ((n + 1 : ℕ) : ℤ) ≤ xiZeroCount T := hT
  omega

theorem xiOrderedPositiveOrdinate_nonneg (n : ℕ) :
    0 ≤ xiOrderedPositiveOrdinate n := by
  rw [xiOrderedPositiveOrdinate]
  exact le_csInf (xiPositiveOrdinateUpperSet_nonempty n)
    (fun T hT => by
      by_contra hneg
      have hT0 : T ≤ 0 := le_of_not_ge hneg
      have hcount := xiZeroCount_mono hT0
      rw [xiZeroCount_zero] at hcount
      have hmem : ((n + 1 : ℕ) : ℤ) ≤ xiZeroCount T := hT
      omega)

theorem xiOrderedPositiveOrdinate_mem_upperSet (n : ℕ) :
    xiOrderedPositiveOrdinate n ∈ xiPositiveOrdinateUpperSet n := by
  set gamma : ℝ := xiOrderedPositiveOrdinate n with hgamma
  have hgamma0 : 0 ≤ gamma := by simpa [hgamma] using xiOrderedPositiveOrdinate_nonneg n
  obtain ⟨delta, hdelta, hconst⟩ := exists_xiZeroCount_eq_on_right hgamma0
  have hinf : sInf (xiPositiveOrdinateUpperSet n) < gamma + delta := by
    change xiOrderedPositiveOrdinate n < gamma + delta
    rw [← hgamma]
    linarith
  obtain ⟨U, hUmem, hU⟩ := exists_lt_of_csInf_lt
    (xiPositiveOrdinateUpperSet_nonempty n) hinf
  have hgammaU : gamma ≤ U := by
    rw [hgamma, xiOrderedPositiveOrdinate]
    exact csInf_le (xiPositiveOrdinateUpperSet_bddBelow n) hUmem
  have hEq : xiZeroCount U = xiZeroCount gamma := hconst U hgammaU (by linarith)
  show ((n + 1 : ℕ) : ℤ) ≤ xiZeroCount gamma
  rw [← hEq]
  exact hUmem

/-- Generalized-inverse Galois law for the multiplicity-ordered positive Xi ordinates. -/
theorem xiOrderedPositiveOrdinate_le_iff {n : ℕ} {T : ℝ} :
    xiOrderedPositiveOrdinate n ≤ T ↔
      ((n + 1 : ℕ) : ℤ) ≤ xiZeroCount T := by
  constructor
  · intro hgamma
    have hmem := xiOrderedPositiveOrdinate_mem_upperSet n
    exact le_trans hmem (xiZeroCount_mono hgamma)
  · intro hT
    rw [xiOrderedPositiveOrdinate]
    exact csInf_le (xiPositiveOrdinateUpperSet_bddBelow n) hT

theorem xiOrderedPositiveOrdinate_pos (n : ℕ) :
    0 < xiOrderedPositiveOrdinate n := by
  have hnonneg := xiOrderedPositiveOrdinate_nonneg n
  refine lt_of_le_of_ne hnonneg ?_
  intro hzero
  have hmem := xiOrderedPositiveOrdinate_mem_upperSet n
  rw [← hzero] at hmem
  change ((n + 1 : ℕ) : ℤ) ≤ xiZeroCount 0 at hmem
  rw [xiZeroCount_zero] at hmem
  omega

theorem xiOrderedPositiveOrdinate_monotone : Monotone xiOrderedPositiveOrdinate := by
  intro n m hnm
  rw [xiOrderedPositiveOrdinate_le_iff]
  have hm := xiOrderedPositiveOrdinate_mem_upperSet m
  exact le_trans (by exact_mod_cast Nat.succ_le_succ hnm) hm

/-- Every multiplicity-ordered ordinate is attained by an actual Xi zero. -/
theorem exists_xi_zero_im_eq_xiOrderedPositiveOrdinate (n : ℕ) :
    ∃ z : ℂ, xi z = 0 ∧ z.im = xiOrderedPositiveOrdinate n := by
  by_contra h
  have hno : ∀ z : ℂ, xi z = 0 → z.im ≠ xiOrderedPositiveOrdinate n := by
    intro z hz him
    apply h
    exact ⟨z, hz, him⟩
  have hgammaPos := xiOrderedPositiveOrdinate_pos n
  obtain ⟨delta, hdelta, _hdeltaLe, hconst⟩ :=
    exists_xiZeroCount_eq_on_left_of_no_zero hgammaPos hno
  set L : ℝ := xiOrderedPositiveOrdinate n - delta / 2 with hL
  have hLlower : xiOrderedPositiveOrdinate n - delta ≤ L := by
    rw [hL]
    linarith
  have hLupper : L ≤ xiOrderedPositiveOrdinate n := by
    rw [hL]
    linarith
  have hLlt : L < xiOrderedPositiveOrdinate n := by
    rw [hL]
    linarith
  have heq := hconst L hLlower hLupper
  have hmem := xiOrderedPositiveOrdinate_mem_upperSet n
  change ((n + 1 : ℕ) : ℤ) ≤ xiZeroCount (xiOrderedPositiveOrdinate n) at hmem
  have hnot : ¬ ((n + 1 : ℕ) : ℤ) ≤ xiZeroCount L := by
    intro hLmem
    have hle : xiOrderedPositiveOrdinate n ≤ L :=
      xiOrderedPositiveOrdinate_le_iff.mpr hLmem
    linarith
  rw [heq] at hnot
  exact hnot hmem

/-- Under RH, the ordered ordinate gives the literal critical-line Xi zero. -/
theorem xi_half_add_orderedPositiveOrdinate_mul_I_eq_zero
    (hRH : RiemannHypothesis) (n : ℕ) :
    xi (((1 / 2 : ℝ) : ℂ) + (xiOrderedPositiveOrdinate n : ℂ) * I) = 0 := by
  obtain ⟨z, hz, hzim⟩ := exists_xi_zero_im_eq_xiOrderedPositiveOrdinate n
  have hre : z.re = 1 / 2 :=
    riemannHypothesis_iff_xi_zero_re_eq_half.mp hRH z hz
  have hzEq : z = ((1 / 2 : ℝ) : ℂ) + (xiOrderedPositiveOrdinate n : ℂ) * I := by
    apply Complex.ext
    · simpa using hre
    · simpa using hzim
  rw [← hzEq]
  exact hz

/-- Finite prefix of multiplicity-ordered positive Xi ordinates below height `T`. -/
def xiOrderedPositiveOrdinateCountFinset (T : ℝ) : Finset ℕ :=
  Finset.range (xiZeroCount T).toNat

/-- Exact generalized-inverse count law, including divisor multiplicity. -/
theorem mem_xiOrderedPositiveOrdinateCountFinset_iff {n : ℕ} {T : ℝ} :
    n ∈ xiOrderedPositiveOrdinateCountFinset T ↔
      xiOrderedPositiveOrdinate n ≤ T := by
  rw [xiOrderedPositiveOrdinateCountFinset, Finset.mem_range,
    xiOrderedPositiveOrdinate_le_iff]
  have hcast : (((xiZeroCount T).toNat : ℕ) : ℤ) = xiZeroCount T :=
    Int.toNat_of_nonneg (xiZeroCount_nonneg T)
  omega

theorem intCast_card_xiOrderedPositiveOrdinateCountFinset (T : ℝ) :
    ((xiOrderedPositiveOrdinateCountFinset T).card : ℤ) = xiZeroCount T := by
  rw [xiOrderedPositiveOrdinateCountFinset, Finset.card_range]
  exact Int.toNat_of_nonneg (xiZeroCount_nonneg T)

end

end RHTower
