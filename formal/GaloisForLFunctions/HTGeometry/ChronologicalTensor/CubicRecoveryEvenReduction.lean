import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicChebyshevOptimizer

/-!
# The even monic reduction `E_{2m}(w) = 4^m t_m`

Put `r = (1 - t²)/4`.  For the weight `w(t) = √(1 - |t|)` raised to degree `2m`,

  `E_{2m}(w) = inf { sup_{[-1,1]} (1 - |t|)^m |P(t)| : P monic of degree 2m } = 4^m t_m`,

where `t_m` is the norm of the degree-`m` optimizer on `[0, 1/4]` for the weight
`W(r)^m = (1 - √(1 - 4r))^m`.  The infimum is attained by `P(t) = (-4)^m T_m((1 - t²)/4)`.  Conversely,
averaging a monic `P` with its reflection keeps it monic and cannot increase the even weighted norm;
the even average is `q(t²)` with `q` monic of degree `m`, and `(-1/4)^m q(1 - 4r)` is monic in `r`.
-/

open Set Polynomial

noncomputable section

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor

/-- The even weighted norm `sup_{t ∈ [-1,1]} (1 - |t|)^m |P(t)|`. -/
def evenWeightedNorm (m : ℕ) (P : Polynomial ℝ) : ℝ :=
  sSup ((fun t => (1 - |t|) ^ m * |P.eval t|) '' Icc (-1) 1)

theorem bddAbove_evenWeightedNorm (m : ℕ) (P : Polynomial ℝ) :
    BddAbove ((fun t => (1 - |t|) ^ m * |P.eval t|) '' Icc (-1) 1) :=
  (isCompact_Icc.image_of_continuousOn (by fun_prop)).bddAbove

theorem le_evenWeightedNorm {m : ℕ} (P : Polynomial ℝ) {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    (1 - |t|) ^ m * |P.eval t| ≤ evenWeightedNorm m P :=
  le_csSup (bddAbove_evenWeightedNorm m P) ⟨t, ht, rfl⟩

theorem bddAbove_cubicWeightedIntervalNorm (m : ℕ) (T : Polynomial ℝ) :
    BddAbove ((fun r : ℝ => cubicRadialWeight r ^ m * |T.eval r|) '' Icc 0 (1 / 4)) :=
  (isCompact_Icc.image_of_continuousOn ((cubicRadialWeight_continuous.pow m).mul
    (T.continuous.abs)).continuousOn).bddAbove

/-- `W((1 - t²)/4) = 1 - |t|`. -/
theorem cubicRadialWeight_one_sub_sq (t : ℝ) : cubicRadialWeight ((1 - t ^ 2) / 4) = 1 - |t| := by
  rw [cubicRadialWeight, show 1 - 4 * ((1 - t ^ 2) / 4) = t ^ 2 by ring, Real.sqrt_sq_eq_abs]

theorem one_sub_sq_div_four_mem {t : ℝ} (ht : t ∈ Icc (-1 : ℝ) 1) :
    (1 - t ^ 2) / 4 ∈ Icc (0 : ℝ) (1 / 4) := by
  have : t ^ 2 ≤ 1 := by nlinarith [ht.1, ht.2]
  constructor <;> nlinarith [sq_nonneg t]

/-! ### The even part -/

/-- The even part `q = Σ_{k ≤ m} P_{2k} X^k`, so that `q(t²) = (P(t) + P(-t))/2`. -/
def evenPartPoly (m : ℕ) (P : Polynomial ℝ) : Polynomial ℝ :=
  ∑ k ∈ Finset.range (m + 1), C (P.coeff (2 * k)) * X ^ k

theorem eval_evenPartPoly {m : ℕ} {P : Polynomial ℝ} (hdeg : P.natDegree ≤ 2 * m) (t : ℝ) :
    (evenPartPoly m P).eval (t ^ 2) = (P.eval t + P.eval (-t)) / 2 := by
  rw [eval_eq_sum_range' (n := 2 * m + 1) (by omega) t,
    eval_eq_sum_range' (n := 2 * m + 1) (by omega) (-t), ← Finset.sum_add_distrib,
    Finset.sum_div, evenPartPoly, eval_finsetSum]
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  -- only even indices survive
  have key : ∀ n : ℕ, ∑ i ∈ Finset.range (2 * n + 1), (P.coeff i * t ^ i + P.coeff i * (-t) ^ i) / 2 =
      ∑ k ∈ Finset.range (n + 1), P.coeff (2 * k) * (t ^ 2) ^ k := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ,
        Finset.sum_range_succ, ih, Finset.sum_range_succ (n := n + 1)]
      have hodd : (-t) ^ (2 * n + 1) = -t ^ (2 * n + 1) := Odd.neg_pow ⟨n, rfl⟩ t
      have heven : (-t) ^ (2 * n + 1 + 1) = t ^ (2 * n + 1 + 1) := Even.neg_pow ⟨n + 1, by ring⟩ t
      rw [hodd, heven, show 2 * n + 1 + 1 = 2 * (n + 1) by ring, pow_mul]
      ring
  exact (key m).symm

theorem evenPartPoly_natDegree_coeff {m : ℕ} {P : Polynomial ℝ} (hmon : P.coeff (2 * m) = 1) :
    (evenPartPoly m P).natDegree = m ∧ (evenPartPoly m P).coeff m = 1 := by
  have hcoeff : (evenPartPoly m P).coeff m = 1 := by
    rw [evenPartPoly, finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single m (fun k _ hk => if_neg (Ne.symm hk))
      (fun h => absurd (Finset.mem_range.mpr (Nat.lt_succ_self m)) h), if_pos rfl, hmon]
  refine ⟨natDegree_eq_of_le_of_coeff_ne_zero ?_ (by rw [hcoeff]; exact one_ne_zero), hcoeff⟩
  exact natDegree_sum_le_of_forall_le _ _ fun k hk =>
    (natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk))

/-- The monic `r`-polynomial `(-1/4)^m q(1 - 4r)` attached to a monic even `P` of degree `2m`. -/
def evenReductionPoly (m : ℕ) (P : Polynomial ℝ) : Polynomial ℝ :=
  C ((-1 / 4 : ℝ) ^ m) * (evenPartPoly m P).comp (C 1 - C 4 * X)

theorem evenReductionPoly_monic {m : ℕ} {P : Polynomial ℝ} (hmon : P.coeff (2 * m) = 1) :
    (evenReductionPoly m P).natDegree ≤ m ∧ (evenReductionPoly m P).coeff m = 1 := by
  obtain ⟨hdq, hcq⟩ := evenPartPoly_natDegree_coeff hmon
  have hform : (C 1 - C 4 * X : Polynomial ℝ) = C (-4) * X + C 1 := by rw [C_neg]; ring
  have hlin : (C 1 - C 4 * X : Polynomial ℝ).natDegree = 1 := by
    rw [hform, natDegree_add_C, natDegree_C_mul_X _ (by norm_num)]
  have hlinc : (C 1 - C 4 * X : Polynomial ℝ).leadingCoeff = -4 := by
    rw [leadingCoeff, hlin, hform]; simp [coeff_one]
  have hc : ((-1 / 4 : ℝ) ^ m) ≠ 0 := by positivity
  have hcomp : ((evenPartPoly m P).comp (C 1 - C 4 * X)).natDegree = m := by
    rw [natDegree_comp, hdq, hlin, mul_one]
  have hlc : ((evenPartPoly m P).comp (C 1 - C 4 * X)).leadingCoeff = (-4) ^ m := by
    rw [leadingCoeff_comp (by rw [hlin]; exact one_ne_zero), hlinc, leadingCoeff, hdq, hcq, one_mul]
  have hcm : ((evenPartPoly m P).comp (C 1 - C 4 * X)).coeff m = (-4) ^ m := by
    rw [← hlc, ← coeff_natDegree, hcomp]
  refine ⟨by rw [evenReductionPoly, natDegree_C_mul hc, hcomp], ?_⟩
  rw [evenReductionPoly, coeff_C_mul, hcm, ← mul_pow]
  norm_num

theorem eval_evenReductionPoly {m : ℕ} {P : Polynomial ℝ} (hdeg : P.natDegree ≤ 2 * m) (t : ℝ) :
    (evenReductionPoly m P).eval ((1 - t ^ 2) / 4) =
      (-1 / 4 : ℝ) ^ m * ((P.eval t + P.eval (-t)) / 2) := by
  rw [evenReductionPoly, eval_mul, eval_C, eval_comp]
  simp only [eval_sub, eval_C, eval_mul, eval_X]
  rw [show (1 : ℝ) - 4 * ((1 - t ^ 2) / 4) = t ^ 2 by ring, eval_evenPartPoly hdeg]

/-- **Every monic `P` of degree `2m` has even weighted norm at least `4^m t_m`.** -/
theorem four_pow_mul_le_evenWeightedNorm {m : ℕ} {T : Polynomial ℝ} (hT : IsCubicChebyshev m T)
    {P : Polynomial ℝ} (hdeg : P.natDegree ≤ 2 * m) (hmon : P.coeff (2 * m) = 1) :
    4 ^ m * cubicWeightedIntervalNorm m T ≤ evenWeightedNorm m P := by
  obtain ⟨hRdeg, hRmon⟩ := evenReductionPoly_monic (m := m) hmon
  have hopt := hT.2.2 _ hRdeg hRmon
  have h4 : (0 : ℝ) < 4 ^ m := by positivity
  refine (mul_le_mul_of_nonneg_left hopt h4.le).trans ?_
  rw [← le_div_iff₀' h4]
  refine csSup_le ((nonempty_Icc.mpr (by norm_num)).image _) ?_
  rintro v ⟨r, hr, rfl⟩
  set t := Real.sqrt (1 - 4 * r) with htdef
  have h14 : 0 ≤ 1 - 4 * r := by linarith [hr.2]
  have ht2 : t ^ 2 = 1 - 4 * r := Real.sq_sqrt h14
  have htmem : t ∈ Icc (-1 : ℝ) 1 :=
    ⟨by linarith [Real.sqrt_nonneg (1 - 4 * r)], Real.sqrt_le_one.mpr (by linarith [hr.1])⟩
  have hr' : r = (1 - t ^ 2) / 4 := by rw [ht2]; ring
  -- the even average does not exceed the norm of `P`
  have hP := le_evenWeightedNorm (m := m) P htmem
  have hPneg := le_evenWeightedNorm (m := m) P (t := -t) ⟨by linarith [htmem.2], by
    linarith [htmem.1]⟩
  rw [abs_neg] at hPneg
  simp only
  rw [hr', cubicRadialWeight_one_sub_sq, eval_evenReductionPoly hdeg, le_div_iff₀' h4]
  have hW : 0 ≤ (1 - |t|) ^ m := pow_nonneg (by linarith [abs_le.mpr ⟨htmem.1, htmem.2⟩]) m
  calc 4 ^ m * ((1 - |t|) ^ m * |(-1 / 4 : ℝ) ^ m * ((P.eval t + P.eval (-t)) / 2)|)
      = (1 - |t|) ^ m * |(P.eval t + P.eval (-t)) / 2| := by
        rw [abs_mul, abs_pow, show |(-1 / 4 : ℝ)| = 1 / 4 by norm_num]
        rw [show (4 : ℝ) ^ m * ((1 - |t|) ^ m * ((1 / 4) ^ m * |(P.eval t + P.eval (-t)) / 2|)) =
          (4 * (1 / 4)) ^ m * ((1 - |t|) ^ m * |(P.eval t + P.eval (-t)) / 2|) by
            rw [mul_pow]; ring]
        norm_num
    _ ≤ (1 - |t|) ^ m * ((|P.eval t| + |P.eval (-t)|) / 2) := by
        refine mul_le_mul_of_nonneg_left ?_ hW
        rw [abs_div, abs_two]
        exact div_le_div_of_nonneg_right (abs_add_le _ _) zero_le_two
    _ ≤ evenWeightedNorm m P := by nlinarith

/-- The Chebyshev lift `P(t) = (-4)^m T((1 - t²)/4)`. -/
def evenChebyshevLift (m : ℕ) (T : Polynomial ℝ) : Polynomial ℝ :=
  C ((-4 : ℝ) ^ m) * T.comp (C (-1 / 4) * X ^ 2 + C (1 / 4))

theorem evenChebyshevLift_monic {m : ℕ} {T : Polynomial ℝ} (hT : IsCubicChebyshev m T) :
    (evenChebyshevLift m T).natDegree ≤ 2 * m ∧ (evenChebyshevLift m T).coeff (2 * m) = 1 := by
  have hTdeg : T.natDegree = m :=
    natDegree_eq_of_le_of_coeff_ne_zero hT.1 (by rw [hT.2.1]; exact one_ne_zero)
  have hTlc : T.leadingCoeff = 1 := by rw [leadingCoeff, hTdeg, hT.2.1]
  have hσ : (C (-1 / 4 : ℝ) * X ^ 2 + C (1 / 4)).natDegree = 2 := by
    rw [natDegree_add_C, natDegree_C_mul_X_pow 2 _ (by norm_num)]
  have hσc : (C (-1 / 4 : ℝ) * X ^ 2 + C (1 / 4)).leadingCoeff = -1 / 4 := by
    rw [leadingCoeff, hσ]; simp
  have hc : ((-4 : ℝ) ^ m) ≠ 0 := by positivity
  have hcomp : (T.comp (C (-1 / 4 : ℝ) * X ^ 2 + C (1 / 4))).natDegree = 2 * m := by
    rw [natDegree_comp, hTdeg, hσ, mul_comm]
  have hlc : (T.comp (C (-1 / 4 : ℝ) * X ^ 2 + C (1 / 4))).leadingCoeff = (-1 / 4) ^ m := by
    rw [leadingCoeff_comp (by rw [hσ]; norm_num), hTlc, hσc, hTdeg, one_mul]
  have hcm : (T.comp (C (-1 / 4 : ℝ) * X ^ 2 + C (1 / 4))).coeff (2 * m) = (-1 / 4) ^ m := by
    rw [← hlc, ← coeff_natDegree, hcomp]
  refine ⟨by rw [evenChebyshevLift, natDegree_C_mul hc, hcomp], ?_⟩
  rw [evenChebyshevLift, coeff_C_mul, hcm, ← mul_pow]
  norm_num

theorem eval_evenChebyshevLift (m : ℕ) (T : Polynomial ℝ) (t : ℝ) :
    (evenChebyshevLift m T).eval t = (-4 : ℝ) ^ m * T.eval ((1 - t ^ 2) / 4) := by
  rw [evenChebyshevLift, eval_mul, eval_C, eval_comp]
  simp only [eval_add, eval_mul, eval_C, eval_pow, eval_X]
  congr 2; ring

/-- **The lift has even weighted norm `4^m ‖T‖_m`.** -/
theorem evenWeightedNorm_evenChebyshevLift (m : ℕ) (T : Polynomial ℝ) :
    evenWeightedNorm m (evenChebyshevLift m T) = 4 ^ m * cubicWeightedIntervalNorm m T := by
  have h4 : (0 : ℝ) < 4 ^ m := by positivity
  have hval : ∀ t, (1 - |t|) ^ m * |(evenChebyshevLift m T).eval t| =
      4 ^ m * (cubicRadialWeight ((1 - t ^ 2) / 4) ^ m * |T.eval ((1 - t ^ 2) / 4)|) := fun t => by
    rw [eval_evenChebyshevLift, cubicRadialWeight_one_sub_sq, abs_mul, abs_pow,
      show |(-4 : ℝ)| = 4 by norm_num]
    ring
  apply le_antisymm
  · refine csSup_le ((nonempty_Icc.mpr (by norm_num)).image _) ?_
    rintro v ⟨t, ht, rfl⟩
    simp only
    rw [hval]
    exact mul_le_mul_of_nonneg_left (le_csSup (bddAbove_cubicWeightedIntervalNorm m T)
      ⟨_, one_sub_sq_div_four_mem ht, rfl⟩) h4.le
  · rw [← le_div_iff₀' h4]
    refine csSup_le ((nonempty_Icc.mpr (by norm_num)).image _) ?_
    rintro v ⟨r, hr, rfl⟩
    set t := Real.sqrt (1 - 4 * r) with htdef
    have h14 : 0 ≤ 1 - 4 * r := by linarith [hr.2]
    have ht2 : t ^ 2 = 1 - 4 * r := Real.sq_sqrt h14
    have htmem : t ∈ Icc (-1 : ℝ) 1 :=
      ⟨by linarith [Real.sqrt_nonneg (1 - 4 * r)], Real.sqrt_le_one.mpr (by linarith [hr.1])⟩
    have hr' : r = (1 - t ^ 2) / 4 := by rw [ht2]; ring
    simp only
    rw [le_div_iff₀' h4, hr', ← hval]
    exact le_evenWeightedNorm _ htmem

/-- **`E_{2m}(w) = 4^m t_m`**: `4^m t_m` is the least even weighted norm of a monic polynomial of
degree `2m`. -/
theorem isLeast_evenWeightedNorm {m : ℕ} {T : Polynomial ℝ} (hT : IsCubicChebyshev m T) :
    IsLeast {v | ∃ P : Polynomial ℝ, P.natDegree ≤ 2 * m ∧ P.coeff (2 * m) = 1 ∧
      evenWeightedNorm m P = v} (4 ^ m * cubicWeightedIntervalNorm m T) := by
  refine ⟨⟨evenChebyshevLift m T, (evenChebyshevLift_monic hT).1,
    (evenChebyshevLift_monic hT).2, evenWeightedNorm_evenChebyshevLift m T⟩, ?_⟩
  rintro v ⟨P, hdeg, hmon, rfl⟩
  exact four_pow_mul_le_evenWeightedNorm hT hdeg hmon

end GaloisForLFunctions.HTGeometry.ChronologicalTensor
