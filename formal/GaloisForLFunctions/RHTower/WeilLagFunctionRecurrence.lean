import GaloisForLFunctions.RHTower.WeilLagFunctionInteger
import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet

/-!
# Recurrence of the integer lags to their ceiling

Under RH the lag function is the absolutely convergent cosine series
`Φ(L) = Σ_ρ cos(γ L)/(¼ + γ²)` with positive weights summing to `Φ(0) = 2 + γ − log 4π`.
Simultaneous Dirichlet approximation of finitely many ordinates shows that along the powers `b^m`
of any integer base `b ≥ 2` the integer lags `a_{b^m} = Φ(m log b)` return within any `ε` of the
ceiling `a_1`.  Hence under RH the supremum of `a_n` over `n ≥ 2` is exactly `a_1`, approached
along the powers of every base.
-/

open Real Filter Topology
open GaloisForLFunctions.HTGeometry (latticeClose exists_simultaneous_dirichlet)

namespace RHTower

noncomputable section

/-- The ordinate `γ` of a zero copy. -/
def zeroOrdinate (q : XiZeroCopy) : ℝ := (q.1 : ℂ).im

/-- The positive weight `1/(¼ + γ²)`. -/
def cosWeight (q : XiZeroCopy) : ℝ := 1 / (1 / 4 + zeroOrdinate q ^ 2)

theorem cosWeight_pos (q : XiZeroCopy) : 0 < cosWeight q := by
  unfold cosWeight; positivity

theorem xiZeroCopy_eq_of_riemannHypothesis (h : RiemannHypothesis) (q : XiZeroCopy) :
    (q.1 : ℂ) = 1 / 2 + (zeroOrdinate q : ℂ) * Complex.I := by
  apply Complex.ext
  · simp [zeroOrdinate, xiZeroCopy_re_eq_half_of_riemannHypothesis h q]
  · simp [zeroOrdinate]

theorem half_add_mul_I_mul_one_sub (γ : ℝ) :
    (1 / 2 + (γ : ℂ) * Complex.I) * (1 - (1 / 2 + (γ : ℂ) * Complex.I))
      = ((1 / 4 + γ ^ 2 : ℝ) : ℂ) := by
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem lagWeight_eq_of_riemannHypothesis (h : RiemannHypothesis) (q : XiZeroCopy) :
    lagWeight q = (cosWeight q : ℂ) := by
  unfold lagWeight cosWeight
  rw [xiZeroCopy_eq_of_riemannHypothesis h q, half_add_mul_I_mul_one_sub]
  push_cast
  ring

theorem summable_cosWeight (h : RiemannHypothesis) : Summable cosWeight := by
  refine summable_norm_lagWeight.congr fun q => ?_
  rw [lagWeight_eq_of_riemannHypothesis h q, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (cosWeight_pos q)]

/-- Under RH the lag function is the cosine series `Σ_ρ cos(γL)/(¼+γ²)`. -/
theorem weilLagFunctionReal_eq_cos_series (h : RiemannHypothesis) (L : ℝ) :
    weilLagFunctionReal L = ∑' q : XiZeroCopy, cosWeight q * Real.cos (zeroOrdinate q * L) := by
  unfold weilLagFunctionReal weilLagFunction
  rw [Complex.re_tsum (summable_weilLagTerm L)]
  congr 1
  funext q
  rw [xiZeroCopy_eq_of_riemannHypothesis h q, half_add_mul_I_mul_one_sub, Complex.div_ofReal_re]
  have e : (L : ℂ) * (1 / 2 + (zeroOrdinate q : ℂ) * Complex.I - 1 / 2)
      = ((zeroOrdinate q * L : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [e, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im,
    Complex.ofReal_im, mul_zero, zero_mul, sub_zero, add_zero]
  unfold cosWeight
  ring

/-- Under RH the weights sum to `a_1 = 2 + γ − log 4π`. -/
theorem tsum_cosWeight (h : RiemannHypothesis) :
    ∑' q : XiZeroCopy, cosWeight q = poleSharpConstant := by
  have := weilLagFunctionReal_eq_cos_series h 0
  simp only [mul_zero, Real.cos_zero, mul_one] at this
  rw [← this]
  unfold weilLagFunctionReal
  rw [weilLagFunction_zero, Complex.ofReal_re]

/-- **Recurrence to the ceiling.**  Under RH, for every base `b` and every `ε > 0` some power
`b^m` (`m ≥ 1`) has integer lag within `ε` of the ceiling `a_1 = 2 + γ − log 4π`. -/
theorem exists_pow_integerLag_gt_of_riemannHypothesis (h : RiemannHypothesis) (b : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, 1 ≤ m ∧ poleSharpConstant - ε < integerLag (b ^ m) := by
  classical
  have hw := summable_cosWeight h
  have hw0 : ∀ q, 0 ≤ cosWeight q := fun q => (cosWeight_pos q).le
  have htot := tsum_cosWeight h
  have hc0 := poleSharpConstant_pos
  -- a finite set of zeros carrying all but `ε/4` of the weight
  have htail := tendsto_tsum_compl_atTop_zero cosWeight
  obtain ⟨F, hF⟩ :=
    Filter.eventually_atTop.mp (htail.eventually_lt_const (by linarith : (0:ℝ) < ε / 4))
  have hFtail : ∑' q : {x // x ∉ F}, cosWeight q < ε / 4 := hF F le_rfl
  -- the resolution of the simultaneous approximation
  set Q : ℕ := ⌈8 * π ^ 2 * poleSharpConstant / ε⌉₊ + 1 with hQdef
  have hQ0 : 0 < Q := by omega
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ0
  have hQpos : (0:ℝ) < Q := by linarith
  have hQge : 8 * π ^ 2 * poleSharpConstant / ε ≤ Q := by
    have := Nat.le_ceil (8 * π ^ 2 * poleSharpConstant / ε)
    rw [hQdef]; push_cast; linarith
  have hδ : (2 * π / Q) ^ 2 / 2 * poleSharpConstant ≤ ε / 4 := by
    have h1 : (2 * π / Q) ^ 2 / 2 * poleSharpConstant
        = 2 * π ^ 2 * poleSharpConstant / ((Q : ℝ) ^ 2) := by
      field_simp
    have h2 : 2 * π ^ 2 * poleSharpConstant / ((Q : ℝ) ^ 2)
        ≤ 2 * π ^ 2 * poleSharpConstant / Q := by
      apply div_le_div_of_nonneg_left (by positivity) hQpos
      nlinarith
    have h3 : 2 * π ^ 2 * poleSharpConstant / (Q : ℝ) ≤ ε / 4 := by
      rw [div_le_iff₀ hQpos]
      have := (div_le_iff₀ hε).mp hQge
      linarith
    linarith
  -- the frequencies of the finitely many zeros
  let e := F.equivFin
  let β : Fin F.card → ℝ := fun i => zeroOrdinate (e.symm i).1 * Real.log b / (2 * π)
  obtain ⟨m, hm1, -, hclose⟩ := exists_simultaneous_dirichlet β hQ0
  refine ⟨m, hm1, ?_⟩
  have hval : integerLag (b ^ m)
      = ∑' q : XiZeroCopy, cosWeight q * Real.cos (zeroOrdinate q * (m * Real.log b)) := by
    unfold integerLag
    rw [weilLagFunctionReal_eq_cos_series h, Nat.cast_pow, Real.log_pow]
  -- the cosine lower bound on `F`
  have hcos : ∀ q ∈ F,
      1 - (2 * π / Q) ^ 2 / 2 ≤ Real.cos (zeroOrdinate q * (m * Real.log b)) := by
    intro q hq
    obtain ⟨p, hp⟩ := hclose (e ⟨q, hq⟩)
    have hβ : β (e ⟨q, hq⟩) = zeroOrdinate q * Real.log b / (2 * π) := by
      simp only [β, Equiv.symm_apply_apply]
    rw [hβ] at hp
    have hx : zeroOrdinate q * (m * Real.log b)
        = 2 * π * ((m : ℝ) * (zeroOrdinate q * Real.log b / (2 * π)) - p) + p * (2 * π) := by
      field_simp
      ring
    rw [hx, Real.cos_add_int_mul_two_pi]
    refine le_trans ?_ Real.one_sub_sq_div_two_le_cos
    have habs : |2 * π * ((m : ℝ) * (zeroOrdinate q * Real.log b / (2 * π)) - p)| ≤ 2 * π / Q := by
      rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * π)]
      calc 2 * π * |(m : ℝ) * (zeroOrdinate q * Real.log b / (2 * π)) - p| ≤ 2 * π * (1 / Q) :=
            mul_le_mul_of_nonneg_left hp.le (by positivity)
        _ = 2 * π / Q := by ring
    have hsq : (2 * π * ((m : ℝ) * (zeroOrdinate q * Real.log b / (2 * π)) - p)) ^ 2
        ≤ (2 * π / Q) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    linarith
  -- split the series at `F`
  set f : XiZeroCopy → ℝ := fun q => cosWeight q * Real.cos (zeroOrdinate q * (m * Real.log b))
    with hf
  have hfle : ∀ q, ‖f q‖ ≤ cosWeight q := by
    intro q
    rw [hf]
    simp only [Real.norm_eq_abs, abs_mul, abs_of_pos (cosWeight_pos q)]
    exact mul_le_of_le_one_right (hw0 q) (abs_cos_le_one _)
  have hfs : Summable f := hw.of_norm_bounded hfle
  have hsplit := hfs.sum_add_tsum_compl (s := F)
  have htailf : |∑' q : ↑(↑F : Set XiZeroCopy)ᶜ, f q| ≤ ∑' q : {x // x ∉ F}, cosWeight q := by
    have h1 : ‖∑' q : ↑(↑F : Set XiZeroCopy)ᶜ, f q‖ ≤ ∑' q : ↑(↑F : Set XiZeroCopy)ᶜ, ‖f q‖ :=
      norm_tsum_le_tsum_norm ((hfs.norm).subtype _)
    have h2 : ∑' q : ↑(↑F : Set XiZeroCopy)ᶜ, ‖f q‖ ≤ ∑' q : ↑(↑F : Set XiZeroCopy)ᶜ, cosWeight q :=
      Summable.tsum_le_tsum (fun q => hfle q) ((hfs.norm).subtype _) (hw.subtype _)
    rw [Real.norm_eq_abs] at h1
    exact h1.trans h2
  -- the finite part
  have hFsum : ∑ q ∈ F, cosWeight q = poleSharpConstant - ∑' q : {x // x ∉ F}, cosWeight q := by
    have := hw.sum_add_tsum_compl (s := F)
    rw [htot] at this
    have e' : ∑' q : ↑(↑F : Set XiZeroCopy)ᶜ, cosWeight q = ∑' q : {x // x ∉ F}, cosWeight q := rfl
    linarith
  have hFle : ∑ q ∈ F, cosWeight q ≤ poleSharpConstant := by
    rw [← htot]; exact hw.sum_le_tsum F (fun q _ => hw0 q)
  have hfin : ∑ q ∈ F, cosWeight q - ε / 4 ≤ ∑ q ∈ F, f q := by
    have h1 : ∑ q ∈ F, cosWeight q * (1 - (2 * π / Q) ^ 2 / 2) ≤ ∑ q ∈ F, f q := by
      refine Finset.sum_le_sum fun q hq => ?_
      rw [hf]
      exact mul_le_mul_of_nonneg_left (hcos q hq) (hw0 q)
    rw [← Finset.sum_mul] at h1
    have h3 : (∑ q ∈ F, cosWeight q) * ((2 * π / Q) ^ 2 / 2)
        ≤ poleSharpConstant * ((2 * π / Q) ^ 2 / 2) :=
      mul_le_mul_of_nonneg_right hFle (by positivity)
    have h4 : (∑ q ∈ F, cosWeight q) * (1 - (2 * π / Q) ^ 2 / 2)
        = ∑ q ∈ F, cosWeight q - (∑ q ∈ F, cosWeight q) * ((2 * π / Q) ^ 2 / 2) := by ring
    linarith
  rw [hval, ← hsplit]
  have := neg_abs_le (∑' q : ↑(↑F : Set XiZeroCopy)ᶜ, f q)
  linarith

/-- **The ceiling is the supremum.**  Under RH, `a_1 = 2 + γ − log 4π` is the least upper bound of
the integer lags `a_n`, `n ≥ 2`. -/
theorem isLUB_integerLag_of_riemannHypothesis (h : RiemannHypothesis) :
    IsLUB (Set.range fun n : {n : ℕ // 2 ≤ n} => integerLag n) poleSharpConstant := by
  constructor
  · rintro x ⟨n, rfl⟩
    exact riemannHypothesis_iff_integerLag_le_sharp.mp h n n.2
  · intro M hM
    by_contra hlt
    push Not at hlt
    obtain ⟨m, hm1, hgt⟩ :=
      exists_pow_integerLag_gt_of_riemannHypothesis h 2 (by linarith : 0 < poleSharpConstant - M)
    have h2 : 2 ≤ 2 ^ m := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
    have := hM ⟨⟨2 ^ m, h2⟩, rfl⟩
    simp only at this
    linarith

/-- Under RH the ceiling is the supremum of every tail `{a_n : n ≥ N}`. -/
theorem isLUB_integerLag_tail_of_riemannHypothesis (h : RiemannHypothesis) (N : ℕ) :
    IsLUB (Set.range fun n : {n : ℕ // N ≤ n} => integerLag n) poleSharpConstant := by
  constructor
  · rintro x ⟨n, rfl⟩
    exact (le_abs_self _).trans (abs_integerLag_le_of_riemannHypothesis h n)
  · intro M hM
    by_contra hlt
    push Not at hlt
    obtain ⟨m, hm1, hgt⟩ :=
      exists_pow_integerLag_gt_of_riemannHypothesis h (N + 1) (by linarith : 0 < poleSharpConstant - M)
    have hN : N ≤ (N + 1) ^ m := (Nat.le_succ N).trans (Nat.le_self_pow (by omega) _)
    have := hM ⟨⟨(N + 1) ^ m, hN⟩, rfl⟩
    simp only at this
    linarith

/-- **The ceiling is a limit point of the integer lags, unconditionally.**  For every `ε > 0` there
are arbitrarily large `n` with `a_n > 2 + γ − log 4π − ε`: under RH by recurrence, otherwise
because the sequence is unbounded above. -/
theorem frequently_integerLag_gt (ε : ℝ) (hε : 0 < ε) :
    ∃ᶠ n : ℕ in Filter.atTop, poleSharpConstant - ε < integerLag n := by
  classical
  rw [Filter.frequently_atTop]
  intro N
  by_cases h : RiemannHypothesis
  · obtain ⟨m, hm1, hgt⟩ := exists_pow_integerLag_gt_of_riemannHypothesis h (N + 1) hε
    exact ⟨(N + 1) ^ m, (Nat.le_succ N).trans (Nat.le_self_pow (by omega) _), hgt⟩
  · rcases integerLag_dichotomy with hbd | ⟨hup, -⟩
    · exact absurd (riemannHypothesis_iff_integerLag_le_sharp.mpr
        fun n _ => (le_abs_self _).trans (hbd n)) h
    · obtain ⟨B, hB⟩ := Finset.exists_le ((Finset.range N).image integerLag)
      obtain ⟨n, hn2, hn⟩ := hup (max B (poleSharpConstant - ε))
      refine ⟨n, ?_, lt_of_le_of_lt (le_max_right _ _) hn⟩
      by_contra hlt
      push Not at hlt
      have := hB _ (Finset.mem_image_of_mem integerLag (Finset.mem_range.mpr hlt))
      linarith [le_max_left B (poleSharpConstant - ε)]

/-- **The integer lag law.**  RH holds iff `a_n ≤ a_1` for all `n ≥ 1`; and then `a_1` is the exact
supremum of `a_n` over `n ≥ 2`, approached along the powers `b^m` of every base `b ≥ 2`. -/
theorem integerLag_law :
    (RiemannHypothesis ↔ ∀ n : ℕ, 1 ≤ n → integerLag n ≤ integerLag 1) ∧
      (RiemannHypothesis →
        IsLUB (Set.range fun n : {n : ℕ // 2 ≤ n} => integerLag n) (integerLag 1) ∧
        ∀ b : ℕ, 2 ≤ b → ∀ ε : ℝ, 0 < ε →
          ∃ m : ℕ, 1 ≤ m ∧ integerLag 1 - ε < integerLag (b ^ m) ∧ integerLag (b ^ m) ≤ integerLag 1) := by
  refine ⟨riemannHypothesis_iff_integerLag_le_one, fun h => ⟨?_, fun b hb ε hε => ?_⟩⟩
  · rw [integerLag_one]; exact isLUB_integerLag_of_riemannHypothesis h
  · obtain ⟨m, hm1, hgt⟩ := exists_pow_integerLag_gt_of_riemannHypothesis h b hε
    refine ⟨m, hm1, by rw [integerLag_one]; exact hgt, ?_⟩
    exact riemannHypothesis_iff_integerLag_le_one.mp h _ (Nat.one_le_pow _ _ (by omega))

end

end RHTower
