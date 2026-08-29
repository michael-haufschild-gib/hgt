import GaloisForLFunctions.RHTower.Sieve.SelbergDilatedLogMonomial

/-!
# The dilated Selberg log-monomial has the undilated leading coefficient

Every fixed pair of dilations `(a,b)` gives the same normalized limit
`(q+1)(r+1)/(q+r+1)`, and the whole family admits one envelope
`|Ŝ(q+1,r+1,a,b,N)| ≤ K·(log N)^{q+r+1}` uniform in `(a,b)`.  Both facts are needed by the
prime-peeling argument for the gcd-logarithmic Selberg family.
-/

open Finset Filter Topology
open scoped BigOperators

namespace RHTower.Sieve

noncomputable section

/-- Normalized Euler-correction term of the dilated form. -/
def selbergCorrectionDilatedTerm (q r a b N : ℕ) (mn : ℕ × ℕ) : ℝ :=
  if mn.1 ∈ Finset.Icc 1 (N / a) ∧ mn.2 ∈ Finset.Icc 1 (N / b) then
    selbergEulerCorrectionCoeff mn.1 mn.2 *
      (selbergPrincipalScaledLogPowerModel (q + 1) (r + 1) (a * mn.1) (b * mn.2) N /
        Real.log N ^ (q + r + 1))
  else 0

theorem tsum_selbergCorrectionDilatedTerm (q r a b N : ℕ) :
    (∑' mn : ℕ × ℕ, selbergCorrectionDilatedTerm q r a b N mn) =
      ∑ d ∈ Finset.Icc 1 (N / a), ∑ e ∈ Finset.Icc 1 (N / b),
        selbergEulerCorrectionCoeff d e *
          (selbergPrincipalScaledLogPowerModel (q + 1) (r + 1) (a * d) (b * e) N /
            Real.log N ^ (q + r + 1)) := by
  rw [tsum_eq_sum (s := (Finset.Icc 1 (N / a)) ×ˢ (Finset.Icc 1 (N / b)))]
  · rw [Finset.sum_product]
    apply Finset.sum_congr rfl
    intro d hd
    apply Finset.sum_congr rfl
    intro e he
    simp [selbergCorrectionDilatedTerm, hd, he]
  · intro mn hmn
    simp only [Finset.mem_product] at hmn
    rw [selbergCorrectionDilatedTerm, if_neg hmn]

/-- The normalized dilated form is exactly the correction `tsum`. -/
theorem selbergOriginalDilatedLogMonomial_div_log_pow_eq_tsum
    (q r : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (N : ℕ) :
    selbergOriginalDilatedLogMonomial (q + 1) (r + 1) a b N /
        Real.log N ^ (q + r + 1) =
      ∑' mn : ℕ × ℕ, selbergCorrectionDilatedTerm q r a b N mn := by
  rw [tsum_selbergCorrectionDilatedTerm,
    selbergOriginalDilatedLogMonomial_eq_correction_scaled (q + 1) (r + 1) ha hb N,
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro d _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- One majorant for every dilation and every correction index. -/
theorem exists_eventually_norm_selbergCorrectionDilatedTerm_le (q r : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ᶠ N : ℕ in atTop, ∀ a b : ℕ, 0 < a → 0 < b →
      ∀ mn : ℕ × ℕ,
        ‖selbergCorrectionDilatedTerm q r a b N mn‖ ≤
          M * |selbergEulerCorrectionCoeff mn.1 mn.2| := by
  obtain ⟨M, hM, hMbound⟩ := exists_abs_selbergPrincipalScaledLogPowerModel_le q r
  refine ⟨M, hM, ?_⟩
  filter_upwards [hMbound, eventually_ge_atTop 2] with N hN hN2 a b ha hb mn
  have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  rw [selbergCorrectionDilatedTerm]
  split_ifs with hab
  · obtain ⟨hdMem, heMem⟩ := hab
    have hd : 0 < mn.1 := (Finset.mem_Icc.mp hdMem).1
    have he : 0 < mn.2 := (Finset.mem_Icc.mp heMem).1
    have hmodel := hN (a * mn.1) (b * mn.2) (Nat.mul_pos ha hd) (Nat.mul_pos hb he)
    rw [Real.norm_eq_abs, abs_mul, abs_div,
      abs_of_pos (pow_pos hlogpos (q + r + 1))]
    have hscaled :
        |selbergPrincipalScaledLogPowerModel (q + 1) (r + 1)
            (a * mn.1) (b * mn.2) N| / Real.log N ^ (q + r + 1) ≤ M := by
      rw [div_le_iff₀ (pow_pos hlogpos (q + r + 1))]
      exact hmodel
    calc |selbergEulerCorrectionCoeff mn.1 mn.2| *
          (|selbergPrincipalScaledLogPowerModel (q + 1) (r + 1)
              (a * mn.1) (b * mn.2) N| / Real.log N ^ (q + r + 1))
        ≤ |selbergEulerCorrectionCoeff mn.1 mn.2| * M :=
          mul_le_mul_of_nonneg_left hscaled
            (abs_nonneg (selbergEulerCorrectionCoeff mn.1 mn.2))
      _ = M * |selbergEulerCorrectionCoeff mn.1 mn.2| := mul_comm _ _
  · simp
    positivity

/-- Termwise limit of the dilated correction convolution. -/
theorem tendsto_selbergCorrectionDilatedTerm
    (q r : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (mn : ℕ × ℕ) :
    Tendsto (fun N : ℕ => selbergCorrectionDilatedTerm q r a b N mn)
      atTop (𝓝 ((((q : ℝ) + 1) * ((r : ℝ) + 1)) / ((q : ℝ) + (r : ℝ) + 1) *
        selbergEulerCorrectionCoeff mn.1 mn.2)) := by
  rcases mn with ⟨d, e⟩
  rcases d.eq_zero_or_pos with rfl | hd
  · simp [selbergCorrectionDilatedTerm, selbergEulerCorrectionCoeff]
  rcases e.eq_zero_or_pos with rfl | he
  · simp [selbergCorrectionDilatedTerm, selbergEulerCorrectionCoeff]
  have hmain :=
    (tendsto_selbergPrincipalScaledLogPowerModel_div_log_pow q r
      (Nat.mul_pos ha hd) (Nat.mul_pos hb he)).const_mul
      (selbergEulerCorrectionCoeff d e)
  simpa only [mul_comm] using hmain.congr' (by
    filter_upwards [eventually_ge_atTop (a * d), eventually_ge_atTop (b * e)]
      with N hNa hNb
    rw [selbergCorrectionDilatedTerm, if_pos]
    exact ⟨Finset.mem_Icc.mpr ⟨hd, (Nat.le_div_iff_mul_le ha).2 (by
        rw [Nat.mul_comm]; exact hNa)⟩,
      Finset.mem_Icc.mpr ⟨he, (Nat.le_div_iff_mul_le hb).2 (by
        rw [Nat.mul_comm]; exact hNb)⟩⟩)

/-- **The dilated Selberg log-monomial has the same leading coefficient as the undilated one.** -/
theorem tendsto_selbergOriginalDilatedLogMonomial_div_log_pow
    (q r : ℕ) {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun N : ℕ =>
      selbergOriginalDilatedLogMonomial (q + 1) (r + 1) a b N /
        Real.log N ^ (q + r + 1))
      atTop (𝓝 ((((q : ℝ) + 1) * ((r : ℝ) + 1)) / ((q : ℝ) + (r : ℝ) + 1))) := by
  obtain ⟨M, hM, hdomEventually⟩ :=
    exists_eventually_norm_selbergCorrectionDilatedTerm_le q r
  have hsumAbs : Summable (fun mn : ℕ × ℕ =>
      M * |selbergEulerCorrectionCoeff mn.1 mn.2|) := by
    have hnorm := summable_selbergEulerCorrectionCoeff.norm
    have habs : Summable (fun mn : ℕ × ℕ =>
        |selbergEulerCorrectionCoeff mn.1 mn.2|) := by
      simpa [Real.norm_eq_abs] using hnorm
    exact habs.mul_left M
  have hdom : ∀ᶠ N : ℕ in atTop, ∀ mn : ℕ × ℕ,
      ‖selbergCorrectionDilatedTerm q r a b N mn‖ ≤
        M * |selbergEulerCorrectionCoeff mn.1 mn.2| := by
    filter_upwards [hdomEventually] with N hN mn
    exact hN a b ha hb mn
  have hconv := tendsto_tsum_of_dominated_convergence hsumAbs
    (tendsto_selbergCorrectionDilatedTerm q r ha hb) hdom
  rw [tsum_mul_left, tsum_selbergEulerCorrectionCoeff, mul_one] at hconv
  refine hconv.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with N _
  exact (selbergOriginalDilatedLogMonomial_div_log_pow_eq_tsum q r ha hb N).symm

/-- **One envelope for the whole dilated family.** -/
theorem exists_abs_selbergOriginalDilatedLogMonomial_le (q r : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop, ∀ a b : ℕ, 0 < a → 0 < b →
      |selbergOriginalDilatedLogMonomial (q + 1) (r + 1) a b N| ≤
        K * Real.log N ^ (q + r + 1) := by
  obtain ⟨M, hM, hMbound⟩ := exists_abs_selbergPrincipalScaledLogPowerModel_le q r
  have habs : Summable (fun mn : ℕ × ℕ =>
      |selbergEulerCorrectionCoeff mn.1 mn.2|) := by
    have hnorm := summable_selbergEulerCorrectionCoeff.norm
    simpa [Real.norm_eq_abs] using hnorm
  have hSnn : 0 ≤ ∑' mn : ℕ × ℕ, |selbergEulerCorrectionCoeff mn.1 mn.2| :=
    tsum_nonneg fun _ => abs_nonneg _
  refine ⟨M * (∑' mn : ℕ × ℕ, |selbergEulerCorrectionCoeff mn.1 mn.2|),
    mul_nonneg hM hSnn, ?_⟩
  filter_upwards [hMbound, eventually_ge_atTop 2] with N hN hN2 a b ha hb
  have hlogpos : 0 < Real.log N := Real.log_pos (by exact_mod_cast hN2)
  have hpow : (0 : ℝ) ≤ Real.log N ^ (q + r + 1) := pow_nonneg hlogpos.le _
  rw [selbergOriginalDilatedLogMonomial_eq_correction_scaled (q + 1) (r + 1) ha hb N]
  have hterm : ∀ d ∈ Finset.Icc 1 (N / a), ∀ e ∈ Finset.Icc 1 (N / b),
      |selbergEulerCorrectionCoeff d e *
          selbergPrincipalScaledLogPowerModel (q + 1) (r + 1) (a * d) (b * e) N| ≤
        |selbergEulerCorrectionCoeff d e| * (M * Real.log N ^ (q + r + 1)) := by
    intro d hd e he
    have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
    have he0 : 0 < e := (Finset.mem_Icc.mp he).1
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left
      (hN (a * d) (b * e) (Nat.mul_pos ha hd0) (Nat.mul_pos hb he0))
      (abs_nonneg _)
  calc
    |∑ d ∈ Finset.Icc 1 (N / a), ∑ e ∈ Finset.Icc 1 (N / b),
        selbergEulerCorrectionCoeff d e *
          selbergPrincipalScaledLogPowerModel (q + 1) (r + 1) (a * d) (b * e) N|
        ≤ ∑ d ∈ Finset.Icc 1 (N / a), |∑ e ∈ Finset.Icc 1 (N / b),
            selbergEulerCorrectionCoeff d e *
              selbergPrincipalScaledLogPowerModel (q + 1) (r + 1) (a * d) (b * e) N| :=
          Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Finset.Icc 1 (N / a), ∑ e ∈ Finset.Icc 1 (N / b),
          |selbergEulerCorrectionCoeff d e| * (M * Real.log N ^ (q + r + 1)) := by
          refine Finset.sum_le_sum ?_
          intro d hd
          refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
          exact Finset.sum_le_sum (hterm d hd)
    _ = (∑ p ∈ (Finset.Icc 1 (N / a)) ×ˢ (Finset.Icc 1 (N / b)),
            |selbergEulerCorrectionCoeff p.1 p.2|) *
          (M * Real.log N ^ (q + r + 1)) := by
          rw [Finset.sum_product, Finset.sum_mul]
          exact Finset.sum_congr rfl fun d _ => (Finset.sum_mul _ _ _).symm
    _ ≤ (∑' mn : ℕ × ℕ, |selbergEulerCorrectionCoeff mn.1 mn.2|) *
          (M * Real.log N ^ (q + r + 1)) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact Summable.sum_le_tsum _ (fun i _ => abs_nonneg _) habs
    _ = M * (∑' mn : ℕ × ℕ, |selbergEulerCorrectionCoeff mn.1 mn.2|) *
          Real.log N ^ (q + r + 1) := by ring

end

end RHTower.Sieve
