import GaloisForLFunctions.RHTower.VerticalProgressionMollifier

/-!
# The twisted mollified first moment along a vertical progression: Dirichlet expansion

With `t_ℓ = αℓ + β`, `s_ℓ = ½ + it_ℓ`, a weight `φ` supported in `[1, 2]` and a twist `γ ∈ ℝ`,

`J(T) = Σ_{ℓ ∈ ℤ} φ(ℓ/T) e(ℓγ) ζ(s_ℓ) M_N(s_ℓ)`.

**Theorem** (`norm_firstMoment_sub_expansion_le`). For `X > 0`, `2|β| ≤ αT` and `αT ≥ 2`,

`J(T) = Σ_{m ≥ 1} a(m) m^{−½−iβ} L_T(γ − α log m/2π) + E`,
`‖E‖ ≤ (T + 1) Φ₀ (C(1 + 3αT)/X + X^{1/2} e^{1/4 − (αT/2)²}) 2√N`,

where `a(m) = Σ_{h | m, h ≤ N} b_N(h) V((m/h)/X)` and `L_T(u) = Σ_ℓ φ(ℓ/T) e(ℓu)`.

**Proof.** Replace `ζ(s_ℓ)` by the long smoothed series (error from the Gaussian AFE), multiply by
the mollifier, and exchange the finite `ℓ`-sum with the absolutely convergent `m`-series; then
`m^{−s_ℓ} e(ℓγ) = m^{−½−iβ} e(ℓ(γ − α log m/2π))`.

The coefficient bounds `‖a(m)‖ ≤ d(m)` and `‖a(m)‖ ≤ N K_A (NX/m)^A` are also recorded.
-/

open Complex MeasureTheory Set Filter

namespace RHTower.VerticalAP

noncomputable section

/-- `ζ(½ + i(αx + β)) M_N(½ + i(αx + β))`. -/
def apMollZeta (N : ℕ) (α β x : ℝ) : ℂ :=
  riemannZeta (critPt (α * x + β)) * linMoll N (critPt (α * x + β))

/-- The twisted mollified first moment `J(T) = Σ φ(ℓ/T) e(ℓγ) (ζM)(s_ℓ)`. -/
def firstMoment (φ : ℝ → ℂ) (α β γ : ℝ) (N : ℕ) (T : ℝ) : ℂ :=
  latticeSum (fun x => φ (x / T) * apMollZeta N α β x) γ

/-- `L_T(u) = Σ_ℓ φ(ℓ/T) e(ℓu)`. -/
def bumpSum (φ : ℝ → ℂ) (T u : ℝ) : ℂ := latticeSum (fun x => φ (x / T)) u

/-! ## Coefficient bounds -/

theorem norm_mollCoeff_le_card_divisors (N : ℕ) {X : ℝ} (hX : 0 < X) {m : ℕ} (hm : 1 ≤ m) :
    ‖mollCoeff N X m‖ ≤ (m.divisors.card : ℝ) := by
  unfold mollCoeff
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ h ∈ Finset.Icc 1 N, ‖if h ∣ m then (Sieve.linearMollifierCoeff N h : ℂ) *
      smoothAFECutoff (((m / h : ℕ) : ℝ) / X) else 0‖ ≤ if h ∣ m then (1 : ℝ) else 0 := by
    intro h hh
    split_ifs with hd
    · obtain ⟨q, hq⟩ := hd
      have hpos : 0 < h := (Finset.mem_Icc.mp hh).1
      have hq0 : 0 < q := by
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · rw [h0, mul_zero] at hq; omega
        · exact h0
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hV : ‖smoothAFECutoff (((m / h : ℕ) : ℝ) / X)‖ ≤ 1 := by
        rw [hq, Nat.mul_div_cancel_left _ hpos]
        exact norm_smoothAFECutoff_le_one' (div_pos (by exact_mod_cast hq0) hX)
      calc |Sieve.linearMollifierCoeff N h| * ‖smoothAFECutoff (((m / h : ℕ) : ℝ) / X)‖
          ≤ 1 * 1 := mul_le_mul (abs_linearMollifierCoeff_le_one hh) hV (norm_nonneg _) zero_le_one
        _ = 1 := one_mul 1
    · simp
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hsub : (Finset.Icc 1 N).filter (· ∣ m) ⊆ m.divisors := by
    intro h hh
    rw [Finset.mem_filter] at hh
    exact Nat.mem_divisors.mpr ⟨hh.2, by omega⟩
  exact_mod_cast Finset.card_le_card hsub

theorem norm_mollCoeff_le_decay {A : ℝ} (hA : 0 < A) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) {X : ℝ}, 0 < X → ∀ {m : ℕ}, 1 ≤ m →
      ‖mollCoeff N X m‖ ≤ N * (K * ((N : ℝ) * X / m) ^ A) := by
  obtain ⟨K, hK, hKb⟩ := exists_norm_smoothAFECutoff_le_neg_rpow hA
  refine ⟨K, hK, fun N {X} hX {m} hm => ?_⟩
  unfold mollCoeff
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ h ∈ Finset.Icc 1 N, ‖if h ∣ m then (Sieve.linearMollifierCoeff N h : ℂ) *
      smoothAFECutoff (((m / h : ℕ) : ℝ) / X) else 0‖ ≤ K * ((N : ℝ) * X / m) ^ A := by
    intro h hh
    have hbound : 0 ≤ K * ((N : ℝ) * X / m) ^ A := by positivity
    split_ifs with hd
    · obtain ⟨q, hq⟩ := hd
      obtain ⟨hpos, hhN⟩ := Finset.mem_Icc.mp hh
      have hq0 : 0 < q := by
        rcases Nat.eq_zero_or_pos q with h0 | h0
        · rw [h0, mul_zero] at hq; omega
        · exact h0
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hqX : 0 < (q : ℝ) / X := div_pos (by exact_mod_cast hq0) hX
      have hV := hKb hqX
      have hmR : (m : ℝ) = h * q := by exact_mod_cast hq
      have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hpos
      have hhN' : (h : ℝ) ≤ N := by exact_mod_cast hhN
      have hqpos : (0 : ℝ) < q := by exact_mod_cast hq0
      have hle : ((q : ℝ) / X) ^ (-A) ≤ ((N : ℝ) * X / m) ^ A := by
        rw [Real.rpow_neg hqX.le, ← Real.inv_rpow hqX.le, inv_div]
        refine Real.rpow_le_rpow (by positivity) ?_ hA.le
        rw [hmR, div_le_div_iff₀ hqpos (by positivity)]
        nlinarith [mul_le_mul_of_nonneg_right hhN' (le_of_lt (mul_pos hX hqpos))]
      have hdiv : m / h = q := by rw [hq, Nat.mul_div_cancel_left _ hpos]
      rw [hdiv]
      calc |Sieve.linearMollifierCoeff N h| * ‖smoothAFECutoff ((q : ℝ) / X)‖
          ≤ 1 * (K * ((N : ℝ) * X / m) ^ A) :=
            mul_le_mul (abs_linearMollifierCoeff_le_one hh) (hV.trans
              (mul_le_mul_of_nonneg_left hle hK)) (norm_nonneg _) zero_le_one
        _ = K * ((N : ℝ) * X / m) ^ A := one_mul _
    · simpa using hbound
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, Nat.add_sub_cancel]

theorem summable_mollSeries (N : ℕ) {X : ℝ} (hX : 0 < X) {s : ℂ} (hs : 0 ≤ s.re) :
    Summable (fun m : ℕ => mollCoeff N X (m + 1) * (m + 1 : ℂ) ^ (-s)) := by
  obtain ⟨K, hK, hKb⟩ := norm_mollCoeff_le_decay (A := 2) two_pos
  have hsum : Summable (fun m : ℕ =>
      N * (K * ((N : ℝ) * X) ^ (2 : ℝ)) * (((m : ℝ) + 1) ^ (2 : ℝ))⁻¹) := by
    have := (Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 2)).comp_injective
      (add_left_injective 1)
    refine (this.congr fun n => ?_).mul_left _
    simp
  refine hsum.of_norm_bounded fun m => ?_
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  rw [norm_mul]
  have h1 : ‖(m + 1 : ℂ) ^ (-s)‖ ≤ 1 := by
    have : ((m : ℂ) + 1) = (((m : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_cpow_eq_rpow_re_of_pos hm]
    exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith [m.cast_nonneg (α := ℝ)])
      (by simp; exact hs)
  have h2 := hKb N hX (m := m + 1) (by omega)
  have h3 : ((N : ℝ) * X / ((m + 1 : ℕ) : ℝ)) ^ (2 : ℝ) =
      ((N : ℝ) * X) ^ (2 : ℝ) * (((m : ℝ) + 1) ^ (2 : ℝ))⁻¹ := by
    push_cast
    rw [Real.div_rpow (by positivity) hm.le, div_eq_mul_inv]
  rw [h3] at h2
  calc ‖mollCoeff N X (m + 1)‖ * ‖(m + 1 : ℂ) ^ (-s)‖
      ≤ (N * (K * (((N : ℝ) * X) ^ (2 : ℝ) * (((m : ℝ) + 1) ^ (2 : ℝ))⁻¹))) * 1 :=
        mul_le_mul h2 h1 (norm_nonneg _) (by positivity)
    _ = N * (K * ((N : ℝ) * X) ^ (2 : ℝ)) * (((m : ℝ) + 1) ^ (2 : ℝ))⁻¹ := by ring

/-! ## Phases -/

/-- `m^{−s_ℓ} e(ℓγ) = m^{−½−iβ} e(ℓ(γ − α log m/2π))`. -/
theorem natSucc_cpow_neg_critPt_mul_unitExp (m : ℕ) (α β γ : ℝ) (ℓ : ℝ) :
    (m + 1 : ℂ) ^ (-critPt (α * ℓ + β)) * unitExp (ℓ * γ) =
      (m + 1 : ℂ) ^ (-critPt β) * unitExp (ℓ * (γ - α * Real.log (m + 1) / (2 * Real.pi))) := by
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hcast : ((m : ℂ) + 1) = (((m : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, ZetaNotch.ofReal_cpow_eq_exp hm, ZetaNotch.ofReal_cpow_eq_exp hm]
  unfold unitExp critPt
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  push_cast
  field_simp
  ring

/-! ## The expansion -/

/-- **Dirichlet expansion of the first moment.** -/
theorem norm_firstMoment_sub_expansion_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {φ : ℝ → ℂ}, Function.support φ ⊆ Icc 1 2 → ∀ {Φ₀ : ℝ},
      (∀ y, ‖φ y‖ ≤ Φ₀) → ∀ {α β : ℝ} (γ : ℝ) (N : ℕ) {T X : ℝ}, 0 < α → 0 < X →
      2 * |β| ≤ α * T → 2 ≤ α * T →
      ‖firstMoment φ α β γ N T -
          ∑' m : ℕ, mollCoeff N X (m + 1) * (m + 1 : ℂ) ^ (-critPt β) *
            bumpSum φ T (γ - α * Real.log (m + 1) / (2 * Real.pi))‖ ≤
        (T + 1) * (Φ₀ * ((C * (1 + 3 * α * T) / X +
          X ^ (1 / 2 : ℝ) * Real.exp (1 / 4 - (α * T / 2) ^ 2)) * (2 * Real.sqrt N))) := by
  obtain ⟨C, hC, hζ⟩ := exists_norm_zeta_sub_smoothSum_le
  refine ⟨C, hC, fun {φ} hsupp {Φ₀} hΦ₀ {α β} γ N {T X} hα hX hβ hαT => ?_⟩
  have hT : 0 < T := by
    by_contra h; push Not at h; nlinarith
  have hΦ0 : 0 ≤ Φ₀ := (norm_nonneg _).trans (hΦ₀ 0)
  set D : ℝ → ℂ := fun x => ∑' n : ℕ, (n + 1 : ℂ) ^ (-critPt (α * x + β)) *
    smoothAFECutoff ((n + 1 : ℝ) / X) with hD
  set E : ℝ := (C * (1 + 3 * α * T) / X +
    X ^ (1 / 2 : ℝ) * Real.exp (1 / 4 - (α * T / 2) ^ 2)) * (2 * Real.sqrt N) with hE
  -- the main term is the lattice sum with `ζ` replaced by `D`
  have hmain : latticeSum (fun x => φ (x / T) * (D x * linMoll N (critPt (α * x + β)))) γ =
      ∑' m : ℕ, mollCoeff N X (m + 1) * (m + 1 : ℂ) ^ (-critPt β) *
        bumpSum φ T (γ - α * Real.log (m + 1) / (2 * Real.pi)) := by
    have hsupp' := support_cutoff_subset hsupp hT
      (fun x => D x * linMoll N (critPt (α * x + β)))
    rw [latticeSum_eq_sum hsupp']
    have hre : ∀ x : ℝ, 0 ≤ (critPt (α * x + β)).re := fun x => by simp
    have hexp : ∀ ℓ ∈ Finset.Icc ⌈T⌉ ⌊2 * T⌋,
        φ ((ℓ : ℝ) / T) * (D ℓ * linMoll N (critPt (α * ℓ + β))) * unitExp (ℓ * γ) =
        ∑' m : ℕ, φ ((ℓ : ℝ) / T) * (mollCoeff N X (m + 1) * (m + 1 : ℂ) ^ (-critPt β)) *
          unitExp (ℓ * (γ - α * Real.log (m + 1) / (2 * Real.pi))) := by
      intro ℓ _
      rw [hD, smoothSum_mul_linMoll N hX (hre ℓ), ← tsum_mul_left, ← tsum_mul_right]
      refine tsum_congr fun m => ?_
      have hph := natSucc_cpow_neg_critPt_mul_unitExp m α β γ ℓ
      linear_combination φ ((ℓ : ℝ) / T) * mollCoeff N X (m + 1) * hph
    rw [Finset.sum_congr rfl hexp, ← Summable.tsum_finsetSum]
    · refine tsum_congr fun m => ?_
      unfold bumpSum
      rw [latticeSum_eq_sum (support_cutoff_subset hsupp hT (fun _ => (1 : ℂ))
        |>.trans' (by intro x hx; simpa using hx)), Finset.mul_sum]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      ring
    · intro ℓ _
      have hs := (summable_mollSeries N hX (s := critPt β) (by simp)).mul_left (φ ((ℓ : ℝ) / T))
      refine (summable_norm_iff.mpr hs).of_norm_bounded fun m => ?_
      rw [norm_mul _ (unitExp _), norm_unitExp, mul_one]
  -- the error from replacing `ζ` by the smoothed series
  have hsuppζ := support_cutoff_subset hsupp hT (fun x => apMollZeta N α β x)
  have hsuppD := support_cutoff_subset hsupp hT (fun x => D x * linMoll N (critPt (α * x + β)))
  have hdiff : firstMoment φ α β γ N T -
      latticeSum (fun x => φ (x / T) * (D x * linMoll N (critPt (α * x + β)))) γ =
      latticeSum (fun x => φ (x / T) * ((riemannZeta (critPt (α * x + β)) - D x) *
        linMoll N (critPt (α * x + β)))) γ := by
    unfold firstMoment latticeSum
    rw [← (summable_lattice hsuppζ γ).tsum_sub (summable_lattice hsuppD γ)]
    refine tsum_congr fun ℓ => ?_
    unfold apMollZeta
    ring
  rw [← hmain, hdiff]
  have hbd := norm_latticeSum_le_of_bound (A := T) (B := 2 * T) (M := Φ₀ * E) (by linarith)
    (support_cutoff_subset hsupp hT (fun x => (riemannZeta (critPt (α * x + β)) - D x) *
      linMoll N (critPt (α * x + β)))) (fun x => ?_) γ
  · refine hbd.trans (le_of_eq ?_)
    ring
  by_cases hx : φ (x / T) = 0
  · simp only [hx, zero_mul, norm_zero]; positivity
  obtain ⟨h21, h22⟩ := hsupp hx
  rw [le_div_iff₀ hT] at h21
  rw [div_le_iff₀ hT] at h22
  set t : ℝ := α * x + β with ht
  have hlow : α * T / 2 ≤ t := by
    have := neg_abs_le β
    nlinarith
  have hhigh : t ≤ 3 * α * T := by
    have := le_abs_self β
    nlinarith
  have ht1 : 1 ≤ |t| := by rw [abs_of_pos (by linarith)]; linarith
  have hz := hζ X hX t ht1
  rw [norm_mul, norm_mul]
  have hM := norm_linMoll_critPt_le N t
  have herr : ‖riemannZeta (critPt t) - D x‖ ≤
      C * (1 + 3 * α * T) / X + X ^ (1 / 2 : ℝ) * Real.exp (1 / 4 - (α * T / 2) ^ 2) := by
    refine hz.trans (add_le_add ?_ ?_)
    · rw [abs_of_pos (by linarith)]
      gcongr
    · gcongr
  calc ‖φ (x / T)‖ * (‖riemannZeta (critPt t) - D x‖ * ‖linMoll N (critPt t)‖)
      ≤ Φ₀ * ((C * (1 + 3 * α * T) / X + X ^ (1 / 2 : ℝ) *
          Real.exp (1 / 4 - (α * T / 2) ^ 2)) * (2 * Real.sqrt N)) := by
        gcongr
        exact hΦ₀ _
    _ = Φ₀ * E := rfl

end

end RHTower.VerticalAP
