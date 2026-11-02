import GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations.ThePrimeWindowCountsTheProjectivePoints

/-!
# The energy of a periodic twist

For a horizon window twisted by an `M`-periodic weight `χ`, `x_n = χ(n) h(log(n/N))/√n`, the block
energy `E_N = ∫ |φ̂(wτ)|² |D_x(τ)|²/N dτ` is computed by the autocorrelation of the twist:

`E_N = (2π/c) Σ_n x_n² / χ(n)² · Σ_{|δ| ≤ ⌈c⌉} C_χ(δ) G(δ/a_n) + O(c/N)`,   `a_n = cn/N`,

where `G` is the atom autocorrelation and `C_χ(δ)` is the mean over a period of
`n ↦ χ(n) χ(n + δ)` (`periodicEnergy_le`). No Poisson summation on shifted lattices is needed:

* each row `Σ_m x_m G(N log(m/n)/c)` is linearized entrywise to
  `h_n/√n · Σ_{|δ| ≤ ⌈c⌉} χ(n + δ) G(δ/a_n)` (`abs_twistRow_sub_le`, `sum_offset_eq`);
* for each offset `δ` the sequence `n ↦ χ(n)χ(n + δ)` is `M`-periodic and the profile
  `x ↦ h(log x)²/x · G(δ/(cx))` is Lipschitz uniformly in `|δ| ≤ ⌈c⌉`, so the sum over `n`
  equidistributes to the mean `C_χ(δ)` (`abs_sum_periodic_sub_le`), with error `O(1/N)` per offset
  and `O(c/N)` in total.
-/

noncomputable section

open Finset Filter Topology MeasureTheory Zeta23
open scoped ComplexConjugate

namespace GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations

open SpacingScaleHarmonicAnalysis ArithmeticElectrostatics ArithmeticCastelnuovoSeveri
  RenormalizedArithmeticPotentialTheory.CompletedShell

variable {φ h : ℝ → ℝ} {A : ℝ}

/-! ### Periodic equidistribution -/

/-- The mean of a sequence over `[0, M)`. -/
def periodMean (ψ : ℕ → ℝ) (M : ℕ) : ℝ := (M : ℝ)⁻¹ * ∑ r ∈ range M, ψ r

/-- **Periodic sequences equidistribute against Lipschitz profiles**: for `M`-periodic `|ψ| ≤ B`,
`|Σ_{n ≤ N} ψ(n) f(n/N) − ψ̄ Σ_{n ≤ N} f(n/N)| ≤ 2MB(|f(1)| + L)`. -/
theorem abs_sum_periodic_sub_le {ψ : ℕ → ℝ} {M : ℕ} (hM : 0 < M) (hper : ∀ n, ψ (n + M) = ψ n)
    {B : ℝ} (hB : ∀ n, |ψ n| ≤ B) {f : ℝ → ℝ} {L : ℝ}
    (hL : ∀ x y, |f x - f y| ≤ L * |x - y|) {N : ℕ} (hN : 1 ≤ N) :
    |∑ n ∈ Icc 1 N, ψ n * f (n / N) - periodMean ψ M * ∑ n ∈ Icc 1 N, f (n / N)| ≤
      2 * M * B * (|f 1| + L) := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have hL0 : 0 ≤ L := by
    have := hL 1 0
    norm_num at this
    linarith [abs_nonneg (f 1 - f 0)]
  obtain ⟨C, hC⟩ : ∃ C, C = periodMean ψ M := ⟨_, rfl⟩
  rw [← hC]
  have hCB : |C| ≤ B := by
    rw [hC, periodMean, abs_mul, abs_inv, abs_of_pos hM0, inv_mul_le_iff₀ hM0]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun r _ => hB r).trans (le_of_eq ?_)
    rw [Finset.sum_const, card_range, nsmul_eq_mul]
  set ψ' : ℕ → ℝ := fun i => ψ (i + 1) - C with hψ'
  have hψt : MeanZeroTwist ψ' M := by
    refine ⟨hM, fun i => ?_, ?_⟩
    · simp only [hψ', show i + M + 1 = i + 1 + M by ring, hper]
    · simp only [hψ']
      rw [Finset.sum_sub_distrib, Finset.sum_const, card_range, nsmul_eq_mul]
      have hs := sum_range_shift hper 1
      simp only [add_comm 1] at hs
      rw [hs, hC, periodMean, ← mul_assoc, mul_inv_cancel₀ hM0.ne', one_mul, sub_self]
  have hψB : ∑ j ∈ range M, |ψ' j| ≤ M * (2 * B) := by
    calc ∑ j ∈ range M, |ψ' j| ≤ ∑ j ∈ range M, (2 * B) := sum_le_sum fun j _ => by
          simp only [hψ']
          exact (abs_sub _ _).trans (by linarith [hB (j + 1)])
      _ = M * (2 * B) := by rw [sum_const, card_range, nsmul_eq_mul]
  have hpart : ∀ k ≤ N - 1, |∑ i ∈ range (k + 1), ψ' i| ≤ M * (2 * B) := fun k _ =>
    (abs_sum_range_le hψt (k + 1)).trans hψB
  have hsbp := norm_sum_mul_real_le (fun i => ((f ((i + 1 : ℕ) / N) : ℝ) : ℂ)) ψ' (N - 1) hpart
  have hre : ∑ n ∈ Icc 1 N, ψ n * f (n / N) - C * ∑ n ∈ Icc 1 N, f (n / N) =
      ∑ i ∈ range (N - 1 + 1), f ((i + 1 : ℕ) / N) * ψ' i := by
    rw [mul_sum, ← sum_sub_distrib, show N - 1 + 1 = N by omega,
      show Icc 1 N = Finset.Ico 1 (N + 1) by ext; simp, Finset.sum_Ico_eq_sum_range,
      show N + 1 - 1 = N by omega]
    refine sum_congr rfl fun i _ => ?_
    simp only [hψ', add_comm 1 i]
    ring
  rw [hre]
  have hn : ‖∑ i ∈ range (N - 1 + 1), ((f ((i + 1 : ℕ) / N) : ℝ) : ℂ) * ((ψ' i : ℝ) : ℂ)‖ =
      |∑ i ∈ range (N - 1 + 1), f ((i + 1 : ℕ) / N) * ψ' i| := by
    rw [show (∑ i ∈ range (N - 1 + 1), ((f ((i + 1 : ℕ) / N) : ℝ) : ℂ) * ((ψ' i : ℝ) : ℂ)) =
      ((∑ i ∈ range (N - 1 + 1), f ((i + 1 : ℕ) / N) * ψ' i : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs]
  rw [← hn]
  refine hsbp.trans ?_
  have hlast : ‖((f ((N - 1 + 1 : ℕ) / N) : ℝ) : ℂ)‖ = |f 1| := by
    rw [Complex.norm_real, Real.norm_eq_abs, show N - 1 + 1 = N by omega, div_self hN0.ne']
  have hvar : ∑ i ∈ range (N - 1), ‖((f ((i + 1 + 1 : ℕ) / N) : ℝ) : ℂ) -
      ((f ((i + 1 : ℕ) / N) : ℝ) : ℂ)‖ ≤ L := by
    have hstep : ∀ i ∈ range (N - 1), ‖((f ((i + 1 + 1 : ℕ) / N) : ℝ) : ℂ) -
        ((f ((i + 1 : ℕ) / N) : ℝ) : ℂ)‖ ≤ L / N := fun i _ => by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      refine (hL _ _).trans (le_of_eq ?_)
      rw [← sub_div]
      push_cast
      rw [show (i : ℝ) + 1 + 1 - (i + 1) = 1 by ring, abs_of_pos (by positivity)]
      ring
    refine (sum_le_sum hstep).trans ?_
    rw [sum_const, card_range, nsmul_eq_mul, mul_div_assoc', div_le_iff₀ hN0]
    have : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
    nlinarith
  rw [hlast]
  calc M * (2 * B) * (|f 1| + ∑ i ∈ range (N - 1), ‖((f ((i + 1 + 1 : ℕ) / N) : ℝ) : ℂ) -
        ((f ((i + 1 : ℕ) / N) : ℝ) : ℂ)‖) ≤ M * (2 * B) * (|f 1| + L) := by gcongr
    _ = 2 * M * B * (|f 1| + L) := by ring

/-! ### Twisted rows -/

/-- **A twisted row**: `Σ_m χ_m k_m G(N log(m/n)/c) = k_n Σ_{m ≤ 2N} χ_m G((m − n)/a_n)` up to
`O(c² N^{−3/2})`, `a_n = cn/N`, for a bounded twist `|χ| ≤ M_χ`. -/
theorem abs_twistRow_sub_le {k G : ℝ → ℝ} {Bk Lk BG LG : ℝ} (hk : ∀ y, |k y| ≤ Bk)
    (hkL : ∀ u v, |k u - k v| ≤ Lk * |u - v|) (hG : ∀ t, |G t| ≤ BG)
    (hGL : ∀ s t, |G s - G t| ≤ LG * |s - t|) (hG1 : ∀ t, 1 ≤ |t| → G t = 0)
    (hk0 : ∀ y, 0 < y → k y = 0) (hLk : 0 ≤ Lk) (hBk : 0 ≤ Bk) (hLG : 0 ≤ LG) (hBG : 0 ≤ BG)
    {χ : ℤ → ℝ} {Mχ : ℝ} (hχ : ∀ z, |χ z| ≤ Mχ) {c : ℝ} (hc : 1 ≤ c) {N : ℕ}
    (hcN : 4 * c ≤ N) {n : ℕ} (hn : 1 ≤ n) (hnN : n ≤ N) :
    |∑ m ∈ Icc 1 N, χ m * (k (Real.log m - Real.log N) / Real.sqrt N) *
        G (N * (Real.log m - Real.log n) / c) -
      k (Real.log n - Real.log N) / Real.sqrt N *
        ∑ m ∈ Icc 1 (2 * N), χ m * G (((m : ℝ) - n) * (c * n / N)⁻¹)| ≤
      Mχ * (5 * (Lk * BG + 8 * Bk * LG) * c ^ 2 / (N * Real.sqrt N)) := by
  have hc0 : 0 < c := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
  have hMχ : 0 ≤ Mχ := (abs_nonneg _).trans (hχ 0)
  have ha0 : 0 < c * n / N := by positivity
  have hac : c * n / N ≤ c := by
    rw [div_le_iff₀ hN0]; exact mul_le_mul_of_nonneg_left hnN' hc0.le
  have hrow : ∑ m ∈ Icc 1 N, χ m * (k (Real.log m - Real.log N) / Real.sqrt N) *
      G (N * (Real.log m - Real.log n) / c) = ∑ m ∈ Icc 1 (2 * N),
        χ m * (k (Real.log m - Real.log N) / Real.sqrt N) *
          G (N * (Real.log m - Real.log n) / c) := by
    refine Finset.sum_subset (Finset.Icc_subset_Icc le_rfl (by omega)) fun m hm hmN => ?_
    have hm1 : N < m := by
      rw [Finset.mem_Icc] at hm hmN; omega
    have hlog : 0 < Real.log m - Real.log N := by
      rw [sub_pos]; exact Real.log_lt_log hN0 (by exact_mod_cast hm1)
    rw [hk0 _ hlog, zero_div, mul_zero, zero_mul]
  rw [hrow, mul_sum, ← sum_sub_distrib]
  set X := (Lk * BG + 8 * Bk * LG) * c / (N * Real.sqrt N) with hX
  have hX0 : 0 ≤ X := by positivity
  have hterm : ∀ m ∈ Icc 1 (2 * N), |χ m * (k (Real.log m - Real.log N) / Real.sqrt N) *
      G (N * (Real.log m - Real.log n) / c) - k (Real.log n - Real.log N) / Real.sqrt N *
        (χ m * G (((m : ℝ) - n) * (c * n / N)⁻¹))| ≤
      Mχ * (if |(m : ℝ) - n| ≤ 2 * (c * n / N) then X else 0) := fun m hm => by
    have hE := abs_entry_le hk hkL hG hGL hG1 hLk hBk hLG hBG hc0 hcN hn (Finset.mem_Icc.mp hm).1
    rw [show χ m * (k (Real.log m - Real.log N) / Real.sqrt N) *
        G (N * (Real.log m - Real.log n) / c) - k (Real.log n - Real.log N) / Real.sqrt N *
          (χ m * G (((m : ℝ) - n) * (c * n / N)⁻¹)) =
        χ m * (k (Real.log m - Real.log N) / Real.sqrt N * G (N * (Real.log m - Real.log n) / c) -
          k (Real.log n - Real.log N) / Real.sqrt N * G (((m : ℝ) - n) * (c * n / N)⁻¹)) by ring,
      abs_mul]
    exact mul_le_mul (hχ m) hE (abs_nonneg _) hMχ
  refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hterm).trans ?_)
  rw [← Finset.mul_sum, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
    nsmul_eq_mul]
  have hcard := card_filter_near_le n N ha0.le
  refine mul_le_mul_of_nonneg_left ?_ hMχ
  calc (((Icc 1 (2 * N)).filter fun m : ℕ => |(m : ℝ) - n| ≤ 2 * (c * n / N)).card : ℝ) * X
      ≤ (4 * (c * n / N) + 1) * X := mul_le_mul_of_nonneg_right hcard hX0
    _ ≤ 5 * c * X := mul_le_mul_of_nonneg_right (by linarith) hX0
    _ = 5 * (Lk * BG + 8 * Bk * LG) * c ^ 2 / (N * Real.sqrt N) := by rw [hX]; ring

/-- The lattice sum of a row in the offset `δ = m − n`. -/
theorem sum_offset_eq {G : ℝ → ℝ} (hG1 : ∀ t, 1 ≤ |t| → G t = 0) (χ : ℤ → ℝ) {a : ℝ}
    (ha : 0 < a) {n N D : ℕ} (hn4 : 4 * a ≤ n) (haD : a ≤ D) (hnD : n + D ≤ 2 * N) :
    ∑ m ∈ Icc 1 (2 * N), χ m * G (((m : ℝ) - n) * a⁻¹) =
      ∑ δ ∈ Finset.Icc (-(D : ℤ)) D, χ (n + δ) * G (δ * a⁻¹) := by
  have hlt : ∀ t : ℝ, G (t * a⁻¹) ≠ 0 → |t| < a := fun t ht => by
    by_contra hge
    push Not at hge
    exact ht (hG1 _ (by rw [abs_mul, abs_inv, abs_of_pos ha, le_mul_inv_iff₀ ha, one_mul]; exact hge))
  refine Finset.sum_bij_ne_zero (fun m _ _ => (m : ℤ) - n) ?_ ?_ ?_ ?_
  · intro m hm hne
    have h1 := abs_lt.mp ((hlt _ (right_ne_zero_of_mul hne)).trans_le haD)
    rw [Finset.mem_Icc]
    constructor
    · have : ((-(D : ℤ) : ℤ) : ℝ) < (((m : ℤ) - n : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this.le
    · have : (((m : ℤ) - n : ℤ) : ℝ) < ((D : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this.le
  · intro m₁ _ _ m₂ _ _ h
    omega
  · intro δ hδ hne
    have h1 := abs_lt.mp (hlt _ (right_ne_zero_of_mul hne))
    have hpos : (0 : ℤ) < n + δ := by
      have : (0 : ℝ) < ((n + δ : ℤ) : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hδD := (Finset.mem_Icc.mp hδ).2
    refine ⟨(n + δ).toNat, ?_, ?_, ?_⟩
    · rw [Finset.mem_Icc]; omega
    · have e : (((n + δ).toNat : ℕ) : ℤ) = n + δ := Int.toNat_of_nonneg hpos.le
      have e' : (((n + δ).toNat : ℕ) : ℝ) - n = δ := by
        have : ((((n + δ).toNat : ℕ) : ℤ) : ℝ) = ((n + δ : ℤ) : ℝ) := by rw [e]
        push_cast at this
        linarith
      rw [e, e']
      exact hne
    · omega
  · intro m _ _
    congr 2
    · ring
    · push_cast; ring

/-! ### Periodic twists on `ℤ` -/

/-- The extension of an `M`-periodic twist to `ℤ`. -/
def periodicExt (χ : ℕ → ℝ) (M : ℕ) (z : ℤ) : ℝ := χ (z % M).toNat

/-- The autocorrelation `C_χ(δ)`: the mean over a period of `n ↦ χ(n) χ(n + δ)`. -/
def autoCorr (χ : ℕ → ℝ) (M : ℕ) (δ : ℤ) : ℝ :=
  periodMean (fun n => χ n * periodicExt χ M (n + δ)) M

theorem periodic_add_mul {χ : ℕ → ℝ} {M : ℕ} (hper : ∀ n, χ (n + M) = χ n) (r k : ℕ) :
    χ (r + M * k) = χ r := by
  induction k with
  | zero => simp
  | succ k ih => rw [mul_add, mul_one, ← add_assoc, hper, ih]

theorem periodic_mod {χ : ℕ → ℝ} {M : ℕ} (hper : ∀ n, χ (n + M) = χ n) (n : ℕ) :
    χ (n % M) = χ n := by
  conv_rhs => rw [← Nat.mod_add_div n M]
  rw [periodic_add_mul hper]

theorem periodicExt_natCast {χ : ℕ → ℝ} {M : ℕ} (hper : ∀ n, χ (n + M) = χ n) (n : ℕ) :
    periodicExt χ M n = χ n := by
  rw [periodicExt, show ((n : ℤ) % M) = ((n % M : ℕ) : ℤ) by push_cast; rfl, Int.toNat_natCast,
    periodic_mod hper]

theorem periodicExt_add_period (χ : ℕ → ℝ) (M : ℕ) (z : ℤ) :
    periodicExt χ M (z + M) = periodicExt χ M z := by
  simp [periodicExt, Int.add_emod_self]

theorem abs_periodic_le {χ : ℕ → ℝ} {M : ℕ} (hM : 0 < M) (hper : ∀ n, χ (n + M) = χ n) (n : ℕ) :
    |χ n| ≤ ∑ j ∈ range M, |χ j| := by
  rw [← periodic_mod hper]
  exact Finset.single_le_sum (f := fun j => |χ j|) (fun _ _ => abs_nonneg _)
    (Finset.mem_range.mpr (Nat.mod_lt _ hM))

theorem abs_periodicExt_le {χ : ℕ → ℝ} {M : ℕ} (hM : 0 < M) (hper : ∀ n, χ (n + M) = χ n)
    (z : ℤ) : |periodicExt χ M z| ≤ ∑ j ∈ range M, |χ j| :=
  abs_periodic_le hM hper _

/-! ### The offset profiles -/

/-- `u(x) = h(log x)²/x`, so that `h(log(n/N))²/n = N⁻¹ u(n/N)`. -/
def invWindow (h : ℝ → ℝ) (x : ℝ) : ℝ := sqWindow h x * x⁻¹

theorem exists_invWindow_bounds (hh : ContDiff ℝ 2 h) (hA : 0 ≤ A)
    (hsupp : ∀ y, y ∉ Set.Icc (-A) 0 → h y = 0) :
    ∃ Bu Lu : ℝ, 0 ≤ Bu ∧ 0 ≤ Lu ∧ (∀ x, |invWindow h x| ≤ Bu) ∧
      (∀ x y, |invWindow h x - invWindow h y| ≤ Lu * |x - y|) ∧
      (∀ x, x < Real.exp (-A) → invWindow h x = 0) := by
  obtain ⟨Bh, -, hB, -⟩ := exists_bound_lipschitz hh hsupp
  obtain ⟨Lsq, hLsq0, hLsq⟩ := exists_lipschitz_sqWindow hh hA hsupp
  have hBh0 : 0 ≤ Bh := (abs_nonneg _).trans (hB 0)
  have hsqB : ∀ x, |sqWindow h x| ≤ Bh ^ 2 := fun x => by
    unfold sqWindow
    split_ifs
    · rw [abs_pow]; exact pow_le_pow_left₀ (abs_nonneg _) (hB _) 2
    · simp; positivity
  have he : 0 < Real.exp (-A) := Real.exp_pos _
  have hinvB : ∀ a, 1 * Real.exp (-A) ≤ a → |a⁻¹| ≤ Real.exp A := fun a ha => by
    have ha0 : 0 < a := by linarith
    rw [abs_of_pos (inv_pos.mpr ha0), inv_le_comm₀ ha0 (Real.exp_pos _), ← Real.exp_neg]
    linarith
  have hinvL : ∀ a b, 1 * Real.exp (-A) ≤ a → 1 * Real.exp (-A) ≤ b →
      |a⁻¹ - b⁻¹| ≤ Real.exp A ^ 2 * |a - b| := fun a b ha hb => by
    have ha0 : 0 < a := by linarith
    have hb0 : 0 < b := by linarith
    rw [inv_sub_inv ha0.ne' hb0.ne', abs_div, abs_mul, abs_of_pos ha0, abs_of_pos hb0,
      abs_sub_comm, div_le_iff₀ (by positivity)]
    have h1 : 1 ≤ Real.exp A * a := by
      rw [one_mul] at ha
      have := mul_le_mul_of_nonneg_left ha (Real.exp_pos A).le
      rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
    have h2 : 1 ≤ Real.exp A * b := by
      rw [one_mul] at hb
      have := mul_le_mul_of_nonneg_left hb (Real.exp_pos A).le
      rwa [← Real.exp_add, add_neg_cancel, Real.exp_zero] at this
    have h3 : 1 ≤ (Real.exp A * a) * (Real.exp A * b) := by nlinarith
    nlinarith [abs_nonneg (a - b)]
  have hlip := fun x y => abs_mul_window_sub_le (u := sqWindow h) (G := fun a => a⁻¹)
    (x₀ := Real.exp (-A)) one_pos hLsq hsqB (fun x hx => sqWindow_eq_zero_of_lt hsupp hx) hinvB
    hinvL (Real.exp_pos A).le x y
  refine ⟨Bh ^ 2 * Real.exp A, Lsq * Real.exp A + Bh ^ 2 * 1 * Real.exp A ^ 2, by positivity,
    by positivity, fun x => ?_, fun x y => ?_, fun x hx => ?_⟩
  · unfold invWindow
    rcases lt_or_ge x (Real.exp (-A)) with hx | hx
    · rw [sqWindow_eq_zero_of_lt hsupp hx, zero_mul, abs_zero]; positivity
    · rw [abs_mul]
      exact mul_le_mul (hsqB x) (hinvB x (by linarith)) (abs_nonneg _) (by positivity)
  · have := hlip x y
    simp only [one_mul] at this
    exact this
  · rw [invWindow, sqWindow_eq_zero_of_lt hsupp hx, zero_mul]

/-- The offset profile `f_δ(x) = u(x) G(δ/(cx))` is Lipschitz uniformly in `|δ| ≤ 2c`. -/
theorem abs_offsetProfile_sub_le {G : ℝ → ℝ} {BG LG : ℝ} (hG : ∀ t, |G t| ≤ BG)
    (hGL : ∀ s t, |G s - G t| ≤ LG * |s - t|) (hBG : 0 ≤ BG) {Bu Lu : ℝ}
    (hBu : ∀ x, |invWindow h x| ≤ Bu) (hLu : ∀ x y, |invWindow h x - invWindow h y| ≤ Lu * |x - y|)
    (hu0 : ∀ x, x < Real.exp (-A) → invWindow h x = 0) {c : ℝ} (hc : 0 < c) {δ : ℝ}
    (hδ : |δ| ≤ 2 * c) (x y : ℝ) :
    |invWindow h x * G (δ * (c * x)⁻¹) - invWindow h y * G (δ * (c * y)⁻¹)| ≤
      (Lu * BG + Bu * (2 * LG * Real.exp A ^ 2)) * |x - y| := by
  have hLG0 : 0 ≤ LG := by
    have := hGL 1 0; norm_num at this; linarith [abs_nonneg (G 1 - G 0)]
  have hBu0 : 0 ≤ Bu := (abs_nonneg _).trans (hBu 0)
  have hLG' : ∀ a b, c * Real.exp (-A) ≤ a → c * Real.exp (-A) ≤ b →
      |G (δ * a⁻¹) - G (δ * b⁻¹)| ≤ LG * (2 * c * (c * Real.exp (-A))⁻¹ ^ 2) * |a - b| :=
    fun a b ha hb => by
      have hce : 0 < c * Real.exp (-A) := by positivity
      have ha0 : 0 < a := by linarith
      have hb0 : 0 < b := by linarith
      refine (hGL _ _).trans ?_
      rw [mul_assoc]
      refine mul_le_mul_of_nonneg_left ?_ hLG0
      rw [← mul_sub, abs_mul, inv_sub_inv ha0.ne' hb0.ne', abs_div, abs_mul, abs_of_pos ha0,
        abs_of_pos hb0, abs_sub_comm]
      have hab : (c * Real.exp (-A)) ^ 2 ≤ a * b := by nlinarith
      have h1 : |a - b| / (a * b) ≤ (c * Real.exp (-A))⁻¹ ^ 2 * |a - b| := by
        rw [div_le_iff₀ (by positivity), inv_pow, mul_assoc, mul_comm (|a - b|) (a * b),
          ← mul_assoc, ← div_eq_inv_mul, le_div_iff₀ (by positivity) |>.symm.not.not]
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < (c * Real.exp (-A)) ^ 2)]
        nlinarith [abs_nonneg (a - b)]
      calc |δ| * (|a - b| / (a * b)) ≤ (2 * c) * ((c * Real.exp (-A))⁻¹ ^ 2 * |a - b|) :=
            mul_le_mul hδ h1 (by positivity) (by positivity)
        _ = 2 * c * (c * Real.exp (-A))⁻¹ ^ 2 * |a - b| := by ring
  have hmain := abs_mul_window_sub_le (u := invWindow h) (G := fun a => G (δ * a⁻¹))
    (x₀ := Real.exp (-A)) hc hLu hBu hu0 (fun a _ => hG _) hLG' hBG x y
  refine hmain.trans (mul_le_mul_of_nonneg_right ?_ (abs_nonneg _))
  have e : Bu * c * (LG * (2 * c * (c * Real.exp (-A))⁻¹ ^ 2)) =
      Bu * (2 * LG * Real.exp A ^ 2) := by
    rw [mul_inv, inv_pow, mul_pow, ← Real.exp_neg, neg_neg]
    field_simp
  rw [e]

end GaloisForLFunctions.ArithmeticHodgeTheoryOfDegenerations
