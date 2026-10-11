import Mathlib

/-!
# Kronecker's theorem for linear flows on tori

**Theorem** (`exists_flow_near_of_relations`). Let `α, x : d → ℝ` be such that every integer
relation `Σ k_i α_i = 0` makes `Σ k_i x_i` an integer. Then for every `ε > 0` and every `T` there is
`t ≥ T` with `t α_i − x_i` within `ε` of an integer for every `i`. Without relations this is
`exists_flow_near_of_nonresonant`.

**Proof.** The kernel `Φ(y) = Π_i cos(π y_i)^{2M}` is a nonnegative trigonometric polynomial,
`Φ(y) = Σ_J C_J e^{2πi Σ_i y_i (J_i − M)}` with `C_J = Π_i C(2M, J_i)/4^M`
(`prod_cos_pow_eq_sum`). Its mean coefficient is `(C(2M, M)/4^M)^d ≥ (2M+1)^{−d}`, while off the
`ε`-box it is at most `cos(πε)^{2M}`. Along the discrete times `t_n = T + nh` every nonzero
frequency `ω_J = Σ_i α_i (J_i − M)` gives a geometric sum with ratio `e^{2πihω_J} ≠ 1` (`h` small).
A resonant frequency `ω_J = 0` contributes `C_J e^{−2πi Σ x_i (J_i − M)} = C_J` by the relation
hypothesis. So the time average of `Φ(t_n α − x)` tends to the resonant mass, which is at least the
mean coefficient. If the flow avoided the box
from time `T` on, the average would stay below `cos(πε)^{2M}`, which is smaller for large `M`.

No Haar measure and no Stone–Weierstrass argument is used.
-/

open Complex Finset Filter Topology

namespace GaloisForLFunctions.HTGeometry.KroneckerFlow

noncomputable section

variable {d : Type*} [Fintype d] [DecidableEq d]

/-- Frequencies with no integer relation. -/
def FlowNonresonant (α : d → ℝ) : Prop := ∀ k : d → ℤ, k ≠ 0 → ∑ i, (k i : ℝ) * α i ≠ 0

/-- The binomial kernel coefficients `C(2M, j)/4^M`. -/
def cosKernelCoeff (M : ℕ) (j : Fin (2 * M + 1)) : ℝ := (Nat.choose (2 * M) j : ℝ) / 4 ^ M

theorem cosKernelCoeff_nonneg (M : ℕ) (j : Fin (2 * M + 1)) : 0 ≤ cosKernelCoeff M j := by
  unfold cosKernelCoeff; positivity

omit [Fintype d] [DecidableEq d] in
/-- `cos(πu)^{2M} = Σ_j C(2M, j)/4^M · e^{2πiu(j − M)}`. -/
theorem cos_pow_eq_sum (M : ℕ) (u : ℝ) :
    ((Real.cos (Real.pi * u) ^ (2 * M) : ℝ) : ℂ) =
      ∑ j : Fin (2 * M + 1), (cosKernelCoeff M j : ℂ) *
        Complex.exp (2 * Real.pi * I * u * ((j : ℂ) - M)) := by
  simp only [Complex.ofReal_pow, Complex.ofReal_cos, Complex.ofReal_mul]
  rw [Complex.cos, div_pow, add_pow, Finset.sum_div,
    ← Fin.sum_univ_eq_sum_range (fun m => Complex.exp ((Real.pi * u : ℂ) * I) ^ m *
      Complex.exp (-(Real.pi * u : ℂ) * I) ^ (2 * M - m) * ((2 * M).choose m : ℂ) / 2 ^ (2 * M))]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hj : (j : ℕ) ≤ 2 * M := Nat.lt_succ_iff.mp j.2
  rw [← Complex.exp_nat_mul, ← Complex.exp_nat_mul, ← Complex.exp_add]
  unfold cosKernelCoeff
  have h4 : (2 : ℂ) ^ (2 * M) = 4 ^ M := by rw [pow_mul]; norm_num
  rw [h4]
  push_cast [Nat.cast_sub hj]
  rw [show ((j : ℂ) * ((Real.pi * u : ℂ) * I) + ((2 * M : ℂ) - j) * (-(Real.pi * u : ℂ) * I)) =
    2 * Real.pi * I * u * ((j : ℂ) - M) by ring]
  ring

/-- The product kernel `Π_i cos(π y_i)^{2M}` as a finite exponential sum. -/
theorem prod_cos_pow_eq_sum (M : ℕ) (y : d → ℝ) :
    ((∏ i, Real.cos (Real.pi * y i) ^ (2 * M) : ℝ) : ℂ) =
      ∑ J : d → Fin (2 * M + 1), ((∏ i, cosKernelCoeff M (J i) : ℝ) : ℂ) *
        Complex.exp (2 * Real.pi * I * ∑ i, (y i : ℂ) * ((J i : ℂ) - M)) := by
  rw [Complex.ofReal_prod]
  simp_rw [cos_pow_eq_sum M]
  rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  refine Finset.sum_congr rfl fun J _ => ?_
  rw [Finset.prod_mul_distrib, Complex.ofReal_prod, ← Complex.exp_sum, Finset.mul_sum]
  congr 2
  exact Finset.sum_congr rfl fun i _ => by ring

/-- The central coefficient dominates: `C(2M, M) ≥ 4^M/(2M+1)`. -/
theorem cosKernelCoeff_middle_ge (M : ℕ) :
    (1 : ℝ) / (2 * M + 1) ≤ cosKernelCoeff M ⟨M, by omega⟩ := by
  unfold cosKernelCoeff
  have hsum := Nat.sum_range_choose (2 * M)
  have hle : ∀ j ∈ Finset.range (2 * M + 1), (2 * M).choose j ≤ (2 * M).choose M := by
    intro j _
    have := Nat.choose_le_middle j (2 * M)
    rwa [show 2 * M / 2 = M by omega] at this
  have hbound : 2 ^ (2 * M) ≤ (2 * M + 1) * (2 * M).choose M := by
    rw [← hsum]
    calc ∑ j ∈ Finset.range (2 * M + 1), (2 * M).choose j
        ≤ ∑ _j ∈ Finset.range (2 * M + 1), (2 * M).choose M := Finset.sum_le_sum hle
      _ = (2 * M + 1) * (2 * M).choose M := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hbound' : (4 : ℝ) ^ M ≤ (2 * M + 1) * ((2 * M).choose M : ℝ) := by
    have : ((2 ^ (2 * M) : ℕ) : ℝ) ≤ (((2 * M + 1) * (2 * M).choose M : ℕ) : ℝ) := by
      exact_mod_cast hbound
    push_cast at this
    rwa [pow_mul, show (2 : ℝ) ^ 2 = 4 by norm_num] at this
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  simpa [mul_comm] using hbound'

/-- `|cos(πy)| ≤ cos(πε)` when `y` is at distance at least `ε` from every integer. -/
theorem abs_cos_pi_le_of_far {y ε : ℝ} (hε : 0 ≤ ε)
    (hfar : ∀ z : ℤ, ε ≤ |y - z|) : |Real.cos (Real.pi * y)| ≤ Real.cos (Real.pi * ε) := by
  set r : ℝ := y - round y with hr
  have hr2 : |r| ≤ 1 / 2 := abs_sub_round y
  have hrε : ε ≤ |r| := hfar (round y)
  have hcos : |Real.cos (Real.pi * y)| = Real.cos (Real.pi * |r|) := by
    have hy : Real.pi * y = Real.pi * r + (round y : ℤ) * Real.pi := by rw [hr]; ring
    rw [hy, Real.cos_add_int_mul_pi, abs_mul, abs_zpow, abs_neg, abs_one, one_zpow, one_mul]
    rw [show Real.pi * |r| = |Real.pi * r| by rw [abs_mul, abs_of_pos Real.pi_pos],
      Real.cos_abs]
    exact abs_of_nonneg (Real.cos_nonneg_of_mem_Icc ⟨by
      have := abs_le.mp (show |Real.pi * r| ≤ Real.pi / 2 by
        rw [abs_mul, abs_of_pos Real.pi_pos]; nlinarith [Real.pi_pos])
      linarith, by
      have := abs_le.mp (show |Real.pi * r| ≤ Real.pi / 2 by
        rw [abs_mul, abs_of_pos Real.pi_pos]; nlinarith [Real.pi_pos])
      linarith⟩)
  rw [hcos]
  apply Real.cos_le_cos_of_nonneg_of_le_pi (by positivity)
  · nlinarith [Real.pi_pos]
  · exact mul_le_mul_of_nonneg_left hrε Real.pi_pos.le

/-- A geometric sum with ratio `≠ 1` on the unit circle is bounded. -/
theorem norm_unit_geom_sum_le {w : ℂ} (hw : ‖w‖ = 1) (h1 : w ≠ 1) (N : ℕ) :
    ‖∑ n ∈ Finset.range N, w ^ n‖ ≤ 2 / ‖w - 1‖ := by
  have hne : w - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hpos : 0 < ‖w - 1‖ := norm_pos_iff.mpr hne
  rw [geom_sum_eq h1, norm_div, div_le_div_iff_of_pos_right hpos]
  calc ‖w ^ N - 1‖ ≤ ‖w ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hw, one_pow, norm_one]; norm_num

/-- `e^{2πix} ≠ 1` for `0 < |x| < 1`. -/
theorem exp_two_pi_mul_ne_one {x : ℝ} (hx0 : x ≠ 0) (hx1 : |x| < 1) :
    Complex.exp (2 * Real.pi * I * x) ≠ 1 := by
  intro h
  rw [Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have h2 : (x : ℂ) = n := by
    have hpi : (2 * Real.pi * I : ℂ) ≠ 0 := by simp [Real.pi_ne_zero, Complex.I_ne_zero]
    apply mul_left_cancel₀ hpi
    rw [hn]; ring
  have h3 : x = n := by exact_mod_cast h2
  rw [h3] at hx0 hx1
  have : (n : ℝ) ≠ 0 := hx0
  have hn0 : n ≠ 0 := by exact_mod_cast this
  have : (1 : ℝ) ≤ |(n : ℝ)| := by
    rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hn0
  linarith

/-- The kernel `Π_i cos(π(tα_i − x_i))^{2M}` along the flow. -/
def flowKernel (M : ℕ) (α x : d → ℝ) (t : ℝ) : ℝ :=
  ∏ i, Real.cos (Real.pi * (t * α i - x i)) ^ (2 * M)

/-- Off the `ε`-box around `x` the kernel is at most `cos(πε)^{2M}`. -/
theorem flowKernel_le_of_far (M : ℕ) (α x : d → ℝ) {ε t : ℝ} (hε : 0 ≤ ε) {i₀ : d}
    (hfar : ∀ z : ℤ, ε ≤ |t * α i₀ - x i₀ - z|) :
    flowKernel M α x t ≤ Real.cos (Real.pi * ε) ^ (2 * M) := by
  classical
  unfold flowKernel
  rw [← Finset.mul_prod_erase _ _ (mem_univ i₀)]
  have h1 := abs_cos_pi_le_of_far hε hfar
  have h2 : Real.cos (Real.pi * (t * α i₀ - x i₀)) ^ (2 * M) ≤ Real.cos (Real.pi * ε) ^ (2 * M) := by
    rw [pow_mul, pow_mul]
    apply pow_le_pow_left₀ (sq_nonneg _)
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  have h3 : ∏ i ∈ univ.erase i₀, Real.cos (Real.pi * (t * α i - x i)) ^ (2 * M) ≤ 1 := by
    apply Finset.prod_le_one (fun i _ => by rw [pow_mul]; positivity)
    intro i _
    rw [pow_mul]
    apply pow_le_one₀ (sq_nonneg _)
    rw [sq_le_one_iff_abs_le_one]
    exact Real.abs_cos_le_one _
  have h0 : 0 ≤ ∏ i ∈ univ.erase i₀, Real.cos (Real.pi * (t * α i - x i)) ^ (2 * M) :=
    Finset.prod_nonneg fun i _ => by rw [pow_mul]; positivity
  have hc : 0 ≤ Real.cos (Real.pi * ε) ^ (2 * M) := by rw [pow_mul]; positivity
  calc Real.cos (Real.pi * (t * α i₀ - x i₀)) ^ (2 * M) *
        ∏ i ∈ univ.erase i₀, Real.cos (Real.pi * (t * α i - x i)) ^ (2 * M)
      ≤ Real.cos (Real.pi * ε) ^ (2 * M) * 1 := mul_le_mul h2 h3 h0 hc
    _ = Real.cos (Real.pi * ε) ^ (2 * M) := mul_one _

/-- For `0 < c < 1` the kernel order can be chosen with `(2M+1)^d c^{2M} < 1/2`. -/
theorem exists_kernel_order (D : ℕ) {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    ∃ M : ℕ, ((2 * M + 1 : ℕ) : ℝ) ^ D * c ^ (2 * M) < 1 / 2 := by
  have htend := tendsto_pow_const_mul_const_pow_of_abs_lt_one D
    (show |c| < 1 by rw [abs_of_pos hc0]; exact hc1)
  have hev : ∀ᶠ n : ℕ in atTop, (n : ℝ) ^ D * c ^ n < c / 2 ^ (D + 1) :=
    htend.eventually (gt_mem_nhds (by positivity))
  obtain ⟨K, hK⟩ := eventually_atTop.mp hev
  refine ⟨K + 1, ?_⟩
  have h1 := hK (2 * (K + 1) + 1) (by omega)
  have h2 : ((2 * (K + 1) + 1 : ℕ) : ℝ) ^ D * c ^ (2 * (K + 1) + 1) =
      (((2 * (K + 1) + 1 : ℕ) : ℝ) ^ D * c ^ (2 * (K + 1))) * c := by ring
  rw [h2] at h1
  have h3 : c / 2 ^ (D + 1) ≤ c / 2 := by
    apply div_le_div_of_nonneg_left hc0.le (by norm_num)
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (D + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have h4 : (((2 * (K + 1) + 1 : ℕ) : ℝ) ^ D * c ^ (2 * (K + 1))) * c < (1 / 2) * c := by
    linarith
  exact lt_of_mul_lt_mul_right h4 hc0.le

/-- **Time averages of the kernel.** Under the relation hypothesis there is a step `h > 0` such that
the averages of the kernel along `t_n = T + nh` approach a resonant mass `a₀ ≥ (2M+1)^{−d}` at
rate `O(1/N)`. -/
theorem exists_flowKernel_average (M : ℕ) {α : d → ℝ} (x : d → ℝ)
    (hrel : ∀ k : d → ℤ, ∑ i, (k i : ℝ) * α i = 0 → ∃ z : ℤ, ∑ i, (k i : ℝ) * x i = z) (T : ℝ) :
    ∃ h : ℝ, 0 < h ∧ ∃ a₀ E : ℝ, (1 / ((2 * M + 1 : ℕ) : ℝ)) ^ Fintype.card d ≤ a₀ ∧ 0 ≤ E ∧
      ∀ N : ℕ, 0 < N →
        ‖(∑ n ∈ Finset.range N, ((flowKernel M α x (T + n * h) : ℝ) : ℂ)) / N - a₀‖ ≤ E / N := by
  classical
  set J₀ : d → Fin (2 * M + 1) := fun _ => ⟨M, by omega⟩ with hJ₀
  set ω : (d → Fin (2 * M + 1)) → ℝ := fun J => ∑ i, α i * (((J i : ℕ) : ℝ) - M) with hω
  have hω₀ : ω J₀ = 0 := by simp [hω, hJ₀]
  have hres : ∀ J, ω J = 0 → ∃ z : ℤ, ∑ i, x i * (((J i : ℕ) : ℝ) - M) = z := by
    intro J hJ
    obtain ⟨z, hz⟩ := hrel (fun i => ((J i : ℕ) : ℤ) - M) (by
      rw [← hJ, hω]
      refine Finset.sum_congr rfl fun i _ => ?_
      push_cast
      ring)
    refine ⟨z, ?_⟩
    rw [← hz]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  set B : ℝ := 1 + ∑ J, |ω J| with hB
  have hB1 : 1 ≤ B := by
    rw [hB]; have := Finset.sum_nonneg (fun J (_ : J ∈ (univ : Finset (d → Fin (2 * M + 1)))) =>
      abs_nonneg (ω J)); linarith
  set h : ℝ := 1 / (2 * B) with hh
  have hh0 : 0 < h := by positivity
  set w : (d → Fin (2 * M + 1)) → ℂ := fun J => Complex.exp (2 * Real.pi * I * (h * ω J)) with hw
  have hwnorm : ∀ J, ‖w J‖ = 1 := by
    intro J
    rw [hw, Complex.norm_exp]
    simp [Complex.mul_re, Complex.mul_im]
  have hw1 : ∀ J, ω J ≠ 0 → w J ≠ 1 := by
    intro J hωJ
    have hle : |ω J| ≤ ∑ J', |ω J'| :=
      Finset.single_le_sum (f := fun J' => |ω J'|) (fun J' _ => abs_nonneg _) (mem_univ J)
    have h1 : |h * ω J| < 1 := by
      rw [abs_mul, abs_of_pos hh0, hh, div_mul_eq_mul_div, one_mul,
        div_lt_one (by linarith : (0 : ℝ) < 2 * B)]
      linarith
    have := exp_two_pi_mul_ne_one (mul_ne_zero hh0.ne' hωJ) h1
    push_cast at this
    exact this
  set C : (d → Fin (2 * M + 1)) → ℝ := fun J => ∏ i, cosKernelCoeff M (J i) with hC
  have hC0 : ∀ J, 0 ≤ C J := fun J => Finset.prod_nonneg fun i _ => cosKernelCoeff_nonneg M _
  refine ⟨h, hh0, ∑ J ∈ univ.filter (fun J => ω J = 0), C J, ∑ J, C J * (2 / ‖w J - 1‖), ?_,
    Finset.sum_nonneg fun J _ => mul_nonneg (hC0 J) (by positivity), ?_⟩
  · refine le_trans ?_ (Finset.single_le_sum (f := C) (fun J _ => hC0 J)
      (Finset.mem_filter.mpr ⟨mem_univ _, hω₀⟩))
    rw [hC]
    simp only [hJ₀]
    rw [Finset.prod_const, Finset.card_univ]
    apply pow_le_pow_left₀ (by positivity)
    have := cosKernelCoeff_middle_ge M
    push_cast
    exact this
  intro N hN
  have hNc : (N : ℂ) ≠ 0 := by exact_mod_cast hN.ne'
  have hexp : ∀ n : ℕ, ((flowKernel M α x (T + n * h) : ℝ) : ℂ) = ∑ J, (C J : ℂ) *
      (Complex.exp (2 * Real.pi * I * (T * ω J - ∑ i, x i * (((J i : ℕ) : ℝ) - M))) *
        w J ^ n) := by
    intro n
    rw [flowKernel, prod_cos_pow_eq_sum M (fun i => (T + n * h) * α i - x i)]
    refine Finset.sum_congr rfl fun J _ => ?_
    rw [hw, ← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 2
    simp only [hω]
    push_cast
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hRterm : ∀ J ∈ univ.filter (fun J => ω J = 0), ∀ n : ℕ, (C J : ℂ) *
      (Complex.exp (2 * Real.pi * I * (T * ω J - ∑ i, x i * (((J i : ℕ) : ℝ) - M))) *
        w J ^ n) = C J := by
    intro J hJ n
    have hω0 : ω J = 0 := (Finset.mem_filter.mp hJ).2
    obtain ⟨z, hz⟩ := hres J hω0
    have hw0 : w J = 1 := by rw [hw]; simp [hω0]
    rw [hω0, hz, hw0, one_pow, mul_one]
    have : Complex.exp (2 * Real.pi * I * ((T : ℂ) * ((0 : ℝ) : ℂ) - ((z : ℝ) : ℂ))) = 1 := by
      rw [show (2 * Real.pi * I * ((T : ℂ) * ((0 : ℝ) : ℂ) - ((z : ℝ) : ℂ))) =
        ((-z : ℤ) : ℂ) * (2 * Real.pi * I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    rw [this, mul_one]
  rw [Finset.sum_congr rfl fun n _ => hexp n, Finset.sum_comm,
    ← Finset.sum_filter_add_sum_filter_not univ (fun J => ω J = 0)]
  rw [show (∑ J ∈ univ.filter (fun J => ω J = 0), ∑ n ∈ Finset.range N, (C J : ℂ) *
      (Complex.exp (2 * Real.pi * I * (T * ω J - ∑ i, x i * (((J i : ℕ) : ℝ) - M))) * w J ^ n))
      = (N : ℂ) * ((∑ J ∈ univ.filter (fun J => ω J = 0), C J : ℝ) : ℂ) by
    rw [Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun J hJ => ?_
    rw [Finset.sum_congr rfl fun n _ => hRterm J hJ n, Finset.sum_const, Finset.card_range,
      nsmul_eq_mul]]
  rw [add_div, mul_div_cancel_left₀ _ hNc, add_sub_cancel_left]
  rw [norm_div, Complex.norm_natCast, div_le_div_iff_of_pos_right (by exact_mod_cast hN)]
  calc ‖∑ J ∈ univ.filter (fun J => ¬ω J = 0), ∑ n ∈ Finset.range N, (C J : ℂ) *
        (Complex.exp (2 * Real.pi * I * (T * ω J - ∑ i, x i * (((J i : ℕ) : ℝ) - M))) *
          w J ^ n)‖
      ≤ ∑ J ∈ univ.filter (fun J => ¬ω J = 0), ‖∑ n ∈ Finset.range N, (C J : ℂ) *
        (Complex.exp (2 * Real.pi * I * (T * ω J - ∑ i, x i * (((J i : ℕ) : ℝ) - M))) *
          w J ^ n)‖ := norm_sum_le _ _
    _ ≤ ∑ J ∈ univ.filter (fun J => ¬ω J = 0), C J * (2 / ‖w J - 1‖) := by
        refine Finset.sum_le_sum fun J hJ => ?_
        have hJne : ω J ≠ 0 := (Finset.mem_filter.mp hJ).2
        rw [← Finset.mul_sum, ← Finset.mul_sum, norm_mul, norm_mul]
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hC0 J)]
        have hunit : ‖Complex.exp (2 * Real.pi * I *
            (T * ω J - ∑ i, x i * (((J i : ℕ) : ℝ) - M)))‖ = 1 := by
          rw [Complex.norm_exp]
          simp [Complex.mul_re, Complex.mul_im]
        rw [hunit, one_mul]
        exact mul_le_mul_of_nonneg_left (norm_unit_geom_sum_le (hwnorm J) (hw1 J hJne) N) (hC0 J)
    _ ≤ ∑ J, C J * (2 / ‖w J - 1‖) :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          fun J _ _ => mul_nonneg (hC0 J) (by positivity)

/-- **Kronecker's theorem for linear flows, with relations.** If every integer relation
`Σ k_i α_i = 0` makes `Σ k_i x_i` an integer, the flow `t α` returns arbitrarily late into every
neighbourhood of `x` modulo `ℤ^d`. -/
theorem exists_flow_near_of_relations {α : d → ℝ} (x : d → ℝ)
    (hrel : ∀ k : d → ℤ, ∑ i, (k i : ℝ) * α i = 0 → ∃ z : ℤ, ∑ i, (k i : ℝ) * x i = z)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧ ∀ i, ∃ z : ℤ, |t * α i - x i - z| < ε := by
  by_contra hcon
  push Not at hcon
  set ε' : ℝ := min ε (1 / 4) with hε'
  have hε'0 : 0 < ε' := lt_min hε (by norm_num)
  have hε'4 : ε' ≤ 1 / 4 := min_le_right _ _
  have hε'ε : ε' ≤ ε := min_le_left _ _
  set c : ℝ := Real.cos (Real.pi * ε') with hc
  have hc0 : 0 < c := Real.cos_pos_of_mem_Ioo ⟨by nlinarith [Real.pi_pos], by nlinarith [Real.pi_pos]⟩
  have hc1 : c < 1 := by
    rw [hc]
    have h := Real.cos_lt_cos_of_nonneg_of_le_pi_div_two (le_refl 0)
      (show Real.pi * ε' ≤ Real.pi / 2 by nlinarith [Real.pi_pos])
      (show 0 < Real.pi * ε' by positivity)
    rwa [Real.cos_zero] at h
  obtain ⟨M, hMbound⟩ := exists_kernel_order (Fintype.card d) hc0 hc1
  obtain ⟨h, hh0, a₀, E, ha₀_ge, hE0, havg⟩ := exists_flowKernel_average M x hrel T
  have hsmall : ∀ t, T ≤ t → flowKernel M α x t ≤ c ^ (2 * M) := by
    intro t ht
    obtain ⟨i₀, hi₀⟩ := hcon t ht
    exact flowKernel_le_of_far M α x hε'0.le (i₀ := i₀) fun z => le_trans hε'ε (hi₀ z)
  have ha₀pos : 0 < a₀ := lt_of_lt_of_le (by positivity) ha₀_ge
  have hq : c ^ (2 * M) < a₀ / 2 := by
    have h2 : (1 / ((2 * M + 1 : ℕ) : ℝ)) ^ Fintype.card d =
        1 / ((2 * M + 1 : ℕ) : ℝ) ^ Fintype.card d := by rw [one_div_pow]
    have h3 : 0 < ((2 * M + 1 : ℕ) : ℝ) ^ Fintype.card d := by positivity
    rw [h2] at ha₀_ge
    have : c ^ (2 * M) < 1 / 2 / ((2 * M + 1 : ℕ) : ℝ) ^ Fintype.card d := by
      rw [lt_div_iff₀ h3]; linarith
    calc c ^ (2 * M) < 1 / 2 / ((2 * M + 1 : ℕ) : ℝ) ^ Fintype.card d := this
      _ = (1 / ((2 * M + 1 : ℕ) : ℝ) ^ Fintype.card d) / 2 := by ring
      _ ≤ a₀ / 2 := by linarith
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * E / (a₀ / 2 - c ^ (2 * M)) + 1)
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := lt_of_le_of_lt (by
      have : 0 ≤ 2 * E / (a₀ / 2 - c ^ (2 * M)) := div_nonneg (by linarith) (by linarith)
      linarith) hN
    exact_mod_cast this
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNpos
  have h1 := havg N hNpos
  have hre : ((∑ n ∈ Finset.range N, ((flowKernel M α x (T + n * h) : ℝ) : ℂ)) / N).re ≤
      c ^ (2 * M) := by
    rw [show ((∑ n ∈ Finset.range N, ((flowKernel M α x (T + n * h) : ℝ) : ℂ)) / N) =
      (((∑ n ∈ Finset.range N, flowKernel M α x (T + n * h)) / N : ℝ) : ℂ) by push_cast; rfl,
      Complex.ofReal_re, div_le_iff₀ hNr]
    calc ∑ n ∈ Finset.range N, flowKernel M α x (T + n * h)
        ≤ ∑ _n ∈ Finset.range N, c ^ (2 * M) :=
          Finset.sum_le_sum fun n _ => hsmall _ (by
            have : 0 ≤ (n : ℝ) * h := by positivity
            linarith)
      _ = c ^ (2 * M) * N := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_comm]
  have h2 : a₀ - E / N ≤ ((∑ n ∈ Finset.range N, ((flowKernel M α x (T + n * h) : ℝ) : ℂ)) / N).re := by
    have := Complex.abs_re_le_norm
      ((∑ n ∈ Finset.range N, ((flowKernel M α x (T + n * h) : ℝ) : ℂ)) / N - a₀)
    rw [Complex.sub_re, Complex.ofReal_re] at this
    have := (abs_le.mp (this.trans h1)).1
    linarith
  have h3 : E / N < a₀ / 2 - c ^ (2 * M) := by
    rw [div_lt_iff₀ hNr]
    have hgap : 0 < a₀ / 2 - c ^ (2 * M) := by linarith
    have : 2 * E / (a₀ / 2 - c ^ (2 * M)) < N := by linarith
    rw [div_lt_iff₀ hgap] at this
    nlinarith
  linarith

/-- **Kronecker's theorem for linear flows.** -/
theorem exists_flow_near_of_nonresonant {α : d → ℝ} (hα : FlowNonresonant α) (x : d → ℝ)
    {ε : ℝ} (hε : 0 < ε) (T : ℝ) :
    ∃ t : ℝ, T ≤ t ∧ ∀ i, ∃ z : ℤ, |t * α i - x i - z| < ε := by
  refine exists_flow_near_of_relations x (fun k hk => ⟨0, ?_⟩) hε T
  by_cases h0 : k = 0
  · simp [h0]
  · exact absurd hk (hα k h0)

end

end GaloisForLFunctions.HTGeometry.KroneckerFlow
