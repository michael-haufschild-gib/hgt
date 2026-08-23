import Mathlib.Algebra.Order.Chebyshev
import GaloisForLFunctions.HTGeometry.JacobiWeylAlternative

/-!
# Limit point for a Jacobi matrix with quadratic weights and bounded potential

Writing the Jacobi recurrence in discrete Sturm--Liouville form

`(a_n Δu_n) − (a_{n-1} Δu_{n-1}) = −(a_n + a_{n-1} + b_n − z) u_n`

the *flux* `D_n = a_n (u_{n+1} − u_n)` obeys `D_{n+1} − D_n = −Q_n u_{n+1}` with
`Q_n = a_{n+1} + a_n + b_{n+1} − z`.  If `a_n ≳ n²` and `Q` is bounded, then two square-summable
solutions can never have a nonzero Wronskian: the flux of a square-summable solution grows at most
like `√n` times the tail of its own `ℓ²` norm, so the solution itself decays at least like
`n^{-1/2}` times that tail, and the Wronskian is squeezed to zero.
-/

namespace GaloisForLFunctions.HTGeometry

open scoped BigOperators

variable {a b : ℕ → ℝ} {z : ℂ} {u w : ℕ → ℂ}

/-- The discrete Sturm--Liouville flux of a sequence. -/
def slFlux (a : ℕ → ℝ) (u : ℕ → ℂ) (n : ℕ) : ℂ := (a n : ℂ) * (u (n + 1) - u n)

/-- The discrete Sturm--Liouville potential at site `n+1`. -/
def slPotential (a b : ℕ → ℝ) (z : ℂ) (n : ℕ) : ℂ :=
  (a (n + 1) : ℂ) + (a n : ℂ) + (b (n + 1) : ℂ) - z

/-- **The flux increment law.** -/
theorem slFlux_succ_sub (hu : IsJacobiRec a b z u) (n : ℕ) :
    slFlux a u (n + 1) - slFlux a u n = -(slPotential a b z n) * u (n + 1) := by
  simp only [slFlux, slPotential]
  linear_combination hu n

/-! ## Elementary telescoping tail estimates -/

theorem sum_Ico_inv_telescope {N P : ℕ} (hNP : N ≤ P) :
    ∑ k ∈ Finset.Ico N P, ((1 : ℝ) / (k : ℝ) - 1 / ((k : ℝ) + 1))
      = 1 / (N : ℝ) - 1 / (P : ℝ) := by
  induction P, hNP using Nat.le_induction with
  | base => simp
  | succ P hP ih =>
      rw [Finset.sum_Ico_succ_top hP, ih]
      push_cast
      ring

theorem sum_Ico_sqrtinv_telescope {N P : ℕ} (hNP : N ≤ P) :
    ∑ k ∈ Finset.Ico N P, (1 / Real.sqrt (k : ℝ) - 1 / Real.sqrt ((k : ℝ) + 1))
      = 1 / Real.sqrt (N : ℝ) - 1 / Real.sqrt (P : ℝ) := by
  induction P, hNP using Nat.le_induction with
  | base => simp
  | succ P hP ih =>
      rw [Finset.sum_Ico_succ_top hP, ih]
      have hc : ((P : ℝ) + 1) = ((P + 1 : ℕ) : ℝ) := by push_cast; ring
      rw [hc]
      ring

theorem sum_Ico_inv_sq_le {N P : ℕ} (hN : 1 ≤ N) (hNP : N ≤ P) :
    ∑ k ∈ Finset.Ico N P, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 / (N : ℝ) := by
  have hstep : ∀ k ∈ Finset.Ico N P,
      (1 : ℝ) / (k : ℝ) ^ 2 ≤ 2 * ((1 : ℝ) / (k : ℝ) - 1 / ((k : ℝ) + 1)) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans hN hk.1
    have hk0 : (0 : ℝ) < (k : ℝ) := by linarith
    have hrw : (2 : ℝ) * ((1 : ℝ) / (k : ℝ) - 1 / ((k : ℝ) + 1))
        = 2 / ((k : ℝ) * ((k : ℝ) + 1)) := by
      field_simp
      ring
    rw [hrw, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum, sum_Ico_inv_telescope hNP]
  have hP : (0 : ℝ) ≤ 1 / (P : ℝ) := by positivity
  have hN2 : (2 : ℝ) / (N : ℝ) = 2 * (1 / (N : ℝ)) := by ring
  linarith

theorem sum_Ico_sqrt_div_sq_le {N P : ℕ} (hN : 1 ≤ N) (hNP : N ≤ P) :
    ∑ k ∈ Finset.Ico N P, Real.sqrt (k : ℝ) / (k : ℝ) ^ 2 ≤ 4 / Real.sqrt (N : ℝ) := by
  have hstep : ∀ k ∈ Finset.Ico N P,
      Real.sqrt (k : ℝ) / (k : ℝ) ^ 2
        ≤ 4 * (1 / Real.sqrt (k : ℝ) - 1 / Real.sqrt ((k : ℝ) + 1)) := by
    intro k hk
    rw [Finset.mem_Ico] at hk
    have hk1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans hN hk.1
    set s := Real.sqrt (k : ℝ) with hs
    set t := Real.sqrt ((k : ℝ) + 1) with ht
    have hs0 : 0 < s := Real.sqrt_pos.mpr (by linarith)
    have ht0 : 0 < t := Real.sqrt_pos.mpr (by linarith)
    have hs2 : s ^ 2 = (k : ℝ) := Real.sq_sqrt (by linarith)
    have ht2 : t ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt (by linarith)
    have hst : s < t := by
      rw [hs, ht]
      exact Real.sqrt_lt_sqrt (by linarith) (by linarith)
    have hkey : s / (k : ℝ) ^ 2 = 1 / s ^ 3 := by
      rw [← hs2]
      field_simp
    have hrw : (4 : ℝ) * (1 / s - 1 / t) = 4 * (t - s) / (s * t) := by
      field_simp
    rw [hkey, hrw, div_le_div_iff₀ (by positivity) (by positivity)]
    have htle : t ^ 2 ≤ 2 * s ^ 2 := by rw [hs2, ht2]; linarith
    have hts : t ≤ 2 * s := by nlinarith
    have hdiff : (t - s) * (t + s) = 1 := by linear_combination ht2 - hs2
    have hkey2 : s * t * (t + s) ≤ 4 * s ^ 3 := by nlinarith [hs0, ht0, htle, hts]
    have hpos : 0 < t + s := by linarith
    have hgoal : 1 * (s * t) * (t + s) ≤ (4 * (t - s) * s ^ 3) * (t + s) := by
      rw [show (4 * (t - s) * s ^ 3) * (t + s) = 4 * s ^ 3 * ((t - s) * (t + s)) by ring, hdiff]
      linarith
    exact le_of_mul_le_mul_right hgoal hpos
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum, sum_Ico_sqrtinv_telescope hNP]
  have hP : (0 : ℝ) ≤ 1 / Real.sqrt (P : ℝ) := by positivity
  have hN4 : (4 : ℝ) / Real.sqrt (N : ℝ) = 4 * (1 / Real.sqrt (N : ℝ)) := by ring
  linarith

/-! ## Telescoping identities -/

theorem slFlux_sub (hu : IsJacobiRec a b z u) {M N : ℕ} (hMN : M ≤ N) :
    slFlux a u N - slFlux a u M
      = -∑ k ∈ Finset.Ico M N, slPotential a b z k * u (k + 1) := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
      rw [Finset.sum_Ico_succ_top hN]
      have h := slFlux_succ_sub hu N
      linear_combination ih + h

theorem sub_eq_sum_diff (u : ℕ → ℂ) {M N : ℕ} (hMN : M ≤ N) :
    u N - u M = ∑ k ∈ Finset.Ico M N, (u (k + 1) - u k) := by
  induction N, hMN using Nat.le_induction with
  | base => simp
  | succ N hN ih =>
      rw [Finset.sum_Ico_succ_top hN, ← ih]
      ring

theorem norm_diff_eq_norm_slFlux_div {n : ℕ} (han : a n ≠ 0) :
    ‖u (n + 1) - u n‖ = ‖slFlux a u n‖ / |a n| := by
  have : slFlux a u n = (a n : ℂ) * (u (n + 1) - u n) := rfl
  rw [this, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  field_simp

/-! ## Cauchy--Schwarz for a range sum -/

theorem sum_range_le_sqrt_mul {y : ℕ → ℂ} (M L : ℕ) (hy : Summable fun n => ‖y n‖ ^ 2) :
    ∑ i ∈ Finset.range L, ‖y (i + M)‖
      ≤ Real.sqrt (L : ℝ) * Real.sqrt (∑' k, ‖y (k + M)‖ ^ 2) := by
  have hshift : Summable fun k => ‖y (k + M)‖ ^ 2 := (summable_nat_add_iff M).mpr hy
  have hpart : ∑ i ∈ Finset.range L, ‖y (i + M)‖ ^ 2 ≤ ∑' k, ‖y (k + M)‖ ^ 2 :=
    hshift.sum_le_tsum _ (fun i _ => by positivity)
  have hcs := sq_sum_le_card_mul_sum_sq (s := Finset.range L)
    (f := fun i => ‖y (i + M)‖)
  have hcard : ((Finset.range L).card : ℝ) = (L : ℝ) := by simp
  rw [hcard] at hcs
  have hle : (∑ i ∈ Finset.range L, ‖y (i + M)‖) ^ 2
      ≤ (L : ℝ) * ∑' k, ‖y (k + M)‖ ^ 2 := by
    refine le_trans hcs ?_
    exact mul_le_mul_of_nonneg_left hpart (by positivity)
  have hnn : (0:ℝ) ≤ ∑ i ∈ Finset.range L, ‖y (i + M)‖ :=
    Finset.sum_nonneg (fun i _ => norm_nonneg _)
  have hT : (0:ℝ) ≤ ∑' k, ‖y (k + M)‖ ^ 2 := tsum_nonneg (fun k => by positivity)
  have := Real.sqrt_le_sqrt hle
  rwa [Real.sqrt_sq hnn, Real.sqrt_mul (by positivity)] at this

theorem tendsto_norm_zero_of_summable_sq {y : ℕ → ℂ} (hy : Summable fun n => ‖y n‖ ^ 2) :
    Filter.Tendsto (fun n => ‖y n‖) Filter.atTop (nhds 0) := by
  have h := hy.tendsto_atTop_zero
  have h2 : Filter.Tendsto (fun n => Real.sqrt (‖y n‖ ^ 2)) Filter.atTop (nhds (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp h
  simpa [Real.sqrt_sq (norm_nonneg _)] using h2

/-! ## The flux of a square-summable solution grows at most like `√n` -/

theorem norm_slFlux_le {Cq : ℝ} {N₀ : ℕ} (hu : IsJacobiRec a b z u)
    (hQ : ∀ n, N₀ ≤ n → ‖slPotential a b z n‖ ≤ Cq) (hCq : 0 ≤ Cq)
    (hu2 : Summable fun n => ‖u n‖ ^ 2)
    {M N : ℕ} (hM : N₀ ≤ M) (hMN : M ≤ N) :
    ‖slFlux a u N‖ ≤ ‖slFlux a u M‖
      + Cq * (Real.sqrt (N : ℝ) * Real.sqrt (∑' k, ‖u (k + (M + 1))‖ ^ 2)) := by
  have hdiff := slFlux_sub hu hMN
  have hb1 : ‖slFlux a u N - slFlux a u M‖ ≤ Cq * ∑ k ∈ Finset.Ico M N, ‖u (k + 1)‖ := by
    rw [hdiff, norm_neg]
    refine le_trans (norm_sum_le _ _) ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun k hk => ?_)
    rw [Finset.mem_Ico] at hk
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hQ k (le_trans hM hk.1)) (norm_nonneg _)
  have hre : ∑ k ∈ Finset.Ico M N, ‖u (k + 1)‖
      = ∑ i ∈ Finset.range (N - M), ‖u (i + (M + 1))‖ := by
    rw [Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    congr 2
    omega
  have hcs := sum_range_le_sqrt_mul (y := u) (M + 1) (N - M) hu2
  have hsq : Real.sqrt ((N - M : ℕ) : ℝ) ≤ Real.sqrt (N : ℝ) := by
    refine Real.sqrt_le_sqrt ?_
    exact_mod_cast Nat.sub_le N M
  have hTn : (0:ℝ) ≤ Real.sqrt (∑' k, ‖u (k + (M + 1))‖ ^ 2) := Real.sqrt_nonneg _
  have hb2 : ∑ k ∈ Finset.Ico M N, ‖u (k + 1)‖
      ≤ Real.sqrt (N : ℝ) * Real.sqrt (∑' k, ‖u (k + (M + 1))‖ ^ 2) := by
    rw [hre]
    exact le_trans hcs (mul_le_mul_of_nonneg_right hsq hTn)
  have hb3 : ‖slFlux a u N - slFlux a u M‖
      ≤ Cq * (Real.sqrt (N : ℝ) * Real.sqrt (∑' k, ‖u (k + (M + 1))‖ ^ 2)) :=
    le_trans hb1 (mul_le_mul_of_nonneg_left hb2 hCq)
  have := norm_sub_norm_le (slFlux a u N) (slFlux a u M)
  linarith

/-! ## A square-summable solution decays at least like `n^{-1/2}` times its own tail -/

theorem norm_le_tail_decay {c₀ Cq : ℝ} {N₀ : ℕ} (hu : IsJacobiRec a b z u)
    (hc₀ : 0 < c₀) (ha : ∀ n, N₀ ≤ n → c₀ * (n : ℝ) ^ 2 ≤ a n)
    (hQ : ∀ n, N₀ ≤ n → ‖slPotential a b z n‖ ≤ Cq) (hCq : 0 ≤ Cq)
    (hu2 : Summable fun n => ‖u n‖ ^ 2)
    {M L : ℕ} (hN₀ : 1 ≤ N₀) (hM : N₀ ≤ M) (hML : M ≤ L) :
    ‖u L‖ ≤ 2 * ‖slFlux a u M‖ / c₀ * (1 / (L : ℝ))
      + 4 * Cq * Real.sqrt (∑' k, ‖u (k + (M + 1))‖ ^ 2) / c₀ * (1 / Real.sqrt (L : ℝ)) := by
  set B : ℝ := ‖slFlux a u M‖ with hBdef
  set ε : ℝ := Real.sqrt (∑' k, ‖u (k + (M + 1))‖ ^ 2) with hεdef
  have hB0 : 0 ≤ B := norm_nonneg _
  have hε0 : 0 ≤ ε := Real.sqrt_nonneg _
  have hL1 : 1 ≤ L := le_trans hN₀ (le_trans hM hML)
  have hLr : (1:ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
  set R : ℝ := 2 * B / c₀ * (1 / (L : ℝ)) + 4 * Cq * ε / c₀ * (1 / Real.sqrt (L : ℝ)) with hRdef
  have hbound : ∀ N : ℕ, L ≤ N → ‖u N - u L‖ ≤ R := by
    intro N hLN
    have hterm : ∀ k ∈ Finset.Ico L N,
        ‖u (k + 1) - u k‖ ≤ B / c₀ * (1 / (k : ℝ) ^ 2)
          + Cq * ε / c₀ * (Real.sqrt (k : ℝ) / (k : ℝ) ^ 2) := by
      intro k hk
      rw [Finset.mem_Ico] at hk
      have hkN₀ : N₀ ≤ k := le_trans hM (le_trans hML hk.1)
      have hk1 : (1:ℝ) ≤ (k : ℝ) := by exact_mod_cast le_trans hN₀ hkN₀
      have hka : c₀ * (k : ℝ) ^ 2 ≤ a k := ha k hkN₀
      have hkpos : (0:ℝ) < c₀ * (k : ℝ) ^ 2 := by positivity
      have hapos : (0:ℝ) < a k := lt_of_lt_of_le hkpos hka
      have hF := norm_slFlux_le hu hQ hCq hu2 hM (le_trans hML hk.1)
      have hnum : (0:ℝ) ≤ B + Cq * (Real.sqrt (k : ℝ) * ε) := by positivity
      have hdiv : ‖slFlux a u k‖ / |a k|
          ≤ (B + Cq * (Real.sqrt (k : ℝ) * ε)) / (c₀ * (k : ℝ) ^ 2) := by
        rw [abs_of_pos hapos, div_le_div_iff₀ hapos hkpos]
        nlinarith [norm_nonneg (slFlux a u k)]
      have hsplit : (B + Cq * (Real.sqrt (k : ℝ) * ε)) / (c₀ * (k : ℝ) ^ 2)
          = B / c₀ * (1 / (k : ℝ) ^ 2)
            + Cq * ε / c₀ * (Real.sqrt (k : ℝ) / (k : ℝ) ^ 2) := by
        field_simp
      rw [norm_diff_eq_norm_slFlux_div (ne_of_gt hapos)]
      rw [← hsplit]
      exact hdiv
    calc ‖u N - u L‖ = ‖∑ k ∈ Finset.Ico L N, (u (k + 1) - u k)‖ := by
          rw [← sub_eq_sum_diff u hLN]
      _ ≤ ∑ k ∈ Finset.Ico L N, ‖u (k + 1) - u k‖ := norm_sum_le _ _
      _ ≤ ∑ k ∈ Finset.Ico L N, (B / c₀ * (1 / (k : ℝ) ^ 2)
            + Cq * ε / c₀ * (Real.sqrt (k : ℝ) / (k : ℝ) ^ 2)) := Finset.sum_le_sum hterm
      _ = B / c₀ * (∑ k ∈ Finset.Ico L N, (1 : ℝ) / (k : ℝ) ^ 2)
            + Cq * ε / c₀ * (∑ k ∈ Finset.Ico L N, Real.sqrt (k : ℝ) / (k : ℝ) ^ 2) := by
          rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
      _ ≤ B / c₀ * (2 / (L : ℝ)) + Cq * ε / c₀ * (4 / Real.sqrt (L : ℝ)) := by
          have h1 := sum_Ico_inv_sq_le (N := L) (P := N) hL1 hLN
          have h2 := sum_Ico_sqrt_div_sq_le (N := L) (P := N) hL1 hLN
          have hc1 : (0:ℝ) ≤ B / c₀ := by positivity
          have hc2 : (0:ℝ) ≤ Cq * ε / c₀ := by positivity
          exact add_le_add (mul_le_mul_of_nonneg_left h1 hc1)
            (mul_le_mul_of_nonneg_left h2 hc2)
      _ = R := by rw [hRdef]; ring
  have htend := tendsto_norm_zero_of_summable_sq hu2
  refine le_of_forall_pos_le_add (fun δ hδ => ?_)
  obtain ⟨N, hN1, hN2⟩ : ∃ N, L ≤ N ∧ ‖u N‖ ≤ δ := by
    have := (htend.eventually_le_const hδ).and (Filter.eventually_ge_atTop L)
    obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp this
    exact ⟨N, (hN N le_rfl).2, (hN N le_rfl).1⟩
  have := hbound N hN1
  have hsub : ‖u L‖ ≤ ‖u N‖ + ‖u N - u L‖ := by
    have h := norm_sub_le (u N) (u N - u L)
    simpa using h
  linarith

/-! ## The limit-point conclusion -/

theorem le_of_le_add_div_sqrt {X K R : ℝ} (hK : 0 ≤ K) (M : ℕ)
    (h : ∀ L : ℕ, M ≤ L → X ≤ K / Real.sqrt (L : ℝ) + R) : X ≤ R := by
  by_contra hcon
  rw [not_le] at hcon
  set e : ℝ := X - R with hedef
  have he0 : 0 < e := by linarith
  obtain ⟨L, hL⟩ := exists_nat_gt (max ((K / e) ^ 2 + 1) ((M : ℝ) + 1))
  have hLM : M ≤ L := by
    have : (M : ℝ) + 1 ≤ (L : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hL)
    have : (M : ℝ) < (L : ℝ) := by linarith
    exact_mod_cast this.le
  have hLsq : (K / e) ^ 2 < (L : ℝ) := by
    have : (K / e) ^ 2 + 1 ≤ (L : ℝ) := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hL)
    linarith
  have hLpos : (0:ℝ) < (L : ℝ) := lt_of_le_of_lt (by positivity) hLsq
  have hsq : K / e < Real.sqrt (L : ℝ) := by
    rw [show K / e = Real.sqrt ((K / e) ^ 2) from (Real.sqrt_sq (by positivity)).symm]
    exact Real.sqrt_lt_sqrt (by positivity) hLsq
  have hs0 : (0:ℝ) < Real.sqrt (L : ℝ) := Real.sqrt_pos.mpr hLpos
  have hlt : K / Real.sqrt (L : ℝ) < e := by
    rw [div_lt_iff₀ hs0]
    rw [div_lt_iff₀ he0] at hsq
    linarith
  have := h L hLM
  linarith

theorem crossWronskian_eq_flux (a : ℕ → ℝ) (u w : ℕ → ℂ) (n : ℕ) :
    crossWronskian a u w n = w n * slFlux a u n - u n * slFlux a w n := by
  simp only [crossWronskian, slFlux]
  ring

set_option maxHeartbeats 1000000 in
/-- **Limit point for quadratic weights and bounded potential.**  Two square-summable solutions of
the same Jacobi recurrence necessarily have vanishing Wronskian, so the square-summable solutions
never span the whole solution space. -/
theorem crossWronskian_eq_zero_of_both_summable
    {c₀ Cq : ℝ} {N₀ : ℕ}
    (hu : IsJacobiRec a b z u) (hw : IsJacobiRec a b z w)
    (hN₀ : 1 ≤ N₀) (hc₀ : 0 < c₀)
    (ha : ∀ n, N₀ ≤ n → c₀ * (n : ℝ) ^ 2 ≤ a n)
    (hQ : ∀ n, N₀ ≤ n → ‖slPotential a b z n‖ ≤ Cq) (hCq : 0 ≤ Cq)
    (hu2 : Summable fun n => ‖u n‖ ^ 2) (hw2 : Summable fun n => ‖w n‖ ^ 2) :
    crossWronskian a u w N₀ = 0 := by
  set X : ℝ := ‖crossWronskian a u w N₀‖ with hXdef
  have hXconst : ∀ L, ‖crossWronskian a u w L‖ = X := fun L => by
    rw [hXdef, crossWronskian_eq_zero_of_const hu hw (m := L) (n := N₀)]
  have hX0 : 0 ≤ X := norm_nonneg _
  -- the two tail scales
  set eu : ℕ → ℝ := fun M => Real.sqrt (∑' k, ‖u (k + (M + 1))‖ ^ 2) with heudef
  set ew : ℕ → ℝ := fun M => Real.sqrt (∑' k, ‖w (k + (M + 1))‖ ^ 2) with hewdef
  have heu0 : ∀ M, 0 ≤ eu M := fun M => Real.sqrt_nonneg _
  have hew0 : ∀ M, 0 ≤ ew M := fun M => Real.sqrt_nonneg _
  -- the `M`-uniform bound
  have hmain : ∀ M : ℕ, N₀ ≤ M → X ≤ 8 * Cq ^ 2 * eu M * ew M / c₀ := by
    intro M hM
    set Bu : ℝ := ‖slFlux a u M‖ with hBudef
    set Bw : ℝ := ‖slFlux a w M‖ with hBwdef
    have hBu0 : 0 ≤ Bu := norm_nonneg _
    have hBw0 : 0 ≤ Bw := norm_nonneg _
    set A : ℝ := 4 * Bu * Bw with hAdef
    set C : ℝ := 2 * Bw * Cq * eu M + 4 * Cq * ew M * Bu
      + 2 * Bu * Cq * ew M + 4 * Cq * eu M * Bw with hCdef
    have hA0 : 0 ≤ A := by positivity
    have hC0 : 0 ≤ C := by
      rw [hCdef]
      have := heu0 M; have := hew0 M
      positivity
    refine le_of_le_add_div_sqrt (K := (A + C) / c₀) (by positivity) M (fun L hML => ?_)
    have hL1 : 1 ≤ L := le_trans hN₀ (le_trans hM hML)
    have hLr : (1:ℝ) ≤ (L : ℝ) := by exact_mod_cast hL1
    set s : ℝ := Real.sqrt (L : ℝ) with hsdef
    have hs1 : 1 ≤ s := by
      rw [hsdef, show (1:ℝ) = Real.sqrt 1 by simp]
      exact Real.sqrt_le_sqrt hLr
    have hs0 : 0 < s := by linarith
    have hs2 : s ^ 2 = (L : ℝ) := Real.sq_sqrt (by linarith)
    -- decay and flux bounds at the index `L`
    have hEu := norm_le_tail_decay hu hc₀ ha hQ hCq hu2 hN₀ hM hML
    have hEw := norm_le_tail_decay hw hc₀ ha hQ hCq hw2 hN₀ hM hML
    have hFu := norm_slFlux_le hu hQ hCq hu2 hM hML
    have hFw := norm_slFlux_le hw hQ hCq hw2 hM hML
    have hEu' : c₀ * ((L : ℝ) * ‖u L‖) ≤ 2 * Bu + 4 * Cq * eu M * s := by
      have hLpos : (0:ℝ) < (L : ℝ) := by linarith
      have hstep : (L : ℝ) * ‖u L‖
          ≤ (L : ℝ) * (2 * Bu / c₀ * (1 / (L : ℝ)) + 4 * Cq * eu M / c₀ * (1 / s)) :=
        mul_le_mul_of_nonneg_left hEu hLpos.le
      have hrw : (L : ℝ) * (2 * Bu / c₀ * (1 / (L : ℝ)) + 4 * Cq * eu M / c₀ * (1 / s))
          = (2 * Bu + 4 * Cq * eu M * s) / c₀ := by
        rw [← hs2]
        field_simp
      rw [hrw] at hstep
      have := mul_le_mul_of_nonneg_left hstep hc₀.le
      rw [mul_div_cancel₀ _ hc₀.ne'] at this
      linarith
    have hEw' : c₀ * ((L : ℝ) * ‖w L‖) ≤ 2 * Bw + 4 * Cq * ew M * s := by
      have hLpos : (0:ℝ) < (L : ℝ) := by linarith
      have hstep : (L : ℝ) * ‖w L‖
          ≤ (L : ℝ) * (2 * Bw / c₀ * (1 / (L : ℝ)) + 4 * Cq * ew M / c₀ * (1 / s)) :=
        mul_le_mul_of_nonneg_left hEw hLpos.le
      have hrw : (L : ℝ) * (2 * Bw / c₀ * (1 / (L : ℝ)) + 4 * Cq * ew M / c₀ * (1 / s))
          = (2 * Bw + 4 * Cq * ew M * s) / c₀ := by
        rw [← hs2]
        field_simp
      rw [hrw] at hstep
      have := mul_le_mul_of_nonneg_left hstep hc₀.le
      rw [mul_div_cancel₀ _ hc₀.ne'] at this
      linarith
    -- the Wronskian in flux form
    have hXle : X ≤ ‖w L‖ * ‖slFlux a u L‖ + ‖u L‖ * ‖slFlux a w L‖ := by
      rw [← hXconst L, crossWronskian_eq_flux]
      refine le_trans (norm_sub_le _ _) ?_
      rw [norm_mul, norm_mul]
    -- multiply out
    have hp1 : (c₀ * s ^ 2 * ‖w L‖) * ‖slFlux a u L‖
        ≤ (2 * Bw + 4 * Cq * ew M * s) * (Bu + Cq * (s * eu M)) := by
      refine mul_le_mul ?_ hFu (norm_nonneg _)
        (by nlinarith [hBw0, mul_nonneg (mul_nonneg hCq (hew0 M)) hs0.le])
      rw [hs2]
      linarith [hEw']
    have hp2 : (c₀ * s ^ 2 * ‖u L‖) * ‖slFlux a w L‖
        ≤ (2 * Bu + 4 * Cq * eu M * s) * (Bw + Cq * (s * ew M)) := by
      refine mul_le_mul ?_ hFw (norm_nonneg _)
        (by nlinarith [hBu0, mul_nonneg (mul_nonneg hCq (heu0 M)) hs0.le])
      rw [hs2]
      linarith [hEu']
    have hcs0 : (0:ℝ) < c₀ * s ^ 2 := by positivity
    have hXmul : (c₀ * s ^ 2) * X ≤ A + C * s + 8 * Cq ^ 2 * eu M * ew M * s ^ 2 := by
      have hxx : (c₀ * s ^ 2) * X
          ≤ (c₀ * s ^ 2 * ‖w L‖) * ‖slFlux a u L‖ + (c₀ * s ^ 2 * ‖u L‖) * ‖slFlux a w L‖ := by
        calc (c₀ * s ^ 2) * X
            ≤ (c₀ * s ^ 2) * (‖w L‖ * ‖slFlux a u L‖ + ‖u L‖ * ‖slFlux a w L‖) :=
              mul_le_mul_of_nonneg_left hXle hcs0.le
          _ = _ := by ring
      have hsum := add_le_add hp1 hp2
      have hid : (2 * Bw + 4 * Cq * ew M * s) * (Bu + Cq * (s * eu M))
          + (2 * Bu + 4 * Cq * eu M * s) * (Bw + Cq * (s * ew M))
          = A + C * s + 8 * Cq ^ 2 * eu M * ew M * s ^ 2 := by
        rw [hAdef, hCdef]; ring
      linarith [hxx, hsum, hid]
    have hfin : (c₀ * s ^ 2) * X
        ≤ (c₀ * s ^ 2) * ((A + C) / c₀ / s + 8 * Cq ^ 2 * eu M * ew M / c₀) := by
      have hrw : (c₀ * s ^ 2) * ((A + C) / c₀ / s + 8 * Cq ^ 2 * eu M * ew M / c₀)
          = (A + C) * s + 8 * Cq ^ 2 * eu M * ew M * s ^ 2 := by
        field_simp
      rw [hrw]
      have hAs : A ≤ A * s := by nlinarith [hA0, hs1]
      linarith [hXmul, hAs]
    have := le_of_mul_le_mul_left hfin hcs0
    have hdiv : (A + C) / c₀ / s = (A + C) / c₀ / Real.sqrt (L : ℝ) := by rw [hsdef]
    linarith [this]
  -- let the window start tend to infinity
  have htu : Filter.Tendsto (fun M : ℕ => eu M) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun i : ℕ => ∑' k, ‖u (k + i)‖ ^ 2) Filter.atTop (nhds 0) :=
      tendsto_sum_nat_add fun n => ‖u n‖ ^ 2
    have h1 : Filter.Tendsto (fun M : ℕ => ∑' k, ‖u (k + (M + 1))‖ ^ 2)
        Filter.atTop (nhds 0) := h0.comp (Filter.tendsto_add_atTop_nat 1)
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    simpa [heudef, Function.comp_def] using h2
  have htw : Filter.Tendsto (fun M : ℕ => ew M) Filter.atTop (nhds 0) := by
    have h0 : Filter.Tendsto (fun i : ℕ => ∑' k, ‖w (k + i)‖ ^ 2) Filter.atTop (nhds 0) :=
      tendsto_sum_nat_add fun n => ‖w n‖ ^ 2
    have h1 : Filter.Tendsto (fun M : ℕ => ∑' k, ‖w (k + (M + 1))‖ ^ 2)
        Filter.atTop (nhds 0) := h0.comp (Filter.tendsto_add_atTop_nat 1)
    have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
    simpa [hewdef, Function.comp_def] using h2
  have htend : Filter.Tendsto (fun M : ℕ => 8 * Cq ^ 2 * eu M * ew M / c₀)
      Filter.atTop (nhds 0) := by
    have := ((htu.const_mul (8 * Cq ^ 2)).mul htw).div_const c₀
    simpa using this
  have hXle0 : X ≤ 0 := by
    refine ge_of_tendsto htend ?_
    filter_upwards [Filter.eventually_ge_atTop N₀] with M hM
    exact hmain M hM
  have : X = 0 := le_antisymm hXle0 hX0
  rwa [hXdef, norm_eq_zero] at this

end GaloisForLFunctions.HTGeometry
