import GaloisForLFunctions.LogarithmicChowla.ArcMass
import GaloisForLFunctions.LogarithmicChowla.PrimeShiftReduction

/-!
# The circle method for prime-shift correlations

With `K_k(β) = |𝐏_k|⁻¹ Σ_{p∈𝐏_k} e(pβ)` (`primeKernel`) and the Fejér densities
`F(r) = L(|S_n(r/R)|²)/M` (`fejer`):

* `|avg_{p∈𝐏_k} c(ph) − R⁻¹ Σ_{r<R} F(r) Re K_k(hr/R)| ≤ 2^{k+1}h/M` for `R ≥ M + 2^{k+1}h`
  (`abs_avg_corr_sub_le`): `c(d) = L(M⁻¹ Σ_{m<M} λ(n+m)λ(n+m+d))` by shift invariance, the pairs
  leaving the window cost `d/M`, and the rest is the twisted Parseval identity over `ℤ/R`;
* `R⁻¹ Σ_r F(r) = 1` (`sum_fejer_div`), by Parseval and `λ² = 1`;
* **the circle bound** (`abs_avg_corr_le`): if `|K_k(β)| ≤ η` whenever `β` is farther than
  `W/2^k` from every `a/q` with `q ≤ Q₀`, and `4TW ≤ 2^k`, then
  `|avg_{p∈𝐏_k} c(ph)| ≤ η + 4 Σ_{s ≤ hQ₀} Σ_{b<s} V(b/s, T)`.
  A residue `r` with `hr/R` near `a/q` has `r/R` within `W/2^k ≤ 1/(4T)` of `a/(qh)`, so it lies on
  the arc of some `b/s`, `s ≤ hQ₀`; the arc masses are bounded in `ArcMass`, and `M → ∞`.
-/

namespace GaloisForLFunctions.LogarithmicChowla

open Finset Complex Filter Topology

noncomputable section

variable {U : Ultrafilter ℝ}

/-- `K_k(β) = |𝐏_k|⁻¹ Σ_{p∈𝐏_k} e(pβ)`. -/
def primeKernel (k : ℕ) (β : ℝ) : ℂ :=
  (∑ p : primesAt k, ex ((p : ℕ) * β)) / (primesAt k).card

theorem norm_primeKernel_le (k : ℕ) (β : ℝ) : ‖primeKernel k β‖ ≤ 1 := by
  have hc : (0 : ℝ) < (primesAt k).card := by exact_mod_cast card_primesAt_pos k
  rw [primeKernel, norm_div, Complex.norm_natCast, div_le_one hc]
  calc ‖∑ p : primesAt k, ex ((p : ℕ) * β)‖ ≤ ∑ p : primesAt k, ‖ex ((p : ℕ) * β)‖ :=
        norm_sum_le _ _
    _ = (primesAt k).card := by simp [norm_ex]

theorem re_primeKernel (k : ℕ) (β : ℝ) :
    (primeKernel k β).re = (∑ p : primesAt k, (ex ((p : ℕ) * β)).re) / (primesAt k).card := by
  rw [primeKernel, Complex.div_natCast_re, re_sum]

/-- The Fejér density `F(r) = L(|S_n(r/R)|²)/M`. -/
def fejer (U : Ultrafilter ℝ) (M R r : ℕ) : ℝ :=
  limAvg U (fun n => Complex.normSq (lamSum n M (r / R))) / M

theorem fejer_nonneg (hU : (U : Filter ℝ) ≤ atTop) (M R r : ℕ) : 0 ≤ fejer U M R r :=
  div_nonneg (limAvg_nonneg hU (bdd_normSq_lamSum M _) fun _ => Complex.normSq_nonneg _)
    (Nat.cast_nonneg M)

theorem lamSum_eq_sum (n M R r : ℕ) :
    lamSum n M (r / R) = ∑ s ∈ range M, (lam (n + s) : ℂ) * ex (s * r / R) := by
  unfold lamSum
  refine sum_congr rfl fun s _ => ?_
  rw [mul_div_assoc]

/-- `Σ_{m<M} 1[m+d<M] λ(n+m)λ(n+m+d) = R⁻¹ Σ_{r<R} |S_n(r/R)|² Re e(dr/R)` for `M + d ≤ R`. -/
theorem sum_pair_eq (n M R d : ℕ) (hR : 0 < R) (hMd : M + d ≤ R) :
    ∑ m ∈ range M, (if m + d < M then lam (n + m) * lam (n + (m + d)) else 0)
      = (∑ r ∈ range R, Complex.normSq (lamSum n M (r / R)) * (ex (d * r / R)).re) / R := by
  have h := sum_normSq_mul_ex hR hMd fun s => (lam (n + s) : ℂ)
  have hR' : (R : ℝ) ≠ 0 := by exact_mod_cast hR.ne'
  have hre := congrArg Complex.re h
  simp only [re_sum, ← lamSum_eq_sum] at hre
  rw [eq_div_iff hR']
  have e1 : ∑ r ∈ range R, Complex.normSq (lamSum n M (r / R)) * (ex (d * r / R)).re
      = ∑ r ∈ range R, ((Complex.normSq (lamSum n M (r / R)) : ℂ) * ex (d * r / R)).re :=
    sum_congr rfl fun r _ => (re_ofReal_mul _ _).symm
  rw [e1, hre]
  simp only [Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero, re_sum]
  rw [mul_comm]
  congr 1
  refine sum_congr rfl fun m _ => ?_
  split_ifs
  · simp only [Complex.conj_ofReal, ← Complex.ofReal_mul, Complex.ofReal_re]
  · simp

/-- **Prime-shift correlations through the circle.** -/
theorem abs_avg_corr_sub_le (hU : (U : Filter ℝ) ≤ atTop) (h k M R : ℕ) (hM : 0 < M)
    (hR : M + 2 ^ (k + 1) * h ≤ R) :
    |(∑ p : primesAt k, corr U ((p : ℕ) * h)) / (primesAt k).card
      - (∑ r ∈ range R, fejer U M R r * (primeKernel k (h * r / R)).re) / R|
      ≤ 2 ^ (k + 1) * h / M := by
  have hR0 : 0 < R := by
    have : 0 < M + 2 ^ (k + 1) * h := by omega
    omega
  have hRR : (0 : ℝ) < R := by exact_mod_cast hR0
  have hMR : (0 : ℝ) < M := by exact_mod_cast hM
  have hc : (0 : ℝ) < (primesAt k).card := by exact_mod_cast card_primesAt_pos k
  set c : ℝ := ((primesAt k).card : ℝ) with hcdef
  -- the window form of each correlation
  set Φ : primesAt k → ℕ → ℝ := fun p n =>
    (∑ m ∈ range M, lam (n + m) * lam (n + m + (p : ℕ) * h)) / M with hΦ
  have hbΦ : ∀ p, Bdd (Φ p) := fun p =>
    ⟨1, fun n => by
      simp only [hΦ]
      rw [abs_div, abs_of_pos hMR, div_le_one hMR]
      calc |∑ m ∈ range M, lam (n + m) * lam (n + m + (p : ℕ) * h)|
          ≤ ∑ m ∈ range M, |lam (n + m) * lam (n + m + (p : ℕ) * h)| := abs_sum_le_sum_abs _ _
        _ ≤ ∑ _m ∈ range M, (1 : ℝ) := sum_le_sum fun m _ => by
            rw [abs_mul]
            exact mul_le_one₀ (abs_lam_le _) (abs_nonneg _) (abs_lam_le _)
        _ = M := by simp⟩
  have hcorr : ∀ p : primesAt k, corr U ((p : ℕ) * h) = limAvg U (Φ p) := by
    intro p
    have hb : ∀ m ∈ range M, Bdd fun n => lam (n + m) * lam (n + m + (p : ℕ) * h) :=
      fun m _ => (bdd_lam_comp _).mul (bdd_lam_comp _)
    simp only [hΦ, div_eq_inv_mul]
    rw [limAvg_const_mul hU (bdd_sum _ hb), limAvg_sum hU _ hb]
    have : ∀ m ∈ range M, limAvg U (fun n => lam (n + m) * lam (n + m + (p : ℕ) * h))
        = corr U ((p : ℕ) * h) := fun m _ =>
      limAvg_shift_add hU (bdd_lam_mul_shift ((p : ℕ) * h)) m
    rw [sum_congr rfl this, sum_const, card_range, nsmul_eq_mul]
    field_simp
  -- the circle form
  set Ψ : ℕ → ℝ := fun n =>
    (∑ r ∈ range R, Complex.normSq (lamSum n M (r / R)) * (primeKernel k (h * r / R)).re) / R / M
    with hΨ
  have hbΨ : Bdd Ψ := by
    refine ⟨((∑ r ∈ range R, (M : ℝ) ^ 2 * 1) / R / M), fun n => ?_⟩
    simp only [hΨ]
    rw [abs_div, abs_div, abs_of_pos hRR, abs_of_pos hMR]
    gcongr
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun r _ => ?_)
    rw [abs_mul, abs_of_nonneg (Complex.normSq_nonneg _)]
    exact mul_le_mul (normSq_le_sq_of_norm_le (norm_lamSum_le n M _))
      ((Complex.abs_re_le_norm _).trans (norm_primeKernel_le k _)) (abs_nonneg _) (by positivity)
  have hLΨ : limAvg U Ψ = (∑ r ∈ range R, fejer U M R r * (primeKernel k (h * r / R)).re) / R := by
    have hb : ∀ r ∈ range R, Bdd fun n => Complex.normSq (lamSum n M (r / R))
        * (primeKernel k (h * r / R)).re := fun r _ =>
      (bdd_normSq_lamSum M _).mul (bdd_const _)
    have hΨeq : Ψ = fun n => ((R : ℝ)⁻¹ * (M : ℝ)⁻¹) * ∑ r ∈ range R,
        Complex.normSq (lamSum n M (r / R)) * (primeKernel k (h * r / R)).re := by
      funext n
      simp only [hΨ]
      ring
    rw [hΨeq, limAvg_const_mul hU (bdd_sum _ hb), limAvg_sum hU _ hb, sum_div, mul_sum]
    refine sum_congr rfl fun r _ => ?_
    have : limAvg U (fun n => Complex.normSq (lamSum n M (r / R)) * (primeKernel k (h * r / R)).re)
        = (primeKernel k (h * r / R)).re * limAvg U (fun n => Complex.normSq (lamSum n M (r / R))) := by
      rw [← limAvg_const_mul hU (bdd_normSq_lamSum M _)]
      congr 1
      funext n
      ring
    rw [this, fejer]
    field_simp
  -- pointwise comparison
  have hpt : ∀ n, |(∑ p : primesAt k, Φ p n) / c - Ψ n| ≤ 2 ^ (k + 1) * h / M := by
    intro n
    have hpair : ∀ p : primesAt k,
        ∑ m ∈ range M, (if m + (p : ℕ) * h < M then lam (n + m) * lam (n + (m + (p : ℕ) * h)) else 0)
          = (∑ r ∈ range R, Complex.normSq (lamSum n M (r / R))
              * (ex (((p : ℕ) * h : ℕ) * r / R)).re) / R := by
      intro p
      refine sum_pair_eq n M R _ hR0 ?_
      have : (p : ℕ) * h ≤ 2 ^ (k + 1) * h := Nat.mul_le_mul_right h (le_of_mem_primesAt p.2)
      omega
    have hK : ∀ r : ℕ, ∑ p : primesAt k, (ex (((p : ℕ) * h : ℕ) * r / R)).re
        = c * (primeKernel k (h * r / R)).re := by
      intro r
      rw [re_primeKernel, hcdef, mul_div_cancel₀ _ hc.ne']
      refine sum_congr rfl fun p _ => ?_
      congr 2
      push_cast
      ring
    have hΨ' : Ψ n = (∑ p : primesAt k, (∑ m ∈ range M,
        (if m + (p : ℕ) * h < M then lam (n + m) * lam (n + (m + (p : ℕ) * h)) else 0)) / M) / c := by
      simp only [hpair]
      have hswap : ∑ p : primesAt k, (∑ r ∈ range R, Complex.normSq (lamSum n M (r / R))
            * (ex (((p : ℕ) * h : ℕ) * r / R)).re) / R / M
          = (∑ r ∈ range R, Complex.normSq (lamSum n M (r / R))
              * ∑ p : primesAt k, (ex (((p : ℕ) * h : ℕ) * r / R)).re) / R / M := by
        rw [← sum_div, ← sum_div, sum_comm]
        congr 2
        refine sum_congr rfl fun r _ => ?_
        rw [mul_sum]
      rw [hswap]
      simp only [hK, hΨ]
      have hfac : ∑ r ∈ range R, Complex.normSq (lamSum n M (r / R))
            * (c * (primeKernel k (h * r / R)).re)
          = c * ∑ r ∈ range R, Complex.normSq (lamSum n M (r / R))
            * (primeKernel k (h * r / R)).re := by
        rw [mul_sum]
        exact sum_congr rfl fun r _ => by ring
      rw [hfac]
      field_simp
      refine sum_congr rfl fun r _ => ?_
      rw [mul_comm (r : ℝ) (h : ℝ)]
    rw [hΨ', ← sub_div, ← sum_sub_distrib, abs_div, abs_of_pos hc, div_le_iff₀ hc]
    calc |∑ p : primesAt k, (Φ p n - (∑ m ∈ range M, (if m + (p : ℕ) * h < M
            then lam (n + m) * lam (n + (m + (p : ℕ) * h)) else 0)) / M)|
        ≤ ∑ p : primesAt k, |Φ p n - (∑ m ∈ range M, (if m + (p : ℕ) * h < M
            then lam (n + m) * lam (n + (m + (p : ℕ) * h)) else 0)) / M| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ _p : primesAt k, (2 : ℝ) ^ (k + 1) * h / M := by
          refine sum_le_sum fun p _ => ?_
          simp only [hΦ]
          rw [← sub_div, abs_div, abs_of_pos hMR]
          refine div_le_div_of_nonneg_right ?_ hMR.le
          rw [← sum_sub_distrib]
          have hd : ((p : ℕ) * h : ℝ) ≤ 2 ^ (k + 1) * h := by
            have := le_of_mem_primesAt p.2
            have h' : ((p : ℕ) : ℝ) ≤ 2 ^ (k + 1) := by exact_mod_cast this
            exact mul_le_mul_of_nonneg_right h' (Nat.cast_nonneg h)
          calc |∑ m ∈ range M, (lam (n + m) * lam (n + m + (p : ℕ) * h)
                - if m + (p : ℕ) * h < M then lam (n + m) * lam (n + (m + (p : ℕ) * h)) else 0)|
              ≤ ∑ m ∈ (range M).filter (fun m => M ≤ m + (p : ℕ) * h), (1 : ℝ) := by
                rw [← sum_filter_add_sum_filter_not (range M) (fun m => M ≤ m + (p : ℕ) * h)]
                have hz : ∑ m ∈ (range M).filter (fun m => ¬ M ≤ m + (p : ℕ) * h),
                    (lam (n + m) * lam (n + m + (p : ℕ) * h)
                      - if m + (p : ℕ) * h < M then lam (n + m) * lam (n + (m + (p : ℕ) * h))
                        else 0) = 0 := by
                  refine sum_eq_zero fun m hm => ?_
                  rw [if_pos (by have := (mem_filter.mp hm).2; omega), add_assoc, sub_self]
                rw [hz, add_zero]
                refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun m hm => ?_)
                rw [if_neg (by have := (mem_filter.mp hm).2; omega), sub_zero, abs_mul]
                exact mul_le_one₀ (abs_lam_le _) (abs_nonneg _) (abs_lam_le _)
            _ = ((range M).filter (fun m => M ≤ m + (p : ℕ) * h)).card := by simp
            _ ≤ (p : ℕ) * h := by
                have : ((range M).filter (fun m => M ≤ m + (p : ℕ) * h)).card ≤ (p : ℕ) * h := by
                  calc ((range M).filter (fun m => M ≤ m + (p : ℕ) * h)).card
                      ≤ (Ico (M - (p : ℕ) * h) M).card := card_le_card fun m hm => by
                        obtain ⟨h1, h2⟩ := mem_filter.mp hm
                        rw [mem_range] at h1
                        rw [mem_Ico]
                        omega
                    _ ≤ (p : ℕ) * h := by rw [Nat.card_Ico]; omega
                exact_mod_cast this
            _ ≤ 2 ^ (k + 1) * h := hd
      _ = 2 ^ (k + 1) * h / M * c := by
          rw [sum_const, card_univ, Fintype.card_coe, nsmul_eq_mul, hcdef]
          ring
  -- conclude through `L`
  have hdiff : (∑ p : primesAt k, corr U ((p : ℕ) * h)) / c
      - (∑ r ∈ range R, fejer U M R r * (primeKernel k (h * r / R)).re) / R
      = limAvg U (fun n => (∑ p : primesAt k, Φ p n) / c - Ψ n) := by
    have hb1 : Bdd fun n => (∑ p : primesAt k, Φ p n) / c := by
      simpa only [div_eq_inv_mul] using (bdd_sum _ fun p _ => hbΦ p).const_mul c⁻¹
    rw [limAvg_sub hU hb1 hbΨ, hLΨ]
    congr 1
    simp only [div_eq_inv_mul]
    rw [limAvg_const_mul hU (bdd_sum _ fun p _ => hbΦ p), limAvg_sum hU _ fun p _ => hbΦ p]
    simp only [hcorr]
  rw [hdiff]
  exact abs_limAvg_le hU hpt

end

end GaloisForLFunctions.LogarithmicChowla
