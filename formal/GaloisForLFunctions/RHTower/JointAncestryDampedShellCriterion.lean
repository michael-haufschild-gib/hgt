import GaloisForLFunctions.RHTower.JointAncestryShellLoudSetCriterion
import GaloisForLFunctions.RHTower.XiZeroBandFinite

/-!
# A sparse shell criterion for RH with no large-height input

For the shell `(N, 2N]` put `U_ρ(N) = Σ_{N<p≤2N} p^{ρ−3/2}` and damp it by a Mellin multiplier that
decays along vertical lines:

`V_ρ(N) = U_ρ(N)/(ρ+1)²`   (`jasShellDampedSum`),   `D_k(N) = Σ_ρ V_ρ(N)^k/(ρ(1−ρ))`.

**Theorem** (`riemannHypothesis_iff_shellDamped_growth`).

`RH ⟺ ∀ ε > 0, ∃ᶠ N, ∀ k ≥ 1, |D_k(N)| ≤ N^{εk}`.

Neither the zeros approaching the line, nor attainment of the top distance, nor finiteness of loud
sets is assumed: the damping supplies all of it.

**Proof.**
* Every zero has `|U_ρ(N)| ≤ Σ_{N<p≤2N} p^{−1/2} =: S(N)` and `|ρ+1|² ≥ 1 + (Im ρ)²`.  So
  `|V_ρ(N)| > L` forces `(Im ρ)² < S(N)/L`, and the loud set of every shell at every level is finite
  (`finite_loud_jasShellDampedSum`).
* A zero `ρ₁` right of the line has `|U_{ρ₁}(N)| > N^{3δ/4}` on every large shell
  (`eventually_lt_norm_jasShellUniformSum`).  The absorbed Turán bound on the finite loud set above
  `L = |V_{ρ₁}(N)|/2` (`exists_norm_tsum_pow_ge_of_finite_loud`) gives some `k ≥ 1` with
  `|D_k(N)| ≥ 2W L^k > N^{δk/2}`.
* Under RH, `|U_ρ(N)| ≤ Σ 1/p ≤ 1` and `|ρ+1| ≥ 1`, so `|D_k(N)| ≤ W`.

**Reading.**  In the undamped shell power sums the loud zeros need not be finite: high zeros keep
shell values of full size.  The large-height input (ZAL, no chain, or loud-set finiteness) was
needed exactly for this.  Damping inside the `k`-th power makes every high zero quiet, and a free
exponent beats any finite loud set.  The arithmetic side is still explicit:
`D_k(N) = Σ_{p₁…p_k ∈ (N,2N]} (p₁⋯p_k)^{−3/2} 𝓔_{2k}(p₁⋯p_k)`, where `𝓔_{2k}` is the order-`2k`
Riesz mean `∫_0^1 𝓔̃(Xy) (log 1/y)^{2k−1}/(2k−1)! dy` of the explicit-formula error.  So RH is
subexponential growth of these Riesz-smoothed k-fold shell averages along infinitely many shells,
with no side condition.
-/

open Complex Filter
open scoped Topology

namespace RHTower

noncomputable section

/-- The damped shell value `V_s(N) = U_s(N)/(s+1)²`. -/
def jasShellDampedSum (N : ℕ) (s : ℂ) : ℂ := jasShellUniformSum N s / (s + 1) ^ 2

/-- The damped shell power sum `D_k(N) = Σ_ρ V_ρ(N)^k/(ρ(1−ρ))`. -/
def jasShellDampedPowerSum (N k : ℕ) : ℂ :=
  ∑' q : XiZeroCopy, jasShellDampedSum N (q.1 : ℂ) ^ k * (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))))

/-- `S(N) = Σ_{N<p≤2N} p^{−1/2}`. -/
def jasShellHalfMass (N : ℕ) : ℝ :=
  ∑ p ∈ jasPrimeWindow N (2 * N), Real.exp (-(1 / 2) * Real.log p)

theorem jasShellHalfMass_nonneg (N : ℕ) : 0 ≤ jasShellHalfMass N :=
  Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le

theorem norm_jasShellUniformSum_le_halfMass (N : ℕ) (q : XiZeroCopy) :
    ‖jasShellUniformSum N (q.1 : ℂ)‖ ≤ jasShellHalfMass N := by
  refine (norm_jasShellUniformSum_le N (q.1 : ℂ)).trans
    (Finset.sum_le_sum fun p _ => exp_neg_mul_log_prime_anti ?_ p)
  have := xiZeroCopy_re_lt_one q
  linarith

theorem one_add_im_sq_le_normSq_add_one (q : XiZeroCopy) :
    1 + (q.1 : ℂ).im ^ 2 ≤ ‖(q.1 : ℂ) + 1‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  have h0 := xiZeroCopy_re_pos q
  simp only [Complex.add_re, Complex.one_re, Complex.add_im, Complex.one_im, add_zero]
  nlinarith

theorem norm_jasShellDampedSum_le (N : ℕ) (q : XiZeroCopy) :
    ‖jasShellDampedSum N (q.1 : ℂ)‖ ≤ jasShellHalfMass N / (1 + (q.1 : ℂ).im ^ 2) := by
  have h1 := one_add_im_sq_le_normSq_add_one q
  have hpos : 0 < 1 + (q.1 : ℂ).im ^ 2 := by positivity
  rw [jasShellDampedSum, norm_div, norm_pow]
  calc ‖jasShellUniformSum N (q.1 : ℂ)‖ / ‖(q.1 : ℂ) + 1‖ ^ 2
      ≤ jasShellHalfMass N / ‖(q.1 : ℂ) + 1‖ ^ 2 :=
        div_le_div_of_nonneg_right (norm_jasShellUniformSum_le_halfMass N q) (by positivity)
    _ ≤ jasShellHalfMass N / (1 + (q.1 : ℂ).im ^ 2) :=
        div_le_div_of_nonneg_left (jasShellHalfMass_nonneg N) hpos h1

/-- **Every damped loud set is finite.** -/
theorem finite_loud_jasShellDampedSum (N : ℕ) {L : ℝ} (hL : 0 < L) :
    {q : XiZeroCopy | L < ‖jasShellDampedSum N (q.1 : ℂ)‖}.Finite := by
  refine (finite_xiZeroCopy_band 0 (r := √(jasShellHalfMass N / L))
    (Real.sqrt_nonneg _)).subset fun q hq => ?_
  simp only [Set.mem_setOf_eq] at hq ⊢
  rw [sub_zero]
  have h1 := hq.trans_le (norm_jasShellDampedSum_le N q)
  have hpos : 0 < 1 + (q.1 : ℂ).im ^ 2 := by positivity
  rw [lt_div_iff₀ hpos] at h1
  have h2 : (q.1 : ℂ).im ^ 2 ≤ jasShellHalfMass N / L := by
    rw [le_div_iff₀ hL]; nlinarith
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h2

theorem summable_jasShellDampedPowerSum_terms (N k : ℕ) :
    Summable fun q : XiZeroCopy =>
      jasShellDampedSum N (q.1 : ℂ) ^ k * (1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))) := by
  refine Summable.of_norm_bounded (summable_inv_mul_one_sub.norm.mul_left
    (jasShellHalfMass N ^ k)) fun q => ?_
  rw [norm_mul, norm_pow]
  refine mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) ?_ k) (norm_nonneg _)
  refine (norm_jasShellDampedSum_le N q).trans ?_
  exact div_le_self (jasShellHalfMass_nonneg N) (by nlinarith [sq_nonneg (q.1 : ℂ).im])

/-- Under RH every damped shell value has modulus at most `1`. -/
theorem norm_jasShellDampedSum_le_one_of_riemannHypothesis (hRH : RiemannHypothesis) (N : ℕ)
    (q : XiZeroCopy) : ‖jasShellDampedSum N (q.1 : ℂ)‖ ≤ 1 := by
  have h1 := norm_jasShellUniformSum_le_one (N := N)
    (xiZeroCopy_re_eq_half_of_riemannHypothesis hRH q).le
  have h2 := one_add_im_sq_le_normSq_add_one q
  have h3 : 1 ≤ ‖(q.1 : ℂ) + 1‖ ^ 2 := by nlinarith [sq_nonneg (q.1 : ℂ).im]
  rw [jasShellDampedSum, norm_div, norm_pow, div_le_one (by positivity)]
  linarith

/-- **RH ⟺ subexponential growth of the damped shell power sums on infinitely many shells.** -/
theorem riemannHypothesis_iff_shellDamped_growth :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε →
      ∃ᶠ N : ℕ in atTop, ∀ k : ℕ, 1 ≤ k → ‖jasShellDampedPowerSum N k‖ ≤ (N : ℝ) ^ (ε * k) := by
  obtain ⟨W, hW⟩ : ∃ W : ℝ, W = ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
    ⟨_, rfl⟩
  constructor
  · intro hRH ε hε
    have hlim : Tendsto (fun N : ℕ => (N : ℝ) ^ ε) atTop atTop :=
      (tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop
    refine ((hlim.eventually (eventually_ge_atTop W)).and (eventually_ge_atTop 1)).frequently.mono
      fun N ⟨hN, hN1⟩ k hk => ?_
    have hbound : ‖jasShellDampedPowerSum N k‖ ≤ W := by
      rw [jasShellDampedPowerSum, hW]
      refine (norm_tsum_le_tsum_norm (summable_jasShellDampedPowerSum_terms N k).norm).trans ?_
      refine Summable.tsum_le_tsum (fun q => ?_) (summable_jasShellDampedPowerSum_terms N k).norm
        summable_inv_mul_one_sub.norm
      rw [norm_mul, norm_pow]
      exact mul_le_of_le_one_left (norm_nonneg _)
        (pow_le_one₀ (norm_nonneg _) (norm_jasShellDampedSum_le_one_of_riemannHypothesis hRH N q))
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    have : (1 : ℝ) ≤ k := by exact_mod_cast hk
    exact hbound.trans (hN.trans (Real.rpow_le_rpow_of_exponent_le hN1' (by nlinarith)))
  · intro hfr
    by_contra hRH
    obtain ⟨q₁, hq₁⟩ := exists_xiZeroCopy_re_gt_half_of_not_riemannHypothesis hRH
    obtain ⟨δ, hδ⟩ : ∃ δ : ℝ, δ = (q₁.1 : ℂ).re - 1 / 2 := ⟨_, rfl⟩
    have hδ0 : 0 < δ := by rw [hδ]; linarith
    have hW0 : 0 < W := hW ▸ Summable.tsum_pos summable_inv_mul_one_sub.norm
      (fun _ => norm_nonneg _) q₁ (norm_pos_iff.mpr (inv_mul_one_sub_ne_zero q₁))
    obtain ⟨c, hc⟩ : ∃ c : ℝ, c = ‖((q₁.1 : ℂ) + 1) ^ 2‖ := ⟨_, rfl⟩
    have hc0 : 0 < c := by
      rw [hc]; refine norm_pos_iff.mpr (pow_ne_zero 2 fun h => ?_)
      have := xiZeroCopy_re_pos q₁
      have h' : ((q₁.1 : ℂ) + 1).re = 0 := by rw [h]; simp
      simp only [Complex.add_re, Complex.one_re] at h'
      linarith
    obtain ⟨b₀, hb₀⟩ : ∃ b₀ : ℝ, b₀ = 2 * c * max 1 (1 / (2 * W)) := ⟨_, rfl⟩
    have hgrow : Tendsto (fun N : ℕ => (N : ℝ) ^ (δ / 4)) atTop atTop :=
      (tendsto_rpow_atTop (by linarith)).comp tendsto_natCast_atTop_atTop
    have hev := (eventually_lt_norm_jasShellUniformSum q₁ (ε := 3 * δ / 4) (by linarith)
      (by rw [← hδ]; linarith)).and ((hgrow.eventually (eventually_gt_atTop b₀)).and
        (eventually_ge_atTop 1))
    obtain ⟨N, hN, hloudN, hbig, hN1⟩ := ((hfr (δ / 2) (by linarith)).and_eventually hev).exists
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
    have hN1' : (1 : ℝ) ≤ N := by exact_mod_cast hN1
    -- the damped value of `q₁`
    obtain ⟨V, hV⟩ : ∃ V : ℝ, V = ‖jasShellDampedSum N (q₁.1 : ℂ)‖ := ⟨_, rfl⟩
    have hVeq : V = ‖jasShellUniformSum N (q₁.1 : ℂ)‖ / c := by
      rw [hV, jasShellDampedSum, norm_div, hc]
    have hpowpos : 0 < (N : ℝ) ^ (3 * δ / 4) := Real.rpow_pos_of_pos hNpos _
    have hVlow : (N : ℝ) ^ (3 * δ / 4) / c < V := by
      rw [hVeq]; exact div_lt_div_of_pos_right hloudN hc0
    have hV0 : 0 < V := lt_of_le_of_lt (by positivity) hVlow
    obtain ⟨ν, hν0, hν⟩ := exists_norm_tsum_pow_ge_of_finite_loud
      (fun q => jasShellDampedSum N (q.1 : ℂ)) (summable_jasShellDampedPowerSum_terms N)
      (L := V / 2) (by positivity) (finite_loud_jasShellDampedSum N (by positivity))
      ⟨q₁, by rw [← hV]; linarith⟩ 0
    have hν1 : 1 ≤ ν := hν0
    rw [← hW] at hν
    have hA := hN ν hν1
    have hνr : (1 : ℝ) ≤ ν := by exact_mod_cast hν1
    -- `2W (V/2)^ν > N^{δν/2}`
    have hbase : max 1 (1 / (2 * W)) < (N : ℝ) ^ (δ / 4) / (2 * c) := by
      rw [lt_div_iff₀ (by positivity)]
      have : 2 * c * max 1 (1 / (2 * W)) < (N : ℝ) ^ (δ / 4) := by rw [← hb₀]; exact hbig
      linarith
    have hbase1 : 1 ≤ (N : ℝ) ^ (δ / 4) / (2 * c) := (le_max_left _ _).trans hbase.le
    have hsplit : (N : ℝ) ^ (3 * δ / 4) = (N : ℝ) ^ (δ / 4) * (N : ℝ) ^ (δ / 2) := by
      rw [← Real.rpow_add hNpos]; ring_nf
    have hhalf : (N : ℝ) ^ (δ / 4) / (2 * c) * (N : ℝ) ^ (δ / 2) < V / 2 := by
      have e : (N : ℝ) ^ (δ / 4) / (2 * c) * (N : ℝ) ^ (δ / 2) = (N : ℝ) ^ (3 * δ / 4) / c / 2 := by
        rw [hsplit]; field_simp
      rw [e]; linarith
    have hpow2 : ((N : ℝ) ^ (δ / 4) / (2 * c)) ^ ν * ((N : ℝ) ^ (δ / 2)) ^ ν < (V / 2) ^ ν := by
      rw [← mul_pow]
      exact pow_lt_pow_left₀ hhalf (by positivity) (by omega)
    have hgeb : (N : ℝ) ^ (δ / 4) / (2 * c) ≤ ((N : ℝ) ^ (δ / 4) / (2 * c)) ^ ν :=
      le_self_pow₀ hbase1 (by omega)
    have hW2 : 1 < 2 * W * ((N : ℝ) ^ (δ / 4) / (2 * c)) := by
      have h1 : 1 / (2 * W) < (N : ℝ) ^ (δ / 4) / (2 * c) := (le_max_right _ _).trans_lt hbase
      rw [div_lt_iff₀ (by positivity)] at h1
      linarith
    have hrpow : (N : ℝ) ^ (δ / 2 * ν) = ((N : ℝ) ^ (δ / 2)) ^ ν := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
    have hlt : (N : ℝ) ^ (δ / 2 * ν) < 2 * W * (V / 2) ^ ν := by
      rw [hrpow]
      have hp : 0 < ((N : ℝ) ^ (δ / 2)) ^ ν := by positivity
      calc ((N : ℝ) ^ (δ / 2)) ^ ν < 2 * W * ((N : ℝ) ^ (δ / 4) / (2 * c)) *
            ((N : ℝ) ^ (δ / 2)) ^ ν := by nlinarith
        _ ≤ 2 * W * (((N : ℝ) ^ (δ / 4) / (2 * c)) ^ ν * ((N : ℝ) ^ (δ / 2)) ^ ν) := by
            have := mul_le_mul_of_nonneg_right hgeb hp.le
            nlinarith
        _ ≤ 2 * W * (V / 2) ^ ν := by nlinarith
    have hA' : ‖jasShellDampedPowerSum N ν‖ ≤ (N : ℝ) ^ (δ / 2 * ν) := hA
    have hν' : 2 * W * (V / 2) ^ ν ≤ ‖jasShellDampedPowerSum N ν‖ := hν
    linarith

end

end RHTower
