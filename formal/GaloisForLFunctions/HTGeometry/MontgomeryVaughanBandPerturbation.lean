import GaloisForLFunctions.HTGeometry.MontgomeryVaughanIntervalMeanSquare

/-!
# Montgomery–Vaughan lower bound with slowly varying exponential amplitudes

For a `D`-separated exponential sum whose coefficients carry factors `e^{θ_r α}` with
`0 ≤ θ_r ≤ τ ≤ 1` (a band of real parts of width `τ/log T` in the pair-form application), the
interval mean square is bounded below by the constant-coefficient Montgomery–Vaughan bound minus
an explicit perturbation: a finite Taylor expansion of `e^{θα}` to order `K` produces `K − 1`
constant-coefficient sums, each controlled by the Montgomery–Vaughan upper bound, and a remainder
controlled pointwise through `Real.exp_bound` and Cauchy–Schwarz.
-/

open Complex MeasureTheory intervalIntegral
open scoped BigOperators ComplexConjugate

namespace GaloisForLFunctions.HTGeometry

noncomputable section

attribute [fun_prop] continuous_mvExp

/-- The band sum `Σ_r d_r e^{θ_r α} e^{2πi u_r α}`. -/
def mvBandSum {ι : Type} [Fintype ι] (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ) (α : ℝ) : ℂ :=
  ∑ r, d r * ((Real.exp (θ r * α) : ℝ) : ℂ) * mvExp (u r) α

/-- The `m`-th Taylor layer `Σ_r d_r θ_r^m e^{2πi u_r α}` (constant coefficients). -/
def mvPowerSum {ι : Type} [Fintype ι] (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ) (m : ℕ) (α : ℝ) : ℂ :=
  ∑ r, (d r * ((θ r ^ m : ℝ) : ℂ)) * mvExp (u r) α

/-- The Taylor remainder of order `K` of `e^{x}` at `x`. -/
def expTaylorRem (K : ℕ) (x : ℝ) : ℝ :=
  Real.exp x - ∑ m ∈ Finset.range K, x ^ m / (m.factorial : ℝ)

/-- The remainder sum `Σ_r d_r rem_K(θ_r α) e^{2πi u_r α}`. -/
def mvRemSum {ι : Type} [Fintype ι] (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ) (K : ℕ) (α : ℝ) : ℂ :=
  ∑ r, d r * ((expTaylorRem K (θ r * α) : ℝ) : ℂ) * mvExp (u r) α

theorem expTaylorRem_abs_le {K : ℕ} (hK : 0 < K) {x : ℝ} (hx : |x| ≤ 1) :
    |expTaylorRem K x| ≤ |x| ^ K * ((K.succ : ℝ) / ((K.factorial : ℝ) * K)) :=
  Real.exp_bound hx hK

/-- Taylor decomposition of the band sum. -/
theorem mvBandSum_eq {ι : Type} [Fintype ι] (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ) {K : ℕ}
    (hK : 1 ≤ K) (α : ℝ) :
    mvBandSum u d θ α = mvPowerSum u d θ 0 α +
      (∑ m ∈ Finset.Ico 1 K, ((α ^ m / (m.factorial : ℝ) : ℝ) : ℂ) * mvPowerSum u d θ m α) +
        mvRemSum u d θ K α := by
  have hexp : ∀ r, ((Real.exp (θ r * α) : ℝ) : ℂ) =
      ∑ m ∈ Finset.range K, ((α ^ m / (m.factorial : ℝ) : ℝ) : ℂ) * ((θ r ^ m : ℝ) : ℂ) +
        ((expTaylorRem K (θ r * α) : ℝ) : ℂ) := by
    intro r
    unfold expTaylorRem
    push_cast
    have : ∀ m : ℕ, ((α : ℂ) ^ m / (m.factorial : ℂ)) * ((θ r : ℂ) ^ m) =
        ((θ r : ℂ) * (α : ℂ)) ^ m / (m.factorial : ℂ) := by
      intro m
      rw [mul_pow]
      ring
    simp_rw [this]
    ring
  have hrange : ∀ f : ℕ → ℂ, ∑ m ∈ Finset.range K, f m = f 0 + ∑ m ∈ Finset.Ico 1 K, f m := by
    intro f
    rw [Finset.range_eq_Ico, Finset.sum_eq_sum_Ico_succ_bot hK]
  unfold mvBandSum mvPowerSum mvRemSum
  simp_rw [hexp]
  set c : ℕ → ℂ := fun m => ((α ^ m / (m.factorial : ℝ) : ℝ) : ℂ) with hc
  set t : ι → ℕ → ℂ := fun r m => ((θ r ^ m : ℝ) : ℂ) with ht
  set e : ι → ℂ := fun r => ((expTaylorRem K (θ r * α) : ℝ) : ℂ) with he
  set E : ι → ℂ := fun r => mvExp (u r) α with hE
  have h0 : c 0 = 1 := by simp [hc]
  calc ∑ x, d x * (∑ m ∈ Finset.range K, c m * t x m + e x) * E x
      = ∑ x, (∑ m ∈ Finset.range K, c m * (d x * t x m * E x) + d x * e x * E x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
          congr 1
          refine Finset.sum_congr rfl fun m _ => ?_
          ring
    _ = ∑ m ∈ Finset.range K, c m * ∑ x, d x * t x m * E x + ∑ x, d x * e x * E x := by
          rw [Finset.sum_add_distrib, Finset.sum_comm]
          congr 1
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [Finset.mul_sum]
    _ = _ := by
          rw [hrange (fun m => c m * ∑ x, d x * t x m * E x), h0, one_mul]

/-- The Taylor remainder sum is pointwise at most `ρ_K Σ_r ‖d_r‖` on `[0,1]`, with
`ρ_K = τ^K (K+1)/(K! K)`. -/
theorem norm_mvRemSum_le {ι : Type} [Fintype ι] (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ)
    {τ : ℝ} (hτ1 : τ ≤ 1) (hθ : ∀ r, |θ r| ≤ τ) {K : ℕ} (hK : 1 ≤ K)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ‖mvRemSum u d θ K α‖ ≤
      τ ^ K * ((K.succ : ℝ) / ((K.factorial : ℝ) * K)) * ∑ r, ‖d r‖ := by
  unfold mvRemSum
  refine (norm_sum_le _ _).trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [norm_mul, norm_mul, norm_mvExp, mul_one, Complex.norm_real, Real.norm_eq_abs]
  have hθr := hθ r
  have hτ0' : 0 ≤ τ := le_trans (abs_nonneg _) hθr
  have hxτ : |θ r * α| ≤ τ := by
    rw [abs_mul, abs_of_nonneg hα0]
    calc |θ r| * α ≤ τ * 1 := mul_le_mul hθr hα1 hα0 hτ0'
      _ = τ := mul_one _
  have hx1 : |θ r * α| ≤ 1 := hxτ.trans hτ1
  have hrem := expTaylorRem_abs_le (by omega : 0 < K) hx1
  have hpow : |θ r * α| ^ K ≤ τ ^ K := pow_le_pow_left₀ (abs_nonneg _) hxτ K
  have hfac : 0 ≤ (K.succ : ℝ) / ((K.factorial : ℝ) * K) :=
    div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
  calc ‖d r‖ * |expTaylorRem K (θ r * α)|
      ≤ ‖d r‖ * (|θ r * α| ^ K * ((K.succ : ℝ) / ((K.factorial : ℝ) * K))) :=
        mul_le_mul_of_nonneg_left hrem (norm_nonneg _)
    _ ≤ ‖d r‖ * (τ ^ K * ((K.succ : ℝ) / ((K.factorial : ℝ) * K))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hfac) (norm_nonneg _)
    _ = _ := by ring

/-- Squared form: `‖Rem‖² ≤ ρ_K² · N · Σ‖d_r‖²`. -/
theorem normSq_mvRemSum_le {ι : Type} [Fintype ι] (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ)
    {τ : ℝ} (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1) (hθ : ∀ r, |θ r| ≤ τ) {K : ℕ} (hK : 1 ≤ K)
    {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ‖mvRemSum u d θ K α‖ ^ (2 : ℕ) ≤
      (τ ^ K * ((K.succ : ℝ) / ((K.factorial : ℝ) * K))) ^ (2 : ℕ) *
        ((Fintype.card ι : ℝ) * ∑ r, ‖d r‖ ^ (2 : ℕ)) := by
  have h1 := norm_mvRemSum_le u d θ hτ1 hθ hK hα0 hα1
  have h2 : (∑ r, ‖d r‖) ^ (2 : ℕ) ≤ (Fintype.card ι : ℝ) * ∑ r, ‖d r‖ ^ (2 : ℕ) := by
    have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset ι)) (f := fun r => ‖d r‖)
    simpa using this
  have hρ : 0 ≤ τ ^ K * ((K.succ : ℝ) / ((K.factorial : ℝ) * K)) :=
    mul_nonneg (pow_nonneg hτ0 K)
      (div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  have hsum0 : 0 ≤ ∑ r, ‖d r‖ := Finset.sum_nonneg fun r _ => norm_nonneg _
  calc ‖mvRemSum u d θ K α‖ ^ (2 : ℕ)
      ≤ (τ ^ K * ((K.succ : ℝ) / ((K.factorial : ℝ) * K)) * ∑ r, ‖d r‖) ^ (2 : ℕ) :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ = (τ ^ K * ((K.succ : ℝ) / ((K.factorial : ℝ) * K))) ^ (2 : ℕ) * (∑ r, ‖d r‖) ^ (2 : ℕ) := by ring
    _ ≤ _ := by gcongr

/-- Each Taylor layer obeys the Montgomery–Vaughan upper bound with the coefficient budget
`τ^{2m} Σ‖d_r‖²`. -/
theorem integral_normSq_mvPowerSum_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ) {D a ℓ τ : ℝ} (hD : 0 < D) (hℓ : 0 ≤ ℓ)
    (hθ : ∀ r, |θ r| ≤ τ)
    (hsep : ∀ r s, r ≠ s → D ≤ |u r - u s|) (m : ℕ) :
    (∫ α in a..a + ℓ, ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ)) ≤
      (ℓ + 26 / (Real.pi * D)) * (τ ^ (2 * m) * ∑ r, ‖d r‖ ^ (2 : ℕ)) := by
  have h := interval_integral_normSq_expSum_le u (fun r => d r * ((θ r ^ m : ℝ) : ℂ))
    (a := a) (ℓ := ℓ) hD hsep
  have hcoef : ∑ r, ‖d r * ((θ r ^ m : ℝ) : ℂ)‖ ^ (2 : ℕ) ≤ τ ^ (2 * m) * ∑ r, ‖d r‖ ^ (2 : ℕ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun r _ => ?_
    have hθr := hθ r
    have hsq : θ r ^ (2 : ℕ) ≤ τ ^ (2 : ℕ) := sq_le_sq' (abs_le.mp hθr).1 (abs_le.mp hθr).2
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs, ← pow_mul, mul_comm m 2]
    have : (θ r) ^ (2 * m) ≤ τ ^ (2 * m) := by
      rw [pow_mul, pow_mul]
      exact pow_le_pow_left₀ (sq_nonneg _) hsq m
    calc ‖d r‖ ^ (2 : ℕ) * θ r ^ (2 * m) ≤ ‖d r‖ ^ (2 : ℕ) * τ ^ (2 * m) := by gcongr
      _ = _ := by ring
  unfold mvPowerSum
  refine h.trans ?_
  have hℓc : 0 ≤ ℓ + 26 / (Real.pi * D) := add_nonneg hℓ (by positivity)
  exact mul_le_mul_of_nonneg_left hcoef hℓc

/-- `2^{m-1} ≤ m!` for `m ≥ 1`. -/
theorem two_pow_pred_le_factorial : ∀ m : ℕ, 1 ≤ m → 2 ^ (m - 1) ≤ m.factorial := by
  intro m hm
  induction m with
  | zero => omega
  | succ n ih =>
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have h := ih hn
      rw [Nat.factorial_succ]
      have : n + 1 - 1 = (n - 1) + 1 := by omega
      rw [this, pow_succ]
      calc 2 ^ (n - 1) * 2 ≤ n.factorial * 2 := by gcongr
        _ ≤ n.factorial * (n + 1) := by gcongr; omega
        _ = (n + 1) * n.factorial := by ring

/-- `Σ_{1 ≤ m < K} 1/m! ≤ 2`. -/
theorem sum_Ico_inv_factorial_le_two (K : ℕ) :
    ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) ≤ 2 := by
  calc ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ))
      ≤ ∑ m ∈ Finset.Ico 1 K, (1 / 2 : ℝ) ^ (m - 1) := by
        refine Finset.sum_le_sum fun m hm => ?_
        have hm1 : 1 ≤ m := (Finset.mem_Ico.mp hm).1
        have h := two_pow_pred_le_factorial m hm1
        have h' : (2 : ℝ) ^ (m - 1) ≤ (m.factorial : ℝ) := by exact_mod_cast h
        rw [one_div_pow]
        exact one_div_le_one_div_of_le (by positivity) h'
    _ = ∑ i ∈ Finset.range (K - 1), (1 / 2 : ℝ) ^ i := by
        rw [Finset.sum_Ico_eq_sum_range]
        refine Finset.sum_congr rfl fun i _ => ?_
        congr 1
        omega
    _ ≤ 2 := sum_geometric_two_le _

/-- Weighted Cauchy–Schwarz: `(Σ w_m x_m)² ≤ (Σ w_m)(Σ w_m x_m²)` for `w ≥ 0`. -/
theorem sq_sum_weighted_le {ι : Type*} (s : Finset ι) (w x : ι → ℝ) (hw : ∀ m ∈ s, 0 ≤ w m) :
    (∑ m ∈ s, w m * x m) ^ (2 : ℕ) ≤ (∑ m ∈ s, w m) * ∑ m ∈ s, w m * x m ^ (2 : ℕ) := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq s (fun m => Real.sqrt (w m))
    (fun m => Real.sqrt (w m) * x m)
  have h1 : ∑ m ∈ s, Real.sqrt (w m) * (Real.sqrt (w m) * x m) = ∑ m ∈ s, w m * x m := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [← mul_assoc, Real.mul_self_sqrt (hw m hm)]
  have h2 : ∑ m ∈ s, Real.sqrt (w m) ^ (2 : ℕ) = ∑ m ∈ s, w m := by
    refine Finset.sum_congr rfl fun m hm => ?_
    exact Real.sq_sqrt (hw m hm)
  have h3 : ∑ m ∈ s, (Real.sqrt (w m) * x m) ^ (2 : ℕ) = ∑ m ∈ s, w m * x m ^ (2 : ℕ) := by
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [mul_pow, Real.sq_sqrt (hw m hm)]
  rw [h1, h2, h3] at h
  exact h

/-- **Montgomery–Vaughan lower bound with slowly varying amplitudes.**  For `0 ≤ θ_r ≤ τ ≤ 1`,
a window `[a, a+ℓ] ⊆ [0, 1]`, `D`-separated frequencies and any Taylor order `K ≥ 1`,
`∫ ‖Σ_r d_r e^{θ_r α} e(u_r α)‖² ≥ (½(ℓ − 26/(πD)) − 2K(ℓ + 26/(πD)) Σ_{1≤m<K} (τ^m/m!)² − 2ℓ N ρ_K²) Σ‖d_r‖²`
with `ρ_K = τ^K (K+1)/(K! K)` and `N` the number of frequencies. -/
theorem interval_integral_normSq_mvBandSum_ge {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ) {D a ℓ τ : ℝ} (hD : 0 < D) (hℓ : 0 ≤ ℓ)
    (ha : 0 ≤ a) (hab : a + ℓ ≤ 1) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hθ : ∀ r, |θ r| ≤ τ) (hsep : ∀ r s, r ≠ s → D ≤ |u r - u s|)
    {K : ℕ} (hK : 1 ≤ K) :
    (1 / 2 * (ℓ - 26 / (Real.pi * D))
        - 4 * (ℓ + 26 / (Real.pi * D)) * ∑ m ∈ Finset.Ico 1 K, τ ^ (2 * m) / (m.factorial : ℝ)
        - 2 * ℓ * (Fintype.card ι : ℝ) * (τ ^ K * ((K.succ : ℝ) / ((K.factorial : ℝ) * K))) ^ (2 : ℕ))
      * ∑ r, ‖d r‖ ^ (2 : ℕ)
      ≤ ∫ α in a..a + ℓ, ‖mvBandSum u d θ α‖ ^ (2 : ℕ) := by
  classical
  set b := a + ℓ with hb
  set Sd : ℝ := ∑ r, ‖d r‖ ^ (2 : ℕ) with hSd
  set c : ℝ := 26 / (Real.pi * D) with hc
  set ρ : ℝ := τ ^ K * ((K.succ : ℝ) / ((K.factorial : ℝ) * K)) with hρ
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hSd0 : 0 ≤ Sd := Finset.sum_nonneg fun r _ => by positivity
  have hc0 : 0 ≤ c := by positivity
  have hρ0 : 0 ≤ ρ := by
    rw [hρ]
    exact mul_nonneg (pow_nonneg hτ0 K)
      (div_nonneg (Nat.cast_nonneg _) (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)))
  clear_value Sd c ρ N
  have hab' : a ≤ b := by rw [hb]; linarith
  -- the pieces
  set P : ℝ → ℂ := fun α => mvPowerSum u d θ 0 α with hP
  set Q : ℝ → ℂ := fun α =>
    ∑ m ∈ Finset.Ico 1 K, ((α ^ m / (m.factorial : ℝ) : ℝ) : ℂ) * mvPowerSum u d θ m α with hQ
  set Rm : ℝ → ℂ := fun α => mvRemSum u d θ K α with hRm
  have hdecomp : ∀ α, mvBandSum u d θ α = P α + Q α + Rm α := fun α => mvBandSum_eq u d θ hK α
  -- continuity
  have hcontP : Continuous P := by
    simp only [hP]; unfold mvPowerSum; fun_prop
  have hcontPm : ∀ m, Continuous (fun α => mvPowerSum u d θ m α) := by
    intro m; unfold mvPowerSum; fun_prop
  have hcontQ : Continuous Q := by
    simp only [hQ]
    refine continuous_finsetSum _ fun m _ => ?_
    exact (Complex.continuous_ofReal.comp (by fun_prop)).mul (hcontPm m)
  have hcontRm : Continuous Rm := by
    simp only [hRm]; unfold mvRemSum expTaylorRem; fun_prop
  have hcontB : Continuous (mvBandSum u d θ) := by
    unfold mvBandSum; fun_prop
  -- pointwise bounds on the window
  have hpt : ∀ α ∈ Set.Icc a b,
      1 / 2 * ‖P α‖ ^ (2 : ℕ)
        - (4 * ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) * ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ)
            + 2 * (ρ ^ (2 : ℕ) * (N * Sd)))
        ≤ ‖mvBandSum u d θ α‖ ^ (2 : ℕ) := by
    intro α hα
    have hα0 : 0 ≤ α := le_trans ha hα.1
    have hα1 : α ≤ 1 := le_trans hα.2 hab
    -- `‖P‖ ≤ ‖B‖ + ‖Q + Rm‖`
    have hPB : ‖P α‖ ≤ ‖mvBandSum u d θ α‖ + ‖Q α + Rm α‖ := by
      have : P α = mvBandSum u d θ α - (Q α + Rm α) := by rw [hdecomp]; ring
      rw [this]
      exact norm_sub_le _ _
    -- `‖Q‖ ≤ X`, `X := Σ (1/m!) ‖P_m‖`
    set X : ℝ := ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) * ‖mvPowerSum u d θ m α‖ with hX
    have hQX : ‖Q α‖ ≤ X := by
      simp only [hQ]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hαm : |α ^ m / (m.factorial : ℝ)| ≤ 1 / (m.factorial : ℝ) := by
        rw [abs_of_nonneg (by positivity)]
        have : α ^ m ≤ 1 := pow_le_one₀ hα0 hα1
        gcongr
      exact mul_le_mul_of_nonneg_right hαm (norm_nonneg _)
    have hX2 : X ^ (2 : ℕ) ≤ 2 * ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) * ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ) := by
      have h := sq_sum_weighted_le (Finset.Ico 1 K) (fun m => 1 / (m.factorial : ℝ))
        (fun m => ‖mvPowerSum u d θ m α‖) (fun m _ => by positivity)
      have hw := sum_Ico_inv_factorial_le_two K
      have hsum0 : 0 ≤ ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) * ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ) :=
        Finset.sum_nonneg fun m _ => by positivity
      calc X ^ (2 : ℕ) ≤ (∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ))) *
            ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) * ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ) := h
        _ ≤ 2 * ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) * ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ) :=
            mul_le_mul_of_nonneg_right hw hsum0
    have hRm2 : ‖Rm α‖ ^ (2 : ℕ) ≤ ρ ^ (2 : ℕ) * (N * Sd) := by
      rw [hρ, hN, hSd]
      exact normSq_mvRemSum_le u d θ hτ0 hτ1 hθ hK hα0 hα1
    have hQR : ‖Q α + Rm α‖ ^ (2 : ℕ) ≤ 2 * X ^ (2 : ℕ) + 2 * ‖Rm α‖ ^ (2 : ℕ) := by
      have h1 : ‖Q α + Rm α‖ ≤ X + ‖Rm α‖ := (norm_add_le _ _).trans (by linarith)
      have h0 : 0 ≤ ‖Q α + Rm α‖ := norm_nonneg _
      nlinarith [sq_nonneg (X - ‖Rm α‖), norm_nonneg (Rm α), norm_nonneg (Q α)]
    have hPsq : ‖P α‖ ^ (2 : ℕ) ≤ 2 * ‖mvBandSum u d θ α‖ ^ (2 : ℕ) + 2 * ‖Q α + Rm α‖ ^ (2 : ℕ) := by
      have h0 : 0 ≤ ‖P α‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖mvBandSum u d θ α‖ - ‖Q α + Rm α‖), norm_nonneg (mvBandSum u d θ α),
        norm_nonneg (Q α + Rm α)]
    nlinarith [hX2, hRm2, hQR, hPsq]
  -- integrate the pointwise bound
  have hint1 : IntervalIntegrable (fun α => 1 / 2 * ‖P α‖ ^ (2 : ℕ)
      - (4 * ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) * ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ)
          + 2 * (ρ ^ (2 : ℕ) * (N * Sd)))) volume a b := by
    apply Continuous.intervalIntegrable
    refine (continuous_const.mul (hcontP.norm.pow 2)).sub (Continuous.add ?_ continuous_const)
    refine continuous_const.mul (continuous_finsetSum _ fun m _ => ?_)
    exact continuous_const.mul ((hcontPm m).norm.pow 2)
  have hint2 : IntervalIntegrable (fun α => ‖mvBandSum u d θ α‖ ^ (2 : ℕ)) volume a b :=
    (hcontB.norm.pow 2).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on hab' hint1 hint2 hpt
  -- evaluate the left-hand integral
  have hintP : IntervalIntegrable (fun α => ‖P α‖ ^ (2 : ℕ)) volume a b :=
    (hcontP.norm.pow 2).intervalIntegrable _ _
  have hintS : IntervalIntegrable (fun α =>
      ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) * ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ)) volume a b := by
    apply Continuous.intervalIntegrable
    exact continuous_finsetSum _ fun m _ => continuous_const.mul ((hcontPm m).norm.pow 2)
  have hsplit : (∫ α in a..b, (1 / 2 * ‖P α‖ ^ (2 : ℕ)
      - (4 * ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) * ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ)
          + 2 * (ρ ^ (2 : ℕ) * (N * Sd)))))
      = 1 / 2 * (∫ α in a..b, ‖P α‖ ^ (2 : ℕ))
        - (4 * ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) *
            (∫ α in a..b, ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ))
          + 2 * (ρ ^ (2 : ℕ) * (N * Sd)) * ℓ) := by
    rw [intervalIntegral.integral_sub (hintP.const_mul _)
      ((hintS.const_mul _).add intervalIntegrable_const),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hintS.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      intervalIntegral.integral_finsetSum]
    · simp only [smul_eq_mul, hb]
      have : ∀ m ∈ Finset.Ico 1 K,
          (∫ α in a..a + ℓ, (1 / (m.factorial : ℝ)) * ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ))
            = (1 / (m.factorial : ℝ)) * ∫ α in a..a + ℓ, ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ) := by
        intro m _
        rw [intervalIntegral.integral_const_mul]
      rw [Finset.sum_congr rfl this]
      ring
    · intro m _
      exact (continuous_const.mul ((hcontPm m).norm.pow 2)).intervalIntegrable _ _
  rw [hsplit] at hmono
  -- the constant-coefficient lower bound and the layer upper bounds
  have hPlow : (ℓ - c) * Sd ≤ ∫ α in a..b, ‖P α‖ ^ (2 : ℕ) := by
    have h := interval_integral_normSq_expSum_ge u (fun r => d r * ((θ r ^ (0 : ℕ) : ℝ) : ℂ))
      (a := a) (ℓ := ℓ) hD hsep
    have hcoef : ∑ r, ‖d r * ((θ r ^ (0 : ℕ) : ℝ) : ℂ)‖ ^ (2 : ℕ) = Sd := by
      rw [hSd]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp
    rw [hcoef] at h
    simpa only [hP, mvPowerSum, hb, hc] using h
  have hlayer : ∀ m ∈ Finset.Ico 1 K,
      (∫ α in a..b, ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ)) ≤ (ℓ + c) * (τ ^ (2 * m) * Sd) := by
    intro m _
    rw [hb, hc, hSd]
    exact integral_normSq_mvPowerSum_le u d θ (a := a) hD hℓ hθ hsep m
  have hsumbound : ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) *
        (∫ α in a..b, ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ))
      ≤ ∑ m ∈ Finset.Ico 1 K, (ℓ + c) * (τ ^ (2 * m) / (m.factorial : ℝ)) * Sd := by
    refine Finset.sum_le_sum fun m hm => ?_
    have := hlayer m hm
    calc (1 / (m.factorial : ℝ)) * (∫ α in a..b, ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ))
        ≤ (1 / (m.factorial : ℝ)) * ((ℓ + c) * (τ ^ (2 * m) * Sd)) := by gcongr
      _ = (ℓ + c) * (τ ^ (2 * m) / (m.factorial : ℝ)) * Sd := by ring
  have hsum_eq : ∑ m ∈ Finset.Ico 1 K, (ℓ + c) * (τ ^ (2 * m) / (m.factorial : ℝ)) * Sd
      = (ℓ + c) * (∑ m ∈ Finset.Ico 1 K, τ ^ (2 * m) / (m.factorial : ℝ)) * Sd := by
    rw [Finset.mul_sum, Finset.sum_mul]
  have hprod : 4 * ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) *
        (∫ α in a..b, ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ))
      ≤ 4 * ((ℓ + c) * (∑ m ∈ Finset.Ico 1 K, τ ^ (2 * m) / (m.factorial : ℝ)) * Sd) := by
    rw [← hsum_eq]
    exact mul_le_mul_of_nonneg_left hsumbound (by norm_num)
  have hhalf : 1 / 2 * ((ℓ - c) * Sd) ≤ 1 / 2 * ∫ α in a..b, ‖P α‖ ^ (2 : ℕ) :=
    mul_le_mul_of_nonneg_left hPlow (by norm_num)
  rw [hb] at hmono hprod hhalf
  linarith [hmono, hprod, hhalf]

/-- **Montgomery–Vaughan upper bound with slowly varying amplitudes.**  Same hypotheses as the
lower bound; the interval mean square is at most
`(2(ℓ + 26/(πD)) + 8(ℓ + 26/(πD)) Σ_{1≤m<K} τ^{2m}/m! + 4ℓ N ρ_K²) Σ‖d_r‖²`. -/
theorem interval_integral_normSq_mvBandSum_le {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ) {D a ℓ τ : ℝ} (hD : 0 < D) (hℓ : 0 ≤ ℓ)
    (ha : 0 ≤ a) (hab : a + ℓ ≤ 1) (hτ0 : 0 ≤ τ) (hτ1 : τ ≤ 1)
    (hθ : ∀ r, |θ r| ≤ τ) (hsep : ∀ r s, r ≠ s → D ≤ |u r - u s|)
    {K : ℕ} (hK : 1 ≤ K) :
    (∫ α in a..a + ℓ, ‖mvBandSum u d θ α‖ ^ (2 : ℕ)) ≤
      (2 * (ℓ + 26 / (Real.pi * D))
        + 8 * (ℓ + 26 / (Real.pi * D)) * ∑ m ∈ Finset.Ico 1 K, τ ^ (2 * m) / (m.factorial : ℝ)
        + 4 * ℓ * (Fintype.card ι : ℝ) * (τ ^ K * ((K.succ : ℝ) / ((K.factorial : ℝ) * K))) ^ (2 : ℕ))
      * ∑ r, ‖d r‖ ^ (2 : ℕ) := by
  classical
  set b := a + ℓ with hb
  set Sd : ℝ := ∑ r, ‖d r‖ ^ (2 : ℕ) with hSd
  set c : ℝ := 26 / (Real.pi * D) with hc
  set ρ : ℝ := τ ^ K * ((K.succ : ℝ) / ((K.factorial : ℝ) * K)) with hρ
  set N : ℝ := (Fintype.card ι : ℝ) with hN
  have hSd0 : 0 ≤ Sd := Finset.sum_nonneg fun r _ => by positivity
  have hc0 : 0 ≤ c := by positivity
  clear_value Sd c ρ N
  have hab' : a ≤ b := by rw [hb]; linarith
  set P : ℝ → ℂ := fun α => mvPowerSum u d θ 0 α with hP
  set Q : ℝ → ℂ := fun α =>
    ∑ m ∈ Finset.Ico 1 K, ((α ^ m / (m.factorial : ℝ) : ℝ) : ℂ) * mvPowerSum u d θ m α with hQ
  set Rm : ℝ → ℂ := fun α => mvRemSum u d θ K α with hRm
  have hdecomp : ∀ α, mvBandSum u d θ α = P α + Q α + Rm α := fun α => mvBandSum_eq u d θ hK α
  have hcontP : Continuous P := by
    simp only [hP]; unfold mvPowerSum; fun_prop
  have hcontPm : ∀ m, Continuous (fun α => mvPowerSum u d θ m α) := by
    intro m; unfold mvPowerSum; fun_prop
  have hcontB : Continuous (mvBandSum u d θ) := by
    unfold mvBandSum; fun_prop
  have hpt : ∀ α ∈ Set.Icc a b,
      ‖mvBandSum u d θ α‖ ^ (2 : ℕ) ≤
        2 * ‖P α‖ ^ (2 : ℕ)
          + (8 * ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) * ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ)
            + 4 * (ρ ^ (2 : ℕ) * (N * Sd))) := by
    intro α hα
    have hα0 : 0 ≤ α := le_trans ha hα.1
    have hα1 : α ≤ 1 := le_trans hα.2 hab
    have hBP : ‖mvBandSum u d θ α‖ ≤ ‖P α‖ + ‖Q α + Rm α‖ := by
      rw [hdecomp, add_assoc]
      exact norm_add_le _ _
    set X : ℝ := ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) * ‖mvPowerSum u d θ m α‖ with hX
    have hQX : ‖Q α‖ ≤ X := by
      simp only [hQ]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m _ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hαm : |α ^ m / (m.factorial : ℝ)| ≤ 1 / (m.factorial : ℝ) := by
        rw [abs_of_nonneg (by positivity)]
        have : α ^ m ≤ 1 := pow_le_one₀ hα0 hα1
        gcongr
      exact mul_le_mul_of_nonneg_right hαm (norm_nonneg _)
    have hX2 : X ^ (2 : ℕ) ≤ 2 * ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) * ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ) := by
      have h := sq_sum_weighted_le (Finset.Ico 1 K) (fun m => 1 / (m.factorial : ℝ))
        (fun m => ‖mvPowerSum u d θ m α‖) (fun m _ => by positivity)
      have hw := sum_Ico_inv_factorial_le_two K
      have hsum0 : 0 ≤ ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) * ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ) :=
        Finset.sum_nonneg fun m _ => by positivity
      calc X ^ (2 : ℕ) ≤ (∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ))) *
            ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) * ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ) := h
        _ ≤ 2 * ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) * ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ) :=
            mul_le_mul_of_nonneg_right hw hsum0
    have hRm2 : ‖Rm α‖ ^ (2 : ℕ) ≤ ρ ^ (2 : ℕ) * (N * Sd) := by
      rw [hρ, hN, hSd]
      exact normSq_mvRemSum_le u d θ hτ0 hτ1 hθ hK hα0 hα1
    have hQR : ‖Q α + Rm α‖ ^ (2 : ℕ) ≤ 2 * X ^ (2 : ℕ) + 2 * ‖Rm α‖ ^ (2 : ℕ) := by
      have h1 : ‖Q α + Rm α‖ ≤ X + ‖Rm α‖ := (norm_add_le _ _).trans (by linarith)
      have h0 : 0 ≤ ‖Q α + Rm α‖ := norm_nonneg _
      nlinarith [sq_nonneg (X - ‖Rm α‖), norm_nonneg (Rm α), norm_nonneg (Q α)]
    have hBsq : ‖mvBandSum u d θ α‖ ^ (2 : ℕ) ≤ 2 * ‖P α‖ ^ (2 : ℕ) + 2 * ‖Q α + Rm α‖ ^ (2 : ℕ) := by
      have h0 : 0 ≤ ‖mvBandSum u d θ α‖ := norm_nonneg _
      nlinarith [sq_nonneg (‖P α‖ - ‖Q α + Rm α‖), norm_nonneg (P α), norm_nonneg (Q α + Rm α)]
    nlinarith [hX2, hRm2, hQR, hBsq]
  have hintS : IntervalIntegrable (fun α =>
      ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) * ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ)) volume a b := by
    apply Continuous.intervalIntegrable
    exact continuous_finsetSum _ fun m _ => continuous_const.mul ((hcontPm m).norm.pow 2)
  have hintP : IntervalIntegrable (fun α => ‖P α‖ ^ (2 : ℕ)) volume a b :=
    (hcontP.norm.pow 2).intervalIntegrable _ _
  have hint1 : IntervalIntegrable (fun α => 2 * ‖P α‖ ^ (2 : ℕ)
      + (8 * ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) * ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ)
          + 4 * (ρ ^ (2 : ℕ) * (N * Sd)))) volume a b :=
    (hintP.const_mul _).add ((hintS.const_mul _).add intervalIntegrable_const)
  have hint2 : IntervalIntegrable (fun α => ‖mvBandSum u d θ α‖ ^ (2 : ℕ)) volume a b :=
    (hcontB.norm.pow 2).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on hab' hint2 hint1 hpt
  have hsplit : (∫ α in a..b, (2 * ‖P α‖ ^ (2 : ℕ)
      + (8 * ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) * ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ)
          + 4 * (ρ ^ (2 : ℕ) * (N * Sd)))))
      = 2 * (∫ α in a..b, ‖P α‖ ^ (2 : ℕ))
        + (8 * ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) *
            (∫ α in a..b, ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ))
          + 4 * (ρ ^ (2 : ℕ) * (N * Sd)) * ℓ) := by
    rw [intervalIntegral.integral_add (hintP.const_mul _)
      ((hintS.const_mul _).add intervalIntegrable_const),
      intervalIntegral.integral_const_mul,
      intervalIntegral.integral_add (hintS.const_mul _) intervalIntegrable_const,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const,
      intervalIntegral.integral_finsetSum]
    · simp only [smul_eq_mul, hb]
      have : ∀ m ∈ Finset.Ico 1 K,
          (∫ α in a..a + ℓ, (1 / (m.factorial : ℝ)) * ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ))
            = (1 / (m.factorial : ℝ)) * ∫ α in a..a + ℓ, ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ) := by
        intro m _
        rw [intervalIntegral.integral_const_mul]
      rw [Finset.sum_congr rfl this]
      ring
    · intro m _
      exact (continuous_const.mul ((hcontPm m).norm.pow 2)).intervalIntegrable _ _
  rw [hsplit] at hmono
  have hPup : (∫ α in a..b, ‖P α‖ ^ (2 : ℕ)) ≤ (ℓ + c) * Sd := by
    have h := interval_integral_normSq_expSum_le u (fun r => d r * ((θ r ^ (0 : ℕ) : ℝ) : ℂ))
      (a := a) (ℓ := ℓ) hD hsep
    have hcoef : ∑ r, ‖d r * ((θ r ^ (0 : ℕ) : ℝ) : ℂ)‖ ^ (2 : ℕ) = Sd := by
      rw [hSd]
      refine Finset.sum_congr rfl fun r _ => ?_
      simp
    rw [hcoef] at h
    simpa only [hP, mvPowerSum, hb, hc] using h
  have hlayer : ∀ m ∈ Finset.Ico 1 K,
      (∫ α in a..b, ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ)) ≤ (ℓ + c) * (τ ^ (2 * m) * Sd) := by
    intro m _
    rw [hb, hc, hSd]
    exact integral_normSq_mvPowerSum_le u d θ (a := a) hD hℓ hθ hsep m
  have hsumbound : ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) *
        (∫ α in a..b, ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ))
      ≤ ∑ m ∈ Finset.Ico 1 K, (ℓ + c) * (τ ^ (2 * m) / (m.factorial : ℝ)) * Sd := by
    refine Finset.sum_le_sum fun m hm => ?_
    have := hlayer m hm
    calc (1 / (m.factorial : ℝ)) * (∫ α in a..b, ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ))
        ≤ (1 / (m.factorial : ℝ)) * ((ℓ + c) * (τ ^ (2 * m) * Sd)) := by gcongr
      _ = (ℓ + c) * (τ ^ (2 * m) / (m.factorial : ℝ)) * Sd := by ring
  have hsum_eq : ∑ m ∈ Finset.Ico 1 K, (ℓ + c) * (τ ^ (2 * m) / (m.factorial : ℝ)) * Sd
      = (ℓ + c) * (∑ m ∈ Finset.Ico 1 K, τ ^ (2 * m) / (m.factorial : ℝ)) * Sd := by
    rw [Finset.mul_sum, Finset.sum_mul]
  have hprod : 8 * ∑ m ∈ Finset.Ico 1 K, (1 / (m.factorial : ℝ)) *
        (∫ α in a..b, ‖mvPowerSum u d θ m α‖ ^ (2 : ℕ))
      ≤ 8 * ((ℓ + c) * (∑ m ∈ Finset.Ico 1 K, τ ^ (2 * m) / (m.factorial : ℝ)) * Sd) := by
    rw [← hsum_eq]
    exact mul_le_mul_of_nonneg_left hsumbound (by norm_num)
  have hdouble : 2 * (∫ α in a..b, ‖P α‖ ^ (2 : ℕ)) ≤ 2 * ((ℓ + c) * Sd) :=
    mul_le_mul_of_nonneg_left hPup (by norm_num)
  rw [hb] at hmono hprod hdouble
  linarith [hmono, hprod, hdouble]

end

end GaloisForLFunctions.HTGeometry
