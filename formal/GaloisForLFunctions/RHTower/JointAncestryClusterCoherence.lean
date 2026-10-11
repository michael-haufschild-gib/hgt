import GaloisForLFunctions.RHTower.JointAncestryClusterIdentity

/-!
# Rescuing clusters must be exponentially incoherent

Fix a finite prime set `P` with `b_p = p^{−σ} ≤ 1/100`, put `S = Σ_{p∈P} b_p`, and let a cluster
`(u_j, ψ_j)` (real weights, unimodular prime-phase patterns) be tested at the phase design
`θ_p = e^{iπ/S}`.  **Theorem** (`jasCluster_re_le`):

`Re Σ_{j,k} u_j u_k Π_p (1 − e^{iπ/S} ψ_{j,p} ψ̄_{k,p} b_p)⁻¹
   ≤ −½ Σ_{j,k} u_j u_k Π_p (1 − ψ_{j,p} ψ̄_{k,p} b_p)⁻¹ + 3 (Σ_j |u_j|)² Π_p (1 − b_p)⁻¹ e^{−S/60}`.

So the twisted average of a cluster is negative unless its untwisted average (a sum of squares,
`sum_sum_prod_inv_eq_tsum_of_one`) is at most `6 e^{−S/60}` times the fully coherent value
`(Σ|u_j|)² Π_p (1 − b_p)⁻¹`.  In route JAS this means a cluster of zeros near `Re s = 1` can
cancel the negative test of its members only if it is exponentially incoherent on the test primes.

**Proof.**  By the cluster identity the twisted average is `Σ_m cos(πΩ(m)/S) m^{−σ} |Ĉ(m)|²` over
`P`-smooth `m`, where `Ω(m)` counts prime factors with multiplicity.  On `2S/3 ≤ Ω ≤ 4S/3` the
cosine is at most `−½`.  The two tails are bounded by Chernoff's inequality with the tilts
`(6/5)^Ω` and `(5/6)^Ω`, whose Euler products are `Π_p (1 − (6/5) b_p)⁻¹` and
`Π_p (1 − (5/6) b_p)⁻¹`.  Only the elementary bounds `1 − 1/x ≤ log x ≤ x − 1` are used.
-/

open Complex

namespace RHTower

open scoped ComplexConjugate

noncomputable section

/-! ### The prime-factor count on `P`-smooth integers -/

/-- `Ω_P(m) = Σ_{p∈P} v_p(m)`. -/
def jasDeg (P : Finset Nat.Primes) (m : ℕ) : ℕ :=
  ∑ i : ↥P, m.factorization ((i : Nat.Primes) : ℕ)

theorem jasEulerCoeff_const (P : Finset Nat.Primes) (c : ℂ) (m : ℕ) :
    jasEulerCoeff P (fun _ => c) m = c ^ jasDeg P m := by
  unfold jasEulerCoeff jasDeg
  exact Finset.prod_pow_eq_pow_sum _ _ _

theorem rpow_natCast_neg_ofReal {m : ℕ} (σ : ℝ) :
    ((m : ℂ) ^ (-(σ : ℂ))) = (((m : ℝ) ^ (-σ) : ℝ) : ℂ) := by
  rw [Complex.ofReal_cpow (Nat.cast_nonneg m)]
  push_cast; rfl

/-- **Tilted Euler product.**  `Σ_m t^{Ω_P(m)} m^{−σ} = Π_p (1 − t p^{−σ})⁻¹` for `0 ≤ t`,
`t p^{−σ} < 1`. -/
theorem hasSum_tilt {P : Finset Nat.Primes} {σ t : ℝ} (hσ : 0 < σ) (ht : 0 ≤ t)
    (hb : ∀ i : ↥P, t * (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) < 1) :
    HasSum (fun m : Nat.factoredNumbers (jasPrimeNats P) =>
      t ^ jasDeg P m * ((m : ℕ) : ℝ) ^ (-σ))
      (∏ i : ↥P, (1 - t * (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹) := by
  have h := hasSum_jasEulerHom_of_lt (P := P) (w := fun _ => (t : ℂ)) (z := (σ : ℂ))
    (by simpa using hσ) (fun i => by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]; simpa using hb i)
  rw [← Complex.hasSum_ofReal]
  convert h using 1
  · funext m
    rw [jasEulerHom_apply _ _ (ne_zero_of_mem_factoredNumbers m), jasEulerCoeff_const,
      rpow_natCast_neg_ofReal]
    push_cast; ring
  · push_cast
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [rpow_natCast_neg_ofReal]

theorem summable_rpow_neg_factored' {σ : ℝ} (hσ : 0 < σ) (P : Finset Nat.Primes) :
    Summable fun m : Nat.factoredNumbers (jasPrimeNats P) => ((m : ℕ) : ℝ) ^ (-σ) :=
  summable_rpow_neg_factored hσ P

/-- Chernoff above. -/
theorem tsum_tail_above_le {P : Finset Nat.Primes} {σ t A : ℝ} (hσ : 0 < σ) (ht : 1 ≤ t)
    (hb : ∀ i : ↥P, t * (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) < 1) :
    ∑' m : Nat.factoredNumbers (jasPrimeNats P),
        (if A < (jasDeg P m : ℝ) then ((m : ℕ) : ℝ) ^ (-σ) else 0) ≤
      Real.exp (-(A * Real.log t)) *
        ∏ i : ↥P, (1 - t * (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹ := by
  have hT := hasSum_tilt hσ (by linarith) hb
  rw [← hT.tsum_eq, ← tsum_mul_left]
  have hlt : 0 ≤ Real.log t := Real.log_nonneg ht
  refine Summable.tsum_le_tsum (fun m => ?_) ?_ (hT.summable.mul_left _)
  · have hm0 : (0 : ℝ) ≤ ((m : ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    split_ifs with h
    · have h1 : Real.exp (A * Real.log t) ≤ t ^ jasDeg P m := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by linarith)]
        exact Real.exp_le_exp.mpr (by nlinarith)
      have h2 : 1 ≤ Real.exp (-(A * Real.log t)) * t ^ jasDeg P m := by
        rw [Real.exp_neg, inv_mul_eq_div, le_div_iff₀ (Real.exp_pos _), one_mul]; exact h1
      nlinarith
    · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (pow_nonneg (by linarith) _) hm0)
  · refine (summable_rpow_neg_factored' hσ P).of_nonneg_of_le (fun m => ?_) (fun m => ?_)
    · split_ifs
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-- Chernoff below. -/
theorem tsum_tail_below_le {P : Finset Nat.Primes} {σ t A : ℝ} (hσ : 0 < σ) (ht0 : 0 < t)
    (ht : t ≤ 1) (hb : ∀ i : ↥P, t * (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) < 1) :
    ∑' m : Nat.factoredNumbers (jasPrimeNats P),
        (if (jasDeg P m : ℝ) < A then ((m : ℕ) : ℝ) ^ (-σ) else 0) ≤
      Real.exp (-(A * Real.log t)) *
        ∏ i : ↥P, (1 - t * (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹ := by
  have hT := hasSum_tilt hσ ht0.le hb
  rw [← hT.tsum_eq, ← tsum_mul_left]
  have hlt : Real.log t ≤ 0 := Real.log_nonpos ht0.le ht
  refine Summable.tsum_le_tsum (fun m => ?_) ?_ (hT.summable.mul_left _)
  · have hm0 : (0 : ℝ) ≤ ((m : ℕ) : ℝ) ^ (-σ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    split_ifs with h
    · have h1 : Real.exp (A * Real.log t) ≤ t ^ jasDeg P m := by
        rw [← Real.rpow_natCast, Real.rpow_def_of_pos ht0]
        exact Real.exp_le_exp.mpr (by nlinarith)
      have h2 : 1 ≤ Real.exp (-(A * Real.log t)) * t ^ jasDeg P m := by
        rw [Real.exp_neg, inv_mul_eq_div, le_div_iff₀ (Real.exp_pos _), one_mul]; exact h1
      nlinarith
    · exact mul_nonneg (Real.exp_pos _).le (mul_nonneg (pow_nonneg ht0.le _) hm0)
  · refine (summable_rpow_neg_factored' hσ P).of_nonneg_of_le (fun m => ?_) (fun m => ?_)
    · split_ifs
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
      · exact le_rfl
    · split_ifs
      · exact le_rfl
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _

/-! ### Comparison of tilted products -/

theorem prod_tilt_up_le {P : Finset Nat.Primes} {b : ↥P → ℝ} (hb0 : ∀ i, 0 ≤ b i)
    (hb : ∀ i, b i ≤ 1 / 100) :
    ∏ i : ↥P, (1 - 6 / 5 * b i)⁻¹ ≤
      (∏ i : ↥P, (1 - b i)⁻¹) * Real.exp (100 / 494 * ∑ i : ↥P, b i) := by
  rw [Finset.mul_sum, Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun i _ => (inv_pos.mpr (by linarith [hb i])).le) fun i _ => ?_
  have h1 : 0 < 1 - b i := by linarith [hb i]
  have h2 : 0 < 1 - 6 / 5 * b i := by linarith [hb i]
  have h3 : (1 - b i) / (1 - 6 / 5 * b i) ≤ Real.exp (100 / 494 * b i) := by
    rw [div_le_iff₀ h2]
    have := Real.add_one_le_exp (100 / 494 * b i)
    nlinarith [hb0 i, hb i]
  calc (1 - 6 / 5 * b i)⁻¹ = (1 - b i)⁻¹ * ((1 - b i) / (1 - 6 / 5 * b i)) := by
        field_simp
    _ ≤ (1 - b i)⁻¹ * Real.exp (100 / 494 * b i) :=
        mul_le_mul_of_nonneg_left h3 (inv_pos.mpr h1).le

theorem prod_tilt_down_le {P : Finset Nat.Primes} {b : ↥P → ℝ} (hb0 : ∀ i, 0 ≤ b i)
    (hb : ∀ i, b i ≤ 1 / 100) :
    ∏ i : ↥P, (1 - 5 / 6 * b i)⁻¹ ≤
      (∏ i : ↥P, (1 - b i)⁻¹) * Real.exp (-(1 / 6 * ∑ i : ↥P, b i)) := by
  rw [Finset.mul_sum, ← Finset.sum_neg_distrib, Real.exp_sum, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun i _ => (inv_pos.mpr (by linarith [hb i])).le) fun i _ => ?_
  have h1 : 0 < 1 - b i := by linarith [hb i]
  have h2 : 0 < 1 - 5 / 6 * b i := by linarith [hb i]
  have h3 : (1 - b i) / (1 - 5 / 6 * b i) ≤ Real.exp (-(1 / 6 * b i)) := by
    rw [div_le_iff₀ h2]
    have := Real.add_one_le_exp (-(1 / 6 * b i))
    nlinarith [hb0 i, hb i]
  calc (1 - 5 / 6 * b i)⁻¹ = (1 - b i)⁻¹ * ((1 - b i) / (1 - 5 / 6 * b i)) := by
        field_simp
    _ ≤ (1 - b i)⁻¹ * Real.exp (-(1 / 6 * b i)) :=
        mul_le_mul_of_nonneg_left h3 (inv_pos.mpr h1).le

/-- On the bulk the twist is at least `π/2` away from `0`. -/
theorem cos_le_neg_half {x : ℝ} (h1 : 2 * Real.pi / 3 ≤ x) (h2 : x ≤ 4 * Real.pi / 3) :
    Real.cos x ≤ -(1 / 2) := by
  have hpi := Real.pi_pos
  have h : 1 / 2 ≤ Real.cos (x - Real.pi) := by
    rw [← Real.cos_abs, ← Real.cos_pi_div_three]
    exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _) (by linarith)
      (by rw [abs_le]; constructor <;> linarith)
  rw [Real.cos_sub_pi] at h
  linarith

theorem normSq_cluster_le {ι : Type*} (t : Finset ι) (u : ι → ℝ) (P : Finset Nat.Primes)
    {ψ : ι → ↥P → ℂ} (hψ : ∀ j i, ‖ψ j i‖ ≤ 1) (m : ℕ) :
    Complex.normSq (∑ j ∈ t, (u j : ℂ) * jasEulerCoeff P (ψ j) m) ≤ (∑ j ∈ t, |u j|) ^ 2 := by
  rw [Complex.normSq_eq_norm_sq]
  have h : ‖∑ j ∈ t, (u j : ℂ) * jasEulerCoeff P (ψ j) m‖ ≤ ∑ j ∈ t, |u j| := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _) (norm_jasEulerCoeff_le_one (hψ j) m)
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

/-- **Exponential coherence threshold for rescuing clusters.** -/
theorem jasCluster_re_le {ι : Type*} (t : Finset ι) (u : ι → ℝ) (P : Finset Nat.Primes)
    {ψ : ι → ↥P → ℂ} (hψ : ∀ j i, ‖ψ j i‖ ≤ 1) {σ : ℝ} (hσ : 0 < σ)
    (hb : ∀ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) ≤ 1 / 100)
    (hS : 0 < ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) :
    (∑ j ∈ t, ∑ k ∈ t, (u j : ℂ) * u k * ∏ i : ↥P,
        (1 - Complex.exp (((Real.pi / ∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) : ℝ) : ℂ) *
          Complex.I) * ψ j i * conj (ψ k i) * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹).re ≤
      -(1 / 2) * (∑ j ∈ t, ∑ k ∈ t, (u j : ℂ) * u k *
        ∏ i : ↥P, (1 - ψ j i * conj (ψ k i) * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹).re +
      3 * (∑ j ∈ t, |u j|) ^ 2 * (∏ i : ↥P, (1 - (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹) *
        Real.exp (-((∑ i : ↥P, (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ)) / 60)) := by
  classical
  set b : ↥P → ℝ := fun i => (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) with hbdef
  set S : ℝ := ∑ i : ↥P, b i with hSdef
  have hb0 : ∀ i, 0 ≤ b i := fun i => Real.rpow_nonneg (Nat.cast_nonneg _) _
  set τ : ℝ := Real.pi / S with hτ
  set U : ℝ := ∑ j ∈ t, |u j| with hU
  set C : ℕ → ℂ := fun m => ∑ j ∈ t, (u j : ℂ) * jasEulerCoeff P (ψ j) m with hC
  set W : Nat.factoredNumbers (jasPrimeNats P) → ℝ :=
    fun m => ((m : ℕ) : ℝ) ^ (-σ) * Complex.normSq (C m) with hW
  have hsumm := summable_rpow_neg_factored' hσ P
  have hW0 : ∀ m, 0 ≤ W m := fun m => mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
    (Complex.normSq_nonneg _)
  have hWle : ∀ m, W m ≤ U ^ 2 * ((m : ℕ) : ℝ) ^ (-σ) := fun m => by
    rw [hW, mul_comm (U ^ 2)]
    exact mul_le_mul_of_nonneg_left (normSq_cluster_le t u P hψ m)
      (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hWs : Summable W := (hsumm.mul_left (U ^ 2)).of_nonneg_of_le hW0 hWle
  -- the twisted average as a cosine series
  have hθ : ∀ i : ↥P, ‖(fun _ : ↥P => Complex.exp ((τ : ℂ) * Complex.I)) i‖ = 1 := fun i =>
    Complex.norm_exp_ofReal_mul_I τ
  have hL := sum_sum_prod_inv_eq_tsum t u P hθ hψ (z := (σ : ℂ)) (by simpa using hσ)
  have hterm : ∀ m : Nat.factoredNumbers (jasPrimeNats P),
      (jasEulerHom P (fun _ => Complex.exp ((τ : ℂ) * Complex.I)) (σ : ℂ) m *
        (Complex.normSq (C m) : ℂ)).re = Real.cos (τ * jasDeg P m) * W m := by
    intro m
    rw [jasEulerHom_apply _ _ (ne_zero_of_mem_factoredNumbers m), jasEulerCoeff_const,
      ← Complex.exp_nat_mul, rpow_natCast_neg_ofReal]
    rw [show ((jasDeg P m : ℕ) : ℂ) * ((τ : ℂ) * Complex.I) = ((τ * jasDeg P m : ℝ) : ℂ) * Complex.I
      by push_cast; ring]
    rw [mul_assoc, ← Complex.ofReal_mul, Complex.re_mul_ofReal, Complex.exp_ofReal_mul_I_re, hW]
  have hsumT : Summable fun m : Nat.factoredNumbers (jasPrimeNats P) =>
      jasEulerHom P (fun _ => Complex.exp ((τ : ℂ) * Complex.I)) (σ : ℂ) m *
        (Complex.normSq (C m) : ℂ) := by
    refine Summable.of_norm_bounded hWs fun m => ?_
    rw [norm_mul, norm_jasEulerHom_factored hθ, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Complex.normSq_nonneg _)]
    simp [hW]
  have hLHS : (∑ j ∈ t, ∑ k ∈ t, (u j : ℂ) * u k * ∏ i : ↥P,
        (1 - Complex.exp ((τ : ℂ) * Complex.I) * ψ j i * conj (ψ k i) *
          (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹).re =
      ∑' m : Nat.factoredNumbers (jasPrimeNats P), Real.cos (τ * jasDeg P m) * W m := by
    rw [hL, Complex.re_tsum hsumT]
    exact tsum_congr hterm
  -- the untwisted average
  have hR := sum_sum_prod_inv_eq_tsum_of_one t u P hψ hσ
  have hRHS : (∑ j ∈ t, ∑ k ∈ t, (u j : ℂ) * u k *
        ∏ i : ↥P, (1 - ψ j i * conj (ψ k i) * (((i : Nat.Primes) : ℕ) : ℂ) ^ (-(σ : ℂ)))⁻¹).re =
      ∑' m : Nat.factoredNumbers (jasPrimeNats P), W m := by
    rw [hR, ← Complex.ofReal_tsum, Complex.ofReal_re]
  rw [hLHS, hRHS]
  -- pointwise split
  set Iup : Nat.factoredNumbers (jasPrimeNats P) → ℝ := fun m =>
    if 4 * S / 3 < (jasDeg P m : ℝ) then ((m : ℕ) : ℝ) ^ (-σ) else 0 with hIup
  set Idn : Nat.factoredNumbers (jasPrimeNats P) → ℝ := fun m =>
    if (jasDeg P m : ℝ) < 2 * S / 3 then ((m : ℕ) : ℝ) ^ (-σ) else 0 with hIdn
  have hI0 : ∀ m : Nat.factoredNumbers (jasPrimeNats P), 0 ≤ Iup m ∧ 0 ≤ Idn m := fun m => by
    have := Real.rpow_nonneg (Nat.cast_nonneg ((m : ℕ))) (-σ)
    constructor <;> (simp only [hIup, hIdn]; split_ifs <;> linarith)
  have hIs : Summable Iup ∧ Summable Idn := by
    constructor
    · refine hsumm.of_nonneg_of_le (fun m => (hI0 m).1) fun m => ?_
      simp only [hIup]; split_ifs
      · exact le_rfl
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
    · refine hsumm.of_nonneg_of_le (fun m => (hI0 m).2) fun m => ?_
      simp only [hIdn]; split_ifs
      · exact le_rfl
      · exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hpt : ∀ m : Nat.factoredNumbers (jasPrimeNats P), Real.cos (τ * jasDeg P m) * W m ≤
      -(1 / 2) * W m + 3 / 2 * U ^ 2 * (Iup m + Idn m) := by
    intro m
    have hm0 := Real.rpow_nonneg (Nat.cast_nonneg ((m : ℕ))) (-σ)
    by_cases hmid : 2 * S / 3 ≤ (jasDeg P m : ℝ) ∧ (jasDeg P m : ℝ) ≤ 4 * S / 3
    · have hc : Real.cos (τ * jasDeg P m) ≤ -(1 / 2) := by
        apply cos_le_neg_half
        · rw [hτ, div_mul_eq_mul_div, le_div_iff₀ hS]; nlinarith [Real.pi_pos, hmid.1]
        · rw [hτ, div_mul_eq_mul_div, div_le_iff₀ hS]; nlinarith [Real.pi_pos, hmid.2]
      have : 0 ≤ 3 / 2 * U ^ 2 * (Iup m + Idn m) :=
        mul_nonneg (by positivity) (add_nonneg (hI0 m).1 (hI0 m).2)
      nlinarith [hW0 m]
    · have hind : ((m : ℕ) : ℝ) ^ (-σ) ≤ Iup m + Idn m := by
        simp only [hIup, hIdn]
        push Not at hmid
        by_cases h1 : 2 * S / 3 ≤ (jasDeg P m : ℝ)
        · have h2 := hmid h1
          rw [if_pos h2, if_neg (by linarith)]; linarith
        · push Not at h1
          rw [if_pos h1]
          split_ifs <;> linarith
      have hc := Real.cos_le_one (τ * jasDeg P m)
      have := hWle m
      have hU0 : 0 ≤ U ^ 2 := sq_nonneg _
      nlinarith [hW0 m, mul_le_mul_of_nonneg_left hind hU0]
  have hsplit : ∑' m : Nat.factoredNumbers (jasPrimeNats P), Real.cos (τ * jasDeg P m) * W m ≤
      -(1 / 2) * ∑' m : Nat.factoredNumbers (jasPrimeNats P), W m + 3 / 2 * U ^ 2 * (∑' m : Nat.factoredNumbers (jasPrimeNats P), Iup m + ∑' m : Nat.factoredNumbers (jasPrimeNats P), Idn m) := by
    have hcs : Summable fun m : Nat.factoredNumbers (jasPrimeNats P) => Real.cos (τ * jasDeg P m) * W m :=
      hWs.of_norm_bounded fun m => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hW0 m)]
        exact mul_le_of_le_one_left (hW0 m) (Real.abs_cos_le_one _)
    calc ∑' m : Nat.factoredNumbers (jasPrimeNats P), Real.cos (τ * jasDeg P m) * W m
        ≤ ∑' m : Nat.factoredNumbers (jasPrimeNats P), (-(1 / 2) * W m + 3 / 2 * U ^ 2 * (Iup m + Idn m)) :=
          Summable.tsum_le_tsum hpt hcs
            ((hWs.mul_left _).add ((hIs.1.add hIs.2).mul_left _))
      _ = -(1 / 2) * ∑' m : Nat.factoredNumbers (jasPrimeNats P), W m + 3 / 2 * U ^ 2 * (∑' m : Nat.factoredNumbers (jasPrimeNats P), Iup m + ∑' m : Nat.factoredNumbers (jasPrimeNats P), Idn m) := by
          rw [Summable.tsum_add (hWs.mul_left _) ((hIs.1.add hIs.2).mul_left _), tsum_mul_left,
            tsum_mul_left, Summable.tsum_add hIs.1 hIs.2]
  -- the tails
  have hbup : ∀ i : ↥P, 6 / 5 * (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) < 1 := fun i => by
    have := hb i; linarith
  have hbdn : ∀ i : ↥P, 5 / 6 * (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ) < 1 := fun i => by
    have := hb i; linarith
  have hG0 : 0 ≤ ∏ i : ↥P, (1 - b i)⁻¹ :=
    Finset.prod_nonneg fun i _ => (inv_pos.mpr (by linarith [hb i])).le
  have hup : ∑' m : Nat.factoredNumbers (jasPrimeNats P), Iup m ≤ (∏ i : ↥P, (1 - b i)⁻¹) * Real.exp (-(S / 60)) := by
    have h1 := tsum_tail_above_le (P := P) (A := 4 * S / 3) hσ (by norm_num : (1:ℝ) ≤ 6 / 5) hbup
    have h2 := prod_tilt_up_le hb0 hb
    have hlog : 1 / 6 ≤ Real.log (6 / 5) := by
      have := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 6 / 5 by norm_num); norm_num at this ⊢
      linarith
    have h3 : Real.exp (-(4 * S / 3 * Real.log (6 / 5))) * Real.exp (100 / 494 * S) ≤
        Real.exp (-(S / 60)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
    calc ∑' m : Nat.factoredNumbers (jasPrimeNats P), Iup m ≤ Real.exp (-(4 * S / 3 * Real.log (6 / 5))) *
          ∏ i : ↥P, (1 - 6 / 5 * (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹ := h1
      _ ≤ Real.exp (-(4 * S / 3 * Real.log (6 / 5))) *
          ((∏ i : ↥P, (1 - b i)⁻¹) * Real.exp (100 / 494 * S)) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = (∏ i : ↥P, (1 - b i)⁻¹) *
          (Real.exp (-(4 * S / 3 * Real.log (6 / 5))) * Real.exp (100 / 494 * S)) := by ring
      _ ≤ (∏ i : ↥P, (1 - b i)⁻¹) * Real.exp (-(S / 60)) :=
          mul_le_mul_of_nonneg_left h3 hG0
  have hdn : ∑' m : Nat.factoredNumbers (jasPrimeNats P), Idn m ≤ (∏ i : ↥P, (1 - b i)⁻¹) * Real.exp (-(S / 60)) := by
    have h1 := tsum_tail_below_le (P := P) (A := 2 * S / 3) hσ (by norm_num : (0:ℝ) < 5 / 6)
      (by norm_num) hbdn
    have h2 := prod_tilt_down_le hb0 hb
    have hlog : -(1 / 5) ≤ Real.log (5 / 6) := by
      have := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < 5 / 6 by norm_num); norm_num at this ⊢
      linarith
    have h3 : Real.exp (-(2 * S / 3 * Real.log (5 / 6))) * Real.exp (-(1 / 6 * S)) ≤
        Real.exp (-(S / 60)) := by
      rw [← Real.exp_add]; exact Real.exp_le_exp.mpr (by nlinarith)
    calc ∑' m : Nat.factoredNumbers (jasPrimeNats P), Idn m ≤ Real.exp (-(2 * S / 3 * Real.log (5 / 6))) *
          ∏ i : ↥P, (1 - 5 / 6 * (((i : Nat.Primes) : ℕ) : ℝ) ^ (-σ))⁻¹ := h1
      _ ≤ Real.exp (-(2 * S / 3 * Real.log (5 / 6))) *
          ((∏ i : ↥P, (1 - b i)⁻¹) * Real.exp (-(1 / 6 * S))) :=
          mul_le_mul_of_nonneg_left h2 (Real.exp_pos _).le
      _ = (∏ i : ↥P, (1 - b i)⁻¹) *
          (Real.exp (-(2 * S / 3 * Real.log (5 / 6))) * Real.exp (-(1 / 6 * S))) := by ring
      _ ≤ (∏ i : ↥P, (1 - b i)⁻¹) * Real.exp (-(S / 60)) :=
          mul_le_mul_of_nonneg_left h3 hG0
  have hU0 : 0 ≤ U ^ 2 := sq_nonneg _
  nlinarith [mul_le_mul_of_nonneg_left (add_le_add hup hdn) (show 0 ≤ 3 / 2 * U ^ 2 by positivity)]

end

end RHTower
