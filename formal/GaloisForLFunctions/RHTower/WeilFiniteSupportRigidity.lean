import GaloisForLFunctions.RHTower.ZetaNotchTwistMainTerm

/-!
# Weil-cone rigidity on finitely generated multiplicative supports

**Theorem** (`eq_zero_of_positiveDefinite_neg_nullPotential`). Let `P` be a finite set of primes
and `v : ℕ → ℝ` supported on the `P`-smooth numbers `n ≥ 2`, with `|v(n)| ≤ 2 log n + A`. If the
null potential `−ψ_v`, `ψ_v(y) = Σ_n v(n)(K(y + log n) + K(y − log n))`, is positive definite, then
`v = 0`.

**Proof.** Fix `n₀` with `v(n₀) ≠ 0` and the sign `ε` of `v(n₀)`. Pair Bochner's measure of `−ψ_v`
with the `|ζ|²` notch test of weight `q(t) = |1 + ε n₀^{it}|² Π_{p∈P} |1 − p^{−1/2+it}|²`
(`sum_mul_re_weightedMoment_nonpos`): `Σ_n v(n) Re M_q(log n) ≤ 0`. At a smooth twist the Euler
factors cancel the lifted diagonal except at `n = n₀` (`exists_norm_weightedMoment_sub_main_le`), so
`|v(n₀)| Π_p(1 − 1/p) ∫ ω log t` is bounded by the diagonal remainders `O(L)`, the near-resonant and
Gaussian terms of the twists with `log n ≤ M`, and the crude tail of the twists with `log n > M`.
With `L = M^{8J}` every error is `O(L)` while `∫ ω log t ≥ L log L`; letting `M → ∞` forces
`v(n₀) = 0`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

namespace RHTower.WeilFiniteSupport

open RHTower.ZetaNotch RHTower.SmoothNumbers

variable {P : Finset ℕ}

/-! ## Exponent vectors of smooth twists -/

theorem vecNum_mul_vecDen_eq (b : P → ℤ) :
    vecNum b * vecDen b = ∏ p : P, (p : ℕ) ^ (b p).natAbs := by
  unfold vecNum vecDen
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← pow_add, Int.toNat_add_toNat_neg_eq_natAbs]

theorem prod_pow_factorization_eq {n : ℕ} (hn : IsSmoothOver P n) :
    ∏ p : P, (p : ℕ) ^ n.factorization p = n := by
  have hn0 : n ≠ 0 := by have := hn.1; omega
  rw [Finset.prod_coe_sort P (fun p => p ^ n.factorization p),
    ← Finsupp.prod_of_support_subset _ (by rw [Nat.support_factorization]; exact hn.2)
      (fun p k => p ^ k) (fun p _ => pow_zero p)]
  exact Nat.prod_factorization_pow_eq_self hn0

theorem vecNum_vecOf {n : ℕ} (hn : IsSmoothOver P n) : vecNum (vecOf P n) = n := by
  unfold vecNum vecOf
  simp only [Int.toNat_natCast]
  exact prod_pow_factorization_eq hn

theorem vecDen_vecOf (n : ℕ) : vecDen (vecOf P n) = 1 := by
  unfold vecDen vecOf
  refine Finset.prod_eq_one fun p _ => ?_
  have : (-(n.factorization p : ℤ)).toNat = 0 := by omega
  rw [this, pow_zero]

theorem inv_sqrt_eq_prod_primeHalf {n : ℕ} (hn : IsSmoothOver P n) :
    (Real.sqrt n)⁻¹ = ∏ p : P, primeHalf p ^ n.factorization p := by
  have h := inv_sqrt_vecNum_mul_vecDen (vecOf P n)
  rw [vecNum_vecOf hn, vecDen_vecOf, Nat.cast_one, mul_one] at h
  rw [h]
  refine Finset.prod_congr rfl fun p _ => ?_
  simp [vecOf]

/-- The twist bound `K₀ = Π_p p^{v_p(n₀) + 1}`. -/
def twistBound (P : Finset ℕ) (n₀ : ℕ) : ℕ := ∏ p : P, (p : ℕ) ^ (n₀.factorization p + 1)

theorem twistBound_pos (hP : ∀ p ∈ P, p.Prime) (n₀ : ℕ) : 0 < twistBound P n₀ :=
  Finset.prod_pos fun p _ => pow_pos (hP p p.2).pos _

/-- The coordinates of a mode twist `b = v(n) − (j v(n₀) + c)`. -/
theorem mode_coord_bounds {n n₀ : ℕ} {j : ℤ} (hj : j ∈ bohrModes) {c : P → ℤ}
    (hc : c ∈ Fintype.piFinset (fun _ : P => bohrModes)) (p : P) :
    (n.factorization p : ℤ) ≤ ((vecOf P n - (j • vecOf P n₀ + c)) p).natAbs +
        (n₀.factorization p + 1 : ℕ) ∧
      (((vecOf P n - (j • vecOf P n₀ + c)) p).natAbs : ℤ) ≤
        n.factorization p + (n₀.factorization p + 1 : ℕ) ∧
      ((-(vecOf P n - (j • vecOf P n₀ + c)) p).toNat : ℤ) ≤ (n₀.factorization p + 1 : ℕ) := by
  have hcp : c p ∈ bohrModes := Fintype.mem_piFinset.mp hc p
  unfold bohrModes at hj hcp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj hcp
  simp only [vecOf, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rcases hj with rfl | rfl | rfl <;> rcases hcp with h | h | h <;> rw [h] <;> omega

theorem sqrt_twistBound_eq (P : Finset ℕ) (n₀ : ℕ) :
    Real.sqrt (twistBound P n₀) = ∏ p : P, Real.sqrt (p : ℕ) ^ (n₀.factorization p + 1) := by
  have hsq : ((twistBound P n₀ : ℕ) : ℝ) =
      (∏ p : P, Real.sqrt (p : ℕ) ^ (n₀.factorization p + 1)) ^ 2 := by
    unfold twistBound
    push_cast
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [hsq, Real.sqrt_sq (Finset.prod_nonneg fun p _ => by positivity)]

/-- The weight of a mode twist is at most `√K₀ · n_P^{−1/2}`, `n_P = Π_{p∈P} p^{v_p(n)}`. -/
theorem weight_mode_le_prod (hP : ∀ p ∈ P, p.Prime) {n n₀ : ℕ} {j : ℤ} (hj : j ∈ bohrModes)
    {c : P → ℤ} (hc : c ∈ Fintype.piFinset (fun _ : P => bohrModes)) :
    ∏ p : P, primeHalf p ^ ((vecOf P n - (j • vecOf P n₀ + c)) p).natAbs ≤
      Real.sqrt (twistBound P n₀) *
        (Real.sqrt ((∏ p : P, (p : ℕ) ^ n.factorization p : ℕ) : ℝ))⁻¹ := by
  have hinv : (Real.sqrt ((∏ p : P, (p : ℕ) ^ n.factorization p : ℕ) : ℝ))⁻¹ =
      ∏ p : P, primeHalf p ^ n.factorization p := by
    have h := inv_sqrt_vecNum_mul_vecDen (vecOf P n)
    have hnum : vecNum (vecOf P n) = ∏ p : P, (p : ℕ) ^ n.factorization p := by
      unfold vecNum vecOf
      simp only [Int.toNat_natCast]
    rw [hnum, vecDen_vecOf, Nat.cast_one, mul_one] at h
    rw [h]
    refine Finset.prod_congr rfl fun p _ => ?_
    simp [vecOf]
  rw [hinv, sqrt_twistBound_eq, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun p _ => pow_nonneg (primeHalf_nonneg _) _) fun p _ => ?_
  have hp1 : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast (hP p p.2).one_lt.le
  have hsqrt : 0 < Real.sqrt (p : ℕ) := Real.sqrt_pos.mpr (by linarith)
  set s : ℝ := primeHalf p with hs
  have hs0 : 0 < s := inv_pos.mpr hsqrt
  have hs1 : s ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hp1)
  have hsq : Real.sqrt (p : ℕ) * s = 1 := mul_inv_cancel₀ hsqrt.ne'
  set m := ((vecOf P n - (j • vecOf P n₀ + c)) p).natAbs with hm
  set e := n₀.factorization p + 1 with he
  set k := n.factorization p with hk
  have hkm : k ≤ m + e := by
    have := (mode_coord_bounds (n := n) (n₀ := n₀) hj hc p).1
    omega
  calc s ^ m = (Real.sqrt (p : ℕ) * s) ^ e * s ^ m := by rw [hsq, one_pow, one_mul]
    _ = Real.sqrt (p : ℕ) ^ e * s ^ (m + e) := by rw [mul_pow, pow_add]; ring
    _ ≤ Real.sqrt (p : ℕ) ^ e * s ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hs0.le hs1 hkm) (by positivity)

/-- The weight of a mode twist is at most `√K₀ · n^{−1/2}`. -/
theorem weight_mode_le (hP : ∀ p ∈ P, p.Prime) {n n₀ : ℕ} (hn : IsSmoothOver P n) {j : ℤ}
    (hj : j ∈ bohrModes) {c : P → ℤ} (hc : c ∈ Fintype.piFinset (fun _ : P => bohrModes)) :
    ∏ p : P, primeHalf p ^ ((vecOf P n - (j • vecOf P n₀ + c)) p).natAbs ≤
      Real.sqrt (twistBound P n₀) * (Real.sqrt n)⁻¹ := by
  have h := weight_mode_le_prod hP hj hc (n := n) (n₀ := n₀)
  rwa [prod_pow_factorization_eq hn] at h

/-- `log N(b) ≤ log n_P + log K₀` for a mode twist. -/
theorem log_mode_norm_le_prod (hP : ∀ p ∈ P, p.Prime) {n n₀ : ℕ} {j : ℤ}
    (hj : j ∈ bohrModes) {c : P → ℤ} (hc : c ∈ Fintype.piFinset (fun _ : P => bohrModes)) :
    Real.log ((vecNum (vecOf P n - (j • vecOf P n₀ + c)) : ℝ) *
        vecDen (vecOf P n - (j • vecOf P n₀ + c))) ≤
      Real.log ((∏ p : P, (p : ℕ) ^ n.factorization p : ℕ) : ℝ) +
        Real.log (twistBound P n₀) := by
  have hp0 : ∀ p : P, ((p : ℕ) : ℝ) ≠ 0 := fun p => by exact_mod_cast (hP p p.2).ne_zero
  have hlogp : ∀ p : P, 0 ≤ Real.log ((p : ℕ) : ℝ) := fun p =>
    Real.log_nonneg (by exact_mod_cast (hP p p.2).one_lt.le)
  have e1 : ((vecNum (vecOf P n - (j • vecOf P n₀ + c)) : ℝ) *
      vecDen (vecOf P n - (j • vecOf P n₀ + c))) =
      ∏ p : P, ((p : ℕ) : ℝ) ^ ((vecOf P n - (j • vecOf P n₀ + c)) p).natAbs := by
    rw [← Nat.cast_mul, vecNum_mul_vecDen_eq]
    push_cast
    rfl
  have e2 : ((∏ p : P, (p : ℕ) ^ n.factorization p : ℕ) : ℝ) =
      ∏ p : P, ((p : ℕ) : ℝ) ^ n.factorization p := by
    push_cast
    rfl
  have e3 : ((twistBound P n₀ : ℕ) : ℝ) = ∏ p : P, ((p : ℕ) : ℝ) ^ (n₀.factorization p + 1) := by
    unfold twistBound
    push_cast
    rfl
  rw [e1, e2, e3, Real.log_prod (fun p _ => pow_ne_zero _ (hp0 p)),
    Real.log_prod (fun p _ => pow_ne_zero _ (hp0 p)),
    Real.log_prod (fun p _ => pow_ne_zero _ (hp0 p)), ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [Real.log_pow, Real.log_pow, Real.log_pow, ← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hlogp p)
  have := (mode_coord_bounds (n := n) (n₀ := n₀) hj hc p).2.1
  exact_mod_cast (by omega : ((vecOf P n - (j • vecOf P n₀ + c)) p).natAbs ≤
    n.factorization p + (n₀.factorization p + 1))

/-- `log N(b) ≤ log n + log K₀` for a mode twist. -/
theorem log_mode_norm_le (hP : ∀ p ∈ P, p.Prime) {n n₀ : ℕ} (hn : IsSmoothOver P n) {j : ℤ}
    (hj : j ∈ bohrModes) {c : P → ℤ} (hc : c ∈ Fintype.piFinset (fun _ : P => bohrModes)) :
    Real.log ((vecNum (vecOf P n - (j • vecOf P n₀ + c)) : ℝ) *
        vecDen (vecOf P n - (j • vecOf P n₀ + c))) ≤
      Real.log n + Real.log (twistBound P n₀) := by
  have h := log_mode_norm_le_prod hP hj hc (n := n) (n₀ := n₀)
  rwa [prod_pow_factorization_eq hn] at h

/-- The reduced denominator of a mode twist is at most `K₀`. -/
theorem vecDen_mode_le (hP : ∀ p ∈ P, p.Prime) {n n₀ : ℕ} {j : ℤ} (hj : j ∈ bohrModes)
    {c : P → ℤ} (hc : c ∈ Fintype.piFinset (fun _ : P => bohrModes)) :
    vecDen (vecOf P n - (j • vecOf P n₀ + c)) ≤ twistBound P n₀ := by
  unfold vecDen twistBound
  refine Finset.prod_le_prod' fun p _ => Nat.pow_le_pow_right (hP p p.2).pos ?_
  have := (mode_coord_bounds (n := n) (n₀ := n₀) hj hc p).2.2
  omega

/-! ## Rankin sums over a logarithmically summable sequence -/

section Rankin

variable {v : ℕ → ℝ} {J : ℕ}

theorem one_add_log_nonneg (n : ℕ) : 0 ≤ 1 + Real.log n := by
  have := Real.log_natCast_nonneg n
  linarith

/-- `Σ_{n ∈ F} |v(n)| ≤ (1 + T)^J Σ_n |v(n)|(1 + log n)^{−J}` for `log n ≤ T` on `F`. -/
theorem sum_abs_le_of_log_le (hs : Summable fun n : ℕ => |v n| * ((1 + Real.log n) ^ J)⁻¹)
    {F : Finset ℕ} {T : ℝ} (hT0 : 0 ≤ T) (hF : ∀ n ∈ F, Real.log n ≤ T) :
    ∑ n ∈ F, |v n| ≤ (1 + T) ^ J * ∑' n : ℕ, |v n| * ((1 + Real.log n) ^ J)⁻¹ := by
  have hpt : ∀ n ∈ F, |v n| ≤ (1 + T) ^ J * (|v n| * ((1 + Real.log n) ^ J)⁻¹) := by
    intro n hn
    have h0 := one_add_log_nonneg n
    have hpos : 0 < (1 + Real.log n) ^ J := pow_pos (by linarith [Real.log_natCast_nonneg n]) J
    have hle : (1 + Real.log n) ^ J ≤ (1 + T) ^ J := pow_le_pow_left₀ h0 (by linarith [hF n hn]) J
    calc |v n| = (1 + Real.log n) ^ J * (|v n| * ((1 + Real.log n) ^ J)⁻¹) := by
          field_simp
      _ ≤ (1 + T) ^ J * (|v n| * ((1 + Real.log n) ^ J)⁻¹) :=
          mul_le_mul_of_nonneg_right hle (by positivity)
  calc ∑ n ∈ F, |v n| ≤ ∑ n ∈ F, (1 + T) ^ J * (|v n| * ((1 + Real.log n) ^ J)⁻¹) :=
        Finset.sum_le_sum hpt
    _ = (1 + T) ^ J * ∑ n ∈ F, |v n| * ((1 + Real.log n) ^ J)⁻¹ := by rw [Finset.mul_sum]
    _ ≤ (1 + T) ^ J * ∑' n : ℕ, |v n| * ((1 + Real.log n) ^ J)⁻¹ := by
        have hT : 0 ≤ (1 + T) ^ J := by positivity
        exact mul_le_mul_of_nonneg_left (hs.sum_le_tsum _ fun n _ => by positivity) hT

/-- The tail `Σ_{log n > T} |v(n)|(1 + log n)^{−K} ≤ (1 + T)^{−(K − J)} Σ_n |v(n)|(1 + log n)^{−J}`. -/
theorem tsum_tail_le (hs : Summable fun n : ℕ => |v n| * ((1 + Real.log n) ^ J)⁻¹) {K : ℕ}
    (hJK : J ≤ K) {T : ℝ} (hT0 : 0 ≤ T) :
    Summable (fun n : ℕ => if Real.log n ≤ T then 0 else |v n| * ((1 + Real.log n) ^ K)⁻¹) ∧
    ∑' n : ℕ, (if Real.log n ≤ T then 0 else |v n| * ((1 + Real.log n) ^ K)⁻¹) ≤
      ((1 + T) ^ (K - J))⁻¹ * ∑' n : ℕ, |v n| * ((1 + Real.log n) ^ J)⁻¹ := by
  have hpt : ∀ n : ℕ, (if Real.log n ≤ T then 0 else |v n| * ((1 + Real.log n) ^ K)⁻¹) ≤
      ((1 + T) ^ (K - J))⁻¹ * (|v n| * ((1 + Real.log n) ^ J)⁻¹) := by
    intro n
    split_ifs with h
    · positivity
    · push Not at h
      have h1 : 1 ≤ 1 + Real.log n := by linarith [Real.log_natCast_nonneg n]
      have hsplit : (1 + Real.log n) ^ K = (1 + Real.log n) ^ J * (1 + Real.log n) ^ (K - J) := by
        rw [← pow_add, Nat.add_sub_cancel' hJK]
      have hle : (1 + T) ^ (K - J) ≤ (1 + Real.log n) ^ (K - J) :=
        pow_le_pow_left₀ (by linarith) (by linarith) _
      rw [hsplit, mul_inv]
      have hA : 0 ≤ |v n| * ((1 + Real.log n) ^ J)⁻¹ := by positivity
      calc |v n| * (((1 + Real.log n) ^ J)⁻¹ * ((1 + Real.log n) ^ (K - J))⁻¹)
          = |v n| * ((1 + Real.log n) ^ J)⁻¹ * ((1 + Real.log n) ^ (K - J))⁻¹ := by ring
        _ ≤ |v n| * ((1 + Real.log n) ^ J)⁻¹ * ((1 + T) ^ (K - J))⁻¹ :=
            mul_le_mul_of_nonneg_left (inv_anti₀ (by positivity) hle) hA
        _ = ((1 + T) ^ (K - J))⁻¹ * (|v n| * ((1 + Real.log n) ^ J)⁻¹) := by ring
  have hnn : ∀ n : ℕ, 0 ≤ (if Real.log n ≤ T then 0 else |v n| * ((1 + Real.log n) ^ K)⁻¹) :=
    fun n => by split_ifs <;> positivity
  have hsum := Summable.of_nonneg_of_le hnn hpt (hs.mul_left _)
  refine ⟨hsum, ?_⟩
  rw [← tsum_mul_left]
  exact hsum.tsum_le_tsum hpt (hs.mul_left _)

/-- The Rankin constant `(J+1)! 2^{J+1} e^{1/2}` bounds `(1 + log n)^{J+1} n^{−1/2}`. -/
def rankinConst (J : ℕ) : ℝ := (J + 1).factorial * 2 ^ (J + 1) * Real.exp (1 / 2)

theorem one_add_log_pow_mul_inv_sqrt_le (J : ℕ) (n : ℕ) :
    (1 + Real.log n) ^ (J + 1) * (Real.sqrt n)⁻¹ ≤ rankinConst J := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, Real.sqrt_zero, inv_zero, mul_zero]
    unfold rankinConst
    positivity
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  set x := Real.log n with hx
  have hx0 : 0 ≤ x := Real.log_natCast_nonneg n
  have hsq : (Real.sqrt n)⁻¹ = Real.exp (-(x / 2)) := by
    rw [Real.sqrt_eq_rpow, Real.rpow_def_of_pos hn0, ← Real.exp_neg, hx]
    ring_nf
  rw [hsq]
  have h := Real.pow_div_factorial_le_exp (x := (1 + x) / 2) (by positivity) (J + 1)
  have hf : (0 : ℝ) < (J + 1).factorial := by exact_mod_cast (J + 1).factorial_pos
  rw [div_le_iff₀ hf, div_pow] at h
  have h2 : (1 + x) ^ (J + 1) ≤ (J + 1).factorial * 2 ^ (J + 1) * Real.exp ((1 + x) / 2) := by
    have h2pos : (0 : ℝ) < 2 ^ (J + 1) := by positivity
    rw [div_le_iff₀ h2pos] at h
    linarith
  calc (1 + x) ^ (J + 1) * Real.exp (-(x / 2))
      ≤ (J + 1).factorial * 2 ^ (J + 1) * Real.exp ((1 + x) / 2) * Real.exp (-(x / 2)) :=
        mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
    _ = rankinConst J := by
        unfold rankinConst
        rw [mul_assoc, ← Real.exp_add]
        ring_nf

/-- `Σ_n |v(n)| (1 + log n) n^{−1/2} ≤ C_J Σ_n |v(n)|(1 + log n)^{−J}`. -/
theorem tsum_abs_mul_log_inv_sqrt_le (hs : Summable fun n : ℕ => |v n| * ((1 + Real.log n) ^ J)⁻¹) :
    Summable (fun n : ℕ => |v n| * (1 + Real.log n) * (Real.sqrt n)⁻¹) ∧
    ∑' n : ℕ, |v n| * (1 + Real.log n) * (Real.sqrt n)⁻¹ ≤
      rankinConst J * ∑' n : ℕ, |v n| * ((1 + Real.log n) ^ J)⁻¹ := by
  have hpt : ∀ n : ℕ, |v n| * (1 + Real.log n) * (Real.sqrt n)⁻¹ ≤
      rankinConst J * (|v n| * ((1 + Real.log n) ^ J)⁻¹) := by
    intro n
    have h0 : 0 < 1 + Real.log n := by linarith [Real.log_natCast_nonneg n]
    have hR := one_add_log_pow_mul_inv_sqrt_le J n
    have e : |v n| * (1 + Real.log n) * (Real.sqrt n)⁻¹ = (|v n| * ((1 + Real.log n) ^ J)⁻¹) *
        ((1 + Real.log n) ^ (J + 1) * (Real.sqrt n)⁻¹) := by
      rw [pow_succ]
      field_simp
    rw [e, mul_comm (rankinConst J)]
    exact mul_le_mul_of_nonneg_left hR (by positivity)
  have hnn : ∀ n : ℕ, 0 ≤ |v n| * (1 + Real.log n) * (Real.sqrt n)⁻¹ := fun n => by
    have := one_add_log_nonneg n
    positivity
  have hsum := Summable.of_nonneg_of_le hnn hpt (hs.mul_left _)
  refine ⟨hsum, ?_⟩
  rw [← tsum_mul_left]
  exact hsum.tsum_le_tsum hpt (hs.mul_left _)

end Rankin

/-! ## The window main term and uniform decay -/

/-- `Re ∫ ω(t) log t dt ≥ L log L`. -/
theorem re_logWindow_ge {L : ℝ} (hL : 2 ≤ L) : L * Real.log L ≤ (logWindow L).re := by
  have hL0 : 0 < L := by linarith
  have hη : (0 : ℝ) < L / 2 := by linarith
  have hint : Integrable (fun t => notchWindow L t * (Real.log t : ℂ)) :=
    integrable_notchWindow_mul_of_continuousOn hL0
      ((Complex.continuous_ofReal.comp_continuousOn (Real.continuousOn_log.mono fun t ht => by
        simp only [mem_compl_iff, mem_singleton_iff]
        linarith [ht.1])))
  have hre : (logWindow L).re = ∫ t, blockWindow L (2 * L) (L / 2) t * Real.log t := by
    unfold logWindow
    have h := integral_re hint
    simp only [RCLike.re_to_complex] at h
    rw [← h]
    refine integral_congr_ae (Eventually.of_forall fun t => ?_)
    simp [notchWindow, blockWindowC]
  rw [hre]
  have hpt : ∀ t, (Icc L (2 * L)).indicator (fun _ => Real.log L) t ≤
      blockWindow L (2 * L) (L / 2) t * Real.log t := by
    intro t
    by_cases ht : t ∈ Icc L (2 * L)
    · rw [indicator_of_mem ht, blockWindow_eq_one hη ht.1 ht.2, one_mul]
      exact Real.log_le_log hL0 ht.1
    · rw [indicator_of_notMem ht]
      rcases le_or_gt 1 t with h1 | h1
      · exact mul_nonneg (blockWindow_nonneg _ _ _ _) (Real.log_nonneg h1)
      · rw [blockWindow_eq_zero_of_le hη (by linarith), zero_mul]
  have hi2 : Integrable (fun t => blockWindow L (2 * L) (L / 2) t * Real.log t) := by
    have := hint.re
    refine this.congr (Eventually.of_forall fun t => ?_)
    simp [notchWindow, blockWindowC]
  calc L * Real.log L = ∫ t, (Icc L (2 * L)).indicator (fun _ => Real.log L) t := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const,
          Real.volume_real_Icc_of_le (by linarith), smul_eq_mul]
        ring
    _ ≤ ∫ t, blockWindow L (2 * L) (L / 2) t * Real.log t :=
        integral_mono ((integrableOn_const (by simp)).integrable_indicator measurableSet_Icc) hi2 hpt

/-- `‖ζ(½+it)‖² ≤ 81 t²` for `t ≥ 8`. -/
theorem norm_zetaSq_le {t : ℝ} (ht : 8 ≤ t) : ‖zetaSq t‖ ≤ 81 * t ^ 2 := by
  rw [← zetaPairC_ofReal]
  unfold zetaPairC
  have e1 := norm_riemannZeta_half_add_mul_I_le (w := (t : ℂ)) (t := t) (by linarith)
    (by simp) (by simp; rw [abs_of_nonneg (by linarith)]; linarith)
    (by simp; rw [abs_of_nonneg (by linarith)]; linarith)
  have e2 := norm_riemannZeta_half_add_mul_I_le (w := -(t : ℂ)) (t := t) (by linarith)
    (by simp) (by simp; rw [abs_of_nonneg (by linarith)]; linarith)
    (by simp; rw [abs_of_nonneg (by linarith)]; linarith)
  rw [norm_mul]
  calc ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + (t : ℂ) * I)‖ *
        ‖riemannZeta (((1 / 2 : ℝ) : ℂ) + -(t : ℂ) * I)‖ ≤ (9 * t) * (9 * t) :=
        mul_le_mul e1 e2 (norm_nonneg _) (by linarith)
    _ = 81 * t ^ 2 := by ring

/-- **Uniform decay of the twisted moment**: `‖∫ ω|ζ|² e^{−iξt}‖ (1 + |ξ|)^K ≤ C L³`. -/
theorem exists_norm_twistedMoment_mul_pow_le (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 16 ≤ L → ∀ ξ : ℝ,
      ‖ZetaNotch.twistedMoment L ξ‖ * (1 + |ξ|) ^ K ≤ C * L ^ 3 := by
  have hc := crudeJetConst_nonneg K
  refine ⟨2 ^ K * (1013 + 2 * crudeJetConst K), by positivity, fun {L} hL ξ => ?_⟩
  have hL0 : 0 < L := by linarith
  have htriv : ‖ZetaNotch.twistedMoment L ξ‖ ≤ 1013 * L ^ 3 := by
    have h := norm_integral_notchWindow_mul_cexp_le_trivial hL0 (G := zetaSq)
      (A := 81 * (5 * L / 2) ^ 2) (ξ := ξ) (fun t ht => (norm_zetaSq_le (by linarith [ht.1])).trans
        (by nlinarith [ht.1, ht.2]))
    unfold ZetaNotch.twistedMoment
    refine h.trans ?_
    nlinarith [pow_pos hL0 3]
  rcases le_or_gt |ξ| 1 with h1 | h1
  · have hp : (1 + |ξ|) ^ K ≤ 2 ^ K := pow_le_pow_left₀ (by positivity) (by linarith) K
    calc ‖ZetaNotch.twistedMoment L ξ‖ * (1 + |ξ|) ^ K ≤ (1013 * L ^ 3) * 2 ^ K :=
          mul_le_mul htriv hp (by positivity) (by positivity)
      _ ≤ 2 ^ K * (1013 + 2 * crudeJetConst K) * L ^ 3 := by
          have : 0 ≤ 2 ^ K * (2 * crudeJetConst K) * L ^ 3 := by positivity
          nlinarith
  · have hξ : ξ ≠ 0 := fun h => by rw [h, abs_zero] at h1; linarith
    have hcr := norm_twistedMoment_le_pow K hL hξ
    have hp : (1 + |ξ|) ^ K ≤ (2 * |ξ|) ^ K := pow_le_pow_left₀ (by positivity) (by linarith) K
    have hξK : 0 < |ξ| ^ K := pow_pos (by linarith) K
    calc ‖ZetaNotch.twistedMoment L ξ‖ * (1 + |ξ|) ^ K ≤ (2 * crudeJetConst K * L ^ 3 / |ξ| ^ K) *
          (2 * |ξ|) ^ K := mul_le_mul hcr hp (by positivity) (by positivity)
      _ = 2 ^ K * (2 * crudeJetConst K) * L ^ 3 := by
          rw [mul_pow]
          field_simp
      _ ≤ 2 ^ K * (1013 + 2 * crudeJetConst K) * L ^ 3 := by
          have : 0 ≤ 2 ^ K * 1013 * L ^ 3 := by positivity
          nlinarith

/-- **Uniform decay of the weighted moment.** -/
theorem exists_norm_weightedMoment_mul_pow_le (P : Finset ℕ) (ε : ℝ) (n₀ : ℕ) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {L : ℝ}, 16 ≤ L → ∀ y : ℝ,
      ‖ZetaNotch.weightedMoment L (notchWeight P ε n₀) y‖ * (1 + |y|) ^ K ≤ C * L ^ 3 := by
  classical
  obtain ⟨C, hC, hdec⟩ := exists_norm_twistedMoment_mul_pow_le K
  set B : ℝ := ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
    |modeCoeff ε j c| * (1 + |modeFreq n₀ j c|) ^ K with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun c _ => by positivity
  refine ⟨B * C, mul_nonneg hB0 hC, fun {L} hL y => ?_⟩
  have hL0 : 0 < L := by linarith
  rw [weightedMoment_notchWeight_eq hL0]
  have hpt : ∀ (j : ℤ) (c : P → ℤ),
      ‖(modeCoeff ε j c : ℂ) * ZetaNotch.twistedMoment L (y - modeFreq n₀ j c)‖ *
      (1 + |y|) ^ K ≤ |modeCoeff ε j c| * (1 + |modeFreq n₀ j c|) ^ K * (C * L ^ 3) := by
    intro j c
    have hpe := RHTower.WeilRegular.one_add_abs_pow_le_mul K (modeFreq n₀ j c) y
    rw [abs_sub_comm] at hpe
    have hd := hdec hL (y - modeFreq n₀ j c)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    calc |modeCoeff ε j c| * ‖ZetaNotch.twistedMoment L (y - modeFreq n₀ j c)‖ * (1 + |y|) ^ K
        ≤ |modeCoeff ε j c| * ‖ZetaNotch.twistedMoment L (y - modeFreq n₀ j c)‖ *
            ((1 + |modeFreq n₀ j c|) ^ K * (1 + |y - modeFreq n₀ j c|) ^ K) :=
          mul_le_mul_of_nonneg_left hpe (by positivity)
      _ = |modeCoeff ε j c| * (1 + |modeFreq n₀ j c|) ^ K *
            (‖ZetaNotch.twistedMoment L (y - modeFreq n₀ j c)‖ * (1 + |y - modeFreq n₀ j c|) ^ K) := by ring
      _ ≤ |modeCoeff ε j c| * (1 + |modeFreq n₀ j c|) ^ K * (C * L ^ 3) :=
          mul_le_mul_of_nonneg_left hd (by positivity)
  calc ‖∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
        (modeCoeff ε j c : ℂ) * ZetaNotch.twistedMoment L (y - modeFreq n₀ j c)‖ * (1 + |y|) ^ K
      ≤ (∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
          ‖(modeCoeff ε j c : ℂ) * ZetaNotch.twistedMoment L (y - modeFreq n₀ j c)‖) * (1 + |y|) ^ K := by
        refine mul_le_mul_of_nonneg_right ((norm_sum_le _ _).trans
          (Finset.sum_le_sum fun j _ => norm_sum_le _ _)) (by positivity)
    _ = ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
          ‖(modeCoeff ε j c : ℂ) * ZetaNotch.twistedMoment L (y - modeFreq n₀ j c)‖ * (1 + |y|) ^ K := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
    _ ≤ ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
          |modeCoeff ε j c| * (1 + |modeFreq n₀ j c|) ^ K * (C * L ^ 3) :=
        Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun c _ => hpt j c
    _ = B * C * L ^ 3 := by
        rw [hB, Finset.sum_mul]
        simp_rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun c _ => ?_
        ring

/-! ## Scale algebra -/

theorem split_tsum {f : ℕ → ℝ} (hf : Summable f) (F : Finset ℕ) :
    ∑' n, f n = ∑ n ∈ F, f n + ∑' n, (if n ∈ F then 0 else f n) := by
  classical
  have hg : Summable (fun n => if n ∈ F then f n else 0) :=
    summable_of_ne_finset_zero (s := F) fun n hn => if_neg hn
  have hh : Summable (fun n => if n ∈ F then 0 else f n) := by
    refine Summable.of_norm_bounded hf.norm fun n => ?_
    split_ifs <;> simp
  have e : ∑' n, f n =
      ∑' n, ((if n ∈ F then f n else 0) + (if n ∈ F then 0 else f n)) :=
    tsum_congr fun n => by split_ifs <;> simp
  rw [e, hg.tsum_add hh, tsum_eq_sum (s := F) (fun n hn => if_neg hn)]
  congr 1
  exact Finset.sum_congr rfl fun n hn => if_pos hn

theorem mul_exp_neg_le_one (x : ℝ) : x * Real.exp (-x) ≤ 1 := by
  have h := Real.add_one_le_exp x
  have hpos := Real.exp_pos x
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one hpos]
  linarith

/-- The error scales at `L = M^{8J}`, `δ = M^{−6J}`. -/
theorem scale_bounds {J : ℕ} (hJ : 2 ≤ J) {M : ℝ} (hM : 2 ≤ M) (K₀ : ℝ) (hK₀ : 0 ≤ K₀) :
    16 ≤ M ^ (8 * J) ∧ 0 < (M ^ (6 * J))⁻¹ ∧ (M ^ (6 * J))⁻¹ ≤ 1 / 4 ∧
    (1 + M) ^ J * (24 * (M ^ (6 * J))⁻¹ * K₀ * M ^ (8 * J) * Real.sqrt (M ^ (8 * J)) +
      (M ^ (8 * J)) ^ 2 / (M ^ (8 * J) * (M ^ (6 * J))⁻¹) ^ 5 +
      (M ^ (8 * J)) ^ 2 * Real.exp (-((M ^ (8 * J)) ^ 2) / 32)) ≤
      (24 * K₀ + 33) * 2 ^ J * M ^ (8 * J) ∧
    (M ^ (8 * J)) ^ 3 * ((1 + M) ^ (24 * J))⁻¹ ≤ 1 := by
  have hM0 : 0 < M := by linarith
  have hM1 : 1 ≤ M := by linarith
  have hpow : ∀ k : ℕ, 1 ≤ M ^ k := fun k => one_le_pow₀ hM1
  have h16 : 16 ≤ M ^ (8 * J) := by
    have : (2 : ℝ) ^ 4 ≤ M ^ (8 * J) :=
      (pow_le_pow_left₀ (by norm_num) hM 4).trans (pow_le_pow_right₀ hM1 (by omega))
    linarith [show (2 : ℝ) ^ 4 = 16 by norm_num]
  have h4 : 4 ≤ M ^ (6 * J) := by
    have : (2 : ℝ) ^ 2 ≤ M ^ (6 * J) :=
      (pow_le_pow_left₀ (by norm_num) hM 2).trans (pow_le_pow_right₀ hM1 (by omega))
    linarith [show (2 : ℝ) ^ 2 = 4 by norm_num]
  refine ⟨h16, by positivity, ?_, ?_, ?_⟩
  · rw [inv_le_comm₀ (by positivity) (by norm_num)]
    norm_num
    exact h4
  · have hsq : Real.sqrt (M ^ (8 * J)) = M ^ (4 * J) := by
      rw [show 8 * J = 2 * (4 * J) by ring, pow_mul', Real.sqrt_sq (by positivity)]
    have h1M : (1 + M) ^ J ≤ 2 ^ J * M ^ J := by
      rw [← mul_pow]
      exact pow_le_pow_left₀ (by linarith) (by linarith) J
    have t1 : 24 * (M ^ (6 * J))⁻¹ * K₀ * M ^ (8 * J) * Real.sqrt (M ^ (8 * J)) =
        24 * K₀ * M ^ (6 * J) := by
      rw [hsq]
      have : M ^ (8 * J) * M ^ (4 * J) = M ^ (6 * J) * M ^ (6 * J) := by
        rw [← pow_add, ← pow_add]; ring_nf
      rw [show 24 * (M ^ (6 * J))⁻¹ * K₀ * M ^ (8 * J) * M ^ (4 * J) =
        24 * K₀ * (M ^ (6 * J))⁻¹ * (M ^ (8 * J) * M ^ (4 * J)) by ring, this]
      field_simp
    have t2 : (M ^ (8 * J)) ^ 2 / (M ^ (8 * J) * (M ^ (6 * J))⁻¹) ^ 5 = M ^ (6 * J) := by
      have e : M ^ (8 * J) * (M ^ (6 * J))⁻¹ = M ^ (2 * J) := by
        rw [show 8 * J = 2 * J + 6 * J by ring, pow_add]
        field_simp
      rw [e, ← pow_mul, ← pow_mul]
      rw [div_eq_iff (by positivity), ← pow_add]
      ring_nf
    have t3 : (M ^ (8 * J)) ^ 2 * Real.exp (-((M ^ (8 * J)) ^ 2) / 32) ≤ 32 := by
      have := mul_exp_neg_le_one ((M ^ (8 * J)) ^ 2 / 32)
      rw [show -((M ^ (8 * J)) ^ 2) / 32 = -((M ^ (8 * J)) ^ 2 / 32) by ring]
      nlinarith
    rw [t1, t2]
    have hMJ : M ^ J * M ^ (6 * J) ≤ M ^ (8 * J) := by
      rw [← pow_add]
      exact pow_le_pow_right₀ hM1 (by omega)
    have hMJ' : M ^ J ≤ M ^ (8 * J) := pow_le_pow_right₀ hM1 (by omega)
    have h2J : (0 : ℝ) ≤ 2 ^ J := by positivity
    calc (1 + M) ^ J * (24 * K₀ * M ^ (6 * J) + M ^ (6 * J) +
          (M ^ (8 * J)) ^ 2 * Real.exp (-((M ^ (8 * J)) ^ 2) / 32))
        ≤ (2 ^ J * M ^ J) * (24 * K₀ * M ^ (6 * J) + M ^ (6 * J) + 32) :=
          mul_le_mul h1M (by linarith) (by positivity) (by positivity)
      _ = 2 ^ J * ((24 * K₀ + 1) * (M ^ J * M ^ (6 * J)) + 32 * M ^ J) := by ring
      _ ≤ 2 ^ J * ((24 * K₀ + 1) * M ^ (8 * J) + 32 * M ^ (8 * J)) := by
          gcongr
      _ = (24 * K₀ + 33) * 2 ^ J * M ^ (8 * J) := by ring
  · have h1 : M ^ (24 * J) ≤ (1 + M) ^ (24 * J) := pow_le_pow_left₀ hM0.le (by linarith) _
    rw [← pow_mul, show 8 * J * 3 = 24 * J by ring]
    rw [mul_inv_le_iff₀ (by positivity), one_mul]
    exact h1

/-! ## The key inequality -/

theorem primeHalf_sq (p : ℕ) : primeHalf p ^ 2 = 1 / p := by
  unfold primeHalf
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg _), one_div]

theorem eulerProduct_pos (hP : ∀ p ∈ P, p.Prime) : 0 < ∏ p : P, (1 - primeHalf p ^ 2) := by
  refine Finset.prod_pos fun p _ => ?_
  rw [primeHalf_sq]
  have h2 : (2 : ℝ) ≤ (p : ℕ) := by exact_mod_cast (hP p p.2).two_le
  rw [sub_pos, div_lt_one (by linarith)]
  linarith

/-- The envelope of a mode twist at a smooth `n` against `K₀`. -/
theorem twistEnvelope_mode_le (hP : ∀ p ∈ P, p.Prime) {C L δ : ℝ} (hC : 0 ≤ C) (hL : 0 < L)
    (hδ : 0 < δ) (K : ℕ) {n n₀ : ℕ} (hn : IsSmoothOver P n) {j : ℤ} (hj : j ∈ bohrModes)
    {c : P → ℤ} (hc : c ∈ Fintype.piFinset (fun _ : P => bohrModes)) :
    twistEnvelope C L δ K (vecOf P n - (j • vecOf P n₀ + c)) ≤
      2 * L * Real.sqrt (twistBound P n₀) * (C + 2 * Real.log (twistBound P n₀) + 2) *
          ((1 + Real.log n) * (Real.sqrt n)⁻¹) +
        C * (24 * δ * (twistBound P n₀ : ℝ) * L * Real.sqrt L + L ^ 2 / (L * δ) ^ K +
          L ^ 2 * Real.exp (-(L ^ 2) / 32)) := by
  set b := vecOf P n - (j • vecOf P n₀ + c) with hb
  have hw := weight_mode_le hP hn hj hc (n₀ := n₀)
  have hlog := log_mode_norm_le hP hn hj hc (n₀ := n₀)
  have hden := vecDen_mode_le hP hj hc (n := n) (n₀ := n₀)
  have hK1 : (1 : ℝ) ≤ twistBound P n₀ := by exact_mod_cast twistBound_pos hP n₀
  have hlogK : 0 ≤ Real.log (twistBound P n₀) := Real.log_nonneg hK1
  have hlogn : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have hN1 : (1 : ℝ) ≤ (vecNum b : ℝ) * vecDen b := by
    have h1 : (1 : ℝ) ≤ vecNum b := by exact_mod_cast vecNum_pos hP b
    have h2 : (1 : ℝ) ≤ vecDen b := by exact_mod_cast vecDen_pos hP b
    nlinarith
  have hlogN : 0 ≤ Real.log ((vecNum b : ℝ) * vecDen b) := Real.log_nonneg hN1
  have hw0 : 0 ≤ ∏ p : P, primeHalf p ^ (b p).natAbs :=
    Finset.prod_nonneg fun p _ => pow_nonneg (primeHalf_nonneg _) _
  unfold twistEnvelope
  apply add_le_add
  · calc (∏ p : P, primeHalf p ^ (b p).natAbs) *
          (2 * L * (C + 2 * Real.log ((vecNum b : ℝ) * vecDen b)))
        ≤ (Real.sqrt (twistBound P n₀) * (Real.sqrt n)⁻¹) *
            (2 * L * (C + 2 * (Real.log n + Real.log (twistBound P n₀)))) := by
          apply mul_le_mul hw _ (by positivity) (by positivity)
          gcongr
      _ ≤ 2 * L * Real.sqrt (twistBound P n₀) * (C + 2 * Real.log (twistBound P n₀) + 2) *
            ((1 + Real.log n) * (Real.sqrt n)⁻¹) := by
          have hfac : C + 2 * (Real.log n + Real.log (twistBound P n₀)) ≤
              (C + 2 * Real.log (twistBound P n₀) + 2) * (1 + Real.log n) := by nlinarith
          have hpos : 0 ≤ Real.sqrt (twistBound P n₀) * (Real.sqrt n)⁻¹ * (2 * L) := by
            positivity
          calc (Real.sqrt (twistBound P n₀) * (Real.sqrt n)⁻¹) *
                (2 * L * (C + 2 * (Real.log n + Real.log (twistBound P n₀))))
              = (Real.sqrt (twistBound P n₀) * (Real.sqrt n)⁻¹ * (2 * L)) *
                  (C + 2 * (Real.log n + Real.log (twistBound P n₀))) := by ring
            _ ≤ (Real.sqrt (twistBound P n₀) * (Real.sqrt n)⁻¹ * (2 * L)) *
                  ((C + 2 * Real.log (twistBound P n₀) + 2) * (1 + Real.log n)) :=
                mul_le_mul_of_nonneg_left hfac hpos
            _ = _ := by ring
  · apply mul_le_mul_of_nonneg_left _ hC
    gcongr

/-- **The key inequality**: at every scale `L = M^{8J}`,
`|v(n₀)| Π_p (1 − 1/p) L log L ≤ C L`. -/
theorem exists_key_bound (hP : ∀ p ∈ P, p.Prime) {v : ℕ → ℝ}
    (hsupp : ∀ n, v n ≠ 0 → IsSmoothOver P n) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |v n| ≤ 2 * Real.log n + A)
    (hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ))
    {n₀ : ℕ} (hn₀ : IsSmoothOver P n₀) :
    ∃ C : ℝ, ∀ M : ℝ, 2 ≤ M → Real.log n₀ ≤ M →
      |v n₀| * (∏ p : P, (1 - primeHalf p ^ 2)) *
          (M ^ (8 * (2 * P.card + 2)) * Real.log (M ^ (8 * (2 * P.card + 2)))) ≤
        C * M ^ (8 * (2 * P.card + 2)) := by
  classical
  set J : ℕ := 2 * P.card + 2 with hJ
  have hJ2 : 2 ≤ J := by omega
  have hs := summable_abs_mul_inv_log_pow hP hsupp hA ha
  set S : ℝ := ∑' n : ℕ, |v n| * ((1 + Real.log n) ^ J)⁻¹ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun n => by have := one_add_log_nonneg n; positivity
  set ε : ℝ := if 0 ≤ v n₀ then 1 else -1 with hε
  have hεv : v n₀ * ε = |v n₀| := by
    rw [hε]
    split_ifs with h
    · rw [mul_one, abs_of_nonneg h]
    · rw [abs_of_neg (not_le.mp h)]
      ring
  obtain ⟨C_T, hC_T, hmain⟩ := exists_norm_weightedMoment_sub_main_le hP 5
  obtain ⟨C_M, hC_M, hdecay⟩ := exists_norm_weightedMoment_mul_pow_le P ε n₀ (25 * J)
  obtain ⟨-, hR⟩ := tsum_abs_mul_log_inv_sqrt_le hs
  obtain ⟨hsR, -⟩ := tsum_abs_mul_log_inv_sqrt_le hs
  set K₀ : ℝ := (twistBound P n₀ : ℝ) with hK₀
  have hK₀1 : 1 ≤ K₀ := by rw [hK₀]; exact_mod_cast twistBound_pos hP n₀
  set B : ℝ := ∑ j ∈ bohrModes, ∑ c ∈ Fintype.piFinset (fun _ : P => bohrModes),
    |modeCoeff ε j c| with hB
  have hB0 : 0 ≤ B := Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun c _ => abs_nonneg _
  set C₅ : ℝ := C_T + 2 * Real.log K₀ + 2 with hC₅
  have hC₅0 : 0 ≤ C₅ := by have := Real.log_nonneg hK₀1; positivity
  set eP : ℝ := ∏ p : P, (1 - primeHalf p ^ 2) with heP
  have heP0 : 0 < eP := eulerProduct_pos hP
  refine ⟨B * (2 * Real.sqrt K₀ * C₅ * (rankinConst J * S) +
    C_T * ((24 * K₀ + 33) * 2 ^ J) * S) + C_M * S, fun M hM hMn₀ => ?_⟩
  set L : ℝ := M ^ (8 * J) with hL
  set δ : ℝ := (M ^ (6 * J))⁻¹ with hδ
  obtain ⟨hL16, hδ0, hδ4, hE, hL3⟩ := scale_bounds hJ2 hM K₀ (by linarith)
  have hL0 : 0 < L := by linarith
  have hL1 : 1 ≤ L := by linarith
  have hM0 : 0 ≤ M := by linarith
  -- the pairing inequality
  set q : ℝ → ℝ := notchWeight P ε n₀ with hq
  have hpair := sum_mul_re_weightedMoment_nonpos hP hsupp hA ha hPD hL0
    (notchWeight_nonneg P ε n₀) (contDiff_notchWeight P ε n₀ _)
  set f : ℕ → ℝ := fun n => v n * (ZetaNotch.weightedMoment L q (Real.log n)).re with hf
  have hMdec : ∀ n : ℕ, ‖ZetaNotch.weightedMoment L q (Real.log n)‖ ≤
      C_M * L ^ 3 * ((1 + Real.log n) ^ (25 * J))⁻¹ := by
    intro n
    have h := hdecay hL16 (Real.log n)
    rw [abs_of_nonneg (Real.log_natCast_nonneg n)] at h
    have hpos : 0 < (1 + Real.log n) ^ (25 * J) := pow_pos (by
      linarith [Real.log_natCast_nonneg n]) _
    rw [← div_eq_mul_inv, le_div_iff₀ hpos]
    exact h
  have hfle : ∀ n, ‖f n‖ ≤ C_M * L ^ 3 * (|v n| * ((1 + Real.log n) ^ J)⁻¹) := by
    intro n
    have h1 : 1 ≤ 1 + Real.log n := by linarith [Real.log_natCast_nonneg n]
    have hJK : ((1 + Real.log n) ^ (25 * J))⁻¹ ≤ ((1 + Real.log n) ^ J)⁻¹ :=
      inv_anti₀ (by positivity) (pow_le_pow_right₀ h1 (by omega))
    rw [Real.norm_eq_abs, hf, abs_mul]
    calc |v n| * |(ZetaNotch.weightedMoment L q (Real.log n)).re|
        ≤ |v n| * (C_M * L ^ 3 * ((1 + Real.log n) ^ (25 * J))⁻¹) :=
          mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (hMdec n)) (abs_nonneg _)
      _ ≤ |v n| * (C_M * L ^ 3 * ((1 + Real.log n) ^ J)⁻¹) := by gcongr
      _ = C_M * L ^ 3 * (|v n| * ((1 + Real.log n) ^ J)⁻¹) := by ring
  have hfs : Summable f := Summable.of_norm_bounded (hs.mul_left _) hfle
  -- the finite set of small smooth twists
  set F : Finset ℕ := (Finset.range (⌊Real.exp M⌋₊ + 1)).filter
    (fun n => IsSmoothOver P n ∧ Real.log n ≤ M) with hF
  have hFmem : ∀ n, n ∈ F ↔ IsSmoothOver P n ∧ Real.log n ≤ M := by
    intro n
    rw [hF, Finset.mem_filter, Finset.mem_range]
    constructor
    · exact fun h => h.2
    · intro h
      refine ⟨?_, h⟩
      have hn0 : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by have := h.1.1; omega)
      have : (n : ℝ) ≤ Real.exp M := by
        rw [← Real.exp_log hn0]
        exact Real.exp_le_exp.mpr h.2
      have := Nat.le_floor this
      omega
  have hn₀F : n₀ ∈ F := (hFmem n₀).mpr ⟨hn₀, hMn₀⟩
  rw [split_tsum hfs F] at hpair
  -- the main term on `F`
  set logW : ℂ := logWindow L with hlogW
  set E : ℕ → ℂ := fun n => ZetaNotch.weightedMoment L q (Real.log n) -
    ((if n = n₀ then ε * eP else 0 : ℝ) : ℂ) * logW with hEdef
  have hfF : ∑ n ∈ F, f n = |v n₀| * eP * logW.re + ∑ n ∈ F, v n * (E n).re := by
    have hpt : ∀ n ∈ F, f n = (if n = n₀ then v n * (ε * eP) * logW.re else 0) +
        v n * (E n).re := by
      intro n _
      simp only [hf, hEdef, Complex.sub_re, Complex.re_ofReal_mul]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_ite_eq' F n₀, if_pos hn₀F]
    rw [show v n₀ * (ε * eP) * logW.re = (v n₀ * ε) * eP * logW.re by ring, hεv]
  rw [hfF] at hpair
  -- bound on the remainders over `F`
  have hEb : ∀ n ∈ F, ‖E n‖ ≤ B * (2 * L * Real.sqrt K₀ * C₅ *
      ((1 + Real.log n) * (Real.sqrt n)⁻¹) + C_T * (24 * δ * K₀ * L * Real.sqrt L +
        L ^ 2 / (L * δ) ^ 5 + L ^ 2 * Real.exp (-(L ^ 2) / 32))) := by
    intro n hn
    have hsn := ((hFmem n).mp hn).1
    have h := hmain hL16 hδ0 hδ4 ε hsn hn₀
    refine h.trans ?_
    rw [hB, Finset.sum_mul]
    refine Finset.sum_le_sum fun j hj => ?_
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun c hc => ?_
    exact mul_le_mul_of_nonneg_left (twistEnvelope_mode_le hP hC_T hL0 hδ0 5 hsn hj hc)
      (abs_nonneg _)
  have hsumF : ∑ n ∈ F, |v n| * ‖E n‖ ≤ B * (2 * Real.sqrt K₀ * C₅ * (rankinConst J * S) +
      C_T * ((24 * K₀ + 33) * 2 ^ J) * S) * L := by
    set U : ℝ := 24 * δ * K₀ * L * Real.sqrt L + L ^ 2 / (L * δ) ^ 5 +
      L ^ 2 * Real.exp (-(L ^ 2) / 32) with hU
    have hU0 : 0 ≤ U := by positivity
    have h1 : ∑ n ∈ F, |v n| * ‖E n‖ ≤ ∑ n ∈ F, (B * (2 * L * Real.sqrt K₀ * C₅) *
        (|v n| * (1 + Real.log n) * (Real.sqrt n)⁻¹) + B * C_T * U * |v n|) := by
      refine Finset.sum_le_sum fun n hn => ?_
      calc |v n| * ‖E n‖ ≤ |v n| * (B * (2 * L * Real.sqrt K₀ * C₅ *
            ((1 + Real.log n) * (Real.sqrt n)⁻¹) + C_T * U)) :=
            mul_le_mul_of_nonneg_left (hEb n hn) (abs_nonneg _)
        _ = _ := by ring
    have h2 : ∑ n ∈ F, |v n| * (1 + Real.log n) * (Real.sqrt n)⁻¹ ≤ rankinConst J * S :=
      (hsR.sum_le_tsum F fun n _ => by have := one_add_log_nonneg n; positivity).trans hR
    have h3 : ∑ n ∈ F, |v n| ≤ (1 + M) ^ J * S :=
      sum_abs_le_of_log_le hs hM0 fun n hn => ((hFmem n).mp hn).2
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at h1
    refine h1.trans ?_
    have hE' : (1 + M) ^ J * U ≤ (24 * K₀ + 33) * 2 ^ J * L := hE
    calc B * (2 * L * Real.sqrt K₀ * C₅) * ∑ n ∈ F, |v n| * (1 + Real.log n) * (Real.sqrt n)⁻¹ +
          B * C_T * U * ∑ n ∈ F, |v n|
        ≤ B * (2 * L * Real.sqrt K₀ * C₅) * (rankinConst J * S) +
            B * C_T * U * ((1 + M) ^ J * S) := by
          gcongr
      _ = B * (2 * Real.sqrt K₀ * C₅ * (rankinConst J * S)) * L +
            B * C_T * S * ((1 + M) ^ J * U) := by ring
      _ ≤ B * (2 * Real.sqrt K₀ * C₅ * (rankinConst J * S)) * L +
            B * C_T * S * ((24 * K₀ + 33) * 2 ^ J * L) := by gcongr
      _ = _ := by ring
  -- bound on the tail
  have htail := tsum_tail_le hs (K := 25 * J) (by omega) hM0
  have hhle : ∀ n : ℕ, |if n ∈ F then 0 else f n| ≤ C_M * L ^ 3 *
      (if Real.log n ≤ M then 0 else |v n| * ((1 + Real.log n) ^ (25 * J))⁻¹) := by
    intro n
    by_cases hnF : n ∈ F
    · rw [if_pos hnF, abs_zero]
      split_ifs <;> positivity
    · rw [if_neg hnF]
      by_cases hv : v n = 0
      · simp only [hf, hv, zero_mul, abs_zero]
        split_ifs <;> positivity
      · have hsn := hsupp n hv
        have hlog : ¬ Real.log n ≤ M := fun h => hnF ((hFmem n).mpr ⟨hsn, h⟩)
        rw [if_neg hlog, hf, abs_mul]
        calc |v n| * |(ZetaNotch.weightedMoment L q (Real.log n)).re|
            ≤ |v n| * (C_M * L ^ 3 * ((1 + Real.log n) ^ (25 * J))⁻¹) :=
              mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (hMdec n))
                (abs_nonneg _)
          _ = _ := by ring
  have hhs : Summable (fun n => if n ∈ F then 0 else f n) :=
    Summable.of_norm_bounded (htail.1.mul_left (C_M * L ^ 3)) hhle
  have htailb : |∑' n, (if n ∈ F then 0 else f n)| ≤ C_M * S * L := by
    calc |∑' n, (if n ∈ F then 0 else f n)| ≤ ∑' n : ℕ, |if n ∈ F then 0 else f n| := by
          rw [← Real.norm_eq_abs]
          refine (norm_tsum_le_tsum_norm hhs.norm).trans (le_of_eq ?_)
          simp only [Real.norm_eq_abs]
      _ ≤ ∑' n : ℕ, C_M * L ^ 3 *
            (if Real.log n ≤ M then 0 else |v n| * ((1 + Real.log n) ^ (25 * J))⁻¹) :=
          hhs.abs.tsum_le_tsum hhle (htail.1.mul_left _)
      _ = C_M * L ^ 3 * ∑' n : ℕ,
            (if Real.log n ≤ M then 0 else |v n| * ((1 + Real.log n) ^ (25 * J))⁻¹) :=
          tsum_mul_left
      _ ≤ C_M * L ^ 3 * (((1 + M) ^ (25 * J - J))⁻¹ * S) :=
          mul_le_mul_of_nonneg_left htail.2 (by positivity)
      _ = C_M * S * (L ^ 3 * ((1 + M) ^ (24 * J))⁻¹) := by
          rw [show 25 * J - J = 24 * J by omega]
          ring
      _ ≤ C_M * S * 1 := mul_le_mul_of_nonneg_left hL3 (by positivity)
      _ ≤ C_M * S * L := mul_le_mul_of_nonneg_left hL1 (by positivity)
  -- assemble
  have hlogWre := re_logWindow_ge (show 2 ≤ L by linarith)
  have hFabs : |∑ n ∈ F, v n * (E n).re| ≤ ∑ n ∈ F, |v n| * ‖E n‖ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (abs_nonneg _)
  have hmainpos : |v n₀| * eP * (L * Real.log L) ≤ |v n₀| * eP * logW.re :=
    mul_le_mul_of_nonneg_left hlogWre (by positivity)
  have h1 := neg_abs_le (∑ n ∈ F, v n * (E n).re)
  have h2 := neg_abs_le (∑' n, (if n ∈ F then 0 else f n))
  linarith [hsumF, htailb, hFabs, hmainpos, hpair]

/-! ## The theorem -/

/-- **Weil-cone rigidity on finitely generated multiplicative supports.** If `v` is supported on
the `P`-smooth numbers, `|v(n)| ≤ 2 log n + A`, and `−ψ_v` is positive definite, then `v = 0`. -/
theorem eq_zero_of_positiveDefinite_neg_nullPotential (hP : ∀ p ∈ P, p.Prime) {v : ℕ → ℝ}
    (hsupp : ∀ n, v n ≠ 0 → IsSmoothOver P n) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |v n| ≤ 2 * Real.log n + A)
    (hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ)) :
    v = 0 := by
  funext n₀
  by_contra hne
  have hn₀ := hsupp n₀ hne
  obtain ⟨C, hC⟩ := exists_key_bound hP hsupp hA ha hPD hn₀
  set J : ℕ := 2 * P.card + 2 with hJ
  have hJ0 : (0 : ℝ) < 8 * J := by positivity
  set a : ℝ := |v n₀| * ∏ p : P, (1 - primeHalf p ^ 2) with ha'
  have ha0 : 0 < a := mul_pos (abs_pos.mpr hne) (eulerProduct_pos hP)
  -- choose `M` with `a · 8J log M > C`
  set M : ℝ := max (max 2 (Real.log n₀)) (Real.exp (|C| / (a * (8 * J)) + 1)) with hM
  have hM2 : 2 ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hMn : Real.log n₀ ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hMe : Real.exp (|C| / (a * (8 * J)) + 1) ≤ M := le_max_right _ _
  have hM0 : 0 < M := by linarith
  have hlogM : |C| / (a * (8 * J)) + 1 ≤ Real.log M := by
    rw [← Real.log_exp (|C| / (a * (8 * J)) + 1)]
    exact Real.log_le_log (Real.exp_pos _) hMe
  have hkey := hC M hM2 hMn
  set L : ℝ := M ^ (8 * J) with hL
  have hL0 : 0 < L := by positivity
  have hlogL : Real.log L = 8 * J * Real.log M := by
    rw [hL, Real.log_pow]
    push_cast
    ring
  rw [hlogL] at hkey
  -- `a · (L · 8J log M) ≤ C L` forces `a · 8J log M ≤ C`
  have h1 : a * (8 * J * Real.log M) ≤ C := by
    have : a * (8 * J * Real.log M) * L ≤ C * L := by
      calc a * (8 * J * Real.log M) * L = a * (L * (8 * J * Real.log M)) := by ring
        _ ≤ C * L := hkey
    exact le_of_mul_le_mul_right this hL0
  have h2 : |C| < a * (8 * J * Real.log M) := by
    have hpos : 0 < a * (8 * J) := mul_pos ha0 hJ0
    have : |C| / (a * (8 * J)) < Real.log M := by linarith
    rw [div_lt_iff₀ hpos] at this
    linarith
  linarith [le_abs_self C]

/-- If `+ψ_v` is positive definite, `v = 0` as well. -/
theorem eq_zero_of_positiveDefinite_nullPotential (hP : ∀ p ∈ P, p.Prime) {v : ℕ → ℝ}
    (hsupp : ∀ n, v n ≠ 0 → IsSmoothOver P n) {A : ℝ} (hA : 0 ≤ A)
    (ha : ∀ n, |v n| ≤ 2 * Real.log n + A)
    (hPD : PositiveDefiniteOnReal fun y => ((RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ)) :
    v = 0 := by
  have hneg := eq_zero_of_positiveDefinite_neg_nullPotential hP (v := fun n => -v n)
    (fun n h => hsupp n (fun h' => h (by rw [h', neg_zero]))) hA
    (fun n => by rw [abs_neg]; exact ha n)
    (by simpa only [RHTower.WeilRegular.nullPotential_neg, neg_neg] using hPD)
  funext n
  have := congrFun hneg n
  simpa using this

/-- **Corollary.** A full-cone Weil-positive `lam` that agrees with `Λ` off the `P`-smooth numbers
equals `Λ` on all `n ≥ 2`. -/
theorem eq_vonMangoldt_of_weilPositiveFull (hP : ∀ p ∈ P, p.Prime) {lam : ℕ → ℝ}
    (hW : RHTower.WeilPositiveFull lam)
    (hoff : ∀ n, 2 ≤ n → ¬ IsSmoothOver P n → lam n = ArithmeticFunction.vonMangoldt n) :
    ∀ n, 2 ≤ n → lam n = ArithmeticFunction.vonMangoldt n := by
  set v := RHTower.WeilExcess.weilDeviation lam with hv
  obtain ⟨C, hC0, hC⟩ := RHTower.WeilExcess.exists_abs_weilDeviation_le hW
  have hsupp : ∀ n, v n ≠ 0 → IsSmoothOver P n := by
    intro n hn
    by_contra hs
    apply hn
    rw [hv, RHTower.WeilExcess.weilDeviation]
    split_ifs with h2
    · rw [hoff n h2 hs, sub_self, zero_div]
    · rfl
  have hPD : PositiveDefiniteOnReal fun y => ((-RHTower.WeilRegular.nullPotential v y : ℝ) : ℂ) :=
    RHTower.WeilExcess.positiveDefiniteOnReal_neg_deviationPotential hW
  have h0 := eq_zero_of_positiveDefinite_neg_nullPotential hP hsupp hC0 hC hPD
  intro n hn
  have h := congrFun h0 n
  rw [hv, RHTower.WeilExcess.weilDeviation, if_pos hn, Pi.zero_apply] at h
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n))
  rw [div_eq_zero_iff] at h
  rcases h with h | h
  · linarith
  · exact absurd h hs.ne'

end RHTower.WeilFiniteSupport
