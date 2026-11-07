import GaloisForLFunctions.PrimeTorusTheory.TheDiscrepancyOfTheOrbit

/-!
# The boxes of the torus

The resonator of `exists_column_ge` reaches every half-space at the Kronecker scale, and a half-space controls the average coordinate. A box controls every coordinate.

Replace the Fejér kernel by the concentrated kernel `w(x)^e`, `w(x) = (1 + cos x)/2`. Its Fourier coefficients are binomial and sum to `1`, so a product over primes has total coefficient mass `1` whatever the number of primes, and the integer gap bounds its window integral with no factor from the number of terms:

`|∫_T^{T+L} Π_p w(t log p − θ_p)^{e_p} dt − L Π_p μ(e_p)| ≤ 2 D²`, `D = Π_p p^{e_p}`, `μ(e) = C(2e, e)/4^e` (`abs_integral_boxWeight_sub_le`).

If `t` is outside the box of a prime `q`, then `w_q ≤ 1 − δ`, so lowering the exponent of `q` from `2m` to `m` costs only `(1 − δ)^m`. This replaces a union bound over `r` primes by the condition `8 m r (1 − δ)^m ≤ 1`.

**Theorem** (`exists_mem_box`). Under that condition, every window of length `L > 8 (4m)^r D²`, `D = Π_p p^{2m}`, contains a time in the box `w(t log p − θ_p) > 1 − δ` for all `p`, for every target `θ`.

So `m ≍ (log r)/δ` suffices, and every window of length `exp((20/δ) y log y)` enters every box on the primes up to `y` (`eventually_exists_mem_box`), with no input from linear forms in logarithms.

**The mixing bracket.** On `[0, T]` with `T θ(y) ≪ 2^{π(y)}` some box at `δ = ½` is missed (`exists_box_missed`). So the mixing time for boxes satisfies `(log 2) π(y) ≲ log T_mix ≲ 40 y log y`. The half-space scale `exp(c_m y)` lies inside this bracket.
-/

open Complex Finset Filter Topology

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- The bump `(1 + cos x)/2`: `1` at the corner `x = 0`, and `0` at the antipode. -/
def bump (x : ℝ) : ℝ := (1 + Real.cos x) / 2

theorem bump_nonneg (x : ℝ) : 0 ≤ bump x := by
  unfold bump
  linarith [Real.neg_one_le_cos x]

theorem bump_le_one (x : ℝ) : bump x ≤ 1 := by
  unfold bump
  linarith [Real.cos_le_one x]

theorem continuous_bump : Continuous bump := by
  unfold bump
  fun_prop

/-- The unit `e^{iy}`. -/
def ePhase (y : ℝ) : ℂ := cexp ((y : ℂ) * I)

theorem norm_ePhase (y : ℝ) : ‖ePhase y‖ = 1 := Complex.norm_exp_ofReal_mul_I y

theorem ePhase_ne_zero (y : ℝ) : ePhase y ≠ 0 := Complex.exp_ne_zero _

theorem ePhase_add (a b : ℝ) : ePhase (a + b) = ePhase a * ePhase b := by
  unfold ePhase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem ePhase_zero : ePhase 0 = 1 := by
  simp [ePhase]

theorem ePhase_neg (a : ℝ) : ePhase (-a) = (ePhase a)⁻¹ := by
  unfold ePhase
  rw [← Complex.exp_neg]
  congr 1
  push_cast
  ring

theorem ePhase_pow (a : ℝ) (n : ℕ) : ePhase a ^ n = ePhase ((n : ℝ) * a) := by
  unfold ePhase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

theorem bump_eq (x : ℝ) : (bump x : ℂ) = (ePhase (x / 2) + (ePhase (x / 2))⁻¹) ^ 2 / 4 := by
  have hu := ePhase_ne_zero (x / 2)
  have h1 : ePhase (x / 2) ^ 2 = ePhase x := by
    rw [ePhase_pow]
    congr 1
    push_cast
    ring
  have h2 : ((ePhase (x / 2))⁻¹) ^ 2 = ePhase (-x) := by
    rw [ePhase_neg, ← h1, inv_pow]
  have hcos : Complex.cos (x : ℂ) = (ePhase x + ePhase (-x)) / 2 := by
    rw [Complex.cos]
    unfold ePhase
    push_cast
    ring_nf
  have e : (ePhase (x / 2) + (ePhase (x / 2))⁻¹) ^ 2 =
      ePhase (x / 2) ^ 2 + 2 + ((ePhase (x / 2))⁻¹) ^ 2 := by
    field_simp
    ring
  rw [e, h1, h2]
  unfold bump
  push_cast
  rw [hcos]
  ring

/-- **The binomial Fourier expansion of the bump.** -/
theorem bump_pow_eq (x : ℝ) (e : ℕ) :
    ((bump x ^ e : ℝ) : ℂ) = ∑ k ∈ range (2 * e + 1),
      (((2 * e).choose k : ℝ) / 4 ^ e : ℝ) * ePhase (((e : ℝ) - k) * x) := by
  have h4 : ((4 : ℂ)) ^ e ≠ 0 := pow_ne_zero _ (by norm_num)
  push_cast
  rw [bump_eq, div_pow, ← pow_mul, add_comm, add_pow, Finset.sum_div, mul_comm 2 e]
  refine Finset.sum_congr (by rw [mul_comm]) fun k hk => ?_
  have hk' : k ≤ e * 2 := by
    have := Finset.mem_range.mp hk
    omega
  have e1 : ((ePhase (x / 2))⁻¹) ^ k * ePhase (x / 2) ^ (e * 2 - k) = ePhase (((e : ℝ) - k) * x) := by
    rw [← ePhase_neg, ePhase_pow, ePhase_pow, ← ePhase_add]
    congr 1
    rw [Nat.cast_sub hk']
    push_cast
    ring
  rw [e1]
  field_simp

/-- The mean `C(2e, e)/4^e` of `w^e`. -/
def binomMean (e : ℕ) : ℝ := ((2 * e).choose e : ℝ) / 4 ^ e

theorem binomMean_pos (e : ℕ) : 0 < binomMean e := by
  unfold binomMean
  have : 0 < (2 * e).choose e := Nat.choose_pos (by omega)
  positivity

theorem binomMean_le_one (e : ℕ) : binomMean e ≤ 1 := by
  unfold binomMean
  rw [div_le_one (by positivity)]
  have h := Nat.choose_le_two_pow (2 * e) e
  have e4 : (2 : ℕ) ^ (2 * e) = 4 ^ e := by
    rw [pow_mul]
    norm_num
  rw [e4] at h
  exact_mod_cast h

/-- `μ(n) ≥ 1/(2n)`. -/
theorem one_le_binomMean_mul {n : ℕ} (hn : 0 < n) : 1 ≤ binomMean n * (2 * (n : ℝ)) := by
  have h := Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
  have h' : (4 : ℝ) ^ n ≤ 2 * (n : ℝ) * (n.centralBinom : ℝ) := by exact_mod_cast h
  unfold binomMean
  rw [← Nat.centralBinom_eq_two_mul_choose, div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
  linarith

theorem sum_choose_div (e : ℕ) :
    ∑ k ∈ range (2 * e + 1), (((2 * e).choose k : ℝ) / 4 ^ e : ℝ) = 1 := by
  rw [← Finset.sum_div, div_eq_one_iff_eq (by positivity)]
  have h := Nat.sum_range_choose (2 * e)
  have e4 : (2 : ℕ) ^ (2 * e) = 4 ^ e := by
    rw [pow_mul]
    norm_num
  rw [e4] at h
  exact_mod_cast h

/-- The factorization of a product of prime powers over a set of primes reads off the exponents. -/
theorem factorization_prod_pow {Y : Finset ℕ} (hY : ∀ p ∈ Y, p.Prime) (κ : Y → ℕ) (q : Y) :
    (∏ i : Y, (i : ℕ) ^ κ i).factorization q = κ q := by
  classical
  have hne : ∀ i ∈ (Finset.univ : Finset Y), (i : ℕ) ^ κ i ≠ 0 := fun i _ =>
    pow_ne_zero _ (hY i i.2).ne_zero
  rw [Nat.factorization_prod hne, Finsupp.finsetSum_apply,
    Finset.sum_eq_single q]
  · rw [Nat.factorization_pow, (hY q q.2).factorization]
    simp
  · intro b _ hb
    rw [Nat.factorization_pow, (hY b b.2).factorization]
    have : (b : ℕ) ≠ q := fun h => hb (Subtype.ext h)
    simp [this]
  · simp

/-- The weight `Π_p w(t log p − θ_p)^{e_p}`. -/
def boxWeight (Y : Finset ℕ) (e : ℕ → ℕ) (θ : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∏ p ∈ Y, bump (t * Real.log p - θ p) ^ e p

theorem boxWeight_nonneg (Y : Finset ℕ) (e : ℕ → ℕ) (θ : ℕ → ℝ) (t : ℝ) : 0 ≤ boxWeight Y e θ t :=
  Finset.prod_nonneg fun _ _ => pow_nonneg (bump_nonneg _) _

theorem continuous_boxWeight (Y : Finset ℕ) (e : ℕ → ℕ) (θ : ℕ → ℝ) :
    Continuous (boxWeight Y e θ) := by
  unfold boxWeight
  refine continuous_finsetProd _ fun p _ => (continuous_bump.comp ?_).pow _
  fun_prop

/-- The modulus `D = Π_p p^{e_p}`. -/
def boxD (Y : Finset ℕ) (e : ℕ → ℕ) : ℕ := ∏ p ∈ Y, p ^ e p

theorem boxD_pos {Y : Finset ℕ} (hY : ∀ p ∈ Y, p.Prime) (e : ℕ → ℕ) : 0 < boxD Y e :=
  Finset.prod_pos fun p hp => pow_pos (hY p hp).pos _

section Expansion

variable {Y : Finset ℕ} (e : ℕ → ℕ) (θ : ℕ → ℝ)

/-- The total coefficient of a multi-index. -/
def coeffOf (e : ℕ → ℕ) (κ : Y → ℕ) : ℝ :=
  ∏ i : Y, (((2 * e i).choose (κ i) : ℝ) / 4 ^ e i)

/-- The frequency of a multi-index. -/
def freqOf (e : ℕ → ℕ) (κ : Y → ℕ) : ℝ := ∑ i : Y, ((e i : ℝ) - κ i) * Real.log (i : ℕ)

/-- The phase of a multi-index. -/
def phaseOf (e : ℕ → ℕ) (θ : ℕ → ℝ) (κ : Y → ℕ) : ℝ := ∑ i : Y, ((e i : ℝ) - κ i) * θ i

/-- The multi-index set. -/
def boxIndex (Y : Finset ℕ) (e : ℕ → ℕ) : Finset (Y → ℕ) :=
  Fintype.piFinset fun i : Y => range (2 * e i + 1)

theorem coeffOf_nonneg (κ : Y → ℕ) : 0 ≤ coeffOf e κ :=
  Finset.prod_nonneg fun _ _ => by positivity

theorem sum_coeffOf : ∑ κ ∈ boxIndex Y e, coeffOf e κ = 1 := by
  unfold boxIndex coeffOf
  rw [← Finset.prod_univ_sum (fun i : Y => range (2 * e i + 1))
    (fun i k => ((2 * e i).choose k : ℝ) / 4 ^ e i)]
  exact Finset.prod_eq_one fun i _ => sum_choose_div (e i)

theorem boxWeight_expansion (t : ℝ) :
    ((boxWeight Y e θ t : ℝ) : ℂ) = ∑ κ ∈ boxIndex Y e,
      (coeffOf e κ : ℂ) * ePhase (-phaseOf e θ κ) *
        cexp (I * ((freqOf e κ : ℝ) * (t : ℝ))) := by
  have h1 : boxWeight Y e θ t = ∏ i : Y, bump (t * Real.log (i : ℕ) - θ i) ^ e i := by
    unfold boxWeight
    exact (Finset.prod_coe_sort Y fun p => bump (t * Real.log p - θ p) ^ e p).symm
  rw [h1]
  push_cast
  have h2 : ∀ i : Y, ((bump (t * Real.log (i : ℕ) - θ i) : ℂ)) ^ e i =
      ∑ k ∈ range (2 * e i + 1), (((2 * e i).choose k : ℝ) / 4 ^ e i : ℝ) *
        ePhase (((e i : ℝ) - k) * (t * Real.log (i : ℕ) - θ i)) := fun i => by
    have := bump_pow_eq (t * Real.log (i : ℕ) - θ i) (e i)
    push_cast at this ⊢
    exact this
  simp_rw [h2]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun κ _ => ?_
  rw [Finset.prod_mul_distrib]
  have h3 : ∏ i : Y, ePhase (((e i : ℝ) - κ i) * (t * Real.log (i : ℕ) - θ i)) =
      ePhase (-phaseOf e θ κ) * cexp (I * ((freqOf e κ : ℝ) * (t : ℝ))) := by
    have e1 : cexp (I * ((freqOf e κ : ℝ) * (t : ℝ))) = ePhase (freqOf e κ * t) := by
      unfold ePhase
      congr 1
      push_cast
      ring
    rw [e1, ← ePhase_add]
    unfold ePhase
    rw [← Complex.exp_sum]
    congr 1
    rw [← Finset.sum_mul, ← Complex.ofReal_sum]
    congr 2
    unfold phaseOf freqOf
    rw [Finset.sum_mul, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [h3]
  have h4 : ((coeffOf e κ : ℝ) : ℂ) = ∏ i : Y, (((((2 * e i).choose (κ i) : ℝ) / 4 ^ e i : ℝ)) : ℂ) := by
    unfold coeffOf
    push_cast
    rfl
  rw [h4]
  ring

/-- The exponent vector itself, as a multi-index. -/
theorem restrict_mem_boxIndex : (fun i : Y => e i) ∈ boxIndex Y e := by
  unfold boxIndex
  rw [Fintype.mem_piFinset]
  intro i
  exact Finset.mem_range.mpr (by omega)

theorem coeffOf_restrict : coeffOf e (fun i : Y => e i) = ∏ p ∈ Y, binomMean (e p) := by
  unfold coeffOf
  exact Finset.prod_coe_sort Y fun p => binomMean (e p)

theorem freqOf_restrict : freqOf e (fun i : Y => e i) = 0 := by
  unfold freqOf
  exact Finset.sum_eq_zero fun i _ => by simp

theorem phaseOf_restrict : phaseOf e θ (fun i : Y => e i) = 0 := by
  unfold phaseOf
  exact Finset.sum_eq_zero fun i _ => by simp

/-- The frequency is the log-distance of two integers. -/
theorem freqOf_eq (hY : ∀ p ∈ Y, p.Prime) (κ : Y → ℕ) :
    freqOf e κ = Real.log (∏ i : Y, (i : ℕ) ^ e i : ℕ) - Real.log (∏ i : Y, (i : ℕ) ^ κ i : ℕ) := by
  have hlog : ∀ f : Y → ℕ, Real.log (∏ i : Y, (i : ℕ) ^ f i : ℕ) =
      ∑ i : Y, (f i : ℝ) * Real.log (i : ℕ) := by
    intro f
    push_cast
    rw [Real.log_prod fun i _ => pow_ne_zero _ (by exact_mod_cast (hY i i.2).ne_zero)]
    exact Finset.sum_congr rfl fun i _ => Real.log_pow _ _
  rw [hlog, hlog]
  unfold freqOf
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **The integer gap for multi-indices.** Away from the exponent vector the frequency is at least `1/D²`. -/
theorem norm_integral_le (hY : ∀ p ∈ Y, p.Prime) {κ : Y → ℕ} (hκ : κ ∈ boxIndex Y e)
    (hne : κ ≠ fun i : Y => e i) (T L : ℝ) :
    ‖∫ t in T..T + L, cexp (I * ((freqOf e κ : ℝ) * (t : ℝ)))‖ ≤ 2 * (boxD Y e : ℝ) ^ 2 := by
  classical
  set a : ℕ := ∏ i : Y, (i : ℕ) ^ e i with ha
  set b : ℕ := ∏ i : Y, (i : ℕ) ^ κ i with hb
  have hab : a = boxD Y e := Finset.prod_coe_sort Y fun p => p ^ e p
  have hapos : 0 < a := Finset.prod_pos fun i _ => pow_pos (hY i i.2).pos _
  have hbpos : 0 < b := Finset.prod_pos fun i _ => pow_pos (hY i i.2).pos _
  have hneq : a ≠ b := by
    intro h
    refine hne (funext fun q => ?_)
    have h1 := factorization_prod_pow hY κ q
    have h2 := factorization_prod_pow hY (fun i : Y => e i) q
    rw [← hb] at h1
    rw [← ha, h] at h2
    rw [← h1, h2]
  have hgap := HTGeometry.inv_max_le_abs_log_sub_log hapos hbpos hneq
  rw [← freqOf_eq e hY κ] at hgap
  have hmaxpos : (0 : ℝ) < ((max a b : ℕ) : ℝ) := by
    have : 0 < max a b := lt_max_of_lt_left hapos
    exact_mod_cast this
  have hγ : freqOf e κ ≠ 0 := by
    intro h0
    rw [h0, abs_zero] at hgap
    exact absurd hgap (not_le.mpr (by positivity))
  have hI := TrigSum.norm_integral_exp_I_mul_le _ hγ T L
  refine hI.trans ?_
  -- `max(a, b) ≤ a²`
  have hble : b ≤ a ^ 2 := by
    have hsq : a ^ 2 = ∏ i : Y, (i : ℕ) ^ (2 * e i) := by
      rw [ha, ← Finset.prod_pow]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [← pow_mul]
      ring_nf
    rw [hsq]
    refine Finset.prod_le_prod' fun i _ => Nat.pow_le_pow_right (hY i i.2).pos ?_
    have := Fintype.mem_piFinset.mp hκ i
    have := Finset.mem_range.mp this
    omega
  have hale : a ≤ a ^ 2 := Nat.le_self_pow two_ne_zero a
  have hmax : ((max a b : ℕ) : ℝ) ≤ (boxD Y e : ℝ) ^ 2 := by
    rw [← hab]
    exact_mod_cast max_le hale hble
  have hpos : 0 < |freqOf e κ| := abs_pos.mpr hγ
  rw [div_le_iff₀ hpos]
  have h3 : (1 : ℝ) ≤ ((max a b : ℕ) : ℝ) * |freqOf e κ| := by
    have := mul_le_mul_of_nonneg_left hgap hmaxpos.le
    rwa [mul_inv_cancel₀ hmaxpos.ne'] at this
  nlinarith [abs_nonneg (freqOf e κ)]

/-- **The window integral of a box weight.** The coefficient mass is `1`, whatever the number of primes. -/
theorem abs_integral_boxWeight_sub_le (hY : ∀ p ∈ Y, p.Prime) (T L : ℝ) :
    |(∫ t in T..T + L, boxWeight Y e θ t) - L * ∏ p ∈ Y, binomMean (e p)| ≤
      2 * (boxD Y e : ℝ) ^ 2 := by
  classical
  have hc : ∀ κ : Y → ℕ, Continuous fun t : ℝ => (coeffOf e κ : ℂ) * ePhase (-phaseOf e θ κ) *
      cexp (I * ((freqOf e κ : ℝ) * (t : ℝ))) := fun κ => by fun_prop
  have hint : ((∫ t in T..T + L, boxWeight Y e θ t : ℝ) : ℂ) = ∑ κ ∈ boxIndex Y e,
      (coeffOf e κ : ℂ) * ePhase (-phaseOf e θ κ) *
        ∫ t in T..T + L, cexp (I * ((freqOf e κ : ℝ) * (t : ℝ))) := by
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [boxWeight_expansion e θ]
    rw [intervalIntegral.integral_finsetSum fun κ _ => (hc κ).intervalIntegrable _ _]
    refine Finset.sum_congr rfl fun κ _ => ?_
    rw [intervalIntegral.integral_const_mul]
  set κ₀ : Y → ℕ := fun i : Y => e i with hκ₀
  have hmem : κ₀ ∈ boxIndex Y e := restrict_mem_boxIndex e
  have hmain : (coeffOf e κ₀ : ℂ) * ePhase (-phaseOf e θ κ₀) *
      ∫ t in T..T + L, cexp (I * ((freqOf e κ₀ : ℝ) * (t : ℝ))) =
      ((L * ∏ p ∈ Y, binomMean (e p) : ℝ) : ℂ) := by
    rw [hκ₀, freqOf_restrict, phaseOf_restrict, coeffOf_restrict]
    simp [ePhase_zero]
    ring
  rw [← Finset.add_sum_erase _ _ hmem, hmain] at hint
  have hrest : ‖∑ κ ∈ (boxIndex Y e).erase κ₀, (coeffOf e κ : ℂ) * ePhase (-phaseOf e θ κ) *
      ∫ t in T..T + L, cexp (I * ((freqOf e κ : ℝ) * (t : ℝ)))‖ ≤ 2 * (boxD Y e : ℝ) ^ 2 := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ κ ∈ (boxIndex Y e).erase κ₀,
        ‖(coeffOf e κ : ℂ) * ePhase (-phaseOf e θ κ) *
          ∫ t in T..T + L, cexp (I * ((freqOf e κ : ℝ) * (t : ℝ)))‖ ≤
        coeffOf e κ * (2 * (boxD Y e : ℝ) ^ 2) := by
      intro κ hκ
      have hκ' := Finset.mem_erase.mp hκ
      rw [norm_mul, norm_mul, norm_ePhase, mul_one, Complex.norm_real, Real.norm_of_nonneg (coeffOf_nonneg e κ)]
      exact mul_le_mul_of_nonneg_left (norm_integral_le e hY hκ'.2 hκ'.1 T L) (coeffOf_nonneg e κ)
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_mul]
    have h1 : ∑ κ ∈ (boxIndex Y e).erase κ₀, coeffOf e κ ≤ ∑ κ ∈ boxIndex Y e, coeffOf e κ :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _) fun κ _ _ => coeffOf_nonneg e κ
    rw [sum_coeffOf] at h1
    have h2 : (0 : ℝ) ≤ 2 * (boxD Y e : ℝ) ^ 2 := by positivity
    nlinarith
  have hre : ((((∫ t in T..T + L, boxWeight Y e θ t) - L * ∏ p ∈ Y, binomMean (e p) : ℝ)) : ℂ) =
      ∑ κ ∈ (boxIndex Y e).erase κ₀, (coeffOf e κ : ℂ) * ePhase (-phaseOf e θ κ) *
        ∫ t in T..T + L, cexp (I * ((freqOf e κ : ℝ) * (t : ℝ))) := by
    rw [Complex.ofReal_sub, hint]
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hre]
  exact hrest

end Expansion

/-- The real inequality closing the box. -/
theorem box_algebra {A B X c r D L : ℝ} {m : ℝ} (hm : 1 ≤ m) (hB : B ≤ 1)
    (hX : 0 < X) (hc0 : 0 ≤ c) (hr : 0 ≤ r) (hD : 0 ≤ D) (hAm : 1 ≤ A * (4 * m))
    (hcr : 8 * m * (r * c) ≤ 1) (hL0 : 0 < L)
    (h : L * (A * X) - 2 * D ≤ c * (r * (L * (B * X) + 2 * D))) :
    L * (A * X) ≤ 8 * D := by
  have hrc0 : 0 ≤ r * c := mul_nonneg hr hc0
  have h1 : r * c ≤ 1 / (8 * m) := by
    rw [le_div_iff₀ (by positivity)]
    linarith
  have h2 : 1 / (8 * m) ≤ A / 2 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have h3 : r * c * B ≤ A / 2 := by
    have : r * c * B ≤ r * c * 1 := mul_le_mul_of_nonneg_left hB hrc0
    linarith
  have h4 : r * c ≤ 1 := by
    have : 1 / (8 * m) ≤ 1 := by
      rw [div_le_one (by positivity)]
      linarith
    linarith
  have hLX : 0 ≤ L * X := by positivity
  have h5 : (r * c * B) * (L * X) ≤ (A / 2) * (L * X) := mul_le_mul_of_nonneg_right h3 hLX
  have h6 : (r * c) * (2 * D) ≤ 1 * (2 * D) := mul_le_mul_of_nonneg_right h4 (by positivity)
  have e : c * (r * (L * (B * X) + 2 * D)) = (r * c * B) * (L * X) + (r * c) * (2 * D) := by ring
  rw [e] at h
  nlinarith

/-- **The box theorem.** See the module docstring. -/
theorem exists_mem_box {Y : Finset ℕ} (hY : ∀ p ∈ Y, p.Prime) (θ : ℕ → ℝ) {m : ℕ} (hm : 1 ≤ m)
    {δ : ℝ} (hδ1 : δ < 1) (hc : 8 * (m : ℝ) * ((Y.card : ℝ) * (1 - δ) ^ m) ≤ 1) (T : ℝ)
    {L : ℝ} (hL : 8 * (4 * (m : ℝ)) ^ Y.card * ((boxModulus Y (2 * m) : ℕ) : ℝ) ^ 2 < L) :
    ∃ t ∈ Set.Icc T (T + L), ∀ q ∈ Y, 1 - δ < bump (t * Real.log q - θ q) := by
  classical
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hLpos : 0 < L := lt_of_le_of_lt (by positivity) hL
  by_contra hcon
  push Not at hcon
  have hall : ∀ t ∈ Set.Icc T (T + L), ∃ q ∈ Y, bump (t * Real.log q - θ q) ≤ 1 - δ := hcon
  obtain ⟨q₀, hq₀, -⟩ := hall T ⟨le_rfl, by linarith⟩
  set D : ℝ := ((boxModulus Y (2 * m) : ℕ) : ℝ) ^ 2 with hD
  have hD0 : 0 ≤ D := by positivity
  set c : ℝ := (1 - δ) ^ m with hcdef
  have hc0 : 0 ≤ c := pow_nonneg (by linarith) _
  set eAll : ℕ → ℕ := fun _ => 2 * m with heAll
  set eq' : ℕ → ℕ → ℕ := fun q p => if p = q then m else 2 * m with heq'
  -- The pointwise comparison.
  have hsplit : ∀ q ∈ Y, ∀ t, boxWeight Y eAll θ t =
      bump (t * Real.log q - θ q) ^ m * boxWeight Y (eq' q) θ t := by
    intro q hq t
    unfold boxWeight
    rw [← Finset.mul_prod_erase Y _ hq, ← Finset.mul_prod_erase Y (fun p => bump (t * Real.log p - θ p) ^ eq' q p) hq]
    have e1 : ∏ p ∈ Y.erase q, bump (t * Real.log p - θ p) ^ eAll p =
        ∏ p ∈ Y.erase q, bump (t * Real.log p - θ p) ^ eq' q p := by
      refine Finset.prod_congr rfl fun p hp => ?_
      simp [heq', heAll, Finset.ne_of_mem_erase hp]
    rw [e1]
    simp only [heq', heAll, if_true]
    rw [← mul_assoc, ← pow_add]
    congr 2
    ring
  have hpt : ∀ t ∈ Set.Icc T (T + L), boxWeight Y eAll θ t ≤ c * ∑ q ∈ Y, boxWeight Y (eq' q) θ t := by
    intro t ht
    obtain ⟨q, hq, hbad⟩ := hall t ht
    rw [hsplit q hq t]
    have h1 : bump (t * Real.log q - θ q) ^ m ≤ c := pow_le_pow_left₀ (bump_nonneg _) hbad m
    have h2 : boxWeight Y (eq' q) θ t ≤ ∑ q' ∈ Y, boxWeight Y (eq' q') θ t :=
      Finset.single_le_sum (f := fun q' => boxWeight Y (eq' q') θ t)
        (fun q' _ => boxWeight_nonneg _ _ _ _) hq
    exact mul_le_mul h1 h2 (boxWeight_nonneg _ _ _ _) hc0
  -- Integrate.
  have hcont : ∀ e, Continuous (boxWeight Y e θ) := fun e => continuous_boxWeight Y e θ
  have hint : ∫ t in T..T + L, boxWeight Y eAll θ t ≤
      c * ∑ q ∈ Y, ∫ t in T..T + L, boxWeight Y (eq' q) θ t := by
    rw [← intervalIntegral.integral_finsetSum fun q _ => (hcont _).intervalIntegrable _ _,
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith) ((hcont _).intervalIntegrable _ _) ?_ hpt
    refine Continuous.intervalIntegrable ?_ _ _
    exact continuous_const.mul (continuous_finsetSum _ fun q _ => hcont _)
  -- The window integrals.
  set A : ℝ := binomMean (2 * m) with hA
  set B : ℝ := binomMean m with hB
  set r : ℕ := Y.card with hr
  have hr1 : 1 ≤ r := Finset.card_pos.mpr ⟨q₀, hq₀⟩
  set X : ℝ := A ^ (r - 1) with hX
  have hApos : 0 < A := binomMean_pos _
  have hXpos : 0 < X := by positivity
  have hAr : A ^ r = A * X := by
    rw [hX, ← pow_succ']
    congr 1
    omega
  have hDall : (boxD Y eAll : ℝ) ^ 2 = D := by
    rw [hD]
    rfl
  have hlow : L * (A * X) - 2 * D ≤ ∫ t in T..T + L, boxWeight Y eAll θ t := by
    have h1 := abs_integral_boxWeight_sub_le eAll θ hY T L
    rw [hDall] at h1
    have e1 : ∏ p ∈ Y, binomMean (eAll p) = A * X := by
      rw [← hAr]
      exact Finset.prod_const A
    rw [e1] at h1
    linarith [(abs_le.mp h1).1]
  have hupq : ∀ q ∈ Y, ∫ t in T..T + L, boxWeight Y (eq' q) θ t ≤ L * (B * X) + 2 * D := by
    intro q hq
    have h1 := abs_integral_boxWeight_sub_le (eq' q) θ hY T L
    have e1 : ∏ p ∈ Y, binomMean (eq' q p) = B * X := by
      rw [← Finset.mul_prod_erase Y _ hq]
      have e2 : ∏ p ∈ Y.erase q, binomMean (eq' q p) = X := by
        rw [Finset.prod_congr rfl (g := fun _ => A) fun p hp => by
          simp [heq', Finset.ne_of_mem_erase hp, hA], Finset.prod_const,
          Finset.card_erase_of_mem hq]
      rw [e2]
      simp [heq', hB]
    rw [e1] at h1
    have hDq : (boxD Y (eq' q) : ℝ) ^ 2 ≤ D := by
      rw [← hDall]
      have hle : boxD Y (eq' q) ≤ boxD Y eAll := by
        refine Finset.prod_le_prod' fun p hp => Nat.pow_le_pow_right (hY p hp).pos ?_
        simp only [heq', heAll]
        split_ifs <;> omega
      have : (boxD Y (eq' q) : ℝ) ≤ boxD Y eAll := by exact_mod_cast hle
      exact pow_le_pow_left₀ (by positivity) this 2
    linarith [(abs_le.mp h1).2]
  have hsum : ∑ q ∈ Y, ∫ t in T..T + L, boxWeight Y (eq' q) θ t ≤ (r : ℝ) * (L * (B * X) + 2 * D) := by
    have := Finset.sum_le_card_nsmul Y _ _ hupq
    rwa [nsmul_eq_mul] at this
  have hfin : L * (A * X) - 2 * D ≤ c * ((r : ℝ) * (L * (B * X) + 2 * D)) :=
    hlow.trans (hint.trans (mul_le_mul_of_nonneg_left hsum hc0))
  have hAm : 1 ≤ A * (4 * (m : ℝ)) := by
    have := one_le_binomMean_mul (n := 2 * m) (by omega)
    push_cast at this
    rw [hA]
    linarith
  have hclose := box_algebra hmr (binomMean_le_one m) hXpos hc0
    (Nat.cast_nonneg r) hD0 hAm hc hLpos hfin
  rw [← hAr] at hclose
  -- Contradiction with the length.
  have hpow : 1 ≤ A ^ r * (4 * (m : ℝ)) ^ r := by
    rw [← mul_pow]
    exact one_le_pow₀ hAm
  have h4m : 0 < (4 * (m : ℝ)) ^ r := by positivity
  have hLle : L ≤ 8 * (4 * (m : ℝ)) ^ r * D := by
    calc L = L * 1 := (mul_one _).symm
      _ ≤ L * (A ^ r * (4 * (m : ℝ)) ^ r) := mul_le_mul_of_nonneg_left hpow hLpos.le
      _ = (L * A ^ r) * (4 * (m : ℝ)) ^ r := by ring
      _ ≤ (8 * D) * (4 * (m : ℝ)) ^ r := mul_le_mul_of_nonneg_right hclose h4m.le
      _ = _ := by ring
  linarith

/-- The box theorem on the primes up to `y`. -/
theorem exists_mem_box_of_primesUpTo {y m : ℕ} (θ : ℕ → ℝ) (hm : 1 ≤ m) {δ : ℝ}
    (hδ1 : δ < 1) (hc : 8 * (m : ℝ) * ((y : ℝ) * (1 - δ) ^ m) ≤ 1) (T : ℝ) {L : ℝ}
    (hL : 8 * (4 * (m : ℝ)) ^ y * ((4 : ℝ) ^ (2 * m * y)) ^ 2 < L) :
    ∃ t ∈ Set.Icc T (T + L), ∀ q ∈ primesUpTo y, 1 - δ < bump (t * Real.log q - θ q) := by
  refine exists_mem_box (fun p hp => prime_of_mem_primesUpTo hp) θ hm hδ1 ?_ T ?_
  · refine le_trans ?_ hc
    have hcard : ((primesUpTo y).card : ℝ) ≤ y := by exact_mod_cast card_primesUpTo_le y
    have h0 : 0 ≤ (1 - δ) ^ m := pow_nonneg (by linarith) _
    exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard h0) (by positivity)
  · refine lt_of_le_of_lt ?_ hL
    have hmr : (1 : ℝ) ≤ 4 * (m : ℝ) := by
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have h1 : (4 * (m : ℝ)) ^ (primesUpTo y).card ≤ (4 * (m : ℝ)) ^ y :=
      pow_le_pow_right₀ hmr (card_primesUpTo_le y)
    have h2 : ((boxModulus (primesUpTo y) (2 * m) : ℕ) : ℝ) ≤ (4 : ℝ) ^ (2 * m * y) := by
      exact_mod_cast boxModulus_primesUpTo_le y (2 * m)
    have h3 := pow_le_pow_left₀ (by positivity) h2 2
    gcongr

/-- The eventual inequalities behind the scale of the box theorem. -/
theorem eventually_box_conditions {δ : ℝ} (hδ0 : 0 < δ) :
    ∀ᶠ Y : ℝ in atTop, 4 ≤ Real.log Y ∧ 4 * (3 * Real.log Y / δ + 1) ≤ Y ∧
      8 * (3 * Real.log Y / δ + 1) ≤ Y ^ 2 ∧ 1 ≤ Y := by
  have hlog := Real.tendsto_log_atTop
  have h1 : ∀ᶠ Y : ℝ in atTop, 4 ≤ Real.log Y := hlog.eventually_ge_atTop 4
  have h2 := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < δ / 24 by positivity)
  filter_upwards [h1, h2, eventually_ge_atTop (8 : ℝ)] with Y h1 h2 h3
  simp only [id, Real.norm_eq_abs] at h2
  rw [abs_of_nonneg (by linarith), abs_of_nonneg (by linarith)] at h2
  have h4 : 3 * Real.log Y / δ ≤ Y / 8 := by
    rw [div_le_iff₀ hδ0]
    nlinarith
  refine ⟨h1, by linarith, by nlinarith, by linarith⟩

/-- `log (8 (4m)^y 16^{2my}) < (20/δ) y log y` at the scale `m = ⌈3 log y/δ⌉`. -/
theorem log_box_length_lt {δ Y ℓ a : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) (hℓ : 4 ≤ ℓ) (hY : 1 ≤ Y)
    (ha : a ≤ 3 * ℓ / δ + 1) (hlog : Real.log (4 * a) ≤ ℓ) :
    Real.log 8 + Y * Real.log (4 * a) + 4 * a * Y * Real.log 4 < 20 / δ * Y * ℓ := by
  have h8 : Real.log 8 ≤ 2.1 := by
    have e : (8 : ℝ) = 2 ^ 3 := by norm_num
    rw [e, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    linarith
  have h4 : Real.log 4 ≤ 1.4 := by
    have e : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [e, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast
    linarith
  have h40 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hinv : 1 ≤ 1 / δ := by
    rw [le_div_iff₀ hδ0]
    linarith
  have hYℓ : 0 ≤ Y * ℓ := by positivity
  set w : ℝ := Y * ℓ / δ with hw
  have hwY : Y * ℓ ≤ w := by
    rw [hw, le_div_iff₀ hδ0]
    nlinarith
  have e20 : 20 / δ * Y * ℓ = 20 * w := by
    rw [hw]
    ring
  rw [e20]
  have ht1 : Y * Real.log (4 * a) ≤ Y * ℓ := mul_le_mul_of_nonneg_left hlog (by linarith)
  have ht2 : 4 * a * Y * Real.log 4 ≤ 4 * (3 * ℓ / δ + 1) * Y * 1.4 := by
    refine mul_le_mul ?_ h4 h40 (by positivity)
    exact mul_le_mul_of_nonneg_right (by linarith) (by linarith)
  have e3 : 4 * (3 * ℓ / δ + 1) * Y * 1.4 = 16.8 * w + 5.6 * Y := by
    rw [hw]
    field_simp
    ring
  have hY4 : 4 * Y ≤ w := by nlinarith
  linarith

/-- **The scale of the boxes.** Every window of length `exp((20/δ) y log y)` enters every box on the primes up to `y`. -/
theorem eventually_exists_mem_box {δ : ℝ} (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ y₀ : ℕ, ∀ y : ℕ, y₀ ≤ y → ∀ (θ : ℕ → ℝ) (T : ℝ),
      ∃ t ∈ Set.Icc T (T + Real.exp (20 / δ * y * Real.log y)),
        ∀ q ∈ primesUpTo y, 1 - δ < bump (t * Real.log q - θ q) := by
  obtain ⟨y₀, hy₀⟩ := eventually_atTop.mp
    (tendsto_natCast_atTop_atTop.eventually (eventually_box_conditions hδ0))
  refine ⟨y₀, fun y hy θ T => ?_⟩
  obtain ⟨hℓ, hY4, hY8, hY1⟩ := hy₀ y hy
  set ℓ : ℝ := Real.log y with hℓdef
  have hYpos : (0 : ℝ) < y := by linarith
  set m : ℕ := ⌈3 * ℓ / δ⌉₊ with hm
  have hm1 : (3 * ℓ / δ) ≤ m := Nat.le_ceil _
  have hm2 : (m : ℝ) ≤ 3 * ℓ / δ + 1 := (Nat.ceil_lt_add_one (by positivity)).le
  have hmpos : 1 ≤ m := by
    have h : (1 : ℝ) ≤ m := by
      refine le_trans ?_ hm1
      rw [le_div_iff₀ hδ0]
      nlinarith
    exact_mod_cast h
  have hmr : (1 : ℝ) ≤ m := by exact_mod_cast hmpos
  -- The tail `(1 − δ)^m ≤ y^{−3}`.
  have htail : (1 - δ) ^ m ≤ 1 / (y : ℝ) ^ 3 := by
    have h1 : 1 - δ ≤ Real.exp (-δ) := by
      have := Real.add_one_le_exp (-δ)
      linarith
    have h2 : (1 - δ) ^ m ≤ Real.exp (-δ) ^ m := pow_le_pow_left₀ (by linarith) h1 m
    rw [← Real.exp_nat_mul] at h2
    refine h2.trans ?_
    have e3 : 1 / (y : ℝ) ^ 3 = Real.exp (-(3 * ℓ)) := by
      rw [Real.exp_neg, hℓdef, mul_comm, Real.exp_mul, Real.exp_log hYpos]
      norm_num
    rw [e3]
    refine Real.exp_le_exp.mpr ?_
    have : 3 * ℓ ≤ (m : ℝ) * δ := by
      have := mul_le_mul_of_nonneg_right hm1 hδ0.le
      rwa [div_mul_cancel₀ _ hδ0.ne'] at this
    linarith
  have hc : 8 * (m : ℝ) * ((y : ℝ) * (1 - δ) ^ m) ≤ 1 := by
    have h1 : (y : ℝ) * (1 - δ) ^ m ≤ (y : ℝ) * (1 / (y : ℝ) ^ 3) :=
      mul_le_mul_of_nonneg_left htail hYpos.le
    have e : (y : ℝ) * (1 / (y : ℝ) ^ 3) = 1 / (y : ℝ) ^ 2 := by
      field_simp
    rw [e] at h1
    have h2 : 8 * (m : ℝ) ≤ (y : ℝ) ^ 2 := by linarith
    calc 8 * (m : ℝ) * ((y : ℝ) * (1 - δ) ^ m) ≤ (y : ℝ) ^ 2 * (1 / (y : ℝ) ^ 2) :=
          mul_le_mul h2 h1 (mul_nonneg hYpos.le (pow_nonneg (by linarith) _)) (by positivity)
      _ = 1 := by field_simp
  -- The length.
  have hlogm : Real.log (4 * (m : ℝ)) ≤ ℓ := Real.log_le_log (by positivity) (by linarith)
  have hstrict := log_box_length_lt hδ0 hδ1 hℓ hY1 hm2 hlogm
  have hL : 8 * (4 * (m : ℝ)) ^ y * ((4 : ℝ) ^ (2 * m * y)) ^ 2 < Real.exp (20 / δ * y * ℓ) := by
    refine lt_of_le_of_lt (le_of_eq ?_) (Real.exp_lt_exp.mpr hstrict)
    rw [Real.exp_add, Real.exp_add, Real.exp_log (by norm_num)]
    have hm4 : (0 : ℝ) < 4 * (m : ℝ) := by positivity
    have e1 : Real.exp ((y : ℝ) * Real.log (4 * (m : ℝ))) = (4 * (m : ℝ)) ^ y := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos hm4, mul_comm]
    have e2 : Real.exp (4 * (m : ℝ) * (y : ℝ) * Real.log 4) = ((4 : ℝ) ^ (2 * m * y)) ^ 2 := by
      rw [← pow_mul, ← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), mul_comm]
      congr 1
      push_cast
      ring
    rw [e1, e2]
  exact exists_mem_box_of_primesUpTo θ hmpos hδ1 hc T hL

open Classical in
/-- **A box is missed below the mixing time.** Below `2^{π(y)}/θ(y)` some box at `δ = ½` is not entered on `[0, T]`. -/
theorem exists_box_missed {y : ℕ} {T : ℝ}
    (hlt : 2 * ∑ p ∈ primesUpTo y, (⌊T * Real.log p / Real.pi⌋₊ + 1) + 1 < 2 ^ (primesUpTo y).card) :
    ∃ θ : ℕ → ℝ, ∀ t ∈ Set.Icc 0 T, ∃ p ∈ primesUpTo y, bump (t * Real.log p - θ p) ≤ 1 / 2 := by
  have hℓ : ∀ i : primesUpTo y, 0 < Real.log ((i : ℕ) : ℝ) := fun i =>
    Real.log_pos (by exact_mod_cast (prime_of_mem_primesUpTo i.2).one_lt)
  have hsum : ∑ i : primesUpTo y, (⌊T * Real.log ((i : ℕ) : ℝ) / Real.pi⌋₊ + 1) =
      ∑ p ∈ primesUpTo y, (⌊T * Real.log p / Real.pi⌋₊ + 1) :=
    Finset.sum_coe_sort (primesUpTo y) fun p => ⌊T * Real.log p / Real.pi⌋₊ + 1
  obtain ⟨P, hP⟩ := exists_pattern_not_attained (ι := primesUpTo y)
    (ℓ := fun i => Real.log ((i : ℕ) : ℝ)) hℓ (T := T) (by
      rw [hsum, Fintype.card_coe]
      exact hlt)
  refine ⟨fun p => if h : p ∈ primesUpTo y then (if P ⟨p, h⟩ then 0 else Real.pi) else 0,
    fun t ht => ?_⟩
  by_contra hcon
  push Not at hcon
  refine hP t ht (funext fun i => propext ?_)
  have hi := hcon i i.2
  simp only [i.2, dite_true, Subtype.coe_eta] at hi
  unfold pattern
  unfold bump at hi
  by_cases hPi : P i
  · simp only [hPi, if_true, sub_zero] at hi
    refine iff_of_true ?_ hPi
    linarith
  · simp only [hPi, if_false, Real.cos_sub_pi] at hi
    refine iff_of_false ?_ hPi
    linarith

/-- A time in a box brings a column within `2δ` of its size. -/
theorem sum_one_sub_cos_le_of_box {Q : Finset ℕ} {a : ℕ → ℝ} (ha : ∀ r ∈ Q, 0 ≤ a r) {t δ : ℝ}
    (h : ∀ q ∈ Q, 1 - δ < bump (t * Real.log q - 0)) :
    ∑ r ∈ Q, a r * (1 - Real.cos (t * Real.log r)) ≤ 2 * δ * ∑ r ∈ Q, a r := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r hr => ?_
  have h1 := h r hr
  unfold bump at h1
  rw [sub_zero] at h1
  have h2 : 1 - Real.cos (t * Real.log r) ≤ 2 * δ := by linarith
  calc a r * (1 - Real.cos (t * Real.log r)) ≤ a r * (2 * δ) := mul_le_mul_of_nonneg_left h2 (ha r hr)
    _ = _ := by ring

end

end GaloisForLFunctions.PrimeTorusTheory
