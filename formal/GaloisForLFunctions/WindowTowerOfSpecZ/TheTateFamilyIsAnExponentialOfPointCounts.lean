import GaloisForLFunctions.WindowTowerOfSpecZ.TheWindowFormIsTheDerivativeOfTheJordanCounts
import GaloisForLFunctions.WindowTowerOfSpecZ.TheTateFlowOnTheWindowAlgebra
import GaloisForLFunctions.WindowTowerOfSpecZ.TheTowerOfSmallExtensions
import GaloisForLFunctions.RHTower.DirichletLogDerivation

/-!
# The Tate family is an exponential of point counts

The degree derivation `D f = f·log` of the Dirichlet ring determines a function from its logarithmic
derivative: on the window algebra `D_N`, if `D X ≡ c * X` with `c(1) = X(1) = 0`, then `X ≡ 0`
(`mem_truncIdeal_of_degD`; the recursion `X(n) log n = Σ_{d∣n, d>1} c(d)X(n/d)`). The truncated
exponential `exp_L g = Σ_{j≤L} g^j/j!` of `g ∈ m` solves `D F = (D g) * F` modulo `m^{L+1}`
(`degD_expTrunc`). Hence, with the **prime-power logarithm** `ℓ(n) = Λ(n)/log n` (`ℓ(p^a) = 1/a`):

* **The window zeta operator is an exponential** (`expTrunc_sub_zeta_mem`, `windowRep_zeta_eq_exp`):
  `ζ ≡ exp ℓ` on every window, `ρ_A(ζ) = Σ_{j≤L} ρ_A(ℓ)^j/j!` as soon as `e^A < 2^{L+1}`. The logarithm
  of the window zeta operator is `ρ_A(ℓ)`, and **Weil's arithmetic operator is the commutator of the
  position with it**: `ρ_A(Λ) = [M, log Z]` (`windowRep_vonMangoldt_eq_comm_log`).
* **The Tate family is the exponential of the point counts of punctured affine space**
  (`expTrunc_sub_jordan_mem`): `J_k ≡ exp g_k` with `g_k(n) = ℓ(n)(n^k − 1)`, i.e.
  `g_k(p^a) = (p^{ak} − 1)/a = #(𝔸^k∖0)(𝔽_{p^a})/a`. This is the Hasse–Weil formula
  `Z(X, T) = exp Σ_a #X(𝔽_{p^a})T^a/a` for `X = 𝔸^k∖0` over `ℤ`, realized in the window algebra:
  `Σ J_k(n)n^{−s} = ζ(s − k)/ζ(s)` is the zeta function of `𝔸^k∖0`, and Weil's arithmetic term is
  its derivative in `k` at `0`.
* **Positivity of the exponential** (`jordanTotient_ge_exp_tangent`): for `k ≥ 0` the exponent `g_k`
  is nonnegative, so every term of the exponential is, and `J_k(n) ≥ [n = 1] + ℓ(n)(n^k − 1)
  ≥ [n = 1] + kΛ(n)`; at prime powers `J_k(p^a) ≥ (p^{ak} − 1)/a`. The tangent principle is the first
  two terms of an exponential with nonnegative exponent.
-/

noncomputable section

namespace GaloisForLFunctions.WindowTowerOfSpecZ

open CohomologyOfWindowsOfSpecZ ArithmeticDegenerationTheory

/-! ### The degree derivation -/

/-- The degree derivation `D f = f·log`. -/
def degD (f : ArithmeticFunction ℝ) : ArithmeticFunction ℝ := f.pmul ArithmeticFunction.log

theorem degD_apply (f : ArithmeticFunction ℝ) (n : ℕ) : degD f n = f n * Real.log n := by
  rw [degD, ArithmeticFunction.pmul_apply, ArithmeticFunction.log_apply]

theorem degD_mul (f g : ArithmeticFunction ℝ) : degD (f * g) = degD f * g + f * degD g :=
  RHTower.pmul_log_mul f g

theorem degD_add (f g : ArithmeticFunction ℝ) : degD (f + g) = degD f + degD g := by
  ext n; simp only [degD_apply, ArithmeticFunction.add_apply]; ring

theorem degD_sub (f g : ArithmeticFunction ℝ) : degD (f - g) = degD f - degD g := by
  ext n; simp only [degD_apply, sub_apply']; ring

theorem degD_single_one (c : ℝ) : degD (single 1 c) = 0 := by
  ext n
  rw [degD_apply, single_apply]
  split_ifs with h
  · rw [h.1, Nat.cast_one, Real.log_one, mul_zero]; rfl
  · rw [zero_mul]; rfl

theorem degD_single_one_mul (c : ℝ) (f : ArithmeticFunction ℝ) :
    degD (single 1 c * f) = single 1 c * degD f := by
  rw [degD_mul, degD_single_one, zero_mul, zero_add]

theorem degD_apply_one (f : ArithmeticFunction ℝ) : degD f 1 = 0 := by
  rw [degD_apply, Nat.cast_one, Real.log_one, mul_zero]

theorem degD_tateTwist (s : ℝ) (f : ArithmeticFunction ℝ) :
    degD (tateTwist s f) = tateTwist s (degD f) := by
  ext n; simp only [degD_apply, tateTwist_apply]; ring

/-! ### Scalars -/

theorem single_one_mul_apply (c : ℝ) (f : ArithmeticFunction ℝ) (n : ℕ) :
    (single 1 c * f) n = c * f n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  rw [ArithmeticFunction.mul_apply, Finset.sum_eq_single (1, n)]
  · rw [single_apply_self one_ne_zero]
  · intro x hx hx1
    rw [single_apply, if_neg, zero_mul]
    rintro ⟨h1, -⟩
    obtain ⟨hxn, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
    exact hx1 (Prod.ext h1 (by rw [h1, one_mul] at hxn; exact hxn))
  · intro h; exact absurd (Nat.mem_divisorsAntidiagonal.mpr ⟨one_mul n, by omega⟩) h

theorem single_one_one : single 1 (1 : ℝ) = 1 := by
  ext n; rw [single_apply, ArithmeticFunction.one_apply]
  by_cases h : n = 1 <;> simp [h]

theorem single_one_mul_single_one (a b : ℝ) : single 1 a * single 1 b = single 1 (a * b) := by
  rw [single_mul_single one_ne_zero one_ne_zero, mul_one]

theorem single_one_add (a b : ℝ) : single 1 a + single 1 b = single 1 (a + b) := by
  ext n; rw [ArithmeticFunction.add_apply, single_apply, single_apply, single_apply]
  split_ifs <;> ring

theorem finsetSum_apply {ι : Type*} (s : Finset ι) (f : ι → ArithmeticFunction ℝ) (n : ℕ) :
    (∑ i ∈ s, f i) n = ∑ i ∈ s, f i n := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ArithmeticFunction.add_apply, ih]

/-! ### Powers and the truncated exponential -/

theorem pow_apply_one (g : ArithmeticFunction ℝ) (j : ℕ) : (g ^ j) 1 = g 1 ^ j := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_one, Finset.sum_singleton,
      ih, pow_succ]

/-- `D(g^{j+1}) = (j + 1) g^j D g`. -/
theorem degD_pow (g : ArithmeticFunction ℝ) (j : ℕ) :
    degD (g ^ (j + 1)) = single 1 ((j + 1 : ℕ) : ℝ) * (g ^ j * degD g) := by
  induction j with
  | zero => rw [zero_add, pow_one, pow_zero, one_mul, Nat.cast_one, single_one_one, one_mul]
  | succ j ih =>
    rw [pow_succ, degD_mul, ih]
    have : single 1 ((j + 1 + 1 : ℕ) : ℝ) = single 1 ((j + 1 : ℕ) : ℝ) + 1 := by
      rw [← single_one_one, single_one_add]; push_cast; ring_nf
    rw [this]; ring

/-- The truncated exponential `exp_L g = Σ_{j≤L} g^j/j!`. -/
def expTrunc (L : ℕ) (g : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  ∑ j ∈ Finset.range (L + 1), single 1 ((j.factorial : ℝ)⁻¹) * g ^ j

theorem expTrunc_apply_one {g : ArithmeticFunction ℝ} (hg : g 1 = 0) (L : ℕ) :
    expTrunc L g 1 = 1 := by
  rw [expTrunc, finsetSum_apply, Finset.sum_range_succ']
  simp only [single_one_mul_apply, pow_apply_one, hg, zero_pow (Nat.succ_ne_zero _), mul_zero,
    Finset.sum_const_zero, zero_add, pow_zero, Nat.factorial_zero, Nat.cast_one, inv_one, one_mul,
    ArithmeticFunction.one_one]

/-- **The truncated exponential solves `D F = (D g) F` up to its last term.** -/
theorem degD_expTrunc (L : ℕ) (g : ArithmeticFunction ℝ) :
    degD (expTrunc L g) =
      (expTrunc L g - single 1 ((L.factorial : ℝ)⁻¹) * g ^ L) * degD g := by
  induction L with
  | zero =>
    simp only [expTrunc, zero_add, Finset.range_one, Finset.sum_singleton, pow_zero, mul_one,
      degD_single_one, sub_self, zero_mul]
  | succ L ih =>
    have hsplit : expTrunc (L + 1) g =
        expTrunc L g + single 1 (((L + 1).factorial : ℝ)⁻¹) * g ^ (L + 1) := by
      rw [expTrunc, Finset.sum_range_succ]; rfl
    rw [hsplit, degD_add, degD_single_one_mul, degD_pow, ih, ← mul_assoc,
      single_one_mul_single_one]
    have hf : ((L + 1).factorial : ℝ)⁻¹ * ((L + 1 : ℕ) : ℝ) = (L.factorial : ℝ)⁻¹ := by
      rw [Nat.factorial_succ, Nat.cast_mul]
      have : (L.factorial : ℝ) ≠ 0 := by exact_mod_cast (Nat.factorial_pos L).ne'
      have : ((L + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
    rw [hf]; ring

/-! ### Uniqueness for the degree derivation -/

/-- **A function is determined by its logarithmic derivative on a window**: if `X(1) = 0` and
`D X ≡ c * X` modulo `I_N` with `c(1) = 0`, then `X ∈ I_N`. -/
theorem mem_truncIdeal_of_degD {N : ℕ} {c X : ArithmeticFunction ℝ} (hc : c 1 = 0) (hX : X 1 = 0)
    (h : degD X - c * X ∈ truncIdeal N) : X ∈ truncIdeal N := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro h1 hn
    rcases Nat.lt_or_ge n 2 with h2 | h2
    · rw [show n = 1 by omega, hX]
    have hcX : (c * X) n = 0 := by
      rw [ArithmeticFunction.mul_apply]
      refine Finset.sum_eq_zero fun x hx => ?_
      obtain ⟨hxn, -⟩ := Nat.mem_divisorsAntidiagonal.mp hx
      have hx1 : x.1 ≠ 0 := fun h => by rw [h, zero_mul] at hxn; omega
      have hx2 : x.2 ≠ 0 := fun h => by rw [h, mul_zero] at hxn; omega
      rcases Nat.lt_or_ge x.1 2 with ha | ha
      · rw [show x.1 = 1 by omega, hc, zero_mul]
      · have : x.2 < n := by
          rw [← hxn]; exact lt_mul_of_one_lt_left (by omega) (by omega)
        rw [ih x.2 this (by omega) (by omega), mul_zero]
    have := h n h1 hn
    rw [sub_apply', hcX, sub_zero, degD_apply] at this
    have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast h2)).ne'
    exact (mul_eq_zero.mp this).resolve_right hlog

theorem mem_truncIdeal_of_pow_mul {N L : ℕ} (hNL : N < 2 ^ (L + 1)) {g c : ArithmeticFunction ℝ}
    (hg : g 1 = 0) (hc : c 1 = 0) : g ^ L * c ∈ truncIdeal N := by
  have hm : g ^ L * c ∈ (truncIdeal 1 : Ideal (ArithmeticFunction ℝ)) ^ (L + 1) := by
    rw [pow_succ]
    exact Ideal.mul_mem_mul (Ideal.pow_mem_pow (mem_truncIdeal_one.mpr hg) L)
      (mem_truncIdeal_one.mpr hc)
  exact truncIdeal_anti (by omega) (pow_truncIdeal_one_le L hm)

/-- **Exponentials on a window**: if `F(1) = 1` and `D F ≡ (D g) F` modulo `I_N`, `g(1) = 0`, then
`F ≡ exp_L g` as soon as `N < 2^{L+1}`. -/
theorem expTrunc_sub_mem {N L : ℕ} (hNL : N < 2 ^ (L + 1)) {g F : ArithmeticFunction ℝ}
    (hg : g 1 = 0) (hF1 : F 1 = 1) (hF : degD F - degD g * F ∈ truncIdeal N) :
    expTrunc L g - F ∈ truncIdeal N := by
  refine mem_truncIdeal_of_degD (degD_apply_one g)
    (by rw [sub_apply', expTrunc_apply_one hg, hF1, sub_self]) ?_
  have hlast := mem_truncIdeal_of_pow_mul hNL hg (degD_apply_one g)
  have hE : degD (expTrunc L g) - degD g * expTrunc L g =
      -(single 1 ((L.factorial : ℝ)⁻¹) * (g ^ L * degD g)) := by
    rw [degD_expTrunc]; ring
  have : degD (expTrunc L g - F) - degD g * (expTrunc L g - F) =
      (degD (expTrunc L g) - degD g * expTrunc L g) - (degD F - degD g * F) := by
    rw [degD_sub]; ring
  rw [this, hE]
  exact Submodule.sub_mem _ (Submodule.neg_mem _ (Ideal.mul_mem_left _ _ hlast)) hF

/-! ### The prime-power logarithm and the window zeta operator -/

/-- The **prime-power logarithm** `ℓ(n) = Λ(n)/log n`: `ℓ(p^a) = 1/a`, `0` elsewhere. -/
def primePowerLog : ArithmeticFunction ℝ :=
  ⟨fun n => ArithmeticFunction.vonMangoldt n / Real.log n, by simp⟩

theorem primePowerLog_apply (n : ℕ) :
    primePowerLog n = ArithmeticFunction.vonMangoldt n / Real.log n := rfl

theorem primePowerLog_one : primePowerLog 1 = 0 := by simp [primePowerLog_apply]

theorem primePowerLog_nonneg (n : ℕ) : 0 ≤ primePowerLog n := by
  rw [primePowerLog_apply]
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))

/-- `D ℓ = Λ`. -/
theorem degD_primePowerLog : degD primePowerLog = ArithmeticFunction.vonMangoldt := by
  ext n
  rw [degD_apply, primePowerLog_apply]
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n <;> simp
  · exact div_mul_cancel₀ _ (Real.log_pos (by exact_mod_cast h)).ne'

/-- **The zeta function is the exponential of the prime-power logarithm on every window**. -/
theorem expTrunc_sub_zeta_mem {N L : ℕ} (hNL : N < 2 ^ (L + 1)) :
    expTrunc L primePowerLog - (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ∈ truncIdeal N := by
  refine expTrunc_sub_mem hNL primePowerLog_one (by simp) ?_
  rw [degD_primePowerLog, degD, RHTower.zeta_pmul_log, ArithmeticFunction.vonMangoldt_mul_zeta,
    sub_self]
  exact Submodule.zero_mem _

/-- **The window zeta operator is the exponential of its logarithm `ρ_A(ℓ)`**. -/
theorem windowRep_zeta_eq_exp {A : ℝ} {L : ℕ} (hL : windowLevel A < 2 ^ (L + 1)) :
    windowRep A (ArithmeticFunction.zeta : ArithmeticFunction ℝ) =
      ∑ j ∈ Finset.range (L + 1),
        windowRep A (single 1 ((j.factorial : ℝ)⁻¹)) * windowRep A primePowerLog ^ j := by
  have h := windowRep_eq_zero_of_mem (expTrunc_sub_zeta_mem (N := windowLevel A) hL)
  rw [map_sub, sub_eq_zero] at h
  rw [← h, expTrunc, map_sum]
  simp only [map_mul, map_pow]

/-- **Weil's arithmetic operator is the commutator of the position with the logarithm of the window
zeta operator**: `ρ_A(Λ) = [M, ρ_A(ℓ)]`. -/
theorem windowRep_vonMangoldt_eq_comm_log (A : ℝ) :
    windowRep A ArithmeticFunction.vonMangoldt =
      positionOp A * windowRep A primePowerLog - windowRep A primePowerLog * positionOp A := by
  rw [position_comm_windowRep, ← degD, degD_primePowerLog]

/-! ### The Tate family -/

/-- The exponent of the Tate family: `g_k(n) = ℓ(n)(n^k − 1)`, `g_k(p^a) = (p^{ak} − 1)/a`. -/
def tateExponent (k : ℝ) : ArithmeticFunction ℝ := tateTwist (-k) primePowerLog - primePowerLog

theorem tateExponent_apply (k : ℝ) (n : ℕ) :
    tateExponent k n = primePowerLog n * ((n : ℝ) ^ k - 1) := by
  rw [tateExponent, sub_apply', tateTwist_apply, neg_neg]; ring

theorem tateExponent_prime_pow (k : ℝ) {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    tateExponent k (p ^ a) = (((p : ℝ) ^ a) ^ k - 1) / a := by
  rw [tateExponent_apply, primePowerLog_apply,
    ArithmeticFunction.vonMangoldt_apply_pow (by omega), ArithmeticFunction.vonMangoldt_apply_prime hp,
    Nat.cast_pow, Real.log_pow]
  have hlog : Real.log p ≠ 0 := (Real.log_pos (by exact_mod_cast hp.one_lt)).ne'
  have ha' : (a : ℝ) ≠ 0 := by exact_mod_cast (by omega : a ≠ 0)
  field_simp

theorem degD_moebius :
    degD (ArithmeticFunction.moebius : ArithmeticFunction ℝ) =
      -(ArithmeticFunction.vonMangoldt * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) := by
  have h1 : degD ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) = 0 := by
    rw [ArithmeticFunction.coe_zeta_mul_coe_moebius]
    ext n; rw [degD_apply, ArithmeticFunction.one_apply]
    split_ifs with h
    · rw [h, Nat.cast_one, Real.log_one, mul_zero]; rfl
    · rw [zero_mul]; rfl
  rw [degD_mul, degD, RHTower.zeta_pmul_log, ← ArithmeticFunction.vonMangoldt_mul_zeta, mul_assoc,
    ArithmeticFunction.coe_zeta_mul_coe_moebius, mul_one] at h1
  -- `Λ + ζ Dμ = 0`, and `Dμ = μ (ζ Dμ)`
  have h2 : degD (ArithmeticFunction.moebius : ArithmeticFunction ℝ) =
      (ArithmeticFunction.moebius : ArithmeticFunction ℝ) *
        ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          degD (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) := by
    rw [← mul_assoc, mul_comm (ArithmeticFunction.moebius : ArithmeticFunction ℝ),
      ArithmeticFunction.coe_zeta_mul_coe_moebius, one_mul]
  have h3 : (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
      degD (ArithmeticFunction.moebius : ArithmeticFunction ℝ) = -ArithmeticFunction.vonMangoldt := by
    linear_combination h1
  rw [h2, h3]; ring

/-- `D J_k = (D g_k) * J_k`. -/
theorem degD_jordanFun (k : ℝ) : degD (jordanFun k) = degD (tateExponent k) * jordanFun k := by
  have hz : degD (tateTwist (-k) (ArithmeticFunction.zeta : ArithmeticFunction ℝ)) =
      tateTwist (-k) ArithmeticFunction.vonMangoldt *
        tateTwist (-k) (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by
    rw [degD_tateTwist, degD, RHTower.zeta_pmul_log, ← ArithmeticFunction.vonMangoldt_mul_zeta,
      tateTwist_mul]
  rw [jordanFun_eq, degD_mul, hz, degD_moebius, tateExponent, degD_sub, degD_tateTwist,
    degD_primePowerLog]
  ring

theorem jordanFun_apply_one (k : ℝ) : jordanFun k 1 = 1 := by
  rw [jordanFun_eq, ArithmeticFunction.mul_apply, Nat.divisorsAntidiagonal_one,
    Finset.sum_singleton]
  simp [tateTwist_apply]

/-- **The Tate family is the exponential of the point counts of punctured affine space**:
`J_k ≡ exp g_k` on every window, `g_k(p^a) = #(𝔸^k∖0)(𝔽_{p^a})/a`. -/
theorem expTrunc_sub_jordan_mem {N L : ℕ} (hNL : N < 2 ^ (L + 1)) (k : ℝ) :
    expTrunc L (tateExponent k) - jordanFun k ∈ truncIdeal N := by
  refine expTrunc_sub_mem hNL (by rw [tateExponent_apply, primePowerLog_one, zero_mul])
    (jordanFun_apply_one k) ?_
  rw [degD_jordanFun, sub_self]
  exact Submodule.zero_mem _

/-! ### Positivity of the exponential -/

theorem pow_apply_nonneg {g : ArithmeticFunction ℝ} (hg : ∀ n, 0 ≤ g n) (j n : ℕ) :
    0 ≤ (g ^ j) n := by
  induction j generalizing n with
  | zero => rw [pow_zero, ArithmeticFunction.one_apply]; split_ifs <;> norm_num
  | succ j ih =>
    rw [pow_succ, ArithmeticFunction.mul_apply]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (ih _) (hg _)

theorem tateExponent_nonneg {k : ℝ} (hk : 0 ≤ k) (n : ℕ) : 0 ≤ tateExponent k n := by
  rw [tateExponent_apply]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [primePowerLog_apply]
  exact mul_nonneg (primePowerLog_nonneg n)
    (sub_nonneg.mpr (Real.one_le_rpow (by exact_mod_cast hn) hk))

/-- **Positivity of the exponential**: `J_k(n) ≥ [n = 1] + ℓ(n)(n^k − 1)` for `k ≥ 0`. -/
theorem jordanTotient_ge_exp_tangent {k : ℝ} (hk : 0 ≤ k) (n : ℕ) :
    (if n = 1 then 1 else 0) + tateExponent k n ≤ jordanTotient k n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tateExponent_apply, jordanTotient]
  have hmem := expTrunc_sub_jordan_mem (N := n) (L := n)
    (Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by norm_num) (by omega))) k n hn le_rfl
  rw [sub_apply', jordanFun_apply, sub_eq_zero] at hmem
  rw [← hmem, expTrunc, finsetSum_apply]
  have hterm : ∀ j ∈ Finset.range (n + 1), 0 ≤
      (single 1 ((j.factorial : ℝ)⁻¹) * tateExponent k ^ j) n := fun j _ => by
    rw [single_one_mul_apply]
    exact mul_nonneg (by positivity) (pow_apply_nonneg (tateExponent_nonneg hk) j n)
  have hsub : ({0, 1} : Finset ℕ) ⊆ Finset.range (n + 1) := by
    intro j hj
    rw [Finset.mem_insert, Finset.mem_singleton] at hj
    rw [Finset.mem_range]; omega
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum_of_subset_of_nonneg hsub fun j hj _ => hterm j hj)
  rw [Finset.sum_pair zero_ne_one, single_one_mul_apply, single_one_mul_apply, pow_zero, pow_one,
    ArithmeticFunction.one_apply]
  simp

/-- At prime powers: `J_k(p^a) ≥ (p^{ak} − 1)/a` for `k ≥ 0`. -/
theorem jordanTotient_prime_pow_ge {k : ℝ} (hk : 0 ≤ k) {p a : ℕ} (hp : p.Prime) (ha : 1 ≤ a) :
    (((p : ℝ) ^ a) ^ k - 1) / a ≤ jordanTotient k (p ^ a) := by
  have h := jordanTotient_ge_exp_tangent hk (p ^ a)
  rw [if_neg (Nat.one_lt_pow (by omega) hp.one_lt).ne', zero_add,
    tateExponent_prime_pow k hp ha] at h
  exact h

end GaloisForLFunctions.WindowTowerOfSpecZ
