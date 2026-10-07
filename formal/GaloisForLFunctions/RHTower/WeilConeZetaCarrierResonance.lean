import GaloisForLFunctions.RHTower.WeilConeZetaCarrierBoundary
import GaloisForLFunctions.RHTower.WeilPositivityPrimorialResonance

/-!
# ζ-multiplicative pole carriers: the resonance case

For `λ = βΛ + (1 ⋆ m) + v` (as in `WeilConeZetaCarrierBoundary`) with `M(1) > 0`, the
multiplicative Toeplitz bound of the Weil cone (`weil_multiplicativeToeplitz_bound`) fails on a
completely multiplicative resonator `c(k) = 1_{k ∣ N} φ(k)`.

**Resonator.** `φ(p) = p^{−½}` for `p < L` and `φ(p) = 1` for `p ≥ L`;
`N = ∏_{p < L} p^J · ∏_{L ≤ p ≤ y} p`. With `g(n) = φ(n) n^{−½}`, `h = φ² ⋆ 1` and `H = g ⋆ h`, the
Toeplitz bound reads `2 Σ_{n ∣ N, n ≥ 2} λ(n) g(n) h(N/n) ≤ (log N + C₀) h(N)`. Since `g` is
completely multiplicative, the `ζ`-part is `Σ_{k ∣ N} m(k) g(k) H(N/k)`: on the small primes
the resonator evaluates `M` at `s = 1`, on the large primes it evaluates `ζ` at `s = ½`.

**Theorem** (`mu_nonpos`). If `λ` is full-cone Weil-positive, then `M(1) ≤ 0`.

**Proof.** `H(N/k)/H(N) → 1` for fixed `k ∣ ∏_{p<L} p^J` as `J → ∞` (monotone and bounded in
`J`). So the `ζ`-part is at least `H(N)(M(1) − o(1))`, while the `Λ`- and `v`-parts cost at most
`h(N)((1 + 2|β|) log N + O(1))`. The ratio `H(N)/h(N) ≥ ∏_{L ≤ p ≤ y}(1 + p^{−½}/2)` grows like
`exp(c √y / log y)`, against `log N ≤ J L log 4 + y log 4`.

**Corollary** (`eq_vonMangoldt_of_weilPositiveFull_carrier`). A full-cone Weil-positive
`βΛ + (1 ⋆ m) + v`, with `Σ |m(n)| n^{−½}`, `Σ |v(n)| n^{−½} < ∞` and `v(0) = v(1) = 0`, equals
`Λ` on `n ≥ 2`, and the Riemann hypothesis holds.
-/

noncomputable section

open Complex Filter Topology Finset
open scoped ComplexConjugate

namespace RHTower.WeilZetaCarrier

open RHTower.WeilBoundaryDilation (BoundaryRegular regSeries)

/-! ## Completely multiplicative resonators -/

/-- The completely multiplicative function with `φ(p) = w(p)`. -/
def cmul (w : ℕ → ℝ) (k : ℕ) : ℝ := k.factorization.prod fun p e => w p ^ e

variable {w : ℕ → ℝ}

theorem cmul_mul (w : ℕ → ℝ) {k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0) :
    cmul w (k * l) = cmul w k * cmul w l := by
  unfold cmul
  rw [Nat.factorization_mul hk hl,
    Finsupp.prod_add_index' (fun _ => pow_zero _) fun _ _ _ => pow_add _ _ _]

theorem cmul_one (w : ℕ → ℝ) : cmul w 1 = 1 := by simp [cmul]

theorem cmul_prime_pow (w : ℕ → ℝ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    cmul w (p ^ e) = w p ^ e := by
  unfold cmul
  rw [hp.factorization_pow]
  exact Finsupp.prod_single_index (by simp)

theorem cmul_nonneg (hw : ∀ p, 0 ≤ w p) (k : ℕ) : 0 ≤ cmul w k := by
  unfold cmul Finsupp.prod
  exact Finset.prod_nonneg fun p _ => pow_nonneg (hw p) _

theorem cmul_le_one (hw : ∀ p, 0 ≤ w p) (hw1 : ∀ p, w p ≤ 1) (k : ℕ) : cmul w k ≤ 1 := by
  unfold cmul Finsupp.prod
  exact Finset.prod_le_one (fun p _ => pow_nonneg (hw p) _) fun p _ => pow_le_one₀ (hw p) (hw1 p)

/-- `φ` as an arithmetic function. -/
def phiA (w : ℕ → ℝ) : ArithmeticFunction ℝ := ⟨fun k => if k = 0 then 0 else cmul w k, if_pos rfl⟩

/-- `g(k) = φ(k) k^{−½}`. -/
def gA (w : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun k => if k = 0 then 0 else cmul w k / Real.sqrt k, if_pos rfl⟩

/-- `h = φ² ⋆ 1`. -/
def hA (w : ℕ → ℝ) : ArithmeticFunction ℝ :=
  (phiA w).pmul (phiA w) * (ArithmeticFunction.zeta : ArithmeticFunction ℝ)

/-- `H = g ⋆ h`. -/
def HA (w : ℕ → ℝ) : ArithmeticFunction ℝ := gA w * hA w

theorem phiA_apply {k : ℕ} (hk : k ≠ 0) : phiA w k = cmul w k := by
  change (if k = 0 then (0 : ℝ) else cmul w k) = _; rw [if_neg hk]

theorem gA_apply {k : ℕ} (hk : k ≠ 0) : gA w k = cmul w k / Real.sqrt k := by
  change (if k = 0 then (0 : ℝ) else cmul w k / Real.sqrt k) = _; rw [if_neg hk]

theorem gA_mul {k l : ℕ} (hk : k ≠ 0) (hl : l ≠ 0) : gA w (k * l) = gA w k * gA w l := by
  rw [gA_apply (mul_ne_zero hk hl), gA_apply hk, gA_apply hl, cmul_mul w hk hl, Nat.cast_mul,
    Real.sqrt_mul (Nat.cast_nonneg _)]
  field_simp

theorem isMultiplicative_phiA (w : ℕ → ℝ) : (phiA w).IsMultiplicative := by
  refine ⟨by rw [phiA_apply one_ne_zero, cmul_one], fun {k l} _ => ?_⟩
  by_cases hk : k = 0
  · subst hk; simp [phiA]
  by_cases hl : l = 0
  · subst hl; simp [phiA]
  rw [phiA_apply (mul_ne_zero hk hl), phiA_apply hk, phiA_apply hl, cmul_mul w hk hl]

theorem isMultiplicative_gA (w : ℕ → ℝ) : (gA w).IsMultiplicative := by
  refine ⟨by rw [gA_apply one_ne_zero, cmul_one]; simp, fun {k l} _ => ?_⟩
  by_cases hk : k = 0
  · subst hk; simp [gA]
  by_cases hl : l = 0
  · subst hl; simp [gA]
  exact gA_mul hk hl

theorem isMultiplicative_hA (w : ℕ → ℝ) : (hA w).IsMultiplicative :=
  ((isMultiplicative_phiA w).pmul (isMultiplicative_phiA w)).mul
    ArithmeticFunction.isMultiplicative_zeta.natCast

theorem isMultiplicative_HA (w : ℕ → ℝ) : (HA w).IsMultiplicative :=
  (isMultiplicative_gA w).mul (isMultiplicative_hA w)

theorem hA_apply (w : ℕ → ℝ) (K : ℕ) : hA w K = ∑ d ∈ K.divisors, cmul w d ^ 2 := by
  unfold hA
  rw [ArithmeticFunction.coe_mul_zeta_apply]
  refine Finset.sum_congr rfl fun d hd => ?_
  rw [ArithmeticFunction.pmul_apply, phiA_apply (Nat.ne_of_gt (Nat.pos_of_mem_divisors hd)), sq]

theorem HA_apply (w : ℕ → ℝ) (K : ℕ) : HA w K = ∑ l ∈ K.divisors, gA w l * hA w (K / l) := by
  unfold HA
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => gA w x * hA w y)]

theorem gA_nonneg (hw : ∀ p, 0 ≤ w p) (k : ℕ) : 0 ≤ gA w k := by
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h; simp [gA]
  · rw [gA_apply h.ne']; exact div_nonneg (cmul_nonneg hw k) (Real.sqrt_nonneg _)

theorem gA_le (hw : ∀ p, 0 ≤ w p) (hw1 : ∀ p, w p ≤ 1) {k : ℕ} (hk : k ≠ 0) :
    gA w k ≤ 1 / Real.sqrt k := by
  rw [gA_apply hk]
  exact div_le_div_of_nonneg_right (cmul_le_one hw hw1 k) (Real.sqrt_nonneg _)

theorem hA_nonneg (w : ℕ → ℝ) (K : ℕ) : 0 ≤ hA w K := by
  rw [hA_apply]; exact Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem HA_nonneg (hw : ∀ p, 0 ≤ w p) (K : ℕ) : 0 ≤ HA w K := by
  rw [HA_apply]
  exact Finset.sum_nonneg fun l _ => mul_nonneg (gA_nonneg hw l) (hA_nonneg w _)

theorem hA_mono (w : ℕ → ℝ) {K K' : ℕ} (hK' : K' ≠ 0) (h : K ∣ K') : hA w K ≤ hA w K' := by
  rw [hA_apply, hA_apply]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Nat.divisors_subset_of_dvd hK' h)
    fun _ _ _ => sq_nonneg _

theorem one_le_hA (w : ℕ → ℝ) {K : ℕ} (hK : K ≠ 0) : 1 ≤ hA w K := by
  have := hA_mono w hK (one_dvd K)
  rw [hA_apply, Nat.divisors_one, Finset.sum_singleton, cmul_one, one_pow] at this
  exact this

/-- `H = (g ⋆ φ²) ⋆ 1` is monotone under divisibility. -/
theorem HA_mono (hw : ∀ p, 0 ≤ w p) {K K' : ℕ} (hK' : K' ≠ 0) (h : K ∣ K') :
    HA w K ≤ HA w K' := by
  have e : HA w = (gA w * (phiA w).pmul (phiA w)) *
      (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by
    unfold HA hA; rw [mul_assoc]
  have hF : ∀ d, 0 ≤ (gA w * (phiA w).pmul (phiA w)) d := fun d => by
    rw [ArithmeticFunction.mul_apply]
    refine Finset.sum_nonneg fun x _ => mul_nonneg (gA_nonneg hw _) ?_
    rw [ArithmeticFunction.pmul_apply]; exact mul_self_nonneg _
  rw [e, ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.coe_mul_zeta_apply]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Nat.divisors_subset_of_dvd hK' h)
    fun d _ _ => hF d

theorem hA_le_HA (hw : ∀ p, 0 ≤ w p) {K : ℕ} (hK : K ≠ 0) : hA w K ≤ HA w K := by
  rw [HA_apply]
  have h1 : (1 : ℕ) ∈ K.divisors := Nat.mem_divisors.mpr ⟨one_dvd K, hK⟩
  have := Finset.single_le_sum (f := fun l => gA w l * hA w (K / l))
    (fun l _ => mul_nonneg (gA_nonneg hw l) (hA_nonneg w _)) h1
  simpa [gA_apply one_ne_zero, cmul_one] using this

/-! ## The Toeplitz bound on completely multiplicative resonators -/

/-- `c(k) = 1_{k ∣ N} φ(k)`. -/
def cres (w : ℕ → ℝ) (N k : ℕ) : ℂ := if k ∣ N then (cmul w k : ℂ) else 0

theorem sum_cres_mul {N n : ℕ} (hN : 1 ≤ N) (hn : 1 ≤ n) :
    ∑ k ∈ Finset.Icc 1 N, cres w N (n * k) * conj (cres w N k) =
      ((if n ∣ N then cmul w n * hA w (N / n) else 0 : ℝ) : ℂ) := by
  have hpt : ∀ k ∈ Finset.Icc 1 N, cres w N (n * k) * conj (cres w N k) =
      ((if n * k ∣ N then cmul w n * cmul w k ^ 2 else 0 : ℝ) : ℂ) := by
    intro k hk
    have hk1 : k ≠ 0 := by have := (Finset.mem_Icc.mp hk).1; omega
    unfold cres
    by_cases h1 : n * k ∣ N
    · have h2 : k ∣ N := (Dvd.intro_left n rfl).trans h1
      rw [if_pos h1, if_pos h2, if_pos h1, cmul_mul w (by omega) hk1, Complex.conj_ofReal]
      push_cast; ring
    · rw [if_neg h1, if_neg h1, zero_mul, Complex.ofReal_zero]
  rw [Finset.sum_congr rfl hpt, ← Complex.ofReal_sum]
  congr 1
  by_cases hn' : n ∣ N
  · rw [if_pos hn', hA_apply, Finset.mul_sum]
    have key : ∀ k, (n * k ∣ N ↔ k ∣ N / n) := fun k => by
      rw [Nat.dvd_div_iff_mul_dvd hn', mul_comm]
    rw [← Finset.sum_filter]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors, key]
    have hq : N / n ≠ 0 :=
      Nat.pos_iff_ne_zero.mp (Nat.div_pos (Nat.le_of_dvd (by omega) hn') (by omega : 0 < n))
    constructor
    · rintro ⟨-, h⟩; exact ⟨h, hq⟩
    · rintro ⟨h, -⟩
      have hk0 : 0 < k := Nat.pos_of_dvd_of_pos h (Nat.pos_iff_ne_zero.mpr hq)
      exact ⟨⟨hk0, Nat.le_of_dvd (by omega) (h.trans (Nat.div_dvd_of_dvd hn'))⟩, h⟩
  · rw [if_neg hn']
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [if_neg]
    intro h
    exact hn' ((Dvd.intro k rfl).trans h)

theorem sum_norm_sq_cres {N : ℕ} (hN : 1 ≤ N) :
    ∑ k ∈ Finset.Icc 1 N, ‖cres w N k‖ ^ 2 = hA w N := by
  have h : ∀ k, ‖cres w N k‖ ^ 2 = if k ∣ N then cmul w k ^ 2 else 0 := fun k => by
    unfold cres
    split_ifs
    · rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    · simp
  simp_rw [h]
  rw [PrimorialResonance.sum_Icc_ite_dvd hN, hA_apply]

/-- **The Toeplitz bound on `c = 1_{· ∣ N} φ`**:
`2 Σ_{n ∣ N, n ≥ 2} λ(n) g(n) h(N/n) ≤ (log N + C₀) h(N)`. -/
theorem toeplitz_cmul {lam : ℕ → ℝ} (hW : WeilPositive lam) :
    ∃ C₀ : ℝ, ∀ w : ℕ → ℝ, (∀ p, 0 ≤ w p) → ∀ N : ℕ, 1 ≤ N →
      2 * ∑ n ∈ N.divisors with 2 ≤ n, lam n * gA w n * hA w (N / n) ≤
        (Real.log N + C₀) * hA w N := by
  obtain ⟨C₀, hC⟩ := weil_multiplicativeToeplitz_bound hW
  refine ⟨C₀, fun w hw N hN => ?_⟩
  have hsupp : ∀ k, N < k → cres w N k = 0 := fun k hk => by
    unfold cres; rw [if_neg]; intro h; exact absurd (Nat.le_of_dvd (by omega) h) (by omega)
  have h := hC N hN (cres w N) hsupp
  rw [sum_norm_sq_cres hN] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  have hpt : ∀ n ∈ Finset.Icc 2 N, lam n / Real.sqrt n *
      (∑ k ∈ Finset.Icc 1 N, cres w N (n * k) * conj (cres w N k)).re =
      if n ∣ N then lam n * gA w n * hA w (N / n) else 0 := by
    intro n hn
    have hn2 := (Finset.mem_Icc.mp hn).1
    rw [sum_cres_mul hN (by omega), Complex.ofReal_re]
    split_ifs
    · rw [gA_apply (by omega)]; ring
    · ring
  rw [Finset.sum_congr rfl hpt, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext n
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨hd, -⟩, h2⟩; exact ⟨⟨h2, Nat.le_of_dvd (by omega) hd⟩, hd⟩
  · rintro ⟨⟨h2, -⟩, hd⟩; exact ⟨⟨hd, by omega⟩, h2⟩

/-! ## The ζ-part as a Dirichlet convolution -/

/-- `k ↦ m(k) g(k)`. -/
def mgA (w m : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun k => if k = 0 then 0 else m k * gA w k, if_pos rfl⟩

variable {m v : ℕ → ℝ} {β : ℝ}

theorem mgA_mul_gA_apply {n : ℕ} (hn : n ≠ 0) :
    (mgA w m * gA w) n = (∑ k ∈ n.divisors, m k) * gA w n := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun x y => mgA w m x * gA w y),
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk0 : k ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hk)
  have hkd := Nat.dvd_of_mem_divisors hk
  have hq : n / k ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hkd) (Nat.pos_of_ne_zero hk0)).ne'
  change (if k = 0 then 0 else m k * gA w k) * gA w (n / k) = _
  rw [if_neg hk0, mul_assoc, ← gA_mul hk0 hq, Nat.mul_div_cancel' hkd]

/-- **The ζ-part**: `Σ_{n ∣ N} (1 ⋆ m)(n) g(n) h(N/n) = Σ_{k ∣ N} m(k) g(k) H(N/k)`. -/
theorem sum_divisors_conv_eq (N : ℕ) :
    ∑ n ∈ N.divisors, (∑ k ∈ n.divisors, m k) * gA w n * hA w (N / n) =
      ∑ k ∈ N.divisors, m k * gA w k * HA w (N / k) := by
  have h1 : ((mgA w m * gA w) * hA w) N =
      ∑ n ∈ N.divisors, (∑ k ∈ n.divisors, m k) * gA w n * hA w (N / n) := by
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun x y => (mgA w m * gA w) x * hA w y)]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [mgA_mul_gA_apply (Nat.ne_of_gt (Nat.pos_of_mem_divisors hn))]
  have h2 : (mgA w m * (gA w * hA w)) N = ∑ k ∈ N.divisors, m k * gA w k * HA w (N / k) := by
    rw [ArithmeticFunction.mul_apply,
      Nat.sum_divisorsAntidiagonal (fun x y => mgA w m x * (gA w * hA w) y)]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hk0 : k ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hk)
    change (if k = 0 then 0 else m k * gA w k) * (gA w * hA w) (N / k) = _
    rw [if_neg hk0]
    rfl
  rw [← h1, ← h2, mul_assoc]

theorem filter_divisors_not_two_le {N : ℕ} (hN : 1 ≤ N) :
    N.divisors.filter (fun n => ¬ 2 ≤ n) = {1} := by
  ext n
  simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hd, -⟩, h2⟩
    have := Nat.pos_of_dvd_of_pos hd (by omega)
    omega
  · rintro rfl; exact ⟨⟨one_dvd N, by omega⟩, by omega⟩

/-- **The Toeplitz inequality for carrier systems**:
`2 Σ_{k ∣ N} m(k) g(k) H(N/k) ≤ ((1 + 2|β|) log N + C₀ + 2|m(1)| + 2 S_v) h(N)`. -/
theorem toeplitz_carrier (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (carrierSystem β m v)) :
    ∃ C₀ : ℝ, ∀ w : ℕ → ℝ, (∀ p, 0 ≤ w p) → (∀ p, w p ≤ 1) → ∀ N : ℕ, 1 ≤ N →
      2 * ∑ k ∈ N.divisors, m k * gA w k * HA w (N / k) ≤
        ((1 + 2 * |β|) * Real.log N + C₀ + 2 * |m 1| +
          2 * ∑' n : ℕ, |v n| / Real.sqrt n) * hA w N := by
  obtain ⟨C₀, hC⟩ := toeplitz_cmul (weilPositive_of_weilPositiveFull hW)
  refine ⟨C₀, fun w hw hw1 N hN => ?_⟩
  have h := hC w hw N hN
  have hN0 : N ≠ 0 := by omega
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hhN : 0 ≤ hA w N := hA_nonneg w N
  obtain ⟨Sv, hSv⟩ : ∃ Sv, Sv = ∑' n : ℕ, |v n| / Real.sqrt n := ⟨_, rfl⟩
  have hsv := summable_abs_div_sqrt hv.summable
  -- split the weights
  have hsplit : ∑ n ∈ N.divisors with 2 ≤ n, carrierSystem β m v n * gA w n * hA w (N / n) =
      β * (∑ n ∈ N.divisors with 2 ≤ n, (ArithmeticFunction.vonMangoldt n : ℝ) * gA w n *
          hA w (N / n)) +
        ∑ n ∈ N.divisors with 2 ≤ n, (∑ k ∈ n.divisors, m k) * gA w n * hA w (N / n) +
          ∑ n ∈ N.divisors with 2 ≤ n, v n * gA w n * hA w (N / n) := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n hn => ?_
    have h2 := (Finset.mem_filter.mp hn).2
    unfold carrierSystem carrier
    rw [if_pos h2]; ring
  -- the `ζ`-part
  have hZ : ∑ n ∈ N.divisors with 2 ≤ n, (∑ k ∈ n.divisors, m k) * gA w n * hA w (N / n) =
      ∑ k ∈ N.divisors, m k * gA w k * HA w (N / k) - m 1 * hA w N := by
    rw [← sum_divisors_conv_eq, ← Finset.sum_filter_add_sum_filter_not N.divisors
      (fun n => 2 ≤ n), filter_divisors_not_two_le hN, Finset.sum_singleton, Nat.divisors_one,
      Finset.sum_singleton, gA_apply one_ne_zero, cmul_one, Nat.div_one]
    simp
  -- the `Λ`-part
  have hΛ0 : 0 ≤ ∑ n ∈ N.divisors with 2 ≤ n, (ArithmeticFunction.vonMangoldt n : ℝ) *
      gA w n * hA w (N / n) :=
    Finset.sum_nonneg fun n _ => mul_nonneg (mul_nonneg ArithmeticFunction.vonMangoldt_nonneg
      (gA_nonneg hw n)) (hA_nonneg w _)
  have hΛ1 : ∑ n ∈ N.divisors with 2 ≤ n, (ArithmeticFunction.vonMangoldt n : ℝ) *
      gA w n * hA w (N / n) ≤ Real.log N * hA w N := by
    calc _ ≤ ∑ n ∈ N.divisors, (ArithmeticFunction.vonMangoldt n : ℝ) * hA w N := by
          refine (Finset.sum_le_sum fun n hn => ?_).trans
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              fun n _ _ => mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hhN)
          have hnd := Nat.mem_divisors.mp (Finset.mem_filter.mp hn).1
          have hn0 : n ≠ 0 := by have := (Finset.mem_filter.mp hn).2; omega
          have hg : gA w n ≤ 1 := (gA_le hw hw1 hn0).trans (by
            rw [div_le_one (Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hn0))]
            rw [show (1 : ℝ) = Real.sqrt 1 by simp]
            exact Real.sqrt_le_sqrt (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn0))
          have hh : hA w (N / n) ≤ hA w N := hA_mono w hN0 (Nat.div_dvd_of_dvd hnd.1)
          have hL := ArithmeticFunction.vonMangoldt_nonneg (n := n)
          calc (ArithmeticFunction.vonMangoldt n : ℝ) * gA w n * hA w (N / n) ≤
                (ArithmeticFunction.vonMangoldt n : ℝ) * 1 * hA w N :=
                mul_le_mul (mul_le_mul_of_nonneg_left hg hL) hh (hA_nonneg w _) (by linarith)
            _ = _ := by ring
      _ = Real.log N * hA w N := by
          rw [← Finset.sum_mul, ArithmeticFunction.vonMangoldt_sum]
  -- the `v`-part
  have hv1 : |∑ n ∈ N.divisors with 2 ≤ n, v n * gA w n * hA w (N / n)| ≤ Sv * hA w N := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc _ ≤ ∑ n ∈ N.divisors with 2 ≤ n, |v n| / Real.sqrt n * hA w N := by
          refine Finset.sum_le_sum fun n hn => ?_
          have hnd := Nat.mem_divisors.mp (Finset.mem_filter.mp hn).1
          have hn0 : n ≠ 0 := by have := (Finset.mem_filter.mp hn).2; omega
          rw [abs_mul, abs_mul, abs_of_nonneg (gA_nonneg hw n), abs_of_nonneg (hA_nonneg w _)]
          have hh : hA w (N / n) ≤ hA w N := hA_mono w hN0 (Nat.div_dvd_of_dvd hnd.1)
          have hg := gA_le hw hw1 hn0
          calc |v n| * gA w n * hA w (N / n) ≤ |v n| * (1 / Real.sqrt n) * hA w N :=
                mul_le_mul (mul_le_mul_of_nonneg_left hg (abs_nonneg _)) hh (hA_nonneg w _)
                  (mul_nonneg (abs_nonneg _) (by positivity))
            _ = _ := by ring
      _ ≤ Sv * hA w N := by
          rw [← Finset.sum_mul, hSv]
          exact mul_le_mul_of_nonneg_right (hsv.sum_le_tsum _ fun n _ => div_nonneg
            (abs_nonneg _) (Real.sqrt_nonneg _)) hhN
  rw [hsplit, hZ] at h
  have hβΛ : -(|β| * (Real.log N * hA w N)) ≤ β * ∑ n ∈ N.divisors with 2 ≤ n,
      (ArithmeticFunction.vonMangoldt n : ℝ) * gA w n * hA w (N / n) := by
    have := abs_mul β (∑ n ∈ N.divisors with 2 ≤ n,
      (ArithmeticFunction.vonMangoldt n : ℝ) * gA w n * hA w (N / n))
    rw [abs_of_nonneg hΛ0] at this
    have h3 := neg_abs_le (β * ∑ n ∈ N.divisors with 2 ≤ n,
      (ArithmeticFunction.vonMangoldt n : ℝ) * gA w n * hA w (N / n))
    nlinarith [abs_nonneg β]
  have hm1 : m 1 * hA w N ≤ |m 1| * hA w N := mul_le_mul_of_nonneg_right (le_abs_self _) hhN
  rw [← hSv]
  nlinarith [(abs_le.mp hv1).1]

/-! ## The resonator: `s = 1` on primes `< L`, `s = ½` on primes `≥ L` -/

/-- `w_L(p) = p^{−½}` for `p < L`, `1` otherwise. -/
def wL (L p : ℕ) : ℝ := if p < L then (p : ℝ) ^ (-(1 / 2 : ℝ)) else 1

theorem wL_nonneg (L p : ℕ) : 0 ≤ wL L p := by unfold wL; split_ifs <;> positivity

theorem wL_le_one (L p : ℕ) : wL L p ≤ 1 := by
  unfold wL
  split_ifs
  · rcases Nat.eq_zero_or_pos p with h | h
    · subst h; rw [Nat.cast_zero, Real.zero_rpow (by norm_num)]; norm_num
    · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast h) (by norm_num)
  · exact le_rfl

/-- `A_J = ∏_{p < L} p^J`. -/
def Apow (L J : ℕ) : ℕ := ∏ p ∈ L.primesBelow, p ^ J

/-- The large primes `L ≤ p ≤ y`. -/
def bigPrimes (L y : ℕ) : Finset ℕ := y.primesLE.filter (L ≤ ·)

/-- `B = ∏_{L ≤ p ≤ y} p`. -/
def Bprod (L y : ℕ) : ℕ := ∏ p ∈ bigPrimes L y, p

theorem prime_of_mem_bigPrimes {L y p : ℕ} (hp : p ∈ bigPrimes L y) : p.Prime :=
  Nat.prime_of_mem_primesLE (Finset.mem_filter.mp hp).1

theorem le_of_mem_bigPrimes {L y p : ℕ} (hp : p ∈ bigPrimes L y) : L ≤ p :=
  (Finset.mem_filter.mp hp).2

theorem Apow_ne_zero (L J : ℕ) : Apow L J ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hp => pow_ne_zero _ (Nat.prime_of_mem_primesBelow hp).ne_zero

theorem Bprod_ne_zero (L y : ℕ) : Bprod L y ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ hp => (prime_of_mem_bigPrimes hp).ne_zero

theorem coprime_Apow_Bprod (L J y : ℕ) : (Apow L J).Coprime (Bprod L y) := by
  refine Nat.Coprime.prod_left fun p hp => Nat.Coprime.prod_right fun q hq => ?_
  have hp' := Nat.mem_primesBelow.mp hp
  have hq' := le_of_mem_bigPrimes hq
  exact Nat.Coprime.pow_left _ ((Nat.coprime_primes hp'.2 (prime_of_mem_bigPrimes hq)).mpr
    (by omega))

theorem Apow_mul (L a b : ℕ) : Apow L a * Apow L b = Apow L (a + b) := by
  unfold Apow; rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun p _ => (pow_add _ _ _).symm

theorem Apow_dvd {L a b : ℕ} (h : a ≤ b) : Apow L a ∣ Apow L b := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [← Apow_mul]; exact Dvd.intro _ rfl

theorem lt_of_prime_dvd_Apow {L J p : ℕ} (hp : p.Prime) (h : p ∣ Apow L J) : p < L := by
  obtain ⟨q, hq, hpq⟩ := (Nat.prime_iff.mp hp).dvd_finsetProd_iff _ |>.mp h
  have hq' := Nat.mem_primesBelow.mp hq
  have := (Nat.prime_dvd_prime_iff_eq hp hq'.2).mp (hp.dvd_of_dvd_pow hpq)
  omega

theorem factorization_Apow (L J p : ℕ) :
    (Apow L J).factorization p = if p ∈ L.primesBelow then J else 0 := by
  unfold Apow
  rw [Nat.factorization_prod fun q hq => pow_ne_zero _ (Nat.prime_of_mem_primesBelow hq).ne_zero,
    Finsupp.finsetSum_apply]
  simp_rw [Nat.factorization_pow, Finsupp.smul_apply]
  split_ifs with h
  · rw [Finset.sum_eq_single p]
    · rw [(Nat.prime_of_mem_primesBelow h).factorization_self, smul_eq_mul, mul_one]
    · intro q hq hqp
      rw [(Nat.prime_of_mem_primesBelow hq).factorization, Finsupp.single_apply, if_neg hqp,
        smul_zero]
    · intro h'; exact absurd h h'
  · refine Finset.sum_eq_zero fun q hq => ?_
    rw [(Nat.prime_of_mem_primesBelow hq).factorization, Finsupp.single_apply, if_neg, smul_zero]
    rintro rfl; exact h hq

/-- On divisors of `A_J`, `φ(k) = k^{−½}` and `g(k) = 1/k`. -/
theorem cmul_wL_of_dvd_Apow {L J k : ℕ} (hk : k ≠ 0) (h : k ∣ Apow L J) :
    cmul (wL L) k = (k : ℝ) ^ (-(1 / 2 : ℝ)) := by
  have hk' : (k : ℝ) = ∏ p ∈ k.primeFactors, (p : ℝ) ^ k.factorization p := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hk]
    rw [Nat.cast_finsuppProd, Finsupp.prod, Nat.support_factorization]
    push_cast; rfl
  rw [hk', ← Real.finsetProd_rpow _ _ fun p _ => by positivity]
  unfold cmul
  rw [Finsupp.prod, Nat.support_factorization]
  refine Finset.prod_congr rfl fun p hp => ?_
  have hpp := Nat.prime_of_mem_primeFactors hp
  have hpL := lt_of_prime_dvd_Apow hpp ((Nat.dvd_of_mem_primeFactors hp).trans h)
  unfold wL
  rw [if_pos hpL, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity),
    ← Real.rpow_mul (by positivity), mul_comm]

theorem gA_wL_of_dvd_Apow {L J k : ℕ} (hk : k ≠ 0) (h : k ∣ Apow L J) :
    gA (wL L) k = 1 / k := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast Nat.pos_of_ne_zero hk
  rw [gA_apply hk, cmul_wL_of_dvd_Apow hk h, Real.sqrt_eq_rpow, ← Real.rpow_sub hk0]
  norm_num
  rw [Real.rpow_neg_one]

/-- `h(p) = 2` and `H(p) = 2 + p^{−½}` at the large primes. -/
theorem hA_wL_prime {L p : ℕ} (hp : p.Prime) (hL : L ≤ p) : hA (wL L) p = 2 := by
  rw [hA_apply, hp.divisors, Finset.sum_pair (Ne.symm hp.one_lt.ne'), cmul_one]
  have := cmul_prime_pow (wL L) hp 1
  rw [pow_one] at this
  rw [this]
  unfold wL; rw [if_neg (by omega)]; norm_num

theorem HA_wL_prime {L p : ℕ} (hp : p.Prime) (hL : L ≤ p) :
    HA (wL L) p = 2 + 1 / Real.sqrt p := by
  rw [HA_apply, hp.divisors, Finset.sum_pair (Ne.symm hp.one_lt.ne'), Nat.div_one,
    Nat.div_self hp.pos, hA_wL_prime hp hL, gA_apply one_ne_zero, cmul_one, gA_apply hp.ne_zero]
  have := cmul_prime_pow (wL L) hp 1
  rw [pow_one] at this
  rw [this, hA_apply, Nat.divisors_one, Finset.sum_singleton, cmul_one]
  unfold wL; rw [if_neg (by omega)]; simp

theorem hA_Bprod (L y : ℕ) : hA (wL L) (Bprod L y) = 2 ^ (bigPrimes L y).card := by
  unfold Bprod
  rw [(isMultiplicative_hA _).map_prod_of_prime _ fun p hp => prime_of_mem_bigPrimes hp,
    Finset.prod_congr rfl fun p hp => hA_wL_prime (prime_of_mem_bigPrimes hp)
      (le_of_mem_bigPrimes hp), Finset.prod_const]

theorem HA_Bprod (L y : ℕ) :
    HA (wL L) (Bprod L y) = ∏ p ∈ bigPrimes L y, (2 + 1 / Real.sqrt p) := by
  unfold Bprod
  rw [(isMultiplicative_HA _).map_prod_of_prime _ fun p hp => prime_of_mem_bigPrimes hp]
  exact Finset.prod_congr rfl fun p hp => HA_wL_prime (prime_of_mem_bigPrimes hp)
    (le_of_mem_bigPrimes hp)

/-- `H(p^J) ≤ 4` at the small primes. -/
theorem HA_wL_prime_pow_le {L p : ℕ} (hp : p.Prime) (hL : p < L) (J : ℕ) :
    HA (wL L) (p ^ J) ≤ 4 := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by linarith
  have hw : wL L p = (p : ℝ) ^ (-(1 / 2 : ℝ)) := by unfold wL; rw [if_pos hL]
  have hw2 : wL L p ^ 2 = 1 / p := by
    rw [hw, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; norm_num
    rw [Real.rpow_neg_one]
  have hhA : ∀ j, hA (wL L) (p ^ j) ≤ 2 := by
    intro j
    rw [hA_apply, Nat.sum_divisors_prime_pow hp]
    simp_rw [cmul_prime_pow (wL L) hp, ← pow_mul, mul_comm _ 2, pow_mul, hw2]
    refine (Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (by positivity)
      (show 1 / (p : ℝ) ≤ 1 / 2 by rw [div_le_div_iff₀ hp0 (by norm_num)]; linarith) i).trans
      (sum_geometric_two_le _)
  have hgA : ∀ i, gA (wL L) (p ^ i) ≤ (1 / 2) ^ i := by
    intro i
    rw [gA_apply (pow_ne_zero _ hp.ne_zero), cmul_prime_pow (wL L) hp, Nat.cast_pow,
      Real.sqrt_eq_rpow, ← Real.rpow_natCast (p : ℝ) i, ← Real.rpow_mul hp0.le, hw,
      ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, div_eq_mul_inv, ← Real.rpow_neg hp0.le,
      ← Real.rpow_add hp0]
    have : -(1 / 2 : ℝ) * i + -((i : ℝ) * (1 / 2)) = -(i : ℝ) := by ring
    rw [this, Real.rpow_neg hp0.le, Real.rpow_natCast, ← inv_pow, one_div]
    exact pow_le_pow_left₀ (by positivity) (by rw [inv_le_inv₀ hp0 (by norm_num)]; linarith) i
  rw [HA_apply, Nat.sum_divisors_prime_pow hp]
  calc ∑ i ∈ Finset.range (J + 1), gA (wL L) (p ^ i) * hA (wL L) (p ^ J / p ^ i)
      ≤ ∑ i ∈ Finset.range (J + 1), (1 / 2 : ℝ) ^ i * 2 := by
        refine Finset.sum_le_sum fun i hi => ?_
        have hiJ : i ≤ J := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
        rw [Nat.pow_div hiJ hp.pos]
        exact mul_le_mul (hgA i) (hhA _) (hA_nonneg _ _) (by positivity)
    _ = 2 * ∑ i ∈ Finset.range (J + 1), (1 / 2 : ℝ) ^ i := by rw [Finset.mul_sum]; ring_nf
    _ ≤ 2 * 2 := by gcongr; exact sum_geometric_two_le _
    _ = 4 := by norm_num

theorem HA_Apow_le (L J : ℕ) : HA (wL L) (Apow L J) ≤ 4 ^ L.primesBelow.card := by
  unfold Apow
  rw [(isMultiplicative_HA _).map_prod (fun p => p ^ J) _ fun p hp q hq hpq =>
    Nat.Coprime.pow _ _ ((Nat.coprime_primes (Nat.prime_of_mem_primesBelow hp)
      (Nat.prime_of_mem_primesBelow hq)).mpr hpq), ← Finset.prod_const]
  exact Finset.prod_le_prod (fun p _ => HA_nonneg (wL_nonneg L) _) fun p hp =>
    HA_wL_prime_pow_le (Nat.prime_of_mem_primesBelow hp) (Nat.mem_primesBelow.mp hp).1 J

theorem monotone_HA_Apow (L : ℕ) : Monotone fun J => HA (wL L) (Apow L J) :=
  monotone_nat_of_le_succ fun J => HA_mono (wL_nonneg L) (Apow_ne_zero L (J + 1))
    (Apow_dvd (Nat.le_succ J))

/-- `H(A_J) − H(A_{J−r}) → 0`. -/
theorem tendsto_HA_Apow_sub (L r : ℕ) :
    Tendsto (fun J => HA (wL L) (Apow L J) - HA (wL L) (Apow L (J - r))) atTop (𝓝 0) := by
  have hb : BddAbove (Set.range fun J => HA (wL L) (Apow L J)) := by
    refine ⟨4 ^ L.primesBelow.card, ?_⟩
    rintro _ ⟨J, rfl⟩
    exact HA_Apow_le L J
  have h1 := tendsto_atTop_ciSup (monotone_HA_Apow L) hb
  have h2 := h1.comp (tendsto_sub_atTop_nat r)
  simpa using h1.sub h2

/-! ## Divisors of `A_J` and of `N = A_J B` -/

theorem dvd_Apow_of_le {L J K k : ℕ} (hk : k ≠ 0) (h : k ∣ Apow L J) (hkK : k ≤ K) :
    k ∣ Apow L K := by
  refine (Nat.factorization_le_iff_dvd hk (Apow_ne_zero L K)).mp fun p => ?_
  have hJ := (Nat.factorization_le_iff_dvd hk (Apow_ne_zero L J)).mpr h p
  rw [factorization_Apow] at hJ ⊢
  split_ifs at hJ ⊢ with hp
  · have := Nat.factorization_lt p hk; omega
  · exact hJ

theorem Apow_sub_dvd_div {L J K k : ℕ} (h : k ∣ Apow L K) (hKJ : K ≤ J) :
    Apow L (J - K) ∣ Apow L J / k := by
  have e : Apow L J = Apow L K * Apow L (J - K) := by
    rw [Apow_mul, Nat.add_sub_cancel' hKJ]
  rw [e, Nat.mul_div_right_comm h]
  exact Dvd.intro_left _ rfl

theorem le_of_not_dvd_Apow {L J k : ℕ} (hk : k ≠ 0) (h : ¬ k ∣ Apow L J) :
    L ≤ k ∨ 2 ^ (J + 1) ≤ k := by
  have hn : ¬ k.factorization ≤ (Apow L J).factorization :=
    fun hle => h ((Nat.factorization_le_iff_dvd hk (Apow_ne_zero L J)).mp hle)
  rw [Finsupp.le_def] at hn
  push Not at hn
  obtain ⟨p, hp⟩ := hn
  have hpos : 0 < k.factorization p := lt_of_le_of_lt (Nat.zero_le _) hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors
    (Nat.support_factorization k ▸ Finsupp.mem_support_iff.mpr hpos.ne')
  have hpk : p ∣ k := (Nat.Prime.dvd_iff_one_le_factorization hpp hk).mpr hpos
  rw [factorization_Apow] at hp
  split_ifs at hp with hS
  · right
    have h1 : p ^ (J + 1) ∣ k := (Nat.pow_dvd_pow p hp).trans (Nat.ordProj_dvd k p)
    exact (Nat.pow_le_pow_left hpp.two_le _).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) h1)
  · left
    have hL : L ≤ p := by
      by_contra hlt; push Not at hlt
      exact hS (Nat.mem_primesBelow.mpr ⟨hlt, hpp⟩)
    exact hL.trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) hpk)

theorem le_of_dvd_N_not_dvd_Apow {L J y k : ℕ} (hN : k ∣ Apow L J * Bprod L y)
    (h : ¬ k ∣ Apow L J) (hk : k ≠ 0) : L ≤ k := by
  have hnc : ¬ k.Coprime (Bprod L y) := fun hc => h (hc.dvd_of_dvd_mul_right hN)
  obtain ⟨p, hpp, hpk, hpB⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  obtain ⟨q, hq, hpq⟩ := (Nat.prime_iff.mp hpp).dvd_finsetProd_iff _ |>.mp hpB
  have := (Nat.prime_dvd_prime_iff_eq hpp (prime_of_mem_bigPrimes hq)).mp hpq
  subst this
  exact (le_of_mem_bigPrimes hq).trans (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) hpk)

/-! ## The lower bound for the ζ-part -/

theorem tsum_eq_sum_add_ite {f : ℕ → ℝ} (hf : Summable f) (s : Finset ℕ) :
    ∑' j, f j = ∑ j ∈ s, f j + ∑' j, (if j ∈ s then 0 else f j) := by
  have h1 : Summable fun j => if j ∈ s then f j else 0 :=
    summable_of_ne_finset_zero (s := s) fun j hj => if_neg hj
  have h2 : Summable fun j => if j ∈ s then 0 else f j :=
    (hf.sub h1).congr fun j => by split_ifs <;> simp
  have e1 : ∑' j, (if j ∈ s then f j else 0) = ∑ j ∈ s, f j := by
    rw [tsum_eq_sum (s := s) fun j hj => if_neg hj]
    exact Finset.sum_congr rfl fun j hj => if_pos hj
  rw [← e1, ← h1.tsum_add h2]
  exact tsum_congr fun j => by split_ifs <;> simp

theorem summable_ite_of_nonneg (P : ℕ → Prop) [DecidablePred P] {f : ℕ → ℝ} (hf : Summable f)
    (hf0 : ∀ j, 0 ≤ f j) : Summable fun j => if P j then f j else 0 :=
  Summable.of_nonneg_of_le (fun j => by split_ifs; exacts [hf0 j, le_rfl])
    (fun j => by split_ifs; exacts [le_rfl, hf0 j]) hf

theorem summable_abs_div_nat (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2)) :
    Summable fun j : ℕ => |m j| / j := by
  refine Summable.of_nonneg_of_le (fun j => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
    (fun j => ?_) (summable_abs_div_sqrt hm)
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; simp
  · have h1 : (1 : ℝ) ≤ j := by exact_mod_cast h
    exact div_le_div_of_nonneg_left (abs_nonneg _) (Real.sqrt_pos.mpr (by linarith))
      (by rw [Real.sqrt_le_left (by linarith)]; nlinarith)

/-- `Σ_{k ∣ A_J} m(k)/k ≥ M(1) − T₁`. -/
theorem sum_divisors_Apow_ge (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2)) (L J : ℕ) :
    mu m - ∑' j, (if L ≤ j ∨ 2 ^ (J + 1) ≤ j then |m j| / j else 0) ≤
      ∑ k ∈ (Apow L J).divisors, m k / k := by
  have hs0 := summable_abs_div_nat hm
  have hsum : Summable fun j : ℕ => m j / j := by
    refine Summable.of_norm_bounded hs0 fun j => ?_
    rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
  have hsplit := tsum_eq_sum_add_ite hsum (Apow L J).divisors
  rw [← mu_eq_tsum hm] at hsplit
  have hs : Summable fun j => if j ∈ (Apow L J).divisors then 0 else m j / j :=
    Summable.of_norm_bounded hs0 fun j => by
      split_ifs
      · rw [norm_zero]; exact div_nonneg (abs_nonneg _) (Nat.cast_nonneg (α := ℝ) j)
      · rw [Real.norm_eq_abs, abs_div, Nat.abs_cast]
  have hrest : |∑' j, (if j ∈ (Apow L J).divisors then 0 else m j / j)| ≤
      ∑' j, (if L ≤ j ∨ 2 ^ (J + 1) ≤ j then |m j| / j else 0) := by
    refine (norm_tsum_le_tsum_norm hs.norm).trans (Summable.tsum_le_tsum (fun j => ?_)
      hs.norm (summable_ite_of_nonneg _ hs0 fun _ => div_nonneg (abs_nonneg _)
        (Nat.cast_nonneg _)))
    by_cases hj : j ∈ (Apow L J).divisors
    · rw [if_pos hj, norm_zero]
      split_ifs
      · exact div_nonneg (abs_nonneg _) (Nat.cast_nonneg (α := ℝ) j)
      · exact le_rfl
    · rw [if_neg hj, Real.norm_eq_abs, abs_div, Nat.abs_cast]
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0; simp
      · have hnd : ¬ j ∣ Apow L J := fun h => hj (Nat.mem_divisors.mpr ⟨h, Apow_ne_zero L J⟩)
        rw [if_pos (le_of_not_dvd_Apow h0.ne' hnd)]
  linarith [(abs_le.mp hrest).2]

/-- The defect weight `D(k)`: `H(A_J) − H(A_{J−K})` for `k ≤ K`, else `H(A_J)`. -/
def defectW (L J K k : ℕ) : ℝ :=
  if k ≤ K then HA (wL L) (Apow L J) - HA (wL L) (Apow L (J - K)) else HA (wL L) (Apow L J)

theorem main_term_ge {L J K k : ℕ} (hKJ : K ≤ J) (hk : k ∈ (Apow L J).divisors) :
    HA (wL L) (Apow L J) * (m k / k) - |m k| / k * defectW L J K k ≤
      m k / k * HA (wL L) (Apow L J / k) := by
  have hw0 := wL_nonneg L
  have hkA := Nat.dvd_of_mem_divisors hk
  have hk0 : k ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hk)
  have hA0 := Apow_ne_zero L J
  have hAk0 : Apow L J / k ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hA0) hkA) (Nat.pos_of_ne_zero hk0)).ne'
  have hle : HA (wL L) (Apow L J / k) ≤ HA (wL L) (Apow L J) :=
    HA_mono hw0 hA0 (Nat.div_dvd_of_dvd hkA)
  have hd0 : 0 ≤ HA (wL L) (Apow L J) - HA (wL L) (Apow L J / k) := by linarith
  have hdk : HA (wL L) (Apow L J) - HA (wL L) (Apow L J / k) ≤ defectW L J K k := by
    unfold defectW
    split_ifs with hkK
    · have h2 := Apow_sub_dvd_div (dvd_Apow_of_le hk0 hkA hkK) hKJ
      linarith [HA_mono hw0 hAk0 h2]
    · linarith [HA_nonneg hw0 (Apow L J / k)]
  have hmk : m k / k * (HA (wL L) (Apow L J) - HA (wL L) (Apow L J / k)) ≤
      |m k| / k * (HA (wL L) (Apow L J) - HA (wL L) (Apow L J / k)) :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (le_abs_self _)
      (Nat.cast_nonneg _)) hd0
  have hmk2 : |m k| / k * (HA (wL L) (Apow L J) - HA (wL L) (Apow L J / k)) ≤
      |m k| / k * defectW L J K k :=
    mul_le_mul_of_nonneg_left hdk (div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))
  have e : m k / k * HA (wL L) (Apow L J / k) = HA (wL L) (Apow L J) * (m k / k) -
      m k / k * (HA (wL L) (Apow L J) - HA (wL L) (Apow L J / k)) := by ring
  rw [e]
  linarith

theorem defect_sum_le (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2)) (L J K : ℕ) :
    ∑ k ∈ (Apow L J).divisors, |m k| / k * defectW L J K k ≤
      HA (wL L) (Apow L J) * ((HA (wL L) (Apow L J) - HA (wL L) (Apow L (J - K))) *
        ∑' j : ℕ, |m j| / j + ∑' j, (if K < j then |m j| / j else 0)) := by
  have hw0 := wL_nonneg L
  have hs0 := summable_abs_div_nat hm
  obtain ⟨H, hH⟩ : ∃ H, H = HA (wL L) (Apow L J) := ⟨_, rfl⟩
  obtain ⟨δ, hδ⟩ : ∃ δ, δ = HA (wL L) (Apow L J) - HA (wL L) (Apow L (J - K)) := ⟨_, rfl⟩
  have hH1 : 1 ≤ H := hH ▸ (one_le_hA _ (Apow_ne_zero L J)).trans (hA_le_HA hw0 (Apow_ne_zero L J))
  have hδ0 : 0 ≤ δ := by
    have := HA_mono hw0 (Apow_ne_zero L J) (Apow_dvd (L := L) (Nat.sub_le J K))
    rw [hδ]; linarith
  have hpt : ∀ k ∈ (Apow L J).divisors, |m k| / k * defectW L J K k ≤
      H * (δ * (|m k| / k) + (if K < k then |m k| / k else 0)) := by
    intro k _
    have hmk : 0 ≤ |m k| / k := div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
    unfold defectW
    rw [← hδ, ← hH]
    split_ifs with h1 h2 h2
    · omega
    · nlinarith [mul_le_mul_of_nonneg_right hH1 (mul_nonneg hδ0 hmk)]
    · nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ H) hδ0) hmk]
    · omega
  rw [← hδ, ← hH]
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left
    (hs0.sum_le_tsum _ fun _ _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) hδ0)
    ((summable_ite_of_nonneg _ hs0 fun _ => div_nonneg (abs_nonneg _)
      (Nat.cast_nonneg _)).sum_le_tsum _ fun j _ => ?_)) (by linarith : (0 : ℝ) ≤ H)
  split_ifs
  · exact div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
  · exact le_rfl

theorem off_part_le (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2)) (L J y : ℕ) :
    |∑ k ∈ (Apow L J * Bprod L y).divisors with ¬ k ∣ Apow L J, m k * gA (wL L) k *
      HA (wL L) (Apow L J * Bprod L y / k)| ≤ HA (wL L) (Apow L J * Bprod L y) *
        ∑' j, (if L ≤ j then |m j| / Real.sqrt j else 0) := by
  have hw0 := wL_nonneg L
  have hw1 := wL_le_one L
  have hs1 := summable_abs_div_sqrt hm
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hpt : ∀ k ∈ (Apow L J * Bprod L y).divisors.filter (fun k => ¬ k ∣ Apow L J),
      |m k * gA (wL L) k * HA (wL L) (Apow L J * Bprod L y / k)| ≤
        HA (wL L) (Apow L J * Bprod L y) * (if L ≤ k then |m k| / Real.sqrt k else 0) := by
    intro k hk
    obtain ⟨hkN, hkA⟩ := Finset.mem_filter.mp hk
    have hkN' := Nat.mem_divisors.mp hkN
    have hk0 : k ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hkN)
    have hLk : L ≤ k := le_of_dvd_N_not_dvd_Apow hkN'.1 hkA hk0
    rw [if_pos hLk, abs_mul, abs_mul, abs_of_nonneg (gA_nonneg hw0 k),
      abs_of_nonneg (HA_nonneg hw0 _)]
    have hg := gA_le hw0 hw1 hk0
    have hH := HA_mono hw0 hkN'.2 (Nat.div_dvd_of_dvd hkN'.1)
    calc |m k| * gA (wL L) k * HA (wL L) (Apow L J * Bprod L y / k) ≤
          |m k| * (1 / Real.sqrt k) * HA (wL L) (Apow L J * Bprod L y) :=
          mul_le_mul (mul_le_mul_of_nonneg_left hg (abs_nonneg _)) hH (HA_nonneg hw0 _)
            (mul_nonneg (abs_nonneg _) (by positivity))
      _ = _ := by ring
  refine (Finset.sum_le_sum hpt).trans ?_
  rw [← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((summable_ite_of_nonneg _ hs1 fun _ => div_nonneg
    (abs_nonneg _) (Real.sqrt_nonneg _)).sum_le_tsum _ fun j _ => ?_) (HA_nonneg hw0 _)
  split_ifs
  · exact div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  · exact le_rfl

theorem sum_A_part_eq {L J y : ℕ} :
    ∑ k ∈ (Apow L J * Bprod L y).divisors with k ∣ Apow L J, m k * gA (wL L) k *
      HA (wL L) (Apow L J * Bprod L y / k) =
      HA (wL L) (Bprod L y) * ∑ k ∈ (Apow L J).divisors, m k / k * HA (wL L) (Apow L J / k) := by
  have hA0 := Apow_ne_zero L J
  have hB0 := Bprod_ne_zero L y
  have hcop := coprime_Apow_Bprod L J y
  have hfilt : (Apow L J * Bprod L y).divisors.filter (fun k => k ∣ Apow L J) =
      (Apow L J).divisors := by
    ext k
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨-, h⟩; exact ⟨h, hA0⟩
    · rintro ⟨h, -⟩; exact ⟨⟨h.trans (Dvd.intro _ rfl), mul_ne_zero hA0 hB0⟩, h⟩
  rw [hfilt, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkA := Nat.dvd_of_mem_divisors hk
  have hk0 : k ≠ 0 := Nat.ne_of_gt (Nat.pos_of_mem_divisors hk)
  rw [gA_wL_of_dvd_Apow hk0 hkA, Nat.mul_div_right_comm hkA,
    (isMultiplicative_HA _).map_mul_of_coprime
      (Nat.Coprime.coprime_dvd_left (Nat.div_dvd_of_dvd hkA) hcop)]
  ring

/-- **The ζ-part on the resonator.** For `K ≤ J`,
`Σ_{k ∣ N} m(k) g(k) H(N/k) ≥ H(N)(M(1) − T₁ − δ T₀ − T₂ − T₃)`, with `δ = H(A_J) − H(A_{J−K})`,
`T₀ = Σ|m(k)|/k`, `T₁` the part of `T₀` over `k ≥ min(L, 2^{J+1})`, `T₂` the part over `k > K`,
and `T₃ = Σ_{k ≥ L} |m(k)|/√k`. -/
theorem zetaPart_ge (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2)) {L J K y : ℕ}
    (hKJ : K ≤ J) :
    HA (wL L) (Apow L J * Bprod L y) * (mu m -
        ∑' j, (if L ≤ j ∨ 2 ^ (J + 1) ≤ j then |m j| / j else 0) -
        (HA (wL L) (Apow L J) - HA (wL L) (Apow L (J - K))) * ∑' j : ℕ, |m j| / j -
        ∑' j, (if K < j then |m j| / j else 0) -
        ∑' j, (if L ≤ j then |m j| / Real.sqrt j else 0)) ≤
      ∑ k ∈ (Apow L J * Bprod L y).divisors, m k * gA (wL L) k *
        HA (wL L) (Apow L J * Bprod L y / k) := by
  have hw0 := wL_nonneg L
  rw [← Finset.sum_filter_add_sum_filter_not _ (fun k => k ∣ Apow L J), sum_A_part_eq]
  have hoff := off_part_le hm L J y
  have h1 := sum_divisors_Apow_ge hm L J
  have h2 := defect_sum_le hm L J K
  have h3 := Finset.sum_le_sum (s := (Apow L J).divisors) fun k hk =>
    main_term_ge (m := m) (L := L) hKJ hk
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum] at h3
  have hHN := (isMultiplicative_HA (wL L)).map_mul_of_coprime (coprime_Apow_Bprod L J y)
  have hHB0 := HA_nonneg hw0 (Bprod L y)
  have hHA0 := HA_nonneg hw0 (Apow L J)
  obtain ⟨X, hX⟩ : ∃ X, X = ∑ k ∈ (Apow L J).divisors, m k / k * HA (wL L) (Apow L J / k) :=
    ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ Y, Y = ∑ k ∈ (Apow L J * Bprod L y).divisors with ¬ k ∣ Apow L J,
      m k * gA (wL L) k * HA (wL L) (Apow L J * Bprod L y / k) := ⟨_, rfl⟩
  rw [← hX] at h3 ⊢
  rw [← hY] at hoff ⊢
  rw [hHN] at hoff ⊢
  have hA : HA (wL L) (Apow L J) * (mu m -
      ∑' j, (if L ≤ j ∨ 2 ^ (J + 1) ≤ j then |m j| / j else 0) -
      (HA (wL L) (Apow L J) - HA (wL L) (Apow L (J - K))) * ∑' j : ℕ, |m j| / j -
      ∑' j, (if K < j then |m j| / j else 0)) ≤ X := by
    have := mul_le_mul_of_nonneg_left h1 hHA0
    nlinarith
  have := mul_le_mul_of_nonneg_left hA hHB0
  nlinarith [(abs_le.mp hoff).1]

/-! ## Tails and growth -/

theorem tendsto_tail {f : ℕ → ℝ} (hf : Summable f) :
    Tendsto (fun n => ∑' j, (if n ≤ j then f j else 0)) atTop (𝓝 0) := by
  have h := hf.hasSum.tendsto_sum_nat
  have e : ∀ n, ∑' j, (if n ≤ j then f j else 0) = ∑' j, f j - ∑ j ∈ Finset.range n, f j := by
    intro n
    have := tsum_eq_sum_add_ite hf (Finset.range n)
    have e2 : (fun j => if j ∈ Finset.range n then 0 else f j) =
        fun j => if n ≤ j then f j else 0 := by
      funext j; simp only [Finset.mem_range]; split_ifs <;> first | rfl | omega
    rw [e2] at this
    linarith
  simp_rw [e]
  simpa using (tendsto_const_nhds (x := ∑' j, f j)).sub h

theorem exists_tail_le {f : ℕ → ℝ} (hf : Summable f) {ε : ℝ} (hε : 0 < ε) :
    ∃ n₀ : ℕ, ∀ n, n₀ ≤ n → ∑' j, (if n ≤ j then f j else 0) ≤ ε := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.mp ((tendsto_tail hf).eventually (ge_mem_nhds hε))
  exact ⟨n₀, hn₀⟩

theorem prod_bigPrimes_ge (L y : ℕ) :
    (∏ p ∈ y.primesLE, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) / 2)) /
        ∏ p ∈ L.primesBelow, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) / 2) ≤
      ∏ p ∈ bigPrimes L y, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) / 2) := by
  have hpos : ∀ s : Finset ℕ, 0 < ∏ p ∈ s, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) / 2) := fun s =>
    Finset.prod_pos fun p _ => by positivity
  have hsplit := Finset.prod_filter_mul_prod_filter_not y.primesLE (fun p => L ≤ p)
    (f := fun p => (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) / 2))
  have hsub : y.primesLE.filter (fun p => ¬ L ≤ p) ⊆ L.primesBelow := fun p hp => by
    obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_of_mem_primesLE hp1⟩
  have hsmall : ∏ p ∈ y.primesLE.filter (fun p => ¬ L ≤ p), (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) / 2) ≤
      ∏ p ∈ L.primesBelow, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) / 2) := by
    rw [← Finset.prod_sdiff hsub]
    have h1 : 1 ≤ ∏ p ∈ L.primesBelow \ y.primesLE.filter (fun p => ¬ L ≤ p),
        (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) / 2) := by
      calc (1 : ℝ) = ∏ _p ∈ L.primesBelow \ y.primesLE.filter (fun p => ¬ L ≤ p), (1 : ℝ) :=
            Finset.prod_const_one.symm
        _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) fun p _ => by
            have : 0 ≤ (p : ℝ) ^ (-(1 / 2 : ℝ)) := by positivity
            linarith
    exact le_mul_of_one_le_left (le_of_lt (hpos _)) h1
  rw [div_le_iff₀ (hpos _), ← hsplit]
  unfold bigPrimes
  exact mul_le_mul_of_nonneg_left hsmall (le_of_lt (hpos _))

theorem log_Bprod_le (L y : ℕ) : Real.log (Bprod L y) ≤ y * Real.log 4 := by
  have hB : (Bprod L y : ℝ) ≤ primorial y := by
    have : Bprod L y ∣ primorial y := by
      unfold Bprod bigPrimes
      rw [primorial_eq_prod_primesLE]
      exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
    exact_mod_cast Nat.le_of_dvd (primorial_pos y) this
  have h0 : (0 : ℝ) < Bprod L y := by exact_mod_cast Nat.pos_of_ne_zero (Bprod_ne_zero L y)
  exact (Real.log_le_log h0 hB).trans (PrimorialResonance.log_primorial_le y)

/-! ## `M(1) > 0` is impossible -/

/-- **`M(1) ≤ 0`.** -/
theorem mu_nonpos (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2)) (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (carrierSystem β m v)) : mu m ≤ 0 := by
  by_contra hμ
  push Not at hμ
  obtain ⟨C₀, hC⟩ := toeplitz_carrier hv hW
  have hs0 := summable_abs_div_nat hm
  have hs1 := summable_abs_div_sqrt hm
  obtain ⟨T₀, hT₀⟩ : ∃ T₀, T₀ = ∑' j : ℕ, |m j| / j := ⟨_, rfl⟩
  have hT₀0 : 0 ≤ T₀ := hT₀ ▸ tsum_nonneg fun j => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)
  -- `L`: small tails at `k ≥ L`
  obtain ⟨L₀, hL₀⟩ := exists_tail_le hs1 (show 0 < mu m / 16 by linarith)
  obtain ⟨L, hL⟩ : ∃ L, L = max L₀ 1 := ⟨_, rfl⟩
  have hLL₀ : L₀ ≤ L := hL ▸ le_max_left _ _
  have hT3 := hL₀ L hLL₀
  have hT1' : ∑' j, (if L ≤ j then |m j| / j else 0) ≤ mu m / 16 := by
    refine le_trans (Summable.tsum_le_tsum (fun j => ?_) (summable_ite_of_nonneg _ hs0
      fun _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) (summable_ite_of_nonneg _ hs1
      fun _ => div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))) hT3
    split_ifs with h
    · rcases Nat.eq_zero_or_pos j with h0 | h0
      · subst h0; simp
      · have h1 : (1 : ℝ) ≤ j := by exact_mod_cast h0
        exact div_le_div_of_nonneg_left (abs_nonneg _) (Real.sqrt_pos.mpr (by linarith))
          (by rw [Real.sqrt_le_left (by linarith)]; nlinarith)
    · exact le_rfl
  -- `K`: small tail at `k > K`
  obtain ⟨K₁, hK₁⟩ := exists_tail_le hs0 (show 0 < mu m / 16 by linarith)
  have hT2 : ∑' j, (if K₁ < j then |m j| / j else 0) ≤ mu m / 16 := by
    refine le_trans (Summable.tsum_le_tsum (fun j => ?_) (summable_ite_of_nonneg _ hs0
      fun _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _)) (summable_ite_of_nonneg _ hs0
      fun _ => div_nonneg (abs_nonneg _) (Nat.cast_nonneg _))) (hK₁ K₁ le_rfl)
    split_ifs with h1 h2
    · exact le_rfl
    · omega
    · exact div_nonneg (abs_nonneg _) (Nat.cast_nonneg (α := ℝ) j)
    · exact le_rfl
  -- `J`: `δ` small and `J ≥ K₁, L`
  have hev := (tendsto_HA_Apow_sub L K₁).eventually
    (ge_mem_nhds (show 0 < mu m / (16 * (T₀ + 1)) by positivity))
  obtain ⟨J, hJδ, hJK, hJL⟩ := (hev.and ((eventually_ge_atTop K₁).and
    (eventually_ge_atTop L))).exists
  have hT1 : ∑' j, (if L ≤ j ∨ 2 ^ (J + 1) ≤ j then |m j| / j else 0) ≤ mu m / 16 := by
    refine le_trans (le_of_eq (tsum_congr fun j => ?_)) hT1'
    have : 2 ^ (J + 1) ≤ j → L ≤ j := fun h => by
      have := Nat.lt_two_pow_self (n := J + 1); omega
    by_cases h1 : L ≤ j
    · rw [if_pos (Or.inl h1), if_pos h1]
    · rw [if_neg (fun h => h1 (h.elim id this)), if_neg h1]
  have hδT : (HA (wL L) (Apow L J) - HA (wL L) (Apow L (J - K₁))) * T₀ ≤ mu m / 16 := by
    have hδ0 : 0 ≤ HA (wL L) (Apow L J) - HA (wL L) (Apow L (J - K₁)) := by
      have := HA_mono (wL_nonneg L) (Apow_ne_zero L J) (Apow_dvd (L := L) (Nat.sub_le J K₁))
      linarith
    calc _ ≤ mu m / (16 * (T₀ + 1)) * T₀ := mul_le_mul_of_nonneg_right hJδ hT₀0
      _ ≤ mu m / (16 * (T₀ + 1)) * (T₀ + 1) := by
          gcongr; linarith
      _ = mu m / 16 := by field_simp
  -- the resonance inequality at every `y`
  have key : ∀ y : ℕ, mu m * ∏ p ∈ bigPrimes L y, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) / 2) ≤
      (1 + 2 * |β|) * (Real.log (Apow L J) + y * Real.log 4) + C₀ + 2 * |m 1| +
        2 * ∑' n : ℕ, |v n| / Real.sqrt n := by
    intro y
    obtain ⟨N, hN⟩ : ∃ N, N = Apow L J * Bprod L y := ⟨_, rfl⟩
    have hA0 := Apow_ne_zero L J
    have hB0 := Bprod_ne_zero L y
    have hN1 : 1 ≤ N := by rw [hN]; exact Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hA0 hB0)
    have hZ := zetaPart_ge (m := m) (L := L) (y := y) hm hJK
    have hT := hC (wL L) (wL_nonneg L) (wL_le_one L) N hN1
    rw [← hN] at hZ
    have hcop := coprime_Apow_Bprod L J y
    have hHN : HA (wL L) N = HA (wL L) (Apow L J) * HA (wL L) (Bprod L y) := by
      rw [hN]; exact (isMultiplicative_HA _).map_mul_of_coprime hcop
    have hhN : hA (wL L) N = hA (wL L) (Apow L J) * hA (wL L) (Bprod L y) := by
      rw [hN]; exact (isMultiplicative_hA _).map_mul_of_coprime hcop
    have hlogN : Real.log N ≤ Real.log (Apow L J) + y * Real.log 4 := by
      rw [hN, Nat.cast_mul, Real.log_mul (by exact_mod_cast hA0) (by exact_mod_cast hB0)]
      linarith [log_Bprod_le L y]
    have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
    have hlogA0 : 0 ≤ Real.log (Apow L J) :=
      Real.log_nonneg (by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hA0)
    have hHA : hA (wL L) (Apow L J) ≤ HA (wL L) (Apow L J) := hA_le_HA (wL_nonneg L) hA0
    have hhA1 := one_le_hA (wL L) hA0
    have hHB : HA (wL L) (Bprod L y) = 2 ^ (bigPrimes L y).card *
        ∏ p ∈ bigPrimes L y, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) / 2) := by
      rw [HA_Bprod, ← Finset.prod_const, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun p hp => ?_
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (prime_of_mem_bigPrimes hp).pos
      rw [Real.rpow_neg hp0.le, ← Real.sqrt_eq_rpow, one_div]; ring
    have hhB := hA_Bprod L y
    obtain ⟨Pr, hPr⟩ : ∃ Pr, Pr = ∏ p ∈ bigPrimes L y, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) / 2) :=
      ⟨_, rfl⟩
    rw [← hPr] at hHB ⊢
    have hPr0 : 0 ≤ Pr := hPr ▸ Finset.prod_nonneg fun p _ => by positivity
    -- `Z ≥ H(N) M(1)/2`
    have herr : mu m / 2 ≤ mu m -
        ∑' j, (if L ≤ j ∨ 2 ^ (J + 1) ≤ j then |m j| / j else 0) -
        (HA (wL L) (Apow L J) - HA (wL L) (Apow L (J - K₁))) * ∑' j : ℕ, |m j| / j -
        ∑' j, (if K₁ < j then |m j| / j else 0) -
        ∑' j, (if L ≤ j then |m j| / Real.sqrt j else 0) := by
      rw [← hT₀]; linarith
    have hZ2 : HA (wL L) N * (mu m / 2) ≤
        ∑ k ∈ N.divisors, m k * gA (wL L) k * HA (wL L) (N / k) :=
      (mul_le_mul_of_nonneg_left herr (HA_nonneg (wL_nonneg L) _)).trans hZ
    obtain ⟨R, hR⟩ : ∃ R, R = (1 + 2 * |β|) * Real.log N + C₀ + 2 * |m 1| +
        2 * ∑' n : ℕ, |v n| / Real.sqrt n := ⟨_, rfl⟩
    rw [← hR] at hT
    -- `M(1) H(N) ≤ R h(N)`
    have h1 : mu m * HA (wL L) N ≤ R * hA (wL L) N := by linarith
    rw [hHN, hhN, hHB, hhB] at h1
    have h2pos : (0 : ℝ) < 2 ^ (bigPrimes L y).card := by positivity
    have hR0 : mu m * Pr * hA (wL L) (Apow L J) ≤ R * hA (wL L) (Apow L J) := by
      have h3 : mu m * Pr * hA (wL L) (Apow L J) * 2 ^ (bigPrimes L y).card ≤
          mu m * (HA (wL L) (Apow L J) * (2 ^ (bigPrimes L y).card * Pr)) := by
        have := mul_le_mul_of_nonneg_left hHA (mul_nonneg (mul_nonneg hμ.le hPr0) h2pos.le)
        nlinarith
      have h4 := h3.trans h1
      have h5 : R * (hA (wL L) (Apow L J) * 2 ^ (bigPrimes L y).card) =
          R * hA (wL L) (Apow L J) * 2 ^ (bigPrimes L y).card := by ring
      rw [h5] at h4
      exact le_of_mul_le_mul_right h4 h2pos
    have hR1 : mu m * Pr ≤ R := le_of_mul_le_mul_right hR0 (by linarith)
    rw [hR] at hR1
    have : (1 + 2 * |β|) * Real.log N ≤ (1 + 2 * |β|) * (Real.log (Apow L J) + y * Real.log 4) :=
      mul_le_mul_of_nonneg_left hlogN (by positivity)
    linarith
  -- growth
  obtain ⟨KL, hKL⟩ : ∃ KL, KL = ∏ p ∈ L.primesBelow, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) / 2) := ⟨_, rfl⟩
  have hKL0 : 0 < KL := hKL ▸ Finset.prod_pos fun p _ => by positivity
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = 1 + 2 * |β| := ⟨_, rfl⟩
  have hb0 : 0 < b := by rw [hb]; positivity
  obtain ⟨Cst, hCst⟩ : ∃ Cst : ℝ, Cst = Real.log (Apow L J) + (C₀ + 2 * |m 1| +
      2 * ∑' n : ℕ, |v n| / Real.sqrt n) / b := ⟨_, rfl⟩
  have hc : 0 < mu m / (2 * KL * b) := by positivity
  have hev2 := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually
    (PrimorialResonance.eventually_linear_lt_exp (C := Cst) (by norm_num : (1 / 2 : ℝ) < 1) hc)
  obtain ⟨y, hy, hy3⟩ := (hev2.and (eventually_ge_atTop 3)).exists
  have hprod : Real.exp (PrimorialResonance.primeRpowLower (1 / 2) y) ≤
      ∏ p ∈ y.primesLE, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) / 2) :=
    (Real.exp_le_exp.mpr (PrimorialResonance.primeRpowLower_le_sum (by norm_num) hy3)).trans
      (PrimorialResonance.exp_sum_le_prod_one_add (by norm_num) y)
  have hbig := prod_bigPrimes_ge L y
  rw [← hKL] at hbig
  have hk := key y
  have hE : Real.exp (PrimorialResonance.primeRpowLower (1 / 2) y) / KL ≤
      ∏ p ∈ bigPrimes L y, (1 + (p : ℝ) ^ (-(1 / 2 : ℝ)) / 2) :=
    (div_le_div_of_nonneg_right hprod hKL0.le).trans hbig
  have hE2 : mu m * (Real.exp (PrimorialResonance.primeRpowLower (1 / 2) y) / KL) ≤
      (1 + 2 * |β|) * (Real.log (Apow L J) + y * Real.log 4) + C₀ + 2 * |m 1| +
        2 * ∑' n : ℕ, |v n| / Real.sqrt n :=
    (mul_le_mul_of_nonneg_left hE hμ.le).trans hk
  -- `b (y log 4 + Cst) < (M(1)/KL)(exp − 1)`
  have hlin : b * ((y : ℝ) * Real.log 4 + Cst) <
      mu m / KL * (Real.exp (PrimorialResonance.primeRpowLower (1 / 2) y) - 1) := by
    have := mul_lt_mul_of_pos_left hy hb0
    have e : b * (2 * (mu m / (2 * KL * b)) *
        (Real.exp (PrimorialResonance.primeRpowLower (1 / 2) y) - 1)) =
        mu m / KL * (Real.exp (PrimorialResonance.primeRpowLower (1 / 2) y) - 1) := by
      field_simp
    linarith
  have e2 : b * ((y : ℝ) * Real.log 4 + Cst) = (1 + 2 * |β|) * (Real.log (Apow L J) +
      y * Real.log 4) + C₀ + 2 * |m 1| + 2 * ∑' n : ℕ, |v n| / Real.sqrt n := by
    rw [hCst, hb]; field_simp; ring
  have e3 : mu m / KL * (Real.exp (PrimorialResonance.primeRpowLower (1 / 2) y) - 1) ≤
      mu m * (Real.exp (PrimorialResonance.primeRpowLower (1 / 2) y) / KL) := by
    have : mu m / KL * (Real.exp (PrimorialResonance.primeRpowLower (1 / 2) y) - 1) =
        mu m * (Real.exp (PrimorialResonance.primeRpowLower (1 / 2) y) / KL) - mu m / KL := by
      field_simp
    have : 0 ≤ mu m / KL := by positivity
    linarith
  linarith

/-! ## The classification -/

/-- **ζ-multiplicative pole carriers.** If `βΛ + (1 ⋆ m) + v` is full-cone Weil-positive, with
`Σ |m(n)| n^{−½} < ∞`, `Σ |v(n)| n^{−½} < ∞` and `v(0) = v(1) = 0`, then it equals `Λ` on
`n ≥ 2`. -/
theorem eq_vonMangoldt_of_weilPositiveFull_carrier
    (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2)) (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (carrierSystem β m v)) {n : ℕ} (hn : 2 ≤ n) :
    carrierSystem β m v n = ArithmeticFunction.vonMangoldt n :=
  eq_vonMangoldt_of_mu_eq_zero hm hv hW (le_antisymm (mu_nonpos hm hv hW) (mu_nonneg hm hv hW)) hn

/-- Consequently such a system exists only if the Riemann hypothesis holds. -/
theorem riemannHypothesis_of_weilPositiveFull_carrier
    (hm : LSeriesSummable (fun n => (m n : ℂ)) (1 / 2)) (hv : BoundaryRegular v)
    (hW : WeilPositiveFull (carrierSystem β m v)) : RiemannHypothesis :=
  riemannHypothesis_of_weilPositiveFull_of_ge hW fun _ hn =>
    (eq_vonMangoldt_of_weilPositiveFull_carrier hm hv hW hn).ge

end RHTower.WeilZetaCarrier
