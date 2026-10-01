import GaloisForLFunctions.RHTower.ZetaNotchRampMainTerm

/-!
# The refined notch for an arbitrary twist polynomial

Let `P` be a finite set of primes, `A` a finite set of exponent vectors `a : P → ℤ` with
`|a_p| ≤ β_p`, `c : (P → ℤ) → ℝ`, and `q(t) = |Σ_{a∈A} c_a e^{i t λ(a)}|²` with
`λ(a) = Σ_p a_p log p`. Put `K₀ = Π_p p^{2β_p}`.

**Theorem** (`exists_norm_weightedMoment_sub_logMain_le_twist`). There is `D` such that for all
`L ≥ 16` and `n ≠ 0`,
`‖M_L^q(log n) − 1_{K₀n ≤ L/4} W(n) (∫ ω log t − ω̂(0) log n)‖ ≤ D · refWeight(2K₀³, K, L, n)`,
with main weight `W(n) = Σ_{a,a'} c_a c_{a'} (h k)^{−½}`. Here `h/k` is the reduced twist
`n Π_p p^{−(a−a')_p}`.

Unlike the Euler-weighted notch, no cancellation is imposed on the Bohr lift. The main weight keeps
every `P`-fibre of `n`, with the Poisson weights `Π_p p^{−|v_p(n) − g_p|/2}`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

namespace RHTower.WeilAbscissa

open RHTower.ZetaNotch RHTower.SmoothNumbers RHTower.WeilFiniteSupport RHTower.WeilLogSummable

variable {P : Finset ℕ}

/-! ## Coordinate bounds for a twist vector -/

/-- The size `K(B) = Π_p p^{B_p}` of a coordinate bound `B`. -/
def coordBound (P : Finset ℕ) (B : P → ℕ) : ℕ := ∏ p : P, (p : ℕ) ^ B p

theorem coordBound_pos (hP : ∀ p ∈ P, p.Prime) (B : P → ℕ) : 0 < coordBound P B :=
  Finset.prod_pos fun p _ => pow_pos (hP p p.2).pos _

theorem one_le_coordBound (hP : ∀ p ∈ P, p.Prime) (B : P → ℕ) : (1 : ℝ) ≤ coordBound P B := by
  exact_mod_cast coordBound_pos hP B

/-- The coordinates of a twist `b = v(n) − g` with `|g_p| ≤ B_p`. -/
theorem twist_coord_bounds {n : ℕ} {g : P → ℤ} {B : P → ℕ} (hg : ∀ p, |g p| ≤ B p) (p : P) :
    (n.factorization p : ℤ) ≤ ((vecOf P n - g) p).natAbs + B p ∧
      (((vecOf P n - g) p).natAbs : ℤ) ≤ n.factorization p + B p ∧
      ((-(vecOf P n - g) p).toNat : ℤ) ≤ B p := by
  have h := abs_le.mp (hg p)
  simp only [vecOf, Pi.sub_apply]
  omega

theorem sqrt_coordBound_eq (P : Finset ℕ) (B : P → ℕ) :
    Real.sqrt (coordBound P B) = ∏ p : P, Real.sqrt (p : ℕ) ^ B p := by
  have hsq : ((coordBound P B : ℕ) : ℝ) = (∏ p : P, Real.sqrt (p : ℕ) ^ B p) ^ 2 := by
    unfold coordBound
    push_cast
    rw [← Finset.prod_pow]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [hsq, Real.sqrt_sq (Finset.prod_nonneg fun p _ => by positivity)]

/-- The Poisson weight of a twist is at most `√K · n_P^{−½}`. -/
theorem weight_twist_le_prod (hP : ∀ p ∈ P, p.Prime) {n : ℕ} {g : P → ℤ} {B : P → ℕ}
    (hg : ∀ p, |g p| ≤ B p) :
    ∏ p : P, primeHalf p ^ ((vecOf P n - g) p).natAbs ≤
      Real.sqrt (coordBound P B) *
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
  rw [hinv, sqrt_coordBound_eq, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun p _ => pow_nonneg (primeHalf_nonneg _) _) fun p _ => ?_
  have hp1 : (1 : ℝ) ≤ (p : ℕ) := by exact_mod_cast (hP p p.2).one_lt.le
  have hsqrt : 0 < Real.sqrt (p : ℕ) := Real.sqrt_pos.mpr (by linarith)
  set s : ℝ := primeHalf p with hs
  have hs0 : 0 < s := by rw [hs, primeHalf]; positivity
  have hs1 : s ≤ 1 := inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr hp1)
  have hsq : Real.sqrt (p : ℕ) * s = 1 := mul_inv_cancel₀ hsqrt.ne'
  set m := ((vecOf P n - g) p).natAbs with hm
  set e := B p with he
  set k := n.factorization p with hk
  have hkm : k ≤ m + e := by
    have := (twist_coord_bounds (n := n) hg p).1
    omega
  calc s ^ m = (Real.sqrt (p : ℕ) * s) ^ e * s ^ m := by rw [hsq, one_pow, one_mul]
    _ = Real.sqrt (p : ℕ) ^ e * s ^ (m + e) := by rw [mul_pow, pow_add]; ring
    _ ≤ Real.sqrt (p : ℕ) ^ e * s ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hs0.le hs1 hkm) (by positivity)

/-- `log N(b) ≤ log n_P + log K` for a twist. -/
theorem log_twist_norm_le_prod (hP : ∀ p ∈ P, p.Prime) {n : ℕ} {g : P → ℤ} {B : P → ℕ}
    (hg : ∀ p, |g p| ≤ B p) :
    Real.log ((vecNum (vecOf P n - g) : ℝ) * vecDen (vecOf P n - g)) ≤
      Real.log ((∏ p : P, (p : ℕ) ^ n.factorization p : ℕ) : ℝ) + Real.log (coordBound P B) := by
  have hp0 : ∀ p : P, ((p : ℕ) : ℝ) ≠ 0 := fun p => by exact_mod_cast (hP p p.2).ne_zero
  have hlogp : ∀ p : P, 0 ≤ Real.log ((p : ℕ) : ℝ) := fun p =>
    Real.log_nonneg (by exact_mod_cast (hP p p.2).one_lt.le)
  have e1 : ((vecNum (vecOf P n - g) : ℝ) * vecDen (vecOf P n - g)) =
      ∏ p : P, ((p : ℕ) : ℝ) ^ ((vecOf P n - g) p).natAbs := by
    rw [← Nat.cast_mul, vecNum_mul_vecDen_eq]
    push_cast
    rfl
  have e2 : ((∏ p : P, (p : ℕ) ^ n.factorization p : ℕ) : ℝ) =
      ∏ p : P, ((p : ℕ) : ℝ) ^ n.factorization p := by
    push_cast
    rfl
  have e3 : ((coordBound P B : ℕ) : ℝ) = ∏ p : P, ((p : ℕ) : ℝ) ^ B p := by
    unfold coordBound
    push_cast
    rfl
  rw [e1, e2, e3, Real.log_prod (fun p _ => pow_ne_zero _ (hp0 p)),
    Real.log_prod (fun p _ => pow_ne_zero _ (hp0 p)),
    Real.log_prod (fun p _ => pow_ne_zero _ (hp0 p)), ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun p _ => ?_
  rw [Real.log_pow, Real.log_pow, Real.log_pow, ← add_mul]
  refine mul_le_mul_of_nonneg_right ?_ (hlogp p)
  have := (twist_coord_bounds (n := n) hg p).2.1
  exact_mod_cast (by omega : ((vecOf P n - g) p).natAbs ≤ n.factorization p + B p)

/-- The reduced denominator of a twist is at most `K`. -/
theorem vecDen_twist_le (hP : ∀ p ∈ P, p.Prime) {n : ℕ} {g : P → ℤ} {B : P → ℕ}
    (hg : ∀ p, |g p| ≤ B p) : vecDen (vecOf P n - g) ≤ coordBound P B := by
  unfold vecDen coordBound
  refine Finset.prod_le_prod' fun p _ => Nat.pow_le_pow_right (hP p p.2).pos ?_
  have := (twist_coord_bounds (n := n) hg p).2.2
  omega

/-! ## The norm of a twist -/

/-- The norm `hk` of the twist of `n` by the exponent vector `g`. -/
def twistNorm (P : Finset ℕ) (n : ℕ) (g : P → ℤ) : ℝ :=
  ((vecNum (vecOf P n - g) * roughPart P n : ℕ) : ℝ) * vecDen (vecOf P n - g)

theorem twistNorm_pos (hP : ∀ p ∈ P, p.Prime) {n : ℕ} (hn : n ≠ 0) (g : P → ℤ) :
    0 < twistNorm P n g := by
  unfold twistNorm
  have := vecNum_pos hP (vecOf P n - g)
  have := vecDen_pos hP (vecOf P n - g)
  have := roughPart_pos (P := P) hn
  positivity

/-- `(hk)^{−½} ≤ √K n^{−½}`. -/
theorem inv_sqrt_twistNorm_le (hP : ∀ p ∈ P, p.Prime) {n : ℕ} (hn : n ≠ 0) {g : P → ℤ}
    {B : P → ℕ} (hg : ∀ p, |g p| ≤ B p) :
    (Real.sqrt (twistNorm P n g))⁻¹ ≤ Real.sqrt (coordBound P B) * (Real.sqrt n)⁻¹ := by
  unfold twistNorm
  set b := vecOf P n - g with hb
  set r := roughPart P n with hr
  have hr0 : (0 : ℝ) < r := by exact_mod_cast roughPart_pos hn
  have hw := weight_twist_le_prod hP hg (n := n)
  have hsplitN : (((vecNum b * r : ℕ) : ℝ) * vecDen b) = ((vecNum b : ℝ) * vecDen b) * r := by
    push_cast; ring
  have hwN : (Real.sqrt (((vecNum b * r : ℕ) : ℝ) * vecDen b))⁻¹ =
      (∏ p : P, primeHalf p ^ (b p).natAbs) * (Real.sqrt r)⁻¹ := by
    rw [hsplitN, Real.sqrt_mul (by positivity), mul_inv, inv_sqrt_vecNum_mul_vecDen b]
  rw [hwN, ← sqrt_smooth_mul_rough hn, mul_inv, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right hw (by positivity)

/-- `n ≤ K hk`. -/
theorem natCast_le_mul_twistNorm (hP : ∀ p ∈ P, p.Prime) {n : ℕ} (hn : n ≠ 0) {g : P → ℤ}
    {B : P → ℕ} (hg : ∀ p, |g p| ≤ B p) :
    (n : ℝ) ≤ (coordBound P B : ℝ) * twistNorm P n g := by
  have hK1 := one_le_coordBound hP B
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hN0 := twistNorm_pos hP hn g
  have hw := inv_sqrt_twistNorm_le hP hn hg
  have hsq : 0 < Real.sqrt (twistNorm P n g) := Real.sqrt_pos.mpr hN0
  rw [inv_le_comm₀ hsq (by positivity), mul_inv, inv_inv] at hw
  have hsq2 : Real.sqrt n ≤ Real.sqrt (coordBound P B) * Real.sqrt (twistNorm P n g) := by
    have := mul_le_mul_of_nonneg_left hw (Real.sqrt_nonneg (coordBound P B : ℝ))
    rwa [← mul_assoc, mul_inv_cancel₀ (by positivity), one_mul] at this
  rw [← Real.sqrt_mul (by linarith)] at hsq2
  exact (Real.sqrt_le_sqrt_iff (by positivity)).mp hsq2

/-- `hk ≤ K n`. -/
theorem twistNorm_le (hP : ∀ p ∈ P, p.Prime) {n : ℕ} (hn : n ≠ 0) {g : P → ℤ}
    {B : P → ℕ} (hg : ∀ p, |g p| ≤ B p) :
    twistNorm P n g ≤ (coordBound P B : ℝ) * n := by
  unfold twistNorm
  set b := vecOf P n - g with hb
  have hs : (0 : ℝ) < smoothPart P n := by exact_mod_cast smoothPart_pos hP n
  have hK : (0 : ℝ) < coordBound P B := by exact_mod_cast coordBound_pos hP B
  have hlog := log_twist_norm_le_prod hP hg (n := n)
  have hsm : ((∏ p : P, (p : ℕ) ^ n.factorization p : ℕ) : ℝ) = smoothPart P n := rfl
  rw [hsm, ← Real.log_mul hs.ne' hK.ne'] at hlog
  have hnum : (0 : ℝ) < vecNum b := by exact_mod_cast vecNum_pos hP b
  have hden : (0 : ℝ) < vecDen b := by exact_mod_cast vecDen_pos hP b
  have h1 : (vecNum b : ℝ) * vecDen b ≤ smoothPart P n * coordBound P B :=
    (Real.log_le_log_iff (by positivity) (by positivity)).mp hlog
  have hr : (0 : ℝ) < roughPart P n := by exact_mod_cast roughPart_pos hn
  have hn' : (n : ℝ) = smoothPart P n * roughPart P n := by
    rw [← Nat.cast_mul, smoothPart_mul_roughPart n hn]
  rw [hn']
  push_cast
  nlinarith

/-- `|log(hk) − log n| ≤ log K`. -/
theorem abs_log_twistNorm_sub_le (hP : ∀ p ∈ P, p.Prime) {n : ℕ} (hn : n ≠ 0) {g : P → ℤ}
    {B : P → ℕ} (hg : ∀ p, |g p| ≤ B p) :
    |Real.log (twistNorm P n g) - Real.log n| ≤ Real.log (coordBound P B) := by
  have hN0 := twistNorm_pos hP hn g
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hK : (0 : ℝ) < coordBound P B := by exact_mod_cast coordBound_pos hP B
  have h1 := natCast_le_mul_twistNorm hP hn hg
  have h2 := twistNorm_le hP hn hg
  rw [abs_le]
  constructor
  · have := Real.log_le_log hn0 h1
    rw [Real.log_mul hK.ne' hN0.ne'] at this
    linarith
  · have := Real.log_le_log hN0 h2
    rw [Real.log_mul hK.ne' hn0.ne'] at this
    linarith

/-- `√(2k/h) ≤ 2K² n^{−½}`. -/
theorem sqrt_two_mul_div_twist_le (hP : ∀ p ∈ P, p.Prime) {n : ℕ} (hn : n ≠ 0) {g : P → ℤ}
    {B : P → ℕ} (hg : ∀ p, |g p| ≤ B p) :
    Real.sqrt (2 * (vecDen (vecOf P n - g) : ℝ) /
        ((vecNum (vecOf P n - g) * roughPart P n : ℕ) : ℝ)) ≤
      2 * (coordBound P B : ℝ) ^ 2 * (Real.sqrt n)⁻¹ := by
  set h : ℕ := vecNum (vecOf P n - g) * roughPart P n with hh
  set k : ℕ := vecDen (vecOf P n - g) with hk
  set K₀ : ℝ := (coordBound P B : ℝ) with hK₀
  have hK1 : 1 ≤ K₀ := one_le_coordBound hP B
  have hkK : (k : ℝ) ≤ K₀ := by
    have := vecDen_twist_le hP hg (n := n)
    show ((vecDen (vecOf P n - g) : ℕ) : ℝ) ≤ (coordBound P B : ℝ)
    exact_mod_cast this
  have hh0 : (0 : ℝ) < h := by exact_mod_cast Nat.mul_pos (vecNum_pos hP _) (roughPart_pos hn)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast vecDen_pos hP _
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hhk : (n : ℝ) ≤ K₀ * ((h : ℝ) * k) := natCast_le_mul_twistNorm hP hn hg
  have hkh : 2 * (k : ℝ) / h ≤ 2 * K₀ ^ 3 / n := by
    rw [div_le_div_iff₀ hh0 hn0]
    have hk2 : (k : ℝ) * k ≤ K₀ * K₀ := by nlinarith
    nlinarith
  calc Real.sqrt (2 * k / h) ≤ Real.sqrt (2 * K₀ ^ 3 / n) := Real.sqrt_le_sqrt hkh
    _ = Real.sqrt (2 * K₀ ^ 3) * (Real.sqrt n)⁻¹ := by
        rw [Real.sqrt_div' _ hn0.le, div_eq_mul_inv]
    _ ≤ 2 * K₀ ^ 2 * (Real.sqrt n)⁻¹ := by
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        rw [Real.sqrt_le_left (by positivity)]
        nlinarith [pow_le_pow_right₀ hK1 (by norm_num : 3 ≤ 4)]

/-- The near-line small dual pairs of a twist cost at most `96 K √L log L`, and they exist only
for `n ≤ 2K³L`. -/
theorem small_twist_le_ind (hP : ∀ p ∈ P, p.Prime) {L : ℝ} (hL : 16 ≤ L) {n : ℕ} (hn : n ≠ 0)
    {g : P → ℤ} {B : P → ℕ} (hg : ∀ p, |g p| ≤ B p) :
    L ^ (-(1 / 4 : ℝ)) * ∑' Q, smallWeight L L⁻¹
        (vecNum (vecOf P n - g) * roughPart P n) (vecDen (vecOf P n - g)) Q ≤
      96 * (coordBound P B : ℝ) * (Real.sqrt L * Real.log L) *
        (if (n : ℝ) ≤ 2 * (coordBound P B : ℝ) ^ 3 * L then 1 else 0) := by
  set h : ℕ := vecNum (vecOf P n - g) * roughPart P n with hh
  set k : ℕ := vecDen (vecOf P n - g) with hk
  set K₀ : ℝ := (coordBound P B : ℝ) with hK₀
  have hL0 : 0 < L := by linarith
  have hK1 : 1 ≤ K₀ := one_le_coordBound hP B
  have hh1 : 1 ≤ h := Nat.mul_pos (vecNum_pos hP _) (roughPart_pos hn)
  have hk1 : 1 ≤ k := vecDen_pos hP _
  have hkK : (k : ℝ) ≤ K₀ := by
    have := vecDen_twist_le hP hg (n := n)
    show ((vecDen (vecOf P n - g) : ℕ) : ℝ) ≤ (coordBound P B : ℝ)
    exact_mod_cast this
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk1
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hδ : 0 < L⁻¹ := inv_pos.mpr hL0
  have hR0 : 0 ≤ 96 * K₀ * (Real.sqrt L * Real.log L) *
      (if (n : ℝ) ≤ 2 * K₀ ^ 3 * L then 1 else 0) := by
    have : (0 : ℝ) ≤ (if (n : ℝ) ≤ 2 * K₀ ^ 3 * L then 1 else 0) := by split_ifs <;> norm_num
    positivity
  rcases le_or_gt (2 * k * L) (h : ℝ) with hbig | hsmall
  · have hz : ∑' Q, smallWeight L L⁻¹ h k Q = 0 := by
      rw [show (fun Q => smallWeight L L⁻¹ h k Q) = fun _ => (0 : ℝ) from
        funext fun Q => smallWeight_eq_zero_of_le hk1 hL0 hbig Q, tsum_zero]
    rw [hz, mul_zero]
    exact hR0
  · have hJ := shell_count_le_log hδ (by rw [one_div]) (by linarith : (1 : ℝ) < L)
    have hsm := tsum_smallWeight_le (h := h) (k := k) hh1 hk1 hL0 hδ
    set J : ℝ := (Nat.find (exists_shell_count hδ) : ℝ) with hJdef
    have hlog2 : (1 : ℝ) / 2 < Real.log 2 := by
      have := Real.log_two_gt_d9; linarith
    have hJ2 : J ≤ 2 * Real.log L := by
      refine hJ.trans ?_
      rw [div_le_iff₀ (by linarith)]
      nlinarith
    have hnX : (n : ℝ) ≤ 2 * K₀ ^ 3 * L := by
      have h1 : (n : ℝ) ≤ K₀ * ((h : ℝ) * k) := natCast_le_mul_twistNorm hP hn hg
      have h2 : (h : ℝ) * k ≤ 2 * K₀ ^ 2 * L := by
        have hk2 : (k : ℝ) * k ≤ K₀ * K₀ := mul_le_mul hkK hkK hk0.le (by linarith)
        calc (h : ℝ) * k ≤ 2 * k * L * k := mul_le_mul_of_nonneg_right hsmall.le hk0.le
          _ = 2 * L * ((k : ℝ) * k) := by ring
          _ ≤ 2 * L * (K₀ * K₀) := mul_le_mul_of_nonneg_left hk2 (by positivity)
          _ = 2 * K₀ ^ 2 * L := by ring
      calc (n : ℝ) ≤ K₀ * ((h : ℝ) * k) := h1
        _ ≤ K₀ * (2 * K₀ ^ 2 * L) := mul_le_mul_of_nonneg_left h2 (by linarith)
        _ = 2 * K₀ ^ 3 * L := by ring
    rw [if_pos hnX, mul_one]
    have hpow : L ^ (-(1 / 4 : ℝ)) * L ^ (3 / 4 : ℝ) = Real.sqrt L := by
      rw [← Real.rpow_add hL0, Real.sqrt_eq_rpow]; norm_num
    calc L ^ (-(1 / 4 : ℝ)) * ∑' Q, smallWeight L L⁻¹ h k Q
        ≤ L ^ (-(1 / 4 : ℝ)) * (48 * k * L ^ (3 / 4 : ℝ) * J) :=
          mul_le_mul_of_nonneg_left hsm (by positivity)
      _ = 48 * k * J * (L ^ (-(1 / 4 : ℝ)) * L ^ (3 / 4 : ℝ)) := by ring
      _ = 48 * k * J * Real.sqrt L := by rw [hpow]
      _ ≤ 48 * K₀ * (2 * Real.log L) * Real.sqrt L := by
          have hJ0 : 0 ≤ J := Nat.cast_nonneg _
          gcongr
      _ = 96 * K₀ * (Real.sqrt L * Real.log L) := by ring

/-- The envelope of a twist in refined form. -/
theorem twist_envelope_le (hP : ∀ p ∈ P, p.Prime) {C L : ℝ} (hC : 0 ≤ C) (hL : 16 ≤ L)
    {K : ℕ} (hK : 2 ≤ K) {n : ℕ} (hn : n ≠ 0) {g : P → ℤ} {B : P → ℕ} (hg : ∀ p, |g p| ≤ B p) :
    (Real.sqrt (((vecNum (vecOf P n - g) * roughPart P n : ℕ) : ℝ) *
        (vecDen (vecOf P n - g) : ℕ)))⁻¹ * (2 * L * C) +
      C * (L * nearMass L (vecNum (vecOf P n - g) * roughPart P n) (vecDen (vecOf P n - g)) L⁻¹ +
        L * ∑' Q, farWeight L L⁻¹ K (vecNum (vecOf P n - g) * roughPart P n)
          (vecDen (vecOf P n - g)) Q +
        L ^ (-(1 / 4 : ℝ)) * ∑' Q, smallWeight L L⁻¹ (vecNum (vecOf P n - g) * roughPart P n)
          (vecDen (vecOf P n - g)) Q +
        L ^ (5 / 2 : ℝ) * dualTailFactor L K + L ^ 2 * Real.exp (-(L ^ 2) / 32)) ≤
      (2 * C * Real.sqrt (coordBound P B) +
        C * (160 * (coordBound P B : ℝ) ^ 3 + 96 * coordBound P B + pairZeta + 1)) *
        refWeight (2 * (coordBound P B : ℝ) ^ 3) K L n := by
  set h : ℕ := vecNum (vecOf P n - g) * roughPart P n with hh
  set k : ℕ := vecDen (vecOf P n - g) with hk
  set K₀ : ℝ := (coordBound P B : ℝ) with hK₀
  have hL0 : 0 < L := by linarith
  have hK1 : 1 ≤ K₀ := one_le_coordBound hP B
  have hh1 : 1 ≤ h := Nat.mul_pos (vecNum_pos hP _) (roughPart_pos hn)
  have hk1 : 1 ≤ k := vecDen_pos hP _
  have hkK : (k : ℝ) ≤ K₀ := by
    have := vecDen_twist_le hP hg (n := n)
    show ((vecDen (vecOf P n - g) : ℕ) : ℝ) ≤ (coordBound P B : ℝ)
    exact_mod_cast this
  set w₁ : ℝ := L * (Real.sqrt n)⁻¹ with hw₁
  set ind : ℝ := (if (n : ℝ) ≤ 2 * K₀ ^ 3 * L then 1 else 0) with hind
  set w₂ : ℝ := Real.sqrt L * Real.log L * ind with hw₂
  set T : ℝ := L ^ (5 / 2 : ℝ) * dualTailFactor L K with hT
  set Z : ℝ := L ^ 2 * Real.exp (-(L ^ 2) / 32) with hZ
  have hind0 : 0 ≤ ind := by rw [hind]; split_ifs <;> norm_num
  have hlogL : 0 ≤ Real.log L := Real.log_nonneg (by linarith)
  have hw₁0 : 0 ≤ w₁ := by positivity
  have hw₂0 : 0 ≤ w₂ := by positivity
  have hT0 : 0 ≤ T := mul_nonneg (by positivity) (dualTailFactor_nonneg hL0.le K)
  have hZ0 : 0 ≤ Z := by positivity
  have hsq := sqrt_two_mul_div_twist_le hP hn hg
  have hnear := near_crit_le hL hh1 hk1 hkK hsq
  have hfar := far_crit_le hL hK hh1 hk1 hkK hsq
  have hsmall := small_twist_le_ind hP hL hn hg
  have hdiag : (Real.sqrt ((h : ℝ) * (k : ℕ)))⁻¹ * (2 * L * C) ≤ 2 * C * Real.sqrt K₀ * w₁ := by
    have := inv_sqrt_twistNorm_le hP hn hg
    unfold twistNorm at this
    calc (Real.sqrt ((h : ℝ) * (k : ℕ)))⁻¹ * (2 * L * C)
        ≤ (Real.sqrt K₀ * (Real.sqrt n)⁻¹) * (2 * L * C) :=
          mul_le_mul_of_nonneg_right this (by positivity)
      _ = 2 * C * Real.sqrt K₀ * w₁ := by rw [hw₁]; ring
  have hLs : L * (2 * K₀ ^ 2 * (Real.sqrt n)⁻¹) = 2 * K₀ ^ 2 * w₁ := by rw [hw₁]; ring
  rw [hLs] at hnear hfar
  have hK30 : 0 ≤ K₀ ^ 3 := by positivity
  have hpz := pairZeta_nonneg
  have hnear' : L * nearMass L h k L⁻¹ ≤ 32 * K₀ ^ 3 * w₁ := by nlinarith
  have hfar' : L * ∑' Q, farWeight L L⁻¹ K h k Q ≤ 128 * K₀ ^ 3 * w₁ + pairZeta * T := by
    nlinarith
  have hsmall' : L ^ (-(1 / 4 : ℝ)) * ∑' Q, smallWeight L L⁻¹ h k Q ≤ 96 * K₀ * w₂ := by
    rw [hw₂]; linarith
  have hrw : refWeight (2 * K₀ ^ 3) K L n = w₁ + w₂ + T + Z := by
    rw [refWeight, hw₁, hw₂, hind, hT, hZ]
  rw [hrw]
  have hsum : L * nearMass L h k L⁻¹ + L * ∑' Q, farWeight L L⁻¹ K h k Q +
      L ^ (-(1 / 4 : ℝ)) * ∑' Q, smallWeight L L⁻¹ h k Q + T + Z ≤
      (160 * K₀ ^ 3 + 96 * K₀ + pairZeta + 1) * (w₁ + w₂ + T + Z) := by
    have h0 : 0 ≤ (160 * K₀ ^ 3 + 96 * K₀ + pairZeta + 1) * (w₁ + w₂ + T + Z) -
        (160 * K₀ ^ 3 * w₁ + 96 * K₀ * w₂ + pairZeta * T + T + Z) := by
      have e : (160 * K₀ ^ 3 + 96 * K₀ + pairZeta + 1) * (w₁ + w₂ + T + Z) -
          (160 * K₀ ^ 3 * w₁ + 96 * K₀ * w₂ + pairZeta * T + T + Z) =
          160 * K₀ ^ 3 * (w₂ + T + Z) + 96 * K₀ * (w₁ + T + Z) + pairZeta * (w₁ + w₂ + Z) +
            (w₁ + w₂) := by ring
      rw [e]; positivity
    linarith
  have hsq0 : 0 ≤ Real.sqrt K₀ := Real.sqrt_nonneg _
  calc (Real.sqrt ((h : ℝ) * (k : ℕ)))⁻¹ * (2 * L * C) +
        C * (L * nearMass L h k L⁻¹ + L * ∑' Q, farWeight L L⁻¹ K h k Q +
          L ^ (-(1 / 4 : ℝ)) * ∑' Q, smallWeight L L⁻¹ h k Q + T + Z)
      ≤ 2 * C * Real.sqrt K₀ * w₁ + C * ((160 * K₀ ^ 3 + 96 * K₀ + pairZeta + 1) *
          (w₁ + w₂ + T + Z)) := add_le_add hdiag (mul_le_mul_of_nonneg_left hsum hC)
    _ ≤ (2 * C * Real.sqrt K₀ + C * (160 * K₀ ^ 3 + 96 * K₀ + pairZeta + 1)) *
          (w₁ + w₂ + T + Z) := by
        have : 0 ≤ 2 * C * Real.sqrt K₀ * (w₂ + T + Z) := by positivity
        nlinarith

/-! ## The twist polynomial -/

/-- `S(t) = Σ_{a∈A} c_a e^{i t λ(a)}`. -/
def twistExpSum (A : Finset (P → ℤ)) (c : (P → ℤ) → ℝ) (t : ℝ) : ℂ :=
  ∑ a ∈ A, (c a : ℂ) * Complex.exp (((t * vecFreq a : ℝ) : ℂ) * I)

/-- The twist polynomial `q(t) = |S(t)|²`. -/
def twistNotchWeight (A : Finset (P → ℤ)) (c : (P → ℤ) → ℝ) (t : ℝ) : ℝ :=
  Complex.normSq (twistExpSum A c t)

/-- The entire extension `Q(z) = Σ_{a,a'} c_a c_{a'} e^{i z λ(a − a')}`. -/
def twistNotchWeightC (A : Finset (P → ℤ)) (c : (P → ℤ) → ℝ) (z : ℂ) : ℂ :=
  ∑ a ∈ A, ∑ a' ∈ A, ((c a * c a' : ℝ) : ℂ) * Complex.exp (z * (vecFreq (a - a') : ℂ) * I)

variable {A : Finset (P → ℤ)} {c : (P → ℤ) → ℝ}

theorem twistNotchWeight_nonneg (A : Finset (P → ℤ)) (c : (P → ℤ) → ℝ) (t : ℝ) :
    0 ≤ twistNotchWeight A c t := Complex.normSq_nonneg _

theorem twistNotchWeightC_ofReal (A : Finset (P → ℤ)) (c : (P → ℤ) → ℝ) (t : ℝ) :
    twistNotchWeightC A c t = twistNotchWeight A c t := by
  unfold twistNotchWeightC twistNotchWeight
  rw [← Complex.mul_conj, twistExpSum, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun a' _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj, map_mul, Complex.conj_ofReal,
    Complex.conj_I, vecFreq_sub]
  rw [show ((c a : ℂ) * Complex.exp (((t * vecFreq a : ℝ) : ℂ) * I)) *
      ((c a' : ℂ) * Complex.exp (((t * vecFreq a' : ℝ) : ℂ) * -I)) =
      ((c a * c a' : ℝ) : ℂ) * (Complex.exp (((t * vecFreq a : ℝ) : ℂ) * I) *
        Complex.exp (((t * vecFreq a' : ℝ) : ℂ) * -I)) by push_cast; ring, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem differentiable_twistNotchWeightC (A : Finset (P → ℤ)) (c : (P → ℤ) → ℝ) :
    Differentiable ℂ (twistNotchWeightC A c) := by
  unfold twistNotchWeightC
  fun_prop

theorem exists_norm_twistNotchWeightC_le (A : Finset (P → ℤ)) (c : (P → ℤ) → ℝ) :
    ∃ C, 0 ≤ C ∧ ∀ z : ℂ, |z.im| ≤ 1 → ‖twistNotchWeightC A c z‖ ≤ C := by
  refine ⟨∑ a ∈ A, ∑ a' ∈ A, |c a * c a'| * Real.exp |vecFreq (a - a')|,
    Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun a' _ => by positivity, fun z hz => ?_⟩
  unfold twistNotchWeightC
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a' _ => ?_)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (abs_nonneg _)
  have hre : (z * (vecFreq (a - a') : ℂ) * I).re = -(z.im * vecFreq (a - a')) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  have h1 := abs_le.mp hz
  have h2 : |z.im * vecFreq (a - a')| ≤ |vecFreq (a - a')| := by
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) hz
  linarith [neg_abs_le (z.im * vecFreq (a - a'))]

theorem continuous_twistNotchWeight (A : Finset (P → ℤ)) (c : (P → ℤ) → ℝ) :
    Continuous (twistNotchWeight A c) := by
  unfold twistNotchWeight twistExpSum
  exact Complex.continuous_normSq.comp (by fun_prop)

theorem exists_abs_twistNotchWeight_le (A : Finset (P → ℤ)) (c : (P → ℤ) → ℝ) :
    ∃ C, 0 ≤ C ∧ (∀ z : ℂ, |z.im| ≤ 1 → ‖twistNotchWeightC A c z‖ ≤ C) ∧
      ∀ t, |twistNotchWeight A c t| ≤ C := by
  obtain ⟨C, hC0, hC⟩ := exists_norm_twistNotchWeightC_le A c
  refine ⟨C, hC0, hC, fun t => ?_⟩
  have h := hC t (by simp)
  rwa [twistNotchWeightC_ofReal, Complex.norm_real, Real.norm_eq_abs] at h

/-- **The twisted moment expansion.** -/
theorem weightedMoment_twistNotchWeight_eq {L : ℝ} (hL : 0 < L) (A : Finset (P → ℤ))
    (c : (P → ℤ) → ℝ) (y : ℝ) :
    ZetaNotch.weightedMoment L (twistNotchWeight A c) y =
      ∑ a ∈ A, ∑ a' ∈ A, ((c a * c a' : ℝ) : ℂ) *
        ZetaNotch.twistedMoment L (y - vecFreq (a - a')) := by
  classical
  set F : (P → ℤ) → (P → ℤ) → ℝ → ℂ := fun a a' t => ((c a * c a' : ℝ) : ℂ) *
    (notchWindow L t * zetaSq t * Complex.exp (-(((y - vecFreq (a - a') : ℝ) : ℂ) * t) * I))
    with hF
  have hFi : ∀ a a', Integrable (F a a') := fun a a' =>
    (integrable_notchWindow_mul_continuous hL (f := fun t => zetaSq t *
      Complex.exp (-(((y - vecFreq (a - a') : ℝ) : ℂ) * t) * I))
      ((contDiff_zetaSq 0).continuous.mul (by fun_prop))).const_mul _ |>.congr
      (Eventually.of_forall fun t => by simp only [hF]; ring)
  have hpt : ∀ t, notchWindow L t * ((twistNotchWeight A c t : ℝ) : ℂ) * zetaSq t *
      Complex.exp (-(y * t) * I) = ∑ a ∈ A, ∑ a' ∈ A, F a a' t := by
    intro t
    rw [← twistNotchWeightC_ofReal, twistNotchWeightC, Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a' _ => ?_
    simp only [hF]
    have e := exp_mul_exp_twist t (vecFreq (a - a')) y
    rw [show (t : ℂ) * (vecFreq (a - a') : ℂ) * I = ((t * vecFreq (a - a') : ℝ) : ℂ) * I by
      push_cast; ring, ← e]
    ring
  unfold ZetaNotch.weightedMoment
  rw [integral_congr_ae (Eventually.of_forall hpt),
    integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun a' _ => hFi a a')]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [integral_finsetSum _ (fun a' _ => hFi a a')]
  refine Finset.sum_congr rfl fun a' _ => ?_
  simp only [hF]
  rw [integral_const_mul]
  rfl

/-! ## The weighted moment of a twist polynomial -/

/-- The main weight `W(n) = Σ_{a,a'} c_a c_{a'} (hk)^{−½}` of the twist polynomial. -/
def twistMainWeight (P : Finset ℕ) (A : Finset (P → ℤ)) (c : (P → ℤ) → ℝ) (n : ℕ) : ℝ :=
  ∑ a ∈ A, ∑ a' ∈ A, c a * c a' * (Real.sqrt (twistNorm P n (a - a')))⁻¹

/-- **The twist-polynomial moment from truncated twist bounds.** -/
theorem norm_weightedMoment_twist_sub_truncSum_le (hP : ∀ p ∈ P, p.Prime) {L : ℝ}
    (hL : 0 < L) (Env : ℕ → ℕ → ℝ) (hEnv : ∀ h k : ℕ, 0 < h → 0 < k → Nat.Coprime h k →
      ‖ZetaNotch.twistedMoment L (Real.log h - Real.log k) -
          (((Real.sqrt ((h : ℝ) * k))⁻¹ : ℝ) : ℂ) * truncMain L ((h : ℝ) * k)‖ ≤ Env h k)
    (A : Finset (P → ℤ)) (c : (P → ℤ) → ℝ) {n : ℕ} (hn : n ≠ 0) :
    ‖ZetaNotch.weightedMoment L (twistNotchWeight A c) (Real.log n) -
        ∑ a ∈ A, ∑ a' ∈ A, ((c a * c a' : ℝ) : ℂ) *
          (((Real.sqrt (twistNorm P n (a - a')))⁻¹ : ℝ) : ℂ) * truncMain L (twistNorm P n (a - a'))‖ ≤
      ∑ a ∈ A, ∑ a' ∈ A, |c a * c a'| *
        Env (vecNum (vecOf P n - (a - a')) * roughPart P n) (vecDen (vecOf P n - (a - a'))) := by
  classical
  unfold twistNorm
  set r := roughPart P n with hr
  have hr0 : 0 < r := roughPart_pos hn
  have hfreq : ∀ g : P → ℤ, Real.log n - vecFreq g =
      Real.log ((vecNum (vecOf P n - g) * r : ℕ) : ℝ) - Real.log (vecDen (vecOf P n - g)) := by
    intro g
    have hnum : (0 : ℝ) < vecNum (vecOf P n - g) := by exact_mod_cast vecNum_pos hP _
    have hrr : (0 : ℝ) < r := by exact_mod_cast hr0
    rw [Nat.cast_mul, Real.log_mul hnum.ne' hrr.ne', log_eq_smooth_add_rough hP hn,
      ← vecFreq_vecOf_eq_log_smoothPart hP]
    have := vecFreq_eq hP (vecOf P n - g)
    rw [vecFreq_sub] at this
    linarith
  rw [weightedMoment_twistNotchWeight_eq hL]
  simp_rw [hfreq]
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun a' _ => ?_)
  simp only [mul_assoc]
  rw [← mul_sub, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hcop : Nat.Coprime (vecNum (vecOf P n - (a - a')) * r) (vecDen (vecOf P n - (a - a'))) :=
    Nat.Coprime.mul_left (coprime_vecNum_vecDen hP _) (coprime_roughPart_vecDen hP hn _)
  have h := hEnv _ _ (Nat.mul_pos (vecNum_pos hP _) hr0) (vecDen_pos hP _) hcop
  push_cast at h ⊢
  exact mul_le_mul_of_nonneg_left h (abs_nonneg _)

theorem abs_sub_le_two_mul {A : Finset (P → ℤ)} {β : P → ℕ} (hβ : ∀ a ∈ A, ∀ p, |a p| ≤ β p)
    {a a' : P → ℤ} (ha : a ∈ A) (ha' : a' ∈ A) (p : P) : |(a - a') p| ≤ ((2 * β p : ℕ) : ℤ) := by
  have h1 := hβ a ha p
  have h2 := hβ a' ha' p
  rw [Pi.sub_apply]
  push_cast
  calc |a p - a' p| ≤ |a p| + |a' p| := abs_sub _ _
    _ ≤ β p + β p := add_le_add h1 h2
    _ = 2 * β p := by ring

/-- **The twist-polynomial moment with its logarithmic main term.** For `|a_p| ≤ β_p` on `A`,
`K₀ = Π_p p^{2β_p}` and `K ≥ 2`, uniformly in `L ≥ 16` and `n ≠ 0`:
`‖M_L^q(log n) − 1_{K₀n ≤ L/4} W(n) (∫ ω log t − ω̂(0) log n)‖ ≤ D · refWeight(2K₀³, K, L, n)`. -/
theorem exists_norm_weightedMoment_sub_logMain_le_twist (hP : ∀ p ∈ P, p.Prime)
    (A : Finset (P → ℤ)) (c : (P → ℤ) → ℝ) {β : P → ℕ} (hβ : ∀ a ∈ A, ∀ p, |a p| ≤ β p)
    {K : ℕ} (hK : 2 ≤ K) :
    ∃ D, 0 ≤ D ∧ ∀ {L : ℝ}, 16 ≤ L → ∀ {n : ℕ}, n ≠ 0 →
      ‖ZetaNotch.weightedMoment L (twistNotchWeight A c) (Real.log n) -
          (((if (coordBound P (fun p => 2 * β p) : ℝ) * n ≤ L / 4 then
            twistMainWeight P A c n else 0 : ℝ)) : ℂ) *
            (logWindow L - windowHat L 0 * (Real.log n : ℂ))‖ ≤
        D * refWeight (2 * (coordBound P (fun p => 2 * β p) : ℝ) ^ 3) K L n := by
  classical
  obtain ⟨C, hC, htw⟩ := exists_norm_twistedMoment_sub_truncMain_le K
  set Bv : P → ℕ := fun p => 2 * β p with hBv
  have hg : ∀ a ∈ A, ∀ a' ∈ A, ∀ p, |(a - a') p| ≤ Bv p := fun a ha a' ha' p =>
    abs_sub_le_two_mul hβ ha ha' p
  set Bs : ℝ := ∑ a ∈ A, ∑ a' ∈ A, |c a * c a'| with hBs
  have hBs0 : 0 ≤ Bs := Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun a' _ => abs_nonneg _
  set K₀ : ℝ := (coordBound P Bv : ℝ) with hK₀
  have hK1 : 1 ≤ K₀ := one_le_coordBound hP Bv
  set E : ℝ := 2 * C * Real.sqrt K₀ + C * (160 * K₀ ^ 3 + 96 * K₀ + pairZeta + 1) with hE
  have hE0 : 0 ≤ E := by have := pairZeta_nonneg; rw [hE]; positivity
  set G : ℝ := Real.log (25 * K₀ ^ 2) with hG
  have hG0 : 0 ≤ G := Real.log_nonneg (by nlinarith)
  refine ⟨Bs * E + Bs * Real.sqrt K₀ * (2 * G), by positivity, fun {L} hL {n} hn => ?_⟩
  have hL0 : 0 < L := by linarith
  have hn0 : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
  set Env : ℕ → ℕ → ℝ := fun h k => (Real.sqrt ((h : ℝ) * k))⁻¹ * (2 * L * C) +
    C * (L * nearMass L h k L⁻¹ + L * ∑' Q, farWeight L L⁻¹ K h k Q +
      L ^ (-(1 / 4 : ℝ)) * ∑' Q, smallWeight L L⁻¹ h k Q +
      L ^ (5 / 2 : ℝ) * dualTailFactor L K + L ^ 2 * Real.exp (-(L ^ 2) / 32)) with hEnv
  have h1 := norm_weightedMoment_twist_sub_truncSum_le hP hL0 Env
    (fun h k hh hk hcop => htw hL hh hk hcop) A c hn
  have hlogK : Real.log K₀ ≤ G := Real.log_le_log (by linarith) (by nlinarith)
  have h2 := norm_doubleSum_truncMain_sub_le A A (fun a a' => c a * c a')
    (fun a a' => (Real.sqrt (twistNorm P n (a - a')))⁻¹) (fun a a' => twistNorm P n (a - a'))
    (x := Real.log n) (m := twistMainWeight P A c n) (M := Real.sqrt K₀ * (Real.sqrt n)⁻¹)
    (G := G) hL (K₀ * n ≤ L / 4)
    (fun a a' => inv_nonneg.mpr (Real.sqrt_nonneg _))
    (fun a ha a' ha' => inv_sqrt_twistNorm_le hP hn (hg a ha a' ha'))
    (fun a a' => twistNorm_pos hP hn _) rfl
    (fun hsmall a ha a' ha' => ⟨(twistNorm_le hP hn (hg a ha a' ha')).trans hsmall,
      (abs_log_twistNorm_sub_le hP hn (hg a ha a' ha')).trans hlogK⟩)
    (fun hbig a ha a' ha' => by
      push Not at hbig
      have hN0 := twistNorm_pos hP hn (a - a')
      have hlow : (n : ℝ) / K₀ ≤ twistNorm P n (a - a') := by
        rw [div_le_iff₀ (by linarith)]
        have := natCast_le_mul_twistNorm hP hn (hg a ha a' ha')
        linarith
      have hNL : L / (4 * K₀ ^ 2) < twistNorm P n (a - a') := by
        refine lt_of_lt_of_le ?_ hlow
        rw [div_lt_div_iff₀ (by positivity) (by linarith)]
        nlinarith
      have harg : 25 * L / (4 * twistNorm P n (a - a')) ≤ 25 * K₀ ^ 2 := by
        rw [div_le_iff₀ (by linarith)]
        rw [div_lt_iff₀ (by positivity)] at hNL
        nlinarith
      have h3 := halfLogPos_mono (by positivity) harg
      rw [halfLogPos_of_one_le (show (1 : ℝ) ≤ 25 * K₀ ^ 2 by nlinarith)] at h3
      exact h3)
  have hRW := refWeight_nonneg (2 * K₀ ^ 3) K (by linarith : (1 : ℝ) ≤ L) n
  have hmode : ∑ a ∈ A, ∑ a' ∈ A, |c a * c a'| *
      Env (vecNum (vecOf P n - (a - a')) * roughPart P n) (vecDen (vecOf P n - (a - a'))) ≤
      Bs * E * refWeight (2 * K₀ ^ 3) K L n := by
    rw [hBs, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun a ha => ?_
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun a' ha' => ?_
    rw [mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have := twist_envelope_le hP hC hL hK hn (hg a ha a' ha')
    simp only [hEnv]
    push_cast at this ⊢
    exact this
  have hw1 : L * (Real.sqrt n)⁻¹ ≤ refWeight (2 * K₀ ^ 3) K L n := by
    unfold refWeight
    have h0 : (0 : ℝ) ≤ (if (n : ℝ) ≤ 2 * K₀ ^ 3 * L then 1 else 0) := by split_ifs <;> norm_num
    have := Real.log_nonneg (by linarith : (1 : ℝ) ≤ L)
    have := dualTailFactor_nonneg hL0.le K
    have : 0 ≤ Real.sqrt L * Real.log L * (if (n : ℝ) ≤ 2 * K₀ ^ 3 * L then 1 else 0) := by
      positivity
    have : 0 ≤ L ^ (5 / 2 : ℝ) * dualTailFactor L K := by positivity
    have : 0 ≤ L ^ 2 * Real.exp (-(L ^ 2) / 32) := by positivity
    linarith
  have h2' : Bs * (Real.sqrt K₀ * (Real.sqrt n)⁻¹) * (2 * L * G) ≤
      Bs * Real.sqrt K₀ * (2 * G) * refWeight (2 * K₀ ^ 3) K L n := by
    have e : Bs * (Real.sqrt K₀ * (Real.sqrt n)⁻¹) * (2 * L * G) =
        Bs * Real.sqrt K₀ * (2 * G) * (L * (Real.sqrt n)⁻¹) := by ring
    rw [e]
    exact mul_le_mul_of_nonneg_left hw1 (by positivity)
  have h2b : ‖∑ a ∈ A, ∑ a' ∈ A, ((c a * c a' : ℝ) : ℂ) *
        (((Real.sqrt (twistNorm P n (a - a')))⁻¹ : ℝ) : ℂ) * truncMain L (twistNorm P n (a - a')) -
      (((if K₀ * n ≤ L / 4 then twistMainWeight P A c n else 0 : ℝ)) : ℂ) *
        (logWindow L - windowHat L 0 * (Real.log n : ℂ))‖ ≤
      Bs * (Real.sqrt K₀ * (Real.sqrt n)⁻¹) * (2 * L * G) := h2
  calc _ ≤ ‖ZetaNotch.weightedMoment L (twistNotchWeight A c) (Real.log n) -
          ∑ a ∈ A, ∑ a' ∈ A, ((c a * c a' : ℝ) : ℂ) *
            (((Real.sqrt (twistNorm P n (a - a')))⁻¹ : ℝ) : ℂ) *
              truncMain L (twistNorm P n (a - a'))‖ +
        ‖∑ a ∈ A, ∑ a' ∈ A, ((c a * c a' : ℝ) : ℂ) *
            (((Real.sqrt (twistNorm P n (a - a')))⁻¹ : ℝ) : ℂ) *
              truncMain L (twistNorm P n (a - a')) -
          (((if K₀ * n ≤ L / 4 then twistMainWeight P A c n else 0 : ℝ)) : ℂ) *
            (logWindow L - windowHat L 0 * (Real.log n : ℂ))‖ :=
        norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ Bs * E * refWeight (2 * K₀ ^ 3) K L n +
        Bs * Real.sqrt K₀ * (2 * G) * refWeight (2 * K₀ ^ 3) K L n :=
        add_le_add (h1.trans hmode) (h2b.trans h2')
    _ = (Bs * E + Bs * Real.sqrt K₀ * (2 * G)) * refWeight (2 * K₀ ^ 3) K L n := by ring

/-- **The per-scale ramp inequality for a twist polynomial.** -/
theorem exists_sum_re_weightedMoment_ge_ramp_twist (hP : ∀ p ∈ P, p.Prime)
    (A : Finset (P → ℤ)) (c : (P → ℤ) → ℝ) {β : P → ℕ} (hβ : ∀ a ∈ A, ∀ p, |a p| ≤ β p)
    {K : ℕ} (hK : 2 ≤ K) :
    ∃ D, 0 ≤ D ∧ ∀ {v : ℕ → ℝ}, v 0 = 0 → ∀ (N : ℕ) {u : ℝ}, 16 ≤ u →
      u * rampSum (fun n => v n * twistMainWeight P A c n) N
          (coordBound P (fun p => 2 * β p)) notchProfileMass notchProfileLogMass u -
        D * refErrSum v (Finset.range (N + 1))
          (2 * (coordBound P (fun p => 2 * β p) : ℝ) ^ 3) K u ≤
      ∑ n ∈ Finset.range (N + 1), v n *
        (ZetaNotch.weightedMoment u (twistNotchWeight A c) (Real.log n)).re := by
  obtain ⟨D, hD0, hD⟩ := exists_norm_weightedMoment_sub_logMain_le_twist hP A c hβ hK
  refine ⟨D, hD0, fun {v} hv0 N {u} hu => ?_⟩
  have hu0 : 0 < u := by linarith
  set K₀ : ℝ := (coordBound P (fun p => 2 * β p) : ℝ) with hK₀
  unfold rampSum refErrSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun n _ => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hv0]
  set cn : ℝ := if K₀ * n ≤ u / 4 then twistMainWeight P A c n else 0 with hcn
  have h := hD hu hn.ne'
  have hre : |(ZetaNotch.weightedMoment u (twistNotchWeight A c) (Real.log n)).re -
      cn * (u * (notchProfileMass * (Real.log u - Real.log n) + notchProfileLogMass))| ≤
      D * refWeight (2 * K₀ ^ 3) K u n := by
    rw [← re_logWindow_sub_eq hu0 (Real.log n), ← Complex.re_ofReal_mul, ← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans h
  have hmain : u * ((if K₀ * n ≤ u / 4 then v n * twistMainWeight P A c n else 0) *
      (notchProfileMass * (Real.log u - Real.log n) + notchProfileLogMass)) =
      v n * (cn * (u * (notchProfileMass * (Real.log u - Real.log n) + notchProfileLogMass))) := by
    rw [hcn]; split_ifs <;> ring
  rw [hmain]
  have h2 := abs_le.mp hre
  have h3 : v n * (cn * (u * (notchProfileMass * (Real.log u - Real.log n) + notchProfileLogMass))) -
      |v n| * (D * refWeight (2 * K₀ ^ 3) K u n) ≤
      v n * (ZetaNotch.weightedMoment u (twistNotchWeight A c) (Real.log n)).re := by
    rcases le_total 0 (v n) with hv | hv
    · rw [abs_of_nonneg hv]; nlinarith
    · rw [abs_of_nonpos hv]; nlinarith
  linarith

end RHTower.WeilAbscissa
