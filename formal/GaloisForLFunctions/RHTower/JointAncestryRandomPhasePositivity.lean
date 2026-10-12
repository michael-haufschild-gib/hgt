import GaloisForLFunctions.RHTower.JointAncestryDiagonalBochner

/-!
# JAS positivity for almost every phase vector

Test the JAS product aggregate at level `σ` on a finite prime set `P` with vectors
`z_p = r ω^{k_p}`, where `ω = e^{2πi/N}`, `N ≥ 3`, and `k : P → ℤ/N` is a phase vector.

**Theorem** (`card_jasPhaseAggregate_re_neg_le`).  With `a = r/(1 + r²)` and no hypothesis on the
zeros, the number of phase vectors with negative real part is at most

`N^{|P|} · (W/Φ(0))² · (∏_{p ∈ P} (1 + 2a² p^{1−2σ}) − 1)`,

where `W = Σ_ρ |1/(ρ(1−ρ))|` and `Φ(0) = 2 + γ − log 4π`.  At level `σ = 1` the right side is
`N^{|P|}·O(Σ_P 1/p)`, so for every prime set inside a short multiplicative range `(y, y^{1+ε}]`, of
budget up to `y^{½−o(1)}`, positivity fails only on a proportion `O(ε)` of the phase vectors.

Proof.  Each factor is `(1 + r²)(1 + a(ω^k A + ω^{−k} B))`.  Averaged over the phase `k`, the linear
and quadratic phase terms vanish (`Σ_k ω^k = Σ_k ω^{2k} = 0` for `N ≥ 3`), so a single factor has mean
`1` and mean square `1 + a²(|A|² + |B|²)`.  Independence over the primes gives
`E|∏ − 1|² = ∏(1 + a²(|A|² + |B|²)) − 1`, uniformly in the zero, since `|A|, |B| ≤ p^{½−σ}` on the
strip.  The deviation `Σ_ρ w_ρ(∏_ρ − 1)` then has mean square `≤ W²(∏(1 + 2a²p^{1−2σ}) − 1)` by the
weighted Cauchy–Schwarz inequality, and a negative aggregate needs `|deviation| > Φ(0)`.

So under no hypothesis, failures of JAS positivity are confined to a vanishing proportion of phase
vectors.  The vectors that are not covered are the resonant ones, `ω^{k_p} ≈ e^{−iθ} p^{iγ}`.  The
constant vectors on narrow windows, which carry the RH-equivalent receiver, are among them.
-/

open Complex
open scoped ComplexConjugate

namespace RHTower

noncomputable section

/-! ## Phase sums -/

theorem isPrimitiveRoot_unitRoot {N : ℕ} (hN : N ≠ 0) : IsPrimitiveRoot (unitRoot N) N :=
  Complex.isPrimitiveRoot_exp N hN

theorem sum_unitRoot_pow_mul_eq_zero {N m : ℕ} (hm0 : m ≠ 0) (hmN : m < N) :
    ∑ j : Fin N, unitRoot N ^ (m * (j : ℕ)) = 0 := by
  have hprim := isPrimitiveRoot_unitRoot (N := N) (by omega)
  have hne : unitRoot N ^ m ≠ 1 := hprim.pow_ne_one_of_pos_of_lt hm0 hmN
  rw [Fin.sum_univ_eq_sum_range (fun j => unitRoot N ^ (m * j)) N]
  simp_rw [pow_mul]
  rw [geom_sum_eq hne, ← pow_mul, mul_comm m N, pow_mul, hprim.pow_eq_one, one_pow, sub_self,
    zero_div]

theorem norm_unitRoot_pow (N j : ℕ) : ‖unitRoot N ^ j‖ = 1 := by
  have := norm_unitRoot_zpow N (j : ℤ)
  rwa [zpow_natCast] at this

theorem unitRoot_pow_mul_conj (N j : ℕ) : unitRoot N ^ j * conj (unitRoot N ^ j) = 1 := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_unitRoot_pow]; simp

/-- The phase factor `1 + a(ω^j X + ω^{−j} Y)`. -/
def phaseFactor (N : ℕ) (a : ℝ) (X Y : ℂ) (j : Fin N) : ℂ :=
  1 + (a : ℂ) * (unitRoot N ^ (j : ℕ) * X + conj (unitRoot N ^ (j : ℕ)) * Y)

theorem sum_phaseFactor {N : ℕ} (hN : 3 ≤ N) (a : ℝ) (X Y : ℂ) :
    ∑ j : Fin N, phaseFactor N a X Y j = N := by
  have h1 : ∑ j : Fin N, unitRoot N ^ (j : ℕ) = 0 := by
    have := sum_unitRoot_pow_mul_eq_zero (N := N) (m := 1) one_ne_zero (by omega)
    simpa using this
  have h1c : ∑ j : Fin N, conj (unitRoot N ^ (j : ℕ)) = 0 := by
    rw [← map_sum, h1, map_zero]
  unfold phaseFactor
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.sum_mul,
    ← Finset.sum_mul, h1, h1c]
  simp

theorem sum_normSq_phaseFactor {N : ℕ} (hN : 3 ≤ N) (a : ℝ) (X Y : ℂ) :
    ∑ j : Fin N, ‖phaseFactor N a X Y j‖ ^ 2 = N * (1 + a ^ 2 * (‖X‖ ^ 2 + ‖Y‖ ^ 2)) := by
  have h1 : ∑ j : Fin N, unitRoot N ^ (j : ℕ) = 0 := by
    have := sum_unitRoot_pow_mul_eq_zero (N := N) (m := 1) one_ne_zero (by omega)
    simpa using this
  have h2 : ∑ j : Fin N, (unitRoot N ^ (j : ℕ)) ^ 2 = 0 := by
    have := sum_unitRoot_pow_mul_eq_zero (N := N) (m := 2) two_ne_zero (by omega)
    simp_rw [← pow_mul, mul_comm (2 : ℕ)] at this ⊢
    exact this
  have h1c : ∑ j : Fin N, conj (unitRoot N ^ (j : ℕ)) = 0 := by
    rw [← map_sum, h1, map_zero]
  have h2c : ∑ j : Fin N, conj (unitRoot N ^ (j : ℕ)) ^ 2 = 0 := by
    simp_rw [← map_pow]; rw [← map_sum, h2, map_zero]
  -- the complex identity `Σ g ḡ = N (1 + a²(|X|² + |Y|²))`
  have hpt : ∀ j : Fin N, phaseFactor N a X Y j * conj (phaseFactor N a X Y j) =
      1 + (a : ℂ) * (unitRoot N ^ (j : ℕ) * X + conj (unitRoot N ^ (j : ℕ)) * Y +
        conj (unitRoot N ^ (j : ℕ)) * conj X + unitRoot N ^ (j : ℕ) * conj Y) +
      (a : ℂ) ^ 2 * (X * conj X + Y * conj Y) +
      (a : ℂ) ^ 2 * ((unitRoot N ^ (j : ℕ)) ^ 2 * (X * conj Y) +
        conj (unitRoot N ^ (j : ℕ)) ^ 2 * (conj X * Y)) := by
    intro j
    have hw := unitRoot_pow_mul_conj N (j : ℕ)
    unfold phaseFactor
    simp only [map_add, map_one, map_mul, Complex.conj_ofReal, Complex.conj_conj]
    linear_combination ((a : ℂ) ^ 2 * (X * conj X + Y * conj Y)) * hw
  have hsum : ∑ j : Fin N, phaseFactor N a X Y j * conj (phaseFactor N a X Y j) =
      (N : ℂ) * (1 + (a : ℂ) ^ 2 * (X * conj X + Y * conj Y)) := by
    simp_rw [hpt]
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_mul, h1, h1c, h2, h2c]
    simp
    ring
  have hre : ∀ j : Fin N, ‖phaseFactor N a X Y j‖ ^ 2 =
      (phaseFactor N a X Y j * conj (phaseFactor N a X Y j)).re := by
    intro j
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  simp_rw [hre]
  rw [← Complex.re_sum, hsum, Complex.mul_conj X, Complex.mul_conj Y, ← Complex.ofReal_add,
    show (1 : ℂ) + (a : ℂ) ^ 2 * ((Complex.normSq X + Complex.normSq Y : ℝ) : ℂ) =
      ((1 + a ^ 2 * (Complex.normSq X + Complex.normSq Y) : ℝ) : ℂ) by push_cast; ring,
    ← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re,
    Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]

/-! ## Products over the primes -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `Σ_k |∏_i g_i(k_i) − 1|² = N^{|ι|}(∏_i (1 + a²(|X_i|² + |Y_i|²)) − 1)`. -/
theorem sum_normSq_prod_phaseFactor_sub_one {N : ℕ} (hN : 3 ≤ N) (a : ℝ) (X Y : ι → ℂ) :
    ∑ k : ι → Fin N, ‖(∏ i, phaseFactor N a (X i) (Y i) (k i)) - 1‖ ^ 2 =
      (N : ℝ) ^ Fintype.card ι * ((∏ i, (1 + a ^ 2 * (‖X i‖ ^ 2 + ‖Y i‖ ^ 2))) - 1) := by
  have hmean : ∑ k : ι → Fin N, ∏ i, phaseFactor N a (X i) (Y i) (k i) =
      (N : ℂ) ^ Fintype.card ι := by
    rw [← Fintype.prod_sum (fun i j => phaseFactor N a (X i) (Y i) j)]
    simp_rw [sum_phaseFactor hN]
    simp
  have hsq : ∑ k : ι → Fin N, ‖∏ i, phaseFactor N a (X i) (Y i) (k i)‖ ^ 2 =
      (N : ℝ) ^ Fintype.card ι * ∏ i, (1 + a ^ 2 * (‖X i‖ ^ 2 + ‖Y i‖ ^ 2)) := by
    simp_rw [norm_prod, ← Finset.prod_pow]
    rw [← Fintype.prod_sum (fun i j => ‖phaseFactor N a (X i) (Y i) j‖ ^ 2)]
    simp_rw [sum_normSq_phaseFactor hN]
    rw [Finset.prod_mul_distrib]
    simp
  have hexp : ∀ z : ℂ, ‖z - 1‖ ^ 2 = ‖z‖ ^ 2 - 2 * z.re + 1 := by
    intro z
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
    simp
    ring
  simp_rw [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hsq, ← Finset.mul_sum, ← Complex.re_sum,
    hmean]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  push_cast
  rw [← Complex.ofReal_natCast, ← Complex.ofReal_pow, Complex.ofReal_re]
  ring

/-! ## The weighted Cauchy–Schwarz inequality for series -/

theorem sq_tsum_mul_le {α : Type*} {c x : α → ℝ} (hc : ∀ i, 0 ≤ c i) (hcs : Summable c)
    (hcx : Summable fun i => c i * x i) (hcx2 : Summable fun i => c i * x i ^ 2) :
    (∑' i, c i * x i) ^ 2 ≤ (∑' i, c i) * ∑' i, c i * x i ^ 2 := by
  have hq : ∀ t : ℝ, 0 ≤ (∑' i, c i) * (t * t) + (-2 * ∑' i, c i * x i) * t +
      ∑' i, c i * x i ^ 2 := by
    intro t
    have e : (∑' i, c i) * (t * t) + (-2 * ∑' i, c i * x i) * t + ∑' i, c i * x i ^ 2 =
        ∑' i, c i * (x i - t) ^ 2 := by
      have h1 : Summable fun i => c i * (t * t) := hcs.mul_right _
      have h2 : Summable fun i => (-2 * t) * (c i * x i) := hcx.mul_left _
      have e2 : ∀ i, c i * (x i - t) ^ 2 = c i * x i ^ 2 + (-2 * t) * (c i * x i) +
          c i * (t * t) := fun i => by ring
      simp_rw [e2]
      rw [(hcx2.add h2).tsum_add h1, hcx2.tsum_add h2, tsum_mul_left, tsum_mul_right]
      ring
    rw [e]
    exact tsum_nonneg fun i => mul_nonneg (hc i) (sq_nonneg _)
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith

/-! ## The phase aggregate -/

/-- The JAS aggregate at level `σ` of the phase vector `k`, with `z_p = r ω^{k_p}`. -/
def jasPhaseAggregate (σ r : ℝ) (N : ℕ) (P : Finset Nat.Primes) (k : ↥P → Fin N) : ℂ :=
  ∑' q : XiZeroCopy, (∏ p : ↥P, jasBernoulliFactor (jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p)
    (jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p) ((r : ℂ) * unitRoot N ^ ((k p : Fin N) : ℕ))) /
      ((q.1 : ℂ) * (1 - (q.1 : ℂ)))

theorem jasBernoulliFactor_phase (A B : ℂ) {r : ℝ} (hr : 0 ≤ r) {N : ℕ} (j : Fin N) :
    jasBernoulliFactor A B ((r : ℂ) * unitRoot N ^ (j : ℕ)) =
      ((1 + r ^ 2 : ℝ) : ℂ) * phaseFactor N (r / (1 + r ^ 2)) A B j := by
  have hpos : (0 : ℝ) < 1 + r ^ 2 := by positivity
  have hn : ‖(r : ℂ) * unitRoot N ^ (j : ℕ)‖ = r := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr, norm_unitRoot_pow,
      mul_one]
  rw [jasBernoulliFactor_eq_mul, hn]
  unfold phaseFactor
  have hne : ((1 + r ^ 2 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
  rw [map_mul, Complex.conj_ofReal]
  push_cast
  field_simp

theorem norm_phaseFactor_le {N : ℕ} {a : ℝ} (ha : 0 ≤ a) (X Y : ℂ) (j : Fin N) :
    ‖phaseFactor N a X Y j‖ ≤ 1 + a * (‖X‖ + ‖Y‖) := by
  unfold phaseFactor
  refine (norm_add_le _ _).trans ?_
  rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ha]
  have h : ‖unitRoot N ^ (j : ℕ) * X + conj (unitRoot N ^ (j : ℕ)) * Y‖ ≤ ‖X‖ + ‖Y‖ := by
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul, Complex.norm_conj, norm_unitRoot_pow, one_mul, one_mul]
  have := mul_le_mul_of_nonneg_left h ha
  linarith

theorem norm_jasHoloA_le_half (σ : ℝ) (q : XiZeroCopy) (p : Nat.Primes) :
    ‖jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p‖ ≤ Real.exp (-(σ - 1 / 2) * Real.log p) := by
  refine (norm_jasHoloA_dressed_le_abs σ q p).trans (Real.exp_le_exp.mpr ?_)
  have hb : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith [xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q]
  nlinarith [log_prime_pos p]

theorem norm_jasHoloB_le_half (σ : ℝ) (q : XiZeroCopy) (p : Nat.Primes) :
    ‖jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p‖ ≤ Real.exp (-(σ - 1 / 2) * Real.log p) := by
  refine (norm_jasHoloB_dressed_le_abs σ q p).trans (Real.exp_le_exp.mpr ?_)
  have hb : |(q.1 : ℂ).re - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith [xiZeroCopy_re_pos q, xiZeroCopy_re_lt_one q]
  nlinarith [log_prime_pos p]

/-- **JAS positivity for almost every phase vector.**  The number of phase vectors `k : P → ℤ/N`,
`N ≥ 3`, at which the JAS aggregate has negative real part is at most
`N^{|P|}·(W/Φ(0))²·(∏_P(1 + 2a²p^{1−2σ}) − 1)`, `a = r/(1 + r²)`. -/
theorem card_jasPhaseAggregate_re_neg_le (σ : ℝ) {r : ℝ} (hr : 0 ≤ r) {N : ℕ} (hN : 3 ≤ N)
    (P : Finset Nat.Primes) :
    ((Finset.univ.filter fun k : ↥P → Fin N => (jasPhaseAggregate σ r N P k).re < 0).card : ℝ) ≤
      (N : ℝ) ^ P.card * (lagWeightTotal / poleSharpConstant) ^ 2 *
        ((∏ p ∈ P, (1 + 2 * (r / (1 + r ^ 2)) ^ 2 * Real.exp ((1 - 2 * σ) * Real.log p))) - 1) := by
  classical
  obtain ⟨a, hadef⟩ : ∃ a : ℝ, a = r / (1 + r ^ 2) := ⟨_, rfl⟩
  have ha : 0 ≤ a := by rw [hadef]; positivity
  rw [← hadef]
  have hΦ := poleSharpConstant_pos
  have hW := lagWeightTotal_nonneg
  -- notation
  obtain ⟨A, hAdef⟩ : ∃ A : XiZeroCopy → Nat.Primes → ℂ,
      A = fun q p => jasHoloA ((q.1 : ℂ) + (σ - 1 / 2 : ℝ)) p := ⟨_, rfl⟩
  obtain ⟨B, hBdef⟩ : ∃ B : XiZeroCopy → Nat.Primes → ℂ,
      B = fun q p => jasHoloB ((q.1 : ℂ) - (σ - 1 / 2 : ℝ)) p := ⟨_, rfl⟩
  obtain ⟨e, hedef⟩ : ∃ e : Nat.Primes → ℝ,
      e = fun p : Nat.Primes => Real.exp (-(σ - 1 / 2) * Real.log p) :=
    ⟨_, rfl⟩
  have hA : ∀ q p, ‖A q p‖ ≤ e p := fun q p => by rw [hAdef, hedef]; exact norm_jasHoloA_le_half σ q p
  have hB : ∀ q p, ‖B q p‖ ≤ e p := fun q p => by rw [hBdef, hedef]; exact norm_jasHoloB_le_half σ q p
  have he0 : ∀ p, 0 ≤ e p := fun p => by rw [hedef]; exact (Real.exp_pos _).le
  obtain ⟨Pi, hPidef⟩ : ∃ Pi : XiZeroCopy → (↥P → Fin N) → ℂ,
      Pi = fun q k => ∏ p : ↥P, phaseFactor N a (A q p) (B q p) (k p) := ⟨_, rfl⟩
  obtain ⟨w, hwdef⟩ : ∃ w : XiZeroCopy → ℂ, w = fun q => 1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ))) :=
    ⟨_, rfl⟩
  have hws : Summable w := by rw [hwdef]; exact summable_inv_mul_one_sub
  have hwn : Summable fun q => ‖w q‖ := hws.norm
  -- uniform bound on the products
  obtain ⟨M₀, hM₀def⟩ : ∃ M₀ : ℝ, M₀ = ∏ p : ↥P, (1 + a * (2 * e p)) := ⟨_, rfl⟩
  have hPi : ∀ q k, ‖Pi q k‖ ≤ M₀ := by
    intro q k
    rw [hPidef, hM₀def, norm_prod]
    refine Finset.prod_le_prod (fun p _ => norm_nonneg _) fun p _ => ?_
    refine (norm_phaseFactor_le ha _ _ _).trans ?_
    have := hA q p; have := hB q p
    nlinarith
  have hx : ∀ q k, ‖Pi q k - 1‖ ≤ M₀ + 1 := fun q k =>
    (norm_sub_le _ _).trans (by rw [norm_one]; linarith [hPi q k])
  -- the aggregate in terms of `Pi`
  have hagg : ∀ k, jasPhaseAggregate σ r N P k =
      (((1 + r ^ 2) ^ P.card : ℝ) : ℂ) * ∑' q, w q * Pi q k := by
    intro k
    unfold jasPhaseAggregate
    rw [← tsum_mul_left]
    refine tsum_congr fun q => ?_
    rw [Finset.prod_congr rfl fun p _ => jasBernoulliFactor_phase _ _ hr (k p),
      Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_coe, hPidef,
      hwdef, hAdef, hBdef, hadef]
    push_cast
    ring
  -- the deviation
  have hsumPi : ∀ k, Summable fun q => w q * (Pi q k - 1) := fun k =>
    Summable.of_norm_bounded (hwn.mul_right (M₀ + 1)) fun q => by
      rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hx q k) (norm_nonneg _)
  have hsplit : ∀ k, ∑' q, w q * Pi q k = (poleSharpConstant : ℂ) + ∑' q, w q * (Pi q k - 1) := by
    intro k
    have e1 : ∀ q, w q * Pi q k = w q + w q * (Pi q k - 1) := fun q => by ring
    simp_rw [e1]
    rw [hws.tsum_add (hsumPi k), hwdef, tsum_inv_zero_mul_one_sub_zero]
  obtain ⟨S, hSdef⟩ : ∃ S : (↥P → Fin N) → ℝ, S = fun k => ∑' q, ‖w q‖ * ‖Pi q k - 1‖ :=
    ⟨_, rfl⟩
  have hSs : ∀ k, Summable fun q => ‖w q‖ * ‖Pi q k - 1‖ := fun k =>
    Summable.of_nonneg_of_le (fun q => by positivity)
      (fun q => mul_le_mul_of_nonneg_left (hx q k) (norm_nonneg _)) (hwn.mul_right _)
  have hSs2 : ∀ k, Summable fun q => ‖w q‖ * ‖Pi q k - 1‖ ^ 2 := fun k =>
    Summable.of_nonneg_of_le (fun q => by positivity)
      (fun q => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hx q k) 2)
        (norm_nonneg _)) (hwn.mul_right _)
  -- a negative aggregate forces a large deviation
  have hbad : ∀ k, (jasPhaseAggregate σ r N P k).re < 0 → poleSharpConstant ^ 2 ≤ S k ^ 2 := by
    intro k hk
    rw [hagg, hsplit, Complex.re_ofReal_mul] at hk
    have hc : 0 < ((1 + r ^ 2) ^ P.card : ℝ) := by positivity
    have hre : ((poleSharpConstant : ℂ) + ∑' q, w q * (Pi q k - 1)).re < 0 := by
      by_contra h; push Not at h; linarith [mul_nonneg hc.le h]
    rw [Complex.add_re, Complex.ofReal_re] at hre
    have h1 : poleSharpConstant ≤ ‖∑' q, w q * (Pi q k - 1)‖ := by
      have := (neg_le_abs _).trans (Complex.abs_re_le_norm (∑' q, w q * (Pi q k - 1))); linarith
    have h2 : ‖∑' q, w q * (Pi q k - 1)‖ ≤ S k := by
      rw [hSdef]
      refine (norm_tsum_le_tsum_norm (hsumPi k).norm).trans (le_of_eq ?_)
      exact tsum_congr fun q => norm_mul _ _
    exact pow_le_pow_left₀ hΦ.le (h1.trans h2) 2
  -- the mean square of the deviation
  have hCS : ∀ k, S k ^ 2 ≤ lagWeightTotal * ∑' q, ‖w q‖ * ‖Pi q k - 1‖ ^ 2 := by
    intro k
    rw [hSdef]
    have := sq_tsum_mul_le (c := fun q => ‖w q‖) (x := fun q => ‖Pi q k - 1‖)
      (fun q => norm_nonneg _) hwn (hSs k) (hSs2 k)
    have hWt : ∑' q, ‖w q‖ = lagWeightTotal := by rw [hwdef]; rfl
    rwa [hWt] at this
  obtain ⟨Q, hQdef⟩ : ∃ Q : ℝ,
      Q = (∏ p ∈ P, (1 + 2 * a ^ 2 * Real.exp ((1 - 2 * σ) * Real.log p))) - 1 := ⟨_, rfl⟩
  have hmsq : ∀ q, ∑ k : ↥P → Fin N, ‖Pi q k - 1‖ ^ 2 ≤ (N : ℝ) ^ P.card * Q := by
    intro q
    have h := sum_normSq_prod_phaseFactor_sub_one hN a (fun p : ↥P => A q p) (fun p => B q p)
    rw [Fintype.card_coe] at h
    rw [hPidef]
    simp only at h ⊢
    rw [h]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [hQdef]
    have hle : ∏ p : ↥P, (1 + a ^ 2 * (‖A q p‖ ^ 2 + ‖B q p‖ ^ 2)) ≤
        ∏ p : ↥P, (1 + 2 * a ^ 2 * Real.exp ((1 - 2 * σ) * Real.log p)) := by
      refine Finset.prod_le_prod (fun p _ => by positivity) fun p _ => ?_
      have h1 := pow_le_pow_left₀ (norm_nonneg _) (hA q p) 2
      have h2 := pow_le_pow_left₀ (norm_nonneg _) (hB q p) 2
      have h3 : e p ^ 2 = Real.exp ((1 - 2 * σ) * Real.log p) := by
        rw [hedef, ← Real.exp_nat_mul]; push_cast; ring_nf
      nlinarith [sq_nonneg a]
    rw [Finset.prod_coe_sort P (fun p => 1 + 2 * a ^ 2 * Real.exp ((1 - 2 * σ) * Real.log p))]
      at hle
    linarith
  have htotal : ∑ k : ↥P → Fin N, S k ^ 2 ≤
      lagWeightTotal ^ 2 * ((N : ℝ) ^ P.card * Q) := by
    have h1 : ∑ k : ↥P → Fin N, S k ^ 2 ≤
        ∑ k : ↥P → Fin N, lagWeightTotal * ∑' q, ‖w q‖ * ‖Pi q k - 1‖ ^ 2 :=
      Finset.sum_le_sum fun k _ => hCS k
    rw [← Finset.mul_sum, ← Summable.tsum_finsetSum fun k _ => hSs2 k] at h1
    have h2 : ∑' q, ∑ k : ↥P → Fin N, ‖w q‖ * ‖Pi q k - 1‖ ^ 2 ≤
        ∑' q, ‖w q‖ * ((N : ℝ) ^ P.card * Q) := by
      refine Summable.tsum_le_tsum (fun q => ?_) (summable_sum fun k _ => hSs2 k)
        (hwn.mul_right _)
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (hmsq q) (norm_nonneg _)
    rw [tsum_mul_right, show ∑' q, ‖w q‖ = lagWeightTotal by rw [hwdef]; rfl] at h2
    calc ∑ k : ↥P → Fin N, S k ^ 2 ≤ lagWeightTotal * (lagWeightTotal * ((N : ℝ) ^ P.card * Q)) :=
          h1.trans (mul_le_mul_of_nonneg_left h2 hW)
      _ = lagWeightTotal ^ 2 * ((N : ℝ) ^ P.card * Q) := by ring
  -- counting
  have hcount : ((Finset.univ.filter fun k : ↥P → Fin N =>
      (jasPhaseAggregate σ r N P k).re < 0).card : ℝ) * poleSharpConstant ^ 2 ≤
      ∑ k : ↥P → Fin N, S k ^ 2 := by
    rw [show ((Finset.univ.filter fun k : ↥P → Fin N =>
        (jasPhaseAggregate σ r N P k).re < 0).card : ℝ) * poleSharpConstant ^ 2 =
        ∑ _k ∈ Finset.univ.filter (fun k : ↥P → Fin N => (jasPhaseAggregate σ r N P k).re < 0),
          poleSharpConstant ^ 2 by rw [Finset.sum_const, nsmul_eq_mul]]
    calc ∑ _k ∈ Finset.univ.filter (fun k : ↥P → Fin N => (jasPhaseAggregate σ r N P k).re < 0),
          poleSharpConstant ^ 2
        ≤ ∑ k ∈ Finset.univ.filter (fun k : ↥P → Fin N => (jasPhaseAggregate σ r N P k).re < 0),
            S k ^ 2 := Finset.sum_le_sum fun k hk => hbad k (Finset.mem_filter.mp hk).2
      _ ≤ ∑ k : ↥P → Fin N, S k ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun k _ _ => sq_nonneg _)
  have hΦ2 : 0 < poleSharpConstant ^ 2 := by positivity
  rw [← hQdef]
  have hfin := hcount.trans htotal
  rw [div_pow, ← le_div_iff₀ hΦ2] at *
  calc _ ≤ lagWeightTotal ^ 2 * ((N : ℝ) ^ P.card * Q) / poleSharpConstant ^ 2 := hfin
    _ = _ := by ring

end

end RHTower
