import GaloisForLFunctions.SquareRootThreshold.OnLineShadowIndistinguishability

/-!
# Nyquist pinning of on-line configurations

Depth is invisible below the Nyquist aperture (the lattice law). This module shows that *position*
is too: the Weil form of a weighted on-line periodic configuration
`Sh(f) = Σ_k w_k Σ_j |h_f(c_k + 2πj/ℓ)|²` (`onLineShadow`) pins its ordinates exactly from the
Nyquist aperture of its point density on.

* **Moments** (`onLineShadow_eq_lagSum`, `shadowMoment_eq_of_onLineShadow_eq`). `Sh(f) =
  ℓ Σ_m k_f(mℓ) M(m)` with `M(m) = Σ_k w_k e^{ic_k mℓ}`, and agreement of two shadows on all tests
  of aperture `a` is agreement of their moments `M(m)` for `|m| < ⌈2a/ℓ⌉`. One universal family of
  lag-point bump tests (`exists_bumpTest_universal`) reads every Toeplitz form at once.
* **Atomic pinning** (`atomic_pinning`). If `r` distinct unit nodes with real weights have the
  same moments for `|m| ≤ r` as any nonnegative atomic measure, that measure lives on the same
  nodes with the same weights. The Toeplitz form of an atomic moment sequence is
  `Σ_i w_i |P_c(z_i)|²` (`toeplitzForm_atomic`); the vanishing polynomial `Π (z − z_k)` of degree `r`
  annihilates the first measure, hence the second, and the Lagrange polynomials recover the weights.
* **Nyquist pinning** (`onLineShadow_pinning`). Two weighted on-line periodic configurations, the
  first with `r` ordinates per period `2π/ℓ`, that agree on every test of an aperture `a` with
  `r < ⌈2a/ℓ⌉` have the same ordinates and weights, and so agree on every test of every aperture.
* **Sharpness** (`onLineShadow_crystal_unpinned`, `exists_onLineShadow_crystal_distinguished`).
  The `r`-point crystal and its rotation by half a step agree on all tests with `⌈2a/ℓ⌉ ≤ r` and are
  told apart at every aperture with `⌈2a/ℓ⌉ > r`.

Together with the lattice law: below the Nyquist aperture `rℓ/2` of a configuration of `r` points
per period `2π/ℓ` the Weil form sees neither the depth nor the position of its zeros; above it, it
sees both.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-! ### Moments of on-line shadows -/

/-- The moments `M(m) = Σ_k w_k e^{ic_k mℓ}` of a weighted on-line periodic configuration. -/
def shadowMoment (ℓ : ℝ) {r : ℕ} (c w : Fin r → ℝ) (m : ℤ) : ℂ :=
  ∑ k, (w k : ℂ) * cexp (I * c k * (m * ℓ))

/-- The phase nodes `e^{ic_kℓ}`. -/
def shadowNode (ℓ : ℝ) {r : ℕ} (c : Fin r → ℝ) (k : Fin r) : ℂ := cexp ((c k * ℓ : ℝ) * I)

theorem norm_shadowNode (ℓ : ℝ) {r : ℕ} (c : Fin r → ℝ) (k : Fin r) : ‖shadowNode ℓ c k‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem shadowMoment_eq_nodes (ℓ : ℝ) {r : ℕ} (c w : Fin r → ℝ) (m : ℤ) :
    shadowMoment ℓ c w m = ∑ k, (w k : ℂ) * shadowNode ℓ c k ^ m := by
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [shadowNode, ← Complex.exp_int_mul]
  push_cast
  ring_nf

theorem shadowMoment_neg (ℓ : ℝ) {r : ℕ} (c w : Fin r → ℝ) (m : ℤ) :
    shadowMoment ℓ c w (-m) = conj (shadowMoment ℓ c w m) := by
  rw [shadowMoment, shadowMoment, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  congr 2
  simp only [map_mul, Complex.conj_I, Complex.conj_ofReal, map_intCast]
  push_cast
  ring

/-- `Sh(f) = ℓ Σ_m k_f(mℓ) M(m)`. -/
theorem onLineShadow_eq_lagSum {ℓ : ℝ} (hℓ : 0 < ℓ) {r : ℕ} (c w : Fin r → ℝ) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    ((onLineShadow ℓ c w f : ℝ) : ℂ) =
      ((ℓ : ℝ) : ℂ) * ∑' m : ℤ, EF.weilTest f f (m * ℓ) * shadowMoment ℓ c w m := by
  obtain ⟨A, hfs⟩ := exists_Icc_of_hasCompactSupport hfc
  obtain ⟨S, hS⟩ := exists_lag_window (K := EF.weilTest f f) hℓ (weilTest_abs_le hfs hfs)
  have hwin : ∀ x : ℝ, ∑' m : ℤ, EF.weilTest f f (m * ℓ) * cexp (I * x * (m * ℓ)) =
      ∑ m ∈ S, EF.weilTest f f (m * ℓ) * cexp (I * x * (m * ℓ)) := fun x =>
    tsum_eq_sum fun m hm => by rw [hS m hm, zero_mul]
  have hR : ∑' m : ℤ, EF.weilTest f f (m * ℓ) * shadowMoment ℓ c w m =
      ∑ m ∈ S, EF.weilTest f f (m * ℓ) * shadowMoment ℓ c w m :=
    tsum_eq_sum fun m hm => by rw [hS m hm, zero_mul]
  rw [onLineShadow, Complex.ofReal_sum, hR]
  simp_rw [shadowMoment, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Complex.ofReal_mul, ← lagSum_translate_eq_onLine hℓ hf hfs (c k), hwin, Finset.mul_sum,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-! ### Toeplitz forms that vanish identically -/

theorem toeplitzForm_sub (D₁ D₂ : ℤ → ℂ) {n : ℕ} (c : Fin n → ℂ) :
    toeplitzForm (fun m => D₁ m - D₂ m) n c = toeplitzForm D₁ n c - toeplitzForm D₂ n c := by
  simp only [toeplitzForm, mul_sub, Finset.sum_sub_distrib]

theorem toeplitzForm_neg (D : ℤ → ℂ) {n : ℕ} (c : Fin n → ℂ) :
    toeplitzForm (fun m => -D m) n c = -toeplitzForm D n c := by
  simp only [toeplitzForm, mul_neg, Finset.sum_neg_distrib]

/-- A Hermitian symbol whose Toeplitz forms of size `n` all vanish is `0` on `|m| < n`. -/
theorem eq_zero_of_toeplitzForm_eq_zero {E : ℤ → ℂ} (hE : ∀ m, E (-m) = conj (E m)) {n : ℕ}
    (h : ∀ c : Fin n → ℂ, toeplitzForm E n c = 0) {m : ℤ} (hm : |m| < n) : E m = 0 := by
  have hE0 : E 0 = 0 := by
    have hn : 0 < n := by have := abs_nonneg m; omega
    have := h (Pi.single ⟨0, hn⟩ 1)
    simpa [toeplitzForm, Pi.single_apply] using this
  have hpos : ∀ k : ℕ, 1 ≤ k → (k : ℤ) < n → E k = 0 := by
    intro k hk1 hkn
    have h1 := norm_le_of_toeplitzForm_nonneg hE (fun c => by rw [h c, Complex.zero_re]) hk1
      (by exact_mod_cast hkn)
    rw [hE0, Complex.zero_re] at h1
    exact norm_le_zero_iff.mp h1
  obtain ⟨k, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · exact hE0
    · exact hpos k hk (by rw [abs_of_nonneg (by positivity)] at hm; exact hm)
  · rcases Nat.eq_zero_or_pos k with rfl | hk
    · simpa using hE0
    · rw [hE, hpos k hk (by rw [abs_neg, abs_of_nonneg (by positivity)] at hm; exact hm),
        map_zero]

/-- **Universal lag-point test.** For every vector `c` of size `⌈2a/ℓ⌉` one test of aperture `a`
reads `Σ_m k(mℓ) D(m) = B · T_D(c)` for every symbol `D`, with one constant `B > 0`. -/
theorem exists_bumpTest_universal {ℓ a : ℝ} (hℓ : 0 < ℓ) (ha : 0 < a)
    (c : Fin ⌈2 * a / ℓ⌉₊ → ℂ) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧ ∃ B : ℝ, 0 < B ∧
      ∀ D : ℤ → ℂ, ∑' m : ℤ, EF.weilTest f f (m * ℓ) * D m =
        (B : ℂ) * toeplitzForm D ⌈2 * a / ℓ⌉₊ c := by
  have hna : ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) * ℓ < 2 * a := by
    have := Nat.ceil_lt_add_one (by positivity : (0 : ℝ) ≤ 2 * a / ℓ)
    have : ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) < 2 * a / ℓ := by linarith
    rwa [lt_div_iff₀ hℓ] at this
  have hgap : 0 < a - ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) / 2 * ℓ := by linarith
  obtain ⟨w, hw⟩ : ∃ w : ℝ,
      w = min (min (ℓ / 2) (a - ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) / 2 * ℓ)) 1 / 4 := ⟨_, rfl⟩
  have hw0 : 0 < w := by
    rw [hw]; exact div_pos (lt_min (lt_min (by linarith) hgap) one_pos) (by norm_num)
  have hm1 := min_le_left (min (ℓ / 2) (a - ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) / 2 * ℓ)) 1
  have hm2 := min_le_right (min (ℓ / 2) (a - ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) / 2 * ℓ)) 1
  have hm3 := min_le_left (ℓ / 2) (a - ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) / 2 * ℓ)
  have hm4 := min_le_right (ℓ / 2) (a - ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) / 2 * ℓ)
  have hwℓ : 2 * w < ℓ := by rw [hw]; linarith
  have hwa : ((⌈2 * a / ℓ⌉₊ : ℕ) - 1 : ℝ) / 2 * ℓ + w ≤ a := by rw [hw]; linarith
  have hw4 : 4 * w ≤ 1 := by rw [hw]; linarith
  obtain ⟨β, hβ2, hβcs, hβs, -, -, hB⟩ := exists_polarFree_bump hw0 hw4
  exact ⟨bumpTest β ℓ c, contDiff_bumpTest hβ2 ℓ c, tsupport_bumpTest_subset hβs hℓ.le hwa c,
    _, hB, fun D => lagSum_bumpTest_eq_toeplitz hℓ hwℓ hβ2.continuous hβcs hβs D c⟩

/-- Two shadows that agree on every test of aperture `a` have the same moments on
`|m| < ⌈2a/ℓ⌉`. -/
theorem shadowMoment_eq_of_onLineShadow_eq {ℓ : ℝ} (hℓ : 0 < ℓ) {r s : ℕ} (c w : Fin r → ℝ)
    (c' w' : Fin s → ℝ) {a : ℝ} (ha : 0 < a)
    (h : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      onLineShadow ℓ c w f = onLineShadow ℓ c' w' f)
    {m : ℤ} (hm : |m| < ⌈2 * a / ℓ⌉₊) : shadowMoment ℓ c w m = shadowMoment ℓ c' w' m := by
  have hE : ∀ c₀ : Fin ⌈2 * a / ℓ⌉₊ → ℂ, toeplitzForm
      (fun m => shadowMoment ℓ c w m - shadowMoment ℓ c' w' m) ⌈2 * a / ℓ⌉₊ c₀ = 0 := by
    intro c₀
    obtain ⟨f, hf, hfs, B, hB, hlag⟩ := exists_bumpTest_universal hℓ ha c₀
    have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
    have h1 : ((onLineShadow ℓ c w f : ℝ) : ℂ) = ((onLineShadow ℓ c' w' f : ℝ) : ℂ) := by
      rw [h f hf hfs]
    rw [onLineShadow_eq_lagSum hℓ c w hf hfc, onLineShadow_eq_lagSum hℓ c' w' hf hfc, hlag,
      hlag] at h1
    have hℓB : ((ℓ : ℝ) : ℂ) * (B : ℂ) ≠ 0 := by
      have : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
      have : (B : ℂ) ≠ 0 := by exact_mod_cast hB.ne'
      positivity
    rw [toeplitzForm_sub, sub_eq_zero]
    have h2 : ((ℓ : ℝ) : ℂ) * (B : ℂ) * toeplitzForm (shadowMoment ℓ c w) ⌈2 * a / ℓ⌉₊ c₀ =
        ((ℓ : ℝ) : ℂ) * (B : ℂ) * toeplitzForm (shadowMoment ℓ c' w') ⌈2 * a / ℓ⌉₊ c₀ := by
      rw [mul_assoc, mul_assoc]; exact h1
    exact mul_left_cancel₀ hℓB h2
  have hherm : ∀ m, (fun m => shadowMoment ℓ c w m - shadowMoment ℓ c' w' m) (-m) =
      conj ((fun m => shadowMoment ℓ c w m - shadowMoment ℓ c' w' m) m) := fun m => by
    simp only [shadowMoment_neg, map_sub]
  exact sub_eq_zero.mp (eq_zero_of_toeplitzForm_eq_zero hherm hE hm)

/-! ### Atomic pinning -/

/-- The Toeplitz form of an atomic moment sequence on the unit circle is
`Σ_i w_i |Σ_j c_j z_i^j|²`. -/
theorem toeplitzForm_atomic {s : ℕ} (z : Fin s → ℂ) (hz : ∀ i, ‖z i‖ = 1) (w : Fin s → ℝ)
    {n : ℕ} (c : Fin n → ℂ) :
    toeplitzForm (fun m => ∑ i, (w i : ℂ) * z i ^ m) n c =
      ∑ i, (w i : ℂ) * ((‖∑ j, c j * z i ^ (j : ℕ)‖ ^ 2 : ℝ) : ℂ) := by
  have hpow : ∀ (i : Fin s) (j j' : Fin n), z i ^ (((j : ℕ) : ℤ) - ((j' : ℕ) : ℤ)) =
      z i ^ (j : ℕ) * conj (z i ^ (j' : ℕ)) := by
    intro i j j'
    have hz0 : z i ≠ 0 := by intro h0; have := hz i; rw [h0, norm_zero] at this; norm_num at this
    rw [zpow_sub₀ hz0, zpow_natCast, zpow_natCast, div_eq_mul_inv,
      Complex.inv_eq_conj (by rw [norm_pow, hz i, one_pow])]
  have hrhs : ∀ i, (w i : ℂ) * ((‖∑ j, c j * z i ^ (j : ℕ)‖ ^ 2 : ℝ) : ℂ) =
      ∑ j, ∑ j', c j * conj (c j') * ((w i : ℂ) * z i ^ (((j : ℕ) : ℤ) - ((j' : ℕ) : ℤ))) := by
    intro i
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j' _ => ?_
    rw [hpow, map_mul]
    ring
  rw [toeplitzForm, Finset.sum_congr rfl fun i _ => hrhs i]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j' _ => ?_
  rw [Finset.mul_sum]

/-- **Atomic pinning.** If `r` distinct unit nodes with real weights have the same moments for
`|m| ≤ r` as a nonnegative atomic measure on the unit circle, that measure lives on the same nodes
with the same weights. -/
theorem atomic_pinning {r s : ℕ} (z : Fin r → ℂ) (hz : ∀ k, ‖z k‖ = 1)
    (hinj : Function.Injective z) (w : Fin r → ℝ) (z' : Fin s → ℂ)
    (hz' : ∀ i, ‖z' i‖ = 1) (w' : Fin s → ℝ) (hw' : ∀ i, 0 ≤ w' i)
    (hM : ∀ m : ℤ, |m| ≤ r → ∑ k, (w k : ℂ) * z k ^ m = ∑ i, (w' i : ℂ) * z' i ^ m) :
    (∀ i, 0 < w' i → ∃ k, z' i = z k) ∧
      ∀ k, ∑ i ∈ Finset.univ.filter (fun i => z' i = z k), w' i = w k := by
  have hT : ∀ q : Fin (r + 1) → ℂ, toeplitzForm (fun m => ∑ k, (w k : ℂ) * z k ^ m) (r + 1) q =
      toeplitzForm (fun m => ∑ i, (w' i : ℂ) * z' i ^ m) (r + 1) q := by
    intro q
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun j' _ => ?_
    have hj := j.isLt
    have hj' := j'.isLt
    have hm : |((j : ℕ) : ℤ) - ((j' : ℕ) : ℤ)| ≤ r := abs_le.mpr ⟨by omega, by omega⟩
    simp only [hM _ hm]
  have heval : ∀ p : Polynomial ℂ, p.natDegree < r + 1 → ∀ x : ℂ,
      ∑ j : Fin (r + 1), p.coeff j * x ^ (j : ℕ) = p.eval x := by
    intro p hp x
    rw [Polynomial.eval_eq_sum_range' hp, ← Fin.sum_univ_eq_sum_range (fun j => p.coeff j * x ^ j)]
  -- `Σ_k w_k |p(z_k)|² = Σ_i w'_i |p(z'_i)|²` for every `p` of degree at most `r`
  have hkey : ∀ p : Polynomial ℂ, p.natDegree < r + 1 →
      ∑ k, w k * ‖p.eval (z k)‖ ^ 2 = ∑ i, w' i * ‖p.eval (z' i)‖ ^ 2 := by
    intro p hp
    have h1 := hT fun j => p.coeff j
    rw [toeplitzForm_atomic z hz w, toeplitzForm_atomic z' hz' w'] at h1
    simp_rw [heval p hp] at h1
    exact_mod_cast h1
  have hdeg : ∀ t : Finset (Fin r),
      (∏ k ∈ t, (Polynomial.X - Polynomial.C (z k))).natDegree < r + 1 := by
    intro t
    refine lt_of_le_of_lt (Polynomial.natDegree_prod_le _ _) ?_
    refine lt_of_le_of_lt (Finset.sum_le_sum fun k _ => Polynomial.natDegree_X_sub_C_le (z k)) ?_
    have := Finset.card_le_univ t
    simp only [Finset.sum_const, smul_eq_mul, mul_one, Fintype.card_fin] at this ⊢
    omega
  have hevalQ : ∀ (t : Finset (Fin r)) (x : ℂ),
      (∏ k ∈ t, (Polynomial.X - Polynomial.C (z k))).eval x = ∏ k ∈ t, (x - z k) := by
    intro t x
    rw [Polynomial.eval_prod]
    simp
  -- support
  have hsupp : ∀ i, 0 < w' i → ∃ k, z' i = z k := by
    intro i hi
    have h1 := hkey _ (hdeg Finset.univ)
    rw [Finset.sum_eq_zero fun k _ => by
      rw [hevalQ, Finset.prod_eq_zero (Finset.mem_univ k) (sub_self _), norm_zero]; ring] at h1
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ =>
      mul_nonneg (hw' i) (sq_nonneg _)).mp h1.symm i (Finset.mem_univ i)
    have h3 : (∏ k, (z' i - z k)) = 0 := by
      rw [← hevalQ]
      have := (mul_eq_zero.mp h2).resolve_left hi.ne'
      exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp this)
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp h3
    exact ⟨k, sub_eq_zero.mp hk⟩
  refine ⟨hsupp, fun k₀ => ?_⟩
  -- weights through the Lagrange polynomial of `k₀`
  set t := Finset.univ.erase k₀ with ht
  set G := ‖∏ k ∈ t, (z k₀ - z k)‖ ^ 2 with hG
  have hG0 : 0 < G := by
    rw [hG]
    refine pow_pos (norm_pos_iff.mpr (Finset.prod_ne_zero_iff.mpr fun k hk => ?_)) 2
    exact sub_ne_zero.mpr fun h => (Finset.mem_erase.mp hk).1 (hinj h).symm
  have hvan : ∀ k, k ≠ k₀ → ∏ k' ∈ t, (z k - z k') = 0 := fun k hk =>
    Finset.prod_eq_zero (Finset.mem_erase.mpr ⟨hk, Finset.mem_univ k⟩) (sub_self _)
  have h1 := hkey _ (hdeg t)
  simp_rw [hevalQ] at h1
  rw [Finset.sum_eq_single k₀ (fun k _ hk => by rw [hvan k hk, norm_zero]; ring)
    (by simp)] at h1
  have hterm : ∀ i, w' i * ‖∏ k ∈ t, (z' i - z k)‖ ^ 2 =
      if z' i = z k₀ then w' i * G else 0 := by
    intro i
    split_ifs with h
    · rw [h]
    · rcases (hw' i).eq_or_lt with h0 | hpos
      · rw [← h0, zero_mul]
      · obtain ⟨k, hk⟩ := hsupp i hpos
        have hkk : k ≠ k₀ := fun h' => h (by rw [hk, h'])
        rw [hk, hvan k hkk, norm_zero]
        ring
  rw [Finset.sum_congr rfl fun i _ => hterm i, ← Finset.sum_filter, ← Finset.sum_mul] at h1
  exact (mul_right_cancel₀ hG0.ne' h1).symm

/-! ### Nyquist pinning -/

/-- **Nyquist pinning.** Let the first configuration have `r` distinct ordinates per period
`2π/ℓ`. If it agrees with a second weighted on-line periodic configuration on every test
of an aperture `a` with `r < ⌈2a/ℓ⌉`, the second has the same ordinates and weights, and the two
agree on every test of every aperture. -/
theorem onLineShadow_pinning {ℓ : ℝ} (hℓ : 0 < ℓ) {r s : ℕ} (c w : Fin r → ℝ)
    (hc : Function.Injective (shadowNode ℓ c)) (c' w' : Fin s → ℝ)
    (hw' : ∀ i, 0 ≤ w' i) {a : ℝ} (ha : 0 < a) (hr : r < ⌈2 * a / ℓ⌉₊)
    (h : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → tsupport f ⊆ Icc (-a) a →
      onLineShadow ℓ c w f = onLineShadow ℓ c' w' f) :
    (∀ i, 0 < w' i → ∃ k, shadowNode ℓ c' i = shadowNode ℓ c k) ∧
      (∀ k, ∑ i ∈ Finset.univ.filter (fun i => shadowNode ℓ c' i = shadowNode ℓ c k), w' i =
        w k) ∧
      ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
        onLineShadow ℓ c w f = onLineShadow ℓ c' w' f := by
  have hM : ∀ m : ℤ, |m| ≤ r → ∑ k, (w k : ℂ) * shadowNode ℓ c k ^ m =
      ∑ i, (w' i : ℂ) * shadowNode ℓ c' i ^ m := by
    intro m hm
    rw [← shadowMoment_eq_nodes, ← shadowMoment_eq_nodes]
    exact shadowMoment_eq_of_onLineShadow_eq hℓ c w c' w' ha h (by omega)
  obtain ⟨hsupp, hwt⟩ := atomic_pinning _ (norm_shadowNode ℓ c) hc w _
    (norm_shadowNode ℓ c') w' hw' hM
  refine ⟨hsupp, hwt, fun f hf hfc => ?_⟩
  have hall : ∀ m : ℤ, shadowMoment ℓ c w m = shadowMoment ℓ c' w' m := by
    intro m
    rw [shadowMoment_eq_nodes, shadowMoment_eq_nodes]
    have hi : ∀ i, (w' i : ℂ) * shadowNode ℓ c' i ^ m = ∑ k,
        if shadowNode ℓ c' i = shadowNode ℓ c k then (w' i : ℂ) * shadowNode ℓ c k ^ m
        else 0 := by
      intro i
      rcases (hw' i).eq_or_lt with h0 | hpos
      · rw [← h0]
        simp
      · obtain ⟨k₀, hk₀⟩ := hsupp i hpos
        rw [Finset.sum_eq_single k₀ (fun k _ hk => if_neg fun h' => hk (hc (h'.symm.trans hk₀)))
          (by simp), if_pos hk₀, hk₀]
    rw [Finset.sum_congr rfl fun i _ => hi i, Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.sum_filter, ← Finset.sum_mul, ← hwt k]
    push_cast
    rfl
  have h1 := onLineShadow_eq_lagSum hℓ c w hf hfc
  rw [show (∑' m : ℤ, EF.weilTest f f (m * ℓ) * shadowMoment ℓ c w m) =
      ∑' m : ℤ, EF.weilTest f f (m * ℓ) * shadowMoment ℓ c' w' m by simp_rw [hall],
    ← onLineShadow_eq_lagSum hℓ c' w' hf hfc] at h1
  exact_mod_cast h1

/-! ### Sharpness: the crystal and its rotation -/

theorem sum_exp_two_pi_mul_div {r : ℕ} (hr : 0 < r) (m : ℤ) :
    ∑ k : Fin r, cexp (2 * π * I * (k : ℕ) * m / r) = if (r : ℤ) ∣ m then (r : ℂ) else 0 := by
  have hζ := Complex.isPrimitiveRoot_exp r hr.ne'
  set ζ := cexp (2 * π * I / r) with hζdef
  have hterm : ∀ k : Fin r, cexp (2 * π * I * (k : ℕ) * m / r) = (ζ ^ m) ^ (k : ℕ) := by
    intro k
    rw [← zpow_natCast, ← zpow_mul, hζdef, ← Complex.exp_int_mul]
    congr 1
    push_cast
    ring
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun k => (ζ ^ m) ^ k) r]
  split_ifs with hd
  · rw [(hζ.zpow_eq_one_iff_dvd m).mpr hd]
    simp
  · have hne : ζ ^ m ≠ 1 := fun h => hd ((hζ.zpow_eq_one_iff_dvd m).mp h)
    have hpow : (ζ ^ m) ^ r = 1 := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ.pow_eq_one, one_zpow]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div]

/-- The `r`-point crystal at phase `θ`: ordinates `(2πk + θ)/(rℓ)` of unit weight. -/
def crystalOffset (ℓ : ℝ) (r : ℕ) (θ : ℝ) : Fin r → ℝ := fun k => (2 * π * (k : ℕ) + θ) / (r * ℓ)

theorem shadowMoment_crystal {ℓ : ℝ} (hℓ : 0 < ℓ) {r : ℕ} (hr : 0 < r) (θ : ℝ) (m : ℤ) :
    shadowMoment ℓ (crystalOffset ℓ r θ) (fun _ => 1) m =
      if (r : ℤ) ∣ m then (r : ℂ) * cexp (I * θ * m / r) else 0 := by
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hℓc : (ℓ : ℂ) ≠ 0 := by exact_mod_cast hℓ.ne'
  have hk : ∀ k : Fin r, ((1 : ℝ) : ℂ) * cexp (I * (crystalOffset ℓ r θ k : ℝ) * (m * ℓ)) =
      cexp (2 * π * I * (k : ℕ) * m / r) * cexp (I * θ * m / r) := by
    intro k
    rw [Complex.ofReal_one, one_mul, ← Complex.exp_add, crystalOffset]
    congr 1
    push_cast
    field_simp
  rw [shadowMoment, Finset.sum_congr rfl fun k _ => hk k, ← Finset.sum_mul,
    sum_exp_two_pi_mul_div hr]
  split_ifs <;> ring

/-- **Unpinned below Nyquist.** The `r`-point crystal and its rotation by half a step agree on every
test of every aperture `a` with `⌈2a/ℓ⌉ ≤ r`. -/
theorem onLineShadow_crystal_unpinned {ℓ : ℝ} (hℓ : 0 < ℓ) {r : ℕ} (hr : 0 < r) {a : ℝ}
    (ha : ⌈2 * a / ℓ⌉₊ ≤ r) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfs : tsupport f ⊆ Icc (-a) a) :
    onLineShadow ℓ (crystalOffset ℓ r 0) (fun _ => 1) f =
      onLineShadow ℓ (crystalOffset ℓ r π) (fun _ => 1) f := by
  have hfc := hasCompactSupport_of_tsupport_subset_Icc hfs
  have h1 := onLineShadow_eq_lagSum hℓ (crystalOffset ℓ r 0) (fun _ => 1) hf hfc
  have h2 := onLineShadow_eq_lagSum hℓ (crystalOffset ℓ r π) (fun _ => 1) hf hfc
  have hn : 2 * a ≤ r * ℓ := by
    rcases le_or_gt a 0 with h | h
    · have : (0 : ℝ) ≤ r * ℓ := by positivity
      linarith
    · have := Nat.le_ceil (2 * a / ℓ)
      rw [div_le_iff₀ hℓ] at this
      have hc : (⌈2 * a / ℓ⌉₊ : ℝ) ≤ r := by exact_mod_cast ha
      nlinarith
  have hterm : ∀ m : ℤ, EF.weilTest f f (m * ℓ) * shadowMoment ℓ (crystalOffset ℓ r 0)
      (fun _ => 1) m = EF.weilTest f f (m * ℓ) * shadowMoment ℓ (crystalOffset ℓ r π)
      (fun _ => 1) m := by
    intro m
    by_cases hm : |m| < r
    · rw [shadowMoment_crystal hℓ hr, shadowMoment_crystal hℓ hr]
      split_ifs with hd
      · obtain ⟨q, rfl⟩ := hd
        have : q = 0 := by
          by_contra hq
          have : (r : ℤ) ≤ |(r : ℤ) * q| := by
            rw [abs_mul, abs_of_pos (by exact_mod_cast hr)]
            exact le_mul_of_one_le_right (by positivity) (Int.one_le_abs hq)
          omega
        subst this
        simp
      · rfl
    · rw [weilTest_eq_zero_of_two_mul_le hf.continuous hfs, zero_mul, zero_mul]
      push Not at hm
      rw [abs_mul, abs_of_pos hℓ]
      have : (r : ℝ) ≤ |(m : ℝ)| := by rw [← Int.cast_abs]; exact_mod_cast hm
      nlinarith
  rw [tsum_congr hterm, ← h2] at h1
  exact_mod_cast h1

/-- **Pinned above Nyquist.** At every aperture with `⌈2a/ℓ⌉ > r` some test of aperture `a` tells
the crystal from its rotation. -/
theorem exists_onLineShadow_crystal_distinguished {ℓ : ℝ} (hℓ : 0 < ℓ) {r : ℕ} (hr : 0 < r)
    {a : ℝ} (ha : 0 < a) (hra : r < ⌈2 * a / ℓ⌉₊) :
    ∃ f : ℝ → ℂ, ContDiff ℝ 2 f ∧ tsupport f ⊆ Icc (-a) a ∧
      onLineShadow ℓ (crystalOffset ℓ r 0) (fun _ => 1) f ≠
        onLineShadow ℓ (crystalOffset ℓ r π) (fun _ => 1) f := by
  by_contra hcon
  push Not at hcon
  have h := shadowMoment_eq_of_onLineShadow_eq hℓ _ _ _ _ ha hcon (m := r)
    (by rw [abs_of_nonneg (by positivity)]; exact_mod_cast hra)
  rw [shadowMoment_crystal hℓ hr, shadowMoment_crystal hℓ hr, if_pos dvd_rfl, if_pos dvd_rfl]
    at h
  have hrc : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have he : cexp (I * (π : ℝ) * ((r : ℤ) : ℂ) / r) = -1 := by
    rw [show I * (π : ℝ) * ((r : ℤ) : ℂ) / r = π * I by push_cast; field_simp,
      Complex.exp_pi_mul_I]
  rw [he] at h
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, zero_div, Complex.exp_zero, mul_one,
    mul_neg] at h
  have : (2 : ℂ) * r = 0 := by linear_combination h
  exact hrc (by simpa using this)

end GaloisForLFunctions.SquareRootThreshold
