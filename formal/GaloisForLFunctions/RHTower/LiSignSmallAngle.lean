import GaloisForLFunctions.RHTower.LiSignIntersective
import GaloisForLFunctions.RHTower.LiFirstCoefficientsNonneg

/-!
# Li's criterion along polynomials through small Cayley angles

The abstract obstructions of `LiSignIntersective` use Cayley roots spread around the unit circle.
The Cayley roots `v_ρ` of the actual off-line zeros have small arguments: the zero-free band
`γ² ≥ 431/2` gives `|arg v_ρ| ≤ 7/100`. Along `x = Tk + K + x₀` with `T` a common period of the
resonant roots, a resonant root `u` satisfies `u^{P(x)} = u^{P(x₀)} = e^{iθP(x₀)}`, which has
nonnegative real part as soon as `2θ|P(x₀)| ≤ π/2`.

**Theorem** (`riemannHypothesis_iff_eventually_re_xiLiPaired_of_small_value`). If
`P ∈ ℤ[X]` has positive leading coefficient, degree `≥ 1` and a value `|P(x₀)| ≤ 11`, then the
Riemann hypothesis holds iff `Re 2λ_{P(x)} ≥ 0` for all large `x`. This covers the odd numbers
`2x + 1`, `x² + 1` and every arithmetic progression `ax + b` with `|b| ≤ 11`, along which abstract
families can evade (MUST-913/914). So for `ξ` the arithmetic of the zeros, through their height
`|γ| ≥ 14.6`, is enough to remove the abstract obstruction.
-/

open Complex Filter Finset Polynomial

noncomputable section

namespace RHTower

/-! ## The moment argument with a resonant base exponent -/

theorem eventually_neg_le_re_sum_seq_shift {s : ℕ → ℕ → ℕ} {e : ℤ}
    (hres : ∀ T : ℕ, 0 < T → ∀ w : ℂ, w ^ T = 1 → ∀ k, w ^ (s T k) = w ^ e)
    (hweyl : ∀ T : ℕ, 0 < T → ∀ w : ℂ, ‖w‖ = 1 → (∀ n : ℕ, 0 < n → w ^ n ≠ 1) →
      ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ‖∑ k ∈ range N, w ^ (s T k)‖ ≤ δ * N)
    {w : ℂ} (hw : ‖w‖ = 1) {Q : ℕ} (hQ : 0 < Q)
    (hd : w ^ Q = 1 ∨ ∀ n : ℕ, 0 < n → w ^ n ≠ 1) (hpos : 0 ≤ (w ^ e).re) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → -(δ * N) ≤ (∑ k ∈ range N, w ^ (s Q k)).re := by
  rcases hd with h1 | hnr
  · refine ⟨0, fun N _ => ?_⟩
    have hk : ∀ k : ℕ, w ^ (s Q k) = w ^ e := hres Q hQ w h1
    simp only [hk, sum_const, card_range, nsmul_eq_mul]
    rw [Complex.mul_re]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    have : (0 : ℝ) ≤ N := N.cast_nonneg
    nlinarith
  · obtain ⟨N₀, hN₀⟩ := hweyl Q hQ w hw hnr δ hδ
    refine ⟨N₀, fun N hN => ?_⟩
    have h1 := hN₀ N hN
    have h2 := Complex.abs_re_le_norm (∑ k ∈ range N, w ^ (s Q k))
    have h3 := neg_abs_le (∑ k ∈ range N, w ^ (s Q k)).re
    linarith

/-- **Positive density along a family with a resonant base exponent.** -/
theorem exists_card_filter_seq_gt_shift {ι : Type*} [Fintype ι] [Nonempty ι] (idx : ℕ → ℕ → ℕ)
    {e : ℤ} (hres : ∀ T : ℕ, 0 < T → ∀ w : ℂ, w ^ T = 1 → ∀ k, w ^ (idx T k) = w ^ e)
    (hweyl : ∀ T : ℕ, 0 < T → ∀ w : ℂ, ‖w‖ = 1 → (∀ n : ℕ, 0 < n → w ^ n ≠ 1) →
      ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ‖∑ k ∈ range N, w ^ (idx T k)‖ ≤ δ * N)
    (u : ι → ℂ) (m : ι → ℝ) (hu : ∀ i, ‖u i‖ = 1) (hm : ∀ i, 0 < m i)
    (hpos₁ : ∀ i, 0 ≤ (u i ^ e).re) (hpos₂ : ∀ i j, 0 ≤ ((u i * u j) ^ e).re)
    (hpos₃ : ∀ i j, 0 ≤ ((u i * (starRingEnd ℂ) (u j)) ^ e).re) :
    ∃ Q : ℕ, 0 < Q ∧ ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * N ≤ (((range N).filter
        (fun k => ε < ∑ i, m i * (u i ^ (idx Q k)).re)).card : ℝ) := by
  classical
  obtain ⟨Q₁, hQ₁, hd₁⟩ := exists_pow_eq_one_or_not_root u
  obtain ⟨Q₂, hQ₂, hd₂⟩ := exists_pow_eq_one_or_not_root (fun p : ι × ι => u p.1 * u p.2)
  obtain ⟨Q₃, hQ₃, hd₃⟩ :=
    exists_pow_eq_one_or_not_root (fun p : ι × ι => u p.1 * (starRingEnd ℂ) (u p.2))
  set Q : ℕ := Q₁ * Q₂ * Q₃ with hQ
  have hQpos : 0 < Q := Nat.mul_pos (Nat.mul_pos hQ₁ hQ₂) hQ₃
  have e₁ : ∀ i, u i ^ Q = 1 ∨ ∀ n : ℕ, 0 < n → u i ^ n ≠ 1 := fun i =>
    pow_eq_one_or_not_root_of_dvd (hd₁ i) ⟨Q₂ * Q₃, by rw [hQ]; ring⟩
  have e₂ : ∀ p : ι × ι, (u p.1 * u p.2) ^ Q = 1 ∨ ∀ n : ℕ, 0 < n → (u p.1 * u p.2) ^ n ≠ 1 :=
    fun p => pow_eq_one_or_not_root_of_dvd (hd₂ p) ⟨Q₁ * Q₃, by rw [hQ]; ring⟩
  have e₃ : ∀ p : ι × ι, (u p.1 * (starRingEnd ℂ) (u p.2)) ^ Q = 1 ∨
      ∀ n : ℕ, 0 < n → (u p.1 * (starRingEnd ℂ) (u p.2)) ^ n ≠ 1 :=
    fun p => pow_eq_one_or_not_root_of_dvd (hd₃ p) ⟨Q₁ * Q₂, by rw [hQ]; ring⟩
  have hu₂ : ∀ p : ι × ι, ‖u p.1 * u p.2‖ = 1 := fun p => by
    rw [norm_mul, hu, hu, one_mul]
  have hu₃ : ∀ p : ι × ι, ‖u p.1 * (starRingEnd ℂ) (u p.2)‖ = 1 := fun p => by
    rw [norm_mul, Complex.norm_conj, hu, hu, one_mul]
  set f : ℕ → ℝ := fun k => ∑ i, m i * (u i ^ (idx Q k)).re with hf
  set B : ℝ := ∑ i, m i with hBdef
  have hB0 : 0 < B := Finset.sum_pos (fun i _ => hm i) Finset.univ_nonempty
  have hfB : ∀ k, |f k| ≤ B := by
    intro k
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_of_pos (hm i)]
    have h1 := Complex.abs_re_le_norm (u i ^ (idx Q k))
    rw [norm_pow, hu, one_pow] at h1
    nlinarith [hm i]
  set s : ℝ := (∑ i, m i ^ 2) / 2 with hsdef
  have hs0 : 0 < s := by
    have : 0 < ∑ i, m i ^ 2 := Finset.sum_pos (fun i _ => by have := hm i; positivity)
      Finset.univ_nonempty
    positivity
  have hmean : ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → -(δ * N) ≤ ∑ k ∈ range N, f k := by
    intro δ hδ
    have hex : ∀ i, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        -(δ / B * N) ≤ (∑ k ∈ range N, u i ^ (idx Q k)).re := fun i =>
      eventually_neg_le_re_sum_seq_shift hres hweyl (hu i) hQpos (e₁ i) (hpos₁ i) (by positivity)
    choose N₀ hN₀ using hex
    refine ⟨Finset.univ.sup N₀, fun N hN => ?_⟩
    have hswap : ∑ k ∈ range N, f k = ∑ i, m i * (∑ k ∈ range N, u i ^ (idx Q k)).re := by
      simp only [hf]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.re_sum, Finset.mul_sum]
    rw [hswap]
    have hle : ∀ i ∈ (Finset.univ : Finset ι),
        m i * (-(δ / B * N)) ≤ m i * (∑ k ∈ range N, u i ^ (idx Q k)).re := fun i _ =>
      mul_le_mul_of_nonneg_left
        (hN₀ i N (le_trans (Finset.le_sup (Finset.mem_univ i)) hN)) (hm i).le
    have hsum := Finset.sum_le_sum hle
    have heq : ∑ i, m i * (-(δ / B * N)) = -(δ * N) := by
      rw [← Finset.sum_mul, ← hBdef]; field_simp
    linarith
  have hsq : ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (s - δ) * N ≤ ∑ k ∈ range N, f k ^ 2 := by
    intro δ hδ
    set δ' : ℝ := δ / (B ^ 2 + 1) with hδ'
    have hδ'0 : 0 < δ' := by positivity
    have hex₂ : ∀ p : ι × ι, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        -(δ' * N) ≤ (∑ k ∈ range N, (u p.1 * u p.2) ^ (idx Q k)).re := fun p =>
      eventually_neg_le_re_sum_seq_shift hres hweyl (hu₂ p) hQpos (e₂ p) (hpos₂ p.1 p.2) hδ'0
    have hex₃ : ∀ p : ι × ι, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        -(δ' * N) ≤ (∑ k ∈ range N, (u p.1 * (starRingEnd ℂ) (u p.2)) ^ (idx Q k)).re :=
      fun p => eventually_neg_le_re_sum_seq_shift hres hweyl (hu₃ p) hQpos (e₃ p) (hpos₃ p.1 p.2) hδ'0
    choose N₂ hN₂ using hex₂
    choose N₃ hN₃ using hex₃
    refine ⟨max (Finset.univ.sup N₂) (Finset.univ.sup N₃), fun N hN => ?_⟩
    have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
    -- the double-sum form of the second moment
    have hswap : ∑ k ∈ range N, f k ^ 2 = ∑ i, ∑ j, m i * m j / 2 *
        ((∑ k ∈ range N, (u i * u j) ^ (idx Q k)).re +
          (∑ k ∈ range N, (u i * (starRingEnd ℂ) (u j)) ^ (idx Q k)).re) := by
      simp only [hf, sq_sum_mul_re_pow_eq]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.re_sum, Complex.re_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    rw [hswap]
    -- each pair is at least `[i = j]N − 2δ'N`
    have hpair : ∀ i j, (if i = j then (N : ℝ) else 0) - 2 * δ' * N ≤
        (∑ k ∈ range N, (u i * u j) ^ (idx Q k)).re +
          (∑ k ∈ range N, (u i * (starRingEnd ℂ) (u j)) ^ (idx Q k)).re := by
      intro i j
      have h2 := hN₂ (i, j) N (le_trans (Finset.le_sup (Finset.mem_univ (i, j)))
        (le_trans (le_max_left _ _) hN))
      have h3 := hN₃ (i, j) N (le_trans (Finset.le_sup (Finset.mem_univ (i, j)))
        (le_trans (le_max_right _ _) hN))
      simp only at h2 h3
      have hδN : 0 ≤ δ' * N := mul_nonneg hδ'0.le hN0
      split_ifs with hij
      · subst hij
        have hone : u i * (starRingEnd ℂ) (u i) = 1 := by
          rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hu]; simp
        rw [hone]
        simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one, natCast_re]
        linarith
      · linarith
    have hlow : ∑ i, ∑ j, m i * m j / 2 * ((if i = j then (N : ℝ) else 0) - 2 * δ' * N) ≤
        ∑ i, ∑ j, m i * m j / 2 *
          ((∑ k ∈ range N, (u i * u j) ^ (idx Q k)).re +
            (∑ k ∈ range N, (u i * (starRingEnd ℂ) (u j)) ^ (idx Q k)).re) :=
      Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (hpair i j) (by have := hm i; have := hm j; positivity)
    have heval : ∑ i, ∑ j, m i * m j / 2 * ((if i = j then (N : ℝ) else 0) - 2 * δ' * N) =
        s * N - δ' * B ^ 2 * N := by
      have h1 : ∀ i, ∑ j, m i * m j / 2 * ((if i = j then (N : ℝ) else 0) - 2 * δ' * N) =
          m i ^ 2 / 2 * N - m i * B * δ' * N := by
        intro i
        simp only [mul_sub, Finset.sum_sub_distrib, mul_ite, mul_zero, Finset.sum_ite_eq,
          Finset.mem_univ, if_true]
        rw [← Finset.sum_mul, ← Finset.sum_div, ← Finset.mul_sum, ← hBdef]
        ring
      have e1 : ∑ i, m i ^ 2 / 2 * (N : ℝ) = s * N := by
        rw [hsdef, Finset.sum_div, Finset.sum_mul]
      have e2 : ∑ i, m i * B * δ' * (N : ℝ) = δ' * B ^ 2 * N := by
        rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.sum_mul, ← hBdef]; ring
      rw [Finset.sum_congr rfl fun i _ => h1 i, Finset.sum_sub_distrib, e1, e2]
    have hδB : δ' * B ^ 2 ≤ δ := by
      rw [hδ', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    rw [heval] at hlow
    nlinarith
  obtain ⟨ε, c, hε, hc, N₀, hcount⟩ := exists_card_filter_gt_of_mean_sq hB0 hfB hs0 hmean hsq
  exact ⟨Q, hQpos, ε, c, hε, hc, N₀, hcount⟩

/-! ## Unit complex numbers as exponentials -/

theorem eq_exp_arg_mul_I_of_norm_eq_one {u : ℂ} (hu : ‖u‖ = 1) :
    u = Complex.exp ((Complex.arg u : ℂ) * I) := by
  have := Complex.norm_mul_exp_arg_mul_I u
  rw [hu, Complex.ofReal_one, one_mul] at this
  exact this.symm

theorem re_zpow_exp_mul_I (a : ℝ) (e : ℤ) :
    ((Complex.exp ((a : ℂ) * I)) ^ e).re = Real.cos (e * a) := by
  rw [← Complex.exp_int_mul, ← mul_assoc]
  have : ((e : ℂ) * (a : ℂ)) = (((e : ℝ) * a : ℝ) : ℂ) := by push_cast; ring
  rw [this, Complex.exp_ofReal_mul_I_re]

theorem cos_nonneg_of_abs_le_pi_div_two {x : ℝ} (hx : |x| ≤ Real.pi / 2) : 0 ≤ Real.cos x :=
  Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [neg_abs_le x]) (le_trans (le_abs_self x) hx)

/-! ## Shifted polynomial index families -/

theorem exists_shift_nonneg {P : ℤ[X]} (hlc : 0 < P.leadingCoeff) (hdeg : 1 ≤ P.natDegree)
    (x₀ : ℤ) : ∃ K : ℕ, ∀ T : ℕ, 0 < T → ∀ k : ℕ, 0 ≤ P.eval ((T : ℤ) * (k + K) + x₀) := by
  obtain ⟨X₁, hX₁⟩ := eventually_le_eval_of_leadingCoeff_pos hlc hdeg 0
  refine ⟨X₁ + x₀.natAbs, fun T hT k => hX₁ _ ?_⟩
  have hT1 : (1 : ℤ) ≤ T := by exact_mod_cast hT
  have hk : (0 : ℤ) ≤ k := Nat.cast_nonneg k
  have habs : -|x₀| ≤ x₀ := neg_abs_le x₀
  have hX0 : (0 : ℤ) ≤ X₁ := Nat.cast_nonneg _
  have hA0 : (0 : ℤ) ≤ |x₀| := abs_nonneg _
  push_cast
  have hprod : 0 ≤ ((T : ℤ) - 1) * (k + (X₁ + |x₀|)) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

/-- **Small angles defeat the arithmetic obstruction, abstract form.** If every member of the
family outside the unit circle has `|arg v| ≤ θ`, and `P(x₀)` satisfies `2θ|P(x₀)| ≤ π/2`, then the
paired Li sums at `P(x)` are negative for infinitely many `x`. -/
theorem frequently_shift_re_tsum_liTerm_neg {P : ℤ[X]} (hlc : 0 < P.leadingCoeff)
    (hdeg : 1 ≤ P.natDegree) {x₀ : ℤ} {θ : ℝ} (hθ : 0 ≤ θ)
    (hsmall : 2 * θ * |((P.eval x₀ : ℤ) : ℝ)| ≤ Real.pi / 2)
    {ι : Type*} {v : ι → ℂ} {m : ι → ℝ} {M : ℝ}
    (hm : ∀ i, 1 ≤ m i) (hv : ∀ i, 1 ≤ ‖v i‖) (hM : ∀ i, ‖v i‖ ≤ M)
    (hs : Summable fun i => m i * ‖v i - 1‖ ^ (2 : ℕ))
    (hang : ∀ i, 1 < ‖v i‖ → |Complex.arg (v i)| ≤ θ) {i₀ : ι} (hlt : 1 < ‖v i₀‖) :
    ∃ᶠ x : ℕ in atTop, ∑' i, m i * (liTerm (v i) (P.eval (x : ℤ)).toNat).re < 0 := by
  classical
  obtain ⟨K, hK⟩ := exists_shift_nonneg hlc hdeg x₀
  set s : ℕ → ℕ → ℕ := fun T k =>
    if 0 < T then (P.eval ((T : ℤ) * (k + K) + x₀)).toNat else 0 with hsdef
  have hseval : ∀ T, 0 < T → ∀ k : ℕ, ((s T k : ℕ) : ℤ) = P.eval ((T : ℤ) * (k + K) + x₀) := by
    intro T hT k
    simp only [hsdef, if_pos hT]
    exact Int.toNat_of_nonneg (hK T hT k)
  have hres : ∀ T : ℕ, 0 < T → ∀ w : ℂ, w ^ T = 1 → ∀ k, w ^ (s T k) = w ^ (P.eval x₀) := by
    intro T hT w hwT k
    have hw0 : w ≠ 0 := by
      intro h; rw [h, zero_pow hT.ne'] at hwT; exact zero_ne_one hwT
    have hdvd : (T : ℤ) ∣ P.eval ((T : ℤ) * (k + K) + x₀) - P.eval x₀ := by
      have h1 := sub_dvd_eval_sub ((T : ℤ) * (k + K) + x₀) x₀ P
      have h2 : (T : ℤ) ∣ ((T : ℤ) * (k + K) + x₀) - x₀ := ⟨k + K, by ring⟩
      exact dvd_trans h2 h1
    obtain ⟨q, hq⟩ := hdvd
    rw [← zpow_natCast, hseval T hT k,
      show P.eval ((T : ℤ) * (k + K) + x₀) = P.eval x₀ + (T : ℤ) * q by linarith,
      zpow_add₀ hw0, zpow_mul, zpow_natCast, hwT, one_zpow, mul_one]
  have hweyl : ∀ T : ℕ, 0 < T → ∀ w : ℂ, ‖w‖ = 1 → (∀ n : ℕ, 0 < n → w ^ n ≠ 1) →
      ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ‖∑ k ∈ range N, w ^ (s T k)‖ ≤ δ * N := by
    intro T hT w hw hroot δ hδ
    have hTz : (T : ℤ) ≠ 0 := by exact_mod_cast hT.ne'
    obtain ⟨N₀, hN₀⟩ := eventually_norm_sum_zpow_le P.natDegree hdeg
      (constDiffPhase_comp_linear hdeg (c := (T : ℤ) * K + x₀) hTz) hw hroot hδ
    refine ⟨N₀, fun N hN => ?_⟩
    have e : ∀ k : ℕ, w ^ (s T k) =
        w ^ ((P.comp (C (T : ℤ) * X + C ((T : ℤ) * K + x₀))).eval (k : ℤ)) := by
      intro k
      rw [eval_comp_linear, ← zpow_natCast, hseval T hT k]
      congr 2
      ring
    rw [Finset.sum_congr rfl fun k _ => e k]
    exact hN₀ N hN
  obtain ⟨D, R, hDne, hR1, hDnorm, hdec⟩ := abs_re_tsum_liTerm_add_dominant_le hm hv hM hs hlt
  have hR0 : (0 : ℝ) < R := by linarith
  haveI : Nonempty {x // x ∈ D} := ⟨⟨hDne.choose, hDne.choose_spec⟩⟩
  set u : {x // x ∈ D} → ℂ := fun i => v i / R with hudef
  have hunit : ∀ i, ‖u i‖ = 1 := by
    intro i
    rw [hudef]; simp only
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0, (hDnorm i).mp i.2,
      div_self hR0.ne']
  have hargu : ∀ i, |Complex.arg (u i)| ≤ θ := by
    intro i
    have h1 : u i = ((R⁻¹ : ℝ) : ℂ) * v i := by
      rw [hudef]; simp only; rw [div_eq_inv_mul]; push_cast; ring
    rw [h1, Complex.arg_real_mul _ (inv_pos.mpr hR0)]
    exact hang i (by rw [(hDnorm i).mp i.2]; exact hR1)
  set e : ℤ := P.eval x₀ with he
  have hθe : ∀ a : ℝ, |a| ≤ 2 * θ → |(e : ℝ) * a| ≤ Real.pi / 2 := by
    intro a ha
    rw [abs_mul]
    calc |(e : ℝ)| * |a| ≤ |(e : ℝ)| * (2 * θ) := by gcongr
      _ = 2 * θ * |(e : ℝ)| := by ring
      _ ≤ Real.pi / 2 := hsmall
  have hexp : ∀ i, u i = Complex.exp ((Complex.arg (u i) : ℂ) * I) := fun i =>
    eq_exp_arg_mul_I_of_norm_eq_one (hunit i)
  have hpos₁ : ∀ i, 0 ≤ (u i ^ e).re := by
    intro i
    rw [hexp i, re_zpow_exp_mul_I]
    exact cos_nonneg_of_abs_le_pi_div_two (hθe _ (by linarith [hargu i, abs_nonneg (Complex.arg (u i))]))
  have hpos₂ : ∀ i j, 0 ≤ ((u i * u j) ^ e).re := by
    intro i j
    rw [hexp i, hexp j, ← Complex.exp_add,
      show (Complex.arg (u i) : ℂ) * I + (Complex.arg (u j) : ℂ) * I =
        ((Complex.arg (u i) + Complex.arg (u j) : ℝ) : ℂ) * I by push_cast; ring,
      re_zpow_exp_mul_I]
    refine cos_nonneg_of_abs_le_pi_div_two (hθe _ ?_)
    calc |Complex.arg (u i) + Complex.arg (u j)| ≤ |Complex.arg (u i)| + |Complex.arg (u j)| :=
          abs_add_le _ _
      _ ≤ 2 * θ := by linarith [hargu i, hargu j]
  have hpos₃ : ∀ i j, 0 ≤ ((u i * (starRingEnd ℂ) (u j)) ^ e).re := by
    intro i j
    have hc : (starRingEnd ℂ) (u j) = Complex.exp (((-Complex.arg (u j) : ℝ) : ℂ) * I) := by
      conv_lhs => rw [hexp j]
      rw [← Complex.exp_conj]
      congr 1
      simp [Complex.conj_ofReal]
    rw [hc, hexp i, ← Complex.exp_add,
      show (Complex.arg (u i) : ℂ) * I + ((-Complex.arg (u j) : ℝ) : ℂ) * I =
        ((Complex.arg (u i) - Complex.arg (u j) : ℝ) : ℂ) * I by push_cast; ring,
      re_zpow_exp_mul_I]
    refine cos_nonneg_of_abs_le_pi_div_two (hθe _ ?_)
    calc |Complex.arg (u i) - Complex.arg (u j)| ≤ |Complex.arg (u i)| + |Complex.arg (u j)| :=
          abs_sub _ _
      _ ≤ 2 * θ := by linarith [hargu i, hargu j]
  obtain ⟨T, hT, ε, cc, hε, hcc, N₀, hcount⟩ :=
    exists_card_filter_seq_gt_shift s hres hweyl u (fun i => m i) hunit
      (fun i => by linarith [hm i]) hpos₁ hpos₂ hpos₃
  obtain ⟨N₁, hN₁⟩ := hdec (ε / 2) (by linarith)
  have hf : ∀ n, ∑ i : {x // x ∈ D}, m i * (u i ^ n).re = ∑ i ∈ D, m i * ((v i / R) ^ n).re :=
    fun n => Finset.sum_coe_sort D (fun i => m i * ((v i / R) ^ n).re)
  obtain ⟨Y, hY⟩ := eventually_le_eval_of_leadingCoeff_pos hlc hdeg (N₁ : ℤ)
  rw [Filter.frequently_atTop]
  intro y₀
  set A : ℕ := y₀ + Y + x₀.natAbs with hA
  obtain ⟨N, hN⟩ := exists_nat_gt (((A : ℝ) + 1) / cc + N₀)
  have hNN₀ : N₀ ≤ N := by
    have : (N₀ : ℝ) < N := by
      have : (0 : ℝ) ≤ ((A : ℝ) + 1) / cc := by positivity
      linarith
    exact_mod_cast this.le
  have h1 := hcount N hNN₀
  have hbig : A < ((range N).filter
      (fun k => ε < ∑ i : {x // x ∈ D}, m i * (u i ^ (s T k)).re)).card := by
    have h2 : (A : ℝ) + 1 < cc * N := by
      have : ((A : ℝ) + 1) / cc < N := by
        have : (0 : ℝ) ≤ (N₀ : ℝ) := Nat.cast_nonneg _
        linarith
      rwa [div_lt_iff₀ hcc, mul_comm] at this
    have : (A : ℝ) < (((range N).filter
        (fun k => ε < ∑ i : {x // x ∈ D}, m i * (u i ^ (s T k)).re)).card : ℝ) := by linarith
    exact_mod_cast this
  obtain ⟨k, hk, hkA⟩ : ∃ k ∈ (range N).filter
      (fun k => ε < ∑ i : {x // x ∈ D}, m i * (u i ^ (s T k)).re), A ≤ k := by
    by_contra hno
    push Not at hno
    have hsub : (range N).filter (fun k => ε < ∑ i : {x // x ∈ D}, m i * (u i ^ (s T k)).re)
        ⊆ range A := fun k hk => mem_range.mpr (hno k hk)
    have := card_le_card hsub
    rw [card_range] at this
    omega
  have hP' := (mem_filter.mp hk).2
  have hT1 : (1 : ℤ) ≤ T := by exact_mod_cast hT
  have hk0 : (0 : ℤ) ≤ k := Nat.cast_nonneg k
  have hK0 : (0 : ℤ) ≤ K := Nat.cast_nonneg K
  have hkA' : (A : ℤ) ≤ k := by exact_mod_cast hkA
  have hxabs : -(x₀.natAbs : ℤ) ≤ x₀ := by rw [Int.natCast_natAbs]; exact neg_abs_le x₀
  have harg : ((y₀ + Y : ℕ) : ℤ) ≤ (T : ℤ) * (k + K) + x₀ := by
    have : (A : ℤ) = ((y₀ + Y : ℕ) : ℤ) + (x₀.natAbs : ℤ) := by rw [hA]; push_cast; ring
    nlinarith
  set x : ℕ := ((T : ℤ) * (k + K) + x₀).toNat with hxdef
  have hx : (x : ℤ) = (T : ℤ) * (k + K) + x₀ :=
    Int.toNat_of_nonneg (le_trans (by positivity) harg)
  refine ⟨x, ?_, ?_⟩
  · have : ((y₀ : ℕ) : ℤ) ≤ (x : ℤ) := by rw [hx]; push_cast at harg; linarith
    exact_mod_cast this
  · have hidx_eq : (P.eval (x : ℤ)).toNat = s T k := by
      rw [hx]; simp [hsdef, if_pos hT]
    rw [hidx_eq]
    have hn : N₁ ≤ s T k := by
      have h2 := hY ((T : ℤ) * (k + K) + x₀) (by push_cast at harg; linarith)
      rw [← hseval T hT k] at h2
      exact_mod_cast h2
    have hd := hN₁ _ hn
    rw [hf] at hP'
    have hRn : (0 : ℝ) < R ^ (s T k) := pow_pos hR0 _
    have h2 := (abs_le.mp hd).2
    have h3 := mul_pos hRn (sub_pos.mpr hP')
    nlinarith

/-! ## The Cayley roots of `ξ` have small arguments -/

/-- **Off-line Cayley roots of `ξ` have argument at most `7/100`.** -/
theorem abs_arg_xiRootV_le_of_one_lt (ρ : XiDivisorSupport) (h : 1 < ‖xiRootV (ρ : ℂ)‖) :
    |Complex.arg (xiRootV (ρ : ℂ))| ≤ 7 / 100 := by
  have hstrip := xi_divisor_support_re_mem_open_unit ρ
  have him := xi_divisor_support_im_ne_zero ρ
  have hne0 : (ρ : ℂ) ≠ 0 := by intro h0; rw [h0] at him; simp at him
  have hne1 : (ρ : ℂ) ≠ 1 := by intro h1; rw [h1] at him; simp at him
  have hoff : (ρ : ℂ).re ≠ 1 / 2 := by
    intro hre
    have hw1 : ‖xiRootW (ρ : ℂ)‖ = 1 := (norm_xiRootW_eq_one_iff hne0).mpr hre
    rw [norm_xiRootV hne0 hne1, hw1, inv_one, max_self] at h
    exact lt_irrefl _ h
  have hγ := im_sq_ge_of_xi_eq_zero_of_re_ne_half (xi_eq_zero_of_mem_divisor_support ρ) hoff
  have hθ := abs_arg_xiRootW_le hstrip.1 hstrip.2 hγ
  have hbound : |(ρ : ℂ).im| / ((ρ : ℂ).im ^ 2 - 1 / 4) ≤ 7 / 100 := by
    set g := |(ρ : ℂ).im| with hg
    have hg2 : g ^ 2 = (ρ : ℂ).im ^ 2 := sq_abs _
    have hg0 : 0 ≤ g := abs_nonneg _
    have hgl : 1467 / 100 ≤ g := by nlinarith
    have hden : 0 < (ρ : ℂ).im ^ 2 - 1 / 4 := by linarith
    rw [div_le_iff₀ hden, ← hg2]
    nlinarith
  have hw : |Complex.arg (xiRootW (ρ : ℂ))| ≤ 7 / 100 := le_trans hθ hbound
  unfold xiRootV
  split_ifs
  · exact hw
  · rw [Complex.arg_inv]
    have hpi : Complex.arg (xiRootW (ρ : ℂ)) ≠ Real.pi := by
      intro hπ
      rw [hπ] at hw
      have := Real.pi_gt_three
      rw [abs_of_pos (by linarith)] at hw
      linarith
    rw [if_neg hpi, abs_neg]
    exact hw

/-- **Li's criterion along any polynomial with a small value.** If `P ∈ ℤ[X]` has positive leading
coefficient, degree `≥ 1` and `|P(x₀)| ≤ 11` for some integer `x₀`, then the Riemann hypothesis
holds iff `Re 2λ_{P(x)} ≥ 0` for all large `x`. -/
theorem riemannHypothesis_iff_eventually_re_xiLiPaired_of_small_value {P : ℤ[X]}
    (hlc : 0 < P.leadingCoeff) (hdeg : 1 ≤ P.natDegree) {x₀ : ℤ} (hx₀ : |P.eval x₀| ≤ 11) :
    RiemannHypothesis ↔ ∀ᶠ x : ℕ in atTop, 0 ≤ (xiLiPaired (P.eval (x : ℤ)).toNat).re := by
  constructor
  · intro hRH
    exact Filter.Eventually.of_forall fun x => re_xiLiPaired_nonneg_of_rh hRH _
  · intro h
    by_contra hRH
    obtain ⟨M, hmult, hvnorm, hvM, hsum, _, hbad⟩ := xiLi_family_facts
    obtain ⟨ρ₀, hρ₀⟩ := hbad hRH
    have hsmall : 2 * (7 / 100 : ℝ) * |((P.eval x₀ : ℤ) : ℝ)| ≤ Real.pi / 2 := by
      have h1 : |((P.eval x₀ : ℤ) : ℝ)| ≤ 11 := by exact_mod_cast hx₀
      have := Real.pi_gt_d2
      nlinarith [abs_nonneg ((P.eval x₀ : ℤ) : ℝ)]
    have hfreq := frequently_shift_re_tsum_liTerm_neg hlc hdeg (x₀ := x₀) (by norm_num) hsmall
      hmult hvnorm hvM hsum (fun ρ hρ => abs_arg_xiRootV_le_of_one_lt ρ hρ) hρ₀
    obtain ⟨x, hx1, hx2⟩ := (hfreq.and_eventually h).exists
    rw [← re_xiLiPaired_eq_tsum_mult] at hx1
    linarith

/-- **Li's criterion along the odd numbers.** The Riemann hypothesis holds iff
`Re 2λ_{2x+1} ≥ 0` for all large `x`. -/
theorem riemannHypothesis_iff_eventually_re_xiLiPaired_odd :
    RiemannHypothesis ↔ ∀ᶠ x : ℕ in atTop, 0 ≤ (xiLiPaired (2 * x + 1)).re := by
  have hlc : 0 < (C (2 : ℤ) * X + C 1 : ℤ[X]).leadingCoeff := by
    rw [leadingCoeff_linear (by norm_num)]; norm_num
  have hdeg : 1 ≤ (C (2 : ℤ) * X + C 1 : ℤ[X]).natDegree := by
    rw [natDegree_linear (by norm_num)]
  have h := riemannHypothesis_iff_eventually_re_xiLiPaired_of_small_value hlc hdeg (x₀ := 0)
    (by simp)
  have e : ∀ x : ℕ, ((C (2 : ℤ) * X + C 1 : ℤ[X]).eval (x : ℤ)).toNat = 2 * x + 1 := by
    intro x
    simp only [eval_add, eval_mul, eval_C, eval_X]
    omega
  simp only [e] at h
  exact h

/-- **Li's criterion along `x² + 1`**, a non-intersective polynomial (no root modulo `3`). -/
theorem riemannHypothesis_iff_eventually_re_xiLiPaired_sq_add_one :
    RiemannHypothesis ↔ ∀ᶠ x : ℕ in atTop, 0 ≤ (xiLiPaired (x ^ 2 + 1)).re := by
  have hP : (X ^ 2 + C 1 : ℤ[X]).natDegree = 2 := by
    rw [natDegree_add_C, natDegree_X_pow]
  have hlc : 0 < (X ^ 2 + C 1 : ℤ[X]).leadingCoeff := by
    rw [leadingCoeff_X_pow_add_C (by norm_num)]; norm_num
  have hdeg : 1 ≤ (X ^ 2 + C 1 : ℤ[X]).natDegree := by rw [hP]; norm_num
  have h := riemannHypothesis_iff_eventually_re_xiLiPaired_of_small_value hlc hdeg (x₀ := 0)
    (by simp)
  have e : ∀ x : ℕ, ((X ^ 2 + C 1 : ℤ[X]).eval (x : ℤ)).toNat = x ^ 2 + 1 := by
    intro x
    simp only [eval_add, eval_pow, eval_C, eval_X]
    have : ((x : ℤ)) ^ 2 + 1 = ((x ^ 2 + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  simp only [e] at h
  exact h

end RHTower

end
