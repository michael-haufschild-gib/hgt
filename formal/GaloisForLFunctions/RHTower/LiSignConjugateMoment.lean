import GaloisForLFunctions.RHTower.LiSignProgressions
import GaloisForLFunctions.RHTower.RiemannVonMangoldt

/-!
# Li's criterion along polynomials: the conjugate second moment

`LiSignSmallAngle` asks the resonant products `u_iu_j` and `u_iū_j` of the dominant unit Cayley
directions to have nonnegative real part at the base exponent `e`. Products have twice the angle, so
the condition is `2θ|e| ≤ π/2`. For a family closed under conjugation the products are not needed.

* `(u_iū_j)^Q = 1 ⟺ u_i^Q = u_j^Q`, so the `u_iū_j` part of the second moment is a sum over the
  fibres of `i ↦ u_i^Q` and is at least `Σ_i (m_i Re u_i^e)²` when every `Re u_i^e ≥ 0`
  (`sum_mul_resonantRe_conj_ge`).
* The involution `u_{σi} = ū_i` carries the `u_iu_j` part onto the `u_iū_j` part.

Hence `Re u_i^e > 0` for every dominant direction suffices (`exists_card_filter_seq_gt_conj`), and for
directions of argument at most `θ` this is `θ|e| < π/2`.

**Consequences for `ξ`** (`θ = 7/100`). Li's criterion is decided along every polynomial with a value
`|P(x₀)| ≤ 22` (`riemannHypothesis_iff_eventually_re_xiLiPaired_of_value_le`), in particular along
every arithmetic progression of modulus `a ≤ 45` and any residue
(`riemannHypothesis_iff_eventually_re_xiLiPaired_progression_le_45`).

**Sharpness.** The pair `R e^{±iπ/(2c)}` has paired Li sum exactly `4` at every index `2ck + c`
(`halfTurnPair_re_liTerm_eq_four`). For `c = 23` its argument `π/46` is below `7/100`, so the
small-angle mechanism alone cannot decide the progression `46k + 23`: modulus `45` is the exact reach of
the band bound for all residues.
-/

open Complex Filter Finset Polynomial

noncomputable section

namespace RHTower

/-! ## Fibre sums of squares -/

/-- `Σ_{i,j} [w_i = w_j] y_i y_j = Σ_c (Σ_{w_i = c} y_i)² ≥ 0`. -/
theorem sum_sum_ite_eq_mul_nonneg {ι α : Type*} [Fintype ι] [DecidableEq α] (w : ι → α)
    (y : ι → ℝ) : 0 ≤ ∑ i, ∑ j, if w i = w j then y i * y j else 0 := by
  classical
  have key : ∀ i, (∑ j, if w i = w j then y i * y j else 0) =
      y i * ∑ j ∈ univ.filter (fun j => w j = w i), y j := by
    intro i
    rw [Finset.mul_sum, Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases h : w i = w j
    · rw [if_pos h, if_pos h.symm]
    · rw [if_neg h, if_neg (Ne.symm h)]
  rw [Finset.sum_congr rfl fun i _ => key i,
    ← Finset.sum_fiberwise_of_maps_to (t := univ.image w) (g := w)
      (fun i _ => Finset.mem_image_of_mem w (Finset.mem_univ i))]
  refine Finset.sum_nonneg fun c _ => ?_
  have hc : ∑ i ∈ univ with w i = c, y i * ∑ j ∈ univ.filter (fun j => w j = w i), y j =
      (∑ i ∈ univ with w i = c, y i) ^ 2 := by
    rw [sq, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [(Finset.mem_filter.mp hi).2]
  rw [hc]
  exact sq_nonneg _

/-- For `x ≥ 0`, `Σ_{i,j} [w_i = w_j] x_i x_j ≥ Σ_i x_i²`. -/
theorem sum_sq_le_sum_sum_ite_eq_mul {ι α : Type*} [Fintype ι] [DecidableEq α] (w : ι → α)
    {x : ι → ℝ} (hx : ∀ i, 0 ≤ x i) :
    ∑ i, x i ^ 2 ≤ ∑ i, ∑ j, if w i = w j then x i * x j else 0 := by
  refine Finset.sum_le_sum fun i _ => ?_
  have h := Finset.single_le_sum (f := fun j => if w i = w j then x i * x j else 0)
    (s := univ) (fun j _ => by split_ifs <;> [exact mul_nonneg (hx i) (hx j); exact le_rfl])
    (Finset.mem_univ i)
  simp only at h
  rw [sq]
  exact h

/-! ## The resonant real part -/

/-- The part of `Re w^e` that survives averaging along a residue class modulo `Q`. -/
def resonantRe (Q : ℕ) (e : ℤ) (w : ℂ) : ℝ := if w ^ Q = 1 then (w ^ e).re else 0

theorem pow_mul_conj_eq_one_iff {a b : ℂ} (hb : ‖b‖ = 1) (Q : ℕ) :
    (a * (starRingEnd ℂ) b) ^ Q = 1 ↔ a ^ Q = b ^ Q := by
  have hb0 : b ^ Q ≠ 0 := pow_ne_zero _ (ne_zero_of_norm_eq_one hb)
  rw [conj_eq_inv_of_unit_norm hb, mul_pow, inv_pow, mul_inv_eq_one₀ hb0]

theorem mul_mul_resonantRe_conj {a b : ℂ} (hb : ‖b‖ = 1) (Q : ℕ) (e : ℤ)
    (ma mb : ℝ) :
    ma * mb * resonantRe Q e (a * (starRingEnd ℂ) b) =
      (if a ^ Q = b ^ Q then (ma * (a ^ e).re) * (mb * (b ^ e).re) else 0) +
        (if a ^ Q = b ^ Q then (ma * (a ^ e).im) * (mb * (b ^ e).im) else 0) := by
  unfold resonantRe
  by_cases h : a ^ Q = b ^ Q
  · rw [if_pos ((pow_mul_conj_eq_one_iff hb Q).mpr h), if_pos h, if_pos h, mul_zpow,
      ← map_zpow₀, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  · rw [if_neg (fun h' => h ((pow_mul_conj_eq_one_iff hb Q).mp h')), if_neg h, if_neg h]
    ring

/-- **The conjugate part of the second moment is a fibre sum of squares.** -/
theorem sum_mul_resonantRe_conj_ge {ι : Type*} [Fintype ι] {u : ι → ℂ} {m : ι → ℝ}
    (hu : ∀ i, ‖u i‖ = 1) (hm : ∀ i, 0 ≤ m i) (Q : ℕ) (e : ℤ) (hpos : ∀ i, 0 ≤ (u i ^ e).re) :
    ∑ i, (m i * (u i ^ e).re) ^ 2 ≤
      ∑ i, ∑ j, m i * m j * resonantRe Q e (u i * (starRingEnd ℂ) (u j)) := by
  classical
  have hij : ∀ i j, m i * m j * resonantRe Q e (u i * (starRingEnd ℂ) (u j)) =
      (if u i ^ Q = u j ^ Q then (m i * (u i ^ e).re) * (m j * (u j ^ e).re) else 0) +
        (if u i ^ Q = u j ^ Q then (m i * (u i ^ e).im) * (m j * (u j ^ e).im) else 0) :=
    fun i j => mul_mul_resonantRe_conj (hu j) Q e (m i) (m j)
  simp_rw [hij, Finset.sum_add_distrib]
  have h1 := sum_sq_le_sum_sum_ite_eq_mul (fun i => u i ^ Q)
    (x := fun i => m i * (u i ^ e).re) fun i => mul_nonneg (hm i) (hpos i)
  have h2 := sum_sum_ite_eq_mul_nonneg (fun i => u i ^ Q) (fun i => m i * (u i ^ e).im)
  linarith

/-- A pair sum along the index family is at least `N` times its resonant part, up to `δN`. -/
theorem exists_re_sum_ge_resonantRe {s : ℕ → ℕ → ℕ} {e : ℤ}
    (hres : ∀ T : ℕ, 0 < T → ∀ w : ℂ, w ^ T = 1 → ∀ k, w ^ (s T k) = w ^ e)
    (hweyl : ∀ T : ℕ, 0 < T → ∀ w : ℂ, ‖w‖ = 1 → (∀ n : ℕ, 0 < n → w ^ n ≠ 1) →
      ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ‖∑ k ∈ range N, w ^ (s T k)‖ ≤ δ * N)
    {w : ℂ} (hw : ‖w‖ = 1) {Q : ℕ} (hQ : 0 < Q)
    (hd : w ^ Q = 1 ∨ ∀ n : ℕ, 0 < n → w ^ n ≠ 1) {δ : ℝ} (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      N * resonantRe Q e w - δ * N ≤ (∑ k ∈ range N, w ^ (s Q k)).re := by
  rcases hd with h1 | hnr
  · refine ⟨0, fun N _ => ?_⟩
    have hk : ∀ k : ℕ, w ^ (s Q k) = w ^ e := hres Q hQ w h1
    simp only [hk, sum_const, card_range, nsmul_eq_mul, resonantRe, if_pos h1]
    rw [Complex.mul_re]
    simp only [Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero]
    have : (0 : ℝ) ≤ δ * N := by positivity
    linarith
  · obtain ⟨N₀, hN₀⟩ := hweyl Q hQ w hw hnr δ hδ
    refine ⟨N₀, fun N hN => ?_⟩
    have hne : w ^ Q ≠ 1 := hnr Q hQ
    simp only [resonantRe, if_neg hne, mul_zero, zero_sub]
    have h1 := hN₀ N hN
    have h2 := Complex.abs_re_le_norm (∑ k ∈ range N, w ^ (s Q k))
    have h3 := neg_abs_le (∑ k ∈ range N, w ^ (s Q k)).re
    linarith

/-! ## The moment theorem for conjugation-closed families -/

/-- **Positive density for a conjugation-closed family.** If `u_{σi} = ū_i`, `m_{σi} = m_i` and
`Re u_i^e > 0` for every `i`, then `Σ m_i Re u_i^{s(Q,k)} > ε` for a positive proportion of `k`. -/
theorem exists_card_filter_seq_gt_conj {ι : Type*} [Fintype ι] [Nonempty ι] (idx : ℕ → ℕ → ℕ)
    {e : ℤ} (hres : ∀ T : ℕ, 0 < T → ∀ w : ℂ, w ^ T = 1 → ∀ k, w ^ (idx T k) = w ^ e)
    (hweyl : ∀ T : ℕ, 0 < T → ∀ w : ℂ, ‖w‖ = 1 → (∀ n : ℕ, 0 < n → w ^ n ≠ 1) →
      ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ‖∑ k ∈ range N, w ^ (idx T k)‖ ≤ δ * N)
    (u : ι → ℂ) (m : ι → ℝ) (hu : ∀ i, ‖u i‖ = 1) (hm : ∀ i, 0 < m i)
    (σ : ι ≃ ι) (hσu : ∀ i, u (σ i) = (starRingEnd ℂ) (u i)) (hσm : ∀ i, m (σ i) = m i)
    (hpos : ∀ i, 0 < (u i ^ e).re) :
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
  set s : ℝ := ∑ i, (m i * (u i ^ e).re) ^ 2 with hsdef
  have hs0 : 0 < s := Finset.sum_pos (fun i _ => by have := hm i; have := hpos i; positivity)
    Finset.univ_nonempty
  have hmean : ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → -(δ * N) ≤ ∑ k ∈ range N, f k := by
    intro δ hδ
    have hex : ∀ i, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        -(δ / B * N) ≤ (∑ k ∈ range N, u i ^ (idx Q k)).re := fun i =>
      eventually_neg_le_re_sum_seq_shift hres hweyl (hu i) hQpos (e₁ i) (hpos i).le
        (by positivity)
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
  -- the two resonant parts of the second moment agree, and the conjugate one is a fibre sum
  have hsym : ∑ i, ∑ j, m i * m j * resonantRe Q e (u i * u j) =
      ∑ i, ∑ j, m i * m j * resonantRe Q e (u i * (starRingEnd ℂ) (u j)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp σ (fun j => m i * m j * resonantRe Q e (u i * u j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hσm, hσu]
  have hconj := sum_mul_resonantRe_conj_ge hu (fun i => (hm i).le) Q e (fun i => (hpos i).le)
  have hsq : ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (s - δ) * N ≤ ∑ k ∈ range N, f k ^ 2 := by
    intro δ hδ
    set δ' : ℝ := δ / (B ^ 2 + 1) with hδ'
    have hδ'0 : 0 < δ' := by positivity
    have hex₂ : ∀ p : ι × ι, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        N * resonantRe Q e (u p.1 * u p.2) - δ' * N ≤
          (∑ k ∈ range N, (u p.1 * u p.2) ^ (idx Q k)).re := fun p =>
      exists_re_sum_ge_resonantRe hres hweyl (hu₂ p) hQpos (e₂ p) hδ'0
    have hex₃ : ∀ p : ι × ι, ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        N * resonantRe Q e (u p.1 * (starRingEnd ℂ) (u p.2)) - δ' * N ≤
          (∑ k ∈ range N, (u p.1 * (starRingEnd ℂ) (u p.2)) ^ (idx Q k)).re := fun p =>
      exists_re_sum_ge_resonantRe hres hweyl (hu₃ p) hQpos (e₃ p) hδ'0
    choose N₂ hN₂ using hex₂
    choose N₃ hN₃ using hex₃
    refine ⟨max (Finset.univ.sup N₂) (Finset.univ.sup N₃), fun N hN => ?_⟩
    have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
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
    have hpair : ∀ i j, N * resonantRe Q e (u i * u j) +
        N * resonantRe Q e (u i * (starRingEnd ℂ) (u j)) - 2 * δ' * N ≤
        (∑ k ∈ range N, (u i * u j) ^ (idx Q k)).re +
          (∑ k ∈ range N, (u i * (starRingEnd ℂ) (u j)) ^ (idx Q k)).re := by
      intro i j
      have h2 := hN₂ (i, j) N (le_trans (Finset.le_sup (Finset.mem_univ (i, j)))
        (le_trans (le_max_left _ _) hN))
      have h3 := hN₃ (i, j) N (le_trans (Finset.le_sup (Finset.mem_univ (i, j)))
        (le_trans (le_max_right _ _) hN))
      simp only at h2 h3
      linarith
    have hlow := Finset.sum_le_sum fun i (_ : i ∈ (univ : Finset ι)) =>
      Finset.sum_le_sum fun j (_ : j ∈ (univ : Finset ι)) =>
        mul_le_mul_of_nonneg_left (hpair i j) (by have := hm i; have := hm j; positivity :
          0 ≤ m i * m j / 2)
    have heval : ∑ i, ∑ j, m i * m j / 2 * (N * resonantRe Q e (u i * u j) +
        N * resonantRe Q e (u i * (starRingEnd ℂ) (u j)) - 2 * δ' * N) =
        N / 2 * (∑ i, ∑ j, m i * m j * resonantRe Q e (u i * u j)) +
          N / 2 * (∑ i, ∑ j, m i * m j * resonantRe Q e (u i * (starRingEnd ℂ) (u j))) -
            δ' * B ^ 2 * N := by
      have hB2 : ∑ i, ∑ j, m i * m j = B ^ 2 := by
        rw [sq, hBdef, Finset.sum_mul_sum]
      rw [← hB2]
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [heval, hsym] at hlow
    have hδB : δ' * B ^ 2 ≤ δ := by
      rw [hδ', div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
      nlinarith
    nlinarith
  obtain ⟨ε, c, hε, hc, N₀, hcount⟩ := exists_card_filter_gt_of_mean_sq hB0 hfB hs0 hmean hsq
  exact ⟨Q, hQpos, ε, c, hε, hc, N₀, hcount⟩

/-! ## Li's criterion through conjugation-closed small angles -/

/-- **Conjugation-closed small angles, abstract form.** If the family is closed under an involution
`σ` with `v_{σi} = v̄_i` and `m_{σi} = m_i`, every member outside the unit circle has `|arg v| ≤ θ`,
and `θ|P(x₀)| < π/2`, then the paired Li sums at `P(x)` are negative for infinitely many `x`. -/
theorem frequently_shift_re_tsum_liTerm_neg_conj {P : ℤ[X]} (hlc : 0 < P.leadingCoeff)
    (hdeg : 1 ≤ P.natDegree) {x₀ : ℤ} {θ : ℝ}
    (hsmall : θ * |((P.eval x₀ : ℤ) : ℝ)| < Real.pi / 2)
    {ι : Type*} {v : ι → ℂ} {m : ι → ℝ} {M : ℝ}
    (hm : ∀ i, 1 ≤ m i) (hv : ∀ i, 1 ≤ ‖v i‖) (hM : ∀ i, ‖v i‖ ≤ M)
    (hs : Summable fun i => m i * ‖v i - 1‖ ^ (2 : ℕ))
    (σ : ι ≃ ι) (hσv : ∀ i, v (σ i) = (starRingEnd ℂ) (v i)) (hσm : ∀ i, m (σ i) = m i)
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
  -- the involution restricted to the dominant layer
  set σD : {x // x ∈ D} ≃ {x // x ∈ D} := σ.subtypeEquiv fun i => by
    rw [hDnorm i, hDnorm (σ i), hσv, Complex.norm_conj] with hσD
  have hσu : ∀ i, u (σD i) = (starRingEnd ℂ) (u i) := by
    intro i
    simp only [hudef, hσD, Equiv.subtypeEquiv_apply, hσv, map_div₀, Complex.conj_ofReal]
  have hσm' : ∀ i, (fun i : {x // x ∈ D} => m i) (σD i) = m i := by
    intro i
    simp only [hσD, Equiv.subtypeEquiv_apply, hσm]
  set e : ℤ := P.eval x₀ with he
  have hexp : ∀ i, u i = Complex.exp ((Complex.arg (u i) : ℂ) * I) := fun i =>
    eq_exp_arg_mul_I_of_norm_eq_one (hunit i)
  have hpos : ∀ i, 0 < (u i ^ e).re := by
    intro i
    rw [hexp i, re_zpow_exp_mul_I]
    have hb : |(e : ℝ) * Complex.arg (u i)| < Real.pi / 2 := by
      rw [abs_mul]
      calc |(e : ℝ)| * |Complex.arg (u i)| ≤ |(e : ℝ)| * θ := by gcongr; exact hargu i
        _ = θ * |(e : ℝ)| := by ring
        _ < Real.pi / 2 := hsmall
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [neg_abs_le ((e : ℝ) * Complex.arg (u i))],
      lt_of_le_of_lt (le_abs_self _) hb⟩
  obtain ⟨T, hT, ε, cc, hε, hcc, N₀, hcount⟩ :=
    exists_card_filter_seq_gt_conj s hres hweyl u (fun i => m i) hunit
      (fun i => by linarith [hm i]) σD hσu hσm' hpos
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

/-! ## The case of `ξ` -/

theorem xiRootV_conj (ρ : ℂ) : xiRootV ((starRingEnd ℂ) ρ) = (starRingEnd ℂ) (xiRootV ρ) := by
  unfold xiRootV
  rw [xiRootW_conj, Complex.norm_conj]
  split_ifs
  · rfl
  · rw [map_inv₀]

theorem xiSupportConj_involutive : Function.Involutive xiSupportConj := fun ρ =>
  Subtype.ext (by rw [xiSupportConj_coe, xiSupportConj_coe, Complex.conj_conj])

/-- **Li's criterion along any polynomial with a value of size at most `22`.** If `P ∈ ℤ[X]` has
positive leading coefficient, degree `≥ 1` and `|P(x₀)| ≤ 22`, then the Riemann hypothesis holds iff
`Re 2λ_{P(x)} ≥ 0` for all large `x`. -/
theorem riemannHypothesis_iff_eventually_re_xiLiPaired_of_value_le {P : ℤ[X]}
    (hlc : 0 < P.leadingCoeff) (hdeg : 1 ≤ P.natDegree) {x₀ : ℤ} (hx₀ : |P.eval x₀| ≤ 22) :
    RiemannHypothesis ↔ ∀ᶠ x : ℕ in atTop, 0 ≤ (xiLiPaired (P.eval (x : ℤ)).toNat).re := by
  constructor
  · intro hRH
    exact Filter.Eventually.of_forall fun x => re_xiLiPaired_nonneg_of_rh hRH _
  · intro h
    by_contra hRH
    obtain ⟨M, hmult, hvnorm, hvM, hsum, _, hbad⟩ := xiLi_family_facts
    obtain ⟨ρ₀, hρ₀⟩ := hbad hRH
    have hsmall : (7 / 100 : ℝ) * |((P.eval x₀ : ℤ) : ℝ)| < Real.pi / 2 := by
      have h1 : |((P.eval x₀ : ℤ) : ℝ)| ≤ 22 := by exact_mod_cast hx₀
      have := Real.pi_gt_d2
      nlinarith [abs_nonneg ((P.eval x₀ : ℤ) : ℝ)]
    set σ : XiDivisorSupport ≃ XiDivisorSupport :=
      Function.Involutive.toPerm xiSupportConj xiSupportConj_involutive with hσ
    have hσv : ∀ ρ : XiDivisorSupport,
        xiRootV ((σ ρ : XiDivisorSupport) : ℂ) = (starRingEnd ℂ) (xiRootV (ρ : ℂ)) := by
      intro ρ
      rw [hσ, Function.Involutive.coe_toPerm, xiSupportConj_coe, xiRootV_conj]
    have hσm : ∀ ρ : XiDivisorSupport,
        ((MeromorphicOn.divisor xi Set.univ) ((σ ρ : XiDivisorSupport) : ℂ) : ℝ) =
          ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) : ℝ) := by
      intro ρ
      rw [hσ, Function.Involutive.coe_toPerm, xiSupportConj_coe, xi_divisor_conj]
    have hfreq := frequently_shift_re_tsum_liTerm_neg_conj hlc hdeg (x₀ := x₀) hsmall
      hmult hvnorm hvM hsum σ hσv hσm (fun ρ hρ => abs_arg_xiRootV_le_of_one_lt ρ hρ) hρ₀
    obtain ⟨x, hx1, hx2⟩ := (hfreq.and_eventually h).exists
    rw [← re_xiLiPaired_eq_tsum_mult] at hx1
    linarith

/-- **Li's criterion along every arithmetic progression of modulus at most `45`.** For
`1 ≤ a ≤ 45` and every `b`, the Riemann hypothesis holds iff `Re 2λ_{an+b} ≥ 0` for all large `n`. -/
theorem riemannHypothesis_iff_eventually_re_xiLiPaired_progression_le_45 {a b : ℕ} (ha : 1 ≤ a)
    (ha45 : a ≤ 45) :
    RiemannHypothesis ↔ ∀ᶠ n : ℕ in atTop, 0 ≤ (xiLiPaired (a * n + b)).re := by
  have haz : (a : ℤ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
  have hlc : 0 < (C (a : ℤ) * X + C (b : ℤ) : ℤ[X]).leadingCoeff := by
    rw [leadingCoeff_linear haz]; exact_mod_cast (show 0 < a by omega)
  have hdeg : 1 ≤ (C (a : ℤ) * X + C (b : ℤ) : ℤ[X]).natDegree := by
    rw [natDegree_linear haz]
  obtain ⟨x₀, hx₀⟩ := exists_abs_progression_le a b ha
  have hval : |(C (a : ℤ) * X + C (b : ℤ) : ℤ[X]).eval x₀| ≤ 22 := by
    simp only [eval_add, eval_mul, eval_C, eval_X]
    have : ((a / 2 : ℕ) : ℤ) ≤ 22 := by exact_mod_cast (show a / 2 ≤ 22 by omega)
    linarith
  have h := riemannHypothesis_iff_eventually_re_xiLiPaired_of_value_le hlc hdeg hval
  have e : ∀ n : ℕ, ((C (a : ℤ) * X + C (b : ℤ) : ℤ[X]).eval (n : ℤ)).toNat = a * n + b := by
    intro n
    simp only [eval_add, eval_mul, eval_C, eval_X]
    have : (a : ℤ) * n + b = ((a * n + b : ℕ) : ℤ) := by push_cast; ring
    rw [this, Int.toNat_natCast]
  simp only [e] at h
  exact h

/-! ## Sharpness at modulus `46` -/

/-- The unit root `e^{iπ/(2c)}`. -/
def halfTurnRoot (c : ℕ) : ℂ := Complex.exp (((Real.pi / (2 * c) : ℝ) : ℂ) * I)

theorem norm_halfTurnRoot (c : ℕ) : ‖halfTurnRoot c‖ = 1 := by
  unfold halfTurnRoot; exact Complex.norm_exp_ofReal_mul_I _

theorem arg_halfTurnRoot {c : ℕ} (hc : 0 < c) :
    Complex.arg (halfTurnRoot c) = Real.pi / (2 * c) := by
  unfold halfTurnRoot
  rw [Complex.arg_exp_mul_I, toIocMod_eq_self]
  have hπ := Real.pi_pos
  have hc1 : (1 : ℝ) ≤ c := by exact_mod_cast hc
  have h0 : 0 < Real.pi / (2 * c) := by positivity
  have h1 : Real.pi / (2 * c) ≤ Real.pi := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  constructor <;> linarith

/-- At every index `2ck + c` the power `e^{iπ(2ck+c)/(2c)} = ±i` is purely imaginary. -/
theorem re_halfTurnRoot_pow {c : ℕ} (hc : 0 < c) (k : ℕ) :
    (halfTurnRoot c ^ (2 * c * k + c)).re = 0 := by
  unfold halfTurnRoot
  rw [← Complex.exp_nat_mul, ← mul_assoc]
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have : ((2 * c * k + c : ℕ) : ℂ) * ((Real.pi / (2 * c) : ℝ) : ℂ) =
      (((k : ℝ) * Real.pi + Real.pi / 2 : ℝ) : ℂ) := by
    push_cast; field_simp
  rw [this, Complex.exp_ofReal_mul_I_re, Real.cos_add_pi_div_two, Real.sin_nat_mul_pi, neg_zero]

/-- **The half-turn pair.** For `R > 0` the Cayley pair `R e^{±iπ/(2c)}` has paired Li sum exactly `4`
at every index `2ck + c`. -/
theorem halfTurnPair_re_liTerm_eq_four {R : ℝ} (hR : 0 < R) {c : ℕ} (hc : 0 < c) (k : ℕ) :
    (liTerm ((R : ℂ) * halfTurnRoot c) (2 * c * k + c)).re +
      (liTerm ((R : ℂ) * (starRingEnd ℂ) (halfTurnRoot c)) (2 * c * k + c)).re = 4 := by
  have hn : ‖(starRingEnd ℂ) (halfTurnRoot c)‖ = 1 := by
    rw [Complex.norm_conj, norm_halfTurnRoot]
  rw [re_liTerm_ofReal_mul_unit (norm_halfTurnRoot c) hR, re_liTerm_ofReal_mul_unit hn hR,
    ← map_pow, Complex.conj_re, re_halfTurnRoot_pow hc k]
  ring

/-- The half-turn root of modulus `46` lies inside the band angle `7/100`. -/
theorem abs_arg_halfTurnRoot_twentyThree_le : |Complex.arg (halfTurnRoot 23)| ≤ 7 / 100 := by
  rw [arg_halfTurnRoot (by norm_num), abs_of_pos (by positivity)]
  have := Real.pi_lt_d2
  rw [div_le_iff₀ (by norm_num)]
  push_cast
  linarith

end RHTower

end
