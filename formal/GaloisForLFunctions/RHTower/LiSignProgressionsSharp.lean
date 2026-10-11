import GaloisForLFunctions.RHTower.LiSignConjugateMoment

/-!
# Li's criterion along arithmetic progressions: the exact reach of the band angle

Along a progression `n = b + ak` the dominant Li layer is `f(k) = Σ_i m_i Re(u_i^b (u_i^a)^k)`.

**Moment theorem** (`exists_card_filter_progression_gt`). For a conjugation-closed unit family with
`u_i^a ≠ 1` for every `i`, the mean of `f` is `O(1)` (geometric sums), and the mean square tends to
`Σ_c |Σ_{u_i^a = c} m_i u_i^b|²`, a sum over the fibres of `i ↦ u_i^a`. If one fibre sum is nonzero,
then `f > ε` on a positive proportion of `k`.

**Fibres for small angles** (`exists_fibre_sum_ne_zero`). If every `|arg u_i| ≤ 7/100` and
`a ≤ 89`, two members of a fibre differ by an `a`-th root of unity of argument at most `14/100 < 4π/89`,
so the fibre of the member of least argument takes at most two values `u, u e^{2πi/a}`. Its sum
vanishes only if `e^{2πib/a} = −1`, that is `a` even and `b ≡ a/2 (mod a)`.

**Theorem** (`riemannHypothesis_iff_eventually_re_xiLiPaired_progression_lt_90`). For `1 ≤ a ≤ 89` and
every `b` except `a` even with `b ≡ a/2 (mod a)`, the Riemann hypothesis holds iff
`Re 2λ_{an+b} ≥ 0` for all large `n`. With the half-turn pair of `LiSignConjugateMoment`
(`46k + 23`) and the pair `e^{±2πi/a}` of `LiSignProgressions` this is the exact reach of the band
bound `|arg v| ≤ 7/100`.

**Geometric sequences** (`geometricRootFamily_re_liTerm_pos`, `abs_arg_geometricRoot_le`). For every
`b ≥ 2` and every angle bound, the conjugation-closed family `R e^{±2πia/(pb^k)}` (`1 ≤ a < p`, `p` a prime
not dividing `b`) has positive paired Li sums at every `b^m`, `m ≥ k`, and arguments at most `2π/b^k`.
So no argument from small Cayley angles decides Li's criterion along `{b^m}`.
-/

open Complex Filter Finset Polynomial

noncomputable section

namespace RHTower

/-! ## Geometric sums and fibre identities -/

theorem norm_geom_sum_le_of_ne_one {w : ℂ} (hw : ‖w‖ = 1) (h1 : w ≠ 1) (N : ℕ) :
    ‖∑ k ∈ range N, w ^ k‖ ≤ 2 / ‖w - 1‖ := by
  have hne : w - 1 ≠ 0 := sub_ne_zero.mpr h1
  have hpos : 0 < ‖w - 1‖ := norm_pos_iff.mpr hne
  rw [geom_sum_eq h1, norm_div]
  refine div_le_div_of_nonneg_right ?_ hpos.le
  calc ‖w ^ N - 1‖ ≤ ‖w ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hw, one_pow, norm_one]; norm_num

/-- `Σ_{i,j} [w_i = w_j] y_i y_j = Σ_{c ∈ w(ι)} (Σ_{w_i = c} y_i)²`. -/
theorem sum_sum_ite_eq_mul_eq {ι α : Type*} [Fintype ι] [DecidableEq α] (w : ι → α)
    (y : ι → ℝ) : (∑ i, ∑ j, if w i = w j then y i * y j else 0) =
      ∑ c ∈ univ.image w, (∑ i ∈ univ with w i = c, y i) ^ 2 := by
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
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [sq, Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [(Finset.mem_filter.mp hi).2]

/-- One fibre bounds the fibre sum of squares. -/
theorem sq_fibre_le_sum_sum_ite {ι α : Type*} [Fintype ι] [DecidableEq α] (w : ι → α)
    (y : ι → ℝ) (i₀ : ι) :
    (∑ i ∈ univ with w i = w i₀, y i) ^ 2 ≤ ∑ i, ∑ j, if w i = w j then y i * y j else 0 := by
  rw [sum_sum_ite_eq_mul_eq]
  exact Finset.single_le_sum (f := fun c => (∑ i ∈ univ with w i = c, y i) ^ 2)
    (fun c _ => sq_nonneg _) (Finset.mem_image_of_mem w (Finset.mem_univ i₀))

/-- The conjugate resonant part at period `a` dominates the squared norm of any one fibre sum. -/
theorem normSq_fibre_le_sum_mul_resonantRe_conj {ι : Type*} [Fintype ι] {u : ι → ℂ} {m : ι → ℝ}
    (hu : ∀ i, ‖u i‖ = 1) (a n₀ : ℕ) (i₀ : ι) :
    ‖∑ i ∈ univ with u i ^ a = u i₀ ^ a, (m i : ℂ) * u i ^ n₀‖ ^ 2 ≤
      ∑ i, ∑ j, m i * m j * resonantRe a (n₀ : ℤ) (u i * (starRingEnd ℂ) (u j)) := by
  classical
  have hij : ∀ i j, m i * m j * resonantRe a (n₀ : ℤ) (u i * (starRingEnd ℂ) (u j)) =
      (if u i ^ a = u j ^ a then (m i * (u i ^ (n₀ : ℤ)).re) * (m j * (u j ^ (n₀ : ℤ)).re)
        else 0) +
      (if u i ^ a = u j ^ a then (m i * (u i ^ (n₀ : ℤ)).im) * (m j * (u j ^ (n₀ : ℤ)).im)
        else 0) :=
    fun i j => mul_mul_resonantRe_conj (hu j) a (n₀ : ℤ) (m i) (m j)
  simp_rw [hij, Finset.sum_add_distrib]
  have h1 := sq_fibre_le_sum_sum_ite (fun i => u i ^ a) (fun i => m i * (u i ^ (n₀ : ℤ)).re) i₀
  have h2 := sq_fibre_le_sum_sum_ite (fun i => u i ^ a) (fun i => m i * (u i ^ (n₀ : ℤ)).im) i₀
  have hnorm : ‖∑ i ∈ univ with u i ^ a = u i₀ ^ a, (m i : ℂ) * u i ^ n₀‖ ^ 2 =
      (∑ i ∈ univ with u i ^ a = u i₀ ^ a, m i * (u i ^ (n₀ : ℤ)).re) ^ 2 +
        (∑ i ∈ univ with u i ^ a = u i₀ ^ a, m i * (u i ^ (n₀ : ℤ)).im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.re_sum, Complex.im_sum]
    simp only [zpow_natCast, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
    ring
  rw [hnorm]
  linarith

/-! ## The moment theorem along a progression -/

/-- A pair sum along `b + ak` is `N` times its period-`a` resonant part, up to a constant. -/
theorem re_sum_pow_progression_ge {w : ℂ} (hw : ‖w‖ = 1) (a b N : ℕ) :
    N * resonantRe a (b : ℤ) w -
        (if w ^ a = 1 then 0 else 2 / ‖w ^ a - 1‖) ≤
      (∑ k ∈ range N, w ^ (b + a * k)).re := by
  have hsplit : ∑ k ∈ range N, w ^ (b + a * k) = w ^ b * ∑ k ∈ range N, (w ^ a) ^ k := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [pow_add, pow_mul]
  rw [hsplit]
  by_cases h1 : w ^ a = 1
  · have hr : resonantRe a (b : ℤ) w = (w ^ b).re := by
      simp only [resonantRe, if_pos h1, zpow_natCast]
    rw [hr, if_pos h1, h1]
    simp only [one_pow, sum_const, card_range, nsmul_eq_mul, mul_one, Complex.mul_re,
      Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
    linarith
  · simp only [resonantRe, if_neg h1, mul_zero, zero_sub]
    have hwa : ‖w ^ a‖ = 1 := by rw [norm_pow, hw, one_pow]
    have hg := norm_geom_sum_le_of_ne_one hwa h1 N
    have hre := Complex.abs_re_le_norm (w ^ b * ∑ k ∈ range N, (w ^ a) ^ k)
    rw [norm_mul, norm_pow, hw, one_pow, one_mul] at hre
    have := neg_abs_le (w ^ b * ∑ k ∈ range N, (w ^ a) ^ k).re
    linarith

/-- **Positive density along a progression.** For a conjugation-closed unit family with
`u_i^a ≠ 1` and one nonzero fibre sum `Σ_{u_i^a = u_{i₀}^a} m_i u_i^b`, the dominant layer
`Σ m_i Re u_i^{b+ak}` exceeds `ε` for a positive proportion of `k`. -/
theorem exists_card_filter_progression_gt {ι : Type*} [Fintype ι] [Nonempty ι]
    (u : ι → ℂ) (m : ι → ℝ) (hu : ∀ i, ‖u i‖ = 1) (hm : ∀ i, 0 < m i)
    (σ : ι ≃ ι) (hσu : ∀ i, u (σ i) = (starRingEnd ℂ) (u i)) (hσm : ∀ i, m (σ i) = m i)
    {a : ℕ} (hroot : ∀ i, u i ^ a ≠ 1) (b : ℕ) {i₀ : ι}
    (hfib : ∑ i ∈ univ with u i ^ a = u i₀ ^ a, (m i : ℂ) * u i ^ b ≠ 0) :
    ∃ ε c : ℝ, 0 < ε ∧ 0 < c ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      c * N ≤ (((range N).filter
        (fun k => ε < ∑ i, m i * (u i ^ (b + a * k)).re)).card : ℝ) := by
  classical
  set f : ℕ → ℝ := fun k => ∑ i, m i * (u i ^ (b + a * k)).re with hf
  set B : ℝ := ∑ i, m i with hBdef
  have hB0 : 0 < B := Finset.sum_pos (fun i _ => hm i) Finset.univ_nonempty
  have hfB : ∀ k, |f k| ≤ B := by
    intro k
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [abs_mul, abs_of_pos (hm i)]
    have h1 := Complex.abs_re_le_norm (u i ^ (b + a * k))
    rw [norm_pow, hu, one_pow] at h1
    nlinarith [hm i]
  set s : ℝ := ‖∑ i ∈ univ with u i ^ a = u i₀ ^ a, (m i : ℂ) * u i ^ b‖ ^ 2 with hsdef
  have hs0 : 0 < s := by rw [hsdef]; positivity
  -- the error constant of a unit pair
  set err : ℂ → ℝ := fun w => if w ^ a = 1 then 0 else 2 / ‖w ^ a - 1‖ with herr
  have herr0 : ∀ w, 0 ≤ err w := fun w => by
    simp only [herr]; split_ifs <;> positivity
  have hmean : ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → -(δ * N) ≤ ∑ k ∈ range N, f k := by
    intro δ hδ
    set C₁ : ℝ := ∑ i, m i * err (u i) with hC₁
    have hC₁0 : 0 ≤ C₁ := Finset.sum_nonneg fun i _ => mul_nonneg (hm i).le (herr0 _)
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (C₁ / δ)
    refine ⟨N₀, fun N hN => ?_⟩
    have hswap : ∑ k ∈ range N, f k = ∑ i, m i * (∑ k ∈ range N, u i ^ (b + a * k)).re := by
      simp only [hf]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.re_sum, Finset.mul_sum]
    rw [hswap]
    have hle : ∀ i ∈ (univ : Finset ι), m i * (-(err (u i))) ≤
        m i * (∑ k ∈ range N, u i ^ (b + a * k)).re := by
      intro i _
      refine mul_le_mul_of_nonneg_left ?_ (hm i).le
      have h := re_sum_pow_progression_ge (hu i) a b N
      simp only [resonantRe, if_neg (hroot i), mul_zero, zero_sub] at h
      simpa [herr, if_neg (hroot i)] using h
    have hsum := Finset.sum_le_sum hle
    have heq : ∑ i, m i * (-(err (u i))) = -C₁ := by
      rw [hC₁, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      ring
    have hNδ : C₁ ≤ δ * N := by
      have h1 : C₁ / δ < N := lt_of_lt_of_le hN₀ (by exact_mod_cast hN)
      rw [div_lt_iff₀ hδ] at h1
      linarith
    linarith
  have hsym : ∑ i, ∑ j, m i * m j * resonantRe a (b : ℤ) (u i * u j) =
      ∑ i, ∑ j, m i * m j * resonantRe a (b : ℤ) (u i * (starRingEnd ℂ) (u j)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Equiv.sum_comp σ (fun j => m i * m j * resonantRe a (b : ℤ) (u i * u j))]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hσm, hσu]
  have hconj := normSq_fibre_le_sum_mul_resonantRe_conj (m := m) hu a b i₀
  have hsq : ∀ δ : ℝ, 0 < δ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (s - δ) * N ≤ ∑ k ∈ range N, f k ^ 2 := by
    intro δ hδ
    set C₂ : ℝ := ∑ i, ∑ j, m i * m j / 2 *
      (err (u i * u j) + err (u i * (starRingEnd ℂ) (u j))) with hC₂
    have hC₂0 : 0 ≤ C₂ := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ =>
      mul_nonneg (by have := hm i; have := hm j; positivity) (add_nonneg (herr0 _) (herr0 _))
    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (C₂ / δ)
    refine ⟨N₀, fun N hN => ?_⟩
    have hN0 : (0 : ℝ) ≤ N := N.cast_nonneg
    have hswap : ∑ k ∈ range N, f k ^ 2 = ∑ i, ∑ j, m i * m j / 2 *
        ((∑ k ∈ range N, (u i * u j) ^ (b + a * k)).re +
          (∑ k ∈ range N, (u i * (starRingEnd ℂ) (u j)) ^ (b + a * k)).re) := by
      simp only [hf, sq_sum_mul_re_pow_eq]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.re_sum, Complex.re_sum, ← Finset.sum_add_distrib, Finset.mul_sum]
    rw [hswap]
    have hpair : ∀ i j, N * resonantRe a (b : ℤ) (u i * u j) +
        N * resonantRe a (b : ℤ) (u i * (starRingEnd ℂ) (u j)) -
          (err (u i * u j) + err (u i * (starRingEnd ℂ) (u j))) ≤
        (∑ k ∈ range N, (u i * u j) ^ (b + a * k)).re +
          (∑ k ∈ range N, (u i * (starRingEnd ℂ) (u j)) ^ (b + a * k)).re := by
      intro i j
      have h2 := re_sum_pow_progression_ge (w := u i * u j) (by rw [norm_mul, hu, hu, one_mul])
        a b N
      have h3 := re_sum_pow_progression_ge (w := u i * (starRingEnd ℂ) (u j))
        (by rw [norm_mul, Complex.norm_conj, hu, hu, one_mul]) a b N
      simp only [herr]
      linarith
    have hlow := Finset.sum_le_sum fun i (_ : i ∈ (univ : Finset ι)) =>
      Finset.sum_le_sum fun j (_ : j ∈ (univ : Finset ι)) =>
        mul_le_mul_of_nonneg_left (hpair i j) (by have := hm i; have := hm j; positivity :
          0 ≤ m i * m j / 2)
    have heval : ∑ i, ∑ j, m i * m j / 2 * (N * resonantRe a (b : ℤ) (u i * u j) +
        N * resonantRe a (b : ℤ) (u i * (starRingEnd ℂ) (u j)) -
          (err (u i * u j) + err (u i * (starRingEnd ℂ) (u j)))) =
        N / 2 * (∑ i, ∑ j, m i * m j * resonantRe a (b : ℤ) (u i * u j)) +
          N / 2 * (∑ i, ∑ j, m i * m j * resonantRe a (b : ℤ) (u i * (starRingEnd ℂ) (u j))) -
            C₂ := by
      rw [hC₂]
      simp only [Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    rw [heval, hsym] at hlow
    have hNδ : C₂ ≤ δ * N := by
      have h1 : C₂ / δ < N := lt_of_lt_of_le hN₀ (by exact_mod_cast hN)
      rw [div_lt_iff₀ hδ] at h1
      linarith
    have hsN : s * N ≤ N * (∑ i, ∑ j, m i * m j * resonantRe a (b : ℤ)
        (u i * (starRingEnd ℂ) (u j))) := by
      rw [mul_comm]
      exact mul_le_mul_of_nonneg_left hconj hN0
    nlinarith
  exact exists_card_filter_gt_of_mean_sq hB0 hfB hs0 hmean hsq

/-! ## Small angles: no root of unity, and a nonzero fibre -/

theorem exists_int_eq_of_exp_mul_I_eq_one {x : ℝ} (h : Complex.exp ((x : ℂ) * I) = 1) :
    ∃ n : ℤ, x = n * (2 * Real.pi) := by
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
  refine ⟨n, ?_⟩
  have h2 : (x : ℂ) * I = ((n * (2 * Real.pi) : ℝ) : ℂ) * I := by rw [hn]; push_cast; ring
  exact_mod_cast mul_right_cancel₀ Complex.I_ne_zero h2

theorem pow_exp_arg {u : ℂ} (hu : ‖u‖ = 1) (n : ℕ) :
    u ^ n = Complex.exp ((((n : ℝ) * Complex.arg u : ℝ) : ℂ) * I) := by
  conv_lhs => rw [eq_exp_arg_mul_I_of_norm_eq_one hu]
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- A non-real unit of argument at most `7/100` is not a root of unity of order at most `89`. -/
theorem pow_ne_one_of_abs_arg_le {u : ℂ} (hu : ‖u‖ = 1) (him : u.im ≠ 0)
    (harg : |Complex.arg u| ≤ 7 / 100) {a : ℕ} (ha : 1 ≤ a) (ha89 : a ≤ 89) : u ^ a ≠ 1 := by
  intro h
  rw [pow_exp_arg hu] at h
  obtain ⟨n, hn⟩ := exists_int_eq_of_exp_mul_I_eq_one h
  have hπ := Real.pi_gt_d2
  have ha' : (a : ℝ) ≤ 89 := by exact_mod_cast ha89
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have habs : |(n : ℝ)| * (2 * Real.pi) = (a : ℝ) * |Complex.arg u| := by
    have := congrArg abs hn
    rw [abs_mul, abs_mul, Nat.abs_cast, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      at this
    linarith
  have hlt : |(n : ℝ)| * (2 * Real.pi) < 1 * (2 * Real.pi) := by
    rw [habs]
    nlinarith [abs_nonneg (Complex.arg u)]
  have hn1 : |(n : ℝ)| < 1 := lt_of_mul_lt_mul_right hlt (by positivity)
  have hn0 : n = 0 := by
    have : |n| < 1 := by exact_mod_cast hn1
    rw [abs_lt] at this
    omega
  rw [hn0, Int.cast_zero, zero_mul, mul_eq_zero] at hn
  rcases hn with h0 | h0
  · linarith
  · exact him (Complex.arg_eq_zero_iff.mp h0).2

/-- `e^{2πib/a} = −1` only if `a ∣ 2b` and `a ∤ b`. -/
theorem dvd_of_exp_eq_neg_one {a b : ℕ} (ha : 1 ≤ a)
    (h : Complex.exp (((2 * Real.pi * b / a : ℝ) : ℂ) * I) = -1) : a ∣ 2 * b ∧ ¬ a ∣ b := by
  have ha0 : (a : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have ha0C : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hπ := Real.pi_pos
  constructor
  · have hsq : Complex.exp (((2 * (2 * Real.pi * b / a) : ℝ) : ℂ) * I) = 1 := by
      have e : (((2 * (2 * Real.pi * b / a) : ℝ) : ℂ) * I) =
          ((2 : ℕ) : ℂ) * (((2 * Real.pi * b / a : ℝ) : ℂ) * I) := by push_cast; ring
      rw [e, Complex.exp_nat_mul, h]; norm_num
    obtain ⟨n, hn⟩ := exists_int_eq_of_exp_mul_I_eq_one hsq
    have h2 : ((2 * b : ℕ) : ℝ) = (n * a : ℤ) := by
      push_cast
      field_simp at hn
      nlinarith
    have h3 : ((2 * b : ℕ) : ℤ) = n * a := by exact_mod_cast h2
    have h4 : (a : ℤ) ∣ ((2 * b : ℕ) : ℤ) := ⟨n, by rw [h3]; ring⟩
    exact Int.natCast_dvd_natCast.mp h4
  · rintro ⟨t, rfl⟩
    have e : ((2 * Real.pi * ((a * t : ℕ) : ℝ) / a : ℝ) : ℂ) * I =
        (t : ℤ) * (2 * Real.pi * I) := by
      push_cast; field_simp
    rw [e, Complex.exp_eq_one_iff.mpr ⟨t, rfl⟩] at h
    norm_num at h

/-- **A nonzero fibre for small angles.** If every `|arg u_i| ≤ 7/100`, `1 ≤ a ≤ 89` and not
(`a ∣ 2b` and `a ∤ b`), then the fibre of the member of least argument has nonzero sum. -/
theorem exists_fibre_sum_ne_zero {ι : Type*} [Fintype ι] [Nonempty ι] {u : ι → ℂ} {m : ι → ℝ}
    (hu : ∀ i, ‖u i‖ = 1) (hm : ∀ i, 0 < m i) (harg : ∀ i, |Complex.arg (u i)| ≤ 7 / 100)
    {a : ℕ} (ha : 1 ≤ a) (ha89 : a ≤ 89) (b : ℕ) (hb : ¬ (a ∣ 2 * b ∧ ¬ a ∣ b)) :
    ∃ i₀ : ι, ∑ i ∈ univ with u i ^ a = u i₀ ^ a, (m i : ℂ) * u i ^ b ≠ 0 := by
  classical
  obtain ⟨i₀, -, hmin⟩ :=
    Finset.exists_min_image univ (fun i => Complex.arg (u i)) univ_nonempty
  refine ⟨i₀, ?_⟩
  set z : ℂ := Complex.exp (((2 * Real.pi * b / a : ℝ) : ℂ) * I) with hz
  have hz1 : ‖z‖ = 1 := Complex.norm_exp_ofReal_mul_I _
  have hπ := Real.pi_gt_d2
  have hπ0 := Real.pi_pos
  have ha' : (a : ℝ) ≤ 89 := by exact_mod_cast ha89
  have ha1 : (1 : ℝ) ≤ a := by exact_mod_cast ha
  -- each member of the fibre has `u^b ∈ {u₀^b, u₀^b z}`
  have hmem : ∀ j, u j ^ a = u i₀ ^ a → u j ^ b = u i₀ ^ b ∨ u j ^ b = u i₀ ^ b * z := by
    intro j hj
    rw [pow_exp_arg (hu j), pow_exp_arg (hu i₀)] at hj
    have h1 : Complex.exp ((((a : ℝ) * (Complex.arg (u j) - Complex.arg (u i₀)) : ℝ) : ℂ) * I)
        = 1 := by
      have e : ((((a : ℝ) * (Complex.arg (u j) - Complex.arg (u i₀)) : ℝ) : ℂ) * I) =
          (((a : ℝ) * Complex.arg (u j) : ℝ) : ℂ) * I -
            (((a : ℝ) * Complex.arg (u i₀) : ℝ) : ℂ) * I := by push_cast; ring
      rw [e, Complex.exp_sub, hj, div_self (Complex.exp_ne_zero _)]
    obtain ⟨n, hn⟩ := exists_int_eq_of_exp_mul_I_eq_one h1
    have hd0 : 0 ≤ Complex.arg (u j) - Complex.arg (u i₀) :=
      sub_nonneg.mpr (hmin j (mem_univ j))
    have hd1 : Complex.arg (u j) - Complex.arg (u i₀) ≤ 14 / 100 := by
      have h1 := harg j
      have h2 := harg i₀
      have h3 := le_abs_self (Complex.arg (u j))
      have h4 := neg_abs_le (Complex.arg (u i₀))
      linarith
    have hlo : 0 ≤ (n : ℝ) * (2 * Real.pi) := by
      rw [← hn]; exact mul_nonneg (by linarith) hd0
    have hhi : (n : ℝ) * (2 * Real.pi) < 2 * (2 * Real.pi) := by
      rw [← hn]
      calc (a : ℝ) * (Complex.arg (u j) - Complex.arg (u i₀)) ≤ 89 * (14 / 100) := by
            nlinarith
        _ < 2 * (2 * Real.pi) := by linarith
    have hn0 : (0 : ℝ) ≤ n := nonneg_of_mul_nonneg_left hlo (by positivity)
    have hn2 : (n : ℝ) < 2 := lt_of_mul_lt_mul_right hhi (by positivity)
    have hn01 : n = 0 ∨ n = 1 := by
      have h0 : 0 ≤ n := by exact_mod_cast hn0
      have h2 : n < 2 := by exact_mod_cast hn2
      omega
    have hφ : Complex.arg (u j) = Complex.arg (u i₀) + n * (2 * Real.pi) / a := by
      rw [← hn]; field_simp; ring
    rcases hn01 with h0 | h1'
    · left
      rw [pow_exp_arg (hu j), pow_exp_arg (hu i₀), hφ, h0]
      simp
    · right
      rw [pow_exp_arg (hu j), pow_exp_arg (hu i₀), hφ, h1', hz, ← Complex.exp_add]
      congr 1
      push_cast
      field_simp
  have hzne : z ≠ -1 := fun h => hb (dvd_of_exp_eq_neg_one ha h)
  -- `1 + Re z > 0`
  have hrez : 0 < 1 + z.re := by
    have hle : -1 ≤ z.re := by
      have := Complex.abs_re_le_norm z
      rw [hz1] at this
      linarith [neg_abs_le z.re]
    rcases hle.lt_or_eq with hlt | heq
    · linarith
    · exfalso
      have hns : z.re * z.re + z.im * z.im = 1 := by
        rw [← Complex.normSq_apply, ← Complex.sq_norm, hz1]; norm_num
      have him : z.im = 0 := by rw [← heq] at hns; nlinarith
      exact hzne (Complex.ext (by rw [← heq]; simp) (by rw [him]; simp))
  -- pair the fibre sum with `W = conj(u₀^b)(1 + conj z)`
  set W : ℂ := (starRingEnd ℂ) (u i₀ ^ b) * (1 + (starRingEnd ℂ) z) with hW
  have hu0 : u i₀ ^ b * (starRingEnd ℂ) (u i₀ ^ b) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, hu, one_pow]; norm_num
  have hzz : z * (starRingEnd ℂ) z = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz1]; norm_num
  have hterm : ∀ j, u j ^ a = u i₀ ^ a → (u j ^ b * W).re = 1 + z.re := by
    intro j hj
    rcases hmem j hj with h | h
    · rw [h, hW, ← mul_assoc, hu0, one_mul, Complex.add_re, Complex.one_re, Complex.conj_re]
    · rw [h, hW, show u i₀ ^ b * z * ((starRingEnd ℂ) (u i₀ ^ b) * (1 + (starRingEnd ℂ) z)) =
          (u i₀ ^ b * (starRingEnd ℂ) (u i₀ ^ b)) * (z + z * (starRingEnd ℂ) z) by ring,
        hu0, hzz, one_mul, Complex.add_re, Complex.one_re]
      ring
  intro hzero
  have hre : ((∑ i ∈ univ with u i ^ a = u i₀ ^ a, (m i : ℂ) * u i ^ b) * W).re =
      ∑ i ∈ univ with u i ^ a = u i₀ ^ a, m i * (1 + z.re) := by
    rw [Finset.sum_mul, Complex.re_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [mul_assoc, Complex.re_ofReal_mul, hterm i (Finset.mem_filter.mp hi).2]
  rw [hzero, zero_mul, Complex.zero_re] at hre
  have hpos : 0 < ∑ i ∈ univ with u i ^ a = u i₀ ^ a, m i * (1 + z.re) :=
    Finset.sum_pos (fun i _ => mul_pos (hm i) hrez)
      ⟨i₀, Finset.mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
  linarith

/-! ## Li's criterion along progressions below modulus `90` -/

/-- **Progressions through the band angle, abstract form.** For a conjugation-closed family of
non-real Cayley roots whose members outside the unit circle have argument at most `7/100`, the
paired Li sums at `ak + b` are negative for infinitely many `k`, whenever `1 ≤ a ≤ 89` and not
(`a ∣ 2b` and `a ∤ b`). -/
theorem frequently_progression_re_tsum_liTerm_neg {a b : ℕ} (ha : 1 ≤ a) (ha89 : a ≤ 89)
    (hb : ¬ (a ∣ 2 * b ∧ ¬ a ∣ b)) {ι : Type*} {v : ι → ℂ} {m : ι → ℝ} {M : ℝ}
    (hm : ∀ i, 1 ≤ m i) (hv : ∀ i, 1 ≤ ‖v i‖) (hM : ∀ i, ‖v i‖ ≤ M)
    (hs : Summable fun i => m i * ‖v i - 1‖ ^ (2 : ℕ))
    (σ : ι ≃ ι) (hσv : ∀ i, v (σ i) = (starRingEnd ℂ) (v i)) (hσm : ∀ i, m (σ i) = m i)
    (him : ∀ i, (v i).im ≠ 0)
    (hang : ∀ i, 1 < ‖v i‖ → |Complex.arg (v i)| ≤ 7 / 100) {i₀ : ι} (hlt : 1 < ‖v i₀‖) :
    ∃ᶠ k : ℕ in atTop, ∑' i, m i * (liTerm (v i) (a * k + b)).re < 0 := by
  classical
  obtain ⟨D, R, hDne, hR1, hDnorm, hdec⟩ := abs_re_tsum_liTerm_add_dominant_le hm hv hM hs hlt
  have hR0 : (0 : ℝ) < R := by linarith
  haveI : Nonempty {x // x ∈ D} := ⟨⟨hDne.choose, hDne.choose_spec⟩⟩
  set u : {x // x ∈ D} → ℂ := fun i => v i / R with hudef
  have hunit : ∀ i, ‖u i‖ = 1 := by
    intro i
    rw [hudef]; simp only
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR0, (hDnorm i).mp i.2,
      div_self hR0.ne']
  have huR : ∀ i, u i = ((R⁻¹ : ℝ) : ℂ) * v i := by
    intro i; rw [hudef]; simp only; rw [div_eq_inv_mul]; push_cast; ring
  have hargu : ∀ i, |Complex.arg (u i)| ≤ 7 / 100 := by
    intro i
    rw [huR i, Complex.arg_real_mul _ (inv_pos.mpr hR0)]
    exact hang i (by rw [(hDnorm i).mp i.2]; exact hR1)
  have himu : ∀ i, (u i).im ≠ 0 := by
    intro i
    rw [huR i, Complex.im_ofReal_mul]
    exact mul_ne_zero (inv_ne_zero hR0.ne') (him i)
  set σD : {x // x ∈ D} ≃ {x // x ∈ D} := σ.subtypeEquiv fun i => by
    rw [hDnorm i, hDnorm (σ i), hσv, Complex.norm_conj] with hσD
  have hσu : ∀ i, u (σD i) = (starRingEnd ℂ) (u i) := by
    intro i
    simp only [hudef, hσD, Equiv.subtypeEquiv_apply, hσv, map_div₀, Complex.conj_ofReal]
  have hσm' : ∀ i, (fun i : {x // x ∈ D} => m i) (σD i) = m i := by
    intro i
    simp only [hσD, Equiv.subtypeEquiv_apply, hσm]
  have hmpos : ∀ i : {x // x ∈ D}, 0 < (fun i : {x // x ∈ D} => m i) i := fun i => by
    simp only; linarith [hm i]
  have hroot : ∀ i, u i ^ a ≠ 1 := fun i =>
    pow_ne_one_of_abs_arg_le (hunit i) (himu i) (hargu i) ha ha89
  obtain ⟨i₁, hfib⟩ := exists_fibre_sum_ne_zero hunit hmpos hargu ha ha89 b hb
  obtain ⟨ε, cc, hε, hcc, N₀, hcount⟩ :=
    exists_card_filter_progression_gt u (fun i => m i) hunit hmpos σD hσu hσm' hroot b hfib
  obtain ⟨N₁, hN₁⟩ := hdec (ε / 2) (by linarith)
  have hf : ∀ n, ∑ i : {x // x ∈ D}, m i * (u i ^ n).re = ∑ i ∈ D, m i * ((v i / R) ^ n).re :=
    fun n => Finset.sum_coe_sort D (fun i => m i * ((v i / R) ^ n).re)
  rw [Filter.frequently_atTop]
  intro y₀
  set A : ℕ := y₀ + N₁ with hA
  obtain ⟨N, hN⟩ := exists_nat_gt (((A : ℝ) + 1) / cc + N₀)
  have hNN₀ : N₀ ≤ N := by
    have : (N₀ : ℝ) < N := by
      have : (0 : ℝ) ≤ ((A : ℝ) + 1) / cc := by positivity
      linarith
    exact_mod_cast this.le
  have h1 := hcount N hNN₀
  have hbig : A < ((range N).filter
      (fun k => ε < ∑ i : {x // x ∈ D}, m i * (u i ^ (b + a * k)).re)).card := by
    have h2 : (A : ℝ) + 1 < cc * N := by
      have : ((A : ℝ) + 1) / cc < N := by
        have : (0 : ℝ) ≤ (N₀ : ℝ) := Nat.cast_nonneg _
        linarith
      rwa [div_lt_iff₀ hcc, mul_comm] at this
    have : (A : ℝ) < (((range N).filter
        (fun k => ε < ∑ i : {x // x ∈ D}, m i * (u i ^ (b + a * k)).re)).card : ℝ) := by
      linarith
    exact_mod_cast this
  obtain ⟨k, hk, hkA⟩ : ∃ k ∈ (range N).filter
      (fun k => ε < ∑ i : {x // x ∈ D}, m i * (u i ^ (b + a * k)).re), A ≤ k := by
    by_contra hno
    push Not at hno
    have hsub : (range N).filter (fun k => ε < ∑ i : {x // x ∈ D}, m i * (u i ^ (b + a * k)).re)
        ⊆ range A := fun k hk => mem_range.mpr (hno k hk)
    have := card_le_card hsub
    rw [card_range] at this
    omega
  have hP' := (mem_filter.mp hk).2
  refine ⟨k, by omega, ?_⟩
  have hn : N₁ ≤ a * k + b := by nlinarith
  have hd := hN₁ _ hn
  rw [hf, show b + a * k = a * k + b by ring] at hP'
  have hRn : (0 : ℝ) < R ^ (a * k + b) := pow_pos hR0 _
  have h2 := (abs_le.mp hd).2
  have h3 := mul_pos hRn (sub_pos.mpr hP')
  nlinarith

/-- **Li's criterion along progressions below modulus `90`.** For `1 ≤ a ≤ 89` and every `b`
except `a` even with `b ≡ a/2 (mod a)`, the Riemann hypothesis holds iff `Re 2λ_{an+b} ≥ 0` for all
large `n`. -/
theorem riemannHypothesis_iff_eventually_re_xiLiPaired_progression_lt_90 {a b : ℕ} (ha : 1 ≤ a)
    (ha89 : a ≤ 89) (hb : ¬ (a ∣ 2 * b ∧ ¬ a ∣ b)) :
    RiemannHypothesis ↔ ∀ᶠ n : ℕ in atTop, 0 ≤ (xiLiPaired (a * n + b)).re := by
  constructor
  · intro hRH
    exact Filter.Eventually.of_forall fun x => re_xiLiPaired_nonneg_of_rh hRH _
  · intro h
    by_contra hRH
    obtain ⟨M, hmult, hvnorm, hvM, hsum, him, hbad⟩ := xiLi_family_facts
    obtain ⟨ρ₀, hρ₀⟩ := hbad hRH
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
    have hfreq := frequently_progression_re_tsum_liTerm_neg ha ha89 hb hmult hvnorm hvM hsum σ hσv
      hσm him (fun ρ hρ => abs_arg_xiRootV_le_of_one_lt ρ hρ) hρ₀
    obtain ⟨x, hx1, hx2⟩ := (hfreq.and_eventually h).exists
    rw [← re_xiLiPaired_eq_tsum_mult] at hx1
    linarith

/-! ## Geometric sequences: no band argument decides Li along `b^m` -/

theorem primitiveRootExp_mul_pow {p c : ℕ} (hp : 0 < p) (hc : 0 < c) :
    primitiveRootExp (p * c) ^ c = primitiveRootExp p := by
  unfold primitiveRootExp
  rw [← Complex.exp_nat_mul]
  congr 1
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hc0 : (c : ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  push_cast
  field_simp

/-- The scaled root family `e^{2πia/(pb^k)}`, `1 ≤ a < p`, sums to `−1` at every `b^m`, `m ≥ k`, when the
prime `p` does not divide `b`. -/
theorem sum_re_geometricRoot_pow {b p k m : ℕ} (hb : 2 ≤ b) (hp : p.Prime) (hpb : ¬ p ∣ b)
    (hkm : k ≤ m) :
    ∑ a ∈ Finset.Ico 1 p, ((primitiveRootExp (p * b ^ k) ^ a) ^ (b ^ m)).re = -1 := by
  have hbk : 0 < b ^ k := pow_pos (by omega) k
  have hroot := primitiveRootExp_mul_pow hp.pos hbk
  have hsplit : ∀ a, (primitiveRootExp (p * b ^ k) ^ a) ^ (b ^ m) =
      (primitiveRootExp p ^ a) ^ (b ^ (m - k)) := by
    intro a
    rw [← pow_mul, ← pow_mul, show b ^ m = b ^ k * b ^ (m - k) by
      rw [← pow_add, Nat.add_sub_cancel' hkm], show a * (b ^ k * b ^ (m - k)) =
        b ^ k * (a * b ^ (m - k)) by ring, pow_mul, hroot]
  simp_rw [hsplit]
  rw [← Complex.re_sum, sum_primitiveRootExp_pow_eq_neg_one hp.two_le]
  · simp
  · intro hdvd
    exact hpb (hp.dvd_of_dvd_pow hdvd)

/-- **Li along powers of `b` evades every band argument.** The family `R e^{±2πia/(pb^k)}`
(`1 ≤ a < p`, `p` prime, `p ∤ b`), closed under conjugation, has paired Li sum
`4(p−1) + 2(Rⁿ + R⁻ⁿ) > 0` at every index `n = b^m`, `m ≥ k`, and arguments at most `2π/b^k`. -/
theorem geometricRootFamily_re_liTerm_pos {b p k m : ℕ} (hb : 2 ≤ b) (hp : p.Prime)
    (hpb : ¬ p ∣ b) (hkm : k ≤ m) {R : ℝ} (hR : 0 < R) :
    0 < ∑ a ∈ Finset.Ico 1 p, ((liTerm ((R : ℂ) * primitiveRootExp (p * b ^ k) ^ a) (b ^ m)).re +
      (liTerm ((R : ℂ) * (starRingEnd ℂ) (primitiveRootExp (p * b ^ k) ^ a)) (b ^ m)).re) := by
  have hq : 2 ≤ p * b ^ k := by
    have := hp.two_le
    have : 1 ≤ b ^ k := Nat.one_le_pow _ _ (by omega)
    nlinarith
  have hprim : IsPrimitiveRoot (primitiveRootExp (p * b ^ k)) (p * b ^ k) :=
    Complex.isPrimitiveRoot_exp _ (by omega)
  have hnorm : ∀ a, ‖primitiveRootExp (p * b ^ k) ^ a‖ = 1 := fun a => by
    rw [norm_pow, hprim.norm'_eq_one (by omega), one_pow]
  have hnormc : ∀ a, ‖(starRingEnd ℂ) (primitiveRootExp (p * b ^ k) ^ a)‖ = 1 := fun a => by
    rw [Complex.norm_conj, hnorm]
  have hterm : ∀ a, (liTerm ((R : ℂ) * primitiveRootExp (p * b ^ k) ^ a) (b ^ m)).re +
      (liTerm ((R : ℂ) * (starRingEnd ℂ) (primitiveRootExp (p * b ^ k) ^ a)) (b ^ m)).re =
      4 - 2 * (R ^ (b ^ m) + (R⁻¹) ^ (b ^ m)) *
        ((primitiveRootExp (p * b ^ k) ^ a) ^ (b ^ m)).re := by
    intro a
    rw [re_liTerm_ofReal_mul_unit (hnorm a) hR, re_liTerm_ofReal_mul_unit (hnormc a) hR,
      ← map_pow, Complex.conj_re]
    ring
  rw [Finset.sum_congr rfl fun a _ => hterm a, Finset.sum_sub_distrib, ← Finset.mul_sum,
    sum_re_geometricRoot_pow hb hp hpb hkm]
  simp only [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  have h1 : 0 < R ^ (b ^ m) := pow_pos hR _
  have h2 : 0 < (R⁻¹) ^ (b ^ m) := pow_pos (inv_pos.mpr hR) _
  have hp1 : (1 : ℝ) ≤ ((p - 1 : ℕ) : ℝ) := by
    have := hp.two_le
    exact_mod_cast (by omega : 1 ≤ p - 1)
  nlinarith

/-- The arguments of the geometric root family are at most `2π/b^k`. -/
theorem abs_arg_geometricRoot_le {b p k a : ℕ} (hb : 2 ≤ b) (hk : 1 ≤ k) (hp : p.Prime)
    (ha : a < p) :
    |Complex.arg (primitiveRootExp (p * b ^ k) ^ a)| ≤ 2 * Real.pi / b ^ k := by
  have hπ := Real.pi_pos
  have hbk : (2 : ℝ) ≤ (b : ℝ) ^ k := by
    have : 2 ≤ b ^ k := le_trans hb (Nat.le_self_pow (by omega) b)
    exact_mod_cast this
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpa : (a : ℝ) < p := by exact_mod_cast ha
  have ha0 : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have harg : primitiveRootExp (p * b ^ k) ^ a =
      Complex.exp (((2 * Real.pi * a / (p * (b : ℝ) ^ k) : ℝ) : ℂ) * I) := by
    unfold primitiveRootExp
    rw [← Complex.exp_nat_mul]
    congr 1
    have hp0' : (p : ℂ) ≠ 0 := by exact_mod_cast hp.pos.ne'
    have hb0 : (b : ℂ) ≠ 0 := by exact_mod_cast (by omega : b ≠ 0)
    push_cast
    field_simp
  have hx0 : 0 ≤ 2 * Real.pi * a / (p * (b : ℝ) ^ k) := by positivity
  have hx1 : 2 * Real.pi * a / (p * (b : ℝ) ^ k) ≤ 2 * Real.pi / b ^ k := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) hπ) (by positivity : (0:ℝ) < (b : ℝ) ^ k)]
  have hxπ : 2 * Real.pi / b ^ k ≤ Real.pi := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  have ht : toIocMod Real.two_pi_pos (-Real.pi) (2 * Real.pi * a / (p * (b : ℝ) ^ k)) =
      2 * Real.pi * a / (p * (b : ℝ) ^ k) := by
    rw [toIocMod_eq_self]; constructor <;> linarith
  rw [harg, Complex.arg_exp_mul_I, ht, abs_of_nonneg hx0]
  exact hx1

end RHTower

end
