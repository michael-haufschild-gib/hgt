import Mathlib.Analysis.InnerProductSpace.Projection.Minimal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse

/-!
# The finite Pechersky lemma: unimodular combinations are dense

Let `x : ℕ → H` be a sequence in a complex Hilbert space with `Σ ‖x n‖² < ∞`, and suppose that for
every `e ≠ 0` the partial sums `Σ_{n<N} |⟪x n, e⟫|` are unbounded.  Then for every `h ∈ H`, every
`ε > 0` and every `N₀` there are `N ≥ N₀` and unimodular coefficients `a n` with
`‖h − Σ_{n<N} a n • x n‖ < ε`  (`exists_unimodular_finite_approx`).

The proof has three steps.
* **Disc hull density** (`dense_discHull`): the convex set of finite sums `Σ c n • x n` with
  `|c n| ≤ 1` is dense, since a vector outside its closure would be separated from it by the
  nearest-point vector `e`, and `Re ⟪e, Σ c n • x n⟫` reaches `Σ |⟪e, x n⟫|` on the hull.
* **Greedy sign rounding** (`exists_signs_norm_sum_sq_le`): signs `±1` chosen one at a time against
  the running sum keep every partial sum of `Σ s n • w n` inside norm `(Σ ‖w n‖²)^{1/2}`.
* **Unimodular rounding** (`exists_unimodular_round`): a coefficient in the closed unit disc is the
  midpoint of two unit phases, so disc coefficients can be moved to the circle at a cost controlled
  by the greedy rounding.

Applied to a tail of the sequence, whose squared norms are small, this gives the finite lemma.
-/

open Filter Topology Finset
open scoped InnerProductSpace ComplexConjugate

namespace RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## Greedy sign rounding -/

/-- One greedy step: a sign `±1` against `Re ⟪S, w⟫` makes the cross term nonpositive. -/
theorem exists_sign_norm_add_smul_sq_le (S w : H) :
    ∃ s : ℂ, (s = 1 ∨ s = -1) ∧ ‖S + s • w‖ ^ 2 ≤ ‖S‖ ^ 2 + ‖w‖ ^ 2 := by
  by_cases h : 0 ≤ (⟪S, w⟫_ℂ).re
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul, norm_neg, norm_one, one_mul]
    simp only [RCLike.re_to_complex, neg_one_mul, Complex.neg_re]
    linarith
  · refine ⟨1, Or.inl rfl, ?_⟩
    rw [norm_add_sq (𝕜 := ℂ), inner_smul_right, norm_smul, norm_one, one_mul]
    simp only [RCLike.re_to_complex, one_mul]
    simp only [not_le] at h
    linarith

/-- **Greedy sign rounding.**  Signs `±1` can be chosen so that every partial sum of `Σ s n • w n`
has squared norm at most the partial sum of the squared norms. -/
theorem exists_signs_norm_sum_sq_le (w : ℕ → H) (N : ℕ) :
    ∃ s : ℕ → ℂ, (∀ n, s n = 1 ∨ s n = -1) ∧
      ∀ m ≤ N, ‖∑ n ∈ range m, s n • w n‖ ^ 2 ≤ ∑ n ∈ range m, ‖w n‖ ^ 2 := by
  induction N with
  | zero =>
    refine ⟨fun _ => 1, fun _ => Or.inl rfl, fun m hm => ?_⟩
    rw [Nat.le_zero.mp hm]
    simp
  | succ N ih =>
    obtain ⟨s, hs, hbound⟩ := ih
    obtain ⟨σ, hσ, hσle⟩ := exists_sign_norm_add_smul_sq_le (∑ n ∈ range N, s n • w n) (w N)
    have hagree : ∀ m ≤ N, ∑ n ∈ range m, Function.update s N σ n • w n
        = ∑ n ∈ range m, s n • w n := fun m hm =>
      sum_congr rfl fun n hn => by
        rw [Function.update_of_ne (by have := mem_range.mp hn; omega)]
    refine ⟨Function.update s N σ, fun n => ?_, fun m hm => ?_⟩
    · by_cases hn : n = N
      · subst hn
        simpa using hσ
      · rw [Function.update_of_ne hn]
        exact hs n
    · rcases Nat.lt_or_ge m (N + 1) with hlt | hge
      · rw [hagree m (Nat.lt_succ_iff.mp hlt)]
        exact hbound m (Nat.lt_succ_iff.mp hlt)
      · have hmN : m = N + 1 := le_antisymm hm hge
        subst hmN
        rw [sum_range_succ, sum_range_succ, Function.update_self, hagree N le_rfl]
        linarith [hbound N le_rfl]

/-! ## Unimodular rounding -/

/-- A point of the closed unit disc is the midpoint of two points of the unit circle. -/
theorem exists_unit_pair_midpoint (c : ℂ) (hc : ‖c‖ ≤ 1) :
    ∃ a b : ℂ, ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ c = (a + b) / 2 := by
  set θ : ℝ := Complex.arg c
  set φ : ℝ := Real.arccos ‖c‖
  refine ⟨Complex.exp (((θ + φ : ℝ) : ℂ) * Complex.I), Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I),
    Complex.norm_exp_ofReal_mul_I _, Complex.norm_exp_ofReal_mul_I _, ?_⟩
  have h1 : (‖c‖ : ℂ) = Complex.cos (φ : ℂ) := by
    rw [← Complex.ofReal_cos, Real.cos_arccos (by linarith [norm_nonneg c]) hc]
  have h2 : (2 : ℂ) * Complex.cos (φ : ℂ)
      = Complex.exp ((φ : ℂ) * Complex.I) + Complex.exp (-(φ : ℂ) * Complex.I) :=
    Complex.two_cos _
  have hθ : Complex.exp (((θ + φ : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp ((φ : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    push_cast
    ring_nf
  have hθ' : Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I)
      = Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (-(φ : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    push_cast
    ring_nf
  calc c = (‖c‖ : ℂ) * Complex.exp ((θ : ℂ) * Complex.I) :=
        (Complex.norm_mul_exp_arg_mul_I c).symm
    _ = (Complex.exp ((θ : ℂ) * Complex.I) * (2 * Complex.cos (φ : ℂ))) / 2 := by
        rw [h1]; ring
    _ = (Complex.exp (((θ + φ : ℝ) : ℂ) * Complex.I)
          + Complex.exp (((θ - φ : ℝ) : ℂ) * Complex.I)) / 2 := by
        rw [h2, hθ, hθ']; ring

/-- **Unimodular rounding.**  Coefficients in the closed unit disc can be replaced by unimodular
ones so that every partial sum moves by at most `(Σ ‖x n‖²)^{1/2}`. -/
theorem exists_unimodular_round (x : ℕ → H) (c : ℕ → ℂ) (hc : ∀ n, ‖c n‖ ≤ 1) (N : ℕ) :
    ∃ a : ℕ → ℂ, (∀ n, ‖a n‖ = 1) ∧
      ∀ m ≤ N, ‖∑ n ∈ range m, a n • x n - ∑ n ∈ range m, c n • x n‖ ^ 2
        ≤ ∑ n ∈ range m, ‖x n‖ ^ 2 := by
  choose u v hu hv huv using fun n => exists_unit_pair_midpoint (c n) (hc n)
  set d : ℕ → ℂ := fun n => (u n - v n) / 2 with hd
  have hdn : ∀ n, ‖d n‖ ≤ 1 := fun n => by
    simp only [hd, norm_div, Complex.norm_two]
    have := norm_sub_le (u n) (v n)
    rw [hu n, hv n] at this
    linarith
  obtain ⟨s, hs, hbound⟩ := exists_signs_norm_sum_sq_le (fun n => d n • x n) N
  refine ⟨fun n => c n + s n * d n, fun n => ?_, fun m hm => ?_⟩
  · show ‖c n + s n * d n‖ = 1
    rcases hs n with h | h
    · have : c n + s n * d n = u n := by rw [h, huv n, hd]; ring
      rw [this]; exact hu n
    · have : c n + s n * d n = v n := by rw [h, huv n, hd]; ring
      rw [this]; exact hv n
  · show ‖∑ n ∈ range m, (c n + s n * d n) • x n - ∑ n ∈ range m, c n • x n‖ ^ 2
      ≤ ∑ n ∈ range m, ‖x n‖ ^ 2
    have hsplit : ∑ n ∈ range m, (c n + s n * d n) • x n - ∑ n ∈ range m, c n • x n
        = ∑ n ∈ range m, s n • (d n • x n) := by
      rw [← sum_sub_distrib]
      refine sum_congr rfl fun n _ => ?_
      rw [add_smul, mul_smul]
      abel
    rw [hsplit]
    refine (hbound m hm).trans (sum_le_sum fun n _ => ?_)
    rw [norm_smul, mul_pow]
    have h0 : 0 ≤ ‖x n‖ ^ 2 := by positivity
    have h1 : ‖d n‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (hdn n)
    nlinarith

/-! ## Density of the disc hull -/

/-- The finite combinations `Σ_{n<N} c n • x n` with coefficients in the closed unit disc. -/
def discHull (x : ℕ → H) : Set H :=
  {v | ∃ N : ℕ, ∃ c : ℕ → ℂ, (∀ n, ‖c n‖ ≤ 1) ∧ v = ∑ n ∈ range N, c n • x n}

theorem zero_mem_discHull (x : ℕ → H) : (0 : H) ∈ discHull x :=
  ⟨0, fun _ => 0, fun _ => by simp, by simp⟩

/-- A combination over `range N` is a combination over any longer range (zero padding). -/
theorem sum_range_eq_sum_range_pad (x : ℕ → H) (c : ℕ → ℂ) {N M : ℕ} (hNM : N ≤ M) :
    ∑ n ∈ range N, c n • x n = ∑ n ∈ range M, (if n < N then c n else 0) • x n := by
  have h1 : ∑ n ∈ range N, c n • x n = ∑ n ∈ range N, (if n < N then c n else 0) • x n :=
    sum_congr rfl fun n hn => by rw [if_pos (mem_range.mp hn)]
  rw [h1]
  refine sum_subset (Finset.range_mono hNM) fun n _ hn => ?_
  rw [if_neg (fun h => hn (mem_range.mpr h)), zero_smul]

theorem convex_discHull (x : ℕ → H) : Convex ℝ (discHull x) := by
  intro v hv w hw a b ha hb hab
  obtain ⟨N, c, hc, rfl⟩ := hv
  obtain ⟨M, e, he, rfl⟩ := hw
  refine ⟨max N M, fun n => (a : ℂ) * (if n < N then c n else 0) + (b : ℂ) * (if n < M then e n else 0),
    fun n => ?_, ?_⟩
  · have h1 : ‖(if n < N then c n else 0 : ℂ)‖ ≤ 1 := by
      split_ifs
      · exact hc n
      · simp
    have h2 : ‖(if n < M then e n else 0 : ℂ)‖ ≤ 1 := by
      split_ifs
      · exact he n
      · simp
    calc ‖(a : ℂ) * (if n < N then c n else 0) + (b : ℂ) * (if n < M then e n else 0)‖
        ≤ ‖(a : ℂ) * (if n < N then c n else 0)‖ + ‖(b : ℂ) * (if n < M then e n else 0)‖ :=
          norm_add_le _ _
      _ = a * ‖(if n < N then c n else 0 : ℂ)‖ + b * ‖(if n < M then e n else 0 : ℂ)‖ := by
          rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg ha,
            Real.norm_of_nonneg hb]
      _ ≤ a * 1 + b * 1 := by gcongr
      _ = 1 := by linarith
  · rw [sum_range_eq_sum_range_pad x c (le_max_left N M),
      sum_range_eq_sum_range_pad x e (le_max_right N M), smul_sum, smul_sum, ← sum_add_distrib]
    refine sum_congr rfl fun n _ => ?_
    rw [add_smul, ← Complex.coe_smul, ← Complex.coe_smul, smul_smul, smul_smul]

/-- A disc coefficient aligning `⟪e, x⟫` with the positive real axis. -/
theorem exists_disc_coeff_align (z : ℂ) : ∃ c : ℂ, ‖c‖ ≤ 1 ∧ c * z = (‖z‖ : ℂ) := by
  by_cases hz : z = 0
  · exact ⟨0, by simp, by simp [hz]⟩
  · refine ⟨conj z / (‖z‖ : ℂ), ?_, ?_⟩
    · rw [norm_div, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr hz)]
    · have hz' : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hz
      rw [div_mul_eq_mul_div, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
      push_cast
      field_simp

/-- **Density of the disc hull.**  If the partial sums `Σ_{n<N} ‖⟪x n, e⟫‖` are unbounded for every
`e ≠ 0`, the disc hull of `x` is dense. -/
theorem dense_discHull [CompleteSpace H] (x : ℕ → H)
    (hdiv : ∀ e : H, e ≠ 0 → ∀ M : ℝ, ∃ N : ℕ, M < ∑ n ∈ range N, ‖⟪x n, e⟫_ℂ‖) :
    Dense (discHull x) := by
  letI : InnerProductSpace ℝ H := InnerProductSpace.complexToReal
  rw [dense_iff_closure_eq]
  by_contra hne
  obtain ⟨h, hh⟩ : ∃ h : H, h ∉ closure (discHull x) := by
    by_contra hall
    simp only [not_exists, not_not] at hall
    exact hne (Set.eq_univ_of_forall hall)
  have hconv : Convex ℝ (closure (discHull x)) := (convex_discHull x).closure
  obtain ⟨q, hq, hqmin⟩ := exists_norm_eq_iInf_of_complete_convex
    ⟨0, subset_closure (zero_mem_discHull x)⟩ isClosed_closure.isComplete hconv h
  rw [norm_eq_iInf_iff_real_inner_le_zero hconv hq] at hqmin
  have he : h - q ≠ 0 := sub_ne_zero.mpr fun hqe => hh (hqe ▸ hq)
  -- every hull element `w` satisfies `Re ⟪h − q, w⟫ ≤ Re ⟪h − q, q⟫`
  have hsep : ∀ w ∈ discHull x, (⟪h - q, w⟫_ℂ).re ≤ (⟪h - q, q⟫_ℂ).re := by
    intro w hw
    have := hqmin w (subset_closure hw)
    rw [real_inner_eq_re_inner ℂ, inner_sub_right, RCLike.re_to_complex, Complex.sub_re] at this
    linarith
  -- aligned coefficients make `Re ⟪h − q, Σ c n • x n⟫ = Σ ‖⟪h − q, x n⟫‖`
  choose c hc hcalign using fun n => exists_disc_coeff_align ⟪h - q, x n⟫_ℂ
  obtain ⟨N, hN⟩ := hdiv (h - q) he (⟪h - q, q⟫_ℂ).re
  have hw : ∑ n ∈ range N, c n • x n ∈ discHull x := ⟨N, c, hc, rfl⟩
  have hval : (⟪h - q, ∑ n ∈ range N, c n • x n⟫_ℂ).re = ∑ n ∈ range N, ‖⟪x n, h - q⟫_ℂ‖ := by
    rw [inner_sum, Complex.re_sum]
    refine sum_congr rfl fun n _ => ?_
    rw [inner_smul_right, hcalign n, Complex.ofReal_re, norm_inner_symm]
  have := hsep _ hw
  rw [hval] at this
  linarith

/-! ## The finite Pechersky lemma -/

/-- **Finite Pechersky lemma.**  For a square-summable sequence whose inner products with every
nonzero vector have unbounded partial absolute sums, every vector is approximated by a finite
unimodular combination `Σ_{n<N} a n • x n` with `N` as large as desired. -/
theorem exists_unimodular_finite_approx [CompleteSpace H] (x : ℕ → H)
    (hsum : Summable fun n => ‖x n‖ ^ 2)
    (hdiv : ∀ e : H, e ≠ 0 → ∀ M : ℝ, ∃ N : ℕ, M < ∑ n ∈ range N, ‖⟪x n, e⟫_ℂ‖)
    (h : H) {ε : ℝ} (hε : 0 < ε) (N₀ : ℕ) :
    ∃ N : ℕ, N₀ ≤ N ∧ ∃ a : ℕ → ℂ, (∀ n, ‖a n‖ = 1) ∧
      ‖h - ∑ n ∈ range N, a n • x n‖ < ε := by
  -- a tail with small squared norms
  have htail := (tendsto_sum_nat_add fun n => ‖x n‖ ^ 2).eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < (ε / 2) ^ 2))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp htail
  set N₁' : ℕ := max N₀ N₁ with hN₁'
  have htail' : ∑' k, ‖x (k + N₁')‖ ^ 2 < (ε / 2) ^ 2 := hN₁ _ (le_max_right _ _)
  set x' : ℕ → H := fun n => x (n + N₁') with hx'
  -- the divergence hypothesis passes to the tail
  have hdiv' : ∀ e : H, e ≠ 0 → ∀ M : ℝ, ∃ N : ℕ, M < ∑ n ∈ range N, ‖⟪x' n, e⟫_ℂ‖ := by
    intro e he M
    obtain ⟨N, hN⟩ := hdiv e he (M + ∑ n ∈ range N₁', ‖⟪x n, e⟫_ℂ‖)
    refine ⟨N, ?_⟩
    have h1 : ∑ n ∈ range (N₁' + N), ‖⟪x n, e⟫_ℂ‖
        = ∑ n ∈ range N₁', ‖⟪x n, e⟫_ℂ‖ + ∑ n ∈ range N, ‖⟪x' n, e⟫_ℂ‖ := by
      rw [sum_range_add]
      congr 1
      refine sum_congr rfl fun n _ => ?_
      rw [hx', add_comm]
    have h2 : ∑ n ∈ range N, ‖⟪x n, e⟫_ℂ‖ ≤ ∑ n ∈ range (N₁' + N), ‖⟪x n, e⟫_ℂ‖ :=
      sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        fun _ _ _ => norm_nonneg _
    linarith
  -- approximate the residual target in the hull of the tail
  set h' : H := h - ∑ n ∈ range N₁', x n with hh'
  have hmem : h' ∈ closure (discHull x') := by
    rw [(dense_discHull x' hdiv').closure_eq]
    exact Set.mem_univ _
  obtain ⟨w, hw, hdist⟩ := Metric.mem_closure_iff.mp hmem (ε / 2) (half_pos hε)
  obtain ⟨N₂, c, hc, rfl⟩ := hw
  -- round to unimodular coefficients
  obtain ⟨a', ha', hround⟩ := exists_unimodular_round x' c hc N₂
  have hr : ‖∑ n ∈ range N₂, a' n • x' n - ∑ n ∈ range N₂, c n • x' n‖ < ε / 2 := by
    have h1 := hround N₂ le_rfl
    have h2 : ∑ n ∈ range N₂, ‖x' n‖ ^ 2 ≤ ∑' k, ‖x (k + N₁')‖ ^ 2 :=
      ((summable_nat_add_iff N₁').mpr hsum).sum_le_tsum _ fun _ _ => by positivity
    have h3 : ‖∑ n ∈ range N₂, a' n • x' n - ∑ n ∈ range N₂, c n • x' n‖ ^ 2 < (ε / 2) ^ 2 := by
      linarith
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) h3
  refine ⟨N₁' + N₂, by omega, fun n => if n < N₁' then 1 else a' (n - N₁'), fun n => ?_, ?_⟩
  · show ‖(if n < N₁' then (1 : ℂ) else a' (n - N₁'))‖ = 1
    split_ifs
    · simp
    · exact ha' _
  · rw [sum_range_add]
    have hfirst : ∑ n ∈ range N₁', (if n < N₁' then (1 : ℂ) else a' (n - N₁')) • x n
        = ∑ n ∈ range N₁', x n :=
      sum_congr rfl fun n hn => by rw [if_pos (mem_range.mp hn), one_smul]
    have hsecond : ∑ n ∈ range N₂,
        (if N₁' + n < N₁' then (1 : ℂ) else a' (N₁' + n - N₁')) • x (N₁' + n)
        = ∑ n ∈ range N₂, a' n • x' n :=
      sum_congr rfl fun n _ => by
        rw [if_neg (by omega), Nat.add_sub_cancel_left, hx', add_comm]
    rw [hfirst, hsecond]
    rw [dist_eq_norm] at hdist
    calc ‖h - (∑ n ∈ range N₁', x n + ∑ n ∈ range N₂, a' n • x' n)‖
        = ‖(h' - ∑ n ∈ range N₂, c n • x' n)
            - (∑ n ∈ range N₂, a' n • x' n - ∑ n ∈ range N₂, c n • x' n)‖ := by
          rw [hh']
          congr 1
          abel
      _ ≤ ‖h' - ∑ n ∈ range N₂, c n • x' n‖
            + ‖∑ n ∈ range N₂, a' n • x' n - ∑ n ∈ range N₂, c n • x' n‖ := norm_sub_le _ _
      _ < ε / 2 + ε / 2 := add_lt_add hdist hr
      _ = ε := by ring

end RHTower
