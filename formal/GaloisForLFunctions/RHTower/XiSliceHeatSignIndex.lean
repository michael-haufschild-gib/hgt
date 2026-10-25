import GaloisForLFunctions.RHTower.XiSliceHeatHeightPositiveDefinite
import GaloisForLFunctions.RHTower.XiSliceHeatOrderUniformPositivity
import GaloisForLFunctions.RHTower.XiSliceHeatThresholdTouching

/-!
# The sign index of the heated slice is quantized and antitone in the heat

Let `T_n(λ, 0, t)` be the heated slice coefficients.  Count the strict sign changes of
`n ↦ T_{2n}(λ, 0, t)` by chains of indices along which the values alternate strictly in sign
(`HasSignChanges`).

**Variation diminishing** (`hasSignChanges_xiSliceHeat_of_le`).  For `0 ≤ λ ≤ λ'`, every chain of
`k` sign changes at heat `λ'` gives one at heat `λ`.  With `a_n = (2n)! T_{2n}` the heat shift reads
`a_n(λ') = Σ_j c^j/j! · a_{n+j}(λ)`, `c = (λ' − λ)/2`: the exponential `e^{cS}` of the left shift,
the limit of `(1 + (c/N) S)^N`.  One bidiagonal step `f_n + ε f_{n+1}`, `ε ≥ 0`, creates no sign
change (`hasSignChanges_of_bidiag`), and strict alternation survives pointwise limits.

**Quantization and range** (`exists_xiSliceHeat_signIndex_bounds`).  At `0 < λ ≤ 1` the first value
`T_0` and every `T_{2n}` with `n ≥ C/λ` are positive, so chains have length at most `⌈C/λ⌉`, and an
odd chain always extends to an even one: the index is even.  It vanishes exactly when every heated
coefficient is nonnegative (`not_hasSignChanges_one_iff`).
-/

open Complex Filter Topology
open scoped ComplexOrder

namespace RHTower.DeBruijn

noncomputable section

/-! ## Strict sign changes of a real sequence -/

/-- `f` has at least `k` strict sign changes: indices `q 0 < q 1 < ⋯ < q k` along which
consecutive values have strictly opposite signs. -/
def HasSignChanges (f : ℕ → ℝ) (k : ℕ) : Prop :=
  ∃ q : ℕ → ℕ, ∀ i < k, q i < q (i + 1) ∧ f (q i) * f (q (i + 1)) < 0

/-- **One bidiagonal step creates no sign change.**  A nonzero value `f n + w n f (n+1)`,
`w n ≥ 0`, has the strict sign of `f n` or of `f (n+1)`; the chosen witnesses increase strictly. -/
theorem hasSignChanges_of_bidiag {f w : ℕ → ℝ} (hw : ∀ n, 0 ≤ w n) {k : ℕ}
    (h : HasSignChanges (fun n => f n + w n * f (n + 1)) k) : HasSignChanges f k := by
  classical
  obtain ⟨q, hq⟩ := h
  set g : ℕ → ℝ := fun n => f n + w n * f (n + 1) with hg
  set r : ℕ → ℕ := fun n => if 0 < f n * g n then n else n + 1 with hr
  have hwit : ∀ n, g n ≠ 0 → 0 < f (r n) * g n := by
    intro n hn
    by_cases hpos : 0 < f n * g n
    · simp [hr, hpos]
    · simp only [hr, hpos, if_false]
      have hsq : 0 < g n * g n := mul_self_pos.mpr hn
      have he : g n * g n = f n * g n + w n * (f (n + 1) * g n) := by simp only [hg]; ring
      by_contra hneg
      have h1 : w n * (f (n + 1) * g n) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (hw n) (not_lt.mp hneg)
      linarith [not_lt.mp hpos]
  have hrle : ∀ n, n ≤ r n ∧ r n ≤ n + 1 := fun n => by
    by_cases hpos : 0 < f n * g n <;> simp [hr, hpos]
  refine ⟨fun i => r (q i), fun i hi => ?_⟩
  obtain ⟨hlt, hneg⟩ := hq i hi
  have hg1 : g (q i) ≠ 0 := fun h0 => by simp [h0] at hneg
  have hg2 : g (q (i + 1)) ≠ 0 := fun h0 => by simp [h0] at hneg
  have hA := hwit _ hg1
  have hB := hwit _ hg2
  have hsign : f (r (q i)) * f (r (q (i + 1))) < 0 := by
    have hprod := mul_pos hA hB
    have e : f (r (q i)) * g (q i) * (f (r (q (i + 1))) * g (q (i + 1))) =
        (f (r (q i)) * f (r (q (i + 1)))) * (g (q i) * g (q (i + 1))) := by ring
    rw [e] at hprod
    by_contra hc
    exact absurd hprod (not_lt.mpr (mul_nonpos_of_nonneg_of_nonpos (not_lt.mp hc) hneg.le))
  refine ⟨?_, hsign⟩
  have hle : r (q i) ≤ r (q (i + 1)) := by
    have := hrle (q i); have := hrle (q (i + 1)); omega
  refine lt_of_le_of_ne hle fun heq => ?_
  change r (q i) = r (q (i + 1)) at heq
  rw [heq] at hsign
  exact absurd hsign (not_lt.mpr (mul_self_nonneg _))

/-- The bidiagonal step `f ↦ f n + ε f (n+1)`. -/
def bidiag (ε : ℝ) (f : ℕ → ℝ) : ℕ → ℝ := fun n => f n + ε * f (n + 1)

theorem hasSignChanges_of_iterate_bidiag {ε : ℝ} (hε : 0 ≤ ε) {k : ℕ} :
    ∀ (N : ℕ) {f : ℕ → ℝ}, HasSignChanges ((bidiag ε)^[N] f) k → HasSignChanges f k
  | 0, _, h => h
  | N + 1, f, h => by
    rw [Function.iterate_succ_apply'] at h
    exact hasSignChanges_of_iterate_bidiag hε N
      (hasSignChanges_of_bidiag (w := fun _ => ε) (fun _ => hε) h)

/-- `(1 + εS)^N` written out: `Σ_j C(N, j) ε^j f (n + j)`. -/
theorem iterate_bidiag_apply (ε : ℝ) (f : ℕ → ℝ) (N : ℕ) : ∀ n : ℕ,
    (bidiag ε)^[N] f n = ∑ j ∈ Finset.range (N + 1), (N.choose j : ℝ) * ε ^ j * f (n + j) := by
  induction N with
  | zero => intro n; simp
  | succ N ih =>
    intro n
    rw [Function.iterate_succ_apply']
    change (bidiag ε)^[N] f n + ε * (bidiag ε)^[N] f (n + 1) = _
    rw [ih n, ih (n + 1), Finset.sum_range_succ' _ (N + 1)]
    simp only [Nat.choose_succ_succ', Nat.cast_add, add_mul, Finset.sum_add_distrib]
    rw [Finset.mul_sum, Finset.sum_range_succ' (fun j => (N.choose j : ℝ) * ε ^ j * f (n + j)),
      Finset.sum_range_succ (fun j => (N.choose (j + 1) : ℝ) * ε ^ (j + 1) * f (n + (j + 1))),
      Nat.choose_succ_self, Nat.cast_zero, zero_mul, zero_mul, add_zero]
    simp only [Nat.choose_zero_right, Nat.cast_one, pow_zero, one_mul, add_zero, pow_succ]
    have e : ∀ j, ε * ((N.choose j : ℝ) * ε ^ j * f (n + 1 + j)) =
        (N.choose j : ℝ) * (ε ^ j * ε) * f (n + (j + 1)) := fun j => by
      rw [show n + 1 + j = n + (j + 1) by ring]; ring
    simp only [e]
    ring

/-- Strict sign changes persist under pointwise limits. -/
theorem eventually_hasSignChanges_of_tendsto {α : Type*} {l : Filter α} {F : α → ℕ → ℝ}
    {f : ℕ → ℝ} (hF : ∀ n, Tendsto (fun a => F a n) l (𝓝 (f n))) {k : ℕ}
    (h : HasSignChanges f k) : ∀ᶠ a in l, HasSignChanges (F a) k := by
  obtain ⟨q, hq⟩ := h
  have hev : ∀ i ∈ Finset.range k, ∀ᶠ a in l, F a (q i) * F a (q (i + 1)) < 0 := fun i hi =>
    ((hF (q i)).mul (hF (q (i + 1)))).eventually (gt_mem_nhds (hq i (Finset.mem_range.mp hi)).2)
  filter_upwards [(Finset.eventually_all (Finset.range k)).mpr hev] with a ha
  exact ⟨q, fun i hi => ⟨(hq i hi).1, ha i (Finset.mem_range.mpr hi)⟩⟩

theorem choose_mul_div_pow_le {c : ℝ} (hc : 0 ≤ c) (N j : ℕ) :
    (N.choose j : ℝ) * (c / N) ^ j ≤ c ^ j / j.factorial := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · rcases Nat.eq_zero_or_pos j with rfl | hj
    · simp
    · rw [Nat.choose_eq_zero_of_lt hj, Nat.cast_zero, zero_mul]; positivity
  · have hN' : (0 : ℝ) < N := by exact_mod_cast hN
    have hdesc : (N.choose j : ℝ) * j.factorial ≤ (N : ℝ) ^ j := by
      have h := Nat.descFactorial_le_pow N j
      rw [Nat.descFactorial_eq_factorial_mul_choose, mul_comm] at h
      exact_mod_cast h
    rw [div_pow, ← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
    have := mul_le_mul_of_nonneg_left hdesc (pow_nonneg hc j)
    nlinarith [this]

theorem tendsto_choose_mul_div_pow (c : ℝ) (j : ℕ) :
    Tendsto (fun N : ℕ => (N.choose j : ℝ) * (c / N) ^ j) atTop (𝓝 (c ^ j / j.factorial)) := by
  have hequiv := (isEquivalent_choose j).mul
    (Asymptotics.IsEquivalent.refl (u := fun N : ℕ => (c / N) ^ j) (l := atTop))
  refine hequiv.symm.tendsto_nhds ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with N hN
  have hN' : (N : ℝ) ≠ 0 := by positivity
  simp only [Pi.mul_apply]
  rw [div_pow]
  field_simp

/-- **The exponential of the left shift diminishes variation.**  If
`g n = Σ_j c^j/j! f (n + j)`, `c ≥ 0`, with absolutely convergent series, every chain of `k`
strict sign changes of `g` gives one of `f`. -/
theorem hasSignChanges_of_expShift {c : ℝ} (hc : 0 ≤ c) {f g : ℕ → ℝ}
    (hs : ∀ n, Summable fun j => c ^ j / j.factorial * |f (n + j)|)
    (hg : ∀ n, g n = ∑' j, c ^ j / j.factorial * f (n + j)) {k : ℕ}
    (h : HasSignChanges g k) : HasSignChanges f k := by
  have hlim : ∀ n, Tendsto (fun N : ℕ => (bidiag (c / N))^[N] f n) atTop (𝓝 (g n)) := by
    intro n
    rw [hg n]
    have hfin : ∀ N : ℕ, (bidiag (c / N))^[N] f n =
        ∑' j, (N.choose j : ℝ) * (c / N) ^ j * f (n + j) := by
      intro N
      rw [iterate_bidiag_apply, tsum_eq_sum (s := Finset.range (N + 1))]
      intro j hj
      rw [Finset.mem_range, not_lt] at hj
      rw [Nat.choose_eq_zero_of_lt (by omega), Nat.cast_zero, zero_mul, zero_mul]
    simp_rw [hfin]
    refine tendsto_tsum_of_dominated_convergence (hs n) (fun j => ?_) ?_
    · exact (tendsto_choose_mul_div_pow c j).mul tendsto_const_nhds
    · refine Eventually.of_forall fun N j => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
      exact mul_le_mul_of_nonneg_right (choose_mul_div_pow_le hc N j) (abs_nonneg _)
  obtain ⟨N, hN⟩ := (eventually_hasSignChanges_of_tendsto hlim h).exists
  exact hasSignChanges_of_iterate_bidiag (div_nonneg hc (Nat.cast_nonneg N)) N hN


/-- Rescaling by positive weights preserves strict sign changes. -/
theorem hasSignChanges_mul_iff {f w : ℕ → ℝ} (hw : ∀ n, 0 < w n) {k : ℕ} :
    HasSignChanges (fun n => w n * f n) k ↔ HasSignChanges f k := by
  constructor <;> rintro ⟨q, hq⟩ <;> refine ⟨q, fun i hi => ⟨(hq i hi).1, ?_⟩⟩
  · have h := (hq i hi).2
    have e : w (q i) * f (q i) * (w (q (i + 1)) * f (q (i + 1))) =
        (w (q i) * w (q (i + 1))) * (f (q i) * f (q (i + 1))) := by ring
    rw [e] at h
    exact neg_of_mul_neg_right h (mul_pos (hw _) (hw _)).le
  · have e : w (q i) * f (q i) * (w (q (i + 1)) * f (q (i + 1))) =
        (w (q i) * w (q (i + 1))) * (f (q i) * f (q (i + 1))) := by ring
    rw [e]
    exact mul_neg_of_pos_of_neg (mul_pos (hw _) (hw _)) (hq i hi).2

/-- A chain alternates: `(−1)^i f(q 0) f(q i) > 0` along it. -/
theorem pos_neg_one_pow_mul_of_chain {f : ℕ → ℝ} {k : ℕ} {q : ℕ → ℕ} (hk : 0 < k)
    (hq : ∀ i < k, q i < q (i + 1) ∧ f (q i) * f (q (i + 1)) < 0) :
    ∀ i ≤ k, 0 < (-1 : ℝ) ^ i * (f (q 0) * f (q i)) := by
  intro i
  induction i with
  | zero =>
    intro _
    have h0 : f (q 0) ≠ 0 := fun h => by have := (hq 0 hk).2; rw [h, zero_mul] at this; simp at this
    simpa using mul_self_pos.mpr h0
  | succ i ih =>
    intro hi
    have hA := ih (by omega)
    have hB := (hq i (by omega)).2
    have hprod := mul_neg_of_pos_of_neg hA hB
    have e : (-1 : ℝ) ^ i * (f (q 0) * f (q i)) * (f (q i) * f (q (i + 1))) =
        -((-1 : ℝ) ^ (i + 1) * (f (q 0) * f (q (i + 1)))) * (f (q i) * f (q i)) := by ring
    rw [e] at hprod
    have hsq : 0 < f (q i) * f (q i) := by
      have : f (q i) ≠ 0 := fun h => by rw [h, zero_mul] at hB; simp at hB
      exact mul_self_pos.mpr this
    by_contra hc
    exact absurd hprod (not_lt.mpr (mul_nonneg (by linarith [not_lt.mp hc]) hsq.le))

/-- Positive tails bound chain lengths: if `f n > 0` for `n ≥ N₀`, chains have length `≤ N₀`. -/
theorem le_of_hasSignChanges_of_pos {f : ℕ → ℝ} {N₀ k : ℕ} (hpos : ∀ n, N₀ ≤ n → 0 < f n)
    (h : HasSignChanges f k) : k ≤ N₀ := by
  obtain ⟨q, hq⟩ := h
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact Nat.zero_le _
  have hmono : ∀ i ≤ k, i ≤ q i := by
    intro i
    induction i with
    | zero => intro _; exact Nat.zero_le _
    | succ i ih => intro hi; have := (hq i (by omega)).1; have := ih (by omega); omega
  have hlast : q (k - 1) < N₀ := by
    by_contra hc
    have h1 := hq (k - 1) (by omega)
    rw [show k - 1 + 1 = k by omega] at h1
    have := mul_pos (hpos _ (not_lt.mp hc)) (hpos (q k) (by omega))
    linarith [h1.2]
  have := hmono (k - 1) (by omega)
  omega

/-- **Odd chains extend.**  If `f 0 > 0` and `f` is eventually positive, an odd chain of sign
changes extends to an even one, so the maximal number of sign changes is even. -/
theorem hasSignChanges_succ_of_odd {f : ℕ → ℝ} (h0 : 0 < f 0) {N₀ : ℕ}
    (hpos : ∀ n, N₀ ≤ n → 0 < f n) {m : ℕ} (h : HasSignChanges f (2 * m + 1)) :
    HasSignChanges f (2 * m + 2) := by
  classical
  obtain ⟨q, hq⟩ := h
  have halt := pos_neg_one_pow_mul_of_chain (by omega) hq (2 * m + 1) le_rfl
  rw [pow_succ, pow_mul, neg_one_sq, one_pow, one_mul, neg_one_mul, neg_pos] at halt
  rcases lt_or_gt_of_ne (show f (q 0) ≠ 0 from fun h => by rw [h, zero_mul] at halt; simp at halt)
    with hneg | hpos0
  · -- prepend the index `0`
    have hq0 : 0 < q 0 := Nat.pos_of_ne_zero fun h => by rw [h] at hneg; linarith
    refine ⟨fun i => if i = 0 then 0 else q (i - 1), fun i hi => ?_⟩
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp only [if_true, show (0 + 1 = 0) = False by simp, if_false, Nat.add_sub_cancel]
      exact ⟨hq0, mul_neg_of_pos_of_neg h0 hneg⟩
    · have hne : i ≠ 0 := by omega
      simp only [hne, if_false, show i + 1 ≠ 0 by omega, Nat.add_sub_cancel]
      have := hq (i - 1) (by omega)
      rwa [show i - 1 + 1 = i by omega] at this
  · -- append a large index of the positive tail
    have hlast : f (q (2 * m + 1)) < 0 := by
      by_contra hc
      exact absurd halt (not_lt.mpr (mul_nonneg hpos0.le (not_lt.mp hc)))
    set M := max N₀ (q (2 * m + 1) + 1)
    refine ⟨fun i => if i ≤ 2 * m + 1 then q i else M, fun i hi => ?_⟩
    rcases lt_or_eq_of_le (show i ≤ 2 * m + 1 by omega) with hlt | rfl
    · simp only [hlt.le, if_true, show i + 1 ≤ 2 * m + 1 by omega]
      exact hq i hlt
    · simp only [le_rfl, if_true, show ¬ (2 * m + 1 + 1 ≤ 2 * m + 1) by omega, if_false]
      exact ⟨lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _),
        mul_neg_of_neg_of_pos hlast (hpos M (le_max_left _ _))⟩

/-! ## The heated slice -/

/-- The rescaled even heated coefficients `a_n = (2n)! Re T_{2n}(λ, 0, t)`. -/
def heatSignSeq (lam t : ℝ) (n : ℕ) : ℝ :=
  ((2 * n).factorial : ℝ) * (xiSliceHeatTransfer lam 0 t (2 * n)).re

/-- The heat shift in rescaled coefficients: `a_n(λ') = Σ_j c^j/j! · a_{n+j}(λ)`. -/
theorem hasSum_heatSignSeq_shift {lam lam' : ℝ} (hll : lam ≤ lam') (t : ℝ) (n : ℕ) :
    HasSum (fun j : ℕ => ((lam' - lam) / 2) ^ j / j.factorial * heatSignSeq lam t (n + j))
      (heatSignSeq lam' t n) := by
  have h := (Complex.hasSum_re (hasSum_xiSliceHeatTransfer_shift hll 0 t (2 * n))).mul_left
    ((2 * n).factorial : ℝ)
  unfold heatSignSeq
  have e : (fun j : ℕ => ((lam' - lam) / 2) ^ j / j.factorial *
      (((2 * (n + j)).factorial : ℝ) * (xiSliceHeatTransfer lam 0 t (2 * (n + j))).re)) =
      fun i => ((2 * n).factorial : ℝ) * ((((((lam' - lam) / 2) ^ i / i.factorial *
        ((2 * n + 2 * i).factorial / (2 * n).factorial) : ℝ) : ℂ) *
          xiSliceHeatTransfer lam 0 t (2 * n + 2 * i)).re) := by
    funext j
    rw [Complex.re_ofReal_mul, show 2 * n + 2 * j = 2 * (n + j) by ring]
    have hf : ((2 * n).factorial : ℝ) ≠ 0 := by positivity
    field_simp
  rw [e]
  exact h

/-- The shift series converges absolutely, dominated by its value at the central height. -/
theorem summable_abs_heatSignSeq_shift {lam lam' : ℝ} (hlam : 0 ≤ lam) (hll : lam ≤ lam')
    (t : ℝ) (n : ℕ) :
    Summable fun j : ℕ => ((lam' - lam) / 2) ^ j / j.factorial * |heatSignSeq lam t (n + j)| := by
  have hc : 0 ≤ (lam' - lam) / 2 := by linarith
  refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_)
    (hasSum_heatSignSeq_shift hll 0 n).summable
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  unfold heatSignSeq
  rw [abs_mul, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans
    (norm_xiSliceHeatTransfer_le_central hlam 0 t (n + j)).1) (by positivity)

/-- **The sign index is antitone in the heat.**  For `0 ≤ λ ≤ λ'`, a chain of `k` strict sign
changes of `n ↦ T_{2n}(λ', 0, t)` yields one of `n ↦ T_{2n}(λ, 0, t)`. -/
theorem hasSignChanges_xiSliceHeat_of_le {lam lam' : ℝ} (hlam : 0 ≤ lam) (hll : lam ≤ lam')
    (t : ℝ) {k : ℕ}
    (h : HasSignChanges (fun n => (xiSliceHeatTransfer lam' 0 t (2 * n)).re) k) :
    HasSignChanges (fun n => (xiSliceHeatTransfer lam 0 t (2 * n)).re) k := by
  have hw : ∀ n : ℕ, (0 : ℝ) < ((2 * n).factorial : ℝ) := fun n => by positivity
  rw [← hasSignChanges_mul_iff hw] at h ⊢
  exact hasSignChanges_of_expShift (f := heatSignSeq lam t) (g := heatSignSeq lam' t)
    (by linarith) (summable_abs_heatSignSeq_shift hlam hll t)
    (fun n => (hasSum_heatSignSeq_shift hll t n).tsum_eq.symm) h

/-- **Quantization and range of the sign index.**  There is `C > 0` such that for `0 < λ ≤ 1`
and every height, chains of sign changes of `n ↦ T_{2n}(λ, 0, t)` have length at most `⌈C/λ⌉`,
and every odd chain extends to an even one. -/
theorem exists_xiSliceHeat_signIndex_bounds :
    ∃ C : ℝ, 0 < C ∧ ∀ lam : ℝ, 0 < lam → lam ≤ 1 → ∀ t : ℝ,
      (∀ k, HasSignChanges (fun n => (xiSliceHeatTransfer lam 0 t (2 * n)).re) k →
        k ≤ ⌈C / lam⌉₊) ∧
      (∀ m, HasSignChanges (fun n => (xiSliceHeatTransfer lam 0 t (2 * n)).re) (2 * m + 1) →
        HasSignChanges (fun n => (xiSliceHeatTransfer lam 0 t (2 * n)).re) (2 * m + 2)) := by
  obtain ⟨C, hC, htail⟩ := exists_xiSliceHeatTransfer_pos_order_ge_inv_heat
  refine ⟨C, hC, fun lam hlam hlam1 t => ?_⟩
  have hpos : ∀ n, ⌈C / lam⌉₊ ≤ n → 0 < (xiSliceHeatTransfer lam 0 t (2 * n)).re := by
    intro n hn
    have h := htail lam hlam hlam1 t n ((Nat.le_ceil _).trans (by exact_mod_cast hn))
    simpa using (Complex.lt_def.mp h).1
  have h0 : 0 < (xiSliceHeatTransfer lam 0 t (2 * 0)).re := by
    simpa using (Complex.lt_def.mp (xiSliceHeatTransfer_zero_order_pos hlam t)).1
  exact ⟨fun k hk => le_of_hasSignChanges_of_pos hpos hk,
    fun m hm => hasSignChanges_succ_of_odd h0 hpos hm⟩

/-- **The index vanishes exactly at WD positivity.**  At positive heat, `n ↦ T_{2n}(λ, 0, t)` has no
strict sign change iff every heated coefficient `T_n(λ, 0, t)` is nonnegative. -/
theorem not_hasSignChanges_one_iff {lam : ℝ} (hlam : 0 < lam) (t : ℝ) :
    ¬ HasSignChanges (fun n => (xiSliceHeatTransfer lam 0 t (2 * n)).re) 1 ↔
      ∀ n, 0 ≤ xiSliceHeatTransfer lam 0 t n := by
  have him : ∀ n, (xiSliceHeatTransfer lam 0 t n).im = 0 := xiSliceHeatTransfer_im_eq_zero hlam.le t
  constructor
  · intro h n
    obtain ⟨l, rfl | rfl⟩ := Nat.even_or_odd' n
    · refine Complex.le_def.mpr ⟨?_, (him _).symm⟩
      rw [Complex.zero_re]
      by_contra hneg
      have h0 : 0 < (xiSliceHeatTransfer lam 0 t (2 * 0)).re := by
        simpa using (Complex.lt_def.mp (xiSliceHeatTransfer_zero_order_pos hlam t)).1
      have hl : l ≠ 0 := fun hl => by subst hl; exact hneg h0.le
      refine h ⟨fun i => if i = 0 then 0 else l, fun i hi => ?_⟩
      have hi0 : i = 0 := by omega
      subst hi0
      simp only [if_true, show (0 + 1 = 0) = False by simp, if_false]
      exact ⟨Nat.pos_of_ne_zero hl, mul_neg_of_pos_of_neg h0 (not_le.mp hneg)⟩
    · rw [xiSliceHeatTransfer_odd_eq_zero hlam.le]
  · rintro h ⟨q, hq⟩
    have hle : ∀ n, 0 ≤ (xiSliceHeatTransfer lam 0 t (2 * n)).re := fun n => by
      simpa using (Complex.le_def.mp (h (2 * n))).1
    exact absurd (hq 0 one_pos).2 (not_lt.mpr (mul_nonneg (hle _) (hle _)))

end

end RHTower.DeBruijn
