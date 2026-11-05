import GaloisForLFunctions.FiniteFreeProbability.MollifiedJensenCriterion
import GaloisForLFunctions.RHTower.HardyTheorem

/-!
# A finite free Hardy theorem

Hardy's argument excludes a one-signed tail of the real function `Ξ` (a nonnegative or nonpositive
tail would bound the theta source on the whole strip). Hence `Ξ` takes both strict signs beyond
every height, and there is an increasing sequence `p_0 < p_1 < ⋯` with `(−1)^j Ξ(p_j) > 0`.

The scaled Jensen approximants `Φ_d(u) = Σ_{k≤d} c_k d!/((d−k)! d^k) u^k` of `Ξ` converge to `Ξ`
(Tannery), so for large `d` they carry the same strict signs at `p_0, …, p_M` and vanish at some
`u_j ∈ (p_j, p_{j+1})`. Since `R_d(Ξ)(d/u) = (d/u)^d Φ_d(u)`, the points `d/u_j` are distinct real
roots.

**Theorem (unconditional).** For every `M`, the reversed Jensen polynomial of `Ξ` of degree `d` has
at least `M` distinct real roots for all large `d`.
-/

open Polynomial Filter Topology Complex
open scoped Real
open GaloisForLFunctions.HTGeometry RHTower

namespace FiniteFreeProbability

noncomputable section

/-! ## Strict sign changes of `Ξ` -/

/-- `Ξ` is not eventually nonnegative. -/
theorem false_of_Xi_eventually_nonneg {T : ℝ} (hT : 0 < T) (h : ∀ t : ℝ, T < t → 0 ≤ Xi t) :
    False := by
  have hpi := Real.pi_pos
  refine false_of_hardyXiDensity_tail_sign (W := T / (4 * π) + 1) (σ := -1)
    (by positivity) (by norm_num) fun w hw => ?_
  have habs : hardyXiDensity w = hardyXiDensity |w| := by
    rcases abs_cases w with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, hardyXiDensity_neg]
  have hbig : T < 4 * π * |w| := by
    have h1 : T / (4 * π) < |w| := by linarith
    rw [div_lt_iff₀ (by positivity)] at h1
    nlinarith [h1]
  have hXi := h (4 * π * |w|) hbig
  rw [habs, hardyXiDensity]
  have hden : (0 : ℝ) < (4 * π * |w|) ^ 2 + 1 / 4 := by positivity
  rw [neg_one_mul, neg_nonneg]
  exact div_nonpos_of_nonpos_of_nonneg (by nlinarith [hXi]) hden.le

/-- `Ξ` is not eventually nonpositive. -/
theorem false_of_Xi_eventually_nonpos {T : ℝ} (hT : 0 < T) (h : ∀ t : ℝ, T < t → Xi t ≤ 0) :
    False := by
  have hpi := Real.pi_pos
  refine false_of_hardyXiDensity_tail_sign (W := T / (4 * π) + 1) (σ := 1)
    (by positivity) (by norm_num) fun w hw => ?_
  have habs : hardyXiDensity w = hardyXiDensity |w| := by
    rcases abs_cases w with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h]
    · rw [h, hardyXiDensity_neg]
  have hbig : T < 4 * π * |w| := by
    have h1 : T / (4 * π) < |w| := by linarith
    rw [div_lt_iff₀ (by positivity)] at h1
    nlinarith [h1]
  have hXi := h (4 * π * |w|) hbig
  rw [habs, hardyXiDensity, one_mul]
  have hden : (0 : ℝ) < (4 * π * |w|) ^ 2 + 1 / 4 := by positivity
  exact div_nonneg (by nlinarith [hXi]) hden.le

theorem exists_Xi_pos_gt (T : ℝ) : ∃ t : ℝ, T < t ∧ 0 < Xi t := by
  by_contra h
  push Not at h
  exact false_of_Xi_eventually_nonpos (T := max T 1) (by positivity) fun t ht =>
    h t (lt_of_le_of_lt (le_max_left _ _) ht)

theorem exists_Xi_neg_gt (T : ℝ) : ∃ t : ℝ, T < t ∧ Xi t < 0 := by
  by_contra h
  push Not at h
  exact false_of_Xi_eventually_nonneg (T := max T 1) (by positivity) fun t ht =>
    h t (lt_of_le_of_lt (le_max_left _ _) ht)

/-- The next point beyond `T` where `(−1)^j Ξ > 0`. -/
def hardyStep (T : ℝ) (j : ℕ) : ℝ :=
  if Even j then Classical.choose (exists_Xi_pos_gt T) else Classical.choose (exists_Xi_neg_gt T)

theorem hardyStep_spec (T : ℝ) (j : ℕ) :
    T < hardyStep T j ∧ 0 < (-1) ^ j * Xi (hardyStep T j) := by
  unfold hardyStep
  split_ifs with h
  · obtain ⟨h1, h2⟩ := Classical.choose_spec (exists_Xi_pos_gt T)
    exact ⟨h1, by rw [h.neg_one_pow, one_mul]; exact h2⟩
  · obtain ⟨h1, h2⟩ := Classical.choose_spec (exists_Xi_neg_gt T)
    exact ⟨h1, by rw [(Nat.not_even_iff_odd.1 h).neg_one_pow]; linarith⟩

/-- An increasing sequence on which `Ξ` alternates strictly in sign. -/
def hardySeq : ℕ → ℝ
  | 0 => hardyStep 0 0
  | j + 1 => hardyStep (hardySeq j) (j + 1)

theorem hardySeq_pos : 0 < hardySeq 0 := (hardyStep_spec 0 0).1

theorem hardySeq_lt_succ (j : ℕ) : hardySeq j < hardySeq (j + 1) := (hardyStep_spec _ _).1

theorem hardySeq_strictMono : StrictMono hardySeq := strictMono_nat_of_lt_succ hardySeq_lt_succ

theorem hardySeq_sign (j : ℕ) : 0 < (-1) ^ j * Xi (hardySeq j) := by
  cases j with
  | zero => exact (hardyStep_spec 0 0).2
  | succ j => exact (hardyStep_spec _ _).2

/-! ## Real roots of the scaled approximants -/

/-- The real coefficients of `Ξ`. -/
def xiCoeff (k : ℕ) : ℂ := ((realTaylorCoeff XiC k : ℝ) : ℂ)

theorem mk_xiCoeff : PowerSeries.mk xiCoeff = xiSeries := rfl

/-- On the real axis the approximants are real. -/
theorem scaledJensen_xiCoeff_ofReal (d : ℕ) (u : ℝ) :
    scaledJensen xiCoeff d (u : ℂ) = ((∑ k ∈ Finset.range (d + 1), realTaylorCoeff XiC k *
      ((d.descFactorial k : ℝ) / (d : ℝ) ^ k) * u ^ k : ℝ) : ℂ) := by
  simp only [scaledJensen, xiCoeff]
  push_cast
  rfl

theorem tendsto_scaledJensen_xiCoeff (u : ℂ) :
    Tendsto (fun d => scaledJensen xiCoeff d u) atTop (𝓝 (XiC u)) := by
  have hsum : ∀ z, HasSum (fun k => xiCoeff k * z ^ k) (XiC z) := fun z => by
    simpa [xiSeries, xiCoeff] using hasSum_xiSeries z
  have hf := summable_norm_mul_pow_of_summable fun z => (hsum z).summable
  have h := TendstoLocallyUniformlyOn.tendsto_at
    (TendstoLocallyUniformly.tendstoLocallyUniformlyOn
      (tendstoLocallyUniformly_scaledJensen hf (ψ := id) tendsto_id) (s := Set.univ))
    (Set.mem_univ u)
  simpa only [id, (hsum u).tsum_eq] using h

/-- **Finite free Hardy theorem.** For every `M`, the reversed Jensen polynomial of `Ξ` of degree
`d` has at least `M` distinct real roots for all large `d`. -/
theorem eventually_le_card_roots_jensenReverse_XiC (M : ℕ) :
    ∀ᶠ d : ℕ in atTop, M ≤ (jensenReverse (realTaylorCoeff XiC) d).roots.toFinset.card := by
  set p := hardySeq
  set φ : ℕ → ℝ → ℝ := fun d u => ∑ k ∈ Finset.range (d + 1), realTaylorCoeff XiC k *
    ((d.descFactorial k : ℝ) / (d : ℝ) ^ k) * u ^ k
  -- strict signs of the approximants at `p 0, …, p M`
  have hsign : ∀ j : ℕ, ∀ᶠ d : ℕ in atTop, 0 < (-1) ^ j * φ d (p j) := fun j => by
    have h := tendsto_scaledJensen_xiCoeff (p j : ℂ)
    simp only [scaledJensen_xiCoeff_ofReal, XiC_ofReal] at h
    have h' : Tendsto (fun d => φ d (p j)) atTop (𝓝 (Xi (p j))) := by
      have := (Complex.continuous_re.tendsto _).comp h
      simpa only [Function.comp_def, Complex.ofReal_re] using this
    exact (h'.const_mul ((-1) ^ j)).eventually (lt_mem_nhds (hardySeq_sign j))
  have hall : ∀ᶠ d : ℕ in atTop, ∀ j ∈ Finset.range (M + 1), 0 < (-1) ^ j * φ d (p j) :=
    (Filter.eventually_all_finset _).2 fun j _ => hsign j
  filter_upwards [hall, eventually_gt_atTop 0] with d hd hd0
  -- a zero of `φ d` in each window `(p j, p (j+1))`
  have hzero : ∀ j < M, ∃ u ∈ Set.Ioo (p j) (p (j + 1)), φ d u = 0 := fun j hj => by
    have h1 := hd j (Finset.mem_range.2 (by omega))
    have h2 := hd (j + 1) (Finset.mem_range.2 (by omega))
    have hcont : ContinuousOn (φ d) (Set.Icc (p j) (p (j + 1))) := by
      simp only [φ]; fun_prop
    rw [pow_succ] at h2
    rcases neg_one_pow_eq_or ℝ j with hj1 | hj1 <;> rw [hj1] at h1 h2
    · obtain ⟨u, hu, hu0⟩ := intermediate_value_Ioo' (hardySeq_lt_succ j).le hcont
        (show (0 : ℝ) ∈ Set.Ioo (φ d (p (j + 1))) (φ d (p j)) from ⟨by linarith, by linarith⟩)
      exact ⟨u, hu, hu0⟩
    · obtain ⟨u, hu, hu0⟩ := intermediate_value_Ioo (hardySeq_lt_succ j).le hcont
        (show (0 : ℝ) ∈ Set.Ioo (φ d (p j)) (φ d (p (j + 1))) from ⟨by linarith, by linarith⟩)
      exact ⟨u, hu, hu0⟩
  choose! u hu hu0 using hzero
  -- the points `d / u_j` are real roots
  have hne : jensenReverse (realTaylorCoeff XiC) d ≠ 0 := fun h0 => by
    have := jensenRev_ne_zero (d := d) (f := xiSeries)
      (by rw [constantCoeff_xiSeries]; exact XiC_zero_ne)
    rw [jensenRev_xiSeries, h0, Polynomial.map_zero] at this
    exact this rfl
  have hupos : ∀ j < M, 0 < u j := fun j hj =>
    lt_trans (lt_of_lt_of_le hardySeq_pos (hardySeq_strictMono.monotone (Nat.zero_le j)))
      (hu j hj).1
  have hroot : ∀ j < M, (jensenReverse (realTaylorCoeff XiC) d).IsRoot ((d : ℝ) / u j) :=
    fun j hj => by
      have huc : ((u j : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (hupos j hj).ne'
      have h := eval_jensenRev_div xiCoeff hd0 huc
      rw [scaledJensen_xiCoeff_ofReal, show (∑ k ∈ Finset.range (d + 1), realTaylorCoeff XiC k *
        ((d.descFactorial k : ℝ) / (d : ℝ) ^ k) * u j ^ k) = φ d (u j) from rfl, hu0 j hj,
        Complex.ofReal_zero, mul_zero, mk_xiCoeff, jensenRev_xiSeries, eval_map,
        show (d : ℂ) / ((u j : ℝ) : ℂ) = algebraMap ℝ ℂ ((d : ℝ) / u j) by push_cast; rfl,
        eval₂_at_apply] at h
      exact (algebraMap ℝ ℂ).injective (by rw [h, map_zero])
  -- the roots are distinct
  have hinj : Set.InjOn (fun j => (d : ℝ) / u j) (Finset.range M : Set ℕ) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    have hdpos : (0 : ℝ) < d := by exact_mod_cast hd0
    have hu_eq : u i = u j := by
      have := hij; simp only at this
      field_simp [(hupos i hi).ne', (hupos j hj).ne'] at this
      nlinarith
    by_contra hne'
    rcases lt_or_gt_of_ne hne' with hlt | hlt
    · have h1 := (hu i hi).2
      have h2 := (hu j hj).1
      have := hardySeq_strictMono.monotone (show i + 1 ≤ j by omega)
      linarith
    · have h1 := (hu j hj).2
      have h2 := (hu i hi).1
      have := hardySeq_strictMono.monotone (show j + 1 ≤ i by omega)
      linarith
  calc M = ((Finset.range M).image fun j => (d : ℝ) / u j).card := by
        rw [Finset.card_image_of_injOn hinj, Finset.card_range]
    _ ≤ (jensenReverse (realTaylorCoeff XiC) d).roots.toFinset.card := by
        refine Finset.card_le_card fun x hx => ?_
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
        rw [Multiset.mem_toFinset, mem_roots hne]
        exact hroot j (Finset.mem_range.1 hj)

end

end FiniteFreeProbability

#print axioms FiniteFreeProbability.eventually_le_card_roots_jensenReverse_XiC
