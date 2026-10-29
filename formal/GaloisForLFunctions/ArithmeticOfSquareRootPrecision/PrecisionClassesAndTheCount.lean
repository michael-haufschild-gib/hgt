import Mathlib

/-!
# Precision classes and the count

A **weight** is a function `a : ℕ → ℝ` (a prime-side source; `Λ` is the arithmetic one), with
partial sums `A(x) = Σ_{1 ≤ n ≤ x} a(n)`. The **count** is the statement
`A(x) − x = O(√x log² x)`; for `a = Λ` it is the Riemann hypothesis (von Koch).

The **precision class** of a scale `φ` is the space of perturbations `δ` whose partial sums are
`O(φ)`. The square-root class `𝒬` is the class of `√x log² x`.

* **Stabilizer law** (`count_add_iff_mem_sqrtClass`). If `a` satisfies the count, then `a + δ`
  does iff `δ ∈ 𝒬`. The precision class of the count is exactly the square-root class.
* **Power threshold** (`smul_powerWeight_mem_sqrtClass_iff`). For `ε ≠ 0` and `η ≥ 0`, the
  perturbation `ε n^{−η}` lies in `𝒬` iff `η ≥ ½`: its partial sums are at least `|ε| x^{1−η}/2`,
  and at most `2|ε|√x` for `η ≥ ½`.
* **Precision rigidity of the count** (`not_count_and_count_add_smul_powerWeight`). No weight
  satisfies the count together with its perturbation by `ε n^{−η}`, `η < ½`; for `η ≥ ½` the
  perturbation preserves the count (`count_add_smul_powerWeight`). The threshold is sharp.
* Finitely supported perturbations lie in `𝒬` (`mem_sqrtClass_of_eventually_zero`); a lower
  bound `|Σ δ| ≥ c g` against a scale `g` dominating `φ` excludes `δ` from the class of `φ`
  (`not_mem_precisionClass_of_lower_bound`).
-/

noncomputable section

open Filter Asymptotics Real Finset

namespace GaloisForLFunctions.ArithmeticOfSquareRootPrecision

/-- The **partial sum** `A(x) = Σ_{1 ≤ n ≤ x} a(n)` of a weight. -/
def partialSum (a : ℕ → ℝ) (x : ℝ) : ℝ := ∑ n ∈ Ioc 0 ⌊x⌋₊, a n

theorem partialSum_add (a b : ℕ → ℝ) (x : ℝ) :
    partialSum (a + b) x = partialSum a x + partialSum b x := by
  simp [partialSum, sum_add_distrib]

theorem partialSum_sub (a b : ℕ → ℝ) (x : ℝ) :
    partialSum (a - b) x = partialSum a x - partialSum b x := by
  simp [partialSum, sum_sub_distrib]

theorem partialSum_smul (c : ℝ) (a : ℕ → ℝ) (x : ℝ) :
    partialSum (c • a) x = c * partialSum a x := by
  simp [partialSum, mul_sum]

theorem partialSum_zero (x : ℝ) : partialSum 0 x = 0 := by simp [partialSum]

theorem partialSum_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (x : ℝ) : 0 ≤ partialSum a x :=
  sum_nonneg fun n _ => ha n

/-- The partial sums only see `a` on `{1, …, ⌊x⌋}`. -/
theorem partialSum_congr {a b : ℕ → ℝ} {x : ℝ} (h : ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ x → a n = b n) :
    partialSum a x = partialSum b x := by
  refine sum_congr rfl fun n hn => ?_
  obtain ⟨h1, h2⟩ := mem_Ioc.mp hn
  rcases lt_or_ge x 0 with hx | hx
  · rw [Nat.floor_of_nonpos hx.le] at h2; omega
  · exact h n h1 ((Nat.cast_le.mpr h2).trans (Nat.floor_le hx))

/-- The **square-root scale** `√x log² x`. -/
def sqrtScale (x : ℝ) : ℝ := √x * Real.log x ^ 2

theorem sqrtScale_nonneg (x : ℝ) : 0 ≤ sqrtScale x := by unfold sqrtScale; positivity

/-- `√x ≤ √x log² x` once `log x ≥ 1`. -/
theorem sqrt_le_sqrtScale {x : ℝ} (hx : exp 1 ≤ x) : √x ≤ sqrtScale x := by
  have hl : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (exp_pos 1) hx
  unfold sqrtScale
  exact le_mul_of_one_le_right (Real.sqrt_nonneg x) (one_le_pow₀ hl)

theorem one_le_sqrtScale {x : ℝ} (hx : exp 1 ≤ x) : 1 ≤ sqrtScale x := by
  have h1 : 1 ≤ x := le_trans (Real.one_le_exp (by norm_num)) hx
  exact (Real.one_le_sqrt.mpr h1).trans (sqrt_le_sqrtScale hx)

/-- The **precision class** of a scale `φ`: perturbations whose partial sums are `O(φ)`. -/
def PrecisionClass (φ : ℝ → ℝ) : Set (ℕ → ℝ) := {δ | partialSum δ =O[atTop] φ}

/-- The **square-root class** `𝒬`. -/
abbrev sqrtClass : Set (ℕ → ℝ) := PrecisionClass sqrtScale

theorem PrecisionClass.zero_mem (φ : ℝ → ℝ) : (0 : ℕ → ℝ) ∈ PrecisionClass φ := by
  show partialSum 0 =O[atTop] φ
  rw [show partialSum 0 = 0 from funext partialSum_zero]
  exact isBigO_zero φ atTop

theorem PrecisionClass.add_mem {φ : ℝ → ℝ} {δ δ' : ℕ → ℝ} (h : δ ∈ PrecisionClass φ)
    (h' : δ' ∈ PrecisionClass φ) : δ + δ' ∈ PrecisionClass φ := by
  have := (h : partialSum δ =O[atTop] φ).add h'
  simpa [PrecisionClass, funext (partialSum_add δ δ')] using this

theorem PrecisionClass.sub_mem {φ : ℝ → ℝ} {δ δ' : ℕ → ℝ} (h : δ ∈ PrecisionClass φ)
    (h' : δ' ∈ PrecisionClass φ) : δ - δ' ∈ PrecisionClass φ := by
  have := (h : partialSum δ =O[atTop] φ).sub h'
  simpa [PrecisionClass, funext (partialSum_sub δ δ')] using this

theorem PrecisionClass.smul_mem {φ : ℝ → ℝ} {δ : ℕ → ℝ} (c : ℝ) (h : δ ∈ PrecisionClass φ) :
    c • δ ∈ PrecisionClass φ := by
  have := (h : partialSum δ =O[atTop] φ).const_mul_left c
  simpa [PrecisionClass, funext (partialSum_smul c δ)] using this

theorem PrecisionClass.mono {φ ψ : ℝ → ℝ} (hφψ : φ =O[atTop] ψ) {δ : ℕ → ℝ}
    (h : δ ∈ PrecisionClass φ) : δ ∈ PrecisionClass ψ :=
  (h : partialSum δ =O[atTop] φ).trans hφψ

/-- **Exclusion by a lower bound.** If `|Σ_{n ≤ x} δ(n)| ≥ c |g(x)|` eventually, `c > 0`, `φ = o(g)`
and `g` is frequently nonzero, then `δ` is not in the precision class of `φ`. -/
theorem not_mem_precisionClass_of_lower_bound {φ g : ℝ → ℝ} {δ : ℕ → ℝ} (hφ : φ =o[atTop] g)
    {c : ℝ} (hc : 0 < c) (hlow : ∀ᶠ x in atTop, c * ‖g x‖ ≤ ‖partialSum δ x‖)
    (hg : ∃ᶠ x in atTop, g x ≠ 0) : δ ∉ PrecisionClass φ := by
  intro h
  have ho : partialSum δ =o[atTop] g := (h : partialSum δ =O[atTop] φ).trans_isLittleO hφ
  obtain ⟨x, ⟨h1, h2⟩, hx⟩ := ((hlow.and (ho.def (half_pos hc))).and_frequently hg).exists
  have hgx : 0 < ‖g x‖ := norm_pos_iff.mpr hx
  nlinarith

/-- A perturbation vanishing beyond some `N` lies in `𝒬`: its partial sums are eventually
constant. -/
theorem mem_sqrtClass_of_eventually_zero {δ : ℕ → ℝ} {N : ℕ} (hδ : ∀ n, N < n → δ n = 0) :
    δ ∈ sqrtClass := by
  refine IsBigO.of_bound (|partialSum δ N|) ?_
  filter_upwards [eventually_ge_atTop (max (exp 1) N)] with x hx
  have hxN : (N : ℝ) ≤ x := le_trans (le_max_right _ _) hx
  have hconst : partialSum δ x = partialSum δ N := by
    unfold partialSum
    rw [Nat.floor_natCast]
    refine (sum_subset (Ioc_subset_Ioc_right (Nat.le_floor hxN)) fun n hn hnN => ?_).symm
    refine hδ n ?_
    by_contra hle
    exact hnN (mem_Ioc.mpr ⟨(mem_Ioc.mp hn).1, by omega⟩)
  rw [hconst, Real.norm_eq_abs, Real.norm_of_nonneg (sqrtScale_nonneg x)]
  exact le_mul_of_one_le_right (abs_nonneg _) (one_le_sqrtScale (le_trans (le_max_left _ _) hx))

/-! ### The count -/

/-- The **count**: `A(x) − x = O(√x log² x)`. -/
def Count (a : ℕ → ℝ) : Prop := (fun x => partialSum a x - x) =O[atTop] sqrtScale

/-- The **upper count**: `A(x) − x ≤ C √x log² x` eventually. -/
def UpperCount (a : ℕ → ℝ) : Prop := ∃ C : ℝ, ∀ᶠ x in atTop, partialSum a x - x ≤ C * sqrtScale x

/-- The **lower count**: `A(x) − x ≥ −C √x log² x` eventually. -/
def LowerCount (a : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, ∀ᶠ x in atTop, -(C * sqrtScale x) ≤ partialSum a x - x

/-- The count is the conjunction of its two halves. -/
theorem count_iff_upperCount_and_lowerCount {a : ℕ → ℝ} :
    Count a ↔ UpperCount a ∧ LowerCount a := by
  constructor
  · intro h
    obtain ⟨C, hC⟩ := isBigO_iff.mp h
    refine ⟨⟨C, hC.mono fun x hx => ?_⟩, ⟨C, hC.mono fun x hx => ?_⟩⟩ <;>
    · rw [Real.norm_eq_abs, Real.norm_of_nonneg (sqrtScale_nonneg x)] at hx
      linarith [abs_le.mp hx]
  · rintro ⟨⟨C, hC⟩, ⟨C', hC'⟩⟩
    refine IsBigO.of_bound (max C C') ?_
    filter_upwards [hC, hC'] with x h1 h2
    have hs := sqrtScale_nonneg x
    rw [Real.norm_eq_abs, Real.norm_of_nonneg hs]
    refine abs_le.mpr ⟨?_, ?_⟩ <;> nlinarith [le_max_left C C', le_max_right C C']

/-- **The stabilizer law.** If `a` satisfies the count, then `a + δ` does iff `δ ∈ 𝒬`. -/
theorem count_add_iff_mem_sqrtClass {a : ℕ → ℝ} (ha : Count a) (δ : ℕ → ℝ) :
    Count (a + δ) ↔ δ ∈ sqrtClass := by
  have hsplit : ∀ x, partialSum (a + δ) x - x = (partialSum a x - x) + partialSum δ x := by
    intro x; rw [partialSum_add]; ring
  constructor
  · intro h
    have := h.sub ha
    simpa [PrecisionClass, hsplit] using this
  · intro h
    have := ha.add (h : partialSum δ =O[atTop] sqrtScale)
    simpa [Count, hsplit] using this

/-- Two weights satisfying the count differ by an element of `𝒬`. -/
theorem sub_mem_sqrtClass_of_count {a b : ℕ → ℝ} (ha : Count a) (hb : Count b) :
    b - a ∈ sqrtClass := by
  have := (count_add_iff_mem_sqrtClass ha (b - a)).mp (by simpa using hb)
  exact this

/-! ### The power threshold -/

/-- The power perturbation `n ↦ n^{−η}`. -/
def powerWeight (η : ℝ) (n : ℕ) : ℝ := (n : ℝ) ^ (-η)

theorem powerWeight_nonneg (η : ℝ) (n : ℕ) : 0 ≤ powerWeight η n :=
  Real.rpow_nonneg (Nat.cast_nonneg n) _

/-- **Lower bound**: `Σ_{n ≤ x} n^{−η} ≥ x^{1−η}/2` for `η ≥ 0`, `x ≥ 1`. Each term is at least
`x^{−η}` and there are `⌊x⌋ ≥ x/2` terms. -/
theorem partialSum_powerWeight_ge {η x : ℝ} (hη : 0 ≤ η) (hx : 1 ≤ x) :
    x ^ (1 - η) / 2 ≤ partialSum (powerWeight η) x := by
  have hx0 : 0 < x := by linarith
  have hterm : ∀ n ∈ Ioc 0 ⌊x⌋₊, x ^ (-η) ≤ powerWeight η n := by
    intro n hn
    obtain ⟨h1, h2⟩ := mem_Ioc.mp hn
    have hn1 : (0 : ℝ) < n := by exact_mod_cast h1
    exact Real.rpow_le_rpow_of_nonpos hn1 ((Nat.cast_le.mpr h2).trans (Nat.floor_le hx0.le))
      (by linarith)
  have hsum := card_nsmul_le_sum _ _ _ hterm
  rw [Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul] at hsum
  have hfl : x / 2 ≤ (⌊x⌋₊ : ℝ) := by
    have h1 : (1 : ℝ) ≤ ⌊x⌋₊ := by exact_mod_cast Nat.one_le_floor_iff x |>.mpr hx
    have h2 := Nat.lt_floor_add_one x
    linarith
  have hxe : x ^ (1 - η) = x * x ^ (-η) := by
    rw [sub_eq_add_neg, Real.rpow_add hx0, Real.rpow_one]
  have hpos : 0 ≤ x ^ (-η) := Real.rpow_nonneg hx0.le _
  calc x ^ (1 - η) / 2 = x / 2 * x ^ (-η) := by rw [hxe]; ring
    _ ≤ (⌊x⌋₊ : ℝ) * x ^ (-η) := mul_le_mul_of_nonneg_right hfl hpos
    _ ≤ partialSum (powerWeight η) x := hsum

/-- `Σ_{1 ≤ n ≤ N} 1/√n ≤ 2√N`, by `1/√(N+1) ≤ 2(√(N+1) − √N)`. -/
theorem sum_inv_sqrt_le (N : ℕ) : ∑ n ∈ Ioc 0 N, (1 / √(n : ℝ)) ≤ 2 * √(N : ℝ) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Ioc_succ_top (Nat.zero_le N)]
    set s := √(N : ℝ)
    set t := √((N + 1 : ℕ) : ℝ)
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have ht0 : 0 < t := Real.sqrt_pos.mpr (by positivity)
    have hs2 : s ^ 2 = N := Real.sq_sqrt (Nat.cast_nonneg N)
    have ht2 : t ^ 2 = (N : ℝ) + 1 := by
      rw [Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; ring
    have hstep : 1 / t ≤ 2 * t - 2 * s := by
      rw [div_le_iff₀ ht0]; nlinarith [sq_nonneg (t - s)]
    linarith

/-- **Upper bound**: `Σ_{n ≤ x} n^{−η} ≤ 2√x` for `η ≥ ½`. -/
theorem partialSum_powerWeight_le {η x : ℝ} (hη : 1 / 2 ≤ η) (hx : 0 ≤ x) :
    partialSum (powerWeight η) x ≤ 2 * √x := by
  calc partialSum (powerWeight η) x ≤ ∑ n ∈ Ioc 0 ⌊x⌋₊, (1 / √(n : ℝ)) := by
        refine sum_le_sum fun n hn => ?_
        have h1 : (1 : ℝ) ≤ n := by exact_mod_cast (mem_Ioc.mp hn).1
        calc powerWeight η n ≤ (n : ℝ) ^ (-(1 / 2 : ℝ)) :=
              Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
          _ = 1 / √(n : ℝ) := by
              rw [Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow, one_div]
    _ ≤ 2 * √(⌊x⌋₊ : ℝ) := sum_inv_sqrt_le _
    _ ≤ 2 * √x := by gcongr; exact Nat.floor_le hx

/-- `√x log² x = o(x^{1−η})` for `η < ½`. -/
theorem sqrtScale_isLittleO_rpow {η : ℝ} (hη : η < 1 / 2) :
    sqrtScale =o[atTop] fun x => x ^ (1 - η) := by
  set r := (1 / 2 - η) / 2 with hr
  have hr0 : 0 < r := by rw [hr]; linarith
  have h := (isBigO_refl (fun x : ℝ => x ^ (1 / 2 : ℝ)) atTop).mul_isLittleO
    ((isLittleO_log_rpow_atTop hr0).mul (isLittleO_log_rpow_atTop hr0))
  refine (h.congr' ?_ ?_)
  · filter_upwards with x
    simp only [sqrtScale, Real.sqrt_eq_rpow, sq]
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [← Real.rpow_add hx, ← Real.rpow_add hx, hr]
    ring_nf

/-- `ε n^{−η} ∈ 𝒬` for `η ≥ ½`. -/
theorem smul_powerWeight_mem_sqrtClass {η : ℝ} (hη : 1 / 2 ≤ η) (ε : ℝ) :
    ε • powerWeight η ∈ sqrtClass := by
  refine PrecisionClass.smul_mem ε (IsBigO.of_bound 2 ?_)
  filter_upwards [eventually_ge_atTop (exp 1)] with x hx
  have hx0 : 0 ≤ x := le_trans (exp_pos 1).le hx
  rw [Real.norm_of_nonneg (partialSum_nonneg (powerWeight_nonneg η) x),
    Real.norm_of_nonneg (sqrtScale_nonneg x)]
  exact (partialSum_powerWeight_le hη hx0).trans (by linarith [sqrt_le_sqrtScale hx])

/-- `ε n^{−η} ∉ 𝒬` for `ε ≠ 0` and `0 ≤ η < ½`. -/
theorem smul_powerWeight_not_mem_sqrtClass {ε η : ℝ} (hε : ε ≠ 0) (hη0 : 0 ≤ η) (hη : η < 1 / 2) :
    ε • powerWeight η ∉ sqrtClass := by
  refine not_mem_precisionClass_of_lower_bound (sqrtScale_isLittleO_rpow hη)
    (c := |ε| / 2) (by positivity) ?_ ?_
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    have hx0 : 0 < x := by linarith
    simp only [partialSum_smul, norm_mul, Real.norm_eq_abs]
    rw [abs_of_nonneg (Real.rpow_nonneg hx0.le _),
      abs_of_nonneg (partialSum_nonneg (powerWeight_nonneg η) x)]
    have := partialSum_powerWeight_ge hη0 hx
    nlinarith [abs_nonneg ε]
  · exact (eventually_gt_atTop (0 : ℝ)).frequently.mono fun x hx =>
      (Real.rpow_pos_of_pos hx _).ne'

/-- **The power threshold.** For `ε ≠ 0`, `η ≥ 0`: `ε n^{−η} ∈ 𝒬 ↔ η ≥ ½`. -/
theorem smul_powerWeight_mem_sqrtClass_iff {ε η : ℝ} (hε : ε ≠ 0) (hη0 : 0 ≤ η) :
    ε • powerWeight η ∈ sqrtClass ↔ 1 / 2 ≤ η := by
  refine ⟨fun h => ?_, fun h => smul_powerWeight_mem_sqrtClass h ε⟩
  by_contra hlt
  exact smul_powerWeight_not_mem_sqrtClass hε hη0 (not_le.mp hlt) h

/-- **Precision rigidity of the count.** No weight satisfies the count together with its
perturbation by `ε n^{−η}`, `ε ≠ 0`, `0 ≤ η < ½`. -/
theorem not_count_and_count_add_smul_powerWeight (a : ℕ → ℝ) {ε η : ℝ} (hε : ε ≠ 0)
    (hη0 : 0 ≤ η) (hη : η < 1 / 2) : ¬ (Count a ∧ Count (a + ε • powerWeight η)) := fun ⟨h, h'⟩ =>
  smul_powerWeight_not_mem_sqrtClass hε hη0 hη ((count_add_iff_mem_sqrtClass h _).mp h')

/-- **Sharpness.** Perturbations `ε n^{−η}` with `η ≥ ½` preserve the count. -/
theorem count_add_smul_powerWeight {a : ℕ → ℝ} (ha : Count a) {η : ℝ} (hη : 1 / 2 ≤ η) (ε : ℝ) :
    Count (a + ε • powerWeight η) :=
  (count_add_iff_mem_sqrtClass ha _).mpr (smul_powerWeight_mem_sqrtClass hη ε)

end GaloisForLFunctions.ArithmeticOfSquareRootPrecision
