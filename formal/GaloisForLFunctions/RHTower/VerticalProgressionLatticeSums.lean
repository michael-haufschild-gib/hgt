import Mathlib

/-!
# Exponential sums over the integers with a smooth weight

Write `e(x) = exp(2πix)`. For `g : ℝ → ℂ` of class `C^k`, supported in `[A, B]`, with
`‖g⁽ᵏ⁾‖ ≤ M`, and `u ∈ ℝ` at distance at least `δ > 0` from every integer,

`‖Σ_{ℓ ∈ ℤ} g(ℓ) e(ℓu)‖ ≤ (B − A + k + 1) M / (4δ)^k`  (`norm_latticeSum_le`).

**Proof.** With the backward difference `(Δg)(x) = g(x) − g(x − 1)`,
`Σ (Δg)(ℓ) e(ℓu) = (1 − e(u)) Σ g(ℓ) e(ℓu)`, so `(1 − e(u))^k Σ g e = Σ (Δ^k g) e`. By the mean value
theorem `‖Δ^k g‖ ≤ M`, and `Δ^k g` is supported in `[A, B + k]`. Finally
`|1 − e(u)| = 2|sin πu| ≥ 4δ` by Jordan's inequality.

The companion Riemann-sum estimate (`norm_tsum_sub_integral_le`): if `‖g'‖ ≤ M` and `g` is supported
in `[A, B]`, then `‖Σ_ℓ g(ℓ) − ∫ g‖ ≤ (B − A + 4) M`.
-/

open Complex MeasureTheory Set

namespace RHTower.VerticalAP

noncomputable section

/-- `e(x) = exp(2πix)`. -/
def unitExp (x : ℝ) : ℂ := Complex.exp (((2 * Real.pi * x : ℝ) : ℂ) * I)

theorem norm_unitExp (x : ℝ) : ‖unitExp x‖ = 1 := by
  unfold unitExp
  exact Complex.norm_exp_ofReal_mul_I _

theorem unitExp_add (x y : ℝ) : unitExp (x + y) = unitExp x * unitExp y := by
  unfold unitExp
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem unitExp_int (j : ℤ) : unitExp j = 1 := by
  unfold unitExp
  have : (((2 * Real.pi * (j : ℝ) : ℝ) : ℂ) * I) = (j : ℂ) * (2 * Real.pi * I) := by
    push_cast; ring
  rw [this]
  exact Complex.exp_int_mul_two_pi_mul_I j

/-- The lattice exponential sum `Σ_{ℓ ∈ ℤ} g(ℓ) e(ℓu)`. -/
def latticeSum (g : ℝ → ℂ) (u : ℝ) : ℂ := ∑' ℓ : ℤ, g ℓ * unitExp (ℓ * u)

/-- The backward difference `(Δg)(x) = g(x) − g(x − 1)`. -/
def backDiff (g : ℝ → ℂ) (x : ℝ) : ℂ := g x - g (x - 1)

theorem eq_zero_of_not_mem_Icc {g : ℝ → ℂ} {A B : ℝ} (hg : Function.support g ⊆ Icc A B)
    {x : ℝ} (hx : x ∉ Icc A B) : g x = 0 := by
  by_contra h
  exact hx (hg h)

theorem int_mem_Icc_iff {A B : ℝ} (ℓ : ℤ) :
    ((ℓ : ℝ) ∈ Icc A B) ↔ ℓ ∈ Finset.Icc ⌈A⌉ ⌊B⌋ := by
  rw [Finset.mem_Icc, Int.ceil_le, Int.le_floor, mem_Icc]

theorem latticeSum_eq_sum {g : ℝ → ℂ} {A B : ℝ} (hg : Function.support g ⊆ Icc A B) (u : ℝ) :
    latticeSum g u = ∑ ℓ ∈ Finset.Icc ⌈A⌉ ⌊B⌋, g ℓ * unitExp (ℓ * u) := by
  unfold latticeSum
  refine tsum_eq_sum fun ℓ hℓ => ?_
  rw [eq_zero_of_not_mem_Icc hg (fun h => hℓ ((int_mem_Icc_iff ℓ).mp h)), zero_mul]

theorem summable_lattice {g : ℝ → ℂ} {A B : ℝ} (hg : Function.support g ⊆ Icc A B) (u : ℝ) :
    Summable (fun ℓ : ℤ => g ℓ * unitExp (ℓ * u)) := by
  refine summable_of_ne_finset_zero (s := Finset.Icc ⌈A⌉ ⌊B⌋) fun ℓ hℓ => ?_
  rw [eq_zero_of_not_mem_Icc hg (fun h => hℓ ((int_mem_Icc_iff ℓ).mp h)), zero_mul]

theorem support_backDiff {g : ℝ → ℂ} {A B : ℝ} (hg : Function.support g ⊆ Icc A B) :
    Function.support (backDiff g) ⊆ Icc A (B + 1) := by
  intro x hx
  by_contra hxI
  apply hx
  have h1 : g x = 0 := eq_zero_of_not_mem_Icc hg fun h => hxI ⟨h.1, by linarith [h.2]⟩
  have h2 : g (x - 1) = 0 := eq_zero_of_not_mem_Icc hg fun h => by
    rw [mem_Icc, not_and_or, not_le, not_le] at hxI
    rcases hxI with h' | h' <;> [linarith [h.1]; linarith [h.2]]
  simp [backDiff, h1, h2]

theorem support_backDiff_iterate {g : ℝ → ℂ} {A B : ℝ} (hg : Function.support g ⊆ Icc A B)
    (k : ℕ) : Function.support (backDiff^[k] g) ⊆ Icc A (B + k) := by
  induction k with
  | zero => simpa using hg
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    refine (support_backDiff ih).trans ?_
    intro x hx
    exact ⟨hx.1, by push_cast; linarith [hx.2]⟩

/-- **Summation by parts:** `Σ (Δg)(ℓ) e(ℓu) = (1 − e(u)) Σ g(ℓ) e(ℓu)`. -/
theorem latticeSum_backDiff {g : ℝ → ℂ} {A B : ℝ} (hg : Function.support g ⊆ Icc A B) (u : ℝ) :
    latticeSum (backDiff g) u = (1 - unitExp u) * latticeSum g u := by
  have hshift : Function.support (fun x => g (x - 1)) ⊆ Icc (A + 1) (B + 1) := by
    intro x hx
    have := hg hx
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  have hs1 := summable_lattice hg u
  have hs2 := summable_lattice hshift u
  have hrw : ∑' ℓ : ℤ, g ((ℓ : ℝ) - 1) * unitExp (ℓ * u) =
      unitExp u * ∑' ℓ : ℤ, g ℓ * unitExp (ℓ * u) := by
    rw [← (Equiv.addRight (1 : ℤ)).tsum_eq, ← tsum_mul_left]
    refine tsum_congr fun ℓ => ?_
    simp only [Equiv.coe_addRight, Int.cast_add, Int.cast_one, add_sub_cancel_right]
    rw [add_mul, one_mul, add_comm, unitExp_add]
    ring
  unfold latticeSum backDiff
  simp_rw [sub_mul]
  rw [hs1.tsum_sub hs2, hrw]
  ring

theorem latticeSum_backDiff_iterate {g : ℝ → ℂ} {A B : ℝ} (hg : Function.support g ⊆ Icc A B)
    (u : ℝ) (k : ℕ) :
    latticeSum (backDiff^[k] g) u = (1 - unitExp u) ^ k * latticeSum g u := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', latticeSum_backDiff (support_backDiff_iterate hg k), ih]
    ring

/-- **Mean-value bound for iterated differences:** `‖Δ^k g‖ ≤ sup ‖g⁽ᵏ⁾‖`. -/
theorem norm_backDiff_iterate_le :
    ∀ (k : ℕ) {g : ℝ → ℂ} {M : ℝ}, ContDiff ℝ k g → (∀ y, ‖iteratedDeriv k g y‖ ≤ M) →
      ∀ x, ‖backDiff^[k] g x‖ ≤ M := by
  intro k
  induction k with
  | zero =>
    intro g M _ hM x
    simpa using hM x
  | succ k ih =>
    intro g M hg hM x
    rw [Function.iterate_succ_apply]
    have hgk : ContDiff ℝ k g := hg.of_le (by exact_mod_cast Nat.le_succ k)
    have hsh : ContDiff ℝ k (fun z => g (z - 1)) := hgk.comp (contDiff_id.sub contDiff_const)
    refine ih (hgk.sub hsh) (fun y => ?_) x
    rw [show (fun x => g x - g (x - 1)) = g - fun z => g (z - 1) from rfl, iteratedDeriv_sub hgk.contDiffAt hsh.contDiffAt, iteratedDeriv_comp_sub_const]
    have hdiff : Differentiable ℝ (iteratedDeriv k g) :=
      hg.differentiable_iteratedDeriv k (by exact_mod_cast Nat.lt_succ_self k)
    have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := iteratedDeriv k g)
      (a := y - 1) (b := y) (C := M)
      (fun z _ => (hdiff z).hasDerivAt.hasDerivWithinAt)
      (fun z _ => by rw [← iteratedDeriv_succ]; exact hM z) y ⟨by linarith, le_rfl⟩
    simpa using hmv

/-- A bounded weight supported in `[A, B]` has `‖Σ h(ℓ) e(ℓu)‖ ≤ (B − A + 1) M`. -/
theorem norm_latticeSum_le_of_bound {h : ℝ → ℂ} {A B M : ℝ} (hAB : A ≤ B)
    (hh : Function.support h ⊆ Icc A B) (hM : ∀ x, ‖h x‖ ≤ M) (u : ℝ) :
    ‖latticeSum h u‖ ≤ (B - A + 1) * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  rw [latticeSum_eq_sum hh]
  refine (norm_sum_le _ _).trans ?_
  have hterm : ∀ ℓ ∈ Finset.Icc ⌈A⌉ ⌊B⌋, ‖h ℓ * unitExp (ℓ * u)‖ ≤ M := fun ℓ _ => by
    rw [norm_mul, norm_unitExp, mul_one]; exact hM _
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul, Int.card_Icc]
  refine mul_le_mul_of_nonneg_right ?_ hM0
  rcases le_or_gt (⌊B⌋ + 1 - ⌈A⌉) 0 with hle | hlt
  · rw [Int.toNat_of_nonpos hle]; push_cast; linarith
  · have hcast : ((⌊B⌋ + 1 - ⌈A⌉).toNat : ℝ) = ((⌊B⌋ + 1 - ⌈A⌉ : ℤ) : ℝ) := by
      exact_mod_cast Int.toNat_of_nonneg hlt.le
    rw [hcast]
    push_cast
    linarith [Int.floor_le B, Int.le_ceil A]

/-- **Jordan's inequality on the circle:** `|1 − e(u)| ≥ 4 dist(u, ℤ)`. -/
theorem four_mul_le_norm_one_sub_unitExp {u δ : ℝ} (h : ∀ j : ℤ, δ ≤ |u - j|) :
    4 * δ ≤ ‖1 - unitExp u‖ := by
  set v : ℝ := u - round u with hv
  have hvδ : δ ≤ |v| := h (round u)
  have hv2 : |v| ≤ 1 / 2 := abs_sub_round u
  have hnorm : ‖1 - unitExp u‖ = 2 * |Real.sin (Real.pi * u)| := by
    rw [norm_sub_rev]
    unfold unitExp
    rw [show (((2 * Real.pi * u : ℝ) : ℂ) * I) = I * ((2 * Real.pi * u : ℝ) : ℂ) by ring,
      Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs, abs_mul, abs_two,
      show 2 * Real.pi * u / 2 = Real.pi * u by ring]
  have hsin : |Real.sin (Real.pi * u)| = |Real.sin (Real.pi * |v|)| := by
    have e1 : Real.pi * u = Real.pi * v + (round u : ℤ) * Real.pi := by rw [hv]; ring
    rw [e1, Real.sin_add_int_mul_pi, abs_mul, abs_neg_one_zpow, one_mul]
    rcases abs_cases v with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]
    · rw [h1, mul_neg, Real.sin_neg, abs_neg]
  have hjordan : 2 / Real.pi * (Real.pi * |v|) ≤ Real.sin (Real.pi * |v|) :=
    Real.mul_le_sin (by positivity) (by nlinarith [Real.pi_pos, abs_nonneg v])
  have hpi : 2 / Real.pi * (Real.pi * |v|) = 2 * |v| := by
    field_simp
  rw [hnorm, hsin, abs_of_nonneg (le_trans (by positivity) hjordan)]
  linarith

/-- **The lattice exponential sum bound.** For `g ∈ C^k` supported in `[A, B]` with `‖g⁽ᵏ⁾‖ ≤ M`
and `u` at distance `≥ δ > 0` from `ℤ`, `‖Σ g(ℓ) e(ℓu)‖ ≤ (B − A + k + 1) M / (4δ)^k`. -/
theorem norm_latticeSum_le {k : ℕ} {g : ℝ → ℂ} {A B M δ u : ℝ} (hAB : A ≤ B)
    (hg : ContDiff ℝ k g) (hsupp : Function.support g ⊆ Icc A B)
    (hM : ∀ y, ‖iteratedDeriv k g y‖ ≤ M) (hδ : 0 < δ) (hu : ∀ j : ℤ, δ ≤ |u - j|) :
    ‖latticeSum g u‖ ≤ (B - A + k + 1) * M / (4 * δ) ^ k := by
  have hiter := latticeSum_backDiff_iterate hsupp u k
  have hbd := norm_latticeSum_le_of_bound (by linarith : A ≤ B + k)
    (support_backDiff_iterate hsupp k) (norm_backDiff_iterate_le k hg hM) u
  have hj := four_mul_le_norm_one_sub_unitExp hu
  have hpos : 0 < (4 * δ) ^ k := by positivity
  rw [le_div_iff₀ hpos]
  calc ‖latticeSum g u‖ * (4 * δ) ^ k ≤ ‖latticeSum g u‖ * ‖1 - unitExp u‖ ^ k :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hj k) (norm_nonneg _)
    _ = ‖latticeSum (backDiff^[k] g) u‖ := by rw [hiter, norm_mul, norm_pow, mul_comm]
    _ ≤ (B + k - A + 1) * M := hbd
    _ = (B - A + k + 1) * M := by ring

/-! ## Riemann sums -/

/-- **Riemann sum against the integral.** If `g` is differentiable with `‖g'‖ ≤ M` and supported in
`[A, B]`, then `‖Σ_{ℓ ∈ ℤ} g(ℓ) − ∫ g‖ ≤ (B − A + 4) M`. -/
theorem norm_tsum_sub_integral_le {g : ℝ → ℂ} {A B M : ℝ} (hAB : A ≤ B)
    (hg : Differentiable ℝ g) (hsupp : Function.support g ⊆ Icc A B)
    (hM : ∀ x, ‖deriv g x‖ ≤ M) :
    ‖(∑' ℓ : ℤ, g ℓ) - ∫ x, g x‖ ≤ (B - A + 4) * M := by
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  set a : ℤ := ⌊A⌋ - 1 with ha
  set n : ℕ := (⌈B⌉ + 1 - a).toNat with hn
  have hnz : ((n : ℤ)) = ⌈B⌉ + 1 - a := by
    rw [hn, Int.toNat_of_nonneg]
    have : (⌊A⌋ : ℝ) ≤ ⌈B⌉ := (Int.floor_le A).trans (hAB.trans (Int.le_ceil B))
    have : ⌊A⌋ ≤ ⌈B⌉ := by exact_mod_cast this
    omega
  set pt : ℕ → ℝ := fun i => (a : ℝ) + i with hpt
  have hcont : Continuous g := hg.continuous
  -- the sum over integers is the sum over `a + i`, `i < n`
  have hsum : (∑' ℓ : ℤ, g ℓ) = ∑ i ∈ Finset.range n, g (pt i) := by
    have hinj : Set.InjOn (fun i : ℕ => a + (i : ℤ)) (Finset.range n) := by
      intro i _ j _ hij; simpa using hij
    rw [tsum_eq_sum (s := (Finset.range n).image fun i : ℕ => a + (i : ℤ)), Finset.sum_image hinj]
    · refine Finset.sum_congr rfl fun i _ => ?_
      simp [hpt]
    · intro ℓ hℓ
      refine eq_zero_of_not_mem_Icc hsupp fun hmem => hℓ ?_
      rw [Finset.mem_image]
      have h1 : ⌈A⌉ ≤ ℓ := Int.ceil_le.mpr hmem.1
      have h2 : ℓ ≤ ⌊B⌋ := Int.le_floor.mpr hmem.2
      have h3 : ⌊A⌋ ≤ ⌈A⌉ := Int.floor_le_ceil A
      have h4 : ⌊B⌋ ≤ ⌈B⌉ := Int.floor_le_ceil B
      refine ⟨(ℓ - a).toNat, ?_, ?_⟩
      · rw [Finset.mem_range]; omega
      · omega
  -- the integral over `ℝ` is the integral over `[a, a + n]`
  have hint : (∫ x, g x) = ∫ x in pt 0..pt n, g x := by
    have hle : pt 0 ≤ pt n := by simp [hpt]
    rw [intervalIntegral.integral_of_le hle, ← integral_Icc_eq_integral_Ioc]
    symm
    refine setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => ?_
    refine eq_zero_of_not_mem_Icc hsupp fun hmem => hx ⟨?_, ?_⟩
    · have : (⌊A⌋ : ℝ) ≤ A := Int.floor_le A
      simp only [hpt, Nat.cast_zero, add_zero, ha, Int.cast_sub, Int.cast_one]
      linarith [hmem.1]
    · have hnR : ((n : ℕ) : ℝ) = ((⌈B⌉ : ℤ) : ℝ) + 1 - a := by exact_mod_cast hnz
      simp only [hpt, hnR]
      linarith [hmem.2, Int.le_ceil B]
  have hsplit : (∫ x in pt 0..pt n, g x) = ∑ i ∈ Finset.range n, ∫ x in pt i..pt (i + 1), g x :=
    (intervalIntegral.sum_integral_adjacent_intervals fun i _ =>
      hcont.intervalIntegrable _ _).symm
  rw [hsum, hint, hsplit, ← Finset.sum_sub_distrib]
  have hcell : ∀ i ∈ Finset.range n, ‖g (pt i) - ∫ x in pt i..pt (i + 1), g x‖ ≤ M := by
    intro i _
    have hlen : pt (i + 1) = pt i + 1 := by simp [hpt]; ring
    have hconst : g (pt i) = ∫ x in pt i..pt (i + 1), g (pt i) := by
      rw [intervalIntegral.integral_const, hlen]; simp
    rw [hconst, ← intervalIntegral.integral_sub intervalIntegrable_const
      (hcont.intervalIntegrable _ _)]
    have hb : ∀ x ∈ Set.uIoc (pt i) (pt (i + 1)), ‖g (pt i) - g x‖ ≤ M := by
      intro x hx
      rw [Set.uIoc_of_le (by rw [hlen]; linarith)] at hx
      have hmv := norm_image_sub_le_of_norm_deriv_le_segment' (f := g) (a := pt i) (b := x)
        (C := M) (fun z _ => (hg z).hasDerivAt.hasDerivWithinAt) (fun z _ => hM z) x
        ⟨hx.1.le, le_rfl⟩
      rw [norm_sub_rev]
      refine hmv.trans ?_
      have : x - pt i ≤ 1 := by rw [hlen] at hx; linarith [hx.2]
      nlinarith
    have := intervalIntegral.norm_integral_le_of_norm_le_const hb
    rw [hlen] at this ⊢
    simpa using this
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hcell).trans ?_)
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  refine mul_le_mul_of_nonneg_right ?_ hM0
  have hnR : ((n : ℕ) : ℝ) = ((⌈B⌉ : ℤ) : ℝ) + 1 - a := by exact_mod_cast hnz
  rw [hnR, ha]
  push_cast
  have h1 : (⌈B⌉ : ℝ) < B + 1 := Int.ceil_lt_add_one B
  have h2 : A - 1 < (⌊A⌋ : ℝ) := Int.sub_one_lt_floor A
  linarith

end

end RHTower.VerticalAP
