import GaloisForLFunctions.RHTower.PhotonicLosslessProductPortThinSlab
import GaloisForLFunctions.RHTower.PhotonicIntegerClockHalfRate

/-!
# Density law for the RH-complete lossless product port

For the full RH-complete PTR class, that is nonzero multiples of finite products
of lossless temporal-stack entries, the Fresnel–Lee–Yang budgets of all factors
add. Ξ's zero count bounds the sum. For every scale `x ≥ 1`, eventually any
selected family `S` of slabs of all factors satisfies

  `Σ_{s ∈ S} (2x·τ_s - 1) ≤ x log x - x + C √x`

with an absolute `C`. Equivalently `|S| ≥ 2x·Σ_S τ - x log x + x - C√x`. Two
consequences:

* *integer density:* slabs of total duration `½ log x + d` number at least
  `x(1 + 2d) - C√x`;
* *long-slab scarcity:* slabs of duration at least `τ₀` number at most
  `(x log x - x + C√x)/(2xτ₀ - 1)` for every `x > 1/(2τ₀)`.
-/

open Complex Metric Set Filter Topology Finset
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-- Range sums over `getD` are list sums. -/
theorem sum_range_getD_eq_sum_map {α : Type*} (l : List α) (d : α) (g : α → ℝ) :
    ∑ j ∈ range l.length, g (l.getD j d) = (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.length_cons, Finset.sum_range_succ', List.map_cons, List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero, ih]
    ring

/-- The budget of a nonempty lossless list stack at a general circle. -/
theorem ptrLosslessStack_budget_le_zeroSumBall_general (l : List (ℝ × ℝ)) (hl : l ≠ [])
    (hpos : ∀ x ∈ l, 0 < x.1 ∧ 0 < x.2) {T η : ℝ} (hT : 0 < T) (hη : 0 < η)
    (hsph : ∀ z ∈ sphere ((T : ℂ) / 2) (T / 2 + η), ptrLosslessStackEntry l z ≠ 0) :
    (l.map fun s => (((⌈(2 * s.2) * T / (2 * Real.pi)⌉ : ℤ) : ℝ) - 1)).sum ≤
      (zeroSumBall (ptrLosslessStackEntry l) ((T : ℂ) / 2) (T / 2 + η)).re := by
  have hlen : l.length ≠ 0 := by simpa using hl
  have hκ : ∀ j, 0 < ptrListKappa l j := by
    intro j
    by_cases hj : j ≤ l.length - 1
    · exact (hpos _ (ptrList_mem_of_le hl hj)).1
    · have : l.reverse.getD j (1, 1) = (1, 1) := by
        apply List.getD_eq_default; rw [List.length_reverse]; omega
      show 0 < (l.reverse.getD j (1, 1)).1
      rw [this]; norm_num
  have hτ : ∀ j, 0 < ptrListTau l j := by
    intro j
    by_cases hj : j ≤ l.length - 1
    · exact (hpos _ (ptrList_mem_of_le hl hj)).2
    · have : l.reverse.getD j (1, 1) = (1, 1) := by
        apply List.getD_eq_default; rw [List.length_reverse]; omega
      show 0 < (l.reverse.getD j (1, 1)).2
      rw [this]; norm_num
  have hentry : ptrLosslessStackEntry l =
      fun k => ptrLosslessStackSeq (ptrListKappa l) (ptrListTau l) (l.length - 1) k 0 0 := by
    funext k
    rw [ptrLosslessStackEntry, ptrLosslessStack_eq_seq l hl]
  rw [hentry] at hsph ⊢
  have hb := ptrLosslessStackSeq_budget_le_zeroSumBall _ _ _ hκ hτ hT hη hsph
  have hsum : ∑ j : Fin (l.length - 1 + 1),
      (((⌈(2 * ptrListTau l j) * T / (2 * Real.pi)⌉ : ℤ) : ℝ) - 1) =
      (l.map fun s => (((⌈(2 * s.2) * T / (2 * Real.pi)⌉ : ℤ) : ℝ) - 1)).sum := by
    rw [Fin.sum_univ_eq_sum_range (fun j =>
      (((⌈(2 * ptrListTau l j) * T / (2 * Real.pi)⌉ : ℤ) : ℝ) - 1)) (l.length - 1 + 1)]
    have hl1 : l.length - 1 + 1 = l.reverse.length := by rw [List.length_reverse]; omega
    rw [hl1]
    simp only [ptrListTau]
    rw [sum_range_getD_eq_sum_map l.reverse (1, 1)
      (fun s => (((⌈(2 * s.2) * T / (2 * Real.pi)⌉ : ℤ) : ℝ) - 1)), List.map_reverse,
      List.sum_reverse]
  rw [← hsum]
  exact hb

/-- Disc counts of finite products of lossless entries add. -/
theorem zeroSumBall_prod_ptrLosslessStackEntry (M : List (List (ℝ × ℝ))) {c : ℂ} {t : ℝ}
    (ht : 0 ≤ t) (hM : ∀ l ∈ M, ∀ z ∈ sphere c t, ptrLosslessStackEntry l z ≠ 0) :
    zeroSumBall (fun k => (M.map fun l => ptrLosslessStackEntry l k).prod) c t =
      (M.map fun l => zeroSumBall (ptrLosslessStackEntry l) c t).sum := by
  induction M with
  | nil =>
    simp only [List.map_nil, List.prod_nil, List.sum_nil]
    exact zeroSumBall_const_one _ _
  | cons l M ih =>
    have hM' : ∀ l' ∈ M, ∀ z ∈ sphere c t, ptrLosslessStackEntry l' z ≠ 0 :=
      fun l' hl' => hM l' (List.mem_cons_of_mem _ hl')
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    have hMs : ∀ z ∈ sphere c t, (M.map fun l => ptrLosslessStackEntry l z).prod ≠ 0 := by
      intro z hz h
      rw [List.prod_eq_zero_iff, List.mem_map] at h
      obtain ⟨l', hl', h'⟩ := h
      exact hM' l' hl' z hz h'
    rw [zeroSumBall_mul (f := ptrLosslessStackEntry l)
      (g := fun k => (M.map fun l => ptrLosslessStackEntry l k).prod)
      (ptrLosslessStack_differentiable l 0 0) (differentiable_prod_ptrLosslessStackEntry M) ht
      (hM l (List.mem_cons_self ..)) hMs, ih hM']

theorem re_list_sum (M : List ℂ) : M.sum.re = (M.map Complex.re).sum := by
  induction M <;> simp [*]

theorem sum_map_filter_eq_sum_map_ite {α : Type*} (l : List α) (P : α → Prop) [DecidablePred P]
    (g : α → ℝ) :
    ((l.filter fun s => P s).map g).sum = (l.map fun s => if P s then g s else 0).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    by_cases hPa : P a
    · simp only [List.filter_cons, hPa, decide_true, ↓reduceIte, List.map_cons, List.sum_cons, ih]
    · simp only [List.filter_cons, hPa, decide_false, Bool.false_eq_true, ↓reduceIte,
        List.map_cons, List.sum_cons, ih, zero_add]

/-- **Density law for the product port.** There is an absolute `C` such that for
every lossless product-port approximant of `Ξ`, every scale `x ≥ 1` and every
slab predicate `P`, eventually
`Σ_{factors} Σ_{slabs s with P s} (2x·τ_s - 1) ≤ x log x - x + C√x`. -/
theorem exists_ptrLosslessProductPort_density_law : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (c : ℕ → ℂ) (L : ℕ → List (List (ℝ × ℝ))), (∀ n, c n ≠ 0) →
      (∀ n, ∀ l ∈ L n, ∀ s ∈ l, 0 < s.1 ∧ 0 < s.2) →
      TendstoLocallyUniformly (fun n => ptrLosslessProductPort (c n) (L n)) XiC atTop →
      ∀ x : ℝ, 1 ≤ x → ∀ P : ℝ × ℝ → Prop, [DecidablePred P] →
        ∀ᶠ n in atTop, ((L n).map fun l =>
          ((l.filter fun s => P s).map fun s => 2 * x * s.2 - 1).sum).sum ≤
            x * Real.log x - x + C * Real.sqrt x := by
  obtain ⟨C, hC, hbound⟩ := LeeYangCount.exists_two_pi_div_mul_xiZeroCount_le
  refine ⟨C, hC, fun c L hc hL hconv x hx P _ => ?_⟩
  have hπ := Real.pi_pos
  have hxpos : 0 < x := by linarith
  set T : ℝ := 2 * Real.pi * x with hTdef
  have hT : 0 < T := by positivity
  have hT4 : 4 ≤ T := by
    have : (2 : ℝ) * 3 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    nlinarith
  obtain ⟨η, hη0, hη1, hsph⟩ := exists_admissible_eta T hT
  have hXiCd : Differentiable ℂ XiC := fun z => (XiC_analytic z (mem_univ z)).differentiableAt
  have hH := eventually_zeroSumBall_eq_of_tendstoLocallyUniformly
    (fun n => ptrLosslessProductPort_differentiable (c n) (L n)) hXiCd hconv
    (c := (T : ℂ) / 2) (r := T / 2 + η) (R := T / 2 + η + 1) (by positivity) (by linarith) hsph
  have hS := LeeYangCount.eventually_ne_zero_on_sphere hXiCd.continuous hconv hsph
  have hcount : (zeroSumBall XiC ((T : ℂ) / 2) (T / 2 + η)).re ≤ (xiZeroCount (T + η) : ℝ) := by
    have h := LeeYangCount.zeroSumBall_le_xiZeroCount (E := fun _ => (1 : ℂ))
      (differentiable_const _) (fun _ => one_ne_zero) hT hη0 hη1
      (fun z hz => by simpa using hsph z hz)
    simpa using h
  have hgamma := hbound T η hT4 hη0 hη1
  have hTx : T / (2 * Real.pi) = x := by rw [hTdef]; field_simp
  have hNbound : (xiZeroCount (T + η) : ℝ) ≤ x * Real.log x - x + C * Real.sqrt x := by
    rw [hTx] at hgamma
    have h1 : 2 * Real.pi / T = 1 / x := by rw [hTdef]; field_simp
    rw [h1, one_div, inv_mul_le_iff₀ hxpos] at hgamma
    have hsqrt : x * (C / Real.sqrt T) ≤ C * Real.sqrt x := by
      have hsx : 0 < Real.sqrt x := Real.sqrt_pos.mpr hxpos
      have hle : Real.sqrt x ≤ Real.sqrt T := Real.sqrt_le_sqrt (by
        rw [hTdef]; nlinarith [Real.pi_gt_three])
      have h2 : C / Real.sqrt T ≤ C / Real.sqrt x := div_le_div_of_nonneg_left hC hsx hle
      have h3 : x * (C / Real.sqrt x) = C * Real.sqrt x := by
        rw [mul_div_assoc', div_eq_iff hsx.ne', mul_assoc, Real.mul_self_sqrt hxpos.le]
        ring
      calc x * (C / Real.sqrt T) ≤ x * (C / Real.sqrt x) :=
            mul_le_mul_of_nonneg_left h2 hxpos.le
        _ = C * Real.sqrt x := h3
    nlinarith [hgamma, hsqrt]
  filter_upwards [hH, hS] with n hn hs
  have hfac : ∀ l ∈ L n, ∀ z ∈ sphere ((T : ℂ) / 2) (T / 2 + η),
      ptrLosslessStackEntry l z ≠ 0 := by
    intro l hl z hz h
    apply hs z hz
    simp only [ptrLosslessProductPort]
    rw [List.prod_eq_zero (List.mem_map.mpr ⟨l, hl, h⟩), mul_zero]
  have hport : zeroSumBall (ptrLosslessProductPort (c n) (L n)) ((T : ℂ) / 2) (T / 2 + η) =
      ((L n).map fun l => zeroSumBall (ptrLosslessStackEntry l) ((T : ℂ) / 2)
        (T / 2 + η)).sum := by
    unfold ptrLosslessProductPort
    rw [LeeYangCount.zeroSumBall_const_mul (hc n),
      zeroSumBall_prod_ptrLosslessStackEntry (L n) (by positivity) hfac]
  have hyterm : ∀ s : ℝ × ℝ, (2 * s.2) * T / (2 * Real.pi) = 2 * x * s.2 := by
    intro s; rw [hTdef]; field_simp
  -- each factor: filtered linear sum ≤ full ceiling budget ≤ disc count
  have hfactor : ∀ l ∈ L n, ((l.filter fun s => P s).map fun s => 2 * x * s.2 - 1).sum ≤
      (zeroSumBall (ptrLosslessStackEntry l) ((T : ℂ) / 2) (T / 2 + η)).re := by
    intro l hl
    by_cases hne : l = []
    · subst hne
      have h1 : ptrLosslessStackEntry [] = fun _ => (1 : ℂ) := by
        funext k; simp [ptrLosslessStackEntry, ptrLosslessStack]
      rw [h1, zeroSumBall_const_one, Complex.zero_re]
      simp
    · refine le_trans ?_ (ptrLosslessStack_budget_le_zeroSumBall_general l hne (hL n l hl)
        hT hη0 (hfac l hl))
      have hpt : ∀ s ∈ l, (if P s then 2 * x * s.2 - 1 else 0) ≤
          (((⌈(2 * s.2) * T / (2 * Real.pi)⌉ : ℤ) : ℝ) - 1) := by
        intro s hs
        have hpos := (hL n l hl s hs).2
        have hy : 0 < (2 * s.2) * T / (2 * Real.pi) := by positivity
        have h1 : (1 : ℤ) ≤ ⌈(2 * s.2) * T / (2 * Real.pi)⌉ := Int.one_le_ceil_iff.mpr hy
        have h2 : (1 : ℝ) ≤ ((⌈(2 * s.2) * T / (2 * Real.pi)⌉ : ℤ) : ℝ) := by exact_mod_cast h1
        have h3 := Int.le_ceil ((2 * s.2) * T / (2 * Real.pi))
        have h4 := hyterm s
        split_ifs <;> linarith
      rw [sum_map_filter_eq_sum_map_ite l P (fun s => 2 * x * s.2 - 1)]
      exact List.sum_le_sum fun s hs => hpt s hs
  have htotal : ((L n).map fun l =>
      ((l.filter fun s => P s).map fun s => 2 * x * s.2 - 1).sum).sum ≤
      ((L n).map fun l => (zeroSumBall (ptrLosslessStackEntry l) ((T : ℂ) / 2)
        (T / 2 + η)).re).sum := List.sum_le_sum fun l hl => hfactor l hl
  have hre : ((L n).map fun l => (zeroSumBall (ptrLosslessStackEntry l) ((T : ℂ) / 2)
      (T / 2 + η)).re).sum = (zeroSumBall XiC ((T : ℂ) / 2) (T / 2 + η)).re := by
    rw [← hn, hport, re_list_sum, List.map_map]
    rfl
  rw [hre] at htotal
  exact (htotal.trans hcount).trans hNbound

/-- **Long-slab scarcity.** In the RH-complete lossless class, for every
threshold `τ₀ > 0` and every scale `x ≥ 1` with `2xτ₀ > 1`, eventually the number
of slabs of duration at least `τ₀`, over all factors, is at most
`(x log x - x + C√x)/(2xτ₀ - 1)`. -/
theorem exists_ptrLosslessProductPort_longSlab_scarcity : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (c : ℕ → ℂ) (L : ℕ → List (List (ℝ × ℝ))), (∀ n, c n ≠ 0) →
      (∀ n, ∀ l ∈ L n, ∀ s ∈ l, 0 < s.1 ∧ 0 < s.2) →
      TendstoLocallyUniformly (fun n => ptrLosslessProductPort (c n) (L n)) XiC atTop →
      ∀ τ₀ x : ℝ, 1 ≤ x → 1 < 2 * x * τ₀ →
        ∀ᶠ n in atTop, (((L n).map fun l => (l.filter fun s => decide (τ₀ ≤ s.2)).length).sum : ℝ) *
          (2 * x * τ₀ - 1) ≤ x * Real.log x - x + C * Real.sqrt x := by
  obtain ⟨C, hC, hlaw⟩ := exists_ptrLosslessProductPort_density_law
  refine ⟨C, hC, fun c L hc hL hconv τ₀ x hx hτx => ?_⟩
  filter_upwards [hlaw c L hc hL hconv x hx (fun s => τ₀ ≤ s.2)] with n hn
  refine le_trans ?_ hn
  have hfac : ∀ l : List (ℝ × ℝ),
      ((l.filter fun s => decide (τ₀ ≤ s.2)).length : ℝ) * (2 * x * τ₀ - 1) ≤
        ((l.filter fun s => τ₀ ≤ s.2).map fun s => 2 * x * s.2 - 1).sum := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      by_cases ha : τ₀ ≤ a.2
      · simp only [List.filter_cons, ha, decide_true, ↓reduceIte, List.length_cons,
          List.map_cons, List.sum_cons, Nat.cast_add, Nat.cast_one]
        have hxpos : 0 < x := by linarith
        have : 2 * x * τ₀ - 1 ≤ 2 * x * a.2 - 1 := by nlinarith
        linarith
      · simp only [List.filter_cons, ha, decide_false]
        simpa using ih
  have hsum : ∀ M : List (List (ℝ × ℝ)),
      ((M.map fun l => (l.filter fun s => decide (τ₀ ≤ s.2)).length).sum : ℝ) *
        (2 * x * τ₀ - 1) ≤ (M.map fun l =>
          ((l.filter fun s => τ₀ ≤ s.2).map fun s => 2 * x * s.2 - 1).sum).sum := by
    intro M
    induction M with
    | nil => simp
    | cons l M ih =>
      simp only [List.map_cons, List.sum_cons, add_mul]
      exact add_le_add (hfac l) ih
  exact hsum (L n)

end

end RHTower
