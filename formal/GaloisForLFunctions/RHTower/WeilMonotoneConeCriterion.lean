import GaloisForLFunctions.RHTower.WeilPartialSumLandau
import GaloisForLFunctions.RHTower.WeilFullConeOneSidedCriterion

/-!
# The monotone cone: a smaller RH-equivalent cone

For a nonnegative combination `c` of autocorrelations of Weil tests write `ℓ_n(c)` for its
normalized symmetric value at `±log n`, `n ≥ 2`.  The **monotone cone** consists of the
combinations whose `ℓ`-values are nonnegative and nonincreasing in `n`; it lies inside the
nonnegative cone of `WeilOneSided.riemannHypothesis_iff_positiveOnNonnegCone`.

**Abel form of the prime pairing** (`linearCombination_vonMangoldt_eq_abel`).
`Σ_n Λ(n) ℓ_n = Σ_N ψ(N)(ℓ_N − ℓ_{N+1})`, with `ψ(N) = Σ_{n ≤ N} Λ(n)`; on the monotone cone the
weights `ℓ_N − ℓ_{N+1}` are nonnegative, so the prime pairing is a nonnegative average of the
Chebyshev function.

**Theorem** (`riemannHypothesis_iff_positiveOnMonotoneCone`).  RH holds iff `W_Λ ≥ 0` on the
monotone cone.

**Proof.**  `⇒` is Weil's criterion.  `⇐`: in the coordinates `Δv(N) = v(N) − v(N+1)` the
monotone cone is the nonnegative orthant, and its coordinate rays are realized by sums of pair
tests (`ℓ = 1_{[2, N]}`).  The M. Riesz extension theorem gives `S ≥ ψ` with
`⟨S, Δℓ(f)⟩ ≤ A(f)` for every test `f`, where `A` is the pole and archimedean part.  By Abel
summation `lam(n) = S(n) − S(n − 1)` is full-cone Weil-positive and
`Σ_{2 ≤ n ≤ N} (lam(n) − Λ(n)) = S(N) − ψ(N) ≥ 0`; one-signed excess partial sums force RH
(`WeilPartialSum.riemannHypothesis_of_partialSums`).
-/

open Finsupp

noncomputable section

namespace RHTower.WeilMonotoneCone

open WeilSpectral WeilOneSided Zeta23

local notation "Λ" => ArithmeticFunction.vonMangoldt

/-! ## Difference coordinates on `n ≥ 2` -/

/-- The successor on `n ≥ 2`. -/
def succJ (j : LogIndex) : LogIndex := ⟨j + 1, by have := j.2; omega⟩

theorem succJ_injective : Function.Injective succJ := fun a b h => by
  apply Subtype.ext
  have := congrArg Subtype.val h
  simp only [succJ] at this
  omega

theorem finite_support_diff (v : LogIndex →₀ ℝ) :
    (Function.support fun j : LogIndex => v j - v (succJ j)).Finite := by
  refine (v.support.finite_toSet.union
    (v.support.finite_toSet.preimage succJ_injective.injOn)).subset fun j hj => ?_
  rw [Function.mem_support] at hj
  by_contra h
  simp only [Set.mem_union, Finset.mem_coe, Finsupp.mem_support_iff, Set.mem_preimage, not_or,
    not_not] at h
  exact hj (by rw [h.1, h.2, sub_zero])

/-- `Δv(j) = v(j) − v(j + 1)`. -/
def diffVec (v : LogIndex →₀ ℝ) : LogIndex →₀ ℝ :=
  Finsupp.ofSupportFinite (fun j => v j - v (succJ j)) (finite_support_diff v)

theorem diffVec_apply (v : LogIndex →₀ ℝ) (j : LogIndex) : diffVec v j = v j - v (succJ j) := by
  simp [diffVec, Finsupp.ofSupportFinite_coe]

/-- The difference map as a linear map. -/
def diffMap : (LogIndex →₀ ℝ) →ₗ[ℝ] (LogIndex →₀ ℝ) where
  toFun := diffVec
  map_add' v w := by ext j; simp [diffVec_apply]; ring
  map_smul' a v := by ext j; simp [diffVec_apply]; ring

theorem diffMap_apply (v : LogIndex →₀ ℝ) (j : LogIndex) : diffMap v j = v j - v (succJ j) :=
  diffVec_apply v j

/-- The previous value of a sequence on `n ≥ 2`, with `0` before `2`. -/
def prev (S : LogIndex → ℝ) (j : LogIndex) : ℝ :=
  if h : 3 ≤ (j : ℕ) then S ⟨j - 1, by omega⟩ else 0

theorem diffMap_single (j : LogIndex) (a : ℝ) :
    diffMap (Finsupp.single j a) = Finsupp.single j a -
      if h : 3 ≤ (j : ℕ) then Finsupp.single ⟨j - 1, by omega⟩ a else 0 := by
  ext k
  rw [diffMap_apply, Finsupp.sub_apply]
  congr 1
  split_ifs with h
  · simp only [Finsupp.single_apply]
    have e : (j = succJ k) ↔ ((⟨(j : ℕ) - 1, by omega⟩ : LogIndex) = k) := by
      constructor
      · intro hj
        apply Subtype.ext
        have := congrArg Subtype.val hj
        simp only [succJ] at this ⊢
        omega
      · intro hk
        apply Subtype.ext
        have := congrArg Subtype.val hk
        simp only [succJ] at this ⊢
        omega
    by_cases hj : j = succJ k
    · rw [if_pos hj, if_pos (e.mp hj)]
    · rw [if_neg hj, if_neg fun h' => hj (e.mpr h')]
  · rw [Finsupp.single_apply, Finsupp.coe_zero, Pi.zero_apply, if_neg]
    intro hj
    have := congrArg Subtype.val hj
    simp only [succJ] at this
    have := k.2
    omega

/-- **Abel summation on `n ≥ 2`.**  `⟨S, Δv⟩ = ⟨S − S(· − 1), v⟩`. -/
theorem linearCombination_diffMap (S : LogIndex → ℝ) (v : LogIndex →₀ ℝ) :
    linearCombination ℝ S (diffMap v) = linearCombination ℝ (fun j => S j - prev S j) v := by
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => rw [map_add, map_add, hf, hg, map_add]
  | single j a =>
    rw [diffMap_single, map_sub, linearCombination_single, linearCombination_single, smul_eq_mul,
      smul_eq_mul, prev]
    split_ifs with h
    · rw [linearCombination_single, smul_eq_mul]; ring
    · simp

/-- The Chebyshev function on `n ≥ 2`. -/
def psiJ (j : LogIndex) : ℝ := ∑ n ∈ Finset.Icc 2 (j : ℕ), (Λ n : ℝ)

theorem sum_Icc_two_succ (f : ℕ → ℝ) {N : ℕ} (hN : 2 ≤ N + 1) :
    ∑ n ∈ Finset.Icc 2 (N + 1), f n = ∑ n ∈ Finset.Icc 2 N, f n + f (N + 1) :=
  Finset.sum_Icc_succ_top hN f

theorem psiJ_sub_prev (j : LogIndex) : psiJ j - prev psiJ j = Λ j := by
  obtain ⟨n, hn⟩ := j
  unfold prev psiJ
  split_ifs with h
  · simp only
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    rw [sum_Icc_two_succ _ (by omega), show m + 1 - 1 = m by omega]
    ring
  · have hn2 : n = 2 := by simp only at h; omega
    subst hn2
    simp

/-- **Abel form of the prime pairing.**  `Σ_n Λ(n) v(n) = Σ_N ψ(N)(v(N) − v(N+1))`. -/
theorem linearCombination_vonMangoldt_eq_abel (v : LogIndex →₀ ℝ) :
    linearCombination ℝ (fun j : LogIndex => (Λ j : ℝ)) v =
      linearCombination ℝ psiJ (diffMap v) := by
  rw [linearCombination_diffMap,
    show (fun j : LogIndex => (Λ j : ℝ)) = fun j => psiJ j - prev psiJ j from
      funext fun j => (psiJ_sub_prev j).symm]

/-- A finitely supported nonincreasing sequence on `n ≥ 2` is nonnegative. -/
theorem nonneg_of_diffMap_nonneg (v : LogIndex →₀ ℝ) (h : ∀ j, 0 ≤ diffMap v j) (j : LogIndex) :
    0 ≤ v j := by
  have hmono : ∀ t : ℕ, v ⟨j + t, by have := j.2; omega⟩ ≤ v j := by
    intro t
    induction t with
    | zero => exact le_rfl
    | succ t ih =>
      have hd := h ⟨j + t, by have := j.2; omega⟩
      rw [diffMap_apply] at hd
      have e : succJ ⟨j + t, by have := j.2; omega⟩ = ⟨j + (t + 1), by have := j.2; omega⟩ :=
        Subtype.ext (by simp [succJ]; ring)
      rw [e] at hd
      linarith
  obtain ⟨M, hM⟩ : ∃ M : ℕ, ∀ k : LogIndex, M < k → v k = 0 := by
    refine ⟨v.support.sup fun k => (k : ℕ), fun k hk => ?_⟩
    by_contra hne
    have hmem : k ∈ v.support := Finsupp.mem_support_iff.mpr hne
    have := Finset.le_sup (f := fun k : LogIndex => (k : ℕ)) hmem
    omega
  have h0 := hM ⟨j + (M + 1), by have := j.2; omega⟩ (by simp; omega)
  have := hmono (M + 1)
  linarith

/-! ## The monotone cone -/

/-- Weil positivity of `L` on the nonnegative combinations of tests whose `ℓ`-values are
nonnegative and nonincreasing in `n ≥ 2`. -/
def PositiveOnMonotoneCone (L : ℕ → ℝ) : Prop :=
  ∀ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) →
    (∀ n : ℕ, 2 ≤ n → 0 ≤ c.sum fun f t => t * logValue f.1 n) →
    (∀ n : ℕ, 2 ≤ n →
      (c.sum fun f t => t * logValue f.1 (n + 1)) ≤ c.sum fun f t => t * logValue f.1 n) →
    0 ≤ c.sum fun f t => t * (weilFullFunctional L (EF.weilTest f.1 f.1)).re

/-- The nonnegative combinations of tests. -/
abbrev NonnegCombo : Type := {c : WeilTestFn →₀ ℝ // ∀ f, 0 ≤ c f}

/-- The indicator `1_{[2, N]}`. -/
def indicatorVec (N : ℕ) : LogIndex →₀ ℝ :=
  ∑ m ∈ (Finset.Icc 2 N).subtype (fun n => 2 ≤ n), Finsupp.single m 1

theorem indicatorVec_apply (N : ℕ) (k : LogIndex) :
    indicatorVec N k = if (k : ℕ) ≤ N then 1 else 0 := by
  rw [indicatorVec, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  simp only [Finset.mem_subtype, Finset.mem_Icc]
  have := k.2
  by_cases h : (k : ℕ) ≤ N
  · rw [if_pos ⟨this, h⟩, if_pos h]
  · rw [if_neg fun h' => h h'.2, if_neg h]

theorem diffMap_indicatorVec (j : LogIndex) : diffMap (indicatorVec j) = Finsupp.single j 1 := by
  ext k
  rw [diffMap_apply, indicatorVec_apply, indicatorVec_apply, Finsupp.single_apply]
  simp only [succJ]
  by_cases hk : (k : ℕ) = j
  · rw [if_pos hk.le, if_neg (by omega), if_pos (Subtype.ext hk).symm]; ring
  · rw [if_neg fun h => hk (congrArg Subtype.val h).symm]
    split_ifs <;> first | (exfalso; omega) | ring

/-- The pair weight `2(∫ h_j²)/√j > 0`. -/
def pairWeight (j : LogIndex) : ℝ := 2 * (∫ t, (narrowBump j t) ^ 2) / Real.sqrt j

/-- A nonnegative combination of pair tests with `ℓ = 1_{[2, N]}`. -/
def indicatorCombo (N : ℕ) : WeilTestFn →₀ ℝ :=
  ∑ m ∈ (Finset.Icc 2 N).subtype (fun n => 2 ≤ n),
    Finsupp.single (pairTestFn m 1) (1 / pairWeight m)

theorem indicatorCombo_nonneg (N : ℕ) (f : WeilTestFn) : 0 ≤ indicatorCombo N f := by
  classical
  rw [indicatorCombo, Finsupp.finsetSum_apply]
  refine Finset.sum_nonneg fun m _ => ?_
  rw [Finsupp.single_apply]
  split_ifs
  · exact le_of_lt (one_div_pos.mpr (pairTest_weight_pos m))
  · exact le_rfl

theorem logVector_indicatorCombo (N : ℕ) :
    linearCombination ℝ logVector (indicatorCombo N) = indicatorVec N := by
  rw [indicatorCombo, map_sum, indicatorVec]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [linearCombination_single, logVector_pairTestFn, Finsupp.smul_single, smul_eq_mul]
  congr 1
  rw [show 2 * 1 * (∫ t, (narrowBump m t) ^ 2) / Real.sqrt m = pairWeight m by
    unfold pairWeight; ring, one_div,
    inv_mul_cancel₀ (show pairWeight m ≠ 0 from (pairTest_weight_pos m).ne')]

/-! ## The duality -/

/-- **Positivity on the monotone cone produces a Weil-positive system with one-signed excess
partial sums.** -/
theorem exists_weilPositiveFull_of_positiveOnMonotoneCone
    (h : PositiveOnMonotoneCone fun n => (Λ n : ℝ)) :
    ∃ lam : ℕ → ℝ, WeilPositiveFull lam ∧
      ∀ N : ℕ, 0 ≤ ∑ n ∈ Finset.Icc 2 N, (1 : ℝ) * (lam n - Λ n) := by
  set LCl : (WeilTestFn →₀ ℝ) →ₗ[ℝ] (LogIndex →₀ ℝ) := linearCombination ℝ logVector with hLCl
  set LCA : (WeilTestFn →₀ ℝ) →ₗ[ℝ] ℝ :=
    linearCombination ℝ (fun f : WeilTestFn => weilArchRe (EF.weilTest f.1 f.1)) with hLCA
  set T : NonnegCombo → (LogIndex →₀ ℝ) := fun i => diffMap (LCl i.1) with hT
  set D : NonnegCombo → ℝ := fun i => LCA i.1 with hD
  have hTlc : ∀ c' : NonnegCombo →₀ ℝ, linearCombination ℝ T c' =
      diffMap (LCl (linearCombination ℝ (fun i : NonnegCombo => i.1) c')) := by
    intro c'
    rw [← LinearMap.comp_apply, Finsupp.apply_linearCombination]
    rfl
  have hDlc : ∀ c' : NonnegCombo →₀ ℝ, linearCombination ℝ D c' =
      LCA (linearCombination ℝ (fun i : NonnegCombo => i.1) c') := by
    intro c'
    rw [Finsupp.apply_linearCombination]
    rfl
  have hflat_nonneg : ∀ c' : NonnegCombo →₀ ℝ, (∀ i, 0 ≤ c' i) →
      ∀ f, 0 ≤ linearCombination ℝ (fun i : NonnegCombo => i.1) c' f := by
    intro c' hc' f
    rw [linearCombination_apply, Finsupp.sum_apply]
    exact Finsupp.sum_nonneg fun i _ => by
      rw [Finsupp.smul_apply, smul_eq_mul]; exact mul_nonneg (hc' i) (i.2 f)
  obtain ⟨S, hSψ, hST⟩ := GaloisForLFunctions.HTGeometry.exists_ge_of_nonneg_on_nonneg_cone
    T D psiJ
    (fun j => ⟨⟨indicatorCombo j, indicatorCombo_nonneg j⟩, 1, one_pos, by
      simp only [hT]; rw [logVector_indicatorCombo, diffMap_indicatorVec]⟩)
    (fun c' hc' hcT => by
      set c := linearCombination ℝ (fun i : NonnegCombo => i.1) c' with hc
      have hc0 := hflat_nonneg c' hc'
      rw [hTlc] at hcT ⊢
      rw [hDlc, ← linearCombination_vonMangoldt_eq_abel]
      have hval : ∀ n (hn : 2 ≤ n), (c.sum fun f t => t * logValue f.1 n) = LCl c ⟨n, hn⟩ :=
        fun n hn => (linearCombination_logVector_apply c ⟨n, hn⟩).symm
      have hpos := h c hc0
        (fun n hn => by
          rw [hval n hn]; exact nonneg_of_diffMap_nonneg (LCl c) hcT ⟨n, hn⟩)
        (fun n hn => by
          rw [hval n hn, hval (n + 1) (by omega)]
          have := hcT ⟨n, hn⟩
          rw [diffMap_apply] at this
          have e : succJ ⟨n, hn⟩ = ⟨n + 1, by omega⟩ := rfl
          rw [e] at this
          linarith)
      rw [sum_re_weilFullFunctional] at hpos
      linarith)
  -- the Weil-positive system
  set lamJ : LogIndex → ℝ := fun j => S j - prev S j with hlamJ
  have hle : ∀ f : WeilTestFn,
      linearCombination ℝ lamJ (logVector f) ≤ weilArchRe (EF.weilTest f.1 f.1) := by
    intro f
    classical
    have h1 := hST ⟨Finsupp.single f 1, fun g => by
      rw [Finsupp.single_apply]; split_ifs <;> norm_num⟩
    simp only [hT, hD, hLCl, hLCA, linearCombination_single, one_smul] at h1
    rwa [linearCombination_diffMap] at h1
  refine ⟨_, weilPositiveFull_of_le_arch hle, fun N => ?_⟩
  -- telescoping
  have htel : ∀ N : ℕ, ∑ n ∈ Finset.Icc 2 N,
      (1 : ℝ) * ((fun n => if hn : 2 ≤ n then lamJ ⟨n, hn⟩ else 0) n - Λ n) =
      if hN : 2 ≤ N then S ⟨N, hN⟩ - psiJ ⟨N, hN⟩ else 0 := by
    intro N
    induction N with
    | zero => simp
    | succ N ih =>
      by_cases hN : 2 ≤ N + 1
      · rw [sum_Icc_two_succ _ hN, ih]
        have hp := psiJ_sub_prev ⟨N + 1, hN⟩
        simp only [dif_pos hN, one_mul, hlamJ]
        unfold prev at hp ⊢
        by_cases h3 : 3 ≤ N + 1
        · have hN2 : 2 ≤ N := by omega
          simp only [dif_pos hN2, dif_pos h3, show N + 1 - 1 = N by omega] at hp ⊢
          linarith
        · have hN1 : N = 1 := by omega
          subst hN1
          simp only [dif_neg h3, dif_neg (show ¬ 2 ≤ 1 by norm_num)] at hp ⊢
          linarith
      · rw [dif_neg hN]
        have hempty : Finset.Icc 2 (N + 1) = ∅ := Finset.Icc_eq_empty (by omega)
        rw [hempty, Finset.sum_empty]
  rw [htel N]
  split_ifs with hN
  · linarith [hSψ ⟨N, hN⟩]
  · exact le_rfl

/-- **The monotone-cone criterion.**  RH holds iff `W_Λ` is nonnegative on the nonnegative
combinations of tests whose `ℓ`-values are nonnegative and nonincreasing in `n ≥ 2`. -/
theorem riemannHypothesis_iff_positiveOnMonotoneCone :
    RiemannHypothesis ↔ PositiveOnMonotoneCone fun n => (Λ n : ℝ) := by
  constructor
  · intro hRH c hc _ _
    exact sum_nonneg_of_weilPositiveFull
      (riemannHypothesis_iff_weilPositiveFull_vonMangoldt.mp hRH) c hc
  · intro h
    obtain ⟨lam, hW, hS⟩ := exists_weilPositiveFull_of_positiveOnMonotoneCone h
    exact WeilPartialSum.riemannHypothesis_of_partialSums hW (Or.inl rfl) hS

end RHTower.WeilMonotoneCone
