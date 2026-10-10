import GaloisForLFunctions.RHTower.PhotonicLosslessStackFresnelChain
import GaloisForLFunctions.RHTower.PhotonicLosslessProductPortRH

/-!
# Every lossless product-port approximant of Ξ is eventually thin-slab

The multiplicative port of lossless temporal media is RH-complete
(`riemannHypothesis_iff_XiC_limit_losslessProductPort`). This module shows the
Lee–Yang field-density law survives the port. Disc zero counts add over
products. Every factor, read through the Fresnel dictionary, carries its own
budget `Σ_j (⌈2τ_j T/2π⌉ - 1)`. Ξ has no zero in the disc `|z - 3| ≤ 7/2`.
Hence any normalized product of lossless stack entries converging locally
uniformly to Ξ eventually has every slab of every factor of duration at most
`π/6`.

So the RH-complete PTR class is necessarily a thin-slab class. No homogeneous
temporal segment longer than `π/6` can survive in a lossless approximant of Ξ,
and prime delay lines of duration `log p` or `½ log p`, `p ≥ 3`, are excluded.
-/

open Complex Metric Set Filter Topology Finset
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ### Disc zero counts of products -/

theorem continuousOn_logDeriv_sphere {f : ℂ → ℂ} (hf : Differentiable ℂ f) {c : ℂ} {t : ℝ}
    (hsph : ∀ z ∈ sphere c t, f z ≠ 0) : ContinuousOn (fun z => logDeriv f z) (sphere c t) := by
  intro z hz
  have hcont : ContinuousAt (deriv f) z := ((hf.analyticAt z).deriv).continuousAt
  exact (hcont.div (hf z).continuousAt (hsph z hz)).continuousWithinAt

/-- Disc zero counts add over products. -/
theorem zeroSumBall_mul {f g : ℂ → ℂ} (hf : Differentiable ℂ f) (hg : Differentiable ℂ g)
    {c : ℂ} {t : ℝ} (ht : 0 ≤ t) (hfs : ∀ z ∈ sphere c t, f z ≠ 0)
    (hgs : ∀ z ∈ sphere c t, g z ≠ 0) :
    zeroSumBall (fun z => f z * g z) c t = zeroSumBall f c t + zeroSumBall g c t := by
  unfold zeroSumBall
  rw [← add_div]
  congr 1
  have hcongr : EqOn (fun z => logDeriv (fun z => f z * g z) z)
      (fun z => logDeriv f z + logDeriv g z) (sphere c t) := fun z hz =>
    logDeriv_mul z (hfs z hz) (hgs z hz) (hf z) (hg z)
  rw [circleIntegral.integral_congr ht hcongr]
  exact circleIntegral.integral_add ((continuousOn_logDeriv_sphere hf hfs).circleIntegrable ht)
    ((continuousOn_logDeriv_sphere hg hgs).circleIntegrable ht)

/-! ### List stacks as indexed stacks -/

/-- Impedance of the `j`-th slab to act, counting from the first. -/
def ptrListKappa (L : List (ℝ × ℝ)) (j : ℕ) : ℝ := (L.reverse.getD j (1, 1)).1

/-- Duration of the `j`-th slab to act, counting from the first. -/
def ptrListTau (L : List (ℝ × ℝ)) (j : ℕ) : ℝ := (L.reverse.getD j (1, 1)).2

theorem ptrLosslessStackSeq_congr {κ κ' τ τ' : ℕ → ℝ} {N : ℕ}
    (hκ : ∀ j ≤ N, κ j = κ' j) (hτ : ∀ j ≤ N, τ j = τ' j) (k : ℂ) :
    ptrLosslessStackSeq κ τ N k = ptrLosslessStackSeq κ' τ' N k := by
  induction N with
  | zero => simp [ptrLosslessStackSeq, hκ 0 le_rfl, hτ 0 le_rfl]
  | succ N ih =>
    rw [ptrLosslessStackSeq, ptrLosslessStackSeq, hκ (N + 1) le_rfl, hτ (N + 1) le_rfl,
      ih (fun j hj => hκ j (by omega)) (fun j hj => hτ j (by omega))]

theorem ptrLosslessStack_eq_seq (L : List (ℝ × ℝ)) (hL : L ≠ []) (k : ℂ) :
    ptrLosslessStack L k =
      ptrLosslessStackSeq (ptrListKappa L) (ptrListTau L) (L.length - 1) k := by
  induction L with
  | nil => exact absurd rfl hL
  | cons x L ih =>
    by_cases hnil : L = []
    · subst hnil
      simp [ptrLosslessStack, ptrLosslessStackSeq, ptrListKappa, ptrListTau]
    · have hlen : (x :: L).length - 1 = (L.length - 1) + 1 := by
        have : L.length ≠ 0 := by simpa using hnil
        simp only [List.length_cons]; omega
      rw [hlen, ptrLosslessStackSeq]
      have hrev : (x :: L).reverse = L.reverse ++ [x] := List.reverse_cons
      have htop : ptrListKappa (x :: L) (L.length - 1 + 1) = x.1 ∧
          ptrListTau (x :: L) (L.length - 1 + 1) = x.2 := by
        have h1 : L.length - 1 + 1 = L.reverse.length := by
          rw [List.length_reverse]
          have : L.length ≠ 0 := by simpa using hnil
          omega
        simp only [ptrListKappa, ptrListTau, hrev, h1, List.getD_append_right, le_refl,
          Nat.sub_self, List.getD_cons_zero, and_self]
      rw [htop.1, htop.2]
      rw [show ptrLosslessStack (x :: L) k = ptrLosslessSlab x.1 x.2 k * ptrLosslessStack L k by
        simp [ptrLosslessStack]]
      rw [ih hnil]
      congr 1
      apply ptrLosslessStackSeq_congr
      · intro j hj
        have hj' : j < L.reverse.length := by
          rw [List.length_reverse]
          have : L.length ≠ 0 := by simpa using hnil
          omega
        simp only [ptrListKappa, hrev, List.getD_append _ _ _ _ hj']
      · intro j hj
        have hj' : j < L.reverse.length := by
          rw [List.length_reverse]
          have : L.length ≠ 0 := by simpa using hnil
          omega
        simp only [ptrListTau, hrev, List.getD_append _ _ _ _ hj']

theorem ptrList_mem_of_le {L : List (ℝ × ℝ)} (hL : L ≠ []) {j : ℕ} (hj : j ≤ L.length - 1) :
    (ptrListKappa L j, ptrListTau L j) ∈ L := by
  have hlt : j < L.reverse.length := by
    rw [List.length_reverse]
    have : L.length ≠ 0 := by simpa using hL
    omega
  have hmem : L.reverse.getD j (1, 1) ∈ L.reverse := by
    rw [List.getD_eq_getElem _ _ hlt]
    exact List.getElem_mem hlt
  simpa [ptrListKappa, ptrListTau] using List.mem_reverse.mp hmem

/-! ### Per-stack budget -/

/-- **Lee–Yang budget of one lossless stack.** -/
theorem ptrLosslessStackSeq_budget_le_zeroSumBall (κ τ : ℕ → ℝ) (N : ℕ)
    (hκ : ∀ j, 0 < κ j) (hτ : ∀ j, 0 < τ j) {T η : ℝ} (hT : 0 < T) (hη : 0 < η)
    (hsph : ∀ z ∈ sphere ((T : ℂ) / 2) (T / 2 + η), ptrLosslessStackSeq κ τ N z 0 0 ≠ 0) :
    ∑ j : Fin (N + 1), (((⌈(2 * τ j) * T / (2 * Real.pi)⌉ : ℤ) : ℝ) - 1) ≤
      (zeroSumBall (fun k => ptrLosslessStackSeq κ τ N k 0 0) ((T : ℂ) / 2) (T / 2 + η)).re := by
  let L := LeeYangChain.cChainDatum N (ptrFresnelWall κ) (ptrFresnelWall_norm_le hκ)
    (fun j => 2 * τ j) (fun j => by have := hτ j; positivity)
  have hrestr : ∀ k, L.restr k =
      LeeYangChain.cChainZ (ptrFresnelWall κ) (ptrFresnelField τ k) N := by
    intro k
    rw [ptrFresnelChain_eq_restr]
    exact LeeYangChain.cChainDatum_restr _ _ _ _ _ k
  set K : ℂ := (1 / 2) * ∏ j ∈ range N, ptrFresnelScale (κ j) (κ (j + 1)) with hKdef
  set S : ℂ := Complex.I * ∑ j ∈ range (N + 1), (τ j : ℂ) with hSdef
  have hK : K ≠ 0 := mul_ne_zero (by norm_num)
    (Finset.prod_ne_zero_iff.mpr fun j _ => ptrFresnelScale_ne_zero (hκ j) (hκ (j + 1)))
  have hF : (fun k => ptrLosslessStackSeq κ τ N k 0 0) =
      fun k => K * (Complex.exp (S * k) * L.restr k) := by
    funext k
    rw [ptrLosslessStackSeq_entry_eq _ _ hκ, ptrFresnelPrefactor_eq, hrestr]
    ring
  have hsph' : ∀ z ∈ sphere ((T : ℂ) / 2) (T / 2 + η), L.restr z ≠ 0 := by
    intro z hz h
    apply hsph z hz
    have h2 : (fun k => K * (Complex.exp (S * k) * L.restr k)) z = 0 := by
      show K * (Complex.exp (S * z) * L.restr z) = 0
      rw [h, mul_zero, mul_zero]
    exact (congrFun hF z).trans h2
  have hb := LeeYangCount.sum_ceil_sub_one_le_zeroSumBall L
    (LeeYangChain.cChainDatum_degreeOf _ _ _ _ _) hT hη hsph'
  rw [hF, LeeYangCount.zeroSumBall_const_mul hK,
    zeroSumBall_exp_mul L.differentiable_restr _ _ (by positivity) hsph']
  exact hb

private theorem budget_term_nonneg {τ T : ℝ} (hτ : 0 < τ) (hT : 0 < T) :
    0 ≤ (((⌈(2 * τ) * T / (2 * Real.pi)⌉ : ℤ) : ℝ) - 1) := by
  have hx : 0 < (2 * τ) * T / (2 * Real.pi) := by positivity
  have h1 : (1 : ℤ) ≤ ⌈(2 * τ) * T / (2 * Real.pi)⌉ := Int.one_le_ceil_iff.mpr hx
  have h2 : (1 : ℝ) ≤ ((⌈(2 * τ) * T / (2 * Real.pi)⌉ : ℤ) : ℝ) := by exact_mod_cast h1
  linarith

private theorem slab_le_of_budget_term_nonpos {τ : ℝ}
    (h : (((⌈(2 * τ) * 6 / (2 * Real.pi)⌉ : ℤ) : ℝ) - 1) ≤ 0) : τ ≤ Real.pi / 6 := by
  have hceil : ⌈(2 * τ) * 6 / (2 * Real.pi)⌉ ≤ 1 := by
    have : ((⌈(2 * τ) * 6 / (2 * Real.pi)⌉ : ℤ) : ℝ) ≤ 1 := by linarith
    exact_mod_cast this
  have hx := Int.ceil_le.mp hceil
  have hpi : 0 < Real.pi := Real.pi_pos
  rw [div_le_iff₀ (by positivity)] at hx
  push_cast at hx
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 6)]
  nlinarith

/-- The list-stack budget: every slab of a lossless list stack whose entry has
nonnegative-real-part budget at most `0` on the Ξ disc is short. -/
theorem ptrLosslessStack_budget_le_zeroSumBall (l : List (ℝ × ℝ)) (hl : l ≠ [])
    (hpos : ∀ x ∈ l, 0 < x.1 ∧ 0 < x.2)
    (hsph : ∀ z ∈ sphere (((6 : ℝ) : ℂ) / 2) (6 / 2 + 1 / 2), ptrLosslessStackEntry l z ≠ 0) :
    ∑ j : Fin (l.length - 1 + 1),
        (((⌈(2 * ptrListTau l j) * 6 / (2 * Real.pi)⌉ : ℤ) : ℝ) - 1) ≤
      (zeroSumBall (ptrLosslessStackEntry l) (((6 : ℝ) : ℂ) / 2) (6 / 2 + 1 / 2)).re := by
  have hκ : ∀ j, 0 < ptrListKappa l j := by
    intro j
    by_cases hj : j ≤ l.length - 1
    · exact (hpos _ (ptrList_mem_of_le hl hj)).1
    · have : l.reverse.getD j (1, 1) = (1, 1) := by
        apply List.getD_eq_default
        rw [List.length_reverse]
        have : l.length ≠ 0 := by simpa using hl
        omega
      show 0 < (l.reverse.getD j (1, 1)).1
      rw [this]; norm_num
  have hτ : ∀ j, 0 < ptrListTau l j := by
    intro j
    by_cases hj : j ≤ l.length - 1
    · exact (hpos _ (ptrList_mem_of_le hl hj)).2
    · have : l.reverse.getD j (1, 1) = (1, 1) := by
        apply List.getD_eq_default
        rw [List.length_reverse]
        have : l.length ≠ 0 := by simpa using hl
        omega
      show 0 < (l.reverse.getD j (1, 1)).2
      rw [this]; norm_num
  have hentry : ptrLosslessStackEntry l =
      fun k => ptrLosslessStackSeq (ptrListKappa l) (ptrListTau l) (l.length - 1) k 0 0 := by
    funext k
    rw [ptrLosslessStackEntry, ptrLosslessStack_eq_seq l hl]
  rw [hentry] at hsph ⊢
  exact ptrLosslessStackSeq_budget_le_zeroSumBall _ _ _ hκ hτ (by norm_num) (by norm_num) hsph

theorem differentiable_prod_ptrLosslessStackEntry (M : List (List (ℝ × ℝ))) :
    Differentiable ℂ (fun k => (M.map fun l => ptrLosslessStackEntry l k).prod) := by
  induction M with
  | nil => simp
  | cons l M ih =>
    simp only [List.map_cons, List.prod_cons]
    exact (ptrLosslessStack_differentiable l 0 0).mul ih

theorem zeroSumBall_const_one (c : ℂ) (t : ℝ) : zeroSumBall (fun _ => (1 : ℂ)) c t = 0 := by
  unfold zeroSumBall
  have h : (fun ζ => logDeriv (fun _ : ℂ => (1 : ℂ)) ζ) = fun _ => 0 := by
    funext ζ; simp [logDeriv]
  have h0 : (∮ x in C(c, t), (0 : ℂ)) = 0 := by
    have := circleIntegral.integral_const_mul (0 : ℂ) (fun _ => (1 : ℂ)) c t
    simpa using this
  rw [h, h0, zero_div]

/-! ### The thin-slab law for the product port -/

/-- **Thin-slab law for the RH-complete PTR class.** If nonzero multiples of
finite products of lossless temporal-stack entries converge locally uniformly to
Ξ, then eventually every slab of every factor has duration at most `π/6`. -/
theorem ptrLosslessProductPort_slab_le_of_tendsto_XiC
    (c : ℕ → ℂ) (L : ℕ → List (List (ℝ × ℝ))) (hc : ∀ n, c n ≠ 0)
    (hL : ∀ n, ∀ l ∈ L n, ∀ x ∈ l, 0 < x.1 ∧ 0 < x.2)
    (hconv : TendstoLocallyUniformly (fun n => ptrLosslessProductPort (c n) (L n)) XiC atTop) :
    ∀ᶠ n in atTop, ∀ l ∈ L n, ∀ x ∈ l, x.2 ≤ Real.pi / 6 := by
  have hXiCd : Differentiable ℂ XiC := fun z => (XiC_analytic z (mem_univ z)).differentiableAt
  have hc3 : (((6 : ℝ) : ℂ) / 2) = 3 := by push_cast; norm_num
  have hr3 : (6 : ℝ) / 2 + 1 / 2 = 7 / 2 := by norm_num
  have hsph : ∀ z ∈ sphere (((6 : ℝ) : ℂ) / 2) (6 / 2 + 1 / 2), XiC z ≠ 0 := by
    intro z hz
    rw [hc3, hr3] at hz
    exact XiC_ne_zero_of_mem_closedBall_three (sphere_subset_closedBall hz)
  have hH := eventually_zeroSumBall_eq_of_tendstoLocallyUniformly
    (fun n => ptrLosslessProductPort_differentiable (c n) (L n)) hXiCd hconv
    (c := ((6 : ℝ) : ℂ) / 2) (r := 6 / 2 + 1 / 2) (R := 6 / 2 + 1 / 2 + 1)
    (by norm_num) (by linarith) hsph
  have hS := LeeYangCount.eventually_ne_zero_on_sphere hXiCd.continuous hconv hsph
  have hzero : zeroSumBall XiC (((6 : ℝ) : ℂ) / 2) (6 / 2 + 1 / 2) = 0 := by
    have := zeroSumBall_XiC_three
    push_cast at this ⊢
    exact this
  filter_upwards [hH, hS] with n hn hs
  rw [hzero] at hn
  -- every factor is nonvanishing on the circle
  have hfac : ∀ l ∈ L n, ∀ z ∈ sphere (((6 : ℝ) : ℂ) / 2) (6 / 2 + 1 / 2),
      ptrLosslessStackEntry l z ≠ 0 := by
    intro l hl z hz h
    apply hs z hz
    simp only [ptrLosslessProductPort]
    rw [List.prod_eq_zero (List.mem_map.mpr ⟨l, hl, h⟩), mul_zero]
  -- disc count of the product is the sum of the factor counts
  have hsum : ∀ M : List (List (ℝ × ℝ)), (∀ l ∈ M, ∀ z ∈ sphere (((6 : ℝ) : ℂ) / 2)
      (6 / 2 + 1 / 2), ptrLosslessStackEntry l z ≠ 0) →
      zeroSumBall (fun k => (M.map fun l => ptrLosslessStackEntry l k).prod)
        (((6 : ℝ) : ℂ) / 2) (6 / 2 + 1 / 2) =
      (M.map fun l => zeroSumBall (ptrLosslessStackEntry l) (((6 : ℝ) : ℂ) / 2)
        (6 / 2 + 1 / 2)).sum := by
    intro M hM
    induction M with
    | nil =>
      simp only [List.map_nil, List.prod_nil, List.sum_nil]
      exact zeroSumBall_const_one _ _
    | cons l M ih =>
      have hM' : ∀ l' ∈ M, ∀ z ∈ sphere (((6 : ℝ) : ℂ) / 2) (6 / 2 + 1 / 2),
          ptrLosslessStackEntry l' z ≠ 0 := fun l' hl' => hM l' (List.mem_cons_of_mem _ hl')
      simp only [List.map_cons, List.prod_cons, List.sum_cons]
      have hdM := differentiable_prod_ptrLosslessStackEntry M
      have hMs : ∀ z ∈ sphere (((6 : ℝ) : ℂ) / 2) (6 / 2 + 1 / 2),
          (M.map fun l => ptrLosslessStackEntry l z).prod ≠ 0 := by
        intro z hz h
        rw [List.prod_eq_zero_iff, List.mem_map] at h
        obtain ⟨l', hl', h'⟩ := h
        exact hM' l' hl' z hz h'
      rw [zeroSumBall_mul (f := ptrLosslessStackEntry l)
        (g := fun k => (M.map fun l => ptrLosslessStackEntry l k).prod)
        (ptrLosslessStack_differentiable l 0 0) hdM (by norm_num)
        (hM l (List.mem_cons_self ..)) hMs, ih hM']
  have hport : zeroSumBall (ptrLosslessProductPort (c n) (L n)) (((6 : ℝ) : ℂ) / 2)
      (6 / 2 + 1 / 2) = ((L n).map fun l => zeroSumBall (ptrLosslessStackEntry l)
        (((6 : ℝ) : ℂ) / 2) (6 / 2 + 1 / 2)).sum := by
    unfold ptrLosslessProductPort
    rw [LeeYangCount.zeroSumBall_const_mul (hc n), hsum (L n) hfac]
  rw [hport] at hn
  -- budgets
  intro l hl x hx
  have hlne : l ≠ [] := List.ne_nil_of_mem hx
  have hbud : ∀ l' ∈ L n, l' ≠ [] → ∑ j : Fin (l'.length - 1 + 1),
      (((⌈(2 * ptrListTau l' j) * 6 / (2 * Real.pi)⌉ : ℤ) : ℝ) - 1) ≤
      (zeroSumBall (ptrLosslessStackEntry l') (((6 : ℝ) : ℂ) / 2) (6 / 2 + 1 / 2)).re :=
    fun l' hl' hne => ptrLosslessStack_budget_le_zeroSumBall l' hne (hL n l' hl') (hfac l' hl')
  have hzsb_nonneg : ∀ l' ∈ L n,
      0 ≤ (zeroSumBall (ptrLosslessStackEntry l') (((6 : ℝ) : ℂ) / 2) (6 / 2 + 1 / 2)).re := by
    intro l' hl'
    by_cases hne : l' = []
    · subst hne
      have h1 : ptrLosslessStackEntry [] = fun _ => (1 : ℂ) := by
        funext k; simp [ptrLosslessStackEntry, ptrLosslessStack]
      rw [h1, zeroSumBall_const_one, Complex.zero_re]
    · refine le_trans ?_ (hbud l' hl' hne)
      exact Finset.sum_nonneg fun j _ =>
        budget_term_nonneg (by
          by_cases hj : (j : ℕ) ≤ l'.length - 1
          · exact (hL n l' hl' _ (ptrList_mem_of_le hne hj)).2
          · exact absurd (Nat.lt_succ_iff.mp j.isLt) hj) (by norm_num)
  have hre_sum : (((L n).map fun l' => zeroSumBall (ptrLosslessStackEntry l')
      (((6 : ℝ) : ℂ) / 2) (6 / 2 + 1 / 2)).sum).re =
      ((L n).map fun l' => (zeroSumBall (ptrLosslessStackEntry l')
      (((6 : ℝ) : ℂ) / 2) (6 / 2 + 1 / 2)).re).sum := by
    have hgen : ∀ M : List ℂ, M.sum.re = (M.map Complex.re).sum := by
      intro M; induction M <;> simp [*]
    rw [hgen, List.map_map]
    rfl
  have hle_l : (zeroSumBall (ptrLosslessStackEntry l) (((6 : ℝ) : ℂ) / 2)
      (6 / 2 + 1 / 2)).re ≤ 0 := by
    have hsingle := List.single_le_sum (fun y hy => by
      obtain ⟨l', hl', rfl⟩ := List.mem_map.mp hy
      exact hzsb_nonneg l' hl') _ (List.mem_map.mpr ⟨l, hl, rfl⟩)
    have : (zeroSumBall (0 : ℂ → ℂ) 0 0).re = 0 := by simp [zeroSumBall]
    have hn' := congrArg Complex.re hn
    rw [hre_sum, Complex.zero_re] at hn'
    linarith [hsingle, hn'.symm.le, hn'.le]
  -- locate x as a slab index
  obtain ⟨j, hj, hxj⟩ : ∃ j ≤ l.length - 1, (ptrListKappa l j, ptrListTau l j) = x := by
    have hxr : x ∈ l.reverse := List.mem_reverse.mpr hx
    obtain ⟨j, hjlt, hjx⟩ := List.getElem_of_mem hxr
    refine ⟨j, ?_, ?_⟩
    · rw [List.length_reverse] at hjlt; omega
    · have hg : l.reverse.getD j (1, 1) = x := by rw [List.getD_eq_getElem _ _ hjlt, hjx]
      simp only [ptrListKappa, ptrListTau, hg]
  have hterm := (Finset.single_le_sum (fun i _ => budget_term_nonneg (by
      by_cases hi : (i : ℕ) ≤ l.length - 1
      · exact (hL n l hl _ (ptrList_mem_of_le hlne hi)).2
      · exact absurd (Nat.lt_succ_iff.mp i.isLt) hi) (by norm_num : (0 : ℝ) < 6))
    (Finset.mem_univ (⟨j, Nat.lt_succ_of_le hj⟩ : Fin (l.length - 1 + 1)))).trans
    ((hbud l hl hlne).trans hle_l)
  rw [← hxj]
  exact slab_le_of_budget_term_nonpos hterm

end

end RHTower
