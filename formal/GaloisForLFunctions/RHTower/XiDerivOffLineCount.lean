import GaloisForLFunctions.RHTower.RectangleHalfPlaneSegmentsWinding
import GaloisForLFunctions.RHTower.SpeiserExactCount
import GaloisForLFunctions.RHTower.XiLogDerivRePositiveStrict
import GaloisForLFunctions.RHTower.XiLogDerivLineOnePositive
import GaloisForLFunctions.RHTower.XiLogDerivReCriticalLine
import GaloisForLFunctions.RHTower.XiLogDerivSymmetry
import GaloisForLFunctions.RHTower.SeamFluxCompletion
import GaloisForLFunctions.RHTower.XiRealAxisNonvanishing
import GaloisForLFunctions.RHTower.XiEdgeLogDerivativeBlindness
import GaloisForLFunctions.RHTower.DeBruijnShiftContraction

/-!
# `ξ'` and `ξ` have the same number of zeros up to 3 between good heights

A height `T` is *good* (`XiGoodHeight`) if it is unshadowed (every zero `ρ` of `ξ` has
`(Re ρ − 1/2)² ≤ (T − Im ρ)²`) and `ξ(1/2 + iT) ≠ 0`, `ξ'(1/2 + iT) ≠ 0`.

**Theorem** (`exists_abs_count_deriv_xi_sub_xi_le`). For good heights `T₁ < T₂`, the numbers of zeros
of `ξ'` and of `ξ`, with multiplicity, in the closed rectangle `[−1, 2] × [T₁, T₂]` differ by at
most `3`.

**Proof.** On the boundary, `g = ξ'/ξ` lies in closed half-planes:
- `Re g > 0` on `Re s = 2` (`re_logDeriv_xi_pos_of_one_le_re`);
- `Re g < 0` on `Re s = −1`, by `g(1 − s) = −g(s)`;
- on a horizontal edge at a good height, `Re g > 0` for `Re s > 1/2` (strict disk criterion) and
  `Re g < 0` for `Re s < 1/2` (reflection);
- at `Re s = 1/2`, `g` is purely imaginary and nonzero.

The six-segment winding bound (`abs_sum_analyticOrderAt_sub_le_three`) applies to `F₁ = ξ'`,
`F₀ = ξ`.

**Corollary** (`offLine_count_deriv_xi_le`). In the same window, Rolle's theorem for the real
function `t ↦ ξ(1/2 + it)` puts a zero of `ξ'` on the line strictly between any two consecutive
on-line zeros of `ξ`. So `ξ'` has at least `A − 1` distinct on-line zeros, where `A` is the number
of distinct on-line zeros of `ξ`. With the count comparison this gives
`#off-line zeros of ξ' ≤ #off-line zeros of ξ + (on-line multiplicity excess of ξ) + 4`,
all counted with multiplicity: differentiation creates no off-line zeros beyond a bounded error.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- A good height: unshadowed, and neither `ξ` nor `ξ'` vanishes where the line meets it. -/
def XiGoodHeight (T : ℝ) : Prop :=
  SpeiserUnshadowed T ∧ xi (((1 / 2 : ℝ) : ℂ) + T * I) ≠ 0 ∧
    deriv xi (((1 / 2 : ℝ) : ℂ) + T * I) ≠ 0

theorem analyticOnNhd_deriv_xi : AnalyticOnNhd ℂ (deriv xi) Set.univ :=
  xi_analyticOnNhd_univ.deriv

theorem analyticAt_logDeriv_xi {z : ℂ} (hz : xi z ≠ 0) : AnalyticAt ℂ (logDeriv xi) z := by
  have h := xi_analyticOnNhd_univ z (Set.mem_univ z)
  have hq : AnalyticAt ℂ (fun w => deriv xi w / xi w) z := h.deriv.div h hz
  exact hq.congr (Filter.Eventually.of_forall fun w => (logDeriv_apply xi w).symm)

/-- The ratio relation between `ξ'`, `ξ` and `ξ'/ξ` where neither vanishes. -/
theorem ratioRelation_xi {z : ℂ} (hz : xi z ≠ 0) (hd : deriv xi z ≠ 0) :
    RatioRelation (deriv xi) xi (logDeriv xi) z := by
  have h := xi_analyticOnNhd_univ z (Set.mem_univ z)
  refine ⟨hd, hz, ?_⟩
  have hfun : logDeriv xi = fun w => deriv xi w / xi w := funext fun w => logDeriv_apply _ _
  have hq : logDeriv (fun w => deriv xi w / xi w) z = logDeriv (deriv xi) z - logDeriv xi z :=
    logDeriv_div z hd hz h.deriv.differentiableAt h.differentiableAt
  rw [← hfun] at hq
  rw [hq]; ring

theorem deriv_xi_ne_zero_of_logDeriv_ne_zero {z : ℂ} (h : logDeriv xi z ≠ 0) :
    deriv xi z ≠ 0 := fun h0 => h (by rw [logDeriv_apply, h0, zero_div])

/-- At an unshadowed height, `ξ` has no zero off the critical line. -/
theorem xi_ne_zero_of_speiserUnshadowed {T x : ℝ} (hu : SpeiserUnshadowed T) (hx : x ≠ 1 / 2) :
    xi ((x : ℂ) + T * I) ≠ 0 := by
  intro h0
  have h1 := hu _ h0
  have hre : ((x : ℂ) + T * I).re = x := by simp
  have him : ((x : ℂ) + T * I).im = T := by simp
  rw [hre, him, sub_self, zero_pow two_ne_zero] at h1
  have : x - 1 / 2 ≠ 0 := sub_ne_zero.mpr hx
  have := pow_pos (abs_pos.mpr this) 2
  rw [sq_abs] at this
  linarith

/-- Right half of a good horizontal line: `ξ'/ξ` is in the closed right half-plane and the slit
plane. -/
theorem halfPlaneGood_logDeriv_xi_right {T x : ℝ} (hg : XiGoodHeight T) (hx : 1 / 2 ≤ x) :
    xi ((x : ℂ) + T * I) ≠ 0 ∧ HalfPlaneGood (logDeriv xi) ((x : ℂ) + T * I) := by
  obtain ⟨hu, hxi, hd⟩ := hg
  have hre : ((x : ℂ) + T * I).re = x := by simp
  have him : ((x : ℂ) + T * I).im = T := by simp
  rcases eq_or_lt_of_le hx with h | h
  · subst h
    have hL : logDeriv xi (((1 / 2 : ℝ) : ℂ) + T * I) ≠ 0 := by
      rw [logDeriv_apply]; exact div_ne_zero hd hxi
    have hre0 : (logDeriv xi (((1 / 2 : ℝ) : ℂ) + T * I)).re = 0 :=
      re_logDeriv_xi_eq_zero_of_re_eq_half (by simp)
    refine ⟨hxi, analyticAt_logDeriv_xi hxi, ?_, by rw [hre0]⟩
    refine Complex.mem_slitPlane_iff.mpr (Or.inr fun him0 => hL ?_)
    exact Complex.ext hre0 him0
  · have hxi' := xi_ne_zero_of_speiserUnshadowed (x := x) hu (ne_of_gt h)
    have hpos : 0 < (logDeriv xi ((x : ℂ) + T * I)).re :=
      re_logDeriv_xi_pos_of_disk_bound (by rw [hre]; exact h) hxi' fun q => by
        have h1 := hu (q.1 : ℂ) (xi_eq_zero_of_mem_divisor_support q.1)
        rw [hre, him]
        have h2 : 0 < (x - 1 / 2) ^ 2 := by
          have : x - 1 / 2 ≠ 0 := by linarith
          positivity
        linarith
    exact ⟨hxi', analyticAt_logDeriv_xi hxi', Complex.mem_slitPlane_iff.mpr (Or.inl hpos),
      hpos.le⟩

/-- `ξ'/ξ(x + iT) = −conj (ξ'/ξ((1 − x) + iT))`. -/
theorem logDeriv_xi_reflect_horizontal (x T : ℝ) :
    logDeriv xi ((x : ℂ) + T * I) =
      -(starRingEnd ℂ) (logDeriv xi (((1 - x : ℝ) : ℂ) + T * I)) := by
  have h1 : ((x : ℂ) + T * I) = 1 - (starRingEnd ℂ) (((1 - x : ℝ) : ℂ) + T * I) := by
    apply Complex.ext <;> simp
  rw [h1, logDeriv_xi_reciprocity, logDeriv_xi_conj_xiLogDerivSymmetry]

theorem xi_reflect_horizontal (x T : ℝ) :
    xi ((x : ℂ) + T * I) = (starRingEnd ℂ) (xi (((1 - x : ℝ) : ℂ) + T * I)) := by
  have h1 : ((x : ℂ) + T * I) = 1 - (starRingEnd ℂ) (((1 - x : ℝ) : ℂ) + T * I) := by
    apply Complex.ext <;> simp
  rw [h1, xi_one_sub, xi_conj]

/-- Left half of a good horizontal line: `−ξ'/ξ` is in the closed right half-plane and the slit
plane. -/
theorem halfPlaneGood_neg_logDeriv_xi_left {T x : ℝ} (hg : XiGoodHeight T) (hx : x ≤ 1 / 2) :
    xi ((x : ℂ) + T * I) ≠ 0 ∧ HalfPlaneGood (fun w => -logDeriv xi w) ((x : ℂ) + T * I) := by
  obtain ⟨hxi, hA, hs, hre⟩ := halfPlaneGood_logDeriv_xi_right (x := 1 - x) hg (by linarith)
  have hxi' : xi ((x : ℂ) + T * I) ≠ 0 := by
    rw [xi_reflect_horizontal]; exact (map_ne_zero _).mpr hxi
  have hval : -logDeriv xi ((x : ℂ) + T * I) =
      (starRingEnd ℂ) (logDeriv xi (((1 - x : ℝ) : ℂ) + T * I)) := by
    rw [logDeriv_xi_reflect_horizontal, neg_neg]
  refine ⟨hxi', (analyticAt_logDeriv_xi hxi').neg, ?_, ?_⟩
  · show -logDeriv xi ((x : ℂ) + T * I) ∈ slitPlane
    rw [hval]
    rcases Complex.mem_slitPlane_iff.mp hs with h | h
    · exact Complex.mem_slitPlane_iff.mpr (Or.inl (by rwa [Complex.conj_re]))
    · exact Complex.mem_slitPlane_iff.mpr (Or.inr (by rw [Complex.conj_im]; exact neg_ne_zero.mpr h))
  · show 0 ≤ (-logDeriv xi ((x : ℂ) + T * I)).re
    rw [hval, Complex.conj_re]; exact hre

/-- **`ξ'` versus `ξ`.** For good heights `T₁ < T₂`, the zero counts of `ξ'` and `ξ` in
`[−1, 2] × [T₁, T₂]` differ by at most `3`. -/
theorem exists_abs_count_deriv_xi_sub_xi_le {T₁ T₂ : ℝ} (hT : T₁ < T₂) (hg₁ : XiGoodHeight T₁)
    (hg₂ : XiGoodHeight T₂) :
    ∃ Z₁ Z₀ : Finset ℂ,
      (∀ z : ℂ, z ∈ Z₁ ↔ z ∈ (uIcc (-1 : ℝ) 2 ×ℂ uIcc T₁ T₂) ∧ deriv xi z = 0) ∧
      (∀ z : ℂ, z ∈ Z₀ ↔ z ∈ (uIcc (-1 : ℝ) 2 ×ℂ uIcc T₁ T₂) ∧ xi z = 0) ∧
      |(∑ w ∈ Z₁, ((analyticOrderAt (deriv xi) w).toNat : ℝ)) -
        ∑ w ∈ Z₀, ((analyticOrderAt xi w).toNat : ℝ)| ≤ 3 := by
  -- the vertical edges
  have hright : ∀ t : ℝ, xi (((2 : ℝ) : ℂ) + t * I) ≠ 0 ∧
      HalfPlaneGood (logDeriv xi) (((2 : ℝ) : ℂ) + t * I) := by
    intro t
    have h1 : (1 : ℝ) ≤ (((2 : ℝ) : ℂ) + t * I).re := by norm_num
    have hxi := xi_ne_zero_of_one_le_re h1
    have hpos := re_logDeriv_xi_pos_of_one_le_re h1
    exact ⟨hxi, analyticAt_logDeriv_xi hxi, Complex.mem_slitPlane_iff.mpr (Or.inl hpos),
      hpos.le⟩
  have hleft : ∀ t : ℝ, xi (((-1 : ℝ) : ℂ) + t * I) ≠ 0 ∧
      HalfPlaneGood (fun w => -logDeriv xi w) (((-1 : ℝ) : ℂ) + t * I) := by
    intro t
    have hsym : ((-1 : ℝ) : ℂ) + t * I = 1 - (((2 : ℝ) : ℂ) + (-t : ℝ) * I) := by
      push_cast; ring
    obtain ⟨hxi, hA, hs, hre⟩ := hright (-t)
    have hxi' : xi (((-1 : ℝ) : ℂ) + t * I) ≠ 0 := by rw [hsym, xi_one_sub]; exact hxi
    have hval : -logDeriv xi (((-1 : ℝ) : ℂ) + t * I) =
        logDeriv xi (((2 : ℝ) : ℂ) + (-t : ℝ) * I) := by
      rw [hsym, logDeriv_xi_reciprocity, neg_neg]
    refine ⟨hxi', (analyticAt_logDeriv_xi hxi').neg, ?_, ?_⟩
    · show -logDeriv xi (((-1 : ℝ) : ℂ) + t * I) ∈ slitPlane
      rw [hval]; exact hs
    · show 0 ≤ (-logDeriv xi (((-1 : ℝ) : ℂ) + t * I)).re
      rw [hval]; exact hre
  have hrel : ∀ z : ℂ, xi z ≠ 0 → logDeriv xi z ≠ 0 →
      RatioRelation (deriv xi) xi (logDeriv xi) z := fun z hz hL =>
    ratioRelation_xi hz (deriv_xi_ne_zero_of_logDeriv_ne_zero hL)
  have hLne : ∀ {g : ℂ → ℂ} {z : ℂ}, HalfPlaneGood g z → g z ≠ 0 := fun h =>
    slitPlane_ne_zero h.2.1
  have hLneN : ∀ {z : ℂ}, HalfPlaneGood (fun w => -logDeriv xi w) z → logDeriv xi z ≠ 0 :=
    fun h h0 => slitPlane_ne_zero h.2.1 (by simp [h0])
  -- the horizontal edges at a good height
  have hhor : ∀ T : ℝ, XiGoodHeight T → ∀ x ∈ uIcc (-1 : ℝ) 2,
      RatioRelation (deriv xi) xi (logDeriv xi) ((x : ℂ) + T * I) := by
    intro T hg x _
    rcases le_total x (1 / 2) with h | h
    · obtain ⟨hxi, hG⟩ := halfPlaneGood_neg_logDeriv_xi_left hg h
      exact hrel _ hxi (hLneN hG)
    · obtain ⟨hxi, hG⟩ := halfPlaneGood_logDeriv_xi_right hg h
      exact hrel _ hxi (hLne hG)
  have h12 : (1 / 2 : ℝ) < 2 := by norm_num
  have hm1 : (-1 : ℝ) < 1 / 2 := by norm_num
  have hmemL : ∀ x ∈ uIcc (-1 : ℝ) (1 / 2), x ≤ 1 / 2 := fun x hx => by
    rw [uIcc_of_le hm1.le] at hx; exact hx.2
  have hmemR : ∀ x ∈ uIcc (1 / 2 : ℝ) 2, 1 / 2 ≤ x := fun x hx => by
    rw [uIcc_of_le h12.le] at hx; exact hx.1
  exact abs_sum_analyticOrderAt_sub_le_three xi_analyticOnNhd_univ.deriv xi_analyticOnNhd_univ
    ⟨(2 : ℂ), by
      have h1 : (1 : ℝ) ≤ (2 : ℂ).re := by norm_num
      exact deriv_xi_ne_zero_of_logDeriv_ne_zero fun h0 => by
        have := re_logDeriv_xi_pos_of_one_le_re h1
        rw [h0, Complex.zero_re] at this; exact lt_irrefl 0 this⟩
    ⟨0, by simpa using xi_ne_zero_of_real 0⟩ hm1 h12 hT
    (hhor T₁ hg₁) (hhor T₂ hg₂)
    (fun t _ => hrel _ (hright t).1 (hLne (hright t).2))
    (fun t _ => hrel _ (hleft t).1 (hLneN (hleft t).2))
    (fun t _ => (hleft t).2) (fun t _ => (hright t).2)
    (fun x hx => (halfPlaneGood_neg_logDeriv_xi_left hg₁ (hmemL x hx)).2)
    (fun x hx => (halfPlaneGood_logDeriv_xi_right hg₁ (hmemR x hx)).2)
    (fun x hx => (halfPlaneGood_neg_logDeriv_xi_left hg₂ (hmemL x hx)).2)
    (fun x hx => (halfPlaneGood_logDeriv_xi_right hg₂ (hmemR x hx)).2)

/-- **Rolle points between consecutive elements.** If every pair of consecutive elements of a
finite set of reals encloses a point with property `P`, then at least `card S − 1` such points
exist, each strictly between two elements of `S`. -/
theorem exists_finset_between_card {S : Finset ℝ} {P : ℝ → Prop}
    (hgap : ∀ a ∈ S, ∀ b ∈ S, a < b → (∀ x ∈ S, x ≤ a ∨ b ≤ x) → ∃ c, a < c ∧ c < b ∧ P c) :
    ∃ C : Finset ℝ, (∀ c ∈ C, P c ∧ ∃ a ∈ S, ∃ b ∈ S, a < c ∧ c < b) ∧ S.card ≤ C.card + 1 := by
  classical
  induction S using Finset.induction_on_max with
  | empty => exact ⟨∅, by simp, by simp⟩
  | insert a S hlt ih =>
    have hgap' : ∀ a' ∈ S, ∀ b' ∈ S, a' < b' → (∀ x ∈ S, x ≤ a' ∨ b' ≤ x) →
        ∃ c, a' < c ∧ c < b' ∧ P c := by
      intro a' ha' b' hb' hab hcons
      refine hgap a' (Finset.mem_insert_of_mem ha') b' (Finset.mem_insert_of_mem hb') hab ?_
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Or.inr (hlt b' hb').le
      · exact hcons x hx
    obtain ⟨C, hC, hcard⟩ := ih hgap'
    have haS : a ∉ S := fun h => lt_irrefl a (hlt a h)
    rcases S.eq_empty_or_nonempty with hS | hS
    · subst hS
      exact ⟨∅, by simp, by simp⟩
    · set b := S.max' hS with hb
      have hbS : b ∈ S := S.max'_mem hS
      have hba : b < a := hlt b hbS
      obtain ⟨c, hbc, hca, hPc⟩ := hgap b (Finset.mem_insert_of_mem hbS) a
        (Finset.mem_insert_self a S) hba (by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact Or.inr le_rfl
          · exact Or.inl (S.le_max' x hx))
      have hcC : c ∉ C := by
        intro hc
        obtain ⟨-, a', ha', b', hb', -, hcb'⟩ := hC c hc
        have := S.le_max' b' hb'
        linarith
      refine ⟨insert c C, ?_, ?_⟩
      · intro x hx
        rcases Finset.mem_insert.mp hx with rfl | hx
        · exact ⟨hPc, b, Finset.mem_insert_of_mem hbS, a, Finset.mem_insert_self a S, hbc, hca⟩
        · obtain ⟨hP, a', ha', b', hb', h1, h2⟩ := hC x hx
          exact ⟨hP, a', Finset.mem_insert_of_mem ha', b', Finset.mem_insert_of_mem hb', h1, h2⟩
      · rw [Finset.card_insert_of_notMem haS, Finset.card_insert_of_notMem hcC]
        omega

/-- **Rolle on the critical line.** Between two zeros `a < b` of `t ↦ ξ(1/2 + it)` there is `c`
with `ξ'(1/2 + ic) = 0`. -/
theorem exists_deriv_xi_criticalLine_eq_zero {a b : ℝ} (hab : a < b)
    (ha : xi ((1 / 2 : ℂ) + I * (a : ℂ)) = 0) (hb : xi ((1 / 2 : ℂ) + I * (b : ℂ)) = 0) :
    ∃ c ∈ Ioo a b, deriv xi ((1 / 2 : ℂ) + I * (c : ℂ)) = 0 := by
  set f : ℝ → ℝ := fun t => (xi ((1 / 2 : ℂ) + I * (t : ℂ))).re with hf
  have hpath : ∀ t : ℝ, HasDerivAt (fun u : ℝ => (1 / 2 : ℂ) + I * (u : ℂ)) I t := by
    intro t
    have := ((hasDerivAt_id t).ofReal_comp.const_mul I).const_add (1 / 2 : ℂ)
    simpa using this
  have hderiv : ∀ t : ℝ, HasDerivAt f ((I * deriv xi ((1 / 2 : ℂ) + I * (t : ℂ))).re) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => xi ((1 / 2 : ℂ) + I * (u : ℂ)))
        (I • deriv xi ((1 / 2 : ℂ) + I * (t : ℂ))) t :=
      (xi_differentiable _).hasDerivAt.scomp t (hpath t)
    have h2 : HasDerivAt f ((I • deriv xi ((1 / 2 : ℂ) + I * (t : ℂ))).re) t :=
      Complex.reCLM.hasFDerivAt.comp_hasDerivAt t h1
    simpa [smul_eq_mul] using h2
  have hcont : ContinuousOn f (Icc a b) := fun t _ => (hderiv t).continuousAt.continuousWithinAt
  obtain ⟨c, hc, hc0⟩ := exists_hasDerivAt_eq_zero hab hcont
    (by simp only [hf, ha, hb, Complex.zero_re]) (fun t _ => hderiv t)
  refine ⟨c, hc, ?_⟩
  have hre := deriv_xi_criticalLine_re c
  have him : (deriv xi ((1 / 2 : ℂ) + I * (c : ℂ))).im = 0 := by
    have : (I * deriv xi ((1 / 2 : ℂ) + I * (c : ℂ))).re =
        -(deriv xi ((1 / 2 : ℂ) + I * (c : ℂ))).im := by simp
    linarith
  exact Complex.ext hre him

/-- A zero of `ξ'` has multiplicity at least one. -/
theorem one_le_toNat_analyticOrderAt_deriv_xi {w : ℂ} (hw : deriv xi w = 0) :
    1 ≤ (analyticOrderAt (deriv xi) w).toNat := by
  have hA := analyticOnNhd_deriv_xi
  have h1 : deriv xi 1 ≠ 0 := deriv_xi_ne_zero_of_logDeriv_ne_zero fun h0 => by
    have := re_logDeriv_xi_pos_of_one_le_re (s := 1) (by norm_num)
    rw [h0, Complex.zero_re] at this; exact lt_irrefl 0 this
  have h0 : deriv xi 0 ≠ 0 := by
    have := deriv_xi_one_sub 1
    rw [sub_self] at this
    rw [this]; exact neg_ne_zero.mpr h1
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp
    (DeBruijn.analyticOrderAt_ne_top_of_ne_zero hA h0 w)
  have hn0 : n ≠ 0 := by
    rintro rfl
    exact ((hA w (mem_univ _)).analyticOrderAt_eq_zero.mp (by rw [← hn]; rfl)) hw
  rw [← hn, ENat.toNat_coe]
  omega

/-- **Extra critical points are paid for by off-line zeros.** For good heights `T₁ < T₂`, in
`[−1, 2] × [T₁, T₂]`, write `A` for the number of distinct on-line zeros of `ξ` and
`E = (#on-line zeros of ξ', with multiplicity) − (A − 1) ≥ 0` for the critical points of `Ξ` beyond
Rolle's minimum. Then
`E + #off-line zeros of ξ' ≤ #off-line zeros of ξ + (on-line multiplicity excess of ξ) + 4`, and
conversely `E + #off-line zeros of ξ' ≥ #off-line zeros of ξ + (on-line multiplicity excess) − 2`. -/
theorem extraCritical_add_offLine_count_deriv_xi_le {T₁ T₂ : ℝ} (hT : T₁ < T₂) (hg₁ : XiGoodHeight T₁)
    (hg₂ : XiGoodHeight T₂) :
    ∃ Z₁ Z₀ : Finset ℂ,
      (∀ z : ℂ, z ∈ Z₁ ↔ z ∈ (uIcc (-1 : ℝ) 2 ×ℂ uIcc T₁ T₂) ∧ deriv xi z = 0) ∧
      (∀ z : ℂ, z ∈ Z₀ ↔ z ∈ (uIcc (-1 : ℝ) 2 ×ℂ uIcc T₁ T₂) ∧ xi z = 0) ∧
      0 ≤ (∑ w ∈ Z₁.filter (fun w => w.re = 1 / 2), ((analyticOrderAt (deriv xi) w).toNat : ℝ)) -
        (((Z₀.filter (fun w => w.re = 1 / 2)).card : ℝ) - 1) ∧
      ((∑ w ∈ Z₁.filter (fun w => w.re = 1 / 2), ((analyticOrderAt (deriv xi) w).toNat : ℝ)) -
        (((Z₀.filter (fun w => w.re = 1 / 2)).card : ℝ) - 1)) +
      (∑ w ∈ Z₁.filter (fun w => w.re ≠ 1 / 2), ((analyticOrderAt (deriv xi) w).toNat : ℝ)) ≤
        (∑ w ∈ Z₀.filter (fun w => w.re ≠ 1 / 2), ((analyticOrderAt xi w).toNat : ℝ)) +
          ((∑ w ∈ Z₀.filter (fun w => w.re = 1 / 2), ((analyticOrderAt xi w).toNat : ℝ)) -
            ((Z₀.filter (fun w => w.re = 1 / 2)).card : ℝ)) + 4 ∧
      (∑ w ∈ Z₀.filter (fun w => w.re ≠ 1 / 2), ((analyticOrderAt xi w).toNat : ℝ)) +
          ((∑ w ∈ Z₀.filter (fun w => w.re = 1 / 2), ((analyticOrderAt xi w).toNat : ℝ)) -
            ((Z₀.filter (fun w => w.re = 1 / 2)).card : ℝ)) - 2 ≤
      ((∑ w ∈ Z₁.filter (fun w => w.re = 1 / 2), ((analyticOrderAt (deriv xi) w).toNat : ℝ)) -
        (((Z₀.filter (fun w => w.re = 1 / 2)).card : ℝ) - 1)) +
      (∑ w ∈ Z₁.filter (fun w => w.re ≠ 1 / 2), ((analyticOrderAt (deriv xi) w).toNat : ℝ)) := by
  classical
  obtain ⟨Z₁, Z₀, hZ₁, hZ₀, habs⟩ := exists_abs_count_deriv_xi_sub_xi_le hT hg₁ hg₂
  refine ⟨Z₁, Z₀, hZ₁, hZ₀, ?_⟩
  set A₀ := Z₀.filter (fun w => w.re = 1 / 2) with hA₀
  set S : Finset ℝ := A₀.image Complex.im with hS
  have hcardS : S.card = A₀.card := by
    rw [hS]
    refine Finset.card_image_of_injOn fun u hu v hv huv => ?_
    have hu' := (Finset.mem_filter.mp (Finset.mem_coe.mp hu)).2
    have hv' := (Finset.mem_filter.mp (Finset.mem_coe.mp hv)).2
    exact Complex.ext (by rw [hu', hv']) huv
  -- points of `S` are ordinates of on-line zeros inside `[T₁, T₂]`
  have hSmem : ∀ a ∈ S, xi ((1 / 2 : ℂ) + I * (a : ℂ)) = 0 ∧ T₁ ≤ a ∧ a ≤ T₂ := by
    intro a ha
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨hwZ, hwre⟩ := Finset.mem_filter.mp hw
    obtain ⟨hwR, hw0⟩ := (hZ₀ w).mp hwZ
    rw [Complex.mem_reProdIm, uIcc_of_le hT.le] at hwR
    have hweq : (1 / 2 : ℂ) + I * (w.im : ℂ) = w := by
      apply Complex.ext <;> simp [hwre]
    exact ⟨by rw [hweq]; exact hw0, hwR.2.1, hwR.2.2⟩
  -- every on-line zero with ordinate in `[T₁, T₂]` is in `S`
  have hSall : ∀ c : ℝ, T₁ ≤ c → c ≤ T₂ → xi ((1 / 2 : ℂ) + I * (c : ℂ)) = 0 → c ∈ S := by
    intro c h1 h2 h0
    refine Finset.mem_image.mpr ⟨(1 / 2 : ℂ) + I * (c : ℂ), Finset.mem_filter.mpr
      ⟨(hZ₀ _).mpr ⟨?_, h0⟩, by simp⟩, by simp⟩
    rw [Complex.mem_reProdIm, uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2), uIcc_of_le hT.le]
    exact ⟨⟨by simp; norm_num, by simp; norm_num⟩, ⟨by simpa using h1, by simpa using h2⟩⟩
  obtain ⟨C, hC, hcardC⟩ := exists_finset_between_card (S := S)
    (P := fun c => deriv xi ((1 / 2 : ℂ) + I * (c : ℂ)) = 0) fun a ha b hb hab _ => by
      obtain ⟨c, hc, hc0⟩ := exists_deriv_xi_criticalLine_eq_zero hab (hSmem a ha).1 (hSmem b hb).1
      exact ⟨c, hc.1, hc.2, hc0⟩
  -- the Rolle points are on-line zeros of `ξ'` in the window
  set B₁ := Z₁.filter (fun w => w.re = 1 / 2) with hB₁
  have hCB : C.card ≤ B₁.card := by
    refine Finset.card_le_card_of_injOn (fun c => (1 / 2 : ℂ) + I * (c : ℂ)) ?_ ?_
    · intro c hc
      obtain ⟨hP, a, ha, b, hb, hac, hcb⟩ := hC c (Finset.mem_coe.mp hc)
      refine Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨(hZ₁ _).mpr ⟨?_, hP⟩, by simp⟩)
      rw [Complex.mem_reProdIm, uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 2), uIcc_of_le hT.le]
      have h1 := (hSmem a ha).2.1
      have h2 := (hSmem b hb).2.2
      exact ⟨⟨by simp; norm_num, by simp; norm_num⟩, ⟨by simp; linarith, by simp; linarith⟩⟩
    · intro u _ v _ huv
      have := congrArg Complex.im huv
      simpa using this
  -- multiplicities
  have hord₁ : ∀ w ∈ B₁, (1 : ℝ) ≤ ((analyticOrderAt (deriv xi) w).toNat : ℝ) := by
    intro w hw
    obtain ⟨-, hw0⟩ := (hZ₁ w).mp (Finset.mem_filter.mp hw).1
    exact_mod_cast one_le_toNat_analyticOrderAt_deriv_xi hw0
  have hB₁sum : (B₁.card : ℝ) ≤ ∑ w ∈ B₁, ((analyticOrderAt (deriv xi) w).toNat : ℝ) := by
    have := Finset.sum_le_sum hord₁
    simpa using this
  have hsplit₁ := Finset.sum_filter_add_sum_filter_not Z₁ (fun w => w.re = 1 / 2)
    (fun w => ((analyticOrderAt (deriv xi) w).toNat : ℝ))
  have hsplit₀ := Finset.sum_filter_add_sum_filter_not Z₀ (fun w => w.re = 1 / 2)
    (fun w => ((analyticOrderAt xi w).toNat : ℝ))
  have hle := (abs_le.mp habs).2
  have hge := (abs_le.mp habs).1
  have hcards : (A₀.card : ℝ) ≤ (B₁.card : ℝ) + 1 := by
    have : A₀.card ≤ B₁.card + 1 := by rw [← hcardS]; omega
    exact_mod_cast this
  simp only [ne_eq] at hsplit₁ hsplit₀ ⊢
  refine ⟨by linarith, by linarith, by linarith⟩

/-- **Differentiation creates no off-line zeros (up to 4).** For good heights `T₁ < T₂`, in
`[−1, 2] × [T₁, T₂]`:
`#off-line zeros of ξ' ≤ #off-line zeros of ξ + (on-line multiplicity excess of ξ) + 4`,
all with multiplicity. -/
theorem offLine_count_deriv_xi_le {T₁ T₂ : ℝ} (hT : T₁ < T₂) (hg₁ : XiGoodHeight T₁)
    (hg₂ : XiGoodHeight T₂) :
    ∃ Z₁ Z₀ : Finset ℂ,
      (∀ z : ℂ, z ∈ Z₁ ↔ z ∈ (uIcc (-1 : ℝ) 2 ×ℂ uIcc T₁ T₂) ∧ deriv xi z = 0) ∧
      (∀ z : ℂ, z ∈ Z₀ ↔ z ∈ (uIcc (-1 : ℝ) 2 ×ℂ uIcc T₁ T₂) ∧ xi z = 0) ∧
      (∑ w ∈ Z₁.filter (fun w => w.re ≠ 1 / 2), ((analyticOrderAt (deriv xi) w).toNat : ℝ)) ≤
        (∑ w ∈ Z₀.filter (fun w => w.re ≠ 1 / 2), ((analyticOrderAt xi w).toNat : ℝ)) +
          ((∑ w ∈ Z₀.filter (fun w => w.re = 1 / 2), ((analyticOrderAt xi w).toNat : ℝ)) -
            ((Z₀.filter (fun w => w.re = 1 / 2)).card : ℝ)) + 4 := by
  obtain ⟨Z₁, Z₀, hZ₁, hZ₀, hE, h, -⟩ := extraCritical_add_offLine_count_deriv_xi_le hT hg₁ hg₂
  exact ⟨Z₁, Z₀, hZ₁, hZ₀, by linarith⟩

end

end RHTower
