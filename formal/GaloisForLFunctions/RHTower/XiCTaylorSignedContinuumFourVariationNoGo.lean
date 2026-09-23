import GaloisForLFunctions.RHTower.XiCTaylorSignedContinuumSignComplexityNoGo
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Four-row Route-J continuum sources require four phase-weighted sign changes

All four reflected value/derivative rows reduce, after positive exponential reweighting, to the
extended Chebyshev system
`{exp (2 c t), t exp (2 c t), 1, t}`.  A twice-Rolle argument proves four-root rigidity.
Rank-nullity then constructs an exact three-root exponential-Hermite test function; root
simplicity forces global alternation across its prescribed roots.  Pairing this test function
against an atomless physical source excludes every phase-weighted density with at most three
sign changes.

Unlike the radial analytic core, the final theorem retains the physical Fourier carrier
`sin (u t)`.  Its conclusion concerns `sin (u t) h(t)`, and a source-supported-away-from-nodes
hypothesis transfers almost-everywhere vanishing back to `h`.
-/

open Real Set MeasureTheory Filter Topology

namespace RHTower

noncomputable section

def routeJExpHermiteCombination
    (lam A B C D t : ℝ) : ℝ :=
  (A + B * t) * Real.exp (lam * t) + C + D * t

def routeJExpHermiteCombinationDeriv
    (lam A B D t : ℝ) : ℝ :=
  (B + lam * (A + B * t)) * Real.exp (lam * t) + D

def routeJExpHermiteCombinationSecondDeriv
    (lam A B t : ℝ) : ℝ :=
  Real.exp (lam * t) * (2 * lam * B + lam ^ (2 : ℕ) * (A + B * t))

theorem hasDerivAt_routeJExpHermiteCombination
    (lam A B C D t : ℝ) :
    HasDerivAt (routeJExpHermiteCombination lam A B C D)
      (routeJExpHermiteCombinationDeriv lam A B D t) t := by
  unfold routeJExpHermiteCombination routeJExpHermiteCombinationDeriv
  have hlin : HasDerivAt (fun x : ℝ => A + B * x) B t := by
    exact (hasDerivAt_const_mul (x := t) B).const_add A
  have harg : HasDerivAt (fun x : ℝ => lam * x) lam t := by
    exact hasDerivAt_const_mul lam
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (lam * x))
      (lam * Real.exp (lam * t)) t := by
    convert harg.exp using 1 <;> ring
  have htail : HasDerivAt (fun x : ℝ => C + D * x) D t := by
    exact (hasDerivAt_const_mul (x := t) D).const_add C
  convert! (hlin.mul hexp).add htail using 1
  · funext x
    simp only [Pi.add_apply, Pi.mul_apply]
    ring
  · ring

theorem hasDerivAt_routeJExpHermiteCombinationDeriv
    (lam A B D t : ℝ) :
    HasDerivAt (routeJExpHermiteCombinationDeriv lam A B D)
      (routeJExpHermiteCombinationSecondDeriv lam A B t) t := by
  unfold routeJExpHermiteCombinationDeriv
    routeJExpHermiteCombinationSecondDeriv
  have hlin :
      HasDerivAt (fun x : ℝ => B + lam * (A + B * x))
        (lam * B) t := by
    have hinner : HasDerivAt (fun x : ℝ => A + B * x) B t := by
      exact (hasDerivAt_const_mul (x := t) B).const_add A
    convert! (hinner.const_mul lam).const_add B using 1 <;>
      ring
  have harg : HasDerivAt (fun x : ℝ => lam * x) lam t := by
    exact hasDerivAt_const_mul lam
  have hexp : HasDerivAt (fun x : ℝ => Real.exp (lam * x))
      (lam * Real.exp (lam * t)) t := by
    convert harg.exp using 1 <;> ring
  convert! (hlin.mul hexp).add_const D using 1 <;>
    first | rfl | ring

theorem routeJExpHermiteCombination_four_roots_rigid
    {lam A B C D a b d e : ℝ}
    (hlam : lam ≠ 0)
    (hab : a < b) (hbd : b < d) (hde : d < e)
    (ha : routeJExpHermiteCombination lam A B C D a = 0)
    (hb : routeJExpHermiteCombination lam A B C D b = 0)
    (hd : routeJExpHermiteCombination lam A B C D d = 0)
    (he : routeJExpHermiteCombination lam A B C D e = 0) :
    A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0 := by
  let F := routeJExpHermiteCombination lam A B C D
  let F1 := routeJExpHermiteCombinationDeriv lam A B D
  let F2 := routeJExpHermiteCombinationSecondDeriv lam A B
  have hFcont : Continuous F := by
    change Continuous (fun t : ℝ =>
      (A + B * t) * Real.exp (lam * t) + C + D * t)
    fun_prop
  have hF1cont : Continuous F1 := by
    change Continuous (fun t : ℝ =>
      (B + lam * (A + B * t)) * Real.exp (lam * t) + D)
    fun_prop
  obtain ⟨x₁, hx₁mem, hx₁⟩ :=
    exists_hasDerivAt_eq_zero hab hFcont.continuousOn
      (by dsimp [F]; rw [ha, hb])
      (fun x _ => hasDerivAt_routeJExpHermiteCombination lam A B C D x)
  obtain ⟨x₂, hx₂mem, hx₂⟩ :=
    exists_hasDerivAt_eq_zero hbd hFcont.continuousOn
      (by dsimp [F]; rw [hb, hd])
      (fun x _ => hasDerivAt_routeJExpHermiteCombination lam A B C D x)
  obtain ⟨x₃, hx₃mem, hx₃⟩ :=
    exists_hasDerivAt_eq_zero hde hFcont.continuousOn
      (by dsimp [F]; rw [hd, he])
      (fun x _ => hasDerivAt_routeJExpHermiteCombination lam A B C D x)
  have hx₁x₂ : x₁ < x₂ := hx₁mem.2.trans hx₂mem.1
  have hx₂x₃ : x₂ < x₃ := hx₂mem.2.trans hx₃mem.1
  obtain ⟨y₁, hy₁mem, hy₁⟩ :=
    exists_hasDerivAt_eq_zero hx₁x₂ hF1cont.continuousOn
      (by dsimp [F1] at hx₁ hx₂ ⊢; rw [hx₁, hx₂])
      (fun x _ => hasDerivAt_routeJExpHermiteCombinationDeriv lam A B D x)
  obtain ⟨y₂, hy₂mem, hy₂⟩ :=
    exists_hasDerivAt_eq_zero hx₂x₃ hF1cont.continuousOn
      (by dsimp [F1] at hx₂ hx₃ ⊢; rw [hx₂, hx₃])
      (fun x _ => hasDerivAt_routeJExpHermiteCombinationDeriv lam A B D x)
  have hy₁y₂ : y₁ < y₂ := hy₁mem.2.trans hy₂mem.1
  have hy₁aff :
      2 * lam * B + lam ^ (2 : ℕ) * (A + B * y₁) = 0 := by
    dsimp [F2, routeJExpHermiteCombinationSecondDeriv] at hy₁
    exact (mul_eq_zero.mp hy₁).resolve_left (Real.exp_ne_zero _)
  have hy₂aff :
      2 * lam * B + lam ^ (2 : ℕ) * (A + B * y₂) = 0 := by
    dsimp [F2, routeJExpHermiteCombinationSecondDeriv] at hy₂
    exact (mul_eq_zero.mp hy₂).resolve_left (Real.exp_ne_zero _)
  have hB : B = 0 := by
    have hdiff :
        (lam ^ (2 : ℕ) * B) * (y₁ - y₂) = 0 := by
      calc
        (lam ^ (2 : ℕ) * B) * (y₁ - y₂) =
            (2 * lam * B + lam ^ (2 : ℕ) * (A + B * y₁)) -
              (2 * lam * B + lam ^ (2 : ℕ) * (A + B * y₂)) := by ring
        _ = 0 := by rw [hy₁aff, hy₂aff]; ring
    have hyne : y₁ - y₂ ≠ 0 := sub_ne_zero.mpr hy₁y₂.ne
    have hlamSq : lam ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hlam
    have hleft : lam ^ (2 : ℕ) * B = 0 :=
      (mul_eq_zero.mp hdiff).resolve_right hyne
    exact (mul_eq_zero.mp hleft).resolve_left hlamSq
  have hA : A = 0 := by
    have hlamSq : lam ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hlam
    have hAeq : lam ^ (2 : ℕ) * A = 0 := by
      simpa [hB] using hy₁aff
    exact (mul_eq_zero.mp hAeq).resolve_left hlamSq
  have hD : D = 0 := by
    dsimp [routeJExpHermiteCombination] at ha hb
    rw [hA, hB] at ha hb
    norm_num at ha hb
    nlinarith
  have hC : C = 0 := by
    dsimp [routeJExpHermiteCombination] at ha
    rw [hA, hB, hD] at ha
    simpa using ha
  exact ⟨hA, hB, hC, hD⟩

def routeJExpHermiteThreePointEvaluation
    (lam a b d : ℝ) : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) where
  toFun x i :=
    routeJExpHermiteCombination lam (x 0) (x 1) (x 2) (x 3)
      (![a, b, d] i)
  map_add' x y := by
    funext i
    fin_cases i <;>
      simp [routeJExpHermiteCombination] <;> ring
  map_smul' r x := by
    funext i
    fin_cases i <;>
      simp [routeJExpHermiteCombination] <;> ring

theorem exists_nonzero_routeJExpHermiteCombination_three_roots
    (lam a b d : ℝ) :
    ∃ A B C D : ℝ,
      (A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0 ∨ D ≠ 0) ∧
      routeJExpHermiteCombination lam A B C D a = 0 ∧
      routeJExpHermiteCombination lam A B C D b = 0 ∧
      routeJExpHermiteCombination lam A B C D d = 0 := by
  let E := routeJExpHermiteThreePointEvaluation lam a b d
  have hker : LinearMap.ker E ≠ ⊥ := by
    apply LinearMap.ker_ne_bot_of_finrank_lt
    simp
  obtain ⟨x, hxmem, hxne⟩ := (LinearMap.ker E).ne_bot_iff.mp hker
  have hxeval : E x = 0 := hxmem
  refine ⟨x 0, x 1, x 2, x 3, ?_, ?_, ?_, ?_⟩
  · by_contra h
    simp only [not_or, not_ne_iff] at h
    rcases h with ⟨h0, h1, h2, h3⟩
    apply hxne
    funext i
    fin_cases i <;> simp [h0, h1, h2, h3]
  · have h := congrFun hxeval 0
    simpa [E, routeJExpHermiteThreePointEvaluation] using h
  · have h := congrFun hxeval 1
    simpa [E, routeJExpHermiteThreePointEvaluation] using h
  · have h := congrFun hxeval 2
    simpa [E, routeJExpHermiteThreePointEvaluation] using h

theorem routeJExpHermiteCombination_coeff_zero_of_second_two_roots
    {lam A B x y : ℝ}
    (hlam : lam ≠ 0) (hxy : x ≠ y)
    (hx : routeJExpHermiteCombinationSecondDeriv lam A B x = 0)
    (hy : routeJExpHermiteCombinationSecondDeriv lam A B y = 0) :
    A = 0 ∧ B = 0 := by
  have hxaff :
      2 * lam * B + lam ^ (2 : ℕ) * (A + B * x) = 0 := by
    unfold routeJExpHermiteCombinationSecondDeriv at hx
    exact (mul_eq_zero.mp hx).resolve_left (Real.exp_ne_zero _)
  have hyaff :
      2 * lam * B + lam ^ (2 : ℕ) * (A + B * y) = 0 := by
    unfold routeJExpHermiteCombinationSecondDeriv at hy
    exact (mul_eq_zero.mp hy).resolve_left (Real.exp_ne_zero _)
  have hlamSq : lam ^ (2 : ℕ) ≠ 0 := pow_ne_zero 2 hlam
  have hdiff : (lam ^ (2 : ℕ) * B) * (x - y) = 0 := by
    calc
      (lam ^ (2 : ℕ) * B) * (x - y) =
          (2 * lam * B + lam ^ (2 : ℕ) * (A + B * x)) -
            (2 * lam * B + lam ^ (2 : ℕ) * (A + B * y)) := by ring
      _ = 0 := by rw [hxaff, hyaff]; ring
  have hB : B = 0 := by
    have hxy' : x - y ≠ 0 := sub_ne_zero.mpr hxy
    have hleft : lam ^ (2 : ℕ) * B = 0 :=
      (mul_eq_zero.mp hdiff).resolve_right hxy'
    exact (mul_eq_zero.mp hleft).resolve_left hlamSq
  have hAeq : lam ^ (2 : ℕ) * A = 0 := by
    simpa [hB] using hxaff
  exact ⟨(mul_eq_zero.mp hAeq).resolve_left hlamSq, hB⟩

theorem routeJExpHermiteCombination_coeff_zero_of_AB_zero_two_roots
    {lam A B C D x y : ℝ}
    (hxy : x ≠ y) (hA : A = 0) (hB : B = 0)
    (hx : routeJExpHermiteCombination lam A B C D x = 0)
    (hy : routeJExpHermiteCombination lam A B C D y = 0) :
    C = 0 ∧ D = 0 := by
  unfold routeJExpHermiteCombination at hx hy
  rw [hA, hB] at hx hy
  norm_num at hx hy
  have hD : D = 0 := by
    by_contra hD
    have : x = y := by
      apply mul_left_cancel₀ hD
      nlinarith
    exact hxy this
  have hC : C = 0 := by simpa [hD] using hx
  exact ⟨hC, hD⟩

theorem routeJExpHermiteCombination_three_roots_deriv_ne_zero
    {lam A B C D a b d : ℝ}
    (hlam : lam ≠ 0) (hab : a < b) (hbd : b < d)
    (hnonzero : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0 ∨ D ≠ 0)
    (ha : routeJExpHermiteCombination lam A B C D a = 0)
    (hb : routeJExpHermiteCombination lam A B C D b = 0)
    (hd : routeJExpHermiteCombination lam A B C D d = 0) :
    routeJExpHermiteCombinationDeriv lam A B D a ≠ 0 ∧
      routeJExpHermiteCombinationDeriv lam A B D b ≠ 0 ∧
      routeJExpHermiteCombinationDeriv lam A B D d ≠ 0 := by
  let F := routeJExpHermiteCombination lam A B C D
  let F1 := routeJExpHermiteCombinationDeriv lam A B D
  have hFcont : Continuous F := by
    change Continuous (fun t : ℝ =>
      (A + B * t) * Real.exp (lam * t) + C + D * t)
    fun_prop
  have hF1cont : Continuous F1 := by
    change Continuous (fun t : ℝ =>
      (B + lam * (A + B * t)) * Real.exp (lam * t) + D)
    fun_prop
  obtain ⟨x₁, hx₁mem, hx₁⟩ :=
    exists_hasDerivAt_eq_zero hab hFcont.continuousOn
      (by dsimp [F]; rw [ha, hb])
      (fun x _ => hasDerivAt_routeJExpHermiteCombination lam A B C D x)
  obtain ⟨x₂, hx₂mem, hx₂⟩ :=
    exists_hasDerivAt_eq_zero hbd hFcont.continuousOn
      (by dsimp [F]; rw [hb, hd])
      (fun x _ => hasDerivAt_routeJExpHermiteCombination lam A B C D x)
  have hx₁x₂ : x₁ < x₂ := hx₁mem.2.trans hx₂mem.1
  have kill
      {p q : ℝ} (hpq : p < q)
      (hp : routeJExpHermiteCombinationDeriv lam A B D p = 0)
      (hq : routeJExpHermiteCombinationDeriv lam A B D q = 0)
      {r s : ℝ} (hqr : q ≤ r) (hrs : r < s)
      (hr : routeJExpHermiteCombinationDeriv lam A B D r = 0)
      (hs : routeJExpHermiteCombinationDeriv lam A B D s = 0) :
      False := by
    obtain ⟨y₁, hy₁mem, hy₁⟩ :=
      exists_hasDerivAt_eq_zero hpq hF1cont.continuousOn
        (by dsimp [F1] at hp hq ⊢; rw [hp, hq])
        (fun x _ => hasDerivAt_routeJExpHermiteCombinationDeriv lam A B D x)
    obtain ⟨y₂, hy₂mem, hy₂⟩ :=
      exists_hasDerivAt_eq_zero hrs hF1cont.continuousOn
        (by dsimp [F1] at hr hs ⊢; rw [hr, hs])
        (fun x _ => hasDerivAt_routeJExpHermiteCombinationDeriv lam A B D x)
    have hyne : y₁ ≠ y₂ := by
      intro heq
      subst y₂
      have : y₁ < y₁ :=
        (hy₁mem.2.trans_le hqr).trans hy₂mem.1
      exact this.false
    have hAB :=
      routeJExpHermiteCombination_coeff_zero_of_second_two_roots
        hlam hyne hy₁ hy₂
    have hCD :=
      routeJExpHermiteCombination_coeff_zero_of_AB_zero_two_roots
        hab.ne hAB.1 hAB.2 ha hb
    rcases hnonzero with hA | hB | hC | hD
    · exact hA hAB.1
    · exact hB hAB.2
    · exact hC hCD.1
    · exact hD hCD.2
  constructor
  · intro hda
    exact kill hx₁mem.1 hda hx₁ le_rfl hx₁x₂ hx₁ hx₂
  constructor
  · intro hdb
    exact kill hx₁mem.2 hx₁ hdb le_rfl hx₂mem.1 hdb hx₂
  · intro hdd
    exact kill hx₁x₂ hx₁ hx₂ le_rfl hx₂mem.2 hx₂ hdd

theorem routeJExpHermiteCombination_three_roots_zero_iff
    {lam A B C D a b d t : ℝ}
    (hlam : lam ≠ 0) (hab : a < b) (hbd : b < d)
    (hnonzero : A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0 ∨ D ≠ 0)
    (ha : routeJExpHermiteCombination lam A B C D a = 0)
    (hb : routeJExpHermiteCombination lam A B C D b = 0)
    (hd : routeJExpHermiteCombination lam A B C D d = 0) :
    routeJExpHermiteCombination lam A B C D t = 0 ↔
      t = a ∨ t = b ∨ t = d := by
  constructor
  · intro ht
    have reject (hz : A = 0 ∧ B = 0 ∧ C = 0 ∧ D = 0) : False := by
      rcases hnonzero with hA | hB | hC | hD
      · exact hA hz.1
      · exact hB hz.2.1
      · exact hC hz.2.2.1
      · exact hD hz.2.2.2
    rcases lt_trichotomy t a with hta | hta | hat
    · exact (reject
        (routeJExpHermiteCombination_four_roots_rigid
          hlam hta hab hbd ht ha hb hd)).elim
    · exact Or.inl hta
    · rcases lt_trichotomy t b with htb | htb | hbt
      · exact (reject
          (routeJExpHermiteCombination_four_roots_rigid
            hlam hat htb hbd ha ht hb hd)).elim
      · exact Or.inr (Or.inl htb)
      · rcases lt_trichotomy t d with htd | htd | hdt
        · exact (reject
            (routeJExpHermiteCombination_four_roots_rigid
              hlam hab hbt htd ha hb ht hd)).elim
        · exact Or.inr (Or.inr htd)
        · exact (reject
            (routeJExpHermiteCombination_four_roots_rigid
              hlam hab hbd hdt ha hb hd ht)).elim
  · rintro (rfl | rfl | rfl)
    · exact ha
    · exact hb
    · exact hd

theorem sign_eq_of_continuousOn_noZero_Icc
    {f : ℝ → ℝ} {x y : ℝ}
    (hxy : x ≤ y) (hcont : ContinuousOn f (Icc x y))
    (hnonzero : ∀ z ∈ Icc x y, f z ≠ 0) :
    SignType.sign (f x) = SignType.sign (f y) := by
  have hxne : f x ≠ 0 := hnonzero x ⟨le_rfl, hxy⟩
  have hyne : f y ≠ 0 := hnonzero y ⟨hxy, le_rfl⟩
  rcases lt_or_gt_of_ne hxne with hxneg | hxpos
  · rcases lt_or_gt_of_ne hyne with hyneg | hypos
    · rw [sign_neg hxneg, sign_neg hyneg]
    · have hmem : (0 : ℝ) ∈ Icc (f x) (f y) :=
        ⟨hxneg.le, hypos.le⟩
      obtain ⟨z, hz, hzero⟩ :=
        intermediate_value_Icc hxy hcont hmem
      exact (hnonzero z hz hzero).elim
  · rcases lt_or_gt_of_ne hyne with hyneg | hypos
    · have hmem : (0 : ℝ) ∈ Icc (f y) (f x) :=
        ⟨hyneg.le, hxpos.le⟩
      obtain ⟨z, hz, hzero⟩ :=
        intermediate_value_Icc' hxy hcont hmem
      exact (hnonzero z hz hzero).elim
    · rw [sign_pos hxpos, sign_pos hypos]

theorem routeJExpHermiteCombination_exists_sign_flip_near_simple_root
    {lam A B C D l x r : ℝ}
    (hlx : l < x) (hxr : x < r)
    (hroot : routeJExpHermiteCombination lam A B C D x = 0)
    (hderiv :
      routeJExpHermiteCombinationDeriv lam A B D x ≠ 0) :
    ∃ xl ∈ Ioo l x, ∃ xr ∈ Ioo x r,
      SignType.sign (routeJExpHermiteCombination lam A B C D xl) =
        -SignType.sign (routeJExpHermiteCombination lam A B C D xr) := by
  let F := routeJExpHermiteCombination lam A B C D
  have hderivEq :
      deriv F x = routeJExpHermiteCombinationDeriv lam A B D x :=
    (hasDerivAt_routeJExpHermiteCombination lam A B C D x).deriv
  rcases lt_or_gt_of_ne hderiv with hneg | hpos
  · have hdneg : deriv F x < 0 := by rw [hderivEq]; exact hneg
    have hev :=
      eventually_nhdsWithin_sign_eq_of_deriv_neg hdneg hroot
    have hevL :
        ∀ᶠ y in 𝓝[<] x,
          SignType.sign (F y) = SignType.sign (x - y) :=
      hev.filter_mono inf_le_left
    have hevR :
        ∀ᶠ y in 𝓝[>] x,
          SignType.sign (F y) = SignType.sign (x - y) :=
      hev.filter_mono inf_le_left
    obtain ⟨xl, hxlSign, hxlMem⟩ :=
      (hevL.and (Ioo_mem_nhdsLT hlx)).exists
    obtain ⟨xr, hxrSign, hxrMem⟩ :=
      (hevR.and (Ioo_mem_nhdsGT hxr)).exists
    refine ⟨xl, hxlMem, xr, hxrMem, ?_⟩
    rw [hxlSign, hxrSign, sign_pos (sub_pos.mpr hxlMem.2),
      sign_neg (sub_neg.mpr hxrMem.1)]
    rfl
  · have hdpos : 0 < deriv F x := by rw [hderivEq]; exact hpos
    have hev :=
      eventually_nhdsWithin_sign_eq_of_deriv_pos hdpos hroot
    have hevL :
        ∀ᶠ y in 𝓝[<] x,
          SignType.sign (F y) = SignType.sign (y - x) :=
      hev.filter_mono inf_le_left
    have hevR :
        ∀ᶠ y in 𝓝[>] x,
          SignType.sign (F y) = SignType.sign (y - x) :=
      hev.filter_mono inf_le_left
    obtain ⟨xl, hxlSign, hxlMem⟩ :=
      (hevL.and (Ioo_mem_nhdsLT hlx)).exists
    obtain ⟨xr, hxrSign, hxrMem⟩ :=
      (hevR.and (Ioo_mem_nhdsGT hxr)).exists
    refine ⟨xl, hxlMem, xr, hxrMem, ?_⟩
    rw [hxlSign, hxrSign, sign_neg (sub_neg.mpr hxlMem.2),
      sign_pos (sub_pos.mpr hxrMem.1)]

theorem exists_routeJExpHermiteCombination_three_root_sign_certificate
    {lam a b d : ℝ}
    (hlam : lam ≠ 0) (ha0 : 0 < a) (hab : a < b) (hbd : b < d) :
    ∃ A B C D : ℝ,
      (A ≠ 0 ∨ B ≠ 0 ∨ C ≠ 0 ∨ D ≠ 0) ∧
      routeJExpHermiteCombination lam A B C D a = 0 ∧
      routeJExpHermiteCombination lam A B C D b = 0 ∧
      routeJExpHermiteCombination lam A B C D d = 0 ∧
      ((∀ t, 0 < t →
          0 ≤ (t - a) * (t - b) * (t - d) *
            routeJExpHermiteCombination lam A B C D t) ∨
        (∀ t, 0 < t →
          (t - a) * (t - b) * (t - d) *
            routeJExpHermiteCombination lam A B C D t ≤ 0)) := by
  obtain ⟨A, B, C, D, hnonzero, hA, hB, hD⟩ :=
    exists_nonzero_routeJExpHermiteCombination_three_roots lam a b d
  let F := routeJExpHermiteCombination lam A B C D
  have hFcont : Continuous F := by
    change Continuous (fun t : ℝ =>
      (A + B * t) * Real.exp (lam * t) + C + D * t)
    fun_prop
  have hzero (t : ℝ) :
      F t = 0 ↔ t = a ∨ t = b ∨ t = d :=
    routeJExpHermiteCombination_three_roots_zero_iff
      hlam hab hbd hnonzero hA hB hD
  have hderiv :=
    routeJExpHermiteCombination_three_roots_deriv_ne_zero
      hlam hab hbd hnonzero hA hB hD
  have hdlt : d < d + 1 := by linarith
  obtain ⟨x₀, hx₀, x₁, hx₁, hflipA⟩ :=
    routeJExpHermiteCombination_exists_sign_flip_near_simple_root
      ha0 hab hA hderiv.1
  obtain ⟨y₁, hy₁, y₂, hy₂, hflipB⟩ :=
    routeJExpHermiteCombination_exists_sign_flip_near_simple_root
      hab hbd hB hderiv.2.1
  obtain ⟨z₂, hz₂, z₃, hz₃, hflipD⟩ :=
    routeJExpHermiteCombination_exists_sign_flip_near_simple_root
      hbd hdlt hD hderiv.2.2
  have sameAB {p q : ℝ} (hp : p ∈ Ioo a b) (hq : q ∈ Ioo a b) :
      SignType.sign (F p) = SignType.sign (F q) := by
    rcases le_total p q with hpq | hqp
    · apply sign_eq_of_continuousOn_noZero_Icc hpq hFcont.continuousOn
      intro t ht htzero
      have htroot := (hzero t).mp htzero
      have hat : a < t := hp.1.trans_le ht.1
      have htb : t < b := ht.2.trans_lt hq.2
      rcases htroot with rfl | rfl | rfl <;> linarith
    · symm
      apply sign_eq_of_continuousOn_noZero_Icc hqp hFcont.continuousOn
      intro t ht htzero
      have htroot := (hzero t).mp htzero
      have hat : a < t := hq.1.trans_le ht.1
      have htb : t < b := ht.2.trans_lt hp.2
      rcases htroot with rfl | rfl | rfl <;> linarith
  have sameBD {p q : ℝ} (hp : p ∈ Ioo b d) (hq : q ∈ Ioo b d) :
      SignType.sign (F p) = SignType.sign (F q) := by
    rcases le_total p q with hpq | hqp
    · apply sign_eq_of_continuousOn_noZero_Icc hpq hFcont.continuousOn
      intro t ht htzero
      have htroot := (hzero t).mp htzero
      have hbt : b < t := hp.1.trans_le ht.1
      have htd : t < d := ht.2.trans_lt hq.2
      rcases htroot with rfl | rfl | rfl <;> linarith
    · symm
      apply sign_eq_of_continuousOn_noZero_Icc hqp hFcont.continuousOn
      intro t ht htzero
      have htroot := (hzero t).mp htzero
      have hbt : b < t := hq.1.trans_le ht.1
      have htd : t < d := ht.2.trans_lt hp.2
      rcases htroot with rfl | rfl | rfl <;> linarith
  have same0A {p q : ℝ} (hp : p ∈ Ioo 0 a) (hq : q ∈ Ioo 0 a) :
      SignType.sign (F p) = SignType.sign (F q) := by
    rcases le_total p q with hpq | hqp
    · apply sign_eq_of_continuousOn_noZero_Icc hpq hFcont.continuousOn
      intro t ht htzero
      have htroot := (hzero t).mp htzero
      have ht0 : 0 < t := hp.1.trans_le ht.1
      have hta : t < a := ht.2.trans_lt hq.2
      rcases htroot with rfl | rfl | rfl <;> linarith
    · symm
      apply sign_eq_of_continuousOn_noZero_Icc hqp hFcont.continuousOn
      intro t ht htzero
      have htroot := (hzero t).mp htzero
      have ht0 : 0 < t := hq.1.trans_le ht.1
      have hta : t < a := ht.2.trans_lt hp.2
      rcases htroot with rfl | rfl | rfl <;> linarith
  have sameD {p q : ℝ} (hp : p ∈ Ioi d) (hq : q ∈ Ioi d) :
      SignType.sign (F p) = SignType.sign (F q) := by
    rcases le_total p q with hpq | hqp
    · apply sign_eq_of_continuousOn_noZero_Icc hpq hFcont.continuousOn
      intro t ht htzero
      have htroot := (hzero t).mp htzero
      have hdt : d < t := hp.trans_le ht.1
      rcases htroot with rfl | rfl | rfl <;> linarith
    · symm
      apply sign_eq_of_continuousOn_noZero_Icc hqp hFcont.continuousOn
      intro t ht htzero
      have htroot := (hzero t).mp htzero
      have hdt : d < t := hq.trans_le ht.1
      rcases htroot with rfl | rfl | rfl <;> linarith
  have hsx₁y₁ := sameAB hx₁ hy₁
  have hsy₂z₂ := sameBD hy₂ hz₂
  have hx₀ne : F x₀ ≠ 0 := by
    intro hxzero
    rcases (hzero x₀).mp hxzero with rfl | rfl | rfl <;>
      linarith [hx₀.1, hx₀.2, hab, hbd]
  refine ⟨A, B, C, D, hnonzero, hA, hB, hD, ?_⟩
  rcases lt_or_gt_of_ne hx₀ne with hx₀neg | hx₀pos
  · left
    have hsx₀ : SignType.sign (F x₀) = -1 := sign_neg hx₀neg
    have hsx₁ : SignType.sign (F x₁) = 1 := by
      rw [hsx₀] at hflipA
      simpa [F] using (congrArg Neg.neg hflipA).symm
    have hsy₁ : SignType.sign (F y₁) = 1 := by
      rw [← hsx₁y₁]
      exact hsx₁
    have hsy₂ : SignType.sign (F y₂) = -1 := by
      rw [hsy₁] at hflipB
      simpa [F] using (congrArg Neg.neg hflipB).symm
    have hsz₂ : SignType.sign (F z₂) = -1 := by
      rw [← hsy₂z₂]
      exact hsy₂
    have hsz₃ : SignType.sign (F z₃) = 1 := by
      rw [hsz₂] at hflipD
      simpa [F] using (congrArg Neg.neg hflipD).symm
    intro t ht0
    rcases lt_trichotomy t a with hta | rfl | hat
    · have hst : SignType.sign (F t) = -1 := by
        rw [same0A ⟨ht0, hta⟩ hx₀]
        exact hsx₀
      have hFt : F t < 0 := sign_eq_neg_one_iff.mp hst
      have hP :
          (t - a) * (t - b) * (t - d) < 0 := by
        have hta' : t - a < 0 := sub_neg.mpr hta
        have htb' : t - b < 0 := sub_neg.mpr (hta.trans hab)
        have htd' : t - d < 0 := sub_neg.mpr (hta.trans (hab.trans hbd))
        exact mul_neg_of_pos_of_neg
          (mul_pos_of_neg_of_neg hta' htb') htd'
      exact mul_nonneg_of_nonpos_of_nonpos hP.le hFt.le
    · simp
    · rcases lt_trichotomy t b with htb | rfl | hbt
      · have hst : SignType.sign (F t) = 1 := by
          rw [sameAB ⟨hat, htb⟩ hx₁]
          exact hsx₁
        have hFt : 0 < F t := sign_eq_one_iff.mp hst
        have hP :
            0 < (t - a) * (t - b) * (t - d) := by
          have hta' : 0 < t - a := sub_pos.mpr hat
          have htb' : t - b < 0 := sub_neg.mpr htb
          have htd' : t - d < 0 := sub_neg.mpr (htb.trans hbd)
          exact mul_pos_of_neg_of_neg
            (mul_neg_of_pos_of_neg hta' htb') htd'
        exact mul_nonneg hP.le hFt.le
      · simp
      · rcases lt_trichotomy t d with htd | rfl | hdt
        · have hst : SignType.sign (F t) = -1 := by
            rw [sameBD ⟨hbt, htd⟩ hy₂]
            exact hsy₂
          have hFt : F t < 0 := sign_eq_neg_one_iff.mp hst
          have hP :
              (t - a) * (t - b) * (t - d) < 0 := by
            have hta' : 0 < t - a := sub_pos.mpr (hab.trans hbt)
            have htb' : 0 < t - b := sub_pos.mpr hbt
            have htd' : t - d < 0 := sub_neg.mpr htd
            exact mul_neg_of_pos_of_neg (mul_pos hta' htb') htd'
          exact mul_nonneg_of_nonpos_of_nonpos hP.le hFt.le
        · simp
        · have hst : SignType.sign (F t) = 1 := by
            rw [sameD hdt hz₃.1]
            exact hsz₃
          have hFt : 0 < F t := sign_eq_one_iff.mp hst
          have hP :
              0 < (t - a) * (t - b) * (t - d) := by
            exact mul_pos
              (mul_pos (sub_pos.mpr ((hab.trans hbd).trans hdt))
                (sub_pos.mpr (hbd.trans hdt)))
              (sub_pos.mpr hdt)
          exact mul_nonneg hP.le hFt.le
  · right
    have hsx₀ : SignType.sign (F x₀) = 1 := sign_pos hx₀pos
    have hsx₁ : SignType.sign (F x₁) = -1 := by
      rw [hsx₀] at hflipA
      simpa [F] using (congrArg Neg.neg hflipA).symm
    have hsy₁ : SignType.sign (F y₁) = -1 := by
      rw [← hsx₁y₁]
      exact hsx₁
    have hsy₂ : SignType.sign (F y₂) = 1 := by
      rw [hsy₁] at hflipB
      simpa [F] using (congrArg Neg.neg hflipB).symm
    have hsz₂ : SignType.sign (F z₂) = 1 := by
      rw [← hsy₂z₂]
      exact hsy₂
    have hsz₃ : SignType.sign (F z₃) = -1 := by
      rw [hsz₂] at hflipD
      simpa [F] using (congrArg Neg.neg hflipD).symm
    intro t ht0
    rcases lt_trichotomy t a with hta | rfl | hat
    · have hst : SignType.sign (F t) = 1 := by
        rw [same0A ⟨ht0, hta⟩ hx₀]
        exact hsx₀
      have hFt : 0 < F t := sign_eq_one_iff.mp hst
      have hP :
          (t - a) * (t - b) * (t - d) < 0 := by
        have hta' : t - a < 0 := sub_neg.mpr hta
        have htb' : t - b < 0 := sub_neg.mpr (hta.trans hab)
        have htd' : t - d < 0 := sub_neg.mpr (hta.trans (hab.trans hbd))
        exact mul_neg_of_pos_of_neg
          (mul_pos_of_neg_of_neg hta' htb') htd'
      exact mul_nonpos_of_nonpos_of_nonneg hP.le hFt.le
    · simp
    · rcases lt_trichotomy t b with htb | rfl | hbt
      · have hst : SignType.sign (F t) = -1 := by
          rw [sameAB ⟨hat, htb⟩ hx₁]
          exact hsx₁
        have hFt : F t < 0 := sign_eq_neg_one_iff.mp hst
        have hP :
            0 < (t - a) * (t - b) * (t - d) := by
          have hta' : 0 < t - a := sub_pos.mpr hat
          have htb' : t - b < 0 := sub_neg.mpr htb
          have htd' : t - d < 0 := sub_neg.mpr (htb.trans hbd)
          exact mul_pos_of_neg_of_neg
            (mul_neg_of_pos_of_neg hta' htb') htd'
        exact mul_nonpos_of_nonneg_of_nonpos hP.le hFt.le
      · simp
      · rcases lt_trichotomy t d with htd | rfl | hdt
        · have hst : SignType.sign (F t) = 1 := by
            rw [sameBD ⟨hbt, htd⟩ hy₂]
            exact hsy₂
          have hFt : 0 < F t := sign_eq_one_iff.mp hst
          have hP :
              (t - a) * (t - b) * (t - d) < 0 := by
            have hta' : 0 < t - a := sub_pos.mpr (hab.trans hbt)
            have htb' : 0 < t - b := sub_pos.mpr hbt
            have htd' : t - d < 0 := sub_neg.mpr htd
            exact mul_neg_of_pos_of_neg (mul_pos hta' htb') htd'
          exact mul_nonpos_of_nonpos_of_nonneg hP.le hFt.le
        · simp
        · have hst : SignType.sign (F t) = -1 := by
            rw [sameD hdt hz₃.1]
            exact hsz₃
          have hFt : F t < 0 := sign_eq_neg_one_iff.mp hst
          have hP :
              0 < (t - a) * (t - b) * (t - d) := by
            exact mul_pos
              (mul_pos (sub_pos.mpr ((hab.trans hbd).trans hdt))
                (sub_pos.mpr (hbd.trans hdt)))
              (sub_pos.mpr hdt)
          exact mul_nonpos_of_nonneg_of_nonpos hP.le hFt.le

theorem routeJExpHermiteCombination_mul_sine_eq_rows
    (c u A B C D t : ℝ) (h : ℝ → ℝ) :
    routeJExpHermiteCombination (2 * c) A B C D t *
        (Real.exp (-c * t) * (Real.sin (u * t) * h t)) =
      A * routeJContinuumSineValueIntegrand c u h t +
        B * routeJContinuumSineDerivativeIntegrand c u h t +
        C * routeJContinuumSineValueIntegrand (-c) u h t +
        D * routeJContinuumSineDerivativeIntegrand (-c) u h t := by
  unfold routeJExpHermiteCombination
    routeJContinuumSineValueIntegrand
    routeJContinuumSineDerivativeIntegrand
  rw [show (2 * c) * t = c * t + c * t by ring, Real.exp_add,
    show -c * t = -(c * t) by ring, Real.exp_neg]
  field_simp [Real.exp_ne_zero]

/-- Using all four actual sine/value-derivative rows strengthens the physical continuum
obstruction: a nonzero atomless source needs at least four changes of sign in
`sin(u t) h(t)`. -/
theorem routeJ_nonAtomicContinuum_sineRows_atMostThreeChanges_ae_zero
    {μ : Measure ℝ} [NullSingletonClass μ]
    {h : ℝ → ℝ} {c u a b d : ℝ}
    (hc : 0 < c) (ha : 0 < a) (hab : a < b) (hbd : b < d)
    (hsupport :
      ∀ᵐ t ∂μ, h t ≠ 0 → 0 < t ∧ Real.sin (u * t) ≠ 0)
    (hpattern :
      (∀ᵐ t ∂μ,
          0 ≤ (t - a) * (t - b) * (t - d) *
            (Real.sin (u * t) * h t)) ∨
        (∀ᵐ t ∂μ,
          (t - a) * (t - b) * (t - d) *
            (Real.sin (u * t) * h t) ≤ 0))
    (hVpos : Integrable (routeJContinuumSineValueIntegrand c u h) μ)
    (hVneg : Integrable (routeJContinuumSineValueIntegrand (-c) u h) μ)
    (hDpos : Integrable (routeJContinuumSineDerivativeIntegrand c u h) μ)
    (hDneg : Integrable (routeJContinuumSineDerivativeIntegrand (-c) u h) μ)
    (hVposZero :
      ∫ t, routeJContinuumSineValueIntegrand c u h t ∂μ = 0)
    (hVnegZero :
      ∫ t, routeJContinuumSineValueIntegrand (-c) u h t ∂μ = 0)
    (hDposZero :
      ∫ t, routeJContinuumSineDerivativeIntegrand c u h t ∂μ = 0)
    (hDnegZero :
      ∫ t, routeJContinuumSineDerivativeIntegrand (-c) u h t ∂μ = 0) :
    h =ᵐ[μ] 0 := by
  obtain ⟨A, B, C, D, hcoeff, hJa, hJb, hJd, hcertificate⟩ :=
    exists_routeJExpHermiteCombination_three_root_sign_certificate
      (show 2 * c ≠ 0 by positivity) ha hab hbd
  let J := routeJExpHermiteCombination (2 * c) A B C D
  let p : ℝ → ℝ := fun t => Real.sin (u * t) * h t
  let P : ℝ → ℝ := fun t => (t - a) * (t - b) * (t - d)
  let W : ℝ → ℝ := fun t => J t * (Real.exp (-c * t) * p t)
  have hJzero (t : ℝ) :
      J t = 0 ↔ t = a ∨ t = b ∨ t = d :=
    routeJExpHermiteCombination_three_roots_zero_iff
      (show 2 * c ≠ 0 by positivity) hab hbd hcoeff hJa hJb hJd
  have hWint : Integrable W μ := by
    have hraw :=
      (((hVpos.const_mul A).add (hDpos.const_mul B)).add
        (hVneg.const_mul C)).add (hDneg.const_mul D)
    exact hraw.congr (Eventually.of_forall fun t => by
      dsimp [W, J, p]
      exact (routeJExpHermiteCombination_mul_sine_eq_rows
        c u A B C D t h).symm)
  have hWzero : ∫ t, W t ∂μ = 0 := by
    calc
      ∫ t, W t ∂μ =
          ∫ t,
            A * routeJContinuumSineValueIntegrand c u h t +
              B * routeJContinuumSineDerivativeIntegrand c u h t +
              C * routeJContinuumSineValueIntegrand (-c) u h t +
              D * routeJContinuumSineDerivativeIntegrand (-c) u h t ∂μ := by
                apply integral_congr_ae
                filter_upwards [] with t
                dsimp [W, J, p]
                exact routeJExpHermiteCombination_mul_sine_eq_rows
                  c u A B C D t h
      _ =
          ((A * (∫ t, routeJContinuumSineValueIntegrand c u h t ∂μ) +
              B * (∫ t, routeJContinuumSineDerivativeIntegrand c u h t ∂μ)) +
            C * (∫ t, routeJContinuumSineValueIntegrand (-c) u h t ∂μ)) +
              D * (∫ t, routeJContinuumSineDerivativeIntegrand (-c) u h t ∂μ) := by
                have hABC :
                    (∫ t,
                        A * routeJContinuumSineValueIntegrand c u h t +
                          B * routeJContinuumSineDerivativeIntegrand c u h t +
                          C * routeJContinuumSineValueIntegrand (-c) u h t ∂μ) =
                      (∫ t,
                          A * routeJContinuumSineValueIntegrand c u h t +
                            B * routeJContinuumSineDerivativeIntegrand c u h t ∂μ) +
                        ∫ t,
                          C * routeJContinuumSineValueIntegrand (-c) u h t ∂μ := by
                    simpa only [Pi.add_apply] using
                      integral_add
                        ((hVpos.const_mul A).add (hDpos.const_mul B))
                        (hVneg.const_mul C)
                have hAB :
                    (∫ t,
                        A * routeJContinuumSineValueIntegrand c u h t +
                          B * routeJContinuumSineDerivativeIntegrand c u h t ∂μ) =
                      (∫ t,
                          A * routeJContinuumSineValueIntegrand c u h t ∂μ) +
                        ∫ t,
                          B * routeJContinuumSineDerivativeIntegrand c u h t ∂μ := by
                    simpa only [Pi.add_apply] using
                      integral_add
                        (hVpos.const_mul A) (hDpos.const_mul B)
                calc
                  _ =
                      (∫ t,
                        A * routeJContinuumSineValueIntegrand c u h t +
                          B * routeJContinuumSineDerivativeIntegrand c u h t +
                          C * routeJContinuumSineValueIntegrand (-c) u h t ∂μ) +
                        ∫ t,
                          D * routeJContinuumSineDerivativeIntegrand (-c) u h t ∂μ := by
                            simpa only [Pi.add_apply] using
                              integral_add
                                (((hVpos.const_mul A).add
                                  (hDpos.const_mul B)).add
                                  (hVneg.const_mul C))
                                (hDneg.const_mul D)
                  _ =
                      ((∫ t,
                          A * routeJContinuumSineValueIntegrand c u h t +
                            B * routeJContinuumSineDerivativeIntegrand c u h t ∂μ) +
                        ∫ t,
                          C * routeJContinuumSineValueIntegrand (-c) u h t ∂μ) +
                        ∫ t,
                          D * routeJContinuumSineDerivativeIntegrand (-c) u h t ∂μ := by
                            rw [hABC]
                  _ =
                      (((∫ t,
                            A * routeJContinuumSineValueIntegrand c u h t ∂μ) +
                          ∫ t,
                            B * routeJContinuumSineDerivativeIntegrand c u h t ∂μ) +
                        ∫ t,
                          C * routeJContinuumSineValueIntegrand (-c) u h t ∂μ) +
                        ∫ t,
                          D * routeJContinuumSineDerivativeIntegrand (-c) u h t ∂μ := by
                            rw [hAB]
                  _ = _ := by
                    rw [integral_const_mul, integral_const_mul,
                      integral_const_mul, integral_const_mul]
      _ = 0 := by
        rw [hVposZero, hVnegZero, hDposZero, hDnegZero]
        ring
  have Wzero_of_nonneg (hWnonneg : ∀ᵐ t ∂μ, 0 ≤ W t) :
      W =ᵐ[μ] 0 :=
    (integral_eq_zero_iff_of_nonneg_ae hWnonneg hWint).1 hWzero
  have Wzero_of_nonpos (hWnonpos : ∀ᵐ t ∂μ, W t ≤ 0) :
      W =ᵐ[μ] 0 := by
    have hnegInt : Integrable (fun t => -W t) μ := hWint.neg
    have hnegNonneg : ∀ᵐ t ∂μ, 0 ≤ -W t :=
      hWnonpos.mono fun _ ht => neg_nonneg.mpr ht
    have hnegZero : ∫ t, -W t ∂μ = 0 := by
      rw [integral_neg, hWzero, neg_zero]
    have hz :=
      (integral_eq_zero_iff_of_nonneg_ae hnegNonneg hnegInt).1 hnegZero
    filter_upwards [hz] with t ht
    simpa only [Pi.zero_apply, neg_eq_zero] using ht
  have pointwise_same
      {t : ℝ} (ht : 0 < t)
      (hPJ : 0 ≤ P t * J t) (hPp : 0 ≤ P t * p t) :
      0 ≤ W t := by
    by_cases hPt : P t = 0
    · have hroot : t = a ∨ t = b ∨ t = d := by
        dsimp [P] at hPt
        rcases mul_eq_zero.mp hPt with habzero | hdroot
        · rcases mul_eq_zero.mp habzero with haroot | hbroot
          · exact Or.inl (sub_eq_zero.mp haroot)
          · exact Or.inr (Or.inl (sub_eq_zero.mp hbroot))
        · exact Or.inr (Or.inr (sub_eq_zero.mp hdroot))
      have hJt : J t = 0 := (hJzero t).2 hroot
      simp [W, hJt]
    · have hPsq : 0 < P t ^ (2 : ℕ) := sq_pos_of_ne_zero hPt
      have hprod : 0 ≤ (P t * J t) * (P t * p t) :=
        mul_nonneg hPJ hPp
      have hJp : 0 ≤ J t * p t := by
        rw [show (P t * J t) * (P t * p t) =
            P t ^ (2 : ℕ) * (J t * p t) by ring] at hprod
        exact nonneg_of_mul_nonneg_left
          (by simpa [mul_comm] using hprod) hPsq
      dsimp [W]
      rw [show J t * (Real.exp (-c * t) * p t) =
          Real.exp (-c * t) * (J t * p t) by ring]
      exact mul_nonneg (Real.exp_pos _).le hJp
  have pointwise_opposite
      {t : ℝ} (ht : 0 < t)
      (hPJ : 0 ≤ P t * J t) (hPp : P t * p t ≤ 0) :
      W t ≤ 0 := by
    by_cases hPt : P t = 0
    · have hroot : t = a ∨ t = b ∨ t = d := by
        dsimp [P] at hPt
        rcases mul_eq_zero.mp hPt with habzero | hdroot
        · rcases mul_eq_zero.mp habzero with haroot | hbroot
          · exact Or.inl (sub_eq_zero.mp haroot)
          · exact Or.inr (Or.inl (sub_eq_zero.mp hbroot))
        · exact Or.inr (Or.inr (sub_eq_zero.mp hdroot))
      have hJt : J t = 0 := (hJzero t).2 hroot
      simp [W, hJt]
    · have hPsq : 0 < P t ^ (2 : ℕ) := sq_pos_of_ne_zero hPt
      have hprod : (P t * J t) * (P t * p t) ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hPJ hPp
      have hJp : J t * p t ≤ 0 := by
        rw [show (P t * J t) * (P t * p t) =
            P t ^ (2 : ℕ) * (J t * p t) by ring] at hprod
        exact nonpos_of_mul_nonpos_left
          (by simpa [mul_comm] using hprod) hPsq
      dsimp [W]
      rw [show J t * (Real.exp (-c * t) * p t) =
          Real.exp (-c * t) * (J t * p t) by ring]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hJp
  have pointwise_both_nonpos
      {t : ℝ} (ht : 0 < t)
      (hPJ : P t * J t ≤ 0) (hPp : P t * p t ≤ 0) :
      0 ≤ W t := by
    by_cases hPt : P t = 0
    · have hroot : t = a ∨ t = b ∨ t = d := by
        dsimp [P] at hPt
        rcases mul_eq_zero.mp hPt with habzero | hdroot
        · rcases mul_eq_zero.mp habzero with haroot | hbroot
          · exact Or.inl (sub_eq_zero.mp haroot)
          · exact Or.inr (Or.inl (sub_eq_zero.mp hbroot))
        · exact Or.inr (Or.inr (sub_eq_zero.mp hdroot))
      have hJt : J t = 0 := (hJzero t).2 hroot
      simp [W, hJt]
    · have hPsq : 0 < P t ^ (2 : ℕ) := sq_pos_of_ne_zero hPt
      have hprod : 0 ≤ (P t * J t) * (P t * p t) :=
        mul_nonneg_of_nonpos_of_nonpos hPJ hPp
      have hJp : 0 ≤ J t * p t := by
        rw [show (P t * J t) * (P t * p t) =
            P t ^ (2 : ℕ) * (J t * p t) by ring] at hprod
        exact nonneg_of_mul_nonneg_left
          (by simpa [mul_comm] using hprod) hPsq
      dsimp [W]
      rw [show J t * (Real.exp (-c * t) * p t) =
          Real.exp (-c * t) * (J t * p t) by ring]
      exact mul_nonneg (Real.exp_pos _).le hJp
  have pointwise_reverse_opposite
      {t : ℝ} (ht : 0 < t)
      (hPJ : P t * J t ≤ 0) (hPp : 0 ≤ P t * p t) :
      W t ≤ 0 := by
    by_cases hPt : P t = 0
    · have hroot : t = a ∨ t = b ∨ t = d := by
        dsimp [P] at hPt
        rcases mul_eq_zero.mp hPt with habzero | hdroot
        · rcases mul_eq_zero.mp habzero with haroot | hbroot
          · exact Or.inl (sub_eq_zero.mp haroot)
          · exact Or.inr (Or.inl (sub_eq_zero.mp hbroot))
        · exact Or.inr (Or.inr (sub_eq_zero.mp hdroot))
      have hJt : J t = 0 := (hJzero t).2 hroot
      simp [W, hJt]
    · have hPsq : 0 < P t ^ (2 : ℕ) := sq_pos_of_ne_zero hPt
      have hprod : (P t * J t) * (P t * p t) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg hPJ hPp
      have hJp : J t * p t ≤ 0 := by
        rw [show (P t * J t) * (P t * p t) =
            P t ^ (2 : ℕ) * (J t * p t) by ring] at hprod
        exact nonpos_of_mul_nonpos_left
          (by simpa [mul_comm] using hprod) hPsq
      dsimp [W]
      rw [show J t * (Real.exp (-c * t) * p t) =
          Real.exp (-c * t) * (J t * p t) by ring]
      exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hJp
  have hWae : W =ᵐ[μ] 0 := by
    rcases hcertificate with hcert | hcert <;>
      rcases hpattern with hpat | hpat
    · apply Wzero_of_nonneg
      filter_upwards [hsupport, hpat] with t ht hpt
      by_cases hht : h t = 0
      · simp [W, p, hht]
      · exact pointwise_same (ht hht).1 (hcert t (ht hht).1) hpt
    · apply Wzero_of_nonpos
      filter_upwards [hsupport, hpat] with t ht hpt
      by_cases hht : h t = 0
      · simp [W, p, hht]
      · exact pointwise_opposite (ht hht).1 (hcert t (ht hht).1) hpt
    · apply Wzero_of_nonpos
      filter_upwards [hsupport, hpat] with t ht hpt
      by_cases hht : h t = 0
      · simp [W, p, hht]
      · exact pointwise_reverse_opposite
          (ht hht).1 (hcert t (ht hht).1) hpt
    · apply Wzero_of_nonneg
      filter_upwards [hsupport, hpat] with t ht hpt
      by_cases hht : h t = 0
      · simp [W, p, hht]
      · exact pointwise_both_nonpos
          (ht hht).1 (hcert t (ht hht).1) hpt
  filter_upwards [hWae, hsupport, μ.ae_ne a, μ.ae_ne b, μ.ae_ne d] with
      t hWt ht hta htb htd
  by_contra hht
  have hsource := ht hht
  have hJne : J t ≠ 0 := by
    intro hJt
    rcases (hJzero t).1 hJt with rfl | rfl | rfl
    · exact hta rfl
    · exact htb rfl
    · exact htd rfl
  have hnonzeroProduct :
      J t * Real.exp (-c * t) * Real.sin (u * t) * h t ≠ 0 :=
    mul_ne_zero
      (mul_ne_zero (mul_ne_zero hJne (Real.exp_ne_zero _)) hsource.2)
      hht
  apply hnonzeroProduct
  simpa [W, p, mul_assoc] using hWt

end

end RHTower
