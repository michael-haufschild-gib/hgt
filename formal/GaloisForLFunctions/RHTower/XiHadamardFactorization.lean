import GaloisForLFunctions.RHTower.XiCanonicalProduct
import GaloisForLFunctions.RHTower.EntireHasLog
import GaloisForLFunctions.RHTower.ReBoundAffine

/-!
# Multiplicity-exact Hadamard factorization data for Xi

The canonical product over the actual Xi divisor has exactly the same analytic order as `XiC`
at every point.  Filling the removable singularities of their quotient therefore produces a
globally entire, nowhere-zero factor and an exact product identity.  The remaining classical
Hadamard step is to use order-one growth to force that factor to be exponential-affine.
-/

open Complex Metric Function Filter Topology MeromorphicOn

namespace RHTower

noncomputable section

def xiSpectralPointSupport (ρ : XiDivisorSupport) : ℂ :=
  ((ρ : ℂ) - 1 / 2) * (-Complex.I)

theorem xiSpectralPoint_eq_support (q : XiZeroCopy) :
    xiSpectralPoint q = xiSpectralPointSupport q.1 := rfl

theorem xiSpectralPointSupport_injective :
    Function.Injective xiSpectralPointSupport := by
  intro ρ τ h
  apply Subtype.ext
  have hI : (-I : ℂ) ≠ 0 := neg_ne_zero.mpr I_ne_zero
  have hdiff : (ρ : ℂ) - 1 / 2 = (τ : ℂ) - 1 / 2 :=
    mul_right_cancel₀ hI (by simpa only [xiSpectralPointSupport] using h)
  exact sub_left_injective hdiff

abbrev XiZeroCopyAway (ρ : XiDivisorSupport) :=
  {q : XiZeroCopy // q.1 ≠ ρ}

def xiCanonicalProductAway (ρ : XiDivisorSupport) : ℂ → ℂ :=
  canonicalProductE1Indexed (fun q : XiZeroCopyAway ρ => xiSpectralPoint q.1)

theorem xiCanonicalProductAway_inv_sq_summable (ρ : XiDivisorSupport) :
    Summable (fun q : XiZeroCopyAway ρ => 1 / ‖xiSpectralPoint q.1‖ ^ (2 : ℕ)) :=
  xiSpectralPoint_inv_sq_summable.comp_injective Subtype.val_injective

theorem xiCanonicalProductAway_analytic (ρ : XiDivisorSupport) :
    AnalyticOnNhd ℂ (xiCanonicalProductAway ρ) Set.univ :=
  canonicalProductE1Indexed_analytic (fun q : XiZeroCopyAway ρ => xiSpectralPoint q.1)
    (fun q => xiSpectralPoint_ne_zero q.1)
    (xiCanonicalProductAway_inv_sq_summable ρ)

theorem xiCanonicalProductAway_ne_zero_at (ρ : XiDivisorSupport) :
    xiCanonicalProductAway ρ (xiSpectralPointSupport ρ) ≠ 0 := by
  apply canonicalProductE1Indexed_ne_zero
    (fun q : XiZeroCopyAway ρ => xiSpectralPoint q.1)
    (fun q => xiSpectralPoint_ne_zero q.1)
    (xiCanonicalProductAway_inv_sq_summable ρ)
  intro q heq
  apply q.2
  apply xiSpectralPointSupport_injective
  simpa only [xiSpectralPoint_eq_support] using heq.symm

def xiZeroCopyFiberEquiv (ρ : XiDivisorSupport) :
    Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))) ≃
      {q : XiZeroCopy // q.1 = ρ} where
  toFun j := ⟨⟨ρ, j⟩, rfl⟩
  invFun q := cast (by rw [q.2]) q.1.2
  left_inv j := rfl
  right_inv q := by
    rcases q with ⟨⟨τ, j⟩, h⟩
    cases h
    rfl

theorem xiCanonicalProduct_multipliable (z : ℂ) :
    Multipliable (fun q : XiZeroCopy => weierstrassE1 (z / xiSpectralPoint q)) := by
  let f : XiZeroCopy → ℂ := fun q => weierstrassE1 (z / xiSpectralPoint q) - 1
  have hfsum : Summable f :=
    (canonicalProductE1Indexed_sub_one_norm_summable xiSpectralPoint
      xiSpectralPoint_ne_zero xiSpectralPoint_inv_sq_summable z).of_norm
  have hm : Multipliable (fun q => 1 + f q) :=
    Complex.multipliable_one_add_of_summable hfsum
  convert hm using 1
  ext q
  simp only [f]
  ring

theorem xiCanonicalProduct_fiber_tprod (ρ : XiDivisorSupport) (z : ℂ) :
    (∏' q : {q : XiZeroCopy // q.1 = ρ},
      weierstrassE1 (z / xiSpectralPoint q.1)) =
      weierstrassE1 (z / xiSpectralPointSupport ρ) ^
        Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
  calc
    _ = (∏' j : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))),
        weierstrassE1 (z / xiSpectralPoint ((⟨ρ, j⟩ : XiZeroCopy)))) :=
      ((xiZeroCopyFiberEquiv ρ).tprod_eq _).symm
    _ = (∏' _j : Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))),
        weierstrassE1 (z / xiSpectralPointSupport ρ)) := by
      apply tprod_congr
      intro j
      rfl
    _ = _ := by
      rw [tprod_fintype, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

theorem xiCanonicalProduct_factorization_at_support (ρ : XiDivisorSupport) (z : ℂ) :
    xiCanonicalProduct z =
      weierstrassE1 (z / xiSpectralPointSupport ρ) ^
          Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) *
        xiCanonicalProductAway ρ z := by
  letI : Finite {q : XiZeroCopy // q.1 = ρ} :=
    Finite.of_equiv
      (Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))))
      (xiZeroCopyFiberEquiv ρ)
  have hs : Multipliable (fun q : {q : XiZeroCopy // q.1 = ρ} =>
      weierstrassE1 (z / xiSpectralPoint q.1)) := Multipliable.of_finite
  let g : XiZeroCopyAway ρ → ℂ := fun q =>
    weierstrassE1 (z / xiSpectralPoint q.1) - 1
  have hgsum : Summable g :=
    (canonicalProductE1Indexed_sub_one_norm_summable
      (fun q : XiZeroCopyAway ρ => xiSpectralPoint q.1)
      (fun q => xiSpectralPoint_ne_zero q.1)
      (xiCanonicalProductAway_inv_sq_summable ρ) z).of_norm
  have hsc : Multipliable (fun q : XiZeroCopyAway ρ =>
      weierstrassE1 (z / xiSpectralPoint q.1)) := by
    have hm := Complex.multipliable_one_add_of_summable hgsum
    convert hm using 1
    ext q
    simp only [g]
    ring
  -- split the product along the fibre `{q | q.1 = ρ}` and its complement
  have hsplit :
      (∏' q : {q : XiZeroCopy // q.1 = ρ},
          weierstrassE1 (z / xiSpectralPoint q.1)) *
        (∏' q : XiZeroCopyAway ρ,
          weierstrassE1 (z / xiSpectralPoint q.1)) =
        (∏' q : XiZeroCopy, weierstrassE1 (z / xiSpectralPoint q)) :=
    Multipliable.tprod_mul_tprod_compl (s := {q : XiZeroCopy | q.1 = ρ})
      (f := fun q : XiZeroCopy => weierstrassE1 (z / xiSpectralPoint q)) hs hsc
  rw [xiCanonicalProduct, xiCanonicalProductAway, canonicalProductE1Indexed]
  rw [← hsplit, xiCanonicalProduct_fiber_tprod]
  rfl

theorem weierstrassE1_div_analyticOrderAt (a : ℂ) (ha : a ≠ 0) :
    analyticOrderAt (fun z : ℂ => weierstrassE1 (z / a)) a = 1 := by
  let F : ℂ → ℂ := fun z => weierstrassE1 (z / a)
  have hF_an : AnalyticAt ℂ F a := by
    simp only [F, weierstrassE1]
    fun_prop
  have hE : HasDerivAt weierstrassE1 (-Complex.exp 1) 1 := by
    have hraw :=
      ((hasDerivAt_const (x := (1 : ℂ)) (c := (1 : ℂ))).sub (hasDerivAt_id 1)).mul
        (Complex.hasDerivAt_exp 1)
    convert! hraw using 1
    simp
  have hdiv : HasDerivAt (fun z : ℂ => z / a) (1 / a) a := by
    simpa using (hasDerivAt_id a).div_const a
  have hFderiv : HasDerivAt F ((-Complex.exp 1) * (1 / a)) a := by
    have hE' : HasDerivAt weierstrassE1 (-Complex.exp 1)
        ((fun z : ℂ => z / a) a) := by
      simpa only [div_self ha] using hE
    simpa only [F, Function.comp_def] using
      hE'.comp (h := fun z : ℂ => z / a) a hdiv
  apply hF_an.analyticOrderAt_eq_one_of_zero_deriv_ne_zero
  · simp only [F, div_self ha, weierstrassE1_one]
  · rw [hFderiv.deriv]
    exact mul_ne_zero (neg_ne_zero.mpr (Complex.exp_ne_zero 1)) (one_div_ne_zero ha)

theorem xiCanonicalProduct_analyticOrderAt_support (ρ : XiDivisorSupport) :
    analyticOrderAt xiCanonicalProduct (xiSpectralPointSupport ρ) =
      Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
  let a := xiSpectralPointSupport ρ
  let m := Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))
  let base : ℂ → ℂ := fun z => weierstrassE1 (z / a)
  have ha : a ≠ 0 := by
    dsimp only [a, xiSpectralPointSupport]
    exact mul_ne_zero (sub_ne_zero.mpr (xi_divisor_support_ne_half ρ))
      (neg_ne_zero.mpr I_ne_zero)
  have hbase_an : AnalyticAt ℂ base a := by
    simp only [base, weierstrassE1]
    fun_prop
  have hbase_order : analyticOrderAt base a = 1 := by
    simpa only [base] using weierstrassE1_div_analyticOrderAt a ha
  have haway_an : AnalyticAt ℂ (xiCanonicalProductAway ρ) a :=
    xiCanonicalProductAway_analytic ρ a (Set.mem_univ _)
  have haway_order : analyticOrderAt (xiCanonicalProductAway ρ) a = 0 :=
    haway_an.analyticOrderAt_eq_zero.mpr (xiCanonicalProductAway_ne_zero_at ρ)
  have hfun : xiCanonicalProduct = base ^ m * xiCanonicalProductAway ρ := by
    funext z
    simpa only [a, m, base, Pi.pow_apply, Pi.mul_apply] using
      xiCanonicalProduct_factorization_at_support ρ z
  rw [hfun, analyticOrderAt_mul (hbase_an.pow m) haway_an,
    analyticOrderAt_pow hbase_an, hbase_order, haway_order]
  simp [m]

theorem XiC_analytic : AnalyticOnNhd ℂ XiC Set.univ :=
  analyticOnNhd_univ_iff_differentiable.mpr XiC_differentiable

theorem XiC_analyticOrderAt_support (ρ : XiDivisorSupport) :
    analyticOrderAt XiC (xiSpectralPointSupport ρ) =
      Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ)) := by
  let a := xiSpectralPointSupport ρ
  let g : ℂ → ℂ := fun z => 1 / 2 + z * I
  have hga : g a = (ρ : ℂ) := by
    dsimp only [g, a, xiSpectralPointSupport]
    have hI : (-I) * I = (1 : ℂ) := by rw [neg_mul, I_mul_I]; ring
    rw [mul_assoc, hI, mul_one]
    ring
  have hg_an : AnalyticAt ℂ g a := by dsimp only [g]; fun_prop
  have hg_deriv : deriv g a ≠ 0 := by
    have hg' : HasDerivAt g I a := by
      dsimp only [g]
      convert! (hasDerivAt_const (x := a) (c := (1 / 2 : ℂ))).add
        ((hasDerivAt_id a).mul_const I) using 1
      ring
    rw [hg'.deriv]
    exact I_ne_zero
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := xi) hg_an hg_deriv
  have horder_comp : analyticOrderAt XiC a = analyticOrderAt xi (ρ : ℂ) := by
    rw [show XiC = xi ∘ g by rfl, hcomp, hga]
  have hfinite : analyticOrderAt xi (ρ : ℂ) ≠ ⊤ := xi_order_ne_top ρ
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp hfinite
  have hD : (MeromorphicOn.divisor xi Set.univ) (ρ : ℂ) = (n : ℤ) := by
    rw [xi_analyticOnNhd_univ.divisor_apply (Set.mem_univ (ρ : ℂ)), ← hn]
    simp
  rw [horder_comp, ← hn, hD]
  simp

theorem xiCanonicalProduct_analyticOrderAt_eq_XiC (z : ℂ) :
    analyticOrderAt xiCanonicalProduct z = analyticOrderAt XiC z := by
  by_cases hz : XiC z = 0
  · obtain ⟨q, hq⟩ := (XiC_eq_zero_iff_exists_xiZeroCopy z).mp hz
    rw [← hq, xiSpectralPoint_eq_support,
      xiCanonicalProduct_analyticOrderAt_support,
      XiC_analyticOrderAt_support]
  · have hP : xiCanonicalProduct z ≠ 0 := by
      exact (xiCanonicalProduct_eq_zero_iff_XiC_eq_zero z).not.mpr hz
    rw [(xiCanonicalProduct_analytic z (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hP,
      (XiC_analytic z (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hz]

theorem xiCanonicalProduct_zero : xiCanonicalProduct 0 = 1 := by
  rw [xiCanonicalProduct, canonicalProductE1Indexed]
  calc
    (∏' q : XiZeroCopy, weierstrassE1 (0 / xiSpectralPoint q)) =
        ∏' _q : XiZeroCopy, (1 : ℂ) := by
      apply tprod_congr
      intro q
      rw [zero_div, weierstrassE1_zero]
    _ = 1 := tprod_one

theorem XiC_order_ne_top (z : ℂ) : analyticOrderAt XiC z ≠ ⊤ := by
  let g : ℂ → ℂ := fun w => 1 / 2 + w * I
  have hg_an : AnalyticAt ℂ g z := by dsimp only [g]; fun_prop
  have hg_deriv : deriv g z ≠ 0 := by
    have hg' : HasDerivAt g I z := by
      dsimp only [g]
      convert! (hasDerivAt_const (x := z) (c := (1 / 2 : ℂ))).add
        ((hasDerivAt_id z).mul_const I) using 1
      ring
    rw [hg'.deriv]
    exact I_ne_zero
  rw [show XiC = xi ∘ g by rfl,
    analyticOrderAt_comp_of_deriv_ne_zero (f := xi) hg_an hg_deriv]
  exact xi_order_ne_top (g z)

/-- The pointwise quotient before filling its removable singularities. -/
def xiHadamardRawQuotient : ℂ → ℂ := XiC / xiCanonicalProduct

theorem xiHadamardRawQuotient_meromorphic :
    MeromorphicOn xiHadamardRawQuotient Set.univ :=
  XiC_analytic.meromorphicOn.div xiCanonicalProduct_analytic.meromorphicOn

theorem xiHadamardRawQuotient_order_zero (z : ℂ) :
    meromorphicOrderAt xiHadamardRawQuotient z = 0 := by
  have hfinite := XiC_order_ne_top z
  rw [xiHadamardRawQuotient,
    meromorphicOrderAt_div (XiC_analytic z (Set.mem_univ _)).meromorphicAt
      (xiCanonicalProduct_analytic z (Set.mem_univ _)).meromorphicAt,
    (XiC_analytic z (Set.mem_univ _)).meromorphicOrderAt_eq,
    (xiCanonicalProduct_analytic z (Set.mem_univ _)).meromorphicOrderAt_eq,
    xiCanonicalProduct_analyticOrderAt_eq_XiC]
  simp [hfinite]

/-- The entire, removable-singularity-filled quotient between `XiC` and its exact canonical
product. -/
def xiHadamardQuotient : ℂ → ℂ :=
  toMeromorphicNFOn xiHadamardRawQuotient Set.univ

theorem xiHadamardQuotient_analytic :
    AnalyticOnNhd ℂ xiHadamardQuotient Set.univ := by
  intro z hz
  have hNF := meromorphicNFOn_toMeromorphicNFOn xiHadamardRawQuotient Set.univ hz
  apply hNF.meromorphicOrderAt_nonneg_iff_analyticAt.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn xiHadamardRawQuotient_meromorphic hz,
    xiHadamardRawQuotient_order_zero]

theorem xiHadamardQuotient_ne_zero (z : ℂ) : xiHadamardQuotient z ≠ 0 := by
  have hNF := meromorphicNFOn_toMeromorphicNFOn xiHadamardRawQuotient Set.univ
    (Set.mem_univ z)
  apply hNF.meromorphicOrderAt_eq_zero_iff.mp
  rw [meromorphicOrderAt_toMeromorphicNFOn xiHadamardRawQuotient_meromorphic (Set.mem_univ z),
    xiHadamardRawQuotient_order_zero]

theorem xiHadamardQuotient_differentiable : Differentiable ℂ xiHadamardQuotient :=
  analyticOnNhd_univ_iff_differentiable.mp xiHadamardQuotient_analytic

theorem XiC_zero_ne : XiC 0 ≠ 0 := by
  have hpos := xi_pos_on_real_anchor (by norm_num : (0 : ℝ) < 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)
  intro hzero
  have hxi : xi ((1 : ℂ) / 2) = 0 := by
    simpa only [XiC, zero_mul, add_zero] using hzero
  have hpos' : 0 < (xi ((1 : ℂ) / 2)).re := by
    convert hpos using 1
    norm_num
  rw [hxi] at hpos'
  simp at hpos'

/-- Exact Hadamard quotient identity, before proving that the zero-free factor is constant. -/
theorem xiHadamardQuotient_mul_canonicalProduct :
    xiHadamardQuotient * xiCanonicalProduct = XiC := by
  have hP0 : xiCanonicalProduct 0 ≠ 0 := by rw [xiCanonicalProduct_zero]; exact one_ne_zero
  have hraw_an0 : AnalyticAt ℂ xiHadamardRawQuotient 0 := by
    exact (XiC_analytic 0 (Set.mem_univ _)).div
      (xiCanonicalProduct_analytic 0 (Set.mem_univ _)) hP0
  have hQraw : xiHadamardQuotient =ᶠ[𝓝 0] xiHadamardRawQuotient := by
    have hlocal := toMeromorphicNFOn_eq_toMeromorphicNFAt_on_nhds
      xiHadamardRawQuotient_meromorphic (Set.mem_univ (0 : ℂ))
    have heq : toMeromorphicNFAt xiHadamardRawQuotient 0 = xiHadamardRawQuotient :=
      toMeromorphicNFAt_eq_self.mpr hraw_an0.meromorphicNFAt
    rw [heq] at hlocal
    exact hlocal
  have hPne : ∀ᶠ z in 𝓝 (0 : ℂ), xiCanonicalProduct z ≠ 0 :=
    (xiCanonicalProduct_analytic 0 (Set.mem_univ _)).continuousAt.eventually_ne hP0
  have hlocal : xiHadamardQuotient * xiCanonicalProduct =ᶠ[𝓝 0] XiC := by
    filter_upwards [hQraw, hPne] with z hq hp
    simp only [Pi.mul_apply]
    rw [hq, xiHadamardRawQuotient, Pi.div_apply, div_mul_cancel₀ _ hp]
  exact (xiHadamardQuotient_analytic.mul xiCanonicalProduct_analytic).eq_of_eventuallyEq
    XiC_analytic hlocal

/-- Functional-equation reflection preserves the Xi divisor with multiplicity. -/
theorem xi_divisor_one_sub (z : ℂ) :
    (MeromorphicOn.divisor xi Set.univ) (1 - z) =
      (MeromorphicOn.divisor xi Set.univ) z := by
  rw [xi_analyticOnNhd_univ.divisor_apply (Set.mem_univ _),
    xi_analyticOnNhd_univ.divisor_apply (Set.mem_univ _), xi_orderAt_one_sub]

/-- Functional-equation reflection as an involution of the Xi-divisor support. -/
def xiZeroReflectEquiv : XiDivisorSupport ≃ XiDivisorSupport where
  toFun ρ := ⟨1 - (ρ : ℂ), by
    apply Function.mem_support.mpr
    rw [xi_divisor_one_sub]
    exact Function.mem_support.mp ρ.2⟩
  invFun ρ := ⟨1 - (ρ : ℂ), by
    apply Function.mem_support.mpr
    rw [xi_divisor_one_sub]
    exact Function.mem_support.mp ρ.2⟩
  left_inv ρ := Subtype.ext (by simp)
  right_inv ρ := Subtype.ext (by simp)

@[simp]
theorem xiZeroReflectEquiv_apply (ρ : XiDivisorSupport) :
    (xiZeroReflectEquiv ρ : ℂ) = 1 - (ρ : ℂ) := rfl

/-- Functional-equation reflection lifted to the exact multiplicity-copy index. -/
def xiZeroCopyReflectEquiv : XiZeroCopy ≃ XiZeroCopy :=
  Equiv.sigmaCongr xiZeroReflectEquiv (fun ρ => Equiv.cast (by
    change Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (ρ : ℂ))) =
      Fin (Int.toNat ((MeromorphicOn.divisor xi Set.univ) (1 - (ρ : ℂ))))
    rw [xi_divisor_one_sub]))

theorem xiSpectralPointSupport_reflect (ρ : XiDivisorSupport) :
    xiSpectralPointSupport (xiZeroReflectEquiv ρ) = -xiSpectralPointSupport ρ := by
  rw [xiSpectralPointSupport, xiSpectralPointSupport, xiZeroReflectEquiv_apply]
  ring

theorem xiSpectralPoint_reflect (q : XiZeroCopy) :
    xiSpectralPoint (xiZeroCopyReflectEquiv q) = -xiSpectralPoint q := by
  rw [xiSpectralPoint_eq_support, xiSpectralPoint_eq_support]
  change xiSpectralPointSupport (xiZeroReflectEquiv q.1) = -xiSpectralPointSupport q.1
  exact xiSpectralPointSupport_reflect q.1

/-- The multiplicity-exact canonical product is even, by reindexing every divisor copy through
functional-equation reflection. -/
theorem xiCanonicalProduct_even (z : ℂ) :
    xiCanonicalProduct (-z) = xiCanonicalProduct z := by
  change (∏' q : XiZeroCopy, weierstrassE1 (-z / xiSpectralPoint q)) =
    ∏' q : XiZeroCopy, weierstrassE1 (z / xiSpectralPoint q)
  calc
    (∏' q : XiZeroCopy, weierstrassE1 (-z / xiSpectralPoint q)) =
        ∏' q : XiZeroCopy,
          weierstrassE1 (-z / xiSpectralPoint (xiZeroCopyReflectEquiv q)) :=
      ((xiZeroCopyReflectEquiv.tprod_eq
        (fun q => weierstrassE1 (-z / xiSpectralPoint q))).symm)
    _ = ∏' q : XiZeroCopy, weierstrassE1 (z / xiSpectralPoint q) := by
      apply tprod_congr
      intro q
      rw [xiSpectralPoint_reflect]
      congr 1
      field_simp

/-- The removable zero-free Hadamard quotient is even as well.  Cancellation is performed on a
zero-free neighborhood of the origin and then extended globally by analytic uniqueness. -/
theorem xiHadamardQuotient_even (z : ℂ) :
    xiHadamardQuotient (-z) = xiHadamardQuotient z := by
  have hP0 : xiCanonicalProduct 0 ≠ 0 := by rw [xiCanonicalProduct_zero]; exact one_ne_zero
  have hPne : ∀ᶠ w in 𝓝 (0 : ℂ), xiCanonicalProduct w ≠ 0 :=
    (xiCanonicalProduct_analytic 0 (Set.mem_univ _)).continuousAt.eventually_ne hP0
  have hlocal : (fun w => xiHadamardQuotient (-w)) =ᶠ[𝓝 0] xiHadamardQuotient := by
    filter_upwards [hPne] with w hp
    have hneg := congrFun xiHadamardQuotient_mul_canonicalProduct (-w)
    have hpos := congrFun xiHadamardQuotient_mul_canonicalProduct w
    simp only [Pi.mul_apply] at hneg hpos
    rw [xiCanonicalProduct_even, XiC_even] at hneg
    exact mul_right_cancel₀ hp (hneg.trans hpos.symm)
  have hneg_an : AnalyticOnNhd ℂ (fun w => xiHadamardQuotient (-w)) Set.univ := by
    intro w _
    exact (xiHadamardQuotient_analytic (-w) (Set.mem_univ _)).comp
      (by fun_prop : AnalyticAt ℂ (fun u : ℂ => -u) w)
  have heq := hneg_an.eq_of_eventuallyEq xiHadamardQuotient_analytic hlocal
  exact congrFun heq z

/-- The zero-free entire Hadamard quotient admits an entire logarithm. -/
theorem xiHadamardQuotient_has_log :
    ∃ g : ℂ → ℂ, Differentiable ℂ g ∧
      ∀ z, xiHadamardQuotient z = Complex.exp (g z) :=
  entire_nonvanishing_has_log xiHadamardQuotient
    xiHadamardQuotient_differentiable xiHadamardQuotient_ne_zero

/-- Evenness forces the derivative of the Hadamard quotient at the origin to vanish. -/
theorem xiHadamardQuotient_deriv_zero : deriv xiHadamardQuotient 0 = 0 := by
  have heven : (fun z : ℂ => xiHadamardQuotient (-z)) = xiHadamardQuotient := by
    funext z
    exact xiHadamardQuotient_even z
  have hneg : HasDerivAt (fun z : ℂ => -z) (-1) 0 := (hasDerivAt_id 0).neg
  have hcomp : HasDerivAt (fun z : ℂ => xiHadamardQuotient (-z))
      (deriv xiHadamardQuotient 0 * (-1)) 0 := by
    have hQ' : HasDerivAt xiHadamardQuotient (deriv xiHadamardQuotient 0)
        ((fun z : ℂ => -z) 0) := by
      simpa using (xiHadamardQuotient_differentiable 0).hasDerivAt
    simpa only [Function.comp_def] using hQ'.comp (h := fun z : ℂ => -z) 0 hneg
  have heq := congrArg (fun f : ℂ → ℂ => deriv f 0) heven
  change deriv (fun z : ℂ => xiHadamardQuotient (-z)) 0 =
    deriv xiHadamardQuotient 0 at heq
  rw [hcomp.deriv] at heq
  have hnegself : -deriv xiHadamardQuotient 0 = deriv xiHadamardQuotient 0 := by
    simpa using heq
  exact neg_eq_self.mp hnegself

/-- Once the classical Hadamard real-part bound is supplied for an entire logarithm of the
quotient, the quotient is constant.  `entire_reBound_imp_affine` makes the logarithm affine, and
evenness kills its linear coefficient. -/
theorem xiHadamardQuotient_constant_of_log_reBound
    (g : ℂ → ℂ) (hg : Differentiable ℂ g)
    (hexp : ∀ z, xiHadamardQuotient z = Complex.exp (g z))
    (B : ℝ) (hB : 0 ≤ B)
    (hbound : ∀ z : ℂ, (g z).re ≤ B * (1 + ‖z‖) * Real.log (2 + ‖z‖)) :
    ∀ z, xiHadamardQuotient z = xiHadamardQuotient 0 := by
  have haff := entire_reBound_imp_affine g hg B hB hbound
  have hfun : xiHadamardQuotient = fun z => Complex.exp (g z) := funext hexp
  have hExpDeriv : HasDerivAt (fun z => Complex.exp (g z))
      (Complex.exp (g 0) * deriv g 0) 0 := (hg 0).hasDerivAt.cexp
  have hderivEq := congrArg (fun f : ℂ → ℂ => deriv f 0) hfun
  change deriv xiHadamardQuotient 0 = deriv (fun z => Complex.exp (g z)) 0 at hderivEq
  rw [xiHadamardQuotient_deriv_zero, hExpDeriv.deriv] at hderivEq
  have hgderiv : deriv g 0 = 0 := by
    exact (mul_eq_zero.mp hderivEq.symm).resolve_left (Complex.exp_ne_zero _)
  intro z
  rw [hexp z, hexp 0, haff z, hgderiv, zero_mul, add_zero]

end

end RHTower
