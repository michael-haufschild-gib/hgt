import GaloisForLFunctions.RHTower.RiemannHypothesisSOTA2026
import GaloisForLFunctions.RHTower.SuzukiCarlemanCentralFlux
import GaloisForLFunctions.RHTower.FiniteSpectralTraceNoGo
import GaloisForLFunctions.RHTower.XiGuinandWeilRectanglePeeling

/-!
# Suzuki's ordinary entire characteristic limit is impossible

The legacy Suzuki limit wall makes its meromorphic quotient target entire.  Assuming that wall
first gives RH through the existing zero-transfer theorem.  Existing infinite Xi-zero supply then
gives two distinct positive real centered zeros, while compact-rectangle finiteness selects a
consecutive pair.  Rolle supplies a nonzero critical point between them where Xi itself is nonzero.
At that point the quotient has negative meromorphic order, contradicting the claimed entire target.

Thus the legacy wall is unconditionally false.  The argument also records reusable source-level
connectors for positive Xi-zero gaps and the precise pole at a nonzero Xi critical point.
-/

open Complex Filter Topology Set

namespace RHTower

noncomputable section

/-- The derivative of centered Xi has finite analytic order at every point. -/
theorem analyticOrderAt_deriv_XiC_ne_top (z : ℂ) :
    analyticOrderAt (deriv XiC) z ≠ ⊤ := by
  have hglobal : AnalyticOnNhd ℂ (deriv XiC) Set.univ :=
    XiC_analytic.deriv
  obtain ⟨x, hx⟩ : ∃ x : ℂ, deriv XiC x ≠ 0 := by
    by_contra h
    push Not at h
    have hfun : deriv XiC = fun _ : ℂ => 0 := funext h
    have hsecond : deriv (deriv XiC) 0 = 0 := by
      rw [hfun]
      simp
    have hcurv := XiC_secondDeriv_div_center_re_neg
    rw [hsecond, zero_div] at hcurv
    norm_num at hcurv
  apply hglobal.analyticOrderAt_ne_top_of_isPreconnected isPreconnected_univ
    (x := x) (y := z) (Set.mem_univ _) (Set.mem_univ _)
  rw [(hglobal x (Set.mem_univ x)).analyticOrderAt_eq_zero.mpr hx]
  exact ENat.zero_ne_top

/-- A nonzero critical point of centered Xi at which Xi is nonzero is a genuine pole of
Suzuki's unshifted target. -/
theorem not_analyticAt_suzukiXiCharacteristicTarget_of_deriv_eq_zero
    {c : ℂ} (hc : c ≠ 0) (hXi : XiC c ≠ 0)
    (hderiv : deriv XiC c = 0) :
    ¬ AnalyticAt ℂ suzukiXiCharacteristicTarget c := by
  intro htarget
  let numerator : ℂ → ℂ := fun z => z ^ 2 * XiC z
  have hnum : AnalyticAt ℂ numerator c := by
    dsimp only [numerator]
    exact (analyticAt_id.pow 2).mul
      (XiC_analytic c (Set.mem_univ c))
  have hnum0 : numerator c ≠ 0 := by
    dsimp only [numerator]
    exact mul_ne_zero (pow_ne_zero 2 hc) hXi
  have hnumOrder : analyticOrderAt numerator c = 0 :=
    hnum.analyticOrderAt_eq_zero.mpr hnum0
  have hden : AnalyticAt ℂ (deriv XiC) c :=
    (XiC_analytic c (Set.mem_univ c)).deriv
  have hdenOrder0 : analyticOrderAt (deriv XiC) c ≠ 0 :=
    analyticOrderAt_ne_zero.mpr ⟨hden, hderiv⟩
  have hdenOrderTop := analyticOrderAt_deriv_XiC_ne_top c
  let m : ℕ := (analyticOrderAt (deriv XiC) c).toNat
  have hm : (m : ℕ∞) = analyticOrderAt (deriv XiC) c :=
    ENat.coe_toNat hdenOrderTop
  have hm0 : m ≠ 0 := by
    intro hmzero
    apply hdenOrder0
    rw [← hm, hmzero]
    rfl
  have htargetOrder :
      meromorphicOrderAt suzukiXiCharacteristicTarget c < 0 := by
    unfold suzukiXiCharacteristicTarget suzukiShiftedXiTarget
      suzukiShiftedXiDenominator
    simp only [zero_mul, sub_zero]
    change meromorphicOrderAt
      (numerator / deriv XiC) c < 0
    rw [meromorphicOrderAt_div hnum.meromorphicAt hden.meromorphicAt,
      hnum.meromorphicOrderAt_eq, hden.meromorphicOrderAt_eq,
      hnumOrder, ← hm]
    simp only [ENat.map_zero, ENat.map_coe]
    have hmposZ : (0 : ℤ) < (m : ℤ) := by
      exact_mod_cast Nat.pos_of_ne_zero hm0
    have hmposTop : (0 : WithTop ℤ) < ((m : ℤ) : WithTop ℤ) :=
      WithTop.coe_lt_coe.mpr hmposZ
    change (((0 : ℤ) : WithTop ℤ) - ((m : ℤ) : WithTop ℤ)) <
      ((0 : ℤ) : WithTop ℤ)
    rw [← WithTop.LinearOrderedAddCommGroup.coe_sub]
    exact WithTop.coe_lt_coe.mpr (sub_neg.mpr hmposZ)
  have htargetNonneg :
      0 ≤ meromorphicOrderAt suzukiXiCharacteristicTarget c := by
    rw [htarget.meromorphicOrderAt_eq]
    have enatMap_nonneg (n : ℕ∞) :
        (0 : WithTop ℤ) ≤ ENat.map Nat.cast n := by
      induction n using ENat.recTopCoe with
      | top => simp
      | coe n => simp
    exact enatMap_nonneg _
  exact (not_lt_of_ge htargetNonneg) htargetOrder

/-- The real centered Xi detector is continuous. -/
theorem continuous_Xi : Continuous Xi := by
  have h :
      Continuous (fun t : ℝ => (XiC (t : ℂ)).re) :=
    Complex.continuous_re.comp
      (XiC_analytic.continuous.comp RCLike.continuous_ofReal)
  simpa only [XiC_ofReal, Complex.ofReal_re] using h

/-- Rolle connector from two real centered Xi zeros to a real critical point between them. -/
theorem exists_deriv_XiC_eq_zero_between_real_zeros
    {a b : ℝ} (hab : a < b)
    (ha : XiC (a : ℂ) = 0) (hb : XiC (b : ℂ) = 0) :
    ∃ c ∈ Set.Ioo a b, deriv XiC (c : ℂ) = 0 := by
  have haXi : Xi a = 0 := by
    have := ha
    rw [XiC_ofReal] at this
    exact_mod_cast this
  have hbXi : Xi b = 0 := by
    have := hb
    rw [XiC_ofReal] at this
    exact_mod_cast this
  obtain ⟨c, hc, hderiv⟩ :=
    exists_deriv_eq_zero hab continuous_Xi.continuousOn (haXi.trans hbXi.symm)
  refine ⟨c, hc, ?_⟩
  rw [XiC_deriv_ofReal, hderiv]
  norm_num

/-- A Xi zero on the critical line gives a positive-height centered Xi zero after reflection. -/
theorem XiC_abs_im_eq_zero_of_xi_zero_on_critical_line
    {rho : ℂ} (hre : rho.re = 1 / 2) (hzero : xi rho = 0) :
    XiC ((|rho.im| : ℝ) : ℂ) = 0 := by
  have him : XiC (rho.im : ℂ) = 0 := by
    have harg : (1 / 2 : ℂ) + (rho.im : ℂ) * I = rho := by
      apply Complex.ext
      · simpa using hre.symm
      · simp
    rw [XiC, harg, hzero]
  rcases le_total 0 rho.im with hnonneg | hnonpos
  · simpa [abs_of_nonneg hnonneg] using him
  · rw [abs_of_nonpos hnonpos]
    rw [Complex.ofReal_neg, XiC_even]
    exact him

/-- RH and the already-proved infinite Xi divisor supply two distinct positive real Xi zeros. -/
theorem exists_two_distinct_positive_real_XiC_zeros_of_rh
    (hRH : RiemannHypothesis) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ a ≠ b ∧
      XiC (a : ℂ) = 0 ∧ XiC (b : ℂ) = 0 := by
  let rho0 : ℂ := xiZeroPoint 0
  obtain ⟨n, hn⟩ :=
    exists_xiZeroPoint_not_mem ({rho0, 1 - rho0} : Finset ℂ)
  let rhon : ℂ := xiZeroPoint n
  have hzero0 : xi rho0 = 0 := xiZeroPoint_eq_zero 0
  have hzeron : xi rhon = 0 := xiZeroPoint_eq_zero n
  have hre0 : rho0.re = 1 / 2 :=
    xi_zero_re_eq_half_of_RH hRH hzero0
  have hren : rhon.re = 1 / 2 :=
    xi_zero_re_eq_half_of_RH hRH hzeron
  have hroot0 : XiC ((|rho0.im| : ℝ) : ℂ) = 0 :=
    XiC_abs_im_eq_zero_of_xi_zero_on_critical_line hre0 hzero0
  have hrootn : XiC ((|rhon.im| : ℝ) : ℂ) = 0 :=
    XiC_abs_im_eq_zero_of_xi_zero_on_critical_line hren hzeron
  have him0 : rho0.im ≠ 0 := by
    intro him
    apply XiC_zero_ne
    simpa [him] using hroot0
  have himn : rhon.im ≠ 0 := by
    intro him
    apply XiC_zero_ne
    simpa [him] using hrootn
  have habs : |rho0.im| ≠ |rhon.im| := by
    intro h
    rcases abs_eq_abs.mp h with him | him
    · have hrho : rhon = rho0 := by
        apply Complex.ext
        · exact hren.trans hre0.symm
        · exact him.symm
      exact hn (by simp [rhon, hrho])
    · have hrho : rhon = 1 - rho0 := by
        apply Complex.ext
        · simp only [sub_re, one_re]
          rw [hren, hre0]
          norm_num
        · simp only [sub_im, one_im, zero_sub]
          linarith
      exact hn (by simp [rhon, hrho])
  exact ⟨|rho0.im|, |rhon.im|, abs_pos.mpr him0, abs_pos.mpr himn,
    habs, hroot0, hrootn⟩

/-- Compact Xi-zero finiteness selects consecutive positive zeros from any two positive zeros. -/
theorem exists_positive_real_XiC_zero_gap_of_two_zeros
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hza : XiC (a : ℂ) = 0) (hzb : XiC (b : ℂ) = 0) :
    ∃ p q : ℝ, 0 < p ∧ p < q ∧
      XiC (p : ℂ) = 0 ∧ XiC (q : ℂ) = 0 ∧
      ∀ t ∈ Set.Ioo p q, XiC (t : ℂ) ≠ 0 := by
  classical
  let Z : Finset ℂ :=
    xiCClosedRectangleZeros (a : ℂ) (b : ℂ)
  let S : Finset ℝ := Z.image Complex.re
  have hmem (t : ℝ) (hat : a ≤ t) (htb : t ≤ b)
      (hzt : XiC (t : ℂ) = 0) : t ∈ S := by
    simp only [S, Finset.mem_image]
    refine ⟨(t : ℂ), ?_, by simp⟩
    change (t : ℂ) ∈ xiCClosedRectangleZeros (a : ℂ) (b : ℂ)
    rw [mem_xiCClosedRectangleZeros]
    refine ⟨?_, hzt⟩
    rw [mem_reProdIm]
    constructor
    · simpa [uIcc_of_le hab.le] using And.intro hat htb
    · simp
  let P : Finset ℝ := S.filter fun t => t < b
  have haP : a ∈ P := by
    simp only [P, Finset.mem_filter]
    exact ⟨hmem a le_rfl hab.le hza, hab⟩
  have hPne : P.Nonempty := ⟨a, haP⟩
  let p : ℝ := P.max' hPne
  have hpP : p ∈ P := by
    exact Finset.max'_mem P hPne
  have hpS : p ∈ S := (Finset.mem_filter.mp hpP).1
  have hpb : p < b := (Finset.mem_filter.mp hpP).2
  have hap : a ≤ p := by
    exact Finset.le_max' P a haP
  have hzp : XiC (p : ℂ) = 0 := by
    simp only [S, Finset.mem_image] at hpS
    obtain ⟨z, hzZ, hzre⟩ := hpS
    change z ∈ xiCClosedRectangleZeros (a : ℂ) (b : ℂ) at hzZ
    rw [mem_xiCClosedRectangleZeros] at hzZ
    have hcoords := mem_reProdIm.mp hzZ.1
    have hzim : z.im = 0 := by
      simpa using hcoords.2
    have hzEq : z = (p : ℂ) := by
      apply Complex.ext
      · simpa using hzre
      · simpa using hzim
    simpa [hzEq] using hzZ.2
  refine ⟨p, b, ha.trans_le hap, hpb, hzp, hzb, ?_⟩
  intro t ht hzt
  have htS : t ∈ S :=
    hmem t (le_trans hap ht.1.le) ht.2.le hzt
  have htP : t ∈ P := by
    simp only [P, Finset.mem_filter]
    exact ⟨htS, ht.2⟩
  have htp : t ≤ p := Finset.le_max' P t htP
  exact (not_lt_of_ge htp) ht.1

/-- Under RH, centered Xi has a positive consecutive zero pair. -/
theorem exists_positive_real_XiC_zero_gap_of_rh
    (hRH : RiemannHypothesis) :
    ∃ p q : ℝ, 0 < p ∧ p < q ∧
      XiC (p : ℂ) = 0 ∧ XiC (q : ℂ) = 0 ∧
      ∀ t ∈ Set.Ioo p q, XiC (t : ℂ) ≠ 0 := by
  obtain ⟨a, b, ha, hb, hab, hza, hzb⟩ :=
    exists_two_distinct_positive_real_XiC_zeros_of_rh hRH
  rcases lt_or_gt_of_ne hab with hablt | hbalt
  · exact exists_positive_real_XiC_zero_gap_of_two_zeros
      ha hablt hza hzb
  · exact exists_positive_real_XiC_zero_gap_of_two_zeros
      hb hbalt hzb hza

/-- Suzuki's legacy ordinary-entire compact-limit wall is unconditionally false. -/
theorem not_suzukiXiCharacteristicLimitWall :
    ¬ SuzukiXiCharacteristicLimitWall := by
  intro hwall
  have hRH : RiemannHypothesis :=
    suzukiXiCharacteristicLimitWall_implies_riemannHypothesis hwall
  obtain ⟨p, q, hp, hpq, hzp, hzq, hgap⟩ :=
    exists_positive_real_XiC_zero_gap_of_rh hRH
  obtain ⟨c, hc, hderiv⟩ :=
    exists_deriv_XiC_eq_zero_between_real_zeros hpq hzp hzq
  have hc0R : c ≠ 0 := ne_of_gt (hp.trans hc.1)
  have hc0 : (c : ℂ) ≠ 0 := by
    exact_mod_cast hc0R
  have hcXi : XiC (c : ℂ) ≠ 0 := hgap c hc
  rcases hwall with ⟨W, hconv, hentire, hreal, htarget, a, ha⟩
  exact not_analyticAt_suzukiXiCharacteristicTarget_of_deriv_eq_zero
    hc0 hcXi hderiv (htarget (c : ℂ) (Set.mem_univ _))

end

end RHTower
