import GaloisForLFunctions.ExceptionalLayerTheory.EveryFiniteCofactorSeesTheOrdinaryPrimeCount
import GaloisForLFunctions.ExceptionalLayerTheory.TheLastQuotientClassDetectsEveryRightZero

/-!
# The logarithmic singularity in each last quotient class

The centered ordinary-prime series has a derivative containing
the logarithmic derivative of zeta. Dividing any continuation of the
filtered series by its entire filter would make the primitive meromorphic.
This is impossible at a zeta zero, even if the filter vanishes there.
-/

noncomputable section

open Complex Filter Topology

namespace GaloisForLFunctions.ExceptionalLayerTheory

private theorem exists_lastClass_euler_point {q : ℕ} [NeZero q] (hq : 2≤q) :
    ∃ x : ℝ, 3<x ∧ lastQuotientClassSymbol q x≠0 := by
  let c := fun n : ℕ => lastClassJumps (n : ZMod q)
  by_contra! h
  have he : (fun x : ℝ => LSeries c x) =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop (3:ℝ)] with x hx
    change LSeries (fun n : ℕ => lastClassJumps (n : ZMod q)) (x:ℂ) = 0
    rw [← lastQuotientClassSymbol_eq_LSeries q (by simpa using (lt_trans (by norm_num : (1:ℝ)<3) hx))]
    exact h x hx
  have ht := (ZMod.LSeriesSummable_of_one_lt_re (lastClassJumps (q := q)) (s := (2:ℂ)) (by norm_num)).abscissaOfAbsConv_le
  have hh := (LSeries_eventually_eq_zero_iff'.mp he).resolve_right
    (ne_top_of_le_ne_top (EReal.coe_ne_top _) ht)
  have hzero := hh q (by omega)
  have hne : (0 : ZMod q)≠ -1 := by
    intro eq
    have hone : (1:ZMod q)=0 := by simpa using congrArg Neg.neg eq.symm
    have hd : q ∣ 1 := (ZMod.natCast_eq_zero_iff 1 q).mp (by simpa using hone)
    have := Nat.le_of_dvd one_pos hd
    omega
  simp [c,lastClassJumps,ZMod.natCast_self,hne] at hzero

/-- Every fixed quotient class detects all right zeros through its ordinary-prime
series. The symbol may have a zero of any finite order at the zeta zero. -/
theorem lastClass_primePrimitive_continuation_excludes_zero {q : ℕ} [NeZero q] (hq : 2≤q)
    {b : ℝ} (hb : 1/2≤b) (hb1 : b<1) (H : ℂ → ℂ) (hH : MeromorphicOn H {s : ℂ | b<s.re})
    (he : ∀ s : ℂ, 3<s.re → H s =
      lastQuotientClassSymbol q s*LSeries (fun n => (ordinaryPrimeCountWeight n : ℂ)) s)
    {ρ : ℂ} (hρ : b<ρ.re) : riemannZeta ρ≠0 := by
  obtain ⟨x,hx,hD⟩ := exists_lastClass_euler_point hq
  have hx1 : 1<x := (by norm_num : (1:ℝ)<3).trans hx
  let D := lastQuotientClassSymbol q
  have hreg := differentiable_lastQuotientClassSymbol q
  have hG : MeromorphicOn (H/D) {s : ℂ | b<s.re} :=
    fun z hz => (hH z hz).div (hreg.analyticAt z).meromorphicAt
  apply ordinaryPrimeCount_series_continuation_excludes_right_zero hb (hb1.trans hx1) hx1 hG _ hρ
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (x:ℂ) ∈ {s : ℂ | 3<s.re} from hx),hreg.continuous.continuousAt.eventually_ne hD] with s hs hd
  change H s/lastQuotientClassSymbol q s=_
  rw [he s hs,mul_div_cancel_left₀ _ hd]

#print axioms lastClass_primePrimitive_continuation_excludes_zero

end GaloisForLFunctions.ExceptionalLayerTheory
