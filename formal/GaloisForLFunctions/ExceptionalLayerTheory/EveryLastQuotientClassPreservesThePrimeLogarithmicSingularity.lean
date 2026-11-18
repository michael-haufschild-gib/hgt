import GaloisForLFunctions.ExceptionalLayerTheory.EveryFiniteCofactorSeesTheOrdinaryPrimeCount
import GaloisForLFunctions.ExceptionalLayerTheory.TheLastQuotientClassDetectsEveryRightZero
import GaloisForLFunctions.RHTower.CriticalCenteredPrimeTailEulerPrimitive

/-!
# The logarithmic singularity in each last quotient class

The divided prime-power weights have a primitive whose derivative contains
the logarithmic derivative of zeta. Dividing any continuation of the
filtered series by its entire filter would make the primitive meromorphic.
This is impossible at a zeta zero, even if the filter vanishes there.
-/

noncomputable section

open Complex Filter Topology

namespace GaloisForLFunctions.ExceptionalLayerTheory

private def dividedPrimeCurrent (s : ℂ) : ℂ := logDeriv riemannZeta s+riemannZeta s-1

private theorem dividedPrimeCurrent_meromorphic (s : ℂ) : MeromorphicAt dividedPrimeCurrent s := by
  have hz := _root_.RHTower.meromorphicAt_riemannZeta_everywhere s
  have h1 : MeromorphicAt (fun _ : ℂ => (1:ℂ)) s := analyticAt_const.meromorphicAt
  exact ((hz.deriv.div hz).add hz).sub h1

private theorem dividedPrimeCurrent_pole {ρ : ℂ} (hz : riemannZeta ρ=0) :
    meromorphicOrderAt dividedPrimeCurrent ρ=((-1:ℤ):WithTop ℤ) := by
  obtain ⟨m,hm,hr⟩ := _root_.RHTower.neg_logDeriv_zeta_zero_residue hz
  have hreg := ((differentiableAt_riemannZeta (_root_.RHTower.riemannZeta_zero_ne_one hz)).continuousAt.sub
    (continuousAt_const (y := (1:ℂ)))).tendsto.mono_left (nhdsWithin_le_nhds (s := ({ρ}ᶜ : Set ℂ)))
  have hlin := ((continuous_id.sub continuous_const).tendsto' ρ 0 (sub_self ρ)).mono_left
    (nhdsWithin_le_nhds (s := ({ρ}ᶜ : Set ℂ)))
  apply meromorphicOrderAt_eq_neg_one_of_tendsto_mul_sub (dividedPrimeCurrent_meromorphic ρ) (c := (m:ℂ))
    (Nat.cast_ne_zero.mpr (by omega))
  convert (hlin.mul hreg).sub hr using 1
  · funext s
    unfold dividedPrimeCurrent logDeriv
    ring
  · rw [zero_mul,zero_sub,neg_neg]

/-- A nonzero analytic filter cannot remove a branch of the divided prime
weights at a zeta zero in the half-plane of continuation. -/
theorem zeta_ne_zero_of_filtered_primePrimitive_continuation {b x : ℝ} {D H : ℂ → ℂ}
    (hbx : b<x) (hx : 1<x) (hD : Differentiable ℂ D) (hDx : D x≠0)
    (hH : MeromorphicOn H {s : ℂ | b<s.re})
    (he : H =ᶠ[𝓝 (x:ℂ)] fun s => D s*_root_.RHTower.centeredPrimeTailEulerPrimitive s)
    {ρ : ℂ} (hρ : b<ρ.re) : riemannZeta ρ≠0 := by
  intro hz
  let G := H/D
  let U := {s : ℂ | b<s.re}
  have hG : MeromorphicOn G U := fun s hs => (hH s hs).div (hD.analyticAt s).meromorphicAt
  have hEq : G =ᶠ[𝓝 (x:ℂ)] _root_.RHTower.centeredPrimeTailEulerPrimitive := by
    filter_upwards [he,hD.continuous.continuousAt.eventually_ne hDx] with s hs hDs
    change H s/D s=_
    rw [hs,mul_div_cancel_left₀ _ hDs]
  have hnear : {s : ℂ | 1<s.re} ∈ 𝓝 (x:ℂ) :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hx
  let F := deriv G-dividedPrimeCurrent
  have hbase : meromorphicOrderAt F (x:ℂ)=⊤ := by
    apply meromorphicOrderAt_eq_top_iff.mpr
    filter_upwards [nhdsWithin_le_nhds hEq.deriv,nhdsWithin_le_nhds hnear] with s hh hs
    exact sub_eq_zero.mpr (hh.trans (_root_.RHTower.hasDerivAt_centeredPrimeTailEulerPrimitive hs).deriv)
  have hmero : MeromorphicOn F U := fun z hzu => (hG z hzu).deriv.sub (dividedPrimeCurrent_meromorphic z)
  have hp : meromorphicOrderAt F ρ=⊤ := by
    by_contra hn
    exact (hmero.meromorphicOrderAt_ne_top_of_isPreconnected (convex_halfSpace_re_gt b).isPreconnected
      hρ (show (x:ℂ) ∈ U from hbx) hn) hbase
  have hh : deriv G =ᶠ[𝓝[≠] ρ] dividedPrimeCurrent :=
    (meromorphicOrderAt_eq_top_iff.mp hp).mono fun s hs => sub_eq_zero.mp hs
  exact meromorphic_deriv_order_ne_neg_one (hG ρ hρ) ((meromorphicOrderAt_congr hh).trans (dividedPrimeCurrent_pole hz))

private theorem exists_lastClass_euler_point {q : ℕ} [NeZero q] (hq : 2≤q) :
    ∃ x : ℝ, 2<x ∧ lastQuotientClassSymbol q x≠0 := by
  let c := fun n : ℕ => lastClassJumps (n : ZMod q)
  by_contra! h
  have he : (fun x : ℝ => LSeries c x) =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop (2:ℝ)] with x hx
    rw [← lastQuotientClassSymbol_eq_LSeries q (by simpa using (lt_trans (by norm_num : (1:ℝ)<2) hx))]
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

/-- Each single fixed width excludes every zero in a half-plane to which
its centered, divided-weight prime series extends meromorphically. -/
theorem lastClass_primePrimitive_continuation_excludes_zero {q : ℕ} [NeZero q] (hq : 2≤q)
    {b : ℝ} (hb : b<1) (H : ℂ → ℂ) (hH : MeromorphicOn H {s : ℂ | b<s.re})
    (he : ∀ s : ℂ, 2<s.re → H s = lastQuotientClassSymbol q s*_root_.RHTower.centeredPrimeTailEulerPrimitive s)
    {ρ : ℂ} (hρ : b<ρ.re) : riemannZeta ρ≠0 := by
  obtain ⟨x,hx,hD⟩ := exists_lastClass_euler_point hq
  have hx1 : 1<x := (by norm_num : (1:ℝ)<2).trans hx
  apply zeta_ne_zero_of_filtered_primePrimitive_continuation (hb.trans hx1) hx1
    (differentiable_lastQuotientClassSymbol q) hD hH _ hρ
  filter_upwards [(isOpen_lt continuous_const Complex.continuous_re).mem_nhds
    (show (x:ℂ) ∈ {s : ℂ | 2<s.re} from hx)] with s hs
  exact he s hs

#print axioms zeta_ne_zero_of_filtered_primePrimitive_continuation
#print axioms lastClass_primePrimitive_continuation_excludes_zero

end GaloisForLFunctions.ExceptionalLayerTheory
