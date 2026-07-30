import GaloisForLFunctions.RHTower.SuzukiAnchoredEulerWronskian
import GaloisForLFunctions.RHTower.SuzukiCarlemanEvenPoleCarrier
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# Euler-defect pole rigidity for Suzuki's Carleman jump

Suzuki's finite Donoghue quotients and the admissible two-shift Carleman jump quotient have
different pole divisors, so direct equality of those functions is impossible at fixed aperture.
The degree-one Euler defect

`E[f](z) = z * f'(z) - f(z)`

is the correct escape-insensitive observable: it kills every linear Nevanlinna endpoint mode.
This module proves the complementary fact needed for a noncircular weld.  At every nonzero pole,
the Euler defect raises the pole degree by exactly one.  In particular every hypothetical
nonreal Xi zero gives the admissible sewn quotient a simple pole and its Euler defect a double
pole.  Therefore any source construction proving off-real analyticity of that defect proves RH.

The remaining open statement is source-side identification of a holomorphic Euler--Gamma defect,
not equality of incompatible finite and exterior quotients.  No positivity premise, RH assumption,
estimate, or numerical computation occurs here.
-/

open Complex Filter Set Topology WithTop

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## A meromorphic Euler defect makes every nonzero pole worse -/

/-- At a nonzero pole, the degree-one Euler defect has exactly one more pole degree.

If `f(w)=(w-z)^n g(w)` with `n<0` and `g(z)≠0`, then

`w*f'(w)-f(w)=(w-z)^(n-1) G(w)`

and `G(z)=z*n*g(z)≠0`.  The exclusion of `z=0` is sharp: the Euler vector field vanishes at the
origin and can preserve, rather than raise, its pole order there. -/
theorem meromorphicOrderAt_suzukiEulerDefect_eq_sub_one
    {f : ℂ → ℂ} {z : ℂ} {n : ℤ}
    (hf : MeromorphicAt f z) (hz : z ≠ 0)
    (hn : n < 0) (horder : meromorphicOrderAt f z = (n : WithTop ℤ)) :
    meromorphicOrderAt (suzukiEulerDefect f) z = ((n - 1 : ℤ) : WithTop ℤ) := by
  obtain ⟨g, hg, hg0, hfg⟩ := (meromorphicOrderAt_eq_int_iff hf).mp horder
  let G : ℂ → ℂ := fun w =>
    w * ((n : ℂ) * g w + (w - z) * deriv g w) - (w - z) * g w
  have hG : AnalyticAt ℂ G z := by
    dsimp only [G]
    fun_prop
  have hn0 : (n : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_lt hn)
  have hG0 : G z ≠ 0 := by
    dsimp only [G]
    simpa only [sub_self, zero_mul, add_zero, sub_zero, mul_assoc] using
      (mul_ne_zero (mul_ne_zero hz hn0) hg0)
  have hfg' : f =ᶠ[𝓝[≠] z] fun w => (w - z) ^ n * g w := by
    filter_upwards [hfg] with w hw
    simpa only [smul_eq_mul] using hw
  have hfactorDeriv :
      deriv (fun w : ℂ => (w - z) ^ n * g w) =ᶠ[𝓝[≠] z]
        fun w => (n : ℂ) * (w - z) ^ (n - 1) * g w +
          (w - z) ^ n * deriv g w := by
    filter_upwards [eventually_nhdsWithin_of_eventually_nhds hg.eventually_analyticAt,
      self_mem_nhdsWithin] with w hgw hw
    have hw0 : w - z ≠ 0 := sub_ne_zero.mpr hw
    have hpow : HasDerivAt (fun u : ℂ => (u - z) ^ n)
        ((n : ℂ) * (w - z) ^ (n - 1)) w := by
      have hraw := (hasDerivAt_zpow n (w - z) (Or.inl hw0)).comp w
        ((hasDerivAt_id w).sub_const z)
      have hraw' := hraw.congr_deriv
        (g' := (n : ℂ) * (w - z) ^ (n - 1)) (by ring)
      exact hraw'.congr_of_eventuallyEq
        (Eventually.of_forall fun _ => rfl)
    exact (hpow.mul hgw.differentiableAt.hasDerivAt).deriv
  have hEeq : suzukiEulerDefect f =ᶠ[𝓝[≠] z]
      fun w => (w - z) ^ (n - 1) * G w := by
    have hderiv := Filter.EventuallyEq.nhdsNE_deriv hfg'
    filter_upwards [hfg', hderiv, hfactorDeriv, self_mem_nhdsWithin]
      with w hfw hdf hfac hw
    have hw0 : w - z ≠ 0 := sub_ne_zero.mpr hw
    have hpown : (w - z) ^ n = (w - z) ^ (n - 1) * (w - z) := by
      rw [← zpow_add_one₀ hw0 (n - 1), sub_add_cancel]
    rw [suzukiEulerDefect, hfw, hdf, hfac, hpown]
    dsimp only [G]
    ring
  have hE : MeromorphicAt (suzukiEulerDefect f) z := by
    exact ((MeromorphicAt.id z).mul hf.deriv).sub hf
  apply (meromorphicOrderAt_eq_int_iff hE).mpr
  exact ⟨G, hG, hG0, hEeq⟩

/-- **Meromorphic germ weld.** On a preconnected domain, one local pointed-germ identification
between a meromorphic target and an analytic source propagates meromorphically through the whole
domain.  Consequently the target has nonnegative order everywhere, even if its chosen totalized
values at isolated points are not continuous. -/
theorem meromorphicOrderAt_nonneg_of_analytic_source_germ_weld
    {f D : ℂ → ℂ} {U : Set ℂ} {u : ℂ}
    (hf : MeromorphicOn f U)
    (hD : AnalyticOnNhd ℂ D U)
    (hU : IsPreconnected U) (hu : u ∈ U)
    (hseed : f =ᶠ[𝓝[≠] u] D) :
    ∀ z ∈ U, (0 : WithTop ℤ) ≤ meromorphicOrderAt f z := by
  have hsub : MeromorphicOn (f - D) U := hf.sub hD.meromorphicOn
  have htopu : meromorphicOrderAt (f - D) u = ⊤ := by
    rw [meromorphicOrderAt_eq_top_iff]
    filter_upwards [hseed] with z hz
    exact sub_eq_zero.mpr hz
  let S : Set U := {x | meromorphicOrderAt (f - D) x = ⊤}
  have hSclopen : IsClopen S := hsub.isClopen_setOf_meromorphicOrderAt_eq_top
  letI : PreconnectedSpace U := isPreconnected_iff_preconnectedSpace.mp hU
  have hSne : S ≠ ∅ := by
    intro hS
    have huS : (⟨u, hu⟩ : U) ∈ S := htopu
    rw [hS] at huS
    exact huS
  have hSuniv : S = Set.univ :=
    (isClopen_iff.mp hSclopen).resolve_left hSne
  intro z hz
  have htopz : meromorphicOrderAt (f - D) z = ⊤ := by
    have hzS : (⟨z, hz⟩ : U) ∈ S := by rw [hSuniv]; trivial
    exact hzS
  have heq : f =ᶠ[𝓝[≠] z] D := by
    rw [eventuallyEq_iff_sub]
    exact meromorphicOrderAt_eq_top_iff.mp htopz
  rw [meromorphicOrderAt_congr heq]
  exact (hD z hz).meromorphicOrderAt_nonneg

end GaloisForLFunctions.RHTower

namespace RHTower

/-! ## Exact pole amplification for the admissible Carleman jump -/

/-- Every Xi zero away from the sewn source divisor is a simple pole of the admissible exterior
Weyl quotient.  This order statement complements its already-formalized universal trailing
coefficient. -/
theorem meromorphicOrderAt_suzukiAffineSewnExteriorWeylQuotient_eq_neg_one
    {alpha beta : ℂ}
    {WAlpha WBeta rightAlpha rightBeta : ℂ → ℂ} {z : ℂ}
    (hz : XiC z = 0)
    (hWAlpha : ∀ w, AnalyticAt ℂ WAlpha w)
    (hWBeta : ∀ w, AnalyticAt ℂ WBeta w)
    (hP0 : suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta z ≠ 0)
    (hRAlpha : ∀ w, AnalyticAt ℂ rightAlpha w)
    (hRBeta : ∀ w, AnalyticAt ℂ rightBeta w) :
    meromorphicOrderAt
        (suzukiAffineSewnExteriorWeylQuotient alpha beta
          WAlpha WBeta rightAlpha rightBeta) z =
      ((-1 : ℤ) : WithTop ℤ) := by
  let P : ℂ → ℂ := suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta
  let right : ℂ → ℂ :=
    suzukiAffineSewnIntervalPart alpha beta 0 WAlpha WBeta rightAlpha rightBeta
  let C : ℂ → ℂ :=
    suzukiOddCarlemanPoleCarrier (suzukiShiftedXiMultiplier 0) P right
  have hP : AnalyticAt ℂ P z :=
    analyticAt_suzukiAffineSewnCharacteristic (hWAlpha z) (hWBeta z)
  have hright : ∀ w, AnalyticAt ℂ right w := fun w =>
    analyticAt_suzukiAffineSewnIntervalPart
      (hWAlpha w) (hWBeta w) (hRAlpha w) (hRBeta w)
  have hodd : AnalyticAt ℂ (suzukiReflectionOddPart right) z :=
    analyticAt_suzukiReflectionOddPart hright z
  have hC : MeromorphicAt C z :=
    ((meromorphicAt_suzukiShiftedXiMultiplier 0 z).mul hP.meromorphicAt).sub
      hodd.meromorphicAt
  have hCorder : meromorphicOrderAt C z = ((-1 : ℤ) : WithTop ℤ) := by
    change meromorphicOrderAt
      (suzukiExteriorRemainder 0 P (suzukiReflectionOddPart right)) z = _
    exact meromorphicOrderAt_suzukiExteriorRemainder_eq_neg_one hz hP hP0 hodd
  have hPorder : meromorphicOrderAt P z = 0 := by
    rw [hP.meromorphicOrderAt_eq, hP.analyticOrderAt_eq_zero.mpr hP0]
    simp
  have hfun :
      suzukiAffineSewnExteriorWeylQuotient alpha beta
          WAlpha WBeta rightAlpha rightBeta =
        fun w => -(C w / P w) := by
    funext w
    simp only [suzukiAffineSewnExteriorWeylQuotient,
      suzukiAffineSewnOddCarlemanPoleCarrier, suzukiExteriorWeylQuotient,
      C, P, right, div_eq_mul_inv]
    ring
  rw [hfun, ← meromorphicOrderAt_fun_neg]
  rw [fun_meromorphicOrderAt_div hC hP.meromorphicAt, hCorder, hPorder]
  norm_num

/-- At every nonreal Xi zero, the admissible exterior quotient's Euler defect has an exact double
pole.  The Euler transform removes linear endpoint escape but cannot remove the Xi divisor. -/
theorem meromorphicOrderAt_suzukiEulerDefect_affineSewnExteriorWeylQuotient_eq_neg_two
    {alpha beta : ℂ}
    {WAlpha WBeta rightAlpha rightBeta : ℂ → ℂ} {z : ℂ}
    (hz : XiC z = 0)
    (hWAlpha : ∀ w, AnalyticAt ℂ WAlpha w)
    (hWBeta : ∀ w, AnalyticAt ℂ WBeta w)
    (hP0 : suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta z ≠ 0)
    (hRAlpha : ∀ w, AnalyticAt ℂ rightAlpha w)
    (hRBeta : ∀ w, AnalyticAt ℂ rightBeta w) :
    meromorphicOrderAt
        (GaloisForLFunctions.RHTower.suzukiEulerDefect
          (suzukiAffineSewnExteriorWeylQuotient alpha beta
            WAlpha WBeta rightAlpha rightBeta)) z =
      ((-2 : ℤ) : WithTop ℤ) := by
  let m : ℂ → ℂ :=
    suzukiAffineSewnExteriorWeylQuotient alpha beta
      WAlpha WBeta rightAlpha rightBeta
  have hmOrder : meromorphicOrderAt m z = ((-1 : ℤ) : WithTop ℤ) :=
    meromorphicOrderAt_suzukiAffineSewnExteriorWeylQuotient_eq_neg_one
      hz hWAlpha hWBeta hP0 hRAlpha hRBeta
  have hm : MeromorphicAt m z := by
    apply meromorphicAt_of_meromorphicOrderAt_ne_zero
    rw [hmOrder]
    norm_num
  simpa using
    (GaloisForLFunctions.RHTower.meromorphicOrderAt_suzukiEulerDefect_eq_sub_one
      hm hz0 (show (-1 : ℤ) < 0 by omega) hmOrder)
  where
    hz0 : z ≠ 0 := by
      intro h
      subst z
      exact XiC_zero_ne hz

/-! ## The source-side Euler weld is sufficient for RH -/

/-- **Euler-defect weld capstone.** If the actual admissible sewn Carleman quotient has a
holomorphic Euler defect at every nonreal point, then RH follows.  This premise is compatible with
finite Donoghue limits acquiring an arbitrary linear endpoint mode: the Euler defect annihilates
that mode.  It does not assume differentiability of the quotient at a possible pole. -/
theorem riemannHypothesis_of_suzukiAffineSewnExteriorWeylEulerDefect_analytic_offReal
    {alpha beta : ℂ}
    {WAlpha WBeta rightAlpha rightBeta : ℂ → ℂ}
    (hab : alpha ≠ beta)
    (hWAlpha : ∀ w, AnalyticAt ℂ WAlpha w)
    (hWBeta : ∀ w, AnalyticAt ℂ WBeta w)
    (hRAlpha : ∀ w, AnalyticAt ℂ rightAlpha w)
    (hRBeta : ∀ w, AnalyticAt ℂ rightBeta w)
    (hrealAlpha : ∀ z, WAlpha z = 0 → z.im = 0)
    (hrealBeta : ∀ z, WBeta z = 0 → z.im = 0)
    (hdefect : ∀ z : ℂ, z.im ≠ 0 →
      AnalyticAt ℂ
        (GaloisForLFunctions.RHTower.suzukiEulerDefect
          (suzukiAffineSewnExteriorWeylQuotient alpha beta
            WAlpha WBeta rightAlpha rightBeta)) z) :
    RiemannHypothesis := by
  rw [SlabMassSquareCertificate.riemannHypothesis_iff_xiC_zero_im_eq_zero]
  intro z hzXi
  by_contra him
  have hWAlpha0 : WAlpha z ≠ 0 := fun h => him (hrealAlpha z h)
  have hWBeta0 : WBeta z ≠ 0 := fun h => him (hrealBeta z h)
  have hP0 : suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta z ≠ 0 :=
    mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab.symm) hWAlpha0) hWBeta0
  have hEOrder :=
    meromorphicOrderAt_suzukiEulerDefect_affineSewnExteriorWeylQuotient_eq_neg_two
      hzXi hWAlpha hWBeta hP0 hRAlpha hRBeta
  have hnonneg : (0 : WithTop ℤ) ≤
      meromorphicOrderAt
        (GaloisForLFunctions.RHTower.suzukiEulerDefect
          (suzukiAffineSewnExteriorWeylQuotient alpha beta
            WAlpha WBeta rightAlpha rightBeta)) z :=
    (hdefect z him).meromorphicOrderAt_nonneg
  rw [hEOrder] at hnonneg
  have hnot : ¬(0 : WithTop ℤ) ≤ ((-2 : ℤ) : WithTop ℤ) := by
    exact_mod_cast (show ¬(0 : ℤ) ≤ -2 by omega)
  exact hnot hnonneg

/-- **Source-germ Euler weld capstone.** It is enough to construct one function `D`, analytic on
the upper half-plane, whose pointed germ at one upper point equals the Euler defect of the actual
admissible sewn Carleman quotient.  Meromorphic identity propagation then rules out the exact
double pole forced by every hypothetical upper Xi zero; centered Xi symmetry excludes lower
zeros.  This is the formal shape of the Euler--Gamma source theorem still required for RH. -/
theorem riemannHypothesis_of_suzukiAffineSewnExteriorWeylEulerDefect_source_germ_weld
    {alpha beta : ℂ}
    {WAlpha WBeta rightAlpha rightBeta D : ℂ → ℂ} {u : ℂ}
    (hab : alpha ≠ beta)
    (hWAlpha : ∀ w, AnalyticAt ℂ WAlpha w)
    (hWBeta : ∀ w, AnalyticAt ℂ WBeta w)
    (hRAlpha : ∀ w, AnalyticAt ℂ rightAlpha w)
    (hRBeta : ∀ w, AnalyticAt ℂ rightBeta w)
    (hrealAlpha : ∀ z, WAlpha z = 0 → z.im = 0)
    (hrealBeta : ∀ z, WBeta z = 0 → z.im = 0)
    (hD : AnalyticOnNhd ℂ D UpperHalfPlane.upperHalfPlaneSet)
    (hu : u ∈ UpperHalfPlane.upperHalfPlaneSet)
    (hseed :
      GaloisForLFunctions.RHTower.suzukiEulerDefect
          (suzukiAffineSewnExteriorWeylQuotient alpha beta
            WAlpha WBeta rightAlpha rightBeta) =ᶠ[𝓝[≠] u] D) :
    RiemannHypothesis := by
  let P : ℂ → ℂ := suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta
  let right : ℂ → ℂ :=
    suzukiAffineSewnIntervalPart alpha beta 0 WAlpha WBeta rightAlpha rightBeta
  let C : ℂ → ℂ :=
    suzukiOddCarlemanPoleCarrier (suzukiShiftedXiMultiplier 0) P right
  let m : ℂ → ℂ :=
    suzukiAffineSewnExteriorWeylQuotient alpha beta
      WAlpha WBeta rightAlpha rightBeta
  have hP : ∀ z, AnalyticAt ℂ P z := fun z =>
    analyticAt_suzukiAffineSewnCharacteristic (hWAlpha z) (hWBeta z)
  have hright : ∀ z, AnalyticAt ℂ right z := fun z =>
    analyticAt_suzukiAffineSewnIntervalPart
      (hWAlpha z) (hWBeta z) (hRAlpha z) (hRBeta z)
  have hodd : ∀ z, AnalyticAt ℂ (suzukiReflectionOddPart right) z := fun z =>
    analyticAt_suzukiReflectionOddPart hright z
  have hC : Meromorphic C := fun z =>
    ((meromorphicAt_suzukiShiftedXiMultiplier 0 z).mul (hP z).meromorphicAt).sub
      (hodd z).meromorphicAt
  have hfun : m = fun z => -(C z / P z) := by
    funext z
    simp only [m, suzukiAffineSewnExteriorWeylQuotient,
      suzukiAffineSewnOddCarlemanPoleCarrier, suzukiExteriorWeylQuotient,
      C, P, right, div_eq_mul_inv]
    ring
  have hm : Meromorphic m := by
    rw [hfun]
    exact (hC.div fun z => (hP z).meromorphicAt).neg
  have hE : MeromorphicOn
      (GaloisForLFunctions.RHTower.suzukiEulerDefect m)
      UpperHalfPlane.upperHalfPlaneSet := by
    intro z _hz
    exact ((MeromorphicAt.id z).mul (hm z).deriv).sub (hm z)
  have hnonneg :=
    GaloisForLFunctions.RHTower.meromorphicOrderAt_nonneg_of_analytic_source_germ_weld
      hE hD (convex_halfSpace_im_gt 0).isPreconnected hu (by simpa [m] using hseed)
  have hnoUpper : ∀ z : ℂ, 0 < z.im → XiC z ≠ 0 := by
    intro z hzIm hzXi
    have hWAlpha0 : WAlpha z ≠ 0 := fun h => (ne_of_gt hzIm) (hrealAlpha z h)
    have hWBeta0 : WBeta z ≠ 0 := fun h => (ne_of_gt hzIm) (hrealBeta z h)
    have hP0 : suzukiAffineSewnCharacteristic alpha beta WAlpha WBeta z ≠ 0 :=
      mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr hab.symm) hWAlpha0) hWBeta0
    have hEOrder :=
      meromorphicOrderAt_suzukiEulerDefect_affineSewnExteriorWeylQuotient_eq_neg_two
        hzXi hWAlpha hWBeta hP0 hRAlpha hRBeta
    have hpos : z ∈ UpperHalfPlane.upperHalfPlaneSet := by
      simpa [UpperHalfPlane.upperHalfPlaneSet] using hzIm
    have hn := hnonneg z hpos
    rw [hEOrder] at hn
    have hnot : ¬(0 : WithTop ℤ) ≤ ((-2 : ℤ) : WithTop ℤ) := by
      exact_mod_cast (show ¬(0 : ℤ) ≤ -2 by omega)
    exact hnot hn
  rw [SlabMassSquareCertificate.riemannHypothesis_iff_xiC_zero_im_eq_zero]
  intro z hzXi
  by_contra hzIm
  rcases lt_or_gt_of_ne hzIm with hzNeg | hzPos
  · have hnegZero : XiC (-z) = 0 := by simpa [XiC_even] using hzXi
    exact hnoUpper (-z) (by simpa using neg_pos.mpr hzNeg) hnegZero
  · exact hnoUpper z hzPos hzXi

end RHTower
