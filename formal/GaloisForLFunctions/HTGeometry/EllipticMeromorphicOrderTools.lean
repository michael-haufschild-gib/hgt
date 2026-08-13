import GaloisForLFunctions.HTGeometry.EllipticLiouvilleFacetCodimension
import Mathlib.Analysis.Meromorphic.TrailingCoefficient
import Mathlib.Analysis.Meromorphic.NormalForm

/-!
# Leading-term tools for elliptic functions

Three facts about meromorphic functions on `ℂ` that the structure theorem for elliptic functions
needs.

* `meromorphicOrderAt_lt_sub_of_trailingCoeff_eq` — equal order and equal trailing coefficient make
  the difference of two meromorphic functions vanish to strictly higher order.  This is the step
  that lets a pole be cancelled by one explicit model function.
* `even_meromorphicOrderAt_of_neg_eq` — an even meromorphic function has even order at the origin:
  its leading Laurent exponent `n` satisfies `(-1)^n = 1`.
* `exists_const_eventuallyEq_of_lattice_periodic` — the meromorphic form of elliptic Liouville: a
  lattice-periodic meromorphic function with no poles agrees near every point with a constant.  The
  passage from the entire statement is through the canonical normal form, whose periodicity follows
  because two normal forms agreeing off a point agree at it.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Equal leading terms cancel.**  If two meromorphic functions have the same finite order and the
same trailing coefficient at a point, their difference vanishes there to strictly higher order. -/
theorem meromorphicOrderAt_lt_sub_of_trailingCoeff_eq {f g : ℂ → ℂ} {x : ℂ}
    (hf : MeromorphicAt f x) (hg : MeromorphicAt g x)
    (hne : meromorphicOrderAt f x ≠ ⊤)
    (hord : meromorphicOrderAt f x = meromorphicOrderAt g x)
    (htc : meromorphicTrailingCoeffAt f x = meromorphicTrailingCoeffAt g x) :
    meromorphicOrderAt f x < meromorphicOrderAt (fun z => f z - g z) x := by
  lift meromorphicOrderAt f x to ℤ using hne with n hn
  obtain ⟨a, ha, ha0, hae⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hn.symm
  obtain ⟨b, hb, hb0, hbe⟩ := (meromorphicOrderAt_eq_int_iff hg).1 hord.symm
  have hta : meromorphicTrailingCoeffAt f x = a x :=
    ha.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE ha0 hae
  have htb : meromorphicTrailingCoeffAt g x = b x :=
    hb.meromorphicTrailingCoeffAt_of_ne_zero_of_eq_nhdsNE hb0 hbe
  have hab : a x = b x := by rw [← hta, ← htb, htc]
  have hev : (fun z => f z - g z) =ᶠ[𝓝[≠] x] fun z => (z - x) ^ n * (a z - b z) := by
    filter_upwards [hae, hbe] with z hz1 hz2
    simp only [hz1, hz2, smul_eq_mul]
    ring
  rw [meromorphicOrderAt_congr hev]
  have hsub : AnalyticAt ℂ (fun z => a z - b z) x := ha.fun_sub hb
  have hzero : (fun z => a z - b z) x = 0 := by simp [hab]
  have hordsub : (1 : WithTop ℤ) ≤ meromorphicOrderAt (fun z => a z - b z) x := by
    rw [hsub.meromorphicOrderAt_eq]
    have hne0 : analyticOrderAt (fun z => a z - b z) x ≠ 0 := by
      rw [Ne, analyticOrderAt_eq_zero]
      simp only [not_or, not_not]
      exact ⟨hsub, hzero⟩
    have h1 : (1 : ℕ∞) ≤ analyticOrderAt (fun z => a z - b z) x :=
      Order.one_le_iff_ne_zero.mpr hne0
    have hmono : Monotone (ENat.map (Nat.cast : ℕ → ℤ)) := ENat.monotone_map_iff.mpr Nat.mono_cast
    simpa using hmono h1
  have hmpow : MeromorphicAt (fun z : ℂ => (z - x) ^ n) x :=
    ((by fun_prop : AnalyticAt ℂ (fun z : ℂ => z - x) x).meromorphicAt).zpow n
  rw [fun_meromorphicOrderAt_mul hmpow hsub.meromorphicAt,
    fun_meromorphicOrderAt_zpow_id_sub_const]
  have hstep : (n : WithTop ℤ) < (n : WithTop ℤ) + 1 := by
    have hc : ((n : WithTop ℤ) + 1) = ((n + 1 : ℤ) : WithTop ℤ) := by norm_cast
    rw [hc]
    exact_mod_cast (by omega : n < n + 1)
  calc (n : WithTop ℤ) < (n : WithTop ℤ) + 1 := hstep
    _ ≤ (n : WithTop ℤ) + meromorphicOrderAt (fun z => a z - b z) x := by gcongr

/-- Negation preserves the punctured neighbourhood filter of the origin. -/
theorem tendsto_neg_nhdsNE_zero :
    Tendsto (fun z : ℂ => -z) (𝓝[≠] (0 : ℂ)) (𝓝[≠] (0 : ℂ)) := by
  apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
  · simpa using ((by fun_prop : Continuous fun z : ℂ => -z).tendsto (0 : ℂ)).mono_left
      nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simpa using hz

/-- **An even meromorphic function has even order at the origin.**  Writing the function as
`z ^ n · a` with `a` analytic and nonzero at `0`, evenness forces `a 0 = (-1) ^ n · a 0`. -/
theorem even_meromorphicOrderAt_of_neg_eq {f : ℂ → ℂ} {n : ℤ}
    (hf : MeromorphicAt f 0) (heven : ∀ z, f (-z) = f z)
    (hn : meromorphicOrderAt f 0 = (n : WithTop ℤ)) : Even n := by
  obtain ⟨a, ha, ha0, hae⟩ := (meromorphicOrderAt_eq_int_iff hf).1 hn
  have haeneg : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), f (-z) = ((-z) - 0) ^ n • a (-z) :=
    tendsto_neg_nhdsNE_zero.eventually hae
  have hkey : ∀ᶠ z : ℂ in 𝓝[≠] (0 : ℂ), a z = (-1 : ℂ) ^ n * a (-z) := by
    filter_upwards [hae, haeneg, self_mem_nhdsWithin] with z hz1 hz2 hz3
    have hz0 : z ≠ 0 := hz3
    have hzn : (z : ℂ) ^ n ≠ 0 := zpow_ne_zero _ hz0
    have h1 : (z : ℂ) ^ n * a z = ((-1 : ℂ) ^ n * z ^ n) * a (-z) := by
      have e1 : f z = (z : ℂ) ^ n • a z := by simpa using hz1
      have e2 : f (-z) = ((-z : ℂ)) ^ n • a (-z) := by simpa using hz2
      have e3 : ((-z : ℂ)) ^ n = (-1 : ℂ) ^ n * z ^ n := by
        rw [← mul_zpow]
        ring_nf
      rw [smul_eq_mul] at e1 e2
      rw [← e1, ← heven z, e2, e3]
    field_simp at h1 ⊢
    linear_combination h1
  have hA : AnalyticAt ℂ (fun z : ℂ => (-1 : ℂ) ^ n * a (-z)) 0 := by
    have hneg0 : AnalyticAt ℂ a (-(0 : ℂ)) := by simpa using ha
    have hcomp : AnalyticAt ℂ (fun z : ℂ => a (-z)) 0 :=
      hneg0.comp (by fun_prop : AnalyticAt ℂ (fun z : ℂ => -z) 0)
    exact analyticAt_const.fun_mul hcomp
  have hlim1 : Tendsto a (𝓝[≠] (0 : ℂ)) (𝓝 (a 0)) := ha.continuousAt.continuousWithinAt
  have hlim2 : Tendsto (fun z : ℂ => (-1 : ℂ) ^ n * a (-z)) (𝓝[≠] (0 : ℂ))
      (𝓝 ((-1 : ℂ) ^ n * a (-0))) := hA.continuousAt.continuousWithinAt
  have heq : a 0 = (-1 : ℂ) ^ n * a (-0) :=
    tendsto_nhds_unique (hlim1.congr' hkey) hlim2
  rw [neg_zero] at heq
  have hmul : (-1 : ℂ) ^ n * a 0 = 1 * a 0 := by rw [one_mul, ← heq]
  have hone : (-1 : ℂ) ^ n = 1 := mul_right_cancel₀ ha0 hmul
  rcases Int.even_or_odd n with hev | hodd
  · exact hev
  · exfalso
    rw [hodd.neg_one_zpow] at hone
    exact absurd hone (by norm_num)

/-- **Elliptic Liouville, meromorphic form.**  A lattice-periodic meromorphic function without poles
agrees, near every point, with one constant. -/
theorem exists_const_eventuallyEq_of_lattice_periodic (L : PeriodPair) {f : ℂ → ℂ}
    (hf : ∀ z, MeromorphicAt f z)
    (hper : ∀ p ∈ L.lattice, Function.Periodic f p)
    (hord : ∀ z, 0 ≤ meromorphicOrderAt f z) :
    ∃ c : ℂ, ∀ z : ℂ, f =ᶠ[𝓝[≠] z] fun _ => c := by
  have hfOn : MeromorphicOn f Set.univ := fun z _ => hf z
  set F : ℂ → ℂ := toMeromorphicNFOn f Set.univ with hFdef
  have hFNF : MeromorphicNFOn F Set.univ := meromorphicNFOn_toMeromorphicNFOn f Set.univ
  have hFeq : ∀ z : ℂ, F =ᶠ[𝓝[≠] z] f := fun z =>
    hfOn.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
  have hFan : ∀ z : ℂ, AnalyticAt ℂ F z := by
    intro z
    refine (hFNF (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp ?_
    rw [meromorphicOrderAt_congr (hFeq z)]
    exact hord z
  have hFdiff : Differentiable ℂ F := fun z => (hFan z).differentiableAt
  have hFper : ∀ p ∈ L.lattice, Function.Periodic F p := by
    intro p hp z
    have htrans : Tendsto (fun w : ℂ => w + p) (𝓝[≠] z) (𝓝[≠] (z + p)) := by
      apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
      · exact ((by fun_prop : Continuous fun w : ℂ => w + p).tendsto z).mono_left
          nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with w hw
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        intro hcon
        exact hw (by simpa using add_right_cancel hcon)
    have h1 : (fun w : ℂ => F (w + p)) =ᶠ[𝓝[≠] z] fun w : ℂ => f (w + p) :=
      htrans.eventually (hFeq (z + p))
    have h2 : (fun w : ℂ => f (w + p)) = f := funext fun w => hper p hp w
    have h3 : (fun w : ℂ => F (w + p)) =ᶠ[𝓝[≠] z] F := by
      rw [h2] at h1
      exact h1.trans (hFeq z).symm
    have hNF1 : MeromorphicNFAt (fun w : ℂ => F (w + p)) z := by
      have hcomp : AnalyticAt ℂ (F ∘ fun w : ℂ => w + p) z :=
        AnalyticAt.comp (g := F) (f := fun w : ℂ => w + p) (x := z) (hFan (z + p)) (by fun_prop)
      exact hcomp.meromorphicNFAt
    have hNF2 : MeromorphicNFAt F z := (hFan z).meromorphicNFAt
    have h4 := (hNF1.eventuallyEq_nhdsNE_iff_eventuallyEq_nhds hNF2).mp h3
    exact h4.eq_of_nhds
  refine ⟨F 0, fun z => ?_⟩
  have hconst := const_of_lattice_periodic_differentiable L hFdiff hFper
  refine (hFeq z).symm.trans ?_
  filter_upwards with w
  exact hconst w 0

end GaloisForLFunctions.HTGeometry
