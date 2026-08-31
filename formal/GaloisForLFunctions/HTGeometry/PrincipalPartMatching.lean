import GaloisForLFunctions.HTGeometry.QuasiPeriodPoleRigidity
import GaloisForLFunctions.HTGeometry.EllipticThetaLogComparisonRigidity

/-!
# Matching principal parts and quasi-periodic normal forms

Two meromorphic functions with the same simple principal part at a point have a difference of
nonnegative order there.  A meromorphic function all of whose orders are nonnegative has an entire
canonical normal form, and punctured-neighbourhood period and constant-increment identities pass to
that normal form by continuity.  Together with the two-step rigidity this classifies a
one-pole quasi-elliptic increment up to an additive constant.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- A simple principal part with coefficient `r` at `q`. -/
def HasPrincipalPart (f : ℂ → ℂ) (q r : ℂ) : Prop :=
  ∃ g : ℂ → ℂ, AnalyticAt ℂ g q ∧ ∀ᶠ w in 𝓝[≠] q, f w = r * (w - q)⁻¹ + g w

/-- **Matching principal parts cancel.**  Two functions with the same simple principal part at `q`
have a difference of nonnegative order there. -/
theorem meromorphicOrderAt_sub_nonneg_of_principalPart {f h : ℂ → ℂ} {q r : ℂ}
    (hf : HasPrincipalPart f q r) (hh : HasPrincipalPart h q r) :
    0 ≤ meromorphicOrderAt (fun w => f w - h w) q := by
  obtain ⟨g₁, hg₁, hf'⟩ := hf
  obtain ⟨g₂, hg₂, hh'⟩ := hh
  have heq : (fun w => f w - h w) =ᶠ[𝓝[≠] q] (fun w => g₁ w - g₂ w) := by
    filter_upwards [hf', hh'] with w hw1 hw2
    rw [hw1, hw2]
    ring
  rw [meromorphicOrderAt_congr heq]
  exact (hg₁.sub hg₂).meromorphicOrderAt_nonneg

/-- **Constant increments pass to the canonical normal form.**  A punctured-neighbourhood
increment identity for a meromorphic function becomes a genuine increment identity for its entire
canonical normal form. -/
theorem constIncrement_toMeromorphicNFOn_of_eventually_punctured
    {f F : ℂ → ℂ} (hf : MeromorphicOn f Set.univ)
    (hFdef : F = toMeromorphicNFOn f Set.univ)
    (hFan : AnalyticOnNhd ℂ F Set.univ) (p c : ℂ)
    (hlocal : ∀ z, ∀ᶠ w in 𝓝[≠] z, f (w + p) = f w + c) :
    ∀ z, F (z + p) = F z + c := by
  intro z
  have hFz : F =ᶠ[𝓝[≠] z] f := by
    rw [hFdef]
    exact hf.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
  have hFzp : F =ᶠ[𝓝[≠] (z + p)] f := by
    rw [hFdef]
    exact hf.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ (z + p))
  have ht : Tendsto (fun w : ℂ => w + p) (𝓝[≠] z) (𝓝[≠] (z + p)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · exact (continuousAt_id.add continuousAt_const).tendsto.mono_left inf_le_left
    · filter_upwards [self_mem_nhdsWithin] with w hw
      simpa using hw
  have hshift : (fun w => F (w + p)) =ᶠ[𝓝[≠] z] (fun w => f (w + p)) :=
    ht.eventually hFzp
  have heq : (fun w => F (w + p)) =ᶠ[𝓝[≠] z] (fun w => F w + c) := by
    filter_upwards [hshift, hlocal z, hFz] with w h₁ h₂ h₃
    rw [h₁, h₂, ← h₃]
  have hcontF : ContinuousAt (fun w => F w + c) z :=
    ((hFan z (Set.mem_univ z)).continuousAt).add continuousAt_const
  have hcontShift : ContinuousAt (fun w => F (w + p)) z := by
    have hs : ContinuousAt (fun w : ℂ => w + p) z :=
      continuousAt_id.add continuousAt_const
    simpa only [Function.comp_def] using
      (hFan (z + p) (Set.mem_univ (z + p))).continuousAt.comp_of_eq hs rfl
  exact Filter.EventuallyEq.eq_of_nhds
    ((hcontShift.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hcontF).mp heq)

/-- **One-pole classification.**  A meromorphic function whose orders are everywhere nonnegative,
with punctured period one and a punctured constant `τ`-increment, has constant canonical normal
form and vanishing increment. -/
theorem const_of_nonneg_order_of_punctured_unit_period
    {τ : ℂ} (hτ : 0 < τ.im) {f : ℂ → ℂ} (hf : MeromorphicOn f Set.univ)
    (hord : ∀ z, 0 ≤ meromorphicOrderAt f z)
    (hper : ∀ z, ∀ᶠ w in 𝓝[≠] z, f (w + 1) = f w)
    {k : ℂ} (hinc : ∀ z, ∀ᶠ w in 𝓝[≠] z, f (w + τ) = f w + k) :
    (∀ x y, toMeromorphicNFOn f Set.univ x = toMeromorphicNFOn f Set.univ y) ∧ k = 0 := by
  set F : ℂ → ℂ := toMeromorphicNFOn f Set.univ with hFdef
  have hNF : MeromorphicNFOn F Set.univ := meromorphicNFOn_toMeromorphicNFOn f Set.univ
  have hordF : ∀ z, 0 ≤ meromorphicOrderAt F z := by
    intro z
    rw [hFdef, meromorphicOrderAt_toMeromorphicNFOn hf (Set.mem_univ z)]
    exact hord z
  have hFan : AnalyticOnNhd ℂ F Set.univ := by
    intro z _
    exact (hNF (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp (hordF z)
  have hperF : Function.Periodic F 1 := by
    intro z
    have h := constIncrement_toMeromorphicNFOn_of_eventually_punctured hf hFdef hFan 1 0
      (by intro z; filter_upwards [hper z] with w hw; rw [hw]; ring) z
    rw [h, add_zero]
  have hincF : ∀ z, F (z + τ) = F z + k :=
    constIncrement_toMeromorphicNFOn_of_eventually_punctured hf hFdef hFan τ k hinc
  exact const_of_nonneg_order_of_unit_period hτ hNF hordF hperF hincF

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

/-- **Same poles, same principal parts, no poles left.** -/
theorem nonneg_order_sub_of_matching_principal_parts {f h : ℂ → ℂ} (S : Set ℂ) (r : ℂ)
    (hfan : ∀ z ∉ S, AnalyticAt ℂ f z) (hhan : ∀ z ∉ S, AnalyticAt ℂ h z)
    (hfp : ∀ q ∈ S, HasPrincipalPart f q r) (hhp : ∀ q ∈ S, HasPrincipalPart h q r) :
    ∀ z, 0 ≤ meromorphicOrderAt (fun w => f w - h w) z := by
  intro z
  by_cases hz : z ∈ S
  · exact meromorphicOrderAt_sub_nonneg_of_principalPart (hfp z hz) (hhp z hz)
  · exact ((hfan z hz).sub (hhan z hz)).meromorphicOrderAt_nonneg

/-- A simple principal part makes the function meromorphic there. -/
theorem meromorphicAt_of_hasPrincipalPart {f : ℂ → ℂ} {q r : ℂ}
    (h : HasPrincipalPart f q r) : MeromorphicAt f q := by
  obtain ⟨g, hg, heq⟩ := h
  have hlin : AnalyticAt ℂ (fun w : ℂ => w - q) q := analyticAt_id.sub analyticAt_const
  have h1 : MeromorphicAt (fun w : ℂ => (w - q)⁻¹) q := (hlin.meromorphicAt).inv
  have h2 : MeromorphicAt (fun w : ℂ => r * (w - q)⁻¹) q :=
    (analyticAt_const.meromorphicAt).mul h1
  have hmero : MeromorphicAt (fun w : ℂ => r * (w - q)⁻¹ + g w) q := h2.add hg.meromorphicAt
  have heq' : f =ᶠ[𝓝[≠] q] (fun w : ℂ => r * (w - q)⁻¹ + g w) := heq
  exact hmero.congr heq'.symm

/-- Meromorphy of a function with prescribed pole set and principal parts. -/
theorem meromorphicOn_of_principal_parts {f : ℂ → ℂ} {S : Set ℂ} {r : ℂ}
    (hfan : ∀ z ∉ S, AnalyticAt ℂ f z) (hfp : ∀ q ∈ S, HasPrincipalPart f q r) :
    MeromorphicOn f Set.univ := by
  intro z _
  by_cases hz : z ∈ S
  · exact meromorphicAt_of_hasPrincipalPart (hfp z hz)
  · exact (hfan z hz).meromorphicAt

/-- **One-pole classification.**  Two meromorphic functions with the same pole set, the same simple
principal part at each pole, punctured period one and punctured constant `τ`-increments differ by a
constant, and their increments agree. -/
theorem const_sub_of_matching_principal_parts
    {τ : ℂ} (hτ : 0 < τ.im) {f h : ℂ → ℂ} (S : Set ℂ) (r : ℂ)
    (hfan : ∀ z ∉ S, AnalyticAt ℂ f z) (hhan : ∀ z ∉ S, AnalyticAt ℂ h z)
    (hfp : ∀ q ∈ S, HasPrincipalPart f q r) (hhp : ∀ q ∈ S, HasPrincipalPart h q r)
    (hperf : ∀ z, ∀ᶠ w in 𝓝[≠] z, f (w + 1) = f w)
    (hperh : ∀ z, ∀ᶠ w in 𝓝[≠] z, h (w + 1) = h w)
    {kf kh : ℂ}
    (hincf : ∀ z, ∀ᶠ w in 𝓝[≠] z, f (w + τ) = f w + kf)
    (hinch : ∀ z, ∀ᶠ w in 𝓝[≠] z, h (w + τ) = h w + kh) :
    (∀ x y, toMeromorphicNFOn (fun w => f w - h w) Set.univ x
      = toMeromorphicNFOn (fun w => f w - h w) Set.univ y) ∧ kf = kh := by
  have hfm : MeromorphicOn f Set.univ := meromorphicOn_of_principal_parts hfan hfp
  have hhm : MeromorphicOn h Set.univ := meromorphicOn_of_principal_parts hhan hhp
  have hdm : MeromorphicOn (fun w => f w - h w) Set.univ := fun z hz =>
    (hfm z hz).sub (hhm z hz)
  have hord := nonneg_order_sub_of_matching_principal_parts S r hfan hhan hfp hhp
  have hperd : ∀ z, ∀ᶠ w in 𝓝[≠] z, (f (w + 1) - h (w + 1)) = f w - h w := by
    intro z
    filter_upwards [hperf z, hperh z] with w h1 h2
    rw [h1, h2]
  have hincd : ∀ z, ∀ᶠ w in 𝓝[≠] z,
      (f (w + τ) - h (w + τ)) = (f w - h w) + (kf - kh) := by
    intro z
    filter_upwards [hincf z, hinch z] with w h1 h2
    rw [h1, h2]
    ring
  obtain ⟨hconst, hk⟩ :=
    const_of_nonneg_order_of_punctured_unit_period hτ hdm hord hperd hincd
  exact ⟨hconst, by linear_combination hk⟩

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

/-- At a simple zero the analytic order is one. -/
theorem analyticOrderAt_eq_one_of_simple_zero {θ : ℂ → ℂ} {q : ℂ}
    (hθ : AnalyticAt ℂ θ q) (h0 : θ q = 0) (h1 : deriv θ q ≠ 0) :
    analyticOrderAt θ q = 1 := by
  have hne : analyticOrderAt θ q ≠ ⊤ := by
    intro htop
    rw [analyticOrderAt_eq_top] at htop
    have hd : deriv θ q = 0 := by
      have : deriv θ =ᶠ[𝓝 q] deriv (fun _ : ℂ => (0 : ℂ)) :=
        Filter.EventuallyEq.deriv htop
      have := this.eq_of_nhds
      simpa using this
    exact h1 hd
  obtain ⟨u, hu, hu0, hfac⟩ := hθ.analyticOrderAt_ne_top.mp hne
  set m : ℕ := analyticOrderNatAt θ q with hm
  have hmne : m ≠ 0 := by
    intro hm0
    rw [hm0] at hfac
    have := hfac.eq_of_nhds
    simp only [pow_zero, one_smul] at this
    rw [h0] at this
    exact hu0 this.symm
  have hm1 : m = 1 := by
    by_contra hcon
    have hm2 : 2 ≤ m := by omega
    have hderiv : deriv θ q = 0 := by
      have hd : deriv θ q = deriv (fun z : ℂ => (z - q) ^ m • u z) q :=
        Filter.EventuallyEq.deriv_eq hfac
      rw [hd]
      have hp : HasDerivAt (fun z : ℂ => (z - q) ^ m) ((m : ℂ) * (q - q) ^ (m - 1) * 1) q :=
        ((hasDerivAt_id q).sub_const q).pow m
      have hprod : HasDerivAt (fun z : ℂ => (z - q) ^ m * u z)
          ((m : ℂ) * (q - q) ^ (m - 1) * 1 * u q + (q - q) ^ m * deriv u q) q :=
        hp.mul (hu.differentiableAt.hasDerivAt)
      have hsub : (q - q) = 0 := by ring
      have hm1' : m - 1 ≠ 0 := by omega
      simp only [hsub, zero_pow hm1', zero_pow hmne, mul_zero, zero_mul, add_zero] at hprod
      simpa only [smul_eq_mul] using hprod.deriv
    exact h1 hderiv
  rw [← Nat.cast_analyticOrderNatAt hne, ← hm, hm1]
  norm_num

/-- **The logarithmic derivative at a simple zero has principal part `1/(w - q)`.** -/
theorem hasPrincipalPart_logDeriv_of_simple_zero {θ : ℂ → ℂ} {q : ℂ}
    (hθ : AnalyticAt ℂ θ q) (h0 : θ q = 0) (h1 : deriv θ q ≠ 0) :
    HasPrincipalPart (fun w => deriv θ w / θ w) q 1 := by
  have hord := analyticOrderAt_eq_one_of_simple_zero hθ h0 h1
  obtain ⟨u, hu, hu0, hfac⟩ := (hθ.analyticOrderAt_eq_natCast (n := 1)).mp (by rw [hord]; norm_num)
  refine ⟨fun w => deriv u w / u w, (hu.deriv).div hu hu0, ?_⟩
  have hune : ∀ᶠ w in 𝓝 q, u w ≠ 0 := hu.continuousAt.eventually_ne hu0
  have hderiv : ∀ᶠ w in 𝓝 q, deriv θ w = u w + (w - q) * deriv u w := by
    have hfun : θ =ᶠ[𝓝 q] fun z : ℂ => (z - q) * u z := by
      filter_upwards [hfac] with z hz
      simpa using hz
    filter_upwards [hfun.eventually_nhds, hu.eventually_analyticAt] with w hw hwu
    have hd : deriv θ w = deriv (fun z : ℂ => (z - q) * u z) w :=
      Filter.EventuallyEq.deriv_eq hw
    rw [hd]
    have hp : HasDerivAt (fun z : ℂ => z - q) 1 w := (hasDerivAt_id w).sub_const q
    have hprod : HasDerivAt (fun z : ℂ => (z - q) * u z)
        (1 * u w + (w - q) * deriv u w) w := hp.mul (hwu.differentiableAt.hasDerivAt)
    rw [hprod.deriv]
    ring
  have hθval : ∀ᶠ w in 𝓝 q, θ w = (w - q) * u w := by
    filter_upwards [hfac] with z hz
    simpa using hz
  filter_upwards [hderiv.filter_mono nhdsWithin_le_nhds, hθval.filter_mono nhdsWithin_le_nhds,
    hune.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw1 hw2 hw3 hw4
  have hwq : w - q ≠ 0 := sub_ne_zero.mpr (by simpa using hw4)
  rw [hw1, hw2]
  field_simp

end GaloisForLFunctions.HTGeometry
