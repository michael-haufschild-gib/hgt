import GaloisForLFunctions.HTGeometry.MeromorphicNormalFormJetBridge

/-!
# Realizing a meromorphic germ by a function

A function is *realized* by a germ of the global meromorphic field when it agrees, off the zeros of
the denominator, with a fraction of entire representatives of that germ.  Realization is compatible
with sums and constant multiples by ordinary fraction arithmetic, and it transports differential
algebraicity in both directions through the two jet bridges.

This is the dictionary that turns the field-theoretic closure of differentially algebraic germs into
a closure statement about functions: a finite combination of realized functions is realized by the
corresponding combination of germs, so if each is differentially algebraic then so is the
combination.

* `toMeromorphicNFOn_congr` — the normal form depends only on the punctured germs;
* `RealizesMero`, `realizesMero_add`, `realizesMero_const_mul`, `realizesMero_sum`;
* `differentialAlgebraicOver_of_realizesMero`, `differentiallyAlgebraic_of_realizesMero`.
-/

open Filter Set Topology
open scoped Differential

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero

/-- **The normal form depends only on the punctured germs.** -/
theorem toMeromorphicNFOn_congr {f g : ℂ → ℂ} (hf : MeromorphicOn f (Set.univ : Set ℂ))
    (hg : MeromorphicOn g (Set.univ : Set ℂ)) (h : ∀ z, f =ᶠ[𝓝[≠] z] g) :
    toMeromorphicNFOn f (Set.univ : Set ℂ) = toMeromorphicNFOn g (Set.univ : Set ℂ) := by
  funext z
  set F : ℂ → ℂ := toMeromorphicNFOn f (Set.univ : Set ℂ) with hFdef
  set G : ℂ → ℂ := toMeromorphicNFOn g (Set.univ : Set ℂ) with hGdef
  have hFf : F =ᶠ[𝓝[≠] z] f := hf.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
  have hGg : G =ᶠ[𝓝[≠] z] g := hg.toMeromorphicNFOn_eq_self_on_nhdsNE (Set.mem_univ z)
  have hFG : F =ᶠ[𝓝[≠] z] G := (hFf.trans (h z)).trans hGg.symm
  have hNFF : MeromorphicNFOn F (Set.univ : Set ℂ) := meromorphicNFOn_toMeromorphicNFOn _ _
  have hNFG : MeromorphicNFOn G (Set.univ : Set ℂ) := meromorphicNFOn_toMeromorphicNFOn _ _
  have hord : meromorphicOrderAt F z = meromorphicOrderAt G z := meromorphicOrderAt_congr hFG
  rcases le_or_gt 0 (meromorphicOrderAt F z) with hge | hlt
  · have hFan := (hNFF (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp hge
    have hGan := (hNFG (Set.mem_univ z)).meromorphicOrderAt_nonneg_iff_analyticAt.mp (hord ▸ hge)
    exact (eventuallyEq_nhds_of_nhdsNE_of_continuousAt hFG hFan.continuousAt
      hGan.continuousAt).eq_of_nhds
  · rw [eq_zero_of_meromorphicOrderAt_neg (hNFF (Set.mem_univ z)) hlt,
      eq_zero_of_meromorphicOrderAt_neg (hNFG (Set.mem_univ z)) (hord ▸ hlt)]

/-- **The zeros of an entire function with a nonzero germ are isolated.** -/
theorem eventually_nhdsNE_ne_zero_of_germ_ne_zero {b : analyticSubring (Set.univ : Set ℂ)}
    (hb0 : b ≠ 0) {B : ℂ → ℂ} (hB : AnalyticOnNhd ℂ B (Set.univ : Set ℂ))
    (hBb : Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) B = (b : Germ (𝓟 Set.univ) ℂ)) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, B w ≠ 0 := by
  rcases (hB z (Set.mem_univ z)).eventually_eq_zero_or_eventually_ne_zero with hzero | hne
  · exfalso
    have hEq : Set.EqOn B 0 (Set.univ : Set ℂ) :=
      hB.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ z) hzero
    refine hb0 (Subtype.ext ?_)
    rw [← hBb]
    change ((B : ℂ → ℂ) : Germ (𝓟 (Set.univ : Set ℂ)) ℂ) = ((0 : analyticSubring Set.univ) : _)
    rw [ZeroMemClass.coe_zero, ← Germ.coe_zero, Germ.coe_eq]
    exact eventually_principal.mpr fun w _ ↦ hEq (Set.mem_univ w)
  · exact hne

/-- **A function realized by a germ.**  It agrees, off the zeros of the denominator, with a
fraction of entire representatives of the germ. -/
def RealizesMero (x : meroField (Set.univ : Set ℂ)) (f : ℂ → ℂ) : Prop :=
  ∃ (a b : analyticSubring (Set.univ : Set ℂ)) (A B : ℂ → ℂ),
    b ≠ 0 ∧ AnalyticOnNhd ℂ A (Set.univ : Set ℂ) ∧ AnalyticOnNhd ℂ B (Set.univ : Set ℂ) ∧
      Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) A = (a : Germ (𝓟 Set.univ) ℂ) ∧
      Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) B = (b : Germ (𝓟 Set.univ) ℂ) ∧
      x = algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) a /
        algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) b ∧
      ∀ z, B z ≠ 0 → f z = A z / B z

/-- A function agreeing with a fraction of entire functions off the zeros of the denominator is
meromorphic. -/
theorem meromorphicOn_of_fraction {f A B : ℂ → ℂ} {b : analyticSubring (Set.univ : Set ℂ)}
    (hb0 : b ≠ 0) (hA : AnalyticOnNhd ℂ A (Set.univ : Set ℂ))
    (hB : AnalyticOnNhd ℂ B (Set.univ : Set ℂ))
    (hBb : Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) B = (b : Germ (𝓟 Set.univ) ℂ))
    (hfAB : ∀ z, B z ≠ 0 → f z = A z / B z) :
    MeromorphicOn f (Set.univ : Set ℂ) := by
  intro z _
  have hpunct : f =ᶠ[𝓝[≠] z] fun w ↦ A w / B w := by
    filter_upwards [eventually_nhdsNE_ne_zero_of_germ_ne_zero hb0 hB hBb z] with w hw
    exact hfAB w hw
  exact ((hA.meromorphicOn.div hB.meromorphicOn) z (Set.mem_univ z)).congr hpunct.symm

/-- A realized function is meromorphic. -/
theorem meromorphicOn_of_realizesMero {x : meroField (Set.univ : Set ℂ)} {f : ℂ → ℂ}
    (h : RealizesMero x f) : MeromorphicOn f (Set.univ : Set ℂ) := by
  obtain ⟨_, _, A, B, hb0, hA, hB, _, hBb, _, hfAB⟩ := h
  exact meromorphicOn_of_fraction hb0 hA hB hBb hfAB

/-- A realized function has the same normal form as its fraction. -/
theorem toMeromorphicNFOn_eq_of_fraction {f A B : ℂ → ℂ} {b : analyticSubring (Set.univ : Set ℂ)}
    (hb0 : b ≠ 0) (hA : AnalyticOnNhd ℂ A (Set.univ : Set ℂ))
    (hB : AnalyticOnNhd ℂ B (Set.univ : Set ℂ))
    (hBb : Germ.coeRingHom (𝓟 (Set.univ : Set ℂ)) B = (b : Germ (𝓟 Set.univ) ℂ))
    (hfAB : ∀ z, B z ≠ 0 → f z = A z / B z) :
    toMeromorphicNFOn f (Set.univ : Set ℂ)
      = toMeromorphicNFOn (fun z ↦ A z / B z) (Set.univ : Set ℂ) := by
  refine toMeromorphicNFOn_congr (meromorphicOn_of_fraction hb0 hA hB hBb hfAB)
    (hA.meromorphicOn.div hB.meromorphicOn) fun z ↦ ?_
  filter_upwards [eventually_nhdsNE_ne_zero_of_germ_ne_zero hb0 hB hBb z] with w hw
  exact hfAB w hw

/-- **Realization transports differential algebraicity to the germ.** -/
theorem differentialAlgebraicOver_of_realizesMero {x : meroField (Set.univ : Set ℂ)} {f : ℂ → ℂ}
    (h : RealizesMero x f)
    (hDA : DifferentiallyAlgebraic (toMeromorphicNFOn f (Set.univ : Set ℂ))) :
    DifferentialAlgebraicOver (RatFunc ℂ) x := by
  obtain ⟨a, b, A, B, hb0, hA, hB, hAa, hBb, hxab, hfAB⟩ := h
  rw [hxab]
  refine differentialAlgebraicOver_of_differentiallyAlgebraic_toMeromorphicNFOn hb0 hA hB hAa hBb ?_
  rwa [← toMeromorphicNFOn_eq_of_fraction hb0 hA hB hBb hfAB]

theorem algebraMap_analyticSubring_ne_zero {b : analyticSubring (Set.univ : Set ℂ)} (hb0 : b ≠ 0) :
    algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ) b ≠ 0 := fun h ↦
  hb0 (IsFractionRing.injective (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
    (by rw [h, map_zero]))

/-- The zero function realizes the zero germ. -/
theorem realizesMero_zero : RealizesMero (0 : meroField (Set.univ : Set ℂ)) (0 : ℂ → ℂ) := by
  refine ⟨0, 1, 0, 1, one_ne_zero, analyticOnNhd_const, analyticOnNhd_const, map_zero _,
    map_one _, ?_, fun z _ ↦ ?_⟩
  · rw [map_zero, zero_div]
  · simp

/-- **Sums of realized functions are realized by sums of germs.** -/
theorem realizesMero_add {x y : meroField (Set.univ : Set ℂ)} {f g : ℂ → ℂ}
    (hx : RealizesMero x f) (hy : RealizesMero y g) :
    RealizesMero (x + y) (f + g) := by
  obtain ⟨a, b, A, B, hb0, hA, hB, hAa, hBb, hxab, hfAB⟩ := hx
  obtain ⟨c, d, C, D, hd0, hC, hD, hCc, hDd, hycd, hgCD⟩ := hy
  refine ⟨a * d + b * c, b * d, A * D + B * C, B * D, mul_ne_zero hb0 hd0,
    (hA.mul hD).add (hB.mul hC), hB.mul hD, ?_, ?_, ?_, fun z hz ↦ ?_⟩
  · rw [map_add, map_mul, map_mul, hAa, hDd, hCc, hBb]
    push_cast
    ring
  · rw [map_mul, hBb, hDd]
    push_cast
    ring
  · rw [hxab, hycd]
    simp only [map_add, map_mul]
    rw [div_add_div _ _ (algebraMap_analyticSubring_ne_zero hb0)
      (algebraMap_analyticSubring_ne_zero hd0)]
  · have hBz : B z ≠ 0 := fun h ↦ hz (by simp [Pi.mul_apply, h])
    have hDz : D z ≠ 0 := fun h ↦ hz (by simp [Pi.mul_apply, h])
    have hfz := hfAB z hBz
    have hgz := hgCD z hDz
    simp only [Pi.add_apply, Pi.mul_apply, hfz, hgz]
    field_simp

/-- **Constant multiples of realized functions are realized.** -/
theorem realizesMero_const_mul (c : ℂ) {x : meroField (Set.univ : Set ℂ)} {f : ℂ → ℂ}
    (hx : RealizesMero x f) :
    RealizesMero (algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField Set.univ)
      (constToAnalytic Set.univ c) * x) (fun z ↦ c * f z) := by
  obtain ⟨a, b, A, B, hb0, hA, hB, hAa, hBb, hxab, hfAB⟩ := hx
  refine ⟨constToAnalytic Set.univ c * a, b, (fun _ : ℂ ↦ c) * A, B, hb0,
    analyticOnNhd_const.mul hA, hB, ?_, hBb, ?_, fun z hz ↦ ?_⟩
  · rw [map_mul, hAa]
    rfl
  · rw [hxab, map_mul, mul_div_assoc]
  · show c * f z = ((fun _ : ℂ ↦ c) * A) z / B z
    rw [hfAB z hz, Pi.mul_apply, mul_div_assoc]

/-- **Finite sums of realized functions are realized.** -/
theorem realizesMero_sum {ι : Type*} (s : Finset ι) (x : ι → meroField (Set.univ : Set ℂ))
    (f : ι → ℂ → ℂ) (h : ∀ i ∈ s, RealizesMero (x i) (f i)) :
    RealizesMero (∑ i ∈ s, x i) (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction with
  | empty =>
      simpa using realizesMero_zero
  | insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.sum_insert hi]
      exact realizesMero_add (h i (Finset.mem_insert_self i s))
        (ih fun j hj ↦ h j (Finset.mem_insert_of_mem hj))

/-- **Realization transports differential algebraicity back to the function.** -/
theorem differentiallyAlgebraic_of_realizesMero {x : meroField (Set.univ : Set ℂ)} {f : ℂ → ℂ}
    (h : RealizesMero x f) (hDA : DifferentialAlgebraicOver (RatFunc ℂ) x) :
    DifferentiallyAlgebraic (toMeromorphicNFOn f (Set.univ : Set ℂ)) := by
  obtain ⟨a, b, A, B, hb0, hA, hB, hAa, hBb, hxab, hfAB⟩ := h
  rw [toMeromorphicNFOn_eq_of_fraction hb0 hA hB hBb hfAB]
  exact differentiallyAlgebraic_toMeromorphicNFOn_of_differentialAlgebraicOver hb0 hA hB hAa hBb
    (hxab ▸ hDA)

attribute [local instance] meromorphicEllipticCompositumComplexAlgebraMero

/-- **Differential algebraicity of realized meromorphic functions is closed under finite sums.**
The germs of the summands lie in the differentially algebraic subfield of the meromorphic field, so
their sum does too, and realization carries the relation back to the function. -/
theorem differentiallyAlgebraic_toMeromorphicNFOn_sum {ι : Type*} (s : Finset ι)
    (x : ι → meroField (Set.univ : Set ℂ)) (f : ι → ℂ → ℂ)
    (hreal : ∀ i ∈ s, RealizesMero (x i) (f i))
    (hDA : ∀ i ∈ s, DifferentiallyAlgebraic (toMeromorphicNFOn (f i) (Set.univ : Set ℂ))) :
    DifferentiallyAlgebraic (toMeromorphicNFOn (∑ i ∈ s, f i) (Set.univ : Set ℂ)) := by
  refine differentiallyAlgebraic_of_realizesMero (realizesMero_sum s x f hreal) ?_
  have hmem : ∀ i ∈ s, x i ∈ daOverRatFuncField := fun i hi ↦
    (mem_daOverRatFuncField_iff _).mpr
      (differentialAlgebraicOver_of_realizesMero (hreal i hi) (hDA i hi))
  exact (mem_daOverRatFuncField_iff _).mp (sum_mem hmem)

end

end GaloisForLFunctions.HTGeometry
