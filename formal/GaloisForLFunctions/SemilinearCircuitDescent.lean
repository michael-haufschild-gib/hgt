import GaloisForLFunctions.DifferenceDifferential
import Mathlib.Data.Finsupp.SMul
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# Minimal-support descent for coordinatewise semilinear relations

A nonzero subspace of finitely supported coefficient vectors which is stable
under coordinatewise field automorphisms contains a nonzero vector fixed by
all of them.  Choose a relation of least support and normalize one nonzero
coordinate to one.  Any automorphic image has the same support and the same
normalized coordinate.  Their difference would be a nonzero stable relation
of strictly smaller support, so it vanishes.

This is the coefficient-descent mechanism needed by the elementary
multi-automorphism Ostrowski argument.  It replaces the corresponding
fixed-vector step of parameterized Picard--Vessiot descent; it does not assume
a Galois correspondence or algebraic closure of the joint fixed field.
-/

namespace GaloisForLFunctions

noncomputable section

/-- Apply a field automorphism coefficientwise to a finitely supported
vector. -/
def finsuppMapRangeRingEquiv
    {I K : Type*} [Semiring K] (sigma : I → K ≃+* K)
    (i : I) {kappa : Type*} (v : kappa →₀ K) : kappa →₀ K :=
  Finsupp.mapRange (sigma i) (map_zero (sigma i)) v

@[simp] theorem finsuppMapRangeRingEquiv_apply
    {I K : Type*} [Semiring K] (sigma : I → K ≃+* K)
    (i : I) {kappa : Type*} (v : kappa →₀ K) (k : kappa) :
    finsuppMapRangeRingEquiv sigma i v k = sigma i (v k) := by
  simp [finsuppMapRangeRingEquiv]

/-- Coefficientwise application of an automorphism preserves support
exactly. -/
theorem finsuppMapRangeRingEquiv_support
    {I K : Type*} [Semiring K] (sigma : I → K ≃+* K)
    (i : I) {kappa : Type*} (v : kappa →₀ K) :
    (finsuppMapRangeRingEquiv sigma i v).support = v.support := by
  exact Finsupp.support_mapRange_of_injective
    (map_zero (sigma i)) v (sigma i).injective

/-- A least-support relation, normalized at one supported coordinate, is
fixed by every coordinatewise automorphism preserving the relation
subspace. -/
theorem minimal_support_normalized_relation_fixed
    {I kappa K : Type*} [Field K] (sigma : I → K ≃+* K)
    (W : Submodule K (kappa →₀ K))
    (hW : ∀ i v, v ∈ W → finsuppMapRangeRingEquiv sigma i v ∈ W)
    {v : kappa →₀ K} (hvW : v ∈ W) (hv0 : v ≠ 0)
    (hmin : ∀ {w : kappa →₀ K}, w ∈ W → w ≠ 0 →
      v.support.card ≤ w.support.card)
    {k₀ : kappa} (hk₀ : k₀ ∈ v.support) :
    ∀ i, finsuppMapRangeRingEquiv sigma i ((v k₀)⁻¹ • v) =
      (v k₀)⁻¹ • v := by
  let u : kappa →₀ K := (v k₀)⁻¹ • v
  have hvk₀ : v k₀ ≠ 0 := Finsupp.mem_support_iff.mp hk₀
  have hinv : (v k₀)⁻¹ ≠ 0 := inv_ne_zero hvk₀
  have huW : u ∈ W := W.smul_mem _ hvW
  have hu0 : u ≠ 0 := smul_ne_zero hinv hv0
  have husupp : u.support = v.support := Finsupp.support_smul_eq hinv
  have huk₀ : u k₀ = 1 := by
    simp [u, hvk₀]
  intro i
  let w : kappa →₀ K := finsuppMapRangeRingEquiv sigma i u
  have hwW : w ∈ W := hW i u huW
  have hwsupp : w.support = u.support :=
    finsuppMapRangeRingEquiv_support sigma i u
  have hwk₀ : w k₀ = 1 := by simp [w, huk₀]
  let d : kappa →₀ K := w - u
  have hdW : d ∈ W := W.sub_mem hwW huW
  have hdsub : d.support ⊆ u.support := by
    intro k hk
    by_contra hku
    have hu : u k = 0 := Finsupp.notMem_support_iff.mp hku
    have hw : w k = 0 := by
      apply Finsupp.notMem_support_iff.mp
      rw [hwsupp]
      exact hku
    exact Finsupp.mem_support_iff.mp hk (by simp [d, hw, hu])
  have hdk₀ : k₀ ∉ d.support := by
    rw [Finsupp.notMem_support_iff]
    simp [d, hwk₀, huk₀]
  have hk₀u : k₀ ∈ u.support := by simpa [husupp] using hk₀
  have hd : d = 0 := by
    by_contra hd0
    have hstrict : d.support ⊂ u.support :=
      Finset.ssubset_iff_subset_ne.mpr
        ⟨hdsub, fun heq => hdk₀ (heq.symm ▸ hk₀u)⟩
    have hcard : d.support.card < v.support.card := by
      rw [← husupp]
      exact Finset.card_lt_card hstrict
    exact (not_lt_of_ge (hmin hdW hd0)) hcard
  change w = u
  exact sub_eq_zero.mp hd

/-- Every nonzero submodule of finitely supported vectors has a nonzero
element of least support cardinality. -/
theorem Submodule.exists_minimal_finsupp_support_ne_zero
    {kappa K : Type*} [Field K]
    {W : Submodule K (kappa →₀ K)} (hW0 : W ≠ ⊥) :
    ∃ v : kappa →₀ K, v ∈ W ∧ v ≠ 0 ∧
      ∀ {w : kappa →₀ K}, w ∈ W → w ≠ 0 →
        v.support.card ≤ w.support.card := by
  classical
  have hex : ∃ v : kappa →₀ K, v ∈ W ∧ v ≠ 0 := by
    by_contra h
    apply hW0
    ext v
    simp only [Submodule.mem_bot]
    constructor
    · intro hv
      by_contra hv0
      exact h ⟨v, hv, hv0⟩
    · intro hv
      subst v
      exact W.zero_mem
  have hcard : ∃ n : ℕ, ∃ v : kappa →₀ K,
      v ∈ W ∧ v ≠ 0 ∧ v.support.card = n := by
    obtain ⟨v, hvW, hv0⟩ := hex
    exact ⟨v.support.card, v, hvW, hv0, rfl⟩
  let n := Nat.find hcard
  obtain ⟨v, hvW, hv0, hvcard⟩ := Nat.find_spec hcard
  refine ⟨v, hvW, hv0, ?_⟩
  intro w hwW hw0
  rw [hvcard]
  exact Nat.find_min' hcard ⟨w, hwW, hw0, rfl⟩

/-- A nonzero coordinatewise-semilinear-stable relation space contains a
nonzero relation fixed coefficientwise by every automorphism. -/
theorem stable_finsupp_submodule_exists_nonzero_fixed
    {I kappa K : Type*} [Field K] (sigma : I → K ≃+* K)
    (W : Submodule K (kappa →₀ K))
    (hWstable : ∀ i v, v ∈ W → finsuppMapRangeRingEquiv sigma i v ∈ W)
    (hW0 : W ≠ ⊥) :
    ∃ u : kappa →₀ K, u ∈ W ∧ u ≠ 0 ∧
      ∀ i, finsuppMapRangeRingEquiv sigma i u = u := by
  classical
  obtain ⟨v, hvW, hv0, hmin⟩ :=
    Submodule.exists_minimal_finsupp_support_ne_zero hW0
  obtain ⟨k₀, hk₀⟩ := Finsupp.support_nonempty_iff.mpr hv0
  let u : kappa →₀ K := (v k₀)⁻¹ • v
  have hvk₀ : v k₀ ≠ 0 := Finsupp.mem_support_iff.mp hk₀
  have huW : u ∈ W := W.smul_mem _ hvW
  have hu0 : u ≠ 0 := smul_ne_zero (inv_ne_zero hvk₀) hv0
  exact ⟨u, huW, hu0,
    minimal_support_normalized_relation_fixed
      sigma W hWstable hvW hv0 hmin hk₀⟩

/-- Choose a coefficient in `C` representing a jointly fixed element of
`K`. Away from the joint fixed field the value is set to zero; only fixed
inputs are used below. -/
def jointFixedCoefficientLift
    {I C K : Type*} [Field C] [Field K] [Algebra C K]
    (sigma : I → K ≃+* K)
    (hfixed : ∀ x : K, (∀ i, sigma i x = x) →
      ∃ c : C, algebraMap C K c = x)
    (x : K) : C := by
  classical
  exact if hx : ∀ i, sigma i x = x then
    Classical.choose (hfixed x hx) else 0

theorem jointFixedCoefficientLift_zero
    {I C K : Type*} [Field C] [Field K] [Algebra C K]
    (sigma : I → K ≃+* K)
    (hfixed : ∀ x : K, (∀ i, sigma i x = x) →
      ∃ c : C, algebraMap C K c = x) :
    jointFixedCoefficientLift sigma hfixed 0 = 0 := by
  classical
  have hx0 : ∀ i, sigma i (0 : K) = 0 := fun i => map_zero (sigma i)
  apply (algebraMap C K).injective
  rw [map_zero, jointFixedCoefficientLift, dif_pos hx0]
  exact Classical.choose_spec (hfixed 0 hx0)

theorem algebraMap_jointFixedCoefficientLift
    {I C K : Type*} [Field C] [Field K] [Algebra C K]
    (sigma : I → K ≃+* K)
    (hfixed : ∀ x : K, (∀ i, sigma i x = x) →
      ∃ c : C, algebraMap C K c = x)
    {x : K} (hx : ∀ i, sigma i x = x) :
    algebraMap C K (jointFixedCoefficientLift sigma hfixed x) = x := by
  classical
  simp only [jointFixedCoefficientLift, dif_pos hx]
  exact Classical.choose_spec (hfixed x hx)

/-- If the joint fixed field of the coordinate automorphisms is exactly the
image of `C`, a nonzero stable relation space contains a nonzero relation
whose coefficients all come from `C`. -/
theorem stable_finsupp_submodule_exists_nonzero_constant_vector
    {I kappa C K : Type*} [Field C] [Field K] [Algebra C K]
    (sigma : I → K ≃+* K)
    (hfixed : ∀ x : K, (∀ i, sigma i x = x) →
      ∃ c : C, algebraMap C K c = x)
    (W : Submodule K (kappa →₀ K))
    (hWstable : ∀ i v, v ∈ W → finsuppMapRangeRingEquiv sigma i v ∈ W)
    (hW0 : W ≠ ⊥) :
    ∃ c : kappa →₀ C, c ≠ 0 ∧
      Finsupp.mapRange (algebraMap C K) (map_zero (algebraMap C K)) c ∈ W := by
  obtain ⟨u, huW, hu0, hufixed⟩ :=
    stable_finsupp_submodule_exists_nonzero_fixed sigma W hWstable hW0
  have hcoeff (k : kappa) : ∀ i, sigma i (u k) = u k := by
    intro i
    have h := congrArg (fun v : kappa →₀ K => v k) (hufixed i)
    simpa using h
  let c : kappa →₀ C := Finsupp.mapRange
    (jointFixedCoefficientLift sigma hfixed)
    (jointFixedCoefficientLift_zero sigma hfixed) u
  have hmap :
      Finsupp.mapRange (algebraMap C K) (map_zero (algebraMap C K)) c = u := by
    ext k
    simp [c, algebraMap_jointFixedCoefficientLift sigma hfixed (hcoeff k)]
  refine ⟨c, ?_, ?_⟩
  · intro hc0
    apply hu0
    rw [← hmap, hc0, Finsupp.mapRange_zero]
  · rw [hmap]
    exact huW

/-- A coordinatewise semilinear action carries a linear combination to the
combination with automorphically transformed coefficients, provided it fixes
the generating family. -/
theorem semilinearAction_linearCombination
    {I kappa K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (sigma : I → K ≃+* K) (T : I → M ≃+ M) (x : kappa → M)
    (hsmul : ∀ i c m, T i (c • m) = sigma i c • T i m)
    (hx : ∀ i k, T i (x k) = x k)
    (i : I) (v : kappa →₀ K) :
    T i (Finsupp.linearCombination K x v) =
      Finsupp.linearCombination K x (finsuppMapRangeRingEquiv sigma i v) := by
  classical
  rw [Finsupp.linearCombination_apply, Finsupp.linearCombination_apply]
  rw [Finsupp.sum, Finsupp.sum]
  rw [map_sum]
  simp only [finsuppMapRangeRingEquiv,
    Finsupp.support_mapRange_of_injective
      (map_zero (sigma i)) v (sigma i).injective]
  apply Finset.sum_congr rfl
  intro k hk
  rw [hsmul, hx, Finsupp.mapRange_apply]

/-- The coefficient relation space of a semilinearly fixed family is stable
under coefficientwise application of every automorphism. -/
theorem linearCombination_relationSpace_stable
    {I kappa K M : Type*} [Field K] [AddCommGroup M] [Module K M]
    (sigma : I → K ≃+* K) (T : I → M ≃+ M) (x : kappa → M)
    (hsmul : ∀ i c m, T i (c • m) = sigma i c • T i m)
    (hx : ∀ i k, T i (x k) = x k) :
    ∀ i v, v ∈ LinearMap.ker (Finsupp.linearCombination K x) →
      finsuppMapRangeRingEquiv sigma i v ∈
        LinearMap.ker (Finsupp.linearCombination K x) := by
  intro i v hv
  rw [LinearMap.mem_ker] at hv ⊢
  rw [← semilinearAction_linearCombination sigma T x hsmul hx]
  rw [hv, map_zero]

/-- If a semilinearly fixed family has a nontrivial linear relation over
`K`, and the joint fixed field of the automorphisms is the image of `C`, then
it has a nontrivial relation with coefficients in `C`. -/
theorem semilinear_relationSpace_exists_nonzero_constant_relation
    {I kappa C K M : Type*} [Field C] [Field K] [Algebra C K]
    [AddCommGroup M] [Module K M]
    (sigma : I → K ≃+* K)
    (hfixed : ∀ z : K, (∀ i, sigma i z = z) →
      ∃ c : C, algebraMap C K c = z)
    (T : I → M ≃+ M) (x : kappa → M)
    (hsmul : ∀ i c m, T i (c • m) = sigma i c • T i m)
    (hx : ∀ i k, T i (x k) = x k)
    (hrel : LinearMap.ker (Finsupp.linearCombination K x) ≠ ⊥) :
    ∃ c : kappa →₀ C, c ≠ 0 ∧
      Finsupp.linearCombination K x
        (Finsupp.mapRange (algebraMap C K) (map_zero (algebraMap C K)) c) = 0 := by
  let W := LinearMap.ker (Finsupp.linearCombination K x)
  have hWstable : ∀ i v, v ∈ W →
      finsuppMapRangeRingEquiv sigma i v ∈ W :=
    linearCombination_relationSpace_stable sigma T x hsmul hx
  obtain ⟨c, hc0, hcW⟩ :=
    stable_finsupp_submodule_exists_nonzero_constant_vector
      sigma hfixed W hWstable hrel
  exact ⟨c, hc0, LinearMap.mem_ker.mp hcW⟩

end

end GaloisForLFunctions
