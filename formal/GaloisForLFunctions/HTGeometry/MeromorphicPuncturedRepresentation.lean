import GaloisForLFunctions.HTGeometry.MeromorphicFractionJets

/-!
# Punctured-local representatives of meromorphic-field elements

`HasPuncturedMeromorphicRep x φ` says that the global fraction-field element `x` has an entire
quotient representative agreeing with the meromorphic function `φ` on the punctured neighborhood
of every point.  The relation is closed under addition, complex scalar multiplication, finite
sums, differential jets, and constant-coefficient differential operators.
-/

open Filter Set Topology Function Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance puncturedRepDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance puncturedRepComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance puncturedRepComplexAlgebraMero : Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance puncturedRepIntAlgebraAnalytic : Algebra ℤ (analyticSubring Set.univ) :=
  Ring.toIntAlgebra _

local instance puncturedRepIntAlgebraMero : Algebra ℤ (meroField Set.univ) :=
  Ring.toIntAlgebra _

local instance puncturedRepDifferential : Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

/-- A field element and a meromorphic function are represented by the same entire fraction on
every punctured neighborhood. -/
def HasPuncturedMeromorphicRep (x : meroField Set.univ) (φ : ℂ → ℂ) : Prop :=
  ∃ (a b : analyticSubring Set.univ) (f g : ℂ → ℂ),
    b ≠ 0 ∧ AnalyticOnNhd ℂ f Set.univ ∧ AnalyticOnNhd ℂ g Set.univ ∧
    Germ.coeRingHom (𝓟 Set.univ) f = (a : Germ (𝓟 Set.univ) ℂ) ∧
    Germ.coeRingHom (𝓟 Set.univ) g = (b : Germ (𝓟 Set.univ) ℂ) ∧
    x = algebraMap (analyticSubring Set.univ) (meroField Set.univ) a /
      algebraMap (analyticSubring Set.univ) (meroField Set.univ) b ∧
    ∀ z, (fun w => f w / g w) =ᶠ[𝓝[≠] z] φ

/-- An explicit entire fraction has its evident punctured-local representative. -/
theorem hasPuncturedMeromorphicRep_fraction
    {a b : analyticSubring Set.univ} (hb : b ≠ 0)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ)
    (hfa : Germ.coeRingHom (𝓟 Set.univ) f = (a : Germ (𝓟 Set.univ) ℂ))
    (hgb : Germ.coeRingHom (𝓟 Set.univ) g = (b : Germ (𝓟 Set.univ) ℂ)) :
    HasPuncturedMeromorphicRep
      (algebraMap (analyticSubring Set.univ) (meroField Set.univ) a /
        algebraMap (analyticSubring Set.univ) (meroField Set.univ) b)
      (fun z => f z / g z) := by
  exact ⟨a, b, f, g, hb, hf, hg, hfa, hgb, rfl,
    fun _ => Filter.Eventually.of_forall fun _ => rfl⟩

/-- Punctured-local representatives are closed under addition. -/
theorem HasPuncturedMeromorphicRep.add
    {x y : meroField Set.univ} {φ ψ : ℂ → ℂ}
    (hx : HasPuncturedMeromorphicRep x φ)
    (hy : HasPuncturedMeromorphicRep y ψ) :
    HasPuncturedMeromorphicRep (x + y) (φ + ψ) := by
  obtain ⟨a, b, f, g, hb, hf, hg, hfa, hgb, hxf, hxev⟩ := hx
  obtain ⟨c, d, u, v, hd, hu, hv, huc, hvd, hyf, hyev⟩ := hy
  let A : analyticSubring Set.univ := a * d + c * b
  let B : analyticSubring Set.univ := b * d
  let F : ℂ → ℂ := fun z => f z * v z + u z * g z
  let G : ℂ → ℂ := fun z => g z * v z
  have hB : B ≠ 0 := mul_ne_zero hb hd
  have hF : AnalyticOnNhd ℂ F Set.univ := (hf.mul hv).add (hu.mul hg)
  have hG : AnalyticOnNhd ℂ G Set.univ := hg.mul hv
  have hFA : Germ.coeRingHom (𝓟 Set.univ) F = (A : Germ (𝓟 Set.univ) ℂ) := by
    change Germ.ofFun (l := 𝓟 Set.univ) (fun z => f z * v z + u z * g z) =
      a.1 * d.1 + c.1 * b.1
    rw [← hfa, ← hgb, ← huc, ← hvd]
    rfl
  have hGB : Germ.coeRingHom (𝓟 Set.univ) G = (B : Germ (𝓟 Set.univ) ℂ) := by
    change Germ.ofFun (l := 𝓟 Set.univ) (fun z => g z * v z) = b.1 * d.1
    rw [← hgb, ← hvd]
    rfl
  refine ⟨A, B, F, G, hB, hF, hG, hFA, hGB, ?_, ?_⟩
  · rw [hxf, hyf]
    dsimp [A, B]
    simp only [map_add, map_mul]
    have hbF : algebraMap (analyticSubring Set.univ) (meroField Set.univ) b ≠ 0 :=
      fun hz => hb ((IsFractionRing.injective (analyticSubring Set.univ)
        (meroField Set.univ)) (by simpa using hz))
    have hdF : algebraMap (analyticSubring Set.univ) (meroField Set.univ) d ≠ 0 :=
      fun hz => hd ((IsFractionRing.injective (analyticSubring Set.univ)
        (meroField Set.univ)) (by simpa using hz))
    field_simp [hbF, hdF]
  · intro z
    have hgne := analyticSubring_rep_eventually_ne_zero hb hg hgb z
    have hvne := analyticSubring_rep_eventually_ne_zero hd hv hvd z
    filter_upwards [hxev z, hyev z, hgne, hvne] with w hxw hyw hgw hvw
    dsimp [F, G]
    field_simp [hgw] at hxw
    field_simp [hvw] at hyw
    field_simp [hgw, hvw]
    rw [hxw, hyw]
    ring

/-- Punctured-local representatives are closed under multiplication by an embedded complex
constant. -/
theorem HasPuncturedMeromorphicRep.const_mul
    (c : ℂ) {x : meroField Set.univ} {φ : ℂ → ℂ}
    (hx : HasPuncturedMeromorphicRep x φ) :
    HasPuncturedMeromorphicRep
      (algebraMap (analyticSubring Set.univ) (meroField Set.univ)
          (constToAnalytic Set.univ c) * x)
      (fun z => c * φ z) := by
  obtain ⟨a, b, f, g, hb, hf, hg, hfa, hgb, hxf, hxev⟩ := hx
  let A : analyticSubring Set.univ := constToAnalytic Set.univ c * a
  let F : ℂ → ℂ := fun z => c * f z
  refine ⟨A, b, F, g, hb, analyticOnNhd_const.mul hf, hg, ?_, hgb, ?_, ?_⟩
  · change Germ.ofFun (l := 𝓟 Set.univ) (fun z => c * f z) =
      (constToAnalytic Set.univ c : Germ (𝓟 Set.univ) ℂ) * a.1
    rw [← hfa]
    rfl
  · rw [hxf]
    dsimp [A]
    simp only [map_mul]
    have hbF : algebraMap (analyticSubring Set.univ) (meroField Set.univ) b ≠ 0 :=
      fun hz => hb ((IsFractionRing.injective (analyticSubring Set.univ)
        (meroField Set.univ)) (by simpa using hz))
    field_simp [hbF]
  · intro z
    filter_upwards [hxev z] with w hw
    dsimp [F]
    calc
      c * f w / g w = c * (f w / g w) := by ring
      _ = c * φ w := by rw [hw]

/-- The `n`th differential-field jet of an explicit fraction represents the ordinary iterated
derivative punctured-locally. -/
theorem hasPuncturedMeromorphicRep_differentialJet_fraction
    {a b : analyticSubring Set.univ} (hb : b ≠ 0)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ)
    (hfa : Germ.coeRingHom (𝓟 Set.univ) f = (a : Germ (𝓟 Set.univ) ℂ))
    (hgb : Germ.coeRingHom (𝓟 Set.univ) g = (b : Germ (𝓟 Set.univ) ℂ))
    (n : ℕ) :
    HasPuncturedMeromorphicRep
      (differentialJet n
        (algebraMap (analyticSubring Set.univ) (meroField Set.univ) a /
          algebraMap (analyticSubring Set.univ) (meroField Set.univ) b))
      (iteratedDeriv n (fun z => f z / g z)) := by
  have ha : univAnalytic f hf = a := Subtype.ext hfa
  have hb' : univAnalytic g hg = b := Subtype.ext hgb
  let A := (analyticFractionJetPair (univAnalytic f hf) (univAnalytic g hg) n).1
  let B := (analyticFractionJetPair (univAnalytic f hf) (univAnalytic g hg) n).2
  let F := (functionFractionJetPair f g n).1
  let G := (functionFractionJetPair f g n).2
  have hB : B ≠ 0 := analyticFractionJetPair_denominator_ne_zero
    (by simpa [hb'] using hb) n
  have hAn := (functionFractionJetPair_analytic hf hg n).1
  have hGn := (functionFractionJetPair_analytic hf hg n).2
  have hrep := analyticFractionJetPair_rep hf hg n
  refine ⟨A, B, F, G, hB, hAn, hGn, hrep.1, hrep.2, ?_, ?_⟩
  · dsimp [A, B]
    rw [ha, hb', ← differentialJet_analyticFraction_eq a b hb n]
  · intro z
    have hgne := analyticSubring_rep_eventually_ne_zero hb hg hgb z
    filter_upwards [hgne] with w hgw
    exact functionFractionJetPair_div_eq_iteratedDeriv hf hg n hgw

/-- Finite sums preserve punctured-local representation. -/
theorem hasPuncturedMeromorphicRep_sum
    {ι : Type*} (s : Finset ι)
    {x : ι → meroField Set.univ} {φ : ι → ℂ → ℂ}
    (h : ∀ i ∈ s, HasPuncturedMeromorphicRep (x i) (φ i)) :
    HasPuncturedMeromorphicRep (∑ i ∈ s, x i) (fun z => ∑ i ∈ s, φ i z) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, 1, (fun _ => 0), (fun _ => 1), one_ne_zero,
        analyticOnNhd_const, analyticOnNhd_const, rfl, rfl, ?_, ?_⟩
      · simp
      · intro z
        exact Filter.Eventually.of_forall fun _ => by simp
  | insert i s hi ih =>
      rw [Finset.sum_insert hi]
      have hrest : HasPuncturedMeromorphicRep
          (∑ j ∈ s, x j) (fun z => ∑ j ∈ s, φ j z) := by
        apply ih
        intro j hj
        exact h j (Finset.mem_insert_of_mem hj)
      have hadd := (h i (Finset.mem_insert_self i s)).add hrest
      convert hadd using 1
      funext z
      rw [Finset.sum_insert hi]
      rfl

/-- Applying a constant-coefficient differential operator in the global field represents the
pointwise constant-coefficient operator on the quotient function punctured-locally. -/
theorem hasPuncturedMeromorphicRep_differentialOperatorApply_fraction
    {a b : analyticSubring Set.univ} (hb : b ≠ 0)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f Set.univ)
    (hg : AnalyticOnNhd ℂ g Set.univ)
    (hfa : Germ.coeRingHom (𝓟 Set.univ) f = (a : Germ (𝓟 Set.univ) ℂ))
    (hgb : Germ.coeRingHom (𝓟 Set.univ) g = (b : Germ (𝓟 Set.univ) ℂ))
    (L : Polynomial ℂ) :
    HasPuncturedMeromorphicRep
      (differentialOperatorApply L
        (algebraMap (analyticSubring Set.univ) (meroField Set.univ) a /
          algebraMap (analyticSubring Set.univ) (meroField Set.univ) b))
      (constantCoeffDifferentialOperator L (fun z => f z / g z)) := by
  classical
  let x : ℕ → meroField Set.univ := fun n =>
    algebraMap (analyticSubring Set.univ) (meroField Set.univ)
        (constToAnalytic Set.univ (L.coeff n)) *
      differentialJet n
        (algebraMap (analyticSubring Set.univ) (meroField Set.univ) a /
          algebraMap (analyticSubring Set.univ) (meroField Set.univ) b)
  let φ : ℕ → ℂ → ℂ := fun n z => L.coeff n *
    iteratedDeriv n (fun w => f w / g w) z
  have hterm : ∀ n ∈ L.support, HasPuncturedMeromorphicRep (x n) (φ n) := by
    intro n _
    exact (hasPuncturedMeromorphicRep_differentialJet_fraction
      hb hf hg hfa hgb n).const_mul (L.coeff n)
  have hsum := hasPuncturedMeromorphicRep_sum L.support hterm
  simpa only [differentialOperatorApply, Polynomial.sum_def,
    constantCoeffDifferentialOperator, x, φ] using! hsum

/-- Punctured-local equality is preserved by every iterated derivative. -/
theorem EventuallyEq.nhdsNE_iteratedDeriv
    {φ ψ : ℂ → ℂ} {z : ℂ} (h : φ =ᶠ[𝓝[≠] z] ψ) (n : ℕ) :
    iteratedDeriv n φ =ᶠ[𝓝[≠] z] iteratedDeriv n ψ := by
  induction n with
  | zero => simpa [iteratedDeriv_zero] using h
  | succ n ih =>
      rw [iteratedDeriv_succ, iteratedDeriv_succ]
      exact ih.nhdsNE_deriv

/-- Punctured-local equality is preserved by constant-coefficient differential operators. -/
theorem constantCoeffDifferentialOperator_congr_nhdsNE
    (L : Polynomial ℂ) {φ ψ : ℂ → ℂ} {z : ℂ}
    (h : φ =ᶠ[𝓝[≠] z] ψ) :
    constantCoeffDifferentialOperator L φ =ᶠ[𝓝[≠] z]
      constantCoeffDifferentialOperator L ψ := by
  classical
  have hall : ∀ n ∈ L.support,
      iteratedDeriv n φ =ᶠ[𝓝[≠] z] iteratedDeriv n ψ :=
    fun n _ => EventuallyEq.nhdsNE_iteratedDeriv h n
  have hall' : ∀ᶠ w in 𝓝[≠] z, ∀ n ∈ L.support,
      iteratedDeriv n φ w = iteratedDeriv n ψ w :=
    (Filter.eventually_all_finset L.support).2 hall
  filter_upwards [hall'] with w hw
  simp only [constantCoeffDifferentialOperator, Polynomial.sum_def]
  apply Finset.sum_congr rfl
  intro n hn
  rw [hw n hn]

/-- A punctured representative can be replaced by any punctured-locally equal function. -/
theorem HasPuncturedMeromorphicRep.congr_fun
    {x : meroField Set.univ} {φ ψ : ℂ → ℂ}
    (hx : HasPuncturedMeromorphicRep x φ)
    (h : ∀ z, φ =ᶠ[𝓝[≠] z] ψ) : HasPuncturedMeromorphicRep x ψ := by
  obtain ⟨a, b, f, g, hb, hf, hg, hfa, hgb, hxf, hxev⟩ := hx
  exact ⟨a, b, f, g, hb, hf, hg, hfa, hgb, hxf,
    fun z => (hxev z).trans (h z)⟩

end

end GaloisForLFunctions

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance puncturedRepClosureDomain :
    IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ
    isPreconnected_univ Set.univ_nonempty

local instance puncturedRepClosureComplexAlgebraAnalytic :
    Algebra ℂ (analyticSubring Set.univ) := (constToAnalytic Set.univ).toAlgebra

local instance puncturedRepClosureComplexAlgebraMero : Algebra ℂ (meroField Set.univ) :=
  ((algebraMap (analyticSubring Set.univ) (meroField Set.univ)).comp
    (constToAnalytic Set.univ)).toAlgebra

local instance puncturedRepClosureDifferential :
    Differential (meroField (Set.univ : Set ℂ)) :=
  meroFieldDifferential isOpen_univ isPreconnected_univ Set.univ_nonempty

/-- Every punctured-local meromorphic representative is stable under an arbitrary
constant-coefficient differential operator. -/
theorem HasPuncturedMeromorphicRep.differentialOperatorApply
    {x : meroField Set.univ} {φ : ℂ → ℂ}
    (hx : HasPuncturedMeromorphicRep x φ) (L : Polynomial ℂ) :
    HasPuncturedMeromorphicRep (differentialOperatorApply L x)
      (constantCoeffDifferentialOperator L φ) := by
  obtain ⟨a, b, f, g, hb, hf, hg, hfa, hgb, hxf, hxev⟩ := hx
  rw [hxf]
  apply (hasPuncturedMeromorphicRep_differentialOperatorApply_fraction
    hb hf hg hfa hgb L).congr_fun
  intro z
  exact constantCoeffDifferentialOperator_congr_nhdsNE L (hxev z)

end

end GaloisForLFunctions
