import GaloisForLFunctions.HTGeometry.MultipleSineFaceIteration
import GaloisForLFunctions.HTGeometry.BarnesOrderOnePartialFractions
import GaloisForLFunctions.HTGeometry.PeriodCotangentMeroDA
import GaloisForLFunctions.HTGeometry.BarnesSourceRepresentative

/-!
# The order-one face of the multiple sine is differentially algebraic

The face coordinates descend to frames with one direction left, and there the reflected Barnes
source is the cotangent of the period up to a rational function.  Since the cotangent element of the
meromorphic field is differentially algebraic over `ℂ(z)`, so is the order-one source, and therefore
every face of codimension one:

```text
I_{N-1} ⊆ Ann_DA(L_V).
```

The transfer is by punctured-local representatives.  Reflection acts on them by reflecting the
function, the difference of two representatives represents the difference, and the pointwise
partial-fraction identity holds off the period lattice — a discrete set, so it holds on a punctured
neighbourhood of every point.  A rational punctured representative makes an element differentially
algebraic.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher

noncomputable section

local instance puncturedReflectDomain : IsDomain (analyticSubring (Set.univ : Set ℂ)) :=
  Bottcher.isDomain_analyticSubring Set.univ isOpen_univ isPreconnected_univ Set.univ_nonempty

/-! ### Reflection of punctured representatives -/

theorem tendsto_nhdsNE_complexReflection (c z : ℂ) :
    Filter.Tendsto (fun x : ℂ => c - x) (𝓝[≠] z) (𝓝[≠] (c - z)) := by
  refine Filter.Tendsto.inf ?_ ?_
  · exact (continuous_const.sub continuous_id).continuousAt
  · refine Filter.tendsto_principal_principal.mpr fun x hx => ?_
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hx ⊢
    intro hcon
    exact hx (by linear_combination -hcon)

/-- **A reflection is represented by the reflected function.** -/
theorem HasPuncturedMeromorphicRep.reflect {x : meroField (Set.univ : Set ℂ)} {φ : ℂ → ℂ}
    (c : ℂ) (hx : HasPuncturedMeromorphicRep x φ) :
    HasPuncturedMeromorphicRep (complexReflectionMeroEquiv c x) (fun z => φ (c - z)) := by
  obtain ⟨a, b, f, g, hb, hf, hg, hfa, hgb, hxeq, hxev⟩ := hx
  refine ⟨complexReflectionAnalyticEquiv c a, complexReflectionAnalyticEquiv c b,
    fun z => f (c - z), fun z => g (c - z), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro hcon
    exact hb ((complexReflectionAnalyticEquiv c).injective (by rw [hcon, map_zero]))
  · exact hf.comp (analyticOnNhd_complexReflection c _) (Set.mapsTo_univ _ _)
  · exact hg.comp (analyticOnNhd_complexReflection c _) (Set.mapsTo_univ _ _)
  · have hco : ((complexReflectionAnalyticEquiv c a : analyticSubring (Set.univ : Set ℂ)) :
        Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
        = (a : Germ (𝓟 (Set.univ : Set ℂ)) ℂ).compTendsto (complexReflection c)
          (tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)) := rfl
    rw [hco, ← hfa]
    rfl
  · have hco : ((complexReflectionAnalyticEquiv c b : analyticSubring (Set.univ : Set ℂ)) :
        Germ (𝓟 (Set.univ : Set ℂ)) ℂ)
        = (b : Germ (𝓟 (Set.univ : Set ℂ)) ℂ).compTendsto (complexReflection c)
          (tendsto_principal_principal.mpr (Set.mapsTo_univ _ _)) := rfl
    rw [hco, ← hgb]
    rfl
  · rw [hxeq, map_div₀, complexReflectionMeroEquiv_algebraMap,
      complexReflectionMeroEquiv_algebraMap]
  · intro z
    exact (hxev (c - z)).comp_tendsto (tendsto_nhdsNE_complexReflection c z)

theorem intCast_meroField_eq_algebraMap (ε : ℤ) :
    ((ε : ℤ) : meroField (Set.univ : Set ℂ))
      = algebraMap (analyticSubring (Set.univ : Set ℂ)) (meroField (Set.univ : Set ℂ))
          (constToAnalytic (Set.univ : Set ℂ) (ε : ℂ)) := by
  rw [map_intCast, map_intCast]

/-- **A reflected source is represented by the reflected combination.** -/
theorem HasPuncturedMeromorphicRep.reflectedSource {x : meroField (Set.univ : Set ℂ)}
    {φ : ℂ → ℂ} (ε : ℤ) (c : ℂ) (hx : HasPuncturedMeromorphicRep x φ) :
    HasPuncturedMeromorphicRep (meroReflectedSource ε c x)
      (fun z => φ z - (ε : ℂ) * φ (c - z)) := by
  have hrefl := (HasPuncturedMeromorphicRep.reflect c hx).const_mul (ε : ℂ)
  have hsub := hx.sub hrefl
  unfold meroReflectedSource
  rw [intCast_meroField_eq_algebraMap]
  exact hsub

end

end GaloisForLFunctions

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions Bottcher

noncomputable section

attribute [local instance] relativeGaugeDomain relativeGaugeDifferential
  relativeGaugeRatFuncAlgebra relativeGaugeRatFuncDifferential relativeGaugeDifferentialAlgebra
  relativeGaugeCharZeroBase relativeGaugeCharZero relativeGaugeComplexAlgebra
  relativeGaugeComplexAlgebraAnalytic

/-! ### The period lattice is avoided on punctured neighbourhoods -/

theorem eventually_nhdsNE_ne_intMul_period {w : ℂ} (hw : 0 < w.im) (z₀ : ℂ) :
    ∀ᶠ z in 𝓝[≠] z₀, ∀ k : ℤ, z ≠ (k : ℂ) * w := by
  have h1 := eventually_nhdsNE_conePeriod_add_ne_zero (fun _ : Fin 1 => w) (fun _ => hw) z₀
  have h2 := (tendsto_nhdsNE_complexReflection w z₀).eventually
    (eventually_nhdsNE_conePeriod_add_ne_zero (fun _ : Fin 1 => w) (fun _ => hw) (w - z₀))
  have h3 := eventually_nhdsNE_notMem_finite (F := ({0, w} : Set ℂ)) (Set.toFinite _) z₀
  filter_upwards [h1, h2, h3] with z hz1 hz2 hz3
  have key1 : ∀ m : ℕ, m ≠ 0 → (m : ℂ) * w + z ≠ 0 := by
    intro m hm
    have hn : (fun _ : Fin 1 => m) ≠ 0 := fun h => hm (congrFun h 0)
    have hzz := hz1 (fun _ => m) hn
    rwa [conePeriod_const] at hzz
  have key2 : ∀ m : ℕ, m ≠ 0 → (m : ℂ) * w + (w - z) ≠ 0 := by
    intro m hm
    have hn : (fun _ : Fin 1 => m) ≠ 0 := fun h => hm (congrFun h 0)
    have hzz := hz2 (fun _ => m) hn
    rwa [conePeriod_const] at hzz
  have hz0 : z ≠ 0 := by
    intro h
    exact hz3 (by rw [h]; exact Set.mem_insert _ _)
  have hzw : z ≠ w := by
    intro h
    exact hz3 (by rw [h]; exact Set.mem_insert_of_mem _ rfl)
  intro k hcon
  rcases lt_trichotomy k 0 with hneg | hzero | hpos
  · have hm : (-k).toNat ≠ 0 := by omega
    have hcast : (((-k).toNat : ℕ) : ℂ) = -(k : ℂ) := by
      have htn := Int.toNat_of_nonneg (show (0 : ℤ) ≤ -k by omega)
      calc (((-k).toNat : ℕ) : ℂ) = ((((-k).toNat : ℕ) : ℤ) : ℂ) := by push_cast; ring
        _ = ((-k : ℤ) : ℂ) := by rw [htn]
        _ = -(k : ℂ) := by push_cast; ring
    refine key1 (-k).toNat hm ?_
    rw [hcast, hcon]
    ring
  · exact hz0 (by rw [hcon, hzero]; push_cast; ring)
  · rcases eq_or_lt_of_le (show (1 : ℤ) ≤ k by omega) with h1k | h2k
    · exact hzw (by rw [hcon, ← h1k]; push_cast; ring)
    · have hm : (k - 1).toNat ≠ 0 := by omega
      have hcast : (((k - 1).toNat : ℕ) : ℂ) = (k : ℂ) - 1 := by
        have htn := Int.toNat_of_nonneg (show (0 : ℤ) ≤ k - 1 by omega)
        calc (((k - 1).toNat : ℕ) : ℂ) = ((((k - 1).toNat : ℕ) : ℤ) : ℂ) := by push_cast; ring
          _ = ((k - 1 : ℤ) : ℂ) := by rw [htn]
          _ = (k : ℂ) - 1 := by push_cast; ring
      refine key2 (k - 1).toNat hm ?_
      rw [hcast, hcon]
      ring

/-! ### The singleton frame -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

instance uniqueSingletonSubtype (i : ι) : Unique {x : ι // x ∈ ({i} : Finset ι)} where
  default := ⟨i, Finset.mem_singleton_self i⟩
  uniq := fun x => Subtype.ext (Finset.mem_singleton.mp x.2)

omit [Fintype ι] [DecidableEq ι] in
theorem barnesConeProduct_subframe_singleton (ω : ι → ℂ) (i : ι) :
    barnesConeProduct (subframe ω ({i} : Finset ι))
      = barnesConeProduct (fun _ : Fin 1 => ω i) := by
  have hframe : subframe ω ({i} : Finset ι)
      = (fun _ : Fin 1 => ω i) ∘ (Equiv.ofUnique {x : ι // x ∈ ({i} : Finset ι)} (Fin 1)) := by
    funext x
    show ω x.1 = ω i
    rw [Finset.mem_singleton.mp x.2]
  funext z
  rw [hframe]
  exact barnesConeProduct_comp_equiv _ (fun _ : Fin 1 => ω i) z

/-- The rational difference between the order-one source and the period cotangent. -/
def orderOneNumerator (w : ℂ) : Polynomial ℂ := Polynomial.C 2 * Polynomial.X - Polynomial.C w

/-- Its denominator. -/
def orderOneDenominator (w : ℂ) : Polynomial ℂ :=
  Polynomial.X * (Polynomial.C w - Polynomial.X)

theorem orderOneDenominator_ne_zero {w : ℂ} (hw : w ≠ 0) : orderOneDenominator w ≠ 0 := by
  intro h
  have hev := congrArg (Polynomial.eval (w / 2)) h
  rw [orderOneDenominator] at hev
  simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X,
    Polynomial.eval_zero] at hev
  have : w * w / 4 = 0 := by linear_combination hev
  have hww : w * w = 0 := by linear_combination 4 * this
  exact hw (by rcases mul_eq_zero.mp hww with h' | h' <;> exact h')

omit [Fintype ι] [DecidableEq ι] in
/-- **The order-one frame source differs from the period cotangent by an explicit rational
function.** -/
theorem hasPuncturedMeromorphicRep_frameSourceMero_singleton_sub (ω : ι → ℂ)
    (hω : ∀ i, 0 < (ω i).im) (i : ι) (hS : ({i} : Finset ι).Nonempty) :
    HasPuncturedMeromorphicRep
      (frameSourceMero ω hω ({i} : Finset ι) hS - periodCotMero (ω i))
      (fun z => (orderOneNumerator (ω i)).eval z / (orderOneDenominator (ω i)).eval z) := by
  classical
  set w : ℂ := ω i with hwdef
  have hwim : 0 < w.im := hω i
  have hw0 : w ≠ 0 := by
    intro h
    rw [h] at hwim
    simp at hwim
  haveI : Nonempty {x : ι // x ∈ ({i} : Finset ι)} := ⟨⟨i, Finset.mem_singleton_self i⟩⟩
  -- the source as a reflected Barnes source
  have hsign : frameSignZ ({i} : Finset ι) = 1 := by
    rw [frameSignZ, Finset.card_singleton]
    norm_num
  have hpoint : frameReflectionPoint ω ({i} : Finset ι) = w := by
    rw [frameReflectionPoint, Finset.sum_singleton]
  have hsrc : frameSourceMero ω hω ({i} : Finset ι) hS
      = GaloisForLFunctions.meroReflectedSource 1 w
        (barnesSourceLogDerivMero (subframe ω ({i} : Finset ι))
          (subframe_im_pos hω ({i} : Finset ι))) := by
    rw [frameSourceMero_eq, multipleSineSourceMero, hsign, hpoint]
  -- its punctured representative
  have hrepPsi := hasPuncturedMeromorphicRep_barnesSourceLogDerivMero
    (subframe ω ({i} : Finset ι)) (subframe_im_pos hω ({i} : Finset ι))
  rw [barnesConeProduct_subframe_singleton ω i] at hrepPsi
  have hrepSrc := HasPuncturedMeromorphicRep.reflectedSource 1 w hrepPsi
  rw [← hsrc] at hrepSrc
  have hrepCot := hasPuncturedMeromorphicRep_periodCotMero hw0
  have hrepDiff := hrepSrc.sub hrepCot
  -- the difference is rational
  have hratio : HasPuncturedMeromorphicRep
      (frameSourceMero ω hω ({i} : Finset ι) hS - periodCotMero w)
      (fun z => (orderOneNumerator w).eval z / (orderOneDenominator w).eval z) := by
    refine hrepDiff.congr_fun fun z₀ => ?_
    filter_upwards [eventually_nhdsNE_ne_intMul_period hwim z₀] with z hz
    have hidentity := barnesSource_orderOne_reflect_eq_cot w hwim hz
    have hzne : z ≠ 0 := by
      intro h
      exact hz 0 (by rw [h]; ring)
    have hwzne : w - z ≠ 0 := by
      intro h
      exact hz 1 (by push_cast; linear_combination -h)
    show (logDeriv (barnesConeProduct (fun _ : Fin 1 => w)) z
            - ((1 : ℤ) : ℂ) * logDeriv (barnesConeProduct (fun _ : Fin 1 => w)) (w - z))
          - ((Real.pi : ℂ) / w) * Complex.cot ((Real.pi : ℂ) * z / w)
        = (orderOneNumerator w).eval z / (orderOneDenominator w).eval z
    rw [orderOneNumerator, orderOneDenominator]
    simp only [Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_C, Polynomial.eval_X,
      Int.cast_one, one_mul]
    rw [hidentity]
    field_simp
    ring
  exact hratio

omit [Fintype ι] [DecidableEq ι] in
/-- **The order-one frame source is differentially algebraic over `ℂ(z)`.** -/
theorem differentialAlgebraicOver_frameSourceMero_singleton (ω : ι → ℂ)
    (hω : ∀ i, 0 < (ω i).im) (i : ι) (hS : ({i} : Finset ι).Nonempty) :
    DifferentialAlgebraicOver (RatFunc ℂ) (frameSourceMero ω hω ({i} : Finset ι) hS) := by
  have hwim : 0 < (ω i).im := hω i
  have hw0 : ω i ≠ 0 := by
    intro h
    rw [h] at hwim
    simp at hwim
  have hDAdiff : DifferentialAlgebraicOver (RatFunc ℂ)
      (frameSourceMero ω hω ({i} : Finset ι) hS - periodCotMero (ω i)) :=
    differentialAlgebraicOver_of_hasPuncturedMeromorphicRep_ratio
      (orderOneDenominator_ne_zero hw0)
      (hasPuncturedMeromorphicRep_frameSourceMero_singleton_sub ω hω i hS)
  have hsum := differentialAlgebraicOver_add hDAdiff
    (differentialAlgebraicOver_periodCotMero (ω i))
  simpa using hsum

/-! ### The codimension-one face is annihilated -/

omit [Fintype ι] in
/-- **`I_{N-1} ⊆ Ann_DA(L_V)`.**  Every product of shift differences that leaves exactly one
direction annihilates the multiple-sine source modulo the differentially algebraic sector. -/
theorem differentialAlgebraicOver_frameSource_topFace (ω : ι → ℂ) (hω : ∀ i, 0 < (ω i).im)
    (S : Finset ι) (hS : S.Nonempty) (l : List ι) (hnd : l.Nodup) (hsub : ∀ j ∈ l, j ∈ S)
    (i : ι) (hface : S \ l.toFinset = ({i} : Finset ι)) :
    DifferentialAlgebraicOver (RatFunc ℂ)
      (listShiftDiff ω l (frameSourceMero ω hω S hS)) := by
  classical
  have hne : (S \ l.toFinset).Nonempty := by
    rw [hface]
    exact ⟨i, Finset.mem_singleton_self i⟩
  have hsingle : ({i} : Finset ι).Nonempty := ⟨i, Finset.mem_singleton_self i⟩
  have hface' := differentialAlgebraicOver_frameSource_face ω hω S hS l hnd hsub hne
  have hbase : DifferentialAlgebraicOver (RatFunc ℂ)
      (frameSourceMero ω hω (S \ l.toFinset) hne) := by
    rw [frameSourceMero_congr ω hω hface hne hsingle]
    exact differentialAlgebraicOver_frameSourceMero_singleton ω hω i hsingle
  have hprod := _root_.HTGeometry.differentialAlgebraicOver_neg_one_pow_mul
    (n := l.length) hbase
  have hsum := differentialAlgebraicOver_add hface' hprod
  simpa using hsum

end

end GaloisForLFunctions.HTGeometry
