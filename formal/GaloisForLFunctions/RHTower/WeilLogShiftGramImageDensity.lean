import GaloisForLFunctions.RHTower.WeilLogShiftGramImage
import Mathlib.Analysis.Convex.Cone.Dual

/-!
# Single actual Gram tests are dense in the finite coefficient dual

Separated packets make the closure additive. Positive rescaling is exact.
Proper-cone separation would contradict the actual normalized certificate,
so the closure is the entire coefficient space.
-/

open scoped BigOperators
open Filter Topology

namespace RHTower

theorem denseRange_finiteWeilGramCoefficientVector (s : Finset ℕ) :
    DenseRange (finiteWeilGramCoefficientVector s) := by
  classical
  let R : Set (s → ℝ) := Set.range (finiteWeilGramCoefficientVector s)
  have hz : (0 : s → ℝ) ∈ closure R := by
    apply subset_closure
    refine ⟨⟨0, 0, 0, 0⟩, ?_⟩
    funext i
    simp only [finiteWeilGramCoefficientVector_apply, NNReal.coe_zero,
      neg_zero, zero_mul, Pi.zero_apply]
  have hsum (w z : FiniteWeilGramTest) :
      finiteWeilGramCoefficientVector s w + finiteWeilGramCoefficientVector s z ∈ closure R := by
    apply isClosed_closure.mem_of_tendsto
      (tendsto_finiteWeilGramCoefficientVector_separatedSum s w z)
    exact Eventually.of_forall fun T => subset_closure ⟨finiteWeilGramSeparatedSum w z T, rfl⟩
  have hleft (w : FiniteWeilGramTest) : ∀ y ∈ closure R,
      finiteWeilGramCoefficientVector s w + y ∈ closure R := by
    apply closure_minimal
    · rintro y ⟨z, rfl⟩
      exact hsum w z
    · exact isClosed_closure.preimage (continuous_const.add continuous_id)
  have hadd (x : s → ℝ) (hx : x ∈ closure R) (y : s → ℝ) (hy : y ∈ closure R) :
      x + y ∈ closure R := by
    have hsub : R ⊆ {z | z + y ∈ closure R} := by
      rintro z ⟨w, rfl⟩
      exact hleft w y hy
    exact closure_minimal hsub
      (isClosed_closure.preimage (continuous_id.add continuous_const)) hx
  have hsmul (a : ℝ) (ha : 0 ≤ a) (x : s → ℝ) (hx : x ∈ closure R) :
      a • x ∈ closure R := by
    have hsub : R ⊆ {z | a • z ∈ closure R} := by
      rintro z ⟨w, rfl⟩
      apply subset_closure
      exact ⟨finiteWeilGramScale ⟨a, ha⟩ w,
        finiteWeilGramCoefficientVector_scale s ⟨a, ha⟩ w⟩
    have hcont : Continuous (fun z : s → ℝ => a • z) :=
      continuous_const_smul a
    have hclosed : IsClosed {z : s → ℝ | a • z ∈ closure R} :=
      isClosed_closure.preimage hcont
    exact closure_minimal hsub hclosed hx
  let C : ProperCone ℝ (s → ℝ) :=
    { carrier := closure R
      zero_mem' := hz
      add_mem' := by intro x y hx hy; exact hadd x hx y hy
      smul_mem' := by intro a x hx; exact hsmul (a : ℝ) a.property x hx
      isClosed' := isClosed_closure }
  intro x
  by_contra hx
  obtain ⟨f, hf, hfx⟩ := C.hyperplane_separation_point hx
  let c : s → ℝ := fun i => f (Pi.single i 1)
  have hdecomp (v : s → ℝ) : f v = ∑ i, v i * c i := by
    have hv := congrArg f ((Pi.basisFun ℝ s).sum_repr v)
    simpa only [map_sum, map_smul, Pi.basisFun_repr, Pi.basisFun_apply, smul_eq_mul, c] using hv.symm
  have hc0 : c ≠ 0 := by
    intro hc
    have hv := hdecomp x
    rw [hc] at hv
    simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero] at hv
    linarith
  obtain ⟨tests, hcert⟩ := exists_finiteWeilGram_norm_certificate s
  obtain ⟨w, _, hneg⟩ := hcert c hc0
  have hnonneg := hf (finiteWeilGramCoefficientVector s w)
    (show finiteWeilGramCoefficientVector s w ∈ C from subset_closure ⟨w, rfl⟩)
  rw [hdecomp, ← finiteWeilGramCoefficientVector_pairing] at hnonneg
  linarith [norm_nonneg c]

end RHTower
