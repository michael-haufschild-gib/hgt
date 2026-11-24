import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.GraphDiagonalWeights
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.ChartLocalAlgebra

/-! A zero of the graph weights has equal values under the two
pullbacks of every generator of the left normalized chart. -/

noncomputable section

open GlobalTheory.PD GlobalTheory.WH.WeightedChartSystem
open scoped TensorProduct

namespace GlobalTheory.WH

variable {k F E L κ : Type} [Field k] [Field F] [Field E] [Field L] [LinearOrder κ]
  [Algebra k F] [Algebra k E] [Algebra k L] [Algebra F E] [Algebra E L] [Algebra F L]
  [IsScalarTower k F E] [IsScalarTower k E L] [IsScalarTower k F L] [IsScalarTower F E L]
  {d : ℕ} {x : Fin (d + 1) → F} (h : IsPd k x) (j₂ : E →ₐ[k] L)
  {n : κ → ℕ × ℕ} {z : κ → E ⊗[k] E}
  (hz : NormalizedDiagonalEquations h n z)
  {I J : Finset (Fin (d + 1))} {i j : Fin (d + 1)} (hi : i ∈ I) (hj : j ∈ J)
  (e : RY x j₂ I J →ₐ[k] k)

abbrev graphAffineWeight (l : κ ⊕ₗ DiagonalIndex d) : L :=
  (graphChartSystem h j₂ 0 0).normalizedWeight (appendedDiagonalDegrees n)
    (graphScalarMap (IsScalarTower.toAlgHom k E L) j₂ ∘ appendedDiagonalWeights h 0 0 z) i j l

include hz hi hj in
theorem graphAffineWeight_mem (l : κ ⊕ₗ DiagonalIndex d) :
    graphAffineWeight h j₂ (n := n) (z := z) (i := i) (j := j) l ∈ RY x j₂ I J :=
  (graphChartSystem h j₂ 0 0).normalizedWeight_mem (graphChartSystem_good h j₂ 0 0)
    (graphChartSystem_admitted_map h j₂ 0 0 _ _ (appendedDiagonal_admitted h 0 0 hz)) hi hj l

/-- The equations of the graph imply that every function regular on
the left chart has the same local value under the two pullbacks. -/
theorem equal_localValues_of_graphWeights_zero
    (he : ∀ l, e ⟨_, graphAffineWeight_mem h j₂ hz hi hj l⟩ = 0) :
    ∀ b ∈ rB k E x {i}, ∃ c, Val (RY x j₂ I J) e (algebraMap E L b) c ∧
      Val (RY x j₂ I J) e (j₂ b) c := by
  let B := RY x j₂ I J
  let C := loc B e
  let ev := locEval B e
  let inc := Subalgebra.inclusion (le_loc B e)
  have hinc (b : B) : ev (inc b) = e b := locEval_inclusion B e b
  have hleft : rB k L x I ≤ B := le_sup_left
  have hright : (rB k E x J).map j₂ ≤ B := (rB_map_le_R2 j₂ (x := x) J).trans le_sup_right
  let α : B := ⟨algebraMap F L (x j / x i), hleft (chartRatio_mem_rB hi j)⟩
  let β : B := ⟨j₂ (algebraMap F E (x i / x j)),
    hright ⟨algebraMap F E (x i / x j), chartRatio_mem_rB hj i, rfl⟩⟩
  have hzero := he (toLex (Sum.inr (toLex (i, j))))
  have hminor : graphAffineWeight h j₂ (n := n) (z := z) (i := i) (j := j)
      (toLex (Sum.inr (toLex (i, j)))) = (1 : L) - (α : L) * (β : L) := by
    rw [graphAffineWeight, graph_normalizedMinor]
    have hX : algebraMap F L (x i) ≠ 0 := (map_ne_zero _).mpr (h.ne i)
    have hY : j₂ (algebraMap F E (x j)) ≠ 0 := (map_ne_zero _).mpr ((map_ne_zero _).mpr (h.ne j))
    rw [div_self hX, div_self hY, one_mul]
    simp only [α, β, map_div₀]
  have hαβ : e α * e β = 1 := by
    have hval : e ⟨_, graphAffineWeight_mem h j₂ hz hi hj (toLex (Sum.inr (toLex (i, j))))⟩ =
        e (1 - α * β) := congrArg e (Subtype.ext hminor)
    rw [hzero, map_sub, map_one, map_mul] at hval
    exact (sub_eq_zero.mp hval.symm).symm
  have hβ : ev (inc β) ≠ 0 := by
    rw [hinc]
    exact right_ne_zero_of_mul_eq_one hαβ
  let u := (isUnit_loc_of_eval_ne_zero B e (inc β) hβ).unit
  have hu : (u : C) = inc β := (isUnit_loc_of_eval_ne_zero B e (inc β) hβ).unit_spec
  let K (b : E) := ∃ v w : C,
    (v : L) = algebraMap E L b ∧ (w : L) = j₂ b ∧ ev v = ev w
  have hgen : ∀ b ∈ {b : E | b ∈ rB k E x {i} ∧ ∃ l N, n l = (N, N) ∧
      z l = (((normalizedDiagonalSystem (E := E) h 0 0).X i ^ N *
        (normalizedDiagonalSystem (E := E) h 0 0).Y i ^ N : (E ⊗[k] E)ˣ) : E ⊗[k] E) *
        (b ⊗ₜ[k] (1 : E) - (1 : E) ⊗ₜ[k] b)}, K b := by
    rintro b ⟨hb, l, N, hN, hzl⟩
    have hbl : algebraMap E L b ∈ rB k L x I :=
      rB_mono (Finset.singleton_subset_iff.mpr hi) ((show IsIntegral (rA k x {i}) b from hb).algebraMap)
    let v : C := inc ⟨_, hleft hbl⟩
    have hbij : b ∈ rB k E x {i, j} := rB_mono
      (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self i {j})) hb
    obtain ⟨M, hM⟩ := h.exists_pow_mul_mem_rB i j b hbij
    let b₀ : B := ⟨j₂ (algebraMap F E (x i / x j) ^ M * b),
      hright ⟨_, rB_mono (Finset.singleton_subset_iff.mpr hj) hM, rfl⟩⟩
    let w : C := ↑(u⁻¹ ^ M) * inc b₀
    have hbu : (((u⁻¹ : Cˣ) : C) : L) * (β : L) = 1 := by
      have hh : ((u⁻¹ : Cˣ) : C) * (u : C) = 1 := Units.inv_mul u
      have he := congrArg (fun a : C => (a : L)) hh
      rw [Subalgebra.coe_mul, Subalgebra.coe_one, hu] at he
      change (((u⁻¹ : Cˣ) : C) : L) * (β : L) = 1 at he
      exact he
    have hw : (w : L) = j₂ b := by
      change (((u⁻¹ ^ M : Cˣ) : C) : L) * j₂ (algebraMap F E (x i / x j) ^ M * b) = j₂ b
      rw [Units.val_pow_eq_pow_val, Subalgebra.coe_pow, map_mul, map_pow]
      change _ ^ M * ((β : L) ^ M * j₂ b) = j₂ b
      rw [← mul_assoc, ← mul_pow, hbu, one_pow, one_mul]
    let a : B := ⟨_, graphAffineWeight_mem h j₂ hz hi hj (toLex (Sum.inl l))⟩
    have ha : (inc a : C) = (inc β) ^ N * (v - w) := by
      apply Subtype.ext
      change (a : L) = (β : L) ^ N * ((v : L) - (w : L))
      rw [hw]
      change (a : L) = (β : L) ^ N * (algebraMap E L b - j₂ b)
      have heq := graph_normalizedGenerator h j₂ 0 0 n z i j l N b hN hzl
      simpa only [a, graphAffineWeight, β, map_div₀] using heq
    have hev := congrArg ev ha
    rw [hinc, show e a = 0 from he _, map_mul, map_pow, map_sub] at hev
    refine ⟨v, w, rfl, hw, sub_eq_zero.mp ((mul_eq_zero.mp hev.symm).resolve_left (pow_ne_zero _ hβ))⟩
  have hall (b : E) (hb : b ∈ rB k E x {i}) : K b := by
    rw [← hz.generates i] at hb
    induction hb using Algebra.adjoin_induction with
    | mem b hb => exact hgen b hb
    | algebraMap c =>
      refine ⟨algebraMap k C c, algebraMap k C c, ?_, ?_, rfl⟩
      · exact (IsScalarTower.algebraMap_apply k E L c)
      · exact (j₂.commutes c).symm
    | add a b _ _ ha hb =>
      obtain ⟨v, w, hv, hw, he⟩ := ha
      obtain ⟨v', w', hv', hw', he'⟩ := hb
      exact ⟨v + v', w + w', by simp only [Subalgebra.coe_add, map_add, hv, hv'],
        by simp only [Subalgebra.coe_add, map_add, hw, hw'], by simp only [map_add, he, he']⟩
    | mul a b _ _ ha hb =>
      obtain ⟨v, w, hv, hw, he⟩ := ha
      obtain ⟨v', w', hv', hw', he'⟩ := hb
      exact ⟨v * v', w * w', by simp only [Subalgebra.coe_mul, map_mul, hv, hv'],
        by simp only [Subalgebra.coe_mul, map_mul, hw, hw'], by simp only [map_mul, he, he']⟩
  intro b hb
  obtain ⟨v, w, hv, hw, hew⟩ := hall b hb
  refine ⟨ev v, ?_, ?_⟩
  · rw [← hv]
    exact (val_iff_loc B e _ _).mpr ⟨v.property, rfl⟩
  · rw [← hw]
    exact (val_iff_loc B e _ _).mpr ⟨w.property, hew.symm⟩

end GlobalTheory.WH
