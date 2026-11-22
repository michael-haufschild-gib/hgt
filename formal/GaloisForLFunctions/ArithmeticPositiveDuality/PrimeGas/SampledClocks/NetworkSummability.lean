import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.Networks
import GaloisForLFunctions.HTGeometry.ExponentialLatticeWeight

/-!
# Heat summability with sampled edge clocks

The minimum label of each connected component supplies its zeta weight.
The remaining energy controls a summable geometric weight for every
integer winding, even when different edges use incommensurate times.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.Network

open CopyExchange
open scoped Classical

variable {I E : Type*} [Fintype I] [Fintype E] (G : Network I E)

def Domain (s : ℂ) : Prop := ∀ c : G.Component, 1 < (G.size c : ℝ)*s.re

private def excess (x : I → ℕ+) (i : I) : ℝ :=
  energy (x i) - energy (G.lowest x (G.component i))

omit [Fintype E] in
private theorem excess_nonneg (x : I → ℕ+) (i : I) : 0 ≤ G.excess x i :=
  sub_nonneg.mpr (G.lowest_le x i)

private def spacing (e : G.Active) : ℝ := |2*Real.pi/G.time e|

omit [Fintype I] [Fintype E] in
private theorem spacing_pos (e : G.Active) : 0 < G.spacing e :=
  abs_pos.mpr (div_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) e.property)

private def divisor : ℝ := (Fintype.card G.Active : ℝ) + 1

omit [Fintype I] in
private theorem divisor_pos : 0 < G.divisor := by unfold divisor; positivity

omit [Fintype E] in
/-- Each edge consumes at most the entire energy above the component minima. -/
private theorem edge_cost (x : G.Word) (e : G.Active) :
    |(G.winding x e : ℝ)| * G.spacing e ≤ ∑ i, G.excess x.val i := by
  have hgap : energy (x.val (G.src e)) - energy (x.val (G.dst e)) =
      G.excess x.val (G.src e) - G.excess x.val (G.dst e) := by
    simp only [excess,G.component_edge e]
    ring
  change |(G.winding x e : ℝ)| * |2*Real.pi/G.time e| ≤ _
  rw [← abs_mul,← G.winding_eq x e,hgap,abs_sub_le_iff]
  have hb (i : I) := Finset.single_le_sum (s := Finset.univ)
    (fun j _ => G.excess_nonneg x.val j) (Finset.mem_univ i)
  exact ⟨(sub_le_self _ (G.excess_nonneg _ _)).trans (hb _),
    (sub_le_self _ (G.excess_nonneg _ _)).trans (hb _)⟩

private theorem total_cost (x : G.Word) :
    (∑ e, |(G.winding x e : ℝ)| * G.spacing e) / G.divisor ≤ ∑ i, G.excess x.val i := by
  apply (div_le_iff₀ G.divisor_pos).mpr
  calc
    _ ≤ ∑ _e : G.Active, ∑ i, G.excess x.val i := Finset.sum_le_sum fun e _ => G.edge_cost x e
    _ = (Fintype.card G.Active : ℝ) * ∑ i, G.excess x.val i := by simp
    _ ≤ (∑ i, G.excess x.val i) * G.divisor := by
      have hp := Finset.sum_nonneg (s := Finset.univ) fun i _ => G.excess_nonneg x.val i
      unfold divisor
      linarith only [hp]

private def latticeWeight (σ : ℝ) (e : G.Active) (k : ℤ) :=
  Real.exp ((-σ/G.divisor) * (|(k : ℝ)| * G.spacing e))

omit [Fintype I] in
private theorem winding_summable (σ : ℝ) (hσ : 0 < σ) :
    Summable (fun k : G.Active → ℤ => ∏ e, G.latticeWeight σ e (k e)) := by
  let w (e : G.Active) (k : ℤ) : ℂ := (G.latticeWeight σ e k : ℝ)
  have hn (e : G.Active) (k : ℤ) : ‖w e k‖ = G.latticeWeight σ e k :=
    Complex.norm_real _ |>.trans (Real.norm_of_nonneg (Real.exp_pos _).le)
  have hw (e : G.Active) : Summable (fun k => ‖w e k‖) := by
    simp only [hn]
    refine (HTGeometry.summable_exp_neg_abs_int (div_pos (mul_pos hσ (G.spacing_pos e)) G.divisor_pos)).congr fun k => ?_
    unfold latticeWeight
    congr 1
    ring
  have h := (FamilyContinuationTheory.hasSum_pi_prod w (fun e => ∑' k, w e k)
    (fun e => (hw e).of_norm.hasSum) hw).2
  simpa only [norm_prod,hn] using h

theorem wordHeat_norm (s : ℂ) (x : I → ℕ+) :
    ‖wordHeat s x‖ = Real.exp (-s.re * ∑ i, energy (x i)) := by
  simp only [wordHeat,norm_prod,norm_heat,Finset.mul_sum,Real.exp_sum]

private theorem weight_bound (s : ℂ) (hσ : 0 ≤ s.re) (x : G.Word) :
    ‖wordHeat s x.val‖ ≤ ‖wordHeat s (G.flat (G.lowest x.val)).val‖ *
      ∏ e, G.latticeWeight s.re e (G.winding x e) := by
  have he : (∑ i, energy (x.val i)) =
      (∑ i, energy (G.lowest x.val (G.component i))) + ∑ i, G.excess x.val i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp [excess]
  rw [wordHeat_norm,wordHeat_norm]
  change Real.exp _ ≤ Real.exp (-s.re * ∑ i, energy (G.lowest x.val (G.component i))) * _
  simp only [latticeWeight,← Real.exp_sum,← Real.exp_add,← Finset.mul_sum,Real.exp_le_exp]
  rw [he,mul_add]
  apply add_le_add le_rfl
  exact (mul_le_mul_of_nonpos_left (G.total_cost x) (neg_nonpos.mpr hσ)).trans_eq (by ring)

omit [Fintype E] in
private theorem flat_summable (s : ℂ) :
    (Summable fun u => ‖wordHeat s (G.flat u).val‖) ↔ G.Domain s := by
  simp only [flat_heat,independent_heat_summable_iff,Domain,Complex.mul_re,Complex.natCast_re,
    Complex.natCast_im,zero_mul,sub_zero]

/-- Sampled clocks have exactly one convergence inequality per active connected component. -/
theorem summable_iff (s : ℂ) :
    (Summable fun x : G.Word => ‖wordHeat s x.val‖) ↔ G.Domain s := by
  constructor
  · intro h
    exact (G.flat_summable s).mp (h.comp_injective G.flat_injective)
  · intro h
    cases isEmpty_or_nonempty I with
    | inl hempty => exact Summable.of_finite
    | inr hnonempty =>
      let c := G.component (Classical.arbitrary I)
      have hσ : 0 < s.re := by
        by_contra! hn
        have hp : 0 ≤ (G.size c : ℝ) := Nat.cast_nonneg _
        linarith only [h c,mul_nonpos_of_nonneg_of_nonpos hp hn]
      have hf := (G.flat_summable s).mpr h
      have hw := G.winding_summable s.re hσ
      have hj := hf.mul_of_nonneg hw (fun _ => norm_nonneg _)
        (fun _ => Finset.prod_nonneg fun _ _ => (Real.exp_pos _).le)
      let envelope (u : (G.Component → ℕ+) × (G.Active → ℤ)) :=
        ‖wordHeat s (G.flat u.1).val‖ * ∏ e, G.latticeWeight s.re e (u.2 e)
      have hs : Summable envelope := hj
      have hc : Summable (envelope ∘ G.coordinates) :=
        hs.comp_injective (i := G.coordinates) G.coordinates_injective
      exact Summable.of_nonneg_of_le (f := envelope ∘ G.coordinates)
        (fun _ => norm_nonneg _) (G.weight_bound s hσ.le) hc

#print axioms wordHeat_norm
#print axioms summable_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.Network
