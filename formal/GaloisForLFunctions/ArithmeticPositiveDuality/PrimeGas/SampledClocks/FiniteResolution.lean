import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.ReadoutCover
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.NetworkSummability
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks.HeatSectors

/-!
# Compact observations at positive resolution leave the heat boundary unchanged

Hold all components but one at a reference integer. Vary the remaining
component within a ball of profiles around that reference. Finitely many
such balls cover every label, so the individual zeta inequality survives.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks

open CopyExchange
open scoped Classical

variable {I E F : Type*} {K : F → Type*} [∀ j, PseudoMetricSpace (K j)]
variable (G : Network I E) (R : Readout I F K)

def Accepted (x : I → ℕ+) : Prop := G.Resonant x ∧ R.Passes x

private def vary (c : G.Component) (m n : ℕ+) : G.Component → ℕ+ :=
  Function.update (fun _ => m) c n

private theorem vary_passes (c : G.Component) (m n : ℕ+) (hn : R.near n m) :
    R.Passes (G.flat (vary G c m n)).val := by
  intro j
  change dist (R.value j (vary G c m n (G.component (R.left j))))
    (R.value j (vary G c m n (G.component (R.right j)))) < _
  by_cases hl : G.component (R.left j) = c <;> by_cases hr : G.component (R.right j) = c
  · simpa only [hl,hr,vary,Function.update_self,dist_self] using (R.radius j).property
  · simpa only [hl,vary,Function.update_self,Function.update_of_ne hr] using hn j
  · simpa only [hr,vary,Function.update_self,Function.update_of_ne hl] using R.near_symm hn j
  · simpa only [vary,Function.update_of_ne hl,Function.update_of_ne hr,dist_self] using (R.radius j).property

private def line (c : G.Component) (m : ℕ+) (n : {n // R.near n m}) : {x // Accepted G R x} :=
  ⟨(G.flat (vary G c m n.val)).val,(G.flat _).property,vary_passes G R c m n.val n.property⟩

private theorem line_injective (c : G.Component) (m : ℕ+) : Function.Injective (line G R c m) := by
  intro a b h
  obtain ⟨i,hi⟩ := G.component_surjective c
  have he := congrArg (fun x : {x // Accepted G R x} => x.val i) h
  change vary G c m a.val (G.component i) = vary G c m b.val (G.component i) at he
  exact Subtype.ext (by simpa only [hi,vary,Function.update_self] using he)

variable [Fintype I]

private def otherHeat (s : ℂ) (c : G.Component) (m : ℕ+) :=
  ∏ j ∈ Finset.univ.erase c, heat ((G.size j : ℂ)*s) m

private theorem otherHeat_ne_zero (s : ℂ) (c : G.Component) (m : ℕ+) : otherHeat G s c m ≠ 0 :=
  Finset.prod_ne_zero_iff.mpr fun _ _ => Complex.exp_ne_zero _

private theorem line_heat (s : ℂ) (c : G.Component) (m : ℕ+) (n : {n // R.near n m}) :
    wordHeat s (line G R c m n).val = heat ((G.size c : ℂ)*s) n.val * otherHeat G s c m := by
  change wordHeat s (G.flat (vary G c m n.val)).val = _
  rw [G.flat_heat,← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ c)]
  simp only [vary,Function.update_self]
  apply congrArg (fun w => heat ((G.size c : ℂ)*s) n.val * w)
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]

private theorem cell_summable (s : ℂ) (h : AbsoluteHeat (Accepted G R) s) (c : G.Component) (m : ℕ+) :
    Summable (fun n : {n // R.near n m} => ‖heat ((G.size c : ℂ)*s) n.val‖) := by
  have hs := (h.comp_injective (i := line G R c m) (line_injective G R c m)).mul_right ‖otherHeat G s c m‖⁻¹
  refine hs.congr fun n => ?_
  change ‖wordHeat s (line G R c m n).val‖ * _ = _
  rw [line_heat,norm_mul,mul_assoc,mul_inv_cancel₀ (norm_ne_zero_iff.mpr (otherHeat_ne_zero G s c m)),mul_one]

private theorem recover_component [Fintype F] [∀ j, CompactSpace (K j)] (s : ℂ)
    (h : AbsoluteHeat (Accepted G R) s) (c : G.Component) : 1 < (G.size c : ℝ)*s.re := by
  let t : ℂ := (G.size c : ℂ)*s
  let w (n : ℕ+) := ‖heat t n‖
  let cell (m : ℕ+) : Set ℕ+ := {n | R.near n m}
  obtain ⟨S,hS⟩ := R.exists_centers
  have hi (m : ℕ+) : Summable ((cell m).indicator w) :=
    summable_subtype_iff_indicator.mp (cell_summable G R s h c m)
  have hj : Summable fun n => ∑ m ∈ S, (cell m).indicator w n :=
    summable_sum fun m _ => hi m
  have hs : Summable w := by
    refine Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun n => ?_) hj
    obtain ⟨m,hm,hn⟩ := hS n
    have hnn (a : ℕ+) : 0 ≤ (cell a).indicator w n :=
      Set.indicator_nonneg (fun _ _ => norm_nonneg _) _
    have hb := Finset.single_le_sum (s := S) (fun a _ => hnn a) hm
    rw [Set.indicator_of_mem (show n ∈ cell m from hn)] at hb
    exact hb
  simpa only [t,Complex.mul_re,Complex.natCast_re,Complex.natCast_im,zero_mul,sub_zero] using
    (heat_abs_summable t).mp hs

/-- Every finite family of positive-radius compact comparisons preserves the exact-clock domain. -/
theorem accepted_summable_iff [Fintype E] [Fintype F] [∀ j, CompactSpace (K j)] (s : ℂ) :
    AbsoluteHeat (Accepted G R) s ↔ G.Domain s := by
  constructor
  · exact fun h c => recover_component G R s h c
  · intro h
    let inc (x : {x // Accepted G R x}) : G.Word := ⟨x.val,x.property.1⟩
    have hi : Function.Injective inc := by
      intro a b he
      exact Subtype.ext (congrArg (fun v : G.Word => v.val) he)
    have hs := ((G.summable_iff s).mpr h).comp_injective (i := inc) hi
    exact hs

theorem accepted_heat_iff [Fintype E] [Fintype F] [∀ j, CompactSpace (K j)] (s : ℂ) :
    HasSectorHeat (Accepted G R) s ↔ G.Domain s :=
  (sectorHeat_iff _ s).trans (accepted_summable_iff G R s)

#print axioms accepted_summable_iff
#print axioms accepted_heat_iff

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.SampledClocks
