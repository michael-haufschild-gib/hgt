import GaloisForLFunctions.BiScaleUncertainty.ArithmeticEdgeResonance
import GaloisForLFunctions.BiScaleUncertainty.FourEdgeQuarticRelations

/-!
# Exact quartic ambiguity on arithmetic edge support

For sieve coordinates supported on twice-products of coprime odd blocks,
the complete fourth lag array is equivalent to coordinate squares and the
explicit triangle and four-cycle equations. An arbitrary competing sieve
signal is forced onto the same allowed arithmetic support.
-/

open scoped BigOperators
open Finset ZMod
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ArithmeticEdges
open AffineSieve
set_option autoImplicit false
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

namespace Blocks
variable {V : Type*} (D : Blocks V)

/-- Sieve coordinates viewed on the simple arithmetic edge support. -/
def edgeCoord (N : ℕ) (c : ℕ → ℝ) (u v : V) : ℝ := by
  classical
  exact if u = v then 0 else selbergMultiplesCoord N c (D.order u v)

theorem edgeCoord_symm (N : ℕ) (c : ℕ → ℝ) (u v : V) :
    D.edgeCoord N c u v = D.edgeCoord N c v u := by
  classical
  by_cases huv : u = v
  · subst v
    rfl
  · simp only [edgeCoord,if_neg huv,if_neg (Ne.symm huv),D.order_symm]

/-- Every nonzero coordinate lies at an order of a nonloop edge. -/
def EdgeSupported (N : ℕ) (c : ℕ → ℝ) : Prop :=
  ∀ q, (¬ ∃ u v, u ≠ v ∧ q = D.order u v) → selbergMultiplesCoord N c q = 0

/-- Fourth lag arrays give the explicit edge equations without support assumptions. -/
theorem relations_of_fourth_moments (N : ℕ) (hN : 2 ≤ N)
    (hmem : ∀ v, D.value v ∈ Finset.Icc 1 N) (c e : ℕ → ℝ)
    (hm : ∀ h : Fin 4 → ℕ, translatedMoment N c h = translatedMoment N e h) :
    QuarticRelations (D.edgeCoord N c) (D.edgeCoord N e) := by
  classical
  constructor
  · intro u v
    by_cases huv : u = v
    · simp [edgeCoord,huv]
    · simpa only [edgeCoord,if_neg huv] using coordinate_squares_of_fourth_moments N c e hm (D.order u v)
  · intro u v w
    by_cases huv : u = v
    · subst v; simp [edgeCoord]
    by_cases huw : u = w
    · subst w; simp [edgeCoord]
    by_cases hvw : v = w
    · subst w; simp [edgeCoord]
    simpa only [edgeCoord,if_neg huv,if_neg huw,if_neg hvw,order] using
      triangle_products_of_fourth_moments hN (D.odd u) (D.odd v) (D.odd w)
        (hmem u) (hmem v) (hmem w) (D.coprime u v huv) (D.coprime u w huw)
        (D.coprime v w hvw) c e hm
  · intro u v w z
    by_cases huv : u = v
    · subst v; simp [edgeCoord]
    by_cases hvw : v = w
    · subst w; simp [edgeCoord]
    by_cases hwz : w = z
    · subst z; simp [edgeCoord]
    by_cases hzu : z = u
    · subst z; simp [edgeCoord]
    simpa only [edgeCoord,if_neg huv,if_neg hvw,if_neg hwz,if_neg hzu,order] using
      cycle_products_of_fourth_moments hN (D.odd u) (D.odd v) (D.odd w) (D.odd z)
        (hmem u) (hmem v) (hmem w) (hmem z) (D.coprime u v huv) (D.coprime v w hvw)
        (D.coprime w z hwz) (D.coprime z u hzu) c e hm

private theorem noSingleton4_of_resonance (N : ℕ) (r : Fin 4 → ZMod N.factorial)
    (u v : Fin 4 → V) (ho : ∀ i, addOrderOf (r i) = D.order (u i) (v i))
    (hz : (∑ i, r i) = 0) : NoSingleton4 (u 0) (v 0) (u 1) (v 1) (u 2) (v 2) (u 3) (v 3) := by
  intro w
  refine ⟨?_,?_,?_,?_⟩
  · intro hw
    obtain ⟨i,hi,hwi⟩ := D.resonance_vertex_repeats r u v ho hz 0 w hw
    fin_cases i
    · exact (hi rfl).elim
    all_goals tauto
  · intro hw
    obtain ⟨i,hi,hwi⟩ := D.resonance_vertex_repeats r u v ho hz 1 w hw
    fin_cases i
    · tauto
    · exact (hi rfl).elim
    all_goals tauto
  · intro hw
    obtain ⟨i,hi,hwi⟩ := D.resonance_vertex_repeats r u v ho hz 2 w hw
    fin_cases i
    · tauto
    · tauto
    · exact (hi rfl).elim
    · tauto
  · intro hw
    obtain ⟨i,hi,hwi⟩ := D.resonance_vertex_repeats r u v ho hz 3 w hw
    fin_cases i
    · tauto
    · tauto
    · tauto
    · exact (hi rfl).elim

/-- The explicit edge relations determine the entire fourth lag array. -/
theorem fourth_moments_of_relations (N : ℕ) (c e : ℕ → ℝ)
    (hc : D.EdgeSupported N c) (he : D.EdgeSupported N e)
    (H : QuarticRelations (D.edgeCoord N c) (D.edgeCoord N e)) :
    ∀ h : Fin 4 → ℕ, translatedMoment N c h = translatedMoment N e h := by
  classical
  apply (moments_eq_iff_resonant_products N c e 4).2
  intro r hz
  by_cases hs : ∀ i, ∃ u v, u ≠ v ∧ addOrderOf (r i) = D.order u v
  · choose u v hne ho using hs
    have hn := D.noSingleton4_of_resonance N r u v ho hz
    have hh := quartic_relations_complete (D.edgeCoord_symm N c) (D.edgeCoord_symm N e) H
      (u 0) (v 0) (u 1) (v 1) (u 2) (v 2) (u 3) (v 3)
      (hne 0) (hne 1) (hne 2) (hne 3) hn
    simpa only [Agree4,edgeCoord,if_neg (hne 0),if_neg (hne 1),if_neg (hne 2),
      if_neg (hne 3),Fin.prod_univ_four,ho] using hh
  · push Not at hs
    obtain ⟨i,hi⟩ := hs
    have hnot : ¬ ∃ u v, u ≠ v ∧ addOrderOf (r i) = D.order u v := by
      rintro ⟨u,v,huv,ho⟩
      exact hi u v huv ho
    have hc0 : (∏ i, selbergMultiplesCoord N c (addOrderOf (r i))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (hc _ hnot)
    have he0 : (∏ i, selbergMultiplesCoord N e (addOrderOf (r i))) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) (he _ hnot)
    rw [hc0,he0]

/-- Every arbitrary sieve competitor is classified by support and the explicit edge equations. -/
theorem fourth_moments_iff (N : ℕ) (hN : 2 ≤ N)
    (hmem : ∀ v, D.value v ∈ Finset.Icc 1 N) (c e : ℕ → ℝ)
    (hc : D.EdgeSupported N c) :
    (∀ h : Fin 4 → ℕ, translatedMoment N c h = translatedMoment N e h) ↔
      D.EdgeSupported N e ∧ QuarticRelations (D.edgeCoord N c) (D.edgeCoord N e) := by
  constructor
  · intro hm
    refine ⟨?_,D.relations_of_fourth_moments N hN hmem c e hm⟩
    intro q hq
    have hs := coordinate_squares_of_fourth_moments N c e hm q
    rw [hc q hq] at hs
    nlinarith only [hs]
  · rintro ⟨he,H⟩
    exact D.fourth_moments_of_relations N c e hc he H

end Blocks
end GaloisForLFunctions.BiScaleUncertainty.SieveMoments.ArithmeticEdges
