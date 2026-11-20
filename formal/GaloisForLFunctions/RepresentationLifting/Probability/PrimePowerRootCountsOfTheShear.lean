import GaloisForLFunctions.RepresentationLifting.Probability.TheTwoRootTubesOfASplitQuadratic
import GaloisForLFunctions.RHTower.ReducedFrequencyMobiusAliasCollapse

/-!
# Prime-power root counts of the arithmetic shear

The fixed-gap shear uses the literal roots of r(r+g) modulo q. At q=p^h
its root count factors through only ceil(h/2) digits of the gap. Distinct
root tubes contribute two equal fibres and a merged tube contributes one
larger fibre. This extends the prime-modulus count to all prime powers.
-/

namespace GaloisForLFunctions.RepresentationLifting
open RHTower Metric
noncomputable section
variable (p : ℕ) [Fact p.Prime]

/-- Number of roots in the finite shear with a p-adic gap. -/
def padicGapRootCount (h : ℕ) (g : ℤ_[p]) : ℕ :=
  Nat.card {x : ZMod (p^h) // x*(x+PadicInt.toZModPow h g)=0}

private theorem shear_as_two_centers (h : ℕ) (g : ℤ_[p]) :
    let f := PadicInt.toZModPow (p:=p) h
    padicGapRootCount p h g = Nat.card {x : ZMod (p^h) // (x-f 0)*(x-f (-g))=0} := by
  simp only [padicGapRootCount,map_zero,sub_zero,map_neg,sub_neg_eq_add]

/-- Exact root count throughout the integral parameter space. The branch
at precision ceil(h/2) includes the zero gap at every prime. -/
theorem padicGapRootCount_eq (h : ℕ) (g : ℤ_[p]) :
    padicGapRootCount p h g = if PadicInt.toZModPow ((h+1)/2) g=0 then p^(h/2)
      else 2*p^g.valuation := by
  let J := (h+1)/2
  have hp : 1<(p:ℝ) := by exact_mod_cast (Fact.out : p.Prime).one_lt
  split
  · rename_i hg
    rw [shear_as_two_centers]
    exact card_double_quadratic_residues p 0 (-g) h (by rw [map_zero,map_neg,hg,neg_zero])
  · rename_i hg
    have hg₀ : g≠0 := fun he => hg (by rw [he,map_zero])
    have hj : g.valuation<J := by
      have hnorm := lt_of_not_ge (fun he => hg ((OperatorKernels.padicProjection_eq_zero_iff_norm_le p g J).mpr he))
      rw [PadicInt.norm_eq_zpow_neg_valuation hg₀,zpow_lt_zpow_iff_right₀ hp] at hnorm
      exact_mod_cast neg_lt_neg_iff.mp hnorm
    let k := h-g.valuation
    have hsep : g.valuation<k := by dsimp only [k,J] at *; omega
    have he : k+g.valuation=h := by omega
    have hd : dist (0:ℤ_[p]) (-g) = (p:ℝ)^(-(g.valuation:ℤ)) := by
      rw [dist_zero_left,norm_neg,PadicInt.norm_eq_zpow_neg_valuation hg₀]
    have hc := card_separated_quadratic_residues p 0 (-g) hsep hd
    rw [he] at hc
    exact (shear_as_two_centers p h g).trans hc

/-- Congruent half-precision gaps give the same entire root count,
regardless of the higher digits of either gap. -/
theorem padicGapRootCount_factors_through_half (h : ℕ) (a b : ℤ_[p])
    (he : PadicInt.toZModPow ((h+1)/2) a=PadicInt.toZModPow ((h+1)/2) b) :
    padicGapRootCount p h a=padicGapRootCount p h b := by
  let J := (h+1)/2
  rw [padicGapRootCount_eq,padicGapRootCount_eq,he]
  by_cases hb : PadicInt.toZModPow J b=0
  · rw [if_pos hb,if_pos hb]
  · rw [if_neg hb,if_neg hb]
    have hb₀ : b≠0 := fun h => hb (by rw [h,map_zero])
    have ha₀ : a≠0 := fun h => hb (by rw [←he,h,map_zero])
    have hdist : dist a b≤(p:ℝ)^(-(J:ℤ)) := by
      rw [dist_eq_norm,←OperatorKernels.padicProjection_eq_zero_iff_norm_le,map_sub,sub_eq_zero]
      exact he
    have hnorm : (p:ℝ)^(-(J:ℤ))<‖b‖ :=
      lt_of_not_ge fun hh => hb ((OperatorKernels.padicProjection_eq_zero_iff_norm_le p b J).mpr hh)
    have hd : dist a b<dist b 0 := by simpa only [dist_zero_right] using hdist.trans_lt hnorm
    have ht := IsUltrametricDist.dist_eq_max_of_dist_ne_dist a b 0 hd.ne
    rw [max_eq_right hd.le,dist_zero_right,dist_zero_right,PadicInt.norm_eq_zpow_neg_valuation ha₀,
      PadicInt.norm_eq_zpow_neg_valuation hb₀] at ht
    have hp : (1:ℝ)<p := by exact_mod_cast (Fact.out : p.Prime).one_lt
    have hv := (zpow_right_injective₀ (zero_lt_one.trans hp) hp.ne') ht
    rw [show a.valuation=b.valuation by omega]

private theorem arithmetic_shear_eq (h : ℕ) (g : ℤ) :
    _root_.RHTower.quadraticCongruenceRootCountTotal (p^h) g = padicGapRootCount p h (g:ℤ_[p]) := by
  have hp := pow_ne_zero h (Fact.out : p.Prime).ne_zero
  rw [_root_.RHTower.quadraticCongruenceRootCountTotal_of_ne_zero hp]
  unfold _root_.RHTower.quadraticCongruenceRootCount padicGapRootCount
  rw [map_intCast,←Nat.card_eq_fintype_card]
  rfl

/-- Prime-power local factor of the corpus's quadratic-congruence
arithmetic function, with ordinary integer divisibility as the cutoff. -/
theorem arithmetic_shear_root_count (h : ℕ) (g : ℤ) :
    _root_.RHTower.quadraticCongruenceRootCountTotal (p^h) g =
      if (p:ℤ)^((h+1)/2)∣g then p^(h/2) else 2*p^(g:ℤ_[p]).valuation := by
  simp only [arithmetic_shear_eq,padicGapRootCount_eq,map_intCast,ZMod.intCast_zmod_eq_zero_iff_dvd,Nat.cast_pow]

/-- All higher digits of the integer gap disappear from the shear
root count at modulus p^h. -/
theorem arithmetic_shear_half_period (h : ℕ) (g v : ℤ) :
    _root_.RHTower.quadraticCongruenceRootCountTotal (p^h) (g+(p:ℤ)^((h+1)/2)*v) =
      _root_.RHTower.quadraticCongruenceRootCountTotal (p^h) g := by
  rw [arithmetic_shear_eq,arithmetic_shear_eq]
  apply padicGapRootCount_factors_through_half
  simp only [map_add,map_mul,map_pow,map_natCast,map_intCast,Int.cast_add,Int.cast_mul,Int.cast_pow,Int.cast_natCast]
  rw [←Nat.cast_pow,ZMod.natCast_self,zero_mul,add_zero]

#print axioms padicGapRootCount_eq
#print axioms padicGapRootCount_factors_through_half
#print axioms arithmetic_shear_root_count
#print axioms arithmetic_shear_half_period
end
end GaloisForLFunctions.RepresentationLifting
