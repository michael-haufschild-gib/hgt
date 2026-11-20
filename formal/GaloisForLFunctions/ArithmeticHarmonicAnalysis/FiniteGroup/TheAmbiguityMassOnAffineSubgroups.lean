import GaloisForLFunctions.ArithmeticHarmonicAnalysis.FiniteGroup.PeakReadingsIdentifyTheAnnihilatorOfTheAmbiguitySupport

/-!
# Poisson summation on finite phase-space cosets

Summing the squared ambiguity function over a translated subgroup
leaves only frequencies in the symplectic annihilator. The remaining
phase factors measure the exact loss of mass under translation.
This is the finite coset counterpart of the Poisson test in
Di Fratta and Slastikov, Lemma 8.9.
-/
noncomputable section
open Finset Complex
open scoped ComplexConjugate Classical
namespace GaloisForLFunctions.ArithmeticHarmonicAnalysis
variable {q : ℕ} [NeZero q]
local notation "G" => ZMod q × ZMod q
local notation "χ" => (ZMod.stdAddChar : AddChar (ZMod q) ℂ)
local notation "W" => cyclicAmbiguityWeight

/-- Frequencies trivial on every point of the subgroup. -/
def symplecticDualSites (H : AddSubgroup G) : Finset G := by
  classical
  exact univ.filter (fun y => ∀ h : H, symplecticIndex h y=0)

/-- Ambiguity mass belonging to one coset. -/
def ambiguityCosetMass (c : ZMod q → ℂ) (H : AddSubgroup G) (z : G) : ℝ := by
  classical
  exact ∑ h : H,W c (z.1+h.val.1) (z.2+h.val.2)

private def restrictedPhase (H : AddSubgroup G) (y : G) : AddChar H ℂ where
  toFun h := χ (symplecticIndex h y)
  map_zero_eq_one' := by simp [symplecticIndex]
  map_add_eq_mul' h k := by
    change χ ((h.val.1+k.val.1)*y.2-(h.val.2+k.val.2)*y.1)=_
    rw [show (h.val.1+k.val.1)*y.2-(h.val.2+k.val.2)*y.1 =
      symplecticIndex h y+symplecticIndex k y by unfold symplecticIndex; ring,AddChar.map_add_eq_mul]

private theorem subgroup_phase_sum (H : AddSubgroup G) (y : G) :
    ∑ h : H,χ (symplecticIndex h y) =
      if y ∈ symplecticDualSites H then (Nat.card H:ℂ) else 0 := by
  classical
  change ∑ h : H,restrictedPhase H y h = _
  by_cases hy : y ∈ symplecticDualSites H
  · have he : restrictedPhase H y=1 := by
      ext h
      change χ (symplecticIndex h y)=1
      rw [(mem_filter.mp hy).2 h,AddChar.map_zero_eq_one]
    rw [if_pos hy,AddChar.sum_eq_card_of_eq_one he,Nat.card_eq_fintype_card]
  · have hn : restrictedPhase H y≠1 := by
      intro he
      apply hy
      apply mem_filter.mpr
      refine ⟨mem_univ _,fun h => ?_⟩
      have h1 := DFunLike.congr_fun he h
      apply ZMod.injective_stdAddChar
      simpa only [AddChar.map_zero_eq_one] using (show χ (symplecticIndex h y)=1 from h1)
    rw [if_neg hy,AddChar.sum_eq_zero_of_ne_one hn]

/-- Fourier weights on a translated subgroup, including the exact
cardinality factor at every (possibly composite) period. -/
theorem cyclic_ambiguity_coset_poisson (c : ZMod q → ℂ) (H : AddSubgroup G) (z : G) :
    (q:ℂ)*(ambiguityCosetMass c H z:ℂ) =
      (Nat.card H:ℂ)*∑ y ∈ symplecticDualSites H,
        (W c y.1 y.2:ℂ)*χ (symplecticIndex z y) := by
  classical
  have hpoint (h : H) : (q:ℂ)*(W c (z.1+h.val.1) (z.2+h.val.2):ℂ) =
      ∑ y : G,((W c y.1 y.2:ℂ)*χ (symplecticIndex z y))*χ (symplecticIndex h y) := by
    rw [←cyclic_ambiguity_self_fourier,Fintype.sum_prod_type]
    refine sum_congr rfl fun r _ => sum_congr rfl fun s _ => ?_
    rw [mul_assoc,←AddChar.map_add_eq_mul]
    congr 2
    unfold symplecticIndex; dsimp; ring
  rw [ambiguityCosetMass,Complex.ofReal_sum,mul_sum]
  simp_rw [hpoint]
  rw [sum_comm]
  simp_rw [←mul_sum,subgroup_phase_sum]
  rw [mul_sum]
  calc _ = ∑ y : G,if y ∈ symplecticDualSites H then
           (Nat.card H:ℂ)*((W c y.1 y.2:ℂ)*χ (symplecticIndex z y)) else 0 := by
         refine sum_congr rfl fun y _ => ?_
         split_ifs <;> ring
       _ = _ := by
         rw [←sum_filter]
         congr 1; ext y; simp

/-- The exact cosine loss on the annihilator. The neutral coset
maximizes mass, and the deficit retains all occupied dual phases. -/
theorem cyclic_ambiguity_coset_loss (c : ZMod q → ℂ) (H : AddSubgroup G) (z : G) :
    (q:ℝ)*(ambiguityCosetMass c H 0-ambiguityCosetMass c H z) =
      (Nat.card H:ℝ)*∑ y ∈ symplecticDualSites H,
        W c y.1 y.2*(1-(χ (symplecticIndex z y)).re) := by
  have h (x : G) := congrArg Complex.re (cyclic_ambiguity_coset_poisson c H x)
  have hz := h z
  have h0 := h 0
  simp only [Complex.mul_re,Complex.natCast_re,Complex.natCast_im,Complex.ofReal_re,
    Complex.ofReal_im,zero_mul,sub_zero,Complex.re_sum] at hz h0
  simp only [symplecticIndex,Prod.fst_zero,Prod.snd_zero,zero_mul,sub_zero,AddChar.map_zero_eq_one,
    Complex.one_re,mul_one] at h0
  rw [mul_sub,h0,hz,←mul_sub,←sum_sub_distrib]
  refine congrArg (fun x : ℝ => (Nat.card H:ℝ)*x) (sum_congr rfl fun y _ => ?_)
  ring

/-- A translation maximizes mass exactly when it fixes all phases of
the occupied annihilator frequencies. -/
theorem maximal_ambiguity_coset_iff (c : ZMod q → ℂ) (H : AddSubgroup G) (z : G) :
    ambiguityCosetMass c H z=ambiguityCosetMass c H 0 ↔
      ∀ y ∈ symplecticDualSites H, y ∈ ambiguitySupport c → symplecticIndex z y=0 := by
  classical
  have hphase (w : ZMod q) : (χ w).re ≤ 1 := by
    have he : ‖χ w‖=1 := by simp only [ZMod.stdAddChar_apply,Circle.norm_coe]
    exact (Complex.re_le_norm _).trans he.le
  have hr (y : G) : 0 ≤ W c y.1 y.2*(1-(χ (symplecticIndex z y)).re) :=
    mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (hphase _))
  have h := cyclic_ambiguity_coset_loss c H z
  have hc : 0 < (Nat.card H:ℝ) := Nat.cast_pos.mpr Nat.card_pos
  have hq : 0 < (q:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne q))
  constructor
  · intro he y hy hs
    rw [he,sub_self,mul_zero] at h
    have hz := (mul_eq_zero.mp h.symm).resolve_left hc.ne'
    have hterm := single_le_sum (fun y _ => hr y) hy
    rw [hz] at hterm
    have hW : 0 < W c y.1 y.2 := (mem_filter.mp hs).2
    have hgap := (mul_eq_zero.mp (le_antisymm hterm (hr y))).resolve_left hW.ne'
    have hre : (χ (symplecticIndex z y)).re=1 := (sub_eq_zero.mp hgap).symm
    have hnorm : ‖χ (symplecticIndex z y)‖=1 := by simp only [ZMod.stdAddChar_apply,Circle.norm_coe]
    have habs : ‖χ (symplecticIndex z y)-1‖^2=0 := by
      rw [←Complex.normSq_eq_norm_sq,Complex.normSq_sub,Complex.normSq_one,map_one,mul_one,
        Complex.normSq_eq_norm_sq,hnorm,hre]
      norm_num
    apply ZMod.injective_stdAddChar
    rw [AddChar.map_zero_eq_one]
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp habs))
  · intro he
    have hz : (∑ y ∈ symplecticDualSites H,W c y.1 y.2*(1-(χ (symplecticIndex z y)).re))=0 := by
      refine sum_eq_zero fun y hy => ?_
      by_cases hw : 0 < W c y.1 y.2
      · rw [he y hy (mem_filter.mpr ⟨mem_univ _,hw⟩),AddChar.map_zero_eq_one,Complex.one_re,sub_self,mul_zero]
      · rw [le_antisymm (le_of_not_gt hw) (sq_nonneg _),zero_mul]
    rw [hz,mul_zero] at h
    exact (sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left hq.ne')).symm

#print axioms cyclic_ambiguity_coset_poisson
#print axioms cyclic_ambiguity_coset_loss
#print axioms maximal_ambiguity_coset_iff
end GaloisForLFunctions.ArithmeticHarmonicAnalysis
