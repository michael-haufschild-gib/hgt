import GaloisForLFunctions.RHTower.SchattenLogResidueFiniteRankPerturbation
import GaloisForLFunctions.RHTower.SchattenTwoIdentity
import GaloisForLFunctions.HTGeometry.PrimeHodgeSteinGramian

/-! # Strict loss of Hilbert–Schmidt mass under a finite-rank change

Removing the component in the range of the difference costs strictly
positive mass when the second operator is injective and self-adjoint.
Finite-rank interlacing bounds the remaining mass loss.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open ContinuousLinearMap _root_.RHTower

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {A B : H →L[ℂ] H} {r : ℕ}

private theorem summable_approx_sq {T : H →L[ℂ] H} (hT : T.IsHilbertSchmidt) :
    Summable (fun n => approxNumber T n ^ 2) := by
  have h := (memSchattenClass_two_iff_isHilbertSchmidt T).mpr hT
  change Summable (fun n => approxNumber T n ^ (2:ℝ)) at h
  simpa only [Real.rpow_two] using h

/-- Finite-rank interlacing bounds the difference of squared Hilbert–Schmidt norms. -/
theorem hs_loss_le_head (hA : A.IsHilbertSchmidt) (hB : B.IsHilbertSchmidt)
    (hF : HasRankLE (A-B) r) :
    hsNormSq A-hsNormSq B ≤ ∑ k ∈ Finset.range r, approxNumber A k ^ 2 := by
  have hd : B+(A-B) = A := by abel
  have h (n : ℕ) : approxNumber A (n+r) ^ 2 ≤ approxNumber B n ^ 2 := by
    have hp := approxNumber_add_finiteRank_shift_le (A := B) hF n
    rw [hd] at hp
    exact pow_le_pow_left₀ (approxNumber_nonneg _ _) hp 2
  have ha := summable_approx_sq hA
  have hb := summable_approx_sq hB
  have ht := ((summable_nat_add_iff r).mpr ha).tsum_le_tsum h hb
  have he := ha.sum_add_tsum_nat_add r
  rw [hsNormSq_eq_tsum_approxNumber_sq hA,hsNormSq_eq_tsum_approxNumber_sq hB]
  linarith only [he,ht]

/-- A nonzero finite-rank change has strictly smaller loss when the second operator
is injective and self-adjoint. -/
theorem hs_loss_lt_head (hA : A.IsHilbertSchmidt) (hB : B.IsHilbertSchmidt)
    (hs : IsSelfAdjoint B) (hi : Function.Injective B) (hne : A ≠ B)
    (hF : HasRankLE (A-B) r) :
    hsNormSq A-hsNormSq B < ∑ k ∈ Finset.range r, approxNumber A k ^ 2 := by
  obtain ⟨W,hW,hd,hm⟩ := hF
  letI : FiniteDimensional ℂ W := hW
  let R := W.starProjection
  let K := 1-R
  have hr : IsStarProjection R := isStarProjection_starProjection
  have hfix (x : H) : R ((A-B) x) = (A-B) x := Submodule.starProjection_eq_self_iff.mpr (hm x)
  have hk : HasRankLE (A-K*B) r := by
    refine ⟨W,hW,hd,fun x => ?_⟩
    have e : (A-K*B) x = R (A x) := by
      have hf := hfix x
      simp only [sub_apply,map_sub] at hf
      change A x-(B x-R (B x)) = R (A x)
      calc
        _ = (A x-B x)+R (B x) := by abel
        _ = R (A x) := by rw [← hf,sub_add_cancel]
    rw [e]
    exact W.starProjection_apply_mem _
  have he : R*B ≠ 0 := by
    intro hz
    have hbr := congrArg star hz
    rw [star_mul,hs.star_eq,hr.isSelfAdjoint.star_eq,star_zero] at hbr
    have zr (x : H) : R x = 0 := hi ((congrArg (fun T : H →L[ℂ] H => T x) hbr).trans (map_zero B).symm)
    apply hne
    apply ContinuousLinearMap.ext
    intro x
    exact sub_eq_zero.mp ((hfix x).symm.trans (zr _))
  have hP : hsNormSq (R*B) = hsNormSq B-hsNormSq (K*B) := by
    apply HTGeometry.hsNormSq_defect_comp (C := K) _ hB
    change star R*R = 1-star (1-R)*(1-R)
    rw [star_sub,star_one,hr.isSelfAdjoint.star_eq,hr.isIdempotentElem.eq]
    calc
      R = 1-(1-R-R+R*R) := by rw [hr.isIdempotentElem.eq]; abel
      _ = _ := by noncomm_ring
  have hp := lt_of_le_of_ne (hsNormSq_nonneg (R*B))
    (fun eqn => he ((hsNormSq_eq_zero_iff (hB.comp_left R)).mp eqn.symm))
  have bound : hsNormSq A-hsNormSq (K*B) ≤ ∑ k ∈ Finset.range r, approxNumber A k ^ 2 :=
    hs_loss_le_head hA (hB.comp_left K) hk
  linarith only [hP,hp,bound]

#print axioms hs_loss_le_head
#print axioms hs_loss_lt_head

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
