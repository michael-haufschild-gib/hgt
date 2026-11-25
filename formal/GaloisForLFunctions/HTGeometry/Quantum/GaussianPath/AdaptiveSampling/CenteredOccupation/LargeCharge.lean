import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.CenteredOccupation.PerturbedBoxes
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.AdaptiveSampling.CenteredOccupation.SparseDirection

/-! # A dimension-independent loss at every sufficiently large resonance -/

open Filter Set MeasureTheory Topology Finset
namespace GaloisForLFunctions.HTGeometry.AdaptiveSampling.CenteredOccupation
noncomputable section
variable {I : Type} [Fintype I] [DecidableEq I]

/-- Once the total charge reaches 2/y, every cube of side y on every
translate retains at least 2^(−ceil(2/y)) times its ambient Haar mass. -/
theorem large_charge_cube (ω : I → ℝ) (a τ : ℝ) (m : I → ℤ)
    (hgen : ∀ (w : I → ℤ) (k : ℤ), τ*finiteTorusCharacterDetuning w ω=(k:ℝ)*(2*Real.pi) →
      ∃ l : ℤ, w=fun i => l*m i)
    {y : ℝ} (hy : 0<y) (hy' : y≤1) (L : ℕ) (hL : 2/y≤(L:ℝ)) (hm : L≤chargeOn m univ)
    (c : UnitAddTorus I) :
    (ENNReal.ofReal y)^Fintype.card I*(ENNReal.ofReal (1/2:ℝ))^L ≤ atTop.liminf (fun N =>
      (integerClockPrefixLaw (fun n => finiteClockPhasePoint ω (a+(n:ℝ)*τ)) N : Measure _)
        (arcBox c (fun _ => y))) := by
  obtain ⟨s,hs,hB⟩ := sparse_charge m L hm
  let B := (chargeOn m s:ℝ)
  have hsize : 2/y≤B := hL.trans (by exact_mod_cast hB)
  have hpos : 0<B := (div_pos two_pos hy).trans_le hsize
  have hinv : 1/B≤y/2 := (div_le_iff₀ hpos).mpr (by
    have h := (div_le_iff₀ hy).mp hsize
    nlinarith only [h])
  let v := signedDirection m s
  have hc := transverse_haar ω a τ m v hpos.ne' (signed_detuning m s) hgen
  let w i := y*(if i∈s then 1/2 else 1)
  have hfit (i : I) : w i+|v i|/B≤y := by
    by_cases hi : i∈s
    · have hv : |v i|=1 := by
        dsimp only [v,signedDirection]
        rw [if_pos hi]
        split <;> norm_num
      rw [hv]
      dsimp only [w]
      rw [if_pos hi]
      linarith only [hinv]
    · simp [w,v,signedDirection,hi]
  have hw (i : I) : w i≤1 := ((le_add_of_nonneg_right (div_nonneg (abs_nonneg _) hpos.le)).trans (hfit i)).trans hy'
  have hh := box_liminf ω a τ v hpos hc c (fun _ => y) w hw hfit
  have he : ∏ i, ENNReal.ofReal (w i)=(ENNReal.ofReal y)^Fintype.card I*(ENNReal.ofReal (1/2:ℝ))^s.card := by
    simp only [w,ENNReal.ofReal_mul hy.le,apply_ite ENNReal.ofReal,ENNReal.ofReal_one,prod_mul_distrib,
      prod_const,card_univ,prod_ite_mem,univ_inter,prod_const_one,mul_one]
  rw [he] at hh
  exact (mul_le_mul_left' (pow_le_pow_of_le_one' (by norm_num) hs) _).trans hh

#print axioms large_charge_cube
end
end GaloisForLFunctions.HTGeometry.AdaptiveSampling.CenteredOccupation
