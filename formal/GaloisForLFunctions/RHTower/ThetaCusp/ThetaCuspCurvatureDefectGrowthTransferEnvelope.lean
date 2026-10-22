import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCurvatureDefectGrowthTransferKernel
/-!
# Exact highest-monomial envelope for the growth-transfer kernel

On the stable spectral domain q >= 3/2, t >= 8, the full kernel lies
below its own leading degree-eight monomial. The leading coefficient is
strictly positive. This transports the complete operator's remaining
odd-sector losses to eighth moments without changing its q dependence.
The dominant-pair absorption inequality remains a separate target.
-/

namespace RHTower.ThetaCuspDefect
noncomputable section

theorem growthTransferKernel_monomial_shift (y v : ℝ) (hy : 0 ≤ y) (hv : 0 ≤ v) :
    growthTransferKernel (3/2+y) (8+v) ≤
      (3/2+y)*growthCoefficient (3/2+y) 7*growthNumerator (3/2+y) 3*(8+v)^8 := by
  unfold growthTransferKernel growthScore growthScoreJet growthNumerator slopeNumerator
  simp only [Finset.sum_range_succ,Finset.sum_range_zero,zero_add]
  norm_num [growthCoefficient,growthCoefficientJet,coolingCoefficient,coolingCoefficientJet,
    coolingCoefficientJetTwo]
  unfold polynomialMoment
  norm_num [Finset.sum_range_succ,Nat.choose,Nat.factorial]
  apply sub_nonneg.mp
  ring_nf (config := {mode := .raw})
  simp only [Mathlib.Tactic.RingNF.nnrat_rawCast,Mathlib.Tactic.RingNF.nat_rawCast_1,
    Mathlib.Tactic.RingNF.nat_rawCast_2,pow_one]
  positivity

theorem growthTransferKernel_le_monomial {q t : ℝ} (hq : 3/2 ≤ q) (ht : 8 ≤ t) :
    growthTransferKernel q t ≤ q*growthCoefficient q 7*growthNumerator q 3*t^8 := by
  have h := growthTransferKernel_monomial_shift (q-3/2) (t-8) (by linarith) (by linarith)
  simpa only [show (3/2:ℝ)+(q-3/2)=q by ring,show (8:ℝ)+(t-8)=t by ring] using h

def growthTransferLeadingCoefficient (q : ℝ) : ℝ :=
  q*growthCoefficient q 7*growthNumerator q 3

theorem growthTransferLeadingCoefficient_pos {q : ℝ} (hq : 3/2 ≤ q) :
    0 < growthTransferLeadingCoefficient q := by
  have hp := growthTransferKernel_pos hq (le_refl (8:ℝ))
  have hu := growthTransferKernel_le_monomial hq (le_refl (8:ℝ))
  change growthTransferKernel q 8 ≤ growthTransferLeadingCoefficient q*8^8 at hu
  norm_num at hu
  nlinarith

end
end RHTower.ThetaCuspDefect
