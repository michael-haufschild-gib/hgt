import GaloisForLFunctions.RHTower.DivisorSourceNegativeHalfReflection
import GaloisForLFunctions.RHTower.ZetaThreeHalvesLogMoment
import GaloisForLFunctions.RHTower.MobiusDivisorDilationMean
import GaloisForLFunctions.RHTower.RiemannGaussian.RiemannXiSuzukiPointwiseFirstTailBarrier

/-!
# Strict orientation of the actual divisor-source residue

Reflection and the complete positive logarithmic series give
B(-1/2)>1/(272*pi). The exact finite-prime multiplier and the positive
signed moment therefore fix the residue's nonzero sign. The physical
dilation limit transfers that sign to every sufficiently large dilation
for a fixed nonempty core. No uniform threshold over changing cores is used.
-/

noncomputable section
open Complex Filter Set Topology MeasureTheory Finset
namespace RHTower

private lemma source_reflection_coefficient_gt :
    (-1:ℝ)<Real.log (8*Real.pi)-Real.eulerMascheroniConstant-2-Real.pi/2 := by
  have hlog : Real.log (24:ℝ)<Real.log (8*Real.pi) :=
    Real.log_lt_log (by norm_num) (by nlinarith [Real.pi_gt_three])
  have he : Real.log (24:ℝ)=3*Real.log 2+Real.log 3 := by
    rw [show (24:ℝ)=2^3*3 by norm_num, Real.log_mul (by positivity) (by norm_num),
      Real.log_pow]
    norm_num
  rw [he] at hlog
  linarith [Real.log_two_gt_d9,Real.log_three_gt_d9,Real.pi_lt_d2,
    RiemannGaussian.eulerMascheroniConstant_lt_29_over_50]

/-- The actual divisor source has a strict positive residue margin at -1/2,
proved by reflection and a lower bound for the complete logarithmic series. -/
theorem divisorSourceEntire_negative_half_lower :
    1/(272*Real.pi)<(divisorSourceEntire (-(1/2))).re := by
  have hzpos := eulerMass_pos (σ := 3/2) (by norm_num)
  have hzbound := Sieve.norm_riemannZeta_le (s := 3/2) (by norm_num)
  have hzval := riemannZeta_ofReal_eq_eulerMass (σ := 3/2) (by norm_num)
  norm_num at hzval
  rw [hzval,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hzpos] at hzbound
  norm_num at hzbound
  have hc := source_reflection_coefficient_gt
  have hlin : -eulerMass (3/2)<
      (Real.log (8*Real.pi)-Real.eulerMascheroniConstant-2-Real.pi/2)*eulerMass (3/2) := by
    nlinarith
  have hquad : (eulerMass (3/2))^2/(4*Real.pi)<3/4 := by
    apply (div_lt_iff₀ (by positivity : (0:ℝ)<4*Real.pi)).mpr
    nlinarith [Real.pi_gt_three]
  have hmargin : (1/68:ℝ)<eulerLogMass (3/2)+
      (Real.log (8*Real.pi)-Real.eulerMascheroniConstant-2-Real.pi/2)*eulerMass (3/2)-
      (eulerMass (3/2))^2/(4*Real.pi) := by
    linarith [eulerLogMass_three_halves_gt]
  rw [divisorSourceEntire_negative_half_eq,Complex.ofReal_re]
  calc
    1/(272*Real.pi)=(1/68)/(4*Real.pi) := by ring
    _ < _ := div_lt_div_of_pos_right hmargin (by positivity)

/-- The source value that orients the physical fixed-core residue is positive. -/
theorem divisorSourceEntire_negative_half_pos : 0<(divisorSourceEntire (-(1/2))).re :=
  lt_trans (by positivity) divisorSourceEntire_negative_half_lower

/-- The reflected literal source value is exactly real. -/
theorem divisorSourceEntire_negative_half_im : (divisorSourceEntire (-(1/2))).im=0 := by
  rw [divisorSourceEntire_negative_half_eq,Complex.ofReal_im]

/-- The nonzero physical residue has the sign of minus the core's Mobius parity. -/
theorem divisorCoreMellinPairResidue_oriented_pos (P : Finset ℕ) (hP : P.Nonempty)
    (hprime : ∀p∈P,p.Prime) :
    0<(-1:ℝ)^(P.card+1)*(divisorCoreMellinPairResidue P).re := by
  have hp : 0<∏p∈P,(Real.sqrt p-1) := by
    apply Finset.prod_pos
    intro p hp
    have hpr : (1:ℝ)<p := by exact_mod_cast (hprime p hp).one_lt
    have hs : (1:ℝ)<Real.sqrt p := by
      have hsq := Real.sq_sqrt (show (0:ℝ)≤p by positivity)
      have hn := Real.sqrt_nonneg (p:ℝ)
      nlinarith
    linarith
  have he : (∏p∈P,(1-Real.sqrt p):ℝ)=(-1:ℝ)^P.card*∏p∈P,(Real.sqrt p-1) := by
    calc
      _ = ∏p∈P,(-1:ℝ)*(Real.sqrt p-1) := by
        apply Finset.prod_congr rfl
        intro p _
        ring
      _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const]
  have hs : ((-1:ℝ)^P.card)^2=1 := by
    rw [← pow_mul,mul_comm P.card 2,pow_mul]
    norm_num
  rw [divisorCoreMellinPairResidue_eq_signed_moment P hP hprime,
    divisorCoreMellinEuler_zero P hprime]
  simp only [Complex.mul_re,Complex.neg_re,Complex.ofReal_re,Complex.ofReal_im,
    mul_zero,sub_zero,neg_div]
  rw [he,pow_succ]
  have hh := mul_pos (mul_pos divisorSourceEntire_negative_half_pos hp)
    (integral_mobiusDivisorContinuousHead_moment_pos P hprime)
  convert! hh using 1
  calc
    _ = ((-1:ℝ)^P.card)^2*((divisorSourceEntire (-(1/2))).re*
        (∏p∈P,(Real.sqrt p-1))*
        (∫x in Ioi (0:ℝ),mobiusDivisorContinuousHead P x/x^3)) := by ring
    _ = _ := by rw [hs,one_mul]

/-- For every fixed nonempty prime core the actual signed head average has
the strict parity-determined sign at all sufficiently large positive dilations. -/
theorem eventually_mobiusDivisorDilationMean_oriented_pos (P : Finset ℕ) (hP : P.Nonempty)
    (hprime : ∀p∈P,p.Prime) :
    ∀ᶠY : ℝ in atTop, 0<(-1:ℝ)^(P.card+1)*mobiusDivisorDilationMean P Y := by
  have h := (tendsto_mobiusDivisorDilationMean P hP hprime).const_mul ((-1:ℝ)^(P.card+1))
  exact h.eventually (Ioi_mem_nhds (divisorCoreMellinPairResidue_oriented_pos P hP hprime))

end RHTower
