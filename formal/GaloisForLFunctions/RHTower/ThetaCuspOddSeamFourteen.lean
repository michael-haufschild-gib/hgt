import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactSourceTwelve
import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactModel
import GaloisForLFunctions.RHTower.ThetaCuspEvenSeamJets
import Mathlib.Tactic.Ring
/-!
# Exact fourteenth source and reflection jets at the modular seam

The second covariant Lie derivative sees only the transverse two-jet of
an observable at the seam. Applying this identity to the existing exact
order-twelve source polynomial supplies the missing fourteenth source
jet and the seventh signed reflection moment, retaining the full source.
-/

namespace HTGeometry.ThetaSeamFourteen
noncomputable section
open MvPolynomial
open ModularThetaLyapunovState

def seamState (a : ℂ) : ModularThetaLyapunovState → ℂ
  | .S => 0
  | .A => a
  | .W => 0

private theorem states_univ : (Finset.univ : Finset ModularThetaLyapunovState) =
    {.S,.A,.W} := by
  ext i
  cases i <;> simp

/-- At the seam the second covariant derivative only sees the transverse two-jet. -/
theorem seam_double_lie (Q : ModularThetaLyapunovPolynomial) (a : ℂ) :
    let v := seamState a
    let s := 3-3*a/4
    let w := 2+a/2
    eval v (modularThetaLyapunovNormalizedLie (modularThetaLyapunovNormalizedLie Q)) =
      s^2*eval v (pderiv .S (pderiv .S Q))+
      s*w*(eval v (pderiv .S (pderiv .W Q))+eval v (pderiv .W (pderiv .S Q)))+
      w^2*eval v (pderiv .W (pderiv .W Q))-
      2*a*w*eval v (pderiv .A Q)-s/6*eval v Q := by
  dsimp only
  simp [modularThetaLyapunovNormalizedLie,modularThetaLyapunovLie,
    modularThetaLyapunovVectorField,states_univ,pderiv_X,Pi.single_apply,seamState]
  ring


private def seam12Zero {K : Type*} [Field K] (a : K) : K :=
  (-9603111885 / 512 : K)*a^0 +
  (72410457375 / 512 : K)*a^1 +
  (146977580081 / 8192 : K)*a^2 +
  (281792785791 / 16384 : K)*a^3 +
  (-183992803467 / 131072 : K)*a^4 +
  (-2279863179 / 32768 : K)*a^5 +
  (-4153486905 / 2097152 : K)*a^6 +
  (82018251 / 4194304 : K)*a^7

private def seam12SSHalf {K : Type*} [Field K] (a : K) : K :=
  (24136819125 / 256 : K)*a^0 +
  (-3674439502025 / 18432 : K)*a^1 +
  (1331609046581 / 24576 : K)*a^2 +
  (-1717482882775 / 49152 : K)*a^3 +
  (18183821139 / 16384 : K)*a^4 +
  (16860609835 / 524288 : K)*a^5 +
  (3473399655 / 2097152 : K)*a^6

private def seam12SW {K : Type*} [Field K] (a : K) : K :=
  (-146977580081 / 256 : K)*a^1 +
  (-71829533633 / 512 : K)*a^2 +
  (-157119885175 / 2048 : K)*a^3 +
  (2760219099 / 512 : K)*a^4 +
  (14632222215 / 65536 : K)*a^5 +
  (368880669 / 131072 : K)*a^6

private def seam12WWHalf {K : Type*} [Field K] (a : K) : K :=
  (-146977580081 / 256 : K)*a^1 +
  (-82880231115 / 512 : K)*a^2 +
  (-74767393635 / 2048 : K)*a^3 +
  (2970635877 / 512 : K)*a^4 +
  (13698002655 / 65536 : K)*a^5 +
  (246236679 / 131072 : K)*a^6

private def seam12A {K : Type*} [Field K] (a : K) : K :=
  (72410457375 / 512 : K)*(1 : K)*a^(Nat.pred 1) +
  (146977580081 / 8192 : K)*(2 : K)*a^(Nat.pred 2) +
  (281792785791 / 16384 : K)*(3 : K)*a^(Nat.pred 3) +
  (-183992803467 / 131072 : K)*(4 : K)*a^(Nat.pred 4) +
  (-2279863179 / 32768 : K)*(5 : K)*a^(Nat.pred 5) +
  (-4153486905 / 2097152 : K)*(6 : K)*a^(Nat.pred 6) +
  (82018251 / 4194304 : K)*(7 : K)*a^(Nat.pred 7)

private theorem jet12_zero (a : ℂ) : eval (seamState a) (evenCompactSourceJet12) = seam12Zero a := by
  simp [evenCompactSourceJet12,seamState,seam12Zero]
  ring

private theorem jet12_ss (a : ℂ) : eval (seamState a) (pderiv .S (pderiv .S evenCompactSourceJet12)) = 2*seam12SSHalf a := by
  simp [evenCompactSourceJet12,pderiv_X,seamState,seam12SSHalf]
  ring

private theorem jet12_sw (a : ℂ) : eval (seamState a) (pderiv .S (pderiv .W evenCompactSourceJet12)) = seam12SW a := by
  simp [evenCompactSourceJet12,pderiv_X,seamState,seam12SW]
  ring

private theorem jet12_ws (a : ℂ) : eval (seamState a) (pderiv .W (pderiv .S evenCompactSourceJet12)) = seam12SW a := by
  simp [evenCompactSourceJet12,pderiv_X,seamState,seam12SW]
  ring

private theorem jet12_ww (a : ℂ) : eval (seamState a) (pderiv .W (pderiv .W evenCompactSourceJet12)) = 2*seam12WWHalf a := by
  simp [evenCompactSourceJet12,pderiv_X,seamState,seam12WWHalf]
  ring

private theorem jet12_a (a : ℂ) : eval (seamState a) (pderiv .A evenCompactSourceJet12) = seam12A a := by
  simp [evenCompactSourceJet12,pderiv_X,seamState,seam12A]
  ring

/-- Exact factored fourteenth source jet at the modular seam. -/
def sourceFourteen {K : Type*} [Field K] (a : K) : K :=
  let s := 3-3*a/4
  let w := 2+a/2
  2*s^2*seam12SSHalf a+2*s*w*seam12SW a+2*w^2*seam12WWHalf a-
    2*a*w*seam12A a-s/6*seam12Zero a

theorem eval_source_fourteen (a : ℂ) :
    eval (seamState a) (modularThetaLyapunovNormalizedSourceJet 14) = sourceFourteen a := by
  rw [show 14=13+1 by rfl,modularThetaLyapunovNormalizedSourceJet_succ,
    show 13=12+1 by rfl,modularThetaLyapunovNormalizedSourceJet_succ,
    evenCompactSourceJet12_eq,seam_double_lie]
  rw [jet12_ss,jet12_sw,jet12_ws,jet12_ww,jet12_a,jet12_zero]
  unfold sourceFourteen
  ring


end
end HTGeometry.ThetaSeamFourteen

namespace HTGeometry.ThetaSeamFourteen
noncomputable section
open RHTower

/-- Literal complete-source derivative fourteen at the self-dual seam. -/
theorem source_fourteen : iteratedDeriv 14 thetaCuspFullSource 0 =
    thetaCuspSelfDualThetaMass*sourceFourteen (thetaCuspSelfDualModularScale^2) := by
  have h := thetaCuspFullSource_seamJet_eq_formalJet 14
  rw [modularThetaODESourceJet_eq_X_H_mul_normalized, map_mul, MvPolynomial.eval_X] at h
  simp only [modularThetaODESeamState,one_mul] at h
  rw [← modularThetaGeneralLyapunov_normalizedSourceJet,
    eval_modularThetaGeneralLyapunovPullback_seam] at h
  change ((iteratedDeriv 14 thetaCuspFullSource 0 : ℝ) : ℂ) =
    (thetaCuspSelfDualThetaMass : ℂ)*
      MvPolynomial.eval (seamState ((thetaCuspSelfDualModularScale : ℂ)^2))
        (modularThetaLyapunovNormalizedSourceJet 14) at h
  rw [eval_source_fourteen] at h
  apply Complex.ofReal_injective
  rw [h]
  norm_num [sourceFourteen,HTGeometry.ThetaSeamFourteen.seam12SSHalf,
    HTGeometry.ThetaSeamFourteen.seam12SW,HTGeometry.ThetaSeamFourteen.seam12WWHalf,
    HTGeometry.ThetaSeamFourteen.seam12A,HTGeometry.ThetaSeamFourteen.seam12Zero]

end
end HTGeometry.ThetaSeamFourteen


namespace RHTower.ThetaCuspCoupledSeam
noncomputable section
open HTGeometry HTGeometry.ThetaSeamFourteen

def momentSeven (a : ℝ) : ℝ :=
  let f := fun k : Fin 7 => modularThetaEvenSeamSourcePolynomial k a;
  -(2*f 0*sourceFourteen a+182*f 1*f 6+2002*f 2*f 5+6006*f 3*f 4)

/-- The missing signed moment is the literal fourteenth reflected derivative of the infinite source. -/
theorem native_fourteen : -thetaCuspNativeReflectionJet 14 0 =
    thetaCuspSelfDualThetaMass^2*momentSeven (thetaCuspSelfDualModularScale^2) := by
  have h0 := thetaCuspFullSource_even_seamJet_eq_polynomial (0 : Fin 7)
  have h2 := thetaCuspFullSource_even_seamJet_eq_polynomial (1 : Fin 7)
  have h4 := thetaCuspFullSource_even_seamJet_eq_polynomial (2 : Fin 7)
  have h6 := thetaCuspFullSource_even_seamJet_eq_polynomial (3 : Fin 7)
  have h8 := thetaCuspFullSource_even_seamJet_eq_polynomial (4 : Fin 7)
  have h10 := thetaCuspFullSource_even_seamJet_eq_polynomial (5 : Fin 7)
  have h12 := thetaCuspFullSource_even_seamJet_eq_polynomial (6 : Fin 7)
  have h14 := source_fourteen
  norm_num at h0 h2 h4 h6 h8 h10 h12
  have h1 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 1) (by norm_num : Odd 1)
  have h3 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 3) (by norm_num : Odd 3)
  have h5 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 5) (by norm_num : Odd 5)
  have h7 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 7) (by norm_num : Odd 7)
  have h9 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 9) (by norm_num : Odd 9)
  have h11 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 11) (by norm_num : Odd 11)
  have h13 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m := 13) (by norm_num : Odd 13)
  norm_num [thetaCuspNativeReflectionJet_eq,Finset.sum_range_succ,Nat.choose,
    h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,momentSeven]
  ring

end
end RHTower.ThetaCuspCoupledSeam
