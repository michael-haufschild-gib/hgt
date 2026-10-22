import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspNativeMomentVariation
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspOddSeamSixteen
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspCoupledOddGapDerivative
/-! # Actual signed moments through order fourteen and their exact second seam variations. -/

namespace RHTower.ThetaOddSeamCurvature
noncomputable section
open HTGeometry ThetaOddMomentVariation
local notation "Phi" => thetaCuspFullSource
local notation "mass" => thetaCuspSelfDualThetaMass
local notation "scale" => thetaCuspSelfDualModularScale^2

def P (n : ℕ) (a : ℝ) : ℝ :=
  if h : n<7 then modularThetaEvenSeamSourcePolynomial ⟨n,h⟩ a
  else if n=7 then ThetaSeamFourteen.sourceFourteen a
  else if n=8 then ThetaSeamSixteen.sourceSixteen a else 0

def M (r : ℕ) (a : ℝ) : ℝ :=
  (-1:ℝ)^r*∑ j ∈ Finset.range (r+1), ((2*r).choose (2*j):ℝ)*P j a*P (r-j) a

def V (r : ℕ) (a : ℝ) : ℝ :=
  2*(-1:ℝ)^r*∑ j ∈ Finset.range (r+1),
    (((2*r).choose (2*j):ℝ)-((2*r).choose (2*j+1):ℝ))*P (j+1) a*P (r-j) a

theorem source_even (k : Fin 9) : iteratedDeriv (2*k.val) Phi 0=mass*P k.val scale := by
  fin_cases k
  · simpa [P] using thetaCuspFullSource_even_seamJet_eq_polynomial (0:Fin 7)
  · simpa [P] using thetaCuspFullSource_even_seamJet_eq_polynomial (1:Fin 7)
  · simpa [P] using thetaCuspFullSource_even_seamJet_eq_polynomial (2:Fin 7)
  · simpa [P] using thetaCuspFullSource_even_seamJet_eq_polynomial (3:Fin 7)
  · simpa [P] using thetaCuspFullSource_even_seamJet_eq_polynomial (4:Fin 7)
  · simpa [P] using thetaCuspFullSource_even_seamJet_eq_polynomial (5:Fin 7)
  · simpa [P] using thetaCuspFullSource_even_seamJet_eq_polynomial (6:Fin 7)
  · simpa [P] using ThetaSeamFourteen.source_fourteen
  · simpa [P] using ThetaSeamSixteen.source_sixteen

theorem native_first_zero (k : Fin 7) : jetFirst (2*(k.val+1)) 0=0 := by
  have h1 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=1) (by norm_num : Odd 1)
  have h3 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=3) (by norm_num : Odd 3)
  have h5 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=5) (by norm_num : Odd 5)
  have h7 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=7) (by norm_num : Odd 7)
  have h9 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=9) (by norm_num : Odd 9)
  have h11 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=11) (by norm_num : Odd 11)
  have h13 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=13) (by norm_num : Odd 13)
  have h15 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=15) (by norm_num : Odd 15)
  change (∑ i ∈ Finset.range (2*(k.val+1)+1), ((2*(k.val+1)).choose i:ℝ)*
    (-1:ℝ)^(2*(k.val+1)-i)*(iteratedDeriv (i+1) Phi 0*iteratedDeriv (2*(k.val+1)-i) Phi 0+
    iteratedDeriv i Phi 0*iteratedDeriv (2*(k.val+1)-i+1) Phi 0))=0
  fin_cases k <;> norm_num [Finset.sum_range_succ,Nat.choose,h1,h3,h5,h7,h9,h11,h13,h15]

theorem native_second_zero (k : Fin 7) :
    (-1:ℝ)^(k.val+1)*jetSecond (2*(k.val+1)) 0=mass^2*V (k.val+1) scale := by
  have h1 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=1) (by norm_num : Odd 1)
  have h3 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=3) (by norm_num : Odd 3)
  have h5 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=5) (by norm_num : Odd 5)
  have h7 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=7) (by norm_num : Odd 7)
  have h9 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=9) (by norm_num : Odd 9)
  have h11 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=11) (by norm_num : Odd 11)
  have h13 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=13) (by norm_num : Odd 13)
  have h15 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=15) (by norm_num : Odd 15)
  have h0 := source_even (0:Fin 9)
  have h2 := source_even (1:Fin 9)
  have h4 := source_even (2:Fin 9)
  have h6 := source_even (3:Fin 9)
  have h8 := source_even (4:Fin 9)
  have h10 := source_even (5:Fin 9)
  have h12 := source_even (6:Fin 9)
  have h14 := source_even (7:Fin 9)
  have h16 := source_even (8:Fin 9)
  norm_num at h0 h2 h4 h6 h8 h10 h12 h14 h16
  change (-1:ℝ)^(k.val+1)*(∑ i ∈ Finset.range (2*(k.val+1)+1),
    ((2*(k.val+1)).choose i:ℝ)*(-1:ℝ)^(2*(k.val+1)-i)*
    (iteratedDeriv (i+2) Phi 0*iteratedDeriv (2*(k.val+1)-i) Phi 0+
      2*iteratedDeriv (i+1) Phi 0*iteratedDeriv (2*(k.val+1)-i+1) Phi 0+
      iteratedDeriv i Phi 0*iteratedDeriv (2*(k.val+1)-i+2) Phi 0))=mass^2*V (k.val+1) scale
  fin_cases k <;>
    norm_num [V,Finset.sum_range_succ,Nat.choose,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16] <;> ring

theorem native_value (k : Fin 7) :
    (-1:ℝ)^(k.val+1)*thetaCuspNativeReflectionJet (2*(k.val+1)) 0=mass^2*M (k.val+1) scale := by
  have h1 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=1) (by norm_num : Odd 1)
  have h3 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=3) (by norm_num : Odd 3)
  have h5 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=5) (by norm_num : Odd 5)
  have h7 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=7) (by norm_num : Odd 7)
  have h9 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=9) (by norm_num : Odd 9)
  have h11 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=11) (by norm_num : Odd 11)
  have h13 := iteratedDeriv_thetaCuspFullSource_zero_of_odd (m:=13) (by norm_num : Odd 13)
  have h0 := source_even (0:Fin 9)
  have h2 := source_even (1:Fin 9)
  have h4 := source_even (2:Fin 9)
  have h6 := source_even (3:Fin 9)
  have h8 := source_even (4:Fin 9)
  have h10 := source_even (5:Fin 9)
  have h12 := source_even (6:Fin 9)
  have h14 := source_even (7:Fin 9)
  norm_num at h0 h2 h4 h6 h8 h10 h12 h14
  fin_cases k <;>
    norm_num [thetaCuspNativeReflectionJet_eq,M,Finset.sum_range_succ,Nat.choose,
      h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14] <;> ring

open ThetaCuspOddDirectionTransport

theorem moment_first_zero (k : Fin 7) : deriv (moment k) 0=0 := by
  have h := (native_first (2*(k.val+1)) 0).const_mul ((-1:ℝ)^(k.val+1))
  change HasDerivAt (moment k) _ 0 at h
  rw [h.deriv,native_first_zero,mul_zero]

theorem moment_second_zero (k : Fin 7) :
    deriv (deriv (moment k)) 0=mass^2*V (k.val+1) scale := by
  have he : deriv (moment k)=(fun x => (-1:ℝ)^(k.val+1)*jetFirst (2*(k.val+1)) x) := by
    funext x
    exact ((native_first (2*(k.val+1)) x).const_mul ((-1:ℝ)^(k.val+1))).deriv
  rw [he]
  rw [((native_second (2*(k.val+1)) 0).const_mul ((-1:ℝ)^(k.val+1))).deriv]
  exact native_second_zero k

end
end RHTower.ThetaOddSeamCurvature

