import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMScalarStreamMasterIdentity

set_option autoImplicit false
namespace RHTower.D4BMScalarStreamReconstruction
open D4BMScalarStream
noncomputable section

/-- Angular metric amplitude reconstructed from the literal master variable and three source rows. -/
def recoverH (s r μ M M1 eTF eTF1 eTR eT : ℂ) : ℂ :=
  ((r^(2 : ℕ)-1)/s*eT + (μ/2-(r^(2 : ℕ)-1))*eTF - (r^(2 : ℕ)-1)*r*eTF1 +
    (r^(2 : ℕ)-1)/2*M1 + (r^(2 : ℕ)-1)*r/(2*s)*eTR - μ/(4*r)*M)/(2-μ)

/-- Formal radial derivative of the original `(t,r)` row. -/
def harmonicTR1 (s r μ F1 F11 F2 F21 H H1 H2 : ℂ) : ℂ :=
  μ/r^(3 : ℕ)*F1 - μ/(2*r^(2 : ℕ))*F11 + 2*s*(1+1/r^(2 : ℕ))*F2 +
    2*s*(r^(2 : ℕ)-1)/r*F21 - 4*s*(3*r^(2 : ℕ)-1)/(r^(2 : ℕ)*(r^(2 : ℕ)-1)^(2 : ℕ))*H +
    4*s/(r*(r^(2 : ℕ)-1))*H1 - 4*s*H2

/-- Formal radial derivative of the original mixed radial row. -/
def harmonicR1 (s r F0 F01 F02 F1 F11 F2 F21 H2 : ℂ) : ℂ :=
  (-2/(r^(2 : ℕ)-1)^(2 : ℕ) - (1/2-r^(2 : ℕ))/(r^(2 : ℕ)*(r^(2 : ℕ)-1)^(2 : ℕ)) -
    4*(1/2-r^(2 : ℕ))/(r^(2 : ℕ)-1)^(3 : ℕ))*F0 +
  ((1/2-r^(2 : ℕ))/(r*(r^(2 : ℕ)-1)^(2 : ℕ)) - r/(r^(2 : ℕ)-1)^(2 : ℕ))*F01 +
  1/(2*(r^(2 : ℕ)-1))*F02 + 2*s*r/(r^(2 : ℕ)-1)^(2 : ℕ)*F1 - s/(r^(2 : ℕ)-1)*F11 +
  (1+1/(2*r^(2 : ℕ)))*F2 + (r-1/(2*r))*F21 - H2

/-- Formal radial derivative of the original `(r,r)` row. -/
def harmonicRR1 (s r μ F0 F01 F02 F1 F11 F2 F21 H H1 H2 : ℂ) : ℂ :=
  (μ/(r^(3 : ℕ)*(r^(2 : ℕ)-1)^(2 : ℕ)) - 4*r*(2-μ/(2*r^(2 : ℕ)))/(r^(2 : ℕ)-1)^(3 : ℕ))*F0 +
  ((2-μ/(2*r^(2 : ℕ)))/(r^(2 : ℕ)-1)^(2 : ℕ) + (3*r^(2 : ℕ)-1)/(r^(2 : ℕ)*(r^(2 : ℕ)-1)^(2 : ℕ)))*F01 -
  1/(r*(r^(2 : ℕ)-1))*F02 - 4*s*(3*r^(2 : ℕ)-1)/(r^(2 : ℕ)*(r^(2 : ℕ)-1)^(2 : ℕ))*F1 +
  4*s/(r*(r^(2 : ℕ)-1))*F11 - 2/r^(3 : ℕ)*F2 + (1/r^(2 : ℕ)-3)*F21 +
  (-2*(μ-2)/(r^(3 : ℕ)*(r^(2 : ℕ)-1)) - 2*(μ-2)/(r*(r^(2 : ℕ)-1)^(2 : ℕ)) +
    32*s^(2 : ℕ)*r/(r^(2 : ℕ)-1)^(3 : ℕ))*H +
  ((μ-2)/(r^(2 : ℕ)*(r^(2 : ℕ)-1)) - 8*s^(2 : ℕ)/(r^(2 : ℕ)-1)^(2 : ℕ) + 8/(r^(2 : ℕ)-1) -
    (4*r^(2 : ℕ)-2)*(3*r^(2 : ℕ)-1)/(r^(2 : ℕ)*(r^(2 : ℕ)-1)^(2 : ℕ)))*H1 +
  (4*r^(2 : ℕ)-2)/(r*(r^(2 : ℕ)-1))*H2

/-- Radial first jet reconstructed with all source derivative terms retained. -/
def recoverH1 (s r μ M M1 M2 eTF eTF1 eTF2 eTR eTR1 eT eT1 : ℂ) : ℂ :=
  (2*r/s*eT + (r^(2 : ℕ)-1)/s*eT1 - 2*r*eTF +
    (μ/2+2-4*r^(2 : ℕ))*eTF1 - (r^(2 : ℕ)-1)*r*eTF2 +
    (r-μ/(4*r))*M1 + (r^(2 : ℕ)-1)/2*M2 +
    (3*r^(2 : ℕ)-1)/(2*s)*eTR + (r^(2 : ℕ)-1)*r/(2*s)*eTR1 +
    μ/(4*r^(2 : ℕ))*M)/(2-μ)

/-- Mixed metric amplitude, before any source specialization. -/
def recoverF1 (s r M eTF H : ℂ) : ℂ := s/(r^(2 : ℕ)-1)*(4*r*H+2*r*eTF-M)

/-- Radial metric amplitude, before any source specialization. -/
def recoverF2 (s r μ eTR F1 H H1 : ℂ) : ℂ :=
  r/(2*s*(r^(2 : ℕ)-1))*eTR + μ/(4*s*r*(r^(2 : ℕ)-1))*F1 -
    2/(r^(2 : ℕ)-1)^(2 : ℕ)*H + 2*r/(r^(2 : ℕ)-1)*H1

/-- Temporal metric amplitude, before any source specialization. -/
def recoverF0 (r eTF F2 : ℂ) : ℂ := (r^(2 : ℕ)-1)^(2 : ℕ)*F2 + 2*(r^(2 : ℕ)-1)*eTF

variable (s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2 : ℂ)
local notation "M" => masterVar s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2
local notation "M1" => masterVar1 s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2
local notation "M2" => masterVar2 s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2
local notation "ETT" => harmonicTT s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2
local notation "ETR" => harmonicTR s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2
local notation "ERR" => harmonicRR s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2
local notation "ET" => harmonicT s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2
local notation "ER" => harmonicR s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2
local notation "ETF" => harmonicTF s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2
local notation "EL" => harmonicL s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2
local notation "ET1" => harmonicT1 s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2
local notation "ETF1" => harmonicTF1 s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2
local notation "ETF2" => harmonicTF2 s r μ F0 F01 F02 F1 F11 F12 F2 F21 F22 H H1 H2
local notation "ETR1" => harmonicTR1 s r μ F1 F11 F2 F21 H H1 H2
local notation "ER1" => harmonicR1 s r F0 F01 F02 F1 F11 F2 F21 H2
local notation "ERR1" => harmonicRR1 s r μ F0 F01 F02 F1 F11 F2 F21 H H1 H2

/-- Exact inverse identity for the original harmonic stream jet. -/
theorem recoverH_eq (hs : s ≠ 0) (hr : r ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) (hμ : 2-μ ≠ 0) :
    recoverH s r μ M M1 ETF ETF1 ETR ET = H := by
  unfold recoverH masterVar masterVar1 harmonicTF harmonicTF1 harmonicTR harmonicT
  field_simp
  ring

theorem recoverH1_eq (hs : s ≠ 0) (hr : r ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) (hμ : 2-μ ≠ 0) :
    recoverH1 s r μ M M1 M2 ETF ETF1 ETF2 ETR ETR1 ET ET1 = H1 := by
  unfold recoverH1 masterVar masterVar1 masterVar2 harmonicTF harmonicTF1 harmonicTF2
    harmonicTR harmonicTR1 harmonicT harmonicT1
  field_simp
  ring

theorem recoverF1_eq (hs : s ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    recoverF1 s r M ETF H = F1 := by
  unfold recoverF1 masterVar harmonicTF
  field_simp
  ring

theorem recoverF2_eq (hs : s ≠ 0) (hr : r ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    recoverF2 s r μ ETR F1 H H1 = F2 := by
  unfold recoverF2 harmonicTR
  field_simp
  ring

theorem recoverF0_eq (hf : r^(2 : ℕ)-1 ≠ 0) : recoverF0 r ETF F2 = F0 := by
  unfold recoverF0 harmonicTF
  field_simp
  ring

/-- Exact temporal Bianchi relation of the literal seven-row operator. -/
theorem bianchi_time (hr : r ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    (r^(2 : ℕ)-1)*ETR1 + (4*r-2/r)*ETR - 2*s/(r^(2 : ℕ)-1)*ETT + μ/r^(2 : ℕ)*ET = 0 := by
  unfold harmonicTR1 harmonicTR harmonicTT harmonicT
  field_simp
  ring

/-- Exact angular Bianchi relation of the literal seven-row operator. -/
theorem bianchi_angular (hr : r ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    (r^(2 : ℕ)-1)*ER1 + (4*r-2/r)*ER - 2*s/(r^(2 : ℕ)-1)*ET +
      ((μ/2-1)*ETF+EL)/r^(2 : ℕ) = 0 := by
  unfold harmonicR1 harmonicR harmonicT harmonicTF harmonicL
  field_simp
  ring

/-- Exact radial Bianchi relation of the literal seven-row operator. -/
theorem bianchi_radial (hr : r ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    (r^(2 : ℕ)-1)*ERR1 + (5*r-2/r)*ERR - 2*s/(r^(2 : ℕ)-1)*ETR + r/(r^(2 : ℕ)-1)^(2 : ℕ)*ETT +
      μ/r^(2 : ℕ)*ER - 2*EL/r^(3 : ℕ) = 0 := by
  unfold harmonicRR1 harmonicRR harmonicTR harmonicTT harmonicR harmonicL
  field_simp
  ring

/-- Temporal divergence defect of seven supplied harmonic source rows. -/
def timeDefect (s r μ A B B1 D : ℂ) : ℂ :=
  (r^(2 : ℕ)-1)*B1 + (4*r-2/r)*B - 2*s/(r^(2 : ℕ)-1)*A + μ/r^(2 : ℕ)*D

/-- Angular divergence uses the original trace-free Hessian convention. -/
def angularDefect (s r μ D E E1 F G : ℂ) : ℂ :=
  (r^(2 : ℕ)-1)*E1 + (4*r-2/r)*E - 2*s/(r^(2 : ℕ)-1)*D + ((μ/2-1)*F+G)/r^(2 : ℕ)

/-- Radial divergence retains the original angular trace. -/
def radialDefect (s r μ A B C C1 E G : ℂ) : ℂ :=
  (r^(2 : ℕ)-1)*C1 + (5*r-2/r)*C - 2*s/(r^(2 : ℕ)-1)*B + r/(r^(2 : ℕ)-1)^(2 : ℕ)*A +
    μ/r^(2 : ℕ)*E - 2*G/r^(3 : ℕ)

/-- Exact residual decomposition, before imposing compatibility or deleting any row.
The same factor `μ-2` controls both reconstruction and component completeness. -/
theorem radial_residual_decomposition (s r μ A B C C1 D E E1 F G : ℂ)
    (hr : r ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) :
    (μ-2)/r^(2 : ℕ)*(E+F/r) =
      radialDefect s r μ A B C C1 E G + 2/r*angularDefect s r μ D E E1 F G -
      (r^(2 : ℕ)-1)/(2*r)*(2*C+2*r*C1+4*E1) -
      (2-1/(2*r^(2 : ℕ)))*(2*r*C+4*E) - r/(r^(2 : ℕ)-1)^(2 : ℕ)*A +
      2*s/(r^(2 : ℕ)-1)*B + 4*s/(r*(r^(2 : ℕ)-1))*D := by
  unfold radialDefect angularDefect
  field_simp
  ring

/-- Compatibility and the reduced master equation, including its first derivative,
determine every unmatched component away from the displayed exceptional factor.
All quantities here are residuals: an application to a forced solution must supply the
original source's compatibility and genuine derivatives. The remaining trace is a
derivative of the now vanishing radial residual, not a disposable pointwise term. -/
theorem residual_completeness (s r μ A B B1 C C1 D E E1 F G : ℂ)
    (hs : s ≠ 0) (hr : r ≠ 0) (hf : r^(2 : ℕ)-1 ≠ 0) (hμ : μ-2 ≠ 0)
    (ht : timeDefect s r μ A B B1 D = 0)
    (ha : angularDefect s r μ D E E1 F G = 0)
    (hb : radialDefect s r μ A B C C1 E G = 0)
    (hB : B = 0) (hB1 : B1 = 0) (hD : D = 0) (hF : F = 0)
    (hQ : 2*r*C+4*E = 0) (hQ1 : 2*C+2*r*C1+4*E1 = 0) :
    A = 0 ∧ C = 0 ∧ E = 0 ∧ G = -r^(2 : ℕ)*(r^(2 : ℕ)-1)*E1 := by
  have hA : A = 0 := by
    have ht' : (2*s/(r^(2 : ℕ)-1))*A = 0 := by
      unfold timeDefect at ht
      rw [hB, hB1, hD] at ht
      linear_combination -ht
    exact (mul_eq_zero.mp ht').resolve_left
      (div_ne_zero (mul_ne_zero (by norm_num) hs) hf)
  have hE : E = 0 := by
    have hd := radial_residual_decomposition s r μ A B C C1 D E E1 F G hr hf
    rw [hb, ha, hQ, hQ1, hA, hB, hD, hF] at hd
    have hz : ((μ-2)/r^(2 : ℕ))*E = 0 := by linear_combination hd
    exact (mul_eq_zero.mp hz).resolve_left (div_ne_zero hμ (pow_ne_zero 2 hr))
  have hC : C = 0 := by
    have hz : (2*r)*C = 0 := by rw [hE] at hQ; linear_combination hQ
    exact (mul_eq_zero.mp hz).resolve_left (mul_ne_zero (by norm_num) hr)
  have hG : G = -r^(2 : ℕ)*(r^(2 : ℕ)-1)*E1 := by
    unfold angularDefect at ha
    rw [hE,hD,hF] at ha
    have hz : (r^(2 : ℕ)-1)*E1+G/r^(2 : ℕ) = 0 := by linear_combination ha
    field_simp at hz
    linear_combination hz
  exact ⟨hA,hC,hE,hG⟩

end
end RHTower.D4BMScalarStreamReconstruction
