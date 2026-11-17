import GaloisForLFunctions.OrderSixMetaplecticTheory.TheCompositeHeckeTraceIsAPhasedSumOverRatioPoints

/-!
# The composite Hecke trace as nine blocks of Hecke points

With `Θ^{hh}(w) = Θ(A_mw)`, `Θ^{ll}_t(w) = Θ(A_m⁻¹T_tw)`, `Θ^{hl}_t(w) = Θ(A_q⁻¹T_tA_pw)` and
`Θ^{lh}_t(w) = Θ(A_p⁻¹T_tA_qw)`, the coset of type `(i, j)` (`U`, `W` or `L` at `p` and at `q`) contributes
(`heckeTrace_eq_blocks`):

* `(U, U)`: `Θ^{hh}Θ^{ll}_x`;  `(W, W)`: `Θ^{ll}_{f+x}Θ^{hh}`;  `(L, L)`: `(3y/m)₃Θ^{ll}_{x−β_y}Θ^{ll}_x`;
* `(U, W)`: `κ(W'_q)^{−2}κ(M')Θ^{hl}_{p(f'+x)}Θ^{lh}_{1+qx}`;  `(W, U)`: `κ(W'_p)^{−2}κ(M'')Θ^{lh}_{q(f''+x)}Θ^{hl}_{1+px}`;
* `(U, L)`: `(3y/q)₃Θ^{hl}_{px−β_y}Θ^{ll}_x`;  `(L, U)`: `(3y/p)₃Θ^{lh}_{qx−β_y}Θ^{ll}_x`;
* `(W, L)`: `κ(W'_p)^{−2}κ(M_y)Θ^{ll}_{t+x}Θ^{hl}_{1+px}`;  `(L, W)`: `κ(W'_q)^{−2}κ(M_y)Θ^{ll}_{t+x}Θ^{lh}_{1+qx}`.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover

namespace PrimaryPair

variable (R : PrimaryPair)

/-! ### Hecke points -/

/-- `Θ(A_mw)`, `z ↦ mz`. -/
def hh (Θ : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ := Θ (R.dilation • w)

/-- `Θ(A_m⁻¹T_tw)`, `z ↦ (z + 3t)/m`. -/
def ll (Θ : HyperbolicSpace → ℂ) (t : O) (w : HyperbolicSpace) : ℂ :=
  Θ (R.contraction • (complexMatrix (transThree t) • w))

/-- `Θ(A_q⁻¹T_tA_pw)`, `z ↦ (pz + 3t)/q`. -/
def hl (Θ : HyperbolicSpace → ℂ) (t : O) (w : HyperbolicSpace) : ℂ :=
  Θ (R.Q.contraction • (complexMatrix (transThree t) • (R.P.dilation • w)))

/-- `Θ(A_p⁻¹T_tA_qw)`, `z ↦ (qz + 3t)/p`. -/
def lh (Θ : HyperbolicSpace → ℂ) (t : O) (w : HyperbolicSpace) : ℂ :=
  Θ (R.P.contraction • (complexMatrix (transThree t) • (R.Q.dilation • w)))

theorem complexCharacter_mHighMat : complexCharacter R.mHighMat = complexCharacter R.wM ^ 2 := by
  have h1 : ((R.mHighMat : levelThree) : SL(2, O)) 1 0 = 3 * R.mK := rfl
  have h2 : ((R.mHighMat : levelThree) : SL(2, O)) 0 0 = (R.P.p * R.Q.p) ^ 2 := rfl
  have h3 : ((R.wM : levelThree) : SL(2, O)) 1 0 = 3 * R.mK := rfl
  have h4 : ((R.wM : levelThree) : SL(2, O)) 0 0 = R.P.p * R.Q.p := rfl
  rw [complexCharacter_eq_symbol, complexCharacter_eq_symbol, h1, h2, h3, h4, pow_two, symbol_mul_denominator,
    map_mul, pow_two]

theorem isCoprime_crt (y₁ : {y : R.P.Res // y ≠ 0}) (y₂ : {y : R.Q.Res // y ≠ 0}) :
    IsCoprime (R.P.p * R.Q.p) (R.crt y₁.1 y₂.1) := by
  have hP : ¬ R.P.p ∣ R.crt y₁.1 y₂.1 := by rw [← R.P.res_eq_zero_iff, R.P_res_crt]; exact y₁.2
  have hQ : ¬ R.Q.p ∣ R.crt y₁.1 y₂.1 := by rw [← R.Q.res_eq_zero_iff, R.Q_res_crt]; exact y₂.2
  exact ((Irreducible.coprime_iff_not_dvd R.P.prime.irreducible).mpr hP).mul_left
    ((Irreducible.coprime_iff_not_dvd R.Q.prime.irreducible).mpr hQ)

theorem pInv_ne_zero : R.pInv ≠ 0 := inv_ne_zero R.Q_res_p_ne_zero

theorem qInv_ne_zero : R.qInv ≠ 0 := inv_ne_zero R.P_res_q_ne_zero

theorem Q_res_pDelta_ne_zero : R.Q.res R.pDelta ≠ 0 := by
  intro h
  have hd := congrArg R.Q.res R.p_det
  simp only [map_sub, map_mul, map_one, R.Q.res_nine, R.Q.res_p, h, mul_zero, zero_mul, sub_zero] at hd
  exact zero_ne_one hd

theorem P_res_qDelta_ne_zero : R.P.res R.qDelta ≠ 0 := by
  intro h
  have hd := congrArg R.P.res R.q_det
  simp only [map_sub, map_mul, map_one, R.P.res_nine, R.P.res_p, h, mul_zero, zero_mul, sub_zero] at hd
  exact zero_ne_one hd

/-- `y₀` of the `(U, L)` coset: `y = py₀`. -/
def yUL (y₂ : {y : R.Q.Res // y ≠ 0}) : O := R.Q.lift (y₂.1 * R.pInv)
/-- `y₀` of the `(L, U)` coset: `y = qy₀`. -/
def yLU (y₁ : {y : R.P.Res // y ≠ 0}) : O := R.P.lift (y₁.1 * R.qInv)
/-- `y₀` of the `(W, L)` coset. -/
def yWL (y₂ : {y : R.Q.Res // y ≠ 0}) : O := R.Q.lift (y₂.1 * R.Q.res R.pDelta * R.pInv ^ 2)
/-- `y₀` of the `(L, W)` coset. -/
def yLW (y₁ : {y : R.P.Res // y ≠ 0}) : O := R.P.lift (y₁.1 * R.P.res R.qDelta * R.qInv ^ 2)

theorem not_dvd_yUL (y₂ : {y : R.Q.Res // y ≠ 0}) : ¬ R.Q.p ∣ R.yUL y₂ := by
  rw [← R.Q.res_eq_zero_iff, yUL, R.Q.res_lift]
  exact mul_ne_zero y₂.2 R.pInv_ne_zero

theorem not_dvd_yLU (y₁ : {y : R.P.Res // y ≠ 0}) : ¬ R.P.p ∣ R.yLU y₁ := by
  rw [← R.P.res_eq_zero_iff, yLU, R.P.res_lift]
  exact mul_ne_zero y₁.2 R.qInv_ne_zero

theorem not_dvd_yWL (y₂ : {y : R.Q.Res // y ≠ 0}) : ¬ R.Q.p ∣ R.yWL y₂ := by
  rw [← R.Q.res_eq_zero_iff, yWL, R.Q.res_lift]
  exact mul_ne_zero (mul_ne_zero y₂.2 R.Q_res_pDelta_ne_zero) (pow_ne_zero 2 R.pInv_ne_zero)

theorem not_dvd_yLW (y₁ : {y : R.P.Res // y ≠ 0}) : ¬ R.P.p ∣ R.yLW y₁ := by
  rw [← R.P.res_eq_zero_iff, yLW, R.P.res_lift]
  exact mul_ne_zero (mul_ne_zero y₁.2 R.P_res_qDelta_ne_zero) (pow_ne_zero 2 R.qInv_ne_zero)

variable {R}

/-! ### The nine types -/

section Terms

variable (Θ : HyperbolicSpace → ℂ)
  (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
include hΘ

theorem theta_trans (t : O) (x : HyperbolicSpace) : Θ (complexMatrix (transThree t) • x) = Θ x := by
  rw [hΘ, complexCharacter_transThree, one_mul]

theorem theta_lower (t : O) (x : HyperbolicSpace) : Θ (complexMatrix (lowerThree t) • x) = Θ x := by
  rw [hΘ, complexCharacter_lowerThree, one_mul]

theorem term_UU (x₁ : R.P.Res) (x₂ : R.Q.Res) (w : HyperbolicSpace) :
    (complexCharacter (R.rep (.inl x₁, .inl x₂)) ^ 2)⁻¹ *
        R.heckeCorrelation Θ (complexMatrix (R.rep (.inl x₁, .inl x₂)) • w) =
      R.hh Θ w * R.ll Θ (R.crt x₁ x₂) w := by
  have hrep : R.rep (.inl x₁, .inl x₂) = transThree (R.crt x₁ x₂) := by
    simp [rep, gOf, yOf, xOf, lowerThree_zero]
  rw [hrep, complexCharacter_transThree, one_pow, inv_one, one_mul]
  unfold heckeCorrelation hh ll
  rw [← mul_smul, R.dilation_transThree, mul_smul, theta_trans Θ hΘ]

theorem term_WW (x₁ : R.P.Res) (x₂ : R.Q.Res) (w : HyperbolicSpace) :
    (complexCharacter (R.rep (.inr (.inl x₁), .inr (.inl x₂))) ^ 2)⁻¹ *
        R.heckeCorrelation Θ (complexMatrix (R.rep (.inr (.inl x₁), .inr (.inl x₂))) • w) =
      R.ll Θ (R.mShift + R.xOf (.inr (.inl x₁), .inr (.inl x₂))) w * R.hh Θ w := by
  set x := R.xOf (.inr (.inl x₁), .inr (.inl x₂))
  have hrep : R.rep (.inr (.inl x₁), .inr (.inl x₂)) = R.wM * transThree x := by
    simp [rep, gOf, yOf, x, lowerThree_zero]
  have hW : complexCharacter R.wM ≠ 0 := by
    intro h
    have := norm_complexCharacter R.wM
    rw [h, norm_zero] at this
    exact zero_ne_one this
  have h1 : Θ (R.dilation • (complexMatrix (R.wM * transThree x) • w)) =
      complexCharacter R.wM ^ 2 * Θ (R.contraction • (complexMatrix (transThree (R.mShift + x)) • w)) := by
    rw [map_mul, mul_smul, ← mul_smul R.dilation, R.dilation_wM, mul_smul, mul_smul, hΘ,
      R.complexCharacter_mHighMat, ← mul_smul (complexMatrix (transThree R.mShift)), ← map_mul,
      PrimaryPrime.transThree_mul]
  have h2 : Θ (R.contraction • (complexMatrix (R.wM * transThree x) • w)) = Θ (R.dilation • w) := by
    rw [map_mul, mul_smul, ← mul_smul R.contraction, R.contraction_wM, mul_smul, mul_smul, theta_lower Θ hΘ,
      theta_trans Θ hΘ, ← mul_smul, R.dilation_transThree, mul_smul, theta_trans Θ hΘ]
  rw [hrep, map_mul, complexCharacter_transThree, mul_one]
  unfold heckeCorrelation hh ll
  rw [h1, h2, ← mul_assoc, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hW), one_mul]

theorem term_LL (x₁ : R.P.Res) (y₁ : {y : R.P.Res // y ≠ 0}) (x₂ : R.Q.Res) (y₂ : {y : R.Q.Res // y ≠ 0})
    (w : HyperbolicSpace) :
    (complexCharacter (R.rep (.inr (.inr (x₁, y₁)), .inr (.inr (x₂, y₂)))) ^ 2)⁻¹ *
        R.heckeCorrelation Θ (complexMatrix (R.rep (.inr (.inr (x₁, y₁)), .inr (.inr (x₂, y₂)))) • w) =
      ringComplex (symbol (3 * R.crt y₁.1 y₂.1) (R.P.p * R.Q.p)) *
        R.ll Θ (R.crt x₁ x₂ - R.mLowBeta (R.crt y₁.1 y₂.1)) w * R.ll Θ (R.crt x₁ x₂) w := by
  set y := R.crt y₁.1 y₂.1
  set x := R.crt x₁ x₂
  have hy := R.isCoprime_crt y₁ y₂
  have hrep : R.rep (.inr (.inr (x₁, y₁)), .inr (.inr (x₂, y₂))) = lowerThree y * transThree x := by
    simp [rep, gOf, yOf, xOf, x, y]
  have h1 : Θ (R.dilation • (complexMatrix (lowerThree y * transThree x) • w)) =
      ringComplex (symbol (3 * y) (R.P.p * R.Q.p)) *
        Θ (R.contraction • (complexMatrix (transThree (x - R.mLowBeta y)) • w)) := by
    rw [map_mul, mul_smul, ← mul_smul R.dilation, R.dilation_lowerThree y hy, mul_smul, mul_smul, hΘ,
      ← mul_smul (complexMatrix (transThree (-R.mLowBeta y))), ← map_mul, PrimaryPrime.transThree_mul,
      show -R.mLowBeta y + x = x - R.mLowBeta y by ring]
    rfl
  have h2 : Θ (R.contraction • (complexMatrix (lowerThree y * transThree x) • w)) =
      Θ (R.contraction • (complexMatrix (transThree x) • w)) := by
    rw [map_mul, mul_smul, ← mul_smul R.contraction, R.contraction_lowerThree, mul_smul, theta_lower Θ hΘ]
  rw [hrep, map_mul, complexCharacter_transThree, complexCharacter_lowerThree, one_mul, one_pow, inv_one, one_mul]
  unfold heckeCorrelation ll
  rw [h1, h2]

theorem term_UW (x₁ : R.P.Res) (x₂ : R.Q.Res) (w : HyperbolicSpace) :
    (complexCharacter (R.rep (.inl x₁, .inr (.inl x₂))) ^ 2)⁻¹ *
        R.heckeCorrelation Θ (complexMatrix (R.rep (.inl x₁, .inr (.inl x₂))) • w) =
      (complexCharacter R.wQ ^ 2)⁻¹ * complexCharacter R.qHighUp *
        R.hl Θ (R.P.p * (R.qShift + R.xOf (.inl x₁, .inr (.inl x₂)))) w *
        R.lh Θ (1 + R.Q.p * R.xOf (.inl x₁, .inr (.inl x₂))) w := by
  set x := R.xOf (.inl x₁, .inr (.inl x₂))
  have hrep : R.rep (.inl x₁, .inr (.inl x₂)) = R.wQ * transThree x := by
    simp [rep, gOf, yOf, x, lowerThree_zero]
  have h1 : Θ (R.dilation • (complexMatrix (R.wQ * transThree x) • w)) =
      complexCharacter R.qHighUp *
        Θ (R.Q.contraction • (complexMatrix (transThree (R.P.p * (R.qShift + x))) • (R.P.dilation • w))) := by
    rw [dilation, map_mul, mul_smul, mul_smul, ← mul_smul R.Q.dilation, R.dilation_wQ, mul_smul, mul_smul,
      ← mul_smul R.P.dilation, R.dilP_qHighMat, mul_smul, hΘ, ← mul_smul (complexMatrix (transThree R.qShift)),
      ← map_mul, PrimaryPrime.transThree_mul, ← mul_smul R.P.dilation, R.dilP_conQ, mul_smul,
      ← mul_smul R.P.dilation, R.P.dilation_transThree, mul_smul]
  have h2 : Θ (R.contraction • (complexMatrix (R.wQ * transThree x) • w)) =
      Θ (R.P.contraction • (complexMatrix (transThree (1 + R.Q.p * x)) • (R.Q.dilation • w))) := by
    rw [contraction, map_mul, mul_smul, mul_smul, ← mul_smul R.Q.contraction, R.contraction_wQ, mul_smul,
      mul_smul, ← mul_smul R.P.contraction, R.P.contraction_lowerThree, mul_smul, theta_lower Θ hΘ,
      ← mul_smul R.Q.dilation, R.Q.dilation_transThree, mul_smul, ← mul_smul (complexMatrix (transThree 1)),
      ← map_mul, PrimaryPrime.transThree_mul]
  rw [hrep, map_mul, complexCharacter_transThree, mul_one]
  unfold heckeCorrelation hl lh
  rw [h1, h2]
  ring

theorem term_WU (x₁ : R.P.Res) (x₂ : R.Q.Res) (w : HyperbolicSpace) :
    (complexCharacter (R.rep (.inr (.inl x₁), .inl x₂)) ^ 2)⁻¹ *
        R.heckeCorrelation Θ (complexMatrix (R.rep (.inr (.inl x₁), .inl x₂)) • w) =
      (complexCharacter R.wP ^ 2)⁻¹ * complexCharacter R.pHighUp *
        R.lh Θ (R.Q.p * (R.pShift + R.xOf (.inr (.inl x₁), .inl x₂))) w *
        R.hl Θ (1 + R.P.p * R.xOf (.inr (.inl x₁), .inl x₂)) w := by
  set x := R.xOf (.inr (.inl x₁), .inl x₂)
  have hrep : R.rep (.inr (.inl x₁), .inl x₂) = R.wP * transThree x := by
    simp [rep, gOf, yOf, x, lowerThree_zero]
  have h1 : Θ (R.dilation • (complexMatrix (R.wP * transThree x) • w)) =
      complexCharacter R.pHighUp *
        Θ (R.P.contraction • (complexMatrix (transThree (R.Q.p * (R.pShift + x))) • (R.Q.dilation • w))) := by
    rw [dilation, R.dil_dil, map_mul, mul_smul, mul_smul, ← mul_smul R.P.dilation, R.dilation_wP, mul_smul,
      mul_smul, ← mul_smul R.Q.dilation, R.dilQ_pHighMat, mul_smul, hΘ,
      ← mul_smul (complexMatrix (transThree R.pShift)), ← map_mul, PrimaryPrime.transThree_mul,
      ← mul_smul R.Q.dilation, R.dilQ_conP, mul_smul, ← mul_smul R.Q.dilation, R.Q.dilation_transThree, mul_smul]
  have h2 : Θ (R.contraction • (complexMatrix (R.wP * transThree x) • w)) =
      Θ (R.Q.contraction • (complexMatrix (transThree (1 + R.P.p * x)) • (R.P.dilation • w))) := by
    rw [contraction, R.con_con, map_mul, mul_smul, mul_smul, ← mul_smul R.P.contraction, R.contraction_wP,
      mul_smul, mul_smul, ← mul_smul R.Q.contraction, R.Q.contraction_lowerThree, mul_smul, theta_lower Θ hΘ,
      ← mul_smul R.P.dilation, R.P.dilation_transThree, mul_smul, ← mul_smul (complexMatrix (transThree 1)),
      ← map_mul, PrimaryPrime.transThree_mul]
  rw [hrep, map_mul, complexCharacter_transThree, mul_one]
  unfold heckeCorrelation hl lh
  rw [h1, h2]
  ring

theorem term_UL (x₁ : R.P.Res) (x₂ : R.Q.Res) (y₂ : {y : R.Q.Res // y ≠ 0}) (w : HyperbolicSpace) :
    (complexCharacter (R.rep (.inl x₁, .inr (.inr (x₂, y₂)))) ^ 2)⁻¹ *
        R.heckeCorrelation Θ (complexMatrix (R.rep (.inl x₁, .inr (.inr (x₂, y₂)))) • w) =
      ringComplex (symbol (3 * R.yUL y₂) R.Q.p) *
        R.hl Θ (R.P.p * R.crt x₁ x₂ - R.Q.lowBeta (R.yUL y₂)) w * R.ll Θ (R.crt x₁ x₂) w := by
  set x := R.crt x₁ x₂
  set y := R.yUL y₂
  have hy := R.not_dvd_yUL y₂
  have hrep : R.rep (.inl x₁, .inr (.inr (x₂, y₂))) = lowerThree (R.P.p * y) * transThree x := by
    simp [rep, gOf, yOf, xOf, x, y, yUL]
  have h1 : Θ (R.dilation • (complexMatrix (lowerThree (R.P.p * y) * transThree x) • w)) =
      ringComplex (symbol (3 * y) R.Q.p) *
        Θ (R.Q.contraction • (complexMatrix (transThree (R.P.p * x - R.Q.lowBeta y)) • (R.P.dilation • w))) := by
    rw [dilation, R.dil_dil, map_mul, mul_smul, mul_smul, ← mul_smul R.P.dilation, R.P.dilation_lowerThree_mul,
      mul_smul, ← mul_smul R.Q.dilation, R.Q.dilation_lowerThree y hy, mul_smul, mul_smul, hΘ,
      R.Q.complexCharacter_lowMat y hy, ← mul_smul R.P.dilation, R.P.dilation_transThree, mul_smul,
      ← mul_smul (complexMatrix (transThree (-R.Q.lowBeta y))), ← map_mul, PrimaryPrime.transThree_mul,
      show -R.Q.lowBeta y + R.P.p * x = R.P.p * x - R.Q.lowBeta y by ring]
  have h2 : Θ (R.contraction • (complexMatrix (lowerThree (R.P.p * y) * transThree x) • w)) =
      Θ (R.contraction • (complexMatrix (transThree x) • w)) := by
    rw [map_mul, mul_smul, ← mul_smul R.contraction, R.contraction_lowerThree, mul_smul, theta_lower Θ hΘ]
  rw [hrep, map_mul, complexCharacter_transThree, complexCharacter_lowerThree, one_mul, one_pow, inv_one, one_mul]
  unfold heckeCorrelation hl ll
  rw [h1, h2]

theorem term_LU (x₁ : R.P.Res) (y₁ : {y : R.P.Res // y ≠ 0}) (x₂ : R.Q.Res) (w : HyperbolicSpace) :
    (complexCharacter (R.rep (.inr (.inr (x₁, y₁)), .inl x₂)) ^ 2)⁻¹ *
        R.heckeCorrelation Θ (complexMatrix (R.rep (.inr (.inr (x₁, y₁)), .inl x₂)) • w) =
      ringComplex (symbol (3 * R.yLU y₁) R.P.p) *
        R.lh Θ (R.Q.p * R.crt x₁ x₂ - R.P.lowBeta (R.yLU y₁)) w * R.ll Θ (R.crt x₁ x₂) w := by
  set x := R.crt x₁ x₂
  set y := R.yLU y₁
  have hy := R.not_dvd_yLU y₁
  have hrep : R.rep (.inr (.inr (x₁, y₁)), .inl x₂) = lowerThree (R.Q.p * y) * transThree x := by
    simp [rep, gOf, yOf, xOf, x, y, yLU]
  have h1 : Θ (R.dilation • (complexMatrix (lowerThree (R.Q.p * y) * transThree x) • w)) =
      ringComplex (symbol (3 * y) R.P.p) *
        Θ (R.P.contraction • (complexMatrix (transThree (R.Q.p * x - R.P.lowBeta y)) • (R.Q.dilation • w))) := by
    rw [dilation, map_mul, mul_smul, mul_smul, ← mul_smul R.Q.dilation, R.Q.dilation_lowerThree_mul,
      mul_smul, ← mul_smul R.P.dilation, R.P.dilation_lowerThree y hy, mul_smul, mul_smul, hΘ,
      R.P.complexCharacter_lowMat y hy, ← mul_smul R.Q.dilation, R.Q.dilation_transThree, mul_smul,
      ← mul_smul (complexMatrix (transThree (-R.P.lowBeta y))), ← map_mul, PrimaryPrime.transThree_mul,
      show -R.P.lowBeta y + R.Q.p * x = R.Q.p * x - R.P.lowBeta y by ring]
  have h2 : Θ (R.contraction • (complexMatrix (lowerThree (R.Q.p * y) * transThree x) • w)) =
      Θ (R.contraction • (complexMatrix (transThree x) • w)) := by
    rw [map_mul, mul_smul, ← mul_smul R.contraction, R.contraction_lowerThree, mul_smul, theta_lower Θ hΘ]
  rw [hrep, map_mul, complexCharacter_transThree, complexCharacter_lowerThree, one_mul, one_pow, inv_one, one_mul]
  unfold heckeCorrelation lh ll
  rw [h1, h2]

theorem term_WL (x₁ : R.P.Res) (x₂ : R.Q.Res) (y₂ : {y : R.Q.Res // y ≠ 0}) (w : HyperbolicSpace) :
    (complexCharacter (R.rep (.inr (.inl x₁), .inr (.inr (x₂, y₂)))) ^ 2)⁻¹ *
        R.heckeCorrelation Θ (complexMatrix (R.rep (.inr (.inl x₁), .inr (.inr (x₂, y₂)))) • w) =
      (complexCharacter R.wP ^ 2)⁻¹ * complexCharacter (R.wlMat (R.yWL y₂) (R.not_dvd_yWL y₂)) *
        R.ll Θ (R.wlShift (R.yWL y₂) + R.xOf (.inr (.inl x₁), .inr (.inr (x₂, y₂)))) w *
        R.hl Θ (1 + R.P.p * R.xOf (.inr (.inl x₁), .inr (.inr (x₂, y₂)))) w := by
  set x := R.xOf (.inr (.inl x₁), .inr (.inr (x₂, y₂)))
  set y := R.yWL y₂
  have hy := R.not_dvd_yWL y₂
  have hrep : R.rep (.inr (.inl x₁), .inr (.inr (x₂, y₂))) = lowerThree (R.P.p * y) * R.wP * transThree x := by
    simp [rep, gOf, yOf, x, y, yWL]
  have h1 : Θ (R.dilation • (complexMatrix (lowerThree (R.P.p * y) * R.wP * transThree x) • w)) =
      complexCharacter (R.wlMat y hy) * Θ (R.contraction • (complexMatrix (transThree (R.wlShift y + x)) • w)) := by
    rw [map_mul (complexMatrix) (lowerThree (R.P.p * y) * R.wP), mul_smul, ← mul_smul R.dilation,
      R.dilation_wl y hy, mul_smul, mul_smul, hΘ, ← mul_smul (complexMatrix (transThree (R.wlShift y))), ← map_mul,
      PrimaryPrime.transThree_mul]
  have h2 : Θ (R.contraction • (complexMatrix (lowerThree (R.P.p * y) * R.wP * transThree x) • w)) =
      Θ (R.Q.contraction • (complexMatrix (transThree (1 + R.P.p * x)) • (R.P.dilation • w))) := by
    rw [map_mul (complexMatrix) (lowerThree (R.P.p * y) * R.wP), mul_smul, ← mul_smul R.contraction,
      R.contraction_wl y, mul_smul, mul_smul, mul_smul, theta_lower Θ hΘ, ← mul_smul R.P.dilation,
      R.P.dilation_transThree, mul_smul, ← mul_smul (complexMatrix (transThree 1)), ← map_mul,
      PrimaryPrime.transThree_mul]
  have hk : complexCharacter (lowerThree (R.P.p * y) * R.wP * transThree x) = complexCharacter R.wP := by
    rw [map_mul, map_mul, complexCharacter_lowerThree, complexCharacter_transThree, one_mul, mul_one]
  rw [hrep, hk]
  unfold heckeCorrelation hl ll
  rw [h1, h2]
  ring

theorem term_LW (x₁ : R.P.Res) (y₁ : {y : R.P.Res // y ≠ 0}) (x₂ : R.Q.Res) (w : HyperbolicSpace) :
    (complexCharacter (R.rep (.inr (.inr (x₁, y₁)), .inr (.inl x₂))) ^ 2)⁻¹ *
        R.heckeCorrelation Θ (complexMatrix (R.rep (.inr (.inr (x₁, y₁)), .inr (.inl x₂))) • w) =
      (complexCharacter R.wQ ^ 2)⁻¹ * complexCharacter (R.lwMat (R.yLW y₁) (R.not_dvd_yLW y₁)) *
        R.ll Θ (R.lwShift (R.yLW y₁) + R.xOf (.inr (.inr (x₁, y₁)), .inr (.inl x₂))) w *
        R.lh Θ (1 + R.Q.p * R.xOf (.inr (.inr (x₁, y₁)), .inr (.inl x₂))) w := by
  set x := R.xOf (.inr (.inr (x₁, y₁)), .inr (.inl x₂))
  set y := R.yLW y₁
  have hy := R.not_dvd_yLW y₁
  have hrep : R.rep (.inr (.inr (x₁, y₁)), .inr (.inl x₂)) = lowerThree (R.Q.p * y) * R.wQ * transThree x := by
    simp [rep, gOf, yOf, x, y, yLW]
  have h1 : Θ (R.dilation • (complexMatrix (lowerThree (R.Q.p * y) * R.wQ * transThree x) • w)) =
      complexCharacter (R.lwMat y hy) * Θ (R.contraction • (complexMatrix (transThree (R.lwShift y + x)) • w)) := by
    rw [map_mul (complexMatrix) (lowerThree (R.Q.p * y) * R.wQ), mul_smul, ← mul_smul R.dilation,
      R.dilation_lw y hy, mul_smul, mul_smul, hΘ, ← mul_smul (complexMatrix (transThree (R.lwShift y))), ← map_mul,
      PrimaryPrime.transThree_mul]
  have h2 : Θ (R.contraction • (complexMatrix (lowerThree (R.Q.p * y) * R.wQ * transThree x) • w)) =
      Θ (R.P.contraction • (complexMatrix (transThree (1 + R.Q.p * x)) • (R.Q.dilation • w))) := by
    rw [map_mul (complexMatrix) (lowerThree (R.Q.p * y) * R.wQ), mul_smul, ← mul_smul R.contraction,
      R.contraction_lw y, mul_smul, mul_smul, mul_smul, theta_lower Θ hΘ, ← mul_smul R.Q.dilation,
      R.Q.dilation_transThree, mul_smul, ← mul_smul (complexMatrix (transThree 1)), ← map_mul,
      PrimaryPrime.transThree_mul]
  have hk : complexCharacter (lowerThree (R.Q.p * y) * R.wQ * transThree x) = complexCharacter R.wQ := by
    rw [map_mul, map_mul, complexCharacter_lowerThree, complexCharacter_transThree, one_mul, mul_one]
  rw [hrep, hk]
  unfold heckeCorrelation lh ll
  rw [h1, h2]
  ring

end Terms

end PrimaryPair

end GaloisForLFunctions.OrderSixMetaplecticTheory
