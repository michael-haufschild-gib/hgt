import GaloisForLFunctions.OrderSixMetaplecticTheory.TheHeckeTraceAtAPrimaryPrimeIsAPhasedSumOverHeckePoints

/-!
# The Hecke trace at a product of two primary primes is a sum over pairs of cosets

For coprime primary primes `p, q` (`PrimaryPair`) and `m = pq`, `A_m = A_pA_q` (`z ↦ mz`) and the correlation
`F_Θ(w) = Θ(A_mw)Θ(A_m⁻¹w)` has the multiplier `κ²` on `Γ_m = Γ_p ∩ Γ_q` (`heckeCorrelation_automorphy`): the
`q`-adic nebentypus cancels between the two Hecke points as at a prime, and the `p`-adic one cancels after it,
`κ(A_pγ'A_p⁻¹)(p/a)₃ = κ(γ')`, `κ(A_p⁻¹γ''A_p) = κ(γ'')(p/a)₃`.

A coset of `Γ(3)/Γ_m` is a pair of cosets of `Γ(3)/Γ_p` and `Γ(3)/Γ_q` (`cosetOf_bijective`). The representative of
`(i, j)` is `L(y)·G·T_x` (`rep`) with `x, y` fixed by the Chinese remainder theorem and `G` one of
`1`, `W_m = [[m, 3], [3k, δ]]`, `W'_q = [[q, 3], [3pk', δ']]` (`W`-type at `q`, `U`-type at `p`) and `W'_p`; its rows are
proportional to those of the prime representatives at `p` and at `q` (`rep_mul_inv_P`, `rep_mul_inv_Q`). So
(`heckeTrace_eq_sum`) `Tr_mF_Θ(w) = Σ_{(i, j)} κ(δ_{ij})^{−2} F_Θ(δ_{ij}w)` over `P.Index × Q.Index`.
-/

noncomputable section

open scoped BigOperators Classical MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicJacobi
  MetaplecticMobiusDescent.CubicEisenstein MetaplecticMobiusDescent.CubicKubota SpectralTheoryOfTheCubicCover

namespace HeckeEntries

variable {P : PrimaryPrime} (e : HeckeEntries P)

/-- `κ(A_pγA_p⁻¹)(p/a)₃ = κ(γ)`. -/
theorem character_up_mul_symbol :
    complexCharacter e.up * ringComplex (symbol P.p e.a) = complexCharacter e.mat := by
  have h1 : ((e.up : levelThree) : SL(2, O)) 1 0 = e.c := rfl
  have h2 : ((e.up : levelThree) : SL(2, O)) 0 0 = e.a := rfl
  have h5 : ((e.mat : levelThree) : SL(2, O)) 1 0 = P.p * e.c := rfl
  have h6 : ((e.mat : levelThree) : SL(2, O)) 0 0 = e.a := rfl
  rw [complexCharacter_eq_symbol, complexCharacter_eq_symbol, h1, h2, h5, h6]
  simp only [symbol_mul_numerator, map_mul]
  ring

/-- `κ(A_p⁻¹γA_p) = κ(γ)(p/a)₃`. -/
theorem character_down :
    complexCharacter e.down = complexCharacter e.mat * ringComplex (symbol P.p e.a) := by
  have h3 : ((e.down : levelThree) : SL(2, O)) 1 0 = P.p ^ 2 * e.c := rfl
  have h4 : ((e.down : levelThree) : SL(2, O)) 0 0 = e.a := rfl
  have h5 : ((e.mat : levelThree) : SL(2, O)) 1 0 = P.p * e.c := rfl
  have h6 : ((e.mat : levelThree) : SL(2, O)) 0 0 = e.a := rfl
  rw [complexCharacter_eq_symbol, complexCharacter_eq_symbol, h3, h4, h5, h6, pow_two]
  simp only [symbol_mul_numerator, map_mul]
  ring

end HeckeEntries

/-- Two coprime primary primes. -/
structure PrimaryPair where
  P : PrimaryPrime
  Q : PrimaryPrime
  coprime : IsCoprime P.p Q.p

namespace PrimaryPair

variable (R : PrimaryPair)

/-! ### The correlation -/

/-- `A_m = A_pA_q`. -/
def dilation : SL(2, ℂ) := R.P.dilation * R.Q.dilation

/-- `A_m⁻¹ = A_p⁻¹A_q⁻¹`. -/
def contraction : SL(2, ℂ) := R.P.contraction * R.Q.contraction

/-- `Γ_m = Γ_p ∩ Γ_q`. -/
def heckeGroup : Subgroup levelThree := R.P.heckeGroup ⊓ R.Q.heckeGroup

/-- The correlation `F_Θ(w) = Θ(A_mw)Θ(A_m⁻¹w)`. -/
def heckeCorrelation (Θ : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ :=
  Θ (R.dilation • w) * Θ (R.contraction • w)

theorem p_dvd_of_dvd_q_mul {x : O} (h : R.P.p ∣ R.Q.p * x) : R.P.p ∣ x := R.coprime.dvd_of_dvd_mul_left h

/-- **The correlation has the multiplier `κ²` on `Γ_m`.** -/
theorem heckeCorrelation_automorphy (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (γ : levelThree) (hγ : γ ∈ R.heckeGroup) (w : HyperbolicSpace) :
    R.heckeCorrelation Θ (complexMatrix γ • w) = complexCharacter γ ^ 2 * R.heckeCorrelation Θ w := by
  obtain ⟨eQ, rfl⟩ := R.Q.exists_entries_of_mem γ hγ.2
  have hb : R.P.p ∣ eQ.b := R.p_dvd_of_dvd_q_mul hγ.1.1
  have hc : R.P.p ∣ eQ.c := R.p_dvd_of_dvd_q_mul hγ.1.2
  have hup : eQ.up ∈ R.P.heckeGroup := ⟨hb.mul_left _, hc⟩
  have hdown : eQ.down ∈ R.P.heckeGroup := ⟨hb, hc.mul_left _⟩
  obtain ⟨e₁, he₁⟩ := R.P.exists_entries_of_mem _ hup
  obtain ⟨e₂, he₂⟩ := R.P.exists_entries_of_mem _ hdown
  have ha₁ : e₁.a = eQ.a := by
    have h := congrArg (fun M : levelThree => (M : SL(2, O)) 0 0) he₁
    simpa [HeckeEntries.mat, HeckeEntries.up] using h
  have ha₂ : e₂.a = eQ.a := by
    have h := congrArg (fun M : levelThree => (M : SL(2, O)) 0 0) he₂
    simpa [HeckeEntries.mat, HeckeEntries.down] using h
  have h1 := e₁.character_up_mul_symbol
  rw [he₁, ha₁] at h1
  have h2 := e₂.character_down
  rw [he₂, ha₂] at h2
  have hk : complexCharacter e₁.up * complexCharacter e₂.down = complexCharacter eQ.mat ^ 2 := by
    rw [h2, ← eQ.character_up_mul_down, ← h1]
    ring
  have hd : Θ (R.dilation • (complexMatrix eQ.mat • w)) = complexCharacter e₁.up * Θ (R.dilation • w) := by
    rw [dilation, mul_smul, ← mul_smul R.Q.dilation, eQ.dilation_mul, mul_smul, ← mul_smul R.P.dilation, ← he₁,
      e₁.dilation_mul, mul_smul, hΘ, ← mul_smul]
  have hc' : Θ (R.contraction • (complexMatrix eQ.mat • w)) =
      complexCharacter e₂.down * Θ (R.contraction • w) := by
    rw [contraction, mul_smul, ← mul_smul R.Q.contraction, eQ.contraction_mul, mul_smul,
      ← mul_smul R.P.contraction, ← he₂, e₂.contraction_mul, mul_smul, hΘ, ← mul_smul]
  unfold heckeCorrelation
  rw [hd, hc', ← hk]
  ring

instance : R.heckeGroup.FiniteIndex := by unfold heckeGroup; infer_instance

noncomputable instance : Fintype (levelThree ⧸ R.heckeGroup) := Subgroup.fintypeQuotientOfFiniteIndex

/-- **The Hecke trace at `m`** `Tr_mF_Θ(w) = Σ_{γΓ_m} κ(γ)² F_Θ(γ⁻¹w)`. -/
def heckeTrace (Θ : HyperbolicSpace → ℂ) (w : HyperbolicSpace) : ℂ :=
  cosetTrace complexMatrix R.heckeGroup kubotaSquare (R.heckeCorrelation Θ) w

/-- The Hecke trace at `m` has the multiplier `κ²` on `Γ(3)`. -/
theorem heckeTrace_automorphy (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (M : levelThree) (w : HyperbolicSpace) :
    R.heckeTrace Θ (complexMatrix M • w) = complexCharacter M ^ 2 * R.heckeTrace Θ w :=
  cosetTrace_smul (ρ := complexMatrix) (H := R.heckeGroup) (χ := kubotaSquare)
    (F := R.heckeCorrelation Θ) (fun δ hδ x => by
      rw [kubotaSquare_apply]
      exact R.heckeCorrelation_automorphy Θ hΘ δ hδ x) M w

/-! ### Chinese remainder data -/

/-- `u` in `up + vq = 1`. -/
def crtU : O := R.coprime.choose

/-- `v` in `up + vq = 1`. -/
def crtV : O := R.coprime.choose_spec.choose

theorem crt_spec : R.crtU * R.P.p + R.crtV * R.Q.p = 1 := R.coprime.choose_spec.choose_spec

/-- `e_p = vq ≡ 1 mod p`, `≡ 0 mod q`. -/
def ep : O := R.crtV * R.Q.p

/-- `e_q = up ≡ 1 mod q`, `≡ 0 mod p`. -/
def eq : O := R.crtU * R.P.p

theorem P_res_ep : R.P.res R.ep = 1 := by
  have h := congrArg R.P.res R.crt_spec
  rw [map_add, map_mul, map_mul, R.P.res_p, mul_zero, zero_add, map_one] at h
  rw [ep, map_mul]
  exact h

theorem P_res_eq : R.P.res R.eq = 0 := by rw [eq, map_mul, R.P.res_p, mul_zero]

theorem Q_res_ep : R.Q.res R.ep = 0 := by rw [ep, map_mul, R.Q.res_p, mul_zero]

theorem Q_res_eq : R.Q.res R.eq = 1 := by
  have h := congrArg R.Q.res R.crt_spec
  rw [map_add, map_mul, map_mul, R.Q.res_p, mul_zero, add_zero, map_one] at h
  rw [eq, map_mul]
  exact h

/-- The element of `O` with residues `r₁` mod `p` and `r₂` mod `q`. -/
def crt (r₁ : R.P.Res) (r₂ : R.Q.Res) : O := R.ep * R.P.lift r₁ + R.eq * R.Q.lift r₂

@[simp] theorem P_res_crt (r₁ : R.P.Res) (r₂ : R.Q.Res) : R.P.res (R.crt r₁ r₂) = r₁ := by
  rw [crt, map_add, map_mul, map_mul, R.P_res_ep, R.P_res_eq, R.P.res_lift]
  ring

@[simp] theorem Q_res_crt (r₁ : R.P.Res) (r₂ : R.Q.Res) : R.Q.res (R.crt r₁ r₂) = r₂ := by
  rw [crt, map_add, map_mul, map_mul, R.Q_res_ep, R.Q_res_eq, R.Q.res_lift]
  ring

theorem P_res_q_ne_zero : R.P.res R.Q.p ≠ 0 := by
  rw [Ne, R.P.res_eq_zero_iff]
  intro h
  exact R.P.prime.not_unit (R.coprime.isUnit_of_dvd' (dvd_refl _) h)

theorem Q_res_p_ne_zero : R.Q.res R.P.p ≠ 0 := by
  rw [Ne, R.Q.res_eq_zero_iff]
  intro h
  exact R.Q.prime.not_unit (R.coprime.symm.isUnit_of_dvd' (dvd_refl _) h)

/-! ### Bezout matrices -/

theorem isCoprime_nine_p : IsCoprime (9 : O) R.P.p := by
  have := R.P.isCoprime_three.pow_left (m := 2)
  norm_num at this
  exact this

theorem isCoprime_nine_q : IsCoprime (9 : O) R.Q.p := by
  have := R.Q.isCoprime_three.pow_left (m := 2)
  norm_num at this
  exact this

theorem exists_mBezout : ∃ δ k : O, R.P.p * R.Q.p * δ - 9 * k = 1 := by
  obtain ⟨u, v, h⟩ := (R.isCoprime_nine_p.mul_right R.isCoprime_nine_q).symm
  exact ⟨u, -v, by linear_combination h⟩

theorem exists_qBezout : ∃ δ k : O, R.Q.p * δ - 9 * (R.P.p * k) = 1 := by
  obtain ⟨u, v, h⟩ := (R.isCoprime_nine_q.symm.mul_right R.coprime.symm)
  exact ⟨u, -v, by linear_combination h⟩

theorem exists_pBezout : ∃ δ k : O, R.P.p * δ - 9 * (R.Q.p * k) = 1 := by
  obtain ⟨u, v, h⟩ := (R.isCoprime_nine_p.symm.mul_right R.coprime)
  exact ⟨u, -v, by linear_combination h⟩

/-- `δ` in `mδ − 9k = 1`. -/
def mDelta : O := R.exists_mBezout.choose
/-- `k` in `mδ − 9k = 1`. -/
def mK : O := R.exists_mBezout.choose_spec.choose
theorem m_det : R.P.p * R.Q.p * R.mDelta - 9 * R.mK = 1 := R.exists_mBezout.choose_spec.choose_spec

/-- `δ'` in `qδ' − 9pk' = 1`. -/
def qDelta : O := R.exists_qBezout.choose
/-- `k'` in `qδ' − 9pk' = 1`. -/
def qK : O := R.exists_qBezout.choose_spec.choose
theorem q_det : R.Q.p * R.qDelta - 9 * (R.P.p * R.qK) = 1 := R.exists_qBezout.choose_spec.choose_spec

/-- `δ''` in `pδ'' − 9qk'' = 1`. -/
def pDelta : O := R.exists_pBezout.choose
/-- `k''` in `pδ'' − 9qk'' = 1`. -/
def pK : O := R.exists_pBezout.choose_spec.choose
theorem p_det : R.P.p * R.pDelta - 9 * (R.Q.p * R.pK) = 1 := R.exists_pBezout.choose_spec.choose_spec

theorem three_dvd_m_sub_one : (3 : O) ∣ R.P.p * R.Q.p - 1 := by
  obtain ⟨s, hs⟩ := R.P.three_dvd_sub_one
  obtain ⟨t, ht⟩ := R.Q.three_dvd_sub_one
  exact ⟨s * R.Q.p + t, by linear_combination R.Q.p * hs + ht⟩

theorem three_dvd_delta_sub_one {n δ k : O} (hn : (3 : O) ∣ n - 1) (h : n * δ - 9 * k = 1) : (3 : O) ∣ δ - 1 := by
  obtain ⟨t, ht⟩ := hn
  exact ⟨3 * k - δ * t, by linear_combination h - δ * ht⟩

/-- `W_m = [[m, 3], [3k, δ]]`. -/
def wM : levelThree :=
  ⟨⟨!![R.P.p * R.Q.p, 3; 3 * R.mK, R.mDelta], by rw [Matrix.det_fin_two_of]; linear_combination R.m_det⟩,
    levelThree_of_entries _ (by
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using R.three_dvd_m_sub_one
      · simp
      · simp
      · simpa using three_dvd_delta_sub_one R.three_dvd_m_sub_one R.m_det)⟩

/-- `W'_q = [[q, 3], [3pk', δ']]`: `W`-type at `q`, `U`-type at `p`. -/
def wQ : levelThree :=
  ⟨⟨!![R.Q.p, 3; 3 * (R.P.p * R.qK), R.qDelta], by rw [Matrix.det_fin_two_of]; linear_combination R.q_det⟩,
    levelThree_of_entries _ (by
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using R.Q.three_dvd_sub_one
      · simp
      · simp
      · simpa using three_dvd_delta_sub_one R.Q.three_dvd_sub_one R.q_det)⟩

/-- `W'_p = [[p, 3], [3qk'', δ'']]`: `W`-type at `p`, `U`-type at `q`. -/
def wP : levelThree :=
  ⟨⟨!![R.P.p, 3; 3 * (R.Q.p * R.pK), R.pDelta], by rw [Matrix.det_fin_two_of]; linear_combination R.p_det⟩,
    levelThree_of_entries _ (by
      intro i j
      fin_cases i <;> fin_cases j
      · simpa using R.P.three_dvd_sub_one
      · simp
      · simp
      · simpa using three_dvd_delta_sub_one R.P.three_dvd_sub_one R.p_det)⟩

/-! ### Representatives -/

/-- The index of the cosets of `Γ_m`: a coset at `p` and a coset at `q`. -/
abbrev Index := R.P.Index × R.Q.Index

/-- `q⁻¹` modulo `p`. -/
def qInv : R.P.Res := (R.P.res R.Q.p)⁻¹
/-- `p⁻¹` modulo `q`. -/
def pInv : R.Q.Res := (R.Q.res R.P.p)⁻¹

/-- The middle factor `G` of the representative. -/
def gOf : R.Index → levelThree
  | (.inr (.inl _), .inr (.inl _)) => R.wM
  | (.inl _, .inr (.inl _)) => R.wQ
  | (.inr (.inr _), .inr (.inl _)) => R.wQ
  | (.inr (.inl _), .inl _) => R.wP
  | (.inr (.inl _), .inr (.inr _)) => R.wP
  | _ => 1

/-- The lower-triangular parameter `y` of the representative. -/
def yOf : R.Index → O
  | (.inr (.inr (_, y₁)), .inr (.inr (_, y₂))) => R.crt y₁.1 y₂.1
  | (.inl _, .inr (.inr (_, y₂))) => R.crt 0 y₂.1
  | (.inr (.inr (_, y₁)), .inl _) => R.crt y₁.1 0
  | (.inr (.inl _), .inr (.inr (_, y₂))) => R.crt 0 (y₂.1 * R.Q.res R.pDelta * R.pInv)
  | (.inr (.inr (_, y₁)), .inr (.inl _)) => R.crt (y₁.1 * R.P.res R.qDelta * R.qInv) 0
  | _ => 0

/-- The translation parameter `x` of the representative. -/
def xOf : R.Index → O
  | (.inl x₁, .inl x₂) => R.crt x₁ x₂
  | (.inr (.inr (x₁, _)), .inr (.inr (x₂, _))) => R.crt x₁ x₂
  | (.inl x₁, .inr (.inr (x₂, _))) => R.crt x₁ x₂
  | (.inr (.inr (x₁, _)), .inl x₂) => R.crt x₁ x₂
  | (.inr (.inl x₁), .inr (.inl x₂)) =>
      R.crt (x₁ + R.P.res R.mDelta - R.P.res R.P.wDelta) (x₂ + R.Q.res R.mDelta - R.Q.res R.Q.wDelta)
  | (.inl x₁, .inr (.inl x₂)) => R.crt (x₁ - R.qInv) (x₂ + R.Q.res R.qDelta - R.Q.res R.Q.wDelta)
  | (.inr (.inr (x₁, _)), .inr (.inl x₂)) => R.crt (x₁ - R.qInv) (x₂ + R.Q.res R.qDelta - R.Q.res R.Q.wDelta)
  | (.inr (.inl x₁), .inl x₂) => R.crt (x₁ + R.P.res R.pDelta - R.P.res R.P.wDelta) (x₂ - R.pInv)
  | (.inr (.inl x₁), .inr (.inr (x₂, _))) => R.crt (x₁ + R.P.res R.pDelta - R.P.res R.P.wDelta) (x₂ - R.pInv)

/-- The representative `δ_{ij} = L(y)·G·T_x`. -/
def rep (ij : R.Index) : levelThree := lowerThree (R.yOf ij) * R.gOf ij * transThree (R.xOf ij)

theorem rep_entries (ij : R.Index) :
    ((R.rep ij : levelThree) : SL(2, O)) 0 0 = ((R.gOf ij : levelThree) : SL(2, O)) 0 0 ∧
    ((R.rep ij : levelThree) : SL(2, O)) 0 1 =
      3 * R.xOf ij * ((R.gOf ij : levelThree) : SL(2, O)) 0 0 + ((R.gOf ij : levelThree) : SL(2, O)) 0 1 ∧
    ((R.rep ij : levelThree) : SL(2, O)) 1 0 =
      3 * R.yOf ij * ((R.gOf ij : levelThree) : SL(2, O)) 0 0 + ((R.gOf ij : levelThree) : SL(2, O)) 1 0 ∧
    ((R.rep ij : levelThree) : SL(2, O)) 1 1 =
      3 * R.xOf ij * (3 * R.yOf ij * ((R.gOf ij : levelThree) : SL(2, O)) 0 0 +
        ((R.gOf ij : levelThree) : SL(2, O)) 1 0) +
      (3 * R.yOf ij * ((R.gOf ij : levelThree) : SL(2, O)) 0 1 + ((R.gOf ij : levelThree) : SL(2, O)) 1 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp [rep, lowerThree, transThree, Matrix.mul_apply, Fin.sum_univ_two]
    try ring

/-! ### The rows of the representatives -/

theorem P_nine_mK : 9 * R.P.res R.mK = -1 := by
  have h := congrArg R.P.res R.m_det
  simp only [map_sub, map_mul, map_one, R.P.res_nine, R.P.res_p, zero_mul, zero_sub] at h
  linear_combination -h

theorem Q_nine_mK : 9 * R.Q.res R.mK = -1 := by
  have h := congrArg R.Q.res R.m_det
  simp only [map_sub, map_mul, map_one, R.Q.res_nine, R.Q.res_p, mul_zero, zero_mul, zero_sub] at h
  linear_combination -h

theorem P_nine_pK : 9 * R.P.res (R.Q.p * R.pK) = -1 := by
  have h := congrArg R.P.res R.p_det
  simp only [map_sub, map_mul, map_one, R.P.res_nine, R.P.res_p, zero_mul, zero_sub] at h
  linear_combination -h

theorem Q_nine_qK : 9 * R.Q.res (R.P.p * R.qK) = -1 := by
  have h := congrArg R.Q.res R.q_det
  simp only [map_sub, map_mul, map_one, R.Q.res_nine, R.Q.res_p, zero_mul, zero_sub] at h
  linear_combination -h

theorem P_nine_wK : 9 * R.P.res R.P.wK = -1 := by
  have h := congrArg R.P.res R.P.w_det
  simp only [map_sub, map_mul, map_one, R.P.res_nine, R.P.res_p, zero_mul, zero_sub] at h
  linear_combination -h

theorem Q_nine_wK : 9 * R.Q.res R.Q.wK = -1 := by
  have h := congrArg R.Q.res R.Q.w_det
  simp only [map_sub, map_mul, map_one, R.Q.res_nine, R.Q.res_p, zero_mul, zero_sub] at h
  linear_combination -h

theorem eq_of_nine_eq {F : Type*} [Field F] {a b : F} (h9 : (9 : F) ≠ 0) (ha : 9 * a = -1) (hb : 9 * b = -1) :
    a = b := by
  have h : (9 : F) * (a - b) = 0 := by linear_combination ha - hb
  exact sub_eq_zero.mp ((mul_eq_zero.mp h).resolve_left h9)

theorem P_q_mul_qInv : R.P.res R.Q.p * R.qInv = 1 := mul_inv_cancel₀ R.P_res_q_ne_zero

theorem Q_p_mul_pInv : R.Q.res R.P.p * R.pInv = 1 := mul_inv_cancel₀ R.Q_res_p_ne_zero

/-- The rows of `δ_{ij}` are proportional modulo `p` to those of the representative of `i`. -/
theorem rep_mul_inv_P (ij : R.Index) : R.rep ij * (R.P.rep ij.1)⁻¹ ∈ R.P.heckeGroup := by
  rw [R.P.mul_inv_mem_heckeGroup_iff]
  obtain ⟨e0, e1, e2, e3⟩ := R.rep_entries ij
  have hN := R.P.res_rep ij.1
  simp only [Prod.ext_iff] at hN
  obtain ⟨n0, n1, n2, n3⟩ := hN
  rw [e0, e1, e2, e3, n0, n1, n2, n3]
  have hKm := R.P_nine_mK
  have hKp := R.P_nine_pK
  have hk := R.P_nine_wK
  have h9 := R.P.nine_ne_zero'
  have hq := R.P_q_mul_qInv
  have hm0 : R.P.res (R.P.p * R.Q.p) = 0 := by rw [map_mul, R.P.res_p, zero_mul]
  have hq0 : R.P.res (R.P.p * R.qK) = 0 := by rw [map_mul, R.P.res_p, zero_mul]
  have e1' := eq_of_nine_eq h9 hKm hk
  have e2' := eq_of_nine_eq h9 hKp hk
  rcases ij with ⟨x₁ | x₁ | ⟨x₁, y₁⟩, x₂ | x₂ | ⟨x₂, y₂⟩⟩
  · simp [gOf, xOf, yOf, PrimaryPrime.repRes]
  · simp [gOf, xOf, yOf, PrimaryPrime.repRes, wQ, hq0]
    linear_combination 3 * hq
  · simp [gOf, xOf, yOf, PrimaryPrime.repRes]
  · simp [gOf, xOf, yOf, PrimaryPrime.repRes, wP, R.P.res_p]
    linear_combination 3 * R.P.res R.P.wK * (R.P.res R.P.wDelta - R.P.res R.pDelta) * hKp +
      3 * R.P.res R.P.wDelta * e2'
  · simp [gOf, xOf, yOf, PrimaryPrime.repRes, wM, hm0]
    linear_combination 3 * R.P.res R.P.wK * (R.P.res R.P.wDelta - R.P.res R.mDelta) * hKm +
      3 * R.P.res R.P.wDelta * e1'
  · simp [gOf, xOf, yOf, PrimaryPrime.repRes, wP, R.P.res_p]
    linear_combination 3 * R.P.res R.P.wK * (R.P.res R.P.wDelta - R.P.res R.pDelta) * hKp +
      3 * R.P.res R.P.wDelta * e2'
  · simp [gOf, xOf, yOf, PrimaryPrime.repRes]
    ring
  · simp [gOf, xOf, yOf, PrimaryPrime.repRes, wQ, hq0]
    constructor
    · linear_combination 3 * hq
    · linear_combination (3 * y₁.1 * R.P.res R.qDelta + 27 * y₁.1 ^ 2 * R.P.res R.qDelta * R.qInv) * hq
  · simp [gOf, xOf, yOf, PrimaryPrime.repRes]
    ring

/-- The rows of `δ_{ij}` are proportional modulo `q` to those of the representative of `j`. -/
theorem rep_mul_inv_Q (ij : R.Index) : R.rep ij * (R.Q.rep ij.2)⁻¹ ∈ R.Q.heckeGroup := by
  rw [R.Q.mul_inv_mem_heckeGroup_iff]
  obtain ⟨e0, e1, e2, e3⟩ := R.rep_entries ij
  have hN := R.Q.res_rep ij.2
  simp only [Prod.ext_iff] at hN
  obtain ⟨n0, n1, n2, n3⟩ := hN
  rw [e0, e1, e2, e3, n0, n1, n2, n3]
  have hKm := R.Q_nine_mK
  have hKq := R.Q_nine_qK
  have hk := R.Q_nine_wK
  have h9 := R.Q.nine_ne_zero'
  have hp := R.Q_p_mul_pInv
  have hm0 : R.Q.res (R.P.p * R.Q.p) = 0 := by rw [map_mul, R.Q.res_p, mul_zero]
  have hp0 : R.Q.res (R.Q.p * R.pK) = 0 := by rw [map_mul, R.Q.res_p, zero_mul]
  have e1' := eq_of_nine_eq h9 hKm hk
  have e2' := eq_of_nine_eq h9 hKq hk
  rcases ij with ⟨x₁ | x₁ | ⟨x₁, y₁⟩, x₂ | x₂ | ⟨x₂, y₂⟩⟩
  · simp [gOf, xOf, yOf, PrimaryPrime.repRes]
  · simp [gOf, xOf, yOf, PrimaryPrime.repRes, wQ, R.Q.res_p]
    linear_combination 3 * R.Q.res R.Q.wK * (R.Q.res R.Q.wDelta - R.Q.res R.qDelta) * hKq +
      3 * R.Q.res R.Q.wDelta * e2'
  · simp [gOf, xOf, yOf, PrimaryPrime.repRes]
    ring
  · simp [gOf, xOf, yOf, PrimaryPrime.repRes, wP, hp0]
    linear_combination 3 * hp
  · simp [gOf, xOf, yOf, PrimaryPrime.repRes, wM, hm0]
    linear_combination 3 * R.Q.res R.Q.wK * (R.Q.res R.Q.wDelta - R.Q.res R.mDelta) * hKm +
      3 * R.Q.res R.Q.wDelta * e1'
  · simp [gOf, xOf, yOf, PrimaryPrime.repRes, wP, hp0]
    constructor
    · linear_combination 3 * hp
    · linear_combination (3 * y₂.1 * R.Q.res R.pDelta + 27 * y₂.1 ^ 2 * R.Q.res R.pDelta * R.pInv) * hp
  · simp [gOf, xOf, yOf, PrimaryPrime.repRes]
  · simp [gOf, xOf, yOf, PrimaryPrime.repRes, wQ, R.Q.res_p]
    linear_combination 3 * R.Q.res R.Q.wK * (R.Q.res R.Q.wDelta - R.Q.res R.qDelta) * hKq +
      3 * R.Q.res R.Q.wDelta * e2'
  · simp [gOf, xOf, yOf, PrimaryPrime.repRes]
    ring

/-! ### The cosets -/

/-- The coset `δ_{ij}⁻¹Γ_m`. -/
def cosetOf (ij : R.Index) : levelThree ⧸ R.heckeGroup := ((R.rep ij)⁻¹ : levelThree)

theorem cosetOf_bijective : Function.Bijective R.cosetOf := by
  constructor
  · rintro ⟨i, j⟩ ⟨i', j'⟩ h
    have h' := QuotientGroup.eq.mp h
    rw [inv_inv] at h'
    have hP : R.P.rep i * (R.P.rep i')⁻¹ ∈ R.P.heckeGroup := by
      have e := R.P.heckeGroup.mul_mem (R.P.heckeGroup.mul_mem
        (R.P.heckeGroup.inv_mem (R.rep_mul_inv_P (i, j))) h'.1) (R.rep_mul_inv_P (i', j'))
      simpa [mul_assoc] using e
    have hQ : R.Q.rep j * (R.Q.rep j')⁻¹ ∈ R.Q.heckeGroup := by
      have e := R.Q.heckeGroup.mul_mem (R.Q.heckeGroup.mul_mem
        (R.Q.heckeGroup.inv_mem (R.rep_mul_inv_Q (i, j))) h'.2) (R.rep_mul_inv_Q (i', j'))
      simpa [mul_assoc] using e
    have hi : i = i' := R.P.cosetOf_bijective.1 (QuotientGroup.eq.mpr (by rw [inv_inv]; exact hP))
    have hj : j = j' := R.Q.cosetOf_bijective.1 (QuotientGroup.eq.mpr (by rw [inv_inv]; exact hQ))
    rw [hi, hj]
  · intro c
    set γ : levelThree := c.out
    obtain ⟨i, hi⟩ := R.P.cosetOf_bijective.2 (γ : levelThree ⧸ R.P.heckeGroup)
    obtain ⟨j, hj⟩ := R.Q.cosetOf_bijective.2 (γ : levelThree ⧸ R.Q.heckeGroup)
    have hi' := QuotientGroup.eq.mp hi
    have hj' := QuotientGroup.eq.mp hj
    rw [inv_inv] at hi' hj'
    refine ⟨(i, j), ?_⟩
    rw [← QuotientGroup.out_eq' c, cosetOf, QuotientGroup.eq, inv_inv]
    refine ⟨?_, ?_⟩
    · have e := R.P.heckeGroup.mul_mem (R.rep_mul_inv_P (i, j)) hi'
      simpa [mul_assoc] using e
    · have e := R.Q.heckeGroup.mul_mem (R.rep_mul_inv_Q (i, j)) hj'
      simpa [mul_assoc] using e

/-- **The Hecke trace at `m` over the representatives.** -/
theorem heckeTrace_eq_sum (Θ : HyperbolicSpace → ℂ)
    (hΘ : ∀ (M : levelThree) (w : HyperbolicSpace), Θ (complexMatrix M • w) = complexCharacter M * Θ w)
    (w : HyperbolicSpace) :
    R.heckeTrace Θ w = ∑ ij : R.Index,
      (complexCharacter (R.rep ij) ^ 2)⁻¹ * R.heckeCorrelation Θ (complexMatrix (R.rep ij) • w) := by
  have hF : ∀ δ ∈ R.heckeGroup, ∀ x, R.heckeCorrelation Θ (complexMatrix δ • x) =
      kubotaSquare δ * R.heckeCorrelation Θ x := fun δ hδ x => by
    rw [kubotaSquare_apply]
    exact R.heckeCorrelation_automorphy Θ hΘ δ hδ x
  unfold heckeTrace cosetTrace
  rw [← R.cosetOf_bijective.sum_comp]
  refine Finset.sum_congr rfl fun ij _ => ?_
  rw [cosetTerm_congr hF w (γ := (R.cosetOf ij).out) (γ' := (R.rep ij)⁻¹) (QuotientGroup.out_eq' _)]
  unfold cosetTerm
  rw [inv_inv, kubotaSquare_apply, map_inv, inv_pow]

end PrimaryPair

end GaloisForLFunctions.OrderSixMetaplecticTheory
