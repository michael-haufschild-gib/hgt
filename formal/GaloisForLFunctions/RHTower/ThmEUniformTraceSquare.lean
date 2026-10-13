import GaloisForLFunctions.RHTower.ThmEUniformTrace
import GaloisForLFunctions.RHTower.ThmEUniformCross
import GaloisForLFunctions.RHTower.ThmEUniformEnds
import GaloisForLFunctions.RHTower.ThmEUniformCoprimeSums
import Zeta23.ThmE.TracesHypChi
import Zeta23.PrimeSideA.Bridge
import Zeta23.MV.Final

/-!
# The Frobenius side of the prime-side Gram matrix, uniformly in the modulus

For a unimodular coefficient sequence of modulus `q` and parity `κ`, the squared Frobenius norm of the
prime-side Gram matrix `G̃` satisfies, for all `T ≥ T₀` with `T₀` and `C` independent of `q`,

`tr G̃² − (TL/2π)(ℓ_{1,q}² + L²/3)
   ≤ C [ (1 + log q)² (L l log l (l² + X) + l² log L + l √X) + L² X
          + (1 + log²(log q + 8)) T L² + T L ℓ_{1,q}²/l² ]`                    (`tr2_upper_uniform`).

The proof is Alpöge–Furman's decomposition `tr G̃² = 𝓜[ν, ν] + (end effects)`,
`𝓜[ν, ν] = 𝓜[μ, μ] + 𝓜[P, P] + 2𝓜[μ, P]`, with every piece taken in its modulus-uniform form:
`prop_ends_uniform`, `prop_mumu_uniform`, `prop_cross_uniform`, Alpöge–Furman's `prop_PP_chi_uniform`, the
coprime sandwich `sumA2gCoprime_upper_uniform`, and the uniform Γ-facts for `∫ μ_q²`.  Every error is
`o(T L ℓ_{1,q}²)` as soon as `q ≤ T^A`, for any fixed `A`.
-/

open MeasureTheory Real Set Zeta23 Zeta23.ThmE Zeta23.PrimeSide
open scoped ArithmeticFunction

noncomputable section

namespace RHTower

/-- **The splitting of `𝓜[ν, ν]`**, for every setting. -/
theorem eq_Msplit_uniform {cϱ : ℝ} {κ q : ℕ} (hκ : κ ≤ 1) (hq : 1 ≤ q) (c : ℕ → ℂ) {p : Setting}
    {F : LocalFun} (hF : LocalHypsCore cϱ p F) :
    MtotalChiA κ q c p F
      = Mform F.Phi p.T (muq κ q) (muq κ q) + Mform F.Phi p.T (PXc c p.X) (PXc c p.X)
          + 2 * Mform F.Phi p.T (muq κ q) (PXc c p.X) := by
  have hμc : Continuous (muq κ q) := (GammaChi.gammaFactsChi hκ hq).smooth.continuous
  have hPc : Continuous (PXc c p.X) := PXc_continuous c p.X_pos
  have hΦ : Continuous F.Phi := hF.Phi_contDiff.continuous
  have hsum : Continuous (muq κ q + PXc c p.X) := hμc.add hPc
  have he : MtotalChiA κ q c p F
      = Mform F.Phi p.T (muq κ q + PXc c p.X) (muq κ q + PXc c p.X) := rfl
  rw [he, Mform_add_left hΦ hμc hPc hsum, Mform_add_right hΦ hμc hPc hμc,
    Mform_add_right hΦ hμc hPc hPc, Mform_comm hF.Phi_even (PXc c p.X) (muq κ q)]
  ring

/-- The right-hand side of the uniform `tr G̃²` bound. -/
def tr2ErrUniform (P : Params) (q : ℕ) (T : ℝ) : ℝ :=
  (1 + Real.log q) ^ 2 * (P.L T * l T * Real.log (l T) * (l T ^ 2 + P.X T)
      + l T ^ 2 * Real.log (P.L T) + l T * Real.sqrt (P.X T))
    + P.L T ^ 2 * P.X T + (1 + Real.log (Real.log q + 8) ^ 2) * T * P.L T ^ 2
    + T * P.L T * ell1q q T ^ 2 / l T ^ 2

/-- The bookkeeping of the `tr G̃²` bound, as an inequality between real numbers. -/
theorem tr2_combine {t M Mmm MPP MmP A₀ P₀ S E₁ E₂ E₃ E₄ E₅ E₆ Ce Cm Cx Cp Cb Cg : ℝ}
    (hS : 0 ≤ S) (h₁ : 0 ≤ E₁) (h₂ : 0 ≤ E₂) (h₃ : 0 ≤ E₃) (h₄ : 0 ≤ E₄) (h₅ : 0 ≤ E₅)
    (h₆ : 0 ≤ E₆) (hCe : 0 ≤ Ce) (hCm : 0 ≤ Cm) (hCx : 0 ≤ Cx) (hCp : 0 ≤ Cp) (hCb : 0 ≤ Cb)
    (hCg : 0 ≤ Cg)
    (ht : t ≤ M + Ce * (S * E₁)) (hM : M = Mmm + MPP + 2 * MmP)
    (hmm : Mmm ≤ A₀ + Cg * E₆ + Cm * (S * E₂)) (hpp : MPP ≤ P₀ + Cb * E₅ + Cp * E₄)
    (hmp : 2 * MmP ≤ 2 * Cx * (S * E₃)) :
    t - (A₀ + P₀) ≤ (Ce + Cm + 2 * Cx + Cp + Cb + Cg) * (S * (E₁ + E₂ + E₃) + E₄ + E₅ + E₆) := by
  have k₁ : 0 ≤ S * E₁ := mul_nonneg hS h₁
  have k₂ : 0 ≤ S * E₂ := mul_nonneg hS h₂
  have k₃ : 0 ≤ S * E₃ := mul_nonneg hS h₃
  have e : (Ce + Cm + 2 * Cx + Cp + Cb + Cg) * (S * (E₁ + E₂ + E₃) + E₄ + E₅ + E₆)
      = Ce * (S * E₁) + Cm * (S * E₂) + 2 * Cx * (S * E₃) + Cp * E₄ + Cb * E₅ + Cg * E₆
        + (Ce * (S * E₂ + S * E₃ + E₄ + E₅ + E₆) + Cm * (S * E₁ + S * E₃ + E₄ + E₅ + E₆)
          + 2 * Cx * (S * E₁ + S * E₂ + E₄ + E₅ + E₆) + Cp * (S * (E₁ + E₂ + E₃) + E₅ + E₆)
          + Cb * (S * (E₁ + E₂ + E₃) + E₄ + E₆) + Cg * (S * (E₁ + E₂ + E₃) + E₄ + E₅)) := by ring
  have hrest : 0 ≤ Ce * (S * E₂ + S * E₃ + E₄ + E₅ + E₆) + Cm * (S * E₁ + S * E₃ + E₄ + E₅ + E₆)
          + 2 * Cx * (S * E₁ + S * E₂ + E₄ + E₅ + E₆) + Cp * (S * (E₁ + E₂ + E₃) + E₅ + E₆)
          + Cb * (S * (E₁ + E₂ + E₃) + E₄ + E₆) + Cg * (S * (E₁ + E₂ + E₃) + E₄ + E₅) := by
    positivity
  rw [e]
  linarith

/-- The archimedean diagonal against its main term, as an inequality between real numbers. -/
theorem mumu_main_le {Mf b L I M₀ Cg l2 Cm SE T ell : ℝ} (hb1 : b ≤ 1) (hL : 0 ≤ L) (hI : 0 ≤ I)
    (hM₀ : M₀ = T * ell / (4 * π ^ 2)) (hl2 : 0 < l2) (hint : I ≤ M₀ + Cg * M₀ / l2)
    (hM₀0 : 0 ≤ M₀) (hmm : Mf - 2 * π * b * L * I ≤ Cm * SE) :
    Mf ≤ T * L / (2 * π) * ell + |Cg| / (2 * π) * (T * L * ell / l2) + Cm * SE := by
  have h1 : Cg * M₀ / l2 ≤ |Cg| * M₀ / l2 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hM₀0) hl2.le
  have hpos : 0 ≤ 2 * π * L := by positivity
  have h2 : 2 * π * b * L * I ≤ 2 * π * L * (M₀ + |Cg| * M₀ / l2) := by
    calc 2 * π * b * L * I = b * (2 * π * L * I) := by ring
      _ ≤ 1 * (2 * π * L * I) := mul_le_mul_of_nonneg_right hb1 (mul_nonneg hpos hI)
      _ ≤ 2 * π * L * (M₀ + |Cg| * M₀ / l2) := by
          rw [one_mul]; exact mul_le_mul_of_nonneg_left (by linarith) hpos
  have hid : 2 * π * L * (M₀ + |Cg| * M₀ / l2)
      = T * L / (2 * π) * ell + |Cg| / (2 * π) * (T * L * ell / l2) := by
    rw [hM₀]; field_simp; ring
  linarith

/-- **`tr G̃²` from above, uniformly in the modulus, at an abstract setting.** -/
theorem tr2_upper_uniform_at (cϱ : ℝ) {lam : ℝ} (hlam : 0 < lam ∧ lam ≤ 1) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ κ q : ℕ, κ ≤ 1 → 1 ≤ q → ∀ c : ℕ → ℂ, CoeffUnimodular q c →
      ∀ (p : Setting) (F : LocalFun), p.lam = lam → T₀ ≤ p.T → LocalHyps cϱ p F →
        trGt2ChiA κ q c p F
            - p.T * p.L / (2 * π) * (ell1q q p.T ^ 2 + p.L ^ 2 / 3)
          ≤ C * ((1 + Real.log q) ^ 2 * (p.L * l p.T * Real.log (l p.T) * (l p.T ^ 2 + p.X)
                + l p.T ^ 2 * Real.log p.L + l p.T * Real.sqrt p.X)
              + p.L ^ 2 * p.X + (1 + Real.log (Real.log q + 8) ^ 2) * p.T * p.L ^ 2
              + p.T * p.L * ell1q q p.T ^ 2 / l p.T ^ 2) := by
  obtain ⟨Ce, Te, hCe, he⟩ := prop_ends_uniform cϱ hlam
  obtain ⟨Cm, Tm, hCm, hm⟩ := prop_mumu_uniform cϱ lam hlam
  obtain ⟨Cx, Tx, hCx, hx⟩ := prop_cross_uniform cϱ hlam
  obtain ⟨Cp, Tp, hp⟩ := prop_PP_chi_uniform (cϱ := cϱ) (lam := lam) Cheb.chebyshevMertens
    (Zeta23.exists_MVHilbert_of_diag ⟨13, by norm_num, MV.mvDiag_thirteen⟩) hlam
  obtain ⟨Bu, Ku, hBu, hKu, hu⟩ := sumA2gCoprime_upper_uniform (cϱ := cϱ)
  obtain ⟨CΓ, hΓ⟩ := GammaChi.gammaFactsChi_uniform
  refine ⟨Ce + Cm + 2 * Cx + |Cp| + (Bu + Ku + 1) / π + |CΓ| / (2 * π),
    max (max (max Te Tm) (max Tx Tp)) (max CΓ 1), by positivity,
    fun κ q hκ hq c hc p F hpl hT hF => ?_⟩
  have hT₁ : max (max Te Tm) (max Tx Tp) ≤ p.T := (le_max_left _ _).trans hT
  have hTe : Te ≤ p.T := ((le_max_left _ _).trans (le_max_left _ _)).trans hT₁
  have hTm : Tm ≤ p.T := ((le_max_right _ _).trans (le_max_left _ _)).trans hT₁
  have hTx : Tx ≤ p.T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT₁
  have hTp : Tp ≤ p.T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT₁
  have hTΓ : CΓ ≤ p.T := ((le_max_left _ _).trans (le_max_right _ _)).trans hT
  have hT1 : 1 ≤ p.T := ((le_max_right _ _).trans (le_max_right _ _)).trans hT
  have hFc := hF.toCore
  have hcok := hc.toCoeffOK
  have h_ends := (abs_le.mp (he κ q hκ hq c hcok p F hpl hTe hFc)).2
  have h_mumu := (abs_le.mp (hm κ q hκ hq p F hpl hTm hFc)).2
  have h_cross := (abs_le.mp (hx κ q hκ hq c hcok p F hpl hTx hFc)).2
  have h_pp := (abs_le.mp (hp q c hc p F hpl hTp hFc)).2
  have h_sum := hu q hq p F hFc
  have h_split := eq_Msplit_uniform hκ hq c hFc
  have h_int := (abs_le.mp ((hΓ κ q hκ hq).int_mu_sq p.T hTΓ)).2
  clear he hm hx hp hu hΓ
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hl1 : 1 ≤ l p.T := hF.one_le_l
  have hL : 0 < p.L := hF.L_pos
  have hX : 0 < p.X := p.X_pos
  -- atoms
  obtain ⟨S, hSdef⟩ : ∃ x : ℝ, x = (1 + Real.log q) ^ 2 := ⟨_, rfl⟩
  obtain ⟨E₁, hE₁def⟩ : ∃ x : ℝ, x = p.L * l p.T * Real.log (l p.T) * (l p.T ^ 2 + p.X) := ⟨_, rfl⟩
  obtain ⟨E₂, hE₂def⟩ : ∃ x : ℝ, x = l p.T ^ 2 * Real.log p.L := ⟨_, rfl⟩
  obtain ⟨E₃, hE₃def⟩ : ∃ x : ℝ, x = l p.T * Real.sqrt p.X := ⟨_, rfl⟩
  obtain ⟨E₄, hE₄def⟩ : ∃ x : ℝ, x = p.L ^ 2 * p.X := ⟨_, rfl⟩
  obtain ⟨E₅, hE₅def⟩ : ∃ x : ℝ, x = (1 + Real.log (Real.log q + 8) ^ 2) * p.T * p.L ^ 2 :=
    ⟨_, rfl⟩
  obtain ⟨E₆, hE₆def⟩ : ∃ x : ℝ, x = p.T * p.L * ell1q q p.T ^ 2 / l p.T ^ 2 := ⟨_, rfl⟩
  have hS0 : 0 ≤ S := by rw [hSdef]; positivity
  have hE₁ : 0 ≤ E₁ := by rw [hE₁def]; have := Real.log_nonneg hl1; positivity
  have hE₂ : 0 ≤ E₂ := by
    rw [hE₂def]; exact mul_nonneg (sq_nonneg _) (Real.log_nonneg (by linarith [hF.eight_le_L]))
  have hE₃ : 0 ≤ E₃ := by rw [hE₃def]; positivity
  have hE₄ : 0 ≤ E₄ := by rw [hE₄def]; positivity
  have hE₅ : 0 ≤ E₅ := by rw [hE₅def]; positivity
  have hE₆ : 0 ≤ E₆ := by rw [hE₆def]; positivity
  have herr : (1 + Real.log q) ^ 2 * (p.L * l p.T * Real.log (l p.T) * (l p.T ^ 2 + p.X)
                + l p.T ^ 2 * Real.log p.L + l p.T * Real.sqrt p.X)
              + p.L ^ 2 * p.X + (1 + Real.log (Real.log q + 8) ^ 2) * p.T * p.L ^ 2
              + p.T * p.L * ell1q q p.T ^ 2 / l p.T ^ 2
      = S * (E₁ + E₂ + E₃) + E₄ + E₅ + E₆ := by
    rw [hSdef, hE₁def, hE₂def, hE₃def, hE₄def, hE₅def, hE₆def]
  rw [herr]
  -- the archimedean diagonal
  have hmm : Mform F.Phi p.T (muq κ q) (muq κ q)
      ≤ p.T * p.L / (2 * π) * ell1q q p.T ^ 2 + |CΓ| / (2 * π) * E₆ + Cm * (S * E₂) := by
    have hint0 : 0 ≤ ∫ τ in p.T..(2 * p.T), muq κ q τ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) fun τ _ => sq_nonneg _
    have hmm' : Mform F.Phi p.T (muq κ q) (muq κ q)
        - 2 * π * F.b * p.L * ∫ τ in p.T..(2 * p.T), muq κ q τ ^ 2 ≤ Cm * (S * E₂) := by
      rw [hSdef, hE₂def, ← mul_assoc]; exact h_mumu
    have hl2 : 0 < l p.T ^ 2 := by positivity
    have hint : ∫ τ in p.T..(2 * p.T), muq κ q τ ^ 2
        ≤ p.T * ell1q q p.T ^ 2 / (4 * π ^ 2)
          + CΓ * (p.T * ell1q q p.T ^ 2 / (4 * π ^ 2)) / l p.T ^ 2 := by
      linarith only [h_int]
    have := mumu_main_le (Mf := Mform F.Phi p.T (muq κ q) (muq κ q)) (b := F.b) (L := p.L)
      (Cm := Cm) (SE := S * E₂) (hF.b_le_a.trans hF.a_le_one) hL.le hint0 rfl hl2 hint
      (by positivity) hmm'
    rw [hE₆def]
    convert this using 2
  -- the prime diagonal
  have hpp : Mform F.Phi p.T (PXc c p.X) (PXc c p.X)
      ≤ p.T / π * (p.L ^ 3 / 6) + (Bu + Ku + 1) / π * E₅ + |Cp| * E₄ := by
    have h1 : p.T / π * sumA2gCoprime q p.X F.g
        ≤ p.T / π * (p.L ^ 3 / 6 + (Bu + Ku * Real.log (Real.log q + 8) ^ 2) * p.L ^ 2) :=
      mul_le_mul_of_nonneg_left h_sum (by positivity)
    have h2 : Cp * (p.L ^ 2 * p.X) ≤ |Cp| * E₄ := by
      rw [hE₄def]; exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    have hl2 : 0 ≤ Real.log (Real.log q + 8) ^ 2 := sq_nonneg _
    have hk : Bu + Ku * Real.log (Real.log q + 8) ^ 2
        ≤ (Bu + Ku + 1) * (1 + Real.log (Real.log q + 8) ^ 2) := by
      nlinarith only [mul_nonneg hBu hl2, hl2, hKu]
    have hTL2 : 0 ≤ p.T / π * p.L ^ 2 := by positivity
    have h3 : p.T / π * ((Bu + Ku * Real.log (Real.log q + 8) ^ 2) * p.L ^ 2)
        ≤ (Bu + Ku + 1) / π * E₅ := by
      rw [hE₅def]
      calc p.T / π * ((Bu + Ku * Real.log (Real.log q + 8) ^ 2) * p.L ^ 2)
          = (Bu + Ku * Real.log (Real.log q + 8) ^ 2) * (p.T / π * p.L ^ 2) := by ring
        _ ≤ (Bu + Ku + 1) * (1 + Real.log (Real.log q + 8) ^ 2) * (p.T / π * p.L ^ 2) :=
            mul_le_mul_of_nonneg_right hk hTL2
        _ = (Bu + Ku + 1) / π * ((1 + Real.log (Real.log q + 8) ^ 2) * p.T * p.L ^ 2) := by ring
    have e : p.T / π * (p.L ^ 3 / 6 + (Bu + Ku * Real.log (Real.log q + 8) ^ 2) * p.L ^ 2)
        = p.T / π * (p.L ^ 3 / 6) + p.T / π * ((Bu + Ku * Real.log (Real.log q + 8) ^ 2) * p.L ^ 2) := by
      ring
    linarith only [h_pp, h1, h2, h3, e]
  -- the cross term
  have hmp : 2 * Mform F.Phi p.T (muq κ q) (PXc c p.X) ≤ 2 * Cx * (S * E₃) := by
    have hsq : 1 + Real.log q ≤ S := by rw [hSdef]; nlinarith only [hlq]
    have h1 : Cx * (1 + Real.log q) * (l p.T * Real.sqrt p.X) ≤ Cx * (S * E₃) := by
      have hlX : 0 ≤ l p.T * Real.sqrt p.X := by positivity
      calc Cx * (1 + Real.log q) * (l p.T * Real.sqrt p.X)
          ≤ Cx * S * (l p.T * Real.sqrt p.X) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsq hCx) hlX
        _ = Cx * (S * E₃) := by rw [hE₃def]; ring
    linarith only [h_cross, h1]
  have hends : trGt2ChiA κ q c p F ≤ MtotalChiA κ q c p F + Ce * (S * E₁) := by
    have : Ce * (1 + Real.log q) ^ 2 * (p.L * p.l * Real.log p.l * (p.l ^ 2 + p.X))
        = Ce * (S * E₁) := by rw [hSdef, hE₁def]; ring
    linarith only [h_ends, this]
  have hmain : p.T * p.L / (2 * π) * (ell1q q p.T ^ 2 + p.L ^ 2 / 3)
      = p.T * p.L / (2 * π) * ell1q q p.T ^ 2 + p.T / π * (p.L ^ 3 / 6) := by
    field_simp; ring
  rw [hmain]
  exact tr2_combine hS0 hE₁ hE₂ hE₃ hE₄ hE₅ hE₆ hCe hCm hCx (abs_nonneg _) (by positivity)
    (by positivity) hends h_split hmm hpp hmp

/-- **`tr G̃²` from above, uniformly in the modulus** (concrete parameters). -/
theorem tr2_upper_uniform (P : Params) (hP : P.Valid) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ κ q : ℕ, κ ≤ 1 → 1 ≤ q → ∀ c : ℕ → ℂ, CoeffUnimodular q c →
      ∀ T : ℝ, T₀ ≤ T →
        trGtildeSqChi P κ q c T - mainTr2Chi P q T ≤ C * tr2ErrUniform P q T := by
  obtain ⟨C, T₀, hC, h⟩ := tr2_upper_uniform_at P.crho ⟨hP.lam_pos, hP.lam_le_one⟩
  obtain ⟨TL, hTLev⟩ := PrimeSide.localHypsEventually hP
  refine ⟨C, max T₀ TL, hC, fun κ q hκ hq c hc T hT => ?_⟩
  have := h κ q hκ hq c hc (P.toSetting T) (P.localFun T) rfl ((le_max_left _ _).trans hT)
    (hTLev T ((le_max_right _ _).trans hT))
  exact this

end RHTower
