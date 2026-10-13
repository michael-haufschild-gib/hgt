import GaloisForLFunctions.RHTower.FamilyPrimeDiagonal
import GaloisForLFunctions.RHTower.FamilyParityPerturbation
import GaloisForLFunctions.RHTower.FamilyMuMuWide
import GaloisForLFunctions.RHTower.FamilyCrossWide
import GaloisForLFunctions.RHTower.ThmEUniformTraceSquare
import Zeta23.MV.Final

/-!
# The family Frobenius norm at any bandwidth

For the common density `μ = μ_{0,q}` and all characters `χ` modulo `q`, write
`tr G̃²(μ + P_χ) = 𝓜[μ, μ] + 𝓜[P_χ, P_χ] + 2𝓜[μ, P_χ] + E(μ + P_χ)` with `E` the end form.  Summing over `χ`:

* `φ(q) 𝓜[μ, μ] ≤ φ(q)((TL/2π)ℓ² + |C_Γ|/(2π)·TLℓ²/l² + C(1 + log q)² l² log L)` (uniform Γ-facts and
  `prop_mumu_uniform_wide`);
* `Σ_χ 𝓜[P_χ, P_χ] ≤ φ(q)(T/π)(L³/6 + (B + K log²(log q + 8))L²) + diagonal boundary + off-diagonal`
  (`family_PP_le`, `sumA2gCoprime_upper_uniform_wide`);
* `|Σ_χ 𝓜[μ, P_χ]| ≤ φ(q) C (1 + log q) l √X` (`prop_cross_uniform_wide`);
* `|Σ_χ E(μ + P_χ)|` by the character-averaged end-effect bound (`abs_sum_endForm_dirichlet_le`).

The result (`family_frob_le`) bounds `Σ_χ tr G̃²(μ_{0,q} + P_χ)` by `φ(q)·(TL/2π)(ℓ_{1,q}² + L²/3)` plus an explicit error,
at every bandwidth ratio `0 < λ ≤ 2`.
-/

open MeasureTheory Real Set Zeta23 Zeta23.ThmE Zeta23.PrimeSide
open scoped ArithmeticFunction

noncomputable section

namespace RHTower

variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

/-- Dirichlet characters give admissible coefficient sequences. -/
theorem coeffOK_dirichlet {q : ℕ} (χ : DirichletCharacter ℂ q) : CoeffOK q (fun n => χ n) := by
  refine ⟨fun n => DirichletCharacter.norm_le_one χ _, fun n hn => ?_⟩
  exact χ.map_nonunit (fun hu => hn ((ZMod.isUnit_iff_coprime n q).mp hu))

/-- The splitting of `𝓜[ν, ν]` at the `CoreW` layer. -/
theorem Msplit_wide {q : ℕ} (hq : 1 ≤ q) (c : ℕ → ℂ) (hF : LocalHypsCoreW cϱ p F) :
    MtotalNu (muq 0 q + PXc c p.X) p F
      = Mform F.Phi p.T (muq 0 q) (muq 0 q) + Mform F.Phi p.T (PXc c p.X) (PXc c p.X)
          + 2 * Mform F.Phi p.T (muq 0 q) (PXc c p.X) := by
  have hμc : Continuous (muq 0 q) := (GammaChi.gammaFactsChi (by norm_num) hq).smooth.continuous
  have hPc : Continuous (PXc c p.X) := PXc_continuous c p.X_pos
  have hΦ : Continuous F.Phi := hF.Phi_contDiff.continuous
  unfold MtotalNu
  rw [Mform_add_left hΦ hμc hPc (hμc.add hPc), Mform_add_right hΦ hμc hPc hμc,
    Mform_add_right hΦ hμc hPc hPc, Mform_comm hF.Phi_even (PXc c p.X) (muq 0 q)]
  ring

/-- The per-character decomposition of the Frobenius norm. -/
theorem trGt2Nu_eq_split {q : ℕ} (hq : 1 ≤ q) (c : ℕ → ℂ) (hF : LocalHypsCoreW cϱ p F) :
    trGt2Nu (muq 0 q + PXc c p.X) p F
      = Mform F.Phi p.T (muq 0 q) (muq 0 q) + Mform F.Phi p.T (PXc c p.X) (PXc c p.X)
          + 2 * Mform F.Phi p.T (muq 0 q) (PXc c p.X)
          + endForm p F (muq 0 q + PXc c p.X) (muq 0 q + PXc c p.X) := by
  rw [endForm_self, ← Msplit_wide hq c hF]
  unfold trGt2Nu
  ring

/-- **The family Frobenius norm with the common density.** -/
theorem family_frob_le (cϱ lam : ℝ) (hlam : 0 < lam) :
    ∃ Cm Cx B K Cmv Ce C₀ CΓ T₀ : ℝ, 0 ≤ Cm ∧ 0 ≤ Cx ∧ 0 ≤ B ∧ 0 ≤ K ∧ 0 ≤ Cmv ∧ 0 ≤ Ce ∧
      1 ≤ C₀ ∧ ∀ (q : ℕ) [NeZero q], 1 ≤ q → ∀ (p : Setting) (F : LocalFun), p.lam = lam →
        T₀ ≤ p.T → LocalHypsCoreW cϱ p F → p.L ≤ 2 * p.l →
        ∑ χ : DirichletCharacter ℂ q, trGt2Nu (muq 0 q + PXc (fun n => χ n) p.X) p F
          ≤ (q.totient : ℝ) * (p.T * p.L / (2 * π) * (ell1q q p.T ^ 2 + p.L ^ 2 / 3))
            + (q.totient : ℝ) * (Cm * (1 + Real.log q) ^ 2 * (Zeta23.l p.T ^ 2 * Real.log p.L)
              + |CΓ| / (2 * π) * (p.T * p.L * ell1q q p.T ^ 2 / Zeta23.l p.T ^ 2)
              + 2 * (Cx * (1 + Real.log q) * (Zeta23.l p.T * Real.sqrt p.X))
              + (B + K * Real.log (Real.log q + 8) ^ 2) / π * (p.T * p.L ^ 2))
            + (q.totient : ℝ) / (2 * π ^ 2)
                * ((∑ n ∈ primeRange p.X, acoef n ^ 2) * ∫ x, F.Phi x ^ 2 * |x|)
            + (q.totient : ℝ) / (2 * π ^ 2) * ((∫ x, F.Phi x ^ 2) / q
                * (8 * Cmv + 2 + 2 * Real.log ((⌊p.X⌋₊ : ℝ) + 1))
                * ∑ n ∈ primeRange p.X, acoef n ^ 2 * ((n : ℝ) + q))
            + Ce * (p.L * p.l * Real.log p.l) * q.totient *
                (((C₀ + Real.log q) * p.l) ^ 2 + ((C₀ + Real.log q) * p.l + oneClassMass q p.X) ^ 2
                  + 1 / (2 * Real.pi ^ 2) *
                    ∑ r ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
                      (2 * (p.l + classMass q p.X r) ^ 2
                        + (p.l + classMass q p.X r + classMass q p.X r⁻¹) ^ 2)) := by
  obtain ⟨Cm, Tm, hCm, hm⟩ := prop_mumu_uniform_wide cϱ lam
  obtain ⟨Cx, Tx, hCx, hx⟩ := prop_cross_uniform_wide cϱ hlam
  obtain ⟨B, K, hB, hK, hu⟩ := sumA2gCoprime_upper_uniform_wide (cϱ := cϱ)
  obtain ⟨Cmv, hCmv, hMV⟩ := Zeta23.exists_MVHilbert_of_diag ⟨13, by norm_num, MV.mvDiag_thirteen⟩
  obtain ⟨Ce, Te, he⟩ := abs_sum_endForm_dirichlet_le cϱ lam
  obtain ⟨C₀, Tμ, hC₀, hμB⟩ := muq_nuBound_uniform
  obtain ⟨CΓ, hΓ⟩ := GammaChi.gammaFactsChi_uniform
  refine ⟨Cm, Cx, B, K, Cmv, |Ce|, C₀, CΓ, max (max (max Tm Tx) (max Te Tμ)) (max CΓ 1),
    hCm, hCx, hB, hK, hCmv.le, abs_nonneg _, hC₀, fun q _ hq p F hp hT hF hL2 => ?_⟩
  have hT₁ := (le_max_left _ _).trans hT
  have hT₂ := (le_max_right _ _).trans hT
  have hTm : Tm ≤ p.T := (le_max_left _ _).trans ((le_max_left _ _).trans hT₁)
  have hTx : Tx ≤ p.T := (le_max_right _ _).trans ((le_max_left _ _).trans hT₁)
  have hTe : Te ≤ p.T := (le_max_left _ _).trans ((le_max_right _ _).trans hT₁)
  have hTμ : Tμ ≤ p.T := (le_max_right _ _).trans ((le_max_right _ _).trans hT₁)
  have hTΓ : CΓ ≤ p.T := (le_max_left _ _).trans hT₂
  have hT1 : 1 ≤ p.T := (le_max_right _ _).trans hT₂
  have hl1 : 1 ≤ p.l := hF.one_le_l
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hL : 0 < p.L := hF.L_pos
  -- per-character decomposition and sums
  have hsplit : ∑ χ : DirichletCharacter ℂ q, trGt2Nu (muq 0 q + PXc (fun n => χ n) p.X) p F
      = (q.totient : ℝ) * Mform F.Phi p.T (muq 0 q) (muq 0 q)
        + ∑ χ : DirichletCharacter ℂ q,
            Mform F.Phi p.T (PXc (fun n => χ n) p.X) (PXc (fun n => χ n) p.X)
        + 2 * ∑ χ : DirichletCharacter ℂ q, Mform F.Phi p.T (muq 0 q) (PXc (fun n => χ n) p.X)
        + ∑ χ : DirichletCharacter ℂ q, endForm p F (muq 0 q + PXc (fun n => χ n) p.X)
            (muq 0 q + PXc (fun n => χ n) p.X) := by
    rw [Finset.sum_congr rfl fun χ _ => trGt2Nu_eq_split hq (fun n => χ n) hF,
      Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const,
      card_dirichletCharacter, nsmul_eq_mul, Finset.mul_sum]
  rw [hsplit]
  -- the archimedean diagonal
  have hmumu : Mform F.Phi p.T (muq 0 q) (muq 0 q)
      ≤ p.T * p.L / (2 * π) * ell1q q p.T ^ 2
        + |CΓ| / (2 * π) * (p.T * p.L * ell1q q p.T ^ 2 / Zeta23.l p.T ^ 2)
        + Cm * (1 + Real.log q) ^ 2 * (Zeta23.l p.T ^ 2 * Real.log p.L) := by
    have h1 := (abs_le.mp (hm 0 q (by norm_num) hq p F hp hTm hF)).2
    have h2 := (abs_le.mp ((hΓ 0 q (by norm_num) hq).int_mu_sq p.T hTΓ)).2
    have hl0 : 0 < Zeta23.l p.T ^ 2 := by have := hl1; positivity
    have hint0 : 0 ≤ ∫ τ in p.T..(2 * p.T), muq 0 q τ ^ 2 :=
      intervalIntegral.integral_nonneg (by linarith) fun τ _ => sq_nonneg _
    have h3 := mumu_main_le (Mf := Mform F.Phi p.T (muq 0 q) (muq 0 q)) (b := F.b) (L := p.L)
      (I := ∫ τ in p.T..(2 * p.T), muq 0 q τ ^ 2) (M₀ := p.T * ell1q q p.T ^ 2 / (4 * π ^ 2))
      (Cg := CΓ) (l2 := Zeta23.l p.T ^ 2) (Cm := Cm * (1 + Real.log q) ^ 2)
      (SE := Zeta23.l p.T ^ 2 * Real.log p.L) (T := p.T) (ell := ell1q q p.T ^ 2)
      (hF.b_le_a.trans hF.a_le_one) hL.le hint0 rfl hl0 (by linarith) (by positivity) h1
    exact h3
  -- the prime diagonal
  have hPP := family_PP_le hMV hCmv.le (q := q) hF (by linarith)
  have hsum := hu q hq p F hF
  have hPP' : (q.totient : ℝ) * (p.T / π * sumA2gCoprime q p.X F.g)
      ≤ (q.totient : ℝ) * (p.T / π * (p.L ^ 3 / 6))
        + (q.totient : ℝ) * ((B + K * Real.log (Real.log q + 8) ^ 2) / π * (p.T * p.L ^ 2)) := by
    have h1 := mul_le_mul_of_nonneg_left hsum (by positivity : (0:ℝ) ≤ p.T / π)
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0:ℝ) ≤ q.totient)
    have e : (q.totient : ℝ) * (p.T / π * (p.L ^ 3 / 6 + (B + K * Real.log (Real.log q + 8) ^ 2)
        * p.L ^ 2)) = (q.totient : ℝ) * (p.T / π * (p.L ^ 3 / 6))
        + (q.totient : ℝ) * ((B + K * Real.log (Real.log q + 8) ^ 2) / π * (p.T * p.L ^ 2)) := by
      ring
    linarith
  -- the cross terms
  have hcross : 2 * ∑ χ : DirichletCharacter ℂ q, Mform F.Phi p.T (muq 0 q) (PXc (fun n => χ n) p.X)
      ≤ (q.totient : ℝ) * (2 * (Cx * (1 + Real.log q) * (Zeta23.l p.T * Real.sqrt p.X))) := by
    have h1 : ∑ χ : DirichletCharacter ℂ q, Mform F.Phi p.T (muq 0 q) (PXc (fun n => χ n) p.X)
        ≤ ∑ _χ : DirichletCharacter ℂ q, Cx * (1 + Real.log q) * (Zeta23.l p.T * Real.sqrt p.X) :=
      Finset.sum_le_sum fun χ _ =>
        (abs_le.mp (hx 0 q (by norm_num) hq (fun n => χ n) (coeffOK_dirichlet χ) p F hp hTx hF)).2
    rw [Finset.sum_const, card_dirichletCharacter, nsmul_eq_mul] at h1
    linarith
  -- the end effects
  have hends : ∑ χ : DirichletCharacter ℂ q, endForm p F (muq 0 q + PXc (fun n => χ n) p.X)
        (muq 0 q + PXc (fun n => χ n) p.X)
      ≤ |Ce| * (p.L * p.l * Real.log p.l) * q.totient *
          (((C₀ + Real.log q) * p.l) ^ 2 + ((C₀ + Real.log q) * p.l + oneClassMass q p.X) ^ 2
            + 1 / (2 * Real.pi ^ 2) *
              ∑ r ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
                (2 * (p.l + classMass q p.X r) ^ 2
                  + (p.l + classMass q p.X r + classMass q p.X r⁻¹) ^ 2)) := by
    have hμc : Continuous (muq 0 q) := (GammaChi.gammaFactsChi (by norm_num) hq).smooth.continuous
    have hνμ : NuBound p ((C₀ + Real.log q) * p.l) (muq 0 q) := fun τ =>
      hμB 0 q (by norm_num) hq p hTμ τ
    have hBl : p.l ≤ (C₀ + Real.log q) * p.l := by nlinarith
    have h := he p F q (muq 0 q) ((C₀ + Real.log q) * p.l) hp hTe hF hL2 hμc hνμ hBl
    refine (le_abs_self _).trans (h.trans ?_)
    have hX : 0 ≤ ((C₀ + Real.log q) * p.l) ^ 2 + ((C₀ + Real.log q) * p.l + oneClassMass q p.X) ^ 2
        + 1 / (2 * Real.pi ^ 2) *
          ∑ r ∈ (Finset.univ : Finset (ZMod q)).filter IsUnit,
            (2 * (p.l + classMass q p.X r) ^ 2
              + (p.l + classMass q p.X r + classMass q p.X r⁻¹) ^ 2) := by positivity
    have hP : 0 ≤ p.L * p.l * Real.log p.l * q.totient := by
      have := Real.log_nonneg hl1; positivity
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self Ce) hP) hX
    calc Ce * (p.L * p.l * Real.log p.l) * q.totient * _ = Ce * (p.L * p.l * Real.log p.l * q.totient) * _ := by
          ring
      _ ≤ |Ce| * (p.L * p.l * Real.log p.l * q.totient) * _ := this
      _ = _ := by ring
  have hmain : (q.totient : ℝ) * (p.T * p.L / (2 * π) * (ell1q q p.T ^ 2 + p.L ^ 2 / 3))
      = (q.totient : ℝ) * (p.T * p.L / (2 * π) * ell1q q p.T ^ 2)
        + (q.totient : ℝ) * (p.T / π * (p.L ^ 3 / 6)) := by
    field_simp; ring
  have hφ0 : (0 : ℝ) ≤ q.totient := Nat.cast_nonneg _
  have hmumu' := mul_le_mul_of_nonneg_left hmumu hφ0
  rw [hmain]
  linarith only [hmumu', hPP, hPP', hcross, hends]

end RHTower
