import GaloisForLFunctions.RHTower.FamilyCellRates
import GaloisForLFunctions.RHTower.FamilyCellBudget

/-!
# The family certificate at one height

For a prime `q` and the nontrivial characters modulo `q`, the summed rank–trace certificate
(`family_seam_at`), the family error budget (`family_budget`) and its Frobenius share (`family_phi_budget`)
combine into (`family_cell_at`)

`(2 − c − ε) ∑_{χ ≠ 1} N_χ(T, 2T) ≤ ∑_{χ ≠ 1} N₀*_χ(T, 2T)`,   `c = 1/λ₁ + λ₁/3`,

as soon as the per-character trace errors `L E`, the Riemann–von Mangoldt error `R_N`, the boundary counts
`N_II`, the tail `θ₀/(aL)` and the summed Frobenius bound are within their shares of `ε N_low`,
`N_low = Tℓ₁/2π − R_N`.  Every input is stated at the single height `T`.
-/

open MeasureTheory Real Set Zeta23 Zeta23.ThmE Zeta23.PrimeSide Zeta23.Assembly RHLinalg

noncomputable section

namespace RHTower

variable {P : Params} {T : ℝ}

theorem trGt2ChiA_nonneg (κ q : ℕ) (c : ℕ → ℂ) (p : Setting) (F : LocalFun) : 0 ≤ trGt2ChiA κ q c p F := by
  rw [trGt2ChiA_eq]; exact trGt2Nu_nonneg _ _ _

/-- **The family certificate at one height.** -/
theorem family_cell_at (hP : ParamsValidFam P) {q : ℕ} [NeZero q] (hq : 1 < q) (hprime : q.Prime)
    (hT300 : Tail.T₀ ≤ T) (hwL : 8 * P.w ≤ P.L T)
    {E RN NIIb ρB η δ c C K Mj PB ε : ℝ}
    (htr : ∀ χ ∈ nontrivChars q,
      |trGtChiA (parity χ) q (coeff χ) (P.toSetting T) (P.localFun T)
        - P.a T * P.L T * ((famZ hq χ).N T (2 * T) : ℝ)| ≤ P.L T * E)
    (hRvM : ∀ χ ∈ nontrivChars q, |((famZ hq χ).N T (2 * T) : ℝ) - T / (2 * π) * ell1q q T| ≤ RN)
    (hNIIχ : ∀ χ ∈ nontrivChars q, (NII (famZ hq χ) T : ℝ) ≤ NIIb)
    (hθ : Tail.theta0 (uniformA * (1 + Real.log q)) (Real.exp (P.L T / 4) * P.C1 T) T
      / (P.a T * P.L T) ≤ ρB)
    (hFr : ∑ χ ∈ nontrivChars q, trGt2ChiA (parity χ) q (coeff χ) (P.toSetting T) (P.localFun T)
      ≤ (1 + η) * ((((nontrivChars q).card : ℝ) + 1)
          * (c * (T / (2 * π) * ell1q q T) * P.L T ^ 2 + K * Mj))
        + ((nontrivChars q).card : ℝ) * ((1 + 1 / η) * PB))
    (haδ : 1 / P.a T ^ 2 ≤ 1 + δ) (hη0 : 0 < η) (hη : η ≤ δ)
    (hm : 1 ≤ ((nontrivChars q).card : ℝ)) (hmδ : 1 / ((nontrivChars q).card : ℝ) ≤ δ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1) (hc0 : 0 ≤ c) (hc : c ≤ C)
    (hNm : T / (2 * π) * ell1q q T ≤ 2 * (T / (2 * π) * ell1q q T - RN)) (hRN0 : 0 ≤ RN)
    (hRN : C * RN ≤ ε / 64 * (T / (2 * π) * ell1q q T - RN)) (hδC : 14 * δ * C ≤ ε / 32)
    (hK : 0 ≤ K) (hMj0 : 0 ≤ Mj) (hPB0 : 0 ≤ PB)
    (hMj : 16 * (K * Mj) ≤ ε / 64 * (T / (2 * π) * ell1q q T - RN) * P.L T ^ 2)
    (hPB : 4 * ((1 + 1 / η) * PB) ≤ ε / 64 * (T / (2 * π) * ell1q q T - RN) * P.L T ^ 2)
    (hNl0 : 0 < T / (2 * π) * ell1q q T - RN) (hNm0 : 0 ≤ T / (2 * π) * ell1q q T)
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hE0 : 0 ≤ E)
    (hE : 8 * E ≤ ε / 8 * (T / (2 * π) * ell1q q T - RN))
    (hNIIb : 3 * NIIb ≤ ε / 8 * (T / (2 * π) * ell1q q T - RN)) (hρB1 : ρB ≤ 1)
    (hr5 : 5 * ρB ≤ ε / 8 * (T / (2 * π) * ell1q q T - RN))
    (hr6 : 2 * ρB * Real.sqrt (C + 1) ≤ ε / 8 * Real.sqrt (T / (2 * π) * ell1q q T - RN)) :
    (2 - c - ε) * ∑ χ ∈ nontrivChars q, ((famZ hq χ).N T (2 * T) : ℝ)
      ≤ ∑ χ ∈ nontrivChars q, ((famZ hq χ).N0star T (2 * T) : ℝ) := by
  have hseam := family_seam_at hP hq hprime hT300 hwL htr hFr
  obtain ⟨Nm, hNmdef⟩ : ∃ x : ℝ, x = T / (2 * π) * ell1q q T := ⟨_, rfl⟩
  obtain ⟨m, hmdef⟩ : ∃ x : ℝ, x = ((nontrivChars q).card : ℝ) := ⟨_, rfl⟩
  obtain ⟨N, hNdef⟩ : ∃ x : ℝ, x = ∑ χ ∈ nontrivChars q, ((famZ hq χ).N T (2 * T) : ℝ) := ⟨_, rfl⟩
  rw [← hNmdef] at hNm hRN hMj hPB hNl0 hNm0 hE hNIIb hr5 hr6 hFr hseam
  rw [← hmdef] at hm hmδ hFr hseam
  rw [← hNdef] at hseam ⊢
  obtain ⟨Nl, hNldef⟩ : ∃ x : ℝ, x = Nm - RN := ⟨_, rfl⟩
  rw [← hNldef] at hNm hRN hMj hPB hNl0 hE hNIIb hr5 hr6
  have hm0 : 0 < m := by linarith
  have ha : 1 / 2 ≤ P.a T := half_le_a_fam hP hwL
  have ha0 : 0 < P.a T := by linarith
  have hT3 : (300:ℝ) ≤ T := hT300
  have hL : 0 < P.L T := by have := hP.one_le_w; linarith
  -- the counts are at least `N_low`
  have hN : m * Nl ≤ N := by
    have h1 : ∀ χ ∈ nontrivChars q, Nl ≤ ((famZ hq χ).N T (2 * T) : ℝ) := fun χ hχ => by
      have := (abs_le.mp (hRvM χ hχ)).1
      rw [← hNmdef] at this
      linarith
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_const, nsmul_eq_mul, ← hmdef, ← hNdef] at h2
    linarith
  -- the Frobenius share
  have hphi := family_phi_budget (a := P.a T) (L := P.L T) (η := η) (m := m) (c := c) (C := C)
    (Nm := Nm) (Nl := Nl) (RN := RN) (K := K) (Mj := Mj) (P := PB) (δ := δ) (ε := ε) (N := N)
    ha haδ hη0 hη hm hmδ hδ0 hδ1 hc0 hc (by linarith) hNm hRN0 hRN hδC hL hK hMj0 hPB0 hMj hPB hN
    hNl0.le hNm0 hε.le
  -- the trace and boundary shares
  have hR : 4 * (m * (E / P.a T)) ≤ ε / 8 * (m * Nl) := by
    have h1 : E / P.a T ≤ 2 * E := by
      rw [div_le_iff₀ ha0]
      linarith only [mul_nonneg hE0 (by linarith : (0:ℝ) ≤ 2 * P.a T - 1)]
    have h2 := mul_le_mul_of_nonneg_left h1 hm0.le
    have h3 : m * (8 * E) ≤ m * (ε / 8 * Nl) := mul_le_mul_of_nonneg_left hE hm0.le
    linarith only [h2, h3]
  have hNII : 3 * ∑ χ ∈ nontrivChars q, (NII (famZ hq χ) T : ℝ) ≤ ε / 8 * (m * Nl) := by
    have h1 := Finset.sum_le_sum hNIIχ
    rw [Finset.sum_const, nsmul_eq_mul, ← hmdef] at h1
    have h2 := mul_le_mul_of_nonneg_left hNIIb hm0.le
    linarith only [h1, h2]
  have hΦ0 : 0 ≤ ((P.a T * P.L T)⁻¹) ^ 2 * ((1 + η) * ((m + 1) * (c * Nm * P.L T ^ 2 + K * Mj))
      + m * ((1 + 1 / η) * PB)) := by
    have h0 : 0 ≤ ∑ χ ∈ nontrivChars q, trGt2ChiA (parity χ) q (coeff χ) (P.toSetting T) (P.localFun T) :=
      Finset.sum_nonneg fun χ _ => trGt2ChiA_nonneg _ _ _ _ _
    exact mul_nonneg (sq_nonneg _) (h0.trans hFr)
  have hb0 : 0 ≤ Tail.theta0 (uniformA * (1 + Real.log q)) (Real.exp (P.L T / 4) * P.C1 T) T
      / (P.a T * P.L T) := by
    have hq1 : (1:ℝ) ≤ q := by exact_mod_cast hq.le
    have hlq := Real.log_nonneg hq1
    have hA : 0 ≤ uniformA * (1 + Real.log q) :=
      mul_nonneg (zero_le_one.trans one_le_uniformLocalCountConst) (by linarith)
    exact div_nonneg (div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (by linarith)))
      (by linarith)) (by positivity)
  have hbud := family_budget (N := N) (Nl := Nl) (m := m) (R := m * (E / P.a T))
    (Φ := ((P.a T * P.L T)⁻¹) ^ 2 * ((1 + η) * ((m + 1) * (c * Nm * P.L T ^ 2 + K * Mj))
      + m * ((1 + 1 / η) * PB)))
    (NIIs := ∑ χ ∈ nontrivChars q, (NII (famZ hq χ) T : ℝ)) (ρB := ρB) (c := c) (C := C) (ε := ε)
    hm0 hNl0 hN hc hR hNII hphi hΦ0 hb0 hθ hρB1 hr5 hr6 hε hε1
  refine hbud.trans (le_of_eq_of_le ?_ hseam)
  ring

end RHTower
