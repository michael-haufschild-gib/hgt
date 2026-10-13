import GaloisForLFunctions.RHTower.FamilyCell

/-!
# The family certificate in a modulus cell

Fix a bandwidth `λ ∈ (0, 2)` and a cell `T^{κ_lo} ≤ q ≤ T^{κ_hi}` of prime moduli with `κ_lo > 0`,
`κ_hi < 1` and `λ − κ_lo < 1` (so `X = (T/2π)^λ ≤ q T^{1−δ}`).  Then for every `ε > 0` and all large `T`
(`family_cell`):

`(H(λ₁) − ε) ∑_{χ ≠ 1 (mod q)} N_χ(T, 2T) ≤ ∑_{χ ≠ 1 (mod q)} N₀*_χ(T, 2T)`,

`λ₁ = λ l/ℓ₁(q, T)` the bandwidth relative to the analytic conductor and `H(x) = 2 − 1/x − x/3`.  The point
is that `λ` may exceed `1`: the family average needs only the residue-class Montgomery–Vaughan inequality,
whose off-diagonal error `X/q` is a power below `T` exactly when `X ≤ q T^{1−δ}`.
-/

open MeasureTheory Real Set Filter Topology Zeta23 Zeta23.ThmE Zeta23.PrimeSide Zeta23.Assembly RHLinalg

noncomputable section

namespace RHTower

/-- `a ≥ 1 − u`, `u ≤ 1/4` give `1/a² ≤ 1 + 4u`. -/
theorem inv_sq_le_of_ge {a u : ℝ} (hu0 : 0 ≤ u) (hu : u ≤ 1 / 4) (ha : 1 - u ≤ a) :
    1 / a ^ 2 ≤ 1 + 4 * u := by
  have ha0 : 0 < a := by linarith
  have h1 : 1 - 2 * u ≤ a ^ 2 := by nlinarith
  rw [div_le_iff₀ (by positivity)]
  have h2 : (1 + 4 * u) * (1 - 2 * u) ≥ 1 := by nlinarith
  nlinarith

/-- The Frobenius majorant is nonnegative. -/
theorem famMaj_nonneg {q : ℕ} {T L l X : ℝ} (hq : 1 ≤ q) (hT : 0 ≤ T) (hL : 1 ≤ L) (hl : 1 ≤ l)
    (hX : 0 ≤ X) : 0 ≤ famMaj q T L l X := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlq := Real.log_nonneg hq1
  have hlL := Real.log_nonneg hL
  have hll := Real.log_nonneg hl
  have hL0 : 0 ≤ L := by linarith
  have hl0 : 0 ≤ l := by linarith
  unfold famMaj
  have h1 : 0 ≤ (1 + Real.log q) ^ 2 * l ^ 2 * Real.log L := by positivity
  have h2 : 0 ≤ T * L * ell1q q T ^ 2 / l ^ 2 := by positivity
  have h3 : 0 ≤ (1 + Real.log q) * l * Real.sqrt X := by positivity
  have h4 : 0 ≤ (1 + Real.log (Real.log q + 8) ^ 2) * T * L ^ 2 := by positivity
  have h5 : 0 ≤ L ^ 3 * (1 + Real.log L) * (X / q + L) := by positivity
  have h6 : 0 ≤ L * l * Real.log l * ((1 + Real.log q) ^ 2 * l ^ 2 + q * l ^ 2 + (X / q + 1) * L ^ 2) := by
    positivity
  linarith

/-- **The family certificate in a modulus cell.** -/
theorem family_cell {lam κlo κhi : ℝ} (h0 : 0 < lam) (h2 : lam < 2) (hκlo : 0 < κlo)
    (hκ : lam - κlo < 1) (hκhi : κhi < 1) (hκhi0 : 0 ≤ κhi) :
    ∀ ε > 0, ∃ T₀ : ℝ, ∀ T ≥ T₀, ∀ (q : ℕ) [NeZero q], q.Prime → (q : ℝ) ≤ T ^ κhi → T ^ κlo ≤ q →
      (Hfun (lam1q (stdParams lam) q T) - ε) * ∑ χ ∈ nontrivChars q, (NcountL χ T (2 * T) : ℝ)
        ≤ ∑ χ ∈ nontrivChars q, (N0starL χ T (2 * T) : ℝ) := by
  intro ε hε
  obtain ⟨ε', hε'def⟩ : ∃ x : ℝ, x = min ε 1 := ⟨_, rfl⟩
  have hε'0 : 0 < ε' := by rw [hε'def]; exact lt_min hε one_pos
  have hε'1 : ε' ≤ 1 := by rw [hε'def]; exact min_le_right _ _
  have hε'ε : ε' ≤ ε := by rw [hε'def]; exact min_le_left _ _
  have hPfam : ParamsValidFam (stdParams lam) := ⟨taperProfile_stdProfile, h0, le_refl (1:ℝ)⟩
  obtain ⟨Cr, Tr, hrvm⟩ := mainChi_uniform
  obtain ⟨A, hAdef⟩ : ∃ x : ℝ, x = |Cr| * (κhi + 1) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  obtain ⟨Ct, Tt, hCt, htrU⟩ := prop_trace_uniform_wide (cϱ := (stdParams lam).crho) h0 A
  obtain ⟨K, M, CP, Tf, hK, hM, hCP, hfrob⟩ := family_frob_nontriv (stdParams lam).crho lam h0
  obtain ⟨TL, hTL⟩ := localHypsCoreW_eventually_fam hPfam
  obtain ⟨R, hRdef⟩ : ∃ x : ℝ, x = Taper.l1Deriv2 stdProfile := ⟨_, rfl⟩
  have hR0 : 0 ≤ R := by rw [hRdef]; exact MeasureTheory.integral_nonneg fun x => abs_nonneg _
  have huA1 : 1 ≤ uniformA := one_le_uniformLocalCountConst
  obtain ⟨C, hCdef⟩ : ∃ x : ℝ, x = 6 / lam + 1 := ⟨_, rfl⟩
  have hC1 : 1 ≤ C := by rw [hCdef]; have : 0 ≤ 6 / lam := by positivity
                         linarith
  obtain ⟨δ, hδdef⟩ : ∃ x : ℝ, x = min 1 (ε' / (448 * C)) := ⟨_, rfl⟩
  have hδ0 : 0 < δ := by rw [hδdef]; exact lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := by rw [hδdef]; exact min_le_left _ _
  have hδε : δ ≤ ε' / (448 * C) := by rw [hδdef]; exact min_le_right _ _
  have hsC : 0 < Real.sqrt (C + 1) := Real.sqrt_pos.mpr (by linarith)
  obtain ⟨δB, hδBdef⟩ : ∃ x : ℝ, x = min 1 (min (ε' / 40) (ε' / (16 * Real.sqrt (C + 1)))) :=
    ⟨_, rfl⟩
  have hδB0 : 0 < δB := by
    rw [hδBdef]; exact lt_min one_pos (lt_min (by positivity) (by positivity))
  have hδB1 : δB ≤ 1 := by rw [hδBdef]; exact min_le_left _ _
  have hδB2 : δB ≤ ε' / 40 := by rw [hδBdef]; exact (min_le_right _ _).trans (min_le_left _ _)
  have hδB3 : δB ≤ ε' / (16 * Real.sqrt (C + 1)) := by
    rw [hδBdef]; exact (min_le_right _ _).trans (min_le_right _ _)
  have hπ : 0 < π := Real.pi_pos
  -- the rates
  have e0 := eventually_l_bounds.and (eventually_ge_atTop
      (max (max (max Tr Tt) (max Tf TL)) (max 300 (4 * π))))
  have e1 := Real.tendsto_log_atTop.eventually_ge_atTop (16 / (lam * δ))
  have e2 := Real.tendsto_log_atTop.eventually_ge_atTop (2 / δ)
  have e3 := (tendsto_rpow_atTop hκlo).eventually_ge_atTop (2 + 1 / δ)
  have e4 := eventually_famMaj_le h0 h2 hκ hκhi (by positivity : (0:ℝ) < ε' / (4096 * π * (K + 1)))
  have e5 := eventually_parity_le h0 hM hCP (by positivity : (0:ℝ) < ε' / (256 * π))
  have e6 := eventually_log_pow_rpow_le 1 (by norm_num : (0:ℝ) < 1) (by positivity : (0:ℝ) ≤ 32 * Ct)
    (by positivity : (0:ℝ) < ε' / (128 * π))
  have e7 := eventually_log_pow_rpow_le 0 (by linarith : lam / 2 < 1) (by positivity : (0:ℝ) ≤ 16 * Ct)
    (by positivity : (0:ℝ) < ε' / (128 * π))
  have e8 := eventually_log_pow_rpow_le 1 (by norm_num : (1:ℝ) / 2 < 1)
    (by positivity : (0:ℝ) ≤ 54 * uniformA) (by positivity : (0:ℝ) < ε' / (64 * π))
  have e9 := eventually_log_pow_rpow_le 1 (by norm_num : (0:ℝ) < 1) hA0
    (by positivity : (0:ℝ) < 1 / (8 * π))
  have e10 := eventually_log_pow_rpow_le 1 (by norm_num : (0:ℝ) < 1) (by positivity : (0:ℝ) ≤ C * A)
    (by positivity : (0:ℝ) < ε' / (512 * π))
  have e11 := eventually_log_pow_rpow_le_const 2 (by linarith : lam / 2 - 1 < 0)
    (by positivity : (0:ℝ) ≤ 64 * uniformA * R ^ 2) hδB0
  obtain ⟨T₀, hT₀⟩ := Filter.eventually_atTop.mp
    (((((((((((e0.and e1).and e2).and e3).and e4).and e5).and e6).and e7).and e8).and e9).and e10).and e11)
  refine ⟨T₀, fun T hT q _ hprime hqT hqT' => ?_⟩
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hlog1, hl1, hlo, hhi⟩, hTge⟩, hlogL⟩, hlogδ⟩, hTκ⟩, rMaj⟩, rPar⟩, rE1⟩, rE2⟩,
    rNII⟩, rRN1⟩, rRN2⟩, rB⟩ := hT₀ T hT
  -- thresholds
  have hTr : Tr ≤ T := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hTge
  have hTt : Tt ≤ T := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hTge
  have hTf : Tf ≤ T := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hTge
  have hTLT : TL ≤ T := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hTge
  have hT300 : Tail.T₀ ≤ T := by
    show (300 : ℝ) ≤ T
    exact le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hTge
  have hT4π : 4 * π ≤ T := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hTge
  have hT0 : 0 < T := by have : (300:ℝ) ≤ T := hT300; linarith
  obtain ⟨lT, hlTdef⟩ : ∃ x : ℝ, x = Real.log T := ⟨_, rfl⟩
  obtain ⟨l, hldef⟩ : ∃ x : ℝ, x = Zeta23.l T := ⟨_, rfl⟩
  rw [← hlTdef] at hlog1 hlo hhi hlogL hlogδ rE1 rE2 rNII rRN1 rRN2 rB
  rw [← hldef] at hl1 hlo hhi
  rw [pow_one, Real.rpow_zero, mul_one] at rE1 rRN1 rRN2
  rw [pow_zero, mul_one] at rE2
  rw [pow_one] at rNII
  -- the parameters at `T`
  have hLdef : (stdParams lam).L T = lam * l := by rw [hldef]; rfl
  have hw : (stdParams lam).w = 1 := rfl
  have hlam_l : 0 < lam * l := mul_pos h0 (by linarith only [hl1])
  have hδl : 8 / δ ≤ lam * l := by
    rw [div_le_iff₀ (mul_pos h0 hδ0)] at hlogL
    have h1 : lam * (lT / 2) ≤ lam * l := mul_le_mul_of_nonneg_left hlo h0.le
    have h2 := mul_le_mul_of_nonneg_right h1 hδ0.le
    rw [div_le_iff₀ hδ0]
    linarith only [h2, hlogL]
  have h8δ : 8 ≤ 8 / δ := by rw [le_div_iff₀ hδ0]; linarith only [hδ1]
  have hL8 : 8 ≤ (stdParams lam).L T := by rw [hLdef]; linarith only [hδl, h8δ]
  have hL0 : 0 < (stdParams lam).L T := by linarith only [hL8]
  have hwL : 8 * (stdParams lam).w ≤ (stdParams lam).L T := by rw [hw]; linarith only [hL8]
  have ha2 : 1 / 2 ≤ (stdParams lam).a T := half_le_a_fam hPfam hwL
  have hb1 : 1 - 2 * (stdParams lam).w / (stdParams lam).L T ≤ (stdParams lam).b T :=
    Taper.one_sub_le_bConst hPfam.taper hPfam.w_pos (hPfam.two_w_le hwL)
  have hba : (stdParams lam).b T ≤ (stdParams lam).a T :=
    Taper.bConst_le_aConst hPfam.taper hPfam.w_pos (hPfam.two_w_le hwL)
  have haδ : 1 / (stdParams lam).a T ^ 2 ≤ 1 + δ := by
    rw [hw, mul_one] at hb1
    have hu0 : 0 ≤ 2 / (stdParams lam).L T := div_nonneg zero_le_two hL0.le
    have hu : 2 / (stdParams lam).L T ≤ 1 / 4 := by
      rw [div_le_iff₀ hL0]; linarith only [hL8]
    have h1 := inv_sq_le_of_ge hu0 hu (hb1.trans hba)
    have h2 : 4 * (2 / (stdParams lam).L T) ≤ δ := by
      rw [hLdef]
      have h3 : 8 / (lam * l) ≤ δ := by
        rw [div_le_iff₀ hlam_l]
        rw [div_le_iff₀ hδ0] at hδl; linarith only [hδl]
      have e : 4 * (2 / (lam * l)) = 8 / (lam * l) := by ring
      linarith only [h3, e]
    linarith only [h1, h2]
  -- the modulus
  have hq1 : 1 < q := hprime.one_lt
  have hq1r : (1 : ℝ) < q := by exact_mod_cast hq1
  have hlq0 : 0 ≤ Real.log q := Real.log_nonneg hq1r.le
  have hlq : Real.log q ≤ κhi * lT := by
    have h := Real.log_le_log (by positivity) hqT
    rwa [Real.log_rpow hT0, ← hlTdef] at h
  have hlqT : Real.log q ≤ lT := by
    have : κhi * lT ≤ 1 * lT := mul_le_mul_of_nonneg_right hκhi.le (by linarith only [hlog1])
    linarith only [this, hlq]
  have hcard : ((nontrivChars q).card : ℝ) = q - 2 := by
    rw [card_nontrivChars, Nat.totient_prime hprime, Nat.cast_sub hq1.le]
    push_cast; ring
  have hqδ : 2 + 1 / δ ≤ q := hTκ.trans hqT'
  have hδinv : 1 ≤ 1 / δ := by rw [le_div_iff₀ hδ0]; linarith only [hδ1]
  have hm1 : 1 ≤ ((nontrivChars q).card : ℝ) := by
    rw [hcard]; linarith only [hqδ, hδinv]
  have hmδ : 1 / ((nontrivChars q).card : ℝ) ≤ δ := by
    rw [div_le_iff₀ (by linarith only [hm1]), hcard]
    have : 1 / δ ≤ q - 2 := by linarith only [hqδ]
    rw [div_le_iff₀ hδ0] at this
    linarith only [this]
  -- the main term and the conductor
  have hell1 : l ≤ ell1q q T := by rw [hldef]; exact l_le_ell1q hq1.le hT0
  have hell2 : ell1q q T ≤ Real.log q + l + 1 := by rw [hldef]; exact ell1q_le_log_add hq1.le hT0
  have hell0 : 0 < ell1q q T := by linarith only [hell1, hl1]
  obtain ⟨Nm, hNmdef⟩ : ∃ x : ℝ, x = T / (2 * π) * ell1q q T := ⟨_, rfl⟩
  obtain ⟨RN, hRNdef⟩ : ∃ x : ℝ, x = A * lT := ⟨_, rfl⟩
  have hRN0 : 0 ≤ RN := by rw [hRNdef]; exact mul_nonneg hA0 (by linarith only [hlog1])
  have hRNle : RN ≤ T / (8 * π) := by
    rw [hRNdef]
    have e : 1 / (8 * π) * T = T / (8 * π) := by ring
    linarith only [rRN1, e]
  have hNmT : T * l / (2 * π) ≤ Nm := by
    rw [hNmdef]
    have : T * l / (2 * π) = T / (2 * π) * l := by ring
    rw [this]; exact mul_le_mul_of_nonneg_left hell1 (by positivity)
  have hTTl : T ≤ T * l := le_mul_of_one_le_right hT0.le hl1
  have hTl : T / (2 * π) ≤ T * l / (2 * π) := div_le_div_of_nonneg_right hTTl (by positivity)
  have hT8 : T / (8 * π) = T / (2 * π) / 4 := by field_simp; ring
  have hT2π0 : 0 ≤ T / (2 * π) := by positivity
  have hNm2 : Nm ≤ 2 * (Nm - RN) := by linarith only [hRNle, hNmT, hTl, hT8, hT2π0]
  have hNlTl : T * l / (4 * π) ≤ Nm - RN := by
    have e : T * l / (4 * π) = T * l / (2 * π) / 2 := by field_simp; ring
    have e2 : T / (2 * π) / 4 ≤ T * l / (2 * π) / 4 := by linarith only [hTl]
    linarith only [e, hNmT, hRNle, hT8, e2, hT2π0, hTl]
  have hNl1 : 1 ≤ Nm - RN := by
    have h1 : T / (4 * π) ≤ T * l / (4 * π) := div_le_div_of_nonneg_right hTTl (by positivity)
    have h2 : 1 ≤ T / (4 * π) := by rw [le_div_iff₀ (by positivity)]; linarith only [hT4π]
    linarith only [h1, h2, hNlTl]
  have hNlT : T * lT / (8 * π) ≤ Nm - RN := by
    have h1 : T * lT / (8 * π) ≤ T * l / (4 * π) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      have := mul_le_mul_of_nonneg_left (by linarith only [hlo] : lT ≤ 2 * l)
        (by positivity : (0:ℝ) ≤ T * (4 * π))
      linarith only [this]
    linarith only [h1, hNlTl]
  -- per-character inputs
  have hprim : ∀ χ ∈ nontrivChars q, χ.IsPrimitive := fun χ hχ =>
    isPrimitive_of_prime hprime χ (Finset.mem_filter.mp hχ).2
  have hRvMχ : ∀ χ ∈ nontrivChars q,
      |((famZ hq1 χ).N T (2 * T) : ℝ) - T / (2 * π) * ell1q q T| ≤ RN := by
    intro χ hχ
    rw [famZ_N hq1 (hprim χ hχ)]
    refine (hrvm q χ hq1 (hprim χ hχ) T hTr).trans ?_
    rw [hRNdef, hAdef, ← hlTdef]
    have h1 : Real.log q + lT ≤ (κhi + 1) * lT := by linarith only [hlq]
    calc Cr * (Real.log q + lT) ≤ |Cr| * (Real.log q + lT) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith only [hlq0, hlog1])
      _ ≤ |Cr| * ((κhi + 1) * lT) := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
      _ = |Cr| * (κhi + 1) * lT := by ring
  have hXdef : (stdParams lam).X T = Real.exp (lam * l) := by rw [hldef]; rfl
  have hsX : Real.sqrt ((stdParams lam).X T) ≤ T ^ (lam / 2) := by
    have h := sqrt_exp_lam_l_le h0.le hT0 (by rw [← hldef, ← hlTdef]; exact hhi)
    rw [← hldef] at h
    rw [hXdef]; exact h
  obtain ⟨E, hEdef⟩ : ∃ x : ℝ, x = Ct * (1 + Real.log q) * (1 + lT + Real.sqrt ((stdParams lam).X T)) :=
    ⟨_, rfl⟩
  have hE0 : 0 ≤ E := by
    rw [hEdef]
    exact mul_nonneg (mul_nonneg hCt (by linarith only [hlq0]))
      (by linarith only [hlog1, Real.sqrt_nonneg ((stdParams lam).X T)])
  have htrχ : ∀ χ ∈ nontrivChars q,
      |trGtChiA (parity χ) q (coeff χ) ((stdParams lam).toSetting T) ((stdParams lam).localFun T)
        - (stdParams lam).a T * (stdParams lam).L T * ((famZ hq1 χ).N T (2 * T) : ℝ)|
        ≤ (stdParams lam).L T * E := by
    intro χ hχ
    have hR' : |((famZ hq1 χ).N T (2 * T) : ℝ) - T / (2 * π) * ell1q q T| ≤ A * Real.log T := by
      rw [← hlTdef, ← hRNdef]; exact hRvMχ χ hχ
    have h := htrU (parity χ) q parity_le_one hq1.le (coeff χ) (coeffOK_dirichlet χ)
      ((stdParams lam).toSetting T) ((stdParams lam).localFun T) rfl hTt (hTL T hTLT) _ hR'
    refine le_trans h (le_of_eq ?_)
    rw [hEdef, hlTdef]
    show Ct * (1 + Real.log q) * ((stdParams lam).L T * (1 + Real.log T + Real.sqrt ((stdParams lam).X T)))
      = (stdParams lam).L T * (Ct * (1 + Real.log q) * (1 + Real.log T + Real.sqrt ((stdParams lam).X T)))
    ring
  obtain ⟨NIIb, hNIIbdef⟩ : ∃ x : ℝ, x = 3 * (uniformA * (1 + Real.log q)) * Real.sqrt T
      * Real.log (4 * T) := ⟨_, rfl⟩
  have hNIIχ : ∀ χ ∈ nontrivChars q, (NII (famZ hq1 χ) T : ℝ) ≤ NIIb := by
    intro χ hχ
    rw [famZ_of_prim hq1 (hprim χ hχ), hNIIbdef]
    exact uniform_NII_le hq1 (hprim χ hχ) hT300
  -- the tail
  obtain ⟨ρB, hρBdef⟩ : ∃ x : ℝ, x = 64 * uniformA * R ^ 2 * lT ^ 2 * T ^ (lam / 2 - 1) := ⟨_, rfl⟩
  have hρBδ : ρB ≤ δB := by rw [hρBdef]; exact rB
  have hθ : Tail.theta0 (uniformA * (1 + Real.log q)) (Real.exp ((stdParams lam).L T / 4)
      * (stdParams lam).C1 T) T / ((stdParams lam).a T * (stdParams lam).L T) ≤ ρB := by
    have hA₀ : 0 ≤ uniformA * (1 + Real.log q) :=
      mul_nonneg (zero_le_one.trans huA1) (by linarith only [hlq0])
    have hC1 : (stdParams lam).C1 T ≤ 2 * R := by rw [hRdef]; exact C1_le_fam hPfam hwL
    have hth := theta0_le_fam hPfam hT300 hA₀ (Tail.C1_nonneg _ T) hC1
    have hth0 : 0 ≤ Tail.theta0 (uniformA * (1 + Real.log q))
        (Real.exp ((stdParams lam).L T / 4) * (stdParams lam).C1 T) T :=
      div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (by linarith only [hT0, hT4π, Real.pi_gt_three])))
        hT0.le
    have haL1 : 1 ≤ (stdParams lam).a T * (stdParams lam).L T := by nlinarith only [ha2, hL8]
    have h1 : Tail.theta0 (uniformA * (1 + Real.log q))
        (Real.exp ((stdParams lam).L T / 4) * (stdParams lam).C1 T) T
          / ((stdParams lam).a T * (stdParams lam).L T)
        ≤ Tail.theta0 (uniformA * (1 + Real.log q))
          (Real.exp ((stdParams lam).L T / 4) * (stdParams lam).C1 T) T :=
      div_le_self hth0 haL1
    have hl' : Zeta23.l T ≤ lT := by rw [← hldef]; exact hhi
    have h1q : 1 + Real.log q ≤ 2 * lT := by linarith only [hlqT, hlog1]
    have hTp : 0 ≤ T ^ ((stdParams lam).lam / 2 - 1) := by positivity
    have h2 : 32 * (uniformA * (1 + Real.log q)) * R ^ 2 * Zeta23.l T * T ^ ((stdParams lam).lam / 2 - 1)
        ≤ ρB := by
      rw [hρBdef]
      show 32 * (uniformA * (1 + Real.log q)) * R ^ 2 * Zeta23.l T * T ^ (lam / 2 - 1)
        ≤ 64 * uniformA * R ^ 2 * lT ^ 2 * T ^ (lam / 2 - 1)
      have hTp' : 0 ≤ T ^ (lam / 2 - 1) := by positivity
      have hu0 : 0 ≤ uniformA := zero_le_one.trans huA1
      have a1 : uniformA * (1 + Real.log q) ≤ uniformA * (2 * lT) := mul_le_mul_of_nonneg_left h1q hu0
      have a2 : uniformA * (1 + Real.log q) * Zeta23.l T ≤ uniformA * (2 * lT) * lT :=
        mul_le_mul a1 hl' (by rw [← hldef]; linarith only [hl1]) (by positivity)
      have a3 := mul_le_mul_of_nonneg_right a2 (mul_nonneg (sq_nonneg R) hTp')
      have e1 : 32 * (uniformA * (1 + Real.log q)) * R ^ 2 * Zeta23.l T * T ^ (lam / 2 - 1)
          = 32 * (uniformA * (1 + Real.log q) * Zeta23.l T * (R ^ 2 * T ^ (lam / 2 - 1))) := by ring
      have e2 : 64 * uniformA * R ^ 2 * lT ^ 2 * T ^ (lam / 2 - 1)
          = 32 * (uniformA * (2 * lT) * lT * (R ^ 2 * T ^ (lam / 2 - 1))) := by ring
      rw [e1, e2]
      linarith only [a3]
    linarith only [h1, hth, h2]
  have hρB0 : 0 ≤ ρB := by rw [hρBdef]; have := zero_le_one.trans huA1; positivity
  have hρB1 : ρB ≤ 1 := hρBδ.trans hδB1
  have hr5 : 5 * ρB ≤ ε' / 8 * (T / (2 * π) * ell1q q T - RN) := by
    rw [← hNmdef]
    have : 5 * ρB ≤ ε' / 8 := by linarith only [hρBδ, hδB2]
    have h2 : ε' / 8 * 1 ≤ ε' / 8 * (Nm - RN) := mul_le_mul_of_nonneg_left hNl1 (by positivity)
    linarith only [this, h2]
  have hr6 : 2 * ρB * Real.sqrt (C + 1) ≤ ε' / 8 * Real.sqrt (T / (2 * π) * ell1q q T - RN) := by
    rw [← hNmdef]
    have h1 : 2 * ρB * Real.sqrt (C + 1) ≤ 2 * (ε' / (16 * Real.sqrt (C + 1))) * Real.sqrt (C + 1) :=
      mul_le_mul_of_nonneg_right (by linarith only [hρBδ, hδB3]) hsC.le
    have e : 2 * (ε' / (16 * Real.sqrt (C + 1))) * Real.sqrt (C + 1) = ε' / 8 := by
      field_simp; ring
    have h2 : 1 ≤ Real.sqrt (Nm - RN) := by
      rw [show (1:ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]; exact Real.sqrt_le_sqrt hNl1
    have h3 : ε' / 8 * 1 ≤ ε' / 8 * Real.sqrt (Nm - RN) := mul_le_mul_of_nonneg_left h2 (by positivity)
    linarith only [h1, e, h3]
  -- the Frobenius sum
  have hl0 : 0 < l := by linarith only [hl1]
  have hL2 : ((stdParams lam).toSetting T).L ≤ 2 * ((stdParams lam).toSetting T).l := by
    show lam * Zeta23.l T ≤ 2 * Zeta23.l T
    rw [← hldef]; nlinarith only [h2, hl1]
  have hη0 : (0 : ℝ) < 1 / l := by positivity
  have hfr := hfrob q hq1.le ((stdParams lam).toSetting T) ((stdParams lam).localFun T) rfl hTf
    (hTL T hTLT) hL2 (1 / l) hη0
  obtain ⟨lam1, hlam1⟩ : ∃ x : ℝ, x = lam1q (stdParams lam) q T := ⟨_, rfl⟩
  have hlam1' : lam1 = (stdParams lam).L T / ell1q q T := by rw [hlam1]; rfl
  obtain ⟨c, hcdef⟩ : ∃ x : ℝ, x = 1 / lam1 + lam1 / 3 := ⟨_, rfl⟩
  have hc_eq : c = ell1q q T / (stdParams lam).L T + (stdParams lam).L T / (3 * ell1q q T) := by
    rw [hcdef, hlam1']; field_simp
  have hφ : (q.totient : ℝ) = ((nontrivChars q).card : ℝ) + 1 := by rw [card_nontrivChars]; ring
  obtain ⟨Mj, hMjdef⟩ : ∃ x : ℝ, x = famMaj q T ((stdParams lam).L T) l ((stdParams lam).X T) :=
    ⟨_, rfl⟩
  obtain ⟨PB, hPBdef⟩ : ∃ x : ℝ, x = M ^ 2 * (T * (2 * π * (stdParams lam).L T))
      + CP * ((stdParams lam).L T * l * Real.log l * (l + M) ^ 2) := ⟨_, rfl⟩
  have hFr : ∑ χ ∈ nontrivChars q, trGt2ChiA (parity χ) q (coeff χ) ((stdParams lam).toSetting T)
        ((stdParams lam).localFun T)
      ≤ (1 + 1 / l) * ((((nontrivChars q).card : ℝ) + 1)
          * (c * (T / (2 * π) * ell1q q T) * (stdParams lam).L T ^ 2 + K * Mj))
        + ((nontrivChars q).card : ℝ) * ((1 + 1 / (1 / l)) * PB) := by
    refine hfr.trans (le_of_eq ?_)
    rw [hφ, hc_eq, hMjdef, hPBdef, hldef]
    rw [← main_frob_eq hL0 hell0]
    rfl
  -- the remaining shares
  have hlogl0 : 0 ≤ Real.log l := Real.log_nonneg hl1
  have hloglT : Real.log l ≤ lT := by
    have := Real.log_le_sub_one_of_pos hl0; linarith only [this, hhi]
  have hMj0 : 0 ≤ Mj := by
    rw [hMjdef]; exact famMaj_nonneg hq1.le hT0.le (by linarith only [hL8]) hl1 (Real.exp_pos _).le
  have hPB0 : 0 ≤ PB := by
    rw [hPBdef]
    have h1 : 0 ≤ M ^ 2 * (T * (2 * π * (stdParams lam).L T)) := by positivity
    have h2 : 0 ≤ CP * ((stdParams lam).L T * l * Real.log l * (l + M) ^ 2) :=
      mul_nonneg hCP (mul_nonneg (mul_nonneg (mul_nonneg hL0.le hl0.le) hlogl0) (sq_nonneg _))
    linarith only [h1, h2]
  have hLl : (stdParams lam).L T ^ 2 = (lam * l) ^ 2 := by rw [hLdef]
  have hMj : 16 * (K * Mj) ≤ ε' / 64 * (Nm - RN) * (stdParams lam).L T ^ 2 := by
    have r := rMaj q hq1.le hqT hqT'
    rw [← hldef] at r
    have hMj' : Mj ≤ ε' / (4096 * π * (K + 1)) * (T * l * (lam * l) ^ 2) := by
      rw [hMjdef, hLdef, hXdef]; exact r
    have hTlL : 0 ≤ T * l * (lam * l) ^ 2 := by positivity
    have h1 : 16 * (K * Mj) ≤ 16 * K * (ε' / (4096 * π * (K + 1))) * (T * l * (lam * l) ^ 2) := by
      have := mul_le_mul_of_nonneg_left hMj' (by positivity : (0:ℝ) ≤ 16 * K)
      linarith only [this]
    have h2 : 16 * K * (ε' / (4096 * π * (K + 1))) ≤ ε' / (256 * π) := by
      rw [show 16 * K * (ε' / (4096 * π * (K + 1))) = ε' / (256 * π) * (K / (K + 1)) by
        field_simp; ring]
      have : K / (K + 1) ≤ 1 := by rw [div_le_one (by linarith only [hK])]; linarith only
      have h0' : 0 ≤ ε' / (256 * π) := by positivity
      nlinarith only [this, h0']
    have h3 := mul_le_mul_of_nonneg_right h2 hTlL
    have h4 : ε' / (256 * π) * (T * l * (lam * l) ^ 2) ≤ ε' / 64 * (Nm - RN) * (lam * l) ^ 2 := by
      have e : ε' / (256 * π) * (T * l * (lam * l) ^ 2) = ε' / 64 * (T * l / (4 * π)) * (lam * l) ^ 2 := by
        field_simp; ring
      rw [e]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left hNlTl (by positivity)
    rw [hLl]
    linarith only [h1, h3, h4]
  have hPB : 4 * ((1 + 1 / (1 / l)) * PB) ≤ ε' / 64 * (Nm - RN) * (stdParams lam).L T ^ 2 := by
    have r := rPar
    rw [← hldef] at r
    rw [one_div_one_div, hPBdef, hLdef]
    have h4 : ε' / (256 * π) * (T * l * (lam * l) ^ 2) ≤ ε' / 64 * (Nm - RN) * (lam * l) ^ 2 := by
      have e : ε' / (256 * π) * (T * l * (lam * l) ^ 2) = ε' / 64 * (T * l / (4 * π)) * (lam * l) ^ 2 := by
        field_simp; ring
      rw [e]
      apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
      exact mul_le_mul_of_nonneg_left hNlTl (by positivity)
    exact r.trans h4
  have hlam10 : 0 < lam1 := by rw [hlam1', hLdef]; positivity
  have hlam1lo : lam / 4 ≤ lam1 := by
    rw [hlam1', hLdef, le_div_iff₀ hell0]
    have h1 : ell1q q T ≤ 4 * l := by linarith only [hell2, hlqT, hlo, hl1]
    nlinarith only [h1, h0]
  have hlam1hi : lam1 ≤ 2 := by
    rw [hlam1', hLdef, div_le_iff₀ hell0]
    nlinarith only [hell1, h2, hl0]
  have hc0 : 0 ≤ c := by rw [hcdef]; positivity
  have hcC : c ≤ C := by
    rw [hcdef, hCdef]
    have h1 : 1 / lam1 ≤ 4 / lam := by
      rw [div_le_div_iff₀ hlam10 h0]; linarith only [hlam1lo]
    have h3 : lam1 / 3 ≤ 1 := by linarith only [hlam1hi]
    have h4 : 4 / lam ≤ 6 / lam := div_le_div_of_nonneg_right (by norm_num) h0.le
    linarith only [h1, h3, h4]
  have hδC : 14 * δ * C ≤ ε' / 32 := by
    have h1 := mul_le_mul_of_nonneg_left hδε (by positivity : (0:ℝ) ≤ 14 * C)
    have e : 14 * C * (ε' / (448 * C)) = ε' / 32 := by field_simp; ring
    linarith only [h1, e]
  have hηδ : 1 / l ≤ δ := by
    rw [div_le_iff₀ hl0]
    rw [div_le_iff₀ hδ0] at hlogδ
    nlinarith only [hlogδ, hlo, hδ0]
  have hRN : C * RN ≤ ε' / 64 * (Nm - RN) := by
    have h1 : C * RN = C * A * lT := by rw [hRNdef]; ring
    have h2 : ε' / (512 * π) * T = ε' / 64 * (T / (8 * π)) := by field_simp; ring
    have h3 : T / (8 * π) ≤ Nm - RN := by
      have : T / (8 * π) ≤ T / (4 * π) := div_le_div_of_nonneg_left hT0.le (by positivity)
        (by linarith only [hπ])
      have h5 : T / (4 * π) ≤ T * l / (4 * π) := div_le_div_of_nonneg_right hTTl (by positivity)
      linarith only [this, h5, hNlTl]
    have h4 := mul_le_mul_of_nonneg_left h3 (by positivity : (0:ℝ) ≤ ε' / 64)
    linarith only [rRN2, h1, h2, h4]
  have hE : 8 * E ≤ ε' / 8 * (Nm - RN) := by
    rw [hEdef]
    have h1q : 1 + Real.log q ≤ 2 * lT := by linarith only [hlqT, hlog1]
    have h2' : 1 + lT + Real.sqrt ((stdParams lam).X T) ≤ 2 * lT + T ^ (lam / 2) := by
      linarith only [hsX, hlog1]
    have h3 : Ct * (1 + Real.log q) * (1 + lT + Real.sqrt ((stdParams lam).X T))
        ≤ Ct * (2 * lT) * (2 * lT + T ^ (lam / 2)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left h1q hCt) h2'
        (by linarith only [hlog1, Real.sqrt_nonneg ((stdParams lam).X T)]) (by positivity)
    have h4 : 32 * Ct * lT * lT ≤ ε' / (128 * π) * T * lT :=
      mul_le_mul_of_nonneg_right rE1 (by linarith only [hlog1])
    have h5 : 16 * Ct * T ^ (lam / 2) * lT ≤ ε' / (128 * π) * T * lT :=
      mul_le_mul_of_nonneg_right rE2 (by linarith only [hlog1])
    have h6 : ε' / (128 * π) * T * lT + ε' / (128 * π) * T * lT = ε' / 8 * (T * lT / (8 * π)) := by
      field_simp; ring
    have h7 := mul_le_mul_of_nonneg_left hNlT (by positivity : (0:ℝ) ≤ ε' / 8)
    have e : 8 * (Ct * (2 * lT) * (2 * lT + T ^ (lam / 2)))
        = 32 * Ct * lT * lT + 16 * Ct * T ^ (lam / 2) * lT := by ring
    linarith only [h3, h4, h5, h6, h7, e]
  have hNIIb : 3 * NIIb ≤ ε' / 8 * (Nm - RN) := by
    rw [hNIIbdef, Real.sqrt_eq_rpow]
    have h1q : 1 + Real.log q ≤ 2 * lT := by linarith only [hlqT, hlog1]
    have hl4 : Real.log (4 * T) ≤ 3 * lT := by
      rw [Real.log_mul (by norm_num) hT0.ne', ← hlTdef]
      have : Real.log 4 ≤ 2 := by
        have e : Real.log 4 = 2 * Real.log 2 := by
          rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        have := Real.log_two_lt_d9
        linarith only [this, e]
      linarith only [this, hlog1]
    have hl40 : 0 ≤ Real.log (4 * T) := Real.log_nonneg (by linarith only [hT4π, Real.pi_gt_three])
    have hu0 : 0 ≤ uniformA := zero_le_one.trans huA1
    have hTh : 0 ≤ T ^ (1 / 2 : ℝ) := by positivity
    have h3 : 3 * (uniformA * (1 + Real.log q)) * T ^ (1 / 2 : ℝ) * Real.log (4 * T)
        ≤ 3 * (uniformA * (2 * lT)) * T ^ (1 / 2 : ℝ) * (3 * lT) := by
      apply mul_le_mul _ hl4 hl40 (by positivity)
      apply mul_le_mul_of_nonneg_right _ hTh
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1q hu0) (by norm_num)
    have h4 : 54 * uniformA * lT * T ^ (1 / 2 : ℝ) * lT ≤ ε' / (64 * π) * T * lT :=
      mul_le_mul_of_nonneg_right rNII (by linarith only [hlog1])
    have h6 : ε' / (64 * π) * T * lT = ε' / 8 * (T * lT / (8 * π)) := by field_simp; ring
    have h7 := mul_le_mul_of_nonneg_left hNlT (by positivity : (0:ℝ) ≤ ε' / 8)
    have e : 3 * (3 * (uniformA * (2 * lT)) * T ^ (1 / 2 : ℝ) * (3 * lT))
        = 54 * uniformA * lT * T ^ (1 / 2 : ℝ) * lT := by ring
    linarith only [h3, h4, h6, h7, e]
  have hNl0 : 0 < Nm - RN := by linarith only [hNl1]
  have hNm0 : 0 ≤ Nm := by linarith only [hNl1, hRN0]
  have hNm2' := hNm2
  subst hNmdef
  have H := family_cell_at hPfam hq1 hprime hT300 hwL htrχ hRvMχ hNIIχ hθ hFr (δ := δ) haδ hη0 hηδ
    hm1 hmδ hδ0.le hδ1 hc0 hcC hNm2' hRN0 hRN hδC hK hMj0 hPB0 hMj hPB hNl0 hNm0 hε'0 hε'1 hE0 hE
    hNIIb hρB1 hr5 hr6
  have hsN : ∑ χ ∈ nontrivChars q, ((famZ hq1 χ).N T (2 * T) : ℝ)
      = ∑ χ ∈ nontrivChars q, (NcountL χ T (2 * T) : ℝ) :=
    Finset.sum_congr rfl fun χ hχ => by rw [famZ_N hq1 (hprim χ hχ)]
  have hsN0 : ∑ χ ∈ nontrivChars q, ((famZ hq1 χ).N0star T (2 * T) : ℝ)
      = ∑ χ ∈ nontrivChars q, (N0starL χ T (2 * T) : ℝ) :=
    Finset.sum_congr rfl fun χ hχ => by rw [famZ_N0star hq1 (hprim χ hχ)]
  rw [hsN, hsN0] at H
  have hH : Hfun (lam1q (stdParams lam) q T) = 2 - c := by
    rw [← hlam1, hcdef]; unfold Hfun; ring
  have hN0 : 0 ≤ ∑ χ ∈ nontrivChars q, (NcountL χ T (2 * T) : ℝ) :=
    Finset.sum_nonneg fun χ _ => Nat.cast_nonneg _
  rw [hH]
  have := mul_le_mul_of_nonneg_right (by linarith only [hε'ε] : 2 - c - ε ≤ 2 - c - ε') hN0
  linarith only [this, H]

end RHTower
