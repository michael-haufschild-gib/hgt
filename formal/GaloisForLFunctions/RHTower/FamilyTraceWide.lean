import GaloisForLFunctions.RHTower.ThmEUniformTrace
import GaloisForLFunctions.RHTower.FamilyTaperBridge

/-!
# The prime-side trace at any bandwidth, uniformly in the modulus

At a setting with bandwidth ratio `λ > 0` (no upper bound) and the taper facts `LocalHypsCoreW`, the
diagonal entries of the archimedean Gram matrix satisfy

`|Σ_{k<d} ∫ φ̂(r)² μ(τ_k + r) dr − a L² ∫_T^{2T} μ| ≤ d K (I₁ + I₂)/T + 4π C L l`

(increment bound for `μ` plus a monotone Riemann sum), and so

`|tr G̃ − a L N| ≤ C (1 + log q) L (1 + log T + √X)`             (`prop_trace_uniform_wide`)

whenever `|N − (T/2π) ℓ_{1,q}(T)| ≤ A log T`, with `C` and the threshold independent of `q`, of the
coefficients and of the bandwidth's upper range.  The modulus enters through the exact shift
`μ_q = μ_1 + (log q)/2π` (`trGtChiA_shift`), the coefficients through the explicit bound for the prime part.
-/

open MeasureTheory Real Set Zeta23 Zeta23.ThmE Zeta23.PrimeSide
open scoped ArithmeticFunction

noncomputable section

namespace RHTower

variable {cϱ : ℝ} {p : Setting} {F : LocalFun}

/-- The bookkeeping of the archimedean trace, as an inequality between real numbers. -/
theorem trace_comb {trG G M J a L d E C l lam Kc : ℝ} (hL : 0 < L) (hlam : 0 < lam)
    (htr : trG = L⁻¹ * G) (h1 : |G - 2 * π * a * L * M| ≤ d * E)
    (h2 : |2 * π * a * L * M - a * L ^ 2 * J| ≤ 4 * π * C * L * l)
    (t1 : d * E ≤ L * (Kc * L)) (hlL : l = L / lam) :
    |trG - a * L * J| ≤ (Kc + 4 * π * C / lam) * L := by
  have h3 := abs_add_le (G - 2 * π * a * L * M) (2 * π * a * L * M - a * L ^ 2 * J)
  have e' : G - 2 * π * a * L * M + (2 * π * a * L * M - a * L ^ 2 * J) = G - a * L ^ 2 * J := by
    ring
  rw [e'] at h3
  have e : 4 * π * C * L * l = L * (4 * π * C / lam * L) := by rw [hlL]; field_simp
  have hbound : |G - a * L ^ 2 * J| ≤ L * ((Kc + 4 * π * C / lam) * L) := by
    have : L * ((Kc + 4 * π * C / lam) * L) = L * (Kc * L) + L * (4 * π * C / lam * L) := by ring
    rw [this, ← e]
    linarith
  have e2 : trG - a * L * J = L⁻¹ * (G - a * L ^ 2 * J) := by
    rw [htr]; field_simp
  rw [e2, abs_mul, abs_of_pos (inv_pos.2 hL)]
  have h4 := mul_le_mul_of_nonneg_left hbound (le_of_lt (inv_pos.2 hL))
  rwa [← mul_assoc, inv_mul_cancel₀ hL.ne', one_mul] at h4

/-- The final assembly of the trace bound, as an inequality between real numbers. -/
theorem trace_final {tr a L J E N B Cμ A lgT : ℝ} (hcomb : |tr - a * L * J| ≤ B * L)
    (hJE : |J - E| ≤ |Cμ|) (hNE : |N - E| ≤ |A| * lgT) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hL : 0 ≤ L)
    (hlg : 0 ≤ lgT) (hB : 0 ≤ B) :
    |tr - a * L * N| ≤ (B + |Cμ| + |A|) * (L * (1 + lgT)) := by
  have h1 : |a * L * (J - E)| ≤ |Cμ| * L := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg ha0 hL)]
    have := mul_le_mul (mul_le_of_le_one_left hL ha1 |>.trans le_rfl) hJE (abs_nonneg _) hL
    nlinarith [abs_nonneg (J - E)]
  have h2 : |a * L * (E - N)| ≤ |A| * (L * lgT) := by
    rw [abs_mul, abs_of_nonneg (mul_nonneg ha0 hL), abs_sub_comm]
    have : a * L ≤ L := mul_le_of_le_one_left hL ha1
    have h3 := mul_le_mul this hNE (abs_nonneg _) hL
    nlinarith
  have e : tr - a * L * N = (tr - a * L * J) + a * L * (J - E) + a * L * (E - N) := by ring
  rw [e]
  have h4 := abs_add_three (tr - a * L * J) (a * L * (J - E)) (a * L * (E - N))
  have h5 : B * L + |Cμ| * L + |A| * (L * lgT) ≤ (B + |Cμ| + |A|) * (L * (1 + lgT)) := by
    have : 0 ≤ (B + |Cμ|) * (L * lgT) := by positivity
    have : 0 ≤ |A| * L := by positivity
    nlinarith
  linarith

/-- **The archimedean trace at any bandwidth, modulus one, fixed parity.** -/
theorem trace_mu_wide {κ : ℕ} (hκ : κ ≤ 1) {K Cml τ₀ Cμ A : ℝ} (hK0 : 0 ≤ K)
    (hK : ∀ t : ℝ, 2 ≤ t → ∀ r : ℝ, |muq κ 1 (t + r) - muq κ 1 t| ≤ K * (|r| + r ^ 2) / t)
    (hCml0 : 0 ≤ Cml) (hCml : ∀ τ ∈ Set.Icc p.T (2 * p.T), |muq κ 1 τ| ≤ Cml * Zeta23.l p.T)
    (hτ₀ : ∀ x, τ₀ ≤ x → 0 ≤ muq κ 1 x)
    (hCμ : |(∫ τ in p.T..(2 * p.T), muq κ 1 τ) - p.T * ell1q 1 p.T / (2 * π)| ≤ Cμ / p.T)
    (hF : LocalHypsCoreW cϱ p F) (hT4 : 4 ≤ p.T) (hTτ : τ₀ + 1 ≤ p.T) (N : ℝ)
    (hN : |N - p.T / (2 * π) * ell1q 1 p.T| ≤ A * Real.log p.T) :
    |trGtChiA κ 1 (fun _ => 0) p F - F.a * p.L * N|
      ≤ (K * (16 + 2 * cϱ + 2 * cϱ ^ 2) + 4 * π * Cml / p.lam + |Cμ| + |A|)
          * (p.L * (1 + Real.log p.T)) := by
  have hΓ := GammaChi.gammaFactsChi (q := 1) hκ le_rfl
  have hT0 : (0:ℝ) < p.T := by linarith
  have hL := hF.L_pos
  have hL8 := hF.eight_le_L
  have hc4 := hF.four_le_cϱ
  have hc0 : (0:ℝ) ≤ cϱ := by linarith
  have hlam0 := hF.lam_pos
  have hh0 : 0 < p.h := by simp only [Setting.h]; positivity
  have hl1 : (1:ℝ) ≤ Zeta23.l p.T := hF.one_le_l
  have ha1 := hF.a_le_one
  have ha0 := hF.a_pos.le
  have hlogT0 : 0 ≤ Real.log p.T := Real.log_nonneg (by linarith)
  set I₁ := ∫ r, F.phiHat r ^ 2 * |r| with hI₁def
  set I₂ := ∫ r, F.phiHat r ^ 2 * r ^ 2 with hI₂def
  have hI₁0 : 0 ≤ I₁ := MeasureTheory.integral_nonneg fun r => by positivity
  have hI₂0 : 0 ≤ I₂ := MeasureTheory.integral_nonneg fun r => by positivity
  have hI₁ : I₁ ≤ 8 + 2 * cϱ * p.L := by
    refine hF.integral_phiHat_sq_mul_abs_le.trans ?_
    have h1 : Real.log (cϱ * p.L / (4 * p.w)) ≤ cϱ * p.L / (4 * p.w) :=
      Real.log_le_self (by have := hF.one_le_w; positivity)
    have h2 : cϱ * p.L / (4 * p.w) ≤ cϱ * p.L / 4 := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
      linarith [hF.one_le_w]
    linarith
  have hI₂ : I₂ ≤ 8 + 2 * cϱ ^ 2 := by
    refine hF.integral_phiHat_sq_mul_sq_le.trans ?_
    have h3 : (cϱ / p.w) ^ 2 ≤ cϱ ^ 2 := by
      rw [div_pow]
      exact div_le_self (sq_nonneg _) (by nlinarith [hF.one_le_w])
    linarith
  have hτg : ∀ k ∈ Finset.range p.d, p.T ≤ p.tau k ∧ p.tau k ≤ 2 * p.T := fun k hk =>
    p.tau_mem hL hT0.le hk
  -- the diagonal entries are the archimedean parts
  have hdiag : ∀ k ∈ Finset.range p.d, GentryChiA κ 1 (fun _ => 0) p F k k
      = ∫ r, F.phiHat r ^ 2 * muq κ 1 (p.tau k + r) := by
    intro k hk
    rw [GentryChiA_diag_eq hΓ le_rfl hF coeffOK_one_zero k (by linarith [(hτg k hk).1])]
    simp only [PXc_zero, mul_zero, integral_zero, add_zero]
  have h1 : |∑ k ∈ Finset.range p.d, GentryChiA κ 1 (fun _ => 0) p F k k
      - 2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, muq κ 1 (p.tau k)|
      ≤ p.d * (K * (I₁ + I₂) / p.T) := by
    rw [Finset.sum_congr rfl hdiag, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hbd : ∀ k ∈ Finset.range p.d, |(∫ r, F.phiHat r ^ 2 * muq κ 1 (p.tau k + r))
        - 2 * π * F.a * p.L * muq κ 1 (p.tau k)| ≤ K * (I₁ + I₂) / p.T := by
      intro k hk
      have ht2 : 2 ≤ p.tau k := by linarith [(hτg k hk).1]
      refine (muq_part_bound hΓ le_rfl hF hK0 hK ht2).trans ?_
      exact div_le_div_of_nonneg_left (by positivity) hT0 (hτg k hk).1
    refine (Finset.sum_le_sum hbd).trans ?_
    rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have hhT : p.h ≤ p.T := by
    simp only [Setting.h]; rw [div_le_iff₀ hL]; nlinarith [Real.pi_lt_four]
  have h2 : |2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, muq κ 1 (p.tau k)
      - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), muq κ 1 τ|
      ≤ 4 * π * Cml * p.L * Zeta23.l p.T := by
    have hR := riemann_sum_monotone (μ := muq κ 1) (T := p.T) hh0 hhT
      (hΓ.monotoneOn.mono (fun x hx => by
        simp only [Set.mem_Ici] at hx ⊢
        have : (0:ℝ) < p.h := hh0
        have hh1 : p.h ≤ 1 := by
          simp only [Setting.h]; rw [div_le_one hL]; nlinarith [Real.pi_lt_four]
        linarith))
      (fun x hx => hτ₀ x (by
        have hh1 : p.h ≤ 1 := by
          simp only [Setting.h]; rw [div_le_one hL]; nlinarith [Real.pi_lt_four]
        linarith))
    rw [← p.d_eq_floor hL] at hR
    have hsum2 : ∑ k ∈ Finset.range p.d, muq κ 1 (p.tau k)
        = ∑ k ∈ Finset.range p.d, muq κ 1 (p.T + k * p.h) :=
      Finset.sum_congr rfl fun k _ => by rw [Setting.tau_natCast]
    rw [hsum2]
    have hid : 2 * π * F.a * p.L * ∑ k ∈ Finset.range p.d, muq κ 1 (p.T + k * p.h)
        - F.a * p.L ^ 2 * ∫ τ in p.T..(2 * p.T), muq κ 1 τ
        = F.a * p.L ^ 2 * (p.h * ∑ k ∈ Finset.range p.d, muq κ 1 (p.T + k * p.h)
            - ∫ τ in p.T..(2 * p.T), muq κ 1 τ) := by
      simp only [Setting.h]; field_simp
    rw [hid, abs_mul, abs_of_nonneg (by positivity)]
    have hμ2T : muq κ 1 (2 * p.T) ≤ Cml * Zeta23.l p.T :=
      (le_abs_self _).trans (hCml (2 * p.T) ⟨by linarith, le_rfl⟩)
    have hμ2T0 : 0 ≤ muq κ 1 (2 * p.T) := hτ₀ _ (by linarith)
    calc F.a * p.L ^ 2 * |p.h * ∑ k ∈ Finset.range p.d, muq κ 1 (p.T + k * p.h)
          - ∫ τ in p.T..(2 * p.T), muq κ 1 τ|
        ≤ F.a * p.L ^ 2 * (2 * p.h * muq κ 1 (2 * p.T)) := by gcongr
      _ ≤ 1 * p.L ^ 2 * (2 * p.h * (Cml * Zeta23.l p.T)) := by gcongr
      _ = 4 * π * Cml * p.L * Zeta23.l p.T := by
          simp only [Setting.h]; field_simp; ring
  -- assemble
  have hd : (p.d : ℝ) ≤ p.L * p.T / (2 * π) := p.d_le (by positivity)
  have hπ1 : (1:ℝ) ≤ 2 * π := by nlinarith [Real.pi_gt_three]
  have t1 : (p.d : ℝ) * (K * (I₁ + I₂) / p.T) ≤ p.L * (K * (16 + 2 * cϱ + 2 * cϱ ^ 2) * p.L) := by
    have e1 : (p.d : ℝ) * (K * (I₁ + I₂) / p.T) ≤ p.L * p.T / (2 * π) * (K * (I₁ + I₂) / p.T) := by
      gcongr
    have e2 : p.L * p.T / (2 * π) * (K * (I₁ + I₂) / p.T) = p.L * (K * (I₁ + I₂)) / (2 * π) := by
      field_simp
    have e3 : I₁ + I₂ ≤ (16 + 2 * cϱ + 2 * cϱ ^ 2) * p.L := by
      have u1 : (16:ℝ) ≤ 16 * p.L := by nlinarith
      have u3 : 2 * cϱ ^ 2 ≤ 2 * cϱ ^ 2 * p.L := by nlinarith [sq_nonneg cϱ]
      nlinarith
    calc (p.d : ℝ) * (K * (I₁ + I₂) / p.T) ≤ p.L * (K * (I₁ + I₂)) / (2 * π) := by
          rw [← e2]; exact e1
      _ ≤ p.L * (K * (I₁ + I₂)) := div_le_self (by positivity) hπ1
      _ ≤ p.L * (K * ((16 + 2 * cϱ + 2 * cϱ ^ 2) * p.L)) := by gcongr
      _ = p.L * (K * (16 + 2 * cϱ + 2 * cϱ ^ 2) * p.L) := by ring
  have hlL : Zeta23.l p.T = p.L / p.lam := by
    rw [show p.L = p.lam * Zeta23.l p.T from rfl]; field_simp
  have hcomb : |trGtChiA κ 1 (fun _ => 0) p F - F.a * p.L * ∫ τ in p.T..(2 * p.T), muq κ 1 τ|
      ≤ (K * (16 + 2 * cϱ + 2 * cϱ ^ 2) + 4 * π * Cml / p.lam) * p.L := by
    have htr : trGtChiA κ 1 (fun _ => 0) p F
        = p.L⁻¹ * ∑ k ∈ Finset.range p.d, GentryChiA κ 1 (fun _ => 0) p F k k := by
      simp only [trGtChiA]
      rw [Fin.sum_univ_eq_sum_range (fun k => GentryChiA κ 1 (fun _ => 0) p F k k)]
    exact trace_comb hL hlam0 htr h1 h2 t1 hlL
  have hT1 : (1:ℝ) ≤ p.T := by linarith
  -- atoms
  obtain ⟨J, hJ⟩ : ∃ x : ℝ, x = ∫ τ in p.T..(2 * p.T), muq κ 1 τ := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ x : ℝ, x = p.T * ell1q 1 p.T / (2 * π) := ⟨_, rfl⟩
  obtain ⟨tr, htrdef⟩ : ∃ x : ℝ, x = trGtChiA κ 1 (fun _ => 0) p F := ⟨_, rfl⟩
  rw [← hJ, ← htrdef] at hcomb
  rw [← hJ, ← hE] at hCμ
  have hNE : |N - E| ≤ |A| * Real.log p.T := by
    rw [hE, show p.T * ell1q 1 p.T / (2 * π) = p.T / (2 * π) * ell1q 1 p.T by ring]
    exact hN.trans (mul_le_mul_of_nonneg_right (le_abs_self A) hlogT0)
  have hJE : |J - E| ≤ |Cμ| := by
    refine hCμ.trans ?_
    calc Cμ / p.T ≤ |Cμ| / p.T := div_le_div_of_nonneg_right (le_abs_self _) hT0.le
      _ ≤ |Cμ| := div_le_self (abs_nonneg _) hT1
  rw [← htrdef]
  exact trace_final hcomb hJE hNE ha0 ha1 hL.le hlogT0 (by positivity)


/-- The three-part bookkeeping of the uniform trace bound. -/
theorem trace_uniform_combine {x y z Cb lq W S : ℝ} (hlq : 0 ≤ lq) (hW1 : 1 ≤ W) (hCb : 0 ≤ Cb)
    (hx : |x| ≤ Cb * W) (hy : |y| ≤ lq) (hz : |z| ≤ 3 / Real.log 2 * S) (hSW : S ≤ W) :
    |x + y + z| ≤ (Cb + 1 + 3 / Real.log 2) * (1 + lq) * W := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have h3 := abs_add_three x y z
  have hW0 : 0 ≤ W := by linarith
  have hz' : |z| ≤ 3 / Real.log 2 * W := hz.trans (mul_le_mul_of_nonneg_left hSW (by positivity))
  have hy' : |y| ≤ lq * W := hy.trans (le_mul_of_one_le_right hlq hW1)
  have e : (Cb + 1 + 3 / Real.log 2) * (1 + lq) * W
      = Cb * W + lq * W + 3 / Real.log 2 * W
        + (Cb * lq * W + W + 3 / Real.log 2 * lq * W) := by ring
  have hrest : 0 ≤ Cb * lq * W + W + 3 / Real.log 2 * lq * W := by positivity
  linarith

variable (cϱ) in
/-- **[prop:trace] for `L(s, χ)` at any bandwidth, uniformly in the modulus and the coefficients.** -/
theorem prop_trace_uniform_wide {lam : ℝ} (hlam : 0 < lam) (A : ℝ) :
    ∃ C T₀ : ℝ, 0 ≤ C ∧ ∀ κ q : ℕ, κ ≤ 1 → 1 ≤ q → ∀ c : ℕ → ℂ, CoeffOK q c →
      ∀ (p : Setting) (F : LocalFun), p.lam = lam → T₀ ≤ p.T → LocalHypsCoreW cϱ p F →
      ∀ N : ℝ, |N - p.T / (2 * π) * ell1q q p.T| ≤ A * Real.log p.T →
        |trGtChiA κ q c p F - F.a * p.L * N|
          ≤ C * (1 + Real.log q) * (p.L * (1 + Real.log p.T + Real.sqrt p.X)) := by
  have hΓ0 := GammaChi.gammaFactsChi (κ := 0) (q := 1) (by norm_num) le_rfl
  have hΓ1 := GammaChi.gammaFactsChi (κ := 1) (q := 1) le_rfl le_rfl
  obtain ⟨K0, hK00, hK0⟩ := muq_increment_bound hΓ0 le_rfl
  obtain ⟨K1, hK10, hK1⟩ := muq_increment_bound hΓ1 le_rfl
  obtain ⟨Cm0, Tm0, hCm00, hCm0⟩ := muq_abs_le 0 1 hΓ0 le_rfl
  obtain ⟨Cm1, Tm1, hCm10, hCm1⟩ := muq_abs_le 1 1 hΓ1 le_rfl
  obtain ⟨τ0, -, hτ0⟩ := muq_nonneg_eventually hΓ0 le_rfl
  obtain ⟨τ1, -, hτ1⟩ := muq_nonneg_eventually hΓ1 le_rfl
  obtain ⟨Cu0, Tu0, hCu0⟩ := hΓ0.int_mu
  obtain ⟨Cu1, Tu1, hCu1⟩ := hΓ1.int_mu
  obtain ⟨x₀, hx₀⟩ := Cheb.chebyshevMertens.cheb1b
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  obtain ⟨Cb, hCbdef⟩ : ∃ x : ℝ, x = (K0 + K1) * (16 + 2 * cϱ + 2 * cϱ ^ 2) * 1
      + 4 * π * (Cm0 + Cm1) / lam + |Cu0| + |Cu1| + |A| := ⟨_, rfl⟩
  refine ⟨|Cb| + 1 + 3 / Real.log 2,
    max (max (max (max Tm0 Tm1) (max Tu0 Tu1)) (max (τ0 + 1) (τ1 + 1)))
      (max (2 * π * Real.exp (|x₀| / lam)) 4), by positivity,
    fun κ q hκ hq c hc p F hp hT hF N hN => ?_⟩
  have hTa := (le_max_left _ _).trans hT
  have hTb := (le_max_right _ _).trans hT
  have hTx : 2 * π * Real.exp (|x₀| / lam) ≤ p.T := (le_max_left _ _).trans hTb
  have hT4 : 4 ≤ p.T := (le_max_right _ _).trans hTb
  have hT0 : 0 < p.T := by linarith
  have hL : 0 < p.L := hF.L_pos
  have hlam0 : 0 < p.lam := hp ▸ hlam
  have hX : x₀ ≤ p.X := Setting.le_X_of_T hlam0 (by rw [hp]; exact hTx)
  have hX1 : 1 ≤ Real.sqrt p.X := by
    rw [Real.le_sqrt' one_pos, one_pow]; exact Real.one_le_exp hL.le
  have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq)
  have hlogT : 0 ≤ Real.log p.T := Real.log_nonneg (by linarith)
  have ha0 : 0 ≤ F.a := hF.a_pos.le
  have ha1 : F.a ≤ 1 := hF.a_le_one
  have hc4 := hF.four_le_cϱ
  set W := p.L * (1 + Real.log p.T + Real.sqrt p.X) with hWdef
  have hW1 : 1 ≤ W := by
    have h8 := hF.eight_le_L
    have : 1 ≤ 1 + Real.log p.T + Real.sqrt p.X := by linarith
    nlinarith
  -- the modulus-one data
  set N₁ := N - p.T * (Real.log q / (2 * π)) with hN₁
  have hN₁b : |N₁ - p.T / (2 * π) * ell1q 1 p.T| ≤ A * Real.log p.T := by
    have hell : ell1q q p.T = ell1q 1 p.T + Real.log q := by
      unfold ell1q
      rw [Nat.cast_one, one_mul, mul_div_assoc, Real.log_mul (by exact_mod_cast (show q ≠ 0 by omega))
        (by positivity)]
      ring
    have : N₁ - p.T / (2 * π) * ell1q 1 p.T = N - p.T / (2 * π) * ell1q q p.T := by
      rw [hN₁, hell]; field_simp; ring
    rwa [this]
  have hbase : |trGtChiA κ 1 (fun _ => 0) p F - F.a * p.L * N₁| ≤ |Cb| * W := by
    have hW' : p.L * (1 + Real.log p.T) ≤ W := by
      rw [hWdef]; exact mul_le_mul_of_nonneg_left (by linarith [Real.sqrt_nonneg p.X]) hL.le
    have hPW : 0 ≤ p.L * (1 + Real.log p.T) := by positivity
    interval_cases κ
    · have h := trace_mu_wide (le_refl 0 |>.trans (by norm_num)) hK00 hK0 hCm00.le
        (hCm0 p (le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
          (le_max_left _ _))) hTa)) hτ0
        (hCu0 p.T (le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
          (le_max_left _ _))) hTa)) hF hT4
        (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hTa) N₁ hN₁b
      refine h.trans ?_
      rw [hp]
      have hk : K0 * (16 + 2 * cϱ + 2 * cϱ ^ 2) + 4 * π * Cm0 / lam + |Cu0| + |A| ≤ |Cb| := by
        refine le_trans ?_ (le_abs_self _)
        rw [hCbdef]
        have h₁ : 0 ≤ K1 * (16 + 2 * cϱ + 2 * cϱ ^ 2) := by positivity
        have h₂ : 4 * π * Cm0 / lam ≤ 4 * π * (Cm0 + Cm1) / lam := by
          apply div_le_div_of_nonneg_right _ hlam.le; nlinarith only [Real.pi_pos, hCm10]
        linarith only [h₁, h₂, abs_nonneg Cu1]
      exact (mul_le_mul_of_nonneg_right hk hPW).trans (mul_le_mul_of_nonneg_left hW' (abs_nonneg _))
    · have h := trace_mu_wide (le_refl 1) hK10 hK1 hCm10.le
        (hCm1 p (le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
          (le_max_left _ _))) hTa)) hτ1
        (hCu1 p.T (le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
          (le_max_left _ _))) hTa)) hF hT4
        (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hTa) N₁ hN₁b
      refine h.trans ?_
      rw [hp]
      have hk : K1 * (16 + 2 * cϱ + 2 * cϱ ^ 2) + 4 * π * Cm1 / lam + |Cu1| + |A| ≤ |Cb| := by
        refine le_trans ?_ (le_abs_self _)
        rw [hCbdef]
        have h₁ : 0 ≤ K0 * (16 + 2 * cϱ + 2 * cϱ ^ 2) := by positivity
        have h₂ : 4 * π * Cm1 / lam ≤ 4 * π * (Cm0 + Cm1) / lam := by
          apply div_le_div_of_nonneg_right _ hlam.le; nlinarith only [Real.pi_pos, hCm00]
        linarith only [h₁, h₂, abs_nonneg Cu0]
      exact (mul_le_mul_of_nonneg_right hk hPW).trans (mul_le_mul_of_nonneg_left hW' (abs_nonneg _))
  -- the shift term
  have hshift : |2 * π * F.a * p.d * (Real.log q / (2 * π)) - F.a * p.L * (p.T * (Real.log q / (2 * π)))|
      ≤ Real.log q := by
    have h := abs_two_pi_d_sub_le hL hT0 ha0
    have hc0 : 0 ≤ Real.log q / (2 * π) := div_nonneg hlq (by positivity)
    have e : 2 * π * F.a * p.d * (Real.log q / (2 * π)) - F.a * p.L * (p.T * (Real.log q / (2 * π)))
        = (2 * π * F.a * p.d - F.a * p.L * p.T) * (Real.log q / (2 * π)) := by ring
    rw [e, abs_mul, abs_of_nonneg hc0]
    calc |2 * π * F.a * p.d - F.a * p.L * p.T| * (Real.log q / (2 * π))
        ≤ 2 * π * F.a * (Real.log q / (2 * π)) := mul_le_mul_of_nonneg_right h hc0
      _ = F.a * Real.log q := by field_simp
      _ ≤ 1 * Real.log q := mul_le_mul_of_nonneg_right ha1 hlq
      _ = Real.log q := one_mul _
  -- the prime part
  have hP : |(p.L)⁻¹ * ∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * PXc c p.X (p.tau k + r)|
      ≤ 3 / Real.log 2 * (p.L * Real.sqrt p.X) := by
    have h := sum_P_part_chi_bound hF hc
    have hconv : ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, (Λ n : ℝ) * (n : ℝ) ^ (-(1/2 : ℝ))
        = ∑ n ∈ Finset.Ioc 0 ⌊p.X⌋₊, Λ n / Real.sqrt n := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Real.rpow_neg (Nat.cast_nonneg n), ← Real.sqrt_eq_rpow, div_eq_mul_inv]
    rw [hconv] at h
    have h3 := hx₀ p.X hX
    rw [abs_mul, abs_of_pos (inv_pos.mpr hL)]
    calc (p.L)⁻¹ * |∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * PXc c p.X (p.tau k + r)|
        ≤ (p.L)⁻¹ * (p.L ^ 2 / Real.log 2 * (3 * Real.sqrt p.X)) := by
          refine mul_le_mul_of_nonneg_left (h.trans ?_) (by positivity)
          exact mul_le_mul_of_nonneg_left h3 (by positivity)
      _ = 3 / Real.log 2 * (p.L * Real.sqrt p.X) := by field_simp
  have hSW : p.L * Real.sqrt p.X ≤ W := by
    rw [hWdef]; exact mul_le_mul_of_nonneg_left (by linarith) hL.le
  rw [trGtChiA_shift hκ hq hc hF hT0]
  have hsplit : trGtChiA κ 1 (fun _ => 0) p F + 2 * π * F.a * p.d * (Real.log q / (2 * π))
        + (p.L)⁻¹ * (∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * PXc c p.X (p.tau k + r))
        - F.a * p.L * N
      = (trGtChiA κ 1 (fun _ => 0) p F - F.a * p.L * N₁)
        + (2 * π * F.a * p.d * (Real.log q / (2 * π)) - F.a * p.L * (p.T * (Real.log q / (2 * π))))
        + (p.L)⁻¹ * ∑ k ∈ Finset.range p.d, ∫ r, F.phiHat r ^ 2 * PXc c p.X (p.tau k + r) := by
    rw [hN₁]; ring
  refine (le_of_eq (congrArg abs hsplit)).trans ?_
  exact trace_uniform_combine hlq hW1 (abs_nonneg _) hbase hshift hP hSW

end RHTower
