import GaloisForLFunctions.RHTower.FamilyZeroSide

/-!
# The summed rank–trace certificate for the characters modulo a prime

Let `q` be prime and `s` the set of nontrivial characters modulo `q`.  At any bandwidth (`ParamsValidFam`) and
any height `T ≥ 300` with `8w ≤ L`, if every trace is within `L·E` of `aL N_χ` and the summed prime-side traces
of `G̃²_χ` are at most `Fr`, then (`family_seam_at`)

`4(N − |s| E/a) − Fr/(aL)² − 2N − 3 ∑ N_II,χ − b(4|s| + 2(|s| Fr/(aL)²)^{1/2} + |s| b) ≤ ∑ N₀*_χ`,

with `N = ∑ N_χ` and `b = θ₀/(aL)`, `θ₀` the tail parameter for the modulus-uniform local count.

A purely real-variable error budget (`family_budget`) turns this into `(2 − c − ε) N ≤ ∑ N₀*_χ` once
`Fr/(aL)² ≤ cN + (ε/8)|s| N_low`, the trace and `N_II` errors are below `(ε/8)|s| N_low`, and the tail is small;
`N_low` is any per-character lower bound for `N_χ`.
-/

open MeasureTheory Real Set Zeta23 Zeta23.ThmE Zeta23.PrimeSide Zeta23.Assembly RHLinalg

noncomputable section

namespace RHTower

/-- **The family error budget.** -/
theorem family_budget {N Nl m R Φ NIIs b ρB c C ε : ℝ}
    (hm : 0 < m) (hNl : 0 < Nl) (hN : m * Nl ≤ N) (hc : c ≤ C)
    (hR : 4 * R ≤ ε / 8 * (m * Nl)) (hNII : 3 * NIIs ≤ ε / 8 * (m * Nl))
    (hΦ : Φ ≤ c * N + ε / 8 * (m * Nl)) (hΦ0 : 0 ≤ Φ)
    (hb0 : 0 ≤ b) (hb : b ≤ ρB) (hρB1 : ρB ≤ 1) (hr5 : 5 * ρB ≤ ε / 8 * Nl)
    (hr6 : 2 * ρB * Real.sqrt (C + 1) ≤ ε / 8 * Real.sqrt Nl) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    (2 - c - ε) * N
      ≤ 4 * (N - R) - Φ - 2 * N - 3 * NIIs - b * (4 * m + 2 * Real.sqrt (m * Φ) + m * b) := by
  have hmN : 0 < m * Nl := mul_pos hm hNl
  have hN0 : 0 < N := lt_of_lt_of_le hmN hN
  have hε8 : ε / 8 * (m * Nl) ≤ ε / 8 * N := mul_le_mul_of_nonneg_left hN (by positivity)
  have hρB0 : 0 ≤ ρB := hb0.trans hb
  -- the tail terms linear in `b`
  have hbb : b * b ≤ ρB := by
    calc b * b ≤ ρB * 1 := mul_le_mul hb (hb.trans hρB1) hb0 hρB0
      _ = ρB := mul_one _
  have hlin : b * (4 * m + m * b) ≤ ε / 8 * N := by
    have h1 : b * (4 * m + m * b) = m * (4 * b + b * b) := by ring
    have h2 : 4 * b + b * b ≤ 5 * ρB := by linarith
    have h3 : m * (4 * b + b * b) ≤ m * (ε / 8 * Nl) :=
      mul_le_mul_of_nonneg_left (h2.trans hr5) hm.le
    have h4 : m * (ε / 8 * Nl) = ε / 8 * (m * Nl) := by ring
    linarith
  -- the square-root tail term
  have hΦC : Φ ≤ (C + 1) * N := by
    have h1 : c * N ≤ C * N := mul_le_mul_of_nonneg_right hc hN0.le
    have h2 : ε / 8 * N ≤ N := by
      have : ε / 8 ≤ 1 := by linarith
      calc ε / 8 * N ≤ 1 * N := mul_le_mul_of_nonneg_right this hN0.le
        _ = N := one_mul N
    linarith
  have hC1 : 0 ≤ C + 1 := by
    have : 0 ≤ (C + 1) * N := hΦ0.trans hΦC
    by_contra h
    have : (C + 1) * N < 0 := mul_neg_of_neg_of_pos (not_le.mp h) hN0
    linarith
  have hsq : Real.sqrt (m * Φ) ≤ Real.sqrt (C + 1) * (Real.sqrt m * Real.sqrt N) := by
    rw [← Real.sqrt_mul hm.le, ← Real.sqrt_mul hC1]
    apply Real.sqrt_le_sqrt
    calc m * Φ ≤ m * ((C + 1) * N) := mul_le_mul_of_nonneg_left hΦC hm.le
      _ = (C + 1) * (m * N) := by ring
  have hmNl : Real.sqrt Nl * (Real.sqrt m * Real.sqrt N) ≤ N := by
    have e : Real.sqrt Nl * (Real.sqrt m * Real.sqrt N) = Real.sqrt (m * Nl) * Real.sqrt N := by
      rw [Real.sqrt_mul hm.le]; ring
    rw [e]
    calc Real.sqrt (m * Nl) * Real.sqrt N ≤ Real.sqrt N * Real.sqrt N :=
          mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hN) (Real.sqrt_nonneg _)
      _ = N := Real.mul_self_sqrt hN0.le
  have hroot : b * (2 * Real.sqrt (m * Φ)) ≤ ε / 8 * N := by
    have hs0 : 0 ≤ Real.sqrt (m * Φ) := Real.sqrt_nonneg _
    have hmN' : 0 ≤ Real.sqrt m * Real.sqrt N := by positivity
    calc b * (2 * Real.sqrt (m * Φ))
        ≤ ρB * (2 * (Real.sqrt (C + 1) * (Real.sqrt m * Real.sqrt N))) :=
          mul_le_mul hb (by linarith) (by positivity) hρB0
      _ = (2 * ρB * Real.sqrt (C + 1)) * (Real.sqrt m * Real.sqrt N) := by ring
      _ ≤ (ε / 8 * Real.sqrt Nl) * (Real.sqrt m * Real.sqrt N) :=
          mul_le_mul_of_nonneg_right hr6 hmN'
      _ = ε / 8 * (Real.sqrt Nl * (Real.sqrt m * Real.sqrt N)) := by ring
      _ ≤ ε / 8 * N := mul_le_mul_of_nonneg_left hmNl (by positivity)
  have e : b * (4 * m + 2 * Real.sqrt (m * Φ) + m * b)
      = b * (4 * m + m * b) + b * (2 * Real.sqrt (m * Φ)) := by ring
  rw [e]
  have hεN : ε / 8 * N * 5 ≤ ε * N := by nlinarith
  nlinarith

/-- The nontrivial characters modulo `q`. -/
abbrev nontrivChars (q : ℕ) [NeZero q] : Finset (DirichletCharacter ℂ q) :=
  (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1)

theorem card_nontrivChars {q : ℕ} [NeZero q] :
    ((nontrivChars q).card : ℝ) = (q.totient : ℝ) - 1 := by
  have h := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (DirichletCharacter ℂ q))) (fun χ => χ ≠ 1)
  have h1 : ((Finset.univ : Finset (DirichletCharacter ℂ q)).filter (fun χ => ¬ χ ≠ 1)).card = 1 := by
    rw [Finset.card_eq_one]
    exact ⟨1, by ext χ; simp⟩
  rw [h1] at h
  have hc : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Finset.card_univ]; exact card_dirichletCharacter q
  have : (nontrivChars q).card + 1 = q.totient := by rw [← hc]; exact h
  have h' : ((nontrivChars q).card : ℝ) + 1 = q.totient := by exact_mod_cast this
  linarith

theorem famZ_N {q : ℕ} [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q} (h : χ.IsPrimitive)
    (T₁ T₂ : ℝ) : (famZ hq χ).N T₁ T₂ = NcountL χ T₁ T₂ := by
  rw [famZ_of_prim hq h, LZeros_N]

theorem famZ_N0star {q : ℕ} [NeZero q] (hq : 1 < q) {χ : DirichletCharacter ℂ q} (h : χ.IsPrimitive)
    (T₁ T₂ : ℝ) : (famZ hq χ).N0star T₁ T₂ = N0starL χ T₁ T₂ := by
  rw [famZ_of_prim hq h, LZeros_N0star]

variable {P : Params} {T : ℝ}

/-- **The summed seam at one height.** -/
theorem family_seam_at (hP : ParamsValidFam P) {q : ℕ} [NeZero q] (hq : 1 < q) (hprime : q.Prime)
    (hT300 : Tail.T₀ ≤ T) (hwL : 8 * P.w ≤ P.L T) {E Fr : ℝ}
    (htr : ∀ χ ∈ nontrivChars q,
      |trGtChiA (parity χ) q (coeff χ) (P.toSetting T) (P.localFun T)
        - P.a T * P.L T * ((famZ hq χ).N T (2 * T) : ℝ)| ≤ P.L T * E)
    (hFr : ∑ χ ∈ nontrivChars q, trGt2ChiA (parity χ) q (coeff χ) (P.toSetting T) (P.localFun T) ≤ Fr) :
    4 * (∑ χ ∈ nontrivChars q, ((famZ hq χ).N T (2 * T) : ℝ) - (nontrivChars q).card * (E / P.a T))
      - ((P.a T * P.L T)⁻¹) ^ 2 * Fr - 2 * ∑ χ ∈ nontrivChars q, ((famZ hq χ).N T (2 * T) : ℝ)
      - 3 * ∑ χ ∈ nontrivChars q, (NII (famZ hq χ) T : ℝ)
      - Tail.theta0 (uniformA * (1 + Real.log q)) (Real.exp (P.L T / 4) * P.C1 T) T
          / (P.a T * P.L T) * (4 * (nontrivChars q).card
            + 2 * Real.sqrt ((nontrivChars q).card * (((P.a T * P.L T)⁻¹) ^ 2 * Fr))
            + (nontrivChars q).card
              * (Tail.theta0 (uniformA * (1 + Real.log q)) (Real.exp (P.L T / 4) * P.C1 T) T
                / (P.a T * P.L T)))
      ≤ ∑ χ ∈ nontrivChars q, ((famZ hq χ).N0star T (2 * T) : ℝ) := by
  have hT3 : (300:ℝ) ≤ T := hT300
  have hT0 : 0 < T := by linarith
  have hL8 : 8 ≤ P.L T := by have := hP.one_le_w; linarith
  have hL : 0 < P.L T := by linarith
  have ha : 0 < P.a T := lt_of_lt_of_le (by norm_num) (half_le_a_fam hP hwL)
  have hprim : ∀ χ ∈ nontrivChars q, χ.IsPrimitive := fun χ hχ =>
    isPrimitive_of_prime hprime χ (Finset.mem_filter.mp hχ).2
  have hB : ∀ χ ∈ nontrivChars q, BlockInputs (famZ hq χ) P T := fun χ _ =>
    ZeroSide.blockInputsAt (famZ hq χ) P T (fun z => GzGp.phiHat_conj P T z)
      (fun r => GzGp.phiHat_ofReal P T r) (poissonSq_fam hP hwL) hL (by positivity)
  have hA₀ : (1 : ℝ) ≤ uniformA * (1 + Real.log q) := by
    have hlq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq.le)
    exact one_le_mul_of_one_le_of_one_le one_le_uniformLocalCountConst (by linarith)
  have hTl : ∀ χ ∈ nontrivChars q, TailInputs (famZ hq χ) P T
      (Tail.theta0 (uniformA * (1 + Real.log q)) (Real.exp (P.L T / 4) * P.C1 T) T) := by
    intro χ hχ
    refine tailInputs_fam (famZ hq χ) hP hA₀ (fun t => ?_) hT300 (by linarith) hwL
    rw [famZ_N hq (hprim χ hχ)]
    exact uniform_localCount_log hq (hprim χ hχ) t
  have hθ₀ : 0 ≤ Tail.theta0 (uniformA * (1 + Real.log q)) (Real.exp (P.L T / 4) * P.C1 T) T :=
    div_nonneg (mul_nonneg (by positivity) (Real.log_nonneg (by linarith))) hT0.le
  refine family_seamA (nontrivChars q) (famZ hq) P hT0.le hB hθ₀ hTl ha hL rfl ?_ ?_
  · have h := Finset.sum_le_sum fun χ hχ =>
      rtrace_hat_ge_fam hq (hprim χ hχ) hP hL hwL ha (htr χ hχ)
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul] at h
    exact h
  · calc ∑ χ ∈ nontrivChars q, frobSq (P.hat T ((famZ hq χ).Gz P T))
        = ∑ χ ∈ nontrivChars q, ((P.a T * P.L T)⁻¹) ^ 2
            * trGt2ChiA (parity χ) q (coeff χ) (P.toSetting T) (P.localFun T) :=
          Finset.sum_congr rfl fun χ hχ => frobSq_hat_eq_fam hq (hprim χ hχ) hP hL hwL
      _ = ((P.a T * P.L T)⁻¹) ^ 2
            * ∑ χ ∈ nontrivChars q, trGt2ChiA (parity χ) q (coeff χ) (P.toSetting T) (P.localFun T) := by
          rw [Finset.mul_sum]
      _ ≤ ((P.a T * P.L T)⁻¹) ^ 2 * Fr := mul_le_mul_of_nonneg_left hFr (by positivity)

end RHTower
