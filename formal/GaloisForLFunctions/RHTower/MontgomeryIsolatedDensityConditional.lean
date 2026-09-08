import GaloisForLFunctions.RHTower.MontgomerySingleBandWide

/-!
# Isolated off-line zeros obey the density hypothesis, modulo a strip Ingham bound

The single-band laws resolve real parts only up to the isolation scale `D/log T`.  Removing that
restriction needs one analytic inequality, the **strip Ingham bound**: for frequencies with
pairwise gaps `≥ D` and exponents anywhere in `[−K, 0]`, the mean square of the damped sum
`Σ_r d_r e^{θ_r α} e^{2πi u_r α}` over a window `[a, a+ℓ]` with `ℓ ≥ C/D` is at least
`e^{−C(Kℓ + K/D)}/(CD)` times the bottom energy `Σ_r |d_r|² e^{2θ_r a}`, uniformly in the number
of terms.  For `K ≤ D/100` this is a theorem (the damped Montgomery–Vaughan inequality, see
`stripInghamBound_small_decay`); for `K ≫ D` it is the Riesz-sequence property of exponentials
with exponents in a horizontal strip, which is not elementary.

Granting the bound, the whole set of off-line zeros is one band: every zero with real part at least
`1/2 + 4δ₀`, pairwise `D` mean gaps apart, all other zeros within `δ₀` of the line, satisfies
`Σ_j T^{2a(β_j − 1/2)} ≪ T^{1 + C(ℓ + 1/D)} log T`, hence `N(1/2 + δ, T) ≪ T^{1 − 2aδ + C(ℓ+1/D)} log T`
for every `δ ≥ 4δ₀`: the density hypothesis for isolated zeros, up to the loss `C(ℓ + 1/D)` in the
exponent, which tends to zero as the isolation grows.
-/

open Complex MeasureTheory Set Filter Topology
open scoped BigOperators

namespace RHTower

noncomputable section

/-- **Strip Ingham interface.**  A uniform lower Riesz bound, with loss `e^{−C(Kℓ + K/D)}/(CD)`,
for damped exponential sums with `D`-separated frequencies and exponents in `[−K, 0]`, over any
window of length `ℓ ≥ C/D`, weighted by the bottom energies of the terms. -/
def StripInghamBound (C : ℝ) : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ) (D a ℓ K : ℝ),
    0 < D → 0 ≤ K → C / D ≤ ℓ → (∀ r, -K ≤ θ r ∧ θ r ≤ 0) →
    (∀ r s, r ≠ s → D ≤ |u r - u s|) →
    Real.exp (-(C * (K * ℓ + K / D))) / (C * D) * ∑ r, ‖d r‖ ^ 2 * Real.exp (2 * θ r * a) ≤
      ∫ α in a..a + ℓ, ‖GaloisForLFunctions.HTGeometry.mvBandSum u d θ α‖ ^ 2

/-- In the regime `K ≤ D/100` the strip Ingham bound with `C = 100` is a theorem: the damped
Montgomery–Vaughan inequality with `ℓ₀ = 50/D` gives the constant `≥ 10/D`. -/
theorem stripInghamBound_small_decay {ι : Type} [Fintype ι] [DecidableEq ι]
    (u : ι → ℝ) (d : ι → ℂ) (θ : ι → ℝ) {D a ℓ K : ℝ} (hD : 0 < D) (hK0 : 0 ≤ K)
    (hℓ : 100 / D ≤ ℓ) (hK : K ≤ D / 100) (hθ : ∀ r, -K ≤ θ r ∧ θ r ≤ 0)
    (hsep : ∀ r s, r ≠ s → D ≤ |u r - u s|) :
    Real.exp (-(100 * (K * ℓ + K / D))) / (100 * D) * ∑ r, ‖d r‖ ^ 2 * Real.exp (2 * θ r * a) ≤
      ∫ α in a..a + ℓ, ‖GaloisForLFunctions.HTGeometry.mvBandSum u d θ α‖ ^ 2 := by
  have hℓ₀ : (0 : ℝ) ≤ 50 / D := by positivity
  have hℓ₀ℓ : 50 / D ≤ ℓ := by
    have : (50 : ℝ) / D ≤ 100 / D := div_le_div_of_nonneg_right (by norm_num) hD.le
    linarith
  have hcore := GaloisForLFunctions.HTGeometry.interval_integral_normSq_mvBandSum_ge_damped
    u d θ (a := a) hD hℓ₀ hℓ₀ℓ hK0 hθ hsep
  have hW0 : 0 ≤ ∑ r, ‖d r‖ ^ 2 * Real.exp (2 * θ r * a) :=
    Finset.sum_nonneg fun r _ => by positivity
  -- the damped constant is at least `10/D`
  have hconst : 10 / D ≤ 50 / D * Real.exp (-(2 * K * (50 / D))) - 26 / (Real.pi * D)
      - 9 * K / (Real.pi ^ 2 * D ^ 2) := by
    have hKD : 2 * K * (50 / D) ≤ 1 := by
      rw [show 2 * K * (50 / D) = 100 * K / D by ring, div_le_one hD]
      linarith [hK, show D / 100 * 100 = D by ring]
    have hexp : Real.exp (-1) ≤ Real.exp (-(2 * K * (50 / D))) := by
      rw [Real.exp_le_exp]; linarith
    have he : (0.3678794 : ℝ) ≤ Real.exp (-1) := by
      rw [Real.exp_neg, le_inv_comm₀ (by norm_num) (Real.exp_pos 1)]
      exact (lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num)).le
    have hpi := Real.pi_gt_d4
    have hpipos := Real.pi_pos
    have h1 : 26 / (Real.pi * D) ≤ 26 / (3.1415 * D) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      gcongr
    have h2 : 9 * K / (Real.pi ^ 2 * D ^ 2) ≤ 9 * (D / 100) / (3.1415 ^ 2 * D ^ 2) :=
      div_le_div₀ (by positivity) (by gcongr) (by positivity) (by gcongr)
    have h3 : 50 / D * Real.exp (-1) ≤ 50 / D * Real.exp (-(2 * K * (50 / D))) :=
      mul_le_mul_of_nonneg_left hexp hℓ₀
    have h4 : 50 / D * 0.3678794 ≤ 50 / D * Real.exp (-1) :=
      mul_le_mul_of_nonneg_left he hℓ₀
    have h5 : 9 * (D / 100) / (3.1415 ^ 2 * D ^ 2) = (9 / (100 * 3.1415 ^ 2)) * (1 / D) := by
      field_simp
    have h6 : 26 / (3.1415 * D) = (26 / 3.1415) * (1 / D) := by
      field_simp
    have h7 : 50 / D * 0.3678794 = (50 * 0.3678794) * (1 / D) := by ring
    have h8 : 10 / D = 10 * (1 / D) := by ring
    rw [h5] at h2
    rw [h6] at h1
    rw [h7] at h4
    rw [h8]
    have hDinv : 0 < 1 / D := by positivity
    have hnum : (10 : ℝ) ≤ 50 * 0.3678794 - 26 / 3.1415 - 9 / (100 * 3.1415 ^ 2) := by norm_num
    nlinarith [mul_le_mul_of_nonneg_right hnum hDinv.le]
  have hsmall : Real.exp (-(100 * (K * ℓ + K / D))) / (100 * D) ≤ 10 / D := by
    have h1 : Real.exp (-(100 * (K * ℓ + K / D))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ K * ℓ + K / D := by
        have hℓ0 : 0 ≤ ℓ := le_trans (by positivity) hℓ
        positivity
      linarith
    calc Real.exp (-(100 * (K * ℓ + K / D))) / (100 * D) ≤ 1 / (100 * D) := by
          apply div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ 10 / D := by
          rw [div_le_div_iff₀ (by positivity) hD]
          nlinarith
  calc Real.exp (-(100 * (K * ℓ + K / D))) / (100 * D) * ∑ r, ‖d r‖ ^ 2 * Real.exp (2 * θ r * a)
      ≤ 10 / D * ∑ r, ‖d r‖ ^ 2 * Real.exp (2 * θ r * a) :=
        mul_le_mul_of_nonneg_right hsmall hW0
    _ ≤ (50 / D * Real.exp (-(2 * K * (50 / D))) - 26 / (Real.pi * D)
          - 9 * K / (Real.pi ^ 2 * D ^ 2)) * ∑ r, ‖d r‖ ^ 2 * Real.exp (2 * θ r * a) :=
        mul_le_mul_of_nonneg_right hconst hW0
    _ ≤ _ := hcore

/-- **Window lower bound for the whole off-line block, modulo the strip Ingham bound.**  With the
band normalised at the top `σ = 1`, the strip bound gives the window integral of the block of
Montgomery's form at least `2e^{−3} T^{−C(ℓ + 1/D)}/(CD)` times `Σ_j T^{2a(β_j − 1/2)}`. -/
theorem offline_block_window_ge_of_stripIngham {C : ℝ} (hC : 0 < C) (hSI : StripInghamBound C)
    (A : Finset XiZeroCopy) {T D a ℓ : ℝ} (hT : 1 < T) (hD : 0 < D) (hℓD : C / D ≤ ℓ)
    (hsep : ∀ j ∈ A, ∀ k ∈ A, j ≠ k → D ≤ |bandFreq T j - bandFreq T k|) :
    2 * Real.exp (-3) * (T ^ (-(C * (ℓ + 1 / D))) / (C * D)) *
        ∑ j ∈ A, T ^ (2 * a * ((j.1 : ℂ).re - 1 / 2))
      ≤ ∫ α in a..a + ℓ, (montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re := by
  classical
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT
  have hℓ0 : 0 ≤ ℓ := le_trans (by positivity) hℓD
  set b := a + ℓ with hb
  have hab' : a ≤ b := by rw [hb]; linarith
  set L := Real.log T with hLdef
  set c : ℝ := T ^ (-(C * (ℓ + 1 / D))) / (C * D) with hcdef
  have hc0 : 0 ≤ c := by positivity
  set E : ℝ := Real.exp (2 * (a * (1 - 1 / 2) * Real.log T)) with hE
  have hE0 : 0 < E := Real.exp_pos _
  set S : ℝ := ∑ j ∈ A, T ^ (2 * a * ((j.1 : ℂ).re - 1 / 2)) with hS
  set S' : ℝ := ∑ j ∈ A, T ^ (2 * a * ((j.1 : ℂ).re - 1)) with hS'
  have hES : E * S' = S := by
    rw [hS, hS', Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hE, ← Real.exp_log hT0, Real.exp_log hT0]
    have h1 : E = T ^ a := by
      rw [hE, Real.rpow_def_of_pos hT0]
      congr 1
      ring
    rw [← hE, h1, ← Real.rpow_add hT0]
    congr 1
    ring
  set g : ℝ → ℝ → ℝ := fun α ξ =>
    ‖zeroPowerSum A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α * Real.exp (-ξ))‖ ^ 2 with hg
  have hgcont : Continuous (Function.uncurry g) := continuous_normSq_zeroPowerSum_scale A hT0
  have hinner : ∀ ξ ∈ Icc (-1 : ℝ) 1,
      E * c * Real.exp (-1) * S' ≤ ∫ α in a..b, g α ξ := by
    intro ξ hξ
    set u : A → ℝ := fun j => bandFreq T j with hu
    set d : A → ℂ := fun j => bandCoeff ξ j with hd
    set θ : A → ℝ := fun j => bandTheta T 1 j with hθ
    set B : ℝ → ℂ := fun α => GaloisForLFunctions.HTGeometry.mvBandSum u d θ α with hB
    have hgB : ∀ α, g α ξ = Real.exp (2 * (α * (1 - 1 / 2) * Real.log T)) * ‖B α‖ ^ 2 := by
      intro α
      simp only [hg, hB, hu, hd, hθ]
      exact normSq_zeroPowerSum_eq_bandSum A hT0 1 ξ α
    have hBcont : Continuous B := by
      simp only [hB]
      unfold GaloisForLFunctions.HTGeometry.mvBandSum
      fun_prop
    have hmono : ∀ α ∈ Icc a b, E * ‖B α‖ ^ 2 ≤ g α ξ := by
      intro α hα
      rw [hgB α, hE]
      have : Real.exp (2 * (a * (1 - 1 / 2) * Real.log T))
          ≤ Real.exp (2 * (α * (1 - 1 / 2) * Real.log T)) := by
        apply Real.exp_le_exp.mpr
        have : a * (1 - 1 / 2) * Real.log T ≤ α * (1 - 1 / 2) * Real.log T := by
          gcongr
          exact hα.1
        linarith
      gcongr
    have hint2 : E * ∫ α in a..b, ‖B α‖ ^ 2 ≤ ∫ α in a..b, g α ξ := by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_mono_on hab'
      · exact (continuous_const.mul (hBcont.norm.pow 2)).intervalIntegrable _ _
      · exact (hgcont.comp (Continuous.prodMk continuous_id continuous_const)).intervalIntegrable _ _
      · exact hmono
    have hθb : ∀ r : A, -L ≤ θ r ∧ θ r ≤ 0 := by
      intro r
      simp only [hθ, bandTheta]
      have h1 := xiZeroCopy_re_pos r.1
      have h2 := xiZeroCopy_re_lt_one r.1
      constructor
      · nlinarith
      · nlinarith
    have hsep' : ∀ r s : A, r ≠ s → D ≤ |u r - u s| := by
      intro r s hrs
      exact hsep r.1 r.2 s.1 s.2 (fun h => hrs (Subtype.ext h))
    have hstrip := hSI A u d θ D a ℓ L hD hL.le hℓD hθb hsep'
    have hloss : Real.exp (-(C * (L * ℓ + L / D))) / (C * D) = c := by
      rw [hcdef, Real.rpow_def_of_pos hT0, ← hLdef]
      congr 2
      ring
    rw [hloss] at hstrip
    have hcoef : Real.exp (-1) * S' ≤ ∑ r : A, ‖d r‖ ^ 2 * Real.exp (2 * θ r * a) := by
      have hξ1 : |ξ| ≤ 1 := by rw [abs_le]; exact ⟨hξ.1, hξ.2⟩
      have hterm : ∀ r : A, Real.exp (-1) * T ^ (2 * a * (((r.1).1 : ℂ).re - 1)) ≤
          ‖d r‖ ^ 2 * Real.exp (2 * θ r * a) := by
        intro r
        have h1 : Real.exp (-1) ≤ ‖d r‖ ^ 2 := by
          refine le_trans ?_ (normSq_bandCoeff_ge ξ r.1)
          apply Real.exp_le_exp.mpr
          linarith
        have h2 : T ^ (2 * a * (((r.1).1 : ℂ).re - 1)) = Real.exp (2 * θ r * a) := by
          rw [Real.rpow_def_of_pos hT0]
          simp only [hθ, bandTheta]
          congr 1
          rw [← hLdef]
          ring
        rw [h2]
        exact mul_le_mul_of_nonneg_right h1 (Real.exp_pos _).le
      calc Real.exp (-1) * S' = ∑ r : A, Real.exp (-1) * T ^ (2 * a * (((r.1).1 : ℂ).re - 1)) := by
            rw [hS', Finset.mul_sum, ← Finset.sum_coe_sort A]
        _ ≤ _ := Finset.sum_le_sum fun r _ => hterm r
    have hband' : c * (Real.exp (-1) * S') ≤ ∫ α in a..b, ‖B α‖ ^ 2 := by
      calc c * (Real.exp (-1) * S') ≤ c * ∑ r : A, ‖d r‖ ^ 2 * Real.exp (2 * θ r * a) :=
            mul_le_mul_of_nonneg_left hcoef hc0
        _ ≤ ∫ α in a..b, ‖B α‖ ^ 2 := by simpa [hb] using hstrip
    calc E * c * Real.exp (-1) * S' = E * (c * (Real.exp (-1) * S')) := by ring
      _ ≤ E * ∫ α in a..b, ‖B α‖ ^ 2 := mul_le_mul_of_nonneg_left hband' hE0.le
      _ ≤ ∫ α in a..b, g α ξ := hint2
  have := montgomeryForm_window_ge_of_inner A hT0 hℓ0 (E * c * Real.exp (-1) * S')
    (by intro ξ hξ; exact hinner ξ hξ)
  have h3 : Real.exp (-3) = Real.exp (-2) * Real.exp (-1) := by
    rw [← Real.exp_add]; norm_num
  rw [h3, ← hES]
  calc 2 * (Real.exp (-2) * Real.exp (-1)) * c * (E * S')
      = 2 * Real.exp (-2) * (E * c * Real.exp (-1) * S') := by ring
    _ ≤ _ := this

/-- **Isolated off-line energy bound, modulo the strip Ingham bound.**  If every zero with real
part `≥ 1/2 + 4δ₀` up to height `T` is `D` mean gaps from every other such zero and all remaining
zeros are within `δ₀` of the line, then `Σ_j T^{2a(β_j − 1/2)} ≤ (CDℓ e³/π) T^{1 + C(ℓ + 1/D)} log T`
for large `T`, provided the loss `C(ℓ + 1/D)` is below `aδ₀/2`. -/
theorem eventually_sum_offline_energy_le_of_stripIngham {C : ℝ} (hC : 0 < C)
    (hSI : StripInghamBound C) {a ℓ δ₀ D : ℝ}
    (ha : 0 < a) (hℓ : 0 < ℓ) (hab : a + ℓ < 1) (hwin : 2 * (a + ℓ) ≤ 3 * a)
    (hδ₀ : 0 < δ₀) (hD : 0 < D) (hℓD : C / D ≤ ℓ) (hloss : C * (ℓ + 1 / D) < a * δ₀ / 2) :
    ∀ᶠ T : ℝ in atTop, ∀ A : Finset XiZeroCopy, A ⊆ zeroWindow T →
      (∀ j ∈ A, 1 / 2 + 4 * δ₀ ≤ (j.1 : ℂ).re) →
      (∀ k ∈ zeroWindow T \ A, (k.1 : ℂ).re ≤ 1 / 2 + δ₀) →
      (∀ j ∈ A, ∀ k ∈ A, j ≠ k → D ≤ |bandFreq T j - bandFreq T k|) →
      ∑ j ∈ A, T ^ (2 * a * ((j.1 : ℂ).re - 1 / 2)) ≤
        (C * D * ℓ * Real.exp 3 / Real.pi) * T ^ (1 + C * (ℓ + 1 / D)) * Real.log T := by
  classical
  set lam := C * (ℓ + 1 / D) with hlam
  have hlam0 : 0 ≤ lam := by positivity
  set b := a + ℓ with hb
  have hb0 : 0 < b := by rw [hb]; linarith
  have hb1 : b < 1 := hab
  have hab' : a ≤ b := by rw [hb]; linarith
  have hℓa : ℓ ≤ a / 2 := by linarith
  set η := a * δ₀ / 2 - lam with hη
  have hηpos : 0 < η := by rw [hη]; linarith
  set C₀ := xiLineTwoLogDerivConstant with hC₀
  set ε₁ : ℝ := Real.exp (-3) / (192 * C * D * ℓ) with hε₁
  have hε₁pos : 0 < ε₁ := by positivity
  have E1 := eventually_montgomeryForm_div_leadingOrder_uniform ha hab' hb1 (one_pos)
  have E2 := eventually_log_bounds
  have E3 := (tendsto_log_pow_div_rpow 1 hηpos).eventually (eventually_le_nhds hε₁pos)
  have E4 := Real.tendsto_log_atTop.eventually_ge_atTop C₀
  filter_upwards [E1, E2, E3, E4, eventually_gt_atTop (1 : ℝ)] with T e1 e2 e3 e4 hT1
  intro A hA hband hR hsep
  obtain ⟨hl1, _, _, hl4⟩ := e2
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT1
  set L := Real.log T with hLdef
  set S : ℝ := ∑ j ∈ A, T ^ (2 * a * ((j.1 : ℂ).re - 1 / 2)) with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun j _ => by positivity
  -- (i) the block over the window
  have hlow := offline_block_window_ge_of_stripIngham hC hSI A (a := a) hT1 hD hℓD hsep
  rw [← hS, ← hb, ← hlam] at hlow
  -- (ii) pointwise upper bound
  have hW : windowLog T ≤ 3 * L := by
    unfold windowLog
    linarith
  set X : ℝ := ∑ j ∈ A, T ^ (b * ((j.1 : ℂ).re - 1 / 2)) with hX
  have hX0 : 0 ≤ X := Finset.sum_nonneg fun j _ => by positivity
  have hpt : ∀ α ∈ Icc a b,
      (montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
        ≤ T / Real.pi * L + 192 * L * T ^ (b * δ₀) * X := by
    intro α hα
    have hα0 : 0 ≤ α := ha.le.trans hα.1
    have hx1 : 1 ≤ T ^ α := Real.one_le_rpow hT1.le hα0
    have hx0 : 0 < T ^ α := by linarith
    have hF : (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
        ≤ T / Real.pi * L := by
      have h := e1 α hα
      have hNα : 0 < (T / (2 * Real.pi)) * (α * L) := by
        have : 0 < α := lt_of_lt_of_le ha hα.1
        positivity
      rw [abs_lt] at h
      have h2 := h.2
      rw [div_sub_one (ne_of_gt hNα), div_lt_iff₀ hNα] at h2
      have hαL : α * L ≤ L := by
        have : α ≤ 1 := by linarith [hα.2]
        nlinarith
      calc (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
          ≤ 1 * (T / (2 * Real.pi) * (α * L)) + T / (2 * Real.pi) * (α * L) := by linarith
        _ = T / Real.pi * (α * L) := by field_simp; ring
        _ ≤ T / Real.pi * L := by gcongr
    have hRα : ∀ k ∈ zeroWindow T \ A, zeroAmp (T ^ α) k ≤ (T ^ α) ^ δ₀ := by
      intro k hk
      unfold zeroAmp
      apply Real.rpow_le_rpow_of_exponent_le hx1
      linarith [hR k hk]
    have hsplit := montgomeryForm_block_split hx0 A hA (Θ := (T ^ α) ^ δ₀) (by positivity) hRα
    have hamp : ∑ j ∈ A, zeroAmp (T ^ α) j ≤ X := by
      rw [hX]
      refine Finset.sum_le_sum fun j hj => ?_
      unfold zeroAmp
      rw [← Real.rpow_mul hT0.le]
      apply Real.rpow_le_rpow_of_exponent_le hT1.le
      have h1 : 0 ≤ (j.1 : ℂ).re - 1 / 2 := by linarith [hband j hj]
      exact mul_le_mul_of_nonneg_right hα.2 h1
    have hΘ : (T ^ α) ^ δ₀ ≤ T ^ (b * δ₀) := by
      rw [← Real.rpow_mul hT0.le]
      apply Real.rpow_le_rpow_of_exponent_le hT1.le
      exact mul_le_mul_of_nonneg_right hα.2 hδ₀.le
    have hcross : 64 * (T ^ α) ^ δ₀ * windowLog T * ∑ j ∈ A, zeroAmp (T ^ α) j
        ≤ 192 * L * T ^ (b * δ₀) * X := by
      have hsum0 : 0 ≤ ∑ j ∈ A, zeroAmp (T ^ α) j :=
        Finset.sum_nonneg fun j _ => zeroAmp_nonneg hx0.le j
      have hW0 : 0 ≤ windowLog T := windowLog_nonneg hT0.le
      calc 64 * (T ^ α) ^ δ₀ * windowLog T * ∑ j ∈ A, zeroAmp (T ^ α) j
          ≤ 64 * T ^ (b * δ₀) * (3 * L) * X := by gcongr
        _ = 192 * L * T ^ (b * δ₀) * X := by ring
    have h1 := sub_le_iff_le_add.mp hsplit
    calc (montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
        ≤ (montgomeryForm (zeroWindow T) (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re
          + 64 * (T ^ α) ^ δ₀ * windowLog T * ∑ j ∈ A, zeroAmp (T ^ α) j := h1
      _ ≤ T / Real.pi * L + 192 * L * T ^ (b * δ₀) * X := add_le_add hF hcross
  -- (iii) integrate
  have hcontF := continuous_montgomeryForm_rpow A hT0
  have hup : (∫ α in a..b, (montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re)
      ≤ ℓ * (T / Real.pi * L + 192 * L * T ^ (b * δ₀) * X) := by
    have this : (∫ α in a..b, (montgomeryForm A (fun q : XiZeroCopy => (q.1 : ℂ)) (T ^ α)).re)
        ≤ ∫ _α in a..b, (T / Real.pi * L + 192 * L * T ^ (b * δ₀) * X) :=
      intervalIntegral.integral_mono_on hab' (hcontF.intervalIntegrable _ _)
        intervalIntegrable_const hpt
    rw [intervalIntegral.integral_const, smul_eq_mul] at this
    have hba : b - a = ℓ := by rw [hb]; ring
    rw [hba] at this
    exact this
  -- (iv) termwise domination of the cross term by the detection term
  have hTη : 0 < T ^ η := Real.rpow_pos_of_pos hT0 η
  have hlogT : L ≤ ε₁ * T ^ η := by
    have h := e3
    simp only [pow_one] at h
    rwa [div_le_iff₀ hTη] at h
  have hdom : ℓ * (192 * L * T ^ (b * δ₀) * X) ≤
      Real.exp (-3) * (T ^ (-lam) / (C * D)) * S := by
    rw [hX, hS, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun j hj => ?_
    set δj : ℝ := (j.1 : ℂ).re - 1 / 2 with hδj
    have hδj4 : 4 * δ₀ ≤ δj := by rw [hδj]; linarith [hband j hj]
    -- exponent gap
    have hexp : η ≤ 2 * a * δj - (b * δ₀ + b * δj + lam) := by
      rw [hη, hb]
      nlinarith [hℓa, hδj4, hδ₀, ha]
    have hpow : T ^ (2 * a * δj) = T ^ (2 * a * δj - (b * δ₀ + b * δj + lam)) *
        (T ^ (b * δ₀) * T ^ (b * δj) * T ^ lam) := by
      rw [← Real.rpow_add hT0, ← Real.rpow_add hT0, ← Real.rpow_add hT0]
      congr 1
      ring
    have hgap : 192 * C * D * ℓ * L ≤ Real.exp (-3) *
        T ^ (2 * a * δj - (b * δ₀ + b * δj + lam)) := by
      have h1 : T ^ η ≤ T ^ (2 * a * δj - (b * δ₀ + b * δj + lam)) :=
        Real.rpow_le_rpow_of_exponent_le hT1.le hexp
      calc 192 * C * D * ℓ * L ≤ 192 * C * D * ℓ * (ε₁ * T ^ η) := by gcongr
        _ = Real.exp (-3) * T ^ η := by rw [hε₁]; field_simp
        _ ≤ _ := mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
    have hpos1 : 0 < T ^ (b * δ₀) * T ^ (b * δj) := by positivity
    have hTlam : T ^ (-lam) = 1 / T ^ lam := by
      rw [Real.rpow_neg hT0.le, one_div]
    have hTlampos : 0 < T ^ lam := Real.rpow_pos_of_pos hT0 _
    rw [hTlam, hpow]
    have hCD : 0 < C * D := by positivity
    rw [show ℓ * (192 * L * T ^ (b * δ₀) * T ^ (b * δj)) =
      (192 * C * D * ℓ * L) * (T ^ (b * δ₀) * T ^ (b * δj)) / (C * D) by field_simp]
    rw [show Real.exp (-3) * (1 / T ^ lam / (C * D)) *
      (T ^ (2 * a * δj - (b * δ₀ + b * δj + lam)) * (T ^ (b * δ₀) * T ^ (b * δj) * T ^ lam)) =
      (Real.exp (-3) * T ^ (2 * a * δj - (b * δ₀ + b * δj + lam))) *
        (T ^ (b * δ₀) * T ^ (b * δj)) / (C * D) by field_simp]
    apply div_le_div_of_nonneg_right _ hCD.le
    exact mul_le_mul_of_nonneg_right hgap hpos1.le
  -- (v) conclude
  have hmain : Real.exp (-3) * (T ^ (-lam) / (C * D)) * S ≤ ℓ * (T / Real.pi * L) := by
    have h1 : 2 * Real.exp (-3) * (T ^ (-lam) / (C * D)) * S
        ≤ ℓ * (T / Real.pi * L) + ℓ * (192 * L * T ^ (b * δ₀) * X) := by
      have := hup
      rw [mul_add] at this
      linarith only [hlow, this]
    linarith only [h1, hdom]
  have hTlam : 0 < T ^ (-lam) := Real.rpow_pos_of_pos hT0 _
  have hpos : 0 < Real.exp (-3) * (T ^ (-lam) / (C * D)) := by positivity
  have hfinal : S ≤ ℓ * (T / Real.pi * L) / (Real.exp (-3) * (T ^ (-lam) / (C * D))) := by
    rw [le_div_iff₀ hpos]
    linarith [hmain]
  refine hfinal.trans (le_of_eq ?_)
  rw [Real.exp_neg, Real.rpow_neg hT0.le, Real.rpow_add hT0, Real.rpow_one]
  field_simp

/-- **Isolated zeros obey the density hypothesis, modulo the strip Ingham bound.**  Under the
hypotheses of the energy bound, for every `δ` the number of zeros with real part `≥ 1/2 + δ`
is at most `(CDℓ e³/π) T^{1 − 2aδ + C(ℓ + 1/D)} log T`. -/
theorem eventually_card_offline_le_of_stripIngham {C : ℝ} (hC : 0 < C)
    (hSI : StripInghamBound C) {a ℓ δ₀ δ D : ℝ}
    (ha : 0 < a) (hℓ : 0 < ℓ) (hab : a + ℓ < 1) (hwin : 2 * (a + ℓ) ≤ 3 * a)
    (hδ₀ : 0 < δ₀) (hD : 0 < D) (hℓD : C / D ≤ ℓ)
    (hloss : C * (ℓ + 1 / D) < a * δ₀ / 2) :
    ∀ᶠ T : ℝ in atTop, ∀ A : Finset XiZeroCopy, A ⊆ zeroWindow T →
      (∀ j ∈ A, 1 / 2 + 4 * δ₀ ≤ (j.1 : ℂ).re) →
      (∀ k ∈ zeroWindow T \ A, (k.1 : ℂ).re ≤ 1 / 2 + δ₀) →
      (∀ j ∈ A, ∀ k ∈ A, j ≠ k → D ≤ |bandFreq T j - bandFreq T k|) →
      ((A.filter (fun j => 1 / 2 + δ ≤ (j.1 : ℂ).re)).card : ℝ) ≤
        (C * D * ℓ * Real.exp 3 / Real.pi) * T ^ (1 - 2 * a * δ + C * (ℓ + 1 / D)) * Real.log T := by
  classical
  have h := eventually_sum_offline_energy_le_of_stripIngham hC hSI ha hℓ hab hwin hδ₀ hD hℓD hloss
  filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with T hT hT1
  intro A hA hband hR hsep
  have hS := hT A hA hband hR hsep
  have hT0 : 0 < T := by linarith
  have hL : 0 < Real.log T := Real.log_pos hT1
  set B := A.filter (fun j => 1 / 2 + δ ≤ (j.1 : ℂ).re) with hB
  have hcount : (B.card : ℝ) * T ^ (2 * a * δ) ≤ ∑ j ∈ A, T ^ (2 * a * ((j.1 : ℂ).re - 1 / 2)) := by
    calc (B.card : ℝ) * T ^ (2 * a * δ) = ∑ _j ∈ B, T ^ (2 * a * δ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ j ∈ B, T ^ (2 * a * ((j.1 : ℂ).re - 1 / 2)) := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' := (Finset.mem_filter.mp hj).2
          apply Real.rpow_le_rpow_of_exponent_le hT1.le
          have : δ ≤ (j.1 : ℂ).re - 1 / 2 := by linarith
          nlinarith
      _ ≤ ∑ j ∈ A, T ^ (2 * a * ((j.1 : ℂ).re - 1 / 2)) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun j _ _ => by positivity)
  have hTpow : 0 < T ^ (2 * a * δ) := Real.rpow_pos_of_pos hT0 _
  have hfinal : (B.card : ℝ) ≤ (C * D * ℓ * Real.exp 3 / Real.pi) *
      T ^ (1 + C * (ℓ + 1 / D)) * Real.log T / T ^ (2 * a * δ) := by
    rw [le_div_iff₀ hTpow]
    linarith [hcount, hS]
  refine hfinal.trans (le_of_eq ?_)
  have hpow : T ^ (1 - 2 * a * δ + C * (ℓ + 1 / D)) =
      T ^ (1 + C * (ℓ + 1 / D)) / T ^ (2 * a * δ) := by
    rw [← Real.rpow_sub hT0]
    congr 1
    ring
  rw [hpow]
  field_simp

end

end RHTower
