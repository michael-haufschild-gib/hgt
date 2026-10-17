import GaloisForLFunctions.RHTower.TwinRigidityZetaPower
import GaloisForLFunctions.RHTower.WeilConeDegreePoleOrderClassification

/-!
# Pole order rigidity: critical zeros force the pole order to equal the degree

Let `T(s) = Σ a(n) n^{−s}` have real coefficients with `a(1) = 1`, absolutely convergent on
`Re s > σ₀`, and let `Λ(s) = (s(s − 1))^κ Γ_ℝ(s)^d T(s)` extend to an entire function of finite order
with `Λ(1 − s) = Λ(s)` (`PoleTwinDatum`): degree `d ≥ 1`, conductor one, a pole of order at most `κ`
at `s = 1`.  If every zero of `Λ` lies on `Re s = ½`, then `κ = d`, the Riemann hypothesis holds and
`T = ζ^d` (`pole_order_rigidity`).  In particular a pole order below or above the degree is
incompatible with all zeros being critical.

**Proof.**  `Λ` has the order-one envelope (`orderOneEnvelope_pole`), so `Φ = Λ'/(dΛ)` is a
Herglotz function on `Re s > ½` (zero pairs on the critical line), equal far to the right to the Weil
function of `λ_T/d` at pole weight `κ/d`.  The Herglotz argument on a line of absolute convergence
(`weilPoleWeight_nonneg_of_herglotz_abscissa`) makes `W_{d,κ}(λ_T) = d W_{κ/d}(λ_T/d)` nonnegative on
autocorrelations, and the Weil-cone classification (`forall_re_weilDegreePoleFunctional_nonneg_iff`)
gives `κ = d`, RH and `λ_T = dΛ`, whence `T = ζ^d` (`eq_zetaPow_of_lamT`).
-/

open Complex Filter Topology Set LSeries Asymptotics MeasureTheory
open GaloisForLFunctions.EntireZeroDivisor

noncomputable section

namespace RHTower.TwinRigidity

open Zeta23 Zeta23.WeilEF WeilLineIntegral

/-! ### The order-one envelope with independent pole order and degree -/

/-- `(s(s − 1))^κ Γ_ℝ(s)^d` is bounded on the line `Re s = 2m` when `d ≥ 1`. -/
theorem exists_bound_completionFactor_pole {m : ℕ} (hm : 1 ≤ m) (κ : ℕ) {d : ℕ} (hd : 1 ≤ d) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ τ : ℝ,
      ‖((((2 * m : ℕ) : ℂ) + τ * I) * (((2 * m : ℕ) : ℂ) + τ * I - 1)) ^ κ *
        Complex.Gammaℝ (((2 * m : ℕ) : ℂ) + τ * I) ^ d‖ ≤ B := by
  obtain ⟨Cγ, Nγ, hCγ, hγ⟩ := CompletionGrowth.exists_bound_Gammaℝ_even hm
  set N : ℕ := 2 * κ + d * Nγ with hN
  set F : ℝ := (4 / Real.pi) ^ N * N.factorial * Real.exp Real.pi with hF
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  refine ⟨(2 * m) ^ (2 * κ) * Cγ ^ d * F, by positivity, fun τ => ?_⟩
  have hτ := abs_nonneg τ
  have h1 : ‖((2 * m : ℕ) : ℂ) + τ * I‖ ≤ (2 * m) * (|τ| + 4) := by
    calc ‖((2 * m : ℕ) : ℂ) + τ * I‖ ≤ ‖((2 * m : ℕ) : ℂ)‖ + ‖(τ : ℂ) * I‖ := norm_add_le _ _
      _ = 2 * m + |τ| := by simp
      _ ≤ (2 * m) * (|τ| + 4) := by nlinarith
  have h2 : ‖((2 * m : ℕ) : ℂ) + τ * I - 1‖ ≤ (2 * m) * (|τ| + 4) := by
    have e : ((2 * m : ℕ) : ℂ) + τ * I - 1 = ((2 * m - 1 : ℝ) : ℂ) + τ * I := by push_cast; ring
    rw [e]
    calc ‖((2 * m - 1 : ℝ) : ℂ) + τ * I‖ ≤ ‖((2 * m - 1 : ℝ) : ℂ)‖ + ‖(τ : ℂ) * I‖ :=
          norm_add_le _ _
      _ = (2 * m - 1) + |τ| := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; simp
      _ ≤ (2 * m) * (|τ| + 4) := by nlinarith
  have hexp1 : Real.exp (-(Real.pi * |τ| / 4)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by have := Real.pi_pos; nlinarith)
  have hG : ‖Complex.Gammaℝ (((2 * m : ℕ) : ℂ) + τ * I)‖ ^ d ≤
      Cγ ^ d * ((|τ| + 4) ^ (d * Nγ) * Real.exp (-(Real.pi * |τ| / 4))) := by
    calc ‖Complex.Gammaℝ (((2 * m : ℕ) : ℂ) + τ * I)‖ ^ d
        ≤ (Cγ * ((|τ| + 4) ^ Nγ * Real.exp (-(Real.pi * |τ| / 4)))) ^ d :=
          pow_le_pow_left₀ (norm_nonneg _) (hγ τ) d
      _ = Cγ ^ d * ((|τ| + 4) ^ (d * Nγ) * Real.exp (-(Real.pi * |τ| / 4)) ^ d) := by
          rw [mul_pow, mul_pow, ← pow_mul, mul_comm Nγ d]
      _ ≤ Cγ ^ d * ((|τ| + 4) ^ (d * Nγ) * Real.exp (-(Real.pi * |τ| / 4))) := by
          gcongr
          exact pow_le_of_le_one (Real.exp_pos _).le hexp1 (by omega)
  have hpe : (|τ| + 4) ^ N * Real.exp (-(Real.pi * |τ| / 4)) ≤ F := by
    have h := MaassZetaSquaredConverse.pow_mul_exp_le (by positivity : (0 : ℝ) ≤ |τ| + 4) N
    have he : Real.exp (-(Real.pi * |τ| / 4)) =
        Real.exp (-(Real.pi * (|τ| + 4) / 4)) * Real.exp Real.pi := by
      rw [← Real.exp_add]; ring_nf
    rw [he, hF, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right h (Real.exp_pos _).le
  rw [norm_mul, norm_pow, norm_pow, norm_mul]
  calc (‖((2 * m : ℕ) : ℂ) + τ * I‖ * ‖((2 * m : ℕ) : ℂ) + τ * I - 1‖) ^ κ *
        ‖Complex.Gammaℝ (((2 * m : ℕ) : ℂ) + τ * I)‖ ^ d
      ≤ ((2 * m) * (|τ| + 4) * ((2 * m) * (|τ| + 4))) ^ κ *
          (Cγ ^ d * ((|τ| + 4) ^ (d * Nγ) * Real.exp (-(Real.pi * |τ| / 4)))) :=
        mul_le_mul (pow_le_pow_left₀ (by positivity) (mul_le_mul h1 h2 (norm_nonneg _)
          (by positivity)) κ) hG (by positivity) (by positivity)
    _ = (2 * m) ^ (2 * κ) * Cγ ^ d * ((|τ| + 4) ^ N * Real.exp (-(Real.pi * |τ| / 4))) := by
        have e1 : ((2 * m) * (|τ| + 4) * ((2 * m) * (|τ| + 4)) : ℝ) ^ κ =
            (2 * m : ℝ) ^ (2 * κ) * (|τ| + 4) ^ (2 * κ) := by
          rw [show ((2 * m) * (|τ| + 4) * ((2 * m) * (|τ| + 4)) : ℝ) =
            ((2 * m) * (|τ| + 4)) ^ 2 by ring, ← pow_mul, mul_pow]
        rw [e1, hN, pow_add]
        set X : ℝ := (|τ| + 4) ^ (2 * κ)
        set Y : ℝ := (|τ| + 4) ^ (d * Nγ)
        set Z : ℝ := (2 * m : ℝ) ^ (2 * κ)
        set W : ℝ := Cγ ^ d
        ring
    _ ≤ (2 * m) ^ (2 * κ) * Cγ ^ d * F := mul_le_mul_of_nonneg_left hpe (by positivity)

/-- **The order-one envelope for `(s(s − 1))^κ Γ_ℝ(s)^d Σ g(n) n^{−s}`** of finite order. -/
theorem orderOneEnvelope_pole {E : ℂ → ℂ} (hE : Differentiable ℂ E)
    (hfin : ∃ ρ C₀ : ℝ, ∀ s, ‖E s‖ ≤ C₀ * Real.exp (‖s‖ ^ ρ)) {ε : ℂ} (hε : ‖ε‖ = 1)
    (hsym : ∀ s, E (1 - s) = ε * E s) {κ d : ℕ} (hd : 1 ≤ d) {g : ℕ → ℂ} {σ₀ : ℝ}
    (hg : ∀ s : ℂ, σ₀ < s.re → LSeriesSummable g s)
    (hcomp : ∀ s : ℂ, σ₀ < s.re →
      E s = (s * (s - 1)) ^ κ * Complex.Gammaℝ s ^ d * LSeries g s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s, ‖E s‖ ≤ Real.exp (C * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
  obtain ⟨ρ, C₀, hfin⟩ := hfin
  set m : ℕ := ⌈max σ₀ 0⌉₊ + 1 with hmdef
  have hm : 1 ≤ m := by omega
  have hmσ : σ₀ < ((2 * m : ℕ) : ℝ) := by
    have h1 : max σ₀ 0 ≤ ⌈max σ₀ 0⌉₊ := Nat.le_ceil _
    have h2 : σ₀ ≤ max σ₀ 0 := le_max_left _ _
    have h3 : (0 : ℝ) ≤ max σ₀ 0 := le_max_right _ _
    push_cast [hmdef]
    linarith
  have hN2 : (2 : ℝ) ≤ ((2 * m : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    push_cast; linarith
  set N : ℝ := ((2 * m : ℕ) : ℝ) with hN
  have hflip : ∀ s, ‖E s‖ = ‖E (1 - s)‖ := by
    intro s
    have := hsym (1 - s)
    rw [sub_sub_cancel] at this
    rw [this, norm_mul, hε, one_mul]
  have hgN : LSeriesSummable g N := hg N (by simpa using hmσ)
  set S : ℝ := ∑' n, ‖LSeries.term g N n‖ with hS
  have hS0 : 0 ≤ S := tsum_nonneg fun n => norm_nonneg _
  have hLb : ∀ s : ℂ, N ≤ s.re → ‖LSeries g s‖ ≤ S := fun s hs =>
    CompletionGrowth.norm_LSeries_le_of_le hgN hs
  -- the line `Re s = N`
  obtain ⟨B₁, hB₁0, hB₁⟩ := exists_bound_completionFactor_pole hm κ hd
  have hline : ∀ z : ℂ, z.re = N → ‖E z‖ ≤ B₁ * S := by
    intro z hz
    have hz' : z = ((2 * m : ℕ) : ℂ) + (z.im : ℂ) * I := by
      apply Complex.ext <;> simp [hz, hN]
    rw [hcomp z (by linarith), norm_mul]
    refine mul_le_mul ?_ (hLb z hz.ge) (norm_nonneg _) hB₁0
    rw [hz']
    exact hB₁ z.im
  -- the strip
  have hstrip : ∀ z : ℂ, 1 - N ≤ z.re → z.re ≤ N → ‖E z‖ ≤ B₁ * S := fun z h1 h2 =>
    PhragmenLindelof.vertical_strip hE.diffContOnCl
      (CompletionGrowth.isBigO_strip_of_finiteOrder_at hfin (by linarith)) (fun w hw => by
        rw [hflip]; exact hline (1 - w) (by simp [hw])) hline h1 h2
  -- the right half-plane
  obtain ⟨C₁, hC₁0, hC₁⟩ := CompletionGrowth.le_exp_envelope (A := S) (M := d)
    (Nat.cast_nonneg d) (2 * κ)
  have hright : ∀ s : ℂ, N ≤ s.re →
      ‖E s‖ ≤ Real.exp (C₁ * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
    intro s hs
    refine le_trans ?_ (hC₁ ‖s‖ (norm_nonneg s))
    rw [hcomp s (by linarith), norm_mul, norm_mul, norm_pow, norm_pow, norm_mul]
    have h1 : ‖s‖ ≤ 1 + ‖s‖ := by linarith
    have h2 : ‖s - 1‖ ≤ 1 + ‖s‖ := by
      calc ‖s - 1‖ ≤ ‖s‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 1 + ‖s‖ := by simp; ring
    have hG := CompletionGrowth.norm_Gammaℝ_le (s := s) (by linarith)
    calc (‖s‖ * ‖s - 1‖) ^ κ * ‖Complex.Gammaℝ s‖ ^ d * ‖LSeries g s‖
        ≤ ((1 + ‖s‖) * (1 + ‖s‖)) ^ κ * Real.exp (‖s‖ * Real.log (2 + ‖s‖)) ^ d * S := by
          gcongr
          exact hLb s hs
      _ = S * (1 + ‖s‖) ^ (2 * κ) * Real.exp (d * ‖s‖ * Real.log (2 + ‖s‖)) := by
          rw [← Real.exp_nat_mul, ← pow_two, ← pow_mul]
          ring_nf
  obtain ⟨C₂, hC₂0, hC₂⟩ := CompletionGrowth.le_exp_envelope (A := B₁ * S) (M := 0) le_rfl 0
  refine ⟨4 * C₁ + C₂, by positivity, fun s => ?_⟩
  have hmono : ∀ C' : ℝ, C' ≤ 4 * C₁ + C₂ → 0 ≤ C' →
      Real.exp (C' * (1 + ‖s‖) * Real.log (2 + ‖s‖)) ≤
        Real.exp ((4 * C₁ + C₂) * (1 + ‖s‖) * Real.log (2 + ‖s‖)) := by
    intro C' hC' _
    rw [Real.exp_le_exp]
    have hL0 : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith [norm_nonneg s])
    have : 0 ≤ (1 + ‖s‖) * Real.log (2 + ‖s‖) := mul_nonneg (by positivity) hL0
    nlinarith
  rcases le_or_gt N s.re with h2 | h2
  · exact (hright s h2).trans (hmono C₁ (by linarith) hC₁0)
  rcases le_or_gt (1 - N) s.re with h1 | h1
  · have := hC₂ ‖s‖ (norm_nonneg s)
    simp only [pow_zero, mul_one, zero_mul, Real.exp_zero] at this
    exact ((hstrip s h1 h2.le).trans this).trans (hmono C₂ (by linarith) hC₂0)
  · rw [hflip]
    have hre : N ≤ (1 - s).re := by simp; linarith
    refine (hright (1 - s) hre).trans ?_
    have hn : ‖1 - s‖ ≤ 1 + ‖s‖ := by
      calc ‖1 - s‖ ≤ ‖(1 : ℂ)‖ + ‖s‖ := norm_sub_le _ _
        _ = 1 + ‖s‖ := by simp
    refine le_trans ?_ (hmono (4 * C₁) (by linarith) (by positivity))
    rw [Real.exp_le_exp]
    have hx := norm_nonneg s
    have hL0 : 0 ≤ Real.log (2 + ‖s‖) := Real.log_nonneg (by linarith)
    have hl : Real.log (2 + ‖1 - s‖) ≤ 2 * Real.log (2 + ‖s‖) := by
      rw [← Real.log_rpow (by positivity)]
      refine Real.log_le_log (by positivity) ?_
      norm_num
      nlinarith
    have hl0 : 0 ≤ Real.log (2 + ‖1 - s‖) := Real.log_nonneg (by linarith [norm_nonneg (1 - s)])
    calc C₁ * (1 + ‖1 - s‖) * Real.log (2 + ‖1 - s‖)
        ≤ C₁ * (2 * (1 + ‖s‖)) * (2 * Real.log (2 + ‖s‖)) :=
          mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hC₁0) hl hl0 (by positivity)
      _ = 4 * C₁ * (1 + ‖s‖) * Real.log (2 + ‖s‖) := by ring

/-! ### Pole weight `β`: the line formula and the Herglotz bridge -/

/-- The Weil function at pole weight `β`: `Φ_lam + (β − 1)(1/s + 1/(s − 1))`. -/
def weilFunctionPole (β : ℝ) (lam : ℕ → ℝ) (s : ℂ) : ℂ :=
  WeilHerglotz.weilFunction lam s + ((β - 1 : ℝ) : ℂ) * gPair 0 s

theorem gPair_zero_conj (s : ℂ) : gPair 0 ((starRingEnd ℂ) s) = (starRingEnd ℂ) (gPair 0 s) := by
  simp [gPair, map_add, map_sub, map_one]

theorem weilFunctionPole_conj (β : ℝ) (lam : ℕ → ℝ) (s : ℂ) :
    weilFunctionPole β lam ((starRingEnd ℂ) s) = (starRingEnd ℂ) (weilFunctionPole β lam s) := by
  simp only [weilFunctionPole, map_add, map_mul, Complex.conj_ofReal, gPair_zero_conj,
    WeilSpectral.weilFunction_conj]

/-- **The Weil functional at pole weight `β` as a line integral** on a line `Re s = c ≥ 3/2` of
absolute convergence. -/
theorem weilPoleWeightFunctional_eq_line {β : ℝ} {lam : ℕ → ℝ} {c : ℝ} (hc : 3 / 2 ≤ c)
    (hsum : LSeriesSummable (WeilHerglotz.lamC lam) c) {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    WeilPoleWeight.weilPoleWeightFunctional β lam (EF.weilTest f f) =
      (1 / (2 * Real.pi) : ℂ) * ∫ t : ℝ, WeilLineAnyAbscissa.lineF (EF.weilTest f f) c t *
        weilFunctionPole β lam (c + t * I) := by
  set k := EF.weilTest f f with hkdef
  have hk : ContDiff ℝ 2 k := EF.weilTest_contDiff hf hf.continuous hfc
  have hkc : HasCompactSupport k := EF.weilTest_hasCompactSupport hfc hfc
  have hc1 : 1 < c := by linarith
  obtain ⟨C, hC0, hC⟩ := WeilLineAnyAbscissa.norm_Hfn_le_wide hk hkc c
  obtain ⟨D, hD0, hD⟩ := WeilLineAnyAbscissa.norm_Hfn_weilTest_le_wide hf hfc c
  obtain ⟨A, hA0, hA⟩ := HerglotzBridgeAnyLine.norm_weilFunction_le_at hc hsum
  set F : ℝ → ℂ := WeilLineAnyAbscissa.lineF k c with hF
  have hcc : |c - 1 / 2| ≤ c := abs_le.mpr ⟨by linarith, by linarith⟩
  set kn : ℝ → ℂ := fun u => k (-u) with hkn
  have hkn2 : ContDiff ℝ 2 kn := hk.comp contDiff_neg
  have hknc : HasCompactSupport kn := hkc.comp_homeomorph (Homeomorph.neg ℝ)
  have hFm : ∀ t : ℝ, Hfn k (1 - c - t * I) = Hfn kn (c + t * I) := fun t => Hfn_mirror k c t
  have hFc : Continuous F := by
    have e : F = fun t : ℝ => Hfn k (c + t * I) + Hfn kn (c + t * I) := by
      funext t
      simp only [hF, WeilLineAnyAbscissa.lineF, hFm]
    rw [e]
    exact (continuous_Hfn_line hk hkc c).add (continuous_Hfn_line hkn2 hknc c)
  have hFb2 : ∀ t : ℝ, ‖F t‖ ≤ 2 * D / (1 + t ^ 2) ^ 2 := by
    intro t
    have e : (1 : ℂ) - c - t * I = ((1 - c : ℝ) : ℂ) + ((-t : ℝ) : ℂ) * I := by push_cast; ring
    simp only [hF, WeilLineAnyAbscissa.lineF]
    refine (norm_add_le _ _).trans ?_
    rw [e]
    have h1 := hD c t hcc
    have h2 := hD (1 - c) (-t) (abs_le.mpr ⟨by linarith, by linarith⟩)
    rw [neg_sq] at h2
    rw [two_mul, add_div]
    exact add_le_add h1 h2
  have hre : ∀ t : ℝ, ((c : ℂ) + t * I).re = c := fun t => by simp
  -- integrability of `F ⋅ Φ_lam` and `F ⋅ g₀` on the line
  have hgc : Continuous (fun t : ℝ => gPair 0 ((c : ℂ) + t * I)) := by
    unfold gPair
    refine Continuous.add ?_ ?_
    · refine continuous_const.div (by fun_prop) fun t h => ?_
      have := congrArg Complex.re h; simp at this; linarith
    · refine continuous_const.div (by fun_prop) fun t h => ?_
      have := congrArg Complex.re h; simp at this; linarith
  have hig : Integrable (fun t : ℝ => F t * gPair 0 (c + t * I)) := by
    refine ((integrable_inv_one_add_sq.const_mul (2 * D)).mul_const (1 / c + 1 / (c - 1))).mono'
      (hFc.mul hgc).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    calc ‖F t‖ * ‖gPair 0 ((c : ℂ) + t * I)‖
        ≤ (2 * D / (1 + t ^ 2) ^ 2) * (1 / c + 1 / (c - 1)) :=
          mul_le_mul (hFb2 t) (WeilAtomic.norm_gPair_zero_le hc1 t) (norm_nonneg _) (by positivity)
      _ ≤ 2 * D * (1 + t ^ 2)⁻¹ * (1 / c + 1 / (c - 1)) := by
          gcongr
          rw [div_le_iff₀ (by positivity)]
          have h1t : (0 : ℝ) < 1 + t ^ 2 := by positivity
          have : 2 * D * (1 + t ^ 2)⁻¹ * (1 + t ^ 2) ^ 2 = 2 * D * (1 + t ^ 2) := by
            field_simp
          rw [this]
          nlinarith [sq_nonneg t]
  have hwc : Continuous fun t : ℝ => WeilHerglotz.weilFunction lam ((c : ℂ) + t * I) := by
    have heq : (fun t : ℝ => WeilHerglotz.weilFunction lam ((c : ℂ) + t * I)) = fun t : ℝ =>
        logDeriv Complex.Gammaℝ ((c : ℂ) + t * I) + gPair 0 ((c : ℂ) + t * I) -
          LSeries (WeilHerglotz.lamC lam) ((c : ℂ) + t * I) := by
      funext t; exact weilFunction_eq lam (by rw [hre]; linarith)
    rw [heq]
    refine (Continuous.add ?_ hgc).sub ?_
    · have heq2 : (fun t : ℝ => logDeriv Complex.Gammaℝ ((c : ℂ) + t * I)) =
          fun t : ℝ => -((Real.log Real.pi : ℝ) : ℂ) / 2 +
            1 / 2 * Complex.digamma (((c : ℂ) + t * I) / 2) := by
        funext t
        exact logDeriv_Gammaℝ (by rw [hre]; linarith)
      rw [heq2]
      refine continuous_const.add (continuous_const.mul ?_)
      refine continuous_iff_continuousAt.mpr fun t => ?_
      exact ((differentiableAt_digamma_of_re_pos (by simp; linarith)).continuousAt).comp
        (by fun_prop)
    · have hcont : ∀ n : ℕ, Continuous (fun t : ℝ =>
          LSeries.term (WeilHerglotz.lamC lam) ((c : ℂ) + t * I) n) := by
        intro n
        rcases eq_or_ne n 0 with rfl | hn
        · simpa [LSeries.term_zero] using continuous_const
        · simp only [LSeries.term_of_ne_zero hn]
          refine continuous_const.div ?_ (fun t => ?_)
          · exact Continuous.const_cpow (by fun_prop) (Or.inl (by exact_mod_cast hn))
          · exact cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast hn))
      exact continuous_tsum hcont hsum.norm fun n t => by
        rw [LSeries.norm_term_eq, LSeries.norm_term_eq]; simp
  have hiw : Integrable (fun t : ℝ => F t * WeilHerglotz.weilFunction lam (c + t * I)) := by
    refine (integrable_inv_one_add_sq.const_mul (4 * D * A)).mono'
      (hFc.mul hwc).aestronglyMeasurable (Eventually.of_forall fun t => ?_)
    rw [norm_mul]
    have hsq : (1 + |t|) ≤ 2 * (1 + t ^ 2) := by nlinarith [sq_abs t, abs_nonneg t]
    calc ‖F t‖ * ‖WeilHerglotz.weilFunction lam ((c : ℂ) + t * I)‖
        ≤ (2 * D / (1 + t ^ 2) ^ 2) * (A * (2 * (1 + t ^ 2))) :=
          mul_le_mul (hFb2 t) ((hA t).trans (by gcongr)) (norm_nonneg _) (by positivity)
      _ = 4 * D * A * (1 + t ^ 2)⁻¹ := by field_simp; ring
  -- the pole part on the line
  have hpole : (1 / (2 * Real.pi) : ℂ) * (∫ t : ℝ, F t * gPair 0 (c + t * I)) =
      paperFT k (I / 2) + paperFT k (-I / 2) := by
    have h := two_line_pair (differentiable_Hfn hk hkc) (c := c) (C := C)
      (fun σ t h1 h2 => hC σ t (abs_le.mpr ⟨by linarith, by linarith⟩)) (z₀ := 0)
      (by simp; linarith) (by simp; linarith)
    rw [sub_zero, Hfn_zero, Hfn_one] at h
    exact h
  have hW := WeilLineAnyAbscissa.weilFullFunctional_weilTest_eq_line hc hsum hf hfc
  rw [WeilPoleWeight.weilPoleWeightFunctional, hW, ← hpole]
  simp only [weilFunctionPole, mul_add]
  rw [integral_add hiw (by simpa [mul_left_comm] using hig.const_mul ((β - 1 : ℝ) : ℂ))]
  simp only [hF]
  rw [show (∫ t : ℝ, WeilLineAnyAbscissa.lineF k c t * (((β - 1 : ℝ) : ℂ) * gPair 0 (c + t * I))) =
      ((β - 1 : ℝ) : ℂ) * ∫ t : ℝ, WeilLineAnyAbscissa.lineF k c t * gPair 0 (c + t * I) by
    rw [← integral_const_mul]; congr 1; funext t; ring]
  push_cast
  ring

/-- A holomorphic `Φ` on `Re s > ½` agreeing with a conjugation-symmetric `G` on `Re s > σ₂` has
real coefficients. -/
theorem herglotz_conj_of_G {G Φ : ℂ → ℂ} {σ₂ : ℝ} (hσ₂ : 1 ≤ σ₂)
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦ : ∀ s : ℂ, σ₂ < s.re → Φ s = G s)
    (hG : ∀ s : ℂ, G ((starRingEnd ℂ) s) = (starRingEnd ℂ) (G s)) {s : ℂ}
    (hs : 1 / 2 < s.re) : Φ ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Φ s) := by
  set U : Set ℂ := {z | 1 / 2 < z.re} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUc : IsPreconnected U := (convex_halfSpace_re_gt (1 / 2)).isPreconnected
  set g : ℂ → ℂ := (starRingEnd ℂ) ∘ Φ ∘ (starRingEnd ℂ) with hg
  have hgd : DifferentiableOn ℂ g U := by
    intro z hz
    have hcz : (starRingEnd ℂ) z ∈ U := by simpa [hU] using hz
    have h := ((hΦd _ hcz).differentiableAt (hUo.mem_nhds hcz)).conj_conj
    rw [Complex.conj_conj] at h
    exact h.differentiableWithinAt
  have h2 : ((σ₂ + 1 : ℝ) : ℂ) ∈ U := show (1 / 2 : ℝ) < ((σ₂ + 1 : ℝ) : ℂ).re by simp; linarith
  have heq : Φ =ᶠ[𝓝 ((σ₂ + 1 : ℝ) : ℂ)] g := by
    have hV : {z : ℂ | σ₂ < z.re} ∈ 𝓝 ((σ₂ + 1 : ℝ) : ℂ) :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by simp)
    filter_upwards [hV] with z hz
    have hz' : σ₂ < ((starRingEnd ℂ) z).re := by simpa using hz
    simp only [hg, Function.comp_apply]
    rw [hΦ z hz, hΦ _ hz', hG z, Complex.conj_conj]
  have hEq := (hΦd.analyticOnNhd hUo).eqOn_of_preconnected_of_eventuallyEq
    (hgd.analyticOnNhd hUo) hUc h2 heq
  have hcs : (starRingEnd ℂ) s ∈ U := by simpa [hU] using hs
  have := hEq hcs
  simp only [hg, Function.comp_apply, Complex.conj_conj] at this
  exact this

/-- **The Herglotz bridge at pole weight `β` for any abscissa of absolute convergence.** -/
theorem weilPoleWeight_nonneg_of_herglotz_abscissa {β : ℝ} {lam : ℕ → ℝ} {σ₂ : ℝ}
    (hsl : ∀ σ : ℝ, σ₂ < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ) {Φ : ℂ → ℂ}
    (hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re})
    (hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re)
    (hΦ : ∀ s : ℂ, σ₂ < s.re → Φ s = weilFunctionPole β lam s)
    {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    0 ≤ (WeilPoleWeight.weilPoleWeightFunctional β lam (EF.weilTest f f)).re := by
  set σ₃ : ℝ := max σ₂ 1 with hσ₃
  have hσ₃1 : 1 ≤ σ₃ := le_max_right _ _
  have hΦ3 : ∀ s : ℂ, σ₃ < s.re → Φ s = weilFunctionPole β lam s := fun s hs =>
    hΦ s ((le_max_left _ _).trans_lt hs)
  set c : ℝ := σ₃ + 1 with hcdef
  have hc : 3 / 2 ≤ c := by linarith
  have hc1 : 1 < c := by linarith
  have hsum : LSeriesSummable (WeilHerglotz.lamC lam) c := by
    refine Summable.of_norm_bounded (hsl c (by linarith [le_max_left σ₂ 1])) fun n => ?_
    rw [LSeries.norm_term_eq]
    split_ifs with h
    · positivity
    · simp only [WeilHerglotz.lamC]
      split_ifs with h2
      · rw [Complex.norm_real, Real.norm_eq_abs, Complex.ofReal_re]
      · simp only [Complex.ofReal_zero, norm_zero, zero_div]
        positivity
  obtain ⟨A, hA0, hA⟩ := HerglotzBridgeAnyLine.norm_weilFunction_le_at hc hsum
  have hAG : ∀ t : ℝ, ‖weilFunctionPole β lam ((c : ℂ) + t * I)‖ ≤
      (A + |β - 1| * (1 / c + 1 / (c - 1))) * (1 + |t|) := by
    intro t
    have h1 : 1 ≤ 1 + |t| := by linarith [abs_nonneg t]
    have hg := WeilAtomic.norm_gPair_zero_le hc1 t
    simp only [weilFunctionPole]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hg0 : 0 ≤ 1 / c + 1 / (c - 1) := by
      have : 0 < c - 1 := by linarith
      positivity
    have hb := mul_le_mul_of_nonneg_left hg (abs_nonneg (β - 1))
    have hb2 : |β - 1| * (1 / c + 1 / (c - 1)) ≤ |β - 1| * (1 / c + 1 / (c - 1)) * (1 + |t|) :=
      le_mul_of_one_le_right (by positivity) h1
    nlinarith [hA t]
  rw [weilPoleWeightFunctional_eq_line hc hsum hf hfc]
  exact HerglotzBridgeAnyLine.re_lineIntegral_nonneg_of_herglotz_at (by linarith)
    (by linarith : σ₃ < c) hΦd hΦre
    (fun s hs => herglotz_conj_of_G hσ₃1 hΦd hΦ3 (weilFunctionPole_conj β lam) hs) hΦ3
    (by positivity) hAG hf hfc

/-! ### The pole-order datum and its rigidity -/

/-- A completed Dirichlet series of degree `d`, conductor one and pole order at most `κ` at
`s = 1`: `Λ(s) = (s(s − 1))^κ Γ_ℝ(s)^d Σ a(n) n^{−s}` entire of finite order, `Λ(1 − s) = Λ(s)`. -/
structure PoleTwinDatum (κ d : ℕ) (a : ℕ → ℝ) (σ₀ : ℝ) (Λ : ℂ → ℂ) : Prop where
  one : a 1 = 1
  summable : ∀ s : ℂ, σ₀ < s.re → LSeriesSummable (cplx a) s
  entire : Differentiable ℂ Λ
  completion : ∀ s : ℂ, σ₀ < s.re →
    Λ s = (s * (s - 1)) ^ κ * Complex.Gammaℝ s ^ d * LSeries (cplx a) s
  functional_equation : ∀ s, Λ (1 - s) = Λ s
  finite_order : ∃ ρ C : ℝ, ∀ s, ‖Λ s‖ ≤ C * Real.exp (‖s‖ ^ ρ)

variable {κ d : ℕ} {a : ℕ → ℝ} {σ₀ : ℝ} {Λ : ℂ → ℂ}

theorem PoleTwinDatum.abscissa_le (hD : PoleTwinDatum κ d a σ₀ Λ) :
    LSeries.abscissaOfAbsConv (cplx a) ≤ σ₀ :=
  LSeries.abscissaOfAbsConv_le_of_forall_lt_LSeriesSummable fun y hy =>
    hD.summable y (by simpa using hy)

/-- With every zero on the critical line, `Re Λ'/Λ ≥ 0` on `Re s > ½`. -/
theorem PoleTwinDatum.re_logDeriv_nonneg (hd : 1 ≤ d) (hD : PoleTwinDatum κ d a σ₀ Λ)
    (hRH : ∀ s, Λ s = 0 → s.re = 1 / 2) {s : ℂ} (hs : 1 / 2 < s.re) :
    0 ≤ (logDeriv Λ s).re := by
  obtain ⟨C, hC0, hC⟩ := orderOneEnvelope_pole hD.entire hD.finite_order (ε := 1) (by simp)
    (fun s => by rw [hD.functional_equation, one_mul]) hd (g := cplx a) hD.summable hD.completion
  have hΛ2 : Λ 2 ≠ 0 := fun h0 => by have := hRH 2 h0; norm_num at this
  have hΛs : Λ s ≠ 0 := fun h0 => by have := hRH s h0; linarith
  have hsum := CompletionZeroPairs.hasSum_logDeriv_zeroPairs hD.entire one_ne_zero
    (fun s => by rw [hD.functional_equation, one_mul]) hC0 hC hΛ2 hΛs
  have hfd : AnalyticOnNhd ℂ (fun z => Λ (z + 2)) univ :=
    (hD.entire.comp (differentiable_id.add_const 2)).differentiableOn.analyticOnNhd isOpen_univ
  refine (Complex.hasSum_re hsum).nonneg fun q => ?_
  set ρ := zeroCopyPoint (fun z => Λ (z + 2)) q + 2 with hρ
  have hz : Λ ρ = 0 := CompletionZeroPairs.apply_zeroCopyPoint hfd q
  have hre : ρ.re = 1 / 2 := hRH ρ hz
  have hw1 : 0 ≤ (s - ρ).re := by rw [Complex.sub_re, hre]; linarith
  have hw2 : 0 ≤ (s - (1 - ρ)).re := by
    rw [Complex.sub_re, Complex.sub_re, Complex.one_re, hre]; linarith
  have key : ∀ w : ℂ, 0 ≤ w.re → 0 ≤ (1 / w).re := fun w hw => by
    rw [one_div, Complex.inv_re]; exact div_nonneg hw (Complex.normSq_nonneg w)
  rw [show (1 / 2 : ℂ) * WeilLineIntegral.gPair ρ s =
    ((1 / 2 : ℝ) : ℂ) * WeilLineIntegral.gPair ρ s by norm_num, Complex.re_ofReal_mul]
  refine mul_nonneg (by norm_num) ?_
  rw [WeilLineIntegral.gPair, Complex.add_re]
  exact add_nonneg (key _ hw1) (key _ hw2)

/-- `Λ'/Λ = κ (1/s + 1/(s − 1)) + d Γ_ℝ'/Γ_ℝ + T'/T` on the half-plane of absolute convergence. -/
theorem PoleTwinDatum.logDeriv_eq (hD : PoleTwinDatum κ d a σ₀ Λ) {s : ℂ} (hs0 : σ₀ < s.re)
    (hs1 : 1 < s.re) (hΛs : Λ s ≠ 0) :
    logDeriv Λ s = κ * WeilLineIntegral.gPair 0 s + d * logDeriv Complex.Gammaℝ s +
      logDeriv (LSeries (cplx a)) s := by
  have hopen : IsOpen {z : ℂ | σ₀ < z.re} := isOpen_lt continuous_const Complex.continuous_re
  have hev : Λ =ᶠ[𝓝 s] fun z => (z * (z - 1)) ^ κ * Complex.Gammaℝ z ^ d * LSeries (cplx a) z := by
    filter_upwards [hopen.mem_nhds hs0] with z hz
    exact hD.completion z hz
  have hsre : 0 < s.re := by linarith
  have hsne0 : s ≠ 0 := fun h0 => by rw [h0] at hs1; norm_num at hs1
  have hsne1 : s - 1 ≠ 0 := fun h0 => by
    rw [sub_eq_zero] at h0; rw [h0] at hs1; norm_num at hs1
  have hp0 : s * (s - 1) ≠ 0 := mul_ne_zero hsne0 hsne1
  have hG0 : Complex.Gammaℝ s ≠ 0 := Complex.Gammaℝ_ne_zero_of_re_pos hsre
  have hGd : DifferentiableAt ℂ Complex.Gammaℝ s := Zeta23.WeilEF.differentiableAt_Gammaℝ hsre
  have hpd : DifferentiableAt ℂ (fun z : ℂ => z * (z - 1)) s :=
    differentiableAt_id.mul (differentiableAt_id.sub_const 1)
  have habs : LSeries.abscissaOfAbsConv (cplx a) < s.re :=
    lt_of_le_of_lt hD.abscissa_le (by exact_mod_cast hs0)
  have hLd : DifferentiableAt ℂ (LSeries (cplx a)) s := (LSeries_hasDerivAt habs).differentiableAt
  have hL0 : LSeries (cplx a) s ≠ 0 := by
    intro h0; apply hΛs; rw [hD.completion s hs0, h0, mul_zero]
  have hlogE : logDeriv Λ s =
      logDeriv (fun z => (z * (z - 1)) ^ κ * Complex.Gammaℝ z ^ d * LSeries (cplx a) z) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hP : logDeriv (fun z : ℂ => (z * (z - 1)) ^ κ) s = κ * logDeriv (fun z : ℂ => z * (z - 1)) s :=
    logDeriv_fun_pow hpd κ
  have hQ : logDeriv (fun z : ℂ => Complex.Gammaℝ z ^ d) s = d * logDeriv Complex.Gammaℝ s :=
    logDeriv_fun_pow hGd d
  have hlogp : logDeriv (fun z : ℂ => z * (z - 1)) s = WeilLineIntegral.gPair 0 s := by
    rw [logDeriv_mul (f := fun z : ℂ => z) (g := fun z : ℂ => z - 1) s hsne0 hsne1
      differentiableAt_id (differentiableAt_id.sub_const 1)]
    rw [logDeriv_apply, logDeriv_apply, deriv_id'', deriv_sub_const, deriv_id'']
    simp [WeilLineIntegral.gPair]
  rw [hlogE, logDeriv_mul (f := fun z => (z * (z - 1)) ^ κ * Complex.Gammaℝ z ^ d)
      (g := LSeries (cplx a)) s (mul_ne_zero (pow_ne_zero _ hp0) (pow_ne_zero _ hG0)) hL0
      ((hpd.pow κ).mul (hGd.pow d)) hLd,
    logDeriv_mul (f := fun z : ℂ => (z * (z - 1)) ^ κ) (g := fun z => Complex.Gammaℝ z ^ d) s
      (pow_ne_zero _ hp0) (pow_ne_zero _ hG0) (hpd.pow κ) (hGd.pow d), hP, hQ, hlogp]

/-- **Pole order rigidity.**  A completed Dirichlet series of degree `d ≥ 1`, conductor one and
pole order `κ`, all of whose zeros lie on the critical line, has `κ = d`, forces the Riemann
hypothesis, and equals `ζ^d`. -/
theorem pole_order_rigidity (hd : 0 < d) (hD : PoleTwinDatum κ d a σ₀ Λ)
    (hRH : ∀ s, Λ s = 0 → s.re = 1 / 2) :
    κ = d ∧ RiemannHypothesis ∧
      ∀ s : ℂ, max σ₀ 1 < s.re → LSeries (cplx a) s = riemannZeta s ^ d := by
  have ha := hD.one
  have hd0 : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  obtain ⟨σ₂, hσ₂1, hσ₂⟩ := exists_tail_le_half (a := a) (σ₁ := σ₀ + 1)
    (hD.summable _ (by simp))
  set σ₃ : ℝ := max σ₂ 2 with hσ₃
  have hσ₃2 : σ₂ ≤ σ₃ := le_max_left _ _
  have hσ₃0 : σ₀ < σ₃ := by linarith [le_max_left σ₂ 2]
  have hσ₃1 : 1 < σ₃ := by linarith [le_max_right σ₂ 2]
  have hdinv : ∀ s : ℂ, σ₃ ≤ s.re → LSeriesSummable (cplx (dinv a ha)) s := fun s hs =>
    (summable_dinv a ha (S := 1 / 2) (by norm_num) (hσ₂ σ₃ hσ₃2)).of_re_le_re (by simpa using hs)
  have hid : ∀ s : ℂ, σ₃ ≤ s.re →
      LSeries (cplx a) s * LSeries (cplx (dinv a ha)) s = 1 ∧
        LSeriesSummable (cplx (lamT a ha)) s ∧
        LSeries (cplx (lamT a ha)) s = -deriv (LSeries (cplx a)) s / LSeries (cplx a) s :=
    fun s hs => lseries_identities a ha (hD.summable s (by linarith)) (hdinv s hs)
      (lt_of_le_of_lt hD.abscissa_le (by exact_mod_cast (show σ₀ < s.re by linarith)))
  set lam : ℕ → ℝ := fun n => lamT a ha n / d with hlam
  have hsl : ∀ σ : ℝ, σ₃ < σ → Summable fun n : ℕ => |lam n| / (n : ℝ) ^ σ := by
    intro σ hσ
    have hsum := ((hid σ (by simp; linarith)).2.1).norm
    refine (hsum.div_const d).congr fun n => ?_
    rcases eq_or_ne n 0 with rfl | hn
    · simp [LSeries.term, hlam, Real.zero_rpow (show σ ≠ 0 by linarith)]
    · rw [norm_term_cplx hn, hlam, abs_div, abs_of_pos hdR, Real.rpow_neg (Nat.cast_nonneg n)]
      field_simp
  set Φ : ℂ → ℂ := fun s => ((1 / d : ℝ) : ℂ) * logDeriv Λ s with hΦ
  have hΛne : ∀ s : ℂ, 1 / 2 < s.re → Λ s ≠ 0 := fun s hs h0 => by
    have := hRH s h0; linarith
  have hΦd : DifferentiableOn ℂ Φ {s : ℂ | 1 / 2 < s.re} := by
    intro s hs
    have hda := (hD.entire.analyticAt s).deriv.differentiableAt
    refine (DifferentiableAt.const_mul ?_ _).differentiableWithinAt
    simp only [logDeriv]
    exact hda.div (hD.entire s) (hΛne s hs)
  have hΦre : ∀ s : ℂ, 1 / 2 < s.re → 0 ≤ (Φ s).re := fun s hs => by
    simp only [hΦ, Complex.re_ofReal_mul]
    exact mul_nonneg (by positivity) (hD.re_logDeriv_nonneg hd hRH hs)
  have hΦeq : ∀ s : ℂ, σ₃ < s.re → Φ s = weilFunctionPole ((κ : ℝ) / d) lam s := by
    intro s hs
    obtain ⟨h1, -, h3⟩ := hid s hs.le
    have hT0 : LSeries (cplx a) s ≠ 0 := fun h0 => by rw [h0, zero_mul] at h1; exact zero_ne_one h1
    have hΛs : Λ s ≠ 0 := hΛne s (by linarith)
    have hlogT : logDeriv (LSeries (cplx a)) s = -LSeries (cplx (lamT a ha)) s := by
      rw [logDeriv_apply, h3]; field_simp
    have hlamC : LSeries (WeilHerglotz.lamC lam) s =
        ((1 / d : ℝ) : ℂ) * LSeries (cplx (lamT a ha)) s := by
      rw [← LSeries_smul]
      refine LSeries_congr (fun {n} hn => ?_) s
      simp only [WeilHerglotz.lamC, Pi.smul_apply, smul_eq_mul, cplx, hlam]
      split_ifs with h2
      · push_cast; ring
      · have hn1 : n = 1 := by omega
        subst hn1
        rw [lamT_one]; simp
    simp only [hΦ, weilFunctionPole]
    rw [hD.logDeriv_eq (by linarith) (by linarith) hΛs, hlogT,
      WeilLineIntegral.weilFunction_eq lam (by linarith), hlamC]
    push_cast
    field_simp
    ring
  have hpos : ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
      0 ≤ (weilDegreePoleFunctional d κ (lamT a ha) (EF.weilTest f f)).re := by
    intro f hf hfc
    rw [weilDegreePoleFunctional_eq_mul hdR.ne', re_ofReal_mul]
    exact mul_nonneg hdR.le (weilPoleWeight_nonneg_of_herglotz_abscissa hsl hΦd hΦre hΦeq hf hfc)
  obtain ⟨hκ, hRHζ, hvM⟩ := (forall_re_weilDegreePoleFunctional_nonneg_iff hdR).mp hpos
  exact ⟨by exact_mod_cast hκ, hRHζ, eq_zetaPow_of_lamT hd ha hD.summable hvM⟩

end RHTower.TwinRigidity

end
