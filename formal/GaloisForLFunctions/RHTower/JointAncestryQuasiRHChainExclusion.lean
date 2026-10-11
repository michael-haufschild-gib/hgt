import GaloisForLFunctions.RHTower.JointAncestryQuasiRHParameters
import GaloisForLFunctions.RHTower.JointAncestryChainPeaks
import GaloisForLFunctions.RHTower.JointAncestryRouteCapstone
import GaloisForLFunctions.RHTower.AnisotropicPhaseRecurrence

/-!
# Off-line chains are impossible below `σ = ½ + Θ` when `Θ < 1`

**Theorem** (`one_add_sSup_le_of_jasDressedPSD_of_chain`).  Suppose every Xi zero satisfies
`Re ρ ≤ ½ + α` with `α < ½`, the off-line zeros form a chain, and the dressed JAS aggregate is
positive semidefinite at `σ`.  Then `σ ≥ 1 + δ*`, where `δ* = sup |Re ρ − ½|`.

With the farthest-zero theorem this gives, under quasi-RH, the bimodal abscissa law
`σ* ∈ {0} ∪ [½ + Θ, 2]` with `Θ = sup Re ρ = ½ + δ*`, and (`riemannHypothesis_iff_jasDressedPSD_one_and_quasi`)

`RH ⟺ JasDressedPSD 1 ∧ ∃ α < ½, XiZeroHalfPlaneBound α`.

**Proof.**  Choose a chain zero within `ε` of the supremal distance and a peak above it whose
height window `|Im ρ − γ| ≤ γ^{c₀}` contains no farther zero.  Test the aggregate with log-weight
Bernoulli vectors centred at the left copy `ξ` of the peak, over the primes in `(n, n²]` with
`n = ⌊γ^{75/θ}⌋`.  The zeros within height `1` of the peak are aligned by simultaneous Dirichlet
approximation in the amplification scale `τ ∈ [τ_unit, 8^K τ_unit]`, so they add to the negative
contribution of the peak; the remaining zeros are suppressed, by the Mertens deficit of the
window sum near the peak, by the shifted Perron formula at larger heights, and by the weight tail
above the cut `T₀`.  The resulting test value is negative, contradicting positivity.
-/

open Complex Filter Real
open scoped ComplexConjugate BigOperators Topology

namespace RHTower

noncomputable section

/-! ## Mertens bounds for the window `(n, n²]` -/

theorem mertensPrimeWeightSum_eq_add_jasLogMass {A B : ℕ} (hAB : A ≤ B) :
    mertensPrimeWeightSum B = mertensPrimeWeightSum A + jasLogMass A B := by
  rw [mertensPrimeWeightSum_eq, mertensPrimeWeightSum_eq, jasLogMass,
    sum_jasPrimeWindow A B (fun n : ℕ => Real.log n / (n : ℝ))]
  have hIcc : ∀ N : ℕ, Finset.Icc 1 N = Finset.Ioc 0 N := fun N => by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter, hIcc, hIcc]
  exact (Finset.sum_Ioc_consecutive _ (Nat.zero_le A) hAB).symm

theorem jasLogMass_le_massHi {n : ℕ} (hn : 1 ≤ n) :
    jasLogMass n (n ^ 2) ≤ jqrMassHi mertensPrimeWindowBound n := by
  have hB : 1 ≤ n ^ 2 := Nat.one_le_pow _ _ hn
  have hsplit := mertensPrimeWeightSum_eq_add_jasLogMass (show n ≤ n ^ 2 from
    Nat.le_self_pow (n := 2) (by norm_num) n)
  have h1 := abs_mertensPrimeWeightSum_sub_log_le (n ^ 2) hB
  have h0 := mertensPrimeWeightSum_nonneg n
  have hlog : Real.log ((n ^ 2 : ℕ) : ℝ) = 2 * Real.log n := by
    push_cast; rw [Real.log_pow]; norm_num
  rw [hlog] at h1
  unfold jqrMassHi
  rw [abs_le] at h1
  linarith [h1.2]

theorem jasLogMass_ge_massLo {n : ℕ} (hn : 1 ≤ n) :
    jqrMassLo mertensPrimeWindowBound n ≤ jasLogMass n (n ^ 2) := by
  have h := jasLogMass_ge hn (Nat.le_self_pow (n := 2) (by norm_num) n)
  have hlog : Real.log ((n ^ 2 : ℕ) : ℝ) = 2 * Real.log n := by
    push_cast; rw [Real.log_pow]; norm_num
  rw [hlog] at h
  unfold jqrMassLo
  linarith

/-! ## Geometry near the target -/

/-- `‖ξ(1−ξ)‖ ≤ (γ + 2)²` for a strip point of height `γ ≥ 0`. -/
theorem norm_mul_one_sub_le {ξ : ℂ} (h0 : 0 ≤ ξ.re) (h1 : ξ.re ≤ 1) (hγ : 0 ≤ ξ.im) :
    ‖ξ * (1 - ξ)‖ ≤ (ξ.im + 2) ^ 2 := by
  rw [norm_mul]
  have e1 := Complex.norm_le_abs_re_add_abs_im ξ
  have e2 := Complex.norm_le_abs_re_add_abs_im (1 - ξ)
  rw [abs_of_nonneg h0, abs_of_nonneg hγ] at e1
  simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, zero_sub,
    abs_neg] at e2
  rw [abs_of_nonneg (by linarith), abs_of_nonneg hγ] at e2
  have := mul_le_mul e1 e2 (norm_nonneg _) (by linarith)
  nlinarith

/-- **The weight ratio near the target.**  For a strip point within height `1` of `ξ`,
`‖w_s/w_ξ − 1‖ ≤ 20/γ` once `γ ≥ 3`. -/
theorem norm_weight_ratio_sub_one_le {ξ s : ℂ} (hξ0 : 0 ≤ ξ.re) (hξ1 : ξ.re ≤ 1 / 2)
    (hs0 : 0 ≤ s.re) (hs1 : s.re ≤ 1 / 2) {γ : ℝ} (hγ : ξ.im = γ) (hγ3 : 3 ≤ γ)
    (hsγ : |s.im - γ| ≤ 1) :
    ‖(1 / (s * (1 - s))) / (1 / (ξ * (1 - ξ))) - 1‖ ≤ 20 / γ := by
  have him : γ - 1 ≤ s.im := by have := abs_le.mp hsγ; linarith
  have hs00 : s * (1 - s) ≠ 0 := by
    intro h
    have := sq_im_le_norm_mul_one_sub s
    rw [h, norm_zero] at this
    nlinarith
  rw [norm_div_weights_sub_one ξ s hs00]
  have hd1 : ‖ξ - s‖ ≤ 2 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.sub_im, hγ]
    have h1 : |ξ.re - s.re| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |γ - s.im| ≤ 1 := by rw [abs_sub_comm]; exact hsγ
    linarith
  have hd2 : ‖1 - ξ - s‖ ≤ 2 * γ + 2 := by
    refine (Complex.norm_le_abs_re_add_abs_im _).trans ?_
    simp only [Complex.sub_re, Complex.one_re, Complex.sub_im, Complex.one_im, hγ]
    have h1 : |1 - ξ.re - s.re| ≤ 1 := abs_le.mpr ⟨by linarith, by linarith⟩
    have h2 : |0 - γ - s.im| ≤ 2 * γ + 1 := by
      rw [abs_le]; have := abs_le.mp hsγ; constructor <;> linarith
    linarith
  have hden : (γ - 1) ^ 2 ≤ ‖s * (1 - s)‖ := by
    have := sq_im_le_norm_mul_one_sub s
    have h' : (γ - 1) ^ 2 ≤ s.im ^ 2 := by nlinarith
    linarith
  have hden0 : 0 < (γ - 1) ^ 2 := by nlinarith
  rw [div_le_div_iff₀ (lt_of_lt_of_le hden0 hden) (by linarith)]
  calc ‖ξ - s‖ * ‖1 - ξ - s‖ * γ ≤ 2 * (2 * γ + 2) * γ := by
        gcongr
    _ ≤ 20 * (γ - 1) ^ 2 := by nlinarith
    _ ≤ 20 * ‖s * (1 - s)‖ := by linarith

/-! ## Dirichlet alignment over a finite set of zeros -/

/-- **Simultaneous alignment.**  For finitely many real frequencies there is a multiplier
`1 ≤ n ≤ 8^K` putting every multiple within `π/4` of `2πℤ`. -/
theorem exists_aligned_multiple_finset (W : Finset XiZeroCopy) (f : XiZeroCopy → ℝ) :
    ∃ n : ℕ, 0 < n ∧ n ≤ 8 ^ W.card ∧
      ∀ q ∈ W, ∃ k : ℤ, |(n : ℝ) * f q - 2 * Real.pi * k| ≤ Real.pi / 4 := by
  obtain ⟨n, hn, hnQ, r, hr⟩ := exists_fin_simultaneous_two_pi_phase_approximation_anisotropic
    (fun i : Fin W.card => f (W.equivFin.symm i)) (fun _ => 8) (fun _ => by norm_num)
  refine ⟨n, hn, by simpa using hnQ, fun q hq => ⟨r (W.equivFin ⟨q, hq⟩), ?_⟩⟩
  have h := hr (W.equivFin ⟨q, hq⟩)
  simp only [Equiv.symm_apply_apply] at h
  calc |(n : ℝ) * f q - 2 * Real.pi * (r (W.equivFin ⟨q, hq⟩) : ℝ)| ≤ 2 * Real.pi / (8 : ℕ) := h
    _ = Real.pi / 4 := by push_cast; ring

/-- The window of zeros within height `1`, as a finite set, has at most
`16(C + log(γ + 4))` elements. -/
theorem card_unit_window_le (γ : ℝ) (hγ : 0 ≤ γ) :
    ((finite_xiOrdinateWindow 1 γ).toFinset.card : ℝ) ≤
      16 * (xiLineTwoLogDerivConstant + Real.log (γ + 4)) := by
  have h := ncard_xiOrdinateWindow_le_log 1 γ
  rw [Set.ncard_eq_toFinset_card _ (finite_xiOrdinateWindow 1 γ), abs_of_nonneg hγ] at h
  linarith

/-- `8^K ≤ e^{34(C + log(γ+4))}` for the unit window. -/
theorem eight_pow_card_le (γ : ℝ) (hγ : 0 ≤ γ) :
    (8 : ℝ) ^ (finite_xiOrdinateWindow 1 γ).toFinset.card ≤
      Real.exp (34 * (xiLineTwoLogDerivConstant + Real.log (γ + 4))) := by
  set K := (finite_xiOrdinateWindow 1 γ).toFinset.card
  have hK := card_unit_window_le γ hγ
  have hlog8 : Real.log 8 ≤ 2.125 := by
    have h2 := Real.log_two_lt_d9
    have : Real.log 8 = 3 * Real.log 2 := by
      rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
    rw [this]; linarith
  have hpow : (8 : ℝ) ^ K = Real.exp (K * Real.log 8) := by
    rw [← Real.exp_log (show (0 : ℝ) < 8 by norm_num), ← Real.exp_nat_mul, Real.exp_log (by norm_num)]
  rw [hpow]
  refine Real.exp_le_exp.mpr ?_
  have hC := xiLineTwoLogDerivConstant_nonneg
  have hl : 0 ≤ Real.log (γ + 4) := Real.log_nonneg (by linarith)
  have hK0 : (0 : ℝ) ≤ K := Nat.cast_nonneg _
  have hl8 : 0 ≤ Real.log 8 := Real.log_nonneg (by norm_num)
  nlinarith

/-! ## The three dominance inequalities in abstract form -/

/-- Suppressed window zeros. -/
theorem dominance_suppressed {a b r W wξ Γ : ℝ} (hW : 0 ≤ W) (hb : b + 2 * r ≤ 1)
    (hΓ : 0 ≤ Γ) (hwξ : 1 / (Γ + 2) ^ 2 ≤ wξ) :
    Real.exp (a - 2 * (28 + Real.log (8 * W * (Γ + 2) ^ 2 + 1)) / 2 + 26 + b + r) * W ≤
      wξ * Real.exp (a - r) / 8 := by
  set D := 8 * W * (Γ + 2) ^ 2 + 1 with hD
  have hD1 : 1 ≤ D := by rw [hD]; nlinarith [sq_nonneg (Γ + 2)]
  have hD0 : 0 < D := by linarith
  have hsplit : Real.exp (a - 2 * (28 + Real.log D) / 2 + 26 + b + r) =
      Real.exp (a - r) * Real.exp (b + 2 * r - 2) * (1 / D) := by
    rw [one_div, ← Real.exp_log hD0, ← Real.exp_neg, ← Real.exp_add, ← Real.exp_add,
      Real.exp_log hD0]
    congr 1; ring
  rw [hsplit]
  have hE : Real.exp (b + 2 * r - 2) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have hEa := Real.exp_pos (a - r)
  have hWD : W / D ≤ 1 / (8 * (Γ + 2) ^ 2) := by
    rw [div_le_div_iff₀ hD0 (by positivity), hD]; nlinarith [sq_nonneg (Γ + 2)]
  have h1 : 1 / (8 * (Γ + 2) ^ 2) ≤ wξ / 8 := by
    rw [mul_comm 8, ← div_div]; linarith
  have hE0 := Real.exp_pos (b + 2 * r - 2)
  have hWD0 : 0 ≤ W / D := div_nonneg hW hD0.le
  calc Real.exp (a - r) * Real.exp (b + 2 * r - 2) * (1 / D) * W
      = Real.exp (a - r) * (Real.exp (b + 2 * r - 2) * (W / D)) := by ring
    _ ≤ Real.exp (a - r) * (1 * (wξ / 8)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hE (hWD.trans h1) hWD0 (by norm_num)) hEa.le
    _ = wξ * Real.exp (a - r) / 8 := by ring

/-- Bulk zeros. -/
theorem dominance_bulk {τ β r M c W wξ Γ : ℝ} (hτ : 0 ≤ τ) (hβ : τ * β ≤ 1 / 100)
    (hr : r ≤ 1 / 100) (hM : 400 ≤ M) (hc : 1 / 2 ≤ c) (hW : 0 ≤ W) (hΓ : 0 ≤ Γ)
    (hwξ : 1 / (Γ + 2) ^ 2 ≤ wξ)
    (hL : 2 * (28 + Real.log (8 * W * (Γ + 2) ^ 2 + 1)) ≤ τ * M / 4) :
    Real.exp (τ * (99 + β) + r) * W ≤ wξ * Real.exp (τ * M * c - r) / 8 := by
  set D := 8 * W * (Γ + 2) ^ 2 + 1 with hD
  have hD1 : 1 ≤ D := by rw [hD]; nlinarith [sq_nonneg (Γ + 2)]
  have hlD := Real.log_nonneg hD1
  have hexp : τ * (99 + β) + r + Real.log D ≤ τ * M * c - r := by
    have h1 : τ * M / 2 ≤ τ * M * c := by nlinarith
    nlinarith
  have hWD : W ≤ D / (8 * (Γ + 2) ^ 2) := by
    rw [le_div_iff₀ (by positivity), hD]; nlinarith [sq_nonneg (Γ + 2)]
  have hD0 : 0 < D := by linarith
  have hwξ0 : 0 ≤ wξ := le_trans (by positivity) hwξ
  have h1 : D / (8 * (Γ + 2) ^ 2) ≤ D * wξ / 8 := by
    rw [mul_comm 8, ← div_div, div_eq_mul_one_div D ((Γ + 2) ^ 2)]
    gcongr
  calc Real.exp (τ * (99 + β) + r) * W ≤ Real.exp (τ * (99 + β) + r) * (D * wξ / 8) :=
        mul_le_mul_of_nonneg_left (hWD.trans h1) (Real.exp_pos _).le
    _ = Real.exp (τ * (99 + β) + r + Real.log D) * wξ / 8 := by
        rw [Real.exp_add (τ * (99 + β) + r) (Real.log D), Real.exp_log hD0]; ring
    _ ≤ Real.exp (τ * M * c - r) * wξ / 8 := by
        gcongr
    _ = wξ * Real.exp (τ * M * c - r) / 8 := by ring

/-- Far zeros above the cut. -/
theorem dominance_far {E a tail Q C r X wξ Γ : ℝ} (hEa : E ≤ a) (ha : 0 ≤ a) (hC : 0 ≤ C)
    (hΓ : 0 ≤ Γ) (htail0 : 0 ≤ tail)
    (htail : tail ≤ 80 * (C + Real.log (3 * Real.exp Q + 4)) / Real.exp Q)
    (hQ : Q = 2 * (a + Real.log (640 * Real.exp 1 * (C + 3) * (Γ + 2) ^ 2)))
    (hwξ : 1 / (Γ + 2) ^ 2 ≤ wξ) (hr : r ≤ 1) (hX : wξ * Real.exp (-r) ≤ X) :
    Real.exp E * tail ≤ X / 8 := by
  set D := 640 * Real.exp 1 * (C + 3) * (Γ + 2) ^ 2 with hD
  have he1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hD1 : 1 ≤ D := by
    have : (1 : ℝ) ≤ (Γ + 2) ^ 2 := by nlinarith
    have : (1 : ℝ) ≤ 640 * Real.exp 1 * (C + 3) := by nlinarith
    rw [hD]; exact one_le_mul_of_one_le_of_one_le this (by nlinarith)
  have hD0 : 0 < D := by linarith
  have hQ0 : 0 ≤ Q := by rw [hQ]; have := Real.log_nonneg hD1; linarith
  have hT : 1 ≤ Real.exp Q := Real.one_le_exp hQ0
  -- `log(3e^Q + 4) ≤ Q + 2`
  have hlog : Real.log (3 * Real.exp Q + 4) ≤ Q + 2 := by
    have h7 : 3 * Real.exp Q + 4 ≤ Real.exp (Q + 2) := by
      rw [Real.exp_add]
      have : (7 : ℝ) ≤ Real.exp 2 := by
        have he := Real.exp_one_gt_d9
        rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]
        nlinarith
      nlinarith
    calc Real.log (3 * Real.exp Q + 4) ≤ Real.log (Real.exp (Q + 2)) :=
          Real.log_le_log (by positivity) h7
      _ = Q + 2 := Real.log_exp _
  -- `C + Q + 2 ≤ (C + 3) e^{Q/2}`
  have hgrow : C + Q + 2 ≤ (C + 3) * Real.exp (Q / 2) := by
    have h1 : Q ≤ Real.exp (Q / 2) := by
      have := Real.quadratic_le_exp_of_nonneg (show 0 ≤ Q / 2 by linarith)
      nlinarith [sq_nonneg (Q / 2 - 1)]
    have h2 : 1 ≤ Real.exp (Q / 2) := Real.one_le_exp (by linarith)
    nlinarith
  have hQsplit : Real.exp Q = Real.exp (Q / 2) * Real.exp (Q / 2) := by
    rw [← Real.exp_add]; ring_nf
  have hhalf : Real.exp (Q / 2) = Real.exp a * D := by
    rw [hQ, show 2 * (a + Real.log D) / 2 = a + Real.log D by ring, Real.exp_add,
      Real.exp_log hD0]
  have hEe : Real.exp E ≤ Real.exp a := Real.exp_le_exp.mpr hEa
  have hX' : 1 / (8 * Real.exp 1 * (Γ + 2) ^ 2) ≤ X / 8 := by
    have h1 : Real.exp (-1) ≤ Real.exp (-r) := Real.exp_le_exp.mpr (by linarith)
    have h2 : 1 / (Γ + 2) ^ 2 * Real.exp (-1) ≤ wξ * Real.exp (-r) :=
      mul_le_mul hwξ h1 (Real.exp_pos _).le (le_trans (by positivity) hwξ)
    have h3 : 1 / (8 * Real.exp 1 * (Γ + 2) ^ 2) = 1 / (Γ + 2) ^ 2 * Real.exp (-1) / 8 := by
      rw [Real.exp_neg]; field_simp
    rw [h3]; linarith
  have hea := Real.exp_pos a
  have hEQ := Real.exp_pos (Q / 2)
  calc Real.exp E * tail ≤ Real.exp a * (80 * (C + (Q + 2)) / Real.exp Q) := by
        refine mul_le_mul hEe (htail.trans ?_) htail0 hea.le
        gcongr
    _ ≤ Real.exp a * (80 * ((C + 3) * Real.exp (Q / 2)) / Real.exp Q) := by
        gcongr
        linarith
    _ = 80 * (C + 3) * (Real.exp a / Real.exp (Q / 2)) := by
        rw [hQsplit]; field_simp
    _ = 80 * (C + 3) / D := by
        rw [hhalf]; field_simp
    _ = 1 / (8 * Real.exp 1 * (Γ + 2) ^ 2) := by
        rw [hD]; field_simp; ring
    _ ≤ X / 8 := hX'

/-! ## The bulk hypothesis -/

/-- **Bulk zeros have window sums at most `99`.** -/
theorem bulk_window_sum_le {ξ : ℂ} {δt ε γ c₀ σ₁ η K Q : ℝ} {n : ℕ} (hn : 2 ≤ n)
    (hPer : ∀ z : ℂ, z ≠ 0 → -1 / 8 < z.re → z.re ≤ 1 - σ₁ - η → z.re ≤ 1 / 8 →
      ‖jasLogWeightSum n (n ^ 2) z -
          (((((n ^ 2 : ℕ) : ℝ) + 1 / 2 : ℝ) : ℂ) ^ z - ((((n : ℕ) : ℝ) + 1 / 2 : ℝ) : ℂ) ^ z) / z‖
        ≤ K * ((((n : ℕ) : ℝ) + 1 / 2) ^ (σ₁ - (1 - z.re)) *
              (1 + Real.log (((n : ℕ) : ℝ) + 1 / 2 + |z.im| + 9)) ^ 2 +
            (((n ^ 2 : ℕ) : ℝ) + 1 / 2) ^ (σ₁ - (1 - z.re)) *
              (1 + Real.log (((n ^ 2 : ℕ) : ℝ) + 1 / 2 + |z.im| + 9)) ^ 2) + 96)
    (hδ : ξ.re = 1 / 2 - δt) (hγ : ξ.im = γ) (hγ1 : 1 ≤ γ) (hc₀ : 0 ≤ c₀)
    (hε8 : ε ≤ 1 / 8) (hεσ : ε ≤ 1 - σ₁ - η) (hσε : σ₁ - 1 + ε ≤ 0) (hK : 0 ≤ K)
    (hγc : (((n ^ 2 : ℕ) : ℝ) + 1 / 2) ^ ε ≤ γ ^ c₀)
    (hiso : ∀ q : XiZeroCopy, |(q.1 : ℂ).im - γ| ≤ γ ^ c₀ → |(q.1 : ℂ).re - 1 / 2| ≤ δt)
    (hstrip : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ δt + ε)
    (herr : 2 * K * ((n : ℝ) + 1 / 2) ^ (σ₁ - 1 + ε) * (Q + 2) ^ 2 ≤ 1)
    (hcut : 2 * ((n : ℝ) ^ 2 + γ + 10) ≤ Real.exp Q)
    (htriv : Real.exp (-(1 / 8) * Real.log (n + 1)) * jasLogMass n (n ^ 2) ≤ 99) :
    ∀ q : XiZeroCopy, 1 < |(q.1 : ℂ).im - γ| → |(q.1 : ℂ).im| ≤ Real.exp Q →
      ‖jasLogWeightSum n (n ^ 2) (ξ - jasLeftRep q.1)‖ ≤ 99 := by
  intro q hq1 hqT
  have hzim : (ξ - jasLeftRep (q.1 : ℂ)).im = γ - (q.1 : ℂ).im := by
    rw [Complex.sub_im, jasLeftRep_im, hγ]
  have hzre : (ξ - jasLeftRep (q.1 : ℂ)).re ≤ ε := (jasLeftRep_shifts hδ (hstrip q)).1
  have hzim1 : 1 ≤ |(ξ - jasLeftRep (q.1 : ℂ)).im| := by rw [hzim, abs_sub_comm]; linarith
  have hn0 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hB : ((n ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ 2 := by push_cast; ring
  have hnB : ((n : ℕ) : ℝ) + 1 / 2 ≤ ((n ^ 2 : ℕ) : ℝ) + 1 / 2 := by rw [hB]; nlinarith
  have hγc1 : 1 ≤ γ ^ c₀ := Real.one_le_rpow hγ1 hc₀
  set w := (ξ - jasLeftRep (q.1 : ℂ)).re with hw
  -- the main term
  have hmain : ((((n ^ 2 : ℕ) : ℝ) + 1 / 2) ^ w + (((n : ℕ) : ℝ) + 1 / 2) ^ w) /
      |(ξ - jasLeftRep (q.1 : ℂ)).im| ≤ 2 := by
    rw [div_le_iff₀ (by linarith)]
    rcases le_or_gt |(q.1 : ℂ).im - γ| (γ ^ c₀) with hwin | hwin
    · have hz0 : w ≤ 0 := by
        rw [hw, Complex.sub_re, jasLeftRep_re, hδ]; linarith [hiso q hwin]
      have h1 : (((n ^ 2 : ℕ) : ℝ) + 1 / 2) ^ w ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hz0
      have h2 : (((n : ℕ) : ℝ) + 1 / 2) ^ w ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (by linarith) hz0
      linarith
    · have hzw : γ ^ c₀ < |(ξ - jasLeftRep (q.1 : ℂ)).im| := by
        rw [hzim, abs_sub_comm]; exact hwin
      have h1 : (((n ^ 2 : ℕ) : ℝ) + 1 / 2) ^ w ≤ γ ^ c₀ :=
        (Real.rpow_le_rpow_of_exponent_le (by linarith) hzre).trans hγc
      have h2 : (((n : ℕ) : ℝ) + 1 / 2) ^ w ≤ γ ^ c₀ := by
        rcases le_or_gt w 0 with h0 | h0
        · exact (Real.rpow_le_one_of_one_le_of_nonpos (by linarith) h0).trans hγc1
        · exact (Real.rpow_le_rpow (by linarith) hnB h0.le).trans h1
      nlinarith
  -- the Perron error
  have herr' : K * ((((n : ℕ) : ℝ) + 1 / 2) ^ (σ₁ - (1 - w)) *
        (1 + Real.log (((n : ℕ) : ℝ) + 1 / 2 + |(ξ - jasLeftRep (q.1 : ℂ)).im| + 9)) ^ 2 +
      (((n ^ 2 : ℕ) : ℝ) + 1 / 2) ^ (σ₁ - (1 - w)) *
        (1 + Real.log (((n ^ 2 : ℕ) : ℝ) + 1 / 2 + |(ξ - jasLeftRep (q.1 : ℂ)).im| + 9)) ^ 2) ≤
      1 := by
    have hP1 : (((n : ℕ) : ℝ) + 1 / 2) ^ (σ₁ - (1 - w)) ≤ ((n : ℝ) + 1 / 2) ^ (σ₁ - 1 + ε) :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have hP2 : (((n ^ 2 : ℕ) : ℝ) + 1 / 2) ^ (σ₁ - (1 - w)) ≤ ((n : ℝ) + 1 / 2) ^ (σ₁ - 1 + ε) :=
      (Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)).trans
        (Real.rpow_le_rpow_of_nonpos (by linarith) hnB hσε)
    have himT : |(ξ - jasLeftRep (q.1 : ℂ)).im| ≤ γ + Real.exp Q := by
      rw [hzim]
      calc |γ - (q.1 : ℂ).im| ≤ |γ| + |(q.1 : ℂ).im| := abs_sub _ _
        _ ≤ γ + Real.exp Q := by rw [abs_of_nonneg (by linarith)]; linarith
    have hQ0 : 0 ≤ Q := by
      by_contra h
      push Not at h
      have : Real.exp Q < 1 := Real.exp_lt_one_iff.mpr h
      nlinarith
    have hlogB : 1 + Real.log (((n ^ 2 : ℕ) : ℝ) + 1 / 2 + |(ξ - jasLeftRep (q.1 : ℂ)).im| + 9) ≤
        Q + 2 := by
      have h1 : ((n ^ 2 : ℕ) : ℝ) + 1 / 2 + |(ξ - jasLeftRep (q.1 : ℂ)).im| + 9 ≤
          2 * Real.exp Q := by rw [hB]; linarith
      have h2 := Real.log_le_log (by positivity) h1
      rw [Real.log_mul (by norm_num) (Real.exp_pos Q).ne', Real.log_exp] at h2
      have := Real.log_two_lt_d9
      linarith
    have hlogA : 1 + Real.log (((n : ℕ) : ℝ) + 1 / 2 + |(ξ - jasLeftRep (q.1 : ℂ)).im| + 9) ≤
        Q + 2 := by
      refine le_trans ?_ hlogB
      have := Real.log_le_log (by positivity)
        (show ((n : ℕ) : ℝ) + 1 / 2 + |(ξ - jasLeftRep (q.1 : ℂ)).im| + 9 ≤
          ((n ^ 2 : ℕ) : ℝ) + 1 / 2 + |(ξ - jasLeftRep (q.1 : ℂ)).im| + 9 by linarith)
      linarith
    have hl0A : 0 ≤ 1 + Real.log (((n : ℕ) : ℝ) + 1 / 2 + |(ξ - jasLeftRep (q.1 : ℂ)).im| + 9) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ ((n : ℕ) : ℝ) + 1 / 2 +
        |(ξ - jasLeftRep (q.1 : ℂ)).im| + 9 by
          have := abs_nonneg (ξ - jasLeftRep (q.1 : ℂ)).im; linarith)
      linarith
    have hl0B : 0 ≤ 1 + Real.log (((n ^ 2 : ℕ) : ℝ) + 1 / 2 +
        |(ξ - jasLeftRep (q.1 : ℂ)).im| + 9) := by
      have := Real.log_nonneg (show (1 : ℝ) ≤ ((n ^ 2 : ℕ) : ℝ) + 1 / 2 +
        |(ξ - jasLeftRep (q.1 : ℂ)).im| + 9 by
          have := abs_nonneg (ξ - jasLeftRep (q.1 : ℂ)).im
          have : (0 : ℝ) ≤ ((n ^ 2 : ℕ) : ℝ) := Nat.cast_nonneg _
          linarith)
      linarith
    have hsqA := pow_le_pow_left₀ hl0A hlogA 2
    have hsqB := pow_le_pow_left₀ hl0B hlogB 2
    have hPpos : 0 ≤ ((n : ℝ) + 1 / 2) ^ (σ₁ - 1 + ε) := Real.rpow_nonneg (by linarith) _
    calc K * ((((n : ℕ) : ℝ) + 1 / 2) ^ (σ₁ - (1 - w)) *
          (1 + Real.log (((n : ℕ) : ℝ) + 1 / 2 + |(ξ - jasLeftRep (q.1 : ℂ)).im| + 9)) ^ 2 +
        (((n ^ 2 : ℕ) : ℝ) + 1 / 2) ^ (σ₁ - (1 - w)) *
          (1 + Real.log (((n ^ 2 : ℕ) : ℝ) + 1 / 2 + |(ξ - jasLeftRep (q.1 : ℂ)).im| + 9)) ^ 2)
        ≤ K * (((n : ℝ) + 1 / 2) ^ (σ₁ - 1 + ε) * (Q + 2) ^ 2 +
            ((n : ℝ) + 1 / 2) ^ (σ₁ - 1 + ε) * (Q + 2) ^ 2) := by
          gcongr
      _ = 2 * K * ((n : ℝ) + 1 / 2) ^ (σ₁ - 1 + ε) * (Q + 2) ^ 2 := by ring
      _ ≤ 1 := herr
  have hz0 : ξ - jasLeftRep (q.1 : ℂ) ≠ 0 := by
    intro h; rw [h, Complex.zero_im, abs_zero] at hzim1; linarith
  exact norm_jasLogWeightSum_le_of_far (hPer (ξ - jasLeftRep (q.1 : ℂ))) hzim1 hzre hεσ hε8 hmain
    herr' htriv

/-! ## The cluster budget -/

/-- **The phase budget of the cluster.** -/
theorem cluster_budget_le {τ τu τm φ M Mlo L₀ lam0 β r γ c : ℝ} (hτm : 0 < τm) (hτmu : τm ≤ τu)
    (hτu : τu ≤ τ) (hMlo : 0 < Mlo) (hMM : Mlo ≤ M) (hsin0 : 0 ≤ Real.sin φ)
    (hsM : τ * Real.sin φ * M ≤ 4 * Real.pi) (hL₀ : 0 ≤ L₀) (hlam : lam0 = L₀ / (τu * M))
    (h4L : 4 * L₀ ≤ τm * Mlo) (hb : (230 + 4 * Real.pi * L₀) / (τm * Mlo) ≤ Real.pi / 8)
    (hβ : τ * β ≤ 1 / 100) (hr : r ≤ 1 / 100) (hc : c ≤ 20 / γ)
    (hg : 40 / γ ≤ Real.pi / 8 - 3 / 100) :
    2 * c + τ * Real.sin φ ^ 2 * (M * Real.sqrt (2 * lam0)) + τ * Real.sin φ * M * lam0 +
      2 * (τ * β) + r ≤ Real.pi / 4 := by
  have hM : 0 < M := lt_of_lt_of_le hMlo hMM
  have hτ : 0 < τ := lt_of_lt_of_le hτm (hτmu.trans hτu)
  have hτu0 : 0 < τu := lt_of_lt_of_le hτm hτmu
  have hD : 0 < τm * Mlo := mul_pos hτm hMlo
  have hDle : τm * Mlo ≤ τ * M := mul_le_mul (hτmu.trans hτu) hMM hMlo.le hτ.le
  have hDle' : τm * Mlo ≤ τu * M := mul_le_mul hτmu hMM hMlo.le hτu0.le
  -- `lam0 ≤ L₀/(τm Mlo) ≤ 1/4`
  have hlam1 : lam0 ≤ L₀ / (τm * Mlo) := by
    rw [hlam]; exact div_le_div_of_nonneg_left hL₀ hD hDle'
  have hlam14 : lam0 ≤ 1 / 4 := by
    have : L₀ / (τm * Mlo) ≤ 1 / 4 := by rw [div_le_iff₀ hD]; linarith
    linarith
  have hlam0 : 0 ≤ lam0 := by rw [hlam]; positivity
  -- `sin φ ≤ 4π/(τ M)`
  have hsin : Real.sin φ ≤ 4 * Real.pi / (τm * Mlo) := by
    have h1 : Real.sin φ ≤ 4 * Real.pi / (τ * M) := by
      rw [le_div_iff₀ (mul_pos hτ hM)]; linarith
    exact h1.trans (div_le_div_of_nonneg_left (by positivity) hD hDle)
  have hsq : Real.sqrt (2 * lam0) ≤ 1 := by
    rw [Real.sqrt_le_left (by norm_num)]; nlinarith
  have hpi : Real.pi < 3.1416 := Real.pi_lt_d4
  have hterm1 : τ * Real.sin φ ^ 2 * (M * Real.sqrt (2 * lam0)) ≤ 230 / (τm * Mlo) := by
    have e : τ * Real.sin φ ^ 2 * (M * Real.sqrt (2 * lam0)) =
        (τ * Real.sin φ * M) * Real.sin φ * Real.sqrt (2 * lam0) := by ring
    rw [e]
    have hs0 : 0 ≤ Real.sqrt (2 * lam0) := Real.sqrt_nonneg _
    calc (τ * Real.sin φ * M) * Real.sin φ * Real.sqrt (2 * lam0)
        ≤ (4 * Real.pi) * (4 * Real.pi / (τm * Mlo)) * 1 := by
          gcongr
    _ = 16 * Real.pi ^ 2 / (τm * Mlo) := by ring
    _ ≤ 230 / (τm * Mlo) := by
        gcongr; nlinarith [Real.pi_pos]
  have hterm2 : τ * Real.sin φ * M * lam0 ≤ 4 * Real.pi * L₀ / (τm * Mlo) := by
    calc τ * Real.sin φ * M * lam0 ≤ 4 * Real.pi * (L₀ / (τm * Mlo)) :=
          mul_le_mul hsM hlam1 hlam0 (by positivity)
      _ = 4 * Real.pi * L₀ / (τm * Mlo) := by ring
  have hsum : 230 / (τm * Mlo) + 4 * Real.pi * L₀ / (τm * Mlo) ≤ Real.pi / 8 := by
    rw [← add_div]; exact hb
  have h2c : 2 * c ≤ 40 / γ := by
    rw [show (40 : ℝ) / γ = 2 * (20 / γ) by ring]; linarith
  linarith

/-! ## Scale and twist -/

/-- **Scale and twist.**  Given the window and the target, there is a scale `τ ∈ [τ_unit, τ_max]`,
`τ_unit ≥ τ_min`, at which all window zeros near the target are aligned, and a twist `φ` putting
the target at phase `π`. -/
theorem exists_aligned_scale_twist {ξ : ℂ} {γ θ τmin M SB : ℝ} {n : ℕ} (hγ0 : 0 ≤ γ)
    (hγΓ : γ ≤ jqrHeight θ n)
    (hτmin : τmin = jqrScaleMin θ xiLineTwoLogDerivConstant n) (hτmin0 : 0 < τmin)
    (hM : 0 < M) (hSB : SB ≤ M / 2) (hτM : 32 * Real.pi ≤ τmin * M) :
    ∃ τu τ φ : ℝ, τmin ≤ τu ∧ τu ≤ τ ∧ τ ≤ ((n : ℝ) + 1) ^ θ ∧
      (∀ q : XiZeroCopy, |(q.1 : ℂ).im - γ| ≤ 1 → ∃ k : ℤ,
        |τ * (jasLogWeightSum n (n ^ 2) (ξ - jasLeftRep q.1)).im - 2 * Real.pi * k| ≤
          Real.pi / 4) ∧
      0 ≤ φ ∧ φ ≤ Real.pi / 2 ∧ 1 / 2 ≤ Real.cos φ ∧ 0 ≤ Real.sin φ ∧
      (1 / (ξ * (1 - ξ))).arg + τ * (M - SB) * Real.sin φ = Real.pi ∧
      τ * M * Real.sin φ ≤ 4 * Real.pi := by
  classical
  set W₁ := (finite_xiOrdinateWindow 1 γ).toFinset with hW₁
  set τmax : ℝ := ((n : ℝ) + 1) ^ θ with hτmax
  set τu : ℝ := τmax / 8 ^ W₁.card with hτu
  have h8 : (0 : ℝ) < 8 ^ W₁.card := by positivity
  have hτu_ge : τmin ≤ τu := by
    rw [hτmin, hτu, jqrScaleMin, jqrScaleMax, le_div_iff₀ h8]
    have h1 := eight_pow_card_le γ hγ0
    have h2 : Real.exp (34 * (xiLineTwoLogDerivConstant + Real.log (γ + 4))) ≤
        Real.exp (34 * (xiLineTwoLogDerivConstant + Real.log (jqrHeight θ n + 4))) := by
      refine Real.exp_le_exp.mpr ?_
      have := Real.log_le_log (by linarith) (show γ + 4 ≤ jqrHeight θ n + 4 by linarith)
      linarith
    have hE : Real.exp (-(34 * (xiLineTwoLogDerivConstant + Real.log (jqrHeight θ n + 4)))) *
        Real.exp (34 * (xiLineTwoLogDerivConstant + Real.log (jqrHeight θ n + 4))) = 1 := by
      rw [← Real.exp_add]; simp
    have hτ0 : 0 ≤ ((n : ℝ) + 1) ^ θ := Real.rpow_nonneg (by positivity) _
    calc ((n : ℝ) + 1) ^ θ *
          Real.exp (-(34 * (xiLineTwoLogDerivConstant + Real.log (jqrHeight θ n + 4)))) *
          8 ^ W₁.card
        ≤ ((n : ℝ) + 1) ^ θ *
          Real.exp (-(34 * (xiLineTwoLogDerivConstant + Real.log (jqrHeight θ n + 4)))) *
          Real.exp (34 * (xiLineTwoLogDerivConstant + Real.log (jqrHeight θ n + 4))) := by
          gcongr
          exact h1.trans h2
      _ = ((n : ℝ) + 1) ^ θ := by rw [mul_assoc, hE, mul_one]
  have hτu0 : 0 < τu := lt_of_lt_of_le hτmin0 hτu_ge
  obtain ⟨nD, hnD0, hnD8, halign⟩ := exists_aligned_multiple_finset W₁
    (fun q => τu * (jasLogWeightSum n (n ^ 2) (ξ - jasLeftRep q.1)).im)
  set τ : ℝ := nD * τu with hτdef
  have hnD1 : (1 : ℝ) ≤ nD := by exact_mod_cast hnD0
  have hτu_le : τu ≤ τ := by rw [hτdef]; nlinarith
  have hτ_le : τ ≤ τmax := by
    rw [hτdef, hτu, mul_div_assoc', div_le_iff₀ h8]
    have : (nD : ℝ) ≤ 8 ^ W₁.card := by exact_mod_cast hnD8
    have hτmax0 : 0 ≤ τmax := Real.rpow_nonneg (by positivity) _
    nlinarith
  have hτ0 : 0 < τ := lt_of_lt_of_le hτu0 hτu_le
  -- the twist
  set w := 1 / (ξ * (1 - ξ)) with hw
  set cφ : ℝ := Real.pi - w.arg with hcφ
  have hcφ0 : 0 ≤ cφ := by rw [hcφ]; linarith [Complex.arg_le_pi w]
  have hcφ2 : cφ ≤ 2 * Real.pi := by rw [hcφ]; linarith [Complex.neg_pi_lt_arg w]
  have hMS : 0 < M - SB := by linarith
  have hMS2 : M / 2 ≤ M - SB := by linarith
  set u : ℝ := cφ / (τ * (M - SB)) with hu
  have hτMS : 16 * Real.pi ≤ τ * (M - SB) := by
    have h1 : τmin * M ≤ τ * M := mul_le_mul_of_nonneg_right (hτu_ge.trans hτu_le) hM.le
    have h2 : τ * (M / 2) ≤ τ * (M - SB) := mul_le_mul_of_nonneg_left hMS2 hτ0.le
    nlinarith
  have hu0 : 0 ≤ u := div_nonneg hcφ0 (by positivity)
  have hu2 : u ≤ 1 / 2 := by
    rw [hu, div_le_iff₀ (by positivity)]; nlinarith [Real.pi_pos]
  set φ : ℝ := Real.arcsin u with hφ
  have hsin : Real.sin φ = u := Real.sin_arcsin (by linarith) (by linarith)
  have hφ0 : 0 ≤ φ := Real.arcsin_nonneg.mpr hu0
  have hφ1 : φ ≤ Real.pi / 2 := Real.arcsin_le_pi_div_two u
  have hcos : 1 / 2 ≤ Real.cos φ := by
    rw [hφ, Real.cos_arcsin]
    rw [Real.le_sqrt (by norm_num) (by nlinarith)]
    nlinarith
  refine ⟨τu, τ, φ, hτu_ge, hτu_le, hτ_le, ?_, hφ0, hφ1, hcos, by rw [hsin]; exact hu0, ?_, ?_⟩
  · intro q hq
    have hmem : q ∈ W₁ := by rw [hW₁, Set.Finite.mem_toFinset]; exact hq
    obtain ⟨k, hk⟩ := halign q hmem
    refine ⟨k, ?_⟩
    have : τ * (jasLogWeightSum n (n ^ 2) (ξ - jasLeftRep q.1)).im =
        (nD : ℝ) * (τu * (jasLogWeightSum n (n ^ 2) (ξ - jasLeftRep q.1)).im) := by
      rw [hτdef]; ring
    rw [this]; exact hk
  · rw [hsin, hu]
    have : τ * (M - SB) * (cφ / (τ * (M - SB))) = cφ := by field_simp
    rw [this, hcφ]; ring
  · rw [hsin, hu]
    have hk : τ * M * (cφ / (τ * (M - SB))) = cφ * (M / (M - SB)) := by field_simp
    rw [hk]
    have : M / (M - SB) ≤ 2 := by rw [div_le_iff₀ hMS]; linarith
    nlinarith

/-! ## Small consequences of the window conditions -/

theorem gamma_ge_forty {n : ℕ} {θ γ : ℝ} (hnγ : (n : ℝ) ^ (θ / 75) ≤ γ)
    (c12 : 40 / (Real.pi / 8 - 3 / 100) ≤ (n : ℝ) ^ (θ / 75)) :
    40 ≤ γ ∧ 40 / γ ≤ Real.pi / 8 - 3 / 100 := by
  have hpi3 := Real.pi_gt_three
  have hd : 0 < Real.pi / 8 - 3 / 100 := by linarith
  have h1 : (40 : ℝ) ≤ 40 / (Real.pi / 8 - 3 / 100) := by
    rw [le_div_iff₀ hd]; nlinarith [Real.pi_lt_d4]
  have hγ : 40 ≤ γ := by linarith
  refine ⟨hγ, ?_⟩
  rw [div_le_iff₀ (by linarith)]
  have h2 : 40 / (Real.pi / 8 - 3 / 100) ≤ γ := le_trans c12 hnγ
  rw [div_le_iff₀ hd] at h2
  linarith

/-- The mirror sum at the target is at most half the mass. -/
theorem mirror_sum_le_half {n : ℕ} {ξ : ℂ} {δt δS : ℝ} (hδt : ξ.re = 1 / 2 - δt)
    (hδt1 : δS / 2 ≤ δt) (hδS : 0 < δS) (c9 : Real.exp (-δS * Real.log (n + 1)) ≤ 1 / 2) :
    ∑ p ∈ jasPrimeWindow n (n ^ 2), Real.log p / p * Real.exp ((2 * ξ.re - 1) * Real.log p) ≤
      jasLogMass n (n ^ 2) / 2 := by
  have hSB0 := jasLogWeightSum_ofReal_nonneg n (n ^ 2) (2 * ξ.re - 1)
  have hre : ((2 * ξ.re - 1 : ℝ) : ℂ).re = 2 * ξ.re - 1 := by simp
  have hneg : ((2 * ξ.re - 1 : ℝ) : ℂ).re ≤ 0 := by rw [hre, hδt]; linarith
  have h := norm_jasLogWeightSum_le_of_re_nonpos (A := n) (B := n ^ 2) hneg
  rw [jasLogWeightSum_ofReal, Complex.norm_real, Real.norm_of_nonneg hSB0, hre] at h
  refine h.trans ?_
  have hl : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith [(n.cast_nonneg : (0:ℝ) ≤ n)])
  have hE : Real.exp ((2 * ξ.re - 1) * Real.log ((n : ℝ) + 1)) ≤ 1 / 2 := by
    refine le_trans (Real.exp_le_exp.mpr ?_) c9
    rw [hδt]; nlinarith
  have hM := jasLogMass_nonneg n (n ^ 2)
  nlinarith

/-- **Admissibility of the log-weight test.** -/
theorem admissible_of_window {n : ℕ} {ξ : ℂ} {τ θ δt σ : ℝ} (hn : 3 ≤ (n : ℝ))
    (hτmax : τ ≤ ((n : ℝ) + 1) ^ θ) (hδt : ξ.re = 1 / 2 - δt) (hσ : σ - δt - 1 ≤ -(2 * θ))
    (hθ : 0 ≤ θ)
    (c8 : ((n : ℝ) + 1) ^ θ * (2 * Real.log n) * Real.exp (-(2 * θ) * Real.log (n + 1)) ≤ 1 / 2) :
    ∀ p ∈ jasPrimeWindow n (n ^ 2),
      τ * (Real.log p / p) * Real.exp ((ξ.re + (σ - 1 / 2)) * Real.log p) ≤ 1 / 2 := by
  intro p hp
  have hBcast : ((n ^ 2 : ℕ) : ℝ) = (n : ℝ) ^ 2 := by push_cast; ring
  have hpw := mem_jasPrimeWindow.mp hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast p.2.pos
  have hpA : (n : ℝ) + 1 ≤ p := by exact_mod_cast hpw.1
  have hpB : (p : ℝ) ≤ (n : ℝ) ^ 2 := by rw [← hBcast]; exact_mod_cast hpw.2
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
  have hlp : Real.log p ≤ 2 * Real.log n := by
    have := Real.log_le_log hp0 hpB
    rwa [Real.log_pow, Nat.cast_ofNat] at this
  have hl1 := Real.log_le_log (by linarith) hpA
  have hl0 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have h1 : Real.log p / p * Real.exp ((ξ.re + (σ - 1 / 2)) * Real.log p) =
      Real.log p * Real.exp ((σ - δt - 1) * Real.log p) := by
    rw [show (σ - δt - 1) * Real.log p = (ξ.re + (σ - 1 / 2)) * Real.log p + -Real.log p by
      rw [hδt]; ring, Real.exp_add, Real.exp_neg, Real.exp_log hp0]
    ring
  have hexp : Real.log p / p * Real.exp ((ξ.re + (σ - 1 / 2)) * Real.log p) ≤
      2 * Real.log n * Real.exp (-(2 * θ) * Real.log ((n : ℝ) + 1)) := by
    rw [h1]
    refine mul_le_mul hlp (Real.exp_le_exp.mpr ?_) (Real.exp_pos _).le (by linarith)
    nlinarith
  have hpos : 0 ≤ Real.log p / p * Real.exp ((ξ.re + (σ - 1 / 2)) * Real.log p) := by positivity
  calc τ * (Real.log p / p) * Real.exp ((ξ.re + (σ - 1 / 2)) * Real.log p)
      = τ * (Real.log p / p * Real.exp ((ξ.re + (σ - 1 / 2)) * Real.log p)) := by ring
    _ ≤ ((n : ℝ) + 1) ^ θ * (2 * Real.log n * Real.exp (-(2 * θ) * Real.log ((n : ℝ) + 1))) :=
        mul_le_mul hτmax hexp hpos (Real.rpow_nonneg (by linarith) _)
    _ ≤ 1 / 2 := by rw [← mul_assoc]; exact c8

/-- The deviation, remainder and mirror conditions at a scale `τ ≤ τ_max`. -/
theorem small_terms_of_window {n : ℕ} {τ θ ε δt δS : ℝ} (hn : 3 ≤ (n : ℝ)) (hτ0 : 0 ≤ τ)
    (hτmax : τ ≤ ((n : ℝ) + 1) ^ θ) (hδt1 : δS / 2 ≤ δt)
    (hMhi : jasLogMass n (n ^ 2) ≤ jqrMassHi mertensPrimeWindowBound n)
    (c5 : 2 * ((n : ℝ) + 1) ^ θ * (2 * Real.log n) * Real.exp ((ε - 1) * Real.log (n + 1)) ≤ 1 / 2)
    (c6 : 16 * (((n : ℝ) + 1) ^ θ) ^ 2 * (2 * Real.log n) ^ 2 / Real.sqrt n ≤ 1 / 100)
    (c7 : ((n : ℝ) + 1) ^ θ * (Real.exp (-(δS / 2) * Real.log (n + 1)) *
      jqrMassHi mertensPrimeWindowBound n) ≤ 1 / 100) :
    2 * τ * Real.log ((n ^ 2 : ℕ) : ℝ) * Real.exp ((ε - 1) * Real.log ((n : ℕ) + 1)) ≤ 1 / 2 ∧
      16 * τ ^ 2 * Real.log ((n ^ 2 : ℕ) : ℝ) ^ 2 / Real.sqrt (n : ℕ) ≤ 1 / 100 ∧
      τ * (Real.exp (-δt * Real.log ((n : ℕ) + 1)) * jasLogMass n (n ^ 2)) ≤ 1 / 100 := by
  have hlogB : Real.log ((n ^ 2 : ℕ) : ℝ) = 2 * Real.log n := by
    push_cast; rw [Real.log_pow]; norm_num
  have hl : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by linarith)
  have hl1 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
  have hsq : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by linarith)
  rw [hlogB]
  refine ⟨?_, ?_, ?_⟩
  · refine le_trans ?_ c5
    have hE := (Real.exp_pos ((ε - 1) * Real.log ((n : ℝ) + 1))).le
    have : 0 ≤ 2 * Real.log (n : ℝ) := by linarith
    calc 2 * τ * (2 * Real.log n) * Real.exp ((ε - 1) * Real.log ((n : ℕ) + 1))
        = 2 * (2 * Real.log n) * Real.exp ((ε - 1) * Real.log ((n : ℝ) + 1)) * τ := by
          ring
      _ ≤ 2 * (2 * Real.log n) * Real.exp ((ε - 1) * Real.log ((n : ℝ) + 1)) *
            ((n : ℝ) + 1) ^ θ := by gcongr
      _ = _ := by ring
  · refine le_trans ?_ c6
    have hτsq : τ ^ 2 ≤ (((n : ℝ) + 1) ^ θ) ^ 2 := pow_le_pow_left₀ hτ0 hτmax 2
    gcongr
  · refine le_trans ?_ c7
    have hE1 : Real.exp (-δt * Real.log ((n : ℝ) + 1)) ≤ Real.exp (-(δS / 2) * Real.log ((n : ℝ) + 1)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hM0 := jasLogMass_nonneg n (n ^ 2)
    calc τ * (Real.exp (-δt * Real.log ((n : ℝ) + 1)) * jasLogMass n (n ^ 2))
        ≤ ((n : ℝ) + 1) ^ θ * (Real.exp (-(δS / 2) * Real.log ((n : ℝ) + 1)) *
            jqrMassHi mertensPrimeWindowBound n) := by
          gcongr

/-- **The cluster hypothesis.** -/
theorem cluster_hyp_of_window {n : ℕ} {ξ : ℂ} {δt γ τ τu τm φ L₀ Mlo : ℝ}
    (hδt : ξ.re = 1 / 2 - δt) (hδt0 : 0 < δt) (hδth : δt < 1 / 2) (hγ : ξ.im = γ)
    (hγ40 : 40 ≤ γ) (hg : 40 / γ ≤ Real.pi / 8 - 3 / 100)
    (hτm : 0 < τm) (hτmu : τm ≤ τu) (hτu : τu ≤ τ) (hMlo : 0 < Mlo)
    (hMM : Mlo ≤ jasLogMass n (n ^ 2)) (hsin0 : 0 ≤ Real.sin φ)
    (hsM : τ * jasLogMass n (n ^ 2) * Real.sin φ ≤ 4 * Real.pi) (hL₀ : 0 ≤ L₀)
    (h4L : 4 * L₀ ≤ τm * Mlo) (hb : (230 + 4 * Real.pi * L₀) / (τm * Mlo) ≤ Real.pi / 8)
    (hβ : τ * (Real.exp (-δt * Real.log ((n : ℕ) + 1)) * jasLogMass n (n ^ 2)) ≤ 1 / 100)
    (hr : 16 * τ ^ 2 * Real.log ((n ^ 2 : ℕ) : ℝ) ^ 2 / Real.sqrt (n : ℕ) ≤ 1 / 100)
    (q : XiZeroCopy) (hq : |(q.1 : ℂ).im - γ| ≤ 1) :
    ‖(1 / (jasLeftRep q.1 * (1 - jasLeftRep q.1))) / (1 / (ξ * (1 - ξ))) - 1‖ ≤ 1 / 2 ∧
      2 * ‖(1 / (jasLeftRep q.1 * (1 - jasLeftRep q.1))) / (1 / (ξ * (1 - ξ))) - 1‖ +
        τ * Real.sin φ ^ 2 * (jasLogMass n (n ^ 2) *
          Real.sqrt (2 * (L₀ / (τu * jasLogMass n (n ^ 2))))) +
        τ * Real.sin φ * jasLogMass n (n ^ 2) * (L₀ / (τu * jasLogMass n (n ^ 2))) +
        2 * (τ * (Real.exp (-δt * Real.log ((n : ℕ) + 1)) * jasLogMass n (n ^ 2))) +
        16 * τ ^ 2 * Real.log ((n ^ 2 : ℕ) : ℝ) ^ 2 / Real.sqrt (n : ℕ) ≤ Real.pi / 4 := by
  have hstrip := xi_zero_re_mem_open_unit (xi_xiZeroCopy_eq_zero q)
  have hsre := jasLeftRep_re (q.1 : ℂ)
  have habs : |(q.1 : ℂ).re - 1 / 2| < 1 / 2 :=
    abs_lt.mpr ⟨by linarith [hstrip.1], by linarith [hstrip.2]⟩
  have hc := norm_weight_ratio_sub_one_le (ξ := ξ) (s := jasLeftRep q.1) (by linarith)
    (by linarith) (by rw [hsre]; linarith)
    (by rw [hsre]; linarith [abs_nonneg ((q.1 : ℂ).re - 1 / 2)])
    hγ (by linarith) (by rw [jasLeftRep_im]; exact hq)
  have hc2 : 20 / γ ≤ 1 / 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  refine ⟨hc.trans hc2, ?_⟩
  have := cluster_budget_le (τ := τ) (τu := τu) (τm := τm) (φ := φ) (M := jasLogMass n (n ^ 2))
    (Mlo := Mlo) (L₀ := L₀) (lam0 := L₀ / (τu * jasLogMass n (n ^ 2)))
    (β := Real.exp (-δt * Real.log ((n : ℕ) + 1)) * jasLogMass n (n ^ 2))
    (r := 16 * τ ^ 2 * Real.log ((n ^ 2 : ℕ) : ℝ) ^ 2 / Real.sqrt (n : ℕ))
    (γ := γ) (c := ‖(1 / (jasLeftRep q.1 * (1 - jasLeftRep q.1))) / (1 / (ξ * (1 - ξ))) - 1‖)
    hτm hτmu hτu hMlo hMM hsin0 (by linarith [hsM]) hL₀ rfl h4L hb hβ hr hc hg
  linarith

/-- `‖w_ξ‖ ≥ 1/(Γ + 2)²` at a target of height `γ ≤ Γ`. -/
theorem norm_weight_target_ge {ξ : ℂ} {δt γ Γ : ℝ} (hδt : ξ.re = 1 / 2 - δt) (hδt0 : 0 < δt)
    (hδth : δt < 1 / 2) (hγ : ξ.im = γ) (hγ1 : 1 ≤ γ) (hγΓ : γ ≤ Γ) :
    1 / (Γ + 2) ^ 2 ≤ ‖1 / (ξ * (1 - ξ))‖ := by
  have hξ00 : ξ * (1 - ξ) ≠ 0 := by
    intro h
    have := sq_im_le_norm_mul_one_sub ξ
    rw [h, norm_zero, hγ] at this
    nlinarith
  have hle := norm_mul_one_sub_le (ξ := ξ) (by rw [hδt]; linarith) (by rw [hδt]; linarith)
    (by rw [hγ]; linarith)
  rw [hγ] at hle
  rw [norm_div, norm_one]
  have h0 : 0 < ‖ξ * (1 - ξ)‖ := norm_pos_iff.mpr hξ00
  calc 1 / (Γ + 2) ^ 2 ≤ 1 / (γ + 2) ^ 2 := by
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith
    _ ≤ 1 / ‖ξ * (1 - ξ)‖ := one_div_le_one_div_of_le h0 hle

/-- **The three dominance hypotheses on the window `(n, n²]`.** -/
theorem dominance_hyps_of_window {n : ℕ} {ξ : ℂ} {δt γ θ ε τ φ τm : ℝ}
    (hδt : ξ.re = 1 / 2 - δt) (hδt0 : 0 < δt) (hδth : δt < 1 / 2) (hγ : ξ.im = γ) (hγ1 : 1 ≤ γ)
    (hγΓ : γ ≤ jqrHeight θ n) (hτ0 : 0 ≤ τ)
    (hτmax : τ ≤ ((n : ℝ) + 1) ^ θ) (hcos : 1 / 2 ≤ Real.cos φ) (hn : 3 ≤ (n : ℝ))
    (hM400 : 400 ≤ jasLogMass n (n ^ 2))
    (hMhi : jasLogMass n (n ^ 2) ≤ jqrMassHi mertensPrimeWindowBound n)
    (hβ : τ * (Real.exp (-δt * Real.log ((n : ℕ) + 1)) * jasLogMass n (n ^ 2)) ≤ 1 / 100)
    (hr : 16 * τ ^ 2 * Real.log ((n ^ 2 : ℕ) : ℝ) ^ 2 / Real.sqrt (n : ℕ) ≤ 1 / 100)
    (hτm : τm ≤ τ)
    (hL : 4 * jqrThreshold θ (∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) n ≤
      τm * jqrMassLo mertensPrimeWindowBound n)
    (hMlo0 : 0 ≤ jqrMassLo mertensPrimeWindowBound n)
    (hMlo : jqrMassLo mertensPrimeWindowBound n ≤ jasLogMass n (n ^ 2)) :
    Real.exp (τ * jasLogMass n (n ^ 2) * Real.cos φ -
        jqrThreshold θ (∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) n / 2 + 26 +
        τ * (Real.exp (-δt * Real.log ((n : ℕ) + 1)) * jasLogMass n (n ^ 2)) +
        16 * τ ^ 2 * Real.log ((n ^ 2 : ℕ) : ℝ) ^ 2 / Real.sqrt (n : ℕ)) *
        (∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) ≤
      ‖1 / (ξ * (1 - ξ))‖ * Real.exp (τ * jasLogMass n (n ^ 2) * Real.cos φ -
        16 * τ ^ 2 * Real.log ((n ^ 2 : ℕ) : ℝ) ^ 2 / Real.sqrt (n : ℕ)) / 8 ∧
    Real.exp (τ * (99 + Real.exp (-δt * Real.log ((n : ℕ) + 1)) * jasLogMass n (n ^ 2)) +
        16 * τ ^ 2 * Real.log ((n ^ 2 : ℕ) : ℝ) ^ 2 / Real.sqrt (n : ℕ)) *
        (∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) ≤
      ‖1 / (ξ * (1 - ξ))‖ * Real.exp (τ * jasLogMass n (n ^ 2) * Real.cos φ -
        16 * τ ^ 2 * Real.log ((n ^ 2 : ℕ) : ℝ) ^ 2 / Real.sqrt (n : ℕ)) / 8 ∧
    Real.exp (τ * (Real.exp (ε * Real.log ((n ^ 2 : ℕ) : ℝ)) * jasLogMass n (n ^ 2) +
          Real.exp (-δt * Real.log ((n : ℕ) + 1)) * jasLogMass n (n ^ 2)) +
        16 * τ ^ 2 * Real.log ((n ^ 2 : ℕ) : ℝ) ^ 2 / Real.sqrt (n : ℕ)) *
        (∑' q : XiZeroCopy, {q : XiZeroCopy |
          Real.exp (jqrCut θ ε mertensPrimeWindowBound xiLineTwoLogDerivConstant n) <
            |(q.1 : ℂ).im|}.indicator (fun q => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) q) ≤
      ‖1 / (ξ * (1 - ξ))‖ * Real.exp (τ * jasLogMass n (n ^ 2) * Real.cos φ -
        16 * τ ^ 2 * Real.log ((n ^ 2 : ℕ) : ℝ) ^ 2 / Real.sqrt (n : ℕ)) / 8 := by
  have hW0 : 0 ≤ ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
    tsum_nonneg fun q => norm_nonneg _
  have hΓ0 : 0 ≤ jqrHeight θ n := le_trans (by linarith) hγΓ
  have hwξ := norm_weight_target_ge hδt hδt0 hδth hγ hγ1 hγΓ
  have hM0 : 0 < jasLogMass n (n ^ 2) := by linarith
  have hτM : τm * jqrMassLo mertensPrimeWindowBound n ≤ τ * jasLogMass n (n ^ 2) :=
    mul_le_mul hτm hMlo hMlo0 hτ0
  have hr0 : 0 ≤ 16 * τ ^ 2 * Real.log ((n ^ 2 : ℕ) : ℝ) ^ 2 / Real.sqrt (n : ℕ) := by positivity
  have hβ0 : 0 ≤ τ * (Real.exp (-δt * Real.log ((n : ℕ) + 1)) * jasLogMass n (n ^ 2)) := by
    positivity
  refine ⟨?_, ?_, ?_⟩
  · have h := dominance_suppressed (a := τ * jasLogMass n (n ^ 2) * Real.cos φ)
      (b := τ * (Real.exp (-δt * Real.log ((n : ℕ) + 1)) * jasLogMass n (n ^ 2)))
      (r := 16 * τ ^ 2 * Real.log ((n ^ 2 : ℕ) : ℝ) ^ 2 / Real.sqrt (n : ℕ))
      (W := ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖)
      (wξ := ‖1 / (ξ * (1 - ξ))‖) (Γ := jqrHeight θ n) hW0 (by linarith) hΓ0 hwξ
    unfold jqrThreshold
    exact h
  · refine dominance_bulk hτ0 hβ (by linarith) hM400 hcos hW0 hΓ0 hwξ ?_
    have h4 := hL.trans hτM
    unfold jqrThreshold at h4
    linarith
  · have hlogB : Real.log ((n ^ 2 : ℕ) : ℝ) = 2 * Real.log n := by
      push_cast; rw [Real.log_pow]; norm_num
    have hl1 : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
    have hE1 : Real.exp (-δt * Real.log ((n : ℕ) + 1)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    have hMhi0 : 0 ≤ jqrMassHi mertensPrimeWindowBound n := by linarith
    have hEa : τ * (Real.exp (ε * Real.log ((n ^ 2 : ℕ) : ℝ)) * jasLogMass n (n ^ 2) +
          Real.exp (-δt * Real.log ((n : ℕ) + 1)) * jasLogMass n (n ^ 2)) +
        16 * τ ^ 2 * Real.log ((n ^ 2 : ℕ) : ℝ) ^ 2 / Real.sqrt (n : ℕ) ≤
        jqrFarExponent θ ε mertensPrimeWindowBound n := by
      unfold jqrFarExponent jqrScaleMax
      rw [hlogB, show ε * (2 * Real.log n) = 2 * ε * Real.log n by ring]
      have hβM : Real.exp (-δt * Real.log ((n : ℕ) + 1)) * jasLogMass n (n ^ 2) ≤
          jqrMassHi mertensPrimeWindowBound n := by nlinarith
      have hEM : Real.exp (2 * ε * Real.log n) * jasLogMass n (n ^ 2) ≤
          Real.exp (2 * ε * Real.log n) * jqrMassHi mertensPrimeWindowBound n :=
        mul_le_mul_of_nonneg_left hMhi (Real.exp_pos _).le
      have hin : 0 ≤ Real.exp (2 * ε * Real.log n) * jasLogMass n (n ^ 2) +
          Real.exp (-δt * Real.log ((n : ℕ) + 1)) * jasLogMass n (n ^ 2) := by positivity
      have h2 := mul_le_mul hτmax (add_le_add hEM hβM) hin (Real.rpow_nonneg (by linarith) _)
      have hr' := hr
      rw [hlogB] at hr'
      linarith
    have hfar0 : 0 ≤ jqrFarExponent θ ε mertensPrimeWindowBound n := by
      unfold jqrFarExponent jqrScaleMax; positivity
    have hT1 : 1 ≤ Real.exp (jqrCut θ ε mertensPrimeWindowBound xiLineTwoLogDerivConstant n) := by
      refine Real.one_le_exp ?_
      unfold jqrCut
      have := Real.log_nonneg (show (1 : ℝ) ≤ 640 * Real.exp 1 * (xiLineTwoLogDerivConstant + 3) *
          (jqrHeight θ n + 2) ^ 2 by
        have he : (1 : ℝ) ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
        have hC := xiLineTwoLogDerivConstant_nonneg
        have h3 : (1 : ℝ) ≤ 640 * Real.exp 1 * (xiLineTwoLogDerivConstant + 3) := by nlinarith
        have h4 : (1 : ℝ) ≤ (jqrHeight θ n + 2) ^ 2 := by nlinarith
        exact one_le_mul_of_one_le_of_one_le h3 h4)
      linarith
    have htail := tsum_indicator_abs_im_gt_weight_le hT1
    have htail0 : 0 ≤ ∑' q : XiZeroCopy, {q : XiZeroCopy |
        Real.exp (jqrCut θ ε mertensPrimeWindowBound xiLineTwoLogDerivConstant n) <
          |(q.1 : ℂ).im|}.indicator (fun q => ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) q :=
      tsum_nonneg fun q => Set.indicator_nonneg (fun q _ => norm_nonneg _) q
    refine dominance_far (r := 16 * τ ^ 2 * Real.log ((n ^ 2 : ℕ) : ℝ) ^ 2 / Real.sqrt (n : ℕ))
      hEa hfar0 xiLineTwoLogDerivConstant_nonneg hΓ0 htail0 htail rfl hwξ (by linarith) ?_
    have hc0 : 0 ≤ τ * jasLogMass n (n ^ 2) * Real.cos φ := by
      have : 0 ≤ Real.cos φ := by linarith
      positivity
    have hexp := Real.exp_le_exp.mpr (show -(16 * τ ^ 2 * Real.log ((n ^ 2 : ℕ) : ℝ) ^ 2 /
        Real.sqrt (n : ℕ)) ≤ τ * jasLogMass n (n ^ 2) * Real.cos φ -
          16 * τ ^ 2 * Real.log ((n ^ 2 : ℕ) : ℝ) ^ 2 / Real.sqrt (n : ℕ) by linarith)
    exact mul_le_mul_of_nonneg_left hexp (norm_nonneg _)

theorem jqrThreshold_nonneg {θ W x : ℝ} (hW : 0 ≤ W) : 0 ≤ jqrThreshold θ W x := by
  unfold jqrThreshold
  have := Real.log_nonneg (show (1 : ℝ) ≤ 8 * W * (jqrHeight θ x + 2) ^ 2 + 1 by
    have : 0 ≤ 8 * W * (jqrHeight θ x + 2) ^ 2 := by positivity
    linarith)
  linarith

theorem threshold_le_scaled {L τ τu M : ℝ} (hL : 0 ≤ L) (hτu : 0 < τu) (hτ : τu ≤ τ) (hM : 0 < M) :
    L ≤ τ * M * (L / (τu * M)) := by
  rw [show τ * M * (L / (τu * M)) = (τ / τu) * L by field_simp]
  have : 1 ≤ τ / τu := by rw [le_div_iff₀ hτu]; linarith
  nlinarith

/-- The window edge against the target height: `(n² + ½)^ε ≤ γ^{c₀}` when `γ ≥ n^{θ/75}` and
`c₀ θ = 300 ε`. -/
theorem window_pow_le_height_pow {n : ℕ} {θ ε c₀ γ : ℝ} (hn : 2 ≤ (n : ℝ))
    (hε : 0 ≤ ε) (hc₀ : 0 ≤ c₀) (hεc : c₀ * θ = 300 * ε) (hnγ : (n : ℝ) ^ (θ / 75) ≤ γ) :
    (((n ^ 2 : ℕ) : ℝ) + 1 / 2) ^ ε ≤ γ ^ c₀ := by
  have hn0 : 0 < (n : ℝ) := by linarith
  have h1 : ((n : ℝ) ^ (θ / 75)) ^ c₀ ≤ γ ^ c₀ :=
    Real.rpow_le_rpow (Real.rpow_nonneg hn0.le _) hnγ hc₀
  have h2 : ((n : ℝ) ^ (θ / 75)) ^ c₀ = ((n : ℝ) ^ 4) ^ ε := by
    rw [← Real.rpow_mul hn0.le, ← Real.rpow_natCast, ← Real.rpow_mul hn0.le]
    congr 1
    push_cast
    linear_combination hεc / 75
  have h3 : (((n ^ 2 : ℕ) : ℝ) + 1 / 2) ^ ε ≤ ((n : ℝ) ^ 4) ^ ε := by
    refine Real.rpow_le_rpow (by positivity) ?_ hε
    push_cast
    have h4 : (4 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
    nlinarith
  linarith

/-! ## The negative test at a target -/

/-- **The negative test at a target.**  At a target with the window conditions, some admissible
log-weight Bernoulli test has negative real part. -/
theorem exists_neg_test_at_target {θ ε c₀ σ₁ η K δS : ℝ} (hθ0 : 0 < θ) (hθσ : θ ≤ (1 - σ₁) / 20)
    (hε0 : 0 < ε) (hεθ : ε ≤ θ) (hεc : c₀ * θ = 300 * ε) (hσ₁0 : 0 ≤ σ₁) (hσ₁ : σ₁ < 1)
    (hη : η = (1 - σ₁) / 4) (hc₀ : 0 ≤ c₀) (hK : 0 ≤ K) (hδS : 0 < δS) (hδSh : δS < 1 / 2)
    (hPer : ∀ A B : ℕ, 1 ≤ A → A ≤ B → ∀ z : ℂ, z ≠ 0 → -1 / 8 < z.re →
      z.re ≤ 1 - σ₁ - η → z.re ≤ 1 / 8 →
        ‖jasLogWeightSum A B z -
            (((((B : ℝ) + 1 / 2 : ℝ) : ℂ) ^ z - (((A : ℝ) + 1 / 2 : ℝ) : ℂ) ^ z) / z)‖
          ≤ K * (((A : ℝ) + 1 / 2) ^ (σ₁ - (1 - z.re)) *
                (1 + Real.log ((A : ℝ) + 1 / 2 + |z.im| + 9)) ^ 2 +
              ((B : ℝ) + 1 / 2) ^ (σ₁ - (1 - z.re)) *
                (1 + Real.log ((B : ℝ) + 1 / 2 + |z.im| + 9)) ^ 2) + 96)
    (qt : XiZeroCopy) {ξ : ℂ} {δt γ : ℝ} (hqt : jasLeftRep (qt.1 : ℂ) = ξ)
    (hδt : ξ.re = 1 / 2 - δt) (hδt1 : δS / 2 ≤ δt) (hδt2 : δt ≤ δS) (hγ : ξ.im = γ)
    (hstrip : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ δt + ε)
    (hiso : ∀ q : XiZeroCopy, |(q.1 : ℂ).im - γ| ≤ γ ^ c₀ → |(q.1 : ℂ).re - 1 / 2| ≤ δt)
    {n : ℕ} (hnγ : (n : ℝ) ^ (θ / 75) ≤ γ) (hγΓ : γ ≤ jqrHeight θ n)
    (c1 : 3 ≤ (n : ℝ)) (c2 : 400 ≤ jqrMassLo mertensPrimeWindowBound n)
    (c3 : Real.exp (-(1 / 8) * Real.log (n + 1)) * jqrMassHi mertensPrimeWindowBound n ≤ 99)
    (c4 : 2 * K * ((n : ℝ) + 1 / 2) ^ (σ₁ - 1 + ε) *
      (jqrCut θ ε mertensPrimeWindowBound xiLineTwoLogDerivConstant n + 2) ^ 2 ≤ 1)
    (c5 : 2 * ((n : ℝ) + 1) ^ θ * (2 * Real.log n) * Real.exp ((ε - 1) * Real.log (n + 1)) ≤ 1 / 2)
    (c6 : 16 * (((n : ℝ) + 1) ^ θ) ^ 2 * (2 * Real.log n) ^ 2 / Real.sqrt n ≤ 1 / 100)
    (c7 : ((n : ℝ) + 1) ^ θ * (Real.exp (-(δS / 2) * Real.log (n + 1)) *
      jqrMassHi mertensPrimeWindowBound n) ≤ 1 / 100)
    (c8 : ((n : ℝ) + 1) ^ θ * (2 * Real.log n) * Real.exp (-(2 * θ) * Real.log (n + 1)) ≤ 1 / 2)
    (c9 : Real.exp (-δS * Real.log (n + 1)) ≤ 1 / 2)
    (c10 : 32 * Real.pi ≤ jqrScaleMin θ xiLineTwoLogDerivConstant n *
        jqrMassLo mertensPrimeWindowBound n ∧
      4 * jqrThreshold θ (∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) n ≤
        jqrScaleMin θ xiLineTwoLogDerivConstant n * jqrMassLo mertensPrimeWindowBound n ∧
      (230 + 4 * Real.pi * jqrThreshold θ (∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) n) /
          (jqrScaleMin θ xiLineTwoLogDerivConstant n * jqrMassLo mertensPrimeWindowBound n) ≤
        Real.pi / 8)
    (c11 : 2 * ((n : ℝ) ^ 2 + jqrHeight θ n + 10) ≤
      Real.exp (jqrCut θ ε mertensPrimeWindowBound xiLineTwoLogDerivConstant n))
    (c12 : 40 / (Real.pi / 8 - 3 / 100) ≤ (n : ℝ) ^ (θ / 75))
    {σ : ℝ} (hσ : σ - δt - 1 ≤ -(2 * θ)) :
    ∃ τ φ : ℝ, 0 ≤ τ ∧
      (∀ p ∈ jasPrimeWindow n (n ^ 2),
        τ * (Real.log p / p) * Real.exp ((ξ.re + (σ - 1 / 2)) * Real.log p) ≤ 1 / 2) ∧
      (∑' q : XiZeroCopy, jasLogWeightValue ξ n (n ^ 2) τ φ (q.1 : ℂ)).re < 0 := by
  classical
  have hn1 : 1 ≤ n := by exact_mod_cast (show (1 : ℝ) ≤ n by linarith only [c1])
  have hnB : n ≤ n ^ 2 := Nat.le_self_pow (n := 2) (by norm_num) n
  have hδt0 : 0 < δt := by linarith only [hδt1, hδS]
  have hδth : δt < 1 / 2 := by linarith only [hδt2, hδSh]
  obtain ⟨hγ40, hg⟩ := gamma_ge_forty hnγ c12
  have hγ0 : 0 ≤ γ := by linarith only [hγ40]
  have hγ1 : 1 ≤ γ := by linarith only [hγ40]
  have hMlo := jasLogMass_ge_massLo hn1
  have hMhi := jasLogMass_le_massHi hn1
  have hM400 : 400 ≤ jasLogMass n (n ^ 2) := le_trans c2 hMlo
  have hM0 : 0 < jasLogMass n (n ^ 2) := by linarith only [hM400]
  have hSB := mirror_sum_le_half hδt hδt1 hδS c9
  have hτmin0 : 0 < jqrScaleMin θ xiLineTwoLogDerivConstant n := by
    unfold jqrScaleMin jqrScaleMax; positivity
  have hτM : 32 * Real.pi ≤ jqrScaleMin θ xiLineTwoLogDerivConstant n * jasLogMass n (n ^ 2) :=
    c10.1.trans (mul_le_mul_of_nonneg_left hMlo hτmin0.le)
  obtain ⟨τu, τ, φ, hτu, hτuτ, hτmax, halign, hφ0, hφ1, hcos, hsin0, harg, hsinM⟩ :=
    exists_aligned_scale_twist (ξ := ξ) hγ0 hγΓ rfl hτmin0 hM0 hSB hτM
  have hτ0 : 0 ≤ τ := le_trans (le_trans hτmin0.le hτu) hτuτ
  have hτu0 : 0 < τu := lt_of_lt_of_le hτmin0 hτu
  obtain ⟨hdev, hr, hβ⟩ := small_terms_of_window c1 hτ0 hτmax hδt1 hMhi c5 c6 c7
  refine ⟨τ, φ, hτ0, admissible_of_window c1 hτmax hδt hσ hθ0.le c8, ?_⟩
  have hMlo0 : 0 < jqrMassLo mertensPrimeWindowBound n := by linarith only [c2]
  have hW0 : 0 ≤ ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
    tsum_nonneg fun q => norm_nonneg _
  have hL₀ := jqrThreshold_nonneg (θ := θ) (x := n) hW0
  have hcl := cluster_hyp_of_window (n := n) hδt hδt0 hδth hγ hγ40 hg hτmin0 hτu hτuτ hMlo0
    hMlo hsin0 hsinM hL₀ c10.2.1 c10.2.2 hβ hr
  obtain ⟨hY₁, hY₂, hY₄⟩ := dominance_hyps_of_window (ε := ε) hδt hδt0 hδth hγ hγ1 hγΓ hτ0 hτmax
    hcos c1 hM400 hMhi hβ hr (le_trans hτu hτuτ) c10.2.1 hMlo0.le hMlo
  have hn2 : 2 ≤ n := by exact_mod_cast (show (2 : ℝ) ≤ n by linarith only [c1])
  have hθ1 : θ ≤ 1 / 20 := by linarith only [hθσ, hσ₁0]
  have hγc := window_pow_le_height_pow (by linarith only [c1]) hε0.le hc₀ hεc hnγ
  have hcut : 2 * ((n : ℝ) ^ 2 + γ + 10) ≤
      Real.exp (jqrCut θ ε mertensPrimeWindowBound xiLineTwoLogDerivConstant n) := by
    linarith only [c11, hγΓ]
  have htriv : Real.exp (-(1 / 8) * Real.log (n + 1)) * jasLogMass n (n ^ 2) ≤ 99 :=
    le_trans (mul_le_mul_of_nonneg_left hMhi (Real.exp_pos _).le) c3
  have hbulk := bulk_window_sum_le (n := n) hn2 (hPer n (n ^ 2) hn1 hnB) hδt hγ hγ1 hc₀
    (by linarith only [hεθ, hθ1]) (by rw [hη]; linarith only [hεθ, hθσ, hσ₁])
    (by linarith only [hεθ, hθσ, hσ₁]) hK hγc hiso hstrip c4 hcut htriv
  have hwin : ∀ q : XiZeroCopy, |(q.1 : ℂ).im - γ| ≤ 1 → |(q.1 : ℂ).re - 1 / 2| ≤ δt :=
    fun q hq => hiso q (le_trans hq (Real.one_le_rpow hγ1 hc₀))
  have hwξ : 1 / (ξ * (1 - ξ)) ≠ 0 := by
    have := norm_weight_target_ge (Γ := γ) hδt hδt0 hδth hγ hγ1 le_rfl
    intro h; rw [h, norm_zero] at this
    have : 0 < 1 / (γ + 2) ^ 2 := by positivity
    linarith
  have hsin13 : τ * jasLogMass n (n ^ 2) * Real.sin φ ≤ 13 :=
    le_trans hsinM (by linarith only [Real.pi_lt_d2])
  have hL := threshold_le_scaled hL₀ hτu0 hτuτ hM0
  exact re_tsum_jasLogWeightValue_neg hδt hδt0 qt hqt hstrip hwin hn1 hnB hτ0 hε0.le
    (by linarith only [hεθ, hθ1]) hφ0 hφ1 hcos hdev hM0 (by linarith only [hr]) hwξ harg hsin13 hL
    (fun q hq _ => halign q hq) hcl hbulk rfl rfl rfl rfl hY₁ hY₂ hY₄

/-! ## Window from the height -/

/-- The window index `n = ⌊γ^{75/θ}⌋` brackets the height: `n^{θ/75} ≤ γ ≤ (n+1)^{θ/75}`. -/
theorem window_index_brackets {θ γ : ℝ} (hθ : 0 < θ) (hγ : 0 ≤ γ) :
    ((⌊γ ^ (75 / θ)⌋₊ : ℕ) : ℝ) ^ (θ / 75) ≤ γ ∧ γ ≤ jqrHeight θ (⌊γ ^ (75 / θ)⌋₊ : ℕ) := by
  have hp : 0 ≤ γ ^ (75 / θ) := Real.rpow_nonneg hγ _
  have hfl := Nat.floor_le hp
  have hlt := Nat.lt_floor_add_one (γ ^ (75 / θ))
  have hinv : (γ ^ (75 / θ)) ^ (θ / 75) = γ := by
    rw [← Real.rpow_mul hγ, show 75 / θ * (θ / 75) = 1 by field_simp, Real.rpow_one]
  constructor
  · calc ((⌊γ ^ (75 / θ)⌋₊ : ℕ) : ℝ) ^ (θ / 75) ≤ (γ ^ (75 / θ)) ^ (θ / 75) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hfl (by positivity)
      _ = γ := hinv
  · unfold jqrHeight
    calc γ = (γ ^ (75 / θ)) ^ (θ / 75) := hinv.symm
      _ ≤ (((⌊γ ^ (75 / θ)⌋₊ : ℕ) : ℝ) + 1) ^ (θ / 75) :=
          Real.rpow_le_rpow hp hlt.le (by positivity)

/-- The window index grows with the height. -/
theorem le_window_index {θ γ X : ℝ} (hθ : 0 < θ) (hX : 0 ≤ X)
    (hγ : (X + 1) ^ (θ / 75) ≤ γ) : X ≤ ((⌊γ ^ (75 / θ)⌋₊ : ℕ) : ℝ) := by
  have hX1 : 0 ≤ X + 1 := by linarith
  have h1 : X + 1 ≤ γ ^ (75 / θ) := by
    have := Real.rpow_le_rpow (Real.rpow_nonneg hX1 _) hγ (show 0 ≤ 75 / θ by positivity)
    rwa [← Real.rpow_mul hX1, show θ / 75 * (75 / θ) = 1 by field_simp, Real.rpow_one] at this
  have h2 := Nat.lt_floor_add_one (γ ^ (75 / θ))
  linarith

/-! ## The window conditions hold for every large window -/

/-- All window conditions hold eventually. -/
theorem eventually_window_conditions {θ ε σ₁ K δS : ℝ} (hθ0 : 0 < θ) (hθσ : θ ≤ (1 - σ₁) / 20)
    (hθδ : θ ≤ δS / 16) (hε0 : 0 ≤ ε) (hεθ : ε ≤ θ) (hσ₁0 : 0 ≤ σ₁) (hσ₁ : σ₁ < 1)
    (hK : 0 ≤ K) (hδS : 0 < δS) :
    ∀ᶠ x : ℝ in atTop, 3 ≤ x ∧ 400 ≤ jqrMassLo mertensPrimeWindowBound x ∧
      Real.exp (-(1 / 8) * Real.log (x + 1)) * jqrMassHi mertensPrimeWindowBound x ≤ 99 ∧
      2 * K * (x + 1 / 2) ^ (σ₁ - 1 + ε) *
        (jqrCut θ ε mertensPrimeWindowBound xiLineTwoLogDerivConstant x + 2) ^ 2 ≤ 1 ∧
      2 * (x + 1) ^ θ * (2 * Real.log x) * Real.exp ((ε - 1) * Real.log (x + 1)) ≤ 1 / 2 ∧
      16 * ((x + 1) ^ θ) ^ 2 * (2 * Real.log x) ^ 2 / Real.sqrt x ≤ 1 / 100 ∧
      (x + 1) ^ θ * (Real.exp (-(δS / 2) * Real.log (x + 1)) *
        jqrMassHi mertensPrimeWindowBound x) ≤ 1 / 100 ∧
      (x + 1) ^ θ * (2 * Real.log x) * Real.exp (-(2 * θ) * Real.log (x + 1)) ≤ 1 / 2 ∧
      Real.exp (-δS * Real.log (x + 1)) ≤ 1 / 2 ∧
      (32 * Real.pi ≤ jqrScaleMin θ xiLineTwoLogDerivConstant x *
          jqrMassLo mertensPrimeWindowBound x ∧
        4 * jqrThreshold θ (∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) x ≤
          jqrScaleMin θ xiLineTwoLogDerivConstant x * jqrMassLo mertensPrimeWindowBound x ∧
        (230 + 4 * Real.pi *
            jqrThreshold θ (∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖) x) /
            (jqrScaleMin θ xiLineTwoLogDerivConstant x * jqrMassLo mertensPrimeWindowBound x) ≤
          Real.pi / 8) ∧
      2 * (x ^ 2 + jqrHeight θ x + 10) ≤
        Real.exp (jqrCut θ ε mertensPrimeWindowBound xiLineTwoLogDerivConstant x) ∧
      40 / (Real.pi / 8 - 3 / 100) ≤ x ^ (θ / 75) := by
  have hCM := mertensPrimeWindowBound_nonneg
  have hC := xiLineTwoLogDerivConstant_nonneg
  have hW : 0 ≤ ∑' q : XiZeroCopy, ‖1 / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))‖ :=
    tsum_nonneg fun q => norm_nonneg _
  have hθ1 : θ ≤ 1 / 20 := by linarith
  filter_upwards [eventually_ge_atTop 3, eventually_jqrMassLo_ge mertensPrimeWindowBound 400,
    eventually_trivial_mass hCM,
    eventually_perron_small (θ := θ) (ε := ε) hθ0.le hε0 hσ₁0 hσ₁ hθσ (by linarith) hCM hC hK,
    eventually_dev (θ := θ) (ε := ε) (by linarith),
    eventually_remainder hθ0.le hθ1, eventually_mirror_small hδS hθδ hCM,
    eventually_admissible hθ0, eventually_exp_neg_le_half hδS,
    eventually_scale_conditions (C := xiLineTwoLogDerivConstant) (CM := mertensPrimeWindowBound)
      hθ0 (by linarith) hW,
    eventually_cut_large (ε := ε) hθ0.le (by linarith) hCM hC,
    eventually_le_rpow (40 / (Real.pi / 8 - 3 / 100)) (show 0 < θ / 75 by positivity)]
    with x h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

/-! ## Chain exclusion -/

/-- Positivity of every admissible log-weight Bernoulli test on the prime windows `(n, n²]`,
`n ≥ N₀`. -/
def JasWindowPositivity (σ : ℝ) (N₀ : ℕ) : Prop :=
  ∀ n : ℕ, N₀ ≤ n → ∀ (ξ : ℂ) (a : Nat.Primes → ℝ), (∀ p ∈ jasPrimeWindow n (n ^ 2), 0 ≤ a p) →
    (∀ p ∈ jasPrimeWindow n (n ^ 2), a p * Real.exp ((ξ.re + (σ - 1 / 2)) * Real.log p) ≤ 1 / 2) →
    ∀ φ : ℝ, 0 ≤ (∑' q : XiZeroCopy, (∏ p ∈ jasPrimeWindow n (n ^ 2),
      jasLogWeightLocal ξ (q.1 : ℂ) (a p) φ p) / ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re

theorem jasWindowPositivity_of_jasDressedPSD {σ : ℝ} (h : JasDressedPSD σ) :
    JasWindowPositivity σ 0 :=
  fun _ _ ξ a ha0 ha φ => jasLogWeightBernoulli_nonneg h ξ _ a ha0 ha φ

/-- **Chain exclusion from window positivity.**  Under a half-plane bound `α < ½`, if the
off-line zeros form a chain and the log-weight window tests are positive on all windows beyond
some `N₀`, then `σ ≥ 1 + sup |Re ρ − ½|`. -/
theorem one_add_sSup_le_of_jasWindowPositivity_of_chain {alpha σ : ℝ} {N₀ : ℕ} (halpha0 : 0 ≤ alpha)
    (halpha : alpha < 1 / 2) (hXi : XiZeroHalfPlaneBound alpha) (hW : JasWindowPositivity σ N₀)
    (hch : JasOffLineChain) :
    1 + sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) ≤ σ := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨δS, hδSdef⟩ : ∃ δS, δS = sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) :=
    ⟨_, rfl⟩
  rw [← hδSdef] at hlt
  have hbdd : BddAbove (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) :=
    ⟨alpha, by rintro _ ⟨q, rfl⟩; exact abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi q⟩
  have hle : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ δS := fun q => by
    rw [hδSdef]; exact le_csSup hbdd ⟨q, rfl⟩
  obtain ⟨q₁, hq₁⟩ := hch.1
  have hδS0 : 0 < δS := lt_of_lt_of_le (abs_pos.mpr (sub_ne_zero.mpr hq₁)) (hle q₁)
  have hδSa : δS ≤ alpha := by
    rw [hδSdef]
    exact csSup_le ⟨_, ⟨q₁, rfl⟩⟩ (by
      rintro _ ⟨q, rfl⟩; exact abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi q)
  have hδSh : δS < 1 / 2 := lt_of_le_of_lt hδSa halpha
  -- the frontier and the Perron constant
  obtain ⟨σ₁, hσ₁def⟩ : ∃ σ₁ : ℝ, σ₁ = 3 / 4 + alpha / 2 := ⟨_, rfl⟩
  have hσ₁a : 1 / 2 + alpha < σ₁ := by rw [hσ₁def]; linarith
  have hσ₁1 : σ₁ < 1 := by rw [hσ₁def]; linarith
  have hσ₁0 : 0 ≤ σ₁ := by rw [hσ₁def]; linarith
  obtain ⟨η, hηdef⟩ : ∃ η : ℝ, η = (1 - σ₁) / 4 := ⟨_, rfl⟩
  have hη0 : 0 < η := by rw [hηdef]; linarith
  obtain ⟨K, hK0, hPer⟩ := exists_norm_jasLogWeightSum_sub_le halpha0 hXi hσ₁a hσ₁1 hη0
  -- the exponents
  obtain ⟨μ, hμdef⟩ : ∃ μ : ℝ, μ = (1 + δS - σ) / 2 := ⟨_, rfl⟩
  have hμ0 : 0 < μ := by rw [hμdef]; linarith
  obtain ⟨θ, hθdef⟩ : ∃ θ : ℝ, θ = min (min (μ / 2) ((1 - σ₁) / 20)) (δS / 16) := ⟨_, rfl⟩
  have hθ0 : 0 < θ := by
    rw [hθdef]; exact lt_min (lt_min (by linarith) (by linarith)) (by linarith)
  have hθμ : θ ≤ μ / 2 := by rw [hθdef]; exact (min_le_left _ _).trans (min_le_left _ _)
  have hθσ : θ ≤ (1 - σ₁) / 20 := by rw [hθdef]; exact (min_le_left _ _).trans (min_le_right _ _)
  have hθδ : θ ≤ δS / 16 := by rw [hθdef]; exact min_le_right _ _
  -- the peak exponent
  obtain ⟨c₀, hc₀0, hc₀1, G₀, hG₀, hpeak⟩ :=
    exists_isolated_rePeak (σ₀ := 1 / 2 + δS / 2) (by linarith) (by linarith)
  obtain ⟨ε, hεdef⟩ : ∃ ε : ℝ, ε = θ * c₀ / 300 := ⟨_, rfl⟩
  have hε0 : 0 < ε := by rw [hεdef]; positivity
  have hεθ : ε ≤ θ := by rw [hεdef]; nlinarith
  have hεc : c₀ * θ = 300 * ε := by rw [hεdef]; ring
  -- the window threshold
  obtain ⟨X₂, hX₂⟩ := Filter.eventually_atTop.mp
    (eventually_window_conditions hθ0 hθσ hθδ hε0.le hεθ hσ₁0 hσ₁1 hK0.le hδS0)
  obtain ⟨X₀, hX₀def⟩ : ∃ X₀ : ℝ, X₀ = max X₂ (N₀ : ℝ) := ⟨_, rfl⟩
  have hX₀ : ∀ x : ℝ, X₀ ≤ x → _ := fun x hx => hX₂ x (le_trans (by rw [hX₀def]; exact le_max_left _ _) hx)
  obtain ⟨G, hGdef⟩ : ∃ G : ℝ, G = max G₀ (max 1 ((max X₀ 0 + 1) ^ (θ / 75))) := ⟨_, rfl⟩
  have hGG₀ : G₀ ≤ G := by rw [hGdef]; exact le_max_left _ _
  have hG1 : 1 ≤ G := by rw [hGdef]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hGX : (max X₀ 0 + 1) ^ (θ / 75) ≤ G := by
    rw [hGdef]; exact (le_max_right _ _).trans (le_max_right _ _)
  -- a chain zero near the supremum and a peak above it
  obtain ⟨_, ⟨q₀, rfl⟩, hq₀⟩ := exists_lt_of_lt_csSup (Set.range_nonempty _)
    (show δS - ε < sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) by
      rw [← hδSdef]; linarith)
  beta_reduce at hq₀
  have hoff : (q₀.1 : ℂ).re ≠ 1 / 2 := by
    intro h; rw [h, sub_self, abs_zero] at hq₀; linarith
  obtain ⟨q₂, hfar, hhigh⟩ := exists_farther_high_of_chain hch q₀ hoff (2 * G)
  obtain ⟨qt, hre, hγG, hiso⟩ := hpeak G hGG₀ q₂ (by linarith) hhigh.le
  -- the target
  obtain ⟨δt, hδtdef⟩ : ∃ δt : ℝ, δt = (qt.1 : ℂ).re - 1 / 2 := ⟨_, rfl⟩
  have hδt1 : δS - ε < δt := by rw [hδtdef]; linarith
  have hδt2 : δt ≤ δS := by
    have := hle qt; rw [hδtdef]; exact le_trans (le_abs_self _) this
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ, γ = (qt.1 : ℂ).im := ⟨_, rfl⟩
  have hγ0 : 0 ≤ γ := by rw [hγdef]; linarith
  have hqt_gt : 1 / 2 < (qt.1 : ℂ).re := by rw [hδtdef] at hδt1; linarith
  obtain ⟨ξ, hξdef⟩ : ∃ ξ : ℂ, ξ = 1 - conj (qt.1 : ℂ) := ⟨_, rfl⟩
  have hqt : jasLeftRep (qt.1 : ℂ) = ξ := by
    rw [jasLeftRep, if_neg (by linarith), hξdef]
  have hξre : ξ.re = 1 / 2 - δt := by rw [hξdef, hδtdef]; simp; ring
  have hξim : ξ.im = γ := by rw [hξdef, hγdef]; simp
  have hstrip : ∀ q : XiZeroCopy, |(q.1 : ℂ).re - 1 / 2| ≤ δt + ε := fun q => by
    linarith [hle q]
  have hiso' : ∀ q : XiZeroCopy, |(q.1 : ℂ).im - γ| ≤ γ ^ c₀ → |(q.1 : ℂ).re - 1 / 2| ≤ δt := by
    intro q hq
    rw [hγdef] at hq
    have h1 := hiso q hq
    obtain ⟨q', hq're, hq'im⟩ := exists_xiZeroCopy_mirror q
    have h2 := hiso q' (by rw [hq'im]; exact hq)
    rw [hq're] at h2
    rw [abs_le, hδtdef]
    constructor <;> linarith
  -- the window
  have hγX : (max X₀ 0 + 1) ^ (θ / 75) ≤ γ := le_trans hGX (by rw [hγdef]; exact hγG)
  obtain ⟨hnγ, hγΓ⟩ := window_index_brackets (γ := γ) hθ0 hγ0
  have hnX := le_window_index (θ := θ) (γ := γ) hθ0 (le_max_right X₀ 0) hγX
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12⟩ :=
    hX₀ _ (le_trans (le_max_left X₀ 0) hnX)
  have hσt : σ - δt - 1 ≤ -(2 * θ) := by
    have : σ = 1 + δS - 2 * μ := by rw [hμdef]; ring
    rw [this]; linarith
  obtain ⟨τ, φ, hτ0, hadm, hneg⟩ := exists_neg_test_at_target hθ0 hθσ hε0 hεθ hεc hσ₁0 hσ₁1
    hηdef hc₀0.le hK0.le hδS0 hδSh hPer qt hqt hξre (by linarith) hδt2 hξim hstrip hiso'
    hnγ hγΓ c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 hσt
  -- positivity contradicts the negative test
  have hN₀ : N₀ ≤ ⌊γ ^ (75 / θ)⌋₊ := by
    have h1 : (N₀ : ℝ) ≤ ((⌊γ ^ (75 / θ)⌋₊ : ℕ) : ℝ) :=
      le_trans (by rw [hX₀def]; exact le_max_right _ _) (le_trans (le_max_left X₀ 0) hnX)
    exact_mod_cast h1
  have hpos := hW _ hN₀ ξ (fun p => τ * (Real.log p / p))
    (fun p _ => mul_nonneg hτ0 (log_div_nonneg_prime p)) hadm φ
  have : (∑' q : XiZeroCopy,
      jasLogWeightValue ξ ⌊γ ^ (75 / θ)⌋₊ (⌊γ ^ (75 / θ)⌋₊ ^ 2) τ φ (q.1 : ℂ)).re =
      (∑' q : XiZeroCopy, (∏ p ∈ jasPrimeWindow ⌊γ ^ (75 / θ)⌋₊ (⌊γ ^ (75 / θ)⌋₊ ^ 2),
        jasLogWeightLocal ξ (q.1 : ℂ) (τ * (Real.log p / p)) φ p) /
          ((q.1 : ℂ) * (1 - (q.1 : ℂ)))).re := rfl
  linarith only [this, hpos, hneg]

/-- **Off-line chains force `σ ≥ 1 + δ*` under quasi-RH.**  If every Xi zero has
`Re ρ ≤ ½ + α` with `α < ½`, the off-line zeros form a chain, and the dressed JAS aggregate is
positive semidefinite at `σ`, then `σ ≥ 1 + sup |Re ρ − ½|`. -/
theorem one_add_sSup_le_of_jasDressedPSD_of_chain {alpha σ : ℝ} (halpha0 : 0 ≤ alpha)
    (halpha : alpha < 1 / 2) (hXi : XiZeroHalfPlaneBound alpha) (hPSD : JasDressedPSD σ)
    (hch : JasOffLineChain) :
    1 + sSup (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) ≤ σ :=
  one_add_sSup_le_of_jasWindowPositivity_of_chain halpha0 halpha hXi
    (jasWindowPositivity_of_jasDressedPSD hPSD) hch

/-- **JAS under quasi-RH.**  `RH ⟺ JasDressedPSD 1 ∧ ∃ α ∈ [0, ½), XiZeroHalfPlaneBound α`. -/
theorem riemannHypothesis_iff_jasDressedPSD_one_and_quasi :
    RiemannHypothesis ↔
      JasDressedPSD 1 ∧ ∃ alpha : ℝ, 0 ≤ alpha ∧ alpha < 1 / 2 ∧ XiZeroHalfPlaneBound alpha := by
  constructor
  · intro hRH
    obtain ⟨hPSD, hno⟩ := riemannHypothesis_iff_jasDressedPSD_one_and_not_chain.mp hRH
    exact ⟨hPSD, exists_xiZeroHalfPlaneBound_lt_half_of_not_jasOffLineChain hno⟩
  · rintro ⟨hPSD, alpha, halpha0, halpha, hXi⟩
    refine riemannHypothesis_iff_jasDressedPSD_one_and_not_chain.mpr ⟨hPSD, fun hch => ?_⟩
    have h := one_add_sSup_le_of_jasDressedPSD_of_chain halpha0 halpha hXi hPSD hch
    obtain ⟨q₁, hq₁⟩ := hch.1
    have hbdd : BddAbove (Set.range fun q : XiZeroCopy => |(q.1 : ℂ).re - 1 / 2|) :=
      ⟨alpha, by rintro _ ⟨q, rfl⟩; exact abs_re_sub_half_le_of_xiZeroHalfPlaneBound hXi q⟩
    have h1 := le_csSup hbdd ⟨q₁, rfl⟩
    have h2 : 0 < |(q₁.1 : ℂ).re - 1 / 2| := abs_pos.mpr (sub_ne_zero.mpr hq₁)
    simp only at h1
    linarith

end

end RHTower
