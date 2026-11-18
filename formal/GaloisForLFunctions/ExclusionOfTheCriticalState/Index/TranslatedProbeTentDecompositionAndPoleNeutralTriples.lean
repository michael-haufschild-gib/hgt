import GaloisForLFunctions.ExclusionOfTheCriticalState.Index.SingleQuartetRankTwoCompletionAndProbeResonance

/-!
# Translated-Probe Laplace-Tent Decomposition and Pole-Neutral Three-Probe Profiles

This module analyzes the explicit arithmetic, archimedean, and polar components of Weil's half-line
form `bareMixedEnergy` along one-parameter left translations `shiftProfile · R` (`R ≥ 0`) of
exponential probes and three-probe Lagrange combinations:

1. **Symmetric Laplace-tent overlap and horizon split of `primeMixedForm (probe p) (shiftProfile (probe p) R)`**
   (`integral_probe_mul_shiftProfile_sub`, `integral_probe_mul_shiftProfile_add`,
   `primePairTerm_probe_shiftProfile`, `primeMixedForm_shiftProfile_probe_eq`,
   `primeMixedForm_probe_shiftProfile_nonneg`,
   `primeMixedForm_probe_shiftProfile_horizon_split`):
   For `p > 1/2` and `R ≥ 0`, each prime correlation term evaluates to the nonnegative Laplace-tent
   kernel `(Λ_atom(n) / (2p)) (e^{-p |log n - R|} + e^{-p (log n + R)}) ≥ 0`, making
   `primeMixedForm` symmetric and nonnegative on `(probe p, shiftProfile (probe p) R)` and
   splitting it at `⌊e^R⌋₊` into the finite sub-horizon moment
   `(e^{-p R} / (2p)) ∑_{1 ≤ n ≤ ⌊e^R⌋₊} Λ(n) n^{p - 1/2}`, the super-horizon tail, and the
   reflected Dirichlet series.

2. **Translated pole identity, `R`-uniform Gamma bound, `O(e^{R/2})` ceiling, and nonnegative two-probe divergence**
   (`polePart_probe_shiftProfile`, `abs_gammaMixedForm_shiftProfile_le`,
   `bareMixedEnergy_probe_shiftProfile_le_exp_half`,
   `nonneg_twoProbe_bareMixedEnergy_unbounded_of_singleQuartet`):
   The polar cross-pairing of `(probe p, shiftProfile (probe p) R)` equals
   `2 cosh(R / 2) / (p² - 1/4)`, the Gamma pairing is uniformly bounded in `R : ℝ` by its `L¹`
   Fourier-norm majorant, and nonnegativity of `primeMixedForm` yields an unconditional `O(e^{R/2})`
   upper ceiling on `bareMixedEnergy (probe p) (shiftProfile (probe p) R)`. Under
   `HasSingleOffLineQuartet ρ₀`, the strictly nonnegative domain profiles
   `G_R = probe p + shiftProfile (probe p) R` (`p > 4`, `R ≥ 0`) achieve arbitrarily large positive
   and negative diagonal Weil energies `bareMixedEnergy G_R G_R`.

3. **Explicit pole-neutral three-probe profiles and pure prime-pairing dichotomy**
   (`poleNeutralTriple`, `negativeHalfLineLaplace_poleNeutralTriple`,
   `poleNeutralTriple_changes_sign`, `halfMoments_shiftProfile_poleNeutralTriple_eq_zero`,
   `poleNeutralTriple_primeMixed_bounded_of_riemannHypothesis`,
   `poleNeutralTriple_primeMixed_unbounded_of_singleQuartet`,
   `not_hasSingleOffLineQuartet_of_poleNeutralTriple_primeMixed_bddAbove`,
   `not_hasSingleOffLineQuartet_of_poleNeutralTriple_primeMixed_bddBelow`):
   For `4 < p < q < r`, the Lagrange three-probe combination `H = poleNeutralTriple p q r` has
   Laplace transform `(w² - 1/4) / ((p + w)(q + w)(r + w))`, annihilates both `coshHalfMoment` and
   `sinhHalfMoment` at **every** shift `R ∈ ℝ` (while necessarily changing sign on `(-∞, 0)`), and
   reduces `bareMixedEnergy H (shiftProfile H R)` up to an `O(1)` Gamma error to the pure prime
   pairing `(primeMixedForm H (shiftProfile H R) + primeMixedForm (shiftProfile H R) H) / 2`, which
   is uniformly bounded on `[0, ∞)` under `RiemannHypothesis` and unbounded both above and below
   under `HasSingleOffLineQuartet ρ₀`.
-/

noncomputable section
set_option autoImplicit false

open MeasureTheory Set Filter Zeta23 Complex Metric Topology Finset
open scoped ComplexConjugate

namespace GaloisForLFunctions.ExclusionOfTheCriticalState

open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri
  CriticalArithmeticCorrelationTheory SpacingScaleHarmonicAnalysis HTGeometry _root_.RHTower

/-! ## 1. Symmetric Laplace-tent overlap and horizon split of `primeMixedForm` -/

/-- Symmetric Laplace-tent overlap of `probe p` against `shiftProfile (probe p) R (· - L)`:
for `p > 0`, `L ≥ 0`, and `R ≥ 0`, the correlation integral equals `exp(-p |L - R|) / (2 p)`. -/
theorem integral_probe_mul_shiftProfile_sub {p L R : ℝ} (hp : 0 < p) (hL : 0 ≤ L) (hR : 0 ≤ R) :
    (∫ t, probe p t * shiftProfile (probe p) R (t - L)) = Real.exp (-p * |L - R|) / (2 * p) := by
  have h2p : 0 < p + p := by linarith
  rcases le_or_gt L R with hle | hgt
  · have habs : |L - R| = R - L := by rw [abs_of_nonpos (by linarith)]; ring
    have hpt : (fun t => probe p t * shiftProfile (probe p) R (t - L)) =
        fun t => probe p t * probe p (t + (R - L)) := by
      funext t; unfold shiftProfile; congr 2; ring
    rw [hpt, integral_probe_mul_probe_add h2p (by linarith), habs]
    ring_nf
  · have habs : |L - R| = L - R := abs_of_pos (by linarith)
    have hpt : (fun t => probe p t * shiftProfile (probe p) R (t - L)) =
        fun t => probe p t * probe p (t - (L - R)) := by
      funext t; unfold shiftProfile; congr 2; ring
    rw [hpt, integral_probe_mul_probe_sub h2p (by linarith), habs]
    ring_nf

/-- Reflected overlap of `probe p` against `shiftProfile (probe p) R (· + L)`:
for `p > 0`, `L ≥ 0`, and `R ≥ 0`, the integral equals `exp(-p (L + R)) / (2 p)`. -/
theorem integral_probe_mul_shiftProfile_add {p L R : ℝ} (hp : 0 < p) (hL : 0 ≤ L) (hR : 0 ≤ R) :
    (∫ t, probe p t * shiftProfile (probe p) R (t + L)) = Real.exp (-p * (L + R)) / (2 * p) := by
  have h2p : 0 < p + p := by linarith
  have hpt : (fun t => probe p t * shiftProfile (probe p) R (t + L)) =
      fun t => probe p t * probe p (t + (L + R)) := by
    funext t; unfold shiftProfile; congr 2; ring
  rw [hpt, integral_probe_mul_probe_add h2p (by linarith)]
  ring_nf

/-- **Laplace-tent formula and nonnegativity of each prime correlation term.** -/
theorem primePairTerm_probe_shiftProfile {p R : ℝ} (hp : 0 < p) (hR : 0 ≤ R) (n : ℕ) :
    primePairTerm (probe p) (shiftProfile (probe p) R) n =
        vonMangoldtAtom n *
          (Real.exp (-p * |Real.log n - R|) + Real.exp (-p * (Real.log n + R))) / (2 * p) ∧
      0 ≤ primePairTerm (probe p) (shiftProfile (probe p) R) n := by
  have hL : 0 ≤ Real.log n := Real.log_natCast_nonneg n
  have heq : primePairTerm (probe p) (shiftProfile (probe p) R) n =
      vonMangoldtAtom n *
        (Real.exp (-p * |Real.log n - R|) + Real.exp (-p * (Real.log n + R))) / (2 * p) := by
    unfold primePairTerm
    rw [integral_probe_mul_shiftProfile_sub hp hL hR,
      integral_probe_mul_shiftProfile_add hp hL hR]
    ring
  refine ⟨heq, ?_⟩
  rw [heq]
  have hatom_nn : 0 ≤ vonMangoldtAtom n := by
    unfold vonMangoldtAtom
    split_ifs
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.sqrt_nonneg _)
    · exact le_rfl
  positivity

/-- Translation symmetry of `primePairTerm` and `primeMixedForm` on `(probe p, shiftProfile (probe p) R)`. -/
theorem primeMixedForm_shiftProfile_probe_eq (p R : ℝ) :
    (∀ n : ℕ, primePairTerm (shiftProfile (probe p) R) (probe p) n =
        primePairTerm (probe p) (shiftProfile (probe p) R) n) ∧
      primeMixedForm (shiftProfile (probe p) R) (probe p) =
        primeMixedForm (probe p) (shiftProfile (probe p) R) := by
  have hterm : ∀ n : ℕ, primePairTerm (shiftProfile (probe p) R) (probe p) n =
      primePairTerm (probe p) (shiftProfile (probe p) R) n := by
    intro n
    unfold primePairTerm shiftProfile
    have h1 : (∫ t, probe p (t + R) * probe p (t - Real.log n)) =
        ∫ u, probe p u * probe p (u + Real.log n + R) := by
      rw [← integral_add_right_eq_self (fun u => probe p u * probe p (u - R - Real.log n)) R]
      simp only [add_sub_cancel_right]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      rw [mul_comm]
      have htr := integral_add_right_eq_self
        (fun s => probe p s * probe p (s + Real.log n + R)) (-Real.log n - R)
      exact rfl
    -- Direct change of variables `u = t - Real.log n` and `u = t + Real.log n`:
    have ha : (∫ t, probe p (t + R) * probe p (t - Real.log n)) =
        ∫ u, probe p u * probe p (u + Real.log n + R) := by
      rw [← integral_add_right_eq_self (fun u => probe p (u + Real.log n + R) * probe p u)
        (-Real.log n)]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      dsimp only
      rw [mul_comm]
      congr 2 <;> ring
    have hb : (∫ t, probe p (t + R) * probe p (t + Real.log n)) =
        ∫ u, probe p u * probe p (u - Real.log n + R) := by
      rw [← integral_add_right_eq_self (fun u => probe p (u - Real.log n + R) * probe p u)
        (Real.log n)]
      refine integral_congr_ae (Eventually.of_forall fun t => ?_)
      dsimp only
      rw [mul_comm]
      congr 2 <;> ring
    rw [ha, hb, add_comm]
  exact ⟨hterm, by unfold primeMixedForm; exact tsum_congr hterm⟩

/-- Nonnegativity of `primeMixedForm (probe p) (shiftProfile (probe p) R)` for `p > 0`, `R ≥ 0`. -/
theorem primeMixedForm_probe_shiftProfile_nonneg {p R : ℝ} (hp : 0 < p) (hR : 0 ≤ R) :
    0 ≤ primeMixedForm (probe p) (shiftProfile (probe p) R) :=
  tsum_nonneg fun n => (primePairTerm_probe_shiftProfile hp hR n).2

/-- **Exact arithmetic horizon split of `primeMixedForm (probe p) (shiftProfile (probe p) R)`.**
For `p > 1/2` and `R ≥ 0`, splitting `|log n - R|` at `N = ⌊e^R⌋₊` decomposes `primeMixedForm` into
the sub-horizon growing moment `∑_{1 ≤ n ≤ ⌊e^R⌋₊} Λ(n) n^{p - 1/2}`, the super-horizon Dirichlet
tail `∑_{n > ⌊e^R⌋₊} Λ(n) n^{-1/2 - p}`, and the full reflected Dirichlet series. -/
theorem primeMixedForm_probe_shiftProfile_horizon_split {p R : ℝ} (hp : 1 / 2 < p) (hR : 0 ≤ R) :
    primeMixedForm (probe p) (shiftProfile (probe p) R) =
      (Real.exp (-p * R) / (2 * p)) *
          (∑ n ∈ Finset.Icc 1 ⌊Real.exp R⌋₊,
            (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (p - 1 / 2)) +
        (Real.exp (p * R) / (2 * p)) *
          (∑' k : ℕ, (ArithmeticFunction.vonMangoldt (k + ⌊Real.exp R⌋₊ + 1) : ℝ) /
            ((k + ⌊Real.exp R⌋₊ + 1 : ℕ) : ℝ) ^ (1 / 2 + p)) +
        (Real.exp (-p * R) / (2 * p)) *
          (∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (1 / 2 + p)) := by
  have hp0 : 0 < p := by linarith
  set N : ℕ := ⌊Real.exp R⌋₊
  have h1_le_exp : (1 : ℝ) ≤ Real.exp R := Real.one_le_exp hR
  have hN_pos : 1 ≤ N := Nat.one_le_iff_ne_zero.mpr (Nat.floor_pos.mpr h1_le_exp).ne'
  have hs_base : Summable fun n : ℕ =>
      (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (1 / 2 + p) :=
    summable_vonMangoldt_div_rpow (by linarith)
  set f₁ : ℕ → ℝ := fun n => vonMangoldtAtom n * Real.exp (-p * |Real.log n - R|) / (2 * p)
  set f₂ : ℕ → ℝ := fun n => vonMangoldtAtom n * Real.exp (-p * (Real.log n + R)) / (2 * p)
  have hf₂_eq : ∀ n : ℕ, f₂ n =
      (Real.exp (-p * R) / (2 * p)) *
        ((ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (1 / 2 + p)) := by
    intro n
    dsimp [f₂]
    rw [show -p * (Real.log n + R) = -(p * Real.log n) + (-p * R) by ring, Real.exp_add,
      ← mul_assoc, vonMangoldtAtom_mul_exp_eq]
    ring
  have hf₁_tail : ∀ k : ℕ, f₁ (k + (N + 1)) =
      (Real.exp (p * R) / (2 * p)) *
        ((ArithmeticFunction.vonMangoldt (k + N + 1) : ℝ) /
          ((k + N + 1 : ℕ) : ℝ) ^ (1 / 2 + p)) := by
    intro k
    set m : ℕ := k + N + 1
    have hm_eq : k + (N + 1) = m := by dsimp [m]; omega
    rw [hm_eq]
    have hm_gt : Real.exp R < (m : ℝ) := by
      have hlt : Real.exp R < ((N + 1 : ℕ) : ℝ) := Nat.lt_floor_add_one (Real.exp R)
      have hle : ((N + 1 : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast (by dsimp [m]; omega : N + 1 ≤ m)
      exact hlt.trans_le hle
    have hm_pos : (0 : ℝ) < (m : ℝ) := (Real.exp_pos R).trans hm_gt
    have hlog_gt : R < Real.log m := (Real.lt_log_iff_exp_lt hm_pos).mpr hm_gt
    dsimp [f₁]
    rw [abs_of_pos (by linarith), show -p * (Real.log m - R) = -(p * Real.log m) + p * R by ring,
      Real.exp_add, ← mul_assoc, vonMangoldtAtom_mul_exp_eq]
    ring
  have hs_f₂ : Summable f₂ := by
    rw [funext hf₂_eq]
    exact hs_base.mul_left _
  have hs_f₁_shift : Summable fun k : ℕ => f₁ (k + (N + 1)) := by
    rw [funext hf₁_tail]
    exact ((summable_nat_add_iff (N + 1)).mpr hs_base).congr
      (fun k => by simp [add_assoc]) |>.mul_left _
  have hs_f₁ : Summable f₁ := (summable_nat_add_iff (N + 1)).mp hs_f₁_shift
  have hterm_split : ∀ n : ℕ,
      primePairTerm (probe p) (shiftProfile (probe p) R) n = f₁ n + f₂ n := by
    intro n
    rw [(primePairTerm_probe_shiftProfile hp0 hR n).1]
    dsimp [f₁, f₂]
    ring
  have hf₁_head : ∑ n ∈ Finset.range (N + 1), f₁ n =
      (Real.exp (-p * R) / (2 * p)) *
        ∑ n ∈ Finset.Icc 1 N,
          (ArithmeticFunction.vonMangoldt n : ℝ) * (n : ℝ) ^ (p - 1 / 2) := by
    have hrange : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by
      ext n; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]; omega
    rw [hrange, Finset.sum_insert (by simp)]
    have hf₁_zero : f₁ 0 = 0 := by simp [f₁, vonMangoldtAtom]
    rw [hf₁_zero, zero_add, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    rcases eq_or_lt_of_le hn1 with rfl | hn_gt1
    · simp [f₁, vonMangoldtAtom]
    · have hn_pos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hn_le_exp : (n : ℝ) ≤ Real.exp R := Nat.le_of_floor_ge hnN
      have hlog_le : Real.log n ≤ R := (Real.log_le_iff_le_exp hn_pos).mpr hn_le_exp
      dsimp [f₁]
      rw [abs_of_nonpos (by linarith), vonMangoldtAtom, if_pos (by omega : 2 ≤ n),
        show -p * -(Real.log n - R) = -p * R + Real.log n * p by ring, Real.exp_add,
        ← Real.rpow_def_of_pos hn_pos, Real.sqrt_eq_rpow,
        show (n : ℝ) ^ (p - 1 / 2) = (n : ℝ) ^ p / (n : ℝ) ^ (1 / 2 : ℝ) by
          rw [sub_eq_add_neg, Real.rpow_add hn_pos, Real.rpow_neg hn_pos.le, div_eq_mul_inv]]
      field_simp [hp0.ne', (Real.rpow_pos_of_pos hn_pos (1 / 2)).ne']
      ring
  unfold primeMixedForm
  simp_rw [hterm_split]
  rw [hs_f₁.tsum_add hs_f₂, ← hs_f₁.sum_add_tsum_nat_add (N + 1), hf₁_head]
  have htsum_tail : (∑' k : ℕ, f₁ (k + (N + 1))) =
      (Real.exp (p * R) / (2 * p)) *
        ∑' k : ℕ, (ArithmeticFunction.vonMangoldt (k + N + 1) : ℝ) /
          ((k + N + 1 : ℕ) : ℝ) ^ (1 / 2 + p) := by
    simp_rw [hf₁_tail, tsum_mul_left]
  have htsum_f₂ : (∑' n : ℕ, f₂ n) =
      (Real.exp (-p * R) / (2 * p)) *
        ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℝ) / (n : ℝ) ^ (1 / 2 + p) := by
    simp_rw [hf₂_eq, tsum_mul_left]
  rw [htsum_tail, htsum_f₂]

/-! ## 2. Translated pole identity, Gamma majorant, `O(e^{R/2})` ceiling, and nonnegative divergence -/

/-- Symmetry `bareMixedEnergy F G = bareMixedEnergy G F` holds for arbitrary profiles `F, G`. -/
theorem bareMixedEnergy_symm (F G : ℝ → ℝ) :
    bareMixedEnergy F G = bareMixedEnergy G F := by
  have hγ : gammaMixedForm F G = gammaMixedForm G F := by
    unfold gammaMixedForm gammaFourierPair
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun r => by dsimp only; ring)
  unfold bareMixedEnergy
  rw [hγ]
  ring

/-- **Translated probe pole-pairing identity.** For `p > 1/2` and `R ∈ ℝ`,
`2 C(e_p) C(τ_R e_p) - 2 S(e_p) S(τ_R e_p) = 2 cosh(R / 2) / (p² - 1/4)`. -/
theorem polePart_probe_shiftProfile {p : ℝ} (hp : 1 / 2 < p) (R : ℝ) :
    2 * coshHalfMoment (probe p) * coshHalfMoment (shiftProfile (probe p) R) -
        2 * sinhHalfMoment (probe p) * sinhHalfMoment (shiftProfile (probe p) R) =
      2 * Real.cosh (R / 2) / (p ^ 2 - 1 / 4) := by
  have hi1 := integrable_probe_mul_exp (p := p) (c := 1 / 2) (by linarith)
  have hi2 := integrable_probe_mul_exp (p := p) (c := -(1 / 2)) (by linarith)
  have hc : Integrable fun u => probe p u * Real.cosh (u / 2) := by
    refine ((hi1.add hi2).div_const 2).congr (Eventually.of_forall fun u => ?_)
    dsimp only; rw [Real.cosh_eq]; ring_nf
  have hs : Integrable fun u => probe p u * Real.sinh (u / 2) := by
    refine ((hi1.sub hi2).div_const 2).congr (Eventually.of_forall fun u => ?_)
    dsimp only; rw [Real.sinh_eq]; ring_nf
  rw [coshHalfMoment_shiftProfile hc hs, sinhHalfMoment_shiftProfile hc hs,
    coshHalfMoment_probe hp, sinhHalfMoment_probe hp]
  have h1 : 2 * p + 1 ≠ 0 := by linarith
  have h2 : 2 * p - 1 ≠ 0 := by linarith
  have h3 : p ^ 2 - 1 / 4 ≠ 0 := by nlinarith
  rw [show p + 1 / 2 = (2 * p + 1) / 2 by ring, show p - 1 / 2 = (2 * p - 1) / 2 by ring]
  field_simp
  ring

/-- **Uniform `R`-independent Gamma bound along translations.** For any `F` with `Integrable F` and
`Integrable (r ↦ ‖F̂(r)‖² γ(r))` and any `R ∈ ℝ`, `|gammaMixedForm F (shiftProfile F R)|` is
bounded by `(1 / (2π)) ∫ ‖F̂(r)‖² |γ(r)| dr`. -/
theorem abs_gammaMixedForm_shiftProfile_le {F : ℝ → ℝ} (hF : Integrable F)
    (hγ : Integrable fun r : ℝ => ‖paperFT (cx F) r‖ ^ 2 * EF.gammaBracket r) (R : ℝ) :
    |gammaMixedForm F (shiftProfile F R)| ≤
      1 / (2 * Real.pi) * ∫ r : ℝ, ‖paperFT (cx F) r‖ ^ 2 * |EF.gammaBracket r| := by
  have hmaj : Integrable fun r : ℝ => ‖paperFT (cx F) r‖ ^ 2 * |EF.gammaBracket r| := by
    refine hγ.norm.congr (Eventually.of_forall fun r => ?_)
    simp [Real.norm_eq_abs, abs_mul, abs_of_nonneg (sq_nonneg _)]
  have hpt : ∀ r : ℝ, ‖gammaFourierPair F (shiftProfile F R) r * EF.gammaBracket r‖ ≤
      ‖paperFT (cx F) r‖ ^ 2 * |EF.gammaBracket r| := by
    intro r
    rw [Real.norm_eq_abs, abs_mul]
    refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
    have hpair : |gammaFourierPair F (shiftProfile F R) r| ≤
        (‖paperFT (cx F) r‖ ^ 2 + ‖paperFT (cx (shiftProfile F R)) r‖ ^ 2) / 2 := by
      rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
      unfold gammaFourierPair
      rw [abs_le]
      constructor
      · nlinarith [sq_nonneg ((paperFT (cx F) r).re + (paperFT (cx (shiftProfile F R)) r).re),
          sq_nonneg ((paperFT (cx F) r).im + (paperFT (cx (shiftProfile F R)) r).im)]
      · nlinarith [sq_nonneg ((paperFT (cx F) r).re - (paperFT (cx (shiftProfile F R)) r).re),
          sq_nonneg ((paperFT (cx F) r).im - (paperFT (cx (shiftProfile F R)) r).im)]
    rwa [norm_paperFT_shiftProfile, add_self_div_two] at hpair
  unfold gammaMixedForm
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * Real.pi))]
  exact mul_le_mul_of_nonneg_left
    ((Real.norm_eq_abs _).symm.le.trans (norm_integral_le_of_norm_le hmaj (Eventually.of_forall hpt)))
    (by positivity)

/-- **Unconditional `O(e^{R/2})` upper ceiling on `bareMixedEnergy (probe p) (shiftProfile (probe p) R)`.**
Because `primeMixedForm ≥ 0` enters with a minus sign, `bareMixedEnergy (probe p) (shiftProfile (probe p) R)`
cannot exceed its `R`-independent Gamma majorant plus `2 e^{R/2} / (p² - 1/4)`. -/
theorem bareMixedEnergy_probe_shiftProfile_le_exp_half {p R : ℝ} (hp : 1 / 2 < p) (hR : 0 ≤ R) :
    bareMixedEnergy (probe p) (shiftProfile (probe p) R) ≤
      1 / (2 * Real.pi) *
          (∫ r : ℝ, 1 / (p ^ 2 + r ^ 2) * |EF.gammaBracket r|) +
        2 * Real.exp (R / 2) / (p ^ 2 - 1 / 4) := by
  have hp0 : 0 < p := by linarith
  have hγ_int : Integrable fun r : ℝ => ‖paperFT (cx (probe p)) r‖ ^ 2 * EF.gammaBracket r :=
    integrable_gammaEnergy_of_linear_decay (continuous_paperFT_probe hp0)
      (one_add_abs_mul_norm_paperFT_probe_le hp0)
  have hnorm_sq : ∀ r : ℝ, ‖paperFT (cx (probe p)) r‖ ^ 2 = 1 / (p ^ 2 + r ^ 2) := by
    intro r
    rw [paperFT_probe (z := (r : ℂ)) (by simpa using hp0), norm_div, norm_one, div_pow, one_pow,
      Complex.sq_norm, Complex.normSq_apply]
    simp; ring
  have hγ_le := abs_gammaMixedForm_shiftProfile_le (integrable_probe hp0) hγ_int R
  simp_rw [hnorm_sq] at hγ_le
  have hprime_symm := (primeMixedForm_shiftProfile_probe_eq p R).2
  have hprime_nn := primeMixedForm_probe_shiftProfile_nonneg hp0 hR
  have hpole := polePart_probe_shiftProfile hp R
  have hcosh_le : 2 * Real.cosh (R / 2) ≤ 2 * Real.exp (R / 2) := by
    rw [Real.cosh_eq]
    have hexp_le : Real.exp (-(R / 2)) ≤ Real.exp (R / 2) :=
      Real.exp_le_exp.mpr (by linarith)
    linarith
  have hpole_le : 2 * Real.cosh (R / 2) / (p ^ 2 - 1 / 4) ≤
      2 * Real.exp (R / 2) / (p ^ 2 - 1 / 4) :=
    div_le_div_of_nonneg_right hcosh_le (by nlinarith)
  unfold bareMixedEnergy
  rw [hprime_symm, add_self_div_two, hpole]
  linarith [(abs_le.mp hγ_le).2]

/-- **Nonnegative two-probe diagonal Weil divergence under `HasSingleOffLineQuartet ρ₀`.**
For every `p > 4` and threshold `M : ℝ`, there exist shifts `R₊, R₋ ≥ 0` such that the nonnegative
two-probe profiles `G_{R}(u) = probe p u + shiftProfile (probe p) R u ≥ 0` lie in
`CriticalHalfLineEnergyDomain` and satisfy `M < bareMixedEnergy G_{R₊} G_{R₊}` and
`bareMixedEnergy G_{R₋} G_{R₋} < -M`. -/
theorem nonneg_twoProbe_bareMixedEnergy_unbounded_of_singleQuartet {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) {p : ℝ} (hp : 4 < p) (M : ℝ) :
    (∃ R : ℝ, 0 ≤ R ∧ (∀ u : ℝ, 0 ≤ probe p u + shiftProfile (probe p) R u) ∧
        CriticalHalfLineEnergyDomain (fun u => probe p u + shiftProfile (probe p) R u) ∧
        M < bareMixedEnergy (fun u => probe p u + shiftProfile (probe p) R u)
          (fun u => probe p u + shiftProfile (probe p) R u)) ∧
      (∃ R : ℝ, 0 ≤ R ∧ (∀ u : ℝ, 0 ≤ probe p u + shiftProfile (probe p) R u) ∧
        CriticalHalfLineEnergyDomain (fun u => probe p u + shiftProfile (probe p) R u) ∧
        bareMixedEnergy (fun u => probe p u + shiftProfile (probe p) R u)
          (fun u => probe p u + shiftProfile (probe p) R u) < -M) := by
  have hFp := criticalHalfLineEnergyDomain_probe hp
  have hdiag : ∀ {R : ℝ}, 0 ≤ R →
      bareMixedEnergy (fun u => probe p u + shiftProfile (probe p) R u)
          (fun u => probe p u + shiftProfile (probe p) R u) =
        2 * bareMixedEnergy (probe p) (probe p) +
          2 * bareMixedEnergy (probe p) (shiftProfile (probe p) R) := by
    intro R hR
    have hFs := criticalHalfLineEnergyDomain_shiftProfile hFp hR
    have hsum : CriticalHalfLineEnergyDomain (fun u => probe p u + shiftProfile (probe p) R u) := by
      simpa [one_mul] using hFp.add_const_mul hFs 1
    rw [bareMixedEnergy_add_right hsum hFp hFs, bareMixedEnergy_symm hsum (probe p),
      bareMixedEnergy_add_right hFp hFp hFs, bareMixedEnergy_symm hsum (shiftProfile (probe p) R),
      bareMixedEnergy_add_right hFs hFp hFs, bareMixedEnergy_symm (shiftProfile (probe p) R) (probe p),
      bareMixedEnergy_shiftProfile (integrable_mul_cosh_half_of_domain hFp)
        (integrable_mul_sinh_half_of_domain hFp) (integrable_mul_cosh_half_of_domain hFp)
        (integrable_mul_sinh_half_of_domain hFp) R]
    ring
  set B : ℝ := (|M| + 2 * |bareMixedEnergy (probe p) (probe p)|) / 2
  obtain ⟨⟨R₁, hR₁, hgt⟩, ⟨R₂, hR₂, hlt⟩⟩ :=
    probe_shiftProfile_unbounded_above_and_below_of_singleQuartet hq hp B
  refine ⟨⟨R₁, hR₁, fun u => add_nonneg (probe_nonneg p u) (probe_nonneg p (u + R₁)),
      by simpa [one_mul] using hFp.add_const_mul (criticalHalfLineEnergyDomain_shiftProfile hFp hR₁) 1,
      ?_⟩,
    ⟨R₂, hR₂, fun u => add_nonneg (probe_nonneg p u) (probe_nonneg p (u + R₂)),
      by simpa [one_mul] using hFp.add_const_mul (criticalHalfLineEnergyDomain_shiftProfile hFp hR₂) 1,
      ?_⟩⟩
  · rw [hdiag hR₁]
    dsimp [B] at hgt
    linarith [le_abs_self M, neg_abs_le (bareMixedEnergy (probe p) (probe p))]
  · rw [hdiag hR₂]
    dsimp [B] at hlt
    linarith [le_abs_self M, le_abs_self (bareMixedEnergy (probe p) (probe p))]

/-! ## 3. Explicit pole-neutral three-probe profiles and pure prime-pairing dichotomy -/

/-- Explicit Lagrange three-probe combination annihilating the `(±1/2)` polar moments:
`H_{p,q,r}(u) = c₁ e_p(u) + c₂ e_q(u) + c₃ e_r(u)` with `c₁ + c₂ + c₃ = 1`. -/
def poleNeutralTriple (p q r : ℝ) (u : ℝ) : ℝ :=
  ((p ^ 2 - 1 / 4) / ((p - q) * (p - r))) * probe p u +
    ((q ^ 2 - 1 / 4) / ((q - p) * (q - r))) * probe q u +
    ((r ^ 2 - 1 / 4) / ((r - p) * (r - q))) * probe r u

/-- For `p, q, r > 4`, `poleNeutralTriple p q r` lies in `CriticalHalfLineEnergyDomain`. -/
theorem criticalHalfLineEnergyDomain_poleNeutralTriple {p q r : ℝ}
    (hp : 4 < p) (hq : 4 < q) (hr : 4 < r) :
    CriticalHalfLineEnergyDomain (poleNeutralTriple p q r) := by
  have h12 := ((criticalHalfLineEnergyDomain_probe hp).const_mul
    ((p ^ 2 - 1 / 4) / ((p - q) * (p - r)))).add_const_mul
    (criticalHalfLineEnergyDomain_probe hq) ((q ^ 2 - 1 / 4) / ((q - p) * (q - r)))
  have h123 := h12.add_const_mul (criticalHalfLineEnergyDomain_probe hr)
    ((r ^ 2 - 1 / 4) / ((r - p) * (r - q)))
  exact h123

/-- Exact rational Laplace transform of `poleNeutralTriple p q r`: for pairwise distinct `p, q, r`
and `Re w > -min(p, q, r)`, `L H(w) = (w² - 1/4) / ((p + w)(q + w)(r + w))`. -/
theorem negativeHalfLineLaplace_poleNeutralTriple {p q r : ℝ}
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) {w : ℂ}
    (hpw : 0 < p + w.re) (hqw : 0 < q + w.re) (hrw : 0 < r + w.re) :
    negativeHalfLineLaplace (cx (poleNeutralTriple p q r)) w =
      (w ^ 2 - 1 / 4) / (((p : ℂ) + w) * ((q : ℂ) + w) * ((r : ℂ) + w)) := by
  set c₁ : ℝ := (p ^ 2 - 1 / 4) / ((p - q) * (p - r))
  set c₂ : ℝ := (q ^ 2 - 1 / 4) / ((q - p) * (q - r))
  set c₃ : ℝ := (r ^ 2 - 1 / 4) / ((r - p) * (r - q))
  have hi : ∀ {s : ℝ}, 0 < s + w.re → Integrable fun u : ℝ => cexp (w * u) * cx (probe s) u := by
    intro s hs
    refine ((integrable_probe_mul_exp hs).norm).mono'
      (((by fun_prop : Measurable fun u : ℝ => cexp (w * u)).mul
        (Complex.measurable_ofReal.comp (measurable_probe s))).aestronglyMeasurable)
      (Eventually.of_forall fun u => ?_)
    rw [norm_mul, Complex.norm_exp, show (w * (u : ℂ)).re = w.re * u by simp,
      cx, Complex.norm_real, Real.norm_of_nonneg (probe_nonneg s u),
      Real.norm_of_nonneg (mul_nonneg (probe_nonneg s u) (Real.exp_pos _).le), mul_comm]
  have hval : ∀ {s : ℝ}, 0 < s + w.re →
      (∫ u : ℝ, cexp (w * u) * cx (probe s) u) = 1 / ((s : ℂ) + w) := by
    intro s hs
    have heq : (fun u : ℝ => cexp (w * u) * cx (probe s) u) =
        fun u : ℝ => (probe s u : ℂ) * cexp (w * u) := by
      funext u; simp [cx, mul_comm]
    rw [heq, integral_probe_mul_cexp hs]
  unfold negativeHalfLineLaplace poleNeutralTriple
  have hpt : (fun u : ℝ => cexp (w * u) * cx (fun u =>
      c₁ * probe p u + c₂ * probe q u + c₃ * probe r u) u) =
      fun u : ℝ => ((c₁ : ℂ) * (cexp (w * u) * cx (probe p) u) +
        (c₂ : ℂ) * (cexp (w * u) * cx (probe q) u)) +
        (c₃ : ℂ) * (cexp (w * u) * cx (probe r) u) := by
    funext u; simp [cx]; ring
  rw [hpt, integral_add (((hi hpw).const_mul _).add ((hi hqw).const_mul _)) ((hi hrw).const_mul _),
    integral_add ((hi hpw).const_mul _) ((hi hqw).const_mul _),
    integral_const_mul, integral_const_mul, integral_const_mul,
    hval hpw, hval hqw, hval hrw]
  have hpq_c : (p : ℂ) - q ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hpq)
  have hqp_c : (q : ℂ) - p ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hpq.symm)
  have hpr_c : (p : ℂ) - r ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hpr)
  have hrp_c : (r : ℂ) - p ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hpr.symm)
  have hqr_c : (q : ℂ) - r ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hqr)
  have hrq_c : (r : ℂ) - q ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hqr.symm)
  have hpw_c : (p : ℂ) + w ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hqw_c : (q : ℂ) + w ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  have hrw_c : (r : ℂ) + w ≠ 0 := fun h => by
    have := congrArg Complex.re h; simp at this; linarith
  dsimp [c₁, c₂, c₃]
  push_cast
  field_simp [hpq_c, hqp_c, hpr_c, hrp_c, hqr_c, hrq_c, hpw_c, hqw_c, hrw_c]
  ring

/-- **Mandatory sign change of `poleNeutralTriple p q r` on `(-∞, 0)`.**
Because the Lagrange weights sum to `1` (`H(0⁻) = 1 > 0`) while `∫_{-∞}^0 H(u) e^{u/2} du = 0`
against the strictly positive kernel `e^{u/2}`, `poleNeutralTriple p q r` takes both strictly
positive and strictly negative values on `(-∞, 0)`. -/
theorem poleNeutralTriple_changes_sign {p q r : ℝ} (hp : 1 / 2 < p) (hpq : p < q) (hqr : q < r) :
    (∃ u : ℝ, u < 0 ∧ 0 < poleNeutralTriple p q r u) ∧
      (∃ u : ℝ, u < 0 ∧ poleNeutralTriple p q r u < 0) := by
  set c₁ : ℝ := (p ^ 2 - 1 / 4) / ((p - q) * (p - r))
  set c₂ : ℝ := (q ^ 2 - 1 / 4) / ((q - p) * (q - r))
  set c₃ : ℝ := (r ^ 2 - 1 / 4) / ((r - p) * (r - q))
  have hsum1 : c₁ + c₂ + c₃ = 1 := by
    dsimp [c₁, c₂, c₃]
    have h1 : p - q ≠ 0 := by linarith
    have h2 : q - p ≠ 0 := by linarith
    have h3 : p - r ≠ 0 := by linarith
    have h4 : r - p ≠ 0 := by linarith
    have h5 : q - r ≠ 0 := by linarith
    have h6 : r - q ≠ 0 := by linarith
    field_simp
    ring
  -- Continuity at `0` of the smooth formula `g(u) = c₁ e^{pu} + c₂ e^{qu} + c₃ e^{ru}` gives `g(u) > 0` near `0⁻`.
  set g : ℝ → ℝ := fun u => c₁ * Real.exp (p * u) + c₂ * Real.exp (q * u) + c₃ * Real.exp (r * u)
  have hg_cont : Continuous g := by dsimp [g]; fun_prop
  have hg0 : g 0 = 1 := by simp [g, hsum1]
  have h_ev_pos : ∀ᶠ u : ℝ in 𝓝 0, 0 < g u :=
    hg_cont.continuousAt.eventually (gt_mem_nhds (by rw [hg0]; norm_num))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp h_ev_pos
  have hu_pos_mem : -(δ / 2) < 0 ∧ 0 < poleNeutralTriple p q r (-(δ / 2)) := by
    have hneg : -(δ / 2) < 0 := by linarith
    refine ⟨hneg, ?_⟩
    have hdist : dist (-(δ / 2)) 0 < δ := by
      rw [Real.dist_eq, sub_zero, abs_neg, abs_of_pos (by positivity)]
      linarith
    have hgu := hball hdist
    unfold poleNeutralTriple
    rwa [probe_of_neg hneg, probe_of_neg hneg, probe_of_neg hneg]
  refine ⟨⟨-(δ / 2), hu_pos_mem.1, hu_pos_mem.2⟩, ?_⟩
  -- If `H ≥ 0` on `(-∞, 0)`, then `H(u) e^{u/2} ≥ 0` everywhere with integral `0`, forcing `g = 0` on `(-∞, 0)`.
  by_contra hno_neg
  push Not at hno_neg
  have hnn : ∀ u : ℝ, 0 ≤ poleNeutralTriple p q r u * Real.exp (1 / 2 * u) := by
    intro u
    rcases lt_or_ge u 0 with hu | hu
    · exact mul_nonneg (hno_neg u hu) (Real.exp_pos _).le
    · unfold poleNeutralTriple
      rw [probe_of_nonneg hu, probe_of_nonneg hu, probe_of_nonneg hu]
      simp
  have hint : Integrable fun u : ℝ => poleNeutralTriple p q r u * Real.exp (1 / 2 * u) := by
    have hpt : (fun u : ℝ => poleNeutralTriple p q r u * Real.exp (1 / 2 * u)) =
        fun u : ℝ => (c₁ * (probe p u * Real.exp (1 / 2 * u)) +
          c₂ * (probe q u * Real.exp (1 / 2 * u))) +
          c₃ * (probe r u * Real.exp (1 / 2 * u)) := by
      funext u; unfold poleNeutralTriple; ring
    rw [hpt]
    exact (((integrable_probe_mul_exp (by linarith)).const_mul c₁).add
      ((integrable_probe_mul_exp (by linarith)).const_mul c₂)).add
      ((integrable_probe_mul_exp (by linarith)).const_mul c₃)
  have hint_zero : (∫ u : ℝ, poleNeutralTriple p q r u * Real.exp (1 / 2 * u)) = 0 := by
    have hlap := negativeHalfLineLaplace_poleNeutralTriple (ne_of_lt hpq)
      (ne_of_lt (hpq.trans hqr)) (ne_of_lt hqr) (w := (1 / 2 : ℂ))
      (by simp; linarith) (by simp; linarith) (by simp; linarith)
    have h0 : ((1 / 2 : ℂ) ^ 2 - 1 / 4) /
        (((p : ℂ) + 1 / 2) * ((q : ℂ) + 1 / 2) * ((r : ℂ) + 1 / 2)) = 0 := by norm_num
    rw [h0] at hlap
    have hcexp : ((∫ u : ℝ, poleNeutralTriple p q r u * Real.exp (1 / 2 * u) : ℝ) : ℂ) =
        negativeHalfLineLaplace (cx (poleNeutralTriple p q r)) (1 / 2) := by
      unfold negativeHalfLineLaplace
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp [cx, Complex.ofReal_exp, mul_comm]
    exact Complex.ofReal_injective (hcexp.trans hlap)
  have hae : (fun u : ℝ => poleNeutralTriple p q r u * Real.exp (1 / 2 * u)) =ᵐ[volume] 0 :=
    (integral_eq_zero_iff_of_nonneg hnn hint).mp hint_zero
  have hcont_Iio : ContinuousOn (fun u : ℝ => poleNeutralTriple p q r u * Real.exp (1 / 2 * u))
      (Iio 0) := by
    refine (hg_cont.mul (by fun_prop)).continuousOn.congr fun u hu => ?_
    unfold poleNeutralTriple
    rw [probe_of_neg hu, probe_of_neg hu, probe_of_neg hu]
  have heq0 := Measure.eqOn_open_of_ae_eq hae isOpen_Iio hcont_Iio continuousOn_const hu_pos_mem.1
  dsimp only [Pi.zero_apply] at heq0
  exact (ne_of_gt (mul_pos hu_pos_mem.2 (Real.exp_pos _))) heq0

/-- **Complete polar annihilation of `poleNeutralTriple p q r` at ALL shifts `R ∈ ℝ`.**
For `1/2 < p < q < r` and every `R ∈ ℝ`, both `coshHalfMoment` and `sinhHalfMoment` vanish on
`shiftProfile (poleNeutralTriple p q r) R`, leaving only the Gamma and prime pairings in
`bareMixedEnergy`. -/
theorem halfMoments_shiftProfile_poleNeutralTriple_eq_zero {p q r : ℝ}
    (hp : 1 / 2 < p) (hpq : p < q) (hqr : q < r) (R : ℝ) :
    coshHalfMoment (shiftProfile (poleNeutralTriple p q r) R) = 0 ∧
      sinhHalfMoment (shiftProfile (poleNeutralTriple p q r) R) = 0 ∧
      bareMixedEnergy (poleNeutralTriple p q r) (shiftProfile (poleNeutralTriple p q r) R) =
        gammaMixedForm (poleNeutralTriple p q r) (shiftProfile (poleNeutralTriple p q r) R) -
          (primeMixedForm (poleNeutralTriple p q r) (shiftProfile (poleNeutralTriple p q r) R) +
            primeMixedForm (shiftProfile (poleNeutralTriple p q r) R) (poleNeutralTriple p q r)) / 2 := by
  set H := poleNeutralTriple p q r
  set c₁ : ℝ := (p ^ 2 - 1 / 4) / ((p - q) * (p - r))
  set c₂ : ℝ := (q ^ 2 - 1 / 4) / ((q - p) * (q - r))
  set c₃ : ℝ := (r ^ 2 - 1 / 4) / ((r - p) * (r - q))
  have hexp_int : ∀ c : ℝ, -p < c → Integrable fun u : ℝ => H u * Real.exp (c * u) := by
    intro c hc
    have hpt : (fun u : ℝ => H u * Real.exp (c * u)) =
        fun u : ℝ => (c₁ * (probe p u * Real.exp (c * u)) +
          c₂ * (probe q u * Real.exp (c * u))) +
          c₃ * (probe r u * Real.exp (c * u)) := by
      funext u; dsimp [H, poleNeutralTriple]; ring
    rw [hpt]
    exact (((integrable_probe_mul_exp (by linarith)).const_mul c₁).add
      ((integrable_probe_mul_exp (by linarith)).const_mul c₂)).add
      ((integrable_probe_mul_exp (by linarith)).const_mul c₃)
  have hexp_zero : ∀ c : ℝ, c = 1 / 2 ∨ c = -(1 / 2) →
      (∫ u : ℝ, H u * Real.exp (c * u)) = 0 := by
    intro c hc
    have hcp : 0 < p + ((c : ℝ) : ℂ).re := by
      rcases hc with rfl | rfl <;> (simp; linarith)
    have hlap := negativeHalfLineLaplace_poleNeutralTriple (ne_of_lt hpq)
      (ne_of_lt (hpq.trans hqr)) (ne_of_lt hqr) (w := (c : ℂ))
      hcp (by simp at hcp ⊢; linarith) (by simp at hcp ⊢; linarith)
    have hnum0 : ((c : ℂ) ^ 2 - 1 / 4) /
        (((p : ℂ) + c) * ((q : ℂ) + c) * ((r : ℂ) + c)) = 0 := by
      rcases hc with rfl | rfl <;> norm_num
    rw [hnum0] at hlap
    have hcexp : ((∫ u : ℝ, H u * Real.exp (c * u) : ℝ) : ℂ) =
        negativeHalfLineLaplace (cx H) (c : ℂ) := by
      unfold negativeHalfLineLaplace
      rw [← integral_complex_ofReal]
      refine integral_congr_ae (Eventually.of_forall fun u => ?_)
      simp [cx, Complex.ofReal_exp, mul_comm]
    exact Complex.ofReal_injective (hcexp.trans hlap)
  have hi_pos := hexp_int (1 / 2) (by linarith)
  have hi_neg := hexp_int (-(1 / 2)) (by linarith)
  have hHc : Integrable fun u : ℝ => H u * Real.cosh (u / 2) := by
    refine ((hi_pos.add hi_neg).div_const 2).congr (Eventually.of_forall fun u => ?_)
    dsimp only; rw [Real.cosh_eq]; ring_nf
  have hHs : Integrable fun u : ℝ => H u * Real.sinh (u / 2) := by
    refine ((hi_pos.sub hi_neg).div_const 2).congr (Eventually.of_forall fun u => ?_)
    dsimp only; rw [Real.sinh_eq]; ring_nf
  have hC0 : coshHalfMoment H = 0 := by
    unfold coshHalfMoment
    have hpt : (fun x : ℝ => H x * Real.cosh (x / 2)) =
        fun x : ℝ => (H x * Real.exp (1 / 2 * x) + H x * Real.exp (-(1 / 2) * x)) / 2 := by
      funext x; rw [Real.cosh_eq]; ring_nf
    rw [hpt, integral_div, integral_add hi_pos hi_neg,
      hexp_zero (1 / 2) (Or.inl rfl), hexp_zero (-(1 / 2)) (Or.inr rfl)]
    norm_num
  have hS0 : sinhHalfMoment H = 0 := by
    unfold sinhHalfMoment
    have hpt : (fun x : ℝ => H x * Real.sinh (x / 2)) =
        fun x : ℝ => (H x * Real.exp (1 / 2 * x) - H x * Real.exp (-(1 / 2) * x)) / 2 := by
      funext x; rw [Real.sinh_eq]; ring_nf
    rw [hpt, integral_div, integral_sub hi_pos hi_neg,
      hexp_zero (1 / 2) (Or.inl rfl), hexp_zero (-(1 / 2)) (Or.inr rfl)]
    norm_num
  have hCR : coshHalfMoment (shiftProfile H R) = 0 := by
    rw [coshHalfMoment_shiftProfile hHc hHs R, hC0, hS0]; ring
  have hSR : sinhHalfMoment (shiftProfile H R) = 0 := by
    rw [sinhHalfMoment_shiftProfile hHc hHs R, hC0, hS0]; ring
  refine ⟨hCR, hSR, ?_⟩
  unfold bareMixedEnergy
  rw [hC0, hS0, hCR, hSR]
  ring

/-- **Uniform prime-pairing bound for `poleNeutralTriple` under `RiemannHypothesis`.**
Because the polar terms vanish identically and `gammaMixedForm` is uniformly bounded in `R`,
`RiemannHypothesis` forces the pure prime pairing of `(H, shiftProfile H R)` to be uniformly
bounded across all `R ≥ 0`. -/
theorem poleNeutralTriple_primeMixed_bounded_of_riemannHypothesis (hRH : RiemannHypothesis)
    {p q r : ℝ} (hp : 4 < p) (hpq : p < q) (hqr : q < r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ R : ℝ, 0 ≤ R →
      |(primeMixedForm (poleNeutralTriple p q r) (shiftProfile (poleNeutralTriple p q r) R) +
          primeMixedForm (shiftProfile (poleNeutralTriple p q r) R) (poleNeutralTriple p q r)) / 2| ≤
        C := by
  set H := poleNeutralTriple p q r
  have hH := criticalHalfLineEnergyDomain_poleNeutralTriple hp (hp.trans hpq)
    ((hp.trans hpq).trans hqr)
  set Γmax : ℝ := 1 / (2 * Real.pi) * ∫ s : ℝ, ‖paperFT (cx H) s‖ ^ 2 * |EF.gammaBracket s|
  have hΓ_nn : 0 ≤ Γmax := by
    dsimp [Γmax]
    exact mul_nonneg (by positivity)
      (integral_nonneg fun s => mul_nonneg (sq_nonneg _) (abs_nonneg _))
  refine ⟨onLineEnergy H + Γmax, add_nonneg (onLineEnergy_nonneg H) hΓ_nn, fun R hR => ?_⟩
  have hHR := criticalHalfLineEnergyDomain_shiftProfile hH hR
  have hbare_eq := (halfMoments_shiftProfile_poleNeutralTriple_eq_zero (by linarith) hpq hqr R).2.2
  have hon_eq := bareMixedEnergy_eq_onLineMixed_of_riemannHypothesis hRH hH hHR
  have hon_le := abs_onLineMixed_shiftProfile_le hH (finiteOffLine_of_riemannHypothesis hRH) hR
  have hγ_le := abs_gammaMixedForm_shiftProfile_le hH.integrable hH.gamma R
  have hrel : (primeMixedForm H (shiftProfile H R) + primeMixedForm (shiftProfile H R) H) / 2 =
      gammaMixedForm H (shiftProfile H R) - onLineMixed H (shiftProfile H R) := by
    linarith [hbare_eq, hon_eq]
  rw [hrel]
  exact (abs_sub _ _).trans (add_le_add hγ_le hon_le) |>.trans (by linarith)

/-- **Two-sided unboundedness of the pure prime pairing of `poleNeutralTriple` under a single quartet.**
Under `HasSingleOffLineQuartet ρ₀`, for every `4 < p < q < r` and threshold `M : ℝ`, the pure
prime pairing `(primeMixedForm H (shiftProfile H R) + primeMixedForm (shiftProfile H R) H) / 2`
exceeds `M` at some `R₊ ≥ 0` and falls below `-M` at some `R₋ ≥ 0` (with zero polar contribution). -/
theorem poleNeutralTriple_primeMixed_unbounded_of_singleQuartet {ρ₀ : ℂ}
    (hq : HasSingleOffLineQuartet ρ₀) {p q r : ℝ} (hp : 4 < p) (hpq : p < q) (hqr : q < r)
    (M : ℝ) :
    let H := poleNeutralTriple p q r
    (∃ R : ℝ, 0 ≤ R ∧
        M < (primeMixedForm H (shiftProfile H R) + primeMixedForm (shiftProfile H R) H) / 2) ∧
      (∃ R : ℝ, 0 ≤ R ∧
        (primeMixedForm H (shiftProfile H R) + primeMixedForm (shiftProfile H R) H) / 2 < -M) := by
  intro H
  have hq4 : 4 < q := hp.trans hpq
  have hr4 : 4 < r := hq4.trans hqr
  have hH := criticalHalfLineEnergyDomain_poleNeutralTriple hp hq4 hr4
  set zPos : ℂ := ρ₀ - 1 / 2
  set zNeg : ℂ := 1 / 2 - conj ρ₀
  have hzPos_re : zPos.re = ρ₀.re - 1 / 2 := by simp [zPos]
  have hzPos_im : zPos.im = ρ₀.im := by simp [zPos]
  have hzNeg_re : zNeg.re = 1 / 2 - ρ₀.re := by simp [zNeg]
  have hczNeg : conj zNeg = -zPos := by dsimp [zPos, zNeg]; apply Complex.ext <;> simp
  have hLH_pos : negativeHalfLineLaplace (cx H) zPos =
      (zPos ^ 2 - 1 / 4) / (((p : ℂ) + zPos) * ((q : ℂ) + zPos) * ((r : ℂ) + zPos)) :=
    negativeHalfLineLaplace_poleNeutralTriple (ne_of_lt hpq) (ne_of_lt (hpq.trans hqr))
      (ne_of_lt hqr) (by rw [hzPos_re]; linarith [hq.1])
      (by rw [hzPos_re]; linarith [hq.1]) (by rw [hzPos_re]; linarith [hq.1])
  have hLH_neg : negativeHalfLineLaplace (cx H) zNeg =
      (zNeg ^ 2 - 1 / 4) / (((p : ℂ) + zNeg) * ((q : ℂ) + zNeg) * ((r : ℂ) + zNeg)) :=
    negativeHalfLineLaplace_poleNeutralTriple (ne_of_lt hpq) (ne_of_lt (hpq.trans hqr))
      (ne_of_lt hqr) (by rw [hzNeg_re]; linarith [hq.re_lt_one])
      (by rw [hzNeg_re]; linarith [hq.re_lt_one]) (by rw [hzNeg_re]; linarith [hq.re_lt_one])
  -- Nonvanishing of `L H(zPos)` and `L H(zNeg)`: `zPos.im = ρ₀.im ≠ 0` rules out `±1/2` and `-p, -q, -r`.
  have hLH_pos_ne : negativeHalfLineLaplace (cx H) zPos ≠ 0 := by
    rw [hLH_pos]
    have hnum_ne : zPos ^ 2 - 1 / 4 ≠ 0 := by
      rw [show zPos ^ 2 - 1 / 4 = (zPos - 1 / 2) * (zPos + 1 / 2) by ring]
      refine mul_ne_zero (fun h => ?_) (fun h => ?_)
      · have := congrArg Complex.im h; simp [hzPos_im] at this; exact hq.im_ne_zero this
      · have := congrArg Complex.im h; simp [hzPos_im] at this; exact hq.im_ne_zero this
    have hden_ne : ((p : ℂ) + zPos) * ((q : ℂ) + zPos) * ((r : ℂ) + zPos) ≠ 0 :=
      mul_ne_zero (mul_ne_zero
        (fun h => by have := congrArg Complex.re h; simp [hzPos_re] at this; linarith [hq.1])
        (fun h => by have := congrArg Complex.re h; simp [hzPos_re] at this; linarith [hq.1]))
        (fun h => by have := congrArg Complex.re h; simp [hzPos_re] at this; linarith [hq.1])
    exact div_ne_zero hnum_ne hden_ne
  have hLH_neg_ne : negativeHalfLineLaplace (cx H) zNeg ≠ 0 := by
    rw [hLH_neg]
    have hzNeg_im : zNeg.im = ρ₀.im := by simp [zNeg]
    have hnum_ne : zNeg ^ 2 - 1 / 4 ≠ 0 := by
      rw [show zNeg ^ 2 - 1 / 4 = (zNeg - 1 / 2) * (zNeg + 1 / 2) by ring]
      refine mul_ne_zero (fun h => ?_) (fun h => ?_)
      · have := congrArg Complex.im h; simp [hzNeg_im] at this; exact hq.im_ne_zero this
      · have := congrArg Complex.im h; simp [hzNeg_im] at this; exact hq.im_ne_zero this
    have hden_ne : ((p : ℂ) + zNeg) * ((q : ℂ) + zNeg) * ((r : ℂ) + zNeg) ≠ 0 :=
      mul_ne_zero (mul_ne_zero
        (fun h => by have := congrArg Complex.re h; simp [hzNeg_re] at this; linarith [hq.re_lt_one])
        (fun h => by have := congrArg Complex.re h; simp [hzNeg_re] at this; linarith [hq.re_lt_one]))
        (fun h => by have := congrArg Complex.re h; simp [hzNeg_re] at this; linarith [hq.re_lt_one])
    exact div_ne_zero hnum_ne hden_ne
  set w₀ : ℂ := negativeHalfLineLaplace (cx H) zPos * conj (negativeHalfLineLaplace (cx H) zNeg)
  have hw₀_ne : w₀ ≠ 0 := mul_ne_zero hLH_pos_ne (map_ne_zero _ |>.mpr hLH_neg_ne)
  -- Express `dotProduct (quartetEvalVec ρ₀ H) (quartetSwapMatrix *ᵥ quartetEvalVec ρ₀ (shiftProfile H R))`
  have hswap_eq : ∀ R : ℝ,
      dotProduct (quartetEvalVec ρ₀ H)
          (quartetSwapMatrix *ᵥ quartetEvalVec ρ₀ (shiftProfile H R)) =
        Real.exp ((ρ₀.re - 1 / 2) * R) * (w₀ * cexp (I * ((ρ₀.im : ℂ) * (R : ℂ)))).re +
          (conj w₀ * cexp (-(conj zPos * (R : ℂ)))).re := by
    intro R
    have hdot : dotProduct (quartetEvalVec ρ₀ H)
        (quartetSwapMatrix *ᵥ quartetEvalVec ρ₀ (shiftProfile H R)) =
        (negativeHalfLineLaplace (cx H) zPos *
            conj (negativeHalfLineLaplace (cx (shiftProfile H R)) zNeg) +
          negativeHalfLineLaplace (cx H) zNeg *
            conj (negativeHalfLineLaplace (cx (shiftProfile H R)) zPos)).re := by
      rw [quartetSwapMatrix_mulVec]
      unfold quartetEvalVec
      simp only [dotProduct, Fin.sum_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, Complex.add_re, Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    rw [hdot, laplace_shiftProfile, laplace_shiftProfile]
    have ht1 : negativeHalfLineLaplace (cx H) zPos *
        conj (cexp (-(zNeg * (R : ℂ))) * negativeHalfLineLaplace (cx H) zNeg) =
        w₀ * cexp (zPos * (R : ℂ)) := by
      rw [map_mul, ← Complex.exp_conj, map_neg, map_mul, hczNeg, Complex.conj_ofReal,
        neg_mul, neg_neg]
      dsimp [w₀]; ring
    have ht2 : negativeHalfLineLaplace (cx H) zNeg *
        conj (cexp (-(zPos * (R : ℂ))) * negativeHalfLineLaplace (cx H) zPos) =
        conj w₀ * cexp (-(conj zPos * (R : ℂ))) := by
      rw [map_mul, ← Complex.exp_conj, map_neg, map_mul, Complex.conj_ofReal]
      dsimp [w₀]; rw [map_mul, Complex.conj_conj]; ring
    have hexp_split : cexp (zPos * (R : ℂ)) =
        (Real.exp ((ρ₀.re - 1 / 2) * R) : ℂ) * cexp (I * ((ρ₀.im : ℂ) * (R : ℂ))) := by
      have hzR : zPos * (R : ℂ) =
          (((ρ₀.re - 1 / 2) * R : ℝ) : ℂ) + I * ((ρ₀.im : ℂ) * (R : ℂ)) := by
        apply Complex.ext <;> simp [hzPos_re, hzPos_im]
      rw [hzR, Complex.exp_add, ← Complex.ofReal_exp]
    rw [ht1, ht2, hexp_split, Complex.add_re]
    congr 1
    rw [← mul_assoc, mul_comm w₀, mul_assoc, Complex.re_ofReal_mul]
  have hdecay_le : ∀ R : ℝ, 0 ≤ R →
      |(conj w₀ * cexp (-(conj zPos * (R : ℂ)))).re| ≤ ‖w₀‖ := by
    intro R hR
    refine (Complex.abs_re_le_norm _).trans ?_
    rw [norm_mul, Complex.norm_conj, Complex.norm_exp]
    have hre_nonpos : (-(conj zPos * (R : ℂ))).re ≤ 0 := by
      have hzre : (conj zPos).re = ρ₀.re - 1 / 2 := by simp [zPos]
      have : (-(conj zPos * (R : ℂ))).re = -((ρ₀.re - 1 / 2) * R) := by
        simp [Complex.mul_re, hzre]
      rw [this]
      have : 0 ≤ (ρ₀.re - 1 / 2) * R := mul_nonneg (by linarith [hq.1]) hR
      linarith
    calc ‖w₀‖ * Real.exp (-(conj zPos * (R : ℂ))).re
        ≤ ‖w₀‖ * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hre_nonpos)
          (norm_nonneg w₀)
      _ = ‖w₀‖ := mul_one _
  set Γmax : ℝ := 1 / (2 * Real.pi) * ∫ s : ℝ, ‖paperFT (cx H) s‖ ^ 2 * |EF.gammaBracket s|
  have hδ_pos : 0 < ρ₀.re - 1 / 2 := by linarith [hq.1]
  have hm_pos : (0 : ℝ) < 2 * (quartetCopyMult ρ₀ : ℝ) := by
    exact_mod_cast Nat.mul_pos (by decide : 0 < 2) hq.quartetCopyMult_pos
  set B : ℝ := (|M| + Γmax + onLineEnergy H) / (2 * (quartetCopyMult ρ₀ : ℝ)) + ‖w₀‖
  -- Note `(primeMixed + primeMixed_rev)/2 = gammaMixedForm - bareMixedEnergy`.
  -- Large positive primeMixed comes from large NEGATIVE `bareMixedEnergy` (`-w₀`), and vice versa.
  constructor
  · obtain ⟨R, hR, hgt⟩ := exists_nonneg_exp_mul_re_gt (neg_ne_zero.mpr hw₀_ne)
      hq.im_ne_zero hδ_pos B
    refine ⟨R, hR, ?_⟩
    have hHR := criticalHalfLineEnergyDomain_shiftProfile hH hR
    have hbare := (halfMoments_shiftProfile_poleNeutralTriple_eq_zero (by linarith) hpq hqr R).2.2
    have hsq := bareMixedEnergy_singleQuartet hq hH hHR
    rw [hswap_eq R] at hsq
    have hon := (abs_le.mp (abs_onLineMixed_shiftProfile_le hH hq.finiteOffLine hR)).2
    have hγ := (abs_le.mp (abs_gammaMixedForm_shiftProfile_le hH.integrable hH.gamma R)).1
    have hdec := (abs_le.mp (hdecay_le R hR)).2
    have hneg_re : ((-w₀) * cexp (I * ((ρ₀.im : ℂ) * (R : ℂ)))).re =
        -(w₀ * cexp (I * ((ρ₀.im : ℂ) * (R : ℂ)))).re := by simp
    rw [hneg_re, mul_neg] at hgt
    have hlt_div : Real.exp ((ρ₀.re - 1 / 2) * R) * (w₀ * cexp (I * ((ρ₀.im : ℂ) * (R : ℂ)))).re +
        (conj w₀ * cexp (-(conj zPos * (R : ℂ)))).re <
        -((|M| + Γmax + onLineEnergy H) / (2 * (quartetCopyMult ρ₀ : ℝ))) := by
      dsimp [B] at hgt; linarith
    have hmul_lt : 2 * (quartetCopyMult ρ₀ : ℝ) *
        (Real.exp ((ρ₀.re - 1 / 2) * R) * (w₀ * cexp (I * ((ρ₀.im : ℂ) * (R : ℂ)))).re +
          (conj w₀ * cexp (-(conj zPos * (R : ℂ)))).re) <
        -(|M| + Γmax + onLineEnergy H) := by
      have := mul_lt_mul_of_pos_left hlt_div hm_pos
      have hsimp : 2 * (quartetCopyMult ρ₀ : ℝ) *
          -((|M| + Γmax + onLineEnergy H) / (2 * (quartetCopyMult ρ₀ : ℝ))) =
          -(|M| + Γmax + onLineEnergy H) := by field_simp [hm_pos.ne']
      rwa [hsimp] at this
    linarith [le_abs_self M, hbare, hsq, hon, hγ]
  · obtain ⟨R, hR, hgt⟩ := exists_nonneg_exp_mul_re_gt hw₀_ne hq.im_ne_zero hδ_pos B
    refine ⟨R, hR, ?_⟩
    have hHR := criticalHalfLineEnergyDomain_shiftProfile hH hR
    have hbare := (halfMoments_shiftProfile_poleNeutralTriple_eq_zero (by linarith) hpq hqr R).2.2
    have hsq := bareMixedEnergy_singleQuartet hq hH hHR
    rw [hswap_eq R] at hsq
    have hon := (abs_le.mp (abs_onLineMixed_shiftProfile_le hH hq.finiteOffLine hR)).1
    have hγ := (abs_le.mp (abs_gammaMixedForm_shiftProfile_le hH.integrable hH.gamma R)).2
    have hdec := (abs_le.mp (hdecay_le R hR)).1
    have hgt_div : (|M| + Γmax + onLineEnergy H) / (2 * (quartetCopyMult ρ₀ : ℝ)) <
        Real.exp ((ρ₀.re - 1 / 2) * R) * (w₀ * cexp (I * ((ρ₀.im : ℂ) * (R : ℂ)))).re +
          (conj w₀ * cexp (-(conj zPos * (R : ℂ)))).re := by
      dsimp [B] at hgt; linarith
    have hmul_gt := (div_lt_iff₀ hm_pos).mp hgt_div
    linarith [le_abs_self M, hbare, hsq, hon, hγ, hmul_gt]

/-- **One-sided upper bound on the pole-neutral prime pairing excludes all single quartets.** -/
theorem not_hasSingleOffLineQuartet_of_poleNeutralTriple_primeMixed_bddAbove
    {p q r : ℝ} (hp : 4 < p) (hpq : p < q) (hqr : q < r)
    (hbdd : ∃ M : ℝ, ∀ R : ℝ, 0 ≤ R →
      (primeMixedForm (poleNeutralTriple p q r) (shiftProfile (poleNeutralTriple p q r) R) +
        primeMixedForm (shiftProfile (poleNeutralTriple p q r) R) (poleNeutralTriple p q r)) / 2 ≤
        M) :
    ∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀ := by
  obtain ⟨M, hM⟩ := hbdd
  intro ρ₀ hq
  obtain ⟨⟨R, hR, hgt⟩, -⟩ :=
    poleNeutralTriple_primeMixed_unbounded_of_singleQuartet hq hp hpq hqr M
  exact not_lt.mpr (hM R hR) hgt

/-- **One-sided lower bound on the pole-neutral prime pairing excludes all single quartets.** -/
theorem not_hasSingleOffLineQuartet_of_poleNeutralTriple_primeMixed_bddBelow
    {p q r : ℝ} (hp : 4 < p) (hpq : p < q) (hqr : q < r)
    (hbdd : ∃ M : ℝ, ∀ R : ℝ, 0 ≤ R →
      M ≤ (primeMixedForm (poleNeutralTriple p q r) (shiftProfile (poleNeutralTriple p q r) R) +
        primeMixedForm (shiftProfile (poleNeutralTriple p q r) R) (poleNeutralTriple p q r)) / 2) :
    ∀ ρ₀ : ℂ, ¬ HasSingleOffLineQuartet ρ₀ := by
  obtain ⟨M, hM⟩ := hbdd
  intro ρ₀ hq
  obtain ⟨-, ⟨R, hR, hlt⟩⟩ :=
    poleNeutralTriple_primeMixed_unbounded_of_singleQuartet hq hp hpq hqr (-M)
  rw [neg_neg] at hlt
  exact not_lt.mpr (hM R hR) hlt

end GaloisForLFunctions.ExclusionOfTheCriticalState
