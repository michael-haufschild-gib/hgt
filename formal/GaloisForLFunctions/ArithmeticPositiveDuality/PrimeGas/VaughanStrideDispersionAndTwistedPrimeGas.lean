import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.LiouvilleSquareSieveAndMultiScaleEuler
import GaloisForLFunctions.BezoutValuationIncidence.VaughanTypeIIShortAndAllHorizonMobiusL2Energy
import GaloisForLFunctions.ArithmeticProduction.BilinearFormsAreParityBlind
import GaloisForLFunctions.ArithmeticGaugeTheory.TheSpecialLocusReadsGRH
import GaloisForLFunctions.RHTower.CharacterSumMeanValue
import GaloisForLFunctions.RHTower.DirichletLLogStrip
import GaloisForLFunctions.RHTower.Sieve.GapSums

/-!
# Vaughan Stride Dispersion, Periodic Euler–Fourier Acceleration, and Twisted Prime-Gas Power Cancellation

Uniform Type-II bilinear operator norms on arbitrary boxes are invariant under completely
multiplicative `±1` twists (`BilinearFormsAreParityBlind.bilinearConstants_liouvilleTwist`), and any
restricted test class stable under `λ(n) = (-1)^{Ω(n)}` inherits the same blindness
(`BilinearFormsAreParityBlind.classConstants_twist`). By contrast, additive cutoff-shift operators
(`strideAvg` and its modulus-`q` generalization `strideMean q d`) act by additive translation
`X ↦ X + r d` rather than multiplicative scaling, breaking `λ`-twist stability.

This module combines `BezoutValuationIncidence.moebius_vaughan_identity` on trans-horizon quotient
windows `(D, Y / m]`, multi-scale additive stride-mean operators, and Dirichlet / `ℚ(ω)` Hecke
character twists of the Prime-Gas Möbius and Liouville occupation identities across all heights
`Im s ∈ ℝ`:

1. **Modulus-`q` commuting stride-mean operators and explicit bypass of `classConstants_twist`
   (`strideMean_comm`, `iterate_strideMean_div_eq`, `not_liouvilleTwist_stable_additiveStridePairClass`,
   `classConstants_singleStrideTestClass_liouvilleTwist_ne`):**
   `strideMean q d F X = q⁻¹ ∑_{r < q} F(X + r d)` commutes across all `(q₁, d₁), (q₂, d₂)`,
   collapses floor-quotient channels `Y ↦ G(Y / d)` to `(strideMean q 1)^[M] G (X / d)`, refutes
   the multiplicative-sign stability hypothesis of `ArithmeticProduction.classConstants_twist`, and
   strictly separates `classConstants` of `a = 1` from `liouvilleTwist a`.
2. **Trans-horizon Vaughan decomposition inside `multiStrideEuler` and sublinear `3001/24000`
   strip bounds (`highDivisorMoebiusEta_eq_dual_quotient_windows`,
   `highDivisorMoebiusEta_eq_vaughanTypeI_add_typeII`,
   `norm_multiStrideEuler_vaughan_typeI_or_typeII_ge_of_zeta_eq_zero`,
   `exists_sublinear_moebius_and_liouville_on_remaining_strip`):**
   Substituting `moebius_vaughan_apply_of_gt` (`U, V ≤ D`) on every trans-horizon quotient window
   `(D, Y / m]` splits the high-divisor Möbius sum into explicit Type-I and Type-II bilinear pieces,
   at least one of which is forced above `(‖1 - 2^{1-z}‖ - 3 D / 2^{M/2}) / 2` at any hypothetical
   zero `ζ(z) = 0`. Across the entire remaining strip `3001/24000 ≤ Re s < 1/2` (`∀ Im s ∈ ℝ`),
   `SubSevenEighthsZeroFreeHalfPlane` yields unconditional `O_{s, ε}(N^{Re s - 3001/24000 + ε})`
   cancellation (saving `> N^{5/8}` over trivial `N`) on both `moebiusPoly` and `liouvillePoly` at
   `1 - conj s`.
3. **Universal modulus-`q` periodic Euler–Fourier acceleration, `ℚ(ω)` Hecke base change, and
   special-locus zero-abscissa confinement (`norm_LFunction_sub_periodicEulerPartialSum_le`,
   `periodicEulerTailBound_linear_le`, `subSevenEighths_periodicEuler_beats_tail_all_heights`,
   `subOneEighth_primitive_periodicEuler_beats_tail_all_heights`,
   `hecke_dirichletBaseChange_beats_tail_on_subSevenEighths`,
   `gaugeExponent_moebius_dirichletGauge_le_sub_seven_eighths`):**
   Expanding any nonprincipal `χ : DirichletCharacter ℂ q` (`q ≥ 2`) in `q`-th roots of unity
   decomposes `χ.LFunction z - periodicEulerPartialSum χ N M z` into `(M + 1)`-st twisted `q`-mean
   differences, yielding base-`2^{-M}` exponential decay `≤ q^3 (2 M + 1) / 2^M` at linear cutoff
   `N = 2 q M + q - 1` across **all** moduli `q ≥ 2` and **all** heights `|Im z| ≤ M`, certifying
   finite partial sums across `Re z > 20999/24000` (and primitive `χ` on `0 < Re s < 3001/24000`)
   and confining `gaugeExponent moebiusSource (dirichletGauge χ + verticalShift t) ∈ [1/2, 20999/24000]`.
4. **Twisted Prime-Gas occupation identities and quadratic double-energy floor
   (`sum_twistedMoebius_mul_charPartialSum_eq_one`,
   `norm_multiStrideMean_twistedMoebius_highDivisors_ge_of_LFunction_eq_zero`,
   `sum_twistedLiouville_mul_charPartialSum_eq_squareCharHead`,
   `norm_quadratic_LFunction_two_mul_refl_ge`):**
   Twisting by `χ` yields the exact zero-tail Möbius identity `μ χ ⋆ χ = 1` (`∀ X ≥ 1, ∀ z ∈ ℂ`)
   and the exact square-sieve identity `λ χ ⋆ χ = ∑_{k ≤ √X} χ(k)^2 k^{-2w}`, with height-uniform
   floor `(∏_{p ∣ q} (1 - p⁻¹)) (1 - 2 Re s) / (2 - 2 Re s) > 0` on `0 < Re s < 1/2` when `χ^2 = 1`.
5. **Exact Vaughan `typeIIShort` factorization and unconditional all-height power cancellation
   beyond `3001/24000` across all `0 < Re s < 1/2` (`vaughanEulerDefect_eq_typeIIShort_sub_tail`,
   `sum_normSq_vaughanEulerDefect_le`,
   `power_saving_dirichlet_euler_witnesses_beyond_sub_one_eighth`):**
   `1 - M_{D, χ}(w) · periodicEulerPartialSum χ N M w` factors on `(D, N]` through
   `RHTower.Sieve.typeIIShort D n · χ(n) n^{-w}` (`VaughanTypeIIShortAndAllHorizonMobiusL2Energy`).
   Splitting at `q` and combining character orthogonality (`RHTower.meanValue_charSum`) with the
   divisor-square moment (`sum_card_divisors_sq_le` + `invSum_le_one_add_log`) proves unconditional
   polynomial power cancellation `O_s(φ(q) q^{-(1 - 2 Re s)^2 / 4})` across **every** `0 < Re s < 1/2`
   (strictly beyond `3001/24000` up to `1/2`) and **every** height `Im s ∈ ℝ`, certifying linear-prefix
   Euler witnesses and nonvanishing `χ.LFunction s ≠ 0` for all but `o(φ(q))` characters mod `q`.
-/

noncomputable section

open Complex Filter Set
open scoped BigOperators ComplexConjugate Topology

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open _root_.RHTower.DQPT

/-! ### 1. Modulus-`q` Commuting Stride-Mean Operators and `λ`-Twist Parity-Breaking -/

/-- Modulus-`q`, stride-`d` additive shift-averaging operator on `ℕ → ℂ`:
`strideMean q d F X = q⁻¹ ∑_{r=0}^{q-1} F(X + r d)`. At `q = 2` this recovers `strideAvg d`. -/
def strideMean (q d : ℕ) (F : ℕ → ℂ) (X : ℕ) : ℂ :=
  (q : ℂ)⁻¹ * ∑ r ∈ Finset.range q, F (X + r * d)

@[simp]
lemma strideMean_apply (q d : ℕ) (F : ℕ → ℂ) (X : ℕ) :
    strideMean q d F X = (q : ℂ)⁻¹ * ∑ r ∈ Finset.range q, F (X + r * d) := rfl

/-- At `q = 2`, `strideMean 2 d` coincides identically with `strideAvg d`. -/
theorem strideMean_two_eq_strideAvg (d : ℕ) (F : ℕ → ℂ) :
    strideMean 2 d F = strideAvg d F := by
  funext X
  rw [strideMean_apply, strideAvg_apply, Finset.sum_range_succ, Finset.range_one,
    Finset.sum_singleton, zero_mul, add_zero, one_mul]
  norm_num

lemma strideMean_const {q : ℕ} (hq : 1 ≤ q) (d : ℕ) (c : ℂ) :
    strideMean q d (fun _ => c) = fun _ => c := by
  funext X
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [strideMean_apply, Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
    inv_mul_cancel₀ hq0, one_mul]

lemma strideMean_add (q d : ℕ) (F G : ℕ → ℂ) :
    strideMean q d (fun X => F X + G X) = fun X => strideMean q d F X + strideMean q d G X := by
  funext X
  rw [strideMean_apply, strideMean_apply, strideMean_apply, Finset.sum_add_distrib, mul_add]

lemma strideMean_smul (q d : ℕ) (c : ℂ) (F : ℕ → ℂ) :
    strideMean q d (fun X => c * F X) = fun X => c * strideMean q d F X := by
  funext X
  rw [strideMean_apply, strideMean_apply, ← Finset.mul_sum, ← mul_assoc, mul_comm (q : ℂ)⁻¹ c,
    mul_assoc]

/-- Commutativity of additive stride-mean operators across all moduli `q₁, q₂` and strides `d₁, d₂`. -/
theorem strideMean_comm (q₁ d₁ q₂ d₂ : ℕ) (F : ℕ → ℂ) :
    strideMean q₁ d₁ (strideMean q₂ d₂ F) = strideMean q₂ d₂ (strideMean q₁ d₁ F) := by
  funext X
  simp only [strideMean_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r₂ _ => Finset.sum_congr rfl fun r₁ _ => ?_
  have hshift : X + r₁ * d₁ + r₂ * d₂ = X + r₂ * d₂ + r₁ * d₁ := by omega
  rw [hshift]
  ring

private lemma strideMean_iterate_comm_one (q₁ d₁ q₂ d₂ M₂ : ℕ) (F : ℕ → ℂ) :
    strideMean q₁ d₁ ((strideMean q₂ d₂)^[M₂] F) =
      (strideMean q₂ d₂)^[M₂] (strideMean q₁ d₁ F) := by
  induction M₂ generalizing F with
  | zero => rfl
  | succ M₂ ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', strideMean_comm, ih]

theorem iterate_strideMean_comm (q₁ d₁ q₂ d₂ M₁ M₂ : ℕ) (F : ℕ → ℂ) :
    (strideMean q₁ d₁)^[M₁] ((strideMean q₂ d₂)^[M₂] F) =
      (strideMean q₂ d₂)^[M₂] ((strideMean q₁ d₁)^[M₁] F) := by
  induction M₁ generalizing F with
  | zero => rfl
  | succ M₁ ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, strideMean_iterate_comm_one]

lemma iterate_strideMean_add (q d M : ℕ) (F G : ℕ → ℂ) :
    (strideMean q d)^[M] (fun X => F X + G X) =
      fun X => (strideMean q d)^[M] F X + (strideMean q d)^[M] G X := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [Function.iterate_succ_apply', ih, strideMean_add]
    funext X
    simp only [Function.iterate_succ_apply']

lemma iterate_strideMean_smul (q d M : ℕ) (c : ℂ) (F : ℕ → ℂ) :
    (strideMean q d)^[M] (fun X => c * F X) = fun X => c * (strideMean q d)^[M] F X := by
  induction M with
  | zero => rfl
  | succ M ih =>
    rw [Function.iterate_succ_apply', ih, strideMean_smul]
    funext X
    simp only [Function.iterate_succ_apply']

lemma iterate_strideMean_const {q : ℕ} (hq : 1 ≤ q) (d M : ℕ) (c : ℂ) :
    (strideMean q d)^[M] (fun _ => c) = fun _ => c := by
  induction M with
  | zero => rfl
  | succ M ih => rw [Function.iterate_succ_apply', ih, strideMean_const hq]

lemma iterate_strideMean_finset_sum {ι : Type*} (s : Finset ι) (q d M : ℕ) (F : ι → ℕ → ℂ) :
    (strideMean q d)^[M] (fun X => ∑ i ∈ s, F i X) =
      fun X => ∑ i ∈ s, (strideMean q d)^[M] (F i) X := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hempty : (fun X : ℕ => ∑ i ∈ (∅ : Finset ι), F i X) = fun _ => (0 : ℂ) := by
      funext X; exact Finset.sum_empty
    have hzero : (strideMean q d)^[M] (fun _ => (0 : ℂ)) = fun _ => (0 : ℂ) := by
      induction M with
      | zero => rfl
      | succ M ih =>
        rw [Function.iterate_succ_apply', ih]
        funext X; simp [strideMean_apply]
    rw [hempty, hzero]
    funext X
    exact Finset.sum_empty.symm
  | insert a s ha ih =>
    have hsplit : (fun X => ∑ i ∈ insert a s, F i X) =
        fun X => F a X + ∑ i ∈ s, F i X := by
      funext X; exact Finset.sum_insert ha
    rw [hsplit, iterate_strideMean_add, ih]
    funext X
    exact (Finset.sum_insert (f := fun i => (strideMean q d)^[M] (F i) X) ha).symm

/-- **Exact floor-quotient channel collapse:** iterating `strideMean q d` `M` times on `Y ↦ G(Y / d)`
(`d > 0`) collapses identically to `(strideMean q 1)^[M] G (X / d)`. -/
theorem iterate_strideMean_div_eq (q : ℕ) {d : ℕ} (hd : 0 < d) (M : ℕ) (G : ℕ → ℂ) :
    (strideMean q d)^[M] (fun Y => G (Y / d)) =
      fun X => (strideMean q 1)^[M] G (X / d) := by
  induction M with
  | zero => rfl
  | succ M ih =>
    funext X
    rw [Function.iterate_succ_apply', ih, strideMean_apply, Function.iterate_succ_apply',
      strideMean_apply]
    congr 1
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Nat.add_mul_div_right X r hd, mul_one]

/-- Commuting product of `M`-fold modulus-`q` stride-mean operators across a stride list `ds`. -/
def multiStrideMean (q : ℕ) (ds : List ℕ) (M : ℕ) (F : ℕ → ℂ) : ℕ → ℂ :=
  ds.foldr (fun d G => (strideMean q d)^[M] G) F

lemma multiStrideMean_nil (q M : ℕ) (F : ℕ → ℂ) : multiStrideMean q [] M F = F := rfl

lemma multiStrideMean_cons (q d : ℕ) (ds : List ℕ) (M : ℕ) (F : ℕ → ℂ) :
    multiStrideMean q (d :: ds) M F = (strideMean q d)^[M] (multiStrideMean q ds M F) := rfl

theorem multiStrideMean_two_eq_multiStrideEuler (ds : List ℕ) (M : ℕ) (F : ℕ → ℂ) :
    multiStrideMean 2 ds M F = multiStrideEuler ds M F := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    have hfun : strideMean 2 d = strideAvg d := funext (strideMean_two_eq_strideAvg d)
    rw [multiStrideMean_cons, multiStrideEuler_cons, ih, hfun]

lemma multiStrideMean_add (q : ℕ) (ds : List ℕ) (M : ℕ) (F G : ℕ → ℂ) :
    multiStrideMean q ds M (fun X => F X + G X) =
      fun X => multiStrideMean q ds M F X + multiStrideMean q ds M G X := by
  induction ds with
  | nil => rfl
  | cons d ds ih => rw [multiStrideMean_cons, ih, iterate_strideMean_add]; rfl

lemma multiStrideMean_smul (q : ℕ) (ds : List ℕ) (M : ℕ) (c : ℂ) (F : ℕ → ℂ) :
    multiStrideMean q ds M (fun X => c * F X) = fun X => c * multiStrideMean q ds M F X := by
  induction ds with
  | nil => rfl
  | cons d ds ih => rw [multiStrideMean_cons, ih, iterate_strideMean_smul]; rfl

lemma multiStrideMean_finset_sum {ι : Type*} (s : Finset ι) (q : ℕ) (ds : List ℕ) (M : ℕ)
    (F : ι → ℕ → ℂ) :
    multiStrideMean q ds M (fun X => ∑ i ∈ s, F i X) =
      fun X => ∑ i ∈ s, multiStrideMean q ds M (F i) X := by
  induction ds with
  | nil => rfl
  | cons d ds ih => rw [multiStrideMean_cons, ih, iterate_strideMean_finset_sum]; rfl

private lemma norm_iterate_strideMean_sub_const_le_of_window {q : ℕ} (hq : 1 ≤ q) (d M : ℕ)
    (F : ℕ → ℂ) (L : ℂ) {B : ℝ} {X₀ : ℕ}
    (hB : ∀ Y : ℕ, X₀ ≤ Y → Y ≤ X₀ + M * (q - 1) * d → ‖F Y - L‖ ≤ B) :
    ‖(strideMean q d)^[M] F X₀ - L‖ ≤ B := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  induction M generalizing X₀ with
  | zero => exact hB X₀ le_rfl (by simp)
  | succ M ih =>
    rw [Function.iterate_succ_apply', strideMean_apply]
    have hconst : L = (q : ℂ)⁻¹ * ∑ _r ∈ Finset.range q, L := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ hq0, one_mul]
    have hdiff : (q : ℂ)⁻¹ * (∑ r ∈ Finset.range q, (strideMean q d)^[M] F (X₀ + r * d)) - L =
        (q : ℂ)⁻¹ * ∑ r ∈ Finset.range q, ((strideMean q d)^[M] F (X₀ + r * d) - L) := by
      conv_lhs => rw [hconst]
      rw [← mul_sub, ← Finset.sum_sub_distrib]
    rw [hdiff, norm_mul, norm_inv, Complex.norm_natCast]
    calc (q : ℝ)⁻¹ * ‖∑ r ∈ Finset.range q, ((strideMean q d)^[M] F (X₀ + r * d) - L)‖
        ≤ (q : ℝ)⁻¹ * ∑ r ∈ Finset.range q, ‖(strideMean q d)^[M] F (X₀ + r * d) - L‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hq_pos.le)
      _ ≤ (q : ℝ)⁻¹ * ∑ _r ∈ Finset.range q, B := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r hr => ?_)
            (inv_nonneg.mpr hq_pos.le)
          have hr_lt : r < q := Finset.mem_range.mp hr
          have hr_le : r ≤ q - 1 := by omega
          refine ih fun Y hlo hhi => hB Y (by omega) ?_
          have hrd : r * d ≤ (q - 1) * d := Nat.mul_le_mul_right d hr_le
          have hstep : M * (q - 1) * d + (q - 1) * d = (M + 1) * (q - 1) * d := by ring
          omega
      _ = B := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
            inv_mul_cancel₀ hq_pos.ne', one_mul]

/-- Window contractivity of `multiStrideMean q ds M` on `[X₀, X₀ + M (q - 1) ds.sum]`. -/
theorem norm_multiStrideMean_sub_const_le_of_window {q : ℕ} (hq : 1 ≤ q) (ds : List ℕ) (M : ℕ)
    (F : ℕ → ℂ) (L : ℂ) {B : ℝ} {X₀ : ℕ}
    (hB : ∀ Y : ℕ, X₀ ≤ Y → Y ≤ X₀ + M * (q - 1) * ds.sum → ‖F Y - L‖ ≤ B) :
    ‖multiStrideMean q ds M F X₀ - L‖ ≤ B := by
  induction ds generalizing X₀ with
  | nil =>
    simpa only [multiStrideMean_nil, List.sum_nil, mul_zero, add_zero] using hB X₀ le_rfl le_rfl
  | cons d ds ih =>
    rw [multiStrideMean_cons]
    refine norm_iterate_strideMean_sub_const_le_of_window hq d M (multiStrideMean q ds M F) L
      fun Y hlo hhi => ih fun Z hZlo hZhi => hB Z (hlo.trans hZlo) ?_
    rw [List.sum_cons, Nat.mul_add]
    omega

theorem norm_multiStrideMean_le_of_window {q : ℕ} (hq : 1 ≤ q) (ds : List ℕ) (M : ℕ) (F : ℕ → ℂ)
    {B : ℝ} {X₀ : ℕ}
    (hB : ∀ Y : ℕ, X₀ ≤ Y → Y ≤ X₀ + M * (q - 1) * ds.sum → ‖F Y‖ ≤ B) :
    ‖multiStrideMean q ds M F X₀‖ ≤ B := by
  simpa only [sub_zero] using
    norm_multiStrideMean_sub_const_le_of_window hq ds M F 0 (by simpa only [sub_zero] using hB)

private lemma multiStrideMean_congr_of_window {q : ℕ} (hq : 1 ≤ q) (ds : List ℕ) (M : ℕ)
    {F G : ℕ → ℂ} {X₀ : ℕ}
    (hFG : ∀ Y : ℕ, X₀ ≤ Y → Y ≤ X₀ + M * (q - 1) * ds.sum → F Y = G Y) :
    multiStrideMean q ds M F X₀ = multiStrideMean q ds M G X₀ := by
  have h0 : ‖multiStrideMean q ds M (fun Y => F Y - G Y) X₀‖ ≤ 0 :=
    norm_multiStrideMean_le_of_window hq ds M _ fun Y hlo hhi => by
      rw [hFG Y hlo hhi, sub_self, norm_zero]
  have hsub : multiStrideMean q ds M F X₀ =
      multiStrideMean q ds M G X₀ + multiStrideMean q ds M (fun Y => F Y - G Y) X₀ := by
    have h := congrFun (multiStrideMean_add q ds M G (fun Y => F Y - G Y)) X₀
    have hfg : (fun Y => G Y + (F Y - G Y)) = F := funext fun Y => by ring
    rwa [hfg] at h
  rw [hsub, norm_le_zero_iff.mp h0, add_zero]

private lemma iterate_strideMean_multiStrideMean_comm (q d : ℕ) (ds : List ℕ) (M : ℕ)
    (F : ℕ → ℂ) :
    (strideMean q d)^[M] (multiStrideMean q ds M F) =
      multiStrideMean q ds M ((strideMean q d)^[M] F) := by
  induction ds with
  | nil => rfl
  | cons b tl ih =>
    rw [multiStrideMean_cons, multiStrideMean_cons, ← ih, iterate_strideMean_comm]

private lemma exists_multiStrideMean_pull_mem (q : ℕ) {d : ℕ} {ds : List ℕ} (hmem : d ∈ ds)
    (M : ℕ) (F : ℕ → ℂ) :
    ∃ rest : List ℕ, rest.sum + d = ds.sum ∧
      multiStrideMean q ds M F = multiStrideMean q rest M ((strideMean q d)^[M] F) := by
  induction ds with
  | nil => cases hmem
  | cons a tl ih =>
    rcases List.mem_cons.mp hmem with rfl | htl
    · exact ⟨tl, by rw [List.sum_cons]; omega, iterate_strideMean_multiStrideMean_comm q d tl M F⟩
    · obtain ⟨rest, hsum, heq⟩ := ih htl
      exact ⟨a :: rest, by rw [List.sum_cons, List.sum_cons]; omega,
        by rw [multiStrideMean_cons, heq, ← multiStrideMean_cons]⟩

/-- Real additive two-point stride test class `(1_{m = X} + 1_{m = X + d}) / 2` representing
`strideAvg d` in the first slot of `ArithmeticProduction.bilinearForm`. -/
def additiveStridePairClass : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
  {p | ∃ X d : ℕ, 1 ≤ X ∧ 1 ≤ d ∧
    p.1 = fun m => (if m = X then (1 / 2 : ℝ) else 0) + (if m = X + d then (1 / 2 : ℝ) else 0)}

/-- Singleton test class generated by the unit-stride two-point average at `X = 1, d = 1`. -/
def singleStrideTestClass : Set ((ℕ → ℝ) × (ℕ → ℝ)) :=
  {((fun m => (if m = 1 then (1 / 2 : ℝ) else 0) + (if m = 2 then (1 / 2 : ℝ) else 0)),
    (fun n => if n = 1 then (1 : ℝ) else 0))}

/-- **Additive stride test vectors break multiplicative `λ`-twist stability:** `additiveStridePairClass`
refutes the sign-invariance premise `h𝒞` of `ArithmeticProduction.classConstants_twist` for
`isMultiplicativeSign_liouville`. -/
theorem not_liouvilleTwist_stable_additiveStridePairClass :
    ¬ (∀ p ∈ additiveStridePairClass,
      ((fun m => ((-1 : ℝ) ^ ArithmeticFunction.cardFactors m) * p.1 m),
       (fun n => ((-1 : ℝ) ^ ArithmeticFunction.cardFactors n) * p.2 n)) ∈
        additiveStridePairClass) := by
  intro hstab
  let p₀ : (ℕ → ℝ) × (ℕ → ℝ) :=
    ((fun m => (if m = 1 then (1 / 2 : ℝ) else 0) + (if m = 2 then (1 / 2 : ℝ) else 0)),
     (fun n => if n = 1 then (1 : ℝ) else 0))
  have hp₀ : p₀ ∈ additiveStridePairClass := ⟨1, 1, le_rfl, le_rfl, rfl⟩
  obtain ⟨X, d, _, _, hfst⟩ := hstab p₀ hp₀
  have hval := congrFun hfst 2
  have hcf2 : ArithmeticFunction.cardFactors 2 = 1 :=
    ArithmeticFunction.cardFactors_apply_prime Nat.prime_two
  dsimp only [p₀] at hval
  rw [hcf2] at hval
  have hnonneg : (0 : ℝ) ≤ (if 2 = X then (1 / 2 : ℝ) else 0) +
      (if 2 = X + d then (1 / 2 : ℝ) else 0) :=
    add_nonneg (by split_ifs <;> norm_num) (by split_ifs <;> norm_num)
  norm_num at hval
  linarith

/-- **Strict parity-breaking of `classConstants` under `strideAvg`:** unlike unrestricted
`bilinearConstants` (`BilinearFormsAreParityBlind.bilinearConstants_liouvilleTwist`), restricting to
the unit-stride average `singleStrideTestClass ⊆ additiveStridePairClass` strictly separates the
admissible constants of `a = 1` from its Liouville twist `liouvilleTwist a` on `{1, 2} × {1}`. -/
theorem classConstants_singleStrideTestClass_liouvilleTwist_ne :
    singleStrideTestClass ⊆ additiveStridePairClass ∧
    GaloisForLFunctions.ArithmeticProduction.classConstants singleStrideTestClass
        ({1, 2} : Finset ℕ) ({1} : Finset ℕ)
        (GaloisForLFunctions.ArithmeticOfSquareRootPrecision.liouvilleTwist (fun _ => (1 : ℝ))) ≠
      GaloisForLFunctions.ArithmeticProduction.classConstants singleStrideTestClass
        ({1, 2} : Finset ℕ) ({1} : Finset ℕ) (fun _ => (1 : ℝ)) := by
  refine ⟨?_, ?_⟩
  · intro p hp
    rw [Set.mem_singleton_iff.mp hp]
    exact ⟨1, 1, le_rfl, le_rfl, rfl⟩
  · intro heq
    have h0_mem : (0 : ℝ) ∈ GaloisForLFunctions.ArithmeticProduction.classConstants
        singleStrideTestClass ({1, 2} : Finset ℕ) ({1} : Finset ℕ)
        (GaloisForLFunctions.ArithmeticOfSquareRootPrecision.liouvilleTwist (fun _ => (1 : ℝ))) := by
      intro p hp
      rw [Set.mem_singleton_iff.mp hp]
      unfold GaloisForLFunctions.ArithmeticProduction.bilinearForm
        GaloisForLFunctions.ArithmeticOfSquareRootPrecision.liouvilleTwist
      rw [Finset.sum_pair (by decide : (1 : ℕ) ≠ 2), Finset.sum_singleton, Finset.sum_singleton]
      have hcf1 : ArithmeticFunction.cardFactors 1 = 0 := ArithmeticFunction.cardFactors_one
      have hcf2 : ArithmeticFunction.cardFactors 2 = 1 :=
        ArithmeticFunction.cardFactors_apply_prime Nat.prime_two
      norm_num [hcf1, hcf2]
    rw [heq] at h0_mem
    let p₀ : (ℕ → ℝ) × (ℕ → ℝ) :=
      ((fun m => (if m = 1 then (1 / 2 : ℝ) else 0) + (if m = 2 then (1 / 2 : ℝ) else 0)),
       (fun n => if n = 1 then (1 : ℝ) else 0))
    have h0_untwist := h0_mem p₀ (Set.mem_singleton p₀)
    dsimp only [p₀] at h0_untwist
    unfold GaloisForLFunctions.ArithmeticProduction.bilinearForm at h0_untwist
    rw [Finset.sum_pair (by decide : (1 : ℕ) ≠ 2), Finset.sum_singleton, Finset.sum_singleton]
      at h0_untwist
    norm_num at h0_untwist

/-! ### 2. Trans-Horizon Vaughan Decomposition Inside `multiStrideEuler` & Sublinear `3001/24000` Bounds -/

/-- Truncated Möbius Dirichlet polynomial `∑_{d=1}^N μ(d) d^{-w}`. -/
def moebiusPoly (N : ℕ) (w : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-w)

/-- Vaughan Type-I high-divisor Dirichlet–eta sum on `(D, Y]` (`U, V ≤ D`), corresponding to
`-((ζ * truncAF μ U * truncAF μ V) d)` in `BezoutValuationIncidence.moebius_vaughan_apply_of_gt`. -/
def vaughanHighTypeI (U V D : ℕ) (z : ℂ) (Y : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc (D + 1) Y,
    -((((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U *
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) V) d : ℝ) : ℂ) *
      (d : ℂ) ^ (-z) * dqptAltPartialSum z (Y / d)

/-- Vaughan Type-II high-divisor Dirichlet–eta sum on `(D, Y]` (`U, V ≤ D`), corresponding to
`(((μ - truncAF μ U) * typeIIShort V) d)` in `BezoutValuationIncidence.moebius_vaughan_apply_of_gt`. -/
def vaughanHighTypeII (U V D : ℕ) (z : ℂ) (Y : ℕ) : ℂ :=
  ∑ d ∈ Finset.Icc (D + 1) Y,
    (((((ArithmeticFunction.moebius : ArithmeticFunction ℝ) -
        _root_.RHTower.Sieve.truncAF (ArithmeticFunction.moebius : ArithmeticFunction ℝ) U) *
        _root_.RHTower.Sieve.typeIIShort V) d : ℝ) : ℂ) *
      (d : ℂ) ^ (-z) * dqptAltPartialSum z (Y / d)

/-- **Dual trans-horizon quotient-window identity:** swapping `d` and `m` rewrites the high-divisor
Möbius–eta sum on `D < d ≤ Y` into alternating sums of Möbius Dirichlet windows on `(D, Y / m]`. -/
theorem highDivisorMoebiusEta_eq_dual_quotient_windows (D Y : ℕ) (z : ℂ) :
    (∑ d ∈ Finset.Icc (D + 1) Y,
        (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-z) * dqptAltPartialSum z (Y / d)) =
      ∑ m ∈ Finset.Icc 1 (Y / (D + 1)),
        (-1 : ℂ) ^ (m - 1) * (m : ℂ) ^ (-z) *
          ∑ d ∈ Finset.Ioc D (Y / m), (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-z) := by
  have halt : ∀ K : ℕ, dqptAltPartialSum z K =
      ∑ m ∈ Finset.Icc 1 K, (-1 : ℂ) ^ (m - 1) * (m : ℂ) ^ (-z) := by
    intro K
    induction K with
    | zero => simp
    | succ K ih =>
      rw [dqptAltPartialSum_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ K + 1),
        Nat.add_sub_cancel]
      have hcast : (((K : ℝ) + 1 : ℝ) : ℂ) = ((K + 1 : ℕ) : ℂ) := by push_cast; ring
      rw [dqptRp, hcast]
  have hlhs : (∑ d ∈ Finset.Icc (D + 1) Y,
        (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-z) * dqptAltPartialSum z (Y / d)) =
      ∑ p ∈ (Finset.Icc (D + 1) Y).sigma (fun d => Finset.Icc 1 (Y / d)),
        ((ArithmeticFunction.moebius p.1 : ℂ) * (p.1 : ℂ) ^ (-z)) *
          ((-1 : ℂ) ^ (p.2 - 1) * (p.2 : ℂ) ^ (-z)) := by
    simp_rw [halt]
    rw [Finset.sum_sigma]
    exact Finset.sum_congr rfl fun d _ => Finset.mul_sum _ _ _
  have hrhs : (∑ m ∈ Finset.Icc 1 (Y / (D + 1)),
        (-1 : ℂ) ^ (m - 1) * (m : ℂ) ^ (-z) *
          ∑ d ∈ Finset.Ioc D (Y / m), (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-z)) =
      ∑ q ∈ (Finset.Icc 1 (Y / (D + 1))).sigma (fun m => Finset.Ioc D (Y / m)),
        ((-1 : ℂ) ^ (q.1 - 1) * (q.1 : ℂ) ^ (-z)) *
          ((ArithmeticFunction.moebius q.2 : ℂ) * (q.2 : ℂ) ^ (-z)) := by
    rw [Finset.sum_sigma]
    exact Finset.sum_congr rfl fun m _ => Finset.mul_sum _ _ _
  rw [hlhs, hrhs]
  refine Finset.sum_bij (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_ ?_
  · rintro ⟨d, m⟩ hp
    obtain ⟨hd, hm⟩ := Finset.mem_sigma.mp hp
    obtain ⟨hd_lo, _⟩ := Finset.mem_Icc.mp hd
    obtain ⟨hm1, hm_hi⟩ := Finset.mem_Icc.mp hm
    change D + 1 ≤ d at hd_lo
    change 1 ≤ m at hm1
    change m ≤ Y / d at hm_hi
    have hdm : m * d ≤ Y := (Nat.le_div_iff_mul_le (by omega)).mp hm_hi
    have hm_top : m ≤ Y / (D + 1) :=
      (Nat.le_div_iff_mul_le (by omega)).mpr ((Nat.mul_le_mul_left m hd_lo).trans hdm)
    have hd_top : d ≤ Y / m := (Nat.le_div_iff_mul_le hm1).mpr (by rwa [mul_comm])
    exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hm1, hm_top⟩,
      Finset.mem_Ioc.mpr ⟨show D < d from by omega, hd_top⟩⟩
  · rintro ⟨d₁, m₁⟩ _ ⟨d₂, m₂⟩ _ heq
    injection heq with hm_eq hd_eq
    subst hm_eq; subst hd_eq; rfl
  · rintro ⟨m, d⟩ hq
    obtain ⟨hm, hd⟩ := Finset.mem_sigma.mp hq
    obtain ⟨hm1, _⟩ := Finset.mem_Icc.mp hm
    obtain ⟨hd_lo, hd_hi⟩ := Finset.mem_Ioc.mp hd
    change 1 ≤ m at hm1
    change D < d at hd_lo
    change d ≤ Y / m at hd_hi
    have hdm : d * m ≤ Y := (Nat.le_div_iff_mul_le hm1).mp hd_hi
    have hdY : d ≤ Y := by nlinarith
    have hm_div : m ≤ Y / d := (Nat.le_div_iff_mul_le (by omega)).mpr (by rwa [mul_comm])
    exact ⟨⟨d, m⟩, Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨show D + 1 ≤ d from by omega, hdY⟩,
      Finset.mem_Icc.mpr ⟨hm1, hm_div⟩⟩, rfl⟩
  · rintro ⟨d, m⟩ _
    exact mul_comm _ _

/-- **Exact Vaughan Type-I + Type-II decomposition on `(D, Y]` (`U, V ≤ D`):** directly applying
`BezoutValuationIncidence.moebius_vaughan_apply_of_gt` splits the high-divisor Möbius–eta sum into
`vaughanHighTypeI + vaughanHighTypeII`. -/
theorem highDivisorMoebiusEta_eq_vaughanTypeI_add_typeII {U V D : ℕ} (hU : U ≤ D) (hV : V ≤ D)
    (Y : ℕ) (z : ℂ) :
    (∑ d ∈ Finset.Icc (D + 1) Y,
        (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-z) * dqptAltPartialSum z (Y / d)) =
      vaughanHighTypeI U V D z Y + vaughanHighTypeII U V D z Y := by
  unfold vaughanHighTypeI vaughanHighTypeII
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨hd_lo, _⟩ := Finset.mem_Icc.mp hd
  have hv := GaloisForLFunctions.BezoutValuationIncidence.moebius_vaughan_apply_of_gt
    (U := U) (V := V) (n := d) (by omega) (by omega)
  have hm_cast : (ArithmeticFunction.moebius d : ℂ) =
      (((ArithmeticFunction.moebius : ArithmeticFunction ℝ) d : ℝ) : ℂ) := by
    rw [ArithmeticFunction.intCoe_apply]
    exact (Complex.ofReal_intCast (ArithmeticFunction.moebius d)).symm
  rw [hm_cast, hv]
  push_cast
  ring

/-- **Forced multi-stride Vaughan Type-I or Type-II signal at any `ζ(z) = 0` (`∀ Im z ∈ ℝ`):**
at any hypothetical zero `ζ(z) = 0` (`0 < Re z < 1`), `multiStrideEuler (List.range' 1 D) M` forces
at least one of `vaughanHighTypeI U V D z` or `vaughanHighTypeII U V D z` (`U, V ≤ D`) to have
norm at least `(‖1 - 2^{1 - z}‖ - 3 D / 2^{M / 2}) / 2`. -/
theorem norm_multiStrideEuler_vaughan_typeI_or_typeII_ge_of_zeta_eq_zero
    {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re < 1) (hzz : riemannZeta z = 0)
    {U V D M X₀ : ℕ} (hD : 1 ≤ D) (hU : U ≤ D) (hV : V ≤ D)
    (hM10 : 10 ≤ M) (him : |z.im| ≤ (M : ℝ)) (hX₀ : 2 * D * M ≤ X₀) :
    (‖1 - (2 : ℂ) ^ (1 - z)‖ - 3 * (D : ℝ) / (2 : ℝ) ^ (M / 2)) / 2 ≤
      max
        ‖multiStrideEuler (List.range' 1 D) M (vaughanHighTypeI U V D z) X₀‖
        ‖multiStrideEuler (List.range' 1 D) M (vaughanHighTypeII U V D z) X₀‖ := by
  have hhigh := norm_multiStrideEuler_moebius_highDivisors_ge_of_zeta_eq_zero
    hz0 hz1 hzz hD hM10 him hX₀
  have hfun : (fun Y => ∑ d ∈ Finset.Icc (D + 1) Y,
        (ArithmeticFunction.moebius d : ℂ) * (d : ℂ) ^ (-z) * dqptAltPartialSum z (Y / d)) =
      fun Y => vaughanHighTypeI U V D z Y + vaughanHighTypeII U V D z Y :=
    funext fun Y => highDivisorMoebiusEta_eq_vaughanTypeI_add_typeII hU hV Y z
  rw [hfun, multiStrideEuler_add] at hhigh
  have htri := norm_add_le
    (multiStrideEuler (List.range' 1 D) M (vaughanHighTypeI U V D z) X₀)
    (multiStrideEuler (List.range' 1 D) M (vaughanHighTypeII U V D z) X₀)
  have hm1 := le_max_left
    ‖multiStrideEuler (List.range' 1 D) M (vaughanHighTypeI U V D z) X₀‖
    ‖multiStrideEuler (List.range' 1 D) M (vaughanHighTypeII U V D z) X₀‖
  have hm2 := le_max_right
    ‖multiStrideEuler (List.range' 1 D) M (vaughanHighTypeI U V D z) X₀‖
    ‖multiStrideEuler (List.range' 1 D) M (vaughanHighTypeII U V D z) X₀‖
  linarith

private lemma sum_Icc_rpow_sub_one_le {α : ℝ} (hα : 0 < α) {N : ℕ} (hN : 1 ≤ N) :
    (∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ (α - 1)) ≤ (1 + 1 / α) * (N : ℝ) ^ α := by
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN_ge1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  rcases le_or_gt 1 α with hα1 | hα1
  · calc (∑ k ∈ Finset.Icc 1 N, (k : ℝ) ^ (α - 1))
        ≤ ∑ _k ∈ Finset.Icc 1 N, (N : ℝ) ^ (α - 1) := by
          refine Finset.sum_le_sum fun k hk => ?_
          obtain ⟨_, hkN⟩ := Finset.mem_Icc.mp hk
          exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hkN) (by linarith)
      _ = (N : ℝ) ^ α := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul,
            mul_comm, ← Real.rpow_add_one hN_pos.ne']
          congr 1; ring
      _ ≤ (1 + 1 / α) * (N : ℝ) ^ α := by
          have hpos : 0 < (1 / α) * (N : ℝ) ^ α := by positivity
          linarith
  · have hsplit : Finset.Icc 1 N = insert 1 (Finset.Icc 2 N) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; omega
    have hnot : (1 : ℕ) ∉ Finset.Icc 2 N := by simp
    rw [hsplit, Finset.sum_insert hnot, Nat.cast_one, Real.one_rpow]
    have hstep : ∀ k ∈ Finset.Icc 2 N,
        (k : ℝ) ^ (α - 1) ≤ (1 / α) * ((k : ℝ) ^ α - ((k - 1 : ℕ) : ℝ) ^ α) := by
      intro k hk
      obtain ⟨hk2, _⟩ := Finset.mem_Icc.mp hk
      have hk_prev_pos : (0 : ℝ) < ((k - 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < k - 1)
      have hk_lt : ((k - 1 : ℕ) : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : k - 1 < k)
      have hdiff : ((k : ℝ) - ((k - 1 : ℕ) : ℝ)) = 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]; ring
      have hcont : ContinuousOn (fun x : ℝ => x ^ α) (Set.Icc ((k - 1 : ℕ) : ℝ) (k : ℝ)) :=
        ContinuousOn.rpow_const continuousOn_id fun x hx =>
          Or.inl (lt_of_lt_of_le hk_prev_pos hx.1).ne'
      have hder : ∀ x ∈ Set.Ioo ((k - 1 : ℕ) : ℝ) (k : ℝ),
          HasDerivAt (fun y : ℝ => y ^ α) (α * x ^ (α - 1)) x := fun x hx => by
        simpa using Real.hasDerivAt_rpow_const (p := α) (Or.inl (lt_trans hk_prev_pos hx.1).ne')
      obtain ⟨c, ⟨hc_lo, hc_hi⟩, hslope⟩ := exists_hasDerivAt_eq_slope (fun y : ℝ => y ^ α)
        (fun x => α * x ^ (α - 1)) hk_lt hcont hder
      rw [hdiff, div_one] at hslope
      have hc_pos : 0 < c := lt_trans hk_prev_pos hc_lo
      have hmono : (k : ℝ) ^ (α - 1) ≤ c ^ (α - 1) :=
        Real.rpow_le_rpow_of_nonpos hc_pos hc_hi.le (by linarith)
      rw [← hslope, ← mul_assoc, one_div_mul_cancel hα.ne', one_mul]
      exact hmono
    have htel : (∑ k ∈ Finset.Icc 2 N, (1 / α) * ((k : ℝ) ^ α - ((k - 1 : ℕ) : ℝ) ^ α)) ≤
        (1 / α) * (N : ℝ) ^ α := by
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have hsum_tel : ∀ M : ℕ, 1 ≤ M →
          (∑ k ∈ Finset.Icc 2 M, ((k : ℝ) ^ α - ((k - 1 : ℕ) : ℝ) ^ α)) =
            (M : ℝ) ^ α - 1 := by
        intro M hM
        induction M with
        | zero => omega
        | succ M ih =>
          rcases eq_or_lt_of_le hM with h0 | hlt
          · have hM0 : M = 0 := by omega
            subst hM0
            simp
          · rw [Finset.sum_Icc_succ_top (by omega : 2 ≤ M + 1), ih (by omega), Nat.add_sub_cancel]
            ring
      rw [hsum_tel N hN]
      linarith
    have h1_le : (1 : ℝ) ≤ (N : ℝ) ^ α := Real.one_le_rpow hN_ge1 hα.le
    have hsum_le := (Finset.sum_le_sum hstep).trans htel
    linarith

private lemma exists_dirichletPoly_subpower_of_coeffPartial_le (c : ℕ → ℂ) {CM θ : ℝ}
    (hCM : 0 ≤ CM) (hθ : 0 < θ)
    (hpart : ∀ k : ℕ, ‖_root_.RHTower.coeffPartial (fun i => c (i + 1)) k‖ ≤
      CM * ((k : ℝ) + 1) ^ θ)
    {w : ℂ} (hw0 : 0 < w.re) (hw_lt : w.re < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      ‖∑ d ∈ Finset.Icc 1 N, c d * (d : ℂ) ^ (-w)‖ ≤ C * (N : ℝ) ^ (θ - w.re) := by
  have hα : 0 < θ - w.re := by linarith
  refine ⟨CM * (2 : ℝ) ^ θ + CM * (2 : ℝ) ^ θ * ‖w‖ * (1 + 1 / (θ - w.re)), by positivity,
    fun N hN => ?_⟩
  have hN_pos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hN1 : (N : ℝ) + 1 ≤ 2 * (N : ℝ) := by
    have : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    linarith
  have heq : (∑ d ∈ Finset.Icc 1 N, c d * (d : ℂ) ^ (-w)) =
      ∑ i ∈ Finset.range N, (((i : ℝ) + 1 : ℝ) : ℂ) ^ (-w) * c (i + 1) := by
    rw [← _root_.RHTower.sum_range_succ_eq_sum_Icc (fun n => c n * (n : ℂ) ^ (-w)) N]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hcast : (((i + 1 : ℕ) : ℂ)) = (((i : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast, mul_comm]
  rw [heq, _root_.RHTower.sum_eq_abelPartial]
  have hbnd_top : ‖(((N : ℝ)) : ℂ) ^ (-w) * _root_.RHTower.coeffPartial (fun i => c (i + 1)) N‖ ≤
      CM * (2 : ℝ) ^ θ * (N : ℝ) ^ (θ - w.re) := by
    rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos hN_pos, Complex.neg_re]
    have hpN : ‖_root_.RHTower.coeffPartial (fun i => c (i + 1)) N‖ ≤
        CM * (2 : ℝ) ^ θ * (N : ℝ) ^ θ := by
      calc ‖_root_.RHTower.coeffPartial (fun i => c (i + 1)) N‖
          ≤ CM * ((N : ℝ) + 1) ^ θ := hpart N
        _ ≤ CM * (2 * (N : ℝ)) ^ θ :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hN1 hθ.le) hCM
        _ = CM * (2 : ℝ) ^ θ * (N : ℝ) ^ θ := by
            rw [Real.mul_rpow zero_le_two hN_pos.le]; ring
    calc (N : ℝ) ^ (-w.re) * ‖_root_.RHTower.coeffPartial (fun i => c (i + 1)) N‖
        ≤ (N : ℝ) ^ (-w.re) * (CM * (2 : ℝ) ^ θ * (N : ℝ) ^ θ) :=
          mul_le_mul_of_nonneg_left hpN (Real.rpow_nonneg hN_pos.le _)
      _ = CM * (2 : ℝ) ^ θ * ((N : ℝ) ^ (-w.re) * (N : ℝ) ^ θ) := by ring
      _ = CM * (2 : ℝ) ^ θ * (N : ℝ) ^ (θ - w.re) := by
          rw [← Real.rpow_add hN_pos]; congr 2; ring
  have hbnd_sum : ‖∑ k ∈ Finset.range (N - 1),
        _root_.RHTower.coeffPartial (fun i => c (i + 1)) (k + 1) *
          (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-w) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-w))‖ ≤
      CM * (2 : ℝ) ^ θ * ‖w‖ * (1 + 1 / (θ - w.re)) * (N : ℝ) ^ (θ - w.re) := by
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ k ∈ Finset.range (N - 1),
        ‖_root_.RHTower.coeffPartial (fun i => c (i + 1)) (k + 1) *
            (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-w) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-w))‖ ≤
          CM * (2 : ℝ) ^ θ * ‖w‖ * (((k + 1 : ℕ) : ℝ)) ^ (θ - w.re - 1) := by
      intro k _
      have hx : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      have hstep := _root_.RHTower.norm_cpow_shift_sub_le_of_nonneg
        (x := (k : ℝ) + 1) (b := 1) hx zero_le_one hw0
      have hcast2 : (((k : ℝ) + 1 + 1 : ℝ)) = ((k : ℝ) + 2) := by ring
      rw [hcast2, mul_one] at hstep
      have hsub : ‖((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-w) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-w)‖ ≤
          ‖w‖ * ((k : ℝ) + 1) ^ (-w.re - 1) := by
        rw [← norm_neg, show -(((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-w) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-w)) =
          ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-w) - ((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-w) by ring]
        exact hstep
      have hpk : ‖_root_.RHTower.coeffPartial (fun i => c (i + 1)) (k + 1)‖ ≤
          CM * (2 : ℝ) ^ θ * ((k : ℝ) + 1) ^ θ := by
        have hk2 : (((k + 1 : ℕ) : ℝ) + 1) ≤ 2 * ((k : ℝ) + 1) := by push_cast; linarith
        calc ‖_root_.RHTower.coeffPartial (fun i => c (i + 1)) (k + 1)‖
            ≤ CM * (((k + 1 : ℕ) : ℝ) + 1) ^ θ := hpart (k + 1)
          _ ≤ CM * (2 * ((k : ℝ) + 1)) ^ θ :=
              mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hk2 hθ.le) hCM
          _ = CM * (2 : ℝ) ^ θ * ((k : ℝ) + 1) ^ θ := by
              rw [Real.mul_rpow zero_le_two hx.le]; ring
      rw [norm_mul]
      calc ‖_root_.RHTower.coeffPartial (fun i => c (i + 1)) (k + 1)‖ *
            ‖((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-w) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-w)‖
          ≤ (CM * (2 : ℝ) ^ θ * ((k : ℝ) + 1) ^ θ) * (‖w‖ * ((k : ℝ) + 1) ^ (-w.re - 1)) :=
            mul_le_mul hpk hsub (norm_nonneg _) (by positivity)
        _ = CM * (2 : ℝ) ^ θ * ‖w‖ * (((k : ℝ) + 1) ^ θ * ((k : ℝ) + 1) ^ (-w.re - 1)) := by ring
        _ = CM * (2 : ℝ) ^ θ * ‖w‖ * (((k + 1 : ℕ) : ℝ)) ^ (θ - w.re - 1) := by
            rw [← Real.rpow_add hx]
            have hc1 : ((k : ℝ) + 1) = ((k + 1 : ℕ) : ℝ) := by push_cast; ring
            rw [hc1]; congr 2; ring
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.mul_sum]
    have hbij : (∑ k ∈ Finset.range (N - 1), (((k + 1 : ℕ) : ℝ)) ^ (θ - w.re - 1)) ≤
        ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (θ - w.re - 1) := by
      have heq_sum := _root_.RHTower.sum_range_succ_eq_sum_Icc
        (fun m : ℕ => (m : ℝ) ^ (θ - w.re - 1)) (N - 1)
      rw [heq_sum]
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.Icc_subset_Icc_right (Nat.sub_le N 1)) fun _ _ _ => by positivity
    calc CM * (2 : ℝ) ^ θ * ‖w‖ *
          (∑ k ∈ Finset.range (N - 1), (((k + 1 : ℕ) : ℝ)) ^ (θ - w.re - 1))
        ≤ CM * (2 : ℝ) ^ θ * ‖w‖ * (∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (θ - w.re - 1)) :=
          mul_le_mul_of_nonneg_left hbij (by positivity)
      _ ≤ CM * (2 : ℝ) ^ θ * ‖w‖ * ((1 + 1 / (θ - w.re)) * (N : ℝ) ^ (θ - w.re)) :=
          mul_le_mul_of_nonneg_left (sum_Icc_rpow_sub_one_le hα hN) (by positivity)
      _ = CM * (2 : ℝ) ^ θ * ‖w‖ * (1 + 1 / (θ - w.re)) * (N : ℝ) ^ (θ - w.re) := by ring
  have htri := norm_add_le
    ((((N : ℝ)) : ℂ) ^ (-w) * _root_.RHTower.coeffPartial (fun i => c (i + 1)) N)
    (∑ k ∈ Finset.range (N - 1),
      _root_.RHTower.coeffPartial (fun i => c (i + 1)) (k + 1) *
        (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-w) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-w)))
  calc ‖(((N : ℝ)) : ℂ) ^ (-w) * _root_.RHTower.coeffPartial (fun i => c (i + 1)) N +
          ∑ k ∈ Finset.range (N - 1),
            _root_.RHTower.coeffPartial (fun i => c (i + 1)) (k + 1) *
              (((((k : ℝ) + 1 : ℝ)) : ℂ) ^ (-w) - ((((k : ℝ) + 2 : ℝ)) : ℂ) ^ (-w))‖
      ≤ CM * (2 : ℝ) ^ θ * (N : ℝ) ^ (θ - w.re) +
          CM * (2 : ℝ) ^ θ * ‖w‖ * (1 + 1 / (θ - w.re)) * (N : ℝ) ^ (θ - w.re) :=
        htri.trans (add_le_add hbnd_top hbnd_sum)
    _ = (CM * (2 : ℝ) ^ θ + CM * (2 : ℝ) ^ θ * ‖w‖ * (1 + 1 / (θ - w.re))) *
          (N : ℝ) ^ (θ - w.re) := by ring

private lemma exists_moebius_coeffPartial_le_of_zeroFree
    {Θ : ℝ} (hΘ : (1 : ℝ) / 2 ≤ Θ) (hΘ1 : Θ ≤ 1)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ CM : ℝ, 0 ≤ CM ∧ ∀ k : ℕ,
      ‖_root_.RHTower.coeffPartial (fun i => (ArithmeticFunction.moebius (i + 1) : ℂ)) k‖ ≤
        CM * ((k : ℝ) + 1) ^ (Θ + ε) := by
  obtain ⟨CM, hCM0, hM⟩ := _root_.RHTower.mobiusMertens_subpower_of_zeroFree hΘ hΘ1 hzf ε hε
  refine ⟨CM, hCM0, fun k => ?_⟩
  have hfun : (fun i : ℕ => (ArithmeticFunction.moebius (i + 1) : ℂ)) =
      fun i : ℕ => ((_root_.RHTower.moebiusR (i + 1) : ℝ) : ℂ) := by
    funext i
    unfold _root_.RHTower.moebiusR
    exact (Complex.ofReal_intCast (ArithmeticFunction.moebius (i + 1))).symm
  rw [hfun, _root_.RHTower.coeffPartial_ofReal, Complex.norm_real, Real.norm_eq_abs,
    ← _root_.RHTower.norm_mobiusMertensPartialSum_eq_abs_sourcePartialSum_moebiusR]
  exact hM k

private lemma exists_liouville_coeffPartial_le_of_zeroFree
    {Θ : ℝ} (hΘ : (1 : ℝ) / 2 ≤ Θ) (hΘ1 : Θ ≤ 1)
    (hzf : ∀ z : ℂ, Θ < z.re → riemannZeta z ≠ 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ CL : ℝ, 0 ≤ CL ∧ ∀ k : ℕ,
      ‖_root_.RHTower.coeffPartial (fun i => _root_.RHTower.liouvilleC (i + 1)) k‖ ≤
        CL * ((k : ℝ) + 1) ^ (Θ + ε) := by
  obtain ⟨CM, hCM0, hCM⟩ := _root_.RHTower.mobiusMertens_subpower_of_zeroFree hΘ hΘ1 hzf ε hε
  set p : ℝ := Θ + ε
  have hp_pos : 0 < p := by linarith only [hΘ, hε]
  have hZs : Summable fun j : ℕ => 1 / (j : ℝ) ^ (2 * p) :=
    Real.summable_one_div_nat_rpow.2 (by linarith only [hΘ, hε])
  set Z : ℝ := ∑' j : ℕ, 1 / (j : ℝ) ^ (2 * p)
  have hZ0 : 0 ≤ Z := tsum_nonneg fun _ => by positivity
  refine ⟨CM * (2 : ℝ) ^ p * Z, by positivity, fun k => ?_⟩
  have hfun : (fun i : ℕ => _root_.RHTower.liouvilleC (i + 1)) =
      fun i : ℕ => ((_root_.RHTower.liouvilleR (i + 1) : ℝ) : ℂ) := by
    funext i
    rw [_root_.RHTower.liouvilleC_apply]
    unfold _root_.RHTower.liouvilleR
    exact (Complex.ofReal_intCast (ArithmeticFunction.liouville (i + 1))).symm
  rw [hfun, _root_.RHTower.coeffPartial_ofReal, Complex.norm_real, Real.norm_eq_abs]
  rcases Nat.eq_zero_or_pos k with rfl | hkpos
  · simp [_root_.RHTower.sourcePartialSum]
    positivity
  · rw [_root_.RHTower.sourcePartialSum_liouvilleR_eq, _root_.RHTower.floorTransform]
    have hpt : ∀ d ∈ Finset.Icc 1 k,
        |_root_.RHTower.squareIndicatorR d *
            _root_.RHTower.sourcePartialSum _root_.RHTower.moebiusR (k / d)| ≤
          _root_.RHTower.squareIndicatorR d *
            (CM * (2 * ((k : ℝ) + 1)) ^ p * (1 / (d : ℝ) ^ p)) := by
      intro d hd
      obtain ⟨hd1, hdk⟩ := Finset.mem_Icc.1 hd
      have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
      have hsq : 0 ≤ _root_.RHTower.squareIndicatorR d := by
        unfold _root_.RHTower.squareIndicatorR; split_ifs <;> norm_num
      rw [abs_mul, abs_of_nonneg hsq]
      refine mul_le_mul_of_nonneg_left ?_ hsq
      rw [← _root_.RHTower.norm_mobiusMertensPartialSum_eq_abs_sourcePartialSum_moebiusR]
      refine (hCM (k / d)).trans ?_
      have hfl : ((k / d : ℕ) : ℝ) + 1 ≤ 2 * ((k : ℝ) + 1) / d := by
        have h1 : ((k / d : ℕ) : ℝ) ≤ (k : ℝ) / d := Nat.cast_div_le
        have h2 : (1 : ℝ) ≤ ((k : ℝ) + 1) / d := by
          rw [le_div_iff₀ hd0]
          have hd_le_k : (d : ℝ) ≤ k := by exact_mod_cast hdk
          linarith only [hd_le_k]
        have h3 : (k : ℝ) / d ≤ ((k : ℝ) + 1) / d :=
          div_le_div_of_nonneg_right (by linarith only []) hd0.le
        rw [mul_div_assoc]
        linarith only [h1, h2, h3]
      calc CM * (((k / d : ℕ) : ℝ) + 1) ^ p
          ≤ CM * (2 * ((k : ℝ) + 1) / d) ^ p :=
            mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) hfl hp_pos.le) hCM0
        _ = CM * (2 * ((k : ℝ) + 1)) ^ p * (1 / (d : ℝ) ^ p) := by
            rw [Real.div_rpow (by positivity) hd0.le]; ring
    refine (Finset.abs_sum_le_sum_abs _ _).trans ((Finset.sum_le_sum hpt).trans ?_)
    have hsum : ∑ i ∈ Finset.Icc 1 k, _root_.RHTower.squareIndicatorR i * (1 / (i : ℝ) ^ p) ≤ Z := by
      have e1 : ∑ i ∈ Finset.Icc 1 k, _root_.RHTower.squareIndicatorR i * (1 / (i : ℝ) ^ p) =
          ∑ i ∈ (Finset.Icc 1 k).filter IsSquare, 1 / (i : ℝ) ^ p := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun i _ => ?_
        unfold _root_.RHTower.squareIndicatorR; split_ifs <;> simp
      rw [e1]
      have hsub : (Finset.Icc 1 k).filter IsSquare ⊆ (Finset.Icc 1 k).image (fun j => j ^ 2) := by
        intro i hi
        obtain ⟨hi1, ⟨j, rfl⟩⟩ := Finset.mem_filter.1 hi
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.1 hi1
        have hj1 : 1 ≤ j := by
          rcases Nat.eq_zero_or_pos j with rfl | hj
          · simp at h1
          · exact hj
        have hj_le : j ≤ k := le_trans (Nat.le_mul_of_pos_left j hj1) h2
        exact Finset.mem_image.2 ⟨j, Finset.mem_Icc.2 ⟨hj1, hj_le⟩, sq j⟩
      refine (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity).trans ?_
      rw [Finset.sum_image fun _ _ _ _ h => Nat.pow_left_injective (by norm_num) h]
      have e2 : ∀ j ∈ Finset.Icc 1 k, 1 / (((j ^ 2 : ℕ) : ℝ)) ^ p = 1 / (j : ℝ) ^ (2 * p) := by
        intro j _
        rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg j)]
        norm_num
      rw [Finset.sum_congr rfl e2]
      exact hZs.sum_le_tsum _ fun _ _ => by positivity
    have e3 : ∑ i ∈ Finset.Icc 1 k, _root_.RHTower.squareIndicatorR i *
          (CM * (2 * ((k : ℝ) + 1)) ^ p * (1 / (i : ℝ) ^ p)) =
        CM * (2 * ((k : ℝ) + 1)) ^ p *
          ∑ i ∈ Finset.Icc 1 k, _root_.RHTower.squareIndicatorR i * (1 / (i : ℝ) ^ p) := by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e3, Real.mul_rpow zero_le_two (by positivity)]
    have hK_nn : 0 ≤ CM * ((2 : ℝ) ^ p * ((k : ℝ) + 1) ^ p) :=
      mul_nonneg hCM0 (mul_nonneg (Real.rpow_nonneg zero_le_two _) (Real.rpow_nonneg (by positivity) _))
    calc CM * ((2 : ℝ) ^ p * ((k : ℝ) + 1) ^ p) *
          ∑ i ∈ Finset.Icc 1 k, _root_.RHTower.squareIndicatorR i * (1 / (i : ℝ) ^ p)
        ≤ CM * ((2 : ℝ) ^ p * ((k : ℝ) + 1) ^ p) * Z :=
          mul_le_mul_of_nonneg_left hsum hK_nn
      _ = (CM * (2 : ℝ) ^ p * Z) * ((k : ℝ) + 1) ^ p := by ring

/-- **Unconditional sublinear `O_{s, ε}(N^{Re s - 3001/24000 + ε})` power cancellation across the
entire remaining strip (`∀ Im s ∈ ℝ`):** at every point `3001/24000 ≤ Re s < 1/2` and every
`ε > 0`, `SubSevenEighthsZeroFreeHalfPlane` bounds both `moebiusPoly N (1 - conj s)` and
`liouvillePoly N (1 - conj s)` by `C · N^{Re s - 3001/24000 + ε}` (`< N^{3/8}` for small `ε`,
saving `> N^{5/8}` over trivial `N`). -/
theorem exists_sublinear_moebius_and_liouville_on_remaining_strip
    {s : ℂ} (hlo : (3001 / 24000 : ℝ) ≤ s.re) (hhi : s.re < 1 / 2) {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 1 ≤ N →
      ‖moebiusPoly N (1 - conj s)‖ ≤ C * (N : ℝ) ^ (s.re - 3001 / 24000 + ε) ∧
      ‖liouvillePoly N (1 - conj s)‖ ≤ C * (N : ℝ) ^ (s.re - 3001 / 24000 + ε) := by
  have hzf : ∀ z : ℂ, (20999 / 24000 : ℝ) < z.re → riemannZeta z ≠ 0 := fun _ hz =>
    GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_seven_eighths_lt_re hz
  obtain ⟨CM, hCM0, hpartM⟩ := exists_moebius_coeffPartial_le_of_zeroFree
    (by norm_num : (1 : ℝ) / 2 ≤ 20999 / 24000) (by norm_num : (20999 / 24000 : ℝ) ≤ 1) hzf hε
  obtain ⟨CL, hCL0, hpartL⟩ := exists_liouville_coeffPartial_le_of_zeroFree
    (by norm_num : (1 : ℝ) / 2 ≤ 20999 / 24000) (by norm_num : (20999 / 24000 : ℝ) ≤ 1) hzf hε
  have hθ_pos : (0 : ℝ) < (20999 / 24000 : ℝ) + ε := by linarith
  have hw_re : (1 - conj s).re = 1 - s.re := by simp
  have hw0 : 0 < (1 - conj s).re := by rw [hw_re]; linarith
  have hw_lt : (1 - conj s).re < (20999 / 24000 : ℝ) + ε := by rw [hw_re]; linarith
  have hexp_eq : ((20999 / 24000 : ℝ) + ε) - (1 - conj s).re = s.re - 3001 / 24000 + ε := by
    rw [hw_re]; ring
  obtain ⟨C₁, hC₁0, hC₁⟩ := exists_dirichletPoly_subpower_of_coeffPartial_le
    (fun n => (ArithmeticFunction.moebius n : ℂ)) hCM0 hθ_pos hpartM hw0 hw_lt
  obtain ⟨C₂, _, hC₂⟩ := exists_dirichletPoly_subpower_of_coeffPartial_le
    (fun n => _root_.RHTower.liouvilleC n) hCL0 hθ_pos hpartL hw0 hw_lt
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁0, fun N hN => ?_⟩
  have hN_nn : 0 ≤ (N : ℝ) ^ (s.re - 3001 / 24000 + ε) :=
    Real.rpow_nonneg (Nat.cast_nonneg N) _
  refine ⟨?_, ?_⟩
  · unfold moebiusPoly
    have h1 := hC₁ N hN
    rw [hexp_eq] at h1
    exact h1.trans (mul_le_mul_of_nonneg_right (le_max_left C₁ C₂) hN_nn)
  · unfold liouvillePoly
    have h2 := hC₂ N hN
    rw [hexp_eq] at h2
    exact h2.trans (mul_le_mul_of_nonneg_right (le_max_right C₁ C₂) hN_nn)

/-! ### 3. Modulus-`q` Periodic Euler–Fourier Acceleration, Dirichlet/Hecke Base Change & Special Locus -/

/-- Truncated Dirichlet character partial sum `∑_{m=1}^K χ(m) m^{-z}`. -/
def charPartialSum {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℂ) (K : ℕ) : ℂ :=
  ∑ m ∈ Finset.Icc 1 K, χ m * (m : ℂ) ^ (-z)

lemma charPartialSum_eq_dirichletPartialSum {q : ℕ} (χ : DirichletCharacter ℂ q) (z : ℂ) (K : ℕ) :
    charPartialSum χ z K =
      GaloisForLFunctions.RHTower.dirichletPartialSum (fun j => χ ((j : ZMod q) + 1)) K z := by
  unfold charPartialSum GaloisForLFunctions.RHTower.dirichletPartialSum
  rw [← _root_.RHTower.sum_range_succ_eq_sum_Icc
    (fun m : ℕ => χ (m : ZMod q) * (m : ℂ) ^ (-z)) K]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hcast : (((j + 1 : ℕ) : ℂ)) = (((j : ℝ) + 1 : ℝ) : ℂ) := by push_cast; ring
  rw [hcast, Nat.cast_add, Nat.cast_one]

lemma tendsto_charPartialSum_LFunction {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) {z : ℂ} (hz : 0 < z.re) :
    Tendsto (fun K : ℕ => charPartialSum χ z K) atTop (𝓝 (χ.LFunction z)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hmaj : Tendsto
      (fun K : ℕ => 2 * (q : ℝ) * (1 + ‖z‖ / z.re) * ((K : ℝ) + 1) ^ (-z.re))
      atTop (𝓝 0) := by
    have hpow : Tendsto (fun K : ℕ => ((K : ℝ) + 1) ^ (-z.re)) atTop (𝓝 0) :=
      (tendsto_rpow_neg_atTop hz).comp
        (tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop)
    simpa only [mul_zero] using hpow.const_mul (2 * (q : ℝ) * (1 + ‖z‖ / z.re))
  refine squeeze_zero (fun _ => norm_nonneg _) (fun K => ?_) hmaj
  rw [norm_sub_rev, charPartialSum_eq_dirichletPartialSum]
  exact _root_.RHTower.norm_LFunction_sub_character_partial_le hχ hz K

/-- Modulus-`q` `M`-th order Euler–Fourier accelerated Dirichlet character partial sum:
`periodicEulerPartialSum χ N M z = (strideMean q 1)^[M] (charPartialSum χ z) N`. -/
def periodicEulerPartialSum {q : ℕ} (χ : DirichletCharacter ℂ q) (N M : ℕ) (z : ℂ) : ℂ :=
  (strideMean q 1)^[M] (charPartialSum χ z) N

lemma periodicEulerPartialSum_zero {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (z : ℂ) :
    periodicEulerPartialSum χ N 0 z = charPartialSum χ z N := rfl

lemma periodicEulerPartialSum_succ {q : ℕ} (χ : DirichletCharacter ℂ q) (N M : ℕ) (z : ℂ) :
    periodicEulerPartialSum χ N (M + 1) z =
      (q : ℂ)⁻¹ * ∑ r ∈ Finset.range q, periodicEulerPartialSum χ (N + r) M z := by
  unfold periodicEulerPartialSum
  rw [Function.iterate_succ_apply', strideMean_apply]
  simp only [mul_one]

theorem iterate_strideMean_charPartialSum_div_eq {q d : ℕ} (hd : 0 < d)
    (χ : DirichletCharacter ℂ q) (M : ℕ) (z : ℂ) :
    (strideMean q d)^[M] (fun Y => charPartialSum χ z (Y / d)) =
      fun X => periodicEulerPartialSum χ (X / d) M z :=
  iterate_strideMean_div_eq q hd M (charPartialSum χ z)

/-- Explicit tapered real weights of `periodicEulerPartialSum` on `[1, N + M(q - 1)]`: identically
`1` on `[1, N]`, decreasing to `0` above `N + M(q - 1)`. -/
def periodicEulerWeight (q : ℕ) : ℕ → ℕ → ℕ → ℝ
  | N, 0, m => if 1 ≤ m ∧ m ≤ N then 1 else 0
  | N, M + 1, m => (q : ℝ)⁻¹ * ∑ r ∈ Finset.range q, periodicEulerWeight q (N + r) M m

private lemma periodicEulerWeight_succ (q N M m : ℕ) :
    periodicEulerWeight q N (M + 1) m =
      (q : ℝ)⁻¹ * ∑ r ∈ Finset.range q, periodicEulerWeight q (N + r) M m := rfl

lemma periodicEulerWeight_nonneg (q N M m : ℕ) : 0 ≤ periodicEulerWeight q N M m := by
  induction M generalizing N with
  | zero =>
    unfold periodicEulerWeight
    split_ifs <;> norm_num
  | succ M ih =>
    rw [periodicEulerWeight_succ]
    exact mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg q))
      (Finset.sum_nonneg fun r _ => ih (N + r))

lemma periodicEulerWeight_le_one {q : ℕ} (hq : 1 ≤ q) (N M m : ℕ) :
    periodicEulerWeight q N M m ≤ 1 := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  induction M generalizing N with
  | zero =>
    unfold periodicEulerWeight
    split_ifs <;> norm_num
  | succ M ih =>
    rw [periodicEulerWeight_succ]
    calc (q : ℝ)⁻¹ * ∑ r ∈ Finset.range q, periodicEulerWeight q (N + r) M m
        ≤ (q : ℝ)⁻¹ * ∑ _r ∈ Finset.range q, (1 : ℝ) :=
          mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r _ => ih (N + r))
            (inv_nonneg.mpr hq_pos.le)
      _ = 1 := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
            inv_mul_cancel₀ hq_pos.ne']

lemma periodicEulerWeight_eq_one_of_le {q : ℕ} (hq : 1 ≤ q) {N M m : ℕ}
    (hm1 : 1 ≤ m) (hmN : m ≤ N) :
    periodicEulerWeight q N M m = 1 := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  induction M generalizing N with
  | zero =>
    unfold periodicEulerWeight
    exact if_pos ⟨hm1, hmN⟩
  | succ M ih =>
    rw [periodicEulerWeight_succ, Finset.sum_congr rfl fun r _ => ih (by omega : m ≤ N + r),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, inv_mul_cancel₀ hq_pos.ne']

lemma periodicEulerWeight_eq_zero_of_gt {q : ℕ} (hq : 1 ≤ q) {N M m : ℕ}
    (hgt : N + M * (q - 1) < m) :
    periodicEulerWeight q N M m = 0 := by
  induction M generalizing N with
  | zero =>
    unfold periodicEulerWeight
    rw [if_neg]
    rintro ⟨_, hmN⟩
    simp at hgt
    omega
  | succ M ih =>
    rw [periodicEulerWeight_succ]
    have hsum : (∑ r ∈ Finset.range q, periodicEulerWeight q (N + r) M m) = 0 := by
      refine Finset.sum_eq_zero fun r hr => ih ?_
      have hr_lt : r < q := Finset.mem_range.mp hr
      have hr_le : r ≤ q - 1 := by omega
      have hstep : (N + r) + M * (q - 1) ≤ N + (M + 1) * (q - 1) := by
        rw [Nat.succ_mul]
        omega
      omega
    rw [hsum, mul_zero]

/-- Explicit finite Dirichlet-polynomial expansion of `periodicEulerPartialSum` on `[1, N + M(q - 1)]`. -/
theorem periodicEulerPartialSum_eq_sum_weights {q : ℕ} (hq : 1 ≤ q)
    (χ : DirichletCharacter ℂ q) (N M : ℕ) (z : ℂ) :
    periodicEulerPartialSum χ N M z =
      ∑ m ∈ Finset.Icc 1 (N + M * (q - 1)),
        (periodicEulerWeight q N M m : ℂ) * χ m * (m : ℂ) ^ (-z) := by
  induction M generalizing N with
  | zero =>
    rw [periodicEulerPartialSum_zero, zero_mul, add_zero]
    unfold charPartialSum
    refine Finset.sum_congr rfl fun m hm => ?_
    obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
    rw [periodicEulerWeight_eq_one_of_le hq hm1 hmN, Complex.ofReal_one, one_mul]
  | succ M ih =>
    rw [periodicEulerPartialSum_succ]
    have hterm : ∀ r ∈ Finset.range q,
        periodicEulerPartialSum χ (N + r) M z =
          ∑ m ∈ Finset.Icc 1 (N + (M + 1) * (q - 1)),
            (periodicEulerWeight q (N + r) M m : ℂ) * χ m * (m : ℂ) ^ (-z) := by
      intro r hr
      rw [ih (N + r)]
      have hr_lt : r < q := Finset.mem_range.mp hr
      have hsub : N + r + M * (q - 1) ≤ N + (M + 1) * (q - 1) := by
        rw [Nat.succ_mul]; omega
      refine Finset.sum_subset (Finset.Icc_subset_Icc_right hsub) fun m hm hnot => ?_
      rw [Finset.mem_Icc] at hm hnot
      rw [periodicEulerWeight_eq_zero_of_gt hq (by omega : N + r + M * (q - 1) < m)]
      simp
    rw [Finset.sum_congr rfl hterm, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [periodicEulerWeight_succ]
    push_cast
    simp only [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring

/-- Explicit `L(z, χ)`-free remainder bound for `periodicEulerPartialSum χ N M z`. -/
def periodicEulerTailBound (q N M : ℕ) (z : ℂ) : ℝ :=
  2 * (q : ℝ) * ((q - 1 : ℕ) : ℝ) * (((q - 1 : ℕ) : ℝ) / 2) ^ (M + 1) *
    (∏ m ∈ Finset.range (M + 1), ‖z + (m : ℂ)‖) * ((N : ℝ) + 1) ^ (-z.re - (M : ℝ))

private def fourierRoot (q a : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (q : ℂ))

private lemma norm_fourierRoot (q a : ℕ) : ‖fourierRoot q a‖ = 1 := by
  unfold fourierRoot
  have hre : (2 * Real.pi * Complex.I * (a : ℂ) / (q : ℂ)).re = 0 := by
    have heq : 2 * Real.pi * Complex.I * (a : ℂ) / (q : ℂ) =
        (((2 * Real.pi * (a : ℝ) / (q : ℝ) : ℝ) : ℂ) * Complex.I) := by
      push_cast; ring
    rw [heq, Complex.mul_I_re, Complex.ofReal_im, neg_zero]
  rw [Complex.norm_exp, hre, Real.exp_zero]

private lemma fourierRoot_pow_period {q : ℕ} (hq : 1 ≤ q) (a : ℕ) :
    (fourierRoot q a) ^ q = 1 := by
  unfold fourierRoot
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [← Complex.exp_nat_mul]
  have hexp : (q : ℂ) * (2 * Real.pi * Complex.I * (a : ℂ) / (q : ℂ)) =
      (a : ℂ) * (2 * Real.pi * Complex.I) := by
    field_simp [hq0]
  rw [hexp, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]

private lemma fourierRoot_ne_one {q a : ℕ} (ha1 : 1 ≤ a) (haq : a < q) :
    fourierRoot q a ≠ 1 := by
  intro h
  rw [fourierRoot, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
    mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hmul : (2 * Real.pi * Complex.I) * ((a : ℂ) / (q : ℂ)) =
      (2 * Real.pi * Complex.I) * (n : ℂ) := by
    calc (2 * Real.pi * Complex.I) * ((a : ℂ) / (q : ℂ))
        = 2 * Real.pi * Complex.I * (a : ℂ) / (q : ℂ) := (mul_div_assoc _ _ _).symm
      _ = (n : ℂ) * (2 * Real.pi * Complex.I) := hn
      _ = (2 * Real.pi * Complex.I) * (n : ℂ) := mul_comm _ _
  have hdiv := mul_left_cancel₀ hpi hmul
  have ha_eq : (a : ℂ) = (n : ℂ) * (q : ℂ) := (div_eq_iff hq0).mp hdiv
  have ha_real : (a : ℝ) = (n : ℝ) * (q : ℝ) := by
    simpa using congrArg Complex.re ha_eq
  have ha_int : (a : ℤ) = n * (q : ℤ) := by exact_mod_cast ha_real
  rcases le_or_gt n 0 with hn0 | hn1
  · have hle : n * (q : ℤ) ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hn0 (by omega)
    omega
  · have hge : (q : ℤ) ≤ n * (q : ℤ) := by nlinarith
    omega

private def charFourierCoeff {q : ℕ} (χ : DirichletCharacter ℂ q) (a : ℕ) : ℂ :=
  (q : ℂ)⁻¹ * ∑ u ∈ Finset.range q,
    χ u * Complex.exp (-2 * Real.pi * Complex.I * (a : ℂ) * (u : ℂ) / (q : ℂ))

private lemma norm_charFourierCoeff_le_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (a : ℕ) : ‖charFourierCoeff χ a‖ ≤ 1 := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (NeZero.pos q)
  unfold charFourierCoeff
  rw [norm_mul, norm_inv, Complex.norm_natCast]
  calc (q : ℝ)⁻¹ * ‖∑ u ∈ Finset.range q,
          χ u * Complex.exp (-2 * Real.pi * Complex.I * (a : ℂ) * (u : ℂ) / (q : ℂ))‖
      ≤ (q : ℝ)⁻¹ * ∑ u ∈ Finset.range q,
          ‖χ u * Complex.exp (-2 * Real.pi * Complex.I * (a : ℂ) * (u : ℂ) / (q : ℂ))‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hq_pos.le)
    _ ≤ (q : ℝ)⁻¹ * ∑ _u ∈ Finset.range q, (1 : ℝ) := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun u _ => ?_)
          (inv_nonneg.mpr hq_pos.le)
        rw [norm_mul]
        have hexp_re : (-2 * Real.pi * Complex.I * (a : ℂ) * (u : ℂ) / (q : ℂ)).re = 0 := by
          have heq : -2 * Real.pi * Complex.I * (a : ℂ) * (u : ℂ) / (q : ℂ) =
              (((-2 * Real.pi * (a : ℝ) * (u : ℝ) / (q : ℝ) : ℝ) : ℂ) * Complex.I) := by
            push_cast; ring
          rw [heq, Complex.mul_I_re, Complex.ofReal_im, neg_zero]
        rw [Complex.norm_exp, hexp_re, Real.exp_zero, mul_one]
        exact χ.norm_le_one _
    _ = 1 := by
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
          inv_mul_cancel₀ hq_pos.ne']

private lemma charFourierCoeff_zero_eq_zero {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hχ : χ ≠ 1) : charFourierCoeff χ 0 = 0 := by
  unfold charFourierCoeff
  simp only [Nat.cast_zero, mul_zero, zero_mul, zero_div, Complex.exp_zero, mul_one]
  have hfin (r : Fin q) : ZMod.finEquiv q r = (r.val : ZMod q) := by
    cases q with
    | zero => exact (NeZero.ne 0 rfl).elim
    | succ q' =>
      apply ZMod.val_injective
      change r.val = r.val % (q' + 1)
      rw [Nat.mod_eq_of_lt r.isLt]
  have hsum : (∑ x : ZMod q, χ x) = ∑ u ∈ Finset.range q, χ (u : ZMod q) := by
    calc (∑ x : ZMod q, χ x)
        = ∑ r : Fin q, χ (ZMod.finEquiv q r) := ((ZMod.finEquiv q).sum_comp χ).symm
      _ = ∑ r : Fin q, χ (r.val : ZMod q) := by simp_rw [hfin]
      _ = ∑ u ∈ Finset.range q, χ (u : ZMod q) :=
          Fin.sum_univ_eq_sum_range (fun u : ℕ => χ (u : ZMod q)) q
  rw [← hsum, χ.sum_eq_zero_of_ne_one hχ, mul_zero]

private lemma dirichletChar_eq_sum_fourierRoot {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (n : ℕ) :
    χ n = ∑ a ∈ Finset.Ico 1 q, charFourierCoeff χ a * (fourierRoot q a) ^ n := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hrange : Finset.range q = insert 0 (Finset.Ico 1 q) := by
    ext a; simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Ico]; omega
  have h0_not : (0 : ℕ) ∉ Finset.Ico 1 q := by simp
  have hfull : (∑ a ∈ Finset.range q, charFourierCoeff χ a * (fourierRoot q a) ^ n) =
      ∑ a ∈ Finset.Ico 1 q, charFourierCoeff χ a * (fourierRoot q a) ^ n := by
    rw [hrange, Finset.sum_insert h0_not, charFourierCoeff_zero_eq_zero hχ, zero_mul, zero_add]
  rw [← hfull]
  unfold charFourierCoeff fourierRoot
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  set u₀ : ℕ := n % q
  have hu₀_mem : u₀ ∈ Finset.range q := Finset.mem_range.mpr (Nat.mod_lt n (by omega))
  have horth : ∀ u ∈ Finset.range q,
      (∑ a ∈ Finset.range q,
        (q : ℂ)⁻¹ * (χ u * Complex.exp (-2 * Real.pi * Complex.I * (a : ℂ) * (u : ℂ) / (q : ℂ))) *
          Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (q : ℂ)) ^ n) =
        if u = u₀ then χ u₀ else 0 := by
    intro u hu
    have hu_lt : u < q := Finset.mem_range.mp hu
    set ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I * (((n : ℤ) - (u : ℤ) : ℤ) : ℂ) / (q : ℂ))
    have hterm : ∀ a : ℕ,
        (q : ℂ)⁻¹ * (χ u * Complex.exp (-2 * Real.pi * Complex.I * (a : ℂ) * (u : ℂ) / (q : ℂ))) *
          Complex.exp (2 * Real.pi * Complex.I * (a : ℂ) / (q : ℂ)) ^ n =
        (q : ℂ)⁻¹ * χ u * ζ ^ a := by
      intro a
      rw [← Complex.exp_nat_mul]
      have hexp_eq : Complex.exp (-2 * Real.pi * Complex.I * (a : ℂ) * (u : ℂ) / (q : ℂ)) *
            Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I * (a : ℂ) / (q : ℂ))) =
          Complex.exp ((a : ℂ) * (2 * Real.pi * Complex.I * (((n : ℤ) - (u : ℤ) : ℤ) : ℂ) / (q : ℂ))) := by
        rw [← Complex.exp_add]
        congr 1
        push_cast
        ring
      calc (q : ℂ)⁻¹ * (χ u * Complex.exp (-2 * Real.pi * Complex.I * (a : ℂ) * (u : ℂ) / (q : ℂ))) *
            Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I * (a : ℂ) / (q : ℂ)))
          = (q : ℂ)⁻¹ * χ u *
              (Complex.exp (-2 * Real.pi * Complex.I * (a : ℂ) * (u : ℂ) / (q : ℂ)) *
                Complex.exp ((n : ℂ) * (2 * Real.pi * Complex.I * (a : ℂ) / (q : ℂ)))) := by ring
        _ = (q : ℂ)⁻¹ * χ u * ζ ^ a := by rw [hexp_eq, ← Complex.exp_nat_mul]
    simp_rw [hterm, ← Finset.mul_sum]
    by_cases heq : u = u₀
    · rw [if_pos heq]
      subst heq
      have hdiv_c : (((n : ℤ) - (u₀ : ℤ) : ℤ) : ℂ) = ((n / q : ℕ) : ℂ) * (q : ℂ) := by
        have hmod : (n / q) * q + u₀ = n := by
          dsimp [u₀]; rw [Nat.mul_comm]; exact Nat.div_add_mod n q
        have hc : (((n / q) * q + u₀ : ℕ) : ℤ) = (n : ℤ) := congrArg Nat.cast hmod
        rw [Nat.cast_add, Nat.cast_mul] at hc
        have hi : (n : ℤ) - (u₀ : ℤ) = ((n / q : ℕ) : ℤ) * (q : ℤ) := by linarith only [hc]
        rw [hi]
        push_cast
        rfl
      have hζ1 : ζ = 1 := by
        dsimp [ζ]
        rw [hdiv_c]
        have hsimp : 2 * Real.pi * Complex.I * (((n / q : ℕ) : ℂ) * (q : ℂ)) / (q : ℂ) =
            ((n / q : ℕ) : ℂ) * (2 * Real.pi * Complex.I) := by
          field_simp [hq0]
        rw [hsimp, Complex.exp_nat_mul, Complex.exp_two_pi_mul_I, one_pow]
      rw [hζ1]
      simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      field_simp [hq0]
    · rw [if_neg heq]
      have hζq : ζ ^ q = 1 := by
        dsimp [ζ]
        rw [← Complex.exp_nat_mul]
        have hsimp : (q : ℂ) * (2 * Real.pi * Complex.I * (((n : ℤ) - (u : ℤ) : ℤ) : ℂ) / (q : ℂ)) =
            (((n : ℤ) - (u : ℤ) : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
          field_simp [hq0]
        rw [hsimp, Complex.exp_int_mul, Complex.exp_two_pi_mul_I, one_zpow]
      have hζ_ne1 : ζ ≠ 1 := by
        intro h1
        rw [Complex.exp_eq_one_iff] at h1
        obtain ⟨k, hk⟩ := h1
        have hpi : (2 * Real.pi * Complex.I : ℂ) ≠ 0 :=
          mul_ne_zero (mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
            Complex.I_ne_zero
        have hmul : (2 * Real.pi * Complex.I) * ((((n : ℤ) - (u : ℤ) : ℤ) : ℂ) / (q : ℂ)) =
            (2 * Real.pi * Complex.I) * (k : ℂ) := by
          calc (2 * Real.pi * Complex.I) * ((((n : ℤ) - (u : ℤ) : ℤ) : ℂ) / (q : ℂ))
              = 2 * Real.pi * Complex.I * (((n : ℤ) - (u : ℤ) : ℤ) : ℂ) / (q : ℂ) :=
                (mul_div_assoc _ _ _).symm
            _ = (k : ℂ) * (2 * Real.pi * Complex.I) := hk
            _ = (2 * Real.pi * Complex.I) * (k : ℂ) := mul_comm _ _
        have hdiv := mul_left_cancel₀ hpi hmul
        have hceq : (((n : ℤ) - (u : ℤ) : ℤ) : ℂ) = (k : ℂ) * (q : ℂ) := (div_eq_iff hq0).mp hdiv
        have hreq : (((n : ℤ) - (u : ℤ) : ℤ) : ℝ) = (k : ℝ) * (q : ℝ) := by
          simpa using congrArg Complex.re hceq
        have hieq : (n : ℤ) - (u : ℤ) = k * (q : ℤ) := by exact_mod_cast hreq
        have hn_mod : (n / q) * q + u₀ = n := by
          dsimp [u₀]; rw [Nat.mul_comm]; exact Nat.div_add_mod n q
        have hc_mod : (((n / q) * q + u₀ : ℕ) : ℤ) = (n : ℤ) := congrArg Nat.cast hn_mod
        rw [Nat.cast_add, Nat.cast_mul] at hc_mod
        have hu₀_lt : u₀ < q := Nat.mod_lt n (by omega)
        have hdiff_u : (u₀ : ℤ) - (u : ℤ) = (k - ((n / q : ℕ) : ℤ)) * (q : ℤ) := by
          linear_combination hieq + hc_mod
        rcases le_or_gt (k - ((n / q : ℕ) : ℤ)) 0 with hkle | hkgt
        · rcases eq_or_lt_of_le hkle with hk0 | hkneg
          · rw [hk0, zero_mul] at hdiff_u
            exact heq (by omega)
          · have : (k - ((n / q : ℕ) : ℤ)) * (q : ℤ) ≤ -(q : ℤ) := by nlinarith
            omega
        · have : (q : ℤ) ≤ (k - ((n / q : ℕ) : ℤ)) * (q : ℤ) := by nlinarith
          omega
      rw [geom_sum_eq hζ_ne1, hζq, sub_self, zero_div, mul_zero]
  rw [Finset.sum_congr rfl horth, Finset.sum_ite_eq' _ u₀, if_pos hu₀_mem]
  dsimp [u₀]
  rw [ZMod.natCast_mod]

private def twistedMeanDiff (q : ℕ) (ξ : ℂ) (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  (q : ℂ)⁻¹ * ∑ r ∈ Finset.range q, ξ ^ r * g (x + (r : ℝ))

private lemma twistedMeanDiff_apply (q : ℕ) (ξ : ℂ) (g : ℝ → ℂ) (x : ℝ) :
    twistedMeanDiff q ξ g x =
      (q : ℂ)⁻¹ * ∑ r ∈ Finset.range q, ξ ^ r * g (x + (r : ℝ)) := rfl

private lemma hasDerivAt_iterate_twistedMeanDiff_dqptRp (q : ℕ) (ξ : ℂ) (k : ℕ)
    {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 < x) :
    HasDerivAt ((twistedMeanDiff q ξ)^[k] (dqptRp z))
      ((-z) * ((twistedMeanDiff q ξ)^[k] (dqptRp (z + 1))) x) x := by
  induction k generalizing x with
  | zero =>
    simpa only [Function.iterate_zero_apply] using hasDerivAt_dqptRp hz hx
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', twistedMeanDiff_apply]
    have hsum : ∀ m : ℕ, HasDerivAt
        (fun y : ℝ => ∑ r ∈ Finset.range m,
          ξ ^ r * ((twistedMeanDiff q ξ)^[k] (dqptRp z)) (y + (r : ℝ)))
        (∑ r ∈ Finset.range m,
          ξ ^ r * ((-z) * ((twistedMeanDiff q ξ)^[k] (dqptRp (z + 1))) (x + (r : ℝ)))) x := by
      intro m
      induction m with
      | zero =>
        simp only [Finset.range_zero, Finset.sum_empty]
        exact hasDerivAt_const x (0 : ℂ)
      | succ m ihm =>
        simp only [Finset.sum_range_succ]
        have hcomp : HasDerivAt
            (fun y : ℝ => ((twistedMeanDiff q ξ)^[k] (dqptRp z)) (y + (m : ℝ)))
            ((-z) * ((twistedMeanDiff q ξ)^[k] (dqptRp (z + 1))) (x + (m : ℝ))) x :=
          HasDerivAt.comp_add_const x (m : ℝ) (ih (by positivity : 0 < x + (m : ℝ)))
        exact ihm.add (hcomp.const_mul (ξ ^ m))
    refine ((hsum q).const_mul (q : ℂ)⁻¹).congr_deriv ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun r _ => by ring

private lemma sum_range_cast_real {q : ℕ} (hq : 1 ≤ q) :
    (∑ r ∈ Finset.range q, (r : ℝ)) = ((q - 1 : ℕ) : ℝ) * (q : ℝ) / 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  clear hq
  change (∑ r ∈ Finset.range (m + 1), (r : ℝ)) = ((m + 1 - 1 : ℕ) : ℝ) * ((m + 1 : ℕ) : ℝ) / 2
  rw [Nat.add_sub_cancel]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

private lemma norm_iterate_twistedMeanDiff_dqptRp_le {q : ℕ} (hq : 1 ≤ q) {ξ : ℂ}
    (hξ_norm : ‖ξ‖ = 1) (hξ_ne : ξ ≠ 1) (hξ_pow : ξ ^ q = 1) (k : ℕ)
    {z : ℂ} (hz : 0 < z.re) {x : ℝ} (hx : 0 < x) :
    ‖((twistedMeanDiff q ξ)^[k] (dqptRp z)) x‖ ≤
      (((q - 1 : ℕ) : ℝ) / 2) ^ k *
        (∏ m ∈ Finset.range k, ‖z + (m : ℂ)‖) * x ^ (-z.re - (k : ℝ)) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  induction k generalizing z x with
  | zero =>
    rw [Function.iterate_zero_apply, pow_zero, Finset.range_zero, Finset.prod_empty,
      Nat.cast_zero, sub_zero, one_mul, one_mul, dqptRp_norm hx]
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    set F : ℝ → ℂ := (twistedMeanDiff q ξ)^[k] (dqptRp z)
    have hzero_sum : ∑ r ∈ Finset.range q, ξ ^ r = 0 := by
      rw [geom_sum_eq hξ_ne, hξ_pow, sub_self, zero_div]
    have hsub_form : twistedMeanDiff q ξ F x =
        (q : ℂ)⁻¹ * ∑ r ∈ Finset.range q, ξ ^ r * (F (x + (r : ℝ)) - F x) := by
      rw [twistedMeanDiff_apply]
      have hfx : (∑ r ∈ Finset.range q, ξ ^ r * F x) = 0 := by
        rw [← Finset.sum_mul, hzero_sum, zero_mul]
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib, hfx, sub_zero]
    set B : ℝ := (((q - 1 : ℕ) : ℝ) / 2) ^ k *
      (∏ m ∈ Finset.range (k + 1), ‖z + (m : ℂ)‖) * x ^ (-z.re - ((k + 1 : ℕ) : ℝ))
    have hmvt : ∀ r ∈ Finset.range q, ‖F (x + (r : ℝ)) - F x‖ ≤ B * (r : ℝ) := by
      intro r _
      have hdiff : ∀ u ∈ Set.Icc x (x + (r : ℝ)),
          HasDerivAt F ((-z) * ((twistedMeanDiff q ξ)^[k] (dqptRp (z + 1))) u) u :=
        fun u hu => hasDerivAt_iterate_twistedMeanDiff_dqptRp q ξ k hz (lt_of_lt_of_le hx hu.1)
      have hd_le : ∀ u ∈ Set.Icc x (x + (r : ℝ)), ‖deriv F u‖ ≤ B := by
        intro u hu
        have hu_pos : 0 < u := lt_of_lt_of_le hx hu.1
        rw [(hdiff u hu).deriv, norm_mul, norm_neg]
        have hz1 : 0 < (z + 1).re := by simp; linarith
        have hih_u := ih hz1 hu_pos
        have hprod : ‖z‖ * (∏ m ∈ Finset.range k, ‖z + 1 + (m : ℂ)‖) =
            ∏ m ∈ Finset.range (k + 1), ‖z + (m : ℂ)‖ := by
          rw [Finset.prod_range_succ']
          simp only [Nat.cast_zero, add_zero, mul_comm ‖z‖]
          congr 1
          refine Finset.prod_congr rfl fun m _ => ?_
          push_cast; ring_nf
        have hexp_eq : -(z + 1).re - (k : ℝ) = -z.re - ((k + 1 : ℕ) : ℝ) := by
          simp; ring
        have hu_rpow : u ^ (-(z + 1).re - (k : ℝ)) ≤ x ^ (-z.re - ((k + 1 : ℕ) : ℝ)) := by
          rw [hexp_eq]
          exact Real.rpow_le_rpow_of_nonpos hx hu.1 (by linarith [Nat.cast_nonneg (α := ℝ) k])
        calc ‖z‖ * ‖((twistedMeanDiff q ξ)^[k] (dqptRp (z + 1))) u‖
            ≤ ‖z‖ * ((((q - 1 : ℕ) : ℝ) / 2) ^ k *
                (∏ m ∈ Finset.range k, ‖z + 1 + (m : ℂ)‖) * u ^ (-(z + 1).re - (k : ℝ))) :=
              mul_le_mul_of_nonneg_left hih_u (norm_nonneg z)
          _ ≤ ‖z‖ * ((((q - 1 : ℕ) : ℝ) / 2) ^ k *
                (∏ m ∈ Finset.range k, ‖z + 1 + (m : ℂ)‖) * x ^ (-z.re - ((k + 1 : ℕ) : ℝ))) :=
              mul_le_mul_of_nonneg_left
                (mul_le_mul_of_nonneg_left hu_rpow
                  (mul_nonneg (pow_nonneg (by positivity) _)
                    (Finset.prod_nonneg fun _ _ => norm_nonneg _)))
                (norm_nonneg z)
          _ = ((((q - 1 : ℕ) : ℝ) / 2) ^ k) *
                (‖z‖ * ∏ m ∈ Finset.range k, ‖z + 1 + (m : ℂ)‖) *
                x ^ (-z.re - ((k + 1 : ℕ) : ℝ)) := by ring
          _ = B := by rw [hprod]
      have hconv := Convex.norm_image_sub_le_of_norm_deriv_le (𝕜 := ℝ)
        (fun u hu => (hdiff u hu).differentiableAt)
        hd_le (convex_Icc x (x + (r : ℝ)))
        (Set.left_mem_Icc.mpr (by linarith [Nat.cast_nonneg (α := ℝ) r]))
        (Set.right_mem_Icc.mpr (by linarith [Nat.cast_nonneg (α := ℝ) r]))
      simpa only [add_sub_cancel_left, Real.norm_of_nonneg (Nat.cast_nonneg (α := ℝ) r)] using hconv
    have hsum_B : (∑ r ∈ Finset.range q, B * (r : ℝ)) = B * ∑ r ∈ Finset.range q, (r : ℝ) :=
      (Finset.mul_sum _ _ _).symm
    rw [hsub_form, norm_mul, norm_inv, Complex.norm_natCast]
    calc (q : ℝ)⁻¹ * ‖∑ r ∈ Finset.range q, ξ ^ r * (F (x + (r : ℝ)) - F x)‖
        ≤ (q : ℝ)⁻¹ * ∑ r ∈ Finset.range q, ‖ξ ^ r * (F (x + (r : ℝ)) - F x)‖ :=
          mul_le_mul_of_nonneg_left (norm_sum_le _ _) (inv_nonneg.mpr hq_pos.le)
      _ ≤ (q : ℝ)⁻¹ * ∑ r ∈ Finset.range q, B * (r : ℝ) := by
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun r hr => ?_)
            (inv_nonneg.mpr hq_pos.le)
          rw [norm_mul, norm_pow, hξ_norm, one_pow, one_mul]
          exact hmvt r hr
      _ = (q : ℝ)⁻¹ * (B * ∑ r ∈ Finset.range q, (r : ℝ)) := by rw [hsum_B]
      _ = (((q - 1 : ℕ) : ℝ) / 2) * B := by
          rw [sum_range_cast_real hq]
          field_simp [hq_pos.ne']
      _ = (((q - 1 : ℕ) : ℝ) / 2) ^ (k + 1) *
            (∏ m ∈ Finset.range (k + 1), ‖z + (m : ℂ)‖) * x ^ (-z.re - ((k + 1 : ℕ) : ℝ)) := by
          dsimp [B]; rw [pow_succ]; ring

private lemma iterate_strideMean_blockTail {q : ℕ} (hq : 1 ≤ q) {ξ : ℂ} (hξ_pow : ξ ^ q = 1)
    (B M N : ℕ) (z : ℂ) :
    (strideMean q 1)^[M]
        (fun K => ∑ m ∈ Finset.Icc (K + 1) (K + B * q), ξ ^ m * (m : ℂ) ^ (-z)) N =
      (q : ℂ) * ξ ^ (N + 1) *
        ∑ b ∈ Finset.range B,
          ((twistedMeanDiff q ξ)^[M + 1] (dqptRp z)) ((N : ℝ) + 1 + (b : ℝ) * (q : ℝ)) := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  induction M generalizing N with
  | zero =>
    rw [Function.iterate_zero_apply, zero_add, Function.iterate_one]
    have hbij : (∑ m ∈ Finset.Icc (N + 1) (N + B * q), ξ ^ m * (m : ℂ) ^ (-z)) =
        ∑ p ∈ Finset.range B ×ˢ Finset.range q,
          ξ ^ (N + 1 + p.1 * q + p.2) * ((N + 1 + p.1 * q + p.2 : ℕ) : ℂ) ^ (-z) := by
      symm
      refine Finset.sum_bij (fun p _ => N + 1 + p.1 * q + p.2) ?_ ?_ ?_ ?_
      · rintro ⟨b, r⟩ hp
        obtain ⟨hb, hr⟩ := Finset.mem_product.mp hp
        have hb_lt : b < B := Finset.mem_range.mp hb
        have hr_lt : r < q := Finset.mem_range.mp hr
        have htop : (b + 1) * q ≤ B * q := Nat.mul_le_mul_right q (by omega)
        dsimp only
        exact Finset.mem_Icc.mpr ⟨by omega, by rw [Nat.succ_mul] at htop; omega⟩
      · rintro ⟨b₁, r₁⟩ hp₁ ⟨b₂, r₂⟩ hp₂ heq
        dsimp only at heq
        have hr₁ : r₁ < q := Finset.mem_range.mp (Finset.mem_product.mp hp₁).2
        have hr₂ : r₂ < q := Finset.mem_range.mp (Finset.mem_product.mp hp₂).2
        have hlin : b₁ * q + r₁ = b₂ * q + r₂ := by omega
        have hdiv₁ : (b₁ * q + r₁) / q = b₁ := by
          rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr₁, add_zero]
        have hdiv₂ : (b₂ * q + r₂) / q = b₂ := by
          rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hr₂, add_zero]
        have hb_eq : b₁ = b₂ := by rw [← hdiv₁, hlin, hdiv₂]
        subst hb_eq
        ext <;> omega
      · intro m hm
        obtain ⟨hm_lo, hm_hi⟩ := Finset.mem_Icc.mp hm
        set u := m - (N + 1)
        have hu_lt : u < B * q := by omega
        refine ⟨(u / q, u % q), Finset.mem_product.mpr ⟨Finset.mem_range.mpr ?_,
          Finset.mem_range.mpr (Nat.mod_lt u (by omega))⟩, ?_⟩
        · exact (Nat.div_lt_iff_lt_mul (by omega)).mpr hu_lt
        · dsimp only
          have hmod := Nat.div_add_mod u q
          rw [Nat.mul_comm] at hmod
          omega
      · rintro ⟨b, r⟩ _; rfl
    rw [hbij, Finset.sum_product]
    simp_rw [twistedMeanDiff_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun r _ => ?_
    have hpow : ξ ^ (N + 1 + b * q + r) = ξ ^ (N + 1) * ξ ^ r := by
      rw [pow_add, pow_add, mul_comm b q, pow_mul, hξ_pow, one_pow, mul_one]
    have hcast : (((N + 1 + b * q + r : ℕ) : ℂ)) ^ (-z) =
        dqptRp z ((N : ℝ) + 1 + (b : ℝ) * (q : ℝ) + (r : ℝ)) := by
      unfold dqptRp
      congr 1
      push_cast
      ring
    rw [hpow, hcast]
    field_simp [hq0]
  | succ M ih =>
    rw [Function.iterate_succ_apply', strideMean_apply]
    simp_rw [mul_one, ih]
    have hlhs : (q : ℂ)⁻¹ * ∑ s ∈ Finset.range q,
          ((q : ℂ) * ξ ^ (N + s + 1) *
            ∑ b ∈ Finset.range B,
              ((twistedMeanDiff q ξ)^[M + 1] (dqptRp z))
                (((N + s : ℕ) : ℝ) + 1 + (b : ℝ) * (q : ℝ))) =
        ∑ b ∈ Finset.range B, ∑ s ∈ Finset.range q,
          (q : ℂ)⁻¹ * ((q : ℂ) * ξ ^ (N + s + 1) *
            ((twistedMeanDiff q ξ)^[M + 1] (dqptRp z))
              (((N + s : ℕ) : ℝ) + 1 + (b : ℝ) * (q : ℝ))) := by
      simp_rw [Finset.mul_sum]
      exact Finset.sum_comm
    have hrhs : (q : ℂ) * ξ ^ (N + 1) *
          ∑ b ∈ Finset.range B,
            ((twistedMeanDiff q ξ)^[M + 1 + 1] (dqptRp z))
              ((N : ℝ) + 1 + (b : ℝ) * (q : ℝ)) =
        ∑ b ∈ Finset.range B, ∑ s ∈ Finset.range q,
          (q : ℂ) * ξ ^ (N + 1) * ((q : ℂ)⁻¹ *
            (ξ ^ s * ((twistedMeanDiff q ξ)^[M + 1] (dqptRp z))
              ((N : ℝ) + 1 + (b : ℝ) * (q : ℝ) + (s : ℝ)))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [Function.iterate_succ_apply', twistedMeanDiff_apply, ← mul_assoc, Finset.mul_sum]
      exact Finset.sum_congr rfl fun s _ => by ring
    rw [hlhs, hrhs]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun s _ => ?_
    have hpow : ξ ^ (N + s + 1) = ξ ^ (N + 1) * ξ ^ s := by
      rw [show N + s + 1 = (N + 1) + s by omega, pow_add]
    have harg : ((N + s : ℕ) : ℝ) + 1 + (b : ℝ) * (q : ℝ) =
        (N : ℝ) + 1 + (b : ℝ) * (q : ℝ) + (s : ℝ) := by
      push_cast; ring
    rw [hpow, harg]
    ring

private lemma sum_block_rpow_le {q : ℕ} (hq : 1 ≤ q) {β : ℝ} (hβ : 1 ≤ β) (N B : ℕ) :
    (∑ b ∈ Finset.range B, ((N : ℝ) + 1 + (b : ℝ) * (q : ℝ)) ^ (-β - 1)) ≤
      2 * ((N : ℝ) + 1) ^ (-β) := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) N]
  have hq_ge1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  rcases B with _ | B'
  · simp; positivity
  · rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, add_zero]
    have h0 : ((N : ℝ) + 1) ^ (-β - 1) ≤ ((N : ℝ) + 1) ^ (-β) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
    have hstep : ∀ j ∈ Finset.range B',
        ((N : ℝ) + 1 + (((j + 1 : ℕ) : ℝ)) * (q : ℝ)) ^ (-β - 1) ≤
          ((N : ℝ) + 1 + (j : ℝ) * (q : ℝ)) ^ (-β) -
            ((N : ℝ) + 1 + (((j + 1 : ℕ) : ℝ)) * (q : ℝ)) ^ (-β) := by
      intro j _
      set x : ℝ := (N : ℝ) + 1 + (j : ℝ) * (q : ℝ)
      have hx_pos : 0 < x := by dsimp [x]; positivity
      have hy_eq : (N : ℝ) + 1 + (((j + 1 : ℕ) : ℝ)) * (q : ℝ) = x + (q : ℝ) := by
        dsimp [x]; push_cast; ring
      rw [hy_eq]
      have hx_lt : x < x + (q : ℝ) := by linarith
      have hcont : ContinuousOn (fun u : ℝ => -(u ^ (-β))) (Set.Icc x (x + (q : ℝ))) :=
        (ContinuousOn.rpow_const continuousOn_id
          fun u hu => Or.inl (lt_of_lt_of_le hx_pos hu.1).ne').neg
      have hder : ∀ u ∈ Set.Ioo x (x + (q : ℝ)),
          HasDerivAt (fun v : ℝ => -(v ^ (-β))) (β * u ^ (-β - 1)) u := fun u hu => by
        have hd := Real.hasDerivAt_rpow_const (x := u) (p := -β)
          (Or.inl (lt_trans hx_pos hu.1).ne')
        exact hd.neg.congr_deriv (by ring)
      obtain ⟨c, ⟨hc_lo, hc_hi⟩, hslope⟩ := exists_hasDerivAt_eq_slope
        (fun v : ℝ => -(v ^ (-β))) (fun u => β * u ^ (-β - 1)) hx_lt hcont hder
      have hsub_x : x + (q : ℝ) - x = (q : ℝ) := by ring
      rw [hsub_x, show -(x + (q : ℝ)) ^ (-β) - -x ^ (-β) = x ^ (-β) - (x + (q : ℝ)) ^ (-β) by ring]
        at hslope
      have hc_pos : 0 < c := lt_trans hx_pos hc_lo
      have hc_mono : (x + (q : ℝ)) ^ (-β - 1) ≤ c ^ (-β - 1) :=
        Real.rpow_le_rpow_of_nonpos hc_pos hc_hi.le (by linarith)
      have hprod : (x + (q : ℝ)) ^ (-β - 1) ≤ (q : ℝ) * (β * c ^ (-β - 1)) := by
        calc (x + (q : ℝ)) ^ (-β - 1) = 1 * (1 * (x + (q : ℝ)) ^ (-β - 1)) := by ring
          _ ≤ (q : ℝ) * (β * c ^ (-β - 1)) :=
              mul_le_mul hq_ge1 (mul_le_mul hβ hc_mono (by positivity) (by positivity))
                (by positivity) (by positivity)
      have hmul_q := (div_eq_iff (by positivity : (q : ℝ) ≠ 0)).mp hslope.symm
      linarith
    have htel : ∀ K : ℕ,
        (∑ j ∈ Finset.range K,
          (((N : ℝ) + 1 + (j : ℝ) * (q : ℝ)) ^ (-β) -
            ((N : ℝ) + 1 + (((j + 1 : ℕ) : ℝ)) * (q : ℝ)) ^ (-β))) =
        ((N : ℝ) + 1) ^ (-β) - ((N : ℝ) + 1 + (K : ℝ) * (q : ℝ)) ^ (-β) := by
      intro K
      induction K with
      | zero => simp
      | succ K ih =>
        rw [Finset.sum_range_succ, ih]
        ring
    have hsum_le := (Finset.sum_le_sum hstep).trans_eq (htel B')
    have hend_nonneg : 0 ≤ ((N : ℝ) + 1 + (B' : ℝ) * (q : ℝ)) ^ (-β) :=
      Real.rpow_nonneg (by positivity) _
    linarith

private lemma tendsto_iterate_strideMean_LFunction {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) {z : ℂ} (hz : 0 < z.re) (M N : ℕ) :
    Tendsto
      (fun B : ℕ => (strideMean q 1)^[M] (fun K => charPartialSum χ z (K + B * q)) N)
      atTop (𝓝 (χ.LFunction z)) := by
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  induction M generalizing N with
  | zero =>
    simp only [Function.iterate_zero_apply]
    have hmap : Tendsto (fun B : ℕ => N + B * q) atTop atTop :=
      Filter.tendsto_atTop_atTop.mpr fun K => ⟨K, fun B hB => by
        have hBq : B * 1 ≤ B * q := Nat.mul_le_mul_left B (by omega)
        rw [Nat.mul_one] at hBq
        omega⟩
    exact (tendsto_charPartialSum_LFunction hχ hz).comp hmap
  | succ M ih =>
    have hstep : (fun B : ℕ => (strideMean q 1)^[M + 1] (fun K => charPartialSum χ z (K + B * q)) N) =
        fun B : ℕ => (q : ℂ)⁻¹ * ∑ r ∈ Finset.range q,
          (strideMean q 1)^[M] (fun K => charPartialSum χ z (K + B * q)) (N + r) := by
      funext B
      rw [Function.iterate_succ_apply', strideMean_apply]
      simp only [mul_one]
    rw [hstep]
    have hlim : (q : ℂ)⁻¹ * (∑ _r ∈ Finset.range q, χ.LFunction z) = χ.LFunction z := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc,
        inv_mul_cancel₀ hq0, one_mul]
    rw [← hlim]
    exact (tendsto_finsetSum (s := Finset.range q) fun r _ => ih (N + r)).const_mul (q : ℂ)⁻¹

/-- **Universal modulus-`q` periodic Euler–Fourier remainder bound:** for every `q ≥ 2`, every
nonprincipal `χ : DirichletCharacter ℂ q`, every `N : ℕ`, `M ≥ 1`, and `Re z > 0`,
`‖χ.LFunction z - periodicEulerPartialSum χ N M z‖ ≤ periodicEulerTailBound q N M z`. -/
theorem norm_LFunction_sub_periodicEulerPartialSum_le {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (N : ℕ) {M : ℕ} (hM : 1 ≤ M)
    {z : ℂ} (hz : 0 < z.re) :
    ‖χ.LFunction z - periodicEulerPartialSum χ N M z‖ ≤ periodicEulerTailBound q N M z := by
  have hlim := ((tendsto_iterate_strideMean_LFunction hq hχ hz M N).sub
    (tendsto_const_nhds (x := periodicEulerPartialSum χ N M z))).norm
  refine le_of_tendsto hlim (Filter.Eventually.of_forall fun B => ?_)
  have hdiff_fn : (fun K : ℕ => charPartialSum χ z (K + B * q)) =
      fun K : ℕ => charPartialSum χ z K +
        ∑ a ∈ Finset.Ico 1 q, charFourierCoeff χ a *
          ∑ m ∈ Finset.Icc (K + 1) (K + B * q), (fourierRoot q a) ^ m * (m : ℂ) ^ (-z) := by
    funext K
    unfold charPartialSum
    have hunion : Finset.Icc 1 (K + B * q) = Finset.Icc 1 K ∪ Finset.Icc (K + 1) (K + B * q) := by
      ext m; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Icc 1 K) (Finset.Icc (K + 1) (K + B * q)) := by
      rw [Finset.disjoint_left]; intro m h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
    rw [hunion, Finset.sum_union hdisj]
    congr 1
    have hrew : (∑ m ∈ Finset.Icc (K + 1) (K + B * q), χ m * (m : ℂ) ^ (-z)) =
        ∑ m ∈ Finset.Icc (K + 1) (K + B * q),
          ∑ a ∈ Finset.Ico 1 q, charFourierCoeff χ a * ((fourierRoot q a) ^ m * (m : ℂ) ^ (-z)) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [dirichletChar_eq_sum_fourierRoot hq hχ m, Finset.sum_mul]
      exact Finset.sum_congr rfl fun a _ => mul_assoc _ _ _
    rw [hrew, Finset.sum_comm]
    exact Finset.sum_congr rfl fun a _ => (Finset.mul_sum _ _ _).symm
  have hiter_eq : (strideMean q 1)^[M] (fun K => charPartialSum χ z (K + B * q)) N -
        periodicEulerPartialSum χ N M z =
      ∑ a ∈ Finset.Ico 1 q, charFourierCoeff χ a *
        ((q : ℂ) * (fourierRoot q a) ^ (N + 1) *
          ∑ b ∈ Finset.range B,
            ((twistedMeanDiff q (fourierRoot q a))^[M + 1] (dqptRp z))
              ((N : ℝ) + 1 + (b : ℝ) * (q : ℝ))) := by
    unfold periodicEulerPartialSum
    rw [hdiff_fn, iterate_strideMean_add, add_sub_cancel_left, iterate_strideMean_finset_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [iterate_strideMean_smul]
    dsimp only
    rw [iterate_strideMean_blockTail (by omega) (fourierRoot_pow_period (by omega) a) B M N z]
  rw [hiter_eq]
  set E : ℝ := (((q - 1 : ℕ) : ℝ) / 2) ^ (M + 1) *
    (∏ m ∈ Finset.range (M + 1), ‖z + (m : ℂ)‖)
  have hE_nonneg : 0 ≤ E := mul_nonneg (pow_nonneg (by positivity) _)
    (Finset.prod_nonneg fun _ _ => norm_nonneg _)
  have hβ1 : 1 ≤ z.re + (M : ℝ) := by
    have : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    linarith
  refine (norm_sum_le _ _).trans ?_
  calc ∑ a ∈ Finset.Ico 1 q,
        ‖charFourierCoeff χ a * ((q : ℂ) * (fourierRoot q a) ^ (N + 1) *
          ∑ b ∈ Finset.range B,
            ((twistedMeanDiff q (fourierRoot q a))^[M + 1] (dqptRp z))
              ((N : ℝ) + 1 + (b : ℝ) * (q : ℝ)))‖
      ≤ ∑ _a ∈ Finset.Ico 1 q,
          (q : ℝ) * (E * (2 * ((N : ℝ) + 1) ^ (-z.re - (M : ℝ)))) := by
        refine Finset.sum_le_sum fun a ha => ?_
        obtain ⟨ha1, haq⟩ := Finset.mem_Ico.mp ha
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_natCast, norm_pow,
          norm_fourierRoot q a, one_pow, mul_one]
        have hcf := norm_charFourierCoeff_le_one χ a
        have hb_sum : ‖∑ b ∈ Finset.range B,
              ((twistedMeanDiff q (fourierRoot q a))^[M + 1] (dqptRp z))
                ((N : ℝ) + 1 + (b : ℝ) * (q : ℝ))‖ ≤
            E * (2 * ((N : ℝ) + 1) ^ (-z.re - (M : ℝ))) := by
          refine (norm_sum_le _ _).trans ?_
          have hb_pt : ∀ b ∈ Finset.range B,
              ‖((twistedMeanDiff q (fourierRoot q a))^[M + 1] (dqptRp z))
                  ((N : ℝ) + 1 + (b : ℝ) * (q : ℝ))‖ ≤
                E * ((N : ℝ) + 1 + (b : ℝ) * (q : ℝ)) ^ (-(z.re + (M : ℝ)) - 1) := by
            intro b _
            have hpt := norm_iterate_twistedMeanDiff_dqptRp_le (by omega)
              (norm_fourierRoot q a) (fourierRoot_ne_one ha1 haq)
              (fourierRoot_pow_period (by omega) a) (M + 1) hz
              (by positivity : 0 < (N : ℝ) + 1 + (b : ℝ) * (q : ℝ))
            have hexp : -z.re - ((M + 1 : ℕ) : ℝ) = -(z.re + (M : ℝ)) - 1 := by push_cast; ring
            simpa only [E, hexp] using hpt
          refine (Finset.sum_le_sum hb_pt).trans ?_
          rw [← Finset.mul_sum]
          have hblk := sum_block_rpow_le (by omega : 1 ≤ q) hβ1 N B
          have hexp2 : -(z.re + (M : ℝ)) = -z.re - (M : ℝ) := by ring
          conv_rhs at hblk => rw [hexp2]
          exact mul_le_mul_of_nonneg_left hblk hE_nonneg
        calc ‖charFourierCoeff χ a‖ * ((q : ℝ) *
              ‖∑ b ∈ Finset.range B,
                ((twistedMeanDiff q (fourierRoot q a))^[M + 1] (dqptRp z))
                  ((N : ℝ) + 1 + (b : ℝ) * (q : ℝ))‖)
            ≤ 1 * ((q : ℝ) * (E * (2 * ((N : ℝ) + 1) ^ (-z.re - (M : ℝ))))) :=
              mul_le_mul hcf (mul_le_mul_of_nonneg_left hb_sum (Nat.cast_nonneg q))
                (by positivity) zero_le_one
          _ = (q : ℝ) * (E * (2 * ((N : ℝ) + 1) ^ (-z.re - (M : ℝ)))) := one_mul _
    _ = periodicEulerTailBound q N M z := by
        rw [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
        unfold periodicEulerTailBound
        dsimp [E]
        ring

private lemma two_mul_add_one_le_two_pow_sub_half :
    ∀ {M : ℕ}, 10 ≤ M → 2 * M + 1 ≤ 2 ^ (M - M / 2) := by
  intro M hM
  induction M using Nat.strong_induction_on with
  | h M ih =>
    by_cases h12 : M < 12
    · interval_cases M <;> norm_num
    · have hM2 : 10 ≤ M - 2 := by omega
      have hprev := ih (M - 2) (by omega) hM2
      have hsub : M - M / 2 = (M - 2) - (M - 2) / 2 + 1 := by omega
      rw [hsub, pow_succ]
      omega

/-- **Uniform base-`2^{-M}` linear-cutoff decay across ALL moduli `q ≥ 2` and ALL heights
`|Im z| ≤ M`:** at linear cutoff `N = 2 q M + q - 1` (`N + 1 = q(2 M + 1)`), `periodicEulerTailBound`
decays as `≤ q^3 (2 M + 1) / 2^M` (and `≤ q^3 / 2^{M / 2}` for `M ≥ 10`). -/
theorem periodicEulerTailBound_linear_le {q M : ℕ} (hq : 2 ≤ q) (hM : 1 ≤ M)
    {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re ≤ 1) (him : |z.im| ≤ (M : ℝ)) :
    periodicEulerTailBound q (2 * q * M + q - 1) M z ≤
      (q : ℝ) ^ 3 * (2 * (M : ℝ) + 1) / (2 : ℝ) ^ M ∧
    (10 ≤ M →
      periodicEulerTailBound q (2 * q * M + q - 1) M z ≤ (q : ℝ) ^ 3 / (2 : ℝ) ^ (M / 2)) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have h2M1_pos : (0 : ℝ) < 2 * (M : ℝ) + 1 := by positivity
  have hN1_nat : 2 * q * M + q - 1 + 1 = q * (2 * M + 1) := by
    have hpos : 1 ≤ 2 * q * M + q := by omega
    rw [Nat.sub_add_cancel hpos]; ring
  have hN1_real : ((2 * q * M + q - 1 : ℕ) : ℝ) + 1 = (q : ℝ) * (2 * (M : ℝ) + 1) := by
    have hc : (((2 * q * M + q - 1 + 1 : ℕ) : ℝ)) = ((q * (2 * M + 1) : ℕ) : ℝ) :=
      congrArg Nat.cast hN1_nat
    push_cast at hc
    linarith
  have hprod : (∏ m ∈ Finset.range (M + 1), ‖z + (m : ℂ)‖) ≤
      (2 * (M : ℝ) + 1) ^ (M + 1) := by
    calc (∏ m ∈ Finset.range (M + 1), ‖z + (m : ℂ)‖)
        ≤ ∏ _m ∈ Finset.range (M + 1), (2 * (M : ℝ) + 1) := by
          refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun m hm => ?_
          have hm_le : (m : ℝ) ≤ (M : ℝ) := by
            exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
          have h1 := Complex.norm_le_abs_re_add_abs_im (z + (m : ℂ))
          simp only [Complex.add_re, Complex.natCast_re, Complex.add_im, Complex.natCast_im,
            add_zero] at h1
          rw [abs_of_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) m])] at h1
          linarith
      _ = (2 * (M : ℝ) + 1) ^ (M + 1) := by rw [Finset.prod_const, Finset.card_range]
  have hrpow : (((2 * q * M + q - 1 : ℕ) : ℝ) + 1) ^ (-z.re - (M : ℝ)) ≤
      ((q : ℝ) ^ M)⁻¹ * ((2 * (M : ℝ) + 1) ^ M)⁻¹ := by
    have hbase1 : (1 : ℝ) ≤ ((2 * q * M + q - 1 : ℕ) : ℝ) + 1 := by
      rw [hN1_real]
      nlinarith [show (2 : ℝ) ≤ (q : ℝ) by exact_mod_cast hq,
        show (1 : ℝ) ≤ (M : ℝ) by exact_mod_cast hM]
    calc (((2 * q * M + q - 1 : ℕ) : ℝ) + 1) ^ (-z.re - (M : ℝ))
        ≤ (((2 * q * M + q - 1 : ℕ) : ℝ) + 1) ^ (-(M : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le hbase1 (by linarith)
      _ = ((((2 * q * M + q - 1 : ℕ) : ℝ) + 1) ^ M)⁻¹ := by
          rw [Real.rpow_neg (by linarith), Real.rpow_natCast]
      _ = ((q : ℝ) ^ M)⁻¹ * ((2 * (M : ℝ) + 1) ^ M)⁻¹ := by
          rw [hN1_real, mul_pow, mul_inv]
  have hmain : periodicEulerTailBound q (2 * q * M + q - 1) M z ≤
      (q : ℝ) ^ 3 * (2 * (M : ℝ) + 1) / (2 : ℝ) ^ M := by
    unfold periodicEulerTailBound
    have hq1_le : ((q - 1 : ℕ) : ℝ) ≤ (q : ℝ) := by exact_mod_cast Nat.sub_le q 1
    have hstep1 : (∏ m ∈ Finset.range (M + 1), ‖z + (m : ℂ)‖) *
          (((2 * q * M + q - 1 : ℕ) : ℝ) + 1) ^ (-z.re - (M : ℝ)) ≤
        (2 * (M : ℝ) + 1) * ((q : ℝ) ^ M)⁻¹ := by
      calc (∏ m ∈ Finset.range (M + 1), ‖z + (m : ℂ)‖) *
            (((2 * q * M + q - 1 : ℕ) : ℝ) + 1) ^ (-z.re - (M : ℝ))
          ≤ (2 * (M : ℝ) + 1) ^ (M + 1) * (((q : ℝ) ^ M)⁻¹ * ((2 * (M : ℝ) + 1) ^ M)⁻¹) :=
            mul_le_mul hprod hrpow (by positivity) (by positivity)
        _ = (2 * (M : ℝ) + 1) * ((q : ℝ) ^ M)⁻¹ := by
            rw [pow_succ]
            field_simp [h2M1_pos.ne']
    have hstep2 : 2 * (q : ℝ) * ((q - 1 : ℕ) : ℝ) * (((q - 1 : ℕ) : ℝ) / 2) ^ (M + 1) ≤
        (q : ℝ) ^ 3 * ((q : ℝ) / 2) ^ M := by
      have hpow_le : (((q - 1 : ℕ) : ℝ) / 2) ^ (M + 1) ≤
          ((q : ℝ) / 2) * ((q : ℝ) / 2) ^ M := by
        rw [pow_succ']
        exact mul_le_mul (by linarith) (pow_le_pow_left₀ (by positivity) (by linarith) M)
          (by positivity) (by positivity)
      calc 2 * (q : ℝ) * ((q - 1 : ℕ) : ℝ) * (((q - 1 : ℕ) : ℝ) / 2) ^ (M + 1)
          ≤ 2 * (q : ℝ) * (q : ℝ) * (((q : ℝ) / 2) * ((q : ℝ) / 2) ^ M) :=
            mul_le_mul (mul_le_mul_of_nonneg_left hq1_le (by positivity)) hpow_le
              (by positivity) (by positivity)
        _ = (q : ℝ) ^ 3 * ((q : ℝ) / 2) ^ M := by ring
    calc 2 * (q : ℝ) * ((q - 1 : ℕ) : ℝ) * (((q - 1 : ℕ) : ℝ) / 2) ^ (M + 1) *
          (∏ m ∈ Finset.range (M + 1), ‖z + (m : ℂ)‖) *
          (((2 * q * M + q - 1 : ℕ) : ℝ) + 1) ^ (-z.re - (M : ℝ))
        = (2 * (q : ℝ) * ((q - 1 : ℕ) : ℝ) * (((q - 1 : ℕ) : ℝ) / 2) ^ (M + 1)) *
          ((∏ m ∈ Finset.range (M + 1), ‖z + (m : ℂ)‖) *
            (((2 * q * M + q - 1 : ℕ) : ℝ) + 1) ^ (-z.re - (M : ℝ))) := by ring
      _ ≤ ((q : ℝ) ^ 3 * ((q : ℝ) / 2) ^ M) * ((2 * (M : ℝ) + 1) * ((q : ℝ) ^ M)⁻¹) :=
          mul_le_mul hstep2 hstep1 (by positivity) (by positivity)
      _ = (q : ℝ) ^ 3 * (2 * (M : ℝ) + 1) / (2 : ℝ) ^ M := by
          rw [div_pow]
          field_simp [hq_pos.ne']
  refine ⟨hmain, fun hM10 => hmain.trans ?_⟩
  have h2M_le : (2 * (M : ℝ) + 1) ≤ (2 : ℝ) ^ (M - M / 2) := by
    exact_mod_cast two_mul_add_one_le_two_pow_sub_half hM10
  have hpow_split : (2 : ℝ) ^ M = (2 : ℝ) ^ (M - M / 2) * (2 : ℝ) ^ (M / 2) := by
    rw [← pow_add, Nat.sub_add_cancel (Nat.div_le_self M 2)]
  rw [hpow_split, div_mul_eq_div_div]
  refine div_le_div_of_nonneg_right ?_ (by positivity)
  rw [div_le_iff₀ (by positivity)]
  exact mul_le_mul_of_nonneg_left h2M_le (by positivity)

/-- **Exact zero-exclusion criterion for `periodicEulerPartialSum`:** beating `periodicEulerTailBound`
certifies `χ.LFunction z ≠ 0`, while at any zero `χ.LFunction z = 0` no `(N, M)` (`M ≥ 1`) ever passes. -/
theorem LFunction_ne_zero_of_periodicEuler_beats_tail {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (N : ℕ) {M : ℕ} (hM : 1 ≤ M)
    {z : ℂ} (hz : 0 < z.re) :
    (periodicEulerTailBound q N M z < ‖periodicEulerPartialSum χ N M z‖ → χ.LFunction z ≠ 0) ∧
    (χ.LFunction z = 0 → ‖periodicEulerPartialSum χ N M z‖ ≤ periodicEulerTailBound q N M z) := by
  have hrem := norm_LFunction_sub_periodicEulerPartialSum_le hq hχ N hM hz
  refine ⟨fun hlt hzero => ?_, fun hzero => ?_⟩
  · rw [hzero, zero_sub, norm_neg] at hrem
    linarith
  · rw [hzero, zero_sub, norm_neg] at hrem
    exact hrem

/-- **All-height linear-prefix certification for every nonprincipal Dirichlet `L`-function on
`20999/24000 < Re z ≤ 1`:** combining `SubSevenEighthsZeroFreeHalfPlane` with `periodicEulerTailBound_linear_le`
gives a finite witness at every height `Im z ∈ ℝ`. -/
theorem subSevenEighths_periodicEuler_beats_tail_all_heights {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {z : ℂ} (hlo : (20999 / 24000 : ℝ) < z.re) (hhi : z.re ≤ 1) :
    ∃ M : ℕ, max 10 ⌈|z.im|⌉₊ ≤ M ∧
      periodicEulerTailBound q (2 * q * M + q - 1) M z <
        ‖periodicEulerPartialSum χ (2 * q * M + q - 1) M z‖ := by
  have hne : χ.LFunction z ≠ 0 :=
    GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.DirichletCharacter.LFunction_ne_zero_of_sub_seven_eighths_lt_re
      χ hlo (fun h => hχ h.1)
  have hpos : 0 < ‖χ.LFunction z‖ := norm_pos_iff.mpr hne
  let K : ℕ := ⌈2 * (q : ℝ) ^ 3 / ‖χ.LFunction z‖⌉₊ + 1
  let M : ℕ := max (max 10 ⌈|z.im|⌉₊) (2 * K)
  refine ⟨M, le_max_left _ _, ?_⟩
  have hM10 : 10 ≤ M := le_trans (le_max_left 10 ⌈|z.im|⌉₊) (le_max_left _ _)
  have hM1 : 1 ≤ M := by omega
  have him : |z.im| ≤ (M : ℝ) := by
    have h1 : ⌈|z.im|⌉₊ ≤ M := le_trans (le_max_right 10 ⌈|z.im|⌉₊) (le_max_left _ _)
    exact (Nat.le_ceil |z.im|).trans (by exact_mod_cast h1)
  have hKM : K ≤ M / 2 :=
    (Nat.le_div_iff_mul_le zero_lt_two).mpr (by rw [mul_comm]; exact le_max_right _ _)
  have hpow_gt : 2 * (q : ℝ) ^ 3 / ‖χ.LFunction z‖ < (2 : ℝ) ^ (M / 2) := by
    have h1 : 2 * (q : ℝ) ^ 3 / ‖χ.LFunction z‖ < (K : ℝ) := by
      dsimp [K]; push_cast; linarith [Nat.le_ceil (2 * (q : ℝ) ^ 3 / ‖χ.LFunction z‖)]
    have h2 : (K : ℝ) ≤ (2 : ℝ) ^ K := by
      exact_mod_cast (Nat.lt_two_pow_self (n := K)).le
    have h3 : (2 : ℝ) ^ K ≤ (2 : ℝ) ^ (M / 2) := pow_le_pow_right₀ one_le_two hKM
    linarith
  have htail_lt : (q : ℝ) ^ 3 / (2 : ℝ) ^ (M / 2) < ‖χ.LFunction z‖ / 2 := by
    rw [div_lt_iff₀ (by positivity)]
    have hmul := (div_lt_iff₀ hpos).mp hpow_gt
    linarith
  have hlin := (periodicEulerTailBound_linear_le hq hM1 (by linarith) hhi him).2 hM10
  have hrem := norm_LFunction_sub_periodicEulerPartialSum_le hq hχ
    (2 * q * M + q - 1) hM1 (by linarith)
  have htri := norm_sub_norm_le (χ.LFunction z) (periodicEulerPartialSum χ (2 * q * M + q - 1) M z)
  linarith

/-- **Left-strip nonvanishing and reflected linear-prefix certification on `0 < Re s < 3001/24000`
for all primitive nonprincipal Dirichlet characters (`∀ Im s ∈ ℝ`):** via functional reflection
`RHTower.LFunction_eq_zero_conj_one_sub`. -/
theorem subOneEighth_primitive_periodicEuler_beats_tail_all_heights {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hprim : χ.IsPrimitive)
    {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < (3001 / 24000 : ℝ)) :
    χ.LFunction s ≠ 0 ∧
    ∃ M : ℕ, max 10 ⌈|s.im|⌉₊ ≤ M ∧
      periodicEulerTailBound q (2 * q * M + q - 1) M (1 - conj s) <
        ‖periodicEulerPartialSum χ (2 * q * M + q - 1) M (1 - conj s)‖ := by
  have hw_lo : (20999 / 24000 : ℝ) < (1 - conj s).re := by simp; linarith
  have hw_hi : (1 - conj s).re ≤ 1 := by simp; linarith
  have hw_im : |(1 - conj s).im| = |s.im| := by simp
  obtain ⟨M, hM, hbeat⟩ := subSevenEighths_periodicEuler_beats_tail_all_heights hq hχ hw_lo hw_hi
  rw [hw_im] at hM
  have hM1 : 1 ≤ M := le_trans (by norm_num : 1 ≤ 10) (le_trans (le_max_left _ _) hM)
  refine ⟨fun hzero => ?_, M, hM, hbeat⟩
  have hrefl := _root_.RHTower.LFunction_eq_zero_conj_one_sub hχ hprim hzero h0 (by linarith)
  have hconj_eq : conj (1 - s) = 1 - conj s := by rw [map_sub, map_one]
  rw [hconj_eq] at hrefl
  exact (LFunction_ne_zero_of_periodicEuler_beats_tail hq hχ (2 * q * M + q - 1)
    hM1 (by linarith)).1 hbeat hrefl

section HeckeAndSpecialLocus

open GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
open GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.HeckeFamily
open GaloisForLFunctions.ArithmeticGaugeTheory
open GaloisForLFunctions.ArithmeticCorrelationGeometry

/-- **Simultaneous `ℚ(ω)` Hecke base-change certification on `20999/24000 < Re z < 1` (`∀ Im z ∈ ℝ`):**
for `HeckeDirichlet.character χ` (`χ ≠ 1` and `HeckeIdealSeries.baseChangeChar χ ≠ 1`), both factors
of `HeckeDirichlet.LFunction_eq_dirichlet_product` are nonzero and certified by linear-prefix
periodic Euler sums. -/
theorem hecke_dirichletBaseChange_beats_tail_on_subSevenEighths {q : ℕ} [NeZero q] (hq : 2 ≤ q)
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    (hbc : HeckeIdealSeries.baseChangeChar χ ≠ 1)
    {z : ℂ} (hlo : (20999 / 24000 : ℝ) < z.re) (hhi : z.re < 1) :
    LFunction (HeckeDirichlet.character χ) z ≠ 0 ∧
    (∃ M₁ : ℕ, max 10 ⌈|z.im|⌉₊ ≤ M₁ ∧
      periodicEulerTailBound q (2 * q * M₁ + q - 1) M₁ z <
        ‖periodicEulerPartialSum χ (2 * q * M₁ + q - 1) M₁ z‖) ∧
    (∃ M₂ : ℕ, max 10 ⌈|z.im|⌉₊ ≤ M₂ ∧
      periodicEulerTailBound (q * 3) (2 * (q * 3) * M₂ + (q * 3) - 1) M₂ z <
        ‖periodicEulerPartialSum (HeckeIdealSeries.baseChangeChar χ)
          (2 * (q * 3) * M₂ + (q * 3) - 1) M₂ z‖) := by
  haveI : NeZero (q * 3) := ⟨by omega⟩
  have hz0 : z ≠ 0 := by intro h; rw [h, Complex.zero_re] at hlo; norm_num at hlo
  have hz1 : z ≠ 1 := by intro h; rw [h, Complex.one_re] at hhi; norm_num at hhi
  have hprod := HeckeDirichlet.LFunction_eq_dirichlet_product χ hz0 hz1
  obtain ⟨M₁, hM₁, hb₁⟩ := subSevenEighths_periodicEuler_beats_tail_all_heights hq hχ hlo hhi.le
  obtain ⟨M₂, hM₂, hb₂⟩ := subSevenEighths_periodicEuler_beats_tail_all_heights
    (q := q * 3) (by omega) hbc hlo hhi.le
  have hM₁_pos : 1 ≤ M₁ := le_trans (by norm_num : 1 ≤ 10) (le_trans (le_max_left _ _) hM₁)
  have hM₂_pos : 1 ≤ M₂ := le_trans (by norm_num : 1 ≤ 10) (le_trans (le_max_left _ _) hM₂)
  have hne₁ := (LFunction_ne_zero_of_periodicEuler_beats_tail hq hχ
    (2 * q * M₁ + q - 1) hM₁_pos (by linarith)).1 hb₁
  have hne₂ := (LFunction_ne_zero_of_periodicEuler_beats_tail (q := q * 3) (by omega) hbc
    (2 * (q * 3) * M₂ + (q * 3) - 1) hM₂_pos (by linarith)).1 hb₂
  rw [hprod]
  exact ⟨mul_ne_zero hne₁ hne₂, ⟨M₁, hM₁, hb₁⟩, ⟨M₂, hM₂, hb₂⟩⟩

/-- **Unconditional special-locus Möbius gauge-exponent confinement (`TheSpecialLocusReadsGRH` +
`SubSevenEighthsZeroFreeHalfPlane`):** for every primitive nonprincipal `χ : DirichletCharacter ℂ q`
and every vertical shift `t : ℝ`, both `zeroAbscissa χ` and
`gaugeExponent moebiusSource (dirichletGauge χ + verticalShift t)` lie in `[1/2, 20999/24000]`. -/
theorem gaugeExponent_moebius_dirichletGauge_le_sub_seven_eighths {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1) (hprim : χ.IsPrimitive) (t : ℝ) :
    (1 / 2 : ℝ) ≤ _root_.RHTower.zeroAbscissa χ ∧
    _root_.RHTower.zeroAbscissa χ ≤ 20999 / 24000 ∧
    gaugeExponent moebiusSource (dirichletGauge χ + verticalShift t) ∈
      Set.Icc (1 / 2 : ℝ) (20999 / 24000) := by
  have hlo : (1 / 2 : ℝ) ≤ _root_.RHTower.zeroAbscissa χ :=
    _root_.RHTower.half_le_zeroAbscissa hχ hprim
  have hhi : _root_.RHTower.zeroAbscissa χ ≤ 20999 / 24000 := by
    refine csSup_le (_root_.RHTower.zeroReSet_nonempty hχ hprim) fun x hx => ?_
    obtain ⟨ρ, hzero, rfl⟩ := hx
    by_contra hgt
    exact DirichletCharacter.LFunction_ne_zero_of_sub_seven_eighths_lt_re
      χ (lt_of_not_ge hgt) (fun h => hχ h.1) hzero
  have hgauge := gaugeExponent_moebius_dirichletGauge_verticalShift hχ hprim t
  exact ⟨hlo, hhi, by rw [hgauge]; exact ⟨hlo, hhi⟩⟩

end HeckeAndSpecialLocus

/-! ### 4. Twisted Prime-Gas Occupation Identities (`μ χ ⋆ χ = 1`, `λ χ ⋆ χ = χ² · 1_□`) -/

/-- **Exact zero-tail twisted Möbius identity (`∀ q, ∀ χ, ∀ X ≥ 1, ∀ z ∈ ℂ`):**
`∑_{d=1}^X μ(d) χ(d) d^{-z} · charPartialSum χ z ⌊X / d⌋ = 1` identically with zero truncation tail. -/
theorem sum_twistedMoebius_mul_charPartialSum_eq_one {q : ℕ} (χ : DirichletCharacter ℂ q)
    {X : ℕ} (hX : 1 ≤ X) (z : ℂ) :
    (∑ d ∈ Finset.Icc 1 X,
        (ArithmeticFunction.moebius d : ℂ) * χ d * (d : ℂ) ^ (-z) * charPartialSum χ z (X / d)) =
      1 := by
  unfold charPartialSum
  have hexpand : (∑ d ∈ Finset.Icc 1 X,
        (ArithmeticFunction.moebius d : ℂ) * χ d * (d : ℂ) ^ (-z) *
          ∑ m ∈ Finset.Icc 1 (X / d), χ m * (m : ℂ) ^ (-z)) =
      ∑ p ∈ (Finset.Icc 1 X).sigma (fun d => Finset.Icc 1 (X / d)),
        (ArithmeticFunction.moebius p.1 : ℂ) * χ (p.1 * p.2 : ℕ) *
          ((p.1 * p.2 : ℕ) : ℂ) ^ (-z) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hmul : (d : ℂ) ^ (-z) * (m : ℂ) ^ (-z) = ((d * m : ℕ) : ℂ) ^ (-z) := by
      rw [show ((d * m : ℕ) : ℂ) = ((d : ℝ) : ℂ) * ((m : ℝ) : ℂ) by push_cast; ring,
        Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg m)]
      norm_cast
    have hchar : χ (d : ZMod q) * χ (m : ZMod q) = χ ((d * m : ℕ) : ZMod q) := by
      rw [Nat.cast_mul, map_mul]
    calc (ArithmeticFunction.moebius d : ℂ) * χ d * (d : ℂ) ^ (-z) * (χ m * (m : ℂ) ^ (-z))
        = (ArithmeticFunction.moebius d : ℂ) * (χ d * χ m) * ((d : ℂ) ^ (-z) * (m : ℂ) ^ (-z)) := by
          ring
      _ = (ArithmeticFunction.moebius d : ℂ) * χ (d * m : ℕ) * ((d * m : ℕ) : ℂ) ^ (-z) := by
          rw [hchar, hmul]
  have hbij : (∑ p ∈ (Finset.Icc 1 X).sigma (fun d => Finset.Icc 1 (X / d)),
        (ArithmeticFunction.moebius p.1 : ℂ) * χ (p.1 * p.2 : ℕ) *
          ((p.1 * p.2 : ℕ) : ℂ) ^ (-z)) =
      ∑ r ∈ (Finset.Icc 1 X).sigma (fun n => n.divisors),
        (ArithmeticFunction.moebius r.2 : ℂ) * (χ r.1 * (r.1 : ℂ) ^ (-z)) := by
    refine Finset.sum_bij (fun p _ => ⟨p.1 * p.2, p.1⟩) ?_ ?_ ?_ ?_
    · rintro ⟨d, m⟩ hp
      obtain ⟨hd, hm⟩ := Finset.mem_sigma.mp hp
      obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
      obtain ⟨hm1, hmX⟩ := Finset.mem_Icc.mp hm
      have hdm_le : d * m ≤ X := by
        rw [mul_comm]; exact (Nat.le_div_iff_mul_le hd1).mp hmX
      have hdm_pos : 1 ≤ d * m := Nat.mul_pos hd1 hm1
      exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hdm_pos, hdm_le⟩,
        Nat.mem_divisors.mpr ⟨dvd_mul_right d m, Nat.ne_of_gt hdm_pos⟩⟩
    · rintro ⟨d₁, m₁⟩ hp₁ ⟨d₂, m₂⟩ _ heq
      obtain ⟨hd₁, _⟩ := Finset.mem_sigma.mp hp₁
      have hd₁_pos : 0 < d₁ := (Finset.mem_Icc.mp hd₁).1
      injection heq with hprod hd_eq
      subst hd_eq
      have hm_eq : m₁ = m₂ := Nat.eq_of_mul_eq_mul_left hd₁_pos hprod
      subst hm_eq; rfl
    · rintro ⟨n, d⟩ hr
      obtain ⟨hn, hd_div⟩ := Finset.mem_sigma.mp hr
      obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.mp hn
      obtain ⟨⟨m, hm_eq⟩, _⟩ := Nat.mem_divisors.mp hd_div
      change n = d * m at hm_eq
      change 1 ≤ n at hn1
      change n ≤ X at hnX
      subst hm_eq
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos (dvd_mul_right d m) hn1
      have hm1 : 1 ≤ m := Nat.pos_of_dvd_of_pos (dvd_mul_left m d) hn1
      have hm_le : m ≤ X / d := (Nat.le_div_iff_mul_le hd1).mpr (by rwa [mul_comm])
      exact ⟨⟨d, m⟩, Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hd1, by nlinarith⟩,
        Finset.mem_Icc.mpr ⟨hm1, hm_le⟩⟩, rfl⟩
    · rintro ⟨d, m⟩ _
      change (ArithmeticFunction.moebius d : ℂ) * χ (d * m : ℕ) * ((d * m : ℕ) : ℂ) ^ (-z) =
        (ArithmeticFunction.moebius d : ℂ) * (χ (d * m : ℕ) * ((d * m : ℕ) : ℂ) ^ (-z))
      ring
  rw [hexpand, hbij, Finset.sum_sigma]
  rw [Finset.sum_eq_single 1]
  · simp [Nat.cast_one, map_one]
  · intro n _ hn1
    dsimp only
    rw [← Finset.sum_mul]
    have hzero_int : (∑ d ∈ n.divisors, ArithmeticFunction.moebius d) = 0 := by
      have hconv := congrArg (fun f : ArithmeticFunction ℤ => f n)
        ArithmeticFunction.moebius_mul_coe_zeta
      rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply, if_neg hn1] at hconv
      exact hconv
    have hzero_c : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ)) = 0 := by
      exact_mod_cast hzero_int
    rw [hzero_c, zero_mul]
  · intro hnot
    exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hX⟩) hnot

/-- **Twisted multi-stride high-divisor forcing at any `χ.LFunction z = 0` (`∀ Im z ∈ ℝ`):**
for `2 ≤ q`, `χ ≠ 1`, `0 < Re z ≤ 1`, `10 ≤ M`, `|Im z| ≤ M`, and `(2 q M + q - 1) D ≤ X₀`,
`multiStrideMean q (List.range' 1 D) M` drives the first `D` twisted Möbius channels below
`D q^3 / 2^{M / 2}` and forces the remaining `D < d ≤ Y` sum above `1 - D q^3 / 2^{M / 2}`. -/
theorem norm_multiStrideMean_twistedMoebius_highDivisors_ge_of_LFunction_eq_zero
    {q : ℕ} [NeZero q] (hq : 2 ≤ q) {χ : DirichletCharacter ℂ q} (hχ : χ ≠ 1)
    {z : ℂ} (hz0 : 0 < z.re) (hz1 : z.re ≤ 1) (hzz : χ.LFunction z = 0)
    {D M X₀ : ℕ} (hD : 1 ≤ D) (hM10 : 10 ≤ M) (him : |z.im| ≤ (M : ℝ))
    (hX₀ : (2 * q * M + q - 1) * D ≤ X₀) :
    1 - (D : ℝ) * (q : ℝ) ^ 3 / (2 : ℝ) ^ (M / 2) ≤
      ‖multiStrideMean q (List.range' 1 D) M
        (fun Y => ∑ d ∈ Finset.Icc (D + 1) Y,
          (ArithmeticFunction.moebius d : ℂ) * χ d * (d : ℂ) ^ (-z) *
            charPartialSum χ z (Y / d)) X₀‖ := by
  have hN0_pos : 1 ≤ 2 * q * M + q - 1 := by
    have hqM : 2 ≤ 2 * q * M := by nlinarith
    omega
  have hD_le_X₀ : D ≤ X₀ := (Nat.le_mul_of_pos_left D hN0_pos).trans hX₀
  have hX₀1 : 1 ≤ X₀ := hD.trans hD_le_X₀
  set ds := List.range' 1 D
  set Low : ℕ → ℂ := fun Y => ∑ d ∈ Finset.Icc 1 D,
    (ArithmeticFunction.moebius d : ℂ) * χ d * (d : ℂ) ^ (-z) * charPartialSum χ z (Y / d)
  set High : ℕ → ℂ := fun Y => ∑ d ∈ Finset.Icc (D + 1) Y,
    (ArithmeticFunction.moebius d : ℂ) * χ d * (d : ℂ) ^ (-z) * charPartialSum χ z (Y / d)
  have hconst : multiStrideMean q ds M (fun Y => Low Y + High Y) X₀ = 1 := by
    have hcongr : multiStrideMean q ds M (fun Y => Low Y + High Y) X₀ =
        multiStrideMean q ds M (fun _ => (1 : ℂ)) X₀ := by
      refine multiStrideMean_congr_of_window (by omega) ds M fun Y hYlo _ => ?_
      have hDY : D ≤ Y := hD_le_X₀.trans hYlo
      have hunion : Finset.Icc 1 D ∪ Finset.Icc (D + 1) Y = Finset.Icc 1 Y := by
        ext d; simp only [Finset.mem_union, Finset.mem_Icc]; omega
      have hdisj : Disjoint (Finset.Icc 1 D) (Finset.Icc (D + 1) Y) := by
        rw [Finset.disjoint_left]; intro d h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
      dsimp only [Low, High]
      rw [← Finset.sum_union hdisj, hunion]
      exact sum_twistedMoebius_mul_charPartialSum_eq_one χ (hX₀1.trans hYlo) z
    have hconst_eval : multiStrideMean q ds M (fun _ => (1 : ℂ)) X₀ = 1 := by
      have h0 : ‖multiStrideMean q ds M (fun _ => (1 : ℂ)) X₀ - 1‖ ≤ 0 :=
        norm_multiStrideMean_sub_const_le_of_window (by omega) ds M _ _ fun _ _ _ => by simp
      exact sub_eq_zero.mp (norm_le_zero_iff.mp h0)
    rw [hcongr, hconst_eval]
  have hlow_le : ‖multiStrideMean q ds M Low X₀‖ ≤
      (D : ℝ) * (q : ℝ) ^ 3 / (2 : ℝ) ^ (M / 2) := by
    dsimp only [Low]
    rw [multiStrideMean_finset_sum]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ d ∈ Finset.Icc 1 D, ‖multiStrideMean q ds M
            (fun Y => (ArithmeticFunction.moebius d : ℂ) * χ d * (d : ℂ) ^ (-z) *
              charPartialSum χ z (Y / d)) X₀‖
        ≤ ∑ _d ∈ Finset.Icc 1 D, ((q : ℝ) ^ 3 / (2 : ℝ) ^ (M / 2)) := by
          refine Finset.sum_le_sum fun d hd => ?_
          obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
          have hrew : (fun Y => (ArithmeticFunction.moebius d : ℂ) * χ d * (d : ℂ) ^ (-z) *
                charPartialSum χ z (Y / d)) =
              fun Y => ((ArithmeticFunction.moebius d : ℂ) * χ d * (d : ℂ) ^ (-z)) *
                charPartialSum χ z (Y / d) := rfl
          rw [hrew, multiStrideMean_smul, norm_mul]
          have hcoef_le : ‖(ArithmeticFunction.moebius d : ℂ) * χ d * (d : ℂ) ^ (-z)‖ ≤ 1 := by
            rw [norm_mul, norm_mul, show (d : ℂ) = ((d : ℝ) : ℂ) by norm_cast,
              Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hd1), Complex.neg_re]
            have hm1 : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
              rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
              exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
            have hc1 : ‖χ d‖ ≤ 1 := χ.norm_le_one _
            have hr1 : (d : ℝ) ^ (-z.re) ≤ 1 :=
              Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hd1) (by linarith)
            have hp1 : ‖(ArithmeticFunction.moebius d : ℂ)‖ * ‖χ d‖ ≤ 1 :=
              mul_le_one₀ hm1 (norm_nonneg _) hc1
            exact mul_le_one₀ hp1 (Real.rpow_nonneg (Nat.cast_nonneg d) _) hr1
          have hmem : d ∈ ds := List.mem_range'.mpr ⟨d - 1, by omega, by omega⟩
          obtain ⟨rest, _, hpull⟩ := exists_multiStrideMean_pull_mem q hmem M
            (fun Y => charPartialSum χ z (Y / d))
          have herr_le : ‖multiStrideMean q ds M (fun Y => charPartialSum χ z (Y / d)) X₀‖ ≤
              (q : ℝ) ^ 3 / (2 : ℝ) ^ (M / 2) := by
            rw [hpull, iterate_strideMean_charPartialSum_div_eq hd1 χ M z]
            refine norm_multiStrideMean_le_of_window (by omega) rest M
              (fun Y => periodicEulerPartialSum χ (Y / d) M z) fun Y hYlo _ => ?_
            have hN0_le : 2 * q * M + q - 1 ≤ Y / d := by
              refine (Nat.le_div_iff_mul_le hd1).mpr ?_
              exact (Nat.mul_le_mul_left (2 * q * M + q - 1) hdD).trans (hX₀.trans hYlo)
            have hrpow_anti : periodicEulerTailBound q (Y / d) M z ≤
                periodicEulerTailBound q (2 * q * M + q - 1) M z := by
              unfold periodicEulerTailBound
              refine mul_le_mul_of_nonneg_left ?_ (by positivity)
              exact Real.rpow_le_rpow_of_nonpos
                (by positivity : 0 < ((2 * q * M + q - 1 : ℕ) : ℝ) + 1)
                (by exact_mod_cast Nat.add_le_add_right hN0_le 1)
                (by linarith [Nat.cast_nonneg (α := ℝ) M])
            exact ((LFunction_ne_zero_of_periodicEuler_beats_tail hq hχ (Y / d)
              (by omega) hz0).2 hzz).trans
              (hrpow_anti.trans ((periodicEulerTailBound_linear_le hq (by omega) hz0 hz1 him).2 hM10))
          calc ‖(ArithmeticFunction.moebius d : ℂ) * χ d * (d : ℂ) ^ (-z)‖ *
                ‖multiStrideMean q ds M (fun Y => charPartialSum χ z (Y / d)) X₀‖
              ≤ 1 * ((q : ℝ) ^ 3 / (2 : ℝ) ^ (M / 2)) :=
                mul_le_mul hcoef_le herr_le (norm_nonneg _) zero_le_one
            _ = (q : ℝ) ^ 3 / (2 : ℝ) ^ (M / 2) := one_mul _
      _ = (D : ℝ) * (q : ℝ) ^ 3 / (2 : ℝ) ^ (M / 2) := by
          rw [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]; ring
  have hsum_eq : multiStrideMean q ds M Low X₀ + multiStrideMean q ds M High X₀ = 1 := by
    rw [← congrFun (multiStrideMean_add q ds M Low High) X₀]
    exact hconst
  have htri := norm_add_le (multiStrideMean q ds M Low X₀) (multiStrideMean q ds M High X₀)
  rw [hsum_eq, norm_one] at htri
  linarith

/-- **Twisted Liouville square-sieve identity (`∀ q, ∀ χ, ∀ X, ∀ w`):**
`∑_{d=1}^X λ(d) χ(d) d^{-w} · charPartialSum χ w ⌊X / d⌋ = ∑_{k=1}^{⌊√X⌋} χ(k)^2 k^{-2w}`. -/
theorem sum_twistedLiouville_mul_charPartialSum_eq_squareCharHead
    {q : ℕ} (χ : DirichletCharacter ℂ q) (X : ℕ) (w : ℂ) :
    (∑ d ∈ Finset.Icc 1 X,
        _root_.RHTower.liouvilleC d * χ d * (d : ℂ) ^ (-w) * charPartialSum χ w (X / d)) =
      ∑ k ∈ Finset.Icc 1 (Nat.sqrt X), (χ k) ^ 2 * (k : ℂ) ^ (-(2 * w)) := by
  unfold charPartialSum
  have hexpand : (∑ d ∈ Finset.Icc 1 X,
        _root_.RHTower.liouvilleC d * χ d * (d : ℂ) ^ (-w) *
          ∑ m ∈ Finset.Icc 1 (X / d), χ m * (m : ℂ) ^ (-w)) =
      ∑ p ∈ (Finset.Icc 1 X).sigma (fun d => Finset.Icc 1 (X / d)),
        _root_.RHTower.liouvilleC p.1 * χ (p.1 * p.2 : ℕ) *
          ((p.1 * p.2 : ℕ) : ℂ) ^ (-w) := by
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun d _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    have hmul : (d : ℂ) ^ (-w) * (m : ℂ) ^ (-w) = ((d * m : ℕ) : ℂ) ^ (-w) := by
      rw [show ((d * m : ℕ) : ℂ) = ((d : ℝ) : ℂ) * ((m : ℝ) : ℂ) by push_cast; ring,
        Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg m)]
      norm_cast
    have hchar : χ (d : ZMod q) * χ (m : ZMod q) = χ ((d * m : ℕ) : ZMod q) := by
      rw [Nat.cast_mul, map_mul]
    calc _root_.RHTower.liouvilleC d * χ d * (d : ℂ) ^ (-w) * (χ m * (m : ℂ) ^ (-w))
        = _root_.RHTower.liouvilleC d * (χ d * χ m) * ((d : ℂ) ^ (-w) * (m : ℂ) ^ (-w)) := by
          ring
      _ = _root_.RHTower.liouvilleC d * χ (d * m : ℕ) * ((d * m : ℕ) : ℂ) ^ (-w) := by
          rw [hchar, hmul]
  have hbij : (∑ p ∈ (Finset.Icc 1 X).sigma (fun d => Finset.Icc 1 (X / d)),
        _root_.RHTower.liouvilleC p.1 * χ (p.1 * p.2 : ℕ) *
          ((p.1 * p.2 : ℕ) : ℂ) ^ (-w)) =
      ∑ r ∈ (Finset.Icc 1 X).sigma (fun n => n.divisors),
        _root_.RHTower.liouvilleC r.2 * (χ r.1 * (r.1 : ℂ) ^ (-w)) := by
    refine Finset.sum_bij (fun p _ => ⟨p.1 * p.2, p.1⟩) ?_ ?_ ?_ ?_
    · rintro ⟨d, m⟩ hp
      obtain ⟨hd, hm⟩ := Finset.mem_sigma.mp hp
      obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
      obtain ⟨hm1, hmX⟩ := Finset.mem_Icc.mp hm
      have hdm_le : d * m ≤ X := by
        rw [mul_comm]; exact (Nat.le_div_iff_mul_le hd1).mp hmX
      have hdm_pos : 1 ≤ d * m := Nat.mul_pos hd1 hm1
      exact Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hdm_pos, hdm_le⟩,
        Nat.mem_divisors.mpr ⟨dvd_mul_right d m, Nat.ne_of_gt hdm_pos⟩⟩
    · rintro ⟨d₁, m₁⟩ hp₁ ⟨d₂, m₂⟩ _ heq
      obtain ⟨hd₁, _⟩ := Finset.mem_sigma.mp hp₁
      have hd₁_pos : 0 < d₁ := (Finset.mem_Icc.mp hd₁).1
      injection heq with hprod hd_eq
      subst hd_eq
      have hm_eq : m₁ = m₂ := Nat.eq_of_mul_eq_mul_left hd₁_pos hprod
      subst hm_eq; rfl
    · rintro ⟨n, d⟩ hr
      obtain ⟨hn, hd_div⟩ := Finset.mem_sigma.mp hr
      obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.mp hn
      obtain ⟨⟨m, hm_eq⟩, _⟩ := Nat.mem_divisors.mp hd_div
      change n = d * m at hm_eq
      change 1 ≤ n at hn1
      change n ≤ X at hnX
      subst hm_eq
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos (dvd_mul_right d m) hn1
      have hm1 : 1 ≤ m := Nat.pos_of_dvd_of_pos (dvd_mul_left m d) hn1
      have hm_le : m ≤ X / d := (Nat.le_div_iff_mul_le hd1).mpr (by rwa [mul_comm])
      exact ⟨⟨d, m⟩, Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hd1, by nlinarith⟩,
        Finset.mem_Icc.mpr ⟨hm1, hm_le⟩⟩, rfl⟩
    · rintro ⟨d, m⟩ _
      change _root_.RHTower.liouvilleC d * χ (d * m : ℕ) * ((d * m : ℕ) : ℂ) ^ (-w) =
        _root_.RHTower.liouvilleC d * (χ (d * m : ℕ) * ((d * m : ℕ) : ℂ) ^ (-w))
      ring
  have hdiv_sum : (∑ r ∈ (Finset.Icc 1 X).sigma (fun n => n.divisors),
        _root_.RHTower.liouvilleC r.2 * (χ r.1 * (r.1 : ℂ) ^ (-w))) =
      ∑ n ∈ (Finset.Icc 1 X).filter IsSquare, χ n * (n : ℂ) ^ (-w) := by
    rw [Finset.sum_sigma, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    dsimp only
    obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
    rw [← Finset.sum_mul, _root_.RHTower.sum_divisors_liouvilleC (by omega : n ≠ 0),
      _root_.RHTower.squareIndicator]
    split_ifs <;> simp
  have hsq_bij : (∑ n ∈ (Finset.Icc 1 X).filter IsSquare, χ n * (n : ℂ) ^ (-w)) =
      ∑ k ∈ Finset.Icc 1 (Nat.sqrt X), (χ k) ^ 2 * (k : ℂ) ^ (-(2 * w)) := by
    symm
    refine Finset.sum_bij (fun k _ => k * k) ?_ ?_ ?_ ?_
    · intro k hk
      obtain ⟨hk1, hksq⟩ := Finset.mem_Icc.mp hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.mul_pos hk1 hk1,
        Nat.le_sqrt.mp hksq⟩, ⟨k, rfl⟩⟩
    · intro k₁ _ k₂ _ heq
      exact Nat.mul_self_inj.mp heq
    · intro n hn
      obtain ⟨hn_lu, ⟨k, rfl⟩⟩ := Finset.mem_filter.mp hn
      obtain ⟨hn1, hnX⟩ := Finset.mem_Icc.mp hn_lu
      have hk1 : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with rfl | hkpos
        · simp at hn1
        · exact hkpos
      exact ⟨k, Finset.mem_Icc.mpr ⟨hk1, Nat.le_sqrt.mpr hnX⟩, rfl⟩
    · intro k hk
      obtain ⟨hk1, _⟩ := Finset.mem_Icc.mp hk
      have hk_ne : (k : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
      have hmul : ((k * k : ℕ) : ℂ) ^ (-w) = (k : ℂ) ^ (-w) * (k : ℂ) ^ (-w) := by
        rw [show ((k * k : ℕ) : ℂ) = ((k : ℝ) : ℂ) * ((k : ℝ) : ℂ) by push_cast; ring,
          Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg k) (Nat.cast_nonneg k)]
        norm_cast
      have hchar : χ ((k * k : ℕ) : ZMod q) = (χ (k : ZMod q)) ^ 2 := by
        rw [Nat.cast_mul, map_mul, sq]
      rw [hchar, hmul, show -(2 * w) = (-w) + (-w) by ring, Complex.cpow_add _ _ hk_ne]
  rw [hexpand, hbij, hdiv_sum, hsq_bij]

/-- **Height-independent quadratic double-energy floor (`∀ Im s ∈ ℝ`):** for every quadratic
Dirichlet character `χ : DirichletCharacter ℂ q` (`χ ^ 2 = 1`, e.g. `χ_{-3}` of `ℚ(ω)` or any
Kronecker symbol) and every `0 < Re s < 1/2`, `‖(χ ^ 2).LFunction (2(1 - conj s))‖` is bounded
below uniformly across all heights by `(∏_{p ∣ q} (1 - p⁻¹)) (1 - 2 Re s) / (2 - 2 Re s) > 0`. -/
theorem norm_quadratic_LFunction_two_mul_refl_ge {q : ℕ} [NeZero q]
    {χ : DirichletCharacter ℂ q} (hquad : χ ^ 2 = 1)
    {s : ℂ} (h0 : 0 < s.re) (hhi : s.re < 1 / 2) :
    0 < (∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹)) * ((1 - 2 * s.re) / (2 - 2 * s.re)) ∧
    (∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹)) * ((1 - 2 * s.re) / (2 - 2 * s.re)) ≤
      ‖(χ ^ 2).LFunction (2 * (1 - conj s))‖ := by
  set z : ℂ := 2 * (1 - conj s)
  have hz_re : z.re = 2 - 2 * s.re := by simp [z, Complex.mul_re]; ring
  have hz_gt1 : 1 < z.re := by rw [hz_re]; linarith
  have hz_ne1 : z ≠ 1 := fun h => hz_gt1.ne' (by rw [h, Complex.one_re])
  have hp_pos : ∀ p ∈ q.primeFactors, 0 < 1 - (p : ℝ)⁻¹ := by
    intro p hp
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.two_le
    have hinv : (p : ℝ)⁻¹ ≤ (1 / 2 : ℝ) := by
      rw [one_div]; exact inv_anti₀ zero_lt_two hp2
    linarith
  have hprod_pos : 0 < ∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹) :=
    Finset.prod_pos hp_pos
  have hzeta_floor_pos : 0 < (1 - 2 * s.re) / (2 - 2 * s.re) :=
    div_pos (by linarith) (by linarith)
  refine ⟨mul_pos hprod_pos hzeta_floor_pos, ?_⟩
  rw [hquad]
  change _ ≤ ‖DirichletCharacter.LFunctionTrivChar q z‖
  rw [DirichletCharacter.LFunctionTrivChar_eq_mul_riemannZeta hz_ne1, norm_mul, norm_prod]
  have heuler_ge : (∏ p ∈ q.primeFactors, (1 - (p : ℝ)⁻¹)) ≤
      ∏ p ∈ q.primeFactors, ‖1 - (p : ℂ) ^ (-z)‖ := by
    refine Finset.prod_le_prod (fun p hp => (hp_pos p hp).le) fun p hp => ?_
    have hpr := Nat.prime_of_mem_primeFactors hp
    have hp_pos_r : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hpr.pos
    have hp_ge1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpr.one_le
    have hp_cpow : ‖(p : ℂ) ^ (-z)‖ ≤ (p : ℝ)⁻¹ := by
      rw [show (p : ℂ) = ((p : ℝ) : ℂ) by norm_cast,
        Complex.norm_cpow_eq_rpow_re_of_pos hp_pos_r, Complex.neg_re, hz_re,
        ← Real.rpow_neg_one]
      exact Real.rpow_le_rpow_of_exponent_le hp_ge1 (by linarith)
    have htri := norm_sub_norm_le (1 : ℂ) ((p : ℂ) ^ (-z))
    rw [norm_one] at htri
    linarith
  have hzeta_ne : riemannZeta z ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hz_gt1
  have hzeta_pos : 0 < ‖riemannZeta z‖ := norm_pos_iff.mpr hzeta_ne
  have hinv := _root_.RHTower.norm_inv_riemannZeta_le_of_le_re hz_gt1 (s := z) le_rfl
  rw [norm_inv, hz_re, show (2 - 2 * s.re - 1 : ℝ) = 1 - 2 * s.re by ring] at hinv
  have hzeta_ge : (1 - 2 * s.re) / (2 - 2 * s.re) ≤ ‖riemannZeta z‖ := by
    have hsimp : 1 + 1 / (1 - 2 * s.re) = (2 - 2 * s.re) / (1 - 2 * s.re) := by
      field_simp [show (1 - 2 * s.re : ℝ) ≠ 0 by linarith]; ring
    rw [hsimp] at hinv
    rw [div_le_iff₀ (by linarith : 0 < 2 - 2 * s.re)]
    have h1 := (inv_le_iff_one_le_mul₀' hzeta_pos).mp hinv
    rw [mul_div_assoc'] at h1
    simpa only [one_mul] using (le_div_iff₀ (by linarith : 0 < 1 - 2 * s.re)).mp h1
  exact mul_le_mul heuler_ge hzeta_ge hzeta_floor_pos.le
    (Finset.prod_nonneg fun _ _ => norm_nonneg _)

/-! ### 5. Exact Vaughan `typeIIShort` Factorization and All-Height Power Cancellation Beyond `3001/24000` -/

/-- Truncated twisted Möbius polynomial `M_{D, χ}(w) = ∑_{d=1}^D μ(d) χ(d) d^{-w}`. -/
def moebiusCharPoly {q : ℕ} (χ : DirichletCharacter ℂ q) (D : ℕ) (w : ℂ) : ℂ :=
  ∑ d ∈ Finset.Icc 1 D, (ArithmeticFunction.moebius d : ℂ) * χ d * (d : ℂ) ^ (-w)

/-- Convolution coefficient of `moebiusCharPoly χ D w * periodicEulerPartialSum χ N M w`:
agrees with `-RHTower.Sieve.typeIIShort D n` on `(D, N]` and vanishes on `[2, D]`. -/
def vaughanEulerCoeff (q D N M n : ℕ) : ℝ :=
  ∑ d ∈ n.divisors.filter (· ≤ D),
    (ArithmeticFunction.moebius d : ℝ) * periodicEulerWeight q N M (n / d)

/-- Defect separating `M_{D, χ}(w) · periodicEulerPartialSum χ N M w` from `1`. -/
def vaughanEulerDefect {q : ℕ} (χ : DirichletCharacter ℂ q) (D N M : ℕ) (w : ℂ) : ℂ :=
  1 - moebiusCharPoly χ D w * periodicEulerPartialSum χ N M w

lemma vaughanEulerCoeff_eq_ite_sub_typeIIShort_of_le {q D N M n : ℕ}
    (hq : 1 ≤ q) (hn1 : 1 ≤ n) (hnN : n ≤ N) :
    vaughanEulerCoeff q D N M n =
      (if n = 1 then 1 else 0) - _root_.RHTower.Sieve.typeIIShort D n := by
  rw [GaloisForLFunctions.BezoutValuationIncidence.typeIIShort_eq_ite_sub_sieveSeq D hn1]
  have hsieve : vaughanEulerCoeff q D N M n =
      GaloisForLFunctions.BezoutValuationIncidence.sieveSeq D
        GaloisForLFunctions.BezoutValuationIncidence.moebiusReal n := by
    unfold vaughanEulerCoeff GaloisForLFunctions.BezoutValuationIncidence.sieveSeq
    rw [GaloisForLFunctions.BezoutValuationIncidence.filter_dvd_Icc_eq_divisors_filter_le D hn1]
    refine Finset.sum_congr rfl fun d hd => ?_
    obtain ⟨hd_div, _⟩ := Finset.mem_filter.mp hd
    obtain ⟨⟨m, hm_eq⟩, _⟩ := Nat.mem_divisors.mp hd_div
    have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos ⟨m, hm_eq⟩ hn1
    have hm1 : 1 ≤ n / d := Nat.div_pos (Nat.le_of_dvd hn1 ⟨m, hm_eq⟩) hd1
    have hmN : n / d ≤ N := (Nat.div_le_self n d).trans hnN
    rw [periodicEulerWeight_eq_one_of_le hq hm1 hmN, mul_one]
    rfl
  rw [hsieve]
  ring

lemma abs_vaughanEulerCoeff_le_divisors_card {q D N M n : ℕ} (hq : 1 ≤ q) :
    |vaughanEulerCoeff q D N M n| ≤ (n.divisors.card : ℝ) := by
  unfold vaughanEulerCoeff
  calc |∑ d ∈ n.divisors.filter (· ≤ D),
          (ArithmeticFunction.moebius d : ℝ) * periodicEulerWeight q N M (n / d)|
      ≤ ∑ d ∈ n.divisors.filter (· ≤ D),
          |(ArithmeticFunction.moebius d : ℝ) * periodicEulerWeight q N M (n / d)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _d ∈ n.divisors.filter (· ≤ D), (1 : ℝ) := by
        refine Finset.sum_le_sum fun d _ => ?_
        rw [abs_mul, abs_of_nonneg (periodicEulerWeight_nonneg q N M (n / d))]
        have hm1 : |(ArithmeticFunction.moebius d : ℝ)| ≤ 1 := by
          exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
        exact mul_le_one₀ hm1 (periodicEulerWeight_nonneg q N M (n / d))
          (periodicEulerWeight_le_one hq N M (n / d))
    _ = ((n.divisors.filter (· ≤ D)).card : ℝ) := by simp
    _ ≤ (n.divisors.card : ℝ) := by exact_mod_cast Finset.card_filter_le _ _

/-- **Exact Vaughan `typeIIShort` factorization of `vaughanEulerDefect`:** for `1 ≤ q` and
`1 ≤ D ≤ N`, `1 - M_{D, χ}(w) · periodicEulerPartialSum χ N M w` vanishes identically on `[1, D]`,
equals `∑_{n=D+1}^N typeIIShort D n · χ(n) n^{-w}` on `(D, N]`, and carries a finite tapered tail
on `(N, D(N + M(q - 1))]`. -/
theorem vaughanEulerDefect_eq_typeIIShort_sub_tail {q D N M : ℕ}
    (hq : 1 ≤ q) (hD : 1 ≤ D) (hDN : D ≤ N) (χ : DirichletCharacter ℂ q) (w : ℂ) :
    vaughanEulerDefect χ D N M w =
      (∑ n ∈ Finset.Icc (D + 1) (D * (N + M * (q - 1))),
        -(vaughanEulerCoeff q D N M n : ℂ) * (n : ℂ) ^ (-w) * χ n) ∧
    vaughanEulerDefect χ D N M w =
      (∑ n ∈ Finset.Icc (D + 1) N,
        (_root_.RHTower.Sieve.typeIIShort D n : ℂ) * χ n * (n : ℂ) ^ (-w)) -
      ∑ n ∈ Finset.Icc (N + 1) (D * (N + M * (q - 1))),
        (vaughanEulerCoeff q D N M n : ℂ) * χ n * (n : ℂ) ^ (-w) := by
  set K : ℕ := N + M * (q - 1)
  have hprod_eq : moebiusCharPoly χ D w * periodicEulerPartialSum χ N M w =
      ∑ n ∈ Finset.Icc 1 (D * K), (vaughanEulerCoeff q D N M n : ℂ) * χ n * (n : ℂ) ^ (-w) := by
    unfold moebiusCharPoly
    rw [periodicEulerPartialSum_eq_sum_weights hq χ N M w]
    have hlhs : (∑ d ∈ Finset.Icc 1 D, (ArithmeticFunction.moebius d : ℂ) * χ d * (d : ℂ) ^ (-w)) *
          (∑ m ∈ Finset.Icc 1 K, (periodicEulerWeight q N M m : ℂ) * χ m * (m : ℂ) ^ (-w)) =
        ∑ p ∈ Finset.Icc 1 D ×ˢ Finset.Icc 1 K,
          ((ArithmeticFunction.moebius p.1 : ℂ) * (periodicEulerWeight q N M p.2 : ℂ)) *
            (χ (p.1 * p.2 : ℕ) * ((p.1 * p.2 : ℕ) : ℂ) ^ (-w)) := by
      rw [Finset.sum_mul_sum, ← Finset.sum_product']
      refine Finset.sum_congr rfl fun ⟨d, m⟩ _ => ?_
      have hmul : (d : ℂ) ^ (-w) * (m : ℂ) ^ (-w) = ((d * m : ℕ) : ℂ) ^ (-w) := by
        rw [show ((d * m : ℕ) : ℂ) = ((d : ℝ) : ℂ) * ((m : ℝ) : ℂ) by push_cast; ring,
          Complex.mul_cpow_ofReal_nonneg (Nat.cast_nonneg d) (Nat.cast_nonneg m)]
        norm_cast
      have hchar : χ (d : ZMod q) * χ (m : ZMod q) = χ ((d * m : ℕ) : ZMod q) := by
        rw [Nat.cast_mul, map_mul]
      calc ((ArithmeticFunction.moebius d : ℂ) * χ d * (d : ℂ) ^ (-w)) *
            ((periodicEulerWeight q N M m : ℂ) * χ m * (m : ℂ) ^ (-w))
          = ((ArithmeticFunction.moebius d : ℂ) * (periodicEulerWeight q N M m : ℂ)) *
              ((χ d * χ m) * ((d : ℂ) ^ (-w) * (m : ℂ) ^ (-w))) := by ring
        _ = ((ArithmeticFunction.moebius d : ℂ) * (periodicEulerWeight q N M m : ℂ)) *
              (χ (d * m : ℕ) * ((d * m : ℕ) : ℂ) ^ (-w)) := by rw [hchar, hmul]
    have hrhs : (∑ n ∈ Finset.Icc 1 (D * K),
          (vaughanEulerCoeff q D N M n : ℂ) * χ n * (n : ℂ) ^ (-w)) =
        ∑ r ∈ ((Finset.Icc 1 (D * K)).sigma (fun n => n.divisors.filter (· ≤ D))).filter
            (fun r => r.1 / r.2 ≤ K),
          ((ArithmeticFunction.moebius r.2 : ℂ) * (periodicEulerWeight q N M (r.1 / r.2) : ℂ)) *
            (χ r.1 * (r.1 : ℂ) ^ (-w)) := by
      rw [Finset.sum_filter, Finset.sum_sigma]
      refine Finset.sum_congr rfl fun n _ => ?_
      dsimp only
      unfold vaughanEulerCoeff
      push_cast
      rw [Finset.sum_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl fun d _ => ?_
      by_cases hle : n / d ≤ K
      · rw [if_pos hle]; ring
      · rw [if_neg hle, periodicEulerWeight_eq_zero_of_gt hq (by omega : K < n / d)]
        simp
    rw [hlhs, hrhs]
    refine Finset.sum_bij (fun p _ => ⟨p.1 * p.2, p.1⟩) ?_ ?_ ?_ ?_
    · rintro ⟨d, m⟩ hp
      obtain ⟨hd, hm⟩ := Finset.mem_product.mp hp
      obtain ⟨hd1, hdD⟩ := Finset.mem_Icc.mp hd
      obtain ⟨hm1, hmK⟩ := Finset.mem_Icc.mp hm
      have hpos : 1 ≤ d * m := Nat.mul_pos hd1 hm1
      have hle : d * m ≤ D * K := Nat.mul_le_mul hdD hmK
      refine Finset.mem_filter.mpr ⟨Finset.mem_sigma.mpr ⟨Finset.mem_Icc.mpr ⟨hpos, hle⟩,
        Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_mul_right d m, Nat.ne_of_gt hpos⟩, hdD⟩⟩, ?_⟩
      dsimp only
      rwa [Nat.mul_div_cancel_left m hd1]
    · rintro ⟨d₁, m₁⟩ hp₁ ⟨d₂, m₂⟩ _ heq
      have hd₁_pos : 0 < d₁ := (Finset.mem_Icc.mp (Finset.mem_product.mp hp₁).1).1
      injection heq with hprod hd_eq
      subst hd_eq
      have hm_eq : m₁ = m₂ := Nat.eq_of_mul_eq_mul_left hd₁_pos hprod
      subst hm_eq; rfl
    · rintro ⟨n, d⟩ hr
      obtain ⟨hr_sig, hmK⟩ := Finset.mem_filter.mp hr
      obtain ⟨hn, hd_flt⟩ := Finset.mem_sigma.mp hr_sig
      obtain ⟨hn1, _⟩ := Finset.mem_Icc.mp hn
      obtain ⟨hd_div, hdD⟩ := Finset.mem_filter.mp hd_flt
      obtain ⟨⟨m, hm_eq⟩, _⟩ := Nat.mem_divisors.mp hd_div
      change n = d * m at hm_eq
      change 1 ≤ n at hn1
      change n / d ≤ K at hmK
      subst hm_eq
      have hd1 : 1 ≤ d := Nat.pos_of_dvd_of_pos (dvd_mul_right d m) hn1
      have hm1 : 1 ≤ m := Nat.pos_of_dvd_of_pos (dvd_mul_left m d) hn1
      rw [Nat.mul_div_cancel_left m hd1] at hmK
      exact ⟨(d, m), Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hd1, hdD⟩,
        Finset.mem_Icc.mpr ⟨hm1, hmK⟩⟩, rfl⟩
    · rintro ⟨d, m⟩ hp
      have hd1 : 0 < d := (Finset.mem_Icc.mp (Finset.mem_product.mp hp).1).1
      dsimp only
      rw [Nat.mul_div_cancel_left m hd1]
  have hD_le_DK : D ≤ D * K := by
    have h1K : 1 ≤ K := by dsimp [K]; omega
    exact Nat.le_mul_of_pos_right D h1K
  have hN_le_DK : N ≤ D * K := by
    have hNK : N ≤ K := by dsimp [K]; omega
    exact hNK.trans (Nat.le_mul_of_pos_left K hD)
  have hhead_eq_one : (∑ n ∈ Finset.Icc 1 D,
        (vaughanEulerCoeff q D N M n : ℂ) * χ n * (n : ℂ) ^ (-w)) = 1 := by
    rw [Finset.sum_eq_single 1]
    · rw [vaughanEulerCoeff_eq_ite_sub_typeIIShort_of_le hq le_rfl (by omega : 1 ≤ N),
        if_pos rfl, GaloisForLFunctions.BezoutValuationIncidence.typeIIShort_apply_eq_zero_of_le le_rfl hD]
      simp [Nat.cast_one, map_one]
    · intro n hn hn_ne1
      obtain ⟨hn1, hnD⟩ := Finset.mem_Icc.mp hn
      rw [vaughanEulerCoeff_eq_ite_sub_typeIIShort_of_le hq hn1 (hnD.trans hDN),
        if_neg hn_ne1,
        GaloisForLFunctions.BezoutValuationIncidence.typeIIShort_apply_eq_zero_of_le hn1 hnD]
      simp
    · intro hnot
      exact absurd (Finset.mem_Icc.mpr ⟨le_rfl, hD⟩) hnot
  have hsplit1 : Finset.Icc 1 (D * K) = Finset.Icc 1 D ∪ Finset.Icc (D + 1) (D * K) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj1 : Disjoint (Finset.Icc 1 D) (Finset.Icc (D + 1) (D * K)) := by
    rw [Finset.disjoint_left]; intro n h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
  have hdef1 : vaughanEulerDefect χ D N M w =
      ∑ n ∈ Finset.Icc (D + 1) (D * K),
        -(vaughanEulerCoeff q D N M n : ℂ) * (n : ℂ) ^ (-w) * χ n := by
    unfold vaughanEulerDefect
    rw [hprod_eq, hsplit1, Finset.sum_union hdisj1, hhead_eq_one, sub_add_eq_sub_sub, sub_self,
      zero_sub, ← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  refine ⟨hdef1, ?_⟩
  rw [hdef1]
  have hsplit2 : Finset.Icc (D + 1) (D * K) =
      Finset.Icc (D + 1) N ∪ Finset.Icc (N + 1) (D * K) := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_union]; omega
  have hdisj2 : Disjoint (Finset.Icc (D + 1) N) (Finset.Icc (N + 1) (D * K)) := by
    rw [Finset.disjoint_left]; intro n h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
  rw [hsplit2, Finset.sum_union hdisj2]
  have hmid : (∑ n ∈ Finset.Icc (D + 1) N,
        -(vaughanEulerCoeff q D N M n : ℂ) * (n : ℂ) ^ (-w) * χ n) =
      ∑ n ∈ Finset.Icc (D + 1) N,
        (_root_.RHTower.Sieve.typeIIShort D n : ℂ) * χ n * (n : ℂ) ^ (-w) := by
    refine Finset.sum_congr rfl fun n hn => ?_
    obtain ⟨hn_lo, hnN⟩ := Finset.mem_Icc.mp hn
    rw [vaughanEulerCoeff_eq_ite_sub_typeIIShort_of_le hq (by omega) hnN, if_neg (by omega)]
    push_cast
    ring
  have htail : (∑ n ∈ Finset.Icc (N + 1) (D * K),
        -(vaughanEulerCoeff q D N M n : ℂ) * (n : ℂ) ^ (-w) * χ n) =
      -∑ n ∈ Finset.Icc (N + 1) (D * K),
        (vaughanEulerCoeff q D N M n : ℂ) * χ n * (n : ℂ) ^ (-w) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun n _ => by ring
  rw [hmid, htail, sub_eq_add_neg]

private lemma sum_Ioc_divisors_sq_rpow_le_aux (B : ℕ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ (K A : ℕ), 1 ≤ A → B ≤ 2 ^ K * A →
      (∑ k ∈ Finset.Ioc A B, (k.divisors.card : ℝ) ^ (2 : ℕ) * (k : ℝ) ^ (-(1 + δ))) ≤
        2 * (∑ j ∈ Finset.range K, ((2 : ℝ) ^ (-δ)) ^ j) *
          (A : ℝ) ^ (-δ) * (_root_.RHTower.Sieve.invSum B) ^ (3 : ℕ) := by
  intro K
  induction K with
  | zero =>
    intro A _ hBA
    rw [pow_zero, one_mul] at hBA
    have hempty : Finset.Ioc A B = ∅ := by
      ext k; simp only [Finset.mem_Ioc, Finset.notMem_empty, iff_false]; omega
    rw [hempty, Finset.sum_empty, Finset.range_zero, Finset.sum_empty]
    simp
  | succ K ih =>
    intro A hA hBA
    have hA_pos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
    have hsplit : Finset.Ioc A B =
        Finset.Ioc A (min B (2 * A)) ∪ Finset.Ioc (min B (2 * A)) B := by
      ext k; simp only [Finset.mem_Ioc, Finset.mem_union]; omega
    have hdisj : Disjoint (Finset.Ioc A (min B (2 * A))) (Finset.Ioc (min B (2 * A)) B) := by
      rw [Finset.disjoint_left]; intro k h1 h2; rw [Finset.mem_Ioc] at h1 h2; omega
    rw [hsplit, Finset.sum_union hdisj]
    have hhead : (∑ k ∈ Finset.Ioc A (min B (2 * A)),
          (k.divisors.card : ℝ) ^ (2 : ℕ) * (k : ℝ) ^ (-(1 + δ))) ≤
        2 * (A : ℝ) ^ (-δ) * (_root_.RHTower.Sieve.invSum B) ^ (3 : ℕ) := by
      have hpt : ∀ k ∈ Finset.Ioc A (min B (2 * A)),
          (k.divisors.card : ℝ) ^ (2 : ℕ) * (k : ℝ) ^ (-(1 + δ)) ≤
            (A : ℝ) ^ (-(1 + δ)) * (k.divisors.card : ℝ) ^ (2 : ℕ) := by
        intro k hk
        obtain ⟨hkA, _⟩ := Finset.mem_Ioc.mp hk
        have hrpow : (k : ℝ) ^ (-(1 + δ)) ≤ (A : ℝ) ^ (-(1 + δ)) :=
          Real.rpow_le_rpow_of_nonpos hA_pos (by exact_mod_cast hkA.le) (by linarith)
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right hrpow (sq_nonneg _)
      refine (Finset.sum_le_sum hpt).trans ?_
      rw [← Finset.mul_sum]
      have hsub_sum : (∑ k ∈ Finset.Ioc A (min B (2 * A)), (k.divisors.card : ℝ) ^ (2 : ℕ)) ≤
          2 * (A : ℝ) * (_root_.RHTower.Sieve.invSum B) ^ (3 : ℕ) := by
        have hsub : Finset.Ioc A (min B (2 * A)) ⊆ Finset.Icc 1 (min B (2 * A)) := by
          intro k hk
          obtain ⟨hkA, hkM⟩ := Finset.mem_Ioc.mp hk
          exact Finset.mem_Icc.mpr ⟨by omega, hkM⟩
        have h1 := (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => sq_nonneg _).trans
          (_root_.RHTower.Sieve.sum_card_divisors_sq_le (min B (2 * A)))
        have hmin_r : ((min B (2 * A) : ℕ) : ℝ) ≤ 2 * (A : ℝ) := by
          exact_mod_cast min_le_right B (2 * A)
        have hinv_le : (_root_.RHTower.Sieve.invSum (min B (2 * A))) ^ (3 : ℕ) ≤
            (_root_.RHTower.Sieve.invSum B) ^ (3 : ℕ) :=
          pow_le_pow_left₀ (_root_.RHTower.Sieve.invSum_nonneg _)
            (_root_.RHTower.Sieve.invSum_mono (min_le_left B (2 * A))) 3
        exact h1.trans (mul_le_mul hmin_r hinv_le
          (pow_nonneg (_root_.RHTower.Sieve.invSum_nonneg _) 3) (by positivity))
      calc (A : ℝ) ^ (-(1 + δ)) *
            (∑ k ∈ Finset.Ioc A (min B (2 * A)), (k.divisors.card : ℝ) ^ (2 : ℕ))
          ≤ (A : ℝ) ^ (-(1 + δ)) * (2 * (A : ℝ) * (_root_.RHTower.Sieve.invSum B) ^ (3 : ℕ)) :=
            mul_le_mul_of_nonneg_left hsub_sum (Real.rpow_nonneg hA_pos.le _)
        _ = 2 * ((A : ℝ) ^ (-(1 + δ)) * (A : ℝ)) * (_root_.RHTower.Sieve.invSum B) ^ (3 : ℕ) := by ring
        _ = 2 * (A : ℝ) ^ (-δ) * (_root_.RHTower.Sieve.invSum B) ^ (3 : ℕ) := by
            rw [← Real.rpow_add_one hA_pos.ne']
            congr 2; ring
    have hrest : (∑ k ∈ Finset.Ioc (min B (2 * A)) B,
          (k.divisors.card : ℝ) ^ (2 : ℕ) * (k : ℝ) ^ (-(1 + δ))) ≤
        2 * (((2 : ℝ) ^ (-δ)) * ∑ j ∈ Finset.range K, ((2 : ℝ) ^ (-δ)) ^ j) *
          (A : ℝ) ^ (-δ) * (_root_.RHTower.Sieve.invSum B) ^ (3 : ℕ) := by
      by_cases hle : B ≤ 2 * A
      · rw [min_eq_left hle]
        simp only [Finset.Ioc_self, Finset.sum_empty]
        exact mul_nonneg (mul_nonneg (mul_nonneg zero_le_two
          (mul_nonneg (Real.rpow_nonneg zero_le_two _)
            (Finset.sum_nonneg fun _ _ => pow_nonneg (Real.rpow_nonneg zero_le_two _) _)))
          (Real.rpow_nonneg hA_pos.le _))
          (pow_nonneg (_root_.RHTower.Sieve.invSum_nonneg B) 3)
      · rw [min_eq_right (by omega : 2 * A ≤ B)]
        have hBA' : B ≤ 2 ^ K * (2 * A) := by
          calc B ≤ 2 ^ (K + 1) * A := hBA
            _ = 2 ^ K * (2 * A) := by rw [pow_succ]; ring
        have hih := ih (2 * A) (by omega) hBA'
        have hcast2A : ((2 * A : ℕ) : ℝ) ^ (-δ) = (2 : ℝ) ^ (-δ) * (A : ℝ) ^ (-δ) := by
          rw [Nat.cast_mul, Nat.cast_ofNat, Real.mul_rpow zero_le_two hA_pos.le]
        rw [hcast2A] at hih
        calc (∑ k ∈ Finset.Ioc (2 * A) B,
              (k.divisors.card : ℝ) ^ (2 : ℕ) * (k : ℝ) ^ (-(1 + δ)))
            ≤ 2 * (∑ j ∈ Finset.range K, ((2 : ℝ) ^ (-δ)) ^ j) *
                ((2 : ℝ) ^ (-δ) * (A : ℝ) ^ (-δ)) * (_root_.RHTower.Sieve.invSum B) ^ (3 : ℕ) := hih
          _ = 2 * (((2 : ℝ) ^ (-δ)) * ∑ j ∈ Finset.range K, ((2 : ℝ) ^ (-δ)) ^ j) *
                (A : ℝ) ^ (-δ) * (_root_.RHTower.Sieve.invSum B) ^ (3 : ℕ) := by ring
    have hgeom_succ : (∑ j ∈ Finset.range (K + 1), ((2 : ℝ) ^ (-δ)) ^ j) =
        1 + ((2 : ℝ) ^ (-δ)) * ∑ j ∈ Finset.range K, ((2 : ℝ) ^ (-δ)) ^ j := by
      rw [Finset.sum_range_succ', pow_zero, add_comm, Finset.mul_sum]
      congr 1
      exact Finset.sum_congr rfl fun j _ => pow_succ' ((2 : ℝ) ^ (-δ)) j
    rw [hgeom_succ]
    calc (∑ k ∈ Finset.Ioc A (min B (2 * A)),
            (k.divisors.card : ℝ) ^ (2 : ℕ) * (k : ℝ) ^ (-(1 + δ))) +
          (∑ k ∈ Finset.Ioc (min B (2 * A)) B,
            (k.divisors.card : ℝ) ^ (2 : ℕ) * (k : ℝ) ^ (-(1 + δ)))
        ≤ 2 * (A : ℝ) ^ (-δ) * (_root_.RHTower.Sieve.invSum B) ^ (3 : ℕ) +
            2 * (((2 : ℝ) ^ (-δ)) * ∑ j ∈ Finset.range K, ((2 : ℝ) ^ (-δ)) ^ j) *
              (A : ℝ) ^ (-δ) * (_root_.RHTower.Sieve.invSum B) ^ (3 : ℕ) :=
          add_le_add hhead hrest
      _ = 2 * (1 + ((2 : ℝ) ^ (-δ)) * ∑ j ∈ Finset.range K, ((2 : ℝ) ^ (-δ)) ^ j) *
            (A : ℝ) ^ (-δ) * (_root_.RHTower.Sieve.invSum B) ^ (3 : ℕ) := by ring

private lemma sum_Ioc_divisors_sq_rpow_le {A B : ℕ} (hA : 1 ≤ A) {δ : ℝ} (hδ : 0 < δ) :
    (∑ k ∈ Finset.Ioc A B, (k.divisors.card : ℝ) ^ (2 : ℕ) * (k : ℝ) ^ (-(1 + δ))) ≤
      (2 / (1 - (2 : ℝ) ^ (-δ))) * (A : ℝ) ^ (-δ) *
        (_root_.RHTower.Sieve.invSum B) ^ (3 : ℕ) := by
  have hBA : B ≤ 2 ^ B * A := by
    have h1 : B ≤ 2 ^ B := (Nat.lt_two_pow_self (n := B)).le
    exact h1.trans (Nat.le_mul_of_pos_right (2 ^ B) hA)
  have haux := sum_Ioc_divisors_sq_rpow_le_aux B hδ B A hA hBA
  set r : ℝ := (2 : ℝ) ^ (-δ)
  have hr_nonneg : 0 ≤ r := Real.rpow_nonneg zero_le_two _
  have hr_lt1 : r < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith)
  have hgeom : (∑ j ∈ Finset.range B, r ^ j) ≤ (1 - r)⁻¹ := by
    rw [geom_sum_eq hr_lt1.ne, div_le_iff_of_neg (by linarith : r - 1 < 0)]
    have hne : (1 : ℝ) - r ≠ 0 := by linarith
    have hm : (1 - r)⁻¹ * (r - 1) = -1 := by
      rw [show r - 1 = -(1 - r) by ring, mul_neg, inv_mul_cancel₀ hne]
    rw [hm]
    linarith [pow_nonneg hr_nonneg B]
  refine haux.trans ?_
  have hfac_nonneg : 0 ≤ (A : ℝ) ^ (-δ) * (_root_.RHTower.Sieve.invSum B) ^ (3 : ℕ) :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg A) _)
      (pow_nonneg (_root_.RHTower.Sieve.invSum_nonneg B) 3)
  calc 2 * (∑ j ∈ Finset.range B, r ^ j) * (A : ℝ) ^ (-δ) *
        (_root_.RHTower.Sieve.invSum B) ^ (3 : ℕ)
      = 2 * (∑ j ∈ Finset.range B, r ^ j) *
          ((A : ℝ) ^ (-δ) * (_root_.RHTower.Sieve.invSum B) ^ (3 : ℕ)) := by ring
    _ ≤ 2 * (1 - r)⁻¹ *
          ((A : ℝ) ^ (-δ) * (_root_.RHTower.Sieve.invSum B) ^ (3 : ℕ)) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hgeom zero_le_two) hfac_nonneg
    _ = (2 / (1 - r)) * (A : ℝ) ^ (-δ) * (_root_.RHTower.Sieve.invSum B) ^ (3 : ℕ) := by
        rw [div_eq_mul_inv]; ring

private lemma sum_Icc_ite_band_eq {α : Type*} [AddCommMonoid α] {A B N : ℕ}
    (hB : B ≤ N) (f : ℕ → α) :
    (∑ k ∈ Finset.Icc 1 N, if A + 1 ≤ k ∧ k ≤ B then f k else 0) =
      ∑ k ∈ Finset.Icc (A + 1) B, f k := by
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext k; simp only [Finset.mem_filter, Finset.mem_Icc]; omega

/-- **Character-family second-moment bound on `vaughanEulerDefect`:** splitting `(D, D(N + M(q - 1))]`
at `q` (`1 ≤ D ≤ q ≤ N`) separates the zero-off-diagonal regime `(D, q]` from `(q, L]` via
`RHTower.meanValue_charSum` and `sum_card_divisors_sq_le`. -/
theorem sum_normSq_vaughanEulerDefect_le {q D N M : ℕ}
    (hq : 2 ≤ q) (hD : 1 ≤ D) (hDq : D ≤ q) (hN : q ≤ N)
    {w : ℂ} (hw : (1 / 2 : ℝ) < w.re) :
    (∑ χ : DirichletCharacter ℂ q, ‖vaughanEulerDefect χ D N M w‖ ^ (2 : ℕ)) ≤
      (q.totient : ℝ) * (4 / (1 - (2 : ℝ) ^ (-(2 * w.re - 1)))) *
        (_root_.RHTower.Sieve.invSum (D * (N + M * (q - 1)))) ^ (3 : ℕ) *
        (2 * (D : ℝ) ^ (-(2 * w.re - 1)) +
          (((D * (N + M * (q - 1)) : ℕ) : ℝ) / (q : ℝ) + 1) * (q : ℝ) ^ (-(2 * w.re - 1))) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : q ≠ 0)
  have hδ : 0 < 2 * w.re - 1 := by linarith
  have hq_le_L : n + 1 ≤ D * (N + M * (n + 1 - 1)) := by
    have hNL : N ≤ D * (N + M * (n + 1 - 1)) :=
      (Nat.le_add_right N _).trans (Nat.le_mul_of_pos_left _ hD)
    exact hN.trans hNL
  let a : ℕ → ℂ := fun k => -(vaughanEulerCoeff (n + 1) D N M k : ℂ) * (k : ℂ) ^ (-w)
  let a₁ : ℕ → ℂ := fun k => if D + 1 ≤ k ∧ k ≤ n + 1 then a k else 0
  let a₂ : ℕ → ℂ := fun k => if (n + 1) + 1 ≤ k ∧ k ≤ D * (N + M * (n + 1 - 1)) then a k else 0
  have hnorm_a_sq : ∀ k : ℕ, 1 ≤ k →
      ‖a k‖ ^ (2 : ℕ) ≤ (k.divisors.card : ℝ) ^ (2 : ℕ) * (k : ℝ) ^ (-(1 + (2 * w.re - 1))) := by
    intro k hk1
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk1
    dsimp only [a]
    rw [norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      show (k : ℂ) = ((k : ℝ) : ℂ) by norm_cast,
      Complex.norm_cpow_eq_rpow_re_of_pos hk_pos, Complex.neg_re, mul_pow]
    have hc := abs_vaughanEulerCoeff_le_divisors_card (q := n + 1) (D := D) (N := N) (M := M)
      (n := k) (by omega)
    have hc_sq : |vaughanEulerCoeff (n + 1) D N M k| ^ (2 : ℕ) ≤ (k.divisors.card : ℝ) ^ (2 : ℕ) :=
      pow_le_pow_left₀ (abs_nonneg _) hc 2
    have hr_sq : ((k : ℝ) ^ (-w.re)) ^ (2 : ℕ) = (k : ℝ) ^ (-(1 + (2 * w.re - 1))) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hk_pos.le]
      congr 1; push_cast; ring
    rw [hr_sq]
    exact mul_le_mul_of_nonneg_right hc_sq (Real.rpow_nonneg hk_pos.le _)
  have hsplit_char : ∀ χ : DirichletCharacter ℂ (n + 1),
      vaughanEulerDefect χ D N M w =
        _root_.RHTower.charSum n (n + 1) a₁ χ +
          _root_.RHTower.charSum n (D * (N + M * (n + 1 - 1))) a₂ χ := by
    intro χ
    rw [(vaughanEulerDefect_eq_typeIIShort_sub_tail (by omega) hD (hDq.trans hN) χ w).1]
    have hsp : Finset.Icc (D + 1) (D * (N + M * (n + 1 - 1))) =
        Finset.Icc (D + 1) (n + 1) ∪ Finset.Icc ((n + 1) + 1) (D * (N + M * (n + 1 - 1))) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_union]; omega
    have hdj : Disjoint (Finset.Icc (D + 1) (n + 1))
        (Finset.Icc ((n + 1) + 1) (D * (N + M * (n + 1 - 1)))) := by
      rw [Finset.disjoint_left]; intro k h1 h2; rw [Finset.mem_Icc] at h1 h2; omega
    change (∑ k ∈ Finset.Icc (D + 1) (D * (N + M * (n + 1 - 1))), a k * χ k) = _
    rw [hsp, Finset.sum_union hdj]
    congr 1
    · unfold _root_.RHTower.charSum
      have hite : ∀ k : ℕ, a₁ k * χ k = if D + 1 ≤ k ∧ k ≤ n + 1 then a k * χ k else 0 := by
        intro k; dsimp only [a₁]; split_ifs <;> simp
      simp_rw [hite]
      exact (sum_Icc_ite_band_eq le_rfl (fun k => a k * χ k)).symm
    · unfold _root_.RHTower.charSum
      have hite : ∀ k : ℕ, a₂ k * χ k =
          if (n + 1) + 1 ≤ k ∧ k ≤ D * (N + M * (n + 1 - 1)) then a k * χ k else 0 := by
        intro k; dsimp only [a₂]; split_ifs <;> simp
      simp_rw [hite]
      exact (sum_Icc_ite_band_eq le_rfl (fun k => a k * χ k)).symm
  have hpt_sq : ∀ χ : DirichletCharacter ℂ (n + 1),
      ‖vaughanEulerDefect χ D N M w‖ ^ (2 : ℕ) ≤
        2 * ‖_root_.RHTower.charSum n (n + 1) a₁ χ‖ ^ (2 : ℕ) +
          2 * ‖_root_.RHTower.charSum n (D * (N + M * (n + 1 - 1))) a₂ χ‖ ^ (2 : ℕ) := by
    intro χ
    rw [hsplit_char χ]
    have htri := norm_add_le (_root_.RHTower.charSum n (n + 1) a₁ χ)
      (_root_.RHTower.charSum n (D * (N + M * (n + 1 - 1))) a₂ χ)
    nlinarith [norm_nonneg (_root_.RHTower.charSum n (n + 1) a₁ χ +
        _root_.RHTower.charSum n (D * (N + M * (n + 1 - 1))) a₂ χ),
      sq_nonneg (‖_root_.RHTower.charSum n (n + 1) a₁ χ‖ -
        ‖_root_.RHTower.charSum n (D * (N + M * (n + 1 - 1))) a₂ χ‖)]
  have hsum_le := Finset.sum_le_sum fun χ (_ : χ ∈ Finset.univ) => hpt_sq χ
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum_le
  have hmv₁ := _root_.RHTower.meanValue_charSum n (n + 1) a₁
  have hmv₂ := _root_.RHTower.meanValue_charSum n (D * (N + M * (n + 1 - 1))) a₂
  have hocc₁ : (((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ) + 1) = 2 := by
    rw [div_self (by positivity : ((n + 1 : ℕ) : ℝ) ≠ 0)]
    norm_num
  have hflt₁ : (∑ k ∈ (Finset.Icc 1 (n + 1)).filter
          (fun k : ℕ => IsUnit (Nat.cast k : ZMod (n + 1))),
        ‖a₁ k‖ ^ (2 : ℕ)) ≤
      (2 / (1 - (2 : ℝ) ^ (-(2 * w.re - 1)))) * (D : ℝ) ^ (-(2 * w.re - 1)) *
        (_root_.RHTower.Sieve.invSum (D * (N + M * (n + 1 - 1)))) ^ (3 : ℕ) := by
    have h1 : (∑ k ∈ (Finset.Icc 1 (n + 1)).filter
            (fun k : ℕ => IsUnit (Nat.cast k : ZMod (n + 1))),
          ‖a₁ k‖ ^ (2 : ℕ)) ≤
        ∑ k ∈ Finset.Ioc D (n + 1),
          (k.divisors.card : ℝ) ^ (2 : ℕ) * (k : ℝ) ^ (-(1 + (2 * w.re - 1))) := by
      have hite : ∀ k : ℕ, ‖a₁ k‖ ^ (2 : ℕ) =
          if D + 1 ≤ k ∧ k ≤ n + 1 then ‖a k‖ ^ (2 : ℕ) else 0 := by
        intro k; dsimp only [a₁]; split_ifs <;> simp
      have hIcc_Ioc : Finset.Icc (D + 1) (n + 1) = Finset.Ioc D (n + 1) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
      calc (∑ k ∈ (Finset.Icc 1 (n + 1)).filter
              (fun k : ℕ => IsUnit (Nat.cast k : ZMod (n + 1))),
              ‖a₁ k‖ ^ (2 : ℕ))
          ≤ ∑ k ∈ Finset.Icc 1 (n + 1), ‖a₁ k‖ ^ (2 : ℕ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
        _ = ∑ k ∈ Finset.Ioc D (n + 1), ‖a k‖ ^ (2 : ℕ) := by
            simp_rw [hite]
            rw [sum_Icc_ite_band_eq le_rfl (fun k => ‖a k‖ ^ (2 : ℕ)), hIcc_Ioc]
        _ ≤ ∑ k ∈ Finset.Ioc D (n + 1),
              (k.divisors.card : ℝ) ^ (2 : ℕ) * (k : ℝ) ^ (-(1 + (2 * w.re - 1))) :=
            Finset.sum_le_sum fun k hk => hnorm_a_sq k (by have := (Finset.mem_Ioc.mp hk).1; omega)
    refine h1.trans ((sum_Ioc_divisors_sq_rpow_le hD hδ).trans ?_)
    refine mul_le_mul_of_nonneg_left ?_
      (mul_nonneg (div_nonneg zero_le_two
        (sub_nonneg.mpr (Real.rpow_le_one_of_one_le_of_nonpos one_le_two (by linarith))))
        (Real.rpow_nonneg (Nat.cast_nonneg D) _))
    exact pow_le_pow_left₀ (_root_.RHTower.Sieve.invSum_nonneg _)
      (_root_.RHTower.Sieve.invSum_mono hq_le_L) 3
  have hflt₂ : (∑ k ∈ (Finset.Icc 1 (D * (N + M * (n + 1 - 1)))).filter
          (fun k : ℕ => IsUnit (Nat.cast k : ZMod (n + 1))),
        ‖a₂ k‖ ^ (2 : ℕ)) ≤
      (2 / (1 - (2 : ℝ) ^ (-(2 * w.re - 1)))) * ((n + 1 : ℕ) : ℝ) ^ (-(2 * w.re - 1)) *
        (_root_.RHTower.Sieve.invSum (D * (N + M * (n + 1 - 1)))) ^ (3 : ℕ) := by
    have h2 : (∑ k ∈ (Finset.Icc 1 (D * (N + M * (n + 1 - 1)))).filter
            (fun k : ℕ => IsUnit (Nat.cast k : ZMod (n + 1))),
          ‖a₂ k‖ ^ (2 : ℕ)) ≤
        ∑ k ∈ Finset.Ioc (n + 1) (D * (N + M * (n + 1 - 1))),
          (k.divisors.card : ℝ) ^ (2 : ℕ) * (k : ℝ) ^ (-(1 + (2 * w.re - 1))) := by
      have hite : ∀ k : ℕ, ‖a₂ k‖ ^ (2 : ℕ) =
          if (n + 1) + 1 ≤ k ∧ k ≤ D * (N + M * (n + 1 - 1)) then ‖a k‖ ^ (2 : ℕ) else 0 := by
        intro k; dsimp only [a₂]; split_ifs <;> simp
      have hIcc_Ioc : Finset.Icc ((n + 1) + 1) (D * (N + M * (n + 1 - 1))) =
          Finset.Ioc (n + 1) (D * (N + M * (n + 1 - 1))) := by
        ext k; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
      calc (∑ k ∈ (Finset.Icc 1 (D * (N + M * (n + 1 - 1)))).filter
              (fun k : ℕ => IsUnit (Nat.cast k : ZMod (n + 1))),
              ‖a₂ k‖ ^ (2 : ℕ))
          ≤ ∑ k ∈ Finset.Icc 1 (D * (N + M * (n + 1 - 1))), ‖a₂ k‖ ^ (2 : ℕ) :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) fun _ _ _ => sq_nonneg _
        _ = ∑ k ∈ Finset.Ioc (n + 1) (D * (N + M * (n + 1 - 1))), ‖a k‖ ^ (2 : ℕ) := by
            simp_rw [hite]
            rw [sum_Icc_ite_band_eq le_rfl (fun k => ‖a k‖ ^ (2 : ℕ)), hIcc_Ioc]
        _ ≤ ∑ k ∈ Finset.Ioc (n + 1) (D * (N + M * (n + 1 - 1))),
              (k.divisors.card : ℝ) ^ (2 : ℕ) * (k : ℝ) ^ (-(1 + (2 * w.re - 1))) :=
            Finset.sum_le_sum fun k hk => hnorm_a_sq k (by have := (Finset.mem_Ioc.mp hk).1; omega)
    exact h2.trans (sum_Ioc_divisors_sq_rpow_le (by omega) hδ)
  rw [hocc₁] at hmv₁
  have htot_nn : (0 : ℝ) ≤ ((n + 1).totient : ℝ) := Nat.cast_nonneg _
  have hb₁ := mul_le_mul_of_nonneg_left
    (hmv₁.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hflt₁ zero_le_two) htot_nn))
    zero_le_two
  have hb₂ := mul_le_mul_of_nonneg_left
    (hmv₂.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hflt₂ (by positivity)) htot_nn))
    zero_le_two
  exact hsum_le.trans ((add_le_add hb₁ hb₂).trans_eq (by ring))

private lemma real_log_le_rpow_div {x η : ℝ} (hx : 1 ≤ x) (hη : 0 < η) :
    Real.log x ≤ x ^ η / η := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hexp := Real.add_one_le_exp (Real.log x * η)
  rw [← Real.rpow_def_of_pos hx0] at hexp
  rw [le_div_iff₀ hη]
  linarith

/-- Explicit logarithmic Euler order `O_s(log q)` used for character-family power cancellation. -/
def vaughanDispersionOrder (q : ℕ) (s : ℂ) : ℕ :=
  ⌈|s.im|⌉₊ + 10 + 10 * (Nat.log 2 q + 1) + 2 * ⌈4 / s.re⌉₊

private def vaughanBaseOrderReal (s : ℂ) : ℝ :=
  (⌈|s.im|⌉₊ : ℝ) + 21 + 2 * (⌈4 / s.re⌉₊ : ℝ)

/-- Explicit `s`-dependent constant in the character-family power-saving bound. -/
def vaughanDispersionConstant (s : ℂ) : ℝ :=
  let δ := 1 - 2 * s.re
  let η := δ ^ (2 : ℕ) / 16
  let M₀ := vaughanBaseOrderReal s
  4 * (4 / (1 - (2 : ℝ) ^ (-δ))) *
    (1 + Real.log (3 * M₀) + 3 / η) ^ (3 : ℕ) *
    (2 * (2 : ℝ) ^ δ + 4 * (M₀ + 20 / η))

private lemma vaughanDispersionConstant_pos {s : ℂ} (hhi : s.re < 1 / 2) :
    0 < vaughanDispersionConstant s := by
  unfold vaughanDispersionConstant
  dsimp only
  have hδ : 0 < 1 - 2 * s.re := by linarith
  have hη : 0 < (1 - 2 * s.re) ^ (2 : ℕ) / 16 := by positivity
  have hdenom : 0 < 1 - (2 : ℝ) ^ (-(1 - 2 * s.re)) := by
    linarith [Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith : -(1 - 2 * s.re) < 0)]
  have hM₀ : 1 ≤ vaughanBaseOrderReal s := by
    unfold vaughanBaseOrderReal
    linarith [Nat.cast_nonneg (α := ℝ) ⌈|s.im|⌉₊, Nat.cast_nonneg (α := ℝ) ⌈4 / s.re⌉₊]
  have hlog : 0 ≤ Real.log (3 * vaughanBaseOrderReal s) := Real.log_nonneg (by linarith)
  have hblog : 0 < 1 + Real.log (3 * vaughanBaseOrderReal s) +
      3 / ((1 - 2 * s.re) ^ (2 : ℕ) / 16) := by linarith [div_pos (by norm_num : (0 : ℝ) < 3) hη]
  have htail : 0 < 2 * (2 : ℝ) ^ (1 - 2 * s.re) +
      4 * (vaughanBaseOrderReal s + 20 / ((1 - 2 * s.re) ^ (2 : ℕ) / 16)) := by positivity
  positivity

private lemma periodicEuler_beats_tail_of_vaughanEulerDefect_le_half
    {s : ℂ} (h0 : 0 < s.re) (hhi : s.re < 1 / 2)
    {q : ℕ} (hq : 2 ≤ q) (χ : DirichletCharacter ℂ q)
    (hle : ‖vaughanEulerDefect χ ⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊
      (2 * q * vaughanDispersionOrder q s + q - 1) (vaughanDispersionOrder q s)
      (1 - conj s)‖ ≤ 1 / 2) :
    periodicEulerTailBound q (2 * q * vaughanDispersionOrder q s + q - 1)
        (vaughanDispersionOrder q s) (1 - conj s) <
      ‖periodicEulerPartialSum χ (2 * q * vaughanDispersionOrder q s + q - 1)
        (vaughanDispersionOrder q s) (1 - conj s)‖ := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hq_ge1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hδ_pos : 0 < 1 - 2 * s.re := by linarith
  have hq_δ2_ge1 : (1 : ℝ) ≤ (q : ℝ) ^ ((1 - 2 * s.re) / 2) :=
    Real.one_le_rpow hq_ge1 (by linarith)
  have hD1 : 1 ≤ ⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ :=
    Nat.le_floor (by simpa using hq_δ2_ge1)
  have hD_le_rpow : (⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ : ℝ) ≤ (q : ℝ) ^ ((1 - 2 * s.re) / 2) :=
    Nat.floor_le (by positivity)
  have hw_re : (1 - conj s).re = 1 - s.re := by simp
  have hw_im : |(1 - conj s).im| = |s.im| := by simp
  have hMpoly_le : ‖moebiusCharPoly χ ⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ (1 - conj s)‖ ≤
      (1 + 1 / s.re) * (q : ℝ) ^ (1 / 4 : ℝ) := by
    unfold moebiusCharPoly
    have h1 : ‖∑ d ∈ Finset.Icc 1 ⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊,
          (ArithmeticFunction.moebius d : ℂ) * χ d * (d : ℂ) ^ (-(1 - conj s))‖ ≤
        ∑ d ∈ Finset.Icc 1 ⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊, (d : ℝ) ^ (s.re - 1) := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun d hd => ?_)
      obtain ⟨hd1, _⟩ := Finset.mem_Icc.mp hd
      rw [norm_mul, norm_mul, show (d : ℂ) = ((d : ℝ) : ℂ) by norm_cast,
        Complex.norm_cpow_eq_rpow_re_of_pos (by exact_mod_cast hd1), Complex.neg_re, hw_re]
      have hm1 : ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
        rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs]
        exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := d)
      have hp1 : ‖(ArithmeticFunction.moebius d : ℂ)‖ * ‖χ d‖ ≤ 1 :=
        mul_le_one₀ hm1 (norm_nonneg _) (χ.norm_le_one _)
      rw [show -(1 - s.re) = s.re - 1 by ring]
      calc (‖(ArithmeticFunction.moebius d : ℂ)‖ * ‖χ d‖) * (d : ℝ) ^ (s.re - 1)
          ≤ 1 * (d : ℝ) ^ (s.re - 1) :=
            mul_le_mul_of_nonneg_right hp1 (Real.rpow_nonneg (Nat.cast_nonneg d) _)
        _ = (d : ℝ) ^ (s.re - 1) := one_mul _
    have h2 := sum_Icc_rpow_sub_one_le h0 hD1
    have hD_pow : (⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ : ℝ) ^ s.re ≤ (q : ℝ) ^ (1 / 4 : ℝ) := by
      calc (⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ : ℝ) ^ s.re
          ≤ ((q : ℝ) ^ ((1 - 2 * s.re) / 2)) ^ s.re :=
            Real.rpow_le_rpow (Nat.cast_nonneg _) hD_le_rpow h0.le
        _ = (q : ℝ) ^ ((1 - 2 * s.re) / 2 * s.re) := (Real.rpow_mul hq_pos.le _ _).symm
        _ ≤ (q : ℝ) ^ (1 / 4 : ℝ) := by
            refine Real.rpow_le_rpow_of_exponent_le hq_ge1 ?_
            nlinarith [sq_nonneg (2 * s.re - 1 / 2)]
    exact h1.trans (h2.trans (mul_le_mul_of_nonneg_left hD_pow (by positivity)))
  have hprod_ge_half : (1 / 2 : ℝ) ≤
      ‖moebiusCharPoly χ ⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ (1 - conj s)‖ *
        ‖periodicEulerPartialSum χ (2 * q * vaughanDispersionOrder q s + q - 1)
          (vaughanDispersionOrder q s) (1 - conj s)‖ := by
    have htri := norm_sub_norm_le (1 : ℂ)
      (moebiusCharPoly χ ⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ (1 - conj s) *
        periodicEulerPartialSum χ (2 * q * vaughanDispersionOrder q s + q - 1)
          (vaughanDispersionOrder q s) (1 - conj s))
    rw [norm_one, ← vaughanEulerDefect, norm_mul] at htri
    linarith only [htri, hle]
  have hpart_ge : s.re / (2 * (s.re + 1)) * (q : ℝ) ^ (-(1 / 4 : ℝ)) ≤
      ‖periodicEulerPartialSum χ (2 * q * vaughanDispersionOrder q s + q - 1)
        (vaughanDispersionOrder q s) (1 - conj s)‖ := by
    have hfac_pos : 0 < (1 + 1 / s.re) * (q : ℝ) ^ (1 / 4 : ℝ) := by positivity
    have hmul_le : (1 / 2 : ℝ) ≤
        ‖periodicEulerPartialSum χ (2 * q * vaughanDispersionOrder q s + q - 1)
          (vaughanDispersionOrder q s) (1 - conj s)‖ *
          ((1 + 1 / s.re) * (q : ℝ) ^ (1 / 4 : ℝ)) := by
      rw [mul_comm]
      exact hprod_ge_half.trans (mul_le_mul_of_nonneg_right hMpoly_le (norm_nonneg _))
    have hdiv := (div_le_iff₀ hfac_pos).mpr hmul_le
    have hrew : (1 / 2 : ℝ) / ((1 + 1 / s.re) * (q : ℝ) ^ (1 / 4 : ℝ)) =
        s.re / (2 * (s.re + 1)) * (q : ℝ) ^ (-(1 / 4 : ℝ)) := by
      rw [Real.rpow_neg hq_pos.le]
      field_simp [h0.ne', (show s.re + 1 ≠ 0 by linarith),
        (show (q : ℝ) ^ (1 / 4 : ℝ) ≠ 0 by positivity)]
    rwa [hrew] at hdiv
  have hM10 : 10 ≤ vaughanDispersionOrder q s := by
    unfold vaughanDispersionOrder; omega
  have him_M : |(1 - conj s).im| ≤ (vaughanDispersionOrder q s : ℝ) := by
    rw [hw_im]
    have hceil_le : ⌈|s.im|⌉₊ ≤ vaughanDispersionOrder q s := by
      unfold vaughanDispersionOrder; omega
    exact (Nat.le_ceil |s.im|).trans (by exact_mod_cast hceil_le)
  have hlin := (periodicEulerTailBound_linear_le hq (by omega)
    (by rw [hw_re]; linarith) (by rw [hw_re]; linarith) him_M).2 hM10
  have hM_half : 5 * (Nat.log 2 q + 1) + ⌈4 / s.re⌉₊ ≤ vaughanDispersionOrder q s / 2 := by
    refine (Nat.le_div_iff_mul_le zero_lt_two).mpr ?_
    unfold vaughanDispersionOrder
    omega
  have h2_pow_q : (q : ℝ) ^ (5 : ℕ) < (2 : ℝ) ^ (5 * (Nat.log 2 q + 1)) := by
    have hlt_nat : q < 2 ^ (Nat.log 2 q + 1) := Nat.lt_pow_succ_log_self one_lt_two q
    have hlt_r : (q : ℝ) < (2 : ℝ) ^ (Nat.log 2 q + 1) := by exact_mod_cast hlt_nat
    calc (q : ℝ) ^ (5 : ℕ) < ((2 : ℝ) ^ (Nat.log 2 q + 1)) ^ (5 : ℕ) :=
          pow_lt_pow_left₀ hlt_r hq_pos.le (by decide)
      _ = (2 : ℝ) ^ (5 * (Nat.log 2 q + 1)) := by rw [← pow_mul, mul_comm]
  have h2_pow_σ : 4 / s.re < (2 : ℝ) ^ ⌈4 / s.re⌉₊ := by
    have h1 : 4 / s.re ≤ (⌈4 / s.re⌉₊ : ℝ) := Nat.le_ceil (4 / s.re)
    have h2 : (⌈4 / s.re⌉₊ : ℝ) < (2 : ℝ) ^ ⌈4 / s.re⌉₊ := by
      exact_mod_cast Nat.lt_two_pow_self (n := ⌈4 / s.re⌉₊)
    linarith
  have h2_half_gt : (q : ℝ) ^ (4 : ℕ) * (4 / s.re) <
      (2 : ℝ) ^ (vaughanDispersionOrder q s / 2) := by
    have hq4_le_q5 : (q : ℝ) ^ (4 : ℕ) ≤ (q : ℝ) ^ (5 : ℕ) :=
      pow_le_pow_right₀ hq_ge1 (by decide)
    calc (q : ℝ) ^ (4 : ℕ) * (4 / s.re)
        ≤ (q : ℝ) ^ (5 : ℕ) * (4 / s.re) :=
          mul_le_mul_of_nonneg_right hq4_le_q5 (by positivity)
      _ < (2 : ℝ) ^ (5 * (Nat.log 2 q + 1)) * (2 : ℝ) ^ ⌈4 / s.re⌉₊ :=
          mul_lt_mul'' h2_pow_q h2_pow_σ (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (5 * (Nat.log 2 q + 1) + ⌈4 / s.re⌉₊) := (pow_add _ _ _).symm
      _ ≤ (2 : ℝ) ^ (vaughanDispersionOrder q s / 2) := pow_le_pow_right₀ one_le_two hM_half
  have htail1 : (q : ℝ) ^ 3 / (2 : ℝ) ^ (vaughanDispersionOrder q s / 2) <
      (s.re / 4) * (q : ℝ) ^ (-1 : ℝ) := by
    rw [div_lt_iff₀ (by positivity), Real.rpow_neg_one]
    have hrhs : (s.re / 4) * (q : ℝ)⁻¹ * ((q : ℝ) ^ (4 : ℕ) * (4 / s.re)) = (q : ℝ) ^ 3 := by
      field_simp [hq_pos.ne', h0.ne']
    calc (q : ℝ) ^ 3 = (s.re / 4) * (q : ℝ)⁻¹ * ((q : ℝ) ^ (4 : ℕ) * (4 / s.re)) := hrhs.symm
      _ < (s.re / 4) * (q : ℝ)⁻¹ * (2 : ℝ) ^ (vaughanDispersionOrder q s / 2) :=
          mul_lt_mul_of_pos_left h2_half_gt (by positivity)
  have hcmp : (s.re / 4) * (q : ℝ) ^ (-1 : ℝ) ≤
      s.re / (2 * (s.re + 1)) * (q : ℝ) ^ (-(1 / 4 : ℝ)) := by
    have hσ_cmp : s.re / 4 ≤ s.re / (2 * (s.re + 1)) := by
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      nlinarith
    have hq_cmp : (q : ℝ) ^ (-1 : ℝ) ≤ (q : ℝ) ^ (-(1 / 4 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_le hq_ge1 (by norm_num)
    exact mul_le_mul hσ_cmp hq_cmp (by positivity) (by positivity)
  exact lt_of_le_of_lt hlin (lt_of_lt_of_le (lt_of_lt_of_le htail1 hcmp) hpart_ge)

private lemma half_le_log_two : (1 / 2 : ℝ) ≤ Real.log 2 := by
  have hexp2 := Real.add_one_le_exp (-Real.log 2)
  rw [Real.exp_neg, Real.exp_log zero_lt_two, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num] at hexp2
  linarith only [hexp2]

private lemma linear_euler_horizon_le (q M : ℕ) :
    (2 * q * M + q - 1) + M * (q - 1) ≤ 3 * q * (M + 1) := by
  calc (2 * q * M + q - 1) + M * (q - 1)
      ≤ (2 * q * M + q) + M * q :=
        Nat.add_le_add (Nat.sub_le _ _) (Nat.mul_le_mul_left M (Nat.sub_le q 1))
    _ ≤ (2 * q * M + q) + M * q + 2 * q := Nat.le_add_right _ _
    _ = 3 * q * (M + 1) := by ring

private lemma linear_euler_horizon_cast_le (q M : ℕ) :
    (((2 * q * M + q - 1) + M * (q - 1) : ℕ) : ℝ) ≤ 3 * (q : ℝ) * ((M : ℝ) + 1) :=
  (show (((2 * q * M + q - 1) + M * (q - 1) : ℕ) : ℝ) ≤
      ((3 * q * (M + 1) : ℕ) : ℝ) by exact_mod_cast linear_euler_horizon_le q M).trans_eq
    (by push_cast; ring)

private def vaughanDispersionHorizon (q : ℕ) (s : ℂ) : ℕ :=
  ⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ *
    ((2 * q * vaughanDispersionOrder q s + q - 1) + vaughanDispersionOrder q s * (q - 1))

private lemma vaughanDispersionOrder_add_one_le_rpow
    {s : ℂ} (hhi : s.re < 1 / 2) {q : ℕ} (hq : 2 ≤ q) :
    (vaughanDispersionOrder q s : ℝ) + 1 ≤
      (vaughanBaseOrderReal s + 20 / ((1 - 2 * s.re) ^ (2 : ℕ) / 16)) *
        (q : ℝ) ^ ((1 - 2 * s.re) ^ (2 : ℕ) / 16) := by
  have hq_ge1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hδ_pos : 0 < 1 - 2 * s.re := by linarith only [hhi]
  have hη_pos : 0 < (1 - 2 * s.re) ^ (2 : ℕ) / 16 := by positivity
  have hM₀_ge1 : 1 ≤ vaughanBaseOrderReal s := by
    unfold vaughanBaseOrderReal
    have h1 := Nat.cast_nonneg (α := ℝ) ⌈|s.im|⌉₊
    have h2 := Nat.cast_nonneg (α := ℝ) ⌈4 / s.re⌉₊
    linarith only [h1, h2]
  have hlog2_q : (Nat.log 2 q : ℝ) ≤ 2 * Real.log (q : ℝ) := by
    have hpow_le : (2 : ℝ) ^ (Nat.log 2 q) ≤ (q : ℝ) := by
      exact_mod_cast Nat.pow_log_le_self 2 (by omega : q ≠ 0)
    have hlog_le := Real.log_le_log (by positivity) hpow_le
    rw [Real.log_pow] at hlog_le
    have hln2 := half_le_log_two
    have hnn := Nat.cast_nonneg (α := ℝ) (Nat.log 2 q)
    nlinarith only [hlog_le, hln2, hnn]
  have hlog_eta := real_log_le_rpow_div hq_ge1 hη_pos
  have hq_eta_ge1 : (1 : ℝ) ≤ (q : ℝ) ^ ((1 - 2 * s.re) ^ (2 : ℕ) / 16) :=
    Real.one_le_rpow hq_ge1 hη_pos.le
  have hM_eq : (vaughanDispersionOrder q s : ℝ) + 1 =
      vaughanBaseOrderReal s + 10 * (Nat.log 2 q : ℝ) := by
    unfold vaughanDispersionOrder vaughanBaseOrderReal; push_cast; ring
  rw [hM_eq]
  calc vaughanBaseOrderReal s + 10 * (Nat.log 2 q : ℝ)
      ≤ vaughanBaseOrderReal s + 20 * Real.log (q : ℝ) := by linarith only [hlog2_q]
    _ ≤ vaughanBaseOrderReal s * (q : ℝ) ^ ((1 - 2 * s.re) ^ (2 : ℕ) / 16) +
          20 * ((q : ℝ) ^ ((1 - 2 * s.re) ^ (2 : ℕ) / 16) /
            ((1 - 2 * s.re) ^ (2 : ℕ) / 16)) :=
        add_le_add (le_mul_of_one_le_right (by linarith only [hM₀_ge1]) hq_eta_ge1)
          (mul_le_mul_of_nonneg_left hlog_eta (by norm_num))
    _ = (vaughanBaseOrderReal s + 20 / ((1 - 2 * s.re) ^ (2 : ℕ) / 16)) *
          (q : ℝ) ^ ((1 - 2 * s.re) ^ (2 : ℕ) / 16) := by ring

private lemma vaughanDispersionOrder_add_one_le_mul_q {q : ℕ} (hq : 2 ≤ q) (s : ℂ) :
    (vaughanDispersionOrder q s : ℝ) + 1 ≤ vaughanBaseOrderReal s * (q : ℝ) := by
  have hq_ge1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hnat_lt : Nat.log 2 q < q := Nat.log_lt_self 2 (by omega)
  have hnat_le : (Nat.log 2 q : ℝ) + 1 ≤ (q : ℝ) := by exact_mod_cast hnat_lt
  have hM_eq : (vaughanDispersionOrder q s : ℝ) + 1 =
      ((⌈|s.im|⌉₊ : ℝ) + 11 + 2 * (⌈4 / s.re⌉₊ : ℝ)) + 10 * ((Nat.log 2 q : ℝ) + 1) := by
    unfold vaughanDispersionOrder; push_cast; ring
  have hbase_eq : ((⌈|s.im|⌉₊ : ℝ) + 11 + 2 * (⌈4 / s.re⌉₊ : ℝ)) + 10 =
      vaughanBaseOrderReal s := by
    unfold vaughanBaseOrderReal; ring
  rw [hM_eq]
  have hpos_c : 0 ≤ (⌈|s.im|⌉₊ : ℝ) + 11 + 2 * (⌈4 / s.re⌉₊ : ℝ) := by positivity
  nlinarith only [hq_ge1, hnat_le, hbase_eq, hpos_c]

private lemma vaughanDispersionHorizon_invSum_cube_le
    {s : ℂ} (h0 : 0 < s.re) (hhi : s.re < 1 / 2) {q : ℕ} (hq : 2 ≤ q) :
    (_root_.RHTower.Sieve.invSum (vaughanDispersionHorizon q s)) ^ (3 : ℕ) ≤
      (1 + Real.log (3 * vaughanBaseOrderReal s) +
        3 / ((1 - 2 * s.re) ^ (2 : ℕ) / 16)) ^ (3 : ℕ) *
        (q : ℝ) ^ (3 * ((1 - 2 * s.re) ^ (2 : ℕ) / 16)) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hq_ge1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hδ_pos : 0 < 1 - 2 * s.re := by linarith only [hhi]
  have hη_pos : 0 < (1 - 2 * s.re) ^ (2 : ℕ) / 16 := by positivity
  have hM₀_ge1 : 1 ≤ vaughanBaseOrderReal s := by
    unfold vaughanBaseOrderReal
    have h1 := Nat.cast_nonneg (α := ℝ) ⌈|s.im|⌉₊
    have h2 := Nat.cast_nonneg (α := ℝ) ⌈4 / s.re⌉₊
    linarith only [h1, h2]
  have hq_δ2_ge1 : (1 : ℝ) ≤ (q : ℝ) ^ ((1 - 2 * s.re) / 2) :=
    Real.one_le_rpow hq_ge1 (by linarith only [hδ_pos])
  have hq_δ2_le_q : (q : ℝ) ^ ((1 - 2 * s.re) / 2) ≤ (q : ℝ) := by
    calc (q : ℝ) ^ ((1 - 2 * s.re) / 2) ≤ (q : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hq_ge1 (by linarith only [h0])
      _ = (q : ℝ) := Real.rpow_one _
  have hD1 : 1 ≤ ⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ :=
    Nat.le_floor (by simpa using hq_δ2_ge1)
  have hDq : ⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ ≤ q := Nat.floor_le_of_le hq_δ2_le_q
  have hNq : q ≤ 2 * q * vaughanDispersionOrder q s + q - 1 := by
    have hM1 : 1 ≤ vaughanDispersionOrder q s := by unfold vaughanDispersionOrder; omega
    have hqM : 2 ≤ 2 * q * vaughanDispersionOrder q s := by nlinarith only [hq, hM1]
    omega
  have hL_ge1 : 1 ≤ vaughanDispersionHorizon q s := by
    unfold vaughanDispersionHorizon
    exact Nat.mul_pos hD1 (by omega)
  have hL_le : (vaughanDispersionHorizon q s : ℝ) ≤
      3 * vaughanBaseOrderReal s * (q : ℝ) ^ (3 : ℕ) := by
    calc (vaughanDispersionHorizon q s : ℝ)
        = (⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ : ℝ) *
            (((2 * q * vaughanDispersionOrder q s + q - 1) +
              vaughanDispersionOrder q s * (q - 1) : ℕ) : ℝ) := by
          unfold vaughanDispersionHorizon; push_cast; rfl
      _ ≤ (q : ℝ) * (3 * (q : ℝ) * ((vaughanDispersionOrder q s : ℝ) + 1)) :=
          mul_le_mul (by exact_mod_cast hDq)
            (linear_euler_horizon_cast_le q (vaughanDispersionOrder q s))
            (Nat.cast_nonneg _) hq_pos.le
      _ ≤ (q : ℝ) * (3 * (q : ℝ) * (vaughanBaseOrderReal s * (q : ℝ))) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left (vaughanDispersionOrder_add_one_le_mul_q hq s)
              (by positivity)) hq_pos.le
      _ = 3 * vaughanBaseOrderReal s * (q : ℝ) ^ (3 : ℕ) := by ring
  have hinv_le : _root_.RHTower.Sieve.invSum (vaughanDispersionHorizon q s) ≤
      (1 + Real.log (3 * vaughanBaseOrderReal s) +
        3 / ((1 - 2 * s.re) ^ (2 : ℕ) / 16)) *
        (q : ℝ) ^ ((1 - 2 * s.re) ^ (2 : ℕ) / 16) := by
    have h1 := _root_.RHTower.Sieve.invSum_le_one_add_log hL_ge1
    have hlog_L : Real.log (vaughanDispersionHorizon q s : ℝ) ≤
        Real.log (3 * vaughanBaseOrderReal s) + 3 * Real.log (q : ℝ) := by
      calc Real.log (vaughanDispersionHorizon q s : ℝ)
          ≤ Real.log (3 * vaughanBaseOrderReal s * (q : ℝ) ^ (3 : ℕ)) :=
            Real.log_le_log (by exact_mod_cast hL_ge1) hL_le
        _ = Real.log (3 * vaughanBaseOrderReal s) + Real.log ((q : ℝ) ^ (3 : ℕ)) :=
            Real.log_mul (by linarith only [hM₀_ge1]) (by positivity)
        _ = Real.log (3 * vaughanBaseOrderReal s) + 3 * Real.log (q : ℝ) := by
            rw [Real.log_pow]; ring
    have hlog_eta := real_log_le_rpow_div hq_ge1 hη_pos
    have hq_eta_ge1 : (1 : ℝ) ≤ (q : ℝ) ^ ((1 - 2 * s.re) ^ (2 : ℕ) / 16) :=
      Real.one_le_rpow hq_ge1 hη_pos.le
    have hconst_nn : 0 ≤ 1 + Real.log (3 * vaughanBaseOrderReal s) := by
      have hlog_nn := Real.log_nonneg (show 1 ≤ 3 * vaughanBaseOrderReal s by linarith only [hM₀_ge1])
      linarith only [hlog_nn]
    calc _root_.RHTower.Sieve.invSum (vaughanDispersionHorizon q s)
        ≤ (1 + Real.log (3 * vaughanBaseOrderReal s)) + 3 * Real.log (q : ℝ) := by
          linarith only [h1, hlog_L]
      _ ≤ (1 + Real.log (3 * vaughanBaseOrderReal s)) *
            (q : ℝ) ^ ((1 - 2 * s.re) ^ (2 : ℕ) / 16) +
            3 * ((q : ℝ) ^ ((1 - 2 * s.re) ^ (2 : ℕ) / 16) /
              ((1 - 2 * s.re) ^ (2 : ℕ) / 16)) :=
          add_le_add (le_mul_of_one_le_right hconst_nn hq_eta_ge1)
            (mul_le_mul_of_nonneg_left hlog_eta (by norm_num))
      _ = (1 + Real.log (3 * vaughanBaseOrderReal s) +
            3 / ((1 - 2 * s.re) ^ (2 : ℕ) / 16)) *
            (q : ℝ) ^ ((1 - 2 * s.re) ^ (2 : ℕ) / 16) := by ring
  calc (_root_.RHTower.Sieve.invSum (vaughanDispersionHorizon q s)) ^ (3 : ℕ)
      ≤ ((1 + Real.log (3 * vaughanBaseOrderReal s) +
          3 / ((1 - 2 * s.re) ^ (2 : ℕ) / 16)) *
          (q : ℝ) ^ ((1 - 2 * s.re) ^ (2 : ℕ) / 16)) ^ (3 : ℕ) :=
        pow_le_pow_left₀ (_root_.RHTower.Sieve.invSum_nonneg _) hinv_le 3
    _ = (1 + Real.log (3 * vaughanBaseOrderReal s) +
          3 / ((1 - 2 * s.re) ^ (2 : ℕ) / 16)) ^ (3 : ℕ) *
          ((q : ℝ) ^ ((1 - 2 * s.re) ^ (2 : ℕ) / 16)) ^ (3 : ℕ) := mul_pow _ _ 3
    _ = (1 + Real.log (3 * vaughanBaseOrderReal s) +
          3 / ((1 - 2 * s.re) ^ (2 : ℕ) / 16)) ^ (3 : ℕ) *
          (q : ℝ) ^ (3 * ((1 - 2 * s.re) ^ (2 : ℕ) / 16)) := by
        rw [← Real.rpow_natCast ((q : ℝ) ^ _) 3, ← Real.rpow_mul hq_pos.le]
        congr 2; push_cast; ring

private lemma vaughanDispersion_occupancy_sum_le
    {s : ℂ} (h0 : 0 < s.re) (hhi : s.re < 1 / 2) {q : ℕ} (hq : 2 ≤ q) :
    2 * (⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ : ℝ) ^ (-(1 - 2 * s.re)) +
        ((vaughanDispersionHorizon q s : ℝ) / (q : ℝ) + 1) * (q : ℝ) ^ (-(1 - 2 * s.re)) ≤
      (2 * (2 : ℝ) ^ (1 - 2 * s.re) +
        4 * (vaughanBaseOrderReal s + 20 / ((1 - 2 * s.re) ^ (2 : ℕ) / 16))) *
        (q : ℝ) ^ (((1 - 2 * s.re) ^ (2 : ℕ) / 16) - (1 - 2 * s.re) ^ (2 : ℕ) / 2) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hq_ge1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hδ_pos : 0 < 1 - 2 * s.re := by linarith only [hhi]
  have hδ_lt1 : 1 - 2 * s.re < 1 := by linarith only [h0]
  have hη_pos : 0 < (1 - 2 * s.re) ^ (2 : ℕ) / 16 := by positivity
  have hM₀_ge1 : 1 ≤ vaughanBaseOrderReal s := by
    unfold vaughanBaseOrderReal
    have h1 := Nat.cast_nonneg (α := ℝ) ⌈|s.im|⌉₊
    have h2 := Nat.cast_nonneg (α := ℝ) ⌈4 / s.re⌉₊
    linarith only [h1, h2]
  have hq_δ2_ge1 : (1 : ℝ) ≤ (q : ℝ) ^ ((1 - 2 * s.re) / 2) :=
    Real.one_le_rpow hq_ge1 (by linarith only [hδ_pos])
  have hD1 : 1 ≤ ⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ :=
    Nat.le_floor (by simpa using hq_δ2_ge1)
  have hD_le_rpow : (⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ : ℝ) ≤ (q : ℝ) ^ ((1 - 2 * s.re) / 2) :=
    Nat.floor_le (by positivity)
  have hD_ge_half : (q : ℝ) ^ ((1 - 2 * s.re) / 2) / 2 ≤
      (⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ : ℝ) := by
    have hlt := Nat.lt_floor_add_one ((q : ℝ) ^ ((1 - 2 * s.re) / 2))
    have h1D : (1 : ℝ) ≤ (⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ : ℝ) := by exact_mod_cast hD1
    linarith only [hlt, h1D]
  have hD_neg_δ : (⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ : ℝ) ^ (-(1 - 2 * s.re)) ≤
      (2 : ℝ) ^ (1 - 2 * s.re) * (q : ℝ) ^ (-((1 - 2 * s.re) ^ (2 : ℕ) / 2)) := by
    have hhalf_pos : 0 < (q : ℝ) ^ ((1 - 2 * s.re) / 2) / 2 := by positivity
    calc (⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ : ℝ) ^ (-(1 - 2 * s.re))
        ≤ ((q : ℝ) ^ ((1 - 2 * s.re) / 2) / 2) ^ (-(1 - 2 * s.re)) :=
          Real.rpow_le_rpow_of_nonpos hhalf_pos hD_ge_half (by linarith only [hδ_pos])
      _ = ((q : ℝ) ^ ((1 - 2 * s.re) / 2) * (2 : ℝ)⁻¹) ^ (-(1 - 2 * s.re)) := by
          rw [div_eq_mul_inv]
      _ = ((q : ℝ) ^ ((1 - 2 * s.re) / 2)) ^ (-(1 - 2 * s.re)) *
            ((2 : ℝ)⁻¹) ^ (-(1 - 2 * s.re)) :=
          Real.mul_rpow (by positivity) (by positivity)
      _ = (2 : ℝ) ^ (1 - 2 * s.re) * (q : ℝ) ^ (-((1 - 2 * s.re) ^ (2 : ℕ) / 2)) := by
          rw [← Real.rpow_mul hq_pos.le, Real.inv_rpow zero_le_two,
            Real.rpow_neg zero_le_two, inv_inv]
          have hexp : (1 - 2 * s.re) / 2 * -(1 - 2 * s.re) =
              -((1 - 2 * s.re) ^ (2 : ℕ) / 2) := by ring
          rw [hexp]; ring
  have hocc_L : ((vaughanDispersionHorizon q s : ℝ) / (q : ℝ) + 1) * (q : ℝ) ^ (-(1 - 2 * s.re)) ≤
      4 * (vaughanBaseOrderReal s + 20 / ((1 - 2 * s.re) ^ (2 : ℕ) / 16)) *
        (q : ℝ) ^ (((1 - 2 * s.re) ^ (2 : ℕ) / 16) - (1 - 2 * s.re) / 2) := by
    have hdiv_le : (vaughanDispersionHorizon q s : ℝ) / (q : ℝ) ≤
        3 * (q : ℝ) ^ ((1 - 2 * s.re) / 2) * ((vaughanDispersionOrder q s : ℝ) + 1) := by
      rw [div_le_iff₀ hq_pos]
      calc (vaughanDispersionHorizon q s : ℝ)
          = (⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ : ℝ) *
              (((2 * q * vaughanDispersionOrder q s + q - 1) +
                vaughanDispersionOrder q s * (q - 1) : ℕ) : ℝ) := by
            unfold vaughanDispersionHorizon; push_cast; rfl
        _ ≤ (q : ℝ) ^ ((1 - 2 * s.re) / 2) *
              (3 * (q : ℝ) * ((vaughanDispersionOrder q s : ℝ) + 1)) :=
            mul_le_mul hD_le_rpow (linear_euler_horizon_cast_le q (vaughanDispersionOrder q s))
              (Nat.cast_nonneg _) (by positivity)
        _ = 3 * (q : ℝ) ^ ((1 - 2 * s.re) / 2) *
              ((vaughanDispersionOrder q s : ℝ) + 1) * (q : ℝ) := by ring
    have h1_le : (1 : ℝ) ≤
        (q : ℝ) ^ ((1 - 2 * s.re) / 2) * ((vaughanDispersionOrder q s : ℝ) + 1) := by
      have hM_nn := Nat.cast_nonneg (α := ℝ) (vaughanDispersionOrder q s)
      nlinarith only [hq_δ2_ge1, hM_nn]
    have hLq : (vaughanDispersionHorizon q s : ℝ) / (q : ℝ) + 1 ≤
        4 * (q : ℝ) ^ ((1 - 2 * s.re) / 2) * ((vaughanDispersionOrder q s : ℝ) + 1) := by
      linarith only [hdiv_le, h1_le]
    calc ((vaughanDispersionHorizon q s : ℝ) / (q : ℝ) + 1) * (q : ℝ) ^ (-(1 - 2 * s.re))
        ≤ (4 * (q : ℝ) ^ ((1 - 2 * s.re) / 2) * ((vaughanDispersionOrder q s : ℝ) + 1)) *
            (q : ℝ) ^ (-(1 - 2 * s.re)) :=
          mul_le_mul_of_nonneg_right hLq (Real.rpow_nonneg hq_pos.le _)
      _ ≤ (4 * (q : ℝ) ^ ((1 - 2 * s.re) / 2) *
            ((vaughanBaseOrderReal s + 20 / ((1 - 2 * s.re) ^ (2 : ℕ) / 16)) *
              (q : ℝ) ^ ((1 - 2 * s.re) ^ (2 : ℕ) / 16))) *
            (q : ℝ) ^ (-(1 - 2 * s.re)) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (vaughanDispersionOrder_add_one_le_rpow hhi hq)
              (by positivity))
            (Real.rpow_nonneg hq_pos.le _)
      _ = 4 * (vaughanBaseOrderReal s + 20 / ((1 - 2 * s.re) ^ (2 : ℕ) / 16)) *
            ((q : ℝ) ^ ((1 - 2 * s.re) / 2) *
              (q : ℝ) ^ ((1 - 2 * s.re) ^ (2 : ℕ) / 16) *
              (q : ℝ) ^ (-(1 - 2 * s.re))) := by ring
      _ = 4 * (vaughanBaseOrderReal s + 20 / ((1 - 2 * s.re) ^ (2 : ℕ) / 16)) *
            (q : ℝ) ^ (((1 - 2 * s.re) ^ (2 : ℕ) / 16) - (1 - 2 * s.re) / 2) := by
          rw [← Real.rpow_add hq_pos, ← Real.rpow_add hq_pos]
          congr 2; ring
  have hD_eta_le : (q : ℝ) ^ (-((1 - 2 * s.re) ^ (2 : ℕ) / 2)) ≤
      (q : ℝ) ^ (((1 - 2 * s.re) ^ (2 : ℕ) / 16) - (1 - 2 * s.re) ^ (2 : ℕ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hq_ge1 (by linarith only [hη_pos])
  have hsq_le : (1 - 2 * s.re) ^ (2 : ℕ) ≤ 1 - 2 * s.re := by nlinarith only [hδ_pos, hδ_lt1]
  have hq_exp_cmp : (q : ℝ) ^ (((1 - 2 * s.re) ^ (2 : ℕ) / 16) - (1 - 2 * s.re) / 2) ≤
      (q : ℝ) ^ (((1 - 2 * s.re) ^ (2 : ℕ) / 16) - (1 - 2 * s.re) ^ (2 : ℕ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le hq_ge1 (by linarith only [hsq_le])
  have ht1 : 2 * (⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ : ℝ) ^ (-(1 - 2 * s.re)) ≤
      2 * (2 : ℝ) ^ (1 - 2 * s.re) *
        (q : ℝ) ^ (((1 - 2 * s.re) ^ (2 : ℕ) / 16) - (1 - 2 * s.re) ^ (2 : ℕ) / 2) := by
    calc 2 * (⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ : ℝ) ^ (-(1 - 2 * s.re))
        ≤ 2 * ((2 : ℝ) ^ (1 - 2 * s.re) *
            (q : ℝ) ^ (-((1 - 2 * s.re) ^ (2 : ℕ) / 2))) :=
          mul_le_mul_of_nonneg_left hD_neg_δ zero_le_two
      _ = 2 * (2 : ℝ) ^ (1 - 2 * s.re) *
            (q : ℝ) ^ (-((1 - 2 * s.re) ^ (2 : ℕ) / 2)) := by ring
      _ ≤ 2 * (2 : ℝ) ^ (1 - 2 * s.re) *
            (q : ℝ) ^ (((1 - 2 * s.re) ^ (2 : ℕ) / 16) - (1 - 2 * s.re) ^ (2 : ℕ) / 2) :=
          mul_le_mul_of_nonneg_left hD_eta_le (by positivity)
  have hcoef2_nn : 0 ≤ 4 * (vaughanBaseOrderReal s + 20 / ((1 - 2 * s.re) ^ (2 : ℕ) / 16)) := by
    have hd_pos : 0 < 20 / ((1 - 2 * s.re) ^ (2 : ℕ) / 16) := div_pos (by norm_num) hη_pos
    linarith only [hM₀_ge1, hd_pos]
  have ht2 := hocc_L.trans (mul_le_mul_of_nonneg_left hq_exp_cmp hcoef2_nn)
  exact (add_le_add ht1 ht2).trans_eq (by ring)

private lemma mul_four_dispersion_factors_le
    {A K I₁ I₂ S₁ S₂ : ℝ} (hA : 0 ≤ A) (hK : 0 ≤ K) (hI₁ : 0 ≤ I₁) (hS₁ : 0 ≤ S₁)
    (hI : I₁ ≤ I₂) (hS : S₁ ≤ S₂) :
    4 * (A * K * I₁ * S₁) ≤ 4 * (A * K * I₂ * S₂) := by
  have hAK : 0 ≤ A * K := mul_nonneg hA hK
  have hI₂ : 0 ≤ I₂ := hI₁.trans hI
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
  exact mul_le_mul (mul_le_mul_of_nonneg_left hI hAK) hS hS₁ (mul_nonneg hAK hI₂)

private lemma vaughanDispersion_second_moment_le
    {s : ℂ} (h0 : 0 < s.re) (hhi : s.re < 1 / 2) {q : ℕ} (hq : 2 ≤ q) :
    4 * (∑ χ : DirichletCharacter ℂ q,
        ‖vaughanEulerDefect χ ⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊
          (2 * q * vaughanDispersionOrder q s + q - 1) (vaughanDispersionOrder q s)
          (1 - conj s)‖ ^ (2 : ℕ)) ≤
      vaughanDispersionConstant s * (q.totient : ℝ) *
        (q : ℝ) ^ (-((1 - 2 * s.re) ^ (2 : ℕ) / 4)) := by
  have hq_pos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hq_ge1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (by omega : 1 ≤ q)
  have hδ_pos : 0 < 1 - 2 * s.re := by linarith only [hhi]
  have hK_pos : 0 < 1 - (2 : ℝ) ^ (-(1 - 2 * s.re)) := by
    have hr := Real.rpow_lt_one_of_one_lt_of_neg one_lt_two (by linarith only [hδ_pos] : -(1 - 2 * s.re) < 0)
    linarith only [hr]
  have hq_δ2_ge1 : (1 : ℝ) ≤ (q : ℝ) ^ ((1 - 2 * s.re) / 2) :=
    Real.one_le_rpow hq_ge1 (by linarith only [hδ_pos])
  have hq_δ2_le_q : (q : ℝ) ^ ((1 - 2 * s.re) / 2) ≤ (q : ℝ) := by
    calc (q : ℝ) ^ ((1 - 2 * s.re) / 2) ≤ (q : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hq_ge1 (by linarith only [h0])
      _ = (q : ℝ) := Real.rpow_one _
  have hD1 : 1 ≤ ⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ :=
    Nat.le_floor (by simpa using hq_δ2_ge1)
  have hDq : ⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ ≤ q := Nat.floor_le_of_le hq_δ2_le_q
  have hNq : q ≤ 2 * q * vaughanDispersionOrder q s + q - 1 := by
    have hM1 : 1 ≤ vaughanDispersionOrder q s := by unfold vaughanDispersionOrder; omega
    have hqM : 2 ≤ 2 * q * vaughanDispersionOrder q s := by nlinarith only [hq, hM1]
    omega
  have hw_re : (1 - conj s).re = 1 - s.re := by simp
  have h2w_sub1 : 2 * (1 - conj s).re - 1 = 1 - 2 * s.re := by rw [hw_re]; ring
  have hsecond := sum_normSq_vaughanEulerDefect_le (M := vaughanDispersionOrder q s)
    hq hD1 hDq hNq (w := 1 - conj s) (by rw [hw_re]; linarith only [hhi])
  have hL_eq : ⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ *
      ((2 * q * vaughanDispersionOrder q s + q - 1) + vaughanDispersionOrder q s * (q - 1)) =
      vaughanDispersionHorizon q s := rfl
  rw [h2w_sub1, hL_eq] at hsecond
  have hS₁_nn : 0 ≤ 2 * (⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ : ℝ) ^ (-(1 - 2 * s.re)) +
      ((vaughanDispersionHorizon q s : ℝ) / (q : ℝ) + 1) * (q : ℝ) ^ (-(1 - 2 * s.re)) :=
    add_nonneg (mul_nonneg zero_le_two (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      (mul_nonneg (add_nonneg (div_nonneg (Nat.cast_nonneg _) hq_pos.le) zero_le_one)
        (Real.rpow_nonneg hq_pos.le _))
  calc 4 * (∑ χ : DirichletCharacter ℂ q,
          ‖vaughanEulerDefect χ ⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊
            (2 * q * vaughanDispersionOrder q s + q - 1) (vaughanDispersionOrder q s)
            (1 - conj s)‖ ^ (2 : ℕ))
      ≤ 4 * ((q.totient : ℝ) * (4 / (1 - (2 : ℝ) ^ (-(1 - 2 * s.re)))) *
          (_root_.RHTower.Sieve.invSum (vaughanDispersionHorizon q s)) ^ (3 : ℕ) *
          (2 * (⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ : ℝ) ^ (-(1 - 2 * s.re)) +
            ((vaughanDispersionHorizon q s : ℝ) / (q : ℝ) + 1) * (q : ℝ) ^ (-(1 - 2 * s.re)))) :=
        mul_le_mul_of_nonneg_left hsecond (by norm_num)
    _ ≤ 4 * ((q.totient : ℝ) * (4 / (1 - (2 : ℝ) ^ (-(1 - 2 * s.re)))) *
          ((1 + Real.log (3 * vaughanBaseOrderReal s) +
            3 / ((1 - 2 * s.re) ^ (2 : ℕ) / 16)) ^ (3 : ℕ) *
            (q : ℝ) ^ (3 * ((1 - 2 * s.re) ^ (2 : ℕ) / 16))) *
          ((2 * (2 : ℝ) ^ (1 - 2 * s.re) +
            4 * (vaughanBaseOrderReal s + 20 / ((1 - 2 * s.re) ^ (2 : ℕ) / 16))) *
            (q : ℝ) ^ (((1 - 2 * s.re) ^ (2 : ℕ) / 16) - (1 - 2 * s.re) ^ (2 : ℕ) / 2))) :=
        mul_four_dispersion_factors_le
          (Nat.cast_nonneg _)
          (div_nonneg (by norm_num) hK_pos.le)
          (pow_nonneg (_root_.RHTower.Sieve.invSum_nonneg _) 3)
          hS₁_nn
          (vaughanDispersionHorizon_invSum_cube_le h0 hhi hq)
          (vaughanDispersion_occupancy_sum_le h0 hhi hq)
    _ = vaughanDispersionConstant s * (q.totient : ℝ) *
          ((q : ℝ) ^ (3 * ((1 - 2 * s.re) ^ (2 : ℕ) / 16)) *
            (q : ℝ) ^ (((1 - 2 * s.re) ^ (2 : ℕ) / 16) - (1 - 2 * s.re) ^ (2 : ℕ) / 2)) := by
        unfold vaughanDispersionConstant; dsimp only; ring
    _ = vaughanDispersionConstant s * (q.totient : ℝ) *
          (q : ℝ) ^ (-((1 - 2 * s.re) ^ (2 : ℕ) / 4)) := by
        rw [← Real.rpow_add hq_pos]
        congr 2
        ring

/-- **Unconditional all-height power cancellation beyond `3001/24000` across ALL `0 < Re s < 1/2`:**
for **every** `s : ℂ` with `0 < Re s < 1/2` (strictly beyond `3001/24000` all the way to `1/2`)
and **every** ordinate `Im s ∈ ℝ` (zero height averaging), there exists `C > 0` such that for every
modulus `q ≥ 2`, setting `M = vaughanDispersionOrder q s` and linear cutoff `N = 2 q M + q - 1`:
1. At most `C · φ(q) · q^{-(1 - 2 Re s)^2 / 4}` nonprincipal characters `χ : DirichletCharacter ℂ q`
   fail the strict linear-prefix witness test `periodicEulerTailBound q N M (1 - conj s) < ‖periodicEulerPartialSum χ N M (1 - conj s)‖`.
2. Every passing character `χ ≠ 1` satisfies `χ.LFunction (1 - conj s) ≠ 0`, and if `χ.IsPrimitive`
   also `χ.LFunction s ≠ 0` directly at `s`. -/
theorem power_saving_dirichlet_euler_witnesses_beyond_sub_one_eighth
    {s : ℂ} (h0 : 0 < s.re) (hhi : s.re < 1 / 2) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (_hq : 2 ≤ q),
      let M := vaughanDispersionOrder q s
      let N := 2 * q * M + q - 1
      let bad : Finset (DirichletCharacter ℂ q) :=
        Finset.univ.filter (fun χ => χ ≠ 1 ∧
          ¬ (periodicEulerTailBound q N M (1 - conj s) <
              ‖periodicEulerPartialSum χ N M (1 - conj s)‖))
      (bad.card : ℝ) ≤ C * (q.totient : ℝ) * (q : ℝ) ^ (-((1 - 2 * s.re) ^ (2 : ℕ) / 4)) ∧
      (∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → χ ∉ bad →
        χ.LFunction (1 - conj s) ≠ 0 ∧ (χ.IsPrimitive → χ.LFunction s ≠ 0)) := by
  refine ⟨vaughanDispersionConstant s, vaughanDispersionConstant_pos hhi, fun q _ hq => ?_⟩
  let M : ℕ := vaughanDispersionOrder q s
  let N : ℕ := 2 * q * M + q - 1
  let bad : Finset (DirichletCharacter ℂ q) :=
    Finset.univ.filter (fun χ => χ ≠ 1 ∧
      ¬ (periodicEulerTailBound q N M (1 - conj s) <
          ‖periodicEulerPartialSum χ N M (1 - conj s)‖))
  have hbad_gt : ∀ χ ∈ bad,
      (1 / 2 : ℝ) < ‖vaughanEulerDefect χ ⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ N M (1 - conj s)‖ := by
    intro χ hχ
    obtain ⟨_, _, hnot_beat⟩ := Finset.mem_filter.mp hχ
    by_contra hle
    exact hnot_beat (periodicEuler_beats_tail_of_vaughanEulerDefect_le_half
      h0 hhi hq χ (not_lt.mp hle))
  have hmarkov : (bad.card : ℝ) ≤
      4 * ∑ χ : DirichletCharacter ℂ q,
        ‖vaughanEulerDefect χ ⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ N M (1 - conj s)‖ ^ (2 : ℕ) := by
    have h1 : (∑ _χ ∈ bad, (1 / 4 : ℝ)) ≤
        ∑ χ ∈ bad,
          ‖vaughanEulerDefect χ ⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ N M (1 - conj s)‖ ^ (2 : ℕ) := by
      refine Finset.sum_le_sum fun χ hχ => ?_
      have hgt := hbad_gt χ hχ
      nlinarith only [hgt]
    have h2 : (∑ χ ∈ bad,
          ‖vaughanEulerDefect χ ⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ N M (1 - conj s)‖ ^ (2 : ℕ)) ≤
        ∑ χ : DirichletCharacter ℂ q,
          ‖vaughanEulerDefect χ ⌊(q : ℝ) ^ ((1 - 2 * s.re) / 2)⌋₊ N M (1 - conj s)‖ ^ (2 : ℕ) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ bad) fun _ _ _ => sq_nonneg _
    rw [Finset.sum_const, nsmul_eq_mul] at h1
    linarith only [h1, h2]
  refine ⟨hmarkov.trans (vaughanDispersion_second_moment_le h0 hhi hq), ?_⟩
  intro χ hχ hnot
  have hbeat : periodicEulerTailBound q N M (1 - conj s) <
      ‖periodicEulerPartialSum χ N M (1 - conj s)‖ := by
    by_contra hn
    exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ χ, hχ, hn⟩)
  have hM1 : 1 ≤ M := by dsimp only [M, vaughanDispersionOrder]; omega
  have hw_pos : 0 < (1 - conj s).re := by simp; linarith
  have hne_w : χ.LFunction (1 - conj s) ≠ 0 :=
    (LFunction_ne_zero_of_periodicEuler_beats_tail hq hχ N hM1 hw_pos).1 hbeat
  refine ⟨hne_w, fun hprim hzero_s => ?_⟩
  have hrefl := _root_.RHTower.LFunction_eq_zero_conj_one_sub hχ hprim hzero_s h0 (by linarith)
  have hconj_eq : conj (1 - s) = 1 - conj s := by rw [map_sub, map_one]
  rw [hconj_eq] at hrefl
  exact hne_w hrefl

#print axioms strideMean_two_eq_strideAvg
#print axioms strideMean_comm
#print axioms iterate_strideMean_div_eq
#print axioms multiStrideMean_two_eq_multiStrideEuler
#print axioms norm_multiStrideMean_sub_const_le_of_window
#print axioms not_liouvilleTwist_stable_additiveStridePairClass
#print axioms classConstants_singleStrideTestClass_liouvilleTwist_ne
#print axioms highDivisorMoebiusEta_eq_dual_quotient_windows
#print axioms highDivisorMoebiusEta_eq_vaughanTypeI_add_typeII
#print axioms norm_multiStrideEuler_vaughan_typeI_or_typeII_ge_of_zeta_eq_zero
#print axioms exists_sublinear_moebius_and_liouville_on_remaining_strip
#print axioms periodicEulerPartialSum_eq_sum_weights
#print axioms norm_LFunction_sub_periodicEulerPartialSum_le
#print axioms periodicEulerTailBound_linear_le
#print axioms LFunction_ne_zero_of_periodicEuler_beats_tail
#print axioms subSevenEighths_periodicEuler_beats_tail_all_heights
#print axioms subOneEighth_primitive_periodicEuler_beats_tail_all_heights
#print axioms hecke_dirichletBaseChange_beats_tail_on_subSevenEighths
#print axioms gaugeExponent_moebius_dirichletGauge_le_sub_seven_eighths
#print axioms sum_twistedMoebius_mul_charPartialSum_eq_one
#print axioms norm_multiStrideMean_twistedMoebius_highDivisors_ge_of_LFunction_eq_zero
#print axioms sum_twistedLiouville_mul_charPartialSum_eq_squareCharHead
#print axioms norm_quadratic_LFunction_two_mul_refl_ge
#print axioms vaughanEulerDefect_eq_typeIIShort_sub_tail
#print axioms sum_normSq_vaughanEulerDefect_le
#print axioms power_saving_dirichlet_euler_witnesses_beyond_sub_one_eighth

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

end
