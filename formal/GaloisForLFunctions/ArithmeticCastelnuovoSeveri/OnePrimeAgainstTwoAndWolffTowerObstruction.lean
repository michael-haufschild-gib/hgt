import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.OnePrimeSeesEveryWellFoundedLevel
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheTowerDefectCountsTheFrobeniusEigenvalues
import GaloisForLFunctions.HTGeometry.PositiveWolffMeasure
import GaloisForLFunctions.RHTower.WeilLagSingleBaseWolffConfiguration

/-!
# One Prime Against Two: Toeplitz Laurent-Moment Representation, the Wolff Annulus Obstruction, and the Well-Founded Visible Law

This module resolves Open Problem 7 of `ArithmeticCastelnuovoSeveri` (*One prime against two*) by
establishing the exact Toeplitz Laurent-moment representation of a single-prime tower, proving both
the two-annulus Laurent-orthogonal obstruction and the symmetric Wolff Toeplitz-blindness theorem
at non-attained tops, and isolating the unconditional positive laws (`wfVisibleSet`,
above-threshold extraction, bounded-ordinate well-foundedness, and the two-prime rescue) that hold
for every tempered zero configuration:

1. **Exact Toeplitz Laurent-Moment Representation of a Single-Prime Tower
   (`towerMoment`, `summable_towerMoment_term`, `towerGram_apply_eq_towerMoment`,
   `towerGram_eq_of_towerMoment_eq`):**
   - For every tempered configuration `Z`, compactly supported `C²` test `g`, scale `ℓ`, and
     window `K : Finset ℤ`, the `(j, k)`-entry of `towerGram Z g ℓ K` is the two-sided Laurent
     moment
     `towerMoment Z g ℓ (j - k) = ∑' τ : Z.carrier, X_τ(g) conj(X_{1-τ̄}(g)) β(τ)^{j - k}`.
   - Consequently, `towerGram Z g ℓ K` is a Toeplitz matrix that depends on `(Z, g)` **exclusively**
     through the two-sided Laurent moment sequence `m ↦ towerMoment Z g ℓ m` (`m ∈ ℤ`). Any two
     configurations or tests sharing the same Laurent moments at scale `ℓ` have identical
     `towerGram` matrices and identical `hermNegIndex` on every finite window `K ⊂ ℤ`.

2. **The Two-Annulus Laurent-Orthogonal Obstruction and Single-Prime Toeplitz Blindness at
   Non-Attained Tops (`exists_normalized_positive_wolff_annulus`,
   `exists_counterexample_to_laurent_class_extraction_without_wellFounded`,
   `exists_symmetric_wolff_toeplitz_blind_configuration`):**
   - *Sharpness of `tsum_ite_eq_zero_of_moments_of_wellFounded`:* On any two disjoint outer annuli
     `0 < r₁ < R₁ ≤ r₂ < R₂`, the difference of the normalized positive Wolff measures on
     `annulus r₁ R₁` and `annulus r₂ R₂` gives a countable injective family `w : T → ℂ` in
     `annulus r₁ R₂` (with moduli accumulating at `R₁` and `R₂` from below, violating
     `WellFoundedOn (· > ·)`) and nonzero weights `q : T → ℂ` with `∑' τ, ‖q τ‖ = 2` whose
     **entire two-sided Laurent moment sequence vanishes (`∀ m : ℤ, ∑' τ, q τ * w τ ^ m = 0`,
     including `m = 0`)**, yet every class sum `∑' τ, (if w τ = w τ₀ then q τ else 0) = q τ₀ ≠ 0`
     is nonzero. Thus top-down class extraction and span closure fail whenever moduli accumulate at
     a supremum from below.
   - *Single-prime Toeplitz blindness (`exists_symmetric_wolff_toeplitz_blind_configuration`):*
     On any strip `1/2 < Re ρ < 1/2 + Θ` (`Θ > 0, ℓ > 0`), the symmetric Wolff configuration
     (`RHTower.exists_symmetric_lag_configuration_vanishing_samples`) has real parts in
     `(1/2, 1/2 + Θ)` strictly increasing to `1/2 + Θ` (failing `WellFoundedOn (· > ·)`), locally
     finite ordinates (`∀ T, {i | |Im ρ_i| ≤ T}.Finite`), infinitely many distinct outer Frobenius
     eigenvalues `frobEig ℓ (ρ_i)`, and positive summable weights `c_i > 0` such that every nonzero
     Laurent moment `m ≠ 0` vanishes while the `m = 0` moment is `4 ∑' i, c_i > 0`. On **every**
     finite window `K : Finset ℤ`, its Toeplitz matrix is the positive scalar multiple
     `(4 ∑' i, c_i) • 1` with `hermNegIndex = 0`, and adding it to any nonnegative Toeplitz form
     `H₀` preserves `hermNegIndex (H₀ + T_K) = 0` on every window `K`.

3. **Unconditional Positive Survivors: `wfVisibleSet`, Above-Threshold Extraction, Bounded-Ordinate
   Well-Foundedness, and the One-Prime vs. Two-Prime Law
   (`not_wellFoundedOn_of_no_max`, `finite_rightZeros_of_abs_im_le`,
   `upperLevels_wellFounded_of_bounded_im`, `not_wellFounded_upperLevels_imp_unbounded_im`,
   `wfVisibleSet`, `exists_towerGram_negIndex_ge_of_le_wfVisibleSet`,
   `wfVisibleSet_sandwich_and_infinite_law`, `one_prime_vs_two_primes_complete_law`):**
   - *Vertical escape of non-well-founded levels:* Because `Z.finite_window` forces
     `{τ ∈ rightZeros Z | |τ.im| ≤ T}` to be finite for every `ZeroConfig Z` and `T : ℝ`, any level
     `ρ` whose upper zeros have bounded ordinates has `(upperLevels Z ρ).WellFoundedOn (· > ·)`;
     contrapositively, any failure of `(· > ·)`-well-foundedness in a `ZeroConfig` forces the upper
     zeros to escape vertically (`∀ T, ∃ τ ∈ rightZeros Z, ρ.re ≤ τ.re ∧ T < |τ.im|`).
   - *Unconditional two-sided sandwich via `wfVisibleSet`:* Defining `wfVisibleSet Z g ℓ` as the set
     of visible outer eigenvalues whose `upperLevels` is `(· > ·)`-well-founded, **every** tempered
     configuration `Z` (with no global well-foundedness or finiteness hypothesis) satisfies:
     `(n : ℕ∞) ≤ (wfVisibleSet Z g ℓ).encard → ∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g ℓ K)`.
     In particular, every visible outer eigenvalue sitting above a threshold `β_*` that has only
     finitely many right zeros above `β_*` belongs to `wfVisibleSet Z g ℓ` and is seen by one prime
     even when `Z` contains a non-well-founded Wolff-type sequence below `β_*`.
   - *Two-prime rescue:* While a single prime `p` projects `(Re ρ, Im ρ)` to `p^{ρ - 1/2}` and is
     vulnerable to both resonant-prime collisions and Wolff annulus moment cancellation at
     non-attained tops, any two distinct primes `p ≠ q` generate dense shifts `twoPrimeShifts p q`
     in `[0, ∞)` and unconditionally recover the full defect `(rightZeros Z).encard` for **every**
     tempered configuration `Z`.
-/

open Complex Matrix Finset Filter Topology Set
open scoped ComplexConjugate Classical lp BigOperators
open Zeta23 GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.SquareRootThreshold (TemperedConfig)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-! ## 1. Exact Toeplitz Laurent-Moment Representation of `towerGram` -/

/-- The `m`-th two-sided Laurent moment of the Frobenius weights of `(Z, g)` at scale `ℓ`:
`M(m) = ∑' τ : Z.carrier, X_τ(g) conj(X_{1-τ̄}(g)) β(τ)^m`. -/
def towerMoment (Z : ZeroConfig) (g : ℝ → ℂ) (ℓ : ℝ) (m : ℤ) : ℂ :=
  ∑' τ : Z.carrier,
    zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ)) * frobEig ℓ τ ^ m

/-- Bound on `‖frobEig ℓ τ ^ m‖` across the critical strip `0 ≤ Re τ ≤ 1` for `0 < ℓ` and `m : ℤ`. -/
theorem norm_frobEig_zpow_le (Z : ZeroConfig) {ℓ : ℝ} (hℓ : 0 < ℓ) (τ : Z.carrier) (m : ℤ) :
    ‖frobEig ℓ τ ^ m‖ ≤ Real.exp (ℓ / 2) ^ m.natAbs := by
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg m
  · rw [zpow_natCast, norm_pow, Int.natAbs_natCast]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    have h := norm_conj_frobEig_le Z hℓ τ
    rwa [Complex.norm_conj] at h
  · rw [_root_.zpow_neg, zpow_natCast, ← inv_pow, norm_pow, Int.natAbs_neg, Int.natAbs_natCast]
    refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
    have h := norm_inv_conj_frobEig_le Z hℓ τ
    rwa [norm_inv, Complex.norm_conj, ← norm_inv] at h

/-- For a tempered configuration `Z` and compactly supported `C²` test `g`, the Laurent moment
series `towerMoment Z g ℓ m` is absolutely summable for every `m : ℤ`. -/
theorem summable_towerMoment_term (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ) (m : ℤ) :
    Summable fun τ : Z.carrier =>
      ‖zeroCoord Z g τ * conj (zeroCoord Z g (reflectCarrier Z τ)) * frobEig ℓ τ ^ m‖ := by
  refine Summable.of_norm_bounded
    ((summable_zeroCoord_mul_reflect Z hZ hg hgc).mul_right (Real.exp (ℓ / 2) ^ m.natAbs))
    fun τ => ?_
  rw [Real.norm_of_nonneg (norm_nonneg _), norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_frobEig_zpow_le Z hℓ τ m) (norm_nonneg _)

/-- **Exact Toeplitz Laurent-Moment Formula for `towerGram`.**
For every tempered configuration `Z`, compactly supported `C²` test `g`, scale `ℓ`, and finite
window `K : Finset ℤ`, the `(j, k)`-entry of `towerGram Z g ℓ K` equals the Laurent moment
`towerMoment Z g ℓ (j - k)`. -/
theorem towerGram_apply_eq_towerMoment (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ}
    (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) (ℓ : ℝ) (K : Finset ℤ) (j k : K) :
    towerGram Z g ℓ K j k = towerMoment Z g ℓ ((j : ℤ) - (k : ℤ)) := by
  have hW : towerGram Z g ℓ K j k =
      inner ℂ (reflectVec Z (towerVec Z hZ hg hgc ℓ k)) (towerVec Z hZ hg hgc ℓ j) :=
    W_eq_inner Z hZ (translateTest hg hgc (((j : ℤ) : ℝ) * ℓ))
      (translateTest hg hgc (((k : ℤ) : ℝ) * ℓ))
  rw [hW, lp.inner_eq_tsum, towerMoment]
  refine tsum_congr fun τ => ?_
  simp only [RCLike.inner_apply', reflectVec_apply, towerVec_apply]
  have hrefl : frobEig ℓ ((reflectCarrier Z τ : Z.carrier) : ℂ) = (conj (frobEig ℓ τ))⁻¹ :=
    frobEig_reflect ℓ τ
  rw [hrefl, map_mul, map_zpow₀, map_inv₀, Complex.conj_conj, _root_.inv_zpow, ← _root_.zpow_neg,
    sub_eq_add_neg, zpow_add₀ (frobEig_ne_zero ℓ τ)]
  ring

/-- **Laurent-Moment Rigidity of `towerGram` and Its Negative Index.**
If two tempered configurations `(Z₁, g₁)` and `(Z₂, g₂)` have the same two-sided Laurent moments
`towerMoment Z₁ g₁ ℓ m = towerMoment Z₂ g₂ ℓ m` for all `m ∈ ℤ`, then `towerGram Z₁ g₁ ℓ K =
towerGram Z₂ g₂ ℓ K` and `hermNegIndex (towerGram Z₁ g₁ ℓ K) = hermNegIndex (towerGram Z₂ g₂ ℓ K)`
on every finite window `K : Finset ℤ`. -/
theorem towerGram_eq_of_towerMoment_eq (Z₁ Z₂ : ZeroConfig) (hZ₁ : TemperedConfig Z₁)
    (hZ₂ : TemperedConfig Z₂) {g₁ g₂ : ℝ → ℂ} (hg₁ : ContDiff ℝ 2 g₁)
    (hgc₁ : HasCompactSupport g₁) (hg₂ : ContDiff ℝ 2 g₂) (hgc₂ : HasCompactSupport g₂)
    (ℓ : ℝ) (hmom : ∀ m : ℤ, towerMoment Z₁ g₁ ℓ m = towerMoment Z₂ g₂ ℓ m) (K : Finset ℤ) :
    towerGram Z₁ g₁ ℓ K = towerGram Z₂ g₂ ℓ K ∧
      hermNegIndex (towerGram Z₁ g₁ ℓ K) = hermNegIndex (towerGram Z₂ g₂ ℓ K) := by
  have hmat : towerGram Z₁ g₁ ℓ K = towerGram Z₂ g₂ ℓ K := by
    ext j k
    rw [towerGram_apply_eq_towerMoment Z₁ hZ₁ hg₁ hgc₁ ℓ K j k,
      towerGram_apply_eq_towerMoment Z₂ hZ₂ hg₂ hgc₂ ℓ K j k, hmom]
  exact ⟨hmat, congrArg hermNegIndex hmat⟩

/-! ## 2. The Two-Annulus Laurent-Orthogonal Obstruction and Single-Prime Toeplitz Blindness -/

/-- **Normalized Positive Wolff Measure on an Open Annulus (`0 < r < R`).**
Normalizing `PositiveWolffMeasure.exists_positive_wolff_annulus` by `π(R² − r²)` yields a countable
subset `t ⊆ annulus r R` accumulating at the outer boundary `|z| = R` and positive weights `w` of
total mass `1` whose nonzero two-sided Laurent moments `m ∈ ℤ \ {0}` all vanish. -/
theorem exists_normalized_positive_wolff_annulus {r R : ℝ} (hr : 0 < r) (hrR : r < R) :
    ∃ (t : Set ℂ) (w : ℂ → ℝ), t.Countable ∧ t.Nonempty ∧ t ⊆ PositiveWolffMeasure.annulus r R ∧
      (∀ x ∈ t, 0 < w x) ∧ (∀ R' < R, ∃ x ∈ t, R' < ‖x‖) ∧
      HasSum (fun x : t => w x) 1 ∧
      (∀ m : ℤ, m ≠ 0 → HasSum (fun x : t => (w x : ℂ) * (x : ℂ) ^ m) 0) := by
  obtain ⟨t, c, htc, htA, hc, hacc, hmass, hmom, hinv⟩ :=
    PositiveWolffMeasure.exists_positive_wolff_annulus hr.le hrR
  have hR0 : 0 < R := hr.trans hrR
  have hsq : r ^ 2 < R ^ 2 := sq_lt_sq.mpr (by rw [abs_of_pos hr, abs_of_pos hR0]; exact hrR)
  set M : ℝ := Real.pi * (R ^ 2 - r ^ 2) with hMdef
  have hM : 0 < M := mul_pos Real.pi_pos (sub_pos.mpr hsq)
  obtain ⟨x₀, hx₀t, -⟩ := hacc r hrR
  refine ⟨t, fun x => c x / M, htc, ⟨x₀, hx₀t⟩, htA,
    fun x hx => div_pos (hc x hx) hM, hacc, ?_, ?_⟩
  · have h1 := hmass.mul_right M⁻¹
    rw [mul_inv_cancel₀ hM.ne'] at h1
    exact h1.congr_fun fun x => by simp [div_eq_mul_inv]
  · intro m hm
    rcases Int.eq_nat_or_neg m with ⟨k, rfl | rfl⟩
    · have hk : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · exact absurd (by rw [h]; rfl) hm
        · exact h
      have h1 := (hmom k hk).mul_left ((M : ℂ)⁻¹)
      rw [mul_zero] at h1
      refine h1.congr_fun fun x => ?_
      rw [zpow_natCast]
      push_cast
      ring
    · have hk : 1 ≤ k := by
        rcases Nat.eq_zero_or_pos k with h | h
        · exact absurd (by rw [h]; rfl) hm
        · exact h
      have h1 := (hinv hr k hk).mul_left ((M : ℂ)⁻¹)
      rw [mul_zero] at h1
      refine h1.congr_fun fun x => ?_
      rw [_root_.zpow_neg, zpow_natCast]
      push_cast
      ring

/-- **Criterion for Failure of `(· > ·)`-Well-Foundedness.**
Any nonempty set `S : Set ℝ` without a strict maximum element (`∀ y ∈ S, ∃ z ∈ S, y < z`) is not
well-founded with respect to `(· > ·)`. -/
theorem not_wellFoundedOn_of_no_max {S : Set ℝ} (hS : S.Nonempty)
    (hstep : ∀ y ∈ S, ∃ z ∈ S, y < z) : ¬ S.WellFoundedOn (· > ·) := by
  intro hwf
  obtain ⟨x₀, hx₀⟩ := hS
  exact hwf.induction hx₀ (P := fun _ => False) fun y hy IH =>
    let ⟨z, hz, hyz⟩ := hstep y hy
    IH z hz hyz

/-- **Two-Annulus Counterexample to Laurent Class Extraction Without Well-Foundedness.**
For any `0 < r₁ < R₁ ≤ r₂ < R₂`, taking the difference of the normalized positive Wolff measures on
the disjoint annuli `annulus r₁ R₁` and `annulus r₂ R₂` produces a countable, nonempty index type
`T`, an injective map `w : T → ℂ` with `r₁ < ‖w τ‖ < R₂`, and nonzero weights `q : T → ℂ` with
`∑' τ, ‖q τ‖ = 2` such that:
1. **All two-sided Laurent moments vanish (`m ∈ ℤ`, including `m = 0`):**
   `∀ m : ℤ, HasSum (fun τ : T => q τ * w τ ^ m) 0` and `∑' τ : T, q τ * w τ ^ m = 0`;
2. **Every class sum is nonzero:** for every `τ₀ : T`,
   `∑' τ : T, (if w τ = w τ₀ then q τ else 0) = q τ₀ ≠ 0`;
3. **Every upper-modulus set fails `(· > ·)`-well-foundedness:** for every `τ₀ : T`,
   `¬ {x : ℝ | ∃ τ : T, ‖w τ‖ = x ∧ ‖w τ₀‖ ≤ x}.WellFoundedOn (· > ·)`.

This proves that the well-foundedness hypothesis in `tsum_ite_eq_zero_of_moments_of_wellFounded`
cannot be dropped even when all positive, zero, and negative Laurent moments vanish simultaneously. -/
theorem exists_counterexample_to_laurent_class_extraction_without_wellFounded
    {r₁ R₁ r₂ R₂ : ℝ} (hr₁ : 0 < r₁) (hR₁ : r₁ < R₁) (h12 : R₁ ≤ r₂) (hR₂ : r₂ < R₂) :
    ∃ (T : Type) (_ : Countable T) (_ : Nonempty T) (q w : T → ℂ),
      Function.Injective w ∧
      (∀ τ : T, r₁ < ‖w τ‖ ∧ ‖w τ‖ < R₂) ∧
      (∀ τ : T, q τ ≠ 0) ∧
      HasSum (fun τ : T => ‖q τ‖) 2 ∧
      (∀ m : ℤ, HasSum (fun τ : T => q τ * w τ ^ m) 0 ∧ ∑' τ : T, q τ * w τ ^ m = 0) ∧
      (∀ τ₀ : T, ∑' τ : T, (if w τ = w τ₀ then q τ else 0) = q τ₀) ∧
      (∀ τ₀ : T, ¬ {x : ℝ | ∃ τ : T, ‖w τ‖ = x ∧ ‖w τ₀‖ ≤ x}.WellFoundedOn (· > ·)) := by
  have hr₂ : 0 < r₂ := (hr₁.trans hR₁).trans_le h12
  obtain ⟨t₁, w₁, htc₁, hne₁, htA₁, hw₁pos, hacc₁, hmass₁, hmom₁⟩ :=
    exists_normalized_positive_wolff_annulus hr₁ hR₁
  obtain ⟨t₂, w₂, htc₂, hne₂, htA₂, hw₂pos, hacc₂, hmass₂, hmom₂⟩ :=
    exists_normalized_positive_wolff_annulus hr₂ hR₂
  haveI : Countable t₁ := htc₁.to_subtype
  haveI : Countable t₂ := htc₂.to_subtype
  obtain ⟨x₁₀, hx₁₀⟩ := hne₁
  set T := t₁ ⊕ t₂
  haveI : Nonempty T := ⟨Sum.inl ⟨x₁₀, hx₁₀⟩⟩
  set w : T → ℂ := Sum.elim (fun x : t₁ => (x : ℂ)) (fun y : t₂ => (y : ℂ)) with hwdef
  set q : T → ℂ := Sum.elim (fun x : t₁ => (w₁ x : ℂ)) (fun y : t₂ => -((w₂ y : ℂ))) with hqdef
  have hnorm₁ : ∀ x : t₁, r₁ < ‖(x : ℂ)‖ ∧ ‖(x : ℂ)‖ < R₁ := fun x => htA₁ x.2
  have hnorm₂ : ∀ y : t₂, r₂ < ‖(y : ℂ)‖ ∧ ‖(y : ℂ)‖ < R₂ := fun y => htA₂ y.2
  have hinj : Function.Injective w := by
    rintro (x | y) (x' | y') h
    · exact congrArg Sum.inl (Subtype.ext h)
    · exfalso
      have h1 := (hnorm₁ x).2
      have h2 := (hnorm₂ y').1
      have heq : ‖(x : ℂ)‖ = ‖(y' : ℂ)‖ := congrArg norm h
      linarith
    · exfalso
      have h1 := (hnorm₁ x').2
      have h2 := (hnorm₂ y).1
      have heq : ‖(y : ℂ)‖ = ‖(x' : ℂ)‖ := congrArg norm h
      linarith
    · exact congrArg Sum.inr (Subtype.ext h)
  have hwb : ∀ τ : T, r₁ < ‖w τ‖ ∧ ‖w τ‖ < R₂ := by
    rintro (x | y)
    · exact ⟨(hnorm₁ x).1, (hnorm₁ x).2.trans (h12.trans_lt hR₂)⟩
    · exact ⟨hR₁.trans (h12.trans_lt (hnorm₂ y).1), (hnorm₂ y).2⟩
  have hq0 : ∀ τ : T, q τ ≠ 0 := by
    rintro (x | y)
    · exact Complex.ofReal_ne_zero.mpr (hw₁pos x x.2).ne'
    · exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr (hw₂pos y y.2).ne')
  have hqnorm : HasSum (fun τ : T => ‖q τ‖) 2 := by
    have hL : HasSum ((fun τ : T => ‖q τ‖) ∘ Sum.inl) 1 := by
      refine hmass₁.congr_fun fun x => ?_
      rw [Function.comp_apply]
      dsimp [q]
      exact Complex.norm_of_nonneg (hw₁pos x x.2).le
    have hR : HasSum ((fun τ : T => ‖q τ‖) ∘ Sum.inr) 1 := by
      refine hmass₂.congr_fun fun y => ?_
      rw [Function.comp_apply]
      dsimp [q]
      rw [norm_neg]
      exact Complex.norm_of_nonneg (hw₂pos y y.2).le
    simpa only [one_add_one_eq_two] using hL.sum hR
  have hlaurent : ∀ m : ℤ, HasSum (fun τ : T => q τ * w τ ^ m) 0 := by
    intro m
    by_cases hm0 : m = 0
    · subst hm0
      have hL : HasSum ((fun τ : T => q τ * w τ ^ (0 : ℤ)) ∘ Sum.inl) 1 := by
        have h := Complex.hasSum_ofReal.mpr hmass₁
        refine h.congr_fun fun x => ?_
        simp [q, w]
      have hR : HasSum ((fun τ : T => q τ * w τ ^ (0 : ℤ)) ∘ Sum.inr) (-1) := by
        have h := (Complex.hasSum_ofReal.mpr hmass₂).neg
        refine h.congr_fun fun y => ?_
        simp [q, w]
      simpa using hL.sum hR
    · have hL : HasSum ((fun τ : T => q τ * w τ ^ m) ∘ Sum.inl) 0 := hmom₁ m hm0
      have hR : HasSum ((fun τ : T => q τ * w τ ^ m) ∘ Sum.inr) 0 := by
        have h := (hmom₂ m hm0).neg
        rw [neg_zero] at h
        refine h.congr_fun fun y => ?_
        simp [q, w]
      simpa using hL.sum hR
  refine ⟨T, inferInstance, inferInstance, q, w, hinj, hwb, hq0, hqnorm,
    fun m => ⟨hlaurent m, (hlaurent m).tsum_eq⟩, fun τ₀ => ?_, fun τ₀ => ?_⟩
  · rw [tsum_eq_single τ₀]
    · simp
    · intro τ hτ
      exact if_neg (fun h => hτ (hinj h))
  · refine not_wellFoundedOn_of_no_max ⟨‖w τ₀‖, τ₀, rfl, le_rfl⟩ ?_
    rintro y ⟨τ, rfl, hle⟩
    have hyR₂ : ‖w τ‖ < R₂ := (hwb τ).2
    obtain ⟨z, hzt₂, hz⟩ := hacc₂ ‖w τ‖ hyR₂
    exact ⟨‖(z : ℂ)‖, ⟨Sum.inr ⟨z, hzt₂⟩, rfl, hle.trans hz.le⟩, hz⟩

/-- The quadratic form of a nonnegative real scalar multiple of the identity matrix `(A : ℂ) • 1`
is `A * ∑ k, ‖x k‖ ^ 2 ≥ 0`. -/
theorem hermQuad_real_smul_one {ι : Type*} [Fintype ι] [DecidableEq ι] (A : ℝ) (x : ι → ℂ) :
    hermQuad ((A : ℂ) • (1 : Matrix ι ι ℂ)) x = A * ∑ i : ι, ‖x i‖ ^ 2 := by
  simp only [hermQuad, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul, smul_eq_mul,
    Complex.re_ofReal_mul]
  congr 1
  simp only [dotProduct]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Pi.star_apply, RCLike.star_def, Complex.conj_mul', ← Complex.ofReal_pow,
    Complex.ofReal_re]

/-- Adding a nonnegative scalar multiple `(A : ℂ) • 1` (`0 ≤ A`) to any matrix `H₀` with
nonnegative quadratic form preserves `hermNegIndex = 0`. -/
theorem hermNegIndex_add_real_smul_one_eq_zero {ι : Type*} [Fintype ι] [DecidableEq ι]
    {H₀ : Matrix ι ι ℂ} (hH₀ : ∀ x : ι → ℂ, 0 ≤ hermQuad H₀ x) {A : ℝ} (hA : 0 ≤ A) :
    hermNegIndex (H₀ + (A : ℂ) • (1 : Matrix ι ι ℂ)) = 0 := by
  refine negIndex_eq_zero_of_hermQuad_nonneg fun x => ?_
  have hadd : hermQuad (H₀ + (A : ℂ) • (1 : Matrix ι ι ℂ)) x =
      hermQuad H₀ x + hermQuad ((A : ℂ) • (1 : Matrix ι ι ℂ)) x := by
    simp only [hermQuad, Matrix.add_mulVec, dotProduct_add, Complex.add_re]
  rw [hadd, hermQuad_real_smul_one]
  have hsum : 0 ≤ ∑ i : ι, ‖x i‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  exact add_nonneg (hH₀ x) (mul_nonneg hA hsum)

/-- **Single-Prime Toeplitz Blindness to the Symmetric Wolff Configuration at a Non-Attained Top.**
For every scale `ℓ > 0` and strip width `Θ > 0`, there is a countable, nonempty, injective family
of off-line points `ρ : ι → ℂ` in `1/2 < Re ρ < 1/2 + Θ` with locally finite ordinates
(`∀ T, {i | |Im ρ_i| ≤ T}.Finite`) and positive summable weights `c : ι → ℝ` (`0 < c_i`) such that:
1. **Non-well-founded real parts:** the real parts `(ρ i).re` strictly increase toward `1/2 + Θ`
   and fail `WellFoundedOn (· > ·)`;
2. **Infinitely many outer Frobenius eigenvalue moduli:** `1 < ‖frobEig ℓ (ρ i)‖ < e^{Θℓ}` and
   `(Set.range (fun i => frobEig ℓ (ρ i))).Infinite`;
3. **Vanishing off-diagonal Laurent moments:** the symmetric four-point Laurent moment sequence
   `M(m) := ∑' i, (c i : ℂ) * RHTower.symLagSample ℓ (ρ i) m` satisfies `M(m) = 0` for every
   `m ≠ 0` and `M(0) = 4 * ∑' i, c i` with `0 < ∑' i, c i`;
4. **Zero negative index on every finite window:** for **every** finite window `K : Finset ℤ` and
   every matrix `H₀ : Matrix K K ℂ` with nonnegative quadratic form (such as any critical-line
   Herglotz Toeplitz form), the Toeplitz matrix `T_K(j, k) = M(j - k)` equals
   `(4 * ∑' i, c i) • 1`, and both `T_K` and `H₀ + T_K` have `hermNegIndex = 0`! -/
theorem exists_symmetric_wolff_toeplitz_blind_configuration {ℓ Θ : ℝ} (hℓ : 0 < ℓ) (hΘ : 0 < Θ) :
    ∃ (ι : Type) (_ : Countable ι) (_ : Nonempty ι) (ρ : ι → ℂ) (c : ι → ℝ),
      Function.Injective ρ ∧
      (∀ i, 1 / 2 < (ρ i).re ∧ (ρ i).re < 1 / 2 + Θ) ∧
      (∀ β < 1 / 2 + Θ, ∃ i, β < (ρ i).re) ∧
      ¬ (Set.range (fun i => (ρ i).re)).WellFoundedOn (· > ·) ∧
      (Set.range (fun i => frobEig ℓ (ρ i))).Infinite ∧
      (∀ T : ℝ, {i | |(ρ i).im| ≤ T}.Finite) ∧
      (∀ i, 0 < c i) ∧ Summable c ∧ 0 < (∑' i, c i) ∧
      (∀ m : ℤ,
        ∑' i, (c i : ℂ) * RHTower.symLagSample ℓ (ρ i) m =
          if m = 0 then ((4 * ∑' i, c i : ℝ) : ℂ) else 0) ∧
      (∀ (K : Finset ℤ),
        Matrix.of (fun j k : K =>
          ∑' i, (c i : ℂ) * RHTower.symLagSample ℓ (ρ i) ((j : ℤ) - (k : ℤ))) =
          ((4 * ∑' i, c i : ℝ) : ℂ) • (1 : Matrix K K ℂ) ∧
        hermNegIndex (Matrix.of (fun j k : K =>
          ∑' i, (c i : ℂ) * RHTower.symLagSample ℓ (ρ i) ((j : ℤ) - (k : ℤ)))) = 0 ∧
        ∀ H₀ : Matrix K K ℂ, (∀ x : K → ℂ, 0 ≤ hermQuad H₀ x) →
          hermNegIndex (H₀ + Matrix.of (fun j k : K =>
            ∑' i, (c i : ℂ) * RHTower.symLagSample ℓ (ρ i) ((j : ℤ) - (k : ℤ)))) = 0) := by
  obtain ⟨ι, hcnt, ρ, c, hinj_ρ, hstrip, hacc, hloc, hcpos, hcsum, hvan⟩ :=
    RHTower.exists_symmetric_lag_configuration_vanishing_samples hℓ hΘ
  obtain ⟨i₀, _⟩ := hacc (1 / 2) (by linarith)
  haveI : Nonempty ι := ⟨i₀⟩
  have hnot_wf : ¬ (Set.range (fun i => (ρ i).re)).WellFoundedOn (· > ·) := by
    refine not_wellFoundedOn_of_no_max ⟨(ρ i₀).re, i₀, rfl⟩ ?_
    rintro y ⟨i, rfl⟩
    obtain ⟨j, hj⟩ := hacc (ρ i).re (hstrip i).2
    exact ⟨(ρ j).re, ⟨j, rfl⟩, hj⟩
  have hinf_frob : (Set.range (fun i => frobEig ℓ (ρ i))).Infinite := by
    intro hfin
    have hre_sub : Set.range (fun i => (ρ i).re) ⊆
        (fun z : ℂ => Real.log ‖z‖ / ℓ + 1 / 2) '' Set.range (fun i => frobEig ℓ (ρ i)) := by
      rintro σ ⟨i, rfl⟩
      refine ⟨frobEig ℓ (ρ i), ⟨i, rfl⟩, ?_⟩
      dsimp only
      rw [norm_frobEig, Real.log_exp, mul_div_cancel_left₀ _ hℓ.ne', sub_add_cancel]
    exact hnot_wf ((hfin.image _).subset hre_sub).wellFoundedOn
  have htsum_pos : 0 < ∑' i, c i :=
    hcsum.tsum_pos (fun i => (hcpos i).le) i₀ (hcpos i₀)
  have hmom : ∀ m : ℤ,
      ∑' i, (c i : ℂ) * RHTower.symLagSample ℓ (ρ i) m =
        if m = 0 then ((4 * ∑' i, c i : ℝ) : ℂ) else 0 := by
    intro m
    split_ifs with hm0
    · subst hm0
      have h0 : ∀ i, RHTower.symLagSample ℓ (ρ i) 0 = 4 := by
        intro i
        unfold RHTower.symLagSample
        norm_num
      simp_rw [h0, ← mul_comm (4 : ℂ), tsum_mul_left, ← Complex.ofReal_tsum]
      push_cast
      ring
    · exact (hvan m hm0).tsum_eq
  refine ⟨ι, hcnt, inferInstance, ρ, c, hinj_ρ, hstrip, hacc, hnot_wf, hinf_frob, hloc,
    hcpos, hcsum, htsum_pos, hmom, fun K => ?_⟩
  have hmat : Matrix.of (fun j k : K =>
      ∑' i, (c i : ℂ) * RHTower.symLagSample ℓ (ρ i) ((j : ℤ) - (k : ℤ))) =
      ((4 * ∑' i, c i : ℝ) : ℂ) • (1 : Matrix K K ℂ) := by
    ext j k
    rw [Matrix.of_apply, hmom ((j : ℤ) - (k : ℤ)), Matrix.smul_apply, Matrix.one_apply]
    by_cases hjk : j = k
    · subst hjk
      simp
    · have hsub : (j : ℤ) - (k : ℤ) ≠ 0 :=
        sub_ne_zero.mpr (fun h => hjk (Subtype.ext h))
      rw [if_neg hsub, if_neg hjk, smul_zero]
  have hA0 : 0 ≤ 4 * ∑' i, c i := by positivity
  refine ⟨hmat, ?_, fun H₀ hH₀ => ?_⟩
  · rw [hmat]
    have h0 := hermNegIndex_add_real_smul_one_eq_zero (H₀ := (0 : Matrix K K ℂ))
      (fun x => by simp [hermQuad]) hA0
    simpa using h0
  · rw [hmat]
    exact hermNegIndex_add_real_smul_one_eq_zero hH₀ hA0

/-! ## 3. Unconditional Positive Survivors: `wfVisibleSet`, Above-Threshold Extraction, and Bounded-Ordinate Well-Foundedness -/

/-- For every `ZeroConfig Z` and height bound `T : ℝ`, the set of right zeros with `|Im τ| ≤ T`
is finite. -/
theorem finite_rightZeros_of_abs_im_le (Z : ZeroConfig) (T : ℝ) :
    {τ ∈ rightZeros Z | |τ.im| ≤ T}.Finite := by
  refine (Z.finite_window (-|T| - 1) |T|).subset fun τ ⟨hτ, him⟩ => ?_
  refine ⟨hτ.1, ?_, ?_⟩
  · linarith [neg_abs_le τ.im, le_abs_self T, him]
  · exact (le_abs_self τ.im).trans (him.trans (le_abs_self T))

/-- **Bounded-Ordinate Well-Foundedness of `upperLevels Z ρ`.**
If all right zeros of `Z` at or above `Re ρ` have bounded ordinates `|Im τ| ≤ T`, then
`upperLevels Z ρ` is finite and therefore `(· > ·)`-well-founded. -/
theorem upperLevels_wellFounded_of_bounded_im (Z : ZeroConfig) (ρ : ℂ) {T : ℝ}
    (hbdd : ∀ τ ∈ rightZeros Z, ρ.re ≤ τ.re → |τ.im| ≤ T) :
    (upperLevels Z ρ).Finite ∧ (upperLevels Z ρ).WellFoundedOn (· > ·) := by
  have hfin : (upperLevels Z ρ).Finite := by
    refine ((finite_rightZeros_of_abs_im_le Z T).image Complex.re).subset ?_
    rintro σ ⟨τ, hτ, rfl, hle⟩
    exact ⟨τ, ⟨hτ, hbdd τ hτ hle⟩, rfl⟩
  exact ⟨hfin, hfin.wellFoundedOn⟩

/-- **Vertical Escape of Non-Well-Founded Upper Levels.**
In any `ZeroConfig Z`, if `upperLevels Z ρ` is not `(· > ·)`-well-founded, then for every height
bound `T : ℝ` there exists a right zero `τ ∈ rightZeros Z` with `ρ.re ≤ τ.re` and `T < |τ.im|`. -/
theorem not_wellFounded_upperLevels_imp_unbounded_im (Z : ZeroConfig) (ρ : ℂ)
    (hnwf : ¬ (upperLevels Z ρ).WellFoundedOn (· > ·)) (T : ℝ) :
    ∃ τ ∈ rightZeros Z, ρ.re ≤ τ.re ∧ T < |τ.im| := by
  by_contra h
  push Not at h
  exact hnwf (upperLevels_wellFounded_of_bounded_im Z ρ h).2

/-- The **well-founded visible set** `wfVisibleSet Z g ℓ`: visible outer Frobenius eigenvalues
`b ∈ visibleSet Z g ℓ` represented by a right zero `ρ` whose `upperLevels Z ρ` is
`(· > ·)`-well-founded. -/
def wfVisibleSet (Z : ZeroConfig) (g : ℝ → ℂ) (ℓ : ℝ) : Set ℂ :=
  {b | b ∈ visibleSet Z g ℓ ∧ ∃ ρ ∈ rightZeros Z, frobEig ℓ ρ = b ∧
    (upperLevels Z ρ).WellFoundedOn (· > ·)}

theorem wfVisibleSet_subset_visibleSet (Z : ZeroConfig) (g : ℝ → ℂ) (ℓ : ℝ) :
    wfVisibleSet Z g ℓ ⊆ visibleSet Z g ℓ :=
  fun _ hb => hb.1

/-- When `(Complex.re '' rightZeros Z).WellFoundedOn (· > ·)`, every visible outer eigenvalue has
well-founded upper levels, so `wfVisibleSet Z g ℓ = visibleSet Z g ℓ`. -/
theorem wfVisibleSet_eq_visibleSet_of_wellFounded (Z : ZeroConfig) (g : ℝ → ℂ) (ℓ : ℝ)
    (hWF : (Complex.re '' rightZeros Z).WellFoundedOn (· > ·)) :
    wfVisibleSet Z g ℓ = visibleSet Z g ℓ := by
  ext b
  refine ⟨fun hb => hb.1, fun hb => ⟨hb, ?_⟩⟩
  obtain ⟨ρ, hρ, rfl⟩ := hb.1
  refine ⟨ρ, hρ, rfl, hWF.mono le_rfl ?_⟩
  rintro σ ⟨τ, hτ, rfl, -⟩
  exact ⟨τ, hτ, rfl⟩

/-- **Above-Threshold Well-Founded Extraction.**
Even if `Z` contains a non-well-founded increasing sequence of real parts approaching a threshold
`β_*` from below, if only finitely many right zeros of `Z` have real part strictly above `β_*`
(`{τ ∈ rightZeros Z | β_* < τ.re}.Finite`), then every visible outer eigenvalue `b = frobEig ℓ ρ`
with `β_* < ρ.re` belongs to `wfVisibleSet Z g ℓ`. -/
theorem mem_wfVisibleSet_of_finite_above (Z : ZeroConfig) (g : ℝ → ℂ) (ℓ : ℝ) {β_star : ℝ}
    (hfin : {τ ∈ rightZeros Z | β_star < τ.re}.Finite) {ρ : ℂ} (hρ : ρ ∈ rightZeros Z)
    (hβ : β_star < ρ.re) (hvis : frobEig ℓ ρ ∈ visibleSet Z g ℓ) :
    frobEig ℓ ρ ∈ wfVisibleSet Z g ℓ := by
  refine ⟨hvis, ρ, hρ, rfl, ?_⟩
  refine ((hfin.image Complex.re).subset ?_).wellFoundedOn
  rintro σ ⟨τ, hτ, rfl, hle⟩
  exact ⟨τ, ⟨hτ, hβ.trans_le hle⟩, rfl⟩

/-- **Unconditional Single-Prime Lower Bound from `wfVisibleSet`.**
For **every** tempered configuration `Z` (with no global well-foundedness or finiteness hypothesis
on `rightZeros Z`), every `(n : ℕ∞) ≤ (wfVisibleSet Z g ℓ).encard` is realized as
`n ≤ hermNegIndex (towerGram Z g ℓ K)` on some finite window `K : Finset ℤ`. -/
theorem exists_towerGram_negIndex_ge_of_le_wfVisibleSet (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ)
    {n : ℕ} (hn : (n : ℕ∞) ≤ (wfVisibleSet Z g ℓ).encard) :
    ∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g ℓ K) := by
  obtain ⟨t, hts, htc⟩ := Set.exists_subset_encard_eq hn
  have htfin : t.Finite := Set.finite_of_encard_eq_coe htc
  obtain ⟨K, hK⟩ := card_le_towerDefect_of_wellFounded Z hZ hg hgc hℓ htfin.toFinset
    (fun b hb => (hts (htfin.mem_toFinset.mp hb)).1)
    (fun b hb => (hts (htfin.mem_toFinset.mp hb)).2)
  refine ⟨K, le_trans ?_ hK⟩
  have hcard : (htfin.toFinset.card : ℕ∞) = n := by
    rw [← htfin.encard_eq_coe_toFinset_card, htc]
  exact_mod_cast hcard.ge

/-- **Unconditional Two-Sided Sandwich and Infinite-`wfVisibleSet` Law for Every Tempered Configuration.**
For every tempered configuration `Z`, compactly supported `C²` test `g`, and scale `ℓ > 0`:
1. Every `(n : ℕ∞) ≤ (wfVisibleSet Z g ℓ).encard` is attained by `hermNegIndex (towerGram Z g ℓ K)`
   on some finite window `K : Finset ℤ`;
2. Every finite window `K : Finset ℤ` satisfies
   `(hermNegIndex (towerGram Z g ℓ K) : ℕ∞) ≤ (visibleSet Z g ℓ).encard ≤ (outerEig Z ℓ).encard`;
3. Whenever `(wfVisibleSet Z g ℓ).Infinite` (even if `Z` also contains non-well-founded levels
   below), the tower Pontryagin law
   `(∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g ℓ K)) ↔ (n : ℕ∞) ≤ (visibleSet Z g ℓ).encard`
   holds unconditionally for all `n : ℕ`. -/
theorem wfVisibleSet_sandwich_and_infinite_law (Z : ZeroConfig) (hZ : TemperedConfig Z)
    {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g) (hgc : HasCompactSupport g) {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∀ n : ℕ, (n : ℕ∞) ≤ (wfVisibleSet Z g ℓ).encard →
      ∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g ℓ K)) ∧
    (∀ K : Finset ℤ,
      (hermNegIndex (towerGram Z g ℓ K) : ℕ∞) ≤ (visibleSet Z g ℓ).encard ∧
      (visibleSet Z g ℓ).encard ≤ (outerEig Z ℓ).encard) ∧
    ((wfVisibleSet Z g ℓ).Infinite → ∀ n : ℕ,
      (∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g ℓ K)) ↔
        (n : ℕ∞) ≤ (visibleSet Z g ℓ).encard) := by
  have hupper : ∀ K : Finset ℤ,
      (hermNegIndex (towerGram Z g ℓ K) : ℕ∞) ≤ (visibleSet Z g ℓ).encard := by
    intro K
    by_cases hfin : (visibleSet Z g ℓ).Finite
    · rw [hfin.encard_eq_coe_toFinset_card]
      exact_mod_cast negIndex_towerGram_le_of_visible_subset Z hZ hg hgc hℓ hfin.toFinset
        (fun b hb hne => hfin.mem_toFinset.mpr ⟨hb, hne⟩) K
    · rw [Set.Infinite.encard_eq hfin]
      exact le_top
  refine ⟨fun n hn => exists_towerGram_negIndex_ge_of_le_wfVisibleSet Z hZ hg hgc hℓ hn,
    fun K => ⟨hupper K, Set.encard_le_encard (fun _ hb => hb.1)⟩,
    fun hinf n => ⟨fun ⟨K, hK⟩ => (ENat.coe_le_coe.mpr hK).trans (hupper K), fun _ => ?_⟩⟩
  refine exists_towerGram_negIndex_ge_of_le_wfVisibleSet Z hZ hg hgc hℓ ?_
  rw [Set.Infinite.encard_eq hinf]
  exact le_top

/-! ## 4. Complete One-Prime vs. Two-Prime Comparison Theorem -/

/-- **Complete Resolution of Open Problem 7: One Prime Against Two.**
For any two distinct primes `p ≠ q`, any tempered configuration `Z`, and any compactly supported
`C²` spectrally generic test `g`:
1. **Single-Prime Toeplitz Laurent-Moment Law:** On the tower of `p` (`ℓ = log p`),
   `towerGram Z g (log p) K j k = towerMoment Z g (log p) (j - k)` depends on `(Z, g)` exclusively
   through the two-sided Laurent moments `m ↦ towerMoment Z g (log p) m`.
2. **Unconditional Single-Prime Extraction on `wfVisibleSet`:** Every `(n : ℕ∞) ≤
   (wfVisibleSet Z g (log p)).encard` is seen by `towerGram Z g (log p) K` on some finite window
   `K : Finset ℤ`, and any level failing `(· > ·)`-well-foundedness must escape vertically to
   `|Im τ| → ∞`.
3. **Wolff Annulus Obstruction at Non-Attained Tops:** When real parts strictly increase to their
   supremum `1/2 + Θ`, the symmetric Wolff configuration on `(1/2, 1/2 + Θ)` has infinitely many
   outer Frobenius eigenvalues with positive summable weights `c_i > 0` yet its Toeplitz matrix on
   every finite window `K : Finset ℤ` is `(4 ∑' i, c_i) • 1` with `hermNegIndex = 0`.
4. **Unconditional Two-Prime Rescue:** The two-prime Hecke orbit `twoPrimeShifts p q` is dense in
   `[0, ∞)` and sees **every** right zero of `Z` (`(rightZeros Z).encard`), eliminating both
   resonant-prime collisions and Wolff annulus moment cancellation without any well-foundedness
   hypothesis on `rightZeros Z`. -/
theorem one_prime_vs_two_primes_complete_law {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (Z : ZeroConfig) (hZ : TemperedConfig Z) {g : ℝ → ℂ} (hg : ContDiff ℝ 2 g)
    (hgc : HasCompactSupport g) (hgen : SpectrallyGeneric Z g) :
    (∀ (K : Finset ℤ) (j k : K),
      towerGram Z g (Real.log p) K j k = towerMoment Z g (Real.log p) ((j : ℤ) - (k : ℤ))) ∧
    (∀ n : ℕ, (n : ℕ∞) ≤ (wfVisibleSet Z g (Real.log p)).encard →
      ∃ K : Finset ℤ, n ≤ hermNegIndex (towerGram Z g (Real.log p) K)) ∧
    (∀ ρ : ℂ, ¬ (upperLevels Z ρ).WellFoundedOn (· > ·) →
      ∀ T : ℝ, ∃ τ ∈ rightZeros Z, ρ.re ≤ τ.re ∧ T < |τ.im|) ∧
    (∀ n : ℕ,
      (∃ S : Finset ℝ, ↑S ⊆ twoPrimeShifts p q ∧
        n ≤ hermNegIndex (zeroGram Z fun s : S => translate s g)) ↔
      (n : ℕ∞) ≤ (rightZeros Z).encard) := by
  have hℓ : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  exact ⟨fun K j k => towerGram_apply_eq_towerMoment Z hZ hg hgc (Real.log p) K j k,
    fun n hn => exists_towerGram_negIndex_ge_of_le_wfVisibleSet Z hZ hg hgc hℓ hn,
    fun ρ hnwf T => not_wellFounded_upperLevels_imp_unbounded_im Z ρ hnwf T,
    fun n => cyclic_pontryagin_law Z hZ hg hgc hgen (denseShifts_twoPrime hp hq hpq) n⟩

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

end
