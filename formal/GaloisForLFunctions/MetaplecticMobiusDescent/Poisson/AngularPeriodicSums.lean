import GaloisForLFunctions.MetaplecticMobiusDescent.Poisson.AngularFourierProfiles
import GaloisForLFunctions.MetaplecticMobiusDescent.QuadraticSieve.DyadicDivisorBins

/-! # Rapid decay of angular periodic sums

Positive angular weight removes the zero Fourier mode independently of the finite
periodic coefficient. The nonzero lattice envelope gives rapid decay in the ratio
of the physical norm scale to the modulus norm, with finite Schwartz control.
-/

noncomputable section
set_option autoImplicit false
open Complex
open scoped Classical BigOperators SchwartzMap ComplexConjugate
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.SchwartzPlanePoisson
open Eisenstein
open GaloisForLFunctions.MetaplecticMobiusDescent.QuarticPoisson
local notation "O" => Eisenstein.O

/-- The nonzero dual lattice preserves arbitrary decay in the dilation. -/
theorem paperAngularFourier_nonzero_lattice_bound (k A : ℕ) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ (W : 𝓢(ℝ, ℂ)),
      Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2 → ∀ t : ℝ, 0 < t →
      Summable (fun h : {h : O // h ≠ 0} =>
        ‖paperAngularFourier k W (t * ‖ringComplex h.val‖ ^ 2)‖) ∧
      t * (∑' h : {h : O // h ≠ 0},
        ‖paperAngularFourier k W (t * ‖ringComplex h.val‖ ^ 2)‖) ≤
          C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W / (1 + t) ^ A := by
  obtain ⟨S, C, hC, hdecay⟩ := paperAngularFourier_finite_seminorm_bound k (A + 2)
  let E := nonzeroLatticeEnvelopeConstant
  have hE : 0 ≤ E := nonzeroLatticeEnvelopeConstant_nonneg
  refine ⟨S, (E + 1) * C, by positivity, ?_⟩
  intro W hW t ht
  let D := C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hden : 0 < (1 + t) ^ A := by positivity
  have hpoint (h : {h : O // h ≠ 0}) :
      (1 + t * ‖ringComplex h.val‖ ^ 2) ^ 2 *
        ‖paperAngularFourier k W (t * ‖ringComplex h.val‖ ^ 2)‖ ≤ D / (1 + t) ^ A := by
    have hn : 1 ≤ ‖ringComplex h.val‖ ^ 2 := by
      rw [ringComplex_norm_sq_eq_absNorm_span]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (Ideal.absNorm_eq_zero_iff.not.mpr (Ideal.span_singleton_eq_bot.not.mpr h.property))
    have hp : (1 + t) ^ A ≤ (1 + t * ‖ringComplex h.val‖ ^ 2) ^ A := by
      apply pow_le_pow_left₀ (by positivity)
      nlinarith only [ht, hn]
    apply (le_div_iff₀ hden).mpr
    calc
      _ ≤ ((1 + t * ‖ringComplex h.val‖ ^ 2) ^ 2 *
          ‖paperAngularFourier k W (t * ‖ringComplex h.val‖ ^ 2)‖) *
            (1 + t * ‖ringComplex h.val‖ ^ 2) ^ A :=
        mul_le_mul_of_nonneg_left hp (mul_nonneg (sq_nonneg _) (norm_nonneg _))
      _ = (1 + t * ‖ringComplex h.val‖ ^ 2) ^ (A + 2) *
          ‖paperAngularFourier k W (t * ‖ringComplex h.val‖ ^ 2)‖ := by
        rw [pow_add]; ring
      _ ≤ D := hdecay W hW _ (mul_nonneg ht.le (sq_nonneg _))
  obtain ⟨hs, hb⟩ := nonzero_lattice_envelope_sum t (D / (1 + t) ^ A) ht
    (div_nonneg hD hden.le)
    (fun h => ‖paperAngularFourier k W (t * ‖ringComplex h.val‖ ^ 2)‖)
    (fun _ => norm_nonneg _) hpoint
  refine ⟨hs, hb.trans ?_⟩
  dsimp only [D]
  calc
    E * (C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W / (1 + t) ^ A) =
      (E * C) * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W / (1 + t) ^ A := by ring
    _ ≤ _ := by gcongr; linarith

private theorem periodicTrace_norm_le (c : O) (hc : c ≠ 0)
    (P : O ⧸ Ideal.span {c} → ℂ) (B : ℝ) (hB : ∀ r, ‖P r‖ ≤ B) (h : O) :
    letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
    letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
    ‖∑ r : O ⧸ Ideal.span {c}, P r *
      residueTraceQuotientChar 1 c hc (Ideal.Quotient.mk (Ideal.span {c}) h * r)‖ ≤
        ‖ringComplex c‖ ^ 2 * B := by
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  calc
    _ ≤ ∑ r : O ⧸ Ideal.span {c}, ‖P r *
        residueTraceQuotientChar 1 c hc (Ideal.Quotient.mk (Ideal.span {c}) h * r)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _r : O ⧸ Ideal.span {c}, B := by
      apply Finset.sum_le_sum
      intro r _
      rw [norm_mul, AddChar.norm_apply, mul_one]
      exact hB r
    _ = _ := by
      rw [ringComplex_norm_sq_eq_absNorm_span]
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]

/-- Long angular sums have no principal-character exception. Constants depend only on
angular weight, decay order and finitely many seminorms of the radial profile. -/
theorem angular_periodic_sum_bound (n A : ℕ) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ (W : 𝓢(ℝ, ℂ)),
      Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2 →
      ∀ (c : O) (_hc : c ≠ 0) (P : O ⧸ Ideal.span {c} → ℂ)
        (B X : ℝ), 0 ≤ B → (∀ r, ‖P r‖ ≤ B) → 0 < X →
      ‖∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) *
        angularRadial (n + 1) (fun t => W (t / X)) (ringComplex z)‖ ≤
      (C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
        (‖ringComplex c‖ ^ 2 * B) / (1 + X / ‖ringComplex c‖ ^ 2) ^ A := by
  obtain ⟨S, C, hC, hbound⟩ := paperAngularFourier_nonzero_lattice_bound (n + 1) A
  refine ⟨S, C, hC, ?_⟩
  intro W hW c hc P B X hB hP hX
  letI : Finite (O ⧸ Ideal.span {c}) := finite_quotient_span hc
  letI : Fintype (O ⧸ Ideal.span {c}) := Fintype.ofFinite _
  let q : ℝ := ‖ringComplex c‖ ^ 2
  let t : ℝ := X / q
  have hq : 0 < q := sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (ringComplex_ne_zero hc))
  have ht : 0 < t := div_pos hX hq
  let F (h : O) : ℂ :=
    (∑ r : O ⧸ Ideal.span {c}, P r *
      residueTraceQuotientChar 1 c hc (Ideal.Quotient.mk (Ideal.span {c}) h * r)) *
      ((ringComplex c / (‖ringComplex c‖ : ℂ)) ^ (n + 1) *
        (conj (ringComplex h) / (‖ringComplex h‖ : ℂ)) ^ (n + 1) *
        paperAngularFourier (n + 1) W (t * ‖ringComplex h‖ ^ 2))
  have hF0 : F 0 = 0 := by simp only [F, map_zero, norm_zero, ofReal_zero,
    zero_div, zero_pow (Nat.succ_ne_zero n), mul_zero, zero_mul]
  have heq : (∑' h : {h : O // h ≠ 0}, F h.val) = ∑' h : O, F h := by
    apply tsum_subtype_eq_of_support_subset
    intro h hh hz
    exact hh (hz ▸ hF0)
  obtain ⟨hs, hmass⟩ := hbound W hW t ht
  have hterm (h : {h : O // h ≠ 0}) :
      ‖F h.val‖ ≤ (q * B) * ‖paperAngularFourier (n + 1) W (t * ‖ringComplex h.val‖ ^ 2)‖ := by
    have hcn : ‖ringComplex c‖ ≠ 0 := norm_ne_zero_iff.mpr (ringComplex_ne_zero hc)
    have hhn : ‖ringComplex h.val‖ ≠ 0 := norm_ne_zero_iff.mpr (ringComplex_ne_zero h.property)
    simp only [F, norm_mul, norm_pow, norm_div, norm_conj, norm_real, norm_norm,
      div_self hcn, div_self hhn, one_pow, one_mul]
    exact mul_le_mul_of_nonneg_right (periodicTrace_norm_le c hc P B hP h.val) (norm_nonneg _)
  have hsF : Summable (fun h : {h : O // h ≠ 0} => ‖F h.val‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hterm (hs.mul_left (q * B))
  have hsum : ‖∑' h : O, F h‖ ≤ (q * B) *
      ∑' h : {h : O // h ≠ 0}, ‖paperAngularFourier (n + 1) W (t * ‖ringComplex h.val‖ ^ 2)‖ := by
    rw [← heq]
    exact (norm_tsum_le_tsum_norm hsF).trans
      (by simpa only [tsum_mul_left] using hsF.tsum_le_tsum hterm (hs.mul_left (q * B)))
  have hpoisson := actual_angular_poisson_trace (n + 1) W hW X hX c hc P
  have harg (h : O) : X * ‖ringComplex h‖ ^ 2 / ‖ringComplex c‖ ^ 2 =
      t * ‖ringComplex h‖ ^ 2 := by dsimp [t, q]; ring
  simp_rw [harg] at hpoisson
  change _ = t • ∑' h : O, F h at hpoisson
  rw [hpoisson, norm_smul, Real.norm_of_nonneg ht.le]
  calc
    _ ≤ t * ((q * B) * ∑' h : {h : O // h ≠ 0},
        ‖paperAngularFourier (n + 1) W (t * ‖ringComplex h.val‖ ^ 2)‖) :=
      mul_le_mul_of_nonneg_left hsum ht.le
    _ = (q * B) * (t * ∑' h : {h : O // h ≠ 0},
        ‖paperAngularFourier (n + 1) W (t * ‖ringComplex h.val‖ ^ 2)‖) := by ring
    _ ≤ (q * B) * (C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W / (1 + t) ^ A) :=
      mul_le_mul_of_nonneg_left hmass (mul_nonneg hq.le hB)
    _ = _ := by ring

/-- Conjugate angular weights satisfy the same rapid-decay estimate. -/
theorem conjugate_angular_periodic_sum_bound (n A : ℕ) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧ ∀ (W : 𝓢(ℝ, ℂ)),
      Function.support W ⊆ Set.Icc (1 / 2 : ℝ) 2 →
      ∀ (c : O) (_hc : c ≠ 0) (P : O ⧸ Ideal.span {c} → ℂ)
        (B X : ℝ), 0 ≤ B → (∀ r, ‖P r‖ ≤ B) → 0 < X →
      ‖∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) *
        ((conj (ringComplex z) / (‖ringComplex z‖ : ℂ)) ^ (n + 1) *
          W (‖ringComplex z‖ ^ 2 / X))‖ ≤
      (C * S.sup (schwartzSeminormFamily ℝ ℝ ℂ) W) *
        (‖ringComplex c‖ ^ 2 * B) / (1 + X / ‖ringComplex c‖ ^ 2) ^ A := by
  obtain ⟨S, C, hC, hb⟩ := angular_periodic_sum_bound n A
  let T : 𝓢(ℝ, ℂ) →L[ℝ] 𝓢(ℝ, ℂ) :=
    SchwartzMap.postcompCLM Complex.conjCLE.toContinuousLinearMap
  obtain ⟨S', D, hD, hcontrol⟩ := schwartzCLM_finite_seminorm_control T S
  refine ⟨S', C * D, mul_pos hC hD, ?_⟩
  intro W hW c hc P B X hB hP hX
  have hTW : Function.support (T W) ⊆ Set.Icc (1 / 2 : ℝ) 2 := by
    intro x hx
    apply hW
    intro he
    exact hx (by change conj (W x) = 0; rw [he, map_zero])
  have h := hb (T W) hTW c hc (fun r => conj (P r)) B X hB
    (fun r => by simpa only [norm_conj] using hP r) hX
  have heq : (∑' z : O, conj (P (Ideal.Quotient.mk (Ideal.span {c}) z)) *
      angularRadial (n + 1) (fun t => T W (t / X)) (ringComplex z)) =
      conj (∑' z : O, P (Ideal.Quotient.mk (Ideal.span {c}) z) *
        ((conj (ringComplex z) / (‖ringComplex z‖ : ℂ)) ^ (n + 1) *
          W (‖ringComplex z‖ ^ 2 / X))) := by
    rw [Complex.conj_tsum]
    apply tsum_congr
    intro z
    change conj (P _) * ((ringComplex z / (‖ringComplex z‖ : ℂ)) ^ (n + 1) *
      conj (W (‖ringComplex z‖ ^ 2 / X))) = _
    simp only [map_mul, map_pow, map_div₀, conj_conj, conj_ofReal]
  rw [heq, norm_conj] at h
  refine h.trans ?_
  calc
    _ ≤ (C * (D * S'.sup (schwartzSeminormFamily ℝ ℝ ℂ) W)) *
        (‖ringComplex c‖ ^ 2 * B) / (1 + X / ‖ringComplex c‖ ^ 2) ^ A := by
      gcongr
      exact hcontrol W
    _ = _ := by ring

end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.SchwartzPlanePoisson
