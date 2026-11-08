import GaloisForLFunctions.BlackHoleRingdown.TheRankinSelbergEulerProductOfTheCuspModes
import GaloisForLFunctions.BlackHoleRingdown.TheRankinSelbergIntegralOfTheCuspModes
import GaloisForLFunctions.BlackHoleRingdown.TheRankinSelbergContinuation
import GaloisForLFunctions.RHTower.XiCosineShiftNonrealZeroCount

/-!
# The Rankin–Selberg series of a Hecke eigenform

Let `g ∈ S(λ)` be a Hecke eigenform, `T_p g = c_p g`, with Whittaker coefficients `ρ(n)` and
normalized eigenvalues `λ_p = c_p/√p`.

**Theorem** (`cusp_rankinSelberg_euler`). For `Re s > 2`,

  `Σ_{n ≠ 0} |ρ(n)|² |n|^{−s} = (|ρ(1)|² + |ρ(−1)|²) Π_p (1 − p^{−2s}) / Q_p(λ_p, λ̄_p; p^{−s})`

with the Rankin–Selberg local polynomial `Q_p` (`rsLocal`). The coefficients of both signs are
multiples of one normalized Hecke sequence `τ`, `|ρ(±n)|² = |ρ(±1)|² τ(n) τ̄(n)`, and `τ̄` is a Hecke
sequence with eigenvalues `λ̄_p` (`HeckeRec.conj`). For real eigenvalues `Q_p` factors as
`(1 − x)²(1 − (λ_p² − 2)x + x²)` (`rsLocal_self`): the series is `ζ(s) L(Sym² g, s)/ζ(2s)`.

**The Rankin–Selberg integral** (`rankinSelberg_eisenstein_euler`). For `Re s > 2`, `Im s ≠ 0`,

  `∫_𝒟 |g|² E(s − ½) = (2π)^{−s} γ_ν(s) (|ρ(1)|² + |ρ(−1)|²) Π_p (1 − p^{−2s}) / Q_p(λ_p, λ̄_p; p^{−s})`.

**The completed Rankin–Selberg function** (`completedRS_eq_rankinSelberg_euler`). For `Re s > 2`,
`Im s ≠ 0`, the factor `ξ(2s)/(2s(2s−1)) = ½ Γ_ℝ(2s) ζ(2s)` cancels the `ζ(2s)⁻¹` of the series:

  `Λ_g(s) = ½ Γ_ℝ(2s) (2π)^{−s} γ_ν(s) (|ρ(1)|² + |ρ(−1)|²) Π_p Q_p(λ_p, λ̄_p; p^{−s})⁻¹`,

so `Λ_g` is a Gamma factor times `L(g × ḡ, s)`, and for real eigenvalues times `ζ(s) L(Sym² g, s)`.
-/

open Complex MeasureTheory Set Filter Topology
open scoped ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.RHTower GaloisForLFunctions.RHTower.Gamma0MaassHecke
open GaloisForLFunctions.HTGeometry (modifiedBesselKOrder)
open CuspEuler HeckeCusp CuspL CuspRSI CuspRSC

variable {lamE : ℝ} {g : UpperHalfPlane → ℂ} {ρ : ℤ → ℂ}

namespace CuspEuler

/-- The conjugate of a Hecke sequence is a Hecke sequence for the conjugate eigenvalues. -/
theorem HeckeRec.conj {lam σ : ℕ → ℂ} (hσ : HeckeRec lam σ) :
    HeckeRec (fun p => (starRingEnd ℂ) (lam p)) (fun n => (starRingEnd ℂ) (σ n)) := by
  intro p hp n hn
  simp only
  rw [hσ p hp n hn]
  split_ifs <;> simp [map_sub, map_mul]

end CuspEuler

/-- `‖z‖²` as `z z̄`. -/
private theorem ofReal_norm_sq_eq (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]

/-- **The Rankin–Selberg Euler product of a Hecke eigenform** for `Re s > 2`. -/
theorem cusp_rankinSelberg_euler (hg : g ∈ cuspSpace lamE) (c : ℕ → ℂ)
    (hc : ∀ (p : ℕ) [Fact p.Prime], heckeH p g = c p • g) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {s : ℂ} (hs : 2 < s.re) :
    HasSum (fun n : ℤ => ((‖ρ n‖ ^ 2 : ℝ) : ℂ) * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s))
      (((‖ρ 1‖ ^ 2 + ‖ρ (-1)‖ ^ 2 : ℝ) : ℂ) *
        ∏' p : Nat.Primes, (1 - ((p : ℂ) ^ (-s)) ^ 2) /
          rsLocal (heckeLam c p) ((starRingEnd ℂ) (heckeLam c p)) ((p : ℂ) ^ (-s))) := by
  have hP := heckeRec_rho hg hρ c hc 1 (Or.inl rfl)
  have hM := heckeRec_rho hg hρ c hc (-1) (Or.inr rfl)
  simp only [one_mul, neg_one_mul] at hP hM
  obtain ⟨C, hC0, hC⟩ := exists_coeff_bound hg hρ0 hρ
  -- absolute convergence over `ℤ`: `|ρ(n)|²|n|^{−σ} ≤ C²|n|^{−(σ−1)}`
  have hσ1 : 1 < s.re - 1 := by linarith
  have hbound : ∀ n : ℤ, ‖((‖ρ n‖ ^ 2 : ℝ) : ℂ) * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s)‖ ≤
      C ^ 2 * |(n : ℝ)| ^ (-(s.re - 1)) := by
    intro n
    by_cases hn : n = 0
    · rw [hn, hρ0, norm_zero]; simp; positivity
    have hn0 : 0 < |(n : ℝ)| := abs_pos.2 (Int.cast_ne_zero.2 hn)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity),
      norm_cpow_eq_rpow_re_of_pos hn0, neg_re]
    have hsq : ‖ρ n‖ ^ 2 ≤ C ^ 2 * |(n : ℝ)| := by
      have h := pow_le_pow_left₀ (norm_nonneg _) (hC n) 2
      rwa [mul_pow, Real.sq_sqrt hn0.le] at h
    calc ‖ρ n‖ ^ 2 * |(n : ℝ)| ^ (-s.re) ≤ (C ^ 2 * |(n : ℝ)|) * |(n : ℝ)| ^ (-s.re) :=
          mul_le_mul_of_nonneg_right hsq (by positivity)
      _ = C ^ 2 * |(n : ℝ)| ^ (-(s.re - 1)) := by
          rw [mul_assoc, show -(s.re - 1) = 1 + -s.re by ring, Real.rpow_add hn0, Real.rpow_one]
  have hsumZ : Summable fun n : ℤ => ((‖ρ n‖ ^ 2 : ℝ) : ℂ) * ((|(n : ℝ)| : ℝ) : ℂ) ^ (-s) :=
    Summable.of_norm_bounded ((Real.summable_abs_int_rpow hσ1).mul_left (C ^ 2)) hbound
  -- fold the two signs
  have hNat := hsumZ.hasSum.nat_add_neg
  have hf0 : ((‖ρ 0‖ ^ 2 : ℝ) : ℂ) * ((|((0 : ℤ) : ℝ)| : ℝ) : ℂ) ^ (-s) = 0 := by
    rw [hρ0]; simp
  rw [hf0, add_zero] at hNat
  have hfold : ∀ n : ℕ,
      ((‖ρ n‖ ^ 2 : ℝ) : ℂ) * ((|((n : ℤ) : ℝ)| : ℝ) : ℂ) ^ (-s) +
        ((‖ρ (-(n : ℤ))‖ ^ 2 : ℝ) : ℂ) * ((|((-(n : ℤ) : ℤ) : ℝ)| : ℝ) : ℂ) ^ (-s) =
      ((‖ρ n‖ ^ 2 + ‖ρ (-(n : ℤ))‖ ^ 2 : ℝ) : ℂ) * (n : ℂ) ^ (-s) := by
    intro n
    have h1 : ((|((n : ℤ) : ℝ)| : ℝ) : ℂ) = (n : ℂ) := by simp
    have h2 : ((|((-(n : ℤ) : ℤ) : ℝ)| : ℝ) : ℂ) = (n : ℂ) := by simp
    rw [h1, h2]; push_cast; ring
  simp_rw [hfold] at hNat
  by_cases h01 : ρ 1 = 0 ∧ ρ (-1) = 0
  · have hz : ∀ n : ℕ, ‖ρ n‖ ^ 2 + ‖ρ (-(n : ℤ))‖ ^ 2 = 0 := by
      intro n
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; simp [hρ0]
      have e1 := hP.eq_zero (by simpa using h01.1) n hn
      have e2 := hM.eq_zero (by simpa using h01.2) n hn
      rw [e1, e2]; simp
    simp_rw [hz, Complex.ofReal_zero, zero_mul] at hNat
    have htsum := hNat.unique hasSum_zero
    have hval : ((‖ρ 1‖ ^ 2 + ‖ρ (-1)‖ ^ 2 : ℝ) : ℂ) = 0 := by rw [h01.1, h01.2]; simp
    rw [hval, zero_mul, ← htsum]
    exact hsumZ.hasSum
  -- the normalized Hecke sequence
  push Not at h01
  set σ₀ : ℕ → ℂ := if ρ 1 ≠ 0 then (fun n => ρ n) else (fun n => ρ (-(n : ℤ))) with hσ₀def
  have hσ₀ : HeckeRec (heckeLam c) σ₀ := by
    by_cases h : ρ 1 ≠ 0
    · simp only [σ₀, if_pos h]; exact hP
    · simp only [σ₀, if_neg h]; exact hM
  have ha : σ₀ 1 ≠ 0 := by
    by_cases h : ρ 1 ≠ 0
    · simp only [σ₀, if_pos h]; simpa using h
    · simp only [σ₀, if_neg h]; push Not at h; simpa using h01 h
  set τ : ℕ → ℂ := fun n => (σ₀ 1)⁻¹ * σ₀ n + 0 * σ₀ n with hτdef
  have hτ : HeckeRec (heckeLam c) τ := hσ₀.lin hσ₀ _ _
  have hτ1 : τ 1 = 1 := by simp only [τ]; field_simp; ring
  have hσ0 : σ₀ 0 = 0 := by
    by_cases h : ρ 1 ≠ 0
    · simp only [σ₀, if_pos h]; simpa using hρ0
    · simp only [σ₀, if_neg h]; simpa using hρ0
  have hτ0 : τ 0 = 0 := by simp [τ, hσ0]
  have hτc := hτ.conj
  have hτc1 : (fun n => (starRingEnd ℂ) (τ n)) 1 = 1 := by simp [hτ1]
  -- both signs are multiples of `τ`
  have hsplit : ∀ n : ℕ, ((‖ρ n‖ ^ 2 + ‖ρ (-(n : ℤ))‖ ^ 2 : ℝ) : ℂ) =
      ((‖ρ 1‖ ^ 2 + ‖ρ (-1)‖ ^ 2 : ℝ) : ℂ) * (τ n * (starRingEnd ℂ) (τ n)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp [hρ0, hτ0]
    have e1 := hP.proportional hτ n hn
    have e2 := hM.proportional hτ n hn
    rw [hτ1] at e1 e2
    simp only [Nat.cast_one, mul_one] at e1 e2
    have hr1 : ρ (n : ℤ) = τ n * ρ 1 := e1
    have hr2 : ρ (-(n : ℤ)) = τ n * ρ (-1) := by simpa using e2
    rw [Complex.ofReal_add, Complex.ofReal_add, ofReal_norm_sq_eq, ofReal_norm_sq_eq,
      ofReal_norm_sq_eq, ofReal_norm_sq_eq, hr1, hr2]
    simp only [map_mul]
    ring
  simp_rw [hsplit] at hNat
  -- absolute convergence of the normalized product series
  have hsumN : Summable fun n : ℕ => ‖τ n * (starRingEnd ℂ) (τ n) * (n : ℂ) ^ (-s)‖ := by
    have hsq : ∀ n : ℕ, ‖τ n * (starRingEnd ℂ) (τ n) * (n : ℂ) ^ (-s)‖ ≤
        ‖σ₀ 1‖⁻¹ ^ 2 * (C ^ 2 * |((n : ℤ) : ℝ)| ^ (-(s.re - 1))) := by
      intro n
      rcases Nat.eq_zero_or_pos n with hn | hn
      · subst hn; rw [hτ0]; simp; positivity
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      have hσn : ‖σ₀ n‖ ≤ C * Real.sqrt n := by
        by_cases h : ρ 1 ≠ 0
        · simp only [σ₀, if_pos h]; simpa using hC n
        · simp only [σ₀, if_neg h]; simpa using hC (-(n : ℤ))
      have hτn : ‖τ n‖ ≤ ‖σ₀ 1‖⁻¹ * (C * Real.sqrt n) := by
        simp only [τ, zero_mul, add_zero, norm_mul, norm_inv]
        exact mul_le_mul_of_nonneg_left hσn (inv_nonneg.2 (norm_nonneg _))
      rw [norm_mul, norm_mul, Complex.norm_conj,
        show (n : ℂ) = ((n : ℝ) : ℂ) by norm_cast, norm_cpow_eq_rpow_re_of_pos hn0, neg_re]
      have habs : |((n : ℤ) : ℝ)| = n := by simp
      rw [habs, show -(s.re - 1) = 1 + -s.re by ring, Real.rpow_add hn0, Real.rpow_one]
      have hτsq : ‖τ n‖ * ‖τ n‖ ≤ ‖σ₀ 1‖⁻¹ ^ 2 * (C ^ 2 * n) := by
        have h0 := norm_nonneg (τ n)
        have hs2 := Real.mul_self_sqrt hn0.le
        calc ‖τ n‖ * ‖τ n‖ ≤ (‖σ₀ 1‖⁻¹ * (C * Real.sqrt n)) * (‖σ₀ 1‖⁻¹ * (C * Real.sqrt n)) :=
              mul_le_mul hτn hτn h0 (h0.trans hτn)
          _ = ‖σ₀ 1‖⁻¹ ^ 2 * (C ^ 2 * n) := by
              linear_combination (‖σ₀ 1‖⁻¹ ^ 2 * C ^ 2) * hs2
      calc ‖τ n‖ * ‖τ n‖ * (n : ℝ) ^ (-s.re)
          ≤ ‖σ₀ 1‖⁻¹ ^ 2 * (C ^ 2 * n) * (n : ℝ) ^ (-s.re) :=
            mul_le_mul_of_nonneg_right hτsq (by positivity)
        _ = ‖σ₀ 1‖⁻¹ ^ 2 * (C ^ 2 * (n * (n : ℝ) ^ (-s.re))) := by ring
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) hsq ?_
    exact (((Real.summable_abs_int_rpow hσ1).mul_left (C ^ 2)).comp_injective
      Nat.cast_injective).mul_left _
  have hE := hτ.rankinSelberg_euler hτc hτ1 hτc1 hτ0 (by linarith) hsumN
  have hrhs : (((‖ρ 1‖ ^ 2 + ‖ρ (-1)‖ ^ 2 : ℝ) : ℂ) *
      ∏' p : Nat.Primes, (1 - ((p : ℂ) ^ (-s)) ^ 2) /
        rsLocal (heckeLam c p) ((starRingEnd ℂ) (heckeLam c p)) ((p : ℂ) ^ (-s))) =
      ∑' n : ℕ, ((‖ρ 1‖ ^ 2 + ‖ρ (-1)‖ ^ 2 : ℝ) : ℂ) * (τ n * (starRingEnd ℂ) (τ n)) *
        (n : ℂ) ^ (-s) := by
    rw [hE, ← tsum_mul_left]
    exact tsum_congr fun n => by ring
  rw [hrhs, hNat.tsum_eq]
  exact hsumZ.hasSum

/-- **The Rankin–Selberg integral of a Hecke eigenform as an Euler product**, `Re s > 2`,
`Im s ≠ 0`. -/
theorem rankinSelberg_eisenstein_euler (hg : g ∈ cuspSpace lamE) (c : ℕ → ℂ)
    (hc : ∀ (p : ℕ) [Fact p.Prime], heckeH p g = c p • g) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {s : ℂ} (hs : 2 < s.re)
    (him : s.im ≠ 0) :
    (∫ z in ModularGroup.fd, ((‖g z‖ ^ 2 : ℝ) : ℂ) * normalizedEisenstein (s - 1 / 2) z.re z.im) =
      (2 * Real.pi : ℂ) ^ (-s) * gammaFactor (nu lamE) s *
        (((‖ρ 1‖ ^ 2 + ‖ρ (-1)‖ ^ 2 : ℝ) : ℂ) *
          ∏' p : Nat.Primes, (1 - ((p : ℂ) ^ (-s)) ^ 2) /
            rsLocal (heckeLam c p) ((starRingEnd ℂ) (heckeLam c p)) ((p : ℂ) ^ (-s))) := by
  have hI := rankinSelberg_eisenstein hg hρ0 hρ (s := s) (by linarith) him
  have hD := cusp_rankinSelberg_euler hg c hc hρ0 hρ hs
  rw [← hI.tsum_eq, ← hD.tsum_eq, ← tsum_mul_left]

/-- **The normalized Hecke sequence of an eigenform.** If `ρ(1)` or `ρ(−1)` is nonzero, both
`n ↦ ρ(n)` and `n ↦ ρ(−n)` are multiples of one normalized Hecke sequence `τ` with `|τ(n)| ≤ K√n`. -/
theorem exists_normalized_heckeSequence (hg : g ∈ cuspSpace lamE) (c : ℕ → ℂ)
    (hc : ∀ (p : ℕ) [Fact p.Prime], heckeH p g = c p • g) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE))
    (h01 : ¬ (ρ 1 = 0 ∧ ρ (-1) = 0)) :
    ∃ τ : ℕ → ℂ, HeckeRec (heckeLam c) τ ∧ τ 1 = 1 ∧ τ 0 = 0 ∧
      ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, ‖τ n‖ ≤ K * Real.sqrt n := by
  have hP := heckeRec_rho hg hρ c hc 1 (Or.inl rfl)
  have hM := heckeRec_rho hg hρ c hc (-1) (Or.inr rfl)
  simp only [one_mul, neg_one_mul] at hP hM
  obtain ⟨C, hC0, hC⟩ := exists_coeff_bound hg hρ0 hρ
  push Not at h01
  set σ₀ : ℕ → ℂ := if ρ 1 ≠ 0 then (fun n => ρ n) else (fun n => ρ (-(n : ℤ)))
  have hσ₀ : HeckeRec (heckeLam c) σ₀ := by
    by_cases h : ρ 1 ≠ 0
    · simp only [σ₀, if_pos h]; exact hP
    · simp only [σ₀, if_neg h]; exact hM
  have ha : σ₀ 1 ≠ 0 := by
    by_cases h : ρ 1 ≠ 0
    · simp only [σ₀, if_pos h]; simpa using h
    · simp only [σ₀, if_neg h]; push Not at h; simpa using h01 h
  have hσ0 : σ₀ 0 = 0 := by
    by_cases h : ρ 1 ≠ 0
    · simp only [σ₀, if_pos h]; simpa using hρ0
    · simp only [σ₀, if_neg h]; simpa using hρ0
  have hσn : ∀ n : ℕ, ‖σ₀ n‖ ≤ C * Real.sqrt n := fun n => by
    by_cases h : ρ 1 ≠ 0
    · simp only [σ₀, if_pos h]; simpa using hC n
    · simp only [σ₀, if_neg h]; simpa using hC (-(n : ℤ))
  refine ⟨fun n => (σ₀ 1)⁻¹ * σ₀ n + 0 * σ₀ n, hσ₀.lin hσ₀ _ _, by field_simp; ring,
    by simp [hσ0], ‖σ₀ 1‖⁻¹ * C, by positivity, fun n => ?_⟩
  simp only [zero_mul, add_zero, norm_mul, norm_inv, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hσn n) (inv_nonneg.2 (norm_nonneg _))

/-- **The completed Rankin–Selberg function is a Gamma factor times `L(g × ḡ, s)`.** -/
theorem completedRS_eq_rankinSelberg_euler (hg : g ∈ cuspSpace lamE) (c : ℕ → ℂ)
    (hc : ∀ (p : ℕ) [Fact p.Prime], heckeH p g = c p • g) (hρ0 : ρ 0 = 0)
    (hρ : ∀ n : ℤ, ∀ y, 0 < y → fourierCoeff g n y = ρ n * (Real.sqrt y : ℂ) *
      modifiedBesselKOrder (2 * Real.pi * |(n : ℝ)| * y) (nu lamE)) {s : ℂ} (hs : 2 < s.re)
    (him : s.im ≠ 0) :
    completedRS g s = Complex.Gammaℝ (2 * s) / 2 *
      ((2 * Real.pi : ℂ) ^ (-s) * gammaFactor (nu lamE) s) *
        (((‖ρ 1‖ ^ 2 + ‖ρ (-1)‖ ^ 2 : ℝ) : ℂ) *
          ∏' p : Nat.Primes,
            (rsLocal (heckeLam c p) ((starRingEnd ℂ) (heckeLam c p)) ((p : ℂ) ^ (-s)))⁻¹) := by
  have hs1 : 1 < s.re := by linarith
  rw [completedRS_eq hg hρ0 hρ hs1 him, (cusp_rankinSelberg_euler hg c hc hρ0 hρ hs).tsum_eq]
  -- `ξ(2s)/(2s(2s−1)) = ½ Γ_ℝ(2s) ζ(2s)`
  have h2s : 1 < (2 * s).re := by simp; linarith
  have hs0 : (2 * s) * (2 * s - 1) ≠ 0 := by
    refine mul_ne_zero (fun h => ?_) (fun h => ?_)
    · have := congrArg Complex.re h; simp at this; linarith
    · have := congrArg Complex.re h; simp at this; linarith
  have hxi : _root_.RHTower.xi (2 * s) / (2 * s * (2 * s - 1)) =
      Complex.Gammaℝ (2 * s) * riemannZeta (2 * s) / 2 := by
    rw [_root_.RHTower.xi_eq_mul_Gammaℝ_zeta h2s]
    have hs0' : s * (2 * s - 1) ≠ 0 := by
      refine mul_ne_zero (fun h => ?_) (fun h => ?_)
      · have := congrArg Complex.re h; simp at this; linarith
      · have := congrArg Complex.re h; simp at this; linarith
    field_simp
    rw [mul_assoc, mul_div_cancel_left₀ _ hs0']
  rw [hxi]
  by_cases h01 : ρ 1 = 0 ∧ ρ (-1) = 0
  · rw [h01.1, h01.2]; simp
  obtain ⟨τ, hτ, hτ1, hτ0, K, hK0, hK⟩ :=
    exists_normalized_heckeSequence hg c hc hρ0 hρ h01
  -- summability of `τ τ̄ n^{−s}` for `Re s > 2`
  have hsumN : Summable fun n : ℕ => ‖τ n * (starRingEnd ℂ) (τ n) * (n : ℂ) ^ (-s)‖ := by
    have hσ1 : 1 < s.re - 1 := by linarith
    refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
      ((((Real.summable_abs_int_rpow hσ1).comp_injective Nat.cast_injective).mul_left (K ^ 2)))
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; rw [hτ0]; simp; positivity
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [norm_mul, norm_mul, Complex.norm_conj,
      show (n : ℂ) = ((n : ℝ) : ℂ) by norm_cast, norm_cpow_eq_rpow_re_of_pos hn0, neg_re]
    have habs : |((n : ℤ) : ℝ)| = n := by simp
    simp only [Function.comp_apply]
    rw [habs, show -(s.re - 1) = 1 + -s.re by ring, Real.rpow_add hn0, Real.rpow_one]
    have hτsq : ‖τ n‖ * ‖τ n‖ ≤ K ^ 2 * n := by
      have h0 := norm_nonneg (τ n)
      have hs2 := Real.mul_self_sqrt hn0.le
      calc ‖τ n‖ * ‖τ n‖ ≤ (K * Real.sqrt n) * (K * Real.sqrt n) :=
            mul_le_mul (hK n) (hK n) h0 (h0.trans (hK n))
        _ = K ^ 2 * n := by linear_combination K ^ 2 * hs2
    calc ‖τ n‖ * ‖τ n‖ * (n : ℝ) ^ (-s.re) ≤ K ^ 2 * n * (n : ℝ) ^ (-s.re) :=
          mul_le_mul_of_nonneg_right hτsq (by positivity)
      _ = K ^ 2 * (n * (n : ℝ) ^ (-s.re)) := by ring
  have hRS := hτ.rankinSelberg_hasProd hτ.conj hτ1 (by simp [hτ1]) hτ0 (by linarith) hsumN
  have hZ := riemannZeta_eulerProduct_hasProd h2s
  have hprod := hZ.mul hRS
  -- the factor at `p` is `Q_p⁻¹`
  have hfac : ∀ p : Nat.Primes, (1 - (p : ℂ) ^ (-(2 * s)))⁻¹ *
      ((1 - ((p : ℂ) ^ (-s)) ^ 2) /
        rsLocal (heckeLam c p) ((starRingEnd ℂ) (heckeLam c p)) ((p : ℂ) ^ (-s))) =
      (rsLocal (heckeLam c p) ((starRingEnd ℂ) (heckeLam c p)) ((p : ℂ) ^ (-s)))⁻¹ := by
    intro p
    have hsq : ((p : ℂ) ^ (-s)) ^ 2 = (p : ℂ) ^ (-(2 * s)) := by
      rw [← cpow_nat_mul]; congr 1; push_cast; ring
    have hne : 1 - (p : ℂ) ^ (-(2 * s)) ≠ 0 := by
      intro h
      have hn := congrArg norm (sub_eq_zero.mp h).symm
      rw [norm_one, Complex.norm_natCast_cpow_of_pos p.prop.pos, neg_re] at hn
      have hlt : (p : ℝ) ^ (-(2 * s).re) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg (by exact_mod_cast p.prop.one_lt) (by linarith)
      linarith
    rw [hsq, ← mul_div_assoc, inv_mul_cancel₀ hne, one_div]
  simp_rw [hfac] at hprod
  rw [hprod.tprod_eq, ← hRS.tprod_eq]
  ring

end GaloisForLFunctions.BlackHoleRingdown
