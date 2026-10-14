import GaloisForLFunctions.RHTower.WeilPoleShiftHerglotzBridge
import GaloisForLFunctions.RHTower.WeilPoleWeightAtMostOne
import GaloisForLFunctions.RHTower.WeilPoleWeightWindow

/-!
# Weil positivity counts the pole of `ζ` exactly once

For a pole weight `β` let `W_β(lam)` be the Weil functional with `ζ`'s archimedean datum in which
the pole term `k̂(i/2) + k̂(−i/2)` is counted `β` times (`WeilPositiveAt β lam`: nonnegative real
part on every autocorrelation of a `C²` compactly supported test).

**Theorem** (`eq_one_of_weilPositiveAt`).  If some real weight sequence `lam` makes `W_β`
nonnegative on every autocorrelation, then `β = 1`.  There is no hypothesis on `lam`.

Proof.  Weil positivity at pole weight `β` is Herglotz positivity of the Weil function with pole
weight `β` (`exists_herglotz_of_weilPositiveShift`, with `κ = β − 1`), and every Herglotz datum
has pole weight `1` (`eq_one_of_herglotz_poleWeightFunction`).

**Consequences.**
* Prime-blind positivity holds at no pole weight other than `1`
  (`eq_one_of_primeBlindPositiveAt`), so the pole-weight window is empty or `{1}`, and
  `RH ⟺ ∃ β, PrimeBlindPositiveAt β` (`riemannHypothesis_iff_exists_primeBlindPositiveAt`).
* For every `ε ≠ 0` some nonnegative combination of autocorrelations vanishing at every `±log n`
  has `S_A + ε S_P < 0`, where `S_A` is its pole-plus-archimedean part and `S_P` its pole term
  (`exists_blind_arch_add_mul_pole_neg`).  Under RH (`S_A ≥ 0` on such combinations) the blind
  combinations therefore reach pole terms of both signs with `S_A / |S_P|` arbitrarily small
  (`exists_blind_pole_neg_of_riemannHypothesis`, `exists_blind_pole_pos_of_riemannHypothesis`).
-/

open Complex Zeta23 Finsupp

noncomputable section

namespace RHTower

open WeilOneSided

theorem weilPositiveShift_of_weilPositiveAt {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveAt β lam) :
    WeilSpectral.WeilPositiveShift (β - 1) lam := by
  intro f hf hfc
  have hpos := h f hf hfc
  have e : WeilPoleWeight.weilPoleWeightFunctional β lam (EF.weilTest f f) =
      WeilSpectral.shiftFunctional (β - 1) lam (EF.weilTest f f) := by
    unfold WeilPoleWeight.weilPoleWeightFunctional WeilSpectral.shiftFunctional
      WeilSpectral.polePart
    push_cast
    ring
  rwa [e] at hpos

theorem shiftWeilFunction_eq_poleWeightFunction (β : ℝ) (lam : ℕ → ℝ) (s : ℂ) :
    WeilSpectral.shiftWeilFunction (β - 1) lam s = WeilPoleWeight.poleWeightFunction β lam s := by
  unfold WeilSpectral.shiftWeilFunction WeilPoleWeight.poleWeightFunction WeilLineIntegral.gPair
  push_cast
  simp only [sub_zero]

/-- **The pole is counted exactly once.**  Weil positivity with `ζ`'s archimedean datum and the
pole term counted `β` times, for any real weights, forces `β = 1`. -/
theorem eq_one_of_weilPositiveAt {β : ℝ} {lam : ℕ → ℝ} (h : WeilPositiveAt β lam) : β = 1 := by
  obtain ⟨hsl, Φ, hΦd, hΦre, hΦ⟩ :=
    WeilSpectral.exists_herglotz_of_weilPositiveShift (weilPositiveShift_of_weilPositiveAt h)
  exact WeilPoleWeight.eq_one_of_herglotz_poleWeightFunction hsl hΦd hΦre fun s hs => by
    rw [hΦ s hs, shiftWeilFunction_eq_poleWeightFunction]

/-- **The pole-weight window is at most `{1}`.** -/
theorem eq_one_of_primeBlindPositiveAt {β : ℝ} (h : PrimeBlindPositiveAt β) : β = 1 := by
  obtain ⟨lam, hlam⟩ := (exists_weilPositiveAt_iff β).mpr h
  exact eq_one_of_weilPositiveAt hlam

/-- **RH is prime-blind positivity at some pole weight.** -/
theorem riemannHypothesis_iff_exists_primeBlindPositiveAt :
    RiemannHypothesis ↔ ∃ β : ℝ, PrimeBlindPositiveAt β := by
  constructor
  · exact fun h => ⟨1, riemannHypothesis_iff_primeBlindPositiveAt_one.mp h⟩
  · rintro ⟨β, hβ⟩
    obtain rfl := eq_one_of_primeBlindPositiveAt hβ
    exact riemannHypothesis_iff_primeBlindPositiveAt_one.mpr hβ

/-- **No linear slack between energy and pole on the blind cone.**  For every `ε ≠ 0` some
nonnegative blind combination has `S_A + ε S_P < 0`. -/
theorem exists_blind_arch_add_mul_pole_neg {ε : ℝ} (hε : ε ≠ 0) :
    ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧
      (∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1 n) = 0) ∧
        (c.sum fun f t => t * weilArchRe (EF.weilTest f.1 f.1)) +
          ε * (c.sum fun f t => t * (weilPoleTerm (EF.weilTest f.1 f.1)).re) < 0 := by
  have h : ¬ PrimeBlindPositiveAt (1 + ε) := fun h =>
    hε (by linarith [eq_one_of_primeBlindPositiveAt h])
  unfold PrimeBlindPositiveAt at h
  push Not at h
  obtain ⟨c, hc, hnull, hneg⟩ := h
  refine ⟨c, hc, hnull, ?_⟩
  rw [sum_poleWeightArchRe] at hneg
  simpa using hneg

/-- **Pole-negative near-null blind combinations under RH.**  If RH holds, then for every `ε > 0`
some nonnegative blind combination has `S_P < 0` and `0 ≤ S_A < ε |S_P|`. -/
theorem exists_blind_pole_neg_of_riemannHypothesis (hRH : RiemannHypothesis) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧
      (∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1 n) = 0) ∧
        (c.sum fun f t => t * (weilPoleTerm (EF.weilTest f.1 f.1)).re) < 0 ∧
          0 ≤ (c.sum fun f t => t * weilArchRe (EF.weilTest f.1 f.1)) ∧
            (c.sum fun f t => t * weilArchRe (EF.weilTest f.1 f.1)) <
              ε * |c.sum fun f t => t * (weilPoleTerm (EF.weilTest f.1 f.1)).re| := by
  obtain ⟨c, hc, hnull, hneg⟩ := exists_blind_arch_add_mul_pole_neg hε.ne'
  have hA := riemannHypothesis_iff_primeBlindPositiveAt_one.mp hRH c hc hnull
  rw [sum_poleWeightArchRe, sub_self, zero_mul, add_zero] at hA
  set A := c.sum fun f t => t * weilArchRe (EF.weilTest f.1 f.1)
  set P := c.sum fun f t => t * (weilPoleTerm (EF.weilTest f.1 f.1)).re
  have hP : P < 0 := by nlinarith
  refine ⟨c, hc, hnull, hP, hA, ?_⟩
  rw [abs_of_neg hP]
  linarith

/-- **Pole-positive near-null blind combinations under RH.**  If RH holds, then for every `ε > 0`
some nonnegative blind combination has `S_P > 0` and `0 ≤ S_A < ε S_P`. -/
theorem exists_blind_pole_pos_of_riemannHypothesis (hRH : RiemannHypothesis) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ c : WeilTestFn →₀ ℝ, (∀ f, 0 ≤ c f) ∧
      (∀ n : ℕ, 2 ≤ n → (c.sum fun f t => t * logValue f.1 n) = 0) ∧
        0 < (c.sum fun f t => t * (weilPoleTerm (EF.weilTest f.1 f.1)).re) ∧
          0 ≤ (c.sum fun f t => t * weilArchRe (EF.weilTest f.1 f.1)) ∧
            (c.sum fun f t => t * weilArchRe (EF.weilTest f.1 f.1)) <
              ε * c.sum fun f t => t * (weilPoleTerm (EF.weilTest f.1 f.1)).re := by
  obtain ⟨c, hc, hnull, hneg⟩ := exists_blind_arch_add_mul_pole_neg (neg_ne_zero.mpr hε.ne')
  have hA := riemannHypothesis_iff_primeBlindPositiveAt_one.mp hRH c hc hnull
  rw [sum_poleWeightArchRe, sub_self, zero_mul, add_zero] at hA
  set A := c.sum fun f t => t * weilArchRe (EF.weilTest f.1 f.1)
  set P := c.sum fun f t => t * (weilPoleTerm (EF.weilTest f.1 f.1)).re
  have hP : 0 < P := by nlinarith
  exact ⟨c, hc, hnull, hP, hA, by linarith⟩

end RHTower

end
