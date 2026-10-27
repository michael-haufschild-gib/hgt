import GaloisForLFunctions.ArithmeticCorrespondencePositivity.XiRealReciprocalField
import GaloisForLFunctions.RHTower.LevinsonDetectorRightCount
import GaloisForLFunctions.ArithmeticElectrostatics.TheTransverseEnergyOfTheZeroDivisor

/-!
# The external field is a prime sum

Right of the critical strip every charge lies to the left of the observation point, so the
transverse field of the zero divisor there is a sum of positive Coulomb terms; and there the
explicit formula computes it from the primes. Equating the two computations gives an
**alignment law**: the primes cannot align at a height beyond what the archimedean field allows,
less the pull of the charges at that height.

* **The external field** (`re_logDeriv_xi_eq_tsum_of_one_lt_re`, `re_reciprocal_pos_of_one_lt_re`):
  for `Re s > 1`, `Re ξ′/ξ(s) = Σ_ρ Re 1/(s − ρ)`, each term `(σ − β)/|s − ρ|² > 0`.
* **The external field law** (`re_LSeries_vonMangoldt_add_sum_le`): for `Re s > 1` and every finite
  set `F` of zero copies,
  `Re Σ Λ(n) n^{−s} + Σ_{ρ∈F} Re 1/(s − ρ) ≤ Re (archFactor′/archFactor)(s)`;
  the prime field `Re Σ Λ(n) n^{−s} = Σ Λ(n) n^{−σ} cos(t log n)` (`re_LSeries_vonMangoldt_eq`).
* **Anti-alignment at zero ordinates** (`re_LSeries_vonMangoldt_le_at_zero_ordinate`): at
  `s = σ + iγ`, `σ > 1`, with `γ` the ordinate of a zero of real part `β` and multiplicity `m`,
  `Σ Λ(n) n^{−σ} cos(γ log n) ≤ Re (archFactor′/archFactor)(s) − m/(σ − β)`. A deep zero forces the
  primes out of alignment at its own ordinate, by its full Coulomb term.
* **Escape** (`riemannHypothesis_of_transverseForce_zero_of_energy_lt_top`): the marginality identity
  and finite transverse energy give RH; escape of depth to infinite height is the
  infinite-energy regime.

The outward reserve of a terminal is the interior counterpart: just right of an off-line zero, the
same field is bounded below by the zero's own term. The alignment question (Q1 of the frontier) is
whether the prime side can supply the matching upper bound inside the strip.
-/

open RHTower GaloisForLFunctions.ArithmeticCorrespondencePositivity ArithmeticFunction
open scoped ENNReal

namespace GaloisForLFunctions.ArithmeticElectrostatics

noncomputable section

/-- Right of the strip `ζ` has no zeros, so `ξ′/ξ = archFactor′/archFactor + ζ′/ζ` and `ξ ≠ 0`. -/
theorem xi_ne_zero_and_logDeriv_split {s : ℂ} (hs : 1 < s.re) :
    xi s ≠ 0 ∧ logDeriv xi s = logDeriv archFactor s + logDeriv riemannZeta s := by
  have hs1 : s ≠ 1 := fun h => by rw [h, Complex.one_re] at hs; exact lt_irrefl _ hs
  exact logDeriv_xi_eq_archFactor_add_of_re_pos (by linarith) hs1
    (riemannZeta_ne_zero_of_one_lt_re hs)

/-- **The external field**: `Re ξ′/ξ(s) = Σ_ρ Re 1/(s − ρ)` for `Re s > 1`. -/
theorem re_logDeriv_xi_eq_tsum_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    (logDeriv xi s).re = ∑' q : XiZeroCopy, ((s - (q.1 : ℂ))⁻¹).re := by
  rw [re_logDeriv_xi_eq_realReciprocal_tsum (xi_ne_zero_and_logDeriv_split hs).1]
  exact tsum_congr fun q => by simp [xiRealReciprocal]

/-- Each Coulomb term of the external field is positive. -/
theorem re_reciprocal_pos_of_one_lt_re {s : ℂ} (hs : 1 < s.re) (q : XiZeroCopy) :
    0 < ((s - (q.1 : ℂ))⁻¹).re := by
  have hq := (xiDivisorSupport_re_mem q.1).2
  have hd : 0 < (s - (q.1 : ℂ)).re := by rw [Complex.sub_re]; linarith
  rw [Complex.inv_re]
  exact div_pos hd (Complex.normSq_pos.mpr fun h => by rw [h, Complex.zero_re] at hd; exact lt_irrefl _ hd)

/-- The prime field is the real part of `L(Λ, s)`: `Re L(Λ, s) = −Re ζ′/ζ(s)`. -/
theorem re_LSeries_vonMangoldt_eq_neg {s : ℂ} (hs : 1 < s.re) :
    (LSeries (fun n => (vonMangoldt n : ℂ)) s).re = -(logDeriv riemannZeta s).re := by
  rw [LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs, logDeriv_apply, neg_div, Complex.neg_re]

/-- **The external field law**: for `Re s > 1` and every finite set `F` of zero copies,
`Re L(Λ, s) + Σ_{ρ ∈ F} Re 1/(s − ρ) ≤ Re (archFactor′/archFactor)(s)`. -/
theorem re_LSeries_vonMangoldt_add_sum_le {s : ℂ} (hs : 1 < s.re) (F : Finset XiZeroCopy) :
    (LSeries (fun n => (vonMangoldt n : ℂ)) s).re + ∑ q ∈ F, ((s - (q.1 : ℂ))⁻¹).re ≤
      (logDeriv archFactor s).re := by
  have hsplit := (xi_ne_zero_and_logDeriv_split hs).2
  have hfield := re_logDeriv_xi_eq_tsum_of_one_lt_re hs
  have hsum : Summable fun q : XiZeroCopy => ((s - (q.1 : ℂ))⁻¹).re := by
    have := xiRealReciprocal_summable s (h := 0) (by norm_num)
    exact this.congr fun q => by simp [xiRealReciprocal]
  have hle : ∑ q ∈ F, ((s - (q.1 : ℂ))⁻¹).re ≤ ∑' q : XiZeroCopy, ((s - (q.1 : ℂ))⁻¹).re :=
    hsum.sum_le_tsum F fun q _ => (re_reciprocal_pos_of_one_lt_re hs q).le
  rw [re_LSeries_vonMangoldt_eq_neg hs]
  have : (logDeriv xi s).re = (logDeriv archFactor s).re + (logDeriv riemannZeta s).re := by
    rw [hsplit, Complex.add_re]
  linarith

/-- The prime field as a cosine sum: `Re L(Λ, σ + it) = Σ Λ(n) n^{−σ} cos(t log n)`. -/
theorem re_LSeries_vonMangoldt_eq {s : ℂ} (hs : 1 < s.re) :
    (LSeries (fun n => (vonMangoldt n : ℂ)) s).re =
      ∑' n : ℕ, vonMangoldt n * (n : ℝ) ^ (-s.re) * Real.cos (s.im * Real.log n) := by
  have hsum := LSeriesSummable_vonMangoldt hs
  rw [LSeries, Complex.re_tsum hsum]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term]
  rw [LSeries.term_of_ne_zero hn.ne', div_eq_mul_inv, Complex.re_ofReal_mul]
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [← Complex.cpow_neg, Complex.cpow_def_of_ne_zero hn0, Complex.exp_re,
    ← Complex.ofReal_natCast, ← Complex.ofReal_log (Nat.cast_nonneg n)]
  simp only [Complex.re_ofReal_mul, Complex.im_ofReal_mul, Complex.neg_re, Complex.neg_im]
  rw [Real.rpow_def_of_pos (by exact_mod_cast hn),
    show Real.log n * -s.im = -(s.im * Real.log n) by ring, Real.cos_neg]
  ring

/-- **Anti-alignment at a zero ordinate**: at `s = σ + iγ` with `γ` the ordinate of a zero of real
part `β` and multiplicity `m`, the prime field is at most the archimedean field minus `m/(σ − β)`. -/
theorem re_LSeries_vonMangoldt_le_at_zero_ordinate (p : XiZeroCopy) {σ : ℝ} (hσ : 1 < σ) :
    (LSeries (fun n => (vonMangoldt n : ℂ)) (σ + (p.1 : ℂ).im * Complex.I)).re ≤
      (logDeriv archFactor (σ + (p.1 : ℂ).im * Complex.I)).re -
        ((xiZeroCopyFiber p.1).card : ℝ) / (σ - (p.1 : ℂ).re) := by
  set s : ℂ := σ + (p.1 : ℂ).im * Complex.I
  have hs : 1 < s.re := by simp [s, hσ]
  have h := re_LSeries_vonMangoldt_add_sum_le hs (xiZeroCopyFiber p.1)
  have hβ : (p.1 : ℂ).re < 1 := (xiDivisorSupport_re_mem p.1).2
  have hterm : ∀ q ∈ xiZeroCopyFiber p.1, ((s - (q.1 : ℂ))⁻¹).re = 1 / (σ - (p.1 : ℂ).re) := by
    intro q hq
    rw [(mem_xiZeroCopyFiber).mp hq]
    have hsub : s - ((p.1 : XiDivisorSupport) : ℂ) = ((σ - (p.1 : ℂ).re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [s]
    rw [hsub, ← Complex.ofReal_inv, Complex.ofReal_re, one_div]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul] at h
  rw [div_eq_mul_one_div]
  linarith

/-! ### Escape is infinite energy -/

/-- **The marginality identity and finite transverse energy give RH.** -/
theorem riemannHypothesis_of_transverseForce_zero_of_energy_lt_top
    (hH : ∀ j : XiDivisorSupport, transverseForce j = 0) (hE : divisorTransverseEnergy < ⊤) :
    RiemannHypothesis :=
  riemannHypothesis_of_harmonic_of_offLineSupport_finite hH
    (divisorTransverseEnergy_lt_top_iff.mp hE)

end

end GaloisForLFunctions.ArithmeticElectrostatics
