import GaloisForLFunctions.ArithmeticScatteringHolography.TheCurveDatumOfABlackHole

/-!
# The Krein law at every genus

Over a curve of any genus the state of the ringdown is a probe `e`, and the Krein square of a probe is the Toeplitz
form of the normalized traces (`CurveDatum.toeplitz`). Three facts hold for every curve datum, geometric or not.

* **Translation invariance** (`toeplitz_shift`). Delaying a probe by one double tick does not change the form. In
  the energy normalization, the Krein square is divided by `q` per double tick (`curveKrein_step`), for every datum.
* **Liouville.** A mode and its functional-equation partner multiply to `q^{-n}` at double tick `n`
  (`normalizedMode_mul_partner`). So partners have rates with sum `½`, at every genus.
* **The sign.** The form is nonnegative on all probes exactly when the datum is unitary
  (`toeplitz_nonneg_iff_unitary`). The Bode integral, the inner mass, then vanishes
  (`krein_tfae`).

So the genus-one law is the first case of one structure, and over `ℤ` the same structure is the scale isometry of the
Weil form. The form is the only object in the programme that has the universal rate before knowing anything about
the zeros.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.ArithmeticScatteringHolography

open ArithmeticCastelnuovoSeveri ArithmeticInnerFunctionTheory

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- **The Krein form is translation invariant**: delaying a probe by one double tick does not change it. -/
theorem toeplitz_shift (S : Finset ℕ) (e : ℕ → ℝ) :
    D.toeplitz (S.map (addLeftEmbedding 1)) (fun k => e (k - 1)) = D.toeplitz S e := by
  unfold CurveDatum.toeplitz
  simp only [Finset.sum_map, addLeftEmbedding_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hdist : Nat.dist (1 + k) (1 + l) = Nat.dist k l := by
    simp [Nat.dist]
    omega
  simp [hdist]

/-- The Krein square in the energy normalization, at double tick `n`. -/
def curveKrein (S : Finset ℕ) (e : ℕ → ℝ) (n : ℕ) : ℝ := D.toeplitz S e / D.q ^ n

/-- **The Krein law at every genus.** The Krein square is divided by `q` per double tick. -/
theorem curveKrein_step (S : Finset ℕ) (e : ℕ → ℝ) (n : ℕ) :
    curveKrein D S e (n + 1) = curveKrein D S e n / D.q := by
  have hq : D.q ≠ 0 := by linarith [D.one_lt_q]
  unfold curveKrein
  rw [pow_succ]
  field_simp

/-- The amplitude of the mode of an eigenvalue at double tick `n`, in the energy normalization:
`(α/q)^n = β^n q^{-n/2}`. -/
def normalizedMode (i : ι) (n : ℕ) : ℂ := D.β i ^ n / (D.sqrtq : ℂ) ^ n

/-- **Liouville at every genus.** A mode and its functional-equation partner multiply to `q^{-n}`. -/
theorem normalizedMode_mul_partner (i : ι) (n : ℕ) :
    normalizedMode D i n * normalizedMode D (D.fePerm i) n = ((D.q : ℂ) ^ n)⁻¹ := by
  have hr : (D.sqrtq : ℂ) ≠ 0 := by exact_mod_cast D.sqrtq_pos.ne'
  have hrr : (D.q : ℂ) = (D.sqrtq : ℂ) ^ 2 := by
    rw [← D.sqrtq_sq]
    push_cast
    ring
  unfold normalizedMode
  have hprod : D.β i ^ n * D.β (D.fePerm i) ^ n = 1 := by
    rw [← mul_pow, mul_comm, D.β_fePerm, one_pow]
  rw [div_mul_div_comm, hprod, hrr]
  field_simp
  ring

/-- **The sign of the Krein form.** It is nonnegative on all probes exactly when the datum is unitary. -/
theorem toeplitz_nonneg_iff_unitary :
    (∀ (S : Finset ℕ) (e : ℕ → ℝ), 0 ≤ D.toeplitz S e) ↔ ∀ i, ‖D.β i‖ = 1 := by
  rw [← D.hodgeIndexOnSpan_iff_unitary]
  have hr : 0 < D.sqrtq := D.sqrtq_pos
  constructor
  · intro h S d
    rw [D.spanDefect_eq_toeplitz]
    exact h S _
  · intro h S e
    have := h S (fun k => e k / D.sqrtq ^ k)
    rw [D.spanDefect_eq_toeplitz] at this
    have he : (fun k => e k / D.sqrtq ^ k * D.sqrtq ^ k) = e := by
      funext k
      have : D.sqrtq ^ k ≠ 0 := pow_ne_zero k hr.ne'
      field_simp
    rwa [he] at this

/-- **The law as one statement.** The Bode integral vanishes, the modes lie on the universal circle, and the Krein form
is positive: these are the same condition. -/
theorem krein_tfae [Nonempty ι] :
    List.TFAE [innerMass D = 0, ∀ i, ‖D.β i‖ = 1,
      ∀ (S : Finset ℕ) (e : ℕ → ℝ), 0 ≤ D.toeplitz S e] := by
  tfae_have 1 ↔ 2 := innerMass_eq_zero_iff D
  tfae_have 3 ↔ 2 := toeplitz_nonneg_iff_unitary D
  tfae_finish

/-- **The Bode integral at every genus.** The mean of `log |P|` on the universal circle is the total damping deficit
below the universal rate. -/
theorem bode_integral_every_genus (hne : ∀ i, D.β i ≠ 0) :
    Real.circleAverage (fun v : ℂ => Real.log ‖lPoly D v‖) 0 1 =
      ∑ i, 2 * Real.log D.q * max (1 / 4 - dampingRate D.q (D.β i * (D.sqrtq : ℂ))) 0 := by
  rw [circleAverage_log_norm_lPoly]
  unfold innerMass
  refine Finset.sum_congr rfl fun i _ => ?_
  have hr : (D.sqrtq : ℂ) ≠ 0 := by exact_mod_cast D.sqrtq_pos.ne'
  have ha : D.β i * (D.sqrtq : ℂ) ≠ 0 := mul_ne_zero (hne i) hr
  rw [← posLog_eq_rate_deficit D.one_lt_q ha]
  congr 2
  unfold CurveDatum.sqrtq at hr ⊢
  field_simp

end GaloisForLFunctions.ArithmeticScatteringHolography

end
