import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FrobeniusSpanHodgeIndexIsRH
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FakeCurvesAndTheWindowLaw

/-!
# The comb of a curve

Over a curve of genus `g` over `𝔽_q` the degree points are the powers `q^k`: the comb is `q^ℤ`,
one orbit of one Frobenius. In the coordinates `e_k` of the unitary graphs `Γ_k/q^{k/2}` the
pairing of a curve datum has the same shape as the normal form over `ℤ`, with three differences:
there are no jets; the contact of `Γ_k` and `Γ_l` is the point count `N_{|k−l|}/q^{|k−l|/2}`; and
the diagonal is the same formula at the lag `0`, the Lefschetz number `N_0 = 2 − 2g` of the
identity. No finite part is taken and no counterterm appears: a curve has `2g` zeros.

* **One formula with its diagonal** (`curvePairing_eq_sum`): the pairing is
  `Σ_{k,l} e_k e_l N_{|k−l|}/q^{|k−l|/2}`.
* **Weil's form on the comb of a curve** (`curveCombForm_eq_toeplitz`): `2 d₁ d₂ − D·D` is the
  Toeplitz form `Σ e_k e_l Re Σ_i β_i^{|k−l|}` of the normalized Frobenius eigenvalues, the sum
  over the zeros.
* **The inequality is purity** (`curveCombForm_nonneg_iff_unitary`): `D·D ≤ 2 d₁ d₂` for every
  real divisor on every finite set of degree points iff every `|β_i| = 1`. Over a curve the
  statement at finite scale and the statement on all windows coincide.
* **One graph** (`curveCombForm_singleton`): on a single degree point the form is `2g·e_k²`.
* **The golden datum** (`exists_curveCombForm_goldenDatum_neg`): the datum with `q = 5` and the
  eigenvalues `φ^{±1}` has integral point counts and a divisor with `D·D > 2 d₁ d₂`.
-/

open Finset

noncomputable section

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

open ArithmeticCastelnuovoSeveri

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The contact of `Γ_k` and `Γ_l`, `|k − l| = j`, in the unitary normalization:
`N_j/q^{j/2}`. -/
def curveContact (j : ℕ) : ℝ := D.pointCount j / D.sqrtq ^ j

/-- The pairing of the real divisor `Σ e_k γ_k` on the comb of the curve: the contacts off the
diagonal and `2 − 2g` on it. -/
def curvePairing (S : Finset ℕ) (e : ℕ → ℝ) : ℝ :=
  ∑ k ∈ S, ∑ l ∈ S.erase k, e k * e l * curveContact D (Nat.dist k l) +
    ∑ k ∈ S, e k ^ 2 * (2 - Fintype.card ι)

/-- The first degree `Σ e_k q^{−k/2}`. -/
def curveDegOne (S : Finset ℕ) (e : ℕ → ℝ) : ℝ := ∑ k ∈ S, e k / D.sqrtq ^ k

/-- The second degree `Σ e_k q^{k/2}`. -/
def curveDegTwo (S : Finset ℕ) (e : ℕ → ℝ) : ℝ := ∑ k ∈ S, e k * D.sqrtq ^ k

/-- Weil's form on the comb of the curve: `2 d₁ d₂ − D·D`. -/
def curveCombForm (S : Finset ℕ) (e : ℕ → ℝ) : ℝ :=
  2 * (curveDegOne D S e * curveDegTwo D S e) - curvePairing D S e

/-- The diagonal is the contact formula at the lag `0`: `N_0 = 2 − 2g`. -/
theorem curveContact_zero : curveContact D 0 = 2 - Fintype.card ι := by
  rw [curveContact, D.pointCount_zero, pow_zero, div_one]

/-- **One formula with its diagonal.** -/
theorem curvePairing_eq_sum (S : Finset ℕ) (e : ℕ → ℝ) :
    curvePairing D S e = ∑ k ∈ S, ∑ l ∈ S, e k * e l * curveContact D (Nat.dist k l) := by
  rw [curvePairing, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  rw [← Finset.add_sum_erase S _ hk, Nat.dist_self, curveContact_zero]
  ring

/-- The pairing in the coordinates `d_k = e_k/q^{k/2}` of the graphs. -/
theorem curvePairing_eq_graphPair (S : Finset ℕ) (e : ℕ → ℝ) :
    curvePairing D S e =
      ∑ k ∈ S, ∑ l ∈ S, e k / D.sqrtq ^ k * (e l / D.sqrtq ^ l) * D.graphPair k l := by
  have hs0 := D.sqrtq_pos
  have key : ∀ x y a b c m n : ℝ, a ≠ 0 → b ≠ 0 → c ≠ 0 → m * c = a * b →
      x / a * (y / b) * (m * n) = x * y * (n / c) := by
    intro x y a b c m n ha hb hc h
    have hm : m = a * b / c := (eq_div_iff hc).mpr h
    rw [hm]
    field_simp
  rw [curvePairing_eq_sum]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  have hs : D.q ^ min k l * D.sqrtq ^ Nat.dist k l = D.sqrtq ^ k * D.sqrtq ^ l := by
    obtain ⟨-, h2⟩ := CurveDatum.min_add_dist k l
    rw [← D.sqrtq_sq, ← pow_mul, ← pow_add, ← pow_add, h2]
  rw [CurveDatum.graphPair, curveContact]
  exact (key _ _ _ _ _ _ _ (pow_ne_zero _ hs0.ne') (pow_ne_zero _ hs0.ne')
    (pow_ne_zero _ hs0.ne') hs).symm

/-- Weil's form on the comb of the curve is the defect of the span class with the coefficients
`e_k/q^{k/2}`. -/
theorem curveCombForm_eq_spanDefect (S : Finset ℕ) (e : ℕ → ℝ) :
    curveCombForm D S e = D.spanDefect S fun k => e k / D.sqrtq ^ k := by
  have hs0 := D.sqrtq_pos
  have h2 : curveDegTwo D S e = ∑ k ∈ S, e k / D.sqrtq ^ k * D.q ^ k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk : D.sqrtq ^ k ≠ 0 := pow_ne_zero _ hs0.ne'
    rw [← D.sqrtq_sq, ← pow_mul, mul_comm 2 k, pow_mul, sq]
    field_simp
  rw [curveCombForm, CurveDatum.spanDefect, curvePairing_eq_graphPair, h2, curveDegOne]
  ring

/-- **Weil's form on the comb of a curve is the Toeplitz form of the Frobenius eigenvalues.** -/
theorem curveCombForm_eq_toeplitz (S : Finset ℕ) (e : ℕ → ℝ) :
    curveCombForm D S e = D.toeplitz S e := by
  rw [curveCombForm_eq_spanDefect, D.spanDefect_eq_toeplitz]
  have hfun : (fun k => e k / D.sqrtq ^ k * D.sqrtq ^ k) = e :=
    funext fun k => div_mul_cancel₀ _ (pow_ne_zero _ D.sqrtq_pos.ne')
  rw [hfun]

/-- **Over a curve the inequality of Castelnuovo and Severi on the comb is purity.** -/
theorem curveCombForm_nonneg_iff_unitary :
    (∀ (S : Finset ℕ) (e : ℕ → ℝ), 0 ≤ curveCombForm D S e) ↔ ∀ i, ‖D.β i‖ = 1 := by
  rw [← D.hodgeIndexOnSpan_iff_unitary]
  constructor
  · intro h S d
    have h1 := h S fun k => d k * D.sqrtq ^ k
    rw [curveCombForm_eq_spanDefect] at h1
    have hfun : (fun k => d k * D.sqrtq ^ k / D.sqrtq ^ k) = d :=
      funext fun k => mul_div_cancel_right₀ _ (pow_ne_zero _ D.sqrtq_pos.ne')
    rwa [hfun] at h1
  · intro h S e
    rw [curveCombForm_eq_spanDefect]
    exact h S _

/-- **On one graph the form is `2g·e_k²`.** -/
theorem curveCombForm_singleton (k : ℕ) (e : ℕ → ℝ) :
    curveCombForm D {k} e = Fintype.card ι * e k ^ 2 := by
  rw [curveCombForm_eq_toeplitz, CurveDatum.toeplitz, Finset.sum_singleton, Finset.sum_singleton,
    Nat.dist_self, D.trace_zero]
  ring

/-- **The golden datum violates the inequality on its comb.** -/
theorem exists_curveCombForm_goldenDatum_neg :
    ∃ (S : Finset ℕ) (e : ℕ → ℝ), curveCombForm goldenDatum S e < 0 := by
  by_contra h
  refine goldenDatum_not_unitary ((curveCombForm_nonneg_iff_unitary goldenDatum).mp fun S e => ?_)
  by_contra hneg
  exact h ⟨S, e, not_le.mp hneg⟩

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
