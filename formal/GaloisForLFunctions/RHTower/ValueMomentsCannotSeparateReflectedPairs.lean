import Mathlib

/-!
# Value moments cannot separate a reflected pair from two critical zeros

Let `a` be a weight with real Dirichlet coefficients, for example `a = ζ'M` with a mollifier `M`.
Contour integration evaluates holomorphic zero sums `Σ_ρ F(a(ρ), a(1 − ρ))` without RH, and real
coefficients give `a(1 − ρ) = conj (a (1 − ρ̄))`.

* At a critical zero `1 − ρ̄ = ρ`, so the summand is `F(a(ρ), conj a(ρ))`. For `F(z, w) = z w` it is
  the Hermitian square `|a(ρ)|²` that Conrey–Ghosh–Gonek use under RH.
* An off-line zero `ρ` and its reflection `ρ' = 1 − ρ̄` (same height) contribute
  `F(a(ρ), conj a(ρ')) + F(a(ρ'), conj a(ρ))`.

`ZeroValueConfig` is this zero side: the values at simple critical zeros and the value pairs at
reflected off-line pairs. Its `moment F` is the holomorphic zero sum above.

* **Mimicry** (`moment_mimic_eq_moment_doubled`): a reflected pair whose two values agree has the
  moment of two critical zeros carrying that value, for every `F`. A lower bound for the critical
  count that depends only on value moments is therefore at most `0` on every configuration whose
  critical values come in equal pairs (`lowerBound_le_zero_of_doubled`), and the
  Conrey–Ghosh–Gonek ratio `|S₁|²/S₂` is not an unconditional lower bound for the critical count
  (`not_exists_cgg_ratio_lower_bound`).
* **Indefinite reflected square** (`re_secondMoment_antisymmetricPair`): a pair with values
  `z, −z` contributes `−2|z|²` to `S₂`, so `S₂` does not bound `Σ|a|²` from above.
* **What the data certify** (`norm_firstMoment_sq_le`): with the antisymmetric defect
  `D = Σ_pairs |a(ρ) − a(ρ')|²/2`,
  `|S₁|² ≤ (#critical + 2·#pairs)(Re S₂ + D)`.
  This is Cauchy–Schwarz over all simple zeros, critical or reflected, and `D` is exactly what the
  reflected second moment hides. Value moments count zeros that carry the weight, not zeros on
  the line.
-/

open ComplexConjugate Finset

noncomputable section

namespace RHTower

/-- Values of a weight `a` on the zero side: `critValue i = a(ρᵢ)` at simple critical zeros, and
`(left j, right j) = (a(ρⱼ), a(1 − ρ̄ⱼ))` at reflected off-line pairs. -/
structure ZeroValueConfig (ι κ : Type*) where
  crit : Finset ι
  critValue : ι → ℂ
  pairs : Finset κ
  left : κ → ℂ
  right : κ → ℂ

namespace ZeroValueConfig

variable {ι κ : Type*}

/-- The holomorphic zero sum `Σ_ρ F(a(ρ), a(1 − ρ))`. -/
def moment (C : ZeroValueConfig ι κ) (F : ℂ → ℂ → ℂ) : ℂ :=
  ∑ i ∈ C.crit, F (C.critValue i) (conj (C.critValue i)) +
    ∑ j ∈ C.pairs, (F (C.left j) (conj (C.right j)) + F (C.right j) (conj (C.left j)))

/-- First moment `S₁ = Σ_ρ a(ρ)`. -/
def firstMoment (C : ZeroValueConfig ι κ) : ℂ := C.moment fun z _ => z

/-- Reflected second moment `S₂ = Σ_ρ a(ρ) a(1 − ρ)`. -/
def secondMoment (C : ZeroValueConfig ι κ) : ℂ := C.moment fun z w => z * w

/-- Antisymmetric defect `D = Σ_pairs |a(ρ) − a(ρ')|²/2`. -/
def antisymmetricDefect (C : ZeroValueConfig ι κ) : ℝ :=
  ∑ j ∈ C.pairs, ‖C.left j - C.right j‖ ^ 2 / 2

/-- Reflected pairs carrying the same value `x j` at both members. -/
def mimic (P : Finset κ) (x : κ → ℂ) : ZeroValueConfig Empty κ where
  crit := ∅
  critValue := Empty.elim
  pairs := P
  left := x
  right := x

/-- Two critical zeros carrying the value `x j` for each `j ∈ P`. -/
def doubled (P : Finset κ) (x : κ → ℂ) : ZeroValueConfig (κ × Bool) Empty where
  crit := P ×ˢ univ
  critValue := fun i => x i.1
  pairs := ∅
  left := Empty.elim
  right := Empty.elim

/-- One reflected pair with values `z` and `−z`. -/
def antisymmetricPair (z : ℂ) : ZeroValueConfig Empty Unit where
  crit := ∅
  critValue := Empty.elim
  pairs := {()}
  left := fun _ => z
  right := fun _ => -z

/-- **Mimicry.** Equal-valued reflected pairs have every value moment of the configuration with
two critical zeros per pair. -/
theorem moment_mimic_eq_moment_doubled (P : Finset κ) (x : κ → ℂ) (F : ℂ → ℂ → ℂ) :
    (mimic P x).moment F = (doubled P x).moment F := by
  simp [moment, mimic, doubled, sum_product, two_mul]

theorem card_crit_doubled (P : Finset κ) (x : κ → ℂ) :
    (doubled P x).crit.card = 2 * P.card := by
  simp [doubled, card_product, mul_comm]

/-- **No value-moment certificate of criticality.** If `Φ` bounds the critical count from below
using only the value moments, then `Φ ≤ 0` on the data of `2·#P` critical zeros whose values come in
equal pairs: the same data come from `#P` reflected pairs and no critical zero. -/
theorem lowerBound_le_zero_of_doubled (Φ : ((ℂ → ℂ → ℂ) → ℂ) → ℝ)
    (hΦ : ∀ {ι κ : Type} (C : ZeroValueConfig ι κ), Φ C.moment ≤ C.crit.card)
    {κ : Type} (P : Finset κ) (x : κ → ℂ) :
    Φ (doubled P x).moment ≤ 0 := by
  have h := hΦ (mimic P x)
  rw [show (mimic P x).moment = (doubled P x).moment from
    funext (moment_mimic_eq_moment_doubled P x)] at h
  simpa [mimic] using h

/-- **The CGG ratio is not an unconditional bound.** No positive multiple of `|S₁|²/Re S₂`
bounds the critical count: one equal-valued reflected pair has `S₁ = S₂ = 2` and no critical
zero. -/
theorem not_exists_cgg_ratio_lower_bound :
    ¬ ∃ c : ℝ, 0 < c ∧ ∀ {ι κ : Type} (C : ZeroValueConfig ι κ), 0 < C.secondMoment.re →
      c * ‖C.firstMoment‖ ^ 2 / C.secondMoment.re ≤ C.crit.card := by
  rintro ⟨c, hc, h⟩
  have hS₂ : (mimic ({()} : Finset Unit) fun _ => (1 : ℂ)).secondMoment = 2 := by
    simp [secondMoment, moment, mimic]; norm_num
  have hS₁ : (mimic ({()} : Finset Unit) fun _ => (1 : ℂ)).firstMoment = 2 := by
    simp [firstMoment, moment, mimic]; norm_num
  have key := h (mimic ({()} : Finset Unit) fun _ => (1 : ℂ)) (by rw [hS₂]; norm_num)
  rw [hS₁, hS₂] at key
  simp [mimic] at key
  nlinarith

/-- **Indefinite reflected square.** A pair with values `z, −z` contributes `−2|z|²` to `Re S₂`
and nothing to `S₁`. -/
theorem re_secondMoment_antisymmetricPair (z : ℂ) :
    (antisymmetricPair z).secondMoment.re = -2 * ‖z‖ ^ 2 ∧
      (antisymmetricPair z).firstMoment = 0 := by
  constructor
  · simp only [secondMoment, moment, antisymmetricPair, sum_empty, sum_singleton, zero_add]
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, Complex.mul_re]
    ring
  · simp [firstMoment, moment, antisymmetricPair]

/-- Cauchy–Schwarz for two blocks with different weights. -/
theorem add_sq_le_of_sq_le {A B n m X Y : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hn : 0 ≤ n)
    (hm : 0 ≤ m) (hX : 0 ≤ X) (hY : 0 ≤ Y) (hAX : A ^ 2 ≤ n * X) (hBY : B ^ 2 ≤ m * Y) :
    (A + B) ^ 2 ≤ (n + m) * (X + Y) := by
  have hprod : (A * B) ^ 2 ≤ (n * X) * (m * Y) := by
    rw [mul_pow]
    exact mul_le_mul hAX hBY (sq_nonneg _) (by positivity)
  have hsq : (2 * A * B) ^ 2 ≤ (n * Y + m * X) ^ 2 := by
    nlinarith [sq_nonneg (n * Y - m * X)]
  have hcross : 2 * A * B ≤ n * Y + m * X :=
    (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).1 hsq
  nlinarith

/-- The real part of the reflected second moment: squares at critical zeros, `2 Re(a(ρ) conj a(ρ'))`
at reflected pairs. -/
theorem re_secondMoment (C : ZeroValueConfig ι κ) :
    C.secondMoment.re = ∑ i ∈ C.crit, ‖C.critValue i‖ ^ 2 +
      ∑ j ∈ C.pairs, 2 * (C.left j * conj (C.right j)).re := by
  simp only [secondMoment, moment, Complex.add_re, Complex.re_sum]
  congr 1
  · refine sum_congr rfl fun i _ => ?_
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  · refine sum_congr rfl fun j _ => ?_
    simp [Complex.mul_re]
    ring

/-- **What value moments certify.** `|S₁|² ≤ (#critical + 2·#pairs)(Re S₂ + D)`: the first and
reflected second moments bound the number of simple zeros of either kind once the antisymmetric
defect `D` is added back. -/
theorem norm_firstMoment_sq_le (C : ZeroValueConfig ι κ) :
    ‖C.firstMoment‖ ^ 2 ≤
      ((C.crit.card : ℝ) + 2 * C.pairs.card) * (C.secondMoment.re + C.antisymmetricDefect) := by
  set A := ∑ i ∈ C.crit, ‖C.critValue i‖
  set B := ∑ j ∈ C.pairs, ‖C.left j + C.right j‖
  have hS₁ : C.firstMoment = ∑ i ∈ C.crit, C.critValue i + ∑ j ∈ C.pairs, (C.left j + C.right j) :=
    rfl
  have hnorm : ‖C.firstMoment‖ ≤ A + B := by
    rw [hS₁]
    exact (norm_add_le _ _).trans (add_le_add (norm_sum_le _ _) (norm_sum_le _ _))
  have hA : A ^ 2 ≤ C.crit.card * ∑ i ∈ C.crit, ‖C.critValue i‖ ^ 2 := sq_sum_le_card_mul_sum_sq
  have hB : B ^ 2 ≤ C.pairs.card * ∑ j ∈ C.pairs, ‖C.left j + C.right j‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  -- each pair: |x + y|²/2 = 2 Re(x conj y) + |x − y|²/2
  have hpair : ∀ j ∈ C.pairs, ‖C.left j + C.right j‖ ^ 2 / 2 =
      2 * (C.left j * conj (C.right j)).re + ‖C.left j - C.right j‖ ^ 2 / 2 := by
    intro j _
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq, Complex.normSq_add,
      Complex.normSq_sub]
    ring
  have hY : ∑ j ∈ C.pairs, ‖C.left j + C.right j‖ ^ 2 / 2 =
      ∑ j ∈ C.pairs, 2 * (C.left j * conj (C.right j)).re + C.antisymmetricDefect := by
    rw [antisymmetricDefect, ← sum_add_distrib]
    exact sum_congr rfl hpair
  have hB' : B ^ 2 ≤ (2 * C.pairs.card) * ∑ j ∈ C.pairs, ‖C.left j + C.right j‖ ^ 2 / 2 := by
    rw [← sum_div]
    linarith
  have hcs := add_sq_le_of_sq_le (A := A) (B := B) (sum_nonneg fun i _ => norm_nonneg _)
    (sum_nonneg fun j _ => norm_nonneg _) (Nat.cast_nonneg C.crit.card)
    (by positivity : (0 : ℝ) ≤ 2 * C.pairs.card)
    (sum_nonneg fun i _ => sq_nonneg ‖C.critValue i‖)
    (sum_nonneg fun j _ => by positivity : (0 : ℝ) ≤ ∑ j ∈ C.pairs, ‖C.left j + C.right j‖ ^ 2 / 2)
    hA hB'
  rw [hY, ← add_assoc, ← re_secondMoment] at hcs
  calc ‖C.firstMoment‖ ^ 2 ≤ (A + B) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ _ := hcs

end ZeroValueConfig

end RHTower
