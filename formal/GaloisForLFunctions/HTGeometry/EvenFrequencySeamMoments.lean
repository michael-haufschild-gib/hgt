import GaloisForLFunctions.HTGeometry.SingleEvenFrequency
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Tactic

/-!
# Seam moments of even exponential frequencies

The even local log-germ of a frequency `λ` with amplitude `B` is

`L(z) = B (cosh (λ √z) - 1) = ∑_{k ≥ 1} B λ ^ (2k) / (2k)! * z ^ k`,

and the shifted seam moment attached to a coefficient family `a` is

`T k = -2k (-1) ^ k * a k`.

Writing the coefficient of `z ^ k` as `M k / (2k)!` gives the closed form

`T k = (-1) ^ (k + 1) * M k / (2k - 1)!`,

so the seam moments of any germ with positive `M` alternate in sign: the even-order ones are
strictly negative and therefore cannot be moments of a positive measure on the half line.

The half-turn parity repair `a ↦ (-1)^(k+1) a` removes the alternation but replaces it by the
factorial Hankel geometry `U k = M k / (2k - 1)!`, whose first shifted determinant is still
negative.
-/

noncomputable section

namespace GaloisForLFunctions

open scoped BigOperators

/-- The shifted seam moment of a coefficient family. -/
def seamMoment (a : ℕ → ℝ) (k : ℕ) : ℝ := -(2 * (k : ℝ)) * (-1) ^ k * a k

/-- The half-turn parity repair of a coefficient family. -/
def halfTurnCoeff (a : ℕ → ℝ) (k : ℕ) : ℝ := (-1) ^ (k + 1) * a k

/-- The `z ^ k` coefficient of `B (cosh (λ √z) - 1)`. -/
def evenFrequencyCoeff (B lambda : ℝ) (k : ℕ) : ℝ :=
  B * lambda ^ (2 * k) / (Nat.factorial (2 * k))

theorem factorial_two_mul_eq {k : ℕ} (hk : 1 ≤ k) :
    (Nat.factorial (2 * k) : ℝ) = (2 * (k : ℝ)) * (Nat.factorial (2 * k - 1) : ℝ) := by
  have hpos : 2 * k ≠ 0 := by omega
  have hnat : (2 * k) * Nat.factorial (2 * k - 1) = Nat.factorial (2 * k) :=
    Nat.mul_factorial_pred hpos
  have := congrArg (fun n : ℕ => (n : ℝ)) hnat
  push_cast at this
  linarith [this]

/-- **Closed form of the seam moment.**  For a germ whose `z ^ k` coefficient is `M k / (2k)!`,
the shifted seam moment is `(-1) ^ (k + 1) M k / (2k - 1)!`. -/
theorem seamMoment_factorialCoeff (M : ℕ → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    seamMoment (fun j => M j / (Nat.factorial (2 * j))) k =
      (-1) ^ (k + 1) * M k / (Nat.factorial (2 * k - 1)) := by
  have hfac := factorial_two_mul_eq hk
  have hne : (Nat.factorial (2 * k - 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  have hk0 : (2 * (k : ℝ)) ≠ 0 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  rw [seamMoment, hfac, pow_succ]
  field_simp

/-- The seam moments of a single even frequency. -/
theorem seamMoment_evenFrequency (B lambda : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    seamMoment (evenFrequencyCoeff B lambda) k =
      (-1) ^ (k + 1) * (B * lambda ^ (2 * k)) / (Nat.factorial (2 * k - 1)) := by
  have hrewrite : evenFrequencyCoeff B lambda =
      fun j => (B * lambda ^ (2 * j)) / (Nat.factorial (2 * j)) := rfl
  rw [hrewrite]
  exact seamMoment_factorialCoeff (fun j => B * lambda ^ (2 * j)) hk

theorem seamMoment_evenFrequency_one (B lambda : ℝ) :
    seamMoment (evenFrequencyCoeff B lambda) 1 = B * lambda ^ 2 := by
  rw [seamMoment_evenFrequency B lambda (le_refl 1)]
  norm_num

theorem seamMoment_evenFrequency_two (B lambda : ℝ) :
    seamMoment (evenFrequencyCoeff B lambda) 2 = -B * lambda ^ 4 / 6 := by
  rw [seamMoment_evenFrequency B lambda (by norm_num)]
  norm_num [Nat.factorial]

theorem seamMoment_evenFrequency_three (B lambda : ℝ) :
    seamMoment (evenFrequencyCoeff B lambda) 3 = B * lambda ^ 6 / 120 := by
  rw [seamMoment_evenFrequency B lambda (by norm_num)]
  norm_num [Nat.factorial]

/-- **The single even frequency fails the first shifted Hankel test.** -/
theorem seamMoment_evenFrequency_det_neg {B lambda : ℝ} (hB : 0 < B) (hlambda : 0 < lambda) :
    seamMoment (evenFrequencyCoeff B lambda) 1 * seamMoment (evenFrequencyCoeff B lambda) 3 -
        seamMoment (evenFrequencyCoeff B lambda) 2 ^ 2 < 0 := by
  rw [seamMoment_evenFrequency_one, seamMoment_evenFrequency_two, seamMoment_evenFrequency_three]
  exact singleEvenFrequency_det_neg hB hlambda

/-- The half-turn repair turns the alternating seam moments into `2 k a k`. -/
theorem seamMoment_halfTurn (a : ℕ → ℝ) (k : ℕ) :
    seamMoment (halfTurnCoeff a) k = (2 * (k : ℝ)) * a k := by
  rw [seamMoment, halfTurnCoeff, pow_succ]
  have hsq : ((-1 : ℝ) ^ k) * ((-1 : ℝ) ^ k) = 1 := by
    rw [← pow_add, ← two_mul, pow_mul]
    norm_num
  linear_combination (2 * (k : ℝ) * a k) * hsq

theorem seamMoment_halfTurn_evenFrequency (B lambda : ℝ) {k : ℕ} (hk : 1 ≤ k) :
    seamMoment (halfTurnCoeff (evenFrequencyCoeff B lambda)) k =
      B * lambda ^ (2 * k) / (Nat.factorial (2 * k - 1)) := by
  have hfac := factorial_two_mul_eq hk
  have hne : (Nat.factorial (2 * k - 1) : ℝ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero _
  have hk0 : (2 * (k : ℝ)) ≠ 0 := by
    have : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  rw [seamMoment_halfTurn, evenFrequencyCoeff, hfac]
  field_simp

theorem seamMoment_halfTurn_one (B lambda : ℝ) :
    seamMoment (halfTurnCoeff (evenFrequencyCoeff B lambda)) 1 = B * lambda ^ 2 := by
  rw [seamMoment_halfTurn_evenFrequency B lambda (le_refl 1)]
  norm_num

theorem seamMoment_halfTurn_two (B lambda : ℝ) :
    seamMoment (halfTurnCoeff (evenFrequencyCoeff B lambda)) 2 = B * lambda ^ 4 / 6 := by
  rw [seamMoment_halfTurn_evenFrequency B lambda (by norm_num)]
  norm_num [Nat.factorial]

theorem seamMoment_halfTurn_three (B lambda : ℝ) :
    seamMoment (halfTurnCoeff (evenFrequencyCoeff B lambda)) 3 = B * lambda ^ 6 / 120 := by
  rw [seamMoment_halfTurn_evenFrequency B lambda (by norm_num)]
  norm_num [Nat.factorial]

/-- **The half-turn repaired frequency still fails the first shifted Hankel test.** -/
theorem seamMoment_halfTurn_det_neg {B lambda : ℝ} (hB : 0 < B) (hlambda : 0 < lambda) :
    seamMoment (halfTurnCoeff (evenFrequencyCoeff B lambda)) 1 *
          seamMoment (halfTurnCoeff (evenFrequencyCoeff B lambda)) 3 -
        seamMoment (halfTurnCoeff (evenFrequencyCoeff B lambda)) 2 ^ 2 < 0 := by
  rw [seamMoment_halfTurn_one, seamMoment_halfTurn_two, seamMoment_halfTurn_three]
  exact singleEvenFrequency_halfTurn_det_neg hB hlambda

/-! ### Sign alternation of a positive coefficient germ -/

/-- Odd-order seam moments of a positive germ are strictly positive. -/
theorem seamMoment_pos_of_odd {M : ℕ → ℝ} {k : ℕ} (hk : 1 ≤ k) (hM : 0 < M k) (hodd : Odd k) :
    0 < seamMoment (fun j => M j / (Nat.factorial (2 * j))) k := by
  rw [seamMoment_factorialCoeff M hk]
  have hsign : ((-1 : ℝ)) ^ (k + 1) = 1 := by
    obtain ⟨m, hm⟩ := hodd
    rw [hm]
    rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul]
    norm_num
  have hfacpos : (0 : ℝ) < (Nat.factorial (2 * k - 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  rw [hsign]
  positivity

/-- Even-order seam moments of a positive germ are strictly negative: such a germ is never a
Markov/Stieltjes source on the half line. -/
theorem seamMoment_neg_of_even {M : ℕ → ℝ} {k : ℕ} (hk : 1 ≤ k) (hM : 0 < M k) (heven : Even k) :
    seamMoment (fun j => M j / (Nat.factorial (2 * j))) k < 0 := by
  rw [seamMoment_factorialCoeff M hk]
  have hsign : ((-1 : ℝ)) ^ (k + 1) = -1 := by
    obtain ⟨m, hm⟩ := heven
    rw [hm, show m + m + 1 = 2 * m + 1 by ring, pow_succ, pow_mul]
    norm_num
  have hfacpos : (0 : ℝ) < (Nat.factorial (2 * k - 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  rw [hsign]
  have : (-1 : ℝ) * M k < 0 := by linarith
  exact div_neg_of_neg_of_pos this hfacpos

/-! ### The positive frequency cone -/

open MeasureTheory

/-- Every even moment of a nonzero positive measure on the open half line is strictly positive. -/
theorem integral_pow_pos_of_measure_pos {μ : Measure ℝ} {k : ℕ}
    (hμ : 0 < μ (Set.Ioi (0 : ℝ)))
    (hInt : IntegrableOn (fun l : ℝ => l ^ (2 * k)) (Set.Ioi 0) μ) :
    0 < ∫ l in Set.Ioi (0 : ℝ), l ^ (2 * k) ∂μ := by
  have hnonneg : ∀ l : ℝ, 0 ≤ l ^ (2 * k) := by
    intro l
    rw [pow_mul]
    positivity
  have hae : 0 ≤ᵐ[μ.restrict (Set.Ioi (0 : ℝ))] fun l : ℝ => l ^ (2 * k) :=
    Filter.Eventually.of_forall hnonneg
  rw [setIntegral_pos_iff_support_of_nonneg_ae hae hInt]
  have hsupp : Function.support (fun l : ℝ => l ^ (2 * k)) ∩ Set.Ioi (0 : ℝ) = Set.Ioi (0 : ℝ) := by
    ext l
    simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_Ioi, ne_eq, and_iff_right_iff_imp]
    intro hl
    exact pow_ne_zero _ (ne_of_gt hl)
  rw [hsupp]
  exact hμ

/-- **The positive even-frequency cone is not Markov.**  The second shifted seam moment of a
nonzero positive frequency measure is strictly negative. -/
theorem seamMoment_measureCone_two_neg {μ : Measure ℝ}
    (hμ : 0 < μ (Set.Ioi (0 : ℝ)))
    (hInt : IntegrableOn (fun l : ℝ => l ^ (2 * 2)) (Set.Ioi 0) μ) :
    seamMoment (fun j => (∫ l in Set.Ioi (0 : ℝ), l ^ (2 * j) ∂μ) / (Nat.factorial (2 * j))) 2
      < 0 :=
  seamMoment_neg_of_even (by norm_num)
    (integral_pow_pos_of_measure_pos hμ hInt) (by decide)

/-- Odd-order seam moments of a negative germ coefficient are strictly negative. -/
theorem seamMoment_neg_of_odd_of_neg {M : ℕ → ℝ} {k : ℕ} (hk : 1 ≤ k) (hM : M k < 0)
    (hodd : Odd k) : seamMoment (fun j => M j / (Nat.factorial (2 * j))) k < 0 := by
  rw [seamMoment_factorialCoeff M hk]
  have hsign : ((-1 : ℝ)) ^ (k + 1) = 1 := by
    obtain ⟨m, hm⟩ := hodd
    rw [hm, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul]
    norm_num
  have hfacpos : (0 : ℝ) < (Nat.factorial (2 * k - 1) : ℝ) := by
    exact_mod_cast Nat.factorial_pos _
  rw [hsign]
  have hnum : (1 : ℝ) * M k < 0 := by linarith
  exact div_neg_of_neg_of_pos hnum hfacpos

/-! ### Finite signed frequency atoms -/

/-- **Dominant frequency limit.**  A finite signed frequency sum is asymptotically governed by its
largest frequency. -/
theorem tendsto_signedFrequencySum_div {n : ℕ} (c x : Fin (n + 1) → ℝ)
    (hx0 : ∀ j, 0 < x j) (hmono : ∀ j : Fin (n + 1), j ≠ Fin.last n → x j < x (Fin.last n)) :
    Filter.Tendsto (fun k : ℕ => (∑ j, c j * x j ^ k) / x (Fin.last n) ^ k) Filter.atTop
      (nhds (c (Fin.last n))) := by
  have hL : 0 < x (Fin.last n) := hx0 _
  have hrewrite : ∀ k : ℕ, (∑ j, c j * x j ^ k) / x (Fin.last n) ^ k
      = ∑ j, c j * (x j / x (Fin.last n)) ^ k := by
    intro k
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [div_pow]
    field_simp
  simp only [hrewrite]
  have hlim : Filter.Tendsto (fun k : ℕ => ∑ j, c j * (x j / x (Fin.last n)) ^ k) Filter.atTop
      (nhds (∑ j, if j = Fin.last n then c j else 0)) := by
    refine tendsto_finsetSum _ fun j _ => ?_
    by_cases hj : j = Fin.last n
    · subst hj
      simp [div_self (ne_of_gt hL)]
    · rw [if_neg hj]
      have hratio : x j / x (Fin.last n) < 1 := by
        rw [div_lt_one hL]
        exact hmono j hj
      have hnn : 0 ≤ x j / x (Fin.last n) := le_of_lt (div_pos (hx0 j) hL)
      simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one hnn hratio).const_mul (c j)
  simpa using hlim

/-- A finite signed frequency sum eventually has the sign of its dominant amplitude. -/
theorem eventually_signedFrequencySum_pos {n : ℕ} (c x : Fin (n + 1) → ℝ)
    (hx0 : ∀ j, 0 < x j) (hmono : ∀ j : Fin (n + 1), j ≠ Fin.last n → x j < x (Fin.last n))
    (hc : 0 < c (Fin.last n)) :
    ∀ᶠ k : ℕ in Filter.atTop, 0 < ∑ j, c j * x j ^ k := by
  have hL : 0 < x (Fin.last n) := hx0 _
  have hlim := tendsto_signedFrequencySum_div c x hx0 hmono
  have hev : ∀ᶠ k : ℕ in Filter.atTop,
      0 < (∑ j, c j * x j ^ k) / x (Fin.last n) ^ k :=
    hlim.eventually (eventually_gt_nhds hc)
  filter_upwards [hev] with k hk
  have hpow : 0 < x (Fin.last n) ^ k := pow_pos hL k
  rcases div_pos_iff.mp hk with ⟨hnum, -⟩ | ⟨-, hden⟩
  · exact hnum
  · linarith

theorem eventually_signedFrequencySum_neg {n : ℕ} (c x : Fin (n + 1) → ℝ)
    (hx0 : ∀ j, 0 < x j) (hmono : ∀ j : Fin (n + 1), j ≠ Fin.last n → x j < x (Fin.last n))
    (hc : c (Fin.last n) < 0) :
    ∀ᶠ k : ℕ in Filter.atTop, (∑ j, c j * x j ^ k) < 0 := by
  have hneg := eventually_signedFrequencySum_pos (fun j => -c j) x hx0 hmono
    (by simpa using neg_pos.mpr hc)
  filter_upwards [hneg] with k hk
  have hsum : (∑ j, (-c j) * x j ^ k) = -(∑ j, c j * x j ^ k) := by
    simp [neg_mul]
  rw [hsum] at hk
  linarith

/-- **Finite signed frequency atoms are not Markov.**  A nonzero dominant amplitude forces
infinitely many strictly negative shifted seam moments. -/
theorem exists_seamMoment_neg_of_signedFrequency {n : ℕ} (c x : Fin (n + 1) → ℝ)
    (hx0 : ∀ j, 0 < x j) (hmono : ∀ j : Fin (n + 1), j ≠ Fin.last n → x j < x (Fin.last n))
    (hc : c (Fin.last n) ≠ 0) (N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ 1 ≤ k ∧
      seamMoment (fun j => (∑ i, c i * x i ^ j) / (Nat.factorial (2 * j))) k < 0 := by
  rcases lt_or_gt_of_ne hc with hneg | hpos
  · obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
      (eventually_signedFrequencySum_neg c x hx0 hmono hneg)
    refine ⟨2 * (max N K) + 1, by omega, by omega, ?_⟩
    exact seamMoment_neg_of_odd_of_neg (by omega) (hK _ (by omega)) ⟨max N K, by ring⟩
  · obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp
      (eventually_signedFrequencySum_pos c x hx0 hmono hpos)
    refine ⟨2 * (max N K + 1), by omega, by omega, ?_⟩
    exact seamMoment_neg_of_even (by omega) (hK _ (by omega)) ⟨max N K + 1, by ring⟩

/-! ### Bounded half-turn frequency packets -/

variable {ι : Type*} [Fintype ι]

/-- For frequencies confined to `[a, b]`, the third and first moments are dominated by the second.
This is the packet form of `(x - a)(x - b) ≤ 0`. -/
theorem boundedPacket_moment_inequality (c x : ι → ℝ) {a b : ℝ}
    (hc : ∀ i, 0 < c i) (hlow : ∀ i, a ≤ x i) (hhigh : ∀ i, x i ≤ b) (ha : 0 < a) :
    (∑ i, c i * x i ^ 3) + a * b * (∑ i, c i * x i) ≤ (a + b) * (∑ i, c i * x i ^ 2) := by
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  have hxpos : 0 < x i := lt_of_lt_of_le ha (hlow i)
  have hfac : (x i - a) * (x i - b) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by linarith [hlow i]) (by linarith [hhigh i])
  have hprod : c i * x i * ((x i - a) * (x i - b)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (le_of_lt (mul_pos (hc i) hxpos)) hfac
  nlinarith [hprod]

/-- **Bounded packets fail the first shifted Hankel gate.**  If the squared-frequency support of a
positive half-turn repaired packet lies in `[a, b]` with ratio below the sharp threshold, the first
shifted Hankel determinant is strictly negative. -/
theorem boundedPacket_halfTurn_det_neg [Nonempty ι] (c x : ι → ℝ) {a b : ℝ}
    (ha : 0 < a) (hab : a ≤ b) (hc : ∀ i, 0 < c i)
    (hlow : ∀ i, a ≤ x i) (hhigh : ∀ i, x i ≤ b)
    (hthreshold : b / a < halfTurnUpperThreshold) :
    (∑ i, c i * x i) * (∑ i, c i * x i ^ 3) / 120 - ((∑ i, c i * x i ^ 2) / 6) ^ 2 < 0 := by
  have hxpos : ∀ i, 0 < x i := fun i => lt_of_lt_of_le ha (hlow i)
  have hM1pos : 0 < ∑ i, c i * x i :=
    Finset.sum_pos (fun i _ => mul_pos (hc i) (hxpos i)) Finset.univ_nonempty
  have hM2pos : 0 < ∑ i, c i * x i ^ 2 :=
    Finset.sum_pos (fun i _ => mul_pos (hc i) (pow_pos (hxpos i) 2)) Finset.univ_nonempty
  have hM3pos : 0 < ∑ i, c i * x i ^ 3 :=
    Finset.sum_pos (fun i _ => mul_pos (hc i) (pow_pos (hxpos i) 3)) Finset.univ_nonempty
  have hkey := boundedPacket_moment_inequality c x hc hlow hhigh ha
  have habpos : 0 < a * b := mul_pos ha (lt_of_lt_of_le ha hab)
  have hAM : 4 * (a * b * (∑ i, c i * x i)) * (∑ i, c i * x i ^ 3) ≤
      ((∑ i, c i * x i ^ 3) + a * b * (∑ i, c i * x i)) ^ 2 := by
    nlinarith [sq_nonneg ((∑ i, c i * x i ^ 3) - a * b * (∑ i, c i * x i))]
  have hsq : ((∑ i, c i * x i ^ 3) + a * b * (∑ i, c i * x i)) ^ 2 ≤
      (a + b) ^ 2 * (∑ i, c i * x i ^ 2) ^ 2 := by
    have hnn : 0 ≤ (∑ i, c i * x i ^ 3) + a * b * (∑ i, c i * x i) := by
      have : 0 ≤ a * b * (∑ i, c i * x i) := le_of_lt (mul_pos habpos hM1pos)
      linarith
    nlinarith [hkey, hnn]
  have hr : 1 ≤ b / a := (le_div_iff₀ ha).mpr (by linarith)
  have hquadneg : 3 * (b / a) ^ 2 - 34 * (b / a) + 3 < 0 :=
    (halfTurn_ratio_quad_neg_iff hr).mpr hthreshold
  have hquad : 3 * (a + b) ^ 2 < 40 * (a * b) := by
    have ha2 : 0 < a ^ 2 := pow_pos ha 2
    have hexpand : 3 * (b / a) ^ 2 - 34 * (b / a) + 3 =
        (3 * b ^ 2 - 34 * a * b + 3 * a ^ 2) / a ^ 2 := by
      field_simp
    rw [hexpand] at hquadneg
    have hnum : 3 * b ^ 2 - 34 * a * b + 3 * a ^ 2 < 0 := by
      by_contra hcon
      push Not at hcon
      exact absurd hquadneg (not_lt.mpr (div_nonneg hcon (le_of_lt ha2)))
    nlinarith [hnum]
  have hfinal : 3 * ((∑ i, c i * x i) * (∑ i, c i * x i ^ 3)) < 10 * (∑ i, c i * x i ^ 2) ^ 2 := by
    have h1 : 12 * (a * b) * ((∑ i, c i * x i) * (∑ i, c i * x i ^ 3)) ≤
        3 * (a + b) ^ 2 * (∑ i, c i * x i ^ 2) ^ 2 := by nlinarith [hAM, hsq]
    have h2 : 3 * (a + b) ^ 2 * (∑ i, c i * x i ^ 2) ^ 2 <
        40 * (a * b) * (∑ i, c i * x i ^ 2) ^ 2 := by
      have hpos : 0 < (∑ i, c i * x i ^ 2) ^ 2 := pow_pos hM2pos 2
      nlinarith [hquad, hpos]
    nlinarith [h1, h2, habpos]
  exact halfTurn_det_neg_of_moment_ratio_lt hfinal

/-! ### Finite-order local coefficient operators -/

/-- A nonzero real polynomial has a constant strict sign along all large natural arguments. -/
theorem exists_eventual_sign (q : Polynomial ℝ) (hq : q ≠ 0) :
    (∃ K : ℕ, ∀ k : ℕ, K ≤ k → 0 < q.eval (k : ℝ)) ∨
      (∃ K : ℕ, ∀ k : ℕ, K ≤ k → q.eval (k : ℝ) < 0) := by
  have hnat : Filter.Tendsto (fun k : ℕ => (k : ℝ)) Filter.atTop Filter.atTop :=
    tendsto_natCast_atTop_atTop
  rcases lt_or_ge 0 q.degree with hdeg | hdeg
  · rcases le_or_gt 0 q.leadingCoeff with hlc | hlc
    · have hcomp := (Polynomial.tendsto_atTop_of_leadingCoeff_nonneg q hdeg hlc).comp hnat
      obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (hcomp.eventually_gt_atTop 0)
      exact Or.inl ⟨K, fun k hk => hK k hk⟩
    · have hcomp :=
        (Polynomial.tendsto_atBot_of_leadingCoeff_nonpos q hdeg (le_of_lt hlc)).comp hnat
      obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp (hcomp.eventually_lt_atBot 0)
      exact Or.inr ⟨K, fun k hk => hK k hk⟩
  · have heq : q = Polynomial.C (q.coeff 0) := Polynomial.eq_C_of_degree_le_zero hdeg
    have hcc : q.coeff 0 ≠ 0 := by
      intro h
      apply hq
      rw [heq, h, map_zero]
    rcases lt_or_gt_of_ne hcc with h | h
    · refine Or.inr ⟨0, fun k _ => ?_⟩
      rw [heq]
      simpa using h
    · refine Or.inl ⟨0, fun k _ => ?_⟩
      rw [heq]
      simpa using h

/-- **Finite-order local operators cannot repair the frequency cone.**  Multiplying the `z ^ k`
coefficient of a positive germ by a nonzero real polynomial in `k` still leaves infinitely many
strictly negative shifted seam moments. -/
theorem exists_seamMoment_neg_of_polynomialMultiplier (M : ℕ → ℝ)
    (hM : ∀ k : ℕ, 1 ≤ k → 0 < M k) (q : Polynomial ℝ) (hq : q ≠ 0) (N : ℕ) :
    ∃ k : ℕ, N ≤ k ∧ 1 ≤ k ∧
      seamMoment (fun j => q.eval (j : ℝ) * M j / (Nat.factorial (2 * j))) k < 0 := by
  rcases exists_eventual_sign q hq with ⟨K, hK⟩ | ⟨K, hK⟩
  · refine ⟨2 * (max N K + 1), by omega, by omega, ?_⟩
    refine seamMoment_neg_of_even (by omega) ?_ ⟨max N K + 1, by ring⟩
    exact mul_pos (hK _ (by omega)) (hM _ (by omega))
  · refine ⟨2 * (max N K) + 1, by omega, by omega, ?_⟩
    refine seamMoment_neg_of_odd_of_neg (by omega) ?_ ⟨max N K, by ring⟩
    exact mul_neg_of_neg_of_pos (hK _ (by omega)) (hM _ (by omega))

end GaloisForLFunctions
