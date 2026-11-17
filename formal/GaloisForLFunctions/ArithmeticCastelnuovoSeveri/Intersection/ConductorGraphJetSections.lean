import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.Intersection.ConductorGraphContacts
import Mathlib.Analysis.Complex.Norm

/-!
# Integral sections prescribing jets on conductor graphs

Split the binomial expansion of a difference of graph ordinates in two.
Each half vanishes to the prescribed order on one graph. Multiplying the
resulting selectors lifts all jet data over ℤ[T] with one common multiplier.
-/

noncomputable section
open Finset Polynomial
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

section Selection
variable {R : Type*} [CommRing R]

/-- Upper half of the binomial expansion. It is divisible by the first
argument to order h, and its complement by the second to order h. -/
def upperJetPower (h : ℕ) (x y : R) : R :=
  ∑ k ∈ range (2*h+1), if h ≤ k then x^k * y^(2*h-k) * ((2*h).choose k : R) else 0

private theorem upperJetPower_left (h : ℕ) (x y : R) : x^h ∣ upperJetPower h x y := by
  apply dvd_sum
  intro k _
  split_ifs with hk
  · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left (pow_dvd_pow x hk) _) _
  · exact dvd_zero _

private theorem upperJetPower_right (h : ℕ) (x y : R) :
    y^h ∣ (x+y)^(2*h) - upperJetPower h x y := by
  rw [add_pow, upperJetPower, ← sum_sub_distrib]
  apply dvd_sum
  intro k _
  split_ifs with hk
  · simp
  · rw [sub_zero]
    exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_right (pow_dvd_pow y (by omega)) _) _

private def rowFactor (g : ℕ → R) (h i j : ℕ) : R :=
  if i = j then 1 else (g i - g j)^(2*h)

private def jetRow (S : Finset ℕ) (g : ℕ → R) (h i : ℕ) : R :=
  ∏ j ∈ S, rowFactor g h i j

/-- One multiplier in the horizontal coordinate clears all jet data. -/
def graphJetMultiplier (S : Finset ℕ) (g : ℕ → R) (h : ℕ) : R :=
  ∏ i ∈ S, jetRow S g h i

private def selectorFactor (g : ℕ → R) (h i j : ℕ) : R[X] :=
  if i = j then 1 else upperJetPower h (X - C (g j)) (C (g i) - X)

private def jetSelector (S : Finset ℕ) (g : ℕ → R) (h i : ℕ) : R[X] :=
  ∏ j ∈ S, selectorFactor g h i j

/-- Polynomial section lifting branch data after multiplication by the
common horizontal multiplier. All coefficients stay in the original ring. -/
def graphJetSection (S : Finset ℕ) (g : ℕ → R) (h : ℕ) (data : ℕ → R[X]) : R[X] :=
  ∑ i ∈ S, data i * jetSelector S g h i * C (∏ k ∈ S.erase i, jetRow S g h k)

private theorem selectorFactor_same (g : ℕ → R) (h i j : ℕ)
    (I : Ideal R[X]) (hz : (X - C (g i))^h ∈ I) :
    Ideal.Quotient.mk I (selectorFactor g h i j) = Ideal.Quotient.mk I (C (rowFactor g h i j)) := by
  by_cases he : i = j
  · simp [selectorFactor, rowFactor, he]
  simp only [selectorFactor, rowFactor, if_neg he]
  rw [← sub_eq_zero, ← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hn : (C (g i) - X)^h ∈ I := by
    rw [← neg_sub, neg_eq_neg_one_mul, mul_pow]
    exact I.mul_mem_left _ hz
  have hd := upperJetPower_right h (X - C (g j)) (C (g i) - X)
  have hs : X - C (g j) + (C (g i) - X) = C (g i - g j) := by rw [map_sub]; ring
  rw [hs, ← map_pow] at hd
  rw [← neg_sub]
  exact I.neg_mem (I.mem_of_dvd hd hn)

private theorem jetSelector_at (S : Finset ℕ) (g : ℕ → R) (h i j : ℕ) (hj : j ∈ S)
    (I : Ideal R[X]) (hz : (X - C (g j))^h ∈ I) :
    Ideal.Quotient.mk I (jetSelector S g h i) =
      if i = j then Ideal.Quotient.mk I (C (jetRow S g h i)) else 0 := by
  by_cases he : i = j
  · subst j
    simp only [jetSelector, jetRow, map_prod]
    exact prod_congr rfl fun k _ => selectorFactor_same g h i k I hz
  rw [if_neg he]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hd : (X - C (g j))^h ∣ selectorFactor g h i j := by
    rw [selectorFactor, if_neg he]
    exact upperJetPower_left _ _ _
  exact I.mem_of_dvd (hd.trans (dvd_prod_of_mem _ hj)) hz

/-- Simultaneous integral Hermite interpolation, including arbitrarily many
mixed collisions and arbitrary (possibly signed) polynomial jet data. -/
theorem graphJetSection_restrict (S : Finset ℕ) (g : ℕ → R) (h : ℕ) (data : ℕ → R[X])
    {j : ℕ} (hj : j ∈ S) :
    (X - C (g j))^h ∣ graphJetSection S g h data - C (graphJetMultiplier S g h) * data j := by
  let I := Ideal.span ({(X - C (g j))^h} : Set R[X])
  have hz : (X - C (g j))^h ∈ I := Ideal.subset_span (Set.mem_singleton _)
  apply Ideal.mem_span_singleton.mp
  change _ ∈ I
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  rw [map_sub, sub_eq_zero, graphJetSection, map_sum, sum_eq_single j]
  · simp only [map_mul, jetSelector_at S g h j j hj I hz, if_true, graphJetMultiplier,
      ← prod_erase_mul S _ hj, map_mul]
    ring
  · intro i _ hne
    simp only [map_mul, jetSelector_at S g h i j hj I hz, if_neg hne, mul_zero, zero_mul]
  · exact fun h => False.elim (h hj)

end Selection

/-- The conductor multiplier is a nonzero integral polynomial for every finite
set of positive conductors, including at arbitrary thickness. -/
theorem conductorJetMultiplier_ne_zero (S : Finset ℕ) (h : ℕ) (hS : 0 ∉ S) :
    graphJetMultiplier S conductorGraph h ≠ 0 := by
  apply prod_ne_zero_iff.mpr
  intro i hi
  apply prod_ne_zero_iff.mpr
  intro j hj
  by_cases he : i = j
  · simp [rowFactor, he]
  · rw [rowFactor, if_neg he]
    exact pow_ne_zero _ (sub_ne_zero.mpr (conductorContact_graph_ne
      (fun e => hS (e ▸ hi)) (fun e => hS (e ▸ hj)) he))

private theorem contact_le_larger {i j : ℕ} (hi : 0 < i) (hij : i < j) :
    conductorContact i j ≤ j := by
  have hj := hi.trans hij
  have hsmall : (conductorGraph i).coeff j = 0 :=
    coeff_eq_zero_of_natDegree_lt ((conductorGraph_natDegree hi.ne').trans_lt hij)
  let r := ∏ p ∈ j.primeFactors, p
  have htop : (conductorGraph j).coeff j = (r:ℤ) := by
    simp [r, conductorGraph, coeff_monomial, Nat.mem_divisors, hj.ne']
  have hdiv := Int.natAbs_dvd_natAbs.mpr (content_dvd_coeff (p := conductorGraph i - conductorGraph j) j)
  rw [coeff_sub, hsmall, htop, zero_sub, Int.natAbs_neg, Int.natAbs_natCast] at hdiv
  have hr : 0 < r := prod_pos fun p hp => (Nat.prime_of_mem_primeFactors hp).pos
  exact (Nat.le_of_dvd hr hdiv).trans (Nat.le_of_dvd hj (Nat.prod_primeFactors_dvd j))

/-- The same clearing polynomial controls all residue characteristics. Its
integer content is bounded using the top coefficient of each graph difference. -/
theorem conductorJetMultiplier_content_le (S : Finset ℕ) (h s : ℕ) (hs : 1 ≤ s)
    (hS : ∀ i ∈ S, 0 < i ∧ i ≤ s) :
    verticalContent (graphJetMultiplier S conductorGraph h) ≤ s^(2*h*S.card*S.card) := by
  have hc (i j) (hi : i ∈ S) (hj : j ∈ S) (he : i ≠ j) : conductorContact i j ≤ s := by
    rcases lt_or_gt_of_ne he with hlt | hgt
    · exact (contact_le_larger (hS _ hi).1 hlt).trans (hS _ hj).2
    · rw [conductorContact_comm]
      exact (contact_le_larger (hS _ hj).1 hgt).trans (hS _ hi).2
  have hr (i) (hi : i ∈ S) : verticalContent (jetRow S conductorGraph h i) ≤ (s^(2*h))^S.card := by
    rw [jetRow, map_prod, ← prod_const]
    apply prod_le_prod (fun _ _ => Nat.zero_le _)
    intro j hj
    by_cases he : i = j
    · simp only [rowFactor, if_pos he, map_one]
      exact one_le_pow₀ hs
    · simp only [rowFactor, if_neg he, map_pow]
      exact Nat.pow_le_pow_left (hc i j hi hj he) _
  rw [graphJetMultiplier, map_prod, pow_mul, pow_mul, ← prod_const]
  exact prod_le_prod (fun _ _ => Nat.zero_le _) hr

private theorem norm_upperJetPower {A : Type*} [CommRing A] (e : A →+* ℂ) (h : ℕ) (x y : A) :
    ‖e (upperJetPower h x y)‖ ≤ (‖e x‖ + ‖e y‖)^(2*h) := by
  rw [upperJetPower, map_sum, add_pow]
  refine (norm_sum_le _ _).trans (sum_le_sum fun k _ => ?_)
  split_ifs
  · simp only [map_mul, map_pow, map_natCast, norm_mul, norm_pow, Complex.norm_natCast, le_refl]
  · simp only [map_zero, norm_zero]
    positivity

private theorem complex_prod_bound {ι : Type*} (S : Finset ι) (f : ι → ℂ) (K : ℝ)
    (hf : ∀ i ∈ S, ‖f i‖ ≤ K) : ‖∏ i ∈ S, f i‖ ≤ K^S.card := by
  rw [norm_prod]
  simpa using prod_le_prod (fun i _ => norm_nonneg (f i)) hf

/-- Uniform cost on a bidisk, including the multiplier and the interpolating
section. The estimate holds for every evaluation of the coefficient ring. -/
theorem graphJetSection_norm {R : Type*} [CommRing R] (S : Finset ℕ) (g : ℕ → R) (h : ℕ)
    (data : ℕ → R[X]) (e : R[X] →+* ℂ) {L M : ℝ} (hL : 0 ≤ L) (hM : 0 ≤ M)
    (hX : ‖e X‖ ≤ 1) (hg : ∀ i ∈ S, ‖e (C (g i))‖ ≤ L)
    (hd : ∀ i ∈ S, ‖e (data i)‖ ≤ M) :
    let D := (2*(1+L))^(2*h*S.card*(S.card+1))
    ‖e (C (graphJetMultiplier S g h))‖ ≤ D ∧ ‖e (graphJetSection S g h data)‖ ≤ S.card*M*D := by
  let K := (2*(1+L))^(2*h)
  let V := K^S.card
  have hB : 1 ≤ 2*(1+L) := by linarith
  have hK : 1 ≤ K := one_le_pow₀ hB
  have hV : 1 ≤ V := one_le_pow₀ hK
  have hv (i) (hi : i ∈ S) : ‖e (C (jetRow S g h i))‖ ≤ V := by
    simp only [jetRow, map_prod]
    apply complex_prod_bound
    intro j hj
    by_cases he : i = j
    · simpa only [rowFactor, if_pos he, map_one, norm_one] using hK
    · simp only [rowFactor, if_neg he, map_pow, map_sub, norm_pow]
      apply pow_le_pow_left₀ (norm_nonneg _)
      exact (norm_sub_le _ _).trans (by linarith only [hg i hi, hg j hj])
  have hw (i) (hi : i ∈ S) : ‖e (jetSelector S g h i)‖ ≤ V := by
    rw [jetSelector, map_prod]
    apply complex_prod_bound
    intro j hj
    by_cases he : i = j
    · simpa only [selectorFactor, if_pos he, map_one, norm_one] using hK
    · rw [selectorFactor, if_neg he]
      apply (norm_upperJetPower e _ _ _).trans
      apply pow_le_pow_left₀ (by positivity)
      simp only [map_sub]
      linarith only [norm_sub_le (e X) (e (C (g j))), norm_sub_le (e (C (g i))) (e X),
        hg i hi, hg j hj, hX]
  have hdv : (2*(1+L))^(2*h*S.card*(S.card+1)) = V^(S.card+1) := by
    simp only [V, K, pow_mul]
  dsimp only
  rw [hdv]
  constructor
  · simp only [graphJetMultiplier, map_prod]
    exact (complex_prod_bound _ _ _ hv).trans (pow_le_pow_right₀ hV (Nat.le_succ _))
  · rw [graphJetSection, map_sum]
    apply (norm_sum_le _ _).trans
    have ht (i) (hi : i ∈ S) : ‖e (data i * jetSelector S g h i * C (∏ k ∈ S.erase i, jetRow S g h k))‖ ≤
        M * V^(S.card+1) := by
      simp only [map_mul, norm_mul, map_prod]
      have hp := complex_prod_bound (S.erase i) (fun k => e (C (jetRow S g h k))) V
        fun k hk => hv _ (mem_of_mem_erase hk)
      have hp' := hp.trans (pow_le_pow_right₀ hV (card_le_card (erase_subset i S)))
      calc _ ≤ M * V * V^S.card := mul_le_mul
              (mul_le_mul (hd i hi) (hw i hi) (norm_nonneg _) hM) hp' (norm_nonneg _) (by positivity)
           _ = _ := by rw [pow_succ]; ring
    simpa only [sum_const, nsmul_eq_mul, mul_assoc] using sum_le_sum ht

#print axioms graphJetSection_restrict
#print axioms conductorJetMultiplier_ne_zero
#print axioms conductorJetMultiplier_content_le
#print axioms graphJetSection_norm

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
