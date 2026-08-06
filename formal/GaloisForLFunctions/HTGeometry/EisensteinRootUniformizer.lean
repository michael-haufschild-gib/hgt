import GaloisForLFunctions.HTGeometry.TameMonogenicDifferentExponent

/-!
# A root of an Eisenstein polynomial is a uniformizer

In an extension of discrete valuation rings whose ramification index equals the degree of an
Eisenstein polynomial, every root of that polynomial is a uniformizer.  The constant coefficient
has valuation exactly the index upstairs, while every other term of the expansion carries at least
that much and, once the root has positive valuation, strictly more.  The ultrametric strict minimum
then forces the root to have valuation one.

This is what makes an Eisenstein presentation coherent: the element it presents is automatically a
uniformizer, so the different computation may be applied to it without a separate hypothesis.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial IsDiscreteValuationRing

variable {A B : Type*}
variable [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
variable [CommRing B] [IsDomain B] [IsDiscreteValuationRing B]

theorem addVal_pow (x : B) (n : ℕ) : addVal B (x ^ n) = n • addVal B x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, AddValuation.map_mul, ih, succ_nsmul]

omit [IsDomain B] [IsDiscreteValuationRing B] in
theorem eval_eisensteinPoly (e : ℕ) (c : ℕ → B) (x : B) :
    eval x (eisensteinPoly e c) = x ^ e + ∑ i ∈ Finset.range e, c i * x ^ i := by
  rw [eisensteinPoly, eval_add, eval_pow, eval_X, eval_finsetSum]
  simp

omit [IsDomain A] [IsDiscreteValuationRing A] in
/-- The expansion of a monic polynomial pushed forward, evaluated at a point. -/
theorem eval_map_monic (ψ : A →+* B) {g : A[X]} (hmonic : g.Monic) (x : B) :
    eval x (g.map ψ) = x ^ g.natDegree + ∑ i ∈ Finset.range g.natDegree, ψ (g.coeff i) * x ^ i := by
  have hmonic' : (g.map ψ).Monic := hmonic.map ψ
  have hdeg' : (g.map ψ).natDegree = g.natDegree := hmonic.natDegree_map ψ
  conv_lhs => rw [eq_eisensteinPoly_of_monic hmonic']
  rw [eval_eisensteinPoly, hdeg']
  simp [Polynomial.coeff_map]

/-- **A root of an Eisenstein polynomial is a uniformizer.** -/
theorem addVal_eq_one_of_eisenstein_root (ψ : A →+* B) {πA : A} (hπA : Irreducible πA)
    (e : ℕ) (he : 0 < e) (hram : addVal B (ψ πA) = (e : ℕ∞))
    {g : A[X]} (hmonic : g.Monic) (hdeg : g.natDegree = e)
    (hcoef : ∀ i < e, g.coeff i ≠ 0 → addVal A (g.coeff i) ≠ 0)
    (hc0 : addVal A (g.coeff 0) = 1)
    {x : B} (hroot : eval x (g.map ψ) = 0) :
    addVal B x = 1 := by
  -- the constant coefficient has valuation exactly `e` upstairs
  have hc0ne : g.coeff 0 ≠ 0 := by
    intro h
    rw [h, AddValuation.map_zero] at hc0
    simp at hc0
  have hval0 : addVal B (ψ (g.coeff 0)) = (e : ℕ∞) := by
    rw [addVal_map_eq_mul_ramification ψ hπA e hram _ hc0ne, hc0, mul_one]
  -- every coefficient has valuation at least `e` upstairs
  have hvali : ∀ i < e, (e : ℕ∞) ≤ addVal B (ψ (g.coeff i)) := by
    intro i hi
    by_cases hzero : g.coeff i = 0
    · rw [hzero, map_zero, AddValuation.map_zero]
      exact le_top
    · exact le_addVal_map_of_addVal_ne_zero ψ hπA e hram hzero (hcoef i hi hzero)
  -- the expansion
  have hexp : x ^ e + ∑ i ∈ Finset.range e, ψ (g.coeff i) * x ^ i = 0 := by
    rw [← hdeg]
    rw [← eval_map_monic ψ hmonic x]
    exact hroot
  have hsum : addVal B (x ^ e) = addVal B (∑ i ∈ Finset.range e, ψ (g.coeff i) * x ^ i) := by
    have hneg : x ^ e = -∑ i ∈ Finset.range e, ψ (g.coeff i) * x ^ i := by
      linear_combination (norm := ring_nf) hexp
    rw [hneg, AddValuation.map_neg]
  -- `x` is nonzero
  have hx0 : x ≠ 0 := by
    intro h
    subst h
    have hzero : ∑ i ∈ Finset.range e, ψ (g.coeff i) * (0 : B) ^ i = ψ (g.coeff 0) := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro j _ hj
        rw [zero_pow hj, mul_zero]
      · intro h
        exact absurd (Finset.mem_range.mpr he) h
    rw [zero_pow (by omega : e ≠ 0), hzero, zero_add] at hexp
    rw [hexp, AddValuation.map_zero] at hval0
    exact (ENat.top_ne_coe _) hval0
  -- the valuation of `x` is finite
  have hvtop : addVal B x ≠ ⊤ := by
    rw [Ne, addVal_eq_top_iff]
    exact hx0
  obtain ⟨n, hn⟩ : ∃ n : ℕ, addVal B x = (n : ℕ∞) := ⟨_, (ENat.coe_toNat hvtop).symm⟩
  -- the valuation of `x` is positive
  have hnpos : 0 < n := by
    by_contra hcon
    have hn0 : n = 0 := by omega
    have hlhs : addVal B (x ^ e) = 0 := by
      rw [addVal_pow, hn, hn0]
      simp
    have hrhs : (e : ℕ∞) ≤ addVal B (∑ i ∈ Finset.range e, ψ (g.coeff i) * x ^ i) := by
      refine le_addVal_sum _ _ _ fun i hi => ?_
      rw [AddValuation.map_mul, addVal_pow, hn, hn0]
      simpa using hvali i (Finset.mem_range.mp hi)
    rw [← hsum, hlhs] at hrhs
    have hz : (e : ℕ∞) = 0 := le_antisymm hrhs (by simp)
    have hz' : e = 0 := by exact_mod_cast hz
    omega
  -- separate the constant term from the rest
  have hsplit : ∑ i ∈ Finset.range e, ψ (g.coeff i) * x ^ i =
      (∑ i ∈ Finset.range (e - 1), ψ (g.coeff (i + 1)) * x ^ (i + 1)) + ψ (g.coeff 0) := by
    have he' : e = (e - 1) + 1 := (Nat.succ_pred_eq_of_pos he).symm
    rw [he', Finset.sum_range_succ']
    simp
  have htail : (e : ℕ∞) + 1 ≤
      addVal B (∑ i ∈ Finset.range (e - 1), ψ (g.coeff (i + 1)) * x ^ (i + 1)) := by
    refine le_addVal_sum _ _ _ fun i hi => ?_
    rw [AddValuation.map_mul, addVal_pow, hn]
    have hle : (1 : ℕ∞) ≤ ((i + 1) • (n : ℕ∞)) := by
      have : ((1 : ℕ) : ℕ∞) ≤ (((i + 1) * n : ℕ) : ℕ∞) := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by positivity)
      simpa [nsmul_eq_mul] using this
    have hi2 : i < e - 1 := Finset.mem_range.mp hi
    have hi' : i + 1 < e := by omega
    exact add_le_add (hvali (i + 1) hi') hle
  have hlt1 : (e : ℕ∞) < (e : ℕ∞) + 1 := by
    have hcast : ((e : ℕ) : ℕ∞) < ((e + 1 : ℕ) : ℕ∞) := by exact_mod_cast Nat.lt_succ_self e
    simpa using hcast
  have hne : addVal B (∑ i ∈ Finset.range (e - 1), ψ (g.coeff (i + 1)) * x ^ (i + 1)) ≠
      addVal B (ψ (g.coeff 0)) := by
    rw [hval0]
    exact ne_of_gt (lt_of_lt_of_le hlt1 htail)
  have hexact : addVal B (∑ i ∈ Finset.range e, ψ (g.coeff i) * x ^ i) = (e : ℕ∞) := by
    rw [hsplit, AddValuation.map_add_of_distinct_val _ hne, hval0]
    exact min_eq_right (le_trans (le_of_lt hlt1) htail)
  rw [hexact, addVal_pow, hn] at hsum
  have hnat : e * n = e := by
    have : ((e * n : ℕ) : ℕ∞) = ((e : ℕ) : ℕ∞) := by
      simpa [nsmul_eq_mul] using hsum
    exact_mod_cast this
  have hn1 : n = 1 := by
    have he' : e ≠ 0 := by omega
    have h2 : e * n = e * 1 := by rw [mul_one]; exact hnat
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero he') h2
  rw [hn, hn1]
  rfl
/-- An element of valuation one in a discrete valuation ring is a uniformizer. -/
theorem irreducible_of_addVal_eq_one {x : B} (h : addVal B x = 1) : Irreducible x := by
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible B
  have hx0 : x ≠ 0 := by
    intro h0
    rw [h0, AddValuation.map_zero] at h
    simp at h
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx0 hπ
  have hval : addVal B ((u : B) * π ^ n) = (n : ℕ∞) := by
    rw [AddValuation.map_mul, addVal_of_isUnit u.isUnit, zero_add, addVal_pow_uniformizer hπ]
  rw [hval] at h
  have hn : n = 1 := by exact_mod_cast h
  subst hn
  rw [pow_one]
  exact (associated_unit_mul_left π (u : B) u.isUnit).symm.irreducible hπ

/-- **The tame different exponent from an Eisenstein presentation alone.**  Neither irreducibility
of the presented element nor a bound on the coefficients upstairs need be assumed: the presentation
supplies both. -/
theorem addVal_eval_derivative_of_eisenstein_root (ψ : A →+* B) {πA : A} (hπA : Irreducible πA)
    (e : ℕ) (he : 0 < e) (hram : addVal B (ψ πA) = (e : ℕ∞))
    {g : A[X]} (hmonic : g.Monic) (hdeg : g.natDegree = e)
    (hcoef : ∀ i < e, g.coeff i ≠ 0 → addVal A (g.coeff i) ≠ 0)
    (hc0 : addVal A (g.coeff 0) = 1)
    (htame : addVal B ((e : ℕ) : B) = 0)
    {x : B} (hroot : eval x (g.map ψ) = 0) :
    addVal B (eval x (derivative (g.map ψ))) = ((e - 1 : ℕ) : ℕ∞) :=
  addVal_eval_derivative_map_eisenstein ψ hπA e he hram hmonic hdeg hcoef x
    (irreducible_of_addVal_eq_one
      (addVal_eq_one_of_eisenstein_root ψ hπA e he hram hmonic hdeg hcoef hc0 hroot))
    htame

end GaloisForLFunctions.HTGeometry
