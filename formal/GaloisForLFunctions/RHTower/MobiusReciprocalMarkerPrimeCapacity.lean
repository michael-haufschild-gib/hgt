import GaloisForLFunctions.RHTower.ColumnRigidity
import GaloisForLFunctions.RHTower.MobiusBoundaryOppositeSignTransport
import Mathlib.Data.Nat.Dist

/-!
# Reciprocal marker-prime capacity for the Möbius boundary

This module formalizes the finite arithmetic skeleton of the reciprocal-marker source theorem.
A cofactor immediately above `X / p` produces a physical product immediately above `X`; a
negative Möbius cofactor times a larger prime has positive Möbius sign; and the larger prime
uniquely decodes the product.  It also proves the quantitative prime-corner obstruction used to
show that extra multiplicative-cube axes cannot reduce the prime-anchor Hall gate.

No distribution theorem is assumed here.  The paper theorem supplies many suitable cofactors by
Menon's unconditional almost-all short-interval theorem and many marker primes by the ordinary
prime number theorem.
-/

noncomputable section

namespace RHTower

open scoped BigOperators

/-! ## Prime corners of arbitrary finite breadth -/

/-- A finite product equal to a prime has one prime coordinate and only unit coordinates
elsewhere.  This is the arbitrary-breadth version of `prime_frequency_wall_rigidity`. -/
theorem prime_prod_coordinates_eq_one_except
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p : ℕ} (hp : p.Prime) {a : ι → ℕ}
    (ha : ∏ i, a i = p) :
    ∃ j : ι, a j = p ∧ ∀ i, i ≠ j → a i = 1 := by
  have hpdvd : p ∣ ∏ i, a i := by rw [ha]
  obtain ⟨j, _, hpj⟩ := (hp.prime.dvd_finsetProd_iff a).mp hpdvd
  have hajdvd : a j ∣ p := by
    rw [← ha]
    exact Finset.dvd_prod_of_mem a (Finset.mem_univ j)
  have haj : a j = p := Nat.dvd_antisymm hajdvd hpj
  refine ⟨j, haj, ?_⟩
  intro i hij
  have hcofactor : ∏ k ∈ Finset.univ.erase j, a k = 1 := by
    have hsplit := Finset.mul_prod_erase Finset.univ a (Finset.mem_univ j)
    rw [ha, haj] at hsplit
    exact Nat.eq_of_mul_eq_mul_left hp.pos (hsplit.trans (mul_one p).symm)
  have hi : i ∈ Finset.univ.erase j :=
    Finset.mem_erase.mpr ⟨hij, Finset.mem_univ i⟩
  exact Nat.dvd_one.mp
    (hcofactor ▸ Finset.dvd_prod_of_mem (fun k => a k) hi)

/-- If an auxiliary factor is at least two while its product stays in a forward `H`-window,
then the main factor must move a linear distance. -/
theorem nearby_product_with_auxiliary_factor_forces_linear_axis_gap
    {p H q t : ℕ}
    (hH : 3 * H ≤ p) (ht : 2 ≤ t) (hnear : q * t ≤ p + H) :
    q ≤ p ∧ p ≤ 3 * (p - q) := by
  have h2q : 2 * q ≤ p + H := by
    calc
      2 * q = q * 2 := by omega
      _ ≤ q * t := Nat.mul_le_mul_left q ht
      _ ≤ p + H := hnear
  have hqp : q ≤ p := by omega
  exact ⟨hqp, by omega⟩

/-- At a prime corner of breadth at least two, changing every positive coordinate and landing
inside a forward `H ≤ p/3` window forces linear displacement on the unique prime axis. -/
theorem primeAnchor_multiaxis_nearby_forces_linear_mainGap
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p H : ℕ} (hp : p.Prime) {a b : ι → ℕ}
    (hcard : 2 ≤ Fintype.card ι)
    (ha : ∏ i, a i = p)
    (hbpos : ∀ i, 1 ≤ b i)
    (hchange : ∀ i, b i ≠ a i)
    (hH : 3 * H ≤ p)
    (hnear : ∏ i, b i ≤ p + H) :
    ∃ j : ι,
      a j = p ∧
      (∀ i, i ≠ j → a i = 1) ∧
      b j ≤ p ∧
      p ≤ 3 * (p - b j) := by
  obtain ⟨j, haj, haunit⟩ := prime_prod_coordinates_eq_one_except hp ha
  haveI : Nontrivial ι :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega : 1 < Fintype.card ι)
  obtain ⟨k, hkj⟩ := exists_ne j
  have hak : a k = 1 := haunit k hkj
  have hbk : 2 ≤ b k := by
    have := hbpos k
    have := hchange k
    omega
  let t := ∏ i ∈ Finset.univ.erase j, b i
  have hkmem : k ∈ Finset.univ.erase j :=
    Finset.mem_erase.mpr ⟨hkj, Finset.mem_univ k⟩
  have htpos : 0 < t :=
    Finset.prod_pos fun i _ => Nat.zero_lt_of_lt (hbpos i)
  have hbk_dvd : b k ∣ t := Finset.dvd_prod_of_mem b hkmem
  have ht : 2 ≤ t := le_trans hbk (Nat.le_of_dvd htpos hbk_dvd)
  have hsplit := Finset.mul_prod_erase Finset.univ b (Finset.mem_univ j)
  have hqt : b j * t ≤ p + H := by
    simpa [t] using hsplit.trans_le hnear
  obtain ⟨hbjp, hgap⟩ :=
    nearby_product_with_auxiliary_factor_forces_linear_axis_gap hH ht hqt
  exact ⟨j, haj, haunit, hbjp, hgap⟩

/-- Quantitative all-breadth prime-corner collapse: every genuine multi-axis nearby cube has
mixed integer displacement at least `p/3`. -/
theorem primeAnchor_multiaxis_nearby_mixedDisplacement_linear
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {p H : ℕ} (hp : p.Prime) {a b : ι → ℕ}
    (hcard : 2 ≤ Fintype.card ι)
    (ha : ∏ i, a i = p)
    (hbpos : ∀ i, 1 ≤ b i)
    (hchange : ∀ i, b i ≠ a i)
    (hH : 3 * H ≤ p)
    (hnear : ∏ i, b i ≤ p + H) :
    p ≤ 3 * ∏ i, Nat.dist (b i) (a i) := by
  obtain ⟨j, haj, _haunit, hbjp, hgap⟩ :=
    primeAnchor_multiaxis_nearby_forces_linear_mainGap
      hp hcard ha hbpos hchange hH hnear
  have hprodpos : 0 < ∏ i, Nat.dist (b i) (a i) :=
    Finset.prod_pos fun i _ => Nat.dist_pos_of_ne (hchange i)
  have hdvd : Nat.dist (b j) (a j) ∣ ∏ i, Nat.dist (b i) (a i) :=
    Finset.dvd_prod_of_mem (fun i => Nat.dist (b i) (a i))
      (Finset.mem_univ j)
  have haxis :
      Nat.dist (b j) (a j) ≤ ∏ i, Nat.dist (b i) (a i) :=
    Nat.le_of_dvd hprodpos hdvd
  have hdist : Nat.dist (b j) (a j) = p - b j := by
    rw [haj, Nat.dist_eq_sub_of_le hbjp]
  calc
    p ≤ 3 * (p - b j) := hgap
    _ = 3 * Nat.dist (b j) (a j) := by rw [hdist]
    _ ≤ 3 * ∏ i, Nat.dist (b i) (a i) := Nat.mul_le_mul_left 3 haxis

/-! ## Reciprocal marker targets -/

/-- A cofactor in `(X/p, X/p+L]` produces a product in `(X,X+H]` whenever `pL ≤ H`. -/
theorem reciprocalMarker_product_mem_window
    {X H p a L : ℕ} (hp : 0 < p)
    (haLower : X / p < a) (haUpper : a ≤ X / p + L)
    (hcost : p * L ≤ H) :
    X < a * p ∧ a * p ≤ X + H := by
  constructor
  · exact Nat.lt_mul_of_div_lt haLower hp
  · calc
      a * p ≤ (X / p + L) * p := Nat.mul_le_mul_right p haUpper
      _ = (X / p) * p + p * L := by ring
      _ ≤ X + H := Nat.add_le_add (Nat.div_mul_le_self X p) hcost

/-- A positive integer below a prime is coprime to that prime. -/
theorem coprime_of_pos_lt_prime
    {a p : ℕ} (hp : p.Prime) (ha0 : 0 < a) (hap : a < p) :
    a.Coprime p := by
  exact Nat.Coprime.symm (hp.coprime_iff_not_dvd.mpr fun hdvd =>
    Nat.not_lt_of_ge (Nat.le_of_dvd ha0 hdvd) hap)

/-- A negative Möbius cofactor times a larger prime has positive Möbius coefficient. -/
theorem reciprocalMarker_negative_target_positive
    {a p : ℕ} (hp : p.Prime) (ha0 : 0 < a) (hap : a < p)
    (ha : mobiusComplexCoefficient a = -1) :
    mobiusComplexCoefficient (a * p) = 1 := by
  rw [mobiusComplexCoefficient_mul_of_coprime
      (coprime_of_pos_lt_prime hp ha0 hap),
    mobiusComplexCoefficient_prime hp, ha]
  ring

/-- Multiplication by a larger prime reverses either nonzero Möbius sign.  The analytic
reciprocal-marker theorem uses this symmetric form to construct both target reservoirs. -/
theorem reciprocalMarker_target_sign_flip
    {a p : ℕ} (hp : p.Prime) (ha0 : 0 < a) (hap : a < p) :
    mobiusComplexCoefficient (a * p) = -mobiusComplexCoefficient a := by
  rw [mobiusComplexCoefficient_mul_of_coprime
      (coprime_of_pos_lt_prime hp ha0 hap),
    mobiusComplexCoefficient_prime hp]
  ring

/-- Larger-prime marker decoding is collision-free.  If each cofactor is smaller than the other
representation's marker, equal physical products have equal markers and equal cofactors. -/
theorem largePrimeMarker_product_injective
    {a a' p p' : ℕ} (hp : p.Prime) (hp' : p'.Prime)
    (ha'pos : 0 < a')
    (ha'p : a' < p) (hap' : a < p')
    (hprod : a * p = a' * p') :
    a = a' ∧ p = p' := by
  have hpdiv : p ∣ a' * p' := by
    rw [← hprod]
    exact ⟨a, by simp [mul_comm]⟩
  rcases hp.dvd_mul.mp hpdiv with hpa' | hpp'
  · exact False.elim
      (Nat.not_lt_of_ge (Nat.le_of_dvd ha'pos hpa') ha'p)
  · have hppEq : p = p' := by
      rcases hp'.eq_one_or_self_of_dvd p hpp' with hp1 | hEq
      · exact False.elim (hp.ne_one hp1)
      · exact hEq
    subst p'
    exact ⟨Nat.eq_of_mul_eq_mul_right hp.pos hprod, rfl⟩

/-- Pair-to-product is injective on any finite collection whose prime markers are larger than
every cofactor in the collection.  This packages physical distinctness across an arbitrary
finite, and hence growing, collection of marker blocks. -/
theorem largePrimeMarker_pairProduct_injective
    (S : Finset (ℕ × ℕ))
    (hprime : ∀ q ∈ S, q.2.Prime)
    (hpos : ∀ q ∈ S, 0 < q.1)
    (hsmall : ∀ q ∈ S, ∀ r ∈ S, q.1 < r.2) :
    Set.InjOn (fun q : ℕ × ℕ => q.1 * q.2) S := by
  intro q hq r hr hqr
  have hqa : q.1 = r.1 ∧ q.2 = r.2 :=
    largePrimeMarker_product_injective
      (hprime q hq) (hprime r hr) (hpos r hr)
      (hsmall r hr q hq) (hsmall q hq r hr) hqr
  exact Prod.ext hqa.1 hqa.2

/-- A growing finite marker family loses no physical cardinality when pushed forward to
integer products. -/
theorem card_markerProducts_eq
    (S : Finset (ℕ × ℕ))
    (hprime : ∀ q ∈ S, q.2.Prime)
    (hpos : ∀ q ∈ S, 0 < q.1)
    (hsmall : ∀ q ∈ S, ∀ r ∈ S, q.1 < r.2) :
    (S.image fun q => q.1 * q.2).card = S.card := by
  rw [Finset.card_image_iff]
  exact largePrimeMarker_pairProduct_injective S hprime hpos hsmall

end RHTower
