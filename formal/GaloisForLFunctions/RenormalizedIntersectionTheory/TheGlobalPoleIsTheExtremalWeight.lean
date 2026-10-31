import GaloisForLFunctions.AdelicKreinGeometry.LocalSignaturesAddOverDistinctPlaces

/-!
# The global pole is the extremal weight of the local poles

At a prime `p` the local pole is the hyperbolic pair `χ_p + χ_p⁻¹` of the boost character
`χ_p(u) = |u|_p^{1/2}` on `ℚˣ`; at the real place it is `χ_∞ + χ_∞⁻¹`, `χ_∞(u) = |u|^{1/2}`. For a
finite set `S` of primes the local poles combine in three ways.

* **Separated sum** (`negIndex_sumPole`): `Σ_{p∈S} (χ_p + χ_p⁻¹)` has `|S|` negative squares.
* **Tensor product** (`tensorPole_eq_sum_weightChar`, `negIndex_tensorPole`):
  `∏_{p∈S} (χ_p + χ_p⁻¹) = Σ_{t⊆S} χ^t` with the **weight characters**
  `χ^t = ∏_{p∈t} χ_p · ∏_{p∈S∖t} χ_p⁻¹`. Weights pair as `t ↔ S∖t` (`reflectChar_weightChar`), so
  the product is a sum of `2^{|S|−1}` hyperbolic pairs and has exactly that many negative squares.
* **Weight count** (`negIndex_weightPairs`): every combination of distinct weight pairs with nonzero
  coefficients has as many negative squares as pairs.
* **Extremal weight** (`archBoost_sUnit_eq_weightChar_empty`): on the `S`-units the archimedean boost
  equals the extremal weight `χ^∅ = ∏_{p∈S} χ_p⁻¹` — the product formula `|u| · ∏_{p∈S} |u|_p = 1`.
* **Archimedean weights** (`exists_cpow_weightChar_iff`): `χ^t` agrees on the primes of `S` with an
  archimedean character `u ↦ u^s` exactly when `t = ∅` or `t = S`.

So the global pole, one negative square, is neither the sum (`|S|` squares) nor the product
(`2^{|S|−1}` squares) of the local poles: it is the extremal weight pair of their product, the unique
weight pair that is continuous at the real place (`negIndex_extremalPair`).

All computations use the separating unit `u₀ = ∏_{q∈S} q²`, at which
`χ^t(u₀) = ∏_{q∈S∖t} q / ∏_{q∈t} q`; these rationals are distinct for distinct `t` by unique
factorization.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HeckeKreinToeplitz GaloisForLFunctions.AdelicKreinGeometry

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-! ### Finite index counts for sums of hyperbolic pairs indexed by a finset -/

theorem isPosDefKernel_zero {G : Type*} [Group G] : IsPosDefKernel (fun _ : G => (0 : ℂ)) :=
  ⟨fun _ => by simp, fun n x c => by rw [hermQuad_gram]; simp⟩

/-- **Finset form of the Krein–Langer index formula.** Pairs indexed by a finset, separated at one
element, contribute one negative square each. -/
theorem negIndex_sum_pairKernel_eq_card {G : Type*} [Group G] {ι : Type*} (s : Finset ι)
    (χ : ι → G →* ℂ) (ω : ι → ℂ) (hω : ∀ j ∈ s, ω j ≠ 0) (u : G)
    (hne : ∀ j ∈ s, ‖χ j u‖ ≠ 1)
    (hl : ∀ i ∈ s, ∀ j ∈ s, χ i u = χ j u → i = j)
    (hr : ∀ i ∈ s, ∀ j ∈ s, reflectChar (χ i) u = reflectChar (χ j) u → i = j)
    (hlr : ∀ i ∈ s, ∀ j ∈ s, χ i u ≠ reflectChar (χ j) u) :
    negIndex (fun g => ∑ j ∈ s, pairKernel (χ j) (ω j) g) = s.card := by
  set e : Fin s.card ≃ s := s.equivFin.symm
  have h := negIndex_add_sum_pairKernel_eq isPosDefKernel_zero (fun k => χ (e k)) (fun k => ω (e k))
    (fun k => hω _ (e k).2) u (fun k => hne _ (e k).2) (by
      rintro (a | a) (b | b) hab
      · exact congrArg Sum.inl (e.injective (Subtype.ext (hl _ (e a).2 _ (e b).2 hab)))
      · exact absurd hab (hlr _ (e a).2 _ (e b).2)
      · exact absurd hab.symm (hlr _ (e b).2 _ (e a).2)
      · exact congrArg Sum.inr (e.injective (Subtype.ext (hr _ (e a).2 _ (e b).2 hab))))
  have hfun : (fun g => (0 : ℂ) + ∑ k, pairKernel (χ (e k)) (ω (e k)) g) =
      fun g => ∑ j ∈ s, pairKernel (χ j) (ω j) g := funext fun g => by
    rw [zero_add, ← Finset.sum_coe_sort s]
    exact Equiv.sum_comp e (fun j : s => pairKernel (χ j) (ω j) g)
  rw [← hfun, h]

/-! ### Local boosts -/

/-- A prime as a unit of `ℚ`. -/
def primeUnit (q : Nat.Primes) : ℚˣ := Units.mk0 (q : ℚ) (Nat.cast_ne_zero.mpr q.2.ne_zero)

/-- The local boost character `u ↦ |u|_p^{1/2}` at a prime `p`. -/
def localBoost (p : Nat.Primes) : ℚˣ →* ℂ := boostChar (Rat.AbsoluteValue.padic p) 1

/-- The archimedean boost character `u ↦ |u|^{1/2}`. -/
def archBoost : ℚˣ →* ℂ := boostChar Rat.AbsoluteValue.real 1

theorem reflectChar_boostChar (v : AbsoluteValue ℚ ℝ) (s : ℝ) (u : ℚˣ) :
    reflectChar (boostChar v s) u = (((v (u : ℚ) ^ (s / 2))⁻¹ : ℝ) : ℂ) := by
  simp only [reflectChar_apply, boostChar_apply, Units.val_inv_eq_inv_val, map_inv₀,
    Real.inv_rpow (v.nonneg _), Complex.conj_ofReal]

theorem padic_prime (p q : Nat.Primes) :
    Rat.AbsoluteValue.padic p (q : ℚ) = if p = q then ((p : ℝ))⁻¹ else 1 := by
  rw [Rat.AbsoluteValue.padic_eq_padicNorm]
  split_ifs with h
  · subst h
    rw [padicNorm.padicNorm_p_of_prime]
    push_cast; rfl
  · rw [padicNorm.padicNorm_of_prime_of_ne fun h' => h (Subtype.ext h')]
    simp

/-- The local value `|q²|_p^{1/2}`. -/
def localValue (p q : Nat.Primes) : ℝ := if p = q then ((p : ℝ))⁻¹ else 1

theorem localValue_pos (p q : Nat.Primes) : 0 < localValue p q := by
  unfold localValue; split_ifs
  · exact inv_pos.mpr (Nat.cast_pos.mpr p.2.pos)
  · exact one_pos

theorem localBoost_primeUnit_sq (p q : Nat.Primes) :
    localBoost p (primeUnit q ^ 2) = ((localValue p q : ℝ) : ℂ) := by
  rw [localBoost, boostChar_apply, Units.val_pow_eq_pow_val, map_pow, primeUnit, Units.val_mk0,
    padic_prime]
  congr 1
  unfold localValue
  split_ifs
  · rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  · norm_num

theorem reflect_localBoost_primeUnit_sq (p q : Nat.Primes) :
    reflectChar (localBoost p) (primeUnit q ^ 2) = (((localValue p q)⁻¹ : ℝ) : ℂ) := by
  have h := localBoost_primeUnit_sq p q
  rw [localBoost, boostChar_apply, Complex.ofReal_inj] at h
  rw [localBoost, reflectChar_boostChar, h]

theorem prod_localValue (t : Finset Nat.Primes) (q : Nat.Primes) :
    ∏ p ∈ t, localValue p q = if q ∈ t then ((q : ℝ))⁻¹ else 1 :=
  prod_ite_eq' t q fun p => ((p : ℝ))⁻¹

theorem prod_localValue_inv (t : Finset Nat.Primes) (q : Nat.Primes) :
    ∏ p ∈ t, (localValue p q)⁻¹ = if q ∈ t then (q : ℝ) else 1 := by
  rw [prod_congr rfl fun p _ => show (localValue p q)⁻¹ = if p = q then (p : ℝ) else 1 by
    unfold localValue; split_ifs <;> simp]
  exact prod_ite_eq' t q fun p => (p : ℝ)

/-! ### Weight characters and the tensor product of the local poles -/

/-- The weight character `χ^t = ∏_{p∈t} χ_p · ∏_{p∈S∖t} χ_p⁻¹`. -/
def weightChar (S t : Finset Nat.Primes) : ℚˣ →* ℂ :=
  (∏ p ∈ t, localBoost p) * ∏ p ∈ S \ t, reflectChar (localBoost p)

theorem weightChar_apply (S t : Finset Nat.Primes) (u : ℚˣ) :
    weightChar S t u = (∏ p ∈ t, localBoost p u) * ∏ p ∈ S \ t, reflectChar (localBoost p) u := by
  simp only [weightChar, MonoidHom.mul_apply, MonoidHom.finsetProd_apply]

/-- The tensor product `∏_{p∈S} (χ_p + χ_p⁻¹)` of the local poles. -/
def tensorPole (S : Finset Nat.Primes) (u : ℚˣ) : ℂ := ∏ p ∈ S, pairKernel (localBoost p) 1 u

/-- The separated sum `Σ_{p∈S} (χ_p + χ_p⁻¹)` of the local poles. -/
def sumPole (S : Finset Nat.Primes) (u : ℚˣ) : ℂ := ∑ p ∈ S, pairKernel (localBoost p) 1 u

theorem pairKernel_one_apply {G : Type*} [Group G] (χ : G →* ℂ) (u : G) :
    pairKernel χ 1 u = χ u + reflectChar χ u := by
  simp [pairKernel]

/-- **Weight expansion**: the tensor product of the local poles is the sum of all weight
characters. -/
theorem tensorPole_eq_sum_weightChar (S : Finset Nat.Primes) (u : ℚˣ) :
    tensorPole S u = ∑ t ∈ S.powerset, weightChar S t u := by
  simp only [tensorPole, pairKernel_one_apply, weightChar_apply]
  exact Finset.prod_add _ _ S

/-- **Weights pair as `t ↔ S ∖ t`.** -/
theorem reflectChar_weightChar {S t : Finset Nat.Primes} (ht : t ⊆ S) :
    reflectChar (weightChar S t) = weightChar S (S \ t) := by
  ext u
  rw [reflectChar_apply, weightChar_apply, weightChar_apply, Finset.sdiff_sdiff_eq_self ht, map_mul,
    map_prod, map_prod, mul_comm]
  congr 1 <;> refine prod_congr rfl fun p _ => ?_
  · rw [conj_reflectChar, inv_inv]
  · rfl

/-- **The tensor product is a sum of weight pairs**: fixing `p₀ ∈ S`, each pair `{t, S ∖ t}` has
exactly one member containing `p₀`. -/
theorem tensorPole_eq_sum_pairKernel {S : Finset Nat.Primes} {p₀ : Nat.Primes} (hp₀ : p₀ ∈ S)
    (u : ℚˣ) :
    tensorPole S u =
      ∑ t ∈ (S.erase p₀).powerset, pairKernel (weightChar S (insert p₀ t)) 1 u := by
  set S' := S.erase p₀
  have hS : S = insert p₀ S' := (insert_erase hp₀).symm
  have hnot : p₀ ∉ S' := Finset.notMem_erase p₀ S
  rw [tensorPole_eq_sum_weightChar, show S.powerset = (insert p₀ S').powerset by rw [← hS],
    sum_powerset_insert hnot]
  -- the subsets avoiding `p₀` are the complements of the subsets containing it
  have hcompl : ∑ t ∈ S'.powerset, weightChar S t u =
      ∑ t ∈ S'.powerset, weightChar S (S' \ t) u :=
    sum_nbij' (S' \ ·) (S' \ ·) (fun t _ => mem_powerset.mpr sdiff_subset)
      (fun t _ => mem_powerset.mpr sdiff_subset)
      (fun t ht => Finset.sdiff_sdiff_eq_self (mem_powerset.mp ht))
      (fun t ht => Finset.sdiff_sdiff_eq_self (mem_powerset.mp ht))
      (fun t ht => by rw [Finset.sdiff_sdiff_eq_self (mem_powerset.mp ht)])
  rw [hcompl, ← sum_add_distrib]
  refine sum_congr rfl fun t ht => ?_
  have hsub : insert p₀ t ⊆ S := hS ▸ insert_subset_insert p₀ (mem_powerset.mp ht)
  have hdiff : S \ insert p₀ t = S' \ t := by
    rw [sdiff_insert, ← erase_sdiff_comm]
  rw [pairKernel_one_apply, reflectChar_weightChar hsub, hdiff, add_comm]

/-! ### The separating unit `∏_{q∈S} q²` -/

/-- The separating unit `u₀ = ∏_{q∈S} q²`. -/
def sepUnit (S : Finset Nat.Primes) : ℚˣ := ∏ q ∈ S, primeUnit q ^ 2

/-- The value `∏_{q∈S} (q⁻¹ if q ∈ t, q otherwise)` of `χ^t` at the separating unit. -/
def weightValue (S t : Finset Nat.Primes) : ℝ := ∏ q ∈ S, if q ∈ t then ((q : ℝ))⁻¹ else q

theorem weightChar_primeUnit_sq {S t : Finset Nat.Primes} (ht : t ⊆ S) {q : Nat.Primes}
    (hq : q ∈ S) :
    weightChar S t (primeUnit q ^ 2) = ((if q ∈ t then ((q : ℝ))⁻¹ else q : ℝ) : ℂ) := by
  rw [weightChar_apply]
  simp only [localBoost_primeUnit_sq, reflect_localBoost_primeUnit_sq, ← Complex.ofReal_prod,
    ← Complex.ofReal_mul, Complex.ofReal_inj, prod_localValue, prod_localValue_inv]
  by_cases hqt : q ∈ t
  · have : q ∉ S \ t := fun h => (mem_sdiff.mp h).2 hqt
    simp [hqt, this]
  · have : q ∈ S \ t := mem_sdiff.mpr ⟨hq, hqt⟩
    simp [hqt, this]

theorem weightChar_sepUnit {S t : Finset Nat.Primes} (ht : t ⊆ S) :
    weightChar S t (sepUnit S) = ((weightValue S t : ℝ) : ℂ) := by
  rw [sepUnit, map_prod, weightValue, Complex.ofReal_prod]
  exact prod_congr rfl fun q hq => weightChar_primeUnit_sq ht hq

/-- The product of the primes of a finset. -/
def primeProd (A : Finset Nat.Primes) : ℕ := ∏ p ∈ A, (p : ℕ)

theorem primeProd_pos (A : Finset Nat.Primes) : 0 < primeProd A :=
  prod_pos fun p _ => p.2.pos

theorem prime_dvd_primeProd_iff (A : Finset Nat.Primes) (q : Nat.Primes) :
    (q : ℕ) ∣ primeProd A ↔ q ∈ A := by
  rw [primeProd, Prime.dvd_finsetProd_iff q.2.prime]
  constructor
  · rintro ⟨p, hp, hqp⟩
    rwa [show q = p from Subtype.ext ((Nat.prime_dvd_prime_iff_eq q.2 p.2).mp hqp)]
  · exact fun h => ⟨q, h, dvd_rfl⟩

theorem weightValue_eq {S t : Finset Nat.Primes} (ht : t ⊆ S) :
    weightValue S t = (primeProd (S \ t) : ℝ) / primeProd t := by
  rw [weightValue, prod_ite, filter_mem_eq_inter, inter_eq_right.mpr ht, ← sdiff_eq_filter,
    primeProd, primeProd, prod_inv_distrib, Nat.cast_prod, Nat.cast_prod, div_eq_mul_inv, mul_comm]

theorem weightValue_pos (S t : Finset Nat.Primes) : 0 < weightValue S t :=
  prod_pos fun q _ => by
    have : (0 : ℝ) < q := Nat.cast_pos.mpr q.2.pos
    split_ifs
    · exact inv_pos.mpr this
    · exact this

/-- **Unique factorization separates the weights.** -/
theorem weightValue_injOn {S t t' : Finset Nat.Primes} (ht : t ⊆ S) (ht' : t' ⊆ S)
    (h : weightValue S t = weightValue S t') : t = t' := by
  rw [weightValue_eq ht, weightValue_eq ht'] at h
  have hb : (0 : ℝ) < primeProd t := Nat.cast_pos.mpr (primeProd_pos t)
  have hb' : (0 : ℝ) < primeProd t' := Nat.cast_pos.mpr (primeProd_pos t')
  rw [div_eq_div_iff hb.ne' hb'.ne'] at h
  have hN : primeProd (S \ t) * primeProd t' = primeProd (S \ t') * primeProd t := by
    exact_mod_cast h
  -- a prime in `t` but not in `t'` divides the right side but not the left
  have key : ∀ {a b : Finset Nat.Primes}, a ⊆ S → b ⊆ S →
      primeProd (S \ a) * primeProd b = primeProd (S \ b) * primeProd a → a ⊆ b := by
    intro a b ha hb hab q hqa
    by_contra hqb
    have hdvd : (q : ℕ) ∣ primeProd (S \ b) * primeProd a :=
      dvd_mul_of_dvd_right ((prime_dvd_primeProd_iff a q).mpr hqa) _
    rw [← hab] at hdvd
    rcases (Nat.Prime.dvd_mul q.2).mp hdvd with h1 | h1
    · exact (mem_sdiff.mp ((prime_dvd_primeProd_iff _ q).mp h1)).2 hqa
    · exact hqb ((prime_dvd_primeProd_iff _ q).mp h1)
  exact Subset.antisymm (key ht ht' hN) (key ht' ht hN.symm)

theorem weightValue_ne_one {S t : Finset Nat.Primes} (hS : S.Nonempty) (ht : t ⊆ S) :
    weightValue S t ≠ 1 := by
  intro h1
  obtain ⟨q, hq⟩ := hS
  have hb : (0 : ℝ) < primeProd t := Nat.cast_pos.mpr (primeProd_pos t)
  rw [weightValue_eq ht, div_eq_one_iff_eq hb.ne'] at h1
  have hN : primeProd (S \ t) = primeProd t := by exact_mod_cast h1
  by_cases hqt : q ∈ t
  · have := (prime_dvd_primeProd_iff (S \ t) q).mp (hN ▸ (prime_dvd_primeProd_iff t q).mpr hqt)
    exact (mem_sdiff.mp this).2 hqt
  · exact hqt ((prime_dvd_primeProd_iff t q).mp
      (hN ▸ (prime_dvd_primeProd_iff (S \ t) q).mpr (mem_sdiff.mpr ⟨hq, hqt⟩)))

/-! ### Index of weight pairs -/

/-- **Weight count.** A combination `Σ_{t∈J} (ω_t χ^{p₀∪t} + ω̄_t χ^{S∖(p₀∪t)})` of distinct weight
pairs with nonzero coefficients has exactly `|J|` negative squares. -/
theorem negIndex_weightPairs {S : Finset Nat.Primes} {p₀ : Nat.Primes} (hp₀ : p₀ ∈ S)
    (J : Finset (Finset Nat.Primes)) (hJ : J ⊆ (S.erase p₀).powerset) (ω : Finset Nat.Primes → ℂ)
    (hω : ∀ t ∈ J, ω t ≠ 0) :
    negIndex (fun u => ∑ t ∈ J, pairKernel (weightChar S (insert p₀ t)) (ω t) u) = J.card := by
  have hS : S.Nonempty := ⟨p₀, hp₀⟩
  have hsub : ∀ t ∈ J, insert p₀ t ⊆ S := fun t ht =>
    insert_subset hp₀ ((mem_powerset.mp (hJ ht)).trans (erase_subset p₀ S))
  have hnot : ∀ t ∈ J, p₀ ∉ t := fun t ht h => by
    simpa using (mem_powerset.mp (hJ ht)) h
  have hval : ∀ t ∈ J, weightChar S (insert p₀ t) (sepUnit S) =
      ((weightValue S (insert p₀ t) : ℝ) : ℂ) := fun t ht => weightChar_sepUnit (hsub t ht)
  have hrval : ∀ t ∈ J, reflectChar (weightChar S (insert p₀ t)) (sepUnit S) =
      ((weightValue S (S \ insert p₀ t) : ℝ) : ℂ) := fun t ht => by
    rw [reflectChar_weightChar (hsub t ht), weightChar_sepUnit sdiff_subset]
  -- `insert p₀ t` determines `t` for `p₀ ∉ t`
  have hins : ∀ t ∈ J, ∀ t' ∈ J, insert p₀ t = insert p₀ t' → t = t' := fun t ht t' ht' h => by
    rw [← erase_insert (hnot t ht), ← erase_insert (hnot t' ht'), h]
  refine negIndex_sum_pairKernel_eq_card J _ ω hω (sepUnit S) (fun t ht => ?_) ?_ ?_ ?_
  · rw [hval t ht, Complex.norm_real, Real.norm_of_nonneg (weightValue_pos _ _).le]
    exact weightValue_ne_one hS (hsub t ht)
  · intro t ht t' ht' h
    rw [hval t ht, hval t' ht', Complex.ofReal_inj] at h
    exact hins t ht t' ht' (weightValue_injOn (hsub t ht) (hsub t' ht') h)
  · intro t ht t' ht' h
    rw [hrval t ht, hrval t' ht', Complex.ofReal_inj] at h
    have h' := weightValue_injOn sdiff_subset sdiff_subset h
    have := congrArg (S \ ·) h'
    simp only [Finset.sdiff_sdiff_eq_self (hsub t ht), Finset.sdiff_sdiff_eq_self (hsub t' ht')] at this
    exact hins t ht t' ht' this
  · intro t ht t' ht' h
    rw [hval t ht, hrval t' ht', Complex.ofReal_inj] at h
    have h' := weightValue_injOn (hsub t ht) sdiff_subset h
    have hm : p₀ ∈ S \ insert p₀ t' := h' ▸ mem_insert_self p₀ t
    exact (mem_sdiff.mp hm).2 (mem_insert_self p₀ t')

/-- **The tensor product of the local poles has `2^{|S|−1}` negative squares.** -/
theorem negIndex_tensorPole {S : Finset Nat.Primes} (hS : S.Nonempty) :
    negIndex (tensorPole S) = (2 ^ (S.card - 1) : ℕ) := by
  obtain ⟨p₀, hp₀⟩ := hS
  have h := negIndex_weightPairs hp₀ _ subset_rfl (fun _ => 1) (fun _ _ => one_ne_zero)
  rw [card_powerset, card_erase_of_mem hp₀] at h
  rw [← h]
  exact congrArg negIndex (funext fun u => tensorPole_eq_sum_pairKernel hp₀ u)

/-- **The extremal pair** `χ^S + χ^∅` has exactly one negative square. -/
theorem negIndex_extremalPair {S : Finset Nat.Primes} (hS : S.Nonempty) :
    negIndex (pairKernel (weightChar S S) 1) = 1 := by
  obtain ⟨p₀, hp₀⟩ := hS
  have h := negIndex_weightPairs hp₀ {S.erase p₀} (singleton_subset_iff.mpr
    (mem_powerset.mpr subset_rfl)) (fun _ => 1) (fun _ _ => one_ne_zero)
  simpa [insert_erase hp₀] using h

/-- **The separated sum of the local poles has `|S|` negative squares**: the boosts `χ_p(u₀) = p⁻¹`
are distinct and the reflected values `p` lie on the other side of `1`. -/
theorem negIndex_sumPole (S : Finset Nat.Primes) : negIndex (sumPole S) = S.card := by
  have hval : ∀ p ∈ S, localBoost p (sepUnit S) = ((((p : ℝ))⁻¹ : ℝ) : ℂ) := fun p hp => by
    rw [sepUnit, map_prod, ← prod_congr rfl fun q _ => (localBoost_primeUnit_sq p q).symm,
      ← Complex.ofReal_prod, localValue, prod_ite_eq, if_pos hp]
    rfl
  have hrval : ∀ p ∈ S, reflectChar (localBoost p) (sepUnit S) = (((p : ℝ) : ℝ) : ℂ) :=
    fun p hp => by
      have h := hval p hp
      rw [localBoost, boostChar_apply, Complex.ofReal_inj] at h
      rw [localBoost, reflectChar_boostChar, h, inv_inv]
  have hp1 : ∀ p : Nat.Primes, (1 : ℝ) < p := fun p => by exact_mod_cast p.2.one_lt
  have hp0 : ∀ p : Nat.Primes, (0 : ℝ) < p := fun p => by exact_mod_cast p.2.pos
  refine negIndex_sum_pairKernel_eq_card S _ (fun _ => 1) (fun _ _ => one_ne_zero) (sepUnit S)
    (fun p hp => ?_) ?_ ?_ ?_
  · rw [hval p hp, Complex.norm_real, Real.norm_of_nonneg (inv_pos.mpr (hp0 p)).le]
    exact (inv_lt_one_of_one_lt₀ (hp1 p)).ne
  · intro p hp q hq h
    rw [hval p hp, hval q hq, Complex.ofReal_inj, inv_inj, Nat.cast_inj] at h
    exact Subtype.ext h
  · intro p hp q hq h
    rw [hrval p hp, hrval q hq, Complex.ofReal_inj, Nat.cast_inj] at h
    exact Subtype.ext h
  · intro p hp q hq h
    rw [hval p hp, hrval q hq, Complex.ofReal_inj] at h
    have := inv_lt_one_of_one_lt₀ (hp1 p)
    linarith [hp1 q]

/-! ### The extremal weight is the archimedean pole -/

/-- The `S`-unit `∏_{q∈S} q^{n_q}`. -/
def sUnit (S : Finset Nat.Primes) (n : Nat.Primes → ℤ) : ℚˣ := ∏ q ∈ S, primeUnit q ^ n q

theorem archBoost_primeUnit (q : Nat.Primes) :
    archBoost (primeUnit q) = (((q : ℝ) ^ ((1 : ℝ) / 2) : ℝ) : ℂ) := by
  rw [archBoost, boostChar_apply, primeUnit, Units.val_mk0, Rat.AbsoluteValue.real_eq_abs]
  simp

theorem localBoost_primeUnit (p q : Nat.Primes) :
    localBoost p (primeUnit q) = ((localValue p q ^ ((1 : ℝ) / 2) : ℝ) : ℂ) := by
  rw [localBoost, boostChar_apply, primeUnit, Units.val_mk0, padic_prime]
  rfl

theorem reflect_localBoost_primeUnit (p q : Nat.Primes) :
    reflectChar (localBoost p) (primeUnit q) = (((localValue p q ^ ((1 : ℝ) / 2))⁻¹ : ℝ) : ℂ) := by
  rw [localBoost, reflectChar_boostChar, primeUnit, Units.val_mk0, padic_prime]
  rfl

/-- The value of `χ^t` at a prime `q ∈ S`: `q^{−1/2}` if `q ∈ t`, `q^{1/2}` otherwise. -/
theorem weightChar_primeUnit {S t : Finset Nat.Primes} {q : Nat.Primes} (hq : q ∈ S) :
    weightChar S t (primeUnit q) =
      (((q : ℝ) ^ (if q ∈ t then -((1 : ℝ) / 2) else (1 : ℝ) / 2) : ℝ) : ℂ) := by
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  rw [weightChar_apply]
  simp only [localBoost_primeUnit, reflect_localBoost_primeUnit, ← Complex.ofReal_prod,
    ← Complex.ofReal_mul, Complex.ofReal_inj, localValue]
  have e1 : ∀ p : Nat.Primes, (if p = q then ((p : ℝ))⁻¹ else 1) ^ ((1 : ℝ) / 2) =
      if p = q then (((q : ℝ))⁻¹) ^ ((1 : ℝ) / 2) else 1 := fun p => by
    split_ifs with h
    · rw [h]
    · simp
  simp only [e1, apply_ite (·⁻¹), inv_one]
  rw [prod_ite_eq', prod_ite_eq']
  by_cases hqt : q ∈ t
  · have : q ∉ S \ t := fun h => (mem_sdiff.mp h).2 hqt
    simp [hqt, this, Real.inv_rpow hq0, Real.rpow_neg hq0]
  · have : q ∈ S \ t := mem_sdiff.mpr ⟨hq, hqt⟩
    simp [hqt, this, Real.inv_rpow hq0]

/-- **Product formula on the `S`-units**: the archimedean boost is the extremal weight `χ^∅`. -/
theorem archBoost_sUnit_eq_weightChar_empty (S : Finset Nat.Primes) (n : Nat.Primes → ℤ) :
    archBoost (sUnit S n) = weightChar S ∅ (sUnit S n) := by
  rw [sUnit, map_prod, map_prod]
  refine prod_congr rfl fun q hq => ?_
  rw [map_zpow, map_zpow, archBoost_primeUnit, weightChar_primeUnit hq]
  simp

/-- **The archimedean pole on the `S`-units** is the extremal weight pair of the tensor product of
the local poles. -/
theorem archPole_sUnit_eq_extremalPair (S : Finset Nat.Primes) (n : Nat.Primes → ℤ) :
    pairKernel archBoost 1 (sUnit S n) = pairKernel (weightChar S S) 1 (sUnit S n) := by
  have hinv : (sUnit S n)⁻¹ = sUnit S (-n) := by
    simp only [sUnit, Pi.neg_apply, zpow_neg, prod_inv_distrib]
  have h1 : reflectChar archBoost (sUnit S n) = weightChar S S (sUnit S n) := by
    rw [reflectChar_apply, hinv, archBoost_sUnit_eq_weightChar_empty, ← hinv, ← reflectChar_apply,
      reflectChar_weightChar (empty_subset S), sdiff_empty]
  rw [pairKernel_one_apply, pairKernel_one_apply, h1, archBoost_sUnit_eq_weightChar_empty,
    reflectChar_weightChar subset_rfl, sdiff_self, add_comm]

/-- **Exactly the extremal weights are archimedean.** `χ^t` agrees on the primes of `S` with an
archimedean character `u ↦ u^s` iff `t = ∅` or `t = S`. -/
theorem exists_cpow_weightChar_iff {S t : Finset Nat.Primes} (ht : t ⊆ S) :
    (∃ s : ℂ, ∀ q ∈ S, weightChar S t (primeUnit q) = ((q : ℕ) : ℂ) ^ s) ↔ t = ∅ ∨ t = S := by
  constructor
  · rintro ⟨s, hs⟩
    -- the modulus reads the real part of `s` at every prime of `S`
    have hre : ∀ q ∈ S, s.re = if q ∈ t then -((1 : ℝ) / 2) else (1 : ℝ) / 2 := fun q hq => by
      have h := congrArg norm (hs q hq)
      rw [weightChar_primeUnit hq, Complex.norm_real,
        Real.norm_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _),
        Complex.norm_natCast_cpow_of_pos q.2.pos] at h
      have hq1 : (1 : ℝ) < q := by exact_mod_cast q.2.one_lt
      exact le_antisymm ((Real.rpow_le_rpow_left_iff hq1).mp h.ge)
        ((Real.rpow_le_rpow_left_iff hq1).mp h.le)
    by_contra hne
    push_neg at hne
    obtain ⟨q₁, hq₁⟩ := nonempty_iff_ne_empty.mpr hne.1
    obtain ⟨q₂, hq₂S, hq₂t⟩ : ∃ q ∈ S, q ∉ t := by
      by_contra h
      push_neg at h
      exact hne.2 (Subset.antisymm ht h)
    have h1 := hre q₁ (ht hq₁)
    have h2 := hre q₂ hq₂S
    rw [if_pos hq₁] at h1
    rw [if_neg hq₂t] at h2
    linarith
  · rintro (rfl | rfl)
    · refine ⟨(1 / 2 : ℝ), fun q hq => ?_⟩
      rw [weightChar_primeUnit hq, if_neg (not_mem_empty q),
        Complex.ofReal_cpow (Nat.cast_nonneg _)]
      push_cast; rfl
    · refine ⟨(-(1 / 2) : ℝ), fun q hq => ?_⟩
      rw [weightChar_primeUnit hq, if_pos hq, Complex.ofReal_cpow (Nat.cast_nonneg _)]
      push_cast; rfl

end GaloisForLFunctions.RenormalizedIntersectionTheory
