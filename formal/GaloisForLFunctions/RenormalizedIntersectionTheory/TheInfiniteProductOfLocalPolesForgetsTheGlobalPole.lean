import GaloisForLFunctions.RenormalizedIntersectionTheory.TheGlobalPoleIsTheExtremalWeight

/-!
# The infinite product of local poles forgets the global pole

The tensor product `∏_{p∈S} (χ_p + χ_p⁻¹)` grows by the factor `2` with every prime that does not
divide the argument. Its **renormalization** divides each local pole by `2`:
`T(u) = ∏_p ½(χ_p(u) + χ_p(u)⁻¹)`, a finite product for each `u` (`infTensorPole`, a `finprod`).

* **Stabilization** (`infTensorPole_sUnit`): on the `S`-units `T` is the renormalized product over
  `S`, `2^{−|S|} ∏_{p∈S}(χ_p + χ_p⁻¹)`, because every prime outside `S` contributes `½(1 + 1) = 1`.
* **Infinite index** (`negIndex_infTensorPole_eq_top`): on the `S`-units `T` is a sum of `2^{|S|−1}`
  separated weight pairs (`negIndex_infTensorPole_comp_sUnits`), so the renormalized infinite product
  of the local poles has infinitely many negative squares.
* **The global pole has weight `2^{−|S|}`** (`infTensorPole_sUnit_eq_arch_add`): on the `S`-units
  `T` is `2^{−|S|}` times the archimedean pole pair plus the non-extremal weight pairs. As `S` grows
  to all primes the weight of the global pole is `∏_p ½ = 0`.

So the global pole is not a component of the renormalized infinite product of the local poles: the
product carries infinitely many squares and gives the archimedean pole weight zero in the limit. The
one square of `ζ` must be supplied by the archimedean place itself — the gluing of
`TheRenormalizedHodgeIndex` — not assembled from local data.
-/

open Complex Finset
open scoped ComplexConjugate
open GaloisForLFunctions.HeckeKreinToeplitz GaloisForLFunctions.AdelicKreinGeometry

noncomputable section

namespace GaloisForLFunctions.RenormalizedIntersectionTheory

local instance (p : Nat.Primes) : Fact (p : ℕ).Prime := ⟨p.2⟩

/-! ### The `S`-unit group -/

/-- `n ↦ ∏_{q∈S} q^{n_q}` as a homomorphism. -/
def sUnitHom (S : Finset Nat.Primes) : Multiplicative (Nat.Primes → ℤ) →* ℚˣ where
  toFun n := sUnit S (Multiplicative.toAdd n)
  map_one' := by simp [sUnit]
  map_mul' a b := by
    simp only [sUnit, toAdd_mul, Pi.add_apply, zpow_add, prod_mul_distrib]

/-- The `S`-units `{∏_{q∈S} q^{n_q}}`. -/
def sUnits (S : Finset Nat.Primes) : Subgroup ℚˣ := (sUnitHom S).range

theorem sUnit_mem (S : Finset Nat.Primes) (n : Nat.Primes → ℤ) : sUnit S n ∈ sUnits S :=
  ⟨Multiplicative.ofAdd n, rfl⟩

theorem sepUnit_eq_sUnit (S : Finset Nat.Primes) : sepUnit S = sUnit S fun _ => 2 := by
  simp only [sepUnit, sUnit]
  exact prod_congr rfl fun q _ => (zpow_natCast (primeUnit q) 2).symm

theorem localBoost_primeUnit_of_ne {p q : Nat.Primes} (h : p ≠ q) :
    localBoost p (primeUnit q) = 1 := by
  rw [localBoost_primeUnit, localValue, if_neg h, Real.one_rpow, Complex.ofReal_one]

/-- A prime outside `S` does not see the `S`-units. -/
theorem localBoost_sUnit_of_not_mem {S : Finset Nat.Primes} {p : Nat.Primes} (hp : p ∉ S)
    (n : Nat.Primes → ℤ) : localBoost p (sUnit S n) = 1 := by
  rw [sUnit, map_prod]
  exact prod_eq_one fun q hq => by
    rw [map_zpow, localBoost_primeUnit_of_ne fun e => hp (by rw [e]; exact hq), one_zpow]

/-! ### The renormalized infinite product -/

/-- The renormalized local pole `½(χ_p + χ_p⁻¹)`. -/
def halfPole (p : Nat.Primes) (u : ℚˣ) : ℂ := pairKernel (localBoost p) ((1 / 2 : ℝ) : ℂ) u

/-- The renormalized infinite product `∏_p ½(χ_p + χ_p⁻¹)`. -/
def infTensorPole (u : ℚˣ) : ℂ := ∏ᶠ p : Nat.Primes, halfPole p u

theorem halfPole_eq (p : Nat.Primes) (u : ℚˣ) :
    halfPole p u = ((1 / 2 : ℝ) : ℂ) * pairKernel (localBoost p) 1 u := by
  simp only [halfPole, pairKernel, Complex.conj_ofReal, map_one]
  ring

theorem halfPole_sUnit_of_not_mem {S : Finset Nat.Primes} {p : Nat.Primes} (hp : p ∉ S)
    (n : Nat.Primes → ℤ) : halfPole p (sUnit S n) = 1 := by
  have h1 := localBoost_sUnit_of_not_mem hp n
  rw [halfPole_eq, pairKernel_one_apply, reflectChar_apply, map_inv, h1, inv_one, map_one]
  push_cast; ring

/-- **Stabilization**: on the `S`-units the infinite product is `2^{−|S|} ∏_{p∈S}(χ_p + χ_p⁻¹)`. -/
theorem infTensorPole_sUnit (S : Finset Nat.Primes) (n : Nat.Primes → ℤ) :
    infTensorPole (sUnit S n) = (((1 / 2) ^ S.card : ℝ) : ℂ) * tensorPole S (sUnit S n) := by
  rw [infTensorPole, finprod_eq_prod_of_mulSupport_subset (s := S) _ fun p hp => by
    by_contra hpS
    exact hp (halfPole_sUnit_of_not_mem hpS n)]
  simp only [halfPole_eq, prod_mul_distrib, prod_const, tensorPole]
  push_cast; ring

/-- On the `S`-units the infinite product is a sum of weight pairs with coefficient `2^{−|S|}`. -/
theorem infTensorPole_sUnit_eq_sum {S : Finset Nat.Primes} {p₀ : Nat.Primes} (hp₀ : p₀ ∈ S)
    (n : Nat.Primes → ℤ) :
    infTensorPole (sUnit S n) = ∑ t ∈ (S.erase p₀).powerset,
      pairKernel (weightChar S (insert p₀ t)) (((1 / 2) ^ S.card : ℝ) : ℂ) (sUnit S n) := by
  rw [infTensorPole_sUnit, tensorPole_eq_sum_pairKernel hp₀, mul_sum]
  refine sum_congr rfl fun t _ => ?_
  simp only [pairKernel, Complex.conj_ofReal, map_one]
  ring

/-! ### Infinite index -/

theorem reflectChar_comp {G H : Type*} [Group G] [Group H] (χ : G →* ℂ) (f : H →* G) (u : H) :
    reflectChar (χ.comp f) u = reflectChar χ (f u) := by
  simp [reflectChar_apply, map_inv]

/-- **On the `S`-units the infinite product has `2^{|S|−1}` negative squares.** -/
theorem negIndex_infTensorPole_comp_sUnits {S : Finset Nat.Primes} (hS : S.Nonempty) :
    negIndex (infTensorPole ∘ (sUnits S).subtype) = (2 ^ (S.card - 1) : ℕ) := by
  obtain ⟨p₀, hp₀⟩ := hS
  set J := (S.erase p₀).powerset
  set c : ℂ := (((1 / 2) ^ S.card : ℝ) : ℂ)
  have hc : c ≠ 0 := by simp [c]
  obtain ⟨h1, h2, h3, h4⟩ := weightPairs_separation hp₀ (J := J) subset_rfl
  have hu : sepUnit S ∈ sUnits S := by rw [sepUnit_eq_sUnit]; exact sUnit_mem S _
  have hfun : infTensorPole ∘ (sUnits S).subtype = fun h =>
      ∑ t ∈ J, pairKernel ((weightChar S (insert p₀ t)).comp (sUnits S).subtype) c h := by
    funext h
    obtain ⟨n, hn⟩ := h.2
    have hn' : (h : ℚˣ) = sUnit S (Multiplicative.toAdd n) := hn.symm
    simp only [Function.comp_apply, Subgroup.coe_subtype, hn']
    rw [infTensorPole_sUnit_eq_sum hp₀]
    refine sum_congr rfl fun t _ => ?_
    simp only [pairKernel, MonoidHom.comp_apply, Subgroup.coe_subtype, reflectChar_comp, hn', c]
  rw [hfun, negIndex_sum_pairKernel_eq_card J _ (fun _ => c) (fun _ _ => hc) ⟨sepUnit S, hu⟩
    (fun t ht => by simpa using h1 t ht)
    (fun t ht t' ht' h => h2 t ht t' ht' (by simpa using h))
    (fun t ht t' ht' h => h3 t ht t' ht' (by simpa [reflectChar_comp] using h))
    (fun t ht t' ht' h => h4 t ht t' ht' (by simpa [reflectChar_comp] using h)),
    card_powerset, card_erase_of_mem hp₀]

/-- **The renormalized infinite product of the local poles has infinitely many negative
squares.** -/
theorem negIndex_infTensorPole_eq_top : negIndex infTensorPole = ⊤ := by
  refine ENat.eq_top_iff_forall_ge.mpr fun m => ?_
  obtain ⟨S, hS⟩ := Infinite.exists_subset_card_eq Nat.Primes (m + 1)
  have hne : S.Nonempty := card_pos.mp (by omega)
  calc (m : ℕ∞) ≤ ((2 ^ (S.card - 1) : ℕ) : ℕ∞) := by
        rw [hS]; exact_mod_cast (Nat.lt_two_pow_self).le.trans le_rfl
    _ = negIndex (infTensorPole ∘ (sUnits S).subtype) := (negIndex_infTensorPole_comp_sUnits hne).symm
    _ ≤ negIndex infTensorPole := negIndex_comp_le _ _

/-! ### The weight of the global pole -/

/-- **The global pole has weight `2^{−|S|}`** in the renormalized infinite product on the `S`-units:
`T = 2^{−|S|}(χ_∞ + χ_∞⁻¹) +` the non-extremal weight pairs. -/
theorem infTensorPole_sUnit_eq_arch_add {S : Finset Nat.Primes} {p₀ : Nat.Primes} (hp₀ : p₀ ∈ S)
    (n : Nat.Primes → ℤ) :
    infTensorPole (sUnit S n) =
      (((1 / 2) ^ S.card : ℝ) : ℂ) * pairKernel archBoost 1 (sUnit S n) +
        ∑ t ∈ (S.erase p₀).powerset.erase (S.erase p₀),
          pairKernel (weightChar S (insert p₀ t)) (((1 / 2) ^ S.card : ℝ) : ℂ) (sUnit S n) := by
  rw [infTensorPole_sUnit_eq_sum hp₀, ← add_sum_erase _ _ (mem_powerset.mpr subset_rfl),
    insert_erase hp₀, archPole_sUnit_eq_extremalPair]
  congr 1
  simp only [pairKernel, Complex.conj_ofReal, map_one]
  ring

end GaloisForLFunctions.RenormalizedIntersectionTheory
