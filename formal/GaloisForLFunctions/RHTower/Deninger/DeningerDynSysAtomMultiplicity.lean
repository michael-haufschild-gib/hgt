import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysRootMultiplicity
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysReverseRoots
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysNormalizedCorrespondence
import GaloisForLFunctions.RHTower.Deninger.DeningerRationalWittAlgebraicallyClosedPresentation

/-!
# Atom multiplicities of a normalized polynomial over an algebraic closure

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 1.3
(`t26n`), the lower row.

Under `ω : ℤ̲κ ≅ W_rat (κ)` a normalized polynomial `P` over an algebraically closed field
corresponds to the sum of the Teichmüller atoms attached to the inverses of its roots, with
multiplicity.  A normalized irreducible polynomial `α` over `κ₀` becomes, over `κ`, the `d`-th
power of a separable normalized irreducible, where `d` is the degree of inseparability; hence its
atoms are the elements of a single conjugacy class, each with multiplicity exactly `d`.

This is the computation behind Deninger's subring `ℤ̲κ / κ₀ = { ∑ n_r (r) | d_r ∣ n_r }`: the
image of `W_rat (κ₀)` consists of integral combinations whose coefficients are divisible by the
degrees of inseparability.
-/

namespace RHTower

open Polynomial

variable {F : Type*} [Field F]

/-- The atom multiset depends only on the polynomial. -/
theorem deningerRootUnits_congr {K : Type*} [Field K] {P Q : Polynomial K}
    (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) (h : P = Q) :
    deningerNormalizedPolynomialRootUnits P hP
      = deningerNormalizedPolynomialRootUnits Q hQ := by
  subst h
  rfl

/-- The atoms of a power are the atoms of the base repeated. -/
theorem deningerRootUnits_pow {K : Type*} [Field K] (P : Polynomial K) (hP : P.coeff 0 = 1)
    (d : ℕ) (hPd : (P ^ d).coeff 0 = 1) :
    deningerNormalizedPolynomialRootUnits (P ^ d) hPd
      = d • deningerNormalizedPolynomialRootUnits P hP := by
  refine Multiset.map_injective (f := fun r : Kˣ => (r : K)) Units.val_injective ?_
  rw [deningerNormalizedPolynomialRootUnits_coe, Multiset.map_nsmul,
    deningerNormalizedPolynomialRootUnits_coe, roots_pow]
  exact Multiset.map_nsmul _ _ _

/-- **Deninger, Proposition 1.3 (`t26n`), the atom computation.**  A normalized irreducible
polynomial over `F` has, over an algebraic closure, the atoms of one separable normalized
irreducible, each repeated exactly `d` times. -/
theorem deningerRootUnits_map_irreducible {E : Type*} [Field E] [Algebra F E]
    [IsAlgClosed E] (q : ℕ) [ExpChar F q] {α : Polynomial F} (hα0 : α.coeff 0 = 1)
    (hαirr : Irreducible α) (hmap : (α.map (algebraMap F E)).coeff 0 = 1) :
    ∃ (d : ℕ) (S : Multiset Eˣ), 0 < d ∧ S.Nodup ∧
      deningerNormalizedPolynomialRootUnits (α.map (algebraMap F E)) hmap = d • S := by
  classical
  set L := perfectClosure F E with hL
  obtain ⟨d, β, hd, hβ0, hβirr, hpow⟩ :=
    deningerNormalizedIrreducible_map_eq_pow (F := F) (L := L) (E := E) q hα0 hαirr
  have hmapE : α.map (algebraMap F E) = (β.map (algebraMap L E)) ^ d := by
    have h2 := congrArg (fun p : Polynomial L => p.map (algebraMap L E)) hpow
    simp only [Polynomial.map_pow] at h2
    rw [← h2, Polynomial.map_map, ← IsScalarTower.algebraMap_eq F L E]
  have hβmap0 : (β.map (algebraMap L E)).coeff 0 = 1 := by
    rw [Polynomial.coeff_map, hβ0, map_one]
  haveI : PerfectField E := IsAlgClosed.perfectField E
  have hβsep : β.Separable := PerfectField.separable_of_irreducible hβirr
  have hβsepE : (β.map (algebraMap L E)).Separable := hβsep.map
  refine ⟨d, deningerNormalizedPolynomialRootUnits (β.map (algebraMap L E)) hβmap0, hd, ?_, ?_⟩
  · refine Multiset.Nodup.of_map (fun r : Eˣ => (r : E)) ?_
    rw [deningerNormalizedPolynomialRootUnits_coe]
    refine Multiset.Nodup.map_on (fun a _ b _ hab => ?_) (nodup_roots hβsepE)
    exact inv_injective hab
  · have hcongr := deningerRootUnits_congr (P := α.map (algebraMap F E))
      (Q := (β.map (algebraMap L E)) ^ d) hmap (by rw [← hmapE]; exact hmap) hmapE
    rw [hcongr, deningerRootUnits_pow]

end RHTower

namespace RHTower

open Polynomial

/-- The multiplicity of an atom is the multiplicity of the inverse root. -/
theorem deningerRootUnits_count {K : Type*} [Field K] [DecidableEq Kˣ] (P : Polynomial K)
    (hP : P.coeff 0 = 1) (u : Kˣ) :
    Multiset.count u (deningerNormalizedPolynomialRootUnits P hP)
      = P.rootMultiplicity ((u : K)⁻¹) := by
  classical
  have h1 : Multiset.count u (deningerNormalizedPolynomialRootUnits P hP)
      = Multiset.count (u : K)
        ((deningerNormalizedPolynomialRootUnits P hP).map fun r : Kˣ => (r : K)) :=
    (Multiset.count_map_eq_count' _ _ Units.val_injective u).symm
  rw [h1, deningerNormalizedPolynomialRootUnits_coe]
  have h2 : Multiset.count (u : K) (P.roots.map fun r => r⁻¹)
      = Multiset.count ((u : K)⁻¹) P.roots := by
    have := Multiset.count_map_eq_count' (fun r : K => r⁻¹) P.roots inv_injective ((u : K)⁻¹)
    simpa using this
  rw [h2, Polynomial.count_roots]

/-- The atoms of a product are the atoms of the factors together. -/
theorem deningerRootUnits_mul {K : Type*} [Field K] (P Q : Polynomial K)
    (hP : P.coeff 0 = 1) (hQ : Q.coeff 0 = 1) (hPQ : (P * Q).coeff 0 = 1) :
    deningerNormalizedPolynomialRootUnits (P * Q) hPQ
      = deningerNormalizedPolynomialRootUnits P hP
        + deningerNormalizedPolynomialRootUnits Q hQ := by
  refine Multiset.map_injective (f := fun r : Kˣ => (r : K)) Units.val_injective ?_
  have hPne : P ≠ 0 := fun h => by rw [h, Polynomial.coeff_zero] at hP; exact zero_ne_one hP
  have hQne : Q ≠ 0 := fun h => by rw [h, Polynomial.coeff_zero] at hQ; exact zero_ne_one hQ
  rw [deningerNormalizedPolynomialRootUnits_coe, Multiset.map_add,
    deningerNormalizedPolynomialRootUnits_coe, deningerNormalizedPolynomialRootUnits_coe,
    Polynomial.roots_mul (mul_ne_zero hPne hQne), Multiset.map_add]

/-- **Deninger, Proposition 1.3 (`t26n`).**  Every atom of the image of a normalized irreducible
polynomial occurs with multiplicity `0` or exactly `d`. -/
theorem deningerRootUnits_map_irreducible_count {F E : Type*} [Field F] [Field E] [Algebra F E]
    [IsAlgClosed E] [DecidableEq Eˣ] (q : ℕ) [ExpChar F q] {α : Polynomial F}
    (hα0 : α.coeff 0 = 1) (hαirr : Irreducible α)
    (hmap : (α.map (algebraMap F E)).coeff 0 = 1) :
    ∃ d : ℕ, 0 < d ∧ ∀ u : Eˣ,
      Multiset.count u (deningerNormalizedPolynomialRootUnits (α.map (algebraMap F E)) hmap) = 0
        ∨ Multiset.count u
          (deningerNormalizedPolynomialRootUnits (α.map (algebraMap F E)) hmap) = d := by
  obtain ⟨d, S, hd, hSnodup, hS⟩ :=
    deningerRootUnits_map_irreducible (F := F) (E := E) q hα0 hαirr hmap
  refine ⟨d, hd, fun u => ?_⟩
  rw [hS, Multiset.count_nsmul]
  rcases Nat.lt_or_ge (Multiset.count u S) 1 with hlt | hge
  · left
    have : Multiset.count u S = 0 := by omega
    rw [this, mul_zero]
  · right
    have hle : Multiset.count u S ≤ 1 := Multiset.nodup_iff_count_le_one.1 hSnodup u
    have : Multiset.count u S = 1 := by omega
    rw [this, mul_one]

end RHTower

namespace RHTower

open Polynomial

/-- **Deninger, Proposition 1.3 (`t26n`), the coefficient law.**  Every atom of the image of a
normalized irreducible polynomial over `κ₀` occurs with multiplicity exactly the degree of
inseparability of that atom.  This is the statement `d_r ∣ n_r` defining `ℤ̲κ / κ₀`. -/
theorem deningerAtomCount_eq_insepDegree {F E : Type*} [Field F] [Field E] [Algebra F E]
    [IsAlgClosed E] [DecidableEq Eˣ] (q : ℕ) [ExpChar F q] {α : Polynomial F}
    (hα0 : α.coeff 0 = 1) (hαirr : Irreducible α)
    (hmap : (α.map (algebraMap F E)).coeff 0 = 1) {u : Eˣ}
    (hu : u ∈ deningerNormalizedPolynomialRootUnits (α.map (algebraMap F E)) hmap) :
    Multiset.count u (deningerNormalizedPolynomialRootUnits (α.map (algebraMap F E)) hmap)
      = deningerInsepDegree F E q (u : E) := by
  classical
  set P : Polynomial E := α.map (algebraMap F E) with hP
  have hPne : P ≠ 0 := fun h => by
    rw [h, Polynomial.coeff_zero] at hmap; exact zero_ne_one hmap
  have hune : (u : E) ≠ 0 := u.ne_zero
  have hP0 : P.coeff 0 ≠ 0 := by rw [hmap]; exact one_ne_zero
  -- the count is the multiplicity of the inverse root
  have hcount : Multiset.count u (deningerNormalizedPolynomialRootUnits P hmap)
      = P.rootMultiplicity ((u : E)⁻¹) := deningerRootUnits_count P hmap u
  -- the inverse of the atom is a root
  have hroot : P.IsRoot ((u : E)⁻¹) := by
    have hpos : 0 < Multiset.count u (deningerNormalizedPolynomialRootUnits P hmap) :=
      Multiset.count_pos.2 hu
    rw [hcount] at hpos
    exact (Polynomial.rootMultiplicity_pos hPne).1 hpos
  -- transfer to the reverse
  have hrev : P.reverse.rootMultiplicity (u : E) = P.rootMultiplicity ((u : E)⁻¹) := by
    have h := deningerRootMultiplicity_reverse (p := P) hP0 (r := (u : E)⁻¹) (inv_ne_zero hune)
    rwa [inv_inv] at h
  have hrevmap : P.reverse = α.reverse.map (algebraMap F E) :=
    deningerReverse_map (algebraMap F E) (algebraMap F E).injective α
  -- the reverse of `α` is the minimal polynomial of the atom
  haveI : Invertible (u : E) := invertibleOfNonzero hune
  have hevalrev : Polynomial.eval₂ (algebraMap F E) (u : E) α.reverse = 0 := by
    have h1 : Polynomial.eval₂ (algebraMap F E) (u : E) α.reverse
        = Polynomial.eval (u : E) P.reverse := by
      rw [hrevmap, Polynomial.eval_map]
    rw [h1]
    haveI : Invertible ((u : E)⁻¹) := invertibleOfNonzero (inv_ne_zero hune)
    have h2 : Polynomial.eval₂ (RingHom.id E) (⅟((u : E)⁻¹)) P.reverse = 0 ↔
        Polynomial.eval₂ (RingHom.id E) ((u : E)⁻¹) P = 0 :=
      Polynomial.eval₂_reverse_eq_zero_iff (RingHom.id E) ((u : E)⁻¹) P
    have hinv : (⅟((u : E)⁻¹) : E) = (u : E) := by
      rw [invOf_eq_inv, inv_inv]
    rw [hinv] at h2
    have h3 : Polynomial.eval₂ (RingHom.id E) ((u : E)⁻¹) P = 0 := by
      simpa [Polynomial.eval₂_eq_eval_map] using hroot
    have h4 := h2.2 h3
    simpa [Polynomial.eval₂_eq_eval_map] using h4
  have haeval : (Polynomial.aeval (u : E)) α.reverse = 0 := by
    rw [Polynomial.aeval_def]
    exact hevalrev
  have hminpoly : α.reverse = minpoly F (u : E) :=
    minpoly.eq_of_irreducible_of_monic
      (deningerIrreducible_reverse (by rw [hα0]; exact one_ne_zero) hαirr) haeval
      (deningerReverse_monic hα0)
  have hint : IsIntegral F (u : E) :=
    ⟨α.reverse, deningerReverse_monic hα0, hevalrev⟩
  have hrootmin : ((minpoly F (u : E)).map (algebraMap F E)).IsRoot (u : E) := by
    rw [← hminpoly, ← hrevmap]
    have hpos : 0 < P.rootMultiplicity ((u : E)⁻¹) := by
      rw [← hcount]
      exact Multiset.count_pos.2 hu
    rw [← hrev] at hpos
    exact (Polynomial.rootMultiplicity_pos (deningerReverse_ne_zero hP0)).1 hpos
  rw [hcount, ← hrev, hrevmap, hminpoly]
  exact deningerRootMultiplicity_minpoly_map q hint hrootmin

end RHTower

namespace RHTower

open Polynomial

variable {F E : Type*} [Field F] [Field E] [Algebra F E]

/-- The atoms of the constant polynomial `1` are empty. -/
theorem deningerRootUnits_one {K : Type*} [Field K] (h1 : (1 : Polynomial K).coeff 0 = 1) :
    deningerNormalizedPolynomialRootUnits (1 : Polynomial K) h1 = 0 := by
  refine Multiset.map_injective (f := fun r : Kˣ => (r : K)) Units.val_injective ?_
  rw [deningerNormalizedPolynomialRootUnits_coe]
  simp

/-- A product of normalized polynomials is normalized. -/
theorem deningerProdCoeffZero {K : Type*} [Field K] :
    ∀ (S : Multiset (Polynomial K)), (∀ α ∈ S, α.coeff 0 = 1) → (S.prod).coeff 0 = 1 := by
  intro S
  induction S using Multiset.induction_on with
  | empty => intro _; simp
  | cons a S ih =>
      intro hS
      rw [Multiset.prod_cons]
      rw [Polynomial.mul_coeff_zero, hS a (Multiset.mem_cons_self a S),
        ih (fun α hα => hS α (Multiset.mem_cons_of_mem hα)), one_mul]

/-- **Deninger, Proposition 1.3 (`t26n`), the coefficient law for products.**  Every atom of the
image of a product of normalized irreducible polynomials over `κ₀` occurs with multiplicity
divisible by its degree of inseparability. -/
theorem deningerRootUnits_map_prod_count_dvd [IsAlgClosed E] [DecidableEq Eˣ] (q : ℕ)
    [ExpChar F q] :
    ∀ (S : Multiset (Polynomial F)), (∀ α ∈ S, α.coeff 0 = 1 ∧ Irreducible α) →
      ∀ (hmap : ((S.prod).map (algebraMap F E)).coeff 0 = 1) (u : Eˣ),
        (deningerInsepDegree F E q (u : E) : ℕ) ∣
          Multiset.count u
            (deningerNormalizedPolynomialRootUnits ((S.prod).map (algebraMap F E)) hmap) := by
  classical
  intro S
  induction S using Multiset.induction_on with
  | empty =>
      intro _ hmap u
      have h1 : ((0 : Multiset (Polynomial F)).prod).map (algebraMap F E) = 1 := by
        simp
      have := deningerRootUnits_congr (P := ((0 : Multiset (Polynomial F)).prod).map
        (algebraMap F E)) (Q := (1 : Polynomial E)) hmap (by simp) h1
      rw [this, deningerRootUnits_one]
      simp
  | cons a S ih =>
      intro hS hmap u
      have ha := hS a (Multiset.mem_cons_self a S)
      have hSmem : ∀ α ∈ S, α.coeff 0 = 1 ∧ Irreducible α :=
        fun α hα => hS α (Multiset.mem_cons_of_mem hα)
      have haM : (a.map (algebraMap F E)).coeff 0 = 1 := by
        rw [Polynomial.coeff_map, ha.1, map_one]
      have hSM : ((S.prod).map (algebraMap F E)).coeff 0 = 1 := by
        rw [Polynomial.coeff_map]
        have : (S.prod).coeff 0 = 1 := deningerProdCoeffZero S (fun α hα => (hSmem α hα).1)
        rw [this, map_one]
      have hsplit : ((a ::ₘ S).prod).map (algebraMap F E)
          = a.map (algebraMap F E) * (S.prod).map (algebraMap F E) := by
        rw [Multiset.prod_cons, Polynomial.map_mul]
      have hcongr := deningerRootUnits_congr (P := ((a ::ₘ S).prod).map (algebraMap F E))
        (Q := a.map (algebraMap F E) * (S.prod).map (algebraMap F E)) hmap
        (by rw [← hsplit]; exact hmap) hsplit
      rw [hcongr, deningerRootUnits_mul _ _ haM hSM, Multiset.count_add]
      refine dvd_add ?_ (ih hSmem hSM u)
      by_cases hu : u ∈ deningerNormalizedPolynomialRootUnits (a.map (algebraMap F E)) haM
      · rw [deningerAtomCount_eq_insepDegree q ha.1 ha.2 haM hu]
      · rw [Multiset.count_eq_zero_of_notMem hu]
        exact dvd_zero _

end RHTower
