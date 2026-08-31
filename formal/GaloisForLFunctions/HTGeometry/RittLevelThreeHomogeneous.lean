import GaloisForLFunctions.HTGeometry.RittRegularLevelTwo
import GaloisForLFunctions.HTGeometry.RittHomogeneousRigidity
import GaloisForLFunctions.HTGeometry.RittSchwarzian
import GaloisForLFunctions.HTGeometry.RittMonomialConstant

/-!
# Homogeneous eigenvectors at jet order three

The third jet prefix field is `K⟮τ⟯⟮dτ⟯⟮d²τ⟯`, and the shift moves its top generator *affinely*:

`σ(d²τ) = (q/ρ²)·d²τ + λ₂·dτ`,   `λ₂ = −q·(dρ)/ρ³`,

with `λ₂ ≠ 0` whenever the chain-rule factor is nonconstant.  Homogeneous rigidity over an affinely
moved generator therefore applies: a homogeneous eigenvector of the third prefix field either lies
already in the second, or produces the affine connection of the second jet — a relation at jet order
two whose inhomogeneity is a nonzero multiple of `λ₂`, which the level-two classification refutes.

So at jet order three a homogeneous eigenvector is, up to the two base alternatives, a monomial in
the linearizer and its first derivative, with the exponent pair read off the multiplier.
-/

namespace GaloisForLFunctions.HTGeometry

open _root_.Polynomial

variable {K L : Type*} [Field K] [CharZero K] [Field L] [CharZero L] [Algebra K L]

/-- **A homogeneous eigenvector at jet order three is a monomial in the first two jets.** -/
theorem level_three_homogeneous (Fr : RittFrame K L) {τ : L} {q : K}
    {P : K → Prop} (hPreg : RittRegular Fr q P)
    (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) (hq : q ≠ 0)
    (hdρ : Fr.dK Fr.ρ ≠ 0) (hdτ : Fr.d τ ≠ 0)
    (htr0 : Transcendental K τ)
    (htr1 : Transcendental ↥(Fr.jetPrefixField τ 1) (Fr.d τ))
    (htr2 : Transcendental ↥(Fr.jetPrefixField τ 2) (Fr.d^[2] τ))
    {v : L} (hv0 : v ≠ 0) (hvmem : v ∈ Fr.jetPrefixField τ 3)
    {c : K} (hc : c ≠ 0) {i k : ℤ} (hcik : c = q ^ i * Fr.ρ ^ k)
    (hrel : Fr.σ v = algebraMap K L c * v) :
    (∃ (u : K) (I J : ℤ), u ≠ 0 ∧ ¬(I = 0 ∧ J = 0) ∧ Fr.ψ u = q ^ I * Fr.ρ ^ J * u) ∨
    (∃ (u h : K) (I J : ℤ), u ≠ 0 ∧ h ≠ 0 ∧ P h ∧ Fr.ψ u = q ^ I * Fr.ρ ^ J * u + h) ∨
    (∃ (κ : K) (e₀ e₁ : ℤ), κ ≠ 0 ∧ Fr.ψ κ = κ ∧ Fr.dK κ = 0 ∧
      v = algebraMap K L κ * τ ^ e₀ * (Fr.d τ) ^ e₁ ∧ i = e₀ + e₁ ∧ k = -e₁) := by
  classical
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  set E : IntermediateField K L := Fr.jetPrefixField τ 2 with hEdef
  have hEσ : ∀ x ∈ E, Fr.σ x ∈ E := Fr.sigma_mem_jetPrefixField hqconst hshift 2
  set φ : ↥E →+* ↥E :=
    { toFun := fun x => ⟨Fr.σ (x : L), hEσ (x : L) x.2⟩
      map_one' := by ext; simp
      map_mul' := fun _ _ => by ext; simp
      map_zero' := by ext; simp
      map_add' := fun _ _ => by ext; simp } with hφ
  have hcompE : ∀ x : ↥E, Fr.σ (algebraMap ↥E L x) = algebraMap ↥E L (φ x) := fun _ => rfl
  set lam2 : K := -(q * Fr.dK Fr.ρ / Fr.ρ ^ 3) with hlam2
  have hlam20 : lam2 ≠ 0 := by
    rw [hlam2, neg_ne_zero]
    exact div_ne_zero (mul_ne_zero hq hdρ) (pow_ne_zero _ hρ0)
  set aK : K := q / Fr.ρ ^ 2 with haKdef
  have haK0 : aK ≠ 0 := div_ne_zero hq (pow_ne_zero _ hρ0)
  have hdτmem : Fr.d τ ∈ E := by
    have h := Fr.jet_mem_jetPrefixField (τ := τ) (j := 1) (n := 2) (by omega)
    simpa using h
  set aE : ↥E := ⟨algebraMap K L aK, IntermediateField.algebraMap_mem _ _⟩ with haE
  set bE : ↥E := ⟨algebraMap K L lam2 * Fr.d τ,
    mul_mem (IntermediateField.algebraMap_mem _ _) hdτmem⟩ with hbE
  set cE : ↥E := ⟨algebraMap K L c, IntermediateField.algebraMap_mem _ _⟩ with hcE
  have haE0 : aE ≠ 0 := fun h =>
    ((map_ne_zero_iff _ (algebraMap K L).injective).mpr haK0) (congrArg Subtype.val h)
  have hcE0 : cE ≠ 0 := fun h =>
    ((map_ne_zero_iff _ (algebraMap K L).injective).mpr hc) (congrArg Subtype.val h)
  have hσt : Fr.σ (Fr.d^[2] τ) = algebraMap ↥E L aE * Fr.d^[2] τ + algebraMap ↥E L bE :=
    sigma_jet_two Fr hqconst hshift
  have hvadj : v ∈ IntermediateField.adjoin ↥E ({Fr.d^[2] τ} : Set L) := by
    have hv3 : v ∈ Fr.jetPrefixField τ (2 + 1) := hvmem
    have h := (jetPrefixField_succ_eq Fr τ 2) ▸ hv3
    exact h
  have hrelE : Fr.σ v = algebraMap ↥E L cE * v := hrel
  rcases mem_range_or_affine_connection_of_homogeneous_eigen Fr.σ φ hcompE htr2 haE0 hcE0
      hσt hv0 hvadj hrelE with ⟨x, hx⟩ | hb0 | ⟨w, N, hw0, hN, hconn⟩
  · -- the eigenvector is already at jet order two
    have hvmem2 : v ∈ Fr.jetPrefixField τ 2 := by rw [hx]; exact x.2
    have hrel2 : Fr.σ v = algebraMap K L c * v
        + (algebraMap K L (0 : K) * Fr.d τ
          + (algebraMap K L (0 : K) * τ + algebraMap K L (0 : K))) := by
      rw [map_zero, zero_mul, zero_mul, add_zero, add_zero, add_zero]
      exact hrel
    rcases level_two_classification_const Fr hqconst hshift hq htr0 htr1 hv0 hvmem2 hc hcik
        hrel2 with hritt | ⟨hne, -⟩ | hmon
    · exact Or.inl hritt
    · exact absurd ⟨rfl, rfl, rfl⟩ hne
    · obtain ⟨κ, e₀, e₁, hκ0, hψκ, hdκ, -, -, -, hvform, hi, hk⟩ := hmon
      exact Or.inr (Or.inr ⟨κ, e₀, e₁, hκ0, hψκ, hdκ, hvform, hi, hk⟩)
  · -- the second jet has no shift defect, which is impossible
    exfalso
    have hb : algebraMap K L lam2 * Fr.d τ = 0 := hb0
    rcases mul_eq_zero.mp hb with hh | hh
    · exact hlam20 ((map_eq_zero_iff _ (algebraMap K L).injective).mp hh)
    · exact hdτ hh
  · -- the affine connection of the second jet, refuted at jet order two
    have hwL : (w : L) ≠ 0 := fun hh => hw0 (Subtype.ext (by simpa using hh))
    have hcast := congrArg (fun z : ↥E => (z : L)) hconn
    simp only [hφ, haE, hbE] at hcast
    push_cast at hcast
    have hwrel : Fr.σ (w : L) = algebraMap K L aK * (w : L)
        + ∑ j ∈ Finset.range 2,
          aeval τ ((fun j : ℕ => if j = 1 then C (-(N : K) * lam2) else 0) j) * (Fr.d τ) ^ j := by
      rw [Finset.sum_range_succ, Finset.sum_range_one]
      simp only [if_neg (by omega : ¬ (0 : ℕ) = 1), if_true, map_zero, zero_mul, zero_add,
        map_mul, aeval_C, map_neg, pow_one, map_natCast]
      linear_combination hcast
    have hcik2 : aK = q ^ (1 : ℤ) * Fr.ρ ^ (-(2 : ℤ)) := by
      rw [haKdef, zpow_one, zpow_neg, div_eq_mul_inv]
      norm_cast
    have hNlam : (-(N : K) * lam2) ≠ 0 :=
      mul_ne_zero (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr (by omega))) hlam20
    have hPlam2 : P lam2 := by
      have hrw : lam2 = -(q * Fr.dK Fr.ρ * Fr.ρ ^ (-3 : ℤ)) := by
        rw [hlam2, zpow_neg, div_eq_mul_inv]
        norm_cast
      rw [hrw]
      exact hPreg.neg (hPreg.mul (hPreg.mul hPreg.q_mem (hPreg.deriv hPreg.rho_mem))
        (hPreg.rzpow _))
    have hGP : ∀ j m : ℕ,
        P (((fun j : ℕ => if j = 1 then C (-(N : K) * lam2) else 0) j).coeff m) := by
      intro j m
      by_cases hj : j = 1
      · simp only [hj, if_true, coeff_C]
        split
        · exact hPreg.mul (hPreg.neg (hPreg.natCast N)) hPlam2
        · exact hPreg.zero
      · simp only [if_neg hj, coeff_zero]
        exact hPreg.zero
    have hG1 : ((fun j : ℕ => if j = 1 then C (-(N : K) * lam2) else 0) 1) ≠ 0 := by
      simp only [if_true]
      exact fun hz => hNlam (C_eq_zero.mp hz)
    rcases level_two_regular_inhom Fr hPreg hqconst hshift hq htr0 htr1 hwL w.2 haK0 hcik2
        (G := fun j : ℕ => if j = 1 then C (-(N : K) * lam2) else 0) (n := 2)
        ⟨1, by omega, hG1⟩ hGP hwrel with hritt | haff
    · exact Or.inl hritt
    · exact Or.inr (Or.inl haff)

end GaloisForLFunctions.HTGeometry
