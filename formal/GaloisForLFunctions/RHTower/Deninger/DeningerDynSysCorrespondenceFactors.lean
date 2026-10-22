/-
Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), Proposition 1.3
(`t26n`), the factorization law of the correspondence.

Combining the bijection of normalized irreducibles (`DeningerDynSysNormalizedCorrespondence`) with
the free-monoid structure of the normalized polynomials
(`DeningerDynSysNormalizedFactorization`): a normalized irreducible `α` over `κ₀` factors over
`κ₀^perf` as a single normalized irreducible `β` repeated `d` times, `d` the degree of
inseparability, and every normalized irreducible over `κ₀^perf` arises that way.

Since factorization is additive on products, this determines the image of the normalized
polynomials of `κ₀[t]` inside those of `κ₀^perf[t]`: exactly the products `∏ β ^ n_β` whose
multiplicities `n_β` are divisible by the corresponding `d_β` — which is the condition
`d_r ∣ n_r` defining `ℤ̲κ / κ₀`.
-/
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysNormalizedCorrespondence
import GaloisForLFunctions.RHTower.Deninger.DeningerDynSysNormalizedFactorization

namespace RHTower

open Polynomial

variable {F : Type*} [Field F]

/-- **Deninger, Proposition 1.3 (`t26n`), the factorization law.**  A normalized irreducible
polynomial over `κ₀` factors over `κ₀^perf` as a single normalized irreducible repeated `d` times,
`d` the degree of inseparability. -/
theorem deningerNormalizedFactors_map_irreducible {L E : Type*} [Field L] [Field E]
    [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
    [IsPurelyInseparable F L] [IsAlgClosed E] (q : ℕ) [ExpChar F q]
    {α : Polynomial F} (hα0 : α.coeff 0 = 1) (hαirr : Irreducible α) :
    ∃ (d : ℕ) (β : Polynomial L), 0 < d ∧ β.coeff 0 = 1 ∧ Irreducible β ∧
      deningerNormalizedFactors (α.map (algebraMap F L)) = Multiset.replicate d β := by
  obtain ⟨d, β, hd, hβ0, hβirr, hmap⟩ :=
    deningerNormalizedIrreducible_map_eq_pow (F := F) (L := L) (E := E) q hα0 hαirr
  refine ⟨d, β, hd, hβ0, hβirr, ?_⟩
  rw [hmap, deningerNormalizedFactors_pow hβ0, deningerNormalizedFactors_irreducible hβ0 hβirr,
    Multiset.nsmul_singleton]

/-- **Deninger, Proposition 1.3 (`t26n`).**  Every normalized irreducible over `κ₀^perf` occurs in
the factorization of some normalized irreducible over `κ₀`. -/
theorem deningerNormalizedFactors_map_surjective {L E : Type*} [Field L] [Field E]
    [Algebra F L] [Algebra F E] [Algebra L E] [IsScalarTower F L E]
    [IsPurelyInseparable F L] [IsAlgClosed E] (q : ℕ) [ExpChar F q]
    {β : Polynomial L} (hβ0 : β.coeff 0 = 1) (hβirr : Irreducible β) :
    ∃ (d : ℕ) (α : Polynomial F), 0 < d ∧ α.coeff 0 = 1 ∧ Irreducible α ∧
      deningerNormalizedFactors (α.map (algebraMap F L)) = Multiset.replicate d β := by
  obtain ⟨d, α, hd, hα0, hαirr, hmap⟩ :=
    deningerNormalizedIrreducible_exists_preimage (F := F) (L := L) (E := E) q hβ0 hβirr
  refine ⟨d, α, hd, hα0, hαirr, ?_⟩
  rw [hmap, deningerNormalizedFactors_pow hβ0, deningerNormalizedFactors_irreducible hβ0 hβirr,
    Multiset.nsmul_singleton]

/-- **Deninger, Proposition 1.3 (`t26n`), injectivity of the correspondence.**  Two normalized
irreducible polynomials over `κ₀` whose images over `κ₀^perf` are powers of the same normalized
irreducible are equal — so the correspondence `α ↦ α̃` is injective, and with surjectivity it is a
bijection. -/
theorem deningerNormalizedIrreducible_map_injective {L : Type*} [Field L] [Algebra F L]
    {α₁ α₂ : Polynomial F} {β : Polynomial L} {d₁ d₂ : ℕ}
    (hα₁0 : α₁.coeff 0 = 1) (hα₁irr : Irreducible α₁)
    (hα₂0 : α₂.coeff 0 = 1) (hα₂irr : Irreducible α₂)
    (h₁ : α₁.map (algebraMap F L) = β ^ d₁) (h₂ : α₂.map (algebraMap F L) = β ^ d₂) :
    α₁ = α₂ := by
  have hinj : Function.Injective (algebraMap F L) := (algebraMap F L).injective
  have hα₁0' : α₁.coeff 0 ≠ 0 := by rw [hα₁0]; exact one_ne_zero
  have hα₂0' : α₂.coeff 0 ≠ 0 := by rw [hα₂0]; exact one_ne_zero
  have hrev₁ : α₁.reverse.Monic := deningerReverse_monic hα₁0
  have hrev₂ : α₂.reverse.Monic := deningerReverse_monic hα₂0
  have hrev₁irr : Irreducible α₁.reverse := deningerIrreducible_reverse hα₁0' hα₁irr
  have hrev₂irr : Irreducible α₂.reverse := deningerIrreducible_reverse hα₂0' hα₂irr
  -- the reversed images are powers of `β.reverse`
  have hr₁ : α₁.reverse.map (algebraMap F L) = β.reverse ^ d₁ := by
    rw [← deningerReverse_map (algebraMap F L) hinj, h₁, deningerReverse_pow]
  have hr₂ : α₂.reverse.map (algebraMap F L) = β.reverse ^ d₂ := by
    rw [← deningerReverse_map (algebraMap F L) hinj, h₂, deningerReverse_pow]
  -- one divides the other
  have hdvd : α₁.reverse ∣ α₂.reverse ∨ α₂.reverse ∣ α₁.reverse := by
    rcases le_total d₁ d₂ with hle | hle
    · left
      rw [← Polynomial.map_dvd_map (algebraMap F L) hinj hrev₁, hr₁, hr₂]
      exact pow_dvd_pow _ hle
    · right
      rw [← Polynomial.map_dvd_map (algebraMap F L) hinj hrev₂, hr₁, hr₂]
      exact pow_dvd_pow _ hle
  have hrevs : α₁.reverse = α₂.reverse := by
    rcases hdvd with h | h
    · exact Polynomial.eq_of_monic_of_associated hrev₁ hrev₂
        (hrev₁irr.associated_of_dvd hrev₂irr h)
    · exact (Polynomial.eq_of_monic_of_associated hrev₂ hrev₁
        (hrev₂irr.associated_of_dvd hrev₁irr h)).symm
  have := congrArg Polynomial.reverse hrevs
  rwa [deningerReverse_reverse hα₁0', deningerReverse_reverse hα₂0'] at this

/-- If `β ^ d` descends and `d ∣ n` then `β ^ n` descends. -/
theorem deningerPow_mem_range_of_dvd {L : Type*} [Field L] [Algebra F L]
    {β : Polynomial L} {α : Polynomial F} {d n : ℕ} (hα0 : α.coeff 0 = 1)
    (hmap : α.map (algebraMap F L) = β ^ d) (hdvd : d ∣ n) :
    ∃ α' : Polynomial F, α'.coeff 0 = 1 ∧ α'.map (algebraMap F L) = β ^ n := by
  obtain ⟨k, rfl⟩ := hdvd
  exact ⟨α ^ k, deningerPow_coeff_zero hα0 k, by rw [Polynomial.map_pow, hmap, ← pow_mul]⟩

/-- Normalized polynomials in the image of `map` are closed under finite products. -/
theorem deningerNormalized_range_prod {L : Type*} [Field L] [Algebra F L]
    (s : Finset (Polynomial L)) (f : Polynomial L → Polynomial L)
    (h : ∀ β ∈ s, ∃ α : Polynomial F, α.coeff 0 = 1 ∧ α.map (algebraMap F L) = f β) :
    ∃ P₀ : Polynomial F, P₀.coeff 0 = 1 ∧ P₀.map (algebraMap F L) = ∏ β ∈ s, f β := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert a s ha ih =>
      obtain ⟨α, hα0, hα⟩ := h a (Finset.mem_insert_self a s)
      obtain ⟨P₀, hP₀0, hP₀⟩ := ih (fun β hβ => h β (Finset.mem_insert_of_mem hβ))
      refine ⟨α * P₀, deningerMul_coeff_zero hα0 hP₀0, ?_⟩
      rw [Finset.prod_insert ha, Polynomial.map_mul, hα, hP₀]

/-- **Deninger, Proposition 1.3 (`t26n`), the descent criterion.**  A normalized polynomial over
`κ₀^perf` descends to `κ₀` as soon as each of its normalized irreducible factors, raised to its
multiplicity, does — which by the correspondence happens exactly when every multiplicity is
divisible by the corresponding degree of inseparability. -/
theorem deningerNormalized_descends {L : Type*} [Field L] [Algebra F L]
    [DecidableEq (Polynomial L)] (P : Polynomial L) (hP : P.coeff 0 = 1)
    (h : ∀ β ∈ deningerNormalizedFactors P, ∃ α : Polynomial F, α.coeff 0 = 1 ∧
      α.map (algebraMap F L) = β ^ ((deningerNormalizedFactors P).count β)) :
    ∃ P₀ : Polynomial F, P₀.coeff 0 = 1 ∧ P₀.map (algebraMap F L) = P := by
  obtain ⟨P₀, hP₀0, hP₀⟩ := deningerNormalized_range_prod
    (deningerNormalizedFactors P).toFinset
    (fun β => β ^ ((deningerNormalizedFactors P).count β))
    (fun β hβ => h β (Multiset.mem_toFinset.1 hβ))
  refine ⟨P₀, hP₀0, ?_⟩
  rw [hP₀, ← Finset.prod_multiset_count, deningerNormalizedFactors_prod hP]

end RHTower
