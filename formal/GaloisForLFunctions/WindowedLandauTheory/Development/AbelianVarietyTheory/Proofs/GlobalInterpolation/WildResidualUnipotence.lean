import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameKummerCharacters

/-! Taking prime-to-residue-characteristic powers is injective at the identity
on finite wild inertia images. A unipotent residual image in a different
characteristic therefore acts trivially. -/

noncomputable section

open Polynomial NumberField
open WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.TameKummer

private theorem wild_pow_ratio {E Ω : Type*} [Field E] [Field Ω] [Algebra E Ω]
    (A : ValuationSubring Ω) (σ : G E Ω)
    (hσ : ∀ x : Ω, x ≠ 0 → A.valuation (σ x / x - 1) < 1)
    {x : Ω} (hx : x ≠ 0) (n : ℕ) : A.valuation ((σ ^ n) x / x - 1) < 1 := by
  induction n with
  | zero => simp [hx]
  | succ n ih =>
    have hz : (σ ^ n) x ≠ 0 := (map_ne_zero (σ ^ n)).mpr hx
    have hle : A.valuation ((σ ^ n) x / x) ≤ 1 := by
      calc
        A.valuation ((σ ^ n) x / x) = A.valuation (((σ ^ n) x / x - 1) + 1) := by rw [sub_add_cancel]
        _ ≤ 1 := (Valuation.map_add _ _ _).trans (max_le ih.le (by rw [map_one]))
    have he : (σ ^ (n + 1)) x / x - 1 =
        (σ ((σ ^ n) x) / (σ ^ n) x - 1) * ((σ ^ n) x / x) + ((σ ^ n) x / x - 1) := by
      rw [pow_succ', AlgEquiv.mul_apply]
      field_simp
      ring
    rw [he]
    apply Valuation.map_add_lt _ _ ih
    rw [map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_right' hle) (hσ _ hz)

/-- If a prime-to-residue-characteristic power of a wild inertia element
lies in an open subgroup, the element lies in that subgroup. -/
theorem mem_of_wild_pow_mem {E Ω : Type*} [Field E] [NumberField E] [Field Ω]
    [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω)
    (U : Subgroup (G E Ω)) (hU : IsOpen (U : Set (G E Ω))) (σ : G E Ω)
    (hσ : ∀ x : Ω, x ≠ 0 → A.valuation (σ x / x - 1) < 1)
    {n : ℕ} (hn : ¬ A.valuation (n : Ω) < 1) (hpow : σ ^ n ∈ U) : σ ∈ U := by
  letI : IsGalois E Ω := {}
  let C : ClosedSubgroup (G E Ω) := ⟨U, U.isClosed_of_isOpen hU⟩
  have he : (IntermediateField.fixedField U).fixingSubgroup = U :=
    InfiniteGalois.fixingSubgroup_fixedField C
  rw [← he, IntermediateField.mem_fixingSubgroup_iff]
  intro y hy
  have hy' : (σ ^ n) y = y := (IntermediateField.mem_fixedField_iff U y).mp hy _ hpow
  by_contra hne
  let z := σ y - y
  have hz : z ≠ 0 := sub_ne_zero.mpr hne
  have hsum : ∑ j ∈ Finset.range n, (σ ^ j) z = 0 := by
    have hz' (j : ℕ) : (σ ^ j) z = (σ ^ (j + 1)) y - (σ ^ j) y := by
      change (σ ^ j) (σ y - y) = _
      rw [map_sub, pow_succ, AlgEquiv.mul_apply]
    simp_rw [hz']
    rw [Finset.sum_range_sub (fun j => (σ ^ j) y), hy']
    simp
  have hlt : A.valuation (∑ j ∈ Finset.range n, ((σ ^ j) z / z - 1)) < 1 :=
    Valuation.map_sum_lt _ one_ne_zero fun j _ => wild_pow_ratio A σ hσ hz j
  rw [Finset.sum_sub_distrib, ← Finset.sum_div, hsum] at hlt
  exact hn (by simpa using hlt)

private theorem pow_eq_one_of_charpoly_unipotent {K : Type*} [Field K] {ℓ N : ℕ}
    [Fact ℓ.Prime] [CharP K ℓ] (M : Matrix (Fin N) (Fin N) K)
    (hM : M.charpoly = (X - 1) ^ N) : M ^ (ℓ ^ N) = 1 := by
  have h₀ : aeval M ((X - 1 : K[X]) ^ N) = 0 := hM ▸ Matrix.aeval_self_charpoly M
  obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le (Nat.lt_pow_self (Fact.out : ℓ.Prime).one_lt (n := N)).le
  have h := calc
    aeval M ((X - 1 : K[X]) ^ (ℓ ^ N)) =
        aeval M ((X - 1 : K[X]) ^ N * (X - 1) ^ j) := by rw [← pow_add, ← hj]
    _ = 0 := by rw [map_mul, h₀, zero_mul]
  rw [sub_pow_char_pow] at h
  simpa [sub_eq_zero] using h

/-- Wild inertia with unipotent image acts trivially in residue
characteristic different from that of the place. -/
theorem eq_one_of_wild_of_unipotent {E Ω : Type} {K : Type*} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [Field K]
    (A : ValuationSubring Ω) {p ℓ N : ℕ} [Fact p.Prime] [Fact ℓ.Prime] [CharP K ℓ]
    (hℓp : ℓ ≠ p) (hp : A.valuation (p : Ω) < 1)
    (ρ : G E Ω →* GL (Fin N) K) (hρ : IsOpen (ρ.ker : Set (G E Ω)))
    {s : G E Ω} (hs : ∀ x : Ω, x ≠ 0 → A.valuation (s x / x - 1) < 1)
    (hpol : (ρ s : Matrix (Fin N) (Fin N) K).charpoly = (X - 1) ^ N) : ρ s = 1 := by
  have hcop : p.Coprime (ℓ ^ N) :=
    ((Nat.coprime_primes (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).mpr hℓp.symm).pow_right N
  have hval := natCast_valuation_not_lt_one A hp hcop
  apply mem_of_wild_pow_mem A ρ.ker hρ s hs hval
  rw [MonoidHom.mem_ker, map_pow, Units.ext_iff, Units.val_pow_eq_pow_val]
  exact pow_eq_one_of_charpoly_unipotent _ hpol


/-- A continuous adic character that takes a prime-to-residue-characteristic
torsion value on a wild inertia element takes value one there. -/
theorem character_eq_one_of_wild_of_pow_eq_one {E Ω R : Type} [Field E] [NumberField E]
    [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [TopologicalSpace R] [IsTopologicalRing R]
    (A : ValuationSubring Ω) (hR : IsAdic (IsLocalRing.maximalIdeal R))
    (χ : G E Ω →* Rˣ) (hχ : Continuous fun g => ((χ g : Rˣ) : R))
    {s : G E Ω} (hs : ∀ x : Ω, x ≠ 0 → A.valuation (s x / x - 1) < 1)
    {n : ℕ} (hn : ¬ A.valuation (n : Ω) < 1) (hpow : χ s ^ n = 1) : χ s = 1 := by
  rw [Units.ext_iff, Units.val_one, ← sub_eq_zero, ← Ideal.mem_bot,
    ← Ideal.iInf_pow_eq_bot_of_isLocalRing (IsLocalRing.maximalIdeal R)
      (IsLocalRing.maximalIdeal.isMaximal R).ne_top, Ideal.mem_iInf]
  intro m
  let J := IsLocalRing.maximalIdeal R ^ m
  let q := (Units.map (Ideal.Quotient.mk J).toMonoidHom).comp χ
  have hk (t : G E Ω) : t ∈ q.ker ↔ ((χ t : Rˣ) : R) - 1 ∈ J := by
    rw [MonoidHom.mem_ker, Units.ext_iff, ← Ideal.Quotient.eq]
    rfl
  have hko : IsOpen (q.ker : Set (G E Ω)) := by
    have he : (q.ker : Set (G E Ω)) = (fun t => ((χ t : Rˣ) : R) - 1) ⁻¹' (J : Set R) :=
      Set.ext hk
    rw [he]
    exact ((isAdic_iff.mp hR).1 m).preimage (hχ.sub continuous_const)
  refine (hk s).mp (mem_of_wild_pow_mem A q.ker hko s hs hn ?_)
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, map_pow χ, hpow, map_one]

end GlobalTheory.TameKummer
