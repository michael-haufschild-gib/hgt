import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabels
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PolynomialLabelTransport

/-! An injective labelling of the cuspidal characters gives the same
Harish–Chandra series idempotents after permuting the prime factors. -/

noncomputable section
open Polynomial UniqueFactorizationMonoid
open scoped Classical

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

abbrev CuspidalCharacter (g d : ℕ) [Fact g.Prime] := {χ : Gn g d → ℂ // IsCusp χ}
abbrev PrimeLabel (g d : ℕ) [Fact g.Prime] := {P : (ZMod g)[X] // IsPrimeLab d P}

/-- The prime labels of the cuspidal characters in each positive rank. -/
structure CuspidalLabelMap (g : ℕ) [Fact g.Prime] where
  lab : (d : ℕ) → CuspidalCharacter g d → PrimeLabel g d
  lab_injective : ∀ d, Function.Injective (lab d)

private def CuspidalLabelMap.polynomial (O : CuspidalLabelMap g) (p : Pc g) : (ZMod g)[X] :=
  if h : IsCusp p.2 then (O.lab p.1 ⟨p.2, h⟩).val else 0

private theorem CuspidalLabelMap.polynomial_spec (O : CuspidalLabelMap g) {p : Pc g}
    (hp : IsCusp p.2) : IsPrimeLab p.1 (O.polynomial p) := by
  simpa only [CuspidalLabelMap.polynomial, dif_pos hp] using (O.lab p.1 ⟨p.2, hp⟩).property

/-- The product of the cuspidal labels of a flag whose induction contains the character. -/
def HasLabelO (O : CuspidalLabelMap g) (χ : Gn g n → ℂ) (f : (ZMod g)[X]) : Prop :=
  ∃ C : List (Pc g), (∀ p ∈ C, IsCusp p.2) ∧ degL C = n ∧
    f = (C.map O.polynomial).prod ∧ ip χ (hcL C n) ≠ 0

/-- Central idempotent of the irreducible characters carrying a given label. -/
def eSerO (O : CuspidalLabelMap g) (n : ℕ) (f : (ZMod g)[X]) : MonoidAlgebra ℂ (Gn g n) :=
  ∑ᶠ χ ∈ {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabelO O χ f}, zOf χ

private theorem label_product_spec (O : CuspidalLabelMap g) (C : List (Pc g))
    (hC : ∀ p ∈ C, IsCusp p.2) :
    (C.map O.polynomial).prod.Monic ∧ (C.map O.polynomial).prod.natDegree = degL C ∧
      (C.map O.polynomial).prod.coeff 0 ≠ 0 := by
  induction C with
  | nil => simp [degL]
  | cons p C ih =>
    obtain ⟨hm, _, h0, hd⟩ := O.polynomial_spec (hC p List.mem_cons_self)
    obtain ⟨hm', hd', h0'⟩ := ih (fun q hq => hC q (List.mem_cons_of_mem p hq))
    simp only [List.map_cons, List.prod_cons]
    refine ⟨hm.mul hm', ?_, ?_⟩
    · rw [hm.natDegree_mul hm', hd, hd']
      rfl
    · rw [mul_coeff_zero]
      exact mul_ne_zero h0 h0'

theorem hasLabelO_polynomial_properties (O : CuspidalLabelMap g) {χ : Gn g n → ℂ}
    {f : (ZMod g)[X]} (h : HasLabelO O χ f) :
    f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0 := by
  obtain ⟨C, hC, hd, rfl, -⟩ := h
  simpa only [hd] using label_product_spec O C hC

theorem eSerO_eq_zero (O : CuspidalLabelMap g) (f : (ZMod g)[X])
    (hf : ¬ (f.Monic ∧ f.natDegree = n ∧ f.coeff 0 ≠ 0)) : eSerO O n f = 0 := by
  unfold eSerO
  apply finsum_eq_zero_of_forall_eq_zero
  intro χ
  haveI : IsEmpty (χ ∈ {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabelO O χ f}) :=
    ⟨fun h => hf (hasLabelO_polynomial_properties O h.2)⟩
  exact finsum_of_isEmpty _

private theorem primeLabel_finite (d : ℕ) : Finite (PrimeLabel g d) := by
  let e : {f : (ZMod g)[X] // f.Monic ∧ f.natDegree = d} ≃ (Fin d → ZMod g) :=
    (monicEquivDegreeLT d).trans (degreeLTEquiv (ZMod g) d).toEquiv
  letI := Finite.of_equiv _ e.symm
  exact Finite.of_injective (fun P : PrimeLabel g d =>
    (⟨P.val, P.property.1, P.property.2.2.2⟩ : {f : (ZMod g)[X] // f.Monic ∧ f.natDegree = d}))
    (fun _ _ h => Subtype.ext (congrArg (fun f : {f : (ZMod g)[X] // f.Monic ∧ f.natDegree = d} =>
      f.val) h))

private theorem exists_green_equiv (L : LabelDatum g) (d : ℕ) (hd : 0 < d) :
    ∃ e : PrimeLabel g d ≃ CuspidalCharacter g d, ∀ P, IsCuspOf L P.val (e P).val := by
  obtain ⟨τ, hτ, hinj, hcov⟩ := GlobalTheory.green g L d hd
  let u (P : PrimeLabel g d) : CuspidalCharacter g d := ⟨τ P.val, (hτ P.val P.property).1.2.1⟩
  have h : Function.Bijective u := by
    refine ⟨fun P Q e => Subtype.ext (hinj P.val Q.val P.property Q.property
      (congrArg Subtype.val e)), ?_⟩
    intro χ
    obtain ⟨P, hP, hχ⟩ := hcov χ.val χ.property
    exact ⟨⟨P, hP⟩, Subtype.ext hχ.symm⟩
  exact ⟨Equiv.ofBijective u h, fun P => (hτ P.val P.property).1⟩

/-- Green's correspondence gives an injective label map with its elliptic trace formula. -/
theorem exists_cuspidalLabelMap (L : LabelDatum g) :
    ∃ O : CuspidalLabelMap g, ∀ (d : ℕ) (χ : CuspidalCharacter g d),
      IsCuspOf L (O.lab d χ).val χ.val := by
  choose e he using exists_green_equiv L
  let lab (d : ℕ) (χ : CuspidalCharacter g d) := (e d χ.property.1).symm χ
  refine ⟨⟨lab, ?_⟩, ?_⟩
  · intro d χ ξ h
    exact (e d χ.property.1).symm.injective h
  · intro d χ
    change IsCuspOf L (lab d χ).val χ.val
    have h := he d χ.property.1 (lab d χ)
    change IsCuspOf L (lab d χ).val (e d χ.property.1 ((e d χ.property.1).symm χ)).val at h
    rwa [Equiv.apply_symm_apply] at h

private theorem primeLabel_pos {d : ℕ} {P : (ZMod g)[X]} (h : IsPrimeLab d P) : 0 < d := by
  rw [← h.2.2.2]
  exact natDegree_pos_iff_degree_pos.mpr (degree_pos_of_irreducible h.2.1)

/-- The alternate labels and the Green labels differ by a permutation in each degree. -/
theorem exists_cuspidalLabel_permutation (O : CuspidalLabelMap g) (L : LabelDatum g) :
    ∃ σ π : (ZMod g)[X] → (ZMod g)[X],
      (∀ d P, IsPrimeLab d P → IsPrimeLab d (σ P) ∧ π (σ P) = P) ∧
      ∀ (d : ℕ) (χ : CuspidalCharacter g d), IsCuspOf L (σ (O.lab d χ).val) χ.val := by
  choose e he using exists_green_equiv L
  let p (d : ℕ) (hd : 0 < d) : PrimeLabel g d ≃ PrimeLabel g d :=
    haveI := primeLabel_finite (g := g) d
    Equiv.ofBijective (O.lab d ∘ e d hd)
      (Finite.injective_iff_bijective.mp ((O.lab_injective d).comp (e d hd).injective))
  let σ (P : (ZMod g)[X]) := if h : IsPrimeLab P.natDegree P then
    ((p P.natDegree (primeLabel_pos h)).symm ⟨P, h⟩).val else P
  let π (P : (ZMod g)[X]) := if h : IsPrimeLab P.natDegree P then
    (p P.natDegree (primeLabel_pos h) ⟨P, h⟩).val else P
  have hσ (d : ℕ) (P : (ZMod g)[X]) (hP : IsPrimeLab d P) :
      σ P = ((p d (primeLabel_pos hP)).symm ⟨P, hP⟩).val := by
    have hd := hP.2.2.2
    subst d
    exact dif_pos hP
  have hπ (d : ℕ) (P : (ZMod g)[X]) (hP : IsPrimeLab d P) :
      π P = (p d (primeLabel_pos hP) ⟨P, hP⟩).val := by
    have hd := hP.2.2.2
    subst d
    exact dif_pos hP
  refine ⟨σ, π, ?_, ?_⟩
  · intro d P hP
    rw [hσ d P hP]
    let Q := (p d (primeLabel_pos hP)).symm ⟨P, hP⟩
    refine ⟨Q.property, ?_⟩
    rw [hπ d Q.val Q.property]
    exact congrArg Subtype.val ((p d (primeLabel_pos hP)).apply_symm_apply ⟨P, hP⟩)
  · intro d χ
    let hd : 0 < d := χ.property.1
    let P := (e d hd).symm χ
    have h : O.lab d χ = p d hd P := by
      change O.lab d χ = O.lab d (e d hd P)
      rw [(e d hd).apply_symm_apply χ]
    rw [hσ d (O.lab d χ).val (O.lab d χ).property]
    change IsCuspOf L ((p d hd).symm (O.lab d χ)).val χ.val
    rw [h, (p d hd).symm_apply_apply]
    have he' := he d hd P
    rwa [(e d hd).apply_symm_apply χ] at he'

section Relabel

variable (O : CuspidalLabelMap g) (L : LabelDatum g) {σ π : (ZMod g)[X] → (ZMod g)[X]}
variable (hχ : ∀ (d : ℕ) (χ : CuspidalCharacter g d), IsCuspOf L (σ (O.lab d χ).val) χ.val)
include hχ

private theorem isCuspOf_relabelled (p : Pc g) (hp : IsCusp p.2) :
    IsCuspOf L (σ (O.polynomial p)) p.2 := by
  simpa only [CuspidalLabelMap.polynomial, dif_pos hp] using hχ p.1 ⟨p.2, hp⟩

omit hχ in
private theorem relabelled_cuspidal_product (C : List (Pc g)) (hC : ∀ p ∈ C, IsCusp p.2) :
    relabelPolynomial σ (C.map O.polynomial).prod = (C.map fun p => σ (O.polynomial p)).prod := by
  have hprime (P : (ZMod g)[X]) (hP : P ∈ C.map O.polynomial) : IsPrimeLab P.natDegree P := by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hP
    have h := O.polynomial_spec (hC p hp)
    rw [h.2.2.2]
    exact h
  simp only [relabelPolynomial_list_prod _ hprime, List.map_map, Function.comp_def]

theorem hasLabel_of_hasLabelO {χ : Gn g n → ℂ} {f : (ZMod g)[X]} (hf : HasLabelO O χ f) :
    HasLabel L χ (relabelPolynomial σ f) := by
  obtain ⟨C, hC, hd, rfl, hip⟩ := hf
  let Q := C.map fun p => (σ (O.polynomial p), p)
  have hsnd : Q.map Prod.snd = C := by simp [Q, List.map_map, Function.comp_def]
  refine ⟨Q, ?_, by simpa only [hsnd] using hd, ?_, by simpa only [hsnd] using hip⟩
  · intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact isCuspOf_relabelled O L hχ q (hC q hq)
  · rw [relabelled_cuspidal_product O C hC]
    simp only [Q, List.map_map, Function.comp_def]

/-- Relabelling identifies the two series idempotents on valid polynomial labels. -/
theorem eSerO_eq_eSerC (hg : 5 ≤ g)
    (hσ : ∀ d P, IsPrimeLab d P → IsPrimeLab d (σ P) ∧ π (σ P) = P)
    {f : (ZMod g)[X]} (hm : f.Monic) (h0 : f.coeff 0 ≠ 0) :
    eSerO O n f = eSerC L n (relabelPolynomial σ f) := by
  have he (χ : Gn g n → ℂ) : HasLabelO O χ f ↔ HasLabel L χ (relabelPolynomial σ f) := by
    refine ⟨hasLabel_of_hasLabelO O L hχ, ?_⟩
    rintro ⟨Q, hQ, hd, hf, hip⟩
    let C := Q.map Prod.snd
    have hC (p : Pc g) (hp : p ∈ C) : IsCusp p.2 := by
      obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
      exact (hQ q hq).2.1
    have hlabels : (C.map fun p => σ (O.polynomial p)) = Q.map Prod.fst := by
      rw [List.map_map]
      refine List.map_congr_left fun p hp => ?_
      exact isCuspOf_label_eq L hg (isCuspOf_relabelled O L hχ p.2 (hQ p hp).2.1) (hQ p hp)
    have hprod := relabelled_cuspidal_product (σ := σ) O C hC
    rw [hlabels, ← hf] at hprod
    obtain ⟨hm', _, h0'⟩ := label_product_spec O C hC
    have heq : (C.map O.polynomial).prod = f := calc
      _ = relabelPolynomial π (relabelPolynomial σ (C.map O.polynomial).prod) :=
        (relabelPolynomial_left_inv hσ hm' h0').symm
      _ = relabelPolynomial π (relabelPolynomial σ f) := congrArg (relabelPolynomial π) hprod
      _ = _ := relabelPolynomial_left_inv hσ hm h0
    exact ⟨C, hC, hd, heq.symm, hip⟩
  unfold eSerO eSerC
  have h : {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabelO O χ f} =
      {χ : Gn g n → ℂ | IsIrr χ ∧ HasLabel L χ (relabelPolynomial σ f)} := by
    ext χ
    exact and_congr_right (fun _ => he χ)
  rw [h]

end Relabel

end GlobalTheory.GLq
