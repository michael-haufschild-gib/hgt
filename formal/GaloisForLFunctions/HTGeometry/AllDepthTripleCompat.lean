import GaloisForLFunctions.HTGeometry.AllDepthSignatureProperties
import GaloisForLFunctions.HTGeometry.TripticOrbitResidueReciprocity

/-!
# Triple compatibility of the pair-face signatures

The three pair-face signatures of a triple of directions have one common pushforward.  Reciprocity
lets each of them be computed in either of its own two directions; computed in the two directions
of the triple that are not the summation direction, both pushforwards become the same double sum
over the same two-dimensional grid, and Fubini finishes.

* `finite_grid_support_of_finite_classes`, `finsum_comm_grid`;
* **`pairSig_triple_compat`**.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

/-! ## A two-dimensional grid meets finitely many classes -/

theorem finite_grid_support_of_finite_classes {D : ℂ → ℂ} {S : Finset ℂ} {H : AddSubgroup ℂ}
    {u v : ℂ} (hS : ∀ q, D q ≠ 0 → ∃ r ∈ S, q - r ∈ H)
    (hfree : ∀ n m : ℤ, (n : ℂ) * u + (m : ℂ) * v ∈ H → n = 0 ∧ m = 0) (p : ℂ) :
    (Function.support fun x : ℤ × ℤ => D (p + (x.1 : ℂ) * u + (x.2 : ℂ) * v)).Finite := by
  classical
  have hsub : (Function.support fun x : ℤ × ℤ => D (p + (x.1 : ℂ) * u + (x.2 : ℂ) * v))
      ⊆ ⋃ r ∈ (S : Set ℂ), {x : ℤ × ℤ | p + (x.1 : ℂ) * u + (x.2 : ℂ) * v - r ∈ H} := by
    intro x hx
    obtain ⟨r, hr, hmem⟩ := hS _ hx
    exact Set.mem_biUnion (by exact_mod_cast hr) hmem
  refine Set.Finite.subset (Set.Finite.biUnion S.finite_toSet fun r _ => ?_) hsub
  refine Set.Subsingleton.finite ?_
  rintro ⟨n₁, m₁⟩ h₁ ⟨n₂, m₂⟩ h₂
  have hm₁ : p + (n₁ : ℂ) * u + (m₁ : ℂ) * v - r ∈ H := h₁
  have hm₂ : p + (n₂ : ℂ) * u + (m₂ : ℂ) * v - r ∈ H := h₂
  have hrel : ((n₁ - n₂ : ℤ) : ℂ) * u + ((m₁ - m₂ : ℤ) : ℂ) * v ∈ H := by
    have hdiff := sub_mem hm₁ hm₂
    have harg : p + (n₁ : ℂ) * u + (m₁ : ℂ) * v - r
        - (p + (n₂ : ℂ) * u + (m₂ : ℂ) * v - r)
        = ((n₁ - n₂ : ℤ) : ℂ) * u + ((m₁ - m₂ : ℤ) : ℂ) * v := by
      push_cast
      ring
    rwa [harg] at hdiff
  obtain ⟨h1, h2⟩ := hfree _ _ hrel
  have hn : n₁ = n₂ := by omega
  have hm : m₁ = m₂ := by omega
  simp [hn, hm]

theorem finsum_comm_grid {u v : ℂ} {D : ℂ → ℂ} (p : ℂ)
    (hfin : (Function.support fun x : ℤ × ℤ => D (p + (x.1 : ℂ) * u + (x.2 : ℂ) * v)).Finite) :
    (∑ᶠ n : ℤ, ∑ᶠ m : ℤ, D (p + (n : ℂ) * u + (m : ℂ) * v))
      = ∑ᶠ m : ℤ, ∑ᶠ n : ℤ, D (p + (n : ℂ) * u + (m : ℂ) * v) := by
  classical
  set T : ℤ × ℤ → ℂ := fun x => D (p + (x.1 : ℂ) * u + (x.2 : ℂ) * v) with hT
  set T' : ℤ × ℤ → ℂ := fun x => T (Prod.swap x) with hT'
  have hT'fin : (Function.support T').Finite := by
    have hpre := hfin.preimage (Equiv.prodComm ℤ ℤ).injective.injOn
    refine Set.Finite.subset hpre ?_
    intro x hx
    exact hx
  have hcurry := finsum_curry T hfin
  have hcurry' := finsum_curry T' hT'fin
  have hsame : ∑ᶠ x : ℤ × ℤ, T' x = ∑ᶠ x : ℤ × ℤ, T x :=
    finsum_comp_equiv (Equiv.prodComm ℤ ℤ) (f := T)
  rw [← hcurry, ← hsame, hcurry']
  rfl

/-! ## Symmetry of the mixed constraint -/

theorem mixedConstGerm_comm {F : ℂ → ℂ} {a b Cst : ℂ} (h : MixedConstGerm F a b Cst) :
    MixedConstGerm F b a Cst := by
  intro z
  filter_upwards [h z] with w hw
  rw [show w + b + a = w + a + b from by ring]
  linear_combination hw

/-! ## Triple compatibility -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 2000000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **The three pair-face signatures of a triple have one common pushforward.** -/
theorem pairSig_triple_compat (τ : ι → ℂ) (hτ : ∀ m, 0 < (τ m).im)
    (hQ : PeriodsIntegrallyIndependent τ) (s : Finset ι) {i j k : ι}
    (hi : i ∈ s) (hj : j ∈ s) (hk : k ∈ s)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    {Cst : ℂ} {f : ℂ → ℂ} (hmero : MeromorphicOn f (Set.univ : Set ℂ))
    (hper : PeriodicOneGerm f) (hmixed : MixedConstGermSet τ s f Cst)
    {ℓ : ℤ} (hℓ : ℓ < 0) (p : ℂ) :
    (∑ᶠ n : ℤ, pairSig τ s f i j ℓ (p + (n : ℂ) * τ k))
      = ∑ᶠ n : ℤ, pairSig τ s f i k ℓ (p + (n : ℂ) * τ j) := by
  classical
  set W : ℂ → ℂ := HTGeometry.diffCube τ (s \ {i, j, k}) f with hW
  have hWij : pairFaceWitnessFun τ s i j f = HTGeometry.shiftDiffFun (τ k) W :=
    pairFaceWitnessFun_eq_shiftDiffFun τ s (Ne.symm hik) (Ne.symm hjk) hk f
  have hset : s \ ({i, k, j} : Finset ι) = s \ ({i, j, k} : Finset ι) := by
    ext m
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hWik : pairFaceWitnessFun τ s i k f = HTGeometry.shiftDiffFun (τ j) W := by
    have h := pairFaceWitnessFun_eq_shiftDiffFun τ s (Ne.symm hij) (hjk) hj f
    rwa [hset] at h
  set G : ℂ → ℂ := HTGeometry.shiftDiffFun (τ j) (HTGeometry.shiftDiffFun (τ k) W) with hG
  have hGcomm : HTGeometry.shiftDiffFun (τ k) (HTGeometry.shiftDiffFun (τ j) W) = G := by
    rw [hG]
    funext z
    show W (z + τ k + τ j) - W (z + τ k) - (W (z + τ j) - W z)
      = W (z + τ j + τ k) - W (z + τ j) - (W (z + τ k) - W z)
    rw [show z + τ j + τ k = z + τ k + τ j from by ring]
    ring
  -- reciprocity turns each signature into the boundary in the other direction of its pair
  have hWijmero : MeromorphicOn (pairFaceWitnessFun τ s i j f) (Set.univ : Set ℂ) :=
    meromorphicOn_diffCube τ _ hmero
  have hWijper : PeriodicOneGerm (pairFaceWitnessFun τ s i j f) :=
    periodicOneGerm_diffCube τ _ hper
  have hWijmixed : MixedConstGerm (pairFaceWitnessFun τ s i j f) (τ j) (τ i) Cst :=
    mixedConstGerm_pairFaceWitnessFun τ s hij hi hj hmixed
  have hWikmero : MeromorphicOn (pairFaceWitnessFun τ s i k f) (Set.univ : Set ℂ) :=
    meromorphicOn_diffCube τ _ hmero
  have hWikper : PeriodicOneGerm (pairFaceWitnessFun τ s i k f) :=
    periodicOneGerm_diffCube τ _ hper
  have hWikmixed : MixedConstGerm (pairFaceWitnessFun τ s i k f) (τ k) (τ i) Cst :=
    mixedConstGerm_pairFaceWitnessFun τ s hik hi hk hmixed
  have hindepij : ∀ n m l : ℤ, (n : ℂ) * τ j + (m : ℂ) * τ i + (l : ℂ) = 0 →
      n = 0 ∧ m = 0 ∧ l = 0 := by
    intro n m l hrel
    obtain ⟨h1, h2, h3⟩ := indepPeriods_of_periodsIntegrallyIndependent τ hQ hij l n m
      (by linear_combination hrel)
    exact ⟨h2, h3, h1⟩
  have hindepik : ∀ n m l : ℤ, (n : ℂ) * τ k + (m : ℂ) * τ i + (l : ℂ) = 0 →
      n = 0 ∧ m = 0 ∧ l = 0 := by
    intro n m l hrel
    obtain ⟨h1, h2, h3⟩ := indepPeriods_of_periodsIntegrallyIndependent τ hQ hik l n m
      (by linear_combination hrel)
    exact ⟨h2, h3, h1⟩
  have hrecij : ∀ q : ℂ, pairSig τ s f i j ℓ q
      = ∑ᶠ n : ℤ, laurentCoeff G (q + (n : ℂ) * τ j) ℓ := by
    intro q
    have h := triptic_orbit_residue_reciprocity hWijmero hWijper hWijmixed (hτ j) (hτ i)
      hindepij q hℓ
    rw [pairSig, additiveOrbitalDivisorAt, h]
    refine finsum_congr fun n => ?_
    congr 1
    rw [hG, hWij]
    rfl
  have hrecik : ∀ q : ℂ, pairSig τ s f i k ℓ q
      = ∑ᶠ n : ℤ, laurentCoeff G (q + (n : ℂ) * τ k) ℓ := by
    intro q
    have h := triptic_orbit_residue_reciprocity hWikmero hWikper hWikmixed (hτ k) (hτ i)
      hindepik q hℓ
    rw [pairSig, additiveOrbitalDivisorAt, h]
    refine finsum_congr fun n => ?_
    congr 1
    rw [← hGcomm, hWik]
    rfl
  -- finiteness of the two-dimensional grid
  have hGmero : MeromorphicOn G (Set.univ : Set ℂ) := by
    rw [hG, ← hWij]
    intro y _
    exact (meromorphicAt_comp_add.mpr (hWijmero _ (Set.mem_univ _))).sub
      (hWijmero y (Set.mem_univ y))
  obtain ⟨P, hP⟩ := exists_finset_boundaryPoleClasses hWijmero hWijper
    (mixedConstGerm_comm hWijmixed) (linearIndependent_one_of_im_pos (hτ i))
  have hPclass : ∀ q : ℂ, laurentCoeff G q ℓ ≠ 0 →
      ∃ r ∈ P, q - r ∈ lineLattice (τ i) := by
    intro q hq
    have hpole : meromorphicOrderAt G q < 0 :=
      meromorphicOrderAt_neg_of_laurentCoeff_ne_zero (hGmero q (Set.mem_univ q)) hℓ hq
    have hGeq : G = fun w => pairFaceWitnessFun τ s i j f (w + τ j)
        - pairFaceWitnessFun τ s i j f w := by
      rw [hG, hWij]
      rfl
    rw [hGeq] at hpole
    obtain ⟨u, v, hmem⟩ := hP q hpole
    refine ⟨q - (u • (1 : ℂ) + v • τ i), hmem, u, v, ?_⟩
    simp only [zsmul_eq_mul]
    ring
  have hfreeGrid : ∀ n m : ℤ,
      (n : ℂ) * τ k + (m : ℂ) * τ j ∈ lineLattice (τ i) → n = 0 ∧ m = 0 :=
    fun n m h => lineLattice_free_pair τ hQ hik.symm hij.symm (Ne.symm hjk) n m h
  have hgrid := finite_grid_support_of_finite_classes (D := fun q => laurentCoeff G q ℓ)
    (S := P) (H := lineLattice (τ i)) (u := τ k) (v := τ j) hPclass hfreeGrid p
  have hcomm := finsum_comm_grid (u := τ k) (v := τ j) (D := fun q => laurentCoeff G q ℓ) p hgrid
  calc (∑ᶠ n : ℤ, pairSig τ s f i j ℓ (p + (n : ℂ) * τ k))
      = ∑ᶠ n : ℤ, ∑ᶠ m : ℤ, laurentCoeff G (p + (n : ℂ) * τ k + (m : ℂ) * τ j) ℓ := by
        refine finsum_congr fun n => ?_
        exact hrecij _
    _ = ∑ᶠ m : ℤ, ∑ᶠ n : ℤ, laurentCoeff G (p + (n : ℂ) * τ k + (m : ℂ) * τ j) ℓ := hcomm
    _ = ∑ᶠ n : ℤ, pairSig τ s f i k ℓ (p + (n : ℂ) * τ j) := by
        refine finsum_congr fun m => ?_
        rw [hrecik]
        refine finsum_congr fun n => ?_
        rw [show p + (n : ℂ) * τ k + (m : ℂ) * τ j = p + (m : ℂ) * τ j + (n : ℂ) * τ k from by
          ring]

end

end GaloisForLFunctions
