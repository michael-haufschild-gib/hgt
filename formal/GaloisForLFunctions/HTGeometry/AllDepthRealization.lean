import GaloisForLFunctions.HTGeometry.AllDepthTripleCompat
import GaloisForLFunctions.HTGeometry.AllDepthCarrierJets
import GaloisForLFunctions.HTGeometry.AllDepthSimultaneousLift
import GaloisForLFunctions.HTGeometry.AllDepthCarrierSpan
import GaloisForLFunctions.HTGeometry.TripticNormalForm
import GaloisForLFunctions.HTGeometry.AllDepthPeriodSpan
import GaloisForLFunctions.HTGeometry.AllDepthSignatureDescent

/-!
# Realizing a prescribed pair-face signature

Every compatible family of finite class divisors is the pair-face signature of a member of the
all-depth mixed-constraint class.  At depth two this is the corpus's surjectivity of the orbital
divisor; at depth `d ≥ 3` the components through one distinguished direction are lifted to a single
bottom charge by the simultaneous lifting lemma, that charge is realized, and the residual error on
the pairs below the distinguished direction is a one-step difference whose antiderivative is
realized by the inductive hypothesis.

* **`exists_depthTwo_member_with_prescribed_divisor`**.
-/

open Filter Set Topology Complex
open scoped Differential BigOperators

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

set_option maxHeartbeats 1600000 in
/-- **Depth-two realization.**  Every finite class divisor of bounded order is the orbital divisor
of a member of the depth-two class. -/
theorem exists_depthTwo_member_with_prescribed_divisor {a b : ℂ} (ha : 0 < a.im) (hb : 0 < b.im)
    (hindep : IndepPeriods a b) (D : ℤ → ℂ → ℂ) (N : ℕ)
    (hinv : ∀ ℓ : ℤ, ℓ < 0 → DivInvariant (tripticPeriodGroup a b) (D ℓ))
    (hfin : ∀ ℓ : ℤ, ℓ < 0 → DivFiniteClasses (tripticPeriodGroup a b) (D ℓ))
    (htop : ∀ ℓ : ℤ, ℓ < -(N : ℤ) → ∀ p, D ℓ p = 0) :
    ∃ (Y : ℂ → ℂ) (C : ℂ), MeromorphicOn Y (Set.univ : Set ℂ) ∧ PeriodicOneGerm Y ∧
      MixedConstGerm Y a b C ∧
      ∀ (ℓ : ℤ), ℓ < 0 → ∀ p, additiveOrbitalDivisorAt Y b p ℓ = D ℓ p := by
  classical
  set H : AddSubgroup ℂ := tripticPeriodGroup a b with hH
  choose S hS using fun m : ℕ => hfin (-((m : ℤ) + 1)) (by omega)
  set mkq : ℂ → (ℂ ⧸ H) := fun z => QuotientAddGroup.mk z with hmkq
  have hmk_eq : ∀ u v : ℂ, mkq u = mkq v ↔ u - v ∈ H := fun u v =>
    QuotientAddGroup.eq_iff_sub_mem
  have hout : ∀ x : ℂ ⧸ H, mkq (Quotient.out x) = x := fun x => QuotientAddGroup.out_eq' x
  set P : Finset ℂ := ((Finset.range N).biUnion S).image (fun q => Quotient.out (mkq q)) with hP
  have hPform : ∀ q ∈ P, ∃ x : ℂ ⧸ H, q = Quotient.out x := by
    intro q hq
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨mkq t, rfl⟩
  have hsame_mk : ∀ q p : ℂ, SameClass a b q p ↔ mkq q = mkq p := by
    intro q p
    rw [sameClass_iff, hmkq]
    constructor
    · intro h
      exact QuotientAddGroup.eq_iff_sub_mem.mpr h
    · intro h
      exact QuotientAddGroup.eq_iff_sub_mem.mp h
  have huniq : ∀ q ∈ P, ∀ q' ∈ P, SameClass a b q' q → q' = q := by
    intro q hq q' hq' hsame
    obtain ⟨x, rfl⟩ := hPform q hq
    obtain ⟨y, rfl⟩ := hPform q' hq'
    have := (hsame_mk _ _).mp hsame
    rw [hout, hout] at this
    rw [this]
  obtain ⟨Y, C, hYmero, hYper, hYmixed, hYclass, hYoff, hYtop⟩ :=
    exists_mem_class_with_prescribed_divisor ha hb hindep P N
      (fun q m => D (-((m : ℤ) + 1)) q)
  refine ⟨Y, C, hYmero, hYper, hYmixed, ?_⟩
  intro ℓ hℓ p
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, ℓ = -((m : ℤ) + 1) := ⟨(-ℓ - 1).toNat, by omega⟩
  by_cases hmN : m < N
  · by_cases hcase : ∃ q ∈ P, SameClass a b q p
    · obtain ⟨q, hq, hqp⟩ := hcase
      rw [hYclass q hq m hmN p hqp (fun q' hq' hs => huniq q hq q' hq' (by
        have h1 := (hsame_mk q' p).mp hs
        have h2 := (hsame_mk q p).mp hqp
        exact (hsame_mk q' q).mpr (by rw [h1, h2])))]
      have hmem : q - p ∈ H := (sameClass_iff a b q p).mp hqp
      have hval := hinv (-((m : ℤ) + 1)) (by omega) p (q - p) hmem
      rw [show p + (q - p) = q from by ring] at hval
      exact hval
    · push Not at hcase
      rw [hYoff m p (by
        rintro ⟨q, hq, hs⟩
        exact hcase q hq hs)]
      by_contra hne
      obtain ⟨q, hq, hmem⟩ := hS m p (Ne.symm hne)
      have hqT : q ∈ (Finset.range N).biUnion S :=
        Finset.mem_biUnion.mpr ⟨m, Finset.mem_range.mpr hmN, hq⟩
      have hoP : Quotient.out (mkq q) ∈ P := Finset.mem_image.mpr ⟨q, hqT, rfl⟩
      refine hcase _ hoP ?_
      refine (hsame_mk _ _).mpr ?_
      rw [hout]
      exact ((hmk_eq p q).mpr hmem).symm
  · rw [hYtop m (by omega) p]
    exact (htop _ (by omega) p).symm

/-! ## Elementary laws of the signature -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem tripticPeriodGroup_comm (a b : ℂ) : tripticPeriodGroup a b = tripticPeriodGroup b a := by
  ext p
  constructor
  · rintro ⟨c, q, r, rfl⟩
    exact ⟨c, r, q, by ring⟩
  · rintro ⟨c, q, r, rfl⟩
    exact ⟨c, r, q, by ring⟩

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **The signature is symmetric in its pair.** -/
theorem pairSig_symm (τ : ι → ℂ) (hτ : ∀ m, 0 < (τ m).im)
    (hQ : PeriodsIntegrallyIndependent τ) (s : Finset ι) {i j : ι} (hij : i ≠ j)
    (hi : i ∈ s) (hj : j ∈ s) {Cst : ℂ} {f : ℂ → ℂ}
    (hmero : MeromorphicOn f (Set.univ : Set ℂ)) (hper : PeriodicOneGerm f)
    (hmixed : MixedConstGermSet τ s f Cst) {ℓ : ℤ} (hℓ : ℓ < 0) (p : ℂ) :
    pairSig τ s f i j ℓ p = pairSig τ s f j i ℓ p := by
  classical
  have hWmero : MeromorphicOn (pairFaceWitnessFun τ s i j f) (Set.univ : Set ℂ) :=
    meromorphicOn_diffCube τ _ hmero
  have hWper : PeriodicOneGerm (pairFaceWitnessFun τ s i j f) :=
    periodicOneGerm_diffCube τ _ hper
  have hWmixed : MixedConstGerm (pairFaceWitnessFun τ s i j f) (τ j) (τ i) Cst :=
    mixedConstGerm_pairFaceWitnessFun τ s hij hi hj hmixed
  have hindep : ∀ n m l : ℤ, (n : ℂ) * τ j + (m : ℂ) * τ i + (l : ℂ) = 0 →
      n = 0 ∧ m = 0 ∧ l = 0 := by
    intro n m l hrel
    obtain ⟨h1, h2, h3⟩ := indepPeriods_of_periodsIntegrallyIndependent τ hQ hij l n m
      (by linear_combination hrel)
    exact ⟨h2, h3, h1⟩
  have hswap : pairFaceWitnessFun τ s j i f = pairFaceWitnessFun τ s i j f := by
    rw [pairFaceWitnessFun, pairFaceWitnessFun, Finset.pair_comm]
  rw [pairSig, pairSig, hswap]
  exact triptic_orbit_residue_reciprocity hWmero hWper hWmixed (hτ j) (hτ i) hindep p hℓ

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **The depth-`d` signature is the `τ k`-displacement of the depth-`(d−1)` signature.** -/
theorem pairSig_descent (τ : ι → ℂ) (hτ : ∀ m, 0 < (τ m).im)
    (hQ : PeriodsIntegrallyIndependent τ) (s : Finset ι) {i j k : ι}
    (hik : i ≠ k) (hjk : j ≠ k) (hij : i ≠ j) (hk : k ∈ s) (hi : i ∈ s) (hj : j ∈ s)
    {c₀ : ℂ} {f : ℂ → ℂ} (hmero : MeromorphicOn f (Set.univ : Set ℂ))
    (hper : PeriodicOneGerm f) (hmixed : MixedConstGermSet τ (s \ {k}) f c₀)
    {ℓ : ℤ} (hℓ : ℓ < 0) (p : ℂ) :
    pairSig τ s f i j ℓ p
      = pairSig τ (s \ {k}) f i j ℓ (p + τ k) - pairSig τ (s \ {k}) f i j ℓ p := by
  classical
  have hsdiff : (s \ ({k} : Finset ι)) \ ({i, j} : Finset ι) = s \ ({i, j, k} : Finset ι) := by
    ext m
    simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
    tauto
  have hG : pairFaceWitnessFun τ (s \ {k}) i j f
      = HTGeometry.diffCube τ (s \ ({i, j, k} : Finset ι)) f := by
    rw [pairFaceWitnessFun, hsdiff]
  have hshift : pairFaceWitnessFun τ s i j f
      = HTGeometry.shiftDiffFun (τ k) (pairFaceWitnessFun τ (s \ {k}) i j f) := by
    rw [hG]
    exact pairFaceWitnessFun_eq_shiftDiffFun τ s (Ne.symm hik) (Ne.symm hjk) hk f
  have hi' : i ∈ s \ ({k} : Finset ι) :=
    Finset.mem_sdiff.mpr ⟨hi, by simpa using hik⟩
  have hj' : j ∈ s \ ({k} : Finset ι) :=
    Finset.mem_sdiff.mpr ⟨hj, by simpa using hjk⟩
  have hWmero : MeromorphicOn (pairFaceWitnessFun τ (s \ {k}) i j f) (Set.univ : Set ℂ) :=
    meromorphicOn_diffCube τ _ hmero
  have hWper : PeriodicOneGerm (pairFaceWitnessFun τ (s \ {k}) i j f) :=
    periodicOneGerm_diffCube τ _ hper
  have hWmixed : MixedConstGerm (pairFaceWitnessFun τ (s \ {k}) i j f) (τ j) (τ i) c₀ :=
    mixedConstGerm_pairFaceWitnessFun τ (s \ {k}) hij hi' hj' hmixed
  have hindep : ∀ n m l : ℤ, (n : ℂ) * τ i + (m : ℂ) * τ j + (l : ℂ) = 0 →
      n = 0 ∧ m = 0 ∧ l = 0 := by
    intro n m l hrel
    obtain ⟨h1, h2, h3⟩ := indepPeriods_of_periodsIntegrallyIndependent τ hQ hij l m n
      (by linear_combination hrel)
    exact ⟨h3, h2, h1⟩
  have hs1 : {m : ℤ | laurentCoeff
      (fun w : ℂ => pairFaceWitnessFun τ (s \ {k}) i j f (w + τ i + τ k)
        - pairFaceWitnessFun τ (s \ {k}) i j f (w + τ k))
      (p + (m : ℂ) * τ i) ℓ ≠ 0}.Finite :=
    finite_support_orbitalDivisorTerm
      (F := fun w => pairFaceWitnessFun τ (s \ {k}) i j f (w + τ k)) (τ := τ j) (σ := τ i)
      (fun y _ => meromorphicAt_comp_add.mpr (hWmero _ (Set.mem_univ _)))
      (periodicOneGerm_comp_add hWper (τ k)) (mixedConstGerm_comp_add' hWmixed (τ k))
      (hτ j) hindep p hℓ
  have hs2 : {m : ℤ | laurentCoeff
      (fun w : ℂ => pairFaceWitnessFun τ (s \ {k}) i j f (w + τ i)
        - pairFaceWitnessFun τ (s \ {k}) i j f w)
      (p + (m : ℂ) * τ i) ℓ ≠ 0}.Finite :=
    finite_support_orbitalDivisorTerm hWmero hWper hWmixed (hτ j) hindep p hℓ
  rw [pairSig, pairSig, pairSig, hshift]
  exact additiveOrbitalDivisorAt_shiftDiffFun hWmero hs1 hs2

set_option maxHeartbeats 1600000 in
set_option synthInstance.maxHeartbeats 800000 in
/-- **The signature is additive.** -/
theorem pairSig_add (τ : ι → ℂ) (hτ : ∀ m, 0 < (τ m).im)
    (hQ : PeriodsIntegrallyIndependent τ) (s : Finset ι) {i j : ι} (hij : i ≠ j)
    (hi : i ∈ s) (hj : j ∈ s) {Cst₁ Cst₂ : ℂ} {f g : ℂ → ℂ}
    (hfmero : MeromorphicOn f (Set.univ : Set ℂ)) (hfper : PeriodicOneGerm f)
    (hfmixed : MixedConstGermSet τ s f Cst₁)
    (hgmero : MeromorphicOn g (Set.univ : Set ℂ)) (hgper : PeriodicOneGerm g)
    (hgmixed : MixedConstGermSet τ s g Cst₂) {ℓ : ℤ} (hℓ : ℓ < 0) (p : ℂ) :
    pairSig τ s (fun z => f z + g z) i j ℓ p
      = pairSig τ s f i j ℓ p + pairSig τ s g i j ℓ p := by
  classical
  have hindep : ∀ n m l : ℤ, (n : ℂ) * τ i + (m : ℂ) * τ j + (l : ℂ) = 0 →
      n = 0 ∧ m = 0 ∧ l = 0 := by
    intro n m l hrel
    obtain ⟨h1, h2, h3⟩ := indepPeriods_of_periodsIntegrallyIndependent τ hQ hij l m n
      (by linear_combination hrel)
    exact ⟨h3, h2, h1⟩
  have hFs := finite_support_orbitalDivisorTerm (F := pairFaceWitnessFun τ s i j f)
    (τ := τ j) (σ := τ i) (meromorphicOn_diffCube τ _ hfmero)
    (periodicOneGerm_diffCube τ _ hfper)
    (mixedConstGerm_pairFaceWitnessFun τ s hij hi hj hfmixed) (hτ j) hindep p hℓ
  have hGs := finite_support_orbitalDivisorTerm (F := pairFaceWitnessFun τ s i j g)
    (τ := τ j) (σ := τ i) (meromorphicOn_diffCube τ _ hgmero)
    (periodicOneGerm_diffCube τ _ hgper)
    (mixedConstGerm_pairFaceWitnessFun τ s hij hi hj hgmixed) (hτ j) hindep p hℓ
  have hsplit : pairFaceWitnessFun τ s i j (fun z => f z + g z)
      = pairFaceWitnessFun τ s i j f + pairFaceWitnessFun τ s i j g :=
    HTGeometry.diffCube_add τ _ f g
  rw [pairSig, pairSig, pairSig, hsplit,
    additiveOrbitalDivisorAt_add (F := pairFaceWitnessFun τ s i j f)
      (G := pairFaceWitnessFun τ s i j g) (meromorphicOn_diffCube τ _ hfmero)
      (meromorphicOn_diffCube τ _ hgmero) hFs hGs]

/-! ## Realizing the components through one distinguished direction -/

set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1600000 in
/-- **The components of a compatible family through one distinguished direction are realized.** -/
theorem exists_bottom_realizer (τ : ι → ℂ) (hτ : ∀ m, 0 < (τ m).im)
    (hQ : PeriodsIntegrallyIndependent τ) (s : Finset ι) {k : ι} (hk : k ∈ s) {a : ι}
    (hak : a ≠ k) (D : ι → ℤ → ℂ → ℂ) (N : ℕ)
    (hinv : ∀ i ∈ s \ {k}, ∀ ℓ : ℤ, ℓ < 0 →
      DivInvariant (tripticPeriodGroup (τ k) (τ i)) (D i ℓ))
    (hfin : ∀ i ∈ s \ {k}, ∀ ℓ : ℤ, ℓ < 0 →
      DivFiniteClasses (tripticPeriodGroup (τ k) (τ i)) (D i ℓ))
    (htop : ∀ i ∈ s \ {k}, ∀ ℓ : ℤ, ℓ < -(N : ℤ) → ∀ p, D i ℓ p = 0)
    (hcompat : ∀ i ∈ s \ {k}, ∀ j ∈ s \ {k}, ∀ ℓ : ℤ, ℓ < 0 → ∀ p : ℂ,
      (∑ᶠ n : ℤ, D i ℓ (p + (n : ℂ) * τ j)) = ∑ᶠ n : ℤ, D j ℓ (p + (n : ℂ) * τ i)) :
    ∃ (f : ℂ → ℂ) (Cst : ℂ), MeromorphicOn f (Set.univ : Set ℂ) ∧ PeriodicOneGerm f ∧
      MixedConstGermSet τ s f Cst ∧
      ∀ i ∈ s \ {k}, ∀ ℓ : ℤ, ℓ < 0 → ∀ p, pairSig τ s f i k ℓ p = D i ℓ p := by
  classical
  set Λ : AddSubgroup ℂ := lineLattice (τ k) with hΛ
  set mkq : ℂ → (ℂ ⧸ Λ) := fun z => QuotientAddGroup.mk z with hmkq
  set w : ι → (ℂ ⧸ Λ) := fun i => mkq (τ i) with hw
  have hne : ∀ i ∈ s \ ({k} : Finset ι), i ≠ k := fun i hi => by
    simpa using (Finset.mem_sdiff.mp hi).2
  have hzero_iff : ∀ y : ℂ, mkq y = 0 ↔ y ∈ Λ := by
    intro y
    constructor
    · intro h
      have : y - 0 ∈ Λ := QuotientAddGroup.eq_iff_sub_mem.mp (by simpa [hmkq] using h)
      simpa using this
    · intro h
      have h0 : mkq y = mkq 0 := QuotientAddGroup.eq_iff_sub_mem.mpr (by simpa using h)
      simpa [hmkq] using h0
  have hsmul : ∀ (n : ℤ) (i : ι), n • w i = mkq ((n : ℂ) * τ i) := by
    intro n i
    rw [hw, hmkq]
    show (n • (QuotientAddGroup.mk (τ i) : ℂ ⧸ Λ)) = QuotientAddGroup.mk ((n : ℂ) * τ i)
    rw [← QuotientAddGroup.mk_zsmul]
    congr 1
    rw [zsmul_eq_mul]
  have hwone : ∀ i ∈ s \ ({k} : Finset ι), ∀ n : ℤ, n • w i = 0 → n = 0 := by
    intro i hi n hn
    rw [hsmul] at hn
    exact lineLattice_free_single τ hQ (hne i hi) n ((hzero_iff _).mp hn)
  have hwpair : ∀ i ∈ s \ ({k} : Finset ι), ∀ j ∈ s \ ({k} : Finset ι), i ≠ j →
      ∀ n m : ℤ, n • w i + m • w j = 0 → n = 0 ∧ m = 0 := by
    intro i hi j hj hij n m hnm
    rw [hsmul, hsmul] at hnm
    have hsum : mkq ((n : ℂ) * τ i + (m : ℂ) * τ j) = 0 := by
      rw [hmkq] at hnm ⊢
      show QuotientAddGroup.mk _ = _
      rw [QuotientAddGroup.mk_add]
      exact hnm
    exact lineLattice_free_pair τ hQ (hne i hi) (hne j hj) hij n m ((hzero_iff _).mp hsum)
  have hwtriple : ∀ i ∈ s \ ({k} : Finset ι), ∀ j ∈ s \ ({k} : Finset ι),
      ∀ l ∈ s \ ({k} : Finset ι), i ≠ j → i ≠ l → j ≠ l →
      ∀ n m r : ℤ, n • w i + m • w j + r • w l = 0 → n = 0 ∧ m = 0 ∧ r = 0 := by
    intro i hi j hj l hl hij hil hjl n m r hnmr
    rw [hsmul, hsmul, hsmul] at hnmr
    have hsum : mkq ((n : ℂ) * τ i + (m : ℂ) * τ j + (r : ℂ) * τ l) = 0 := by
      rw [hmkq] at hnmr ⊢
      show QuotientAddGroup.mk _ = _
      rw [QuotientAddGroup.mk_add, QuotientAddGroup.mk_add]
      exact hnmr
    exact lineLattice_free_triple τ hQ (hne i hi) (hne j hj) (hne l hl) hij hil hjl n m r
      ((hzero_iff _).mp hsum)
  -- the descended families, order by order
  have hDinvΛ : ∀ i ∈ s \ ({k} : Finset ι), ∀ ℓ : ℤ, ℓ < 0 → DivInvariant Λ (D i ℓ) := by
    intro i hi ℓ hℓ p g hg
    refine hinv i hi ℓ hℓ p g ?_
    obtain ⟨u, v, hg'⟩ := hg
    exact ⟨u, v, 0, by rw [hg']; push_cast; ring⟩
  have key : ∀ m : ℕ, ∃ B : (ℂ ⧸ Λ) → ℂ, (∃ S : Finset (ℂ ⧸ Λ), ∀ x, B x ≠ 0 → x ∈ S) ∧
      ∀ i ∈ s \ ({k} : Finset ι), ∀ x : ℂ ⧸ Λ,
        orbitSum (w i) B x = divQuotient Λ (D i (-((m : ℤ) + 1))) x := by
    intro m
    have hDq_inv : ∀ i ∈ s \ ({k} : Finset ι), ∀ x : ℂ ⧸ Λ,
        divQuotient Λ (D i (-((m : ℤ) + 1))) (x + w i)
          = divQuotient Λ (D i (-((m : ℤ) + 1))) x := by
      intro i hi x
      have harg : x + w i = mkq (Quotient.out x + τ i) := by
        rw [hw, hmkq]
        show x + QuotientAddGroup.mk (τ i) = QuotientAddGroup.mk (Quotient.out x + τ i)
        rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq' x]
      rw [harg, divQuotient_mk (hDinvΛ i hi _ (by omega)), divQuotient]
      exact hinv i hi _ (by omega) (Quotient.out x) (τ i) ⟨0, 0, 1, by push_cast; ring⟩
    have hDq_supp : ∀ i ∈ s \ ({k} : Finset ι), ∃ S : Finset (ℂ ⧸ Λ),
        ∀ x : ℂ ⧸ Λ, divQuotient Λ (D i (-((m : ℤ) + 1))) x ≠ 0 →
          ∃ q ∈ S, ∃ n : ℤ, x = q + n • w i := by
      intro i hi
      obtain ⟨S₀, hS₀⟩ := hfin i hi (-((m : ℤ) + 1)) (by omega)
      refine ⟨S₀.image mkq, fun x hx => ?_⟩
      obtain ⟨q, hq, hmem⟩ := hS₀ (Quotient.out x) hx
      obtain ⟨u, v, r, hqr⟩ := hmem
      refine ⟨mkq q, Finset.mem_image.mpr ⟨q, hq, rfl⟩, r, ?_⟩
      have hxq : x = mkq (Quotient.out x) := (QuotientAddGroup.out_eq' x).symm
      rw [hxq, hsmul, hmkq]
      show QuotientAddGroup.mk (Quotient.out x)
        = QuotientAddGroup.mk q + QuotientAddGroup.mk ((r : ℂ) * τ i)
      rw [← QuotientAddGroup.mk_add]
      refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
      refine ⟨u, v, ?_⟩
      push_cast
      linear_combination hqr
    have hDq_comp : ∀ i ∈ s \ ({k} : Finset ι), ∀ j ∈ s \ ({k} : Finset ι), ∀ x : ℂ ⧸ Λ,
        orbitSum (w j) (divQuotient Λ (D i (-((m : ℤ) + 1)))) x
          = orbitSum (w i) (divQuotient Λ (D j (-((m : ℤ) + 1)))) x := by
      intro i hi j hj x
      have hterm : ∀ (u v : ι), u ∈ s \ ({k} : Finset ι) → ∀ n : ℤ,
          divQuotient Λ (D u (-((m : ℤ) + 1))) (x + n • w v)
            = D u (-((m : ℤ) + 1)) (Quotient.out x + (n : ℂ) * τ v) := by
        intro u v hu n
        have harg : x + n • w v = mkq (Quotient.out x + (n : ℂ) * τ v) := by
          rw [hsmul, hmkq]
          show x + QuotientAddGroup.mk ((n : ℂ) * τ v)
            = QuotientAddGroup.mk (Quotient.out x + (n : ℂ) * τ v)
          rw [QuotientAddGroup.mk_add, QuotientAddGroup.out_eq' x]
        rw [harg]
        exact divQuotient_mk (hDinvΛ u hu _ (by omega)) _
      rw [orbitSum, orbitSum, finsum_congr (fun n => hterm i j hi n),
        finsum_congr (fun n => hterm j i hj n)]
      exact hcompat i hi j hj _ (by omega) (Quotient.out x)
    obtain ⟨B, S, hS, hBprop⟩ := exists_simultaneous_lift w (s \ ({k} : Finset ι))
      hwone hwpair hwtriple (fun i => divQuotient Λ (D i (-((m : ℤ) + 1))))
      hDq_inv hDq_supp hDq_comp
    exact ⟨B, ⟨S, hS⟩, hBprop⟩
  choose Bnat hBsupp hBprop using key
  -- the lifted bottom charge
  set Bfun : ℤ → ℂ → ℂ := fun ℓ p =>
    if (-ℓ - 1).toNat < N ∧ ℓ < 0 then Bnat ((-ℓ - 1).toNat) (mkq p) else 0 with hBfun
  have hBfun_nat : ∀ m : ℕ, m < N → ∀ p : ℂ,
      Bfun (-((m : ℤ) + 1)) p = Bnat m (mkq p) := by
    intro m hm p
    have hto : (-(-((m : ℤ) + 1)) - 1).toNat = m := by
      simp only [neg_neg]
      omega
    simp only [hBfun, hto]
    rw [if_pos ⟨hm, by omega⟩]
  have hBinv : ∀ ℓ : ℤ, ℓ < 0 → ∀ p g : ℂ, g ∈ lineLattice (τ k) →
      Bfun ℓ (p + g) = Bfun ℓ p := by
    intro ℓ hℓ p g hg
    have hmk : mkq (p + g) = mkq p := by
      refine QuotientAddGroup.eq_iff_sub_mem.mpr ?_
      rw [show p + g - p = g from by ring]
      exact hg
    simp only [hBfun, hmk]
  have hBtop : ∀ ℓ : ℤ, ℓ < -(N : ℤ) → ∀ p, Bfun ℓ p = 0 := by
    intro ℓ hℓ p
    simp only [hBfun]
    rw [if_neg]
    rintro ⟨h1, -⟩
    omega
  have hBfin : ∀ ℓ : ℤ, ℓ < 0 → ∃ S : Finset ℂ, ∀ p, Bfun ℓ p ≠ 0 →
      ∃ q ∈ S, sameLine (τ k) q p := by
    intro ℓ hℓ
    by_cases hcase : (-ℓ - 1).toNat < N
    · obtain ⟨S, hS⟩ := hBsupp ((-ℓ - 1).toNat)
      refine ⟨S.image Quotient.out, fun p hp => ?_⟩
      have hne0 : Bnat ((-ℓ - 1).toNat) (mkq p) ≠ 0 := by
        intro hcon
        refine hp ?_
        simp only [hBfun]
        rw [if_pos ⟨hcase, hℓ⟩]
        exact hcon
      have hmem := hS _ hne0
      refine ⟨Quotient.out (mkq p), Finset.mem_image.mpr ⟨_, hmem, rfl⟩, ?_⟩
      show p - Quotient.out (mkq p) ∈ lineLattice (τ k)
      refine QuotientAddGroup.eq_iff_sub_mem.mp ?_
      exact (QuotientAddGroup.out_eq' (mkq p)).symm
    · refine ⟨∅, fun p hp => absurd ?_ hp⟩
      simp only [hBfun]
      rw [if_neg (fun h => hcase h.1)]
  obtain ⟨R, cc, hmatch⟩ := exists_multiAtomRealization_matching (hτ k) Bfun N hBinv hBtop hBfin
  obtain ⟨f, Cst, hfreal, hfper, hfmixed, hfbot⟩ :=
    exists_class_member_with_prescribed_bottomCharge τ hτ s hk hak N R cc
  refine ⟨f, Cst, meromorphicOn_of_realizesMero hfreal, hfper, hfmixed, ?_⟩
  intro i hi ℓ hℓ p
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, ℓ = -((m : ℤ) + 1) := ⟨(-ℓ - 1).toNat, by omega⟩
  have hbotval : ∀ q : ℂ,
      laurentCoeff (bottomWitnessFun τ s k f) q (-((m : ℤ) + 1)) = Bfun (-((m : ℤ) + 1)) q := by
    intro q
    rw [hfbot q _ (by omega), hmatch _ (by omega) q]
  rw [pairSig, additiveOrbitalDivisorAt_pairFaceWitnessFun τ s (hne i hi) (Finset.mem_sdiff.mp hi).1
    f p (-((m : ℤ) + 1)), finsum_congr (fun n : ℤ => hbotval (p + (n : ℂ) * τ i))]
  by_cases hmN : m < N
  · have hstep : ∀ n : ℤ, Bfun (-((m : ℤ) + 1)) (p + (n : ℂ) * τ i)
        = Bnat m (mkq p + n • w i) := by
      intro n
      rw [hBfun_nat m hmN]
      congr 1
      rw [hsmul, hmkq]
      show QuotientAddGroup.mk (p + (n : ℂ) * τ i)
        = QuotientAddGroup.mk p + QuotientAddGroup.mk ((n : ℂ) * τ i)
      rw [QuotientAddGroup.mk_add]
    rw [finsum_congr hstep]
    have := hBprop m i hi (mkq p)
    rw [orbitSum] at this
    rw [this, divQuotient_mk (hDinvΛ i hi _ (by omega))]
  · have hzero : ∀ n : ℤ, Bfun (-((m : ℤ) + 1)) (p + (n : ℂ) * τ i) = 0 := by
      intro n
      have hto : (-(-((m : ℤ) + 1)) - 1).toNat = m := by
        simp only [neg_neg]
        omega
      simp only [hBfun, hto]
      rw [if_neg]
      rintro ⟨h1, -⟩
      omega
    rw [finsum_congr hzero, finsum_zero]
    exact (htop i hi _ (by omega) p).symm

end

end GaloisForLFunctions
