import GaloisForLFunctions.HTGeometry.AllDepthCompletenessCore
import GaloisForLFunctions.HTGeometry.AllDepthBottomRealization
import GaloisForLFunctions.HTGeometry.TripticCompleteness

/-!
# All-depth pair-face completeness

A `1`-periodic meromorphic germ whose full mixed difference in `d` integrally independent
directions is constant is differentially algebraic exactly when all of its pair-face signatures
vanish.

The proof is an induction on `d`.  At `d = 2` the statement is the triptic completeness theorem.
At depth `d ≥ 3` the vanishing of the signatures at the pairs containing one distinguished
direction says exactly that the bottom charge has vanishing orbit sums in every surviving
direction; multi-directional telescoping writes the charge as a full difference cube, an atom sum
realizes that cube, and the difference of the source and the realization has trivial bottom charge,
hence lies in the depth-`(d−1)` class.  Its remaining signatures descend because a finite divisor
invariant under a translation of infinite order modulo the pair lattice vanishes.

* **`differentialAlgebraicOver_of_pairFace_eq_zero`** — the converse half;
* **`differentialAlgebraicOver_iff_pairFace_eq_zero`** — the all-depth classification.
-/

open Filter Set Topology
open scoped BigOperators Classical

namespace GaloisForLFunctions

open Bottcher HTGeometry

noncomputable section

attribute [local instance] ellipticGammaRationalBaseDomain
  ellipticGammaRationalBaseComplexAlgebraMero ellipticGammaRationalBaseComplexDifferential
  ellipticGammaRationalBaseMeroDifferential ellipticGammaRationalBaseMeroCharZero
  ellipticGammaRationalBaseComplexDifferentialAlgebra

variable {ι : Type} [Fintype ι] [DecidableEq ι]

set_option synthInstance.maxHeartbeats 800000 in
/-- **The converse half of all-depth pair-face completeness.**  A member of the all-depth
mixed-constraint class whose pair-face signatures all vanish is differentially algebraic. -/
theorem differentialAlgebraicOver_of_pairFace_eq_zero
    (τ : ι → ℂ) (hτ : ∀ k, 0 < (τ k).im) (hQ : PeriodsIntegrallyIndependent τ) :
    ∀ (n : ℕ) (s : Finset ι), s.card = n → 2 ≤ n →
      ∀ (x : meroField (Set.univ : Set ℂ)) (Cst : ℂ) (f : ℂ → ℂ), RealizesMero x f →
        PeriodicOneGerm f → MixedConstGermSet τ s f Cst →
        (∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 →
          additiveOrbitalDivisorAt (pairFaceWitnessFun τ s i j f) (τ i) p ℓ = 0) →
        DifferentialAlgebraicOver ℂ x := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hcard hn x Cst f hx hper hmixed hsig
  have hmeroF : MeromorphicOn f (Set.univ : Set ℂ) := meromorphicOn_of_realizesMero hx
  rcases eq_or_lt_of_le hn with hn2 | hn3
  · -- depth two: the triptic completeness theorem
    obtain ⟨i, j, hij, hs⟩ := Finset.card_eq_two.mp (by omega : s.card = 2)
    subst hs
    have hi : i ∈ ({i, j} : Finset ι) := Finset.mem_insert_self i {j}
    have hj : j ∈ ({i, j} : Finset ι) :=
      Finset.mem_insert_of_mem (Finset.mem_singleton_self j)
    have hwit : pairFaceWitnessFun τ ({i, j} : Finset ι) i j f = f := by
      rw [pairFaceWitnessFun, Finset.sdiff_self]
      funext z
      simp [HTGeometry.diffCube]
    have hzero : ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 → additiveOrbitalDivisorAt f (τ i) p ℓ = 0 := by
      intro p ℓ hℓ
      have hsigij := hsig i hi j hj hij p ℓ hℓ
      rwa [hwit] at hsigij
    have hpair : MixedConstGerm f (τ j) (τ i) Cst := (mixedConstGermSet_pair_iff hij).mp hmixed
    have hDAf : DifferentiallyAlgebraic (toMeromorphicNFOn f (Set.univ : Set ℂ)) :=
      (differentiallyAlgebraic_iff_additiveOrbitalDivisorAt_eq_zero
        hmeroF hper hpair (hτ j) (hτ i)
        (indepPeriods_of_periodsIntegrallyIndependent τ hQ hij)
        (linearIndependent_one_of_im_pos (hτ j)) (linearIndependent_one_of_im_pos (hτ i))
        (linearIndependent_ellipticGammaSourcePeriods_of_periodsIntegrallyIndependent τ hQ
          hij.symm)).mpr hzero
    exact differentialAlgebraicOver_complex_of_ratFunc
      (differentialAlgebraicOver_of_realizesMero hx hDAf)
  · -- depth at least three
    obtain ⟨k, hk⟩ : ∃ k, k ∈ s := Finset.card_pos.mp (by omega)
    have hcard' : (s \ {k}).card = n - 1 := by
      rw [Finset.sdiff_singleton_eq_erase, Finset.card_erase_of_mem hk, hcard]
    obtain ⟨i₀, hi₀'⟩ : ∃ i₀, i₀ ∈ s \ {k} := Finset.card_pos.mp (by omega)
    have hi₀ : i₀ ∈ s := (Finset.mem_sdiff.mp hi₀').1
    have hi₀k : i₀ ≠ k := by simpa using (Finset.mem_sdiff.mp hi₀').2
    have hVmero : MeromorphicOn (bottomWitnessFun τ s k f) (Set.univ : Set ℂ) :=
      meromorphicOn_diffCube τ _ hmeroF
    have hone : ∀ ℓ : ℤ, ∀ z : ℂ,
        laurentCoeff (bottomWitnessFun τ s k f) (z + 1) ℓ
          = laurentCoeff (bottomWitnessFun τ s k f) z ℓ :=
      fun ℓ z => laurentCoeff_bottomWitnessFun_add_one τ s k hmeroF hper z ℓ
    have htau : ∀ ℓ : ℤ, ℓ < 0 → ∀ z : ℂ,
        laurentCoeff (bottomWitnessFun τ s k f) (z + τ k) ℓ
          = laurentCoeff (bottomWitnessFun τ s k f) z ℓ :=
      fun ℓ hℓ z => laurentCoeff_bottomWitnessFun_add_tau τ s k hk hmeroF hmixed z hℓ
    have hlat : ∀ ℓ : ℤ, ℓ < 0 → ∀ z g : ℂ, g ∈ lineLattice (τ k) →
        laurentCoeff (bottomWitnessFun τ s k f) (z + g) ℓ
          = laurentCoeff (bottomWitnessFun τ s k f) z ℓ :=
      fun ℓ hℓ z g hg => laurentCoeff_lineLattice_of_periods (hone ℓ) (htau ℓ hℓ) z hg
    obtain ⟨P, hP⟩ := exists_finset_bottomCharge_pole_classes τ hτ s k hk hmeroF hper hmixed
    have hP' : ∀ z : ℂ, meromorphicOrderAt (bottomWitnessFun τ s k f) z < 0 →
        ∃ q ∈ P, sameLine (τ k) q z := by
      intro z hz
      obtain ⟨m, nn, hmem⟩ := hP z hz
      refine ⟨z - (m • (1 : ℂ) + nn • τ k), hmem, ?_⟩
      refine ⟨m, nn, ?_⟩
      simp only [zsmul_eq_mul]
      ring
    obtain ⟨N, hN⟩ := exists_order_bound_of_lineLattice_invariant hVmero hlat hP'
    -- the prescribed charge is the negative of the bottom charge
    obtain ⟨R, cc, hdist, hreal⟩ :=
      exists_multiAtomRealization_of_bottomCharge (σ := τ k) (hτ k) (s \ {k}) τ
        (fun i hi nn hmem =>
          lineLattice_free_single τ hQ (by simpa using (Finset.mem_sdiff.mp hi).2) nn hmem)
        (fun i hi j hj hij nn m hmem =>
          lineLattice_free_pair τ hQ (by simpa using (Finset.mem_sdiff.mp hi).2)
            (by simpa using (Finset.mem_sdiff.mp hj).2) hij nn m hmem)
        (fun ℓ p => (-1 : ℂ) * laurentCoeff (bottomWitnessFun τ s k f) p ℓ) N
        (fun ℓ hℓ p g hg => by rw [hlat ℓ hℓ p g hg])
        (fun ℓ hℓ p => by rw [hN ℓ hℓ p, mul_zero])
        (fun ℓ hℓ => ⟨P, fun p hp => by
          refine hP' p (meromorphicOrderAt_neg_of_laurentCoeff_ne_zero
            (hVmero p (Set.mem_univ p)) hℓ ?_)
          intro hcon
          exact hp (by rw [hcon, mul_zero])⟩)
        (fun i hi ℓ hℓ p => by
          have hik : i ≠ k := by simpa using (Finset.mem_sdiff.mp hi).2
          have hsum := additiveOrbitalDivisorAt_pairFaceWitnessFun τ s hik
            (Finset.mem_sdiff.mp hi).1 f p ℓ
          have hzero := hsig i (Finset.mem_sdiff.mp hi).1 k hk hik p ℓ hℓ
          rw [hzero] at hsum
          rw [← mul_finsum, ← hsum, mul_zero])
    have hZmero : MeromorphicOn (multiAtomRealization (τ k) N R cc) (Set.univ : Set ℂ) :=
      meromorphicOn_multiAtomRealization (hτ k) N R cc
    have hZbotmero :
        MeromorphicOn (bottomWitnessFun τ s k (multiAtomRealization (τ k) N R cc))
          (Set.univ : Set ℂ) := meromorphicOn_diffCube τ _ hZmero
    have hZbot : ∀ ℓ : ℤ, ℓ < 0 → ∀ p : ℂ,
        laurentCoeff (bottomWitnessFun τ s k (multiAtomRealization (τ k) N R cc)) p ℓ
          = (-1 : ℂ) * laurentCoeff (bottomWitnessFun τ s k f) p ℓ := by
      intro ℓ hℓ p
      rw [bottomWitnessFun, laurentCoeff_diffCube τ (s \ {k}) hZmero p ℓ]
      exact hreal ℓ hℓ p
    obtain ⟨xZ, hxZ, hxZmem⟩ := realizedDA_multiAtomRealization (hτ k) N R cc
    have hxZDA : DifferentialAlgebraicOver ℂ xZ :=
      differentialAlgebraicOver_complex_of_ratFunc ((mem_daOverRatFuncField_iff xZ).mp hxZmem)
    have hxE : RealizesMero (x + xZ) (f + multiAtomRealization (τ k) N R cc) :=
      realizesMero_add hx hxZ
    have hEmero : MeromorphicOn (f + multiAtomRealization (τ k) N R cc) (Set.univ : Set ℂ) :=
      meromorphicOn_of_realizesMero hxE
    have hZper : PeriodicOneGerm (multiAtomRealization (τ k) N R cc) :=
      periodicOneGerm_multiAtomRealization (τ k) N R cc
    have hEper : PeriodicOneGerm (f + multiAtomRealization (τ k) N R cc) := by
      intro z
      filter_upwards [hper z, hZper z] with w h1 h2
      show f (w + 1) + multiAtomRealization (τ k) N R cc (w + 1)
        = f w + multiAtomRealization (τ k) N R cc w
      rw [h1, h2]
    have hZmix : MixedConstGermSet τ s (multiAtomRealization (τ k) N R cc) 0 :=
      mixedConstGermSet_multiAtomRealization hk hi₀ hi₀k (hτ k) N R cc
    have hEmix : MixedConstGermSet τ s (f + multiAtomRealization (τ k) N R cc) Cst := by
      intro z
      filter_upwards [hmixed z, hZmix z] with w h1 h2
      have hsplit : HTGeometry.diffCube τ s (f + multiAtomRealization (τ k) N R cc) w
          = HTGeometry.diffCube τ s f w
            + HTGeometry.diffCube τ s (multiAtomRealization (τ k) N R cc) w := by
        rw [HTGeometry.diffCube_add τ s f (multiAtomRealization (τ k) N R cc)]
        rfl
      rw [hsplit, h1, h2, add_zero]
    have hbotE : ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 →
        laurentCoeff (bottomWitnessFun τ s k (f + multiAtomRealization (τ k) N R cc)) p ℓ = 0 := by
      intro p ℓ hℓ
      have hsplit : bottomWitnessFun τ s k (f + multiAtomRealization (τ k) N R cc)
          = fun z => bottomWitnessFun τ s k f z
              + bottomWitnessFun τ s k (multiAtomRealization (τ k) N R cc) z := by
        rw [bottomWitnessFun, bottomWitnessFun, bottomWitnessFun,
          HTGeometry.diffCube_add τ _ f (multiAtomRealization (τ k) N R cc)]
        rfl
      rw [hsplit, laurentCoeff_add (hVmero p (Set.mem_univ p)) (hZbotmero p (Set.mem_univ p)),
        hZbot ℓ hℓ p]
      ring
    obtain ⟨-, c₀, hEmix'⟩ := exists_mixedConstGermSet_erase_of_bottomCharge_eq_zero
      τ hτ s k hk hEmero hEper hEmix hbotE
    have hZsig : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 →
        additiveOrbitalDivisorAt
          (pairFaceWitnessFun τ s i j (multiAtomRealization (τ k) N R cc)) (τ i) p ℓ = 0 :=
      fun i hi j hj hij => pairFaceSignature_eq_zero_of_differentialAlgebraicOver
        τ hτ hQ s hij hi hj hxZ hZper hZmix hxZDA
    have hindepPair : ∀ (i j : ι), i ≠ j →
        ∀ m nn l : ℤ, (m : ℂ) * τ i + (nn : ℂ) * τ j + (l : ℂ) = 0 →
          m = 0 ∧ nn = 0 ∧ l = 0 := by
      intro i j hij m nn l hrel
      obtain ⟨h1, h2, h3⟩ := indepPeriods_of_periodsIntegrallyIndependent τ hQ hij l nn m
        (by linear_combination hrel)
      exact ⟨h3, h2, h1⟩
    have hEsigD : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 →
        additiveOrbitalDivisorAt
          (pairFaceWitnessFun τ s i j (f + multiAtomRealization (τ k) N R cc)) (τ i) p ℓ = 0 := by
      intro i hi j hj hij p ℓ hℓ
      have hsplit : pairFaceWitnessFun τ s i j (f + multiAtomRealization (τ k) N R cc)
          = pairFaceWitnessFun τ s i j f
            + pairFaceWitnessFun τ s i j (multiAtomRealization (τ k) N R cc) := by
        rw [pairFaceWitnessFun, pairFaceWitnessFun, pairFaceWitnessFun,
          HTGeometry.diffCube_add τ _ f (multiAtomRealization (τ k) N R cc)]
      have hAs := finite_support_orbitalDivisorTerm
        (F := pairFaceWitnessFun τ s i j f) (τ := τ j) (σ := τ i)
        (meromorphicOn_diffCube τ _ hmeroF) (periodicOneGerm_diffCube τ _ hper)
        (mixedConstGerm_pairFaceWitnessFun τ s hij hi hj hmixed) (hτ j)
        (hindepPair i j hij) p hℓ
      have hBs := finite_support_orbitalDivisorTerm
        (F := pairFaceWitnessFun τ s i j (multiAtomRealization (τ k) N R cc))
        (τ := τ j) (σ := τ i)
        (meromorphicOn_diffCube τ _ hZmero) (periodicOneGerm_diffCube τ _ hZper)
        (mixedConstGerm_pairFaceWitnessFun τ s hij hi hj hZmix) (hτ j)
        (hindepPair i j hij) p hℓ
      rw [hsplit, additiveOrbitalDivisorAt_add
        (F := pairFaceWitnessFun τ s i j f)
        (G := pairFaceWitnessFun τ s i j (multiAtomRealization (τ k) N R cc))
        (meromorphicOn_diffCube τ _ hmeroF)
        (meromorphicOn_diffCube τ _ hZmero) hAs hBs, hsig i hi j hj hij p ℓ hℓ,
        hZsig i hi j hj hij p ℓ hℓ, add_zero]
    have hEsig' : ∀ i ∈ s \ {k}, ∀ j ∈ s \ {k}, i ≠ j → ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 →
        additiveOrbitalDivisorAt
          (pairFaceWitnessFun τ (s \ {k}) i j (f + multiAtomRealization (τ k) N R cc))
          (τ i) p ℓ = 0 := by
      intro i hi' j hj' hij p ℓ hℓ
      have hi : i ∈ s := (Finset.mem_sdiff.mp hi').1
      have hj : j ∈ s := (Finset.mem_sdiff.mp hj').1
      have hik : i ≠ k := by simpa using (Finset.mem_sdiff.mp hi').2
      have hjk : j ≠ k := by simpa using (Finset.mem_sdiff.mp hj').2
      have hsdiff : (s \ ({k} : Finset ι)) \ {i, j} = s \ {i, j, k} := by
        ext m
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton]
        tauto
      have hG : pairFaceWitnessFun τ (s \ {k}) i j (f + multiAtomRealization (τ k) N R cc)
          = HTGeometry.diffCube τ (s \ {i, j, k}) (f + multiAtomRealization (τ k) N R cc) := by
        rw [pairFaceWitnessFun, hsdiff]
      have hshift : pairFaceWitnessFun τ s i j (f + multiAtomRealization (τ k) N R cc)
          = HTGeometry.shiftDiffFun (τ k)
              (pairFaceWitnessFun τ (s \ {k}) i j (f + multiAtomRealization (τ k) N R cc)) := by
        rw [hG]
        exact pairFaceWitnessFun_eq_shiftDiffFun τ s (Ne.symm hik) (Ne.symm hjk) hk _
      refine orbitalDivisor_eq_zero_of_shiftDiff_orbitalDivisor_eq_zero
        (G := pairFaceWitnessFun τ (s \ {k}) i j (f + multiAtomRealization (τ k) N R cc))
        (σ := τ i) (τ := τ j) (t := τ k)
        (meromorphicOn_diffCube τ _ hEmero) (periodicOneGerm_diffCube τ _ hEper)
        (mixedConstGerm_pairFaceWitnessFun τ (s \ {k}) hij hi' hj' hEmix') (hτ j)
        (hindepPair i j hij) (tripticPeriodGroup_free τ hQ hik hjk) hℓ ?_ p
      intro q
      rw [← hshift]
      exact hEsigD i hi j hj hij q ℓ hℓ
    have hxEDA : DifferentialAlgebraicOver ℂ (x + xZ) :=
      ih (n - 1) (by omega) (s \ {k}) hcard' (by omega) (x + xZ) c₀
        (f + multiAtomRealization (τ k) N R cc) hxE hEper hEmix' hEsig'
    have hxeq : x = (x + xZ) - xZ := by ring
    rw [hxeq]
    exact differentialAlgebraicOver_sub hxEDA hxZDA

set_option synthInstance.maxHeartbeats 800000 in
/-- **All-depth pair-face completeness.**  A `1`-periodic meromorphic germ with constant full mixed
difference in a family of integrally independent directions is differentially algebraic exactly
when every pair-face signature vanishes. -/
theorem differentialAlgebraicOver_iff_pairFace_eq_zero
    (τ : ι → ℂ) (hτ : ∀ k, 0 < (τ k).im) (hQ : PeriodsIntegrallyIndependent τ)
    (s : Finset ι) (hs : 2 ≤ s.card)
    {x : meroField (Set.univ : Set ℂ)} {Cst : ℂ} {f : ℂ → ℂ} (hx : RealizesMero x f)
    (hper : PeriodicOneGerm f) (hmixed : MixedConstGermSet τ s f Cst) :
    DifferentialAlgebraicOver ℂ x ↔
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 →
        additiveOrbitalDivisorAt (pairFaceWitnessFun τ s i j f) (τ i) p ℓ = 0 := by
  constructor
  · intro hDA i hi j hj hij
    exact pairFaceSignature_eq_zero_of_differentialAlgebraicOver τ hτ hQ s hij hi hj hx hper
      hmixed hDA
  · intro hsig
    exact differentialAlgebraicOver_of_pairFace_eq_zero τ hτ hQ s.card s rfl hs x Cst f hx hper
      hmixed hsig

set_option synthInstance.maxHeartbeats 800000 in
/-- **All-depth pair-face completeness on the full parameter family.** -/
theorem differentialAlgebraicOver_iff_pairFace_univ
    (τ : ι → ℂ) (hτ : ∀ k, 0 < (τ k).im) (hQ : PeriodsIntegrallyIndependent τ)
    (hs : 2 ≤ Fintype.card ι)
    {x : meroField (Set.univ : Set ℂ)} {Cst : ℂ} {f : ℂ → ℂ} (hx : RealizesMero x f)
    (hper : PeriodicOneGerm f)
    (hmixed : MixedConstGermSet τ (Finset.univ : Finset ι) f Cst) :
    DifferentialAlgebraicOver ℂ x ↔
      ∀ i j : ι, i ≠ j → ∀ (p : ℂ) (ℓ : ℤ), ℓ < 0 →
        additiveOrbitalDivisorAt (pairFaceWitnessFun τ (Finset.univ : Finset ι) i j f)
          (τ i) p ℓ = 0 := by
  rw [differentialAlgebraicOver_iff_pairFace_eq_zero τ hτ hQ (Finset.univ : Finset ι)
    (by simpa using hs) hx hper hmixed]
  constructor
  · intro h i j hij
    exact h i (Finset.mem_univ i) j (Finset.mem_univ j) hij
  · intro h i _ j _ hij
    exact h i j hij

end

end GaloisForLFunctions
