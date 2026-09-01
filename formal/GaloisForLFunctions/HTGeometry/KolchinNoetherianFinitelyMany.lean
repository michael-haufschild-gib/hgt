import GaloisForLFunctions.HTGeometry.RittRaudenbushFinitelyMany
import GaloisForLFunctions.HTGeometry.DifferentialKolchinClosure

/-!
# Kolchin Noetherianity in finitely many differential coordinates

The finite-variable Ritt--Raudenbush theorem gives ACC for radical differential ideals in
`C{y₁, ..., yₖ}` and hence DCC for Kolchin-closed subsets of finite affine differential space.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

variable {K L : Type*} [Field K] [Algebra ℚ K] [Differential K]
  [CommRing L] [IsReduced L] [Algebra K L] [Differential L] [DifferentialAlgebra K L]

attribute [local instance] differentialPolynomialOverDifferential

omit [Algebra ℚ K] [Differential K] [DifferentialAlgebra K L] in
theorem isRadical_differentialVanishingIdealOver_finite {ι : Type*} (X : Set (ι → L)) :
    (differentialVanishingIdealOver (K := K) (L := L) X).IsRadical := by
  intro P hP
  obtain ⟨n, hn⟩ := hP
  intro x hx
  have hzero : (differentialPolynomialEvalOver (K := K) x P) ^ n = 0 := by
    rw [← map_pow]
    exact hn x hx
  exact IsReduced.eq_zero _ ⟨n, hzero⟩

/-- ACC for radical differential ideals in finitely many differential indeterminates. -/
theorem acc_radicalDifferentialIdeal_fin (k : ℕ)
    (I : ℕ → Ideal (DifferentialPolynomial (Fin k) K))
    (hmono : Monotone I) (hrad : ∀ n, (I n).IsRadical)
    (hδ : ∀ n, ∀ x ∈ I n, Differential.deriv x ∈ I n) :
    ∃ N : ℕ, ∀ n, N ≤ n → I n = I N := by
  classical
  have hdir : Directed (· ≤ ·) I := hmono.directed_le
  have hmem : ∀ x, x ∈ (⨆ n, I n) ↔ ∃ n, x ∈ I n := fun x =>
    Submodule.mem_iSup_of_directed I hdir
  have hJrad : (⨆ n, I n).IsRadical := by
    intro y hy
    obtain ⟨n, hn⟩ := hy
    obtain ⟨m, hm⟩ := (hmem _).mp hn
    exact (hmem y).mpr ⟨m, hrad m ⟨n, hm⟩⟩
  have hJδ : ∀ x ∈ (⨆ n, I n), Differential.deriv x ∈ (⨆ n, I n) := by
    intro x hx
    obtain ⟨n, hn⟩ := (hmem x).mp hx
    exact (hmem _).mpr ⟨n, hδ n x hn⟩
  obtain ⟨T, hT⟩ := radDiffFG_differentialPolynomial_fin k (⨆ n, I n) hJrad hJδ
  have hTmem : ∀ t ∈ T, ∃ n, t ∈ I n := by
    intro t ht
    refine (hmem t).mp ?_
    rw [hT]
    exact subset_radicalDifferentialIdeal _ (by exact_mod_cast ht)
  choose! f hf using hTmem
  refine ⟨T.sup f, fun n hn => ?_⟩
  have hTN : ↑T ⊆ (I (T.sup f) : Set (DifferentialPolynomial (Fin k) K)) := by
    intro t ht
    have htT : t ∈ T := by exact_mod_cast ht
    exact hmono (Finset.le_sup (f := f) htT) (hf t htT)
  have hJN : (⨆ n, I n) ≤ I (T.sup f) := by
    rw [hT]
    exact radicalDifferentialIdeal_le hTN (hrad (T.sup f)) (hδ (T.sup f))
  exact le_antisymm (le_trans (le_iSup I n) hJN) (hmono hn)

/-- Ritt--Raudenbush finite generation in any finite coordinate type. -/
theorem radDiffFG_differentialPolynomial_finite {ι : Type*} [Finite ι]
    (J : Ideal (DifferentialPolynomial ι K)) (hrad : J.IsRadical)
    (hδ : ∀ x ∈ J, Differential.deriv x ∈ J) : IsRadDiffFG J := by
  obtain ⟨k, ⟨e⟩⟩ := Finite.exists_equiv_fin ι
  exact radDiffFG_of_ringEquiv (renameDifferentialEquiv (C := K) e)
    (renameDifferentialEquiv_deriv e)
    (fun L hLrad hLδ => radDiffFG_differentialPolynomial_fin k L hLrad hLδ)
    J hrad hδ

/-- ACC for radical differential ideals in any finite coordinate type. -/
theorem acc_radicalDifferentialIdeal_finite {ι : Type*} [Finite ι]
    (I : ℕ → Ideal (DifferentialPolynomial ι K))
    (hmono : Monotone I) (hrad : ∀ n, (I n).IsRadical)
    (hδ : ∀ n, ∀ x ∈ I n, Differential.deriv x ∈ I n) :
    ∃ N : ℕ, ∀ n, N ≤ n → I n = I N := by
  classical
  have hdir : Directed (· ≤ ·) I := hmono.directed_le
  have hmem : ∀ x, x ∈ (⨆ n, I n) ↔ ∃ n, x ∈ I n := fun x =>
    Submodule.mem_iSup_of_directed I hdir
  have hJrad : (⨆ n, I n).IsRadical := by
    intro y hy
    obtain ⟨n, hn⟩ := hy
    obtain ⟨m, hm⟩ := (hmem _).mp hn
    exact (hmem y).mpr ⟨m, hrad m ⟨n, hm⟩⟩
  have hJδ : ∀ x ∈ (⨆ n, I n), Differential.deriv x ∈ (⨆ n, I n) := by
    intro x hx
    obtain ⟨n, hn⟩ := (hmem x).mp hx
    exact (hmem _).mpr ⟨n, hδ n x hn⟩
  obtain ⟨T, hT⟩ := radDiffFG_differentialPolynomial_finite (⨆ n, I n) hJrad hJδ
  have hTmem : ∀ t ∈ T, ∃ n, t ∈ I n := by
    intro t ht
    refine (hmem t).mp ?_
    rw [hT]
    exact subset_radicalDifferentialIdeal _ (by exact_mod_cast ht)
  choose! f hf using hTmem
  refine ⟨T.sup f, fun n hn => ?_⟩
  have hTN : ↑T ⊆ (I (T.sup f) : Set (DifferentialPolynomial ι K)) := by
    intro t ht
    have htT : t ∈ T := by exact_mod_cast ht
    exact hmono (Finset.le_sup (f := f) htT) (hf t htT)
  have hJN : (⨆ n, I n) ≤ I (T.sup f) := by
    rw [hT]
    exact radicalDifferentialIdeal_le hTN (hrad (T.sup f)) (hδ (T.sup f))
  exact le_antisymm (le_trans (le_iSup I n) hJN) (hmono hn)

/-- DCC for Kolchin-closed subsets of finite affine differential space. -/
theorem dcc_isKolchinClosedOver_fin (k : ℕ) (X : ℕ → Set (Fin k → L))
    (hanti : Antitone X) (hclosed : ∀ n, IsKolchinClosedOver K (X n)) :
    ∃ N : ℕ, ∀ n, N ≤ n → X n = X N := by
  classical
  set I : ℕ → Ideal (DifferentialPolynomial (Fin k) K) :=
    fun n => differentialVanishingIdealOver (K := K) (L := L) (X n) with hI
  have hmono : Monotone I := by
    intro m n hmn P hP x hx
    exact hP x (hanti hmn hx)
  obtain ⟨N, hN⟩ := acc_radicalDifferentialIdeal_fin k I hmono
    (fun n => isRadical_differentialVanishingIdealOver_finite (K := K) (X n))
    (fun n P hP => differentialPolynomialOverDerivation_mem_differentialVanishingIdealOver
      (X n) hP)
  refine ⟨N, fun n hn => ?_⟩
  have hXn : kolchinClosureOver K (X n) = X n :=
    isKolchinClosedOver_iff_kolchinClosureOver_eq.mp (hclosed n)
  have hXN : kolchinClosureOver K (X N) = X N :=
    isKolchinClosedOver_iff_kolchinClosureOver_eq.mp (hclosed N)
  rw [← hXn, ← hXN, kolchinClosureOver, kolchinClosureOver]
  congr 1
  exact congrArg
    (fun J : Ideal (DifferentialPolynomial (Fin k) K) =>
      (J : Set (DifferentialPolynomial (Fin k) K))) (hN n hn)

/-- DCC for Kolchin-closed subsets in any finite coordinate type. -/
theorem dcc_isKolchinClosedOver_finite {ι : Type*} [Finite ι]
    (X : ℕ → Set (ι → L)) (hanti : Antitone X)
    (hclosed : ∀ n, IsKolchinClosedOver K (X n)) :
    ∃ N : ℕ, ∀ n, N ≤ n → X n = X N := by
  classical
  set I : ℕ → Ideal (DifferentialPolynomial ι K) :=
    fun n => differentialVanishingIdealOver (K := K) (L := L) (X n) with hI
  have hmono : Monotone I := by
    intro m n hmn P hP x hx
    exact hP x (hanti hmn hx)
  obtain ⟨N, hN⟩ := acc_radicalDifferentialIdeal_finite I hmono
    (fun n => isRadical_differentialVanishingIdealOver_finite (K := K) (X n))
    (fun n P hP => differentialPolynomialOverDerivation_mem_differentialVanishingIdealOver
      (X n) hP)
  refine ⟨N, fun n hn => ?_⟩
  have hXn : kolchinClosureOver K (X n) = X n :=
    isKolchinClosedOver_iff_kolchinClosureOver_eq.mp (hclosed n)
  have hXN : kolchinClosureOver K (X N) = X N :=
    isKolchinClosedOver_iff_kolchinClosureOver_eq.mp (hclosed N)
  rw [← hXn, ← hXN, kolchinClosureOver, kolchinClosureOver]
  congr 1
  exact congrArg
    (fun J : Ideal (DifferentialPolynomial ι K) =>
      (J : Set (DifferentialPolynomial ι K))) (hN n hn)

/-- A closed finite-coordinate differential set whose every one-point puncture is closed is
finite.  This is the DCC form of "Noetherian and discrete implies finite" and avoids installing a
global topology instance. -/
theorem finite_of_isKolchinClosedOver_of_punctures
    {F : Type*} [Field F] [Algebra K F] [Differential F] [DifferentialAlgebra K F]
    {ι : Type*} [Finite ι]
    (H : Set (ι → F)) (hHclosed : IsKolchinClosedOver K H)
    (hpuncture : ∀ x ∈ H, IsKolchinClosedOver K (H \ {x})) : H.Finite := by
  classical
  by_contra hHfinite
  have hHinfinite : H.Infinite := hHfinite
  letI : Infinite H := Set.infinite_coe_iff.mpr hHinfinite
  let f : ℕ ↪ H := Infinite.natEmbedding H
  let X : ℕ → Set (ι → F) := fun n =>
    {x | x ∈ H ∧ ∀ m < n, x ≠ (f m : H).1}
  have hanti : Antitone X := by
    intro m n hmn x hx
    exact ⟨hx.1, fun j hj => hx.2 j (lt_of_lt_of_le hj hmn)⟩
  have hclosed : ∀ n, IsKolchinClosedOver K (X n) := by
    intro n
    induction n with
    | zero => simpa [X] using hHclosed
    | succ n ih =>
        have hEq : X (n + 1) = X n ∩ (H \ {(f n : H).1}) := by
          ext x
          constructor
          · intro hx
            refine ⟨⟨hx.1, fun m hm => hx.2 m (by omega)⟩, hx.1, ?_⟩
            intro heq
            exact hx.2 n (by omega) heq
          · rintro ⟨⟨hxH, hx⟩, -, hxn⟩
            refine ⟨hxH, fun m hm => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hm with hm | rfl
            · exact hx m hm
            · exact hxn
        rw [hEq]
        have hInter := isKolchinClosedOver_sInter (K := K) (L := F)
          {X n, H \ {(f n : H).1}} (by
            intro Y hY
            rcases hY with (rfl | hY)
            · exact ih
            · have : Y = H \ {(f n : H).1} := by simpa using hY
              subst Y
              exact hpuncture (f n).1 (f n).2)
        simpa using hInter
  obtain ⟨N, hN⟩ := dcc_isKolchinClosedOver_finite X hanti hclosed
  have hstable := hN (N + 1) (by omega)
  have hfN : (f N : H).1 ∈ X N := by
    refine ⟨(f N).2, fun m hm heq => ?_⟩
    have hsub : f N = f m := Subtype.ext heq
    have hNm : N = m := f.injective hsub
    omega
  have hfNnot : (f N : H).1 ∉ X (N + 1) := by
    intro hmem
    exact hmem.2 N (by omega) rfl
  exact hfNnot (hstable ▸ hfN)

end

end GaloisForLFunctions.HTGeometry
