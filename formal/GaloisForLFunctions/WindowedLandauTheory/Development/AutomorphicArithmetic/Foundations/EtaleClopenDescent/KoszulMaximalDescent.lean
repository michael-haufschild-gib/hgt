import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.KoszulWeaklyRegular
import GaloisForLFunctions.HTGeometry.PointsSeparate

/-! A local Koszul primitive clears one denominator for the whole
cochain. If there is such a denominator outside each maximal ideal,
the cochain has a primitive over the original lattice. -/

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace GlobalTheory.WH

variable {R V ι : Type*} [CommRing R] [LinearOrder ι] [Fintype ι]
  [AddCommGroup V] [Module R V]
  {P Q : Submodule R V} (r : ι → R) {n : ℤ}

/-- Clear the denominators of a primitive in an enlarged lattice. -/
theorem exists_koszul_primitive_after_denominator (hPQ : P ≤ Q) (S : Submonoid R)
    (hS : ∀ v : Q, ∃ s : S, (s : R) • (v : V) ∈ P)
    (a : Finset ι → P) (b : Finset ι → Q)
    (hb : ∀ I, (I.card : ℤ) ≠ n - 1 → b I = 0)
    (hdb : koszulDifferential r b = fun I => Submodule.inclusion hPQ (a I)) :
    ∃ s : S, ∃ c : Finset ι → P, (∀ I, (I.card : ℤ) ≠ n - 1 → c I = 0) ∧
      koszulDifferential r c = (s : R) • a := by
  classical
  choose s hs using fun I => hS (b I)
  let u : S := ∏ I, s I
  have hu (I : Finset ι) : (u : R) • (b I : V) ∈ P := by
    have hprod : s I * (∏ J ∈ Finset.univ.erase I, s J) = u :=
      Finset.mul_prod_erase Finset.univ s (Finset.mem_univ I)
    rw [← hprod, Submonoid.coe_mul, mul_comm, mul_smul]
    exact P.smul_mem _ (hs I)
  let c (I : Finset ι) : P := ⟨(u : R) • (b I : V), hu I⟩
  refine ⟨u, c, ?_, ?_⟩
  · intro I hI
    apply Subtype.ext
    change (u : R) • (b I : V) = 0
    rw [hb I hI, Submodule.coe_zero, smul_zero]
  · let f := Submodule.inclusion hPQ
    have hfc : (fun I => f (c I)) = (u : R) • b := funext fun I => Subtype.ext rfl
    funext I
    apply Submodule.inclusion_injective hPQ
    have he : f (koszulDifferential r c I) = koszulDifferential r (fun I => f (c I)) I := by
      simp only [koszulDifferential_apply, map_sum, map_zsmul, map_smul]
    rw [he, hfc, map_smul, hdb, Pi.smul_apply, Pi.smul_apply, map_smul]

omit [Fintype ι] in
/-- A denominator outside every maximal ideal suffices to descend
the primitive to the original ring. -/
theorem exists_koszul_primitive_of_maximal (a : Finset ι → P)
    (h : ∀ m : Ideal R, m.IsMaximal → ∃ s : R, s ∉ m ∧ ∃ b : Finset ι → P,
      (∀ I, (I.card : ℤ) ≠ n - 1 → b I = 0) ∧ koszulDifferential r b = s • a) :
    ∃ b : Finset ι → P, (∀ I, (I.card : ℤ) ≠ n - 1 → b I = 0) ∧ koszulDifferential r b = a := by
  let J : Submodule R (Finset ι → P) :=
    Submodule.pi Set.univ fun I => if (I.card : ℤ) = n - 1 then ⊤ else ⊥
  let f : R →ₗ[R] (Finset ι → P) := (LinearMap.id : R →ₗ[R] R).smulRight a
  let B : Ideal R := (J.map (koszulDifferential r)).comap f
  have hb : B = ⊤ := by
    by_contra hh
    obtain ⟨m, hm, hBm⟩ := Ideal.exists_le_maximal B hh
    obtain ⟨s, hs, b, hb, hdb⟩ := h m hm
    apply hs (hBm ?_)
    refine ⟨b, Submodule.mem_pi.mpr (fun I _ => ?_), hdb⟩
    split_ifs with hI
    · exact Submodule.mem_top
    · exact (Submodule.mem_bot R).mpr (hb I hI)
  have h1 : (1 : R) ∈ B := by
    rw [hb]
    exact Submodule.mem_top
  obtain ⟨b, hb, hdb⟩ := h1
  refine ⟨b, fun I hI => (Submodule.mem_bot R).mp ?_, ?_⟩
  · simpa only [if_neg hI] using Submodule.mem_pi.mp hb I (Set.mem_univ I)
  · exact hdb.trans (one_smul R a)

omit [Fintype ι] in
/-- Over a finite type algebra with algebraically closed ground
field, rational evaluations test all maximal ideals. -/
theorem exists_koszul_primitive_of_evaluations {k : Type*} [Field k] [IsAlgClosed k]
    [Algebra k R] [Algebra.FiniteType k R] (a : Finset ι → P)
    (h : ∀ e : R →ₐ[k] k, ∃ s : R, e s ≠ 0 ∧ ∃ b : Finset ι → P,
      (∀ I, (I.card : ℤ) ≠ n - 1 → b I = 0) ∧ koszulDifferential r b = s • a) :
    ∃ b : Finset ι → P, (∀ I, (I.card : ℤ) ≠ n - 1 → b I = 0) ∧ koszulDifferential r b = a := by
  refine exists_koszul_primitive_of_maximal r a (fun m hm => ?_)
  letI := hm
  obtain ⟨e, he⟩ := exists_algHom_ker_eq_of_isMaximal (C := k) m
  obtain ⟨s, hs, b, hb, hdb⟩ := h e
  exact ⟨s, fun hs' => hs ((he s).mpr hs'), b, hb, hdb⟩

end GlobalTheory.WH
