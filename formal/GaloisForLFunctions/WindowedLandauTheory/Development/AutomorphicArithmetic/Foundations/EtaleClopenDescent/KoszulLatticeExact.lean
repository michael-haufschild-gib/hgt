import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.KoszulWeaklyRegular

/-! The Koszul differential on an invariant lattice computes the
augmented weighted Čech complex with that lattice in every component. -/

noncomputable section

open GlobalTheory.CechDR

namespace GlobalTheory.WH

variable {k R ι V : Type*} [Field k] [CommRing R] [Algebra k R] [LinearOrder ι]
  [AddCommGroup V] [Module k V] [Module R V] [IsScalarTower k R V]

/-- Extending the coefficients of the weights through a scalar tower
does not change the Koszul differential on the same cochains. -/
theorem koszulDifferential_algebraMap {S : Type*} [CommRing S] [Algebra R S]
    [Module S V] [IsScalarTower R S V] (r : ι → R) (a : Finset ι → V) :
    koszulDifferential (fun i => algebraMap R S (r i)) a = koszulDifferential r a := by
  funext s
  simp only [koszulDifferential_apply, IsScalarTower.algebraMap_smul]

/-- Exactness on lattice-valued Koszul cochains gives exactness
in the associated weighted Čech complex on the ambient module. -/
theorem acx_lattice_exact (P : Submodule R V) (r : ι → R) (n : ℤ)
    (hex : ∀ a : Finset ι → P, (∀ t : Finset ι, (t.card : ℤ) ≠ n → a t = 0) →
      koszulDifferential r a = 0 → ∃ b : Finset ι → P,
        (∀ t : Finset ι, (t.card : ℤ) ≠ n - 1 → b t = 0) ∧ koszulDifferential r b = a) :
    let C := acx (fun _ => P.restrictScalars k) (fun i => Algebra.lsmul k k V (r i))
    C.Z n ≤ C.B n := by
  intro C c hc
  have hc' (s : Finset ι) : c s ∈ (if (s.card : ℤ) = n then P.restrictScalars k else ⊥) :=
    Submodule.mem_pi.mp hc.1 s (Set.mem_univ _)
  have hP (s : Finset ι) : c s ∈ P := by
    have h := hc' s
    split_ifs at h
    · exact h
    · rw [(Submodule.mem_bot k).mp h]
      exact zero_mem _
  let a (s : Finset ι) : P := ⟨c s, hP s⟩
  have ha (s : Finset ι) (hs : (s.card : ℤ) ≠ n) : a s = 0 :=
    Subtype.ext ((Submodule.mem_bot k).mp (by simpa only [if_neg hs] using hc' s))
  have hza : koszulDifferential r a = 0 := by
    funext s
    apply Subtype.ext
    have e : wd (fun i => Algebra.lsmul k k V (r i)) c = 0 := hc.2
    have h := congrFun e s
    rw [wd_apply, Pi.zero_apply] at h
    change ((koszulDifferential r a s : P) : V) = 0
    rw [koszulDifferential_apply]
    simpa only [Algebra.lsmul_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower,
      Submodule.coe_smul, a, Submodule.coe_mk] using h
  obtain ⟨b, hb, hdb⟩ := hex a ha hza
  refine ⟨fun s => (b s : V), Submodule.mem_pi.mpr (fun s _ => ?_), ?_⟩
  · change (b s : V) ∈ (if (s.card : ℤ) = n - 1 then P.restrictScalars k else ⊥)
    split_ifs with hs
    · exact (b s).property
    · rw [hb s hs]
      exact zero_mem _
  · change wd (fun i => Algebra.lsmul k k V (r i)) (fun s => (b s : V)) = c
    funext s
    have h := congrArg (fun u : Finset ι → P => (u s : V)) hdb
    change ((koszulDifferential r b s : P) : V) = c s at h
    rw [koszulDifferential_apply] at h
    rw [wd_apply]
    simpa only [Algebra.lsmul_apply, Submodule.coe_sum, Submodule.coe_smul_of_tower,
      Submodule.coe_smul] using h

/-- Restricting coefficients of the Koszul complex to an invariant
lattice preserves the exactness coming from a weakly regular sequence. -/
theorem acx_lattice_exact_of_weaklyRegular (P : Submodule R V) (r : ι → R)
    (l : List R) (hl : ∀ g ∈ l, g ∈ Ideal.span (Set.range r))
    (hreg : RingTheory.Sequence.IsWeaklyRegular P l) (n : ℤ) (hn : n < l.length) :
    let C := acx (fun _ => P.restrictScalars k) (fun i => Algebra.lsmul k k V (r i))
    C.Z n ≤ C.B n :=
  acx_lattice_exact P r n (koszul_exact_of_weaklyRegular r l hl P hreg n hn)

end GlobalTheory.WH
