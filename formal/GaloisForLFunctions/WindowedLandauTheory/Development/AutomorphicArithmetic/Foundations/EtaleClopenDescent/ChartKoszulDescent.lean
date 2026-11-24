import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.LocalChartFormLattice
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.KoszulMaximalDescent
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.KoszulLatticeExact
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.JoinedCechColumnExact
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.AffineCoverRationalForms

/-! Local primitives on all rational points of a finite-type chart
descend to a primitive with regular chart coefficients. -/

noncomputable section

open GlobalTheory.CechDR GlobalTheory.PD
open scoped GlobalTheory.CechDR GlobalTheory.SchemeCohomology

namespace GlobalTheory.WH

variable {k L ι : Type} [Field k] [IsAlgClosed k] [Field L] [Algebra k L]
  [LinearOrder ι] [Fintype ι] (B : Subalgebra k L) [Algebra.FiniteType k B]
  (p : ℕ) (r : ι → B) {m : ℤ}

local notation "w" => fun i => Algebra.lsmul k k (DR k L) (r i : L)

/-- A cochain with a regular local primitive at each rational
evaluation has a primitive on the chart. -/
theorem chartKoszul_mem_boundaries_of_local (a : Finset ι → DR k L)
    (ha : a ∈ (acx (fun _ => omB k L B p) w).C m)
    (h : ∀ e : B →ₐ[k] k, a ∈ (acx (fun _ => omB k L (loc B e) p) w).B m) :
    a ∈ (acx (fun _ => omB k L B p) w).B m := by
  let P := chartFormLattice B p
  letI : Module B P := Submodule.module P
  have hsmul (x : B) (v : DR k L) : x • v = (x : L) • v := rfl
  have hP (I : Finset ι) : a I ∈ P := by
    have hm := acx_mem_terms_iff.mp ha I
    split_ifs at hm
    · exact hm
    · rw [(Submodule.mem_bot k).mp hm]
      exact zero_mem _
  let c (I : Finset ι) : P := ⟨a I, hP I⟩
  have hlocal (e : B →ₐ[k] k) :
      ∃ s : B, e s ≠ 0 ∧ ∃ b : Finset ι → P,
        (∀ I, (I.card : ℤ) ≠ m - 1 → b I = 0) ∧
        koszulDifferential r b = fun I => SMul.smul s (c I) := by
    let C := loc B e
    let Q : Submodule B (DR k L) :=
      { __ := (omB k L C p).toAddSubmonoid
        smul_mem' := fun x v hv => by
          change (x : L) • v ∈ omB k L C p
          have hx : (x : L) ∈ C := (le_loc B e) x.property
          exact smul_mem_omB (B := C) (p := p) hx hv }
    have hPQ : P ≤ Q := by
      intro v hv
      exact omB_mono (le_loc B e) p hv
    let S := (RingHom.ker e.toRingHom).primeCompl
    obtain ⟨v, hv, hd⟩ := h e
    have hQ (I : Finset ι) : v I ∈ Q := by
      have hm := acx_mem_terms_iff.mp hv I
      split_ifs at hm
      · exact hm
      · rw [(Submodule.mem_bot k).mp hm]
        exact zero_mem _
    let z (I : Finset ι) : Q := ⟨v I, hQ I⟩
    have hz (I : Finset ι) (hI : (I.card : ℤ) ≠ m - 1) : z I = 0 :=
      Subtype.ext ((Submodule.mem_bot k).mp (by
        simpa only [if_neg hI] using acx_mem_terms_iff.mp hv I))
    have hzD : koszulDifferential r z = fun I => Submodule.inclusion hPQ (c I) := by
      funext I
      apply Subtype.ext
      have he := congrFun hd I
      change wd w v I = a I at he
      rw [wd_apply] at he
      change (↑(koszulDifferential r z I : Q) : DR k L) = a I
      rw [koszulDifferential_apply]
      simpa only [Algebra.lsmul_apply, Submodule.coe_sum, Submodule.coe_smul,
        Submodule.coe_smul_of_tower, hsmul, z, Submodule.coe_mk] using he
    have hden (u : Q) : ∃ s : S, (s : B) • (u : DR k L) ∈ P :=
      exists_chartForm_denominator B p e u u.property
    obtain ⟨s, b, hb, hdb⟩ :=
      exists_koszul_primitive_after_denominator (n := m) r hPQ S hden c z hz hzD
    exact ⟨s, s.property, b, hb, hdb⟩
  obtain ⟨b, hb, hdb⟩ :=
    exists_koszul_primitive_of_evaluations (k := k) (n := m) r c hlocal
  refine ⟨fun I => (b I : DR k L), acx_mem_terms_iff.mpr fun I => ?_, ?_⟩
  · split_ifs with hI
    · exact (b I).property
    · rw [hb I hI, Submodule.coe_zero]
      exact zero_mem _
  · change wd w (fun I => (b I : DR k L)) = a
    funext I
    have he := congrArg (fun x : Finset ι → P => (x I : DR k L)) hdb
    change (↑(koszulDifferential r b I : P) : DR k L) = a I at he
    rw [wd_apply]
    rw [koszulDifferential_apply] at he
    simpa only [Algebra.lsmul_apply, Submodule.coe_sum, Submodule.coe_smul,
      Submodule.coe_smul_of_tower, hsmul] using he

end GlobalTheory.WH
