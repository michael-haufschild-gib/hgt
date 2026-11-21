import GaloisForLFunctions.WindowedLandauTheory.SatakeDualWeyl.DefsCS
import GaloisForLFunctions.WindowedLandauTheory.HermitianLattices.ClassSetAssembly
import GaloisForLFunctions.WindowedLandauTheory.HermitianLattices.TraceReal
import GaloisForLFunctions.WindowedLandauTheory.HermitianLattices.ShortVectors
import GaloisForLFunctions.WindowedLandauTheory.HermitianLattices.FinIntermediate
import GaloisForLFunctions.WindowedLandauTheory.HermitianLattices.IsomOfTrace

noncomputable section

open NumberField

namespace WindowedLandauTheory.UG.P

theorem csBdd_nat_mul {K : Type} [Field K] [NumberField K] (d : 𝓞 K) (hd : d ≠ 0) :
    ∃ m : ℕ, 0 < m ∧ ∃ t : 𝓞 K, (m : 𝓞 K) = d * t := by
  classical
  refine ⟨Ideal.absNorm (Ideal.span {d}), ?_, ?_⟩
  · refine Nat.pos_of_ne_zero ?_
    rw [Ne, Ideal.absNorm_eq_zero_iff, Ideal.span_singleton_eq_bot]
    exact hd
  · obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.absNorm_mem (Ideal.span {d}))
    exact ⟨t, by rw [← ht, mul_comm]⟩

theorem class_set_finite_bounded_holds (hCovolOfDual : WindowedLandauTheory.UG.CS.CovolOfDual) :
    WindowedLandauTheory.UG.CS.ClassSetFiniteBdd := by
  intro K V _ _ _ _ _ _ _ _ h hsymm hpos d e hd he
  obtain ⟨N, ι, hι, hmul, hlat⟩ := WindowedLandauTheory.HermitianLatticesTheory.traceReal_main h hsymm hpos
  obtain ⟨C, hC⟩ := hCovolOfDual K V h hsymm hpos N ι hι e he
  obtain ⟨m, hm, t, ht⟩ := csBdd_nat_mul d hd
  let S : Set (Submodule (𝓞 K) V) := {M | Submodule.IsLattice K M ∧
    (∀ x ∈ M, ∀ y ∈ M, (d : K) * h x y ∈ (1 : Submodule (𝓞 K) K)) ∧
    (∀ x ∈ WindowedLandauTheory.HermitianLatticesTheory.dual h M, (e : K) • x ∈ M)}
  have hSd : ∀ M ∈ S, ∀ x ∈ M, ∀ y ∈ M, (m : K) * h x y ∈ (1 : Submodule (𝓞 K) K) := by
    intro M hM x hx y hy
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp (hM.2.1 x hx y hy)
    refine Submodule.mem_one.mpr ⟨t * a, ?_⟩
    have hmK : (m : K) = (d : K) * (t : K) := by
      have := congrArg (algebraMap (𝓞 K) K) ht
      simpa using this
    rw [map_mul, ha, hmK]
    have htc : algebraMap (𝓞 K) K t = (t : K) := rfl
    rw [htc]
    ring
  obtain ⟨s, -, hs⟩ := WindowedLandauTheory.HermitianLatticesTheory.classSetFinite_core WindowedLandauTheory.HermitianLatticesTheory.shortVectors
    WindowedLandauTheory.HermitianLatticesTheory.finIntermediate WindowedLandauTheory.HermitianLatticesTheory.isomOfTrace h hpos N ι hι hmul m hm C S hSd
    (fun M hM => hlat M hM.1) (fun M hM _ _ => hC M hM.1 hM.2.2)
  exact ⟨s, fun M hM hdM heM => hs M ⟨hM, hdM, heM⟩⟩

end WindowedLandauTheory.UG.P
