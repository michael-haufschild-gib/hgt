import GaloisForLFunctions.WindowedLandauTheory.ReciprocityTheory.IdeleGroups.LocalUnitFiltration
import Mathlib.Topology.Algebra.GroupWithZero

/-! Positive congruence levels form a neighbourhood basis at one in the
multiplicative group of an adic completion. -/

open IsDedekindDomain WithZero Topology Filter

namespace GlobalTheory.Reciprocity

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K]
  [Algebra R K] [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem exists_unitsLevel_subset {t : Set (v.adicCompletion K)ˣ} (ht : t ∈ 𝓝 1) :
    ∃ n : ℕ, 1 ≤ n ∧ (unitsLevel (K := K) v n : Set (v.adicCompletion K)ˣ) ⊆ t := by
  rw [Units.isEmbedding_val₀.nhds_eq_comap, Units.val_one, mem_comap] at ht
  obtain ⟨t', ht', hsub⟩ := ht
  obtain ⟨γ, hγ⟩ := Valued.mem_nhds.1 ht'
  set c := MonoidWithZeroHom.ValueGroup₀.embedding γ.1 with hc
  have hc0 : c ≠ 0 := fun h ↦ γ.ne_zero
    (MonoidWithZeroHom.ValueGroup₀.embedding_injective (h.trans (map_zero _).symm))
  refine ⟨(-(log c)).toNat + 1, by omega, fun x hx ↦ hsub (hγ ?_)⟩
  change Valued.v.restrict ((x : v.adicCompletion K) - 1) < γ.1
  rw [Valuation.restrict_lt_iff_lt_embedding, ← hc]
  refine hx.2.trans_lt (lt_of_lt_of_eq ?_ (exp_log hc0))
  rw [exp_lt_exp]
  omega

end GlobalTheory.Reciprocity
