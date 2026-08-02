import GaloisForLFunctions.HTGeometry.FreeDifferentialFrechetIndependence
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Incompressibility of the jet order under differential embeddings

For a differential embedding `Φ : C⟨y₁,…,y_s⟩ → C⟨x₁,…,x_r⟩` of free differential rational
fields, the jet order of an element and the jet order of its image differ by at most a constant
depending only on the embedding:

`|ord (Φ u) - ord u| ≤ K`.

The upper bound is subadditivity of the order under the Frechet matrix product; the lower bound is
the bounded-distortion theorem for matrices with linearly independent rows over the ring of
differential operators, which replaces the right inverse of the Frechet matrix over the skew field
of rational pseudodifferential operators.

Dividing by `n` turns the two-sided bound into equality of normalized limits along any sequence,
which is the clock-speed statement.
-/

open scoped Differential
open Filter Topology

namespace GaloisForLFunctions.HTGeometry

namespace JetField

noncomputable section

universe w

variable {C : Type u} {ι : Type v} {ι' : Type w} [Field C]

/-- The jet order of an element of the free differential field: the order of its Frechet row.
It is the least jet level at which the element has a nonvanishing partial derivative. -/
def ordJet [Fintype ι] (u : JetField C ι) : ℕ := DiffOp.degVec (frechet u)

theorem ordJet_eq_zero_iff_forall [Fintype ι] (u : JetField C ι) :
    ordJet u ≤ 0 ↔ ∀ (j : ι) (m : ℕ), 0 < m → pd (j, m) u = 0 := by
  rw [ordJet, DiffOp.degVec_le_iff]
  constructor
  · intro h j m hm
    have := DiffOp.degree_le_iff.mp (h j) m hm
    rwa [coeff_frechet] at this
  · intro h j
    refine DiffOp.degree_le_iff.mpr fun m hm => ?_
    rw [coeff_frechet]
    exact h j m hm

section Embedding

variable [Algebra (JetField C ι') (JetField C ι)]
  [IsScalarTower C (JetField C ι') (JetField C ι)]

variable (hδ : ∀ u : JetField C ι', algebraMap (JetField C ι') (JetField C ι) (u′)
  = (algebraMap (JetField C ι') (JetField C ι) u)′)

include hδ

omit [IsScalarTower C (JetField C ι') (JetField C ι)] hδ in
theorem degVec_map_frechet [Fintype ι'] (u : JetField C ι') :
    DiffOp.degVec (fun i => DiffOp.map (algebraMap (JetField C ι') (JetField C ι))
      (frechet u i)) = ordJet u := by
  rw [ordJet, DiffOp.degVec, DiffOp.degVec]
  refine Finset.sup_congr rfl fun i _ => ?_
  exact DiffOp.degree_map _ (algebraMap (JetField C ι') (JetField C ι)).injective _

/-- The order of a substituted element is bounded by the order of the element plus the order of
the Frechet matrix. -/
theorem ordJet_algebraMap_le [Fintype ι] [Fintype ι'] (u : JetField C ι') :
    ordJet (algebraMap (JetField C ι') (JetField C ι) u)
      ≤ ordJet u + DiffOp.matDeg (frechetMatrix (C := C) (ι' := ι') (ι := ι)) := by
  have hchain : frechet (algebraMap (JetField C ι') (JetField C ι) u)
      = DiffOp.vecMul (fun i => DiffOp.map (algebraMap (JetField C ι') (JetField C ι))
          (frechet u i)) frechetMatrix := by
    funext j
    exact frechet_algebraMap_eq_vecMul hδ u j
  rw [ordJet, hchain]
  refine le_trans (DiffOp.degVec_vecMul_le _ _) ?_
  rw [degVec_map_frechet u]

/-- The order of an element is bounded by the order of its image plus a constant depending only on
the embedding. -/
theorem exists_ordJet_le_of_algebraMap [CharZero C] [Fintype ι] [Fintype ι'] [DecidableEq ι'] :
    ∃ B : ℕ, ∀ u : JetField C ι',
      ordJet u ≤ ordJet (algebraMap (JetField C ι') (JetField C ι) u) + B := by
  obtain ⟨B, hB⟩ := DiffOp.boundedDistortion_of_rowIndep (Fintype.card ι')
    (frechetMatrix (C := C) (ι' := ι') (ι := ι)) le_rfl (rowIndep_frechetMatrix hδ)
  refine ⟨B, fun u => ?_⟩
  have hchain : frechet (algebraMap (JetField C ι') (JetField C ι) u)
      = DiffOp.vecMul (fun i => DiffOp.map (algebraMap (JetField C ι') (JetField C ι))
          (frechet u i)) frechetMatrix := by
    funext j
    exact frechet_algebraMap_eq_vecMul hδ u j
  have h := hB (fun i => DiffOp.map (algebraMap (JetField C ι') (JetField C ι)) (frechet u i))
  rw [degVec_map_frechet u] at h
  have hrhs : ordJet (algebraMap (JetField C ι') (JetField C ι) u)
      = DiffOp.degVec (DiffOp.vecMul (fun i =>
          DiffOp.map (algebraMap (JetField C ι') (JetField C ι)) (frechet u i)) frechetMatrix) := by
    rw [ordJet, hchain]
  rw [hrhs]
  exact h

/-- **Uniform two-sided order comparison.**  A differential embedding of free differential
rational fields changes the jet order by at most a fixed additive constant. -/
theorem exists_uniform_ordJet_comparison [CharZero C] [Fintype ι] [Fintype ι'] [DecidableEq ι'] :
    ∃ K : ℕ, ∀ u : JetField C ι',
      ordJet (algebraMap (JetField C ι') (JetField C ι) u) ≤ ordJet u + K ∧
        ordJet u ≤ ordJet (algebraMap (JetField C ι') (JetField C ι) u) + K := by
  obtain ⟨B, hB⟩ := exists_ordJet_le_of_algebraMap (C := C) (ι := ι) (ι' := ι') hδ
  refine ⟨max (DiffOp.matDeg (frechetMatrix (C := C) (ι' := ι') (ι := ι))) B, fun u => ?_⟩
  constructor
  · exact le_trans (ordJet_algebraMap_le hδ u)
      (Nat.add_le_add_left (le_max_left _ _) _)
  · exact le_trans (hB u) (Nat.add_le_add_left (le_max_right _ _) _)

end Embedding

/-- A two-sided additive comparison of two integer sequences forces the same normalized limit. -/
theorem tendsto_normalized_of_bounded_diff (a b : ℕ → ℕ) (K : ℕ)
    (hab : ∀ n, a n ≤ b n + K) (hba : ∀ n, b n ≤ a n + K) {L : ℝ}
    (ha : Tendsto (fun n : ℕ => (a n : ℝ) / n) atTop (nhds L)) :
    Tendsto (fun n : ℕ => (b n : ℝ) / n) atTop (nhds L) := by
  have hK : Tendsto (fun n : ℕ => (K : ℝ) / n) atTop (nhds 0) :=
    tendsto_const_div_atTop_nhds_zero_nat (K : ℝ)
  have hupper : Tendsto (fun n : ℕ => (a n : ℝ) / n + (K : ℝ) / n) atTop (nhds (L + 0)) :=
    ha.add hK
  have hlower : Tendsto (fun n : ℕ => (a n : ℝ) / n - (K : ℝ) / n) atTop (nhds (L - 0)) :=
    ha.sub hK
  rw [add_zero] at hupper
  rw [sub_zero] at hlower
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlower hupper ?_ ?_
  · refine Eventually.of_forall fun n => ?_
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [div_sub_div_same, div_le_div_iff_of_pos_right hn']
      have : (a n : ℝ) ≤ (b n : ℝ) + K := by exact_mod_cast hab n
      linarith
  · refine Eventually.of_forall fun n => ?_
    rcases Nat.eq_zero_or_pos n with hn | hn
    · simp [hn]
    · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
      rw [← add_div, div_le_div_iff_of_pos_right hn']
      have : (b n : ℝ) ≤ (a n : ℝ) + K := by exact_mod_cast hba n
      linarith


section Tuples

variable [Algebra (JetField C ι') (JetField C ι)]
  [IsScalarTower C (JetField C ι') (JetField C ι)]

variable (hδ : ∀ u : JetField C ι', algebraMap (JetField C ι') (JetField C ι) (u′)
  = (algebraMap (JetField C ι') (JetField C ι) u)′)

include hδ

/-- **Uniform two-sided order comparison for finite tuples.**  The same constant works for every
finite tuple, the order of a tuple being the largest order of its entries. -/
theorem exists_uniform_ordJet_comparison_tuple [CharZero C] [Fintype ι] [Fintype ι']
    [DecidableEq ι'] :
    ∃ K : ℕ, ∀ (k : ℕ) (u : Fin k → JetField C ι'),
      (Finset.univ.sup fun a => ordJet (algebraMap (JetField C ι') (JetField C ι) (u a)))
          ≤ (Finset.univ.sup fun a => ordJet (u a)) + K ∧
        (Finset.univ.sup fun a => ordJet (u a))
          ≤ (Finset.univ.sup fun a => ordJet (algebraMap (JetField C ι') (JetField C ι) (u a)))
            + K := by
  obtain ⟨K, hK⟩ := exists_uniform_ordJet_comparison (C := C) (ι := ι) (ι' := ι') hδ
  refine ⟨K, fun k u => ⟨Finset.sup_le fun a _ => ?_, Finset.sup_le fun a _ => ?_⟩⟩
  · refine le_trans (hK (u a)).1 (Nat.add_le_add_right ?_ K)
    exact Finset.le_sup (f := fun a => ordJet (u a)) (Finset.mem_univ a)
  · refine le_trans (hK (u a)).2 (Nat.add_le_add_right ?_ K)
    exact Finset.le_sup
      (f := fun a => ordJet (algebraMap (JetField C ι') (JetField C ι) (u a)))
      (Finset.mem_univ a)

/-- **Dynamical corollary.**  Along the orbit of any differential endomorphism of the source
field, the intrinsic and the embedded orders differ by a constant, so the two clock speeds
agree. -/
theorem exists_uniform_orbit_comparison [CharZero C] [Fintype ι] [Fintype ι'] [DecidableEq ι']
    (σ : JetField C ι' → JetField C ι') (y : JetField C ι') :
    ∃ K : ℕ, ∀ n : ℕ,
      ordJet (algebraMap (JetField C ι') (JetField C ι) (σ^[n] y)) ≤ ordJet (σ^[n] y) + K ∧
        ordJet (σ^[n] y)
          ≤ ordJet (algebraMap (JetField C ι') (JetField C ι) (σ^[n] y)) + K := by
  obtain ⟨K, hK⟩ := exists_uniform_ordJet_comparison (C := C) (ι := ι) (ι' := ι') hδ
  exact ⟨K, fun n => hK (σ^[n] y)⟩

/-- The intrinsic and embedded clock speeds along an orbit coincide. -/
theorem tendsto_orbit_clock_speed [CharZero C] [Fintype ι] [Fintype ι'] [DecidableEq ι']
    (σ : JetField C ι' → JetField C ι') (y : JetField C ι') {L : ℝ}
    (hlim : Tendsto (fun n : ℕ => (ordJet (σ^[n] y) : ℝ) / n) atTop (nhds L)) :
    Tendsto (fun n : ℕ =>
      (ordJet (algebraMap (JetField C ι') (JetField C ι) (σ^[n] y)) : ℝ) / n) atTop (nhds L) := by
  obtain ⟨K, hK⟩ := exists_uniform_orbit_comparison hδ σ y
  exact tendsto_normalized_of_bounded_diff (fun n => ordJet (σ^[n] y))
    (fun n => ordJet (algebraMap (JetField C ι') (JetField C ι) (σ^[n] y))) K
    (fun n => (hK n).2) (fun n => (hK n).1) hlim

end Tuples

end

end JetField

end GaloisForLFunctions.HTGeometry
