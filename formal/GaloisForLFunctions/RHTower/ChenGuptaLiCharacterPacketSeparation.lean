/-
# Chen--Gupta--Li separated character packets

Chen--Gupta--Li Lemma 9.1 controls the same-character off-diagonal interval
kernels by ordinate separation.  This module packages a finite ordered packet
with its separation certificate and applies the existing harmonic
reciprocal-row theorem to obtain the exact logarithmic-loss row bound.

The global ordering used here is a reusable finite model.  The source's
weaker same-character-only separation will be recovered by applying this
model to individual character fibres in the next layer.

No RH, GRH, smoothness, large-value, or zero-density premise is used.
-/

import GaloisForLFunctions.RHTower.ChenGuptaLiCharacterPacketKernel
import GaloisForLFunctions.RHTower.Sieve.SeparatedRowSum

noncomputable section

namespace RHTower

/-- An ordered finite character packet.  Its ordinate sequence is extended to
all naturals so the global gap condition is closed data; the actual CGL packet
uses only the first `R` terms. -/
structure CGLGloballySeparatedPacket (q R : ℕ) where
  ordinate : ℕ → ℝ
  spacing : ℝ
  spacing_pos : 0 < spacing
  spacing_step : ∀ i : ℕ, ordinate i + spacing ≤ ordinate (i + 1)
  character : Fin R → DirichletCharacter ℂ (q + 1)

/-- The literal CGL rows carried by an ordered separated packet. -/
def cglGloballySeparatedPacketRows {q R : ℕ}
    (P : CGLGloballySeparatedPacket q R) : Fin R → CGLCharacterDyadicRowData (q + 1) :=
  fun r => { time := P.ordinate r.1, character := P.character r }

/-- The reciprocal-gap row which bounds the off-diagonal interval kernels at
the row label `r`. -/
def cglGloballySeparatedPacketReciprocalRow {q R : ℕ}
    (P : CGLGloballySeparatedPacket q R) (r : Fin R) : ℝ :=
  ∑ s ∈ (Finset.range R).erase r.1, 2 / |P.ordinate s - P.ordinate r.1|

/-- A separated CGL packet has a closed harmonic reciprocal-gap row bound.
The factor two is exactly the endpoint cost in
`norm_cglCharacterPacketIntervalKernel_le`. -/
theorem cglGloballySeparatedPacket_reciprocalRow_le {q R : ℕ}
    (P : CGLGloballySeparatedPacket q R) (r : Fin R) :
    cglGloballySeparatedPacketReciprocalRow P r ≤
      (4 / P.spacing) * ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1) := by
  have hbase := RHTower.Sieve.sum_inv_abs_dist_le P.spacing_pos P.spacing_step r.isLt
  unfold cglGloballySeparatedPacketReciprocalRow
  calc
    ∑ s ∈ (Finset.range R).erase r.1, 2 / |P.ordinate s - P.ordinate r.1| =
        2 * ∑ s ∈ (Finset.range R).erase r.1, 1 / |P.ordinate s - P.ordinate r.1| := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s hs
      ring
    _ ≤ 2 * ((2 / P.spacing) * ∑ i ∈ Finset.range R, 1 / ((i : ℝ) + 1)) := by
      exact mul_le_mul_of_nonneg_left hbase (by norm_num)
    _ = _ := by ring

/-- Exact reindexing of a reciprocal row from `range R` to the finite row
labels used by the CGL packet matrix. -/
theorem cglGloballySeparatedPacketReciprocalRow_eq_fin {q R : ℕ}
    (P : CGLGloballySeparatedPacket q R) (r : Fin R) :
    cglGloballySeparatedPacketReciprocalRow P r =
      ∑ s ∈ (Finset.univ : Finset (Fin R)).erase r,
        2 / |P.ordinate s.1 - P.ordinate r.1| := by
  let f : ℕ → ℝ := fun s => 2 / |P.ordinate s - P.ordinate r.1|
  have hselfNat : f r.1 = 0 := by
    dsimp [f]
    simp
  have hsplitNat := Finset.add_sum_erase (Finset.range R) f
    (Finset.mem_range.mpr r.isLt)
  rw [hselfNat] at hsplitNat
  have hnat : ∑ s ∈ (Finset.range R).erase r.1, f s = ∑ s ∈ Finset.range R, f s := by
    linarith [hsplitNat]
  have hselfFin : f r.1 = 0 := hselfNat
  have hsplitFin := Finset.add_sum_erase (Finset.univ : Finset (Fin R))
    (fun s : Fin R => f s.1) (Finset.mem_univ r)
  rw [hselfFin] at hsplitFin
  have hfin : ∑ s ∈ (Finset.univ : Finset (Fin R)).erase r, f s.1 = ∑ s : Fin R, f s.1 := by
    linarith [hsplitFin]
  unfold cglGloballySeparatedPacketReciprocalRow
  change (∑ s ∈ (Finset.range R).erase r.1, f s) = _
  rw [hnat, ← Fin.sum_univ_eq_sum_range f R, ← hfin]

end RHTower
