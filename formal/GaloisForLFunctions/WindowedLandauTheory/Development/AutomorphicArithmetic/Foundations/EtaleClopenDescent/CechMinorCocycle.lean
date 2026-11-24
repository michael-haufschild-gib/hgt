import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.EtaleClopenDescent.WeightedCechComplex
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.SubcoverCechRestriction
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! The ordered minors of a family of rows form a weighted cocycle.
The weights are a linear combination of the columns of the family. -/

noncomputable section

open GaloisForLFunctions.HTGeometry.BorelWeil

namespace GlobalTheory.WH

/-- Take the determinant with rows in the order on the index set,
and return zero off the determinant's degree. -/
def orderedMinor {S κ : Type} [CommRing S] [LinearOrder κ] {p : ℕ}
    (rows : κ → Fin p → S) (t : Finset κ) : S :=
  if h : t.card = p then (Matrix.of fun i j => rows (t.orderEmbOfFin h i) j).det else 0

theorem map_orderedMinor {S T κ : Type} [CommRing S] [CommRing T] [LinearOrder κ]
    {p : ℕ} (f : S →+* T) (r : κ → Fin p → S) (s : Finset κ) :
    f (orderedMinor r s) = orderedMinor (fun i j => f (r i j)) s := by
  by_cases hs : s.card = p
  · rw [orderedMinor, orderedMinor, dif_pos hs, dif_pos hs, RingHom.map_det]
    rfl
  · simp only [orderedMinor, dif_neg hs, map_zero]

private theorem cubeSign_emb {κ : Type} [LinearOrder κ] (t : Finset κ) {n : ℕ}
    (h : t.card = n) (i : Fin n) :
    cubeSign t (t.orderEmbOfFin h i) = (-1 : ℤ) ^ (i : ℕ) := by
  let e := t.orderEmbOfFin h
  have he := GlobalTheory.SchemeCohomology.cechSign_orderEmbedding (R := ℤ) e Finset.univ i
  have hmap : Finset.univ.map e.toEmbedding = t := Finset.map_orderEmbOfFin_univ t h
  rw [hmap] at he
  have hI : Finset.univ.filter (· < i) = Finset.Iio i := by
    ext j
    simp
  simpa only [Int.cast_id, cechSign, belowCard, hI, Fin.card_Iio] using he

private theorem erase_emb {κ : Type} [LinearOrder κ] (t : Finset κ) {n : ℕ} (h : t.card = n + 1) (k : Fin (n + 1))
    (h' : (t.erase (t.orderEmbOfFin h k)).card = n) (a : Fin n) :
    (t.erase (t.orderEmbOfFin h k)).orderEmbOfFin h' a = t.orderEmbOfFin h (k.succAbove a) := by
  have := Finset.orderEmbOfFin_unique h' (f := fun a => t.orderEmbOfFin h (k.succAbove a))
    (fun x => Finset.mem_erase.2 ⟨fun hx => Fin.succAbove_ne k x ((t.orderEmbOfFin h).injective hx),
      Finset.orderEmbOfFin_mem _ _ _⟩)
    ((t.orderEmbOfFin h).strictMono.comp (Fin.strictMono_succAbove k))
  exact (congrFun this a).symm

private theorem orderedMinor_erase {S κ : Type} [CommRing S] [LinearOrder κ] {p : ℕ} (ρ : κ → Fin p → S) (t : Finset κ)
    (h : t.card = p + 1) (k : Fin (p + 1)) :
    orderedMinor ρ (t.erase (t.orderEmbOfFin h k)) =
      (Matrix.of fun a b => ρ (t.orderEmbOfFin h (k.succAbove a)) b).det := by
  have h' : (t.erase (t.orderEmbOfFin h k)).card = p := by
    rw [Finset.card_erase_of_mem (Finset.orderEmbOfFin_mem _ _ _), h]; rfl
  unfold orderedMinor
  rw [dif_pos h']
  congr 1
  ext a b
  simp only [Matrix.of_apply]
  rw [erase_emb t h k h' a]

private theorem ring_core {S κ : Type} [CommRing S] [LinearOrder κ] {p : ℕ} (ρ : κ → Fin p → S) (f : Fin p → S)
    (t : Finset κ) (h : t.card = p + 1) :
    ∑ i ∈ t, ((GlobalTheory.cubeSign t i : ℤ) : S) * ((∑ b, ρ i b * f b) * orderedMinor ρ (t.erase i)) = 0 := by
  set e := t.orderEmbOfFin h with he
  let A : Matrix (Fin (p + 1)) (Fin (p + 1)) S :=
    Matrix.of fun a => Fin.cons (∑ b, ρ (e a) b * f b) (ρ (e a))
  have hA : A.det = 0 := by
    have h1 := Matrix.det_updateCol_sum A 0 (Fin.cons 0 f : Fin (p + 1) → S)
    have h2 : (A.updateCol 0 fun k => ∑ i, (Fin.cons 0 f : Fin (p + 1) → S) i • A k i) = A := by
      ext a b
      refine Fin.cases ?_ (fun b => ?_) b
      · simp [A, Matrix.updateCol_apply, Fin.sum_univ_succ, mul_comm]
      · simp [A, Matrix.updateCol_apply, Fin.succ_ne_zero]
    rw [h2] at h1
    simpa using h1
  have ht : t = Finset.univ.map e.toEmbedding := by
    rw [he, Finset.map_orderEmbOfFin_univ]
  have hs : ∑ i ∈ t, ((GlobalTheory.cubeSign t i : ℤ) : S) * ((∑ b, ρ i b * f b) * orderedMinor ρ (t.erase i)) =
      ∑ k : Fin (p + 1), (((-1 : ℤ) ^ (k : ℕ) : ℤ) : S) * ((∑ b, ρ (e k) b * f b) * orderedMinor ρ (t.erase (e k))) := by
    conv_lhs => rw [show (∑ i ∈ t, ((GlobalTheory.cubeSign t i : ℤ) : S) * ((∑ b, ρ i b * f b) * orderedMinor ρ (t.erase i))) =
      ∑ i ∈ Finset.univ.map e.toEmbedding, ((GlobalTheory.cubeSign t i : ℤ) : S) * ((∑ b, ρ i b * f b) * orderedMinor ρ (t.erase i)) by
        rw [← ht]]
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [RelEmbedding.coe_toEmbedding]
    rw [he, cubeSign_emb t h k]
  rw [hs, ← hA, Matrix.det_succ_column_zero]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [he, orderedMinor_erase ρ t h k]
  have : (A.submatrix k.succAbove Fin.succ) = Matrix.of fun a b => ρ (t.orderEmbOfFin h (k.succAbove a)) b := by
    ext a b
    simp [A, he]
  rw [this]
  simp [A, he, mul_assoc]

/-- Acting by the ordered minors gives a cocycle for the weights
obtained by applying each row to a fixed column vector. -/
theorem wd_orderedMinor_eq_zero {k S E κ : Type} [Field k] [CommRing S] [Algebra k S]
    [AddCommGroup E] [Module k E] [LinearOrder κ] {p : ℕ}
    (act : S →ₐ[k] Module.End k E) (ρ : κ → Fin p → S) (f : Fin p → S) (m : E) :
    wd (fun l => act (∑ b, ρ l b * f b)) (fun s => act (orderedMinor ρ s) m) = 0 := by
  funext t
  rw [wd_apply]
  by_cases h : t.card = p + 1
  · have h0 := congrArg (fun x => act x m) (ring_core ρ f t h)
    simp only [map_zero, LinearMap.zero_apply, map_sum, LinearMap.sum_apply] at h0
    rw [Pi.zero_apply, ← h0]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← zsmul_eq_mul, map_zsmul, LinearMap.smul_apply, map_mul, Module.End.mul_apply]
  · rw [Pi.zero_apply]
    refine Finset.sum_eq_zero fun i hi => ?_
    have hc : (t.erase i).card ≠ p := by
      rw [Finset.card_erase_of_mem hi]
      have := Finset.card_pos.2 ⟨i, hi⟩
      omega
    simp [orderedMinor, hc]

end GlobalTheory.WH
