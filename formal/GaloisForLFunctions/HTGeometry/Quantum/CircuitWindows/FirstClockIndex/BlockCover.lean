import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FirstClockIndex.PairArcs
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FirstClockIndex.SecondMoment

/-! # The probability that a block of harmonics misses a phase box -/
open Set MeasureTheory
open scoped ENNReal
namespace GaloisForLFunctions.HTGeometry.FirstClockIndex
noncomputable section

local instance : IsProbabilityMeasure (volume : Measure UnitAddCircle) := ⟨UnitAddCircle.measure_univ⟩

/-- A harmonic falls in the full product of d identical phase arcs. -/
def boxHit (I : Type*) (q : ℕ) (x : ℝ) : Set (I → UnitAddCircle) :=
  univ.pi fun _ => (fun θ : UnitAddCircle => q • θ) ⁻¹' forwardUnitArc x

private theorem box_measurable {I : Type*} [Fintype I] (q : ℕ) (x : ℝ) :
    MeasurableSet (boxHit I q x) := by
  apply MeasurableSet.univ_pi
  exact fun _ => (isClosed_forwardUnitArc x).measurableSet.preimage (continuous_nsmul q).measurable

private theorem box_mass {I : Type*} [Fintype I] {q : ℕ} (hq : 0 < q) (x : Icc (0:ℝ) (1/2)) :
    volume.real (boxHit I q x) = (x:ℝ)^(Fintype.card I) := by
  rw [Measure.real,boxHit,volume_pi_pi]
  simp only [Finset.prod_const, Finset.card_univ,ENNReal.toReal_pow,
    (multiple_preserves hq).measure_preimage (isClosed_forwardUnitArc x).measurableSet.nullMeasurableSet,
    volume_forwardUnitArc x,ENNReal.toReal_ofReal x.2.1]

private theorem box_pair {I : Type*} [Fintype I] {q h : ℕ} (hq : 0 < q) (hh : 0 < h)
    {x : ℝ} (hx : 0 ≤ x) (hy : x+(h:ℝ)/q ≤ 1/2) :
    volume.real (boxHit I q x ∩ boxHit I (q+h) x) ≤ (x*(x+(h:ℝ)/q))^(Fintype.card I) := by
  let C := {θ : UnitAddCircle | q • θ ∈ forwardUnitArc x ∧ (q+h) • θ ∈ forwardUnitArc x}
  have he : boxHit I q x ∩ boxHit I (q+h) x = univ.pi (fun _ => C) := by
    ext θ
    exact ⟨fun hh i hi => ⟨hh.1 i hi,hh.2 i hi⟩,fun hh => ⟨fun i hi => (hh i hi).1,fun i hi => (hh i hi).2⟩⟩
  rw [he,Measure.real,volume_pi_pi]
  simp only [Finset.prod_const,Finset.card_univ,ENNReal.toReal_pow]
  exact pow_le_pow_left₀ ENNReal.toReal_nonneg (pair_arc_mass hq hh hx hy) _

/-- For R consecutive positive tests starting at Q, near independence in
each of d coordinates costs at most (1+R/(Qx))ᵈ. -/
theorem block_miss {I : Type*} [Fintype I] {Q R : ℕ} (hQ : 0 < Q) (hR : 0 < R)
    {x : ℝ} (hx : 0 < x) (hshort : x+(R:ℝ)/Q ≤ 1/2) :
    let d := Fintype.card I
    volume.real (⋃ i : Fin R, boxHit I (Q+i.val) x)ᶜ ≤ 1/((R:ℝ)*x^d)+((1+(R:ℝ)/Q/x)^d-1) := by
  intro d
  have hQr : 0 < (Q:ℝ) := Nat.cast_pos.mpr hQ
  have hxhalf := (le_add_of_nonneg_right (div_nonneg (Nat.cast_nonneg R) hQr.le) : x ≤ _).trans hshort
  let b := (1+(R:ℝ)/Q/x)^d
  have hb : 1 ≤ b := one_le_pow₀ (le_add_of_nonneg_right (by positivity))
  let A (i : Fin R) := boxHit I (Q+i.val) x
  have pair (i j : Fin R) (hij : i.val < j.val) : volume.real (A i ∩ A j) ≤ (x^d)^2*b := by
    let h := j.val-i.val
    have hh : 0 < h := Nat.sub_pos_of_lt hij
    have hq : 0 < Q+i.val := Nat.add_pos_left hQ _
    have he : Q+j.val=Q+i.val+h := by dsimp [h]; omega
    have hratio : (h:ℝ)/(Q+i.val:ℕ) ≤ (R:ℝ)/Q := by
      apply div_le_div₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr (show h ≤ R by dsimp [h]; omega)) hQr
        (Nat.cast_le.mpr (Nat.le_add_right Q _))
    have hz := box_pair (I := I) hq hh hx.le ((add_le_add (le_refl x) hratio).trans hshort)
    change volume.real (boxHit I (Q+i.val) x ∩ boxHit I (Q+j.val) x) ≤ _
    rw [he]
    apply hz.trans
    calc
      _ ≤ (x*(x+(R:ℝ)/Q))^d := pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_left
        (add_le_add (le_refl x) hratio) hx.le) d
      _ = _ := by
        dsimp only [b]
        rw [show x*(x+(R:ℝ)/Q)=x^2*(1+(R:ℝ)/Q/x) by field_simp,mul_pow,
          ←pow_mul,Nat.mul_comm 2 d,pow_mul]
  apply missed_block volume hR A (fun i => box_measurable _ _) (pow_pos hx d) hb
    (fun i => box_mass (Nat.add_pos_left hQ i.val) ⟨x,hx.le,hxhalf⟩)
  intro i j hij
  rcases lt_or_gt_of_ne (fun e => hij (Fin.ext e)) with hi | hj
  · exact pair i j hi
  · rw [inter_comm]
    exact pair j i hj

#print axioms block_miss
end
end GaloisForLFunctions.HTGeometry.FirstClockIndex
