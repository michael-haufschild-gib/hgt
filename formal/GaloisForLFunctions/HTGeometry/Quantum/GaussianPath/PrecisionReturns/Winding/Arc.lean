import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.EmptyVisitFlux.CrossingWindows

/-! # Integer turns witnessing a scalar visit -/

open Set
namespace GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding
open EmptyVisitFlux
noncomputable section
variable {I : Type*}

/-- Relative winding based at a phase at the beginning of the covering arc.
Frequency coordinates are measured in complete turns per unit time. -/
def Anchored (w : I→ℝ) (t r : ℝ) (b : I) (z : I→ℤ) :=
  ∀ i, t*(w i-w b)-(z i:ℝ) ∈ Icc (0:ℝ) r

private theorem int_turn (k : ℤ) : (((k:ℤ):ℝ):UnitAddCircle)=0 :=
  (AddCircle.coe_eq_zero_iff (1:ℝ)).mpr ⟨k,by simp only [zsmul_eq_mul,mul_one]⟩

private theorem relative (w : I→ℝ) (t : ℝ) (i b : I) :
    ((t*(w i-w b):ℝ):UnitAddCircle)=flow w t i-flow w t b := by
  rw [mul_sub,AddCircle.coe_sub]
  rfl

theorem anchored_iff {w : I→ℝ} {t r : ℝ} (hr : 0 ≤ r) :
    flow w t∈enclosingUnitArc r ↔ ∃ b z, Anchored w t r b z := by
  constructor
  · intro h
    obtain ⟨b,hb⟩ := mem_iUnion.mp h
    have lift (i : I) : ∃ u∈Icc (0:ℝ) r, (u:UnitAddCircle)=flow w t i-flow w t b := by
      by_cases hi : i=b
      · subst i; exact ⟨0,⟨le_rfl,hr⟩,by simp⟩
      exact hb i hi
    have winding (i : I) : ∃ k : ℤ, t*(w i-w b)-(k:ℝ)∈Icc (0:ℝ) r := by
      obtain ⟨u,hu,hh⟩ := lift i
      have hz : ((t*(w i-w b)-u:ℝ):UnitAddCircle)=0 := by
        rw [AddCircle.coe_sub,relative,hh,sub_self]
      obtain ⟨k,hk⟩ := (AddCircle.coe_eq_zero_iff (1:ℝ)).mp hz
      have he : (k:ℝ)=t*(w i-w b)-u := by simpa only [zsmul_eq_mul,mul_one] using hk
      exact ⟨k,by rwa [he,sub_sub_cancel]⟩
    choose z hz using winding
    exact ⟨b,z,hz⟩
  · rintro ⟨b,z,hz⟩
    apply mem_iUnion.mpr
    refine ⟨b,fun i _ => ⟨_,hz i,?_⟩⟩
    rw [AddCircle.coe_sub,int_turn,sub_zero,relative]

/-- A common divisor of the winding coordinates produces a scalar visit
at each multiple j/d with the same scaling of the arc width. -/
theorem divide_turns {w : I→ℝ} {t r : ℝ} {b : I} {z : I→ℤ} (h : Anchored w t r b z)
    {j d : ℕ} (hd : 0 < d) (hdiv : ∀ i, (d:ℤ) ∣ z i) :
    ∃ y : I→ℤ, Anchored w ((j:ℝ)/d*t) ((j:ℝ)/d*r) b y := by
  choose u hu using hdiv
  refine ⟨fun i => (j:ℤ)*u i,?_⟩
  intro i
  have hd' := Nat.cast_pos (α:=ℝ).mpr hd
  have hscale : 0 ≤ (j:ℝ)/d := div_nonneg (Nat.cast_nonneg _) hd'.le
  have hw : (j:ℝ)/d*(t*(w i-w b)-(z i:ℝ)) =
      (j:ℝ)/d*t*(w i-w b)-(((j:ℤ)*u i:ℤ):ℝ) := by
    rw [hu i]
    push_cast
    field_simp
  exact hw ▸ (show (j:ℝ)/d*(t*(w i-w b)-(z i:ℝ))∈Icc (0:ℝ) ((j:ℝ)/d*r) from
    ⟨mul_nonneg hscale (h i).1,mul_le_mul_of_nonneg_left (h i).2 hscale⟩)

#print axioms anchored_iff
#print axioms divide_turns
end
end GaloisForLFunctions.HTGeometry.PrecisionReturns.Winding
