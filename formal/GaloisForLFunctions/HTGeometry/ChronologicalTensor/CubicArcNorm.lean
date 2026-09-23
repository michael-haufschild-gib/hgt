import GaloisForLFunctions.HTGeometry.ChronologicalTensor.CubicPairings

/-!
# The curved cubic observation factor

The balanced triangular probes define an explicit one-variable supremum J.
Every lost-plane observation on the entire physical complex is bounded by J.
Two fixed evaluations prove that this factor has trivial kernel. All bounds
come from inequalities and polynomial identities, with no numerical search.
-/

namespace GaloisForLFunctions.HTGeometry.ChronologicalTensor
noncomputable section
open Set


def cubicArcProbe (t : ℝ) : Fin 5 → ℝ := ![(1-t)/2,0,t,0,(1-t)/2]

def cubicArcReadout (A E t : ℝ) : ℝ := (A/4)*t*(1-t)^(2 : ℕ)+E*t^(2 : ℕ)

def cubicArcValues (A E : ℝ) : Set ℝ := (fun t => |cubicArcReadout A E t|) '' Icc 0 1

def cubicArcCapacity (A E : ℝ) : ℝ := sSup (cubicArcValues A E)

theorem cubicArcProbe_section : MapsTo cubicArcProbe (Icc 0 1) cubicProbeSection := by
  intro t ht
  rcases ht with ⟨ht0,ht1⟩
  refine ⟨?_,?_,?_,?_,?_,?_⟩
  · intro q
    fin_cases q <;> simp [cubicArcProbe] <;> linarith
  all_goals simp [cubicArcProbe] <;> ring

theorem cubicArcReadout_probe (A B C D E t : ℝ) :
    cubicReadout A B C D E (cubicArcProbe t)=cubicArcReadout A E t := by
  simp [cubicReadout,cubicArcProbe,cubicArcReadout]
  ring

theorem cubicArcValues_nonempty (A E : ℝ) : (cubicArcValues A E).Nonempty :=
  ⟨|cubicArcReadout A E 0|,0,⟨le_rfl,zero_le_one⟩,rfl⟩

theorem cubicArcValues_bddAbove (A E : ℝ) : BddAbove (cubicArcValues A E) := by
  obtain ⟨M,hM⟩ := cubicReadoutValues_bddAbove A 0 0 0 E
  refine ⟨M,?_⟩
  rintro y ⟨t,ht,rfl⟩
  apply hM
  exact ⟨cubicArcProbe t,cubicArcProbe_section ht,
    congrArg abs (cubicArcReadout_probe A 0 0 0 E t)⟩

theorem cubicArcCapacity_bounds (A E : ℝ) :
    MapsTo (fun t => |cubicArcReadout A E t|) (Icc 0 1) (Iic (cubicArcCapacity A E)) := by
  intro t ht
  exact le_csSup (cubicArcValues_bddAbove A E) ⟨t,ht,rfl⟩

theorem cubicArcCapacity_nonneg (A E : ℝ) : 0 ≤ cubicArcCapacity A E := by
  have h := cubicArcCapacity_bounds A E (show (0:ℝ) ∈ Icc 0 1 from ⟨le_rfl,zero_le_one⟩)
  simpa [cubicArcReadout] using h

theorem cubicArcCapacity_endpoint (A E : ℝ) : |E| ≤ cubicArcCapacity A E := by
  have h := cubicArcCapacity_bounds A E (show (1:ℝ) ∈ Icc 0 1 from ⟨zero_le_one,le_rfl⟩)
  simpa [cubicArcReadout] using h

theorem cubicArcCapacity_lost_bound (A E : ℝ) :
    MapsTo (fun g => |cubicReadout A 0 0 0 E g|) cubicProbeSection
      (Iic (cubicArcCapacity A E)) := by
  intro g hg
  rcases hg with ⟨hnn,hsum,h01,h12,h23,h34⟩
  change |cubicReadout A 0 0 0 E g| ≤ cubicArcCapacity A E
  by_cases hc : g 2=0
  · simpa [cubicReadout,hc] using cubicArcCapacity_nonneg A E
  have hb : g 1=0 := (mul_eq_zero.mp h12).resolve_right hc
  have hd : g 3=0 := (mul_eq_zero.mp h23).resolve_left hc
  have ha0 := hnn 0
  have hc0 := hnn 2
  have he0 := hnn 4
  have hsum' : g 0+g 2+g 4=1 := by simpa [hb,hd] using hsum
  have hc1 : g 2 ≤ 1 := by linarith
  have hprod : g 0*g 4 ≤ (1-g 2)^(2 : ℕ)/4 := by nlinarith [sq_nonneg (g 0-g 4)]
  let x := g 0*g 2*g 4
  let R := g 2*(1-g 2)^(2 : ℕ)/4
  let v := E*(g 2)^(2 : ℕ)
  let J := cubicArcCapacity A E
  have hx0 : 0 ≤ x := mul_nonneg (mul_nonneg ha0 hc0) he0
  have hxR : x ≤ R := by
    have h := mul_le_mul_of_nonneg_left hprod hc0
    dsimp [x,R]
    nlinarith only [h]
  have hv : |v| ≤ J := by
    have hc2 : (g 2)^(2 : ℕ) ≤ 1 := by nlinarith
    calc
      |v|=|E| * (g 2)^(2 : ℕ) := by simp [v,abs_mul,abs_of_nonneg hc0]
      _ ≤ |E| := by nlinarith [abs_nonneg E]
      _ ≤ J := cubicArcCapacity_endpoint A E
  have hR : |A*R+v| ≤ J := by
    have h := cubicArcCapacity_bounds A E ⟨hc0,hc1⟩
    change |cubicArcReadout A E (g 2)| ≤ J at h
    have hid : A*R+v=cubicArcReadout A E (g 2) := by
      dsimp [R,v,cubicArcReadout]
      ring
    rw [hid]
    exact h
  have hx : |A*x+v| ≤ J := by
    rcases abs_le.mp hv with ⟨hv0,hv1⟩
    rcases abs_le.mp hR with ⟨hR0,hR1⟩
    apply abs_le.mpr
    rcases le_total 0 A with hA | hA
    · have hl := mul_nonneg hA hx0
      have hu := mul_le_mul_of_nonneg_left hxR hA
      constructor <;> nlinarith only [hv0,hR1,hl,hu]
    · have hl := mul_le_mul_of_nonpos_left hxR hA
      have hu := mul_nonpos_of_nonpos_of_nonneg hA hx0
      constructor <;> nlinarith only [hR0,hv1,hl,hu]
  have hval : cubicReadout A 0 0 0 E g=A*x+v := by
    unfold cubicReadout
    rw [hsum]
    simp [hb,hd,x,v]
    ring
  rw [hval]
  exact hx


theorem cubicArcCapacity_zero : cubicArcCapacity 0 0=0 := by
  apply le_antisymm
  · apply csSup_le (cubicArcValues_nonempty 0 0)
    rintro y ⟨t,ht,rfl⟩
    simp [cubicArcReadout]
  · exact cubicArcCapacity_nonneg 0 0

theorem cubicArcCapacity_zero_iff (A E : ℝ) :
    cubicArcCapacity A E=0 ↔ A=0 ∧ E=0 := by
  constructor
  · intro h
    have hE : E=0 := abs_eq_zero.mp (le_antisymm (by
      simpa [h] using cubicArcCapacity_endpoint A E) (abs_nonneg E))
    have ht : (1/3:ℝ) ∈ Icc 0 1 := by constructor <;> linarith
    have hval := cubicArcCapacity_bounds A E ht
    have hz : cubicArcReadout A E (1/3)=0 :=
      abs_eq_zero.mp (le_antisymm (by simpa [h] using hval) (abs_nonneg _))
    rw [hE] at hz
    dsimp [cubicArcReadout] at hz
    exact ⟨by nlinarith,hE⟩
  · rintro ⟨rfl,rfl⟩
    exact cubicArcCapacity_zero

end
end GaloisForLFunctions.HTGeometry.ChronologicalTensor
