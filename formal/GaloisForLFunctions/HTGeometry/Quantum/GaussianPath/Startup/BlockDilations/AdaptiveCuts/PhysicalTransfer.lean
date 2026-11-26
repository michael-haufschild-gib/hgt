import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.BufferedOwners
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.PacketCount

/-! # Fixed-time Gaussian circuit probability on the selected weak seams -/

open Real MeasureTheory ProbabilityTheory Finset Set
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section
variable {n N : ℕ}

/-- Select one minimum-energy seam in each full physical buffer.
The event is measured on the original undilated coefficients. -/
def adaptiveDraw (hN : 0<N) (F E w R : ℝ) : Set (PathLabel n→ℝ) :=
  letI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  {z | let p := owners (bondLabels (n:=n) hN) z
       z∈cutBounds (cutLabels (bufferedOwner hN p)) F E w R}

/-- The probability estimate pays for one Gaussian Jacobian, with no
factor from the number of possible choices of the weak bonds. -/
theorem physical_weak_seam_mass (hN : 0<N) (r s g : ℕ) {t a w R : ℝ} (ht : 0≤t) (ha : 0≤a)
    (hw : 0≤w) (hR : 0≤R) (e F E : ℝ) {m C : ℝ} (hm : 0≤m) (hC : 0<C) :
    let b := (n+1)/(3*N)+1
    let L := 2*(3*N)
    let δ := t^2*a*((84:ℝ)*(9*((n+1)/(3*N)):ℕ)*w*R)
    let μ := Measure.pi fun _ : PathLabel n => gaussianReal 0 1
    π≤2*(t*a)*m → 2*(e+δ)+(t*a)*C*(sqrt 21+2+2*sqrt (21*(2*(r:ℝ))))<1 →
    b*m+g*(sqrt L*C)+sqrt L/C*E<F/(1+a) →
    μ.real (affordableDraw n s e t ∩ adaptiveDraw hN F E w R)*(2:ℝ)^b ≤
      (1+a)^Fintype.card (PathLabel n)*((3^g*4^(b-g):ℕ):ℝ)/(2:ℝ)^(b-2*s/(r+1)) := by
  classical
  letI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  intro b L δ μ hcross htest hfield
  let loc (p : fullBuffers n N→Fin N) := bufferedOwner hN p
  let T p := cutLabels (loc p)
  let S p (j : packetIndices n N→Bool) := T p∪selectedLabels (sites (loc p)) j
  let Z p := affordableDraw n s e t ∩ cutBounds (T p) F E w R
  have hZ p : MeasurableSet (Z p) := (measurable_affordableDraw ..).inter (measurable_cutBounds ..)
  have hc p j b k : bondLabels hN b (p b) k∈S p j := by
    apply mem_union_left
    rw [show T p=_ from bufferedOwner_cut hN p]
    exact mem_image.mpr ⟨(b,k),mem_univ _,rfl⟩
  let D := (2:ℝ)^(b-2*s/(r+1))
  let M := ((3^g*4^(b-g):ℕ):ℝ)/D
  have hD : 0<D := by dsimp only [D]; positivity
  have hcap := weakest_bond_pattern_cap (bondLabels (n:=n) hN) S hc Z hZ (le_add_of_nonneg_right ha) M
  have h := hcap (fun z => by
    let p := owners (bondLabels (n:=n) hN) z
    have ht' : t^2*a*(84*((T p).card:ℝ)*w*R)≤δ := by
      apply mul_le_mul_of_nonneg_left _ (mul_nonneg (sq_nonneg _) ha)
      apply mul_le_mul_of_nonneg_right _ hR
      apply mul_le_mul_of_nonneg_right _ hw
      exact mul_le_mul_of_nonneg_left (Nat.cast_le.mpr (cutLabel_count hN p)) (by norm_num)
    have hp := weak_partition_count (loc p) L r s g (bufferedOwner_size hN p) ht ha hw hR
      e F E hm hC hcross (lt_of_le_of_lt
        (add_le_add (mul_le_mul_of_nonneg_left (add_le_add (le_refl e) ht') zero_le_two) le_rfl) htest)
    simp only [Fintype.card_fin] at hp
    have hcount := hp hfield z
    apply (le_div_iff₀ hD).mpr
    dsimp only [D]
    exact_mod_cast hcount)
  simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat] at h
  simpa only [M,D,mul_div_assoc] using h

#print axioms physical_weak_seam_mass
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
