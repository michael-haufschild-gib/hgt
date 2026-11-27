import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.BufferedCount
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.BlockDilations.AdaptiveCuts.PhysicalDraw

/-! # Fixed-time Gaussian circuit probability on the selected weak seams -/

open Real MeasureTheory ProbabilityTheory Finset Set
namespace GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
noncomputable section
variable {n N : ℕ}

private theorem selected_minimum {ι I B : Type*} [Fintype I] [Nonempty I] [LinearOrder I]
    (L : B→I→Fin 9→ι) (z : ι→ℝ) : z∈ownerCell L (owners L z) :=
  (ownerCell_iff L (owners L z) z).mpr rfl

/-- The probability estimate pays for one Gaussian Jacobian, with no
factor from the number of possible choices of the weak bonds. -/
theorem physical_weak_seam_mass (hN : 0<N) (r s g : ℕ) {t a w R : ℝ} (ht : 0≤t) (ha : 0≤a)
    (hw : 0≤w) (hR : 0≤R) (e F E : ℝ) {m C : ℝ} (hm : 0 ≤ m) (hC : 0<C) :
    let b := (n+1)/(3*N)+1
    let L := 2*(3*N)
    let δ := t^2*a*((84:ℝ)*(9*((n+1)/(3*N)):ℕ)*w*R)
    let μ := Measure.pi fun _ : PathLabel n => gaussianReal 0 1
    π≤2*(t*a)*m → 2*(e+δ)+(t*a)*C*(sqrt 21+2+2*sqrt (21*(2*(r:ℝ))))<1 →
    b*m+g*(sqrt L*C)+sqrt L/C*E<F/(1+a) →
    μ.real (affordableDraw n s e t ∩ adaptiveDraw (n:=n) hN F E w R)*(2:ℝ)^b ≤
      (1+a)^Fintype.card (PathLabel n)*((3^g*4^(b-g):ℕ):ℝ)/(2:ℝ)^(b-2*s/(r+1)) := by
  classical
  letI : Nonempty (Fin N) := ⟨⟨0,hN⟩⟩
  intro b L δ μ hcross htest hfield
  let S := bufferedMask (n:=n) hN
  let Z := bufferedFit (n:=n) hN s e t F E w R
  have hZ p : MeasurableSet (Z p) := (measurable_affordableDraw ..).inter (measurable_cutBounds ..)
  have hc p j b k : bondLabels (n:=n) hN b (p b) k∈S p j := by
    apply Finset.mem_union_left
    rw [bufferedOwner_cut (n:=n) hN p]
    exact Finset.mem_image.mpr ⟨(b,k),Finset.mem_univ _,rfl⟩
  let M := ((3^g*4^(b-g):ℕ):ℝ)/(2:ℝ)^(b-2*s/(r+1))
  have h := weakest_bond_pattern_cap (bondLabels (n:=n) hN) S hc Z hZ
    (le_add_of_nonneg_right ha) M fun z => by
      have hb := buffered_count (n:=n) hN (owners (bondLabels (n:=n) hN) z)
        r s g ht ha hw hR e F E hm hC hcross htest hfield z
      refine le_trans ?_ hb
      apply Nat.cast_le.mpr
      apply Finset.card_le_card
      intro j hj
      simpa only [Finset.mem_filter,Finset.mem_univ,true_and,S,Z] using hj
  have hsub : affordableDraw n s e t ∩ adaptiveDraw (n:=n) hN F E w R ⊆
      {z | z∈Z (owners (bondLabels (n:=n) hN) z)} := by
    intro z hz
    exact ⟨hz.1,adaptive_cut_bounds hN hw F E R z (owners (bondLabels (n:=n) hN) z)
      (selected_minimum _ _) hz.2⟩
  have hJ : (Fintype.card (packetIndices n N→Bool):ℝ)=(2:ℝ)^b := by
    simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin,Nat.cast_pow,Nat.cast_ofNat,b]
  calc
    _ ≤ μ.real {z | z∈Z (owners (bondLabels (n:=n) hN) z)} * (2:ℝ)^b :=
      mul_le_mul_of_nonneg_right (measureReal_mono (μ:=μ) hsub (measure_ne_top _ _)) (by positivity)
    _ = μ.real {z | z∈Z (owners (bondLabels (n:=n) hN) z)} *
        (Fintype.card (packetIndices n N→Bool):ℝ) := congrArg (_ * ·) hJ.symm
    _ ≤ (1+a)^Fintype.card (PathLabel n)*M := h
    _ = _ := (mul_div_assoc ..).symm

#print axioms physical_weak_seam_mass
end
end GaloisForLFunctions.HTGeometry.BlockDilations.AdaptiveCuts
