import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NormalizedRadius.BulkEnergy
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.FixedRadius
import GaloisForLFunctions.HTGeometry.GaussianCoordinateSelection

/-! # Weak bonds at a macroscopic total coupling norm -/
open Set MeasureTheory ProbabilityTheory Real
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NormalizedRadius
open PrescribedTimes
noncomputable section

/-- Conditioning only on the cut coordinates preserves the original
Gaussian law in the complementary coordinates. At least a fixed
fraction of the weak-cut mass has norm comparable to the typical norm. -/
theorem weak_box_norm (n : ℕ) (S : Finset (PrefixIndex n)) (hcard : S.card=18)
    (hm : 36≤Fintype.card (PrefixIndex n)) {δ : ℝ} (hδ : 0≤δ) (hδ' : δ≤1) :
    let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
    let m : ℝ := Fintype.card (PrefixIndex n)
    ((2*gaussianDensityFloor)*δ)^18*(bulkMass/2) ≤ μ.real {x |
      (∀ i∈S, |x i|≤δ) ∧ sqrt m*sqrt (bulkMass/4) ≤ coefficientNorm x} := by
  classical
  intro μ m
  let I := {i : PrefixIndex n // i ∈ S}
  let K := {i : PrefixIndex n // i ∉ S}
  let α := Measure.pi fun _ : I => gaussianReal 0 1
  let ν := Measure.pi fun _ : K => gaussianReal 0 1
  let e := MeasurableEquiv.piEquivPiSubtypeProd (fun _ : PrefixIndex n => ℝ) (fun i => i∈S)
  have he : MeasurePreserving e μ (α.prod ν) := by
    dsimp only [e,μ,α,ν,I,K]
    convert measurePreserving_piEquivPiSubtypeProd (fun _ : PrefixIndex n => gaussianReal 0 1)
      (fun i => i ∈ S) using 1
    congr!
  have hI : Fintype.card I=18 := (Fintype.card_coe S).trans hcard
  have hK : Fintype.card K=Fintype.card (PrefixIndex n)-18 := by
    rw [Fintype.card_subtype_compl]; exact congrArg (Fintype.card (PrefixIndex n)-·) hI
  have hk : 0<Fintype.card K := by rw [hK]; omega
  letI : Nonempty K := Fintype.card_pos_iff.mp hk
  let W := univ.pi (fun _ : I => Icc (-δ) δ)
  let B := {z : K → ℝ | (Fintype.card K:ℝ)*(bulkMass/2) ≤ ∑ i, (z i)^2}
  have hW : MeasurableSet W := MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Icc)
  have hB : MeasurableSet B := measurableSet_le measurable_const (by fun_prop)
  have hw : ((2*gaussianDensityFloor)*δ)^18 ≤ α.real W := by
    have h := coefficientBox_floor (Finset.univ : Finset I) univ hδ hδ'
    have eq : coefficientBox (Finset.univ : Finset I) δ univ=W := by
      simp only [coefficientBox,W,Finset.mem_univ,if_true]
    dsimp only at h
    rw [eq,Finset.card_univ,hI,Finset.compl_univ,Finset.card_empty,pow_zero,mul_one,←mul_pow] at h
    exact h
  have hsub : e ⁻¹' (W ×ˢ B) ⊆ {x : PrefixIndex n → ℝ |
      (∀ i∈S, |x i|≤δ) ∧ sqrt m*sqrt (bulkMass/4)≤coefficientNorm x} := by
    rintro x ⟨hc,hb⟩
    refine ⟨fun i hi => abs_le.mpr (hc ⟨i,hi⟩ (mem_univ _)),?_⟩
    change (Fintype.card K:ℝ)*(bulkMass/2) ≤ ∑ i : K, (x i.val)^2 at hb
    have hsize : m ≤ 2*(Fintype.card K:ℝ) := by
      have hnat : Fintype.card (PrefixIndex n) ≤ 2*Fintype.card K := by rw [hK]; omega
      dsimp only [m]
      exact_mod_cast hnat
    have hsum : (∑ i : I, (x i.val)^2)+(∑ i : K, (x i.val)^2)=∑ i, (x i)^2 := by
      convert Fintype.sum_subtype_add_sum_subtype (fun i => i∈S) (fun i => (x i)^2) using 1
      congr!
    have hnon := Finset.sum_nonneg (s:=Finset.univ) (fun i (_ : i∈Finset.univ) => sq_nonneg (x (i:I).val))
    have hn : (coefficientNorm x)^2=∑ i, (x i)^2 :=
      EuclideanSpace.real_norm_sq_eq (WithLp.toLp 2 x)
    have hsq : (sqrt m*sqrt (bulkMass/4))^2=m*(bulkMass/4) := by
      rw [mul_pow,sq_sqrt (Nat.cast_nonneg _),sq_sqrt (div_nonneg bulkMass_pos.le (by norm_num))]
    apply le_of_not_gt
    intro hh
    have hcn : 0 ≤ coefficientNorm x := norm_nonneg _
    have hstrict : (coefficientNorm x)^2 < (sqrt m*sqrt (bulkMass/4))^2 := by
      nlinarith only [mul_pos (sub_pos.mpr hh) (add_pos_of_pos_of_nonneg (hcn.trans_lt hh) hcn)]
    rw [hsq,hn] at hstrict
    have hbulk : m*(bulkMass/4) ≤ (Fintype.card K:ℝ)*(bulkMass/2) := by
      linarith only [mul_le_mul_of_nonneg_right hsize bulkMass_pos.le]
    exact hstrict.not_ge (hbulk.trans (hb.trans ((le_add_of_nonneg_left hnon).trans_eq hsum)))
  calc
    _ ≤ α.real W * ν.real B := mul_le_mul hw (bulk_energy_mass K) (half_pos bulkMass_pos).le measureReal_nonneg
    _ = μ.real (e ⁻¹' (W ×ˢ B)) := (measureReal_prod_prod W B).symm.trans
      (he.measureReal_preimage (hW.prod hB).nullMeasurableSet).symm
    _ ≤ _ := measureReal_mono hsub

#print axioms weak_box_norm
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NormalizedRadius
