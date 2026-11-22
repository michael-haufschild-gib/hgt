import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.PrescribedTimes.GaussianDilation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # Gaussian mass of hits isolated from nearby dilations -/
open MeasureTheory ProbabilityTheory Set Real
namespace GaloisForLFunctions.HTGeometry.PrescribedTimes.ShortWindows
noncomputable section
variable {ι : Type*} {m : ℕ}

/-- In every row of dilation ratios only the diagonal may hit the event. -/
def isolated (a : Fin m → ℝ) (E : Set (ι → ℝ)) : Set (ι → ℝ) :=
  E ∩ ⋂ i : Fin m, ⋂ j : {j : Fin m // j≠i}, ((fun x : ι → ℝ => (a j/a i) • x) ⁻¹' E)ᶜ

theorem measurable_isolated (a : Fin m → ℝ) {E : Set (ι → ℝ)} (hE : MeasurableSet E) :
    MeasurableSet (isolated a E) :=
  hE.inter (MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
    (hE.preimage (measurable_id.const_smul (a j/a i))).compl)

theorem mem_isolated {a : Fin m → ℝ} {E : Set (ι → ℝ)} {x : ι → ℝ} (hx : x∈E)
    (h : ∀ i j : Fin m, j≠i → (a j/a i) • x ∉ E) : x∈isolated a E :=
  ⟨hx,mem_iInter.mpr fun i => mem_iInter.mpr fun j => h i j j.property⟩

/-- A dilation grid whose fractional changes are at most one inverse
coefficient dimension costs at most e, independently of the dimension. -/
theorem gaussian_isolated_mass [Fintype ι] {a : Fin m → ℝ} {E : Set (ι → ℝ)} (hE : MeasurableSet E)
    (ha : ∀ i, 1 ≤ a i) (hd : ∀ i, (Fintype.card ι:ℝ)*(a i-1) ≤ 1) :
    let μ := Measure.pi (fun _ : ι => gaussianReal 0 1)
    (m:ℝ)*μ.real (isolated a E) ≤ exp 1 := by
  classical
  intro μ
  let B := isolated a E
  let V (i : Fin m) := (fun x : ι → ℝ => a i • x) ⁻¹' B
  have hm : MeasurableSet B := measurable_isolated a hE
  have hV (i : Fin m) : MeasurableSet (V i) := hm.preimage (measurable_id.const_smul (a i))
  have hp (i : Fin m) : 0 < a i := zero_lt_one.trans_le (ha i)
  have hdis : Pairwise (fun i j => Disjoint (V i) (V j)) := by
    intro i j hij
    apply disjoint_left.mpr
    intro x hx hy
    have hi : a i • x ∈ isolated a E := hx
    have hj : a j • x ∈ isolated a E := hy
    have hno := mem_iInter.mp (mem_iInter.mp hi.2 i) (⟨j,hij.symm⟩ : {k : Fin m // k≠i})
    change (a j/a i) • (a i • x) ∉ E at hno
    rw [smul_smul,div_mul_cancel₀ _ (hp i).ne'] at hno
    exact hno hj.1
  have hpow (i : Fin m) : (a i)^(Fintype.card ι) ≤ exp 1 := by
    have h := Real.add_one_le_exp (a i-1)
    rw [sub_add_cancel] at h
    refine (pow_le_pow_left₀ (hp i).le h _).trans ?_
    rw [←Real.exp_nat_mul]
    exact Real.exp_le_exp.mpr (hd i)
  have he (i : Fin m) : μ.real B ≤ exp 1*μ.real (V i) :=
    (gaussian_dilation_comparison (ha i) B hm).trans
      (mul_le_mul_of_nonneg_right (hpow i) (measureReal_nonneg))
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun i _ => he i)
  rw [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,←Finset.mul_sum,
    ←measureReal_iUnion_fintype hdis hV (fun _ => measure_ne_top _ _)] at h
  exact h.trans ((mul_le_mul_of_nonneg_left (measureReal_le_one) (Real.exp_pos _).le).trans_eq (mul_one _))

#print axioms gaussian_isolated_mass
end
end GaloisForLFunctions.HTGeometry.PrescribedTimes.ShortWindows
