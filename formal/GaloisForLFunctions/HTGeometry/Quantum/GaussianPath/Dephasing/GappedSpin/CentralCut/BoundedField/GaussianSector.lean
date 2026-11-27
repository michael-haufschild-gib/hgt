import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.BoundedField.CoefficientBox
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Quantitative.PricedWidths
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Middle

/-! # Gaussian mass with bounded fields and a linear-in-dimension orbit cap -/
open Filter MeasureTheory ProbabilityTheory Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open PrescribedTimes
noncomputable section

/-- A separated carrier with bounded onsite and bond coefficients gives
a linear all-time cap and cheap increments through the prescribed date. -/
theorem bounded_gaussian_sector :
    ∃ C > (0:ℝ), ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let K := n+2
      let P := nearHilbertContinuousCircuitBudget K
      let μ := Measure.pi (fun _ : PathLabel n => gaussianReal 0 1)
      ∀ T ≥ (1:ℝ), ∃ B : ℕ, ∃ E : Set (PathLabel n→ℝ), 2*B ≤ P ∧ MeasurableSet E ∧
        exp (-C*(K:ℝ)^2) ≤ T^7*μ.real E ∧
        (∃ q : Fin K, ∀ x∈E, ∀ j : Fin 3, j≠2 →
          |x (.inl (q,j))| ≤ 1/(3600*sqrt T)) ∧
        ∀ x∈E, (∀ l, |x l| ≤ 3) ∧ (∀ l, IsDiagLabel l → 1/2 < x l) ∧
          (∀ l, ¬IsDiagLabel l → |x l| ≤ 1/20000) ∧
          (∀ t : ℝ, HasProjectiveCircuitApproximation K (1/10) (2^K*3)
            (unitaryEvolution (pathHamiltonian (WithLp.toLp 2 x : PathShell n)) t)) ∧
          ∀ t : ℝ, |t| ≤ T → HasProjectiveCircuitApproximation K (1/100) B
            (unitaryEvolution (pathHamiltonian (WithLp.toLp 2 x : PathShell n)) t) := by
  classical
  obtain ⟨β,hβ,hgeom⟩ := bounded_field_box
  obtain ⟨C,hC,hprice⟩ := priced_transverse_widths (β:=β) ⟨hβ.1,hβ.2.trans (by norm_num)⟩
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop 64] with k hk
  intro n K P μ T hT
  obtain ⟨a,b,hab,hL,hR,hB⟩ := affordable_middle_spin n (by dsimp only [n]; omega)
  obtain ⟨w,hd,hz,hfit⟩ := hgeom a b hab hL hR
  let M := Fintype.card (PathLabel n)
  let r := β/((M:ℝ)*3^K)
  have hcount : M=(n+2)*3+(n+1)*(3*3) := by
    simp only [M,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  have hM : (1:ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hr : 0 ≤ r := div_nonneg hβ.1.le (by positivity)
  have hrsmall : r ≤ 1/20000 := (div_le_self hβ.1.le
    (one_le_mul_of_one_le_of_one_le hM (one_le_pow₀ (by norm_num) (n:=K)))).trans hβ.2
  have hw (l) : |w l| ≤ 2 := by
    by_cases hl : IsDiagLabel l
    · rw [abs_of_nonneg (zero_le_one.trans (hd l hl).1)]
      exact (hd l hl).2
    · rw [hz l hl,abs_zero]; norm_num
  obtain ⟨E,hE,hm,hwidth⟩ := hprice a b w hz (fun l => (hw l).trans
    (le_add_of_nonneg_right (by split <;> positivity))) T hT
  have hs := zero_lt_one.trans_le (one_le_sqrt.mpr hT)
  refine ⟨_,E,hB,hE,hm,⟨a.succ,?_⟩,?_⟩
  · intro x hx j hj
    have hj' : Sum.inl (a.succ,j) ∈ transverseLabels a b :=
      Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr
        ⟨j,Finset.mem_erase.mpr ⟨hj,Finset.mem_univ j⟩,rfl⟩))
    apply ((hwidth x hx).2 _ hj').trans
    change r/2/(1800*sqrt T) ≤ 1/(3600*sqrt T)
    rw [div_div,show 2*(1800*sqrt T)=3600*sqrt T by ring]
    exact div_le_div_of_nonneg_right (hrsmall.trans (by norm_num)) (by positivity)
  intro x hx
  obtain ⟨hball,hcut⟩ := hwidth x hx
  have hbulk l : |x l-w l| ≤ r := (hball l).trans (half_le_self hr)
  obtain ⟨hglobal,hinc⟩ := hfit (WithLp.toLp 2 x) hbulk
  refine ⟨?_,?_,?_,hglobal,hinc T hT ?_⟩
  · intro l
    have h := abs_add_le (x l-w l) (w l)
    rw [sub_add_cancel] at h
    linarith only [h,hbulk l,hw l,hrsmall]
  · intro l hl
    linarith only [(abs_le.mp (hbulk l)).1,(hd l hl).1,hrsmall]
  · intro l hl
    simpa only [hz l hl,sub_zero] using (hbulk l).trans hrsmall
  · intro l hl
    have hdiv : r/2/(1800*sqrt T) ≤ r/sqrt T := by
      rw [←div_div]
      exact div_le_div_of_nonneg_right ((div_le_self (div_nonneg hr (by norm_num)) (by norm_num)).trans
        (half_le_self hr)) hs.le
    exact (hcut l hl).trans hdiv

#print axioms bounded_gaussian_sector
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
