import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Quantitative.JointCap
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Quantitative.PricedWidths
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Middle

/-! # Gaussian mass for a long first excursion and a bounded orbit maximum -/
open Filter MeasureTheory ProbabilityTheory Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open PrescribedTimes WeakBonds.SingleCut
noncomputable section

/-- A longitudinal frame with cheap increments has Gaussian mass
at least exp(−CK²)/T⁷. Every diagonal coefficient is bounded below;
the same draw admits the diagonal gate budget for all real times. -/
theorem gaussian_joint_central_box :
    ∃ C > (0:ℝ), ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let K := n+2
      let P := nearHilbertContinuousCircuitBudget K
      let μ := Measure.pi (fun _ : PathLabel n => gaussianReal 0 1)
      ∀ T ≥ (1:ℝ), ∃ B : ℕ, ∃ E : Set (PathLabel n→ℝ), 2*B ≤ P ∧ MeasurableSet E ∧
        exp (-C*(K:ℝ)^2) ≤ T^7*μ.real E ∧
        ∀ x∈E, (∀ l, IsDiagLabel l → 1/2 < x l) ∧ (∀ l, ¬IsDiagLabel l → |x l| ≤ 1/20000) ∧
          (∀ t : ℝ, HasProjectiveCircuitApproximation K (1/10) (2^K*(2*K+1))
            (unitaryEvolution (pathHamiltonian (WithLp.toLp 2 x : PathShell n)) t)) ∧
          ∀ t : ℝ, |t| ≤ T → HasProjectiveCircuitApproximation K (1/100) B
            (unitaryEvolution (pathHamiltonian (WithLp.toLp 2 x : PathShell n)) t) := by
  classical
  obtain ⟨β,hβ,hgeom⟩ := uniform_joint_central_box
  obtain ⟨C,hC,hprice⟩ := priced_transverse_widths hβ
  refine ⟨C,hC,?_⟩
  filter_upwards [eventually_ge_atTop 64] with k hk
  intro n K P μ T hT
  obtain ⟨a,b,hab,hL,hR,hB⟩ := affordable_middle_spin n (by dsimp only [n]; omega)
  obtain ⟨w,hi,he,hz,hmax,hcheap⟩ := hgeom a b hab hL hR
  let M := Fintype.card (PathLabel n)
  have hcounts : M=(n+2)*3+(n+1)*(3*3) := by
    simp only [M,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  have hM : 1 ≤ M := by omega
  have hM₁ : (1:ℝ) ≤ M := by exact_mod_cast hM
  let r := β/((M:ℝ)*3^K)/2
  have hr₁ : r ≤ 1/4 := by
    have hden := one_le_mul_of_one_le_of_one_le hM₁ (one_le_pow₀ (by norm_num : (1:ℝ)≤3) (n:=K))
    have h := (div_le_self hβ.1.le hden).trans hβ.2
    dsimp only [r]; linarith only [h]

  have hrsmall : r ≤ 1/20000 := by
    have h₀ : 10 ≤ K := by dsimp only [K,n]; omega
    have h₁ : (10000:ℝ) ≤ 3^K := (by norm_num : (10000:ℝ) ≤ 3^(10:ℕ)).trans
      (pow_le_pow_right₀ (by norm_num) h₀)
    have hden : (10000:ℝ) ≤ (M:ℝ)*3^K := h₁.trans (le_mul_of_one_le_left (by positivity) hM₁)
    have hdiv : β/((M:ℝ)*3^K) ≤ 1/10000 := (div_le_iff₀ (by positivity)).mpr
      (by linarith only [hβ.2,hden])
    dsimp only [r]; linarith only [hdiv]
  obtain ⟨E,hE,hfloor,hwidth⟩ := hprice a b w hz hmax T hT
  refine ⟨_,E,hB,hE,hfloor,?_⟩
  intro x hx
  obtain ⟨hball,hcut⟩ := hwidth _ hx
  have hw (l) := (hball l).trans (half_le_self (div_pos hβ.1 (by positivity : 0 < (M:ℝ)*3^K)).le)
  obtain ⟨hglobal,hinc⟩ := hcheap (WithLp.toLp 2 x) hw
  refine ⟨?_,?_,hglobal,hinc T hT (fun l hl => (hcut l hl).trans
    (div_le_div_of_nonneg_right (hr₁.trans (by norm_num : (1/4:ℝ)≤1)) (by positivity)))⟩
  · intro l hl
    have h₁ : 1 ≤ w l := by
      rcases l with ⟨i,p⟩|⟨e,p⟩
      · change p=2 at hl
        subst p; exact hi i
      · change p=(2,2) at hl
        subst p; exact (he e).ge
    have hh := (abs_le.mp (hball l)).1
    linarith only [hh,hr₁,h₁]
  · intro l hl
    have hh := hball l
    rw [hz l hl,sub_zero] at hh
    exact hh.trans hrsmall

#print axioms gaussian_joint_central_box
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
