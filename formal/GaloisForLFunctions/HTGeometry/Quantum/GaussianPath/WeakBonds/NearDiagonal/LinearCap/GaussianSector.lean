import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.LinearCap.Carrier
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Rotated.Frame
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Quantitative.BoxMass
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Quantitative.Prefactor

/-! # Gaussian mass of a linear-in-dimension gate cap -/

open Set Finset Real MeasureTheory ProbabilityTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal
open Dephasing.GappedSpin.CentralCut AccuracyScales.TenthPlateau PrescribedTimes
noncomputable section

/-- At every positive error through one, a measurable sector of the
physical Gaussian law has the diagonal gate cap for the entire orbit.
Only the ten off-diagonal coordinates per added site pay for precision. -/
theorem linear_cap_gaussian_sector :
    ∃ C > (0:ℝ), ∀ n : ℕ,
      let K := n+2
      let μ := Measure.pi (fun _ : PathLabel n => gaussianReal 0 1)
      ∀ ε ∈ Set.Ioc (0:ℝ) 1, ∃ E : Set (PathLabel n → ℝ), MeasurableSet E ∧
        ε^(10*n+12)*exp (-C*(K:ℝ)^2) ≤ μ.real E ∧
        ∀ x ∈ E, (fun i => x (pathCoeffEquiv n i)) ∈ allCoordStrongEvent n (1/100) ∧
          ∀ t : ℝ, HasProjectiveCircuitApproximation K ε (2^K*3)
            (unitaryEvolution (pathHamiltonian (WithLp.toLp 2 x : PathShell n)) t) := by
  classical
  obtain ⟨β,hβ,hgeom⟩ := linear_separated_box
  let f := (sqrt (2*π))⁻¹
  have hf : 0 < f := by dsimp only [f]; positivity
  obtain ⟨C,hC,hprice⟩ := quadratic_box_prefactor (mul_pos (mul_pos two_pos hf) hβ.1)
  refine ⟨144*C,mul_pos (by norm_num) hC,?_⟩
  intro n K μ ε hε
  let M := Fintype.card (PathLabel n)
  have hcounts : M=(n+2)*3+(n+1)*(3*3) := by
    simp only [M,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
  have hM : 1 ≤ M := by omega
  have h₁ : (1:ℝ) ≤ M := by exact_mod_cast hM
  have hK : K ≤ M := by dsimp only [K]; omega
  have hMhi : (M:ℝ) ≤ 12*(K:ℝ) := by exact_mod_cast (show M ≤ 12*K by dsimp only [K]; omega)
  let r := β/((M:ℝ)*3^K)
  have hr : 0 < r := div_pos hβ.1 (by positivity)
  have hrsmall : r ≤ 1/20000 :=
    (div_le_self hβ.1.le (one_le_mul_of_one_le_of_one_le h₁ (one_le_pow₀ (by norm_num) (n:=K)))).trans hβ.2
  obtain ⟨w,hw,hz,hcap⟩ := hgeom n
  let S : Finset (PathLabel n) := Finset.univ.filter (fun l => ¬IsDiagLabel l)
  have hS : S.card=10*n+12 := (Fintype.card_subtype (fun l : PathLabel n => ¬IsDiagLabel l)).symm.trans (card_offDiagLabel n)
  have hs : 1 ≤ ε⁻¹ := (one_le_inv₀ hε.1).mpr hε.2
  let width (l : PathLabel n) := if l∈S then r/ε⁻¹ else r
  let E := Set.univ.pi fun l => Icc (w l-width l) (w l+width l)
  have hE : MeasurableSet E := MeasurableSet.pi (Set.to_countable _) (fun _ _ => measurableSet_Icc)
  have hb := gaussian_rectangular_floor S w.ofLp hr (hrsmall.trans (by norm_num)) hs
  change (2*f*r)^M*exp (-(∑ l, (|w l|+1)^2)/2) ≤ (ε⁻¹)^S.card*μ.real E at hb
  have hradii : ∑ l, (|w l|+1)^2 ≤ 9*(M:ℝ) := by
    calc _ ≤ ∑ _ : PathLabel n, (9:ℝ) := sum_le_sum fun l _ => by
           by_cases hl : IsDiagLabel l
           · obtain ⟨hlo,hhi⟩ := hw l hl
             rw [abs_of_nonneg (zero_le_one.trans hlo)]
             exact (pow_le_pow_left₀ (by linarith only [hlo])
               (by linarith only [hhi] : w l+1 ≤ 3) 2).trans (by norm_num)
           · rw [hz l hl,abs_zero]; norm_num
         _ = _ := by rw [sum_const,card_univ,nsmul_eq_mul,mul_comm]
  have hbase : 2*f*r=2*f*β/((M:ℝ)*3^K) := by dsimp only [r]; ring
  have hlow : exp (-144*C*(K:ℝ)^2) ≤ (ε⁻¹)^S.card*μ.real E := by
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg M) hMhi 2
    apply (exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hsq hC.le]) :
      exp (-144*C*(K:ℝ)^2) ≤ exp (-C*(M:ℝ)^2)).trans
    apply (hprice M K hM hK).trans
    rw [←hbase]
    apply le_trans (div_le_self (by positivity) (by norm_num))
    apply le_trans _ hb
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact exp_le_exp.mpr (by linarith only [hradii,sq_nonneg (2*(M:ℝ)+6)])
  obtain ⟨F,hF,hm,hrot⟩ := rotated_sector hE
  refine ⟨F,hF,?_,?_⟩
  · rw [hm,←hS]
    have h := mul_le_mul_of_nonneg_left hlow (pow_nonneg hε.1.le S.card)
    rw [←mul_assoc,←mul_pow,mul_inv_cancel₀ hε.1.ne',one_pow,one_mul] at h
    simpa only [neg_mul] using h
  · intro x hx
    obtain ⟨y,hy,rfl⟩ := hrot x hx
    have hbnd (l) : |y l-w l| ≤ width l := by
      have hi : y l ∈ Icc (w l-width l) (w l+width l) := hy l (Set.mem_univ l)
      exact abs_le.mpr ⟨by linarith only [hi.1],by linarith only [hi.2]⟩
    have hd (l) (hl : IsDiagLabel l) : |y l-w l| ≤ r := by simpa [width,S,hl] using hbnd l
    have ho (l) (hl : ¬IsDiagLabel l) : |y l| ≤ r*ε := by
      simpa [width,S,hl,hz l hl,div_eq_mul_inv] using hbnd l
    refine ⟨rotated_coordinates_strong (fun l hl => ?_) (fun l hl => ?_),fun t =>
      rotated_increment_fit (hcap ε hε (WithLp.toLp 2 y) hd ho t)⟩
    · linarith only [(abs_le.mp (hd l hl)).1,(hw l hl).1,hrsmall]
    · exact ((ho l hl).trans (mul_le_of_le_one_right hr.le hε.2)).trans hrsmall

#print axioms linear_cap_gaussian_sector
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal
