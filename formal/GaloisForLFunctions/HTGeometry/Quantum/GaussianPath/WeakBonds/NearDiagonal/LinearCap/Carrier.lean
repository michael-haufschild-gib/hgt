import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.MultiplexedPhases.Commuting
import GaloisForLFunctions.HTGeometry.NearUniformSeparatingCarrier
import GaloisForLFunctions.HTGeometry.EternityObservableHorizonLaw

/-! # A separated Ising box with a linear-in-dimension gate cap -/

open Finset Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal
open DiagonalSynthesis DiagonalSynthesis.CommutatorBounds
noncomputable section
variable {n : ℕ}

/-- Coordinatewise errors add in operator norm since each Pauli word
has norm one. -/
theorem coordinate_norm_bound (u v : PathShell n) {r : ℝ} (hu : ∀ l, |u l-v l| ≤ r) :
    ‖pathHamiltonian u-pathHamiltonian v‖ ≤ (Fintype.card (PathLabel n):ℝ)*r := by
  rw [pathHamiltonian_eq_sum,pathHamiltonian_eq_sum,←sum_sub_distrib]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ _ : PathLabel n, r := sum_le_sum fun l _ => by
      simpa only [←sub_smul,←Complex.ofReal_sub,norm_smul,norm_finitePauliMatrix,mul_one,
        Complex.norm_real,Real.norm_eq_abs] using hu l
    _ = _ := by rw [sum_const,card_univ,nsmul_eq_mul]

/-- Diagonal entries can vary at the spacing scale independently of
precision. Only transverse coefficients pay the extra factor ε. -/
theorem linear_separated_box :
    ∃ β ∈ Set.Ioc (0:ℝ) (1/20000), ∀ n : ℕ,
      let K := n+2
      let M : ℝ := Fintype.card (PathLabel n)
      let r := β/(M*3^K)
      ∃ w : PathShell n, (∀ l, IsDiagLabel l → 1 ≤ w l ∧ w l ≤ 2) ∧
        (∀ l, ¬IsDiagLabel l → w l=0) ∧
        ∀ ε ∈ Set.Ioc (0:ℝ) 1, ∀ u : PathShell n,
          (∀ l, IsDiagLabel l → |u l-w l| ≤ r) →
          (∀ l, ¬IsDiagLabel l → |u l| ≤ r*ε) →
          ∀ t : ℝ, HasProjectiveCircuitApproximation K ε (2^K*3)
            (unitaryEvolution (pathHamiltonian u) t) := by
  let p := sqrt packConstant
  let β := min (1/20000:ℝ) (1/(8*(1+p)))
  have hp : 0 ≤ p := sqrt_nonneg _
  have hβ : 0 < β := lt_min (by norm_num) (by positivity)
  have hβ₁ : β ≤ 1/20000 := min_le_left ..
  have hpβ : 8*p*β ≤ 1 := by
    apply (mul_le_mul_of_nonneg_left (min_le_right ..) (mul_nonneg (by norm_num) hp)).trans
    rw [mul_one_div,div_le_one (by positivity)]
    linarith only [hp]
  refine ⟨β,⟨hβ,hβ₁⟩,?_⟩
  intro n K M r
  let g := 1/(3:ℝ)^K
  let w := nearUniformCarrier n (g/2)
  have hg : 0 < g := by dsimp only [g]; positivity
  have hM : 0 < M := Nat.cast_pos.mpr Fintype.card_pos
  have hbase : g/2*3^(n+2)=1/2 := by dsimp only [g,K]; field_simp
  have hMr : M*r=β*g := by dsimp only [r,g]; field_simp [hM.ne']
  have hr : 0 < r := div_pos hβ (by positivity)
  have hoff := nearUniformCarrier_offDiag (n:=n) (g/2)
  refine ⟨w,nearUniformCarrier_coord_mem (half_pos hg).le (hbase.le.trans (by norm_num)),hoff,?_⟩
  intro ε hε u hd ht t
  let v : PathShell n := WithLp.toLp 2 fun l => if IsDiagLabel l then u l else 0
  have hv (l : PathLabel n) : v l = if IsDiagLabel l then u l else 0 := rfl
  have hD := pathHamiltonian_eq_diagonal v (fun l hl => (hv l).trans (if_neg hl))
  have hW := pathHamiltonian_eq_diagonal w hoff
  have hreg : ‖pathHamiltonian v-pathHamiltonian w‖ ≤ M*r := by
    apply coordinate_norm_bound
    intro l
    by_cases hl : IsDiagLabel l
    · rw [hv,if_pos hl]; exact hd l hl
    · rw [hv,if_neg hl,hoff l hl,sub_zero,abs_zero]; exact hr.le
  have hdiag (i) : |pathDiagEnergy v i-pathDiagEnergy w i| ≤ M*r := by
    have he := (norm_entry_le_l2_opNorm (pathHamiltonian v-pathHamiltonian w) i i).trans hreg
    simpa only [hD,hW,Matrix.sub_apply,diagonal_apply_eq,←Complex.ofReal_sub,
      Complex.norm_real,Real.norm_eq_abs] using he
  have hsep (i j) (hne : i≠j) : g/2 ≤ |pathDiagEnergy v i-pathDiagEnergy v j| := by
    have hg₀ := separation_nearUniformCarrier (half_pos hg) (hbase.le.trans (by norm_num)) hne
    change 2*(g/2) ≤ |pathDiagEnergy w i-pathDiagEnergy w j| at hg₀
    have tri : |pathDiagEnergy w i-pathDiagEnergy w j| ≤
        |pathDiagEnergy v i-pathDiagEnergy w i| + |pathDiagEnergy v i-pathDiagEnergy v j| +
        |pathDiagEnergy v j-pathDiagEnergy w j| := by
      simpa only [Real.dist_eq,abs_sub_comm (pathDiagEnergy w i) (pathDiagEnergy v i)] using
        dist_triangle4 (pathDiagEnergy w i) (pathDiagEnergy v i) (pathDiagEnergy v j) (pathDiagEnergy w j)
    have hi := hdiag i
    have hj := hdiag j
    rw [hMr] at hi hj
    nlinarith only [hg₀,tri,hi,hj,mul_le_mul_of_nonneg_right hβ₁ hg.le,hg.le]
  have herr : ‖pathHamiltonian u-pathHamiltonian v‖ ≤ M*(r*ε) := by
    apply coordinate_norm_bound
    intro l
    by_cases hl : IsDiagLabel l
    · rw [hv,if_pos hl,sub_self,abs_zero]; exact mul_nonneg hr.le hε.1.le
    · rw [hv,if_neg hl,sub_zero]; exact ht l hl
  let H : selfAdjoint (Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
  obtain ⟨z,hz,C,hC,hfit⟩ := MultiplexedPhases.all_time_gate_cap (by dsimp only [K]; omega) H
    (pathDiagEnergy v) (half_pos hg) hsep t
  rw [←hD] at hfit
  refine ⟨z,hz,C,hC,hfit.trans ?_⟩
  calc
    _ ≤ 4*p/(g/2)*(M*(r*ε)) := mul_le_mul_of_nonneg_left herr (by positivity)
    _ = (8*p*β)*ε := by rw [←mul_assoc M,hMr]; field_simp; ring
    _ ≤ ε := mul_le_of_le_one_left hε.1.le hpβ

#print axioms linear_separated_box
end
end GaloisForLFunctions.HTGeometry.WeakBonds.NearDiagonal
