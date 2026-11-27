import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.NearDiagonal.SeparatedBox
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Quantitative.CarrierGap
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Quantitative.Cost
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Neighborhood

/-! # All-time and first-excursion budgets on the same coefficient box -/
open Matrix Finset Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open WeakBonds.SingleCut
open private quadratic_error from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Neighborhood
noncomputable section
variable {n : ℕ}

private theorem core_difference (q : Fin (n+2)) (u v : PathShell n) {r : ℝ} (hr : 0 ≤ r)
    (hu : ∀ l, |u l-v l| ≤ r) :
    ‖pathHamiltonian (core q u)-pathHamiltonian (core q v)‖ ≤ (Fintype.card (PathLabel n):ℝ)*r := by
  rw [pathHamiltonian_eq_sum,pathHamiltonian_eq_sum,←sum_sub_distrib]
  apply (norm_sum_le ..).trans
  calc
    _ ≤ ∑ _ : PathLabel n, r := sum_le_sum fun l _ => by
      rw [←sub_smul,←Complex.ofReal_sub,norm_smul,norm_finitePauliMatrix,mul_one,Complex.norm_real,Real.norm_eq_abs]
      by_cases hl : axial q l
      · rw [restricted_eq u hl,restricted_eq v hl]; exact hu l
      · rw [restricted_zero u hl,restricted_zero v hl,sub_self,abs_zero]; exact hr
    _ = _ := by rw [sum_const,card_univ,nsmul_eq_mul]

/-- A box of radius β3⁻ᴷ/M in the M physical coordinates suffices.
The full orbit has diagonal cost. Fourteen transverse entries
control the smaller increment budget on the prescribed window. -/
theorem uniform_joint_central_box :
    ∃ β∈Set.Ioc (0:ℝ) (1/2), ∀ {n : ℕ} (a b : Fin (n+1)), a.succ=b.castSucc →
      2 ≤ (Iic a.succ).card → 2 ≤ (Ici a.succ).card →
      let M : ℝ := Fintype.card (PathLabel n)
      let r := β/(M*3^(n+2))
      ∃ w : PathShell n, (∀ i : Fin (n+2), 1 ≤ w (.inl (i,2))) ∧
        (∀ e : Fin (n+1), w (.inr (e,(2,2)))=1) ∧ (∀ l, ¬IsDiagLabel l → w l=0) ∧
        (∀ l : PathLabel n, |w l| ≤ 2+(if l=.inl (a.succ,2) then 2*M+3 else 0)) ∧
        ∀ u : PathShell n, (∀ l, |u l-w l| ≤ r) →
        (∀ t : ℝ, HasProjectiveCircuitApproximation (n+2) (1/10) (2^(n+2)*(2*(n+2)+1))
          (unitaryEvolution (pathHamiltonian u) t)) ∧
        ∀ T ≥ (1:ℝ), (∀ l∈transverseLabels a b, |u l| ≤ 1/(1800*sqrt T)) →
        ∀ t : ℝ, |t| ≤ T → HasProjectiveCircuitApproximation (n+2) (1/100)
          (blockCost (Iic a.succ).card+blockCost (Ici a.succ).card)
          (unitaryEvolution (pathHamiltonian u) t) := by
  let p := sqrt packConstant
  have hp : 0 ≤ p := sqrt_nonneg _
  let β := min (1/2:ℝ) (1/(2000*(1+p)))
  have hβ : 0 < β := lt_min (by norm_num) (by positivity)
  have hβ₁ : β ≤ 1/2 := min_le_left ..
  have hconst : 4*p*β ≤ 1/400 := by
    apply (mul_le_mul_of_nonneg_left (min_le_right ..) (mul_nonneg (by norm_num) hp)).trans
    rw [mul_one_div]
    apply (div_le_iff₀ (by positivity)).mpr
    linarith only [hp]
  refine ⟨β,⟨hβ,hβ₁⟩,?_⟩
  intro n a b hab hL hR M r
  let q := a.succ
  let g : ℝ := 1/3^(n+2)
  have hg : 0 < g := by dsimp only [g]; positivity
  have hg₁ : g ≤ 1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num) (n:=n+2))
  have hM : 0 < M := Nat.cast_pos.mpr Fintype.card_pos
  have hr : 0 < r := div_pos hβ (by positivity)
  have hMr : M*r=β*g := by dsimp only [r,g]; field_simp [hM.ne']
  obtain ⟨w,h,_,d,hs,hmat,hc,hgap,hi,he,hz,hh,hw⟩ := quantitative_gapped_carrier q
  refine ⟨w,hi,he,hz,fun l => (hw l).trans ?_,?_⟩
  · by_cases hl : l=.inl (q,2) <;> simp only [q] at hl ⊢
    · simp only [if_pos hl]; linarith only [hh]
    · simp only [if_neg hl,le_refl]
  · intro u hu
    constructor
    · intro t
      let A : selfAdjoint (DiagonalSynthesis.Register (n+2)) :=
        ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
      obtain ⟨z,hz,C,hC,hfit⟩ := DiagonalSynthesis.CommutatorBounds.all_time_diagonal_approximation
        (by omega : 2 ≤ n+2) A d hg hs t
      rw [←hmat] at hfit
      have hclose := WeakBonds.NearDiagonal.shell_difference u w hu
      change ‖pathHamiltonian u-pathHamiltonian w‖ ≤ M*r at hclose
      rw [hMr] at hclose
      refine ⟨z,hz,C,hC,hfit.trans ?_⟩
      calc _ ≤ 4*p/g*(β*g) := mul_le_mul_of_nonneg_left hclose (by positivity)
           _ = 4*p*β := by field_simp
           _ ≤ 1/10 := hconst.trans (by norm_num)
    intro T hT hδ t ht
    let H := pathHamiltonian (core q u)
    have hclose : ‖H-pathHamiltonian w‖ ≤ β*g := by
      have hdiff := core_difference q u w hr.le hu
      change ‖H-pathHamiltonian (core q w)‖ ≤ M*r at hdiff
      rwa [hc,hMr] at hdiff
    have hgap' : 2 < h-‖H-h • spin q‖ := by
      have htri := norm_sub_le_norm_sub_add_norm_sub H (pathHamiltonian w) (h • spin q)
      linarith only [htri,hclose,hgap,mul_le_of_le_one_right hβ.le hg₁,hβ₁]
    have hcost := conserved_cost_at_gap a (core q u) hL hR (core_longitudinal q u) d hg hs t
    obtain ⟨z,hz,C,hC,hfit⟩ := hcost
    rw [←hmat] at hfit
    have herr : 4*p/g*‖H-pathHamiltonian w‖ ≤ 1/400 := by
      calc _ ≤ 4*p/g*(β*g) := mul_le_mul_of_nonneg_left hclose (by positivity)
           _ = 4*p*β := by field_simp
           _ ≤ _ := hconst
    have hb := core_evolution_bound q u h (by linarith only [hgap']) t
    have hn := offAxis_norm hab u (by positivity : 0 ≤ 1/(1800*sqrt T)) hδ
    have hpert := quadratic_error (one_le_sqrt.mpr hT) (norm_nonneg _) hgap' hn
      (ht.trans_eq (sq_sqrt (zero_le_one.trans hT)).symm)
    refine ⟨z,hz,C,hC,?_⟩
    apply (norm_sub_le_norm_sub_add_norm_sub _ (unitaryEvolution H t) _).trans
    change ‖unitaryEvolution H t-z • C.eval.val‖ ≤
      4*p/g*‖H-pathHamiltonian w‖+4*p/g*‖H-pathHamiltonian w‖ at hfit
    linarith only [hb.trans hpert,hfit,herr]

#print axioms uniform_joint_central_box
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
