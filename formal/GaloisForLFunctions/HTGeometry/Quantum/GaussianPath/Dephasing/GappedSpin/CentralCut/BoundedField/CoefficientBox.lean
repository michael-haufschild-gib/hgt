import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.BoundedField.Evolution
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Quantitative.JointCap
import GaloisForLFunctions.HTGeometry.Quantum.CircuitSynthesis.Diagonal.MultiplexedPhases.Commuting

/-! # Bounded Ising coefficients on a long first-excursion box -/
open Finset Matrix Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
open WeakBonds.SingleCut DiagonalSynthesis
open private axial_diag from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Quantitative.CarrierGap
open private core_difference from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.Quantitative.JointCap
noncomputable section

private theorem transverse_error {p g β v T t : ℝ} (hp : 0≤p) (hg : 0<g) (hg₁ : g≤1)
    (hβ : 0≤β) (hβ₁ : β≤1) (hv : 0≤v) (hT : 1≤T) (ht : |t|≤T)
    (hb : v*sqrt T ≤ β*g) :
    (2+|t| * v)*(2*(p/g)*v) ≤ 6*(p*β) := by
  have hs := one_le_sqrt.mpr hT
  have hv₁ : v ≤ β*g := (le_mul_of_one_le_right hv hs).trans hb
  have hv₂ : |t| * v^2 ≤ (β*g)^2 := by
    calc _ ≤ T*v^2 := mul_le_mul_of_nonneg_right ht (sq_nonneg _)
         _ = (v*sqrt T)^2 := by rw [mul_pow,sq_sqrt (zero_le_one.trans hT),mul_comm]
         _ ≤ _ := pow_le_pow_left₀ (mul_nonneg hv (sqrt_nonneg _)) hb 2
  have hbg : β*g ≤ 1 := mul_le_one₀ hβ₁ hg.le hg₁
  calc _ = 4*(p/g)*v+2*(p/g)*(|t| * v^2) := by ring
       _ ≤ 4*(p/g)*(β*g)+2*(p/g)*(β*g)^2 := add_le_add
         (mul_le_mul_of_nonneg_left hv₁ (by positivity)) (mul_le_mul_of_nonneg_left hv₂ (by positivity))
       _ = 4*(p*β)+2*(p*β)*(β*g) := by field_simp
       _ ≤ _ := by linarith only [mul_le_of_le_one_right (mul_nonneg (by norm_num : (0:ℝ)≤2) (mul_nonneg hp hβ)) hbg]

/-- All diagonal carrier fields lie between one and two. The common
spacing controls both the full-register cap and the inverse commutator
for the fourteen transverse coordinates. -/
theorem bounded_field_box :
    ∃ β ∈ Set.Ioc (0:ℝ) (1/20000), ∀ {n : ℕ} (a b : Fin (n+1)), a.succ=b.castSucc →
      2 ≤ (Iic a.succ).card → 2 ≤ (Ici a.succ).card →
      let K := n+2
      let M : ℝ := Fintype.card (PathLabel n)
      let r := β/(M*3^K)
      ∃ w : PathShell n, (∀ l, IsDiagLabel l → 1 ≤ w l ∧ w l ≤ 2) ∧
        (∀ l, ¬IsDiagLabel l → w l=0) ∧ ∀ u : PathShell n, (∀ l, |u l-w l| ≤ r) →
        (∀ t : ℝ, HasProjectiveCircuitApproximation K (1/10) (2^K*3)
          (unitaryEvolution (pathHamiltonian u) t)) ∧
        ∀ T ≥ (1:ℝ), (∀ l∈transverseLabels a b, |u l| ≤ r/sqrt T) →
        ∀ t : ℝ, |t| ≤ T → HasProjectiveCircuitApproximation K (1/100)
          (blockCost (Iic a.succ).card+blockCost (Ici a.succ).card)
          (unitaryEvolution (pathHamiltonian u) t) := by
  let p := sqrt packConstant
  have hp : 0≤p := sqrt_nonneg _
  let β := min (1/20000:ℝ) (1/(4000*(1+p)))
  have hβ : 0<β := lt_min (by norm_num) (by positivity)
  have hβ₁ : β≤1/20000 := min_le_left ..
  have hpβ : p*β≤1/4000 := by
    apply (mul_le_mul_of_nonneg_left (min_le_right ..) hp).trans
    rw [mul_one_div,div_le_iff₀ (by positivity)]
    linarith only [hp]
  refine ⟨β,⟨hβ,hβ₁⟩,?_⟩
  intro n a b hab hL hR K M r
  let g := 1/(3:ℝ)^K
  let w := nearUniformCarrier n (g/2)
  let d := pathDiagEnergy w
  let q := a.succ
  have hg : 0<g := by dsimp only [g]; positivity
  have hg₁ : g≤1 := (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num) (n:=K))
  have hbase : g/2*3^(n+2)=1/2 := by dsimp only [g,K]; field_simp
  have hM : (14:ℝ) ≤ M := by
    have hcount : Fintype.card (PathLabel n)=(n+2)*3+(n+1)*(3*3) := by
      simp only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    change (14:ℝ) ≤ (Fintype.card (PathLabel n):ℝ)
    exact_mod_cast (show 14 ≤ Fintype.card (PathLabel n) by omega)
  have hM₀ : 0<M := by linarith only [hM]
  have hr : 0<r := div_pos hβ (by positivity)
  have hMr : M*r=β*g := by dsimp only [r,g]; field_simp [hM₀.ne']
  have hz := nearUniformCarrier_offDiag (n:=n) (g/2)
  have hd := pathHamiltonian_eq_diagonal w hz
  have hsep (x y) (hne : x≠y) : g ≤ |d x-d y| := by
    have h := separation_nearUniformCarrier (half_pos hg) (hbase.le.trans (by norm_num)) hne
    change 2*(g/2) ≤ |d x-d y| at h
    linarith only [h]
  have hc : core q w=w := by
    suffices he : (core q w).ofLp=w.ofLp from congrArg (WithLp.toLp 2) he
    funext l
    by_cases hl : axial q l
    · exact restricted_eq w hl
    · exact (restricted_zero w hl).trans (hz l (fun h => hl (axial_diag q l h))).symm
  refine ⟨w,nearUniformCarrier_coord_mem (half_pos hg).le (hbase.le.trans (by norm_num)),hz,?_⟩
  intro u hu
  have cap {A : Register K} (hA : ‖A-pathHamiltonian w‖≤β*g) :
      (p/g)*‖A-pathHamiltonian w‖≤p*β :=
    (mul_le_mul_of_nonneg_left hA (by positivity)).trans_eq (by field_simp)
  have four (x : ℝ) : 4*p/g*x=4*((p/g)*x) := by ring
  constructor
  · intro t
    let H : selfAdjoint (Register K) := ⟨pathHamiltonian u,isSelfAdjoint_pathHamiltonian u⟩
    obtain ⟨z,hz,C,hC,hfit⟩ := MultiplexedPhases.all_time_gate_cap (by dsimp only [K]; omega) H d hg hsep t
    rw [←hd] at hfit
    have h := cap ((WeakBonds.NearDiagonal.shell_difference u w hu).trans_eq hMr)
    refine ⟨z,hz,C,hC,hfit.trans ?_⟩
    change 4*p/g*‖pathHamiltonian u-pathHamiltonian w‖ ≤ 1/10
    rw [four]
    linarith only [h,hpβ]
  intro T hT hcut t ht
  let H := pathHamiltonian (core q u)
  let V := pathHamiltonian (offAxis q u)
  have h₀ := core_difference q u w hr.le hu
  rw [hc] at h₀
  have h := cap (h₀.trans_eq hMr)
  have hcost := conserved_cost_at_gap a (core q u) hL hR (core_longitudinal q u) d hg hsep t
  obtain ⟨z,hz,C,hC,hfit⟩ := hcost
  rw [←hd] at hfit
  change ‖unitaryEvolution H t-z • C.eval.val‖ ≤ 4*p/g*‖H-pathHamiltonian w‖+4*p/g*‖H-pathHamiltonian w‖ at hfit
  simp only [four] at hfit
  change (p/g)*‖H-pathHamiltonian w‖≤p*β at h
  have hsmall : 2*(p/g)*‖H-diagonal (fun i => (d i:ℂ))‖ ≤ 1/2 := by
    rw [←hd]; linarith only [h,hpβ]
  have hev := separated_core_evolution q u d hg hsep hsmall t
  have hpos : 0 < sqrt T := (by positivity : (0:ℝ)<1).trans_le (one_le_sqrt.mpr hT)
  have hv : ‖V‖*sqrt T ≤ β*g := by
    rw [←hMr]
    apply (le_div_iff₀ hpos).mp
    exact (offAxis_norm hab u (div_nonneg hr.le hpos.le) hcut).trans
      (by rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_right hM (div_nonneg hr.le hpos.le))
  have he := transverse_error hp hg hg₁ hβ.le (hβ₁.trans (by norm_num)) (norm_nonneg V) hT ht hv
  refine ⟨z,hz,C,hC,?_⟩
  apply (norm_sub_le_norm_sub_add_norm_sub _ (unitaryEvolution H t) _).trans
  change ‖unitaryEvolution (pathHamiltonian u) t-unitaryEvolution H t‖ ≤ (2+|t| * ‖V‖)*(2*(p/g)*‖V‖) at hev
  linarith only [hev.trans he,hfit,h,hpβ]

#print axioms bounded_field_box
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut
