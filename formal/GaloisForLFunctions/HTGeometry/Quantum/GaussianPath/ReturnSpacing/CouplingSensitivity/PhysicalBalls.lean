import GaloisForLFunctions.HTGeometry.PathShellPatchTransport
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.ExtensiveWindow
import GaloisForLFunctions.HTGeometry.RationalCommonTimeWitness
import GaloisForLFunctions.HTGeometry.ObserverProfileStability

/-! # Coupling perturbations at a physical circuit return -/
open MeasureTheory Filter Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.ReturnSpacing.CouplingSensitivity
noncomputable section

/-- Affordability at the specified date with the perturbed physical couplings. -/
def affordable {n : ℕ} (u : PathShell n) (v ε : ℝ) (s : ℕ) : Prop :=
  HasProjectiveCircuitApproximation (n+2) ε s (unitaryEvolution (pathHamiltonian u) v)

/-- The same gates work on a whole coefficient ball after allowing an
additional 1/20 in physical error. -/
theorem affordable_ball {n s : ℕ} {u y : PathShell n} {v ε : ℝ} (hv : 0 < v)
    (h : affordable u v ε s) (hd : v*sqrt (n+2:ℕ)*‖y-u‖ ≤ 1/100) :
    affordable y v (ε+1/20) s := by
  let N := n+2
  have hdim : (Fintype.card (PathLabel n):ℝ) ≤ 16*(N:ℝ) := by
    simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,N,Nat.cast_add,
      Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
    linarith only [Nat.cast_nonneg (α:=ℝ) n]
  have hroot : sqrt (Fintype.card (PathLabel n)) ≤ 4*sqrt N := by
    simpa only [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 16),show sqrt (16:ℝ)=4 by norm_num] using Real.sqrt_le_sqrt hdim
  have hgen : ‖pathHamiltonian y-pathHamiltonian u‖ ≤ 4*sqrt N*‖y-u‖ :=
    (norm_pathHamiltonianLM_sub_le y u).trans (mul_le_mul_of_nonneg_right hroot (norm_nonneg _))
  have hU := norm_unitaryEvolution_sub_le _ _ (isSelfAdjoint_pathHamiltonian y) (isSelfAdjoint_pathHamiltonian u) v
  rw [abs_of_pos hv] at hU
  have hdiff := hU.trans (mul_le_mul_of_nonneg_left hgen hv.le)
  obtain ⟨z,hz,C,hC,herr⟩ := h
  refine ⟨z,hz,C,hC,?_⟩
  have htri := norm_sub_le_norm_sub_add_norm_sub (unitaryEvolution (pathHamiltonian y) v)
    (unitaryEvolution (pathHamiltonian u) v) (z • C.eval.val)
  change v*sqrt N*‖y-u‖ ≤ 1/100 at hd
  linarith only [htri,hdiff,hd,herr]

private theorem radial_evolution {n : ℕ} (u : PathShell n) {v : ℝ} (hv : 0 < v) (t : ℝ) :
    unitaryEvolution (pathHamiltonian ((1+t/v) • u)) v=unitaryEvolution (pathHamiltonian u) (v+t) := by
  let a := 1+t/v
  have he : pathHamiltonian (a • u)=(a:ℂ) • pathHamiltonian u := by
    change pathHamiltonianLM n (a • u)=_
    rw [map_smul]
    ext i j
    simp [Matrix.smul_apply,Complex.real_smul,smul_eq_mul,pathHamiltonianLM]
  rw [he,unitaryEvolution_smul_generator,show a*v=v+t by dsimp [a]; field_simp [hv.ne']]

/-- Every positive-date s-gate visit has a nearby Euclidean ball of
couplings on which s plus the new physical gate count is extensive.
Both the ball radius and the maximum displacement of its center scale
as 1/(v√N), uniformly over the entire trajectory. -/
theorem gaussian_hard_ball_at_visits :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let N := n+2
      let u := pathPauliDisorderShell ω n
      ∀ v : ℝ, 0 < v → ∀ s : ℕ, affordable u v (1/10) s →
        ∃ z : PathShell n, v*sqrt N*‖z-u‖ ≤ C ∧
          ∀ y : PathShell n, v*sqrt N*‖y-z‖ ≤ 1/100 →
            ∀ r : ℕ, affordable y v (1/10) r → c*(N:ℝ) ≤ (s:ℝ)+r := by
  obtain ⟨A,c,J,hA,hc,hwin⟩ := LocalPatches.gaussian_extensive_window_after_return 2 (by decide)
  obtain ⟨_,b,_,hb,hmass⟩ := gaussian_path_eventual_coefficient_mass
  obtain ⟨m,hm⟩ := exists_nat_gt (A^2)
  refine ⟨c,A*sqrt b,hc,mul_pos hA (sqrt_pos.mpr hb),?_⟩
  filter_upwards [hwin,hmass] with ω hω hbω
  filter_upwards [hω,hbω,eventually_ge_atTop m] with n hw hmassn hn
  intro N u v hv s hs
  let t := A/(N:ℝ)
  let z := (1+t/v) • u
  have hN : (0:ℝ) < N := by dsimp [N]; positivity
  have ht : 0 < t := div_pos hA hN
  have hNm : (m:ℝ) ≤ N := by exact_mod_cast (show m ≤ N by dsimp [N]; omega)
  have hscale : (N:ℝ)*t^2 ≤ 1 := by
    calc
      _ = A^2/(N:ℝ) := by dsimp [t]; field_simp [hN.ne']
      _ ≤ 1 := (div_le_one hN).mpr (hm.trans_le hNm).le
  obtain ⟨j,hj,hfloor,_⟩ := hw v s (1/10) (3/20) (by norm_num) (by norm_num) hs t le_rfl hscale
  have hsq : ‖u‖ ≤ sqrt b*sqrt N := by
    rw [←sqrt_mul hb.le,←Real.sqrt_sq (norm_nonneg u)]
    exact sqrt_le_sqrt hmassn.2
  have hz : z-u=(t/v) • u := by dsimp only [z]; rw [add_smul,one_smul,add_sub_cancel_left]
  refine ⟨z,?_,?_⟩
  · rw [hz,norm_smul,Real.norm_eq_abs,abs_of_pos (div_pos ht hv)]
    calc
      _ ≤ v*sqrt N*(t/v*(sqrt b*sqrt N)) := by gcongr
      _ = (t*(sqrt N)^2)*sqrt b := by field_simp [hv.ne']
      _ = A*sqrt b := by rw [Real.sq_sqrt hN.le,show t*(N:ℝ)=A from div_mul_cancel₀ _ hN.ne']
  · intro y hd r hr
    have hzy : v*sqrt N*‖z-y‖ ≤ 1/100 := by rwa [norm_sub_rev]
    have hh := affordable_ball hv hr hzy
    change HasProjectiveCircuitApproximation N (1/10+1/20:ℝ) r
      (unitaryEvolution (pathHamiltonian z) v) at hh
    rw [radial_evolution u hv t,show (1/10+1/20:ℝ)=3/20 by norm_num] at hh
    have hjr : (j:ℝ) ≤ (r:ℝ) := by exact_mod_cast hj.2 hh
    linarith only [hfloor,hjr]

#print axioms gaussian_hard_ball_at_visits
end
end GaloisForLFunctions.HTGeometry.ReturnSpacing.CouplingSensitivity
