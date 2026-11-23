import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.BlockApproximation.SeamEstimate
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.BlockApproximation.GaussianVariance
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.LocalSimulation.CubicMass

/-! # Gaussian spectral trace throughout the inverse-square-root time scale -/
open MeasureTheory Real Finset Filter
open scoped Topology
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
noncomputable section
open PeriodicCuts

private theorem fourth_sqrt_sqrt {x : ℝ} (hx : 0 ≤ x) : (sqrt (sqrt x))^4=x := by
  rw [show (4:ℕ)=2*2 from rfl,pow_mul,sq_sqrt (sqrt_nonneg _),sq_sqrt hx]

private theorem fourth_sqrt {x : ℝ} (hx : 0 ≤ x) : (sqrt x)^4=x^2 := by
  rw [show (4:ℕ)=2*2 from rfl,pow_mul,sq_sqrt hx]

private theorem abs_fourth (x : ℝ) : |x|^4=x^4 := by
  simp only [show (4:ℕ)=2*2 from rfl,pow_mul,sq_abs]

private theorem seam_share {n L : ℕ} (hL : L ≤ n+2) (u : PathShell n) {B : ℝ}
    (hm : (∑ l : PathLabel n, |u l|^4) ≤ B*(n+2:ℕ)) :
    (seamMass L u)^2*L ≤ 24*B*((n+2:ℕ):ℝ)^2 := by
  let N := n+2
  have hc : ((N/L+1:ℕ):ℝ)*L ≤ 2*(N:ℝ) := by
    exact_mod_cast (show (N/L+1)*L ≤ 2*N by
      rw [Nat.add_mul,Nat.one_mul,two_mul]
      exact Nat.add_le_add (Nat.div_mul_le_self ..) hL)
  have hBN : 0 ≤ B*(N:ℝ) := (sum_nonneg fun _ _ => by positivity).trans hm
  calc
    _ ≤ (12*((N/L+1:ℕ):ℝ)*(∑ l : PathLabel n, |u l|^4))*L :=
      mul_le_mul_of_nonneg_right (seam_mass_sq L u) (Nat.cast_nonneg _)
    _ ≤ (12*((N/L+1:ℕ):ℝ)*(B*N))*L :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hm (by positivity)) (Nat.cast_nonneg _)
    _ = (12*(B*N))*(((N/L+1:ℕ):ℝ)*L) := by ring
    _ ≤ (12*(B*N))*(2*N) := mul_le_mul_of_nonneg_left hc (mul_nonneg (by norm_num) hBN)
    _ = _ := by dsimp only [N]; ring

private theorem critical_comparison {n L : ℕ} (hL : 0 < L) (hLN : L ≤ n+2)
    (u : PathShell n) {B R b d t : ℝ} (hB : 0 ≤ B) (hb : 0 < b) (hd : 0 < d)
    (hm : (∑ l : PathLabel n, |u l|^4) ≤ B*(n+2:ℕ))
    (hv : shellVariance u ≤ 13*(n+2:ℕ)) (ht : (n+2:ℕ)*t^2 ≤ R)
    (hcut : 24*B*R^2 ≤ b^4*L) (hpeak : B*R^2 ≤ d^4*(n+2:ℕ)) :
    ‖shellTrace u t-(exp (-(t^2*shellVariance u/2)):ℂ)‖ ≤ b+36*L*d*(13*R)+b^2/2 := by
  let N : ℝ := (n+2:ℕ)
  let M := sqrt (sqrt (B*N))
  let e := seamMass L u
  have hN : 0 < N := by dsimp only [N]; positivity
  have hLR : (0:ℝ) < L := Nat.cast_pos.mpr hL
  have hM : M^4=B*N := fourth_sqrt_sqrt (mul_nonneg hB hN.le)
  have ht₂ : N^2*t^4 ≤ R^2 := by
    simpa only [mul_pow,←pow_mul] using pow_le_pow_left₀ (mul_nonneg hN.le (sq_nonneg t)) ht 2
  have he : 0 ≤ e := seamMass_nonneg L u
  have hseam : |t| *sqrt e ≤ b := by
    have hh : (|t| *sqrt e)^4*L ≤ b^4*L := calc
      _ = t^4*(e^2*L) := by rw [mul_pow,abs_fourth,fourth_sqrt he]; ring
      _ ≤ t^4*(24*B*N^2) := mul_le_mul_of_nonneg_left (seam_share hLN u hm) (by positivity)
      _ = 24*B*(N^2*t^4) := by ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left ht₂ (mul_nonneg (by norm_num) hB)).trans hcut
    exact le_of_not_gt fun h => (mul_lt_mul_of_pos_right (pow_lt_pow_left₀ h hb.le (by decide : 4≠0)) hLR).not_ge hh
  have hsmall : |t| *M ≤ d := by
    have hh : (|t| *M)^4*N ≤ d^4*N := calc
      _ = B*(N^2*t^4) := by rw [mul_pow,abs_fourth,hM]; ring
      _ ≤ _ := (mul_le_mul_of_nonneg_left ht₂ hB).trans hpeak
    exact le_of_not_gt fun h => (mul_lt_mul_of_pos_right (pow_lt_pow_left₀ h hd.le (by decide : 4≠0)) hN).not_ge hh
  have hmax (l : PathLabel n) : |u l| ≤ M := by
    have hh : |u l|^4 ≤ M^4 := (single_le_sum (fun j (_ : j∈univ) => pow_nonneg (abs_nonneg (u j)) 4)
      (mem_univ l)).trans (hm.trans_eq hM.symm)
    exact le_of_not_gt fun h => (pow_lt_pow_left₀ h (sqrt_nonneg _) (by decide : 4≠0)).not_ge hh
  have hvar : t^2*shellVariance u ≤ 13*R :=
    ((mul_le_mul_of_nonneg_left hv (sq_nonneg t)).trans_eq (show t^2*(13*N)=13*(N*t^2) by ring)).trans
      (mul_le_mul_of_nonneg_left ht (by norm_num))
  have hp : 36* |t|^3*L*M*shellVariance u ≤ 36*L*d*(13*R) := by
    have halg : 36* |t|^3*L*M*shellVariance u = 36*L*(|t| *M)*(t^2*shellVariance u) := by
      rw [pow_succ, sq_abs]; ring
    rw [halg]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hsmall (by positivity)) hvar
      (mul_nonneg (sq_nonneg _) (sum_nonneg fun _ _ => sq_nonneg _)) (by positivity)
  have hbis := pow_le_pow_left₀ (mul_nonneg (abs_nonneg t) (sqrt_nonneg e)) hseam 2
  rw [mul_pow,sq_abs,sq_sqrt he] at hbis
  exact (periodic_gaussian_error hL u (sqrt_nonneg _) hmax t).trans
    (add_le_add (add_le_add hseam hp) (div_le_div_of_nonneg_right hbis (by norm_num)))

/-- Almost surely on one infinite Gaussian chain, the spectral trace approaches
its Gaussian with the sample variance, uniformly throughout bounded Nt². -/
theorem gaussian_sample_characteristic :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ R > (0:ℝ), ∀ ε > (0:ℝ), ∀ᶠ n : ℕ in atTop,
      ∀ t : ℝ, (n+2:ℕ)*t^2 ≤ R →
        let u := pathPauliDisorderShell ω n
        ‖shellTrace u t-(exp (-(t^2*shellVariance u/2)):ℂ)‖ < ε := by
  obtain ⟨B,hB,h₄⟩ := LocalPatches.gaussian_power_mass 4
  filter_upwards [h₄,gaussian_variance_per_site] with ω hm hv
  intro R hR ε hε
  let b := min 1 (ε/4)
  have hb : 0 < b := lt_min zero_lt_one (by positivity)
  obtain ⟨L,hL⟩ := exists_nat_gt (24*B*R^2/b^4)
  have hL' : 0 < L := Nat.cast_pos.mp ((by positivity : 0 ≤ 24*B*R^2/b^4).trans_lt hL)
  have hcut : 24*B*R^2 ≤ b^4*L := by
    simpa only [mul_comm (L:ℝ)] using ((div_lt_iff₀ (pow_pos hb 4)).mp hL).le
  let Q := 36*(L:ℝ)*(13*R)
  have hQ : 0 < Q := by dsimp only [Q]; positivity
  let d := b/Q
  have hd : 0 < d := div_pos hb hQ
  obtain ⟨J,hJ⟩ := exists_nat_gt (B*R^2/d^4)
  filter_upwards [hm,hv.eventually_lt_const (by norm_num : (12:ℝ)<13),
    eventually_ge_atTop L,eventually_ge_atTop J] with n hmn hvn hLn hJn
  intro t ht u
  have hN : (0:ℝ) < (n+2:ℕ) := by positivity
  have hJ' : B*R^2/d^4 < ((n+2:ℕ):ℝ) := hJ.trans_le (by exact_mod_cast (show J ≤ n+2 by omega))
  have h := critical_comparison hL' (by omega) u hB.le hb hd hmn
    ((div_lt_iff₀ hN).mp hvn).le ht hcut
    (by simpa only [mul_comm (d^4)] using ((div_lt_iff₀ (pow_pos hd 4)).mp hJ').le)
  have hprod : 36*(L:ℝ)*d*(13*R)=b := by
    change _*(b/Q)*_=b
    rw [show 36*(L:ℝ)*(b/Q)*(13*R)=b/Q*Q by dsimp only [Q]; ring,div_mul_cancel₀ _ hQ.ne']
  have hsq : b^2 ≤ b := by simpa only [sq,mul_one] using mul_le_mul_of_nonneg_left (min_le_left 1 (ε/4)) hb.le
  rw [hprod] at h
  exact h.trans_lt (by linarith only [hsq,show b ≤ ε/4 from min_le_right ..,hε])

#print axioms gaussian_sample_characteristic
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.Bulk
