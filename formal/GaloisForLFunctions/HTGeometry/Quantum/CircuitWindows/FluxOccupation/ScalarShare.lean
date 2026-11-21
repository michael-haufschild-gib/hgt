import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.FluxOccupation.GaussianLaw
import GaloisForLFunctions.HTGeometry.DyadicExponentGeometricSummable

/-! # Vanishing scalar share of affordable time at fixed physical error -/
open Matrix MeasureTheory Filter Topology Set Real
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.FluxOccupation
noncomputable section
open SharpOccupation

private theorem eventually_gain (R : ℝ) (hR : 1≤R) :
    ∀ᶠ k : ℕ in atTop, 4*R*(128*π*(Fintype.card (PathLabel (k+1)):ℝ)) < sqrt ((2:ℝ)^(k+3)) := by
  obtain ⟨m,hm⟩ := exists_nat_gt (4*R*(128*π*48))
  obtain ⟨K,hK⟩ := eventually_atTop.mp (eventually_mul_le_two_pow m)
  filter_upwards [eventually_ge_atTop (2*K+4)] with k hk
  let l := k/2
  have hl : K≤l := by dsimp only [l]; omega
  have hl' : (0:ℝ)<l := Nat.cast_pos.mpr (by dsimp only [l]; omega)
  have hj : Fintype.card (PathLabel (k+1)) ≤ 48*l := by
    simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    dsimp only [l]
    omega
  have hsq : (2:ℝ)^l ≤ sqrt ((2:ℝ)^(k+3)) := by
    apply (Real.le_sqrt (by positivity) (by positivity)).mpr
    rw [←pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by dsimp only [l]; omega)
  calc
    _ ≤ 4*R*(128*π*(48*(l:ℝ))) := by gcongr; exact_mod_cast hj
    _ = (4*R*(128*π*48))*(l:ℝ) := by ring
    _ < (m:ℝ)*l := mul_lt_mul_of_pos_right hm hl'
    _ ≤ (2:ℝ)^l := by exact_mod_cast hK l hl
    _ ≤ _ := hsq

/-- At each fixed error up to 1/4, arbitrarily large ratios are attained
on every sufficiently long prefix, even when the observation origin is
chosen from the draw. The long observation limit comes first. -/
theorem gaussian_vanishing_scalar_share :
    ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ R ≥ (1:ℝ), ∀ᶠ k : ℕ in atTop,
      let N := k+3
      let H : selfAdjoint (Register N) := ⟨pathHamiltonian (pathPauliDisorderShell ω (k+1)),isSelfAdjoint_pathHamiltonian _⟩
      let J := Fintype.card (PathLabel (k+1))
      ∀ ε : ℝ, 0<ε → ε≤1/4 → ∀ a : ℝ, ∀ᶠ T : ℝ in atTop,
        R*visitFraction H 0 ε a T < visitFraction H J ε a T := by
  filter_upwards [gaussian_fixed_error_occupation_gain,gaussian_path_all_prefixes_maximally_projective] with ω hg hi
  intro R hR
  filter_upwards [eventually_gain R hR] with k hk
  intro N H J ε hε hε' a
  let D : ℕ := 2^N
  let p := (D:ℝ)*(physicalArc ε)^(D-1)
  have hr : ε<sqrt 2 := by nlinarith only [hε',Real.sq_sqrt (by norm_num : (0:ℝ)≤2),Real.sqrt_nonneg 2]
  have hx := (physicalArc_spec hε hr).1.1
  have hp : 0<p := mul_pos (by dsimp only [D]; positivity) (pow_pos hx _)
  have hs := (ShortTimeProducts.scalar_fraction H (hi k) hε hr 0).eventually_const_lt (half_lt_self hp)
  let m (s : ℕ) (b T : ℝ) := volume.real (visitSet H s ε ∩ Icc b T)
  have hoff (s : ℕ) (T : ℝ) : |m s a T-m s 0 T| ≤ |a| := by
    simpa only [m,sub_zero] using abs_occupation_sub_le_start_displacement (visitSet H s ε) a 0 T
  have hg' : 4*R*(128*π*(J:ℝ)) < sqrt (D:ℝ) := by simpa only [D,N,Nat.cast_pow,Nat.cast_ofNat] using hk
  filter_upwards [hg k ε hε hε',hs,eventually_gt_atTop (|a|/(p/2)),eventually_gt_atTop a] with T hgT hscalar hT ha
  have hpos : 0<T := (div_nonneg (abs_nonneg _) (half_pos hp).le).trans_lt hT
  have h0 : |a| < m 0 0 T := by
    change p/2 < m 0 0 T/(T-0) at hscalar
    rw [sub_zero,lt_div_iff₀ hpos] at hscalar
    exact ((div_lt_iff₀ (half_pos hp)).mp hT).trans (by rwa [mul_comm])
  have hJ : 0<128*π*(J:ℝ) := by
    have hj : 0<J := Fintype.card_pos
    positivity
  have hmul : 4*R*m 0 0 T < m J 0 T := by
    change sqrt (D:ℝ)*(m 0 0 T/(T-0)) ≤ 128*π*(J:ℝ)*(m J 0 T/(T-0)) at hgT
    rw [sub_zero,←mul_div_assoc,←mul_div_assoc,div_le_div_iff_of_pos_right hpos] at hgT
    have h := (mul_lt_mul_of_pos_right hg' ((abs_nonneg a).trans_lt h0)).trans_le hgT
    apply (mul_lt_mul_iff_right₀ hJ).mp
    linarith only [h]
  have h1 := (abs_le.mp (hoff 0 T)).2
  have h2 := (abs_le.mp (hoff J T)).1
  have h3 := mul_le_mul_of_nonneg_left h1 (zero_le_one.trans hR)
  have h4 := mul_le_mul_of_nonneg_left h0.le (zero_le_one.trans hR)
  have h5 := mul_le_mul_of_nonneg_right hR ((abs_nonneg a).trans h0.le)
  change R*(m 0 a T/(T-a)) < m J a T/(T-a)
  rw [←mul_div_assoc,div_lt_div_iff_of_pos_right (sub_pos.mpr ha)]
  linarith only [hmul,h2,h3,h4,h5,h0,abs_nonneg a]

#print axioms gaussian_vanishing_scalar_share
end
end GaloisForLFunctions.HTGeometry.FluxOccupation
