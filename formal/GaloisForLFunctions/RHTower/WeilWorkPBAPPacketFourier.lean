import GaloisForLFunctions.RHTower.WeilWorkPBAPGramPackets
import GaloisForLFunctions.RHTower.Sieve.DirichletMeanValueSharp
import GaloisForLFunctions.RHTower.Sieve.DirichletIntegralMeanValue
import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon
import GaloisForLFunctions.RHTower.ZetaWeilFiniteLevelInertia
import GaloisForLFunctions.HTGeometry.IntegralCauchySchwarz
import GaloisForLFunctions.RHTower.WeilDeletionTestKit

/-!
# Fourier mass of narrow integer packets

Literal packet mass and Fourier factorization, with an explicit mean-square bound.
No integer-null or Weil-positivity premise is used. These estimates support the
full signed-energy audit recorded in the WP01 packet-energy paper.
-/
open Complex MeasureTheory Zeta23
open scoped BigOperators
noncomputable section
namespace RHTower.WeilWorkPBAP
open WeilOneSided

def packetL1 (N L : ℕ) : ℝ := ∫ u, narrowBump (N*L) u

theorem packetL1_nonneg (N L : ℕ) : 0 ≤ packetL1 N L :=
  integral_nonneg fun _ => (narrowBump _).nonneg

theorem packetL1_sq_le (N L : ℕ) :
    (packetL1 N L)^2 ≤ (2 / (4*((N*L:ℕ)+1:ℝ))) * packetMass N L := by
  let r : ℝ := 1 / (4*((N*L:ℕ)+1:ℝ))
  have hr : 0 ≤ r := by dsimp [r]; positivity
  have hz : ∀ u : ℝ, u ∉ Set.Icc (-r) r → narrowBump (N*L) u = 0 := by
    intro u hu
    apply (narrowBump _).zero_of_le_dist
    change r ≤ dist u 0
    rw [Real.dist_eq, sub_zero]
    by_contra hh
    exact hu (abs_le.mp (le_of_lt (lt_of_not_ge hh)))
  have h1 := setIntegral_eq_integral_of_forall_compl_eq_zero (μ := volume) hz
  have h2 := setIntegral_eq_integral_of_forall_compl_eq_zero
    (μ := volume) (f := fun u => (narrowBump (N*L) u)^2)
    (fun u hu => by rw [hz u hu, zero_pow (by decide)])
  have hcs := GaloisForLFunctions.HTGeometry.sq_integral_mul_le
    (μ := volume.restrict (Set.Icc (-r) r))
    (f := fun u => narrowBump (N*L) u) (g := fun _ => (1:ℝ))
    (narrowBump _).continuous.aestronglyMeasurable continuous_const.aestronglyMeasurable
    ((narrowBump _).continuous.pow 2).integrableOn_Icc
    (continuous_const.pow 2).integrableOn_Icc
  simp only [mul_one, one_pow] at hcs
  rw [h1, h2, setIntegral_const, Real.volume_real_Icc_of_le (by linarith : -r ≤ r)] at hcs
  change (packetL1 N L)^2 ≤ _ at hcs
  simpa [smul_eq_mul, packetMass, r, sub_neg_eq_add, mul_comm, div_eq_mul_inv,
    ← two_mul] using hcs

theorem gramPacket_mass (N L : ℕ) (hL : 1 ≤ L) (c : ℕ → ℂ) :
    (∫ u, ‖gramPacket N L c u‖^2) = packetMass N L *
      ∑ n ∈ Finset.Icc 1 N, ‖c n‖^2 := by
  have hs := gramPacket_rational_sample N L c (a := 1) (b := 1)
    (by omega) (by omega) hL
  simp only [sub_self, one_mul] at hs
  have hzero : EF.weilTest (gramPacket N L c) (gramPacket N L c) 0 =
      ((∫u, ‖gramPacket N L c u‖^2 : ℝ):ℂ) := by
    rw [weilTest_apply, ← integral_complex_ofReal]
    apply integral_congr_ae
    filter_upwards [] with u
    simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hzero] at hs
  simp only [Finset.sum_ite_eq', Complex.mul_conj, Complex.normSq_eq_norm_sq] at hs
  simp only [Finset.sum_congr rfl (fun n hn => if_pos hn)] at hs
  exact_mod_cast hs

theorem paperFT_gramPacket (N L : ℕ) (c : ℕ → ℂ) (z : ℂ) :
    paperFT (gramPacket N L c) z = paperFT (narrowBumpC (N*L)) z *
      ∑ n ∈ Finset.Icc 1 N, c n * Complex.exp (Complex.I * z * resPt N n) := by
  classical
  change paperFT (fun u => ∑ m ∈ Finset.Icc 1 N,
    c m * narrowBumpC (N*L) (u-resPt N m)) z = _
  rw [paperFT_finset_sum (Finset.Icc 1 N) c
    (f := fun n u => narrowBumpC (N*L) (u-resPt N n))
    (fun n => (contDiff_narrowBumpC (N*L)).continuous.comp (continuous_id.sub continuous_const))
    (fun n => (hasCompactSupport_narrowBumpC (N*L)).comp_homeomorph
      (Homeomorph.subRight (resPt N n))) z, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [paperFT_translate']
  ring

theorem paperFT_gramPacket_real (N L : ℕ) (c : ℕ → ℂ) (t : ℝ) :
    paperFT (gramPacket N L c) (t:ℂ) =
      paperFT (narrowBumpC (N*L)) (t:ℂ) *
      Complex.exp (-Complex.I * (t:ℂ) * ((Real.log N/2:ℝ):ℂ)) *
      Sieve.dirPoly N (fun j => c ((j:ℕ)+1)) t := by
  classical
  rw [paperFT_gramPacket, Sieve.dirPoly]
  have hsum : ∑ j : Fin N, c ((j:ℕ)+1) *
      Complex.exp (((t*Real.log ((j:ℕ)+1):ℝ):ℂ)*Complex.I) =
      ∑ n ∈ Finset.Icc 1 N, c n * Complex.exp (((t*Real.log n:ℝ):ℂ)*Complex.I) := by
    rw [← Sieve.image_succ_univ N, Finset.sum_image (Sieve.succ_injOn N)]
    simp only [Nat.cast_add, Nat.cast_one]
  rw [hsum, mul_assoc]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n _
  have he : Complex.I*(t:ℂ)*(resPt N n:ℂ) =
      -Complex.I*(t:ℂ)*((Real.log N/2:ℝ):ℂ) +
      (((t*Real.log n:ℝ):ℂ)*Complex.I) := by
    unfold resPt
    push_cast
    ring
  rw [he, Complex.exp_add]
  ring

theorem norm_paperFT_gramPacket_real (N L : ℕ) (c : ℕ → ℂ) (t : ℝ) :
    ‖paperFT (gramPacket N L c) (t:ℂ)‖ =
      ‖paperFT (narrowBumpC (N*L)) (t:ℂ)‖ *
      ‖Sieve.dirPoly N (fun j => c ((j:ℕ)+1)) t‖ := by
  rw [paperFT_gramPacket_real, norm_mul, norm_mul]
  simp only [Complex.norm_exp, Complex.mul_re, Complex.neg_re, Complex.I_re,
    Complex.ofReal_re, Complex.ofReal_im, neg_zero, zero_mul, mul_zero, sub_zero,
    Real.exp_zero, mul_one]


/-- The literal bump envelope, including non-real Fourier arguments. -/
theorem norm_paperFT_narrowBumpC_le (N L : ℕ) (z : ℂ) :
    ‖paperFT (narrowBumpC (N*L)) z‖ ≤
      Real.exp (1/(4*((N*L:ℕ)+1:ℝ)) * |z.im|) * packetL1 N L := by
  let r : ℝ := 1/(4*((N*L:ℕ)+1:ℝ))
  have hb : Integrable (fun u => narrowBump (N*L) u) :=
    (narrowBump (N*L)).continuous.integrable_of_hasCompactSupport
    (narrowBump (N*L)).hasCompactSupport
  calc
    ‖paperFT (narrowBumpC (N*L)) z‖ ≤
        ∫ u, Real.exp (r*|z.im|) * narrowBump (N*L) u := by
      apply norm_integral_le_of_norm_le (hb.const_mul _)
      filter_upwards [] with u
      by_cases hu : |u| ≤ r
      · rw [norm_mul]
        have hn : ‖narrowBumpC (N*L) u‖ = narrowBump (N*L) u := by
          simp only [narrowBumpC, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (narrowBump _).nonneg]
        rw [hn, mul_comm (Real.exp _) _]
        exact mul_le_mul_of_nonneg_left (WeilDeletion.norm_exp_I_mul_le hu)
          (narrowBump _).nonneg
      · have hz := narrowBumpC_eq_zero (N*L) (lt_of_not_ge hu)
        have hrz : narrowBump (N*L) u = 0 := Complex.ofReal_eq_zero.mp hz
        simp only [hz, hrz, zero_mul, norm_zero, mul_zero, le_refl]
    _ = _ := by rw [integral_const_mul]; rfl

/-- Montgomery–Vaughan on a symmetric interval, using the corpus constant 104. -/
theorem dirPoly_symmetric_mean_square (N : ℕ) (c : Fin N → ℂ) (T : ℝ) :
    (∫ t in (-T)..T, ‖Sieve.dirPoly N c t‖^2) ≤
      (2*T + 208*N) * ∑ j, ‖c j‖^2 := by
  have hp := (abs_le.mp (Sieve.dirichlet_meanValue_sharp N c T)).2
  have hn := (abs_le.mp (Sieve.dirichlet_meanValue_sharp N c (-T))).1
  have hc := (Sieve.continuous_dirPoly N c).norm.pow 2
  have hs := intervalIntegral.integral_add_adjacent_intervals (μ := volume)
    (hc.intervalIntegrable (-T) 0) (hc.intervalIntegrable 0 T)
  rw [intervalIntegral.integral_symm 0 (-T)] at hs
  simp only [Pi.pow_apply] at hs
  have hw : (∑ j : Fin N, ((j : ℕ)+1:ℝ)*‖c j‖^2) ≤
      (N:ℝ)*∑ j, ‖c j‖^2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact_mod_cast (Nat.succ_le_iff.mpr j.2)
  linarith

/-- The actual packet spectrum obeys the envelope times mean-square bound. -/
theorem gramPacket_low_mass_envelope (N L : ℕ) (c : ℕ → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (-T)..T, ‖paperFT (gramPacket N L c) (t:ℂ)‖^2) ≤
      (packetL1 N L)^2 * (2*T+208*N) * ∑ n ∈ Finset.Icc 1 N, ‖c n‖^2 := by
  have hpc : Continuous fun t : ℝ => paperFT (gramPacket N L c) (t:ℂ) :=
    (Zeta23.WeilEF.differentiable_paperFT (contDiff_gramPacket N L c).continuous
      (hasCompactSupport_gramPacket N L c)).continuous.comp Complex.continuous_ofReal
  have hc := (Sieve.continuous_dirPoly N (fun j => c ((j:ℕ)+1))).norm.pow 2
  have hbound : ∀ t : ℝ, ‖paperFT (gramPacket N L c) (t:ℂ)‖^2 ≤
      (packetL1 N L)^2 * ‖Sieve.dirPoly N (fun j => c ((j:ℕ)+1)) t‖^2 := by
    intro t
    rw [norm_paperFT_gramPacket_real, mul_pow]
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    have hb := norm_paperFT_narrowBumpC_le N L (t:ℂ)
    simp only [Complex.ofReal_im, abs_zero, mul_zero, Real.exp_zero, one_mul] at hb
    nlinarith [norm_nonneg (paperFT (narrowBumpC (N*L)) (t:ℂ)), packetL1_nonneg N L]
  calc
    (∫ t in (-T)..T, ‖paperFT (gramPacket N L c) (t:ℂ)‖^2) ≤
        ∫ t in (-T)..T, (packetL1 N L)^2 *
          ‖Sieve.dirPoly N (fun j => c ((j:ℕ)+1)) t‖^2 :=
      intervalIntegral.integral_mono (by linarith)
        ((hpc.norm.pow 2).intervalIntegrable _ _)
        ((hc.const_mul _).intervalIntegrable _ _) hbound
    _ = (packetL1 N L)^2 *
        ∫ t in (-T)..T, ‖Sieve.dirPoly N (fun j => c ((j:ℕ)+1)) t‖^2 := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ (packetL1 N L)^2 * ((2*T+208*N) * ∑ j : Fin N, ‖c ((j:ℕ)+1)‖^2) :=
      mul_le_mul_of_nonneg_left (dirPoly_symmetric_mean_square N _ T) (sq_nonneg _)
    _ = _ := by rw [Sieve.sum_fin_eq_sum_Icc N (fun n => ‖c n‖^2)]; ring

/-- Uniform coefficient-independent low-frequency mass bound. -/
theorem gramPacket_low_mass_le (N L : ℕ) (hL : 104 ≤ L) (c : ℕ → ℂ) :
    (∫ t in (-((N*L:ℕ):ℝ))..((N*L:ℕ):ℝ),
      ‖paperFT (gramPacket N L c) (t:ℂ)‖^2) ≤
      2 * packetMass N L * ∑ n ∈ Finset.Icc 1 N, ‖c n‖^2 := by
  have henv := gramPacket_low_mass_envelope N L c (T := ((N*L:ℕ):ℝ)) (by positivity)
  have hm := packetL1_sq_le N L
  have hS : 0 ≤ ∑ n ∈ Finset.Icc 1 N, ‖c n‖^2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hM := (packetMass_pos N L).le
  have hLr : (104:ℝ) ≤ L := by exact_mod_cast hL
  have hN : (0:ℝ) ≤ N := Nat.cast_nonneg _
  have hNL : (0:ℝ) ≤ (N*L:ℕ) := Nat.cast_nonneg _
  have hd : 0 < 4 * (((N*L:ℕ):ℝ)+1) := by positivity
  have hr : (2 / (4 * (((N*L:ℕ):ℝ)+1))) *
      (2*((N*L:ℕ):ℝ)+208*N) ≤ 2 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hd]
    push_cast
    nlinarith [mul_nonneg hN (sub_nonneg.mpr hLr)]
  calc
    _ ≤ (packetL1 N L)^2 * (2*((N*L:ℕ):ℝ)+208*N) *
        ∑ n ∈ Finset.Icc 1 N, ‖c n‖^2 := henv
    _ ≤ ((2 / (4*(((N*L:ℕ):ℝ)+1)))*packetMass N L) *
        (2*((N*L:ℕ):ℝ)+208*N) * ∑ n ∈ Finset.Icc 1 N, ‖c n‖^2 := by
      apply mul_le_mul_of_nonneg_right _ hS
      exact mul_le_mul_of_nonneg_right hm (by positivity)
    _ = ((2 / (4*(((N*L:ℕ):ℝ)+1)))*(2*((N*L:ℕ):ℝ)+208*N)) *
        packetMass N L * ∑ n ∈ Finset.Icc 1 N, ‖c n‖^2 := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hr hM) hS

end RHTower.WeilWorkPBAP
