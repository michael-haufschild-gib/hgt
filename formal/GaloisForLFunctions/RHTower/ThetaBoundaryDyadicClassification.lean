import Mathlib.Analysis.SpecificLimits.Normed
import GaloisForLFunctions.RHTower.WindingDivisor
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-!
# What the theta boundary dyadic identity retains

The equation `F(x+1)+F(x)=F(4*x)/2` does not determine its bounded
2-periodic solutions. Their anti-periodic primitive `A(x)=(F(x)-F(x+1))/2`
is arbitrary; reconstruction is the uniformly convergent geometric series
`sum 4^(-n) A(4^n*x)`. We prove both inverse identities, continuity,
a quantitative finite-depth remainder, and the norm bound.

More strongly, continuous nowhere-zero solutions with zero mean and the same
normalized theta endpoint values have winding `-(2*k+1)` for every `k`.
Thus the dyadic law and these anchors do not constrain the boundary winding.
This does not identify such loops with the actual theta renewal feedback,
and does not prove or falsify RH.
-/

open Filter Topology
open scoped BigOperators
noncomputable section
namespace RHTower.DyadicBoundary

def Primitive (F : ℝ → ℂ) (x : ℝ) : ℂ := (F x - F (x+1))/2

def Law (F : ℝ → ℂ) : Prop := ∀ x, F (x+1) + F x = F (4*x)/2

def Reconstruction (A : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, (1/4 : ℂ)^n * A ((4:ℝ)^n*x)

private theorem norm_quarter : ‖(1/4 : ℂ)‖ = (1/4 : ℝ) := by norm_num

private theorem geometric_summable (M : ℝ) :
    Summable (fun n : ℕ => (1/4 : ℝ)^n*M) :=
  (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/4 : ℝ)‖ < 1)).mul_right M

private theorem term_bound {A : ℝ → ℂ} {M : ℝ} (hA : ∀ x, ‖A x‖ ≤ M)
    (n : ℕ) (x : ℝ) : ‖(1/4 : ℂ)^n * A ((4:ℝ)^n*x)‖ ≤ (1/4 : ℝ)^n*M := by
  rw [norm_mul, norm_pow, norm_quarter]
  exact mul_le_mul_of_nonneg_left (hA _) (by positivity)

theorem reconstruction_summable {A : ℝ → ℂ} {M : ℝ} (hA : ∀ x, ‖A x‖ ≤ M) (x : ℝ) :
    Summable (fun n : ℕ => (1/4 : ℂ)^n * A ((4:ℝ)^n*x)) :=
  (geometric_summable M).of_norm_bounded (fun n => term_bound hA n x)

theorem continuous_reconstruction {A : ℝ → ℂ} {M : ℝ} (hA : ∀ x, ‖A x‖ ≤ M)
    (hc : Continuous A) : Continuous (Reconstruction A) := by
  apply continuous_tsum (u := fun n : ℕ => (1/4 : ℝ)^n*M)
  · intro n
    exact continuous_const.mul (hc.comp (continuous_const.mul continuous_id))
  · exact geometric_summable M
  · exact term_bound hA

theorem primitive_antiperiodic {F : ℝ → ℂ} (hp : Function.Periodic F 2) :
    Function.Antiperiodic (Primitive F) 1 := by
  intro x
  unfold Primitive
  rw [show x+1+1 = x+2 by ring, hp x]
  ring

theorem law_iff_refinement (F : ℝ → ℂ) :
    Law F ↔ ∀ x, F x = Primitive F x + (1/4 : ℂ)*F (4*x) := by
  unfold Law Primitive
  constructor
  · intro h x
    linear_combination (h x) / 2
  · intro h x
    linear_combination 2 * h x

theorem finite_reconstruction {F : ℝ → ℂ} (hF : Law F) (N : ℕ) (x : ℝ) :
    F x = (∑ n ∈ Finset.range N, (1/4 : ℂ)^n * Primitive F ((4:ℝ)^n*x)) +
      (1/4 : ℂ)^N * F ((4:ℝ)^N*x) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, pow_succ, pow_succ]
    have hstep := (law_iff_refinement F).mp hF ((4:ℝ)^N*x)
    rw [show (4:ℝ)^N*4*x = 4*((4:ℝ)^N*x) by ring]
    linear_combination ih + (1/4:ℂ)^N * hstep

theorem finite_reconstruction_error {F : ℝ → ℂ} {M : ℝ} (hF : Law F)
    (hM : ∀ x, ‖F x‖ ≤ M) (N : ℕ) (x : ℝ) :
    ‖F x - ∑ n ∈ Finset.range N, (1/4 : ℂ)^n * Primitive F ((4:ℝ)^n*x)‖ ≤
      (1/4 : ℝ)^N*M := by
  rw [sub_eq_iff_eq_add.mpr (by simpa only [add_comm] using finite_reconstruction hF N x)]
  exact term_bound hM N x

private theorem primitive_bound {F : ℝ → ℂ} {M : ℝ} (hM : ∀ x, ‖F x‖ ≤ M) (x : ℝ) :
    ‖Primitive F x‖ ≤ M := by
  rw [Primitive, norm_div]
  norm_num only [Complex.norm_ofNat]
  apply (div_le_div_of_nonneg_right (norm_sub_le _ _) (by norm_num : (0:ℝ) ≤ 2)).trans
  linarith [hM x, hM (x+1)]

theorem reconstruction_primitive {F : ℝ → ℂ} {M : ℝ} (hF : Law F)
    (hM : ∀ x, ‖F x‖ ≤ M) : Reconstruction (Primitive F) = F := by
  funext x
  have ht : Tendsto (fun N : ℕ => (1/4 : ℝ)^N*M) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_norm_lt_one
      (by norm_num : ‖(1/4 : ℝ)‖ < 1)).mul_const M
  have hr : Tendsto (fun N : ℕ => (1/4 : ℂ)^N * F ((4:ℝ)^N*x)) atTop (𝓝 0) :=
    squeeze_zero_norm (fun N => term_bound hM N x) ht
  have hs : Tendsto (fun N => ∑ n ∈ Finset.range N,
      (1/4 : ℂ)^n * Primitive F ((4:ℝ)^n*x)) atTop (𝓝 (F x)) := by
    have hh := (tendsto_const_nhds (x := F x)).sub hr
    simp only [sub_zero] at hh
    convert hh using 1
    funext N
    linear_combination -(finite_reconstruction hF N x)
  exact tendsto_nhds_unique
    (reconstruction_summable (primitive_bound hM) x).hasSum.tendsto_sum_nat hs

theorem reconstruction_refinement {A : ℝ → ℂ} {M : ℝ} (hA : ∀ x, ‖A x‖ ≤ M) (x : ℝ) :
    Reconstruction A x = A x + (1/4 : ℂ)*Reconstruction A (4*x) := by
  rw [Reconstruction, (reconstruction_summable hA x).tsum_eq_zero_add]
  simp only [pow_zero, one_mul]
  congr 1
  rw [Reconstruction, ← tsum_mul_left]
  apply tsum_congr
  intro n
  rw [pow_succ, pow_succ]
  rw [show (4:ℝ)^n*4*x = (4:ℝ)^n*(4*x) by ring]
  ring

theorem reconstruction_periodic {A : ℝ → ℂ} (ha : Function.Antiperiodic A 1) :
    Function.Periodic (Reconstruction A) 2 := by
  have hp : Function.Periodic A 2 := by simpa using ha.periodic
  intro x
  apply tsum_congr
  intro n
  congr 1
  have hh := hp.nat_mul (4^n) ((4:ℝ)^n*x)
  convert hh using 1
  push_cast
  congr 1
  ring

theorem reconstruction_shift_four {A : ℝ → ℂ} (ha : Function.Antiperiodic A 1) (x : ℝ) :
    Reconstruction A (4*(x+1)) = Reconstruction A (4*x) := by
  have hh := (reconstruction_periodic ha).nat_mul 2 (4*x)
  convert hh using 1
  congr 1
  ring

theorem primitive_reconstruction {A : ℝ → ℂ} {M : ℝ}
    (hA : ∀ x, ‖A x‖ ≤ M) (ha : Function.Antiperiodic A 1) :
    Primitive (Reconstruction A) = A := by
  funext x
  rw [Primitive, reconstruction_refinement hA x, reconstruction_refinement hA (x+1),
    ha x, reconstruction_shift_four ha x]
  ring

theorem law_reconstruction {A : ℝ → ℂ} {M : ℝ}
    (hA : ∀ x, ‖A x‖ ≤ M) (ha : Function.Antiperiodic A 1) :
    Law (Reconstruction A) := by
  rw [law_iff_refinement, primitive_reconstruction hA ha]
  exact reconstruction_refinement hA

theorem reconstruction_bound {A : ℝ → ℂ} {M : ℝ} (hA : ∀ x, ‖A x‖ ≤ M) (x : ℝ) :
    ‖Reconstruction A x‖ ≤ (4/3:ℝ)*M := by
  have hg : HasSum (fun n : ℕ => (1/4:ℝ)^n*M) ((4/3:ℝ)*M) := by
    convert! (hasSum_geometric_of_lt_one (by norm_num : (0:ℝ) ≤ 1/4)
      (by norm_num : (1/4:ℝ) < 1)).mul_right M using 1
    norm_num
  exact (reconstruction_summable hA x).hasSum.norm_le_of_bounded hg
    (fun n => term_bound hA n x)

theorem reconstruction_zero {A : ℝ → ℂ} {M : ℝ} (hA : ∀ x, ‖A x‖ ≤ M) :
    Reconstruction A 0 = (4/3:ℂ)*A 0 := by
  have hh := reconstruction_refinement hA 0
  simp only [mul_zero] at hh
  linear_combination (4/3:ℂ)*hh

theorem reconstruction_one {A : ℝ → ℂ} {M : ℝ}
    (hA : ∀ x, ‖A x‖ ≤ M) (ha : Function.Antiperiodic A 1) :
    Reconstruction A 1 = -(2/3:ℂ)*A 0 := by
  have hh := law_reconstruction hA ha 0
  simp only [zero_add, mul_zero, reconstruction_zero hA] at hh
  linear_combination hh

theorem reconstruction_injective {A B : ℝ → ℂ} {M N : ℝ}
    (hA : ∀ x, ‖A x‖ ≤ M) (ha : Function.Antiperiodic A 1)
    (hB : ∀ x, ‖B x‖ ≤ N) (hb : Function.Antiperiodic B 1)
    (heq : Reconstruction A = Reconstruction B) : A = B := by
  simpa only [primitive_reconstruction hA ha, primitive_reconstruction hB hb] using
    congrArg Primitive heq

def phaseSeed (x : ℝ) : ℂ := Complex.exp (-((Real.pi*x : ℝ) : ℂ)*Complex.I)

def freeSeed (c : ℂ) (x : ℝ) : ℂ := phaseSeed x + c*((phaseSeed x)^3 - phaseSeed x)

theorem phaseSeed_norm (x : ℝ) : ‖phaseSeed x‖ = 1 := by
  simp [phaseSeed, Complex.norm_exp, Complex.mul_re]

theorem phaseSeed_antiperiodic : Function.Antiperiodic phaseSeed 1 := by
  intro x
  unfold phaseSeed
  rw [show -((Real.pi*(x+1):ℝ):ℂ)*Complex.I =
      -((Real.pi*x:ℝ):ℂ)*Complex.I - (Real.pi:ℂ)*Complex.I by push_cast; ring,
    Complex.exp_sub_pi_mul_I]

theorem phaseSeed_half : phaseSeed (1/2) = -Complex.I := by
  unfold phaseSeed
  rw [show -((Real.pi*(1/2):ℝ):ℂ)*Complex.I =
      -(Real.pi:ℂ)/2*Complex.I by push_cast; ring]
  exact Complex.exp_neg_pi_div_two_mul_I

theorem freeSeed_bound (c : ℂ) (x : ℝ) : ‖freeSeed c x‖ ≤ 1 + 2*‖c‖ := by
  calc
    ‖freeSeed c x‖ ≤ ‖phaseSeed x‖ + ‖c‖ * ‖phaseSeed x ^ 3 - phaseSeed x‖ := by
      rw [freeSeed, ← norm_mul]
      exact norm_add_le _ _
    _ ≤ 1 + 2*‖c‖ := by
      have hh := norm_sub_le (phaseSeed x^3) (phaseSeed x)
      rw [norm_pow, phaseSeed_norm, one_pow] at hh
      rw [phaseSeed_norm]
      nlinarith [norm_nonneg c]

theorem freeSeed_antiperiodic (c : ℂ) : Function.Antiperiodic (freeSeed c) 1 := by
  intro x
  simp only [freeSeed, phaseSeed_antiperiodic x]
  ring

theorem continuous_freeSeed (c : ℂ) : Continuous (freeSeed c) := by
  unfold freeSeed phaseSeed
  fun_prop

theorem freeSeed_zero (c : ℂ) : freeSeed c 0 = 1 := by simp [freeSeed, phaseSeed]

theorem freeSeed_half (c : ℂ) : freeSeed c (1/2) = -Complex.I + 2*c*Complex.I := by
  rw [freeSeed, phaseSeed_half]
  have hh := Complex.I_sq
  linear_combination -c*Complex.I*hh

theorem reconstruction_freeSeed_injective :
    Function.Injective (fun c : ℂ => Reconstruction (freeSeed c)) := by
  intro c d h
  have hh := congrFun (reconstruction_injective (freeSeed_bound c) (freeSeed_antiperiodic c)
    (freeSeed_bound d) (freeSeed_antiperiodic d) h) (1/2)
  rw [freeSeed_half, freeSeed_half] at hh
  have hi := Complex.I_sq
  linear_combination (-Complex.I/2)*hh + (c-d)*hi

/-- A whole complex parameter survives continuity, period two, the dyadic law,
and both normalized theta endpoint values. No zero-location assertion is made. -/
theorem exists_injective_normalized_family :
    ∃ F : ℂ → ℝ → ℂ, Function.Injective F ∧ ∀ c,
      Continuous (F c) ∧ Function.Periodic (F c) 2 ∧ Law (F c) ∧
      F c 0 = 4/3 ∧ F c 1 = -2/3 := by
  refine ⟨fun c => Reconstruction (freeSeed c), reconstruction_freeSeed_injective, fun c => ?_⟩
  refine ⟨continuous_reconstruction (freeSeed_bound c) (continuous_freeSeed c),
    reconstruction_periodic (freeSeed_antiperiodic c),
    law_reconstruction (freeSeed_bound c) (freeSeed_antiperiodic c), ?_, ?_⟩
  · change Reconstruction (freeSeed c) 0 = 4/3
    rw [reconstruction_zero (freeSeed_bound c), freeSeed_zero, mul_one]
  · change Reconstruction (freeSeed c) 1 = -2/3
    rw [reconstruction_one (freeSeed_bound c) (freeSeed_antiperiodic c), freeSeed_zero, mul_one]
    ring

theorem integral_eq_zero {F : ℝ → ℂ} (hc : Continuous F)
    (hp : Function.Periodic F 2) (hF : Law F) : (∫ x in (0:ℝ)..2, F x) = 0 := by
  have hshift : (∫ x in (0:ℝ)..2, F (x+1)) = ∫ x in (0:ℝ)..2, F x := by
    rw [intervalIntegral.integral_comp_add_right]
    convert! hp.intervalIntegral_add_eq 1 0 using 1 <;> norm_num
  have hlong : (∫ x in (0:ℝ)..8, F x) = (4:ℝ) • ∫ x in (0:ℝ)..2, F x := by
    convert! hp.intervalIntegral_add_zsmul_eq 4 0
      (fun a b => hc.intervalIntegrable a b) using 1 <;> norm_num
  have hscale : (∫ x in (0:ℝ)..2, F (4*x)) = ∫ x in (0:ℝ)..2, F x := by
    rw [intervalIntegral.integral_comp_mul_left F (by norm_num : (4:ℝ) ≠ 0)]
    norm_num only [mul_zero, show (4:ℝ)*2=8 by norm_num]
    rw [hlong, smul_smul]
    norm_num
  have hh := congrArg (fun G : ℝ → ℂ => ∫ x in (0:ℝ)..2, G x) (funext hF)
  change (∫ x in (0:ℝ)..2, F (x+1)+F x) = (∫ x in (0:ℝ)..2, F (4*x)/2) at hh
  have hcshift : Continuous (fun x : ℝ => F (x+1)) := hc.comp (continuous_id.add continuous_const)
  rw [intervalIntegral.integral_add (hcshift.intervalIntegrable _ _)
    (hc.intervalIntegrable _ _), hshift, intervalIntegral.integral_div, hscale] at hh
  linear_combination (2/3:ℂ)*hh

/-- The retained primitive can carry any negative odd winding. -/
def oddPhase (k : ℕ) (x : ℝ) : ℂ := phaseSeed x ^ (2*k+1)

theorem oddPhase_antiperiodic (k : ℕ) : Function.Antiperiodic (oddPhase k) 1 := by
  intro x
  simp only [oddPhase, phaseSeed_antiperiodic x]
  simp [pow_add, pow_mul]

theorem oddPhase_norm (k : ℕ) (x : ℝ) : ‖oddPhase k x‖ = 1 := by
  simp [oddPhase, norm_pow, phaseSeed_norm]

theorem continuous_oddPhase (k : ℕ) : Continuous (oddPhase k) := by
  unfold oddPhase phaseSeed
  fun_prop

private theorem oddPhase_nonzero (k : ℕ) (x : ℝ) : oddPhase k x ≠ 0 := by
  intro hz
  have hh := oddPhase_norm k x
  rw [hz, norm_zero] at hh
  norm_num at hh

theorem reconstruction_oddPhase_tail (k : ℕ) (x : ℝ) :
    ‖Reconstruction (oddPhase k) x - oddPhase k x‖ ≤ (1/3:ℝ) := by
  have hb : ∀ x, ‖oddPhase k x‖ ≤ 1 := fun x => (oddPhase_norm k x).le
  rw [reconstruction_refinement hb, add_sub_cancel_left, norm_mul, norm_quarter]
  have hh := reconstruction_bound hb (4*x)
  nlinarith

theorem reconstruction_oddPhase_nonzero (k : ℕ) (x : ℝ) :
    Reconstruction (oddPhase k) x ≠ 0 := by
  intro hz
  have hh := reconstruction_oddPhase_tail k x
  rw [hz, zero_sub, norm_neg, oddPhase_norm] at hh
  norm_num at hh

private theorem phaseSeed_loop : IsLoop phaseSeed 0 2 := by
  refine ⟨by unfold phaseSeed; fun_prop, ?_, ?_⟩
  · intro x
    exact Complex.exp_ne_zero _
  · have hp : Function.Periodic phaseSeed 2 := by simpa using phaseSeed_antiperiodic.periodic
    simpa using (hp 0).symm

theorem windingNumber_phaseSeed : windingNumber phaseSeed 0 2 = -1 := by
  have hh := contLog_increment phaseSeed_loop
    (L := fun x => -((Real.pi*x:ℝ):ℂ)*Complex.I) (by fun_prop) (fun _ => rfl)
  have hc : (2*(Real.pi:ℂ)*Complex.I) ≠ 0 := by
    simp [Real.pi_ne_zero, Complex.I_ne_zero]
  have he : (windingNumber phaseSeed 0 2 : ℂ)*(2*(Real.pi:ℂ)*Complex.I) =
      (-1:ℂ)*(2*(Real.pi:ℂ)*Complex.I) := by
    rw [← hh]
    push_cast
    ring
  have hi := mul_right_cancel₀ hc he
  exact_mod_cast hi

theorem windingNumber_oddPhase (k : ℕ) :
    windingNumber (oddPhase k) 0 2 = -(2*k+1 : ℤ) := by
  unfold oddPhase
  rw [windingNumber_pow phaseSeed_loop, windingNumber_phaseSeed]
  push_cast
  ring

theorem windingNumber_reconstruction_oddPhase (k : ℕ) :
    windingNumber (Reconstruction (oddPhase k)) 0 2 = -(2*k+1 : ℤ) := by
  let F := Reconstruction (oddPhase k)
  let A := oddPhase k
  have hA : ∀ x, ‖A x‖ ≤ 1 := fun x => (oddPhase_norm k x).le
  have hFc : Continuous F := continuous_reconstruction hA (continuous_oddPhase k)
  have hAc : Continuous A := continuous_oddPhase k
  have hAn : ∀ x, A x ≠ 0 := oddPhase_nonzero k
  have hFn : ∀ x, F x ≠ 0 := reconstruction_oddPhase_nonzero k
  have hFp : Function.Periodic F 2 := reconstruction_periodic (oddPhase_antiperiodic k)
  have hAp : Function.Periodic A 2 := by simpa using (oddPhase_antiperiodic k).periodic
  have hAl : IsLoop A 0 2 := ⟨hAc, hAn, by simpa using (hAp 0).symm⟩
  let U : ℝ → ℂ := fun x => F x/A x
  have hUc : Continuous U := hFc.div hAc hAn
  have hUl : IsLoop U 0 2 := ⟨hUc, fun x => div_ne_zero (hFn x) (hAn x), by
    dsimp [U]
    rw [show F 0 = F 2 by simpa using (hFp 0).symm,
      show A 0 = A 2 by simpa using (hAp 0).symm]⟩
  have hball : ∀ x, ‖U x-1‖ < 1 := by
    intro x
    have he : U x-1 = (F x-A x)/A x := by dsimp [U]; field_simp [hAn x]
    rw [he, norm_div, oddPhase_norm, div_one]
    exact (reconstruction_oddPhase_tail k x).trans_lt (by norm_num)
  have hwU := windingNumber_eq_zero_of_ball1 hUc hUl.closed hball
  have hprod : (fun x => A x*U x) = F := by
    funext x
    dsimp [U]
    field_simp [hAn x]
  have hh := windingNumber_mul hAl hUl
  rw [hprod, hwU, add_zero, windingNumber_oddPhase] at hh
  exact hh

/-- Explicit continuous, nonvanishing, mean-zero boundary loops satisfy the
same dyadic identity and endpoint anchors while their winding is unbounded. -/
theorem exists_arbitrary_odd_winding (k : ℕ) :
    ∃ F : ℝ → ℂ, Continuous F ∧ Function.Periodic F 2 ∧ Law F ∧
      F 0 = 4/3 ∧ F 1 = -2/3 ∧ (∫ x in (0:ℝ)..2, F x) = 0 ∧
      (∀ x, F x ≠ 0) ∧ windingNumber F 0 2 = -(2*k+1 : ℤ) := by
  let F := Reconstruction (oddPhase k)
  have hA : ∀ x, ‖oddPhase k x‖ ≤ 1 := fun x => (oddPhase_norm k x).le
  have hAc := continuous_oddPhase k
  have hAp := oddPhase_antiperiodic k
  have hFc := continuous_reconstruction hA hAc
  have hFp := reconstruction_periodic hAp
  have hFl := law_reconstruction hA hAp
  refine ⟨F, hFc, hFp, hFl, ?_, ?_, integral_eq_zero hFc hFp hFl,
    reconstruction_oddPhase_nonzero k, windingNumber_reconstruction_oddPhase k⟩
  · change Reconstruction (oddPhase k) 0 = 4/3
    rw [reconstruction_zero hA]
    simp [oddPhase, phaseSeed]
  · change Reconstruction (oddPhase k) 1 = -2/3
    rw [reconstruction_one hA hAp]
    simp [oddPhase, phaseSeed]
    ring

end RHTower.DyadicBoundary
