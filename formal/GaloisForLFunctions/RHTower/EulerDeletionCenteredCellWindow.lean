import GaloisForLFunctions.RHTower.EulerDeletionCoefficientPrefixEnergy
import Mathlib.Algebra.Order.Chebyshev

/-!
# Finite-window coercivity for the complete Euler-deletion source

A bounded centered residue primitive controls every finite spatial window
of the literal cell numerator. Cauchy--Schwarz against the complete energy
series then gives a lower certificate without changing its physical weights.
Choosing the window from the actual coefficient moment gives the closed bound
`|mean a N|^(3 : ℕ) ≤ 8 * moment a N * ‖source a N‖^(2 : ℕ)`.

For the prime-power boundary forcing this is the analytic step in its
`N / log(N)^(2 : ℕ)` lower bound. The required arithmetic moment estimates and the
complete signed source ceiling are separate obligations.
-/

noncomputable section
set_option autoImplicit false
open Finset
open scoped BigOperators
namespace RHTower.DeletionCellWindow
open DeletionCoefficientTransfer

/-- Exact centered primitive of one residue channel. -/
def centeredPrimitive (m k : ℕ) : ℝ :=
  ((k % m : ℕ) : ℝ)*(((k % m : ℕ) : ℝ)-(m : ℝ))/(2*(m : ℝ))

/-- The centered residue is the exact discrete derivative of the primitive. -/
theorem centeredPrimitive_succ {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    centeredPrimitive m (k+1)-centeredPrimitive m k =
      ((k%m : ℕ) : ℝ)/(m : ℝ)-((m : ℝ)-1)/(2*(m : ℝ)) := by
  by_cases hm1 : m=1
  · subst m; norm_num [centeredPrimitive, Nat.mod_one]
  have hm2 : 1 < m := by omega
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (by omega : m ≠ 0)
  have hr := Nat.mod_lt k (by omega : 0 < m)
  have hstep : (k+1)%m=(k%m+1)%m := by
    rw [Nat.add_mod, Nat.mod_eq_of_lt hm2]
  unfold centeredPrimitive
  by_cases hw : k%m+1=m
  · rw [hstep,hw,Nat.mod_self]
    have hwr : ((k%m : ℕ) : ℝ)+1=(m : ℝ) := by exact_mod_cast hw
    simp only [Nat.cast_zero]
    field_simp
    nlinarith
  · rw [hstep,Nat.mod_eq_of_lt (by omega : k%m+1 < m)]
    push_cast
    field_simp
    ring

/-- The primitive lies in an interval of length one eighth of the modulus. -/
theorem centeredPrimitive_bounds {m : ℕ} (hm : 1 ≤ m) (k : ℕ) :
    -(m : ℝ)/8 ≤ centeredPrimitive m k ∧ centeredPrimitive m k ≤ 0 := by
  have hm0 : 0 < (m : ℝ) := by exact_mod_cast (by omega : 0 < m)
  have hr0 : 0 ≤ ((k%m : ℕ) : ℝ) := Nat.cast_nonneg _
  have hr1 : ((k%m : ℕ) : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast (Nat.mod_lt k (by omega : 0 < m)).le
  unfold centeredPrimitive
  constructor
  · rw [le_div_iff₀ (by positivity)]
    nlinarith [sq_nonneg (2*((k%m : ℕ) : ℝ)-(m : ℝ))]
  · exact div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos hr0 (by linarith)) (by positivity)

/-- Two endpoints cost one primitive range, with no extra factor of two. -/
theorem centeredPrimitive_sub_bound {m : ℕ} (hm : 1 ≤ m) (k l : ℕ) :
    |centeredPrimitive m k-centeredPrimitive m l| ≤ (m : ℝ)/8 := by
  obtain ⟨hk0,hk1⟩ := centeredPrimitive_bounds hm k
  obtain ⟨hl0,hl1⟩ := centeredPrimitive_bounds hm l
  exact abs_le.mpr ⟨by linarith,by linarith⟩

/-- The residue sum is its mean plus the exact two-endpoint correction. -/
theorem sum_residue_window {m : ℕ} (hm : 1 ≤ m) (T L : ℕ) :
    (∑ i ∈ range L, (((T+i)%m : ℕ) : ℝ)/(m : ℝ)) =
      (L : ℝ)*((m : ℝ)-1)/(2*(m : ℝ))+
        centeredPrimitive m (T+L)-centeredPrimitive m T := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [Finset.sum_range_succ, ih]
    have h := centeredPrimitive_succ hm (T+L)
    rw [Nat.add_assoc] at h
    push_cast
    linear_combination -h



/-- The mean of the exact periodic cell numerator. -/
def mean (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ range N, a (i+1)*(i : ℝ)/(2*((i : ℝ)+1))

/-- Coefficient moment controlling the centered cell primitive. -/
def moment (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ i ∈ range N, |a (i+1)| * ((i : ℝ)+1)

/-- Sum of actual cell numerators on a finite spatial window. -/
def window (a : ℕ → ℝ) (N T L : ℕ) : ℝ :=
  ∑ i ∈ range L, cell a N (T+i)

/-- Summing the primitive identity retains every signed coefficient. -/
theorem window_eq_mean_add_boundary (a : ℕ → ℝ) (N T L : ℕ) :
    window a N T L = (L : ℝ)*mean a N +
      ∑ i ∈ range N, a (i+1)*
        (centeredPrimitive (i+1) (T+L)-centeredPrimitive (i+1) T) := by
  unfold window cell mean
  rw [Finset.sum_comm]
  simp_rw [mul_div_assoc, ← Finset.mul_sum]
  have he (i : ℕ) :
      (∑ j ∈ range L, (((T+j)%(i+1) : ℕ) : ℝ)/((i : ℝ)+1)) =
        (L : ℝ)*(i : ℝ)/(2*((i : ℝ)+1))+
          centeredPrimitive (i+1) (T+L)-centeredPrimitive (i+1) T := by
    simpa only [Nat.cast_add, Nat.cast_one, add_sub_cancel_right] using
      sum_residue_window (m := i+1) (by omega) T L
  simp_rw [he]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- The coefficient moment bounds the finite-window error. -/
theorem abs_window_sub_mean_le (a : ℕ → ℝ) (N T L : ℕ) :
    |window a N T L-(L : ℝ)*mean a N| ≤ moment a N/8 := by
  rw [window_eq_mean_add_boundary, add_sub_cancel_left]
  calc
    _ ≤ ∑ i ∈ range N, |a (i+1)*
        (centeredPrimitive (i+1) (T+L)-centeredPrimitive (i+1) T)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range N, |a (i+1)| * (((i : ℝ)+1)/8) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      simpa only [Nat.cast_add, Nat.cast_one] using
        centeredPrimitive_sub_bound (m := i+1) (by omega) (T+L) T
    _ = moment a N/8 := by
      simp only [moment, Finset.sum_div, mul_div_assoc]


/-- A finite window tests the complete physical energy, with its original weights. -/
theorem window_sq_le_source_energy (a : ℕ → ℝ) (N T L : ℕ) :
    window a N (T+1) L ^ (2 : ℕ) ≤
      (L : ℝ)*((T : ℝ)+(L : ℝ)+1)^(2 : ℕ)*‖source a N‖^(2 : ℕ) := by
  let f : ℕ → ℝ := fun j => cell a N (j+1)^(2 : ℕ)/(((j : ℝ)+1)*((j : ℝ)+2))
  have hf : HasSum f (‖source a N‖^(2 : ℕ)) := hasSum_source_energy a N
  have hs : (∑ i ∈ range L, f (T+i)) ≤ ‖source a N‖^(2 : ℕ) := by
    have h := sum_le_hasSum ((range L).image (fun i => T+i))
      (fun j _ => by dsimp [f]; positivity) hf
    rw [Finset.sum_image (by intro i hi j hj hij; dsimp only at hij; omega)] at h
    exact h
  have hterm (i : ℕ) (hi : i ∈ range L) :
      cell a N (T+1+i)^(2 : ℕ) ≤ ((T : ℝ)+(L : ℝ)+1)^(2 : ℕ)*f (T+i) := by
    have hiL : (i : ℝ)+1 ≤ (L : ℝ) := by
      exact_mod_cast (Nat.succ_le_of_lt (mem_range.mp hi))
    have hT : 0 ≤ (T : ℝ) := Nat.cast_nonneg _
    have hi0 : 0 ≤ (i : ℝ) := Nat.cast_nonneg _
    dsimp [f]
    rw [show T+1+i = T+i+1 by omega, ← mul_div_assoc,
      le_div_iff₀ (by positivity)]
    conv_rhs => rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
    push_cast
    nlinarith
  calc
    window a N (T+1) L ^ (2 : ℕ) ≤
        (L : ℝ)*(∑ i ∈ range L, cell a N (T+1+i)^(2 : ℕ)) := by
      simpa only [window, card_range] using
        (sq_sum_le_card_mul_sum_sq (s := range L) (f := fun i => cell a N (T+1+i)))
    _ ≤ (L : ℝ)*(((T : ℝ)+(L : ℝ)+1)^(2 : ℕ)*(∑ i ∈ range L, f (T+i))) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum hterm
    _ ≤ (L : ℝ)*((T : ℝ)+(L : ℝ)+1)^(2 : ℕ)*‖source a N‖^(2 : ℕ) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_left hs (by positivity)

/-- A nonzero mean survives every window up to the sharp coefficient moment error. -/
theorem mean_le_abs_window_add_moment (a : ℕ → ℝ) (N T L : ℕ) :
    (L : ℝ)*|mean a N| ≤ |window a N T L|+moment a N/8 := by
  have h := abs_window_sub_mean_le a N T L
  have hr := abs_sub_le ((L : ℝ)*mean a N) (window a N T L) 0
  simp only [sub_zero, abs_sub_comm ((L : ℝ)*mean a N) (window a N T L),
    abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (L : ℝ) from Nat.cast_nonneg L)] at hr
  linarith

/-- Closed finite-window lower certificate for the complete physical source energy. -/
theorem mean_window_source_certificate (a : ℕ → ℝ) (N T L : ℕ) :
    (max 0 ((L : ℝ)*|mean a N| - moment a N/8))^(2 : ℕ) ≤
      (L : ℝ)*((T : ℝ)+(L : ℝ)+1)^(2 : ℕ)*‖source a N‖^(2 : ℕ) := by
  have hw := window_sq_le_source_energy a N T L
  have hm := mean_le_abs_window_add_moment a N (T+1) L
  have hb : max 0 ((L : ℝ)*|mean a N| - moment a N/8) ≤
      |window a N (T+1) L| := max_le (abs_nonneg _) (by linarith)
  have hn : 0 ≤ max 0 ((L : ℝ)*|mean a N| - moment a N/8) := le_max_left _ _
  nlinarith [sq_abs (window a N (T+1) L)]

/-- The coefficient moment dominates eight times the absolute cell mean. -/
theorem abs_mean_le_moment (a : ℕ → ℝ) (N : ℕ) :
    |mean a N| ≤ moment a N / 8 := by
  unfold mean
  calc
    _ ≤ ∑ i ∈ range N, |a (i+1)*(i : ℝ)/(2*((i : ℝ)+1))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range N, |a (i+1)| * ((i : ℝ)+1)/8 := by
      apply Finset.sum_le_sum
      intro i hi
      rw [abs_div, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (i : ℝ) from Nat.cast_nonneg i),
        abs_of_pos (by positivity : (0 : ℝ) < 2*((i : ℝ)+1)), mul_div_assoc,
        mul_div_assoc]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg ((i : ℝ)-1)]
    _ = moment a N/8 := by rw [← Finset.sum_div]; rfl

/-- A nonzero cell mean forces energy at a scale determined by the actual coefficient moment. -/
theorem abs_mean_cube_le_moment_energy (a : ℕ → ℝ) (N : ℕ) :
    |mean a N| ^ (3 : ℕ) ≤ 8*moment a N*‖source a N‖^(2 : ℕ) := by
  have hsmall := abs_mean_le_moment a N
  have hR0 : 0 ≤ moment a N := by linarith [abs_nonneg (mean a N)]
  by_cases hm : mean a N = 0
  · rw [hm, abs_zero, zero_pow (by omega)]
    positivity
  have hm0 : 0 < |mean a N| := abs_pos.mpr hm
  let L : ℕ := ⌈moment a N/(4*|mean a N|)⌉₊
  have hR : moment a N ≤ (L : ℝ)*(4*|mean a N|) := by
    exact (div_le_iff₀ (by positivity)).mp (Nat.le_ceil _)
  have hL2 : 2 ≤ (L : ℝ) := by nlinarith
  have hL0 : 0 < (L : ℝ) := by linarith
  have hround : (L : ℝ) < moment a N/(4*|mean a N|)+1 :=
    Nat.ceil_lt_add_one (by positivity)
  have hLM : (L : ℝ)*|mean a N| ≤ moment a N/2 := by
    have hlt := mul_lt_mul_of_pos_right hround hm0
    have he : (moment a N/(4*|mean a N|)+1)*|mean a N| =
        moment a N/4+|mean a N| := by field_simp
    rw [he] at hlt
    linarith
  have hmean := mean_le_abs_window_add_moment a N 1 L
  have hlow : ((L : ℝ)*|mean a N|/2)^(2 : ℕ) ≤ window a N 1 L^(2 : ℕ) := by
    have hb : (L : ℝ)*|mean a N|/2 ≤ |window a N 1 L| := by nlinarith
    have hn : 0 ≤ (L : ℝ)*|mean a N|/2 := by positivity
    nlinarith [sq_abs (window a N 1 L)]
  have henergy : window a N 1 L^(2 : ℕ) ≤ (L : ℝ)*((L : ℝ)+1)^(2 : ℕ)*‖source a N‖^(2 : ℕ) := by
    simpa only [Nat.zero_add, Nat.cast_zero, zero_add] using
      window_sq_le_source_energy a N 0 L
  have hweight : ((L : ℝ)+1)^(2 : ℕ) ≤ 4*(L : ℝ)^(2 : ℕ) := by nlinarith
  have hupper : (L : ℝ)*((L : ℝ)+1)^(2 : ℕ)*‖source a N‖^(2 : ℕ) ≤
      4*(L : ℝ)^(3 : ℕ)*‖source a N‖^(2 : ℕ) := by
    have h := mul_le_mul_of_nonneg_right hweight
      (mul_nonneg hL0.le (sq_nonneg ‖source a N‖))
    nlinarith
  have hc : (L : ℝ)^(2 : ℕ)*|mean a N| ^ (2 : ℕ) ≤
      (L : ℝ)^(2 : ℕ)*(16*(L : ℝ)*‖source a N‖^(2 : ℕ)) := by
    nlinarith [hlow.trans (henergy.trans hupper)]
  have hm2 := le_of_mul_le_mul_left hc (sq_pos_of_pos hL0)
  calc
    |mean a N| ^ (3 : ℕ) = |mean a N| * |mean a N| ^ (2 : ℕ) := by ring
    _ ≤ |mean a N| * (16*(L : ℝ)*‖source a N‖^(2 : ℕ)) :=
      mul_le_mul_of_nonneg_left hm2 hm0.le
    _ = (16*‖source a N‖^(2 : ℕ))*((L : ℝ)*|mean a N|) := by ring
    _ ≤ (16*‖source a N‖^(2 : ℕ))*(moment a N/2) :=
      mul_le_mul_of_nonneg_left hLM (by positivity)
    _ = 8*moment a N*‖source a N‖^(2 : ℕ) := by ring

end RHTower.DeletionCellWindow
