import GaloisForLFunctions.HTGeometry.CenteredModularAbel
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Normed.Group.InfiniteSum

/-!
# Logarithmic cost of replacing the complete divisor-flux weights

The first primitive of the centered Möbius residue source is bounded by
`N * (N + 1) / 16`. Each modulus `d ≤ N` samples every multiple beyond `N`
through `d * (N / d + j + 1)`. A telescoping reciprocal majorant proves
absolute convergence of both complete channel series. The difference between
`1 / k²` and `1 / (k * (k + 1))` gains a further factor `1 / N`, so the
aggregate signed flux changes by at most `harmonic N / 4`.

This bounds the weight-replacement error, not the remaining signed flux.
-/

noncomputable section
set_option autoImplicit false
open Finset Filter Topology
namespace RHTower.DeletionFlux

/-- The literal signed first primitive of the centered Möbius residue source. -/
def primitive (N k : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 N, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    HTGeometry.centeredModularPrimitive d k

private theorem abs_mu_le (n : ℕ) :
    |((ArithmeticFunction.moebius n : ℤ) : ℝ)| ≤ 1 := by
  exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))

private theorem sum_nat (N : ℕ) :
    (∑ d ∈ Icc 1 N, (d : ℝ)) = (N : ℝ)*(N+1)/2 := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_Icc_succ_top (by omega), ih]
    push_cast
    ring

private theorem primitive_bound (N k : ℕ) :
    |primitive N k| ≤ (N : ℝ)*(N+1)/16 := by
  calc
    _ ≤ ∑ d ∈ Icc 1 N,
        |((ArithmeticFunction.moebius d : ℤ) : ℝ) *
          HTGeometry.centeredModularPrimitive d k| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 N, (d : ℝ)/8 := by
      apply sum_le_sum
      intro d hd
      rw [abs_mul]
      have hp := HTGeometry.centeredModularPrimitive_bounds d k
      have hb : |HTGeometry.centeredModularPrimitive d k| ≤ (d : ℝ)/8 :=
        abs_le.mpr ⟨by linarith [hp.1], by linarith [hp.2]⟩
      calc _ ≤ 1 * ((d : ℝ)/8) :=
             mul_le_mul (abs_mu_le d) hb (abs_nonneg _) (by norm_num)
           _ = _ := one_mul _
    _ = _ := by rw [← sum_div, sum_nat]; ring

private theorem reciprocal_series_bound {q : ℕ} (hq : 0 < q) {C : ℝ}
    (hC : 0 ≤ C) (f : ℕ → ℝ)
    (h : ∀ j, |f j| ≤ C / (((q : ℝ)+j)*((q : ℝ)+j+1))) :
    Summable f ∧ |∑' j, f j| ≤ C/q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hb (T : ℕ) : ∑ j ∈ range T, |f j| ≤ C/q := by
    calc _ ≤ ∑ j ∈ range T, C / (((q : ℝ)+j)*((q : ℝ)+j+1)) :=
           sum_le_sum (fun j _ => h j)
         _ = C/q - C/((q : ℝ)+T) := by
           calc _ = ∑ j ∈ range T, (C/((q : ℝ)+j)-C/((q : ℝ)+(j+1 : ℕ))) := by
                  apply sum_congr rfl
                  intro j hj
                  push_cast
                  field_simp
                  ring
                _ = _ := by
                  simpa using sum_range_sub' (fun j : ℕ => C/((q : ℝ)+j)) T
         _ ≤ _ := sub_le_self _ (by positivity)
  have ha : Summable (fun j => |f j|) := summable_of_sum_range_le (fun _ => abs_nonneg _) hb
  refine ⟨summable_abs_iff.mp ha, ?_⟩
  have hlim : (∑' j, |f j|) ≤ C/q :=
    le_of_tendsto ha.hasSum.tendsto_sum_nat (Eventually.of_forall hb)
  have hnorm : Summable (fun j => ‖f j‖) := by simpa only [Real.norm_eq_abs] using ha
  have hn := norm_tsum_le_tsum_norm hnorm
  simpa only [Real.norm_eq_abs] using hn.trans hlim

private theorem quotient_bounds {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) (j : ℕ) :
    0 < N/d ∧ N < d*(N/d+j+1) ∧ N ≤ 2*d*(N/d) := by
  have hm := Nat.mod_lt N hd
  have he := Nat.mod_add_div N d
  have hq : 0 < N/d := Nat.div_pos hdN hd
  refine ⟨hq, ?_, ?_⟩ <;> nlinarith

private theorem inverse_square_bound {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) (j : ℕ) :
    1 / ((d*(N/d+j+1) : ℕ) : ℝ)^2 ≤
      (1/(d : ℝ)^2) / (((N/d : ℕ) : ℝ)+j) / (((N/d : ℕ) : ℝ)+j+1) := by
  have hq := (quotient_bounds hd hdN j).1
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hqR : (0 : ℝ) < (N/d : ℕ) := by exact_mod_cast hq
  push_cast
  rw [div_div, div_div]
  apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
  have ht : (0 : ℝ) ≤ ((N/d : ℕ) : ℝ)+j := by positivity
  nlinarith [sq_nonneg (d : ℝ)]

private theorem weight_gap {k : ℕ} (hk : 0 < k) :
    1/(k : ℝ)^2 - 1/((k : ℝ)*(k+1)) = (1/(k : ℝ)^2)*(1/(k+1)) := by
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  field_simp
  ring



private theorem channel_summable {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N)
    (w : ℕ → ℝ) (hw : ∀ k, 0 < k → |w k| ≤ 1/(k : ℝ)^2) :
    Summable (fun j : ℕ => primitive N (d*(N/d+j+1))*w (d*(N/d+j+1))) := by
  let B : ℝ := (N : ℝ)*(N+1)/16
  have hq := (quotient_bounds hd hdN 0).1
  apply (reciprocal_series_bound hq (C := B/(d : ℝ)^2) (by dsimp [B]; positivity) _ ?_).1
  intro j
  have hk : 0 < d*(N/d+j+1) := by positivity
  calc
    _ = |primitive N (d*(N/d+j+1))| * |w (d*(N/d+j+1))| := abs_mul _ _
    _ ≤ B*(1/((d*(N/d+j+1) : ℕ) : ℝ)^2) :=
      mul_le_mul (primitive_bound N _) (hw _ hk) (abs_nonneg _) (by dsimp [B]; positivity)
    _ ≤ B*((1/(d : ℝ)^2) / (((N/d : ℕ) : ℝ)+j) / (((N/d : ℕ) : ℝ)+j+1)) :=
      mul_le_mul_of_nonneg_left (inverse_square_bound hd hdN j) (by dsimp [B]; positivity)
    _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev, one_mul]; ring

/-- Every literal divisor channel converges for both the physical and inverse-square weights. -/
theorem channels_summable {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
    Summable (fun j : ℕ => primitive N (d*(N/d+j+1)) /
      ((d*(N/d+j+1) : ℕ) : ℝ)^2) ∧
    Summable (fun j : ℕ => primitive N (d*(N/d+j+1)) /
      (((d*(N/d+j+1) : ℕ) : ℝ)*(((d*(N/d+j+1) : ℕ) : ℝ)+1))) := by
  constructor
  · have h := channel_summable hd hdN
      (fun k => 1/(k : ℝ)^2) (fun k hk => by rw [abs_of_nonneg (by positivity)])
    exact h.congr (fun j => by ring)
  · have h := channel_summable hd hdN (fun k => 1/((k : ℝ)*(k+1))) (by
      intro k hk
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      rw [abs_of_nonneg (by positivity)]
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      nlinarith)
    exact h.congr (fun j => by ring)

/-- Complete divisor-sampled primitive flux in the physical step weights. -/
def stepFlux (N : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 N, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    ∑' j : ℕ, primitive N (d*(N/d+j+1)) /
      (((d*(N/d+j+1) : ℕ) : ℝ)*(((d*(N/d+j+1) : ℕ) : ℝ)+1))

/-- The same complete signed flux in homogeneous inverse-square weights. -/
def reciprocalFlux (N : ℕ) : ℝ :=
  ∑ d ∈ Icc 1 N, ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    ∑' j : ℕ, primitive N (d*(N/d+j+1)) / ((d*(N/d+j+1) : ℕ) : ℝ)^2

private theorem channel_difference {N d : ℕ} (hd : 0 < d) (hdN : d ≤ N) :
    |(∑' j : ℕ, primitive N (d*(N/d+j+1)) / ((d*(N/d+j+1) : ℕ) : ℝ)^2) -
      ∑' j : ℕ, primitive N (d*(N/d+j+1)) /
        (((d*(N/d+j+1) : ℕ) : ℝ)*(((d*(N/d+j+1) : ℕ) : ℝ)+1))| ≤ 1/(4*(d : ℝ)) := by
  let B : ℝ := (N : ℝ)*(N+1)/16
  have hN : 0 < N := hd.trans_le hdN
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hq := (quotient_bounds hd hdN 0).1
  have hqR : (0 : ℝ) < (N/d : ℕ) := by exact_mod_cast hq
  let f (j : ℕ) : ℝ := primitive N (d*(N/d+j+1)) *
    (1/((d*(N/d+j+1) : ℕ) : ℝ)^2 -
      1/(((d*(N/d+j+1) : ℕ) : ℝ)*(((d*(N/d+j+1) : ℕ) : ℝ)+1)))
  have hb := reciprocal_series_bound hq (C := B/((N : ℝ)*(d : ℝ)^2))
    (by dsimp [B]; positivity) f (by
      intro j
      let k := d*(N/d+j+1)
      have hNk : N < k := (quotient_bounds hd hdN j).2.1
      have hk : 0 < k := hN.trans hNk
      have hkR : (0 : ℝ) < k := by exact_mod_cast hk
      have hNkR : (N : ℝ) ≤ (k : ℝ)+1 := by exact_mod_cast (show N ≤ k+1 by omega)
      have hrec : 1/((k : ℝ)+1) ≤ 1/(N : ℝ) :=
        div_le_div_of_nonneg_left (by norm_num) hNR hNkR
      change |primitive N k * (1/(k : ℝ)^2-1/((k : ℝ)*(k+1)))| ≤ _
      rw [weight_gap hk, abs_mul,
        abs_of_nonneg (show 0 ≤ (1/(k : ℝ)^2)*(1/(k+1)) by positivity)]
      calc
        _ ≤ B*((1/(k : ℝ)^2)*(1/(k+1))) :=
          mul_le_mul_of_nonneg_right (primitive_bound N k) (by positivity)
        _ ≤ B*((1/(k : ℝ)^2)*(1/N)) := by
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hrec (by positivity))
            (by dsimp [B]; positivity)
        _ ≤ B*(((1/(d : ℝ)^2) / (((N/d : ℕ) : ℝ)+j) /
            (((N/d : ℕ) : ℝ)+j+1))*(1/N)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (inverse_square_bound hd hdN j)
            (by positivity)) (by dsimp [B]; positivity)
        _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev, one_mul]; ring)
  have hscale : B/((N : ℝ)*(d : ℝ)^2)/((N/d : ℕ) : ℝ) ≤ 1/(4*(d : ℝ)) := by
    have hqn : (N : ℝ) ≤ 2*(d : ℝ)*((N/d : ℕ) : ℝ) := by
      exact_mod_cast (quotient_bounds hd hdN 0).2.2
    have hN1 : (N : ℝ)+1 ≤ 4*(d : ℝ)*((N/d : ℕ) : ℝ) := by
      have hNge : (1 : ℝ) ≤ N := by exact_mod_cast hN
      linarith
    calc _ = ((N : ℝ)+1)/(16*(d : ℝ)^2*((N/d : ℕ) : ℝ)) := by dsimp [B]; field_simp
         _ ≤ (4*(d : ℝ)*((N/d : ℕ) : ℝ))/(16*(d : ℝ)^2*((N/d : ℕ) : ℝ)) :=
           div_le_div_of_nonneg_right hN1 (by positivity)
         _ = _ := by field_simp; ring
  have hc := channels_summable hd hdN
  have hc2 : Summable (fun j : ℕ => primitive N (d*(N/d+j+1)) /
      (((d*(N/d+j+1) : ℕ) : ℝ)*(((d*(N/d+j+1) : ℕ) : ℝ)+1))) := by
    exact hc.2
  have he : (∑' j, f j) =
      (∑' j : ℕ, primitive N (d*(N/d+j+1)) / ((d*(N/d+j+1) : ℕ) : ℝ)^2) -
      ∑' j : ℕ, primitive N (d*(N/d+j+1)) /
        (((d*(N/d+j+1) : ℕ) : ℝ)*(((d*(N/d+j+1) : ℕ) : ℝ)+1)) := by
    rw [← hc.1.tsum_sub hc2]
    apply tsum_congr
    intro j
    dsimp [f]
    ring
  rw [← he]
  exact hb.2.trans hscale

/-- Replacing the complete physical flux weights costs at most one quarter of the
harmonic mass, after summing all actual Möbius divisor channels. -/
theorem flux_weight_replacement (N : ℕ) :
    |reciprocalFlux N-stepFlux N| ≤ (harmonic N : ℝ)/4 := by
  unfold reciprocalFlux stepFlux
  rw [← sum_sub_distrib]
  calc
    _ ≤ ∑ d ∈ Icc 1 N, |((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        (∑' j : ℕ, primitive N (d*(N/d+j+1)) / ((d*(N/d+j+1) : ℕ) : ℝ)^2) -
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
        ∑' j : ℕ, primitive N (d*(N/d+j+1)) /
          (((d*(N/d+j+1) : ℕ) : ℝ)*(((d*(N/d+j+1) : ℕ) : ℝ)+1))| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 N, 1/(4*(d : ℝ)) := by
      apply sum_le_sum
      intro d hd
      obtain ⟨hd1, hdN⟩ := mem_Icc.mp hd
      rw [← mul_sub, abs_mul]
      calc _ ≤ 1*(1/(4*(d : ℝ))) :=
             mul_le_mul (abs_mu_le d) (channel_difference hd1 hdN) (abs_nonneg _) (by norm_num)
           _ = _ := one_mul _
    _ = _ := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      rw [sum_div]
      apply sum_congr rfl
      intro d hd
      simp only [one_div]
      ring

end RHTower.DeletionFlux
