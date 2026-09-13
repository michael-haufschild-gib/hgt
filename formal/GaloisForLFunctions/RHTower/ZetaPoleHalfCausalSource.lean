import GaloisForLFunctions.HTGeometry.PoleClearedHalfKernel
import GaloisForLFunctions.RHTower.SquarefreeConvolutionHalfSelbergDelangeFactorization

/-!
# Absolute mass of the actual pole-half causal source

The literal positive zeta-half coefficients weight delayed copies of the pole-cleared
half-order kernel. On each logarithmic integer cell, every older contribution decreases.
The newest atom therefore forces a quantitative absolute-mass lower bound, without any
sign assumption on the sum. The kernel is unnormalized: division by `sqrt(pi)` gives
the usual Gamma-half normalization. No global Laplace-convergence estimate is assumed.
-/

open MeasureTheory Set

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

def zetaPoleHalfCausalPrefix (N : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 N, (zetaBinomialHalf n).re *
    poleClearedHalfKernel (x + (Real.log N - Real.log n))

def zetaPoleHalfCausalSource (u : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊Real.exp u⌋₊, (zetaBinomialHalf n).re *
    poleClearedHalfKernel (u - Real.log n)

theorem zetaPoleHalfCausalPrefix_absolute_mass_lower {N : ℕ} (hN : 1 ≤ N)
    {d : ℝ} (hd : 0 < d) :
    (zetaBinomialHalf N).re *
      (4 * (d / 2) ^ ((1 : ℝ) / 2) - 2 * d ^ ((1 : ℝ) / 2)) ≤
        ∫ x in (0 : ℝ)..d, |zetaPoleHalfCausalPrefix N x| := by
  apply poleClearedHalfPacket_absolute_mass_lower
    (Finset.Icc 1 N) (fun n : ℕ => Real.log N - Real.log n)
    (fun n : ℕ => (zetaBinomialHalf n).re) (j := N)
  · exact Finset.mem_Icc.mpr ⟨hN, le_rfl⟩
  · intro n hn
    have hn' := Finset.mem_Icc.mp hn
    apply sub_nonneg.mpr
    exact Real.log_le_log (by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn'.1))
      (by exact_mod_cast hn'.2)
  · intro n _
    exact zetaBinomialHalf_apply_nonneg n
  · exact sub_self _
  · exact hd

theorem zetaPoleHalfCausalSource_eq_prefix {N : ℕ} (hN : 1 ≤ N) {x : ℝ}
    (hx : x ∈ Ioo 0 (Real.log (N + 1 : ℕ) - Real.log N)) :
    zetaPoleHalfCausalSource (Real.log N + x) = zetaPoleHalfCausalPrefix N x := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hNp1 : (0 : ℝ) < (N + 1 : ℕ) := by positivity
  have hfloor : ⌊Real.exp (Real.log N + x)⌋₊ = N := by
    apply (Nat.floor_eq_iff (Real.exp_pos _).le).mpr
    constructor
    · calc
        (N : ℝ) = Real.exp (Real.log N) := (Real.exp_log hNp).symm
        _ ≤ Real.exp (Real.log N + x) := Real.exp_le_exp.mpr (by linarith [hx.1])
    · have h := Real.exp_lt_exp.mpr (show Real.log N + x < Real.log (N + 1 : ℕ) by
        linarith [hx.2])
      rw [Real.exp_log hNp1] at h
      simpa only [Nat.cast_add, Nat.cast_one] using h
  unfold zetaPoleHalfCausalSource zetaPoleHalfCausalPrefix
  rw [hfloor]
  apply Finset.sum_congr rfl
  intro n _
  congr 2
  ring

theorem zetaPoleHalfCausalSource_cell_absolute_mass_lower {N : ℕ} (hN : 1 ≤ N) :
    (zetaBinomialHalf N).re *
      (4 * ((Real.log (N + 1 : ℕ) - Real.log N) / 2) ^ ((1 : ℝ) / 2) -
        2 * (Real.log (N + 1 : ℕ) - Real.log N) ^ ((1 : ℝ) / 2)) ≤
      ∫ x in (0 : ℝ)..(Real.log (N + 1 : ℕ) - Real.log N),
        |zetaPoleHalfCausalSource (Real.log N + x)| := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hN)
  have hd : 0 < Real.log (N + 1 : ℕ) - Real.log N := by
    apply sub_pos.mpr
    exact Real.log_lt_log hNp (by exact_mod_cast Nat.lt_succ_self N)
  have h := zetaPoleHalfCausalPrefix_absolute_mass_lower hN hd
  apply h.trans_eq
  rw [intervalIntegral.integral_of_le hd.le, intervalIntegral.integral_of_le hd.le,
    integral_Ioc_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro x hx
  dsimp only
  rw [zetaPoleHalfCausalSource_eq_prefix hN hx]

theorem zetaPoleHalfCausalSource_prime_cell_mass_lower {p : ℕ} (hp : p.Prime) :
    (Real.log (p + 1 : ℕ) - Real.log p) ^ ((1 : ℝ) / 2) / 4 ≤
      ∫ x in (0 : ℝ)..(Real.log (p + 1 : ℕ) - Real.log p),
        |zetaPoleHalfCausalSource (Real.log p + x)| := by
  have hcoeff : (zetaBinomialHalf p).re = (1 / 2 : ℝ) := by
    have h := zetaBinomialHalf_apply_prime_pow_eq_centralBinom (p := p) (k := 1) hp
    norm_num at h
    rw [h]
    norm_num [Nat.centralBinom]
  have hd : 0 < Real.log (p + 1 : ℕ) - Real.log p := by
    apply sub_pos.mpr
    exact Real.log_lt_log (by exact_mod_cast hp.pos) (by exact_mod_cast Nat.lt_succ_self p)
  have h := zetaPoleHalfCausalSource_cell_absolute_mass_lower hp.one_le
  rw [hcoeff] at h
  have hfactor := halfSingular_massFactor_lower hd.le
  linarith

end RHTower

