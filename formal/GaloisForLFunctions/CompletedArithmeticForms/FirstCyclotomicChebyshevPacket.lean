import GaloisForLFunctions.CompletedArithmeticForms.FirstCyclotomicMellinAnalytic
import GaloisForLFunctions.CompletedArithmeticForms.ChebyshevCyclotomicTail

/-!
# The first Chebyshev cyclotomic difference

The discrete packet at an integer horizon is exactly the cyclic difference
of the first Fourier mode. Its squared norm is paid by first-band energy
with one inverse power of the horizon.
-/

noncomputable section
set_option autoImplicit false

open Complex Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

/-- The first difference packet at a real horizon. -/
def chebyshevFirstCyclotomicPacket (x : ℝ) : ℂ :=
  ∑ j ∈ Icc 1 ⌊x⌋₊, (chebyshevConductorCoeff j : ℂ) * firstCyclotomicKernel (j / x)

theorem firstCyclotomicKernel_one : firstCyclotomicKernel 1 = 0 := by
  rw [firstCyclotomicKernel, Complex.ofReal_one, mul_one,
    show Complex.I * (2 * Real.pi) = 2 * (Real.pi : ℂ) * Complex.I by ring,
    Complex.exp_two_pi_mul_I, sub_self]

private theorem firstCyclotomicKernel_nat_div (Q j : ℕ) :
    firstCyclotomicKernel ((j : ℝ) / Q) = 1 - cyclotomicMode Q 1 ^ j := by
  rw [firstCyclotomicKernel, cyclotomicMode, ← Complex.exp_nat_mul]
  congr 2
  push_cast
  ring

/-- At an integer horizon, the endpoint vanishes and the packet is the exact cyclic difference. -/
theorem chebyshevFirstCyclotomicPacket_nat {Q : ℕ} (hQ : 0 < Q) :
    chebyshevFirstCyclotomicPacket Q =
      (1 - cyclotomicMode Q 1) * prefixPacket Q chebyshevConductorCoeff (cyclotomicMode Q 1) := by
  classical
  have hQr : (Q : ℝ) ≠ 0 := by exact_mod_cast hQ.ne'
  have hset : Finset.Icc 1 Q = insert Q (Finset.Ico 1 Q) := by
    ext j
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_Ico]
    omega
  rw [chebyshevFirstCyclotomicPacket, Nat.floor_natCast, hset,
    sum_insert (by simp), div_self hQr, firstCyclotomicKernel_one, mul_zero, zero_add,
    prefixPacket_difference, ← sum_sub_distrib]
  apply sum_congr rfl
  intro j _
  rw [firstCyclotomicKernel_nat_div]
  ring

private theorem first_mode_gap_le {Q : ℕ} (hQ : 0 < Q) :
    ‖1 - cyclotomicMode Q 1‖ ≤ 2 * Real.pi / Q := by
  have hQr : (0 : ℝ) < Q := by exact_mod_cast hQ
  have h := norm_firstCyclotomicKernel_le (((1 : ℕ) : ℝ) / Q)
  rw [firstCyclotomicKernel_nat_div, pow_one] at h
  simpa only [Nat.cast_one, abs_of_pos (one_div_pos.mpr hQr), mul_one_div] using h

private theorem one_le_norm_first_mode_sum {Q : ℕ} (hQ : 8 ≤ Q) :
    1 ≤ ‖1 + cyclotomicMode Q 1‖ := by
  have hQr : (8 : ℝ) ≤ Q := by exact_mod_cast hQ
  have hQp : (0 : ℝ) < Q := by linarith only [hQr]
  have hgap := first_mode_gap_le (show 0 < Q by omega)
  have hratio : 2 * Real.pi / Q ≤ 1 := (div_le_one hQp).mpr
    (by linarith only [Real.pi_lt_four, hQr])
  have htriangle := norm_add_le (1 + cyclotomicMode Q 1) (1 - cyclotomicMode Q 1)
  rw [show (1 + cyclotomicMode Q 1) + (1 - cyclotomicMode Q 1) = (2 : ℂ) by ring,
    norm_ofNat] at htriangle
  linarith only [htriangle, hgap, hratio]

private theorem first_mode_energy_le_near {N : ℕ} (hN : 1 ≤ N) :
    ‖(1 + cyclotomicMode (N + 1) 1) *
      prefixPacket (N + 1) chebyshevConductorCoeff (cyclotomicMode (N + 1) 1)‖ ^ 2 ≤
        ((N : ℝ) + 1) * chebyshevCyclotomicNear N 1 := by
  have hmem : 1 ∈ (Finset.Ico 1 (N + 1)).filter (fun k => ¬ (1 < k ∧ 1 < N + 1 - k)) := by
    simp only [mem_filter, Finset.mem_Ico]
    omega
  have h := single_le_sum (fun k _ => sq_nonneg
    ‖(1 + cyclotomicMode (N + 1) k) *
      prefixPacket (N + 1) chebyshevConductorCoeff (cyclotomicMode (N + 1) k)‖) hmem
  have hcancel : ((N : ℝ) + 1) * chebyshevCyclotomicNear N 1 =
      ∑ k ∈ (Finset.Ico 1 (N + 1)).filter (fun k => ¬ (1 < k ∧ 1 < N + 1 - k)),
        ‖(1 + cyclotomicMode (N + 1) k) *
          prefixPacket (N + 1) chebyshevConductorCoeff (cyclotomicMode (N + 1) k)‖ ^ 2 := by
    unfold chebyshevCyclotomicNear
    field_simp
  rw [hcancel]
  exact h

/-- First-band energy controls the actual difference packet with one inverse horizon factor. -/
theorem norm_chebyshevFirstCyclotomicPacket_sq_le {N : ℕ} (hN : 7 ≤ N) :
    ‖chebyshevFirstCyclotomicPacket (N + 1 : ℕ)‖ ^ 2 ≤
      (2 * Real.pi) ^ 2 * chebyshevCyclotomicNear N 1 / ((N : ℝ) + 1) := by
  let z := cyclotomicMode (N + 1) 1
  let P := prefixPacket (N + 1) chebyshevConductorCoeff z
  have hQ : 0 < (N : ℝ) + 1 := by positivity
  have hgap : ‖1 - z‖ ≤ 2 * Real.pi / ((N : ℝ) + 1) := by
    simpa only [z, Nat.cast_add, Nat.cast_one] using first_mode_gap_le (by omega : 0 < N + 1)
  have hplus : 1 ≤ ‖1 + z‖ := one_le_norm_first_mode_sum (by omega : 8 ≤ N + 1)
  have hp : ‖P‖ ^ 2 ≤ ‖(1 + z) * P‖ ^ 2 := by
    apply pow_le_pow_left₀ (norm_nonneg _) _ 2
    rw [norm_mul]
    exact le_mul_of_one_le_left (norm_nonneg _) hplus
  have henergy : ‖P‖ ^ 2 ≤ ((N : ℝ) + 1) * chebyshevCyclotomicNear N 1 :=
    hp.trans (first_mode_energy_le_near (by omega))
  rw [chebyshevFirstCyclotomicPacket_nat (by omega), norm_mul, mul_pow]
  change ‖1 - z‖ ^ 2 * ‖P‖ ^ 2 ≤ _
  calc
    _ ≤ (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 * ‖P‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hgap 2) (sq_nonneg _)
    _ ≤ (2 * Real.pi / ((N : ℝ) + 1)) ^ 2 *
        (((N : ℝ) + 1) * chebyshevCyclotomicNear N 1) :=
      mul_le_mul_of_nonneg_left henergy (sq_nonneg _)
    _ = _ := by field_simp [hQ.ne']

#print axioms chebyshevFirstCyclotomicPacket_nat
#print axioms norm_chebyshevFirstCyclotomicPacket_sq_le


/-- The first difference kernel has the Lipschitz constant of one full turn. -/
theorem norm_firstCyclotomicKernel_sub_le (u v : ℝ) :
    ‖firstCyclotomicKernel u - firstCyclotomicKernel v‖ ≤ 2 * Real.pi * |u - v| := by
  have hphase (t : ℝ) : Complex.I * (2 * Real.pi) * t =
      ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [firstCyclotomicKernel, firstCyclotomicKernel,
    show (1 - Complex.exp (Complex.I * (2 * Real.pi) * u)) -
        (1 - Complex.exp (Complex.I * (2 * Real.pi) * v)) =
      Complex.exp (Complex.I * (2 * Real.pi) * v) -
        Complex.exp (Complex.I * (2 * Real.pi) * u) by ring,
    norm_sub_rev, hphase u, hphase v]
  have h := GaloisForLFunctions.HTGeometry.norm_exp_sub_exp_le
    (2 * Real.pi * u) (2 * Real.pi * v)
  rwa [← mul_sub, abs_mul, abs_mul,
    abs_of_pos (by norm_num : (0 : ℝ) < 2), abs_of_pos Real.pi_pos] at h

/-- Every positive conductor coefficient is uniformly bounded. -/
theorem norm_chebyshevConductorCoeff_le_six {j : ℕ} (hj : 1 ≤ j) :
    ‖(chebyshevConductorCoeff j : ℂ)‖ ≤ 6 := by
  have hjr : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hs : 1 ≤ Real.sqrt (j : ℝ) := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hjr
  have hsp : 0 < Real.sqrt (j : ℝ) := lt_of_lt_of_le zero_lt_one hs
  rw [Complex.norm_real, Real.norm_eq_abs]
  refine (abs_chebyshevConductorCoeff_le hj).trans ((div_le_iff₀ hsp).mpr ?_)
  linarith only [hs]

/-- Moving a horizon within one integer cell changes the packet by a uniform constant. -/
theorem norm_chebyshevFirstCyclotomicPacket_sub_floor_le {x : ℝ} (hx : 1 ≤ x) :
    ‖chebyshevFirstCyclotomicPacket x - chebyshevFirstCyclotomicPacket ⌊x⌋₊‖ ≤
      12 * Real.pi := by
  let Q := ⌊x⌋₊
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hQ1 : 1 ≤ Q := (Nat.le_floor_iff hx0.le).mpr (by simpa only [Nat.cast_one] using hx)
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hQx : (Q : ℝ) ≤ x := Nat.floor_le hx0.le
  have hxQ : x < (Q : ℝ) + 1 := Nat.lt_floor_add_one x
  have hphase (j : ℕ) (hj : j ∈ Icc 1 Q) :
      |(j : ℝ) / x - (j : ℝ) / Q| ≤ 1 / (Q : ℝ) := by
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hjQ : (j : ℝ) ≤ Q := by exact_mod_cast (mem_Icc.mp hj).2
    have horder : (j : ℝ) / x ≤ (j : ℝ) / Q :=
      div_le_div_of_nonneg_left hj0 hQ0 hQx
    rw [abs_of_nonpos (sub_nonpos.mpr horder)]
    have hnum : (j : ℝ) * (x - Q) ≤ x := by
      calc
        _ ≤ (j : ℝ) * 1 := mul_le_mul_of_nonneg_left (by linarith only [hxQ]) hj0
        _ = j := mul_one _
        _ ≤ Q := hjQ
        _ ≤ x := hQx
    calc
      -((j : ℝ) / x - (j : ℝ) / Q) =
          (j : ℝ) * (x - Q) / (x * Q) := by field_simp [hx0.ne', hQ0.ne']; ring
      _ ≤ x / (x * Q) := div_le_div_of_nonneg_right hnum (mul_pos hx0 hQ0).le
      _ = 1 / (Q : ℝ) := by field_simp [hx0.ne', hQ0.ne']
  have hterm (j : ℕ) (hj : j ∈ Icc 1 Q) :
      ‖(chebyshevConductorCoeff j : ℂ) *
        (firstCyclotomicKernel (j / x) - firstCyclotomicKernel (j / (Q : ℝ)))‖ ≤
          12 * Real.pi / (Q : ℝ) := by
    rw [norm_mul]
    have hker := (norm_firstCyclotomicKernel_sub_le ((j : ℝ) / x) ((j : ℝ) / Q)).trans
      (mul_le_mul_of_nonneg_left (hphase j hj) (by positivity : 0 ≤ 2 * Real.pi))
    calc
      _ ≤ 6 * (2 * Real.pi * (1 / (Q : ℝ))) :=
        mul_le_mul (norm_chebyshevConductorCoeff_le_six (mem_Icc.mp hj).1) hker
          (norm_nonneg _) (by norm_num)
      _ = _ := by ring
  rw [chebyshevFirstCyclotomicPacket, chebyshevFirstCyclotomicPacket, Nat.floor_natCast,
    ← sum_sub_distrib]
  change ‖∑ j ∈ Icc 1 Q, ((chebyshevConductorCoeff j : ℂ) * firstCyclotomicKernel (j / x) -
    (chebyshevConductorCoeff j : ℂ) * firstCyclotomicKernel (j / (Q : ℝ)))‖ ≤ _
  calc
    _ ≤ ∑ j ∈ Icc 1 Q, ‖(chebyshevConductorCoeff j : ℂ) * firstCyclotomicKernel (j / x) -
        (chebyshevConductorCoeff j : ℂ) * firstCyclotomicKernel (j / (Q : ℝ))‖ := norm_sum_le _ _
    _ ≤ ∑ _j ∈ Icc 1 Q, 12 * Real.pi / (Q : ℝ) := by
      apply sum_le_sum
      intro j hj
      rw [← mul_sub]
      exact hterm j hj
    _ = 12 * Real.pi := by
      simp only [sum_const, nsmul_eq_mul]
      rw [show (Icc 1 Q).card = Q by simp]
      field_simp [hQ0.ne']

#print axioms norm_chebyshevFirstCyclotomicPacket_sub_floor_le

end GaloisForLFunctions.CompletedArithmeticForms
