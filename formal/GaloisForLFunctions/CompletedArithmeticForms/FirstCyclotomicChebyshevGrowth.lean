import GaloisForLFunctions.CompletedArithmeticForms.FirstCyclotomicChebyshevComparison

/-!
# First-band energy controls continuous packet growth

An energy bound of exponent `r ≥ 1` gives growth exponent `(r-1)/2`
for the literal continuous first-mode packet. The integer mode bound,
real-horizon interpolation and uniform quadrature error supply the estimate.
-/

noncomputable section
set_option autoImplicit false
open Complex Filter Asymptotics

namespace GaloisForLFunctions.CompletedArithmeticForms

private theorem norm_chebyshevFirstCyclotomicPacket_nat_le_of_power
    {r C : ℝ} (hr : 1 ≤ r) (hC : 0 ≤ C)
    (hB : ∀ N : ℕ, 2 ≤ N → chebyshevCyclotomicNear N 1 ≤ C * (N : ℝ) ^ r)
    {Q : ℕ} (hQ : 8 ≤ Q) :
    ‖chebyshevFirstCyclotomicPacket Q‖ ≤
      (2 * Real.pi * (C + 1)) * (Q : ℝ) ^ ((r - 1) / 2) := by
  have hQ0 : (0 : ℝ) < Q := by exact_mod_cast (show 0 < Q by omega)
  have hQr : ((Q - 1 : ℕ) : ℝ) + 1 = (Q : ℝ) := by
    rw [Nat.cast_sub (by omega), Nat.cast_one]
    ring
  have hpacket := norm_chebyshevFirstCyclotomicPacket_sq_le (N := Q - 1) (by omega)
  rw [Nat.sub_add_cancel (by omega), hQr] at hpacket
  have hpower : ((Q - 1 : ℕ) : ℝ) ^ r ≤ (Q : ℝ) ^ r :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le Q 1)
      (by linarith only [hr])
  have henergy : chebyshevCyclotomicNear (Q - 1) 1 ≤ C * (Q : ℝ) ^ r :=
    (hB (Q - 1) (by omega)).trans (mul_le_mul_of_nonneg_left hpower hC)
  have hexponent : ((Q : ℝ) ^ ((r - 1) / 2)) ^ 2 = (Q : ℝ) ^ (r - 1) := by
    rw [pow_two, ← Real.rpow_add hQ0]
    congr 1
    ring
  have hconst : (2 * Real.pi) ^ 2 * C ≤ (2 * Real.pi * (C + 1)) ^ 2 := by
    calc
      _ ≤ (2 * Real.pi) ^ 2 * (C + 1) ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith only [hC, sq_nonneg C]) (sq_nonneg _)
      _ = _ := (mul_pow _ _ 2).symm
  have hsq : ‖chebyshevFirstCyclotomicPacket Q‖ ^ 2 ≤
      ((2 * Real.pi * (C + 1)) * (Q : ℝ) ^ ((r - 1) / 2)) ^ 2 := by
    calc
      _ ≤ (2 * Real.pi) ^ 2 * chebyshevCyclotomicNear (Q - 1) 1 / Q := hpacket
      _ ≤ (2 * Real.pi) ^ 2 * (C * (Q : ℝ) ^ r) / Q :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left henergy (sq_nonneg _)) hQ0.le
      _ = ((2 * Real.pi) ^ 2 * C) * (Q : ℝ) ^ (r - 1) := by
        rw [Real.rpow_sub hQ0, Real.rpow_one]
        ring
      _ ≤ (2 * Real.pi * (C + 1)) ^ 2 * (Q : ℝ) ^ (r - 1) :=
        mul_le_mul_of_nonneg_right hconst (Real.rpow_nonneg hQ0.le _)
      _ = _ := by
        rw [mul_pow (2 * Real.pi * (C + 1)) ((Q : ℝ) ^ ((r - 1) / 2)) 2, hexponent]
  have hright : 0 ≤ (2 * Real.pi * (C + 1)) * (Q : ℝ) ^ ((r - 1) / 2) := by positivity
  nlinarith only [hsq, hright, norm_nonneg (chebyshevFirstCyclotomicPacket Q)]

/-- A first-band power bound gives the corresponding growth of the actual continuous packet. -/
theorem isBigO_chebyshevFirstCyclotomicContinuous_of_near_power
    {r C : ℝ} (hr : 1 ≤ r) (hC : 0 ≤ C)
    (hB : ∀ N : ℕ, 2 ≤ N → chebyshevCyclotomicNear N 1 ≤ C * (N : ℝ) ^ r) :
    chebyshevFirstCyclotomicContinuous =O[atTop] fun x : ℝ => x ^ ((r - 1) / 2) := by
  let D : ℝ := 2 * Real.pi * (C + 1)
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hb : 0 ≤ (r - 1) / 2 := by linarith only [hr]
  refine Asymptotics.IsBigO.of_bound (D + 92 * Real.pi) ?_
  filter_upwards [eventually_ge_atTop (8 : ℝ)] with x hx
  have hx0 : 0 ≤ x := by linarith only [hx]
  have hx1 : 1 ≤ x := by linarith only [hx]
  have hQ : 8 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).mpr (by simpa using hx)
  have hfloor : (⌊x⌋₊ : ℝ) ^ ((r - 1) / 2) ≤ x ^ ((r - 1) / 2) :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le hx0) hb
  have hone : 1 ≤ x ^ ((r - 1) / 2) := by
    simpa only [Real.rpow_zero] using Real.rpow_le_rpow_of_exponent_le hx1 hb
  have hnat := norm_chebyshevFirstCyclotomicPacket_nat_le_of_power hr hC hB hQ
  have hinterp := norm_chebyshevFirstCyclotomicPacket_sub_floor_le hx1
  have hcompare := norm_chebyshevFirstCyclotomicContinuous_sub_packet_le
    (by linarith only [hx] : 2 ≤ x)
  have htriangle : ‖chebyshevFirstCyclotomicContinuous x‖ ≤
      80 * Real.pi + 12 * Real.pi + D * x ^ ((r - 1) / 2) := by
    calc
      _ ≤ ‖chebyshevFirstCyclotomicContinuous x - chebyshevFirstCyclotomicPacket x‖ +
          ‖chebyshevFirstCyclotomicPacket x‖ := norm_le_norm_sub_add _ _
      _ ≤ 80 * Real.pi +
          (‖chebyshevFirstCyclotomicPacket x - chebyshevFirstCyclotomicPacket ⌊x⌋₊‖ +
            ‖chebyshevFirstCyclotomicPacket ⌊x⌋₊‖) :=
        add_le_add hcompare (norm_le_norm_sub_add _ _)
      _ ≤ 80 * Real.pi + (12 * Real.pi + D * x ^ ((r - 1) / 2)) :=
        add_le_add le_rfl (add_le_add hinterp
          (hnat.trans (mul_le_mul_of_nonneg_left hfloor hD)))
      _ = _ := by ring
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 _)]
  calc
    _ ≤ 80 * Real.pi + 12 * Real.pi + D * x ^ ((r - 1) / 2) := htriangle
    _ ≤ _ := by
      have hscale := mul_le_mul_of_nonneg_left hone
        (show 0 ≤ 92 * Real.pi by positivity)
      nlinarith only [hscale]

#print axioms isBigO_chebyshevFirstCyclotomicContinuous_of_near_power

end GaloisForLFunctions.CompletedArithmeticForms
