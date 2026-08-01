import GaloisForLFunctions.HTGeometry.ShiftOrbitSumBounds

/-!
# Factorial series over a shift orbit

Reciprocal rising factorials sum in closed form over a shift orbit: the difference of two
consecutive ones is `m` times the next reciprocal rising factorial, so

`∑_{n≥0} 1/((s+n)(s+n+1)⋯(s+n+m)) = 1/(m·s(s+1)⋯(s+m−1))`

exactly, for every `s` in the right half plane and every `m ≥ 1`.  These are the exactly summable
building blocks of the expansion of a polygamma jet: the reciprocal power `(s+n)^{-k}` differs from
the reciprocal rising factorial of the same length by one order, and the orbit bound turns that
difference into one gained power of the ordinate.
-/

open Filter Topology Complex

namespace GaloisForLFunctions

/-- The rising factorial `s(s+1)⋯(s+m−1)`. -/
noncomputable def risingProd (s : ℂ) (m : ℕ) : ℂ := ∏ j ∈ Finset.range m, (s + (j : ℂ))

@[simp] theorem risingProd_zero (s : ℂ) : risingProd s 0 = 1 := by
  simp [risingProd]

theorem risingProd_succ (s : ℂ) (m : ℕ) :
    risingProd s (m + 1) = risingProd s m * (s + (m : ℂ)) := by
  rw [risingProd, risingProd, Finset.prod_range_succ]

theorem risingProd_succ' (s : ℂ) (m : ℕ) :
    risingProd s (m + 1) = s * risingProd (s + 1) m := by
  rw [risingProd, risingProd, Finset.prod_range_succ']
  have hcongr : ∀ j ∈ Finset.range m, s + ((j : ℕ) + 1 : ℕ) = (s + 1) + (j : ℂ) := by
    intro j _
    push_cast
    ring
  rw [Finset.prod_congr rfl hcongr]
  simp [mul_comm]

theorem re_add_nat_pos {s : ℂ} (hs : 0 < s.re) (j : ℕ) : 0 < (s + (j : ℂ)).re := by
  have : (s + (j : ℂ)).re = s.re + (j : ℝ) := by simp
  rw [this]
  positivity

theorem risingProd_ne_zero {s : ℂ} (hs : 0 < s.re) (m : ℕ) : risingProd s m ≠ 0 := by
  rw [risingProd]
  refine Finset.prod_ne_zero_iff.mpr fun j _ => ?_
  intro h
  have := re_add_nat_pos hs j
  rw [h] at this
  simp at this

/-- The modulus of a rising factorial is at least the corresponding power of the abscissa. -/
theorem norm_risingProd_ge {s : ℂ} (hs : 0 < s.re) (m : ℕ) :
    s.re ^ m ≤ ‖risingProd s m‖ := by
  rw [risingProd, norm_prod]
  have hprod : ∏ _j ∈ Finset.range m, s.re = s.re ^ m := by
    rw [Finset.prod_const, Finset.card_range]
  rw [← hprod]
  refine Finset.prod_le_prod (fun j _ => hs.le) (fun j _ => ?_)
  have hre : (s + (j : ℂ)).re = s.re + (j : ℝ) := by simp
  calc s.re ≤ s.re + (j : ℝ) := le_add_of_nonneg_right (Nat.cast_nonneg j)
    _ = (s + (j : ℂ)).re := hre.symm
    _ ≤ |(s + (j : ℂ)).re| := le_abs_self _
    _ ≤ ‖s + (j : ℂ)‖ := Complex.abs_re_le_norm _

/-- **The telescoping step.** -/
theorem inv_risingProd_sub {s : ℂ} (hs : 0 < s.re) (m : ℕ) :
    (risingProd s m)⁻¹ - (risingProd (s + 1) m)⁻¹
      = (m : ℂ) * (risingProd s (m + 1))⁻¹ := by
  have hs1 : (0 : ℝ) < (s + 1).re := by
    have : (s + 1).re = s.re + 1 := by simp
    rw [this]; linarith
  have hP : risingProd s m ≠ 0 := risingProd_ne_zero hs m
  have hQ : risingProd (s + 1) m ≠ 0 := risingProd_ne_zero hs1 m
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    simp at hs
  have hfull : risingProd s (m + 1) = risingProd s m * (s + (m : ℂ)) := risingProd_succ s m
  have hfull' : risingProd s (m + 1) = s * risingProd (s + 1) m := risingProd_succ' s m
  have hne : risingProd s (m + 1) ≠ 0 := risingProd_ne_zero hs (m + 1)
  have hfac : (s + (m : ℂ)) ≠ 0 := by
    intro h
    rw [hfull, h, mul_zero] at hne
    exact hne rfl
  have h1 : (risingProd s m)⁻¹ = (s + (m : ℂ)) * (risingProd s (m + 1))⁻¹ := by
    rw [hfull]
    field_simp
  have h2 : (risingProd (s + 1) m)⁻¹ = s * (risingProd s (m + 1))⁻¹ := by
    rw [hfull']
    field_simp
  rw [h1, h2, ← sub_mul]
  congr 1
  ring

theorem summable_inv_risingProd {s : ℂ} (hs : 0 < s.re) (m : ℕ) :
    Summable (fun n : ℕ => ‖(risingProd (s + (n : ℂ)) (m + 2))⁻¹‖) := by
  refine Summable.of_nonneg_of_le (fun n => norm_nonneg _) (fun n => ?_)
    (summable_one_div_shift_pow hs (m + 2) (by omega))
  have hsn : (0 : ℝ) < (s + (n : ℂ)).re := re_add_nat_pos hs n
  have hge := norm_risingProd_ge hsn (m + 2)
  have hre : (s + (n : ℂ)).re = s.re + (n : ℝ) := by simp
  rw [hre] at hge
  have hpos : (0 : ℝ) < (s.re + (n : ℝ)) ^ (m + 2) := by
    have : (0 : ℝ) < s.re + (n : ℝ) := by positivity
    positivity
  rw [norm_inv, one_div]
  rw [inv_le_inv₀ (lt_of_lt_of_le hpos hge) hpos]
  exact hge

/-- **The factorial series.**  Reciprocal rising factorials sum in closed form over the orbit. -/
theorem hasSum_inv_risingProd {s : ℂ} (hs : 0 < s.re) (m : ℕ) :
    HasSum (fun n : ℕ => (risingProd (s + (n : ℂ)) (m + 2))⁻¹)
      (((m : ℂ) + 1)⁻¹ * (risingProd s (m + 1))⁻¹) := by
  have hsummable : Summable (fun n : ℕ => (risingProd (s + (n : ℂ)) (m + 2))⁻¹) :=
    Summable.of_norm (summable_inv_risingProd hs m)
  have hstep : ∀ n : ℕ, (risingProd (s + (n : ℂ)) (m + 2))⁻¹
      = ((m : ℂ) + 1)⁻¹ * ((risingProd (s + (n : ℂ)) (m + 1))⁻¹
        - (risingProd (s + ((n : ℂ) + 1)) (m + 1))⁻¹) := by
    intro n
    have hsn : (0 : ℝ) < (s + (n : ℂ)).re := re_add_nat_pos hs n
    have h := inv_risingProd_sub hsn (m + 1)
    have hcast : ((m + 1 : ℕ) : ℂ) = (m : ℂ) + 1 := by push_cast; ring
    have hidx : m + 1 + 1 = m + 2 := by omega
    rw [hcast, hidx] at h
    have hshift : s + (n : ℂ) + 1 = s + ((n : ℂ) + 1) := by ring
    rw [hshift] at h
    rw [h]
    have hne : ((m : ℂ) + 1) ≠ 0 := by
      intro hzero
      have : ((m + 1 : ℕ) : ℂ) = 0 := by push_cast; linear_combination hzero
      exact absurd (Nat.cast_eq_zero.mp this) (Nat.succ_ne_zero m)
    field_simp
  have hpartial : ∀ N : ℕ, ∑ n ∈ Finset.range N, (risingProd (s + (n : ℂ)) (m + 2))⁻¹
      = ((m : ℂ) + 1)⁻¹ * ((risingProd s (m + 1))⁻¹
        - (risingProd (s + (N : ℂ)) (m + 1))⁻¹) := by
    intro N
    rw [Finset.sum_congr rfl (fun n _ => hstep n), ← Finset.mul_sum]
    congr 1
    have hfun : ∀ n : ℕ, (risingProd (s + ((n : ℂ) + 1)) (m + 1))⁻¹
        = (risingProd (s + (((n + 1 : ℕ) : ℂ))) (m + 1))⁻¹ := by
      intro n
      congr 2
      push_cast
      ring
    rw [Finset.sum_congr rfl (fun n _ => by rw [hfun n])]
    have := Finset.sum_range_sub' (fun n : ℕ => (risingProd (s + (n : ℂ)) (m + 1))⁻¹) N
    simpa using this
  rw [hsummable.hasSum_iff_tendsto_nat]
  have hlim : Tendsto (fun N : ℕ => (risingProd (s + (N : ℂ)) (m + 1))⁻¹) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have hbound : ∀ N : ℕ, ‖(risingProd (s + (N : ℂ)) (m + 1))⁻¹‖
        ≤ (s.re ^ m * (s.re + (N : ℝ)))⁻¹ := by
      intro N
      have hsn : (0 : ℝ) < (s + (N : ℂ)).re := re_add_nat_pos hs N
      have hge := norm_risingProd_ge hsn (m + 1)
      have hre : (s + (N : ℂ)).re = s.re + (N : ℝ) := by simp
      rw [hre] at hge
      have hpos : (0 : ℝ) < s.re + (N : ℝ) := by positivity
      have hprodpos : (0 : ℝ) < s.re ^ m * (s.re + (N : ℝ)) := by positivity
      have hlow : s.re ^ m * (s.re + (N : ℝ)) ≤ (s.re + (N : ℝ)) ^ (m + 1) := by
        rw [pow_succ]
        exact mul_le_mul_of_nonneg_right
          (pow_le_pow_left₀ hs.le (by linarith [Nat.cast_nonneg (α := ℝ) N]) m) hpos.le
      have hchain : s.re ^ m * (s.re + (N : ℝ)) ≤ ‖risingProd (s + (N : ℂ)) (m + 1)‖ :=
        le_trans hlow hge
      have hXpos : (0 : ℝ) < ‖risingProd (s + (N : ℂ)) (m + 1)‖ :=
        lt_of_lt_of_le hprodpos hchain
      rw [norm_inv, inv_le_inv₀ hXpos hprodpos]
      exact hchain
    refine squeeze_zero (fun N => norm_nonneg _) hbound ?_
    have hdiv : Tendsto (fun N : ℕ => s.re ^ m * (s.re + (N : ℝ))) atTop atTop := by
      refine Filter.Tendsto.const_mul_atTop (by positivity) ?_
      exact tendsto_atTop_add_const_left _ s.re tendsto_natCast_atTop_atTop
    exact hdiv.inv_tendsto_atTop
  have hconst := (tendsto_const_nhds (x := ((m : ℂ) + 1)⁻¹ * (risingProd s (m + 1))⁻¹)
    (f := atTop (α := ℕ)))
  have hmul : Tendsto (fun N : ℕ => ((m : ℂ) + 1)⁻¹ * ((risingProd s (m + 1))⁻¹
      - (risingProd (s + (N : ℂ)) (m + 1))⁻¹)) atTop
      (nhds (((m : ℂ) + 1)⁻¹ * ((risingProd s (m + 1))⁻¹ - 0))) :=
    (tendsto_const_nhds.sub hlim).const_mul _
  rw [sub_zero] at hmul
  exact hmul.congr fun N => (hpartial N).symm

end GaloisForLFunctions
