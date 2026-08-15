import GaloisForLFunctions.RHTower.CCMDiagonalFockLift

/-!
# The zero packets of the infinitesimal real Euler-ray kernel

Each paired zero `lambda` of the centred completed function contributes to

```text
J (x, y) = (Q x + Q y)/(x + y)
```

the packet `2 (x y - lambda^2)/((x^2 - lambda^2)(y^2 - lambda^2))`.  On the critical line
(`lambda = i gamma`) this is a *sum* of two rank-one Gram kernels, hence positive semidefinite; off
the line (`lambda = a` real, the model case of a conjugate quartet) it is a *difference* of two
rank-one Gram kernels, and its two-point minor is `-4 a^2 (x - y)^2/(...)^2 < 0`, so it carries a
genuine negative square.

Also proved here: the causal/anti-causal polarization
`f conj g + g conj f = |u><u| - |v><v|`, the diagonal identity `J (x, x) = Q x / x`, and the
infinitesimal derivation `(13)`: `J` is the `omega -> 0` limit of the shifted Cauchy--Loewner
kernel of `f_omega (x) = X (x - omega)/X (x + omega)`.
-/

open Matrix MeasureTheory Set Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-! ## Rank-one Gram kernels -/

/-- The rank-one Gram matrix of a real feature vector. -/
def rankOneMatrix {n : ℕ} (u : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => u i * u j

theorem posSemidef_rankOneMatrix {n : ℕ} (u : Fin n → ℝ) : (rankOneMatrix u).PosSemidef := by
  constructor
  · ext i j
    simp only [Matrix.conjTranspose_apply, rankOneMatrix, Matrix.of_apply, star_trivial]
    ring
  · intro α
    have hval : (α.sum fun i xi => α.sum fun j xj => star xi * rankOneMatrix u i j * xj)
        = (α.sum fun i xi => xi * u i) ^ 2 := by
      rw [Finsupp.sum_fintype _ _ (by intro i; simp)]
      have hinner : ∀ i : Fin n, (α.sum fun j xj => star (α i) * rankOneMatrix u i j * xj)
          = (α i * u i) * ∑ j, α j * u j := by
        intro i
        rw [Finsupp.sum_fintype _ _ (by intro j; simp), Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [rankOneMatrix, Matrix.of_apply, star_trivial]
        ring
      rw [Finset.sum_congr rfl fun i _ => hinner i, ← Finset.sum_mul,
        Finsupp.sum_fintype _ _ (by intro i; simp), sq]
    rw [hval]
    positivity

/-! ## The critical-line packet -/

/-- The packet kernel of a critical-line zero at height `gamma`, equation `(9)`. -/
def imagPacketKernel (γ x y : ℝ) : ℝ := 2 * (x * y + γ ^ 2) / ((x ^ 2 + γ ^ 2) * (y ^ 2 + γ ^ 2))

/-- **Equation (9).**  A critical-line packet is the sum of two rank-one Gram kernels. -/
theorem imagPacketKernel_eq {γ x y : ℝ} (hx : x ^ 2 + γ ^ 2 ≠ 0) (hy : y ^ 2 + γ ^ 2 ≠ 0) :
    imagPacketKernel γ x y
      = 2 * (x / (x ^ 2 + γ ^ 2)) * (y / (y ^ 2 + γ ^ 2))
        + 2 * (γ / (x ^ 2 + γ ^ 2)) * (γ / (y ^ 2 + γ ^ 2)) := by
  unfold imagPacketKernel
  field_simp

/-- **Equation (9), positivity.**  Hence every critical-line packet is positive semidefinite. -/
theorem posSemidef_imagPacketMatrix {n : ℕ} {γ : ℝ} {x : Fin n → ℝ}
    (hx : ∀ i, x i ^ 2 + γ ^ 2 ≠ 0) :
    (kernelMatrix (imagPacketKernel γ) x).PosSemidef := by
  have hsum : kernelMatrix (imagPacketKernel γ) x
      = (2 : ℝ) • rankOneMatrix (fun i => x i / (x i ^ 2 + γ ^ 2))
        + (2 : ℝ) • rankOneMatrix (fun i => γ / (x i ^ 2 + γ ^ 2)) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, rankOneMatrix, Matrix.of_apply,
      kernelMatrix_apply, smul_eq_mul]
    rw [imagPacketKernel_eq (hx i) (hx j)]
    ring
  rw [hsum]
  exact ((posSemidef_rankOneMatrix _).smul (by norm_num)).add
    ((posSemidef_rankOneMatrix _).smul (by norm_num))

/-! ## The off-line packet -/

/-- The packet kernel of a real off-line parameter `a`, equation `(10)`. -/
def realPacketKernel (a x y : ℝ) : ℝ := 2 * (x * y - a ^ 2) / ((x ^ 2 - a ^ 2) * (y ^ 2 - a ^ 2))

/-- **Equation (10).**  An off-line packet is a *difference* of two rank-one Gram kernels. -/
theorem realPacketKernel_eq {a x y : ℝ} (hx : x ^ 2 - a ^ 2 ≠ 0) (hy : y ^ 2 - a ^ 2 ≠ 0) :
    realPacketKernel a x y
      = 2 * (x / (x ^ 2 - a ^ 2)) * (y / (y ^ 2 - a ^ 2))
        - 2 * (a / (x ^ 2 - a ^ 2)) * (a / (y ^ 2 - a ^ 2)) := by
  unfold realPacketKernel
  field_simp

/-- The two-point minor of an off-line packet. -/
theorem det_realPacket_two_point {a x y : ℝ} (hx : x ^ 2 - a ^ 2 ≠ 0) (hy : y ^ 2 - a ^ 2 ≠ 0) :
    realPacketKernel a x x * realPacketKernel a y y
        - realPacketKernel a x y * realPacketKernel a y x
      = -(4 * a ^ 2 * (x - y) ^ 2) / ((x ^ 2 - a ^ 2) ^ 2 * (y ^ 2 - a ^ 2) ^ 2) := by
  unfold realPacketKernel
  field_simp
  ring

/-- **Equation (10), negative square.**  The two-point minor of a genuine off-line packet is
strictly negative, so the packet is not positive semidefinite. -/
theorem det_realPacket_two_point_neg {a x y : ℝ} (ha : a ≠ 0) (hne : x ≠ y)
    (hx : x ^ 2 - a ^ 2 ≠ 0) (hy : y ^ 2 - a ^ 2 ≠ 0) :
    realPacketKernel a x x * realPacketKernel a y y
        - realPacketKernel a x y * realPacketKernel a y x < 0 := by
  rw [det_realPacket_two_point hx hy]
  have hnum : 0 < 4 * a ^ 2 * (x - y) ^ 2 := by
    have h1 : 0 < a ^ 2 := by positivity
    have h2 : 0 < (x - y) ^ 2 := by
      have : x - y ≠ 0 := sub_ne_zero.2 hne
      positivity
    positivity
  have hden : 0 < (x ^ 2 - a ^ 2) ^ 2 * (y ^ 2 - a ^ 2) ^ 2 := by positivity
  rw [neg_div, neg_lt_zero]
  positivity

/-- The two-point packet matrix. -/
def realPacketMatrix (a x y : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![realPacketKernel a x x, realPacketKernel a x y;
     realPacketKernel a y x, realPacketKernel a y y]

theorem not_posSemidef_realPacketMatrix {a x y : ℝ} (ha : a ≠ 0) (hne : x ≠ y)
    (hx : x ^ 2 - a ^ 2 ≠ 0) (hy : y ^ 2 - a ^ 2 ≠ 0) :
    ¬ (realPacketMatrix a x y).PosSemidef := by
  intro hpos
  have hdet := hpos.det_nonneg
  rw [realPacketMatrix, Matrix.det_fin_two_of] at hdet
  exact absurd hdet (not_le.2 (det_realPacket_two_point_neg ha hne hx hy))

/-! ## The causal / anti-causal polarization -/

/-- **The quartet polarization.**  A causal/anti-causal Hermitian packet is one positive square
minus one negative square. -/
theorem quartet_polarization (f g : ℂ) :
    f * (starRingEnd ℂ) g + g * (starRingEnd ℂ) f
      = ((f + g) / Real.sqrt 2) * (starRingEnd ℂ) ((f + g) / Real.sqrt 2)
        - ((f - g) / Real.sqrt 2) * (starRingEnd ℂ) ((f - g) / Real.sqrt 2) := by
  have h2 : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    norm_num
  have hne : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
    intro h
    rw [h] at h2
    norm_num at h2
  simp only [map_div₀, map_add, map_sub, Complex.conj_ofReal]
  field_simp
  ring_nf
  linear_combination (f * (starRingEnd ℂ) g + g * (starRingEnd ℂ) f) * h2

/-! ## The packet algebra and the diagonal -/

/-- **Equation (7).**  The paired zero packet. -/
theorem qPacket_eq {z lam : ℂ} (h1 : z - lam ≠ 0) (h2 : z + lam ≠ 0) :
    (z - lam)⁻¹ + (z + lam)⁻¹ = 2 * z / (z ^ 2 - lam ^ 2) := by
  have hprod : z ^ 2 - lam ^ 2 = (z - lam) * (z + lam) := by ring
  rw [hprod]
  field_simp
  ring

/-- **Equation (8).**  The packet's contribution to the Euler-ray kernel. -/
theorem packet_contribution {x y lam : ℝ} (hx : x ^ 2 - lam ^ 2 ≠ 0) (hy : y ^ 2 - lam ^ 2 ≠ 0)
    (hxy : x + y ≠ 0) :
    (2 * x / (x ^ 2 - lam ^ 2) + 2 * y / (y ^ 2 - lam ^ 2)) / (x + y)
      = 2 * (x * y - lam ^ 2) / ((x ^ 2 - lam ^ 2) * (y ^ 2 - lam ^ 2)) := by
  field_simp
  ring

/-- **Equation (17).**  The diagonal of the Euler-ray kernel. -/
theorem euler_kernel_diagonal (Q : ℝ → ℝ) {x : ℝ} (hx : x ≠ 0) :
    rhKernel Q x x = Q x / x := by
  unfold rhKernel
  rw [show x + x = 2 * x from by ring, show Q x + Q x = 2 * Q x from by ring]
  field_simp

/-! ## The infinitesimal derivation -/

/-- **Equations (11)–(13).**  The Euler-ray kernel is the `omega -> 0` derivative of the shifted
Cauchy–Loewner kernel of `f_omega (x) = X (x - omega)/X (x + omega)`. -/
theorem hasDerivAt_shiftedQuotient {X : ℝ → ℝ} {Xp : ℝ → ℝ} {x : ℝ}
    (hX : ∀ u, HasDerivAt X (Xp u) u) (hne : X x ≠ 0) :
    HasDerivAt (fun ω : ℝ => X (x - ω) / X (x + ω)) (-(2 * (Xp x / X x))) 0 := by
  have hnum : HasDerivAt (fun ω : ℝ => X (x - ω)) (-Xp x) 0 := by
    have hb : HasDerivAt X (Xp x) (x - 0) := by
      rw [sub_zero]; exact hX x
    exact hb.comp_const_sub x 0
  have hden : HasDerivAt (fun ω : ℝ => X (x + ω)) (Xp x) 0 := by
    have hb : HasDerivAt X (Xp x) (x + 0) := by
      rw [add_zero]; exact hX x
    exact hb.comp_const_add x 0
  have hne0 : X (x + 0) ≠ 0 := by simpa using hne
  have hdiv := hnum.fun_div hden hne0
  refine hdiv.congr_deriv ?_
  simp only [add_zero, sub_zero]
  field_simp
  ring

/-- **Equation (13).**  The infinitesimal shifted Cauchy–Loewner kernel is the Euler-ray kernel. -/
theorem hasDerivAt_loewnerKernel {X Xp : ℝ → ℝ} {x y : ℝ}
    (hX : ∀ u, HasDerivAt X (Xp u) u) (hx : X x ≠ 0) (hy : X y ≠ 0) (hxy : x + y ≠ 0) :
    HasDerivAt (fun ω : ℝ =>
        (1 - (X (x - ω) / X (x + ω)) * (X (y - ω) / X (y + ω))) / (x + y))
      (2 * ((Xp x / X x + Xp y / X y) / (x + y))) 0 := by
  have hfx := hasDerivAt_shiftedQuotient hX hx
  have hfy := hasDerivAt_shiftedQuotient hX hy
  have hprod := hfx.fun_mul hfy
  simp only [sub_zero, add_zero, div_self hx, div_self hy] at hprod
  have hsub := (hasDerivAt_const (0 : ℝ) (1 : ℝ)).fun_sub hprod
  have hdiv := hsub.div_const (x + y)
  refine hdiv.congr_deriv ?_
  field_simp
  ring

end GaloisForLFunctions.RHTower

end
