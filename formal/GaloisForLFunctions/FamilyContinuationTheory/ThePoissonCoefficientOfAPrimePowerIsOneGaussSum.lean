import GaloisForLFunctions.FamilyContinuationTheory.TheGaussSumOfAPrimePowerLivesOnOneLayer

/-!
# The Poisson coefficient of a prime power is one Gauss sum

Poisson summation of the cubic-theta probe in its element variable `m` meets, at a prime `π` of
`O = ℤ[ω]` with residue character `χ`, the function `m ↦ χ(m)^t g_{χ^k}(π^k, −m)` (index `A` with
`v_π(A) = t`, row twist `s` with `v_π(s) = k`). Its Fourier transform modulo `π^{t+k}` at the
frequency `h` is

`P(t, k; h) = Σ_m χ(m)^t ψ(hm) I(m)`,  `I(m) = Σ_d χ(d)^k ψ(−π^t m d)`  (`localPoisson`)

with `ψ = ψ_{π^{t+k}}` and every sum over `O/(π^{t+k})`. For a prime `π` with `N(π) = Q`:

* `t = 0`: `P = Q^k χ(h)^k` (`localPoisson_zero_left`);
* `k = 0`, `t ≥ 1`: `P = Q^t` times the layer sum of `χ^t` at `h` (`localPoisson_zero_right`);
* `k = 1`, `t ≥ 1`: `P = Q^t χ(−1)⁻¹ G(χ)` times the layer sum of the character `χ^{t−1}`
  (zero-extended, also for `t = 1`) modulo `π^{t+1}` (`localPoisson_one`);
* `k ≥ 2`, `t ≥ 1`: `P = 0` (`localPoisson_eq_zero`).

With the layer sums of `TheGaussSumOfAPrimePowerLivesOnOneLayer` these are the local values of
the Poisson coefficient in the scalar Euler identity: a nonzero value needs `π^{t−1} ∣ h`
(`k = 0`) or `π^t ∣ h` (`k = 1`), which ties the valuation of the frequency to the cube exponent
of the index.
-/

noncomputable section

open scoped BigOperators Classical

namespace GaloisForLFunctions.FamilyContinuationTheory

open MetaplecticMobiusDescent.Eisenstein

variable (π : O) [NeZero π] (χ : MulChar (O ⧸ Ideal.span {π}) ℂ)

/-- The twisted row sum `I(m) = Σ_d χ(d)^k ψ_{π^{t+k}}(−π^t m d)`. -/
def rowGauss {t k : ℕ} (hn : 1 ≤ t + k) (m : O ⧸ Ideal.span {π ^ (t + k)}) : ℂ :=
  ∑ d : O ⧸ Ideal.span {π ^ (t + k)}, χ (layerReduction π hn d) ^ k *
    principalTraceChar (π ^ (t + k)) (NeZero.ne _) (-(Ideal.Quotient.mk _ (π ^ t) * m * d))

/-- The local Poisson coefficient `Σ_m χ(m)^t ψ_{π^{t+k}}(hm) I(m)`. -/
def localPoisson {t k : ℕ} (hn : 1 ≤ t + k) (h : O) : ℂ :=
  ∑ m : O ⧸ Ideal.span {π ^ (t + k)}, χ (layerReduction π hn m) ^ t *
    principalTraceChar (π ^ (t + k)) (NeZero.ne _) (Ideal.Quotient.mk _ h * m) *
      rowGauss π χ hn m

/-- A residue sum over `O/(π^n)` of a primitive character at a nonzero multiplier vanishes. -/
theorem sum_traceChar_mul_eq (n : ℕ) (y : O ⧸ Ideal.span {π ^ n}) :
    ∑ m : O ⧸ Ideal.span {π ^ n}, principalTraceChar (π ^ n) (NeZero.ne _) (m * y) =
      if y = 0 then (Ideal.absNorm (Ideal.span {π}) : ℂ) ^ n else 0 := by
  rw [AddChar.sum_mulShift y (principalTraceChar_primitive _ _)]
  split_ifs <;> simp [card_quot_span_pow]

/-- **`t = 0`.** `P(0, k; h) = Q^k χ(h)^k`. -/
theorem localPoisson_zero_left {k : ℕ} (hn : 1 ≤ 0 + k) (h : O) :
    localPoisson π χ hn h =
      (Ideal.absNorm (Ideal.span {π}) : ℂ) ^ (0 + k) *
        χ (Ideal.Quotient.mk _ h) ^ k := by
  unfold localPoisson rowGauss
  simp only [pow_zero, one_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  have hphase : ∀ d m : O ⧸ Ideal.span {π ^ (0 + k)},
      principalTraceChar (π ^ (0 + k)) (NeZero.ne _) (Ideal.Quotient.mk _ h * m) *
        (χ (layerReduction π hn d) ^ k *
          principalTraceChar (π ^ (0 + k)) (NeZero.ne _) (-(Ideal.Quotient.mk _ 1 * m * d))) =
      χ (layerReduction π hn d) ^ k *
        principalTraceChar (π ^ (0 + k)) (NeZero.ne _) (m * (Ideal.Quotient.mk _ h - d)) := by
    intro d m
    rw [map_one, one_mul, mul_left_comm, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  simp only [hphase, ← Finset.mul_sum, sum_traceChar_mul_eq]
  rw [Finset.sum_eq_single (Ideal.Quotient.mk _ h)]
  · rw [sub_self, if_pos rfl, layerReduction_mk, mul_comm]
  · intro d _ hd
    rw [if_neg (sub_ne_zero.mpr (Ne.symm hd)), mul_zero]
  · intro hmem
    exact absurd (Finset.mem_univ _) hmem

/-- **`k = 0`.** `P(t, 0; h) = Q^t` times the layer sum of `χ^t`. -/
theorem localPoisson_zero_right {t : ℕ} (hn : 1 ≤ t + 0) (h : O) :
    localPoisson π χ hn h =
      (Ideal.absNorm (Ideal.span {π}) : ℂ) ^ t * layerGauss π hn (fun e => χ e ^ t) h := by
  have hrow : ∀ m : O ⧸ Ideal.span {π ^ (t + 0)}, rowGauss π χ hn m =
      (Ideal.absNorm (Ideal.span {π}) : ℂ) ^ t := by
    intro m
    unfold rowGauss
    have h0 : Ideal.Quotient.mk (Ideal.span {π ^ (t + 0)}) (π ^ t) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    simp only [h0, zero_mul, neg_zero, AddChar.map_zero_eq_one, pow_zero, mul_one,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
    exact card_quot_span_pow π t
  unfold localPoisson layerGauss
  simp only [hrow, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => by ring

/-- The row sum for `k = 1`: on a unit residue it is `Q^t χ(−m)⁻¹ G(χ)`. -/
theorem rowGauss_one [(Ideal.span {π}).IsMaximal] {t : ℕ} (hn : 1 ≤ t + 1)
    (m : O ⧸ Ideal.span {π ^ (t + 1)}) (hm : layerReduction π hn m ≠ 0) :
    rowGauss π χ hn m * χ (-layerReduction π hn m) =
      (Ideal.absNorm (Ideal.span {π}) : ℂ) ^ t *
        gaussSum χ (principalTraceChar π (NeZero.ne _)) := by
  letI : Field (O ⧸ Ideal.span {π}) := Ideal.Quotient.field _
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective m
  -- the phase factors through the reduction
  have hphase : ∀ d : O ⧸ Ideal.span {π ^ (t + 1)},
      principalTraceChar (π ^ (t + 1)) (NeZero.ne _)
          (-(Ideal.Quotient.mk _ (π ^ t) * Ideal.Quotient.mk _ x * d)) =
        principalTraceChar π (NeZero.ne _)
          (Ideal.Quotient.mk _ (-x) * layerReduction π hn d) := by
    intro d
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective d
    rw [layerReduction_mk, ← map_mul, ← map_mul, ← map_mul, ← map_neg]
    have h := principalTraceChar_pow_mul π (t := t + 1) (by omega) (-x) y
    rw [show t + 1 - 1 = t by omega] at h
    rw [← h]
    congr 2
    ring
  unfold rowGauss
  simp only [pow_one, hphase]
  rw [sum_comp_eq_card_mul (layerReduction π hn) (layerReduction_surjective π hn)
    (fun e => χ e * principalTraceChar π (NeZero.ne _) (Ideal.Quotient.mk _ (-x) * e)),
    card_ker_layerReduction, show t + 1 - 1 = t by omega, mul_assoc]
  congr 1
  -- Gauss sum at the unit multiplier `−x`
  have hu : IsUnit (Ideal.Quotient.mk (Ideal.span {π}) (-x)) := by
    rw [map_neg]
    exact (isUnit_iff_ne_zero.mpr hm).neg
  have hg := gaussSum_mulShift χ (principalTraceChar π (NeZero.ne _)) hu.unit
  rw [IsUnit.unit_spec] at hg
  rw [← hg, layerReduction_mk, ← map_neg, mul_comm]
  rfl

end GaloisForLFunctions.FamilyContinuationTheory
