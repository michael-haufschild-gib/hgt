import GaloisForLFunctions.HTGeometry.OrderOneEnvelope
import GaloisForLFunctions.HTGeometry.FactorialFockInfiniteRadius

/-!
# Entire functions of order one lie in the factorial Fock space at every center

A function with an order-one growth envelope `‖f s‖ ≤ exp(C (1+‖s‖) log(2+‖s‖))` satisfies, for
each center `a` and each `ε > 0`, a Gaussian bound `‖f z‖ ≤ K exp(ε ‖z - a‖²)`. For an entire such
`f`, Cauchy estimates on the circle of radius `√(n / 2ε)` with `ε = 1/(8e)` bound the Taylor jet,
so the factorial Fock energy `∑ₙ ‖f⁽ⁿ⁾(a)‖² / n!` is finite, being dominated by a geometric
series of ratio `1/4`.

## Main results

- `OrderOneEnvelope.gaussian_bound_at`: for every center `a` and `ε > 0` there is `K > 0` with
  `‖f z‖ ≤ K exp(ε ‖z - a‖²)` for all `z`.
- `OrderOneEnvelope.summable_rawJetFactorialFockEnergy`: for entire `f` with an order-one
  envelope, `n ↦ ‖f⁽ⁿ⁾(a)‖² / n!` is summable at every `a ∈ ℂ`.

## Hypotheses

Both results assume `OrderOneEnvelope f`, a Prop-valued global growth bound of order one; the
summability result also assumes that `f` is complex differentiable on all of `ℂ`. Under these
hypotheses the results are unconditional.
-/

open Complex Filter Topology Metric

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Assuming the order-one envelope `hf`, for every center `a` and every `ε > 0` there is `K > 0`
with `‖f z‖ ≤ K exp(ε ‖z - a‖²)` for all `z ∈ ℂ`. -/
theorem OrderOneEnvelope.gaussian_bound_at
    {f : ℂ → ℂ} (hf : OrderOneEnvelope f) (a : ℂ) {eps : ℝ} (heps : 0 < eps) :
    ∃ K : ℝ, 0 < K ∧ ∀ z : ℂ, ‖f z‖ ≤ K * Real.exp (eps * ‖z - a‖ ^ 2) := by
  obtain ⟨C, hC, hbound⟩ := hf.subquadratic
  by_cases hC0 : C = 0
  · refine ⟨1, by norm_num, ?_⟩
    intro z
    have hfz : ‖f z‖ ≤ 1 := by
      simpa [hC0] using hbound z
    calc
      ‖f z‖ ≤ 1 := hfz
      _ ≤ 1 * Real.exp (eps * ‖z - a‖ ^ 2) := by
        simp only [one_mul]
        exact Real.one_le_exp (mul_nonneg (le_of_lt heps) (sq_nonneg _))
  · have hCpos : 0 < C := lt_of_le_of_ne hC (Ne.symm hC0)
    let A : ℝ := 1 + ‖a‖
    let delta : ℝ := eps / (4 * C)
    let B : ℝ := C / (4 * delta)
    let D : ℝ := eps / 2 * A ^ 2 + B * A + B ^ 2 / (2 * eps)
    have hA : 0 ≤ A := by dsimp [A]; positivity
    have hApos : 0 < A := by dsimp [A]; positivity
    have hdelta : 0 < delta := by dsimp [delta]; positivity
    have hB : 0 ≤ B := by dsimp [B]; positivity
    refine ⟨Real.exp D, Real.exp_pos _, ?_⟩
    intro z
    let q : ℝ := ‖z - a‖
    let x : ℝ := 1 + ‖z‖
    have hq : 0 ≤ q := norm_nonneg _
    have hx : 0 ≤ x := by dsimp [x]; positivity
    have hx_le : x ≤ A + q := by
      dsimp [x, A, q]
      have hz : ‖z‖ ≤ ‖a‖ + ‖z - a‖ := by
        calc
          ‖z‖ = ‖a + (z - a)‖ := by ring_nf
          _ ≤ ‖a‖ + ‖z - a‖ := norm_add_le _ _
      linarith
    have hAq : 0 ≤ A + q := add_nonneg hA hq
    have hAqpos : 0 < A + q := add_pos_of_pos_of_nonneg hApos hq
    have hsqrt_tunable : Real.sqrt (A + q) ≤ delta * (A + q) + 1 / (4 * delta) := by
      have hs2 : (Real.sqrt (A + q)) ^ 2 = A + q := Real.sq_sqrt hAq
      have hsq : 0 ≤ (2 * delta * Real.sqrt (A + q) - 1) ^ 2 := sq_nonneg _
      have h4d : (0 : ℝ) < 4 * delta := mul_pos (by norm_num) hdelta
      have hscaled : (Real.sqrt (A + q) - delta * (A + q)) * (4 * delta) ≤ 1 := by
        calc
          (Real.sqrt (A + q) - delta * (A + q)) * (4 * delta) =
              4 * delta * Real.sqrt (A + q) - 4 * delta ^ 2 * (Real.sqrt (A + q)) ^ 2 := by
                rw [hs2]
                ring
          _ ≤ 1 := by nlinarith
      have hdiv : Real.sqrt (A + q) - delta * (A + q) ≤ 1 / (4 * delta) :=
        (le_div_iff₀ h4d).2 hscaled
      linarith
    have hpow_bound : C * x ^ (3 / 2 : ℝ) ≤ D + eps * q ^ 2 := by
      have hrpow_mono : x ^ (3 / 2 : ℝ) ≤ (A + q) ^ (3 / 2 : ℝ) := by
        exact Real.rpow_le_rpow hx hx_le (by norm_num)
      have h32 : (3 / 2 : ℝ) = 1 + 1 / 2 := by norm_num
      have hrewrite : (A + q) ^ (3 / 2 : ℝ) =
          (A + q) * Real.sqrt (A + q) := by
        rw [h32, Real.rpow_add hAqpos, Real.rpow_one, ← Real.sqrt_eq_rpow]
      have hroot : C * ((A + q) * Real.sqrt (A + q)) ≤
          C * ((A + q) * (delta * (A + q) + 1 / (4 * delta))) := by
        gcongr
      have hCd : C * delta = eps / 4 := by
        dsimp [delta]
        field_simp
      have hCB : C / (4 * delta) = B := by rfl
      have hsquare : (A + q) ^ 2 ≤ 2 * A ^ 2 + 2 * q ^ 2 := by
        nlinarith [sq_nonneg (A - q)]
      have hyoung : B * q ≤ eps / 2 * q ^ 2 + B ^ 2 / (2 * eps) := by
        rw [show eps / 2 * q ^ 2 + B ^ 2 / (2 * eps) =
            (eps ^ 2 * q ^ 2 + B ^ 2) / (2 * eps) by field_simp]
        apply (le_div_iff₀ (mul_pos (by norm_num) heps)).2
        nlinarith [sq_nonneg (eps * q - B)]
      calc
        C * x ^ (3 / 2 : ℝ) ≤ C * (A + q) ^ (3 / 2 : ℝ) := by gcongr
        _ = C * ((A + q) * Real.sqrt (A + q)) := by rw [hrewrite]
        _ ≤ C * ((A + q) * (delta * (A + q) + 1 / (4 * delta))) := hroot
        _ = eps / 4 * (A + q) ^ 2 + B * (A + q) := by
          rw [← hCd, ← hCB]
          ring
        _ ≤ eps / 4 * (2 * A ^ 2 + 2 * q ^ 2) + B * (A + q) := by
          gcongr
        _ ≤ D + eps * q ^ 2 := by
          dsimp [D]
          nlinarith
    calc
      ‖f z‖ ≤ Real.exp (C * x ^ (3 / 2 : ℝ)) := by simpa [x] using hbound z
      _ ≤ Real.exp (D + eps * q ^ 2) := Real.exp_le_exp.mpr hpow_bound
      _ = Real.exp D * Real.exp (eps * ‖z - a‖ ^ 2) := by
        rw [Real.exp_add]

/-- Assuming `f` is entire and has an order-one envelope, the factorial Fock energy of its Taylor
jet at any `a` is finite: `∑ₙ ‖f⁽ⁿ⁾(a)‖² / n!` converges, by Cauchy estimates and a geometric
comparison with ratio `1/4`. -/
theorem OrderOneEnvelope.summable_rawJetFactorialFockEnergy
    {f : ℂ → ℂ} (hf : OrderOneEnvelope f) (hfd : Differentiable ℂ f) (a : ℂ) :
    Summable (fun n : ℕ => ‖iteratedDeriv n f a‖ ^ 2 / n.factorial) := by
  let eps : ℝ := 1 / (8 * Real.exp 1)
  have heps : 0 < eps := by dsimp [eps]; positivity
  obtain ⟨K, hK, hgauss⟩ := hf.gaussian_bound_at a heps
  have hratio : Real.exp 1 * (2 * eps) = 1 / 4 := by
    dsimp [eps]
    field_simp
    ring
  have hgeom : Summable (fun n : ℕ => K ^ 2 * (1 / 4 : ℝ) ^ n) := by
    exact summable_geometric_of_norm_lt_one (by norm_num : ‖(1 / 4 : ℝ)‖ < 1) |>.mul_left _
  apply hgeom.of_nonneg_of_le (fun n => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _))
  intro n
  by_cases hn0 : n = 0
  · subst n
    simp only [iteratedDeriv_zero, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, mul_one]
    have ha := hgauss a
    simp only [sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, Real.exp_zero, mul_one] at ha
    exact (sq_le_sq₀ (norm_nonneg _) (le_of_lt hK)).2 ha
  · have hn : 0 < n := Nat.pos_of_ne_zero hn0
    let R : ℝ := Real.sqrt ((n : ℝ) / (2 * eps))
    have hRarg : 0 ≤ (n : ℝ) / (2 * eps) := by positivity
    have hR : 0 < R := by dsimp [R]; positivity
    have hR2 : R ^ 2 = (n : ℝ) / (2 * eps) := by
      dsimp [R]
      exact Real.sq_sqrt hRarg
    have hsphere : ∀ z : ℂ, z ∈ Metric.sphere a R →
        ‖f z‖ ≤ K * Real.exp ((n : ℝ) / 2) := by
      intro z hz
      have hzdist : ‖z - a‖ = R := by
        simpa [Metric.mem_sphere, dist_eq] using hz
      calc
        ‖f z‖ ≤ K * Real.exp (eps * ‖z - a‖ ^ 2) := hgauss z
        _ = K * Real.exp ((n : ℝ) / 2) := by rw [hzdist, hR2]; congr 2; field_simp
    have hd := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le
      (f := f) (c := a) (n := n) (R := R) (C := K * Real.exp ((n : ℝ) / 2))
      hR hfd.diffContOnCl hsphere
    have hfac : (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
      exact_mod_cast Nat.factorial_le_pow n
    have hRpow : R ^ (2 * n) = ((n : ℝ) / (2 * eps)) ^ n := by
      rw [pow_mul, hR2]
    have hRne : R ^ n ≠ 0 := pow_ne_zero _ (ne_of_gt hR)
    have hncast : (0 : ℝ) < n := by exact_mod_cast hn
    have hfacpos : (0 : ℝ) < n.factorial := by positivity
    have hexp_half : Real.exp ((n : ℝ) / 2) ^ 2 = Real.exp (n : ℝ) := by
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hexp_nat : Real.exp (n : ℝ) = Real.exp 1 ^ n := by
      simpa using Real.exp_nat_mul 1 n
    have htarget : ‖iteratedDeriv n f a‖ ^ 2 / (n.factorial : ℝ) ≤
        K ^ 2 * (Real.exp 1 * (2 * eps)) ^ n := by
      have hdsq : ‖iteratedDeriv n f a‖ ^ 2 ≤
          ((n.factorial : ℝ) * (K * Real.exp ((n : ℝ) / 2)) / R ^ n) ^ 2 := by
        nlinarith [norm_nonneg (iteratedDeriv n f a)]
      calc
        ‖iteratedDeriv n f a‖ ^ 2 / (n.factorial : ℝ) ≤
            (((n.factorial : ℝ) * (K * Real.exp ((n : ℝ) / 2)) / R ^ n) ^ 2) /
              (n.factorial : ℝ) := by gcongr
        _ = (n.factorial : ℝ) * K ^ 2 * Real.exp ((n : ℝ) / 2) ^ 2 /
              (R ^ n) ^ 2 := by
          field_simp
        _ = (n.factorial : ℝ) * K ^ 2 * Real.exp (n : ℝ) / R ^ (2 * n) := by
          rw [hexp_half, ← pow_mul, mul_comm 2 n]
        _ ≤ ((n : ℝ) ^ n) * K ^ 2 * Real.exp (n : ℝ) /
              ((n : ℝ) / (2 * eps)) ^ n := by
          rw [hRpow]
          gcongr
        _ = K ^ 2 * (Real.exp 1 * (2 * eps)) ^ n := by
          rw [hexp_nat, div_pow]
          field_simp
          ring
    simpa [hratio] using htarget

end

end GaloisForLFunctions.HTGeometry
