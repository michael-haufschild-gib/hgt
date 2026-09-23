import GaloisForLFunctions.RHTower.DeningerPoissonOperator
import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Möbius inversion of the Poisson sum

The double family `μ(n)f(nmx)` is absolutely summable for a Schwartz function vanishing at the
origin, so it may be summed in two ways.  Summing first over `m` gives the Möbius-weighted sum of
the Poisson sums; summing along the fibres of `(n,m) ↦ nm` gives `∑ₖ(∑_{d∣k}μ(d))f(kx)`, and the
inner sum is the unit of Dirichlet convolution.  Hence

`∑_{n≥1} μ(n)(Zf)(nx) = f(x)`.

So the Möbius-weighted Poisson sum is a left inverse of the Poisson operator on the multiplicative
half line, and the Poisson operator is injective on Meyer's space — an even function vanishing at
the origin is determined by its values there.

* `deningerMoebiusPair` : the double family.
* `summable_deningerMoebiusPair` : it is absolutely summable.
* `deningerMoebius_poissonValue` : **`∑_{n≥1}μ(n)(Zf)(nx) = f(x)`.**
* `deningerPoissonValue_injOn` : **the Poisson sum determines the function.**
-/

open scoped Real SchwartzMap FourierTransform ArithmeticFunction
open Complex MeasureTheory GaloisForLFunctions GaloisForLFunctions.RHTower

noncomputable section

namespace RHTower

/-- The Möbius-weighted multiplicative sum `∑_{n≥1} μ(n)g(nx)`. -/
def deningerMoebiusValue (g : ℝ → ℂ) (x : ℝ) : ℂ :=
  ∑' n : ℕ, ((ArithmeticFunction.moebius n : ℤ) : ℂ) * g ((n : ℝ) * x)

/-- The double family whose two summation orders give the Möbius inversion. -/
def deningerMoebiusPair (f : 𝓢(ℝ, ℂ)) (x : ℝ) (p : ℕ × ℕ) : ℂ :=
  ((ArithmeticFunction.moebius p.1 : ℤ) : ℂ) * f ((p.1 : ℝ) * (p.2 : ℝ) * x)

/-! ## Summability -/

theorem norm_moebius_le_one (n : ℕ) : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖ ≤ 1 := by
  have h : |ArithmeticFunction.moebius n| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
  have hcast : ‖((ArithmeticFunction.moebius n : ℤ) : ℂ)‖
      = |(ArithmeticFunction.moebius n : ℝ)| := by
    rw [show ((ArithmeticFunction.moebius n : ℤ) : ℂ)
        = (((ArithmeticFunction.moebius n : ℤ) : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs]
  rw [hcast]
  exact_mod_cast h

theorem norm_deningerMoebiusPair_le (f : 𝓢(ℝ, ℂ)) (h0 : f 0 = 0) {x : ℝ} (hx : 0 < x)
    (p : ℕ × ℕ) :
    ‖deningerMoebiusPair f x p‖
      ≤ (SchwartzMap.seminorm ℂ 2 0 f / x ^ (2 : ℕ))
        * ((1 / ((p.1 : ℝ) ^ (2 : ℕ))) * (1 / ((p.2 : ℝ) ^ (2 : ℕ)))) := by
  set S : ℝ := SchwartzMap.seminorm ℂ 2 0 f with hS
  have hSnn : 0 ≤ S := apply_nonneg _ _
  rcases Nat.eq_zero_or_pos p.1 with h1 | h1
  · have hμ : ((ArithmeticFunction.moebius p.1 : ℤ) : ℂ) = 0 := by
      rw [h1]
      simp
    rw [deningerMoebiusPair, hμ, zero_mul, norm_zero, h1]
    simp
  rcases Nat.eq_zero_or_pos p.2 with h2 | h2
  · have hzero : ((p.1 : ℝ) * (p.2 : ℝ) * x) = 0 := by
      rw [h2]
      simp
    rw [deningerMoebiusPair, hzero, h0, mul_zero, norm_zero, h2]
    simp
  have hp1 : (0 : ℝ) < (p.1 : ℝ) := by exact_mod_cast h1
  have hp2 : (0 : ℝ) < (p.2 : ℝ) := by exact_mod_cast h2
  have harg : (0 : ℝ) < (p.1 : ℝ) * (p.2 : ℝ) * x := by positivity
  have hsem := SchwartzMap.norm_pow_mul_le_seminorm ℂ f 2 ((p.1 : ℝ) * (p.2 : ℝ) * x)
  have hnorm : ‖(p.1 : ℝ) * (p.2 : ℝ) * x‖ = (p.1 : ℝ) * (p.2 : ℝ) * x := by
    rw [Real.norm_eq_abs, abs_of_pos harg]
  rw [hnorm] at hsem
  calc ‖deningerMoebiusPair f x p‖
      = ‖((ArithmeticFunction.moebius p.1 : ℤ) : ℂ)‖ * ‖f ((p.1 : ℝ) * (p.2 : ℝ) * x)‖ := by
        rw [deningerMoebiusPair, norm_mul]
    _ ≤ 1 * ‖f ((p.1 : ℝ) * (p.2 : ℝ) * x)‖ :=
        mul_le_mul_of_nonneg_right (norm_moebius_le_one p.1) (norm_nonneg _)
    _ = ‖f ((p.1 : ℝ) * (p.2 : ℝ) * x)‖ := one_mul _
    _ ≤ S / ((p.1 : ℝ) * (p.2 : ℝ) * x) ^ (2 : ℕ) := by
        rw [le_div_iff₀ (by positivity)]
        calc ‖f ((p.1 : ℝ) * (p.2 : ℝ) * x)‖ * ((p.1 : ℝ) * (p.2 : ℝ) * x) ^ (2 : ℕ)
            = ((p.1 : ℝ) * (p.2 : ℝ) * x) ^ (2 : ℕ) * ‖f ((p.1 : ℝ) * (p.2 : ℝ) * x)‖ := by ring
          _ ≤ S := hsem
    _ = (S / x ^ (2 : ℕ)) * ((1 / ((p.1 : ℝ) ^ (2 : ℕ))) * (1 / ((p.2 : ℝ) ^ (2 : ℕ)))) := by
        field_simp

theorem summable_deningerMoebiusPair (f : 𝓢(ℝ, ℂ)) (h0 : f 0 = 0) {x : ℝ} (hx : 0 < x) :
    Summable (deningerMoebiusPair f x) := by
  have hbase : Summable fun n : ℕ => 1 / ((n : ℝ) ^ (2 : ℕ)) :=
    Real.summable_one_div_nat_pow.mpr one_lt_two
  have hprod : Summable fun p : ℕ × ℕ => (1 / ((p.1 : ℝ) ^ (2 : ℕ))) * (1 / ((p.2 : ℝ) ^ (2 : ℕ))) :=
    hbase.mul_of_nonneg hbase (fun n => by positivity) (fun n => by positivity)
  refine Summable.of_norm_bounded
    (g := fun p : ℕ × ℕ => (SchwartzMap.seminorm ℂ 2 0 f / x ^ (2 : ℕ))
      * ((1 / ((p.1 : ℝ) ^ (2 : ℕ))) * (1 / ((p.2 : ℝ) ^ (2 : ℕ)))))
    (hprod.mul_left _) fun p => norm_deningerMoebiusPair_le f h0 hx p

/-! ## Summing first over the second index -/

theorem tsum_deningerMoebiusPair_snd (f : 𝓢(ℝ, ℂ)) (h0 : f 0 = 0) {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (∑' m : ℕ, f ((n : ℝ) * (m : ℝ) * x)) = deningerPoissonValue f ((n : ℝ) * x) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hzero : ∀ m : ℕ, f ((n : ℝ) * (m : ℝ) * x) = 0 := by
      intro m
      have hval : ((n : ℝ) * (m : ℝ) * x) = 0 := by
        rw [hn]
        simp
      rw [hval, h0]
    have hzero' : ∀ m : ℕ, f (((n : ℝ) * x) * ((m : ℝ) + 1)) = 0 := by
      intro m
      have hval : (((n : ℝ) * x) * ((m : ℝ) + 1)) = 0 := by
        rw [hn]
        simp
      rw [hval, h0]
    rw [deningerPoissonValue, tsum_congr hzero, tsum_congr hzero']
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hnne : ((n : ℝ) * x) ≠ 0 := by positivity
  have hshift : Summable fun m : ℕ => f ((n : ℝ) * ((m : ℝ) + 1) * x) := by
    have h := summable_deningerPoissonTerm f hnne
    refine h.congr fun m => ?_
    congr 1
    ring
  have hsum : Summable fun m : ℕ => f ((n : ℝ) * (m : ℝ) * x) := by
    refine (summable_nat_add_iff 1).mp ?_
    refine hshift.congr fun m => ?_
    congr 1
    push_cast
    ring
  rw [hsum.tsum_eq_zero_add]
  have hfirst : f ((n : ℝ) * ((0 : ℕ) : ℝ) * x) = 0 := by
    have hval : ((n : ℝ) * ((0 : ℕ) : ℝ) * x) = 0 := by simp
    rw [hval, h0]
  rw [hfirst, zero_add, deningerPoissonValue]
  refine tsum_congr fun m => ?_
  congr 1
  push_cast
  ring

theorem tsum_deningerMoebiusPair_eq (f : 𝓢(ℝ, ℂ)) (h0 : f 0 = 0) {x : ℝ} (hx : 0 < x) :
    (∑' p : ℕ × ℕ, deningerMoebiusPair f x p)
      = deningerMoebiusValue (deningerPoissonValue f) x := by
  rw [(summable_deningerMoebiusPair f h0 hx).tsum_prod, deningerMoebiusValue]
  refine tsum_congr fun n => ?_
  have hfun : (fun m : ℕ => deningerMoebiusPair f x (n, m))
      = fun m : ℕ => ((ArithmeticFunction.moebius n : ℤ) : ℂ) * f ((n : ℝ) * (m : ℝ) * x) := rfl
  rw [hfun, tsum_mul_left, tsum_deningerMoebiusPair_snd f h0 hx n]

/-! ## Summing along the fibres -/

theorem sum_moebius_divisorsAntidiagonal (k : ℕ) :
    (∑ p ∈ k.divisorsAntidiagonal, ArithmeticFunction.moebius p.1)
      = if k = 1 then (1 : ℤ) else 0 := by
  classical
  by_cases hk : k = 0
  · subst hk
    simp
  have happly := ArithmeticFunction.mul_apply (R := ℤ) (f := ArithmeticFunction.moebius)
    (g := (↑ArithmeticFunction.zeta : ArithmeticFunction ℤ)) (n := k)
  have hzero : ∀ p ∈ k.divisorsAntidiagonal,
      ArithmeticFunction.moebius p.1 * ((↑ArithmeticFunction.zeta : ArithmeticFunction ℤ) p.2)
        = ArithmeticFunction.moebius p.1 := by
    intro p hp
    have hmem := Nat.mem_divisorsAntidiagonal.mp hp
    have hp2 : p.2 ≠ 0 := by
      rintro h
      rw [h, mul_zero] at hmem
      exact hmem.2 hmem.1.symm
    rw [ArithmeticFunction.natCoe_apply, ArithmeticFunction.zeta_apply, if_neg hp2]
    simp
  rw [Finset.sum_congr rfl hzero] at happly
  rw [← happly, ArithmeticFunction.moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

theorem tsum_fiber_deningerMoebiusPair (f : 𝓢(ℝ, ℂ)) (h0 : f 0 = 0) {x : ℝ} (_hx : 0 < x)
    (k : ℕ) :
    (∑' p : (fun q : ℕ × ℕ => q.1 * q.2) ⁻¹' {k}, deningerMoebiusPair f x p)
      = (if k = 1 then (1 : ℂ) else 0) * f ((k : ℝ) * x) := by
  classical
  by_cases hk : k = 0
  · subst hk
    have hzero : ∀ p : (fun q : ℕ × ℕ => q.1 * q.2) ⁻¹' {0},
        deningerMoebiusPair f x (p : ℕ × ℕ) = 0 := by
      rintro ⟨⟨a, b⟩, hp⟩
      have hab : a * b = 0 := hp
      rcases Nat.mul_eq_zero.mp hab with ha | hb
      · have hμ : ((ArithmeticFunction.moebius a : ℤ) : ℂ) = 0 := by
          rw [ha]
          simp
        show ((ArithmeticFunction.moebius a : ℤ) : ℂ) * f ((a : ℝ) * (b : ℝ) * x) = 0
        rw [hμ, zero_mul]
      · have hzero : ((a : ℝ) * (b : ℝ) * x) = 0 := by
          rw [hb]
          simp
        show ((ArithmeticFunction.moebius a : ℤ) : ℂ) * f ((a : ℝ) * (b : ℝ) * x) = 0
        rw [hzero, h0, mul_zero]
    rw [tsum_congr hzero, tsum_zero, if_neg (by norm_num), zero_mul]
  rw [show (fun q : ℕ × ℕ => q.1 * q.2) ⁻¹' {k} = ↑k.divisorsAntidiagonal by
      ext p
      simp [Nat.mem_divisorsAntidiagonal, hk],
    Finset.tsum_subtype' k.divisorsAntidiagonal (deningerMoebiusPair f x)]
  have hterm : ∀ p ∈ k.divisorsAntidiagonal,
      deningerMoebiusPair f x p
        = ((ArithmeticFunction.moebius p.1 : ℤ) : ℂ) * f ((k : ℝ) * x) := by
    intro p hp
    have hmul : p.1 * p.2 = k := (Nat.mem_divisorsAntidiagonal.mp hp).1
    have harg : ((p.1 : ℝ) * (p.2 : ℝ) * x) = (k : ℝ) * x := by
      rw [← Nat.cast_mul, hmul]
    rw [deningerMoebiusPair, harg]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  congr 1
  calc (∑ p ∈ k.divisorsAntidiagonal, ((ArithmeticFunction.moebius p.1 : ℤ) : ℂ))
      = (((∑ p ∈ k.divisorsAntidiagonal, ArithmeticFunction.moebius p.1 : ℤ)) : ℂ) := by
        push_cast
        ring
    _ = (((if k = 1 then (1 : ℤ) else 0) : ℤ) : ℂ) := by
        rw [sum_moebius_divisorsAntidiagonal]
    _ = (if k = 1 then (1 : ℂ) else 0) := by
        by_cases hk1 : k = 1
        · rw [if_pos hk1, if_pos hk1]
          norm_num
        · rw [if_neg hk1, if_neg hk1]
          norm_num

/-! ## The inversion -/

/-- **Möbius inversion of the Poisson sum.** -/
theorem deningerMoebius_poissonValue (f : 𝓢(ℝ, ℂ)) (h0 : f 0 = 0) {x : ℝ} (hx : 0 < x) :
    deningerMoebiusValue (deningerPoissonValue f) x = f x := by
  classical
  have hsum := summable_deningerMoebiusPair f h0 hx
  have hfib := hsum.hasSum.tsum_fiberwise (fun q : ℕ × ℕ => q.1 * q.2)
  have hfun : (fun k : ℕ =>
      ∑' p : (fun q : ℕ × ℕ => q.1 * q.2) ⁻¹' {k}, deningerMoebiusPair f x p)
      = fun k : ℕ => (if k = 1 then (1 : ℂ) else 0) * f ((k : ℝ) * x) := by
    funext k
    exact tsum_fiber_deningerMoebiusPair f h0 hx k
  rw [hfun] at hfib
  have hone : HasSum (fun k : ℕ => (if k = 1 then (1 : ℂ) else 0) * f ((k : ℝ) * x))
      (f ((1 : ℝ) * x)) := by
    have h := hasSum_ite_eq (1 : ℕ) (f (((1 : ℕ) : ℝ) * x))
    have hfun : (fun k : ℕ => if k = 1 then f (((1 : ℕ) : ℝ) * x) else 0)
        = fun k : ℕ => (if k = 1 then (1 : ℂ) else 0) * f ((k : ℝ) * x) := by
      funext k
      by_cases hk : k = 1
      · rw [if_pos hk, if_pos hk, one_mul, hk]
      · rw [if_neg hk, if_neg hk, zero_mul]
    rw [hfun] at h
    have hcast : f (((1 : ℕ) : ℝ) * x) = f ((1 : ℝ) * x) := by norm_num
    rwa [hcast] at h
  have hval : (∑' p : ℕ × ℕ, deningerMoebiusPair f x p) = f ((1 : ℝ) * x) := hfib.unique hone
  rw [← tsum_deningerMoebiusPair_eq f h0 hx, hval, one_mul]

/-- **The Poisson sum determines the function on the positive half line.** -/
theorem deningerPoissonValue_injOn {f g : 𝓢(ℝ, ℂ)} (hf : f 0 = 0) (hg : g 0 = 0)
    (h : ∀ x : ℝ, 0 < x → deningerPoissonValue f x = deningerPoissonValue g x) :
    ∀ x : ℝ, 0 < x → f x = g x := by
  intro x hx
  have hfval := deningerMoebius_poissonValue f hf hx
  have hgval := deningerMoebius_poissonValue g hg hx
  rw [← hfval, ← hgval, deningerMoebiusValue, deningerMoebiusValue]
  refine tsum_congr fun n => ?_
  rcases Nat.eq_zero_or_pos n with hn | hn
  · have hμ : ((ArithmeticFunction.moebius n : ℤ) : ℂ) = 0 := by
      rw [hn]
      simp
    rw [hμ, zero_mul, zero_mul]
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  rw [h ((n : ℝ) * x) (by positivity)]

end RHTower

end
