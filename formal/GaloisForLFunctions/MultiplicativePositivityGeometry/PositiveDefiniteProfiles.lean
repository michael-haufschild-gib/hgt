import GaloisForLFunctions.MultiplicativePositivityGeometry.PositiveDefiniteFunctions
import GaloisForLFunctions.HTGeometry.CosinePolynomialPurchaseCap

/-!
# Positive-definite profiles have nonnegative cosine polynomials

A profile is an even function `d : ℤ → ℝ` supported in `[−K, K]`: the restriction of a boundary
divisor to a progression `t₀ℤ`. Its cosine polynomial is
`P_d(θ) = d 0 + 2 Σ_{m=1}^{K} d m cos(mθ)`, written with the corpus coefficients `profileCoeff`.

* `cosinePolynomial_profileCoeff_nonneg`: a positive-definite profile has `P_d ≥ 0`.

The proof uses the Fejér limit. The Gram forms with coefficients `cos(jθ)` and `sin(jθ)` at the
points `0, …, N−1` add up to `Σ_{i,j<N} d(i−j) cos((i−j)θ)`. The progression identity rewrites this
as `N P_d(θ) − C(θ)` with `C` independent of `N`. So `P_d(θ) ≥ C(θ)/N` for every `N`, and
`P_d(θ) ≥ 0`. The converse (every nonnegative cosine polynomial is a positive-definite profile) is
realized arithmetically by twisted von Mangoldt weights in `ProfileCharacterization`.
-/

open Finset

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-- Cosine-polynomial coefficients of a profile: `d 0` at `0`, `2 d m` at `m ≥ 1`. -/
noncomputable def profileCoeff (d : ℤ → ℝ) (m : ℕ) : ℝ := if m = 0 then d 0 else 2 * d m

theorem cosinePolynomial_profileCoeff (d : ℤ → ℝ) (K : ℕ) (θ : ℝ) :
    HTGeometry.cosinePolynomial (profileCoeff d) K θ =
      d 0 + 2 * ∑ r ∈ range K, d ((r : ℤ) + 1) * Real.cos ((r + 1 : ℝ) * θ) := by
  unfold HTGeometry.cosinePolynomial
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp only [profileCoeff, Nat.add_one_ne_zero, if_false, if_true, Nat.cast_zero, zero_mul,
    Real.cos_zero, mul_one]
  rw [add_comm]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  push_cast
  ring

/-- **Positive-definite profiles have nonnegative cosine polynomials.** -/
theorem cosinePolynomial_profileCoeff_nonneg {d : ℤ → ℝ} (hd : IsEvenPosDef d) {K : ℕ}
    (hsupp : ∀ r : ℕ, K ≤ r → d ((r : ℤ) + 1) = 0) (θ : ℝ) :
    0 ≤ HTGeometry.cosinePolynomial (profileCoeff d) K θ := by
  rw [cosinePolynomial_profileCoeff]
  set g : ℤ → ℝ := fun z => d z * Real.cos (z * θ) with hgdef
  have hg : ∀ z, g (-z) = g z := fun z => by
    simp only [hgdef, hd.even, Int.cast_neg, neg_mul, Real.cos_neg]
  -- Fejér Gram inequality at every `N`.
  have hN : ∀ N : ℕ, 0 ≤ N * g 0 + 2 * ∑ r ∈ range N, ((N : ℝ) - (r + 1)) * g ((r : ℤ) + 1) := by
    intro N
    have h1 := hd.posDef N (fun i => ((i : ℕ) : ℤ)) (fun i => Real.cos ((i : ℕ) * θ))
    have h2 := hd.posDef N (fun i => ((i : ℕ) : ℤ)) (fun i => Real.sin ((i : ℕ) * θ))
    have hsum : ∑ i : Fin N, ∑ j : Fin N,
        (Real.cos ((i : ℕ) * θ) * Real.cos ((j : ℕ) * θ) * d (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ)) +
          Real.sin ((i : ℕ) * θ) * Real.sin ((j : ℕ) * θ) * d (((i : ℕ) : ℤ) - ((j : ℕ) : ℤ))) =
        ∑ i ∈ range N, ∑ j ∈ range N, g ((i : ℤ) - j) := by
      rw [Fin.sum_univ_eq_sum_range (fun i => ∑ j : Fin N, (Real.cos (i * θ) *
        Real.cos ((j : ℕ) * θ) * d ((i : ℤ) - ((j : ℕ) : ℤ)) + Real.sin (i * θ) *
        Real.sin ((j : ℕ) * θ) * d ((i : ℤ) - ((j : ℕ) : ℤ))))]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Fin.sum_univ_eq_sum_range (fun j => Real.cos (i * θ) * Real.cos (j * θ) *
        d ((i : ℤ) - j) + Real.sin (i * θ) * Real.sin (j * θ) * d ((i : ℤ) - j))]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [hgdef]
      have : (((i : ℤ) - j : ℤ) : ℝ) * θ = i * θ - j * θ := by push_cast; ring
      rw [this, Real.cos_sub]
      ring
    have h12 := add_nonneg h1 h2
    rw [← Finset.sum_add_distrib] at h12
    simp only [← Finset.sum_add_distrib] at h12
    rw [hsum, sum_range_sum_range_sub g hg] at h12
    exact h12
  set P := d 0 + 2 * ∑ r ∈ range K, d ((r : ℤ) + 1) * Real.cos ((r + 1 : ℝ) * θ)
  set C := 2 * ∑ r ∈ range K, (r + 1 : ℝ) * g ((r : ℤ) + 1)
  -- For `N ≥ K` the Gram inequality reads `N P − C ≥ 0`.
  have hNK : ∀ N : ℕ, K ≤ N → C ≤ N * P := by
    intro N hKN
    have h := hN N
    have htail : ∑ r ∈ range N, ((N : ℝ) - (r + 1)) * g ((r : ℤ) + 1) =
        ∑ r ∈ range K, ((N : ℝ) - (r + 1)) * g ((r : ℤ) + 1) := by
      rw [← Finset.sum_range_add_sum_Ico _ hKN]
      have : ∑ r ∈ Finset.Ico K N, ((N : ℝ) - (r + 1)) * g ((r : ℤ) + 1) = 0 :=
        Finset.sum_eq_zero fun r hr => by
          simp only [hgdef, hsupp r (Finset.mem_Ico.mp hr).1, zero_mul, mul_zero]
      rw [this, add_zero]
    rw [htail] at h
    have hg0 : g 0 = d 0 := by simp [hgdef]
    have hgr : ∀ r : ℕ, g ((r : ℤ) + 1) =
        d ((r : ℤ) + 1) * Real.cos ((r + 1 : ℝ) * θ) := fun r => by simp [hgdef]
    have hexp : (N : ℝ) * P - C =
        N * g 0 + 2 * ∑ r ∈ range K, ((N : ℝ) - (r + 1)) * g ((r : ℤ) + 1) := by
      simp only [P, C, hg0, hgr, Finset.mul_sum, mul_add]
      rw [add_sub_assoc, ← Finset.sum_sub_distrib]
      congr 1
      refine Finset.sum_congr rfl fun r _ => ?_
      ring
    linarith
  by_contra hneg
  push Not at hneg
  obtain ⟨N, hN'⟩ := exists_nat_gt (max (K : ℝ) (-C / -P))
  have hKN : K ≤ N := by exact_mod_cast (le_max_left _ _).trans hN'.le
  have h := hNK N hKN
  have hP : 0 < -P := by linarith
  have : -C / -P < N := (le_max_right _ _).trans_lt hN'
  rw [div_lt_iff₀ hP, mul_neg] at this
  linarith

end GaloisForLFunctions.MultiplicativePositivityGeometry
