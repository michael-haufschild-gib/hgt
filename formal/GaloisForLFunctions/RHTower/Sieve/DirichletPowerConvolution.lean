import GaloisForLFunctions.RHTower.Sieve.DirichletCubeCoefficients
import GaloisForLFunctions.RHTower.Sieve.DirichletLargeValuesCount

/-!
# Arbitrary powers of a Dirichlet polynomial

`F(t) = ∑_{n ≤ N} a_n n^{it}` satisfies `F(t)^k = ∑_{j ≤ N^k} b_j j^{it}` with `b` the `k`-fold
Dirichlet convolution of `a`, because the phases multiply.  Applying a mean-value theorem to the
`k`-th power converts a large-values bound with `V²` into one with `V^{2k}`, at the cost of
replacing the length `N` by `N^k` and the coefficient vector by its `k`-fold convolution.  The
exponent is free, which is what a large-values estimate with a variable power needs.
-/

namespace RHTower.Sieve

open Finset

/-- The `k`-fold product of a tuple, shifted down by one, lands in `Fin (N^k)`. -/
theorem powIdx_lt {N k : ℕ} (p : Fin k → Fin N) :
    (∏ i, ((p i : ℕ) + 1)) - 1 < N ^ k := by
  have hpos : 0 < ∏ i, ((p i : ℕ) + 1) := Finset.prod_pos fun i _ => Nat.succ_pos _
  have hle : (∏ i : Fin k, ((p i : ℕ) + 1)) ≤ ∏ _i : Fin k, N :=
    Finset.prod_le_prod' fun i _ => (p i).isLt
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hle
  omega

/-- The index of a `k`-tuple in `Fin (N^k)`: the product of its entries, shifted down by one. -/
def dirichletPowerConvolutionPowIdx {N k : ℕ} (p : Fin k → Fin N) : Fin (N ^ k) :=
  ⟨(∏ i, ((p i : ℕ) + 1)) - 1, powIdx_lt p⟩

theorem dirichletPowerConvolutionPowIdx_val_add_one {N k : ℕ} (p : Fin k → Fin N) :
    ((dirichletPowerConvolutionPowIdx p : ℕ) + 1) = ∏ i, ((p i : ℕ) + 1) := by
  have hpos : 0 < ∏ i, ((p i : ℕ) + 1) := Finset.prod_pos fun i _ => Nat.succ_pos _
  simp only [dirichletPowerConvolutionPowIdx]
  omega

/-- The fibre of `dirichletPowerConvolutionPowIdx` over an index. -/
noncomputable def powFibre (k N : ℕ) (j : Fin (N ^ k)) : Finset (Fin k → Fin N) :=
  (Finset.univ : Finset (Fin k → Fin N)).filter (fun p => dirichletPowerConvolutionPowIdx p = j)

/-- The `k`-fold Dirichlet convolution of a coefficient vector, indexed by `Fin (N^k)`. -/
noncomputable def dirichletPowerConvolutionConvPow (k N : ℕ) (a : Fin N → ℂ) : Fin (N ^ k) → ℂ := fun j =>
  ∑ p ∈ powFibre k N j, ∏ i, a (p i)

/-- The phase of a tuple is the phase of its product. -/
theorem exp_phase_powIdx {N k : ℕ} (t : ℝ) (p : Fin k → Fin N) :
    (∏ i, Complex.exp (((t * Real.log ((p i : ℕ) + 1) : ℝ) : ℂ) * Complex.I))
      = Complex.exp (((t * Real.log ((dirichletPowerConvolutionPowIdx p : ℕ) + 1) : ℝ) : ℂ) * Complex.I) := by
  have hne : ∀ i ∈ (Finset.univ : Finset (Fin k)), (((p i : ℕ) + 1 : ℕ) : ℝ) ≠ 0 := by
    intro i _
    positivity
  have hcast : (((dirichletPowerConvolutionPowIdx p : ℕ) + 1 : ℕ) : ℝ) = ∏ i, (((p i : ℕ) + 1 : ℕ) : ℝ) := by
    rw [dirichletPowerConvolutionPowIdx_val_add_one]
    push_cast
    ring
  have hlog : Real.log ((dirichletPowerConvolutionPowIdx p : ℕ) + 1)
      = ∑ i, Real.log ((p i : ℕ) + 1) := by
    have h := Real.log_prod (s := (Finset.univ : Finset (Fin k)))
      (f := fun i => (((p i : ℕ) + 1 : ℕ) : ℝ)) hne
    rw [← hcast] at h
    push_cast at h ⊢
    exact h
  rw [← Complex.exp_sum]
  congr 1
  rw [hlog]
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]

/-- **The `k`-th power of a Dirichlet polynomial is a Dirichlet polynomial.** -/
theorem dirichletPowerConvolutionDirPoly_convPow (k N : ℕ) (a : Fin N → ℂ) (t : ℝ) :
    dirPoly (N ^ k) (dirichletPowerConvolutionConvPow k N a) t = (dirPoly N a t) ^ k := by
  classical
  set E : Fin N → ℂ := fun n =>
    Complex.exp (((t * Real.log ((n : ℕ) + 1) : ℝ) : ℂ) * Complex.I) with hE
  have hpoly : dirPoly N a t = ∑ n : Fin N, a n * E n := rfl
  have hconst : (∑ n : Fin N, a n * E n) ^ k
      = ∏ _i : Fin k, (∑ n : Fin N, a n * E n) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hexpand : (dirPoly N a t) ^ k
      = ∑ p : Fin k → Fin N, ∏ i, (a (p i) * E (p i)) := by
    rw [hpoly, hconst,
      Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset (Fin N)))
        (fun _ n => a n * E n), Fintype.piFinset_univ]
  have hsplit : ∀ p : Fin k → Fin N,
      (∏ i, (a (p i) * E (p i)))
        = (∏ i, a (p i))
          * Complex.exp (((t * Real.log ((dirichletPowerConvolutionPowIdx p : ℕ) + 1) : ℝ) : ℂ) * Complex.I) := by
    intro p
    rw [Finset.prod_mul_distrib, hE, exp_phase_powIdx t p]
  rw [hexpand]
  simp only [hsplit]
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin k → Fin N)))
    (t := (Finset.univ : Finset (Fin (N ^ k)))) (g := fun p => dirichletPowerConvolutionPowIdx p)
    (f := fun p : Fin k → Fin N => (∏ i, a (p i))
      * Complex.exp (((t * Real.log ((dirichletPowerConvolutionPowIdx p : ℕ) + 1) : ℝ) : ℂ) * Complex.I))
    (fun p _ => Finset.mem_univ _)
  rw [← hfib]
  have hpoly2 : dirPoly (N ^ k) (dirichletPowerConvolutionConvPow k N a) t
      = ∑ j : Fin (N ^ k), dirichletPowerConvolutionConvPow k N a j
          * Complex.exp (((t * Real.log ((j : ℕ) + 1) : ℝ) : ℂ) * Complex.I) := rfl
  rw [hpoly2]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [dirichletPowerConvolutionConvPow, powFibre, Finset.sum_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.mem_filter] at hp
  rw [hp.2]

/-- **The `ℓ²` norm of the `k`-fold convolution.** -/
theorem sum_normSq_convPow_le (k N : ℕ) (a : Fin N → ℂ) {D : ℝ}
    (hD : ∀ j : Fin (N ^ k), ((powFibre k N j).card : ℝ) ≤ D) :
    ∑ j : Fin (N ^ k), ‖dirichletPowerConvolutionConvPow k N a j‖ ^ 2
      ≤ D * (∑ n : Fin N, ‖a n‖ ^ 2) ^ k := by
  classical
  set g : (Fin k → Fin N) → ℝ := fun p => ‖∏ i, a (p i)‖ with hg
  have hfibre : ∀ j : Fin (N ^ k),
      ‖dirichletPowerConvolutionConvPow k N a j‖ ^ 2 ≤ D * ∑ p ∈ powFibre k N j, g p ^ 2 := by
    intro j
    have hnorm : ‖dirichletPowerConvolutionConvPow k N a j‖ ≤ ∑ p ∈ powFibre k N j, g p := by
      rw [dirichletPowerConvolutionConvPow]
      exact norm_sum_le _ _
    have hsq : ‖dirichletPowerConvolutionConvPow k N a j‖ ^ 2 ≤ (∑ p ∈ powFibre k N j, g p) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    have hcs : (∑ p ∈ powFibre k N j, g p) ^ 2
        ≤ ((powFibre k N j).card : ℝ) * ∑ p ∈ powFibre k N j, g p ^ 2 :=
      sq_sum_le_card_mul_sum_sq
    have hsum0 : (0 : ℝ) ≤ ∑ p ∈ powFibre k N j, g p ^ 2 :=
      Finset.sum_nonneg fun p _ => sq_nonneg _
    have hmul : ((powFibre k N j).card : ℝ) * ∑ p ∈ powFibre k N j, g p ^ 2
        ≤ D * ∑ p ∈ powFibre k N j, g p ^ 2 :=
      mul_le_mul_of_nonneg_right (hD j) hsum0
    linarith
  have hsum : ∑ j : Fin (N ^ k), ‖dirichletPowerConvolutionConvPow k N a j‖ ^ 2
      ≤ ∑ j : Fin (N ^ k), D * ∑ p ∈ powFibre k N j, g p ^ 2 :=
    Finset.sum_le_sum fun j _ => hfibre j
  have hfib := Finset.sum_fiberwise_of_maps_to
    (s := (Finset.univ : Finset (Fin k → Fin N)))
    (t := (Finset.univ : Finset (Fin (N ^ k)))) (g := fun p => dirichletPowerConvolutionPowIdx p)
    (f := fun p : Fin k → Fin N => g p ^ 2)
    (fun p _ => Finset.mem_univ _)
  have hcollect : ∑ j : Fin (N ^ k), D * ∑ p ∈ powFibre k N j, g p ^ 2
      = D * ∑ p : Fin k → Fin N, g p ^ 2 := by
    simp only [powFibre]
    rw [← Finset.mul_sum, ← hfib]
  have hprod : ∑ p : Fin k → Fin N, g p ^ 2 = (∑ n : Fin N, ‖a n‖ ^ 2) ^ k := by
    have hterm : ∀ p : Fin k → Fin N, g p ^ 2 = ∏ i, ‖a (p i)‖ ^ 2 := by
      intro p
      rw [hg]
      simp only [norm_prod]
      rw [← Finset.prod_pow]
    have hconst : (∑ n : Fin N, ‖a n‖ ^ 2) ^ k
        = ∏ _i : Fin k, (∑ n : Fin N, ‖a n‖ ^ 2) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    simp only [hterm]
    rw [hconst,
      Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset (Fin N)))
        (fun _ n => ‖a n‖ ^ 2), Fintype.piFinset_univ]
  rw [hcollect, hprod] at hsum
  exact hsum

/-- **The `2k`-th moment at separated frequencies.** -/
theorem powMoment_dirPoly (k N : ℕ) (hk : 1 ≤ k) (hN : 2 ≤ N) (a : Fin N → ℂ)
    {lam : ℕ → ℝ} {δ T D : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T)
    (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (hlow : δ / 2 ≤ lam 0) (R : ℕ)
    (hhigh : lam R + δ / 2 ≤ T)
    (hD : ∀ j : Fin (N ^ k), ((powFibre k N j).card : ℝ) ≤ D) :
    ∑ r ∈ Finset.range (R + 1), ‖dirPoly N a (lam r)‖ ^ (2 * k)
      ≤ (T + 4 * ((N ^ k : ℕ) : ℝ) * (1 + Real.log ((N ^ k : ℕ) : ℝ)))
          * (1 / δ + 2 * Real.log ((N ^ k : ℕ) : ℝ))
          * (D * (∑ n : Fin N, ‖a n‖ ^ 2) ^ k) := by
  classical
  have hNk : 2 ≤ N ^ k := le_trans hN (Nat.le_self_pow (by omega) N)
  have hmv := largeValues_dirPoly (N ^ k) hNk (dirichletPowerConvolutionConvPow k N a) hδ hT hgap hlow R hhigh
  have hrewrite : ∀ r : ℕ,
      ‖dirPoly (N ^ k) (dirichletPowerConvolutionConvPow k N a) (lam r)‖ ^ 2 = ‖dirPoly N a (lam r)‖ ^ (2 * k) := by
    intro r
    rw [dirichletPowerConvolutionDirPoly_convPow, norm_pow, ← pow_mul, mul_comm k 2]
  simp only [hrewrite] at hmv
  refine le_trans hmv ?_
  have hlogNk : (0 : ℝ) ≤ Real.log ((N ^ k : ℕ) : ℝ) := by
    refine Real.log_nonneg ?_
    have : (1 : ℕ) ≤ N ^ k := by omega
    exact_mod_cast this
  have hfactor : (0 : ℝ)
      ≤ (T + 4 * ((N ^ k : ℕ) : ℝ) * (1 + Real.log ((N ^ k : ℕ) : ℝ)))
          * (1 / δ + 2 * Real.log ((N ^ k : ℕ) : ℝ)) := by
    have hcast : (0 : ℝ) ≤ ((N ^ k : ℕ) : ℝ) := Nat.cast_nonneg _
    have h1 : (0 : ℝ) ≤ T + 4 * ((N ^ k : ℕ) : ℝ) * (1 + Real.log ((N ^ k : ℕ) : ℝ)) := by
      nlinarith
    have h2 : (0 : ℝ) ≤ 1 / δ + 2 * Real.log ((N ^ k : ℕ) : ℝ) := by
      have : (0 : ℝ) < 1 / δ := by positivity
      linarith
    exact mul_nonneg h1 h2
  exact mul_le_mul_of_nonneg_left (sum_normSq_convPow_le k N a hD) hfactor

/-- **A cap on the number of large values, `2k`-th power form.** -/
theorem card_largeValues_pow_le (k N : ℕ) (hk : 1 ≤ k) (hN : 2 ≤ N) (a : Fin N → ℂ)
    {lam : ℕ → ℝ} {δ T V D : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T) (hV : 0 < V)
    (hgap : ∀ i, lam i + δ ≤ lam (i + 1)) (hlow : δ / 2 ≤ lam 0) (R : ℕ)
    (hhigh : lam R + δ / 2 ≤ T)
    (hD : ∀ j : Fin (N ^ k), ((powFibre k N j).card : ℝ) ≤ D)
    (hbig : ∀ r ∈ Finset.range (R + 1), V ≤ ‖dirPoly N a (lam r)‖) :
    ((R : ℝ) + 1) * V ^ (2 * k)
      ≤ (T + 4 * ((N ^ k : ℕ) : ℝ) * (1 + Real.log ((N ^ k : ℕ) : ℝ)))
          * (1 / δ + 2 * Real.log ((N ^ k : ℕ) : ℝ))
          * (D * (∑ n : Fin N, ‖a n‖ ^ 2) ^ k) := by
  classical
  have hlower : ((R : ℝ) + 1) * V ^ (2 * k)
      ≤ ∑ r ∈ Finset.range (R + 1), ‖dirPoly N a (lam r)‖ ^ (2 * k) := by
    calc ((R : ℝ) + 1) * V ^ (2 * k) = ∑ _r ∈ Finset.range (R + 1), V ^ (2 * k) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
          push_cast
          ring
      _ ≤ _ := Finset.sum_le_sum fun r hr =>
          pow_le_pow_left₀ hV.le (hbig r hr) (2 * k)
  exact le_trans hlower (powMoment_dirPoly k N hk hN a hδ hT hgap hlow R hhigh hD)

end RHTower.Sieve
