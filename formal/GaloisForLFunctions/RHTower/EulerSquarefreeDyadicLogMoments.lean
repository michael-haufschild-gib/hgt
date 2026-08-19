import GaloisForLFunctions.RHTower.EulerSquarefreeDyadicLogTransport

/-!
# Logarithmic moments of the dyadic squarefree source

`dyadic-squarefree-euler-fock-source-factorization`, §3–§4 (moment layer).

All logarithmic moments `∑ (log n)^k n^{-σ}` of the Euler source and of its signed squarefree
parity factor converge for `σ > 1`, and the first two split exactly along `n = m² d`:

```text
∑ (log n) n^{-σ}   = A₁(σ)·ζ(2σ)   + 2 A₀(σ)·B₁(2σ),
∑ (log n)² n^{-σ}  = A₂(σ)·ζ(2σ)   + 4 A₁(σ)·B₁(2σ) + 4 A₀(σ)·B₂(2σ).
```

The consequence used by the card is the exact **variance additivity**
`Var_σ(log n) = Var_σ(log d) + 4 Var_{2σ}(log m)`, which is the norm identity `(15)`.
-/

open Complex Set

noncomputable section

namespace RHTower

open GaloisForLFunctions.HTGeometry

/-! ## Convergence of every logarithmic moment -/

theorem summable_pnat_logpow_rpow (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun n : ℕ+ => Real.log (n : ℝ) ^ k * (n : ℝ) ^ (-σ)) := by
  set δ : ℝ := (σ - 1) / (2 * (k + 1)) with hδ
  have hkpos : (0 : ℝ) < 2 * (k + 1) := by positivity
  have hδpos : 0 < δ := by rw [hδ]; positivity
  have hkδ : (k : ℝ) * δ ≤ (σ - 1) / 2 := by
    rw [hδ, ← sub_nonneg]
    have hid : (σ - 1) / 2 - (k : ℝ) * ((σ - 1) / (2 * ((k : ℝ) + 1)))
        = (σ - 1) / (2 * ((k : ℝ) + 1)) := by
      field_simp
      ring
    rw [hid]
    exact div_nonneg (by linarith) (by positivity)
  have hσkδ : 1 < σ - (k : ℝ) * δ := by linarith
  refine Summable.of_nonneg_of_le
    (g := fun n : ℕ+ => Real.log (n : ℝ) ^ k * (n : ℝ) ^ (-σ))
    (f := fun n : ℕ+ => (δ ^ k)⁻¹ * (n : ℝ) ^ (-(σ - (k : ℝ) * δ)))
    (fun n => ?_) (fun n => ?_) ((summable_pnat_rpow hσkδ).mul_left (δ ^ k)⁻¹)
  · have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast n.property)
    positivity
  · have hn : (0 : ℝ) < (n : ℝ) := by positivity
    have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast n.property)
    have hle : Real.log (n : ℝ) ≤ (n : ℝ) ^ δ / δ := Real.log_le_rpow_div (le_of_lt hn) hδpos
    have hpow : Real.log (n : ℝ) ^ k ≤ ((n : ℝ) ^ δ / δ) ^ k :=
      pow_le_pow_left₀ hlog hle k
    have hrw : ((n : ℝ) ^ δ / δ) ^ k = (δ ^ k)⁻¹ * (n : ℝ) ^ ((k : ℝ) * δ) := by
      rw [div_pow, ← Real.rpow_natCast ((n : ℝ) ^ δ) k, ← Real.rpow_mul (le_of_lt hn),
        div_eq_inv_mul, mul_comm δ (k : ℝ)]
    have hstep : Real.log (n : ℝ) ^ k * (n : ℝ) ^ (-σ)
        ≤ ((δ ^ k)⁻¹ * (n : ℝ) ^ ((k : ℝ) * δ)) * (n : ℝ) ^ (-σ) := by
      rw [← hrw]
      exact mul_le_mul_of_nonneg_right hpow (by positivity)
    have hcomb : ((δ ^ k)⁻¹ * (n : ℝ) ^ ((k : ℝ) * δ)) * (n : ℝ) ^ (-σ)
        = (δ ^ k)⁻¹ * (n : ℝ) ^ (-(σ - (k : ℝ) * δ)) := by
      rw [mul_assoc, ← Real.rpow_add hn]
      congr 2
      ring
    linarith [hstep, hcomb.le, hcomb.ge]

theorem summable_squarefree_logpow_rpow (k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun d : SquarefreePNat =>
      Real.log ((d.1 : ℝ)) ^ k * ((d.1 : ℝ)) ^ (-σ)) :=
  (summable_pnat_logpow_rpow k hσ).comp_injective (fun _ _ hab => Subtype.ext hab)

theorem logpow_rpow_nonneg (k : ℕ) {σ : ℝ} (n : ℕ+) :
    0 ≤ Real.log (n : ℝ) ^ k * (n : ℝ) ^ (-σ) := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast n.property)
  positivity

/-! ## The moment masses -/

/-- `A_k(σ) = ∑_{d squarefree} (log d)^k d^{-σ}`. -/
def squarefreeLogPowMass (k : ℕ) (σ : ℝ) : ℝ :=
  ∑' d : SquarefreePNat, Real.log ((d.1 : ℝ)) ^ k * ((d.1 : ℝ)) ^ (-σ)

/-- `B_k(σ) = ∑_{n ≥ 1} (log n)^k n^{-σ}`. -/
def eulerLogPowMass (k : ℕ) (σ : ℝ) : ℝ :=
  ∑' n : ℕ+, Real.log (n : ℝ) ^ k * (n : ℝ) ^ (-σ)

@[simp] theorem eulerLogPowMass_zero (σ : ℝ) : eulerLogPowMass 0 σ = eulerMass σ := by
  rw [eulerLogPowMass, eulerMass]
  exact tsum_congr fun n => by rw [pow_zero, one_mul]

@[simp] theorem eulerLogPowMass_one (σ : ℝ) : eulerLogPowMass 1 σ = eulerLogMass σ := by
  rw [eulerLogPowMass, eulerLogMass]
  exact tsum_congr fun n => by rw [pow_one]

@[simp] theorem squarefreeLogPowMass_zero (σ : ℝ) :
    squarefreeLogPowMass 0 σ = squarefreeMass σ := by
  rw [squarefreeLogPowMass, squarefreeMass]
  exact tsum_congr fun d => by rw [pow_zero, one_mul]

@[simp] theorem squarefreeLogPowMass_one (σ : ℝ) :
    squarefreeLogPowMass 1 σ = squarefreeLogMass σ := by
  rw [squarefreeLogPowMass, squarefreeLogMass]
  exact tsum_congr fun d => by rw [pow_one]

/-! ## Products across the two factors -/

theorem tsum_dyadic_prod {f : SquarefreePNat → ℝ} {g : ℕ+ → ℝ}
    (hf : Summable f) (hg : Summable g) (hfn : ∀ d, 0 ≤ f d) (hgn : ∀ m, 0 ≤ g m) :
    ∑' q : SquarefreePNat × ℕ+, f q.1 * g q.2 = (∑' d, f d) * ∑' m, g m := by
  have hfa : Summable fun d => ‖f d‖ := by
    refine hf.congr fun d => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hfn d)]
  have hga : Summable fun m => ‖g m‖ := by
    refine hg.congr fun m => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (hgn m)]
  exact (tsum_mul_tsum_of_summable_norm hfa hga).symm

/-- The dyadic weight of the squarefree coordinate. -/
private def wsq (k : ℕ) (σ : ℝ) (d : SquarefreePNat) : ℝ :=
  Real.log ((d.1 : ℝ)) ^ k * ((d.1 : ℝ)) ^ (-σ)

/-- The dyadic weight of the square-residual coordinate. -/
private def wres (k : ℕ) (σ : ℝ) (m : ℕ+) : ℝ :=
  Real.log (m : ℝ) ^ k * (m : ℝ) ^ (-(2 * σ))

private theorem wsq_nonneg (k : ℕ) (σ : ℝ) (d : SquarefreePNat) : 0 ≤ wsq k σ d :=
  logpow_rpow_nonneg (σ := σ) k d.1

private theorem wres_nonneg (k : ℕ) (σ : ℝ) (m : ℕ+) : 0 ≤ wres k σ m :=
  logpow_rpow_nonneg (σ := 2 * σ) k m

private theorem summable_wsq (k : ℕ) {σ : ℝ} (hσ : 1 < σ) : Summable (wsq k σ) :=
  summable_squarefree_logpow_rpow k hσ

private theorem summable_wres (k : ℕ) {σ : ℝ} (hσ : 1 < σ) : Summable (wres k σ) :=
  summable_pnat_logpow_rpow k (by linarith : (1 : ℝ) < 2 * σ)

private theorem tsum_wsq (k : ℕ) (σ : ℝ) : ∑' d, wsq k σ d = squarefreeLogPowMass k σ := rfl

private theorem tsum_wres (k : ℕ) (σ : ℝ) : ∑' m, wres k σ m = eulerLogPowMass k (2 * σ) := rfl

/-- The reindexing of a nonnegative Euler weight along `n = m² d`. -/
private theorem tsum_dyadic_reindex (F : ℕ+ → ℝ) :
    ∑' n : ℕ+, F n
      = ∑' q : SquarefreePNat × ℕ+, F (dyadicSquarefreeSquareEquiv.symm q) := by
  rw [← dyadicSquarefreeSquareEquiv.tsum_eq (fun q => F (dyadicSquarefreeSquareEquiv.symm q))]
  exact tsum_congr fun n => by rw [Equiv.symm_apply_apply]

/-- The `k = 0, 1, 2` integrand identities at one index, in product coordinates. -/
private theorem dyadic_integrand_zero {σ : ℝ} (q : SquarefreePNat × ℕ+) :
    Real.log ((dyadicSquarefreeSquareEquiv.symm q : ℕ+) : ℝ) ^ 0
        * ((dyadicSquarefreeSquareEquiv.symm q : ℕ+) : ℝ) ^ (-σ)
      = wsq 0 σ q.1 * wres 0 σ q.2 := by
  have hrp := rpow_dyadic_split_symm (-σ) q
  rw [show 2 * (-σ) = -(2 * σ) by ring] at hrp
  rw [wsq, wres, pow_zero, pow_zero, pow_zero, one_mul, one_mul, one_mul, hrp]

private theorem dyadic_integrand_one {σ : ℝ} (q : SquarefreePNat × ℕ+) :
    Real.log ((dyadicSquarefreeSquareEquiv.symm q : ℕ+) : ℝ) ^ 1
        * ((dyadicSquarefreeSquareEquiv.symm q : ℕ+) : ℝ) ^ (-σ)
      = wsq 1 σ q.1 * wres 0 σ q.2 + 2 * (wsq 0 σ q.1 * wres 1 σ q.2) := by
  have hrp := rpow_dyadic_split_symm (-σ) q
  rw [show 2 * (-σ) = -(2 * σ) by ring] at hrp
  have hlog := dyadicSquarefreeSquareEquiv_log (dyadicSquarefreeSquareEquiv.symm q)
  rw [Equiv.apply_symm_apply] at hlog
  rw [wsq, wsq, wres, wres, pow_zero, pow_zero, pow_one, pow_one, pow_one, hrp, hlog]
  ring

private theorem dyadic_integrand_two {σ : ℝ} (q : SquarefreePNat × ℕ+) :
    Real.log ((dyadicSquarefreeSquareEquiv.symm q : ℕ+) : ℝ) ^ 2
        * ((dyadicSquarefreeSquareEquiv.symm q : ℕ+) : ℝ) ^ (-σ)
      = wsq 2 σ q.1 * wres 0 σ q.2 + 4 * (wsq 1 σ q.1 * wres 1 σ q.2)
        + 4 * (wsq 0 σ q.1 * wres 2 σ q.2) := by
  have hrp := rpow_dyadic_split_symm (-σ) q
  rw [show 2 * (-σ) = -(2 * σ) by ring] at hrp
  have hlog := dyadicSquarefreeSquareEquiv_log (dyadicSquarefreeSquareEquiv.symm q)
  rw [Equiv.apply_symm_apply] at hlog
  rw [wsq, wsq, wsq, wres, wres, wres, pow_zero, pow_zero, pow_one, pow_one, hrp, hlog]
  ring

/-! ## The exact moment splits -/

private theorem summable_dyadic_block (j k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    Summable (fun q : SquarefreePNat × ℕ+ => wsq j σ q.1 * wres k σ q.2) :=
  (summable_wsq j hσ).mul_of_nonneg (summable_wres k hσ)
    (fun d => wsq_nonneg j σ d) (fun m => wres_nonneg k σ m)

private theorem tsum_dyadic_block (j k : ℕ) {σ : ℝ} (hσ : 1 < σ) :
    ∑' q : SquarefreePNat × ℕ+, wsq j σ q.1 * wres k σ q.2
      = squarefreeLogPowMass j σ * eulerLogPowMass k (2 * σ) :=
  tsum_dyadic_prod (summable_wsq j hσ) (summable_wres k hσ)
    (fun d => wsq_nonneg j σ d) (fun m => wres_nonneg k σ m)

/-- **Zeroth moment split** — the mass identity `(6)` in moment notation. -/
theorem eulerLogPowMass_split_zero {σ : ℝ} (hσ : 1 < σ) :
    eulerLogPowMass 0 σ = squarefreeLogPowMass 0 σ * eulerLogPowMass 0 (2 * σ) := by
  rw [eulerLogPowMass, tsum_dyadic_reindex
    (fun n : ℕ+ => Real.log (n : ℝ) ^ 0 * (n : ℝ) ^ (-σ))]
  rw [tsum_congr (fun q => dyadic_integrand_zero (σ := σ) q), tsum_dyadic_block 0 0 hσ]

/-- **First moment split.** -/
theorem eulerLogPowMass_split_one {σ : ℝ} (hσ : 1 < σ) :
    eulerLogPowMass 1 σ
      = squarefreeLogPowMass 1 σ * eulerLogPowMass 0 (2 * σ)
        + 2 * (squarefreeLogPowMass 0 σ * eulerLogPowMass 1 (2 * σ)) := by
  have h1 := summable_dyadic_block 1 0 hσ
  have h2 := (summable_dyadic_block 0 1 hσ).mul_left 2
  rw [eulerLogPowMass, tsum_dyadic_reindex
    (fun n : ℕ+ => Real.log (n : ℝ) ^ 1 * (n : ℝ) ^ (-σ))]
  rw [tsum_congr (fun q => dyadic_integrand_one (σ := σ) q), h1.tsum_add h2,
    tsum_dyadic_block 1 0 hσ, tsum_mul_left, tsum_dyadic_block 0 1 hσ]

/-- **Second moment split.** -/
theorem eulerLogPowMass_split_two {σ : ℝ} (hσ : 1 < σ) :
    eulerLogPowMass 2 σ
      = squarefreeLogPowMass 2 σ * eulerLogPowMass 0 (2 * σ)
        + 4 * (squarefreeLogPowMass 1 σ * eulerLogPowMass 1 (2 * σ))
        + 4 * (squarefreeLogPowMass 0 σ * eulerLogPowMass 2 (2 * σ)) := by
  have h1 := summable_dyadic_block 2 0 hσ
  have h2 := (summable_dyadic_block 1 1 hσ).mul_left 4
  have h3 := (summable_dyadic_block 0 2 hσ).mul_left 4
  rw [eulerLogPowMass, tsum_dyadic_reindex
    (fun n : ℕ+ => Real.log (n : ℝ) ^ 2 * (n : ℝ) ^ (-σ))]
  rw [tsum_congr (fun q => dyadic_integrand_two (σ := σ) q), (h1.add h2).tsum_add h3,
    h1.tsum_add h2, tsum_dyadic_block 2 0 hσ, tsum_mul_left, tsum_dyadic_block 1 1 hσ,
    tsum_mul_left, tsum_dyadic_block 0 2 hσ]

/-! ## Variances and their exact additivity -/

/-- `Var_σ(log n)` in the pointed Euler state `e_σ`. -/
def eulerLogVariance (σ : ℝ) : ℝ :=
  eulerLogPowMass 2 σ / eulerMass σ - (eulerLogMean σ) ^ 2

/-- `Var_σ(log d)` in the signed squarefree parity state `s_σ`. -/
def squarefreeLogVariance (σ : ℝ) : ℝ :=
  squarefreeLogPowMass 2 σ / squarefreeMass σ - (squarefreeLogMean σ) ^ 2

/-- **Exact variance additivity.**  `Var_σ(log n) = Var_σ(log d) + 4 · Var_{2σ}(log m)`.
This is the norm identity `(15)` of the card. -/
theorem eulerLogVariance_split {σ : ℝ} (hσ : 1 < σ) :
    eulerLogVariance σ = squarefreeLogVariance σ + 4 * eulerLogVariance (2 * σ) := by
  have hσ2 : 1 < 2 * σ := by linarith
  have hZ : squarefreeMass σ ≠ 0 := ne_of_gt (squarefreeMass_pos hσ)
  have hE2 : eulerMass (2 * σ) ≠ 0 := ne_of_gt (eulerMass_pos hσ2)
  have hmass : eulerMass σ = squarefreeMass σ * eulerMass (2 * σ) :=
    (squarefreeMass_mul_eulerMass_two_mul hσ).symm
  have hone := eulerLogPowMass_split_one hσ
  have htwo := eulerLogPowMass_split_two hσ
  simp only [eulerLogPowMass_zero, eulerLogPowMass_one, squarefreeLogPowMass_zero,
    squarefreeLogPowMass_one] at hone htwo
  rw [eulerLogVariance, eulerLogVariance, squarefreeLogVariance, eulerLogMean, eulerLogMean,
    squarefreeLogMean, htwo, hone, hmass]
  field_simp
  ring

end RHTower
