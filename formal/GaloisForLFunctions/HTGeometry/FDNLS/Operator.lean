import GaloisForLFunctions.HTGeometry.FDNLS.DispersionRelation

/-!
# The quasi-Riesz fractional discrete derivative as an operator

Zhong--Malomed--Yan, arXiv:2407.12441, Section II A, equations (9), (11) and (14).

Equation (9) *defines* the operator by conjugating multiplication by the symbol `|k|^α` with the
lattice Fourier transform, and then evaluates the conjugation as the convolution
`u ↦ ∑_ℓ D_ℓ^{(α)} u_{n+ℓ}`.  This file carries out that evaluation, and specialises it to the two
Lévy indices for which the paper writes the operator out: `α = 2` (equation (11), the inverse-square
long-range lattice) and `α = 1` (equation (14), where only odd separations couple).

## Main results

* `quasiRieszDeriv` — the convolution form of the operator.
* `quasiRieszDeriv_eq_finsum` — on finitely supported data the convolution is a finite sum.
* `quasiRieszDeriv_eq_fourierMultiplier` — **equation (9)**: the convolution really is the Fourier
  multiplier `|k|^α`.
* `quasiRieszCoupling_two_eq`, `quasiRieszCoupling_one_eq` — **equations (11) and (14)** as complete
  coefficient tables.
* `quasiRieszDeriv_two`, `quasiRieszDeriv_one` — the two operators written out.
-/

open MeasureTheory Set Filter Topology intervalIntegral

namespace GaloisForLFunctions.HTGeometry.FDNLS

/-- **Equation (9), right-hand side.**  The quasi-Riesz fractional discrete derivative of Lévy
index `α`, as a convolution against the coupling coefficients. -/
noncomputable def quasiRieszDeriv (α : ℝ) (u : ℤ → ℂ) (n : ℤ) : ℂ :=
  ∑' ℓ : ℤ, ((quasiRieszCoupling α ℓ : ℝ) : ℂ) * u (n + ℓ)

/-- On finitely supported lattice data the operator is a finite sum against the coupling table. -/
theorem quasiRieszDeriv_eq_finsum {α : ℝ} (S : Finset ℤ) (u : ℤ → ℂ) (hu : ∀ m ∉ S, u m = 0)
    (n : ℤ) :
    quasiRieszDeriv α u n = ∑ m ∈ S, ((quasiRieszCoupling α (m - n) : ℝ) : ℂ) * u m := by
  have hzero : ∀ ℓ ∉ S.image (fun m => m - n), ((quasiRieszCoupling α ℓ : ℝ) : ℂ) * u (n + ℓ) = 0 := by
    intro ℓ hℓ
    have : u (n + ℓ) = 0 := by
      refine hu (n + ℓ) fun hmem => hℓ ?_
      refine Finset.mem_image.mpr ⟨n + ℓ, hmem, by ring⟩
    rw [this, mul_zero]
  rw [quasiRieszDeriv, tsum_eq_sum hzero]
  rw [Finset.sum_image (fun x _ y _ h => by omega)]
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 2
  omega

/-- **Equation (9).**  The convolution operator is exactly the Fourier multiplier by `|k|^α`:
for finitely supported data,
`∑_ℓ D_ℓ^{(α)} u_{n+ℓ} = (1/2π) ∫_{-π}^{π} e^{ikn} |k|^α (∑_m u_m e^{-ikm}) dk`. -/
theorem quasiRieszDeriv_eq_fourierMultiplier {α : ℝ} (hα : 0 ≤ α) (S : Finset ℤ) (u : ℤ → ℂ)
    (hu : ∀ m ∉ S, u m = 0) (n : ℤ) :
    quasiRieszDeriv α u n
      = (1 / (2 * Real.pi) : ℝ) • ∫ k in (-Real.pi)..Real.pi,
          Complex.exp ((k : ℂ) * (n : ℂ) * Complex.I) * ((|k| ^ α : ℝ) : ℂ)
            * (∑ m ∈ S, u m * Complex.exp (-((k : ℂ) * (m : ℂ) * Complex.I))) := by
  have hcont : ∀ m : ℤ, Continuous (rieszFourierIntegrand α (m - n)) := fun m =>
    continuous_rieszFourierIntegrand hα _
  have hexpand : ∀ k : ℝ,
      Complex.exp ((k : ℂ) * (n : ℂ) * Complex.I) * ((|k| ^ α : ℝ) : ℂ)
          * (∑ m ∈ S, u m * Complex.exp (-((k : ℂ) * (m : ℂ) * Complex.I)))
        = ∑ m ∈ S, u m * rieszFourierIntegrand α (m - n) k := by
    intro k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    simp only [rieszFourierIntegrand]
    rw [show (-(((m - n : ℤ) : ℂ) * (k : ℂ) * Complex.I))
        = ((k : ℂ) * (n : ℂ) * Complex.I) + (-((k : ℂ) * (m : ℂ) * Complex.I)) by push_cast; ring,
      Complex.exp_add]
    ring
  rw [intervalIntegral.integral_congr (fun k _ => hexpand k),
    intervalIntegral.integral_finsetSum
      (fun m _ => ((hcont m).const_mul (u m)).intervalIntegrable _ _)]
  rw [Finset.smul_sum, quasiRieszDeriv_eq_finsum S u hu n]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [intervalIntegral.integral_const_mul, quasiRieszCoupling_eq_fourierIntegral hα (m - n)]
  simp only [Complex.real_smul]
  ring

/-! ## The two written-out operators -/

/-- **Equation (11), coefficient table.**  At `α = 2` the coupling is `π²/3` on the diagonal and
`2(-1)^ℓ/ℓ²` off it: an inverse-square long-range lattice with alternating signs. -/
theorem quasiRieszCoupling_two_eq (ℓ : ℤ) :
    quasiRieszCoupling 2 ℓ = if ℓ = 0 then Real.pi ^ (2 : ℕ) / 3 else 2 * (-1 : ℝ) ^ ℓ / (ℓ : ℝ) ^ (2 : ℕ) := by
  by_cases h : ℓ = 0
  · rw [if_pos h, h, quasiRieszCoupling_two_zero]
  · rw [if_neg h, quasiRieszCoupling_two h]

/-- **Equation (14), coefficient table.**  At `α = 1` the coupling is `π/2` on the diagonal, `0` at
every even separation, and `-2/(π ℓ²)` at every odd one. -/
theorem quasiRieszCoupling_one_eq (ℓ : ℤ) :
    quasiRieszCoupling 1 ℓ
      = if ℓ = 0 then Real.pi / 2 else ((-1 : ℝ) ^ ℓ - 1) / (Real.pi * (ℓ : ℝ) ^ (2 : ℕ)) := by
  by_cases h : ℓ = 0
  · rw [if_pos h, h, quasiRieszCoupling_one_zero]
  · rw [if_neg h, quasiRieszCoupling_one h]

/-- **Equation (11).**  The integer-order operator of the paper, written out on finitely supported
data. -/
theorem quasiRieszDeriv_two (S : Finset ℤ) (u : ℤ → ℂ) (hu : ∀ m ∉ S, u m = 0) (n : ℤ) :
    quasiRieszDeriv 2 u n
      = ((Real.pi ^ (2 : ℕ) / 3 : ℝ) : ℂ) * u n
        + ∑ m ∈ S.erase n, ((2 * (-1 : ℝ) ^ (m - n) / ((m - n : ℤ) : ℝ) ^ (2 : ℕ) : ℝ) : ℂ) * u m := by
  rw [quasiRieszDeriv_eq_finsum S u hu n]
  by_cases hn : n ∈ S
  · rw [← Finset.sum_erase_add S _ hn]
    have hd : ((quasiRieszCoupling 2 (n - n) : ℝ) : ℂ) * u n = ((Real.pi ^ (2 : ℕ) / 3 : ℝ) : ℂ) * u n := by
      rw [show n - n = (0:ℤ) by ring, quasiRieszCoupling_two_zero]
    rw [hd, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [quasiRieszCoupling_two (by
      have := Finset.ne_of_mem_erase hm
      omega)]
  · have hun : u n = 0 := hu n hn
    rw [hun, mul_zero, zero_add, Finset.erase_eq_of_notMem hn]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [quasiRieszCoupling_two (by
      have : m ≠ n := fun h => hn (h ▸ hm)
      omega)]

/-- **Equation (14).**  The `α = 1` operator, written out on finitely supported data.  The
coefficient `((-1)^{m-n} - 1)/(π (m-n)²)` vanishes at every even separation, so a site is coupled
only to `n ± 1, n ± 3, n ± 5, …`. -/
theorem quasiRieszDeriv_one (S : Finset ℤ) (u : ℤ → ℂ) (hu : ∀ m ∉ S, u m = 0) (n : ℤ) :
    quasiRieszDeriv 1 u n
      = ((Real.pi / 2 : ℝ) : ℂ) * u n
        + ∑ m ∈ S.erase n,
            ((((-1 : ℝ) ^ (m - n) - 1) / (Real.pi * ((m - n : ℤ) : ℝ) ^ (2 : ℕ)) : ℝ) : ℂ) * u m := by
  rw [quasiRieszDeriv_eq_finsum S u hu n]
  by_cases hn : n ∈ S
  · rw [← Finset.sum_erase_add S _ hn]
    have hd : ((quasiRieszCoupling 1 (n - n) : ℝ) : ℂ) * u n = ((Real.pi / 2 : ℝ) : ℂ) * u n := by
      rw [show n - n = (0:ℤ) by ring, quasiRieszCoupling_one_zero]
    rw [hd, add_comm]
    congr 1
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [quasiRieszCoupling_one (by
      have := Finset.ne_of_mem_erase hm
      omega)]
  · have hun : u n = 0 := hu n hn
    rw [hun, mul_zero, zero_add, Finset.erase_eq_of_notMem hn]
    refine Finset.sum_congr rfl fun m hm => ?_
    rw [quasiRieszCoupling_one (by
      have : m ≠ n := fun h => hn (h ▸ hm)
      omega)]

end GaloisForLFunctions.HTGeometry.FDNLS
