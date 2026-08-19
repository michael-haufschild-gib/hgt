import GaloisForLFunctions.HTGeometry.LpInjectionCompression

/-!
# The concrete all-prime multiplicative co-shift model on `ℓ²(ℕ≥1)`

`H = ℓ²(ℕ≥1)` carries, for every positive integer `p`, the multiplicative isometry
`V_p e_n = e_{pn}` and its adjoint the co-shift `(V_p^* x)_n = x_{pn}`.  For a complex parameter
`s` the *all-prime row* is the family of operators

```
T_{p,s} = V_p^* - p^{-s}, p prime.
```

This module builds the model and proves the **common eigenline theorem**: the simultaneous
eigenspace

```
L_s = ⋂_p ker T_{p,s}
```

is the single line `ℂ·Ψ_s`, `Ψ_s = (n^{-s})_{n ≥ 1}`, when `Re s > 1/2`, and is `0` when
`Re s ≤ 1/2`.  Both halves come from the same coordinate recursion `x_{pn} = p^{-s} x_n`, which
unique factorization integrates to `x_n = n^{-s} x_1`; the threshold is exactly the convergence
abscissa of `∑ n^{-2 Re s}`.

Nothing here uses an Euler product, analytic continuation, or any property of `ζ`.
-/

open scoped ENNReal
open RHTower

namespace RHTower.PrimeCoShift

noncomputable section

/-- The arithmetic Hilbert space `ℓ²(ℕ≥1)`. -/
abbrev H : Type := lp (fun _ : ℕ+ => ℂ) 2

/-- Multiplication by a positive integer is injective on `ℕ≥1`. -/
theorem mulLeft_injective (p : ℕ+) : Function.Injective (fun n : ℕ+ => p * n) :=
  fun _ _ h => mul_left_cancel h

/-- The multiplicative isometry `V_p e_n = e_{pn}`. -/
def primeShift (p : ℕ+) : H →ₗᵢ[ℂ] H :=
  lpScalarInjection (fun n : ℕ+ => p * n) (mulLeft_injective p)

/-- The multiplicative co-shift `(V_p^* x)_n = x_{pn}`, the Hilbert adjoint of `V_p`. -/
def primeCoShift (p : ℕ+) : H →L[ℂ] H :=
  lpCoordinatePullback (E := ℂ) (fun n : ℕ+ => p * n) (mulLeft_injective p)

@[simp] theorem primeCoShift_apply (p : ℕ+) (x : H) (n : ℕ+) :
    primeCoShift p x n = x (p * n) := rfl

theorem primeCoShift_eq_adjoint (p : ℕ+) :
    primeCoShift p = ((primeShift p).toContinuousLinearMap).adjoint :=
  lpCoordinatePullback_eq_adjoint_lpScalarInjection _ _

/-- A prime, viewed as a positive integer. -/
def primePNat (p : Nat.Primes) : ℕ+ := ⟨(p : ℕ), p.property.pos⟩

@[simp] theorem primePNat_coe (p : Nat.Primes) : ((primePNat p : ℕ+) : ℕ) = (p : ℕ) := rfl

/-- The `p`-th member of the all-prime row, `T_{p,s} = V_p^* - p^{-s}`. -/
def rowOp (s : ℂ) (p : Nat.Primes) : H →L[ℂ] H :=
  primeCoShift (primePNat p) - (((p : ℕ) : ℂ) ^ (-s)) • ContinuousLinearMap.id ℂ H

@[simp] theorem rowOp_apply (s : ℂ) (p : Nat.Primes) (x : H) (n : ℕ+) :
    rowOp s p x n = x (primePNat p * n) - ((p : ℕ) : ℂ) ^ (-s) * x n := by
  simp [rowOp]

/-- The simultaneous eigenspace of the all-prime co-shift row. -/
def eigenSubmodule (s : ℂ) : Submodule ℂ H :=
  ⨅ p : Nat.Primes, LinearMap.ker (rowOp s p).toLinearMap

theorem mem_eigenSubmodule_iff {s : ℂ} {x : H} :
    x ∈ eigenSubmodule s ↔ ∀ p : Nat.Primes, rowOp s p x = 0 := by
  simp [eigenSubmodule, Submodule.mem_iInf, LinearMap.mem_ker]

theorem eigen_recursion {s : ℂ} {x : H} (hx : x ∈ eigenSubmodule s)
    (p : Nat.Primes) (n : ℕ+) :
    x (primePNat p * n) = ((p : ℕ) : ℂ) ^ (-s) * x n := by
  have h := mem_eigenSubmodule_iff.mp hx p
  have := congrArg (fun z : H => z n) h
  simp only [rowOp_apply, lp.coeFn_zero, Pi.zero_apply] at this
  linear_combination this

/-- **The coordinate law.**  Unique factorization integrates the prime recursion
`x_{pn} = p^{-s} x_n` into `x_n = n^{-s} x_1`. -/
theorem eigen_coordinate {s : ℂ} {x : H} (hx : x ∈ eigenSubmodule s) (n : ℕ+) :
    x n = ((n : ℕ) : ℂ) ^ (-s) * x 1 := by
  have key : ∀ m : ℕ, ∀ n : ℕ+, (n : ℕ) = m → x n = ((n : ℕ) : ℂ) ^ (-s) * x 1 := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro n hn
      by_cases h1 : (n : ℕ) = 1
      · have : n = 1 := PNat.coe_injective (by simpa using h1)
        subst this
        simp
      · have hq : Nat.Prime ((n : ℕ).minFac) := Nat.minFac_prime h1
        set q : ℕ := (n : ℕ).minFac with hqdef
        have hdvd : q ∣ (n : ℕ) := Nat.minFac_dvd _
        obtain ⟨k, hk⟩ := hdvd
        have hnpos : 0 < (n : ℕ) := n.property
        have hkpos : 0 < k := by
          rcases Nat.eq_zero_or_pos k with hk0 | hk0
          · exfalso; rw [hk0, Nat.mul_zero] at hk; omega
          · exact hk0
        have hq2 : 2 ≤ q := hq.two_le
        have hklt : k < (n : ℕ) := by
          have : q * k ≥ 2 * k := Nat.mul_le_mul_right k hq2
          omega
        let nk : ℕ+ := ⟨k, hkpos⟩
        have hmul : primePNat ⟨q, hq⟩ * nk = n := by
          apply PNat.coe_injective
          simpa [primePNat, nk] using hk.symm
        have hrec := eigen_recursion hx ⟨q, hq⟩ nk
        rw [hmul] at hrec
        have hih : x nk = ((k : ℕ) : ℂ) ^ (-s) * x 1 := ih k (hn ▸ hklt) nk rfl
        rw [hrec, hih]
        have hqk : ((q * k : ℕ) : ℂ) ^ (-s) = ((q : ℕ) : ℂ) ^ (-s) * ((k : ℕ) : ℂ) ^ (-s) := by
          rw [Nat.cast_mul]
          exact Complex.natCast_mul_natCast_cpow q k (-s)
        rw [hk, hqk]
        ring
  exact key (n : ℕ) n rfl

/-- The tail of the ground state: `n ↦ n^{-s}`. -/
def groundFun (s : ℂ) : ℕ+ → ℂ := fun n => ((n : ℕ) : ℂ) ^ (-s)

theorem memℓp_groundFun {s : ℂ} (hs : 1 / 2 < s.re) : Memℓp (groundFun s) 2 := by
  refine memℓp_gen ?_
  have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [h2]
  have hbase : Summable fun n : ℕ => (((n : ℝ)) ^ (2 * s.re))⁻¹ := by
    rw [Real.summable_nat_rpow_inv]; linarith
  refine (hbase.comp_injective PNat.coe_injective).congr ?_
  intro n
  have hn : 0 < (n : ℕ) := n.property
  have hx : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg _
  simp only [Function.comp_apply, groundFun]
  rw [Complex.norm_natCast_cpow_of_pos hn]
  simp only [Complex.neg_re]
  rw [← Real.rpow_mul hx, ← Real.rpow_neg hx]
  congr 1
  ring

/-- The arithmetic ground state `Ψ_s = (n^{-s})_{n ≥ 1}`, defined for `Re s > 1/2`. -/
def groundState (s : ℂ) : H :=
  if h : 1 / 2 < s.re then ⟨groundFun s, memℓp_groundFun h⟩ else 0

theorem groundState_apply {s : ℂ} (hs : 1 / 2 < s.re) (n : ℕ+) :
    groundState s n = ((n : ℕ) : ℂ) ^ (-s) := by
  rw [groundState, dif_pos hs]; rfl

theorem groundState_one {s : ℂ} (hs : 1 / 2 < s.re) : groundState s 1 = 1 := by
  rw [groundState_apply hs]
  simp

theorem groundState_ne_zero {s : ℂ} (hs : 1 / 2 < s.re) : groundState s ≠ 0 := by
  intro h
  have := groundState_one hs
  rw [h] at this
  simp at this

/-- The ground state satisfies every prime eigen-equation. -/
theorem groundState_mem_eigenSubmodule {s : ℂ} (hs : 1 / 2 < s.re) :
    groundState s ∈ eigenSubmodule s := by
  refine mem_eigenSubmodule_iff.mpr fun p => ?_
  apply lp.ext
  funext n
  simp only [rowOp_apply, lp.coeFn_zero, Pi.zero_apply, groundState_apply hs]
  have hcoe : ((primePNat p * n : ℕ+) : ℕ) = (p : ℕ) * (n : ℕ) := rfl
  rw [hcoe, Nat.cast_mul, Complex.natCast_mul_natCast_cpow]
  ring

/-- Below the Hilbert wall the ground profile is not square summable. -/
theorem not_summable_rpow_inv_of_le {σ : ℝ} (hσ : σ ≤ 1 / 2) :
    ¬ Summable fun n : ℕ+ => (((n : ℕ) : ℝ) ^ (2 * σ))⁻¹ := by
  intro h
  have hinj : Function.Injective fun k : ℕ => (⟨k + 1, Nat.succ_pos k⟩ : ℕ+) := by
    intro a b hab
    simpa using congrArg (fun m : ℕ+ => (m : ℕ)) hab
  have h1 := h.comp_injective hinj
  have h2 : Summable fun k : ℕ => ((((k + 1 : ℕ)) : ℝ) ^ (2 * σ))⁻¹ := h1
  have h3 : Summable fun k : ℕ => (((k : ℕ) : ℝ) ^ (2 * σ))⁻¹ :=
    (summable_nat_add_iff (f := fun k : ℕ => (((k : ℕ) : ℝ) ^ (2 * σ))⁻¹) 1).mp (by
      simpa using h2)
  have := Real.summable_nat_rpow_inv.mp h3
  linarith

/-- **The Hilbert threshold.**  Above the wall the eigenspace is exactly the arithmetic line. -/
theorem eigenSubmodule_eq_span {s : ℂ} (hs : 1 / 2 < s.re) :
    eigenSubmodule s = Submodule.span ℂ {groundState s} := by
  refine le_antisymm (fun x hx => ?_) ?_
  · refine Submodule.mem_span_singleton.mpr ⟨x 1, ?_⟩
    apply lp.ext
    funext n
    rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, groundState_apply hs]
    rw [eigen_coordinate hx n]
    ring
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    exact groundState_mem_eigenSubmodule hs

/-- **The Hilbert threshold, lower half.**  On or below the wall there is no common Hilbert
eigenvector at all. -/
theorem eigenSubmodule_eq_bot {s : ℂ} (hs : s.re ≤ 1 / 2) : eigenSubmodule s = ⊥ := by
  refine le_antisymm (fun x hx => ?_) bot_le
  have hcoord := eigen_coordinate hx
  have hx1 : x 1 = 0 := by
    by_contra hne
    have hsum : Summable fun n : ℕ+ => ‖x n‖ ^ (2 : ℝ≥0∞).toReal :=
      (lp.memℓp x).summable (by norm_num)
    have h2 : (2 : ℝ≥0∞).toReal = 2 := by norm_num
    rw [h2] at hsum
    have hprofile : ∀ n : ℕ+, ‖x n‖ ^ (2 : ℝ)
        = (((n : ℕ) : ℝ) ^ (2 * s.re))⁻¹ * ‖x 1‖ ^ (2 : ℝ) := by
      intro n
      have hn : 0 < (n : ℕ) := n.property
      have hb : (0 : ℝ) ≤ ((n : ℕ) : ℝ) := Nat.cast_nonneg _
      rw [hcoord n, norm_mul, Complex.norm_natCast_cpow_of_pos hn]
      simp only [Complex.neg_re]
      rw [Real.mul_rpow (by positivity) (norm_nonneg _)]
      congr 1
      rw [← Real.rpow_mul hb, ← Real.rpow_neg hb]
      congr 1
      ring
    have hsum2 : Summable fun n : ℕ+ => (((n : ℕ) : ℝ) ^ (2 * s.re))⁻¹ * ‖x 1‖ ^ (2 : ℝ) :=
      hsum.congr hprofile
    have hne2 : ‖x 1‖ ^ (2 : ℝ) ≠ 0 := by
      have : ‖x 1‖ ≠ 0 := norm_ne_zero_iff.mpr hne
      positivity
    have := hsum2.mul_right (‖x 1‖ ^ (2 : ℝ))⁻¹
    refine not_summable_rpow_inv_of_le hs (this.congr fun n => ?_)
    field_simp
  refine Submodule.mem_bot ℂ |>.mpr ?_
  apply lp.ext
  funext n
  rw [hcoord n, hx1]
  simp

end

end RHTower.PrimeCoShift
