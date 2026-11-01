import GaloisForLFunctions.ArithmeticCouplingTheory.TheCouplingCalculus
import GaloisForLFunctions.ArithmeticPositiveDuality.WeilsTheoremForCurvesIsPositiveDefinitenessOnZ

/-!
# The coupling of a curve: the `𝔽_q` calibration

For a curve datum with normalized Frobenius eigenvalues `β_i`, the scaling group of the curve is
`q^ℤ`, of rank one, and Weil's kernel on it is the **Frobenius kernel** `K(n) = Σ_i β_i^n`,
`n ∈ ℤ` (`frobKernel`). Its coupling is a sum of products (`coupling_frobKernel`):

  `C_K(a, b) = Σ_i (β_i^a − 1)(β_i^b − 1)`,

the primitive intersection of the graph differences `Γ_{F^a} − Δ` and `Γ_{F^b} − Δ`.

Two prime towers of degrees `d₁, d₂` live in `d₁ℤ` and `d₂ℤ`. They are **commensurable**: the
antidiagonal `(d₁d₂k, −d₁d₂k)` lies in `d₁ℤ × d₂ℤ`, so the self-coupling
`C(n, −n) = 2(K(0) − K(n))` is sampled exactly, with no density argument. Hence
(`unitary_iff_bounded_tower_coupling`, `spanHodgeIndex_iff_bounded_tower_coupling`):

  bounded coupling of two Frobenius towers ⇔ `|β_i| = 1` for all `i` ⇔ Castelnuovo–Severi on the
  Frobenius span.

The golden fake curve (`β = φ^{±1}`, integral point counts) has unbounded coupling on every pair of
towers (`not_bounded_tower_coupling_golden`). Over `ℤ` the two-prime towers are incommensurable
(`2^a ≠ 3^b`), the antidiagonal is never sampled, and the density transfer of
`TheCouplingIsAsLargeAsTheKernel` replaces commensurability without loss.
-/

open Complex Finset
open GaloisForLFunctions.ArithmeticCastelnuovoSeveri (CurveDatum goldenDatum)

noncomputable section

namespace GaloisForLFunctions.ArithmeticCouplingTheory

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

theorem CurveDatum.β_ne_zero (i : ι) : D.β i ≠ 0 := by
  intro h
  have := D.β_fePerm i
  rw [h, mul_zero] at this
  exact zero_ne_one this

/-- The character `n ↦ β_i^n` of the scaling group `ℤ` of the curve. -/
def frobCharacter (i : ι) : Multiplicative ℤ →* ℂ where
  toFun n := D.β i ^ Multiplicative.toAdd n
  map_one' := by simp
  map_mul' m n := by rw [toAdd_mul, zpow_add₀ (CurveDatum.β_ne_zero D i)]

/-- The **Frobenius kernel** `K(n) = Σ_i β_i^n` on the scaling group `ℤ` of the curve. -/
def frobKernel (n : Multiplicative ℤ) : ℂ := ∑ i, frobCharacter D i n

theorem frobKernel_one : frobKernel D 1 = Fintype.card ι := by
  simp [frobKernel]

/-- The functional equation makes the Frobenius kernel even. -/
theorem frobKernel_inv (n : Multiplicative ℤ) : frobKernel D n⁻¹ = frobKernel D n := by
  unfold frobKernel
  rw [← Equiv.sum_comp D.fePerm]
  refine sum_congr rfl fun i _ => ?_
  have h : D.β (D.fePerm i) = (D.β i)⁻¹ := eq_inv_of_mul_eq_one_left (D.β_fePerm i)
  simp only [frobCharacter, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_inv, h, zpow_neg, inv_zpow]

/-- **The coupling of a curve is a sum of products.** -/
theorem coupling_frobKernel (a b : Multiplicative ℤ) :
    coupling (frobKernel D) a b = ∑ i, (frobCharacter D i a - 1) * (frobCharacter D i b - 1) := by
  rw [show frobKernel D = fun n => ∑ i ∈ univ, frobCharacter D i n from rfl, coupling_sum]
  exact sum_congr rfl fun i _ => coupling_monoidHom _ a b

/-- The self-coupling along the antidiagonal: `C(n, −n) = 2(K(0) − K(n))`. -/
theorem coupling_frobKernel_inv (n : Multiplicative ℤ) :
    coupling (frobKernel D) n n⁻¹ = 2 * (frobKernel D 1 - frobKernel D n) := by
  rw [coupling, mul_inv_cancel, frobKernel_inv]; ring

/-- **The coupling of two Frobenius towers is bounded iff the curve satisfies RH.** The towers have
degrees `d₁, d₂ > 0`; the coupling is read on `d₁ℤ × d₂ℤ`. -/
theorem unitary_iff_bounded_tower_coupling {d₁ d₂ : ℕ} (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    (∀ i, ‖D.β i‖ = 1) ↔ ∃ M : ℝ, ∀ a b : ℤ,
      ‖coupling (frobKernel D) (Multiplicative.ofAdd ((d₁ : ℤ) * a))
        (Multiplicative.ofAdd ((d₂ : ℤ) * b))‖ ≤ M := by
  constructor
  · intro hU
    refine ⟨Fintype.card ι * 4, fun a b => ?_⟩
    rw [coupling_frobKernel]
    have hχ : ∀ i (n : Multiplicative ℤ), ‖frobCharacter D i n - 1‖ ≤ 2 := fun i n => by
      calc ‖frobCharacter D i n - 1‖ ≤ ‖frobCharacter D i n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by
          simp only [frobCharacter, MonoidHom.coe_mk, OneHom.coe_mk, norm_zpow, hU, one_zpow,
            norm_one]
          norm_num
    calc ‖∑ i, (frobCharacter D i _ - 1) * (frobCharacter D i _ - 1)‖
        ≤ ∑ i : ι, ‖(frobCharacter D i (Multiplicative.ofAdd ((d₁ : ℤ) * a)) - 1) *
            (frobCharacter D i (Multiplicative.ofAdd ((d₂ : ℤ) * b)) - 1)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : ι, (4 : ℝ) := sum_le_sum fun i _ => by
          rw [norm_mul]
          nlinarith [hχ i (Multiplicative.ofAdd ((d₁ : ℤ) * a)),
            hχ i (Multiplicative.ofAdd ((d₂ : ℤ) * b)), norm_nonneg
            (frobCharacter D i (Multiplicative.ofAdd ((d₁ : ℤ) * a)) - 1)]
      _ = Fintype.card ι * 4 := by simp
  · rintro ⟨M, hM⟩
    set L : ℕ := d₁ * d₂
    have hL : 0 < L := Nat.mul_pos h₁ h₂
    have hbound : ∀ k : ℕ, ‖∑ i, (D.β i ^ L) ^ k‖ ≤ (Fintype.card ι + M / 2) * 1 ^ k := by
      intro k
      have hc := hM ((d₂ : ℤ) * k) (-((d₁ : ℤ) * k))
      have e1 : Multiplicative.ofAdd ((d₁ : ℤ) * ((d₂ : ℤ) * k)) = Multiplicative.ofAdd ((L * k : ℕ) : ℤ) := by
        congr 1; push_cast; ring
      have e2 : Multiplicative.ofAdd ((d₂ : ℤ) * -((d₁ : ℤ) * k)) =
          (Multiplicative.ofAdd ((L * k : ℕ) : ℤ))⁻¹ := by
        rw [← ofAdd_neg]; congr 1; push_cast; ring
      rw [e1, e2, coupling_frobKernel_inv, norm_mul, Complex.norm_two] at hc
      have hK : frobKernel D (Multiplicative.ofAdd ((L * k : ℕ) : ℤ)) = ∑ i, (D.β i ^ L) ^ k := by
        simp only [frobKernel, frobCharacter, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd,
          zpow_natCast, pow_mul]
      have h3 : ‖frobKernel D (Multiplicative.ofAdd ((L * k : ℕ) : ℤ))‖ ≤
          ‖frobKernel D 1‖ + ‖frobKernel D 1 - frobKernel D (Multiplicative.ofAdd ((L * k : ℕ) : ℤ))‖ := by
        have := norm_sub_le (frobKernel D 1)
          (frobKernel D 1 - frobKernel D (Multiplicative.ofAdd ((L * k : ℕ) : ℤ)))
        rwa [sub_sub_cancel] at this
      rw [frobKernel_one, Complex.norm_natCast] at h3
      rw [← hK, one_pow, mul_one]
      linarith
    have hle : ∀ i, ‖D.β i‖ ≤ 1 := fun i => by
      have h := RHTower.WeilKloosterman.norm_le_of_power_sums_bound univ (fun i => D.β i ^ L)
        (m0 := 0) zero_le_one (fun m _ => hbound m) i (mem_univ i)
      rw [norm_pow] at h
      exact (pow_le_one_iff_of_nonneg (norm_nonneg _) hL.ne').mp h
    intro i
    have hfe := congrArg norm (D.β_fePerm i)
    rw [norm_mul, norm_one] at hfe
    have hi := hle i
    have hf := hle (D.fePerm i)
    nlinarith [norm_nonneg (D.β i), norm_nonneg (D.β (D.fePerm i))]

/-- **Calibration.** Bounded coupling of two Frobenius towers is Castelnuovo–Severi on the Frobenius
span of the curve. -/
theorem spanHodgeIndex_iff_bounded_tower_coupling {d₁ d₂ : ℕ} (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    (∀ S d, 0 ≤ D.spanDefect S d) ↔ ∃ M : ℝ, ∀ a b : ℤ,
      ‖coupling (frobKernel D) (Multiplicative.ofAdd ((d₁ : ℤ) * a))
        (Multiplicative.ofAdd ((d₂ : ℤ) * b))‖ ≤ M := by
  rw [← unitary_iff_bounded_tower_coupling D h₁ h₂]
  exact ((ArithmeticPositiveDuality.CurveDatum'.curve_rh_tfae D).out 4 0)

/-- **The golden fake curve fails the calibration** on every pair of towers. -/
theorem not_bounded_tower_coupling_golden {d₁ d₂ : ℕ} (h₁ : 0 < d₁) (h₂ : 0 < d₂) :
    ¬∃ M : ℝ, ∀ a b : ℤ,
      ‖coupling (frobKernel goldenDatum) (Multiplicative.ofAdd ((d₁ : ℤ) * a))
        (Multiplicative.ofAdd ((d₂ : ℤ) * b))‖ ≤ M := by
  rw [← unitary_iff_bounded_tower_coupling goldenDatum h₁ h₂]
  intro h
  have h0 := h 0
  have hφ : goldenDatum.β 0 = ((goldenRatio : ℝ) : ℂ) := rfl
  rw [hφ, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.goldenRatio_pos] at h0
  exact (ne_of_gt Real.one_lt_goldenRatio) h0

end GaloisForLFunctions.ArithmeticCouplingTheory
