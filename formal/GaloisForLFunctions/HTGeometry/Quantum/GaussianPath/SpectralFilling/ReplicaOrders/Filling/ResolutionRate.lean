import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.Filling.FrozenChain
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralJets.Detuning.AllHeights.Growth

/-! # Inverse-precision dependence of the measured phase-filling clock -/
open Real
namespace GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
open SpectralJets.AllHeights
open private discount discount_pos from
  GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralFilling.ReplicaOrders.Filling.PolynomialOrder
noncomputable section

private def orderPrefactor (D : ℕ) : ℝ := (D:ℝ)*(4*(D:ℝ)^2*((D:ℝ)+1)/discount+2)+1

private theorem order_rate {D : ℕ} (hD : 0 < D) {ε : ℝ} (hε : 0 < ε) (h₁ : ε ≤ 1) :
    (alignmentOrder D ε:ℝ)+1 ≤ orderPrefactor D*(ε⁻¹)^4 := by
  let η := ε^2/(2*(D:ℝ))
  let b := 4*(D:ℝ)^2*((D:ℝ)+1)/discount
  have hd : 0 < (D:ℝ) := by exact_mod_cast hD
  have hx : 1 ≤ (ε⁻¹)^4 := one_le_pow₀ ((one_le_inv₀ hε).mpr h₁)
  have hn : 0 ≤ ((D:ℝ)+1)/(discount*η^2) := div_nonneg (by positivity) (mul_nonneg discount_pos.le (sq_nonneg _))
  have he : ((D:ℝ)+1)/(discount*η^2)=b*(ε⁻¹)^4 := by
    dsimp only [η,b]
    field_simp [hd.ne',hε.ne',discount_pos.ne']
    ring
  have hh := (Nat.ceil_lt_add_one hn).le
  rw [he] at hh
  change ((D*(⌈((D:ℝ)+1)/(discount*η^2)⌉₊+1):ℕ):ℝ)+1 ≤ _
  rw [he]
  push_cast
  have hd' := mul_le_mul_of_nonneg_left (add_le_add_right hh 1) hd.le
  change _ ≤ ((D:ℝ)*(b+2)+1)*(ε⁻¹)^4
  linarith only [hd',mul_le_mul_of_nonneg_left hx (show 0 ≤ 2*(D:ℝ)+1 by positivity)]

/-- One deterministic prefix prefactor suffices for all tolerances.
The inverse-precision exponent is four times the all-height exponent. -/
theorem alignment_length_polynomial (k : ℕ) :
    let D := 2^(k+3)
    let L := (D+1)*(D-2)
    ∃ C > (0:ℝ), ∀ E : Level k → ℝ, ∀ ε > (0:ℝ), ε ≤ 1 →
      alignmentLength k E ε ≤ C*(ε⁻¹)^(4*L) := by
  intro D L
  let A := orderPrefactor D
  have hD : 0 < D := by dsimp only [D]; positivity
  have hA : 0 < A := by
    dsimp only [A,orderPrefactor]
    have := discount_pos
    positivity
  refine ⟨4*π*(heightMargin k 0)⁻¹*A^L,by have := heightMargin_pos k 0; positivity,?_⟩
  intro E ε hε h₁
  let q := alignmentOrder D ε
  have hgap : (recordGap k E q)⁻¹ ≤ (heightMargin k q)⁻¹ :=
    inv_anti₀ (heightMargin_pos k q) ((le_max_right ..).trans (le_max_left ..))
  have hq : (q:ℝ)+1 ≤ A*(ε⁻¹)^4 := order_rate hD hε h₁
  have hheight := inverse_height_polynomial k q
  have hscale := pow_le_pow_left₀ (by positivity : 0 ≤ (q:ℝ)+1) hq L
  rw [alignmentLength,min_eq_left h₁,div_eq_mul_inv]
  apply (mul_le_mul_of_nonneg_left (hgap.trans (hheight.trans (mul_le_mul_of_nonneg_left hscale
    (inv_nonneg.mpr (heightMargin_pos k 0).le)))) (by positivity)).trans_eq
  rw [mul_pow,pow_mul]
  ring

#print axioms alignment_length_polynomial
end
end GaloisForLFunctions.HTGeometry.SpectralFilling.ReplicaOrders
