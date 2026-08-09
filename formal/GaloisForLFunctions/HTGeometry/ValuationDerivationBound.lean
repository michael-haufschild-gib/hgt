import GaloisForLFunctions.HTGeometry.TopDegreeSharpDrop

/-!
# From a bound on the valuation ring to a bound on the whole field

A derivation that lowers the order of the elements of a discrete valuation ring by at most `c`
lowers the order of *every* element of the fraction field by at most `c + 1`.  The extra unit comes
from the uniformiser: writing `f = t^k·g` with `g` a unit, the logarithmic derivative splits as

`δf/f = k·(δt/t) + δg/g`,

and multiplying by `t^(c+1)` puts both summands in the ring — the first because `t^c·δt` is there and
one factor `t` is spent on the pole of `1/t`, the second because `t^c·δg` is there and `g⁻¹` is a
unit.  Nothing beyond the unit decomposition of the fraction field is used.

Applied to the coordinate field itself, where the derivation at the uniformiser preserves the
valuation ring outright, this gives the logarithmic form of the degree drop: `u·(δf/f)` is integral
for every nonzero `f`, with `u = 1/X_m`.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-! ## The general propagation -/

/-- **A bound on the valuation ring propagates to the fraction field, at the cost of one unit.** -/
theorem pow_mul_logDeriv_mem {R L : Type*} [CommRing R] [Field L] [Algebra R L]
    (δ : Derivation R L L) (O : Subring L) (t : L) (ht : t ∈ O) (ht0 : t ≠ 0) (c : ℕ)
    (hδ : ∀ b ∈ O, t ^ c * δ b ∈ O)
    (hdec : ∀ f : L, f ≠ 0 → ∃ (k : ℤ) (g : L), g ∈ O ∧ g⁻¹ ∈ O ∧ f = t ^ k * g)
    {f : L} (hf : f ≠ 0) :
    t ^ (c + 1) * (δ f / f) ∈ O := by
  obtain ⟨k, g, hg, hginv, rfl⟩ := hdec f hf
  have hT0 : (t : L) ^ k ≠ 0 := zpow_ne_zero k ht0
  have hg0 : g ≠ 0 := by
    intro h
    rw [h, mul_zero] at hf
    exact hf rfl
  have hz : (t : L) ^ (k - 1) = t ^ k * t⁻¹ := by
    rw [zpow_sub₀ ht0, zpow_one, div_eq_mul_inv]
  have hδf : δ (t ^ k * g) = t ^ k * δ g + g * ((k : L) * ((t ^ k * t⁻¹) * δ t)) := by
    rw [Derivation.leibniz, Derivation.leibniz_zpow, hz]
    simp only [smul_eq_mul, zsmul_eq_mul]
  have key : t ^ (c + 1) * (δ (t ^ k * g) / (t ^ k * g))
      = (k : L) * (t ^ c * δ t) + t * (t ^ c * δ g) * g⁻¹ := by
    rw [hδf]
    field_simp
    ring
  rw [key]
  refine Subring.add_mem _ ?_ ?_
  · rw [← zsmul_eq_mul]
    exact zsmul_mem (hδ t ht) k
  · exact Subring.mul_mem _ (Subring.mul_mem _ ht (hδ g hg)) hginv

/-! ## The unit decomposition of the coordinate field -/

theorem topOrdRep_zpow {m : ℕ} {f : CascadeField} (hf : f ≠ 0) (k : ℤ) :
    topOrdRep m (f ^ k) = k * topOrdRep m f := by
  induction k using Int.induction_on with
  | zero => simp [topOrdRep_one]
  | succ n ih =>
      have h1 : f ^ ((n : ℤ) + 1) = f ^ (n : ℤ) * f := by
        rw [zpow_add₀ hf, zpow_one]
      rw [h1, topOrdRep_mul (zpow_ne_zero _ hf) hf, ih]
      ring
  | pred n ih =>
      have h1 : f ^ (-(n : ℤ) - 1) = f ^ (-(n : ℤ)) * f⁻¹ := by
        rw [zpow_sub₀ hf, zpow_one, div_eq_mul_inv]
      rw [h1, topOrdRep_mul (zpow_ne_zero _ hf) (inv_ne_zero hf), topOrdRep_inv hf, ih]
      ring

theorem topOrdRep_inv_fx_zpow (m : ℕ) (k : ℤ) :
    topOrdRep m (((fx m)⁻¹) ^ k) = k := by
  rw [topOrdRep_zpow (inv_ne_zero (fx_ne_zero m)), topOrdRep_inv_fx, mul_one]

/-- **Every nonzero element of the coordinate field is a power of the uniformiser times a unit.** -/
theorem topInt_unit_decomp (m : ℕ) (f : CascadeField) (hf : f ≠ 0) :
    ∃ (k : ℤ) (g : CascadeField), g ∈ topInt m ∧ g⁻¹ ∈ topInt m
      ∧ f = ((fx m)⁻¹) ^ k * g := by
  refine ⟨topOrdRep m f, f * ((fx m)⁻¹) ^ (-(topOrdRep m f)), ?_, ?_, ?_⟩
  · rw [mem_topInt_iff_rep (mul_ne_zero hf (zpow_ne_zero _ (inv_ne_zero (fx_ne_zero m)))),
      topOrdRep_mul hf (zpow_ne_zero _ (inv_ne_zero (fx_ne_zero m))), topOrdRep_inv_fx_zpow]
    omega
  · have hne : f * ((fx m)⁻¹) ^ (-(topOrdRep m f)) ≠ 0 :=
      mul_ne_zero hf (zpow_ne_zero _ (inv_ne_zero (fx_ne_zero m)))
    rw [mem_topInt_iff_rep (inv_ne_zero hne), topOrdRep_inv hne,
      topOrdRep_mul hf (zpow_ne_zero _ (inv_ne_zero (fx_ne_zero m))), topOrdRep_inv_fx_zpow]
    omega
  · rw [← mul_assoc, mul_comm (((fx m)⁻¹) ^ topOrdRep m f) f, mul_assoc, ← zpow_add₀
      (inv_ne_zero (fx_ne_zero m))]
    simp

/-! ## The logarithmic form of the degree drop -/

/-- **The logarithmic derivative at the uniformiser is integral after one factor of `u`.** -/
theorem inv_fx_mul_logDeriv_uDeriv_mem_topInt {m : ℕ} {f : CascadeField} (hf : f ≠ 0) :
    ((fx m)⁻¹) * (uDeriv m f / f) ∈ topInt m := by
  have h := pow_mul_logDeriv_mem (uDeriv m) (topInt m) ((fx m)⁻¹) (inv_fx_mem_topInt m)
    (inv_ne_zero (fx_ne_zero m)) 0
    (fun b hb => by simpa using uDeriv_mem_topInt hb)
    (topInt_unit_decomp m) hf
  simpa using h

end GaloisForLFunctions.HTGeometry
