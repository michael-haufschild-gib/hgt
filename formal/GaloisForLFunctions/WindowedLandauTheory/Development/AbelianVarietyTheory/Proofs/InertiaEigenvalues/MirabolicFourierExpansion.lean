import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicCoordinates
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColumnFourierTrace

/-! Fourier inversion in the last column splits a mirabolic class function
into the zero-frequency mean and the average of its last-coordinate
coefficient over the nonzero covectors. -/

noncomputable section
open Matrix
open scoped Classical

namespace GlobalTheory.GLq

variable {g m : ℕ} [Fact g.Prime]

/-- Conjugation invariance on the standard mirabolic subgroup. -/
def IsMirabolicClass (F : Gn g (m + 1) → ℂ) : Prop :=
  ∀ x ∈ mirabolicSubgroup g m, ∀ y ∈ mirabolicSubgroup g m, F (y * x * y⁻¹) = F x

theorem IsClass.isMirabolicClass {F : Gn g (m + 1) → ℂ} (hF : IsClass F) :
    IsMirabolicClass F := fun x _ y _ => hF x y

/-- The Fourier coefficient of the last column at a fixed leading block. -/
def mirabolicFourier (ψ : AddChar (ZMod g) ℂ) (F : Gn g (m + 1) → ℂ)
    (A : Gn g m) (r : Fin m → ZMod g) : ℂ :=
  columnFourier ψ (fun v => F (mirabolicBlock A v)) r

theorem mirabolicFourier_conj (ψ : AddChar (ZMod g) ℂ)
    {F : Gn g (m + 1) → ℂ} (hF : IsMirabolicClass F)
    (A B : Gn g m) (r : Fin m → ZMod g) :
    mirabolicFourier ψ F (B * A * B⁻¹) r = mirabolicFourier ψ F A (r ᵥ* B.val) := by
  have he (v : Fin m → ZMod g) :
      F (mirabolicBlock (B * A * B⁻¹) (B.val.mulVec v)) = F (mirabolicBlock A v) := by
    have h := hF _ (mirabolicBlock_mem A v) _ (mirabolicBlock_mem B 0)
    rw [mirabolicBlock_conj, Matrix.mulVec_zero, add_zero, sub_zero] at h
    exact h
  unfold mirabolicFourier
  have h := columnFourier_mulVec ψ (fun v => F (mirabolicBlock (B * A * B⁻¹) v))
    B (r ᵥ* B.val)
  rw [vecMul_vecMul, B.val_inv, vecMul_one, funext he] at h
  exact h.symm

/-- Only the covectors fixed by the leading block can have nonzero coefficient. -/
theorem mirabolicFourier_eq_zero_of_not_fixed (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1)
    {F : Gn g (m + 1) → ℂ} (hF : IsMirabolicClass F)
    (A : Gn g m) (r : Fin m → ZMod g) (hr : r ᵥ* A.val ≠ r) :
    mirabolicFourier ψ F A r = 0 := by
  by_contra hne
  apply hr
  funext i
  let w : Fin m → ZMod g := Pi.single i 1
  have hshift (v : Fin m → ZMod g) :
      F (mirabolicBlock A ((w - A.val.mulVec w) + v)) = F (mirabolicBlock A v) := by
    have h := hF _ (mirabolicBlock_mem A v) _ (mirabolicBlock_mem (1 : Gn g m) w)
    rw [mirabolicBlock_conj, one_mul, inv_one, mul_one, Units.val_one, Matrix.one_mulVec] at h
    simpa only [sub_add_eq_add_sub, add_comm w v] using h
  have hz := dot_eq_zero_of_columnFourier_ne_zero ψ hψ
    (fun v => F (mirabolicBlock A v)) r (w - A.val.mulVec w) hshift hne
  rw [dotProduct_sub, dotProduct_mulVec, sub_eq_zero] at hz
  simpa only [w, dotProduct_single_one] using hz.symm

theorem mirabolicFourier_last_isMirabolicClass (ψ : AddChar (ZMod g) ℂ)
    {F : Gn g (m + 2) → ℂ} (hF : IsMirabolicClass F) :
    IsMirabolicClass (fun A : Gn g (m + 1) => mirabolicFourier ψ F A (Pi.single (Fin.last m) 1)) := by
  intro A _ B hB
  change mirabolicFourier ψ F (B * A * B⁻¹) (Pi.single (Fin.last m) 1) =
    mirabolicFourier ψ F A (Pi.single (Fin.last m) 1)
  rw [mirabolicFourier_conj ψ hF]
  exact congrArg (mirabolicFourier ψ F A) hB

private theorem sum_over_rows (φ : (Fin (m + 1) → ZMod g) → ℂ) :
    (∑ B : Gn g (m + 1), φ (Pi.single (Fin.last m) 1 ᵥ* B.val)) =
      (Nat.card (mirabolicSubgroup g m) : ℂ) * ∑ r, if r = 0 then 0 else φ r := by
  let r₀ : Fin (m + 1) → ZMod g := Pi.single (Fin.last m) 1
  let ρ (B : Gn g (m + 1)) := r₀ ᵥ* B.val
  have hn : r₀ ≠ 0 := by
    intro h
    have e := congrFun h (Fin.last m)
    exact one_ne_zero (by simpa only [r₀, Pi.single_eq_same, Pi.zero_apply] using e)
  have hρ (B : Gn g (m + 1)) : ρ B ≠ 0 := by
    intro h
    apply hn
    have he := congrArg (fun r : Fin (m + 1) → ZMod g => r ᵥ* B.inv) h
    simpa only [ρ, vecMul_vecMul, B.val_inv, vecMul_one, zero_vecMul] using he
  have hex (r : Fin (m + 1) → ZMod g) (hr : r ≠ 0) : ∃ B, ρ B = r := by
    obtain ⟨B, hB⟩ := exists_GL_with_row (Fin.last m) r hr
    refine ⟨B, funext fun i => ?_⟩
    simpa only [ρ, r₀, vecMul, single_dotProduct, one_mul] using hB i
  have hc : (∑ B : Gn g (m + 1), if B ∈ mirabolicSubgroup g m then (1 : ℂ) else 0) =
      (Nat.card (mirabolicSubgroup g m) : ℂ) := by
    rw [← Finset.natCast_card_filter, Nat.card_eq_fintype_card, Fintype.card_subtype]
  change (∑ B : Gn g (m + 1), φ (ρ B)) = _
  rw [← hc, Finset.mul_sum, ← Finset.sum_fiberwise Finset.univ ρ]
  refine Finset.sum_congr rfl fun r _ => ?_
  by_cases hr : r = 0
  · rw [if_pos hr, mul_zero]
    apply Finset.sum_eq_zero
    intro B hB
    exact (hρ B ((Finset.mem_filter.mp hB).2.trans hr)).elim
  · obtain ⟨B₀, hB₀⟩ := hex r hr
    rw [if_neg hr, Finset.sum_filter, Finset.sum_mul, ← Equiv.sum_comp (Equiv.mulRight B₀)]
    refine Finset.sum_congr rfl fun B _ => ?_
    have hiff : ρ (B * B₀) = r ↔ B ∈ mirabolicSubgroup g m := by
      change r₀ ᵥ* (B.val * B₀.val) = r ↔ r₀ ᵥ* B.val = r₀
      rw [← hB₀, ← vecMul_vecMul]
      refine ⟨fun h => ?_, fun h => congrArg (fun t => t ᵥ* B₀.val) h⟩
      simpa only [ρ, vecMul_vecMul _ B₀.val B₀.inv, B₀.val_inv, vecMul_one] using
        congrArg (fun t : Fin (m + 1) → ZMod g => t ᵥ* B₀.inv) h
    change (if ρ (B * B₀) = r then φ (ρ (B * B₀)) else 0) = _
    by_cases hB : B ∈ mirabolicSubgroup g m
    · rw [if_pos hB, one_mul, if_pos (hiff.mpr hB), hiff.mpr hB]
    · rw [if_neg hB, zero_mul, if_neg (fun h => hB (hiff.mp h))]

/-- Expanding a mirabolic class function separates the untwisted column mean
from the induced contribution of a single nonzero covector. -/
theorem mirabolicBlock_eq_fourier_average (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1)
    {F : Gn g (m + 2) → ℂ} (hF : IsMirabolicClass F)
    (A : Gn g (m + 1)) (v : Fin (m + 1) → ZMod g) :
    F (mirabolicBlock A v) = mirabolicFourier ψ F A 0 +
      (Nat.card (mirabolicSubgroup g m) : ℂ)⁻¹ * ∑ B : Gn g (m + 1),
        if B * A * B⁻¹ ∈ mirabolicSubgroup g m then
          mirabolicFourier ψ F (B * A * B⁻¹) (Pi.single (Fin.last m) 1) *
            ψ ((Pi.single (Fin.last m) 1 : Fin (m + 1) → ZMod g) ⬝ᵥ B.val.mulVec v)
        else 0 := by
  let r₀ : Fin (m + 1) → ZMod g := Pi.single (Fin.last m) 1
  let φ (r : Fin (m + 1) → ZMod g) := mirabolicFourier ψ F A r * ψ (r ⬝ᵥ v)
  have he (B : Gn g (m + 1)) :
      (if B * A * B⁻¹ ∈ mirabolicSubgroup g m then mirabolicFourier ψ F (B * A * B⁻¹) r₀ *
        ψ (r₀ ⬝ᵥ B.val.mulVec v) else 0) = φ (r₀ ᵥ* B.val) := by
    have hiff : B * A * B⁻¹ ∈ mirabolicSubgroup g m ↔ (r₀ ᵥ* B.val) ᵥ* A.val = r₀ ᵥ* B.val := by
      change r₀ ᵥ* ((B.val * A.val) * B.inv) = r₀ ↔ _
      rw [← vecMul_vecMul r₀, ← vecMul_vecMul r₀]
      refine ⟨fun h => ?_, fun h => ?_⟩
      · simpa only [vecMul_vecMul _ B.inv B.val, B.inv_val, vecMul_one] using
          congrArg (fun r : Fin (m + 1) → ZMod g => r ᵥ* B.val) h
      · rw [h, vecMul_vecMul, B.val_inv, vecMul_one]
    split_ifs with h
    · rw [mirabolicFourier_conj ψ hF, dotProduct_mulVec]
    · change 0 = mirabolicFourier ψ F A (r₀ ᵥ* B.val) * ψ ((r₀ ᵥ* B.val) ⬝ᵥ v)
      rw [mirabolicFourier_eq_zero_of_not_fixed ψ hψ hF _ _ (fun e => h (hiff.mpr e)), zero_mul]
  have hcard : (Nat.card (mirabolicSubgroup g m) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  change F (mirabolicBlock A v) = mirabolicFourier ψ F A 0 +
    (Nat.card (mirabolicSubgroup g m) : ℂ)⁻¹ * ∑ B : Gn g (m + 1),
      if B * A * B⁻¹ ∈ mirabolicSubgroup g m then
        mirabolicFourier ψ F (B * A * B⁻¹) r₀ * ψ (r₀ ⬝ᵥ B.val.mulVec v) else 0
  rw [Finset.sum_congr rfl fun B _ => he B, sum_over_rows φ, ← mul_assoc, inv_mul_cancel₀ hcard, one_mul]
  have htotal : (∑ r : Fin (m + 1) → ZMod g, φ r) = F (mirabolicBlock A v) :=
    columnFourier_eval ψ hψ _ v
  rw [← htotal]
  have h₀ : ∑ r : Fin (m + 1) → ZMod g, (if r = 0 then φ r else 0) =
      mirabolicFourier ψ F A 0 := by
    simp [φ]
  rw [← h₀, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun r _ => by split_ifs <;> simp

end GlobalTheory.GLq
