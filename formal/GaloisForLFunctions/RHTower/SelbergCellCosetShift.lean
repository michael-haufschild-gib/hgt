import GaloisForLFunctions.RHTower.SelbergTruncationIdentity

open MeasureTheory UpperHalfPlane ModularGroup Set
open scoped MatrixGroups Pointwise

/-!
# The `Γ(N)` cell as translates of the modular cell, and the right `T`-shift of its cosets

`∫_{cellP} F = ∫_𝒟 Σ_c F(R_c w)` over the right cosets `c ∈ Γ̄(N)\PSL(2,ℤ)` with representatives `R_c`
(`integral_cellP_eq`). Right multiplication by `T` permutes the cosets (`shEquiv`), and for `Γ(N)`-invariant `F`
it shifts the argument: `F(R_{cT} w) = F(R_c(w + 1))` (`F_out_sh`), while `F(R_c(w + N)) = F(R_c w)` by normality
of `Γ(N)` (`F_out_periodic`). Summing a `T`-invariant weight over the cosets therefore turns the `N` width-one
pieces of a cusp into one full period of width `N`: the averaging behind the constant terms in the
Maass–Selberg relation.
-/

namespace GaloisForLFunctions.RHTower.SelbergCellCosetShift
open GaloisForLFunctions.HTGeometry GaloisForLFunctions.RHTower.SarnakXuePretrace
  GaloisForLFunctions.RHTower.SelbergPoincareUnfolding
open CongruenceSubgroup

variable (N : ℕ)

/-- `∫_{cellP} F = ∫_𝒟 Σ_c F(R_c w)`. -/
theorem integral_cellP_eq {F : ℍ → ℂ} (hF : IntegrableOn F (cellP N)) :
    ∫ z in cellP N, F z = ∫ w in fd, ∑' c : Cosets N, F ((Quotient.out c : PSL2Z) • w) := by
  have hinj : Function.Injective (fun c : Cosets N => (Quotient.out c : PSL2Z)) := by
    intro c c' h
    rw [← Quotient.out_eq c, ← Quotient.out_eq c']
    simp only at h
    rw [h]
  exact integral_iUnion_eq_integral_tsum isFundamentalDomain_fd hinj hF

/-- `Γ(N)`-invariant functions are invariant under `Γ̄(N)`. -/
theorem inv_gammaBar {F : ℍ → ℂ} (hF : ∀ (γ : Gamma N) z, F ((γ : SL(2, ℤ)) • z) = F z)
    (h : gammaBar N) (z : ℍ) : F ((h : PSL2Z) • z) = F z := by
  obtain ⟨γ, hγ, e⟩ := Subgroup.mem_map.mp h.2
  rw [← e]
  show F ((QuotientGroup.mk γ : PSL2Z) • z) = F z
  rw [PSL2Z_mk_smul]
  exact hF ⟨γ, hγ⟩ z

/-- The image of `T` in `PSL(2, ℤ)`. -/
noncomputable abbrev Tbar : PSL2Z := QuotientGroup.mk T

/-- Right translation of cosets by `T`. -/
noncomputable def sh : Cosets N → Cosets N :=
  Quotient.map' (· * Tbar) (fun a b hab => by
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa [mul_assoc] using hab)

noncomputable def shInv : Cosets N → Cosets N :=
  Quotient.map' (· * Tbar⁻¹) (fun a b hab => by
    rw [QuotientGroup.rightRel_apply] at hab ⊢
    simpa [mul_assoc] using hab)

/-- Right translation by `T` is a permutation of the cosets. -/
noncomputable def shEquiv : Cosets N ≃ Cosets N where
  toFun := sh N
  invFun := shInv N
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h a => show Quotient.mk _ (a * Tbar * Tbar⁻¹) = Quotient.mk _ a; rw [mul_inv_cancel_right]
  right_inv c := by
    induction c using Quotient.inductionOn with
    | h a => show Quotient.mk _ (a * Tbar⁻¹ * Tbar) = Quotient.mk _ a; rw [inv_mul_cancel_right]

theorem out_sh (c : Cosets N) :
    ∃ h : gammaBar N, (Quotient.out (sh N c) : PSL2Z) = (h : PSL2Z) * ((Quotient.out c : PSL2Z) * Tbar) := by
  have hc : QuotientGroup.rightRel (gammaBar N) (Quotient.out (sh N c)) (Quotient.out c * Tbar) := by
    have : sh N c = Quotient.mk _ (Quotient.out c * Tbar) := by
      conv_lhs => rw [← Quotient.out_eq c]
      rfl
    exact Quotient.exact (by rw [Quotient.out_eq, this])
  rw [QuotientGroup.rightRel_apply] at hc
  refine ⟨⟨_, inv_mem hc⟩, ?_⟩
  simp only [mul_inv_rev, inv_inv]
  group

/-- **Shift**: `F(R_{cT} w) = F(R_c (w + 1))` for `Γ(N)`-invariant `F`. -/
theorem F_out_sh {F : ℍ → ℂ} (hF : ∀ (γ : Gamma N) z, F ((γ : SL(2, ℤ)) • z) = F z) (c : Cosets N) (w : ℍ) :
    F ((Quotient.out (sh N c) : PSL2Z) • w) = F ((Quotient.out c : PSL2Z) • (T • w)) := by
  obtain ⟨h, e⟩ := out_sh N c
  rw [e, mul_smul, inv_gammaBar N hF, mul_smul, PSL2Z_mk_smul]

/-- **Periodicity**: `F(R_c (w + N)) = F(R_c w)` for `Γ(N)`-invariant `F`. -/
theorem F_out_periodic {F : ℍ → ℂ} (hF : ∀ (γ : Gamma N) z, F ((γ : SL(2, ℤ)) • z) = F z) (c : Cosets N) (w : ℍ) :
    F ((Quotient.out c : PSL2Z) • ((T ^ (N : ℤ)) • w)) = F ((Quotient.out c : PSL2Z) • w) := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (Quotient.out c : PSL2Z)
  rw [← hg, PSL2Z_mk_smul, PSL2Z_mk_smul, ← mul_smul]
  have hmem : g * T ^ (N : ℤ) * g⁻¹ ∈ Gamma N := (Gamma_normal N).conj_mem _ (GaloisForLFunctions.RHTower.SelbergPoincare.T_pow_mem N) g
  have : g * T ^ (N : ℤ) = (g * T ^ (N : ℤ) * g⁻¹) * g := by group
  rw [this, mul_smul]
  exact hF ⟨_, hmem⟩ _

end GaloisForLFunctions.RHTower.SelbergCellCosetShift
