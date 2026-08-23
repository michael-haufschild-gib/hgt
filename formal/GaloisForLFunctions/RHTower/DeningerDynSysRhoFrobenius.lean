import GaloisForLFunctions.RHTower.DeningerDynSysTwistedNorm
import GaloisForLFunctions.RHTower.DeningerDynSysPointedMultiplicativeRoot

/-!
# Deninger's `ρ` and its Frobenius law

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), equations (41)–(43).

For a character `P` of the units of an algebraically closed field, the torsion part of the kernel
of `P ∘ ( )^ν` is an extension of the torsion part of the kernel of `P` by the `ν`-th roots of
unity: the `ν`-th power map is surjective on torsion because the field is algebraically closed.
Hence `ρ (F_ν P) = ν_x · ρ (P)`, where `ν_x` is the prime-to-characteristic part of `ν`.
-/

namespace RHTower

open MonoidHom

universe u

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Type u} [Field C]

/-- **Deninger, equation (41).**  The torsion part of the kernel of a character. -/
def deningerTorsionKernel (P : Kˣ →* Cˣ) : Subgroup Kˣ :=
  P.ker ⊓ CommGroup.torsion Kˣ

omit [IsAlgClosed K] in
theorem deningerMem_torsionKernel {P : Kˣ →* Cˣ} {y : Kˣ} :
    y ∈ deningerTorsionKernel P ↔ P y = 1 ∧ IsOfFinOrder y := Iff.rfl

/-- The `ν`-th power map from the torsion kernel of `F_ν P` to that of `P`. -/
def deningerTorsionKernelPow (P : Kˣ →* Cˣ) (ν : ℕ) :
    ↥(deningerTorsionKernel (P.comp (powMonoidHom ν))) →* ↥(deningerTorsionKernel P) :=
  MonoidHom.codRestrict
    ((powMonoidHom ν).comp (deningerTorsionKernel (P.comp (powMonoidHom ν))).subtype)
    (deningerTorsionKernel P)
    (fun y => ⟨y.2.1, y.2.2.pow⟩)

omit [IsAlgClosed K] in
@[simp] theorem deningerTorsionKernelPow_val (P : Kˣ →* Cˣ) (ν : ℕ)
    (y : ↥(deningerTorsionKernel (P.comp (powMonoidHom ν)))) :
    ((deningerTorsionKernelPow P ν y : ↥(deningerTorsionKernel P)) : Kˣ) = (y : Kˣ) ^ ν := rfl

theorem deningerTorsionKernelPow_surjective (P : Kˣ →* Cˣ) {ν : ℕ} (hν : 0 < ν) :
    Function.Surjective (deningerTorsionKernelPow P ν) := by
  intro z
  obtain ⟨y, hy⟩ := deningerUnits_divisible (z : Kˣ) ν hν
  have hz : IsOfFinOrder (z : Kˣ) := z.2.2
  obtain ⟨n, hn, hzn⟩ := isOfFinOrder_iff_pow_eq_one.1 hz
  have hyfin : IsOfFinOrder y := by
    refine isOfFinOrder_iff_pow_eq_one.2 ⟨ν * n, by positivity, ?_⟩
    rw [pow_mul, hy, hzn]
  have hmem : y ∈ deningerTorsionKernel (P.comp (powMonoidHom ν)) := by
    refine ⟨?_, hyfin⟩
    show P (y ^ ν) = 1
    rw [hy]
    exact z.2.1
  refine ⟨⟨y, hmem⟩, ?_⟩
  refine Subtype.ext ?_
  rw [deningerTorsionKernelPow_val]
  exact hy

/-- The kernel of the `ν`-th power map is the group of `ν`-th roots of unity. -/
def deningerTorsionKernelPowKerEquiv (P : Kˣ →* Cˣ) {ν : ℕ} (hν : 0 < ν) :
    ↥(deningerTorsionKernelPow P ν).ker ≃* ↥(rootsOfUnity ν K) where
  toFun y := ⟨((y : ↥(deningerTorsionKernel (P.comp (powMonoidHom ν)))) : Kˣ), by
    rw [mem_rootsOfUnity]
    have h := y.2
    have h' : ((deningerTorsionKernelPow P ν y : ↥(deningerTorsionKernel P)) : Kˣ) = 1 := by
      rw [show (deningerTorsionKernelPow P ν (y : _)) = 1 from h]
      rfl
    rw [deningerTorsionKernelPow_val] at h'
    exact h'⟩
  invFun ζ := ⟨⟨(ζ : Kˣ), by
      refine ⟨?_, ?_⟩
      · show P ((ζ : Kˣ) ^ ν) = 1
        rw [(mem_rootsOfUnity ν (ζ : Kˣ)).1 ζ.2, map_one]
      · exact isOfFinOrder_iff_pow_eq_one.2 ⟨ν, hν, (mem_rootsOfUnity ν (ζ : Kˣ)).1 ζ.2⟩⟩, by
      show deningerTorsionKernelPow P ν _ = 1
      refine Subtype.ext ?_
      rw [deningerTorsionKernelPow_val]
      exact (mem_rootsOfUnity ν (ζ : Kˣ)).1 ζ.2⟩
  left_inv := by intro y; rfl
  right_inv := by intro ζ; rfl
  map_mul' := by intro a b; rfl

/-- **Deninger, equation (42).**  The torsion kernel of `F_ν P` is an extension of the torsion
kernel of `P` by the `ν`-th roots of unity. -/
theorem deningerTorsionKernel_card_pow (P : Kˣ →* Cˣ) {ν : ℕ} (hν : 0 < ν) :
    Nat.card ↥(deningerTorsionKernel (P.comp (powMonoidHom ν)))
      = Nat.card ↥(rootsOfUnity ν K) * Nat.card ↥(deningerTorsionKernel P) := by
  have hsurj := deningerTorsionKernelPow_surjective P hν
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup
    (deningerTorsionKernelPow P ν).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hsurj).toEquiv,
    Nat.card_congr (deningerTorsionKernelPowKerEquiv P hν).toEquiv, mul_comm] at hcard
  exact hcard

/-- **Deninger, equation (43), positive characteristic.**  `ρ (F_ν P) = ν_x · ρ (P)` with `ν_x`
the prime-to-`p` part of `ν`. -/
theorem deningerTorsionKernel_card_pow_charP {p : ℕ} [Fact p.Prime] [CharP K p]
    (P : Kˣ →* Cˣ) {ν : ℕ} (hν : 0 < ν) :
    Nat.card ↥(deningerTorsionKernel (P.comp (powMonoidHom ν)))
      = ordCompl[p] ν * Nat.card ↥(deningerTorsionKernel P) := by
  rw [deningerTorsionKernel_card_pow P hν,
    deningerCard_rootsOfUnity_charP (K := K) (N := ν) hν.ne']

/-- **Deninger, equation (43), characteristic zero.**  `ρ (F_ν P) = ν · ρ (P)`. -/
theorem deningerTorsionKernel_card_pow_charZero [CharZero K]
    (P : Kˣ →* Cˣ) {ν : ℕ} (hν : 0 < ν) :
    Nat.card ↥(deningerTorsionKernel (P.comp (powMonoidHom ν)))
      = ν * Nat.card ↥(deningerTorsionKernel P) := by
  rw [deningerTorsionKernel_card_pow P hν,
    deningerCard_rootsOfUnity_charZero (K := K) (N := ν) hν.ne']

end RHTower
