/-
# Barrier: unipotent Fitting seam is invisible to every additive deck charge

The M⁺ torsion-seam layer supplies live Fitting boundary classes for cutoff-crossing
(unipotent) defects (`exists_nonfake_crossBoundary`, `fittingClass_seamDef_ne_zero`).  The ladder
supplies additive deck charges `wCharge n : ℤ → ZMod n`.  A natural hope is that some additive
functional of the Fitting jet algebra recovers a nontrivial deck charge — reading monodromy off the
seam cochain.

That route is **dead** for a coefficient reason, not an estimate:

* Fitting classes of the standard unipotent seam defects `seamDef t` lie on the **constant-jet line**
  `t ↦ jetClass(C t) ≅ ℚ` inside `LocalDivisorJet ℚ m`;
* every additive map `ℚ →+ ZMod n` is zero (`Hom(ℚ, ℤ/n) = 0`: divisible source, bounded-exponent
  target);
* therefore every additive `ψ : LocalDivisorJet ℚ m →+ ZMod n` vanishes on all unipotent Fitting
  classes — including the live nonzero class at `t = 1`.

So no additive jet charge can both (i) see the live unipotent Fitting defect and (ii) return a
nontrivial deck residue.  Deck monodromy and unipotent Fitting seam are not merely independent free
parameters of a gluing: the Fitting face is **structurally invisible** to the entire additive deck-charge
channel.

## Dual-gate note
Not packaging of free `(s,t)` gluing, prime-flux collapse, `{1}∪{log p}`, apex packaging, or RH TFAE.
The banked non-identification is “unipotent ≠ torsion root by exponentiation” (`CutoffCochain` §6).
This file is the **charge-channel barrier**: every additive `ZMod n`-valued reading of the Fitting jet
kills the unipotent seam face.  Classical input is `Hom(ℚ,ℤ/n)=0`; the new claim is the program
barrier for the M⁺ monodromy-from-Fitting route.
-/
import GaloisForLFunctions.RHTower.LiftedGluingFaces
import GaloisForLFunctions.RHTower.DeckChargeCalculus

noncomputable section

namespace RHTower

open Polynomial

/-! ### §1 `Hom(ℚ, ℤ/n) = 0` -/

/-- **Every additive map `ℚ →+ ZMod n` is zero.**  For any `q`, `q = n · (q/n)`, so
`φ q = n • φ(q/n) = 0` by the characteristic of `ZMod n`. -/
theorem addHom_rat_zmod_eq_zero {n : ℕ} [NeZero n] (φ : ℚ →+ ZMod n) (q : ℚ) : φ q = 0 := by
  have hn : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hq : q = n • (q / n) := by
    rw [nsmul_eq_mul, mul_div_cancel₀ q hn]
  rw [hq, map_nsmul, ZModModule.char_nsmul_eq_zero]

/-! ### §2 Constant jets as an additive line `ℚ ↪ LocalDivisorJet` -/

/-- Constant polynomials as an additive homomorphism into the local divisor-jet algebra. -/
def constJetHom (m : ℕ) : ℚ →+ LocalDivisorJet ℚ m where
  toFun t := jetClass ℚ m (C t)
  map_zero' := by
    simp [jetClass, map_zero]
  map_add' a b := by
    change jetClass ℚ m (C (a + b)) = jetClass ℚ m (C a) + jetClass ℚ m (C b)
    have hC : (C (a + b) : ℚ[X]) = C a + C b := map_add C a b
    rw [jetClass, jetClass, jetClass, hC, map_add]

@[simp] theorem constJetHom_apply (m : ℕ) (t : ℚ) :
    constJetHom m t = jetClass ℚ m (C t) := rfl

/-- The Fitting class of `seamDef t` is the constant jet of `-t`. -/
theorem fittingClass_seamDef_eq_neg_constJet (m : ℕ) (t : ℚ) :
    fittingBoundaryClass m (standardPres m) (seamDef t) = -constJetHom m t := by
  rw [fittingClass_seamDef, constJetHom_apply, jetClass]
  -- jetClass (-C t) = - jetClass (C t)
  have h : (-C t : ℚ[X]) = -(C t) := by simp
  rw [h]
  exact (map_neg (Ideal.Quotient.mk (jetIdeal ℚ m)) (C t)).symm

/-! ### §3 Barrier: every additive jet charge kills unipotent Fitting -/

/-- **Unipotent Fitting is invisible to additive deck charges.**  Any additive
`ψ : LocalDivisorJet ℚ m →+ ZMod n` vanishes on every Fitting class of `seamDef t`. -/
theorem fitting_seamDef_charge_eq_zero {m n : ℕ} [NeZero n]
    (ψ : LocalDivisorJet ℚ m →+ ZMod n) (t : ℚ) :
    ψ (fittingBoundaryClass m (standardPres m) (seamDef t)) = 0 := by
  rw [fittingClass_seamDef_eq_neg_constJet, map_neg, neg_eq_zero]
  -- ψ ∘ constJetHom : ℚ →+ ZMod n is zero
  exact addHom_rat_zmod_eq_zero (ψ.comp (constJetHom m)) t

/-- **Live Fitting is still invisible.**  Even the nonzero class at `t = 1` (`m ≥ 1`) maps to `0`
under every additive `ZMod n` charge. -/
theorem live_fitting_seamDef_charge_eq_zero {m n : ℕ} [NeZero n]
    (ψ : LocalDivisorJet ℚ m →+ ZMod n) :
    ψ (fittingBoundaryClass m (standardPres m) (seamDef 1)) = 0 :=
  fitting_seamDef_charge_eq_zero ψ 1

/-! ### §4 No additive recovery of nontrivial deck charge from unipotent Fitting -/

/-- **Barrier capstone.**  There is no additive jet charge `ψ` and index `idx` such that
`ψ(Fitting(seamDef t)) = wCharge n idx` for all `t` with the charge nontrivial: any additive `ψ`
returns `0` on all unipotent Fitting classes, while a nontrivial deck charge is nonzero. -/
theorem not_exists_addHom_fitting_eq_nontrivial_wCharge {m n : ℕ} [NeZero n]
    {idx : ℤ} (hne : _root_.RHTower.wCharge n idx ≠ 0) :
    ¬ ∃ ψ : LocalDivisorJet ℚ m →+ ZMod n,
        ∀ t : ℚ, ψ (fittingBoundaryClass m (standardPres m) (seamDef t)) =
          _root_.RHTower.wCharge n idx := by
  rintro ⟨ψ, hψ⟩
  have hL : ψ (fittingBoundaryClass m (standardPres m) (seamDef 0)) = 0 :=
    fitting_seamDef_charge_eq_zero ψ 0
  have hR := hψ 0
  exact hne (by rw [← hR, hL])

/-- Stronger pointwise form: no additive `ψ` can send the live Fitting class at `t = 1` to a
nontrivial deck charge. -/
theorem not_exists_addHom_live_fitting_eq_nontrivial_wCharge {m n : ℕ} [NeZero n]
    {idx : ℤ} (hne : _root_.RHTower.wCharge n idx ≠ 0) :
    ¬ ∃ ψ : LocalDivisorJet ℚ m →+ ZMod n,
        ψ (fittingBoundaryClass m (standardPres m) (seamDef 1)) =
          _root_.RHTower.wCharge n idx := by
  rintro ⟨ψ, hψ⟩
  have h0 := live_fitting_seamDef_charge_eq_zero (n := n) ψ
  exact hne (by rw [← hψ, h0])

/-- **Program consequence.**  The route “read a nontrivial ladder/deck charge as an additive
functional of the unipotent Fitting seam face” is empty: every candidate functional is identically
zero on that face. -/
theorem unipotent_fitting_route_to_deck_charge_empty {m n : ℕ} [NeZero n] :
    ∀ ψ : LocalDivisorJet ℚ m →+ ZMod n,
      ∀ t : ℚ, ψ (fittingBoundaryClass m (standardPres m) (seamDef t)) = 0 :=
  fun ψ t => fitting_seamDef_charge_eq_zero ψ t

end RHTower
