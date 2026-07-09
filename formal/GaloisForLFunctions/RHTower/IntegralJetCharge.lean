/-
# Integral repair of the additive deck-charge channel on divisor jets

Over `ℚ`-coefficient jets the additive deck-charge channel is dead for a coefficient reason:
Fitting classes of the standard unipotent seam defects lie on the constant-jet line
`t ↦ jetClass(C t)`, and every additive map `ℚ →+ ZMod n` vanishes (`Hom(ℚ, ℤ/n) = 0`, a divisible
source into a bounded-exponent target).  So every additive functional of the `ℚ` Fitting jet algebra
kills the live unipotent seam face (`FittingDeckChargeBarrier`).

That death is an artifact of **divisibility**, not of the seam geometry.  This module is the mirror
over the **integral** jet lattice `ℤ[X]/(X^m)`.  There the additive charge channel is alive:
constant-coefficient reduction `P mod X^m ↦ (P.coeff 0 : ZMod n)` is a genuine additive `ZMod n`
charge — well defined because `coeff 0` of a multiple of `X^m` vanishes for `m ≥ 1` — and it sends the
standard unipotent Fitting class to a **nonzero** element of `ZMod n`.  Integrality of the coefficient
stream is exactly what re-opens the Fitting-to-deck channel that divisible coefficients close.

The naturality of the two pictures is precisely divisibility vs integrality: base-changing the
integral class along `ℤ → ℚ` lands on the constant-jet line, where every additive `ZMod n` reading is
zero; the integral charge itself is not.  So the integral charge does not factor through the `ℚ` jet
algebra.
-/
import GaloisForLFunctions.RHTower.FittingSeamBoundary

noncomputable section

namespace RHTower

open Matrix Polynomial

/-! ### §1 Integral seam model (`ℤ`-mirror of `standardPres` / `seamDef`) -/

/-- The standard cutoff presentation over `ℤ[X]`: `[[X^m, 1], [0, 1]]`, with `det = X^m`. -/
def standardPresZ (m : ℕ) : Matrix (Fin 2) (Fin 2) (Polynomial ℤ) :=
  !![(X : ℤ[X]) ^ m, 1; 0, 1]

/-- The standard unipotent seam defect over `ℤ[X]`, scaling the lower-left cross entry by `t`. -/
def seamDefZ (t : ℤ) : Matrix (Fin 2) (Fin 2) (Polynomial ℤ) :=
  (C t) • (!![(0 : ℤ[X]), 0; 1, 0])

/-! ### §2 Integral Fitting class of the seam defect lands on the constant-jet line -/

/-- The Fitting boundary trace of the integral seam defect is `-C t` (adjugate first variation). -/
theorem fittingTrace_seamDefZ (m : ℕ) (t : ℤ) :
    fittingBoundaryTrace (standardPresZ m) (seamDefZ t) = -C t := by
  have hadj : (standardPresZ m).adjugate = !![1, -1; 0, (X : ℤ[X]) ^ m] := by
    simp [standardPresZ, Matrix.adjugate_fin_two]
  have hΔ : seamDefZ t = !![0, 0; C t, 0] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [seamDefZ, Matrix.smul_apply]
  unfold fittingBoundaryTrace
  rw [hadj, hΔ, Matrix.mul_fin_two, Matrix.trace_fin_two]
  simp

/-- The integral Fitting class of the standard unipotent seam defect is the constant jet of `-t`;
it lies on the constant-jet line `t ↦ jetClass ℤ m (C t)`. -/
theorem fittingClass_seamDefZ (m : ℕ) (t : ℤ) :
    fittingBoundaryClass m (standardPresZ m) (seamDefZ t) = jetClass ℤ m (-C t) := by
  rw [fittingBoundaryClass, fittingTrace_seamDefZ]

/-! ### §3 The constant-coefficient reduction charge and its nonvanishing -/

/-- Constant-coefficient reduction `P ↦ (P.coeff 0 : ZMod n)` as a ring homomorphism on `ℤ[X]`,
factored as evaluation at `0` followed by reduction `ℤ → ZMod n`. -/
def coeffZeroRingHomZ (n : ℕ) : Polynomial ℤ →+* ZMod n :=
  (Int.castRingHom (ZMod n)).comp (Polynomial.evalRingHom 0)

@[simp] theorem coeffZeroRingHomZ_C (n : ℕ) (t : ℤ) :
    coeffZeroRingHomZ n (C t) = (t : ZMod n) := by
  simp [coeffZeroRingHomZ]

/-- The reduction kills `X^m` for `m ≥ 1`: the constant coefficient of a positive power of `X`
vanishes.  This is the well-definedness of the descended charge. -/
theorem coeffZeroRingHomZ_X_pow (n m : ℕ) (hm : 1 ≤ m) :
    coeffZeroRingHomZ n ((X : ℤ[X]) ^ m) = 0 := by
  simp [coeffZeroRingHomZ, zero_pow (show m ≠ 0 by omega)]

/-- The constant-coefficient reduction descends to the integral jet lattice `ℤ[X]/(X^m)` as a ring
homomorphism, since `X^m` — the generator of the jet ideal — reduces to `0` for `m ≥ 1`. -/
def jetCoeffZeroRingHomZ (m n : ℕ) (hm : 1 ≤ m) : LocalDivisorJet ℤ m →+* ZMod n :=
  Ideal.Quotient.lift (jetIdeal ℤ m) (coeffZeroRingHomZ n) (by
    intro a ha
    obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp ha
    rw [map_mul, coeffZeroRingHomZ_X_pow n m hm, zero_mul])

/-- The additive deck-charge on the integral jet lattice: constant-coefficient reduction into
`ZMod n`, viewed as an additive homomorphism. -/
def integralJetCharge (m n : ℕ) (hm : 1 ≤ m) : LocalDivisorJet ℤ m →+ ZMod n :=
  (jetCoeffZeroRingHomZ m n hm).toAddMonoidHom

/-- The integral charge reads a jet class off its representative's constant coefficient. -/
theorem integralJetCharge_jetClass (m n : ℕ) (hm : 1 ≤ m) (P : Polynomial ℤ) :
    integralJetCharge m n hm (jetClass ℤ m P) = coeffZeroRingHomZ n P := by
  show jetCoeffZeroRingHomZ m n hm (jetClass ℤ m P) = coeffZeroRingHomZ n P
  rw [jetClass, jetCoeffZeroRingHomZ, Ideal.Quotient.lift_mk]

/-- The integral charge sends the constant-jet-line generator `jetClass ℤ m (C 1)` to `1`. -/
theorem integralJetCharge_constJet_one (m n : ℕ) (hm : 1 ≤ m) :
    integralJetCharge m n hm (jetClass ℤ m (C 1)) = 1 := by
  rw [integralJetCharge_jetClass, coeffZeroRingHomZ_C]
  simp

/-! ### §4 The repair and the contrast with the `ℚ` barrier -/

/-- **Integral repair.**  For `m ≥ 1` and `n ≥ 2` there is an explicit additive charge
`ψ : LocalDivisorJet ℤ m →+ ZMod n` that is nonzero on the live unipotent constant-jet class at
`t = 1`: `ψ (jetClass ℤ m (C 1)) = 1 ≠ 0`.  The additive deck-charge channel that dies over `ℚ`
(`Hom(ℚ, ℤ/n) = 0`) is alive over the integral jet lattice. -/
theorem integral_jet_charge_exists {m n : ℕ} (hm : 1 ≤ m) (hn : 2 ≤ n) :
    ∃ ψ : LocalDivisorJet ℤ m →+ ZMod n,
      ψ (jetClass ℤ m (C 1)) = 1 ∧ ψ (jetClass ℤ m (C 1)) ≠ 0 := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  refine ⟨integralJetCharge m n hm, integralJetCharge_constJet_one m n hm, ?_⟩
  rw [integralJetCharge_constJet_one m n hm]
  exact one_ne_zero

/-- **Contrast corollary.**  Over the integral jet lattice there is an additive `ZMod n` charge that
does **not** vanish on the standard unipotent Fitting class `Fitting(seamDefZ (-1)) = jetClass ℤ m (C 1)`.
This is the exact statement whose `ℚ`-analogue is proven impossible in `FittingDeckChargeBarrier`:
there every additive `ZMod n` charge kills that face. -/
theorem integral_evades_barrier {m n : ℕ} (hm : 1 ≤ m) (hn : 2 ≤ n) :
    ∃ ψ : LocalDivisorJet ℤ m →+ ZMod n,
      ψ (fittingBoundaryClass m (standardPresZ m) (seamDefZ (-1))) ≠ 0 := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  refine ⟨integralJetCharge m n hm, ?_⟩
  have hclass : fittingBoundaryClass m (standardPresZ m) (seamDefZ (-1)) = jetClass ℤ m (C 1) := by
    rw [fittingClass_seamDefZ]
    congr 1
    simp
  rw [hclass, integralJetCharge_constJet_one m n hm]
  exact one_ne_zero

/-! ### §5 Naturality: the integral charge does not factor through the `ℚ` jet algebra -/

/-- Base change `ℤ[X]/(X^m) → ℚ[X]/(X^m)` induced by the coefficient inclusion `ℤ → ℚ`. -/
def baseChangeZQ (m : ℕ) : LocalDivisorJet ℤ m →+* LocalDivisorJet ℚ m :=
  Ideal.Quotient.lift (jetIdeal ℤ m)
    ((Ideal.Quotient.mk (jetIdeal ℚ m)).comp (Polynomial.mapRingHom (Int.castRingHom ℚ)))
    (by
      intro a ha
      obtain ⟨q, rfl⟩ := Ideal.mem_span_singleton.mp ha
      simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.map_mul,
        Polynomial.map_pow, Polynomial.map_X]
      exact jetClass_mul_X_pow_eq_zero ℚ m _)

/-- Base change carries the integral constant-jet generator to the rational one. -/
theorem baseChangeZQ_constJet_one (m : ℕ) :
    baseChangeZQ m (jetClass ℤ m (C 1)) = jetClass ℚ m (C 1) := by
  rw [jetClass, baseChangeZQ, Ideal.Quotient.lift_mk, jetClass]
  simp only [map_one]

/-- **The `ℚ` jet line is killed by every additive `ZMod n` charge.**  For `n ≥ 2`, the class
`jetClass ℚ m (C 1)` is `n`-divisible (`jetClass ℚ m (C 1) = n • jetClass ℚ m (C (1/n))`), so any
additive `φ : LocalDivisorJet ℚ m →+ ZMod n` sends it to `n • φ(·) = 0`.  This is the divisibility
that closes the channel over `ℚ`. -/
theorem rat_jet_line_killed {m n : ℕ} (hn : 2 ≤ n)
    (φ : LocalDivisorJet ℚ m →+ ZMod n) :
    φ (jetClass ℚ m (C 1)) = 0 := by
  have hn0 : (n : ℚ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hpoly : ((n : ℕ) • (C (1 / (n : ℚ)) : ℚ[X])) = C 1 := by
    rw [nsmul_eq_mul, ← map_natCast (C : ℚ →+* ℚ[X]) n, ← map_mul]
    congr 1
    field_simp
  have hx : jetClass ℚ m (C 1) = (n : ℕ) • jetClass ℚ m (C (1 / (n : ℚ))) := by
    rw [jetClass, jetClass, ← map_nsmul, hpoly]
  rw [hx, map_nsmul, ZModModule.char_nsmul_eq_zero]

/-- **Naturality remark: integrality vs divisibility.**  Composing the base change `ℤ → ℚ` with any
additive `ZMod n` charge of the `ℚ` jet algebra annihilates the integral constant-jet class, while
the integral charge itself does not.  Hence the integral charge does not factor through the `ℚ` jet
algebra: the live channel is a strictly integral phenomenon. -/
theorem integral_charge_not_factoring_through_rat {m n : ℕ} (hm : 1 ≤ m) (hn : 2 ≤ n) :
    (∀ φ : LocalDivisorJet ℚ m →+ ZMod n, φ (baseChangeZQ m (jetClass ℤ m (C 1))) = 0) ∧
      integralJetCharge m n hm (jetClass ℤ m (C 1)) ≠ 0 := by
  haveI : Fact (1 < n) := ⟨by omega⟩
  refine ⟨fun φ => ?_, ?_⟩
  · rw [baseChangeZQ_constJet_one]; exact rat_jet_line_killed hn φ
  · rw [integralJetCharge_constJet_one m n hm]; exact one_ne_zero

end RHTower
