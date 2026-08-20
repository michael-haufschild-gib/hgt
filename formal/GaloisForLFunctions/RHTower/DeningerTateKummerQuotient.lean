import GaloisForLFunctions.RHTower.DeningerEquivariantTateRegulator

/-!
# The period-one Tate Kummer quotient

At suspension period one, the Tate exponential identifies complex coefficients modulo the integer
lattice with invertible complex values.  This packages the closed exponential exact sequence as a
quotient isomorphism.
-/

namespace RHTower

noncomputable section

/-- The period-one Tate exponential as an additive homomorphism into complex units. -/
def deningerTateExpOneAddHom : ℂ →+ Additive ℂˣ where
  toFun α := Additive.ofMul (Units.mk0 (deningerTateExp 1 α) (deningerTateExp_ne_zero 1 α))
  map_zero' := by
    apply (Additive.toMul : Additive ℂˣ ≃ ℂˣ).injective
    apply Units.ext
    simp [deningerTateExp]
  map_add' α β := by
    apply (Additive.toMul : Additive ℂˣ ≃ ℂˣ).injective
    apply Units.ext
    exact deningerTateExp_add 1 α β

/-- The period-one Tate exponential has the integer lattice as its exact kernel. -/
theorem deningerTateExpOne_exact :
    Function.Exact (Int.castAddHom ℂ) deningerTateExpOneAddHom := by
  intro α
  constructor
  · intro h
    have hunit : (Additive.toMul (deningerTateExpOneAddHom α) : ℂˣ) = 1 := by
      simpa using congrArg Additive.toMul h
    have hexp : deningerTateExp 1 α = 1 := by
      exact congrArg Units.val hunit
    obtain ⟨n, hn⟩ := (deningerTateExp_eq_one_iff (by norm_num) α).mp hexp
    refine ⟨n, ?_⟩
    simpa using hn.symm
  · rintro ⟨n, rfl⟩
    apply (Additive.toMul : Additive ℂˣ ≃ ℂˣ).injective
    apply Units.ext
    change deningerTateExp 1 (n : ℂ) = 1
    exact (deningerTateExp_eq_one_iff (by norm_num) _).mpr ⟨n, by simp⟩

/-- The period-one Tate exponential realizes every nonzero complex value. -/
theorem deningerTateExpOne_surjective :
    Function.Surjective deningerTateExpOneAddHom := by
  intro z
  obtain ⟨α, hα⟩ := deningerTateExp_surjective (u := 1) (by norm_num) (Units.ne_zero z)
  refine ⟨α, ?_⟩
  apply (Additive.toMul : Additive ℂˣ ≃ ℂˣ).injective
  apply Units.ext
  exact hα

/-- The period-one Kummer quotient: complex coefficients modulo the integer lattice are exactly
the invertible complex values. -/
noncomputable def deningerTateExpOneQuotientEquiv :
    (ℂ ⧸ (Int.castAddHom ℂ).range) ≃+ Additive ℂˣ :=
  (QuotientAddGroup.quotientAddEquivOfEq
    (AddMonoidHom.exact_iff.mp deningerTateExpOne_exact).symm).trans
      (QuotientAddGroup.quotientKerEquivOfSurjective
        deningerTateExpOneAddHom deningerTateExpOne_surjective)

theorem deningerTateExpOneQuotientEquiv_mk (α : ℂ) :
    deningerTateExpOneQuotientEquiv (QuotientAddGroup.mk α) =
      deningerTateExpOneAddHom α := by
  simp only [deningerTateExpOneQuotientEquiv, AddEquiv.trans_apply,
    QuotientAddGroup.quotientAddEquivOfEq_mk]
  change QuotientAddGroup.kerLift deningerTateExpOneAddHom
    (QuotientAddGroup.mk α) = _
  rfl

end

end RHTower
