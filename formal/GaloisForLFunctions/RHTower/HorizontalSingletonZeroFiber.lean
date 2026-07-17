import GaloisForLFunctions.RHTower.CensusProfile

/-!
# Horizontal-singleton Xi-zero fibers

At a fixed ordinate `t`, `xiHorizontalMultiplicity t` is the total analytic multiplicity of all
Xi zeros in the open critical strip.  Critical-line reflection preserves the ordinate and the
analytic order.  Therefore an off-line zero contributes together with a distinct reflected zero,
so every off-line horizontal fiber has total multiplicity at least two.

The multiplicity-one fiber is consequently an unconditional, intrinsically defined group of Xi
zeros on the critical line.  Its members are also simple.
-/

open Complex Set

namespace RHTower

noncomputable section

/-- Total Xi-zero multiplicity in the open critical strip at the exact ordinate `t`. -/
def xiHorizontalMultiplicity (t : ℝ) : ℕ :=
  ∑ z ∈ stripHeightFinset t, (analyticOrderAt xi z).toNat

/-- An off-critical Xi zero forces its horizontal fiber to contain at least two zero copies: the
zero itself and its distinct critical-line reflection, with equal positive analytic orders. -/
theorem two_le_xiHorizontalMultiplicity_of_offLine
    {ρ : ℂ} (hρ : ρ ∈ stripHeightFinset ρ.im) (hoff : ρ.re ≠ 1 / 2) :
    2 ≤ xiHorizontalMultiplicity ρ.im := by
  classical
  have hreflect : lineReflect ρ ∈ stripHeightFinset ρ.im :=
    lineReflect_mem_stripHeightFinset hρ
  have hne : ρ ≠ lineReflect ρ := by
    intro h
    apply hoff
    have hre := congrArg Complex.re h
    rw [lineReflect_re] at hre
    linarith
  have hpair : ({ρ, lineReflect ρ} : Finset ℂ) ⊆ stripHeightFinset ρ.im := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hρ
    · exact hreflect
  have hle := Finset.sum_le_sum_of_subset hpair
      (f := fun z => (analyticOrderAt xi z).toNat)
  rw [Finset.sum_pair hne, xi_orderAt_lineReflect] at hle
  have hzero : xi ρ = 0 := (mem_stripHeightFinset.mp hρ).2.2.2
  have hpos : 1 ≤ (analyticOrderAt xi ρ).toNat :=
    Nat.one_le_iff_ne_zero.mpr (xi_order_toNat_ne_zero hzero)
  rw [xiHorizontalMultiplicity]
  omega

/-- The intrinsic group of Xi zeros whose complete horizontal fiber has total multiplicity one. -/
def XiHorizontalSingletonZero (ρ : ℂ) : Prop :=
  ρ ∈ stripHeightFinset ρ.im ∧ xiHorizontalMultiplicity ρ.im = 1

/-- Every horizontal-singleton Xi zero lies on the critical line. -/
theorem xiHorizontalSingletonZero_re_eq_half {ρ : ℂ}
    (hρ : XiHorizontalSingletonZero ρ) : ρ.re = 1 / 2 := by
  by_contra hoff
  have htwo := two_le_xiHorizontalMultiplicity_of_offLine hρ.1 hoff
  omega

/-- Every horizontal-singleton Xi zero is simple. -/
theorem xiHorizontalSingletonZero_order_eq_one {ρ : ℂ}
    (hρ : XiHorizontalSingletonZero ρ) :
    (analyticOrderAt xi ρ).toNat = 1 := by
  have hzero : xi ρ = 0 := (mem_stripHeightFinset.mp hρ.1).2.2.2
  have hpos : 1 ≤ (analyticOrderAt xi ρ).toNat :=
    Nat.one_le_iff_ne_zero.mpr (xi_order_toNat_ne_zero hzero)
  have hle : (analyticOrderAt xi ρ).toNat ≤ xiHorizontalMultiplicity ρ.im := by
    rw [xiHorizontalMultiplicity]
    exact Finset.single_le_sum (fun z _ => Nat.zero_le _) hρ.1
  omega

end


end RHTower
