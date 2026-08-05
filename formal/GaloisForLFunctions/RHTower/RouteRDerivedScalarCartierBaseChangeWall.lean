import GaloisForLFunctions.RHTower.RouteRPreDivisorRationalCartierCoinvariantFunctor

/-!
# Derived scalar Cartier base-change wall

The universal neutral Cartier atom has two-term specialization differential `g - 1`.  This file
models its derived scalar fibre by the chain map `ℂ --(g-1)--> ℂ` and proves the sharp dichotomy:

* at neutral character `g = 1`, its degree-zero atom survives and its degree-one atom is closed;
* at every nonneutral scalar character, multiplication by `g - 1` has an explicit two-sided
  contracting homotopy, so the whole two-term fibre is contractible.

For the actual prime-dilation character at a Xi divisor, noncontractibility, coefficient-faithful
atom landing, vanishing of the explicit Hodge-mate coefficient, and critical-line placement are
equivalent.  Thus ordinary derived scalar base change cannot supply Route R's missing singular
comparison: off line it erases the complete derived atom, not only an underived quotient class.
-/

open Polynomial Complex

namespace RHTower

noncomputable section

/-- Specialized two-term Cartier differential, multiplication by the physical character defect. -/
def routeRScalarCartierDifferential (g : ℂ) : ℂ →ₗ[ℂ] ℂ :=
  (g - 1) • LinearMap.id

@[simp]
theorem routeRScalarCartierDifferential_apply (g z : ℂ) :
    routeRScalarCartierDifferential g z = (g - 1) * z := by
  simp [routeRScalarCartierDifferential]

/-- Candidate contraction of the scalar Cartier differential away from neutral character. -/
def routeRScalarCartierContractingHomotopy (g : ℂ) : ℂ →ₗ[ℂ] ℂ :=
  (g - 1)⁻¹ • LinearMap.id

@[simp]
theorem routeRScalarCartierContractingHomotopy_apply (g z : ℂ) :
    routeRScalarCartierContractingHomotopy g z = (g - 1)⁻¹ * z := by
  simp [routeRScalarCartierContractingHomotopy]

/-- Away from neutral character, differential followed by the explicit contraction is identity. -/
theorem routeRScalarCartierDifferential_comp_contractingHomotopy
    {g : ℂ} (hg : g ≠ 1) :
    (routeRScalarCartierDifferential g).comp
        (routeRScalarCartierContractingHomotopy g) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  have hsub : g - 1 ≠ 0 := sub_ne_zero.mpr hg
  simp [LinearMap.comp_apply, hsub]

/-- Away from neutral character, contraction followed by differential is identity. -/
theorem routeRScalarCartierContractingHomotopy_comp_differential
    {g : ℂ} (hg : g ≠ 1) :
    (routeRScalarCartierContractingHomotopy g).comp
        (routeRScalarCartierDifferential g) = LinearMap.id := by
  apply LinearMap.ext
  intro z
  have hsub : g - 1 ≠ 0 := sub_ne_zero.mpr hg
  simp [LinearMap.comp_apply, hsub]

/-- Degree-zero boundary space of the specialized scalar Cartier complex. -/
def routeRScalarCartierBoundary (g : ℂ) : Submodule ℂ ℂ :=
  LinearMap.range (routeRScalarCartierDifferential g)

/-- Degree-zero homology of the specialized scalar Cartier complex. -/
abbrev RouteRScalarCartierH0 (g : ℂ) := ℂ ⧸ routeRScalarCartierBoundary g

/-- Distinguished unit atom in degree-zero scalar Cartier homology. -/
def routeRScalarCartierH0Atom (g : ℂ) : RouteRScalarCartierH0 g :=
  (routeRScalarCartierBoundary g).mkQ 1

/-- At a nonneutral scalar character, every degree-zero vector is a boundary. -/
theorem routeRScalarCartierBoundary_eq_top_of_ne_one
    {g : ℂ} (hg : g ≠ 1) : routeRScalarCartierBoundary g = ⊤ := by
  rw [routeRScalarCartierBoundary, LinearMap.range_eq_top]
  intro z
  refine ⟨(g - 1)⁻¹ * z, ?_⟩
  have hsub : g - 1 ≠ 0 := sub_ne_zero.mpr hg
  simp [hsub]

/-- At neutral character, the specialized differential has zero boundary space. -/
theorem routeRScalarCartierBoundary_eq_bot_of_eq_one
    {g : ℂ} (hg : g = 1) : routeRScalarCartierBoundary g = ⊥ := by
  subst g
  apply le_antisymm
  · rintro z ⟨w, rfl⟩
    simp
  · exact bot_le

/-- The degree-zero Cartier atom is erased at every nonneutral scalar specialization. -/
theorem routeRScalarCartierH0Atom_eq_zero_of_ne_one
    {g : ℂ} (hg : g ≠ 1) : routeRScalarCartierH0Atom g = 0 := by
  change Submodule.Quotient.mk (1 : ℂ) = 0
  rw [Submodule.Quotient.mk_eq_zero,
    routeRScalarCartierBoundary_eq_top_of_ne_one hg]
  trivial

/-- The degree-zero Cartier atom survives at neutral scalar specialization. -/
theorem routeRScalarCartierH0Atom_ne_zero_of_eq_one
    {g : ℂ} (hg : g = 1) : routeRScalarCartierH0Atom g ≠ 0 := by
  change Submodule.Quotient.mk (1 : ℂ) ≠ 0
  intro hzero
  have hone : (1 : ℂ) ∈ routeRScalarCartierBoundary g :=
    (Submodule.Quotient.mk_eq_zero _).mp hzero
  rw [routeRScalarCartierBoundary_eq_bot_of_eq_one hg,
    Submodule.mem_bot] at hone
  exact one_ne_zero hone

/-- Sharp support law for degree-zero scalar Cartier homology. -/
theorem routeRScalarCartierH0Atom_ne_zero_iff (g : ℂ) :
    routeRScalarCartierH0Atom g ≠ 0 ↔ g = 1 := by
  constructor
  · intro h
    by_contra hg
    exact h (routeRScalarCartierH0Atom_eq_zero_of_ne_one hg)
  · exact routeRScalarCartierH0Atom_ne_zero_of_eq_one

/-- Sharp support law for the distinguished degree-one cycle. -/
theorem routeRScalarCartierH1Atom_mem_ker_iff (g : ℂ) :
    (1 : ℂ) ∈ LinearMap.ker (routeRScalarCartierDifferential g) ↔ g = 1 := by
  rw [LinearMap.mem_ker]
  simp [sub_eq_zero]

/-- Both homological orientations survive exactly at neutral character. -/
theorem routeRScalarCartierTwoSidedAtomSurvives_iff (g : ℂ) :
    (routeRScalarCartierH0Atom g ≠ 0 ∧
      (1 : ℂ) ∈ LinearMap.ker (routeRScalarCartierDifferential g)) ↔ g = 1 := by
  rw [routeRScalarCartierH0Atom_ne_zero_iff,
    routeRScalarCartierH1Atom_mem_ker_iff, and_self]

/-- Normalized period-one atom landing into scalar Cartier homology. -/
def routeRScalarCartierH0AtomLanding (g : ℂ) :
    ℂ →ₗ[ℂ] RouteRScalarCartierH0 g where
  toFun z := z • routeRScalarCartierH0Atom g
  map_add' z w := add_smul z w _
  map_smul' z w := by simp [smul_smul]

@[simp]
theorem routeRScalarCartierH0AtomLanding_apply (g z : ℂ) :
    routeRScalarCartierH0AtomLanding g z =
      z • routeRScalarCartierH0Atom g := rfl

/-- The normalized scalar landing is coefficient-faithful exactly at neutral character. -/
theorem routeRScalarCartierH0AtomLanding_injective_iff (g : ℂ) :
    Function.Injective (routeRScalarCartierH0AtomLanding g) ↔ g = 1 := by
  rw [← routeRScalarCartierH0Atom_ne_zero_iff]
  constructor
  · intro hinj hzero
    have h := hinj (show routeRScalarCartierH0AtomLanding g 1 =
      routeRScalarCartierH0AtomLanding g 0 by simp [hzero])
    exact one_ne_zero h
  · intro hatom z w hzw
    have hzero : (z - w) • routeRScalarCartierH0Atom g = 0 := by
      simpa [sub_smul] using sub_eq_zero.mpr hzw
    rcases smul_eq_zero.mp hzero with hscalar | hclass
    · exact sub_eq_zero.mp hscalar
    · exact (hatom hclass).elim

/-- Chain-level contractibility of the complete two-term scalar specialization. -/
def RouteRScalarCartierSpecializationContractible (g : ℂ) : Prop :=
  ∃ h : ℂ →ₗ[ℂ] ℂ,
    (routeRScalarCartierDifferential g).comp h = LinearMap.id ∧
      h.comp (routeRScalarCartierDifferential g) = LinearMap.id

/-- Complete derived scalar fibre is contractible exactly off neutral character. -/
theorem routeRScalarCartierSpecializationContractible_iff (g : ℂ) :
    RouteRScalarCartierSpecializationContractible g ↔ g ≠ 1 := by
  constructor
  · rintro ⟨h, hleft, -⟩ hg
    subst g
    have hone := LinearMap.congr_fun hleft (1 : ℂ)
    simp at hone
  · intro hg
    exact ⟨routeRScalarCartierContractingHomotopy g,
      routeRScalarCartierDifferential_comp_contractingHomotopy hg,
      routeRScalarCartierContractingHomotopy_comp_differential hg⟩

/-- Coefficient-faithful atom landing is equivalent to noncontractibility of the derived fibre. -/
theorem routeRScalarCartierH0AtomLanding_injective_iff_not_contractible
    (g : ℂ) :
    Function.Injective (routeRScalarCartierH0AtomLanding g) ↔
      ¬ RouteRScalarCartierSpecializationContractible g := by
  rw [routeRScalarCartierH0AtomLanding_injective_iff,
    routeRScalarCartierSpecializationContractible_iff]
  tauto

/-- Actual complex scalar prime-dilation character at a Xi divisor. -/
def routeRPrimeXiScalarCartierGain
    (p : Nat.Primes) (rho : XiDivisorSupport) : ℂ :=
  deningerHalfDensityMateGain p (rho : ℂ)

/-- Actual scalar character is neutral exactly at critical-line support. -/
theorem routeRPrimeXiScalarCartierGain_eq_one_iff
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    routeRPrimeXiScalarCartierGain p rho = 1 ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [routeRPrimeXiScalarCartierGain]
  norm_cast
  exact deningerHalfDensityMateGain_eq_one_iff_re_eq_half p.2.two_le _

/-- Actual normalized period-one landing into the specialized scalar derived fibre. -/
def routeRPrimeXiScalarCartierAtomLanding
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    ℂ →ₗ[ℂ] RouteRScalarCartierH0 (routeRPrimeXiScalarCartierGain p rho) :=
  routeRScalarCartierH0AtomLanding _

/-- Actual scalar atom landing is faithful exactly on the critical line. -/
theorem routeRPrimeXiScalarCartierAtomLanding_injective_iff_re_eq_half
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    Function.Injective (routeRPrimeXiScalarCartierAtomLanding p rho) ↔
      (rho : ℂ).re = 1 / 2 := by
  rw [routeRPrimeXiScalarCartierAtomLanding,
    routeRScalarCartierH0AtomLanding_injective_iff,
    routeRPrimeXiScalarCartierGain_eq_one_iff]

/-- Exact comparison with Route R's explicit fixed same-fibre Hodge-mate coefficient. -/
theorem routeRPrimeXiScalarCartierAtomLanding_injective_iff_hodgeMateCoefficient_eq_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    Function.Injective (routeRPrimeXiScalarCartierAtomLanding p rho) ↔
      ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho = 0 :=
  (routeRPrimeXiScalarCartierAtomLanding_injective_iff_re_eq_half p rho).trans
    (ccmRationalAdelicPrimeXiHodgeMateCoefficient_eq_zero_iff_re_eq_half p rho).symm

/-- Actual complete scalar derived fibre is contractible exactly off the critical line. -/
theorem routeRPrimeXiScalarCartierSpecializationContractible_iff_re_ne_half
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    RouteRScalarCartierSpecializationContractible
        (routeRPrimeXiScalarCartierGain p rho) ↔
      (rho : ℂ).re ≠ 1 / 2 := by
  rw [routeRScalarCartierSpecializationContractible_iff,
    ne_eq, routeRPrimeXiScalarCartierGain_eq_one_iff]

/-- Contractibility is equivalent to nonvanishing of the explicit physical Hodge-mate port. -/
theorem routeRPrimeXiScalarCartierSpecializationContractible_iff_hodgeMateCoefficient_ne_zero
    (p : Nat.Primes) (rho : XiDivisorSupport) :
    RouteRScalarCartierSpecializationContractible
        (routeRPrimeXiScalarCartierGain p rho) ↔
      ccmRationalAdelicPrimeXiHodgeMateCoefficient p rho ≠ 0 := by
  rw [routeRPrimeXiScalarCartierSpecializationContractible_iff_re_ne_half]
  exact not_congr
    (ccmRationalAdelicPrimeXiHodgeMateCoefficient_eq_zero_iff_re_eq_half
      p rho).symm

/-- Global coefficient-faithful scalar derived Cartier landing. -/
def RouteRPrimeXiGlobalScalarCartierNonerasure (p : Nat.Primes) : Prop :=
  ∀ rho : XiDivisorSupport,
    Function.Injective (routeRPrimeXiScalarCartierAtomLanding p rho)

/-- Global scalar derived Cartier non-erasure is precisely the Route R/RH endpoint. -/
theorem routeRPrimeXiGlobalScalarCartierNonerasure_iff_riemannHypothesis
    (p : Nat.Primes) :
    RouteRPrimeXiGlobalScalarCartierNonerasure p ↔ RiemannHypothesis := by
  constructor
  · intro hnonerase
    apply (forall_ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_riemannHypothesis p).1
    intro rho
    apply (ccmRationalAdelicPrimeXiSameFiberNormIdentity_iff_hodgeMateCoefficient_eq_zero
      p rho).2
    exact
      (routeRPrimeXiScalarCartierAtomLanding_injective_iff_hodgeMateCoefficient_eq_zero
        p rho).1 (hnonerase rho)
  · intro hRH rho
    apply
      (routeRPrimeXiScalarCartierAtomLanding_injective_iff_re_eq_half p rho).2
    exact xi_divisor_support_re_eq_half_of_rh hRH rho

end

end RHTower
