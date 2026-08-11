import GaloisForLFunctions.RHTower.CCMRationalAdelicPrimeIsotropyObserverFreedom
import GaloisForLFunctions.RHTower.CCMRationalAdelicEndpointReal

/-!
# The vertical gauge group of the rational-adelic prime-isotropy complex

Inside the complex

`A --D₀--> A ⊕ ℂ --D₁--> ℂ`,  `D₀x = (Tx, ε₀x)`,  `D₁(y,z) = ε₀y`,  `T = α_p - 1`,

consider the cochain automorphisms that fix degrees zero and two, fix the isotropy coordinate in
degree one, and fix the retained cocycle `η = (0,1)`.  Every such automorphism is the vertical
shear `(y,z) ↦ (y, z + ℓ(y))` for a unique linear functional `ℓ` annihilating `im T`, and shears
compose additively.  So the vertical gauge group is the annihilator of `im T`, that is the
algebraic dual of the source coinvariants `A / im T`.

The set of Stokes primitives — functionals `R` with `RT = ε₀` — is nonempty by the bilateral orbit
regulator, and is exactly one orbit of that group, on which the group acts simply transitively.
The induced ambiguity on cohomology is affine over `Ann(im T) / ℂε₀`, which restriction identifies
with the algebraic dual of the residual quotient `Q_p = ker ε₀ / im T`.  The Haar endpoint trace
lies in `Ann(im T)` and restricts to a nonzero functional on `Q_p`, so the ambiguity is nonzero.

Rational scaling automorphisms commute with the Haar shear, the Real involution conjugates its
parameter, and the strict resolved Xi comparison is preserved up to an explicit cochain homotopy.
Consequently a reader of `H¹` invariant under the whole Haar shear line must annihilate the
retained class, while marking a Stokes splitting leaves every target coefficient available.
-/

noncomputable section

open MeasureTheory
open GaloisForLFunctions
open GaloisForLFunctions.RHTower

namespace RHTower

private abbrev Core := CCMRationalAdelicBruhatSimpleTensor
private abbrev One := CCMRationalAdelicPrimeRelativeOne

/-! ## The vertical shear group -/

/-- **Card `(VSG.5)`.**  Functionals annihilating the orbit-difference image. -/
abbrev ccmRationalAdelicPrimeShearAnnihilator (p : Nat.Primes) :
    Submodule ℂ (Module.Dual ℂ Core) :=
  (LinearMap.range (ccmRationalAdelicPrimeOrbitDifference p)).dualAnnihilator

theorem mem_ccmRationalAdelicPrimeShearAnnihilator_iff (p : Nat.Primes)
    (ell : Module.Dual ℂ Core) :
    ell ∈ ccmRationalAdelicPrimeShearAnnihilator p ↔
      ∀ x : Core, ell (ccmRationalAdelicPrimeOrbitDifference p x) = 0 := by
  rw [Submodule.mem_dualAnnihilator]
  constructor
  · intro h x
    exact h _ ⟨x, rfl⟩
  · rintro h _ ⟨x, rfl⟩
    exact h x

/-- **Card `(VSG.6)`.**  The vertical shear attached to a linear functional. -/
def ccmRationalAdelicPrimeVerticalShear (ell : Module.Dual ℂ Core) : One →ₗ[ℂ] One where
  toFun w := (w.1, w.2 + ell w.1)
  map_add' w v := by
    refine Prod.ext rfl ?_
    rw [Prod.snd_add, Prod.snd_add, Prod.fst_add, map_add]
    ring
  map_smul' c w := by
    refine Prod.ext rfl ?_
    rw [RingHom.id_apply, Prod.smul_snd, Prod.smul_snd, Prod.smul_fst, map_smul]
    simp only [smul_eq_mul]
    ring

@[simp] theorem ccmRationalAdelicPrimeVerticalShear_apply (ell : Module.Dual ℂ Core) (w : One) :
    ccmRationalAdelicPrimeVerticalShear ell w = (w.1, w.2 + ell w.1) := rfl

@[simp] theorem ccmRationalAdelicPrimeVerticalShear_zero :
    ccmRationalAdelicPrimeVerticalShear (0 : Module.Dual ℂ Core) = LinearMap.id := by
  apply LinearMap.ext
  intro w
  rw [ccmRationalAdelicPrimeVerticalShear_apply]
  simp

/-- Shears compose additively. -/
theorem ccmRationalAdelicPrimeVerticalShear_comp (ell m : Module.Dual ℂ Core) :
    (ccmRationalAdelicPrimeVerticalShear ell).comp
        (ccmRationalAdelicPrimeVerticalShear m) =
      ccmRationalAdelicPrimeVerticalShear (ell + m) := by
  apply LinearMap.ext
  intro w
  refine Prod.ext rfl ?_
  change w.2 + m w.1 + ell w.1 = w.2 + (ell w.1 + m w.1)
  ring

/-- Every shear fixes the isotropy coordinate. -/
@[simp] theorem ccmRationalAdelicPrimeVerticalShear_fst (ell : Module.Dual ℂ Core) (w : One) :
    (ccmRationalAdelicPrimeVerticalShear ell w).1 = w.1 := rfl

/-- Every shear fixes the retained cocycle. -/
theorem ccmRationalAdelicPrimeVerticalShear_cocycle (ell : Module.Dual ℂ Core) :
    ccmRationalAdelicPrimeVerticalShear ell ((0 : Core), (1 : ℂ)) = ((0 : Core), (1 : ℂ)) := by
  rw [ccmRationalAdelicPrimeVerticalShear_apply, map_zero, add_zero]

/-- A shear commutes with the second differential. -/
theorem ccmRationalAdelicPrimeVerticalShear_comp_D1 (ell : Module.Dual ℂ Core) :
    ccmRationalAdelicPrimeRelativeD1.comp
      (ccmRationalAdelicPrimeVerticalShear ell) = ccmRationalAdelicPrimeRelativeD1 := rfl

/-- **Card `(VSG.6)`.**  A shear is a cochain map exactly when its functional kills orbit
differences. -/
theorem ccmRationalAdelicPrimeVerticalShear_comp_D0 (p : Nat.Primes)
    {ell : Module.Dual ℂ Core} (hell : ell ∈ ccmRationalAdelicPrimeShearAnnihilator p) :
    (ccmRationalAdelicPrimeVerticalShear ell).comp (ccmRationalAdelicPrimeRelativeD0 p) =
      ccmRationalAdelicPrimeRelativeD0 p := by
  apply LinearMap.ext
  intro x
  refine Prod.ext rfl ?_
  change ccmRationalAdelicBruhatZeroEval x +
    ell (ccmRationalAdelicPrimeScaling p • x - x) = ccmRationalAdelicBruhatZeroEval x
  rw [show ccmRationalAdelicPrimeScaling p • x - x =
      ccmRationalAdelicPrimeOrbitDifference p x from rfl,
    (mem_ccmRationalAdelicPrimeShearAnnihilator_iff p ell).1 hell x, add_zero]

/-- **Theorem A, card `(VSG.5)` boxed.**  Every coordinate-fixing cochain automorphism of the
prime-isotropy complex is a vertical shear by a unique functional annihilating `im T`. -/
theorem ccmRationalAdelicPrimeVerticalGauge_classification (p : Nat.Primes)
    (U : One →ₗ[ℂ] One)
    (hfst : ∀ w : One, (U w).1 = w.1)
    (heta : U ((0 : Core), (1 : ℂ)) = ((0 : Core), (1 : ℂ)))
    (hD0 : U.comp (ccmRationalAdelicPrimeRelativeD0 p) =
      ccmRationalAdelicPrimeRelativeD0 p) :
    ∃! ell : Module.Dual ℂ Core, ell ∈ ccmRationalAdelicPrimeShearAnnihilator p ∧
      U = ccmRationalAdelicPrimeVerticalShear ell := by
  classical
  set ell : Module.Dual ℂ Core :=
    (LinearMap.snd ℂ Core ℂ).comp (U.comp (LinearMap.inl ℂ Core ℂ)) with hell
  have hUsnd : ∀ w : One, (U w).2 = ell w.1 + w.2 := by
    intro w
    have hsplit : w = (w.1, (0 : ℂ)) + w.2 • ((0 : Core), (1 : ℂ)) := by
      refine Prod.ext ?_ ?_
      · change w.1 = w.1 + w.2 • (0 : Core)
        rw [smul_zero, add_zero]
      · change w.2 = 0 + w.2 • (1 : ℂ)
        rw [smul_eq_mul, mul_one, zero_add]
    conv_lhs => rw [hsplit]
    rw [map_add, map_smul, heta]
    change (U (w.1, (0 : ℂ))).2 + w.2 • (1 : ℂ) = ell w.1 + w.2
    rw [smul_eq_mul, mul_one]
    rfl
  have hUapply : ∀ w : One, U w = (w.1, ell w.1 + w.2) :=
    fun w => Prod.ext (hfst w) (hUsnd w)
  have hann : ell ∈ ccmRationalAdelicPrimeShearAnnihilator p := by
    rw [mem_ccmRationalAdelicPrimeShearAnnihilator_iff]
    intro x
    have hx := LinearMap.congr_fun hD0 x
    have hx2 := congrArg Prod.snd hx
    rw [LinearMap.comp_apply, hUapply] at hx2
    change ell (ccmRationalAdelicPrimeOrbitDifference p x) +
      ccmRationalAdelicBruhatZeroEval x = ccmRationalAdelicBruhatZeroEval x at hx2
    linear_combination hx2
  refine ⟨ell, ⟨hann, ?_⟩, ?_⟩
  · apply LinearMap.ext
    intro w
    rw [hUapply, ccmRationalAdelicPrimeVerticalShear_apply]
    exact Prod.ext rfl (add_comm _ _)
  · rintro m ⟨-, hm⟩
    apply LinearMap.ext
    intro x
    have := congrArg (fun F => (F ((x : Core), (0 : ℂ))).2) hm
    change (U (x, (0 : ℂ))).2 = (0 : ℂ) + m x at this
    rw [hUapply] at this
    change ell x + (0 : ℂ) = (0 : ℂ) + m x at this
    rw [add_zero, zero_add] at this
    exact this.symm

/-- **Card `(VSG.5)`.**  The vertical gauge group is the algebraic dual of the source
coinvariants. -/
def ccmRationalAdelicPrimeShearAnnihilatorEquivDualCoinvariants (p : Nat.Primes) :
    Module.Dual ℂ (Core ⧸ LinearMap.range (ccmRationalAdelicPrimeOrbitDifference p)) ≃ₗ[ℂ]
      ccmRationalAdelicPrimeShearAnnihilator p :=
  Submodule.dualQuotEquivDualAnnihilator _

/-! ## Theorem B: Stokes primitives form a shear torsor -/

/-- **Card `(VSG.7)`.**  The set of Stokes primitives. -/
def ccmRationalAdelicPrimeStokesPrimitives (p : Nat.Primes) : Set (Module.Dual ℂ Core) :=
  {R | ∀ x : Core, R (ccmRationalAdelicPrimeOrbitDifference p x) =
    ccmRationalAdelicBruhatZeroEval x}

/-- The exact Stokes law, phrased with the orbit-difference map. -/
theorem ccmRationalAdelicPrimeOrbitStokes_orbitDifference (p : Nat.Primes) (x : Core) :
    ccmRationalAdelicPrimeOrbitStokesLM p (ccmRationalAdelicPrimeOrbitDifference p x) =
      ccmRationalAdelicBruhatZeroEval x :=
  ccmRationalAdelicPrimeOrbitStokes_scaling_sub p x

/-- The bilateral orbit regulator is a Stokes primitive. -/
theorem ccmRationalAdelicPrimeOrbitStokesLM_mem_primitives (p : Nat.Primes) :
    ccmRationalAdelicPrimeOrbitStokesLM p ∈ ccmRationalAdelicPrimeStokesPrimitives p :=
  fun x => ccmRationalAdelicPrimeOrbitStokes_scaling_sub p x

/-- **Theorem B, card `(VSG.8)` boxed.**  The Stokes primitives are exactly one shear orbit. -/
theorem mem_ccmRationalAdelicPrimeStokesPrimitives_iff (p : Nat.Primes)
    (R : Module.Dual ℂ Core) :
    R ∈ ccmRationalAdelicPrimeStokesPrimitives p ↔
      R - ccmRationalAdelicPrimeOrbitStokesLM p ∈ ccmRationalAdelicPrimeShearAnnihilator p := by
  rw [mem_ccmRationalAdelicPrimeShearAnnihilator_iff]
  constructor
  · intro hR x
    rw [LinearMap.sub_apply, hR x, ccmRationalAdelicPrimeOrbitStokes_orbitDifference, sub_self]
  · intro hR x
    have := hR x
    rw [LinearMap.sub_apply, ccmRationalAdelicPrimeOrbitStokes_orbitDifference,
      sub_eq_zero] at this
    exact this

/-- **Card `(VSG.9)`.**  The normalized relative reader of a Stokes primitive. -/
def ccmRationalAdelicPrimeStokesReader (R : Module.Dual ℂ Core) : One →ₗ[ℂ] ℂ :=
  (LinearMap.snd ℂ Core ℂ) - R.comp (LinearMap.fst ℂ Core ℂ)

@[simp] theorem ccmRationalAdelicPrimeStokesReader_apply (R : Module.Dual ℂ Core) (w : One) :
    ccmRationalAdelicPrimeStokesReader R w = w.2 - R w.1 := rfl

/-- **Card `(VSG.9)`.**  Every primitive reads the retained cocycle with period one. -/
theorem ccmRationalAdelicPrimeStokesReader_cocycle (R : Module.Dual ℂ Core) :
    ccmRationalAdelicPrimeStokesReader R ((0 : Core), (1 : ℂ)) = 1 := by
  rw [ccmRationalAdelicPrimeStokesReader_apply, map_zero, sub_zero]

/-- **Card `(VSG.10)` boxed.**  Shears act on readers by translating the primitive. -/
theorem ccmRationalAdelicPrimeStokesReader_comp_shear (R ell : Module.Dual ℂ Core) :
    (ccmRationalAdelicPrimeStokesReader R).comp
        (ccmRationalAdelicPrimeVerticalShear ell) =
      ccmRationalAdelicPrimeStokesReader (R - ell) := by
  apply LinearMap.ext
  intro w
  change w.2 + ell w.1 - R w.1 = w.2 - (R w.1 - ell w.1)
  ring

/-- The shear action on Stokes primitives is simply transitive: the unique shear carrying `R` to
`R'` is `R - R'`. -/
theorem ccmRationalAdelicPrimeStokes_simplyTransitive (p : Nat.Primes)
    {R R' : Module.Dual ℂ Core} (hR : R ∈ ccmRationalAdelicPrimeStokesPrimitives p)
    (hR' : R' ∈ ccmRationalAdelicPrimeStokesPrimitives p) :
    ∃! ell : Module.Dual ℂ Core,
      ell ∈ ccmRationalAdelicPrimeShearAnnihilator p ∧ R - ell = R' := by
  refine ⟨R - R', ⟨?_, by abel⟩, ?_⟩
  · rw [mem_ccmRationalAdelicPrimeShearAnnihilator_iff]
    intro x
    rw [LinearMap.sub_apply, hR x, hR' x, sub_self]
  · rintro m ⟨-, hm⟩
    rw [← hm]
    abel

/-! ## The ambiguity space `Ann(im T) / ℂε₀ ≅ Q_p^*` -/

/-- The zero-adele endpoint is a shear functional. -/
theorem ccmRationalAdelicBruhatZeroEval_mem_shearAnnihilator (p : Nat.Primes) :
    ccmRationalAdelicBruhatZeroEval ∈ ccmRationalAdelicPrimeShearAnnihilator p := by
  rw [mem_ccmRationalAdelicPrimeShearAnnihilator_iff]
  exact fun x => ccmRationalAdelicPrimeOrbitDifference_mem_ker p x

/-- **Card `(VSG.4)`.**  The Haar endpoint trace is a shear functional. -/
theorem ccmRationalAdelicBruhatIntegral_mem_shearAnnihilator (p : Nat.Primes) :
    ccmRationalAdelicBruhatIntegral ∈ ccmRationalAdelicPrimeShearAnnihilator p := by
  rw [mem_ccmRationalAdelicPrimeShearAnnihilator_iff]
  exact ccmRationalAdelicBruhatIntegral_orbitDifference p

/-- A normalized adelic tensor: the Gaussian against the characteristic function of the integral
finite adeles. -/
def ccmRationalAdelicUnitWitness : Core :=
  gaussianSchwartz ⊗ₜ[ℂ] ccmRationalIntegralFiniteAdelesBruhat

theorem ccmRationalAdelicUnitWitness_zeroEval :
    ccmRationalAdelicBruhatZeroEval ccmRationalAdelicUnitWitness = 1 := by
  have hzero : (0 : CCMRationalFiniteAdele) ∈ ccmRationalIntegralFiniteAdeles :=
    fun _ => zero_mem _
  rw [ccmRationalAdelicUnitWitness, ccmRationalAdelicBruhatZeroEval_tmul,
    ccmRationalIntegralFiniteAdelesBruhat_apply, if_pos hzero, gaussianSchwartz_apply]
  norm_num [gaussReal]

/-- Restriction of a shear functional to the residual quotient. -/
def ccmRationalAdelicPrimeResidualRestrictLM (p : Nat.Primes) :
    ccmRationalAdelicPrimeShearAnnihilator p →ₗ[ℂ]
      Module.Dual ℂ (CCMRationalAdelicPrimeResidualQuotient p) where
  toFun ell := (ccmRationalAdelicPrimeResidualRelations p).liftQ
    ((ell : Module.Dual ℂ Core).comp
      (LinearMap.ker ccmRationalAdelicBruhatZeroEval).subtype)
    (by
      intro y hy
      obtain ⟨x, hx⟩ := hy
      have hx' : ccmRationalAdelicPrimeOrbitDifference p x = (y : Core) := hx
      change (ell : Module.Dual ℂ Core) (y : Core) = 0
      rw [← hx']
      exact (mem_ccmRationalAdelicPrimeShearAnnihilator_iff p _).1 ell.2 x)
  map_add' a b := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H y => rfl
  map_smul' c a := by
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H y => rfl

@[simp] theorem ccmRationalAdelicPrimeResidualRestrictLM_mk (p : Nat.Primes)
    (ell : ccmRationalAdelicPrimeShearAnnihilator p)
    (y : LinearMap.ker ccmRationalAdelicBruhatZeroEval) :
    ccmRationalAdelicPrimeResidualRestrictLM p ell (Submodule.Quotient.mk y) =
      (ell : Module.Dual ℂ Core) (y : Core) := rfl

/-- Restriction to the residual quotient is surjective: every functional on a subquotient of a
vector space extends. -/
theorem ccmRationalAdelicPrimeResidualRestrictLM_surjective (p : Nat.Primes) :
    Function.Surjective (ccmRationalAdelicPrimeResidualRestrictLM p) := by
  intro L
  obtain ⟨G, hG⟩ := LinearMap.exists_extend
    (L.comp (ccmRationalAdelicPrimeResidualRelations p).mkQ)
  have hGy : ∀ y : LinearMap.ker ccmRationalAdelicBruhatZeroEval,
      G (y : Core) = L (Submodule.Quotient.mk y) := fun y => LinearMap.congr_fun hG y
  have hGann : G ∈ ccmRationalAdelicPrimeShearAnnihilator p := by
    rw [mem_ccmRationalAdelicPrimeShearAnnihilator_iff]
    intro x
    have hmem : ccmRationalAdelicPrimeOrbitDifference p x ∈
        LinearMap.ker ccmRationalAdelicBruhatZeroEval :=
      ccmRationalAdelicPrimeOrbitDifference_mem_ker p x
    rw [show ccmRationalAdelicPrimeOrbitDifference p x =
        ((⟨ccmRationalAdelicPrimeOrbitDifference p x, hmem⟩ :
          LinearMap.ker ccmRationalAdelicBruhatZeroEval) : Core) from rfl, hGy]
    rw [show (Submodule.Quotient.mk
        (⟨ccmRationalAdelicPrimeOrbitDifference p x, hmem⟩ :
          LinearMap.ker ccmRationalAdelicBruhatZeroEval) :
        CCMRationalAdelicPrimeResidualQuotient p) = 0 from
      (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩, map_zero]
  refine ⟨⟨G, hGann⟩, ?_⟩
  apply LinearMap.ext
  intro q
  induction q using Submodule.Quotient.induction_on with
  | H y => exact hGy y

/-- **Card `(VSG.11)`.**  The kernel of restriction is the line spanned by the zero-adele
endpoint. -/
theorem ker_ccmRationalAdelicPrimeResidualRestrictLM (p : Nat.Primes) :
    LinearMap.ker (ccmRationalAdelicPrimeResidualRestrictLM p) =
      (ℂ ∙ (⟨ccmRationalAdelicBruhatZeroEval,
        ccmRationalAdelicBruhatZeroEval_mem_shearAnnihilator p⟩ :
          ccmRationalAdelicPrimeShearAnnihilator p)) := by
  apply le_antisymm
  · intro ell hell
    have hzero : ∀ y : Core, ccmRationalAdelicBruhatZeroEval y = 0 →
        (ell : Module.Dual ℂ Core) y = 0 := by
      intro y hy
      have := LinearMap.congr_fun (LinearMap.mem_ker.mp hell)
        (Submodule.Quotient.mk (⟨y, hy⟩ : LinearMap.ker ccmRationalAdelicBruhatZeroEval))
      exact this
    refine Submodule.mem_span_singleton.2
      ⟨(ell : Module.Dual ℂ Core) ccmRationalAdelicUnitWitness, ?_⟩
    refine Subtype.ext ?_
    apply LinearMap.ext
    intro x
    have hshift : ccmRationalAdelicBruhatZeroEval
        (x - ccmRationalAdelicBruhatZeroEval x • ccmRationalAdelicUnitWitness) = 0 := by
      rw [map_sub, map_smul, ccmRationalAdelicUnitWitness_zeroEval, smul_eq_mul, mul_one,
        sub_self]
    have hkey := hzero _ hshift
    rw [map_sub, map_smul, sub_eq_zero] at hkey
    simp only [Submodule.coe_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [hkey, smul_eq_mul]
    ring
  · rw [Submodule.span_le, Set.singleton_subset_iff]
    apply LinearMap.mem_ker.mpr
    apply LinearMap.ext
    intro q
    induction q using Submodule.Quotient.induction_on with
    | H y => exact y.2

/-- **Theorem B, card `(VSG.11)` boxed.**  The effective cohomological Stokes ambiguity is the
algebraic dual of the residual quotient. -/
def ccmRationalAdelicPrimeAmbiguityEquiv (p : Nat.Primes) :
    (ccmRationalAdelicPrimeShearAnnihilator p ⧸
        (ℂ ∙ (⟨ccmRationalAdelicBruhatZeroEval,
          ccmRationalAdelicBruhatZeroEval_mem_shearAnnihilator p⟩ :
            ccmRationalAdelicPrimeShearAnnihilator p))) ≃ₗ[ℂ]
      Module.Dual ℂ (CCMRationalAdelicPrimeResidualQuotient p) :=
  (Submodule.quotEquivOfEq _ _ (ker_ccmRationalAdelicPrimeResidualRestrictLM p).symm).trans
    (LinearMap.quotKerEquivOfSurjective _
      (ccmRationalAdelicPrimeResidualRestrictLM_surjective p))

/-- **Card `(VSG.11a)`.**  The descended Haar covector on the residual quotient. -/
def ccmRationalAdelicPrimeResidualHaar (p : Nat.Primes) :
    Module.Dual ℂ (CCMRationalAdelicPrimeResidualQuotient p) :=
  ccmRationalAdelicPrimeResidualRestrictLM p
    ⟨ccmRationalAdelicBruhatIntegral,
      ccmRationalAdelicBruhatIntegral_mem_shearAnnihilator p⟩

/-- **Card `(VSG.11a)`.**  The descended Haar covector is nonzero, so the ambiguity space is
nonzero: the Haar shear line is a genuine nontrivial subtorsor. -/
theorem ccmRationalAdelicPrimeResidualHaar_ne_zero (p : Nat.Primes) :
    ccmRationalAdelicPrimeResidualHaar p ≠ 0 := by
  intro hzero
  apply ccmRationalAdelicHaarWitness_integral_ne_zero p
  have := LinearMap.congr_fun hzero
    (Submodule.Quotient.mk (⟨ccmRationalAdelicHaarWitness p,
      ccmRationalAdelicHaarWitness_mem_ker p⟩ :
        LinearMap.ker ccmRationalAdelicBruhatZeroEval))
  exact this

end RHTower

end
