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

/-! ## Theorem C: known source symmetries do not remove the Haar shear -/

/-- **Card `(VSG.11b)`.**  The rational-scaling cochain automorphism. -/
def ccmRationalAdelicPrimeScalingCochain (k : CCMRationalAdelicScaling) : One →ₗ[ℂ] One :=
  (ccmRationalAdelicBruhatScaling k).prodMap LinearMap.id

/-- The scaling cochain map is a genuine chain map over the scaling of the source. -/
theorem ccmRationalAdelicPrimeScalingCochain_comm_D0 (p : Nat.Primes)
    (k : CCMRationalAdelicScaling) :
    (ccmRationalAdelicPrimeScalingCochain k).comp (ccmRationalAdelicPrimeRelativeD0 p) =
      (ccmRationalAdelicPrimeRelativeD0 p).comp (ccmRationalAdelicBruhatScaling k) := by
  apply LinearMap.ext
  intro x
  refine Prod.ext ?_ ?_
  · change ccmRationalAdelicBruhatScaling k (ccmRationalAdelicPrimeScaling p • x - x) =
      ccmRationalAdelicPrimeScaling p • (k • x) - k • x
    rw [map_sub]
    congr 1
    change k • (ccmRationalAdelicPrimeScaling p • x) =
      ccmRationalAdelicPrimeScaling p • (k • x)
    rw [smul_smul, smul_smul, mul_comm]
  · change ccmRationalAdelicBruhatZeroEval x =
      ccmRationalAdelicBruhatZeroEval (k • x)
    rw [ccmRationalAdelicBruhatZeroEval_smul]

theorem ccmRationalAdelicPrimeScalingCochain_comm_D1 (k : CCMRationalAdelicScaling) :
    ccmRationalAdelicPrimeRelativeD1.comp (ccmRationalAdelicPrimeScalingCochain k) =
      ccmRationalAdelicPrimeRelativeD1.comp
        ((ccmRationalAdelicBruhatScaling k).prodMap LinearMap.id) := rfl

/-- **Card `(VSG.11c)` boxed.**  Rational scalings commute with every Haar shear, because the Haar
endpoint trace is scaling invariant. -/
theorem ccmRationalAdelicPrimeScalingCochain_comm_haarShear
    (k : CCMRationalAdelicScaling) (lam : ℂ) :
    (ccmRationalAdelicPrimeScalingCochain k).comp
        (ccmRationalAdelicPrimeVerticalShear (lam • ccmRationalAdelicBruhatIntegral)) =
      (ccmRationalAdelicPrimeVerticalShear (lam • ccmRationalAdelicBruhatIntegral)).comp
        (ccmRationalAdelicPrimeScalingCochain k) := by
  apply LinearMap.ext
  intro w
  refine Prod.ext rfl ?_
  change w.2 + lam * ccmRationalAdelicBruhatIntegral w.1 =
    w.2 + lam * ccmRationalAdelicBruhatIntegral (ccmRationalAdelicBruhatScaling k w.1)
  rw [show ccmRationalAdelicBruhatScaling k w.1 = k • w.1 from rfl,
    ccmRationalAdelicBruhatIntegral_smul]

/-- **Card `(VSG.11d)`.**  The literal anti-linear Real structure in degree one. -/
def ccmRationalAdelicPrimeRelativeReal (w : One) : One :=
  (ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma w.1, star w.2)

theorem ccmRationalAdelicPrimeRelativeReal_involutive (w : One) :
    ccmRationalAdelicPrimeRelativeReal (ccmRationalAdelicPrimeRelativeReal w) = w := by
  refine Prod.ext ?_ ?_
  · exact ccmRationalAdelicBruhatSimpleTensor_sigma_sq w.1
  · exact star_star w.2

/-- The Real structure is a chain map over the source involution. -/
theorem ccmRationalAdelicPrimeRelativeReal_D0 (p : Nat.Primes) (x : Core) :
    ccmRationalAdelicPrimeRelativeReal (ccmRationalAdelicPrimeRelativeD0 p x) =
      ccmRationalAdelicPrimeRelativeD0 p
        (ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma x) := by
  refine Prod.ext ?_ ?_
  · change ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma
      (ccmRationalAdelicPrimeScaling p • x - x) =
      ccmRationalAdelicPrimeScaling p •
        ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma x -
        ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma x
    rw [map_sub, ccmRationalAdelicBruhatScaling_sigma]
  · change star (ccmRationalAdelicBruhatZeroEval x) =
      ccmRationalAdelicBruhatZeroEval
        (ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma x)
    rw [ccmRationalAdelicBruhatZeroEval_real]

/-- **Card `(VSG.11e)` boxed.**  The Real involution conjugates the Haar shear parameter. -/
theorem ccmRationalAdelicPrimeRelativeReal_haarShear (lam : ℂ) (w : One) :
    ccmRationalAdelicPrimeRelativeReal
        (ccmRationalAdelicPrimeVerticalShear
          (lam • ccmRationalAdelicBruhatIntegral) w) =
      ccmRationalAdelicPrimeVerticalShear (star lam • ccmRationalAdelicBruhatIntegral)
        (ccmRationalAdelicPrimeRelativeReal w) := by
  refine Prod.ext rfl ?_
  change star (w.2 + lam * ccmRationalAdelicBruhatIntegral w.1) =
    star w.2 + star lam * ccmRationalAdelicBruhatIntegral
      (ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma w.1)
  rw [ccmRationalAdelicBruhatIntegral_real, star_add, star_mul']

/-- **Card `(VSG.11e)`.**  Exactly the real Haar shears commute with the Real involution. -/
theorem ccmRationalAdelicPrimeRelativeReal_commutes_haarShear_iff (p : Nat.Primes) (lam : ℂ) :
    (∀ w : One, ccmRationalAdelicPrimeRelativeReal
        (ccmRationalAdelicPrimeVerticalShear
          (lam • ccmRationalAdelicBruhatIntegral) w) =
      ccmRationalAdelicPrimeVerticalShear (lam • ccmRationalAdelicBruhatIntegral)
        (ccmRationalAdelicPrimeRelativeReal w)) ↔ star lam = lam := by
  constructor
  · intro hcomm
    have hw := hcomm ((ccmRationalAdelicHaarWitness p), (0 : ℂ))
    rw [ccmRationalAdelicPrimeRelativeReal_haarShear] at hw
    have hsnd := congrArg Prod.snd hw
    change star (0 : ℂ) + star lam * ccmRationalAdelicBruhatIntegral
        (ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma
          (ccmRationalAdelicHaarWitness p)) =
      star (0 : ℂ) + lam * ccmRationalAdelicBruhatIntegral
        (ccmRationalAdelicBruhatSimpleTensorKRealEven.sigma
          (ccmRationalAdelicHaarWitness p)) at hsnd
    rw [ccmRationalAdelicBruhatIntegral_real] at hsnd
    have hne : star (ccmRationalAdelicBruhatIntegral (ccmRationalAdelicHaarWitness p)) ≠ 0 := by
      simpa using ccmRationalAdelicHaarWitness_integral_ne_zero p
    simp only [star_zero, zero_add] at hsnd
    exact mul_right_cancel₀ hne hsnd
  · intro hlam w
    rw [ccmRationalAdelicPrimeRelativeReal_haarShear, hlam]

/-- **Card `(VSG.13)`, `(VSG.15)`.**  The shear changes the strict resolved comparison by the
resolved boundary of an explicit degree-minus-one homotopy. -/
theorem ccmRationalAdelicPrimeXiComparison_shear_homotopy (p : Nat.Primes)
    (ell : Module.Dual ℂ Core) (w : One) :
    ccmRationalAdelicPrimeRelativeXiComparison1 p
        (ccmRationalAdelicPrimeVerticalShear ell w) -
      ccmRationalAdelicPrimeRelativeXiComparison1 p w =
      primeDepthBVWoldXiResolvedCovariantD0
        (ell w.1 • primeDepthBVWoldXiPrimeLocalizedLeadingConormal p) := by
  change (w.2 + ell w.1) •
      primeDepthBVWoldXiResolvedCovariantD0
        (primeDepthBVWoldXiPrimeLocalizedLeadingConormal p) -
      w.2 • primeDepthBVWoldXiResolvedCovariantD0
        (primeDepthBVWoldXiPrimeLocalizedLeadingConormal p) = _
  rw [map_smul, add_smul]
  abel

/-- **Card `(VSG.14)`.**  The homotopy annihilates every relative boundary, so the correction is a
genuine cochain homotopy and not merely a difference. -/
theorem ccmRationalAdelicPrimeXiComparison_shear_homotopy_D0 (p : Nat.Primes)
    {ell : Module.Dual ℂ Core} (hell : ell ∈ ccmRationalAdelicPrimeShearAnnihilator p)
    (x : Core) :
    ell (ccmRationalAdelicPrimeRelativeD0 p x).1 •
      primeDepthBVWoldXiPrimeLocalizedLeadingConormal p = 0 := by
  rw [show (ccmRationalAdelicPrimeRelativeD0 p x).1 =
      ccmRationalAdelicPrimeOrbitDifference p x from rfl,
    (mem_ccmRationalAdelicPrimeShearAnnihilator_iff p ell).1 hell x, zero_smul]

/-! ## Theorem D: full-gauge invariance forces erasure -/

/-- A shear, packaged as an endomorphism of the prime-isotropy complex. -/
def ccmRationalAdelicPrimeVerticalShearHom (p : Nat.Primes)
    {ell : Module.Dual ℂ Core} (hell : ell ∈ ccmRationalAdelicPrimeShearAnnihilator p) :
    DeningerThreeTermHom (ccmRationalAdelicPrimeRelativeComplex p)
      (ccmRationalAdelicPrimeRelativeComplex p) where
  f0 := LinearMap.id
  f1 := ccmRationalAdelicPrimeVerticalShear ell
  f2 := LinearMap.id
  comm0 := by
    change (ccmRationalAdelicPrimeRelativeD0 p).comp LinearMap.id =
      (ccmRationalAdelicPrimeVerticalShear ell).comp (ccmRationalAdelicPrimeRelativeD0 p)
    rw [ccmRationalAdelicPrimeVerticalShear_comp_D0 p hell]
    rfl
  comm1 := rfl

/-- The Haar shear functional is a shear functional for every complex parameter. -/
theorem ccmRationalAdelicPrimeHaarShear_mem (p : Nat.Primes) (lam : ℂ) :
    lam • ccmRationalAdelicBruhatIntegral ∈ ccmRationalAdelicPrimeShearAnnihilator p :=
  Submodule.smul_mem _ lam (ccmRationalAdelicBruhatIntegral_mem_shearAnnihilator p)

/-- The Haar shear moves the Haar witness class by a multiple of the retained class. -/
theorem ccmRationalAdelicPrimeHaarShear_H1map_witness (p : Nat.Primes) (lam : ℂ) :
    (ccmRationalAdelicPrimeVerticalShearHom p
        (ccmRationalAdelicPrimeHaarShear_mem p lam)).H1map
      (Submodule.Quotient.mk (ccmRationalAdelicHaarWitnessCocycle p)) =
      Submodule.Quotient.mk (ccmRationalAdelicHaarWitnessCocycle p) +
        (lam * ccmRationalAdelicBruhatIntegral (ccmRationalAdelicHaarWitness p)) •
          ccmRationalAdelicPrimeRelativeClass p := by
  rw [DeningerThreeTermHom.H1map_mk, ccmRationalAdelicPrimeRelativeClass,
    ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
  congr 1
  refine Subtype.ext (Prod.ext ?_ ?_)
  · change ccmRationalAdelicHaarWitness p =
      ccmRationalAdelicHaarWitness p +
        (lam * ccmRationalAdelicBruhatIntegral (ccmRationalAdelicHaarWitness p)) • (0 : Core)
    rw [smul_zero, add_zero]
  · change (0 : ℂ) + lam * ccmRationalAdelicBruhatIntegral (ccmRationalAdelicHaarWitness p) =
      0 + (lam * ccmRationalAdelicBruhatIntegral (ccmRationalAdelicHaarWitness p)) • (1 : ℂ)
    rw [smul_eq_mul, mul_one]

/-- **Theorem D, card `(VSG.16)` boxed.**  A reader of the first cohomology invariant under the
whole Haar shear line annihilates the retained ordinary-prime class. -/
theorem ccmRationalAdelicPrimeGaugeInvariantReader_erases (p : Nat.Primes)
    {V : Type*} [AddCommGroup V] [Module ℂ V]
    (P : (ccmRationalAdelicPrimeRelativeComplex p).H1 →ₗ[ℂ] V)
    (hinv : ∀ lam : ℂ, ∀ h : (ccmRationalAdelicPrimeRelativeComplex p).H1,
      P ((ccmRationalAdelicPrimeVerticalShearHom p
        (ccmRationalAdelicPrimeHaarShear_mem p lam)).H1map h) = P h) :
    P (ccmRationalAdelicPrimeRelativeClass p) = 0 := by
  set c : ℂ := ccmRationalAdelicBruhatIntegral (ccmRationalAdelicHaarWitness p) with hc
  have hcne : c ≠ 0 := ccmRationalAdelicHaarWitness_integral_ne_zero p
  have hstep := hinv c⁻¹ (Submodule.Quotient.mk (ccmRationalAdelicHaarWitnessCocycle p))
  rw [ccmRationalAdelicPrimeHaarShear_H1map_witness, map_add, map_smul,
    inv_mul_cancel₀ hcne, one_smul] at hstep
  have h2 : P (Submodule.Quotient.mk (ccmRationalAdelicHaarWitnessCocycle p)) +
      P (ccmRationalAdelicPrimeRelativeClass p) =
      P (Submodule.Quotient.mk (ccmRationalAdelicHaarWitnessCocycle p)) + 0 := by
    rw [add_zero]
    exact hstep
  exact add_left_cancel h2

/-! ## Target-coefficient no-go and the constitutive dichotomy -/

/-- **Card §6.**  The physical observer family is homogeneous in its target vector, so homogeneous
linear naturality alone can never select one nonzero coefficient. -/
theorem ccmRationalAdelicPrimeStokesObserver_smul (p : Nat.Primes)
    {V : Type*} [AddCommGroup V] [Module ℂ V] (c : ℂ) (v : V) :
    ccmRationalAdelicPrimeStokesObserver p (c • v) =
      c • ccmRationalAdelicPrimeStokesObserver p v := by
  apply LinearMap.ext
  intro h
  change ccmRationalAdelicPrimeRelativeH1StokesRegulator p h • (c • v) =
    c • (ccmRationalAdelicPrimeRelativeH1StokesRegulator p h • v)
  rw [smul_comm]

/-- **Constitutive-rigidity dichotomy, first horn.**  Treating the vertical shear as gauge forces
the physical target vector to vanish, erasing the retained class. -/
theorem ccmRationalAdelicPrimeGaugeInvariantObserver_target_eq_zero (p : Nat.Primes)
    {V : Type*} [AddCommGroup V] [Module ℂ V] (v : V)
    (hinv : ∀ lam : ℂ, ∀ h : (ccmRationalAdelicPrimeRelativeComplex p).H1,
      ccmRationalAdelicPrimeStokesObserver p v
        ((ccmRationalAdelicPrimeVerticalShearHom p
          (ccmRationalAdelicPrimeHaarShear_mem p lam)).H1map h) =
        ccmRationalAdelicPrimeStokesObserver p v h) :
    v = 0 := by
  have := ccmRationalAdelicPrimeGaugeInvariantReader_erases p
    (ccmRationalAdelicPrimeStokesObserver p v) hinv
  rwa [ccmRationalAdelicPrimeStokesObserver_class] at this

/-- **Constitutive-rigidity dichotomy, second horn.**  Marking a Stokes splitting instead leaves
every target vector available, so no nonerasing gauge-invariant constitutive observer is produced
by the present source data. -/
theorem ccmRationalAdelicPrimeMarkedObserver_target_free (p : Nat.Primes)
    {V : Type*} [AddCommGroup V] [Module ℂ V] (v : V) :
    ccmRationalAdelicPrimeStokesObserver p v (ccmRationalAdelicPrimeRelativeClass p) = v :=
  ccmRationalAdelicPrimeStokesObserver_class p v

end RHTower

end
