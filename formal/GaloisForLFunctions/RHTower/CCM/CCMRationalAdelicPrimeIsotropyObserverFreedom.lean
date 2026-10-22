import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicPrimeIsotropyStokesRegulator
import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicEpsilonOne
import GaloisForLFunctions.RHTower.PrimeFirstTraceGammaCofinalNormalizerFrontier
import GaloisForLFunctions.HTGeometry.GaussianSchwartz

/-!
# Observer-coefficient freedom on the rational-adelic prime-isotropy `H¹`

The relative prime-isotropy complex of one ordinary prime is

`A --D₀--> A ⊕ ℂ --D₁--> ℂ`,  `D₀x = (Tx, ε₀x)`,  `D₁(y,z) = ε₀y`,  `T = α_p - 1`,

and the bilateral orbit Stokes primitive satisfies `R_p T = ε₀`.  Its first cohomology therefore
splits as an intrinsic residual quotient plus one Stokes line,

`H¹ ≅ (ker ε₀ / im T) ⊕ ℂ`,

by the coordinate change `(y,z) ↦ (y, z - R_p y)`.  The splitting depends on the chosen primitive;
the quotient and the retained class do not.

The strict resolved comparison to the actual Xi complex reads only the isotropy coordinate, so it
annihilates *all* of `H¹` and not merely the retained class.  Consequently every linear observer of
`H¹` descends, and the target coefficient of a descended observer is completely free: for each
vector `v` the Stokes period times `v` is a descended observer sending the retained class to `v`.

The Haar endpoint trace is invariant under every rational scaling, so it annihilates `im T` while
not annihilating `ker ε₀`: an archimedean orbit difference of Gaussians tensored with the
characteristic function of the integral finite adeles has zero value at the zero adele and nonzero
Haar integral.  Hence the residual quotient is nonzero and the Stokes primitive can be moved by an
arbitrary multiple of the Haar trace without breaking either the boundary law or the period-one
normalisation, producing a complex line of distinct cohomology covectors.

Finally the reflection-doubled physical coefficient avoids the origin of `V ⊕ V` throughout the
moderate strip and avoids the coordinate-axis discriminant exactly at neutral grade.
-/

noncomputable section

open MeasureTheory
open GaloisForLFunctions
open GaloisForLFunctions.RHTower

namespace RHTower

private abbrev Arch := CCMRationalArchimedeanSchwartz
private abbrev FinBruhat := CCMRationalFiniteBruhatSchwartz
private abbrev Core := CCMRationalAdelicBruhatSimpleTensor
private abbrev One := CCMRationalAdelicPrimeRelativeOne

/-! ## The residual quotient `Q_p = ker ε₀ / im T` -/

/-- The prime orbit difference `T = α_p - 1` on the actual adelic Bruhat core. -/
def ccmRationalAdelicPrimeOrbitDifference (p : Nat.Primes) : Core →ₗ[ℂ] Core :=
  (LinearMap.fst ℂ Core ℂ).comp (ccmRationalAdelicPrimeRelativeD0 p)

@[simp] theorem ccmRationalAdelicPrimeOrbitDifference_apply (p : Nat.Primes) (x : Core) :
    ccmRationalAdelicPrimeOrbitDifference p x =
      ccmRationalAdelicPrimeScaling p • x - x := rfl

/-- The orbit difference lands in the kernel of the zero-adele endpoint. -/
theorem ccmRationalAdelicPrimeOrbitDifference_mem_ker (p : Nat.Primes) (x : Core) :
    ccmRationalAdelicPrimeOrbitDifference p x ∈
      LinearMap.ker ccmRationalAdelicBruhatZeroEval := by
  rw [LinearMap.mem_ker, ccmRationalAdelicPrimeOrbitDifference_apply, map_sub,
    ccmRationalAdelicBruhatZeroEval_smul, sub_self]

/-- Relations of the residual quotient: orbit differences, viewed inside `ker ε₀`. -/
def ccmRationalAdelicPrimeResidualRelations (p : Nat.Primes) :
    Submodule ℂ (LinearMap.ker ccmRationalAdelicBruhatZeroEval) :=
  (LinearMap.range (ccmRationalAdelicPrimeOrbitDifference p)).comap
    (LinearMap.ker ccmRationalAdelicBruhatZeroEval).subtype

/-- **Card `(OCF.6)`.**  The intrinsic residual quotient `Q_p = ker ε₀ / im T`. -/
abbrev CCMRationalAdelicPrimeResidualQuotient (p : Nat.Primes) : Type :=
  (LinearMap.ker ccmRationalAdelicBruhatZeroEval) ⧸
    ccmRationalAdelicPrimeResidualRelations p

theorem mem_ccmRationalAdelicPrimeResidualRelations_iff (p : Nat.Primes)
    (y : LinearMap.ker ccmRationalAdelicBruhatZeroEval) :
    y ∈ ccmRationalAdelicPrimeResidualRelations p ↔
      ∃ x : Core, ccmRationalAdelicPrimeOrbitDifference p x = (y : Core) :=
  Iff.rfl

/-- A relative one-cocycle has isotropy-free coordinate in `ker ε₀`. -/
theorem ccmRationalAdelicPrimeRelativeCycle_fst_mem_ker (p : Nat.Primes)
    (w : (ccmRationalAdelicPrimeRelativeComplex p).cycles1) :
    (w : One).1 ∈ LinearMap.ker ccmRationalAdelicBruhatZeroEval := w.2

/-! ## Theorem A: the full source `H¹` decomposition -/

/-- The Stokes coordinate change `(y,z) ↦ ([y], z - R_p y)` on relative one-cocycles. -/
def ccmRationalAdelicPrimeRelativeCyclesSplit (p : Nat.Primes) :
    (ccmRationalAdelicPrimeRelativeComplex p).cycles1 →ₗ[ℂ]
      CCMRationalAdelicPrimeResidualQuotient p × ℂ where
  toFun w :=
    (Submodule.Quotient.mk ⟨(w : One).1, ccmRationalAdelicPrimeRelativeCycle_fst_mem_ker p w⟩,
      (w : One).2 - ccmRationalAdelicPrimeOrbitStokesLM p (w : One).1)
  map_add' w v := by
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_add]
      change Submodule.Quotient.mk _ = Submodule.Quotient.mk _ + Submodule.Quotient.mk _
      rw [← Submodule.Quotient.mk_add]
      rfl
    · rw [Prod.snd_add]
      change (w : One).2 + (v : One).2 -
          ccmRationalAdelicPrimeOrbitStokesLM p ((w : One).1 + (v : One).1) =
        ((w : One).2 - ccmRationalAdelicPrimeOrbitStokesLM p (w : One).1) +
          ((v : One).2 - ccmRationalAdelicPrimeOrbitStokesLM p (v : One).1)
      rw [map_add]
      ring
  map_smul' c w := by
    refine Prod.ext ?_ ?_
    · rw [RingHom.id_apply, Prod.smul_fst]
      change Submodule.Quotient.mk _ = c • Submodule.Quotient.mk _
      rw [← Submodule.Quotient.mk_smul]
      rfl
    · rw [RingHom.id_apply, Prod.smul_snd]
      change c * (w : One).2 -
          ccmRationalAdelicPrimeOrbitStokesLM p (c • (w : One).1) =
        c • ((w : One).2 - ccmRationalAdelicPrimeOrbitStokesLM p (w : One).1)
      rw [map_smul]
      simp only [smul_eq_mul]
      ring

@[simp] theorem ccmRationalAdelicPrimeRelativeCyclesSplit_apply (p : Nat.Primes)
    (w : (ccmRationalAdelicPrimeRelativeComplex p).cycles1) :
    ccmRationalAdelicPrimeRelativeCyclesSplit p w =
      (Submodule.Quotient.mk ⟨(w : One).1, ccmRationalAdelicPrimeRelativeCycle_fst_mem_ker p w⟩,
        (w : One).2 - ccmRationalAdelicPrimeOrbitStokesLM p (w : One).1) := rfl

/-- The Stokes coordinate change annihilates every relative boundary. -/
theorem ccmRationalAdelicPrimeRelativeCyclesSplit_boundaries (p : Nat.Primes) :
    (ccmRationalAdelicPrimeRelativeComplex p).boundaries1.comap
        (ccmRationalAdelicPrimeRelativeComplex p).cycles1.subtype ≤
      LinearMap.ker (ccmRationalAdelicPrimeRelativeCyclesSplit p) := by
  intro w hw
  change (w : One) ∈ LinearMap.range (ccmRationalAdelicPrimeRelativeD0 p) at hw
  obtain ⟨x, hx⟩ := hw
  have hfst : ccmRationalAdelicPrimeScaling p • x - x = (w : One).1 := congrArg Prod.fst hx
  have hsnd : ccmRationalAdelicBruhatZeroEval x = (w : One).2 := congrArg Prod.snd hx
  refine Prod.ext ?_ ?_
  · change Submodule.Quotient.mk _ = (0 : CCMRationalAdelicPrimeResidualQuotient p)
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨x, hfst⟩
  · change (w : One).2 - ccmRationalAdelicPrimeOrbitStokesLM p (w : One).1 = 0
    rw [← hfst, ccmRationalAdelicPrimeOrbitStokes_scaling_sub, hsnd, sub_self]

/-- **Card `(OCF.8)`.**  The Stokes splitting on the first relative cohomology. -/
def ccmRationalAdelicPrimeRelativeH1Split (p : Nat.Primes) :
    (ccmRationalAdelicPrimeRelativeComplex p).H1 →ₗ[ℂ]
      CCMRationalAdelicPrimeResidualQuotient p × ℂ :=
  ((ccmRationalAdelicPrimeRelativeComplex p).boundaries1.comap
      (ccmRationalAdelicPrimeRelativeComplex p).cycles1.subtype).liftQ
    (ccmRationalAdelicPrimeRelativeCyclesSplit p)
    (ccmRationalAdelicPrimeRelativeCyclesSplit_boundaries p)

@[simp] theorem ccmRationalAdelicPrimeRelativeH1Split_mk (p : Nat.Primes)
    (w : (ccmRationalAdelicPrimeRelativeComplex p).cycles1) :
    ccmRationalAdelicPrimeRelativeH1Split p (Submodule.Quotient.mk w) =
      ccmRationalAdelicPrimeRelativeCyclesSplit p w := rfl

/-- The residual half of the inverse splitting, before passing to the quotient. -/
def ccmRationalAdelicPrimeResidualToH1Raw (p : Nat.Primes) :
    (LinearMap.ker ccmRationalAdelicBruhatZeroEval) →ₗ[ℂ]
      (ccmRationalAdelicPrimeRelativeComplex p).H1 where
  toFun y := Submodule.Quotient.mk
    ⟨((y : Core), ccmRationalAdelicPrimeOrbitStokesLM p (y : Core)), y.2⟩
  map_add' y v := by
    rw [← Submodule.Quotient.mk_add]
    congr 1
    refine Subtype.ext (Prod.ext rfl ?_)
    exact map_add _ _ _
  map_smul' c y := by
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    refine Subtype.ext (Prod.ext rfl ?_)
    exact map_smul _ _ _

/-- Orbit differences are killed by the inverse splitting: their Stokes lift is a boundary. -/
theorem ccmRationalAdelicPrimeResidualToH1Raw_relations (p : Nat.Primes) :
    ccmRationalAdelicPrimeResidualRelations p ≤
      LinearMap.ker (ccmRationalAdelicPrimeResidualToH1Raw p) := by
  intro y hy
  obtain ⟨x, hx⟩ := hy
  have hx' : ccmRationalAdelicPrimeScaling p • x - x = (y : Core) := hx
  change Submodule.Quotient.mk
    (⟨((y : Core), ccmRationalAdelicPrimeOrbitStokesLM p (y : Core)), y.2⟩ :
      (ccmRationalAdelicPrimeRelativeComplex p).cycles1) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨x, Prod.ext hx' ?_⟩
  change ccmRationalAdelicBruhatZeroEval x =
    ccmRationalAdelicPrimeOrbitStokesLM p (y : Core)
  rw [← hx', ccmRationalAdelicPrimeOrbitStokes_scaling_sub]

/-- **Card `(OCF.9)`, residual half.** -/
def ccmRationalAdelicPrimeResidualToH1 (p : Nat.Primes) :
    CCMRationalAdelicPrimeResidualQuotient p →ₗ[ℂ]
      (ccmRationalAdelicPrimeRelativeComplex p).H1 :=
  (ccmRationalAdelicPrimeResidualRelations p).liftQ
    (ccmRationalAdelicPrimeResidualToH1Raw p)
    (ccmRationalAdelicPrimeResidualToH1Raw_relations p)

/-- **Card `(OCF.9)`, Stokes half.**  The Stokes line inside the first relative cohomology. -/
def ccmRationalAdelicPrimeStokesLineToH1 (p : Nat.Primes) :
    ℂ →ₗ[ℂ] (ccmRationalAdelicPrimeRelativeComplex p).H1 where
  toFun c := Submodule.Quotient.mk ⟨((0 : Core), c), by
    change ccmRationalAdelicBruhatZeroEval (0 : Core) = 0
    exact map_zero _⟩
  map_add' c d := by
    rw [← Submodule.Quotient.mk_add]
    congr 1
  map_smul' c d := by
    rw [← Submodule.Quotient.mk_smul]
    congr 1

/-- **Card `(OCF.9)`.**  Inverse of the Stokes splitting. -/
def ccmRationalAdelicPrimeRelativeH1Unsplit (p : Nat.Primes) :
    CCMRationalAdelicPrimeResidualQuotient p × ℂ →ₗ[ℂ]
      (ccmRationalAdelicPrimeRelativeComplex p).H1 :=
  (ccmRationalAdelicPrimeResidualToH1 p).coprod (ccmRationalAdelicPrimeStokesLineToH1 p)

@[simp] theorem ccmRationalAdelicPrimeResidualToH1_mk (p : Nat.Primes)
    (y : LinearMap.ker ccmRationalAdelicBruhatZeroEval) :
    ccmRationalAdelicPrimeResidualToH1 p (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk
        ⟨((y : Core), ccmRationalAdelicPrimeOrbitStokesLM p (y : Core)), y.2⟩ := rfl

@[simp] theorem ccmRationalAdelicPrimeStokesLineToH1_apply (p : Nat.Primes) (c : ℂ) :
    ccmRationalAdelicPrimeStokesLineToH1 p c =
      Submodule.Quotient.mk ⟨((0 : Core), c), map_zero ccmRationalAdelicBruhatZeroEval⟩ := rfl

theorem ccmRationalAdelicPrimeRelativeH1Split_unsplit (p : Nat.Primes)
    (qc : CCMRationalAdelicPrimeResidualQuotient p × ℂ) :
    ccmRationalAdelicPrimeRelativeH1Split p
      (ccmRationalAdelicPrimeRelativeH1Unsplit p qc) = qc := by
  obtain ⟨q, c⟩ := qc
  induction q using Submodule.Quotient.induction_on with
  | H y =>
    rw [ccmRationalAdelicPrimeRelativeH1Unsplit, LinearMap.coprod_apply,
      ccmRationalAdelicPrimeResidualToH1_mk, ccmRationalAdelicPrimeStokesLineToH1_apply,
      ← Submodule.Quotient.mk_add, ccmRationalAdelicPrimeRelativeH1Split_mk,
      ccmRationalAdelicPrimeRelativeCyclesSplit_apply]
    refine Prod.ext ?_ ?_
    · show Submodule.Quotient.mk _ = Submodule.Quotient.mk y
      congr 1
      refine Subtype.ext ?_
      show (y : Core) + 0 = (y : Core)
      exact add_zero _
    · show ccmRationalAdelicPrimeOrbitStokesLM p (y : Core) + c -
        ccmRationalAdelicPrimeOrbitStokesLM p ((y : Core) + 0) = c
      rw [add_zero]
      ring

theorem ccmRationalAdelicPrimeRelativeH1Unsplit_split (p : Nat.Primes)
    (h : (ccmRationalAdelicPrimeRelativeComplex p).H1) :
    ccmRationalAdelicPrimeRelativeH1Unsplit p
      (ccmRationalAdelicPrimeRelativeH1Split p h) = h := by
  induction h using Submodule.Quotient.induction_on with
  | H w =>
    rw [ccmRationalAdelicPrimeRelativeH1Split_mk, ccmRationalAdelicPrimeRelativeCyclesSplit_apply,
      ccmRationalAdelicPrimeRelativeH1Unsplit, LinearMap.coprod_apply,
      ccmRationalAdelicPrimeResidualToH1_mk, ccmRationalAdelicPrimeStokesLineToH1_apply,
      ← Submodule.Quotient.mk_add]
    congr 1
    refine Subtype.ext (Prod.ext ?_ ?_)
    · show (w : One).1 + 0 = (w : One).1
      exact add_zero _
    · show ccmRationalAdelicPrimeOrbitStokesLM p (w : One).1 +
        ((w : One).2 - ccmRationalAdelicPrimeOrbitStokesLM p (w : One).1) = (w : One).2
      ring

/-- **Theorem A, card `(OCF.7)` boxed.**  The first cohomology of the rational-adelic prime-isotropy
complex is the intrinsic residual quotient plus one Stokes line. -/
def ccmRationalAdelicPrimeRelativeH1Equiv (p : Nat.Primes) :
    (ccmRationalAdelicPrimeRelativeComplex p).H1 ≃ₗ[ℂ]
      CCMRationalAdelicPrimeResidualQuotient p × ℂ :=
  LinearEquiv.ofLinear (ccmRationalAdelicPrimeRelativeH1Split p)
    (ccmRationalAdelicPrimeRelativeH1Unsplit p)
    (LinearMap.ext (ccmRationalAdelicPrimeRelativeH1Split_unsplit p))
    (LinearMap.ext (ccmRationalAdelicPrimeRelativeH1Unsplit_split p))

/-- **Card `(OCF.10)`.**  The retained ordinary-prime class is the Stokes generator. -/
theorem ccmRationalAdelicPrimeRelativeH1Equiv_class (p : Nat.Primes) :
    ccmRationalAdelicPrimeRelativeH1Equiv p (ccmRationalAdelicPrimeRelativeClass p) =
      (0, 1) := by
  change ccmRationalAdelicPrimeRelativeCyclesSplit p
    (ccmRationalAdelicPrimeRelativeCocycle p) = (0, 1)
  rw [ccmRationalAdelicPrimeRelativeCyclesSplit_apply]
  refine Prod.ext ?_ ?_
  · change Submodule.Quotient.mk _ = (0 : CCMRationalAdelicPrimeResidualQuotient p)
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨0, by rw [map_zero]; rfl⟩
  · change (1 : ℂ) - ccmRationalAdelicPrimeOrbitStokesLM p 0 = 1
    rw [map_zero, sub_zero]

/-! ## Theorem B: the resolved comparison kills all of `H¹` -/

/-- **Theorem B, card `(OCF.14)` boxed.**  The strict resolved Route-R comparison sends *every*
class of the source `H¹`, not merely the retained one, to a resolved boundary. -/
theorem ccmRationalAdelicPrimeRelativeXiChainMap_H1map_eq_zero (p : Nat.Primes) :
    (ccmRationalAdelicPrimeRelativeXiChainMap p).H1map = 0 := by
  apply LinearMap.ext
  intro h
  induction h using Submodule.Quotient.induction_on with
  | H w =>
    rw [DeningerThreeTermHom.H1map_mk]
    refine (primeDepthBVWoldXiResolvedThreeTermComplex.H1_mk_eq_zero_iff _).2 ?_
    refine ⟨(w : One).2 • primeDepthBVWoldXiPrimeLocalizedLeadingConormal p, ?_⟩
    change primeDepthBVWoldXiResolvedCovariantD0
        ((w : One).2 • primeDepthBVWoldXiPrimeLocalizedLeadingConormal p) =
      ccmRationalAdelicPrimeRelativeXiComparison1 p (w : One)
    rw [map_smul]
    rfl

/-- **Card `(OCF.15)`.**  Every source class is available to the observer. -/
theorem ker_ccmRationalAdelicPrimeRelativeXiChainMap_H1map (p : Nat.Primes) :
    LinearMap.ker (ccmRationalAdelicPrimeRelativeXiChainMap p).H1map = ⊤ := by
  rw [ccmRationalAdelicPrimeRelativeXiChainMap_H1map_eq_zero, LinearMap.ker_zero]

/-- **Card `(OCF.16)` boxed.**  The observer-descent space of the resolved comparison is the entire
dual-valued space, and the Stokes splitting exhibits it as residual observers plus one free target
vector. -/
def ccmRationalAdelicPrimeObserverDescentEquiv (p : Nat.Primes)
    (V : Type*) [AddCommGroup V] [Module ℂ V] :
    ((ccmRationalAdelicPrimeRelativeComplex p).H1 →ₗ[ℂ] V) ≃ₗ[ℂ]
      ((CCMRationalAdelicPrimeResidualQuotient p →ₗ[ℂ] V) × V) :=
  (LinearEquiv.arrowCongr (ccmRationalAdelicPrimeRelativeH1Equiv p)
      (LinearEquiv.refl ℂ V)).trans
    ((LinearMap.coprodEquiv ℂ).symm.trans
      ((LinearEquiv.refl ℂ (CCMRationalAdelicPrimeResidualQuotient p →ₗ[ℂ] V)).prodCongr
        (LinearMap.ringLmapEquivSelf ℂ ℂ V)))

/-! ## Theorem C: the target coefficient is completely free -/

/-- The descended observer with prescribed target vector: Stokes period times `v`. -/
def ccmRationalAdelicPrimeStokesObserver (p : Nat.Primes)
    {V : Type*} [AddCommGroup V] [Module ℂ V] (v : V) :
    (ccmRationalAdelicPrimeRelativeComplex p).H1 →ₗ[ℂ] V :=
  (LinearMap.toSpanSingleton ℂ V v).comp
    (ccmRationalAdelicPrimeRelativeH1StokesRegulator p)

/-- **Card `(OCF.19)`.**  The prescribed observer sends the retained class to its target vector. -/
@[simp] theorem ccmRationalAdelicPrimeStokesObserver_class (p : Nat.Primes)
    {V : Type*} [AddCommGroup V] [Module ℂ V] (v : V) :
    ccmRationalAdelicPrimeStokesObserver p v (ccmRationalAdelicPrimeRelativeClass p) = v := by
  change ccmRationalAdelicPrimeRelativeH1StokesRegulator p
    (ccmRationalAdelicPrimeRelativeClass p) • v = v
  rw [ccmRationalAdelicPrimeRelativeH1StokesRegulator_class, one_smul]

/-- **Theorem C, card `(OCF.20)`.**  Exact relative-observer duality makes every target coefficient
available: distinct vectors give distinct descended observers, so nothing selects the physical one.
-/
theorem ccmRationalAdelicPrimeStokesObserver_injective (p : Nat.Primes)
    {V : Type*} [AddCommGroup V] [Module ℂ V] :
    Function.Injective
      (fun v : V => ccmRationalAdelicPrimeStokesObserver p v) := by
  intro v w hvw
  have := congrArg (fun φ => φ (ccmRationalAdelicPrimeRelativeClass p)) hvw
  simpa using this

/-! ## Theorem D: the Haar trace produces Stokes ambiguity -/

/-- **Card `(OCF.21)`.**  Rational inverse-scaling invariance makes the Haar endpoint trace
annihilate every prime orbit difference. -/
theorem ccmRationalAdelicBruhatIntegral_orbitDifference (p : Nat.Primes) (x : Core) :
    ccmRationalAdelicBruhatIntegral (ccmRationalAdelicPrimeOrbitDifference p x) = 0 := by
  rw [ccmRationalAdelicPrimeOrbitDifference_apply, map_sub,
    ccmRationalAdelicBruhatIntegral_smul, sub_self]

/-- The integral finite adeles form a compact open, hence clopen, subset. -/
theorem ccmRationalIntegralFiniteAdeles_isClopen :
    IsClopen ccmRationalIntegralFiniteAdeles :=
  ⟨ccmRationalIntegralFiniteAdeles_isCompact.isClosed,
    ccmRationalIntegralFiniteAdeles_isOpen⟩

/-- **Card `(OCF.22b)`.**  The characteristic function of the integral finite adeles is a genuine
finite Bruhat function: locally constant because the set is clopen, compactly supported because it
is compact. -/
def ccmRationalIntegralFiniteAdelesBruhat : FinBruhat :=
  ⟨(LocallyConstant.const CCMRationalFiniteAdele (1 : ℂ)).indicator
      ccmRationalIntegralFiniteAdeles_isClopen, by
    classical
    apply HasCompactSupport.of_support_subset_isCompact
      ccmRationalIntegralFiniteAdeles_isCompact
    intro z hz
    by_contra hmem
    apply hz
    rw [LocallyConstant.indicator_apply_eq_if]
    exact if_neg hmem⟩

open Classical in
theorem ccmRationalIntegralFiniteAdelesBruhat_apply (z : CCMRationalFiniteAdele) :
    (ccmRationalIntegralFiniteAdelesBruhat.1 : CCMRationalFiniteAdele → ℂ) z =
      if z ∈ ccmRationalIntegralFiniteAdeles then 1 else 0 :=
  LocallyConstant.indicator_apply_eq_if _ _ ccmRationalIntegralFiniteAdeles_isClopen

/-- **Card `(OCF.22c)`.**  Its normalized finite Haar integral is one. -/
theorem ccmRationalFiniteBruhatIntegral_integralFiniteAdelesBruhat :
    ccmRationalFiniteBruhatIntegral ccmRationalIntegralFiniteAdelesBruhat = 1 := by
  classical
  have hmeas : MeasurableSet ccmRationalIntegralFiniteAdeles :=
    ccmRationalIntegralFiniteAdeles_isOpen.measurableSet
  have hfun : (fun z => (ccmRationalIntegralFiniteAdelesBruhat.1 :
        CCMRationalFiniteAdele → ℂ) z)
      = Set.indicator ccmRationalIntegralFiniteAdeles (fun _ => (1 : ℂ)) := by
    funext z
    rw [ccmRationalIntegralFiniteAdelesBruhat_apply, Set.indicator_apply]
  rw [ccmRationalFiniteBruhatIntegral_apply]
  change ∫ z, (fun w => (ccmRationalIntegralFiniteAdelesBruhat.1 :
      CCMRationalFiniteAdele → ℂ) w) z ∂ccmRationalFiniteAdeleHaar = 1
  rw [hfun, integral_indicator_const _ hmeas, Measure.real,
    ccmRationalFiniteAdeleHaar_integral_subring]
  norm_num

/-- The total mass of the Gaussian. -/
theorem ccmRationalArchimedeanSchwartzIntegral_gaussianSchwartz :
    ccmRationalArchimedeanSchwartzIntegral gaussianSchwartz = 1 := by
  have h : ∀ x : ℝ, (gaussianSchwartz x) = ((Real.exp (-Real.pi * x ^ (2 : ℕ)) : ℝ) : ℂ) := by
    intro x
    rw [gaussianSchwartz_apply]
    norm_num [gaussReal]
  rw [ccmRationalArchimedeanSchwartzIntegral_apply]
  simp only [h]
  rw [integral_complex_ofReal, integral_gaussian, div_self Real.pi_ne_zero, Real.sqrt_one]
  norm_num

/-- **Card `(OCF.22)`.**  The archimedean witness: an orbit difference of Gaussians.  It vanishes at
the origin and has nonzero total mass, because the archimedean Haar integral is *not* scaling
invariant while the value at the origin is. -/
def ccmRationalArchimedeanHaarWitness (p : Nat.Primes) : Arch :=
  ccmRationalArchimedeanScaling (ccmRationalAdelicPrimeScaling p) gaussianSchwartz -
    gaussianSchwartz

theorem ccmRationalArchimedeanHaarWitness_zero (p : Nat.Primes) :
    ccmRationalArchimedeanHaarWitness p 0 = 0 := by
  change ccmRationalArchimedeanScaling (ccmRationalAdelicPrimeScaling p) gaussianSchwartz 0 -
    gaussianSchwartz 0 = 0
  rw [ccmRationalArchimedeanScaling_apply, mul_zero, sub_self]

theorem ccmRationalArchimedeanSchwartzIntegral_haarWitness (p : Nat.Primes) :
    ccmRationalArchimedeanSchwartzIntegral (ccmRationalArchimedeanHaarWitness p) =
      (p.1 : ℂ) - 1 := by
  rw [ccmRationalArchimedeanHaarWitness, map_sub,
    ccmRationalArchimedeanSchwartzIntegral_scaling,
    ccmRationalArchimedeanSchwartzIntegral_gaussianSchwartz]
  have hval : ((((ccmRationalAdelicPrimeScaling p).val : CCMRationalUnit) : ℚ) : ℝ) =
      (p.1 : ℝ) := by
    norm_num [ccmRationalAdelicPrimeScaling]
  rw [hval, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p.1 : ℝ)), Complex.real_smul]
  norm_num

/-- **Card `(OCF.22)`, `(OCF.24a)`.**  The adelic Haar witness. -/
def ccmRationalAdelicHaarWitness (p : Nat.Primes) : Core :=
  ccmRationalArchimedeanHaarWitness p ⊗ₜ[ℂ] ccmRationalIntegralFiniteAdelesBruhat

/-- **Card `(OCF.23)`.**  Its zero-adele value vanishes. -/
theorem ccmRationalAdelicHaarWitness_zeroEval (p : Nat.Primes) :
    ccmRationalAdelicBruhatZeroEval (ccmRationalAdelicHaarWitness p) = 0 := by
  rw [ccmRationalAdelicHaarWitness, ccmRationalAdelicBruhatZeroEval_tmul,
    ccmRationalArchimedeanHaarWitness_zero, zero_mul]

/-- **Card `(OCF.24a)`.**  Its Haar endpoint trace is `p - 1`. -/
theorem ccmRationalAdelicHaarWitness_integral (p : Nat.Primes) :
    ccmRationalAdelicBruhatIntegral (ccmRationalAdelicHaarWitness p) = (p.1 : ℂ) - 1 := by
  rw [ccmRationalAdelicHaarWitness, ccmRationalAdelicBruhatIntegral_tmul,
    ccmRationalArchimedeanSchwartzIntegral_haarWitness,
    ccmRationalFiniteBruhatIntegral_integralFiniteAdelesBruhat, mul_one]

theorem ccmRationalAdelicHaarWitness_integral_ne_zero (p : Nat.Primes) :
    ccmRationalAdelicBruhatIntegral (ccmRationalAdelicHaarWitness p) ≠ 0 := by
  rw [ccmRationalAdelicHaarWitness_integral, sub_ne_zero]
  intro hcast
  have : (p.1 : ℕ) = 1 := by exact_mod_cast hcast
  exact p.2.one_lt.ne' this

theorem ccmRationalAdelicHaarWitness_mem_ker (p : Nat.Primes) :
    ccmRationalAdelicHaarWitness p ∈ LinearMap.ker ccmRationalAdelicBruhatZeroEval :=
  ccmRationalAdelicHaarWitness_zeroEval p

/-- **Card `(OCF.25)` boxed.**  The residual quotient is nonzero: the Haar witness is not an orbit
difference. -/
theorem ccmRationalAdelicHaarWitness_notMem_residualRelations (p : Nat.Primes) :
    (⟨ccmRationalAdelicHaarWitness p, ccmRationalAdelicHaarWitness_mem_ker p⟩ :
        LinearMap.ker ccmRationalAdelicBruhatZeroEval) ∉
      ccmRationalAdelicPrimeResidualRelations p := by
  rintro ⟨x, hx⟩
  apply ccmRationalAdelicHaarWitness_integral_ne_zero p
  have hx' : ccmRationalAdelicPrimeOrbitDifference p x = ccmRationalAdelicHaarWitness p := hx
  rw [← hx', ccmRationalAdelicBruhatIntegral_orbitDifference]

/-- **Card `(OCF.25)` boxed.**  `Q_p ≠ 0`. -/
theorem ccmRationalAdelicPrimeResidualQuotient_nontrivial (p : Nat.Primes) :
    Nontrivial (CCMRationalAdelicPrimeResidualQuotient p) := by
  refine ⟨⟨Submodule.Quotient.mk
    ⟨ccmRationalAdelicHaarWitness p, ccmRationalAdelicHaarWitness_mem_ker p⟩, 0, ?_⟩⟩
  rw [Ne, Submodule.Quotient.mk_eq_zero]
  exact ccmRationalAdelicHaarWitness_notMem_residualRelations p

/-- **Card `(OCF.26)`.**  The Stokes primitive shifted by an arbitrary multiple of the Haar
endpoint trace. -/
def ccmRationalAdelicPrimeShiftedStokesLM (p : Nat.Primes) (lam : ℂ) : Core →ₗ[ℂ] ℂ :=
  ccmRationalAdelicPrimeOrbitStokesLM p + lam • ccmRationalAdelicBruhatIntegral

/-- **Card `(OCF.27)`.**  Every shifted primitive satisfies the same exact Stokes law. -/
theorem ccmRationalAdelicPrimeShiftedStokes_scaling_sub (p : Nat.Primes) (lam : ℂ) (x : Core) :
    ccmRationalAdelicPrimeShiftedStokesLM p lam
        (ccmRationalAdelicPrimeScaling p • x - x) =
      ccmRationalAdelicBruhatZeroEval x := by
  change ccmRationalAdelicPrimeOrbitStokesLM p (ccmRationalAdelicPrimeScaling p • x - x) +
    lam * ccmRationalAdelicBruhatIntegral (ccmRationalAdelicPrimeScaling p • x - x) = _
  rw [ccmRationalAdelicPrimeOrbitStokes_scaling_sub, map_sub,
    ccmRationalAdelicBruhatIntegral_smul, sub_self, mul_zero, add_zero]

/-- **Card `(OCF.28)`.**  The shifted Stokes reader on the relative degree-one source. -/
def ccmRationalAdelicPrimeShiftedStokesRegulatorLM (p : Nat.Primes) (lam : ℂ) :
    One →ₗ[ℂ] ℂ where
  toFun yz := yz.2 - ccmRationalAdelicPrimeShiftedStokesLM p lam yz.1
  map_add' x y := by
    simp
    ring
  map_smul' c x := by
    simp [smul_eq_mul]
    ring

theorem ccmRationalAdelicPrimeShiftedStokesRegulator_comp_D0 (p : Nat.Primes) (lam : ℂ) :
    (ccmRationalAdelicPrimeShiftedStokesRegulatorLM p lam).comp
      (ccmRationalAdelicPrimeRelativeD0 p) = 0 := by
  apply LinearMap.ext
  intro x
  change ccmRationalAdelicBruhatZeroEval x -
    ccmRationalAdelicPrimeShiftedStokesLM p lam
      (ccmRationalAdelicPrimeScaling p • x - x) = 0
  rw [ccmRationalAdelicPrimeShiftedStokes_scaling_sub, sub_self]

theorem ccmRationalAdelicPrimeShiftedStokes_boundaries_le_ker (p : Nat.Primes) (lam : ℂ) :
    (ccmRationalAdelicPrimeRelativeComplex p).boundaries1.comap
        (ccmRationalAdelicPrimeRelativeComplex p).cycles1.subtype ≤
      LinearMap.ker ((ccmRationalAdelicPrimeShiftedStokesRegulatorLM p lam).comp
        (ccmRationalAdelicPrimeRelativeComplex p).cycles1.subtype) := by
  intro w hw
  change (w : One) ∈ LinearMap.range (ccmRationalAdelicPrimeRelativeD0 p) at hw
  obtain ⟨x, hx⟩ := hw
  change ccmRationalAdelicPrimeShiftedStokesRegulatorLM p lam (w : One) = 0
  rw [← hx]
  exact LinearMap.congr_fun (ccmRationalAdelicPrimeShiftedStokesRegulator_comp_D0 p lam) x

/-- **Card `(OCF.28)`.**  The shifted Stokes period on the first relative cohomology. -/
def ccmRationalAdelicPrimeRelativeH1ShiftedStokes (p : Nat.Primes) (lam : ℂ) :
    (ccmRationalAdelicPrimeRelativeComplex p).H1 →ₗ[ℂ] ℂ :=
  ((ccmRationalAdelicPrimeRelativeComplex p).boundaries1.comap
      (ccmRationalAdelicPrimeRelativeComplex p).cycles1.subtype).liftQ
    ((ccmRationalAdelicPrimeShiftedStokesRegulatorLM p lam).comp
      (ccmRationalAdelicPrimeRelativeComplex p).cycles1.subtype)
    (ccmRationalAdelicPrimeShiftedStokes_boundaries_le_ker p lam)

/-- Every shifted period is still normalized to one on the retained class. -/
theorem ccmRationalAdelicPrimeRelativeH1ShiftedStokes_class (p : Nat.Primes) (lam : ℂ) :
    ccmRationalAdelicPrimeRelativeH1ShiftedStokes p lam
      (ccmRationalAdelicPrimeRelativeClass p) = 1 := by
  change (1 : ℂ) - ccmRationalAdelicPrimeShiftedStokesLM p lam 0 = 1
  rw [map_zero, sub_zero]

/-- The Haar witness as a relative one-cocycle with zero isotropy coordinate. -/
def ccmRationalAdelicHaarWitnessCocycle (p : Nat.Primes) :
    (ccmRationalAdelicPrimeRelativeComplex p).cycles1 :=
  ⟨(ccmRationalAdelicHaarWitness p, 0), ccmRationalAdelicHaarWitness_zeroEval p⟩

/-- **Card `(OCF.28a)`.**  Distinct shifts give distinct cohomology covectors: neither boundary
annihilation nor period-one normalization pins the Stokes covector. -/
theorem ccmRationalAdelicPrimeRelativeH1ShiftedStokes_injective (p : Nat.Primes) :
    Function.Injective
      (fun lam : ℂ => ccmRationalAdelicPrimeRelativeH1ShiftedStokes p lam) := by
  intro lam mu hlm
  have hval := congrArg
    (fun φ => φ (Submodule.Quotient.mk (ccmRationalAdelicHaarWitnessCocycle p))) hlm
  have hexp : ∀ nu : ℂ,
      ccmRationalAdelicPrimeRelativeH1ShiftedStokes p nu
          (Submodule.Quotient.mk (ccmRationalAdelicHaarWitnessCocycle p)) =
        -(ccmRationalAdelicPrimeOrbitStokesLM p (ccmRationalAdelicHaarWitness p)) -
          nu * ccmRationalAdelicBruhatIntegral (ccmRationalAdelicHaarWitness p) := by
    intro nu
    change (0 : ℂ) - (ccmRationalAdelicPrimeOrbitStokesLM p (ccmRationalAdelicHaarWitness p) +
      nu * ccmRationalAdelicBruhatIntegral (ccmRationalAdelicHaarWitness p)) = _
    ring
  simp only [hexp] at hval
  have hsub : (lam - mu) *
      ccmRationalAdelicBruhatIntegral (ccmRationalAdelicHaarWitness p) = 0 := by
    have := sub_eq_zero.mpr hval
    linear_combination -this
  rcases mul_eq_zero.mp hsub with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h (ccmRationalAdelicHaarWitness_integral_ne_zero p)

/-! ## Theorem E: the reflection-doubled observer discriminant -/

/-- **Card `(OCF.29)`.**  The fixed physical quotient `ℂ^𝒫 / ℓ¹(𝒫)`. -/
abbrev CCMRationalPrimeFixedPhysicalSpace : Type :=
  PrimeTraceSequence ⧸ primeFirstTraceSummableIdeal

/-- **Card `(OCF.30)`.**  The reflection-doubled physical observer coefficient at horizontal grade
`t` with divisor scalar `c`. -/
def primeReflectionDoubledObserver (c : ℂ) (t : ℝ) :
    CCMRationalPrimeFixedPhysicalSpace × CCMRationalPrimeFixedPhysicalSpace :=
  (c • primeFixedPhysicalFisherClass (-t), c • primeFixedPhysicalFisherClass t)

/-- **Card `(OCF.35)`.**  The coordinate-axis discriminant of the doubled space. -/
def primeObserverAxisDiscriminant :
    Set (CCMRationalPrimeFixedPhysicalSpace × CCMRationalPrimeFixedPhysicalSpace) :=
  {s | s.1 = 0 ∨ s.2 = 0}

/-- Reflection of the horizontal grade swaps the two doubled components. -/
theorem primeReflectionDoubledObserver_neg (c : ℂ) (t : ℝ) :
    primeReflectionDoubledObserver c (-t) =
      Prod.swap (primeReflectionDoubledObserver c t) := by
  rw [primeReflectionDoubledObserver, primeReflectionDoubledObserver, Prod.swap, neg_neg]

/-- Reflection preserves the coordinate-axis discriminant. -/
theorem primeObserverAxisDiscriminant_swap :
    Prod.swap ⁻¹' primeObserverAxisDiscriminant = primeObserverAxisDiscriminant := by
  ext s
  exact or_comm

theorem primeReflectionDoubledObserver_fst_ne_zero_iff {c : ℂ} (hc : c ≠ 0) {t : ℝ}
    (ht : -1 < t) :
    (primeReflectionDoubledObserver c t).1 ≠ 0 ↔ t ≤ 0 := by
  rw [primeReflectionDoubledObserver, ne_eq, smul_eq_zero, not_or,
    ← ne_eq, ← ne_eq]
  constructor
  · rintro ⟨-, h⟩
    have := (primeFixedPhysicalFisherClass_ne_zero_iff (t := -t) (by linarith)).1 h
    linarith
  · intro h
    exact ⟨hc, (primeFixedPhysicalFisherClass_ne_zero_iff (t := -t) (by linarith)).2
      (by linarith)⟩

theorem primeReflectionDoubledObserver_snd_ne_zero_iff {c : ℂ} (hc : c ≠ 0) {t : ℝ}
    (ht : t < 1) :
    (primeReflectionDoubledObserver c t).2 ≠ 0 ↔ 0 ≤ t := by
  rw [primeReflectionDoubledObserver, ne_eq, smul_eq_zero, not_or, ← ne_eq, ← ne_eq]
  constructor
  · rintro ⟨-, h⟩
    exact (primeFixedPhysicalFisherClass_ne_zero_iff ht).1 h
  · intro h
    exact ⟨hc, (primeFixedPhysicalFisherClass_ne_zero_iff ht).2 h⟩

/-- **Card `(OCF.32)`.**  The doubled physical coefficient never reaches the origin in the moderate
strip. -/
theorem primeReflectionDoubledObserver_ne_zero {c : ℂ} (hc : c ≠ 0) {t : ℝ} (ht : |t| < 1) :
    primeReflectionDoubledObserver c t ≠ 0 := by
  rw [Ne, Prod.ext_iff, not_and_or]
  rcases le_total t 0 with h | h
  · exact Or.inl ((primeReflectionDoubledObserver_fst_ne_zero_iff hc
      (by linarith [(abs_lt.mp ht).1])).2 h)
  · exact Or.inr ((primeReflectionDoubledObserver_snd_ne_zero_iff hc (abs_lt.mp ht).2).2 h)

/-- **Card `(OCF.33)`.**  Positive grade erases the reflected orientation. -/
theorem primeReflectionDoubledObserver_pos {c : ℂ} (hc : c ≠ 0) {t : ℝ} (ht : t < 1)
    (htpos : 0 < t) :
    (primeReflectionDoubledObserver c t).1 = 0 ∧
      (primeReflectionDoubledObserver c t).2 ≠ 0 := by
  refine ⟨?_, (primeReflectionDoubledObserver_snd_ne_zero_iff hc ht).2 htpos.le⟩
  by_contra h
  have := (primeReflectionDoubledObserver_fst_ne_zero_iff hc (by linarith)).1 h
  linarith

/-- **Card `(OCF.34)`.**  Negative grade erases the direct orientation. -/
theorem primeReflectionDoubledObserver_neg_grade {c : ℂ} (hc : c ≠ 0) {t : ℝ} (ht : -1 < t)
    (htneg : t < 0) :
    (primeReflectionDoubledObserver c t).1 ≠ 0 ∧
      (primeReflectionDoubledObserver c t).2 = 0 := by
  refine ⟨(primeReflectionDoubledObserver_fst_ne_zero_iff hc ht).2 htneg.le, ?_⟩
  by_contra h
  have := (primeReflectionDoubledObserver_snd_ne_zero_iff hc (by linarith)).1 h
  linarith

/-- **Theorem E, card `(OCF.36)` boxed.**  The reflection-doubled physical coefficient avoids the
coordinate-axis discriminant exactly at neutral grade. -/
theorem primeReflectionDoubledObserver_notMem_axisDiscriminant_iff
    {c : ℂ} (hc : c ≠ 0) {t : ℝ} (ht : |t| < 1) :
    primeReflectionDoubledObserver c t ∉ primeObserverAxisDiscriminant ↔ t = 0 := by
  have hlt : -1 < t := (abs_lt.mp ht).1
  have hgt : t < 1 := (abs_lt.mp ht).2
  constructor
  · intro hnot
    rw [primeObserverAxisDiscriminant, Set.mem_setOf_eq, not_or] at hnot
    have h1 := (primeReflectionDoubledObserver_fst_ne_zero_iff hc hlt).1 hnot.1
    have h2 := (primeReflectionDoubledObserver_snd_ne_zero_iff hc hgt).1 hnot.2
    linarith
  · rintro rfl
    rw [primeObserverAxisDiscriminant, Set.mem_setOf_eq, not_or]
    exact ⟨(primeReflectionDoubledObserver_fst_ne_zero_iff hc hlt).2 le_rfl,
      (primeReflectionDoubledObserver_snd_ne_zero_iff hc hgt).2 le_rfl⟩

end RHTower

end
