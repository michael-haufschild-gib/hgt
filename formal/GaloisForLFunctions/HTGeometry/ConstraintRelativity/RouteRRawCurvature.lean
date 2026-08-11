import Mathlib
import GaloisForLFunctions.RHTower.PrimeDepthBVWoldCurvedSourceDifferential
import GaloisForLFunctions.HTGeometry.ConstraintRelativity.RouteRConeCharacter

/-!
# The raw Route-R reporter and its curvature-corrected stabilization

The raw scalar prime-depth reporter is not a cochain complex away from the centre: on the witness
triangle the composite of its two differentials is multiplication by
`U₀₂ · (2^{−a/8} − 1)`, which vanishes exactly at `a = 0`.

That failure is not an obstruction to ordinary homological encoding.  For any composable pair of
linear maps the enlarged pair `d̃₀ f = (D₀f, f)`, `d̃₁(ω, g) = D₁ω − D₁D₀g` is an ordinary complex
retaining both the raw maps and their exact curvature, and its direct sum with a mapping cone
retains the relative class as well.
-/

open RHTower

namespace HTGeometry.ConstraintRelativity

/-! ## The raw reporter is not a complex off centre -/

section RawCurvature

/-- The cocycle defect of the prime-depth connection on the witness triangle. -/
theorem connection_witness_defect :
    primeDepthBVWoldConnection primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
        + primeDepthBVWoldConnection primeDepthBVWoldWitnessOne primeDepthBVWoldWitnessTwo
        - primeDepthBVWoldConnection primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessTwo
      = -Real.log 2 / 8 := by
  have hswap := primeDepthBVWoldConnection_swap
    primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessTwo
  calc primeDepthBVWoldConnection primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
          + primeDepthBVWoldConnection primeDepthBVWoldWitnessOne primeDepthBVWoldWitnessTwo
          - primeDepthBVWoldConnection primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessTwo
        = primeDepthBVWoldAdditiveCurvature primeDepthBVWoldWitnessZero
            primeDepthBVWoldWitnessOne primeDepthBVWoldWitnessTwo := by
          rw [primeDepthBVWoldAdditiveCurvature, hswap]
          ring
    _ = -Real.log 2 / 8 := primeDepthBVWoldAdditiveCurvature_witness

/-- **Card `(RRC.16)`.**  On the witness triangle the transport ratio is `2^{−a/8}`. -/
theorem transport_witness_ratio (a : ℝ) :
    primeDepthBVWoldTransport a primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne
        * primeDepthBVWoldTransport a primeDepthBVWoldWitnessOne primeDepthBVWoldWitnessTwo
      = (2 : ℝ) ^ (-a / 8)
        * primeDepthBVWoldTransport a primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessTwo := by
  have hdef := connection_witness_defect
  rw [primeDepthBVWoldTransport, primeDepthBVWoldTransport, primeDepthBVWoldTransport,
    ← Real.exp_add, Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), ← Real.exp_add]
  congr 1
  linear_combination a * hdef

/-- `2^{−a/8} = 1` exactly at the centre. -/
theorem rpow_neg_div_eq_one_iff (a : ℝ) : (2 : ℝ) ^ (-a / 8) = 1 ↔ a = 0 := by
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), Real.exp_eq_one_iff]
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num : (1:ℝ) < 2)).ne'
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h1
    · exact absurd h1 hlog
    · linarith
  · intro h
    rw [h]
    ring

/-- **Card `(RRC.15)`, `(RRC.17)`.**  The raw curvature on the witness triangle is multiplication
by `U₀₂ · (2^{−a/8} − 1)`. -/
theorem rawCurvature_witness_apply (a : ℝ) (f : PrimeDepthBVWoldZeroCochain) :
    primeDepthBVWoldCovariantD1 a (primeDepthBVWoldCovariantD0 a f)
        primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne primeDepthBVWoldWitnessTwo
      = ((primeDepthBVWoldTransport a primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessTwo
            * ((2 : ℝ) ^ (-a / 8) - 1) : ℝ) : ℂ) * f primeDepthBVWoldWitnessTwo := by
  rw [primeDepthBVWoldCovariantD1_comp_D0_apply, transport_witness_ratio]
  push_cast
  ring

/-- **Card `(RRC.17)`.**  Off the centre the raw curvature is nonzero on any section that does not
vanish at the far vertex. -/
theorem rawCurvature_witness_ne_zero {a : ℝ} (ha : a ≠ 0) (f : PrimeDepthBVWoldZeroCochain)
    (hf : f primeDepthBVWoldWitnessTwo ≠ 0) :
    primeDepthBVWoldCovariantD1 a (primeDepthBVWoldCovariantD0 a f)
        primeDepthBVWoldWitnessZero primeDepthBVWoldWitnessOne primeDepthBVWoldWitnessTwo ≠ 0 := by
  rw [rawCurvature_witness_apply]
  refine mul_ne_zero ?_ hf
  simp only [ne_eq, Complex.ofReal_eq_zero]
  refine mul_ne_zero (primeDepthBVWoldTransport_pos a _ _).ne' ?_
  rw [sub_ne_zero]
  exact fun h => ha ((rpow_neg_div_eq_one_iff a).mp h)

/-- **Card `(RRC.17)`, Theorem A.**  Away from the centre the raw pair of prime-depth reporters is
not a cochain complex. -/
theorem raw_pair_not_complex {a : ℝ} (ha : a ≠ 0) :
    ∃ (f : PrimeDepthBVWoldZeroCochain) (i j k : PrimeDepthBVWoldCell),
      primeDepthBVWoldCovariantD1 a (primeDepthBVWoldCovariantD0 a f) i j k ≠ 0 :=
  ⟨fun _ => 1, primeDepthBVWoldWitnessZero, primeDepthBVWoldWitnessOne,
    primeDepthBVWoldWitnessTwo, rawCurvature_witness_ne_zero ha _ one_ne_zero⟩

end RawCurvature

/-! ## Curvature-corrected stabilization -/

section Stabilization

variable {k : Type} [Field k] {R₀ R₁ R₂ : Type} [AddCommGroup R₀] [Module k R₀]
  [AddCommGroup R₁] [Module k R₁] [AddCommGroup R₂] [Module k R₂]

/-- **Card `(RRC.33)`.**  The stabilized degree-zero map `f ↦ (D₀f, f)`. -/
def stabilizedD₀ (D₀ : R₀ →ₗ[k] R₁) : R₀ →ₗ[k] (R₁ × R₀) :=
  LinearMap.prod D₀ LinearMap.id

/-- **Card `(RRC.33)`.**  The stabilized degree-one map `(ω, g) ↦ D₁ω − D₁D₀g`. -/
def stabilizedD₁ (D₀ : R₀ →ₗ[k] R₁) (D₁ : R₁ →ₗ[k] R₂) : (R₁ × R₀) →ₗ[k] R₂ :=
  D₁.comp (LinearMap.fst k R₁ R₀) - (D₁.comp D₀).comp (LinearMap.snd k R₁ R₀)

/-- **Card `(RRC.34)`.**  The stabilized pair is an ordinary complex: the curvature term cancels
the raw composite exactly. -/
theorem stabilized_d_squared (D₀ : R₀ →ₗ[k] R₁) (D₁ : R₁ →ₗ[k] R₂) (x : R₀) :
    stabilizedD₁ D₀ D₁ (stabilizedD₀ D₀ x) = 0 := by
  show D₁ (D₀ x) - D₁ (D₀ x) = 0
  exact sub_self _

/-- The stabilization loses no data: the enlarged degree-zero map is injective. -/
theorem stabilizedD₀_injective (D₀ : R₀ →ₗ[k] R₁) :
    Function.Injective (stabilizedD₀ D₀) := fun _ _ h => congrArg Prod.snd h

/-- The raw degree-one map is recovered from the stabilization on the first summand. -/
theorem stabilizedD₁_inl (D₀ : R₀ →ₗ[k] R₁) (D₁ : R₁ →ₗ[k] R₂) (ω : R₁) :
    stabilizedD₁ D₀ D₁ (ω, 0) = D₁ ω := by
  show D₁ ω - D₁ (D₀ 0) = D₁ ω
  rw [map_zero, map_zero, sub_zero]

/-- The exact curvature is recovered from the stabilization on the second summand. -/
theorem stabilizedD₁_inr (D₀ : R₀ →ₗ[k] R₁) (D₁ : R₁ →ₗ[k] R₂) (g : R₀) :
    stabilizedD₁ D₀ D₁ (0, g) = -D₁ (D₀ g) := by
  show D₁ 0 - D₁ (D₀ g) = -D₁ (D₀ g)
  rw [map_zero, zero_sub]

/-- **Card `(RRC.32)`–`(RRC.34)`, the countertheorem.**  Every composable pair of linear maps sits
inside an ordinary three-term cochain complex that retains both maps and their exact curvature. -/
noncomputable def stabilizedComplex (D₀ : R₀ →ₗ[k] R₁) (D₁ : R₁ →ₗ[k] R₂) :
    ZCochain k (fun n => (pieceCat (ModuleCat.of k R₀) (ModuleCat.of k (R₁ × R₀))
      (ModuleCat.of k R₂) n : Type)) :=
  truncComplex (stabilizedD₀ D₀) (stabilizedD₁ D₀ D₁) (stabilized_d_squared D₀ D₁)

end Stabilization

/-- **Card `(RRC.32)`.**  The raw Route-R reporter, curvature-corrected. -/
noncomputable def rawStabilizedComplex (a : ℝ) :
    ZCochain ℂ (fun n => (pieceCat (ModuleCat.of ℂ PrimeDepthBVWoldZeroCochain)
      (ModuleCat.of ℂ (PrimeDepthBVWoldOneCochain × PrimeDepthBVWoldZeroCochain))
      (ModuleCat.of ℂ PrimeDepthBVWoldTwoCochain) n : Type)) :=
  stabilizedComplex (primeDepthBVWoldCovariantD0 a) (primeDepthBVWoldCovariantD1 a)

/-! ## Direct sums of cochain complexes -/

section Prod

variable {k : Type*} [Field k] {M N : ℤ → Type*} [∀ n, AddCommGroup (M n)]
  [∀ n, Module k (M n)] [∀ n, AddCommGroup (N n)] [∀ n, Module k (N n)]

/-- The direct sum of two cochain complexes. -/
noncomputable def prodComplex (C : ZCochain k M) (D : ZCochain k N) :
    ZCochain k (fun n => M n × N n) where
  d n := (C.d n).prodMap (D.d n)
  d_squared n x := Prod.ext (C.d_squared n x.1) (D.d_squared n x.2)

variable (C : ZCochain k M) (D : ZCochain k N)

/-- The inclusion of the second summand. -/
noncomputable def prodInr : ZCochainMap D (prodComplex C D) where
  f n := LinearMap.inr k (M n) (N n)
  comm n x := by
    refine Prod.ext ?_ rfl
    show (0 : M (n + 1)) = C.d n 0
    rw [map_zero]

/-- The projection onto the second summand. -/
noncomputable def prodSnd : ZCochainMap (prodComplex C D) D where
  f n := LinearMap.snd k (M n) (N n)
  comm _ _ := rfl

/-- The inclusion is split by the projection on cohomology. -/
theorem prodSnd_prodInr_cohomologyMap (n : ℤ) (z : D.cohomology n) :
    (prodSnd C D).cohomologyMap n ((prodInr C D).cohomologyMap n z) = z := by
  obtain ⟨c, rfl⟩ := D.cls_surjective n z
  rw [ZCochainMap.cohomologyMap_cls, ZCochainMap.cohomologyMap_cls]
  congr 1

/-- Consequently the direct sum retains every nonzero class of the second summand. -/
theorem prodInr_cohomologyMap_ne_zero (n : ℤ) {z : D.cohomology n} (hz : z ≠ 0) :
    (prodInr C D).cohomologyMap n z ≠ 0 := by
  intro h
  refine hz ?_
  rw [← prodSnd_prodInr_cohomologyMap C D n z, h, map_zero]

end Prod

/-! ## The direct sum retains raw curvature and the relative class -/

section Survivor

variable {A : Type} [AddCommGroup A] [Module ℂ A] (S : RouteRSource A) (a : ℝ)

/-- **Card `§7`.**  The direct sum of the curvature-corrected raw complex with the mapping cone of
the universal exactification is an ordinary complex that retains the raw reporter, its exact
curvature, and the nonzero relative cone class.  Excluding such an encoding therefore needs a
naturality, minimality or source-admission axiom, not a homological obstruction. -/
theorem rawStabilized_prod_retains_coneClass :
    (prodInr (rawStabilizedComplex a) (coneComplex S.exactifyMap)).cohomologyMap (-1)
      S.exactifyConeClass ≠ 0 :=
  prodInr_cohomologyMap_ne_zero _ _ (-1) S.exactifyConeClass_ne_zero

end Survivor

end HTGeometry.ConstraintRelativity
