import Mathlib

/-!
# Soldering transport defect and the first-order law symbol

The defect of a family of local solderings against a pair of transports is a twisted cocycle when
the transports are strict, and obeys an exact curved transgression identity when they are not.  An
additive change of soldering changes the defect by a coboundary.

The second half is the first-order obstruction: over a square-zero thickening the multiplication
symbol determines whether a map of head layers lifts, and the obstruction is the class of the
composite symbol in the cokernel of precomposition.
-/

namespace HTGeometry.ConstraintRelativity

/-! ## The bivariant transport defect -/

section Defect

variable {R : Type*} [CommRing R]
variable {KA KB KC TA TB TC : Type*}
  [AddCommGroup KA] [Module R KA] [AddCommGroup KB] [Module R KB] [AddCommGroup KC] [Module R KC]
  [AddCommGroup TA] [Module R TA] [AddCommGroup TB] [Module R TB] [AddCommGroup TC] [Module R TC]

/-- **Card `(3)`.**  The soldering transport defect of an edge. -/
def bivariantDefect (Kf : KA →ₗ[R] KB) (Tf : TA →ₗ[R] TB) (sA : KA →ₗ[R] TA)
    (sB : KB →ₗ[R] TB) : KA →ₗ[R] TB :=
  Tf ∘ₗ sA - sB ∘ₗ Kf

/-- **Card `(5a)`.**  The intrinsic transport curvature of a composable pair. -/
def transportCurvature (Kf : KA →ₗ[R] KB) (Kg : KB →ₗ[R] KC) (Kgf : KA →ₗ[R] KC) :
    KA →ₗ[R] KC :=
  Kg ∘ₗ Kf - Kgf

/-- **Card `(5b)`.**  The curved Bianchi / transgression identity: the failure of the defect to be
a cocycle is the soldered difference of the two transport curvatures. -/
theorem bivariantDefect_curved (Kf : KA →ₗ[R] KB) (Kg : KB →ₗ[R] KC) (Kgf : KA →ₗ[R] KC)
    (Tf : TA →ₗ[R] TB) (Tg : TB →ₗ[R] TC) (Tgf : TA →ₗ[R] TC)
    (sA : KA →ₗ[R] TA) (sB : KB →ₗ[R] TB) (sC : KC →ₗ[R] TC) :
    Tg ∘ₗ bivariantDefect Kf Tf sA sB + bivariantDefect Kg Tg sB sC ∘ₗ Kf
        - bivariantDefect Kgf Tgf sA sC
      = transportCurvature Tf Tg Tgf ∘ₗ sA - sC ∘ₗ transportCurvature Kf Kg Kgf := by
  ext x
  simp only [bivariantDefect, transportCurvature, LinearMap.add_apply, LinearMap.sub_apply,
    LinearMap.comp_apply, map_sub]
  abel

/-- **Card `(4)`.**  With strict transports the defect is a twisted one-cocycle. -/
theorem bivariantDefect_cocycle {Kf : KA →ₗ[R] KB} {Kg : KB →ₗ[R] KC} {Kgf : KA →ₗ[R] KC}
    {Tf : TA →ₗ[R] TB} {Tg : TB →ₗ[R] TC} {Tgf : TA →ₗ[R] TC}
    (hK : Kgf = Kg ∘ₗ Kf) (hT : Tgf = Tg ∘ₗ Tf)
    (sA : KA →ₗ[R] TA) (sB : KB →ₗ[R] TB) (sC : KC →ₗ[R] TC) :
    bivariantDefect Kgf Tgf sA sC
      = Tg ∘ₗ bivariantDefect Kf Tf sA sB + bivariantDefect Kg Tg sB sC ∘ₗ Kf := by
  have hcurv := bivariantDefect_curved Kf Kg Kgf Tf Tg Tgf sA sB sC
  have hKz : transportCurvature Kf Kg Kgf = 0 := by
    rw [transportCurvature, hK, sub_self]
  have hTz : transportCurvature Tf Tg Tgf = 0 := by
    rw [transportCurvature, hT, sub_self]
  rw [hKz, hTz] at hcurv
  simp only [LinearMap.zero_comp, LinearMap.comp_zero, sub_zero] at hcurv
  linear_combination (norm := module) -hcurv

/-- **Card `(5)`.**  An additive change of soldering changes the defect by a coboundary. -/
theorem bivariantDefect_gauge (Kf : KA →ₗ[R] KB) (Tf : TA →ₗ[R] TB)
    (sA hA : KA →ₗ[R] TA) (sB hB : KB →ₗ[R] TB) :
    bivariantDefect Kf Tf (sA + hA) (sB + hB) - bivariantDefect Kf Tf sA sB
      = Tf ∘ₗ hA - hB ∘ₗ Kf := by
  ext x
  simp only [bivariantDefect, LinearMap.sub_apply, LinearMap.add_apply, LinearMap.comp_apply,
    map_add]
  abel

/-- **Card `(7)`.**  Bianchi consistency for a source current: any current realizing the defect
obeys the same curved law. -/
theorem source_current_consistency {Kf : KA →ₗ[R] KB} {Kg : KB →ₗ[R] KC} {Kgf : KA →ₗ[R] KC}
    {Tf : TA →ₗ[R] TB} {Tg : TB →ₗ[R] TC} {Tgf : TA →ₗ[R] TC}
    {sA : KA →ₗ[R] TA} {sB : KB →ₗ[R] TB} {sC : KC →ₗ[R] TC}
    {Jf : KA →ₗ[R] TB} {Jg : KB →ₗ[R] TC} {Jgf : KA →ₗ[R] TC}
    (hf : Jf = bivariantDefect Kf Tf sA sB) (hg : Jg = bivariantDefect Kg Tg sB sC)
    (hgf : Jgf = bivariantDefect Kgf Tgf sA sC) :
    Tg ∘ₗ Jf + Jg ∘ₗ Kf - Jgf
      = transportCurvature Tf Tg Tgf ∘ₗ sA - sC ∘ₗ transportCurvature Kf Kg Kgf := by
  rw [hf, hg, hgf]
  exact bivariantDefect_curved Kf Kg Kgf Tf Tg Tgf sA sB sC

end Defect

/-! ## The literal Route-R scalar two-curvature -/

section RouteR

/-- **Card `(5c)`.**  The depth mass. -/
noncomputable def depthMass (e : ℕ) : ℝ := (2 : ℝ) ^ (-((e : ℤ) + 1))

/-- **Card `(5c)`.**  The depth frequency. -/
noncomputable def depthFreq (e : ℕ) : ℝ := ((e : ℝ) + 1) * Real.log 2

/-- **Card `(5c)`.**  The antisymmetric depth pairing. -/
noncomputable def depthTheta (e f : ℕ) : ℝ := depthMass e * depthFreq f - depthMass f * depthFreq e

theorem depthTheta_01 : depthTheta 0 1 = (3 / 4) * Real.log 2 := by
  simp only [depthTheta, depthMass, depthFreq]
  norm_num
  ring

theorem depthTheta_12 : depthTheta 1 2 = (1 / 2) * Real.log 2 := by
  simp only [depthTheta, depthMass, depthFreq]
  norm_num
  ring

theorem depthTheta_02 : depthTheta 0 2 = (11 / 8) * Real.log 2 := by
  simp only [depthTheta, depthMass, depthFreq]
  norm_num
  ring

/-- **Card `(5e)`.**  The depth pairing fails the cocycle identity by an explicit nonzero amount. -/
theorem depthTheta_defect :
    depthTheta 0 1 + depthTheta 1 2 - depthTheta 0 2 = -(1 / 8) * Real.log 2 := by
  rw [depthTheta_01, depthTheta_12, depthTheta_02]
  ring

theorem depthTheta_defect_ne_zero :
    depthTheta 0 1 + depthTheta 1 2 - depthTheta 0 2 ≠ 0 := by
  rw [depthTheta_defect]
  have := Real.log_pos (by norm_num : (1:ℝ) < 2)
  intro hcon
  nlinarith

/-- **Card `(5f)`.**  The scalar transport curvature of the depth chart. -/
noncomputable def depthCurvature (c : ℝ) : ℝ :=
  Real.exp (c * depthTheta 1 2) * Real.exp (c * depthTheta 0 1) - Real.exp (c * depthTheta 0 2)

/-- **Card `(5g)`.**  Its derivative at zero drift is the nonzero cocycle defect: Route R needs a
curved two-transport. -/
theorem hasDerivAt_depthCurvature :
    HasDerivAt depthCurvature (depthTheta 0 1 + depthTheta 1 2 - depthTheta 0 2) 0 := by
  have h1 : HasDerivAt (fun c : ℝ => Real.exp (c * depthTheta 1 2)) (depthTheta 1 2) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const (depthTheta 1 2)).exp
    simpa using this
  have h2 : HasDerivAt (fun c : ℝ => Real.exp (c * depthTheta 0 1)) (depthTheta 0 1) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const (depthTheta 0 1)).exp
    simpa using this
  have h3 : HasDerivAt (fun c : ℝ => Real.exp (c * depthTheta 0 2)) (depthTheta 0 2) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const (depthTheta 0 2)).exp
    simpa using this
  have hcomb := (h1.mul h2).sub h3
  have hfun : (fun c : ℝ => Real.exp (c * depthTheta 1 2) * Real.exp (c * depthTheta 0 1)
      - Real.exp (c * depthTheta 0 2)) = depthCurvature := rfl
  have hcomb' : HasDerivAt depthCurvature
      (depthTheta 1 2 + depthTheta 0 1 - depthTheta 0 2) 0 := by
    simpa [Pi.mul_def, Pi.sub_def, hfun] using hcomb
  have hval : depthTheta 1 2 + depthTheta 0 1 - depthTheta 0 2
      = depthTheta 0 1 + depthTheta 1 2 - depthTheta 0 2 := by ring
  rwa [hval] at hcomb'

theorem deriv_depthCurvature_ne_zero :
    deriv depthCurvature 0 ≠ 0 := by
  rw [hasDerivAt_depthCurvature.deriv]
  exact depthTheta_defect_ne_zero

end RouteR

/-! ## The first-order law symbol -/

section LawSymbol

set_option maxHeartbeats 1000000

variable {k A : Type*} [Field k] [CommRing A] [Algebra k A] (m : Ideal A)
variable {M : Type*} [AddCommGroup M] [Module A M] [Module k M] [IsScalarTower k A M]
variable {N : Type*} [AddCommGroup N] [Module A N] [Module k N] [IsScalarTower k A N]

/-- **Card `(8)`.**  The radical layer `mM`, as a `k`-subspace. -/
noncomputable def radLayer (m : Ideal A) (M : Type*) [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] : Submodule k M :=
  Submodule.restrictScalars k (m • (⊤ : Submodule A M))

theorem mem_radLayer_iff {x : M} :
    x ∈ radLayer (k := k) m M ↔ x ∈ m • (⊤ : Submodule A M) :=
  Submodule.restrictScalars_mem _ _ _

theorem smul_mem_radLayer {u : A} (hu : u ∈ m) (x : M) : u • x ∈ radLayer (k := k) m M :=
  (mem_radLayer_iff m).2 (Submodule.smul_mem_smul hu Submodule.mem_top)

/-- **Card `(8)`.**  The head layer `M/mM`. -/
abbrev headLayer (m : Ideal A) (M : Type*) [AddCommGroup M] [Module A M] [Module k M]
    [IsScalarTower k A M] : Type _ := M ⧸ radLayer (k := k) m M

/-- The raw multiplication map of an ideal element. -/
noncomputable def symbolRaw (u : ↥m) : M →ₗ[k] radLayer (k := k) m M where
  toFun x := ⟨(u : A) • x, smul_mem_radLayer m u.2 x⟩
  map_add' x y := by ext; simp [smul_add]
  map_smul' c x := by
    ext
    show (u : A) • (c • x) = c • ((u : A) • x)
    rw [smul_comm]

/-- **Card `(9)`.**  The first-order law symbol, once the square-zero condition holds. -/
noncomputable def symbol (hsq : ∀ (u v : A), u ∈ m → v ∈ m → ∀ x : M, u • v • x = 0) (u : ↥m) :
    headLayer (k := k) m M →ₗ[k] radLayer (k := k) m M := by
  refine Submodule.liftQ (radLayer (k := k) m M) (symbolRaw m u) ?_
  rintro y hy
  refine Subtype.ext ?_
  show (u : A) • y = 0
  rw [mem_radLayer_iff] at hy
  refine Submodule.smul_induction_on (p := fun z => (u : A) • z = 0) hy ?_ ?_
  · intro v hv z _
    exact hsq (u : A) v u.2 hv z
  · intro y z hy' hz'
    rw [smul_add, hy', hz', add_zero]

@[simp] theorem symbol_mk (hsq : ∀ (u v : A), u ∈ m → v ∈ m → ∀ x : M, u • v • x = 0) (u : ↥m)
    (x : M) :
    (symbol m hsq u (Submodule.Quotient.mk x : headLayer (k := k) m M) : M) = (u : A) • x := rfl

/-- **Card `(9)`.**  The symbol kills `m²`: it descends to `W = m/m²`. -/
theorem symbol_eq_zero_of_mem_sq (hsq : ∀ (u v : A), u ∈ m → v ∈ m → ∀ x : M, u • v • x = 0)
    (u v : ↥m) (x : headLayer (k := k) m M) :
    symbol m hsq ⟨(u : A) * (v : A), Ideal.mul_mem_left _ _ v.2⟩ x = 0 := by
  induction x using Submodule.Quotient.induction_on with
  | H y =>
    refine Subtype.ext ?_
    show ((u : A) * (v : A)) • y = 0
    rw [mul_smul]
    exact hsq (u : A) (v : A) u.2 v.2 y

/-- The induced map of head layers. -/
noncomputable def headMap (φ : M →ₗ[A] N) : headLayer (k := k) m M →ₗ[k] headLayer (k := k) m N :=
  Submodule.mapQ _ _ (φ.restrictScalars k) (by
    rintro y hy
    rw [mem_radLayer_iff] at hy
    refine Submodule.smul_induction_on (p := fun z => φ z ∈ radLayer (k := k) m N) hy ?_ ?_
    · intro v hv z _
      rw [map_smul]
      exact smul_mem_radLayer m hv (φ z)
    · intro y z hy' hz'
      rw [map_add]
      exact Submodule.add_mem _ hy' hz')

/-- The induced map of radical layers. -/
noncomputable def radMap (φ : M →ₗ[A] N) :
    radLayer (k := k) m M →ₗ[k] radLayer (k := k) m N :=
  LinearMap.restrict (φ.restrictScalars k) (fun y hy => by
    rw [mem_radLayer_iff] at hy
    refine Submodule.smul_induction_on (p := fun z => φ z ∈ radLayer (k := k) m N) hy ?_ ?_
    · intro v hv z _
      rw [map_smul]
      exact smul_mem_radLayer m hv (φ z)
    · intro y z hy' hz'
      rw [map_add]
      exact Submodule.add_mem _ hy' hz')

/-- **Card `(10)`.**  A lift intertwines the symbols. -/
theorem symbol_intertwine (hsqM : ∀ (u v : A), u ∈ m → v ∈ m → ∀ x : M, u • v • x = 0)
    (hsqN : ∀ (u v : A), u ∈ m → v ∈ m → ∀ x : N, u • v • x = 0)
    (φ : M →ₗ[A] N) (u : ↥m) (h : headLayer (k := k) m M) :
    radMap m φ (symbol m hsqM u h) = symbol m hsqN u (headMap m φ h) := by
  induction h using Submodule.Quotient.induction_on with
  | H x =>
    refine Subtype.ext ?_
    show φ ((u : A) • x) = (u : A) • φ x
    rw [map_smul]

/-- **Card `(10)`, sufficiency.**  A radical-layer map intertwining the symbols assembles a lift,
given the coefficient splitting `A = k ⊕ m`. -/
theorem exists_lift_of_symbol_compat
    (hsqM : ∀ (u v : A), u ∈ m → v ∈ m → ∀ x : M, u • v • x = 0)
    (hsqN : ∀ (u v : A), u ∈ m → v ∈ m → ∀ x : N, u • v • x = 0)
    (hsplit : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ m)
    (f : headLayer (k := k) m M →ₗ[k] headLayer (k := k) m N)
    (g : radLayer (k := k) m M →ₗ[k] radLayer (k := k) m N)
    (hcompat : ∀ (u : ↥m) (h : headLayer (k := k) m M),
      g (symbol m hsqM u h) = symbol m hsqN u (f h)) :
    ∃ φ : M →ₗ[A] N,
      headMap (k := k) m φ = f ∧
      (∀ x : M, x ∈ radLayer (k := k) m M → ∀ hx : x ∈ radLayer (k := k) m M,
        φ x = (g ⟨x, hx⟩ : N)) := by
  classical
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (radLayer (k := k) m M)
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl (radLayer (k := k) m N)
  set prM : M →ₗ[k] radLayer (k := k) m M :=
    Submodule.projectionOnto _ _ hC with hprM
  set secN : headLayer (k := k) m N →ₗ[k] N :=
    D.subtype ∘ₗ (Submodule.quotientEquivOfIsCompl _ _ hD : _ ≃ₗ[k] D).toLinearMap with hsecN
  have hsecN_mk : ∀ y : headLayer (k := k) m N,
      (Submodule.Quotient.mk (secN y) : headLayer (k := k) m N) = y := fun y =>
    Submodule.mk_quotientEquivOfIsCompl_apply hD y
  set φ₀ : M →ₗ[k] N :=
    (radLayer (k := k) m N).subtype ∘ₗ g ∘ₗ prM
      + secN ∘ₗ f ∘ₗ (radLayer (k := k) m M).mkQ with hφ₀
  have hrad : ∀ (x : M) (hx : x ∈ radLayer (k := k) m M), φ₀ x = (g ⟨x, hx⟩ : N) := by
    intro x hx
    have h1 : prM x = ⟨x, hx⟩ := by
      rw [hprM]
      exact Submodule.projectionOnto_apply_left hC ⟨x, hx⟩
    have h2 : (Submodule.Quotient.mk x : headLayer (k := k) m M) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).2 hx
    rw [hφ₀]
    simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.mkQ_apply, h1, h2, map_zero,
      Submodule.subtype_apply, add_zero]
  have hAlin : ∀ (a : A) (x : M), φ₀ (a • x) = a • φ₀ x := by
    intro a x
    obtain ⟨c, hc⟩ := hsplit a
    have hax : a • x = (algebraMap k A c) • x + (a - algebraMap k A c) • x := by
      rw [← add_smul]
      ring_nf
    have hk : (algebraMap k A c) • x = c • x := algebraMap_smul A c x
    set u : ↥m := ⟨a - algebraMap k A c, hc⟩ with hu
    have hmem : (u : A) • x ∈ radLayer (k := k) m M := smul_mem_radLayer m u.2 x
    have hleft : φ₀ ((u : A) • x) = (g ⟨(u : A) • x, hmem⟩ : N) := hrad _ hmem
    have hsym : (g ⟨(u : A) • x, hmem⟩ : N)
        = (u : A) • secN (f (Submodule.Quotient.mk x)) := by
      have hEq : (⟨(u : A) • x, hmem⟩ : radLayer (k := k) m M)
          = symbol m hsqM u (Submodule.Quotient.mk x) := by
        refine Subtype.ext ?_
        rw [symbol_mk]
      rw [hEq, hcompat u (Submodule.Quotient.mk x)]
      set y := f (Submodule.Quotient.mk x) with hydef
      conv_lhs => rw [← hsecN_mk y]
      exact symbol_mk m hsqN u (secN y)
    have hright : (u : A) • φ₀ x = (u : A) • secN (f (Submodule.Quotient.mk x)) := by
      rw [hφ₀]
      simp only [LinearMap.add_apply, LinearMap.comp_apply, smul_add, Submodule.mkQ_apply]
      have hzero : (u : A) • ((radLayer (k := k) m N).subtype (g (prM x))) = 0 := by
        have hmemN : (g (prM x) : N) ∈ m • (⊤ : Submodule A N) :=
          (mem_radLayer_iff m).1 (g (prM x)).2
        refine Submodule.smul_induction_on (p := fun z => (u : A) • z = 0) hmemN ?_ ?_
        · intro v hv z _
          exact hsqN (u : A) v u.2 hv z
        · intro y z hy' hz'
          rw [smul_add, hy', hz', add_zero]
      rw [hzero, zero_add]
    have hasum : algebraMap k A c + (u : A) = a := by rw [hu]; ring
    calc φ₀ (a • x) = φ₀ ((algebraMap k A c) • x) + φ₀ ((u : A) • x) := by
          rw [← map_add, ← hax]
      _ = c • φ₀ x + (u : A) • φ₀ x := by rw [hk, map_smul, hleft, hsym, hright]
      _ = (algebraMap k A c) • φ₀ x + (u : A) • φ₀ x := by rw [algebraMap_smul]
      _ = a • φ₀ x := by rw [← add_smul, hasum]
  refine ⟨{ toFun := φ₀, map_add' := φ₀.map_add, map_smul' := fun a x => hAlin a x }, ?_,
    fun x _ hx => hrad x hx⟩
  refine LinearMap.ext fun h => ?_
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  show (Submodule.Quotient.mk (φ₀ x) : headLayer (k := k) m N) = f (Submodule.Quotient.mk x)
  rw [hφ₀]
  simp only [LinearMap.add_apply, LinearMap.comp_apply, Submodule.mkQ_apply,
    Submodule.subtype_apply]
  rw [Submodule.Quotient.mk_add,
    (Submodule.Quotient.mk_eq_zero _).2 (g (prM x)).2, zero_add, hsecN_mk]

/-- **Card `(11)`.**  The first-order obstruction of a head map. -/
noncomputable def lawObstruction
    (_hsqM : ∀ (u v : A), u ∈ m → v ∈ m → ∀ x : M, u • v • x = 0)
    (hsqN : ∀ (u v : A), u ∈ m → v ∈ m → ∀ x : N, u • v • x = 0)
    (f : headLayer (k := k) m M →ₗ[k] headLayer (k := k) m N) :
    (↥m → (headLayer (k := k) m M →ₗ[k] radLayer (k := k) m N)) :=
  fun u => symbol m hsqN u ∘ₗ f

/-- **Card `(11)`, boxed.**  A head map lifts to a source-linear comparison exactly when its
first-order obstruction is a precomposition of the symbol.  The forward direction assembles the
lift from a chosen coefficient complement; the backward direction takes the radical-layer map
induced by the lift itself. -/
theorem lift_iff_obstruction_eq
    (hsqM : ∀ (u v : A), u ∈ m → v ∈ m → ∀ x : M, u • v • x = 0)
    (hsqN : ∀ (u v : A), u ∈ m → v ∈ m → ∀ x : N, u • v • x = 0)
    (hsplit : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ m)
    (f : headLayer (k := k) m M →ₗ[k] headLayer (k := k) m N) :
    (∃ g : radLayer (k := k) m M →ₗ[k] radLayer (k := k) m N,
        lawObstruction m hsqM hsqN f = fun u => g ∘ₗ symbol m hsqM u)
      ↔ ∃ φ : M →ₗ[A] N, headMap (k := k) m φ = f := by
  constructor
  · rintro ⟨g, hg⟩
    have hcompat : ∀ (u : ↥m) (h : headLayer (k := k) m M),
        g (symbol m hsqM u h) = symbol m hsqN u (f h) := by
      intro u h
      have := congrArg (fun F => F u h) hg
      simpa [lawObstruction] using this.symm
    obtain ⟨ψ, hψ, _⟩ := exists_lift_of_symbol_compat m hsqM hsqN hsplit f g hcompat
    exact ⟨ψ, hψ⟩
  · rintro ⟨φ, rfl⟩
    refine ⟨radMap m φ, ?_⟩
    funext u
    refine LinearMap.ext fun h => ?_
    exact (symbol_intertwine m hsqM hsqN φ u h).symm

/-- **Card `(11)`.**  The vanishing of the obstruction produces a lift. -/
theorem exists_lift_of_obstruction_eq
    (hsqM : ∀ (u v : A), u ∈ m → v ∈ m → ∀ x : M, u • v • x = 0)
    (hsqN : ∀ (u v : A), u ∈ m → v ∈ m → ∀ x : N, u • v • x = 0)
    (hsplit : ∀ a : A, ∃ c : k, a - algebraMap k A c ∈ m)
    (f : headLayer (k := k) m M →ₗ[k] headLayer (k := k) m N)
    (h : ∃ g : radLayer (k := k) m M →ₗ[k] radLayer (k := k) m N,
      lawObstruction m hsqM hsqN f = fun u => g ∘ₗ symbol m hsqM u) :
    ∃ φ : M →ₗ[A] N, headMap (k := k) m φ = f :=
  (lift_iff_obstruction_eq m hsqM hsqN hsplit f).1 h

end LawSymbol

end HTGeometry.ConstraintRelativity
