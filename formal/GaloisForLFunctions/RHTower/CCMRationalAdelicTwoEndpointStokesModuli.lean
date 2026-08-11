import GaloisForLFunctions.RHTower.CCMRationalAdelicPrimeIsotropyObserverFreedom

/-!
# Two-endpoint Stokes moduli

Let `A` be a vector space with an endomorphism `α`, put `T = α - 1`, and let `ε₀, ε₁` be two
endpoint forms annihilating `im T`.  Restricting the isotropy coordinate to the simultaneous kernel

`K = ker ε₀ ∩ ker ε₁`

gives the two-term complex `A --D₀--> K ⊕ k`, `D₀x = (Tx, ε₀x)`, whose first cohomology splits by
any Stokes primitive `R` (a functional with `RT = ε₀`) as

`H¹₀₁ ≅ (K / im T) ⊕ k`.

Normalized covectors — those sending the retained class `η = [(0,1)]` to `1` — therefore form an
affine space over the algebraic dual of the two-endpoint coinvariants `K / im T`, and each of them
comes from a Stokes primitive.

Two consequences are opposite in sign.  Positively, the second endpoint collapses exactly: for
every `λ` the primitives `R` and `R + λε₁` induce the *same* normalized covector, because the
isotropy coordinate is now constrained to `ker ε₁`.  Negatively, everything else survives: the
affine space is as large as `(K / im T)^*`.
-/

noncomputable section

namespace RHTower

/-! ## The abstract two-endpoint source -/

section Abstract

variable {k A : Type*} [Field k] [AddCommGroup A] [Module k A]

/-- **Card `(TPS.1)`.**  The orbit difference `T = α - 1`. -/
def twoEndpointOrbitDifference (alpha : A →ₗ[k] A) : A →ₗ[k] A :=
  alpha - LinearMap.id

@[simp] theorem twoEndpointOrbitDifference_apply (alpha : A →ₗ[k] A) (x : A) :
    twoEndpointOrbitDifference alpha x = alpha x - x := rfl

/-- **Card `(TPS.3)`.**  The simultaneous endpoint kernel. -/
def twoEndpointKernel (eps0 eps1 : A →ₗ[k] k) : Submodule k A :=
  LinearMap.ker eps0 ⊓ LinearMap.ker eps1

theorem mem_twoEndpointKernel_iff (eps0 eps1 : A →ₗ[k] k) (y : A) :
    y ∈ twoEndpointKernel eps0 eps1 ↔ eps0 y = 0 ∧ eps1 y = 0 :=
  Iff.rfl

variable (alpha : A →ₗ[k] A) (eps0 eps1 : A →ₗ[k] k)

/-- The orbit difference, corestricted to the simultaneous endpoint kernel. -/
def twoEndpointOrbitDifferenceToKernel
    (h0 : ∀ x : A, eps0 (twoEndpointOrbitDifference alpha x) = 0)
    (h1 : ∀ x : A, eps1 (twoEndpointOrbitDifference alpha x) = 0) :
    A →ₗ[k] twoEndpointKernel eps0 eps1 :=
  (twoEndpointOrbitDifference alpha).codRestrict _ fun x => ⟨h0 x, h1 x⟩

@[simp] theorem twoEndpointOrbitDifferenceToKernel_coe
    (h0 : ∀ x : A, eps0 (twoEndpointOrbitDifference alpha x) = 0)
    (h1 : ∀ x : A, eps1 (twoEndpointOrbitDifference alpha x) = 0) (x : A) :
    ((twoEndpointOrbitDifferenceToKernel alpha eps0 eps1 h0 h1 x :
        twoEndpointKernel eps0 eps1) : A) = alpha x - x := rfl

/-- **Card `(TPS.4)`.**  The two-term two-endpoint complex. -/
def twoEndpointD0
    (h0 : ∀ x : A, eps0 (twoEndpointOrbitDifference alpha x) = 0)
    (h1 : ∀ x : A, eps1 (twoEndpointOrbitDifference alpha x) = 0) :
    A →ₗ[k] (twoEndpointKernel eps0 eps1 × k) :=
  (twoEndpointOrbitDifferenceToKernel alpha eps0 eps1 h0 h1).prod eps0

/-- **Card `(TPS.5)`.**  The two-endpoint first cohomology. -/
abbrev TwoEndpointH1
    (h0 : ∀ x : A, eps0 (twoEndpointOrbitDifference alpha x) = 0)
    (h1 : ∀ x : A, eps1 (twoEndpointOrbitDifference alpha x) = 0) : Type _ :=
  (twoEndpointKernel eps0 eps1 × k) ⧸
    LinearMap.range (twoEndpointD0 alpha eps0 eps1 h0 h1)

/-- **Card `(TPS.5)`.**  The retained class `η = [(0,1)]`. -/
def twoEndpointRetainedClass
    (h0 : ∀ x : A, eps0 (twoEndpointOrbitDifference alpha x) = 0)
    (h1 : ∀ x : A, eps1 (twoEndpointOrbitDifference alpha x) = 0) :
    TwoEndpointH1 alpha eps0 eps1 h0 h1 :=
  Submodule.Quotient.mk (0, 1)

/-- The two-endpoint coinvariants `K / im T`. -/
abbrev TwoEndpointCoinvariants
    (h0 : ∀ x : A, eps0 (twoEndpointOrbitDifference alpha x) = 0)
    (h1 : ∀ x : A, eps1 (twoEndpointOrbitDifference alpha x) = 0) : Type _ :=
  twoEndpointKernel eps0 eps1 ⧸
    LinearMap.range (twoEndpointOrbitDifferenceToKernel alpha eps0 eps1 h0 h1)

variable {alpha eps0 eps1}
variable {h0 : ∀ x : A, eps0 (twoEndpointOrbitDifference alpha x) = 0}
variable {h1 : ∀ x : A, eps1 (twoEndpointOrbitDifference alpha x) = 0}

/-- **Card `(TPS.7)`.**  The Stokes coordinate change, before passing to cohomology. -/
def twoEndpointSplitRaw (R : Module.Dual k A) :
    (twoEndpointKernel eps0 eps1 × k) →ₗ[k]
      (TwoEndpointCoinvariants alpha eps0 eps1 h0 h1 × k) :=
  ((twoEndpointOrbitDifferenceToKernel alpha eps0 eps1 h0 h1).range.mkQ.comp
      (LinearMap.fst k (twoEndpointKernel eps0 eps1) k)).prod
    ((LinearMap.snd k (twoEndpointKernel eps0 eps1) k) -
      (R.comp ((twoEndpointKernel eps0 eps1).subtype.comp
        (LinearMap.fst k (twoEndpointKernel eps0 eps1) k))))

@[simp] theorem twoEndpointSplitRaw_apply (R : Module.Dual k A)
    (w : twoEndpointKernel eps0 eps1 × k) :
    twoEndpointSplitRaw (alpha := alpha) (h0 := h0) (h1 := h1) R w =
      (Submodule.Quotient.mk w.1, w.2 - R (w.1 : A)) := rfl

/-- The coordinate change annihilates every boundary. -/
theorem twoEndpointSplitRaw_boundaries {R : Module.Dual k A}
    (hR : ∀ x : A, R (twoEndpointOrbitDifference alpha x) = eps0 x) :
    LinearMap.range (twoEndpointD0 alpha eps0 eps1 h0 h1) ≤
      LinearMap.ker (twoEndpointSplitRaw (alpha := alpha) (h0 := h0) (h1 := h1) R) := by
  rintro _ ⟨x, rfl⟩
  refine Prod.ext ?_ ?_
  · change Submodule.Quotient.mk _ = (0 : TwoEndpointCoinvariants alpha eps0 eps1 h0 h1)
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨x, rfl⟩
  · change eps0 x - R (alpha x - x) = 0
    rw [show alpha x - x = twoEndpointOrbitDifference alpha x from rfl, hR x, sub_self]

/-- **Card `(TPS.7)`.**  The Stokes coordinate change on the two-endpoint cohomology. -/
def twoEndpointSplit {R : Module.Dual k A}
    (hR : ∀ x : A, R (twoEndpointOrbitDifference alpha x) = eps0 x) :
    TwoEndpointH1 alpha eps0 eps1 h0 h1 →ₗ[k]
      (TwoEndpointCoinvariants alpha eps0 eps1 h0 h1 × k) :=
  (LinearMap.range (twoEndpointD0 alpha eps0 eps1 h0 h1)).liftQ _
    (twoEndpointSplitRaw_boundaries hR)

@[simp] theorem twoEndpointSplit_mk {R : Module.Dual k A}
    (hR : ∀ x : A, R (twoEndpointOrbitDifference alpha x) = eps0 x)
    (w : twoEndpointKernel eps0 eps1 × k) :
    twoEndpointSplit (h0 := h0) (h1 := h1) hR (Submodule.Quotient.mk w) =
      (Submodule.Quotient.mk w.1, w.2 - R (w.1 : A)) := rfl

/-- **Card `(TPS.10)`, coinvariant half. -/
def twoEndpointUnsplitCoinvariants {R : Module.Dual k A}
    (hR : ∀ x : A, R (twoEndpointOrbitDifference alpha x) = eps0 x) :
    TwoEndpointCoinvariants alpha eps0 eps1 h0 h1 →ₗ[k]
      TwoEndpointH1 alpha eps0 eps1 h0 h1 :=
  (LinearMap.range (twoEndpointOrbitDifferenceToKernel alpha eps0 eps1 h0 h1)).liftQ
    ((LinearMap.range (twoEndpointD0 alpha eps0 eps1 h0 h1)).mkQ.comp
      ((LinearMap.id (R := k) (M := twoEndpointKernel eps0 eps1)).prod
        (R.comp (twoEndpointKernel eps0 eps1).subtype)))
    (by
      rintro y ⟨x, hx⟩
      have hx' : alpha x - x = (y : A) := congrArg Subtype.val hx
      change Submodule.Quotient.mk
        ((y, R (y : A)) : twoEndpointKernel eps0 eps1 × k) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      refine ⟨x, Prod.ext hx ?_⟩
      change eps0 x = R (y : A)
      rw [← hx', show alpha x - x = twoEndpointOrbitDifference alpha x from rfl, hR x])

/-- **Card `(TPS.10)`, Stokes half. -/
def twoEndpointUnsplitLine :
    k →ₗ[k] TwoEndpointH1 alpha eps0 eps1 h0 h1 where
  toFun c := Submodule.Quotient.mk ((0 : twoEndpointKernel eps0 eps1), c)
  map_add' c d := by
    rw [← Submodule.Quotient.mk_add]
    congr 1
    exact Prod.ext (add_zero (0 : twoEndpointKernel eps0 eps1)).symm rfl
  map_smul' c d := by
    rw [← Submodule.Quotient.mk_smul]
    congr 1
    exact Prod.ext (smul_zero c).symm rfl

/-- **Card `(TPS.10)`.**  The inverse coordinate change. -/
def twoEndpointUnsplit {R : Module.Dual k A}
    (hR : ∀ x : A, R (twoEndpointOrbitDifference alpha x) = eps0 x) :
    (TwoEndpointCoinvariants alpha eps0 eps1 h0 h1 × k) →ₗ[k]
      TwoEndpointH1 alpha eps0 eps1 h0 h1 :=
  (twoEndpointUnsplitCoinvariants hR).coprod twoEndpointUnsplitLine

@[simp] theorem twoEndpointUnsplitCoinvariants_mk {R : Module.Dual k A}
    (hR : ∀ x : A, R (twoEndpointOrbitDifference alpha x) = eps0 x)
    (y : twoEndpointKernel eps0 eps1) :
    twoEndpointUnsplitCoinvariants (h0 := h0) (h1 := h1) hR (Submodule.Quotient.mk y) =
      Submodule.Quotient.mk ((y, R (y : A)) : twoEndpointKernel eps0 eps1 × k) := rfl

@[simp] theorem twoEndpointUnsplitLine_apply (c : k) :
    twoEndpointUnsplitLine (alpha := alpha) (h0 := h0) (h1 := h1) c =
      Submodule.Quotient.mk ((0 : twoEndpointKernel eps0 eps1), c) := rfl

/-- **Theorem A, card `(TPS.7)`.**  The Stokes splitting is an isomorphism. -/
def twoEndpointH1Equiv {R : Module.Dual k A}
    (hR : ∀ x : A, R (twoEndpointOrbitDifference alpha x) = eps0 x) :
    TwoEndpointH1 alpha eps0 eps1 h0 h1 ≃ₗ[k]
      (TwoEndpointCoinvariants alpha eps0 eps1 h0 h1 × k) :=
  LinearEquiv.ofLinear (twoEndpointSplit hR) (twoEndpointUnsplit hR)
    (by
      apply LinearMap.ext
      rintro ⟨q, c⟩
      simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq]
      induction q using Submodule.Quotient.induction_on with
      | H y =>
        rw [twoEndpointUnsplit, LinearMap.coprod_apply, twoEndpointUnsplitCoinvariants_mk,
          twoEndpointUnsplitLine_apply, ← Submodule.Quotient.mk_add, twoEndpointSplit_mk]
        refine Prod.ext ?_ ?_
        · show Submodule.Quotient.mk _ = Submodule.Quotient.mk y
          congr 1
          exact add_zero _
        · show R (y : A) + c - R (((y + 0 : twoEndpointKernel eps0 eps1)) : A) = c
          rw [add_zero]
          ring)
    (by
      apply LinearMap.ext
      intro h
      simp only [LinearMap.comp_apply, LinearMap.id_coe, id_eq]
      induction h using Submodule.Quotient.induction_on with
      | H w =>
        rw [twoEndpointSplit_mk, twoEndpointUnsplit, LinearMap.coprod_apply,
          twoEndpointUnsplitCoinvariants_mk, twoEndpointUnsplitLine_apply,
          ← Submodule.Quotient.mk_add]
        congr 1
        refine Prod.ext ?_ ?_
        · exact add_zero _
        · show R (w.1 : A) + (w.2 - R (w.1 : A)) = w.2
          ring)

/-- **Card `(TPS.7)`.**  The splitting sends the retained class to the Stokes generator. -/
theorem twoEndpointH1Equiv_retainedClass {R : Module.Dual k A}
    (hR : ∀ x : A, R (twoEndpointOrbitDifference alpha x) = eps0 x) :
    twoEndpointH1Equiv (h0 := h0) (h1 := h1) hR
      (twoEndpointRetainedClass alpha eps0 eps1 h0 h1) = (0, 1) := by
  change twoEndpointSplit hR (Submodule.Quotient.mk
    ((0 : twoEndpointKernel eps0 eps1), (1 : k))) = _
  rw [twoEndpointSplit_mk]
  refine Prod.ext ?_ ?_
  · change Submodule.Quotient.mk _ =
      (0 : TwoEndpointCoinvariants alpha eps0 eps1 h0 h1)
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨0, Subtype.ext (by rw [twoEndpointOrbitDifferenceToKernel_coe, map_zero, sub_zero]; rfl)⟩
  · change (1 : k) - R ((0 : twoEndpointKernel eps0 eps1) : A) = 1
    rw [show (((0 : twoEndpointKernel eps0 eps1)) : A) = 0 from rfl, map_zero, sub_zero]

/-- **Card `(TPS.9)`.**  The normalized covector attached to a Stokes primitive. -/
def twoEndpointStokesCovector {R : Module.Dual k A}
    (hR : ∀ x : A, R (twoEndpointOrbitDifference alpha x) = eps0 x) :
    Module.Dual k (TwoEndpointH1 alpha eps0 eps1 h0 h1) :=
  (LinearMap.snd k (TwoEndpointCoinvariants alpha eps0 eps1 h0 h1) k).comp
    (twoEndpointSplit hR)

@[simp] theorem twoEndpointStokesCovector_mk {R : Module.Dual k A}
    (hR : ∀ x : A, R (twoEndpointOrbitDifference alpha x) = eps0 x)
    (w : twoEndpointKernel eps0 eps1 × k) :
    twoEndpointStokesCovector (h0 := h0) (h1 := h1) hR (Submodule.Quotient.mk w) =
      w.2 - R (w.1 : A) := rfl

theorem twoEndpointStokesCovector_retainedClass {R : Module.Dual k A}
    (hR : ∀ x : A, R (twoEndpointOrbitDifference alpha x) = eps0 x) :
    twoEndpointStokesCovector (h0 := h0) (h1 := h1) hR
      (twoEndpointRetainedClass alpha eps0 eps1 h0 h1) = 1 := by
  change (1 : k) - R ((0 : twoEndpointKernel eps0 eps1) : A) = 1
  rw [show (((0 : twoEndpointKernel eps0 eps1)) : A) = 0 from rfl, map_zero, sub_zero]

/-- **Theorem B, card `(TPS.11)` boxed.**  The Haar direction collapses exactly: shifting the
Stokes primitive by any multiple of the second endpoint does not change the induced covector,
because the isotropy coordinate now lies in `ker ε₁`. -/
theorem twoEndpointStokesCovector_shift_eps1 {R : Module.Dual k A}
    (hR : ∀ x : A, R (twoEndpointOrbitDifference alpha x) = eps0 x) (lam : k)
    (hRlam : ∀ x : A, (R + lam • eps1) (twoEndpointOrbitDifference alpha x) = eps0 x) :
    twoEndpointStokesCovector (h0 := h0) (h1 := h1) hRlam =
      twoEndpointStokesCovector (h0 := h0) (h1 := h1) hR := by
  apply LinearMap.ext
  intro h
  induction h using Submodule.Quotient.induction_on with
  | H w =>
    rw [twoEndpointStokesCovector_mk, twoEndpointStokesCovector_mk]
    change w.2 - (R (w.1 : A) + lam * eps1 (w.1 : A)) = w.2 - R (w.1 : A)
    rw [w.1.2.2, mul_zero, add_zero]

/-- The shifted primitive is still a Stokes primitive. -/
theorem twoEndpointStokes_shift_eps1_isPrimitive {R : Module.Dual k A}
    (hR : ∀ x : A, R (twoEndpointOrbitDifference alpha x) = eps0 x)
    (he1 : ∀ x : A, eps1 (twoEndpointOrbitDifference alpha x) = 0) (lam : k) :
    ∀ x : A, (R + lam • eps1) (twoEndpointOrbitDifference alpha x) = eps0 x := by
  intro x
  change R (twoEndpointOrbitDifference alpha x) +
    lam * eps1 (twoEndpointOrbitDifference alpha x) = eps0 x
  rw [hR x, he1 x, mul_zero, add_zero]

/-- **Card `(TPS.8)` boxed, first half.**  Every functional on the coinvariants perturbs the
Stokes covector, and the result is still normalized. -/
theorem twoEndpointStokesCovector_add_normalized {R : Module.Dual k A}
    (hR : ∀ x : A, R (twoEndpointOrbitDifference alpha x) = eps0 x)
    (L : Module.Dual k (TwoEndpointCoinvariants alpha eps0 eps1 h0 h1)) :
    (twoEndpointStokesCovector (h0 := h0) (h1 := h1) hR +
        L.comp ((LinearMap.fst k (TwoEndpointCoinvariants alpha eps0 eps1 h0 h1) k).comp
          (twoEndpointSplit hR)))
      (twoEndpointRetainedClass alpha eps0 eps1 h0 h1) = 1 := by
  have hclass := twoEndpointH1Equiv_retainedClass (h0 := h0) (h1 := h1) hR
  change twoEndpointStokesCovector (h0 := h0) (h1 := h1) hR
      (twoEndpointRetainedClass alpha eps0 eps1 h0 h1) +
    L ((twoEndpointSplit hR (twoEndpointRetainedClass alpha eps0 eps1 h0 h1)).1) = 1
  rw [twoEndpointStokesCovector_retainedClass]
  change (1 : k) + L ((twoEndpointH1Equiv (h0 := h0) (h1 := h1) hR
    (twoEndpointRetainedClass alpha eps0 eps1 h0 h1)).1) = 1
  rw [hclass]
  simp

/-- **Card `(TPS.8)` boxed, second half.**  Every normalized covector differs from the Stokes
covector by a functional on the coinvariants. -/
theorem twoEndpointNormalizedCovector_sub {R : Module.Dual k A}
    (hR : ∀ x : A, R (twoEndpointOrbitDifference alpha x) = eps0 x)
    (I : Module.Dual k (TwoEndpointH1 alpha eps0 eps1 h0 h1))
    (hI : I (twoEndpointRetainedClass alpha eps0 eps1 h0 h1) = 1) :
    ∃ L : Module.Dual k (TwoEndpointCoinvariants alpha eps0 eps1 h0 h1),
      I = twoEndpointStokesCovector (h0 := h0) (h1 := h1) hR +
        L.comp ((LinearMap.fst k (TwoEndpointCoinvariants alpha eps0 eps1 h0 h1) k).comp
          (twoEndpointSplit hR)) := by
  refine ⟨(I - twoEndpointStokesCovector (h0 := h0) (h1 := h1) hR).comp
    (twoEndpointUnsplitCoinvariants hR), ?_⟩
  apply LinearMap.ext
  intro h
  induction h using Submodule.Quotient.induction_on with
  | H w =>
    change I (Submodule.Quotient.mk w) =
      twoEndpointStokesCovector (h0 := h0) (h1 := h1) hR (Submodule.Quotient.mk w) +
        (I - twoEndpointStokesCovector (h0 := h0) (h1 := h1) hR)
          (twoEndpointUnsplitCoinvariants hR (Submodule.Quotient.mk w.1))
    rw [twoEndpointUnsplitCoinvariants_mk, LinearMap.sub_apply,
      twoEndpointStokesCovector_mk, twoEndpointStokesCovector_mk]
    have hsplit : (Submodule.Quotient.mk w : TwoEndpointH1 alpha eps0 eps1 h0 h1) =
        Submodule.Quotient.mk ((w.1, R (w.1 : A)) : twoEndpointKernel eps0 eps1 × k) +
          (w.2 - R (w.1 : A)) • twoEndpointRetainedClass alpha eps0 eps1 h0 h1 := by
      rw [twoEndpointRetainedClass, ← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_add]
      congr 1
      refine Prod.ext ?_ ?_
      · show w.1 = w.1 + (w.2 - R (w.1 : A)) • (0 : twoEndpointKernel eps0 eps1)
        rw [smul_zero, add_zero]
      · show w.2 = R (w.1 : A) + (w.2 - R (w.1 : A)) • (1 : k)
        rw [smul_eq_mul, mul_one]
        ring
    rw [hsplit, map_add, map_smul, hI, smul_eq_mul, mul_one]
    change I (Submodule.Quotient.mk _) + (w.2 - R (w.1 : A)) =
      w.2 - R (w.1 : A) + (I (Submodule.Quotient.mk _) - (R (w.1 : A) - R (w.1 : A)))
    rw [sub_self, sub_zero]
    ring

/-- **Card `(TPS.8)`.**  Every normalized covector is induced by an honest Stokes primitive:
pull the coinvariant functional back to `K`, extend it to `A`, and subtract. -/
theorem twoEndpointNormalizedCovector_from_primitive {R : Module.Dual k A}
    (hR : ∀ x : A, R (twoEndpointOrbitDifference alpha x) = eps0 x)
    (L : Module.Dual k (TwoEndpointCoinvariants alpha eps0 eps1 h0 h1)) :
    ∃ R' : Module.Dual k A,
      (∀ x : A, R' (twoEndpointOrbitDifference alpha x) = eps0 x) ∧
        ∀ y : twoEndpointKernel eps0 eps1,
          R' (y : A) = R (y : A) - L (Submodule.Quotient.mk y) := by
  obtain ⟨G, hG⟩ := LinearMap.exists_extend
    (L.comp (LinearMap.range
      (twoEndpointOrbitDifferenceToKernel alpha eps0 eps1 h0 h1)).mkQ)
  have hGy : ∀ y : twoEndpointKernel eps0 eps1,
      G (y : A) = L (Submodule.Quotient.mk y) := fun y => LinearMap.congr_fun hG y
  refine ⟨R - G, fun x => ?_, fun y => ?_⟩
  · have hmem : twoEndpointOrbitDifference alpha x ∈ twoEndpointKernel eps0 eps1 :=
      ⟨h0 x, h1 x⟩
    have hzero : G (twoEndpointOrbitDifference alpha x) = 0 := by
      rw [show twoEndpointOrbitDifference alpha x =
        ((⟨twoEndpointOrbitDifference alpha x, hmem⟩ :
          twoEndpointKernel eps0 eps1) : A) from rfl, hGy]
      rw [show (Submodule.Quotient.mk
          (⟨twoEndpointOrbitDifference alpha x, hmem⟩ :
            twoEndpointKernel eps0 eps1) :
          TwoEndpointCoinvariants alpha eps0 eps1 h0 h1) = 0 from
        (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩, map_zero]
    change R (twoEndpointOrbitDifference alpha x) -
      G (twoEndpointOrbitDifference alpha x) = eps0 x
    rw [hR x, hzero, sub_zero]
  · change R (y : A) - G (y : A) = R (y : A) - L (Submodule.Quotient.mk y)
    rw [hGy]

end Abstract

/-! ## Literal rational-adelic instantiation -/

section Literal

open GaloisForLFunctions
open GaloisForLFunctions.RHTower

private abbrev Arch := CCMRationalArchimedeanSchwartz
private abbrev FinBruhat := CCMRationalFiniteBruhatSchwartz
private abbrev Core := CCMRationalAdelicBruhatSimpleTensor

/-- The ordinary-prime scaling as an endomorphism of the actual adelic core. -/
abbrev ccmRationalAdelicPrimeAlpha (p : Nat.Primes) : Core →ₗ[ℂ] Core :=
  ccmRationalAdelicBruhatScaling (ccmRationalAdelicPrimeScaling p)

/-- **Card `(TPS.13)`.**  The zero-adele endpoint annihilates orbit differences. -/
theorem ccmRationalAdelicTwoEndpoint_eps0 (p : Nat.Primes) (x : Core) :
    ccmRationalAdelicBruhatZeroEval
      (twoEndpointOrbitDifference (ccmRationalAdelicPrimeAlpha p) x) = 0 :=
  ccmRationalAdelicPrimeOrbitDifference_mem_ker p x

/-- **Card `(TPS.13)`.**  The Haar endpoint annihilates orbit differences. -/
theorem ccmRationalAdelicTwoEndpoint_eps1 (p : Nat.Primes) (x : Core) :
    ccmRationalAdelicBruhatIntegral
      (twoEndpointOrbitDifference (ccmRationalAdelicPrimeAlpha p) x) = 0 :=
  ccmRationalAdelicBruhatIntegral_orbitDifference p x

/-- **Card `(TPS.13)`.**  The bilateral orbit regulator is a Stokes primitive. -/
theorem ccmRationalAdelicTwoEndpoint_primitive (p : Nat.Primes) (x : Core) :
    ccmRationalAdelicPrimeOrbitStokesLM p
      (twoEndpointOrbitDifference (ccmRationalAdelicPrimeAlpha p) x) =
      ccmRationalAdelicBruhatZeroEval x :=
  ccmRationalAdelicPrimeOrbitStokes_scaling_sub p x

/-- **Card `(TPS.3)`.**  The literal two-endpoint kernel. -/
abbrev CCMRationalAdelicTwoEndpointKernel : Submodule ℂ Core :=
  twoEndpointKernel ccmRationalAdelicBruhatZeroEval ccmRationalAdelicBruhatIntegral

/-- **Card `(TPS.17)`.**  The literal two-endpoint coinvariants. -/
abbrev CCMRationalAdelicTwoEndpointCoinvariants (p : Nat.Primes) : Type :=
  TwoEndpointCoinvariants (ccmRationalAdelicPrimeAlpha p)
    ccmRationalAdelicBruhatZeroEval ccmRationalAdelicBruhatIntegral
    (ccmRationalAdelicTwoEndpoint_eps0 p) (ccmRationalAdelicTwoEndpoint_eps1 p)

/-- **Theorem A instantiated.**  The literal two-endpoint cohomology splits. -/
def ccmRationalAdelicTwoEndpointH1Equiv (p : Nat.Primes) :
    TwoEndpointH1 (ccmRationalAdelicPrimeAlpha p)
        ccmRationalAdelicBruhatZeroEval ccmRationalAdelicBruhatIntegral
        (ccmRationalAdelicTwoEndpoint_eps0 p) (ccmRationalAdelicTwoEndpoint_eps1 p) ≃ₗ[ℂ]
      (CCMRationalAdelicTwoEndpointCoinvariants p × ℂ) :=
  twoEndpointH1Equiv (ccmRationalAdelicTwoEndpoint_primitive p)

/-- **Theorem B instantiated, card `(TPS.11)`.**  The literal Haar direction collapses. -/
theorem ccmRationalAdelicTwoEndpointStokes_haar_collapse (p : Nat.Primes) (lam : ℂ) :
    twoEndpointStokesCovector (h0 := ccmRationalAdelicTwoEndpoint_eps0 p)
        (h1 := ccmRationalAdelicTwoEndpoint_eps1 p)
        (twoEndpointStokes_shift_eps1_isPrimitive
          (ccmRationalAdelicTwoEndpoint_primitive p)
          (ccmRationalAdelicTwoEndpoint_eps1 p) lam) =
      twoEndpointStokesCovector (h0 := ccmRationalAdelicTwoEndpoint_eps0 p)
        (h1 := ccmRationalAdelicTwoEndpoint_eps1 p)
        (ccmRationalAdelicTwoEndpoint_primitive p) :=
  twoEndpointStokesCovector_shift_eps1 _ lam _

/-! ### Bilateral orbit sampling at a rational base -/

/-- The scaling whose inverse label is the sampling base. -/
def ccmRationalScalingOfBase (a : ℚ) (ha : a ≠ 0) : CCMRationalAdelicScaling :=
  ⟨(Units.mk0 a ha)⁻¹⟩

@[simp] theorem ccmRationalScalingOfBase_invLabel (a : ℚ) (ha : a ≠ 0) :
    ((((ccmRationalScalingOfBase a ha).val⁻¹ : CCMRationalUnit) : ℚ) : ℝ) = (a : ℝ) := by
  simp [ccmRationalScalingOfBase]

/-- **Card `(TPS.14)`.**  Bilateral orbit sampling at a rational base. -/
def ccmRationalAdelicOrbitSample (p : Nat.Primes) (a : ℚ) (ha : a ≠ 0) : Core →ₗ[ℂ] ℂ :=
  (ccmRationalAdelicPrimeOrbitStokesLM p).comp
    (ccmRationalAdelicBruhatScaling (ccmRationalScalingOfBase a ha))

/-- **Lemma D, card `(TPS.15)`.**  Universal boundary response: every sampling base reads an orbit
difference as the zero-adele endpoint. -/
theorem ccmRationalAdelicOrbitSample_orbitDifference (p : Nat.Primes) (a : ℚ) (ha : a ≠ 0)
    (x : Core) :
    ccmRationalAdelicOrbitSample p a ha (ccmRationalAdelicPrimeOrbitDifference p x) =
      ccmRationalAdelicBruhatZeroEval x := by
  set k := ccmRationalScalingOfBase a ha with hk
  have hcomm : ccmRationalAdelicBruhatScaling k (ccmRationalAdelicPrimeScaling p • x) =
      ccmRationalAdelicPrimeScaling p • (ccmRationalAdelicBruhatScaling k x) := by
    change k • (ccmRationalAdelicPrimeScaling p • x) =
      ccmRationalAdelicPrimeScaling p • (k • x)
    rw [smul_smul, smul_smul, mul_comm]
  change ccmRationalAdelicPrimeOrbitStokesLM p
    (ccmRationalAdelicBruhatScaling k (ccmRationalAdelicPrimeScaling p • x - x)) = _
  rw [map_sub, hcomm]
  have hstokes := ccmRationalAdelicPrimeOrbitStokes_scaling_sub p
    (ccmRationalAdelicBruhatScaling k x)
  change ccmRationalAdelicPrimeOrbitStokesLM p
      (ccmRationalAdelicPrimeScaling p • (ccmRationalAdelicBruhatScaling k x) -
        ccmRationalAdelicBruhatScaling k x) = _
  rw [hstokes]
  change ccmRationalAdelicBruhatZeroEval (k • x) = _
  rw [ccmRationalAdelicBruhatZeroEval_smul]

/-- **Card `(TPS.16)`.**  The orbit-phase difference of two sampling bases. -/
def ccmRationalAdelicOrbitPhase (p : Nat.Primes) (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Core →ₗ[ℂ] ℂ :=
  ccmRationalAdelicOrbitSample p a ha - ccmRationalAdelicOrbitSample p b hb

/-- Orbit-phase differences annihilate every orbit difference. -/
theorem ccmRationalAdelicOrbitPhase_orbitDifference (p : Nat.Primes) (a b : ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0) (x : Core) :
    ccmRationalAdelicOrbitPhase p a b ha hb (ccmRationalAdelicPrimeOrbitDifference p x) = 0 := by
  change ccmRationalAdelicOrbitSample p a ha (ccmRationalAdelicPrimeOrbitDifference p x) -
    ccmRationalAdelicOrbitSample p b hb (ccmRationalAdelicPrimeOrbitDifference p x) = 0
  rw [ccmRationalAdelicOrbitSample_orbitDifference,
    ccmRationalAdelicOrbitSample_orbitDifference, sub_self]

/-- **Card `(TPS.16)`.**  The orbit-phase covector on the two-endpoint coinvariants. -/
def ccmRationalAdelicOrbitPhaseCovector (p : Nat.Primes) (a b : ℚ) (ha : a ≠ 0) (hb : b ≠ 0) :
    Module.Dual ℂ (CCMRationalAdelicTwoEndpointCoinvariants p) :=
  Submodule.liftQ _
    ((ccmRationalAdelicOrbitPhase p a b ha hb).comp
      CCMRationalAdelicTwoEndpointKernel.subtype)
    (by
      rintro y ⟨x, hx⟩
      have hx' : ccmRationalAdelicPrimeOrbitDifference p x = (y : Core) := congrArg Subtype.val hx
      change ccmRationalAdelicOrbitPhase p a b ha hb (y : Core) = 0
      rw [← hx']
      exact ccmRationalAdelicOrbitPhase_orbitDifference p a b ha hb x)

@[simp] theorem ccmRationalAdelicOrbitPhaseCovector_mk (p : Nat.Primes) (a b : ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0) (y : CCMRationalAdelicTwoEndpointKernel) :
    ccmRationalAdelicOrbitPhaseCovector p a b ha hb (Submodule.Quotient.mk y) =
      ccmRationalAdelicOrbitPhase p a b ha hb (y : Core) := rfl

end Literal

end RHTower

end
