import GaloisForLFunctions.RHTower.CCM.CCMRationalAdelicPrimeIsotropyObserverFreedom

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
private abbrev Core_cCMRationalAdelicPrimeIsotropyObserverFreedom_cCMRationalAdelicTwoEndpointStokesModuli := CCMRationalAdelicBruhatSimpleTensor

/-- The ordinary-prime scaling as an endomorphism of the actual adelic core. -/
abbrev ccmRationalAdelicPrimeAlpha (p : Nat.Primes) : Core_cCMRationalAdelicPrimeIsotropyObserverFreedom_cCMRationalAdelicTwoEndpointStokesModuli →ₗ[ℂ] Core_cCMRationalAdelicPrimeIsotropyObserverFreedom_cCMRationalAdelicTwoEndpointStokesModuli :=
  ccmRationalAdelicBruhatScaling (ccmRationalAdelicPrimeScaling p)

/-- **Card `(TPS.13)`.**  The zero-adele endpoint annihilates orbit differences. -/
theorem ccmRationalAdelicTwoEndpoint_eps0 (p : Nat.Primes) (x : Core_cCMRationalAdelicPrimeIsotropyObserverFreedom_cCMRationalAdelicTwoEndpointStokesModuli) :
    ccmRationalAdelicBruhatZeroEval
      (twoEndpointOrbitDifference (ccmRationalAdelicPrimeAlpha p) x) = 0 :=
  ccmRationalAdelicPrimeOrbitDifference_mem_ker p x

/-- **Card `(TPS.13)`.**  The Haar endpoint annihilates orbit differences. -/
theorem ccmRationalAdelicTwoEndpoint_eps1 (p : Nat.Primes) (x : Core_cCMRationalAdelicPrimeIsotropyObserverFreedom_cCMRationalAdelicTwoEndpointStokesModuli) :
    ccmRationalAdelicBruhatIntegral
      (twoEndpointOrbitDifference (ccmRationalAdelicPrimeAlpha p) x) = 0 :=
  ccmRationalAdelicBruhatIntegral_orbitDifference p x

/-- **Card `(TPS.13)`.**  The bilateral orbit regulator is a Stokes primitive. -/
theorem ccmRationalAdelicTwoEndpoint_primitive (p : Nat.Primes) (x : Core_cCMRationalAdelicPrimeIsotropyObserverFreedom_cCMRationalAdelicTwoEndpointStokesModuli) :
    ccmRationalAdelicPrimeOrbitStokesLM p
      (twoEndpointOrbitDifference (ccmRationalAdelicPrimeAlpha p) x) =
      ccmRationalAdelicBruhatZeroEval x :=
  ccmRationalAdelicPrimeOrbitStokes_scaling_sub p x

/-- **Card `(TPS.3)`.**  The literal two-endpoint kernel. -/
abbrev CCMRationalAdelicTwoEndpointKernel : Submodule ℂ Core_cCMRationalAdelicPrimeIsotropyObserverFreedom_cCMRationalAdelicTwoEndpointStokesModuli :=
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
def ccmRationalAdelicOrbitSample (p : Nat.Primes) (a : ℚ) (ha : a ≠ 0) : Core_cCMRationalAdelicPrimeIsotropyObserverFreedom_cCMRationalAdelicTwoEndpointStokesModuli →ₗ[ℂ] ℂ :=
  (ccmRationalAdelicPrimeOrbitStokesLM p).comp
    (ccmRationalAdelicBruhatScaling (ccmRationalScalingOfBase a ha))

/-- **Lemma D, card `(TPS.15)`.**  Universal boundary response: every sampling base reads an orbit
difference as the zero-adele endpoint. -/
theorem ccmRationalAdelicOrbitSample_orbitDifference (p : Nat.Primes) (a : ℚ) (ha : a ≠ 0)
    (x : Core_cCMRationalAdelicPrimeIsotropyObserverFreedom_cCMRationalAdelicTwoEndpointStokesModuli) :
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
    Core_cCMRationalAdelicPrimeIsotropyObserverFreedom_cCMRationalAdelicTwoEndpointStokesModuli →ₗ[ℂ] ℂ :=
  ccmRationalAdelicOrbitSample p a ha - ccmRationalAdelicOrbitSample p b hb

/-- Orbit-phase differences annihilate every orbit difference. -/
theorem ccmRationalAdelicOrbitPhase_orbitDifference (p : Nat.Primes) (a b : ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0) (x : Core_cCMRationalAdelicPrimeIsotropyObserverFreedom_cCMRationalAdelicTwoEndpointStokesModuli) :
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
      have hx' : ccmRationalAdelicPrimeOrbitDifference p x = (y : Core_cCMRationalAdelicPrimeIsotropyObserverFreedom_cCMRationalAdelicTwoEndpointStokesModuli) := congrArg Subtype.val hx
      change ccmRationalAdelicOrbitPhase p a b ha hb (y : Core_cCMRationalAdelicPrimeIsotropyObserverFreedom_cCMRationalAdelicTwoEndpointStokesModuli) = 0
      rw [← hx']
      exact ccmRationalAdelicOrbitPhase_orbitDifference p a b ha hb x)

@[simp] theorem ccmRationalAdelicOrbitPhaseCovector_mk (p : Nat.Primes) (a b : ℚ)
    (ha : a ≠ 0) (hb : b ≠ 0) (y : CCMRationalAdelicTwoEndpointKernel) :
    ccmRationalAdelicOrbitPhaseCovector p a b ha hb (Submodule.Quotient.mk y) =
      ccmRationalAdelicOrbitPhase p a b ha hb (y : Core_cCMRationalAdelicPrimeIsotropyObserverFreedom_cCMRationalAdelicTwoEndpointStokesModuli) := rfl

end Literal

/-! ## Infinite orbit-phase moduli -/

section Witnesses

open GaloisForLFunctions
open GaloisForLFunctions.RHTower

/-- Sampling an archimedean witness supported inside the fundamental interval `(1,2)` sees exactly
the point of its orbit lying in that interval. -/
theorem ccmRationalArchimedeanPrimeOrbitStokes_of_support (p : Nat.Primes) {a : ℝ}
    (ha1 : 1 ≤ a) (ha2 : a ≤ 7 / 4) (g : Arch)
    (hg : ∀ u : ℝ, u ≤ 1 ∨ 2 ≤ u → g u = 0)
    {k : CCMRationalAdelicScaling}
    (hk : ((((k.val⁻¹ : CCMRationalUnit)) : ℚ) : ℝ) = a) :
    ccmRationalArchimedeanPrimeOrbitStokes p (ccmRationalArchimedeanScaling k g) = g a := by
  have hp2 : (2 : ℝ) ≤ (p.1 : ℝ) := by exact_mod_cast p.2.two_le
  have hppos : (0 : ℝ) < (p.1 : ℝ) := by linarith
  have hval : ∀ x : ℝ, ccmRationalArchimedeanScaling k g x = g (a * x) := by
    intro x
    rw [ccmRationalArchimedeanScaling_apply, hk]
  have hzero : ccmRationalArchimedeanScaling k g 0 = 0 := by
    rw [hval, mul_zero]
    exact hg 0 (Or.inl (by norm_num))
  have hneg : ∀ n : ℕ, ccmRationalArchimedeanScaling k g (((p.1 : ℝ)⁻¹) ^ (n + 1)) -
      ccmRationalArchimedeanScaling k g 0 = 0 := by
    intro n
    rw [hzero, sub_zero, hval]
    refine hg _ (Or.inl ?_)
    have hinv : ((p.1 : ℝ)⁻¹) ^ (n + 1) ≤ 1 / 2 := by
      have h1 : ((p.1 : ℝ)⁻¹) ≤ 1 / 2 := by
        rw [one_div]
        exact inv_anti₀ (by norm_num) hp2
      have h2 : (0 : ℝ) ≤ (p.1 : ℝ)⁻¹ := by positivity
      calc ((p.1 : ℝ)⁻¹) ^ (n + 1) ≤ (1 / 2 : ℝ) ^ (n + 1) :=
            pow_le_pow_left₀ h2 h1 _
        _ ≤ (1 / 2 : ℝ) ^ 1 := by
            apply pow_le_pow_of_le_one (by norm_num) (by norm_num)
            omega
        _ = 1 / 2 := by norm_num
    have hnn : (0 : ℝ) ≤ ((p.1 : ℝ)⁻¹) ^ (n + 1) := by positivity
    nlinarith
  have hpos : ∀ n : ℕ, n ≠ 0 → ccmRationalArchimedeanScaling k g ((p.1 : ℝ) ^ n) = 0 := by
    intro n hn
    rw [hval]
    refine hg _ (Or.inr ?_)
    have hge : (2 : ℝ) ≤ (p.1 : ℝ) ^ n := by
      calc (2 : ℝ) = (2 : ℝ) ^ 1 := by norm_num
        _ ≤ (p.1 : ℝ) ^ 1 := by
            exact pow_le_pow_left₀ (by norm_num) hp2 1
        _ ≤ (p.1 : ℝ) ^ n := by
            apply pow_le_pow_right₀ (by linarith)
            omega
    nlinarith
  rw [ccmRationalArchimedeanPrimeOrbitStokes_eq, tsum_congr hneg, tsum_zero, add_zero,
    tsum_eq_single 0 hpos, pow_zero, hval, mul_one]

/-- Orbit sampling of a simple tensor factors through the finite value at zero. -/
theorem ccmRationalAdelicOrbitSample_tmul (p : Nat.Primes) (a : ℚ) (ha : a ≠ 0)
    (g : Arch) (phi : FinBruhat) :
    ccmRationalAdelicOrbitSample p a ha (g ⊗ₜ[ℂ] phi) =
      phi.1 0 * ccmRationalArchimedeanPrimeOrbitStokes p
        (ccmRationalArchimedeanScaling (ccmRationalScalingOfBase a ha) g) := by
  set k := ccmRationalScalingOfBase a ha with hk
  change ccmRationalArchimedeanPrimeOrbitStokesLM p
    (ccmRationalAdelicFiniteZeroPartialEval
      (ccmRationalAdelicBruhatScaling k (g ⊗ₜ[ℂ] phi))) = _
  rw [ccmRationalAdelicBruhatScaling_tmul, ccmRationalAdelicFiniteZeroPartialEval_tmul]
  have hphi : (ccmRationalFiniteBruhatScaling k phi).1 0 = phi.1 0 := by
    rw [ccmRationalFiniteBruhatScaling_apply, mul_zero]
  rw [hphi, map_smul, smul_eq_mul]
  rfl

/-! ### A finite Bruhat function with vanishing Haar integral -/

/-- The rational scaling with label two. -/
def ccmRationalScalingTwo : CCMRationalAdelicScaling := ⟨Units.mk0 (2 : ℚ) two_ne_zero⟩

/-- **Card `(TPS.19)`, finite factor.**  A finite Bruhat function with zero Haar integral and
nonzero value at the zero adele.  It puts every archimedean witness into `ker ε₁` for free. -/
def ccmRationalFiniteHaarNull : FinBruhat :=
  ccmRationalIntegralFiniteAdelesBruhat -
    (2 : ℂ) • ccmRationalFiniteBruhatScalingLinear ccmRationalScalingTwo
      ccmRationalIntegralFiniteAdelesBruhat

theorem ccmRationalFiniteHaarNull_integral :
    ccmRationalFiniteBruhatIntegral ccmRationalFiniteHaarNull = 0 := by
  rw [ccmRationalFiniteHaarNull, map_sub, map_smul]
  change ccmRationalFiniteBruhatIntegral ccmRationalIntegralFiniteAdelesBruhat -
    (2 : ℂ) * ccmRationalFiniteBruhatIntegral
      (ccmRationalFiniteBruhatScaling ccmRationalScalingTwo
        ccmRationalIntegralFiniteAdelesBruhat) = 0
  rw [ccmRationalFiniteBruhatIntegral_scaling,
    ccmRationalFiniteBruhatIntegral_integralFiniteAdelesBruhat]
  have hlabel : ((((ccmRationalScalingTwo.val : CCMRationalUnit)) : ℚ) : ℝ) = 2 := by
    simp [ccmRationalScalingTwo]
  rw [hlabel]
  norm_num

theorem ccmRationalFiniteHaarNull_zero :
    ccmRationalFiniteHaarNull.1 0 = -1 := by
  have hzero : (0 : CCMRationalFiniteAdele) ∈ ccmRationalIntegralFiniteAdeles :=
    fun _ => zero_mem _
  have hscal : (ccmRationalFiniteBruhatScaling ccmRationalScalingTwo
      ccmRationalIntegralFiniteAdelesBruhat).1 0 =
      ccmRationalIntegralFiniteAdelesBruhat.1 0 := by
    rw [ccmRationalFiniteBruhatScaling_apply, mul_zero]
  have hind : ccmRationalIntegralFiniteAdelesBruhat.1 0 = 1 := by
    rw [ccmRationalIntegralFiniteAdelesBruhat_apply, if_pos hzero]
  change ccmRationalIntegralFiniteAdelesBruhat.1 0 -
    (2 : ℂ) * (ccmRationalFiniteBruhatScaling ccmRationalScalingTwo
      ccmRationalIntegralFiniteAdelesBruhat).1 0 = -1
  rw [hscal, hind]
  norm_num

/-! ### Separating archimedean witnesses -/

/-- **Card `(TPS.18)`.**  Sampling centres accumulating at one from above. -/
def orbitCentre (j : ℕ) : ℚ := 1 + (1 / 2) ^ (j + 1)

theorem orbitCentre_cast (j : ℕ) :
    ((orbitCentre j : ℚ) : ℝ) = 1 + (1 / 2 : ℝ) ^ (j + 1) := by
  rw [orbitCentre]
  push_cast
  ring

theorem orbitPow_le (j : ℕ) : (1 / 2 : ℝ) ^ (j + 1) ≤ 1 / 2 := by
  calc (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2 : ℝ) ^ 1 := by
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ = 1 / 2 := by norm_num

theorem orbitPow_pos (m : ℕ) : (0 : ℝ) < (1 / 2 : ℝ) ^ m := by positivity

theorem one_lt_orbitCentre (j : ℕ) : (1 : ℝ) < ((orbitCentre j : ℚ) : ℝ) := by
  rw [orbitCentre_cast]
  linarith [orbitPow_pos (j + 1)]

theorem orbitCentre_le (j : ℕ) : ((orbitCentre j : ℚ) : ℝ) ≤ 3 / 2 := by
  rw [orbitCentre_cast]
  linarith [orbitPow_le j]

theorem orbitCentre_ne_zero (j : ℕ) : orbitCentre j ≠ 0 := by
  intro hzero
  have := one_lt_orbitCentre j
  rw [hzero] at this
  norm_num at this

theorem orbitRadius_le (j : ℕ) : (1 / 2 : ℝ) ^ (j + 4) ≤ 1 / 16 := by
  calc (1 / 2 : ℝ) ^ (j + 4) ≤ (1 / 2 : ℝ) ^ 4 := by
        exact pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    _ = 1 / 16 := by norm_num

/-- **Card `(TPS.18)`.**  The bump at the `j`-th centre. -/
def orbitBump (j : ℕ) : ContDiffBump (((orbitCentre j : ℚ) : ℝ)) where
  rIn := (1 / 2 : ℝ) ^ (j + 5)
  rOut := (1 / 2 : ℝ) ^ (j + 4)
  rIn_pos := orbitPow_pos _
  rIn_lt_rOut := by
    have hpos := orbitPow_pos (j + 4)
    have hsucc : (1 / 2 : ℝ) ^ (j + 5) = (1 / 2 : ℝ) ^ (j + 4) * (1 / 2) := by
      rw [show j + 5 = (j + 4) + 1 from rfl, pow_succ]
    rw [hsucc]
    linarith

/-- **Card `(TPS.19)`, archimedean factor. -/
def orbitWitnessArch (j : ℕ) : CCMRationalArchimedeanSchwartz := by
  refine HasCompactSupport.toSchwartzMap
    (f := fun x : ℝ => (((orbitBump j) x : ℝ) : ℂ)) ?_ ?_
  · exact (orbitBump j).hasCompactSupport.comp_left (g := fun r : ℝ => (r : ℂ))
      Complex.ofReal_zero
  · exact Complex.ofRealCLM.contDiff.comp (orbitBump j).contDiff

theorem orbitWitnessArch_apply (j : ℕ) (x : ℝ) :
    orbitWitnessArch j x = (((orbitBump j) x : ℝ) : ℂ) := rfl

theorem orbitWitnessArch_centre (j : ℕ) :
    orbitWitnessArch j ((orbitCentre j : ℚ) : ℝ) = 1 := by
  rw [orbitWitnessArch_apply,
    (orbitBump j).one_of_mem_closedBall (by
      simp only [Metric.mem_closedBall, dist_self]
      exact (orbitPow_pos (j + 5)).le)]
  norm_num

theorem orbitWitnessArch_eq_zero (j : ℕ) {x : ℝ}
    (hx : (1 / 2 : ℝ) ^ (j + 4) ≤ |x - ((orbitCentre j : ℚ) : ℝ)|) :
    orbitWitnessArch j x = 0 := by
  rw [orbitWitnessArch_apply,
    (orbitBump j).zero_of_le_dist (by rw [Real.dist_eq]; exact hx)]
  norm_num

/-- The witness vanishes outside the fundamental interval. -/
theorem orbitWitnessArch_eq_zero_of_out (j : ℕ) (u : ℝ) (hu : u ≤ 1 ∨ 2 ≤ u) :
    orbitWitnessArch j u = 0 := by
  refine orbitWitnessArch_eq_zero j ?_
  have hlow := one_lt_orbitCentre j
  have hhigh := orbitCentre_le j
  have hrad := orbitRadius_le j
  rcases hu with hu | hu
  · rw [abs_of_nonpos (by linarith)]
    rw [orbitCentre_cast]
    have hpow : (1 / 2 : ℝ) ^ (j + 4) ≤ (1 / 2 : ℝ) ^ (j + 1) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    linarith
  · rw [abs_of_nonneg (by linarith)]
    linarith

/-- Distinct centres are separated by more than the bump radius. -/
theorem orbitWitnessArch_centre_ne (i j : ℕ) (hij : i ≠ j) :
    orbitWitnessArch j ((orbitCentre i : ℚ) : ℝ) = 0 := by
  refine orbitWitnessArch_eq_zero j ?_
  rw [orbitCentre_cast, orbitCentre_cast]
  have hsimp : (1 + (1 / 2 : ℝ) ^ (i + 1)) - (1 + (1 / 2 : ℝ) ^ (j + 1)) =
      (1 / 2 : ℝ) ^ (i + 1) - (1 / 2 : ℝ) ^ (j + 1) := by ring
  rw [hsimp]
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · rw [abs_of_nonneg (by
      have : (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2 : ℝ) ^ (i + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      linarith)]
    have h1 : (1 / 2 : ℝ) ^ (j + 1) ≤ (1 / 2 : ℝ) ^ (i + 2) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h2 : (1 / 2 : ℝ) ^ (j + 4) ≤ (1 / 2 : ℝ) ^ (i + 2) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h3 : (1 / 2 : ℝ) ^ (i + 2) = (1 / 2 : ℝ) ^ (i + 1) * (1 / 2) := by
      rw [show i + 2 = (i + 1) + 1 from rfl, pow_succ]
    have h4 : (1 / 2 : ℝ) ^ (j + 4) < (1 / 2 : ℝ) ^ (i + 2) := by
      have hstrict : (1 / 2 : ℝ) ^ (j + 4) ≤ (1 / 2 : ℝ) ^ (i + 3) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have hlt3 : (1 / 2 : ℝ) ^ (i + 3) < (1 / 2 : ℝ) ^ (i + 2) := by
        have hp := orbitPow_pos (i + 2)
        have : (1 / 2 : ℝ) ^ (i + 3) = (1 / 2 : ℝ) ^ (i + 2) * (1 / 2) := by
          rw [show i + 3 = (i + 2) + 1 from rfl, pow_succ]
        linarith
      linarith
    linarith
  · rw [abs_of_nonpos (by
      have : (1 / 2 : ℝ) ^ (i + 1) ≤ (1 / 2 : ℝ) ^ (j + 1) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      linarith)]
    have h1 : (1 / 2 : ℝ) ^ (i + 1) ≤ (1 / 2 : ℝ) ^ (j + 2) :=
      pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
    have h3 : (1 / 2 : ℝ) ^ (j + 2) = (1 / 2 : ℝ) ^ (j + 1) * (1 / 2) := by
      rw [show j + 2 = (j + 1) + 1 from rfl, pow_succ]
    have h4 : (1 / 2 : ℝ) ^ (j + 4) < (1 / 2 : ℝ) ^ (j + 2) := by
      have hp := orbitPow_pos (j + 2)
      have h5 : (1 / 2 : ℝ) ^ (j + 4) ≤ (1 / 2 : ℝ) ^ (j + 3) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      have h6 : (1 / 2 : ℝ) ^ (j + 3) = (1 / 2 : ℝ) ^ (j + 2) * (1 / 2) := by
        rw [show j + 3 = (j + 2) + 1 from rfl, pow_succ]
      linarith
    linarith

/-- The base point is outside every witness support. -/
theorem orbitWitnessArch_base (j : ℕ) : orbitWitnessArch j ((7 / 4 : ℚ) : ℝ) = 0 := by
  refine orbitWitnessArch_eq_zero j ?_
  have hhigh := orbitCentre_le j
  have hrad := orbitRadius_le j
  have hcast : ((7 / 4 : ℚ) : ℝ) = 7 / 4 := by norm_num
  rw [hcast, abs_of_nonneg (by linarith)]
  linarith

/-! ### Infinite-dimensional residual coinvariants -/

/-- **Card `(TPS.19)`.**  The `j`-th two-endpoint witness. -/
def orbitWitness (j : ℕ) : CCMRationalAdelicBruhatSimpleTensor :=
  orbitWitnessArch j ⊗ₜ[ℂ] ccmRationalFiniteHaarNull

theorem orbitWitness_mem (j : ℕ) :
    orbitWitness j ∈ CCMRationalAdelicTwoEndpointKernel := by
  refine ⟨?_, ?_⟩
  · show ccmRationalAdelicBruhatZeroEval (orbitWitness j) = 0
    rw [orbitWitness, ccmRationalAdelicBruhatZeroEval_tmul,
      orbitWitnessArch_eq_zero_of_out j 0 (Or.inl (by norm_num)), zero_mul]
  · show ccmRationalAdelicBruhatIntegral (orbitWitness j) = 0
    rw [orbitWitness, ccmRationalAdelicBruhatIntegral_tmul,
      ccmRationalFiniteHaarNull_integral, mul_zero]

/-- **Card `(TPS.20)`.**  Each sampling base reads exactly its own witness. -/
theorem ccmRationalAdelicOrbitSample_witness (p : Nat.Primes) (i j : ℕ) :
    ccmRationalAdelicOrbitSample p (orbitCentre i) (orbitCentre_ne_zero i) (orbitWitness j) =
      -(if j = i then (1 : ℂ) else 0) := by
  rw [orbitWitness, ccmRationalAdelicOrbitSample_tmul, ccmRationalFiniteHaarNull_zero,
    ccmRationalArchimedeanPrimeOrbitStokes_of_support p
      (a := ((orbitCentre i : ℚ) : ℝ)) (le_of_lt (one_lt_orbitCentre i))
      (by linarith [orbitCentre_le i]) _ (orbitWitnessArch_eq_zero_of_out j)
      (ccmRationalScalingOfBase_invLabel (orbitCentre i) (orbitCentre_ne_zero i))]
  by_cases hij : j = i
  · subst hij
    rw [orbitWitnessArch_centre, if_pos rfl]
    ring
  · rw [orbitWitnessArch_centre_ne i j (fun h => hij h.symm), if_neg hij]
    ring

/-- **Card `(TPS.20)`.**  The base sampling reads no witness. -/
theorem ccmRationalAdelicOrbitSample_witness_base (p : Nat.Primes) (j : ℕ) :
    ccmRationalAdelicOrbitSample p (7 / 4) (by norm_num) (orbitWitness j) = 0 := by
  rw [orbitWitness, ccmRationalAdelicOrbitSample_tmul,
    ccmRationalArchimedeanPrimeOrbitStokes_of_support p
      (a := ((7 / 4 : ℚ) : ℝ)) (by norm_num) (by norm_num) _
      (orbitWitnessArch_eq_zero_of_out j)
      (ccmRationalScalingOfBase_invLabel (7 / 4) (by norm_num)),
    orbitWitnessArch_base, mul_zero]

/-- **Card `(TPS.21)`.**  The orbit-phase covectors form a dual family to the witnesses. -/
theorem ccmRationalAdelicOrbitPhaseCovector_witness (p : Nat.Primes) (i j : ℕ) :
    ccmRationalAdelicOrbitPhaseCovector p (orbitCentre i) (7 / 4)
        (orbitCentre_ne_zero i) (by norm_num)
        (Submodule.Quotient.mk ⟨orbitWitness j, orbitWitness_mem j⟩) =
      -(if j = i then (1 : ℂ) else 0) := by
  rw [ccmRationalAdelicOrbitPhaseCovector_mk]
  change ccmRationalAdelicOrbitSample p (orbitCentre i) (orbitCentre_ne_zero i)
      (orbitWitness j) -
    ccmRationalAdelicOrbitSample p (7 / 4) (by norm_num) (orbitWitness j) = _
  rw [ccmRationalAdelicOrbitSample_witness, ccmRationalAdelicOrbitSample_witness_base, sub_zero]

/-- **Card `(TPS.21)`.**  The witness classes are linearly independent in the two-endpoint
coinvariants. -/
theorem orbitWitnessClass_linearIndependent (p : Nat.Primes) :
    LinearIndependent ℂ (fun j : ℕ =>
      (Submodule.Quotient.mk ⟨orbitWitness j, orbitWitness_mem j⟩ :
        CCMRationalAdelicTwoEndpointCoinvariants p)) := by
  rw [linearIndependent_iff']
  intro s c hsum i hi
  have happly := congrArg (ccmRationalAdelicOrbitPhaseCovector p (orbitCentre i) (7 / 4)
    (orbitCentre_ne_zero i) (by norm_num)) hsum
  rw [map_sum, map_zero] at happly
  have hterm : ∀ j ∈ s,
      ccmRationalAdelicOrbitPhaseCovector p (orbitCentre i) (7 / 4)
          (orbitCentre_ne_zero i) (by norm_num)
          (c j • (Submodule.Quotient.mk ⟨orbitWitness j, orbitWitness_mem j⟩ :
            CCMRationalAdelicTwoEndpointCoinvariants p)) =
        if j = i then -c j else 0 := by
    intro j _
    rw [map_smul, ccmRationalAdelicOrbitPhaseCovector_witness, smul_eq_mul]
    by_cases hji : j = i
    · rw [if_pos hji, if_pos hji]
      ring
    · rw [if_neg hji, if_neg hji]
      ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' s i (fun j => -c j), if_pos hi] at happly
  have := neg_eq_zero.mp happly
  exact this

/-- **Theorem E, card `(TPS.17)` boxed.**  The two-endpoint coinvariants are infinite-dimensional,
so normalized two-endpoint Stokes covectors form an infinite-dimensional affine space: the second
endpoint collapses the Haar direction and nothing else. -/
theorem not_finiteDimensional_ccmRationalAdelicTwoEndpointCoinvariants (p : Nat.Primes) :
    ¬ FiniteDimensional ℂ (CCMRationalAdelicTwoEndpointCoinvariants p) := by
  intro hfd
  haveI := (orbitWitnessClass_linearIndependent p).finite_of_isNoetherian
  exact not_finite ℕ

/-- **Card `(TPS.17)`.**  Arbitrarily many independent residual classes exist. -/
theorem exists_independent_orbitWitnesses (p : Nat.Primes) (m : ℕ) :
    ∃ v : Fin m → CCMRationalAdelicTwoEndpointCoinvariants p, LinearIndependent ℂ v :=
  ⟨fun j => Submodule.Quotient.mk ⟨orbitWitness (j : ℕ), orbitWitness_mem _⟩,
    (orbitWitnessClass_linearIndependent p).comp _ Fin.val_injective⟩

end Witnesses

end RHTower

end
