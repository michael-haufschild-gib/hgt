import GaloisForLFunctions.HTGeometry.CDGABarMul
import GaloisForLFunctions.HTGeometry.CDGATensorSingle

/-!
# The head of the bar differential

The head of a bar differential multiplies the outer factor of a nested tensor product with the first
factor of the inner one.  Because the graded tensor product is a product over the decompositions of
the degree, the component of the result at a decomposition `(c, e)` is a finite sum over the ways
`c` splits as `a + a' + 1`: project the inner factor at `(a', e)`, reassociate, and multiply the
first two slots.  No graded associator is needed, only the ordinary associator of tensor products.

* `HTGeometry.BarSplit` : the ways a shifted degree splits under one multiplication.
* `HTGeometry.barHeadTerm` : one term of the head.
* `HTGeometry.barHead` : the head of the bar differential.
-/

universe u

namespace GaloisForLFunctions.HTGeometry

open TensorProduct

variable {R : Type u} [CommRing R] {X : ℕ → Type u} [∀ n, AddCommGroup (X n)]
  [∀ n, Module R (X n)] {A : CDGAStructure R X} (ε : CDGAHom A (groundCDGA R))
  (Z : ℕ → Type u) [∀ n, AddCommGroup (Z n)] [∀ n, Module R (Z n)]

/-- The ways a shifted degree splits into two under one multiplication. -/
abbrev BarSplit (c : ℕ) : Type := {aa : ℕ × ℕ // aa.1 + aa.2 + 1 = c}

/-- A split, as a decomposition of the same degree. -/
def barSplitEmbed {c : ℕ} (p : BarSplit c) : {ab : ℕ × ℕ // ab.1 + ab.2 = c} :=
  ⟨(p.1.1, p.1.2 + 1), by have h := p.2; omega⟩

theorem barSplitEmbed_injective {c : ℕ} : Function.Injective (barSplitEmbed (c := c)) := by
  rintro ⟨⟨a, a'⟩, h⟩ ⟨⟨b, b'⟩, h'⟩ hEq
  have h1 : ((a, a' + 1) : ℕ × ℕ) = (b, b' + 1) := congrArg Subtype.val hEq
  have ha : a = b := congrArg Prod.fst h1
  have ha' : a' + 1 = b' + 1 := congrArg Prod.snd h1
  refine Subtype.ext (Prod.ext ha ?_)
  show a' = b'
  omega

noncomputable instance barSplitFintype (c : ℕ) : Fintype (BarSplit c) :=
  Fintype.ofInjective barSplitEmbed barSplitEmbed_injective

/-- The shifted augmentation ideal, as a graded family. -/
abbrev barShiftFamily (n : ℕ) : Type u := augIdealCarrier ε (n + 1)

/-- **One term of the head of the bar differential**, as a linear map: project the inner tensor
factor at the second part of the split, reassociate, and multiply the first two slots. -/
noncomputable def barHeadTermₗ (n : ℕ) (c e : ℕ) (hp : c + e = n + 1) (a a' : ℕ)
    (hs : a + a' + 1 = c) :
    TensorCarrier (R := R) (barShiftFamily ε)
        (TensorCarrier (R := R) (barShiftFamily ε) Z) n
      →ₗ[R] TensorProduct R (barShiftFamily ε c) (Z e) :=
  hs ▸ (((TensorProduct.map (augIdealShiftMulTensor ε a a') (LinearMap.id (R := R) (M := Z e))).comp
      ((TensorProduct.assoc R (barShiftFamily ε a) (barShiftFamily ε a') (Z e)).symm.toLinearMap)).comp
    ((TensorProduct.map (LinearMap.id (R := R) (M := barShiftFamily ε a))
        (LinearMap.proj (R := R) (φ := fun q : {ab : ℕ × ℕ // ab.1 + ab.2 = a' + e} =>
          TensorProduct R (barShiftFamily ε q.1.1) (Z q.1.2)) ⟨(a', e), rfl⟩)).comp
      (LinearMap.proj (R := R) (φ := fun q : {ab : ℕ × ℕ // ab.1 + ab.2 = n} =>
        TensorProduct R (barShiftFamily ε q.1.1)
          (TensorCarrier (R := R) (barShiftFamily ε) Z q.1.2)) ⟨(a, a' + e), by omega⟩)))

/-- The sum over the splits, at one decomposition. -/
noncomputable def barHeadTermSum (n : ℕ) (p : {ce : ℕ × ℕ // ce.1 + ce.2 = n + 1}) :
    TensorCarrier (R := R) (barShiftFamily ε)
        (TensorCarrier (R := R) (barShiftFamily ε) Z) n
      →ₗ[R] TensorProduct R (barShiftFamily ε p.1.1) (Z p.1.2) :=
  ∑ s : BarSplit p.1.1, barHeadTermₗ ε Z n p.1.1 p.1.2 p.2 s.1.1 s.1.2 s.2

/-- **The head of the bar differential**, as a linear map. -/
noncomputable def barHeadₗ (n : ℕ) :
    TensorCarrier (R := R) (barShiftFamily ε)
        (TensorCarrier (R := R) (barShiftFamily ε) Z) n
      →ₗ[R] TensorCarrier (R := R) (barShiftFamily ε) Z (n + 1) :=
  LinearMap.pi fun p => barHeadTermSum ε Z n p

/-- The head of the bar differential. -/
noncomputable def barHead (n : ℕ)
    (F : TensorCarrier (R := R) (barShiftFamily ε)
      (TensorCarrier (R := R) (barShiftFamily ε) Z) n) :
    TensorCarrier (R := R) (barShiftFamily ε) Z (n + 1) :=
  barHeadₗ ε Z n F

/-- The head, componentwise: a finite sum over the splits of the first degree. -/
theorem barHead_apply (n : ℕ)
    (F : TensorCarrier (R := R) (barShiftFamily ε)
      (TensorCarrier (R := R) (barShiftFamily ε) Z) n)
    (p : {ce : ℕ × ℕ // ce.1 + ce.2 = n + 1}) :
    barHead ε Z n F p
      = ∑ s : BarSplit p.1.1, barHeadTermₗ ε Z n p.1.1 p.1.2 p.2 s.1.1 s.1.2 s.2 F := by
  show barHeadTermSum ε Z n p F = _
  rw [barHeadTermSum, LinearMap.sum_apply]

/-- One term of the head, on the component it reads. -/
theorem barHeadTermₗ_apply (n c e : ℕ) (hp : c + e = n + 1) (a a' : ℕ) (hs : a + a' + 1 = c)
    (F : TensorCarrier (R := R) (barShiftFamily ε)
      (TensorCarrier (R := R) (barShiftFamily ε) Z) n) :
    barHeadTermₗ ε Z n c e hp a a' hs F
      = hs ▸ (TensorProduct.map (augIdealShiftMulTensor ε a a') LinearMap.id
        ((TensorProduct.assoc R (barShiftFamily ε a) (barShiftFamily ε a') (Z e)).symm
          (TensorProduct.map LinearMap.id
            (LinearMap.proj (R := R) (φ := fun q : {ab : ℕ × ℕ // ab.1 + ab.2 = a' + e} =>
              TensorProduct R (barShiftFamily ε q.1.1) (Z q.1.2)) ⟨(a', e), rfl⟩)
            (F ⟨(a, a' + e), by omega⟩)))) := by
  cases hs
  rfl

end GaloisForLFunctions.HTGeometry
