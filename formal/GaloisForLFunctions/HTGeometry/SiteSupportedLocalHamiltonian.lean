import GaloisForLFunctions.HTGeometry.LocalMatrixTensorFactorization
import Mathlib.Algebra.Star.Module
import Mathlib.LinearAlgebra.Matrix.Hermitian

/-!
# Site-supported operators and graph-local Hamiltonian spaces

A finite quantum network is a family of named local factors `A v` together with
an interaction graph.  Its physical carrier is the site product `∀ v, A v`, and
its admissible Hamiltonians are the real span of Hermitian operators supported
on single sites and on interaction edges.

This file introduces the intrinsic support predicate

```
IsSiteSupported S H
```

which says that `H` acts as the identity outside the site packet `S`, states it
without naming the local block, and proves the closure properties needed to run
network inductions: it is a real subspace, it is monotone in the packet, it is
preserved by the conjugate transpose, and it is exactly the image of
`liftLocalMatrix S`.

`siteFactorLocalSubmodule` is the resulting exact onsite-plus-edge Hermitian
Hamiltonian space of an interaction graph.
-/

open scoped Kronecker BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- `H` acts as the identity outside the site packet `S`: it vanishes between
configurations differing off `S`, and its matrix entries depend only on the
`S`-coordinates. -/
def IsSiteSupported {V : Type*} {A : V → Type*} (S : Finset V)
    (H : Matrix (∀ v, A v) (∀ v, A v) ℂ) : Prop :=
  (∀ x y : ∀ v, A v, (∃ w, w ∉ S ∧ x w ≠ y w) → H x y = 0) ∧
    ∀ x y x' y' : ∀ v, A v,
      (∀ w ∈ S, x w = x' w) → (∀ w ∈ S, y w = y' w) →
      (∀ w, w ∉ S → x w = y w) → (∀ w, w ∉ S → x' w = y' w) →
      H x y = H x' y'

namespace IsSiteSupported

variable {V : Type*} {A : V → Type*}

theorem zero (S : Finset V) :
    IsSiteSupported (A := A) S 0 :=
  ⟨fun _ _ _ => rfl, fun _ _ _ _ _ _ _ _ => rfl⟩

theorem add {S : Finset V} {H K : Matrix (∀ v, A v) (∀ v, A v) ℂ}
    (hH : IsSiteSupported S H) (hK : IsSiteSupported S K) :
    IsSiteSupported S (H + K) := by
  refine ⟨fun x y hxy => ?_, fun x y x' y' h₁ h₂ h₃ h₄ => ?_⟩
  · simp [Matrix.add_apply, hH.1 x y hxy, hK.1 x y hxy]
  · simp [Matrix.add_apply, hH.2 x y x' y' h₁ h₂ h₃ h₄,
      hK.2 x y x' y' h₁ h₂ h₃ h₄]

theorem smul {S : Finset V} {H : Matrix (∀ v, A v) (∀ v, A v) ℂ}
    (c : ℝ) (hH : IsSiteSupported S H) :
    IsSiteSupported S (c • H) := by
  refine ⟨fun x y hxy => ?_, fun x y x' y' h₁ h₂ h₃ h₄ => ?_⟩
  · simp [Matrix.smul_apply, hH.1 x y hxy]
  · simp [Matrix.smul_apply, hH.2 x y x' y' h₁ h₂ h₃ h₄]

theorem neg {S : Finset V} {H : Matrix (∀ v, A v) (∀ v, A v) ℂ}
    (hH : IsSiteSupported S H) :
    IsSiteSupported S (-H) := by
  refine ⟨fun x y hxy => ?_, fun x y x' y' h₁ h₂ h₃ h₄ => ?_⟩
  · simp [Matrix.neg_apply, hH.1 x y hxy]
  · simp [Matrix.neg_apply, hH.2 x y x' y' h₁ h₂ h₃ h₄]

/-- Enlarging the packet preserves support: entries that would newly be allowed
to differ already force a zero entry. -/
theorem mono {S T : Finset V} (hST : S ⊆ T)
    {H : Matrix (∀ v, A v) (∀ v, A v) ℂ} (hH : IsSiteSupported S H) :
    IsSiteSupported T H := by
  refine ⟨fun x y hxy => ?_, fun x y x' y' h₁ h₂ h₃ h₄ => ?_⟩
  · obtain ⟨w, hwT, hxy⟩ := hxy
    exact hH.1 x y ⟨w, fun hwS => hwT (hST hwS), hxy⟩
  · by_cases hcase : ∀ w, w ∉ S → x w = y w
    · have hcase' : ∀ w, w ∉ S → x' w = y' w := by
        intro w hwS
        by_cases hwT : w ∈ T
        · rw [← h₁ w hwT, ← h₂ w hwT]
          exact hcase w hwS
        · exact h₄ w hwT
      exact hH.2 x y x' y'
        (fun w hwS => h₁ w (hST hwS)) (fun w hwS => h₂ w (hST hwS))
        hcase hcase'
    · push Not at hcase
      obtain ⟨w, hwS, hne⟩ := hcase
      have hwT : w ∈ T := by
        by_contra hwT
        exact hne (h₃ w hwT)
      have hne' : x' w ≠ y' w := by
        rw [← h₁ w hwT, ← h₂ w hwT]
        exact hne
      rw [hH.1 x y ⟨w, hwS, hne⟩, hH.1 x' y' ⟨w, hwS, hne'⟩]

theorem conjTranspose {S : Finset V} {H : Matrix (∀ v, A v) (∀ v, A v) ℂ}
    (hH : IsSiteSupported S H) :
    IsSiteSupported S Hᴴ := by
  refine ⟨fun x y hxy => ?_, fun x y x' y' h₁ h₂ h₃ h₄ => ?_⟩
  · obtain ⟨w, hwS, hne⟩ := hxy
    have := hH.1 y x ⟨w, hwS, fun h => hne h.symm⟩
    simp [Matrix.conjTranspose_apply, this]
  · have := hH.2 y x y' x' h₂ h₁
      (fun w hw => (h₃ w hw).symm) (fun w hw => (h₄ w hw).symm)
    simp [Matrix.conjTranspose_apply, this]

end IsSiteSupported

variable {V : Type*} [Fintype V] [DecidableEq V]
    {A : V → Type*} [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)]

/-- A lifted local block acts as the identity outside its packet. -/
theorem isSiteSupported_liftLocalMatrix (S : Finset V)
    (B : Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ) :
    IsSiteSupported S (liftLocalMatrix S B) := by
  constructor
  · rintro x y ⟨w, hwS, hne⟩
    have hout : restrictOutsideConfiguration S x ≠
        restrictOutsideConfiguration S y := by
      intro h
      exact hne (congrFun h ⟨w, hwS⟩)
    simp [liftLocalMatrix, hout]
  · intro x y x' y' h₁ h₂ h₃ h₄
    have hxout : restrictOutsideConfiguration S x =
        restrictOutsideConfiguration S y := by
      funext w
      exact h₃ w.1 w.2
    have hx'out : restrictOutsideConfiguration S x' =
        restrictOutsideConfiguration S y' := by
      funext w
      exact h₄ w.1 w.2
    have hxloc : restrictLocalConfiguration S x =
        restrictLocalConfiguration S x' := by
      funext w
      exact h₁ w.1 w.2
    have hyloc : restrictLocalConfiguration S y =
        restrictLocalConfiguration S y' := by
      funext w
      exact h₂ w.1 w.2
    simp [liftLocalMatrix, hxout, hx'out, hxloc, hyloc]

/-- Glue a packet configuration to a fixed spectator configuration. -/
def glueLocalConfiguration (S : Finset V)
    (a : LocalConfiguration A S) (z : ∀ v, A v) : ∀ v, A v :=
  fun w => if h : w ∈ S then a ⟨w, h⟩ else z w

omit [Fintype V] [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] in
@[simp] theorem glueLocalConfiguration_mem (S : Finset V)
    (a : LocalConfiguration A S) (z : ∀ v, A v) {w : V} (hw : w ∈ S) :
    glueLocalConfiguration S a z w = a ⟨w, hw⟩ := by
  simp [glueLocalConfiguration, hw]

omit [Fintype V] [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] in
@[simp] theorem glueLocalConfiguration_notMem (S : Finset V)
    (a : LocalConfiguration A S) (z : ∀ v, A v) {w : V} (hw : w ∉ S) :
    glueLocalConfiguration S a z w = z w := by
  simp [glueLocalConfiguration, hw]

/-- **Support is exactly locality.**  Every operator acting as the identity
outside a packet is the lift of an explicit block on that packet. -/
theorem exists_liftLocalMatrix_of_isSiteSupported [∀ v, Nonempty (A v)]
    {S : Finset V} {H : Matrix (∀ v, A v) (∀ v, A v) ℂ}
    (hH : IsSiteSupported S H) :
    ∃ B : Matrix (LocalConfiguration A S) (LocalConfiguration A S) ℂ,
      H = liftLocalMatrix S B := by
  classical
  let z : ∀ v, A v := fun v => Classical.arbitrary (A v)
  refine ⟨fun a b => H (glueLocalConfiguration S a z)
    (glueLocalConfiguration S b z), ?_⟩
  ext x y
  by_cases hout : restrictOutsideConfiguration S x =
      restrictOutsideConfiguration S y
  · have h₃ : ∀ w, w ∉ S → x w = y w := fun w hw =>
      congrFun hout ⟨w, hw⟩
    have h₄ : ∀ w, w ∉ S →
        glueLocalConfiguration S (restrictLocalConfiguration S x) z w =
          glueLocalConfiguration S (restrictLocalConfiguration S y) z w := by
      intro w hw
      simp [hw]
    have h₁ : ∀ w ∈ S, x w =
        glueLocalConfiguration S (restrictLocalConfiguration S x) z w := by
      intro w hw
      simp [hw, restrictLocalConfiguration]
    have h₂ : ∀ w ∈ S, y w =
        glueLocalConfiguration S (restrictLocalConfiguration S y) z w := by
      intro w hw
      simp [hw, restrictLocalConfiguration]
    rw [liftLocalMatrix, if_pos hout]
    exact hH.2 x y _ _ h₁ h₂ h₃ h₄
  · have hne : ∃ w, w ∉ S ∧ x w ≠ y w := by
      by_contra hcon
      push Not at hcon
      exact hout (funext fun w => hcon w.1 w.2)
    rw [liftLocalMatrix, if_neg hout]
    exact hH.1 x y hne

variable (A)

/-- Hermitian one-site and interaction-edge generators of an interaction
graph on a site-factorized carrier. -/
def siteFactorLocalGenerator (G : SimpleGraph V) : Set (Matrix (∀ v, A v) (∀ v, A v) ℂ) :=
  {H : Matrix (∀ v, A v) (∀ v, A v) ℂ | H.IsHermitian ∧
    ((∃ v : V, IsSiteSupported {v} H) ∨
      ∃ u v : V, G.Adj u v ∧ IsSiteSupported {u, v} H)}

/-- Exact real vector space of Hermitian onsite-plus-edge Hamiltonians of an
interaction graph on a site-factorized carrier. -/
def siteFactorLocalSubmodule (G : SimpleGraph V) : Submodule ℝ (Matrix (∀ v, A v) (∀ v, A v) ℂ) :=
  Submodule.span ℝ (siteFactorLocalGenerator A G)

omit [Fintype V] [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] in
theorem siteFactorLocalSubmodule_le_selfAdjoint (G : SimpleGraph V) :
    siteFactorLocalSubmodule A G ≤
      selfAdjoint.submodule ℝ (Matrix (∀ v, A v) (∀ v, A v) ℂ) := by
  apply Submodule.span_le.2
  rintro H ⟨hH, -⟩
  exact hH

omit [Fintype V] [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] in
/-- Adding interaction edges enlarges the local Hamiltonian space. -/
theorem siteFactorLocalSubmodule_mono
    {G G' : SimpleGraph V} (hG : G ≤ G') :
    siteFactorLocalSubmodule A G ≤ siteFactorLocalSubmodule A G' := by
  apply Submodule.span_le.2
  rintro H ⟨hH, hcase⟩
  refine Submodule.subset_span ⟨hH, ?_⟩
  rcases hcase with ⟨v, hv⟩ | ⟨u, v, huv, hsupp⟩
  · exact Or.inl ⟨v, hv⟩
  · exact Or.inr ⟨u, v, hG huv, hsupp⟩

omit [Fintype V] [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] in
theorem mem_siteFactorLocalSubmodule_of_oneSite (G : SimpleGraph V) {H : Matrix (∀ v, A v) (∀ v, A v) ℂ}
    (hH : H.IsHermitian) (v : V) (hsupp : IsSiteSupported {v} H) :
    H ∈ siteFactorLocalSubmodule A G :=
  Submodule.subset_span ⟨hH, Or.inl ⟨v, hsupp⟩⟩

/-- One admissible interaction term of a graph: an operator supported on a
single site or on one interaction edge.  Hermiticity is not required. -/
def IsGraphLocalTerm (G : SimpleGraph V)
    (X : Matrix (∀ v, A v) (∀ v, A v) ℂ) : Prop :=
  (∃ v : V, IsSiteSupported {v} X) ∨
    ∃ u v : V, G.Adj u v ∧ IsSiteSupported {u, v} X

omit [Fintype V] [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] in
theorem IsGraphLocalTerm.conjTranspose {G : SimpleGraph V}
    {X : Matrix (∀ v, A v) (∀ v, A v) ℂ} (hX : IsGraphLocalTerm A G X) :
    IsGraphLocalTerm A G Xᴴ := by
  rcases hX with ⟨v, hv⟩ | ⟨u, v, huv, hsupp⟩
  · exact Or.inl ⟨v, hv.conjTranspose⟩
  · exact Or.inr ⟨u, v, huv, hsupp.conjTranspose⟩

omit [Fintype V] [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] in
theorem IsGraphLocalTerm.add_conjTranspose {G : SimpleGraph V}
    {X : Matrix (∀ v, A v) (∀ v, A v) ℂ} (hX : IsGraphLocalTerm A G X) :
    IsGraphLocalTerm A G (X + Xᴴ) := by
  rcases hX with ⟨v, hv⟩ | ⟨u, v, huv, hsupp⟩
  · exact Or.inl ⟨v, hv.add hv.conjTranspose⟩
  · exact Or.inr ⟨u, v, huv, hsupp.add hsupp.conjTranspose⟩

omit [Fintype V] [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] in
/-- **Hermitian sums of local terms are local Hamiltonians.**  Individual
interaction terms of a Hermitian local Hamiltonian need not be Hermitian; the
Hermitian part of each term has the same site support and reassembles the same
operator. -/
theorem mem_siteFactorLocalSubmodule_of_hermitian_sum
    {ι : Type*} [Fintype ι] (G : SimpleGraph V)
    (X : ι → Matrix (∀ v, A v) (∀ v, A v) ℂ)
    (hX : ∀ i, IsGraphLocalTerm A G (X i))
    {H : Matrix (∀ v, A v) (∀ v, A v) ℂ} (hH : H.IsHermitian)
    (hsum : H = ∑ i, X i) :
    H ∈ siteFactorLocalSubmodule A G := by
  have hconj : ∑ i, (X i)ᴴ = H := by
    rw [← Matrix.conjTranspose_sum, ← hsum]
    exact hH
  have hkey : H = ∑ i, (2⁻¹ : ℝ) • (X i + (X i)ᴴ) := by
    rw [← Finset.smul_sum, Finset.sum_add_distrib, ← hsum, hconj]
    rw [show H + H = (2 : ℝ) • H by
      rw [two_smul]]
    rw [smul_smul]
    norm_num
  rw [hkey]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
  refine Submodule.subset_span ⟨?_, (hX i).add_conjTranspose⟩
  show (X i + (X i)ᴴ).IsHermitian
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose, add_comm]

omit [Fintype V] [∀ v, Fintype (A v)] [∀ v, DecidableEq (A v)] in
theorem mem_siteFactorLocalSubmodule_of_edge (G : SimpleGraph V) {H : Matrix (∀ v, A v) (∀ v, A v) ℂ}
    (hH : H.IsHermitian) {u v : V} (huv : G.Adj u v)
    (hsupp : IsSiteSupported {u, v} H) :
    H ∈ siteFactorLocalSubmodule A G :=
  Submodule.subset_span ⟨hH, Or.inr ⟨u, v, huv, hsupp⟩⟩

end

end GaloisForLFunctions.HTGeometry
