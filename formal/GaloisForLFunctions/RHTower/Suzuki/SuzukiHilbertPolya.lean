import GaloisForLFunctions.RHTower.Suzuki.SuzukiWeilTauIsomorphism
import Mathlib.Analysis.InnerProductSpace.LinearPMap

noncomputable section

/-!
# The Hilbert--Pólya operator

Under the Riemann hypothesis the Weil space is isometrically the weighted sequence space `L²(τ)`,
where the natural operator is multiplication by the spectral points.  It is unbounded, so it is
carried by a `LinearPMap` on the domain where the multiplied sequence is still square-summable.

The operator is symmetric because the spectral points are real, and it is *self-adjoint*: testing
the fundamental property of the adjoint against the standard basis vector at `γ` shows that the
adjoint acts coordinatewise by the same multiplication, so its domain is already the original
domain.  Its eigenvectors are the basis vectors, with the spectral points as eigenvalues, and each
eigenvalue is simple — the multiplicity of a zero of `ξ` is carried by the weight of `L²(τ)`, not
by the dimension of the eigenspace.

This is the operator `A_{W,π/2}` of the source, transported to the sequence model.
-/

open MeasureTheory Set Complex Filter Topology

namespace RHTower

/-- Multiplication of a spectral sequence by the spectral points. -/
def suzukiTauDiagFun (f : SuzukiTauSpace) (ρ : XiDivisorSupport) : ℂ :=
  ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) * (f : ∀ _ : XiDivisorSupport, ℂ) ρ

@[simp] theorem suzukiTauDiagFun_add (f g : SuzukiTauSpace) :
    suzukiTauDiagFun (f + g) = suzukiTauDiagFun f + suzukiTauDiagFun g := by
  funext ρ
  show ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) * ((f : ∀ _ : XiDivisorSupport, ℂ) ρ
      + (g : ∀ _ : XiDivisorSupport, ℂ) ρ)
    = ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) * (f : ∀ _ : XiDivisorSupport, ℂ) ρ
      + ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) * (g : ∀ _ : XiDivisorSupport, ℂ) ρ
  ring

@[simp] theorem suzukiTauDiagFun_smul (c : ℂ) (f : SuzukiTauSpace) :
    suzukiTauDiagFun (c • f) = c • suzukiTauDiagFun f := by
  funext ρ
  show ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) * (c * (f : ∀ _ : XiDivisorSupport, ℂ) ρ)
    = c * (((xiRealSpectralPointSupport ρ : ℝ) : ℂ) * (f : ∀ _ : XiDivisorSupport, ℂ) ρ)
  ring

/-- The domain of the spectral multiplication operator. -/
def suzukiTauDomain : Submodule ℂ SuzukiTauSpace where
  carrier := {f | Memℓp (suzukiTauDiagFun f) 2}
  add_mem' := by
    intro f g hf hg
    show Memℓp (suzukiTauDiagFun (f + g)) 2
    rw [suzukiTauDiagFun_add]
    exact hf.add hg
  zero_mem' := by
    show Memℓp (suzukiTauDiagFun 0) 2
    have h0 : suzukiTauDiagFun 0 = 0 := by
      funext ρ
      show ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) * (0 : SuzukiTauSpace) ρ = 0
      simp
    rw [h0]
    exact zero_memℓp
  smul_mem' := by
    intro c f hf
    show Memℓp (suzukiTauDiagFun (c • f)) 2
    rw [suzukiTauDiagFun_smul]
    exact hf.const_smul c

/-- **The spectral multiplication operator on `L²(τ)`.**  Through the isomorphisms of Theorem 1.1
and Lemma 5.4 this is the operator `A_{W,π/2}` of the source. -/
def suzukiTauDiag : SuzukiTauSpace →ₗ.[ℂ] SuzukiTauSpace where
  domain := suzukiTauDomain
  toFun :=
    { toFun := fun f => ⟨suzukiTauDiagFun (f : SuzukiTauSpace), f.2⟩
      map_add' := by
        intro f g
        refine lp.ext ?_
        exact suzukiTauDiagFun_add _ _
      map_smul' := by
        intro c f
        refine lp.ext ?_
        exact suzukiTauDiagFun_smul c _ }

@[simp] theorem suzukiTauDiag_apply (f : suzukiTauDiag.domain) (ρ : XiDivisorSupport) :
    ((suzukiTauDiag f : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) ρ
      = ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)
        * ((f : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) ρ := rfl

/-- **The operator is symmetric.**  The spectral points are real. -/
theorem inner_suzukiTauDiag_symm (f g : suzukiTauDiag.domain) :
    (inner ℂ (suzukiTauDiag f) (g : SuzukiTauSpace) : ℂ)
      = (inner ℂ (f : SuzukiTauSpace) (suzukiTauDiag g) : ℂ) := by
  have hb := lp.hasSum_inner (𝕜 := ℂ) (suzukiTauDiag f) (g : SuzukiTauSpace)
  have hb' := lp.hasSum_inner (𝕜 := ℂ) (f : SuzukiTauSpace) (suzukiTauDiag g)
  refine HasSum.unique hb ?_
  refine hb'.congr_fun ?_
  intro ρ
  show (inner ℂ (((suzukiTauDiag f : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) ρ)
      (((g : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) ρ) : ℂ)
    = (inner ℂ (((f : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) ρ)
      (((suzukiTauDiag g : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) ρ) : ℂ)
  rw [RCLike.inner_apply, RCLike.inner_apply]
  show ((g : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) ρ
      * (starRingEnd ℂ) (((xiRealSpectralPointSupport ρ : ℝ) : ℂ)
        * ((f : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) ρ)
    = ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)
        * ((g : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) ρ
      * (starRingEnd ℂ) (((f : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) ρ)
  rw [map_mul, Complex.conj_ofReal]
  ring


/-! ## Eigenvectors -/

/-- The standard basis vector of `L²(τ)` at a spectral point. -/
def suzukiTauBasis (ρ : XiDivisorSupport) : SuzukiTauSpace :=
  lp.single (E := fun _ : XiDivisorSupport => ℂ) 2 ρ (1 : ℂ)

theorem suzukiTauBasis_self (ρ : XiDivisorSupport) :
    (suzukiTauBasis ρ : ∀ _ : XiDivisorSupport, ℂ) ρ = 1 :=
  lp.single_apply_self (E := fun _ : XiDivisorSupport => ℂ) 2 ρ (1 : ℂ)

theorem suzukiTauBasis_ne {ρ σ : XiDivisorSupport} (h : σ ≠ ρ) :
    (suzukiTauBasis ρ : ∀ _ : XiDivisorSupport, ℂ) σ = 0 :=
  lp.single_apply_ne (E := fun _ : XiDivisorSupport => ℂ) 2 ρ (1 : ℂ) h

theorem suzukiTauDiagFun_basis (ρ : XiDivisorSupport) :
    suzukiTauDiagFun (suzukiTauBasis ρ)
      = ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)
        • ((suzukiTauBasis ρ : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) := by
  funext σ
  by_cases h : σ = ρ
  · subst h
    rfl
  · show ((xiRealSpectralPointSupport σ : ℝ) : ℂ)
        * ((suzukiTauBasis ρ : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) σ
      = ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)
        * ((suzukiTauBasis ρ : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) σ
    rw [suzukiTauBasis_ne h, mul_zero, mul_zero]

theorem suzukiTauBasis_mem_suzukiTauDomain (ρ : XiDivisorSupport) :
    suzukiTauBasis ρ ∈ suzukiTauDomain := by
  show Memℓp (suzukiTauDiagFun (suzukiTauBasis ρ)) 2
  rw [suzukiTauDiagFun_basis]
  exact (lp.memℓp (suzukiTauBasis ρ)).const_smul _

/-- **The basis vectors are eigenvectors with the spectral points as eigenvalues.** -/
theorem suzukiTauDiag_basis (ρ : XiDivisorSupport) :
    suzukiTauDiag ⟨suzukiTauBasis ρ, suzukiTauBasis_mem_suzukiTauDomain ρ⟩
      = ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) • suzukiTauBasis ρ :=
  lp.ext (suzukiTauDiagFun_basis ρ)

/-- **Multiplicity one.**  An eigenvector for a spectral eigenvalue is a multiple of the
corresponding basis vector. -/
theorem eq_smul_suzukiTauBasis_of_eigen (hRH : RiemannHypothesis) (ρ : XiDivisorSupport)
    {f : suzukiTauDiag.domain}
    (hf : suzukiTauDiag f = ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) • (f : SuzukiTauSpace)) :
    (f : SuzukiTauSpace)
      = (((f : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) ρ) • suzukiTauBasis ρ := by
  refine lp.ext ?_
  funext σ
  have hval := congrFun (congrArg (fun g : SuzukiTauSpace =>
    (g : ∀ _ : XiDivisorSupport, ℂ)) hf) σ
  by_cases h : σ = ρ
  · subst h
    show ((f : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) σ
      = (((f : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) σ)
        * ((suzukiTauBasis σ : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) σ
    rw [suzukiTauBasis_self, mul_one]
  · show ((f : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) σ
      = (((f : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) ρ)
        * ((suzukiTauBasis ρ : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) σ
    rw [suzukiTauBasis_ne h, mul_zero]
    have heq : ((xiRealSpectralPointSupport σ : ℝ) : ℂ)
        * ((f : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) σ
        = ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)
          * ((f : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) σ := hval
    have hne : ((xiRealSpectralPointSupport σ : ℝ) : ℂ)
        - ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) ≠ 0 := by
      intro hc
      refine h (xiRealSpectralPointSupport_injective hRH ?_)
      have hcast : ((xiRealSpectralPointSupport σ : ℝ) : ℂ)
          = ((xiRealSpectralPointSupport ρ : ℝ) : ℂ) := by
        linear_combination hc
      exact_mod_cast hcast
    have hzero : (((xiRealSpectralPointSupport σ : ℝ) : ℂ)
        - ((xiRealSpectralPointSupport ρ : ℝ) : ℂ))
        * ((f : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) σ = 0 := by
      linear_combination heq
    exact (mul_eq_zero.mp hzero).resolve_left hne

/-! ## Self-adjointness -/

theorem dense_suzukiTauDomain :
    Dense ((suzukiTauDiag.domain : Submodule ℂ SuzukiTauSpace) : Set SuzukiTauSpace) := by
  refine Submodule.dense_iff_topologicalClosure_eq_top.mpr ?_
  refine Submodule.topologicalClosure_eq_top_iff.mpr ?_
  rw [Submodule.eq_bot_iff]
  intro y hy
  refine lp.ext ?_
  funext ρ
  have h0 : (inner ℂ (suzukiTauBasis ρ) y : ℂ) = 0 :=
    Submodule.mem_orthogonal _ _ |>.mp hy _ (suzukiTauBasis_mem_suzukiTauDomain ρ)
  have hval : (inner ℂ (suzukiTauBasis ρ) y : ℂ)
      = (y : ∀ _ : XiDivisorSupport, ℂ) ρ := by
    rw [suzukiTauBasis, lp.inner_single_left]
    simp
  rw [hval] at h0
  show (y : ∀ _ : XiDivisorSupport, ℂ) ρ = (0 : SuzukiTauSpace) ρ
  rw [h0]
  rfl

theorem suzukiTauDiag_isFormalAdjoint : suzukiTauDiag.IsFormalAdjoint suzukiTauDiag :=
  fun x y => inner_suzukiTauDiag_symm x y

/-- **The spectral multiplication operator is self-adjoint.** -/
theorem isSelfAdjoint_suzukiTauDiag : IsSelfAdjoint suzukiTauDiag := by
  have hdense := dense_suzukiTauDomain
  refine le_antisymm ?_ (suzukiTauDiag_isFormalAdjoint.le_adjoint hdense)
  -- `A† ≤ A`
  have hform := LinearPMap.adjoint_isFormalAdjoint (T := suzukiTauDiag) hdense
  have hcoord : ∀ y : suzukiTauDiag.adjoint.domain, ∀ ρ : XiDivisorSupport,
      ((suzukiTauDiag.adjoint y : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) ρ
        = ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)
          * ((y : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) ρ := by
    intro y ρ
    have hb := hform y ⟨suzukiTauBasis ρ, suzukiTauBasis_mem_suzukiTauDomain ρ⟩
    rw [suzukiTauDiag_basis, inner_smul_right] at hb
    have hL : (inner ℂ (suzukiTauDiag.adjoint y) (suzukiTauBasis ρ) : ℂ)
        = (starRingEnd ℂ)
          (((suzukiTauDiag.adjoint y : SuzukiTauSpace) :
            ∀ _ : XiDivisorSupport, ℂ) ρ) := by
      rw [suzukiTauBasis, lp.inner_single_right]
      simp
    have hR : (inner ℂ (y : SuzukiTauSpace) (suzukiTauBasis ρ) : ℂ)
        = (starRingEnd ℂ) (((y : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) ρ) := by
      rw [suzukiTauBasis, lp.inner_single_right]
      simp
    rw [hL, hR] at hb
    have hb' := congrArg (starRingEnd ℂ) hb
    rw [Complex.conj_conj, map_mul, Complex.conj_ofReal, Complex.conj_conj] at hb'
    exact hb'
  refine ⟨?_, ?_⟩
  · intro y hy
    show Memℓp (suzukiTauDiagFun y) 2
    have hfun : suzukiTauDiagFun y
        = ((suzukiTauDiag.adjoint ⟨y, hy⟩ : SuzukiTauSpace) :
            ∀ _ : XiDivisorSupport, ℂ) := by
      funext ρ
      exact (hcoord ⟨y, hy⟩ ρ).symm
    rw [hfun]
    exact lp.memℓp _
  · intro x y hxy
    refine lp.ext ?_
    funext ρ
    have h1 := hcoord x ρ
    have h2 : ((y : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) ρ
        = ((x : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) ρ := by
      rw [hxy]
    show ((suzukiTauDiag.adjoint x : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) ρ
      = ((xiRealSpectralPointSupport ρ : ℝ) : ℂ)
        * ((y : SuzukiTauSpace) : ∀ _ : XiDivisorSupport, ℂ) ρ
    rw [h1, h2]


end RHTower
