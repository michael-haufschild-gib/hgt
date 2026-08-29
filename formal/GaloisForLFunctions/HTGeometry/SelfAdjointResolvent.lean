import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# The resolvent of a self-adjoint partially defined operator

A self-adjoint operator on a Hilbert space is symmetric, so at a nonreal spectral parameter the
imaginary part gives a two-sided lower bound on `A - z`.  Together with closedness of the graph
that makes the range closed, and the adjoint characterization makes it dense.  Hence `A - z` is a
bijection of the domain onto the whole space for every nonreal `z`.

This is the basic resolvent theorem for unbounded self-adjoint operators.
-/

open scoped InnerProductSpace

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A self-adjoint partially defined operator is its own formal adjoint. -/
theorem isFormalAdjoint_of_isSelfAdjoint {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) :
    A.IsFormalAdjoint A := by
  have h := LinearPMap.adjoint_isFormalAdjoint (T := A) hA.dense_domain
  rwa [LinearPMap.isSelfAdjoint_def.1 hA] at h

/-- The diagonal form of a self-adjoint operator is real. -/
theorem inner_selfAdjoint_self_im {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (x : A.domain) :
    (inner ℂ (A x) (x : H)).im = 0 := by
  have h := isFormalAdjoint_of_isSelfAdjoint hA x x
  have hconj : (starRingEnd ℂ) (inner ℂ (A x) (x : H)) = inner ℂ (A x) (x : H) := by
    rw [inner_conj_symm]
    exact h.symm
  exact Complex.conj_eq_iff_im.1 hconj

/-- **The imaginary lower bound.**  At a nonreal parameter the shifted self-adjoint operator is
bounded below by the imaginary part. -/
theorem norm_sub_smul_lower_bound {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) (z : ℂ)
    (x : A.domain) :
    |z.im| * ‖(x : H)‖ ≤ ‖A x - z • (x : H)‖ := by
  set u : H := A x - (z.re : ℂ) • (x : H) with hu
  set w : H := ((z.im : ℂ) * Complex.I) • (x : H) with hw
  have hsplit : A x - z • (x : H) = u - w := by
    rw [hu, hw, sub_sub, ← add_smul]
    congr 2
    simp
  have hinner : inner ℂ u (x : H) = inner ℂ (A x) (x : H) - (z.re : ℂ) * inner ℂ (x : H) (x : H) := by
    rw [hu, inner_sub_left, inner_smul_left]
    simp
  have hreal : (inner ℂ u (x : H)).im = 0 := by
    have h1 := inner_selfAdjoint_self_im hA x
    have h2 : (inner ℂ (x : H) (x : H)).im = 0 := by
      simpa using inner_self_im (𝕜 := ℂ) (x : H)
    rw [hinner, Complex.sub_im, h1, Complex.mul_im, h2, Complex.ofReal_im]
    ring
  have hcross : RCLike.re (inner ℂ u w) = 0 := by
    have hz1 : ((z.im : ℂ) * Complex.I).re = 0 := by simp
    have hz2 : ((z.im : ℂ) * Complex.I).im = z.im := by simp
    rw [hw, inner_smul_right]
    show (((z.im : ℂ) * Complex.I) * inner ℂ u (x : H)).re = 0
    rw [Complex.mul_re, hz1, hz2, hreal]
    ring
  have hnormw : ‖w‖ = |z.im| * ‖(x : H)‖ := by
    rw [hw, norm_smul]
    simp
  have hsq : ‖A x - z • (x : H)‖ ^ 2 = ‖u‖ ^ 2 + ‖w‖ ^ 2 := by
    rw [hsplit, norm_sub_sq (𝕜 := ℂ), hcross]
    ring
  have hle : ‖w‖ ^ 2 ≤ ‖A x - z • (x : H)‖ ^ 2 := by
    rw [hsq]
    nlinarith [sq_nonneg ‖u‖]
  have hnn : (0 : ℝ) ≤ ‖A x - z • (x : H)‖ := norm_nonneg _
  rw [← hnormw]
  nlinarith [norm_nonneg w, hnn, hle]

/-! ## Injectivity at a nonreal parameter -/

/-- The shifted operator on the domain of a partially defined operator. -/
def shiftedMap (A : H →ₗ.[ℂ] H) (z : ℂ) : A.domain →ₗ[ℂ] H :=
  A.toFun - z • A.domain.subtype

omit [CompleteSpace H] in
@[simp] theorem shiftedMap_apply (A : H →ₗ.[ℂ] H) (z : ℂ) (x : A.domain) :
    shiftedMap A z x = A x - z • (x : H) := rfl

/-- **No nonreal eigenvalues.**  A self-adjoint operator is injective after a nonreal shift. -/
theorem injective_shiftedMap {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) :
    Function.Injective (shiftedMap A z) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro x hx
  have hzero : ‖A x - z • (x : H)‖ = 0 := by
    have : shiftedMap A z x = 0 := hx
    rw [shiftedMap_apply] at this
    rw [this, norm_zero]
  have hbound := norm_sub_smul_lower_bound hA z x
  rw [hzero] at hbound
  have habs : 0 < |z.im| := abs_pos.2 hz
  have hnx : ‖(x : H)‖ = 0 := by
    nlinarith [norm_nonneg ((x : H))]
  exact Subtype.ext (norm_eq_zero.1 hnx)

/-- **The eigenvalues of a self-adjoint operator are real.** -/
theorem eq_zero_of_apply_eq_smul {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) {x : A.domain} (hx : A x = z • (x : H)) : (x : H) = 0 := by
  have hker : shiftedMap A z x = 0 := by
    rw [shiftedMap_apply, hx, sub_self]
  have := injective_shiftedMap hA hz (a₁ := x) (a₂ := 0) (by simpa using hker)
  exact congrArg Subtype.val this

/-! ## Closed range -/

/-- The shifted operator read on the graph. -/
def graphShift (A : H →ₗ.[ℂ] H) (z : ℂ) : A.graph →L[ℂ] H :=
  ((ContinuousLinearMap.snd ℂ H H) - z • (ContinuousLinearMap.fst ℂ H H)).comp
    (A.graph.subtypeL)

omit [CompleteSpace H] in
@[simp] theorem graphShift_apply (A : H →ₗ.[ℂ] H) (z : ℂ) (p : A.graph) :
    graphShift A z p = (p : H × H).2 - z • (p : H × H).1 := rfl

omit [CompleteSpace H] in
theorem range_graphShift (A : H →ₗ.[ℂ] H) (z : ℂ) :
    Set.range (graphShift A z) = Set.range (shiftedMap A z) := by
  ext v
  constructor
  · rintro ⟨p, rfl⟩
    obtain ⟨y, hy1, hy2⟩ := A.mem_graph_iff.1 p.2
    exact ⟨y, by rw [shiftedMap_apply, graphShift_apply, hy1, hy2]⟩
  · rintro ⟨y, rfl⟩
    exact ⟨⟨((y : H), A y), A.mem_graph y⟩, by rw [graphShift_apply, shiftedMap_apply]⟩

/-- **The graph norm is controlled by the shifted operator.** -/
theorem norm_graph_le {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0)
    (p : A.graph) :
    ‖p‖ ≤ (1 + (1 + ‖z‖) / |z.im|) * ‖graphShift A z p‖ := by
  obtain ⟨y, hy1, hy2⟩ := A.mem_graph_iff.1 p.2
  have habs : 0 < |z.im| := abs_pos.2 hz
  have hv : graphShift A z p = A y - z • (y : H) := by
    rw [graphShift_apply, hy1, hy2]
  have hlow := norm_sub_smul_lower_bound hA z y
  rw [← hv] at hlow
  have hx : ‖(p : H × H).1‖ ≤ ‖graphShift A z p‖ / |z.im| := by
    rw [← hy1, le_div_iff₀ habs, mul_comm]
    exact hlow
  have hy : ‖(p : H × H).2‖ ≤ ‖graphShift A z p‖ + ‖z‖ * ‖(p : H × H).1‖ := by
    have hsplit : (p : H × H).2 = graphShift A z p + z • (p : H × H).1 := by
      rw [graphShift_apply]
      abel
    calc ‖(p : H × H).2‖ = ‖graphShift A z p + z • (p : H × H).1‖ := by rw [← hsplit]
      _ ≤ ‖graphShift A z p‖ + ‖z • (p : H × H).1‖ := norm_add_le _ _
      _ = ‖graphShift A z p‖ + ‖z‖ * ‖(p : H × H).1‖ := by rw [norm_smul]
  have hnn : (0 : ℝ) ≤ ‖graphShift A z p‖ := norm_nonneg _
  have hznn : (0 : ℝ) ≤ ‖z‖ := norm_nonneg _
  rw [show ‖p‖ = ‖(p : H × H)‖ from rfl, Prod.norm_def]
  refine max_le ?_ ?_
  · refine le_trans hx ?_
    rw [div_le_iff₀ habs]
    have hkey : (1 + ‖z‖) / |z.im| * |z.im| = 1 + ‖z‖ := div_mul_cancel₀ _ habs.ne'
    nlinarith [hnn, habs.le, hznn, hkey, mul_nonneg hnn habs.le, mul_nonneg hnn hznn]
  · refine le_trans hy ?_
    have hx' : ‖z‖ * ‖(p : H × H).1‖ ≤ ‖z‖ * (‖graphShift A z p‖ / |z.im|) :=
      mul_le_mul_of_nonneg_left hx hznn
    have hdiv : ‖z‖ * (‖graphShift A z p‖ / |z.im|) =
        (‖z‖ / |z.im|) * ‖graphShift A z p‖ := by
      field_simp
    rw [hdiv] at hx'
    have hcoef : (1 : ℝ) + ‖z‖ / |z.im| ≤ 1 + (1 + ‖z‖) / |z.im| := by
      gcongr
      linarith
    nlinarith [mul_le_mul_of_nonneg_right hcoef hnn]

/-- **The range of the shifted operator is closed.** -/
theorem isClosed_range_shiftedMap {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) : IsClosed (Set.range (shiftedMap A z)) := by
  haveI : IsClosed (A.graph : Set (H × H)) := hA.isClosed
  haveI : CompleteSpace (A.graph : Set (H × H)) := IsClosed.completeSpace_coe
  haveI : CompleteSpace A.graph := this
  set K : NNReal := ⟨1 + (1 + ‖z‖) / |z.im|, by positivity⟩ with hK
  have hanti : AntilipschitzWith K (graphShift A z) := by
    refine AddMonoidHomClass.antilipschitz_of_bound (graphShift A z) fun p => ?_
    exact norm_graph_le hA hz p
  have := hanti.isClosed_range (graphShift A z).uniformContinuous
  rwa [range_graphShift] at this

/-! ## Dense range and bijectivity -/

/-- **The shifted operator has no orthogonal complement.** -/
theorem orthogonal_range_shiftedMap_eq_bot {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ}
    (hz : z.im ≠ 0) : (LinearMap.range (shiftedMap A z))ᗮ = ⊥ := by
  have hAeq : A.adjoint = A := LinearPMap.isSelfAdjoint_def.1 hA
  have hdense := hA.dense_domain
  rw [Submodule.eq_bot_iff]
  intro y hy
  have hperp : ∀ x : A.domain, inner ℂ (A x - z • (x : H)) y = 0 := by
    intro x
    exact (Submodule.mem_orthogonal _ y).1 hy _ ⟨x, rfl⟩
  have hz' : ∀ x : A.domain, inner ℂ y (A x) = z * inner ℂ y ((x : H)) := by
    intro x
    have h0 := hperp x
    rw [inner_sub_left, inner_smul_left, sub_eq_zero] at h0
    have h2 := congrArg (starRingEnd ℂ) h0
    simpa [inner_conj_symm, map_mul] using h2
  have hcond : ∀ x : A.domain,
      inner ℂ ((starRingEnd ℂ) z • y) ((x : H)) = inner ℂ y (A x) := by
    intro x
    rw [inner_smul_left, Complex.conj_conj, hz' x]
  have hydom' : y ∈ (A.adjoint).domain :=
    LinearPMap.mem_adjoint_domain_of_exists y ⟨(starRingEnd ℂ) z • y, hcond⟩
  have hydom : y ∈ A.domain := by rwa [hAeq] at hydom'
  have hsym := isFormalAdjoint_of_isSelfAdjoint hA
  have hdiff : ∀ x : A.domain,
      inner ℂ (A ⟨y, hydom⟩ - (starRingEnd ℂ) z • y) ((x : H)) = 0 := by
    intro x
    rw [inner_sub_left, hsym ⟨y, hydom⟩ x, hcond x, sub_self]
  have hdomperp : (A.domain)ᗮ = ⊥ :=
    Submodule.topologicalClosure_eq_top_iff.1
      ((Submodule.dense_iff_topologicalClosure_eq_top).1 hdense)
  have hmem : A ⟨y, hydom⟩ - (starRingEnd ℂ) z • y ∈ (A.domain)ᗮ := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    exact hdiff ⟨u, hu⟩
  have happ : A ⟨y, hydom⟩ = (starRingEnd ℂ) z • y := by
    have := (Submodule.eq_bot_iff _).1 hdomperp _ hmem
    linear_combination (norm := module) this
  have hzc : ((starRingEnd ℂ) z).im ≠ 0 := by
    simpa using hz
  exact eq_zero_of_apply_eq_smul hA hzc (x := ⟨y, hydom⟩) happ

/-- **The shifted operator is surjective.** -/
theorem surjective_shiftedMap {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) :
    Function.Surjective (shiftedMap A z) := by
  have hclosed : IsClosed ((LinearMap.range (shiftedMap A z) : Submodule ℂ H) : Set H) :=
    isClosed_range_shiftedMap hA hz
  have htop := Submodule.topologicalClosure_eq_top_iff.2 (orthogonal_range_shiftedMap_eq_bot hA hz)
  have hself : (LinearMap.range (shiftedMap A z)).topologicalClosure =
      LinearMap.range (shiftedMap A z) :=
    SetLike.coe_injective hclosed.closure_eq
  rw [hself] at htop
  exact LinearMap.range_eq_top.1 htop

/-- **The resolvent theorem.**  At every nonreal parameter a self-adjoint operator shifts to a
bijection of its domain onto the whole space. -/
theorem bijective_shiftedMap {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {z : ℂ} (hz : z.im ≠ 0) :
    Function.Bijective (shiftedMap A z) :=
  ⟨injective_shiftedMap hA hz, surjective_shiftedMap hA hz⟩

/-! ## The reducing-subspace lemma -/

/-- `B` is the restriction of `A` to the closed subspace `M`. -/
structure IsPMapRestriction (A : H →ₗ.[ℂ] H) (M : Submodule ℂ H) (B : M →ₗ.[ℂ] M) : Prop where
  /-- The domain of the restriction sits inside the domain of the ambient operator. -/
  domain_mem : ∀ x : B.domain, ((x : M) : H) ∈ A.domain
  /-- The two operators agree there. -/
  apply_eq : ∀ x : B.domain, A ⟨((x : M) : H), domain_mem x⟩ = ((B x : M) : H)

/-- **The reducing-subspace lemma.**  If a self-adjoint restriction of a self-adjoint operator to a
closed subspace `M` is itself self-adjoint, then the resolvent of the ambient operator maps `M`
into `M`: every solution of `(A - z) x = y` with `y` in `M` already lies in `M`. -/
theorem mem_of_shiftedMap_eq {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {M : Submodule ℂ H}
    [CompleteSpace M] {B : M →ₗ.[ℂ] M} (hB : IsSelfAdjoint B)
    (hres : IsPMapRestriction A M B) {z : ℂ} (hz : z.im ≠ 0) {y : H} (hy : y ∈ M)
    {x : A.domain} (hx : shiftedMap A z x = y) : (x : H) ∈ M := by
  obtain ⟨x', hx'⟩ := surjective_shiftedMap hB hz ⟨y, hy⟩
  have hmem := hres.domain_mem x'
  have himage : shiftedMap A z ⟨((x' : M) : H), hmem⟩ = y := by
    rw [shiftedMap_apply, hres.apply_eq x']
    have : ((B x' : M) : H) - z • ((x' : M) : H) = ((B x' - z • (x' : M) : M) : H) := by
      push_cast
      rfl
    rw [this]
    have hx'' : B x' - z • (x' : M) = (⟨y, hy⟩ : M) := hx'
    rw [hx'']
  have heq : x = ⟨((x' : M) : H), hmem⟩ :=
    injective_shiftedMap hA hz (by rw [hx, himage])
  rw [heq]
  exact (x' : M).2

/-! ## Transport of the eigenvalue-free property -/

/-- An operator has no eigenvectors. -/
def HasNoEigenvector (A : H →ₗ.[ℂ] H) : Prop :=
  ∀ (lam : ℂ) (x : A.domain), A x = lam • (x : H) → (x : H) = 0

/-- A self-adjoint operator has no nonreal eigenvalue. -/
theorem no_nonreal_eigenvector {A : H →ₗ.[ℂ] H} (hA : IsSelfAdjoint A) {lam : ℂ}
    (hlam : lam.im ≠ 0) (x : A.domain) (hx : A x = lam • (x : H)) : (x : H) = 0 :=
  eq_zero_of_apply_eq_smul hA hlam hx

omit [CompleteSpace H] in
/-- **Restrictions inherit the absence of eigenvectors.**  This is the spectral half of the
pullback-completion theorem: a self-adjoint operator that is a restriction of an eigenvector-free
operator to a closed subspace is itself eigenvector-free. -/
theorem hasNoEigenvector_of_restriction {A : H →ₗ.[ℂ] H} {M : Submodule ℂ H}
    {B : M →ₗ.[ℂ] M} (hres : IsPMapRestriction A M B) (hA : HasNoEigenvector A) :
    HasNoEigenvector B := by
  intro lam x hx
  have hmem := hres.domain_mem x
  have happ : A ⟨((x : M) : H), hmem⟩ = lam • (((x : M) : H)) := by
    rw [hres.apply_eq x, hx]
    push_cast
    rfl
  have := hA lam ⟨((x : M) : H), hmem⟩ happ
  exact Submodule.coe_eq_zero.1 this

end GaloisForLFunctions.HTGeometry
