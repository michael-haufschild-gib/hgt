import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Continuity
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-!
# The polar transport unitary between nearby subspaces

A map from a finite-dimensional inner product space into a Hilbert space that is close to an
isometry has a canonical unitary polar factor `T (T* T)^{-1/2}`.  The inverse square root is the
continuous functional calculus of `t ↦ t^{-1/2}` applied to the positive operator `T* T`, which is
close to the identity precisely when `T` is close to an isometry.

Continuity of the functional calculus in the operator then transports the estimate: the polar
factors converge in operator norm to the limiting isometry.  This is the general-index form of the
boundary transport of a nested exhaustion, where `T` is the compression of the inclusion of one
deficiency space by the projection onto another.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

variable {N : Type*} [NormedAddCommGroup N] [InnerProductSpace ℂ N] [CompleteSpace N]
  [Nontrivial N]

/-- The window of spectral values used by the inverse square root. -/
def nearOneWindow : Set ℝ := Set.Icc (1 / 2 : ℝ) (3 / 2)

theorem isCompact_nearOneWindow : IsCompact nearOneWindow := isCompact_Icc

theorem pos_of_mem_nearOneWindow {t : ℝ} (ht : t ∈ nearOneWindow) : 0 < t := by
  have := ht.1
  linarith

/-- **Spectral localization near the identity.**  An operator within `1/2` of the identity has
real spectrum inside the window. -/
theorem spectrum_subset_nearOneWindow {A : N →L[ℂ] N}
    (hnorm : ‖A - 1‖ ≤ 1 / 2) : spectrum ℝ A ⊆ nearOneWindow := by
  intro t ht
  have hmapone : (algebraMap ℝ (N →L[ℂ] N)) 1 = 1 := map_one _
  have hsub : t - 1 ∈ spectrum ℝ (A - 1) := by
    rw [← hmapone, ← spectrum.sub_singleton_eq]
    exact ⟨t, ht, 1, rfl, rfl⟩
  have hball := spectrum.subset_closedBall_norm (𝕜 := ℝ) (A - 1) hsub
  rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hball
  have habs : |t - 1| ≤ 1 / 2 := le_trans hball hnorm
  rw [abs_le] at habs
  constructor <;> [linarith [habs.1]; linarith [habs.2]]

/-- The inverse square root of an operator near the identity. -/
noncomputable def invSqrtNearOne (A : N →L[ℂ] N) : N →L[ℂ] N :=
  cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) A

theorem continuousOn_invSqrtFun :
    ContinuousOn (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) nearOneWindow := by
  refine ContinuousOn.rpow_const (by fun_prop) ?_
  intro t ht
  exact Or.inl (ne_of_gt (pos_of_mem_nearOneWindow ht))

omit [Nontrivial N] in
theorem isSelfAdjoint_invSqrtNearOne (A : N →L[ℂ] N) :
    IsSelfAdjoint (invSqrtNearOne A) := by
  rw [invSqrtNearOne]
  exact cfc_predicate (R := ℝ) _ A

/-- **The inverse square root inverts the operator symmetrically.** -/
theorem invSqrtNearOne_mul_mul {A : N →L[ℂ] N} (hA : IsSelfAdjoint A)
    (hnorm : ‖A - 1‖ ≤ 1 / 2) :
    invSqrtNearOne A * A * invSqrtNearOne A = 1 := by
  have hspec := spectrum_subset_nearOneWindow hnorm
  have hcont : ContinuousOn (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) (spectrum ℝ A) :=
    continuousOn_invSqrtFun.mono hspec
  have hid : ContinuousOn (fun t : ℝ => t) (spectrum ℝ A) := continuousOn_id
  have hA' : A = cfc (fun t : ℝ => t) A := (cfc_id ℝ A).symm
  have h1 : cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) A * cfc (fun t : ℝ => t) A
      = cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2) * t) A :=
    (cfc_mul _ _ A hcont hid).symm
  have h2 : cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2) * t) A
      * cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) A
      = cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2) * t * t ^ (-(1 : ℝ) / 2)) A :=
    (cfc_mul _ _ A (hcont.mul hid) hcont).symm
  calc invSqrtNearOne A * A * invSqrtNearOne A
      = cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) A * cfc (fun t : ℝ => t) A
          * cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) A := by
        rw [invSqrtNearOne, ← hA']
    _ = cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2) * t * t ^ (-(1 : ℝ) / 2)) A := by
        rw [h1, h2]
    _ = cfc (fun _ : ℝ => (1 : ℝ)) A := by
        refine cfc_congr ?_
        intro t ht
        have hpos : 0 < t := pos_of_mem_nearOneWindow (hspec ht)
        have hsum : t ^ (-(1 : ℝ) / 2 + 1 + -(1 : ℝ) / 2)
            = t ^ (-(1 : ℝ) / 2) * t * t ^ (-(1 : ℝ) / 2) := by
          rw [Real.rpow_add hpos, Real.rpow_add hpos, Real.rpow_one]
        have hzero : (-(1 : ℝ) / 2 + 1 + -(1 : ℝ) / 2) = 0 := by norm_num
        rw [hzero, Real.rpow_zero] at hsum
        exact hsum.symm
    _ = 1 := cfc_one ℝ A

/-- **Continuity of the inverse square root.**  Along a family of self-adjoint operators
converging in norm to the identity, the inverse square roots converge in norm to the identity. -/
theorem tendsto_invSqrtNearOne {ι : Type*} {l : Filter ι} {A : ι → N →L[ℂ] N}
    (hsa : ∀ i, IsSelfAdjoint (A i)) (hnorm : ∀ i, ‖A i - 1‖ ≤ 1 / 2)
    (h : Tendsto A l (𝓝 1)) :
    Tendsto (fun i => invSqrtNearOne (A i)) l (𝓝 1) := by
  have hcontOn := continuousOn_cfc (𝕜 := ℝ) (N →L[ℂ] N) isCompact_nearOneWindow
    (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) continuousOn_invSqrtFun
  have hmem : ∀ i, A i ∈ {a : N →L[ℂ] N | IsSelfAdjoint a ∧ spectrum ℝ a ⊆ nearOneWindow} :=
    fun i => ⟨hsa i, spectrum_subset_nearOneWindow (hnorm i)⟩
  have hsa1 : IsSelfAdjoint (1 : N →L[ℂ] N) := star_one _
  have hspec1 : spectrum ℝ (1 : N →L[ℂ] N) ⊆ nearOneWindow := by
    rw [spectrum.one_eq]
    intro t ht
    rw [Set.mem_singleton_iff] at ht
    subst ht
    constructor <;> norm_num
  have hone : (1 : N →L[ℂ] N) ∈ {a : N →L[ℂ] N | IsSelfAdjoint a ∧
      spectrum ℝ a ⊆ nearOneWindow} := ⟨hsa1, hspec1⟩
  have hlim : Tendsto (fun i => cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) (A i)) l
      (𝓝 (cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) (1 : N →L[ℂ] N))) := by
    refine ((hcontOn _ hone).tendsto).comp ?_
    exact tendsto_nhdsWithin_iff.mpr ⟨h, Filter.Eventually.of_forall hmem⟩
  have hval : cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) (1 : N →L[ℂ] N) = 1 := by
    have hcg : cfc (fun t : ℝ => t ^ (-(1 : ℝ) / 2)) (1 : N →L[ℂ] N)
        = cfc (fun _ : ℝ => (1 : ℝ)) (1 : N →L[ℂ] N) := by
      refine cfc_congr ?_
      intro t ht
      rw [spectrum.one_eq, Set.mem_singleton_iff] at ht
      rw [ht]
      norm_num
    rw [hcg]
    exact cfc_one ℝ _
  rwa [hval] at hlim

/-! ## The polar factor -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

omit [Nontrivial N] in
open ContinuousLinearMap in
/-- The Gram operator of a map out of a finite-dimensional space. -/
theorem isSelfAdjoint_gram (T : N →L[ℂ] E) : IsSelfAdjoint (adjoint T ∘L T) := by
  unfold IsSelfAdjoint
  rw [show star (adjoint T ∘L T) = adjoint (adjoint T ∘L T) from rfl, adjoint_comp,
    adjoint_adjoint]

omit [Nontrivial N] in
open ContinuousLinearMap in
/-- The Gram operator is close to the identity when the map is close to an isometry. -/
theorem norm_gram_sub_one_le {T iota : N →L[ℂ] E}
    (hiso : adjoint iota ∘L iota = 1) (hnorm : ‖iota‖ ≤ 1) :
    ‖adjoint T ∘L T - 1‖ ≤ ‖T - iota‖ * (2 + ‖T - iota‖) := by
  have hsplit : adjoint T ∘L T - 1
      = adjoint T ∘L (T - iota) + adjoint (T - iota) ∘L iota := by
    rw [← hiso, map_sub, comp_sub, sub_comp]
    abel
  have hT : ‖T‖ ≤ 1 + ‖T - iota‖ := by
    have := norm_add_le (T - iota) iota
    simp only [sub_add_cancel] at this
    linarith
  have h1 : ‖adjoint T ∘L (T - iota)‖ ≤ ‖T‖ * ‖T - iota‖ := by
    refine le_trans (opNorm_comp_le _ _) ?_
    rw [LinearIsometryEquiv.norm_map]
  have h2 : ‖adjoint (T - iota) ∘L iota‖ ≤ ‖T - iota‖ * ‖iota‖ := by
    refine le_trans (opNorm_comp_le _ _) ?_
    rw [LinearIsometryEquiv.norm_map]
  rw [hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have hd : (0:ℝ) ≤ ‖T - iota‖ := norm_nonneg _
  nlinarith [h1, h2, hT, hd, norm_nonneg iota]

/-- The polar factor of a map that is close to an isometry. -/
noncomputable def polarTransport (T : N →L[ℂ] E) : N →L[ℂ] E :=
  T ∘L invSqrtNearOne (ContinuousLinearMap.adjoint T ∘L T)

open ContinuousLinearMap in
/-- **The polar factor is an isometry.** -/
theorem adjoint_polarTransport_comp_self {T : N →L[ℂ] E}
    (hnorm : ‖adjoint T ∘L T - 1‖ ≤ 1 / 2) :
    adjoint (polarTransport T) ∘L polarTransport T = 1 := by
  set A : N →L[ℂ] N := adjoint T ∘L T with hA
  set S : N →L[ℂ] N := invSqrtNearOne A with hS
  have hsa : IsSelfAdjoint S := isSelfAdjoint_invSqrtNearOne A
  have hkey : S * A * S = 1 := invSqrtNearOne_mul_mul (isSelfAdjoint_gram T) hnorm
  have hstar : adjoint S = S := hsa
  calc adjoint (polarTransport T) ∘L polarTransport T
      = adjoint S ∘L (adjoint T ∘L T) ∘L S := by
        rw [polarTransport, adjoint_comp]
        rfl
    _ = S * A * S := by rw [hstar, hA]; rfl
    _ = 1 := hkey

open ContinuousLinearMap in
theorem norm_polarTransport_apply {T : N →L[ℂ] E}
    (hnorm : ‖adjoint T ∘L T - 1‖ ≤ 1 / 2) (x : N) :
    ‖polarTransport T x‖ = ‖x‖ := by
  have h := adjoint_polarTransport_comp_self hnorm
  have hinner : (inner ℂ (polarTransport T x) (polarTransport T x) : ℂ) = inner ℂ x x := by
    rw [← adjoint_inner_left]
    have : (adjoint (polarTransport T)) (polarTransport T x)
        = ((adjoint (polarTransport T) ∘L polarTransport T) : N →L[ℂ] N) x := rfl
    rw [this, h]
    rfl
  have h2 : ‖polarTransport T x‖ ^ 2 = ‖x‖ ^ 2 := by
    have e1 : RCLike.re (inner ℂ (polarTransport T x) (polarTransport T x))
        = ‖polarTransport T x‖ ^ 2 := inner_self_eq_norm_sq _
    have e2 : RCLike.re (inner ℂ x x) = ‖x‖ ^ 2 := inner_self_eq_norm_sq _
    rw [← e1, ← e2, hinner]
  have := norm_nonneg (polarTransport T x)
  nlinarith [norm_nonneg x, h2]

open ContinuousLinearMap in
/-- **The polar factor converges to the limiting isometry.** -/
theorem tendsto_polarTransport {ι : Type*} {l : Filter ι} {T : ι → N →L[ℂ] E} {iota : N →L[ℂ] E}
    (hiso : adjoint iota ∘L iota = 1) (hnorm : ‖iota‖ ≤ 1)
    (hsmall : ∀ i, ‖adjoint (T i) ∘L T i - 1‖ ≤ 1 / 2)
    (hd : Tendsto (fun i => ‖T i - iota‖) l (𝓝 0)) :
    Tendsto (fun i => ‖polarTransport (T i) - iota‖) l (𝓝 0) := by
  set A : ι → N →L[ℂ] N := fun i => adjoint (T i) ∘L T i with hA
  have hAone : Tendsto A l (𝓝 1) := by
    have hbound : ∀ i, ‖A i - 1‖ ≤ ‖T i - iota‖ * (2 + ‖T i - iota‖) := fun i =>
      norm_gram_sub_one_le hiso hnorm
    have hzero : Tendsto (fun i => ‖T i - iota‖ * (2 + ‖T i - iota‖)) l (𝓝 0) := by
      have := hd.mul (hd.const_add 2)
      simpa using this
    have hnormzero : Tendsto (fun i => ‖A i - 1‖) l (𝓝 0) :=
      squeeze_zero (fun i => norm_nonneg _) hbound hzero
    have := tendsto_zero_iff_norm_tendsto_zero.mpr hnormzero
    simpa using this.add_const (1 : N →L[ℂ] N)
  have hS : Tendsto (fun i => invSqrtNearOne (A i)) l (𝓝 1) :=
    tendsto_invSqrtNearOne (fun i => isSelfAdjoint_gram (T i)) hsmall hAone
  have hSone : Tendsto (fun i => ‖invSqrtNearOne (A i) - 1‖) l (𝓝 0) := by
    simpa using (hS.sub (tendsto_const_nhds (x := (1 : N →L[ℂ] N)))).norm
  have hsplit : ∀ i, polarTransport (T i) - iota
      = (T i - iota) ∘L invSqrtNearOne (A i) + iota ∘L (invSqrtNearOne (A i) - 1) := by
    intro i
    rw [polarTransport, sub_comp, comp_sub]
    simp
    abel
  have hbnd : ∀ i, ‖polarTransport (T i) - iota‖
      ≤ ‖T i - iota‖ * (1 + ‖invSqrtNearOne (A i) - 1‖) + ‖invSqrtNearOne (A i) - 1‖ := by
    intro i
    rw [hsplit i]
    refine le_trans (norm_add_le _ _) ?_
    have h1 : ‖(T i - iota) ∘L invSqrtNearOne (A i)‖
        ≤ ‖T i - iota‖ * (1 + ‖invSqrtNearOne (A i) - 1‖) := by
      refine le_trans (opNorm_comp_le _ _) ?_
      refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
      have := norm_add_le (invSqrtNearOne (A i) - 1) (1 : N →L[ℂ] N)
      simp only [sub_add_cancel] at this
      have hone : ‖(1 : N →L[ℂ] N)‖ ≤ 1 := le_of_eq norm_one
      linarith
    have h2 : ‖iota ∘L (invSqrtNearOne (A i) - 1)‖ ≤ ‖invSqrtNearOne (A i) - 1‖ := by
      refine le_trans (opNorm_comp_le _ _) ?_
      have := mul_le_mul_of_nonneg_right hnorm (norm_nonneg (invSqrtNearOne (A i) - 1))
      simpa using this
    linarith
  have hzero : Tendsto (fun i => ‖T i - iota‖ * (1 + ‖invSqrtNearOne (A i) - 1‖)
      + ‖invSqrtNearOne (A i) - 1‖) l (𝓝 0) := by
    have h1 : Tendsto (fun i => ‖T i - iota‖ * (1 + ‖invSqrtNearOne (A i) - 1‖)) l (𝓝 0) := by
      have := hd.mul (hSone.const_add 1)
      simpa using this
    simpa using h1.add hSone
  exact squeeze_zero (fun i => norm_nonneg _) hbnd hzero

open ContinuousLinearMap in
/-- **The polar factor has the same range as the original map.**  Hence it is a unitary of the
finite-dimensional source onto that range. -/
theorem range_polarTransport {T : N →L[ℂ] E}
    (hnorm : ‖adjoint T ∘L T - 1‖ ≤ 1 / 2) :
    LinearMap.range (polarTransport T : N →ₗ[ℂ] E) = LinearMap.range (T : N →ₗ[ℂ] E) := by
  set A : N →L[ℂ] N := adjoint T ∘L T with hA
  set S : N →L[ℂ] N := invSqrtNearOne A with hS
  have hkey : S * A * S = 1 := invSqrtNearOne_mul_mul (isSelfAdjoint_gram T) hnorm
  apply le_antisymm
  · rintro y ⟨x, rfl⟩
    exact ⟨S x, rfl⟩
  · rintro y ⟨x, rfl⟩
    refine ⟨A (S x), ?_⟩
    have hx : S (A (S x)) = x := by
      have := congrArg (fun f : N →L[ℂ] N => f x) hkey
      simpa using this
    show T (S (A (S x))) = T x
    rw [hx]

/-! ## Norm convergence of the projections themselves -/

omit [Nontrivial N] in
open ContinuousLinearMap in
/-- **Projections built from converging isometries converge in operator norm.**  Writing an
orthogonal projection as `J J*` for an isometry `J` onto its range, the difference of two such
projections splits as `(J - J₀)J* + J₀(J - J₀)*`, so the projections converge in norm as soon as
the isometries do.  This is what upgrades strong convergence of finite-rank deficiency projections
to norm convergence: the equal rank enters through the existence of the isometries. -/
theorem tendsto_opNorm_selfComp_sub {ι : Type*} {l : Filter ι} {J : ι → N →L[ℂ] E}
    {J₀ : N →L[ℂ] E} (hJ : ∀ i, ‖J i‖ ≤ 1) (hJ₀ : ‖J₀‖ ≤ 1)
    (h : Tendsto (fun i => ‖J i - J₀‖) l (𝓝 0)) :
    Tendsto (fun i => ‖J i ∘L adjoint (J i) - J₀ ∘L adjoint J₀‖) l (𝓝 0) := by
  have hsplit : ∀ i, J i ∘L adjoint (J i) - J₀ ∘L adjoint J₀
      = (J i - J₀) ∘L adjoint (J i) + J₀ ∘L adjoint (J i - J₀) := by
    intro i
    rw [map_sub, sub_comp, comp_sub]
    abel
  have hbound : ∀ i, ‖J i ∘L adjoint (J i) - J₀ ∘L adjoint J₀‖ ≤ 2 * ‖J i - J₀‖ := by
    intro i
    rw [hsplit i]
    refine le_trans (norm_add_le _ _) ?_
    have h1 : ‖(J i - J₀) ∘L adjoint (J i)‖ ≤ ‖J i - J₀‖ := by
      refine le_trans (opNorm_comp_le _ _) ?_
      rw [LinearIsometryEquiv.norm_map]
      have := mul_le_mul_of_nonneg_left (hJ i) (norm_nonneg (J i - J₀))
      simpa using this
    have h2 : ‖J₀ ∘L adjoint (J i - J₀)‖ ≤ ‖J i - J₀‖ := by
      refine le_trans (opNorm_comp_le _ _) ?_
      rw [LinearIsometryEquiv.norm_map]
      have := mul_le_mul_of_nonneg_right hJ₀ (norm_nonneg (J i - J₀))
      simpa using this
    linarith
  have hzero : Tendsto (fun i => 2 * ‖J i - J₀‖) l (𝓝 0) := by
    simpa using h.const_mul 2
  exact squeeze_zero (fun i => norm_nonneg _) hbound hzero

end GaloisForLFunctions.HTGeometry
