import GaloisForLFunctions.HTGeometry.CStarEnvelope
import GaloisForLFunctions.HTGeometry.CompactKernelRankOneDensity
import GaloisForLFunctions.HTGeometry.CompactOperatorIdealSimplicity
import GaloisForLFunctions.HTGeometry.BoundaryCoronaCStarAlgebra
import GaloisForLFunctions.HTGeometry.HilbertSchmidtCompact

/-!
# (SAC.14) The full crossed product `C₀(ℝ) ⋊ ℝ` is the compact operators on `L²(ℝ)`

The translation action `(α_r f)(x) = f(x - r)` of `ℝ` on `C₀(ℝ)` has the twisted convolution core
`C_c(ℝ × ℝ)`, `(F₁ ⋆ F₂)(s, x) = ∫ F₁(r, x) F₂(s - r, x - r) dr`, `F*(s, x) = conj F(-s, x - s)`;
in the kernel picture `k(x, y) = F(x - y, x)` this is kernel composition (`KernelAlg.fibre_mul`,
`KernelAlg.fibre_star`, `KernelAlg.toTwisted`).  The **full crossed product** is its enveloping
C⋆-algebra for the `L¹(ℝ, C₀(ℝ))` norm.

* The Schrödinger representation (integral operators on `L²(ℝ)`) is `L¹`-bounded (Schur), so it
  extends to the full crossed product.
* **Faithfulness (Stone–von Neumann).**  With a unit vector `φ₀ ∈ C_c(ℝ)` the corner
  `E = e_{φ₀φ₀}` satisfies `E w E ∈ ℂ E`.  If `π(y) = 0`, then for each column `a = y e_{ψφ₀}` the
  element `a* a = E(e_{φ₀ψ} y* y e_{ψφ₀})E` is a scalar multiple of `E` killed by `π`, hence zero,
  so `y` annihilates all rank-one kernels; these are dense, so `y y* = 0` and `y = 0`.  An injective
  `*`-homomorphism of C⋆-algebras is isometric.
* **Image.**  Each `π(y)` is compact (limit of Hilbert–Schmidt operators); the closed range contains
  every `|ξ⟩⟨η|` (density of `C_c(ℝ)` in `L²(ℝ)`), hence every finite-rank operator, hence every
  compact operator.

Hence `C₀(ℝ) ⋊ ℝ ≃⋆ₐ 𝒦(L²(ℝ))` (`realCrossedProductEquivCompact`).
-/

set_option autoImplicit false

open MeasureTheory Set Filter Topology
open scoped CompactlySupported

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The twisted convolution picture -/

/-- **Twisted convolution.**  In the picture `F(s, x) = k(x, x - s)` the kernel product is the
crossed-product convolution for the translation action `(α_r f)(x) = f(x - r)`:
`(F₁ ⋆ F₂)(s, x) = ∫ F₁(r, x) (α_r F₂(s - r))(x) dr`. -/
theorem KernelAlg.fibre_mul (k₁ k₂ : KernelAlg) (s x : ℝ) :
    (k₁ * k₂).fibre s x = ∫ r, k₁.fibre r x * k₂.fibre (s - r) (x - r) := by
  simp only [KernelAlg.fibre_apply, KernelAlg.mul_apply]
  have h : (fun r => k₁.toFun (x, x - r) * k₂.toFun (x - r, x - r - (s - r))) =
      fun r => (fun y => k₁.toFun (x, y) * k₂.toFun (y, x - s)) (x - r) := by
    funext r
    rw [show x - r - (s - r) = x - s by ring]
  rw [h, integral_sub_left_eq_self (fun y => k₁.toFun (x, y) * k₂.toFun (y, x - s)) volume x]

/-- **Twisted involution**: `F*(s, x) = conj F(-s, x - s)`, i.e. `F*(s) = α_s(F(-s)*)`. -/
theorem KernelAlg.fibre_star (k : KernelAlg) (s x : ℝ) :
    (star k).fibre s x = star (k.fibre (-s) (x - s)) := by
  simp only [KernelAlg.fibre_apply, KernelAlg.star_apply]
  congr 3
  ring

/-- The twisted convolution picture `k ↦ F`, `F(s, x) = k(x, x - s)`. -/
def KernelAlg.toTwisted (k : KernelAlg) : C_c(ℝ × ℝ, ℂ) where
  toFun p := k.toFun (p.2, p.2 - p.1)
  continuous_toFun := k.continuous_toFun.comp (continuous_snd.prodMk (continuous_snd.sub continuous_fst))
  hasCompactSupport' := by
    let e : ℝ × ℝ ≃ₜ ℝ × ℝ :=
      { toFun := fun p => (p.2, p.2 - p.1)
        invFun := fun q => (q.1 - q.2, q.1)
        left_inv := fun p => by ext <;> simp
        right_inv := fun q => by ext <;> simp
        continuous_toFun := continuous_snd.prodMk (continuous_snd.sub continuous_fst)
        continuous_invFun := (continuous_fst.sub continuous_snd).prodMk continuous_fst }
    exact k.hasCompactSupport_toFun.comp_homeomorph e

/-- Every compactly supported continuous `F(s, x)` comes from a unique kernel. -/
def KernelAlg.ofTwisted (F : C_c(ℝ × ℝ, ℂ)) : KernelAlg :=
  (show C_c(ℝ × ℝ, ℂ) from
  { toFun := fun q => F (q.1 - q.2, q.1)
    continuous_toFun := F.continuous.comp ((continuous_fst.sub continuous_snd).prodMk continuous_fst)
    hasCompactSupport' := by
      let e : ℝ × ℝ ≃ₜ ℝ × ℝ :=
        { toFun := fun q => (q.1 - q.2, q.1)
          invFun := fun p => (p.2, p.2 - p.1)
          left_inv := fun q => by ext <;> simp
          right_inv := fun p => by ext <;> simp
          continuous_toFun := (continuous_fst.sub continuous_snd).prodMk continuous_fst
          continuous_invFun := continuous_snd.prodMk (continuous_snd.sub continuous_fst) }
      exact F.hasCompactSupport.comp_homeomorph e })

theorem KernelAlg.toTwisted_ofTwisted (F : C_c(ℝ × ℝ, ℂ)) : (KernelAlg.ofTwisted F).toTwisted = F := by
  ext ⟨s, x⟩
  change F (x - (x - s), x) = F (s, x)
  congr 1
  ext <;> simp

theorem KernelAlg.ofTwisted_toTwisted (k : KernelAlg) : KernelAlg.ofTwisted k.toTwisted = k := by
  refine KernelAlg.ext fun ⟨x, y⟩ => ?_
  change k.toFun (x, x - (x - y)) = k.toFun (x, y)
  congr 2
  ring

theorem KernelAlg.toTwisted_apply (k : KernelAlg) (s x : ℝ) :
    k.toTwisted (s, x) = k.fibre s x := rfl

/-! ## The full crossed product `C₀(ℝ) ⋊ ℝ` and its Schrödinger representation -/

/-- **The full crossed product `C₀(ℝ) ⋊ ℝ`** for translation: the enveloping C⋆-algebra of the
twisted convolution core (`KernelAlg`, in the kernel picture `k(x, y) = F(x - y, x)`) for the
`L¹(ℝ, C₀(ℝ))` norm. -/
abbrev RealCrossedProduct : Type 1 := CStarEnvelope KernelAlg KernelAlg.l1Norm

/-- The Schrödinger (integral) representation as an `L¹`-bounded representation. -/
def schrodingerRep : BoundedRep KernelAlg KernelAlg.l1Norm where
  H := L2Real
  π := KernelAlg.opHom
  bound := KernelAlg.norm_op_le_l1Norm

/-- The Schrödinger representation of the full crossed product on `L²(ℝ)`. -/
def schrodinger : RealCrossedProduct →⋆ₙₐ[ℂ] (L2Real →L[ℂ] L2Real) := schrodingerRep.extend

theorem schrodinger_toEnvelope (k : KernelAlg) :
    schrodinger (toEnvelope KernelAlg KernelAlg.l1Norm k) = k.op := rfl

theorem continuous_schrodinger : Continuous schrodinger :=
  (NonUnitalStarAlgHom.instContinuousLinearMapClassComplex (F := RealCrossedProduct →⋆ₙₐ[ℂ]
    (L2Real →L[ℂ] L2Real))).map_continuous schrodinger

/-- The canonical map of the core. -/
abbrev toRCP : KernelAlg →⋆ₙₐ[ℂ] RealCrossedProduct := toEnvelope KernelAlg KernelAlg.l1Norm

theorem norm_toRCP_le (k : KernelAlg) : ‖toRCP k‖ ≤ k.l1Norm :=
  norm_toEnvelope_le KernelAlg KernelAlg.l1Norm k k.l1Norm_nonneg

/-- The rank-one kernels are dense in the full crossed product. -/
theorem exists_rankOneSpan_dist_lt (y : RealCrossedProduct) {ε : ℝ} (hε : 0 < ε) :
    ∃ k ∈ rankOneSpan, dist y (toRCP k) < ε := by
  obtain ⟨k₀, hk₀⟩ := (toEnvelope_dense KernelAlg KernelAlg.l1Norm).exists_dist_lt y
    (by positivity : (0 : ℝ) < ε / 2)
  obtain ⟨k, hk, hkk⟩ := k₀.exists_rankOneSpan_l1Norm_sub_lt (by positivity : (0 : ℝ) < ε / 2)
  refine ⟨k, hk, ?_⟩
  calc dist y (toRCP k) ≤ dist y (toRCP k₀) + dist (toRCP k₀) (toRCP k) := dist_triangle _ _ _
    _ < ε / 2 + ε / 2 := by
        refine add_lt_add_of_lt_of_le hk₀ ?_
        rw [dist_eq_norm, ← map_sub]
        exact (norm_toRCP_le _).trans hkk.le
    _ = ε := by ring

/-- Elements annihilated by the rank-one kernels are annihilated by everything. -/
theorem mul_eq_zero_of_rankOne {y : RealCrossedProduct}
    (h : ∀ φ ψ : C_c(ℝ, ℂ), y * toRCP (KernelAlg.rankOneKernel φ ψ) = 0) (w : RealCrossedProduct) :
    y * w = 0 := by
  have hspan : ∀ k ∈ rankOneSpan, y * toRCP k = 0 := by
    intro k hk
    induction hk using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨⟨φ, ψ⟩, rfl⟩ := hg
      exact h φ ψ
    | zero => rw [map_zero, mul_zero]
    | add x z _ _ hx hz => rw [map_add, mul_add, hx, hz, add_zero]
    | smul c x _ hx => rw [map_smul, mul_smul_comm, hx, smul_zero]
  have hclosed : IsClosed {w : RealCrossedProduct | y * w = 0} :=
    isClosed_eq (continuous_const.mul continuous_id) continuous_const
  have hsub : toRCP '' (rankOneSpan : Set KernelAlg) ⊆ {w | y * w = 0} := by
    rintro _ ⟨k, hk, rfl⟩
    exact hspan k hk
  have hw : w ∈ closure (toRCP '' (rankOneSpan : Set KernelAlg)) :=
    Metric.mem_closure_iff.mpr fun ε hε => by
      obtain ⟨k, hk, hdist⟩ := exists_rankOneSpan_dist_lt w hε
      exact ⟨toRCP k, ⟨k, hk, rfl⟩, hdist⟩
  exact hclosed.closure_subset_iff.mpr hsub hw

/-! ## A unit vector and the corner projection -/

theorem KernelAlg.mul_rankOneKernel (k : KernelAlg) (φ ψ : C_c(ℝ, ℂ)) :
    k * KernelAlg.rankOneKernel φ ψ = KernelAlg.rankOneKernel (k.applyCc φ) ψ := by
  refine KernelAlg.ext fun ⟨x, z⟩ => ?_
  rw [KernelAlg.mul_apply, KernelAlg.rankOneKernel_apply, KernelAlg.applyCc_apply,
    ← integral_mul_const]
  congr 1
  funext y
  rw [KernelAlg.rankOneKernel_apply]
  ring

theorem cc2_tentCc_ne_zero : cc2 (tentCc 1) ≠ 0 := by
  intro h
  have hae : (tentCc 1 : ℝ → ℂ) =ᵐ[volume] fun _ => 0 := by
    filter_upwards [cc2_ae (tentCc 1), Lp.coeFn_zero ℂ 2 (volume : Measure ℝ)] with x h1 h2
    rw [← h1, h, h2]
    rfl
  have heq := (Continuous.ae_eq_iff_eq volume (tentCc 1).continuous continuous_const).mp hae
  have h0 := congrFun heq 0
  change ((tentReal 1 0 : ℝ) : ℂ) = 0 at h0
  rw [tentReal_eq_one (by norm_num)] at h0
  norm_num at h0

/-- A normalized bump `φ₀ ∈ C_c(ℝ)`, `‖φ₀‖₂ = 1`. -/
def unitBump : C_c(ℝ, ℂ) := ((‖cc2 (tentCc 1)‖⁻¹ : ℝ) : ℂ) • tentCc 1

theorem norm_cc2_unitBump : ‖cc2 unitBump‖ = 1 := by
  have hpos : 0 < ‖cc2 (tentCc 1)‖ := norm_pos_iff.mpr cc2_tentCc_ne_zero
  rw [unitBump, KernelAlg.cc2_smul, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hpos), inv_mul_cancel₀ hpos.ne']

theorem inner_cc2_unitBump : inner ℂ (cc2 unitBump) (cc2 unitBump) = 1 := by
  rw [inner_self_eq_norm_sq_to_K, norm_cc2_unitBump]
  simp

/-- The corner projection `E = e_{φ₀ φ₀}` of the full crossed product. -/
def rcpCorner : RealCrossedProduct := toRCP (KernelAlg.rankOneKernel unitBump unitBump)

theorem toRCP_rankOne_mul (φ ψ φ' ψ' : C_c(ℝ, ℂ)) :
    toRCP (KernelAlg.rankOneKernel φ ψ) * toRCP (KernelAlg.rankOneKernel φ' ψ') =
      inner ℂ (cc2 ψ) (cc2 φ') • toRCP (KernelAlg.rankOneKernel φ ψ') := by
  rw [← map_mul, KernelAlg.rankOneKernel_mul, map_smul]

theorem star_toRCP_rankOne (φ ψ : C_c(ℝ, ℂ)) :
    star (toRCP (KernelAlg.rankOneKernel φ ψ)) = toRCP (KernelAlg.rankOneKernel ψ φ) := by
  rw [← map_star, KernelAlg.star_rankOneKernel]

theorem rcpCorner_mul_rankOne (ψ : C_c(ℝ, ℂ)) :
    rcpCorner * toRCP (KernelAlg.rankOneKernel unitBump ψ) =
      toRCP (KernelAlg.rankOneKernel unitBump ψ) := by
  rw [rcpCorner, toRCP_rankOne_mul, inner_cc2_unitBump, one_smul]

theorem rankOne_mul_rcpCorner (ψ : C_c(ℝ, ℂ)) :
    toRCP (KernelAlg.rankOneKernel ψ unitBump) * rcpCorner =
      toRCP (KernelAlg.rankOneKernel ψ unitBump) := by
  rw [rcpCorner, toRCP_rankOne_mul, inner_cc2_unitBump, one_smul]

/-- **Compression to the corner is scalar**: `E w E ∈ ℂ E` for every `w`. -/
theorem rcpCorner_compress (w : RealCrossedProduct) :
    ∃ c : ℂ, rcpCorner * w * rcpCorner = c • rcpCorner := by
  have hclosed : IsClosed {w : RealCrossedProduct |
      rcpCorner * w * rcpCorner ∈ Submodule.span ℂ {rcpCorner}} :=
    (Submodule.closed_of_finiteDimensional _).preimage
      ((continuous_const.mul continuous_id).mul continuous_const)
  have hcore : ∀ k : KernelAlg,
      rcpCorner * toRCP k * rcpCorner ∈ Submodule.span ℂ {rcpCorner} := by
    intro k
    rw [Submodule.mem_span_singleton]
    refine ⟨inner ℂ (cc2 unitBump) (cc2 (k.applyCc unitBump)), ?_⟩
    rw [mul_assoc, rcpCorner, ← map_mul, KernelAlg.mul_rankOneKernel, ← rcpCorner,
      rcpCorner, toRCP_rankOne_mul]
  have hw : w ∈ {w : RealCrossedProduct |
      rcpCorner * w * rcpCorner ∈ Submodule.span ℂ {rcpCorner}} :=
    hclosed.closure_subset_iff.mpr (by rintro _ ⟨k, rfl⟩; exact hcore k)
      ((toEnvelope_dense KernelAlg KernelAlg.l1Norm) w)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hw
  exact ⟨c, hc.symm⟩

theorem schrodinger_cornerProj_ne_zero : schrodinger rcpCorner ≠ 0 := by
  rw [rcpCorner, schrodinger_toEnvelope, KernelAlg.op_rankOneKernel]
  intro h
  have := congrArg norm h
  rw [InnerProductSpace.norm_rankOne, norm_cc2_unitBump, norm_zero, mul_one] at this
  exact one_ne_zero this

/-! ## Injectivity: Stone–von Neumann for `C₀(ℝ) ⋊ ℝ` -/

/-- **The Schrödinger representation of the full crossed product is faithful.** -/
theorem schrodinger_injective : Function.Injective schrodinger := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  -- `y` annihilates the columns `e_{ψ φ₀}`
  have hcol : ∀ ψ : C_c(ℝ, ℂ), y * toRCP (KernelAlg.rankOneKernel ψ unitBump) = 0 := by
    intro ψ
    set a := y * toRCP (KernelAlg.rankOneKernel ψ unitBump)
    have hEX := rcpCorner_mul_rankOne ψ
    have hYE := rankOne_mul_rcpCorner ψ
    have hstar : star a * a = rcpCorner * (toRCP (KernelAlg.rankOneKernel unitBump ψ) *
        (star y * y) * toRCP (KernelAlg.rankOneKernel ψ unitBump)) * rcpCorner := by
      calc star a * a = toRCP (KernelAlg.rankOneKernel unitBump ψ) * (star y * y) *
            toRCP (KernelAlg.rankOneKernel ψ unitBump) := by
            simp only [a, star_mul, star_toRCP_rankOne]
            noncomm_ring
        _ = (rcpCorner * toRCP (KernelAlg.rankOneKernel unitBump ψ)) * (star y * y) *
            (toRCP (KernelAlg.rankOneKernel ψ unitBump) * rcpCorner) := by rw [hEX, hYE]
        _ = _ := by noncomm_ring
    obtain ⟨c, hc⟩ := rcpCorner_compress (toRCP (KernelAlg.rankOneKernel unitBump ψ) *
      (star y * y) * toRCP (KernelAlg.rankOneKernel ψ unitBump))
    rw [hc] at hstar
    have hΦ : schrodinger (star a * a) = 0 := by
      simp only [a, map_mul, map_star, hy, zero_mul, mul_zero, star_zero]
    rw [hstar, map_smul] at hΦ
    have hc0 : c = 0 := by
      by_contra hc0
      exact schrodinger_cornerProj_ne_zero ((smul_eq_zero.mp hΦ).resolve_left hc0)
    rw [hc0, zero_smul] at hstar
    have hnorm : ‖a‖ * ‖a‖ = 0 := by rw [← CStarRing.norm_star_mul_self, hstar, norm_zero]
    exact norm_eq_zero.mp (mul_self_eq_zero.mp hnorm)
  -- hence `y` annihilates every rank-one kernel, so every element
  have hall : ∀ φ ψ : C_c(ℝ, ℂ), y * toRCP (KernelAlg.rankOneKernel φ ψ) = 0 := by
    intro φ ψ
    have h1 : toRCP (KernelAlg.rankOneKernel φ ψ) =
        toRCP (KernelAlg.rankOneKernel φ unitBump) * toRCP (KernelAlg.rankOneKernel unitBump ψ) := by
      rw [toRCP_rankOne_mul, inner_cc2_unitBump, one_smul]
    rw [h1, ← mul_assoc, hcol, zero_mul]
  have hyy : y * star y = 0 := mul_eq_zero_of_rankOne hall (star y)
  have hnorm : ‖star y‖ * ‖star y‖ = 0 := by
    rw [← CStarRing.norm_star_mul_self, star_star, hyy, norm_zero]
  exact star_eq_zero.mp (norm_eq_zero.mp (mul_self_eq_zero.mp hnorm))

/-- The Schrödinger representation is isometric. -/
theorem norm_schrodinger (y : RealCrossedProduct) : ‖schrodinger y‖ = ‖y‖ :=
  NonUnitalStarAlgHom.norm_map schrodinger schrodinger_injective y

/-! ## The image is the compact operators -/

/-- Every element of the full crossed product acts by a compact operator. -/
theorem isCompactOperator_schrodinger (y : RealCrossedProduct) :
    IsCompactOperator (schrodinger y) := by
  have hclosed : IsClosed {w : RealCrossedProduct | IsCompactOperator (schrodinger w)} :=
    (isClosed_setOf_isCompactOperator (𝕜₁ := ℂ) (M₁ := L2Real) (M₂ := L2Real)).preimage
      continuous_schrodinger
  refine hclosed.closure_subset_iff.mpr ?_ ((toEnvelope_dense KernelAlg KernelAlg.l1Norm) y)
  rintro _ ⟨k, rfl⟩
  exact (KernelAlg.isHilbertSchmidt_op k).isCompactOperator

theorem isClosed_range_schrodinger : IsClosed (Set.range schrodinger) :=
  (NonUnitalStarAlgHom.isometry schrodinger schrodinger_injective).isClosedEmbedding.isClosed_range

theorem rankOne_sub_rankOne (ξ η ξ' η' : L2Real) :
    InnerProductSpace.rankOne ℂ ξ η - InnerProductSpace.rankOne ℂ ξ' η' =
      InnerProductSpace.rankOne ℂ (ξ - ξ') η + InnerProductSpace.rankOne ℂ ξ' (η - η') := by
  rw [map_sub, map_sub, sub_apply]
  abel

theorem rankOne_mem_range_schrodinger (ξ η : L2Real) :
    InnerProductSpace.rankOne ℂ ξ η ∈ Set.range schrodinger := by
  refine isClosed_range_schrodinger.closure_subset_iff.mpr subset_rfl
    (Metric.mem_closure_iff.mpr fun ε hε => ?_)
  set δ : ℝ := min 1 (ε / (2 * (‖ξ‖ + ‖η‖ + 1)))
  have hδ : 0 < δ := lt_min one_pos (by positivity)
  have hδ1 : δ ≤ 1 := min_le_left _ _
  have hδε : δ * (‖ξ‖ + ‖η‖ + 1) ≤ ε / 2 := by
    calc δ * (‖ξ‖ + ‖η‖ + 1) ≤ ε / (2 * (‖ξ‖ + ‖η‖ + 1)) * (‖ξ‖ + ‖η‖ + 1) :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) (by positivity)
      _ = ε / 2 := by field_simp
  obtain ⟨φ, hφ⟩ := Metric.denseRange_iff.mp denseRange_cc2 ξ δ hδ
  obtain ⟨ψ, hψ⟩ := Metric.denseRange_iff.mp denseRange_cc2 η δ hδ
  refine ⟨schrodinger (toRCP (KernelAlg.rankOneKernel φ ψ)), ⟨_, rfl⟩, ?_⟩
  rw [schrodinger_toEnvelope, KernelAlg.op_rankOneKernel, dist_eq_norm, rankOne_sub_rankOne]
  rw [dist_eq_norm] at hφ hψ
  have hφn : ‖cc2 φ‖ ≤ ‖ξ‖ + δ := by
    have := norm_sub_norm_le (cc2 φ) ξ
    rw [norm_sub_rev] at this
    linarith
  calc ‖InnerProductSpace.rankOne ℂ (ξ - cc2 φ) η + InnerProductSpace.rankOne ℂ (cc2 φ) (η - cc2 ψ)‖
      ≤ ‖ξ - cc2 φ‖ * ‖η‖ + ‖cc2 φ‖ * ‖η - cc2 ψ‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [InnerProductSpace.norm_rankOne, InnerProductSpace.norm_rankOne]
    _ ≤ δ * ‖η‖ + (‖ξ‖ + δ) * δ := by
        gcongr
    _ ≤ δ * (‖ξ‖ + ‖η‖ + 1) := by nlinarith [norm_nonneg ξ, norm_nonneg η]
    _ < ε := by linarith

/-- **Every compact operator on `L²(ℝ)` is in the image.** -/
theorem compact_mem_range_schrodinger {T : L2Real →L[ℂ] L2Real} (hT : IsCompactOperator T) :
    T ∈ Set.range schrodinger := by
  have hsub : ∀ F : L2Real →L[ℂ] L2Real, (∃ n, _root_.RHTower.HasRankLE F n) → F ∈ Set.range schrodinger := by
    rintro F ⟨n, hF⟩
    obtain ⟨ι, _, b, c, rfl⟩ := exists_eq_sum_rankOne hF
    have hmem : ∀ i, InnerProductSpace.rankOne ℂ (b i) (c i) ∈
        (NonUnitalStarAlgHom.range schrodinger : Set (L2Real →L[ℂ] L2Real)) := fun i => by
      rw [NonUnitalStarAlgHom.coe_range]
      exact rankOne_mem_range_schrodinger (b i) (c i)
    have hsum := Submodule.sum_mem (NonUnitalStarAlgHom.range schrodinger).toNonUnitalSubalgebra.toSubmodule
      (t := Finset.univ) fun i _ => hmem i
    rw [← NonUnitalStarAlgHom.coe_range]
    exact hsum
  obtain ⟨F, hF, hlim⟩ := exists_finiteRank_tendsto hT
  exact isClosed_range_schrodinger.mem_of_tendsto hlim (Filter.Eventually.of_forall fun m =>
    hsub (F m) (hF m))

/-! ## (SAC.14) `C₀(ℝ) ⋊ ℝ ≅ 𝒦(L²(ℝ))` -/

/-- The Schrödinger representation with values in the compact operators. -/
def schrodingerCompact : RealCrossedProduct →⋆ₙₐ[ℂ] CompactOps L2Real where
  toFun y := CompactOps.mk (schrodinger y) (isCompactOperator_schrodinger y)
  map_smul' c y := CompactOps.op_injective (map_smul schrodinger c y)
  map_zero' := CompactOps.op_injective (map_zero schrodinger)
  map_add' y z := CompactOps.op_injective (map_add schrodinger y z)
  map_mul' y z := CompactOps.op_injective (map_mul schrodinger y z)
  map_star' y := CompactOps.op_injective (by
    change schrodinger (star y) = ContinuousLinearMap.adjoint (schrodinger y)
    rw [map_star]
    rfl)

theorem schrodingerCompact_bijective : Function.Bijective schrodingerCompact := by
  refine ⟨fun y z h => schrodinger_injective (congrArg CompactOps.op h), fun T => ?_⟩
  obtain ⟨y, hy⟩ := compact_mem_range_schrodinger (CompactOps.isCompactOperator_op T)
  exact ⟨y, CompactOps.op_injective hy⟩

/-- **(SAC.14) Stone–von Neumann: the full crossed product `C₀(ℝ) ⋊ ℝ` of the translation action
is isomorphic to the compact operators on `L²(ℝ)`**, by the Schrödinger representation. -/
def realCrossedProductEquivCompact : RealCrossedProduct ≃⋆ₐ[ℂ] CompactOps L2Real :=
  StarAlgEquiv.ofBijective schrodingerCompact schrodingerCompact_bijective

theorem realCrossedProductEquivCompact_toRCP (k : KernelAlg) :
    (realCrossedProductEquivCompact (toRCP k)).op = k.op := rfl

end GaloisForLFunctions.HTGeometry
