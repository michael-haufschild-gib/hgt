import GaloisForLFunctions.HTGeometry.ScaleMautnerGenerator
import GaloisForLFunctions.HTGeometry.GramianInverseForm

/-!
# Cross-fibre scale formation

Each scale `s` carries a Hilbert fibre `H_s`, a unitary clock `V^s_t = e^{itA_s}` and a unitary
transport `T_s : H_s → H_{qs}` with `V^{qs}_t T_s = T_s V^s_{qt}`, i.e. **(SM.10)**
`A_{qs} T_s = q T_s A_s` with transported domains.

* **(SM.11)** The normalized clock `B_s = A_s / s` is conserved: `B_{qs} T_s = T_s B_s`; it is
  the generator of the normalized flow `t ↦ V^s_{t/s}`, which `T_s` conjugates exactly.
* **(SM.12)** `σ(A_{qs}) = q σ(A_s)`.
* **(SM.13)** The counting function `N(Λ) = dim E(Λ)` of the spectral subspace below `Λ` satisfies
  `N_{qs}(Λ) = N_s(Λ/q)`; for a nonnegative compact-resolvent clock it counts eigenvalues with
  multiplicity.
* **(SM.14)** For compact-resolvent clocks the functional calculus depends only on the flow, so
  `e^{-tA_{qs}} = T_s e^{-qtA_s} T_s⁻¹` and `A_{qs}^{-z} = q^{-z} T_s A_s^{-z} T_s⁻¹`; hence
  `Tr e^{-tA_{qs}} = Tr e^{-qtA_s}` and `ζ_{A_{qs}}(z) = q^{-z} ζ_{A_s}(z)` on trace class, and both
  traces are the eigenvalue sums `∑ e^{-tλ_k}` and `∑ λ_k^{-z}`.
* **Corollary 6.2.**  Closing the lifted history by a clock-respecting identification of `H_{qⁿs}`
  with `H_s` gives a same-fibre unitary `L` with `L A_s L⁻¹ = qⁿ A_s`; a compact-resolvent clock then
  forces `A_s = 0` and `dim H_s < ∞`.
-/

open Filter Topology ContinuousLinearMap
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-! ## Time rescaling -/

/-- The time-rescaled flow `t ↦ V_{ct}`. -/
def UnitaryFlow.timeRescale (V : UnitaryFlow ℂ H) (c : ℝ) : UnitaryFlow ℂ H where
  op t := V.op (c * t)
  op_add s t x := by rw [mul_add, V.op_add]
  continuous_orbit x := (V.continuous_orbit x).comp (continuous_const.mul continuous_id)

/-- The generator of `t ↦ V_{ct}` is `cA`. -/
theorem scaleIntertwining_timeRescale (V : UnitaryFlow ℂ H) {c : ℝ} (hc : c ≠ 0) :
    ScaleIntertwining (LinearIsometryEquiv.refl ℂ H) (flowGenerator V)
      (flowGenerator (V.timeRescale c)) c :=
  scaleIntertwining_flowGenerator _ hc fun _ _ => rfl

/-- The inverse of a transport `W_t T = T V_{ct}`: `V_t T⁻¹ = T⁻¹ W_{t/c}`. -/
theorem transport_symm {V : UnitaryFlow ℂ H} {W : UnitaryFlow ℂ K} (T : H ≃ₗᵢ[ℂ] K) {c : ℝ}
    (hc : c ≠ 0) (hT : ∀ t x, W.op t (T x) = T (V.op (c * t) x)) (t : ℝ) (y : K) :
    V.op t (T.symm y) = T.symm (W.op (c⁻¹ * t) y) := by
  conv_rhs => rw [← T.apply_symm_apply y]
  rw [hT, mul_inv_cancel_left₀ hc, LinearIsometryEquiv.symm_apply_apply]

/-! ## Eigenspaces and the counting function -/

/-- The eigenspace of frequency `ν`: the vectors with `V_t x = e^{iνt} x`. -/
def flowEigenspace (V : UnitaryFlow ℂ H) (ν : ℝ) : Submodule ℂ H where
  carrier := {x | ∀ t, V.op t x = flowCharacter ν t • x}
  add_mem' {x y} hx hy t := by rw [map_add, hx t, hy t, smul_add]
  zero_mem' t := by rw [map_zero, smul_zero]
  smul_mem' c x hx t := by rw [LinearIsometryEquiv.map_smul, hx t, smul_comm]

theorem mem_flowEigenspace {V : UnitaryFlow ℂ H} {ν : ℝ} {x : H} :
    x ∈ flowEigenspace V ν ↔ ∀ t, V.op t x = flowCharacter ν t • x := Iff.rfl

/-- The eigenspace of frequency `ν` is the eigenspace `ker(A - ν)` of the generator. -/
theorem mem_flowEigenspace_iff_generator {V : UnitaryFlow ℂ H} {ν : ℝ} {x : H} :
    x ∈ flowEigenspace V ν ↔
      ∃ hx : x ∈ (flowGenerator V).domain, flowGenerator V ⟨x, hx⟩ = (ν : ℂ) • x := by
  constructor
  · intro hx
    apply flowGenerator_of_hasDerivAt
    have h0 : HasDerivAt (fun t : ℝ => Complex.I * ((ν : ℂ) * (t : ℂ)))
        (Complex.I * ((ν : ℂ) * ((1 : ℝ) : ℂ))) 0 :=
      ((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul _).const_mul _
    have hc : HasDerivAt (fun t : ℝ => flowCharacter ν t) (Complex.I * ν) 0 := by
      have := h0.cexp
      simpa [flowCharacter] using this
    rw [show (fun t => V.op t x) = fun t => flowCharacter ν t • x from funext hx, smul_smul]
    exact hc.smul_const x
  · rintro ⟨hx, hAx⟩
    -- `f(t) = e^{-iνt} V_t x` has derivative `0` everywhere
    set f : ℝ → H := fun t => flowCharacter (-ν) t • V.op t x
    have hderiv : ∀ t, HasDerivAt f 0 t := by
      intro t
      have hV : HasDerivAt (fun s => V.op s x) (V.op t (Complex.I • (ν : ℂ) • x)) t := by
        have h := (hasDerivAt_flowGenerator V ⟨x, hx⟩)
        rw [hAx] at h
        have h1 : HasDerivAt (fun s => V.op t (V.op (s - t) x)) (V.op t (Complex.I • (ν : ℂ) • x)) t :=
          (((V.op t).toContinuousLinearEquiv : H →L[ℂ] H).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
            t (HasDerivAt.scomp_of_eq t h ((hasDerivAt_id t).sub_const t |>.congr_deriv rfl)
              (sub_self t).symm |>.congr_deriv (one_smul ℝ _))
        refine h1.congr_of_eventuallyEq (Eventually.of_forall fun s => ?_)
        simp only
        rw [← V.op_add, add_sub_cancel]
      have hχ : HasDerivAt (fun s : ℝ => flowCharacter (-ν) s)
          (flowCharacter (-ν) t * (Complex.I * (-ν : ℝ))) t := by
        have h0 : HasDerivAt (fun s : ℝ => Complex.I * (((-ν : ℝ) : ℂ) * (s : ℂ)))
            (Complex.I * (((-ν : ℝ) : ℂ) * ((1 : ℝ) : ℂ))) t :=
          ((hasDerivAt_id t).ofReal_comp.const_mul _).const_mul _
        have := h0.cexp
        simpa [flowCharacter] using this
      have h := hχ.smul hV
      have hval : flowCharacter (-ν) t • (V.op t) (Complex.I • (ν : ℂ) • x) +
          (flowCharacter (-ν) t * (Complex.I * ((-ν : ℝ) : ℂ))) • (V.op t) x = 0 := by
        rw [LinearIsometryEquiv.map_smul, LinearIsometryEquiv.map_smul, smul_smul, smul_smul,
          ← add_smul]
        convert zero_smul ℂ (V.op t x) using 2
        push_cast
        ring
      exact h.congr_deriv hval
    have hconst : ∀ t, f t = f 0 := fun t =>
      is_const_of_deriv_eq_zero (fun s => (hderiv s).differentiableAt) (fun s => (hderiv s).deriv) t 0
    intro t
    have h := hconst t
    simp only [f, op_zero] at h
    have h0 : flowCharacter (-ν) 0 = 1 := by simp [flowCharacter]
    rw [h0, one_smul] at h
    have hinv : flowCharacter ν t * flowCharacter (-ν) t = 1 := by
      unfold flowCharacter
      rw [← Complex.exp_add]
      push_cast
      ring_nf
      exact Complex.exp_zero
    calc V.op t x = (flowCharacter ν t * flowCharacter (-ν) t) • V.op t x := by rw [hinv, one_smul]
      _ = flowCharacter ν t • x := by rw [← smul_smul, h]

/-- The spectral subspace `E(Λ)` spanned by the eigenvectors of frequency at most `Λ`. -/
def flowLowSubspace (V : UnitaryFlow ℂ H) (Λ : ℝ) : Submodule ℂ H :=
  ⨆ (ν : ℝ) (_ : ν ≤ Λ), flowEigenspace V ν

/-- The eigenvalue counting function `N(Λ) = dim E(Λ)`. -/
def flowCounting (V : UnitaryFlow ℂ H) (Λ : ℝ) : ℕ :=
  Module.finrank ℂ (flowLowSubspace V Λ)

section Transport

variable {V : UnitaryFlow ℂ H} {W : UnitaryFlow ℂ K} (T : H ≃ₗᵢ[ℂ] K) {c : ℝ}

/-- A transport `W_t T = T V_{ct}` maps the `ν`-eigenspace onto the `cν`-eigenspace. -/
theorem map_flowEigenspace (hc : c ≠ 0) (hT : ∀ t x, W.op t (T x) = T (V.op (c * t) x)) (ν : ℝ) :
    (flowEigenspace V ν).map (T.toLinearEquiv : H →ₗ[ℂ] K) = flowEigenspace W (c * ν) := by
  ext y
  simp only [Submodule.mem_map, mem_flowEigenspace]
  constructor
  · rintro ⟨x, hx, rfl⟩ t
    change W.op t (T x) = flowCharacter (c * ν) t • T x
    rw [hT, hx (c * t), LinearIsometryEquiv.map_smul, flowCharacter_mul, mul_comm ν c]
  · intro hy
    refine ⟨T.symm y, fun t => ?_, T.apply_symm_apply y⟩
    rw [transport_symm T hc hT, hy, LinearIsometryEquiv.map_smul, flowCharacter_mul, mul_comm c ν,
      mul_assoc, mul_inv_cancel₀ hc, mul_one]

/-- A transport `W_t T = T V_{ct}`, `c > 0`, maps `E_V(Λ/c)` onto `E_W(Λ)`. -/
theorem map_flowLowSubspace (hc : 0 < c) (hT : ∀ t x, W.op t (T x) = T (V.op (c * t) x)) (Λ : ℝ) :
    (flowLowSubspace V (Λ / c)).map (T.toLinearEquiv : H →ₗ[ℂ] K) = flowLowSubspace W Λ := by
  simp only [flowLowSubspace, Submodule.map_iSup, map_flowEigenspace T hc.ne' hT]
  apply le_antisymm
  · refine iSup₂_le fun ν hν => le_iSup₂_of_le (c * ν) ?_ le_rfl
    rwa [le_div_iff₀' hc] at hν
  · refine iSup₂_le fun ν hν => le_iSup₂_of_le (ν / c) (div_le_div_of_nonneg_right hν hc.le) ?_
    rw [mul_div_cancel₀ ν hc.ne']

/-- **(SM.13)** `N_W(Λ) = N_V(Λ/c)`. -/
theorem flowCounting_transport (hc : 0 < c) (hT : ∀ t x, W.op t (T x) = T (V.op (c * t) x))
    (Λ : ℝ) : flowCounting W Λ = flowCounting V (Λ / c) := by
  rw [flowCounting, flowCounting, ← map_flowLowSubspace T hc hT Λ, LinearEquiv.finrank_map_eq]

end Transport

/-! ## Compact-resolvent clocks: counting, transport and functional calculus -/

namespace CompactResolventClock

variable {V : UnitaryFlow ℂ H} {κ : Type*} (C : CompactResolventClock V κ)

/-- For a clock with finitely many frequencies `≤ Λ`, `E(Λ)` is spanned by those basis vectors:
an eigenvector of frequency `ν ≤ Λ` has only finitely many nonzero coordinates. -/
theorem flowLowSubspace_eq {Λ : ℝ} (hfin : {k | C.freq k ≤ Λ}.Finite) :
    flowLowSubspace V Λ = Submodule.span ℂ (C.basis '' {k | C.freq k ≤ Λ}) := by
  classical
  apply le_antisymm
  · refine iSup₂_le fun ν hν y hy => ?_
    have hzero : ∀ k ∉ hfin.toFinset, C.basis.repr y k • C.basis k = 0 := by
      intro k hk
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_le] at hk
      rw [HilbertBasis.repr_apply_apply,
        C.inner_eq_zero_of_jointEigen (mem_flowEigenspace.1 hy) (lt_of_le_of_lt hν hk).ne', zero_smul]
    rw [← (hasSum_sum_of_ne_finset_zero hzero).unique (C.basis.hasSum_repr y)]
    exact Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _
      (Submodule.subset_span ⟨k, hfin.mem_toFinset.1 hk, rfl⟩)
  · rw [Submodule.span_le]
    rintro _ ⟨k, hk, rfl⟩
    exact (le_iSup₂_of_le (C.freq k) hk le_rfl : flowEigenspace V (C.freq k) ≤ _) (C.eigen k)

/-- The counting function of a clock counts its frequencies `≤ Λ` with multiplicity. -/
theorem flowCounting_eq_card {Λ : ℝ} (hfin : {k | C.freq k ≤ Λ}.Finite) :
    flowCounting V Λ = hfin.toFinset.card := by
  classical
  rw [flowCounting, C.flowLowSubspace_eq hfin]
  have hli : LinearIndependent ℂ (fun k : hfin.toFinset => C.basis k) :=
    C.basis.orthonormal.linearIndependent.comp _ Subtype.val_injective
  have h := finrank_span_eq_card hli
  rw [Fintype.card_coe] at h
  have hset : C.basis '' {k | C.freq k ≤ Λ} = Set.range (fun k : hfin.toFinset => C.basis k) := by
    ext x
    simp
  rw [hset, h]

/-- A nonnegative clock has finitely many frequencies below every level. -/
theorem finite_le_of_nonneg (hpos : ∀ k, 0 ≤ C.freq k) (Λ : ℝ) : {k | C.freq k ≤ Λ}.Finite :=
  (C.finite_sublevel Λ).subset fun k hk => by
    simp only [Set.mem_setOf_eq] at hk ⊢
    rwa [abs_of_nonneg (hpos k)]

/-- A positive clock has a uniform spectral gap at `0`. -/
theorem exists_freq_lower_bound (hpos : ∀ k, 0 < C.freq k) : ∃ c, 0 < c ∧ ∀ k, c ≤ C.freq k := by
  classical
  have hfin := C.finite_sublevel 1
  by_cases hS : hfin.toFinset.Nonempty
  · obtain ⟨k0, hk0, hmin⟩ := hfin.toFinset.exists_min_image C.freq hS
    refine ⟨min 1 (C.freq k0), lt_min one_pos (hpos k0), fun k => ?_⟩
    by_cases hk : |C.freq k| ≤ 1
    · exact (min_le_right _ _).trans (hmin k (by simpa using hk))
    · push Not at hk
      rw [abs_of_pos (hpos k)] at hk
      exact (min_le_left _ _).trans hk.le
  · refine ⟨1, one_pos, fun k => ?_⟩
    by_contra hk
    push Not at hk
    exact hS ⟨k, by simp [abs_of_pos (hpos k), hk.le]⟩

/-- A transport `W_t T = T V_{ct}`, `c ≠ 0`, carries a clock of `V` to a clock of `W` with basis
`T f_k` and frequencies `cλ_k`. -/
def transport {W : UnitaryFlow ℂ K} (T : H ≃ₗᵢ[ℂ] K) {c : ℝ} (hc : c ≠ 0)
    (hT : ∀ t x, W.op t (T x) = T (V.op (c * t) x)) : CompactResolventClock W κ where
  basis := HilbertBasis.ofRepr (T.symm.trans C.basis.repr)
  freq k := c * C.freq k
  eigen k t := by
    classical
    have hb : HilbertBasis.ofRepr (T.symm.trans C.basis.repr) k = T (C.basis k) := by
      rw [← HilbertBasis.repr_symm_single, ← HilbertBasis.repr_symm_single]
      rfl
    rw [hb, hT, C.eigen, LinearIsometryEquiv.map_smul, flowCharacter_mul, mul_comm (C.freq k) c]
  finite_sublevel M := by
    refine (C.finite_sublevel (M / |c|)).subset fun k hk => ?_
    simp only [Set.mem_setOf_eq, abs_mul] at hk ⊢
    rwa [le_div_iff₀' (abs_pos.2 hc)]

theorem transport_basis {W : UnitaryFlow ℂ K} (T : H ≃ₗᵢ[ℂ] K) {c : ℝ} (hc : c ≠ 0)
    (hT : ∀ t x, W.op t (T x) = T (V.op (c * t) x)) (k : κ) :
    (C.transport T hc hT).basis k = T (C.basis k) := by
  classical
  change HilbertBasis.ofRepr (T.symm.trans C.basis.repr) k = T (C.basis k)
  rw [← HilbertBasis.repr_symm_single, ← HilbertBasis.repr_symm_single]
  rfl

theorem transport_freq {W : UnitaryFlow ℂ K} (T : H ≃ₗᵢ[ℂ] K) {c : ℝ} (hc : c ≠ 0)
    (hT : ∀ t x, W.op t (T x) = T (V.op (c * t) x)) (k : κ) :
    (C.transport T hc hT).freq k = c * C.freq k := rfl

/-- The **functional calculus** `g(A)` of a clock, for `g` bounded on the frequencies:
`g(A) f_k = g(λ_k) f_k`. -/
def calculus (g : ℝ → ℂ) {M : ℝ} (hM : 0 ≤ M) (hg : ∀ k, ‖g (C.freq k)‖ ≤ M) : H →L[ℂ] H :=
  basisDiag C.basis (fun k => g (C.freq k)) hM hg

theorem calculus_basis (g : ℝ → ℂ) {M : ℝ} (hM : 0 ≤ M) (hg : ∀ k, ‖g (C.freq k)‖ ≤ M) (k : κ) :
    C.calculus g hM hg (C.basis k) = g (C.freq k) • C.basis k := by
  classical
  exact basisDiag_basis _ _ hM hg k

/-- `g(A)` acts on an eigenvector of frequency `ν` by the scalar `g(ν)`. -/
theorem calculus_apply_of_mem (g : ℝ → ℂ) {M : ℝ} (hM : 0 ≤ M) (hg : ∀ k, ‖g (C.freq k)‖ ≤ M)
    {ν : ℝ} {y : H} (hy : y ∈ flowEigenspace V ν) : C.calculus g hM hg y = g ν • y := by
  refine C.basis.repr.injective (lp.ext (funext fun k => ?_))
  rw [calculus, repr_basisDiag, map_smul, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul]
  by_cases hk : C.freq k = ν
  · rw [hk]
  · rw [HilbertBasis.repr_apply_apply, C.inner_eq_zero_of_jointEigen (mem_flowEigenspace.1 hy) hk,
      mul_zero, mul_zero]

/-- **The functional calculus depends only on the flow**, not on the clock diagonalizing it. -/
theorem calculus_eq {ι : Type*} (C' : CompactResolventClock V ι) (g : ℝ → ℂ) {M M' : ℝ}
    (hM : 0 ≤ M) (hg : ∀ k, ‖g (C.freq k)‖ ≤ M) (hM' : 0 ≤ M') (hg' : ∀ k, ‖g (C'.freq k)‖ ≤ M') :
    C.calculus g hM hg = C'.calculus g hM' hg' := by
  refine ext_hilbertBasis (b := C.basis) fun k => ?_
  rw [C.calculus_basis, C'.calculus_apply_of_mem g hM' hg' (C.eigen k)]

theorem calculus_congr {g g' : ℝ → ℂ} (h : ∀ k, g (C.freq k) = g' (C.freq k)) {M M' : ℝ}
    (hM : 0 ≤ M) (hg : ∀ k, ‖g (C.freq k)‖ ≤ M) (hM' : 0 ≤ M') (hg' : ∀ k, ‖g' (C.freq k)‖ ≤ M') :
    C.calculus g hM hg = C.calculus g' hM' hg' := by
  refine ext_hilbertBasis (b := C.basis) fun k => ?_
  rw [C.calculus_basis, C.calculus_basis, h]

theorem calculus_const_mul (a : ℂ) (g : ℝ → ℂ) {M M' : ℝ} (hM : 0 ≤ M)
    (hg : ∀ k, ‖g (C.freq k)‖ ≤ M) (hM' : 0 ≤ M') (hg' : ∀ k, ‖a * g (C.freq k)‖ ≤ M') :
    C.calculus (fun x => a * g x) hM' hg' = a • C.calculus g hM hg := by
  refine ext_hilbertBasis (b := C.basis) fun k => ?_
  rw [C.calculus_basis, smul_apply, C.calculus_basis, smul_smul]

/-- **Transport of the functional calculus**: `g(A_W) = T (g(c·))(A_V) T⁻¹`. -/
theorem calculus_transport {W : UnitaryFlow ℂ K} (T : H ≃ₗᵢ[ℂ] K) {c : ℝ} (hc : c ≠ 0)
    (hT : ∀ t x, W.op t (T x) = T (V.op (c * t) x)) (g : ℝ → ℂ) {M : ℝ} (hM : 0 ≤ M)
    (hg : ∀ k, ‖g ((C.transport T hc hT).freq k)‖ ≤ M) (hg' : ∀ k, ‖g (c * C.freq k)‖ ≤ M) :
    (C.transport T hc hT).calculus g hM hg =
      ((T : H ≃L[ℂ] K) : H →L[ℂ] K) ∘L C.calculus (fun x => g (c * x)) hM hg' ∘L
        ((T.symm : K ≃L[ℂ] H) : K →L[ℂ] H) := by
  refine ext_hilbertBasis (b := (C.transport T hc hT).basis) fun k => ?_
  rw [calculus_basis, transport_basis, transport_freq, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply]
  simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.symm_apply_apply]
  rw [calculus_basis, LinearIsometryEquiv.map_smul]

theorem norm_heatSymbol_le (hpos : ∀ k, 0 ≤ C.freq k) {t : ℝ} (ht : 0 ≤ t) (k : κ) :
    ‖((Real.exp (-(t * C.freq k)) : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
  exact neg_nonpos.2 (mul_nonneg ht (hpos k))

/-- The heat semigroup `e^{-tA}` of a nonnegative clock, `t ≥ 0`. -/
def heat (hpos : ∀ k, 0 ≤ C.freq k) {t : ℝ} (ht : 0 ≤ t) : H →L[ℂ] H :=
  C.calculus (fun x => ((Real.exp (-(t * x)) : ℝ) : ℂ)) zero_le_one (C.norm_heatSymbol_le hpos ht)

theorem norm_negPowerSymbol_le (hpos : ∀ k, 0 < C.freq k) {c : ℝ} (hc : 0 < c)
    (hck : ∀ k, c ≤ C.freq k) {z : ℂ} (hz : 0 ≤ z.re) (k : κ) :
    ‖((C.freq k : ℂ)) ^ (-z)‖ ≤ c ^ (-z.re) := by
  rw [Complex.norm_cpow_eq_rpow_re_of_pos (hpos k), Complex.neg_re]
  exact Real.rpow_le_rpow_of_nonpos hc (hck k) (neg_nonpos.2 hz)

/-- The complex power `A^{-z}` of a positive clock, `Re z ≥ 0`. -/
def negPower (hpos : ∀ k, 0 < C.freq k) {z : ℂ} (hz : 0 ≤ z.re) : H →L[ℂ] H :=
  C.calculus (fun x => (x : ℂ) ^ (-z))
    (Real.rpow_nonneg (C.exists_freq_lower_bound hpos).choose_spec.1.le _)
    (C.norm_negPowerSymbol_le hpos (C.exists_freq_lower_bound hpos).choose_spec.1
      (C.exists_freq_lower_bound hpos).choose_spec.2 hz)

/-- The heat semigroup depends only on the flow. -/
theorem heat_eq {ι : Type*} (C' : CompactResolventClock V ι) (hpos : ∀ k, 0 ≤ C.freq k)
    (hpos' : ∀ k, 0 ≤ C'.freq k) {t : ℝ} (ht : 0 ≤ t) : C.heat hpos ht = C'.heat hpos' ht :=
  C.calculus_eq C' _ _ _ _ _

/-- The complex powers depend only on the flow. -/
theorem negPower_eq {ι : Type*} (C' : CompactResolventClock V ι) (hpos : ∀ k, 0 < C.freq k)
    (hpos' : ∀ k, 0 < C'.freq k) {z : ℂ} (hz : 0 ≤ z.re) : C.negPower hpos hz = C'.negPower hpos' hz :=
  C.calculus_eq C' _ _ _ _ _

/-- **(SM.14), heat semigroup.**  For a transport `W_t T = T V_{qt}`, `q > 0`, and nonnegative
compact-resolvent clocks of both flows, `e^{-tA_W} = T e^{-qtA_V} T⁻¹`. -/
theorem heat_transport {W : UnitaryFlow ℂ K} (T : H ≃ₗᵢ[ℂ] K) {q : ℝ} (hq : 0 < q)
    (hT : ∀ t x, W.op t (T x) = T (V.op (q * t) x)) (hpos : ∀ k, 0 ≤ C.freq k) {ι : Type*}
    (C' : CompactResolventClock W ι) (hpos' : ∀ k, 0 ≤ C'.freq k) {t : ℝ} (ht : 0 ≤ t) :
    C'.heat hpos' ht = ((T : H ≃L[ℂ] K) : H →L[ℂ] K) ∘L C.heat hpos (mul_nonneg hq.le ht) ∘L
      ((T.symm : K ≃L[ℂ] H) : K →L[ℂ] H) := by
  refine ext_hilbertBasis (b := (C.transport T hq.ne' hT).basis) fun k => ?_
  rw [heat, C'.calculus_apply_of_mem _ _ _ ((C.transport T hq.ne' hT).eigen k), transport_basis,
    comp_apply, comp_apply]
  simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.symm_apply_apply]
  rw [heat, calculus_basis, LinearIsometryEquiv.map_smul, transport_freq]
  congr 3
  ring

/-- **(SM.14), complex powers.**  For a transport `W_t T = T V_{qt}`, `q > 0`, and positive
compact-resolvent clocks of both flows, `A_W^{-z} = q^{-z} T A_V^{-z} T⁻¹`. -/
theorem negPower_transport {W : UnitaryFlow ℂ K} (T : H ≃ₗᵢ[ℂ] K) {q : ℝ} (hq : 0 < q)
    (hT : ∀ t x, W.op t (T x) = T (V.op (q * t) x)) (hpos : ∀ k, 0 < C.freq k) {ι : Type*}
    (C' : CompactResolventClock W ι) (hpos' : ∀ k, 0 < C'.freq k) {z : ℂ} (hz : 0 ≤ z.re) :
    C'.negPower hpos' hz = ((q : ℂ) ^ (-z)) • (((T : H ≃L[ℂ] K) : H →L[ℂ] K) ∘L C.negPower hpos hz ∘L
      ((T.symm : K ≃L[ℂ] H) : K →L[ℂ] H)) := by
  refine ext_hilbertBasis (b := (C.transport T hq.ne' hT).basis) fun k => ?_
  rw [negPower, C'.calculus_apply_of_mem _ _ _ ((C.transport T hq.ne' hT).eigen k), transport_basis,
    smul_apply, comp_apply, comp_apply]
  simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    LinearIsometryEquiv.symm_apply_apply]
  rw [negPower, calculus_basis, LinearIsometryEquiv.map_smul, transport_freq, smul_smul]
  congr 1
  push_cast
  exact Complex.mul_cpow_ofReal_nonneg hq.le (hpos k).le _

section Trace

variable [CompleteSpace H]

/-- On trace class, the trace of `g(A)` is the eigenvalue sum `∑ g(λ_k)`. -/
theorem opTrace_calculus (g : ℝ → ℂ) {M : ℝ} (hM : 0 ≤ M) (hg : ∀ k, ‖g (C.freq k)‖ ≤ M)
    (htr : MemSchattenClass 1 (C.calculus g hM hg)) :
    opTrace (C.calculus g hM hg) = ∑' k, g (C.freq k) := by
  obtain ⟨S, U, hS, hU, heq⟩ := htr.one_isTraceClass
  rw [heq, opTrace_comp_eq_tsum_basis hS hU C.basis, ← heq]
  refine tsum_congr fun k => ?_
  rw [C.calculus_basis, inner_smul_right, inner_self_eq_norm_sq_to_K, C.basis.orthonormal.1 k]
  simp

/-- The heat trace `Tr e^{-tA}`. -/
def heatTrace (hpos : ∀ k, 0 ≤ C.freq k) {t : ℝ} (ht : 0 ≤ t) : ℂ := opTrace (C.heat hpos ht)

/-- The spectral zeta function `ζ_A(z) = Tr A^{-z}`. -/
def spectralZeta (hpos : ∀ k, 0 < C.freq k) {z : ℂ} (hz : 0 ≤ z.re) : ℂ :=
  opTrace (C.negPower hpos hz)

/-- On trace class the heat trace is `∑ e^{-tλ_k}`. -/
theorem heatTrace_eq_tsum (hpos : ∀ k, 0 ≤ C.freq k) {t : ℝ} (ht : 0 ≤ t)
    (htr : MemSchattenClass 1 (C.heat hpos ht)) :
    C.heatTrace hpos ht = ∑' k, ((Real.exp (-(t * C.freq k)) : ℝ) : ℂ) :=
  C.opTrace_calculus _ _ _ htr

/-- On trace class the spectral zeta function is `∑ λ_k^{-z}`. -/
theorem spectralZeta_eq_tsum (hpos : ∀ k, 0 < C.freq k) {z : ℂ} (hz : 0 ≤ z.re)
    (htr : MemSchattenClass 1 (C.negPower hpos hz)) :
    C.spectralZeta hpos hz = ∑' k, ((C.freq k : ℂ)) ^ (-z) :=
  C.opTrace_calculus _ _ _ htr

end Trace

section TraceTransport

variable [CompleteSpace H] [CompleteSpace K]

omit [CompleteSpace K] in
theorem memSchattenClass_smul_iff_of_ne {p : ℝ} {c : ℂ} (hc : c ≠ 0) (X : H →L[ℂ] H) :
    MemSchattenClass p (c • X) ↔ MemSchattenClass p X := by
  unfold MemSchattenClass
  have h : ∀ n, approxNumber (c • X) n ^ p = ‖c‖ ^ p * approxNumber X n ^ p := fun n => by
    rw [approxNumber_smul, Real.mul_rpow (norm_nonneg c) (approxNumber_nonneg X n)]
  simp_rw [h]
  exact summable_mul_left_iff (Real.rpow_pos_of_pos (norm_pos_iff.2 hc) p).ne'

theorem unitary_comp_comp_eq_cornerConj (T : H ≃ₗᵢ[ℂ] K) (X : H →L[ℂ] H) :
    ((T : H ≃L[ℂ] K) : H →L[ℂ] K) ∘L X ∘L ((T.symm : K ≃L[ℂ] H) : K →L[ℂ] H) =
      cornerConj ((T : H ≃L[ℂ] K) : H →L[ℂ] K) X := by
  rw [cornerConj, LinearIsometryEquiv.adjoint_eq_symm]

theorem adjoint_comp_self_unitary (T : H ≃ₗᵢ[ℂ] K) :
    adjoint ((T : H ≃L[ℂ] K) : H →L[ℂ] K) ∘L ((T : H ≃L[ℂ] K) : H →L[ℂ] K) =
      ContinuousLinearMap.id ℂ H := by
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  ext x
  simp

/-- **(SM.14), heat trace.**  `e^{-tA_W}` is trace class exactly when `e^{-qtA_V}` is, and then
`Tr e^{-tA_W} = Tr e^{-qtA_V}`. -/
theorem heatTrace_transport {W : UnitaryFlow ℂ K} (T : H ≃ₗᵢ[ℂ] K) {q : ℝ} (hq : 0 < q)
    (hT : ∀ t x, W.op t (T x) = T (V.op (q * t) x)) (hpos : ∀ k, 0 ≤ C.freq k) {ι : Type*}
    (C' : CompactResolventClock W ι) (hpos' : ∀ k, 0 ≤ C'.freq k) {t : ℝ} (ht : 0 ≤ t) :
    (MemSchattenClass 1 (C'.heat hpos' ht) ↔ MemSchattenClass 1 (C.heat hpos (mul_nonneg hq.le ht))) ∧
      (MemSchattenClass 1 (C.heat hpos (mul_nonneg hq.le ht)) →
        C'.heatTrace hpos' ht = C.heatTrace hpos (mul_nonneg hq.le ht)) := by
  rw [heatTrace, heatTrace, C.heat_transport T hq hT hpos C' hpos' ht, unitary_comp_comp_eq_cornerConj]
  exact ⟨memSchattenClass_cornerConj_iff (adjoint_comp_self_unitary T) _,
    opTrace_cornerConj (adjoint_comp_self_unitary T)⟩

/-- **(SM.14), spectral zeta function.**  `A_W^{-z}` is trace class exactly when `A_V^{-z}` is, and
then `ζ_{A_W}(z) = q^{-z} ζ_{A_V}(z)`. -/
theorem spectralZeta_transport {W : UnitaryFlow ℂ K} (T : H ≃ₗᵢ[ℂ] K) {q : ℝ} (hq : 0 < q)
    (hT : ∀ t x, W.op t (T x) = T (V.op (q * t) x)) (hpos : ∀ k, 0 < C.freq k) {ι : Type*}
    (C' : CompactResolventClock W ι) (hpos' : ∀ k, 0 < C'.freq k) {z : ℂ} (hz : 0 ≤ z.re) :
    (MemSchattenClass 1 (C'.negPower hpos' hz) ↔ MemSchattenClass 1 (C.negPower hpos hz)) ∧
      (MemSchattenClass 1 (C.negPower hpos hz) →
        C'.spectralZeta hpos' hz = (q : ℂ) ^ (-z) * C.spectralZeta hpos hz) := by
  have hq0 : (q : ℂ) ^ (-z) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    exact fun h => (Complex.ofReal_ne_zero.2 hq.ne') h.1
  rw [spectralZeta, spectralZeta, C.negPower_transport T hq hT hpos C' hpos' hz,
    unitary_comp_comp_eq_cornerConj]
  refine ⟨?_, fun htr => ?_⟩
  · rw [memSchattenClass_smul_iff_of_ne hq0, memSchattenClass_cornerConj_iff (adjoint_comp_self_unitary T)]
  · have h1 : opTrace ((q : ℂ) ^ (-z) • cornerConj ((T : H ≃L[ℂ] K) : H →L[ℂ] K) (C.negPower hpos hz)) =
        (q : ℂ) ^ (-z) * opTrace (cornerConj ((T : H ≃L[ℂ] K) : H →L[ℂ] K) (C.negPower hpos hz)) := by
      simp only [opTrace, smul_apply, inner_smul_right, tsum_mul_left]
    rw [h1, opTrace_cornerConj (adjoint_comp_self_unitary T) htr]

end TraceTransport

end CompactResolventClock

/-! ## The cross-fibre scale system -/

/-- **A cross-fibre scale system (SM.10).**  Fibres `F s`, unitary clocks `V^s`, and unitary
transports `T_s : F s → F (qs)` with `V^{qs}_t T_s = T_s V^s_{qt}`. -/
structure CrossFibreScaleSystem (q : ℝ) (F : ℝ → Type*) [∀ s, NormedAddCommGroup (F s)]
    [∀ s, InnerProductSpace ℂ (F s)] where
  /-- The clock of each fibre. -/
  clock : ∀ s, UnitaryFlow ℂ (F s)
  /-- The transport to the next scale. -/
  transport : ∀ s, F s ≃ₗᵢ[ℂ] F (q * s)
  /-- The cross-fibre formation law. -/
  transport_clock : ∀ s t x,
    (clock (q * s)).op t (transport s x) = transport s ((clock s).op (q * t) x)

namespace CrossFibreScaleSystem

variable {q : ℝ} {F : ℝ → Type*} [∀ s, NormedAddCommGroup (F s)] [∀ s, InnerProductSpace ℂ (F s)]
  (S : CrossFibreScaleSystem q F)

/-- The clock generator `A_s`. -/
def clockGenerator (s : ℝ) : F s →ₗ.[ℂ] F s := flowGenerator (S.clock s)

/-- **(SM.10)** `A_{qs} T_s = q T_s A_s` with transported domains. -/
theorem generator_intertwining (hq : q ≠ 0) (s : ℝ) :
    ScaleIntertwining (S.transport s) (S.clockGenerator s) (S.clockGenerator (q * s)) q :=
  scaleIntertwining_flowGenerator _ hq (S.transport_clock s)

/-- **(SM.10)** as an identity of partially defined operators: `T_s⁻¹ A_{qs} T_s = q A_s`. -/
theorem unitaryConjugate_clockGenerator (hq : q ≠ 0) (s : ℝ) :
    unitaryConjugateLinearPMap (S.transport s) (S.clockGenerator (q * s)) =
      (q : ℂ) • S.clockGenerator s :=
  (S.generator_intertwining hq s).unitaryConjugate_eq

/-- The normalized clock `B_s = A_s / s`. -/
def normalizedGenerator (s : ℝ) : F s →ₗ.[ℂ] F s := ((s : ℂ)⁻¹) • S.clockGenerator s

/-- **(SM.11)** The normalized clock is conserved: `B_{qs} T_s = T_s B_s`. -/
theorem normalized_intertwining (hq : q ≠ 0) {s : ℝ} (hs : s ≠ 0) :
    ScaleIntertwining (S.transport s) (S.normalizedGenerator s) (S.normalizedGenerator (q * s)) 1 := by
  have h := (S.generator_intertwining hq s).smul (inv_ne_zero (by exact_mod_cast hs : (s : ℂ) ≠ 0))
    (((q * s : ℝ) : ℂ)⁻¹)
  have h1 : ((q * s : ℝ) : ℂ)⁻¹ * (q : ℂ) / (s : ℂ)⁻¹ = 1 := by
    have hq' : (q : ℂ) ≠ 0 := by exact_mod_cast hq
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
    push_cast
    field_simp
  rw [h1] at h
  exact h

/-- **(SM.11)** as an identity of partially defined operators: `T_s⁻¹ B_{qs} T_s = B_s`. -/
theorem unitaryConjugate_normalizedGenerator (hq : q ≠ 0) {s : ℝ} (hs : s ≠ 0) :
    unitaryConjugateLinearPMap (S.transport s) (S.normalizedGenerator (q * s)) =
      S.normalizedGenerator s := by
  rw [(S.normalized_intertwining hq hs).unitaryConjugate_eq, one_smul]

/-- The normalized flow `t ↦ V^s_{t/s}`. -/
def normalizedClock (s : ℝ) : UnitaryFlow ℂ (F s) := (S.clock s).timeRescale s⁻¹

/-- The transports conjugate the normalized flows exactly. -/
theorem normalizedClock_transport (hq : q ≠ 0) (s t : ℝ) (x : F s) :
    (S.normalizedClock (q * s)).op t (S.transport s x) =
      S.transport s ((S.normalizedClock s).op t x) := by
  change (S.clock (q * s)).op ((q * s)⁻¹ * t) (S.transport s x) =
    S.transport s ((S.clock s).op (s⁻¹ * t) x)
  rw [S.transport_clock, mul_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hq, one_mul]

/-- `B_s` is the generator of the normalized flow. -/
theorem normalizedGenerator_generates {s : ℝ} (hs : s ≠ 0) :
    ScaleIntertwining (LinearIsometryEquiv.refl ℂ (F s)) (S.normalizedGenerator s)
      (flowGenerator (S.normalizedClock s)) 1 := by
  have h := (scaleIntertwining_timeRescale (S.clock s) (inv_ne_zero hs)).smul
    (inv_ne_zero (by exact_mod_cast hs : (s : ℂ) ≠ 0)) 1
  have h1 : (1 : ℂ) * ((s⁻¹ : ℝ) : ℂ) / (s : ℂ)⁻¹ = 1 := by
    have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs
    push_cast
    field_simp
  rw [h1, one_smul] at h
  exact h

/-- **(SM.12)** `σ(A_{qs}) = q σ(A_s)`. -/
theorem spectrum_scaling (hq : q ≠ 0) (s : ℝ) :
    pmapSpectrum (S.clockGenerator (q * s)) =
      (fun z => (q : ℂ) * z) '' pmapSpectrum (S.clockGenerator s) :=
  (S.generator_intertwining hq s).pmapSpectrum_eq (by exact_mod_cast hq)

/-- **(SM.13)** `N_{qs}(Λ) = N_s(Λ/q)`. -/
theorem counting_scaling (hq : 0 < q) (s Λ : ℝ) :
    flowCounting (S.clock (q * s)) Λ = flowCounting (S.clock s) (Λ / q) :=
  flowCounting_transport (S.transport s) hq (S.transport_clock s) Λ

/-- **(SM.13)** for nonnegative compact-resolvent clocks: the eigenvalues of `A_{qs}` below `Λ`,
counted with multiplicity, are as many as those of `A_s` below `Λ/q`. -/
theorem counting_scaling_card (hq : 0 < q) (s Λ : ℝ) {κ ι : Type*}
    (C : CompactResolventClock (S.clock s) κ) (hpos : ∀ k, 0 ≤ C.freq k)
    (C' : CompactResolventClock (S.clock (q * s)) ι) (hpos' : ∀ k, 0 ≤ C'.freq k) :
    (C'.finite_le_of_nonneg hpos' Λ).toFinset.card =
      (C.finite_le_of_nonneg hpos (Λ / q)).toFinset.card := by
  rw [← C'.flowCounting_eq_card, ← C.flowCounting_eq_card, S.counting_scaling hq]

variable [∀ s, CompleteSpace (F s)]

/-- **(SM.14)** `Tr e^{-tA_{qs}} = Tr e^{-qtA_s}`, with trace class transported in both
directions. -/
theorem heatTrace_scaling (hq : 0 < q) (s : ℝ) {κ ι : Type*}
    (C : CompactResolventClock (S.clock s) κ) (hpos : ∀ k, 0 ≤ C.freq k)
    (C' : CompactResolventClock (S.clock (q * s)) ι) (hpos' : ∀ k, 0 ≤ C'.freq k) {t : ℝ}
    (ht : 0 ≤ t) :
    (MemSchattenClass 1 (C'.heat hpos' ht) ↔ MemSchattenClass 1 (C.heat hpos (mul_nonneg hq.le ht))) ∧
      (MemSchattenClass 1 (C.heat hpos (mul_nonneg hq.le ht)) →
        C'.heatTrace hpos' ht = C.heatTrace hpos (mul_nonneg hq.le ht)) :=
  C.heatTrace_transport (S.transport s) hq (S.transport_clock s) hpos C' hpos' ht

/-- **(SM.14)** `ζ_{A_{qs}}(z) = q^{-z} ζ_{A_s}(z)`, with trace class transported in both
directions. -/
theorem spectralZeta_scaling (hq : 0 < q) (s : ℝ) {κ ι : Type*}
    (C : CompactResolventClock (S.clock s) κ) (hpos : ∀ k, 0 < C.freq k)
    (C' : CompactResolventClock (S.clock (q * s)) ι) (hpos' : ∀ k, 0 < C'.freq k) {z : ℂ}
    (hz : 0 ≤ z.re) :
    (MemSchattenClass 1 (C'.negPower hpos' hz) ↔ MemSchattenClass 1 (C.negPower hpos hz)) ∧
      (MemSchattenClass 1 (C.negPower hpos hz) →
        C'.spectralZeta hpos' hz = (q : ℂ) ^ (-z) * C.spectralZeta hpos hz) :=
  C.spectralZeta_transport (S.transport s) hq (S.transport_clock s) hpos C' hpos' hz

omit [∀ s, CompleteSpace (F s)]

/-- The `n`-step lifted transport `H_s → H_{qⁿs}` intertwines `V^{qⁿs}_t` with `V^s_{qⁿt}`. -/
theorem exists_iterate_transport (s : ℝ) (n : ℕ) :
    ∃ T : F s ≃ₗᵢ[ℂ] F (q ^ n * s),
      ∀ t x, (S.clock (q ^ n * s)).op t (T x) = T ((S.clock s).op (q ^ n * t) x) := by
  induction n with
  | zero =>
      have key : ∀ r, s = r → ∃ T : F s ≃ₗᵢ[ℂ] F r,
          ∀ t x, (S.clock r).op t (T x) = T ((S.clock s).op t x) := by
        rintro r rfl
        exact ⟨LinearIsometryEquiv.refl ℂ (F s), fun t x => rfl⟩
      obtain ⟨T, hT⟩ := key (q ^ 0 * s) (by rw [pow_zero, one_mul])
      exact ⟨T, fun t x => by rw [hT]; exact congrArg T (by rw [pow_zero, one_mul])⟩
  | succ n ih =>
      obtain ⟨T, hT⟩ := ih
      have key : ∀ r, q * (q ^ n * s) = r → ∃ T' : F s ≃ₗᵢ[ℂ] F r,
          ∀ t x, (S.clock r).op t (T' x) = T' ((S.clock s).op (q ^ (n + 1) * t) x) := by
        rintro r rfl
        refine ⟨T.trans (S.transport (q ^ n * s)), fun t x => ?_⟩
        rw [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply, S.transport_clock, hT]
        exact congrArg _ (congrArg T (by rw [← mul_assoc, ← pow_succ]))
      exact key _ (by ring)

/-- **Corollary 6.2 — recurrent scale projection has open lifted clock history.**  Identifying the
observer points `s` and `qⁿs` (`n ≥ 1`) by a unitary `J : H_{qⁿs} → H_s` respecting the clocks
closes the lifted history into a same-fibre unitary `L` with `L⁻¹ A_s L = qⁿ A_s`.  If `A_s` has
compact resolvent, then `A_s = 0` on all of `H_s`, its clock is trivial, and `dim H_s < ∞`. -/
theorem lifted_history_open (hq : 1 < q) (s : ℝ) {n : ℕ} (hn : n ≠ 0)
    (J : F (q ^ n * s) ≃ₗᵢ[ℂ] F s)
    (hJ : ∀ t x, (S.clock s).op t (J x) = J ((S.clock (q ^ n * s)).op t x)) {κ : Type*}
    (C : CompactResolventClock (S.clock s) κ) :
    (∀ k, C.freq k = 0) ∧ (∀ t x, (S.clock s).op t x = x) ∧ Finite κ ∧
      FiniteDimensional ℂ (F s) ∧ (S.clockGenerator s).domain = ⊤ ∧
        ∀ x : (S.clockGenerator s).domain, S.clockGenerator s x = 0 := by
  obtain ⟨T, hT⟩ := S.exists_iterate_transport s n
  have hL : ∀ t x, (S.clock s).op t ((T.trans J) x) = (T.trans J) ((S.clock s).op (q ^ n * t) x) := by
    intro t x
    rw [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.trans_apply, hJ, hT]
  have hqn : 1 < q ^ n := one_lt_pow₀ hq hn
  have hI := scaleIntertwining_flowGenerator (T.trans J) (by positivity : q ^ n ≠ 0) hL
  rw [← LinearIsometryEquiv.symm_symm (T.trans J)] at hI
  exact compactResolvent_generator_scaleLaw hqn hI C

end CrossFibreScaleSystem

end GaloisForLFunctions.HTGeometry
