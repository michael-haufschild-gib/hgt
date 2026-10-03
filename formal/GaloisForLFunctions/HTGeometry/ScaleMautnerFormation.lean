import GaloisForLFunctions.HTGeometry.UnitaryFlowSmoothing
import GaloisForLFunctions.HTGeometry.FlowMultiplicityMeasure
import GaloisForLFunctions.HTGeometry.IsometricConjugationSchatten

/-!
# Scale–Mautner pure-point blindness and cross-fibre scale formation

A strongly continuous unitary group `V` and a unitary `U` obey the exact scale law
`U V_t U⁻¹ = V_{qt}`, `q > 1` (**(SM.1)**).

* **Theorem 2.1 (SM.2)–(SM.3).**  Every eigenvector of `U` is fixed by every `V_t`:
  `‖V_tξ - ξ‖ = ‖V_{t/qⁿ}ξ - ξ‖ → 0`.  Hence the closed span of the eigenvectors lies in every fixed
  space, and pure-point `U` forces `V ≡ 1`; on a finite-dimensional space `V ≡ 1` (Corollary 2.2).
* **Theorem 3.1 (SM.5).**  A self-adjoint generator with compact resolvent — a Hilbert basis of
  joint eigenvectors whose frequencies have finite sublevel sets — admits the scale law only for
  `A = 0` on a finite-dimensional space: `U` maps the frequency `λ` to `λ/q`, and the frequencies
  `λ/qⁿ` would accumulate.
* **Theorem 4.1 (SM.8).**  A bounded scale defect satisfies `‖WAW⁻¹ - qA‖ ≥ (q-1)‖A‖`.
* **Corollary 5.1.**  An isometric intertwining recovery cannot restore the erased sector.
* **Theorem 6.1 (SM.10)–(SM.14).**  Cross-fibre transports `T_s : H_s → H_{qs}` with
  `V^{qs}_t T_s = T_s V^s_{qt}` conserve the normalized clock `A_s/s`, scale point and approximate
  spectra by `q`, and for compact-resolvent clocks scale the counting function, the heat trace and
  the spectral zeta function.

Operator identities between self-adjoint generators are taken in their exponentiated form, which
carries the domains: `U A U⁻¹ = qA` is `U V_t U⁻¹ = V_{qt}`.
-/

open MeasureTheory Set Filter Topology ContinuousLinearMap
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **(SM.1)** The exact formation scale law `U V_t U⁻¹ = V_{qt}`. -/
def IsScaleLaw (U : H ≃ₗᵢ[ℂ] H) (V : UnitaryFlow ℂ H) (q : ℝ) : Prop :=
  ∀ t x, U (V.op t (U.symm x)) = V.op (q * t) x

/-! ## Theorem 2.1: scale–Mautner blindness -/

theorem scaleLaw_apply {U : H ≃ₗᵢ[ℂ] H} {V : UnitaryFlow ℂ H} {q : ℝ} (hq : 0 < q)
    (hS : IsScaleLaw U V q) (t : ℝ) (x : H) : V.op t x = U (V.op (t / q) (U.symm x)) := by
  rw [hS, mul_div_cancel₀ t hq.ne']

/-- One scale step does not change the displacement of an eigenvector. -/
theorem norm_op_sub_eq_div {U : H ≃ₗᵢ[ℂ] H} {V : UnitaryFlow ℂ H} {q : ℝ} (hq : 0 < q)
    (hS : IsScaleLaw U V q) {ξ : H} {μ : ℂ} (hnorm : ‖μ‖ = 1) (hξ : U ξ = μ • ξ) (t : ℝ) :
    ‖V.op t ξ - ξ‖ = ‖V.op (t / q) ξ - ξ‖ := by
  have hμ : μ ≠ 0 := fun h => by simp [h] at hnorm
  have hsymm : U.symm ξ = μ⁻¹ • ξ := by
    apply U.injective
    rw [U.apply_symm_apply, map_smul, hξ, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  have hξ' : ξ = μ⁻¹ • U ξ := by rw [hξ, smul_smul, inv_mul_cancel₀ hμ, one_smul]
  have h1 : V.op t ξ - ξ = μ⁻¹ • U (V.op (t / q) ξ - ξ) := by
    rw [scaleLaw_apply hq hS t ξ, hsymm, LinearIsometryEquiv.map_smul, LinearIsometryEquiv.map_smul,
      map_sub, smul_sub, ← hξ']
  rw [h1, norm_smul, norm_inv, hnorm, inv_one, one_mul, LinearIsometryEquiv.norm_map]

/-- **Theorem 2.1 (SM.2).**  Every eigenvector of `U` is fixed by every `V_t`. -/
theorem op_eq_of_eigenvector {U : H ≃ₗᵢ[ℂ] H} {V : UnitaryFlow ℂ H} {q : ℝ} (hq : 1 < q)
    (hS : IsScaleLaw U V q) {ξ : H} {μ : ℂ} (hξ : U ξ = μ • ξ) (t : ℝ) : V.op t ξ = ξ := by
  by_cases h0 : ξ = 0
  · rw [h0, map_zero]
  have hnorm := norm_eq_one_of_unitary_eigenvector U h0 hξ
  have hq0 : 0 < q := by linarith
  have hiter : ∀ n : ℕ, ‖V.op t ξ - ξ‖ = ‖V.op (t / q ^ n) ξ - ξ‖ := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [ih, norm_op_sub_eq_div hq0 hS hnorm hξ, pow_succ, div_div]
  have hlim : Tendsto (fun n : ℕ => ‖V.op (t / q ^ n) ξ - ξ‖) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => t / q ^ n) atTop (𝓝 0) := by
      simpa using (tendsto_pow_atTop_atTop_of_one_lt hq).const_div_atTop t
    have h2 := ((V.continuous_orbit ξ).tendsto 0).comp h1
    rw [op_zero] at h2
    have h3 := (h2.sub_const ξ).norm
    simpa using h3
  have hconst : ‖V.op t ξ - ξ‖ = 0 :=
    tendsto_nhds_unique (tendsto_const_nhds.congr fun n => hiter n) hlim
  exact sub_eq_zero.1 (norm_eq_zero.1 hconst)

/-- The closed span `H_pp(U)` of the eigenvectors of `U`. -/
def ppSubspace (U : H ≃ₗᵢ[ℂ] H) : Submodule ℂ H :=
  (Submodule.span ℂ {ξ | ∃ μ : ℂ, U ξ = μ • ξ}).topologicalClosure

/-- The fixed space of `V_t`. -/
def fixedSubspace (V : UnitaryFlow ℂ H) (t : ℝ) : Submodule ℂ H :=
  LinearMap.ker ((V.op t).toLinearEquiv.toLinearMap - LinearMap.id)

theorem mem_fixedSubspace {V : UnitaryFlow ℂ H} {t : ℝ} {x : H} : x ∈ fixedSubspace V t ↔ V.op t x = x := by
  simp only [fixedSubspace, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  rfl

theorem isClosed_fixedSubspace (V : UnitaryFlow ℂ H) (t : ℝ) : IsClosed (fixedSubspace V t : Set H) := by
  have h : (fixedSubspace V t : Set H) = {x | V.op t x = x} := Set.ext fun x => mem_fixedSubspace
  rw [h]
  exact isClosed_eq (V.op t).continuous continuous_id

/-- **Theorem 2.1 (SM.2)** `H_pp(U) ⊆ ker(V_t - 1)` for every `t`. -/
theorem ppSubspace_le_fixedSubspace {U : H ≃ₗᵢ[ℂ] H} {V : UnitaryFlow ℂ H} {q : ℝ} (hq : 1 < q)
    (hS : IsScaleLaw U V q) (t : ℝ) : ppSubspace U ≤ fixedSubspace V t := by
  refine Submodule.topologicalClosure_minimal _ (Submodule.span_le.2 fun ξ ⟨μ, hξ⟩ => ?_)
    (isClosed_fixedSubspace V t)
  exact mem_fixedSubspace.2 (op_eq_of_eigenvector hq hS hξ t)

/-- **Theorem 2.1 (SM.3)** If `U` has pure-point spectrum, then `V_t = 1` for every `t`. -/
theorem op_eq_id_of_pp {U : H ≃ₗᵢ[ℂ] H} {V : UnitaryFlow ℂ H} {q : ℝ} (hq : 1 < q)
    (hS : IsScaleLaw U V q) (hpp : ppSubspace U = ⊤) (t : ℝ) (x : H) : V.op t x = x :=
  mem_fixedSubspace.1 (ppSubspace_le_fixedSubspace hq hS t (hpp ▸ Submodule.mem_top))

/-- On a finite-dimensional complex space a unitary has pure-point spectrum: the orthogonal
complement of its eigenvectors is invariant and would contain an eigenvector. -/
theorem ppSubspace_eq_top_of_finiteDimensional [FiniteDimensional ℂ H] (U : H ≃ₗᵢ[ℂ] H) :
    ppSubspace U = ⊤ := by
  set S := Submodule.span ℂ {ξ | ∃ μ : ℂ, U ξ = μ • ξ} with hSdef
  have hSc : IsClosed (S : Set H) := Submodule.closed_of_finiteDimensional S
  rw [ppSubspace, ← hSdef, hSc.submodule_topologicalClosure_eq]
  have hsymm : ∀ u ∈ S, U.symm u ∈ S := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem ξ hξ =>
        obtain ⟨μ, hμ⟩ := hξ
        by_cases h0 : ξ = 0
        · rw [h0, map_zero]
          exact S.zero_mem
        have hμ0 : μ ≠ 0 := fun h => h0 (by
          have := hμ
          rw [h, zero_smul] at this
          exact U.injective (this.trans (map_zero U).symm))
        have h1 : U.symm ξ = μ⁻¹ • ξ := by
          apply U.injective
          rw [U.apply_symm_apply, map_smul, hμ, smul_smul, inv_mul_cancel₀ hμ0, one_smul]
        rw [h1]
        exact S.smul_mem _ (Submodule.subset_span ⟨μ, hμ⟩)
    | zero => rw [map_zero]; exact S.zero_mem
    | add x y _ _ hx hy => rw [map_add]; exact S.add_mem hx hy
    | smul c x _ hx => rw [map_smul]; exact S.smul_mem c hx
  have hinv : ∀ w ∈ Sᗮ, U w ∈ Sᗮ := by
    intro w hw
    rw [Submodule.mem_orthogonal]
    intro u hu
    have h := U.inner_map_map (U.symm u) w
    rw [U.apply_symm_apply] at h
    rw [h]
    exact (Submodule.mem_orthogonal _ _).1 hw _ (hsymm u hu)
  by_contra hne
  have hperp : Sᗮ ≠ ⊥ := fun h => hne (by rwa [Submodule.orthogonal_eq_bot_iff] at h)
  haveI : Nontrivial Sᗮ := Submodule.nontrivial_iff_ne_bot.2 hperp
  set f : Module.End ℂ Sᗮ := (U.toLinearEquiv.toLinearMap).restrict hinv
  obtain ⟨μ, hμ⟩ := Module.End.exists_eigenvalue f
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  have heig : U (w : H) = μ • (w : H) := by
    have := Module.End.mem_eigenspace_iff.mp hw.1
    exact congrArg Subtype.val this
  have hwS : (w : H) ∈ S := Submodule.subset_span ⟨μ, heig⟩
  have hw0 : (w : H) = 0 := by
    have := (Submodule.mem_orthogonal _ _).1 w.2 _ hwS
    exact inner_self_eq_zero.1 this
  exact hw.2 (Subtype.ext hw0)

/-- **Corollary 2.2.**  A nontrivial scale-covariant group forces a nonzero continuous sector of
`U`; no finite-dimensional same-fibre model is nontrivial. -/
theorem continuous_sector_of_nontrivial {U : H ≃ₗᵢ[ℂ] H} {V : UnitaryFlow ℂ H} {q : ℝ} (hq : 1 < q)
    (hS : IsScaleLaw U V q) :
    ((∃ t x, V.op t x ≠ x) → ppSubspace U ≠ ⊤) ∧
      (FiniteDimensional ℂ H → ∀ t x, V.op t x = x) :=
  ⟨fun ⟨t, x, hx⟩ hpp => hx (op_eq_id_of_pp hq hS hpp t x),
    fun _ t x => op_eq_id_of_pp hq hS (ppSubspace_eq_top_of_finiteDimensional U) t x⟩

/-! ## Theorem 3.1: compact-resolvent fracture -/

theorem flowCharacter_mul (a b t : ℝ) : flowCharacter a (b * t) = flowCharacter (a * b) t := by
  unfold flowCharacter
  push_cast
  ring_nf

theorem conj_flowCharacter_neg (a t : ℝ) : starRingEnd ℂ (flowCharacter a (-t)) = flowCharacter a t := by
  unfold flowCharacter
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal]

/-- Distinct frequencies give distinct characters. -/
theorem eq_of_flowCharacter_eq {a b : ℝ} (h : ∀ t, flowCharacter a t = flowCharacter b t) : a = b := by
  by_contra hab
  have hne : a - b ≠ 0 := sub_ne_zero.2 hab
  have h1 := h (Real.pi / (a - b))
  have h2 : flowCharacter (a - b) (Real.pi / (a - b)) = 1 := by
    have hb : flowCharacter b (Real.pi / (a - b)) ≠ 0 := Complex.exp_ne_zero _
    have : flowCharacter (a - b) (Real.pi / (a - b)) * flowCharacter b (Real.pi / (a - b)) =
        flowCharacter a (Real.pi / (a - b)) := by
      unfold flowCharacter
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [h1] at this
    exact (mul_eq_right₀ hb).1 this
  have h3 : flowCharacter (a - b) (Real.pi / (a - b)) = -1 := by
    unfold flowCharacter
    have hne' : (a : ℂ) - b ≠ 0 := by exact_mod_cast hne
    rw [show Complex.I * ((((a - b : ℝ)) : ℂ) * ((Real.pi / (a - b) : ℝ) : ℂ)) = Real.pi * Complex.I by
      push_cast
      field_simp]
    exact Complex.exp_pi_mul_I
  rw [h2] at h3
  norm_num at h3

/-- **A self-adjoint generator with compact resolvent, in spectral form.**  A Hilbert basis of joint
eigenvectors `V_t f_k = e^{itλ_k} f_k` whose real frequencies have finite sublevel sets. -/
structure CompactResolventClock (V : UnitaryFlow ℂ H) (κ : Type*) where
  basis : HilbertBasis κ ℂ H
  freq : κ → ℝ
  eigen : ∀ k t, V.op t (basis k) = flowCharacter (freq k) t • basis k
  finite_sublevel : ∀ M : ℝ, {k | |freq k| ≤ M}.Finite

namespace CompactResolventClock

variable {V : UnitaryFlow ℂ H} {κ : Type*} (C : CompactResolventClock V κ)

/-- A joint eigenvector of frequency `ν` has no component along basis vectors of other
frequencies. -/
theorem inner_eq_zero_of_jointEigen {y : H} {ν : ℝ} (hy : ∀ t, V.op t y = flowCharacter ν t • y)
    {j : κ} (hj : C.freq j ≠ ν) : ⟪C.basis j, y⟫_ℂ = 0 := by
  by_contra hc
  apply hj
  refine eq_of_flowCharacter_eq fun t => ?_
  have h1 : ⟪C.basis j, V.op t y⟫_ℂ = flowCharacter ν t * ⟪C.basis j, y⟫_ℂ := by
    rw [hy, inner_smul_right]
  have h2 : ⟪C.basis j, V.op t y⟫_ℂ = flowCharacter (C.freq j) t * ⟪C.basis j, y⟫_ℂ := by
    have := inner_op_left V (-t) (C.basis j) y
    rw [neg_neg] at this
    rw [← this, C.eigen, inner_smul_left, conj_flowCharacter_neg]
  exact mul_right_cancel₀ hc (h2.symm.trans h1)

/-- A nonzero joint eigenvector has its frequency among the clock frequencies. -/
theorem exists_freq_eq_of_jointEigen {y : H} (hy0 : y ≠ 0) {ν : ℝ}
    (hy : ∀ t, V.op t y = flowCharacter ν t • y) : ∃ j, C.freq j = ν := by
  by_contra hall
  push Not at hall
  apply hy0
  apply C.basis.repr.injective
  refine lp.ext (funext fun j => ?_)
  rw [HilbertBasis.repr_apply_apply, C.inner_eq_zero_of_jointEigen hy (hall j), map_zero]
  rfl

end CompactResolventClock

namespace CompactResolventClock

variable {V : UnitaryFlow ℂ H} {κ : Type*} (C : CompactResolventClock V κ)

/-- **The accumulation step of Theorem 3.1.**  If the frequency set is closed under division by
`q > 1`, every frequency vanishes: otherwise `λ/qⁿ` are infinitely many distinct frequencies in the
finite sublevel set `|·| ≤ |λ|`.  Then `V ≡ 1` and the basis, hence the space, is finite. -/
theorem trivial_of_freq_div {q : ℝ} (hq : 1 < q) (hstep : ∀ k, ∃ j, C.freq j = C.freq k / q) :
    (∀ k, C.freq k = 0) ∧ (∀ t x, V.op t x = x) ∧ Finite κ ∧ FiniteDimensional ℂ H := by
  classical
  have hq0 : 0 < q := by linarith
  have hiter : ∀ k (n : ℕ), ∃ j, C.freq j = C.freq k / q ^ n := by
    intro k n
    induction n with
    | zero => exact ⟨k, by simp⟩
    | succ n ih =>
        obtain ⟨j, hj⟩ := ih
        obtain ⟨j', hj'⟩ := hstep j
        exact ⟨j', by rw [hj', hj, pow_succ, div_div]⟩
  have hzero : ∀ k, C.freq k = 0 := by
    intro k
    by_contra hk
    choose j hj using hiter k
    have hinj : Function.Injective j := fun n m hnm => by
      have h := (hj n).symm.trans ((congrArg C.freq hnm).trans (hj m))
      rw [div_eq_div_iff (by positivity) (by positivity)] at h
      have h' : q ^ m = q ^ n := mul_left_cancel₀ hk h
      exact (pow_right_injective₀ hq0 hq.ne').eq_iff.1 h' |>.symm
    have hsub : Set.range j ⊆ {k' | |C.freq k'| ≤ |C.freq k|} := by
      rintro _ ⟨n, rfl⟩
      simp only [Set.mem_setOf_eq, hj, abs_div]
      exact div_le_self (abs_nonneg _) (by rw [abs_of_pos (by positivity)]; exact one_le_pow₀ hq.le)
    exact Set.infinite_range_of_injective hinj ((C.finite_sublevel _).subset hsub)
  have hid : ∀ t x, V.op t x = x := by
    intro t x
    have hsum := C.basis.hasSum_repr x
    have h1 := hsum.mapL ((V.op t).toContinuousLinearEquiv.toContinuousLinearMap)
    have h2 : (fun k => (V.op t).toContinuousLinearEquiv.toContinuousLinearMap (C.basis.repr x k • C.basis k)) =
        fun k => C.basis.repr x k • C.basis k := funext fun k => by
      simp only [ContinuousLinearEquiv.coe_coe, LinearIsometryEquiv.coe_toContinuousLinearEquiv,
        LinearIsometryEquiv.map_smul, C.eigen, hzero k]
      simp [flowCharacter]
    rw [h2] at h1
    exact h1.unique hsum
  have hfin : Finite κ := by
    have := C.finite_sublevel 0
    simp only [hzero, abs_zero, le_refl, Set.setOf_true] at this
    exact Set.finite_univ_iff.1 this
  refine ⟨hzero, hid, hfin, ?_⟩
  haveI := Fintype.ofFinite κ
  exact Module.Finite.of_basis C.basis.toOrthonormalBasis.toBasis

end CompactResolventClock

/-- **Theorem 3.1 (SM.5) Compact-resolvent fracture.**  If the generator of `V` has compact resolvent
and `U V_t U⁻¹ = V_{qt}`, then every frequency vanishes, `V ≡ 1` (`A = 0`) and the space is
finite-dimensional. -/
theorem compactResolvent_scaleLaw {U : H ≃ₗᵢ[ℂ] H} {V : UnitaryFlow ℂ H} {q : ℝ} (hq : 1 < q)
    (hS : IsScaleLaw U V q) {κ : Type*} (C : CompactResolventClock V κ) :
    (∀ k, C.freq k = 0) ∧ (∀ t x, V.op t x = x) ∧ Finite κ ∧ FiniteDimensional ℂ H := by
  have hq0 : 0 < q := by linarith
  -- `U` lowers frequencies by the factor `q`
  refine C.trivial_of_freq_div hq fun k => ?_
  have hy0 : U (C.basis k) ≠ 0 := fun h => by
    have := C.basis.orthonormal.1 k
    rw [← LinearIsometryEquiv.norm_map U, h, norm_zero] at this
    exact zero_ne_one this
  refine C.exists_freq_eq_of_jointEigen hy0 fun t => ?_
  have h := hS (t / q) (U (C.basis k))
  rw [U.symm_apply_apply, mul_div_cancel₀ t hq0.ne', C.eigen, LinearIsometryEquiv.map_smul] at h
  rw [← h]
  congr 1
  unfold flowCharacter
  congr 1
  push_cast
  ring

/-- **Theorem 3.1, converse.**  The trivial clock on a finite-dimensional space satisfies every scale
law and has compact resolvent. -/
theorem trivialClock_scaleLaw [FiniteDimensional ℂ H] (U : H ≃ₗᵢ[ℂ] H) (V : UnitaryFlow ℂ H)
    (hV : ∀ t x, V.op t x = x) (q : ℝ) :
    IsScaleLaw U V q ∧ Nonempty (CompactResolventClock V (Fin (Module.finrank ℂ H))) := by
  refine ⟨fun t x => by rw [hV, hV, U.apply_symm_apply], ⟨?_⟩⟩
  exact { basis := (stdOrthonormalBasis ℂ H).toHilbertBasis
          freq := fun _ => 0
          eigen := fun k t => by rw [hV]; simp [flowCharacter]
          finite_sublevel := fun M => Set.toFinite _ }

/-! ## Theorem 4.1: the bounded scale anomaly -/

/-- **Theorem 4.1 (SM.8)** `‖W A W⁻¹ - qA‖ ≥ (q-1)‖A‖` for a unitary `W`. -/
theorem norm_scaleDefect_ge [CompleteSpace H] (W : H ≃ₗᵢ[ℂ] H) (A : H →L[ℂ] H) {q : ℝ} (hq : 1 ≤ q) :
    (q - 1) * ‖A‖ ≤ ‖(W : H →L[ℂ] H) ∘L A ∘L (W.symm : H →L[ℂ] H) - (q : ℂ) • A‖ := by
  have hW : adjoint (W : H →L[ℂ] H) ∘L (W : H →L[ℂ] H) = ContinuousLinearMap.id ℂ H := by
    ext x
    simp [LinearIsometryEquiv.adjoint_eq_symm]
  have hconj : ‖(W : H →L[ℂ] H) ∘L A ∘L (W.symm : H →L[ℂ] H)‖ = ‖A‖ := by
    have := norm_cornerConj hW A
    rwa [cornerConj, LinearIsometryEquiv.adjoint_eq_symm] at this
  have h := norm_sub_norm_le ((q : ℂ) • A) ((W : H →L[ℂ] H) ∘L A ∘L (W.symm : H →L[ℂ] H))
  rw [norm_smul, Complex.norm_real, Real.norm_of_nonneg (by linarith), hconj, norm_sub_rev] at h
  linarith

/-- **Theorem 4.1, cofinal form.**  Diverging apertures force diverging anomalies. -/
theorem tendsto_norm_scaleDefect [CompleteSpace H] (W : ℕ → H ≃ₗᵢ[ℂ] H) (A : ℕ → H →L[ℂ] H) {q : ℝ}
    (hq : 1 < q) (hA : Tendsto (fun N => ‖A N‖) atTop atTop) :
    Tendsto (fun N => ‖(W N : H →L[ℂ] H) ∘L A N ∘L ((W N).symm : H →L[ℂ] H) - (q : ℂ) • A N‖) atTop atTop :=
  tendsto_atTop_mono (fun N => norm_scaleDefect_ge (W N) (A N) hq.le)
    (hA.const_mul_atTop (by linarith))

/-! ## Corollary 5.1: common recovery cannot restore the erased sector -/

/-- **Corollary 5.1.**  If an isometric embedding intertwines `(U, V)` with a scale system `(U₁, V₁)`,
every `U`-eigenvector is fixed by `V_t`, and its recovered image by `V₁_t`. -/
theorem recovery_fixed_of_eigenvector {K : Type*} [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    {U : H ≃ₗᵢ[ℂ] H} {V : UnitaryFlow ℂ H} {U₁ : K ≃ₗᵢ[ℂ] K} {V₁ : UnitaryFlow ℂ K} (E : H →ₗᵢ[ℂ] K)
    (hU : ∀ x, U₁ (E x) = E (U x)) (hV : ∀ t x, V₁.op t (E x) = E (V.op t x)) {q : ℝ} (hq : 1 < q)
    (hS : IsScaleLaw U₁ V₁ q) {ξ : H} {μ : ℂ} (hξ : U ξ = μ • ξ) (t : ℝ) :
    V.op t ξ = ξ ∧ V₁.op t (E ξ) = E ξ := by
  have hE : U₁ (E ξ) = μ • E ξ := by rw [hU, hξ, LinearIsometry.map_smul]
  have h := op_eq_of_eigenvector hq hS hE t
  exact ⟨E.injective (by rw [← hV, h]), h⟩

end GaloisForLFunctions.HTGeometry
