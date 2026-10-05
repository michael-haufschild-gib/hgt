import GaloisForLFunctions.HTGeometry.UnitarySpectrumClosedRange
import GaloisForLFunctions.HTGeometry.LpReindexCompactDichotomy
import GaloisForLFunctions.HTGeometry.CompactObserverTraceBlindness

/-!
# Positivity is necessary in the trace-norm formation law

On `ℓ²(ℤ × Bool)` let `U` shift the integer coordinate of both sheets.  `U` has no eigenvectors:
an eigenvector has constant modulus along each sheet, which square-summability forbids.  The
self-adjoint trace-class packet `T = |δ_{0,0}⟩⟨δ_{0,0}| - |δ_{0,1}⟩⟨δ_{0,1}|` has zero continuous
mass, `tr(T P_c) = tr T = 0`, and zero atomic pinching, yet its Cesàro formation is
`M_N(T) = N⁻¹ ∑_{n<N} (|δ_{-n,0}⟩⟨δ_{-n,0}| - |δ_{-n,1}⟩⟨δ_{-n,1}|)`; compressing to the first sheet
leaves a normalized orthogonal average of trace norm one.  So `‖M_N(T) - Π_at(T)‖₁ ≥ 1` for every
`N ≥ 1`: without positivity, zero continuous mass does not control the cross-sheet cancellation and
the trace-norm formation law fails.
-/

open Filter Topology Set
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.ContinuousLinearMap LpDiagonal

/-- The sheet shift `(n, b) ↦ (n + 1, b)` of `ℤ × Bool`. -/
def sheetShift : ℤ × Bool ≃ ℤ × Bool := (Equiv.addRight (1 : ℤ)).prodCongr (Equiv.refl Bool)

/-- The shift unitary of `ℓ²(ℤ × Bool)`. -/
def sheetShiftUnitary : LpTwo (ℤ × Bool) ≃ₗᵢ[ℂ] LpTwo (ℤ × Bool) := lpReindex sheetShift

/-- The coordinate vector at `(n, b)`. -/
def sheetVec (n : ℤ) (b : Bool) : LpTwo (ℤ × Bool) := lp.single 2 (n, b) (1 : ℂ)

theorem sheetShiftUnitary_apply_coe (x : LpTwo (ℤ × Bool)) (n : ℤ) (b : Bool) :
    ((sheetShiftUnitary x : LpTwo (ℤ × Bool)) : ℤ × Bool → ℂ) (n, b) =
      (x : ℤ × Bool → ℂ) (n - 1, b) := by
  rw [sheetShiftUnitary, lpReindex_coe]
  rfl

theorem sheetShiftUnitary_symm_sheetVec (n : ℤ) (b : Bool) :
    sheetShiftUnitary.symm (sheetVec n b) = sheetVec (n - 1) b := by
  refine lp.ext (funext fun i => ?_)
  rcases i with ⟨m, c⟩
  show (sheetVec n b : ℤ × Bool → ℂ) (m + 1, c) = (sheetVec (n - 1) b : ℤ × Bool → ℂ) (m, c)
  simp only [sheetVec, lp.single_apply, Pi.single_apply, Prod.mk.injEq]
  congr 1
  apply propext
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by omega, h2⟩

theorem sheetShiftUnitary_symm_iterate (b : Bool) (n : ℕ) :
    sheetShiftUnitary.symm^[n] (sheetVec 0 b) = sheetVec (-(n : ℤ)) b := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, sheetShiftUnitary_symm_sheetVec]
      congr 1
      push_cast
      ring

theorem orthonormal_lpSingle : Orthonormal ℂ fun p : ℤ × Bool => lp.single 2 p (1 : ℂ) := by
  classical
  rw [orthonormal_iff_ite]
  intro i j
  rw [lp.inner_single_left, lp.single_apply, Pi.single_apply]
  by_cases h : j = i
  · subst h
    simp
  · simp [Ne.symm h]

/-- Each sheet orbit `n ↦ δ_{-n,b}` is orthonormal. -/
theorem orthonormal_sheetOrbit (b : Bool) :
    Orthonormal ℂ fun n : ℕ => sheetVec (-(n : ℤ)) b :=
  orthonormal_lpSingle.comp (fun n : ℕ => (-(n : ℤ), b)) fun m n h => by
    simp only [Prod.mk.injEq, neg_inj, Nat.cast_inj] at h
    exact h.1

/-- **The sheet shift has no eigenvectors.** -/
theorem hasNoEigenvectors_sheetShiftUnitary : HasNoEigenvectors sheetShiftUnitary := by
  intro x c hx
  have hcoord : ∀ (n : ℤ) (b : Bool),
      (x : ℤ × Bool → ℂ) (n - 1, b) = c * (x : ℤ × Bool → ℂ) (n, b) := by
    intro n b
    have h := congrArg (fun y : LpTwo (ℤ × Bool) => (y : ℤ × Bool → ℂ) (n, b)) hx
    simpa only [sheetShiftUnitary_apply_coe, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul] using h
  by_contra hx0
  have hc : ‖c‖ = 1 := by
    have h := sheetShiftUnitary.norm_map x
    rw [hx, norm_smul] at h
    exact (mul_eq_right₀ (norm_ne_zero_iff.mpr hx0)).mp h
  have hstep : ∀ (n : ℤ) (b : Bool),
      ‖(x : ℤ × Bool → ℂ) (n - 1, b)‖ = ‖(x : ℤ × Bool → ℂ) (n, b)‖ := by
    intro n b
    rw [hcoord, norm_mul, hc, one_mul]
  have hconst : ∀ (b : Bool) (n : ℤ),
      ‖(x : ℤ × Bool → ℂ) (n, b)‖ = ‖(x : ℤ × Bool → ℂ) (0, b)‖ := by
    intro b n
    refine Int.induction_on n rfl (fun k ih => ?_) (fun k ih => ?_)
    · have h := hstep ((k : ℤ) + 1) b
      rw [add_sub_cancel_right] at h
      rw [← h, ih]
    · rw [hstep, ih]
  have hsum : Summable fun i : ℤ × Bool => ‖(x : ℤ × Bool → ℂ) i‖ ^ 2 := by
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
      (memℓp_gen_iff (by norm_num : 0 < (2 : ℝ≥0∞).toReal)).mp (lp.memℓp x)
  have hzero : ∀ b : Bool, (x : ℤ × Bool → ℂ) (0, b) = 0 := by
    intro b
    have hs := hsum.comp_injective (i := fun n : ℤ => (n, b))
      fun m n h => (Prod.mk.inj h).1
    have hc0 : Summable fun _ : ℤ => ‖(x : ℤ × Bool → ℂ) (0, b)‖ ^ 2 :=
      hs.congr fun n => by simp only [Function.comp_apply, hconst b n]
    rw [summable_const_iff] at hc0
    exact norm_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp hc0)
  refine hx0 (lp.ext (funext fun i => ?_))
  rcases i with ⟨n, b⟩
  have h := hconst b n
  rw [hzero b, norm_zero] at h
  exact norm_eq_zero.mp h

/-- The two-sheet packet `|δ_{0,0}⟩⟨δ_{0,0}| - |δ_{0,1}⟩⟨δ_{0,1}|`. -/
def sheetPacket : LpTwo (ℤ × Bool) →L[ℂ] LpTwo (ℤ × Bool) :=
  InnerProductSpace.rankOne ℂ (sheetVec 0 false) (sheetVec 0 false) -
    InnerProductSpace.rankOne ℂ (sheetVec 0 true) (sheetVec 0 true)

theorem memSchattenClass_one_sheetPacket : RHTower.MemSchattenClass 1 sheetPacket :=
  memSchattenClass_one_sub' (memSchattenClass_one_rankOne _ _) (memSchattenClass_one_rankOne _ _)

theorem continuousSubspace_sheetShiftUnitary : continuousSubspace sheetShiftUnitary = ⊤ := by
  have hE : ∀ c, unitaryEigenspace sheetShiftUnitary c = ⊥ := fun c =>
    (Submodule.eq_bot_iff _).mpr fun x hx =>
      hasNoEigenvectors_sheetShiftUnitary x c (mem_unitaryEigenspace.mp hx)
  have hat : atomicSubspace sheetShiftUnitary = ⊥ := by
    rw [atomicSubspace]
    simp_rw [hE, iSup_bot]
    exact IsClosed.submodule_topologicalClosure_eq (Submodule.closed_of_finiteDimensional _)
  rw [continuousSubspace, hat, Submodule.bot_orthogonal_eq_top]

/-- **Zero continuous mass**: `tr(T P_c) = tr T = 0`. -/
theorem continuousMass_sheetPacket : continuousMass sheetShiftUnitary sheetPacket = 0 := by
  have hP : contproj sheetShiftUnitary = ContinuousLinearMap.id ℂ _ := by
    ext x : 1
    exact Submodule.starProjection_eq_self_iff.mpr
      (by rw [continuousSubspace_sheetShiftUnitary]; trivial)
  rw [continuousMass, hP, ContinuousLinearMap.comp_id, sheetPacket,
    RHTower.opTrace_sub_of_memSchattenClass_one (memSchattenClass_one_rankOne _ _)
      (memSchattenClass_one_rankOne _ _), opTrace_rankOne, opTrace_rankOne, sheetVec, sheetVec,
    lp.inner_single_left, lp.inner_single_left, lp.single_apply_self, lp.single_apply_self,
    sub_self]

/-- **Zero atomic pinching.** -/
theorem atomicPinch_sheetPacket :
    atomicPinch sheetShiftUnitary memSchattenClass_one_sheetPacket.one_isHilbertSchmidt = 0 :=
  atomicPinch_eq_zero_of_hasNoEigenvectors hasNoEigenvectors_sheetShiftUnitary _

theorem hsCesaro_sub {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (U : H ≃ₗᵢ[ℂ] H) (N : ℕ) (A B : H →L[ℂ] H) :
    hsCesaro U N (A - B) = hsCesaro U N A - hsCesaro U N B := by
  rw [eq_sub_iff_add_eq, ← hsCesaro_add, sub_add_cancel]

/-- The formation of the packet: two orthogonal sheet averages with opposite signs. -/
theorem hsCesaro_sheetPacket (N : ℕ) :
    hsCesaro sheetShiftUnitary N sheetPacket =
      orthoAverage (fun n => sheetVec (-(n : ℤ)) false) N -
        orthoAverage (fun n => sheetVec (-(n : ℤ)) true) N := by
  rw [sheetPacket, hsCesaro_sub, hsCesaro_rankOne_eq_orthoAverage,
    hsCesaro_rankOne_eq_orthoAverage]
  simp_rw [sheetShiftUnitary_symm_iterate]

/-- The compression to the first sheet. -/
def sheetProj : LpTwo (ℤ × Bool) →L[ℂ] LpTwo (ℤ × Bool) :=
  lpDiag (fun i => if i.2 = false then 1 else 0) 1 zero_le_one fun i => by
    split_ifs <;> simp

theorem sheetProj_sheetVec (n : ℤ) (b : Bool) :
    sheetProj (sheetVec n b) = if b = false then sheetVec n b else 0 := by
  rw [sheetProj, sheetVec, lpDiag_single]
  split_ifs <;> simp

theorem comp_orthoAverage (E : LpTwo (ℤ × Bool) →L[ℂ] LpTwo (ℤ × Bool))
    (e : ℕ → LpTwo (ℤ × Bool)) (N : ℕ) :
    E ∘L orthoAverage e N =
      (N : ℂ)⁻¹ • ∑ k ∈ Finset.range N, InnerProductSpace.rankOne ℂ (E (e k)) (e k) := by
  ext x : 1
  simp only [orthoAverage, ContinuousLinearMap.comp_apply, smul_apply, sum_apply,
    InnerProductSpace.rankOne_apply, map_smul, map_sum]

theorem sheetProj_comp_hsCesaro (N : ℕ) :
    sheetProj ∘L hsCesaro sheetShiftUnitary N sheetPacket =
      orthoAverage (fun n => sheetVec (-(n : ℤ)) false) N := by
  rw [hsCesaro_sheetPacket, ContinuousLinearMap.comp_sub, comp_orthoAverage, comp_orthoAverage]
  simp only [sheetProj_sheetVec, if_true, Bool.true_eq_false, if_false, map_zero, zero_apply]
  rw [orthoAverage]
  ext x : 1
  simp

/-- **Positivity is necessary in the trace-norm formation law.**  The self-adjoint trace-class
packet `T` on the two-sheet shift has zero continuous mass and zero atomic pinching, yet
`‖M_N(T) - Π_at(T)‖₁ ≥ 1` for every `N ≥ 1`. -/
theorem sheetPacket_formation_traceNorm {N : ℕ} (hN : 0 < N) :
    1 ≤ RHTower.traceNorm (LpTwo (ℤ × Bool)) (hsCesaro sheetShiftUnitary N sheetPacket -
      atomicPinch sheetShiftUnitary memSchattenClass_one_sheetPacket.one_isHilbertSchmidt) := by
  rw [atomicPinch_sheetPacket, sub_zero]
  have hM := memSchattenClass_one_hsCesaro sheetShiftUnitary memSchattenClass_one_sheetPacket N
  have h1 := RHTower.traceNorm_comp_left_le hM.one_summable_approxNumber sheetProj
  rw [sheetProj_comp_hsCesaro, traceNorm_orthoAverage (orthonormal_sheetOrbit false) hN] at h1
  have hE : ‖sheetProj‖ ≤ 1 := norm_lpDiag_le _ _ _ _
  calc (1 : ℝ) ≤ ‖sheetProj‖ * RHTower.traceNorm _ (hsCesaro sheetShiftUnitary N sheetPacket) := h1
    _ ≤ 1 * RHTower.traceNorm _ (hsCesaro sheetShiftUnitary N sheetPacket) :=
        mul_le_mul_of_nonneg_right hE (RHTower.traceNorm_nonneg _)
    _ = _ := one_mul _

/-- **Hostile boundary of Theorem 5.1.**  There is a trace-class packet with zero continuous mass
whose formation does not converge to its atomic pinching in trace norm. -/
theorem exists_traceClass_continuousMass_zero_not_tendsto :
    ∃ T : LpTwo (ℤ × Bool) →L[ℂ] LpTwo (ℤ × Bool), ∃ hT : RHTower.MemSchattenClass 1 T,
      continuousMass sheetShiftUnitary T = 0 ∧
      ¬ Tendsto (fun N => RHTower.traceNorm _
        (hsCesaro sheetShiftUnitary N T - atomicPinch sheetShiftUnitary hT.one_isHilbertSchmidt))
        atTop (𝓝 0) := by
  refine ⟨sheetPacket, memSchattenClass_one_sheetPacket, continuousMass_sheetPacket, fun h => ?_⟩
  obtain ⟨N, hN⟩ := (h.eventually (gt_mem_nhds one_pos)).exists_forall_of_atTop
  have := sheetPacket_formation_traceNorm (N := max N 1) (by omega)
  linarith [hN (max N 1) (le_max_left _ _)]

end GaloisForLFunctions.HTGeometry
