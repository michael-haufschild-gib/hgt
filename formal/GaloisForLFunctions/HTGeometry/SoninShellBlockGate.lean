import GaloisForLFunctions.HTGeometry.SoninShellTightResolution
import GaloisForLFunctions.HTGeometry.LocalFredholmCofinalFailures
import GaloisForLFunctions.HTGeometry.ProjectionSumCalkinLift
import GaloisForLFunctions.RHTower.SoninEulerEssentialNorm
import GaloisForLFunctions.RHTower.SummableEulerCalkinInjectivity

/-!
# The Sonin shell-block gate

Fix `a > 0` and a scale `p > 1`, with bilateral apertures `a_n = a pⁿ` (`n ∈ ℤ`).  The one-scale
even Sonin corner `L_n` at aperture `a_n` has local Gram `L_n*L_n = S_n` modulo compact operators,
where `S_n = P_n + Q_n` is the sum of the physical shell `P_n` and the Fourier shell `Q_n` between
`a_n` and `a_{n+1}` (`(7.1)`, `(7.2)`).  Since `P_n Q_n` is compact, `S_n` lifts to a genuine
orthogonal projection `Π_n` with `Π_n - S_n` compact; compressing the local Gram to `ran Π_n` gives
blocks `B_n` that are identity plus compact, hence Fredholm, and the block formation `⊕_n B_n` is
upper semi-Fredholm exactly when `inf_n γ(B_n) > 0` and `Σ_n dim ker B_n < ∞` (`(7.4)`).
-/

open Filter Topology
open scoped InnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry.TightFormation

open _root_.RHTower

variable {a p : ℝ} (ha : 0 < a) (hp : 1 < p)

include ha hp in
theorem shellRadius_pos (n : ℤ) : 0 < shellRadius a p n :=
  mul_pos ha (zpow_pos (by linarith) n)

include hp in
theorem shellRadius_add_one (n : ℤ) : shellRadius a p (n + 1) = p * shellRadius a p n := by
  rw [shellRadius, shellRadius, zpow_add_one₀ (by linarith : p ≠ 0)]
  ring

/-- The Fourier shell `Q_n = F_{a_{n+1}} - F_{a_n}`. -/
def fourierShell (a p : ℝ) (n : ℤ) : evenSubspace →L[ℂ] evenSubspace :=
  evenFourierCutoff (shellRadius a p (n + 1)) - evenFourierCutoff (shellRadius a p n)

/-- The one-scale even Sonin corner at aperture `a_n = a pⁿ`. -/
def soninCorner (a p : ℝ) (hp : 1 < p) (n : ℤ) : evenSubspace →L[ℂ] evenSubspace :=
  evenCentralSoninDilationCorner (shellRadius a p n) p hp

include ha in
/-- **`(7.1)`–`(7.2)`**: the local Gram of the corner is `S_n = P_n + Q_n` modulo a compact
residual `K_n = L_n*L_n - S_n`. -/
theorem isCompactOperator_soninCorner_gram_sub (n : ℤ) :
    IsCompactOperator (ContinuousLinearMap.adjoint (soninCorner a p hp n) * soninCorner a p hp n -
      (physicalShell a p n + fourierShell a p n)) := by
  have h := evenCentralSoninDilationCorner_adjoint_mul_compactEq_shell (shellRadius a p n) p
    (shellRadius_pos ha hp n) hp
  rw [← shellRadius_add_one hp n] at h
  exact h

include ha hp in
theorem isStarProjection_physicalShell (n : ℤ) : IsStarProjection (physicalShell a p n) :=
  ⟨ContinuousLinearMap.ext fun x => (physicalShellFamily ha hp).idem n x,
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 fun x y =>
      (physicalShellFamily ha hp).symm n x y⟩

include ha hp in
theorem isStarProjection_fourierShell (n : ℤ) : IsStarProjection (fourierShell a p n) := by
  have hQ : ∀ x, ((soninShellResolution ha hp).conj evenFourierUnitary
      evenFourierUnitary_involutive).P n x = fourierShell a p n x := fun x =>
    soninShellResolution_conj_apply ha hp n x
  refine ⟨ContinuousLinearMap.ext fun x => ?_,
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.2 fun x y => ?_⟩
  · change fourierShell a p n (fourierShell a p n x) = fourierShell a p n x
    rw [← hQ, ← hQ, ((soninShellResolution ha hp).conj evenFourierUnitary
      evenFourierUnitary_involutive).idem n x]
  · change ⟪fourierShell a p n x, y⟫_ℂ = ⟪x, fourierShell a p n y⟫_ℂ
    rw [← hQ, ← hQ, ((soninShellResolution ha hp).conj evenFourierUnitary
      evenFourierUnitary_involutive).symm n x y]

include ha hp in
/-- The physical and Fourier shells are almost orthogonal: `P_n Q_n` is compact. -/
theorem isCompactOperator_physicalShell_comp_fourierShell (n : ℤ) :
    IsCompactOperator (physicalShell a p n ∘L fourierShell a p n) :=
  isCompactOperator_evenIndicatorDiff_mul_evenFourierDiff _ _ _ _ (shellRadius_pos ha hp (n + 1))
    (shellRadius_pos ha hp n)

include ha hp in
/-- The principal shell projection: an orthogonal projection `Π_n` with `Π_n - S_n` compact. -/
theorem exists_soninShellProjection (n : ℤ) :
    ∃ Ψ : evenSubspace →L[ℂ] evenSubspace, IsStarProjection Ψ ∧
      IsCompactOperator (Ψ - (physicalShell a p n + fourierShell a p n)) :=
  exists_isStarProjection_compact_sub_add (isStarProjection_physicalShell ha hp n)
    (isStarProjection_fourierShell ha hp n) (isCompactOperator_physicalShell_comp_fourierShell ha hp n)

/-- A chosen principal shell projection `Π_n`. -/
def soninShellProjection (n : ℤ) : evenSubspace →L[ℂ] evenSubspace :=
  Classical.choose (exists_soninShellProjection ha hp n)

theorem soninShellProjection_spec (n : ℤ) :
    IsStarProjection (soninShellProjection ha hp n) ∧
      IsCompactOperator (soninShellProjection ha hp n - (physicalShell a p n + fourierShell a p n)) :=
  Classical.choose_spec (exists_soninShellProjection ha hp n)

/-- The principal shell space `ran Π_n`. -/
def soninShellSpace (n : ℤ) : Submodule ℂ evenSubspace :=
  LinearMap.range (soninShellProjection ha hp n : evenSubspace →ₗ[ℂ] evenSubspace)

instance soninShellSpace_completeSpace (n : ℤ) : CompleteSpace (soninShellSpace ha hp n) :=
  (ContinuousLinearMap.IsIdempotentElem.isClosed_range
    (soninShellProjection_spec ha hp n).1.isIdempotentElem).completeSpace_coe

theorem starProjection_soninShellSpace (n : ℤ) :
    (soninShellSpace ha hp n).starProjection = soninShellProjection ha hp n := by
  have hΨ := (soninShellProjection_spec ha hp n).1
  have hidem : ∀ x, soninShellProjection ha hp n (soninShellProjection ha hp n x) =
      soninShellProjection ha hp n x := fun x =>
    congrArg (fun T : evenSubspace →L[ℂ] evenSubspace => T x) hΨ.isIdempotentElem.eq
  have hsym : ∀ x y, ⟪soninShellProjection ha hp n x, y⟫_ℂ =
      ⟪x, soninShellProjection ha hp n y⟫_ℂ := hΨ.isSelfAdjoint.isSymmetric
  ext1 x
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (LinearMap.mem_range_self _ x) ?_
  rintro _ ⟨y, rfl⟩
  change ⟪x - soninShellProjection ha hp n x, soninShellProjection ha hp n y⟫_ℂ = 0
  rw [inner_sub_left, ← hsym, ← hsym, hidem, sub_self]

/-- The local Gram `D_n = L_n*L_n` differs from the principal shell projection by a compact
operator. -/
theorem isCompactOperator_soninGram_sub_shell (n : ℤ) :
    IsCompactOperator (ContinuousLinearMap.adjoint (soninCorner a p hp n) ∘L
      soninCorner a p hp n - (soninShellSpace ha hp n).starProjection) := by
  rw [starProjection_soninShellSpace]
  have h1 := isCompactOperator_soninCorner_gram_sub ha hp n
  have h2 := (soninShellProjection_spec ha hp n).2
  have h : ContinuousLinearMap.adjoint (soninCorner a p hp n) ∘L soninCorner a p hp n -
      soninShellProjection ha hp n =
      (ContinuousLinearMap.adjoint (soninCorner a p hp n) * soninCorner a p hp n -
        (physicalShell a p n + fourierShell a p n)) -
      (soninShellProjection ha hp n - (physicalShell a p n + fourierShell a p n)) := by
    rw [ContinuousLinearMap.mul_def]
    abel
  rw [h]
  exact h1.sub h2

/-- The corners are uniformly bounded: `‖L_n‖ ≤ 2`. -/
theorem norm_soninCorner_le (n : ℤ) : ‖soninCorner a p hp n‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun f => ?_
  rw [soninCorner, norm_evenCentralSoninDilationCorner_apply, crossBoundary]
  set P := centralSoninProjection (shellRadius a p n)
  have hP : IsStarProjection P := isStarProjection_starProjection _
  change ‖(1 - P) (dilationSum p hp (P (f : SoninL2)))‖ ≤ 2 * ‖f‖
  have h1 : ‖(1 - P) (dilationSum p hp (P (f : SoninL2)))‖ ≤ ‖dilationSum p hp (P (f : SoninL2))‖ := by
    have := norm_sq_eq_of_isStarProjection hP (dilationSum p hp (P (f : SoninL2)))
    rw [sub_apply, one_apply_eq_self]
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
      (by nlinarith [sq_nonneg ‖P (dilationSum p hp (P (f : SoninL2)))‖])
  have h2 : ‖P (f : SoninL2)‖ ≤ ‖(f : SoninL2)‖ := by
    have := norm_sq_eq_of_isStarProjection hP (f : SoninL2)
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1
      (by nlinarith [sq_nonneg ‖(f : SoninL2) - P (f : SoninL2)‖])
  calc ‖(1 - P) (dilationSum p hp (P (f : SoninL2)))‖
      ≤ ‖dilationSum p hp (P (f : SoninL2))‖ := h1
    _ ≤ ‖dilationSum p hp‖ * ‖P (f : SoninL2)‖ := ContinuousLinearMap.le_opNorm _ _
    _ ≤ 2 * ‖(f : SoninL2)‖ := mul_le_mul (norm_dilationSum_le_two p hp) h2 (norm_nonneg _)
        (by norm_num)
    _ = 2 * ‖f‖ := by rw [Submodule.coe_norm]

theorem norm_soninGram_le (n : ℤ) :
    ‖ContinuousLinearMap.adjoint (soninCorner a p hp n) ∘L soninCorner a p hp n‖ ≤ 4 := by
  calc ‖ContinuousLinearMap.adjoint (soninCorner a p hp n) ∘L soninCorner a p hp n‖
      ≤ ‖ContinuousLinearMap.adjoint (soninCorner a p hp n)‖ * ‖soninCorner a p hp n‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖soninCorner a p hp n‖ * ‖soninCorner a p hp n‖ := by
        rw [LinearIsometryEquiv.norm_map]
    _ ≤ 2 * 2 := mul_le_mul (norm_soninCorner_le hp n) (norm_soninCorner_le hp n)
        (norm_nonneg (soninCorner a p hp n)) (by norm_num)
    _ = 4 := by norm_num

/-- The compressed shell block `B_n = Π_n (L_n*L_n) Π_n|_{ran Π_n}`. -/
def soninShellBlock (n : ℤ) :=
  compressedBlock (soninShellSpace ha hp)
    (fun n => ContinuousLinearMap.adjoint (soninCorner a p hp n) ∘L soninCorner a p hp n) n

/-- **§7**: every shell block is identity plus compact, hence locally Fredholm. -/
theorem soninShellBlock_fredholm (n : ℤ) :
    IsCompactOperator ⇑(soninShellBlock ha hp n - 1) ∧
      IsFredholmOp (E := soninShellSpace ha hp n) (F := soninShellSpace ha hp n)
        (soninShellBlock ha hp n) :=
  compressedBlock_fredholm (soninShellSpace ha hp) _
    (fun n => isCompactOperator_soninGram_sub_shell ha hp n) n

/-- The Sonin source formation `⊕_n B_n` on `⊕_n ran Π_n`. -/
def soninShellFormation :
    lp (fun n => soninShellSpace ha hp n) 2 →L[ℂ] lp (fun n => soninShellSpace ha hp n) 2 :=
  blockFormation (H := fun n => soninShellSpace ha hp n) (Y := fun n => soninShellSpace ha hp n)
    (soninShellBlock ha hp) (by norm_num : (0 : ℝ) ≤ 4)
    fun n => (norm_compressedBlock_le _ _ n).trans (norm_soninGram_le hp n)

/-- **`(7.4)`, the shell-block gate**: the Sonin source formation `⊕_n B_n` is upper
semi-Fredholm exactly when `inf_n γ(B_n) > 0` and `Σ_n dim ker B_n < ∞`. -/
theorem soninShellGate :
    (IsClosed (Set.range (soninShellFormation ha hp)) ∧
      FiniteDimensional ℂ (LinearMap.ker (soninShellFormation ha hp :
        lp (fun n => soninShellSpace ha hp n) 2 →ₗ[ℂ] lp (fun n => soninShellSpace ha hp n) 2))) ↔
      0 < ⨅ n, reducedMinModulus (E := soninShellSpace ha hp n) (F := soninShellSpace ha hp n)
        (soninShellBlock ha hp n) ∧
        Cardinal.sum (fun n => Module.rank ℂ
          (LinearMap.ker (soninShellBlock ha hp n :
            soninShellSpace ha hp n →ₗ[ℂ] soninShellSpace ha hp n))) <
            Cardinal.aleph0 :=
  sourceShellGate (soninShellSpace ha hp)
    (fun n => ContinuousLinearMap.adjoint (soninCorner a p hp n) ∘L soninCorner a p hp n)
    (by norm_num) fun n => norm_soninGram_le hp n

end GaloisForLFunctions.HTGeometry.TightFormation
