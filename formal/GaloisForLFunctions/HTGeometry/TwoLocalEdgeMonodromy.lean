import GaloisForLFunctions.Bottcher.CircleDegree
import GaloisForLFunctions.Bottcher.WindingBasepoint
import GaloisForLFunctions.HTGeometry.OddWindingSheetSwap
import GaloisForLFunctions.HTGeometry.TwoLocalIsolatedEdgeSpectrum
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Tactic

/-!
# An explicit two-local spectral sheet-swap loop

For every selected Boolean environment, this file gives a closed complex
longitudinal-field loop for the two-local star Hamiltonian constructed in
`TwoLocalIsolatedEdgeSpectrum`.  Along that loop:

* the selected two-level characteristic radicand winds once around zero;
* an explicit eigenvalue lift returns with the opposite sign;
* every non-selected environment block remains nondegenerate.

Thus the local parameter loop has exactly one quadratic branch pair.  This
is the constructive local input needed for a transposition generator in the
generic two-local spectral monodromy argument.
-/

open Topology unitInterval

namespace GaloisForLFunctions.HTGeometry

/-- Standard unit phase, traversed once on the unit interval. -/
noncomputable def twoLocalMonodromyPhase (s : I) : ℂ :=
  Complex.exp
    ((2 * (Real.pi : ℂ) * Complex.I) * (s : ℝ))

theorem twoLocalMonodromyPhase_norm (s : I) :
    ‖twoLocalMonodromyPhase s‖ = 1 := by
  rw [twoLocalMonodromyPhase, Complex.norm_exp]
  norm_num [Complex.mul_re]

theorem twoLocalMonodromyPhase_re_le_one (s : I) :
    (twoLocalMonodromyPhase s).re ≤ 1 := by
  exact (Complex.re_le_norm _).trans_eq
    (twoLocalMonodromyPhase_norm s)

/-- Argument of the principal square root defining the closed parameter
loop.  It stays in the unit ball about `1`, hence in the slit plane. -/
noncomputable def twoLocalMonodromySqrtArgument (s : I) : ℂ :=
  1 - (1 / 4 : ℂ) * twoLocalMonodromyPhase s

theorem twoLocalMonodromySqrtArgument_mem_slitPlane (s : I) :
    twoLocalMonodromySqrtArgument s ∈ Complex.slitPlane := by
  rw [twoLocalMonodromySqrtArgument, sub_eq_add_neg]
  apply Complex.mem_slitPlane_of_norm_lt_one
  rw [norm_neg, norm_mul, twoLocalMonodromyPhase_norm, mul_one]
  norm_num

/-- Closed longitudinal-field loop centered at the selected simple branch.
The inverse-branch parametrization is chosen so that its selected
radicand is exactly a radius-`1/4` circle. -/
noncomputable def twoLocalSelectedEdgeParameter (s : I) : ℂ :=
  Complex.I * Complex.sqrt (twoLocalMonodromySqrtArgument s)

theorem continuous_twoLocalMonodromyPhase :
    Continuous twoLocalMonodromyPhase := by
  unfold twoLocalMonodromyPhase
  fun_prop

theorem continuous_twoLocalMonodromySqrtArgument :
    Continuous twoLocalMonodromySqrtArgument := by
  unfold twoLocalMonodromySqrtArgument
  exact continuous_const.sub
    (continuous_const.mul continuous_twoLocalMonodromyPhase)

theorem continuous_twoLocalSelectedEdgeParameter :
    Continuous twoLocalSelectedEdgeParameter := by
  unfold twoLocalSelectedEdgeParameter
  apply continuous_const.mul
  exact Complex.continuousOn_sqrt.comp_continuous
    continuous_twoLocalMonodromySqrtArgument
    twoLocalMonodromySqrtArgument_mem_slitPlane

@[simp] theorem twoLocalMonodromyPhase_zero :
    twoLocalMonodromyPhase 0 = 1 := by
  simp [twoLocalMonodromyPhase]

@[simp] theorem twoLocalMonodromyPhase_one :
    twoLocalMonodromyPhase 1 = 1 := by
  simp [twoLocalMonodromyPhase]

/-- The Hamiltonian parameter itself closes after one circuit. -/
theorem twoLocalSelectedEdgeParameter_closed :
    twoLocalSelectedEdgeParameter 1 =
      twoLocalSelectedEdgeParameter 0 := by
  simp [twoLocalSelectedEdgeParameter,
    twoLocalMonodromySqrtArgument]

private theorem twoLocalMonodromySqrt_sq (s : I) :
    (Complex.sqrt (twoLocalMonodromySqrtArgument s)) ^ 2 =
      twoLocalMonodromySqrtArgument s := by
  simp [Complex.sqrt]

/-- Exact selected-block radicand: the inverse-branch parameter converts
the quadratic divisor into the standard once-winding circle. -/
theorem twoLocalSelectedEdgeRadicand_eq_phase {m : ℕ}
    (z₀ : Fin m → Bool) (s : I) :
    twoLocalEdgeBranchRadicand z₀ z₀
        (twoLocalSelectedEdgeParameter s) =
      (1 / 4 : ℂ) * twoLocalMonodromyPhase s := by
  rw [twoLocalEdgeBranchRadicand]
  simp only [starIsingBinaryCode_self, Nat.cast_zero, zero_add]
  rw [twoLocalSelectedEdgeParameter,
    mul_pow, twoLocalMonodromySqrt_sq]
  simp only [Complex.I_sq]
  rw [twoLocalMonodromySqrtArgument]
  ring

private theorem twoLocalMonodromySqrt_re_nonneg (s : I) :
    0 ≤
      (Complex.sqrt
        (twoLocalMonodromySqrtArgument s)).re := by
  have hre :
      (Complex.sqrt
        (twoLocalMonodromySqrtArgument s)).re =
        Real.sqrt
          ((‖twoLocalMonodromySqrtArgument s‖ +
              (twoLocalMonodromySqrtArgument s).re) / 2) := by
    rw [Complex.sqrt_eq_real_add_ite]
    split_ifs <;> norm_num [Complex.mul_re]
  rw [hre]
  exact Real.sqrt_nonneg _

theorem twoLocalSelectedEdgeParameter_im_nonneg (s : I) :
    0 ≤ (twoLocalSelectedEdgeParameter s).im := by
  simpa [twoLocalSelectedEdgeParameter, Complex.mul_im] using
    twoLocalMonodromySqrt_re_nonneg s

/-- The inverse-branch loop stays within distance `1/4` of its selected
branch point `i`.  This quantitative collar later keeps every other
Boolean block in the open right half-plane. -/
theorem twoLocalSelectedEdgeParameter_dist_I_le_quarter (s : I) :
    ‖twoLocalSelectedEdgeParameter s - Complex.I‖ ≤ 1 / 4 := by
  let w : ℂ := twoLocalSelectedEdgeParameter s
  have hfactor :
      (w - Complex.I) * (w + Complex.I) =
        (1 / 4 : ℂ) * twoLocalMonodromyPhase s := by
    have hselected :=
      twoLocalSelectedEdgeRadicand_eq_phase
        (m := 0) (fun i => Fin.elim0 i) s
    have hselected' :
        w ^ 2 + 1 =
          (1 / 4 : ℂ) * twoLocalMonodromyPhase s := by
      simpa [w, twoLocalEdgeBranchRadicand] using hselected
    calc
      (w - Complex.I) * (w + Complex.I) =
          w ^ 2 - Complex.I ^ 2 := by ring
      _ = w ^ 2 + 1 := by rw [Complex.I_sq]; ring
      _ = (1 / 4 : ℂ) * twoLocalMonodromyPhase s :=
        hselected'
  have hnormProduct :
      ‖w - Complex.I‖ * ‖w + Complex.I‖ = 1 / 4 := by
    have h := congrArg norm hfactor
    rw [norm_mul, norm_mul, twoLocalMonodromyPhase_norm] at h
    norm_num at h ⊢
    exact h
  have hplusIm : 1 ≤ (w + Complex.I).im := by
    change 1 ≤ w.im + 1
    exact le_add_of_nonneg_left
      (twoLocalSelectedEdgeParameter_im_nonneg s)
  have hplusNorm : 1 ≤ ‖w + Complex.I‖ := by
    have himNorm := Complex.abs_im_le_norm (w + Complex.I)
    rw [abs_of_nonneg (le_trans (by norm_num) hplusIm)] at himNorm
    exact hplusIm.trans himNorm
  calc
    ‖w - Complex.I‖ ≤
        ‖w - Complex.I‖ * ‖w + Complex.I‖ :=
      le_mul_of_one_le_right (norm_nonneg _) hplusNorm
    _ = 1 / 4 := hnormProduct

theorem abs_twoLocalSelectedEdgeParameter_re_le_quarter (s : I) :
    |(twoLocalSelectedEdgeParameter s).re| ≤ 1 / 4 := by
  calc
    |(twoLocalSelectedEdgeParameter s).re| =
        |(twoLocalSelectedEdgeParameter s - Complex.I).re| := by
      norm_num
    _ ≤ ‖twoLocalSelectedEdgeParameter s - Complex.I‖ :=
      Complex.abs_re_le_norm _
    _ ≤ 1 / 4 :=
      twoLocalSelectedEdgeParameter_dist_I_le_quarter s

theorem twoLocalSelectedEdgeParameter_im_ge_three_quarters (s : I) :
    (3 / 4 : ℝ) ≤
      (twoLocalSelectedEdgeParameter s).im := by
  have himNorm :=
    Complex.abs_im_le_norm
      (twoLocalSelectedEdgeParameter s - Complex.I)
  have hdist :=
    twoLocalSelectedEdgeParameter_dist_I_le_quarter s
  have himAbs :
      |(twoLocalSelectedEdgeParameter s).im - 1| ≤
        (1 / 4 : ℝ) := by
    norm_num [Complex.sub_im] at himNorm
    exact himNorm.trans hdist
  have hlower := (abs_le.mp himAbs).1
  linarith

/-- Explicit continuous eigenvalue lift of the selected two-level block. -/
noncomputable def twoLocalSelectedEigenvalueLift (s : I) : ℂ :=
  (1 / 2 : ℂ) *
    Complex.exp
      (((Real.pi : ℂ) * Complex.I) * (s : ℝ))

theorem continuous_twoLocalSelectedEigenvalueLift :
    Continuous twoLocalSelectedEigenvalueLift := by
  unfold twoLocalSelectedEigenvalueLift
  fun_prop

theorem twoLocalSelectedEigenvalueLift_ne_zero (s : I) :
    twoLocalSelectedEigenvalueLift s ≠ 0 := by
  unfold twoLocalSelectedEigenvalueLift
  exact mul_ne_zero (by norm_num) (Complex.exp_ne_zero _)

/-- The explicit lift squares to the selected characteristic radicand. -/
theorem twoLocalSelectedEigenvalueLift_sq {m : ℕ}
    (z₀ : Fin m → Bool) (s : I) :
    (twoLocalSelectedEigenvalueLift s) ^ 2 =
      twoLocalEdgeBranchRadicand z₀ z₀
        (twoLocalSelectedEdgeParameter s) := by
  rw [twoLocalSelectedEdgeRadicand_eq_phase]
  unfold twoLocalSelectedEigenvalueLift
  rw [mul_pow]
  norm_num [twoLocalMonodromyPhase, pow_two,
    ← Complex.exp_add]
  congr 1
  ring

/-- The selected eigenvalue lift is a root of the exact two-level
characteristic polynomial at every point of the loop. -/
theorem det_twoLocalSelectedEigenvalueLift_eq_zero {m : ℕ}
    (z₀ : Fin m → Bool) (s : I) :
    (twoLocalEdgeCharacteristicMatrix z₀ z₀
      (twoLocalSelectedEdgeParameter s)
      (twoLocalSelectedEigenvalueLift s)).det = 0 := by
  rw [det_twoLocalEdgeCharacteristicMatrix,
    twoLocalSelectedEigenvalueLift_sq]
  ring

/-- One circuit returns the selected eigenvalue on the opposite sheet. -/
theorem twoLocalSelectedEigenvalueLift_endpoint_swap :
    twoLocalSelectedEigenvalueLift 1 =
      -twoLocalSelectedEigenvalueLift 0 := by
  unfold twoLocalSelectedEigenvalueLift
  rw [show
    Complex.exp (((Real.pi : ℂ) * Complex.I) * ((1 : I) : ℝ)) =
      -1 by simp]
  simp

/-- The sheet swap is forced by odd winding, not by a branch convention:
the normalized selected radicand is the standard degree-one circle. -/
theorem twoLocalSelectedEigenvalueLift_endpoint_swap_of_oddWinding :
    twoLocalSelectedEigenvalueLift 1 =
      -twoLocalSelectedEigenvalueLift 0 := by
  apply squareRootPath_endpoint_eq_neg_of_oddDegree
    ⟨twoLocalSelectedEigenvalueLift,
      continuous_twoLocalSelectedEigenvalueLift⟩
    twoLocalSelectedEigenvalueLift_ne_zero
    (by
      change
        (twoLocalSelectedEigenvalueLift 1) ^ 2 =
          (twoLocalSelectedEigenvalueLift 0) ^ 2
      rw [twoLocalSelectedEigenvalueLift_endpoint_swap]
      ring)
    Pi1CMinusZero.circleLoop
  · intro s
    change
      (twoLocalSelectedEigenvalueLift s /
          twoLocalSelectedEigenvalueLift 0) ^ 2 =
        (Pi1CMinusZero.circleLoop s : ℂ)
    show
      (twoLocalSelectedEigenvalueLift s /
          twoLocalSelectedEigenvalueLift 0) ^ 2 =
        (Pi1CMinusZero.circleLoop s : ℂ)
    simp [twoLocalSelectedEigenvalueLift,
      Pi1CMinusZero.circleLoop, Pi1CMinusZero.pexp,
      
      ]
    rw [show
      (2 : ℂ)⁻¹ *
          Complex.exp ((Real.pi : ℂ) * Complex.I * (s : ℝ)) *
          2 =
        Complex.exp ((Real.pi : ℂ) * Complex.I * (s : ℝ)) by
      ring]
    rw [pow_two, ← Complex.exp_add]
    congr 1
    ring
  · exact ⟨0, by
      rw [Pi1CMinusZero.degZ_circleLoop]
      norm_num⟩

/-- At every point of the loop, distinct Boolean environments have
distinct quadratic radicands.  The only algebraic alternative to equal
codes would force the longitudinal parameter to be real, contradicting
the loop's uniform imaginary-height bound. -/
theorem twoLocalEdgeBranchRadicand_injective_along_selectedLoop
    {m : ℕ} (z₀ : Fin m → Bool) (s : I) :
    Function.Injective fun z : Fin m → Bool =>
      twoLocalEdgeBranchRadicand z₀ z
        (twoLocalSelectedEdgeParameter s) := by
  intro z y heq
  have hsquare :
      ((starIsingBinaryCode z₀ z : ℂ) +
          twoLocalSelectedEdgeParameter s) ^ 2 =
        ((starIsingBinaryCode z₀ y : ℂ) +
          twoLocalSelectedEdgeParameter s) ^ 2 := by
    change
      twoLocalEdgeBranchRadicand z₀ z
          (twoLocalSelectedEdgeParameter s) =
        twoLocalEdgeBranchRadicand z₀ y
          (twoLocalSelectedEdgeParameter s) at heq
    simp only [twoLocalEdgeBranchRadicand] at heq
    linear_combination heq
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsquare with hsame | hopposite
  · apply starIsingBinaryCode_injective z₀
    have hcast :
        (starIsingBinaryCode z₀ z : ℂ) =
          (starIsingBinaryCode z₀ y : ℂ) := by
      linear_combination hsame
    exact_mod_cast hcast
  · have him := congrArg Complex.im hopposite
    norm_num [Complex.add_im] at him
    have hheight :=
      twoLocalSelectedEdgeParameter_im_ge_three_quarters s
    linarith

/-- No eigenvalue root belonging to one environment block can collide with
an eigenvalue root of another block anywhere on the loop.  This statement
is branch-independent: only the two characteristic equations are used. -/
theorem twoLocalCrossBlockEigenvalue_ne_along_selectedLoop
    {m : ℕ} (z₀ z y : Fin m → Bool) (hzy : z ≠ y)
    (s : I) {lam mu : ℂ}
    (hlam :
      lam ^ 2 =
        twoLocalEdgeBranchRadicand z₀ z
          (twoLocalSelectedEdgeParameter s))
    (hmu :
      mu ^ 2 =
        twoLocalEdgeBranchRadicand z₀ y
          (twoLocalSelectedEdgeParameter s)) :
    lam ≠ mu := by
  intro heq
  apply hzy
  apply
    twoLocalEdgeBranchRadicand_injective_along_selectedLoop
      z₀ s
  change
    twoLocalEdgeBranchRadicand z₀ z
        (twoLocalSelectedEdgeParameter s) =
      twoLocalEdgeBranchRadicand z₀ y
        (twoLocalSelectedEdgeParameter s)
  rw [← hlam, ← hmu, heq]

/-- Every non-selected block stays in the open right half-plane.  The
quantitative estimate uses the exact `1/4` branch circle and the
distance-`1/4` collar around `i`; for the smallest nonzero Boolean code
the remaining real-part margin is already strictly positive. -/
theorem twoLocalNonselectedEdgeRadicand_re_pos {m : ℕ}
    (z₀ z : Fin m → Bool) (hz : z ≠ z₀) (s : I) :
    0 <
      (twoLocalEdgeBranchRadicand z₀ z
        (twoLocalSelectedEdgeParameter s)).re := by
  let c : ℕ := starIsingBinaryCode z₀ z
  let w : ℂ := twoLocalSelectedEdgeParameter s
  have hcpos : 0 < c := Nat.pos_of_ne_zero
    (by
      intro hc
      exact hz ((starIsingBinaryCode_eq_zero_iff z₀ z).mp hc))
  have hcReal : (1 : ℝ) ≤ c := by
    exact_mod_cast hcpos
  have hwAbs :
      |w.re| ≤ (1 / 4 : ℝ) := by
    exact abs_twoLocalSelectedEdgeParameter_re_le_quarter s
  have hwLower : -(1 / 4 : ℝ) ≤ w.re :=
    (abs_le.mp hwAbs).1
  have hphaseAbs :
      |(twoLocalMonodromyPhase s).re| ≤ 1 := by
    simpa [twoLocalMonodromyPhase_norm s] using
      Complex.abs_re_le_norm (twoLocalMonodromyPhase s)
  have hphaseLower :
      -(1 : ℝ) ≤ (twoLocalMonodromyPhase s).re :=
    (abs_le.mp hphaseAbs).1
  have hdecomposition :
      twoLocalEdgeBranchRadicand z₀ z w =
        (c : ℂ) ^ 2 + 2 * (c : ℂ) * w +
          (1 / 4 : ℂ) * twoLocalMonodromyPhase s := by
    have hselected :=
      twoLocalSelectedEdgeRadicand_eq_phase z₀ s
    rw [twoLocalEdgeBranchRadicand,
      starIsingBinaryCode_self, Nat.cast_zero, zero_add] at hselected
    rw [twoLocalEdgeBranchRadicand]
    change ((c : ℂ) + w) ^ 2 + 1 =
      (c : ℂ) ^ 2 + 2 * (c : ℂ) * w +
        (1 / 4 : ℂ) * twoLocalMonodromyPhase s
    rw [← hselected]
    ring
  have hre := congrArg Complex.re hdecomposition
  norm_num [pow_two, Complex.mul_re] at hre
  have hcNonneg : (0 : ℝ) ≤ c := by positivity
  have hcsq : (c : ℝ) ≤ (c : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hcReal) hcNonneg]
  rw [hre]
  nlinarith

/-- No non-selected Boolean environment meets its quadratic branch divisor
anywhere on the explicit selected loop. -/
theorem twoLocalNonselectedEdgeRadicand_ne_zero {m : ℕ}
    (z₀ z : Fin m → Bool) (hz : z ≠ z₀) (s : I) :
    twoLocalEdgeBranchRadicand z₀ z
        (twoLocalSelectedEdgeParameter s) ≠ 0 := by
  intro hzero
  have hre := congrArg Complex.re hzero
  have hpos :=
    twoLocalNonselectedEdgeRadicand_re_pos z₀ z hz s
  simp at hre
  linarith

/-- Closed radicand path of one Boolean environment block. -/
noncomputable def twoLocalEdgeRadicandPath {m : ℕ}
    (z₀ z : Fin m → Bool) :
    Path
      (twoLocalEdgeBranchRadicand z₀ z
        (twoLocalSelectedEdgeParameter 0))
      (twoLocalEdgeBranchRadicand z₀ z
        (twoLocalSelectedEdgeParameter 0)) where
  toFun := fun s =>
    twoLocalEdgeBranchRadicand z₀ z
      (twoLocalSelectedEdgeParameter s)
  continuous_toFun := by
    unfold twoLocalEdgeBranchRadicand
    exact
      ((continuous_const.add
        continuous_twoLocalSelectedEdgeParameter).pow 2).add
        continuous_const
  source' := rfl
  target' := by
    rw [twoLocalSelectedEdgeParameter_closed]

/-- Canonically normalized non-selected radicand loop in `ℂ*`. -/
noncomputable def twoLocalNonselectedNormalizedRadicandLoop {m : ℕ}
    (z₀ z : Fin m → Bool) (hz : z ≠ z₀) :
    Path Pi1CMinusZero.one_cs Pi1CMinusZero.one_cs :=
  Bottcher.normLoop (twoLocalEdgeRadicandPath z₀ z) 0
    (fun s =>
      twoLocalNonselectedEdgeRadicand_ne_zero z₀ z hz s)

/-- Every non-selected radicand loop has exactly zero winding.  The proof
constructs its principal-log lift explicitly; right-half-plane confinement
makes that lift continuous and the closed Hamiltonian loop makes its
endpoint return to zero. -/
theorem twoLocalNonselectedNormalizedRadicandLoop_degree_zero {m : ℕ}
    (z₀ z : Fin m → Bool) (hz : z ≠ z₀) :
    Pi1CMinusZero.degZ
      ⟦twoLocalNonselectedNormalizedRadicandLoop z₀ z hz⟧ = 0 := by
  let P := twoLocalEdgeRadicandPath z₀ z
  have hne : ∀ s : I, (P s : ℂ) ≠ 0 := fun s =>
    twoLocalNonselectedEdgeRadicand_ne_zero z₀ z hz s
  have hlogContinuous :
      Continuous fun s : I => Complex.log (P s : ℂ) :=
    (P.continuous.clog fun s =>
      Or.inl
        (twoLocalNonselectedEdgeRadicand_re_pos z₀ z hz s))
  let L : C(I, ℂ) :=
    ⟨fun s => Complex.log (P s : ℂ) -
        Complex.log (P 0 : ℂ),
      hlogContinuous.sub continuous_const⟩
  let q :=
    twoLocalNonselectedNormalizedRadicandLoop z₀ z hz
  have hL : Pi1CMinusZero.pexp ∘ L = q := by
    funext s
    apply Subtype.ext
    change
      Complex.exp
          (Complex.log (P s : ℂ) -
            Complex.log (P 0 : ℂ)) =
        ((P s : ℂ) - 0) / ((P 0 : ℂ) - 0)
    rw [Complex.exp_sub, Complex.exp_log (hne s),
      Complex.exp_log (hne 0)]
    ring
  have hL0 : L 0 = (Pi1CMinusZero.e0 : ℂ) := by
    change
      Complex.log (P 0 : ℂ) -
          Complex.log (P 0 : ℂ) = 0
    ring
  have hL1 :
      (L 1 : ℂ) =
        ((0 : ℤ) : ℂ) *
          (2 * (Real.pi : ℂ) * Complex.I) := by
    dsimp [L]
    simp only [Int.cast_zero, zero_mul]
    rw [P.target, P.source]
    ring
  change Pi1CMinusZero.degZ ⟦q⟧ = 0
  exact Pi1CMinusZero.degZ_eq_of_lift
    q L hL hL0 0 hL1

/-- Principal square-root continuation of a non-selected block. -/
noncomputable def twoLocalNonselectedEigenvalueLift {m : ℕ}
    (z₀ z : Fin m → Bool) (s : I) : ℂ :=
  Complex.sqrt
    (twoLocalEdgeBranchRadicand z₀ z
      (twoLocalSelectedEdgeParameter s))

theorem continuous_twoLocalNonselectedEigenvalueLift {m : ℕ}
    (z₀ z : Fin m → Bool) (hz : z ≠ z₀) :
    Continuous (twoLocalNonselectedEigenvalueLift z₀ z) := by
  unfold twoLocalNonselectedEigenvalueLift
  apply Complex.continuousOn_sqrt.comp_continuous
  · exact (twoLocalEdgeRadicandPath z₀ z).continuous
  · intro s
    exact Complex.mem_slitPlane_iff.mpr
      (Or.inl
        (twoLocalNonselectedEdgeRadicand_re_pos z₀ z hz s))

theorem twoLocalNonselectedEigenvalueLift_sq {m : ℕ}
    (z₀ z : Fin m → Bool) (s : I) :
    (twoLocalNonselectedEigenvalueLift z₀ z s) ^ 2 =
      twoLocalEdgeBranchRadicand z₀ z
        (twoLocalSelectedEdgeParameter s) := by
  simp [twoLocalNonselectedEigenvalueLift, Complex.sqrt]

/-- Every non-selected eigenvalue branch returns to itself. -/
theorem twoLocalNonselectedEigenvalueLift_closed {m : ℕ}
    (z₀ z : Fin m → Bool) :
    twoLocalNonselectedEigenvalueLift z₀ z 1 =
      twoLocalNonselectedEigenvalueLift z₀ z 0 := by
  simp [twoLocalNonselectedEigenvalueLift,
    twoLocalSelectedEdgeParameter_closed]

theorem twoLocalEdgeRadicand_ne_zero_along_selectedLoop {m : ℕ}
    (z₀ z : Fin m → Bool) (s : I) :
    twoLocalEdgeBranchRadicand z₀ z
      (twoLocalSelectedEdgeParameter s) ≠ 0 := by
  by_cases hz : z = z₀
  · subst z
    rw [twoLocalSelectedEdgeRadicand_eq_phase]
    exact mul_ne_zero (by norm_num)
      (Complex.exp_ne_zero _)
  · exact twoLocalNonselectedEdgeRadicand_ne_zero z₀ z hz s

/-- Continuous choice of one eigenvalue in each environment block.  The
selected environment uses the explicit sheet-swapping lift; every other
environment uses the closed principal lift in the right half-plane. -/
noncomputable def twoLocalBaseEigenvalueLift {m : ℕ}
    (z₀ z : Fin m → Bool) (s : I) : ℂ :=
  if z = z₀ then
    twoLocalSelectedEigenvalueLift s
  else
    twoLocalNonselectedEigenvalueLift z₀ z s

theorem continuous_twoLocalBaseEigenvalueLift {m : ℕ}
    (z₀ z : Fin m → Bool) :
    Continuous (twoLocalBaseEigenvalueLift z₀ z) := by
  classical
  change Continuous fun s =>
    if z = z₀ then
      twoLocalSelectedEigenvalueLift s
    else
      twoLocalNonselectedEigenvalueLift z₀ z s
  by_cases hz : z = z₀
  · simpa only [if_pos hz] using
      continuous_twoLocalSelectedEigenvalueLift
  · simpa only [if_neg hz] using
      continuous_twoLocalNonselectedEigenvalueLift z₀ z hz

theorem twoLocalBaseEigenvalueLift_sq {m : ℕ}
    (z₀ z : Fin m → Bool) (s : I) :
    (twoLocalBaseEigenvalueLift z₀ z s) ^ 2 =
      twoLocalEdgeBranchRadicand z₀ z
        (twoLocalSelectedEdgeParameter s) := by
  classical
  by_cases hz : z = z₀
  · subst z
    rw [twoLocalBaseEigenvalueLift, if_pos rfl]
    exact twoLocalSelectedEigenvalueLift_sq z₀ s
  · rw [twoLocalBaseEigenvalueLift, if_neg hz]
    exact twoLocalNonselectedEigenvalueLift_sq z₀ z s

theorem twoLocalBaseEigenvalueLift_ne_zero {m : ℕ}
    (z₀ z : Fin m → Bool) (s : I) :
    twoLocalBaseEigenvalueLift z₀ z s ≠ 0 := by
  intro hzero
  have hsquare :=
    twoLocalBaseEigenvalueLift_sq z₀ z s
  rw [hzero, zero_pow (by norm_num)] at hsquare
  exact
    (twoLocalEdgeRadicand_ne_zero_along_selectedLoop
      z₀ z s) hsquare.symm

/-- Permutation that flips exactly the distinguished Boolean coordinate
above the selected environment and fixes every other state. -/
def twoLocalSelectedEdgeSwap {m : ℕ}
    (z₀ : Fin m → Bool) :
    Equiv (Bool × (Fin m → Bool))
      (Bool × (Fin m → Bool)) where
  toFun x :=
    if x.2 = z₀ then (!x.1, x.2) else x
  invFun x :=
    if x.2 = z₀ then (!x.1, x.2) else x
  left_inv := by
    rintro ⟨b, z⟩
    by_cases hz : z = z₀ <;>
      simp [hz]
  right_inv := by
    rintro ⟨b, z⟩
    by_cases hz : z = z₀ <;>
      simp [hz]

/-- The two signed eigenvalue lifts in every environment block. -/
noncomputable def twoLocalGlobalEigenvalueLift {m : ℕ}
    (z₀ : Fin m → Bool)
    (x : Bool × (Fin m → Bool)) (s : I) : ℂ :=
  if x.1 then
    -twoLocalBaseEigenvalueLift z₀ x.2 s
  else
    twoLocalBaseEigenvalueLift z₀ x.2 s

theorem continuous_twoLocalGlobalEigenvalueLift {m : ℕ}
    (z₀ : Fin m → Bool)
    (x : Bool × (Fin m → Bool)) :
    Continuous (twoLocalGlobalEigenvalueLift z₀ x) := by
  rcases x with ⟨b, z⟩
  cases b
  · change Continuous (twoLocalBaseEigenvalueLift z₀ z)
    exact continuous_twoLocalBaseEigenvalueLift z₀ z
  · change Continuous fun s =>
      -twoLocalBaseEigenvalueLift z₀ z s
    exact (continuous_twoLocalBaseEigenvalueLift z₀ z).neg

theorem twoLocalGlobalEigenvalueLift_sq {m : ℕ}
    (z₀ : Fin m → Bool)
    (x : Bool × (Fin m → Bool)) (s : I) :
    (twoLocalGlobalEigenvalueLift z₀ x s) ^ 2 =
      twoLocalEdgeBranchRadicand z₀ x.2
        (twoLocalSelectedEdgeParameter s) := by
  cases x.1 <;>
    simp [twoLocalGlobalEigenvalueLift,
      twoLocalBaseEigenvalueLift_sq]

theorem det_twoLocalGlobalEigenvalueLift_eq_zero {m : ℕ}
    (z₀ : Fin m → Bool)
    (x : Bool × (Fin m → Bool)) (s : I) :
    (twoLocalEdgeCharacteristicMatrix z₀ x.2
      (twoLocalSelectedEdgeParameter s)
      (twoLocalGlobalEigenvalueLift z₀ x s)).det = 0 := by
  rw [det_twoLocalEdgeCharacteristicMatrix,
    twoLocalGlobalEigenvalueLift_sq]
  ring

/-- Endpoint law: the closed Hamiltonian loop acts on its complete
eigenvalue labeling by exactly one Boolean-edge transposition. -/
theorem twoLocalGlobalEigenvalueLift_endpoint_permutation {m : ℕ}
    (z₀ : Fin m → Bool)
    (x : Bool × (Fin m → Bool)) :
    twoLocalGlobalEigenvalueLift z₀ x 1 =
      twoLocalGlobalEigenvalueLift z₀
        (twoLocalSelectedEdgeSwap z₀ x) 0 := by
  rcases x with ⟨b, z⟩
  by_cases hz : z = z₀
  · subst z
    cases b <;>
      simp [twoLocalGlobalEigenvalueLift,
        twoLocalBaseEigenvalueLift,
        twoLocalSelectedEdgeSwap,
        twoLocalSelectedEigenvalueLift_endpoint_swap]
  · cases b <;>
      simp [twoLocalGlobalEigenvalueLift,
        twoLocalBaseEigenvalueLift,
        twoLocalSelectedEdgeSwap, hz,
        twoLocalNonselectedEigenvalueLift_closed]

/-- The complete signed eigenvalue labeling is injective at every point of
the loop: no within-block or cross-block collision occurs. -/
theorem twoLocalGlobalEigenvalueLift_injective {m : ℕ}
    (z₀ : Fin m → Bool) (s : I) :
    Function.Injective fun x : Bool × (Fin m → Bool) =>
      twoLocalGlobalEigenvalueLift z₀ x s := by
  rintro ⟨b, z⟩ ⟨d, y⟩ heq
  have hsq := congrArg (fun q : ℂ => q ^ 2) heq
  rw [twoLocalGlobalEigenvalueLift_sq,
    twoLocalGlobalEigenvalueLift_sq] at hsq
  have hzy : z = y :=
    twoLocalEdgeBranchRadicand_injective_along_selectedLoop
      z₀ s hsq
  subst y
  have hrootNe :=
    twoLocalBaseEigenvalueLift_ne_zero z₀ z s
  cases b <;> cases d
  · rfl
  · exfalso
    simp [twoLocalGlobalEigenvalueLift] at heq
    apply hrootNe
    linear_combination (1 / 2 : ℂ) * heq
  · exfalso
    simp [twoLocalGlobalEigenvalueLift] at heq
    apply hrootNe
    linear_combination (-1 / 2 : ℂ) * heq
  · rfl

/-- Exact single-transposition spectral monodromy certificate. -/
theorem twoLocal_exact_singleEdge_transposition {m : ℕ}
    (z₀ : Fin m → Bool) :
    twoLocalSelectedEdgeParameter 1 =
        twoLocalSelectedEdgeParameter 0 ∧
      (∀ x s,
        (twoLocalEdgeCharacteristicMatrix z₀ x.2
          (twoLocalSelectedEdgeParameter s)
          (twoLocalGlobalEigenvalueLift z₀ x s)).det = 0) ∧
      (∀ s,
        Function.Injective fun x : Bool × (Fin m → Bool) =>
          twoLocalGlobalEigenvalueLift z₀ x s) ∧
      ∀ x,
        twoLocalGlobalEigenvalueLift z₀ x 1 =
          twoLocalGlobalEigenvalueLift z₀
            (twoLocalSelectedEdgeSwap z₀ x) 0 := by
  exact
    ⟨twoLocalSelectedEdgeParameter_closed,
      det_twoLocalGlobalEigenvalueLift_eq_zero z₀,
      twoLocalGlobalEigenvalueLift_injective z₀,
      twoLocalGlobalEigenvalueLift_endpoint_permutation z₀⟩

/-- Full local branch certificate for every chosen Boolean edge: the
parameter closes, the chosen eigenvalue pair swaps, and every other
environment block stays off its branch divisor. -/
theorem exists_twoLocal_exact_singleEdge_sheetSwap {m : ℕ}
    (z₀ : Fin m → Bool) :
    ∃ (w root : C(I, ℂ)),
      w 1 = w 0 ∧
      (∀ s,
        (twoLocalEdgeCharacteristicMatrix z₀ z₀
          (w s) (root s)).det = 0) ∧
      root 1 = -root 0 ∧
      ∀ z ≠ z₀, ∀ s,
        twoLocalEdgeBranchRadicand z₀ z (w s) ≠ 0 := by
  refine ⟨
    ⟨twoLocalSelectedEdgeParameter,
      continuous_twoLocalSelectedEdgeParameter⟩,
    ⟨twoLocalSelectedEigenvalueLift,
      continuous_twoLocalSelectedEigenvalueLift⟩,
    twoLocalSelectedEdgeParameter_closed,
    ?_, twoLocalSelectedEigenvalueLift_endpoint_swap, ?_⟩
  · exact det_twoLocalSelectedEigenvalueLift_eq_zero z₀
  · intro z hz s
    exact twoLocalNonselectedEdgeRadicand_ne_zero z₀ z hz s

end GaloisForLFunctions.HTGeometry
