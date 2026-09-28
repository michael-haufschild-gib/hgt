import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMPhysicalLiftHorizonCurrent
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMActualIngoingCurrent
import GaloisForLFunctions.RHTower.ThetaCuspHawkingBMJointSourceSmooth

/-! # The literal time-lift stream realizes the lift jets

On the static exterior `r > 1` the time-lift stream
`L_j(t, r, z) = P(r) χ(t + r_*(r)) Q_j(z)` (radial profile `P`, onset `χ`, full-square covector
`Q_j`, tortoise coordinate `r_*`) is a smooth field whose complete coordinate two-jet is exactly
`liftJet q s a r v z j` with `v = t + r_*(r)`.  Hence the reconstructed metric action of two such
fields is the lift current, and adding the source contact gives the angular master current. -/

open Set Filter Topology
open scoped ContDiff

namespace RHTower.D4BMPhysicalLiftCurrent
open GaloisForLFunctions.HTGeometry ScalarTwoJet D4BMJointSource D4BMLaplaceRadial
open D4BMModularCore D4BMIngoingCoordinates D4BMActualIngoingCurrent

set_option autoImplicit false

/-! ### Two-jets of fields depending on one coordinate or on the angular block -/

section Jets

private theorem coordDeriv_coord {g : ℝ → ℂ} {g' : ℂ} {i : Fin 4} {y : Fin 4 → ℝ}
    (hg : HasDerivAt g g' (y i)) (k : Fin 4) :
    coordDeriv k (fun z : Fin 4 → ℝ => g (z i)) y = if k = i then g' else 0 := by
  have h := HasFDerivAt.comp (f := fun z : Fin 4 → ℝ => z i) y hg.hasFDerivAt
    (hasFDerivAt_apply i y)
  have he : (fun z : Fin 4 → ℝ => g (z i)) = g ∘ fun z => z i := rfl
  rw [coordDeriv, he, h.fderiv]
  by_cases hk : k = i
  · subst hk
    simp
  · simp [hk, Ne.symm hk]

/-- The two-jet of `z ↦ g (z i)` from the first two derivatives of `g`. -/
theorem ofField_coord {g g₁ : ℝ → ℂ} {g₂ : ℂ} {i : Fin 4} {y : Fin 4 → ℝ}
    (h₁ : ∀ᶠ u in 𝓝 (y i), HasDerivAt g (g₁ u) u) (h₂ : HasDerivAt g₁ g₂ (y i)) :
    ofField (fun z => g (z i)) y =
      ⟨g (y i), fun k => if k = i then g₁ (y i) else 0,
        fun k l => if k = i ∧ l = i then g₂ else 0⟩ := by
  have hloc : ∀ᶠ z in 𝓝 y, HasDerivAt g (g₁ (z i)) (z i) :=
    (continuous_apply i).continuousAt.tendsto.eventually h₁
  ext k l
  · rfl
  · exact coordDeriv_coord h₁.self_of_nhds k
  · change coordDeriv k (coordDeriv l (fun z : Fin 4 → ℝ => g (z i))) y = _
    have he : coordDeriv l (fun z : Fin 4 → ℝ => g (z i)) =ᶠ[𝓝 y]
        fun z => if l = i then g₁ (z i) else 0 := by
      filter_upwards [hloc] with z hz
      exact coordDeriv_coord hz l
    rw [coordDeriv, he.fderiv_eq]
    by_cases hl : l = i
    · simp only [hl, if_true, and_true]
      exact coordDeriv_coord h₂ k
    · simp [hl]

/-- The coordinate projection onto the angular block `(z₂, z₃)`. -/
private noncomputable def angularProj : (Fin 4 → ℝ) →L[ℝ] (Fin 2 → ℝ) :=
  ContinuousLinearMap.pi ![ContinuousLinearMap.proj 2, ContinuousLinearMap.proj 3]

private theorem angularProj_apply (z : Fin 4 → ℝ) : angularProj z = ![z 2, z 3] := by
  funext m
  fin_cases m <;> rfl

/-- The angular index of a coordinate direction: `e₂ ↦ e₀`, `e₃ ↦ e₁`, radial/time `↦ 0`. -/
private theorem angularProj_single (k : Fin 4) :
    angularProj (Pi.single k 1) =
      if k = 2 then Pi.single 0 1 else if k = 3 then Pi.single 1 1 else 0 := by
  funext m
  fin_cases k <;> fin_cases m <;> simp [angularProj_apply]

private theorem coordDeriv_angular {f : (Fin 2 → ℝ) → ℂ} {z : Fin 4 → ℝ}
    (hf : DifferentiableAt ℝ f (angularProj z)) (k : Fin 4) :
    coordDeriv k (fun w : Fin 4 → ℝ => f (angularProj w)) z =
      fderiv ℝ f (angularProj z) (angularProj (Pi.single k 1)) := by
  have h := hf.hasFDerivAt.comp z angularProj.hasFDerivAt
  rw [coordDeriv, show (fun w : Fin 4 → ℝ => f (angularProj w)) = f ∘ angularProj from rfl,
    h.fderiv]
  rfl

/-- The two-jet of `z ↦ f (z₂, z₃)` is the two-jet of `f` placed in the angular block. -/
theorem ofField_angular {f : (Fin 2 → ℝ) → ℂ} {y : Fin 4 → ℝ}
    (hf : ContDiffAt ℝ 2 f ![y 2, y 3]) :
    ofField (fun z => f ![z 2, z 3]) y =
      ⟨f ![y 2, y 3], ![0, 0, (ofField f ![y 2, y 3]).first 0, (ofField f ![y 2, y 3]).first 1],
        fun k l => if k = 2 ∧ l = 2 then (ofField f ![y 2, y 3]).second 0 0
          else if k = 2 ∧ l = 3 then (ofField f ![y 2, y 3]).second 0 1
          else if k = 3 ∧ l = 2 then (ofField f ![y 2, y 3]).second 1 0
          else if k = 3 ∧ l = 3 then (ofField f ![y 2, y 3]).second 1 1 else 0⟩ := by
  have hfun : (fun z : Fin 4 → ℝ => f ![z 2, z 3]) = fun z => f (angularProj z) := by
    funext z
    rw [angularProj_apply]
  have hy : angularProj y = ![y 2, y 3] := angularProj_apply y
  rw [← hy] at hf ⊢
  rw [hfun]
  have hd : DifferentiableAt ℝ f (angularProj y) := hf.differentiableAt (by norm_num)
  have hloc : ∀ᶠ w in 𝓝 y, DifferentiableAt ℝ f (angularProj w) :=
    angularProj.continuous.continuousAt.tendsto.eventually
      ((hf.eventually (by norm_num)).mono fun _ h => h.differentiableAt (by norm_num))
  have hD (v : Fin 2 → ℝ) : DifferentiableAt ℝ (fun w => fderiv ℝ f w v) (angularProj y) :=
    ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).clm_apply
      (differentiableAt_const v)
  ext k l
  · rfl
  · change coordDeriv k (fun w : Fin 4 → ℝ => f (angularProj w)) y = _
    rw [coordDeriv_angular hd, angularProj_single]
    fin_cases k <;> simp [ofField, coordDeriv]
  · change coordDeriv k (coordDeriv l (fun w : Fin 4 → ℝ => f (angularProj w))) y = _
    have he : coordDeriv l (fun w : Fin 4 → ℝ => f (angularProj w)) =ᶠ[𝓝 y]
        fun w => fderiv ℝ f (angularProj w) (angularProj (Pi.single l 1)) := by
      filter_upwards [hloc] with w hw
      exact coordDeriv_angular hw l
    rw [coordDeriv, he.fderiv_eq]
    have h2 := coordDeriv_angular (f := fun w => fderiv ℝ f w (angularProj (Pi.single l 1)))
      (hD _) k
    rw [coordDeriv] at h2
    rw [h2, angularProj_single, angularProj_single]
    fin_cases k <;> fin_cases l <;> simp [ofField, coordDeriv]

end Jets

/-! ### Smoothness of the three factors -/

theorem profile_contDiffAt (s a : ℂ) {r : ℝ} (hr : 0 < r) : ContDiffAt ℝ ∞ (profile s a) r := by
  have he : ∀ᶠ x in 𝓝 r, profile s a x = (-s * (s - 1) / 4) * a ^ 2 * ((x : ℂ)⁻¹) ^ 2 *
      Complex.exp (2 * s * (Real.log (1 + x⁻¹) : ℂ)) := by
    filter_upwards [lt_mem_nhds hr] with x hx
    have hp : (0 : ℝ) < 1 + x⁻¹ := by positivity
    rw [profile, power, Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hp.ne'),
      ← Complex.ofReal_log hp.le]
    ring_nf
  refine ContDiffAt.congr_of_eventuallyEq ?_ he
  have hp : (0 : ℝ) < 1 + r⁻¹ := by positivity
  have hinv : ContDiffAt ℝ ∞ (fun x : ℝ => ((x : ℂ)⁻¹)) r :=
    (Complex.ofRealCLM.contDiff.contDiffAt (x := r)).inv (Complex.ofReal_ne_zero.mpr hr.ne')
  have hlog : ContDiffAt ℝ ∞ (fun x : ℝ => (Real.log (1 + x⁻¹) : ℂ)) r :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp r
      ((contDiffAt_const.add (contDiffAt_inv ℝ hr.ne')).log hp.ne')
  exact (contDiffAt_const.mul (hinv.pow 2)).mul (contDiffAt_const.mul hlog).cexp

/-! ### The time-lift stream -/

/-- The lift stream in the ingoing chart `y = (v, r, X, Y)`: `P(r) χ(v) Q_j(X, Y)`. -/
noncomputable def ingoingLiftStream (q : XiZeroCopy) (s a : ℂ) (j : Fin 2)
    (y : Fin 4 → ℝ) : ℂ :=
  profile s a (y 1) * timeOnset (2 * s) (y 0) * fullSquareCovector q j ![y 2, y 3]

/-- The static time-lift stream `L_j(t, r, X, Y) = P(r) χ(t + r_*(r)) Q_j(X, Y)`. -/
noncomputable def timeLiftStream (q : XiZeroCopy) (s a : ℂ) (j : Fin 2) (x : Fin 4 → ℝ) : ℂ :=
  profile s a (x 1) * timeOnset (2 * s) (x 0 + tortoise (x 1)) *
    fullSquareCovector q j ![x 2, x 3]

theorem timeLiftStream_eq_comp (q : XiZeroCopy) (s a : ℂ) (j : Fin 2) :
    timeLiftStream q s a j = fun x => ingoingLiftStream q s a j (ingoingPoint x) := by
  funext x
  simp [timeLiftStream, ingoingLiftStream, ingoingPoint]

private theorem profile_factor_contDiffAt (s a : ℂ) {y : Fin 4 → ℝ} (hr : 0 < y 1) :
    ContDiffAt ℝ ∞ (fun z : Fin 4 → ℝ => profile s a (z 1)) y :=
  (profile_contDiffAt s a hr).comp y (contDiff_apply ℝ ℝ (1 : Fin 4)).contDiffAt

private theorem onset_factor_contDiffAt (s : ℂ) (y : Fin 4 → ℝ) :
    ContDiffAt ℝ ∞ (fun z : Fin 4 → ℝ => timeOnset (2 * s) (z 0)) y :=
  (timeOnset_smooth (2 * s)).contDiffAt.comp y (contDiff_apply ℝ ℝ (0 : Fin 4)).contDiffAt

private theorem angular_factor_contDiffAt (q : XiZeroCopy) (j : Fin 2) {y : Fin 4 → ℝ}
    (hY : 0 < y 3) (n : ℕ) :
    ContDiffAt ℝ n (fun z : Fin 4 → ℝ => fullSquareCovector q j ![z 2, z 3]) y := by
  have h := fullSquareCovector_smooth q ![y 2, y 3] (by simpa using hY) n j
  have hp : ContDiffAt ℝ n (fun z : Fin 4 → ℝ => ![z 2, z 3]) y := by
    apply contDiffAt_pi.mpr
    intro m
    fin_cases m
    · exact (contDiff_apply ℝ ℝ (2 : Fin 4)).contDiffAt
    · exact (contDiff_apply ℝ ℝ (3 : Fin 4)).contDiffAt
  exact h.comp y hp

/-- The ingoing lift stream is `C²` on `r > 0`, `Y > 0`. -/
theorem ingoingLiftStream_contDiffAt (q : XiZeroCopy) (s a : ℂ) (j : Fin 2) {y : Fin 4 → ℝ}
    (hr : 0 < y 1) (hY : 0 < y 3) : ContDiffAt ℝ 2 (ingoingLiftStream q s a j) y :=
  (((profile_factor_contDiffAt s a hr).of_le (WithTop.coe_le_coe.mpr le_top)).mul
    ((onset_factor_contDiffAt s y).of_le (WithTop.coe_le_coe.mpr le_top))).mul
    (angular_factor_contDiffAt q j hY 2)

/-- **The time-lift stream is a genuine `C²` field** on the static exterior. -/
theorem timeLiftStream_contDiffAt (q : XiZeroCopy) (s a : ℂ) (j : Fin 2) {x : Fin 4 → ℝ}
    (hr : 1 < x 1) (hY : 0 < x 3) : ContDiffAt ℝ 2 (timeLiftStream q s a j) x := by
  rw [timeLiftStream_eq_comp]
  have hc : ContDiffAt ℝ 2 ingoingPoint x := by
    apply contDiffAt_pi.mpr
    intro m
    fin_cases m
    · have ht : ContDiffAt ℝ 2 tortoise (x 1) := by
        have he : ∀ᶠ r in 𝓝 (x 1), tortoise r = (Real.log (r - 1) - Real.log (r + 1)) / 2 :=
          Eventually.of_forall fun r => rfl
        refine ContDiffAt.congr_of_eventuallyEq ?_ he
        exact (((contDiffAt_id.sub contDiffAt_const).log (show x 1 - 1 ≠ 0 by linarith)).sub
          ((contDiffAt_id.add contDiffAt_const).log (show x 1 + 1 ≠ 0 by linarith))).div_const 2
      exact (contDiff_apply ℝ ℝ (0 : Fin 4)).contDiffAt.add
        (ht.comp x (contDiff_apply ℝ ℝ (1 : Fin 4)).contDiffAt)
    · exact (contDiff_apply ℝ ℝ (1 : Fin 4)).contDiffAt
    · exact (contDiff_apply ℝ ℝ (2 : Fin 4)).contDiffAt
    · exact (contDiff_apply ℝ ℝ (3 : Fin 4)).contDiffAt
  have hy1 : 0 < ingoingPoint x 1 := by simp [ingoingPoint]; linarith
  have hy3 : 0 < ingoingPoint x 3 := by simpa [ingoingPoint] using hY
  exact (ingoingLiftStream_contDiffAt q s a j hy1 hy3).comp x hc

/-- The two-jet of the ingoing lift stream: the product of the radial, onset and angular jets. -/
theorem ofField_ingoingLiftStream (q : XiZeroCopy) (s a : ℂ) (j : Fin 2) {y : Fin 4 → ℝ}
    (hr : 0 < y 1) (hY : 0 < y 3) :
    ofField (ingoingLiftStream q s a j) y =
      mul (mul ⟨profile s a (y 1), fun k => if k = 1 then profileFirst s a (y 1) else 0,
          fun k l => if k = 1 ∧ l = 1 then profileSecond s a (y 1) else 0⟩
        ⟨timeOnset (2 * s) (y 0), fun k => if k = 0 then timeOnsetFirst (2 * s) (y 0) else 0,
          fun k l => if k = 0 ∧ l = 0 then timeOnsetSecond (2 * s) (y 0) else 0⟩)
      ⟨fullSquareCovector q j ![y 2, y 3],
        ![0, 0, (angularJets q ![y 2, y 3] j).first 0, (angularJets q ![y 2, y 3] j).first 1],
        fun k l => if k = 2 ∧ l = 2 then (angularJets q ![y 2, y 3] j).second 0 0
          else if k = 2 ∧ l = 3 then (angularJets q ![y 2, y 3] j).second 0 1
          else if k = 3 ∧ l = 2 then (angularJets q ![y 2, y 3] j).second 1 0
          else if k = 3 ∧ l = 3 then (angularJets q ![y 2, y 3] j).second 1 1 else 0⟩ := by
  have hA : ContDiffAt ℝ 2 (fun z : Fin 4 → ℝ => profile s a (z 1)) y :=
    (profile_factor_contDiffAt s a hr).of_le (WithTop.coe_le_coe.mpr le_top)
  have hB : ContDiffAt ℝ 2 (fun z : Fin 4 → ℝ => timeOnset (2 * s) (z 0)) y :=
    (onset_factor_contDiffAt s y).of_le (WithTop.coe_le_coe.mpr le_top)
  have hC := angular_factor_contDiffAt q j hY 2
  have hQ : ContDiffAt ℝ 2 (fullSquareCovector q j) ![y 2, y 3] :=
    fullSquareCovector_smooth q ![y 2, y 3] (by simpa using hY) 2 j
  have hPA : ofField (fun z : Fin 4 → ℝ => profile s a (z 1)) y = _ :=
    ofField_coord (g₁ := profileFirst s a) (i := 1)
      ((lt_mem_nhds hr).mono fun u hu => (profile_derivatives s a ⟨u, hu⟩).1)
      (profile_derivatives s a ⟨y 1, hr⟩).2
  have hPB : ofField (fun z : Fin 4 → ℝ => timeOnset (2 * s) (z 0)) y = _ :=
    ofField_coord (g₁ := timeOnsetFirst (2 * s)) (i := 0)
      (Eventually.of_forall fun u => timeOnset_hasDerivAt (2 * s) u)
      (timeOnsetFirst_hasDerivAt (2 * s) (y 0))
  have hPC := ofField_angular hQ
  have hprod : ofField (ingoingLiftStream q s a j) y =
      mul (mul (ofField (fun z : Fin 4 → ℝ => profile s a (z 1)) y)
        (ofField (fun z : Fin 4 → ℝ => timeOnset (2 * s) (z 0)) y))
        (ofField (fun z : Fin 4 → ℝ => fullSquareCovector q j ![z 2, z 3]) y) := by
    rw [← ofField_mul hA hB, ← ofField_mul (hA.mul hB) hC]
    rfl
  rw [hprod, hPA, hPB, hPC]
  rfl

/-- **The time-lift stream realizes the lift jet.**  At every exterior point, with
`v = t + r_*(r)`, the complete coordinate two-jet of `L_j` is `liftJet q s a r v z j`. -/
theorem ofField_timeLiftStream (q : XiZeroCopy) (s a : ℂ) (j : Fin 2) {x : Fin 4 → ℝ}
    (hr : 1 < x 1) (hY : 0 < x 3) :
    ofField (timeLiftStream q s a j) x =
      liftJet q s a (x 1) (x 0 + tortoise (x 1)) ![x 2, x 3] j := by
  have hy1 : 0 < ingoingPoint x 1 := by simp [ingoingPoint]; linarith
  have hy3 : 0 < ingoingPoint x 3 := by simpa [ingoingPoint] using hY
  rw [timeLiftStream_eq_comp, ofField_ingoing_comp hr
    (ingoingLiftStream_contDiffAt q s a j hy1 hy3), ofField_ingoingLiftStream q s a j hy1 hy3]
  have h0 : ingoingPoint x 0 = x 0 + tortoise (x 1) := rfl
  have h1 : ingoingPoint x 1 = x 1 := rfl
  have h2 : ingoingPoint x 2 = x 2 := rfl
  have h3 : ingoingPoint x 3 = x 3 := rfl
  simp only [h0, h1, h2, h3]
  have hv : (angularJets q ![x 2, x 3] j).value = fullSquareCovector q j ![x 2, x 3] := rfl
  ext k l
  · simp only [D4BMIngoingFullCurrent.toStatic, mul, liftJet, separatedJet, hv]
  · fin_cases k <;>
      simp only [D4BMIngoingFullCurrent.toStatic, mul, liftJet, separatedJet, hv, Fin.isValue,
        Fin.reduceFinMk, Fin.reduceEq, if_true, if_false, Matrix.cons_val, Matrix.cons_val_zero,
        Matrix.cons_val_one, mul_zero, zero_mul, add_zero, zero_add]
    ring
  · fin_cases k <;> fin_cases l <;>
      simp only [D4BMIngoingFullCurrent.toStatic, mul, liftJet, separatedJet, hv, Fin.isValue,
        Fin.reduceFinMk, Fin.reduceEq, if_true, if_false, and_true, true_and, and_false,
        false_and, and_self, Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one,
        mul_zero, zero_mul, add_zero, zero_add] <;> ring

/-- **Reconstructed metric action of two time-lift streams.**  At every exterior point the actual
ingoing Einstein action current of the metrics reconstructed from `L(s, a)` and `L(t, b)` is the
lift current at `v = t + r_*(r)`. -/
theorem metricIngoingCurrent_timeLiftStream (p : D4BMBackground.ExteriorPoint) (q : XiZeroCopy)
    (s t a b : ℂ) :
    metricIngoingCurrent p (timeLiftStream q s a) (timeLiftStream q t b) =
      liftCurrent q s t a b (p.val 1) (p.val 0 + tortoise (p.val 1)) ![p.val 2, p.val 3] := by
  rw [metricIngoingCurrent_eq _ _ p
    (fun j => timeLiftStream_contDiffAt q s a j p.property.1 p.property.2)
    (fun j => timeLiftStream_contDiffAt q t b j p.property.1 p.property.2)]
  have hs : (fun j => ofField (timeLiftStream q s a j) p.val) =
      liftJet q s a (p.val 1) (p.val 0 + tortoise (p.val 1)) ![p.val 2, p.val 3] :=
    funext fun j => ofField_timeLiftStream q s a j p.property.1 p.property.2
  have ht : (fun j => ofField (timeLiftStream q t b j) p.val) =
      liftJet q t b (p.val 1) (p.val 0 + tortoise (p.val 1)) ![p.val 2, p.val 3] :=
    funext fun j => ofField_timeLiftStream q t b j p.property.1 p.property.2
  rw [hs, ht]
  exact lift_action_current p q s t a b _

/-- Adding the retained source contact to the reconstructed metric action of the two literal
time-lift streams gives the angular master current. -/
theorem metricIngoingCurrent_timeLiftStream_add_contact (p : D4BMBackground.ExteriorPoint)
    (q : XiZeroCopy) (s t a b : ℂ) :
    metricIngoingCurrent p (timeLiftStream q s a) (timeLiftStream q t b) +
        liftContact q s t a b (p.val 1) (p.val 0 + tortoise (p.val 1)) ![p.val 2, p.val 3] =
      liftAngularCurrent q s t a b (p.val 1) (p.val 0 + tortoise (p.val 1))
        ![p.val 2, p.val 3] := by
  rw [metricIngoingCurrent_timeLiftStream, lift_current_add_contact]

end RHTower.D4BMPhysicalLiftCurrent
