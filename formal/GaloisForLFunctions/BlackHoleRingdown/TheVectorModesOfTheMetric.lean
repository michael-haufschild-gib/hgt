import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMStreamMetricField
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMVectorStreamEinstein

/-!
# The vector modes of the metric

Let `Y` be a `C³` function on the upper half plane with `y²ΔY = λY`, and put `V = (∂_y Y, -∂_x Y)`, a
divergence-free covector. With `F = r² - 1`, the perturbation of the metric of the massless topological black hole

`h_{t i} = F e^{wt} f'(r) V_i`,  `h_{r i} = w e^{wt} f(r) V_i / F`

has as its linearized cosmological Einstein tensor exactly the vector master tensor of the corpus. Since
`y²(∂_x² + ∂_y²)V₀ + 2y(∂_y V₀ - ∂_x V₁) = ∂_y(y²ΔY) = λ V₀` and `y²(∂_x²V₁ - ∂_x∂_y V₀) = λ V₁`, it vanishes as soon as
`f` solves the radial master equation `r²F f'' + 2r f' - (w²r²/F + 2) f + λ f = 0`.

With `γ(r) = ½ log(r²-1) - log(2r)`, so that `t + γ` is the hyperboloidal time, two solutions are explicit:
`f = e^{wγ}` for `λ = (w+1)(w+2)` and `f = r e^{wγ}` for `λ = w(w+1)`.
-/

open Complex Filter Topology
open scoped ContDiff

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open _root_.RHTower _root_.RHTower.D4BMHorizon _root_.RHTower.D4BMMetricReconstruction
  _root_.RHTower.D4BMScalarLinearEquation _root_.RHTower.D4BMVectorStream

/-! ### Fields of one coordinate -/

/-- The two-jet of a function of one coordinate. -/
theorem ofField_comp_coord {g : ℝ → ℂ} (k : Fin 4) {x : Fin 4 → ℝ} (hg : ContDiffAt ℝ 2 g (x k)) :
    ofField (fun z => g (z k)) x = ⟨g (x k), fun i => if i = k then deriv g (x k) else 0,
      fun i j => if i = k ∧ j = k then deriv (deriv g) (x k) else 0⟩ := by
  have hproj (z : Fin 4 → ℝ) : HasFDerivAt (fun z : Fin 4 → ℝ => z k)
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) k) z :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 4 => ℝ) k).hasFDerivAt
  have hev : ∀ᶠ t in 𝓝 (x k), ContDiffAt ℝ 2 g t := hg.eventually (by simp)
  have hevz : ∀ᶠ z : Fin 4 → ℝ in 𝓝 x, ContDiffAt ℝ 2 g (z k) :=
    (continuous_apply k).continuousAt.eventually hev
  have hfirst : ∀ j : Fin 4, coordDeriv j (fun z : Fin 4 → ℝ => g (z k)) =ᶠ[𝓝 x]
      fun z => if j = k then deriv g (z k) else 0 := fun j => by
    filter_upwards [hevz] with z hz
    have h1 : HasDerivAt g (deriv g (z k)) (z k) := (hz.differentiableAt (by norm_num)).hasDerivAt
    have h2 := h1.hasFDerivAt.comp z (hproj z)
    change fderiv ℝ (g ∘ fun z : Fin 4 → ℝ => z k) z (Pi.single j 1) = _
    rw [h2.fderiv]
    by_cases hj : j = k
    · subst hj
      simp
    · simp [hj, Ne.symm hj]
  have hd1 : ContDiffAt ℝ 1 (deriv g) (x k) := by
    have h := (hg.fderiv_right (m := 1) (by norm_num)).clm_apply
      (contDiffAt_const (c := (1 : ℝ)))
    exact h.congr_of_eventuallyEq (Eventually.of_forall fun t => (fderiv_apply_one_eq_deriv).symm)
  have hd2 : HasDerivAt (deriv g) (deriv (deriv g) (x k)) (x k) :=
    (hd1.differentiableAt (by norm_num)).hasDerivAt
  ext i j
  · rfl
  · exact (hfirst i).self_of_nhds
  · change fderiv ℝ (coordDeriv j (fun z : Fin 4 → ℝ => g (z k))) x (Pi.single i 1) = _
    rw [(hfirst j).fderiv_eq]
    by_cases hj : j = k
    · subst hj
      have h2 := hd2.hasFDerivAt.comp x (hproj x)
      have h3 : (fun z : Fin 4 → ℝ => if j = j then deriv g (z j) else 0) =
          deriv g ∘ fun z : Fin 4 → ℝ => z j := by
        funext z
        simp
      rw [h3, h2.fderiv]
      by_cases hi : i = j
      · subst hi
        simp
      · simp [hi, Ne.symm hi]
    · have h3 : (fun z : Fin 4 → ℝ => if j = k then deriv g (z k) else 0) = fun _ => 0 := by
        funext z
        simp [hj]
      rw [h3]
      simp [hj]

theorem hasDerivAt_exp_real_mul (w : ℂ) (s : ℝ) :
    HasDerivAt (fun s : ℝ => Complex.exp (w * s)) (w * Complex.exp (w * s)) s := by
  have h := (((hasDerivAt_id s).ofReal_comp).const_mul w).cexp
  simpa [mul_comm] using h

/-- The separated field `e^{wt} g(r)`. -/
def timeRadial (w : ℂ) (g : ℝ → ℂ) (x : Fin 4 → ℝ) : ℂ := Complex.exp (w * x 0) * g (x 1)

theorem contDiff_exp_real_mul (w : ℂ) {n : WithTop ℕ∞} :
    ContDiff ℝ n fun s : ℝ => Complex.exp (w * s) :=
  (contDiff_const.mul Complex.ofRealCLM.contDiff).cexp

theorem contDiffAt_timeRadial (w : ℂ) {g : ℝ → ℂ} {x : Fin 4 → ℝ} (hg : ContDiffAt ℝ 2 g (x 1)) :
    ContDiffAt ℝ 2 (timeRadial w g) x := by
  have h1 : ContDiffAt ℝ 2 (fun z : Fin 4 → ℝ => Complex.exp (w * z 0)) x :=
    (contDiff_exp_real_mul w).contDiffAt.comp x (contDiff_apply ℝ ℝ 0).contDiffAt
  have h2 : ContDiffAt ℝ 2 (fun z : Fin 4 → ℝ => g (z 1)) x :=
    hg.comp x (contDiff_apply ℝ ℝ 1).contDiffAt
  exact h1.mul h2

/-- **The jet of a separated field** is the corpus radial jet. -/
theorem timeRadial_jet (w : ℂ) {g : ℝ → ℂ} {x : Fin 4 → ℝ} (hg : ContDiffAt ℝ 2 g (x 1)) :
    ofField (timeRadial w g) x = radialJet w (timeRadial w g x)
      (Complex.exp (w * x 0) * deriv g (x 1)) (Complex.exp (w * x 0) * deriv (deriv g) (x 1)) := by
  have hT1 : deriv (fun s : ℝ => Complex.exp (w * s)) = fun s : ℝ => w * Complex.exp (w * s) :=
    funext fun s => (hasDerivAt_exp_real_mul w s).deriv
  have hT2 : deriv (fun s : ℝ => w * Complex.exp (w * s)) =
      fun s : ℝ => w * (w * Complex.exp (w * s)) :=
    funext fun s => ((hasDerivAt_exp_real_mul w s).const_mul w).deriv
  have h1 : ContDiffAt ℝ 2 (fun s : ℝ => Complex.exp (w * s)) (x 0) :=
    (contDiff_exp_real_mul w).contDiffAt
  have hA := ofField_comp_coord 0 h1
  have hB := ofField_comp_coord 1 hg
  have hAc : ContDiffAt ℝ 2 (fun z : Fin 4 → ℝ => Complex.exp (w * z 0)) x :=
    (contDiff_exp_real_mul w).contDiffAt.comp x (contDiff_apply ℝ ℝ 0).contDiffAt
  have hBc : ContDiffAt ℝ 2 (fun z : Fin 4 → ℝ => g (z 1)) x :=
    hg.comp x (contDiff_apply ℝ ℝ 1).contDiffAt
  have hmul := ofField_mul hAc hBc
  change ofField (fun z => Complex.exp (w * z 0) * g (z 1)) x = _
  rw [hmul, hA, hB, hT1, hT2]
  ext i j
  · rfl
  · fin_cases i <;> simp [ScalarTwoJet.mul, radialJet, timeRadial]
    all_goals ring
  · fin_cases i <;> fin_cases j <;> simp [ScalarTwoJet.mul, radialJet, timeRadial]
    all_goals ring

/-! ### The vector field -/

/-- The temporal block `F e^{wt} f'(r)`. -/
def vectorTimeBlock (w : ℂ) (f : ℝ → ℂ) (x : Fin 4 → ℝ) : ℂ :=
  ((x 1 : ℂ) * (x 1 : ℂ) + (-1)) * timeRadial w (deriv f) x

/-- The radial block `w e^{wt} f(r) / F`. -/
def vectorRadiusBlock (w : ℂ) (f : ℝ → ℂ) (x : Fin 4 → ℝ) : ℂ :=
  (w * timeRadial w f x) * ((x 1 : ℂ) * (x 1 : ℂ) + (-1))⁻¹

/-- **The vector perturbation** of the metric. -/
def vectorMetricField (w : ℂ) (f : ℝ → ℂ) (V : Covector) (x : Fin 4 → ℝ) :
    Matrix (Fin 4) (Fin 4) ℂ :=
  let T := vectorTimeBlock w f x
  let R := vectorRadiusBlock w f x
  let A := V 0 (angularPoint x)
  let C := V 1 (angularPoint x)
  !![0,0,T*A,T*C; 0,0,R*A,R*C; T*A,R*A,0,0; T*C,R*C,0,0]

section Jets

variable (w : ℂ) {f : ℝ → ℂ} (V : Covector) (p : D4BMBackground.ExteriorPoint)

theorem factor_ne_zero' : (p.val 1 : ℂ) * (p.val 1 : ℂ) + (-1) ≠ 0 := by
  have h : (p.val 1 : ℂ) ^ (2 : ℕ) - 1 ≠ 0 := by
    exact_mod_cast (by nlinarith [p.property.1] : (p.val 1) ^ (2 : ℕ) - 1 ≠ 0)
  simpa only [← pow_two, ← sub_eq_add_neg] using h

private theorem radius_smooth' : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => (x 1 : ℂ)) p.val :=
  (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).contDiffAt

private theorem factor_smooth' :
    ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => (x 1 : ℂ) * (x 1 : ℂ) + (-1)) p.val :=
  ((radius_smooth' p).mul (radius_smooth' p)).add contDiffAt_const

/-- The first derivative of a `C³` function is `C²`. -/
theorem contDiffAt_deriv_two {f : ℝ → ℂ} {r : ℝ} (hf : ContDiffAt ℝ 3 f r) :
    ContDiffAt ℝ 2 (deriv f) r := by
  have h := (hf.fderiv_right (m := 2) (by norm_num)).clm_apply (contDiffAt_const (c := (1 : ℝ)))
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun t => (fderiv_apply_one_eq_deriv).symm)

private def assemble' (J : Matrix (Fin 4) (Fin 4) (ScalarTwoJet (Fin 4) ℂ)) :
    CoordinateMetricTwoJet 4 ℂ :=
  ⟨fun i j => (J i j).value, fun k i j => (J i j).first k, fun k l i j => (J i j).second k l⟩

variable {p} in
/-- The values entering the jet. -/
def radialValue (w : ℂ) (f : ℝ → ℂ) (x : Fin 4 → ℝ) (n : ℕ) : ℂ :=
  Complex.exp (w * x 0) * (deriv^[n] f) (x 1)

/-- **The jet of the vector perturbation** is the corpus table. -/
theorem vectorMetricField_jet (hf : ContDiffAt ℝ 3 f (p.val 1))
    (hV : ∀ k, ContDiffAt ℝ 2 (V k) (angularPoint p.val))
    (hD : ∀ z, 0 < z 1 → divergence V z = 0) :
    ofMetricField (vectorMetricField w f V) p.val =
      D4BMVectorStream.metricJet w (p.val 1) (radialValue w f p.val 0) (radialValue w f p.val 1)
        (radialValue w f p.val 2) (radialValue w f p.val 3)
        (V 0 (angularPoint p.val)) (V 1 (angularPoint p.val))
        (coordDeriv 0 (V 0) (angularPoint p.val)) (coordDeriv 1 (V 0) (angularPoint p.val))
        (coordDeriv 0 (V 1) (angularPoint p.val))
        (coordDeriv 0 (coordDeriv 0 (V 0)) (angularPoint p.val))
        (coordDeriv 0 (coordDeriv 1 (V 0)) (angularPoint p.val))
        (coordDeriv 0 (coordDeriv 0 (V 1)) (angularPoint p.val))
        (coordDeriv 1 (coordDeriv 1 (V 0)) (angularPoint p.val)) := by
  have hf2 : ContDiffAt ℝ 2 f (p.val 1) := hf.of_le (by norm_num)
  have hf1 : ContDiffAt ℝ 2 (deriv f) (p.val 1) := contDiffAt_deriv_two hf
  have hR := radius_smooth' p
  have hF := factor_smooth' p
  have hjR : ofField (fun x : Fin 4 → ℝ => (x 1 : ℂ)) p.val = coord (p.val 1) 1 :=
    D4BMFundamentalScalarMetric.coordinate_jet p.val 1
  have hjF : ofField (fun x : Fin 4 → ℝ => (x 1 : ℂ) * (x 1 : ℂ) + (-1)) p.val =
      ((coord (p.val 1) 1).mul (coord (p.val 1) 1)).add (constant (-1)) := by
    rw [ofField_add (hR.mul hR) contDiffAt_const, ofField_mul hR hR, ofField_constant, hjR]
  have hE := contDiffAt_timeRadial w hf2
  have hE1 := contDiffAt_timeRadial w hf1
  have hFi : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => ((x 1 : ℂ) * (x 1 : ℂ) + (-1))⁻¹) p.val :=
    hF.inv (factor_ne_zero' p)
  have hT : ContDiffAt ℝ 2 (vectorTimeBlock w f) p.val := hF.mul hE1
  have hRad : ContDiffAt ℝ 2 (vectorRadiusBlock w f) p.val := (contDiffAt_const.mul hE).mul hFi
  have hjT : ofField (vectorTimeBlock w f) p.val =
      (((coord (p.val 1) 1).mul (coord (p.val 1) 1)).add (constant (-1))).mul
        (radialJet w (radialValue w f p.val 1) (radialValue w f p.val 2)
          (radialValue w f p.val 3)) := by
    unfold vectorTimeBlock
    rw [ofField_mul hF hE1, hjF, timeRadial_jet w hf1]
    rfl
  have hjRad : ofField (vectorRadiusBlock w f) p.val =
      ((constant w).mul (radialJet w (radialValue w f p.val 0) (radialValue w f p.val 1)
        (radialValue w f p.val 2))).mul
        (((coord (p.val 1) 1).mul (coord (p.val 1) 1)).add (constant (-1))).inv := by
    unfold vectorRadiusBlock
    rw [ofField_mul ((contDiffAt_const (c := w)).mul hE) hFi,
      ofField_mul (contDiffAt_const (c := w)) hE, ofField_constant,
      ofField_inv hF (factor_ne_zero' p), hjF, timeRadial_jet w hf2]
    rfl
  have hu : ContDiff ℝ 2 angularPoint := by
    apply contDiff_pi.mpr
    intro k
    fin_cases k <;> exact contDiff_apply ℝ ℝ _
  have hLift (k : Fin 2) : ContDiffAt ℝ 2 (fun x => V k (angularPoint x)) p.val :=
    (hV k).comp p.val hu.contDiffAt
  have ht (k : Fin 2) := ofField_mul hT (hLift k)
  have hr (k : Fin 2) := ofField_mul hRad (hLift k)
  simp_rw [hjT, _root_.RHTower.D4BMModularCore.streamAngularJet_actual V p hV hD] at ht
  simp_rw [hjRad, _root_.RHTower.D4BMModularCore.streamAngularJet_actual V p hV hD] at hr
  change assemble' _ = assemble' _
  congr 1
  funext i j
  fin_cases i <;> fin_cases j
  all_goals first | exact ofField_constant 0 p.val | exact ht 0 | exact ht 1 | exact hr 0 | exact hr 1

/-- **The Einstein tensor of the vector perturbation** is the corpus master tensor. -/
theorem vectorMetricField_einstein (hf : ContDiffAt ℝ 3 f (p.val 1))
    (hV : ∀ k, ContDiffAt ℝ 2 (V k) (angularPoint p.val))
    (hD : ∀ z, 0 < z 1 → divergence V z = 0) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet (p.val 1) (p.val 3))
      (ofMetricField (vectorMetricField w f V) p.val) (-3) i j =
    sourceTensor w (p.val 1) (p.val 3) (radialValue w f p.val 0) (radialValue w f p.val 1)
      (radialValue w f p.val 2) (radialValue w f p.val 3)
      (V 0 (angularPoint p.val)) (V 1 (angularPoint p.val))
      (coordDeriv 1 (V 0) (angularPoint p.val)) (coordDeriv 0 (V 1) (angularPoint p.val))
      (coordDeriv 0 (coordDeriv 0 (V 0)) (angularPoint p.val))
      (coordDeriv 0 (coordDeriv 1 (V 0)) (angularPoint p.val))
      (coordDeriv 0 (coordDeriv 0 (V 1)) (angularPoint p.val))
      (coordDeriv 1 (coordDeriv 1 (V 0)) (angularPoint p.val)) i j := by
  have hr : (p.val 1 : ℂ) ≠ 0 := by exact_mod_cast (by linarith [p.property.1] : p.val 1 ≠ 0)
  have hy : (p.val 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr p.property.2.ne'
  have hF : (p.val 1 : ℂ) ^ (2 : ℕ) - 1 ≠ 0 := by
    exact_mod_cast (by nlinarith [p.property.1] : (p.val 1) ^ (2 : ℕ) - 1 ≠ 0)
  rw [vectorMetricField_jet w V p hf hV hD]
  exact cosmological_component _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hr hy hF i j

/-- The master tensor vanishes when the angular operator acts by `λ` and the radial master equation holds. -/
theorem sourceTensor_eq_zero {r y H H1 H2 H3 A C Q R U V W Z lam : ℂ}
    (hD0 : y ^ (2 : ℕ) * (U + Z) + 2 * y * (Q - R) = lam * A)
    (hD1 : y ^ (2 : ℕ) * (W - V) = lam * C)
    (hm : r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1) * H2 + 2 * r * H1 -
      (w ^ (2 : ℕ) * r ^ (2 : ℕ) / (r ^ (2 : ℕ) - 1) + 2) * H + lam * H = 0)
    (hm1 : r ^ (2 : ℕ) * (r ^ (2 : ℕ) - 1) * H3 + 4 * r ^ (3 : ℕ) * H2 -
      w ^ (2 : ℕ) * r ^ (2 : ℕ) / (r ^ (2 : ℕ) - 1) * H1 +
      2 * w ^ (2 : ℕ) * r / (r ^ (2 : ℕ) - 1) ^ (2 : ℕ) * H + lam * H1 = 0) (i j : Fin 4) :
    sourceTensor w r y H H1 H2 H3 A C Q R U V W Z i j = 0 := by
  have h0 : ∀ B D : ℂ, D = lam * B → master w r H H1 H2 B D = 0 := fun B D hD => by
    rw [master, hD]
    linear_combination B * hm
  have h1 : ∀ B D : ℂ, D = lam * B → masterFirst w r H H1 H2 H3 B D = 0 := fun B D hD => by
    rw [masterFirst, hD]
    linear_combination B * hm1
  fin_cases i <;> fin_cases j <;>
    simp [sourceTensor, h0 _ _ hD0, h0 _ _ hD1, h1 _ _ hD0, h1 _ _ hD1]

end Jets

/-! ### Covectors from eigenfunctions -/

/-- The divergence-free covector `V = (∂_y Y, -∂_x Y)` of a scalar. -/
def gradCovector (Y : Field) : Covector := ![coordDeriv 1 Y, fun z => -coordDeriv 0 Y z]

section Angular

variable {Y : Field}

theorem contDiffAt_coordDeriv {n : ℕ} {z : Point} (hY : ContDiffAt ℝ (n + 1 : ℕ) Y z) (k : Fin 2) :
    ContDiffAt ℝ n (coordDeriv k Y) z := by
  have h := (hY.fderiv_right (m := n) (by norm_cast)).clm_apply
    (contDiffAt_const (c := (Pi.single k 1 : Point)))
  exact h

theorem contDiffAt_gradCovector {z : Point} (hY : ContDiffAt ℝ (3 : ℕ) Y z) (k : Fin 2) :
    ContDiffAt ℝ 2 (gradCovector Y k) z := by
  have h0 := contDiffAt_coordDeriv (n := 2) hY 0
  have h1 := contDiffAt_coordDeriv (n := 2) hY 1
  fin_cases k
  · exact h1
  · exact h0.neg

/-- **`V` is divergence-free.** -/
theorem divergence_gradCovector (hY : ∀ z : Point, 0 < z 1 → ContDiffAt ℝ (3 : ℕ) Y z) :
    ∀ z : Point, 0 < z 1 → divergence (gradCovector Y) z = 0 := fun z hz => by
  rw [divergence_eq _ z hz]
  have hc := coordDeriv_commute ((hY z hz).of_le (by norm_num)) 1 0
  have h0 : coordDeriv 0 (gradCovector Y 0) z = coordDeriv 0 (coordDeriv 1 Y) z := rfl
  have h1 : coordDeriv 1 (gradCovector Y 1) z = -coordDeriv 1 (coordDeriv 0 Y) z := by
    change coordDeriv 1 (fun z => -coordDeriv 0 Y z) z = _
    rw [coordDeriv, fderiv_fun_neg]
    rfl
  rw [h0, h1, hc]
  ring

/-- **The eigenvalue equation differentiated.** -/
theorem coordDeriv_eigen (hY : ∀ z : Point, 0 < z 1 → ContDiffAt ℝ (3 : ℕ) Y z) {lam : ℂ}
    (hL : ∀ z : Point, 0 < z 1 → (z 1 : ℂ) ^ (2 : ℕ) *
      (coordDeriv 0 (coordDeriv 0 Y) z + coordDeriv 1 (coordDeriv 1 Y) z) = lam * Y z)
    {z : Point} (hz : 0 < z 1) (k : Fin 2) :
    (if k = 1 then 2 * (z 1 : ℂ) else 0) *
        (coordDeriv 0 (coordDeriv 0 Y) z + coordDeriv 1 (coordDeriv 1 Y) z) +
      (z 1 : ℂ) ^ (2 : ℕ) * (coordDeriv k (coordDeriv 0 (coordDeriv 0 Y)) z +
        coordDeriv k (coordDeriv 1 (coordDeriv 1 Y)) z) = lam * coordDeriv k Y z := by
  have h3 := hY z hz
  have h00 : ContDiffAt ℝ 1 (coordDeriv 0 (coordDeriv 0 Y)) z :=
    contDiffAt_coordDeriv (n := 1) (contDiffAt_coordDeriv (n := 2) h3 0) 0
  have h11 : ContDiffAt ℝ 1 (coordDeriv 1 (coordDeriv 1 Y)) z :=
    contDiffAt_coordDeriv (n := 1) (contDiffAt_coordDeriv (n := 2) h3 1) 1
  have hd0 := (h00.differentiableAt (by norm_num)).hasFDerivAt
  have hd1 := (h11.differentiableAt (by norm_num)).hasFDerivAt
  have hdY := (h3.differentiableAt (by norm_num)).hasFDerivAt
  have hcoord : HasFDerivAt (fun w : Point => (w 1 : ℂ))
      (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)) z :=
    (Complex.ofRealCLM.comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) 1)).hasFDerivAt
  have hprod := (hcoord.mul hcoord).mul (hd0.add hd1)
  have he : (fun w : Point => (w 1 : ℂ) * (w 1 : ℂ) *
      (coordDeriv 0 (coordDeriv 0 Y) w + coordDeriv 1 (coordDeriv 1 Y) w)) =ᶠ[𝓝 z]
      fun w => lam * Y w := by
    filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
    rw [← pow_two]
    exact hL w hw
  have hrhs := hdY.const_mul lam
  have hder := congrArg (fun a => a (Pi.single k 1))
    ((hprod.congr_of_eventuallyEq he.symm).fderiv.symm.trans hrhs.fderiv)
  have hk : (Pi.single k (1 : ℝ) : Point) 1 = if k = 1 then 1 else 0 := by
    by_cases h : k = 1
    · subst h
      simp
    · simp [h, Ne.symm h]
  simp only [add_apply, smul_apply, smul_eq_mul,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply, hk,
    Pi.mul_apply, Pi.add_apply] at hder
  by_cases h : k = 1
  · subst h
    simp only [if_true, ofReal_one] at hder ⊢
    simp only [coordDeriv] at hder ⊢
    linear_combination hder
  · simp only [h, if_false, ofReal_zero] at hder ⊢
    simp only [coordDeriv] at hder ⊢
    linear_combination hder

/-- **The angular operator acts by `λ`, first component.** -/
theorem angular_zero (hY : ∀ z : Point, 0 < z 1 → ContDiffAt ℝ (3 : ℕ) Y z) {lam : ℂ}
    (hL : ∀ z : Point, 0 < z 1 → (z 1 : ℂ) ^ (2 : ℕ) *
      (coordDeriv 0 (coordDeriv 0 Y) z + coordDeriv 1 (coordDeriv 1 Y) z) = lam * Y z)
    {z : Point} (hz : 0 < z 1) :
    (z 1 : ℂ) ^ (2 : ℕ) * (coordDeriv 0 (coordDeriv 0 (gradCovector Y 0)) z +
        coordDeriv 1 (coordDeriv 1 (gradCovector Y 0)) z) +
      2 * (z 1 : ℂ) * (coordDeriv 1 (gradCovector Y 0) z - coordDeriv 0 (gradCovector Y 1) z) =
    lam * gradCovector Y 0 z := by
  have h3 := hY z hz
  have hE := coordDeriv_eigen hY hL hz 1
  simp only [if_true] at hE
  have hg0 : gradCovector Y 0 = coordDeriv 1 Y := rfl
  have hg1 : gradCovector Y 1 = fun z => -coordDeriv 0 Y z := rfl
  have hneg : coordDeriv 0 (fun z => -coordDeriv 0 Y z) z = -coordDeriv 0 (coordDeriv 0 Y) z := by
    rw [coordDeriv, fderiv_fun_neg]
    rfl
  -- commute the third derivative
  have hc1 : coordDeriv 1 (coordDeriv 0 (coordDeriv 0 Y)) z =
      coordDeriv 0 (coordDeriv 1 (coordDeriv 0 Y)) z :=
    coordDeriv_commute (contDiffAt_coordDeriv (n := 2) h3 0) 1 0
  have hc2 : coordDeriv 0 (coordDeriv 1 (coordDeriv 0 Y)) z =
      coordDeriv 0 (coordDeriv 0 (coordDeriv 1 Y)) z := by
    have hev : coordDeriv 1 (coordDeriv 0 Y) =ᶠ[𝓝 z] coordDeriv 0 (coordDeriv 1 Y) := by
      filter_upwards [(isOpen_lt continuous_const (continuous_apply 1)).mem_nhds hz] with w hw
      exact coordDeriv_commute ((hY w hw).of_le (by norm_num)) 1 0
    change fderiv ℝ _ z _ = fderiv ℝ _ z _
    rw [hev.fderiv_eq]
  rw [hg0, hg1, hneg]
  rw [hc1, hc2] at hE
  linear_combination hE

/-- **The angular operator acts by `λ`, second component.** -/
theorem angular_one (hY : ∀ z : Point, 0 < z 1 → ContDiffAt ℝ (3 : ℕ) Y z) {lam : ℂ}
    (hL : ∀ z : Point, 0 < z 1 → (z 1 : ℂ) ^ (2 : ℕ) *
      (coordDeriv 0 (coordDeriv 0 Y) z + coordDeriv 1 (coordDeriv 1 Y) z) = lam * Y z)
    {z : Point} (hz : 0 < z 1) :
    (z 1 : ℂ) ^ (2 : ℕ) * (coordDeriv 0 (coordDeriv 0 (gradCovector Y 1)) z -
        coordDeriv 0 (coordDeriv 1 (gradCovector Y 0)) z) = lam * gradCovector Y 1 z := by
  have h3 := hY z hz
  have hE := coordDeriv_eigen hY hL hz 0
  simp only [Fin.isValue, zero_ne_one, if_false, zero_mul, zero_add] at hE
  have hg0 : gradCovector Y 0 = coordDeriv 1 Y := rfl
  have hg1 : gradCovector Y 1 = fun z => -coordDeriv 0 Y z := rfl
  have hneg : coordDeriv 0 (fun z => -coordDeriv 0 Y z) = fun w => -coordDeriv 0 (coordDeriv 0 Y) w := by
    funext w
    rw [coordDeriv, fderiv_fun_neg]
    rfl
  have hneg2 : coordDeriv 0 (fun w => -coordDeriv 0 (coordDeriv 0 Y) w) z =
      -coordDeriv 0 (coordDeriv 0 (coordDeriv 0 Y)) z := by
    rw [coordDeriv, fderiv_fun_neg]
    rfl
  rw [hg0, hg1, hneg, hneg2]
  simp only
  linear_combination -hE

end Angular

/-- **Every eigenfunction carries a vacuum vector perturbation.** -/
theorem vectorMetricField_vacuum (w : ℂ) {f : ℝ → ℂ} {Y : Field} {lam : ℂ}
    (hY : ∀ z : Point, 0 < z 1 → ContDiffAt ℝ (3 : ℕ) Y z)
    (hL : ∀ z : Point, 0 < z 1 → (z 1 : ℂ) ^ (2 : ℕ) *
      (coordDeriv 0 (coordDeriv 0 Y) z + coordDeriv 1 (coordDeriv 1 Y) z) = lam * Y z)
    (p : D4BMBackground.ExteriorPoint) (hf : ContDiffAt ℝ 3 f (p.val 1))
    (hm : ((p.val 1 : ℝ) : ℂ) ^ (2 : ℕ) * (((p.val 1 : ℝ) : ℂ) ^ (2 : ℕ) - 1) * deriv (deriv f) (p.val 1) +
      2 * ((p.val 1 : ℝ) : ℂ) * deriv f (p.val 1) -
      (w ^ (2 : ℕ) * ((p.val 1 : ℝ) : ℂ) ^ (2 : ℕ) / (((p.val 1 : ℝ) : ℂ) ^ (2 : ℕ) - 1) + 2) * f (p.val 1) +
      lam * f (p.val 1) = 0)
    (hm1 : ((p.val 1 : ℝ) : ℂ) ^ (2 : ℕ) * (((p.val 1 : ℝ) : ℂ) ^ (2 : ℕ) - 1) * deriv (deriv (deriv f)) (p.val 1) +
      4 * ((p.val 1 : ℝ) : ℂ) ^ (3 : ℕ) * deriv (deriv f) (p.val 1) -
      w ^ (2 : ℕ) * ((p.val 1 : ℝ) : ℂ) ^ (2 : ℕ) / (((p.val 1 : ℝ) : ℂ) ^ (2 : ℕ) - 1) * deriv f (p.val 1) +
      2 * w ^ (2 : ℕ) * ((p.val 1 : ℝ) : ℂ) / (((p.val 1 : ℝ) : ℂ) ^ (2 : ℕ) - 1) ^ (2 : ℕ) * f (p.val 1) +
      lam * deriv f (p.val 1) = 0) (i j : Fin 4) :
    CoordinateMetricTwoJet.Linearization.cosmological (D4BMBackground.jet (p.val 1) (p.val 3))
      (ofMetricField (vectorMetricField w f (gradCovector Y)) p.val) (-3) i j = 0 := by
  have hz : 0 < angularPoint p.val 1 := p.property.2
  have hV : ∀ k, ContDiffAt ℝ 2 (gradCovector Y k) (angularPoint p.val) := fun k =>
    contDiffAt_gradCovector (hY _ hz) k
  rw [vectorMetricField_einstein w _ p hf hV (divergence_gradCovector hY)]
  have hyy : (p.val 3 : ℂ) = ((angularPoint p.val 1 : ℝ) : ℂ) := rfl
  refine sourceTensor_eq_zero w (lam := lam) ?_ ?_ ?_ ?_ i j
  · rw [hyy]
    exact angular_zero hY hL hz
  · rw [hyy]
    exact angular_one hY hL hz
  · simp only [radialValue, Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    linear_combination Complex.exp (w * p.val 0) * hm
  · simp only [radialValue, Function.iterate_succ, Function.iterate_zero, Function.comp_apply, id]
    linear_combination Complex.exp (w * p.val 0) * hm1

end GaloisForLFunctions.BlackHoleRingdown

end
