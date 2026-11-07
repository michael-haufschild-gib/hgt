import GaloisForLFunctions.BlackHoleRingdown.TheLinearityOfTheEinsteinOperator
import GaloisForLFunctions.BlackHoleRingdown.TheGravitationalModesOfTheZeros
import GaloisForLFunctions.BlackHoleRingdown.TheImageFieldOfAPulse

/-!
# The metric of a row

Let `s(z) = y/|cz+d|²` be the height of an image, `σ = (∂_y s, -∂_x s)` its rotated gradient, and
`S = t + γ(r) + log s`, with `γ(r) = ½ log(r²-1) - log(2r)`. For every `C³` function `m : ℝ → ℂ` the perturbation

`h_{t i} = σ_i (F m(S) + m'(S))`,  `h_{r i} = σ_i (r/F) m'(S)`,  `F = r² - 1`,

solves the vacuum linearized Einstein equations of the massless topological black hole, with no separation of
variables and no decay of `m`.

For `m = a e^{wS}` this is the separated vector mode of `y²ΔY = w(w+1) Y` with `Y = a s^{w+1}/(w+1)`. The general
case follows by interpolation: the two-jet of the perturbation at a point depends only on the values of `m, m', m'', m'''`
at one point, and four exponentials `e^{jS}`, `j = 0, 1, 2, 3`, realize any such values by Vandermonde.
-/

open Complex Filter Topology
open scoped ContDiff BigOperators

noncomputable section

namespace GaloisForLFunctions.BlackHoleRingdown

open GaloisForLFunctions.HTGeometry GaloisForLFunctions.HTGeometry.ScalarTwoJet
open _root_.RHTower _root_.RHTower.D4BMHorizon _root_.RHTower.D4BMMetricReconstruction

/-! ### The chain rule for jets -/

theorem contDiffAt_deriv_one {g : ℝ → ℂ} {r : ℝ} (hg : ContDiffAt ℝ 2 g r) :
    ContDiffAt ℝ 1 (deriv g) r := by
  have h := (hg.fderiv_right (m := 1) (by norm_num)).clm_apply (contDiffAt_const (c := (1 : ℝ)))
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun t => (fderiv_apply_one_eq_deriv).symm)

/-- **The two-jet of a composition with a real field.** -/
theorem ofField_comp_real {g : ℝ → ℂ} {S : (Fin 4 → ℝ) → ℝ} {p : Fin 4 → ℝ}
    (hg : ContDiffAt ℝ 2 g (S p)) (hS : ContDiffAt ℝ 2 S p) :
    ofField (fun x => g (S x)) p = ⟨g (S p), fun i => (fderiv ℝ S p (Pi.single i 1)) • deriv g (S p),
      fun i j => (fderiv ℝ S p (Pi.single j 1)) • ((fderiv ℝ S p (Pi.single i 1)) • deriv (deriv g) (S p)) +
        (fderiv ℝ (fun x => fderiv ℝ S x (Pi.single j 1)) p (Pi.single i 1)) • deriv g (S p)⟩ := by
  have hev1 : ∀ᶠ x in 𝓝 p, ContDiffAt ℝ 2 S x := hS.eventually (by simp)
  have hev2 : ∀ᶠ x in 𝓝 p, ContDiffAt ℝ 2 g (S x) :=
    hS.continuousAt.eventually (hg.eventually (by simp))
  have hfirst : ∀ j : Fin 4, coordDeriv j (fun x => g (S x)) =ᶠ[𝓝 p]
      fun x => (fderiv ℝ S x (Pi.single j 1)) • deriv g (S x) := fun j => by
    filter_upwards [hev1, hev2] with x h1 h2
    have hd := ((h2.differentiableAt (by norm_num)).hasDerivAt).hasFDerivAt.comp x
      ((h1.differentiableAt (by norm_num)).hasFDerivAt)
    change fderiv ℝ (g ∘ S) x (Pi.single j 1) = _
    rw [hd.fderiv]
    simp
  have hDj : ∀ j : Fin 4, HasFDerivAt (fun x => fderiv ℝ S x (Pi.single j 1))
      (fderiv ℝ (fun x => fderiv ℝ S x (Pi.single j 1)) p) p := fun j =>
    (((hS.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt
      (by norm_num)).hasFDerivAt
  have hdg := (((contDiffAt_deriv_one hg).differentiableAt (by norm_num)).hasDerivAt).hasFDerivAt.comp p
    ((hS.differentiableAt (by norm_num)).hasFDerivAt)
  ext i j
  · rfl
  · exact (hfirst i).self_of_nhds
  · change fderiv ℝ (coordDeriv j (fun x => g (S x))) p (Pi.single i 1) = _
    have hprod : HasFDerivAt (fun x => (fderiv ℝ S x (Pi.single j 1)) • deriv g (S x)) _ p :=
      (hDj j).smul hdg
    rw [(hfirst j).fderiv_eq, hprod.fderiv]
    simp

/-! ### The row data -/

/-- The rotated gradient of the height. -/
def rowSigma (c d : ℝ) (i : Fin 2) (x : Fin 4 → ℝ) : ℝ :=
  if i = 0 then rowHgtY c d (x 2) (x 3) else -rowHgtX c d (x 2) (x 3)

/-- The phase `S = t + γ(r) + log s`. -/
def rowS (c d : ℝ) (x : Fin 4 → ℝ) : ℝ :=
  x 0 + radialPhase (x 1) + Real.log (rowHgt c d (x 2) (x 3))

/-- The factor `r² - 1`. -/
def rowF (x : Fin 4 → ℝ) : ℂ := (x 1 : ℂ) * (x 1 : ℂ) + (-1)

/-- The temporal block. -/
def rowT (c d : ℝ) (m m₁ : ℝ → ℂ) (i : Fin 2) (x : Fin 4 → ℝ) : ℂ :=
  (rowSigma c d i x : ℂ) * rowF x * m (rowS c d x) + (rowSigma c d i x : ℂ) * m₁ (rowS c d x)

/-- The radial block. -/
def rowR (c d : ℝ) (m₁ : ℝ → ℂ) (i : Fin 2) (x : Fin 4 → ℝ) : ℂ :=
  (rowSigma c d i x : ℂ) * ((x 1 : ℂ) * (rowF x)⁻¹) * m₁ (rowS c d x)

/-- **The perturbation of a row.** -/
def rowMetric (c d : ℝ) (m m₁ : ℝ → ℂ) (x : Fin 4 → ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![0, 0, rowT c d m m₁ 0 x, rowT c d m m₁ 1 x;
    0, 0, rowR c d m₁ 0 x, rowR c d m₁ 1 x;
    rowT c d m m₁ 0 x, rowR c d m₁ 0 x, 0, 0;
    rowT c d m m₁ 1 x, rowR c d m₁ 1 x, 0, 0]

section Smooth

variable {c d : ℝ} (hden : ∀ x y : ℝ, 0 < y → 0 < rowDen c d x y) (q : D4BMBackground.ExteriorPoint)

include hden

theorem rowHgt_pos' {x y : ℝ} (hy : 0 < y) : 0 < rowHgt c d x y := div_pos hy (hden x y hy)

omit hden in
theorem contDiffAt_rowDen {p : Fin 4 → ℝ} {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun x : Fin 4 → ℝ => rowDen c d (x 2) (x 3)) p := by
  unfold rowDen
  fun_prop

theorem contDiffAt_rowS : ContDiffAt ℝ 2 (rowS c d) q.val := by
  have hr := q.property.1
  have hy := q.property.2
  have hD := hden (q.val 2) (q.val 3) hy
  have hS : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => rowHgt c d (x 2) (x 3)) q.val :=
    ContDiffAt.div (by fun_prop) contDiffAt_rowDen hD.ne'
  have hL := hS.log (rowHgt_pos' hden hy).ne'
  have h2 : ContDiffAt ℝ 2 radialPhase (q.val 1) := by
    exact_mod_cast contDiffAt_infty.mp (contDiffAt_radialPhase hr) 2
  have hP : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => radialPhase (x 1)) q.val :=
    h2.comp q.val (contDiff_apply ℝ ℝ 1).contDiffAt
  exact ((contDiff_apply ℝ ℝ 0).contDiffAt.add hP).add hL

theorem contDiffAt_rowSigma (i : Fin 2) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (fun x : Fin 4 → ℝ => (rowSigma c d i x : ℂ)) q.val := by
  have hy := q.property.2
  have hD := hden (q.val 2) (q.val 3) hy
  have hD2 : ContDiffAt ℝ n (fun x : Fin 4 → ℝ => rowDen c d (x 2) (x 3) ^ 2) q.val :=
    contDiffAt_rowDen.pow 2
  have hne : rowDen c d (q.val 2) (q.val 3) ^ 2 ≠ 0 := pow_ne_zero 2 hD.ne'
  refine Complex.ofRealCLM.contDiff.contDiffAt.comp q.val ?_
  fin_cases i
  · change ContDiffAt ℝ n (fun x : Fin 4 → ℝ => rowSigma c d 0 x) q.val
    simp only [rowSigma, if_true]
    exact ContDiffAt.div (by fun_prop) hD2 hne
  · change ContDiffAt ℝ n (fun x : Fin 4 → ℝ => rowSigma c d 1 x) q.val
    simp only [rowSigma, Fin.isValue, one_ne_zero, if_false]
    exact (ContDiffAt.div (by fun_prop) hD2 hne).neg

omit hden in
theorem contDiffAt_rowF {p : Fin 4 → ℝ} : ContDiffAt ℝ 2 rowF p := by
  have hR : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => (x 1 : ℂ)) p :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).contDiffAt
  exact (hR.mul hR).add contDiffAt_const

omit hden in
theorem rowF_ne : rowF q.val ≠ 0 := factor_ne_zero' q

variable {m m₁ n n₁ : ℝ → ℂ}

theorem contDiffAt_rowT (hm : ContDiffAt ℝ 2 m (rowS c d q.val)) (hm₁ : ContDiffAt ℝ 2 m₁ (rowS c d q.val))
    (i : Fin 2) : ContDiffAt ℝ 2 (rowT c d m m₁ i) q.val :=
  (((contDiffAt_rowSigma hden q i).mul contDiffAt_rowF).mul (hm.comp q.val (contDiffAt_rowS hden q))).add
    ((contDiffAt_rowSigma hden q i).mul (hm₁.comp q.val (contDiffAt_rowS hden q)))

theorem contDiffAt_rowR (hm₁ : ContDiffAt ℝ 2 m₁ (rowS c d q.val)) (i : Fin 2) :
    ContDiffAt ℝ 2 (rowR c d m₁ i) q.val := by
  have hR : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => (x 1 : ℂ)) q.val :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).contDiffAt
  exact ((contDiffAt_rowSigma hden q i).mul (hR.mul (contDiffAt_rowF.inv (rowF_ne q)))).mul
    (hm₁.comp q.val (contDiffAt_rowS hden q))

theorem contDiffAt_rowMetric (hm : ContDiffAt ℝ 2 m (rowS c d q.val))
    (hm₁ : ContDiffAt ℝ 2 m₁ (rowS c d q.val)) (a b : Fin 4) :
    ContDiffAt ℝ 2 (fun x => rowMetric c d m m₁ x a b) q.val := by
  have hT := contDiffAt_rowT hden q hm hm₁
  have hR := contDiffAt_rowR hden q hm₁
  fin_cases a <;> fin_cases b
  all_goals first | exact contDiffAt_const | exact hT 0 | exact hT 1 | exact hR 0 | exact hR 1

/-- **The jet of the perturbation depends only on finitely many derivatives of `m`.** -/
theorem rowMetric_congr_jet (hm : ContDiffAt ℝ 2 m (rowS c d q.val))
    (hm₁ : ContDiffAt ℝ 2 m₁ (rowS c d q.val)) (hn : ContDiffAt ℝ 2 n (rowS c d q.val))
    (hn₁ : ContDiffAt ℝ 2 n₁ (rowS c d q.val))
    (h0 : m (rowS c d q.val) = n (rowS c d q.val))
    (h1 : deriv m (rowS c d q.val) = deriv n (rowS c d q.val))
    (h2 : deriv (deriv m) (rowS c d q.val) = deriv (deriv n) (rowS c d q.val))
    (h3 : m₁ (rowS c d q.val) = n₁ (rowS c d q.val))
    (h4 : deriv m₁ (rowS c d q.val) = deriv n₁ (rowS c d q.val))
    (h5 : deriv (deriv m₁) (rowS c d q.val) = deriv (deriv n₁) (rowS c d q.val)) :
    ofMetricField (rowMetric c d m m₁) q.val = ofMetricField (rowMetric c d n n₁) q.val := by
  have hS := contDiffAt_rowS hden q
  have hjm : ofField (fun x => m (rowS c d x)) q.val = ofField (fun x => n (rowS c d x)) q.val := by
    rw [ofField_comp_real hm hS, ofField_comp_real hn hS, h0, h1, h2]
  have hjm₁ : ofField (fun x => m₁ (rowS c d x)) q.val = ofField (fun x => n₁ (rowS c d x)) q.val := by
    rw [ofField_comp_real hm₁ hS, ofField_comp_real hn₁ hS, h3, h4, h5]
  have hG := fun i => (contDiffAt_rowSigma hden q i (n := 2))
  have hT : ∀ i, ofField (rowT c d m m₁ i) q.val = ofField (rowT c d n n₁ i) q.val := fun i => by
    have e : ∀ (u u₁ : ℝ → ℂ), ContDiffAt ℝ 2 u (rowS c d q.val) → ContDiffAt ℝ 2 u₁ (rowS c d q.val) →
        ofField (rowT c d u u₁ i) q.val =
          (((ofField (fun x => (rowSigma c d i x : ℂ) * rowF x) q.val).mul
            (ofField (fun x => u (rowS c d x)) q.val))).add
          ((ofField (fun x => (rowSigma c d i x : ℂ)) q.val).mul
            (ofField (fun x => u₁ (rowS c d x)) q.val)) := fun u u₁ hu hu₁ => by
      have huS : ContDiffAt ℝ 2 (fun x => u (rowS c d x)) q.val := hu.comp q.val hS
      have hu₁S : ContDiffAt ℝ 2 (fun x => u₁ (rowS c d x)) q.val := hu₁.comp q.val hS
      change ofField (fun x => (rowSigma c d i x : ℂ) * rowF x * u (rowS c d x) +
        (rowSigma c d i x : ℂ) * u₁ (rowS c d x)) q.val = _
      rw [ofField_add (((hG i).mul contDiffAt_rowF).mul huS) ((hG i).mul hu₁S),
        ofField_mul ((hG i).mul contDiffAt_rowF) huS, ofField_mul (hG i) hu₁S]
    rw [e m m₁ hm hm₁, e n n₁ hn hn₁, hjm, hjm₁]
  have hR : ∀ i, ofField (rowR c d m₁ i) q.val = ofField (rowR c d n₁ i) q.val := fun i => by
    have hRr : ContDiffAt ℝ 2 (fun x : Fin 4 → ℝ => (x 1 : ℂ)) q.val :=
      (Complex.ofRealCLM.contDiff.comp (contDiff_apply ℝ ℝ 1)).contDiffAt
    have hC := (hG i).mul (hRr.mul (contDiffAt_rowF.inv (rowF_ne q)))
    have e : ∀ (u₁ : ℝ → ℂ), ContDiffAt ℝ 2 u₁ (rowS c d q.val) →
        ofField (rowR c d u₁ i) q.val =
          (ofField (fun x => (rowSigma c d i x : ℂ) * ((x 1 : ℂ) * (rowF x)⁻¹)) q.val).mul
            (ofField (fun x => u₁ (rowS c d x)) q.val) := fun u₁ hu₁ =>
      ofField_mul hC (hu₁.comp q.val hS)
    rw [e m₁ hm₁, e n₁ hn₁, hjm₁]
  unfold ofMetricField
  congr 1
  funext a b
  fin_cases a <;> fin_cases b
  all_goals first
    | exact (ofField_constant 0 q.val).trans (ofField_constant 0 q.val).symm
    | exact hT 0 | exact hT 1 | exact hR 0 | exact hR 1

end Smooth

/-! ### The potential of an exponential -/

section Potential

variable {c d : ℝ} (hden : ∀ x y : ℝ, 0 < y → 0 < rowDen c d x y) (w a : ℂ)

/-- The potential `a s^{w+1}/(w+1)`. -/
def rowPotential (c d : ℝ) (w a : ℂ) (z : Point) : ℂ :=
  a * (w + 1)⁻¹ * Complex.exp ((w + 1) * ((Real.log (rowHgt c d (z 0) (z 1)) : ℝ) : ℂ))

/-- The factor `a s^w`. -/
def rowQ (c d : ℝ) (w a : ℂ) (x y : ℝ) : ℂ :=
  a * Complex.exp (w * ((Real.log (rowHgt c d x y) : ℝ) : ℂ))

omit hden in
theorem exp_succ_log {s : ℝ} (hs : 0 < s) :
    Complex.exp ((w + 1) * ((Real.log s : ℝ) : ℂ)) =
      Complex.exp (w * ((Real.log s : ℝ) : ℂ)) * (s : ℂ) := by
  have h : (s : ℂ) = Complex.exp ((Real.log s : ℝ) : ℂ) := by
    rw [← Complex.ofReal_exp, Real.exp_log hs]
  conv_rhs => rw [h]
  rw [← Complex.exp_add]
  congr 1
  ring

omit hden in
/-- Differentiating `s^{w+1}` along a curve. -/
theorem hasDerivAt_power (hw : w + 1 ≠ 0) {s : ℝ → ℝ} {s' q : ℝ} (hs : HasDerivAt s s' q)
    (hq : 0 < s q) (a : ℂ) :
    HasDerivAt (fun t => a * (w + 1)⁻¹ * Complex.exp ((w + 1) * ((Real.log (s t) : ℝ) : ℂ)))
      (a * Complex.exp (w * ((Real.log (s q) : ℝ) : ℂ)) * (s' : ℂ)) q := by
  have hl := (hs.log hq.ne').ofReal_comp
  have h := ((hl.const_mul (w + 1)).cexp).const_mul (a * (w + 1)⁻¹)
  refine h.congr_deriv ?_
  rw [exp_succ_log w hq]
  have hsC : (s q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  push_cast
  field_simp

omit hden in
/-- Differentiating `s^w s'` along a curve. -/
theorem hasDerivAt_powerFirst {s s₁ : ℝ → ℝ} {s' s'' q : ℝ} (hs : HasDerivAt s s' q) (hs₁ : HasDerivAt s₁ s'' q)
    (hq : 0 < s q) (hval : s₁ q = s') (a : ℂ) :
    HasDerivAt (fun t => a * Complex.exp (w * ((Real.log (s t) : ℝ) : ℂ)) * (s₁ t : ℂ))
      (a * Complex.exp (w * ((Real.log (s q) : ℝ) : ℂ)) *
        (w * (s' : ℂ) ^ 2 / (s q : ℂ) + (s'' : ℂ))) q := by
  have hl := (hs.log hq.ne').ofReal_comp
  have h := (((hl.const_mul w).cexp).const_mul a).mul hs₁.ofReal_comp
  refine h.congr_deriv ?_
  rw [hval]
  have hsC : (s q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  push_cast
  field_simp

include hden

theorem hasDerivAt_rowPotential_x (hw : w + 1 ≠ 0) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun q : ℝ => rowPotential c d w a ![q, y])
      (rowQ c d w a x y * (rowHgtX c d x y : ℂ)) x :=
  hasDerivAt_power w hw (hasDerivAt_rowHgt_x (hden x y hy).ne') (rowHgt_pos' hden hy) a

theorem hasDerivAt_rowPotential_y (hw : w + 1 ≠ 0) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun q : ℝ => rowPotential c d w a ![x, q])
      (rowQ c d w a x y * (rowHgtY c d x y : ℂ)) y :=
  hasDerivAt_power w hw (hasDerivAt_rowHgt_y (hden x y hy).ne') (rowHgt_pos' hden hy) a

theorem contDiffAt_rowPotential {z : Point} (hz : 0 < z 1) {n : WithTop ℕ∞} :
    ContDiffAt ℝ n (rowPotential c d w a) z := by
  have hD := hden (z 0) (z 1) hz
  have hDc : ContDiffAt ℝ n (fun v : Point => rowDen c d (v 0) (v 1)) z := by
    unfold rowDen
    fun_prop
  have hS : ContDiffAt ℝ n (fun v : Point => rowHgt c d (v 0) (v 1)) z :=
    ContDiffAt.div (by fun_prop) hDc hD.ne'
  have hL := hS.log (rowHgt_pos' hden hz).ne'
  have hLc := Complex.ofRealCLM.contDiff.contDiffAt.comp z hL
  exact contDiffAt_const.mul (contDiffAt_const.mul hLc).cexp

theorem coordDeriv_zero_rowPotential (hw : w + 1 ≠ 0) {z : Point} (hz : 0 < z 1) :
    coordDeriv 0 (rowPotential c d w a) z = rowQ c d w a (z 0) (z 1) * (rowHgtX c d (z 0) (z 1) : ℂ) :=
  coordDeriv_zero_eq ((contDiffAt_rowPotential hden w a hz (n := 1)).differentiableAt (by norm_num))
    (hasDerivAt_rowPotential_x hden w a hw (z 0) hz)

theorem coordDeriv_one_rowPotential (hw : w + 1 ≠ 0) {z : Point} (hz : 0 < z 1) :
    coordDeriv 1 (rowPotential c d w a) z = rowQ c d w a (z 0) (z 1) * (rowHgtY c d (z 0) (z 1) : ℂ) :=
  coordDeriv_one_eq ((contDiffAt_rowPotential hden w a hz (n := 1)).differentiableAt (by norm_num))
    (hasDerivAt_rowPotential_y hden w a hw (z 0) hz)

/-- **The potential is an eigenfunction**, `y²ΔY = w(w+1) Y`. -/
theorem rowPotential_eigen (hw : w + 1 ≠ 0) {z : Point} (hz : 0 < z 1) :
    ((z 1 : ℝ) : ℂ) ^ (2 : ℕ) * (coordDeriv 0 (coordDeriv 0 (rowPotential c d w a)) z +
      coordDeriv 1 (coordDeriv 1 (rowPotential c d w a)) z) =
      (w * (w + 1)) * rowPotential c d w a z := by
  have hC : ContDiffAt ℝ ((1 + 1 : ℕ)) (rowPotential c d w a) z :=
    contDiffAt_rowPotential hden w a hz
  have hd0 : DifferentiableAt ℝ (coordDeriv 0 (rowPotential c d w a)) z :=
    (contDiffAt_coordDeriv (n := 1) hC 0).differentiableAt (by norm_num)
  have hd1 : DifferentiableAt ℝ (coordDeriv 1 (rowPotential c d w a)) z :=
    (contDiffAt_coordDeriv (n := 1) hC 1).differentiableAt (by norm_num)
  have hD := hden (z 0) (z 1) hz
  have hs := rowHgt_pos' hden (c := c) (d := d) (x := z 0) hz
  have hxx : coordDeriv 0 (coordDeriv 0 (rowPotential c d w a)) z =
      a * Complex.exp (w * ((Real.log (rowHgt c d (z 0) (z 1)) : ℝ) : ℂ)) *
        (w * (rowHgtX c d (z 0) (z 1) : ℂ) ^ 2 / (rowHgt c d (z 0) (z 1) : ℂ) +
          (rowHgtXX c d (z 0) (z 1) : ℂ)) := by
    refine coordDeriv_zero_eq hd0 ?_
    have he : (fun q : ℝ => coordDeriv 0 (rowPotential c d w a) ![q, z 1]) =
        fun q => a * Complex.exp (w * ((Real.log (rowHgt c d q (z 1)) : ℝ) : ℂ)) *
          (rowHgtX c d q (z 1) : ℂ) := by
      funext q
      exact coordDeriv_zero_rowPotential hden w a hw (z := ![q, z 1]) hz
    rw [he]
    exact hasDerivAt_powerFirst w (hasDerivAt_rowHgt_x hD.ne') (hasDerivAt_rowHgtX_x hD.ne') hs rfl a
  have hyy : coordDeriv 1 (coordDeriv 1 (rowPotential c d w a)) z =
      a * Complex.exp (w * ((Real.log (rowHgt c d (z 0) (z 1)) : ℝ) : ℂ)) *
        (w * (rowHgtY c d (z 0) (z 1) : ℂ) ^ 2 / (rowHgt c d (z 0) (z 1) : ℂ) +
          (rowHgtYY c d (z 0) (z 1) : ℂ)) := by
    refine coordDeriv_one_eq hd1 ?_
    have he : (fun q : ℝ => coordDeriv 1 (rowPotential c d w a) ![z 0, q]) =ᶠ[𝓝 (z 1)]
        fun q => a * Complex.exp (w * ((Real.log (rowHgt c d (z 0) q) : ℝ) : ℂ)) *
          (rowHgtY c d (z 0) q : ℂ) := by
      filter_upwards [lt_mem_nhds hz] with q hq
      exact coordDeriv_one_rowPotential hden w a hw (z := ![z 0, q]) hq
    exact (hasDerivAt_powerFirst w (hasDerivAt_rowHgt_y hD.ne') (hasDerivAt_rowHgtY_y hD.ne') hs rfl a).congr_of_eventuallyEq he
  rw [hxx, hyy]
  have hg := rowHgt_grad_sq hD.ne'
  have hh := rowHgt_harmonic hD.ne'
  have hgC : (rowHgtX c d (z 0) (z 1) : ℂ) ^ 2 + (rowHgtY c d (z 0) (z 1) : ℂ) ^ 2 =
      1 / (rowDen c d (z 0) (z 1) : ℂ) ^ 2 := by exact_mod_cast hg
  have hhC : (rowHgtXX c d (z 0) (z 1) : ℂ) + (rowHgtYY c d (z 0) (z 1) : ℂ) = 0 := by exact_mod_cast hh
  have hsC : (rowHgt c d (z 0) (z 1) : ℂ) ≠ 0 := by exact_mod_cast hs.ne'
  have hDC : (rowDen c d (z 0) (z 1) : ℂ) ≠ 0 := by exact_mod_cast hD.ne'
  have hsv : (rowHgt c d (z 0) (z 1) : ℂ) = ((z 1 : ℝ) : ℂ) / (rowDen c d (z 0) (z 1) : ℂ) := by
    rw [rowHgt]
    push_cast
    rfl
  have hyy2 : ((z 1 : ℝ) : ℂ) ^ 2 * (1 / (rowDen c d (z 0) (z 1) : ℂ) ^ 2) =
      (rowHgt c d (z 0) (z 1) : ℂ) ^ 2 := by
    rw [hsv]
    field_simp
  rw [rowPotential, exp_succ_log w hs]
  set E := Complex.exp (w * ((Real.log (rowHgt c d (z 0) (z 1)) : ℝ) : ℂ))
  set s := (rowHgt c d (z 0) (z 1) : ℂ)
  set A := (rowHgtX c d (z 0) (z 1) : ℂ)
  set B := (rowHgtY c d (z 0) (z 1) : ℂ)
  have hkey : ((z 1 : ℝ) : ℂ) ^ 2 * (A ^ 2 + B ^ 2) = s ^ 2 := by rw [hgC, hyy2]
  have hL : ((z 1 : ℝ) : ℂ) ^ (2 : ℕ) * (a * E * (w * A ^ 2 / s + (rowHgtXX c d (z 0) (z 1) : ℂ)) +
      a * E * (w * B ^ 2 / s + (rowHgtYY c d (z 0) (z 1) : ℂ))) =
      a * E * (w * (((z 1 : ℝ) : ℂ) ^ 2 * (A ^ 2 + B ^ 2)) / s + ((z 1 : ℝ) : ℂ) ^ 2 *
        ((rowHgtXX c d (z 0) (z 1) : ℂ) + (rowHgtYY c d (z 0) (z 1) : ℂ))) := by
    ring
  rw [hL, hkey, hhC]
  field_simp
  ring

/-- The separated mode of an exponential is a vacuum perturbation. -/
theorem vac_vector_row (hw : w + 1 ≠ 0) (q : D4BMBackground.ExteriorPoint) :
    Vac (D4BMBackground.jet (q.val 1) (q.val 3))
      (ofMetricField (vectorMetricField w (fN w) (gradCovector (rowPotential c d w a))) q.val) := by
  intro i j
  have hr : 1 < q.val 1 := q.property.1
  obtain ⟨h1, h2, h3⟩ := deriv_chain (fun _ h => hasDerivAt_fN h w) (fun _ h => hasDerivAt_fN1 h w)
    (fun _ h => hasDerivAt_fN2 h w) hr
  obtain ⟨hm, hm1⟩ := fN_master hr w
  refine vectorMetricField_vacuum w (lam := w * (w + 1))
    (fun z hz => contDiffAt_rowPotential hden w a hz)
    (fun z hz => rowPotential_eigen hden w a hw hz) q
    (by exact_mod_cast contDiffAt_infty.mp (contDiffAt_fN hr w) 3) ?_ ?_ i j
  · rw [h1, h2]
    exact hm
  · rw [h1, h2, h3]
    exact hm1

/-- **The perturbation of an exponential is the separated vector mode.** -/
theorem rowMetric_exp (hw : w + 1 ≠ 0) {x : Fin 4 → ℝ} (hr : 1 < x 1) (hy : 0 < x 3) :
    rowMetric c d (fun S => a * Complex.exp (w * S)) (fun S => a * (w * Complex.exp (w * S))) x =
      vectorMetricField w (fN w) (gradCovector (rowPotential c d w a)) x := by
  have hF : rowF x ≠ 0 := by
    have h : (x 1 : ℂ) ^ (2 : ℕ) - 1 ≠ 0 := by
      exact_mod_cast (by nlinarith : (x 1) ^ (2 : ℕ) - 1 ≠ 0)
    simpa only [rowF, ← pow_two, ← sub_eq_add_neg] using h
  have hR0 : (x 1 : ℂ) ≠ 0 := by exact_mod_cast (by linarith : x 1 ≠ 0)
  have hFv : rowF x = (x 1 : ℂ) ^ 2 - 1 := by
    rw [rowF]
    ring
  have hF2 : (x 1 : ℂ) ^ 2 - 1 ≠ 0 := by
    rw [← hFv]
    exact hF
  have hs := rowHgt_pos' hden (c := c) (d := d) (x := x 2) hy
  have hexp : Complex.exp (w * ((rowS c d x : ℝ) : ℂ)) =
      Complex.exp (w * (x 0 : ℂ)) * gP w (x 1) *
        Complex.exp (w * ((Real.log (rowHgt c d (x 2) (x 3)) : ℝ) : ℂ)) := by
    rw [gP, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    simp only [rowS]
    push_cast
    ring
  have hzV : angularPoint x 1 = x 3 := rfl
  have hz0 : angularPoint x 0 = x 2 := rfl
  have hV0 : gradCovector (rowPotential c d w a) 0 (angularPoint x) =
      rowQ c d w a (x 2) (x 3) * (rowSigma c d 0 x : ℂ) := by
    change coordDeriv 1 (rowPotential c d w a) (angularPoint x) = _
    rw [coordDeriv_one_rowPotential hden w a hw (z := angularPoint x) hy]
    simp [rowSigma, hz0, hzV]
  have hV1 : gradCovector (rowPotential c d w a) 1 (angularPoint x) =
      rowQ c d w a (x 2) (x 3) * (rowSigma c d 1 x : ℂ) := by
    change -coordDeriv 0 (rowPotential c d w a) (angularPoint x) = _
    rw [coordDeriv_zero_rowPotential hden w a hw (z := angularPoint x) hy]
    simp [rowSigma, hz0, hzV]
  have hTb : vectorTimeBlock w (fN w) x =
      Complex.exp (w * (x 0 : ℂ)) * gP w (x 1) * (rowF x + w) := by
    obtain ⟨h1, -, -⟩ := deriv_chain (fun _ h => hasDerivAt_fN h w) (fun _ h => hasDerivAt_fN1 h w)
      (fun _ h => hasDerivAt_fN2 h w) hr
    simp only [vectorTimeBlock, timeRadial, h1, fN1, gP1, rateA, radialRho]
    change rowF x * _ = _
    rw [hFv]
    push_cast
    field_simp
  have hRb : vectorRadiusBlock w (fN w) x =
      w * (Complex.exp (w * (x 0 : ℂ)) * ((x 1 : ℂ) * gP w (x 1))) * (rowF x)⁻¹ := rfl
  have hT : ∀ i : Fin 2, rowT c d (fun S => a * Complex.exp (w * S))
      (fun S => a * (w * Complex.exp (w * S))) i x =
      vectorTimeBlock w (fN w) x * (rowQ c d w a (x 2) (x 3) * (rowSigma c d i x : ℂ)) := fun i => by
    simp only [rowT, hTb, hexp, rowQ]
    ring
  have hR : ∀ i : Fin 2, rowR c d (fun S => a * (w * Complex.exp (w * S))) i x =
      vectorRadiusBlock w (fN w) x * (rowQ c d w a (x 2) (x 3) * (rowSigma c d i x : ℂ)) := fun i => by
    simp only [rowR, hRb, hexp, rowQ]
    ring
  rw [rowMetric, vectorMetricField]
  simp only [hT, hR, hV0, hV1]

end Potential

/-! ### Interpolation by exponentials -/

/-- The exponent `j`. -/
def expRate (j : Fin 4) : ℂ := ((j : ℕ) : ℂ)

/-- The sum `Σ_j a_j j^n e^{jS}`. -/
def expSum (a : Fin 4 → ℂ) (n : ℕ) (S : ℝ) : ℂ :=
  ∑ j, a j * (expRate j ^ n * Complex.exp (expRate j * S))

theorem hasDerivAt_expSum (a : Fin 4 → ℂ) (n : ℕ) (S : ℝ) :
    HasDerivAt (expSum a n) (expSum a (n + 1) S) S := by
  have h : HasDerivAt (fun S : ℝ => ∑ j, a j * (expRate j ^ n * Complex.exp (expRate j * S)))
      (∑ j, a j * (expRate j ^ n * (expRate j * Complex.exp (expRate j * S)))) S :=
    HasDerivAt.fun_sum fun j _ => ((hasDerivAt_exp_real_mul (expRate j) S).const_mul (expRate j ^ n)).const_mul (a j)
  refine h.congr_deriv (Finset.sum_congr rfl fun j _ => ?_)
  ring

theorem deriv_expSum (a : Fin 4 → ℂ) (n : ℕ) : deriv (expSum a n) = expSum a (n + 1) :=
  funext fun S => (hasDerivAt_expSum a n S).deriv

theorem contDiff_expSum (a : Fin 4 → ℂ) (n : ℕ) : ContDiff ℝ 2 (expSum a n) := by
  unfold expSum
  exact ContDiff.sum fun j _ => contDiff_const.mul (contDiff_const.mul (contDiff_exp_real_mul _))

/-- **Interpolation.**  Four exponentials realize any four values of the derivatives at a point. -/
theorem exists_expSum_eq (b : Fin 4 → ℂ) (S₀ : ℝ) :
    ∃ a : Fin 4 → ℂ, ∀ n : Fin 4, expSum a n S₀ = b n := by
  have hinj : Function.Injective expRate := fun i j h => by
    have h' : ((i : ℕ) : ℂ) = ((j : ℕ) : ℂ) := h
    have : (i : ℕ) = j := by exact_mod_cast h'
    exact Fin.ext this
  set A := Matrix.transpose (Matrix.vandermonde expRate) with hA
  have hdet : A.det ≠ 0 := by
    rw [hA, Matrix.det_transpose]
    exact Matrix.det_vandermonde_ne_zero_iff.mpr hinj
  set e := A⁻¹.mulVec b with he
  have hsol : A.mulVec e = b := by
    rw [he, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A (isUnit_iff_ne_zero.mpr hdet),
      Matrix.one_mulVec]
  refine ⟨fun j => e j * Complex.exp (-(expRate j * S₀)), fun n => ?_⟩
  have h := congrFun hsol n
  rw [← h]
  simp only [expSum, Matrix.mulVec, dotProduct, hA, Matrix.transpose_apply, Matrix.vandermonde_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hc : Complex.exp (-(expRate j * S₀)) * Complex.exp (expRate j * S₀) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  linear_combination (e j * expRate j ^ (n : ℕ)) * hc

/-! ### The theorem -/

section Main

variable {c d : ℝ} (hden : ∀ x y : ℝ, 0 < y → 0 < rowDen c d x y) (q : D4BMBackground.ExteriorPoint)

include hden

/-- A sum of exponentials has a vacuum perturbation. -/
theorem vac_rowMetric_expSum (a : Fin 4 → ℂ) :
    Vac (D4BMBackground.jet (q.val 1) (q.val 3))
      (ofMetricField (rowMetric c d (expSum a 0) (expSum a 1)) q.val) := by
  set g : Fin 4 → (Fin 4 → ℝ) → Matrix (Fin 4) (Fin 4) ℂ := fun j =>
    rowMetric c d (fun S => a j * Complex.exp (expRate j * S))
      (fun S => a j * (expRate j * Complex.exp (expRate j * S))) with hg
  have hsum : rowMetric c d (expSum a 0) (expSum a 1) = fun x => ∑ j, (1 : ℂ) • g j x := by
    funext x
    have hT : ∀ i, rowT c d (expSum a 0) (expSum a 1) i x =
        ∑ j, rowT c d (fun S => a j * Complex.exp (expRate j * S))
          (fun S => a j * (expRate j * Complex.exp (expRate j * S))) i x := fun i => by
      simp only [rowT, expSum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    have hR : ∀ i, rowR c d (expSum a 1) i x =
        ∑ j, rowR c d (fun S => a j * (expRate j * Complex.exp (expRate j * S))) i x := fun i => by
      simp only [rowR, expSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      ring
    ext u v
    simp only [one_smul, Matrix.sum_apply, hg]
    fin_cases u <;> fin_cases v
    all_goals first
      | (simp [rowMetric]; done)
      | exact hT 0 | exact hT 1 | exact hR 0 | exact hR 1
  rw [hsum]
  have hexpC (j : Fin 4) : ContDiffAt ℝ 2 (fun S : ℝ => a j * Complex.exp (expRate j * S))
      (rowS c d q.val) := contDiffAt_const.mul (contDiff_exp_real_mul _).contDiffAt
  have hexpC₁ (j : Fin 4) : ContDiffAt ℝ 2
      (fun S : ℝ => a j * (expRate j * Complex.exp (expRate j * S))) (rowS c d q.val) :=
    contDiffAt_const.mul (contDiffAt_const.mul (contDiff_exp_real_mul _).contDiffAt)
  refine vac_sum _ Finset.univ _ g (fun j _ a b => contDiffAt_rowMetric hden q (hexpC j) (hexpC₁ j) a b)
    (fun j _ => ?_)
  have hgerm : g j =ᶠ[𝓝 q.val] vectorMetricField (expRate j) (fN (expRate j))
      (gradCovector (rowPotential c d (expRate j) (a j))) := by
    have hopen : {x : Fin 4 → ℝ | 1 < x 1 ∧ 0 < x 3} ∈ 𝓝 q.val :=
      ((isOpen_lt continuous_const (continuous_apply 1)).inter
        (isOpen_lt continuous_const (continuous_apply 3))).mem_nhds q.property
    filter_upwards [hopen] with x hx
    exact rowMetric_exp hden (expRate j) (a j)
      (by simpa [expRate] using Nat.cast_add_one_ne_zero (R := ℂ) (j : ℕ)) hx.1 hx.2
  rw [ofMetricField_congr_germ hgerm]
  exact vac_vector_row hden (expRate j) (a j)
    (by simpa [expRate] using Nat.cast_add_one_ne_zero (R := ℂ) (j : ℕ)) q

/-- **The perturbation of a row is vacuum, for every `C³` function.** -/
theorem rowMetric_vacuum {m : ℝ → ℂ} (hm : ContDiffAt ℝ 3 m (rowS c d q.val)) :
    Vac (D4BMBackground.jet (q.val 1) (q.val 3))
      (ofMetricField (rowMetric c d m (deriv m)) q.val) := by
  set S₀ := rowS c d q.val with hS₀
  have hm2 : ContDiffAt ℝ 2 m S₀ := hm.of_le (by norm_num)
  have hm1 : ContDiffAt ℝ 2 (deriv m) S₀ := contDiffAt_deriv_two hm
  obtain ⟨a, ha⟩ := exists_expSum_eq ![m S₀, deriv m S₀, deriv (deriv m) S₀, deriv (deriv (deriv m)) S₀] S₀
  have h0 : expSum a 0 S₀ = m S₀ := ha 0
  have h1 : expSum a 1 S₀ = deriv m S₀ := ha 1
  have h2 : expSum a 2 S₀ = deriv (deriv m) S₀ := ha 2
  have h3 : expSum a 3 S₀ = deriv (deriv (deriv m)) S₀ := ha 3
  have hjet := rowMetric_congr_jet hden q (m := m) (m₁ := deriv m) (n := expSum a 0) (n₁ := expSum a 1)
    hm2 hm1 (contDiff_expSum a 0).contDiffAt (contDiff_expSum a 1).contDiffAt
    h0.symm (by rw [deriv_expSum]; exact h1.symm) (by rw [deriv_expSum, deriv_expSum]; exact h2.symm)
    h1.symm (by rw [deriv_expSum]; exact h2.symm) (by rw [deriv_expSum, deriv_expSum]; exact h3.symm)
  rw [hjet]
  exact vac_rowMetric_expSum hden q a

end Main

end GaloisForLFunctions.BlackHoleRingdown

end
