import GaloisForLFunctions.HTGeometry.ClockPrincipalSymbolCalibration
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Complex.Basic

/-!
# Complete scalar two-jets of complex fields on real coordinates

The algebraic scalar two-jet retains every ordered coordinate derivative. The operations below
are identified with actual derivatives on their local domains, for later metric reconstruction.
-/

namespace GaloisForLFunctions.HTGeometry.ScalarTwoJet

open scoped ContDiff
noncomputable section

variable {d : ℕ}

/-- Constant scalar field jet. -/
def constant (c : ℂ) : ScalarTwoJet (Fin d) ℂ := ⟨c, fun _ => 0, fun _ _ => 0⟩

/-- Entrywise addition of complete scalar jets. -/
def add (a b : ScalarTwoJet (Fin d) ℂ) : ScalarTwoJet (Fin d) ℂ :=
  ⟨a.value + b.value, fun i => a.first i + b.first i, fun i j => a.second i j + b.second i j⟩

/-- Entrywise negation of complete scalar jets. -/
def neg (a : ScalarTwoJet (Fin d) ℂ) : ScalarTwoJet (Fin d) ℂ :=
  ⟨-a.value, fun i => -a.first i, fun i j => -a.second i j⟩

/-- Reciprocal jet, with the complete second-order chain rule. -/
def inv (a : ScalarTwoJet (Fin d) ℂ) : ScalarTwoJet (Fin d) ℂ where
  value := a.value⁻¹
  first i := -(a.value⁻¹ ^ 2) * a.first i
  second i j := 2 * a.value⁻¹ ^ 3 * a.first i * a.first j - a.value⁻¹ ^ 2 * a.second i j

/-- Coordinate coordDeriv of a complex-valued field on real coordinates. -/
abbrev coordDeriv (i : Fin d) (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  fderiv ℝ f x (Pi.single i 1)

/-- Actual complete two-jet, without imposing symmetry on formal input arrays. -/
def ofField (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ScalarTwoJet (Fin d) ℂ :=
  ⟨f x, fun i => coordDeriv i f x, fun i j => coordDeriv i (coordDeriv j f) x⟩

private theorem partial_hasFDerivAt {f : (Fin d → ℝ) → ℂ} {x : Fin d → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (j : Fin d) :
    HasFDerivAt (coordDeriv j f) ((fderiv ℝ (fderiv ℝ f) x).flip (Pi.single j 1)) x := by
  have h := ((hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)).hasFDerivAt
  simpa [coordDeriv] using h.clm_apply (hasFDerivAt_const (Pi.single j 1) x)

private theorem partial_second {f : (Fin d → ℝ) → ℂ} {x : Fin d → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (i j : Fin d) :
    coordDeriv i (coordDeriv j f) x =
      fderiv ℝ (fderiv ℝ f) x (Pi.single i 1) (Pi.single j 1) :=
  congrArg (fun L => L (Pi.single i 1)) (partial_hasFDerivAt hf j).fderiv

private theorem partial_mul {f g : (Fin d → ℝ) → ℂ} {x : Fin d → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin d) :
    coordDeriv i (fun y => f y * g y) x = coordDeriv i f x * g x + f x * coordDeriv i g x := by
  simp only [coordDeriv, fderiv_fun_mul hf hg, add_apply, smul_apply, smul_eq_mul]
  ring

private theorem partial_add {f g : (Fin d → ℝ) → ℂ} {x : Fin d → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (i : Fin d) :
    coordDeriv i (fun y => f y + g y) x = coordDeriv i f x + coordDeriv i g x := by
  simp only [coordDeriv, fderiv_fun_add hf hg, add_apply]

/-- Constant fields have zero first and second coordinate jets. -/
theorem ofField_constant (c : ℂ) (x : Fin d → ℝ) :
    ofField (fun _ => c) x = constant c := by
  have hzero (j : Fin d) : coordDeriv j (fun _ : Fin d → ℝ => c) = fun _ => 0 := by
    funext y
    simp [coordDeriv]
  ext i j
  · rfl
  · simp [ofField, constant, coordDeriv]
  · change coordDeriv i (coordDeriv j (fun _ => c)) x = 0
    rw [hzero]
    simp [coordDeriv]

/-- Jet addition agrees with the actual local coordinate derivatives. -/
theorem ofField_add {f g : (Fin d → ℝ) → ℂ} {x : Fin d → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    ofField (fun y => f y + g y) x = add (ofField f x) (ofField g x) := by
  have hfd := hf.differentiableAt (by norm_num)
  have hgd := hg.differentiableAt (by norm_num)
  ext i j
  · rfl
  · exact partial_add hfd hgd i
  · have heq : coordDeriv j (fun y => f y + g y) =ᶠ[nhds x]
        fun y => coordDeriv j f y + coordDeriv j g y := by
      filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hy hy'
      exact partial_add (hy.differentiableAt (by norm_num)) (hy'.differentiableAt (by norm_num)) j
    have hd := ((partial_hasFDerivAt hf j).add (partial_hasFDerivAt hg j)).congr_of_eventuallyEq heq
    change fderiv ℝ (coordDeriv j (fun y => f y + g y)) x (Pi.single i 1) = _
    rw [hd.fderiv]
    simp only [ofField, add, partial_second hf, partial_second hg, add_apply,
      ContinuousLinearMap.flip_apply]

/-- Negation agrees with the actual coordinate derivatives, including the second jet. -/
theorem ofField_neg (f : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) :
    ofField (fun y => -f y) x = neg (ofField f x) := by
  have hfun (j : Fin d) : coordDeriv j (fun y => -f y) = fun y => -coordDeriv j f y := by
    funext y
    simp [coordDeriv]
  ext i j
  · rfl
  · simp [ofField, neg, coordDeriv]
  · change coordDeriv i (coordDeriv j (fun y => -f y)) x = _
    rw [hfun]
    simp [coordDeriv, ofField, neg]

/-- The corpus product jet is the actual local second-order product rule. -/
theorem ofField_mul {f g : (Fin d → ℝ) → ℂ} {x : Fin d → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) :
    ofField (fun y => f y * g y) x = mul (ofField f x) (ofField g x) := by
  have hfd := hf.differentiableAt (by norm_num)
  have hgd := hg.differentiableAt (by norm_num)
  ext i j
  · rfl
  · exact partial_mul hfd hgd i
  · have heq : coordDeriv j (fun y => f y * g y) =ᶠ[nhds x]
        fun y => coordDeriv j f y * g y + f y * coordDeriv j g y := by
      filter_upwards [hf.eventually (by simp), hg.eventually (by simp)] with y hy hy'
      exact partial_mul (hy.differentiableAt (by norm_num)) (hy'.differentiableAt (by norm_num)) j
    have hd := (((partial_hasFDerivAt hf j).mul hgd.hasFDerivAt).add
      (hfd.hasFDerivAt.mul (partial_hasFDerivAt hg j))).congr_of_eventuallyEq heq
    change fderiv ℝ (coordDeriv j (fun y => f y * g y)) x (Pi.single i 1) = _
    rw [hd.fderiv]
    simp only [ofField, mul, partial_second hf, partial_second hg, add_apply,
      smul_apply, smul_eq_mul, ContinuousLinearMap.flip_apply, coordDeriv]
    ring

private theorem field_inv_hasFDerivAt {f : (Fin d → ℝ) → ℂ} {x : Fin d → ℝ}
    (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) :
    HasFDerivAt (fun y => (f y)⁻¹) (-(f x)⁻¹ ^ 2 • fderiv ℝ f x) x := by
  simpa only [Function.comp_def, inv_pow] using
    (hasDerivAt_inv hx).comp_hasFDerivAt x hf.hasFDerivAt

private theorem partial_inv {f : (Fin d → ℝ) → ℂ} {x : Fin d → ℝ}
    (hf : DifferentiableAt ℝ f x) (hx : f x ≠ 0) (i : Fin d) :
    coordDeriv i (fun y => (f y)⁻¹) x = -(f x)⁻¹ ^ 2 * coordDeriv i f x := by
  simp only [coordDeriv, (field_inv_hasFDerivAt hf hx).fderiv, smul_apply, smul_eq_mul]

/-- Reciprocal jets agree with actual local derivatives wherever the scalar value is nonzero. -/
theorem ofField_inv {f : (Fin d → ℝ) → ℂ} {x : Fin d → ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hx : f x ≠ 0) :
    ofField (fun y => (f y)⁻¹) x = inv (ofField f x) := by
  have hfd := hf.differentiableAt (by norm_num)
  have hi := field_inv_hasFDerivAt hfd hx
  ext i j
  · rfl
  · exact partial_inv hfd hx i
  · have heq : coordDeriv j (fun y => (f y)⁻¹) =ᶠ[nhds x]
        fun y => -((f y)⁻¹ * (f y)⁻¹) * coordDeriv j f y := by
      filter_upwards [hf.eventually (by simp), hf.continuousAt.eventually_ne hx] with y hy hy'
      simpa only [pow_two] using partial_inv (hy.differentiableAt (by norm_num)) hy' j
    have hd := (((hi.fun_mul hi).neg).fun_mul
      (partial_hasFDerivAt hf j)).congr_of_eventuallyEq heq
    change fderiv ℝ (coordDeriv j (fun y => (f y)⁻¹)) x (Pi.single i 1) = _
    rw [hd.fderiv]
    simp only [ofField, inv, partial_second hf, add_apply, neg_apply, Pi.neg_apply, smul_apply,
      smul_eq_mul, ContinuousLinearMap.flip_apply, coordDeriv]
    ring

/-- Second-order composition with the value and first two derivatives of a scalar function. -/
def compose (a : ScalarTwoJet (Fin d) ℂ) (v p q : ℂ) : ScalarTwoJet (Fin d) ℂ where
  value := v
  first i := p * a.first i
  second i j := q * a.first i * a.first j + p * a.second i j

private theorem partial_comp {φ : ℂ → ℂ} {g : (Fin d → ℝ) → ℂ} {x : Fin d → ℝ}
    (hφ : DifferentiableAt ℂ φ (g x)) (hg : DifferentiableAt ℝ g x) (i : Fin d) :
    coordDeriv i (fun y => φ (g y)) x = deriv φ (g x) * coordDeriv i g x := by
  have hd := hφ.hasDerivAt.comp_hasFDerivAt x hg.hasFDerivAt
  simp only [Function.comp_def] at hd
  simp only [coordDeriv, hd.fderiv, smul_apply, smul_eq_mul]

/-- Scalar composition retains both the Hessian-principal and coordinate-connection terms. -/
theorem ofField_comp {φ : ℂ → ℂ} {g : (Fin d → ℝ) → ℂ} {x : Fin d → ℝ}
    (hφ : ContDiffAt ℂ 2 φ (g x)) (hg : ContDiffAt ℝ 2 g x) :
    ofField (fun y => φ (g y)) x =
      compose (ofField g x) (φ (g x)) (deriv φ (g x)) (deriv (deriv φ) (g x)) := by
  have hgd := hg.differentiableAt (by norm_num)
  ext i j
  · rfl
  · exact partial_comp (hφ.differentiableAt (by norm_num)) hgd i
  · have houter : ∀ᶠ y in nhds x, ContDiffAt ℂ 2 φ (g y) :=
      hg.continuousAt.eventually (hφ.eventually (by simp))
    have heq : coordDeriv j (fun y => φ (g y)) =ᶠ[nhds x]
        fun y => deriv φ (g y) * coordDeriv j g y := by
      filter_upwards [houter, hg.eventually (by simp)] with y hy hy'
      exact partial_comp (hy.differentiableAt (by norm_num)) (hy'.differentiableAt (by norm_num)) j
    have hp := ((hφ.derivWithin (m := 1) (by norm_num)).differentiableAt
      (by norm_num)).hasDerivAt.comp_hasFDerivAt x hgd.hasFDerivAt
    have hd := (hp.fun_mul (partial_hasFDerivAt hg j)).congr_of_eventuallyEq heq
    change fderiv ℝ (coordDeriv j (fun y => φ (g y))) x (Pi.single i 1) = _
    rw [hd.fderiv]
    simp only [ofField, compose, partial_second hg, add_apply, smul_apply, smul_eq_mul,
      ContinuousLinearMap.flip_apply, coordDeriv, Function.comp_def]
    ring

/-- Rational scalar expressions whose two-jets can be evaluated with a local correctness proof. -/
inductive Expression (α : Type*) where
  | atom (a : α)
  | constant (c : ℂ)
  | add (p q : Expression α)
  | neg (p : Expression α)
  | mul (p q : Expression α)
  | inv (p : Expression α)

namespace Expression

variable {α : Type*}

/-- Literal scalar evaluation of a reconstruction expression. -/
def eval (a : α → ℂ) : Expression α → ℂ
  | .atom i => a i
  | .constant c => c
  | .add p q => p.eval a + q.eval a
  | .neg p => -(p.eval a)
  | .mul p q => p.eval a * q.eval a
  | .inv p => (p.eval a)⁻¹

/-- Finite evaluation in the complete scalar two-jet calculus. -/
def evalJet (a : α → ScalarTwoJet (Fin d) ℂ) : Expression α → ScalarTwoJet (Fin d) ℂ
  | .atom i => a i
  | .constant c => ScalarTwoJet.constant c
  | .add p q => ScalarTwoJet.add (p.evalJet a) (q.evalJet a)
  | .neg p => ScalarTwoJet.neg (p.evalJet a)
  | .mul p q => ScalarTwoJet.mul (p.evalJet a) (q.evalJet a)
  | .inv p => ScalarTwoJet.inv (p.evalJet a)

/-- The value of the finite jet evaluation is the literal scalar expression. -/
@[simp] theorem evalJet_value (p : Expression α) (a : α → ScalarTwoJet (Fin d) ℂ) :
    (p.evalJet a).value = p.eval (fun i => (a i).value) := by
  induction p with
  | atom i => rfl
  | constant c => rfl
  | add p q ihp ihq => simpa only [evalJet, ScalarTwoJet.add, eval] using congrArg₂ (· + ·) ihp ihq
  | neg p ih => simpa only [evalJet, ScalarTwoJet.neg, eval] using congrArg Neg.neg ih
  | mul p q ihp ihq => simpa only [evalJet, ScalarTwoJet.mul, eval] using congrArg₂ (· * ·) ihp ihq
  | inv p ih => simpa only [evalJet, ScalarTwoJet.inv, eval] using congrArg Inv.inv ih

/-- Exactly the denominator conditions required by the displayed scalar expression. -/
def Regular (a : α → ℂ) : Expression α → Prop
  | .atom _ => True
  | .constant _ => True
  | .add p q => p.Regular a ∧ q.Regular a
  | .neg p => p.Regular a
  | .mul p q => p.Regular a ∧ q.Regular a
  | .inv p => p.Regular a ∧ p.eval a ≠ 0

/-- Every rational reconstruction expression has its actual complete two-jet on its regular domain. -/
theorem eval_jet_correct (p : Expression α) {a : α → (Fin d → ℝ) → ℂ} {x : Fin d → ℝ}
    (ha : ∀ i, ContDiffAt ℝ 2 (a i) x) (hp : p.Regular (fun i => a i x)) :
    ContDiffAt ℝ 2 (fun y => p.eval (fun i => a i y)) x ∧
      ofField (fun y => p.eval (fun i => a i y)) x = p.evalJet (fun i => ofField (a i) x) := by
  induction p with
  | atom i => exact ⟨ha i, rfl⟩
  | constant c => exact ⟨contDiffAt_const, ofField_constant c x⟩
  | add p q ihp ihq =>
    obtain ⟨hpd, hpj⟩ := ihp hp.1
    obtain ⟨hqd, hqj⟩ := ihq hp.2
    refine ⟨hpd.add hqd, ?_⟩
    change ofField (fun y => p.eval (fun i => a i y) + q.eval (fun i => a i y)) x = _
    rw [ofField_add hpd hqd, hpj, hqj]
    rfl
  | neg p ih =>
    obtain ⟨hd, hj⟩ := ih hp
    refine ⟨hd.neg, ?_⟩
    change ofField (fun y => -(p.eval (fun i => a i y))) x = _
    rw [ofField_neg, hj]
    rfl
  | mul p q ihp ihq =>
    obtain ⟨hpd, hpj⟩ := ihp hp.1
    obtain ⟨hqd, hqj⟩ := ihq hp.2
    refine ⟨hpd.mul hqd, ?_⟩
    change ofField (fun y => p.eval (fun i => a i y) * q.eval (fun i => a i y)) x = _
    rw [ofField_mul hpd hqd, hpj, hqj]
    rfl
  | inv p ih =>
    obtain ⟨hd, hj⟩ := ih hp.1
    refine ⟨hd.inv hp.2, ?_⟩
    change ofField (fun y => (p.eval (fun i => a i y))⁻¹) x = _
    rw [ofField_inv hd hp.2, hj]
    rfl

end Expression

end
end GaloisForLFunctions.HTGeometry.ScalarTwoJet
