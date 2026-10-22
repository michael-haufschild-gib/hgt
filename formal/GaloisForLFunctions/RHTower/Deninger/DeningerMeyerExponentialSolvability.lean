import GaloisForLFunctions.RHTower.Deninger.DeningerMeyerConvolutionQuotient

/-! # Global exponential convolution equations in the original source

For every original source g, the kernel with transform exp(Mg)-1 is again
an original source. The equation h + E(g)*h = f has a unique original source
solution E(-g)*f + f, with no smallness, sign or spectral-location premise.
The actual Poisson ideal is preserved, so this action descends to cohomology.
-/

open Complex MeasureTheory
namespace RHTower
noncomputable section

local notation "V" => DeningerMeyerStrongLogTarget
local notation "Q" => DeningerMeyerStrongLogCohomology
local notation "N" => LinearMap.range deningerMeyerStrongLogSumLM

@[simp] theorem deningerMeyerStrongLogMellin_neg (g : V) (s : ℂ) :
    deningerMeyerStrongLogMellin (-g) s = -deningerMeyerStrongLogMellin g s :=
  (deningerMeyerStrongLogMellinLM s).map_neg g

@[simp] theorem deningerMeyerSourceExp_zero : deningerMeyerSourceExp 0 = 0 := by
  apply deningerMeyerStrongLogMellin_injective
  funext s
  simp

theorem deningerMeyerSourceExp_add (g h : V) :
    deningerMeyerSourceExp (g+h) = deningerMeyerSourceExp g + deningerMeyerSourceExp h +
      deningerMeyerSourceConvolution (deningerMeyerSourceExp g) (deningerMeyerSourceExp h) := by
  apply deningerMeyerStrongLogMellin_injective
  funext s
  change (deningerMeyerStrongLogMellinLM s) (deningerMeyerSourceExp (g+h)) =
    (deningerMeyerStrongLogMellinLM s) (deningerMeyerSourceExp g + deningerMeyerSourceExp h +
      deningerMeyerSourceConvolution (deningerMeyerSourceExp g) (deningerMeyerSourceExp h))
  rw [map_add, map_add]
  change deningerMeyerStrongLogMellin (deningerMeyerSourceExp (g+h)) s =
    deningerMeyerStrongLogMellin (deningerMeyerSourceExp g) s +
    deningerMeyerStrongLogMellin (deningerMeyerSourceExp h) s +
    deningerMeyerStrongLogMellin
      (deningerMeyerSourceConvolution (deningerMeyerSourceExp g) (deningerMeyerSourceExp h)) s
  simp only [deningerMeyerSourceExp_mellin, Submodule.coe_add, deningerMeyerStrongLogMellin_add,
    deningerMeyerSourceConvolution_mellin, Complex.exp_add]
  ring

/-- An entire exponential gives a genuine linear convolution operator on original sources. -/
def deningerMeyerSourceGauge (g : V) : Module.End ℂ V :=
  LinearMap.id + deningerMeyerSourceConvolutionLM (deningerMeyerSourceExp g)

@[simp] theorem deningerMeyerSourceGauge_apply (g h : V) :
    deningerMeyerSourceGauge g h = h +
      deningerMeyerSourceConvolution (deningerMeyerSourceExp g) h := rfl

@[simp] theorem deningerMeyerSourceGauge_mellin (g h : V) (s : ℂ) :
    deningerMeyerStrongLogMellin (deningerMeyerSourceGauge g h) s =
      Complex.exp (deningerMeyerStrongLogMellin g s) * deningerMeyerStrongLogMellin h s := by
  simp only [deningerMeyerSourceGauge_apply, Submodule.coe_add, deningerMeyerStrongLogMellin_add,
    deningerMeyerSourceConvolution_mellin, deningerMeyerSourceExp_mellin]
  ring

@[simp] theorem deningerMeyerSourceGauge_zero : deningerMeyerSourceGauge 0 = LinearMap.id := by
  apply LinearMap.ext
  intro g
  apply deningerMeyerStrongLogMellin_injective
  funext s
  simp

theorem deningerMeyerSourceGauge_add (g h : V) :
    deningerMeyerSourceGauge (g+h) =
      (deningerMeyerSourceGauge g).comp (deningerMeyerSourceGauge h) := by
  apply LinearMap.ext
  intro f
  apply deningerMeyerStrongLogMellin_injective
  funext s
  simp only [LinearMap.comp_apply, deningerMeyerSourceGauge_mellin,
    Submodule.coe_add, deningerMeyerStrongLogMellin_add, Complex.exp_add, mul_assoc]

theorem deningerMeyerSourceGauge_nat_mul (n : ℕ) (z : ℂ) (g : V) :
    deningerMeyerSourceGauge (((n : ℂ)*z) • g) = (deningerMeyerSourceGauge (z • g))^n := by
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_mul, zero_smul, deningerMeyerSourceGauge_zero, pow_zero]
    rfl
  | succ n ih =>
    have he : (((n+1 : ℕ) : ℂ)*z) • g = ((n : ℂ)*z) • g + z • g := by
      simp only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_smul]
    rw [he, deningerMeyerSourceGauge_add, ih, pow_succ]
    rfl

/-- Every positive integer root is itself an admitted original-source convolution gauge. -/
theorem deningerMeyerSourceGauge_root (n : ℕ) (g : V) :
    (deningerMeyerSourceGauge (((n+1 : ℕ) : ℂ)⁻¹ • g))^(n+1) =
      deningerMeyerSourceGauge g := by
  have hn : ((n+1 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
  simpa only [mul_inv_cancel₀ hn, one_smul] using
    (deningerMeyerSourceGauge_nat_mul (n+1) (((n+1 : ℕ) : ℂ)⁻¹) g).symm

/-- Global inversion in the actual all-weight space. -/
def deningerMeyerSourceGaugeEquiv (g : V) : V ≃ₗ[ℂ] V where
  toLinearMap := deningerMeyerSourceGauge g
  invFun := deningerMeyerSourceGauge (-g)
  left_inv f := by
    change ((deningerMeyerSourceGauge (-g)).comp (deningerMeyerSourceGauge g)) f = f
    rw [← deningerMeyerSourceGauge_add, neg_add_cancel, deningerMeyerSourceGauge_zero]
    rfl
  right_inv f := by
    change ((deningerMeyerSourceGauge g).comp (deningerMeyerSourceGauge (-g))) f = f
    rw [← deningerMeyerSourceGauge_add, add_neg_cancel, deningerMeyerSourceGauge_zero]
    rfl

/-- Every exponential convolution equation has a unique literal source solution. -/
theorem deningerMeyerExponentialEquation_existsUnique (g f : V) :
    ∃! h : V, ∀ x : ℝ,
      h.val x + (∫ t : ℝ, (deningerMeyerSourceExp g).val t * h.val (x-t)) = f.val x := by
  refine ⟨deningerMeyerSourceGauge (-g) f, ?_, ?_⟩
  · intro x
    have h := (deningerMeyerSourceGaugeEquiv g).apply_symm_apply f
    change deningerMeyerSourceGauge g (deningerMeyerSourceGauge (-g) f) = f at h
    have hx := congrArg (fun u : V => u.val x) h
    simpa only [deningerMeyerSourceGauge_apply, Submodule.coe_add, Pi.add_apply,
      deningerMeyerSourceConvolution_apply] using hx
  · intro h hh
    apply (deningerMeyerSourceGaugeEquiv g).injective
    change deningerMeyerSourceGauge g h = deningerMeyerSourceGauge g (deningerMeyerSourceGauge (-g) f)
    have hinv := (deningerMeyerSourceGaugeEquiv g).apply_symm_apply f
    change deningerMeyerSourceGauge g (deningerMeyerSourceGauge (-g) f) = f at hinv
    rw [hinv]
    apply Subtype.ext
    funext x
    simpa only [deningerMeyerSourceGauge_apply, Submodule.coe_add, Pi.add_apply,
      deningerMeyerSourceConvolution_apply] using hh x

private theorem sourceGauge_mem (g : V) {h : V} (hh : h ∈ N) :
    deningerMeyerSourceGauge g h ∈ N := by
  obtain ⟨f, rfl⟩ := hh
  exact (N).add_mem ⟨f, rfl⟩ (deningerMeyerSourceConvolution_boundary (deningerMeyerSourceExp g) f)

/-- The same actual-source gauge acts on the original Poisson quotient. -/
def deningerMeyerCohomologySourceGauge (g : V) : Module.End ℂ Q :=
  (N).mapQ N (deningerMeyerSourceGauge g) (by intro h hh; exact sourceGauge_mem g hh)

@[simp] theorem deningerMeyerCohomologySourceGauge_mk (g h : V) :
    deningerMeyerCohomologySourceGauge g (Submodule.Quotient.mk h) =
      Submodule.Quotient.mk (deningerMeyerSourceGauge g h) := rfl

theorem deningerMeyerCohomologySourceGauge_add (g h : V) :
    deningerMeyerCohomologySourceGauge (g+h) =
      (deningerMeyerCohomologySourceGauge g).comp (deningerMeyerCohomologySourceGauge h) := by
  apply LinearMap.ext
  intro u
  induction u using Submodule.Quotient.induction_on with
  | H f =>
    change Submodule.Quotient.mk (deningerMeyerSourceGauge (g+h) f) =
      Submodule.Quotient.mk (deningerMeyerSourceGauge g (deningerMeyerSourceGauge h f))
    rw [deningerMeyerSourceGauge_add, LinearMap.comp_apply]

@[simp] theorem deningerMeyerCohomologySourceGauge_zero :
    deningerMeyerCohomologySourceGauge 0 = LinearMap.id := by
  apply LinearMap.ext
  intro u
  induction u using Submodule.Quotient.induction_on with
  | H f =>
    change Submodule.Quotient.mk (deningerMeyerSourceGauge 0 f) = Submodule.Quotient.mk f
    rw [deningerMeyerSourceGauge_zero, LinearMap.id_apply]

def deningerMeyerCohomologySourceGaugeEquiv (g : V) : Q ≃ₗ[ℂ] Q where
  toLinearMap := deningerMeyerCohomologySourceGauge g
  invFun := deningerMeyerCohomologySourceGauge (-g)
  left_inv u := by
    change ((deningerMeyerCohomologySourceGauge (-g)).comp
      (deningerMeyerCohomologySourceGauge g)) u = u
    rw [← deningerMeyerCohomologySourceGauge_add, neg_add_cancel,
      deningerMeyerCohomologySourceGauge_zero]
    rfl
  right_inv u := by
    change ((deningerMeyerCohomologySourceGauge g).comp
      (deningerMeyerCohomologySourceGauge (-g))) u = u
    rw [← deningerMeyerCohomologySourceGauge_add, add_neg_cancel,
      deningerMeyerCohomologySourceGauge_zero]
    rfl

end
end RHTower
