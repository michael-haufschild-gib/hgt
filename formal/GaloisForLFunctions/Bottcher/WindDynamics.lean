/-
# Winding of a composed loop, and its dynamical algebra

For a nowhere-zero continuous `g : X → ℂ` and a loop `p` at `x₀`, the **transported loop**
`t ↦ g(p t)/g(x₀)` is a loop in `ℂ*` based at `1`; its degree `wind g p := deg⟦·⟧` is the winding
number of `g ∘ p` around `0`. Because we divide by the basepoint, everything lives at the single
basepoint `1`, so the whole `Pi1CMinusZero` calculus applies verbatim. The resulting algebra —

* `wind_mul`   : `wind (g·h) = wind g + wind h`        (pointwise product; `degZ_mulLoop`)
* `wind_pow`   : `wind (gᵏ)   = k · wind g`            (`degZ_powLoop`)
* `wind_const` : `wind (const) = 0`
* `wind_zero_of_re_pos` : a factor staying in the right half-plane is windingless (`degZ_zero_of_re_pos`)
* `wind_exp`   : `wind (exp ∘ M) = 0`                  (lifts to `M ∘ p`, a closed loop)

— is exactly the bookkeeping that turns "f is degree 2" into "the winding of `βlev_n ∘ f` is even":
`f ∘ g = g² · (1 + c/g²)`, and the corrector `1 + c/g²` stays near `1`. -/
import GaloisForLFunctions.Bottcher.Pi1CMinusZero

open Topology unitInterval
open Pi1CMinusZero

namespace Bottcher

variable {X : Type*} [TopologicalSpace X]

/-- The transported loop `t ↦ g(p t)/g(x₀)`, a loop in `ℂ*` based at `1`. -/
noncomputable def transLoop (g : X → ℂ) (hg : Continuous g) (hgne : ∀ x, g x ≠ 0)
    {x₀ : X} (p : Path x₀ x₀) : Path one_cs one_cs where
  toFun := fun t => ⟨g (p t) / g x₀, div_ne_zero (hgne _) (hgne _)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((hg.comp p.continuous_toFun).div_const _)
  source' := by
    apply Subtype.ext
    show g (p 0) / g x₀ = (1 : ℂ); rw [p.source]; exact div_self (hgne _)
  target' := by
    apply Subtype.ext
    show g (p 1) / g x₀ = (1 : ℂ); rw [p.target]; exact div_self (hgne _)

/-- The winding number of `g ∘ p` around `0`. -/
noncomputable def wind (g : X → ℂ) (hg : Continuous g) (hgne : ∀ x, g x ≠ 0)
    {x₀ : X} (p : Path x₀ x₀) : ℤ :=
  degZ ⟦transLoop g hg hgne p⟧

/-- **Winding is additive under pointwise products.** -/
theorem wind_mul (g h : X → ℂ) (hg : Continuous g) (hh : Continuous h)
    (hgne : ∀ x, g x ≠ 0) (hhne : ∀ x, h x ≠ 0) {x₀ : X} (p : Path x₀ x₀) :
    wind (fun x => g x * h x) (hg.mul hh) (fun x => mul_ne_zero (hgne x) (hhne x)) p
      = wind g hg hgne p + wind h hh hhne p := by
  have hpath : transLoop (fun x => g x * h x) (hg.mul hh)
      (fun x => mul_ne_zero (hgne x) (hhne x)) p
      = mulLoop (transLoop g hg hgne p) (transLoop h hh hhne p) := by
    apply Path.ext; funext t; apply Subtype.ext
    show g (p t) * h (p t) / (g x₀ * h x₀) = g (p t) / g x₀ * (h (p t) / h x₀)
    rw [div_mul_div_comm]
  show degZ ⟦transLoop (fun x => g x * h x) _ _ p⟧ = _
  rw [hpath, degZ_mulLoop]

/-- A constant loop has winding `0`. -/
theorem wind_const (a : ℂ) (ha : a ≠ 0) {x₀ : X} (p : Path x₀ x₀) :
    wind (fun _ => a) continuous_const (fun _ => ha) p = 0 := by
  have hpath : transLoop (fun _ => a) continuous_const (fun _ => ha) p = Path.refl one_cs := by
    apply Path.ext; funext t; apply Subtype.ext
    show a / a = (1 : ℂ); exact div_self ha
  show degZ ⟦transLoop (fun _ => a) _ _ p⟧ = 0
  rw [hpath, degZ_refl]

/-- **Winding of a pointwise power:** `wind (gᵏ) = k · wind g`. -/
theorem wind_pow (g : X → ℂ) (hg : Continuous g) (hgne : ∀ x, g x ≠ 0)
    (k : ℕ) {x₀ : X} (p : Path x₀ x₀) :
    wind (fun x => g x ^ k) (hg.pow k) (fun x => pow_ne_zero k (hgne x)) p
      = k * wind g hg hgne p := by
  have hpath : transLoop (fun x => g x ^ k) (hg.pow k) (fun x => pow_ne_zero k (hgne x)) p
      = powLoop k (transLoop g hg hgne p) := by
    apply Path.ext; funext t; apply Subtype.ext
    show g (p t) ^ k / g x₀ ^ k = ((powLoop k (transLoop g hg hgne p)) t : ℂ)
    rw [div_pow]
    -- `(transLoop g p t)^k` pointwise equals `powLoop k (transLoop g p) t`
    induction k with
    | zero => simp [powLoop]
    | succ k ih =>
      show (g (p t) / g x₀) ^ (k + 1) = ((mulLoop (transLoop g hg hgne p) (powLoop k _)) t : ℂ)
      show (g (p t) / g x₀) ^ (k + 1)
          = (g (p t) / g x₀) * ((powLoop k (transLoop g hg hgne p)) t : ℂ)
      rw [← ih, pow_succ]; ring
  show degZ ⟦transLoop (fun x => g x ^ k) _ _ p⟧ = _
  rw [hpath, degZ_powLoop]

/-- A factor whose transported loop stays in the right half-plane is windingless. -/
theorem wind_zero_of_re_pos (g : X → ℂ) (hg : Continuous g) (hgne : ∀ x, g x ≠ 0)
    {x₀ : X} (p : Path x₀ x₀) (hre : ∀ t : I, 0 < (g (p t) / g x₀).re) :
    wind g hg hgne p = 0 :=
  degZ_zero_of_re_pos _ (fun t => hre t)

/-- **`wind (exp ∘ M) = 0`** for any continuous `M`: the transported loop `exp(M∘p − M(x₀))` lifts to
the closed loop `M ∘ p − M(x₀)`, whose endpoints coincide. -/
theorem wind_exp (M : X → ℂ) (hM : Continuous M) {x₀ : X} (p : Path x₀ x₀) :
    wind (fun x => Complex.exp (M x)) (Complex.continuous_exp.comp hM)
      (fun x => Complex.exp_ne_zero (M x)) p = 0 := by
  set q : Path one_cs one_cs :=
    transLoop (fun x => Complex.exp (M x)) (Complex.continuous_exp.comp hM)
      (fun x => Complex.exp_ne_zero (M x)) p with hq
  set L : C(I, ℂ) := ⟨fun t => M (p t) - M x₀, by fun_prop⟩ with hLdef
  have hL : pexp ∘ L = q := by
    funext t; apply Subtype.ext
    show Complex.exp (M (p t) - M x₀) = Complex.exp (M (p t)) / Complex.exp (M x₀)
    rw [Complex.exp_sub]
  have h0 : L 0 = (e0 : ℂ) := by
    show M (p 0) - M x₀ = (e0 : ℂ); rw [p.source]; show M x₀ - M x₀ = (0 : ℂ); ring
  have hc : (degClass ⟦q⟧ : ℂ) = L 1 := degClass_eq_of_lift q L hL h0
  have h1 : (L : I → ℂ) 1 = 0 := by
    show M (p 1) - M x₀ = (0 : ℂ); rw [p.target]; ring
  rw [h1] at hc
  show degZ ⟦q⟧ = 0
  have hsp := degOfFiber_spec (degClass ⟦q⟧)
  have hzero : (degOfFiber (degClass ⟦q⟧) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) = 0 :=
    hsp.symm.trans hc
  have hz : (degOfFiber (degClass ⟦q⟧) : ℂ) = 0 :=
    (mul_eq_zero.mp hzero).resolve_right twopiI_ne_zero
  show fiberEquivInt _ = 0
  simp only [fiberEquivInt, Equiv.ofBijective_apply]
  exact_mod_cast hz

end Bottcher
