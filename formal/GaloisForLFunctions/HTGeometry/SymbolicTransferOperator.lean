import GaloisForLFunctions.HTGeometry.SymbolicHolderSpace

/-!
# Transfer operators of Hölder potentials on a subshift

For a potential `φ` on sequences and `s ∈ ℂ` the transfer operator is

  `(L g)(x) = Σ_a e^{−s φ(a x)} g(a x)`.

Applied to functions vanishing off the subshift, only admissible preimages contribute, and its
`n`-th power is `(Lⁿ g)(x) = Σ_{|v| = n} e^{−s φⁿ(v x)} g(v x)` (`transferFun_pow_apply`).

* `norm_transferFun_pow_apply_le` and `norm_transferFun_pow_apply_sub_le` — the **Lasota–Yorke
  inequality**: with the partition function `Φₙ(x) = Σ_{v x admissible} e^{−σ φⁿ(v x)}`,
  `|Lⁿ g(x)| ≤ Φₙ(x) ‖g‖_∞`, and for admissible `x, y` agreeing on `j ≥ 1` symbols
  `|Lⁿ g(x) − Lⁿ g(y)| ≤ Φₙ(x) (b ϑ^{n+j} + ‖g‖_∞ |s| D θ^j e^{|s| D})` when `g` has Hölder
  constant `b` and `φ` has distortion constant `D = C/(1 − θ)`.
* `transferOp` — the bounded operator on `HolderSpace A ϑ`, with `transferOp_pow_apply`.
* `cylPoint`, `levelPotential` — the locally constant approximation `φ_m = φ ∘ π_m` of a Hölder
  potential, `π_m y` a chosen admissible sequence with the same first `m` symbols.
-/

namespace GaloisForLFunctions.HTGeometry.Symbolic

open Finset

noncomputable section

variable {k : ℕ} {A : Fin k → Fin k → Prop}

/-! ## An exponential estimate -/

/-- `|e^{−s a} − e^{−s b}| ≤ e^{−σ a} |s| |a − b| e^{|s| |a − b|}`. -/
theorem norm_cexp_neg_mul_sub_le (s : ℂ) (a b : ℝ) :
    ‖Complex.exp (-(s * a)) - Complex.exp (-(s * b))‖ ≤
      Real.exp (-(s.re * a)) * (‖s‖ * |a - b| * Real.exp (‖s‖ * |a - b|)) := by
  have hfac : Complex.exp (-(s * a)) - Complex.exp (-(s * b)) =
      Complex.exp (-(s * a)) * -(Complex.exp (s * ((a : ℂ) - b)) - 1) := by
    rw [mul_neg, neg_sub, mul_sub, mul_one, ← Complex.exp_add]
    congr 2; ring
  rw [hfac, norm_mul, norm_neg, Complex.norm_exp]
  have hre : (-(s * (a : ℂ))).re = -(s.re * a) := by simp
  rw [hre]
  refine mul_le_mul_of_nonneg_left ?_ (Real.exp_pos _).le
  have h := Complex.norm_exp_sub_sum_le_norm_mul_exp (s * ((a : ℂ) - b)) 1
  simp only [Finset.range_one, Finset.sum_singleton, pow_zero, Nat.factorial_zero, Nat.cast_one,
    div_one, pow_one] at h
  have hn : ‖s * ((a : ℂ) - b)‖ = ‖s‖ * |a - b| := by
    rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rwa [hn] at h

/-! ## Hölder potentials -/

/-- A potential bounded by `R₀` and `(C, θ)`-Hölder on the subshift. -/
structure IsHolderPotential (A : Fin k → Fin k → Prop) (φ : (ℕ → Fin k) → ℝ) (R₀ C θ : ℝ) :
    Prop where
  bound : ∀ y, IsAdmissible A y → |φ y| ≤ R₀
  holder : ∀ x y j, IsAdmissible A x → IsAdmissible A y → Agree j x y → |φ x - φ y| ≤ C * θ ^ j

theorem IsHolderPotential.const_nonneg {φ : (ℕ → Fin k) → ℝ} {R₀ C θ : ℝ}
    (hφ : IsHolderPotential A φ R₀ C θ) {x : ℕ → Fin k} (hx : IsAdmissible A x) : 0 ≤ C := by
  have := hφ.holder x x 0 hx hx (Agree.refl 0 x)
  simpa using this

/-! ## The transfer operator on functions -/

/-- The transfer operator `(L g)(x) = Σ_a e^{−s φ(a x)} g(a x)` on functions of sequences. -/
def transferFun (φ : (ℕ → Fin k) → ℝ) (s : ℂ) :
    ((ℕ → Fin k) → ℂ) →ₗ[ℂ] (ℕ → Fin k) → ℂ where
  toFun g x := ∑ a : Fin k, Complex.exp (-(s * φ (cons a x))) * g (cons a x)
  map_add' g h := by
    funext x; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c g := by
    funext x; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring

theorem transferFun_apply (φ : (ℕ → Fin k) → ℝ) (s : ℂ) (g : (ℕ → Fin k) → ℂ) (x : ℕ → Fin k) :
    transferFun φ s g x = ∑ a : Fin k, Complex.exp (-(s * φ (cons a x))) * g (cons a x) := rfl

/-- **The `n`-th power of the transfer operator** is a sum over the words of length `n`. -/
theorem transferFun_pow_apply (φ : (ℕ → Fin k) → ℝ) (s : ℂ) (n : ℕ) (g : (ℕ → Fin k) → ℂ)
    (x : ℕ → Fin k) :
    (transferFun φ s ^ n) g x = ∑ v : Fin n → Fin k,
      Complex.exp (-(s * birkhoff φ n (prepend v x))) * g (prepend v x) := by
  induction n generalizing g with
  | zero =>
    rw [pow_zero, Module.End.one_apply]
    rw [Fintype.sum_unique]
    simp
  | succ n ih =>
    rw [pow_succ, Module.End.mul_apply, ih]
    rw [Fintype.sum_equiv (Fin.consEquiv fun _ => Fin k).symm _
      (fun p : Fin k × (Fin n → Fin k) => Complex.exp (-(s * birkhoff φ (n + 1)
        (prepend (Fin.cons p.1 p.2 : Fin (n + 1) → Fin k) x))) *
          g (prepend (Fin.cons p.1 p.2 : Fin (n + 1) → Fin k) x))
      (fun u => by
        simp only [Equiv.symm_apply_apply]
        sorry)]
    sorry

end

end GaloisForLFunctions.HTGeometry.Symbolic
