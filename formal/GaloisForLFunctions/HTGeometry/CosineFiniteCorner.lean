import GaloisForLFunctions.HTGeometry.CosineRamifiedInverse
import GaloisForLFunctions.HTGeometry.CosineTwoPoleCorner

/-! # The conic corner with one finite coordinate and one pole

The finite cosine coordinate and a logarithmic pole coordinate give a
scalar analytic submersion. Exact integer periods specialize its branch
to the original conic, with no growth or remainder estimate.
-/

namespace GaloisForLFunctions.HTGeometry.CosineFiniteCorner

open Complex Filter
open CosineTwoPoleCorner (small argument exponential_pole_lift)
open scoped Topology

noncomputable section

def equation (u β : ℂ → ℂ) (m : ℕ) (c : ℂ) (p : (ℂ × ℂ) × ℂ) : ℂ :=
  4 * Real.pi * (u (small p) - I * argument β m p) +
    p.1.1 * (u (small p) ^ 2 + argument β m p ^ 2 - c)

def center (u β : ℂ → ℂ) (m : ℕ) : ℂ := (β 0 - u 0) / m

theorem equation_corner (u β : ℂ → ℂ) (m : ℕ) (c ell : ℂ) :
    equation u β m c ((0, 0), ell) = 4 * Real.pi * (u 0 + (m : ℂ) * ell - β 0) := by
  simp only [equation, small, argument, zero_mul, add_zero]
  ring_nf
  simp only [I_sq]
  ring

theorem equation_analyticAt {u β : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) (hβ : AnalyticAt ℂ β 0) (m : ℕ) (c ell : ℂ) :
    AnalyticAt ℂ (equation u β m c) ((0, 0), ell) := by
  have hs : AnalyticAt ℂ small ((0, 0), ell) :=
    (analyticAt_snd.comp (f := Prod.fst) analyticAt_fst).mul
      ((Complex.differentiable_exp.analyticAt ell).comp
        (f := fun p : (ℂ × ℂ) × ℂ => p.2) analyticAt_snd)
  have hu' : AnalyticAt ℂ u (small ((0, 0), ell)) := by simpa [small] using hu
  have huc := hu'.comp hs
  have hv := CosineTwoPoleCorner.argument_analyticAt hβ m ell
  have ht : AnalyticAt ℂ (fun p : (ℂ × ℂ) × ℂ => p.1.1) ((0, 0), ell) :=
    analyticAt_fst.comp (f := Prod.fst) analyticAt_fst
  exact (analyticAt_const.mul (huc.sub (analyticAt_const.mul hv))).add
    (ht.mul (((huc.pow 2).add (hv.pow 2)).sub analyticAt_const))

theorem exists_corner {u β : ℂ → ℂ}
    (hu : AnalyticAt ℂ u 0) (hβ : AnalyticAt ℂ β 0) (m : ℕ) (hm : 0 < m) (c : ℂ) :
    ∃ ell : ℂ × ℂ → ℂ, AnalyticAt ℂ ell (0, 0) ∧ ell (0, 0) = center u β m ∧
      ∀ᶠ p in 𝓝 (0, 0), equation u β m c (p, ell p) = 0 := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hm
  have hf := equation_analyticAt hu hβ m c (center u β m)
  have hroot : equation u β m c ((0, 0), center u β m) = 0 := by
    rw [equation_corner, center, mul_div_cancel₀ _ hm']
    ring
  have hd : HasDerivAt (fun z : ℂ => equation u β m c ((0, 0), z))
      (4 * Real.pi * m) (center u β m) := by
    simp_rw [equation_corner]
    simpa using ((((hasDerivAt_id (center u β m)).const_mul (m : ℂ)).const_add
      (u 0)).sub_const (β 0)).const_mul (4 * (Real.pi : ℂ))
  have hi : HasFDerivAt (fun z : ℂ => ((0, 0), z))
      (ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ) (center u β m) := by
    convert! ((ContinuousLinearMap.inr ℂ (ℂ × ℂ) ℂ).hasFDerivAt (x := center u β m)) using 1
  have hc := hf.differentiableAt.hasFDerivAt.comp (center u β m) hi
  have he := congrArg (fun L : ℂ →L[ℂ] ℂ => L 1) (hc.unique hd.hasFDerivAt)
  apply parametric_holo_implicit hf hroot
  have he' : (fderiv ℂ (equation u β m c) ((0, 0), center u β m)) (0, 1) =
      4 * Real.pi * m := by simpa using he
  rw [he']
  exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)) hm'

def parameters (m n : ℕ) : ℂ × ℂ :=
  ((n : ℂ)⁻¹, exp (-(n : ℂ) * (2 * Real.pi) / m))

def firstLift (u : ℂ → ℂ) (m n : ℕ) (ell : ℂ) : ℂ :=
  n * (2 * Real.pi) + u (small (parameters m n, ell))

def secondLift (β : ℂ → ℂ) (m n : ℕ) (ell : ℂ) : ℂ :=
  -I * n * (2 * Real.pi) + argument β m (parameters m n, ell)

theorem firstLift_cos (u : ℂ → ℂ) (m n : ℕ) (ell : ℂ) :
    cos (firstLift u m n ell) = cos (u (small (parameters m n, ell))) := by
  rw [firstLift, add_comm]
  exact Complex.cos_add_nat_mul_two_pi _ n

theorem secondLift_exp (β : ℂ → ℂ) (m n : ℕ) (hm : 0 < m) (ell : ℂ) :
    exp (secondLift β m n ell * I) =
      exp (β (small (parameters m n, ell))) / small (parameters m n, ell) ^ m := by
  have hm' : (m : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hm
  have h := exponential_pole_lift ((n : ℂ) * (2 * Real.pi) / m) ell
    (β (small (parameters m n, ell))) 0 m
  convert! h using 1
  · congr 1
    dsimp [secondLift, argument]
    norm_num only [Int.cast_zero, mul_zero, zero_add]
    field_simp
    ring
  · simp only [small, parameters, neg_div, neg_mul]

theorem conic_of_equation {u β : ℂ → ℂ} {m n : ℕ} {c ell : ℂ}
    (hn : 0 < n) (he : equation u β m c (parameters m n, ell) = 0) :
    firstLift u m n ell ^ 2 + secondLift β m n ell ^ 2 = c := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast Nat.ne_zero_of_lt hn
  let a := u (small (parameters m n, ell))
  let b := argument β m (parameters m n, ell)
  change 4 * Real.pi * (a - I * b) + (n : ℂ)⁻¹ * (a ^ 2 + b ^ 2 - c) = 0 at he
  have hh := congrArg (fun z : ℂ => (n : ℂ) * z) he
  simp only [mul_add, ← mul_assoc, mul_inv_cancel₀ hn', one_mul, mul_zero] at hh
  change ((n : ℂ) * (2 * Real.pi) + a) ^ 2 + (-I * n * (2 * Real.pi) + b) ^ 2 = c
  linear_combination hh + ((n : ℂ) * (2 * Real.pi)) ^ 2 * I_sq

end

end GaloisForLFunctions.HTGeometry.CosineFiniteCorner
