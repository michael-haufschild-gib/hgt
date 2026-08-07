import GaloisForLFunctions.RHTower.EMCarrier
import GaloisForLFunctions.RHTower.MollifierDetection
import GaloisForLFunctions.RHTower.ReflectionCocycleClass

/-!
# Zero detection: at a zeta zero the mollified detection polynomial is large

The Euler–Maclaurin carrier gives, unconditionally, for `N ≥ 1` and `0 < re s`, `s ≠ 1`,

```text
ζ(s) = Σ_{n ≤ N} n^(−s) + N^(1−s)/(s−1) − s · emTail N s ,      ‖emTail N s‖ ≤ N^(−re s)/re s .
```

Multiplying by the Möbius mollifier `M_y(s) = Σ_{m ≤ y} μ(m) m^(−s)` and using the convolution
identity for finite Dirichlet polynomials turns a zero of `ζ` into a lower bound for the *detection
polynomial*

```text
detPolyC N y s = Σ_k e_k k^(−s) ,      e_k = Σ_{ab = k, a ≤ N, b ≤ y} μ(b) − [k = 1] ,
```

namely `detPolyC N y ρ = M_y(ρ)·(remainder) − 1`, so that whenever the mollified remainder is at most
`1/2` in modulus the detection polynomial has modulus at least `1/2` at `ρ`.  This is the step that
converts an analytic statement about `ζ` into a large value of a *finite* Dirichlet polynomial — the
input a density argument consumes.

Everything here is unconditional and explicit: no asymptotics and no cited constants.
-/

open Complex Finset

namespace RHTower

noncomputable section

/-- A finite Dirichlet polynomial with real coefficients on an arbitrary index set, in the complex
variable. -/
def dpolyC (b : ℕ → ℝ) (S : Finset ℕ) : ℂ → ℂ :=
  fun s => ∑ n ∈ S, ((b n : ℝ) : ℂ) * (n : ℂ) ^ (-s)

theorem dpolyC_apply (b : ℕ → ℝ) (S : Finset ℕ) (s : ℂ) :
    dpolyC b S s = ∑ n ∈ S, ((b n : ℝ) : ℂ) * (n : ℂ) ^ (-s) := rfl

/-- The unit-coefficient instance is the Euler–Maclaurin carrier's Dirichlet block. -/
theorem dpolyC_one (N : ℕ) : dpolyC (fun _ => 1) (Finset.Icc 1 N) = dirichletPoly N := by
  funext s
  unfold dpolyC dirichletPoly
  simp

/-- Multiplicativity of `n ↦ n^(−s)` on positive naturals. -/
theorem natCast_mul_cpow_neg (a b : ℕ) (s : ℂ) :
    ((a * b : ℕ) : ℂ) ^ (-s) = (a : ℂ) ^ (-s) * (b : ℂ) ^ (-s) := by
  have h := mul_cpow_ofReal_nonneg (a := (a : ℝ)) (b := (b : ℝ))
    (Nat.cast_nonneg a) (Nat.cast_nonneg b) (-s)
  simpa using h

/-- **The convolution identity in the complex variable.**  The product of two finite Dirichlet
polynomials is the Dirichlet polynomial of their convolution on the product support. -/
theorem dpolyC_mul (a b : ℕ → ℝ) (S T : Finset ℕ) (s : ℂ) :
    dpolyC a S s * dpolyC b T s = dpolyC (dpolyConv a b S T) (prodSupport S T) s := by
  rw [dpolyC_apply, dpolyC_apply, Finset.sum_mul_sum, ← Finset.sum_product']
  have hmap : ∀ p ∈ S ×ˢ T, p.1 * p.2 ∈ prodSupport S T := fun p hp =>
    Finset.mem_image.mpr ⟨p, hp, rfl⟩
  rw [← Finset.sum_fiberwise_of_maps_to hmap
    (fun p => ((a p.1 : ℝ) : ℂ) * (p.1 : ℂ) ^ (-s) * (((b p.2 : ℝ) : ℂ) * (p.2 : ℂ) ^ (-s)))]
  rw [dpolyC_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hk : ((dpolyConv a b S T k : ℝ) : ℂ) * (k : ℂ) ^ (-s)
      = ∑ p ∈ (S ×ˢ T).filter (fun p => p.1 * p.2 = k),
          ((a p.1 * b p.2 : ℝ) : ℂ) * (k : ℂ) ^ (-s) := by
    unfold dpolyConv
    rw [Complex.ofReal_sum, Finset.sum_mul]
  rw [hk]
  refine Finset.sum_congr rfl fun p hp => ?_
  simp only [Finset.mem_filter] at hp
  obtain ⟨-, hprod⟩ := hp
  rw [← hprod, natCast_mul_cpow_neg]
  push_cast
  ring

/-- The Möbius mollifier in the complex variable. -/
def mollifierC (y : ℕ) : ℂ → ℂ := dpolyC moebiusCoeff (Finset.Icc 1 y)

/-- The detection polynomial in the complex variable: the convolution coefficients with the unit
removed. -/
def detPolyC (N y : ℕ) : ℂ → ℂ :=
  dpolyC (detCoeff N y) (prodSupport (Finset.Icc 1 N) (Finset.Icc 1 y))

/-- `1` lies in every product support built from `[1, N] × [1, y]` with `N, y ≥ 1`. -/
theorem one_mem_prodSupport {N y : ℕ} (hN : 1 ≤ N) (hy : 1 ≤ y) :
    (1 : ℕ) ∈ prodSupport (Finset.Icc 1 N) (Finset.Icc 1 y) := by
  rw [prodSupport, Finset.mem_image]
  exact ⟨(1, 1), by rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]; omega, by norm_num⟩

/-- **The detection polynomial is `D_N·M_y − 1` in the complex variable.**  This is the complex-`s`
form of `detection_poly_eq`; it needs only the definition of `detCoeff` as a convolution minus the
unit, not the Möbius cancellation. -/
theorem detPolyC_eq {N y : ℕ} (hN : 1 ≤ N) (hy : 1 ≤ y) (s : ℂ) :
    detPolyC N y s = dirichletPoly N s * mollifierC y s - 1 := by
  have hdc : detCoeff N y = fun k => dpolyConv (fun _ => (1 : ℝ)) moebiusCoeff
      (Finset.Icc 1 N) (Finset.Icc 1 y) k - (if k = 1 then (1 : ℝ) else 0) := rfl
  have hone : dpolyC (fun k => if k = 1 then (1 : ℝ) else 0)
      (prodSupport (Finset.Icc 1 N) (Finset.Icc 1 y)) s = 1 := by
    rw [dpolyC_apply, Finset.sum_eq_single (1 : ℕ)]
    · norm_num
    · intro k _ hk
      simp [hk]
    · intro h
      exact absurd (one_mem_prodSupport hN hy) h
  have hsplit : detPolyC N y s
      = dpolyC (dpolyConv (fun _ => (1 : ℝ)) moebiusCoeff (Finset.Icc 1 N) (Finset.Icc 1 y))
          (prodSupport (Finset.Icc 1 N) (Finset.Icc 1 y)) s
        - dpolyC (fun k => if k = 1 then (1 : ℝ) else 0)
          (prodSupport (Finset.Icc 1 N) (Finset.Icc 1 y)) s := by
    unfold detPolyC
    rw [hdc, dpolyC_apply, dpolyC_apply, dpolyC_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast
    ring
  rw [hsplit, hone, ← dpolyC_mul, dpolyC_one]
  rfl

/-! ### The detection inequality -/

/-- **Zero detection.**  At a zero of `ζ` in the right half plane the detection polynomial differs
from `−1` by exactly the mollified Euler–Maclaurin remainder:

`detPolyC N y ρ + 1 = M_y(ρ)·(−N^(1−ρ)/(ρ−1) + ρ·emTail N ρ)`. -/
theorem detPolyC_add_one_eq_of_zeta_eq_zero {N y : ℕ} (hN : 1 ≤ N) (hy : 1 ≤ y) {ρ : ℂ}
    (hσ : 0 < ρ.re) (hzero : riemannZeta ρ = 0) :
    detPolyC N y ρ + 1 = mollifierC y ρ * (-(emPole N ρ) + ρ * emTail N ρ) := by
  have hρ1 : ρ ≠ 1 := riemannZeta_zero_ne_one hzero
  have hrep := zeta_eq_emCarrier_sub hN hσ hρ1
  rw [hzero] at hrep
  have hD : dirichletPoly N ρ = -(emPole N ρ) + ρ * emTail N ρ := by
    unfold emCarrier at hrep
    linear_combination -hrep
  rw [detPolyC_eq hN hy, hD]
  ring

/-- The mollified remainder bound, entirely explicit. -/
theorem norm_detPolyC_add_one_le {N y : ℕ} (hN : 1 ≤ N) (hy : 1 ≤ y) {ρ : ℂ}
    (hσ : 0 < ρ.re) (hzero : riemannZeta ρ = 0) :
    ‖detPolyC N y ρ + 1‖ ≤
      ‖mollifierC y ρ‖ * (‖emPole N ρ‖ + ‖ρ‖ * (N : ℝ) ^ (-ρ.re) / ρ.re) := by
  have hρ1 : ρ ≠ 1 := riemannZeta_zero_ne_one hzero
  rw [detPolyC_add_one_eq_of_zeta_eq_zero hN hy hσ hzero, norm_mul]
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_neg, norm_mul, mul_div_assoc]
  have h := mul_le_mul_of_nonneg_left (norm_emTail_le hN hσ hρ1) (norm_nonneg ρ)
  linarith

/-- **The detection lower bound.**  If the mollified Euler–Maclaurin remainder at a zeta zero is at
most `1/2`, the detection polynomial has modulus at least `1/2` there.  This is the analytic input a
zero-density argument consumes: a zero of `ζ` becomes a large value of an explicit finite Dirichlet
polynomial. -/
theorem half_le_norm_detPolyC {N y : ℕ} (hN : 1 ≤ N) (hy : 1 ≤ y) {ρ : ℂ}
    (hσ : 0 < ρ.re) (hzero : riemannZeta ρ = 0)
    (hsmall : ‖mollifierC y ρ‖ * (‖emPole N ρ‖ + ‖ρ‖ * (N : ℝ) ^ (-ρ.re) / ρ.re) ≤ 1 / 2) :
    1 / 2 ≤ ‖detPolyC N y ρ‖ := by
  have hb := le_trans (norm_detPolyC_add_one_le hN hy hσ hzero) hsmall
  have htri : (1 : ℝ) ≤ ‖detPolyC N y ρ + 1‖ + ‖detPolyC N y ρ‖ := by
    have h := norm_sub_le (detPolyC N y ρ + 1) (detPolyC N y ρ)
    simpa using h
  linarith

/-! ### Making the hypothesis explicit -/

/-- The mollifier is dominated by the corresponding real Dirichlet sum, since `|μ(m)| ≤ 1`. -/
theorem norm_mollifierC_le (y : ℕ) (s : ℂ) :
    ‖mollifierC y s‖ ≤ ∑ m ∈ Finset.Icc 1 y, (m : ℝ) ^ (-s.re) := by
  unfold mollifierC dpolyC
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun m hm => ?_)
  have hm1 : 0 < m := (Finset.mem_Icc.mp hm).1
  rw [norm_mul, Complex.norm_real, Complex.norm_natCast_cpow_of_pos hm1]
  have hpow : (0 : ℝ) ≤ (m : ℝ) ^ ((-s).re) := Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hmu : |moebiusCoeff m| ≤ 1 := abs_moebiusCoeff_le_one m
  calc |moebiusCoeff m| * (m : ℝ) ^ ((-s).re)
      ≤ 1 * (m : ℝ) ^ ((-s).re) := mul_le_mul_of_nonneg_right hmu hpow
    _ = (m : ℝ) ^ (-s.re) := by rw [one_mul]; norm_num

/-- The Euler–Maclaurin pole term has modulus `N^(1 − re s)/‖s − 1‖`. -/
theorem norm_emPole {N : ℕ} (hN : 0 < N) (s : ℂ) :
    ‖emPole N s‖ = (N : ℝ) ^ (1 - s.re) / ‖s - 1‖ := by
  unfold emPole
  rw [norm_div, Complex.norm_natCast_cpow_of_pos hN]
  norm_num

/-- **The detection criterion with every quantity explicit.**  At a zero of `ζ` with `0 < re ρ`, if

`(Σ_{m ≤ y} m^(−re ρ)) · (N^(1−re ρ)/‖ρ−1‖ + ‖ρ‖·N^(−re ρ)/re ρ)  ≤  1/2`

then the finite Dirichlet polynomial `detPolyC N y` has modulus at least `1/2` at `ρ`.  Every factor
is elementary in `N`, `y`, `re ρ` and `‖ρ‖`; no analytic input beyond the Euler–Maclaurin carrier is
used. -/
theorem half_le_norm_detPolyC_of_explicit {N y : ℕ} (hN : 1 ≤ N) (hy : 1 ≤ y) {ρ : ℂ}
    (hσ : 0 < ρ.re) (hzero : riemannZeta ρ = 0)
    (hsmall : (∑ m ∈ Finset.Icc 1 y, (m : ℝ) ^ (-ρ.re))
        * ((N : ℝ) ^ (1 - ρ.re) / ‖ρ - 1‖ + ‖ρ‖ * (N : ℝ) ^ (-ρ.re) / ρ.re) ≤ 1 / 2) :
    1 / 2 ≤ ‖detPolyC N y ρ‖ := by
  refine half_le_norm_detPolyC hN hy hσ hzero (le_trans ?_ hsmall)
  have hrem : 0 ≤ ‖emPole N ρ‖ + ‖ρ‖ * (N : ℝ) ^ (-ρ.re) / ρ.re := by
    have h1 : (0 : ℝ) ≤ ‖ρ‖ * (N : ℝ) ^ (-ρ.re) / ρ.re := by positivity
    have h2 : (0 : ℝ) ≤ ‖emPole N ρ‖ := norm_nonneg _
    linarith
  have heq : ‖emPole N ρ‖ + ‖ρ‖ * (N : ℝ) ^ (-ρ.re) / ρ.re
      = (N : ℝ) ^ (1 - ρ.re) / ‖ρ - 1‖ + ‖ρ‖ * (N : ℝ) ^ (-ρ.re) / ρ.re := by
    rw [norm_emPole (lt_of_lt_of_le Nat.zero_lt_one hN)]
  rw [← heq]
  exact mul_le_mul_of_nonneg_right (norm_mollifierC_le y ρ) hrem

/-- The same bound in the form used downstream: a zero with `re ρ ≥ σ` and the remainder controlled
gives a detecting value of size `1/2`. -/
theorem exists_detection_value {N y : ℕ} (hN : 1 ≤ N) (hy : 1 ≤ y) {σ : ℝ} {ρ : ℂ}
    (hσ0 : 0 < σ) (hρσ : σ ≤ ρ.re) (hzero : riemannZeta ρ = 0)
    (hsmall : ‖mollifierC y ρ‖ * (‖emPole N ρ‖ + ‖ρ‖ * (N : ℝ) ^ (-ρ.re) / ρ.re) ≤ 1 / 2) :
    ∃ V : ℝ, 0 < V ∧ V ≤ ‖detPolyC N y ρ‖ :=
  ⟨1 / 2, by norm_num, half_le_norm_detPolyC hN hy (lt_of_lt_of_le hσ0 hρσ) hzero hsmall⟩


/-! ### The parameter range: the criterion is satisfiable for every `σ > 1/2`

The two requirements pull against each other.  Smallness of the Euler–Maclaurin remainder needs
`N^σ ≳ S·T`, while smallness of the pole term needs `S·N^{1−σ} ≲ T`, where `S` bounds the mollifier
sum.  Writing `S ≈ T^α`, the two are compatible exactly when

```text
(α + 1)/σ  ≤  (1 − α)/(1 − σ)   ⟺   α ≤ 2σ − 1 ,
```

which is a nonempty range for **every** `σ > 1/2`, shrinking to a point as `σ → 1/2⁺`.  The lemma
below is the pointwise half of that statement: it discharges the criterion from the two separated
inequalities, uniformly over the zero's exact abscissa. -/

/-- **Monotone transfer to the abscissa `σ`.**  Every factor of the detection criterion is
monotone in `re ρ`, so the criterion at `re ρ ≥ σ` follows from the corresponding bounds stated at
`σ` alone. -/
theorem detection_remainder_le_half {N y : ℕ} {σ T S : ℝ} {ρ : ℂ}
    (hN : 1 ≤ N) (_hy : 1 ≤ y)
    (hσ0 : 0 < σ) (_hσ1 : σ ≤ 1) (hρσ : σ ≤ ρ.re)
    (hT0 : 0 < T) (hγ : T ≤ ‖ρ - 1‖) (hnorm : ‖ρ‖ ≤ 2 * T)
    (hS : (∑ m ∈ Finset.Icc 1 y, (m : ℝ) ^ (-σ)) ≤ S) (hS1 : 1 ≤ S)
    (hA : S * (N : ℝ) ^ (1 - σ) ≤ T / 4)
    (hB : S * (2 * T) * (N : ℝ) ^ (-σ) / σ ≤ 1 / 4) :
    (∑ m ∈ Finset.Icc 1 y, (m : ℝ) ^ (-ρ.re))
        * ((N : ℝ) ^ (1 - ρ.re) / ‖ρ - 1‖ + ‖ρ‖ * (N : ℝ) ^ (-ρ.re) / ρ.re) ≤ 1 / 2 := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hρ0 : 0 < ρ.re := lt_of_lt_of_le hσ0 hρσ
  -- the mollifier sum decreases in the abscissa
  have hsum : (∑ m ∈ Finset.Icc 1 y, (m : ℝ) ^ (-ρ.re)) ≤ S := by
    refine le_trans (Finset.sum_le_sum fun m hm => ?_) hS
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hm).1
    exact Real.rpow_le_rpow_of_exponent_le hm1 (by linarith)
  have hsum0 : 0 ≤ ∑ m ∈ Finset.Icc 1 y, (m : ℝ) ^ (-ρ.re) :=
    Finset.sum_nonneg fun m _ => Real.rpow_nonneg (Nat.cast_nonneg m) _
  -- the pole factor
  have hpow1 : (N : ℝ) ^ (1 - ρ.re) ≤ (N : ℝ) ^ (1 - σ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hnormpos : 0 < ‖ρ - 1‖ := lt_of_lt_of_le hT0 hγ
  have hpole : (N : ℝ) ^ (1 - ρ.re) / ‖ρ - 1‖ ≤ (N : ℝ) ^ (1 - σ) / T := by
    have h0 : (0:ℝ) ≤ (N : ℝ) ^ (1 - σ) := Real.rpow_nonneg (le_trans zero_le_one hN1) _
    gcongr
  -- the tail factor
  have hpow2 : (N : ℝ) ^ (-ρ.re) ≤ (N : ℝ) ^ (-σ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hpow2nn : 0 ≤ (N : ℝ) ^ (-ρ.re) := Real.rpow_nonneg (le_trans zero_le_one hN1) _
  have htail : ‖ρ‖ * (N : ℝ) ^ (-ρ.re) / ρ.re ≤ (2 * T) * (N : ℝ) ^ (-σ) / σ := by
    have hnum : ‖ρ‖ * (N : ℝ) ^ (-ρ.re) ≤ (2 * T) * (N : ℝ) ^ (-σ) :=
      mul_le_mul hnorm hpow2 hpow2nn (by linarith)
    have hnum0 : 0 ≤ (2 * T) * (N : ℝ) ^ (-σ) :=
      mul_nonneg (by linarith) (Real.rpow_nonneg (le_trans zero_le_one hN1) _)
    gcongr
  -- combine
  have hbrk : (N : ℝ) ^ (1 - ρ.re) / ‖ρ - 1‖ + ‖ρ‖ * (N : ℝ) ^ (-ρ.re) / ρ.re
      ≤ (N : ℝ) ^ (1 - σ) / T + (2 * T) * (N : ℝ) ^ (-σ) / σ := by linarith
  have hbrk0 : 0 ≤ (N : ℝ) ^ (1 - ρ.re) / ‖ρ - 1‖ + ‖ρ‖ * (N : ℝ) ^ (-ρ.re) / ρ.re := by
    have h1 : 0 ≤ (N : ℝ) ^ (1 - ρ.re) / ‖ρ - 1‖ :=
      div_nonneg (Real.rpow_nonneg (le_trans zero_le_one hN1) _) hnormpos.le
    have h2 : 0 ≤ ‖ρ‖ * (N : ℝ) ^ (-ρ.re) / ρ.re := by positivity
    linarith
  have hSbrk : S * ((N : ℝ) ^ (1 - σ) / T + (2 * T) * (N : ℝ) ^ (-σ) / σ) ≤ 1 / 2 := by
    have hA' : S * ((N : ℝ) ^ (1 - σ) / T) ≤ 1 / 4 := by
      rw [mul_div_assoc'] at *
      exact (div_le_iff₀ hT0).mpr (by linarith)
    have hB' : S * ((2 * T) * (N : ℝ) ^ (-σ) / σ) ≤ 1 / 4 := by
      rw [← mul_div_assoc, ← mul_assoc]
      exact hB
    linarith
  calc (∑ m ∈ Finset.Icc 1 y, (m : ℝ) ^ (-ρ.re))
        * ((N : ℝ) ^ (1 - ρ.re) / ‖ρ - 1‖ + ‖ρ‖ * (N : ℝ) ^ (-ρ.re) / ρ.re)
      ≤ S * ((N : ℝ) ^ (1 - σ) / T + (2 * T) * (N : ℝ) ^ (-σ) / σ) :=
        mul_le_mul hsum hbrk hbrk0 (by linarith)
    _ ≤ 1 / 2 := hSbrk

/-- **Detection at every zero of the box, from two separated inequalities.**  Combining the
monotone transfer with the explicit criterion: under the two `σ`-level bounds, every zeta zero with
`re ρ ≥ σ` and `T ≤ ‖ρ − 1‖`, `‖ρ‖ ≤ 2T` gives a detecting value. -/
theorem half_le_norm_detPolyC_of_box {N y : ℕ} {σ T S : ℝ} {ρ : ℂ}
    (hN : 1 ≤ N) (hy : 1 ≤ y)
    (hσ0 : 0 < σ) (hσ1 : σ ≤ 1) (hρσ : σ ≤ ρ.re)
    (hT0 : 0 < T) (hγ : T ≤ ‖ρ - 1‖) (hnorm : ‖ρ‖ ≤ 2 * T)
    (hS : (∑ m ∈ Finset.Icc 1 y, (m : ℝ) ^ (-σ)) ≤ S) (hS1 : 1 ≤ S)
    (hA : S * (N : ℝ) ^ (1 - σ) ≤ T / 4)
    (hB : S * (2 * T) * (N : ℝ) ^ (-σ) / σ ≤ 1 / 4)
    (hzero : riemannZeta ρ = 0) :
    1 / 2 ≤ ‖detPolyC N y ρ‖ :=
  half_le_norm_detPolyC_of_explicit hN hy (lt_of_lt_of_le hσ0 hρσ) hzero
    (detection_remainder_le_half hN hy hσ0 hσ1 hρσ hT0 hγ hnorm hS hS1 hA hB)



/-- **The two requirements are compatible exactly when `σ > 1/2`.**  Taking
`x = (8ST/σ)^{1/σ}` makes the tail requirement an exact equality and turns the pole requirement into
`4S(8S/σ)^{(1−σ)/σ} ≤ T^{(2σ−1)/σ}`, whose exponent `(2σ−1)/σ` is positive precisely for `σ > 1/2`.
So for every `σ > 1/2` the admissible range is nonempty once `T` is large; it shrinks as `σ → 1/2⁺`
but is never empty. -/
theorem exists_length_detection {σ T S : ℝ} (hσ : 1 / 2 < σ) (hσ1 : σ < 1)
    (hS1 : 1 ≤ S) (hT0 : 0 < T) (hbase1 : 1 ≤ 8 * S * T / σ)
    (hbig : 4 * S * (8 * S / σ) ^ ((1 - σ) / σ) ≤ T ^ ((2 * σ - 1) / σ)) :
    ∃ x : ℝ, 1 ≤ x ∧ S * x ^ (1 - σ) ≤ T / 4 ∧ S * (2 * T) * x ^ (-σ) / σ ≤ 1 / 4 := by
  have hσ0 : 0 < σ := by linarith
  have hS0 : 0 < S := by linarith
  have hbase : (0 : ℝ) < 8 * S * T / σ := by positivity
  refine ⟨(8 * S * T / σ) ^ (1 / σ), ?_, ?_, ?_⟩
  · have h := Real.rpow_le_rpow_of_exponent_le hbase1
      (show (0 : ℝ) ≤ 1 / σ by positivity)
    simpa using h
  · have hexp : ((8 * S * T / σ) ^ (1 / σ)) ^ (1 - σ)
        = (8 * S * T / σ) ^ ((1 - σ) / σ) := by
      rw [← Real.rpow_mul hbase.le]
      congr 1
      field_simp
    have hsplit : (8 : ℝ) * S * T / σ = (8 * S / σ) * T := by ring
    rw [hexp, hsplit, Real.mul_rpow (by positivity) hT0.le]
    have hpos : (0 : ℝ) < T ^ ((1 - σ) / σ) := Real.rpow_pos_of_pos hT0 _
    have hTexp : T ^ ((2 * σ - 1) / σ) * T ^ ((1 - σ) / σ) = T := by
      rw [← Real.rpow_add hT0]
      have hsum : (2 * σ - 1) / σ + (1 - σ) / σ = 1 := by field_simp; ring
      rw [hsum, Real.rpow_one]
    have key := mul_le_mul_of_nonneg_right hbig hpos.le
    rw [hTexp] at key
    have hrw : S * ((8 * S / σ) ^ ((1 - σ) / σ) * T ^ ((1 - σ) / σ))
        = (4 * S * (8 * S / σ) ^ ((1 - σ) / σ) * T ^ ((1 - σ) / σ)) / 4 := by ring
    rw [hrw]
    linarith
  · have hinv : ((8 * S * T / σ) ^ (1 / σ)) ^ (-σ) = (8 * S * T / σ)⁻¹ := by
      rw [← Real.rpow_mul hbase.le]
      have hne : 1 / σ * -σ = -1 := by field_simp
      rw [hne, Real.rpow_neg_one]
    have hval : S * (2 * T) * ((8 * S * T / σ)⁻¹) / σ = 1 / 4 := by
      field_simp
      ring
    rw [hinv, hval]

end

end RHTower
