import GaloisForLFunctions.GaloisTheoryOfZeros.TheHeatCoverOfTheZeros
import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch

/-!
# The Hermite monodromy of a collision

Let `(τ₀, z₀)` be a collision of exact order `m` of the heat family: at the complex time `τ₀` the
function `H_τ₀` vanishes at `z₀` to order exactly `m`. Every zero of the family is a collision of
some order `m ≥ 1` (`exists_isCollision`). The Hermite profile `Q_m` has `m` simple real roots,
symmetric under `ρ ↦ −ρ`. On the double cover `τ = τ₀ + s²` the cover of zeros is unramified:

* **Sheets** (`collisionBranch_spec`, `complexHeat_collisionZero`). Through every root `ρ` passes
  one analytic branch `y_ρ` of zeros of the blow-up, `y_ρ(0) = ρ`. The point
  `Z_ρ(s) = z₀ + s y_ρ(s)` is a zero of `H_{τ₀+s²}`, and the `m` points are distinct for small
  `s ≠ 0` (`collisionZero_ne`).
* **Monodromy** (`collisionZero_neg`). `Z_ρ(−s) = Z_{−ρ}(s)`. One turn of `τ` around `τ₀` is
  `s ↦ −s`, so the local monodromy is the reflection `ρ ↦ −ρ` of the Hermite roots: `⌊m/2⌋`
  disjoint transpositions, with the fixed sheet `ρ = 0` exactly when `m` is odd
  (`heatModelFwd_zero_eq_zero_iff`).
* **Conjugation** (`collisionZero_conj`). Conjugation carries the sheet `ρ` at `(τ₀, z₀)` to the
  sheet `ρ` at the conjugate collision, `conj Z_ρ(s) = Z'_ρ(conj s)`.
* **Reflection** (`collisionZero_reflect`). The functional equation `z ↦ −z` carries the sheet `ρ`
  at `z₀` to the sheet `−ρ` at `−z₀`.

At a real collision (real time, real place) conjugation preserves the collision. After it (`s`
real) all `m` zeros are real (`collisionZero_ofReal_im`). Before it (`s = iσ`) conjugation carries
the sheet `ρ` to the sheet `−ρ` (`conj_collisionZero_I_mul`), and the zeros on the sheets `ρ ≠ 0`
are not real (`collisionZero_I_mul_im_ne_zero`): conjugation acts as the local monodromy.

At a collision at the centre `z₀ = 0` the order is even and the functional equation acts as the
local monodromy, `−Z_ρ(s) = Z_ρ(−s)` (`neg_collisionZero_center`). Before a real central collision
the three involutions agree on the colliding zeros, which lie on the imaginary axis
(`collisionZero_center_I_mul_re`).

The branches come from the analytic implicit function theorem applied to the blow-up `G` at
`(0, ρ)`, where `∂_y G = (a/m!) Q_m'(ρ) ≠ 0`. The laws follow from the symmetries of `G` and the
uniqueness of continuous branches.
-/

open Complex Filter Topology Set Metric
open RHTower RHTower.DeBruijn GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

namespace GaloisForLFunctions.GaloisTheoryOfZeros

noncomputable section
set_option autoImplicit false

/-! ## The Hermite profile has simple real roots -/

/-- The profile `Q_m` as a polynomial. -/
def profilePolynomial (m : ℕ) : Polynomial ℂ :=
  ∑ j ∈ Finset.range (m / 2 + 1),
    Polynomial.C ((-1 : ℂ) ^ j * (m.factorial : ℂ) /
      ((j.factorial : ℂ) * ((m - 2 * j).factorial : ℂ))) * Polynomial.X ^ (m - 2 * j)

theorem eval_profilePolynomial (m : ℕ) (σ : ℂ) :
    (profilePolynomial m).eval σ = heatModelFwd m σ := by
  simp only [profilePolynomial, heatModelFwd, Polynomial.eval_finsetSum, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

theorem differentiable_heatModelFwd (m : ℕ) : Differentiable ℂ (heatModelFwd m) := by
  rw [show heatModelFwd m = fun σ => (profilePolynomial m).eval σ from
    funext fun σ => (eval_profilePolynomial m σ).symm]
  exact Polynomial.differentiable _

theorem natDegree_profilePolynomial_le (m : ℕ) : (profilePolynomial m).natDegree ≤ m :=
  Polynomial.natDegree_sum_le_of_forall_le _ _ fun _ _ =>
    (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.sub_le _ _)

theorem coeff_profilePolynomial_top (m : ℕ) : (profilePolynomial m).coeff m = 1 := by
  rw [profilePolynomial, Polynomial.finsetSum_coeff, Finset.sum_eq_single 0]
  · have hm : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
    rw [Polynomial.coeff_C_mul_X_pow, if_pos (by omega)]
    simp [hm]
  · intro j hj hj0
    have := Finset.mem_range.mp hj
    rw [Polynomial.coeff_C_mul_X_pow, if_neg (by omega)]
  · intro h
    exact absurd (Finset.mem_range.mpr (Nat.succ_pos _)) h

theorem profilePolynomial_ne_zero (m : ℕ) : profilePolynomial m ≠ 0 := fun h => by
  have h1 := coeff_profilePolynomial_top m
  rw [h, Polynomial.coeff_zero] at h1
  exact zero_ne_one h1

theorem heatModelFwd_profileRoot {m : ℕ} {r : ℝ} (hr : r ∈ profileRoots m) :
    heatModelFwd m (r : ℂ) = 0 := by
  rw [heatModelFwd_ofReal, heatPoly_eq_zero_of_mem hr, Complex.ofReal_zero]

/-- The profile has exactly the `m` real roots `profileRoots m`, each simple. -/
theorem roots_profilePolynomial (m : ℕ) :
    (profilePolynomial m).roots = ((profileRoots m).image fun r : ℝ => (r : ℂ)).val := by
  classical
  have hP := profilePolynomial_ne_zero m
  have hsub : ((profileRoots m).image fun r : ℝ => (r : ℂ)).val ≤ (profilePolynomial m).roots := by
    rw [Multiset.le_iff_subset (Finset.nodup _)]
    intro τ hτ
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp (Finset.mem_val.mp hτ)
    refine (Polynomial.mem_roots hP).mpr ?_
    rw [Polynomial.IsRoot.def, eval_profilePolynomial]
    exact heatModelFwd_profileRoot hr
  refine (Multiset.eq_of_le_of_card_le hsub ?_).symm
  calc Multiset.card (profilePolynomial m).roots
      ≤ (profilePolynomial m).natDegree := Polynomial.card_roots' _
    _ ≤ m := natDegree_profilePolynomial_le m
    _ = Multiset.card ((profileRoots m).image fun r : ℝ => (r : ℂ)).val := by
        rw [Finset.card_val, Finset.card_image_of_injective _ Complex.ofReal_injective,
          card_profileRoots]

/-- The complex roots of the profile are the real points `profileRoots m`. -/
theorem heatModelFwd_eq_zero_iff {m : ℕ} {ρ : ℂ} :
    heatModelFwd m ρ = 0 ↔ ∃ r ∈ profileRoots m, (r : ℂ) = ρ := by
  classical
  rw [← eval_profilePolynomial, ← Polynomial.IsRoot.def,
    ← Polynomial.mem_roots (profilePolynomial_ne_zero m), roots_profilePolynomial, Finset.mem_val,
    Finset.mem_image]

/-- **The roots of the profile are simple.** -/
theorem deriv_heatModelFwd_ne_zero {m : ℕ} {ρ : ℂ} (h : heatModelFwd m ρ = 0) :
    deriv (heatModelFwd m) ρ ≠ 0 := by
  classical
  have hP := profilePolynomial_ne_zero m
  have hroot : (profilePolynomial m).IsRoot ρ := by
    rw [Polynomial.IsRoot.def, eval_profilePolynomial]
    exact h
  have hnd : (profilePolynomial m).roots.Nodup := by
    rw [roots_profilePolynomial]
    exact Finset.nodup _
  have hmult : (profilePolynomial m).rootMultiplicity ρ = 1 := by
    rw [← Polynomial.count_roots]
    exact Multiset.count_eq_one_of_mem hnd ((Polynomial.mem_roots hP).mpr hroot)
  rw [show heatModelFwd m = fun σ => (profilePolynomial m).eval σ from
    funext fun σ => (eval_profilePolynomial m σ).symm, Polynomial.deriv]
  intro h0
  have hder := Polynomial.derivative_rootMultiplicity_of_root hroot
  rw [hmult] at hder
  by_cases hd0 : Polynomial.derivative (profilePolynomial m) = 0
  · have hC := Polynomial.eq_C_of_derivative_eq_zero hd0
    have h00 : (profilePolynomial m).coeff 0 = 0 := by
      have h1 := hroot
      rw [hC, Polynomial.IsRoot.def, Polynomial.eval_C] at h1
      exact h1
    exact hP (by rw [hC, h00, Polynomial.C_0])
  · have := (Polynomial.rootMultiplicity_pos hd0).mpr h0
    omega

/-- The profile has the parity of its degree. -/
theorem heatModelFwd_neg (m : ℕ) (y : ℂ) : heatModelFwd m (-y) = (-1) ^ m * heatModelFwd m y := by
  rw [heatModelFwd, heatModelFwd, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : 2 * j ≤ m := by
    have := Finset.mem_range.mp hj
    omega
  have h1 : (-1 : ℂ) ^ (m - 2 * j) = (-1) ^ m := by
    have h2 : (-1 : ℂ) ^ m = (-1) ^ (m - 2 * j) * (-1) ^ (2 * j) := by
      rw [← pow_add, Nat.sub_add_cancel hj']
    rw [h2, pow_mul]
    norm_num
  have h3 : (-y) ^ (m - 2 * j) = (-1) ^ m * y ^ (m - 2 * j) := by rw [neg_pow, h1]
  rw [h3]
  ring

/-- The fixed sheet: `0` is a root of the profile exactly when `m` is odd. -/
theorem heatModelFwd_zero_eq_zero_iff (m : ℕ) : heatModelFwd m 0 = 0 ↔ Odd m := by
  constructor
  · intro h
    by_contra hodd
    obtain ⟨k, hk⟩ := Nat.not_odd_iff_even.mp hodd
    have hmk : m / 2 = k := by omega
    rw [heatModelFwd, Finset.sum_eq_single k] at h
    · have h1 : m - 2 * k = 0 := by omega
      rw [h1, pow_zero, mul_one] at h
      have hk0 : (k.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero k
      have hm0 : (m.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero m
      have h10 : ((0 : ℕ).factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero 0
      exact div_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) hm0) (mul_ne_zero hk0 h10) h
    · intro j hj hjk
      have := Finset.mem_range.mp hj
      rw [zero_pow (by omega), mul_zero]
    · intro hk'
      exact absurd (Finset.mem_range.mpr (by omega)) hk'
  · intro hodd
    have h := heatModelFwd_neg m 0
    rw [neg_zero, hodd.neg_one_pow] at h
    linear_combination (1 / 2 : ℂ) * h

/-! ## Collisions -/

/-- A collision of exact order `m` of the heat family: a complex time `τ₀` and a point `z₀` at
which `H_τ₀` vanishes to order exactly `m`. Order one is a simple zero. -/
structure IsCollision (τ₀ z₀ : ℂ) (m : ℕ) : Prop where
  vanish : ∀ i < m, iteratedDeriv i (complexHeat τ₀) z₀ = 0
  top_ne_zero : iteratedDeriv m (complexHeat τ₀) z₀ ≠ 0

variable {τ₀ z₀ : ℂ} {m : ℕ} {ρ : ℂ}

theorem isCollision_iff_analyticOrderAt :
    IsCollision τ₀ z₀ m ↔ analyticOrderAt (complexHeat τ₀) z₀ = (m : ℕ∞) := by
  rw [analyticOrderAt_eq_nat_iff_iteratedDeriv_eq_zero
    ((differentiable_complexHeat τ₀).analyticAt z₀)]
  exact ⟨fun h => ⟨h.vanish, h.top_ne_zero⟩, fun h => ⟨h.1, h.2⟩⟩

/-- **Every zero of the family is a collision of some order `m ≥ 1`.** -/
theorem exists_isCollision (h : complexHeat τ₀ z₀ = 0) : ∃ m, 1 ≤ m ∧ IsCollision τ₀ z₀ m := by
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (analyticOrderAt_complexHeat_ne_top τ₀ z₀)
  have hc : IsCollision τ₀ z₀ n := isCollision_iff_analyticOrderAt.mpr hn.symm
  refine ⟨n, Nat.one_le_iff_ne_zero.mpr fun h0 => ?_, hc⟩
  have h1 := hc.top_ne_zero
  rw [h0, iteratedDeriv_zero] at h1
  exact h1 h

/-- At a real time a collision is a zero of exact order `m` of the de Bruijn–Newman family. -/
theorem isCollision_ofReal_iff {t : ℝ} :
    IsCollision (t : ℂ) z₀ m ↔ (∀ i < m, iteratedDeriv i (riemannHeat t) z₀ = 0) ∧
      iteratedDeriv m (riemannHeat t) z₀ ≠ 0 := by
  have h : complexHeat (t : ℂ) = riemannHeat t := funext (complexHeat_ofReal t)
  constructor
  · rintro ⟨h1, h2⟩
    rw [h] at h1 h2
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    rw [← h] at h1 h2
    exact ⟨h1, h2⟩

/-- The conjugate of a collision is a collision. -/
theorem IsCollision.conj (hc : IsCollision τ₀ z₀ m) :
    IsCollision (starRingEnd ℂ τ₀) (starRingEnd ℂ z₀) m :=
  ⟨fun i hi => by rw [iteratedDeriv_complexHeat_conj, hc.vanish i hi, map_zero], by
    rw [iteratedDeriv_complexHeat_conj]
    exact (map_ne_zero _).mpr hc.top_ne_zero⟩

/-- The reflection of a collision is a collision. -/
theorem IsCollision.neg (hc : IsCollision τ₀ z₀ m) : IsCollision τ₀ (-z₀) m :=
  ⟨fun i hi => by rw [iteratedDeriv_complexHeat_neg, hc.vanish i hi, mul_zero], by
    rw [iteratedDeriv_complexHeat_neg]
    exact mul_ne_zero (pow_ne_zero _ (by norm_num)) hc.top_ne_zero⟩

/-- A collision at the centre has even order. -/
theorem IsCollision.even_of_center (hc : IsCollision τ₀ 0 m) : Even m := by
  by_contra hodd
  have h := iteratedDeriv_complexHeat_neg τ₀ m 0
  rw [neg_zero, (Nat.not_even_iff_odd.mp hodd).neg_one_pow] at h
  exact hc.top_ne_zero (by linear_combination (1 / 2 : ℂ) * h)

/-! ## The sheets of a collision -/

/-- At a root of the profile the `y`-derivative of the blow-up is `(a/m!) Q_m'(ρ) ≠ 0`. -/
private theorem fderiv_collisionBlowup_ne_zero (hc : IsCollision τ₀ z₀ m)
    (hρ : heatModelFwd m ρ = 0) :
    (fderiv ℂ (collisionBlowup τ₀ z₀ m) (0, ρ)) (0, 1) ≠ 0 := by
  have hd := (analyticAt_collisionBlowup τ₀ z₀ m (0, ρ)).differentiableAt.hasFDerivAt
  have hline : HasDerivAt (fun y : ℂ => ((0 : ℂ), y)) ((0 : ℂ), (1 : ℂ)) ρ :=
    (hasDerivAt_const ρ (0 : ℂ)).prodMk (hasDerivAt_id ρ)
  have h1 := hd.comp_hasDerivAt ρ hline
  rw [show (collisionBlowup τ₀ z₀ m ∘ fun y : ℂ => ((0 : ℂ), y)) = fun y =>
      iteratedDeriv m (complexHeat τ₀) z₀ / (m.factorial : ℂ) * heatModelFwd m y from
    funext fun y => collisionBlowup_zero hc.vanish y] at h1
  have h2 := ((differentiable_heatModelFwd m ρ).hasDerivAt.const_mul
    (iteratedDeriv m (complexHeat τ₀) z₀ / (m.factorial : ℂ)))
  rw [h1.unique h2]
  exact mul_ne_zero
    (div_ne_zero hc.top_ne_zero (by exact_mod_cast Nat.factorial_ne_zero m))
    (deriv_heatModelFwd_ne_zero hρ)

/-- **Hermite branches.** Through every root `ρ` of the profile passes an analytic branch `y` of
zeros of the blow-up, and every continuous branch through `ρ` agrees with it near `s = 0`. -/
theorem exists_collisionBranch (hc : IsCollision τ₀ z₀ m) (hρ : heatModelFwd m ρ = 0) :
    ∃ y : ℂ → ℂ, AnalyticAt ℂ y 0 ∧ y 0 = ρ ∧
      (∀ᶠ s in 𝓝 0, collisionBlowup τ₀ z₀ m (s, y s) = 0) ∧
      ∀ y' : ℂ → ℂ, ContinuousAt y' 0 → y' 0 = ρ →
        (∀ᶠ s in 𝓝 0, collisionBlowup τ₀ z₀ m (s, y' s) = 0) → y =ᶠ[𝓝 0] y' :=
  parametric_holo_implicit_unique (analyticAt_collisionBlowup τ₀ z₀ m (0, ρ))
    (by rw [collisionBlowup_zero hc.vanish, hρ, mul_zero])
    (fderiv_collisionBlowup_ne_zero hc hρ)

open Classical in
/-- The Hermite branch `y_ρ` of the collision through the root `ρ` of the profile. -/
def collisionBranch (τ₀ z₀ : ℂ) (m : ℕ) (ρ : ℂ) : ℂ → ℂ :=
  if h : IsCollision τ₀ z₀ m ∧ heatModelFwd m ρ = 0 then (exists_collisionBranch h.1 h.2).choose
  else fun _ => ρ

/-- The branch is analytic, starts at `ρ`, consists of zeros of the blow-up, and is the only
continuous branch through `ρ`. -/
theorem collisionBranch_spec (hc : IsCollision τ₀ z₀ m) (hρ : heatModelFwd m ρ = 0) :
    AnalyticAt ℂ (collisionBranch τ₀ z₀ m ρ) 0 ∧ collisionBranch τ₀ z₀ m ρ 0 = ρ ∧
      (∀ᶠ s in 𝓝 0, collisionBlowup τ₀ z₀ m (s, collisionBranch τ₀ z₀ m ρ s) = 0) ∧
      ∀ y' : ℂ → ℂ, ContinuousAt y' 0 → y' 0 = ρ →
        (∀ᶠ s in 𝓝 0, collisionBlowup τ₀ z₀ m (s, y' s) = 0) →
          collisionBranch τ₀ z₀ m ρ =ᶠ[𝓝 0] y' := by
  have h : IsCollision τ₀ z₀ m ∧ heatModelFwd m ρ = 0 := ⟨hc, hρ⟩
  have hdef : collisionBranch τ₀ z₀ m ρ = (exists_collisionBranch h.1 h.2).choose := by
    rw [collisionBranch, dif_pos h]
  rw [hdef]
  exact (exists_collisionBranch h.1 h.2).choose_spec

/-- The zero of `H_{τ₀+s²}` on the sheet `ρ`: `Z_ρ(s) = z₀ + s y_ρ(s)`. -/
def collisionZero (τ₀ z₀ : ℂ) (m : ℕ) (ρ s : ℂ) : ℂ := z₀ + s * collisionBranch τ₀ z₀ m ρ s

/-- **The sheets consist of zeros.** `H_{τ₀+s²}(Z_ρ(s)) = 0` for small `s`. -/
theorem complexHeat_collisionZero (hc : IsCollision τ₀ z₀ m) (hρ : heatModelFwd m ρ = 0) :
    ∀ᶠ s in 𝓝 0, complexHeat (τ₀ + s ^ 2) (collisionZero τ₀ z₀ m ρ s) = 0 := by
  filter_upwards [(collisionBranch_spec hc hρ).2.2.1] with s hs
  rw [collisionZero, complexHeat_blowup hc.vanish, hs, mul_zero]

/-- **The sheets are distinct.** Two roots carry different zeros for small `s ≠ 0`. -/
theorem collisionZero_ne (hc : IsCollision τ₀ z₀ m) {ρ' : ℂ} (hρ : heatModelFwd m ρ = 0)
    (hρ' : heatModelFwd m ρ' = 0) (hne : ρ ≠ ρ') :
    ∀ᶠ s in 𝓝[≠] 0, collisionZero τ₀ z₀ m ρ s ≠ collisionZero τ₀ z₀ m ρ' s := by
  obtain ⟨han, h0, -, -⟩ := collisionBranch_spec hc hρ
  obtain ⟨han', h0', -, -⟩ := collisionBranch_spec hc hρ'
  have hd : Tendsto (fun s => collisionBranch τ₀ z₀ m ρ s - collisionBranch τ₀ z₀ m ρ' s) (𝓝 0)
      (𝓝 (ρ - ρ')) := by
    have h : ContinuousAt
        (fun s => collisionBranch τ₀ z₀ m ρ s - collisionBranch τ₀ z₀ m ρ' s) 0 :=
      han.continuousAt.sub han'.continuousAt
    have h' := h.tendsto
    simpa only [h0, h0'] using h'
  filter_upwards [(hd.eventually_ne (sub_ne_zero.mpr hne)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s h1 h2 heq
  have h3 : s * (collisionBranch τ₀ z₀ m ρ s - collisionBranch τ₀ z₀ m ρ' s) = 0 := by
    rw [collisionZero, collisionZero] at heq
    linear_combination heq
  exact h1 ((mul_eq_zero.mp h3).resolve_left h2)

/-! ## The monodromy law -/

/-- The branch through `−ρ` is the reflection of the branch through `ρ`. -/
theorem collisionBranch_neg (hc : IsCollision τ₀ z₀ m) (hρ : heatModelFwd m ρ = 0) :
    collisionBranch τ₀ z₀ m (-ρ) =ᶠ[𝓝 0] fun s => -collisionBranch τ₀ z₀ m ρ (-s) := by
  have hρ' : heatModelFwd m (-ρ) = 0 := by rw [heatModelFwd_neg, hρ, mul_zero]
  obtain ⟨han, h0, hz, -⟩ := collisionBranch_spec hc hρ
  have hneg : Tendsto (fun s : ℂ => -s) (𝓝 0) (𝓝 0) := by
    have h := (continuous_neg (G := ℂ)).tendsto 0
    rwa [neg_zero] at h
  refine (collisionBranch_spec hc hρ').2.2.2 _ ?_ ?_ ?_
  · have h2 : ContinuousAt (collisionBranch τ₀ z₀ m ρ) (-(0 : ℂ)) := by
      rw [neg_zero]
      exact han.continuousAt
    exact (h2.comp (continuous_neg (G := ℂ)).continuousAt).neg
  · simp only [neg_zero, h0]
  · filter_upwards [hneg.eventually hz] with s hs
    have h := collisionBlowup_neg hc.vanish (-s) (collisionBranch τ₀ z₀ m ρ (-s))
    rw [neg_neg, hs, mul_zero] at h
    exact h

/-- **The monodromy of a collision.** `Z_ρ(−s) = Z_{−ρ}(s)`: the turn `s ↦ −s` of the time around
the collision carries the sheet `ρ` to the sheet `−ρ`. -/
theorem collisionZero_neg (hc : IsCollision τ₀ z₀ m) (hρ : heatModelFwd m ρ = 0) :
    ∀ᶠ s in 𝓝 0, collisionZero τ₀ z₀ m ρ (-s) = collisionZero τ₀ z₀ m (-ρ) s := by
  filter_upwards [collisionBranch_neg hc hρ] with s hs
  rw [collisionZero, collisionZero, hs]
  ring

/-! ## The conjugation law -/

theorem collisionBranch_conj (hc : IsCollision τ₀ z₀ m) (hρ : heatModelFwd m ρ = 0) :
    ∀ᶠ s in 𝓝 0, starRingEnd ℂ (collisionBranch τ₀ z₀ m ρ s) =
      collisionBranch (starRingEnd ℂ τ₀) (starRingEnd ℂ z₀) m ρ (starRingEnd ℂ s) := by
  obtain ⟨han, h0, hz, -⟩ := collisionBranch_spec hc hρ
  have hreal : starRingEnd ℂ ρ = ρ := by
    obtain ⟨r, -, rfl⟩ := heatModelFwd_eq_zero_iff.mp hρ
    exact Complex.conj_ofReal r
  have hconj : Tendsto (starRingEnd ℂ) (𝓝 (0 : ℂ)) (𝓝 0) := by
    have h := Complex.continuous_conj.tendsto 0
    rwa [map_zero] at h
  have key : collisionBranch (starRingEnd ℂ τ₀) (starRingEnd ℂ z₀) m ρ =ᶠ[𝓝 0]
      fun s => starRingEnd ℂ (collisionBranch τ₀ z₀ m ρ (starRingEnd ℂ s)) := by
    refine (collisionBranch_spec hc.conj hρ).2.2.2 _ ?_ ?_ ?_
    · have h2 : ContinuousAt (collisionBranch τ₀ z₀ m ρ) (starRingEnd ℂ 0) := by
        rw [map_zero]
        exact han.continuousAt
      exact Complex.continuous_conj.continuousAt.comp
        (h2.comp Complex.continuous_conj.continuousAt)
    · simp only [map_zero, h0, hreal]
    · filter_upwards [hconj.eventually hz] with s hs
      have h := collisionBlowup_conj hc.vanish (starRingEnd ℂ s)
        (collisionBranch τ₀ z₀ m ρ (starRingEnd ℂ s))
      rw [hs, map_zero, Complex.conj_conj] at h
      exact h.symm
  filter_upwards [hconj.eventually key] with s hs
  simp only [Complex.conj_conj] at hs
  exact hs.symm

/-- **The conjugation law.** Conjugation carries the sheet `ρ` of a collision to the sheet `ρ` of
the conjugate collision: `conj Z_ρ(s) = Z'_ρ(conj s)`. -/
theorem collisionZero_conj (hc : IsCollision τ₀ z₀ m) (hρ : heatModelFwd m ρ = 0) :
    ∀ᶠ s in 𝓝 0, starRingEnd ℂ (collisionZero τ₀ z₀ m ρ s) =
      collisionZero (starRingEnd ℂ τ₀) (starRingEnd ℂ z₀) m ρ (starRingEnd ℂ s) := by
  filter_upwards [collisionBranch_conj hc hρ] with s hs
  rw [collisionZero, collisionZero, map_add, map_mul, hs]

/-! ## The reflection law -/

theorem collisionBranch_reflect (hc : IsCollision τ₀ z₀ m) (hρ : heatModelFwd m ρ = 0) :
    collisionBranch τ₀ (-z₀) m (-ρ) =ᶠ[𝓝 0] fun s => -collisionBranch τ₀ z₀ m ρ s := by
  have hρ' : heatModelFwd m (-ρ) = 0 := by rw [heatModelFwd_neg, hρ, mul_zero]
  obtain ⟨han, h0, hz, -⟩ := collisionBranch_spec hc hρ
  refine (collisionBranch_spec hc.neg hρ').2.2.2 _ han.continuousAt.neg ?_ ?_
  · simp only [h0]
  · filter_upwards [hz] with s hs
    rw [collisionBlowup_reflect hc.vanish, neg_neg, hs]

/-- **The reflection law.** The functional equation `z ↦ −z` carries the sheet `ρ` of the collision
at `z₀` to the sheet `−ρ` of the collision at `−z₀`. -/
theorem collisionZero_reflect (hc : IsCollision τ₀ z₀ m) (hρ : heatModelFwd m ρ = 0) :
    ∀ᶠ s in 𝓝 0, -collisionZero τ₀ z₀ m ρ s = collisionZero τ₀ (-z₀) m (-ρ) s := by
  filter_upwards [collisionBranch_reflect hc hρ] with s hs
  rw [collisionZero, collisionZero, hs]
  ring

/-- **At a central collision the functional equation is the monodromy.** For a collision at
`z₀ = 0`, `−Z_ρ(s) = Z_ρ(−s)`. -/
theorem neg_collisionZero_center (hc : IsCollision τ₀ 0 m) (hρ : heatModelFwd m ρ = 0) :
    ∀ᶠ s in 𝓝 0, -collisionZero τ₀ 0 m ρ s = collisionZero τ₀ 0 m ρ (-s) := by
  filter_upwards [collisionZero_reflect hc hρ, collisionZero_neg hc hρ] with s h1 h2
  rw [h1, neg_zero, h2]

/-! ## Real collisions -/

variable {t x₀ : ℝ}

/-- At a real collision conjugation preserves each sheet: `conj Z_ρ(s) = Z_ρ(conj s)`. -/
theorem collisionZero_conj_real (hc : IsCollision (t : ℂ) (x₀ : ℂ) m)
    (hρ : heatModelFwd m ρ = 0) :
    ∀ᶠ s in 𝓝 0, starRingEnd ℂ (collisionZero (t : ℂ) (x₀ : ℂ) m ρ s) =
      collisionZero (t : ℂ) (x₀ : ℂ) m ρ (starRingEnd ℂ s) := by
  have h := collisionZero_conj hc hρ
  simpa only [Complex.conj_ofReal] using h

/-- **After a real collision the `m` zeros are real.** -/
theorem collisionZero_ofReal_im (hc : IsCollision (t : ℂ) (x₀ : ℂ) m)
    (hρ : heatModelFwd m ρ = 0) :
    ∀ᶠ q : ℝ in 𝓝 0, (collisionZero (t : ℂ) (x₀ : ℂ) m ρ (q : ℂ)).im = 0 := by
  have hcast : Tendsto (fun q : ℝ => (q : ℂ)) (𝓝 0) (𝓝 0) := by
    have h := Complex.continuous_ofReal.tendsto 0
    rwa [Complex.ofReal_zero] at h
  filter_upwards [hcast.eventually (collisionZero_conj_real hc hρ)] with q hq
  rw [Complex.conj_ofReal] at hq
  exact Complex.conj_eq_iff_im.mp hq

private theorem tendsto_I_mul_ofReal : Tendsto (fun σ : ℝ => I * (σ : ℂ)) (𝓝 0) (𝓝 0) := by
  have hc : Continuous fun σ : ℝ => I * (σ : ℂ) := by fun_prop
  have h := hc.tendsto 0
  simpa only [Complex.ofReal_zero, mul_zero] using h

/-- **Before a real collision, conjugation is the monodromy.** At the time `t − σ²` conjugation
carries the zero on the sheet `ρ` to the zero on the sheet `−ρ`. -/
theorem conj_collisionZero_I_mul (hc : IsCollision (t : ℂ) (x₀ : ℂ) m)
    (hρ : heatModelFwd m ρ = 0) :
    ∀ᶠ σ : ℝ in 𝓝 0, starRingEnd ℂ (collisionZero (t : ℂ) (x₀ : ℂ) m ρ (I * σ)) =
      collisionZero (t : ℂ) (x₀ : ℂ) m (-ρ) (I * σ) := by
  filter_upwards [tendsto_I_mul_ofReal.eventually (collisionZero_conj_real hc hρ),
    tendsto_I_mul_ofReal.eventually (collisionZero_neg hc hρ)] with σ h1 h2
  rw [h1, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul, h2]

/-- **Before a real collision the zeros on the sheets `ρ ≠ 0` are not real.** -/
theorem collisionZero_I_mul_im_ne_zero (hc : IsCollision (t : ℂ) (x₀ : ℂ) m)
    (hρ : heatModelFwd m ρ = 0) (hρ0 : ρ ≠ 0) :
    ∀ᶠ σ : ℝ in 𝓝[≠] 0, (collisionZero (t : ℂ) (x₀ : ℂ) m ρ (I * σ)).im ≠ 0 := by
  obtain ⟨han, h0, -, -⟩ := collisionBranch_spec hc hρ
  obtain ⟨r, -, rfl⟩ := heatModelFwd_eq_zero_iff.mp hρ
  have hr : r ≠ 0 := fun h => hρ0 (by rw [h, Complex.ofReal_zero])
  have hre : Tendsto (fun σ : ℝ => (collisionBranch (t : ℂ) (x₀ : ℂ) m r (I * σ)).re) (𝓝 0)
      (𝓝 r) := by
    have h1 := han.continuousAt.tendsto.comp tendsto_I_mul_ofReal
    rw [h0] at h1
    have h2 : Tendsto (fun σ : ℝ => (collisionBranch (t : ℂ) (x₀ : ℂ) m r (I * σ)).re) (𝓝 0)
        (𝓝 (r : ℂ).re) := (Complex.continuous_re.tendsto (r : ℂ)).comp h1
    simpa only [Complex.ofReal_re] using h2
  filter_upwards [(hre.eventually_ne hr).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with σ h1 h2
  have him : (collisionZero (t : ℂ) (x₀ : ℂ) m r (I * σ)).im =
      σ * (collisionBranch (t : ℂ) (x₀ : ℂ) m r (I * σ)).re := by
    simp [collisionZero]
  rw [him]
  exact mul_ne_zero h2 h1

/-- **Before a real central collision the colliding zeros lie on the imaginary axis**: there
conjugation, the functional equation and the monodromy agree. -/
theorem collisionZero_center_I_mul_re (hc : IsCollision (t : ℂ) 0 m)
    (hρ : heatModelFwd m ρ = 0) :
    ∀ᶠ σ : ℝ in 𝓝 0, (collisionZero (t : ℂ) 0 m ρ (I * σ)).re = 0 := by
  have hc' : IsCollision (t : ℂ) ((0 : ℝ) : ℂ) m := by rwa [Complex.ofReal_zero]
  have hconj := conj_collisionZero_I_mul hc' hρ
  rw [Complex.ofReal_zero] at hconj
  filter_upwards [hconj, tendsto_I_mul_ofReal.eventually (neg_collisionZero_center hc hρ),
    tendsto_I_mul_ofReal.eventually (collisionZero_neg hc hρ)] with σ h1 h2 h3
  have h4 : starRingEnd ℂ (collisionZero (t : ℂ) 0 m ρ (I * σ)) =
      -collisionZero (t : ℂ) 0 m ρ (I * σ) := by rw [h1, h2, h3]
  have h5 := congrArg Complex.re h4
  rw [Complex.conj_re, Complex.neg_re] at h5
  linarith

end

end GaloisForLFunctions.GaloisTheoryOfZeros
