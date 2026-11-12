import GaloisForLFunctions.GaloisTheoryOfZeros.TheHeatCoverOfTheZeros
import GaloisForLFunctions.HTGeometry.ParametricSpectralBranch

/-!
# The Hermite monodromy of a collision

Let `(t, z₀)` be a collision of exact order `m` of the heat family: `H_t` vanishes at `z₀` to order
exactly `m`. The Hermite profile `Q_m` has `m` simple real roots, symmetric under `ρ ↦ −ρ`. On the
double cover `τ = t + s²` the cover of zeros is unramified:

* **Sheets** (`collisionBranch_spec`, `complexHeat_collisionZero`). Through every root `ρ` passes
  one analytic branch `y_ρ` of zeros of the blow-up, `y_ρ(0) = ρ`. The point
  `Z_ρ(s) = z₀ + s y_ρ(s)` is a zero of `H_{t+s²}`, and the `m` points are distinct for small
  `s ≠ 0` (`collisionZero_ne`).
* **Monodromy** (`collisionZero_neg`). `Z_ρ(−s) = Z_{−ρ}(s)`. One turn of `τ` around `t` is
  `s ↦ −s`, so the local monodromy is the reflection `ρ ↦ −ρ` of the Hermite roots: `⌊m/2⌋`
  disjoint transpositions, with the fixed sheet `ρ = 0` exactly when `m` is odd
  (`heatModelFwd_zero_eq_zero_iff`).
* **Conjugation** (`collisionZero_conj`). At a real centre, `conj Z_ρ(s) = Z_ρ(conj s)`. After the
  collision (`s` real) all `m` zeros are real (`collisionZero_ofReal_im`). Before it (`s = iσ`)
  conjugation carries the sheet `ρ` to the sheet `−ρ` (`conj_collisionZero_I_mul`), and the zeros on
  the sheets `ρ ≠ 0` are not real (`collisionZero_I_mul_im_ne_zero`).

So before a real collision complex conjugation acts on the colliding zeros as the local monodromy
of the heat cover.

The branches come from the analytic implicit function theorem applied to the blow-up `G` at
`(0, ρ)`, where `∂_y G = (a/m!) Q_m'(ρ) ≠ 0`. The two laws follow from the symmetries of `G` and the
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

/-! ## Collisions and their sheets -/

/-- A collision of exact order `m` of the heat family: a real time `t ≥ 0` and a point `z₀` at which
`H_t` vanishes to order exactly `m`. -/
structure IsCollision (t : ℝ) (z₀ : ℂ) (m : ℕ) : Prop where
  time_nonneg : 0 ≤ t
  vanish : ∀ i < m, iteratedDeriv i (riemannHeat t) z₀ = 0
  top_ne_zero : iteratedDeriv m (riemannHeat t) z₀ ≠ 0

variable {t : ℝ} {z₀ : ℂ} {m : ℕ} {ρ : ℂ}

/-- At a root of the profile the `y`-derivative of the blow-up is `(a/m!) Q_m'(ρ) ≠ 0`. -/
private theorem fderiv_collisionBlowup_ne_zero (hc : IsCollision t z₀ m)
    (hρ : heatModelFwd m ρ = 0) :
    (fderiv ℂ (collisionBlowup t z₀ m) (0, ρ)) (0, 1) ≠ 0 := by
  have hd := (analyticAt_collisionBlowup hc.time_nonneg z₀ m (0, ρ)).differentiableAt.hasFDerivAt
  have hline : HasDerivAt (fun y : ℂ => ((0 : ℂ), y)) ((0 : ℂ), (1 : ℂ)) ρ :=
    (hasDerivAt_const ρ (0 : ℂ)).prodMk (hasDerivAt_id ρ)
  have h1 := hd.comp_hasDerivAt ρ hline
  rw [show (collisionBlowup t z₀ m ∘ fun y : ℂ => ((0 : ℂ), y)) = fun y =>
      iteratedDeriv m (riemannHeat t) z₀ / (m.factorial : ℂ) * heatModelFwd m y from
    funext fun y => collisionBlowup_zero hc.time_nonneg hc.vanish y] at h1
  have h2 := ((differentiable_heatModelFwd m ρ).hasDerivAt.const_mul
    (iteratedDeriv m (riemannHeat t) z₀ / (m.factorial : ℂ)))
  rw [h1.unique h2]
  exact mul_ne_zero
    (div_ne_zero hc.top_ne_zero (by exact_mod_cast Nat.factorial_ne_zero m))
    (deriv_heatModelFwd_ne_zero hρ)

/-- **Hermite branches.** Through every root `ρ` of the profile passes an analytic branch `y` of
zeros of the blow-up, and every continuous branch through `ρ` agrees with it near `s = 0`. -/
theorem exists_collisionBranch (hc : IsCollision t z₀ m) (hρ : heatModelFwd m ρ = 0) :
    ∃ y : ℂ → ℂ, AnalyticAt ℂ y 0 ∧ y 0 = ρ ∧
      (∀ᶠ s in 𝓝 0, collisionBlowup t z₀ m (s, y s) = 0) ∧
      ∀ y' : ℂ → ℂ, ContinuousAt y' 0 → y' 0 = ρ →
        (∀ᶠ s in 𝓝 0, collisionBlowup t z₀ m (s, y' s) = 0) → y =ᶠ[𝓝 0] y' :=
  parametric_holo_implicit_unique (analyticAt_collisionBlowup hc.time_nonneg z₀ m (0, ρ))
    (by rw [collisionBlowup_zero hc.time_nonneg hc.vanish, hρ, mul_zero])
    (fderiv_collisionBlowup_ne_zero hc hρ)

open Classical in
/-- The Hermite branch `y_ρ` of the collision through the root `ρ` of the profile. -/
def collisionBranch (t : ℝ) (z₀ : ℂ) (m : ℕ) (ρ : ℂ) : ℂ → ℂ :=
  if h : IsCollision t z₀ m ∧ heatModelFwd m ρ = 0 then (exists_collisionBranch h.1 h.2).choose
  else fun _ => ρ

/-- The branch is analytic, starts at `ρ`, consists of zeros of the blow-up, and is the only
continuous branch through `ρ`. -/
theorem collisionBranch_spec (hc : IsCollision t z₀ m) (hρ : heatModelFwd m ρ = 0) :
    AnalyticAt ℂ (collisionBranch t z₀ m ρ) 0 ∧ collisionBranch t z₀ m ρ 0 = ρ ∧
      (∀ᶠ s in 𝓝 0, collisionBlowup t z₀ m (s, collisionBranch t z₀ m ρ s) = 0) ∧
      ∀ y' : ℂ → ℂ, ContinuousAt y' 0 → y' 0 = ρ →
        (∀ᶠ s in 𝓝 0, collisionBlowup t z₀ m (s, y' s) = 0) →
          collisionBranch t z₀ m ρ =ᶠ[𝓝 0] y' := by
  have h : IsCollision t z₀ m ∧ heatModelFwd m ρ = 0 := ⟨hc, hρ⟩
  have hdef : collisionBranch t z₀ m ρ = (exists_collisionBranch h.1 h.2).choose := by
    rw [collisionBranch, dif_pos h]
  rw [hdef]
  exact (exists_collisionBranch h.1 h.2).choose_spec

/-- The zero of `H_{t+s²}` on the sheet `ρ`: `Z_ρ(s) = z₀ + s y_ρ(s)`. -/
def collisionZero (t : ℝ) (z₀ : ℂ) (m : ℕ) (ρ s : ℂ) : ℂ := z₀ + s * collisionBranch t z₀ m ρ s

/-- **The sheets consist of zeros.** `H_{t+s²}(Z_ρ(s)) = 0` for small `s`. -/
theorem complexHeat_collisionZero (hc : IsCollision t z₀ m) (hρ : heatModelFwd m ρ = 0) :
    ∀ᶠ s in 𝓝 0, complexHeat (t + s ^ 2) (collisionZero t z₀ m ρ s) = 0 := by
  filter_upwards [(collisionBranch_spec hc hρ).2.2.1] with s hs
  rw [collisionZero, complexHeat_blowup hc.time_nonneg hc.vanish, hs, mul_zero]

/-- **The sheets are distinct.** Two roots carry different zeros for small `s ≠ 0`. -/
theorem collisionZero_ne (hc : IsCollision t z₀ m) {ρ' : ℂ} (hρ : heatModelFwd m ρ = 0)
    (hρ' : heatModelFwd m ρ' = 0) (hne : ρ ≠ ρ') :
    ∀ᶠ s in 𝓝[≠] 0, collisionZero t z₀ m ρ s ≠ collisionZero t z₀ m ρ' s := by
  obtain ⟨han, h0, -, -⟩ := collisionBranch_spec hc hρ
  obtain ⟨han', h0', -, -⟩ := collisionBranch_spec hc hρ'
  have hd : Tendsto (fun s => collisionBranch t z₀ m ρ s - collisionBranch t z₀ m ρ' s) (𝓝 0)
      (𝓝 (ρ - ρ')) := by
    have h : ContinuousAt
        (fun s => collisionBranch t z₀ m ρ s - collisionBranch t z₀ m ρ' s) 0 :=
      han.continuousAt.sub han'.continuousAt
    have h' := h.tendsto
    simpa only [h0, h0'] using h'
  filter_upwards [(hd.eventually_ne (sub_ne_zero.mpr hne)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with s h1 h2 heq
  have h3 : s * (collisionBranch t z₀ m ρ s - collisionBranch t z₀ m ρ' s) = 0 := by
    rw [collisionZero, collisionZero] at heq
    linear_combination heq
  exact h1 ((mul_eq_zero.mp h3).resolve_left h2)

/-! ## The monodromy law -/

/-- The branch through `−ρ` is the reflection of the branch through `ρ`. -/
theorem collisionBranch_neg (hc : IsCollision t z₀ m) (hρ : heatModelFwd m ρ = 0) :
    collisionBranch t z₀ m (-ρ) =ᶠ[𝓝 0] fun s => -collisionBranch t z₀ m ρ (-s) := by
  have hρ' : heatModelFwd m (-ρ) = 0 := by rw [heatModelFwd_neg, hρ, mul_zero]
  obtain ⟨han, h0, hz, -⟩ := collisionBranch_spec hc hρ
  have hneg : Tendsto (fun s : ℂ => -s) (𝓝 0) (𝓝 0) := by
    have h := (continuous_neg (G := ℂ)).tendsto 0
    rwa [neg_zero] at h
  refine (collisionBranch_spec hc hρ').2.2.2 _ ?_ ?_ ?_
  · have h2 : ContinuousAt (collisionBranch t z₀ m ρ) (-(0 : ℂ)) := by
      rw [neg_zero]
      exact han.continuousAt
    exact (h2.comp (continuous_neg (G := ℂ)).continuousAt).neg
  · simp only [neg_zero, h0]
  · filter_upwards [hneg.eventually hz] with s hs
    have h := collisionBlowup_neg hc.time_nonneg hc.vanish (-s) (collisionBranch t z₀ m ρ (-s))
    rw [neg_neg, hs, mul_zero] at h
    exact h

/-- **The monodromy of a collision.** `Z_ρ(−s) = Z_{−ρ}(s)`: the turn `s ↦ −s` of the time around
the collision carries the sheet `ρ` to the sheet `−ρ`. -/
theorem collisionZero_neg (hc : IsCollision t z₀ m) (hρ : heatModelFwd m ρ = 0) :
    ∀ᶠ s in 𝓝 0, collisionZero t z₀ m ρ (-s) = collisionZero t z₀ m (-ρ) s := by
  filter_upwards [collisionBranch_neg hc hρ] with s hs
  rw [collisionZero, collisionZero, hs]
  ring

/-! ## The conjugation law at a real centre -/

variable {x₀ : ℝ}

theorem collisionBranch_conj (hc : IsCollision t x₀ m) (hρ : heatModelFwd m ρ = 0) :
    ∀ᶠ s in 𝓝 0, starRingEnd ℂ (collisionBranch t x₀ m ρ s) =
      collisionBranch t x₀ m ρ (starRingEnd ℂ s) := by
  obtain ⟨han, h0, hz, huniq⟩ := collisionBranch_spec hc hρ
  have hreal : starRingEnd ℂ ρ = ρ := by
    obtain ⟨r, -, rfl⟩ := heatModelFwd_eq_zero_iff.mp hρ
    exact Complex.conj_ofReal r
  have hconj : Tendsto (starRingEnd ℂ) (𝓝 (0 : ℂ)) (𝓝 0) := by
    have h := Complex.continuous_conj.tendsto 0
    rwa [map_zero] at h
  have key : collisionBranch t x₀ m ρ =ᶠ[𝓝 0]
      fun s => starRingEnd ℂ (collisionBranch t x₀ m ρ (starRingEnd ℂ s)) := by
    refine huniq _ ?_ ?_ ?_
    · have h2 : ContinuousAt (collisionBranch t x₀ m ρ) (starRingEnd ℂ 0) := by
        rw [map_zero]
        exact han.continuousAt
      exact Complex.continuous_conj.continuousAt.comp
        (h2.comp Complex.continuous_conj.continuousAt)
    · simp only [map_zero, h0, hreal]
    · filter_upwards [hconj.eventually hz] with s hs
      have h := collisionBlowup_conj hc.time_nonneg hc.vanish (starRingEnd ℂ s)
        (collisionBranch t x₀ m ρ (starRingEnd ℂ s))
      rw [hs, map_zero, Complex.conj_conj] at h
      exact h.symm
  filter_upwards [hconj.eventually key] with s hs
  simp only [Complex.conj_conj] at hs
  exact hs.symm

/-- **The conjugation law.** At a real centre, `conj Z_ρ(s) = Z_ρ(conj s)`. -/
theorem collisionZero_conj (hc : IsCollision t x₀ m) (hρ : heatModelFwd m ρ = 0) :
    ∀ᶠ s in 𝓝 0, starRingEnd ℂ (collisionZero t x₀ m ρ s) =
      collisionZero t x₀ m ρ (starRingEnd ℂ s) := by
  filter_upwards [collisionBranch_conj hc hρ] with s hs
  rw [collisionZero, collisionZero, map_add, map_mul, hs, Complex.conj_ofReal]

/-- **After a real collision the `m` zeros are real.** -/
theorem collisionZero_ofReal_im (hc : IsCollision t x₀ m) (hρ : heatModelFwd m ρ = 0) :
    ∀ᶠ q : ℝ in 𝓝 0, (collisionZero t x₀ m ρ (q : ℂ)).im = 0 := by
  have hcast : Tendsto (fun q : ℝ => (q : ℂ)) (𝓝 0) (𝓝 0) := by
    have h := Complex.continuous_ofReal.tendsto 0
    rwa [Complex.ofReal_zero] at h
  filter_upwards [hcast.eventually (collisionZero_conj hc hρ)] with q hq
  rw [Complex.conj_ofReal] at hq
  exact Complex.conj_eq_iff_im.mp hq

private theorem tendsto_I_mul_ofReal : Tendsto (fun σ : ℝ => I * (σ : ℂ)) (𝓝 0) (𝓝 0) := by
  have hc : Continuous fun σ : ℝ => I * (σ : ℂ) := by fun_prop
  have h := hc.tendsto 0
  simpa only [Complex.ofReal_zero, mul_zero] using h

/-- **Before a real collision, conjugation is the monodromy.** At the time `t − σ²` conjugation
carries the zero on the sheet `ρ` to the zero on the sheet `−ρ`. -/
theorem conj_collisionZero_I_mul (hc : IsCollision t x₀ m) (hρ : heatModelFwd m ρ = 0) :
    ∀ᶠ σ : ℝ in 𝓝 0, starRingEnd ℂ (collisionZero t x₀ m ρ (I * σ)) =
      collisionZero t x₀ m (-ρ) (I * σ) := by
  filter_upwards [tendsto_I_mul_ofReal.eventually (collisionZero_conj hc hρ),
    tendsto_I_mul_ofReal.eventually (collisionZero_neg hc hρ)] with σ h1 h2
  rw [h1, map_mul, Complex.conj_I, Complex.conj_ofReal, neg_mul, h2]

/-- **Before a real collision the zeros on the sheets `ρ ≠ 0` are not real.** -/
theorem collisionZero_I_mul_im_ne_zero (hc : IsCollision t x₀ m) (hρ : heatModelFwd m ρ = 0)
    (hρ0 : ρ ≠ 0) :
    ∀ᶠ σ : ℝ in 𝓝[≠] 0, (collisionZero t x₀ m ρ (I * σ)).im ≠ 0 := by
  obtain ⟨han, h0, -, -⟩ := collisionBranch_spec hc hρ
  obtain ⟨r, -, rfl⟩ := heatModelFwd_eq_zero_iff.mp hρ
  have hr : r ≠ 0 := fun h => hρ0 (by rw [h, Complex.ofReal_zero])
  have hre : Tendsto (fun σ : ℝ => (collisionBranch t x₀ m r (I * σ)).re) (𝓝 0) (𝓝 r) := by
    have h1 := han.continuousAt.tendsto.comp tendsto_I_mul_ofReal
    rw [h0] at h1
    have h2 : Tendsto (fun σ : ℝ => (collisionBranch t x₀ m r (I * σ)).re) (𝓝 0)
        (𝓝 (r : ℂ).re) := (Complex.continuous_re.tendsto (r : ℂ)).comp h1
    simpa only [Complex.ofReal_re] using h2
  filter_upwards [(hre.eventually_ne hr).filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin]
    with σ h1 h2
  have him : (collisionZero t x₀ m r (I * σ)).im = σ * (collisionBranch t x₀ m r (I * σ)).re := by
    simp [collisionZero]
  rw [him]
  exact mul_ne_zero h2 h1

end

end GaloisForLFunctions.GaloisTheoryOfZeros
