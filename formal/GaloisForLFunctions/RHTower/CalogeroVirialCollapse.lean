import Mathlib

/-!
# The virial law of the attractive pair flow, and finite-time collapse

The backward de Bruijn--Newman dynamics of the real zeros is the attractive rational
Calogero flow

```text
  dx_j/dτ = -2 ∑_{k ≠ j} (x_j - x_k)⁻¹ .
```

Every criterion built for this flow so far has been *local*: it isolates one gap, freezes the
field of the remaining zeros, and then needs an upper bound on that field.  The field bound is
the obstruction.

This file records a *global* law that needs no field bound at all.  Two exact algebraic
identities hold for any finite set of distinct reals:

```text
  ∑_j ∑_{k ≠ j} (x_j - x_k)⁻¹ = 0 ,          ∑_j x_j ∑_{k ≠ j} (x_j - x_k)⁻¹ = N(N-1)/2 .
```

The first is antisymmetry.  The second says that the *virial* of the pair force is a pure
count: it does not see the configuration at all.  Consequently the second moment of the
configuration about any centre obeys

```text
  d/dτ ∑_j (x_j - c)² = -2N(N-1)
```

exactly — a configuration-independent, height-uniform rate.  Since the second moment is
nonnegative, the flow cannot exist past time `∑_j (x_j(0) - c)² / (2N(N-1))`: some pair must
collide.

The same symmetrisation identifies the full class of observables with a sign:
for any weight `g`, `2 ∑_j g(x_j) F_j` is the off-diagonal sum of the divided differences of
`g`, so `∑_j g(x_j) ẋ_j ≤ 0` exactly when `g` is monotone — i.e. exactly when the observable
`∫ g` is convex.  This pins the localisation obstruction precisely: a localised virial weight
would be a nonconstant convex function bounded above on `ℝ`, and none exists.

The external-field lemmas at the end give the sign of the correction when the finite set is a
window inside a larger configuration: the outside zeros always *oppose* collapse, and their
total effect is controlled by the second moment itself.
-/

namespace RHTower

open Finset

variable {ι : Type*}

/-- The pair force at `j`: `∑_{k ≠ j} (x_j - x_k)⁻¹`.  The diagonal term is `0⁻¹ = 0`, so the
unrestricted sum already omits it. -/
noncomputable def calogeroField (S : Finset ι) (x : ι → ℝ) (j : ι) : ℝ := ∑ k ∈ S, (x j - x k)⁻¹

theorem calogeroField_eq_sum_erase [DecidableEq ι] (S : Finset ι) (x : ι → ℝ) {j : ι}
    (hj : j ∈ S) :
    calogeroField S x j = ∑ k ∈ S.erase j, (x j - x k)⁻¹ := by
  rw [Finset.sum_erase_eq_sub hj]
  simp [calogeroField]

/-- Symmetrisation of an off-diagonal double sum. -/
private theorem two_mul_double (S : Finset ι) (F : ι → ι → ℝ) :
    2 * (∑ j ∈ S, ∑ k ∈ S, F j k) = ∑ j ∈ S, ∑ k ∈ S, (F j k + F k j) := by
  have h : (∑ j ∈ S, ∑ k ∈ S, F k j) = ∑ j ∈ S, ∑ k ∈ S, F j k := Finset.sum_comm
  simp only [Finset.sum_add_distrib]
  rw [h]; ring

/-- **Balance.**  The pair forces sum to zero: the centre of mass is conserved. -/
theorem sum_calogeroField (S : Finset ι) (x : ι → ℝ) :
    ∑ j ∈ S, calogeroField S x j = 0 := by
  have h2 := two_mul_double S (fun j k => (x j - x k)⁻¹)
  have hz : ∀ j k : ι, (x j - x k)⁻¹ + (x k - x j)⁻¹ = 0 := by
    intro j k
    have hrw : x k - x j = -(x j - x k) := by ring
    rw [hrw, inv_neg]; ring
  simp only [hz, Finset.sum_const_zero] at h2
  simp only [calogeroField]
  linarith

private theorem sum_off_one [DecidableEq ι] {S : Finset ι} {j : ι} (hj : j ∈ S) :
    (∑ k ∈ S, (if j = k then (0 : ℝ) else 1)) = (S.card : ℝ) - 1 := by
  have hrw : ∀ k : ι, (if j = k then (0 : ℝ) else 1) = 1 - (if j = k then (1 : ℝ) else 0) := by
    intro k; by_cases h : j = k <;> simp [h]
  simp only [hrw, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [Finset.sum_ite_eq S j (fun _ => (1 : ℝ)), if_pos hj]

/-- **Divided-difference law.**  For any weight `g`, twice the `g`-weighted virial is the
off-diagonal sum of the divided differences of `g`. -/
theorem two_mul_sum_weighted_calogeroField [DecidableEq ι] (S : Finset ι) (x : ι → ℝ)
    (g : ℝ → ℝ)
    (hinj : Set.InjOn x S) :
    2 * ∑ j ∈ S, g (x j) * calogeroField S x j
      = ∑ j ∈ S, ∑ k ∈ S, (if j = k then 0 else (g (x j) - g (x k)) / (x j - x k)) := by
  have h2 := two_mul_double S (fun j k => g (x j) * (x j - x k)⁻¹)
  have hval : ∀ j ∈ S, ∀ k ∈ S,
      g (x j) * (x j - x k)⁻¹ + g (x k) * (x k - x j)⁻¹
        = (if j = k then 0 else (g (x j) - g (x k)) / (x j - x k)) := by
    intro j hj k hk
    by_cases h : j = k
    · subst h; simp
    · have hne : x j - x k ≠ 0 := sub_ne_zero.mpr fun hh => h (hinj hj hk hh)
      have hrw : x k - x j = -(x j - x k) := by ring
      rw [hrw, inv_neg, if_neg h]
      field_simp
      ring
  have hright : (∑ j ∈ S, ∑ k ∈ S,
        (g (x j) * (x j - x k)⁻¹ + g (x k) * (x k - x j)⁻¹))
      = ∑ j ∈ S, ∑ k ∈ S, (if j = k then 0 else (g (x j) - g (x k)) / (x j - x k)) :=
    Finset.sum_congr rfl fun j hj => Finset.sum_congr rfl fun k hk => hval j hj k hk
  calc 2 * ∑ j ∈ S, g (x j) * calogeroField S x j
      = 2 * (∑ j ∈ S, ∑ k ∈ S, g (x j) * (x j - x k)⁻¹) := by
        simp only [calogeroField, Finset.mul_sum]
    _ = ∑ j ∈ S, ∑ k ∈ S, (g (x j) * (x j - x k)⁻¹ + g (x k) * (x k - x j)⁻¹) := h2
    _ = _ := hright

/-- **Virial identity.**  The virial of the pair force is a pure pair count: it is completely
blind to the configuration. -/
theorem sum_mul_calogeroField [DecidableEq ι] (S : Finset ι) (x : ι → ℝ)
    (hinj : Set.InjOn x S) :
    ∑ j ∈ S, x j * calogeroField S x j = (S.card : ℝ) * ((S.card : ℝ) - 1) / 2 := by
  have h := two_mul_sum_weighted_calogeroField S x id hinj
  have hdd : ∀ j ∈ S, ∀ k ∈ S,
      (if j = k then 0 else (id (x j) - id (x k)) / (x j - x k))
        = (if j = k then (0 : ℝ) else 1) := by
    intro j hj k hk
    by_cases hjk : j = k
    · simp [hjk]
    · have hne : x j - x k ≠ 0 := sub_ne_zero.mpr fun hh => hjk (hinj hj hk hh)
      simp [hjk, id, div_self hne]
  have hrewrite : (∑ j ∈ S, ∑ k ∈ S,
        (if j = k then 0 else (id (x j) - id (x k)) / (x j - x k)))
      = ∑ j ∈ S, ((S.card : ℝ) - 1) :=
    Finset.sum_congr rfl fun j hj => by
      rw [Finset.sum_congr rfl fun k hk => hdd j hj k hk, sum_off_one hj]
  rw [hrewrite, Finset.sum_const, nsmul_eq_mul] at h
  simp only [id] at h
  linarith

/-- The virial identity about an arbitrary centre: translation does not change the rate. -/
theorem sum_sub_mul_calogeroField [DecidableEq ι] (S : Finset ι) (x : ι → ℝ)
    (hinj : Set.InjOn x S) (c : ℝ) :
    ∑ j ∈ S, (x j - c) * calogeroField S x j = (S.card : ℝ) * ((S.card : ℝ) - 1) / 2 := by
  have hsplit : ∀ j : ι, (x j - c) * calogeroField S x j
      = x j * calogeroField S x j - c * calogeroField S x j := by
    intro j; ring
  simp only [hsplit, Finset.sum_sub_distrib, ← Finset.mul_sum, sum_calogeroField,
    mul_zero, sub_zero]
  exact sum_mul_calogeroField S x hinj

/-- **Monotone observables decrease.**  If `g` is monotone then the `g`-weighted virial is
nonnegative, so the observable `∑_j G(x_j)` with `G' = g` is nonincreasing along the flow. -/
theorem sum_weighted_calogeroField_nonneg [DecidableEq ι] (S : Finset ι) (x : ι → ℝ)
    {g : ℝ → ℝ}
    (hg : Monotone g) (hinj : Set.InjOn x S) :
    0 ≤ ∑ j ∈ S, g (x j) * calogeroField S x j := by
  have h := two_mul_sum_weighted_calogeroField S x g hinj
  have hnn : (0 : ℝ) ≤ ∑ j ∈ S, ∑ k ∈ S,
      (if j = k then 0 else (g (x j) - g (x k)) / (x j - x k)) := by
    refine Finset.sum_nonneg fun j _ => Finset.sum_nonneg fun k _ => ?_
    by_cases hjk : j = k
    · simp [hjk]
    · rw [if_neg hjk]
      rcases lt_trichotomy (x j) (x k) with hlt | heq | hgt
      · have h1 : g (x j) - g (x k) ≤ 0 := sub_nonpos.mpr (hg hlt.le)
        have h2 : x j - x k < 0 := sub_neg.mpr hlt
        exact div_nonneg_iff.mpr (Or.inr ⟨h1, h2.le⟩)
      · simp [heq]
      · have h1 : 0 ≤ g (x j) - g (x k) := sub_nonneg.mpr (hg hgt.le)
        have h2 : 0 < x j - x k := sub_pos.mpr hgt
        exact div_nonneg h1 h2.le
  linarith


/-- Along the flow, every monotone observable weight has nonpositive rate. -/
theorem sum_weighted_velocity_nonpos [DecidableEq ι] (S : Finset ι) (x : ι → ℝ) {g : ℝ → ℝ}
    (hg : Monotone g) (hinj : Set.InjOn x S) :
    ∑ j ∈ S, g (x j) * (-2 * calogeroField S x j) ≤ 0 := by
  have h := sum_weighted_calogeroField_nonneg S x hg hinj
  have hrw : ∑ j ∈ S, g (x j) * (-2 * calogeroField S x j)
      = -2 * ∑ j ∈ S, g (x j) * calogeroField S x j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hrw]; linarith

/-- The second moment of the configuration about `c`. -/
def calogeroSecondMoment (S : Finset ι) (x : ι → ℝ) (c : ℝ) : ℝ :=
  ∑ j ∈ S, (x j - c) ^ (2 : ℕ)

theorem calogeroSecondMoment_nonneg (S : Finset ι) (x : ι → ℝ) (c : ℝ) :
    0 ≤ calogeroSecondMoment S x c :=
  Finset.sum_nonneg fun j _ => by positivity

/-- **Exact collapse rate.**  Along the attractive pair flow the second moment about any centre
decreases at the configuration-independent rate `2N(N-1)`. -/
theorem hasDerivAt_calogeroSecondMoment [DecidableEq ι] {S : Finset ι} {x : ℝ → ι → ℝ} {c t : ℝ}
    (hd : ∀ j ∈ S, HasDerivAt (fun s => x s j) (-2 * calogeroField S (x t) j) t)
    (hinj : Set.InjOn (x t) S) :
    HasDerivAt (fun s => calogeroSecondMoment S (x s) c)
      (-2 * (S.card : ℝ) * ((S.card : ℝ) - 1)) t := by
  have key : ∀ j ∈ S, HasDerivAt (fun s => (x s j - c) ^ (2 : ℕ))
      (2 * (x t j - c) * (-2 * calogeroField S (x t) j)) t := by
    intro j hj
    have h1 := (hd j hj).sub_const c
    have h2 := h1.mul h1
    have hfun : ((fun s : ℝ => x s j - c) * fun s : ℝ => x s j - c)
        = fun s : ℝ => (x s j - c) ^ (2 : ℕ) := by
      funext s
      show (x s j - c) * (x s j - c) = (x s j - c) ^ (2 : ℕ)
      ring
    rw [hfun] at h2
    have hval : -2 * calogeroField S (x t) j * (x t j - c)
          + (x t j - c) * (-2 * calogeroField S (x t) j)
        = 2 * (x t j - c) * (-2 * calogeroField S (x t) j) := by ring
    rw [hval] at h2
    exact h2
  have hsum := HasDerivAt.sum key
  have hfun : (∑ j ∈ S, fun s : ℝ => (x s j - c) ^ (2 : ℕ))
      = fun s : ℝ => calogeroSecondMoment S (x s) c := by
    funext s
    simp [calogeroSecondMoment, Finset.sum_apply]
  rw [hfun] at hsum
  have hval : (∑ j ∈ S, 2 * (x t j - c) * (-2 * calogeroField S (x t) j))
      = -2 * (S.card : ℝ) * ((S.card : ℝ) - 1) := by
    have hterm : ∀ j : ι, 2 * (x t j - c) * (-2 * calogeroField S (x t) j)
        = -4 * ((x t j - c) * calogeroField S (x t) j) := by intro j; ring
    simp only [hterm, ← Finset.mul_sum, sum_sub_mul_calogeroField S (x t) hinj c]
    ring
  rwa [hval] at hsum

/-- The second moment is exactly linear in time while the flow exists. -/
theorem calogeroSecondMoment_eq_of_flow [DecidableEq ι] {S : Finset ι} {x : ℝ → ι → ℝ} {c T : ℝ}
    (hT : 0 < T)
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ j ∈ S,
      HasDerivAt (fun s => x s j) (-2 * calogeroField S (x t) j) t)
    (hinj : ∀ t ∈ Set.Icc (0 : ℝ) T, Set.InjOn (x t) S) :
    calogeroSecondMoment S (x T) c
      = calogeroSecondMoment S (x 0) c - 2 * (S.card : ℝ) * ((S.card : ℝ) - 1) * T := by
  have hderiv : ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasDerivAt (fun s => calogeroSecondMoment S (x s) c
        + 2 * (S.card : ℝ) * ((S.card : ℝ) - 1) * s) 0 t := by
    intro t ht
    have h1 := hasDerivAt_calogeroSecondMoment (c := c) (hd t ht) (hinj t ht)
    have h2 : HasDerivAt (fun s : ℝ => 2 * (S.card : ℝ) * ((S.card : ℝ) - 1) * s)
        (2 * (S.card : ℝ) * ((S.card : ℝ) - 1)) t := by
      simpa using (hasDerivAt_id t).const_mul (2 * (S.card : ℝ) * ((S.card : ℝ) - 1))
    have h3 := h1.add h2
    have hz : -2 * (S.card : ℝ) * ((S.card : ℝ) - 1)
        + 2 * (S.card : ℝ) * ((S.card : ℝ) - 1) = 0 := by ring
    rwa [hz] at h3
  have hcont : ContinuousOn (fun s => calogeroSecondMoment S (x s) c
      + 2 * (S.card : ℝ) * ((S.card : ℝ) - 1) * s) (Set.Icc 0 T) :=
    fun t ht => ((hderiv t ht).continuousAt).continuousWithinAt
  obtain ⟨ξ, hξ, hslope⟩ :=
    exists_hasDerivAt_eq_slope _ (fun _ => (0 : ℝ)) hT hcont
      (fun t ht => hderiv t (Set.mem_Icc_of_Ioo ht))
  have hTne : T - 0 ≠ 0 := by
    simp only [sub_zero]; exact hT.ne'
  rw [eq_comm, div_eq_iff hTne] at hslope
  simp only [sub_zero, zero_mul] at hslope
  linarith

/-- **Finite-time collapse.**  The attractive pair flow cannot be continued past
`∑_j (x_j(0) - c)² / (2N(N-1))`: some pair must collide. -/
theorem calogero_collapse_time_le [DecidableEq ι] {S : Finset ι} {x : ℝ → ι → ℝ} {c T : ℝ}
    (hT : 0 < T) (hcard : 2 ≤ S.card)
    (hd : ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ j ∈ S,
      HasDerivAt (fun s => x s j) (-2 * calogeroField S (x t) j) t)
    (hinj : ∀ t ∈ Set.Icc (0 : ℝ) T, Set.InjOn (x t) S) :
    T ≤ calogeroSecondMoment S (x 0) c / (2 * (S.card : ℝ) * ((S.card : ℝ) - 1)) := by
  have hN : (2 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hcard
  have hpos : 0 < 2 * (S.card : ℝ) * ((S.card : ℝ) - 1) := by nlinarith
  have hlin := calogeroSecondMoment_eq_of_flow (c := c) hT hd hinj
  have hnn := calogeroSecondMoment_nonneg S (x T) c
  rw [le_div_iff₀ hpos]
  nlinarith

/-! ### The external field of a window -/

/-- Centring at the centroid cancels the leading effect of a distant zero exactly: what remains
is quadratic in the window radius. -/
theorem external_shift_eq {S : Finset ι} {u : ι → ℝ} {d : ℝ} (hd : d ≠ 0)
    (hu : ∀ j ∈ S, d - u j ≠ 0) (hsum : ∑ j ∈ S, u j = 0) :
    ∑ j ∈ S, u j / (d - u j) = ∑ j ∈ S, (u j) ^ (2 : ℕ) / (d * (d - u j)) := by
  have hterm : ∀ j ∈ S, u j / (d - u j) = u j / d + (u j) ^ (2 : ℕ) / (d * (d - u j)) := by
    intro j hj
    have hj' := hu j hj
    field_simp
    ring
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib]
  have hz : ∑ j ∈ S, u j / d = 0 := by
    simp only [div_eq_mul_inv, ← Finset.sum_mul, hsum, zero_mul]
  rw [hz, zero_add]

/-- A zero outside the window has `d(d-u) ≥ |d|(|d|-r) > 0`: the external term never changes
sign, so the outside configuration can only *oppose* collapse. -/
theorem external_denom_ge {u d r : ℝ} (hu : |u| ≤ r) (hd : r < |d|) :
    0 < |d| * (|d| - r) ∧ |d| * (|d| - r) ≤ d * (d - u) := by
  have hr : 0 ≤ r := le_trans (abs_nonneg u) hu
  have hdpos : 0 < |d| := lt_of_le_of_lt hr hd
  obtain ⟨hlb, hub⟩ := abs_le.mp hu
  have hgap : 0 < |d| - r := by linarith
  refine ⟨by positivity, ?_⟩
  have hdne : d ≠ 0 := abs_pos.mp hdpos
  rcases lt_or_gt_of_ne hdne with hneg | hpos
  · rw [abs_of_neg hneg]; nlinarith
  · rw [abs_of_pos hpos]; nlinarith

theorem external_sum_nonneg {S : Finset ι} {u : ι → ℝ} {d r : ℝ}
    (hu : ∀ j ∈ S, |u j| ≤ r) (hd : r < |d|) :
    0 ≤ ∑ j ∈ S, (u j) ^ (2 : ℕ) / (d * (d - u j)) := by
  refine Finset.sum_nonneg fun j hj => ?_
  obtain ⟨h1, h2⟩ := external_denom_ge (hu j hj) hd
  exact div_nonneg (by positivity) (le_of_lt (lt_of_lt_of_le h1 h2))

private theorem div_le_div_left_aux {a B A : ℝ} (ha : 0 ≤ a) (hA : 0 < A) (hAB : A ≤ B) :
    a / B ≤ a / A := by
  have hB : 0 < B := lt_of_lt_of_le hA hAB
  rw [div_le_iff₀ hB, div_mul_eq_mul_div, le_div_iff₀ hA]
  nlinarith

/-- The total external correction is controlled by the second moment of the window itself. -/
theorem external_sum_le {S : Finset ι} {u : ι → ℝ} {d r : ℝ}
    (hu : ∀ j ∈ S, |u j| ≤ r) (hd : r < |d|) :
    ∑ j ∈ S, (u j) ^ (2 : ℕ) / (d * (d - u j))
      ≤ (∑ j ∈ S, (u j) ^ (2 : ℕ)) / (|d| * (|d| - r)) := by
  rw [Finset.sum_div]
  refine Finset.sum_le_sum fun j hj => ?_
  obtain ⟨h1, h2⟩ := external_denom_ge (hu j hj) hd
  exact div_le_div_left_aux (by positivity) h1 h2

/-! ### The localisation obstruction -/

/-- **No localised virial weight.**  A convex function on `ℝ` bounded above is constant.  Since
the observables with a sign along the flow are exactly the convex ones, no nonconstant observable
with a sign is supported in a bounded window: the sign law and localisation are incompatible. -/
theorem eq_of_convexOn_univ_of_le {φ : ℝ → ℝ} (hφ : ConvexOn ℝ Set.univ φ) {M : ℝ}
    (hM : ∀ y, φ y ≤ M) (a b : ℝ) : φ a = φ b := by
  have key : ∀ p q : ℝ, p < q → φ p = φ q := by
    intro p q hpq
    set sl : ℝ := (φ q - φ p) / (q - p) with hsl
    have hqp : 0 < q - p := sub_pos.mpr hpq
    rcases lt_trichotomy sl 0 with hneg | hzero | hpos
    · exfalso
      have hslne : sl ≠ 0 := ne_of_lt hneg
      have hns : 0 < -sl := by linarith
      have hMp : 0 < M - φ p + 1 := by linarith [hM p]
      set e : ℝ := (M - φ p + 1) / (-sl) with he
      have hepos : 0 < e := div_pos hMp hns
      have hse : sl * e = φ p - M - 1 := by
        rw [he]; field_simp; ring
      have hcp : p - e < p := by linarith
      have hmono := hφ.slope_mono_adjacent (Set.mem_univ (p - e)) (Set.mem_univ q) hcp hpq
      rw [← hsl] at hmono
      have hdd : p - (p - e) = e := by ring
      rw [hdd] at hmono
      rw [div_le_iff₀ hepos] at hmono
      linarith [hM (p - e)]
    · have : φ q - φ p = sl * (q - p) := by
        rw [hsl]; field_simp
      rw [hzero] at this
      linarith
    · exfalso
      have hslne : sl ≠ 0 := ne_of_gt hpos
      have hMq : 0 < M - φ q + 1 := by linarith [hM q]
      set e : ℝ := (M - φ q + 1) / sl with he
      have hepos : 0 < e := div_pos hMq hpos
      have hse : sl * e = M - φ q + 1 := by
        rw [he]; field_simp
      have hqc : q < q + e := by linarith
      have hmono := hφ.slope_mono_adjacent (Set.mem_univ p) (Set.mem_univ (q + e)) hpq hqc
      rw [← hsl] at hmono
      have hdd : q + e - q = e := by ring
      rw [hdd] at hmono
      rw [le_div_iff₀ hepos] at hmono
      linarith [hM (q + e)]
  rcases lt_trichotomy a b with h | h | h
  · exact key a b h
  · rw [h]
  · exact (key b a h).symm

end RHTower
