import GaloisForLFunctions.RHTower.ConstrainedProlateRayleighFloor

/-!
# The constrained Rayleigh floor is attained only on the secular ray

If a constrained coordinate vector realizes the ground root as its Rayleigh value, it is a scalar
multiple of the secular vector.  The mechanism needs no equality case of Cauchy–Schwarz: because
`(d_j − μ₀)v_j = ℓ_j` and `∑ ℓ_j v_j = 0`, the secular vector lies in the radical of the shifted
quadratic form on the constraint hyperplane, so subtracting the right multiple of it leaves a
constrained vector with vanishing head coordinate and the same, vanishing, form value — and away
from the head every coefficient of the form is strictly positive.
-/

noncomputable section

open Filter Set

namespace RHTower

variable {d ℓ : ℕ → ℝ}

theorem summable_secularVector_sq (h01 : d 0 < d 1) (h12 : d 1 < d 2)
    (hd2 : ∀ j, d 2 ≤ d (j + 2)) (hsum : Summable fun j => ℓ j ^ (2 : ℕ))
    (hℓ0 : ℓ 0 ≠ 0) (hℓ1 : ℓ 1 ≠ 0) :
    Summable fun j : ℕ => secularVector d ℓ (infiniteSecularRoot d ℓ) j ^ (2 : ℕ) := by
  obtain ⟨hrmem, _, _⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsum hℓ0 hℓ1
  exact (summable_nat_add_iff
      (f := fun j => secularVector d ℓ (infiniteSecularRoot d ℓ) j ^ (2 : ℕ)) 2).mp
    (summable_secularVector_sq_tail hd2 hsum (by linarith [hrmem.2]))

/-- **Rigidity of the constrained Rayleigh floor.**  A constrained vector whose Rayleigh value is
the secular ground root is a multiple of the secular vector. -/
theorem eq_smul_secularVector_of_rayleigh_eq (h01 : d 0 < d 1) (h12 : d 1 < d 2)
    (hd2 : ∀ j, d 2 ≤ d (j + 2)) (hsum : Summable fun j => ℓ j ^ (2 : ℕ))
    (hℓ0 : ℓ 0 ≠ 0) (hℓ1 : ℓ 1 ≠ 0)
    {x : ℕ → ℝ} (hx2 : Summable fun j => x j ^ (2 : ℕ))
    (hdx : Summable fun j => d j * x j ^ (2 : ℕ))
    (hcon : (∑' j : ℕ, ℓ j * x j) = 0)
    (heq : infiniteSecularRoot d ℓ * ∑' j : ℕ, x j ^ (2 : ℕ) = ∑' j : ℕ, d j * x j ^ (2 : ℕ)) :
    ∀ j : ℕ, x j = (x 0 / secularVector d ℓ (infiniteSecularRoot d ℓ) 0)
      * secularVector d ℓ (infiniteSecularRoot d ℓ) j := by
  obtain ⟨hrmem, hr0, _⟩ := infiniteSecularRoot_spec h01 h12 hd2 hsum hℓ0 hℓ1
  set μ := infiniteSecularRoot d ℓ with hμdef
  set v : ℕ → ℝ := secularVector d ℓ μ with hvdef
  have hμ0 : d 0 < μ := hrmem.1
  have hμ1 : μ < d 1 := hrmem.2
  have hpos : ∀ j : ℕ, 0 < d (j + 1) - μ := by
    intro j
    match j with
    | 0 => linarith
    | (m + 1) => have := hd2 m; linarith [h12]
  have hv0 : v 0 ≠ 0 := by
    rw [hvdef, secularVector]
    exact div_ne_zero hℓ0 (sub_ne_zero.mpr (ne_of_lt hμ0))
  have hsv : Summable fun j : ℕ => v j ^ (2 : ℕ) :=
    summable_secularVector_sq h01 h12 hd2 hsum hℓ0 hℓ1
  have hvterm : ∀ j : ℕ, (d j - μ) * v j = ℓ j := by
    intro j
    have hne : d j - μ ≠ 0 := secular_pole_ne h12 hd2 hrmem j
    rw [hvdef, secularVector]
    field_simp
  have hconv : (∑' j : ℕ, ℓ j * v j) = 0 := secularVector_constraint h01 h12 hd2 hsum hℓ0 hℓ1
  have hslv : Summable fun j : ℕ => ℓ j * v j := summable_mul_of_sq_summable hsum hsv
  have hslx : Summable fun j : ℕ => ℓ j * x j := summable_mul_of_sq_summable hsum hx2
  set t : ℝ := x 0 / v 0 with htdef
  set z : ℕ → ℝ := fun j => x j - t * v j with hzdef
  have hz0 : z 0 = 0 := by
    rw [hzdef, htdef]
    field_simp
    ring
  -- the three shifted summable pieces
  have hqx : Summable fun j : ℕ => (d j - μ) * x j ^ (2 : ℕ) :=
    (hdx.sub (hx2.mul_left μ)).congr fun j => by ring
  have hqv : Summable fun j : ℕ => (d j - μ) * v j ^ (2 : ℕ) :=
    hslv.congr fun j => by rw [← hvterm j]; ring
  have hqvx : Summable fun j : ℕ => (d j - μ) * v j * x j :=
    hslx.congr fun j => by rw [← hvterm j]
  have hqxval : (∑' j : ℕ, (d j - μ) * x j ^ (2 : ℕ)) = 0 := by
    have h1 : (∑' j : ℕ, (d j - μ) * x j ^ (2 : ℕ))
        = (∑' j : ℕ, (d j * x j ^ (2 : ℕ) - μ * x j ^ (2 : ℕ))) := tsum_congr fun j => by ring
    rw [h1, Summable.tsum_sub hdx (hx2.mul_left μ), tsum_mul_left, ← heq]
    ring
  have hqvval : (∑' j : ℕ, (d j - μ) * v j ^ (2 : ℕ)) = 0 := by
    rw [tsum_congr (fun j : ℕ => by rw [← hvterm j]; ring :
      ∀ j : ℕ, (d j - μ) * v j ^ (2 : ℕ) = ℓ j * v j)]
    exact hconv
  have hqvxval : (∑' j : ℕ, (d j - μ) * v j * x j) = 0 := by
    rw [tsum_congr (fun j : ℕ => by rw [← hvterm j] :
      ∀ j : ℕ, (d j - μ) * v j * x j = ℓ j * x j)]
    exact hcon
  -- the shifted form at `z`
  have hqz : Summable fun j : ℕ => (d j - μ) * z j ^ (2 : ℕ) := by
    refine ((hqx.sub ((hqvx.mul_left (2 * t)))).add (hqv.mul_left (t ^ (2 : ℕ)))).congr fun j => ?_
    rw [hzdef]
    ring
  have hqzval : (∑' j : ℕ, (d j - μ) * z j ^ (2 : ℕ)) = 0 := by
    have hcongr : ∀ j : ℕ, (d j - μ) * z j ^ (2 : ℕ)
        = (d j - μ) * x j ^ (2 : ℕ) - 2 * t * ((d j - μ) * v j * x j)
          + t ^ (2 : ℕ) * ((d j - μ) * v j ^ (2 : ℕ)) := by
      intro j
      rw [hzdef]
      ring
    rw [tsum_congr hcongr,
      Summable.tsum_add (hqx.sub (hqvx.mul_left (2 * t))) (hqv.mul_left (t ^ (2 : ℕ))),
      Summable.tsum_sub hqx (hqvx.mul_left (2 * t)), tsum_mul_left, tsum_mul_left,
      hqxval, hqvxval, hqvval]
    ring
  -- every term vanishes
  have hnn : ∀ j : ℕ, 0 ≤ (d j - μ) * z j ^ (2 : ℕ) := by
    intro j
    match j with
    | 0 => rw [hz0]; simp
    | (m + 1) => exact mul_nonneg (le_of_lt (hpos m)) (sq_nonneg _)
  have hterm : ∀ j : ℕ, (d j - μ) * z j ^ (2 : ℕ) = 0 := by
    intro j
    have hle : (d j - μ) * z j ^ (2 : ℕ) ≤ ∑' k : ℕ, (d k - μ) * z k ^ (2 : ℕ) :=
      le_hasSum hqz.hasSum j fun k _ => hnn k
    rw [hqzval] at hle
    exact le_antisymm hle (hnn j)
  have hzero : ∀ j : ℕ, z j = 0 := by
    intro j
    match j with
    | 0 => exact hz0
    | (m + 1) =>
      have h := hterm (m + 1)
      have hne : d (m + 1) - μ ≠ 0 := ne_of_gt (hpos m)
      have hsq : z (m + 1) ^ (2 : ℕ) = 0 := by
        rcases mul_eq_zero.mp h with h1 | h2
        · exact absurd h1 hne
        · exact h2
      exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hsq
  intro j
  have := hzero j
  rw [hzdef] at this
  linarith [this]

end RHTower

end
