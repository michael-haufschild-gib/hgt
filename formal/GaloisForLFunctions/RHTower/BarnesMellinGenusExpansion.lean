import GaloisForLFunctions.RHTower.BarnesMellinGenusRepresentation
import GaloisForLFunctions.RHTower.BarnesMellinNegResidues

/-!
# The Barnes expansion at arbitrary genus

For `g < 1/s < g+1` the singularities of

```text
F_m(w) = (-w)^m x^{-w} ζ(-sw) (-π/sin πw)
```

to the right of the strip `-(g+1) < Re w < -g` are, in order, the pullback `-1/s` of the pole of
zeta and then every integer `-g, -g+1, -g+2, …`.  The ladder

```text
σ_0 = -((g+1) + 1/s)/2 ,  σ_1 = -(g + 1/s)/2 ,  σ_{k+2} = k - g + 1/2
```

separates them: `-1/s` lies between `σ_0` and `σ_1`, and the integer `k - g` lies between
`σ_{k+1}` and `σ_{k+2}`.  Each step crosses exactly one simple pole, so the shifted contour is the
sum minus the residues already collected, and the modulus of the remaining integral is
`O(x^{-σ_K})`.

At `m = 0` the crossed residues are `-(-1)^j ζ(-sj) x^{-j}`: for `j < 0` the ascending powers
`(-1)^j ζ(s|j|) x^{|j|}`, for `j = 0` the constant `-1/2` and for `j > 0` the descending Barnes
tail `(-1)^j ζ(-sj) x^{-j}`.
-/

open Complex Filter Set MeasureTheory

namespace RHTower

open GaloisForLFunctions.HTGeometry

noncomputable section

/-! ### The residue at an arbitrary integer -/

/-- The residue of `F_m` at the integer `j`, as it enters the expansion. -/
def barnesIntResidue (s x : ℝ) (m : ℕ) (j : ℤ) : ℂ :=
  (-(j : ℂ)) ^ m * (((x : ℝ) : ℂ) ^ (-(j : ℂ)) * riemannZeta (-(s : ℂ) * (j : ℂ)))
    * (-(-1 : ℂ) ^ j)

/-- **Crossing an integer of either sign.** -/
theorem verticalIntegral'_shift_int {s x : ℝ} (hs : 0 < s) (hx : 0 < x) (m : ℕ) (j : ℤ)
    {σ σ' : ℝ} (hσ : σ < (j : ℝ)) (hσ' : (j : ℝ) < σ')
    (hlow : (j : ℝ) - 1 < σ) (hhigh : σ' < (j : ℝ) + 1)
    (hzeta : -(1 / s) < σ)
    (hσsin : Real.sin (Real.pi * σ) ≠ 0) (hσ'sin : Real.sin (Real.pi * σ') ≠ 0)
    (hσz : -(s : ℝ) * σ ≠ 1) (hσ'z : -(s : ℝ) * σ' ≠ 1) :
    VerticalIntegral' (barnesIntegrandPow s x m) σ'
        - VerticalIntegral' (barnesIntegrandPow s x m) σ
      = barnesIntResidue s x m j := by
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg j
  · subst hk
    have hzp : ((-1 : ℂ)) ^ ((k : ℕ) : ℤ) = ((-1 : ℂ)) ^ (k : ℕ) := zpow_natCast _ _
    have hcC : (((k : ℕ) : ℤ) : ℂ) = ((k : ℕ) : ℂ) := by push_cast; ring
    have hcR : (((k : ℕ) : ℤ) : ℝ) = ((k : ℕ) : ℝ) := by push_cast; ring
    rw [barnesIntResidue, hzp, hcC]
    rw [hcR] at hσ hσ' hlow hhigh
    exact verticalIntegral'_shift_nat hs hx m k hσ hσ' hlow hhigh hzeta hσsin hσ'sin hσz hσ'z
  · subst hk
    have hsign : ((-1 : ℂ)) ^ (k : ℕ) * ((-1 : ℂ)) ^ (k : ℕ) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]
      norm_num
    have hzp : ((-1 : ℂ)) ^ (-((k : ℕ) : ℤ)) = ((-1 : ℂ)) ^ (k : ℕ) := by
      rw [zpow_neg, zpow_natCast]
      exact inv_eq_of_mul_eq_one_right hsign
    have hcC : ((-((k : ℕ) : ℤ) : ℤ) : ℂ) = -((k : ℕ) : ℂ) := by push_cast; ring
    have hcR : ((-((k : ℕ) : ℤ) : ℤ) : ℝ) = -((k : ℕ) : ℝ) := by push_cast; ring
    rw [barnesIntResidue, hzp, hcC]
    rw [hcR] at hσ hσ' hlow hhigh
    exact verticalIntegral'_shift_negNat hs hx m k hσ hσ' (by linarith) (by linarith) hzeta
      hσsin hσ'sin hσz hσ'z

/-! ### The ladder -/

/-- The abscissae of the genus-`g` ladder. -/
def genusAbscissa (s : ℝ) (g : ℕ) : ℕ → ℝ
  | 0 => -(((g : ℝ) + 1 + 1 / s) / 2)
  | 1 => -(((g : ℝ) + 1 / s) / 2)
  | (k + 2) => (k : ℝ) - (g : ℝ) + 1 / 2

@[simp] theorem genusAbscissa_zero (s : ℝ) (g : ℕ) :
    genusAbscissa s g 0 = -(((g : ℝ) + 1 + 1 / s) / 2) := rfl

@[simp] theorem genusAbscissa_one (s : ℝ) (g : ℕ) :
    genusAbscissa s g 1 = -(((g : ℝ) + 1 / s) / 2) := rfl

@[simp] theorem genusAbscissa_add_two (s : ℝ) (g : ℕ) (k : ℕ) :
    genusAbscissa s g (k + 2) = (k : ℝ) - (g : ℝ) + 1 / 2 := rfl

variable {s : ℝ} {g : ℕ}

theorem genusAbscissa_zero_lt (hgu : 1 / s < (g : ℝ) + 1) :
    -((g : ℝ) + 1) < genusAbscissa s g 0 := by
  rw [genusAbscissa_zero]
  linarith

theorem genusAbscissa_zero_lt_zetaPole : genusAbscissa s g 0 < -(1 / s) ↔ 1 / s < (g : ℝ) + 1 := by
  rw [genusAbscissa_zero]
  constructor <;> intro h <;> linarith

theorem zetaPole_lt_genusAbscissa_one (hgl : (g : ℝ) < 1 / s) :
    -(1 / s) < genusAbscissa s g 1 := by
  rw [genusAbscissa_one]
  linarith

theorem genusAbscissa_one_lt (hgl : (g : ℝ) < 1 / s) : genusAbscissa s g 1 < -(g : ℝ) := by
  rw [genusAbscissa_one]
  linarith

/-- Every abscissa of the ladder from the second one on is to the right of the zeta pole. -/
theorem zetaPole_lt_genusAbscissa (hgl : (g : ℝ) < 1 / s) (k : ℕ) :
    -(1 / s) < genusAbscissa s g (k + 1) := by
  cases k with
  | zero => exact zetaPole_lt_genusAbscissa_one hgl
  | succ n =>
      rw [genusAbscissa_add_two]
      have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith

theorem sin_pi_genusAbscissa_zero_ne_zero (hgl : (g : ℝ) < 1 / s) (hgu : 1 / s < (g : ℝ) + 1) :
    Real.sin (Real.pi * genusAbscissa s g 0) ≠ 0 := by
  refine sin_pi_ne_zero_of_mem_gap (n := -(g : ℤ) - 1) ?_ ?_
  · rw [genusAbscissa_zero]; push_cast; linarith
  · rw [genusAbscissa_zero]; push_cast; linarith

theorem sin_pi_genusAbscissa_one_ne_zero (hgl : (g : ℝ) < 1 / s) (hgu : 1 / s < (g : ℝ) + 1) :
    Real.sin (Real.pi * genusAbscissa s g 1) ≠ 0 := by
  refine sin_pi_ne_zero_of_mem_gap (n := -(g : ℤ) - 1) ?_ ?_
  · rw [genusAbscissa_one]; push_cast; linarith
  · rw [genusAbscissa_one]; push_cast; linarith

theorem sin_pi_genusAbscissa_add_two_ne_zero (k : ℕ) :
    Real.sin (Real.pi * genusAbscissa s g (k + 2)) ≠ 0 := by
  refine sin_pi_ne_zero_of_mem_gap (n := (k : ℤ) - (g : ℤ)) ?_ ?_
  · rw [genusAbscissa_add_two]; push_cast; linarith
  · rw [genusAbscissa_add_two]; push_cast; linarith

theorem sin_pi_genusAbscissa_ne_zero (hgl : (g : ℝ) < 1 / s) (hgu : 1 / s < (g : ℝ) + 1) (k : ℕ) :
    Real.sin (Real.pi * genusAbscissa s g k) ≠ 0 := by
  match k with
  | 0 => exact sin_pi_genusAbscissa_zero_ne_zero hgl hgu
  | 1 => exact sin_pi_genusAbscissa_one_ne_zero hgl hgu
  | (n + 2) => exact sin_pi_genusAbscissa_add_two_ne_zero n

/-- An abscissa away from `-1/s` is not annihilated by the zeta factor. -/
theorem mul_genusAbscissa_ne_one (hs : 0 < s) {σ : ℝ} (hσ : σ ≠ -(1 / s)) :
    -(s : ℝ) * σ ≠ 1 := by
  intro hcon
  refine hσ ?_
  have hsne : s ≠ 0 := ne_of_gt hs
  field_simp
  linarith

theorem genusAbscissa_ne_zetaPole (hgl : (g : ℝ) < 1 / s) (hgu : 1 / s < (g : ℝ) + 1) (k : ℕ) :
    genusAbscissa s g k ≠ -(1 / s) := by
  match k with
  | 0 =>
      have h := genusAbscissa_zero_lt_zetaPole (s := s) (g := g) |>.mpr hgu
      exact ne_of_lt h
  | (n + 1) => exact ne_of_gt (zetaPole_lt_genusAbscissa hgl n)

/-! ### The first step: the pole of zeta -/

/-- The residue of the zeta pole, as it enters the expansion. -/
def barnesLeadingGenusResidue (s x : ℝ) (m : ℕ) : ℂ :=
  (-(-(1 / ((s : ℝ) : ℂ)))) ^ m * (((x : ℝ) : ℂ) ^ (-(-(1 / ((s : ℝ) : ℂ))))
      * -((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * (-(1 / ((s : ℝ) : ℂ))))))
    * (-(1 / (s : ℂ)))

/-- **Crossing the pole of zeta.**  Between the first two abscissae the only singularity is
`w = -1/s`. -/
theorem verticalIntegral'_shift_genusZetaPole {x : ℝ} (hs : 0 < s) (hx : 0 < x) (m : ℕ)
    (hgl : (g : ℝ) < 1 / s) (hgu : 1 / s < (g : ℝ) + 1) :
    VerticalIntegral' (barnesIntegrandPow s x m) (genusAbscissa s g 1)
        - VerticalIntegral' (barnesIntegrandPow s x m) (genusAbscissa s g 0)
      = barnesLeadingGenusResidue s x m := by
  set p : ℂ := -(1 / ((s : ℝ) : ℂ)) with hpdef
  have hpre : p.re = -(1 / s) := by rw [hpdef]; simp
  have hsne : ((s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs)
  have hpmul : -((s : ℝ) : ℂ) * p = 1 := by
    rw [hpdef]
    field_simp
  have hσp : genusAbscissa s g 0 < p.re := by
    rw [hpre]
    exact genusAbscissa_zero_lt_zetaPole.mpr hgu
  have hpσ' : p.re < genusAbscissa s g 1 := by
    rw [hpre]
    exact zetaPole_lt_genusAbscissa_one hgl
  have hsinp : Complex.sin ((Real.pi : ℂ) * p) ≠ 0 := by
    intro hcon
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hcon
    have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
    have hpk : p = (k : ℂ) := mul_left_cancel₀ hpi (by rw [hk]; ring)
    have hre : p.re = (k : ℝ) := by rw [hpk]; simp
    rw [hpre] at hre
    have hk0 : (k : ℝ) < -(g : ℝ) := by rw [← hre]; linarith
    have hk1 : -((g : ℝ) + 1) < (k : ℝ) := by rw [← hre]; linarith
    have hkz0 : k < -(g : ℤ) := by exact_mod_cast (by push_cast; linarith : ((k : ℤ) : ℝ) < ((-(g : ℤ) : ℤ) : ℝ))
    have hkz1 : -(g : ℤ) - 1 < k := by
      exact_mod_cast (by push_cast; linarith : ((-(g : ℤ) - 1 : ℤ) : ℝ) < ((k : ℤ) : ℝ))
    omega
  have hreg : ∀ w : ℂ, w.re ∈ Set.Icc (genusAbscissa s g 0) (genusAbscissa s g 1) → w ≠ p →
      -((s : ℝ) : ℂ) * w ≠ 1 ∧ Complex.sin ((Real.pi : ℂ) * w) ≠ 0 := by
    intro w hw hne
    obtain ⟨hwl, hwr⟩ := hw
    refine barnes_regular_of_ne (fun hcon => hne ?_) (fun k hk => ?_)
    · rw [eq_zetaPole_of_mul_eq_one hs hcon, hpdef]
    · have hre : w.re = (k : ℝ) := by rw [hk]; simp
      rw [hre] at hwl hwr
      have hk0 : (k : ℝ) < -(g : ℝ) := by
        have := genusAbscissa_one_lt (s := s) (g := g) hgl
        linarith
      have hk1 : -((g : ℝ) + 1) < (k : ℝ) := by
        have := genusAbscissa_zero_lt (s := s) (g := g) hgu
        linarith
      have hkz0 : k < -(g : ℤ) := by
        exact_mod_cast (by push_cast; linarith : ((k : ℤ) : ℝ) < ((-(g : ℤ) : ℤ) : ℝ))
      have hkz1 : -(g : ℤ) - 1 < k := by
        exact_mod_cast (by push_cast; linarith : ((-(g : ℤ) - 1 : ℤ) : ℝ) < ((k : ℤ) : ℝ))
      omega
  have hres := verticalIntegral'_barnes_shift hs hx m hσp hpσ' hreg
    (barnesIntegrandPow_simplePole_at_zetaPole hs hx m hpmul hsinp)
    (sin_pi_genusAbscissa_ne_zero hgl hgu 0)
    (mul_genusAbscissa_ne_one hs (genusAbscissa_ne_zetaPole hgl hgu 0))
    (sin_pi_genusAbscissa_ne_zero hgl hgu 1)
    (mul_genusAbscissa_ne_one hs (genusAbscissa_ne_zetaPole hgl hgu 1))
  rw [hres, barnesLeadingGenusResidue, hpdef]

/-! ### The integer steps -/

/-- **One integer step of the ladder.**  Passing from the `(k+1)`-st abscissa to the next crosses
the integer `k - g`. -/
theorem verticalIntegral'_genus_shift_step {x : ℝ} (hs : 0 < s) (hx : 0 < x) (m : ℕ)
    (hgl : (g : ℝ) < 1 / s) (hgu : 1 / s < (g : ℝ) + 1) (k : ℕ) :
    VerticalIntegral' (barnesIntegrandPow s x m) (genusAbscissa s g (k + 2))
        - VerticalIntegral' (barnesIntegrandPow s x m) (genusAbscissa s g (k + 1))
      = barnesIntResidue s x m ((k : ℤ) - (g : ℤ)) := by
  have hjR : (((k : ℤ) - (g : ℤ) : ℤ) : ℝ) = (k : ℝ) - (g : ℝ) := by push_cast; ring
  refine verticalIntegral'_shift_int hs hx m ((k : ℤ) - (g : ℤ)) ?_ ?_ ?_ ?_
    (zetaPole_lt_genusAbscissa hgl k)
    (sin_pi_genusAbscissa_ne_zero hgl hgu (k + 1))
    (sin_pi_genusAbscissa_ne_zero hgl hgu (k + 2))
    (mul_genusAbscissa_ne_one hs (genusAbscissa_ne_zetaPole hgl hgu (k + 1)))
    (mul_genusAbscissa_ne_one hs (genusAbscissa_ne_zetaPole hgl hgu (k + 2)))
  · rw [hjR]
    cases k with
    | zero =>
        rw [genusAbscissa_one]
        push_cast
        linarith
    | succ n =>
        rw [genusAbscissa_add_two]
        push_cast
        linarith
  · rw [hjR, genusAbscissa_add_two]
    linarith
  · rw [hjR]
    cases k with
    | zero =>
        rw [genusAbscissa_one]
        push_cast
        linarith
    | succ n =>
        rw [genusAbscissa_add_two]
        push_cast
        linarith
  · rw [hjR, genusAbscissa_add_two]
    linarith

/-! ### The finite expansion -/

/-- **The finite Barnes expansion at genus `g`.**  Shifting the initial contour rightwards past the
zeta pole and the first `K` integers leaves the contour at the `(K+1)`-st abscissa. -/
theorem verticalIntegral'_genus_finite_expansion {x : ℝ} (hs : 0 < s) (hx : 0 < x) (m : ℕ)
    (hgl : (g : ℝ) < 1 / s) (hgu : 1 / s < (g : ℝ) + 1) (K : ℕ) :
    VerticalIntegral' (barnesIntegrandPow s x m) (genusAbscissa s g 0)
      = VerticalIntegral' (barnesIntegrandPow s x m) (genusAbscissa s g (K + 1))
        - barnesLeadingGenusResidue s x m
        - ∑ k ∈ Finset.range K, barnesIntResidue s x m ((k : ℤ) - (g : ℤ)) := by
  have htel : ∑ k ∈ Finset.range K,
      (VerticalIntegral' (barnesIntegrandPow s x m) (genusAbscissa s g (k + 1 + 1))
        - VerticalIntegral' (barnesIntegrandPow s x m) (genusAbscissa s g (k + 1)))
      = VerticalIntegral' (barnesIntegrandPow s x m) (genusAbscissa s g (K + 1))
        - VerticalIntegral' (barnesIntegrandPow s x m) (genusAbscissa s g (0 + 1)) :=
    Finset.sum_range_sub
      (fun k => VerticalIntegral' (barnesIntegrandPow s x m) (genusAbscissa s g (k + 1))) K
  have hsteps : ∑ k ∈ Finset.range K,
      (VerticalIntegral' (barnesIntegrandPow s x m) (genusAbscissa s g (k + 1 + 1))
        - VerticalIntegral' (barnesIntegrandPow s x m) (genusAbscissa s g (k + 1)))
      = ∑ k ∈ Finset.range K, barnesIntResidue s x m ((k : ℤ) - (g : ℤ)) := by
    refine Finset.sum_congr rfl fun k _ => ?_
    exact verticalIntegral'_genus_shift_step hs hx m hgl hgu k
  rw [hsteps] at htel
  have hzeta := verticalIntegral'_shift_genusZetaPole hs hx m hgl hgu
  have hzero : (0 : ℕ) + 1 = 1 := rfl
  rw [hzero] at htel
  linear_combination htel - hzeta

/-! ### The expansion of the canonical-product sum -/

theorem genusAbscissa_zero_mem (hs : 0 < s) (hgl : (g : ℝ) < 1 / s)
    (hgu : 1 / s < (g : ℝ) + 1) :
    -((g : ℝ) + 1) < genusAbscissa s g 0 ∧ genusAbscissa s g 0 < -(g : ℝ)
      ∧ s * genusAbscissa s g 0 < -1 := by
  refine ⟨genusAbscissa_zero_lt hgu, ?_, ?_⟩
  · have h1 : genusAbscissa s g 0 < -(1 / s) := genusAbscissa_zero_lt_zetaPole.mpr hgu
    have h2 : -(1 / s) < -(g : ℝ) := by linarith
    linarith
  · rw [genusAbscissa_zero]
    have hval : s * -(((g : ℝ) + 1 + 1 / s) / 2) = -(s * ((g : ℝ) + 1) + 1) / 2 := by
      field_simp
    rw [hval]
    have hkey : 1 < s * ((g : ℝ) + 1) := by
      rw [div_lt_iff₀ hs] at hgu
      linarith [mul_comm ((g : ℝ) + 1) s]
    linarith

/-- **The Barnes expansion of the genus-`g` canonical-product sum.**  The sum of the rescaled model
factors is the shifted contour integral minus the residues already crossed. -/
theorem hasSum_barnes_genus_expansion {x : ℝ} (hs : 0 < s) (hx : 0 < x)
    (hgl : (g : ℝ) < 1 / s) (hgu : 1 / s < (g : ℝ) + 1) (K : ℕ) :
    HasSum (fun n : ℕ => ((-1) ^ g : ℂ) * barnesModel g (x / ((n : ℝ) + 1) ^ s))
      (VerticalIntegral' (barnesIntegrandPow s x 0) (genusAbscissa s g (K + 1))
        - barnesLeadingGenusResidue s x 0
        - ∑ k ∈ Finset.range K, barnesIntResidue s x 0 ((k : ℤ) - (g : ℤ))) := by
  obtain ⟨h1, h2, hsσ⟩ := genusAbscissa_zero_mem hs hgl hgu
  have hbase := hasSum_barnesModel_verticalIntegral' (g := g) (s := s) (x := x)
    (σ := genusAbscissa s g 0) hx h1 h2 hsσ
  have hpow : VerticalIntegral' (barnesIntegrand s x) (genusAbscissa s g 0)
      = VerticalIntegral' (barnesIntegrandPow s x 0) (genusAbscissa s g 0) :=
    congrArg (fun f => VerticalIntegral' f (genusAbscissa s g 0))
      (funext fun w => (barnesIntegrandPow_zero s x w).symm)
  rw [hpow, verticalIntegral'_genus_finite_expansion hs hx 0 hgl hgu K] at hbase
  exact hbase

/-- **The Barnes expansion at genus `g` with explicit error.**  After the leading term and the first
`K` crossed integers the error is `O(x^{-σ_{K+1}})`, uniformly in `x > 0`. -/
theorem barnes_genus_poincare_expansion (hs : 0 < s) (hgl : (g : ℝ) < 1 / s)
    (hgu : 1 / s < (g : ℝ) + 1) (K : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 0 < x →
      ‖(∑' n : ℕ, ((-1) ^ g : ℂ) * barnesModel g (x / ((n : ℝ) + 1) ^ s))
          + barnesLeadingGenusResidue s x 0
          + ∑ k ∈ Finset.range K, barnesIntResidue s x 0 ((k : ℤ) - (g : ℤ))‖
        ≤ C * x ^ (-(genusAbscissa s g (K + 1))) := by
  set σK : ℝ := genusAbscissa s g (K + 1) with hσK
  set C : ℝ :=
    (2 * Real.pi)⁻¹ * ∫ t : ℝ, ‖barnesIntegrandPow s 1 0 ((σK : ℂ) + (t : ℂ) * I)‖ with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    exact mul_nonneg (by positivity) (MeasureTheory.integral_nonneg fun t => norm_nonneg _)
  refine ⟨C, hC0, fun x hx => ?_⟩
  have hsum := hasSum_barnes_genus_expansion hs hx hgl hgu K
  have hval : (∑' n : ℕ, ((-1) ^ g : ℂ) * barnesModel g (x / ((n : ℝ) + 1) ^ s))
      + barnesLeadingGenusResidue s x 0
      + ∑ k ∈ Finset.range K, barnesIntResidue s x 0 ((k : ℤ) - (g : ℤ))
      = VerticalIntegral' (barnesIntegrandPow s x 0) σK := by
    rw [hsum.tsum_eq, ← hσK]
    ring
  rw [hval]
  exact norm_verticalIntegral'_barnesPow_le 0 hx

end

end RHTower
