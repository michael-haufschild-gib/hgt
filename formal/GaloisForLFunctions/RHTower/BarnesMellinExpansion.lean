import GaloisForLFunctions.RHTower.BarnesMellinRepresentation
import GaloisForLFunctions.RHTower.BarnesMellinShift

/-!
# The Barnes expansion, one crossed pole at a time

The abscissae

```text
σ_0 = -(1+1/s)/2 ,  a_0 = -(1/s)/2 ,  a_{k+1} = k + 1/2
```

separate the singularities of the Mellin integrand: `-1/s` lies between `σ_0` and `a_0`, and the
integer `k` lies between `a_k` and `a_{k+1}`.  Each step of the shift therefore crosses exactly one
simple pole, and its residue is the corresponding term of the Barnes expansion.
-/

open Complex Filter Set MeasureTheory

namespace RHTower

noncomputable section

/-- The pullback of the zeta pole is the unique solution of `-s w = 1`. -/
theorem eq_zetaPole_of_mul_eq_one {s : ℝ} (hs : 0 < s) {w : ℂ} (h : -(s : ℂ) * w = 1) :
    w = -(1 / (s : ℂ)) := by
  have hsne : ((s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs)
  have hne : -((s : ℝ) : ℂ) ≠ 0 := neg_ne_zero.mpr hsne
  have hw : w = (-((s : ℝ) : ℂ))⁻¹ * 1 := by
    rw [← h, ← mul_assoc, inv_mul_cancel₀ hne, one_mul]
  rw [hw]
  field_simp

/-- The real part of a solution of `-s w = 1` is `-1/s`. -/
theorem re_eq_of_mul_eq_one {s : ℝ} (hs : 0 < s) {w : ℂ} (h : -(s : ℂ) * w = 1) :
    w.re = -(1 / s) := by
  rw [eq_zetaPole_of_mul_eq_one hs h]
  simp

/-- The zeta pole is off the real axis nowhere: its ordinate is zero. -/
theorem zetaPole_re : (-(1 / ((s : ℝ) : ℂ))).re = -(1 / s) := by simp

/-- **Crossing the zeta pole.**  On the strip `-(1+1/s)/2 < Re w < -(1/s)/2` the only singularity
is `w = -1/s`, and the shift picks up its residue. -/
theorem verticalIntegral'_shift_zetaPole {s x : ℝ} (hs1 : 1 < s) (hx : 0 < x) (m : ℕ) :
    VerticalIntegral' (barnesIntegrandPow s x m) (-(1 / s) / 2)
        - VerticalIntegral' (barnesIntegrandPow s x m) (-(1 + 1 / s) / 2)
      = (-(-(1 / ((s : ℝ) : ℂ)))) ^ m * (((x : ℝ) : ℂ) ^ (-(-(1 / ((s : ℝ) : ℂ))))
          * -((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * (-(1 / ((s : ℝ) : ℂ))))))
        * (-(1 / (s : ℂ))) := by
  have hs : (0 : ℝ) < s := lt_trans zero_lt_one hs1
  have hinv0 : (0 : ℝ) < 1 / s := by positivity
  have hinv1 : 1 / s < 1 := by
    rw [div_lt_one hs]; exact hs1
  set σ : ℝ := -(1 + 1 / s) / 2 with hσdef
  set σ' : ℝ := -(1 / s) / 2 with hσ'def
  set p : ℂ := -(1 / ((s : ℝ) : ℂ)) with hpdef
  have hpre : p.re = -(1 / s) := by rw [hpdef]; simp
  have hσlow : -1 < σ := by rw [hσdef]; linarith
  have hσp : σ < p.re := by rw [hpre, hσdef]; linarith
  have hpσ' : p.re < σ' := by rw [hpre, hσ'def]; linarith
  have hσ'0 : σ' < 0 := by rw [hσ'def]; linarith
  have hsne : ((s : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hs)
  have hpmul : -((s : ℝ) : ℂ) * p = 1 := by
    rw [hpdef]
    field_simp
  have hsinp : Complex.sin ((Real.pi : ℂ) * p) ≠ 0 := by
    intro hcon
    obtain ⟨k, hk⟩ := Complex.sin_eq_zero_iff.mp hcon
    have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt Real.pi_pos)
    have hpk : p = (k : ℂ) := mul_left_cancel₀ hpi (by rw [hk]; ring)
    have hre : p.re = (k : ℝ) := by rw [hpk]; simp
    rw [hpre] at hre
    have hk0 : (k : ℝ) < 0 := by rw [← hre]; linarith
    have hk1 : -1 < (k : ℝ) := by rw [← hre]; linarith
    have hkz1 : (-1 : ℤ) < k := by exact_mod_cast hk1
    have hkz0 : k < 0 := by exact_mod_cast hk0
    omega
  have hreg : ∀ w : ℂ, w.re ∈ Set.Icc σ σ' → w ≠ p →
      -((s : ℝ) : ℂ) * w ≠ 1 ∧ Complex.sin ((Real.pi : ℂ) * w) ≠ 0 := by
    intro w hw hne
    refine barnes_regular_of_ne (fun hcon => hne ?_) (fun k hk => ?_)
    · rw [eq_zetaPole_of_mul_eq_one hs hcon, hpdef]
    · have hre : w.re = (k : ℝ) := by rw [hk]; simp
      obtain ⟨hl, hr⟩ := hw
      rw [hre] at hl hr
      have hk0 : (k : ℝ) < 0 := by linarith
      have hk1 : -1 < (k : ℝ) := by linarith
      have hkz1 : (-1 : ℤ) < k := by exact_mod_cast hk1
      have hkz0 : k < 0 := by exact_mod_cast hk0
      omega
  have hσsin : Real.sin (Real.pi * σ) ≠ 0 := by
    have hlow : -Real.pi < Real.pi * σ := by nlinarith [Real.pi_pos, hσlow]
    have hhigh : Real.pi * σ < 0 := by nlinarith [Real.pi_pos, hσdef, hinv0]
    intro hcon
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hcon
    have hkr : (k : ℝ) * Real.pi = Real.pi * σ := hk
    have h1 : (k : ℝ) * Real.pi < 0 := by rw [hkr]; exact hhigh
    have h2 : -Real.pi < (k : ℝ) * Real.pi := by rw [hkr]; exact hlow
    have hk0 : (k : ℝ) < 0 := by nlinarith [Real.pi_pos]
    have hk1 : -1 < (k : ℝ) := by nlinarith [Real.pi_pos]
    have hkz1 : (-1 : ℤ) < k := by exact_mod_cast hk1
    have hkz0 : k < 0 := by exact_mod_cast hk0
    omega
  have hσ'sin : Real.sin (Real.pi * σ') ≠ 0 := by
    have hlow : -Real.pi < Real.pi * σ' := by nlinarith [Real.pi_pos, hσ'def, hinv1]
    have hhigh : Real.pi * σ' < 0 := by nlinarith [Real.pi_pos, hσ'def, hinv0]
    intro hcon
    obtain ⟨k, hk⟩ := Real.sin_eq_zero_iff.mp hcon
    have hkr : (k : ℝ) * Real.pi = Real.pi * σ' := hk
    have h1 : (k : ℝ) * Real.pi < 0 := by rw [hkr]; exact hhigh
    have h2 : -Real.pi < (k : ℝ) * Real.pi := by rw [hkr]; exact hlow
    have hk0 : (k : ℝ) < 0 := by nlinarith [Real.pi_pos]
    have hk1 : -1 < (k : ℝ) := by nlinarith [Real.pi_pos]
    have hkz1 : (-1 : ℤ) < k := by exact_mod_cast hk1
    have hkz0 : k < 0 := by exact_mod_cast hk0
    omega
  have hσz : -(s : ℝ) * σ ≠ 1 := by
    intro hcon
    have : σ = -(1 / s) := by field_simp at hcon ⊢; linarith
    rw [this] at hσp
    rw [hpre] at hσp
    exact lt_irrefl _ hσp
  have hσ'z : -(s : ℝ) * σ' ≠ 1 := by
    intro hcon
    have : σ' = -(1 / s) := by field_simp at hcon ⊢; linarith
    rw [this] at hpσ'
    rw [hpre] at hpσ'
    exact lt_irrefl _ hpσ'
  exact verticalIntegral'_barnes_shift hs hx m hσp hpσ' hreg
    (barnesIntegrandPow_simplePole_at_zetaPole hs hx m hpmul hsinp) hσsin hσz hσ'sin hσ'z


/-- **Crossing an integer.**  If the strip `[σ, σ']` meets the integers only in `k` and stays to the
right of the zeta pole, the shift picks up the kernel residue at `k`. -/
theorem verticalIntegral'_shift_nat {s x : ℝ} (hs : 0 < s) (hx : 0 < x) (m : ℕ) (k : ℕ)
    {σ σ' : ℝ} (hσ : σ < (k : ℝ)) (hσ' : (k : ℝ) < σ')
    (hlow : (k : ℝ) - 1 < σ) (hhigh : σ' < (k : ℝ) + 1)
    (hzeta : -(1 / s) < σ)
    (hσsin : Real.sin (Real.pi * σ) ≠ 0) (hσ'sin : Real.sin (Real.pi * σ') ≠ 0)
    (hσz : -(s : ℝ) * σ ≠ 1) (hσ'z : -(s : ℝ) * σ' ≠ 1) :
    VerticalIntegral' (barnesIntegrandPow s x m) σ'
        - VerticalIntegral' (barnesIntegrandPow s x m) σ
      = (-(k : ℂ)) ^ m * (((x : ℝ) : ℂ) ^ (-(k : ℂ)) * riemannZeta (-(s : ℂ) * (k : ℂ)))
        * (-(-1) ^ k) := by
  have hpre : ((k : ℂ)).re = (k : ℝ) := by simp
  have hreg : ∀ w : ℂ, w.re ∈ Set.Icc σ σ' → w ≠ (k : ℂ) →
      -((s : ℝ) : ℂ) * w ≠ 1 ∧ Complex.sin ((Real.pi : ℂ) * w) ≠ 0 := by
    intro w hw hne
    obtain ⟨hwl, hwr⟩ := hw
    refine barnes_regular_of_ne (fun hcon => ?_) (fun m hm => ?_)
    · have hre := re_eq_of_mul_eq_one hs hcon
      rw [hre] at hwl
      linarith
    · have hre : w.re = (m : ℝ) := by rw [hm]; simp
      rw [hre] at hwl hwr
      have h1 : (k : ℝ) - 1 < (m : ℝ) := lt_of_lt_of_le hlow hwl
      have h2 : (m : ℝ) < (k : ℝ) + 1 := lt_of_le_of_lt hwr hhigh
      have h1' : ((k : ℤ) : ℝ) - 1 < ((m : ℤ) : ℝ) := by push_cast; linarith
      have h2' : ((m : ℤ) : ℝ) < ((k : ℤ) : ℝ) + 1 := by push_cast; linarith
      have hz1 : (k : ℤ) - 1 < m := by exact_mod_cast h1'
      have hz2 : m < (k : ℤ) + 1 := by exact_mod_cast h2'
      have hmk : m = (k : ℤ) := by omega
      exact hne (by rw [hm, hmk]; push_cast; ring)
  refine verticalIntegral'_barnes_shift hs hx m (by rw [hpre]; exact hσ) (by rw [hpre]; exact hσ')
    hreg ?_ hσsin hσz hσ'sin hσ'z
  exact barnesIntegrandPow_simplePole_at_nat hs hx m k


/-! ### The abscissa ladder -/

/-- The abscissae of the successive contours: `-(1/s)/2` first, then the half-integers. -/
def barnesAbscissa (s : ℝ) : ℕ → ℝ
  | 0 => -(1 / s) / 2
  | (k + 1) => (k : ℝ) + 1 / 2

@[simp] theorem barnesAbscissa_zero (s : ℝ) : barnesAbscissa s 0 = -(1 / s) / 2 := rfl

@[simp] theorem barnesAbscissa_succ (s : ℝ) (k : ℕ) :
    barnesAbscissa s (k + 1) = (k : ℝ) + 1 / 2 := rfl

/-- The sine does not vanish at a half-integer. -/
theorem sin_pi_half_odd_ne_zero (n : ℕ) : Real.sin (Real.pi * ((n : ℝ) + 1 / 2)) ≠ 0 := by
  intro hcon
  obtain ⟨m, hm⟩ := Real.sin_eq_zero_iff.mp hcon
  have hpi : Real.pi ≠ 0 := ne_of_gt Real.pi_pos
  have heq : (m : ℝ) * Real.pi = ((n : ℝ) + 1 / 2) * Real.pi := by rw [hm]; ring
  have hval : (m : ℝ) = (n : ℝ) + 1 / 2 := mul_right_cancel₀ hpi heq
  have h2 : ((2 * m : ℤ) : ℝ) = ((2 * (n : ℤ) + 1 : ℤ) : ℝ) := by push_cast; linarith
  have hz : 2 * m = 2 * (n : ℤ) + 1 := by exact_mod_cast h2
  omega

/-- **One step of the ladder.**  Passing from the `k`-th abscissa to the next crosses the integer
`k` and collects its residue. -/
theorem verticalIntegral'_shift_step {s x : ℝ} (hs1 : 1 < s) (hx : 0 < x) (m : ℕ) (k : ℕ) :
    VerticalIntegral' (barnesIntegrandPow s x m) (barnesAbscissa s (k + 1))
        - VerticalIntegral' (barnesIntegrandPow s x m) (barnesAbscissa s k)
      = (-(k : ℂ)) ^ m * (((x : ℝ) : ℂ) ^ (-(k : ℂ)) * riemannZeta (-(s : ℂ) * (k : ℂ)))
        * (-(-1) ^ k) := by
  have hs : (0 : ℝ) < s := lt_trans zero_lt_one hs1
  have hinv0 : (0 : ℝ) < 1 / s := by positivity
  have hinv1 : 1 / s < 1 := by rw [div_lt_one hs]; exact hs1
  cases k with
  | zero =>
      have hσ0 : barnesAbscissa s 0 = -(1 / s) / 2 := rfl
      have hσ1 : barnesAbscissa s 1 = 1 / 2 := by simp
      rw [hσ0, hσ1]
      have hσlow : -1 < -(1 / s) / 2 := by linarith
      have hσneg : -(1 / s) / 2 < 0 := by linarith
      refine verticalIntegral'_shift_nat hs hx m 0 (by simpa using hσneg) (by norm_num)
        (by push_cast; linarith) (by norm_num) (by linarith)
        (GaloisForLFunctions.HTGeometry.sin_pi_ne_zero_of_mem_strip hσlow hσneg) ?_ ?_ ?_
      · have h := sin_pi_half_odd_ne_zero 0
        simpa using h
      · intro hcon
        have : (1 : ℝ) / 2 = 1 := by field_simp at hcon ⊢; linarith
        norm_num at this
      · intro hcon
        nlinarith [hs]
  | succ j =>
      have hσj : barnesAbscissa s (j + 1) = (j : ℝ) + 1 / 2 := rfl
      have hσj1 : barnesAbscissa s (j + 1 + 1) = ((j : ℝ) + 1) + 1 / 2 := by
        simp only [barnesAbscissa]
        push_cast
        ring
      rw [hσj, hσj1]
      have hjnn : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
      refine verticalIntegral'_shift_nat hs hx m (j + 1) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
      · push_cast; linarith
      · push_cast; linarith
      · push_cast; linarith
      · push_cast; linarith
      · linarith
      · exact sin_pi_half_odd_ne_zero j
      · have h := sin_pi_half_odd_ne_zero (j + 1)
        refine fun hcon => h ?_
        rw [show ((j : ℝ) + 1) + 1 / 2 = ((j + 1 : ℕ) : ℝ) + 1 / 2 by push_cast; ring] at hcon
        exact hcon
      · intro hcon
        nlinarith [hs, hjnn]
      · intro hcon
        nlinarith [hs, hjnn]


/-! ### The finite expansion -/

/-- The residue of the zeta pole, as it enters the expansion. -/
def barnesLeadingResidue (s x : ℝ) (m : ℕ) : ℂ :=
  (-(-(1 / ((s : ℝ) : ℂ)))) ^ m * (((x : ℝ) : ℂ) ^ (-(-(1 / ((s : ℝ) : ℂ))))
      * -((Real.pi : ℂ) / Complex.sin ((Real.pi : ℂ) * (-(1 / ((s : ℝ) : ℂ))))))
    * (-(1 / (s : ℂ)))

/-- The residue at the integer `k`, as it enters the expansion. -/
def barnesTailResidue (s x : ℝ) (m : ℕ) (k : ℕ) : ℂ :=
  (-(k : ℂ)) ^ m * (((x : ℝ) : ℂ) ^ (-(k : ℂ)) * riemannZeta (-(s : ℂ) * (k : ℂ)))
    * (-(-1) ^ k)

/-- **The finite Barnes expansion.**  Shifting the initial contour rightwards past the zeta pole and
the first `K` integers leaves the contour at the `K`-th abscissa. -/
theorem verticalIntegral'_barnes_finite_expansion {s x : ℝ} (hs1 : 1 < s) (hx : 0 < x) (m : ℕ)
    (K : ℕ) :
    VerticalIntegral' (barnesIntegrandPow s x m) (-(1 + 1 / s) / 2)
      = VerticalIntegral' (barnesIntegrandPow s x m) (barnesAbscissa s K)
        - barnesLeadingResidue s x m
        - ∑ k ∈ Finset.range K, barnesTailResidue s x m k := by
  have htel : ∑ k ∈ Finset.range K,
      (VerticalIntegral' (barnesIntegrandPow s x m) (barnesAbscissa s (k + 1))
        - VerticalIntegral' (barnesIntegrandPow s x m) (barnesAbscissa s k))
      = VerticalIntegral' (barnesIntegrandPow s x m) (barnesAbscissa s K)
        - VerticalIntegral' (barnesIntegrandPow s x m) (barnesAbscissa s 0) :=
    Finset.sum_range_sub
      (fun k => VerticalIntegral' (barnesIntegrandPow s x m) (barnesAbscissa s k)) K
  have hsteps : ∑ k ∈ Finset.range K,
      (VerticalIntegral' (barnesIntegrandPow s x m) (barnesAbscissa s (k + 1))
        - VerticalIntegral' (barnesIntegrandPow s x m) (barnesAbscissa s k))
      = ∑ k ∈ Finset.range K, barnesTailResidue s x m k := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [verticalIntegral'_shift_step hs1 hx m k, barnesTailResidue]
  have hzeta := verticalIntegral'_shift_zetaPole hs1 hx m
  rw [hsteps] at htel
  have hzero : barnesAbscissa s 0 = -(1 / s) / 2 := rfl
  rw [hzero] at htel
  rw [← barnesLeadingResidue] at hzeta
  linear_combination htel - hzeta

/-- **The Barnes expansion of the Euler sum.**  The canonical-product sum equals the shifted contour
integral minus the residues already crossed. -/
theorem hasSum_barnes_expansion {s x : ℝ} (hs1 : 1 < s) (hx : 0 < x) (K : ℕ) :
    HasSum (fun n : ℕ => ((x : ℝ) : ℂ) / (((((n : ℝ) + 1) ^ s : ℝ) : ℂ) + ((x : ℝ) : ℂ)))
      (VerticalIntegral' (barnesIntegrandPow s x 0) (barnesAbscissa s K)
        - barnesLeadingResidue s x 0
        - ∑ k ∈ Finset.range K, barnesTailResidue s x 0 k) := by
  have hs : (0 : ℝ) < s := lt_trans zero_lt_one hs1
  have hinv1 : 1 / s < 1 := by rw [div_lt_one hs]; exact hs1
  have hinv0 : (0 : ℝ) < 1 / s := by positivity
  have h1 : -1 < -(1 + 1 / s) / 2 := by linarith
  have h2 : -(1 + 1 / s) / 2 < 0 := by linarith
  have hsσ : s * (-(1 + 1 / s) / 2) < -1 := by
    have hval : s * (-(1 + 1 / s) / 2) = -(s + 1) / 2 := by field_simp
    rw [hval]
    linarith
  have hbase := hasSum_barnes_verticalIntegral' hx h1 h2 hsσ
  rw [show barnesIntegrand s x = barnesIntegrandPow s x 0 from
    funext fun w => (barnesIntegrandPow_zero s x w).symm] at hbase
  rw [verticalIntegral'_barnes_finite_expansion hs1 hx 0 K] at hbase
  exact hbase

end

end RHTower
