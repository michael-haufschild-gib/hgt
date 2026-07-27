import Mathlib

/-!
# The Gamma renormalization turns the Turán inequality into a dispersion window

Let `m : ℕ → ℝ` be a moment sequence and let

```text
γ n = (n ! / (2n)!) · m n
```

be its Gamma renormalization.  The Turán (log-concavity) inequality `γ(n+1)² ≥ γ n · γ(n+2)` is
*not* a statement about `m` being log-concave: the renormalization contributes an exact rational
factor, and the inequality is equivalent to

```text
(2n + 1) · m n · m (n+2)  ≤  (2n + 3) · m (n+1)² ,
```

a **relaxed reverse Cauchy–Schwarz** inequality.  Writing the relative dispersion

```text
D n = m n · m (n+2) / m (n+1)² − 1 ,
```

which for a moment sequence `m k = ∫ sᵏ dμ` is exactly the squared coefficient of variation of the
tilted probability measure `s ↦ sⁿ dμ / m n`, the equivalence reads

```text
Turán at n  ↔  D n ≤ 2 / (2n + 1) .
```

The two ends of that window have completely different status.  For any positive measure the Hankel
form is positive semidefinite, so `D n ≥ 0` — free, unconditional, and available from the positivity
of the measure alone.  The upper end `D n ≤ 2/(2n+1)` is a **concentration** statement about the
tilted measure, and no positivity of `μ` supplies it.  So the Gamma factor converts a question about
log-concavity of `m` into the exact question of how tightly the free log-convexity is saturated: the
dispersion must be nonnegative and smaller than `2/(2n+1)`.

Both directions are proved here, the lower one from the nonnegativity of `∫ sⁿ (s − c)² dμ` and the
upper one left as the quantity to be estimated.
-/

open scoped Nat

namespace GaloisForLFunctions

namespace TuranWindow

/-- The Gamma renormalization `γ n = (n !/(2n)!) · m n` of a moment sequence. -/
noncomputable def jensenGamma (m : ℕ → ℝ) (n : ℕ) : ℝ := (n ! : ℝ) / ((2 * n)! : ℝ) * m n

/-- The relative dispersion `m n · m (n+2)/m (n+1)² − 1`.  For `m k = ∫ sᵏ dμ` this is the squared
coefficient of variation of the tilted probability measure with density proportional to `sⁿ`. -/
noncomputable def dispersion (m : ℕ → ℝ) (n : ℕ) : ℝ := m n * m (n + 2) / m (n + 1) ^ 2 - 1

/-- The exact rational content of the Gamma renormalization: the ratio of the squared middle factor
to the product of the outer factors is `(2n+3)/(2n+1)`. -/
theorem gammaFactor_relation (n : ℕ) :
    (((n + 1)! : ℝ) / ((2 * n + 2)! : ℝ)) ^ 2 * (2 * (n : ℝ) + 1)
      = ((n ! : ℝ) / ((2 * n)! : ℝ)) * (((n + 2)! : ℝ) / ((2 * n + 4)! : ℝ))
          * (2 * (n : ℝ) + 3) := by
  have h0 : ((2 * n)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h1 : ((n)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have e1 : ((n + 1)! : ℝ) = ((n : ℝ) + 1) * (n ! : ℝ) := by
    rw [Nat.factorial_succ]; push_cast; ring
  have e2 : ((n + 2)! : ℝ) = ((n : ℝ) + 2) * ((n : ℝ) + 1) * (n ! : ℝ) := by
    rw [show n + 2 = (n + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have e3 : ((2 * n + 2)! : ℝ) = (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 1) * ((2 * n)! : ℝ) := by
    rw [show 2 * n + 2 = (2 * n + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  have e4 : ((2 * n + 4)! : ℝ)
      = (2 * (n : ℝ) + 4) * (2 * (n : ℝ) + 3) * (2 * (n : ℝ) + 2) * (2 * (n : ℝ) + 1)
          * ((2 * n)! : ℝ) := by
    rw [show 2 * n + 4 = (2 * n + 3) + 1 from rfl, Nat.factorial_succ,
      show 2 * n + 3 = (2 * n + 2) + 1 from rfl, Nat.factorial_succ,
      show 2 * n + 2 = (2 * n + 1) + 1 from rfl, Nat.factorial_succ, Nat.factorial_succ]
    push_cast; ring
  rw [e1, e2, e3, e4]
  have p1 : (2 * (n : ℝ) + 1) ≠ 0 := by positivity
  have p2 : (2 * (n : ℝ) + 2) ≠ 0 := by positivity
  have p3 : (2 * (n : ℝ) + 3) ≠ 0 := by positivity
  have p4 : (2 * (n : ℝ) + 4) ≠ 0 := by positivity
  have p5 : ((n : ℝ) + 1) ≠ 0 := by positivity
  have p6 : ((n : ℝ) + 2) ≠ 0 := by positivity
  field_simp
  ring

/-- **The Turán inequality is a relaxed reverse Cauchy–Schwarz inequality.**  For a positive
sequence, log-concavity of the Gamma renormalization is exactly the bound
`(2n+1)·m n·m (n+2) ≤ (2n+3)·m (n+1)²`. -/
theorem turan_iff_weighted (m : ℕ → ℝ) (n : ℕ) :
    jensenGamma m n * jensenGamma m (n + 2) ≤ jensenGamma m (n + 1) ^ 2
      ↔ (2 * (n : ℝ) + 1) * (m n * m (n + 2)) ≤ (2 * (n : ℝ) + 3) * m (n + 1) ^ 2 := by
  have hA : (0 : ℝ) < (n ! : ℝ) / ((2 * n)! : ℝ) := by
    apply div_pos <;> exact_mod_cast Nat.factorial_pos _
  have hB : (0 : ℝ) < ((n + 1)! : ℝ) / ((2 * n + 2)! : ℝ) := by
    apply div_pos <;> exact_mod_cast Nat.factorial_pos _
  have hC : (0 : ℝ) < ((n + 2)! : ℝ) / ((2 * n + 4)! : ℝ) := by
    apply div_pos <;> exact_mod_cast Nat.factorial_pos _
  have hidx1 : 2 * (n + 1) = 2 * n + 2 := by ring
  have hidx2 : 2 * (n + 2) = 2 * n + 4 := by ring
  have hrel := gammaFactor_relation n
  have hpos1 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  constructor
  · intro h
    simp only [jensenGamma, hidx1, hidx2] at h
    have h' : (2 * (n : ℝ) + 1) *
        (((n ! : ℝ) / ((2 * n)! : ℝ)) * (((n + 2)! : ℝ) / ((2 * n + 4)! : ℝ))
          * (m n * m (n + 2)))
        ≤ (2 * (n : ℝ) + 1) *
        ((((n + 1)! : ℝ) / ((2 * n + 2)! : ℝ)) ^ 2 * m (n + 1) ^ 2) := by
      have := mul_le_mul_of_nonneg_left h (le_of_lt hpos1)
      nlinarith [this]
    rw [show (2 * (n : ℝ) + 1) *
        ((((n + 1)! : ℝ) / ((2 * n + 2)! : ℝ)) ^ 2 * m (n + 1) ^ 2)
        = ((((n + 1)! : ℝ) / ((2 * n + 2)! : ℝ)) ^ 2 * (2 * (n : ℝ) + 1)) * m (n + 1) ^ 2 by ring,
      hrel] at h'
    have hD : (0 : ℝ) < ((n ! : ℝ) / ((2 * n)! : ℝ)) * (((n + 2)! : ℝ) / ((2 * n + 4)! : ℝ)) :=
      mul_pos hA hC
    nlinarith [h', hD]
  · intro h
    simp only [jensenGamma, hidx1, hidx2]
    have hD : (0 : ℝ) < ((n ! : ℝ) / ((2 * n)! : ℝ)) * (((n + 2)! : ℝ) / ((2 * n + 4)! : ℝ)) :=
      mul_pos hA hC
    have h' := mul_le_mul_of_nonneg_left h (le_of_lt hD)
    have hkey : ((n ! : ℝ) / ((2 * n)! : ℝ)) * (((n + 2)! : ℝ) / ((2 * n + 4)! : ℝ))
        * ((2 * (n : ℝ) + 3) * m (n + 1) ^ 2)
        = (2 * (n : ℝ) + 1) *
          ((((n + 1)! : ℝ) / ((2 * n + 2)! : ℝ)) ^ 2 * m (n + 1) ^ 2) := by
      rw [show ((n ! : ℝ) / ((2 * n)! : ℝ)) * (((n + 2)! : ℝ) / ((2 * n + 4)! : ℝ))
          * ((2 * (n : ℝ) + 3) * m (n + 1) ^ 2)
          = (((n ! : ℝ) / ((2 * n)! : ℝ)) * (((n + 2)! : ℝ) / ((2 * n + 4)! : ℝ))
              * (2 * (n : ℝ) + 3)) * m (n + 1) ^ 2 by ring, ← hrel]
      ring
    rw [hkey] at h'
    nlinarith [h', hpos1]

/-- **The dispersion window.**  Turán at `n` is exactly the bound `D n ≤ 2/(2n+1)` on the relative
dispersion.  The lower end `0 ≤ D n` is free for every positive measure; this equivalence isolates
the upper end as the whole content of the inequality. -/
theorem turan_iff_dispersion_le (m : ℕ → ℝ) (n : ℕ) (h1 : 0 < m (n + 1)) :
    jensenGamma m n * jensenGamma m (n + 2) ≤ jensenGamma m (n + 1) ^ 2
      ↔ dispersion m n ≤ 2 / (2 * (n : ℝ) + 1) := by
  rw [turan_iff_weighted m n]
  have hsq : (0 : ℝ) < m (n + 1) ^ 2 := by positivity
  have hpos1 : (0 : ℝ) < 2 * (n : ℝ) + 1 := by positivity
  have hne : (2 * (n : ℝ) + 1) ≠ 0 := ne_of_gt hpos1
  have hrw : (2 : ℝ) / (2 * (n : ℝ) + 1) + 1 = (2 * (n : ℝ) + 3) / (2 * (n : ℝ) + 1) := by
    field_simp
    ring
  unfold dispersion
  rw [sub_le_iff_le_add, hrw, div_le_div_iff₀ hsq hpos1]
  constructor <;> intro h <;> linarith

/-- **The free end of the window.**  If the Hankel quadratic form `c ↦ m n · c² − 2 m (n+1) · c
+ m (n+2)` is nonnegative — which holds for the moments of any positive measure, being
`∫ sⁿ (s − c)² dμ` — then the dispersion is nonnegative. -/
theorem dispersion_nonneg (m : ℕ → ℝ) (n : ℕ) (h0 : 0 < m n) (h1 : 0 < m (n + 1))
    (hpsd : ∀ c : ℝ, 0 ≤ m n * c ^ 2 - 2 * m (n + 1) * c + m (n + 2)) :
    0 ≤ dispersion m n := by
  have hdisc := hpsd (m (n + 1) / m n)
  have hsq : (0 : ℝ) < m (n + 1) ^ 2 := by positivity
  have hkey : m (n + 1) ^ 2 ≤ m n * m (n + 2) := by
    have hne : m n ≠ 0 := ne_of_gt h0
    field_simp at hdisc
    nlinarith [hdisc, h0]
  unfold dispersion
  rw [le_sub_iff_add_le, zero_add, le_div_iff₀ hsq, one_mul]
  exact hkey

/-- **The window, both ends.**  Under the free Hankel positivity, Turán at `n` is exactly the
statement that the dispersion lies in `[0, 2/(2n+1)]`. -/
theorem turan_iff_dispersion_mem_window (m : ℕ → ℝ) (n : ℕ) (h0 : 0 < m n) (h1 : 0 < m (n + 1))
    (hpsd : ∀ c : ℝ, 0 ≤ m n * c ^ 2 - 2 * m (n + 1) * c + m (n + 2)) :
    jensenGamma m n * jensenGamma m (n + 2) ≤ jensenGamma m (n + 1) ^ 2
      ↔ dispersion m n ∈ Set.Icc 0 (2 / (2 * (n : ℝ) + 1)) := by
  rw [turan_iff_dispersion_le m n h1, Set.mem_Icc]
  exact ⟨fun h => ⟨dispersion_nonneg m n h0 h1 hpsd, h⟩, fun h => h.2⟩

/-- Hankel positivity for the moments of a positive measure: `∫ sⁿ (s − c)² dμ ≥ 0` expands to the
quadratic form used above. -/
theorem hankel_nonneg_of_measure {μ : MeasureTheory.Measure ℝ} (n : ℕ)
    (hi0 : MeasureTheory.Integrable (fun s : ℝ => s ^ n) μ)
    (hi1 : MeasureTheory.Integrable (fun s : ℝ => s ^ (n + 1)) μ)
    (hi2 : MeasureTheory.Integrable (fun s : ℝ => s ^ (n + 2)) μ)
    (hsupp : ∀ᵐ s ∂μ, 0 ≤ s ^ n) (c : ℝ) :
    0 ≤ (∫ s, s ^ n ∂μ) * c ^ 2 - 2 * (∫ s, s ^ (n + 1) ∂μ) * c + (∫ s, s ^ (n + 2) ∂μ) := by
  have hexp : ∀ s : ℝ, s ^ n * (s - c) ^ 2
      = s ^ (n + 2) - 2 * c * s ^ (n + 1) + c ^ 2 * s ^ n := by
    intro s; ring
  have hB' : MeasureTheory.Integrable (fun s : ℝ => 2 * c * s ^ (n + 1)) μ := hi1.const_mul _
  have hC' : MeasureTheory.Integrable (fun s : ℝ => c ^ 2 * s ^ n) μ := hi0.const_mul _
  have hA' : MeasureTheory.Integrable (fun s : ℝ => s ^ (n + 2) - 2 * c * s ^ (n + 1)) μ :=
    hi2.sub hB'
  have hnn : 0 ≤ ∫ s, s ^ n * (s - c) ^ 2 ∂μ := by
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [hsupp] with s hs
    exact mul_nonneg hs (sq_nonneg _)
  have hval : (∫ s, s ^ n * (s - c) ^ 2 ∂μ)
      = (∫ s, s ^ (n + 2) ∂μ) - 2 * c * (∫ s, s ^ (n + 1) ∂μ) + c ^ 2 * (∫ s, s ^ n ∂μ) := by
    rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hexp),
      MeasureTheory.integral_add hA' hC', MeasureTheory.integral_sub hi2 hB',
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [hval] at hnn
  linarith


/-- **The Gamma renormalization is an inverse Pochhammer weight.**  Shifting the index by `j`
multiplies the renormalization factor by `∏_{i<j} (4n + 4i + 2)⁻¹`, an identity of naturals. -/
theorem factorial_pochhammer_law (n j : ℕ) :
    (n + j)! * (2 * n)! * ∏ i ∈ Finset.range j, (4 * n + 4 * i + 2) = n ! * (2 * n + 2 * j)! := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Finset.prod_range_succ, show n + (j + 1) = (n + j) + 1 from rfl, Nat.factorial_succ,
      show 2 * n + 2 * (j + 1) = (2 * n + 2 * j + 1) + 1 by ring, Nat.factorial_succ,
      Nat.factorial_succ]
    have hsplit : (n + j + 1) * (n + j)! * (2 * n)!
        * ((∏ i ∈ Finset.range j, (4 * n + 4 * i + 2)) * (4 * n + 4 * j + 2))
        = ((n + j + 1) * (4 * n + 4 * j + 2))
          * ((n + j)! * (2 * n)! * ∏ i ∈ Finset.range j, (4 * n + 4 * i + 2)) := by ring
    rw [hsplit, ih]
    ring

/-- The real form of the Pochhammer law: clearing the weight `∏_{i<j}(4n+4i+2)` from the `j`-shifted
Gamma renormalization returns the unshifted factor times the raw moment. -/
theorem jensenGamma_mul_pochhammer (m : ℕ → ℝ) (n j : ℕ) :
    jensenGamma m (n + j) * ∏ i ∈ Finset.range j, (4 * (n : ℝ) + 4 * (i : ℝ) + 2)
      = ((n ! : ℝ) / ((2 * n)! : ℝ)) * m (n + j) := by
  have hnat := factorial_pochhammer_law n j
  have hcast : (((n + j)! : ℝ)) * ((2 * n)! : ℝ)
      * ∏ i ∈ Finset.range j, (4 * (n : ℝ) + 4 * (i : ℝ) + 2)
      = (n ! : ℝ) * ((2 * n + 2 * j)! : ℝ) := by
    have := congrArg (fun k : ℕ => (k : ℝ)) hnat
    push_cast at this
    simpa using this
  have h1 : ((2 * (n + j))! : ℝ) = ((2 * n + 2 * j)! : ℝ) := by
    rw [show 2 * (n + j) = 2 * n + 2 * j by ring]
  have h2 : ((2 * n + 2 * j)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h3 : ((2 * n)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  unfold jensenGamma
  rw [h1]
  have hkey : ((n + j)! : ℝ) / ((2 * n + 2 * j)! : ℝ)
      * ∏ i ∈ Finset.range j, (4 * (n : ℝ) + 4 * (i : ℝ) + 2) = (n ! : ℝ) / ((2 * n)! : ℝ) := by
    rw [div_mul_eq_mul_div, div_eq_div_iff h2 h3]
    linear_combination hcast
  calc ((n + j)! : ℝ) / ((2 * n + 2 * j)! : ℝ) * m (n + j)
        * ∏ i ∈ Finset.range j, (4 * (n : ℝ) + 4 * (i : ℝ) + 2)
      = (((n + j)! : ℝ) / ((2 * n + 2 * j)! : ℝ)
          * ∏ i ∈ Finset.range j, (4 * (n : ℝ) + 4 * (i : ℝ) + 2)) * m (n + j) := by ring
    _ = ((n ! : ℝ) / ((2 * n)! : ℝ)) * m (n + j) := by rw [hkey]


/-- The Pochhammer weight `∏_{i<j} (4n + 4i + 2) = 4^j (n+½)_j` produced by the Gamma
renormalization. -/
noncomputable def pochWeight (n j : ℕ) : ℝ := ∏ i ∈ Finset.range j, (4 * (n : ℝ) + 4 * (i : ℝ) + 2)

theorem pochWeight_pos (n j : ℕ) : 0 < pochWeight n j := by
  unfold pochWeight
  refine Finset.prod_pos fun i _ => by positivity

/-- The Jensen polynomial of the Gamma-renormalized sequence, evaluated. -/
noncomputable def jensenPolyEval (m : ℕ → ℝ) (d n : ℕ) (Y : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (d + 1), (d.choose j : ℝ) * jensenGamma m (n + j) * Y ^ j

/-- The universal model polynomial `∑_j C(d,j) z^j / ∏_{i<j}(4n+4i+2)`.  Up to normalization this is
`₁F₁(−d; n+½; −z/4)`, hence a generalized Laguerre polynomial of parameter `n − ½`. -/
noncomputable def modelPoly (d n : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (d + 1), (d.choose j : ℝ) * z ^ j / pochWeight n j

/-- **Clearing the Gamma factor.**  Multiplying the Jensen polynomial by `(2n)!/n!` replaces each
renormalized coefficient by the raw moment divided by the Pochhammer weight. -/
theorem jensenPolyEval_mul_factor (m : ℕ → ℝ) (d n : ℕ) (Y : ℝ) :
    jensenPolyEval m d n Y * (((2 * n)! : ℝ) / (n ! : ℝ))
      = ∑ j ∈ Finset.range (d + 1), (d.choose j : ℝ) * m (n + j) * Y ^ j / pochWeight n j := by
  unfold jensenPolyEval
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hg : jensenGamma m (n + j) * pochWeight n j
      = ((n ! : ℝ) / ((2 * n)! : ℝ)) * m (n + j) := jensenGamma_mul_pochhammer m n j
  have hwpos := pochWeight_pos n j
  have h3 : ((2 * n)! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h4 : (n ! : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hgam : jensenGamma m (n + j)
      = ((n ! : ℝ) / ((2 * n)! : ℝ)) * m (n + j) / pochWeight n j :=
    (eq_div_iff hwpos.ne').mpr hg
  rw [hgam]
  field_simp

/-- **Superposition law.**  For a finitely supported positive measure `∑ w i · δ (s i)`, the Jensen
polynomial of the Gamma-renormalized moments is the `w`-average of one universal polynomial with the
argument scaled by `s i`.  Every summand is a generalized Laguerre polynomial in `Y`, so the Jensen
polynomial is a positive superposition of hyperbolic polynomials whose root sets are the fixed
Laguerre roots rescaled by `s i`. -/
theorem jensenPolyEval_superposition {ι : Type*} (F : Finset ι) (w s : ι → ℝ) (m : ℕ → ℝ) (d n : ℕ)
    (Y : ℝ) (hm : ∀ k : ℕ, m k = ∑ i ∈ F, w i * s i ^ k) :
    jensenPolyEval m d n Y * (((2 * n)! : ℝ) / (n ! : ℝ))
      = ∑ i ∈ F, w i * s i ^ n * modelPoly d n (s i * Y) := by
  rw [jensenPolyEval_mul_factor]
  have hexp : ∀ i : ι, w i * s i ^ n * modelPoly d n (s i * Y)
      = ∑ j ∈ Finset.range (d + 1),
          (d.choose j : ℝ) * (w i * s i ^ (n + j)) * Y ^ j / pochWeight n j := by
    intro i
    unfold modelPoly
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hwpos := (pochWeight_pos n j).ne'
    field_simp
    ring
  rw [Finset.sum_congr rfl fun i _ => hexp i, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hm (n + j), Finset.mul_sum, Finset.sum_mul, Finset.sum_div]


/-- The perturbation part of a Jensen polynomial relative to the model: the model polynomial with the
normalized moment ratios `ε j` inserted coefficientwise. -/
noncomputable def perturbationPoly (ε : ℕ → ℝ) (d n : ℕ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (d + 1), (d.choose j : ℝ) * ε j * z ^ j / pochWeight n j

/-- **Exact perturbation form.**  Writing the moments as `m (n+j) = m n · t^j · (1 + ε j)` — with
`t = m (n+1)/m n`, so that `ε 0 = ε 1 = 0` and `ε j` are the normalized moment ratios of the tilted
measure — the Jensen polynomial is the model polynomial at rescaled argument plus the `ε`-perturbation
in the same basis.  Hyperbolicity of `J^(d,n)` is therefore a condition on the finitely many numbers
`ε 2, …, ε d` alone, at the single parameter `n`. -/
theorem jensenPolyEval_eq_model_add_perturbation (m : ℕ → ℝ) (ε : ℕ → ℝ) (t : ℝ) (d n : ℕ) (Y : ℝ)
    (hm : ∀ j ∈ Finset.range (d + 1), m (n + j) = m n * t ^ j * (1 + ε j)) :
    jensenPolyEval m d n Y * (((2 * n)! : ℝ) / (n ! : ℝ))
      = m n * (modelPoly d n (t * Y) + perturbationPoly ε d n (t * Y)) := by
  rw [jensenPolyEval_mul_factor]
  unfold modelPoly perturbationPoly
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hw := (pochWeight_pos n j).ne'
  rw [hm j hj, mul_pow]
  field_simp

end TuranWindow

end GaloisForLFunctions
