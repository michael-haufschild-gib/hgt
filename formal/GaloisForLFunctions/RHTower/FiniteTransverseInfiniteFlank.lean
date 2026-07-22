import GaloisForLFunctions.RHTower.FiniteTransverseExpEigenslice

/-!
# Finite-transverse rigidity for infinite flank slices

An absolutely convergent two-generator lower-flank series may have infinitely many frequencies in
each first-generator slice while occupying only finitely many second-generator slices.  Each
infinite slice is still an exact eigenfunction of the first-generator period.  Its weighted
absolute convergence supplies the common lower-flank bound, so the finite-transverse reflection
capstone forces the entire even carrier to be constant.
-/

open Complex Filter Topology

noncomputable section

namespace RHTower

/-- A single infinitely supported transverse slice of the lower-flank exponential series. -/
def finiteTransverseInfiniteSlice (α β : ℝ) (b : ℕ → ℕ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑' m : ℕ, b m n * Complex.exp
    (-Complex.I * z * (((m : ℝ) * α + (n : ℝ) * β : ℝ) : ℂ))

/-- A lower-flank frequency is multiplied by the expected transverse phase after one exact
first-generator period. -/
theorem expFlankNatFreq_shiftEig (α β : ℝ) (hα : α ≠ 0) (m n : ℕ) (z : ℂ) :
    Complex.exp (-Complex.I * (z + (2 * Real.pi / α : ℝ)) *
        (((m : ℝ) * α + (n : ℝ) * β : ℝ) : ℂ)) =
      (Complex.exp (-2 * Real.pi * Complex.I * (β / α : ℝ))) ^ n *
        Complex.exp (-Complex.I * z * (((m : ℝ) * α + (n : ℝ) * β : ℝ) : ℂ)) := by
  have hαc : (α : ℂ) ≠ 0 := by exact_mod_cast hα
  rw [show -Complex.I * (z + (2 * Real.pi / α : ℝ)) *
        (((m : ℝ) * α + (n : ℝ) * β : ℝ) : ℂ) =
      -Complex.I * z * (((m : ℝ) * α + (n : ℝ) * β : ℝ) : ℂ) +
        ((-(m : ℤ) : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) +
        (n : ℂ) * (-2 * (Real.pi : ℂ) * Complex.I * (β / α : ℝ)) by
      push_cast
      field_simp
      ring]
  rw [Complex.exp_add, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one,
    ← Complex.exp_nat_mul]
  ring

/-- Every infinitely supported transverse slice is an exact shift eigenfunction. -/
theorem finiteTransverseInfiniteSlice_shiftEig
    (α β : ℝ) (hα : α ≠ 0) (b : ℕ → ℕ → ℂ) (n : ℕ) (z : ℂ) :
    finiteTransverseInfiniteSlice α β b n (z + (2 * Real.pi / α : ℝ)) =
      (Complex.exp (-2 * Real.pi * Complex.I * (β / α : ℝ))) ^ n *
        finiteTransverseInfiniteSlice α β b n z := by
  rw [finiteTransverseInfiniteSlice, finiteTransverseInfiniteSlice]
  calc
    (∑' m : ℕ, b m n * Complex.exp
        (-Complex.I * (z + (2 * Real.pi / α : ℝ)) *
          (((m : ℝ) * α + (n : ℝ) * β : ℝ) : ℂ))) =
        ∑' m : ℕ, (Complex.exp (-2 * Real.pi * Complex.I * (β / α : ℝ))) ^ n *
          (b m n * Complex.exp
            (-Complex.I * z * (((m : ℝ) * α + (n : ℝ) * β : ℝ) : ℂ))) := by
      apply tsum_congr
      intro m
      rw [expFlankNatFreq_shiftEig α β hα m n z]
      ring
    _ = _ := tsum_mul_left

/-- **Finite-transverse leaf-reflection rigidity for the full infinite slices.**

Let an even entire carrier agree on `Im z ≤ -w` with an absolutely convergent two-generator
exponential series occupying a finite set `S` of transverse slices.  The series may have infinitely
many first-generator frequencies in every occupied slice.  If `β / α` is irrational, the carrier is
constant. -/
theorem finiteTransverse_infiniteSeries_reflection_rigidity
    (α β w : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hirr : Irrational (β / α))
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (hEven : ∀ z, G (-z) = G z)
    (b : ℕ → ℕ → ℂ) (S : Finset ℕ)
    (hb : ∀ n ∈ S, Summable (fun m : ℕ =>
      ‖b m n‖ * Real.exp (-(((m : ℝ) * α + (n : ℝ) * β) * w))))
    (htrace : ∀ z : ℂ, z.im ≤ -w →
      G z = ∑ n ∈ S, finiteTransverseInfiniteSlice α β b n z) :
    ∀ s t : ℂ, G s = G t := by
  let ω : ℂ := Complex.exp (-2 * Real.pi * Complex.I * (β / α : ℝ))
  let B : ℝ := ∑ n ∈ S, ∑' m : ℕ,
    ‖b m n‖ * Real.exp (-(((m : ℝ) * α + (n : ℝ) * β) * w))
  have hre : ∀ (z : ℂ) (m n : ℕ),
      (-Complex.I * z * (((m : ℝ) * α + (n : ℝ) * β : ℝ) : ℂ)).re =
        ((m : ℝ) * α + (n : ℝ) * β) * z.im := by
    intro z m n
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hterm : ∀ z : ℂ, z.im ≤ -w → ∀ n ∈ S, ∀ m : ℕ,
      ‖b m n * Complex.exp
          (-Complex.I * z * (((m : ℝ) * α + (n : ℝ) * β : ℝ) : ℂ))‖ ≤
        ‖b m n‖ * Real.exp (-(((m : ℝ) * α + (n : ℝ) * β) * w)) := by
    intro z hz n hn m
    have hfreq : 0 ≤ (m : ℝ) * α + (n : ℝ) * β := by positivity
    rw [norm_mul, Complex.norm_exp, hre z m n]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [hfreq, hz])) (norm_nonneg _)
  have hbound : ∀ z : ℂ, z.im ≤ -w → ‖G z‖ ≤ B := by
    intro z hz
    rw [htrace z hz]
    calc
      ‖∑ n ∈ S, finiteTransverseInfiniteSlice α β b n z‖ ≤
          ∑ n ∈ S, ‖finiteTransverseInfiniteSlice α β b n z‖ := norm_sum_le _ _
      _ ≤ ∑ n ∈ S, ∑' m : ℕ,
          ‖b m n‖ * Real.exp (-(((m : ℝ) * α + (n : ℝ) * β) * w)) := by
        refine Finset.sum_le_sum (fun n hn => ?_)
        have hnorm : Summable (fun m : ℕ =>
            ‖b m n * Complex.exp
              (-Complex.I * z * (((m : ℝ) * α + (n : ℝ) * β : ℝ) : ℂ))‖) :=
          Summable.of_nonneg_of_le (fun m => norm_nonneg _) (hterm z hz n hn) (hb n hn)
        calc
          ‖finiteTransverseInfiniteSlice α β b n z‖ ≤ ∑' m : ℕ,
              ‖b m n * Complex.exp
                (-Complex.I * z * (((m : ℝ) * α + (n : ℝ) * β : ℝ) : ℂ))‖ := by
            exact norm_tsum_le_tsum_norm hnorm
          _ ≤ ∑' m : ℕ,
              ‖b m n‖ * Real.exp (-(((m : ℝ) * α + (n : ℝ) * β) * w)) :=
            Summable.tsum_le_tsum (hterm z hz n hn) hnorm (hb n hn)
      _ = B := rfl
  refine finiteTransverse_reflection_rigidity hG hEven
    (T := 2 * Real.pi / α) (w := w) (ω := ω) (S := S)
    (Gn := finiteTransverseInfiniteSlice α β b) (by positivity) (Complex.exp_ne_zero _) ?_ htrace
    ?_ hbound
  · intro k hk
    have hneg : Irrational (-(β / α)) := hirr.neg
    simpa only [ω, show -2 * Real.pi * Complex.I * (β / α : ℝ) =
        2 * Real.pi * Complex.I * (-(β / α) : ℝ) by push_cast; ring] using
      expOmega_pow_ne_one hneg k hk
  · intro n hn z hz
    exact finiteTransverseInfiniteSlice_shiftEig α β hα.ne' b n z

/-- **Infinite-transverse-support corollary.**  A nonconstant even entire carrier with irrational
generator ratio admits no absolutely convergent lower-flank representation supported on finitely
many transverse slices.  Swapping `α`, `β` and transposing the coefficients gives the identical
conclusion for the other slice direction. -/
theorem finiteTransverse_nonconstant_forces_no_finiteSliceRepresentation
    (α β w : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hirr : Irrational (β / α))
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (hEven : ∀ z, G (-z) = G z)
    (hNonconstant : ∃ s t : ℂ, G s ≠ G t) (b : ℕ → ℕ → ℂ) :
    ¬ ∃ S : Finset ℕ,
      (∀ n ∈ S, Summable (fun m : ℕ =>
        ‖b m n‖ * Real.exp (-(((m : ℝ) * α + (n : ℝ) * β) * w)))) ∧
      (∀ z : ℂ, z.im ≤ -w →
        G z = ∑ n ∈ S, finiteTransverseInfiniteSlice α β b n z) := by
  rintro ⟨S, hb, htrace⟩
  obtain ⟨s, t, hst⟩ := hNonconstant
  exact hst (finiteTransverse_infiniteSeries_reflection_rigidity
    α β w hα hβ hirr hG hEven b S hb htrace s t)

/-! ## The literal double-series statement -/

/-- The full two-generator lower-flank series, indexed without a prior slicing choice. -/
def finiteTransverseFlankSeries (α β : ℝ) (b : ℕ → ℕ → ℂ) (z : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, b p.1 p.2 * Complex.exp
    (-Complex.I * z * (((p.1 : ℝ) * α + (p.2 : ℝ) * β : ℝ) : ℂ))

/-- The set of occupied second-generator slices. -/
def finiteTransverseSecondSupport (b : ℕ → ℕ → ℂ) : Set ℕ :=
  {n | ∃ m, b m n ≠ 0}

/-- The set of occupied first-generator slices. -/
def finiteTransverseFirstSupport (b : ℕ → ℕ → ℂ) : Set ℕ :=
  {m | ∃ n, b m n ≠ 0}

/-- Transposing the coefficient array and the two generators leaves the full flank series
unchanged. -/
theorem finiteTransverseFlankSeries_transpose
    (α β : ℝ) (b : ℕ → ℕ → ℂ) (z : ℂ) :
    finiteTransverseFlankSeries β α (fun n m => b m n) z =
      finiteTransverseFlankSeries α β b z := by
  rw [finiteTransverseFlankSeries, finiteTransverseFlankSeries]
  let term : ℕ × ℕ → ℂ := fun p => b p.1 p.2 * Complex.exp
    (-Complex.I * z * (((p.1 : ℝ) * α + (p.2 : ℝ) * β : ℝ) : ℂ))
  calc
    (∑' p : ℕ × ℕ, b p.2 p.1 * Complex.exp
        (-Complex.I * z * (((p.1 : ℝ) * β + (p.2 : ℝ) * α : ℝ) : ℂ))) =
        ∑' p : ℕ × ℕ, term (p.2, p.1) := by
      apply tsum_congr
      intro p
      simp only [term]
      congr 2
      push_cast
      ring
    _ = ∑' p : ℕ × ℕ, term p := (Equiv.prodComm ℕ ℕ).tsum_eq term

/-- Absolute convergence of the full weighted double series permits exact regrouping over a finite
set containing the occupied second-generator slices. -/
theorem finiteTransverseFlankSeries_eq_sum_slices
    (α β w : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (b : ℕ → ℕ → ℂ) (S : Finset ℕ)
    (hS : ∀ n, n ∉ S → ∀ m, b m n = 0)
    (habs : Summable (fun p : ℕ × ℕ =>
      ‖b p.1 p.2‖ * Real.exp
        (-(((p.1 : ℝ) * α + (p.2 : ℝ) * β) * w))))
    {z : ℂ} (hz : z.im ≤ -w) :
    finiteTransverseFlankSeries α β b z =
      ∑ n ∈ S, finiteTransverseInfiniteSlice α β b n z := by
  let term : ℕ × ℕ → ℂ := fun p => b p.1 p.2 * Complex.exp
    (-Complex.I * z * (((p.1 : ℝ) * α + (p.2 : ℝ) * β : ℝ) : ℂ))
  have hre : ∀ p : ℕ × ℕ,
      (-Complex.I * z * (((p.1 : ℝ) * α + (p.2 : ℝ) * β : ℝ) : ℂ)).re =
        ((p.1 : ℝ) * α + (p.2 : ℝ) * β) * z.im := by
    intro p
    simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hterm : ∀ p : ℕ × ℕ,
      ‖term p‖ ≤ ‖b p.1 p.2‖ * Real.exp
        (-(((p.1 : ℝ) * α + (p.2 : ℝ) * β) * w)) := by
    intro p
    have hfreq : 0 ≤ (p.1 : ℝ) * α + (p.2 : ℝ) * β := by positivity
    change ‖b p.1 p.2 * Complex.exp
        (-Complex.I * z * (((p.1 : ℝ) * α + (p.2 : ℝ) * β : ℝ) : ℂ))‖ ≤ _
    rw [norm_mul, Complex.norm_exp, hre p]
    exact mul_le_mul_of_nonneg_left
      (Real.exp_le_exp.mpr (by nlinarith [hfreq, hz])) (norm_nonneg _)
  have hnorm : Summable (fun p : ℕ × ℕ => ‖term p‖) :=
    Summable.of_nonneg_of_le (fun p => norm_nonneg _) hterm habs
  have hsum : Summable term := summable_norm_iff.mp hnorm
  have hslice : ∀ n : ℕ,
      (∑' m : ℕ, term (m, n)) = finiteTransverseInfiniteSlice α β b n z := by
    intro n
    rfl
  rw [finiteTransverseFlankSeries]
  change (∑' p : ℕ × ℕ, term p) = _
  calc
    (∑' p : ℕ × ℕ, term p) = ∑' m : ℕ, ∑' n : ℕ, term (m, n) :=
      hsum.tsum_prod
    _ = ∑' n : ℕ, ∑' m : ℕ, term (m, n) := hsum.tsum_comm.symm
    _ = ∑' n : ℕ, finiteTransverseInfiniteSlice α β b n z :=
      tsum_congr hslice
    _ = ∑ n ∈ S, finiteTransverseInfiniteSlice α β b n z := by
      exact tsum_eq_sum (fun n hn => by
        have hb0 : ∀ m, b m n = 0 := hS n hn
        simp only [finiteTransverseInfiniteSlice, hb0, zero_mul, tsum_zero])

/-- **Literal finite-transverse leaf-reflection theorem.**  This is the paper statement with one
absolutely convergent double series and a finite occupied transverse support, rather than a sliced
representation supplied as a hypothesis. -/
theorem finiteTransverse_flankSeries_reflection_rigidity
    (α β w : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hirr : Irrational (β / α))
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (hEven : ∀ z, G (-z) = G z)
    (b : ℕ → ℕ → ℂ)
    (habs : Summable (fun p : ℕ × ℕ =>
      ‖b p.1 p.2‖ * Real.exp
        (-(((p.1 : ℝ) * α + (p.2 : ℝ) * β) * w))))
    (hfinite : (finiteTransverseSecondSupport b).Finite)
    (htrace : ∀ z : ℂ, z.im ≤ -w → G z = finiteTransverseFlankSeries α β b z) :
    ∀ s t : ℂ, G s = G t := by
  let S : Finset ℕ := hfinite.toFinset
  have hS : ∀ n, n ∉ S → ∀ m, b m n = 0 := by
    intro n hn m
    by_contra hmn
    apply hn
    simpa only [S, Set.Finite.mem_toFinset] using
      (show n ∈ finiteTransverseSecondSupport b from ⟨m, hmn⟩)
  have hb : ∀ n ∈ S, Summable (fun m : ℕ =>
      ‖b m n‖ * Real.exp (-(((m : ℝ) * α + (n : ℝ) * β) * w))) := by
    intro n hn
    simpa using habs.comp_injective (show Function.Injective (fun m : ℕ => (m, n)) from by
      intro m k hmk
      exact congrArg Prod.fst hmk)
  apply finiteTransverse_infiniteSeries_reflection_rigidity
    α β w hα hβ hirr hG hEven b S hb
  intro z hz
  rw [htrace z hz]
  exact finiteTransverseFlankSeries_eq_sum_slices α β w hα hβ b S hS habs hz

/-- **Symmetric literal theorem.**  Finite support in the first-generator direction also forces the
even entire carrier to be constant. -/
theorem finiteTransverse_flankSeries_reflection_rigidity_of_finiteFirstSupport
    (α β w : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hirr : Irrational (β / α))
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (hEven : ∀ z, G (-z) = G z)
    (b : ℕ → ℕ → ℂ)
    (habs : Summable (fun p : ℕ × ℕ =>
      ‖b p.1 p.2‖ * Real.exp
        (-(((p.1 : ℝ) * α + (p.2 : ℝ) * β) * w))))
    (hfinite : (finiteTransverseFirstSupport b).Finite)
    (htrace : ∀ z : ℂ, z.im ≤ -w → G z = finiteTransverseFlankSeries α β b z) :
    ∀ s t : ℂ, G s = G t := by
  have hratio : α / β = (β / α)⁻¹ := by
    field_simp [hα.ne', hβ.ne']
  have hirr' : Irrational (α / β) := by
    rw [hratio]
    exact hirr.inv
  have habs' : Summable (fun p : ℕ × ℕ =>
      ‖b p.2 p.1‖ * Real.exp
        (-(((p.1 : ℝ) * β + (p.2 : ℝ) * α) * w))) := by
    simpa [Function.comp_def, Equiv.prodComm, Prod.swap, add_comm] using
      ((Equiv.prodComm ℕ ℕ).summable_iff.mpr habs)
  have hfinite' : (finiteTransverseSecondSupport (fun n m => b m n)).Finite := by
    simpa only [finiteTransverseSecondSupport, finiteTransverseFirstSupport]
      using hfinite
  apply finiteTransverse_flankSeries_reflection_rigidity
    β α w hβ hα hirr' hG hEven (fun n m => b m n) habs' hfinite'
  intro z hz
  rw [finiteTransverseFlankSeries_transpose]
  exact htrace z hz

/-- **Two-sided infinite-support corollary.**  Any nonconstant carrier satisfying the concrete
two-generator lower-flank representation has infinitely many occupied slices in both generator
directions. -/
theorem finiteTransverse_nonconstant_forces_both_sliceSupports_infinite
    (α β w : ℝ) (hα : 0 < α) (hβ : 0 < β)
    (hirr : Irrational (β / α))
    {G : ℂ → ℂ} (hG : Differentiable ℂ G) (hEven : ∀ z, G (-z) = G z)
    (hNonconstant : ∃ s t : ℂ, G s ≠ G t) (b : ℕ → ℕ → ℂ)
    (habs : Summable (fun p : ℕ × ℕ =>
      ‖b p.1 p.2‖ * Real.exp
        (-(((p.1 : ℝ) * α + (p.2 : ℝ) * β) * w))))
    (htrace : ∀ z : ℂ, z.im ≤ -w → G z = finiteTransverseFlankSeries α β b z) :
    ¬ (finiteTransverseFirstSupport b).Finite ∧
      ¬ (finiteTransverseSecondSupport b).Finite := by
  constructor
  · intro hfinite
    obtain ⟨s, t, hst⟩ := hNonconstant
    exact hst (finiteTransverse_flankSeries_reflection_rigidity_of_finiteFirstSupport
      α β w hα hβ hirr hG hEven b habs hfinite htrace s t)
  · intro hfinite
    obtain ⟨s, t, hst⟩ := hNonconstant
    exact hst (finiteTransverse_flankSeries_reflection_rigidity
      α β w hα hβ hirr hG hEven b habs hfinite htrace s t)

end RHTower
