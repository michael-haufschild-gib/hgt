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
    (α β w : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 0 < w)
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
    (Gn := finiteTransverseInfiniteSlice α β b) (by positivity) hw (Complex.exp_ne_zero _) ?_ htrace
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
    (α β w : ℝ) (hα : 0 < α) (hβ : 0 < β) (hw : 0 < w)
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
    α β w hα hβ hw hirr hG hEven b S hb htrace s t)

end RHTower
