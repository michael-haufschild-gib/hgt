import GaloisForLFunctions.HTGeometry.ZeroListBridge

/-!
# The base case: only real exponents

When every exponent is real the exponential polynomial is a real exponential sum, and Laguerre's rule
applies directly.  Two small facts make the passage automatic:

* for a real exponent `y`, `Re (C y · e^{y t}) = (Re C y) · e^{y t}`, so no linear independence is
  needed to read off the real form;
* the coefficients are real anyway — the imaginary parts form a vanishing real exponential
  combination, so `exp_coeff_eq_zero` kills them.

The support is then indexed in increasing order and Laguerre's bound reads `|Z| + 1 ≤ |S|`.
-/

open Set Filter Real

namespace GaloisForLFunctions.HTGeometry

variable {S : Finset ℂ} {C : ℂ → ℂ}

/-- With real exponents the real part is read off termwise. -/
theorem re_expCombo_of_real_exponents (hSreal : ∀ y ∈ S, y.im = 0) (t : ℝ) :
    (∑ y ∈ S, C y * Complex.exp (y * t)).re
      = ∑ y ∈ S, (C y).re * Real.exp (y.re * t) := by
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl (fun y hy => ?_)
  have harg : y * (t : ℂ) = ((y.re * t : ℝ) : ℂ) := by
    refine Complex.ext ?_ ?_
    · simp [Complex.mul_re]
    · simp [Complex.mul_im, hSreal y hy]
  have hexp : Complex.exp (y * t) = ((Real.exp (y.re * t) : ℝ) : ℂ) := by
    rw [harg, Complex.ofReal_exp]
  rw [hexp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
  ring

/-- The coefficients of a real-valued exponential polynomial with real exponents are real. -/
theorem coeff_re_of_real_exponents (hSreal : ∀ y ∈ S, y.im = 0)
    (hreal : ∀ t : ℝ, (∑ y ∈ S, C y * Complex.exp (y * t)).im = 0) :
    ∀ y ∈ S, (C y).im = 0 := by
  have hzero : ∀ t : ℝ, ∑ y ∈ S, ((C y).im : ℂ) * Complex.exp (y * t) = 0 := by
    intro t
    have hsum : (∑ y ∈ S, ((C y).im : ℂ) * Complex.exp (y * t))
        = (((∑ y ∈ S, (C y).im * Real.exp (y.re * t) : ℝ)) : ℂ) := by
      rw [Complex.ofReal_sum]
      refine Finset.sum_congr rfl (fun y hy => ?_)
      have harg : y * (t : ℂ) = ((y.re * t : ℝ) : ℂ) := by
        refine Complex.ext ?_ ?_
        · simp [Complex.mul_re]
        · simp [Complex.mul_im, hSreal y hy]
      have hexp : Complex.exp (y * t) = ((Real.exp (y.re * t) : ℝ) : ℂ) := by
        rw [harg, Complex.ofReal_exp]
      rw [hexp, ← Complex.ofReal_mul]
    have him : (∑ y ∈ S, (C y).im * Real.exp (y.re * t)) = 0 := by
      have h1 := hreal t
      rw [Complex.im_sum] at h1
      rw [← h1]
      refine Finset.sum_congr rfl (fun y hy => ?_)
      have harg : y * (t : ℂ) = ((y.re * t : ℝ) : ℂ) := by
        refine Complex.ext ?_ ?_
        · simp [Complex.mul_re]
        · simp [Complex.mul_im, hSreal y hy]
      have hexp : Complex.exp (y * t) = ((Real.exp (y.re * t) : ℝ) : ℂ) := by
        rw [harg, Complex.ofReal_exp]
      rw [hexp, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hsum, him]
    simp
  intro y hy
  have := exp_coeff_eq_zero (S := S) (C := fun y => ((C y).im : ℂ)) hzero y hy
  exact_mod_cast this

/-- **The base case.**  A real-valued exponential polynomial all of whose exponents are real, with
nonzero coefficients, has at most `|S| - 1` zeros. -/
theorem card_zeros_le_realExponents (hSreal : ∀ y ∈ S, y.im = 0) (hCne : ∀ y ∈ S, C y ≠ 0)
    (hSne : S.Nonempty)
    (hreal : ∀ t : ℝ, (∑ y ∈ S, C y * Complex.exp (y * t)).im = 0)
    (Z : Finset ℝ) (hZ : ∀ x ∈ Z, (∑ y ∈ S, C y * Complex.exp (y * x)).re = 0) :
    Z.card + 1 ≤ S.card := by
  classical
  have hCim := coeff_re_of_real_exponents hSreal hreal
  have hcast : ∀ y ∈ S, ((y.re : ℝ) : ℂ) = y := by
    intro y hy
    refine Complex.ext rfl ?_
    rw [Complex.ofReal_im]
    exact (hSreal y hy).symm
  set T : Finset ℝ := S.image Complex.re with hT
  have hinj : Set.InjOn Complex.re S := by
    intro y₁ h₁ y₂ h₂ hre
    rw [← hcast y₁ h₁, ← hcast y₂ h₂, hre]
  have hTcard : T.card = S.card := by
    rw [hT]
    exact Finset.card_image_of_injOn hinj
  set m : ℕ := S.card with hm
  have hmpos : 0 < m := Finset.card_pos.mpr hSne
  set e : Fin m ↪o ℝ := T.orderEmbOfFin hTcard with he
  have hemem : ∀ i, ((e i : ℝ) : ℂ) ∈ S := by
    intro i
    have h1 : e i ∈ T := T.orderEmbOfFin_mem hTcard i
    rw [hT, Finset.mem_image] at h1
    obtain ⟨y, hy, hyre⟩ := h1
    rw [← hyre, hcast y hy]
    exact hy
  set aa : Fin m → ℝ := fun i => e i with haa
  set cc : Fin m → ℝ := fun i => (C ((e i : ℝ) : ℂ)).re with hcc
  have hstrict : StrictMono aa := fun i j hij => (OrderEmbedding.lt_iff_lt e).mpr hij
  have hccne : ∀ i, cc i ≠ 0 := by
    intro i hcon
    refine hCne _ (hemem i) (Complex.ext hcon (hCim _ (hemem i)))
  have hsum : ∀ t : ℝ, (∑ y ∈ S, C y * Complex.exp (y * t)).re = expSum cc aa t := by
    intro t
    rw [re_expCombo_of_real_exponents hSreal t, expSum]
    have hstep : (∑ y ∈ S, (C y).re * Real.exp (y.re * t))
        = ∑ r ∈ T, (C ((r : ℝ) : ℂ)).re * Real.exp (r * t) := by
      rw [hT, Finset.sum_image hinj]
      refine Finset.sum_congr rfl (fun y hy => ?_)
      rw [hcast y hy]
    rw [hstep]
    refine (Finset.sum_bij (fun (i : Fin m) _ => (e i : ℝ)) (fun i _ =>
      T.orderEmbOfFin_mem hTcard i) ?_ ?_ ?_).symm
    · intro i _ j _ hij
      exact e.injective hij
    · intro r hr
      have hrange : r ∈ Set.range (e : Fin m → ℝ) := by
        rw [he, T.range_orderEmbOfFin hTcard]
        exact hr
      obtain ⟨i, hi⟩ := hrange
      exact ⟨i, Finset.mem_univ i, hi⟩
    · intro i _
      rw [hcc, haa]
  refine card_zeros_le_expSum hmpos cc aa hstrict hccne Z (fun x hx => ?_)
  rw [← hsum x]
  exact hZ x hx

end GaloisForLFunctions.HTGeometry
