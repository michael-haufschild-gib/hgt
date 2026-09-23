import GaloisForLFunctions.RHTower.PrimeArchCentralPairedFourthTraceBand

open Complex Filter Topology

namespace RHTower

noncomputable section

private def pairedBarrier (w lam : ℂ) : ℝ :=
  Complex.normSq lam *
      ((1 - w.re * lam.re) ^ (2 : ℕ) + (w.re * lam.im) ^ (2 : ℕ) +
        w.im ^ (2 : ℕ) * Complex.normSq lam) -
    2 * lam.im ^ (2 : ℕ)

private theorem pairedBarrier_resonance_eq (lam : ℂ) (ha : lam.re ≠ 0) :
    lam.re ^ (2 : ℕ) * pairedBarrier ((1 / lam.re : ℝ) : ℂ) lam =
      lam.im ^ (2 : ℕ) * (lam.im ^ (2 : ℕ) - lam.re ^ (2 : ℕ)) := by
  unfold pairedBarrier
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
  field_simp [ha]
  ring

private theorem pairedBarrier_resonance_neg (lam : ℂ)
    (ha : 0 < lam.re) (hb : lam.im ≠ 0)
    (hphase : lam.im ^ (2 : ℕ) < lam.re ^ (2 : ℕ)) :
    pairedBarrier ((1 / lam.re : ℝ) : ℂ) lam < 0 := by
  have h := pairedBarrier_resonance_eq lam ha.ne'
  have hpos : 0 < lam.re ^ (2 : ℕ) := sq_pos_of_pos ha
  have hneg : lam.im ^ (2 : ℕ) *
      (lam.im ^ (2 : ℕ) - lam.re ^ (2 : ℕ)) < 0 :=
    mul_neg_of_pos_of_neg (sq_pos_of_ne_zero hb) (sub_neg.mpr hphase)
  nlinarith only [h, hpos, hneg]

private theorem pairedBarrier_continuous (lam : ℂ) :
    Continuous (fun w : ℂ => pairedBarrier w lam) := by
  unfold pairedBarrier
  fun_prop

private theorem paired_response_negative_near_resonance (lam : ℂ)
    (ha : 0 < lam.re) (hb : lam.im ≠ 0)
    (hphase : lam.im ^ (2 : ℕ) < lam.re ^ (2 : ℕ)) :
    ∃ z : ℂ, 0 < z.re ∧ 0 < z.im ∧ z.im < 1 / 2 ∧
      1 - z ^ (2 : ℕ) * lam ≠ 0 ∧
      1 - z ^ (2 : ℕ) * (starRingEnd ℂ) lam ≠ 0 ∧
      (lam / (1 - z ^ (2 : ℕ) * lam) +
        (starRingEnd ℂ) lam /
          (1 - z ^ (2 : ℕ) * (starRingEnd ℂ) lam)).im < 0 := by
  let x : ℝ := Real.sqrt (1 / lam.re)
  let z : ℝ → ℂ := fun y => (x : ℂ) + (y : ℂ) * I
  have hxpos : 0 < x := Real.sqrt_pos.2 (one_div_pos.2 ha)
  have hx : x ^ (2 : ℕ) = 1 / lam.re := Real.sq_sqrt (one_div_pos.2 ha).le
  have hz0 : z 0 ^ (2 : ℕ) = ((1 / lam.re : ℝ) : ℂ) := by
    have hzero : z 0 = (x : ℂ) := by simp [z]
    rw [hzero, ← Complex.ofReal_pow, hx]
  have hbar0 : pairedBarrier (z 0 ^ (2 : ℕ)) lam < 0 := by
    rw [hz0]
    exact pairedBarrier_resonance_neg lam ha hb hphase
  have hden0 : 1 - z 0 ^ (2 : ℕ) * lam ≠ 0 := by
    rw [hz0]
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.one_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.zero_im] at hi
    have ha0 : 1 / lam.re ≠ 0 := (one_div_pos.2 ha).ne'
    have hmul : (1 / lam.re) * lam.im = 0 := by linarith only [hi]
    exact hb ((mul_eq_zero.mp hmul).resolve_left ha0)
  have hdenconj0 : 1 - z 0 ^ (2 : ℕ) * (starRingEnd ℂ) lam ≠ 0 := by
    rw [hz0]
    intro he
    have hi := congrArg Complex.im he
    simp only [Complex.sub_im, Complex.one_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.zero_im, Complex.conj_im] at hi
    have ha0 : 1 / lam.re ≠ 0 := (one_div_pos.2 ha).ne'
    have hmul : (1 / lam.re) * -lam.im = 0 := by linarith only [hi]
    exact hb (neg_eq_zero.mp ((mul_eq_zero.mp hmul).resolve_left ha0))
  have hzcont : Continuous z := by
    dsimp [z]
    fun_prop
  have hbarcont : ContinuousAt (fun y : ℝ => pairedBarrier (z y ^ (2 : ℕ)) lam) 0 :=
    ((pairedBarrier_continuous lam).comp (hzcont.pow 2)).continuousAt
  have hdencont : ContinuousAt (fun y : ℝ => 1 - z y ^ (2 : ℕ) * lam) 0 := by
    fun_prop
  have hdenconjcont : ContinuousAt
      (fun y : ℝ => 1 - z y ^ (2 : ℕ) * (starRingEnd ℂ) lam) 0 := by
    fun_prop
  have hev : ∀ᶠ y : ℝ in 𝓝 0,
      pairedBarrier (z y ^ (2 : ℕ)) lam < 0 ∧
      1 - z y ^ (2 : ℕ) * lam ≠ 0 ∧
      1 - z y ^ (2 : ℕ) * (starRingEnd ℂ) lam ≠ 0 :=
    (hbarcont.eventually (eventually_lt_nhds hbar0)).and
      ((hdencont.eventually (eventually_ne_nhds hden0)).and
        (hdenconjcont.eventually (eventually_ne_nhds hdenconj0)))
  obtain ⟨ε, hε, hnear⟩ := Metric.eventually_nhds_iff.mp hev
  let y : ℝ := min (ε / 2) (1 / 4)
  have hypos : 0 < y := lt_min (half_pos hε) (by norm_num)
  have hyhalf : y < 1 / 2 := (min_le_right _ _).trans_lt (by norm_num)
  have hydist : dist y (0 : ℝ) < ε := by
    rw [Real.dist_eq, sub_zero, abs_of_pos hypos]
    have hyle : y ≤ ε / 2 := min_le_left _ _
    linarith
  obtain ⟨hbar, hden, hdenconj⟩ := hnear hydist
  have hzre : (z y).re = x := by simp [z]
  have hzim : (z y).im = y := by simp [z]
  refine ⟨z y, hzre ▸ hxpos, hzim ▸ hypos, hzim ▸ hyhalf,
    hden, hdenconj, ?_⟩
  have hwim : 0 < (z y ^ (2 : ℕ)).im := by
    rw [pow_two, Complex.mul_im, hzre, hzim]
    nlinarith [mul_pos hxpos hypos]
  have hdenpos : 0 < Complex.normSq (1 - z y ^ (2 : ℕ) * lam) :=
    Complex.normSq_pos.mpr hden
  have hdenconjpos : 0 < Complex.normSq
      (1 - z y ^ (2 : ℕ) * (starRingEnd ℂ) lam) :=
    Complex.normSq_pos.mpr hdenconj
  rw [centralPaired_reciprocalSquare_lineConj_pair_im_formula
    (z y ^ (2 : ℕ)) lam hden hdenconj]
  change 2 * (z y ^ (2 : ℕ)).im * pairedBarrier (z y ^ (2 : ℕ)) lam /
    (Complex.normSq (1 - z y ^ (2 : ℕ) * lam) *
      Complex.normSq (1 - z y ^ (2 : ℕ) * (starRingEnd ℂ) lam)) < 0
  exact div_neg_of_neg_of_pos (mul_neg_of_pos_of_neg (by positivity) hbar)
    (mul_pos hdenpos hdenconjpos)

end
end RHTower
