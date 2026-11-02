import GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary.TwoPrimeResolventSeparation

/-!
# Joint clock separation throughout a vertical strip

Baker separation for the averaged clock defect gives a polynomial lower
bound for the sum of two clock distances. Orienting the point difference
into the left half-plane removes any ordering assumption on real parts.
-/

open Complex
noncomputable section
namespace GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary

lemma norm_clock_sub (a : ℝ) (z w : ℂ) :
    ‖Complex.exp ((a:ℂ)*z)-Complex.exp ((a:ℂ)*w)‖ =
      Real.exp (a*w.re)*‖Complex.exp ((a:ℂ)*(z-w))-1‖ := by
  have he : Complex.exp ((a:ℂ)*z)-Complex.exp ((a:ℂ)*w) =
      Complex.exp ((a:ℂ)*w)*(Complex.exp ((a:ℂ)*(z-w))-1) := by
    rw [mul_sub,mul_one,← Complex.exp_add]
    congr 2
    ring
  rw [he,norm_mul,Complex.norm_exp,Complex.re_ofReal_mul]

lemma norm_clockDefect_le_half_chords (a b : ℝ) (w : ℂ) :
    ‖clockDefect a b w‖ ≤
      (‖Complex.exp ((a:ℂ)*w)-1‖+‖Complex.exp ((b:ℂ)*w)-1‖)/2 := by
  have he : clockDefect a b w =
      -((Complex.exp ((a:ℂ)*w)-1)+(Complex.exp ((b:ℂ)*w)-1))/2 := by
    unfold clockDefect
    ring
  rw [he,norm_div,norm_neg,Complex.norm_two]
  exact div_le_div_of_nonneg_right (norm_add_le _ _) (by norm_num)

/-- In a fixed vertical strip, a joint clock difference controls the averaged defect. -/
lemma strip_clock_distance_lower {a b D : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (z w : ℂ) (hw : -D ≤ w.re) :
    2*min (Real.exp (-a*D)) (Real.exp (-b*D))*‖clockDefect a b (z-w)‖ ≤
      ‖Complex.exp ((a:ℂ)*z)-Complex.exp ((a:ℂ)*w)‖+
      ‖Complex.exp ((b:ℂ)*z)-Complex.exp ((b:ℂ)*w)‖ := by
  let η := min (Real.exp (-a*D)) (Real.exp (-b*D))
  have hη : 0 ≤ η := le_of_lt (lt_min (Real.exp_pos _) (Real.exp_pos _))
  have hηa : η ≤ Real.exp (a*w.re) := (min_le_left _ _).trans
    (Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hw ha]))
  have hηb : η ≤ Real.exp (b*w.re) := (min_le_right _ _).trans
    (Real.exp_le_exp.mpr (by nlinarith only [mul_le_mul_of_nonneg_left hw hb]))
  have hh := mul_le_mul_of_nonneg_left (norm_clockDefect_le_half_chords a b (z-w)) hη
  have hA := mul_le_mul_of_nonneg_right hηa (norm_nonneg (Complex.exp ((a:ℂ)*(z-w))-1))
  have hB := mul_le_mul_of_nonneg_right hηb (norm_nonneg (Complex.exp ((b:ℂ)*(z-w))-1))
  rw [norm_clock_sub,norm_clock_sub]
  change 2*η*‖clockDefect a b (z-w)‖ ≤ _
  linarith only [hh,hA,hB]

/-- Distinct prime clocks separate any two points of a fixed vertical strip,
polynomially in their ordinate difference, outside a fixed diagonal neighborhood. -/
theorem exists_strip_joint_clock_lower {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpq : p ≠ q) (D : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ z w : ℂ,
      -D ≤ z.re → -D ≤ w.re → r ≤ ‖z-w‖ →
      c/(2+|z.im-w.im|)^N ≤
        ‖Complex.exp ((Real.log p:ℂ)*z)-Complex.exp ((Real.log p:ℂ)*w)‖+
        ‖Complex.exp ((Real.log q:ℂ)*z)-Complex.exp ((Real.log q:ℂ)*w)‖ := by
  obtain ⟨c,hc,N,hsep⟩ := exists_two_prime_clockDefect_lower hp hq hpq hr
  let η := min (Real.exp (-Real.log p*D)) (Real.exp (-Real.log q*D))
  have hη : 0 < η := lt_min (Real.exp_pos _) (Real.exp_pos _)
  have ha : 0 ≤ Real.log p := (Real.log_pos (by exact_mod_cast hp.one_lt)).le
  have hb : 0 ≤ Real.log q := (Real.log_pos (by exact_mod_cast hq.one_lt)).le
  refine ⟨2*η*c,by positivity,N,?_⟩
  intro z w hz hw hdist
  have hordered (z w : ℂ) (hw : -D ≤ w.re) (hdist : r ≤ ‖z-w‖) (hre : z.re ≤ w.re) :
      2*η*c/(2+|z.im-w.im|)^N ≤
        ‖Complex.exp ((Real.log p:ℂ)*z)-Complex.exp ((Real.log p:ℂ)*w)‖+
        ‖Complex.exp ((Real.log q:ℂ)*z)-Complex.exp ((Real.log q:ℂ)*w)‖ := by
    have hs := hsep (z-w) (by simpa only [Complex.sub_re] using sub_nonpos.mpr hre) hdist
    rw [Complex.sub_im] at hs
    have hm := mul_le_mul_of_nonneg_left hs (show 0 ≤ 2*η by positivity)
    have hl := strip_clock_distance_lower ha hb z w hw
    have hm' : 2*η*c/(2+|z.im-w.im|)^N ≤
        2*η*‖clockDefect (Real.log p) (Real.log q) (z-w)‖ := by
      simpa only [mul_div_assoc] using hm
    exact hm'.trans hl
  rcases le_total z.re w.re with h | h
  · exact hordered z w hw hdist h
  · have hh := hordered w z hz (by simpa only [norm_sub_rev] using hdist) h
    simpa only [abs_sub_comm w.im z.im,norm_sub_rev] using hh

#print axioms exists_strip_joint_clock_lower
end GaloisForLFunctions.ArithmeticCouplingTheory.ConeBoundary
