import GaloisForLFunctions.RHTower.Sieve.DistanceTriangle

/-!
# The triangle inequality on the closed unit disc

For unimodular values the distance is a Euclidean norm and the triangle inequality is free.  On the
closed unit disc the identity `1 - Re(u conj v) = ‖u-v‖²/2` fails and the naive comparison

`1 - Re(u conj w) ≤ (1 - Re(u conj v)) + (1 - Re(v conj w))`

is false — at `u = e^{iπ/3}`, `v = 1`, `w = e^{-iπ/3}` it reads `3/2 ≤ 1/2 + 1/2`.  The cross term is
essential.

The identity that survives is

`2(1 - Re(u conj v)) = ‖u - v‖² + (1 - ‖u‖²) + (1 - ‖v‖²)`,

so with `X = ‖u-v‖`, `Y = ‖v-w‖`, `Z = ‖u-w‖` and defects `a = 1-‖u‖²`, `b = 1-‖v‖²`, `c = 1-‖w‖²`,

`2A = X² + a + b`,  `2B = Y² + b + c`,  `2C = Z² + a + c`.

Then `4AB ≥ (X²+b)(Y²+b) = (XY+b)² + b(X-Y)² ≥ (XY+b)²`, so `2√(AB) ≥ XY + b`, while `Z ≤ X + Y`
gives `C ≤ A + B + XY - b`.  Hence `C ≤ A + B + 2√A√B = (√A + √B)²`.

Summing over primes against the weights `1/p` and applying Minkowski gives the full
Granville–Soundararajan triangle inequality for multiplicative functions bounded by one.
-/

namespace RHTower.Sieve

open Finset

/-- **The pointwise triangle inequality on the closed unit disc.** -/
theorem sqrt_one_sub_re_triangle {u v w : ℂ} (hu : ‖u‖ ≤ 1) (hv : ‖v‖ ≤ 1) (hw : ‖w‖ ≤ 1) :
    Real.sqrt (1 - (u * (starRingEnd ℂ) w).re)
      ≤ Real.sqrt (1 - (u * (starRingEnd ℂ) v).re)
        + Real.sqrt (1 - (v * (starRingEnd ℂ) w).re) := by
  have hu0 : (0 : ℝ) ≤ ‖u‖ := norm_nonneg u
  have hv0 : (0 : ℝ) ≤ ‖v‖ := norm_nonneg v
  have hw0 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg w
  set A := 1 - (u * (starRingEnd ℂ) v).re with hAdef
  set B := 1 - (v * (starRingEnd ℂ) w).re with hBdef
  set C := 1 - (u * (starRingEnd ℂ) w).re with hCdef
  set X := ‖u - v‖ with hXdef
  set Y := ‖v - w‖ with hYdef
  set Z := ‖u - w‖ with hZdef
  set a := 1 - ‖u‖ ^ (2 : ℕ) with hadef
  set b := 1 - ‖v‖ ^ (2 : ℕ) with hbdef
  set c := 1 - ‖w‖ ^ (2 : ℕ) with hcdef
  have ha : 0 ≤ a := by rw [hadef]; nlinarith
  have hb : 0 ≤ b := by rw [hbdef]; nlinarith
  have hc : 0 ≤ c := by rw [hcdef]; nlinarith
  have hX0 : 0 ≤ X := norm_nonneg _
  have hY0 : 0 ≤ Y := norm_nonneg _
  have hZ0 : 0 ≤ Z := norm_nonneg _
  have h2A : 2 * A = X ^ (2 : ℕ) + a + b := by
    have h := normSq_sub_eq u v
    rw [hAdef, hXdef, hadef, hbdef]; linarith [h]
  have h2B : 2 * B = Y ^ (2 : ℕ) + b + c := by
    have h := normSq_sub_eq v w
    rw [hBdef, hYdef, hbdef, hcdef]; linarith [h]
  have h2C : 2 * C = Z ^ (2 : ℕ) + a + c := by
    have h := normSq_sub_eq u w
    rw [hCdef, hZdef, hadef, hcdef]; linarith [h]
  have hZle : Z ≤ X + Y := by
    rw [hXdef, hYdef, hZdef]
    simpa [dist_eq_norm] using dist_triangle u v w
  have hA0 : 0 ≤ A := by linarith [sq_nonneg X]
  have hB0 : 0 ≤ B := by linarith [sq_nonneg Y]
  have hC0 : 0 ≤ C := by linarith [sq_nonneg Z]
  set sA := Real.sqrt A with hsAdef
  set sB := Real.sqrt B with hsBdef
  have hsA0 : 0 ≤ sA := Real.sqrt_nonneg _
  have hsB0 : 0 ≤ sB := Real.sqrt_nonneg _
  have hsA : sA ^ (2 : ℕ) = A := Real.sq_sqrt hA0
  have hsB : sB ^ (2 : ℕ) = B := Real.sq_sqrt hB0
  have hfac1 : (0 : ℝ) ≤ X ^ (2 : ℕ) + b := by linarith [sq_nonneg X]
  have hfac2 : (0 : ℝ) ≤ Y ^ (2 : ℕ) + b := by linarith [sq_nonneg Y]
  -- the slack `b (X - Y)²` is what pays for the cross term
  have hstep2 : (X * Y + b) ^ (2 : ℕ) ≤ (X ^ (2 : ℕ) + b) * (Y ^ (2 : ℕ) + b) := by
    linarith [mul_nonneg hb (sq_nonneg (X - Y))]
  have hstep1 : (X ^ (2 : ℕ) + b) * (Y ^ (2 : ℕ) + b) ≤ (X ^ (2 : ℕ) + a + b) * (Y ^ (2 : ℕ) + b + c) := by
    linarith [mul_nonneg ha hfac2, mul_nonneg hc hfac1, mul_nonneg ha hc]
  have h4AB : 4 * (A * B) = (X ^ (2 : ℕ) + a + b) * (Y ^ (2 : ℕ) + b + c) := by
    calc 4 * (A * B) = (2 * A) * (2 * B) := by ring
      _ = (X ^ (2 : ℕ) + a + b) * (Y ^ (2 : ℕ) + b + c) := by rw [h2A, h2B]
  have hkey : (X * Y + b) ^ (2 : ℕ) ≤ (2 * sA * sB) ^ (2 : ℕ) := by
    have hexp : (2 * sA * sB) ^ (2 : ℕ) = 4 * (A * B) := by
      calc (2 * sA * sB) ^ (2 : ℕ) = 4 * (sA ^ (2 : ℕ) * sB ^ (2 : ℕ)) := by ring
        _ = 4 * (A * B) := by rw [hsA, hsB]
    rw [hexp, h4AB]
    linarith [hstep1, hstep2]
  have hcross : X * Y + b ≤ 2 * sA * sB := by
    have h1 : (0 : ℝ) ≤ X * Y + b := by linarith [mul_nonneg hX0 hY0]
    have h2 : (0 : ℝ) ≤ 2 * sA * sB := by linarith [mul_nonneg hsA0 hsB0]
    have h3 := Real.sqrt_le_sqrt hkey
    rwa [Real.sqrt_sq h1, Real.sqrt_sq h2] at h3
  have hZsq : Z ^ (2 : ℕ) ≤ (X + Y) ^ (2 : ℕ) := pow_le_pow_left₀ hZ0 hZle 2
  have hCle : C ≤ A + B + 2 * sA * sB := by linarith [hZsq, h2A, h2B, h2C, hcross, hb]
  have hsC : Real.sqrt C ^ (2 : ℕ) = C := Real.sq_sqrt hC0
  have hsC0 : (0 : ℝ) ≤ Real.sqrt C := Real.sqrt_nonneg _
  have hsum0 : (0 : ℝ) ≤ sA + sB := by linarith
  have hsq : Real.sqrt C ^ (2 : ℕ) ≤ (sA + sB) ^ (2 : ℕ) := by linarith [hsC, hCle, hsA, hsB]
  have h4 := Real.sqrt_le_sqrt hsq
  rwa [Real.sqrt_sq hsC0, Real.sqrt_sq hsum0] at h4

/-- **Minkowski's inequality for a finite sum of squares.** -/
theorem sqrt_sum_sq_add_le (P : Finset ℕ) (x y : ℕ → ℝ) :
    Real.sqrt (∑ p ∈ P, (x p + y p) ^ (2 : ℕ))
      ≤ Real.sqrt (∑ p ∈ P, x p ^ (2 : ℕ)) + Real.sqrt (∑ p ∈ P, y p ^ (2 : ℕ)) := by
  have hnorm : ∀ z : ℕ → ℝ,
      ‖(WithLp.toLp 2 (fun p : {q // q ∈ P} => z p.1) : EuclideanSpace ℝ {q // q ∈ P})‖
        = Real.sqrt (∑ p ∈ P, z p ^ (2 : ℕ)) := by
    intro z
    rw [EuclideanSpace.norm_eq]
    congr 1
    rw [← Finset.sum_coe_sort P fun p => z p ^ (2 : ℕ)]
    refine Finset.sum_congr rfl fun p _ => ?_
    simp [Real.norm_eq_abs, sq_abs]
  have hadd :
      (WithLp.toLp 2 (fun p : {q // q ∈ P} => x p.1) : EuclideanSpace ℝ {q // q ∈ P})
          + WithLp.toLp 2 (fun p : {q // q ∈ P} => y p.1)
        = WithLp.toLp 2 (fun p : {q // q ∈ P} => x p.1 + y p.1) := by
    ext p; simp
  rw [← hnorm x, ← hnorm y, ← hnorm (fun n => x n + y n), ← hadd]
  exact norm_add_le _ _

/-- A product of two values in the closed unit disc, one conjugated, has real part at most one. -/
theorem one_sub_re_mul_conj_nonneg {F G : ℕ → ℂ} {P : Finset ℕ} (hF : ∀ p ∈ P, ‖F p‖ ≤ 1)
    (hG : ∀ p ∈ P, ‖G p‖ ≤ 1) {p : ℕ} (hp : p ∈ P) :
    (0 : ℝ) ≤ 1 - (F p * (starRingEnd ℂ) (G p)).re := by
  refine one_sub_re_nonneg ?_
  rw [norm_mul, RCLike.norm_conj]
  exact mul_le_one₀ (hF p hp) (norm_nonneg _) (hG p hp)

/-- **The Granville–Soundararajan triangle inequality for functions bounded by one.** -/
theorem sqrt_mulDistSqPair_triangle_disc {f g h : ℕ → ℂ} {P : Finset ℕ}
    (hf : ∀ p ∈ P, ‖f p‖ ≤ 1) (hg : ∀ p ∈ P, ‖g p‖ ≤ 1) (hh : ∀ p ∈ P, ‖h p‖ ≤ 1)
    (hP : ∀ p ∈ P, 0 < p) :
    Real.sqrt (mulDistSqPair f h P)
      ≤ Real.sqrt (mulDistSqPair f g P) + Real.sqrt (mulDistSqPair g h P) := by
  classical
  set x : ℕ → ℝ := fun p => Real.sqrt ((1 - (f p * (starRingEnd ℂ) (g p)).re) / (p : ℝ))
    with hxdef
  set y : ℕ → ℝ := fun p => Real.sqrt ((1 - (g p * (starRingEnd ℂ) (h p)).re) / (p : ℝ))
    with hydef
  have hpt : ∀ p ∈ P, (1 - (f p * (starRingEnd ℂ) (h p)).re) / (p : ℝ) ≤ (x p + y p) ^ (2 : ℕ) := by
    intro p hp
    have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hP p hp
    have hAn := one_sub_re_mul_conj_nonneg hf hg hp
    have hBn := one_sub_re_mul_conj_nonneg hg hh hp
    have hCn := one_sub_re_mul_conj_nonneg hf hh hp
    have hCq : (0 : ℝ) ≤ (1 - (f p * (starRingEnd ℂ) (h p)).re) / (p : ℝ) := by positivity
    have hbase := sqrt_one_sub_re_triangle (hf p hp) (hg p hp) (hh p hp)
    have hdiv : Real.sqrt ((1 - (f p * (starRingEnd ℂ) (h p)).re) / (p : ℝ)) ≤ x p + y p := by
      simp only [hxdef, hydef]
      rw [Real.sqrt_div hCn, Real.sqrt_div hAn, Real.sqrt_div hBn, ← add_div]
      gcongr
    have hsq : Real.sqrt ((1 - (f p * (starRingEnd ℂ) (h p)).re) / (p : ℝ)) ^ (2 : ℕ)
        = (1 - (f p * (starRingEnd ℂ) (h p)).re) / (p : ℝ) := Real.sq_sqrt hCq
    rw [← hsq]
    exact pow_le_pow_left₀ (Real.sqrt_nonneg _) hdiv 2
  have hsum : mulDistSqPair f h P ≤ ∑ p ∈ P, (x p + y p) ^ (2 : ℕ) := Finset.sum_le_sum hpt
  have hx2 : ∑ p ∈ P, x p ^ (2 : ℕ) = mulDistSqPair f g P := by
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [hxdef]
    exact Real.sq_sqrt (by have := one_sub_re_mul_conj_nonneg hf hg hp
                           have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hP p hp
                           positivity)
  have hy2 : ∑ p ∈ P, y p ^ (2 : ℕ) = mulDistSqPair g h P := by
    refine Finset.sum_congr rfl fun p hp => ?_
    simp only [hydef]
    exact Real.sq_sqrt (by have := one_sub_re_mul_conj_nonneg hg hh hp
                           have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hP p hp
                           positivity)
  calc Real.sqrt (mulDistSqPair f h P)
      ≤ Real.sqrt (∑ p ∈ P, (x p + y p) ^ (2 : ℕ)) := Real.sqrt_le_sqrt hsum
    _ ≤ Real.sqrt (∑ p ∈ P, x p ^ (2 : ℕ)) + Real.sqrt (∑ p ∈ P, y p ^ (2 : ℕ)) := sqrt_sum_sq_add_le P x y
    _ = Real.sqrt (mulDistSqPair f g P) + Real.sqrt (mulDistSqPair g h P) := by rw [hx2, hy2]

/-- The distance between functions bounded by one is nonnegative. -/
theorem mulDistSqPair_nonneg_disc {f g : ℕ → ℂ} {P : Finset ℕ} (hf : ∀ p ∈ P, ‖f p‖ ≤ 1)
    (hg : ∀ p ∈ P, ‖g p‖ ≤ 1) (hP : ∀ p ∈ P, 0 < p) : 0 ≤ mulDistSqPair f g P := by
  refine Finset.sum_nonneg fun p hp => ?_
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hP p hp
  have := one_sub_re_mul_conj_nonneg hf hg hp
  positivity

/-- **Distance to a character is transitive for any function bounded by one.** -/
theorem sqrt_mulDistSq_triangle_char_disc {f : ℕ → ℂ} {P : Finset ℕ} (hf : ∀ p ∈ P, ‖f p‖ ≤ 1)
    (t u : ℝ) (hP : ∀ p ∈ P, 0 < p) :
    Real.sqrt (mulDistSq f t P)
      ≤ Real.sqrt (mulDistSqPair f (charFn u) P)
        + Real.sqrt (mulDistSqPair (charFn u) (charFn t) P) := by
  rw [mulDistSq_eq_pair]
  exact sqrt_mulDistSqPair_triangle_disc hf (fun p _ => (norm_charFn u p).le)
    (fun p _ => (norm_charFn t p).le) hP

end RHTower.Sieve
