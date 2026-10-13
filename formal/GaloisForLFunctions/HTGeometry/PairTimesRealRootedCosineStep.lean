import GaloisForLFunctions.HTGeometry.ShiftAverageNonrealCount

/-!
# The cosine step on one non-real pair times a real-rooted polynomial

Let `p = ((X − x)² + y²)·g` with `g` a nonzero real polynomial having only real roots, and let
`a > 0`. Every root `w` of the shift average `cos(aD)p = (p(z + ia) + p(z − ia))/2` with `Im w > 0`
lies in the closed disc

`(Re w − x)² + (Im w)² + a² ≤ y²`

(`sq_add_sq_add_sq_le_of_shiftAvg_pair_mul_root`). In particular `(Im w)² + a² ≤ y²`: the
cosine step lowers the squared height of the surviving non-real root by at least `a²`, whatever
the real roots are, and kills the pair when `a ≥ y`.

The same holds with `g` multiplied by any product of shallow pairs `(z − x_j)² + y_j²`,
`y_j² ≤ a²` (`sq_add_sq_add_sq_le_of_shiftAvg_pair_mul_shallow_root`): a shallow pair grows upward,
`|q_j(w − ia)| ≤ |q_j(w + ia)|`, exactly like a real root (`normSq_shallowPair_sub_le_add`).

**Any number of pairs** (`exists_disc_of_shiftAvg_pairs_root`): for `p = g·∏_{k∈s}((X − x_k)² + y_k²)`
every upper root `w` of the shift average lies in some closed disc
`(Re w − x_k)² + (Im w)² + a² ≤ y_k²`. Outside all discs every pair factor grows strictly upward
and every real root weakly, so `|p(w + ia)| > |p(w − ia)|`; a vanishing lower factor forces
`w + ia` onto a pair root, which lies in that pair's disc. This refines de Bruijn's strip bound
`(Im w)² + a² ≤ max_k y_k²` to a union of discs.

**Proof.** At such a root `p(w + ia) = −p(w − ia)`. Each real root `r` of `g` satisfies
`|w + ia − r|² − |w − ia − r|² = 4a·Im w ≥ 0`, so `|g(w + ia)| ≥ |g(w − ia)|` with
`g(w + ia) ≠ 0` (`normSq_eval_sub_le_add_of_real_roots`). Hence `|q(w + ia)| ≤ |q(w − ia)|` for
`q = (z − x)² + y²`. With `ζ = w − x = u + iv` and `F(s) = |(u + is)² + y²|²
= (u² + s² + y²)² − 4s²y²`, one has `F(v + a) − F(v − a) = 8va(u² + v² + a² − y²)`
(`normSq_pair_add_sub_normSq_pair_sub`), which must be `≤ 0`.
-/

open Polynomial Complex

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The pair `(X − x)² + y²` times `g`. -/
def pairTimes (x y : ℝ) (g : ℝ[X]) : ℝ[X] := ((X - C x) ^ 2 + C (y ^ 2)) * g

/-- A real root contributes a nonnegative difference of squared distances. -/
theorem normSq_sub_le_add (w r : ℂ) (hr : r.im = 0) {a : ℝ} (ha : 0 ≤ a) (hw : 0 ≤ w.im) :
    normSq (w - a * I - r) ≤ normSq (w + a * I - r) := by
  simp only [normSq_apply, sub_re, add_re, mul_re, ofReal_re, I_re, ofReal_im, I_im, sub_im,
    add_im, mul_im, hr]
  nlinarith [mul_nonneg ha hw]

/-- **Real-rooted factors grow upward.** If every complex root of `g` is real, then
`|g(w − ia)| ≤ |g(w + ia)|` for `Im w ≥ 0`, `a ≥ 0`. -/
theorem normSq_eval_sub_le_add_of_real_roots {g : ℝ[X]}
    (hg : ∀ r ∈ (g.map ofRealHom).roots, r.im = 0) {a : ℝ} (ha : 0 ≤ a) {w : ℂ}
    (hw : 0 ≤ w.im) :
    normSq ((g.map ofRealHom).eval (w - a * I)) ≤ normSq ((g.map ofRealHom).eval (w + a * I)) := by
  set G := g.map ofRealHom
  have hsplit : C G.leadingCoeff * (G.roots.map fun r => X - C r).prod = G :=
    C_leadingCoeff_mul_prod_multiset_X_sub_C IsAlgClosed.card_roots_eq_natDegree
  have heval : ∀ z : ℂ, G.eval z = G.leadingCoeff * (G.roots.map fun r => z - r).prod := by
    intro z
    conv_lhs => rw [← hsplit]
    rw [eval_mul, eval_C, eval_multiset_prod, Multiset.map_map]
    simp
  rw [heval, heval, map_mul, map_mul, map_multiset_prod, map_multiset_prod, Multiset.map_map,
    Multiset.map_map]
  apply mul_le_mul_of_nonneg_left _ (normSq_nonneg _)
  apply Multiset.prod_map_le_prod_map₀
  · intro r _; exact normSq_nonneg _
  · intro r hr; exact normSq_sub_le_add w r (hg r hr) ha hw

/-- The squared-norm difference for the pair factor: with `ζ = u + iv`,
`|(ζ + ia)² + y²|² − |(ζ − ia)² + y²|² = 8va(u² + v² + a² − y²)`. -/
theorem normSq_pair_add_sub_normSq_pair_sub (u v a y : ℝ) :
    normSq (((u : ℂ) + v * I + a * I) ^ 2 + (y : ℂ) ^ 2) -
        normSq (((u : ℂ) + v * I - a * I) ^ 2 + (y : ℂ) ^ 2) =
      8 * v * a * (u ^ 2 + v ^ 2 + a ^ 2 - y ^ 2) := by
  simp only [normSq_apply, add_re, sub_re, add_im, sub_im, pow_two, mul_re, mul_im, ofReal_re,
    ofReal_im, I_re, I_im]
  ring

theorem eval_map_pairTimes (x y : ℝ) (g : ℝ[X]) (z : ℂ) :
    ((pairTimes x y g).map ofRealHom).eval z =
      ((z - x) ^ 2 + (y : ℂ) ^ 2) * (g.map ofRealHom).eval z := by
  simp [pairTimes]

/-- **The cosine step on a pair times a real-rooted polynomial.** For `a > 0`, every root `w` of
`(p(z + ia) + p(z − ia))/2` with `Im w > 0`, `p = ((X − x)² + y²)·g`, `g ≠ 0` real-rooted,
satisfies `(Re w − x)² + (Im w)² + a² ≤ y²`. -/
theorem sq_add_sq_add_sq_le_of_shiftAvg_pair_mul_root {x y a : ℝ} {g : ℝ[X]} (hg0 : g ≠ 0)
    (hg : ∀ r ∈ (g.map ofRealHom).roots, r.im = 0) (ha : 0 < a) {w : ℂ} (hw : 0 < w.im)
    (hroot : ((shiftAvg a (pairTimes x y g)).map ofRealHom).eval w = 0) :
    (w.re - x) ^ 2 + w.im ^ 2 + a ^ 2 ≤ y ^ 2 := by
  rw [eval_map_shiftAvg, eval_map_pairTimes, eval_map_pairTimes] at hroot
  set G := g.map ofRealHom
  have hsum : ((w + a * I - x) ^ 2 + (y : ℂ) ^ 2) * G.eval (w + a * I) =
      -(((w - a * I - x) ^ 2 + (y : ℂ) ^ 2) * G.eval (w - a * I)) := by
    linear_combination (2 : ℂ) * hroot
  have hn := congrArg normSq hsum
  rw [normSq_neg, map_mul, map_mul] at hn
  have hG := normSq_eval_sub_le_add_of_real_roots hg ha.le (w := w) hw.le
  -- `g(w + ia) ≠ 0` because `w + ia` is not real.
  have hGne : G.eval (w + a * I) ≠ 0 := by
    intro h0
    have hG0 : G ≠ 0 := (Polynomial.map_ne_zero_iff ofRealHom.injective).mpr hg0
    have hmem : w + a * I ∈ G.roots := (mem_roots hG0).mpr h0
    have := hg _ hmem
    simp only [add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, add_zero,
      mul_one] at this
    linarith
  have hpos : 0 < normSq (G.eval (w + a * I)) := normSq_pos.mpr hGne
  have hq : normSq ((w + a * I - x) ^ 2 + (y : ℂ) ^ 2) ≤
      normSq ((w - a * I - x) ^ 2 + (y : ℂ) ^ 2) := by
    by_contra hcon
    replace hcon := lt_of_not_ge hcon
    have h1 : normSq ((w - a * I - x) ^ 2 + (y : ℂ) ^ 2) * normSq (G.eval (w - a * I)) ≤
        normSq ((w - a * I - x) ^ 2 + (y : ℂ) ^ 2) * normSq (G.eval (w + a * I)) :=
      mul_le_mul_of_nonneg_left hG (normSq_nonneg _)
    have h2 : normSq ((w - a * I - x) ^ 2 + (y : ℂ) ^ 2) * normSq (G.eval (w + a * I)) <
        normSq ((w + a * I - x) ^ 2 + (y : ℂ) ^ 2) * normSq (G.eval (w + a * I)) :=
      mul_lt_mul_of_pos_right hcon hpos
    linarith
  have hw' : w = ((w.re - x : ℝ) : ℂ) + x + (w.im : ℂ) * I := by
    apply Complex.ext <;> simp
  have key := normSq_pair_add_sub_normSq_pair_sub (w.re - x) w.im a y
  have e1 : ((w + a * I - x) ^ 2 + (y : ℂ) ^ 2) =
      ((((w.re - x : ℝ) : ℂ) + w.im * I + a * I) ^ 2 + (y : ℂ) ^ 2) := by
    conv_lhs => rw [hw']
    ring
  have e2 : ((w - a * I - x) ^ 2 + (y : ℂ) ^ 2) =
      ((((w.re - x : ℝ) : ℂ) + w.im * I - a * I) ^ 2 + (y : ℂ) ^ 2) := by
    conv_lhs => rw [hw']
    ring
  rw [← e1, ← e2] at key
  have hva : 0 < 8 * w.im * a := by positivity
  have : 8 * w.im * a * ((w.re - x) ^ 2 + w.im ^ 2 + a ^ 2 - y ^ 2) ≤ 0 := by linarith
  have := (mul_nonpos_iff.mp this)
  rcases this with ⟨h, _⟩ | ⟨_, h⟩
  · linarith
  · linarith

/-- A shallow pair `(z − x)² + y²` with `y² ≤ a²` grows upward: `|q(w − ia)| ≤ |q(w + ia)|` for
`Im w ≥ 0`, `a ≥ 0`, because the difference of squared norms is
`8·Im w·a((Re w − x)² + (Im w)² + a² − y²) ≥ 0`. -/
theorem normSq_shallowPair_sub_le_add {x y a : ℝ} (ha : 0 ≤ a) (hya : y ^ 2 ≤ a ^ 2) {w : ℂ}
    (hw : 0 ≤ w.im) :
    normSq ((w - a * I - x) ^ 2 + (y : ℂ) ^ 2) ≤ normSq ((w + a * I - x) ^ 2 + (y : ℂ) ^ 2) := by
  have hw' : w = ((w.re - x : ℝ) : ℂ) + x + (w.im : ℂ) * I := by
    apply Complex.ext <;> simp
  have key := normSq_pair_add_sub_normSq_pair_sub (w.re - x) w.im a y
  have e1 : ((w + a * I - x) ^ 2 + (y : ℂ) ^ 2) =
      ((((w.re - x : ℝ) : ℂ) + w.im * I + a * I) ^ 2 + (y : ℂ) ^ 2) := by
    conv_lhs => rw [hw']
    ring
  have e2 : ((w - a * I - x) ^ 2 + (y : ℂ) ^ 2) =
      ((((w.re - x : ℝ) : ℂ) + w.im * I - a * I) ^ 2 + (y : ℂ) ^ 2) := by
    conv_lhs => rw [hw']
    ring
  rw [← e1, ← e2] at key
  have : 0 ≤ 8 * w.im * a * ((w.re - x) ^ 2 + w.im ^ 2 + a ^ 2 - y ^ 2) := by
    apply mul_nonneg (by positivity)
    nlinarith [sq_nonneg (w.re - x), sq_nonneg w.im]
  linarith

/-- The product of shallow pairs `∏_{j ∈ s} ((z − x_j)² + y_j²)`. -/
def shallowPairs {ι : Type*} (s : Finset ι) (x y : ι → ℝ) : ℝ[X] :=
  ∏ j ∈ s, ((X - C (x j)) ^ 2 + C (y j ^ 2))

theorem eval_map_shallowPairs {ι : Type*} (s : Finset ι) (x y : ι → ℝ) (z : ℂ) :
    ((shallowPairs s x y).map ofRealHom).eval z = ∏ j ∈ s, ((z - x j) ^ 2 + (y j : ℂ) ^ 2) := by
  simp [shallowPairs, Polynomial.map_prod, eval_prod]

theorem normSq_eval_shallowPairs_sub_le_add {ι : Type*} (s : Finset ι) (x y : ι → ℝ) {a : ℝ}
    (ha : 0 ≤ a) (hya : ∀ j ∈ s, y j ^ 2 ≤ a ^ 2) {w : ℂ} (hw : 0 ≤ w.im) :
    normSq (((shallowPairs s x y).map ofRealHom).eval (w - a * I)) ≤
      normSq (((shallowPairs s x y).map ofRealHom).eval (w + a * I)) := by
  rw [eval_map_shallowPairs, eval_map_shallowPairs, map_prod, map_prod]
  apply Finset.prod_le_prod
  · intro j _; exact normSq_nonneg _
  · intro j hj; exact normSq_shallowPair_sub_le_add ha (hya j hj) hw

/-- **One deep pair, any shallow configuration.** Let `p = ((X − x)² + y²)·g·∏_{j∈s}((X − x_j)² +
y_j²)` with `g ≠ 0` real-rooted and every `y_j² ≤ a²`. For `a > 0`, every root `w` of
`(p(z + ia) + p(z − ia))/2` with `Im w > 0` satisfies `(Re w − x)² + (Im w)² + a² ≤ y²`. -/
theorem sq_add_sq_add_sq_le_of_shiftAvg_pair_mul_shallow_root {ι : Type*} {x y a : ℝ}
    {g : ℝ[X]} (hg0 : g ≠ 0) (hg : ∀ r ∈ (g.map ofRealHom).roots, r.im = 0)
    (s : Finset ι) (xs ys : ι → ℝ) (hys : ∀ j ∈ s, ys j ^ 2 ≤ a ^ 2) (ha : 0 < a) {w : ℂ}
    (hw : 0 < w.im)
    (hroot : ((shiftAvg a (pairTimes x y (g * shallowPairs s xs ys))).map ofRealHom).eval w = 0) :
    (w.re - x) ^ 2 + w.im ^ 2 + a ^ 2 ≤ y ^ 2 := by
  rw [eval_map_shiftAvg, eval_map_pairTimes, eval_map_pairTimes] at hroot
  set G := g.map ofRealHom
  set H := (shallowPairs s xs ys).map ofRealHom
  have hmapmul : ((g * shallowPairs s xs ys).map ofRealHom) = G * H := Polynomial.map_mul _
  rw [hmapmul, eval_mul, eval_mul] at hroot
  have hsum : ((w + a * I - x) ^ 2 + (y : ℂ) ^ 2) * (G.eval (w + a * I) * H.eval (w + a * I)) =
      -(((w - a * I - x) ^ 2 + (y : ℂ) ^ 2) * (G.eval (w - a * I) * H.eval (w - a * I))) := by
    linear_combination (2 : ℂ) * hroot
  have hn := congrArg normSq hsum
  rw [normSq_neg, map_mul, map_mul, map_mul, map_mul] at hn
  have hG := normSq_eval_sub_le_add_of_real_roots hg ha.le (w := w) hw.le
  have hH := normSq_eval_shallowPairs_sub_le_add s xs ys ha.le hys (w := w) hw.le
  -- `g(w + ia) ≠ 0` and every shallow pair is nonzero at `w + ia`.
  have hGne : G.eval (w + a * I) ≠ 0 := by
    intro h0
    have hG0 : G ≠ 0 := (Polynomial.map_ne_zero_iff ofRealHom.injective).mpr hg0
    have := hg _ ((mem_roots hG0).mpr h0)
    simp only [add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, add_zero,
      mul_one] at this
    linarith
  have hHne : H.eval (w + a * I) ≠ 0 := by
    rw [eval_map_shallowPairs, Finset.prod_ne_zero_iff]
    intro j hj h0
    have hle := normSq_shallowPair_sub_le_add (x := xs j) ha.le (hys j hj) hw.le
    -- At `w + ia` the pair is a sum of a strictly positive and a nonnegative square.
    have hval : normSq ((w + a * I - xs j) ^ 2 + (ys j : ℂ) ^ 2) = 0 := by rw [h0, map_zero]
    have hw' : w = ((w.re - xs j : ℝ) : ℂ) + xs j + (w.im : ℂ) * I := by
      apply Complex.ext <;> simp
    have key := normSq_pair_add_sub_normSq_pair_sub (w.re - xs j) w.im a (ys j)
    have e1 : ((w + a * I - xs j) ^ 2 + (ys j : ℂ) ^ 2) =
        ((((w.re - xs j : ℝ) : ℂ) + w.im * I + a * I) ^ 2 + (ys j : ℂ) ^ 2) := by
      conv_lhs => rw [hw']
      ring
    have e2 : ((w - a * I - xs j) ^ 2 + (ys j : ℂ) ^ 2) =
        ((((w.re - xs j : ℝ) : ℂ) + w.im * I - a * I) ^ 2 + (ys j : ℂ) ^ 2) := by
      conv_lhs => rw [hw']
      ring
    rw [← e1, ← e2, hval] at key
    have hnn := normSq_nonneg ((w - a * I - xs j) ^ 2 + (ys j : ℂ) ^ 2)
    have hpos : 0 < 8 * w.im * a * ((w.re - xs j) ^ 2 + w.im ^ 2 + a ^ 2 - ys j ^ 2) := by
      apply mul_pos (by positivity)
      nlinarith [sq_nonneg (w.re - xs j), hys j hj, sq_pos_of_pos hw]
    linarith
  have hpos : 0 < normSq (G.eval (w + a * I)) * normSq (H.eval (w + a * I)) :=
    mul_pos (normSq_pos.mpr hGne) (normSq_pos.mpr hHne)
  have hGH : normSq (G.eval (w - a * I)) * normSq (H.eval (w - a * I)) ≤
      normSq (G.eval (w + a * I)) * normSq (H.eval (w + a * I)) :=
    mul_le_mul hG hH (normSq_nonneg _) (normSq_nonneg _)
  have hq : normSq ((w + a * I - x) ^ 2 + (y : ℂ) ^ 2) ≤
      normSq ((w - a * I - x) ^ 2 + (y : ℂ) ^ 2) := by
    by_contra hcon
    replace hcon := lt_of_not_ge hcon
    have h1 := mul_le_mul_of_nonneg_left hGH (normSq_nonneg ((w - a * I - x) ^ 2 + (y : ℂ) ^ 2))
    have h2 := mul_lt_mul_of_pos_right hcon hpos
    nlinarith
  have hw' : w = ((w.re - x : ℝ) : ℂ) + x + (w.im : ℂ) * I := by
    apply Complex.ext <;> simp
  have key := normSq_pair_add_sub_normSq_pair_sub (w.re - x) w.im a y
  have e1 : ((w + a * I - x) ^ 2 + (y : ℂ) ^ 2) =
      ((((w.re - x : ℝ) : ℂ) + w.im * I + a * I) ^ 2 + (y : ℂ) ^ 2) := by
    conv_lhs => rw [hw']
    ring
  have e2 : ((w - a * I - x) ^ 2 + (y : ℂ) ^ 2) =
      ((((w.re - x : ℝ) : ℂ) + w.im * I - a * I) ^ 2 + (y : ℂ) ^ 2) := by
    conv_lhs => rw [hw']
    ring
  rw [← e1, ← e2] at key
  have hva : 0 < 8 * w.im * a := by positivity
  have : 8 * w.im * a * ((w.re - x) ^ 2 + w.im ^ 2 + a ^ 2 - y ^ 2) ≤ 0 := by linarith
  rcases mul_nonpos_iff.mp this with ⟨h, _⟩ | ⟨_, h⟩
  · linarith
  · linarith

/-- Pair factors in coordinates: `|q(w ± ia)|²` for `q = (z − x)² + y²`, as the two-point
difference `8·Im w·a((Re w − x)² + (Im w)² + a² − y²)`. -/
theorem normSq_pair_add_sub_sub (x y a : ℝ) (w : ℂ) :
    normSq ((w + a * I - x) ^ 2 + (y : ℂ) ^ 2) - normSq ((w - a * I - x) ^ 2 + (y : ℂ) ^ 2) =
      8 * w.im * a * ((w.re - x) ^ 2 + w.im ^ 2 + a ^ 2 - y ^ 2) := by
  have hw' : w = ((w.re - x : ℝ) : ℂ) + x + (w.im : ℂ) * I := by
    apply Complex.ext <;> simp
  have key := normSq_pair_add_sub_normSq_pair_sub (w.re - x) w.im a y
  have e1 : ((w + a * I - x) ^ 2 + (y : ℂ) ^ 2) =
      ((((w.re - x : ℝ) : ℂ) + w.im * I + a * I) ^ 2 + (y : ℂ) ^ 2) := by
    conv_lhs => rw [hw']
    ring
  have e2 : ((w - a * I - x) ^ 2 + (y : ℂ) ^ 2) =
      ((((w.re - x : ℝ) : ℂ) + w.im * I - a * I) ^ 2 + (y : ℂ) ^ 2) := by
    conv_lhs => rw [hw']
    ring
  rw [← e1, ← e2] at key
  exact key

/-- **Disc localisation for any number of pairs.** Let
`p = g·∏_{k∈s}((X − x_k)² + y_k²)` with `g ≠ 0` real-rooted and `s` nonempty, and `a > 0`.
Every root `w` of `(p(z + ia) + p(z − ia))/2` with `Im w > 0` lies in one of the closed discs
`(Re w − x_k)² + (Im w)² + a² ≤ y_k²`. -/
theorem exists_disc_of_shiftAvg_pairs_root {ι : Type*} {g : ℝ[X]} (hg0 : g ≠ 0)
    (hg : ∀ r ∈ (g.map ofRealHom).roots, r.im = 0) {s : Finset ι} (hs : s.Nonempty)
    (xs ys : ι → ℝ) {a : ℝ} (ha : 0 < a) {w : ℂ} (hw : 0 < w.im)
    (hroot : ((shiftAvg a (g * shallowPairs s xs ys)).map ofRealHom).eval w = 0) :
    ∃ k ∈ s, (w.re - xs k) ^ 2 + w.im ^ 2 + a ^ 2 ≤ ys k ^ 2 := by
  by_contra hcon
  push Not at hcon
  rw [eval_map_shiftAvg] at hroot
  set G := g.map ofRealHom
  have hmapmul : ((g * shallowPairs s xs ys).map ofRealHom) =
      G * (shallowPairs s xs ys).map ofRealHom := Polynomial.map_mul _
  rw [hmapmul, eval_mul, eval_mul, eval_map_shallowPairs, eval_map_shallowPairs] at hroot
  have hsum : G.eval (w + a * I) * ∏ k ∈ s, ((w + a * I - xs k) ^ 2 + (ys k : ℂ) ^ 2) =
      -(G.eval (w - a * I) * ∏ k ∈ s, ((w - a * I - xs k) ^ 2 + (ys k : ℂ) ^ 2)) := by
    linear_combination (2 : ℂ) * hroot
  have hn := congrArg normSq hsum
  rw [normSq_neg, map_mul, map_mul, map_prod, map_prod] at hn
  have hG := normSq_eval_sub_le_add_of_real_roots hg ha.le (w := w) hw.le
  have hGne : G.eval (w + a * I) ≠ 0 := by
    intro h0
    have hG0 : G ≠ 0 := (Polynomial.map_ne_zero_iff ofRealHom.injective).mpr hg0
    have := hg _ ((mem_roots hG0).mpr h0)
    simp only [add_im, mul_im, ofReal_re, I_im, ofReal_im, I_re, mul_zero, add_zero,
      mul_one] at this
    linarith
  have hGpos : 0 < normSq (G.eval (w + a * I)) := normSq_pos.mpr hGne
  -- Outside every disc, each pair factor strictly grows upward.
  have hlt : ∀ k ∈ s, normSq ((w - a * I - xs k) ^ 2 + (ys k : ℂ) ^ 2) <
      normSq ((w + a * I - xs k) ^ 2 + (ys k : ℂ) ^ 2) := by
    intro k hk
    have := normSq_pair_add_sub_sub (xs k) (ys k) a w
    have hpos : 0 < 8 * w.im * a * ((w.re - xs k) ^ 2 + w.im ^ 2 + a ^ 2 - ys k ^ 2) :=
      mul_pos (by positivity) (by linarith [hcon k hk])
    linarith
  by_cases hzero : ∃ k ∈ s, normSq ((w - a * I - xs k) ^ 2 + (ys k : ℂ) ^ 2) = 0
  · -- A vanishing lower factor forces an upper factor to vanish: `w + ia` is a root of a pair,
    -- which puts `w` inside that pair's disc.
    obtain ⟨k₀, hk₀, h0⟩ := hzero
    have hlow : normSq (G.eval (w - a * I)) *
        ∏ k ∈ s, normSq ((w - a * I - xs k) ^ 2 + (ys k : ℂ) ^ 2) = 0 := by
      rw [Finset.prod_eq_zero hk₀ h0, mul_zero]
    rw [hlow, mul_eq_zero] at hn
    rcases hn with h | h
    · exact absurd h hGpos.ne'
    · obtain ⟨j, hj, hj0⟩ := Finset.prod_eq_zero_iff.mp h
      have hq0 : (w + a * I - xs j) ^ 2 + (ys j : ℂ) ^ 2 = 0 := normSq_eq_zero.mp hj0
      -- `|q_j(w + ia)| = 0` and `|q_j(w − ia)| ≥ 0` give the disc inequality directly.
      have hd := normSq_pair_add_sub_sub (xs j) (ys j) a w
      rw [hj0] at hd
      have hnn := normSq_nonneg ((w - a * I - xs j) ^ 2 + (ys j : ℂ) ^ 2)
      have hva : 0 < 8 * w.im * a := by positivity
      have : 8 * w.im * a * ((w.re - xs j) ^ 2 + w.im ^ 2 + a ^ 2 - ys j ^ 2) ≤ 0 := by linarith
      rcases mul_nonpos_iff.mp this with ⟨h1, h2⟩ | ⟨h1, _⟩
      · linarith [hcon j hj]
      · linarith
  · push Not at hzero
    have hprod : ∏ k ∈ s, normSq ((w - a * I - xs k) ^ 2 + (ys k : ℂ) ^ 2) <
        ∏ k ∈ s, normSq ((w + a * I - xs k) ^ 2 + (ys k : ℂ) ^ 2) := by
      apply Finset.prod_lt_prod_of_nonempty
      · intro k hk
        exact lt_of_le_of_ne (normSq_nonneg _) (hzero k hk).symm
      · exact hlt
      · exact hs
    have hP : 0 ≤ ∏ k ∈ s, normSq ((w - a * I - xs k) ^ 2 + (ys k : ℂ) ^ 2) :=
      Finset.prod_nonneg fun k _ => normSq_nonneg _
    have h1 : normSq (G.eval (w - a * I)) *
        ∏ k ∈ s, normSq ((w - a * I - xs k) ^ 2 + (ys k : ℂ) ^ 2) ≤
        normSq (G.eval (w + a * I)) *
        ∏ k ∈ s, normSq ((w - a * I - xs k) ^ 2 + (ys k : ℂ) ^ 2) :=
      mul_le_mul_of_nonneg_right hG hP
    have h2 := mul_lt_mul_of_pos_left hprod hGpos
    linarith

end

end GaloisForLFunctions.HTGeometry
