import Mathlib.Tactic

/-!
# Affine correspondences of `ℤ` have genus zero

Over `𝔽_q` the spectrum of a curve is read from the fixed points of the iterates of one
correspondence, the Frobenius: `N_m = #Fix(F^m)` grows like `q^m` and its deviation is the
spectrum. The gauge-charged correspondences of `ℤ` are the affine maps `n ↦ an + b`. This file
computes their fixed-point theory and their intersections: both are trivial.

* **Iterates** (`affineIter_mul`). `(a − 1)(f^m(n) − n) = (a^m − 1)((a − 1)n + b)` for
  `f(n) = an + b`.
* **Expanding maps have at most one periodic point** (`affineIter_fixed_iff`). For `a ≥ 2` and
  `m ≥ 1`, `f^m(n) = n` iff `(a − 1)n + b = 0`: the only periodic point is the fixed point
  `−b/(a − 1)`, integral iff `(a − 1) ∣ b`. So `#Fix(f^m) ∈ {0, 1}` for every `m`
  (`fixedPoints_iter_subsingleton`), constant in `m`: the Lefschetz sequence of an affine map is
  `0` or `1`, its dynamical zeta function is `1` or `(1 − t)⁻¹`, and it has no spectrum.
* **The successor has no periodic points** (`translate_iter_ne`): `n + mb ≠ n` for `b ≠ 0`, `m ≥ 1`.
* **Two affine graphs meet at most once** (`affine_graphs_meet_at_most_once`). If
  `(a, b) ≠ (c, d)`, then `an + b = cn + d` has at most one integral solution.

So every intersection number between graphs of affine maps of `ℤ` is `0` or `1`, and no iterate
amplifies it: affine correspondences have genus zero and carry no budget. The arithmetic of
gauge-charged correspondences is not in the geometry of any single map; it enters only through
counts over families weighted by a source — the near-incidences `ab − cd = h` of ACG — that is,
through the source, never through a Lefschetz sequence. The spectral side of `ℤ` is read by the
dilations and the archimedean place.
-/

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

/-- The affine map `n ↦ an + b` of `ℤ`. -/
def affineMap (a b : ℤ) (n : ℤ) : ℤ := a * n + b

/-- **The iterate identity**: `(a − 1)(f^m(n) − n) = (a^m − 1)((a − 1)n + b)`. -/
theorem affineIter_mul (a b : ℤ) (m : ℕ) (n : ℤ) :
    (a - 1) * ((affineMap a b)^[m] n - n) = (a ^ m - 1) * ((a - 1) * n + b) := by
  induction m generalizing n with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    have h := ih n
    simp only [affineMap]
    have e : (a - 1) * (a * (affineMap a b)^[m] n + b - n) =
        a * ((a - 1) * ((affineMap a b)^[m] n - n)) + (a - 1) * ((a - 1) * n + b) := by ring
    rw [e, h]; ring

/-- **An expanding affine map has at most one periodic point**: for `a ≥ 2`, `m ≥ 1`,
`f^m(n) = n` iff `(a − 1)n + b = 0`. -/
theorem affineIter_fixed_iff {a : ℤ} (ha : 2 ≤ a) (b : ℤ) {m : ℕ} (hm : 1 ≤ m) (n : ℤ) :
    (affineMap a b)^[m] n = n ↔ (a - 1) * n + b = 0 := by
  have h := affineIter_mul a b m n
  have ha1 : a - 1 ≠ 0 := by omega
  have ham : a ^ m - 1 ≠ 0 := by
    have : 2 ^ m ≤ a ^ m := pow_le_pow_left₀ (by norm_num) ha m
    have : 2 ≤ 2 ^ m := by
      calc (2 : ℤ) = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) hm
    omega
  constructor
  · intro hf
    rw [hf, sub_self, mul_zero] at h
    exact (mul_eq_zero.mp h.symm).resolve_left ham
  · intro h0
    rw [h0, mul_zero] at h
    have := (mul_eq_zero.mp h).resolve_left ha1
    linarith

/-- **The Lefschetz numbers of an expanding affine map are `0` or `1`**: the fixed points of every
iterate form a subsingleton. -/
theorem fixedPoints_iter_subsingleton {a : ℤ} (ha : 2 ≤ a) (b : ℤ) {m : ℕ} (hm : 1 ≤ m) :
    {n : ℤ | (affineMap a b)^[m] n = n}.Subsingleton := by
  intro x hx y hy
  rw [Set.mem_setOf_eq, affineIter_fixed_iff ha b hm] at hx hy
  have : (a - 1) * (x - y) = 0 := by linarith
  have ha1 : a - 1 ≠ 0 := by omega
  linarith [(mul_eq_zero.mp this).resolve_left ha1]

/-- The periodic point exists iff `(a − 1) ∣ b`, and then it is fixed by every iterate. -/
theorem exists_fixed_iff {a : ℤ} (ha : 2 ≤ a) (b : ℤ) {m : ℕ} (hm : 1 ≤ m) :
    (∃ n, (affineMap a b)^[m] n = n) ↔ (a - 1) ∣ b := by
  simp only [affineIter_fixed_iff ha b hm]
  constructor
  · rintro ⟨n, hn⟩
    exact ⟨-n, by linarith⟩
  · rintro ⟨k, hk⟩
    exact ⟨-k, by rw [hk]; ring⟩

/-- **The successor has no periodic points.** -/
theorem translate_iter_ne {b : ℤ} (hb : b ≠ 0) {m : ℕ} (hm : 1 ≤ m) (n : ℤ) :
    (affineMap 1 b)^[m] n ≠ n := by
  have h : ∀ k : ℕ, (affineMap 1 b)^[k] n = n + k * b := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Function.iterate_succ_apply', ih, affineMap]; push_cast; ring
  rw [h]
  intro he
  have : (m : ℤ) * b = 0 := by linarith
  rcases mul_eq_zero.mp this with h0 | h0
  · omega
  · exact hb h0

/-- **Two distinct affine graphs meet at most once.** -/
theorem affine_graphs_meet_at_most_once {a b c d : ℤ} (h : (a, b) ≠ (c, d)) :
    {n : ℤ | affineMap a b n = affineMap c d n}.Subsingleton := by
  intro x hx y hy
  simp only [Set.mem_setOf_eq, affineMap] at hx hy
  have hxy : (a - c) * (x - y) = 0 := by linarith
  rcases mul_eq_zero.mp hxy with hac | hxy
  · exfalso
    have hac' : a = c := by linarith
    subst hac'
    have : b = d := by linarith
    exact h (by rw [this])
  · linarith

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
