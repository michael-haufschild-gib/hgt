import GaloisForLFunctions.HTGeometry.ShiftAverageNonrealCount
import GaloisForLFunctions.HTGeometry.PolynomialHeatFlow

/-!
# The cosine is the only even operator with a depth-resolved count of nonreal roots

For a real sequence `a` let `evenOp a = Σ_k (−1)^k a_k D^{2k}` act on real polynomials. On an
isolated pair `z² + x` it gives `z² + x − 2a₁`, so `h = √(2a₁)` is the depth below which a single
pair is absorbed. Say that `a` satisfies the *depth-resolved count law at threshold `h`* if for
every nonzero real polynomial `p`

  `#{nonreal roots of evenOp a p} ≤ 2·#{roots w of p : Im w > h}`

(`DepthCountLaw`). The cosine `cos(hD)`, with `a_k = h^{2k}/(2k)!`, satisfies it: on polynomials
it is the shift average `(p(z + ih) + p(z − ih))/2` (`shiftAvg_eq_evenOp_cosCoeff`), and the
shift average obeys the generalized Hermite–Biehler count (`nonrealRootCount_shiftAvg_le`).

**Theorem** (`eq_cosCoeff_of_depthCountLaw`). Conversely, if `a₀ = 1`, `a₁ = h²/2`, `h > 0` and `a`
satisfies the law at threshold `h`, then `a_k = h^{2k}/(2k)!` for every `k`. So the two-point
average is the only even operator of infinite order whose defects are counted by the zeros deeper
than its absorption depth.

**Proof.** By induction on `k`. If `a_j = h^{2j}/(2j)!` for `j < m`, then on a polynomial `p` of
degree `2m` the operator differs from the shift average by the constant
`κ = (−1)^m (a_m − h^{2m}/(2m)!)(2m)!` times the leading coefficient (`evenOp_eq_add_of_eq`).
* `m = 2`. For `p = (z² + h²)²` the shift average is `z²(z² − 4h²)`, so `κ < 0` gives the imaginary
  roots `±iy₀` of `y⁴ + 4h²y² + κ`, although no root of `p` is deeper than `h`. For
  `p = (z² + h²)(z² + 9h²)` it is `z²(z² + 4h²)`, so `κ > 0` leaves no real root: four nonreal
  roots against one deep pair.
* `m ≥ 3`. For `p = (z² + h²)^m` the shift average is `z^m((z + 2ih)^m + (z − 2ih)^m)/2`. With
  `κ ≠ 0` the polynomial `g = z^m(…) + κ` has `g(0) ≠ 0` while `g′` vanishes to order `m − 1 ≥ 2`
  at `0`. A real-rooted polynomial has no multiple critical point off its zero set
  (`rootMultiplicity_derivative_le_one_of_realRooted`, Rolle with multiplicities), so `g` has a
  nonreal root, although no root of `p` is deeper than `h`.

**Consequence** (`not_heat_depthCountLaw`). For every `t > 0` the heat flow `e^{−tD²}`
(`a_k = t^k/k!`) violates the law at its absorption depth `√(2t)`, since `t²/2 ≠ (2t)²/24`.
-/

open Polynomial Complex Finset

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- The even operator `Σ_k (−1)^k a_k D^{2k}` on real polynomials. -/
def evenOp (a : ℕ → ℝ) (p : ℝ[X]) : ℝ[X] :=
  ∑ k ∈ range (p.natDegree + 1), C ((-1) ^ k * a k) * derivative^[2 * k] p

/-- The Taylor coefficients `h^{2k}/(2k)!` of `cos(hz)`. -/
def cosCoeff (h : ℝ) (k : ℕ) : ℝ := h ^ (2 * k) / ((2 * k).factorial : ℝ)

/-- The depth-resolved count law at threshold `h`: the nonreal roots of `evenOp a p` are at most
twice the roots of `p` above height `h`. -/
def DepthCountLaw (a : ℕ → ℝ) (h : ℝ) : Prop :=
  ∀ p : ℝ[X], p ≠ 0 → nonrealRootCount (evenOp a p) ≤
    2 * Multiset.card ((p.map Complex.ofRealHom).roots.filter (fun w => h < w.im))

theorem cosCoeff_zero (h : ℝ) : cosCoeff h 0 = 1 := by simp [cosCoeff]

theorem cosCoeff_one (h : ℝ) : cosCoeff h 1 = h ^ 2 / 2 := by
  simp [cosCoeff, Nat.factorial]

/-! ## The operator on a longer range -/

theorem evenOp_eq_sum_of_le (a : ℕ → ℝ) {p : ℝ[X]} {N : ℕ} (hN : p.natDegree ≤ N) :
    evenOp a p = ∑ k ∈ range (N + 1), C ((-1) ^ k * a k) * derivative^[2 * k] p := by
  unfold evenOp
  refine Finset.sum_subset (range_subset_range.mpr (by omega)) fun k _ hk => ?_
  simp only [mem_range, not_lt] at hk
  rw [iterate_derivative_eq_zero (by omega), mul_zero]

/-- Two sequences that agree below a degree give the same operator on that degree, except at one
index `m`, whose contribution is `(−1)^m (a_m − b_m) D^{2m} p`. -/
theorem evenOp_eq_add_of_eq {a b : ℕ → ℝ} {p : ℝ[X]} {m : ℕ}
    (hab : ∀ k, k ≠ m → 2 * k ≤ p.natDegree → a k = b k) :
    evenOp a p = evenOp b p + C ((-1) ^ m * (a m - b m)) * derivative^[2 * m] p := by
  set N := max p.natDegree m with hN
  rw [evenOp_eq_sum_of_le a (le_max_left _ m), evenOp_eq_sum_of_le b (le_max_left _ m)]
  rw [← sub_eq_iff_eq_add', ← Finset.sum_sub_distrib]
  rw [Finset.sum_eq_single_of_mem m (mem_range.mpr (by omega))]
  · rw [← sub_mul, ← C_sub]
    ring_nf
  · intro k _ hkm
    by_cases hk : 2 * k ≤ p.natDegree
    · rw [hab k hkm hk, sub_self]
    · rw [iterate_derivative_eq_zero (by omega), mul_zero, mul_zero, sub_self]

/-- With `a₀ = 1` the operator keeps the degree. -/
theorem natDegree_evenOp {a : ℕ → ℝ} (h0 : a 0 = 1) (p : ℝ[X]) :
    (evenOp a p).natDegree = p.natDegree := by
  unfold evenOp
  rw [Finset.sum_range_succ']
  simp only [pow_zero, h0, mul_one, C_1, one_mul, mul_zero, Function.iterate_zero, id_eq]
  rcases Nat.eq_zero_or_pos p.natDegree with h | h
  · rw [h, Finset.sum_range_zero, zero_add, h]
  · rw [add_comm, natDegree_add_eq_left_of_natDegree_lt]
    refine lt_of_le_of_lt (natDegree_sum_le_of_forall_le _ _ (n := p.natDegree - 1)
      fun k _ => ?_) (by omega)
    refine (natDegree_C_mul_le _ _).trans ((natDegree_iterate_derivative _ _).trans ?_)
    omega

/-! ## The cosine on polynomials is the shift average -/

/-- Taylor's formula for complex polynomials, with the iterated derivatives. -/
theorem eval_add_eq_sum_iterate_derivative (q : ℂ[X]) (z c : ℂ) :
    q.eval (z + c) =
      ∑ n ∈ range (q.natDegree + 1), (derivative^[n] q).eval z * c ^ n / (n.factorial : ℂ) := by
  rw [show z + c = c + z by ring, ← taylor_eval, eval_eq_sum_range, natDegree_taylor]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [taylor_coeff]
  have h := congrArg (eval z) (congrFun (factorial_smul_hasseDeriv (R := ℂ) n) q)
  rw [LinearMap.smul_apply, eval_smul, nsmul_eq_mul] at h
  rw [← h]
  have hf : (n.factorial : ℂ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  field_simp

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ range (2 * n), f i = ∑ k ∈ range n, (f (2 * k) + f (2 * k + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih,
      Finset.sum_range_succ, add_assoc]

theorem ofReal_eval_eq (A : ℝ[X]) (x : ℝ) :
    ((A.eval x : ℝ) : ℂ) = (A.map Complex.ofRealHom).eval (x : ℂ) := by
  rw [eval_map, show (x : ℂ) = Complex.ofRealHom x from rfl, eval₂_at_apply]
  rfl

/-- **The cosine on polynomials.** `(p(z + ih) + p(z − ih))/2 = Σ_k (−1)^k h^{2k}/(2k)! p^{(2k)}`. -/
theorem shiftAvg_eq_evenOp_cosCoeff (h : ℝ) (p : ℝ[X]) :
    shiftAvg h p = evenOp (cosCoeff h) p := by
  refine Polynomial.funext fun x => ?_
  apply Complex.ofReal_injective
  rw [ofReal_eval_eq, eval_map_shiftAvg]
  set N := p.natDegree with hN
  set d : ℕ → ℂ := fun n => (((derivative^[n] p).eval x : ℝ) : ℂ) with hd
  have hdq : ∀ n, (derivative^[n] (p.map Complex.ofRealHom)).eval (x : ℂ) = d n := by
    intro n
    rw [iterate_derivative_map, ← ofReal_eval_eq]
  have hNC : (p.map Complex.ofRealHom).natDegree = N :=
    natDegree_map_eq_of_injective Complex.ofRealHom.injective p
  have hdz : ∀ n, N < n → d n = 0 := by
    intro n hn
    simp only [hd, iterate_derivative_eq_zero hn, eval_zero, Complex.ofReal_zero]
  have h1 := eval_add_eq_sum_iterate_derivative (p.map Complex.ofRealHom) (x : ℂ) (h * I)
  have h2 := eval_add_eq_sum_iterate_derivative (p.map Complex.ofRealHom) (x : ℂ) (-(h * I))
  rw [sub_eq_add_neg, h1, h2, hNC]
  simp only [hdq]
  -- the right side
  have hR : (((evenOp (cosCoeff h) p).eval x : ℝ) : ℂ) =
      ∑ k ∈ range (N + 1), (-1) ^ k * (cosCoeff h k : ℂ) * d (2 * k) := by
    rw [evenOp, eval_finsetSum, Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp [hd, eval_mul, eval_C]
  rw [hR]
  set e : ℕ → ℂ := fun n => d n * ((h * I) ^ n + (-(h * I)) ^ n) / 2 / (n.factorial : ℂ) with he
  have hsplit : (∑ n ∈ range (N + 1), d n * (↑h * I) ^ n / (n.factorial : ℂ) +
      ∑ n ∈ range (N + 1), d n * (-(↑h * I)) ^ n / (n.factorial : ℂ)) / 2 =
      ∑ n ∈ range (N + 1), e n := by
    rw [← Finset.sum_add_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [he]
    ring
  rw [hsplit]
  have hext : ∑ n ∈ range (N + 1), e n = ∑ n ∈ range (2 * (N + 1)), e n := by
    refine Finset.sum_subset (range_subset_range.mpr (by omega)) fun n _ hn => ?_
    simp only [mem_range, not_lt] at hn
    simp only [he, hdz n (by omega), zero_mul, zero_div]
  rw [hext, sum_range_two_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hodd : e (2 * k + 1) = 0 := by
    simp only [he]
    rw [neg_pow, pow_succ (-1 : ℂ), pow_mul (-1 : ℂ)]
    norm_num
  have hev : ((h : ℂ) * I) ^ (2 * k) = (-1) ^ k * (h : ℂ) ^ (2 * k) := by
    rw [mul_pow, pow_mul I, I_sq, mul_comm]
  rw [hodd, add_zero]
  simp only [he, neg_pow (↑h * I), pow_mul (-1 : ℂ), neg_one_sq, one_pow, one_mul, hev, cosCoeff]
  push_cast
  ring

/-! ## Rolle's theorem with multiplicities -/

theorem card_roots_eq_sum_rootMultiplicity (g : ℝ[X]) :
    Multiset.card g.roots = ∑ x ∈ g.roots.toFinset, rootMultiplicity x g := by
  classical
  rw [← Multiset.toFinset_sum_count_eq]
  exact Finset.sum_congr rfl fun x _ => count_roots g

/-- **A real-rooted polynomial has no multiple critical point off its zero set.** If all roots of
`g` are real, every root of `g′` at which `g` does not vanish is simple. -/
theorem rootMultiplicity_derivative_le_one_of_realRooted {g : ℝ[X]}
    (hreal : g.natDegree ≤ Multiset.card g.roots) {x₀ : ℝ} (hx : g.eval x₀ ≠ 0) :
    rootMultiplicity x₀ (derivative g) ≤ 1 := by
  classical
  by_contra H
  push Not at H
  set g' := derivative g with hg'
  have hg'0 : g' ≠ 0 := by
    intro h0
    rw [h0, rootMultiplicity_zero] at H
    omega
  have hdeg : g.natDegree ≠ 0 := by
    intro h0
    exact hg'0 (derivative_of_natDegree_zero h0)
  set S := g.roots.toFinset with hS
  set D := g'.roots.toFinset with hD
  have hmult : ∀ x ∈ S, rootMultiplicity x g ≤ rootMultiplicity x g' + 1 := fun x _ => by
    have := rootMultiplicity_sub_one_le_derivative_rootMultiplicity g x
    rw [← hg'] at this
    omega
  have hzero : ∀ x ∉ D, rootMultiplicity x g' = 0 := by
    intro x hx'
    rw [rootMultiplicity_eq_zero_iff]
    intro hroot
    exact absurd (Multiset.mem_toFinset.mpr ((mem_roots hg'0).mpr hroot)) hx'
  have hpos : ∀ x ∈ D, 1 ≤ rootMultiplicity x g' := by
    intro x hx'
    exact (rootMultiplicity_pos hg'0).mpr ((mem_roots hg'0).mp (Multiset.mem_toFinset.mp hx'))
  have hx₀D : x₀ ∈ D := by
    refine Multiset.mem_toFinset.mpr ((mem_roots hg'0).mpr ?_)
    exact (rootMultiplicity_pos hg'0).mp (by omega)
  have hx₀S : x₀ ∉ S := by
    intro hm
    exact hx ((mem_roots (fun h0 => by simp [h0] at hx)).mp (Multiset.mem_toFinset.mp hm))
  have hx₀DS : x₀ ∈ D \ S := Finset.mem_sdiff.mpr ⟨hx₀D, hx₀S⟩
  -- the sum over `S` only sees `S ∩ D`
  have hSsum : ∑ x ∈ S, rootMultiplicity x g' = ∑ x ∈ D ∩ S, rootMultiplicity x g' := by
    rw [← Finset.sum_inter_add_sum_sdiff S D, Finset.inter_comm]
    rw [Finset.sum_eq_zero (s := S \ D) fun x hx' => hzero x (Finset.mem_sdiff.mp hx').2, add_zero]
  -- the roots of `g′` off the zero set of `g`, with the double point `x₀`
  have hDS : (D \ S).card + 1 ≤ ∑ x ∈ D \ S, rootMultiplicity x g' := by
    rw [← Finset.add_sum_erase _ _ hx₀DS]
    have hrest : ((D \ S).erase x₀).card * 1 ≤ ∑ x ∈ (D \ S).erase x₀, rootMultiplicity x g' := by
      rw [← smul_eq_mul]
      exact Finset.card_nsmul_le_sum _ _ _ fun x hx' =>
        hpos x (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hx')).1
    have hc := Finset.card_erase_add_one hx₀DS
    omega
  have hrolle := card_roots_toFinset_le_card_roots_derivative_sdiff_roots_succ g
  have hgS : Multiset.card g.roots ≤ ∑ x ∈ S, rootMultiplicity x g' + S.card := by
    rw [card_roots_eq_sum_rootMultiplicity, Finset.card_eq_sum_ones, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum hmult
  have hg'D : Multiset.card g'.roots =
      ∑ x ∈ D ∩ S, rootMultiplicity x g' + ∑ x ∈ D \ S, rootMultiplicity x g' := by
    rw [card_roots_eq_sum_rootMultiplicity, Finset.sum_inter_add_sum_sdiff]
  have hlt : g'.natDegree < g.natDegree := natDegree_derivative_lt hdeg
  have hle := card_roots' g'
  rw [← hS, ← hD] at hrolle
  omega

/-! ## The quartic tests -/

theorem quartic_eq (u b : ℝ) :
    (X ^ 2 + C u) * (X ^ 2 + C b) = X ^ 4 + C (u + b) * X ^ 2 + C (u * b) := by
  rw [C_add, C_mul]
  ring

theorem natDegree_quarticTest (u b : ℝ) : ((X ^ 2 + C u) * (X ^ 2 + C b)).natDegree = 4 := by
  rw [quartic_eq]
  compute_degree!

theorem eval_iterate_derivative_quartic (s t : ℝ) (n : ℕ) (x : ℝ) :
    (derivative^[n] (X ^ 4 + C s * X ^ 2 + C t)).eval x =
      (Nat.descFactorial 4 n : ℝ) * x ^ (4 - n) + s * ((Nat.descFactorial 2 n : ℝ) * x ^ (2 - n)) +
        (if n = 0 then t else 0) := by
  rw [iterate_map_add, iterate_map_add, iterate_derivative_C_mul,
    iterate_derivative_X_pow_eq_smul, iterate_derivative_X_pow_eq_smul]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · rw [iterate_derivative_C hn]
    simp [hn.ne', Algebra.smul_def]

/-- On the quartic `(z² + u)(z² + b)` the operator only sees `a₀, a₁, a₂`. -/
theorem evenOp_quarticTest {a : ℕ → ℝ} {h : ℝ} (h0 : a 0 = 1) (h1 : a 1 = h ^ 2 / 2) (b : ℝ) :
    evenOp a ((X ^ 2 + C (h ^ 2)) * (X ^ 2 + C b)) =
      X ^ 4 + C (b - 5 * h ^ 2) * X ^ 2 + C (24 * a 2 - h ^ 4) := by
  refine Polynomial.funext fun x => ?_
  rw [evenOp, natDegree_quarticTest, eval_finsetSum, quartic_eq]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, eval_mul, eval_C,
    eval_iterate_derivative_quartic, eval_add, eval_pow, eval_X]
  norm_num [Nat.descFactorial, h0, h1]
  ring

/-! ## The power tests -/

theorem monic_X_sq_add_C (c : ℝ) : (X ^ 2 + C c).Monic := monic_X_pow_add_C c two_ne_zero

theorem natDegree_powerTest (c : ℝ) (m : ℕ) : ((X ^ 2 + C c) ^ m).natDegree = 2 * m := by
  rw [(monic_X_sq_add_C c).natDegree_pow, natDegree_X_pow_add_C, mul_comm]

theorem iterate_derivative_powerTest (c : ℝ) (m : ℕ) :
    derivative^[2 * m] ((X ^ 2 + C c) ^ m) = C (((2 * m).factorial : ℕ) : ℝ) := by
  set q := (X ^ 2 + C c) ^ m with hq
  have hdeg : (derivative^[2 * m] q).natDegree = 0 := by
    have := natDegree_iterate_derivative q (2 * m)
    rw [natDegree_powerTest] at this
    omega
  rw [eq_C_of_natDegree_eq_zero hdeg, coeff_iterate_derivative, zero_add, Nat.descFactorial_self]
  have hlead : q.coeff (2 * m) = 1 := by
    have := ((monic_X_sq_add_C c).pow m).leadingCoeff
    rwa [Polynomial.leadingCoeff, natDegree_powerTest] at this
  rw [hlead, nsmul_eq_mul, mul_one]

/-- The shift average of `(z² + h²)^m` is `z^m((z + 2ih)^m + (z − 2ih)^m)/2`, a multiple of `z^m`. -/
theorem X_pow_dvd_shiftAvg_powerTest (h : ℝ) (m : ℕ) : X ^ m ∣ shiftAvg h ((X ^ 2 + C (h ^ 2)) ^ m) := by
  rw [← map_dvd_map Complex.ofRealHom Complex.ofRealHom.injective (monic_X_pow m), map_shiftAvg,
    Polynomial.map_pow, map_X, shiftAvgC]
  simp only [Polynomial.map_pow, Polynomial.map_add, map_X, map_C, pow_comp, add_comp, X_comp,
    C_comp]
  have hplus : (X + C ((h : ℂ) * I)) ^ 2 + C (Complex.ofRealHom (h ^ 2)) =
      X * (X + C (2 * (h : ℂ) * I)) := by
    refine Polynomial.funext fun z => ?_
    simp only [eval_add, eval_pow, eval_X, eval_C, eval_mul, Complex.ofRealHom_eq_coe,
      Complex.ofReal_pow]
    linear_combination (h : ℂ) ^ 2 * I_sq
  have hminus : (X - C ((h : ℂ) * I)) ^ 2 + C (Complex.ofRealHom (h ^ 2)) =
      X * (X - C (2 * (h : ℂ) * I)) := by
    refine Polynomial.funext fun z => ?_
    simp only [eval_add, eval_sub, eval_pow, eval_X, eval_C, eval_mul, Complex.ofRealHom_eq_coe,
      Complex.ofReal_pow]
    linear_combination (h : ℂ) ^ 2 * I_sq
  rw [hplus, hminus, mul_pow, mul_pow]
  exact Dvd.intro (C (1 / 2 : ℂ) * ((X + C (2 * (h : ℂ) * I)) ^ m + (X - C (2 * (h : ℂ) * I)) ^ m))
    (by ring)

/-! ## Roots of the test polynomials -/

theorem map_X_sq_add_C_sq (s : ℝ) :
    (X ^ 2 + C (s ^ 2) : ℝ[X]).map Complex.ofRealHom = (X - C ((s : ℂ) * I)) * (X - C (-((s : ℂ) * I))) := by
  refine Polynomial.funext fun z => ?_
  simp only [Polynomial.map_add, Polynomial.map_pow, map_X, map_C, eval_add, eval_pow, eval_X,
    eval_C, eval_mul, eval_sub, Complex.ofRealHom_eq_coe, Complex.ofReal_pow]
  linear_combination (s : ℂ) ^ 2 * I_sq

theorem roots_map_X_sq_add_C_sq (s : ℝ) :
    ((X ^ 2 + C (s ^ 2) : ℝ[X]).map Complex.ofRealHom).roots = {(s : ℂ) * I, -((s : ℂ) * I)} := by
  rw [map_X_sq_add_C_sq, roots_mul (mul_ne_zero (X_sub_C_ne_zero _) (X_sub_C_ne_zero _)),
    roots_X_sub_C, roots_X_sub_C]
  rfl

theorem filter_roots_powerTest {h : ℝ} (hh : 0 < h) (m : ℕ) :
    (((X ^ 2 + C (h ^ 2)) ^ m : ℝ[X]).map Complex.ofRealHom).roots.filter (fun w => h < w.im) = 0 := by
  classical
  rw [Polynomial.map_pow, roots_pow, roots_map_X_sq_add_C_sq, Multiset.filter_nsmul]
  simp only [Multiset.insert_eq_cons, Multiset.filter_cons, Multiset.filter_singleton]
  simp [show ¬ h < -h by linarith]

theorem card_filter_roots_quarticTest {h : ℝ} (hh : 0 < h) :
    Multiset.card ((((X ^ 2 + C (h ^ 2)) * (X ^ 2 + C ((3 * h) ^ 2)) : ℝ[X]).map
      Complex.ofRealHom).roots.filter (fun w => h < w.im)) = 1 := by
  classical
  rw [Polynomial.map_mul, roots_mul (mul_ne_zero (Monic.ne_zero (by
      rw [map_X_sq_add_C_sq]; exact (monic_X_sub_C _).mul (monic_X_sub_C _)))
      (Monic.ne_zero (by rw [map_X_sq_add_C_sq]; exact (monic_X_sub_C _).mul (monic_X_sub_C _)))),
    roots_map_X_sq_add_C_sq, roots_map_X_sq_add_C_sq]
  simp only [Multiset.insert_eq_cons, Multiset.filter_add, Multiset.filter_cons,
    Multiset.filter_singleton]
  simp [show ¬ h < -h by linarith, show h < 3 * h by linarith, show ¬ h < -(3 * h) by linarith]

/-! ## The rigidity -/

theorem cosCoeff_two (h : ℝ) : cosCoeff h 2 = h ^ 4 / 24 := by
  simp [cosCoeff, Nat.factorial]

/-- The quartic tests pin the fourth Taylor coefficient. -/
theorem a_two_eq_of_depthCountLaw {a : ℕ → ℝ} {h : ℝ} (hh : 0 < h) (h0 : a 0 = 1)
    (h1 : a 1 = h ^ 2 / 2) (hlaw : DepthCountLaw a h) : a 2 = cosCoeff h 2 := by
  classical
  rw [cosCoeff_two]
  set κ := 24 * a 2 - h ^ 4 with hκ
  suffices hk : κ = 0 by linarith
  refine le_antisymm ?_ ?_
  · -- `κ > 0`: the quartic `z⁴ + 4h²z² + κ` has no real root, four nonreal roots against one deep pair
    by_contra hpos
    push Not at hpos
    set p := (X ^ 2 + C (h ^ 2)) * (X ^ 2 + C ((3 * h) ^ 2)) with hp
    have hp0 : p ≠ 0 := ((monic_X_sq_add_C _).mul (monic_X_sq_add_C _)).ne_zero
    have hg := evenOp_quarticTest h0 h1 ((3 * h) ^ 2)
    rw [← hp] at hg
    have hdeg : (evenOp a p).natDegree = 4 := by rw [natDegree_evenOp h0, natDegree_quarticTest]
    have hroots : (evenOp a p).roots = 0 := by
      refine Multiset.eq_zero_of_forall_notMem fun x hx => ?_
      have hne : evenOp a p ≠ 0 := fun h' => by rw [h', natDegree_zero] at hdeg; norm_num at hdeg
      have hr := (mem_roots hne).mp hx
      rw [IsRoot, hg] at hr
      simp only [eval_add, eval_mul, eval_pow, eval_X, eval_C] at hr
      nlinarith [sq_nonneg (x ^ 2), sq_nonneg x, sq_nonneg h]
    have hcount : nonrealRootCount (evenOp a p) = 4 := by
      rw [nonrealRootCount, hdeg, hroots]
      rfl
    have := hlaw p hp0
    rw [hcount, card_filter_roots_quarticTest hh] at this
    norm_num at this
  · -- `κ < 0`: the imaginary point `iy₀` is a root, although no root of `(z² + h²)²` is deep
    by_contra hneg
    push Not at hneg
    set p := (X ^ 2 + C (h ^ 2)) * (X ^ 2 + C (h ^ 2)) with hp
    have hp0 : p ≠ 0 := ((monic_X_sq_add_C _).mul (monic_X_sq_add_C _)).ne_zero
    have hg := evenOp_quarticTest h0 h1 (h ^ 2)
    rw [← hp] at hg
    have hdeg : (evenOp a p).natDegree = 4 := by rw [natDegree_evenOp h0, natDegree_quarticTest]
    have hne : evenOp a p ≠ 0 := fun h' => by rw [h', natDegree_zero] at hdeg; norm_num at hdeg
    -- the root `y₀` of `y⁴ + 4h²y² + κ`
    set f : ℝ → ℝ := fun y => y ^ 4 + 4 * h ^ 2 * y ^ 2 + κ with hf
    have hfc : Continuous f := by fun_prop
    set Y : ℝ := 1 - κ with hY
    have hY1 : 1 ≤ Y := by linarith
    have hfY : 0 ≤ f Y := by
      simp only [hf]
      nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hY1 3, sq_nonneg h, sq_nonneg Y,
        mul_nonneg (sq_nonneg h) (sq_nonneg Y)]
    obtain ⟨y₀, hy₀, hfy₀⟩ := intermediate_value_Icc (by linarith : (0 : ℝ) ≤ Y) hfc.continuousOn
      (show (0 : ℝ) ∈ Set.Icc (f 0) (f Y) from ⟨by simp [hf]; linarith, hfY⟩)
    have hy₀0 : y₀ ≠ 0 := by
      rintro rfl
      simp [hf] at hfy₀
      linarith
    have hroot : ((evenOp a p).map Complex.ofRealHom).IsRoot (I * y₀) := by
      rw [IsRoot, hg]
      simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_pow, map_X, map_C,
        eval_add, eval_mul, eval_pow, eval_X, eval_C, Complex.ofRealHom_eq_coe]
      have hfy : (y₀ : ℂ) ^ 4 + 4 * (h : ℂ) ^ 2 * (y₀ : ℂ) ^ 2 + (κ : ℂ) = 0 := by
        exact_mod_cast hfy₀
      push_cast
      rw [hκ] at hfy
      push_cast at hfy
      linear_combination hfy + ((y₀ : ℂ) ^ 4 * (I ^ 2 - 1) - 4 * (h : ℂ) ^ 2 * (y₀ : ℂ) ^ 2) * I_sq
    have hmem : I * y₀ ∈ ((evenOp a p).map Complex.ofRealHom).roots :=
      (mem_roots (Polynomial.map_ne_zero hne)).mpr hroot
    have hpos : 1 ≤ nonrealRootCount (evenOp a p) := by
      rw [nonrealRootCount_eq]
      exact Multiset.card_pos_iff_exists_mem.mpr ⟨_, Multiset.mem_filter.mpr ⟨hmem, by simpa using hy₀0⟩⟩
    have hfilt : (p.map Complex.ofRealHom).roots.filter (fun w => h < w.im) = 0 := by
      rw [hp, ← pow_two]
      exact filter_roots_powerTest hh 2
    have := hlaw p hp0
    rw [hfilt, Multiset.card_zero, mul_zero] at this
    omega

/-- The power tests pin every coefficient from the sixth on. -/
theorem a_eq_of_depthCountLaw_of_three_le {a : ℕ → ℝ} {h : ℝ} (hh : 0 < h) (h0 : a 0 = 1)
    (hlaw : DepthCountLaw a h) {m : ℕ} (hm : 3 ≤ m) (ih : ∀ k < m, a k = cosCoeff h k) :
    a m = cosCoeff h m := by
  classical
  set p := (X ^ 2 + C (h ^ 2)) ^ m with hp
  have hp0 : p ≠ 0 := ((monic_X_sq_add_C _).pow m).ne_zero
  have hpdeg : p.natDegree = 2 * m := natDegree_powerTest _ m
  set κ := (-1) ^ m * (a m - cosCoeff h m) * (((2 * m).factorial : ℕ) : ℝ) with hκ
  have hdecomp : evenOp a p = shiftAvg h p + C κ := by
    rw [evenOp_eq_add_of_eq (b := cosCoeff h) (m := m) fun k hkm hk => ih k (by omega),
      ← shiftAvg_eq_evenOp_cosCoeff, iterate_derivative_powerTest, ← C_mul]
  by_contra hne
  have hκ0 : κ ≠ 0 := by
    rw [hκ]
    refine mul_ne_zero (mul_ne_zero (pow_ne_zero _ (by norm_num)) (sub_ne_zero.mpr hne)) ?_
    exact_mod_cast (2 * m).factorial_ne_zero
  have hgdeg : (evenOp a p).natDegree = 2 * m := by rw [natDegree_evenOp h0, hpdeg]
  -- real-rootedness from the law: no root of `p` lies above height `h`
  have hfilt : (p.map Complex.ofRealHom).roots.filter (fun w => h < w.im) = 0 := by
    rw [hp]
    exact filter_roots_powerTest hh m
  have hreal : (evenOp a p).natDegree ≤ Multiset.card (evenOp a p).roots := by
    have := hlaw p hp0
    rw [hfilt, Multiset.card_zero, mul_zero] at this
    unfold nonrealRootCount at this
    omega
  -- `g(0) = κ`
  have hX : X ^ m ∣ shiftAvg h p := X_pow_dvd_shiftAvg_powerTest h m
  have heval : (evenOp a p).eval 0 = κ := by
    have h1 : X ∣ shiftAvg h p := (dvd_pow_self X (by omega)).trans hX
    have h2 := X_dvd_iff.mp h1
    rw [hdecomp, eval_add, eval_C, ← coeff_zero_eq_eval_zero, h2, zero_add]
  -- `g′` vanishes to order `m − 1` at `0`
  have hderiv : derivative (evenOp a p) = derivative (shiftAvg h p) := by
    rw [hdecomp, derivative_add, derivative_C, add_zero]
  have hg'0 : derivative (evenOp a p) ≠ 0 := by
    intro h'
    have := derivative_eq_zero.mp h'
    omega
  have hmult : m - 1 ≤ rootMultiplicity 0 (derivative (evenOp a p)) := by
    rw [le_rootMultiplicity_iff hg'0, C_0, sub_zero, hderiv]
    exact pow_sub_one_dvd_derivative_of_pow_dvd hX
  have hle := rootMultiplicity_derivative_le_one_of_realRooted hreal (x₀ := 0)
    (by rw [heval]; exact hκ0)
  omega

/-- **Rigidity of the cosine.** An even operator `Σ (−1)^k a_k D^{2k}` with `a₀ = 1` and absorption
depth `h = √(2a₁) > 0` whose nonreal roots are always counted by the roots deeper than `h` is
`cos(hD)`: `a_k = h^{2k}/(2k)!` for every `k`. -/
theorem eq_cosCoeff_of_depthCountLaw {a : ℕ → ℝ} {h : ℝ} (hh : 0 < h) (h0 : a 0 = 1)
    (h1 : a 1 = h ^ 2 / 2) (hlaw : DepthCountLaw a h) : a = cosCoeff h := by
  funext m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases m with _ | _ | _ | n
    · rw [h0, cosCoeff_zero]
    · rw [h1, cosCoeff_one]
    · exact a_two_eq_of_depthCountLaw hh h0 h1 hlaw
    · exact a_eq_of_depthCountLaw_of_three_le hh h0 hlaw (by omega) ih

/-- The cosine satisfies the law: on polynomials it is the shift average. -/
theorem depthCountLaw_cosCoeff (h : ℝ) : DepthCountLaw (cosCoeff h) h := fun p hp => by
  rw [← shiftAvg_eq_evenOp_cosCoeff]
  exact nonrealRootCount_shiftAvg_le hp h

/-- **The cosine is the only even operator with a depth-resolved count.** -/
theorem depthCountLaw_iff {a : ℕ → ℝ} {h : ℝ} (hh : 0 < h) :
    (a 0 = 1 ∧ a 1 = h ^ 2 / 2 ∧ DepthCountLaw a h) ↔ a = cosCoeff h := by
  constructor
  · rintro ⟨h0, h1, hlaw⟩
    exact eq_cosCoeff_of_depthCountLaw hh h0 h1 hlaw
  · rintro rfl
    exact ⟨cosCoeff_zero h, cosCoeff_one h, depthCountLaw_cosCoeff h⟩

/-! ## The heat flow -/

theorem polyHeat_eq_evenOp (t : ℝ) (p : ℝ[X]) :
    polyHeat t p = evenOp (fun k => t ^ k / (k.factorial : ℝ)) p := by
  unfold polyHeat evenOp
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [neg_pow]
  ring_nf

/-- **The heat flow has no depth-resolved count at any time.** For every `t > 0` some real
polynomial `p` has more nonreal roots after `e^{−tD²}` than twice its roots above the absorption
depth `√(2t)`. -/
theorem not_heat_depthCountLaw {t : ℝ} (ht : 0 < t) :
    ¬ ∀ p : ℝ[X], p ≠ 0 → nonrealRootCount (polyHeat t p) ≤
      2 * Multiset.card ((p.map Complex.ofRealHom).roots.filter
        (fun w => Real.sqrt (2 * t) < w.im)) := by
  intro hall
  have hlaw : DepthCountLaw (fun k => t ^ k / (k.factorial : ℝ)) (Real.sqrt (2 * t)) := by
    intro p hp
    rw [← polyHeat_eq_evenOp]
    exact hall p hp
  have hs : 0 < Real.sqrt (2 * t) := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt (2 * t) ^ 2 = 2 * t := Real.sq_sqrt (by linarith)
  have h1 : (fun k => t ^ k / (k.factorial : ℝ)) 1 = Real.sqrt (2 * t) ^ 2 / 2 := by
    rw [hsq]
    simp
  have h2 := congrFun (eq_cosCoeff_of_depthCountLaw hs (by simp) h1 hlaw) 2
  rw [cosCoeff_two, show Real.sqrt (2 * t) ^ 4 = (Real.sqrt (2 * t) ^ 2) ^ 2 by ring, hsq] at h2
  simp [Nat.factorial] at h2
  nlinarith

end

end GaloisForLFunctions.HTGeometry
