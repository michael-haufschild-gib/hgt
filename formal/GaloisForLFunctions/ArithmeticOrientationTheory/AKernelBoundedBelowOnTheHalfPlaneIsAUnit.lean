import GaloisForLFunctions.ArithmeticOrientationTheory.WienersLemmaOnTheBohrPolydisk
import GaloisForLFunctions.HTGeometry.PrimeTorusKroneckerDensity
import Mathlib.NumberTheory.SmoothNumbers
import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# A kernel bounded below on the half-plane is a unit

Wiener's lemma for `𝒲_σ` (`isUnit_iff_forall_bohrEval_ne_zero`) reads invertibility on the whole
Bohr polydisk, while the half-plane `Re s ≥ σ` reaches only the points `ω(p) = p^{σ−s}`, whose
radii are tied by one `Re s`.  The half-plane form of the lemma is nevertheless true once the bound
is uniform (`isUnit_iff_exists_le_norm_lSeries`):

  `f` is a unit of `𝒲_σ`  ⟺  `inf_{Re s ≥ σ} |L(f, s)| > 0`.

Proof of `⇐`, for the part `g` of `f` supported on `N`-smooth integers (the rest is a small tail):

1. **Tied tori** (`le_norm_bohrEval_of_onTorus`). Kronecker's theorem for `t log p`, `p ≤ N`
   (`primeTorus_cpow_dense`) steers the vertical line `Re s = σ + u` to every point with
   `|ω(p)| = p^{−u}`, so the bound holds there.
2. **Untying the radii** (`le_norm_bohrEval_of_inPolydisk`). On the polydisk `|ω(p)| ≤ p^{−u}`,
   if `ĝ` has no zero, the bound passes from the torus to the polydisk one prime at a time by the
   maximum modulus principle for `1/ĝ` in that coordinate.
3. **Radial descent** (`le_norm_bohrEval_of_smooth`). For large `u` the polydisk is so small that
   `ĝ ≈ g(1) ≠ 0`; shrinking every coordinate by `p^{−h}` moves `ĝ` by less than the bound, so
   zero-freeness, and with step 2 the bound, descends from `u` to `u − h`, down to `u = 0`.
-/

open Finset ArithmeticFunction LSeries Complex Filter Topology Metric

namespace GaloisForLFunctions.ArithmeticOrientationTheory

noncomputable section
set_option autoImplicit false

/-! ### Bohr points from prime values -/

theorem norm_list_prod_le_one {l : List ℂ} (h : ∀ x ∈ l, ‖x‖ ≤ 1) : ‖l.prod‖ ≤ 1 := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.prod_cons, norm_mul]
    exact mul_le_one₀ (h a (by simp)) (norm_nonneg _) (ih fun x hx => h x (by simp [hx]))

namespace BohrPoint

theorem apply_list_prod (ω : BohrPoint) (l : List ℕ) : ω.ω l.prod = (l.map ω.ω).prod := by
  induction l with
  | nil => simp [ω.map_one]
  | cons a l ih => rw [List.prod_cons, ω.map_mul, ih, List.map_cons, List.prod_cons]

/-- A Bohr point is the product of its prime values along the factorization. -/
theorem apply_eq_prod (ω : BohrPoint) {n : ℕ} (hn : n ≠ 0) :
    ω.ω n = (n.primeFactorsList.map ω.ω).prod := by
  conv_lhs => rw [← Nat.prod_primeFactorsList hn]
  exact ω.apply_list_prod _

/-- The Bohr point with prescribed values `v p` at the primes. -/
def ofPrimes (v : ℕ → ℂ) (hv : ∀ p, p.Prime → ‖v p‖ ≤ 1) : BohrPoint where
  ω n := if n = 0 then 0 else (n.primeFactorsList.map v).prod
  map_one := by simp
  map_mul m n := by
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn,
      ((Nat.perm_primeFactorsList_mul hm hn).map v).prod_eq, List.map_append, List.prod_append]
  norm_le_one n := by
    split_ifs
    · simp
    · refine norm_list_prod_le_one fun x hx => ?_
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
      exact hv p (Nat.prime_of_mem_primeFactorsList hp)

theorem ofPrimes_apply_prime {v : ℕ → ℂ} (hv : ∀ p, p.Prime → ‖v p‖ ≤ 1) {p : ℕ}
    (hp : p.Prime) : (ofPrimes v hv).ω p = v p := by
  simp [ofPrimes, hp.ne_zero, Nat.primeFactorsList_prime hp]

/-- Shrinking every coordinate: `ω(n) n^{−h}`, `h ≥ 0`. -/
def scale (ω : BohrPoint) {h : ℝ} (hh : 0 ≤ h) : BohrPoint where
  ω n := ω.ω n * (((n : ℝ) ^ (-h) : ℝ) : ℂ)
  map_one := by simp [ω.map_one]
  map_mul m n := by
    rw [ω.map_mul, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    push_cast; ring
  norm_le_one n := by
    have hr : 0 ≤ (n : ℝ) ^ (-h) := Real.rpow_nonneg (Nat.cast_nonneg _) _
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr]
    refine mul_le_one₀ (ω.norm_le_one n) hr ?_
    rcases eq_or_ne n 0 with rfl | hn
    · rw [Nat.cast_zero]; exact Real.zero_rpow_le_one _
    · exact Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn)
        (by linarith)

theorem scale_apply (ω : BohrPoint) {h : ℝ} (hh : 0 ≤ h) (n : ℕ) :
    (ω.scale hh).ω n = ω.ω n * (((n : ℝ) ^ (-h) : ℝ) : ℂ) := rfl

end BohrPoint

/-! ### Polydisks and tori over the primes below `N` -/

/-- `|ω(p)| ≤ p^{−u}` for every prime `p < N`. -/
def InPolydisk (N : ℕ) (u : ℝ) (ω : BohrPoint) : Prop :=
  ∀ p, p.Prime → p < N → ‖ω.ω p‖ ≤ (p : ℝ) ^ (-u)

/-- `|ω(p)| = p^{−u}` for every prime `p < N`. -/
def OnTorus (N : ℕ) (u : ℝ) (ω : BohrPoint) : Prop :=
  ∀ p, p.Prime → p < N → ‖ω.ω p‖ = (p : ℝ) ^ (-u)

theorem inPolydisk_zero (N : ℕ) (ω : BohrPoint) : InPolydisk N 0 ω := fun p _ _ => by
  simpa using ω.norm_le_one p

theorem inPolydisk_mono {N : ℕ} {u u' : ℝ} (h : u ≤ u') {ω : BohrPoint} (hω : InPolydisk N u' ω) :
    InPolydisk N u ω := fun p hp hpN =>
  (hω p hp hpN).trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hp.one_le) (by linarith))

theorem inPolydisk_scale {N : ℕ} {u h : ℝ} (hh : 0 ≤ h) {ω : BohrPoint} (hω : InPolydisk N u ω) :
    InPolydisk N (u + h) (ω.scale hh) := fun p hp hpN => by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  show ‖ω.ω p * (((p : ℝ) ^ (-h) : ℝ) : ℂ)‖ ≤ _
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hp0.le _),
    neg_add, Real.rpow_add hp0]
  exact mul_le_mul_of_nonneg_right (hω p hp hpN) (Real.rpow_nonneg hp0.le _)

/-- On the polydisk, `|ω(n)| ≤ n^{−u}` at the `N`-smooth integers. -/
theorem norm_apply_le_of_inPolydisk {N : ℕ} {u : ℝ} {ω : BohrPoint} (hω : InPolydisk N u ω)
    {n : ℕ} (hn : n ∈ Nat.smoothNumbers N) : ‖ω.ω n‖ ≤ (n : ℝ) ^ (-u) := by
  rw [Nat.mem_smoothNumbers] at hn
  have key : ∀ l : List ℕ, (∀ p ∈ l, p.Prime ∧ p < N) →
      ‖(l.map ω.ω).prod‖ ≤ ((l.prod : ℕ) : ℝ) ^ (-u) := by
    intro l
    induction l with
    | nil => simp
    | cons a l ih =>
      intro hl
      have ha := hl a (by simp)
      rw [List.map_cons, List.prod_cons, List.prod_cons, norm_mul, Nat.cast_mul,
        Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
      exact mul_le_mul (hω a ha.1 ha.2) (ih fun p hp => hl p (by simp [hp])) (norm_nonneg _)
        (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  rw [ω.apply_eq_prod hn.1]
  conv_rhs => rw [← Nat.prod_primeFactorsList hn.1]
  exact key _ fun p hp => ⟨Nat.prime_of_mem_primeFactorsList hp, hn.2 p hp⟩

/-! ### Step 2: the bound passes from the torus to the polydisk -/

/-- The Bohr evaluation with the value at `q` replaced by `z`, as a function of `z ∈ ℂ`. -/
def coordEval (σ : ℝ) (g : ArithmeticFunction ℂ) (ω : BohrPoint) (q : ℕ) (z : ℂ) : ℂ :=
  LSeries (fun n => g n * (n.primeFactorsList.map (Function.update ω.ω q z)).prod) σ

/-- The replaced point, for `|z| ≤ 1`. -/
def replace (ω : BohrPoint) (q : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) : BohrPoint :=
  BohrPoint.ofPrimes (Function.update ω.ω q z) fun p _ => by
    rcases eq_or_ne p q with rfl | h
    · simpa using hz
    · simpa [Function.update_of_ne h] using ω.norm_le_one p

theorem replace_apply_prime (ω : BohrPoint) (q : ℕ) {z : ℂ} (hz : ‖z‖ ≤ 1) {p : ℕ}
    (hp : p.Prime) : (replace ω q hz).ω p = Function.update ω.ω q z p :=
  BohrPoint.ofPrimes_apply_prime _ hp

theorem bohrEval_replace (σ : ℝ) (g : ArithmeticFunction ℂ) (ω : BohrPoint) (q : ℕ) {z : ℂ}
    (hz : ‖z‖ ≤ 1) : bohrEval σ g (replace ω q hz) = coordEval σ g ω q z := by
  unfold bohrEval coordEval
  refine LSeries_congr (fun {n} hn => ?_) _
  simp [replace, BohrPoint.ofPrimes, hn]

theorem coordEval_self (σ : ℝ) (g : ArithmeticFunction ℂ) (ω : BohrPoint) (q : ℕ) :
    coordEval σ g ω q (ω.ω q) = bohrEval σ g ω := by
  unfold bohrEval coordEval
  refine LSeries_congr (fun {n} hn => ?_) _
  rw [Function.update_eq_self, ω.apply_eq_prod hn]

theorem list_prod_update (w : ℕ → ℂ) (q : ℕ) (z : ℂ) (l : List ℕ) :
    (l.map (Function.update w q z)).prod =
      z ^ l.count q * (l.map fun p => if p = q then 1 else w p).prod := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rcases eq_or_ne a q with rfl | h
    · rw [List.map_cons, List.prod_cons, Function.update_self, ih, List.count_cons_self,
        List.map_cons, List.prod_cons, if_pos rfl, pow_succ]
      ring
    · rw [List.map_cons, List.prod_cons, Function.update_of_ne h, ih, List.count_cons_of_ne h,
        List.map_cons, List.prod_cons, if_neg h]
      ring

theorem norm_coordEval_term_le {σ : ℝ} (g : ArithmeticFunction ℂ) (ω : BohrPoint) (q n : ℕ)
    {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ‖term (fun n => g n * (n.primeFactorsList.map (Function.update ω.ω q z)).prod) σ n‖ ≤
      ‖term (⇑g) σ n‖ := by
  refine norm_term_le _ ?_
  rw [norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) (norm_list_prod_le_one fun x hx => ?_)
  obtain ⟨p, -, rfl⟩ := List.mem_map.1 hx
  rcases eq_or_ne p q with rfl | h
  · simpa using hz
  · simpa [Function.update_of_ne h] using ω.norm_le_one p

theorem differentiableOn_coordEval {σ : ℝ} {g : ArithmeticFunction ℂ}
    (hg : LSeriesSummable (⇑g) σ) (ω : BohrPoint) (q : ℕ) :
    DifferentiableOn ℂ (coordEval σ g ω q) (ball 0 1) := by
  unfold coordEval LSeries
  refine differentiableOn_tsum_of_summable_norm hg.norm (fun n => ?_) isOpen_ball
    fun n z hz => norm_coordEval_term_le g ω q n (mem_ball_zero_iff.1 hz).le
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [term_zero]; exact differentiableOn_const _
  simp only [term_of_ne_zero hn, list_prod_update]
  fun_prop

theorem continuousOn_coordEval {σ : ℝ} {g : ArithmeticFunction ℂ}
    (hg : LSeriesSummable (⇑g) σ) (ω : BohrPoint) (q : ℕ) :
    ContinuousOn (coordEval σ g ω q) (closedBall 0 1) := by
  unfold coordEval LSeries
  refine continuousOn_tsum (fun n => ?_) hg.norm
    fun n z hz => norm_coordEval_term_le g ω q n (mem_closedBall_zero_iff.1 hz)
  rcases eq_or_ne n 0 with rfl | hn
  · simp only [term_zero]; exact continuousOn_const
  simp only [term_of_ne_zero hn, list_prod_update]
  fun_prop

/-- **Minimum modulus in one coordinate**: a zero-free coordinate disk takes its least modulus on
the boundary circle. -/
theorem le_norm_coordEval {σ : ℝ} {g : ArithmeticFunction ℂ} (hg : LSeriesSummable (⇑g) σ)
    (ω : BohrPoint) (q : ℕ) {r δ : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) (hδ : 0 < δ)
    (hne : ∀ z ∈ closedBall (0 : ℂ) r, coordEval σ g ω q z ≠ 0)
    (hbd : ∀ z ∈ sphere (0 : ℂ) r, δ ≤ ‖coordEval σ g ω q z‖) {z₀ : ℂ}
    (hz₀ : z₀ ∈ closedBall (0 : ℂ) r) : δ ≤ ‖coordEval σ g ω q z₀‖ := by
  have hd : DiffContOnCl ℂ (fun z => (coordEval σ g ω q z)⁻¹) (ball 0 r) := by
    refine ⟨((differentiableOn_coordEval hg ω q).mono (ball_subset_ball hr1)).inv
      fun z hz => hne z (ball_subset_closedBall hz), ?_⟩
    rw [closure_ball _ hr0.ne']
    exact ((continuousOn_coordEval hg ω q).mono (closedBall_subset_closedBall hr1)).inv₀ hne
  have h := Complex.norm_le_of_forall_mem_frontier_norm_le isBounded_ball hd
    (C := δ⁻¹) (fun z hz => by
      rw [frontier_ball _ hr0.ne'] at hz
      rw [norm_inv]
      exact inv_anti₀ hδ (hbd z hz))
    (z := z₀) (by rwa [closure_ball _ hr0.ne'])
  rw [norm_inv] at h
  have hpos : 0 < ‖coordEval σ g ω q z₀‖ := norm_pos_iff.2 (hne z₀ hz₀)
  exact (inv_le_inv₀ hpos hδ).1 h

/-- **Untying the radii.**  If `ĝ` has no zero on the polydisk `|ω(p)| ≤ p^{−u}` (`p < N`) and
`|ĝ| ≥ δ` on its torus, then `|ĝ| ≥ δ` on the whole polydisk. -/
theorem le_norm_bohrEval_of_inPolydisk {σ : ℝ} {g : ArithmeticFunction ℂ}
    (hg : LSeriesSummable (⇑g) σ) {N : ℕ} {u δ : ℝ} (hu : 0 ≤ u) (hδ : 0 < δ)
    (hne : ∀ ω : BohrPoint, InPolydisk N u ω → bohrEval σ g ω ≠ 0)
    (htor : ∀ ω : BohrPoint, OnTorus N u ω → δ ≤ ‖bohrEval σ g ω‖) (ω : BohrPoint)
    (hω : InPolydisk N u ω) : δ ≤ ‖bohrEval σ g ω‖ := by
  -- Free the coordinates in `S` one at a time; the others stay on the torus.
  suffices H : ∀ S : Finset ℕ, ∀ ω : BohrPoint, InPolydisk N u ω →
      (∀ p, p.Prime → p < N → p ∉ S → ‖ω.ω p‖ = (p : ℝ) ^ (-u)) → δ ≤ ‖bohrEval σ g ω‖ from
    H (range N) ω hω fun p _ hpN hpS => absurd (mem_range.2 hpN) hpS
  intro S
  induction S using Finset.induction_on with
  | empty => exact fun ω _ hT => htor ω fun p hp hpN => hT p hp hpN (Finset.notMem_empty p)
  | @insert q S hqS ih =>
    intro ω hω hT
    by_cases hq : q.Prime ∧ q < N
    swap
    · refine ih ω hω fun p hp hpN hpS => hT p hp hpN ?_
      rw [mem_insert, not_or]
      exact ⟨fun h => hq (h ▸ ⟨hp, hpN⟩), hpS⟩
    have hq0 : (0 : ℝ) < q := by exact_mod_cast hq.1.pos
    have hr0 : 0 < (q : ℝ) ^ (-u) := Real.rpow_pos_of_pos hq0 _
    have hr1 : (q : ℝ) ^ (-u) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hq.1.one_le) (by linarith)
    have hz1 : ∀ z ∈ closedBall (0 : ℂ) ((q : ℝ) ^ (-u)), ‖z‖ ≤ 1 := fun z hz =>
      (mem_closedBall_zero_iff.1 hz).trans hr1
    have hpoly : ∀ z (hz : z ∈ closedBall (0 : ℂ) ((q : ℝ) ^ (-u))),
        InPolydisk N u (replace ω q (hz1 z hz)) := fun z hz p hp hpN => by
      rw [replace_apply_prime _ _ _ hp]
      rcases eq_or_ne p q with rfl | h
      · simpa using mem_closedBall_zero_iff.1 hz
      · rw [Function.update_of_ne h]; exact hω p hp hpN
    have key := le_norm_coordEval hg ω q hr0 hr1 hδ
      (fun z hz => by rw [← bohrEval_replace σ g ω q (hz1 z hz)]; exact hne _ (hpoly z hz))
      (fun z hz => by
        have hz' : z ∈ closedBall (0 : ℂ) ((q : ℝ) ^ (-u)) := sphere_subset_closedBall hz
        rw [← bohrEval_replace σ g ω q (hz1 z hz')]
        refine ih _ (hpoly z hz') fun p hp hpN hpS => ?_
        rw [replace_apply_prime _ _ _ hp]
        rcases eq_or_ne p q with rfl | h
        · simpa using mem_sphere_zero_iff_norm.1 hz
        · rw [Function.update_of_ne h]
          exact hT p hp hpN (by rw [mem_insert, not_or]; exact ⟨h, hpS⟩))
      (z₀ := ω.ω q) (mem_closedBall_zero_iff.2 (hω q hq.1 hq.2))
    rwa [coordEval_self] at key

/-! ### Step 1: Kronecker on the tied tori -/

theorem norm_list_prod_sub_le {a b : ℕ → ℂ} {ε : ℝ} (l : List ℕ)
    (ha : ∀ p ∈ l, ‖a p‖ ≤ 1) (hb : ∀ p ∈ l, ‖b p‖ ≤ 1) (hab : ∀ p ∈ l, ‖a p - b p‖ ≤ ε) :
    ‖(l.map a).prod - (l.map b).prod‖ ≤ l.length * ε := by
  induction l with
  | nil => simp
  | cons x l ih =>
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    have h1 := ih (fun p hp => ha p (by simp [hp])) (fun p hp => hb p (by simp [hp]))
      (fun p hp => hab p (by simp [hp]))
    have hB : ‖(l.map b).prod‖ ≤ 1 := norm_list_prod_le_one fun y hy => by
      obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hy; exact hb p (by simp [hp])
    calc ‖a x * (l.map a).prod - b x * (l.map b).prod‖
        = ‖a x * ((l.map a).prod - (l.map b).prod) + (a x - b x) * (l.map b).prod‖ := by
          congr 1; ring
      _ ≤ 1 * (l.length * ε) + ε * 1 := by
          refine (norm_add_le _ _).trans (add_le_add ?_ ?_) <;> rw [norm_mul]
          · exact mul_le_mul (ha x (by simp)) h1 (norm_nonneg _) zero_le_one
          · exact mul_le_mul (hab x (by simp)) hB (norm_nonneg _)
              ((norm_nonneg _).trans (hab x (by simp)))
      _ = ((l.length + 1 : ℕ) : ℝ) * ε := by push_cast; ring

/-- **The bound on the tied tori.**  For `g` supported on `N`-smooth integers, a lower bound for
`L(g, s)` on `Re s ≥ σ` holds at every point with `|ω(p)| = p^{−u}`: Kronecker's theorem steers the
line `Re s = σ + u` to it. -/
theorem le_norm_bohrEval_of_onTorus {σ : ℝ} {g : ArithmeticFunction ℂ}
    (hg : LSeriesSummable (⇑g) σ) {N : ℕ} (hgN : ∀ n, n ∉ Nat.smoothNumbers N → g n = 0)
    {u δ : ℝ} (hu : 0 ≤ u) (hhalf : ∀ s : ℂ, σ ≤ s.re → δ ≤ ‖LSeries (⇑g) s‖) (ω : BohrPoint)
    (hω : OnTorus N u ω) : δ ≤ ‖bohrEval σ g ω‖ := by
  -- Phases of `ω` at the primes `≤ N`, and times steering `p^{it}` to them.
  have hK : ∀ j : ℕ, ∃ t : ℝ, ∀ p : primesLE N,
      ‖(((p : Nat.Primes) : ℕ) : ℂ) ^ ((t : ℂ) * I) -
        exp ((arg (ω.ω ((p : Nat.Primes) : ℕ)) : ℝ) * I)‖ < 1 / ((j : ℝ) + 1) := fun j =>
    primeTorus_cpow_dense N (fun p => arg (ω.ω ((p : Nat.Primes) : ℕ))) (by positivity)
  choose t ht using hK
  have hs : ∀ j : ℕ, σ ≤ ((σ + u : ℝ) - (t j : ℂ) * I : ℂ).re := fun j => by simp; linarith
  set ωj : ℕ → BohrPoint := fun j => WienerAlgebraAt.halfPlanePoint σ _ (hs j)
  -- At the primes below `N` the points `ωj` converge to `ω`.
  have hprime : ∀ j : ℕ, ∀ p, p.Prime → p < N → ‖(ωj j).ω p - ω.ω p‖ ≤ 1 / ((j : ℝ) + 1) := by
    intro j p hp hpN
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hmem : (⟨p, hp⟩ : Nat.Primes) ∈ primesLE N := (mem_primesLE N _).2 hpN.le
    have h1 := ht j ⟨⟨p, hp⟩, hmem⟩
    simp only at h1
    have hωp : ω.ω p = (((p : ℝ) ^ (-u) : ℝ) : ℂ) * exp ((arg (ω.ω p) : ℝ) * I) := by
      rw [← hω p hp hpN]; exact (norm_mul_exp_arg_mul_I _).symm
    have hjp : (ωj j).ω p = (((p : ℝ) ^ (-u) : ℝ) : ℂ) * (p : ℂ) ^ ((t j : ℂ) * I) := by
      simp only [ωj, WienerAlgebraAt.halfPlanePoint, hp.ne_zero, if_false]
      have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
      rw [show (σ : ℂ) - ((σ + u : ℝ) - (t j : ℂ) * I) = (-u : ℝ) + (t j : ℂ) * I by
          push_cast; ring, cpow_add _ _ hpc, ← ofReal_natCast, ← ofReal_cpow hp0.le]
    rw [hjp, hωp, ← mul_sub, norm_mul, norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hp0.le _)]
    calc (p : ℝ) ^ (-u) * _ ≤ 1 * (1 / ((j : ℝ) + 1)) :=
          mul_le_mul (Real.rpow_le_one_of_one_le_of_nonpos (by exact_mod_cast hp.one_le)
            (by linarith)) h1.le (norm_nonneg _) zero_le_one
      _ = _ := one_mul _
  -- Termwise convergence and domination give convergence of the Bohr evaluations.
  have hlim : Tendsto (fun j => bohrEval σ g (ωj j)) atTop (𝓝 (bohrEval σ g ω)) := by
    unfold bohrEval LSeries
    refine tendsto_tsum_of_dominated_convergence hg.norm (fun n => ?_)
      (Eventually.of_forall fun j n => norm_term_le _ (by
        rw [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) ((ωj j).norm_le_one n)))
    rcases eq_or_ne n 0 with rfl | hn
    · simp only [term_zero]; exact tendsto_const_nhds
    by_cases hsm : n ∈ Nat.smoothNumbers N
    swap
    · simp only [term_of_ne_zero hn, hgN n hsm, zero_mul, zero_div]; exact tendsto_const_nhds
    simp only [term_of_ne_zero hn]
    refine Tendsto.div_const (Tendsto.const_mul _ ?_) _
    rw [tendsto_iff_norm_sub_tendsto_zero]
    have hfac : ∀ p ∈ n.primeFactorsList, p.Prime ∧ p < N := fun p hp =>
      ⟨Nat.prime_of_mem_primeFactorsList hp, (Nat.mem_smoothNumbers.1 hsm).2 p hp⟩
    have hb : Tendsto (fun j : ℕ => (n.primeFactorsList.length : ℝ) * (1 / ((j : ℝ) + 1))) atTop
        (𝓝 0) := by
      simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul
        (n.primeFactorsList.length : ℝ)
    refine squeeze_zero (fun _ => norm_nonneg _) (fun j => ?_) hb
    rw [(ωj j).apply_eq_prod hn, ω.apply_eq_prod hn]
    exact norm_list_prod_sub_le _ (fun p _ => (ωj j).norm_le_one p) (fun p _ => ω.norm_le_one p)
      fun p hp => hprime j p (hfac p hp).1 (hfac p hp).2
  refine ge_of_tendsto (hlim.norm) (Eventually.of_forall fun j => ?_)
  rw [WienerAlgebraAt.bohrEval_halfPlanePoint]
  exact hhalf _ (hs j)

/-! ### Step 3: radial descent -/

theorem one_sub_rpow_neg_mem (n : ℕ) {h : ℝ} (hh : 0 ≤ h) :
    0 ≤ 1 - (n : ℝ) ^ (-h) ∧ 1 - (n : ℝ) ^ (-h) ≤ 1 := by
  have h0 : 0 ≤ (n : ℝ) ^ (-h) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine ⟨?_, by linarith⟩
  rcases eq_or_ne n 0 with rfl | hn
  · rw [Nat.cast_zero]; linarith [Real.zero_rpow_le_one (-h)]
  · linarith [Real.rpow_le_one_of_one_le_of_nonpos
      (by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn : (1 : ℝ) ≤ n) (by linarith : -h ≤ 0)]

theorem summable_scaleDefect {σ : ℝ} {g : ArithmeticFunction ℂ} (hg : LSeriesSummable (⇑g) σ)
    {h : ℝ} (hh : 0 ≤ h) : Summable fun n : ℕ => ‖term (⇑g) σ n‖ * (1 - (n : ℝ) ^ (-h)) :=
  hg.norm.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (one_sub_rpow_neg_mem n hh).1)
    fun n => mul_le_of_le_one_right (norm_nonneg _) (one_sub_rpow_neg_mem n hh).2

/-- Shrinking every coordinate by `n^{−h}` moves the Bohr evaluation by at most
`Σ |g(n)| n^{−σ} (1 − n^{−h})`, uniformly in the point. -/
theorem norm_bohrEval_sub_scale_le {σ : ℝ} {g : ArithmeticFunction ℂ}
    (hg : LSeriesSummable (⇑g) σ) (ω : BohrPoint) {h : ℝ} (hh : 0 ≤ h) :
    ‖bohrEval σ g ω - bohrEval σ g (ω.scale hh)‖ ≤
      ∑' n : ℕ, ‖term (⇑g) σ n‖ * (1 - (n : ℝ) ^ (-h)) := by
  unfold bohrEval LSeries
  rw [← (lSeriesSummable_twist hg ω).tsum_sub (lSeriesSummable_twist hg (ω.scale hh))]
  refine tsum_of_norm_bounded (summable_scaleDefect hg hh).hasSum fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hb := one_sub_rpow_neg_mem n hh
  rw [term_of_ne_zero hn, term_of_ne_zero hn, term_of_ne_zero hn, ← sub_div, norm_div, norm_div,
    BohrPoint.scale_apply, show g n * ω.ω n - g n * (ω.ω n * (((n : ℝ) ^ (-h) : ℝ) : ℂ)) =
      g n * ω.ω n * ((1 - (n : ℝ) ^ (-h) : ℝ) : ℂ) by push_cast; ring, norm_mul, norm_mul,
    norm_real, Real.norm_eq_abs, abs_of_nonneg hb.1, div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_of_le_one_right (norm_nonneg _) (ω.norm_le_one n)) hb.1) (norm_nonneg _)

theorem exists_scaleDefect_lt {σ : ℝ} {g : ArithmeticFunction ℂ} (hg : LSeriesSummable (⇑g) σ)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ h : ℝ, 0 < h ∧ ∑' n : ℕ, ‖term (⇑g) σ n‖ * (1 - (n : ℝ) ^ (-h)) < δ := by
  have hj : ∀ j : ℕ, (0 : ℝ) ≤ 1 / ((j : ℝ) + 1) := fun j => by positivity
  have hlim : Tendsto (fun j : ℕ => ∑' n : ℕ, ‖term (⇑g) σ n‖ * (1 - (n : ℝ) ^ (-(1 / ((j : ℝ) + 1)))))
      atTop (𝓝 (∑' _ : ℕ, (0 : ℝ))) := by
    refine tendsto_tsum_of_dominated_convergence hg.norm (fun n => ?_)
      (Eventually.of_forall fun j n => ?_)
    · rcases eq_or_ne n 0 with rfl | hn
      · simp
      have h0 : Tendsto (fun j : ℕ => -(1 / ((j : ℝ) + 1))) atTop (𝓝 0) := by
        simpa using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).neg
      have h1 : Tendsto (fun j : ℕ => (n : ℝ) ^ (-(1 / ((j : ℝ) + 1)))) atTop (𝓝 1) := by
        have := (Real.continuousAt_const_rpow (a := (n : ℝ)) (b := 0)
          (Nat.cast_ne_zero.2 hn)).tendsto.comp h0
        simpa [Function.comp_def] using this
      simpa using (h1.const_sub 1).const_mul ‖term (⇑g) σ n‖
    · have hb := one_sub_rpow_neg_mem n (hj j)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) hb.1)]
      exact mul_le_of_le_one_right (norm_nonneg _) hb.2
  rw [tsum_zero] at hlim
  obtain ⟨j, hj'⟩ := (hlim.eventually (gt_mem_nhds hδ)).exists
  exact ⟨1 / ((j : ℝ) + 1), by positivity, hj'⟩

/-- **The half-plane Wiener lemma for smooth kernels.**  For `g` supported on `N`-smooth integers, a
uniform lower bound for `L(g, s)` on `Re s ≥ σ` holds at every point of the Bohr polydisk. -/
theorem le_norm_bohrEval_of_smooth {σ : ℝ} {g : ArithmeticFunction ℂ}
    (hg : LSeriesSummable (⇑g) σ) {N : ℕ} (hgN : ∀ n, n ∉ Nat.smoothNumbers N → g n = 0)
    {δ : ℝ} (hδ : 0 < δ) (hhalf : ∀ s : ℂ, σ ≤ s.re → δ ≤ ‖LSeries (⇑g) s‖) (ω : BohrPoint) :
    δ ≤ ‖bohrEval σ g ω‖ := by
  have hstep : ∀ u, 0 ≤ u → (∀ ω, InPolydisk N u ω → bohrEval σ g ω ≠ 0) →
      ∀ ω, InPolydisk N u ω → δ ≤ ‖bohrEval σ g ω‖ := fun u hu hne =>
    le_norm_bohrEval_of_inPolydisk hg hu hδ hne fun ω hω =>
      le_norm_bohrEval_of_onTorus hg hgN hu hhalf ω hω
  -- Base: on a small polydisk `ĝ` is within `δ` of its value at a real half-plane point.
  set G := ∑' n : ℕ, ‖term (⇑g) σ n‖
  obtain ⟨m, hm⟩ := pow_unbounded_of_one_lt (2 * G / δ) (by norm_num : (1 : ℝ) < 2)
  have h2m : (0 : ℝ) < 2 ^ m := by positivity
  have hsmall : ∀ ω, InPolydisk N m ω → ∀ n, n ∈ Nat.smoothNumbers N → 2 ≤ n →
      ‖ω.ω n‖ ≤ ((2 : ℝ) ^ m)⁻¹ := fun ω hω n hn hn2 => by
    refine (norm_apply_le_of_inPolydisk hω hn).trans ?_
    rw [← Real.rpow_natCast, ← Real.rpow_neg (by norm_num)]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast hn2) (by simp)
  have hs0 : σ ≤ ((σ + m : ℝ) : ℂ).re := by simp
  set ω₀ := WienerAlgebraAt.halfPlanePoint σ _ hs0
  have hω₀ : InPolydisk N m ω₀ := fun p hp _ => le_of_eq (by
    simp only [ω₀, WienerAlgebraAt.halfPlanePoint, hp.ne_zero, if_false]
    rw [norm_natCast_cpow_of_pos hp.pos]
    congr 1; simp)
  have hbase : ∀ ω, InPolydisk N m ω → bohrEval σ g ω ≠ 0 := by
    intro ω hω h0
    have hd : ‖bohrEval σ g ω - bohrEval σ g ω₀‖ ≤ G * (2 * ((2 : ℝ) ^ m)⁻¹) := by
      unfold bohrEval LSeries
      rw [← (lSeriesSummable_twist hg ω).tsum_sub (lSeriesSummable_twist hg ω₀)]
      refine tsum_of_norm_bounded (hg.norm.hasSum.mul_right _) fun n => ?_
      rcases eq_or_ne n 0 with rfl | hn
      · simp
      by_cases hsm : n ∈ Nat.smoothNumbers N
      swap
      · simp [term_of_ne_zero hn, hgN n hsm]
      rw [term_of_ne_zero hn, term_of_ne_zero hn, term_of_ne_zero hn, ← sub_div, norm_div,
        norm_div, ← mul_sub, norm_mul, mul_div_right_comm]
      refine mul_le_mul_of_nonneg_left ?_ (div_nonneg (norm_nonneg _) (norm_nonneg _))
      rcases eq_or_ne n 1 with rfl | hn1
      · rw [ω.map_one, ω₀.map_one, sub_self, norm_zero]; positivity
      have hn2 : 2 ≤ n := by omega
      exact (norm_sub_le _ _).trans (by linarith [hsmall ω hω n hsm hn2, hsmall ω₀ hω₀ n hsm hn2])
    rw [h0, zero_sub, norm_neg, WienerAlgebraAt.bohrEval_halfPlanePoint] at hd
    have h1 := hhalf _ hs0
    have hlt : G * (2 * ((2 : ℝ) ^ m)⁻¹) < δ := by
      have e : G * (2 * ((2 : ℝ) ^ m)⁻¹) = 2 * G / 2 ^ m := by field_simp
      rw [e, div_lt_iff₀ h2m]
      have := (div_lt_iff₀ hδ).1 hm
      linarith
    linarith
  -- Descent: shrinking by `p^{−h}` moves `ĝ` by less than `δ`, so zero-freeness descends by `h`.
  obtain ⟨h, hh, hD⟩ := exists_scaleDefect_lt hg hδ
  have hdesc : ∀ k : ℕ, ∀ u, 0 ≤ u → (m : ℝ) - k * h ≤ u →
      ∀ ω, InPolydisk N u ω → δ ≤ ‖bohrEval σ g ω‖ := by
    intro k
    induction k with
    | zero =>
      intro u hu hku
      exact hstep u hu fun ω' hω' => hbase ω' (inPolydisk_mono (by simpa using hku) hω')
    | succ k ih =>
      intro u hu hku
      refine hstep u hu fun ω' hω' h0 => ?_
      have h1 := ih (u + h) (by linarith) (by push_cast at hku; linarith) _
        (inPolydisk_scale hh.le hω')
      have h2 := norm_bohrEval_sub_scale_le hg ω' hh.le
      rw [h0, zero_sub, norm_neg] at h2
      linarith
  obtain ⟨k, hk⟩ := exists_nat_gt ((m : ℝ) / h)
  exact hdesc k 0 le_rfl (by rw [div_lt_iff₀ hh] at hk; linarith) ω (inPolydisk_zero N ω)

/-! ### Step 4: truncation to smooth kernels -/

/-- The `N`-smooth part of an arithmetic function. -/
def smoothPart (N : ℕ) (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  ⟨fun n => if n ∈ Nat.smoothNumbers N then f n else 0, by simp [Nat.mem_smoothNumbers]⟩

theorem smoothPart_apply (N : ℕ) (f : ArithmeticFunction ℂ) (n : ℕ) :
    smoothPart N f n = if n ∈ Nat.smoothNumbers N then f n else 0 := rfl

/-- The mass of `f` off the `N`-smooth integers. -/
def smoothTail (σ : ℝ) (f : ArithmeticFunction ℂ) (N : ℕ) : ℝ :=
  ∑' n : ℕ, ‖term (⇑f) σ n‖ * (if n ∈ Nat.smoothNumbers N then 0 else 1)

theorem summable_smoothTail {σ : ℝ} {f : ArithmeticFunction ℂ} (hf : LSeriesSummable (⇑f) σ)
    (N : ℕ) : Summable fun n : ℕ => ‖term (⇑f) σ n‖ * (if n ∈ Nat.smoothNumbers N then 0 else 1) :=
  hf.norm.of_nonneg_of_le (fun n => mul_nonneg (norm_nonneg _) (by split_ifs <;> norm_num))
    fun n => mul_le_of_le_one_right (norm_nonneg _) (by split_ifs <;> norm_num)

theorem lSeriesSummable_smoothPart {σ : ℝ} {f : ArithmeticFunction ℂ}
    (hf : LSeriesSummable (⇑f) σ) (N : ℕ) : LSeriesSummable (⇑(smoothPart N f)) σ := by
  rw [← summable_norm_term_iff] at hf ⊢
  exact hf.of_nonneg_of_le (fun _ => norm_nonneg _) fun n => norm_term_le _ (by
    rw [smoothPart_apply]; split_ifs <;> simp)

theorem norm_bohrEval_sub_smoothPart_le {σ : ℝ} {f : ArithmeticFunction ℂ}
    (hf : LSeriesSummable (⇑f) σ) (N : ℕ) (ω : BohrPoint) :
    ‖bohrEval σ f ω - bohrEval σ (smoothPart N f) ω‖ ≤ smoothTail σ f N := by
  unfold bohrEval LSeries smoothTail
  rw [← (lSeriesSummable_twist hf ω).tsum_sub
    (lSeriesSummable_twist (lSeriesSummable_smoothPart hf N) ω)]
  refine tsum_of_norm_bounded (summable_smoothTail hf N).hasSum fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [term_of_ne_zero hn, term_of_ne_zero hn, term_of_ne_zero hn, ← sub_div, smoothPart_apply]
  split_ifs with hsm
  · simp
  · rw [zero_mul, sub_zero, mul_one, norm_div, norm_div, norm_mul]
    exact div_le_div_of_nonneg_right (mul_le_of_le_one_right (norm_nonneg _) (ω.norm_le_one n))
      (norm_nonneg _)

theorem tendsto_smoothTail {σ : ℝ} {f : ArithmeticFunction ℂ} (hf : LSeriesSummable (⇑f) σ) :
    Tendsto (smoothTail σ f) atTop (𝓝 0) := by
  have h := tendsto_tsum_of_dominated_convergence (𝓕 := atTop) (g := fun _ : ℕ => (0 : ℝ))
    (f := fun N n => ‖term (⇑f) σ n‖ * (if n ∈ Nat.smoothNumbers N then 0 else 1)) hf.norm
    (fun n => ?_) (Eventually.of_forall fun N n => ?_)
  · rw [tsum_zero] at h
    exact h
  · refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop n] with N hN
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    rw [if_pos (Nat.mem_smoothNumbers_of_lt (Nat.pos_of_ne_zero hn) hN), mul_zero]
  · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (by split_ifs <;> norm_num))]
    exact mul_le_of_le_one_right (norm_nonneg _) (by split_ifs <;> norm_num)

/-- **A uniform lower bound on the half-plane holds on the Bohr polydisk.** -/
theorem le_norm_bohrEval_of_le_norm_lSeries {σ : ℝ} {f : ArithmeticFunction ℂ}
    (hf : LSeriesSummable (⇑f) σ) {δ : ℝ} (hδ : 0 < δ)
    (hhalf : ∀ s : ℂ, σ ≤ s.re → δ ≤ ‖LSeries (⇑f) s‖) (ω : BohrPoint) :
    δ ≤ ‖bohrEval σ f ω‖ := by
  have hτ := tendsto_smoothTail hf
  have hev : ∀ᶠ N in atTop, δ - 2 * smoothTail σ f N ≤ ‖bohrEval σ f ω‖ := by
    filter_upwards [hτ.eventually (gt_mem_nhds hδ)] with N hN
    have hgN : ∀ n, n ∉ Nat.smoothNumbers N → smoothPart N f n = 0 := fun n hn => by
      rw [smoothPart_apply, if_neg hn]
    have hhalfN : ∀ s : ℂ, σ ≤ s.re → δ - smoothTail σ f N ≤ ‖LSeries (⇑(smoothPart N f)) s‖ := by
      intro s hs
      have h1 := norm_bohrEval_sub_smoothPart_le hf N (WienerAlgebraAt.halfPlanePoint σ s hs)
      rw [WienerAlgebraAt.bohrEval_halfPlanePoint, WienerAlgebraAt.bohrEval_halfPlanePoint] at h1
      linarith [hhalf s hs, norm_sub_norm_le (LSeries (⇑f) s) (LSeries (⇑(smoothPart N f)) s)]
    have h3 := le_norm_bohrEval_of_smooth (lSeriesSummable_smoothPart hf N) hgN (by linarith)
      hhalfN ω
    linarith [norm_bohrEval_sub_smoothPart_le hf N ω,
      norm_sub_norm_le (bohrEval σ (smoothPart N f) ω) (bohrEval σ f ω),
      norm_sub_rev (bohrEval σ f ω) (bohrEval σ (smoothPart N f) ω)]
  have hlim : Tendsto (fun N => δ - 2 * smoothTail σ f N) atTop (𝓝 δ) := by
    simpa using (hτ.const_mul 2).const_sub δ
  exact le_of_tendsto hlim hev

namespace WienerAlgebraAt

/-- **The half-plane Wiener lemma** (`⇐`): a kernel of `𝒲_σ` whose L-series is bounded below on
`Re s ≥ σ` is a unit. -/
theorem isUnit_of_le_norm_lSeries {σ : ℝ} (f : WienerAlgebraAt σ) {δ : ℝ} (hδ : 0 < δ)
    (hhalf : ∀ s : ℂ, σ ≤ s.re → δ ≤ ‖LSeries (⇑f.toFn) s‖) : IsUnit f :=
  (isUnit_iff_forall_bohrEval_ne_zero f).2 fun ω h => by
    have := le_norm_bohrEval_of_le_norm_lSeries f.summable hδ hhalf ω
    rw [h, norm_zero] at this
    linarith

theorem norm_bohrEval_le {σ : ℝ} {f : ArithmeticFunction ℂ} (hf : LSeriesSummable (⇑f) σ)
    (ω : BohrPoint) : ‖bohrEval σ f ω‖ ≤ ∑' n : ℕ, ‖term (⇑f) σ n‖ :=
  tsum_of_norm_bounded hf.norm.hasSum fun n => norm_term_le _ (by
    simp only [norm_mul]; exact mul_le_of_le_one_right (norm_nonneg _) (ω.norm_le_one n))

/-- **The half-plane Wiener lemma.**  `f ∈ 𝒲_σ` is a unit iff `inf_{Re s ≥ σ} |L(f, s)| > 0`. -/
theorem isUnit_iff_exists_le_norm_lSeries {σ : ℝ} (f : WienerAlgebraAt σ) :
    IsUnit f ↔ ∃ δ > 0, ∀ s : ℂ, σ ≤ s.re → δ ≤ ‖LSeries (⇑f.toFn) s‖ := by
  refine ⟨fun hf => ?_, fun ⟨δ, hδ, h⟩ => isUnit_of_le_norm_lSeries f hδ h⟩
  obtain ⟨g, hg⟩ := hf.exists_right_inv
  set G := ∑' n : ℕ, ‖term (⇑g.toFn) σ n‖
  have hprod : ∀ ω, bohrEval σ f.toFn ω * bohrEval σ g.toFn ω = 1 := fun ω => by
    have h := congrArg (bohrCharacter σ ω) hg
    rwa [_root_.map_mul, _root_.map_one, bohrCharacter_apply, bohrCharacter_apply] at h
  have hG : 0 < G := by
    have h1 := hprod (halfPlanePoint σ σ (by simp))
    have h2 := norm_bohrEval_le g.summable (halfPlanePoint σ σ (by simp))
    by_contra hle
    have : bohrEval σ g.toFn (halfPlanePoint σ σ (by simp)) = 0 :=
      norm_le_zero_iff.1 (h2.trans (not_lt.1 hle))
    rw [this, mul_zero] at h1
    exact zero_ne_one h1
  refine ⟨G⁻¹, inv_pos.2 hG, fun s hs => ?_⟩
  rw [← bohrEval_halfPlanePoint f.toFn s hs]
  have h1 := hprod (halfPlanePoint σ s hs)
  have h2 := norm_bohrEval_le g.summable (halfPlanePoint σ s hs)
  have h3 : ‖bohrEval σ f.toFn (halfPlanePoint σ s hs)‖ * ‖bohrEval σ g.toFn (halfPlanePoint σ s hs)‖ = 1 := by
    rw [← norm_mul, h1, norm_one]
  rw [inv_le_iff_one_le_mul₀ hG]
  calc (1 : ℝ) = ‖bohrEval σ f.toFn (halfPlanePoint σ s hs)‖ *
        ‖bohrEval σ g.toFn (halfPlanePoint σ s hs)‖ := h3.symm
    _ ≤ ‖bohrEval σ f.toFn (halfPlanePoint σ s hs)‖ * G :=
        mul_le_mul_of_nonneg_left h2 (norm_nonneg _)

end WienerAlgebraAt

end

end GaloisForLFunctions.ArithmeticOrientationTheory
