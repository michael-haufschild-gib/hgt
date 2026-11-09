import GaloisForLFunctions.ArithmeticWeightTheory.TheTrivialFibreIsTheJump
import GaloisForLFunctions.ArithmeticWeightTheory.TheArchimedeanLineHasTheGenericMoments

/-!
# The generic Frobenius is Gaussian

Deligne's equidistribution theorem identifies the monodromy group of a family and the law of its
Frobenius classes. For the gauge family the coinvariants of the `2k`-th tensor power are the
multiplicative pairings, at most `k!` per monomial (`TheGenericFibreHasUniformWeights`). Here the
bound is shown to be attained: the permutation pairings of distinct primes are all present.

**Pairing lower bound** (`factorial_mul_injSum_le_powNorm`). For nonnegative coefficients,
`Σ_N |a^{*k}(N)|² ≥ k! Σ_{t injective} Π_i a_{t_i}²`: an injective tuple `t` and its `k!`
rearrangements `t ∘ σ` have the same product, so the coefficient of that product is at least
`k! Π a_{t_i}`.

**Distinct primes** (`pow_sub_le_injSum`). With `w = a²`, `V = Σ w`, `w ≤ M`,
`Σ_{t injective} Π w_{t_i} ≥ (V − kM)^k` whenever `kM ≤ V`: each new entry avoids at most `k`
values.

**Theorem** (`factorial_mul_pow_le_moment`, `moment_le_factorial_mul_variance_pow`). For a window `0 ≤ g ≤ 1`, `g ≥ c > 0` on `[−1, 1]`, `R ≥ 1`,
`u ≥ 200`, with `V(u) = ∫|T_x(u)|² dx`,

  `k! (V − k e^{−u}(u+R)²)^k ≤ ∫ |T_x(u)|^{2k} dx ≤ k! V^k`,  and `V ≥ c²(u − 1)`.

**Theorem** (`tendsto_moment_ratio`). `∫|T_x(u)|^{2k} dx / V(u)^k → k!` as `u → ∞`: the generic
Frobenius of the gauge family has the moments of a standard complex Gaussian — the Sato–Tate law of
a family whose monodromy is the full torus.
-/

open MeasureTheory Finset Real Filter Topology
open scoped Chebyshev

noncomputable section

namespace GaloisForLFunctions.ArithmeticWeightTheory

open ArithmeticCorrelationGeometry ArithmeticKunnethTheory

/-! ### Tuples -/

/-- Sums over `(k+1)`-tuples split off the first entry. -/
theorem sum_piFinset_succ (s : Finset ℕ) (k : ℕ) (f : (Fin (k + 1) → ℕ) → ℝ) :
    ∑ t ∈ Fintype.piFinset (fun _ : Fin (k + 1) => s), f t =
      ∑ p ∈ s, ∑ t ∈ Fintype.piFinset (fun _ : Fin k => s), f (Fin.cons p t) := by
  rw [← Finset.sum_product']
  refine Finset.sum_nbij' (fun t => (t 0, Fin.tail t)) (fun q => Fin.cons q.1 q.2) ?_ ?_ ?_ ?_ ?_
  · intro t ht
    rw [Fintype.mem_piFinset] at ht
    exact Finset.mem_product.mpr ⟨ht 0, Fintype.mem_piFinset.mpr fun i => ht i.succ⟩
  · intro q hq
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hq
    rw [Fintype.mem_piFinset] at h2 ⊢
    intro i
    refine Fin.cases ?_ (fun j => ?_) i
    · simpa using h1
    · simpa using h2 j
  · intro t _
    exact Fin.cons_self_tail t
  · intro q _
    simp
  · intro t _
    rw [Fin.cons_self_tail]

theorem piFinset_fin_zero (s : Finset ℕ) :
    Fintype.piFinset (fun _ : Fin 0 => s) = {fun i => Fin.elim0 i} := by
  ext t
  simp only [Fintype.mem_piFinset, Finset.mem_singleton]
  constructor
  · intro _; funext i; exact Fin.elim0 i
  · intro _ i; exact Fin.elim0 i

/-- The sum of `Π_i w(t_i)` over injective `k`-tuples from `s`. -/
def injSum (s : Finset ℕ) (w : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ t ∈ (Fintype.piFinset (fun _ : Fin k => s)).filter Function.Injective, ∏ i, w (t i)

theorem injSum_zero (s : Finset ℕ) (w : ℕ → ℝ) : injSum s w 0 = 1 := by
  classical
  unfold injSum
  rw [piFinset_fin_zero, Finset.filter_singleton, if_pos (Function.injective_of_subsingleton _)]
  simp

theorem injSum_nonneg (s : Finset ℕ) {w : ℕ → ℝ} (hw : ∀ p, 0 ≤ w p) (k : ℕ) : 0 ≤ injSum s w k :=
  Finset.sum_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => hw _

/-- **One more distinct prime.** `I_{k+1} ≥ I_k (Σ w − kM)`. -/
theorem injSum_succ_ge (s : Finset ℕ) {w : ℕ → ℝ} (hw : ∀ p, 0 ≤ w p) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ p ∈ s, w p ≤ M) (k : ℕ) :
    injSum s w k * ((∑ p ∈ s, w p) - k * M) ≤ injSum s w (k + 1) := by
  classical
  have hsplit : injSum s w (k + 1) = ∑ t ∈ (Fintype.piFinset (fun _ : Fin k => s)).filter
      Function.Injective, (∏ i, w (t i)) * ∑ p ∈ s.filter (fun p => p ∉ Set.range t), w p := by
    unfold injSum
    rw [Finset.sum_filter, sum_piFinset_succ, Finset.sum_comm, Finset.sum_filter]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.mul_sum, Finset.sum_filter]
    by_cases ht : Function.Injective t
    · rw [if_pos ht]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      by_cases hp : p ∈ Set.range t
      · rw [if_neg (fun h => (Fin.cons_injective_iff.mp h).1 hp), if_neg (not_not.mpr hp)]
      · rw [if_pos (Fin.cons_injective_iff.mpr ⟨hp, ht⟩), if_pos hp]; ring
    · rw [if_neg ht]
      refine Finset.sum_eq_zero fun p _ => ?_
      rw [if_neg (fun h => ht (Fin.cons_injective_iff.mp h).2)]
  rw [hsplit]
  unfold injSum
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun t ht => ?_
  have hprod : 0 ≤ ∏ i, w (t i) := Finset.prod_nonneg fun i _ => hw _
  refine mul_le_mul_of_nonneg_left ?_ hprod
  -- the excluded values number at most `k`
  have hsub : ∑ p ∈ s.filter (fun p => p ∈ Set.range t), w p ≤ k * M := by
    have hcard : (s.filter (fun p => p ∈ Set.range t)).card ≤ k := by
      calc (s.filter (fun p => p ∈ Set.range t)).card ≤ (Finset.univ.image t).card := by
            refine Finset.card_le_card fun p hp => ?_
            obtain ⟨i, rfl⟩ := (Finset.mem_filter.mp hp).2
            exact Finset.mem_image_of_mem t (Finset.mem_univ i)
        _ ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
        _ = k := by simp
    calc ∑ p ∈ s.filter (fun p => p ∈ Set.range t), w p
        ≤ ∑ _p ∈ s.filter (fun p => p ∈ Set.range t), M :=
          Finset.sum_le_sum fun p hp => hM p (Finset.mem_filter.mp hp).1
      _ = (s.filter (fun p => p ∈ Set.range t)).card * M := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ k * M := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hM0
  have hfs := Finset.sum_filter_add_sum_filter_not s (fun p => p ∈ Set.range t) w
  linarith

/-- **Distinct primes.** `Σ_{t injective} Π w(t_i) ≥ (Σw − kM)^k` when `kM ≤ Σ w`. -/
theorem pow_sub_le_injSum (s : Finset ℕ) {w : ℕ → ℝ} (hw : ∀ p, 0 ≤ w p) {M : ℝ}
    (hM0 : 0 ≤ M) (hM : ∀ p ∈ s, w p ≤ M) :
    ∀ k : ℕ, k * M ≤ ∑ p ∈ s, w p → ((∑ p ∈ s, w p) - k * M) ^ k ≤ injSum s w k
  | 0, _ => by simp [injSum_zero]
  | k + 1, hk => by
    have hk' : (k : ℝ) * M ≤ ∑ p ∈ s, w p := by
      have : (k : ℝ) * M ≤ ((k + 1 : ℕ) : ℝ) * M := by
        push_cast; nlinarith
      linarith
    have ih := pow_sub_le_injSum s hw hM0 hM k hk'
    have hstep := injSum_succ_ge s hw hM0 hM k
    have h0 : 0 ≤ (∑ p ∈ s, w p) - ((k + 1 : ℕ) : ℝ) * M := by linarith
    have hle : (∑ p ∈ s, w p) - ((k + 1 : ℕ) : ℝ) * M ≤ (∑ p ∈ s, w p) - k * M := by
      push_cast; linarith
    calc ((∑ p ∈ s, w p) - ((k + 1 : ℕ) : ℝ) * M) ^ (k + 1)
        = ((∑ p ∈ s, w p) - ((k + 1 : ℕ) : ℝ) * M) ^ k * ((∑ p ∈ s, w p) - ((k + 1 : ℕ) : ℝ) * M) :=
          pow_succ _ _
      _ ≤ ((∑ p ∈ s, w p) - k * M) ^ k * ((∑ p ∈ s, w p) - k * M) :=
          mul_le_mul (pow_le_pow_left₀ h0 hle k) hle h0 (pow_nonneg (h0.trans hle) k)
      _ ≤ injSum s w k * ((∑ p ∈ s, w p) - k * M) :=
          mul_le_mul_of_nonneg_right ih (h0.trans hle)
      _ ≤ injSum s w (k + 1) := hstep

/-! ### The pairings are attained -/

/-- The weight `Π_i a(t_i)` of a tuple. -/
def tupleWeight (a : ℕ → ℝ) {k : ℕ} (t : Fin k → ℕ) : ℝ := ∏ i, a (t i)

theorem tupleWeight_nonneg {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {k : ℕ} (t : Fin k → ℕ) :
    0 ≤ tupleWeight a t :=
  Finset.prod_nonneg fun _ _ => ha _

theorem tupleWeight_comp_perm (a : ℕ → ℝ) {k : ℕ} (t : Fin k → ℕ) (σ : Equiv.Perm (Fin k)) :
    tupleWeight a (t ∘ ⇑σ) = tupleWeight a t :=
  Equiv.prod_comp σ (fun i => a (t i))

theorem powCoeffReal_eq_sum (s : Finset ℕ) (a : ℕ → ℝ) (k N : ℕ) :
    powCoeffReal s a k N = ∑ t ∈ (Fintype.piFinset (fun _ : Fin k => s)).filter
      (fun t => ∏ i, t i = N), tupleWeight a t := rfl

/-- **An injective tuple brings its `k!` rearrangements**: `k! Π a(t_i) ≤ a^{*k}(Π t_i)`. -/
theorem factorial_mul_tupleWeight_le (s : Finset ℕ) {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) {k N : ℕ}
    {t : Fin k → ℕ} (ht : t ∈ (Fintype.piFinset (fun _ : Fin k => s)).filter (fun t => ∏ i, t i = N))
    (hinj : Function.Injective t) :
    (k.factorial : ℝ) * tupleWeight a t ≤ powCoeffReal s a k N := by
  classical
  obtain ⟨hT, hN⟩ := Finset.mem_filter.mp ht
  have himg : (Finset.univ : Finset (Equiv.Perm (Fin k))).image
      (fun σ : Equiv.Perm (Fin k) => t ∘ ⇑σ) ⊆
      (Fintype.piFinset (fun _ : Fin k => s)).filter (fun t => ∏ i, t i = N) := by
    intro t' ht'
    obtain ⟨σ, -, rfl⟩ := Finset.mem_image.mp ht'
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [Fintype.mem_piFinset] at hT ⊢
      exact fun i => hT (σ i)
    · rw [← hN]; exact Equiv.prod_comp σ t
  have hinjσ : Set.InjOn (fun σ : Equiv.Perm (Fin k) => t ∘ ⇑σ)
      ↑(Finset.univ : Finset (Equiv.Perm (Fin k))) := by
    intro σ _ τ _ h
    exact Equiv.ext fun i => congrFun (hinj.comp_left h) i
  rw [powCoeffReal_eq_sum]
  calc (k.factorial : ℝ) * tupleWeight a t = ∑ σ : Equiv.Perm (Fin k), tupleWeight a (t ∘ ⇑σ) := by
        simp only [tupleWeight_comp_perm, Finset.sum_const, Finset.card_univ, Fintype.card_perm,
          Fintype.card_fin, nsmul_eq_mul]
    _ = ∑ t' ∈ (Finset.univ : Finset (Equiv.Perm (Fin k))).image
          (fun σ : Equiv.Perm (Fin k) => t ∘ ⇑σ),
          tupleWeight a t' := (Finset.sum_image hinjσ).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg himg fun t' _ _ => tupleWeight_nonneg ha t'

/-- Squaring fibrewise: `k! Σ_{t injective, Πt = N} (Π a(t_i))² ≤ a^{*k}(N)²`. -/
theorem factorial_mul_fibre_sq_le (s : Finset ℕ) {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (k N : ℕ) :
    (k.factorial : ℝ) * ∑ t ∈ ((Fintype.piFinset (fun _ : Fin k => s)).filter Function.Injective).filter
      (fun t => ∏ i, t i = N), tupleWeight a t ^ 2 ≤ powCoeffReal s a k N ^ 2 := by
  classical
  have hb0 : 0 ≤ powCoeffReal s a k N := powCoeffReal_nonneg ha k N
  calc (k.factorial : ℝ) * ∑ t ∈ ((Fintype.piFinset (fun _ : Fin k => s)).filter
        Function.Injective).filter (fun t => ∏ i, t i = N), tupleWeight a t ^ 2
      = ∑ t ∈ ((Fintype.piFinset (fun _ : Fin k => s)).filter Function.Injective).filter
          (fun t => ∏ i, t i = N), tupleWeight a t * ((k.factorial : ℝ) * tupleWeight a t) := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun t _ => by ring
    _ ≤ ∑ t ∈ ((Fintype.piFinset (fun _ : Fin k => s)).filter Function.Injective).filter
          (fun t => ∏ i, t i = N), tupleWeight a t * powCoeffReal s a k N := by
        refine Finset.sum_le_sum fun t ht => mul_le_mul_of_nonneg_left ?_ (tupleWeight_nonneg ha t)
        obtain ⟨ht1, hN⟩ := Finset.mem_filter.mp ht
        obtain ⟨hT, hinj⟩ := Finset.mem_filter.mp ht1
        exact factorial_mul_tupleWeight_le s ha (Finset.mem_filter.mpr ⟨hT, hN⟩) hinj
    _ ≤ ∑ t ∈ (Fintype.piFinset (fun _ : Fin k => s)).filter (fun t => ∏ i, t i = N),
          tupleWeight a t * powCoeffReal s a k N := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun t ht => ?_)
          fun t _ _ => mul_nonneg (tupleWeight_nonneg ha t) hb0
        obtain ⟨ht1, hN⟩ := Finset.mem_filter.mp ht
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp ht1).1, hN⟩
    _ = powCoeffReal s a k N ^ 2 := by rw [← Finset.sum_mul, ← powCoeffReal_eq_sum]; ring

/-- **Pairing lower bound.** `Σ_N (a^{*k}(N))² ≥ k! Σ_{t injective} Π a(t_i)²`. -/
theorem factorial_mul_injSum_le_powNorm (s : Finset ℕ) {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (k : ℕ) :
    (k.factorial : ℝ) * injSum s (fun n => a n ^ 2) k ≤
      ∑ N ∈ powSupport s k, powCoeffReal s a k N ^ 2 := by
  classical
  have hmaps : ∀ t ∈ (Fintype.piFinset (fun _ : Fin k => s)).filter Function.Injective,
      (∏ i, t i) ∈ powSupport s k := by
    intro t ht
    unfold powSupport
    exact Finset.mem_image_of_mem _ (Finset.mem_filter.mp ht).1
  have hpart := Finset.sum_fiberwise_of_maps_to hmaps (fun t => tupleWeight a t ^ 2)
  have hinj : injSum s (fun n => a n ^ 2) k =
      ∑ t ∈ (Fintype.piFinset (fun _ : Fin k => s)).filter Function.Injective, tupleWeight a t ^ 2 := by
    unfold injSum tupleWeight
    exact Finset.sum_congr rfl fun t _ => by beta_reduce; rw [Finset.prod_pow]
  rw [hinj, ← hpart, Finset.mul_sum]
  exact Finset.sum_le_sum fun N _ => factorial_mul_fibre_sq_le s ha k N

/-! ### The Gaussian law of the window traces -/

/-- The window variance is at least `c²(u − 1)` for `u ≥ 200`. -/
theorem variance_ge {g : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hgc : ∀ v, |v| ≤ 1 → c ≤ g v) {R : ℝ} (hR : 1 ≤ R) {u : ℝ} (hu : 200 ≤ u) :
    c ^ 2 * (u - 1) ≤ ∑ p ∈ windowPrimes R u, windowWeightReal g u p ^ 2 := by
  set A := Nat.primesLE ⌊Real.exp (u + 1)⌋₊
  set B := Nat.primesLE ⌊Real.exp (u - 1)⌋₊
  have hBA : B ⊆ A := Nat.primesLE_mono (Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith)))
  have hAW : A ⊆ windowPrimes R u :=
    Nat.primesLE_mono (Nat.floor_le_floor (Real.exp_le_exp.mpr (by linarith)))
  have hθ : θ (Real.exp (u + 1)) - θ (Real.exp (u - 1)) = ∑ p ∈ A \ B, Real.log p := by
    rw [Chebyshev.theta_eq_sum_primesLE, Chebyshev.theta_eq_sum_primesLE, ← Finset.sum_sdiff hBA]
    ring
  have hwin := exp_le_theta_window hu
  rw [hθ] at hwin
  have hterm : ∀ p ∈ A \ B, Real.exp (-u) * (u - 1) * c ^ 2 * Real.log p ≤ windowWeightReal g u p ^ 2 := by
    intro p hp
    obtain ⟨hpA, hpB⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpN, hpp⟩ := Nat.mem_primesLE.mp hpA
    have hnot : ⌊Real.exp (u - 1)⌋₊ < p := by
      by_contra h; push Not at h; exact hpB (Nat.mem_primesLE.mpr ⟨h, hpp⟩)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hl1 : u - 1 < Real.log p :=
      (Real.lt_log_iff_exp_lt hp0).mpr ((Nat.floor_lt (Real.exp_pos _).le).mp hnot)
    have hl2 : Real.log p ≤ u + 1 := (Real.log_le_iff_le_exp hp0).mpr
      ((Nat.cast_le.mpr hpN).trans (Nat.floor_le (Real.exp_pos _).le))
    have hgv := hgc (Real.log p - u) (abs_le.mpr ⟨by linarith, by linarith⟩)
    have hexp : Real.exp (-(u / 2)) ^ 2 = Real.exp (-u) := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    have hc2 : c ^ 2 ≤ g (Real.log p - u) ^ 2 := pow_le_pow_left₀ hc hgv 2
    have hlog0 : 0 ≤ Real.log p := by linarith
    unfold windowWeightReal
    rw [mul_pow, mul_pow, hexp]
    have he := (Real.exp_pos (-u)).le
    calc Real.exp (-u) * (u - 1) * c ^ 2 * Real.log p
        = Real.exp (-u) * ((u - 1) * Real.log p) * c ^ 2 := by ring
      _ ≤ Real.exp (-u) * (Real.log p * Real.log p) * g (Real.log p - u) ^ 2 := by
          gcongr
      _ = Real.exp (-u) * Real.log p ^ 2 * g (Real.log p - u) ^ 2 := by ring
  have hee : Real.exp (-u) * Real.exp u = 1 := by
    rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
  calc c ^ 2 * (u - 1) = Real.exp (-u) * (u - 1) * c ^ 2 * Real.exp u := by
        rw [show Real.exp (-u) * (u - 1) * c ^ 2 * Real.exp u =
          (Real.exp (-u) * Real.exp u) * (c ^ 2 * (u - 1)) by ring, hee, one_mul]
    _ ≤ Real.exp (-u) * (u - 1) * c ^ 2 * ∑ p ∈ A \ B, Real.log p := by
        gcongr
        have : 0 ≤ u - 1 := by linarith
        positivity
    _ = ∑ p ∈ A \ B, Real.exp (-u) * (u - 1) * c ^ 2 * Real.log p := by rw [Finset.mul_sum]
    _ ≤ ∑ p ∈ A \ B, windowWeightReal g u p ^ 2 := Finset.sum_le_sum hterm
    _ ≤ ∑ p ∈ windowPrimes R u, windowWeightReal g u p ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.sdiff_subset.trans hAW)
          fun p _ _ => sq_nonneg _

/-- Each window weight is at most `e^{−u}(u + R)²`. -/
theorem windowWeightReal_sq_le {g : ℝ → ℝ} (hg : ∀ v, |g v| ≤ 1) {R u : ℝ} :
    ∀ p ∈ windowPrimes R u, windowWeightReal g u p ^ 2 ≤ Real.exp (-u) * (u + R) ^ 2 := by
  intro p hp
  obtain ⟨hpN, hpp⟩ := Nat.mem_primesLE.mp hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
  have hlog0 : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
  have hlogle : Real.log p ≤ u + R := (Real.log_le_iff_le_exp hp0).mpr
    ((Nat.cast_le.mpr hpN).trans (Nat.floor_le (Real.exp_pos _).le))
  have hexp : Real.exp (-(u / 2)) ^ 2 = Real.exp (-u) := by
    rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hg2 : g (Real.log p - u) ^ 2 ≤ 1 := by
    rw [← sq_abs]; nlinarith [hg (Real.log p - u), abs_nonneg (g (Real.log p - u))]
  unfold windowWeightReal
  rw [mul_pow, mul_pow, hexp]
  have he := (Real.exp_pos (-u)).le
  calc Real.exp (-u) * Real.log p ^ 2 * g (Real.log p - u) ^ 2 ≤ Real.exp (-u) * Real.log p ^ 2 * 1 := by
        gcongr
    _ ≤ Real.exp (-u) * (u + R) ^ 2 := by
        rw [mul_one]; gcongr

/-- The window variance `V(u) = ∫ |T_x(u)|² dx`. -/
def windowVariance (g : ℝ → ℝ) (R u : ℝ) : ℝ := ∑ p ∈ windowPrimes R u, windowWeightReal g u p ^ 2

theorem integral_normSq_fibreTrace (g : ℝ → ℝ) (R u : ℝ) :
    ∫ x, ‖fibreTrace g R u x‖ ^ 2 ∂gaugeHaar = windowVariance g R u := by
  unfold fibreTrace windowVariance
  rw [integral_normSq_twistSum (s := windowPrimes R u) (fun n hn => (Nat.mem_primesLE.mp hn).2.ne_zero)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [show windowWeight g u p = ((windowWeightReal g u p : ℝ) : ℂ) from rfl, Complex.norm_real,
    Real.norm_eq_abs, sq_abs]

theorem integral_fibreTrace_pow_eq_powNorm (g : ℝ → ℝ) (R u : ℝ) (k : ℕ) :
    ∫ x, ‖fibreTrace g R u x‖ ^ (2 * k) ∂gaugeHaar =
      ∑ N ∈ powSupport (windowPrimes R u) k, powCoeffReal (windowPrimes R u) (windowWeightReal g u) k N ^ 2 := by
  unfold fibreTrace
  rw [show windowWeight g u = fun n => ((windowWeightReal g u n : ℝ) : ℂ) from rfl,
    integral_normSq_twistSum_pow (s := windowPrimes R u) (fun n hn => (Nat.mem_primesLE.mp hn).2.ne_zero)]
  refine Finset.sum_congr rfl fun N _ => ?_
  rw [powCoeff_ofReal, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- **Upper Gaussian bound**: the coinvariants are at most the `k!` pairings. -/
theorem moment_le_factorial_mul_variance_pow (g : ℝ → ℝ) (R u : ℝ) (k : ℕ) :
    ∫ x, ‖fibreTrace g R u x‖ ^ (2 * k) ∂gaugeHaar ≤ (k.factorial : ℝ) * windowVariance g R u ^ k := by
  have h := integral_norm_twistSum_pow_le (B := windowPrimes R u)
    (fun p hp => (Nat.mem_primesLE.mp hp).2) (windowWeight g u) k
  have hv : ∑ p ∈ windowPrimes R u, ‖windowWeight g u p‖ ^ 2 = windowVariance g R u := by
    unfold windowVariance
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [show windowWeight g u p = ((windowWeightReal g u p : ℝ) : ℂ) from rfl, Complex.norm_real,
      Real.norm_eq_abs, sq_abs]
  rw [hv] at h
  exact h

/-- **Lower Gaussian bound**: the pairings of distinct primes are all present. -/
theorem factorial_mul_pow_le_moment {g : ℝ → ℝ} (hg : ∀ v, |g v| ≤ 1) (hg0 : ∀ v, 0 ≤ g v)
    {R u : ℝ} (k : ℕ)
    (hkV : k * (Real.exp (-u) * (u + R) ^ 2) ≤ windowVariance g R u) :
    (k.factorial : ℝ) * (windowVariance g R u - k * (Real.exp (-u) * (u + R) ^ 2)) ^ k ≤
      ∫ x, ‖fibreTrace g R u x‖ ^ (2 * k) ∂gaugeHaar := by
  have ha : ∀ n, 0 ≤ windowWeightReal g u n := fun n =>
    mul_nonneg (mul_nonneg (Real.exp_pos _).le (Real.log_natCast_nonneg n)) (hg0 _)
  have hw : ∀ p, 0 ≤ windowWeightReal g u p ^ 2 := fun p => sq_nonneg _
  have hM0 : 0 ≤ Real.exp (-u) * (u + R) ^ 2 := by positivity
  rw [integral_fibreTrace_pow_eq_powNorm]
  refine le_trans ?_ (factorial_mul_injSum_le_powNorm _ ha k)
  exact mul_le_mul_of_nonneg_left (pow_sub_le_injSum _ hw hM0
    (windowWeightReal_sq_le hg) k hkV) (by positivity)

/-- **The Sato–Tate law of the gauge family.** The `2k`-th moment over the `k`-th power of the
variance tends to `k!`. -/
theorem tendsto_moment_ratio {g : ℝ → ℝ} (hg : ∀ v, |g v| ≤ 1) (hg0 : ∀ v, 0 ≤ g v) {c : ℝ}
    (hc : 0 < c) (hgc : ∀ v, |v| ≤ 1 → c ≤ g v) {R : ℝ} (hR : 1 ≤ R) (k : ℕ) :
    Tendsto (fun u => (∫ x, ‖fibreTrace g R u x‖ ^ (2 * k) ∂gaugeHaar) / windowVariance g R u ^ k)
      atTop (𝓝 (k.factorial : ℝ)) := by
  have hc2 : 0 < c ^ 2 := by positivity
  set ε : ℝ → ℝ := fun u => k * (Real.exp (-u) * (u + R) ^ 2) / (c ^ 2 * (u - 1)) with hεdef
  -- the relative size of one weight tends to zero
  have hε : Tendsto ε atTop (𝓝 0) := by
    have h1 : Tendsto (fun u : ℝ => u ^ 2 * Real.exp (-u)) atTop (𝓝 0) :=
      Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2
    have h2 : Tendsto (fun u : ℝ => u * Real.exp (-u)) atTop (𝓝 0) := by
      simpa using Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1
    have h3 : Tendsto (fun u : ℝ => Real.exp (-u)) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero
    have hnum : Tendsto (fun u : ℝ => Real.exp (-u) * (u + R) ^ 2) atTop (𝓝 0) := by
      have := h1.add ((h2.const_mul (2 * R)).add (h3.const_mul (R ^ 2)))
      simp only [mul_zero, add_zero] at this
      exact this.congr fun u => by ring
    have hbound : ∀ᶠ u in atTop, ‖ε u‖ ≤ k / c ^ 2 * (Real.exp (-u) * (u + R) ^ 2) := by
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with u hu
      have hnum0 : 0 ≤ (k : ℝ) * (Real.exp (-u) * (u + R) ^ 2) := by positivity
      have hden : c ^ 2 ≤ c ^ 2 * (u - 1) := le_mul_of_one_le_right hc2.le (by linarith)
      have h1 : ε u ≤ (k : ℝ) * (Real.exp (-u) * (u + R) ^ 2) / c ^ 2 :=
        div_le_div_of_nonneg_left hnum0 hc2 hden
      rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hnum0 (mul_nonneg hc2.le (by linarith)))]
      calc ε u ≤ (k : ℝ) * (Real.exp (-u) * (u + R) ^ 2) / c ^ 2 := h1
        _ = k / c ^ 2 * (Real.exp (-u) * (u + R) ^ 2) := by ring
    have hlim := hnum.const_mul ((k : ℝ) / c ^ 2)
    rw [mul_zero] at hlim
    exact squeeze_zero_norm' hbound hlim
  have hlow : Tendsto (fun u => (k.factorial : ℝ) * (1 - ε u) ^ k) atTop (𝓝 (k.factorial : ℝ)) := by
    have := ((tendsto_const_nhds (x := (1 : ℝ))).sub hε).pow k |>.const_mul (k.factorial : ℝ)
    simpa using this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_ge_atTop (200 : ℝ), hε.eventually (gt_mem_nhds one_pos)]
      with u hu hε1
    have hu1 : (0 : ℝ) < u - 1 := by linarith
    have hV := variance_ge hc.le hgc hR hu
    have hVpos : 0 < windowVariance g R u := lt_of_lt_of_le (by positivity) hV
    have hε0 : 0 ≤ ε u := div_nonneg (by positivity) (mul_nonneg hc2.le hu1.le)
    have hεle : (k : ℝ) * (Real.exp (-u) * (u + R) ^ 2) ≤ ε u * windowVariance g R u := by
      simp only [hεdef]
      rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left hV (by positivity)
    have hεV : ε u * windowVariance g R u ≤ windowVariance g R u := by
      nlinarith
    have hkV : (k : ℝ) * (Real.exp (-u) * (u + R) ^ 2) ≤ windowVariance g R u := hεle.trans hεV
    have hl := factorial_mul_pow_le_moment hg hg0 k hkV
    rw [le_div_iff₀ (pow_pos hVpos k)]
    have h0 : 0 ≤ windowVariance g R u - ε u * windowVariance g R u := by linarith
    have hle : windowVariance g R u - ε u * windowVariance g R u ≤
        windowVariance g R u - k * (Real.exp (-u) * (u + R) ^ 2) := by linarith
    calc (k.factorial : ℝ) * (1 - ε u) ^ k * windowVariance g R u ^ k
        = (k.factorial : ℝ) * (windowVariance g R u - ε u * windowVariance g R u) ^ k := by
          rw [mul_assoc, ← mul_pow]
          congr 2
          ring
      _ ≤ (k.factorial : ℝ) * (windowVariance g R u - k * (Real.exp (-u) * (u + R) ^ 2)) ^ k :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hle k) (by positivity)
      _ ≤ _ := hl
  · filter_upwards [eventually_ge_atTop (200 : ℝ)] with u hu
    have hu1 : (0 : ℝ) < u - 1 := by linarith
    have hVpos : 0 < windowVariance g R u :=
      lt_of_lt_of_le (by positivity) (variance_ge hc.le hgc hR hu)
    rw [div_le_iff₀ (pow_pos hVpos k)]
    exact moment_le_factorial_mul_variance_pow g R u k

end GaloisForLFunctions.ArithmeticWeightTheory
