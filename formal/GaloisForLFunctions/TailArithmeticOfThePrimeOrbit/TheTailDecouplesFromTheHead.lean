import GaloisForLFunctions.RHTower.Sieve.DirichletMVTWindow
import GaloisForLFunctions.HTGeometry.LogFrequencySeparation
import Mathlib.NumberTheory.SmoothNumbers

/-!
# The tail decouples from the head

A *head polynomial* `R(t) = Σ_{m∈A} r_m m^{it}` lives on `y`-smooth integers; a *tail polynomial*
`B(t) = Σ_{n∈B} b_n n^{it}` lives on `y`-rough integers (every prime factor at least `y`). The weight `|R|²` is how a
resonator conditions on the head: a box resonator concentrates it on heights where the head is aligned.

**Unique factorization decouples.** A smooth integer times a rough one determines both factors
(`smooth_mul_rough_injective`). So `R·B` is a Dirichlet polynomial whose coefficient vector is the tensor product
`r ⊗ b`, of squared norm `‖r‖²‖b‖²`, and the mean value theorem gives (`integral_head_mul_tail`)

`∫_T^{2T} |R|²|B|² = T ‖r‖² ‖b‖² + O(N log N ‖r‖² ‖b‖²)`, `N ≥ max mn`.

With `∫_T^{2T} |R|² = T ‖r‖² + O(N log N ‖r‖²)` this is the **conditional second moment**
(`abs_conditional_second_moment_sub_le`): on the head-conditioned measure `|R|² dt / ∫|R|²` the tail has the second
moment `‖b‖²` it has unconditionally, up to `O(N log N/T)`.

**The conditional mean of the tail vanishes** (`norm_integral_head_sq_mul_tail_le`). If no tail integer is `1`, then
`mn ≠ m'` for smooth `m, m'` and rough `n`, so every frequency `log(mn/m')` of `|R|²B` is at least `1/N` by the integer
gap, and `|∫_T^{2T} |R|² B| ≤ 2N (Σ|r_m|)² Σ|b_n|`, independent of `T`.

Every power `B^k` is again a tail polynomial, so the statements apply to all conditional moments. The range is the
Kronecker scale: they say something only while `N log N ≪ T`, that is while the head resonator is shorter than the
height. Past it, the head weight has frequencies below `1/T` and the conditional law is dark.
-/

open Real Finset MeasureTheory intervalIntegral

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

noncomputable section

/-! ## Indexed Dirichlet polynomials and their mean value -/

/-- A Dirichlet polynomial indexed by a finite set `E` with integer frequencies `k_j`. -/
def indexedPoly {J : Type*} (E : Finset J) (k : J → ℕ) (c : J → ℂ) (t : ℝ) : ℂ :=
  ∑ j ∈ E, c j * Complex.exp (((t * Real.log (k j : ℝ) : ℝ) : ℂ) * Complex.I)

/-- The coefficient vector of an indexed polynomial on `Fin N`. -/
def fiberCoeff {J : Type*} (E : Finset J) (k : J → ℕ) (c : J → ℂ) (N : ℕ) : Fin N → ℂ :=
  fun n => ∑ j ∈ E.filter (fun j => k j = (n : ℕ) + 1), c j

variable {J : Type*} [DecidableEq J]

omit [DecidableEq J] in
theorem sum_range_fiber {E : Finset J} {k : J → ℕ} {N : ℕ} (hk : ∀ j ∈ E, 1 ≤ k j ∧ k j ≤ N)
    (f : J → ℂ) : ∑ m ∈ range N, ∑ j ∈ E.filter (fun j => k j = m + 1), f j = ∑ j ∈ E, f j := by
  have h := Finset.sum_fiberwise_of_maps_to (s := E) (t := range N) (g := fun j => k j - 1)
    (fun j hj => by
      have := hk j hj
      exact Finset.mem_range.mpr (by omega)) f
  rw [← h]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr ?_ fun _ _ => rfl
  ext j
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hj, h⟩; exact ⟨hj, by omega⟩
  · rintro ⟨hj, h⟩; have := hk j hj; exact ⟨hj, by omega⟩

omit [DecidableEq J] in
theorem dirPoly_fiberCoeff {E : Finset J} {k : J → ℕ} (c : J → ℂ) {N : ℕ} (hk : ∀ j ∈ E, 1 ≤ k j ∧ k j ≤ N)
    (t : ℝ) : RHTower.Sieve.dirPoly N (fiberCoeff E k c N) t = indexedPoly E k c t := by
  unfold RHTower.Sieve.dirPoly fiberCoeff indexedPoly
  rw [Fin.sum_univ_eq_sum_range (fun m => (∑ j ∈ E.filter (fun j => k j = m + 1), c j) *
    Complex.exp (((t * Real.log ((m : ℝ) + 1) : ℝ) : ℂ) * Complex.I)) N]
  rw [← sum_range_fiber hk]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hkj : (k j : ℝ) = (m : ℝ) + 1 := by
    have := (Finset.mem_filter.mp hj).2
    rw [this]
    push_cast
    ring
  rw [hkj]

omit [DecidableEq J] in
theorem norm_sq_sum_of_card_le_one {F : Finset J} (hF : F.card ≤ 1) (c : J → ℂ) :
    ‖∑ j ∈ F, c j‖ ^ 2 = ∑ j ∈ F, ‖c j‖ ^ 2 := by
  rcases F.eq_empty_or_nonempty with h | ⟨j, hj⟩
  · simp [h]
  · have hF1 : F = {j} :=
      Finset.eq_singleton_iff_unique_mem.mpr ⟨hj, fun b hb => Finset.card_le_one.mp hF b hb j hj⟩
    simp [hF1]

omit [DecidableEq J] in
theorem sum_norm_sq_fiberCoeff {E : Finset J} {k : J → ℕ} (c : J → ℂ) {N : ℕ}
    (hk : ∀ j ∈ E, 1 ≤ k j ∧ k j ≤ N) (hinj : Set.InjOn k E) :
    ∑ n : Fin N, ‖fiberCoeff E k c N n‖ ^ 2 = ∑ j ∈ E, ‖c j‖ ^ 2 := by
  unfold fiberCoeff
  rw [Fin.sum_univ_eq_sum_range (fun m => ‖∑ j ∈ E.filter (fun j => k j = m + 1), c j‖ ^ 2) N]
  have hcast : ∀ j ∈ E, ((‖c j‖ ^ 2 : ℝ) : ℂ) = ((‖c j‖ ^ 2 : ℝ) : ℂ) := fun _ _ => rfl
  have h := sum_range_fiber hk (fun j => ((‖c j‖ ^ 2 : ℝ) : ℂ))
  have h' : ∑ m ∈ range N, ∑ j ∈ E.filter (fun j => k j = m + 1), ‖c j‖ ^ 2 = ∑ j ∈ E, ‖c j‖ ^ 2 := by
    exact_mod_cast h
  rw [← h']
  refine Finset.sum_congr rfl fun m _ => norm_sq_sum_of_card_le_one ?_ c
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  obtain ⟨haE, hka⟩ := Finset.mem_filter.mp ha
  obtain ⟨hbE, hkb⟩ := Finset.mem_filter.mp hb
  exact hinj haE hbE (hka.trans hkb.symm)

omit [DecidableEq J] in
/-- **The mean value theorem for indexed polynomials.** -/
theorem indexed_meanValue {E : Finset J} {k : J → ℕ} (c : J → ℂ) {N : ℕ}
    (hk : ∀ j ∈ E, 1 ≤ k j ∧ k j ≤ N) (hinj : Set.InjOn k E) (T : ℝ) :
    |(∫ t in T..(2 * T), ‖indexedPoly E k c t‖ ^ 2) - T * ∑ j ∈ E, ‖c j‖ ^ 2| ≤
      8 * N * (1 + Real.log N) * ∑ j ∈ E, ‖c j‖ ^ 2 := by
  have h := RHTower.Sieve.dirichlet_meanValue_dyadic N (fiberCoeff E k c N) T
  rw [sum_norm_sq_fiberCoeff c hk hinj] at h
  have e : (fun t => ‖RHTower.Sieve.dirPoly N (fiberCoeff E k c N) t‖ ^ 2) =
      fun t => ‖indexedPoly E k c t‖ ^ 2 := by
    funext t
    rw [dirPoly_fiberCoeff c hk t]
  rw [e] at h
  exact h

/-! ## Smooth times rough -/

/-- `n` is `y`-rough: nonzero, with every prime factor at least `y`. -/
def IsRough (y n : ℕ) : Prop := n ≠ 0 ∧ ∀ p, p.Prime → p ∣ n → y ≤ p

theorem coprime_of_smooth_of_rough {y m n : ℕ} (hm : m ∈ Nat.smoothNumbers y) (hn : IsRough y n) :
    Nat.Coprime m n :=
  Nat.coprime_of_dvd fun p hp hpm hpn => by
    have h1 := (Nat.mem_smoothNumbers'.mp hm) p hp hpm
    have h2 := hn.2 p hp hpn
    omega

/-- **Unique factorization decouples.** A smooth integer times a rough integer determines both. -/
theorem smooth_mul_rough_injective {y m m' n n' : ℕ} (hm : m ∈ Nat.smoothNumbers y)
    (hm' : m' ∈ Nat.smoothNumbers y) (hn : IsRough y n) (hn' : IsRough y n') (h : m * n = m' * n') :
    m = m' ∧ n = n' := by
  have h1 : m ∣ m' := (coprime_of_smooth_of_rough hm hn').dvd_of_dvd_mul_right ⟨n, by rw [← h]⟩
  have h2 : m' ∣ m := (coprime_of_smooth_of_rough hm' hn).dvd_of_dvd_mul_right ⟨n', by rw [h]⟩
  have hmm : m = m' := Nat.dvd_antisymm h1 h2
  refine ⟨hmm, ?_⟩
  rw [hmm] at h
  exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (Nat.ne_zero_of_mem_smoothNumbers hm')) h

/-- A polynomial `Σ_{m∈A} r_m m^{it}`. -/
def headPoly (A : Finset ℕ) (r : ℕ → ℂ) (t : ℝ) : ℂ :=
  ∑ m ∈ A, r m * Complex.exp (((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I)

theorem headPoly_eq_indexedPoly (A : Finset ℕ) (r : ℕ → ℂ) (t : ℝ) :
    headPoly A r t = indexedPoly A id r t := rfl

theorem headPoly_mul (A B : Finset ℕ) (r b : ℕ → ℂ) (hA : ∀ m ∈ A, m ≠ 0) (hB : ∀ n ∈ B, n ≠ 0) (t : ℝ) :
    headPoly A r t * headPoly B b t =
      indexedPoly (A ×ˢ B) (fun q => q.1 * q.2) (fun q => r q.1 * b q.2) t := by
  unfold headPoly indexedPoly
  rw [Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun n hn => ?_
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast hA m hm
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hB n hn
  have hlog : Real.log ((m * n : ℕ) : ℝ) = Real.log m + Real.log n := by
    rw [Nat.cast_mul, Real.log_mul hm0 hn0]
  dsimp only
  rw [hlog, mul_add, Complex.ofReal_add, add_mul, Complex.exp_add]
  ring

theorem sum_norm_sq_tensor (A B : Finset ℕ) (r b : ℕ → ℂ) :
    ∑ q ∈ A ×ˢ B, ‖r q.1 * b q.2‖ ^ 2 = (∑ m ∈ A, ‖r m‖ ^ 2) * ∑ n ∈ B, ‖b n‖ ^ 2 := by
  rw [Finset.sum_product, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun m _ => Finset.sum_congr rfl fun n _ => ?_
  rw [norm_mul, mul_pow]

/-- **Head–tail decoupling.** -/
theorem integral_head_mul_tail {y : ℕ} {A B : Finset ℕ} (hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y)
    (hB : ∀ n ∈ B, IsRough y n) (r b : ℕ → ℂ) {N : ℕ} (hN : ∀ m ∈ A, ∀ n ∈ B, m * n ≤ N) (T : ℝ) :
    |(∫ t in T..(2 * T), ‖headPoly A r t‖ ^ 2 * ‖headPoly B b t‖ ^ 2) -
        T * ((∑ m ∈ A, ‖r m‖ ^ 2) * ∑ n ∈ B, ‖b n‖ ^ 2)| ≤
      8 * N * (1 + Real.log N) * ((∑ m ∈ A, ‖r m‖ ^ 2) * ∑ n ∈ B, ‖b n‖ ^ 2) := by
  have hA0 : ∀ m ∈ A, m ≠ 0 := fun m hm => Nat.ne_zero_of_mem_smoothNumbers (hA m hm)
  have hB0 : ∀ n ∈ B, n ≠ 0 := fun n hn => (hB n hn).1
  have hk : ∀ q ∈ A ×ˢ B, 1 ≤ q.1 * q.2 ∧ q.1 * q.2 ≤ N := by
    intro q hq
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hq
    exact ⟨Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (hA0 _ h1) (hB0 _ h2)), hN _ h1 _ h2⟩
  have hinj : Set.InjOn (fun q : ℕ × ℕ => q.1 * q.2) (A ×ˢ B : Finset (ℕ × ℕ)) := by
    intro q hq q' hq' h
    obtain ⟨h1, h2⟩ := Finset.mem_product.mp hq
    obtain ⟨h1', h2'⟩ := Finset.mem_product.mp hq'
    obtain ⟨e1, e2⟩ := smooth_mul_rough_injective (hA _ h1) (hA _ h1') (hB _ h2) (hB _ h2') h
    exact Prod.ext e1 e2
  have h := indexed_meanValue (fun q : ℕ × ℕ => r q.1 * b q.2) hk hinj T
  rw [sum_norm_sq_tensor] at h
  have e : (fun t => ‖indexedPoly (A ×ˢ B) (fun q => q.1 * q.2) (fun q => r q.1 * b q.2) t‖ ^ 2) =
      fun t => ‖headPoly A r t‖ ^ 2 * ‖headPoly B b t‖ ^ 2 := by
    funext t
    rw [← headPoly_mul A B r b hA0 hB0 t, norm_mul, mul_pow]
  rw [e] at h
  exact h

/-- The mean value of the head weight alone. -/
theorem integral_head_sq {A : Finset ℕ} (hA : ∀ m ∈ A, m ≠ 0) (r : ℕ → ℂ) {N : ℕ} (hN : ∀ m ∈ A, m ≤ N)
    (T : ℝ) :
    |(∫ t in T..(2 * T), ‖headPoly A r t‖ ^ 2) - T * ∑ m ∈ A, ‖r m‖ ^ 2| ≤
      8 * N * (1 + Real.log N) * ∑ m ∈ A, ‖r m‖ ^ 2 :=
  indexed_meanValue (E := A) (k := id) r (fun m hm => ⟨Nat.one_le_iff_ne_zero.mpr (hA m hm), hN m hm⟩)
    (fun _ _ _ _ h => h) T

/-- **The conditional second moment of the tail.** The head-weighted second moment of the tail is `‖b‖²` times the head
weight, up to `16 N log N ‖r‖²‖b‖²`. -/
theorem abs_conditional_second_moment_sub_le {y : ℕ} {A B : Finset ℕ} (hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y)
    (hB : ∀ n ∈ B, IsRough y n) (r b : ℕ → ℂ) {N : ℕ} (hAN : ∀ m ∈ A, m ≤ N)
    (hN : ∀ m ∈ A, ∀ n ∈ B, m * n ≤ N) (T : ℝ) :
    |(∫ t in T..(2 * T), ‖headPoly A r t‖ ^ 2 * ‖headPoly B b t‖ ^ 2) -
        (∫ t in T..(2 * T), ‖headPoly A r t‖ ^ 2) * ∑ n ∈ B, ‖b n‖ ^ 2| ≤
      16 * N * (1 + Real.log N) * ((∑ m ∈ A, ‖r m‖ ^ 2) * ∑ n ∈ B, ‖b n‖ ^ 2) := by
  have h1 := integral_head_mul_tail hA hB r b hN T
  have h2 := integral_head_sq (fun m hm => Nat.ne_zero_of_mem_smoothNumbers (hA m hm)) r hAN T
  have hb0 : 0 ≤ ∑ n ∈ B, ‖b n‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have h3 := mul_le_mul_of_nonneg_right h2 hb0
  rw [← abs_of_nonneg hb0, ← abs_mul, abs_of_nonneg hb0] at h3
  have e : (∫ t in T..(2 * T), ‖headPoly A r t‖ ^ 2) * ∑ n ∈ B, ‖b n‖ ^ 2 - T * ((∑ m ∈ A, ‖r m‖ ^ 2) *
      ∑ n ∈ B, ‖b n‖ ^ 2) = ((∫ t in T..(2 * T), ‖headPoly A r t‖ ^ 2) - T * ∑ m ∈ A, ‖r m‖ ^ 2) *
      ∑ n ∈ B, ‖b n‖ ^ 2 := by ring
  calc _ ≤ |(∫ t in T..(2 * T), ‖headPoly A r t‖ ^ 2 * ‖headPoly B b t‖ ^ 2) -
          T * ((∑ m ∈ A, ‖r m‖ ^ 2) * ∑ n ∈ B, ‖b n‖ ^ 2)| +
        |T * ((∑ m ∈ A, ‖r m‖ ^ 2) * ∑ n ∈ B, ‖b n‖ ^ 2) -
          (∫ t in T..(2 * T), ‖headPoly A r t‖ ^ 2) * ∑ n ∈ B, ‖b n‖ ^ 2| := abs_sub_le _ _ _
    _ = |(∫ t in T..(2 * T), ‖headPoly A r t‖ ^ 2 * ‖headPoly B b t‖ ^ 2) -
          T * ((∑ m ∈ A, ‖r m‖ ^ 2) * ∑ n ∈ B, ‖b n‖ ^ 2)| +
        |(∫ t in T..(2 * T), ‖headPoly A r t‖ ^ 2) * ∑ n ∈ B, ‖b n‖ ^ 2 -
          T * ((∑ m ∈ A, ‖r m‖ ^ 2) * ∑ n ∈ B, ‖b n‖ ^ 2)| := by rw [abs_sub_comm (T * _)]
    _ ≤ _ := by
        rw [e]
        have hN0 : (0 : ℝ) ≤ 8 * N * (1 + Real.log N) := by
          have : 0 ≤ Real.log (N : ℝ) := Real.log_natCast_nonneg N
          positivity
        nlinarith [h1, h3]

/-! ## The conditional mean of the tail -/

/-- `|∫_a^b e^{iλt} dt| ≤ 2/|λ|`. -/
theorem norm_integral_exp_le {lam : ℝ} (hlam : lam ≠ 0) (a b : ℝ) :
    ‖∫ t in a..b, Complex.exp (((t * lam : ℝ) : ℂ) * Complex.I)‖ ≤ 2 / |lam| := by
  have hc : ((lam : ℂ) * Complex.I) ≠ 0 := mul_ne_zero (by exact_mod_cast hlam) Complex.I_ne_zero
  have e : (fun t : ℝ => Complex.exp (((t * lam : ℝ) : ℂ) * Complex.I)) =
      fun t : ℝ => Complex.exp (((lam : ℂ) * Complex.I) * t) := by
    funext t
    push_cast
    ring_nf
  rw [e, integral_exp_mul_complex hc, norm_div]
  have h1 : ‖Complex.exp ((lam : ℂ) * Complex.I * b) - Complex.exp ((lam : ℂ) * Complex.I * a)‖ ≤ 2 := by
    refine (norm_sub_le _ _).trans ?_
    have hb : ‖Complex.exp ((lam : ℂ) * Complex.I * b)‖ = 1 := by
      rw [show (lam : ℂ) * Complex.I * b = ((lam * b : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    have ha : ‖Complex.exp ((lam : ℂ) * Complex.I * a)‖ = 1 := by
      rw [show (lam : ℂ) * Complex.I * a = ((lam * a : ℝ) : ℂ) * Complex.I by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    rw [hb, ha]
    norm_num
  have h2 : ‖(lam : ℂ) * Complex.I‖ = |lam| := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
  rw [h2]
  exact div_le_div_of_nonneg_right h1 (abs_nonneg lam)

theorem continuous_phase (lam : ℝ) : Continuous fun t : ℝ => Complex.exp (((t * lam : ℝ) : ℂ) * Complex.I) :=
  Complex.continuous_exp.comp ((Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).mul
    continuous_const)

/-- The head weight times the tail, expanded over triples. -/
theorem normSq_headPoly_mul (A B : Finset ℕ) (r b : ℕ → ℂ) (t : ℝ) :
    ((‖headPoly A r t‖ ^ 2 : ℝ) : ℂ) * headPoly B b t =
      ∑ m ∈ A, ∑ m' ∈ A, ∑ n ∈ B, (r m * (starRingEnd ℂ) (r m') * b n) *
        Complex.exp (((t * (Real.log m - Real.log m' + Real.log n) : ℝ) : ℂ) * Complex.I) := by
  have hsq : ((‖headPoly A r t‖ ^ 2 : ℝ) : ℂ) = headPoly A r t * (starRingEnd ℂ) (headPoly A r t) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hsq]
  unfold headPoly
  rw [map_sum, Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [map_mul, ← Complex.exp_conj]
  have hc : (starRingEnd ℂ) (((t * Real.log (m' : ℝ) : ℝ) : ℂ) * Complex.I) =
      ((-(t * Real.log (m' : ℝ)) : ℝ) : ℂ) * Complex.I := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [hc]
  have e : Complex.exp (((t * (Real.log m - Real.log m' + Real.log n) : ℝ) : ℂ) * Complex.I) =
      Complex.exp (((t * Real.log (m : ℝ) : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((-(t * Real.log (m' : ℝ)) : ℝ) : ℂ) * Complex.I) *
        Complex.exp (((t * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [e]
  ring

theorem sum_sum_sum_mul (A B : Finset ℕ) (f g : ℕ → ℝ) (C : ℝ) :
    ∑ m ∈ A, ∑ m' ∈ A, ∑ n ∈ B, C * (f m * f m' * g n) = C * ((∑ m ∈ A, f m) ^ 2 * ∑ n ∈ B, g n) := by
  rw [sq, Finset.sum_mul_sum (s := A) (t := A), Finset.sum_mul (s := A), Finset.mul_sum (s := A)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_mul (s := A), Finset.mul_sum (s := A)]
  refine Finset.sum_congr rfl fun m' _ => ?_
  rw [Finset.mul_sum (s := B), Finset.mul_sum (s := B)]

/-- **The conditional mean of the tail vanishes.** If the tail integers exceed `1`, the head-weighted integral of the
tail is at most `2N (Σ|r_m|)² Σ|b_n|`, for every window. -/
theorem norm_integral_head_sq_mul_tail_le {y : ℕ} {A B : Finset ℕ} (hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y)
    (hB : ∀ n ∈ B, IsRough y n) (hB1 : ∀ n ∈ B, 2 ≤ n) (r b : ℕ → ℂ) {N : ℕ} (hN1 : 1 ≤ N)
    (hAN : ∀ m ∈ A, m ≤ N) (hN : ∀ m ∈ A, ∀ n ∈ B, m * n ≤ N) (T₁ T₂ : ℝ) :
    ‖∫ t in T₁..T₂, ((‖headPoly A r t‖ ^ 2 : ℝ) : ℂ) * headPoly B b t‖ ≤
      2 * N * ((∑ m ∈ A, ‖r m‖) ^ 2 * ∑ n ∈ B, ‖b n‖) := by
  have hA0 : ∀ m ∈ A, m ≠ 0 := fun m hm => Nat.ne_zero_of_mem_smoothNumbers (hA m hm)
  simp_rw [normSq_headPoly_mul]
  have hc3 : ∀ m m' n : ℕ, Continuous fun t : ℝ => (r m * (starRingEnd ℂ) (r m') * b n) *
      Complex.exp (((t * (Real.log m - Real.log m' + Real.log n) : ℝ) : ℂ) * Complex.I) :=
    fun _ _ _ => continuous_const.mul (continuous_phase _)
  have hc2 : ∀ m m' : ℕ, Continuous fun t : ℝ => ∑ n ∈ B, (r m * (starRingEnd ℂ) (r m') * b n) *
      Complex.exp (((t * (Real.log m - Real.log m' + Real.log n) : ℝ) : ℂ) * Complex.I) :=
    fun m m' => continuous_finsetSum _ fun n _ => hc3 m m' n
  have hc1 : ∀ m : ℕ, Continuous fun t : ℝ => ∑ m' ∈ A, ∑ n ∈ B, (r m * (starRingEnd ℂ) (r m') * b n) *
      Complex.exp (((t * (Real.log m - Real.log m' + Real.log n) : ℝ) : ℂ) * Complex.I) :=
    fun m => continuous_finsetSum _ fun m' _ => hc2 m m'
  rw [intervalIntegral.integral_finsetSum fun m _ => (hc1 m).intervalIntegrable _ _]
  simp_rw [intervalIntegral.integral_finsetSum fun m' _ => (hc2 _ m').intervalIntegrable _ _]
  simp_rw [intervalIntegral.integral_finsetSum fun n _ => (hc3 _ _ n).intervalIntegrable _ _]
  -- Each frequency is at least `1/N` by the integer gap.
  have hterm : ∀ m ∈ A, ∀ m' ∈ A, ∀ n ∈ B,
      ‖∫ t in T₁..T₂, (r m * (starRingEnd ℂ) (r m') * b n) *
        Complex.exp (((t * (Real.log m - Real.log m' + Real.log n) : ℝ) : ℂ) * Complex.I)‖ ≤
        2 * N * (‖r m‖ * ‖r m'‖ * ‖b n‖) := by
    intro m hm m' hm' n hn
    rw [intervalIntegral.integral_const_mul, norm_mul, norm_mul, norm_mul, Complex.norm_conj]
    have hn0 : n ≠ 0 := (hB n hn).1
    have hne : m * n ≠ m' := by
      intro h
      obtain ⟨p, hp, hpn⟩ := Nat.exists_prime_and_dvd (by have := hB1 n hn; omega : n ≠ 1)
      have hpm' : p ∣ m' := h ▸ Dvd.dvd.mul_left hpn m
      have h1 := (Nat.mem_smoothNumbers'.mp (hA m' hm')) p hp hpm'
      have h2 := (hB n hn).2 p hp hpn
      omega
    have hlam : Real.log m - Real.log m' + Real.log n = Real.log ((m * n : ℕ) : ℝ) - Real.log (m' : ℝ) := by
      push_cast
      rw [Real.log_mul (by exact_mod_cast hA0 m hm) (by exact_mod_cast hn0)]
      ring
    have hmn0 : 0 < m * n := Nat.pos_of_ne_zero (Nat.mul_ne_zero (hA0 m hm) hn0)
    have hgap := HTGeometry.inv_max_le_abs_log_sub_log hmn0 (Nat.pos_of_ne_zero (hA0 m' hm')) hne
    have hmax : ((max (m * n) m' : ℕ) : ℝ) ≤ N := by
      exact_mod_cast max_le (hN m hm n hn) (hAN m' hm')
    have hmax0 : (0 : ℝ) < ((max (m * n) m' : ℕ) : ℝ) := by
      have : 0 < max (m * n) m' := lt_of_lt_of_le hmn0 (le_max_left _ _)
      exact_mod_cast this
    have hlam0 : Real.log m - Real.log m' + Real.log n ≠ 0 := by
      rw [hlam]
      intro h0
      rw [h0, abs_zero] at hgap
      exact absurd hgap (not_le.mpr (inv_pos.mpr hmax0))
    have hI := norm_integral_exp_le hlam0 T₁ T₂
    have hinv : 2 / |Real.log m - Real.log m' + Real.log n| ≤ 2 * N := by
      rw [hlam, div_le_iff₀ (lt_of_lt_of_le (inv_pos.mpr hmax0) hgap)]
      have h3 : 1 ≤ (N : ℝ) * |Real.log ((m * n : ℕ) : ℝ) - Real.log (m' : ℝ)| := by
        calc (1 : ℝ) = ((max (m * n) m' : ℕ) : ℝ) * ((max (m * n) m' : ℕ) : ℝ)⁻¹ := by field_simp
          _ ≤ (N : ℝ) * |Real.log ((m * n : ℕ) : ℝ) - Real.log (m' : ℝ)| :=
              mul_le_mul hmax hgap (by positivity) (by positivity)
      linarith
    have h0 : 0 ≤ ‖r m‖ * ‖r m'‖ * ‖b n‖ := by positivity
    calc ‖r m‖ * ‖r m'‖ * ‖b n‖ *
          ‖∫ t in T₁..T₂, Complex.exp (((t * (Real.log m - Real.log m' + Real.log n) : ℝ) : ℂ) * Complex.I)‖
        ≤ ‖r m‖ * ‖r m'‖ * ‖b n‖ * (2 * N) := mul_le_mul_of_nonneg_left (hI.trans hinv) h0
      _ = 2 * N * (‖r m‖ * ‖r m'‖ * ‖b n‖) := by ring
  calc ‖∑ m ∈ A, ∑ m' ∈ A, ∑ n ∈ B, ∫ t in T₁..T₂, (r m * (starRingEnd ℂ) (r m') * b n) *
        Complex.exp (((t * (Real.log m - Real.log m' + Real.log n) : ℝ) : ℂ) * Complex.I)‖
      ≤ ∑ m ∈ A, ∑ m' ∈ A, ∑ n ∈ B, 2 * N * (‖r m‖ * ‖r m'‖ * ‖b n‖) := by
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m hm => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun m' hm' => ?_)
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n hn => ?_)
        exact hterm m hm m' hm' n hn
    _ = 2 * N * ((∑ m ∈ A, ‖r m‖) ^ 2 * ∑ n ∈ B, ‖b n‖) :=
        sum_sum_sum_mul A B (fun m => ‖r m‖) (fun n => ‖b n‖) (2 * N)

end

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
