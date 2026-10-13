import GaloisForLFunctions.RHTower.JointAncestryRandomPhaseParseval

/-!
# Orbits of the global phase shift and the moments of a linear phase sum

On the phase torus `(ℤ/N)^ι` the global shift `k ↦ k + j·1` is a bijection for every `j`.
Hence the number of phase vectors in any set is the orbit average
`#A = (1/N) Σ_k #{j : k + j·1 ∈ A}` (`card_filter_mul_eq_sum_card_shift`).

For the linear phase sum `Z(k) = Σ_i a_i ω^{−k_i}` with real coefficients:
* `Σ_k |Z|² = N^{|ι|} V` with `V = Σ a_i²` (`sum_normSq_linearPhaseSum`);
* `Σ_k |Z|⁴ ≤ 2 N^{|ι|} V²` for `N ≥ 3` (`sum_normSq_sq_linearPhaseSum_le`);
* Paley–Zygmund: `|Z|² ≥ V/2` on at least `N^{|ι|}/8` vectors
  (`card_half_le_normSq_linearPhaseSum`);
* Chebyshev: `|Z|² > R²` on at most `N^{|ι|} V / R²` vectors
  (`card_lt_normSq_linearPhaseSum_le`).

The fourth moment is Parseval for the off-diagonal part
`|Z|² − V = Σ_{i ≠ i'} a_i a_{i'} ω^{−k_i} ω^{k_{i'}}`: its terms are distinct characters of the
torus.
-/

open Complex Finset
open scoped ComplexConjugate

namespace RHTower

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## The global shift -/

/-- The global phase shift `k ↦ k + j·1`. -/
def phaseShift {N : ℕ} (j : Fin N) (k : ι → Fin N) : ι → Fin N := fun i => k i + j

omit [Fintype ι] [DecidableEq ι] in
theorem phaseShift_bijective {N : ℕ} [NeZero N] (j : Fin N) :
    Function.Bijective (phaseShift (ι := ι) j) := by
  refine ⟨fun k k' h => funext fun i => ?_, fun k => ⟨fun i => k i - j, funext fun i => ?_⟩⟩
  · have := congrFun h i; simpa [phaseShift] using this
  · simp only [phaseShift]; exact sub_add_cancel _ _

/-- **Orbit counting.**  `N · #A = Σ_k #{j : k + j·1 ∈ A}`. -/
theorem card_filter_mul_eq_sum_card_shift {N : ℕ} [NeZero N] (A : (ι → Fin N) → Prop) [DecidablePred A] :
    ((univ.filter A).card : ℝ) * N =
      ∑ k : ι → Fin N, ((univ.filter fun j : Fin N => A (phaseShift j k)).card : ℝ) := by
  have hj : ∀ j : Fin N, ((univ.filter fun k : ι → Fin N => A (phaseShift j k)).card : ℝ) =
      (univ.filter A).card := by
    intro j
    have := Finset.card_bij (s := univ.filter fun k : ι → Fin N => A (phaseShift j k))
      (t := univ.filter A) (fun k _ => phaseShift j k)
      (fun k hk => by simpa using hk)
      (fun k _ k' _ h => (phaseShift_bijective j).1 h)
      (fun k hk => by
        obtain ⟨k', rfl⟩ := (phaseShift_bijective j).2 k
        exact ⟨k', by simpa using hk, rfl⟩)
    exact_mod_cast this
  have hswap : ∑ k : ι → Fin N, ((univ.filter fun j : Fin N => A (phaseShift j k)).card : ℝ) =
      ∑ j : Fin N, ((univ.filter fun k : ι → Fin N => A (phaseShift j k)).card : ℝ) := by
    simp only [Finset.card_filter]
    push_cast
    exact Finset.sum_comm
  rw [hswap, Finset.sum_congr rfl fun j _ => hj j]
  simp [mul_comm]

/-- `ω^{k + j} = ω^k ω^j` in `ℤ/N`. -/
theorem unitRoot_pow_add_fin {N : ℕ} (hN : 0 < N) (k j : Fin N) :
    unitRoot N ^ ((k + j : Fin N) : ℕ) = unitRoot N ^ (k : ℕ) * unitRoot N ^ (j : ℕ) := by
  have hprim := isPrimitiveRoot_unitRoot (N := N) hN.ne'
  rw [Fin.val_add, ← pow_add]
  conv_rhs => rw [← Nat.mod_add_div ((k : ℕ) + j) N, pow_add, pow_mul, hprim.pow_eq_one, one_pow,
    mul_one]

/-! ## The linear phase sum -/

/-- `Z(k) = Σ_i a_i ω^{−k_i}`. -/
def linearPhaseSum {N : ℕ} (a : ι → ℝ) (k : ι → Fin N) : ℂ :=
  ∑ i, (a i : ℂ) * conj (unitRoot N ^ ((k i : Fin N) : ℕ))

omit [DecidableEq ι] in
theorem linearPhaseSum_shift {N : ℕ} (hN : 0 < N) (a : ι → ℝ) (j : Fin N) (k : ι → Fin N) :
    linearPhaseSum a (phaseShift j k) = conj (unitRoot N ^ (j : ℕ)) * linearPhaseSum a k := by
  unfold linearPhaseSum phaseShift
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [unitRoot_pow_add_fin hN, map_mul]; ring

/-- The single conjugate character at `i`. -/
def conjCharAt (i : ι) : ι → Fin 3 := fun t => if t = i then 2 else 0

omit [Fintype ι] in
theorem conjCharAt_injective : Function.Injective (conjCharAt (ι := ι)) := by
  intro i i' h
  have := congrFun h i
  by_contra hne
  simp [conjCharAt, hne] at this

theorem jasPhaseCharVec_conjCharAt {N : ℕ} (i : ι) (k : ι → Fin N) :
    jasPhaseCharVec N (conjCharAt i) k = conj (unitRoot N ^ ((k i : Fin N) : ℕ)) := by
  unfold jasPhaseCharVec conjCharAt
  rw [Finset.prod_eq_single i]
  · simp [jasPhaseChar]
  · intro t _ ht; simp [ht, jasPhaseChar]
  · simp

/-- **Second moment.** -/
theorem sum_normSq_linearPhaseSum {N : ℕ} (hN : 3 ≤ N) (a : ι → ℝ) :
    ∑ k : ι → Fin N, ‖linearPhaseSum a k‖ ^ 2 = (N : ℝ) ^ Fintype.card ι * ∑ i, a i ^ 2 := by
  have h := sum_normSq_sum_jasPhaseCharVec (ι := ι) hN (univ.image conjCharAt)
    (fun e => ∑ i, if conjCharAt i = e then (a i : ℂ) else 0)
  have hZ : ∀ k : ι → Fin N, linearPhaseSum a k = ∑ e ∈ univ.image conjCharAt,
      (∑ i, if conjCharAt i = e then (a i : ℂ) else 0) * jasPhaseCharVec N e k := by
    intro k
    rw [Finset.sum_image fun i _ i' _ hii' => conjCharAt_injective hii']
    unfold linearPhaseSum
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_eq_single i, if_pos rfl, jasPhaseCharVec_conjCharAt]
    · intro t _ ht; rw [if_neg]; exact fun h => ht (conjCharAt_injective h)
    · simp
  simp_rw [hZ]
  rw [h, Finset.sum_image fun i _ i' _ hii' => conjCharAt_injective hii']
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i, if_pos rfl, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  · intro t _ ht; rw [if_neg]; exact fun h => ht (conjCharAt_injective h)
  · simp

/-- The off-diagonal character `ω^{−k_i} ω^{k_{i'}}`. -/
def pairCharAt (x : ι × ι) : ι → Fin 3 := fun t => if t = x.1 then 2 else if t = x.2 then 1 else 0

theorem pairCharAt_injOn :
    Set.InjOn (pairCharAt (ι := ι)) (univ.offDiag : Finset (ι × ι)) := by
  rintro ⟨i, i'⟩ hx ⟨l, l'⟩ hy h
  simp only [coe_offDiag, coe_univ, Set.mem_offDiag, Set.mem_univ, true_and] at hx hy
  have h1 := congrFun h i
  have h2 := congrFun h i'
  simp only [pairCharAt] at h1 h2
  by_cases hil : i = l
  · subst hil
    by_cases hil' : i' = l'
    · subst hil'; rfl
    · simp [Ne.symm hx, hil'] at h2
  · split_ifs at h1 with ha hb <;> simp_all

theorem jasPhaseCharVec_pairCharAt {N : ℕ} {x : ι × ι} (hx : x.1 ≠ x.2) (k : ι → Fin N) :
    jasPhaseCharVec N (pairCharAt x) k =
      conj (unitRoot N ^ ((k x.1 : Fin N) : ℕ)) * unitRoot N ^ ((k x.2 : Fin N) : ℕ) := by
  unfold jasPhaseCharVec pairCharAt
  rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ x.1),
    ← Finset.prod_erase_mul _ _ (Finset.mem_erase.mpr ⟨Ne.symm hx, Finset.mem_univ x.2⟩)]
  rw [Finset.prod_eq_one]
  · simp [jasPhaseChar, Ne.symm hx, mul_comm]
  · intro t ht
    have h1 : t ≠ x.2 := (Finset.mem_erase.mp ht).1
    have h2 : t ≠ x.1 := (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
    simp [jasPhaseChar, h1, h2]

/-- `|Z|² = V + Σ_{i ≠ i'} a_i a_{i'} ω^{−k_i}ω^{k_{i'}}`. -/
theorem normSq_linearPhaseSum_eq {N : ℕ} (a : ι → ℝ) (k : ι → Fin N) :
    ((‖linearPhaseSum a k‖ ^ 2 : ℝ) : ℂ) = ((∑ i, a i ^ 2 : ℝ) : ℂ) +
      ∑ x ∈ (univ.offDiag : Finset (ι × ι)), ((a x.1 * a x.2 : ℝ) : ℂ) *
        jasPhaseCharVec N (pairCharAt x) k := by
  have hn : ((‖linearPhaseSum a k‖ ^ 2 : ℝ) : ℂ) =
      linearPhaseSum a k * conj (linearPhaseSum a k) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hn]
  unfold linearPhaseSum
  rw [map_sum, Finset.sum_mul_sum]
  have hsplit := Finset.sum_product' (s := (univ : Finset ι)) (t := (univ : Finset ι))
    (f := fun i i' => (a i : ℂ) * conj (unitRoot N ^ ((k i : Fin N) : ℕ)) *
      conj ((a i' : ℂ) * conj (unitRoot N ^ ((k i' : Fin N) : ℕ))))
  rw [← hsplit, ← Finset.diag_union_offDiag,
    Finset.sum_union (Finset.disjoint_diag_offDiag _)]
  congr 1
  · rw [Finset.sum_diag]
    push_cast
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
    have h' : conj (unitRoot N ^ ((k i : Fin N) : ℕ)) * unitRoot N ^ ((k i : Fin N) : ℕ) = 1 := by
      rw [mul_comm]; exact unitRoot_pow_mul_conj N (k i : ℕ)
    linear_combination ((a i : ℂ) ^ 2) * h'
  · refine Finset.sum_congr rfl fun x hx => ?_
    have hx' : x.1 ≠ x.2 := (Finset.mem_offDiag.mp hx).2.2
    rw [jasPhaseCharVec_pairCharAt hx']
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_conj]
    push_cast; ring

/-- **Fourth moment.** -/
theorem sum_normSq_sq_linearPhaseSum_le {N : ℕ} (hN : 3 ≤ N) (a : ι → ℝ) :
    ∑ k : ι → Fin N, (‖linearPhaseSum a k‖ ^ 2) ^ 2 ≤
      2 * (N : ℝ) ^ Fintype.card ι * (∑ i, a i ^ 2) ^ 2 := by
  set V := ∑ i, a i ^ 2 with hV
  set D : (ι → Fin N) → ℂ := fun k => ∑ x ∈ (univ.offDiag : Finset (ι × ι)),
    ((a x.1 * a x.2 : ℝ) : ℂ) * jasPhaseCharVec N (pairCharAt x) k with hD
  have hdecomp : ∀ k, ((‖linearPhaseSum a k‖ ^ 2 : ℝ) : ℂ) = (V : ℂ) + D k :=
    fun k => normSq_linearPhaseSum_eq a k
  have hDre : ∀ k, D k = (((‖linearPhaseSum a k‖ ^ 2 - V : ℝ)) : ℂ) := by
    intro k
    have h := hdecomp k
    rw [Complex.ofReal_sub, h]; ring
  -- Parseval for `D`
  have hpars : ∑ k : ι → Fin N, ‖D k‖ ^ 2 =
      (N : ℝ) ^ Fintype.card ι * ∑ x ∈ (univ.offDiag : Finset (ι × ι)), (a x.1 * a x.2) ^ 2 := by
    have h := sum_normSq_sum_jasPhaseCharVec (ι := ι) hN
      ((univ.offDiag : Finset (ι × ι)).image pairCharAt)
      (fun e => ∑ x ∈ (univ.offDiag : Finset (ι × ι)),
        if pairCharAt x = e then ((a x.1 * a x.2 : ℝ) : ℂ) else 0)
    have hDk : ∀ k, D k = ∑ e ∈ (univ.offDiag : Finset (ι × ι)).image pairCharAt,
        (∑ x ∈ (univ.offDiag : Finset (ι × ι)),
          if pairCharAt x = e then ((a x.1 * a x.2 : ℝ) : ℂ) else 0) *
            jasPhaseCharVec N e k := by
      intro k
      rw [Finset.sum_image fun x hx y hy hxy => pairCharAt_injOn hx hy hxy]
      refine Finset.sum_congr rfl fun x hx => ?_
      rw [Finset.sum_eq_single x, if_pos rfl]
      · intro y hy hyx; rw [if_neg]; exact fun h => hyx (pairCharAt_injOn hy hx h)
      · intro h; exact absurd hx h
    simp_rw [hDk]
    rw [h, Finset.sum_image fun x hx y hy hxy => pairCharAt_injOn hx hy hxy]
    congr 1
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [Finset.sum_eq_single x, if_pos rfl, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    · intro y hy hyx; rw [if_neg]; exact fun h => hyx (pairCharAt_injOn hy hx h)
    · intro h; exact absurd hx h
  have hoff : ∑ x ∈ (univ.offDiag : Finset (ι × ι)), (a x.1 * a x.2) ^ 2 ≤ V ^ 2 := by
    have hsq : V ^ 2 = ∑ x ∈ (univ : Finset ι) ×ˢ (univ : Finset ι), (a x.1 * a x.2) ^ 2 := by
      rw [hV, sq, Finset.sum_mul_sum, ← Finset.sum_product']
      refine Finset.sum_congr rfl fun x _ => by ring
    rw [hsq]
    exact Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => by
      simp only [Finset.mem_offDiag] at hx; simp) (fun x _ _ => sq_nonneg _)
  have hsum0 : ∑ k : ι → Fin N, (‖linearPhaseSum a k‖ ^ 2 - V) = 0 := by
    rw [Finset.sum_sub_distrib, sum_normSq_linearPhaseSum hN, Finset.sum_const, Finset.card_univ,
      Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
    push_cast; ring
  have hDn : ∀ k, ‖D k‖ ^ 2 = (‖linearPhaseSum a k‖ ^ 2 - V) ^ 2 := by
    intro k; rw [hDre k, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hexp : ∀ k : ι → Fin N, (‖linearPhaseSum a k‖ ^ 2) ^ 2 =
      V ^ 2 + 2 * V * (‖linearPhaseSum a k‖ ^ 2 - V) + ‖D k‖ ^ 2 := by
    intro k; rw [hDn k]; ring
  simp_rw [hexp]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, hsum0, hpars,
    Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, nsmul_eq_mul]
  push_cast
  have hNp : (0 : ℝ) ≤ (N : ℝ) ^ Fintype.card ι := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hoff hNp]

/-! ## Counting bounds -/

/-- **Paley–Zygmund on the phase torus.**  `|Z|² ≥ V/2` on at least `N^{|ι|}/8` vectors. -/
theorem card_half_le_normSq_linearPhaseSum {N : ℕ} (hN : 3 ≤ N) (a : ι → ℝ)
    (hV : 0 < ∑ i, a i ^ 2) :
    (N : ℝ) ^ Fintype.card ι / 8 ≤
      ((univ.filter fun k : ι → Fin N =>
        (∑ i, a i ^ 2) / 2 ≤ ‖linearPhaseSum a k‖ ^ 2).card : ℝ) := by
  set V := ∑ i, a i ^ 2
  set n : ℝ := (N : ℝ) ^ Fintype.card ι
  have hn : 0 < n := by positivity
  set G := univ.filter fun k : ι → Fin N => V / 2 ≤ ‖linearPhaseSum a k‖ ^ 2
  have h2 := sum_normSq_linearPhaseSum (ι := ι) hN a
  have h4 := sum_normSq_sq_linearPhaseSum_le (ι := ι) hN a
  -- the mass on `G`
  have hmass : n * V / 2 ≤ ∑ k ∈ G, ‖linearPhaseSum a k‖ ^ 2 := by
    have hsplit := Finset.sum_filter_add_sum_filter_not (univ : Finset (ι → Fin N))
      (fun k => V / 2 ≤ ‖linearPhaseSum a k‖ ^ 2) (fun k => ‖linearPhaseSum a k‖ ^ 2)
    have hlow : ∑ k ∈ univ.filter (fun k : ι → Fin N => ¬ V / 2 ≤ ‖linearPhaseSum a k‖ ^ 2),
        ‖linearPhaseSum a k‖ ^ 2 ≤ n * (V / 2) := by
      calc _ ≤ ∑ _k ∈ univ.filter (fun k : ι → Fin N => ¬ V / 2 ≤ ‖linearPhaseSum a k‖ ^ 2),
            V / 2 := Finset.sum_le_sum fun k hk => (not_le.mp (Finset.mem_filter.mp hk).2).le
        _ ≤ ∑ _k : ι → Fin N, V / 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              (fun _ _ _ => by positivity)
        _ = n * (V / 2) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
              nsmul_eq_mul]
            push_cast; ring
    have : ∑ k : ι → Fin N, ‖linearPhaseSum a k‖ ^ 2 = n * V := h2
    linarith
  -- Cauchy–Schwarz on `G`
  have hcs : (∑ k ∈ G, ‖linearPhaseSum a k‖ ^ 2) ^ 2 ≤
      (G.card : ℝ) * ∑ k ∈ G, (‖linearPhaseSum a k‖ ^ 2) ^ 2 := by
    have := Finset.sum_mul_sq_le_sq_mul_sq G (fun _ => (1 : ℝ)) (fun k => ‖linearPhaseSum a k‖ ^ 2)
    simpa using this
  have hG4 : ∑ k ∈ G, (‖linearPhaseSum a k‖ ^ 2) ^ 2 ≤ 2 * n * V ^ 2 :=
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => by positivity)).trans h4
  have hG0 : (0 : ℝ) ≤ G.card := Nat.cast_nonneg _
  have key : (n * V / 2) ^ 2 ≤ (G.card : ℝ) * (2 * n * V ^ 2) := by
    have h0 : 0 ≤ n * V / 2 := by positivity
    calc (n * V / 2) ^ 2 ≤ (∑ k ∈ G, ‖linearPhaseSum a k‖ ^ 2) ^ 2 := by gcongr
      _ ≤ _ := hcs
      _ ≤ _ := mul_le_mul_of_nonneg_left hG4 hG0
  have hnV : 0 < n * V ^ 2 := by positivity
  have : n * V ^ 2 * (n / 8) ≤ n * V ^ 2 * (G.card : ℝ) := by nlinarith
  exact le_of_mul_le_mul_left this hnV

/-- **Chebyshev on the phase torus.** -/
theorem card_lt_normSq_linearPhaseSum_le {N : ℕ} (hN : 3 ≤ N) (a : ι → ℝ) {R : ℝ} (hR : 0 < R) :
    ((univ.filter fun k : ι → Fin N => R ^ 2 < ‖linearPhaseSum a k‖ ^ 2).card : ℝ) ≤
      (N : ℝ) ^ Fintype.card ι * (∑ i, a i ^ 2) / R ^ 2 := by
  rw [le_div_iff₀ (by positivity)]
  have h2 := sum_normSq_linearPhaseSum (ι := ι) hN a
  calc ((univ.filter fun k : ι → Fin N => R ^ 2 < ‖linearPhaseSum a k‖ ^ 2).card : ℝ) * R ^ 2
      = ∑ _k ∈ univ.filter (fun k : ι → Fin N => R ^ 2 < ‖linearPhaseSum a k‖ ^ 2), R ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ univ.filter (fun k : ι → Fin N => R ^ 2 < ‖linearPhaseSum a k‖ ^ 2),
        ‖linearPhaseSum a k‖ ^ 2 := Finset.sum_le_sum fun k hk => (Finset.mem_filter.mp hk).2.le
    _ ≤ ∑ k : ι → Fin N, ‖linearPhaseSum a k‖ ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun _ _ _ => by positivity)
    _ = _ := h2

/-- **Markov on a finite set.** -/
theorem card_lt_le_sum_div {α : Type*} [Fintype α] (f : α → ℝ) (hf : ∀ x, 0 ≤ f x) {t : ℝ}
    (ht : 0 < t) : ((univ.filter fun x => t < f x).card : ℝ) ≤ (∑ x, f x) / t := by
  rw [le_div_iff₀ ht]
  calc ((univ.filter fun x => t < f x).card : ℝ) * t = ∑ _x ∈ univ.filter (fun x => t < f x), t := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ univ.filter (fun x => t < f x), f x :=
        Finset.sum_le_sum fun x hx => (Finset.mem_filter.mp hx).2.le
    _ ≤ ∑ x, f x := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun x _ _ => hf x)

end

end RHTower
