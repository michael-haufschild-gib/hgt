import Mathlib

/-!
# The single-qubit stabilizer two-design identity

The six single-qubit stabilizer amplitudes have the exact fourth-order moment of a two-design: the
average of the product of two amplitudes with two conjugate amplitudes is the sum of the two ways of
pairing the indices.  Equivalently, the second tensor power of the stabilizer ensemble is the
normalized projection onto the symmetric subspace.

The identity is the arithmetic core of the local-Clifford collision estimate: it is what turns the
fourth moment of an overlap with a product stabilizer state into a sum over subsets of the qubits.
-/

open Complex

noncomputable section

namespace GaloisForLFunctions.HTGeometry

section SingleQubit

/-- The six single-qubit stabilizer amplitudes, in terms of the reciprocal square root of two. -/
def stabAmp (s : ℂ) : Fin 6 → Fin 2 → ℂ :=
  ![![1, 0], ![0, 1], ![s, s], ![s, -s], ![s, s * I], ![s, -(s * I)]]

/-- **Single-qubit stabilizer two-design.**  The fourth-order amplitude moment is the sum of the
two index pairings. -/
theorem sum_stabAmp_four (s : ℂ) (hs : s * s = 1 / 2) (hsc : (starRingEnd ℂ) s = s)
    (x u y v : Fin 2) :
    (∑ t : Fin 6, stabAmp s t x * stabAmp s t u *
        (starRingEnd ℂ) (stabAmp s t y) * (starRingEnd ℂ) (stabAmp s t v)) =
      (if x = y then (1 : ℂ) else 0) * (if u = v then 1 else 0) +
        (if x = v then (1 : ℂ) else 0) * (if u = y then 1 else 0) := by
  have hs4 : s ^ 4 = 1 / 4 := by
    have h : s ^ 4 = (s * s) ^ 2 := by ring
    rw [h, hs]
    norm_num
  fin_cases x <;> fin_cases u <;> fin_cases y <;> fin_cases v <;>
    simp [stabAmp, Fin.sum_univ_six, hsc, Complex.conj_I] <;>
    ring_nf <;>
    simp [hs4, Complex.I_sq] <;>
    ring_nf

end SingleQubit

section ManyQubit

variable {n : ℕ}

/-- Amplitudes of a product stabilizer state on `n` qubits. -/
def prodStabAmp (s : ℂ) (σ : Fin n → Fin 6) (b : Fin n → Fin 2) : ℂ :=
  ∏ i, stabAmp s (σ i) (b i)

/-- The coordinate mix of two bit strings along a subset. -/
def mixOn (A : Finset (Fin n)) (b c : Fin n → Fin 2) : Fin n → Fin 2 :=
  fun i => if i ∈ A then b i else c i

theorem mixOn_involutive (A : Finset (Fin n)) (b c : Fin n → Fin 2) :
    mixOn A (mixOn A b c) (mixOn A c b) = b ∧ mixOn A (mixOn A c b) (mixOn A b c) = c := by
  constructor <;> funext i <;> by_cases hi : i ∈ A <;> simp [mixOn, hi]

/-- **Fourth-moment kernel of the product stabilizer ensemble.** -/
theorem sum_prodStabAmp_kernel (s : ℂ) (hs : s * s = 1 / 2) (hsc : (starRingEnd ℂ) s = s)
    (b c b' c' : Fin n → Fin 2) :
    (∑ σ : Fin n → Fin 6, prodStabAmp s σ b * prodStabAmp s σ c *
        (starRingEnd ℂ) (prodStabAmp s σ b') * (starRingEnd ℂ) (prodStabAmp s σ c')) =
      ∏ i, ((if b i = b' i then (1 : ℂ) else 0) * (if c i = c' i then 1 else 0) +
        (if b i = c' i then (1 : ℂ) else 0) * (if c i = b' i then 1 else 0)) := by
  classical
  have hfac : ∀ σ : Fin n → Fin 6,
      prodStabAmp s σ b * prodStabAmp s σ c *
        (starRingEnd ℂ) (prodStabAmp s σ b') * (starRingEnd ℂ) (prodStabAmp s σ c') =
      ∏ i, (stabAmp s (σ i) (b i) * stabAmp s (σ i) (c i) *
        (starRingEnd ℂ) (stabAmp s (σ i) (b' i)) *
        (starRingEnd ℂ) (stabAmp s (σ i) (c' i))) := by
    intro σ
    rw [prodStabAmp, prodStabAmp, prodStabAmp, prodStabAmp, map_prod, map_prod,
      ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  rw [Finset.sum_congr rfl fun σ _ => hfac σ]
  rw [show (Finset.univ : Finset (Fin n → Fin 6)) =
      Fintype.piFinset (fun _ : Fin n => (Finset.univ : Finset (Fin 6))) from
    (Fintype.piFinset_univ).symm]
  rw [← Finset.prod_univ_sum (fun _ : Fin n => (Finset.univ : Finset (Fin 6)))
    (fun (i : Fin n) (t : Fin 6) => stabAmp s t (b i) * stabAmp s t (c i) *
      (starRingEnd ℂ) (stabAmp s t (b' i)) * (starRingEnd ℂ) (stabAmp s t (c' i)))]
  exact Finset.prod_congr rfl fun i _ => sum_stabAmp_four s hs hsc (b i) (c i) (b' i) (c' i)

theorem prod_delta_eq (A : Finset (Fin n)) (b c b' c' : Fin n → Fin 2) :
    ((∏ i ∈ A, ((if b i = b' i then (1 : ℂ) else 0) * (if c i = c' i then 1 else 0))) *
      ∏ i ∈ Finset.univ \ A,
        ((if b i = c' i then (1 : ℂ) else 0) * (if c i = b' i then 1 else 0))) =
      if b' = mixOn A b c ∧ c' = mixOn A c b then 1 else 0 := by
  classical
  by_cases hcond : b' = mixOn A b c ∧ c' = mixOn A c b
  · rw [if_pos hcond]
    obtain ⟨hb', hc'⟩ := hcond
    have h1 : ∀ i ∈ A, ((if b i = b' i then (1 : ℂ) else 0) * (if c i = c' i then 1 else 0)) = 1 := by
      intro i hi
      rw [hb', hc']
      simp [mixOn, hi]
    have h2 : ∀ i ∈ Finset.univ \ A,
        ((if b i = c' i then (1 : ℂ) else 0) * (if c i = b' i then 1 else 0)) = 1 := by
      intro i hi
      rw [Finset.mem_sdiff] at hi
      rw [hb', hc']
      simp [mixOn, hi.2]
    rw [Finset.prod_congr rfl h1, Finset.prod_congr rfl h2, Finset.prod_const_one,
      Finset.prod_const_one, one_mul]
  · rw [if_neg hcond]
    have hex : ∃ i : Fin n, ¬ (b' i = mixOn A b c i ∧ c' i = mixOn A c b i) := by
      by_contra hall
      have hall' : ∀ i, b' i = mixOn A b c i ∧ c' i = mixOn A c b i := fun i =>
        not_not.mp (not_exists.mp hall i)
      exact hcond ⟨funext fun i => (hall' i).1, funext fun i => (hall' i).2⟩
    obtain ⟨i, hi⟩ := hex
    by_cases hiA : i ∈ A
    · refine mul_eq_zero_of_left (Finset.prod_eq_zero (i := i) hiA ?_) _
      simp only [mixOn, if_pos hiA] at hi
      by_cases h1 : b i = b' i
      · by_cases h2 : c i = c' i
        · exact absurd ⟨h1.symm, h2.symm⟩ hi
        · rw [if_neg h2, mul_zero]
      · rw [if_neg h1, zero_mul]
    · refine mul_eq_zero_of_right _ (Finset.prod_eq_zero (i := i) ?_ ?_)
      · exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, hiA⟩
      · simp only [mixOn, if_neg hiA] at hi
        by_cases h1 : b i = c' i
        · by_cases h2 : c i = b' i
          · exact absurd ⟨h2.symm, h1.symm⟩ hi
          · rw [if_neg h2, mul_zero]
        · rw [if_neg h1, zero_mul]


/-- The mixing involution on pairs of bit strings. -/
def mixSwap (A : Finset (Fin n)) : ((Fin n → Fin 2) × (Fin n → Fin 2)) →
    ((Fin n → Fin 2) × (Fin n → Fin 2)) :=
  fun p => (mixOn A p.1 p.2, mixOn A p.2 p.1)

theorem mixSwap_involutive (A : Finset (Fin n)) : Function.Involutive (mixSwap A) := by
  intro p
  obtain ⟨b, c⟩ := p
  obtain ⟨h1, h2⟩ := mixOn_involutive A b c
  simp only [mixSwap]
  rw [h1, h2]

/-- **Subset term bound.**  Each mixing term of the fourth moment is bounded by the square of the
squared norm. -/
theorem norm_mix_term_le (e : (Fin n → Fin 2) → ℂ) (A : Finset (Fin n)) :
    ‖∑ b, ∑ c, ((starRingEnd ℂ) (e b) * (starRingEnd ℂ) (e c) *
        e (mixOn A b c) * e (mixOn A c b))‖ ≤ (∑ b, ‖e b‖ ^ 2) ^ 2 := by
  classical
  set P : ℝ := ∑ b, ‖e b‖ ^ 2 with hP
  set F : ((Fin n → Fin 2) × (Fin n → Fin 2)) → ℝ := fun p => ‖e p.1‖ * ‖e p.2‖ with hF
  have hFnn : ∀ p, 0 ≤ F p := fun p => by positivity
  have hprod : ∀ p : (Fin n → Fin 2) × (Fin n → Fin 2),
      ‖(starRingEnd ℂ) (e p.1) * (starRingEnd ℂ) (e p.2) *
        e (mixOn A p.1 p.2) * e (mixOn A p.2 p.1)‖ = F p * F (mixSwap A p) := by
    intro p
    rw [norm_mul, norm_mul, norm_mul, RCLike.norm_conj, RCLike.norm_conj, hF]
    simp only [mixSwap]
    ring
  have hsumF : (∑ p : (Fin n → Fin 2) × (Fin n → Fin 2), F p ^ 2) = P ^ 2 := by
    rw [hF, Fintype.sum_prod_type]
    rw [hP, sq, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => by ring
  have hsumG : (∑ p : (Fin n → Fin 2) × (Fin n → Fin 2), F (mixSwap A p) ^ 2) = P ^ 2 := by
    rw [← hsumF]
    exact Fintype.sum_equiv ((mixSwap_involutive A).toPerm) _ _ fun p => rfl
  have hcs : (∑ p : (Fin n → Fin 2) × (Fin n → Fin 2), F p * F (mixSwap A p)) ≤ P ^ 2 := by
    have hbase : (∑ p : (Fin n → Fin 2) × (Fin n → Fin 2), F p * F (mixSwap A p)) ^ 2 ≤
        (∑ p : (Fin n → Fin 2) × (Fin n → Fin 2), F p ^ 2) *
          ∑ p : (Fin n → Fin 2) × (Fin n → Fin 2), F (mixSwap A p) ^ 2 :=
      Finset.sum_mul_sq_le_sq_mul_sq _ _ _
    rw [hsumF, hsumG] at hbase
    have hnn : 0 ≤ ∑ p : (Fin n → Fin 2) × (Fin n → Fin 2), F p * F (mixSwap A p) :=
      Finset.sum_nonneg fun p _ => mul_nonneg (hFnn p) (hFnn _)
    nlinarith [hnn, sq_nonneg (P ^ 2)]
  calc ‖∑ b, ∑ c, ((starRingEnd ℂ) (e b) * (starRingEnd ℂ) (e c) *
          e (mixOn A b c) * e (mixOn A c b))‖
      = ‖∑ p : (Fin n → Fin 2) × (Fin n → Fin 2), ((starRingEnd ℂ) (e p.1) *
          (starRingEnd ℂ) (e p.2) * e (mixOn A p.1 p.2) * e (mixOn A p.2 p.1))‖ := by
        rw [Fintype.sum_prod_type]
    _ ≤ ∑ p : (Fin n → Fin 2) × (Fin n → Fin 2), ‖(starRingEnd ℂ) (e p.1) *
          (starRingEnd ℂ) (e p.2) * e (mixOn A p.1 p.2) * e (mixOn A p.2 p.1)‖ :=
        norm_sum_le _ _
    _ = ∑ p : (Fin n → Fin 2) × (Fin n → Fin 2), F p * F (mixSwap A p) :=
        Finset.sum_congr rfl fun p _ => hprod p
    _ ≤ P ^ 2 := hcs


/-- **Local-Clifford collision law.**  The total fourth moment of the overlaps with the `6^n`
product stabilizer states is at most `2^n` times the square of the squared norm. -/
theorem sum_prodStab_fourth_le (s : ℂ) (hs : s * s = 1 / 2) (hsc : (starRingEnd ℂ) s = s)
    (e : (Fin n → Fin 2) → ℂ) :
    (∑ σ : Fin n → Fin 6, ‖∑ b, (starRingEnd ℂ) (e b) * prodStabAmp s σ b‖ ^ 4) ≤
      2 ^ n * (∑ b, ‖e b‖ ^ 2) ^ 2 := by
  classical
  set P : ℝ := ∑ b, ‖e b‖ ^ 2 with hP
  set W : (Fin n → Fin 6) → ℂ := fun σ => ∑ b, (starRingEnd ℂ) (e b) * prodStabAmp s σ b with hW
  set E : ((Fin n → Fin 2) × (Fin n → Fin 2)) → ℂ := fun p => e p.1 * e p.2 with hE
  set Φ : (Fin n → Fin 6) → ((Fin n → Fin 2) × (Fin n → Fin 2)) → ℂ :=
    fun σ p => prodStabAmp s σ p.1 * prodStabAmp s σ p.2 with hΦ
  have hsq : ∀ σ, W σ ^ 2 = ∑ p, (starRingEnd ℂ) (E p) * Φ σ p := by
    intro σ
    rw [hW, sq, Finset.sum_mul_sum, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
    rw [hE, hΦ, map_mul]
    ring
  have hpt : ∀ σ, ((‖W σ‖ ^ 4 : ℝ) : ℂ) = (W σ ^ 2) * (starRingEnd ℂ) (W σ ^ 2) := by
    intro σ
    have h2 : ((‖W σ ^ 2‖ ^ 2 : ℝ) : ℂ) = (W σ ^ 2) * (starRingEnd ℂ) (W σ ^ 2) := by
      rw [Complex.mul_conj]
      norm_cast
      exact Complex.sq_norm _
    rw [← h2, norm_pow, ← pow_mul]
  have hkernel : ∀ p q : (Fin n → Fin 2) × (Fin n → Fin 2),
      (∑ σ : Fin n → Fin 6, Φ σ p * (starRingEnd ℂ) (Φ σ q)) =
        ∑ A ∈ (Finset.univ : Finset (Fin n)).powerset,
          if q = mixSwap A p then (1 : ℂ) else 0 := by
    intro p q
    have hΦexp : ∀ σ : Fin n → Fin 6, Φ σ p * (starRingEnd ℂ) (Φ σ q) =
        prodStabAmp s σ p.1 * prodStabAmp s σ p.2 *
          (starRingEnd ℂ) (prodStabAmp s σ q.1) * (starRingEnd ℂ) (prodStabAmp s σ q.2) := by
      intro σ
      rw [hΦ, map_mul]
      ring
    rw [Finset.sum_congr rfl fun σ _ => hΦexp σ,
      sum_prodStabAmp_kernel s hs hsc p.1 p.2 q.1 q.2, Finset.prod_add]
    refine Finset.sum_congr rfl fun A _ => ?_
    rw [prod_delta_eq A p.1 p.2 q.1 q.2]
    exact if_congr ⟨fun h => Prod.ext h.1 h.2,
      fun h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩⟩ rfl rfl
  have hstep : ∀ σ : Fin n → Fin 6, (W σ ^ 2) * (starRingEnd ℂ) (W σ ^ 2) =
      ∑ p, ∑ q, ((starRingEnd ℂ) (E p) * E q) * (Φ σ p * (starRingEnd ℂ) (Φ σ q)) := by
    intro σ
    rw [hsq σ, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    simp only [map_mul, Complex.conj_conj]
    ring
  have hmain : ((∑ σ : Fin n → Fin 6, ‖W σ‖ ^ 4 : ℝ) : ℂ) =
      ∑ A ∈ (Finset.univ : Finset (Fin n)).powerset,
        ∑ p, (starRingEnd ℂ) (E p) * E (mixSwap A p) := by
    rw [Complex.ofReal_sum, Finset.sum_congr rfl fun σ _ => hpt σ,
      Finset.sum_congr rfl fun σ _ => hstep σ, Finset.sum_comm]
    have hp2 : ∀ p : (Fin n → Fin 2) × (Fin n → Fin 2),
        (∑ σ : Fin n → Fin 6, ∑ q,
            ((starRingEnd ℂ) (E p) * E q) * (Φ σ p * (starRingEnd ℂ) (Φ σ q))) =
          ∑ A ∈ (Finset.univ : Finset (Fin n)).powerset,
            (starRingEnd ℂ) (E p) * E (mixSwap A p) := by
      intro p
      rw [Finset.sum_comm]
      have hinner : ∀ q : (Fin n → Fin 2) × (Fin n → Fin 2),
          (∑ σ : Fin n → Fin 6,
              ((starRingEnd ℂ) (E p) * E q) * (Φ σ p * (starRingEnd ℂ) (Φ σ q))) =
            ∑ A ∈ (Finset.univ : Finset (Fin n)).powerset,
              ((starRingEnd ℂ) (E p) * E q) * (if q = mixSwap A p then (1 : ℂ) else 0) := by
        intro q
        rw [← Finset.mul_sum, hkernel p q, Finset.mul_sum]
      rw [Finset.sum_congr rfl fun q _ => hinner q, Finset.sum_comm]
      refine Finset.sum_congr rfl fun A _ => ?_
      rw [Finset.sum_eq_single (mixSwap A p)]
      · rw [if_pos rfl, mul_one]
      · intro q _ hq
        rw [if_neg hq, mul_zero]
      · intro hcon
        exact absurd (Finset.mem_univ (mixSwap A p)) hcon
    rw [Finset.sum_congr rfl fun p _ => hp2 p]
    exact Finset.sum_comm
  have hterm : ∀ A : Finset (Fin n),
      ‖∑ p, (starRingEnd ℂ) (E p) * E (mixSwap A p)‖ ≤ P ^ 2 := by
    intro A
    have hrw : (∑ p, (starRingEnd ℂ) (E p) * E (mixSwap A p)) =
        ∑ b, ∑ c, ((starRingEnd ℂ) (e b) * (starRingEnd ℂ) (e c) *
          e (mixOn A b c) * e (mixOn A c b)) := by
      rw [Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun c _ => ?_
      rw [hE, map_mul]
      simp only [mixSwap]
      ring
    rw [hrw, hP]
    exact norm_mix_term_le e A
  have hnn : 0 ≤ ∑ σ : Fin n → Fin 6, ‖W σ‖ ^ 4 :=
    Finset.sum_nonneg fun σ _ => by positivity
  have hbound : (∑ σ : Fin n → Fin 6, ‖W σ‖ ^ 4) ≤ 2 ^ n * P ^ 2 := by
    have hcast : (∑ σ : Fin n → Fin 6, ‖W σ‖ ^ 4) =
        ‖((∑ σ : Fin n → Fin 6, ‖W σ‖ ^ 4 : ℝ) : ℂ)‖ := by
      rw [Complex.norm_real, Real.norm_of_nonneg hnn]
    rw [hcast, hmain]
    refine le_trans (norm_sum_le _ _) ?_
    calc (∑ A ∈ (Finset.univ : Finset (Fin n)).powerset,
            ‖∑ p, (starRingEnd ℂ) (E p) * E (mixSwap A p)‖)
        ≤ ∑ _A ∈ (Finset.univ : Finset (Fin n)).powerset, P ^ 2 :=
          Finset.sum_le_sum fun A _ => hterm A
      _ = 2 ^ n * P ^ 2 := by
          rw [Finset.sum_const, Finset.card_powerset, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul]
          push_cast
          ring
  exact hbound


/-- **Collision average over the product stabilizer ensemble.**  Summing the collision of a fixed
orthonormal family over all product stabilizer inputs costs one factor of the family size times the
qubit power of two; the normalized average is therefore at most the family size times three to the
minus qubit number. -/
theorem sum_collision_le (s : ℂ) (hs : s * s = 1 / 2) (hsc : (starRingEnd ℂ) s = s)
    {D : Type*} [Fintype D] (e : D → (Fin n → Fin 2) → ℂ) (he : ∀ j, ∑ b, ‖e j b‖ ^ 2 = 1) :
    (∑ σ : Fin n → Fin 6, ∑ j : D,
        ‖∑ b, (starRingEnd ℂ) (e j b) * prodStabAmp s σ b‖ ^ 4) ≤
      (Fintype.card D : ℝ) * 2 ^ n := by
  classical
  rw [Finset.sum_comm]
  calc (∑ j : D, ∑ σ : Fin n → Fin 6,
        ‖∑ b, (starRingEnd ℂ) (e j b) * prodStabAmp s σ b‖ ^ 4)
      ≤ ∑ _j : D, (2 : ℝ) ^ n := by
        refine Finset.sum_le_sum fun j _ => ?_
        have hbase := sum_prodStab_fourth_le s hs hsc (e j)
        rw [he j, one_pow, mul_one] at hbase
        exact hbase
    _ = (Fintype.card D : ℝ) * 2 ^ n := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end ManyQubit


end GaloisForLFunctions.HTGeometry
