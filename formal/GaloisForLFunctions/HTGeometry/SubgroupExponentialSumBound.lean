import GaloisForLFunctions.HTGeometry.ShiftedSubgroupStepanov

/-!
# Exponential sums over multiplicative subgroups beyond the square-root barrier

For `g ∈ (ℤ/p)ˣ` of order `t` and `S(a) = Σ_{s<t} e(a gˢ/p)`:

* `S(a gᵏ) = S(a)` (`subgroupSum_mul_pow`), so a nonzero `a` contributes `t` equal values to the
  fourth moment;
* `Σ_y |S(y)|⁴ = p · E(H)` with `E(H)` the additive energy of `H = ⟨g⟩` (`sum_norm_pow_four`);
* `E(H) ≤ t² (1 + 4B²)` by the Heath-Brown–Konyagin bound `|H ∩ (H + λ)| < 4B²`
  (`energy_le`).

Hence `|S(a)|⁴ ≤ p t (1 + 4B²)` for `a ≠ 0` (`norm_subgroupSum_pow_four_le`); with
`B ≍ t^{1/3}` this is `|S(a)| ≪ p^{1/4} t^{5/12}`, nontrivial as soon as `t ≥ p^{3/7+ε}` — below
the range `t > √p` of the Gauss-sum bound.
-/

open Finset

namespace GaloisForLFunctions.HTGeometry.ShiftedSubgroup

variable {p : ℕ} [Fact p.Prime]

instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

/-- The subgroup sum `S(a) = Σ_{s<t} e(a gˢ/p)`. -/
noncomputable def subgroupSum (g : ZMod p) (t : ℕ) (a : ZMod p) : ℂ :=
  ∑ s : Fin t, ZMod.stdAddChar (a * g ^ (s : ℕ))

theorem sum_range_shift_of_periodic {t : ℕ} {f : ℕ → ℂ} (hf : ∀ n, f (n + t) = f n) (k : ℕ) :
    ∑ s ∈ range t, f (k + s) = ∑ s ∈ range t, f s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← ih]
    rcases Nat.eq_zero_or_pos t with h0 | ht
    · subst h0; simp
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    rw [sum_range_succ, sum_range_succ']
    rw [show k + 1 + t' = k + (t' + 1) by ring, hf, add_zero]
    congr 1
    exact sum_congr rfl fun n _ => by congr 1; ring

/-- `S(a gᵏ) = S(a)` when `gᵗ = 1`. -/
theorem subgroupSum_mul_pow {g : ZMod p} {t : ℕ} (hg : g ^ t = 1) (a : ZMod p) (k : ℕ) :
    subgroupSum g t (a * g ^ k) = subgroupSum g t a := by
  unfold subgroupSum
  rw [Fin.sum_univ_eq_sum_range (fun s => ZMod.stdAddChar (a * g ^ k * g ^ s)),
    Fin.sum_univ_eq_sum_range (fun s => ZMod.stdAddChar (a * g ^ s))]
  have hf : ∀ n, ZMod.stdAddChar (a * g ^ (n + t)) = ZMod.stdAddChar (a * g ^ n) := by
    intro n; rw [pow_add, hg, mul_one]
  rw [← sum_range_shift_of_periodic (f := fun n => ZMod.stdAddChar (a * g ^ n)) hf k]
  exact sum_congr rfl fun s _ => by rw [mul_assoc, ← pow_add]

/-- The additive energy of `{gˢ : s < t}`. -/
noncomputable def energy (g : ZMod p) (t : ℕ) : ℕ :=
  (univ.filter fun q : Fin t × Fin t × Fin t × Fin t =>
    g ^ (q.1 : ℕ) + g ^ (q.2.1 : ℕ) = g ^ (q.2.2.1 : ℕ) + g ^ (q.2.2.2 : ℕ)).card

theorem subgroupSum_fourth (g : ZMod p) (t : ℕ) (y : ZMod p) :
    subgroupSum g t y * subgroupSum g t y * starRingEnd ℂ (subgroupSum g t y) *
        starRingEnd ℂ (subgroupSum g t y) =
      ∑ q : Fin t × Fin t × Fin t × Fin t, ZMod.stdAddChar (y * (g ^ (q.2.2.1 : ℕ) +
        g ^ (q.2.2.2 : ℕ) - g ^ (q.1 : ℕ) - g ^ (q.2.1 : ℕ))) := by
  have hconj : starRingEnd ℂ (subgroupSum g t y) =
      ∑ s : Fin t, ZMod.stdAddChar (-(y * g ^ (s : ℕ))) := by
    unfold subgroupSum
    rw [map_sum]
    exact sum_congr rfl fun s _ => (AddChar.map_neg_eq_conj _ _).symm
  rw [hconj]
  unfold subgroupSum
  simp only [Finset.sum_mul, Finset.mul_sum, Fintype.sum_prod_type]
  refine sum_congr rfl fun s1 _ => sum_congr rfl fun s2 _ => sum_congr rfl fun s3 _ =>
    sum_congr rfl fun s4 _ => ?_
  rw [← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul]
  congr 1; ring

/-- **Fourth moment.**  `Σ_y |S(y)|⁴ = p · E`. -/
theorem sum_norm_pow_four (g : ZMod p) (t : ℕ) :
    ∑ y : ZMod p, ‖subgroupSum g t y‖ ^ 4 = p * (energy g t : ℝ) := by
  apply Complex.ofReal_injective
  push_cast
  have hn : ∀ y : ZMod p, ((‖subgroupSum g t y‖ ^ 4 : ℝ) : ℂ) =
      subgroupSum g t y * subgroupSum g t y * starRingEnd ℂ (subgroupSum g t y) *
        starRingEnd ℂ (subgroupSum g t y) := by
    intro y
    have h := Complex.mul_conj (subgroupSum g t y)
    rw [Complex.normSq_eq_norm_sq] at h
    calc ((‖subgroupSum g t y‖ ^ 4 : ℝ) : ℂ) = ((‖subgroupSum g t y‖ ^ 2 : ℝ) : ℂ) ^ 2 := by
          push_cast; ring
      _ = _ := by rw [← h]; ring
  simp_rw [← Complex.ofReal_pow] at hn ⊢
  rw [Finset.sum_congr rfl fun y _ => hn y]
  simp_rw [subgroupSum_fourth]
  rw [Finset.sum_comm]
  simp_rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar p), ZMod.card]
  rw [energy, Finset.card_filter, Nat.cast_sum, Finset.mul_sum]
  refine sum_congr rfl fun q _ => ?_
  have hiff : (g ^ (q.2.2.1 : ℕ) + g ^ (q.2.2.2 : ℕ) - g ^ (q.1 : ℕ) - g ^ (q.2.1 : ℕ) = 0) ↔
      (g ^ (q.1 : ℕ) + g ^ (q.2.1 : ℕ) = g ^ (q.2.2.1 : ℕ) + g ^ (q.2.2.2 : ℕ)) := by
    constructor <;> intro h
    · linear_combination -h
    · linear_combination -h
  by_cases hq : g ^ (q.1 : ℕ) + g ^ (q.2.1 : ℕ) = g ^ (q.2.2.1 : ℕ) + g ^ (q.2.2.2 : ℕ)
  · rw [if_pos (hiff.mpr hq), if_pos hq]; push_cast; ring
  · rw [if_neg (fun h => hq (hiff.mp h)), if_neg hq]; push_cast; ring

theorem pow_injective_fin {g : ZMod p} {t : ℕ} (hord : orderOf g = t) {s s' : Fin t}
    (h : g ^ (s : ℕ) = g ^ (s' : ℕ)) : s = s' :=
  Fin.ext (pow_injOn_Iio_orderOf (x := g) (by rw [hord]; exact s.isLt)
    (by rw [hord]; exact s'.isLt) h)

/-- **Energy bound.**  `E ≤ t² (1 + 4B²)` from the Heath-Brown–Konyagin bound. -/
theorem energy_le {g : ZMod p} {t B : ℕ} (hord : orderOf g = t) (hB : 0 < B)
    (hB3 : 3 * t ≤ 2 * B ^ 3) (h2B : 2 * B ≤ t) (htB : t * B ≤ p) :
    energy g t ≤ t * t + t * t * (4 * B ^ 2) := by
  classical
  have ht : 0 < t := by omega
  have hgt : g ^ t = 1 := by rw [← hord]; exact pow_orderOf_eq_one g
  have hg0 : g ≠ 0 := by
    rintro rfl; rw [zero_pow (by omega)] at hgt; exact zero_ne_one hgt
  set P : Fin t → Fin t → Fin t → Fin t → Prop := fun s1 s2 s3 s4 =>
    g ^ (s1 : ℕ) + g ^ (s2 : ℕ) = g ^ (s3 : ℕ) + g ^ (s4 : ℕ)
  have hE : energy g t = ∑ s1 : Fin t, ∑ s3 : Fin t, ∑ s2 : Fin t, ∑ s4 : Fin t,
      (if P s1 s2 s3 s4 then 1 else 0) := by
    rw [energy, card_filter]
    simp only [Fintype.sum_prod_type]
    exact sum_congr rfl fun s1 _ => Finset.sum_comm
  -- the inner count
  have hinner : ∀ s1 s3 : Fin t, ∑ s2 : Fin t, ∑ s4 : Fin t, (if P s1 s2 s3 s4 then 1 else 0) ≤
      (if s1 = s3 then t else 0) + 4 * B ^ 2 := by
    intro s1 s3
    by_cases h13 : s1 = s3
    · rw [if_pos h13]
      subst h13
      have : ∀ s2 : Fin t, ∑ s4 : Fin t, (if P s1 s2 s1 s4 then 1 else 0) ≤ 1 := by
        intro s2
        rw [← card_filter]
        refine card_le_one.mpr fun u hu v hv => ?_
        simp only [mem_filter, mem_univ, true_and, P, add_right_inj] at hu hv
        exact (pow_injective_fin hord hu).symm.trans (pow_injective_fin hord hv)
      calc ∑ s2 : Fin t, ∑ s4 : Fin t, (if P s1 s2 s1 s4 then 1 else 0)
          ≤ ∑ _s2 : Fin t, 1 := sum_le_sum fun s2 _ => this s2
        _ = t := by simp
        _ ≤ t + 4 * B ^ 2 := Nat.le_add_right _ _
    · rw [if_neg h13, zero_add]
      set μ := g ^ (s1 : ℕ) - g ^ (s3 : ℕ)
      have hμ : μ ≠ 0 := fun h0 => h13 (pow_injective_fin hord (sub_eq_zero.mp h0))
      set T := (univ : Finset (Fin t × Fin t)).filter fun q => P s1 q.1 s3 q.2
      have hT : ∑ s2 : Fin t, ∑ s4 : Fin t, (if P s1 s2 s3 s4 then 1 else 0) = T.card := by
        rw [card_filter, Fintype.sum_prod_type]
      rw [hT]
      set Sμ := (univ : Finset (ZMod p)).filter fun x =>
        x ≠ 0 ∧ x ≠ μ ∧ x ^ t = 1 ∧ (x - μ) ^ t = 1
      have hmaps : ∀ q ∈ T, g ^ (q.2 : ℕ) ∈ Sμ := by
        intro q hq
        simp only [T, mem_filter, mem_univ, true_and, P] at hq
        have hsub : g ^ (q.2 : ℕ) - μ = g ^ (q.1 : ℕ) := by simp only [μ]; linear_combination -hq
        simp only [Sμ, mem_filter, mem_univ, true_and]
        refine ⟨pow_ne_zero _ hg0, fun h => ?_, ?_, ?_⟩
        · rw [h, sub_self] at hsub; exact pow_ne_zero _ hg0 hsub.symm
        · rw [← pow_mul, mul_comm, pow_mul, hgt, one_pow]
        · rw [hsub, ← pow_mul, mul_comm, pow_mul, hgt, one_pow]
      have hinj : Set.InjOn (fun q : Fin t × Fin t => g ^ (q.2 : ℕ)) T := by
        intro u hu v hv huv
        simp only [T, coe_filter, mem_univ, true_and, Set.mem_setOf_eq, P] at hu hv
        have h2 : u.2 = v.2 := pow_injective_fin hord huv
        have h1 : g ^ (u.1 : ℕ) = g ^ (v.1 : ℕ) := by
          have huv' : g ^ (u.2 : ℕ) = g ^ (v.2 : ℕ) := huv
          linear_combination hu - hv + huv'
        exact Prod.ext (pow_injective_fin hord h1) h2
      have hcard : T.card ≤ Sμ.card := card_le_card_of_injOn _ hmaps hinj
      have hS : ∀ x ∈ Sμ, x ≠ 0 ∧ x ≠ μ ∧ x ^ t = 1 ∧ (x - μ) ^ t = 1 := by
        intro x hx; simpa [Sμ] using hx
      exact (hcard.trans (card_shifted_lt hμ hB hB3 h2B htB 1 1 Sμ hS).le)
  rw [hE]
  calc ∑ s1 : Fin t, ∑ s3 : Fin t, ∑ s2 : Fin t, ∑ s4 : Fin t, (if P s1 s2 s3 s4 then 1 else 0)
      ≤ ∑ s1 : Fin t, ∑ s3 : Fin t, ((if s1 = s3 then t else 0) + 4 * B ^ 2) :=
        sum_le_sum fun s1 _ => sum_le_sum fun s3 _ => hinner s1 s3
    _ = t * t + t * t * (4 * B ^ 2) := by
        simp only [sum_add_distrib, sum_ite_eq, mem_univ, if_true, sum_const, card_univ,
          Fintype.card_fin, smul_eq_mul]
        ring

/-- **Subgroup sums beyond `√p`.**  If `g` has order `t` in `(ℤ/p)ˣ`, `B ≥ 1`, `3t ≤ 2B³`,
`2B ≤ t` and `tB ≤ p`, then `|Σ_{s<t} e(a gˢ/p)|⁴ ≤ p t (1 + 4B²)` for every `a ≠ 0`. -/
theorem norm_subgroupSum_pow_four_le {g : ZMod p} {t B : ℕ} (hord : orderOf g = t) (hB : 0 < B)
    (hB3 : 3 * t ≤ 2 * B ^ 3) (h2B : 2 * B ≤ t) (htB : t * B ≤ p) {a : ZMod p} (ha : a ≠ 0) :
    ‖subgroupSum g t a‖ ^ 4 ≤ p * t * (1 + 4 * B ^ 2) := by
  classical
  have ht : 0 < t := by omega
  have hgt : g ^ t = 1 := by rw [← hord]; exact pow_orderOf_eq_one g
  have himg : ∑ k : Fin t, ‖subgroupSum g t (a * g ^ (k : ℕ))‖ ^ 4 ≤
      ∑ y : ZMod p, ‖subgroupSum g t y‖ ^ 4 := by
    rw [← Finset.sum_image (f := fun y => ‖subgroupSum g t y‖ ^ 4)
      (s := (univ : Finset (Fin t))) (g := fun k : Fin t => a * g ^ (k : ℕ))]
    · exact sum_le_sum_of_subset_of_nonneg (subset_univ _) fun y _ _ => by positivity
    · intro u _ v _ huv
      exact pow_injective_fin hord (mul_left_cancel₀ ha huv)
  have hleft : ∑ k : Fin t, ‖subgroupSum g t (a * g ^ (k : ℕ))‖ ^ 4 =
      t * ‖subgroupSum g t a‖ ^ 4 := by
    simp_rw [subgroupSum_mul_pow hgt]
    simp
  rw [hleft, sum_norm_pow_four] at himg
  have hE := energy_le hord hB hB3 h2B htB
  have hE' : (energy g t : ℝ) ≤ t * t * (1 + 4 * B ^ 2) := by
    have : ((energy g t : ℕ) : ℝ) ≤ ((t * t + t * t * (4 * B ^ 2) : ℕ) : ℝ) := by exact_mod_cast hE
    push_cast at this; linarith
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have hp0 : (0 : ℝ) ≤ p := by positivity
  have := mul_le_mul_of_nonneg_left hE' hp0
  have h2 : (t : ℝ) * ‖subgroupSum g t a‖ ^ 4 ≤ t * (p * t * (1 + 4 * B ^ 2)) := by nlinarith
  exact le_of_mul_le_mul_left h2 htR

end GaloisForLFunctions.HTGeometry.ShiftedSubgroup
