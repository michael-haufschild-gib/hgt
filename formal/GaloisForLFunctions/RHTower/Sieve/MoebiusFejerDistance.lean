import GaloisForLFunctions.RHTower.Sieve.MoebiusPairDamping
import GaloisForLFunctions.RHTower.AtlasBlindToUnfolded

/-!
# The sign-sensitive distance bound with ratio `(K−1)/K`

`two_mul_sum_inv_div_five_le_max` is the case `K = 2` of a family.  Writing `θ_p = t·log p`, the
positivity of the pair-correlation form

`0 ≤ ∑_{j,k < K+1} cos((j − k)θ)`

— which is `|∑_{j<K+1} e^{ijθ}|² ≥ 0`, the Fejér kernel — gives, for `f(p) = −1` and
`A = ∑_{p ∈ P}1/p`,

`∑_{j,k < K+1} 𝔻(f, n^{i(j−k)t})² ≥ (K+1)²·A`,

while the `K+1` diagonal terms contribute exactly `2(K+1)A`.  Averaging over the `(K+1)K`
off-diagonal pairs,

`max_{1 ≤ k ≤ K} 𝔻(f, n^{ikt})² ≥ ((K−1)/K)·A`,

whose `K = 2` case is the `2/5` of the pair bound and whose limit is the full mass `A`.  So among the
frequencies `t, 2t, …, Kt` at least one is at distance `√((1−1/K)A)` from `f`, unconditionally and with
no zero-free region: the whole content is that `f(p) = −1`, i.e. the sign of the coefficients.
-/

noncomputable section
namespace RHTower.Sieve
open Finset

/-- The distance to a character is even in the frequency. -/
theorem mulDistSqPair_neg_one_charFn_neg {f : ℕ → ℂ} {P : Finset ℕ} (hneg : ∀ p ∈ P, f p = -1)
    (u : ℝ) :
    mulDistSqPair f (charFn (-u)) P = mulDistSqPair f (charFn u) P := by
  rw [mulDistSqPair_neg_one_charFn hneg, mulDistSqPair_neg_one_charFn hneg]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [show -u * Real.log (p : ℝ) = -(u * Real.log (p : ℝ)) by ring, Real.cos_neg]

/-- **The pair-correlation lower bound for the doubled distance sum.** -/
theorem sq_le_sum_sum_mulDistSqPair {f : ℕ → ℂ} {P : Finset ℕ} (hneg : ∀ p ∈ P, f p = -1)
    (hP : ∀ p ∈ P, 0 < p) (K : ℕ) (t : ℝ) :
    (((K : ℝ) + 1) ^ 2) * (∑ p ∈ P, 1 / (p : ℝ))
      ≤ ∑ j : Fin (K + 1), ∑ k : Fin (K + 1),
          mulDistSqPair f (charFn ((((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) * t) ) P := by
  classical
  set G : Fin (K + 1) → Fin (K + 1) → ℕ → ℝ := fun j k p =>
    (1 + Real.cos ((((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) * t * Real.log (p : ℝ))) / (p : ℝ) with hG
  have hval : ∀ j k : Fin (K + 1),
      mulDistSqPair f (charFn ((((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) * t)) P = ∑ p ∈ P, G j k p := by
    intro j k
    rw [hG]
    exact mulDistSqPair_neg_one_charFn hneg _
  -- the double sum of distances is a `p`-sum of pair-correlation forms
  have hswap : (∑ j : Fin (K + 1), ∑ k : Fin (K + 1),
        mulDistSqPair f (charFn ((((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) * t)) P)
      = ∑ p ∈ P, ∑ j : Fin (K + 1), ∑ k : Fin (K + 1), G j k p := by
    rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => hval j k]
    rw [Finset.sum_congr rfl fun j (_ : j ∈ (Finset.univ : Finset (Fin (K + 1)))) =>
      (Finset.sum_comm (s := (Finset.univ : Finset (Fin (K + 1)))) (t := P)
        (f := fun k p => G j k p))]
    exact Finset.sum_comm
  -- the mass side is a `p`-sum too
  have hmass : (((K : ℝ) + 1) ^ 2) * (∑ p ∈ P, 1 / (p : ℝ))
      = ∑ p ∈ P, (((K : ℝ) + 1) ^ 2) / (p : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by rw [mul_one_div]
  rw [hswap, hmass]
  refine Finset.sum_le_sum fun p hp => ?_
  have hp0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hP p hp
  have hcos := RHTower.pair_correlation_nonneg (n := K + 1) (fun _ => (1 : ℝ))
    (fun j => ((j : ℕ) : ℝ)) (t * Real.log (p : ℝ))
  have hcongr : ∑ j : Fin (K + 1), ∑ k : Fin (K + 1),
        (1 : ℝ) * 1 * Real.cos (t * Real.log (p : ℝ) * (((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)))
      = ∑ j : Fin (K + 1), ∑ k : Fin (K + 1),
        Real.cos ((((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) * t * Real.log (p : ℝ)) := by
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    rw [one_mul, one_mul]
    congr 1
    ring
  rw [hcongr] at hcos
  have hexpand : (∑ j : Fin (K + 1), ∑ k : Fin (K + 1), G j k p)
      = (((K : ℝ) + 1) ^ 2) / (p : ℝ)
        + (∑ j : Fin (K + 1), ∑ k : Fin (K + 1),
            Real.cos ((((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) * t * Real.log (p : ℝ))) / (p : ℝ) := by
    have hinner : ∀ j : Fin (K + 1), (∑ k : Fin (K + 1), G j k p)
        = (((K : ℝ) + 1) / (p : ℝ))
          + (∑ k : Fin (K + 1),
              Real.cos ((((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) * t * Real.log (p : ℝ))) / (p : ℝ) := by
      intro j
      rw [hG]
      rw [Finset.sum_div (s := (Finset.univ : Finset (Fin (K + 1))))]
      rw [show (∑ k : Fin (K + 1),
            (1 + Real.cos ((((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) * t * Real.log (p : ℝ))) / (p : ℝ))
          = ∑ k : Fin (K + 1),
              (1 / (p : ℝ)
                + Real.cos ((((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) * t * Real.log (p : ℝ)) / (p : ℝ)) from
        Finset.sum_congr rfl fun k _ => by rw [add_div]]
      rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      push_cast
      ring
    rw [Finset.sum_congr rfl fun j (_ : j ∈ (Finset.univ : Finset (Fin (K + 1)))) => hinner j]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Finset.sum_div (s := (Finset.univ : Finset (Fin (K + 1))))]
    push_cast
    ring
  rw [hexpand]
  have hdiv : (0 : ℝ) ≤ (∑ j : Fin (K + 1), ∑ k : Fin (K + 1),
      Real.cos ((((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) * t * Real.log (p : ℝ))) / (p : ℝ) :=
    div_nonneg hcos hp0.le
  linarith

/-- **The sign-sensitive distance bound.**  Among the frequencies `t, 2t, …, Kt` at least one is at
squared distance `((K−1)/K)·∑_{p ∈ P}1/p` from `f`.  At `K = 2` this is the `2/5` of
`two_mul_sum_inv_div_five_le_max`; the ratio tends to `1`. -/
theorem exists_mulDistSqPair_ge_of_neg_one {f : ℕ → ℂ} {P : Finset ℕ} (hneg : ∀ p ∈ P, f p = -1)
    (hP : ∀ p ∈ P, 0 < p) {K : ℕ} (hK : 1 ≤ K) (t : ℝ) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧
      (((K : ℝ) - 1) / (K : ℝ)) * (∑ p ∈ P, 1 / (p : ℝ))
        ≤ mulDistSqPair f (charFn ((k : ℝ) * t)) P := by
  classical
  set A : ℝ := ∑ p ∈ P, 1 / (p : ℝ) with hA
  have hA0 : (0 : ℝ) ≤ A := by
    rw [hA]
    refine Finset.sum_nonneg fun p hp => ?_
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hP p hp
    positivity
  have hKR : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
  have hbase := sq_le_sum_sum_mulDistSqPair hneg hP K t
  rw [← hA] at hbase
  have hpeel : ∀ j : Fin (K + 1),
      (∑ k : Fin (K + 1), mulDistSqPair f (charFn ((((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) * t)) P)
        = 2 * A + ∑ k ∈ (Finset.univ.erase j),
            mulDistSqPair f (charFn ((((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) * t)) P := by
    intro j
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    congr 1
    have hzero : (((j : ℕ) : ℝ) - ((j : ℕ) : ℝ)) * t = 0 := by ring
    rw [hzero, hA]
    exact mulDistSqPair_neg_one_zero hneg
  have hoff : ((K : ℝ) + 1) * ((K : ℝ) - 1) * A
      ≤ ∑ j : Fin (K + 1), ∑ k ∈ (Finset.univ.erase j),
          mulDistSqPair f (charFn ((((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) * t)) P := by
    have hsum : (∑ j : Fin (K + 1), ∑ k : Fin (K + 1),
          mulDistSqPair f (charFn ((((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) * t)) P)
        = ((K : ℝ) + 1) * (2 * A)
          + ∑ j : Fin (K + 1), ∑ k ∈ (Finset.univ.erase j),
              mulDistSqPair f (charFn ((((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) * t)) P := by
      rw [Finset.sum_congr rfl fun j (_ : j ∈ (Finset.univ : Finset (Fin (K + 1)))) => hpeel j,
        Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]
      push_cast
      ring
    rw [hsum] at hbase
    nlinarith [hbase]
  have hnonempty : (Finset.univ : Finset (Fin (K + 1))).Nonempty :=
    Finset.univ_nonempty (α := Fin (K + 1))
  have havg1 : ∑ _j : Fin (K + 1), (((K : ℝ) - 1) * A)
      ≤ ∑ j : Fin (K + 1), ∑ k ∈ (Finset.univ.erase j),
          mulDistSqPair f (charFn ((((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) * t)) P := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    nlinarith [hoff]
  obtain ⟨j, -, hj⟩ := Finset.exists_le_of_sum_le hnonempty havg1
  have hcard : (((Finset.univ.erase j).card : ℕ) : ℝ) = (K : ℝ) := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin]
    push_cast
    ring
  have hne : (Finset.univ.erase j).Nonempty := by
    refine Finset.card_pos.1 ?_
    have hpos : (0 : ℝ) < (((Finset.univ.erase j).card : ℕ) : ℝ) := by rw [hcard]; exact hK0
    exact_mod_cast hpos
  have havg2 : ∑ _k ∈ (Finset.univ.erase j), ((((K : ℝ) - 1) / (K : ℝ)) * A)
      ≤ ∑ k ∈ (Finset.univ.erase j),
          mulDistSqPair f (charFn ((((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) * t)) P := by
    rw [Finset.sum_const, nsmul_eq_mul, hcard]
    have hval : (K : ℝ) * ((((K : ℝ) - 1) / (K : ℝ)) * A) = ((K : ℝ) - 1) * A := by
      field_simp
    rw [hval]
    exact hj
  obtain ⟨k, hkmem, hk⟩ := Finset.exists_le_of_sum_le hne havg2
  have hjk : (j : ℕ) ≠ (k : ℕ) := by
    intro h
    exact (Finset.ne_of_mem_erase hkmem) (Fin.ext h).symm
  have hjlt : (j : ℕ) < K + 1 := j.isLt
  have hklt : (k : ℕ) < K + 1 := k.isLt
  rcases le_total (k : ℕ) (j : ℕ) with hle | hle
  · refine ⟨(j : ℕ) - (k : ℕ), by omega, by omega, ?_⟩
    have hcast : (((j : ℕ) - (k : ℕ) : ℕ) : ℝ) = ((j : ℕ) : ℝ) - ((k : ℕ) : ℝ) := by
      rw [Nat.cast_sub hle]
    rw [hcast]
    exact hk
  · refine ⟨(k : ℕ) - (j : ℕ), by omega, by omega, ?_⟩
    have hcast : (((k : ℕ) - (j : ℕ) : ℕ) : ℝ) = -(((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) := by
      rw [Nat.cast_sub hle]
      ring
    rw [hcast, show -(((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) * t
        = -((((j : ℕ) : ℝ) - ((k : ℕ) : ℝ)) * t) by ring,
      mulDistSqPair_neg_one_charFn_neg hneg]
    exact hk

/-- **The damping consequence.**  Among `t, 2t, …, Kt` at least one frequency has a smooth sum of size
`exp(A/K + B)`, where `A = ∑_{p ∈ P}1/p` and `B = ∑_{p ∈ P}1/p²`.  The trivial bound is `exp(A + B)`, so
the saving is `exp(−(1 − 1/K)A)`: at `P = {p ≤ z}` a factor `(log z)^{-(1-1/K)}`, unconditional and with
no distance hypothesis. -/
theorem exists_norm_smoothMulSum_le_of_neg_one {f : ℕ → ℂ} (hf : ∀ n, ‖f n‖ ≤ 1)
    (hmul : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b) (h1 : f 1 = 1)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hneg : ∀ p ∈ P, f p = -1) {K : ℕ} (hK : 1 ≤ K)
    (t : ℝ) :
    ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧
      ‖smoothMulSum f P ((k : ℝ) * t)‖
        ≤ Real.exp ((∑ p ∈ P, 1 / (p : ℝ)) / (K : ℝ) + ∑ p ∈ P, 1 / (p : ℝ) ^ 2) := by
  classical
  have hPpos : ∀ p ∈ P, 0 < p := fun p hp => (hP p hp).pos
  set A : ℝ := ∑ p ∈ P, 1 / (p : ℝ) with hA
  set B : ℝ := ∑ p ∈ P, 1 / (p : ℝ) ^ 2 with hB
  have hA0 : (0 : ℝ) ≤ A := by
    rw [hA]
    refine Finset.sum_nonneg fun p hp => ?_
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hPpos p hp
    positivity
  have hKR : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK
  have hK0 : (0 : ℝ) < (K : ℝ) := by linarith
  obtain ⟨k, hk1, hkK, hk⟩ := exists_mulDistSqPair_ge_of_neg_one hneg hPpos hK t
  rw [← hA] at hk
  refine ⟨k, hk1, hkK, ?_⟩
  set δ : ℝ := Real.sqrt ((((K : ℝ) - 1) / (K : ℝ)) * A) with hδdef
  have hratio : (0 : ℝ) ≤ (((K : ℝ) - 1) / (K : ℝ)) * A := by
    have h1' : (0 : ℝ) ≤ ((K : ℝ) - 1) / (K : ℝ) := div_nonneg (by linarith) hK0.le
    exact mul_nonneg h1' hA0
  have hδ0 : (0 : ℝ) ≤ δ := Real.sqrt_nonneg _
  have hδsq : δ ^ 2 = (((K : ℝ) - 1) / (K : ℝ)) * A := Real.sq_sqrt hratio
  have hfar : δ ≤ Real.sqrt (mulDistSqPair f (charFn ((k : ℝ) * t)) P) := Real.sqrt_le_sqrt hk
  have hdamp := norm_sum_smooth_le_exp_of_far hf hmul h1 ((k : ℝ) * t) hP hδ0 hfar
  rw [← smoothMulSum] at hdamp
  refine le_trans hdamp (Real.exp_le_exp.mpr ?_)
  rw [hδsq, ← hA, ← hB]
  have hval : A - ((K : ℝ) - 1) / (K : ℝ) * A = A / (K : ℝ) := by
    field_simp
    ring
  linarith [hval]

/-- **The dichotomy form.**  If `t` itself is close, then a *proper* multiple of it is far: the
frequency produced by the Fejér bound cannot be `k = 1`. -/
theorem exists_two_le_mulDistSqPair_ge_of_close {f : ℕ → ℂ} {P : Finset ℕ}
    (hneg : ∀ p ∈ P, f p = -1) (hP : ∀ p ∈ P, 0 < p) {K : ℕ} (hK : 1 ≤ K) (t : ℝ)
    (hclose : mulDistSqPair f (charFn t) P
      < (((K : ℝ) - 1) / (K : ℝ)) * (∑ p ∈ P, 1 / (p : ℝ))) :
    ∃ k : ℕ, 2 ≤ k ∧ k ≤ K ∧
      (((K : ℝ) - 1) / (K : ℝ)) * (∑ p ∈ P, 1 / (p : ℝ))
        ≤ mulDistSqPair f (charFn ((k : ℝ) * t)) P := by
  obtain ⟨k, hk1, hkK, hk⟩ := exists_mulDistSqPair_ge_of_neg_one hneg hP hK t
  refine ⟨k, ?_, hkK, hk⟩
  rcases Nat.lt_or_ge k 2 with hlt | hge
  · have hk1' : k = 1 := by omega
    subst hk1'
    rw [Nat.cast_one, one_mul] at hk
    linarith
  · exact hge

/-- **The limit form.**  For every `ε > 0` there is a length `K` such that every frequency `t` has a
multiple `kt`, `1 ≤ k ≤ K`, at squared distance at least `(1 − ε)∑_{p ∈ P}1/p`. -/
theorem exists_length_mulDistSqPair_ge_of_neg_one {f : ℕ → ℂ} {P : Finset ℕ}
    (hneg : ∀ p ∈ P, f p = -1) (hP : ∀ p ∈ P, 0 < p) {ε : ℝ} (hε : 0 < ε) :
    ∃ K : ℕ, 1 ≤ K ∧ ∀ t : ℝ, ∃ k : ℕ, 1 ≤ k ∧ k ≤ K ∧
      (1 - ε) * (∑ p ∈ P, 1 / (p : ℝ)) ≤ mulDistSqPair f (charFn ((k : ℝ) * t)) P := by
  classical
  obtain ⟨K, hK1, hKε⟩ : ∃ K : ℕ, 1 ≤ K ∧ 1 / ε ≤ (K : ℝ) := by
    refine ⟨max 1 ⌈1 / ε⌉₊, le_max_left _ _, ?_⟩
    have h1 : (1 / ε) ≤ (⌈1 / ε⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ((⌈1 / ε⌉₊ : ℕ) : ℝ) ≤ ((max 1 ⌈1 / ε⌉₊ : ℕ) : ℝ) := by
      exact_mod_cast Nat.cast_le.2 (le_max_right 1 ⌈1 / ε⌉₊)
    linarith
  have hK0 : (0 : ℝ) < (K : ℝ) := by
    have : (1 : ℝ) ≤ (K : ℝ) := by exact_mod_cast hK1
    linarith
  have hA0 : (0 : ℝ) ≤ ∑ p ∈ P, 1 / (p : ℝ) := by
    refine Finset.sum_nonneg fun p hp => ?_
    have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hP p hp
    positivity
  have hratio : 1 - ε ≤ ((K : ℝ) - 1) / (K : ℝ) := by
    rw [le_div_iff₀ hK0]
    have hinv : 1 ≤ ε * (K : ℝ) := by
      rw [div_le_iff₀ hε] at hKε
      linarith
    nlinarith [hinv]
  refine ⟨K, hK1, fun t => ?_⟩
  obtain ⟨k, hk1, hkK, hk⟩ := exists_mulDistSqPair_ge_of_neg_one hneg hP hK1 t
  refine ⟨k, hk1, hkK, le_trans ?_ hk⟩
  exact mul_le_mul_of_nonneg_right hratio hA0

end RHTower.Sieve
end
