import GaloisForLFunctions.RHTower.Sieve.RamarePhaseBilinear
import GaloisForLFunctions.RHTower.Sieve.SupportMeanSquare
import GaloisForLFunctions.RHTower.Sieve.RamarePrimeOffDiagonal

/-!
# The Ramaré cofactors of a block share one range

If the integers being factored lie in a block `[A, B]` and the designated primes lie in `(Q, 2Q]`,
then every cofactor `m = n/p` lies in the single block `[A/(2Q), B/Q]`, whose endpoints do not
depend on `p`.  This is what makes the Ramaré bilinear form a genuine *product* up to the
divisibility filter: all the cofactor polynomials are supported in one common index set, so they
differ from a single polynomial only by the terms divisible by `p`.

Over an initial segment `[1, M]` this fails — the cofactor range `[1, M/p]` moves with `p` by a
factor two — which is why the argument has to be run on a block.
-/

namespace RHTower.Sieve

open Finset

/-- **The cofactor block.**  Cofactors of a block, over a dyadic prime range, share one range. -/
theorem ramareCofactorSet_subset_common {S : Finset ℕ} {A B Q : ℝ} (hQ : 0 < Q)
    (hS : ∀ n ∈ S, A ≤ (n : ℝ) ∧ (n : ℝ) ≤ B) {p : ℕ}
    (hplo : Q < (p : ℝ)) (hphi : (p : ℝ) ≤ 2 * Q) :
    ramareCofactorSet S p ⊆ Finset.Icc ⌈A / (2 * Q)⌉₊ ⌊B / Q⌋₊ := by
  classical
  intro m hm
  rw [ramareCofactorSet, Finset.mem_image] at hm
  obtain ⟨n, hn, hnm⟩ := hm
  rw [Finset.mem_filter] at hn
  obtain ⟨hnS, hdvd⟩ := hn
  obtain ⟨hAn, hnB⟩ := hS n hnS
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_trans hQ hplo
  have hnpm : n = p * m := by
    rw [← hnm]
    exact (Nat.mul_div_cancel' hdvd).symm
  have hcast : ((n : ℕ) : ℝ) = (p : ℝ) * (m : ℝ) := by
    rw [hnpm]
    push_cast
    ring
  rw [hcast] at hAn hnB
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  refine Finset.mem_Icc.2 ⟨Nat.ceil_le.2 ?_, Nat.le_floor ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    nlinarith [hAn, hphi, hm0, hQ]
  · rw [le_div_iff₀ hQ]
    nlinarith [hnB, hplo, hm0, hp0]

/-- A cast-friendly cardinality bound for an integer interval. -/
theorem card_Icc_cast_le {a b : ℕ} {r s : ℝ} (ha : r ≤ (a : ℝ)) (hb : ((b : ℕ) : ℝ) ≤ s)
    (hrs : 0 ≤ s - r + 1) : ((Finset.Icc a b).card : ℝ) ≤ s - r + 1 := by
  rcases Nat.lt_or_ge b a with hab | hab
  · have hempty : Finset.Icc a b = ∅ := Finset.Icc_eq_empty (by omega)
    rw [hempty]
    simpa using hrs
  · have hle : a ≤ b + 1 := by omega
    have hval : ((Finset.Icc a b).card : ℝ) = (b : ℝ) + 1 - (a : ℝ) := by
      rw [Nat.card_Icc, Nat.cast_sub hle]
      push_cast
      ring
    rw [hval]
    linarith

/-- **Membership in a Ramaré cofactor set.**  `m` is a cofactor of `p` exactly when `p·m` is in the
set being factored. -/
theorem mem_ramareCofactorSet_iff {S : Finset ℕ} {p m : ℕ} (hp : 0 < p) :
    m ∈ ramareCofactorSet S p ↔ p * m ∈ S := by
  classical
  rw [ramareCofactorSet, Finset.mem_image]
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [Finset.mem_filter] at hn
    rw [Nat.mul_div_cancel' hn.2]
    exact hn.1
  · intro hpm
    refine ⟨p * m, Finset.mem_filter.2 ⟨hpm, Dvd.intro m rfl⟩, ?_⟩
    exact Nat.mul_div_cancel_left m hp

/-- **The cofactor gap over a narrow prime range.**  If the designated primes lie in
`(Q, Q(1+η)]`, the cofactor set of `p` inside a block `[A₀, B₀]` differs from the fixed block
`[A₀/(Q(1+η)), B₀/Q]` by at most `(A₀ + B₀)·η/Q + 4` elements: the two moving endpoints each sweep
an interval of relative width `η`.

This is the exact trade-off the Matomäki--Radziwiłł ladder has to balance: a narrow range makes the
cofactor polynomials common, a wide one carries the harmonic mass the Ramaré weight needs. -/
theorem card_cofactor_gap_le {A₀ B₀ : ℕ} {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) {p : ℕ}
    (hp0 : 0 < p) (hplo : Q < (p : ℝ)) (hphi : (p : ℝ) ≤ Q * (1 + η)) :
    (((Finset.Icc ⌈(A₀ : ℝ) / (Q * (1 + η))⌉₊ ⌊(B₀ : ℝ) / Q⌋₊
        \ ramareCofactorSet (Finset.Icc A₀ B₀) p).card : ℝ))
      ≤ ((A₀ : ℝ) + (B₀ : ℝ)) * η / Q + 4 := by
  classical
  have hp0R : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  have hQη : (0 : ℝ) < Q * (1 + η) := by positivity
  -- the bad cofactors sit in two short intervals
  have hsub : (Finset.Icc ⌈(A₀ : ℝ) / (Q * (1 + η))⌉₊ ⌊(B₀ : ℝ) / Q⌋₊
        \ ramareCofactorSet (Finset.Icc A₀ B₀) p)
      ⊆ Finset.Icc ⌈(A₀ : ℝ) / (Q * (1 + η))⌉₊ ⌊(A₀ : ℝ) / Q⌋₊
        ∪ Finset.Icc ⌈(B₀ : ℝ) / (Q * (1 + η))⌉₊ ⌊(B₀ : ℝ) / Q⌋₊ := by
    intro m hm
    rw [Finset.mem_sdiff, Finset.mem_Icc] at hm
    obtain ⟨⟨hlo, hhi⟩, hnot⟩ := hm
    have hpm : ¬ (A₀ ≤ p * m ∧ p * m ≤ B₀) := fun hc =>
      hnot ((mem_ramareCofactorSet_iff hp0).2 (Finset.mem_Icc.2 hc))
    rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc]
    by_cases hA : A₀ ≤ p * m
    · -- then `p*m > B₀`, so `m` is near the top
      have hB : B₀ < p * m := by
        rcases Nat.lt_or_ge B₀ (p * m) with hlt | hge
        · exact hlt
        · exact absurd ⟨hA, hge⟩ hpm
      refine Or.inr ⟨?_, hhi⟩
      refine Nat.ceil_le.2 ?_
      have hBR : ((B₀ : ℕ) : ℝ) < (p : ℝ) * (m : ℝ) := by exact_mod_cast hB
      rw [div_le_iff₀ hQη]
      nlinarith [hBR, hphi, Nat.cast_nonneg (α := ℝ) m]
    · -- then `p*m < A₀`, so `m` is near the bottom
      have hAlt : p * m < A₀ := Nat.lt_of_not_le hA
      refine Or.inl ⟨hlo, ?_⟩
      refine Nat.le_floor ?_
      have hAR : (p : ℝ) * (m : ℝ) < ((A₀ : ℕ) : ℝ) := by exact_mod_cast hAlt
      rw [le_div_iff₀ hQ]
      nlinarith [hAR, hplo, Nat.cast_nonneg (α := ℝ) m]
  have hcardA : ((Finset.Icc ⌈(A₀ : ℝ) / (Q * (1 + η))⌉₊ ⌊(A₀ : ℝ) / Q⌋₊).card : ℝ)
      ≤ (A₀ : ℝ) * η / Q + 2 := by
    have hgap : (A₀ : ℝ) / Q - (A₀ : ℝ) / (Q * (1 + η)) ≤ (A₀ : ℝ) * η / Q := by
      rw [div_sub_div _ _ (ne_of_gt hQ) (ne_of_gt hQη), div_le_div_iff₀ (by positivity) hQ]
      nlinarith [(by positivity : (0 : ℝ) ≤ (A₀ : ℝ) * η ^ 2 * Q ^ 2)]
    have hmono : (A₀ : ℝ) / (Q * (1 + η)) ≤ (A₀ : ℝ) / Q := by
      refine div_le_div_of_nonneg_left (Nat.cast_nonneg A₀) hQ ?_
      nlinarith [hη, hQ]
    have hstep := card_Icc_cast_le (Nat.le_ceil ((A₀ : ℝ) / (Q * (1 + η))))
      (Nat.floor_le (by positivity : (0 : ℝ) ≤ (A₀ : ℝ) / Q)) (by linarith)
    linarith
  have hcardB : ((Finset.Icc ⌈(B₀ : ℝ) / (Q * (1 + η))⌉₊ ⌊(B₀ : ℝ) / Q⌋₊).card : ℝ)
      ≤ (B₀ : ℝ) * η / Q + 2 := by
    have hgap : (B₀ : ℝ) / Q - (B₀ : ℝ) / (Q * (1 + η)) ≤ (B₀ : ℝ) * η / Q := by
      rw [div_sub_div _ _ (ne_of_gt hQ) (ne_of_gt hQη), div_le_div_iff₀ (by positivity) hQ]
      nlinarith [(by positivity : (0 : ℝ) ≤ (B₀ : ℝ) * η ^ 2 * Q ^ 2)]
    have hmono : (B₀ : ℝ) / (Q * (1 + η)) ≤ (B₀ : ℝ) / Q := by
      refine div_le_div_of_nonneg_left (Nat.cast_nonneg B₀) hQ ?_
      nlinarith [hη, hQ]
    have hstep := card_Icc_cast_le (Nat.le_ceil ((B₀ : ℝ) / (Q * (1 + η))))
      (Nat.floor_le (by positivity : (0 : ℝ) ≤ (B₀ : ℝ) / Q)) (by linarith)
    linarith
  have hcardU := Finset.card_le_card hsub
  have hunion := Finset.card_union_le
    (Finset.Icc ⌈(A₀ : ℝ) / (Q * (1 + η))⌉₊ ⌊(A₀ : ℝ) / Q⌋₊)
    (Finset.Icc ⌈(B₀ : ℝ) / (Q * (1 + η))⌉₊ ⌊(B₀ : ℝ) / Q⌋₊)
  have hchain : ((Finset.Icc ⌈(A₀ : ℝ) / (Q * (1 + η))⌉₊ ⌊(B₀ : ℝ) / Q⌋₊
        \ ramareCofactorSet (Finset.Icc A₀ B₀) p).card : ℝ)
      ≤ ((Finset.Icc ⌈(A₀ : ℝ) / (Q * (1 + η))⌉₊ ⌊(A₀ : ℝ) / Q⌋₊).card : ℝ)
        + ((Finset.Icc ⌈(B₀ : ℝ) / (Q * (1 + η))⌉₊ ⌊(B₀ : ℝ) / Q⌋₊).card : ℝ) := by
    have := le_trans hcardU hunion
    exact_mod_cast this
  have hsplit : ((A₀ : ℝ) + (B₀ : ℝ)) * η / Q + 4
      = ((A₀ : ℝ) * η / Q + 2) + ((B₀ : ℝ) * η / Q + 2) := by
    field_simp
    ring
  rw [hsplit]
  linarith [hchain, hcardA, hcardB]

/-! ## The `ℓ²` cost of a change of index set -/

open MeasureTheory

theorem logPoly_sub_eq_sdiff (a : ℕ → ℂ) (U V : Finset ℕ) (w : ℝ) :
    logPoly a U w - logPoly a V w = logPoly a (U \ V) w - logPoly a (V \ U) w := by
  classical
  have hUeq : U \ (U ∩ V) = U \ V := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hVeq : V \ (V ∩ U) = V \ U := by
    ext n
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hU : logPoly a (U \ V) w + logPoly a (U ∩ V) w = logPoly a U w := by
    rw [← hUeq, logPoly, logPoly, logPoly]
    exact Finset.sum_sdiff Finset.inter_subset_left
  have hV : logPoly a (V \ U) w + logPoly a (V ∩ U) w = logPoly a V w := by
    rw [← hVeq, logPoly, logPoly, logPoly]
    exact Finset.sum_sdiff Finset.inter_subset_left
  have hcomm : (V ∩ U) = (U ∩ V) := Finset.inter_comm V U
  rw [hcomm] at hV
  linear_combination hV - hU

/-- **The mean square of a change of index set.**  Replacing the index set of a bounded-coefficient
Dirichlet polynomial costs, in mean square, only the size of the symmetric difference. -/
theorem integral_Icc_normSq_logPoly_sub_le {a : ℕ → ℂ} (hA : ∀ n, ‖a n‖ ≤ 1)
    {U V : Finset ℕ} (hU0 : (0 : ℕ) ∉ U) (hV0 : (0 : ℕ) ∉ V) {M : ℕ}
    (hUM : ∀ n ∈ U, n ≤ M) (hVM : ∀ n ∈ V, n ≤ M) {W : ℝ} (hW : 1 ≤ W) :
    (∫ w in Set.Icc (-W) W, ‖logPoly a U w - logPoly a V w‖ ^ 2)
      ≤ 2 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
          * (((U \ V).card : ℝ) + ((V \ U).card : ℝ)) := by
  classical
  have hcoef : (0 : ℝ) ≤ 5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ) := by
    have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have h1 : (0 : ℝ) ≤ 5 * Real.pi / 2 * W := mul_nonneg (by positivity) hW0.le
    have h2 : (0 : ℝ) ≤ 5 * Real.exp 1 / 2 * (M : ℝ) := mul_nonneg (by positivity) hM0
    linarith
  -- the two pieces
  have hUd0 : (0 : ℕ) ∉ U \ V := fun hc => hU0 (Finset.mem_sdiff.1 hc).1
  have hVd0 : (0 : ℕ) ∉ V \ U := fun hc => hV0 (Finset.mem_sdiff.1 hc).1
  have hUdM : ∀ n ∈ U \ V, n ≤ M := fun n hn => hUM n (Finset.mem_sdiff.1 hn).1
  have hVdM : ∀ n ∈ V \ U, n ≤ M := fun n hn => hVM n (Finset.mem_sdiff.1 hn).1
  have hEU := integral_Icc_normSq_logPoly_le_energy a hUd0 hUdM hW
  have hEV := integral_Icc_normSq_logPoly_le_energy a hVd0 hVdM hW
  have hmassU : (∑ n ∈ U \ V, ‖a n‖ ^ 2) ≤ ((U \ V).card : ℝ) := by
    have h1 : ∀ n ∈ U \ V, ‖a n‖ ^ 2 ≤ (1 : ℝ) := by
      intro n _
      have := pow_le_pow_left₀ (norm_nonneg (a n)) (hA n) 2
      simpa using this
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h2
    exact h2
  have hmassV : (∑ n ∈ V \ U, ‖a n‖ ^ 2) ≤ ((V \ U).card : ℝ) := by
    have h1 : ∀ n ∈ V \ U, ‖a n‖ ^ 2 ≤ (1 : ℝ) := by
      intro n _
      have := pow_le_pow_left₀ (norm_nonneg (a n)) (hA n) 2
      simpa using this
    have h2 := Finset.sum_le_sum h1
    rw [Finset.sum_const, nsmul_eq_mul, mul_one] at h2
    exact h2
  -- the pointwise inequality
  have hpt : ∀ w : ℝ, ‖logPoly a U w - logPoly a V w‖ ^ 2
      ≤ 2 * ‖logPoly a (U \ V) w‖ ^ 2 + 2 * ‖logPoly a (V \ U) w‖ ^ 2 := by
    intro w
    rw [logPoly_sub_eq_sdiff]
    have htri := norm_sub_le (logPoly a (U \ V) w) (logPoly a (V \ U) w)
    have h0 : (0 : ℝ) ≤ ‖logPoly a (U \ V) w‖ := norm_nonneg _
    have h1 : (0 : ℝ) ≤ ‖logPoly a (V \ U) w‖ := norm_nonneg _
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [hsq, sq_nonneg (‖logPoly a (U \ V) w‖ - ‖logPoly a (V \ U) w‖)]
  have hcont : Continuous fun w : ℝ => ‖logPoly a U w - logPoly a V w‖ ^ 2 :=
    ((((continuous_logPoly a U).sub (continuous_logPoly a V)).norm).pow 2)
  have hcontU : Continuous fun w : ℝ => ‖logPoly a (U \ V) w‖ ^ 2 :=
    (((continuous_logPoly a (U \ V)).norm).pow 2)
  have hcontV : Continuous fun w : ℝ => ‖logPoly a (V \ U) w‖ ^ 2 :=
    (((continuous_logPoly a (V \ U)).norm).pow 2)
  have hint1 : IntegrableOn (fun w : ℝ => ‖logPoly a U w - logPoly a V w‖ ^ 2)
      (Set.Icc (-W) W) volume := hcont.integrableOn_Icc
  have hint2 : IntegrableOn (fun w : ℝ =>
      2 * ‖logPoly a (U \ V) w‖ ^ 2 + 2 * ‖logPoly a (V \ U) w‖ ^ 2)
      (Set.Icc (-W) W) volume := ((hcontU.const_mul 2).add (hcontV.const_mul 2)).integrableOn_Icc
  have hmono := setIntegral_mono_on hint1 hint2 measurableSet_Icc (fun w _ => hpt w)
  have hsplit : (∫ w in Set.Icc (-W) W,
      (2 * ‖logPoly a (U \ V) w‖ ^ 2 + 2 * ‖logPoly a (V \ U) w‖ ^ 2))
      = 2 * (∫ w in Set.Icc (-W) W, ‖logPoly a (U \ V) w‖ ^ 2)
        + 2 * (∫ w in Set.Icc (-W) W, ‖logPoly a (V \ U) w‖ ^ 2) := by
    have hiU : IntegrableOn (fun w : ℝ => 2 * ‖logPoly a (U \ V) w‖ ^ 2)
        (Set.Icc (-W) W) volume := (hcontU.const_mul 2).integrableOn_Icc
    have hiV : IntegrableOn (fun w : ℝ => 2 * ‖logPoly a (V \ U) w‖ ^ 2)
        (Set.Icc (-W) W) volume := (hcontV.const_mul 2).integrableOn_Icc
    rw [integral_add hiU hiV, integral_const_mul, integral_const_mul]
  rw [hsplit] at hmono
  have hUfin : (∫ w in Set.Icc (-W) W, ‖logPoly a (U \ V) w‖ ^ 2)
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ)) * ((U \ V).card : ℝ) :=
    le_trans hEU (mul_le_mul_of_nonneg_left hmassU hcoef)
  have hVfin : (∫ w in Set.Icc (-W) W, ‖logPoly a (V \ U) w‖ ^ 2)
      ≤ (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ)) * ((V \ U).card : ℝ) :=
    le_trans hEV (mul_le_mul_of_nonneg_left hmassV hcoef)
  nlinarith [hmono, hUfin, hVfin, hcoef]

/-! ## The divisibility filter -/

/-- The multiples of `p` in a block are few. -/
private theorem card_multiples_le (a b p : ℕ) :
    ((((Finset.Icc a b).filter (fun m => p ∣ m)).card : ℕ) : ℝ) ≤ (b : ℝ) / (p : ℝ) + 1 := by
  classical
  have hmaps : ∀ m ∈ (Finset.Icc a b).filter (fun m => p ∣ m),
      m / p ∈ Finset.Icc 0 (b / p) := by
    intro m hm
    rw [Finset.mem_filter, Finset.mem_Icc] at hm
    exact Finset.mem_Icc.2 ⟨Nat.zero_le _, Nat.div_le_div_right hm.1.2⟩
  have hinj : Set.InjOn (fun m => m / p)
      ((Finset.Icc a b).filter (fun m => p ∣ m) : Finset ℕ) := by
    intro m₁ h₁ m₂ h₂ hEq
    simp only [Finset.coe_filter, Set.mem_setOf_eq] at h₁ h₂
    have hd₁ : p ∣ m₁ := h₁.2
    have hd₂ : p ∣ m₂ := h₂.2
    have e₁ : p * (m₁ / p) = m₁ := Nat.mul_div_cancel' hd₁
    have e₂ : p * (m₂ / p) = m₂ := Nat.mul_div_cancel' hd₂
    have hEq' : m₁ / p = m₂ / p := hEq
    rw [← e₁, ← e₂, hEq']
  have hcard := Finset.card_le_card_of_injOn (fun m => m / p) hmaps hinj
  have hIcc : (Finset.Icc 0 (b / p)).card = b / p + 1 := by
    simp [Nat.card_Icc]
  rw [hIcc] at hcard
  have hcast : (((Finset.Icc a b).filter (fun m => p ∣ m)).card : ℝ) ≤ ((b / p : ℕ) : ℝ) + 1 := by
    have := (Nat.cast_le (α := ℝ)).2 hcard
    push_cast at this
    linarith
  have hdiv : ((b / p : ℕ) : ℝ) ≤ (b : ℝ) / (p : ℝ) := Nat.cast_div_le
  linarith

/-- **The cofactor set differs from the common block by a controlled number of elements.**  The
gap comes from the two moving endpoints (relative width `η`) and from the multiples of `p`. -/
theorem card_cofactor_symmDiff_le {A₀ B₀ : ℕ} {Q η : ℝ} (hQ : 0 < Q) (hη : 0 ≤ η) {p : ℕ}
    (hp0 : 0 < p) (hplo : Q < (p : ℝ)) (hphi : (p : ℝ) ≤ Q * (1 + η)) :
    (((Finset.Icc ⌈(A₀ : ℝ) / (Q * (1 + η))⌉₊ ⌊(B₀ : ℝ) / Q⌋₊
        \ {m ∈ ramareCofactorSet (Finset.Icc A₀ B₀) p | ¬ p ∣ m}).card : ℝ))
      ≤ ((A₀ : ℝ) + (B₀ : ℝ)) * η / Q + 4 + ((B₀ : ℝ) / Q ^ 2 + 1) := by
  classical
  set C : Finset ℕ := Finset.Icc ⌈(A₀ : ℝ) / (Q * (1 + η))⌉₊ ⌊(B₀ : ℝ) / Q⌋₊ with hC
  set R : Finset ℕ := ramareCofactorSet (Finset.Icc A₀ B₀) p with hR
  have hsub : C \ {m ∈ R | ¬ p ∣ m} ⊆ (C \ R) ∪ (C.filter (fun m => p ∣ m)) := by
    intro m hm
    rw [Finset.mem_sdiff] at hm
    obtain ⟨hmC, hmnot⟩ := hm
    by_cases hdvd : p ∣ m
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨hmC, hdvd⟩)
    · refine Finset.mem_union_left _ (Finset.mem_sdiff.2 ⟨hmC, fun hmR => hmnot ?_⟩)
      exact Finset.mem_filter.2 ⟨hmR, hdvd⟩
  have hgap := card_cofactor_gap_le (A₀ := A₀) (B₀ := B₀) hQ hη hp0 hplo hphi
  have hmult : ((C.filter (fun m => p ∣ m)).card : ℝ) ≤ (B₀ : ℝ) / Q ^ 2 + 1 := by
    have hstep := card_multiples_le ⌈(A₀ : ℝ) / (Q * (1 + η))⌉₊ ⌊(B₀ : ℝ) / Q⌋₊ p
    have hfl : ((⌊(B₀ : ℝ) / Q⌋₊ : ℕ) : ℝ) ≤ (B₀ : ℝ) / Q :=
      Nat.floor_le (by positivity)
    have hp0R : (0 : ℝ) < (p : ℝ) := lt_trans hQ hplo
    have hB0 : (0 : ℝ) ≤ (B₀ : ℝ) := Nat.cast_nonneg B₀
    have hdiv : ((⌊(B₀ : ℝ) / Q⌋₊ : ℕ) : ℝ) / (p : ℝ) ≤ (B₀ : ℝ) / Q ^ 2 := by
      rw [div_le_div_iff₀ hp0R (by positivity)]
      have h1 : ((⌊(B₀ : ℝ) / Q⌋₊ : ℕ) : ℝ) * Q ≤ (B₀ : ℝ) := by
        have := mul_le_mul_of_nonneg_right hfl hQ.le
        rw [div_mul_cancel₀ _ (ne_of_gt hQ)] at this
        exact this
      nlinarith [h1, hplo, Nat.cast_nonneg (α := ℝ) (⌊(B₀ : ℝ) / Q⌋₊), hQ]
    rw [hC]
    linarith [hstep, hdiv]
  have hunion := Finset.card_union_le (C \ R) (C.filter (fun m => p ∣ m))
  have hchain : ((C \ {m ∈ R | ¬ p ∣ m}).card : ℝ)
      ≤ ((C \ R).card : ℝ) + ((C.filter (fun m => p ∣ m)).card : ℝ) := by
    have := le_trans (Finset.card_le_card hsub) hunion
    exact_mod_cast this
  linarith [hchain, hgap, hmult]

/-! ## The cofactor discrepancy of one prime -/

theorem norm_ramareCofactorCoeff_le_one (P : Finset ℕ) (m : ℕ) :
    ‖ramareCofactorCoeff P m‖ ≤ 1 := by
  have hnum : ‖((ArithmeticFunction.moebius m : ℤ) : ℂ)‖ ≤ 1 := by
    have hnorm : ‖((ArithmeticFunction.moebius m : ℤ) : ℂ)‖
        = |((ArithmeticFunction.moebius m : ℤ) : ℝ)| := by
      rw [show (((ArithmeticFunction.moebius m : ℤ)) : ℂ)
          = ((((ArithmeticFunction.moebius m : ℤ) : ℝ)) : ℂ) by push_cast; ring,
        Complex.norm_real, Real.norm_eq_abs]
    rw [hnorm]
    exact abs_moebius_real_le_one m
  have hden : ‖(((primeFactorsIn P m).card : ℂ) + 1)‖
      = ((primeFactorsIn P m).card : ℝ) + 1 := by
    have hcast : (((primeFactorsIn P m).card : ℂ) + 1)
        = ((((primeFactorsIn P m).card + 1 : ℕ)) : ℂ) := by push_cast; ring
    rw [hcast, Complex.norm_natCast]
    push_cast
    ring
  rw [ramareCofactorCoeff, norm_div, hden]
  have h1 : (0 : ℝ) ≤ ((primeFactorsIn P m).card : ℝ) := Nat.cast_nonneg _
  refine div_le_one_of_le₀ ?_ (by linarith)
  linarith

/-- **The filtered cofactor set sits inside the common block.** -/
theorem cofactorFilter_subset_common (M : ℕ) {Q η : ℝ} (hQ : 1 ≤ Q) (hη : 0 ≤ η)
    {p : ℕ} (hp0 : 0 < p) (hplo : Q < (p : ℝ)) (hphi : (p : ℝ) ≤ Q * (1 + η)) :
    {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m}
      ⊆ Finset.Icc ⌈((1 : ℕ) : ℝ) / (Q * (1 + η))⌉₊ ⌊((M : ℕ) : ℝ) / Q⌋₊ := by
  classical
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  have hQη : (0 : ℝ) < Q * (1 + η) := by positivity
  intro m hm
  rw [Finset.mem_filter] at hm
  have hmem := (mem_ramareCofactorSet_iff hp0).1 hm.1
  rw [Finset.mem_Icc] at hmem
  obtain ⟨hlo, hhi⟩ := hmem
  have hmR : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hloR : (1 : ℝ) ≤ (p : ℝ) * (m : ℝ) := by exact_mod_cast hlo
  have hhiR : (p : ℝ) * (m : ℝ) ≤ ((M : ℕ) : ℝ) := by exact_mod_cast hhi
  rw [Finset.mem_Icc]
  constructor
  · refine Nat.ceil_le.2 ?_
    rw [div_le_iff₀ hQη]
    push_cast
    nlinarith [hloR, hphi, hmR]
  · refine Nat.le_floor ?_
    rw [le_div_iff₀ hQ0]
    nlinarith [hhiR, hplo, hmR]

/-- **The cofactor polynomial of one prime, against the common block.**  Over a prime range of
relative width `η` the discrepancy is proportional to `η` plus the multiples of `p`. -/
theorem integral_normSq_cofactor_sub_common_le {P : Finset ℕ} (M : ℕ) {Q η W : ℝ}
    (hQ : 1 ≤ Q) (hη : 0 ≤ η) (hW : 1 ≤ W) {p : ℕ}
    (hp0 : 0 < p) (hplo : Q < (p : ℝ)) (hphi : (p : ℝ) ≤ Q * (1 + η)) :
    (∫ w in Set.Icc (-W) W, ‖ramareCofactorPoly P M p w
        - logPoly (ramareCofactorCoeff P)
            (Finset.Icc ⌈((1 : ℕ) : ℝ) / (Q * (1 + η))⌉₊ ⌊((M : ℕ) : ℝ) / Q⌋₊) w‖ ^ 2)
      ≤ 2 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ))
          * ((((1 : ℕ) : ℝ) + ((M : ℕ) : ℝ)) * η / Q + 4 + (((M : ℕ) : ℝ) / Q ^ 2 + 1)) := by
  classical
  have hQ0 : (0 : ℝ) < Q := lt_of_lt_of_le zero_lt_one hQ
  have hQη : (0 : ℝ) < Q * (1 + η) := by positivity
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp0
  set U : Finset ℕ := {m ∈ ramareCofactorSet (Finset.Icc 1 M) p | ¬ p ∣ m} with hU
  set C : Finset ℕ := Finset.Icc ⌈((1 : ℕ) : ℝ) / (Q * (1 + η))⌉₊ ⌊((M : ℕ) : ℝ) / Q⌋₊ with hC
  have hmemU : ∀ m ∈ U, 1 ≤ p * m ∧ p * m ≤ M := by
    intro m hm
    rw [hU, Finset.mem_filter] at hm
    have := (mem_ramareCofactorSet_iff hp0).1 hm.1
    rw [Finset.mem_Icc] at this
    exact this
  have hU0 : (0 : ℕ) ∉ U := by
    intro hc
    have := (hmemU 0 hc).1
    omega
  have hC0 : (0 : ℕ) ∉ C := by
    intro hc
    rw [hC, Finset.mem_Icc] at hc
    have h1 : 1 ≤ ⌈((1 : ℕ) : ℝ) / (Q * (1 + η))⌉₊ := Nat.one_le_ceil_iff.2 (by positivity)
    omega
  have hUM : ∀ n ∈ U, n ≤ M := by
    intro m hm
    obtain ⟨-, hhi⟩ := hmemU m hm
    calc m ≤ p * m := Nat.le_mul_of_pos_left m hp0
      _ ≤ M := hhi
  have hCM : ∀ n ∈ C, n ≤ M := by
    intro m hm
    rw [hC, Finset.mem_Icc] at hm
    have hfl : ((⌊((M : ℕ) : ℝ) / Q⌋₊ : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) / Q :=
      Nat.floor_le (by positivity)
    have hmR : ((m : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) / Q := le_trans (by exact_mod_cast hm.2) hfl
    have : ((m : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) := by
      rw [le_div_iff₀ hQ0] at hmR
      nlinarith [hmR, hQ, Nat.cast_nonneg (α := ℝ) m]
    exact_mod_cast this
  have hUsubC : U ⊆ C := by
    rw [hU, hC]
    exact cofactorFilter_subset_common M hQ hη hp0 hplo hphi
  have hsdiff : U \ C = ∅ := Finset.sdiff_eq_empty_iff_subset.2 hUsubC
  have hgap := card_cofactor_symmDiff_le (A₀ := 1) (B₀ := M) hQ0 hη hp0 hplo hphi
  have hbase := integral_Icc_normSq_logPoly_sub_le
    (a := ramareCofactorCoeff P) (norm_ramareCofactorCoeff_le_one P) (U := U) (V := C)
    hU0 hC0 hUM hCM hW
  rw [hsdiff] at hbase
  simp only [Finset.card_empty, Nat.cast_zero, zero_add] at hbase
  have hcoef : (0 : ℝ) ≤ 2 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ)) := by
    have hW0 : (0 : ℝ) < W := lt_of_lt_of_le zero_lt_one hW
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    have h1 : (0 : ℝ) ≤ 5 * Real.pi / 2 * W := mul_nonneg (by positivity) hW0.le
    have h2 : (0 : ℝ) ≤ 5 * Real.exp 1 / 2 * (M : ℝ) := mul_nonneg (by positivity) hM0
    linarith
  have hcong : ramareCofactorPoly P M p = fun w => logPoly (ramareCofactorCoeff P) U w := rfl
  rw [hcong]
  refine hbase.trans ?_
  exact mul_le_mul_of_nonneg_left hgap hcoef

end RHTower.Sieve
