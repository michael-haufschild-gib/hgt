import GaloisForLFunctions.RHTower.Sieve.DirichletOffDiagonalCorrelation
import GaloisForLFunctions.RHTower.DeciderBarrier

/-!
# The correlation of a completely multiplicative sequence along a ratio

`DirichletOffDiagonalCorrelation.integral_normSq_dirPoly_sub_diag_ratio` writes the off-diagonal of the
mean square as a sum over coprime pairs of `C(m,n) · K_T(m,n)`, with

`C(m,n) = ∑_{d : dm ≤ N, dn ≤ N} a_{dm} conj(a_{dn})`.

For a completely multiplicative unimodular sequence the inner sum *evaluates exactly*:

`g(dm) conj(g(dn)) = ‖g(d)‖² g(m) conj(g(n)) = g(m) conj(g(n))`

for every scale `d`, so `C(m,n) = g(m) conj(g(n)) · ⌊N / max(m,n)⌋`.

Two consequences, both unconditional.

* **The scale sum carries no cancellation.**  For a completely multiplicative unimodular sequence,
  the correlation along a fixed primitive ratio is as large as the trivial bound allows — every term
  has the same phase. Möbius coefficients and Dirichlet characters with zeros do not satisfy these
  hypotheses; their squarefree or coprimality restrictions must be retained separately.
  So no estimate of the inner sum can help; whatever cancellation the off-diagonal enjoys lives entirely
  in the outer sum over coprime pairs, where the kernel `K_T` sits.

* **The correlation modulus is coefficient-blind.**  `‖C(m,n)‖ = ⌊N / max(m,n)⌋` for *every* unimodular
  completely multiplicative `g`, so `‖C‖` is an invariant that cannot distinguish `λ` from `1`.  By
  `RHTower.le_bound_of_invariant_collision` any bound routed through `‖C‖` is capped at its value on the
  constant sequence — the same obstruction as `CoefficientFreeCap.le_of_coefficientFree_bound`, now one
  level deeper, inside the primitive-ratio decomposition.

Together these locate the remaining freedom precisely: a route must use the joint sign pattern of
`(g(m) conj(g(n)))_{m ⊥ n}` against `K_T`, and may not pass to moduli at any point.
-/

namespace RHTower.Sieve

open Finset

/-- The available scales are an initial segment: `d ≤ N / max(m,n)`. -/
theorem ratioScales_eq_Icc (N : ℕ) {m n : ℕ} (hm : 1 ≤ m) (_hn : 1 ≤ n) :
    ratioScales N m n = Finset.Icc 1 (N / max m n) := by
  classical
  have hmax : 0 < max m n := lt_of_lt_of_le Nat.zero_lt_one (le_max_of_le_left hm)
  ext d
  rw [ratioScales, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Icc]
  constructor
  · intro ⟨⟨hd1, _⟩, h1, h2⟩
    refine ⟨hd1, (Nat.le_div_iff_mul_le hmax).2 ?_⟩
    rcases le_total m n with h | h
    · rw [max_eq_right h]; exact h2
    · rw [max_eq_left h]; exact h1
  · intro ⟨hd1, hd⟩
    have hle : d * max m n ≤ N := (Nat.le_div_iff_mul_le hmax).1 hd
    refine ⟨⟨hd1, ?_⟩, ?_, ?_⟩
    · calc d = d * 1 := (mul_one d).symm
        _ ≤ d * max m n := Nat.mul_le_mul_left d (le_max_of_le_left hm)
        _ ≤ N := hle
    · exact le_trans (Nat.mul_le_mul_left d (le_max_left m n)) hle
    · exact le_trans (Nat.mul_le_mul_left d (le_max_right m n)) hle

/-- The truncated sequence of a function on `ℕ`, read off inside its range. -/
theorem dirSeq_restrict {N : ℕ} (g : ℕ → ℂ) {k : ℕ} (hk : 1 ≤ k) (hkN : k ≤ N) :
    dirSeq (fun i : Fin N => g ((i : ℕ) + 1)) k = g k := by
  rw [dirSeq, dif_pos (⟨hk, by omega⟩ : 1 ≤ k ∧ k - 1 < N)]
  show g (k - 1 + 1) = g k
  congr 1
  omega

/-- **The correlation of a completely multiplicative unimodular sequence.**  The scale sum has no
cancellation whatsoever: it is a count times a single unimodular phase. -/
theorem dirCorrelation_completelyMultiplicative (N : ℕ) (g : ℕ → ℂ)
    (hmul : ∀ a b : ℕ, g (a * b) = g a * g b)
    (hnorm : ∀ d : ℕ, 1 ≤ d → d ≤ N → ‖g d‖ = 1) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n) :
    dirCorrelation (fun i : Fin N => g ((i : ℕ) + 1)) m n
      = g m * (starRingEnd ℂ) (g n) * ((N / max m n : ℕ) : ℂ) := by
  classical
  have hstep : ∀ d ∈ ratioScales N m n,
      dirSeq (fun i : Fin N => g ((i : ℕ) + 1)) (d * m)
          * (starRingEnd ℂ) (dirSeq (fun i : Fin N => g ((i : ℕ) + 1)) (d * n))
        = g m * (starRingEnd ℂ) (g n) := by
    intro d hd
    rw [ratioScales, Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hd1, hdN⟩, h1, h2⟩ := hd
    have hdm1 : 1 ≤ d * m := Nat.one_le_iff_ne_zero.2 (by
      have : 0 < d * m := Nat.mul_pos hd1 hm
      omega)
    have hdn1 : 1 ≤ d * n := Nat.one_le_iff_ne_zero.2 (by
      have : 0 < d * n := Nat.mul_pos hd1 hn
      omega)
    rw [dirSeq_restrict g hdm1 h1, dirSeq_restrict g hdn1 h2, hmul, hmul, map_mul]
    have hd2 : g d * (starRingEnd ℂ) (g d) = 1 := by
      rw [Complex.mul_conj]
      norm_cast
      rw [Complex.normSq_eq_norm_sq, hnorm d hd1 hdN]
      norm_num
    calc g d * g m * ((starRingEnd ℂ) (g d) * (starRingEnd ℂ) (g n))
        = (g d * (starRingEnd ℂ) (g d)) * (g m * (starRingEnd ℂ) (g n)) := by ring
      _ = g m * (starRingEnd ℂ) (g n) := by rw [hd2, one_mul]
  rw [dirCorrelation, Finset.sum_congr rfl hstep, Finset.sum_const,
    ratioScales_eq_Icc N hm hn, Nat.card_Icc]
  rw [Nat.add_sub_cancel]
  ring

/-- **The correlation modulus is coefficient-blind.**  It is the same count for every unimodular
completely multiplicative sequence — in particular `λ` and `1` are indistinguishable through it.
This theorem does not apply to the Möbius function. -/
theorem norm_dirCorrelation_completelyMultiplicative (N : ℕ) (g : ℕ → ℂ)
    (hmul : ∀ a b : ℕ, g (a * b) = g a * g b)
    (hnorm : ∀ d : ℕ, 1 ≤ d → d ≤ N → ‖g d‖ = 1) {m n : ℕ} (hm : 1 ≤ m) (hn : 1 ≤ n)
    (hmN : m ≤ N) (hnN : n ≤ N) :
    ‖dirCorrelation (fun i : Fin N => g ((i : ℕ) + 1)) m n‖ = ((N / max m n : ℕ) : ℝ) := by
  rw [dirCorrelation_completelyMultiplicative N g hmul hnorm hm hn, norm_mul, norm_mul,
    RCLike.norm_conj, hnorm m hm hmN, hnorm n hn hnN]
  simp

/-- **The mean square of a completely multiplicative Dirichlet polynomial.**  Off the diagonal it is an
explicit Hermitian form in the coprime pairs: the weight `⌊N/max(m,n)⌋` is real and positive, and all the
arithmetic sits in the phases `g(m) conj(g(n))`. -/
theorem integral_normSq_dirPoly_sub_diag_completelyMultiplicative (N : ℕ) (g : ℕ → ℂ)
    (hmul : ∀ a b : ℕ, g (a * b) = g a * g b)
    (hnorm : ∀ d : ℕ, 1 ≤ d → d ≤ N → ‖g d‖ = 1) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, ((‖dirPoly N (fun i : Fin N => g ((i : ℕ) + 1)) t‖ ^ 2 : ℝ) : ℂ))
        - (T : ℂ) * ∑ m : Fin N, ((‖g ((m : ℕ) + 1)‖ ^ 2 : ℝ) : ℂ)
      = ∑ q ∈ primitiveRatioPairs N,
          g q.1 * (starRingEnd ℂ) (g q.2) * ((N / max q.1 q.2 : ℕ) : ℂ) * ratioKernel T q.1 q.2 := by
  classical
  rw [integral_normSq_dirPoly_sub_diag_ratio]
  refine Finset.sum_congr rfl fun q hq => ?_
  rw [primitiveRatioPairs, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc,
    Finset.mem_Icc] at hq
  obtain ⟨⟨⟨hm1, _⟩, hn1, _⟩, _, _⟩ := hq
  rw [dirCorrelation_completelyMultiplicative N g hmul hnorm hm1 hn1]

/-- The mass of a unimodular completely multiplicative sequence is the length. -/
theorem sum_normSq_completelyMultiplicative (N : ℕ) (g : ℕ → ℂ)
    (hnorm : ∀ d : ℕ, 1 ≤ d → d ≤ N → ‖g d‖ = 1) :
    ∑ m : Fin N, ((‖g ((m : ℕ) + 1)‖ ^ 2 : ℝ) : ℂ) = (N : ℂ) := by
  have hone : ∀ m : Fin N, ((‖g ((m : ℕ) + 1)‖ ^ 2 : ℝ) : ℂ) = 1 := by
    intro m
    rw [hnorm ((m : ℕ) + 1) (by omega) (by have := m.isLt; omega)]
    norm_num
  rw [Finset.sum_congr rfl (fun m _ => hone m)]
  simp

/-- **The mean square of a completely multiplicative Dirichlet polynomial, in closed form.**  The whole
`T`-dependence beyond the trivial term `TN` is the coprime-pair Hermitian form. -/
theorem integral_normSq_dirPoly_completelyMultiplicative (N : ℕ) (g : ℕ → ℂ)
    (hmul : ∀ a b : ℕ, g (a * b) = g a * g b)
    (hnorm : ∀ d : ℕ, 1 ≤ d → d ≤ N → ‖g d‖ = 1) (T : ℝ) :
    (∫ t in (0 : ℝ)..T, ((‖dirPoly N (fun i : Fin N => g ((i : ℕ) + 1)) t‖ ^ 2 : ℝ) : ℂ))
      = (T : ℂ) * (N : ℂ)
        + ∑ q ∈ primitiveRatioPairs N,
            g q.1 * (starRingEnd ℂ) (g q.2) * ((N / max q.1 q.2 : ℕ) : ℂ)
              * ratioKernel T q.1 q.2 := by
  have h := integral_normSq_dirPoly_sub_diag_completelyMultiplicative N g hmul hnorm T
  rw [sum_normSq_completelyMultiplicative N g hnorm] at h
  linear_combination h

/-- **The correlation modulus does not see the coefficients at all.**  For every unimodular completely
multiplicative `g` it agrees with the constant sequence, at every pair. -/
theorem norm_dirCorrelation_eq_norm_one (N : ℕ) (g : ℕ → ℂ)
    (hmul : ∀ a b : ℕ, g (a * b) = g a * g b)
    (hnorm : ∀ d : ℕ, 1 ≤ d → d ≤ N → ‖g d‖ = 1) (m n : ℕ) :
    ‖dirCorrelation (fun i : Fin N => g ((i : ℕ) + 1)) m n‖
      = ‖dirCorrelation (fun _ : Fin N => (1 : ℂ)) m n‖ := by
  classical
  rcases Nat.eq_zero_or_pos m with hm0 | hm
  · simp [dirCorrelation, hm0, dirSeq_zero]
  rcases Nat.eq_zero_or_pos n with hn0 | hn
  · simp [dirCorrelation, hn0, dirSeq_zero]
  rcases Finset.eq_empty_or_nonempty (ratioScales N m n) with hempty | ⟨d, hd⟩
  · rw [dirCorrelation, dirCorrelation, hempty, Finset.sum_empty, Finset.sum_empty]
  · rw [ratioScales, Finset.mem_filter, Finset.mem_Icc] at hd
    obtain ⟨⟨hd1, _⟩, h1, h2⟩ := hd
    have hmN : m ≤ N := le_trans (by
      calc m = 1 * m := (one_mul m).symm
        _ ≤ d * m := Nat.mul_le_mul_right m hd1) h1
    have hnN : n ≤ N := le_trans (by
      calc n = 1 * n := (one_mul n).symm
        _ ≤ d * n := Nat.mul_le_mul_right n hd1) h2
    rw [norm_dirCorrelation_completelyMultiplicative N g hmul hnorm hm hn hmN hnN,
      norm_dirCorrelation_completelyMultiplicative N (fun _ => (1 : ℂ))
        (fun a b => by norm_num) (fun d _ _ => by norm_num) hm hn hmN hnN]

/-- **The cap, one level inside the primitive-ratio decomposition.**  Any quantity bounded through the
correlation moduli is bounded by its value at the constant sequence. -/
theorem le_bound_of_norm_dirCorrelation {N : ℕ} {Φ : (Fin N → ℂ) → ℝ}
    {B : ((ℕ × ℕ) → ℝ) → ℝ}
    (hB : ∀ a : Fin N → ℂ, Φ a ≤ B (fun q => ‖dirCorrelation a q.1 q.2‖))
    (g : ℕ → ℂ) (hmul : ∀ a b : ℕ, g (a * b) = g a * g b)
    (hnorm : ∀ d : ℕ, 1 ≤ d → d ≤ N → ‖g d‖ = 1) :
    max (Φ (fun i : Fin N => g ((i : ℕ) + 1))) (Φ (fun _ : Fin N => (1 : ℂ)))
      ≤ B (fun q => ‖dirCorrelation (fun i : Fin N => g ((i : ℕ) + 1)) q.1 q.2‖) :=
  RHTower.le_bound_of_invariant_collision
    (fun a : Fin N → ℂ => fun q : ℕ × ℕ => ‖dirCorrelation a q.1 q.2‖) B Φ hB
    (funext fun q => norm_dirCorrelation_eq_norm_one N g hmul hnorm q.1 q.2)

end RHTower.Sieve
