import GaloisForLFunctions.HTGeometry.DaiYoshikawa.AnnulusPeriodSubstitution

/-!
# Proposition 5.1 (1): the period integral is a logarithm plus a continuous remainder

For the substitution `y = t/x` on the vanishing annulus the Laurent coefficient at exponent `k` is
`c_k(t) = Σ_{m−n=k} a_{mn} t^n`.  When `k < 0` every fibre exponent satisfies `n ≥ −k`, so `c_k` is
divisible by `t^{−k}`; that divisibility is exactly what cancels the divergent factor `|t|^{2k}`
produced by the radial integral.  Consequently every exponent other than `k = 0` contributes a term
that extends continuously across `t = 0`, while `k = 0` contributes `2π c₀ \overline{d₀} log|t|^{-1}`.

This is Proposition 5.1 (1) of Dai–Yoshikawa, *Degeneration of Riemann surfaces and small
eigenvalues of the Laplacian* (arXiv:2509.06151v2) — `a_{ij} log|t|^{-2} + b_{ij} + o(1)` — in the
sharper form "logarithm plus a globally continuous function", with `a_{ij}` the product of the two
residues `c₀(0)`, `d₀(0)`.
-/

open MeasureTheory Set Real Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry.DaiYoshikawa

open _root_.HTGeometry (deningerAnnulus)

/-! ## Divisibility of the Laurent coefficients -/

/-- On the fibre over `k ≤ 0` the second exponent is at least `−k`. -/
theorem le_snd_of_mem_substFiber {S : Finset (ℕ × ℕ)} {k : ℤ} {m : ℕ} (hm : (m : ℤ) = -k)
    {p : ℕ × ℕ} (hp : p ∈ S.filter fun p => (p.1 : ℤ) - (p.2 : ℤ) = k) : m ≤ p.2 := by
  rw [Finset.mem_filter] at hp
  have h := hp.2
  omega

/-- The Laurent coefficient with `t^m` divided out. -/
noncomputable def substTail (S : Finset (ℕ × ℕ)) (a : ℕ × ℕ → ℂ) (k : ℤ) (m : ℕ) (t : ℂ) : ℂ :=
  ∑ p ∈ S.filter fun p => (p.1 : ℤ) - (p.2 : ℤ) = k, a p * t ^ (p.2 - m)

theorem continuous_substTail (S : Finset (ℕ × ℕ)) (a : ℕ × ℕ → ℂ) (k : ℤ) (m : ℕ) :
    Continuous (substTail S a k m) := by
  show Continuous fun t : ℂ =>
    ∑ p ∈ S.filter fun p => (p.1 : ℤ) - (p.2 : ℤ) = k, a p * t ^ (p.2 - m)
  exact continuous_finsetSum _ fun p _ => continuous_const.mul (continuous_pow _)

theorem continuous_substCoeff (S : Finset (ℕ × ℕ)) (a : ℕ × ℕ → ℂ) (k : ℤ) :
    Continuous (substCoeff S a k) := by
  show Continuous fun t : ℂ =>
    ∑ p ∈ S.filter fun p => (p.1 : ℤ) - (p.2 : ℤ) = k, a p * t ^ p.2
  exact continuous_finsetSum _ fun p _ => continuous_const.mul (continuous_pow _)

/-- **Divisibility.**  For `k ≤ 0` the coefficient `c_k` is `t^{−k}` times a polynomial. -/
theorem substCoeff_eq_pow_mul_substTail (S : Finset (ℕ × ℕ)) (a : ℕ × ℕ → ℂ) {k : ℤ} {m : ℕ}
    (hm : (m : ℤ) = -k) (t : ℂ) :
    substCoeff S a k t = t ^ m * substTail S a k m t := by
  rw [substCoeff, substTail, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hle : m ≤ p.2 := le_snd_of_mem_substFiber hm hp
  have hsplit : t ^ p.2 = t ^ m * t ^ (p.2 - m) := by
    rw [← pow_add]
    congr 1
    omega
  rw [hsplit]
  ring

/-! ## The continuous extension of a single term -/

/-- The continuous extension across `t = 0` of the contribution of the exponent `k ≠ 0`. -/
noncomputable def substTermCont (S T : Finset (ℕ × ℕ)) (a b : ℕ × ℕ → ℂ) (k : ℤ) (t : ℂ) : ℂ :=
  if 0 < k then
    substCoeff S a k t * (starRingEnd ℂ) (substCoeff T b k t)
      * (2 * (π : ℂ) * ((1 - (‖t‖ : ℂ) ^ (2 * k).toNat) / (2 * (k : ℂ))))
  else
    2 * (π : ℂ) / (2 * (k : ℂ)) *
      ((‖t‖ : ℂ) ^ (2 * (-k).toNat)
          * (substTail S a k (-k).toNat t
              * (starRingEnd ℂ) (substTail T b k (-k).toNat t))
        - substTail S a k (-k).toNat t
            * (starRingEnd ℂ) (substTail T b k (-k).toNat t))

theorem continuous_substTermCont (S T : Finset (ℕ × ℕ)) (a b : ℕ × ℕ → ℂ) (k : ℤ) :
    Continuous (substTermCont S T a b k) := by
  have hnorm : ∀ n : ℕ, Continuous fun t : ℂ => ((‖t‖ : ℂ)) ^ n := fun n =>
    ((Complex.continuous_ofReal.comp continuous_norm)).pow n
  unfold substTermCont
  by_cases hk : 0 < k
  · simp only [if_pos hk]
    exact ((continuous_substCoeff S a k).mul
      (Complex.continuous_conj.comp (continuous_substCoeff T b k))).mul
      (continuous_const.mul (((continuous_const.sub (hnorm _)).div_const _)))
  · simp only [if_neg hk]
    refine continuous_const.mul ?_
    refine Continuous.sub ?_ ?_
    · exact (hnorm _).mul ((continuous_substTail S a k _).mul
        (Complex.continuous_conj.comp (continuous_substTail T b k _)))
    · exact (continuous_substTail S a k _).mul
        (Complex.continuous_conj.comp (continuous_substTail T b k _))

/-- `t \overline{t} = ‖t‖²` inside `ℂ`. -/
theorem mul_conj_eq_normSq (t : ℂ) : t * (starRingEnd ℂ) t = ((‖t‖ : ℂ)) ^ 2 := by
  rw [Complex.mul_conj]
  rw [Complex.normSq_eq_norm_sq]
  push_cast
  ring

/-- **The term of exponent `k ≠ 0` extends continuously.** -/
theorem substTerm_eq_substTermCont (S T : Finset (ℕ × ℕ)) (a b : ℕ × ℕ → ℂ) {k : ℤ}
    (hk : k ≠ 0) {t : ℂ} (ht : t ≠ 0) :
    substCoeff S a k t * (starRingEnd ℂ) (substCoeff T b k t)
        * (2 * (π : ℂ) * (((1 : ℂ) ^ (2 * k) - (‖t‖ : ℂ) ^ (2 * k)) / (2 * (k : ℂ))))
      = substTermCont S T a b k t := by
  have hR : ((‖t‖ : ℂ)) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero, norm_eq_zero]
    exact ht
  rcases lt_or_gt_of_ne hk with hneg | hpos
  · -- `k < 0`
    have hknot : ¬ (0 < k) := not_lt.mpr hneg.le
    set m : ℕ := (-k).toNat with hmdef
    have hm : (m : ℤ) = -k := by omega
    have hcS := substCoeff_eq_pow_mul_substTail S a hm t
    have hcT := substCoeff_eq_pow_mul_substTail T b hm t
    have hconj : (starRingEnd ℂ) (substCoeff T b k t)
        = (starRingEnd ℂ) t ^ m * (starRingEnd ℂ) (substTail T b k m t) := by
      rw [hcT, map_mul, map_pow]
    have hprod : substCoeff S a k t * (starRingEnd ℂ) (substCoeff T b k t)
        = ((‖t‖ : ℂ)) ^ (2 * m)
            * (substTail S a k m t * (starRingEnd ℂ) (substTail T b k m t)) := by
      rw [hcS, hconj]
      have hpm : t ^ m * (starRingEnd ℂ) t ^ m = ((‖t‖ : ℂ)) ^ (2 * m) := by
        rw [← mul_pow, mul_conj_eq_normSq, ← pow_mul, mul_comm 2 m]
      calc t ^ m * substTail S a k m t
            * ((starRingEnd ℂ) t ^ m * (starRingEnd ℂ) (substTail T b k m t))
          = (t ^ m * (starRingEnd ℂ) t ^ m)
              * (substTail S a k m t * (starRingEnd ℂ) (substTail T b k m t)) := by ring
        _ = ((‖t‖ : ℂ)) ^ (2 * m)
              * (substTail S a k m t * (starRingEnd ℂ) (substTail T b k m t)) := by rw [hpm]
    have hzpow : ((‖t‖ : ℂ)) ^ (2 * k) = (((‖t‖ : ℂ)) ^ (2 * m))⁻¹ := by
      have h2 : (2 : ℤ) * k = -((2 * m : ℕ) : ℤ) := by omega
      rw [h2, zpow_neg, zpow_natCast]
    have hcancel : ((‖t‖ : ℂ)) ^ (2 * m) * (((‖t‖ : ℂ)) ^ (2 * m))⁻¹ = 1 :=
      mul_inv_cancel₀ (pow_ne_zero _ hR)
    simp only [substTermCont, if_neg hknot, ← hmdef]
    rw [hprod, hzpow, one_zpow]
    field_simp
  · -- `k > 0`
    have hpow : ((‖t‖ : ℂ)) ^ (2 * k) = ((‖t‖ : ℂ)) ^ (2 * k).toNat := by
      rw [← zpow_natCast]
      congr 1
      omega
    simp only [substTermCont, if_pos hpos]
    rw [hpow, one_zpow]

/-! ## The period asymptotic -/

/-- **Proposition 5.1 (1).**

The annulus period integral of a substituted polynomial pair is
`2π c₀(t) \overline{d₀(t)} log|t|^{-1}` plus a function that extends continuously across `t = 0`. -/
theorem exists_continuous_annulusPeriodRemainder (S T : Finset (ℕ × ℕ)) (a b : ℕ × ℕ → ℂ)
    {s : Finset ℤ}
    (hS : (S.image fun p => (p.1 : ℤ) - (p.2 : ℤ)) ⊆ s)
    (hT : (T.image fun p => (p.1 : ℤ) - (p.2 : ℤ)) ⊆ s) :
    ∃ G : ℂ → ℂ, Continuous G ∧ ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ ≤ 1 →
      (∫ w in deningerAnnulus ‖t‖ 1,
          (∑ p ∈ S, a p * w ^ p.1 * (t / w) ^ p.2)
            * (starRingEnd ℂ) (∑ q ∈ T, b q * w ^ q.1 * (t / w) ^ q.2) / ((‖w‖ : ℂ) ^ 2))
        = 2 * (π : ℂ) * substCoeff S a 0 t * (starRingEnd ℂ) (substCoeff T b 0 t)
            * ((Real.log (1 / ‖t‖) : ℝ) : ℂ)
          + G t := by
  refine ⟨fun t => ∑ k ∈ s.erase 0, substTermCont S T a b k t, ?_, ?_⟩
  · exact continuous_finsetSum _ fun k _ => continuous_substTermCont S T a b k
  · intro t ht ht1
    have hne : t ≠ 0 := by
      intro hz
      rw [hz, norm_zero] at ht
      exact lt_irrefl 0 ht
    rw [setIntegral_substPairing S T a b hS hT ht ht1]
    have hterm : ∀ k ∈ s.erase 0,
        substCoeff S a k t * (starRingEnd ℂ) (substCoeff T b k t)
            * (if k = 0 then (2 * π * Real.log (1 / ‖t‖) : ℂ)
               else 2 * π * (((1 : ℂ) ^ (2 * k) - (‖t‖ : ℂ) ^ (2 * k)) / (2 * (k : ℂ))))
          = substTermCont S T a b k t := by
      intro k hk
      have hk0 : k ≠ 0 := (Finset.mem_erase.mp hk).1
      rw [if_neg hk0]
      exact substTerm_eq_substTermCont S T a b hk0 hne
    have hsplit : ∀ F : ℤ → ℂ, ∑ k ∈ s, F k
        = (if (0 : ℤ) ∈ s then F 0 else 0) + ∑ k ∈ s.erase 0, F k := by
      intro F
      by_cases h0 : (0 : ℤ) ∈ s
      · rw [if_pos h0]
        exact (Finset.add_sum_erase s F h0).symm
      · rw [if_neg h0, Finset.erase_eq_of_notMem h0, zero_add]
    rw [hsplit, Finset.sum_congr rfl hterm]
    congr 1
    by_cases h0 : (0 : ℤ) ∈ s
    · rw [if_pos h0, if_pos rfl]
      ring
    · rw [if_neg h0]
      have hzero : substCoeff S a 0 t = 0 :=
        substCoeff_eq_zero_of_notMem t fun hmem => h0 (hS hmem)
      rw [hzero]
      ring

end GaloisForLFunctions.HTGeometry.DaiYoshikawa
